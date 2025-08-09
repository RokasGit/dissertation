# SPDX-License-Identifier: BSD-2-Clause
"""OCEOS Unity Test Generator from SPIN output"""

from __future__ import annotations

import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, List, Dict, Any, Set, Tuple

import yaml


@dataclass
class Step:
    kind: str  # 'call' | 'scalar' | 'assert_eq' | 'log' | 'sync' | 'define' | 'decl' | 'other' | 'scenario'
    api: str | None = None
    args: List[str] | None = None
    retvar: str | None = None
    name: str | None = None
    values: List[str] | None = None
    label: str | None = None
    raw: str = ""


class OceosUnityGenerator:
    """Generates Unity test code for OCEOS from SPIN traces"""

    def __init__(self, model_root: str, preamble_file: str | Path, postamble_file: str | Path,
                 run_file: str | Path, refine_file: str | Path) -> None:
        self.model_root = model_root
        self.preamble_file = Path(preamble_file)
        self.postamble_file = Path(postamble_file)
        self.run_file = Path(run_file)
        self.refine_file = Path(refine_file)

        # Load refinement mappings (reserved for future)
        self.refine = yaml.safe_load(self.refine_file.read_text(encoding="utf-8")) if self.refine_file.exists() else {}

    def generate_test(self, test_number: int, output_file: str | Path, spin_trace_path: str | Path) -> None:
        output_path = Path(output_file)
        output_path.parent.mkdir(parents=True, exist_ok=True)

        spin_path = Path(spin_trace_path)
        if not spin_path.exists():
            raise FileNotFoundError(f"SPIN trace not found: {spin_path}")

        lines = spin_path.read_text(encoding="utf-8", errors="ignore" ).splitlines()
        steps = self.parse_spin_trace(lines)
        code = self.generate_unity_code(steps, test_number)
        output_path.write_text(code, encoding="utf-8", newline="\n")

    # printf('<fmt>', _pid, <args...>) extractor inside DOT-like lines
    _re_printf = re.compile(r"printf\((?P<fmt>'[^']*')\s*(?:,\s*(?P<args>[^)]*))?\)")

    def parse_spin_trace(self, lines: Iterable[str]) -> List[Step]:
        steps: List[Step] = []
        for ln in lines:
            if "printf(" not in ln or "@@@" not in ln:
                continue
            m = self._re_printf.search(ln)
            if not m:
                continue
            fmt = m.group("fmt").strip("'")  # ex: "@@@ %d CALL ..."
            args_str = (m.group("args") or "").strip()
            # Drop leading _pid if present
            args = [a.strip() for a in args_str.split(",") if a.strip()] if args_str else []
            if args and args[0] == "_pid":
                args = args[1:]

            # Normalize spaces inside fmt (remove multiple spaces)
            inner = re.sub(r"\s+", " ", fmt)
            if not inner.startswith("@@@"):
                continue
            payload = inner[3:].strip()
            # Strip optional leading "%d " (the _pid placeholder in format string)
            if payload.startswith("%d "):
                payload = payload[3:].lstrip()

            # Classify
            if payload.startswith("CALL "):
                # Example: CALL oceos_task_create %d %d createRC
                parts = payload.split()
                api = parts[1]
                # retvar is last token if it's an identifier
                retvar = None
                if parts and re.fullmatch(r"[A-Za-z_]\w*", parts[-1] or ""):
                    retvar = parts[-1]
                steps.append(Step(kind="call", api=api, args=args, retvar=retvar, raw=ln))
            elif payload.startswith("SCALAR "):
                # SCALAR resumeRC %d  with args like [resumeRC]
                parts = payload.split()
                name = parts[1] if len(parts) > 1 else None
                steps.append(Step(kind="scalar", name=name, args=args, raw=ln))
            elif payload.startswith("ASSERT_EQ "):
                # ASSERT_EQ %d %d Label; args: [actual, expected]
                # Try to capture trailing label from format string (after the two %d)
                label = None
                try:
                    # e.g., "ASSERT_EQ %d %d TaskCreated" -> label "TaskCreated"
                    tokens = payload.split()
                    if len(tokens) >= 4:
                        label = tokens[3]
                except Exception:
                    label = None
                steps.append(Step(kind="assert_eq", args=args, label=label, raw=ln))
            elif payload.startswith("SYNC "):
                steps.append(Step(kind="sync", raw=ln))
            elif payload.startswith("DEFINE "):
                steps.append(Step(kind="define", raw=ln))
            elif payload.startswith("DECL "):
                parts = payload.split()
                # DECL byte createRC  → name at end
                name = parts[-1] if parts else None
                steps.append(Step(kind="decl", name=name, raw=ln))
            elif payload.startswith("SCENARIO "):
                # scenario marker with name as first arg
                # args will have [ScenarioName]
                scen_name = (args[0] if args else "")
                steps.append(Step(kind="scenario", name=scen_name, raw=ln))
            elif payload.startswith("LOG ") or payload.startswith("TASK "):
                steps.append(Step(kind="log", raw=ln))
            else:
                steps.append(Step(kind="other", raw=ln))
        return steps

    def generate_unity_code(self, steps: List[Step], test_number: int) -> str:
        pre = self.preamble_file.read_text(encoding="utf-8") if self.preamble_file.exists() else ""
        post = self.postamble_file.read_text(encoding="utf-8") if self.postamble_file.exists() else ""
        run_tmpl = self.run_file.read_text(encoding="utf-8") if self.run_file.exists() else ""

        # Split by scenarios: if no scenario markers, use one scenario with index test_number
        scenarios: List[Dict[str, Any]] = []
        current: Dict[str, Any] = {"name": f"Scenario_{test_number}", "steps": []}
        for st in steps:
            if st.kind == "scenario":
                # start a new segment
                if current["steps"]:
                    scenarios.append(current)
                scen_display = st.name or f"Scenario_{len(scenarios)}"
                current = {"name": scen_display, "steps": []}
            else:
                current["steps"].append(st)
        if current["steps"]:
            scenarios.append(current)
        if not scenarios:
            scenarios = [{"name": f"Scenario_{test_number}", "steps": steps}]

        # Emit runners per scenario and corresponding test functions
        bodies: List[str] = []
        run_funcs: List[str] = []
        for idx, scen in enumerate(scenarios):
            runner_name = f"OceosModelTaskMgr_Run_{idx}"
            bodies.append(self._emit_runner_function(scen["steps"], idx, runner_name))
            # Instantiate run template for this scenario index
            run_funcs.append(run_tmpl.format(idx))

        return "\n".join([
            pre.rstrip(),
            "\n\n".join(bodies).rstrip(),
            "\n".join(run_funcs).rstrip(),
            post.rstrip(),
        ]) + "\n"

    def _emit_runner_function(self, steps: List[Step], scenario_index: int, runner_name: str) -> str:
        # Signature mirrors the test runner call in tc-task-mgr-run.h
        sig = (
            f"void {runner_name}(\n"
            "    enum DIRECTIVE_STATUS (*TaskCreate)(\n"
            "        unsigned int, unsigned char, unsigned char, unsigned char, bool, bool,\n"
            "        void (*)(void *), void (*)(void *), unsigned int, unsigned int),\n"
            "    enum DIRECTIVE_STATUS (*TaskStart)(unsigned int),\n"
            "    enum DIRECTIVE_STATUS (*TaskDelete)(unsigned int),\n"
            "    enum DIRECTIVE_STATUS (*TaskSuspend)(unsigned int),\n"
            "    enum DIRECTIVE_STATUS (*TaskResume)(unsigned int),\n"
            "    enum DIRECTIVE_STATUS (*TaskSetPriority)(unsigned int, unsigned char, unsigned char *)\n"
            ")\n{\n"
        )

        # name -> (ctype, init)
        decls: Dict[str, Tuple[str, str | None]] = {}
        idents_needed: Set[str] = set()
        lines: List[str] = []

        def ensure_decl(name: str, ctype: str, init: str | None = None) -> None:
            if not name:
                return
            if name not in decls:
                decls[name] = (ctype, init)

        def collect_ident(arg: str) -> None:
            if not arg:
                return
            if re.fullmatch(r"\d+", arg):
                return
            if arg in {"NULL", "true", "false"}:
                return
            idents_needed.add(arg)

        # First pass: collect identifiers from args
        for st in steps:
            if st.kind == "call" and st.args:
                for a in st.args:
                    collect_ident(a)

        # Heuristic type mapping for identifiers
        for nm in sorted(idents_needed):
            lname = nm.lower()
            if lname.endswith("_id") or lname.endswith("id"):
                ensure_decl(nm, "unsigned int", "0u")
            elif "prio" in lname or "priority" in lname:
                ensure_decl(nm, "unsigned char", "0")
            else:
                ensure_decl(nm, "unsigned int", "0u")

        # Always present
        ensure_decl("old_prio", "unsigned char", "0")

        for st in steps:
            if st.kind == "call" and st.api:
                api = st.api
                args = st.args or []
                rv = st.retvar or (f"{api}RC")

                if api == "setTask":
                    tid = args[0] if len(args) > 0 else "1"
                    lines.append(f"    OceosTest_SetTask({tid});")
                    continue
                if api == "WaitForSuspend":
                    tid = args[0] if len(args) > 0 else "1"
                    lines.append(f"    (void)OceosTest_WaitForSuspend({tid}, 1000u);")
                    continue

                if api == "oceos_task_create":
                    ensure_decl(rv, "enum DIRECTIVE_STATUS")
                    tid = args[0] if len(args) > 0 else "1"
                    prio = args[1] if len(args) > 1 else "10"
                    lines.append(f"    {rv} = TaskCreate({tid}, (unsigned char){prio}, (unsigned char){prio}, 1, false, true, NULL, NULL, 0u, 0u);")
                elif api == "oceos_task_start":
                    ensure_decl(rv, "enum DIRECTIVE_STATUS")
                    tid = args[0] if len(args) > 0 else "1"
                    lines.append(f"    {rv} = TaskStart({tid});")
                elif api == "oceos_task_delete":
                    ensure_decl(rv, "enum DIRECTIVE_STATUS")
                    tid = args[0] if len(args) > 0 else "1"
                    lines.append(f"    {rv} = TaskDelete({tid});")
                elif api == "oceos_task_suspend":
                    ensure_decl(rv, "enum DIRECTIVE_STATUS")
                    tid = args[0] if len(args) > 0 else "1"
                    lines.append(f"    {rv} = TaskSuspend({tid});")
                elif api == "oceos_task_resume":
                    ensure_decl(rv, "enum DIRECTIVE_STATUS")
                    tid = args[0] if len(args) > 0 else "1"
                    lines.append(f"    {rv} = TaskResume({tid});")
                elif api == "oceos_task_set_priority":
                    ensure_decl(rv, "enum DIRECTIVE_STATUS")
                    tid = args[0] if len(args) > 0 else "1"
                    newp = args[1] if len(args) > 1 else "10"
                    lines.append(f"    {rv} = TaskSetPriority({tid}, (unsigned char){newp}, &old_prio);")
                else:
                    lines.append(f"    /* Unmapped CALL {api} */;")
            elif st.kind == "assert_eq":
                # args: [actual, expected]
                actual = st.args[0] if st.args and len(st.args) > 0 else "0"
                expected = st.args[1] if st.args and len(st.args) > 1 else "0"
                lines.append(f"    TEST_ASSERT_EQUAL_INT((int)({expected}), (int)({actual}));")
            elif st.kind == "scalar":
                # Keep scalar as comment for now
                nm = st.name or "var"
                lines.append(f"    /* SCALAR {nm} observed */;")
            elif st.kind in ("log", "sync", "define", "decl", "other"):
                # Omit or keep brief comment
                pass

        # Emit declarations at top
        decl_lines: List[str] = []
        for name, (ctype, init) in decls.items():
            if init is not None:
                decl_lines.append(f"    {ctype} {name} = {init};")
            else:
                decl_lines.append(f"    {ctype} {name};")
        body = "\n".join(decl_lines + lines) if (decl_lines or lines) else "    /* No actionable steps parsed */\n"

        return sig + body + "}\n"


def main(test_number, unused_arg, model_root, preamble_file, postamble_file, 
         run_file, refine_file, output_file):
    """Main function for generating OCEOS Unity tests"""
    
    generator = OceosUnityGenerator(
        model_root, preamble_file, postamble_file, run_file, refine_file
    )
    
    generator.generate_test(test_number, output_file)
    print(f"Generated Unity test: {output_file}")


if __name__ == '__main__':
    import sys
    if len(sys.argv) != 8:
        print("Usage: spin2test_oceos.py test_number unused model_root preamble postamble run refine output")
        sys.exit(1)
    
    main(*sys.argv[1:])
