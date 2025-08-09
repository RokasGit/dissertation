#!/usr/bin/env python3
# SPDX-License-Identifier: BSD-2-Clause
"""OCEOS formal test generation using SPIN model checker and Unity framework"""

# Copyright (C) 2025 Trinity College Dublin (www.tcd.ie)
#               Andrew Butterfield
#               Rokas Paulauskas
#
# Redistribution and use in source and binary forms, with or without
# modification, are permitted provided that the following conditions
# are met:
# 1. Redistributions of source code must retain the above copyright
#    notice, this list of conditions and the following disclaimer.
# 2. Redistributions in binary form must reproduce the above copyright
#    notice, this list of conditions and the following disclaimer in the
#    documentation and/or other materials provided with the distribution.
#
# THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
# AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
# IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
# ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE
# LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
# CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
# SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
# INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
# CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
# ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
# POSSIBILITY OF SUCH DAMAGE.

import argparse
import os
import shutil
import subprocess
import sys
import textwrap
from pathlib import Path
from typing import Dict

try:
    import yaml  # type: ignore
except Exception:  # pragma: no cover - best effort import
    yaml = None  # type: ignore


ROOT = Path(__file__).resolve().parent
MODELS_DIR = ROOT / "models"
TESTS_UNITY_DIR = ROOT / "tests" / "unity"
CONFIG_FILE = ROOT / "testbuilder_oceos.yml"
ERROR_LOG = MODELS_DIR / "errors.log"


def _read_yaml(path: Path) -> Dict:
    if not path.exists():
        return {}
    with path.open("r", encoding="utf-8") as f:
        return yaml.safe_load(f) if yaml else {}


def _write_text(path: Path, data: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8", newline="\n") as f:
        f.write(data)


def _run(cmd, cwd: Path | None = None, stdout=None, stderr=None) -> subprocess.CompletedProcess:
    cp = subprocess.run(
        cmd,
        cwd=str(cwd) if cwd else None,
        stdout=stdout,
        stderr=stderr,
        text=True,
        shell=False,
        check=False,
    )
    return cp


def _load_model_registry() -> Dict[str, str]:
    cfg = _read_yaml(CONFIG_FILE)
    modelsfile = cfg.get("modelsfile")
    if modelsfile:
        models_yaml = Path(modelsfile)
    else:
        models_yaml = MODELS_DIR / "models.yml"
    models = _read_yaml(models_yaml)
    return models or {}


def _find_model(model_name: str, model_registry: Dict[str, str]) -> tuple[Path, str]:
    if model_name not in model_registry:
        raise SystemExit(f"Unknown model '{model_name}'. Check models/models.yml")
    rel = model_registry[model_name]
    # rel like 'task-mgr/oceos-task-mgr-model'
    model_dir = MODELS_DIR / Path(rel).parent
    model_root = Path(rel).name
    model_pml = model_dir / f"{model_root}.pml"
    return model_pml, model_root


def _get_out_c_path(model_name: str) -> Path:
    registry = _load_model_registry()
    _model_pml, model_root = _find_model(model_name, registry)
    return TESTS_UNITY_DIR / f"tc-{model_root}.c"


def cmd_spin(model_name: str) -> Path:
    """Run SPIN → pan → produce .spn for model; returns .spn path."""
    cfg = _read_yaml(CONFIG_FILE)
    modelsfile = cfg.get("modelsfile")
    if modelsfile:
        # Allow absolute override; else use local models/models.yml
        models_yaml = Path(modelsfile)
    else:
        models_yaml = MODELS_DIR / "models.yml"

    models = _read_yaml(models_yaml)
    model_registry: Dict[str, str] = models or {}

    model_pml, model_root = _find_model(model_name, model_registry)
    model_dir = model_pml.parent

    if not model_pml.exists():
        raise SystemExit(f"Model file not found: {model_pml}")

    # Ensure gen dir
    gen_dir = model_dir / "gen"
    gen_dir.mkdir(parents=True, exist_ok=True)

    # 1) spin -a <model>
    cp = _run(["spin", "-a", model_pml.name], cwd=model_dir, stderr=subprocess.PIPE)
    if cp.returncode != 0:
        _write_text(ERROR_LOG, cp.stderr or "")
        raise SystemExit("SPIN failed. See models/errors.log")

    pan_c = model_dir / "pan.c"
    if not pan_c.exists():
        _write_text(ERROR_LOG, cp.stderr or "pan.c not generated")
        raise SystemExit("SPIN did not generate pan.c. See models/errors.log")

    # 2) gcc -o pan pan.c
    gcc = ["gcc", "-std=gnu99", "-O", "-DTEST_GEN", "-o", "pan", "pan.c"]
    cp = _run(gcc, cwd=model_dir, stderr=subprocess.PIPE)
    if cp.returncode != 0:
        _write_text(ERROR_LOG, cp.stderr or "")
        raise SystemExit("Failed to compile pan.c. See models/errors.log")

    pan_exe = model_dir / ("pan.exe" if sys.platform.startswith("win") else "pan")

    # 3) run pan and capture output
    spin_opts = cfg.get("spinallscenarios", "-DTEST_GEN -e -c0").split()
    spn_path = gen_dir / f"{model_root}-0.spn"
    with spn_path.open("w", encoding="utf-8", newline="\n") as out:
        cp = _run([str(pan_exe), *spin_opts], cwd=model_dir, stdout=out, stderr=subprocess.PIPE)
    if cp.returncode not in (0, 1):  # pan can return 1 for errors found
        _write_text(ERROR_LOG, cp.stderr or "")
        raise SystemExit("pan execution failed. See models/errors.log")

    return spn_path


def cmd_gentests(model_name: str, spn_path: Path | None = None) -> Path:
    cfg = _read_yaml(CONFIG_FILE)
    models_yaml = Path(cfg.get("modelsfile", MODELS_DIR / "models.yml"))
    model_registry: Dict[str, str] = _read_yaml(models_yaml) or {}

    model_pml, model_root = _find_model(model_name, model_registry)
    model_dir = model_pml.parent

    # Prepare inputs
    pre = model_dir / "tc-task-mgr-pre.h"
    post = model_dir / "tc-task-mgr-post.h"
    run = model_dir / "tc-task-mgr-run.h"
    refine = ROOT / "refine-config-oceos.yml"

    # Default spn path
    if spn_path is None:
        spn_path = model_dir / "gen" / f"{model_root}-0.spn"

    out_c = TESTS_UNITY_DIR / f"tc-{model_root}.c"
    TESTS_UNITY_DIR.mkdir(parents=True, exist_ok=True)

    # Call converter using current Python
    converter = ROOT / "spin2test_oceos.py"
    pyexe = sys.executable
    args = [
        pyexe,
        str(converter),
        model_root,
        str(pre),
        str(post),
        str(run),
        str(refine),
        str(out_c),
        "--spin-trace",
        str(spn_path),
        "--test-number",
        "0",
    ]
    cp = _run(args, cwd=ROOT, stderr=subprocess.PIPE)
    if cp.returncode != 0:
        msg = cp.stderr or "spin2test conversion failed"
        _write_text(ERROR_LOG, str(msg))
        raise SystemExit("spin2test_oceos failed. See models/errors.log")

    return out_c


def cmd_copy(model_name: str, generated_c: Path) -> Path | None:
    """Copy generated test into OCEOS native tests folder and scaffold makefile and runner."""
    cfg = _read_yaml(CONFIG_FILE)
    oceos_root = Path(cfg.get("oceos", "")).resolve() if cfg.get("oceos") else None
    if not oceos_root or not oceos_root.exists():
        print("[COPY] OCEOS root not configured or not found; skipping copy.")
        return None

    dest_dir = oceos_root / "test" / "common" / "formal_task_mgr_test"
    dest_dir.mkdir(parents=True, exist_ok=True)

    # Copy the generated test
    dest_c = dest_dir / "formal_task_mgr_test.c"
    shutil.copyfile(generated_c, dest_c)

    # Extract test function names
    txt = generated_c.read_text(encoding="utf-8", errors="ignore")
    import re as _re
    tests = _re.findall(r"^void\s+(test_OceosTaskMgr_Scenario_\d+)\s*\(\s*void\s*\)\s*\{", txt, flags=_re.M)
    if not tests:
        # fallback to single known test
        tests = ["test_OceosTaskMgr_Scenario_0"]

    # Scaffold a runner that calls discovered tests
    runner = dest_dir / "formal_task_mgr_test_Runner.c"
    if not runner.exists():
        lines = [
            "#include \"unity.h\"",
            "extern void setUp(void);",
            "extern void tearDown(void);",
        ]
        lines += [f"extern void {t}(void);" for t in tests]
        lines += [
            "int main(void)",
            "{",
            "    UnityBegin(\"formal_task_mgr_test.c\");",
        ]
        for t in tests:
            lines.append(f"    RUN_TEST({t}, __LINE__);")
        lines += [
            "    return UnityEnd();",
            "}",
        ]
        _write_text(runner, "\n".join(lines) + "\n")

    # Scaffold a makefile if missing
    mk = dest_dir / "makefile"
    if not mk.exists():
        mk_text = textwrap.dedent(
            """
            # Auto-generated formal test makefile
            UNIT_TEST_SINGLE = formal_task_mgr_test.exe
            LOCATION_OFFSET = ../../

            export $(UNIT_TEST_SINGLE)
            export $(LOCATION_OFFSET)

            include $(LOCATION_OFFSET)makefile.mk

            formal_task_mgr_test: test
            formal_task_mgr_build_test: test_build_only

            .PHONY: formal_task_mgr_test
            .PHONY: formal_task_mgr_build_test
            """
        ).strip() + "\n"
        _write_text(mk, mk_text)

    print(f"[COPY] Installed test at: {dest_c}")
    return dest_c


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(
        prog="testbuilder_oceos.py",
        description="Generate Unity tests from OCEOS Promela models",
    )
    parser.add_argument("command", choices=["help", "spin", "gentests", "allsteps", "copy"], help="Action")
    parser.add_argument("model", nargs="?", default="task-mgr", help="Model name (from models.yml) or allmodels")
    args = parser.parse_args(argv)

    if args.command == "help":
        help_file = ROOT / "testbuilder_oceos.help"
        if help_file.exists():
            print(help_file.read_text(encoding="utf-8"))
        else:
            print("Run: python testbuilder_oceos.py allsteps task-mgr")
        return 0

    if args.model == "allmodels":
        registry: Dict[str, str] = _load_model_registry()
        names = sorted(registry.keys())
    else:
        names = [args.model]

    last_output: Path | None = None

    for name in names:
        spn: Path | None = None
        if args.command in ("spin", "allsteps"):
            print(f"[SPIN] Generating trace for model: {name}")
            try:
                spn = cmd_spin(name)
            except SystemExit as e:
                print(e, file=sys.stderr)
                return 2

        if args.command in ("gentests", "allsteps"):
            print(f"[GEN] Converting trace to Unity C: {name}")
            try:
                out = cmd_gentests(name, spn)
                last_output = out
            except SystemExit as e:
                print(e, file=sys.stderr)
                return 3

        if args.command in ("copy", "allsteps"):
            try:
                # If we don't have a freshly generated output, try to locate existing one
                if not last_output:
                    candidate = _get_out_c_path(name)
                    if not candidate.exists():
                        print(f"[COPY] No generated test found at {candidate}; run 'gentests' first.")
                        continue
                    last_output = candidate
                cmd_copy(name, last_output)
            except SystemExit as e:
                print(e, file=sys.stderr)
                # don't fail entire build on copy issues

    if last_output:
        print(f"Generated: {last_output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
