# SPDX-License-Identifier: BSD-2-Clause
"""SPIN trace to OCEOS Unity test converter CLI and generator glue"""

import argparse
import sys
from pathlib import Path

# Ensure 'src' is on sys.path for package imports
ROOT = Path(__file__).resolve().parent
SRC_DIR = ROOT / "src"
if str(SRC_DIR) not in sys.path:
    sys.path.insert(0, str(SRC_DIR))

from spin2test_oceos import OceosUnityGenerator  # type: ignore


def parse_args(argv: list[str]) -> argparse.Namespace:
    p = argparse.ArgumentParser(description="Promela to OCEOS Unity Test Generator")
    p.add_argument("model_root", help="Model filename root (e.g., oceos-task-mgr-model)")
    p.add_argument("preamble", help="Path to preamble header")
    p.add_argument("postamble", help="Path to postamble header")
    p.add_argument("runfile", help="Path to runfile header")
    p.add_argument("refine", help="Path to refine-config YAML")
    p.add_argument("output", help="Output Unity C file path")
    p.add_argument("--spin-trace", required=True, help="Path to SPIN .spn trace file")
    p.add_argument("--test-number", default="0", help="Test number / trail index")
    return p.parse_args(argv)


def main(argv: list[str]) -> int:
    ns = parse_args(argv)

    gen = OceosUnityGenerator(
        model_root=ns.model_root,
        preamble_file=ns.preamble,
        postamble_file=ns.postamble,
        run_file=ns.runfile,
        refine_file=ns.refine,
    )

    gen.generate_test(
        test_number=int(ns.test_number),
        output_file=ns.output,
        spin_trace_path=ns.spin_trace,
    )

    print(f"Generated Unity test: {ns.output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
