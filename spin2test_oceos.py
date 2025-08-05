# SPDX-License-Identifier: BSD-2-Clause
"""SPIN trace to OCEOS Unity test converter"""

# Copyright (C) 2025 Trinity College Dublin (www.tcd.ie)
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

import src.spin2test_oceos

import argparse

if __name__ == '__main__':
    claparser = argparse.ArgumentParser(
        description="Promela to OCEOS Unity Test Generator")
    claparser.add_argument("root", help="Model filename root")
    claparser.add_argument("pre_amble", help="Model pre-amble file")
    claparser.add_argument("post_amble", help="Model post-amble file")
    claparser.add_argument("run", help="Model test run file")
    claparser.add_argument("refine", help="Model test refine file")
    claparser.add_argument("testfile", help="Model helper file")
    claparser.add_argument("tstno", help="Model test number")

    cl_args = claparser.parse_args()
    src.spin2test_oceos.main(cl_args.tstno, '', cl_args.root, cl_args.pre_amble,
                       cl_args.post_amble, cl_args.run, cl_args.refine,
                       cl_args.testfile)
