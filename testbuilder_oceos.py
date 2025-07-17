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

import sys
import os
import subprocess
import glob
import shutil
from functools import wraps
import yaml
from pathlib import Path
from datetime import datetime


def catch_subprocess_errors(func):
    @wraps(func)
    def wrapper(*args, **kwargs):
        try:
            result = func(*args, **kwargs)
        except subprocess.CalledProcessError as e:
            print(f"error executing: {e.cmd}")
            sys.exit(1)
        return result
    return wrapper

def all_steps(models, model_to_path, source_dir):
    if models == ["allmodels"]:
        models = list(model_to_path.keys())

    for model_name in models:
        path = model_to_path[model_name]
        config = get_config(source_dir, model_name)
        model_to_roots = get_model_roots(config)
        model_root = model_to_roots[model_name]
        refine_config = get_refine_config(source_dir, 
                                          model_name, path, model_root)
        
        clean(model_name, model_to_path, model_to_roots, source_dir)
        generate_spin_files(model_name, path, model_root,
                            config["spinallscenarios"],
                            refine_config)
        genpath = Path("gen", path)
        generate_test_files(model_name, genpath, model_root, 
                            config["spin2test"], refine_config)
        copy_oceos_tests(model_root, genpath, config["testcode"], 
                        config["oceos"], config["testyaml"], 
                        config["testsuite"], refine_config["testfiletype"])

    compile_oceos(config["oceos"])
    run_oceos_tests("", "", "", config["testsuite"])

def clean(model_name, model_to_path, model_to_roots, source_dir):
    """Cleans out generated files in <model_name> directory"""
    cwd = os.getcwd()
    if model_name == "allmodels":
        models = list(model_to_path.keys())
    else:
        models = [model_name]
    for model_name in models:
        model_dir = model_to_path[model_name]
        model_root = model_to_roots[model_name]
        config = get_config(source_dir, model_name)
        refine_config = get_refine_config(source_dir, 
                                          model_name, model_dir, model_root)
        os.chdir(Path(model_dir,"gen"))
        print(f"Removing spin and test files for {model_name}")
        files = get_generated_files(model_root, config["testsuite"],
                                    refine_config["testfiletype"])
        for file in files:
            if os.path.exists(file):
                os.remove(file)
    os.chdir(cwd)

def archive(model_name, model_dir, model_root, testsuite, test_extension):
    cwd = os.getcwd()
    os.chdir(Path(model_dir,"gen"))
    print(f"Archiving spin and test files for {model_name}")
    files = get_generated_files(model_name, testsuite, test_extension)
    date = datetime.now().strftime("%Y%m%d-%H%M%S")
    archive_dir = Path(f"archive/{date}")
    archive_dir.mkdir(parents=True, exist_ok=True)
    for file in files:
        if os.path.exists(file):
            shutil.copy2(file, archive_dir)
    print(f"Files archived to {archive_dir}")
    os.chdir(cwd)

def ready_to_generate(model_root, refine_config):
    """Checks if relevant files are in place for spin and test generation"""
    ready = True
    fname = f"{model_root}.pml"
    if not os.path.isfile(fname):
        print(f"Promela file '{fname}' does not exist")
        ready = False
    fname = f"{refine_config['preamble']}"
    if not os.path.isfile(fname):
        print(f"Preconditions file '{fname}' does not exist")
        ready = False
    fname = f"{refine_config['postamble']}"
    if not os.path.isfile(fname):
        print(f"Postconditions file '{fname}' does not exist")
        ready = False
    fname = f"{refine_config['runfile']}"
    if not os.path.isfile(fname):
        print(f"Unity runner file '{fname}' does not exist")
        ready = False
    fname = f"{refine_config['refinefile']}"
    if not os.path.isfile(fname):
        print(f"Refinement file '{fname}' does not exist")
        ready = False
    return ready

@catch_subprocess_errors
def generate_spin_files(model_name, model_dir, model_root,
                       spinallscenarios, refine_config):
    """Create spin files from model_name"""
    cwd = os.getcwd()
    os.chdir(model_dir)
    if not ready_to_generate(model_root, refine_config):
        sys.exit(1)
    
    # Remove any old SPIN output so that our -a will regenerate pan.c/pan.h
    for f in ("pan", "pan.c", "pan.h", "pan.m", "pan.t", "pan.b", "pan.p"):
        try: 
            os.remove(f)
        except OSError: 
            pass
    
    print(f"Generating spin files for {model_name}")
    # Ensure -a flag is included to regenerate verifier
    if "-a" not in spinallscenarios:
        spinallscenarios = f"-a {spinallscenarios}"
    # Add warning suppression to reduce noise (optional)
    if "-w" not in spinallscenarios:
        spinallscenarios = f"-w {spinallscenarios}"
    subprocess.run(f"spin {spinallscenarios} {model_root}.pml",
                   check=True, shell=True)
    no_of_trails = len(glob.glob(f"{model_root}*.trail"))
    if no_of_trails == 0:
        print("no trail files generated")
    else:
        print(f"{no_of_trails} trail files generated")
        for i in range(no_of_trails):
            subprocess.run(f"spin -T -t{i+1} {model_root}.pml > gen/{model_root}-{i}.spn",
                           check=True, shell=True)
            subprocess.run( 
                f"mv {model_root}.pml{i+1}.trail gen/{model_root}.pml{i+1}.trail",
                check=True, shell=True )
    if os.path.exists('pan'):
        os.remove('pan')
    os.chdir(cwd)

@catch_subprocess_errors
def generate_test_files(model_name, model_dir, model_root, 
                        testgen, refine_config):
    """Create Unity test files from spin files"""
    cwd = os.getcwd()
    print(f"model_dir is {model_dir}.")
    os.chdir(model_dir)
    if not ready_to_generate(model_root, refine_config):
        sys.exit(1)
    print(f"Generating Unity test files for {model_name}")
    no_of_trails = len(glob.glob(f"gen/{model_root}*.trail"))
    if no_of_trails == 0:
        print("no trail files found")
    else:
        for i in range(no_of_trails):
            test_file = f"tr-{model_root}-{i}{refine_config['testfiletype']}"
            subprocess.run(f"python {testgen} {model_root} "
                           f"{refine_config['preamble']} "
                           f"{refine_config['postamble']} "
                           f"{refine_config['runfile']} "
                           f"{refine_config['refinefile']} "
                           f"{test_file} {i}",
                           check=True, shell=True)

    generate_unity_testcase_file(model_root, refine_config, no_of_trails)
    os.chdir(cwd)

def generate_unity_testcase_file(model_root, refine_config, no_of_trails):
    """Generate Unity test case file with proper Unity framework structure"""
    missing_files = list()
    for key in ["testcase_preamble", "testcase_runfile", "testcase_postamble"]:
        if not Path(refine_config[key]).exists():
            missing_files.append(refine_config[key])

    if not missing_files:
        file_name = f"tc-{model_root}{refine_config['testfiletype']}"
        with open(file_name, "w") as f:
            # Unity test case structure
            preamble = Path(refine_config["testcase_preamble"]).read_text()
            f.write(preamble)
            
            # Generate individual test functions
            run = Path(refine_config["testcase_runfile"]).read_text()
            for i in range(no_of_trails):
                f.write(run.format(i))

            postamble = Path(refine_config["testcase_postamble"]).read_text()
            f.write(postamble)
    else:
        for file in missing_files:
            print(f"File not found: {file}")
        print(f"tc-{model_root}{refine_config['testfiletype']} "
              f"will not be generated")

def copy_oceos_tests(model_root, model_path, codedir, oceos, modfile, 
                    testsuite_name, test_file_extension):
    """Copies Unity test files to OCEOS test directory"""
    cwd = os.getcwd()
    os.chdir(model_path)

    # Remove old test files
    print(f"Removing old files for {model_root}")
    files = glob.glob(f"{codedir}tr-{model_root}-model*{test_file_extension}")
    files += glob.glob(f"{codedir}tr-{model_root}-model*.h")
    files += glob.glob(f"{codedir}tc-{model_root}-model{test_file_extension}")
    for file in files:
        if os.path.exists(file):
            os.remove(file)

    # Copy new test files
    print(f"Copying new Unity test files for {model_root}")

    # Ensure destination directory exists
    unity_test_dir = f"{oceos}tests/unity"
    os.makedirs(unity_test_dir, exist_ok=True)

    # Copy fixed model_root top-level files
    fixedhfiles = glob.glob(f"tr-{model_root}.h")
    fixedcfiles = glob.glob(f"tc-{model_root}{test_file_extension}")
    fixedcfiles += glob.glob(f"tr-{model_root}{test_file_extension}")
    fixedfiles = fixedhfiles + fixedcfiles
    for file in fixedfiles:
        if os.path.exists(file):
            shutil.copyfile(file, f"{oceos}tests/unity/{file}")

    # Copy files common to all models
    os.chdir("../../common")
    commoncfiles = glob.glob(f"tx*{test_file_extension}")
    commonhfiles = glob.glob(f"tx*.h")
    commonfiles = commonhfiles + commoncfiles 
    for file in commonfiles:
        if os.path.exists(file):
            shutil.copyfile(file, f"{oceos}tests/unity/{file}")
    os.chdir(model_path)

    # Copy per-scenario test runners
    os.chdir("gen")
    genfiles = glob.glob(f"tr-{model_root}-*{test_file_extension}")
    os.chdir("..")
    for file in genfiles:
        if os.path.exists(f"gen/{file}"):
            shutil.copyfile(f"gen/{file}", f"{oceos}tests/unity/{file}")

    # Update Unity test suite configuration
    print(f"Updating Unity test suite for {model_root}")
    update_unity_config(modfile, model_root, fixedcfiles, commoncfiles, genfiles)
    os.chdir(cwd)

def update_unity_config(modfile, model_root, fixedcfiles, commoncfiles, genfiles):
    """Update Unity test configuration file"""
    try:
        with open(modfile) as file:
            model_yaml = yaml.load(file, Loader=yaml.FullLoader)
    except FileNotFoundError:
        model_yaml = {'tests': []}
    
    # Update test sources list
    source_list = model_yaml.get('tests', [])
    source_set = set(source_list)
    
    for file in commoncfiles:
        source_set.add(f"tests/unity/{file}")
    for file in fixedcfiles:
        source_set.add(f"tests/unity/{file}")
    for file in genfiles:
        source_set.add(f"tests/unity/{file}")
    
    new_list = list(source_set)
    model_yaml['tests'] = sorted(new_list)
    
    with open(modfile, 'w') as file:
        yaml.dump(model_yaml, file)

@catch_subprocess_errors
def compile_oceos(oceos_dir):
    """Compile OCEOS with Unity tests using make orchestration"""
    cwd = os.getcwd()
    os.chdir(oceos_dir)
    print("Compiling OCEOS with Unity tests...")
    # Use OCEOS-specific build command pattern
    subprocess.run("make test_build_only BSP=pm698 SPARC=1 TOOLCHAIN=gcc", 
                   check=True, shell=True)
    os.chdir(cwd)

@catch_subprocess_errors
def run_oceos_tests(test_runner, test_args, testexe, testsuite):
    """Run OCEOS Unity tests with @@@ annotation parsing"""
    print(f"Running OCEOS Unity tests...")
    result = subprocess.run("make oceos_test BSP=pm698 SPARC=1 TOOLCHAIN=gcc",
                           check=True, shell=True, capture_output=True, text=True)
    
    # Parse @@@ annotations from output
    lines = result.stdout.split('\n')
    with open(f"{testsuite}-test.log", 'w') as log:
        for line in lines:
            log.write(line + '\n')
            if line.strip().startswith('@@@ '):
                print(f"ANNOTATION: {line.strip()}")

def get_generated_files(model_root, testsuite, test_extension):
    trails = glob.glob(f"{model_root}*.trail")
    files = trails
    files += glob.glob(f"{model_root}*.spn")
    files += glob.glob(f"tc-{model_root}{test_extension}")
    if len(trails) == 1:
        files += glob.glob(f"tr-{model_root}-0{test_extension}")
    else:
        files += glob.glob(f"tr-{model_root}-*{test_extension}")
    files += glob.glob(f"{testsuite}-test.log")
    return files

def get_model_paths(config):
    models_file = Path(config["modelsfile"])
    model_to_absolute_path = dict()
    if models_file.exists():
        with open(models_file) as file:
            model_to_relative_path = yaml.load(file, Loader=yaml.FullLoader)
        for model_name, model_path in model_to_relative_path.items():
            relative_path = Path(model_path)
            absolute_path = Path(models_file.parent / relative_path.parent)
            model_to_absolute_path[model_name] = absolute_path
    else:
        print(f"modelsfile not found {models_file}")
        raise SystemExit()

    return model_to_absolute_path

def get_model_roots(config):
    models_file = Path(config["modelsfile"])
    model_to_roots = dict()
    if models_file.exists():
        with open(models_file) as file:
            model_to_relative_path = yaml.load(file, Loader=yaml.FullLoader)
        for model_name, model_path in model_to_relative_path.items():
            relative_path = Path(model_path)
            pathsplit = os.path.split(relative_path)
            root = pathsplit[1]
            model_to_roots[model_name] = root
    else:
        print(f"modelsfile not found {models_file}")
        raise SystemExit()

    return model_to_roots

def get_config(source_dir, model_name=""):
    config = dict()
    with open(f"{source_dir}/testbuilder_oceos.yml") as file:
        global_config = yaml.load(file, Loader=yaml.FullLoader)
        for key, val in global_config.items():
            config[key] = val
    if model_name and model_name != "allmodels":
        model_to_path = get_model_paths(config)
        model_path = model_to_path[model_name]
        local_config_path = Path(model_path / "testbuilder_oceos.yml")
        if Path(local_config_path).exists():
            with open(local_config_path) as file:
                local_config = yaml.load(file, Loader=yaml.FullLoader)
                if local_config:
                    for key, val in local_config.items():
                        config[key] = val
    if "testsuite" not in config.keys():
        config["testsuite"] = "model-0"
    missing_keys = {
                    "spin2test", "modelsfile", "oceos", "test_runner", 
                    "testyamldir", "testcode", "testexedir", "test_args",
                    "spinallscenarios"
                    } - config.keys()
    if missing_keys:
        print("testbuilder_oceos.yml configuration is incomplete")
        print("The following configuration items are missing:")
        for key in missing_keys:
            print(key)
        sys.exit(1)
    config["testyaml"] = f"{config['testyamldir']}{config['testsuite']}.yml"
    config["testexe"] = f"{config['testexedir']}test-{config['testsuite']}.exe"
    return config

def get_refine_config(source_dir, model_name, model_dir, model_root):
    refine_config = dict()
    with open(f"{source_dir}/refine-config-oceos.yml") as file:
        global_config = yaml.load(file, Loader=yaml.FullLoader)
        for key, val in global_config.items():
            refine_config[key] = val
    if Path(f"{model_dir}/refine-config-oceos.yml").exists():
        with open(f"{model_dir}/refine-config-oceos.yml") as file:
            local_config = yaml.load(file, Loader=yaml.FullLoader)
            if local_config:
                for key, val in local_config.items():
                    refine_config[key] = val
    missing_keys = {
                       "preamble", "postamble", "refinefile", "testfiletype",
                       "runfile", "testcase_preamble", "testcase_postamble",
                       "testcase_runfile"
                    } - refine_config.keys()
    if missing_keys:
        print("refine-config-oceos.yml configuration is incomplete")
        print("The following configuration items are missing:")
        for key in missing_keys:
            print(key)
        sys.exit(1)
    # Note: File paths should be used as-is from configuration
    # No need to prepend model_root since paths are already relative to project root
    return refine_config

def check_models_exist(modelnames, model_to_path, config):
    if modelnames == ["allmodels"]:
        return True
    else:
        all_models_exist = True
        for model_name in modelnames:
            if model_name not in model_to_path.keys():
                all_models_exist = False
                print(f"{model_name} not found in model_name file")
        if not all_models_exist:
            print(f"\nChoose model(s) from: ")
            for key in model_to_path.keys():
                print(key)
            print(f"\nOr update {config['modelsfile']}")
            raise SystemExit(1)

def main():
    """generates and deploys Unity tests from Promela models for OCEOS"""
    source_dir = os.path.dirname(os.path.realpath(__file__))
    if not (len(sys.argv) == 2 and sys.argv[1] == "help"
            or len(sys.argv) >= 3 and sys.argv[1] == "allsteps"
            or len(sys.argv) == 3 and sys.argv[1] == "clean"
            or len(sys.argv) == 3 and sys.argv[1] == "archive"
            or 2 <= len(sys.argv) <= 3 and sys.argv[1] == "zero"
            or len(sys.argv) == 3 and sys.argv[1] == "spin"
            or len(sys.argv) == 3 and sys.argv[1] == "gentests"
            or len(sys.argv) == 3 and sys.argv[1] == "copy"
            or len(sys.argv) == 2 and sys.argv[1] == "compile"
            or len(sys.argv) == 2 and sys.argv[1] == "run"
            or len(sys.argv) == 2 and sys.argv[1] == "standalone"
            or len(sys.argv) == 3 and sys.argv[1] == "standalone"):
        print("*** Invalid command-line arguments\n")
        with open(f"{source_dir}/testbuilder_oceos.help") as helpfile:
            print(helpfile.read())
        sys.exit(1)

    if not Path.exists(Path(f"{source_dir}/spin2test_oceos.py")) \
            or not Path.exists(Path(f"{source_dir}/env")):
        print("Setup incomplete...")
        print("Please run the following before continuing:")
        print(f"cd {source_dir} && bash setup_oceos.sh")
        print(f". {source_dir}/env/bin/activate")
        sys.exit(1)

    config = get_config(source_dir)
    model_to_path = get_model_paths(config)
    model_to_roots = get_model_roots(config)
    refine_config = dict()
    if len(sys.argv) >= 3:
        config = get_config(source_dir, sys.argv[2])
        check_models_exist(sys.argv[2::], model_to_roots, config)
        if sys.argv[2] != "allmodels":
            refine_config = get_refine_config(source_dir, sys.argv[2],
                                              model_to_path[sys.argv[2]],
                                              model_to_roots[sys.argv[2]])

    if sys.argv[1] == "help":
        with open(f"{source_dir}/testbuilder_oceos.help") as helpfile:
            print(helpfile.read())

    if sys.argv[1] == "allsteps":
        all_steps(sys.argv[2::], model_to_path, source_dir)
        sys.exit(None)

    if sys.argv[1] == "spin":
        generate_spin_files(sys.argv[2], model_to_path[sys.argv[2]], 
                            model_to_roots[sys.argv[2]],
                            config["spinallscenarios"], refine_config)

    if sys.argv[1] == "gentests":
        genpath = Path("gen",model_to_path[sys.argv[2]])
        generate_test_files(sys.argv[2], genpath, model_to_roots[sys.argv[2]],
                            config["spin2test"], refine_config)

    if sys.argv[1] == "clean":
        clean(sys.argv[2], model_to_path, model_to_roots, source_dir)

    if sys.argv[1] == "archive":
        archive(sys.argv[2], model_to_path[sys.argv[2]], "", config["testsuite"],
                refine_config["testfiletype"])

    if sys.argv[1] == "copy":
        copy_oceos_tests(sys.argv[2], model_to_path[sys.argv[2]], config["testcode"],
                        config["oceos"], config["testyaml"], config["testsuite"],
                        refine_config["testfiletype"])

    if sys.argv[1] == "compile":
        compile_oceos(config["oceos"])

    if sys.argv[1] == "run":
        run_oceos_tests(config["test_runner"], config["test_args"],
                       config["testexe"], config["testsuite"])

    if sys.argv[1] == "standalone":
        # Generate standalone Unity tests for hardware deployment
        print("Generating standalone Unity tests for SPARC hardware deployment...")
        from standalone_test_generator import OCEOSStandaloneTestGenerator
        generator = OCEOSStandaloneTestGenerator()
        if len(sys.argv) == 3:
            # Generate for specific model
            model_name = sys.argv[2]
            model_path = model_to_path[model_name]
            trail_dir = model_path / "gen"
            output_dir = f"tests/standalone/{model_name}"
        else:
            # Generate for all models
            trail_dir = "gen"
            output_dir = "tests/standalone"
        
        test_files = generator.generate_all_standalone_tests(str(trail_dir), output_dir)
        generator.create_makefile_for_standalone_tests(test_files, output_dir)
        print(f"Standalone test generation complete. Use 'make standalone' to build.")

if __name__ == '__main__':
    main()
