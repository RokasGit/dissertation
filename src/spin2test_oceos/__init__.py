# SPDX-License-Identifier: BSD-2-Clause
"""OCEOS Unity Test Generator from SPIN output"""

# Copyright (C) 2025 Trinity College Dublin (www.tcd.ie)
# Adapted for OCEOS with Unity testing framework

import re
import yaml
from pathlib import Path


class OceosUnityGenerator:
    """Generates Unity test code for OCEOS from SPIN traces"""
    
    def __init__(self, model_root, preamble_file, postamble_file, 
                 run_file, refine_file):
        self.model_root = model_root
        self.preamble_file = preamble_file
        self.postamble_file = postamble_file
        self.run_file = run_file
        self.refine_file = refine_file
        
        # Load refinement mappings
        with open(refine_file) as f:
            self.refinements = yaml.load(f, Loader=yaml.FullLoader)
    
    def generate_test(self, test_number, output_file):
        """Generate Unity test from SPIN trace"""
        spin_file = f"gen/{self.model_root}-{test_number}.spn"
        
        # Read SPIN trace
        with open(spin_file, 'r') as f:
            spin_trace = f.read()
        
        # Parse SPIN trace to extract test steps
        test_steps = self.parse_spin_trace(spin_trace)
        
        # Generate Unity test code
        unity_code = self.generate_unity_code(test_steps, test_number)
        
        # Write output
        with open(output_file, 'w') as f:
            f.write(unity_code)
    
    def parse_spin_trace(self, trace):
        """Parse SPIN trace to extract OCEOS API calls and assertions"""
        steps = []
        lines = trace.split('\n')
        
        for line in lines:
            line = line.strip()
            if not line:
                continue
                
            # Look for OCEOS API calls
            if 'CALL' in line:
                call_match = re.search(r'CALL\s+(\w+)\s*(.*)', line)
                if call_match:
                    api_call = call_match.group(1)
                    args = call_match.group(2).strip()
                    steps.append({
                        'type': 'call',
                        'api': api_call,
                        'args': args,
                        'line': line
                    })
            
            # Look for assertions/checks
            elif 'ASSERT' in line or 'CHECK' in line:
                steps.append({
                    'type': 'assert',
                    'condition': line,
                    'line': line
                })
            
            # Look for scalar values (return codes, etc.)
            elif 'SCALAR' in line:
                scalar_match = re.search(r'SCALAR\s+(\w+)\s+(\w+)', line)
                if scalar_match:
                    var_name = scalar_match.group(1)
                    value = scalar_match.group(2)
                    steps.append({
                        'type': 'scalar',
                        'variable': var_name,
                        'value': value,
                        'line': line
                    })
        
        return steps
    
    def generate_unity_code(self, test_steps, test_number):
        """Generate Unity test code from parsed steps"""
        
        # Read preamble
        with open(self.preamble_file, 'r') as f:
            preamble = f.read()
        
        # Read postamble  
        with open(self.postamble_file, 'r') as f:
            postamble = f.read()
        
        # Generate test function
        test_body = self.generate_test_body(test_steps, test_number)
        
        # Combine all parts
        unity_code = f"""/* SPDX-License-Identifier: BSD-2-Clause */
/**
 * @file
 *
 * @ingroup OceosTestSuite{self.model_root.title()}
 *
 * @brief Unity tests for Promela model {self.model_root}
 */

{preamble}

/**
 * @brief Test case {test_number} for {self.model_root}
 * Scenario-based test case
 */
void test_{self.model_root}_scenario_{test_number}(void)
{{
{test_body}
}}

{postamble}
"""
        return unity_code
    
    def generate_test_body(self, test_steps, test_number):
        """Generate the body of the Unity test function"""
        body_lines = []
        body_lines.append(f"    // Test scenario {test_number}")
        body_lines.append("    enum DIRECTIVE_STATUS result;")
        body_lines.append("    unsigned int task_id;")
        body_lines.append("")
        
        for step in test_steps:
            if step['type'] == 'call':
                # Map SPIN API call to OCEOS Unity test
                unity_call = self.map_api_call(step)
                if unity_call:
                    body_lines.append(f"    {unity_call}")
            
            elif step['type'] == 'scalar':
                # Add assertion for return value
                assertion = self.map_scalar_check(step)
                if assertion:
                    body_lines.append(f"    {assertion}")
            
            elif step['type'] == 'assert':
                # Add direct assertion
                unity_assert = self.map_assertion(step)
                if unity_assert:
                    body_lines.append(f"    {unity_assert}")
        
        return '\n'.join(body_lines)
    
    def map_api_call(self, step):
        """Map SPIN API call to OCEOS Unity test call"""
        api = step['api']
        args = step['args']
        
        # Map common OCEOS APIs
        if api == 'oceos_task_create':
            return f"result = oceos_task_create({args});"
        elif api == 'oceos_task_start':
            return f"result = oceos_task_start({args});"
        elif api == 'oceos_task_delete':
            return f"result = oceos_task_delete({args});"
        elif api == 'oceos_task_suspend':
            return f"result = oceos_task_suspend({args});"
        elif api == 'oceos_task_resume':
            return f"result = oceos_task_resume({args});"
        elif api == 'oceos_sem_create':
            return f"result = oceos_sem_create({args});"
        elif api == 'oceos_sem_wait':
            return f"result = oceos_sem_wait({args});"
        elif api == 'oceos_sem_post':
            return f"result = oceos_sem_post({args});"
        else:
            return f"// Unknown API call: {api}({args})"
    
    def map_scalar_check(self, step):
        """Map scalar value to Unity assertion"""
        var_name = step['variable']
        value = step['value']
        
        if var_name.endswith('RC') or var_name.endswith('_result'):
            # This is a return code
            if value == '0' or value == 'SUCCESSFUL':
                return f"TEST_ASSERT_EQUAL(SUCCESSFUL, result);"
            else:
                return f"TEST_ASSERT_EQUAL({value}, result);"
        else:
            return f"TEST_ASSERT_EQUAL({value}, {var_name});"
    
    def map_assertion(self, step):
        """Map SPIN assertion to Unity assertion"""
        condition = step['condition']
        
        # Simple mapping - may need refinement
        if 'true' in condition.lower():
            return "TEST_ASSERT_TRUE(1);"
        elif 'false' in condition.lower():
            return "TEST_ASSERT_FALSE(0);"
        else:
            return f"// Assertion: {condition}"


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
