#!/usr/bin/env bash
# SPDX-License-Identifier: BSD-2-Clause
# OCEOS Formal Testing Framework Setup Script
# Cross-platform setup for Windows, Linux, macOS, and WSL

set -euo pipefail

echo "Setting up OCEOS Formal Testing Framework..."

#
# Detect operating system / environment
#
if [[ "$OSTYPE" == msys* || "$OSTYPE" == cygwin* || "${OS-:-}" == "Windows_NT" ]]; then
    echo "Detected Windows environment"
    WINDOWS=true
    VENV_ACTIVATE="Scripts/activate"
else
    echo "Detected Unix-like environment"
    WINDOWS=false
    VENV_ACTIVATE="bin/activate"
fi

#
# Paths
#
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
VENV_DIR="$SCRIPT_DIR/env"
REQUIREMENTS_FILE="$SCRIPT_DIR/requirements.txt"

#
# (Re)create Python virtual environment if missing or broken
#
if [ ! -d "$VENV_DIR" ] || [ ! -f "$VENV_DIR/$VENV_ACTIVATE" ]; then
    if [ -d "$VENV_DIR" ]; then
        echo "⚠ Found env directory but no activate script."
        echo "   Removing and recreating venv with --copies mode."
        rm -rf "$VENV_DIR"
    else
        echo "Creating Python virtual environment in $VENV_DIR..."
    fi
    # --copies avoids symlink issues on Windows mounts
    python3 -m venv --copies "$VENV_DIR"
fi

#
# Show venv contents for debugging (optional)
#
echo "→ Contents of $VENV_DIR:"
ls -R "$VENV_DIR" || true

#
# Activate virtual environment
#
echo "Activating virtual environment..."
# shellcheck source=/dev/null
source "$VENV_DIR/$VENV_ACTIVATE"

#
# Upgrade pip
#
pip install --upgrade pip

#
# Install Python dependencies
#
if [ -f "$REQUIREMENTS_FILE" ]; then
    echo "Installing Python dependencies from requirements.txt..."
    pip install -r "$REQUIREMENTS_FILE"
else
    echo "Installing basic dependencies..."
    pip install pyyaml
fi

#
# Create directory structure
#
echo "Creating directory structure..."
mkdir -p build/{obj,bin,deps}
mkdir -p tests/unity
mkdir -p logs

#
# Git hooks
#
if [ -d "$SCRIPT_DIR/.git" ]; then
    echo "Setting up git hooks..."
    cp "$SCRIPT_DIR/scripts/pre-commit" "$SCRIPT_DIR/.git/hooks/" 2>/dev/null || true
    chmod +x "$SCRIPT_DIR/.git/hooks/pre-commit" 2>/dev/null || true
fi

#
# Tool checks
#
echo "Checking for required tools..."
check_tool() {
    if command -v "$1" &> /dev/null; then
        echo "✓ $1 found"
    else
        echo "✗ $1 not found — please install $2"
        return 1
    fi
}
MISSING_TOOLS=0
if ! check_tool spin      "SPIN model checker"; then MISSING_TOOLS=1; fi
if ! check_tool gcc       "GCC compiler";           then MISSING_TOOLS=1; fi
if ! check_tool make      "GNU Make";               then MISSING_TOOLS=1; fi

if [ ! -d "unity" ] && [ ! -d "../unity" ]; then
    echo "✗ Unity framework not found"
    echo "  git clone https://github.com/ThrowTheSwitch/Unity.git unity"
    MISSING_TOOLS=1
else
    echo "✓ Unity framework found"
fi

#
# Embedded toolchains
#
echo ""
echo "Checking for embedded toolchains..."
if command -v sparc-gaisler-elf-gcc &> /dev/null; then
    echo "✓ SPARC/LEON3 toolchain: $(sparc-gaisler-elf-gcc --version | head -n1)"
else
    echo "⚠ SPARC/LEON3 toolchain not found — required for SPARC/LEON3 targets"
fi
if command -v arm-none-eabi-gcc &> /dev/null; then
    echo "✓ ARM Cortex-M toolchain: $(arm-none-eabi-gcc --version | head -n1)"
else
    echo "⚠ ARM Cortex-M toolchain not found — sudo apt-get install gcc-arm-none-eabi"
fi

#
# Update configuration templates
#
echo ""
if [ -f "$SCRIPT_DIR/testbuilder_oceos.yml" ]; then
    echo "Updating testbuilder_oceos.yml with actual paths..."
    sed -i.bak \
        -e "s|<path_to_oceos_formal_testing>|$SCRIPT_DIR|g" \
        -e "s|<path-to-main-oceos-directory>|$SCRIPT_DIR/../oceos|g" \
        -e "s|<path-to-unity>|$SCRIPT_DIR/../unity|g" \
        "$SCRIPT_DIR/testbuilder_oceos.yml"
    rm -f "$SCRIPT_DIR/testbuilder_oceos.yml.bak"
    echo "✓ testbuilder_oceos.yml updated"
fi

#
# Create example test
#
echo ""
echo "Creating example test in tests/test_example.c..."
cat > tests/test_example.c << 'EOF'
#include "unity.h"
#include "oceos-test-support.h"

void setUp(void) {
    unity_setUp();
}

void tearDown(void) {
    unity_tearDown();
}

void test_example_task_creation(void) {
    enum DIRECTIVE_STATUS result;
    unsigned int task_id;

    task_id = CreateTestTask(PRIO_NORMAL, PRIO_NORMAL);
    TEST_ASSERT_NOT_EQUAL(0, task_id);

    result = DeleteTestTask(task_id);
    TEST_ASSERT_OCEOS_SUCCESS(result);
}

void test_example_invalid_task_id(void) {
    enum DIRECTIVE_STATUS result;
    result = DeleteTestTask(TEST_INVALID_ID);
    TEST_ASSERT_OCEOS_ERROR(INVALID_ID, result);
}

int main(void) {
    UNITY_BEGIN();
    RUN_TEST(test_example_task_creation);
    RUN_TEST(test_example_invalid_task_id);
    return UNITY_END();
}
EOF
echo "✓ tests/test_example.c created"

#
# Summary
#
echo ""
echo "Setup complete!"
if [ $MISSING_TOOLS -eq 0 ]; then
    echo "✓ All required tools found"
else
    echo "⚠ Some tools are missing — please install them before proceeding"
fi

cat << EOF

Next steps:
  1. Activate the Python environment:
       source env/${VENV_ACTIVATE}
  2. Configure paths in testbuilder_oceos.yml
  3. Run example test:
       make test
  4. Generate formal tests:
       make formal-test

For help:
  make help

EOF

# Prompt for immediate test-build
read -rp "Run a test-build now? (y/N) " REPLY
if [[ "$REPLY" =~ ^[Yy]$ ]]; then
    echo "Running test-build (make config)..."
    make config
    echo "Configuration displayed — run 'make' to build."
fi

echo "Setup script completed successfully!"
