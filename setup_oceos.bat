@echo off
REM OCEOS Formal Testing Framework Setup Script for Windows
REM Run from Command Prompt or PowerShell

echo Setting up OCEOS Formal Testing Framework...

REM Configuration
set SCRIPT_DIR=%~dp0
set VENV_DIR=%SCRIPT_DIR%env
set REQUIREMENTS_FILE=%SCRIPT_DIR%requirements.txt

REM Create Python virtual environment
if not exist "%VENV_DIR%" (
    echo Creating Python virtual environment...
    python -m venv "%VENV_DIR%"
)

REM Activate virtual environment
call "%VENV_DIR%\Scripts\activate.bat"

REM Upgrade pip
pip install --upgrade pip

REM Install Python dependencies
if exist "%REQUIREMENTS_FILE%" (
    echo Installing Python dependencies...
    pip install -r "%REQUIREMENTS_FILE%"
) else (
    echo Installing basic dependencies...
    pip install pyyaml
)

REM Create necessary directories
echo Creating directory structure...
if not exist "build" mkdir build
if not exist "build\obj" mkdir build\obj
if not exist "build\bin" mkdir build\bin
if not exist "build\deps" mkdir build\deps
if not exist "tests\unity" mkdir tests\unity
if not exist "logs" mkdir logs

REM Check for required tools
echo Checking for required tools...

where make >nul 2>&1
if %errorlevel% equ 0 (
    echo [OK] make found
) else (
    echo [ERROR] make not found - please install GNU Make
    echo   - Via Chocolatey: choco install make
    echo   - Via MSYS2: pacman -S make
    echo   - Via Git Bash: comes with Git for Windows
)

where python >nul 2>&1
if %errorlevel% equ 0 (
    echo [OK] Python found
    python --version
) else (
    echo [ERROR] Python not found - please install Python 3.7+
)

where spin >nul 2>&1
if %errorlevel% equ 0 (
    echo [OK] SPIN model checker found
) else (
    echo [WARNING] SPIN not found
    echo   Download from: http://spinroot.com/
)

REM Check for BCC2 SPARC compiler
if exist "C:\opt\bcc-2.2.0-gcc\bin\sparc-gaisler-elf-gcc.exe" (
    echo [OK] BCC2 SPARC compiler found
    C:\opt\bcc-2.2.0-gcc\bin\sparc-gaisler-elf-gcc.exe --version
) else (
    echo [WARNING] BCC2 SPARC compiler not found
    echo   Download bcc-2.2.0-gcc-mingw64.zip from:
    echo   https://download.gaisler.com/anonftp/bcc2/bin/
    echo   Extract to C:\opt\bcc-2.2.0-gcc
)

REM Update configuration with Windows paths
if exist "testbuilder_oceos.yml" (
    echo Updating configuration file for Windows...
    powershell -Command "(Get-Content testbuilder_oceos.yml) -replace '<path_to_oceos_formal_testing>', '%SCRIPT_DIR%' | Set-Content testbuilder_oceos.yml"
    powershell -Command "(Get-Content testbuilder_oceos.yml) -replace '<path-to-main-oceos-directory>', '%SCRIPT_DIR%..\oceos' | Set-Content testbuilder_oceos.yml"
    powershell -Command "(Get-Content testbuilder_oceos.yml) -replace '<path-to-unity>', '%SCRIPT_DIR%..\oceos\test\unity' | Set-Content testbuilder_oceos.yml"
    echo [OK] Configuration updated
)

REM Create example test
echo Creating example test...
echo #include "unity.h" > tests\test_windows_example.c
echo #include "oceos-test-support.h" >> tests\test_windows_example.c
echo. >> tests\test_windows_example.c
echo void setUp(void) { } >> tests\test_windows_example.c
echo void tearDown(void) { } >> tests\test_windows_example.c
echo. >> tests\test_windows_example.c
echo void test_windows_example(void) { >> tests\test_windows_example.c
echo     TEST_ASSERT_TRUE(1); >> tests\test_windows_example.c
echo } >> tests\test_windows_example.c
echo. >> tests\test_windows_example.c
echo int main(void) { >> tests\test_windows_example.c
echo     UNITY_BEGIN(); >> tests\test_windows_example.c
echo     RUN_TEST(test_windows_example); >> tests\test_windows_example.c
echo     return UNITY_END(); >> tests\test_windows_example.c
echo } >> tests\test_windows_example.c

echo [OK] Created example test in tests\test_windows_example.c

echo.
echo Setup complete!
echo.
echo Next steps:
echo 1. Keep this Command Prompt open (virtual environment is activated)
echo 2. Configure paths in testbuilder_oceos.yml if needed
echo 3. Run test build: make test_build_only BSP=pm698 SPARC=1 TOOLCHAIN=gcc
echo 4. Generate formal tests: python testbuilder_oceos.py allsteps task-mgr
echo.
echo For help: make help

pause
