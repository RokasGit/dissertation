# OCEOS Formal Testing Framework - Windows Setup Guide

## Quick Start for Windows

### Prerequisites Installation

1. **Install Python 3.7+**
   - Download from https://python.org
   - ✅ Check "Add Python to PATH" during installation

2. **Install GNU Make**
   - **Option A (Recommended)**: Install Git for Windows (includes make)
     - Download from https://git-scm.com/download/win
     - Use Git Bash terminal for commands
   - **Option B**: Install via Chocolatey
     ```cmd
     choco install make
     ```
   - **Option C**: Install via MSYS2
     ```cmd
     pacman -S make
     ```

3. **Download BCC2 SPARC Compiler**
   - Download `bcc-2.2.0-gcc-mingw64.zip` from:
     https://download.gaisler.com/anonftp/bcc2/bin/
   - Create `C:\opt` folder
   - Extract to `C:\opt\bcc-2.2.0-gcc`

4. **Install SPIN Model Checker**
   - Download Windows binary from http://spinroot.com/
   - Add to your PATH environment variable

### Setup Options

#### Option 1: Batch Script (Command Prompt/PowerShell)
```cmd
cd C:\Users\rokas\OneDrive\Desktop\developer\dissertation\Project
setup_oceos.bat
```

#### Option 2: Bash Script (Git Bash/MSYS2)
```bash
cd /c/Users/rokas/OneDrive/Desktop/developer/dissertation/Project
./setup_oceos.sh
```

### Building and Running Tests

#### Using Command Prompt
```cmd
REM Activate Python environment
env\Scripts\activate.bat

REM Build tests
make test_build_only BSP=pm698 SPARC=1 TOOLCHAIN=gcc

REM Generate formal tests
python testbuilder_oceos.py allsteps task-mgr
```

#### Using Git Bash
```bash
# Activate Python environment
source env/Scripts/activate

# Build tests  
make test_build_only BSP=pm698 SPARC=1 TOOLCHAIN=gcc

# Generate formal tests
python3 testbuilder_oceos.py allsteps task-mgr
```

## Common Windows Issues & Solutions

### Issue 1: "make: command not found"
**Solution**: Install GNU Make (see prerequisites above)

### Issue 2: "Python: command not found"  
**Solution**: 
- Reinstall Python with "Add to PATH" checked
- Or manually add Python to PATH environment variable

### Issue 3: BCC2 compiler not found
**Solution**:
```cmd
REM Verify extraction location
dir C:\opt\bcc-2.2.0-gcc\bin\sparc-gaisler-elf-gcc.exe

REM If different location, update tools_config_sparc.mk
```

### Issue 4: Path separator issues
**Solution**: Framework automatically handles Windows paths with forward slashes

### Issue 5: Virtual environment activation
**Commands**:
```cmd
REM Command Prompt
env\Scripts\activate.bat

REM PowerShell  
env\Scripts\Activate.ps1

REM Git Bash
source env/Scripts/activate
```

## Recommended Development Setup

### Terminal: Git Bash
- Best compatibility with Unix-style commands
- Comes with Git for Windows
- Handles path separators correctly

### Alternative: Windows Terminal with PowerShell
- Modern Windows terminal
- Good PowerShell integration
- May need some command adjustments

### IDE Integration
- **VS Code**: Excellent support for C/Unity testing
- **CLion**: Good CMake/Makefile support
- **Dev-C++**: Simple option for basic C development

## Verification Commands

```cmd
REM Check all tools
make verify-bcc2
make show-sparc-config

REM Test Python environment
python --version
pip list

REM Test SPIN
spin -V

REM Test make
make --version
```

## Windows-Specific File Structure

```
C:\Users\rokas\OneDrive\Desktop\developer\dissertation\Project\
├── env\                          # Python virtual environment
│   └── Scripts\                  # Windows activation scripts
├── build\                        # Build artifacts  
├── tests\                        # Generated tests
├── tools_config_sparc.mk         # Windows BCC2 paths
├── setup_oceos.bat               # Windows batch setup
└── setup_oceos.sh                # Bash setup (Git Bash)
```

## Tips for Windows Development

1. **Use Git Bash** for best compatibility
2. **Avoid spaces in paths** for OCEOS directory structure  
3. **Run as Administrator** if permission issues occur
4. **Use forward slashes** in Makefile paths (framework handles this)
5. **Check Windows Defender** - may flag compiler executables

## Troubleshooting

If you encounter issues:

1. **Check PATH variables**:
   ```cmd
   echo %PATH%
   ```

2. **Verify file permissions**:
   ```cmd
   icacls C:\opt\bcc-2.2.0-gcc /t
   ```

3. **Test individual components**:
   ```cmd
   python --version
   make --version  
   C:\opt\bcc-2.2.0-gcc\bin\sparc-gaisler-elf-gcc.exe --version
   ```

4. **Use verbose make output**:
   ```cmd
   make -d test_build_only BSP=pm698 SPARC=1 TOOLCHAIN=gcc
   ```
