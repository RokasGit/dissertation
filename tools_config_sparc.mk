# OCEOS SPARC Toolchain Configuration
# BCC2 compiler setup for LEON3 targets

# BCC2 SPARC Compiler Setup
# Available from: https://download.gaisler.com/anonftp/bcc2/bin/bcc-2.2.0-gcc-mingw64.zip

# Windows Configuration (default)
ifeq ($(OS),Windows_NT)
    # Create C:\opt directory and extract BCC2 there
    # Use forward slashes for make compatibility
    BCC2_ROOT = C:/opt/bcc-2.2.0-gcc
    SPARC_TOOLS = $(BCC2_ROOT)/bin
    SPARC_PREFIX = sparc-gaisler-elf-
    
    # Windows-specific settings
    SHELL = cmd.exe
    RM = del /q
    MKDIR = mkdir
    PATHSEP = ;
    EXEEXT = .exe
    
    # Tools
    SPARC_CC = $(SPARC_TOOLS)/$(SPARC_PREFIX)gcc
    SPARC_AS = $(SPARC_TOOLS)/$(SPARC_PREFIX)as  
    SPARC_LD = $(SPARC_TOOLS)/$(SPARC_PREFIX)ld
    SPARC_AR = $(SPARC_TOOLS)/$(SPARC_PREFIX)ar
    SPARC_OBJCOPY = $(SPARC_TOOLS)/$(SPARC_PREFIX)objcopy
    SPARC_OBJDUMP = $(SPARC_TOOLS)/$(SPARC_PREFIX)objdump
    SPARC_SIZE = $(SPARC_TOOLS)/$(SPARC_PREFIX)size
    SPARC_GDB = $(SPARC_TOOLS)/$(SPARC_PREFIX)gdb
    
    # Include paths
    SPARC_INCLUDES = -I$(BCC2_ROOT)/sparc-gaisler-elf/include
    SPARC_INCLUDES += -I$(BCC2_ROOT)/lib/gcc/sparc-gaisler-elf/*/include
    
    # Library paths
    SPARC_LIBPATHS = -L$(BCC2_ROOT)/sparc-gaisler-elf/lib
    SPARC_LIBPATHS += -L$(BCC2_ROOT)/lib/gcc/sparc-gaisler-elf/*/
else
    # Linux Configuration
    # Modify this section for your Linux setup
    BCC2_ROOT = /opt/bcc-2.2.0-gcc
    SPARC_TOOLS = $(BCC2_ROOT)/bin
    SPARC_PREFIX = sparc-gaisler-elf-
    
    # Tools (same pattern as Windows)
    SPARC_CC = $(SPARC_TOOLS)/$(SPARC_PREFIX)gcc
    SPARC_AS = $(SPARC_TOOLS)/$(SPARC_PREFIX)as  
    SPARC_LD = $(SPARC_TOOLS)/$(SPARC_PREFIX)ld
    SPARC_AR = $(SPARC_TOOLS)/$(SPARC_PREFIX)ar
    SPARC_OBJCOPY = $(SPARC_TOOLS)/$(SPARC_PREFIX)objcopy
    SPARC_OBJDUMP = $(SPARC_TOOLS)/$(SPARC_PREFIX)objdump
    SPARC_SIZE = $(SPARC_TOOLS)/$(SPARC_PREFIX)size
    SPARC_GDB = $(SPARC_TOOLS)/$(SPARC_PREFIX)gdb
    
    # Include paths
    SPARC_INCLUDES = -I$(BCC2_ROOT)/sparc-gaisler-elf/include
    SPARC_INCLUDES += -I$(BCC2_ROOT)/lib/gcc/sparc-gaisler-elf/*/include
    
    # Library paths  
    SPARC_LIBPATHS = -L$(BCC2_ROOT)/sparc-gaisler-elf/lib
    SPARC_LIBPATHS += -L$(BCC2_ROOT)/lib/gcc/sparc-gaisler-elf/*/
endif

# SPARC-specific compiler flags
SPARC_CFLAGS = -mcpu=leon3 -msoft-float
SPARC_CFLAGS += -O2 -g3 -Wall -Wextra

# OCEOS BSP specific flags
ifeq ($(BSP),pm698)
    SPARC_CFLAGS += -DBSP_PM698
else ifeq ($(BSP),gr712rc)
    SPARC_CFLAGS += -DBSP_GR712RC  
else ifeq ($(BSP),leon3)
    SPARC_CFLAGS += -DBSP_LEON3
endif

# Linker flags
SPARC_LDFLAGS = $(SPARC_CFLAGS)
SPARC_LDFLAGS += -Wl,--gc-sections

# Export for use in main Makefile
export SPARC_CC SPARC_AS SPARC_LD SPARC_AR SPARC_OBJCOPY SPARC_OBJDUMP SPARC_SIZE
export SPARC_INCLUDES SPARC_LIBPATHS SPARC_CFLAGS SPARC_LDFLAGS

# Verification targets
verify-bcc2:
	@echo "Verifying BCC2 SPARC compiler installation..."
ifeq ($(OS),Windows_NT)
	@if not exist "$(SPARC_CC).exe" ( \
		echo ERROR: BCC2 SPARC compiler not found at $(SPARC_CC).exe && \
		echo Please download from https://download.gaisler.com/anonftp/bcc2/bin/ && \
		echo Extract to $(BCC2_ROOT) && \
		exit /b 1 \
	)
	@echo BCC2 SPARC compiler found: $(SPARC_CC).exe
	@"$(SPARC_CC).exe" --version
else
	@if [ ! -f "$(SPARC_CC)" ]; then \
		echo "ERROR: BCC2 SPARC compiler not found at $(SPARC_CC)"; \
		echo "Please download from https://download.gaisler.com/anonftp/bcc2/bin/"; \
		echo "Extract to $(BCC2_ROOT)"; \
		exit 1; \
	fi
	@echo "BCC2 SPARC compiler found: $(SPARC_CC)"
	@$(SPARC_CC) --version
endif

show-sparc-config:
	@echo "SPARC Toolchain Configuration:"
	@echo "  BCC2_ROOT: $(BCC2_ROOT)"
	@echo "  SPARC_CC: $(SPARC_CC)"
	@echo "  SPARC_CFLAGS: $(SPARC_CFLAGS)"
	@echo "  BSP: $(BSP)"
