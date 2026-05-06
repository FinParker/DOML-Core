#!/bin/bash
# Clean all generated files in DOML-rocq Project

set -e

echo "==> Cleaning DOML-rocq Project"
echo ""

# Function to clean directory
clean_dir() {
    local dir=$1
    echo "===> Cleaning $dir"
    
    cd "$dir" 2>/dev/null || return
    
    # Clean Coq generated files
    rm -f *.vo *.vok *.vos *.glob *.aux .*.aux
    
    # Clean native code
    rm -rf .coq-native .lia.cache .nia.cache
    
    # Clean Makefile
    if [ -f Makefile ]; then
        make cleanall -f Makefile 2>/dev/null || true
        rm -f Makefile Makefile.conf .Makefile.d
    fi
    
    cd - > /dev/null
    echo "     ✓ $dir cleaned"
    echo ""
}

# Clean Core directory
if [ -d "Core" ]; then
    clean_dir "Core"
fi

# Clean root directory generated files
echo "===> Cleaning root directory"
rm -f CoqMakefile CoqMakefile.conf .CoqMakefile.d .Makefile.d
echo "     ✓ Root cleaned"
echo ""

echo "==> Clean complete!"
