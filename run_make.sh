#!/bin/bash
# Build script for DOML-rocq Project
# Generates and compiles Coq files using rocq makefile

set -e

echo "==> Building DOML-rocq Project"
echo ""

# Check if rocq is available
if ! command -v rocq &> /dev/null; then
    echo "ERROR: rocq not found in PATH"
    echo "Please ensure Rocq is installed and environment is loaded:"
    echo "  eval \$(opam env)"
    exit 1
fi

echo "Rocq version:"
rocq --version
echo ""

# Check if _CoqProject exists
if [ ! -f _CoqProject ]; then
    echo "ERROR: _CoqProject not found in current directory"
    exit 1
fi

# Generate or update Makefile
echo "===> Generating CoqMakefile from _CoqProject..."
rocq makefile -f _CoqProject -o CoqMakefile

# Build with parallel jobs
echo "===> Compiling with $(nproc) parallel jobs..."
echo ""

make -j$(nproc) -f CoqMakefile all

echo ""
echo "✓ Build complete!"
echo ""