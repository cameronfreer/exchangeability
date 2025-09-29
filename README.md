# leantest-afp

A basic Lean 4 example project demonstrating fundamental concepts and proofs.

## Overview

This repository contains a simple Lean 4 project that demonstrates:
- Basic project structure with Lake build system
- Simple theorems and proofs
- Function definitions
- Type definitions (structures)
- List operations
- Basic mathematical proofs

## Project Structure

- `lakefile.lean` - Lake project configuration
- `Main.lean` - Main executable entry point 
- `LeantestAfp.lean` - Main library module
- `LeantestAfp/Basic.lean` - Basic examples and proofs

## Prerequisites

To run this project, you need:
1. [Lean 4](https://leanprover.github.io/lean4/doc/setup.html) installed
2. [elan](https://github.com/leanprover/elan) (Lean version manager)

## Installation

Install elan (Lean version manager):
```bash
curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh
```

Install Lean 4 stable:
```bash
elan default stable
```

## Building the Project

To build the project:
```bash
lake build
```

To run the main executable:
```bash
lake exe leantest-afp
```

## Examples Included

### Basic Theorems
- Addition commutativity: `a + b = b + a`
- Additive identity: `n + 0 = n`
- Successor addition properties

### Data Structures
- Point structure with x, y coordinates
- Distance function between points

### List Operations
- List mapping functions
- Proof that mapping preserves list length

## Learning Resources

- [Lean 4 Manual](https://leanprover.github.io/lean4/doc/)
- [Theorem Proving in Lean 4](https://leanprover.github.io/theorem_proving_in_lean4/)
- [Lean 4 Metaprogramming Book](https://leanprover-community.github.io/lean4-metaprogramming-book/)