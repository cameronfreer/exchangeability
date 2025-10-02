# exchangeability

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
- `Exchangeability.lean` - Main library module
- `Exchangeability/Basic.lean` - Basic examples and proofs
- `Exchangeability/Advanced.lean` - More advanced examples with inductive types
- `Exchangeability/Tutorial.lean` - Step-by-step tutorial for beginners

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
lake exe exchangeability
```

## Examples Included

### Tutorial (`Exchangeability/Tutorial.lean`)
- Step-by-step introduction to Lean 4 concepts
- Simple function definitions
- Working with structures and custom types
- Basic proof techniques

### Basic Examples (`Exchangeability/Basic.lean`)
- Addition commutativity: `a + b = b + a`
- Additive identity: `n + 0 = n`
- Point structure with distance calculations
- List operations with mapping functions

### Advanced Examples (`Exchangeability/Advanced.lean`)
- Inductive type definitions (Color enum)
- Recursive functions (factorial)
- Dependent types (vectors)
- Proofs by induction

## Learning Resources

- [Lean 4 Manual](https://leanprover.github.io/lean4/doc/)
- [Theorem Proving in Lean 4](https://leanprover.github.io/theorem_proving_in_lean4/)
- [Lean 4 Metaprogramming Book](https://leanprover-community.github.io/lean4-metaprogramming-book/)