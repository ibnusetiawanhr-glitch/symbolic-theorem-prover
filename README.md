# Symbolic Theorem Prover & Formal Verification Engine

Open-source symbolic theorem proving and formal mathematical verification benchmark developed at the **Department of Mathematics, Institut Teknologi Sepuluh Nopember (ITS)**.

## Overview
This repository implements an automated theorem prover for propositional and quantifier-free first-order mathematical logic:
- **AST Canonicalization & Equivalence Reduction**: Material implication and biconditional elimination.
- **Clausal Normal Form Transformation**: De Morgan's NNF reduction and distributive CNF encoding.
- **Refutation-Based DPLL Engine**: Unit propagation, pure literal elimination, and MOMS branching heuristics for formal unsatisfiability (UNSAT) verification and countermodel generation.

## Usage
Run the verification benchmark suite directly with Python 3.8+:
`python prover.py`

## Author & Affiliation
- **Muhammad Fadhil Dzaki Ibnu Pratama**
- Department of Mathematics, Institut Teknologi Sepuluh Nopember (ITS), Surabaya, Indonesia
