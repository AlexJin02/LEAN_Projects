# Lean Projects

This repository contains my coursework and self-study projects in **Lean 4** (mainly using **mathlib**), with a focus on formalising standard results from undergraduate mathematics.

Each project includes:

* Lean source files (`.lean`)
* A short written report (usually PDF/LaTeX)

## Current projects

### Project 1 — Continuity and uniform continuity of (f(x)=x^2)

Formalisation using explicit (\varepsilon)–(\delta) definitions:

* (x^2) is continuous on (\mathbb{R})
* (x^2) is not uniformly continuous on (\mathbb{R})
* (x^2) is uniformly continuous on ([0,1])

Key ideas: factorisation (x^2-y^2=(x-y)(x+y)), absolute value bounds, and careful quantifier order for the “not uniformly continuous” proof.

## How to build / run

### Requirements

* Lean 4 + mathlib (recommended via `lake`)
* (Optional) VS Code with the Lean 4 extension

### Checking a specific file

Open the `.lean` file in VS Code and the Lean extension will typecheck it automatically.

## Notes on style

I try to keep proofs readable and close to the informal mathematics. When a proof becomes long, I split it into small helper lemmas (especially for algebraic rewriting and inequality bounds).
