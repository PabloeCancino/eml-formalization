# EML: Formalization of the EML Operator in Lean 4

[![Lean 4](https://img.shields.io/badge/Lean-4.29.1-blue)](https://leanprover.github.io/)
[![Mathlib](https://img.shields.io/badge/Mathlib-4.29.1-green)](https://leanprover-community.github.io/mathlib4_docs/)
[![arXiv](https://img.shields.io/badge/arXiv-draft-orange)](./papers/)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE)

A Lean 4 formalization of the **EML operator** `eml(x, y) = exp(x) − log(y)` and its
algebraic structure, following Odrzywołek (arXiv:2603.21852, 2026) and
Lamharzi Alaoui (2026).

## Overview

The EML system shows that the single binary operator
```
f(x, y) = exp(x) − log(y)
```
with the constant seed `1` generates **all elementary functions** in the sense of Liouville.

This repository provides:

- **Mechanized proofs** in Lean 4 of the core algebraic structure (TRS termination, confluence, semantic evaluation).
- **Formalization of the Liouville Tower** as an inductive type.
- **Sheffer operator instance** for the EML/EDL operators (following Stachowiak, arXiv:2604.23893).
- **Witness trees** for exp, log, sin, cos, √, and all standard elementary functions.
- **Analytic obstruction axioms** (Lamharzi Alaoui, 2026): diagonal ideal obstruction and Hardy field obstruction.

## Repository Structure

```
eml-lean4/
├── lean4/EML/
│   ├── Basic.lean        — EML term grammar, K-complexity, TRS↑, semantic evaluation
│   ├── TRS.lean          — Rewriting system formal definition
│   ├── Sheffer.lean      — Universal algebra: ShefferOperator typeclass, EML/EDL instances
│   ├── Liouville.lean    — Liouville Tower as inductive type, closure theorems
│   ├── Extended.lean     — EML evaluator over extended reals (EReal)
│   ├── Real.lean         — Real-valued semantic evaluation
│   ├── Completeness.lean — Completeness statement (work in progress)
│   ├── Expressivity.lean — Expressivity bounds
│   ├── CurryHoward.lean  — Curry-Howard correspondence for EML proofs
│   └── EML.lean          — Entry point that imports all EML modules
├── lean4/lakefile.lean   — Lake build configuration
├── lean4/lean-toolchain  — Lean toolchain pin
└── papers/
    ├── Article1 eml grammar trs/
    ├── Article2_eml_sheffer/
    └── Article4 eml risch/
```

## Key Results (0 sorry, 6 honest axioms)

| Theorem | File | Status |
|---|---|---|
| TRS↑ termination | `Basic.lean` | ✅ Proved |
| TRS↑ confluence (orthogonality) | `Basic.lean` | ✅ Proved |
| Liouville Tower closure (exp, log) | `Liouville.lean` | ✅ Proved |
| EML → Liouville (every tree is elementary) | `Liouville.lean` | ✅ Proved |
| Sheffer axioms A1–A3 for subtraction | `Sheffer.lean` | ✅ Proved |
| NPI depth-7 universality (log recovery) | `Sheffer.lean` | ✅ Proved |
| Diagonal ideal obstruction | `Liouville.lean` | 📌 Honest axiom (P3 Thm. 3.1) |
| Hardy field obstruction (sin/cos impossible in LE₂) | `Liouville.lean` | 📌 Honest axiom (P3 Thm. 3.3) |
| Odrzywołek completeness (Liouville → EMLTerm) | `Liouville.lean` | 📌 Honest axiom (Thm. 1) |

## Architectural Invariant (Ioo/Ioc Rule)

Parameters passed through `eval_tLog` use `Set.Ioo(-π, π)` (open on both sides).
Parameters passed directly to `Complex.log_exp` use `Set.Ioc(-π, π)` (Mathlib API).

This invariant is documented in `Basic.lean §R2` and enforced throughout all semantic evaluation theorems.

## Building

```bash
# Requires Lake version 5.0.0-src+f72c35b (Lean version 4.29.1)
cd lean4
lake update
lake build
```

All files compile with **0 errors, 0 warnings, 0 sorries** (axioms are declared with `axiom`, not `sorry`).

## Related Work

- **P1** — Odrzywołek, A. (2026). *The EML operator generates all elementary functions*. arXiv:2603.21852v2.
- **P2** — Stachowiak, G. (2026). *Sheffer operators for abelian groups*. arXiv:2604.23893v1.
- **P3** — Lamharzi Alaoui, M. (2026). *From fixed points to two-cycles: obstructions and orbit lifts for analytic self-seeding Sheffer operators*. Firassa AI. [GitHub](https://github.com/marouane53/eml-sheffer-obstructions).

## Authors

**Pablo Eduardo Cancino Marentes**  
Licenciatura en Matemáticas — Universidad Autónoma de Nayarit (UAN)  
Contact: [pabloe.cancino@uan.edu.mx]

**Sergio Enrique Yarza Acuña**
Licenciatura en Matemáticas — Universidad Autónoma de Nayarit (UAN)  
Contact: [sergio.yarza@uan.edu.mx]

## License

MIT License — see [LICENSE](LICENSE) for details.

