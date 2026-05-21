# `QanaryContracts/` — Lean 4 source

A flat module set (plus the `Executes/` infrastructure subdirectory). The
discriminating-power result is organized into four layers; the table below maps
each layer and supporting role to its file(s). All theorems are gated by the CI
in `.github/workflows/build.yml` and audited by `PrintAxioms.lean`.

Build from the repository root: `lake build` (≈901 jobs). Axiom records:
`lake env lean QanaryContracts/PrintAxioms.lean`.

## Discriminating-power layers

| Layer | Role | File(s) | Theorems |
|---|---|---|---|
| **6-A** | DAO 2016 negative instance (attack reproduction; guard-absent baseline) | `DAOContract.lean`, `DAOAttack.lean` | 6 (incl. `dao_attack_is_reentrant`) |
| **6-B** | Compound v2 cToken positive instance (correctness) | `CompoundContract.lean` | 3 |
| **6-C** | Aave V3 boundary case: production `flashLoan` vs. minimal-diff `flashLoanVulnerable` mutant | `AaveBoundaryCase.lean` | 3 |
| **6-D** | Capstone composition meta-theorem (no-retrofit; `[propext]`-only) | `CrossProtocolAudit.lean` | 1 |

Thirteen CI-gated headline theorems total (6 + 3 + 3 + 1). Each file also contains
supporting lemmas. The authoritative per-theorem statements, hypothesis lists, and
`#print axioms` records are in the paper's Appendix A; the live audit gate is
`PrintAxioms.lean`.

## Supporting modules

| Role | Files |
|---|---|
| Audit gate (`#print axioms` introspection) | `PrintAxioms.lean` |
| OZ guard discipline + Theorems 4 & 5 + W3 | `OZSoundness.lean` |
| CEI sufficiency + W1/W2 walls | `CEISufficiency.lean`, `CEISufficiencyV2.lean` |
| Minimal EVM call-frame model | `EVM.lean`, `Storage.lean`, `Step.lean` |
| CEI / reentrancy predicates | `CEI.lean`, `Reentrancy.lean`, `ReentrancyFree.lean` |
| Contract / function-body model | `Contract.lean`, `FunctionBody.lean`, `MultiFunction.lean`, `ValidExecution.lean`, `Reachability.lean` |
| Body-to-trace (F4) lift + W8 + completeness substrate | `BodyTraceLift.lean`, `Executes.lean`, `Executes/CountHelpers.lean`, `Executes/StackHistory.lean`, `Executes/BodyShape.lean`, `W8.lean`, `Completeness.lean` |
| Concrete-trace tests / early spikes | `Tests.lean`, `Spikes.lean` |
| Root aggregator | `../QanaryContracts.lean` |

## Axiom-record discipline

No theorem is admitted with `sorry`, `admit`, or any user-introduced `axiom`.
Per-function inner lemmas are kernel-only; master/wrapper theorems carry
`[propext]`-only records; the Layer 6-D capstone records exactly the union of the
three prior-layer records by direct conjunction — no new axiom is introduced at
any layer. CI fails on any axiom-record drift.
