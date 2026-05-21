# QANARY Contracts

**Tridirectional Discriminating-Power Formal Verification of Smart Contract Reentrancy Defense Against Production-Deployed Solidity Source**

Ray Iskander (Verdict Security)

A Lean 4 + mathlib4 formalization that machine-checks the correctness of the
OpenZeppelin reentrancy-guard pattern against a state-machine model of
**production-deployed Solidity source** — the DAO (2016), Compound v2 cToken,
and Aave V3 `flashLoan` — with a single capstone composition meta-theorem.
Part of the QANARY research line.

## Result

All **thirteen theorems** are machine-checked in Lean 4 with:

- **zero `sorry`** and **zero user-introduced axioms**;
- an **axiom footprint bounded by `[propext]`** (propositional extensionality) across the entire corpus — per-function inner lemmas are kernel-only; master/wrapper theorems carry `[propext]`-only records; the capstone is exactly the union of the prior-layer records by direct conjunction;
- continuous-integration gating across **four parallel verification blocks** that re-check each theorem **and its `#print axioms` record** on every push.

The corpus establishes *discriminating power*: the guard pattern **blocks** attacks
against vulnerable instances (negative leg), **preserves** correct execution for
non-attacking transactions (positive leg), and **distinguishes** structurally-adjacent
safe and vulnerable variants (boundary leg). A capstone meta-theorem composes the
three protocol instantiations under a **no-retrofit composition discipline** — each
protocol proof is sealed *before* the capstone is authored, with no underlying-proof
modification during composition.

| Item | State |
|---|---|
| `lake build` | green at **901 jobs** |
| `sorry` / `admit` | 0 |
| user-introduced axioms | 0 |
| corpus axiom footprint | bounded by `[propext]` |
| Lean toolchain | `leanprover/lean4:v4.30.0-rc1` (see `lean-toolchain`) |
| mathlib4 pin | `322515540d7f` (see `lakefile.lean` / `lake-manifest.json`) |

## Reproduction

### Prerequisites

- [`elan`](https://github.com/leanprover/elan) — the Lean version manager.
- `git`; ~5 GB disk for the mathlib4 build cache.

### Build and verify

```bash
git clone https://github.com/rayiskander2406/qanary-contracts.git
cd qanary-contracts
git checkout v1.6-phase7-closure # post-audit content seal (see Tags)
elan toolchain install "$(cat lean-toolchain)"
lake build # ~901 jobs; first build ~10–15 min (mathlib4)
lake env lean QanaryContracts/PrintAxioms.lean # prints each theorem's axiom record
```

The corpus is reproducible end-to-end from a single tagged commit. The
substantive proof substrate is independently reproducible at
`v1.3-layer6-closure`.

### Spot checks

```bash
# zero sorry / admit
grep -rnE "^\s*(sorry|admit)\b" QanaryContracts/ --include="*.lean" # (no output)
# zero user-introduced axiom declarations
grep -rn "^axiom " QanaryContracts/ --include="*.lean" # (no output)
```

## Tags

| Tag | Meaning |
|---|---|
| `v1.3-layer6-closure` | Substantive proof substrate sealed (all four protocol layers + capstone). |
| `v1.6-phase7-closure` | Post-audit content seal — the reproducibility anchor cited by the paper. |
| `v1.7-methodology-housekeeping` | Methodology-framework canonical artifacts canonized. |

(Earlier tags `v1.0-soundness` … `v1.2-layer6c-closure` mark intermediate milestones.)

## Repository structure

```
QanaryContracts/ Lean 4 source (flat module set; files map to layers below)
methodology/ Methodology-framework canonical artifacts (companion-paper pointers)
paper/ Manuscript source + arXiv v1 package + measurement scaffold
.github/workflows/ CI: four parallel verification blocks + axiom-record gating
lakefile.lean, lake-manifest.json, lean-toolchain Lean/mathlib4 pins
```

### `QanaryContracts/` — layer mapping

The source is a flat module set; the discriminating-power layers map to files as
follows (the foundation and lift modules support all layers):

| Layer | Role | Primary file(s) |
|---|---|---|
| **6-A** negative instance | DAO 2016 attack reproduction | `DAOContract.lean`, `DAOAttack.lean` |
| **6-B** positive instance | Compound v2 cToken correctness | `CompoundContract.lean` |
| **6-C** boundary case | Aave V3 `flashLoan` vs. minimal-diff `flashLoanVulnerable` mutant | `AaveBoundaryCase.lean` |
| **6-D** capstone | no-retrofit composition meta-theorem (`[propext]`-only) | `CrossProtocolAudit.lean` |
| audit gate | per-theorem `#print axioms` introspection | `PrintAxioms.lean` |
| soundness | OZ guard discipline + Theorems 4 & 5 | `OZSoundness.lean`, `CEISufficiency.lean` |
| model | minimal EVM call-frame state machine | `EVM.lean`, `Storage.lean`, `Step.lean`, `CEI.lean`, `Reentrancy.lean`, `Contract.lean`, `FunctionBody.lean`, `ValidExecution.lean`, `Reachability.lean`, `ReentrancyFree.lean`, `MultiFunction.lean` |
| body-to-trace lift | F4 lift + supporting infrastructure | `BodyTraceLift.lean`, `Executes.lean`, `Executes/{CountHelpers,StackHistory,BodyShape}.lean`, `W8.lean`, `Completeness.lean` |

See `QanaryContracts/README.md` for the full file-by-file map.

## Methodology framework

The `methodology/` directory holds the canonical artifacts for the methodology
framework underpinning this work (the no-retrofit composition discipline, the
axiom-record-minimal wrapper composition, and the multi-model audit workflow).
Per the boundary discipline of the paper, the framework is presented **in full in
a companion methodology paper** (separate arXiv track); these artifacts are the
pointer-table targets referenced from the manuscript's Appendix B. See
`methodology/README.md`.

## Paper

The manuscript source and the arXiv v1 submission package are under `paper/`:

- `paper/qanary_contracts_manuscript.md` — manuscript source.
- `paper/arxiv_v1_package/` — LaTeX source + compiled PDF + supplementary material (the arXiv-hosted PDF is the manuscript of record).
- `paper/ieeetran-measurement/` — IEEEtran-compsoc page-budget measurement scaffold (reusable; referenced by `methodology/page_budget_actual_compile_grounding_canonical.md`).

See `paper/README.md`.

## License

[MIT License](LICENSE). Copyright © 2026 Ray Iskander.

## Citation

The paper is forthcoming on arXiv. Until then, cite the repository:

```bibtex
@misc{qanary-contracts-2026,
  author = {Iskander, Ray},
  title = {{QANARY} Contracts: Tridirectional Discriminating-Power Formal
                  Verification of Smart Contract Reentrancy Defense Against
                  Production-Deployed Solidity Source},
  year = {2026},
  howpublished = {\url{https://github.com/rayiskander2406/qanary-contracts}},
  note = {Reproducibility anchor: tag \texttt{v1.6-phase7-closure}}
}
```
