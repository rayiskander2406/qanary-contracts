# Tridirectional Discriminating-Power Formal Verification of Smart Contract Reentrancy Defense at Production Scale

**Ray Iskander**

Verdict Security, Independent Formal Verification Firm

*Manuscript draft for IEEE Security & Privacy 2027 submission.*
*Phase 6 manuscript authoring; arXiv v1 + v2 community feedback cycle pre-venue-submission per agreed authoring trajectory.*
*Status indicator at top of file is informational; not part of submission.*

---

## Abstract

Smart contract reentrancy has caused over US\$200M in cumulative documented losses since 2016, with the DAO 2016 attack alone draining ≈3.6M ETH. The OpenZeppelin `ReentrancyGuard` mutex pattern has emerged as the de facto defense across most production DeFi protocols, yet no prior formal verification effort has established its discriminating power — that is, the property that the guard pattern blocks attacks against vulnerable instances *and* preserves correct execution for non-attacking transactions *and* maintains these properties when composed across heterogeneous protocol implementations. Prior work has formalized either guard correctness on toy contracts or attack feasibility on isolated vulnerable instances, but not both directions plus boundary cases against production-deployed source.

We present the first **tridirectional discriminating-power formal verification** of the OpenZeppelin guard pattern, applied to three production protocol instantiations: a negative-instance attack reproduction of the DAO 2016 vulnerable pattern, a positive-instance correctness proof against the Compound v2 cToken contract family, and a boundary-case proof distinguishing Aave V3's `flashLoan` function (safe by design via CEI-correct implementation) from a structurally-adjacent vulnerable variant `flashLoanVulnerable`. All thirteen theorems are machine-checked in Lean 4 and gated under continuous integration across four parallel verification blocks. A single capstone meta-theorem composes the three protocol instantiations under a *compose-from-outside* discipline, establishing the first cross-protocol stress-test PASS of guard-pattern correctness as a portable claim. Total verification budget: thirteen theorems, three production protocol instantiations, ~903-job CI build, zero `sorry`, zero introduced axioms, single `[propext]` dependence acknowledged.

We release the full Lean 4 source, CI gating configuration, and reproduction tags at `github.com/rayiskander2406/qanary-contracts`, with reproducibility verified at tagged commit `v1.6-phase7-closure`.

---

## §1 Introduction

*[Outline-with-bullet-points stage; full prose draft authored at Session 46 per PADS §4 writing order strategy. Bullet content below establishes section structure + key-claim allocation for Session 46 drafting.]*

### §1.1 Problem statement

- Smart contract reentrancy is one of the oldest and most consequential vulnerability classes on Ethereum-style chains, dating to the DAO 2016 attack (~3.6M ETH drained, ~US\$60M at attack-time price, ~US\$10B+ at 2025 prices).
- The attack class persists despite years of community awareness: Cream Finance 2021 (~US\$130M), Fei Protocol 2022 (~US\$80M), and dozens of smaller incidents cumulatively cross US\$500M.
- OpenZeppelin's `ReentrancyGuard` modifier — a single-bit mutex enforcing "not currently executing inside this contract" before re-entry — has emerged as the de facto defense pattern across most production DeFi protocols (Compound, Aave, Uniswap-style, and most TVL-significant deployments).
- Despite ubiquity, the guard pattern has no machine-checked correctness proof against production-deployed contract source. Auditors rely on pattern recognition + informal reasoning; researchers have formalized either toy instances or single-direction claims.

### §1.2 Limitations of prior approaches

- *Auditor-pattern-recognition layer:* fast but informal; recurring incidents demonstrate the pattern-recognition layer alone insufficient.
- *Toy-example formal verification:* establishes correctness for simplified models that do not match production contract code semantics (storage layout, modifier interaction, cross-function state mutation).
- *Single-direction formalization:* prior work formalizes either attack feasibility (negative-instance) on vulnerable contracts OR guard correctness (positive-instance) on defended contracts, rarely both, almost never with cross-protocol boundary cases included.
- *Composition gap:* even when individual-protocol formalizations exist, the cross-protocol portability of the guard-pattern correctness claim has not been established as a load-bearing theorem.

### §1.3 Contribution claim summary

- We present the **first tridirectional discriminating-power formal verification** of the OpenZeppelin guard pattern against production protocol source.
- *Tridirectional* = (a) negative-instance attack reproduction on the DAO 2016 vulnerable pattern (Layer 6-A), (b) positive-instance correctness proof against the Compound v2 cToken family (Layer 6-B), (c) boundary-case proof distinguishing Aave V3 `flashLoan` (safe by design) from the structurally-adjacent vulnerable variant `flashLoanVulnerable` (Layer 6-C).
- *Discriminating power* = the guard pattern's ability to distinguish defended-correctly from defended-incorrectly from undefended cases is provably correct in all three directions, machine-checked in Lean 4.
- A single capstone meta-theorem at Layer 6-D composes the three protocol instantiations under the *compose-from-outside* discipline (no modification of underlying protocol-instantiation contract proofs; composition adds outer-layer claim only). This establishes the first **cross-protocol stress-test PASS** of guard-pattern correctness as a portable claim.

### §1.4 Approach summary

- **Lean 4 + mathlib4** as proof assistant + library foundation; thirteen theorems gated under four parallel CI blocks at `lake build` + `lake build QanaryContracts.PrintAxioms` axiom-print verification.
- **Compose-from-outside discipline (M-26.1):** protocol-instantiation contracts (DAOAttack.lean, CompoundReentrancy.lean, AaveBoundaryCase.lean) sealed against modification across cross-protocol meta-theorem authoring. Layer 6-D meta-theorem composes from outside only.
- **Multi-protocol composition:** three protocol instantiations + one capstone meta-theorem = four-tier proof structure exercising compose-from-outside across heterogeneous protocol semantics.
- **Reproducibility:** tagged commits at protocol-instantiation closure boundaries (`v1.2-layer6c-closure`, `v1.3-layer6-closure`, `v1.4-methodology-housekeeping`) + manuscript-revision boundaries (`v1.5-phase6-closure`, `v1.6-phase7-closure`) + arXiv submission boundaries (`v1.7-arxiv-v1`, `v1.8-arxiv-v2`).

### §1.5 Results summary

- **Thirteen theorems** machine-checked: six Layer 6-A theorems (negative-instance DAO 2016), three Layer 6-B theorems (positive-instance Compound v2 cToken), three Layer 6-C theorems (boundary-case Aave V3), one Layer 6-D capstone meta-theorem (`tridirectionalDiscriminatingPower_certificate`, at `[propext]`-only).
- **Four protocol instantiations** exercised: DAO 2016 (negative); Compound v2 cToken (positive); Aave V3 `flashLoan` + `flashLoanVulnerable` pair (boundary); composition across the three (meta).
- **M-26.1 first cross-protocol stress-test PASS:** compose-from-outside discipline held across Compound v2 → Aave V3 protocol-instantiation boundary at Session 42 Unit 1, the first empirical instance where the discipline was stress-tested under non-trivial protocol semantics divergence and passed.
- **Build state:** `lake build` green at 901 jobs default + 903 jobs `lake build QanaryContracts.PrintAxioms` target; zero `sorry`; zero introduced axioms; single `[propext]` dependence acknowledged at Layer 6-D capstone.

### §1.6 Paper outline preview

- **§2 Background** — smart contract reentrancy class; OpenZeppelin guard pattern; Lean 4 foundations; prior formal verification efforts.
- **§3 Threat Model** — adversary capabilities; trust assumptions; defense surface scope; explicit out-of-scope items.
- **§4 Methodology Overview** — tridirectional discriminating-power claim framing; compose-from-outside discipline introduction; reproducibility approach.
- **§5 Formalization** — Layer 6 substantive substrate body; thirteen theorems detailed.
- **§6 Implementation/Evaluation** — repository structure; CI gating; reproducibility; build performance.
- **§7 Discussion** — first cross-protocol stress-test PASS framing; portability claim; methodology discriminating power.
- **§8 Related Work** — formal verification literature; commercial offerings positioning.
- **§9 Limitations** — guard-pattern scope; cross-protocol claim scope; kernel + `[propext]` trust assumption.
- **§10 Conclusion + Appendix** — research contribution summary; future work; §10.3 anchor (Layer 6 substantive substrate); §10.4 anchor (thin methodology framework reference).

---

*[Sections 2-10 authored across Phase 6 Sessions 46-51 per PADS §4 writing order strategy.]*
