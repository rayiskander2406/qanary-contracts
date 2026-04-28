# QANARY Contracts

**Machine-checked reentrancy soundness for OpenZeppelin-style guard contracts.**

A Lean 4 + Mathlib formalization in support of the paper *Machine-Checked
Reentrancy Soundness for OpenZeppelin-Style Guard Contracts: A Minimal EVM
Model in Lean 4 + Mathlib*. Part of the QANARY research line.

## Status

| Item                                  | State                                             |
|---------------------------------------|---------------------------------------------------|
| Build                                 | 894 jobs, zero errors, zero warnings              |
| `sorry` / `admit` count               | 0                                                 |
| Project `axiom` declarations          | 0                                                 |
| Headline theorem axioms               | `[propext, Classical.choice, Quot.sound]`         |
| Tagged release                        | `v1.0-soundness`                                  |
| Lean toolchain                        | `leanprover/lean4:v4.30.0-rc1`                    |
| Mathlib pin                           | `322515540d7f`                                    |

## What's proved

* **Theorem 5 (`oz_guard_prevents_reentrancy`).** Universal soundness for the
  single-external-call subset of contracts satisfying `OZGuardDiscipline`,
  against a minimal 4-opcode EVM call-frame model.
  Statement: `∀ C : Contract, lockedValue ≠ unlockedValue → OZGuardDiscipline C → ReentrancyFree C`.
* **Theorem 4 (`cei_oz_incompatible`).** Machine-checked formal incompatibility
  between Checks-Effects-Interactions and the OpenZeppelin guard discipline:
  there exists an OZ-disciplined contract whose execution trace violates CEI
  by design (the unlock SSTORE follows the external call).
* **Theorem 1 (`dao_attack_is_reentrant`).** The 2016 DAO attack exhibits
  structural reentrancy (call-graph topology only).
* **Three methodology walls (W1, W2, W3).** Machine-checked exhibits showing
  the Vacuity Re-Verification Protocol surfaced under-specifications during
  proof development:
  * **W1** (`hypothesis_H_is_inconsistent`) — the literal CEI-only universal
    hypothesis is globally inconsistent.
  * **W2** (`stateless_trace_breaks_naive_strategy`) — `ValidExecution` ∧
    `SatisfiesCEI` ∧ `ReentrancyVulnerableStateful` are jointly satisfiable.
  * **W3** (`weak_rto_admits_self_unlock_reentry`) — a weak Reachable-Trace-Of
    predicate admits a self-unlock-reentry attack.

## What's in progress (F2–F4 per an internal handoff document)

* **Completeness direction.** Constructive `extractSafetyCertificate` —
  bottom-up plan: `NoExternalCalls` → `NoSStores` → `SatisfiesCEI_AllPaths`
  → `OZGuardConfig` (per the internal completeness strategy and the handover).
* **Multi-external-call generalization** of `IsOZGuardedFunction`.
* **Body-to-trace lift** connecting Solidity function bodies to the
  `ReachableTraceOf` predicate.
* **Protocol instantiations.** Pendle (Solidity), Compound (Solidity).
  Curve is excluded — its `nonReentrant` decorator is in Vyper with
  different semantics.

## What's out of scope (current scope limits)

See the internal paper scaffold §11 for the full Limitations section.

* `STATICCALL`, `DELEGATECALL`, `CALLCODE`, `CREATE`, `CREATE2`.
* Gas-related attacks (gas griefing, OOG-induced behavior changes).
* `REVERT` storage rollback semantics.
* Vyper-compiled contracts.
* Read-only reentrancy via `STATICCALL`.
* Compile-time correctness of `solc` (the connection from Solidity source
  to the trace model is informal at present; the body-to-trace lift will
  formalize the Lean-side connection).

## Reproducibility

### Prerequisites

* [`elan`](https://github.com/leanprover/elan) — the Lean 4 version manager.
* `git`.
* ~5 GB disk for Mathlib build cache.

### Quick start

```bash
git clone https://github.com/rayiskander2406/qanary-contracts.git
cd qanary-contracts
elan toolchain install $(cat lean-toolchain)
lake build
```

Expected: `Build completed successfully (894 jobs).` First-clone build is
~10–15 minutes (most of it Mathlib compilation; subsequent incremental
builds are fast).

### Verification

```bash
# Zero sorry / admit
grep -rn -E "^\s*(sorry|admit)\b" QanaryContracts/ --include="*.lean"
# (expects no output)

# Zero project axiom declarations
grep -rn "^axiom " QanaryContracts/ --include="*.lean"
# (expects no output)

# Headline theorem axiom audit
lake env lean QanaryContracts/PrintAxioms.lean 2>&1 | \
  grep "oz_guard_prevents_reentrancy"
# expected: '...oz_guard_prevents_reentrancy' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Pinning policy

The Lean toolchain (`lean-toolchain`) and Mathlib (`lakefile.lean` +
`lake-manifest.json`) pins are load-bearing across the QANARY paper line
and **must not be bumped** without a coordinated cross-paper migration.

### CI

GitHub Actions builds on `ubuntu-latest` and `macos-latest` per push to
`main` and per pull request, exercising `lake build` and the verification
commands above. See `.github/workflows/build.yml`.

## Repository layout

```
QanaryContracts/
├── EVM.lean                 minimal 4-opcode model (sstore/call/ret/revert)
├── Storage.lean             Mathlib Finmap-based EVMState
├── Step.lean                applyStep, slot stability lemmas
├── CEI.lean                 currentFrameAt, SatisfiesCEI
├── Reentrancy.lean          structural + state-aware predicates
├── Contract.lean            application-level Contract record
├── FunctionBody.lean        declarative function-body steps
├── ValidExecution.lean      trace validity constraints
├── Reachability.lean        ReachableTraceOf (5-conjunct OZ semantics)
├── ReentrancyFree.lean      universal safety predicate
├── DAOAttack.lean           9-step DAO attack witness (Theorem 1)
├── MultiFunction.lean       guard-protected discrimination test
├── CEISufficiency.lean      Theorem 2 (vacuous) + W1 + W2 walls
├── CEISufficiencyV2.lean    v2 def : Prop (deferred via build-gate)
├── OZSoundness.lean         IsOZGuardedFunction + Theorems 4 + 5 + W3
├── PrintAxioms.lean         audit gate (run via `lake env lean`)
├── Tests.lean               Phase 3 concrete-trace test cases
└── Spikes.lean              Phase 2 Mathlib reachability spikes
```

## Documentation

* the internal paper scaffold — paper structure (12 sections, theorem index, open items).
* the internal methodology notes — paper-grade methodology paragraphs.
* the internal completeness strategy — completeness-direction roadmap (Phase 5+).
* an internal handoff document — current handover (Path B).
* an internal audit transcript — 7-persona audit baseline.

Phase reports `Phase{1-4}*_report.md` document the proof-development arc.

## Standing rules

The development is governed by an explicit rule set (see
an internal handoff document Block 2):

* **R1.** Zero project axioms.
* **R2.** Zero `sorry`, zero `admit`.
* **R3.** Report before substantive proof attempts.
* **R4** (amended 2026-04-28). The frozen claim is locked against
  weakening-to-hide-progress but **must** be updated when proof scope
  reveals a modifier belongs to a different paper.
* **R5.** Vacuity Re-Verification Protocol mandatory before any predicate
  refinement.
* **R6.** Standing report format with items 1–10.
* **R7** (new 2026-04-28). Claim-Proof Match Audit at every session start.
* **R8** (new 2026-04-28). Post-Proof Persona Audit at every milestone.

R7 and R8 were added after the 2026-04-28 audit found that R1–R6 (inside-the-proof
discipline) caught proof bugs but not claim drift. The audit is in
an internal audit transcript; the post-audit handover is in
an internal handoff document.

## Citation

The paper is in preparation. Until it lands on arXiv, cite the repository:

```bibtex
@misc{qanary-contracts-2026,
  author       = {Iskander, Ray},
  title        = {{QANARY} Contracts: Machine-Checked Reentrancy Soundness
                  for {OpenZeppelin-Style} Guard Contracts},
  year         = {2026},
  howpublished = {\url{https://github.com/rayiskander2406/qanary-contracts}},
  note         = {Tag \texttt{v1.0-soundness}; commit \texttt{d74b35d}}
}
```

## License

License: TBD (pending). Until a `LICENSE` file is added to the repository,
this work is preserved under default copyright; see the repository owner
(Ray Iskander, Verdict Security) for permissions. The intended license is
expected to be permissive (MIT or Apache-2.0) consistent with prior QANARY
artifacts; the specific choice is in progress.

## Related work

See the internal paper scaffold §10 (Related Work) and the deep-dive recon reports
under `recon/` (Verity, SeRIF, CEUR Vol-4105). Mandatory citations to be
added per F6 of an internal handoff document: EtherTrust, VerX,
SmartPulse, eth-isabelle, ConCert, Cao-Wang.
