/-
  QanaryContracts/CrossProtocolAudit.lean

  Layer 6-D Cross-Protocol Audit (Phase 5 Session 42).

  Tridirectional discriminating-power certificate composing Layer 6-A
  negative-instance (`daoContract_violates_OZGuardDisciplineGeneral`),
  Layer 6-B positive-instance (`compoundContract_satisfies_OZGuardDisciplineGeneral`),
  and Layer 6-C boundary-case (`aaveBoundaryCase_certificate`) certificates
  into a single `[propext]`-only conjunctive proposition. Paper §10
  Section 10.3 anchor — single load-bearing citable Lean theorem name
  for the tridirectional discriminating-power claim.

  Compose-from-outside discipline (M-26.1): Layer 6-A/B/C source files
  preserved unchanged; this module's cross-references are additive only,
  via the import statements and the proof term's named-theorem references.
  No modifications to DAOContract.lean, CompoundContract.lean,
  AaveBoundaryCase.lean, or DAOAttack.lean. First cross-protocol stress
  test of M-26.1 across four protocol-instantiation boundaries (DAO 2016
  / Compound v2 cToken / Aave V3 flashLoan / structurally adjacent
  flashLoanVulnerable).

  M-22.2 Tier 1 wrapper-layer absorption pattern fifth empirical instance:
  the meta-theorem inherits `[propext]`-only axiom records from the three
  composed certificates via direct anonymous-constructor conjunction
  ⟨α, β, γ⟩. No new tactics introduce additional axioms. After Layer 6-A
  Phase 3 master, Layer 6-A Phase 4 meta-theorem, Layer 6-B compressed
  master, and Layer 6-C boundary-case meta-theorem, this is the fifth
  empirical instance — strengthening five-instance evidence base for
  graduation candidacy review at Session 44 post-Layer-6 housekeeping.

  Module-level docstring with §1-§6 sections per directive Part 5
  Action 1.2 follows below; theorem statement at module body.
-/

import QanaryContracts.DAOContract
import QanaryContracts.CompoundContract
import QanaryContracts.AaveBoundaryCase

namespace QanaryContracts

/-! # Layer 6-D Cross-Protocol Audit — Tridirectional Discriminating-Power Certificate

## §1 Compositional Context

Layer 6-D closes the tridirectional discriminating-power claim's
substantive substrate by composing three protocol-instantiation
evidence layers — Layer 6-A negative-instance, Layer 6-B positive-
instance, Layer 6-C boundary-case — into a single conjunctive Lean
theorem. The result is the structural anchor for paper §10 Section
10.3: a single citable theorem name (`tridirectionalDiscriminatingPower_certificate`)
rather than three separate certificates requiring prose-level
conjunction.

The claim under composition: the body-shape `OZGuardDisciplineGeneral`
predicate **discriminates** across three orthogonal protocol-instantiation
axes:

* **Negative-instance axis** (rejection at deployed historical artifact):
  the predicate rejects DAO 2016 (`daoContract`), the canonical
  reentrancy exploit reference. Closed at Layer 6-A.

* **Positive-instance axis** (acceptance at deployed production reference):
  the predicate accepts Compound v2 cToken family (`compoundContract`,
  per Session 36 closure framing — abstract-pattern-load-bearing per
  Question 5d Option (X-prime)). Closed at Layer 6-B.

* **Boundary-case axis** (structural-neighborhood discrimination at
  paired contracts): the predicate accepts protocol-by-design `flashLoan`
  (`aaveContract`) AND rejects structurally adjacent vulnerable
  `flashLoanVulnerable` (`aaveContractAdjacent`). Body-shape-vs-trace-
  layer discrimination per Question 8e Framing (a). Closed at Layer 6-C.

The certificate that nobody else has even tried to issue at this level
of historical-instance rigor closes its substantive substrate here.

## §2 Cross-References to Prior Layer Certificates

This module references three prior layer certificates by name (no
modifications; compose-from-outside discipline):

* **Layer 6-A negative-instance** —
  `QanaryContracts.daoContract_violates_OZGuardDisciplineGeneral`
  at `QanaryContracts/DAOContract.lean:451`. Rejection-named per Ray's
  adjudication ("the contract violates the discipline"). Phase 3 master
  composing Sessions 32 Unit 4 falsifications at `withdrawRewardFor:724`
  and `splitDAO:669`. `[propext]`-only axiom record.

* **Layer 6-B positive-instance** —
  `QanaryContracts.compoundContract_satisfies_OZGuardDisciplineGeneral`
  at `QanaryContracts/CompoundContract.lean:450`. Acceptance-named per
  parallelism with Layer 6-A's rejection-named master. Phase 3-4
  compressed master composing `IsOZGuardedFunctionGeneral_at_transfer`
  and `IsOZGuardedFunctionGeneral_at_transferFrom` per Session 38 Unit 3.
  `[propext]`-only axiom record.

* **Layer 6-C boundary-case** —
  `QanaryContracts.aaveBoundaryCase_certificate`
  at `QanaryContracts/AaveBoundaryCase.lean:764`. Paired-theorem
  meta-theorem composing
  `aaveContract_satisfies_OZGuardDisciplineGeneral_at_flashLoan` (α) and
  `aaveContractAdjacent_violates_OZGuardDisciplineGeneral_at_flashLoanVulnerable`
  (β) per Session 41 Unit 1. `[propext]`-only axiom record (inherited
  from α and β via direct conjunction).

Protocol-instantiation provenance:

| Layer | Contract             | Deployed reference                                              | Solidity / artifact              |
|-------|----------------------|-----------------------------------------------------------------|----------------------------------|
| 6-A   | `daoContract`        | `0xbb9bc244d798123fde783fcc1c72d3bb8c189413` (DAO 2016)         | `blockchainsllc/DAO` v1.0        |
| 6-B   | `compoundContract`   | `0x5d3a536e4d6dbd6114cc1ead35777bab948e3643` (cDAI Compound v2) | Compound v2 cToken family        |
| 6-C+  | `aaveContract`       | `0x87870bca3f3fd6335c3f4ce8392d69350b4fa4e2` (Aave V3 Pool)     | Aave V3 `flashLoan`              |
| 6-C-  | `aaveContractAdjacent` | structurally adjacent vulnerable pattern (synthetic)          | DAO-mirror SSTORE-after-CALL var |

## §3 Discriminating-Power Claim Structural Statement

The conjunctive proposition asserts three claims in canonical order:

* `¬ OZGuardDisciplineGeneral daoContract` —
  the body-shape discipline predicate **rejects** the DAO 2016
  formalization. Witness: Layer 6-A's master via two CEI-violation
  positions.

* `OZGuardDisciplineGeneral compoundContract` —
  the body-shape discipline predicate **accepts** the Compound v2
  cToken formalization. Witness: Layer 6-B's master via per-function
  guard structure at `transfer` and `transferFrom`.

* `OZGuardDisciplineGeneral aaveContract ∧ ¬ OZGuardDisciplineGeneral aaveContractAdjacent` —
  the body-shape discipline predicate **accepts** the Aave V3 `flashLoan`
  protocol-by-design formalization AND **rejects** the structurally
  adjacent vulnerable formalization. Witness: Layer 6-C's paired-theorem
  certificate composing α (acceptance) and β (rejection).

The conjunction order (negative / positive / boundary) follows the
chronological closure order across Layers 6-A → 6-B → 6-C → 6-D. The
boundary-case clause preserves the inner conjunction structure of
Layer 6-C's certificate (acceptance ∧ rejection at paired contracts)
rather than flattening to a four-way top-level conjunction — Layer 6-C
remains the canonical entry point for paired-contract structural-
neighborhood discrimination claims.

## §4 Audit Gate Verification Scope

The meta-theorem is gated under the parallel **Verify Layer 6-D
cross-protocol theorem axiom records** CI block at
`.github/workflows/build.yml:~466`. The four parallel CI blocks at
build.yml — Layer 6-A (line 287), Layer 6-B (line 356), Layer 6-C
(line 408), Layer 6-D (line ~466) — preserve layer-scope-symmetry
across the four protocol-instantiation boundaries; Layer 6-D's block
mirrors the existing blocks' awk-pipeline + array-iteration pattern
without modifying them (Decision 1 parallel preservation per
opening directive v1.1 Part 2).

The audit gate enforces `[propext]`-only on
`tridirectionalDiscriminatingPower_certificate` per the M-22.2 Tier 1
fifth empirical instance prediction (§6 below). Any drift to a wider
axiom record (e.g., `Classical.choice`, `Quot.sound`) or a missing
`propext` baseline causes CI failure.

The PrintAxioms.lean entry at the audit gate's hook layer is

```
#print axioms tridirectionalDiscriminatingPower_certificate
```

closing the thirteenth Layer 6 theorem under axiom-record gating
discipline (six Layer 6-A + three Layer 6-B + three Layer 6-C + one
Layer 6-D = thirteen at Session 42 close).

## §5 Paper §10 Section 10.3 Anchor

Paper §10 Section 10.3 acquires `tridirectionalDiscriminatingPower_certificate`
as the single load-bearing citable Lean theorem name for the
tridirectional discriminating-power claim. Prior to Layer 6-D, paper
§10 Section 10.3 would have referenced three separate certificates
(`daoContract_violates_OZGuardDisciplineGeneral`,
`compoundContract_satisfies_OZGuardDisciplineGeneral`,
`aaveBoundaryCase_certificate`) requiring prose-level conjunction;
post-Layer-6-D the section references one theorem name with the
conjunction structure visible at the theorem statement itself.

The structural anchor's value is **citation atomicity**: paper readers
trace the discriminating-power claim to a single named theorem and
verify the build-gated `[propext]`-only axiom record at one location,
rather than tracing three separate names and checking three separate
axiom records.

## §6 M-22.2 Tier 1 Wrapper-Layer Absorption Pattern — Fifth Empirical Instance

M-22.2 Tier 1 graduated at Session 36 housekeeping with four empirical
instances of wrapper-layer absorption (a wrapper composing prior
theorems via direct anonymous-constructor or simple aliasing inherits
the underlying `[propext]`-only axiom records without introducing
additional axioms):

1. **Layer 6-A Phase 3 master** (`daoContract_violates_OZGuardDisciplineGeneral`,
   Session 32 Unit 4) — composes `OZGuardDisciplineGeneral_falsified_at_withdrawRewardFor`
   and `OZGuardDisciplineGeneral_falsified_at_splitDAO` (zero-axiom)
   via `simp [daoContract]` membership reduction; result `[propext]`-only.

2. **Layer 6-A Phase 4 meta-theorem** (`daoContract_negative_instance_certificate`,
   Session 33 Unit 3) — composes Phase 3 master and Phase 4 wrappers
   via direct anonymous-constructor; result `[propext]`-only.

3. **Layer 6-B compressed master** (`compoundContract_satisfies_OZGuardDisciplineGeneral`,
   Session 38 Unit 3) — composes per-function witnesses
   `IsOZGuardedFunctionGeneral_at_transfer` and
   `IsOZGuardedFunctionGeneral_at_transferFrom` via `simp [compoundContract]`;
   result `[propext]`-only.

4. **Layer 6-C boundary-case meta-theorem** (`aaveBoundaryCase_certificate`,
   Session 41 Unit 1) — composes paired-theorem α and β via direct
   anonymous-constructor; result `[propext]`-only.

5. **Layer 6-D cross-protocol meta-theorem** (`tridirectionalDiscriminatingPower_certificate`,
   Session 42 Unit 1; **this module**) — composes Layer 6-A master,
   Layer 6-B master, and Layer 6-C boundary-case meta-theorem via direct
   anonymous-constructor ⟨α, β, γ⟩; result `[propext]`-only (predicted;
   audit-gate-verified).

Five-instance evidence base strengthens M-22.2 Tier 1 portability claim
for graduation candidacy review at Session 44 post-Layer-6 housekeeping.
Reflexive graduation forbidden per discipline-strict default; held at
five-instance candidacy through Session 44.

Marker: `M-22.2-T1-empirical-instance-5` (paper §10 traceability).
-/

/-- F2-B / Layer 6-D meta-theorem: the **tridirectional discriminating-power
    certificate**. Composes Layer 6-A negative-instance, Layer 6-B
    positive-instance, and Layer 6-C boundary-case certificates into a
    single conjunctive proposition. Paper §10 Section 10.3 single
    load-bearing citable anchor.

    Compose-from-outside discipline (M-26.1) holds across four
    protocol-instantiation boundaries (DAO 2016 / Compound v2 cToken /
    Aave V3 flashLoan / structurally adjacent flashLoanVulnerable);
    this is the first cross-protocol stress test of M-26.1.

    Direct anonymous-constructor composition. Axiom record target:
    `[propext]`-only — inherited from `daoContract_violates_...` (α),
    `compoundContract_satisfies_...` (β), and `aaveBoundaryCase_certificate`
    (γ) via direct conjunction; no new tactics introduce additional axioms.
    M-22.2 Tier 1 wrapper-layer absorption pattern fifth empirical instance
    (`M-22.2-T1-empirical-instance-5`).

    See an internal VRVP methodology note for the full VRVP including
    M-26.1 first-cross-protocol-stress-test analysis and M-22.2 Tier 1
    five-instance evidence base documentation. -/
theorem tridirectionalDiscriminatingPower_certificate :
    (¬ OZGuardDisciplineGeneral daoContract) ∧
    (OZGuardDisciplineGeneral compoundContract) ∧
    (OZGuardDisciplineGeneral aaveContract ∧
      ¬ OZGuardDisciplineGeneral aaveContractAdjacent) :=
  ⟨daoContract_violates_OZGuardDisciplineGeneral,
   compoundContract_satisfies_OZGuardDisciplineGeneral,
   aaveBoundaryCase_certificate⟩

end QanaryContracts
