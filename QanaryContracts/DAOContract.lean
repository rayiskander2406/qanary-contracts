/-
  QanaryContracts/DAOContract.lean

  DAO 2016 Contract Formalization (Layer 6-A Phase 3).

  Per Session 29 survey (an internal reconnaissance note) verbatim
  Solidity source from the `blockchainsllc/DAO` repository (renamed
  from `slockit/DAO` post-2016), v1.0 tag commit `982e3c242ee3`,
  dated 2016-04-29; deployed at
  `0xbb9bc244d798123fde783fcc1c72d3bb8c189413` on 2016-04-30.

  Formalizes `withdrawRewardFor` (Session 31 Unit 1) and `splitDAO`
  (Session 31 Unit 2) in the project's EVM model. Per Session 29
  survey Action 1.3 verdict and Session 30 Phase 2 closure: no EVM
  model extensions needed; the minimal 4-opcode model captures every
  load-bearing feature for the body-shape negative-instance proof.

  The contract-level `OZGuardDisciplineGeneral` evaluation produced
  at Session 32 demonstrates this contract fails predicate
  satisfaction at two distinct CEI-violation positions:
    * `withdrawRewardFor:724` — `paidOut[_account] += reward` after
      external `payOut` CALL.
    * `splitDAO:669` — `balances[msg.sender] = 0` after internal CALL
      transitively executing external CALL via `withdrawRewardFor`
      → `ManagedAccount.payOut`.

  Phase 4 negative-instance proof composes against this formalization.
  Phase 5 produces the explicit equivalence-gap disclosure (Option G
  per survey Action 1.5.3).
  Phase 6 produces the audit gate.

  Coexistence: Sessions 14-27 substantive constructs and DAOAttack.lean
  (trace-layer prior work, complementary not duplicating per survey
  Action 1.4.5) are preserved unchanged; this module is additive.
-/
import QanaryContracts.Contract
import QanaryContracts.FunctionBody
import QanaryContracts.Step
import QanaryContracts.EVM
import QanaryContracts.OZSoundness
import QanaryContracts.Reentrancy
import QanaryContracts.DAOAttack

namespace QanaryContracts

/-! ## Concrete addresses and storage slots for the DAO 2016 contract

    Abstract slot identities consistent with v1.0 Solidity layout
    (Phase 5 Option G: explicit-gap-disclosure with respect to
    deployed-bytecode keccak256 slot derivation per survey Action 1.5).

    The DAO contract does NOT have a reentrancy guard slot — it
    predates OpenZeppelin `ReentrancyGuard` by ~18 months. `daoGuardSlot`
    is specified solely to make `IsOZGuardedFunctionGeneral` evaluable
    at the predicate layer; no body-shape will ever match the
    lock-prefix convention this slot would carry, which is precisely
    the negative-instance evidence Phase 4 produces. -/

/-- The DAO contract's address. Corresponds to the historically deployed
    `0xbb9bc244d798123fde783fcc1c72d3bb8c189413`; abstract per Phase 5
    gap-disclosure. Distinct from `daoVictim` in `DAOAttack.lean`
    (a trace-layer placeholder); this is the contract-layer address. -/
def daoAddress : Address := ⟨3, by decide⟩

/-- The `rewardAccount` (a `ManagedAccount` instance) that
    `withdrawRewardFor` calls via `rewardAccount.payOut(_account, reward)`
    at v1.0 line 722. -/
def daoRewardAccount : Address := ⟨4, by decide⟩

/-- The DAO's notional reentrancy guard slot. The DAO does NOT actually
    use a reentrancy guard; this slot exists purely to make
    `IsOZGuardedFunctionGeneral` evaluable. The body-shape will fail to
    match the predicate's lock-prefix convention — the negative-instance
    witness Phase 4 produces. -/
def daoGuardSlot : Word256 := ⟨0, by decide⟩

/-- Storage slot abstraction for `paidOut[_account]` (Solidity mapping
    that `withdrawRewardFor:724` SSTOREs *after* the external CALL —
    the CEI violation the maintainers patched on 2016-06-12 but never
    deployed before the 2016-06-17 attack). -/
def daoPaidOutSlot : Word256 := ⟨1, by decide⟩

/-- Storage slot abstraction for `balances[_account]` (Solidity mapping
    that `splitDAO:669` SSTOREs *after* the internal call to
    `withdrawRewardFor` — the second, unpatched CEI violation that the
    June 17 attacker exploited; Unit 2). -/
def daoBalancesSlot : Word256 := ⟨2, by decide⟩

/-- The newly-created DAO contract that `splitDAO` calls via
    `p.splitData[0].newDAO.createTokenProxy.value(fundsToBeMoved)(...)`
    at v1.0 line 643. Distinct from `daoAddress` (the original DAO);
    this is the fork-target produced by the `splitDAO` proposal. -/
def daoNewDAO : Address := ⟨5, by decide⟩

/-- Representative storage slot for `splitDAO`'s interim SSTOREs at
    v1.0 lines 655, 658, 660, 663, 668 (`rewardToken`/`DAOpaidOut`
    updates for newDAO and self, plus `totalSupply -= balances[msg.sender]`).
    Collapsed to a single representative slot per Unit 2 VRVP §3
    single-path abstraction; the predicate's `NoSStoreOnGuardSlotInSteps`
    evaluates identically regardless of whether these SSTOREs target
    distinct slots or share one (none equal `daoGuardSlot`). -/
def daoMiscSlot : Word256 := ⟨6, by decide⟩

/-- The `unlockedValue` for `daoContract`'s notional reentrancy guard,
    chosen per OpenZeppelin v4 convention (`_NOT_ENTERED = 1`). The DAO
    has no real reentrancy guard; this value is structurally inert for
    the predicate-rejection witness (the head-element-injectivity
    argument holds regardless of the concrete value). Session 32 Unit 1. -/
def daoUnlockedValue : Word256 := ⟨1, by decide⟩

/-- The `lockedValue` for `daoContract`'s notional reentrancy guard,
    chosen per OpenZeppelin v4 convention (`_ENTERED = 2`). Session 32 Unit 1. -/
def daoLockedValue : Word256 := ⟨2, by decide⟩

/-! ## `withdrawRewardFor` formalization (Layer 6-A Phase 3, Unit 1) -/

/-- F2-B / Layer 6-A: `withdrawRewardFor` formalization per Session 29
    survey Action 1.2.2 verbatim Solidity (DAO.sol v1.0 lines 716-726).
    The body-shape's CEI violation at the position corresponding to
    Solidity line 724 falsifies `IsOZGuardedFunctionGeneral` via missing
    lock-prefix at the head of the function body.

    Single-path abstraction per Session 29 survey Action 1.8.1 (a)
    recommendation: revert-gates at v1.0 lines 717-718 and 723 elided
    as non-occurring on the successful execution path. Local-variable
    computation at lines 720-721 is invisible at the body-shape layer.

    Three steps:
    * `.call daoRewardAccount 0`  (v1.0 line 722: external `rewardAccount.payOut`)
    * `.sstore daoPaidOutSlot _`  (v1.0 line 724: `paidOut[_account] += reward` — CEI VIOLATION)
    * `.ret true`                 (v1.0 line 725: `return true`)

    See an internal VRVP methodology note for the full
    body-shape decomposition and predicate-falsification position. -/
def withdrawRewardFor : FunctionBody :=
  [FunctionBody.Step.call daoRewardAccount ⟨0, by decide⟩,
   FunctionBody.Step.sstore daoPaidOutSlot ⟨0, by decide⟩,
   FunctionBody.Step.ret true]

/-! ## `splitDAO` formalization (Layer 6-A Phase 3, Unit 2) -/

/-- F2-B / Layer 6-A: `splitDAO` formalization per Session 29 survey
    Action 1.2.1 verbatim Solidity (DAO.sol v1.0 lines 599-672). The
    body-shape's CEI violation at the position corresponding to
    Solidity line 669 (`balances[msg.sender] = 0` after the internal
    call to `withdrawRewardFor`) is what the June 17 2016 attacker
    exploited.

    Single-path abstraction per Unit 2 VRVP §2 (revert-gates from
    `noEther`/`onlyTokenholders`/sanity-check elided; "newDAO already
    exists" branch selected for the conditional CREATE block at lines
    625-637). Internal-call inlining per VRVP §5 mode (a):
    `withdrawRewardFor`'s observable steps appear inline at the
    corresponding-to-Solidity-line-667 position rather than as a
    symbolic invocation (FunctionBody.Step has no symbolic-invoke
    constructor by design).

    Body steps (per VRVP §3, 8 steps after LOG3 elision and interim-SSTORE collapse):
    * `.call daoNewDAO 0`         (line 643: external CALL to newDAO)
    * `.sstore daoMiscSlot 0`     (lines 655-663: interim SSTOREs collapsed)
    * `.call daoRewardAccount 0`  (line 667→722: inlined withdrawRewardFor's external CALL)
    * `.sstore daoPaidOutSlot 0`  (line 667→724: inlined CEI violation 1)
    * `.sstore daoMiscSlot 0`     (line 668: totalSupply update)
    * `.sstore daoBalancesSlot 0` (line 669: CEI VIOLATION 2 — attacker-exploited)
    * `.sstore daoPaidOutSlot 0`  (line 670: paidOut[msg.sender] = 0)
    * `.ret true`                 (line 671: return true)

    The body's predicate-rejection witness is the head-element-injectivity
    argument: head step is `.call`, predicate requires `.sstore C.guardSlot
    C.lockedValue`. Same general principle as `withdrawRewardFor` (Unit 1),
    but distinct body — both falsifications independently establish
    `OZGuardDisciplineGeneral` rejection at Session 32.

    DAOAttack.lean composition: complementary not duplicating per VRVP §8;
    no import of DAOAttack.lean. Address-namespace independent. -/
def splitDAO : FunctionBody :=
  [FunctionBody.Step.call daoNewDAO ⟨0, by decide⟩,
   FunctionBody.Step.sstore daoMiscSlot ⟨0, by decide⟩,
   FunctionBody.Step.call daoRewardAccount ⟨0, by decide⟩,
   FunctionBody.Step.sstore daoPaidOutSlot ⟨0, by decide⟩,
   FunctionBody.Step.sstore daoMiscSlot ⟨0, by decide⟩,
   FunctionBody.Step.sstore daoBalancesSlot ⟨0, by decide⟩,
   FunctionBody.Step.sstore daoPaidOutSlot ⟨0, by decide⟩,
   FunctionBody.Step.ret true]

/-! ## DAO Contract definition (Layer 6-A Phase 3 closure, Session 32 Unit 1) -/

/-- F2-B / Layer 6-A Phase 3 closure: the DAO contract definition
    composing Session 31's `withdrawRewardFor` and `splitDAO` into a
    `Contract` value matching `QanaryContracts/Contract.lean`'s record
    signature.

    Field semantics:
    * `address := daoAddress` (abstract per Phase 5 gap-disclosure;
      corresponds to historical `0xbb9bc244...`).
    * `guardSlot := daoGuardSlot` (notional; the DAO has no real
      reentrancy guard).
    * `unlockedValue := daoUnlockedValue` and `lockedValue :=
      daoLockedValue` (OpenZeppelin v4 convention; structurally inert
      for the predicate-rejection witness).
    * `functions := [withdrawRewardFor, splitDAO]` (Session 31).

    `OZGuardDisciplineGeneral daoContract` evaluates to `False`:
    the non-emptiness conjunct holds (`functions ≠ []`), but the
    universal conjunct fails because both `withdrawRewardFor` and
    `splitDAO` falsify `IsOZGuardedFunctionGeneral` via
    head-element-injectivity (Units 2 and 3 produce the formal
    witnesses; Unit 4 composes them defensively).

    See an internal VRVP methodology note for field-by-field
    specification and Units 2-3 foundation-discipline check. -/
def daoContract : Contract :=
  { address := daoAddress,
    guardSlot := daoGuardSlot,
    unlockedValue := daoUnlockedValue,
    lockedValue := daoLockedValue,
    functions := [withdrawRewardFor, splitDAO] }

/-! ## Predicate falsification at `withdrawRewardFor` (Layer 6-A Phase 3 closure, Session 32 Unit 2) -/

/-- F2-B / Layer 6-A Phase 3 closure: `withdrawRewardFor` falsifies
    `IsOZGuardedFunctionGeneral` via head-element-injectivity. The
    head step of `withdrawRewardFor` (per Session 31 Unit 1) is
    `.call daoRewardAccount 0`; the predicate's required head element
    is `.sstore daoContract.guardSlot daoContract.lockedValue`. By
    constructor disjointness `.call ≠ .sstore`, no `body` makes the
    predicate's existential body-shape equation hold.

    See an internal VRVP methodology note for
    the head-element-injectivity argument and the four-tactic
    reconstruction (`rintro` → `unfold` → `injection` → `noConfusion`). -/
theorem OZGuardDisciplineGeneral_falsified_at_withdrawRewardFor :
    ¬ IsOZGuardedFunctionGeneral daoContract withdrawRewardFor := by
  rintro ⟨body, h_eq, _, _⟩
  unfold withdrawRewardFor at h_eq
  injection h_eq with h_head _
  exact FunctionBody.Step.noConfusion h_head

/-! ## Predicate falsification at `splitDAO` (Layer 6-A Phase 3 closure, Session 32 Unit 3) -/

/-- F2-B / Layer 6-A Phase 3 closure: `splitDAO` falsifies
    `IsOZGuardedFunctionGeneral` via head-element-injectivity. The
    head step of `splitDAO` (per Session 31 Unit 2) is `.call daoNewDAO 0`
    (the external CALL at v1.0 line 643 to the newly-created DAO);
    the predicate's required head element is `.sstore daoContract.guardSlot
    daoContract.lockedValue`. Constructor disjointness `.call ≠ .sstore`
    via `FunctionBody.Step.noConfusion` produces `False`.

    Independence from Unit 2 (`withdrawRewardFor` falsification): both
    theorems operate at the same head-element-injectivity layer but
    against structurally distinct function bodies (3 steps vs 8 steps,
    distinct head sub-arguments `daoRewardAccount` vs `daoNewDAO`).
    Either theorem alone suffices to falsify `OZGuardDisciplineGeneral`
    daoContract; Unit 4's defensive composition invokes both to make
    both CEI-violation positions visible at the master theorem layer
    per the Session 29 survey two-CEI-violations precision finding.

    See an internal VRVP methodology note for the
    independence verification and parallel four-tactic reconstruction. -/
theorem OZGuardDisciplineGeneral_falsified_at_splitDAO :
    ¬ IsOZGuardedFunctionGeneral daoContract splitDAO := by
  rintro ⟨body, h_eq, _, _⟩
  unfold splitDAO at h_eq
  injection h_eq with h_head _
  exact FunctionBody.Step.noConfusion h_head

/-! ## Master rejection theorem (Layer 6-A Phase 3 closure, Session 32 Unit 4) -/

/-- F2-B / Layer 6-A Phase 3 closure master theorem: the DAO contract
    violates `OZGuardDisciplineGeneral`. The proof composes defensively
    over both CEI-violation positions per Ray's Session 31 success report
    adjudication:

    * `withdrawRewardFor:724` (the patched-but-never-deployed June 12
      violation) — invoked via Unit 2's
      `OZGuardDisciplineGeneral_falsified_at_withdrawRewardFor`.
    * `splitDAO:669` (the actually-exploited June 17 violation) —
      invoked via Unit 3's
      `OZGuardDisciplineGeneral_falsified_at_splitDAO`.

    Either witness alone suffices for the rejection; defensive
    composition makes both CEI-violation positions visible at the
    proof-term layer per the Session 29 survey two-CEI-violations
    precision finding. The conjunction-pair `⟨h_w_contra, h_s_contra⟩`
    references both falsifications in the elaborated term; `.1`
    closes via Unit 2's witness; `.2` would close via Unit 3 equivalently.

    Rejection-named (`daoContract_violates_...`) per Ray's adjudication:
    the name reads as substantive evidence ("the contract violates the
    discipline") rather than formal logic; same theorem statement either
    way, but the substantive name is paper §10 raw material.

    See an internal VRVP methodology note for the
    defensive-vs-compact tradeoff and full tactic-level reconstruction. -/
theorem daoContract_violates_OZGuardDisciplineGeneral :
    ¬ OZGuardDisciplineGeneral daoContract := by
  rintro ⟨_h_ne, h_all⟩
  have h_w_mem : withdrawRewardFor ∈ daoContract.functions := by
    simp [daoContract]
  have h_s_mem : splitDAO ∈ daoContract.functions := by
    simp [daoContract]
  have h_w_contra : False :=
    OZGuardDisciplineGeneral_falsified_at_withdrawRewardFor
      (h_all withdrawRewardFor h_w_mem)
  have h_s_contra : False :=
    OZGuardDisciplineGeneral_falsified_at_splitDAO
      (h_all splitDAO h_s_mem)
  exact (⟨h_w_contra, h_s_contra⟩ : False ∧ False).1

/-! ## Predicate-rejection invocation wrapper (Layer 6-A Phase 4 opening, Session 33 Unit 1) -/

/-- F2-B / Layer 6-A Phase 4 (Unit 1): Phase-3-into-Phase-4 wrapper for
    the contract-layer predicate rejection. Re-frames Session 32 Unit 4's
    master theorem `daoContract_violates_OZGuardDisciplineGeneral` at
    the Phase 4 composition layer. The body-shape evidence (two
    CEI-violation positions: `withdrawRewardFor:724` and `splitDAO:669`)
    flows through Phase 3's defensive composition to this Phase-4
    framed restatement, suitable for Unit 3's meta-theorem composition.

    Layer-distinction visibility: Phase 3 closes the body-shape
    contract-layer evidence; Phase 4 lifts that closure into the
    negative-instance certificate's composition framing. The wrapper
    is the structural seam that makes the layer distinction visible
    at the artifact structure (per directive Part 5 framing).

    See an internal VRVP methodology note for
    the full VRVP including foundation-discipline check for Unit 3. -/
theorem daoContract_predicate_rejected_at_Phase4 :
    ¬ OZGuardDisciplineGeneral daoContract :=
  daoContract_violates_OZGuardDisciplineGeneral

/-! ## Vulnerability-witness invocation wrapper (Layer 6-A Phase 4 opening, Session 33 Unit 2) -/

/-- F2-B / Layer 6-A Phase 4 (Unit 2): trace-layer-into-Phase-4 wrapper
    for the reentrancy-vulnerability witness. Re-frames DAOAttack.lean's
    `dao_attack_is_reentrant` (Phase 2 deliverable, 2026-04-26) at the
    Phase 4 composition layer. The trace-layer evidence (9-step DAO
    attack trace with witness indices `(daoVictim, 0, 2)`) flows
    through DAOAttack's existing structural reentrancy proof to this
    Phase-4 framed restatement, suitable for Unit 3's meta-theorem
    composition.

    Compose-from-outside discipline: DAOAttack.lean preserved unchanged
    (Sessions 31-33); the wrapper invokes `dao_attack_is_reentrant`
    directly via term-mode `:=`. Address-namespace independence
    preserved at the type layer: the wrapper's subject is
    `daoAttackTrace` (parametrized over `daoVictim`), distinct from
    `daoContract`'s `daoAddress`. The discriminating-power linkage to
    the contract layer is supplied by Unit 3's meta-theorem
    composition rather than by typed quantification.

    See an internal VRVP methodology note
    for the compose-from-outside verification + foundation-discipline
    check for Unit 3. -/
theorem daoAttackTrace_vulnerability_witness_at_Phase4 :
    ReentrancyVulnerable daoAttackTrace :=
  dao_attack_is_reentrant

/-! ## Negative-instance certificate (Layer 6-A Phase 4 closure, Session 33 Unit 3) -/

/-- F2-B / Layer 6-A Phase 4 closure: the DAO contract carries the
    negative-instance certificate. The trace exhibits reentrancy AND
    `OZGuardDisciplineGeneral daoContract` is violated; this co-occurrence
    is the discriminating-power claim — the predicate accurately rejects
    vulnerable contracts at the historical instance the certificate's
    load-bearing argument depends on.

    Composition: the two CEI-violation positions visible at Phase 3
    (`withdrawRewardFor:724`, `splitDAO:669`) are body-shape evidence
    of the predicate's rejection (right conjunct, via Unit 1 wrapper);
    DAOAttack.lean's 9-step `daoAttackTrace` with witness indices
    `(daoVictim, 0, 2)` is trace-layer evidence of actual exploitability
    (left conjunct, via Unit 2 wrapper). The meta-theorem composes both
    layers via anonymous constructor.

    Address-namespace independence: the conjunction's left conjunct is
    over `daoAttackTrace`/`daoVictim ⟨1,_⟩`; the right conjunct is over
    `daoContract`/`daoAddress ⟨3,_⟩`. The discriminating-power linkage
    between the two namespaces is documented HERE rather than enforced
    by typed quantification, per Session 31 splitDAO design choice and
    Phase 5 Option G gap-disclosure framing. The historical DAO 2016
    deployment at `0xbb9bc244...` is the singular real-world referent
    both namespaces abstract; Phase 5 makes that referential structure
    paper-§10-explicit.

    See an internal VRVP methodology note for the discriminating-
    power claim's full framing including M-22.2 tier classification. -/
theorem daoContract_negative_instance_certificate :
    ReentrancyVulnerable daoAttackTrace ∧
    ¬ OZGuardDisciplineGeneral daoContract :=
  ⟨daoAttackTrace_vulnerability_witness_at_Phase4,
   daoContract_predicate_rejected_at_Phase4⟩

end QanaryContracts
