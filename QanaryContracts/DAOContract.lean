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

end QanaryContracts
