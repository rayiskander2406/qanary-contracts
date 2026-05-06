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

end QanaryContracts
