/-
  QanaryContracts/ValidExecution.lean

  The `ValidExecution` predicate — what it means for a trace to be a
  *valid* EVM execution in our minimal model. Phase 3 Session 2.

  Three structural constraints, conjuncted:

    (1) `SStoresInOwnFrame`  — every SSTORE targets the currently-
                                executing contract's storage.
    (2) `CallsFromTopFrame`  — every CALL's `caller` field equals the
                                currently-executing contract (or the
                                stack is empty for the initial entry).
    (3) `BalancedFrames`     — the call-stack depth never goes negative
                                (no orphan RET/REVERT before any CALL).

  All three are decidable on concrete traces because the universal
  quantifier ranges over `Fin tr.length` and the bodies reduce.

  These constraints are sufficient for the Phase 3 Session 3 CEI
  sufficiency theorem; tighter constraints (matching actual function
  bodies of a specific contract) are layered on in Phase 4 with the
  OpenZeppelin formalization.
-/
import QanaryContracts.EVM
import QanaryContracts.Storage
import QanaryContracts.Step
import QanaryContracts.CEI
import QanaryContracts.Contract

namespace QanaryContracts

/-! ## Three structural constraints -/

/-- Every SSTORE in the trace targets the currently-executing
    contract's storage (the address on top of the call stack). -/
def SStoresInOwnFrame (tr : ExecutionTrace) : Prop :=
  ∀ k : Fin tr.length, ∀ addr key val,
    tr[k.val]? = some (EVMStep.sstore addr key val) →
    currentFrameAt tr k.val = some addr

/-- Every CALL's `caller` field equals the currently-executing contract
    (or the stack is empty, in which case the call is the initial
    entry from an EOA). -/
def CallsFromTopFrame (tr : ExecutionTrace) : Prop :=
  ∀ k : Fin tr.length, ∀ caller callee value,
    tr[k.val]? = some (EVMStep.call caller callee value) →
    currentFrameAt tr k.val = some caller ∨ currentFrameAt tr k.val = none

/-- The call-stack depth never goes negative (no orphan RET/REVERT). -/
def BalancedFrames (tr : ExecutionTrace) : Prop :=
  ∀ k : Fin tr.length, frameDepthAt tr k.val ≥ 0

/-! ## ValidExecution

A trace is a valid execution iff it satisfies all three structural
constraints. Note: this predicate is *trace-only* — the initial state
`s₀` does not appear in the constraints (validity is a property of the
trace's structure, not its dynamic effect). The `s₀` argument is
threaded through `ReentrancyFree` separately. -/

/-- A trace is a valid EVM execution iff it satisfies the three
    structural validity constraints. -/
def ValidExecution (tr : ExecutionTrace) : Prop :=
  SStoresInOwnFrame tr ∧ CallsFromTopFrame tr ∧ BalancedFrames tr

/-! ## Decidability -/

instance (tr : ExecutionTrace) : Decidable (SStoresInOwnFrame tr) := by
  unfold SStoresInOwnFrame; infer_instance

instance (tr : ExecutionTrace) : Decidable (CallsFromTopFrame tr) := by
  unfold CallsFromTopFrame; infer_instance

instance (tr : ExecutionTrace) : Decidable (BalancedFrames tr) := by
  unfold BalancedFrames; infer_instance

instance (tr : ExecutionTrace) : Decidable (ValidExecution tr) := by
  unfold ValidExecution; infer_instance

end QanaryContracts
