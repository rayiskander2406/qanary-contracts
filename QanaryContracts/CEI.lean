/-
  QanaryContracts/CEI.lean

  Stack reconstruction from trace prefixes (`currentFrameAt`,
  `frameStartOf`) and the trace-level Checks-Effects-Interactions
  predicate (`SatisfiesCEI`).

  Phase 3 first session — Priority 2 (Ray, 2026-04-27).

  The CEI rule (informal):
    For every external CALL out from contract `a`'s currently-executing
    function, every SSTORE to `a`'s storage *within the same call frame*
    must precede that CALL.

  Equivalently (negated form, which is what we encode for decidability):
    There is no `(i, j)` pair with `i < j` such that
      step `i` is a CALL out from `a` (a's frame is on top, target ≠ a)
      AND step `j` is an SSTORE on `a`'s storage with a's frame still on top.

  Per Phase 1 spike 4 / 2026-04-26: predicate is FLAT (∀ over indices)
  using a stack-aware HELPER (`currentFrameAt`). Mathlib has no
  TransitionSystem type, but `List.foldl` + bounded ∀-Fin is sufficient.
-/
import QanaryContracts.EVM
import QanaryContracts.Storage
import QanaryContracts.Step

namespace QanaryContracts

/-! ## Stack reconstruction from trace prefix

The implicit call stack at any trace position is determined by counting
unmatched CALL/RETURN-or-REVERT pairs in the prefix. We make this
explicit via `currentFrameAt`, which returns the address whose frame
is on top of the stack immediately before `tr[k]` would execute.
-/

/-- `currentFrameAt tr k` is the address whose call frame is on top of
    the stack immediately *before* step `tr[k]` would execute, or
    `none` if the stack is empty (depth = 0).

    Implementation: fold over `tr.take k`, pushing on CALL, popping on
    RETURN/REVERT, ignoring SSTORE. The head of the resulting stack is
    the current frame. -/
def currentFrameAt (tr : ExecutionTrace) (k : Nat) : Option Address :=
  let stack : List Address := (tr.take k).foldl
    (fun (st : List Address) (s : EVMStep) =>
      match s with
      | .call _ callee _ => callee :: st
      | .ret _           => st.tail
      | .revert          => st.tail
      | .sstore _ _ _    => st)
    []
  stack.head?

/-! ## CEI violation predicate -/

/-- A specific `(i, j)` pair witnesses a CEI violation iff:
    - step `i` is a CALL whose caller is the currently-executing
      contract `a`, with target ≠ `a` (genuine *external* call out)
    - step `j` is a SSTORE on `a`'s storage
    - `a`'s frame is still on top of the stack at position `j`
      (i.e., we are inside the same call frame in which the CALL was issued)

    The predicate is decidable on concrete traces because all conjuncts
    reduce to `Decidable` Nat / Address / Word256 comparisons. -/
def CEIViolated (tr : ExecutionTrace) (i j : Nat) : Prop :=
  match tr[i]?, tr[j]? with
  | some (.call caller₁ callee₁ _), some (.sstore addr _ _) =>
      currentFrameAt tr i = some caller₁ ∧
      currentFrameAt tr j = some caller₁ ∧
      addr = caller₁ ∧
      callee₁ ≠ caller₁
  | _, _ => False

/-- A trace satisfies CEI iff no `(i, j)` pair witnesses a violation. -/
def SatisfiesCEI (tr : ExecutionTrace) : Prop :=
  ∀ i j : Fin tr.length, i.val < j.val → ¬ CEIViolated tr i.val j.val

/-! ## Decidability

For concrete traces (where `tr.length` is a concrete `Nat`), both
`CEIViolated` and `SatisfiesCEI` are decidable. -/

instance (tr : ExecutionTrace) (i j : Nat) : Decidable (CEIViolated tr i j) := by
  unfold CEIViolated; split <;> infer_instance

instance (tr : ExecutionTrace) : Decidable (SatisfiesCEI tr) := by
  unfold SatisfiesCEI; infer_instance

end QanaryContracts
