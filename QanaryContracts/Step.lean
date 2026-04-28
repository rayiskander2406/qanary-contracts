/-
  QanaryContracts/Step.lean

  State transition: how a single `EVMStep` modifies the global `EVMState`,
  how a trace evaluates from an initial state, and the helper `stateAt`
  that gives the state immediately before any specified trace position.

  Phase 3 first session — Priority 1 infrastructure.

  In our minimal model only `SSTORE` modifies storage. `CALL`, `RETURN`,
  and `REVERT` are control-flow steps; they affect the call stack but
  not the storage map. Stack tracking lives in `CEI.lean` via
  `currentFrameAt`, which reconstructs the stack from the trace prefix.
-/
import Mathlib.Data.Finmap
import QanaryContracts.EVM
import QanaryContracts.Storage

namespace QanaryContracts

/-- Apply one `EVMStep` to the global state. Only `sstore` modifies
    storage; control-flow steps are storage-neutral. -/
def applyStep (s : EVMState) (step : EVMStep) : EVMState :=
  match step with
  | .sstore addr key val =>
      let storage    := (s.lookup addr).getD Storage.empty
      let storage'   := storage.insert key val
      (s.erase addr).insert addr storage'
  | _ => s

/-- Evaluate a trace from an initial state by applying each step in order. -/
def evalState (s₀ : EVMState) (tr : ExecutionTrace) : EVMState :=
  tr.foldl applyStep s₀

/-- The EVM state immediately *before* step `tr[k]` would execute.
    By convention `stateAt s₀ tr 0 = s₀`. -/
def stateAt (s₀ : EVMState) (tr : ExecutionTrace) (k : Nat) : EVMState :=
  evalState s₀ (tr.take k)

/-- Lookup a storage slot at trace position `k` (state immediately before
    step `k` would execute). -/
def slotAt (s₀ : EVMState) (tr : ExecutionTrace) (k : Nat)
    (a : Address) (key : Word256) : Word256 :=
  (stateAt s₀ tr k).lookupSlot a key

/-! ## Inductive Step relation (Phase 3 Session 2, 2026-04-27)

The function `applyStep` defines a *deterministic* state transition.
Lifting it to an inductive `Prop`-valued relation `StepRel` provides
the relational view used in Phase 4+ proofs (where induction over
the step relation is more ergonomic than induction over the trace
list directly). The two views are equivalent.
-/

/-- The single-step transition relation. `StepRel s₁ st s₂` holds iff
    applying step `st` to state `s₁` yields state `s₂`. -/
inductive StepRel : EVMState → EVMStep → EVMState → Prop where
  | mk (s : EVMState) (st : EVMStep) : StepRel s st (applyStep s st)

theorem StepRel.iff (s : EVMState) (st : EVMStep) (s' : EVMState) :
    StepRel s st s' ↔ s' = applyStep s st :=
  ⟨fun h => by cases h; rfl, fun h => h ▸ StepRel.mk s st⟩

/-- The multi-step trace relation: `ExecuteTrace s tr s'` iff executing
    every step of `tr` from state `s` yields state `s'`. Equivalent to
    `s' = evalState s tr` by `evalState_eq_executeTrace`. -/
inductive ExecuteTrace : EVMState → ExecutionTrace → EVMState → Prop where
  | nil (s : EVMState) : ExecuteTrace s [] s
  | cons (s : EVMState) (st : EVMStep) (s' : EVMState)
         (tr : ExecutionTrace) (s'' : EVMState) :
      StepRel s st s' →
      ExecuteTrace s' tr s'' →
      ExecuteTrace s (st :: tr) s''

theorem ExecuteTrace.iff_evalState (s : EVMState) (tr : ExecutionTrace) (s' : EVMState) :
    ExecuteTrace s tr s' ↔ s' = evalState s tr := by
  constructor
  · intro h; induction h with
    | nil _ => rfl
    | cons s₀ st s₁ tr s_end hstep _hrest ih =>
      cases hstep
      simp [evalState, ih]
  · intro h
    subst h
    induction tr generalizing s with
    | nil => exact ExecuteTrace.nil s
    | cons st rest ih =>
      apply ExecuteTrace.cons s st (applyStep s st) rest (evalState (applyStep s st) rest)
      · exact StepRel.mk s st
      · simp [evalState]; exact ih (applyStep s st)

/-! ## Slot-stability lemmas (Phase 4 Session 7.2)

The substantive proof of `oz_guard_prevents_reentrancy` requires
tracking how a specific storage slot evolves across a trace. The
two lemmas here are the trace-semantics infrastructure used by
`OZSoundness.guard_locked_during_call`.

* **`slot_unchanged_by_non_sstore`** — single-step claim: any step
  that is *not* an SSTORE on `(a, key)` leaves slot `(a, key)` of
  the global state unchanged.

* **`slot_stable_no_sstore`** — multi-step claim: between two trace
  positions `p ≤ q`, if no step in `[p, q)` is an SSTORE on
  `(a, key)`, then the slot value at `p` and `q` is the same.
-/

/-- Predicate: `step` writes to slot `(a, key)` of the global state. -/
def EVMStep.IsSStoreOn (step : EVMStep) (a : Address) (key : Word256) : Prop :=
  ∃ val : Word256, step = EVMStep.sstore a key val

/-- **Lemma 1 (Phase 4 Session 7.2).** Any step that does not write to
    slot `(a, key)` leaves that slot unchanged in the global state.

    Case analysis on `EVMStep` constructors:
    * `.sstore addr' key' val'` — split on whether `(addr', key') = (a, key)`.
      If equal, contradicts the hypothesis. Otherwise, `Finmap.lookup_insert_of_ne`
      and `Finmap.lookup_erase_ne` show the lookup is preserved.
    * `.call _ _ _`, `.ret _`, `.revert` — `applyStep` returns `s` unchanged
      by definition, so the lookup is trivially equal. -/
theorem slot_unchanged_by_non_sstore (s : EVMState) (step : EVMStep)
    (a : Address) (key : Word256) (h : ¬ step.IsSStoreOn a key) :
    (applyStep s step).lookupSlot a key = s.lookupSlot a key := by
  cases step with
  | call _ _ _ => rfl
  | ret _ => rfl
  | revert => rfl
  | sstore addr' key' val' =>
    by_cases haddr : addr' = a
    · by_cases hkey : key' = key
      · -- step IS sstore a key val' — contradicts h
        exfalso
        apply h
        exact ⟨val', by rw [haddr, hkey]⟩
      · -- addr' = a, key' ≠ key: SSTORE on different slot of same address
        unfold applyStep EVMState.lookupSlot Storage.lookupZ
        rw [haddr]
        simp only [Finmap.lookup_insert]
        rw [Finmap.lookup_insert_of_ne _ (Ne.symm hkey)]
        cases hl : Finmap.lookup a s with
        | none => simp [Storage.empty]
        | some storage => rfl
    · -- addr' ≠ a: SSTORE on different address entirely
      unfold applyStep EVMState.lookupSlot
      rw [Finmap.lookup_insert_of_ne _ (Ne.symm haddr),
          Finmap.lookup_erase_ne (Ne.symm haddr)]

/-- **Lemma 2 (Phase 4 Session 7.2).** If no step in trace positions
    `[p, q)` is an SSTORE on `(a, key)`, then slot `(a, key)` has the
    same value at `p` and at `q`.

    Induction on `q - p` over the foldl in `evalState`. Uses
    `slot_unchanged_by_non_sstore` at each step. -/
theorem slot_stable_no_sstore (s₀ : EVMState) (tr : ExecutionTrace)
    (a : Address) (key : Word256) (p q : Nat) (hpq : p ≤ q)
    (hq : q ≤ tr.length)
    (h : ∀ k, p ≤ k → k < q →
      ∀ step, tr[k]? = some step → ¬ step.IsSStoreOn a key) :
    slotAt s₀ tr p a key = slotAt s₀ tr q a key := by
  induction q, hpq using Nat.le_induction with
  | base => rfl
  | succ q hpq ih =>
    have hq' : q ≤ tr.length := Nat.le_of_succ_le hq
    have h' : ∀ k, p ≤ k → k < q →
        ∀ step, tr[k]? = some step → ¬ step.IsSStoreOn a key := by
      intro k hpk hkq step hstep
      exact h k hpk (Nat.lt_succ_of_lt hkq) step hstep
    have ih' := ih hq' h'
    rw [ih']
    have hq_lt : q < tr.length := hq
    have hstep : tr[q]? = some (tr[q]'hq_lt) := List.getElem?_eq_getElem hq_lt
    have hnotSSTORE : ¬ (tr[q]'hq_lt).IsSStoreOn a key :=
      h q hpq (Nat.lt_succ_self q) (tr[q]'hq_lt) hstep
    have htake : tr.take (q + 1) = tr.take q ++ [tr[q]'hq_lt] := by
      rw [List.take_add_one, hstep]
      rfl
    show slotAt s₀ tr q a key = slotAt s₀ tr (q + 1) a key
    unfold slotAt stateAt evalState
    rw [htake, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    exact (slot_unchanged_by_non_sstore _ (tr[q]'hq_lt) a key hnotSSTORE).symm

end QanaryContracts
