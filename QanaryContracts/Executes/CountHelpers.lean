/-
  QanaryContracts/Executes/CountHelpers.lean

  Phase 5 Session 7 γ — count-arithmetic helpers for body-faithful trace
  reasoning.

  Originally introduced in Session 6 as private helpers in
  `Executes.lean` during L1 development. Relocated here in Session 7 so
  L2 (`executes_C_guard_unlocked_at_entry`) and L3
  (`executes_C_guard_locked_during_body_call`) — which live in
  `BodyTraceLift.lean` — can share the bench. The Step 0 bridge helper
  `cFrameProjection_get?_eq_some_iff` stays in `Executes.lean` adjacent
  to L1 per Ray's Session 7 γ directive (Part 2.3).

  Contents:
  * `liftStep`, `unfoldBody`, `cFrameProjection` — the body-faithfulness
    primitives (originally introduced in Session 3's `Executes.lean`).
  * Bool predicates `isCallStep`, `isLockStep`.
  * `countP_isCallStep_map_liftStep_NoCall`,
    `unfoldBody_countP_isCallStep_eq_one`,
    `unfoldBody_call_callee_ne_C` — Case A killers for L1.
  * `two_le_countP_of_distinct` — generic `List.countP` lemma.
  * `cFrameProjection_countP_eq`,
    `cFrameProjection_countP_ge_two` — generic count arithmetic over the
    C-frame projection.
  * `countP_isLockStep_map_liftStep_NoSStore`,
    `unfoldBody_countP_isLockStep_eq_one` — Case B killers for L1
    (lock-SSTORE counting under `h_distinct`).
  * `cFrameProjection_head?_at_kplus1` — projection's first element
    equals `tr[k+1]?` when `currentFrameAt tr (k+1) = some C.address`.
-/
import QanaryContracts.EVM
import QanaryContracts.Storage
import QanaryContracts.Step
import QanaryContracts.CEI
import QanaryContracts.Contract
import QanaryContracts.FunctionBody
import QanaryContracts.ValidExecution
import QanaryContracts.Reachability
import QanaryContracts.OZSoundness

namespace QanaryContracts

/-! ## `liftStep` and `unfoldBody`

A `FunctionBody.Step` carries no caller/owner address — when the contract
`C` executes the step, the caller (for CALL) and storage owner (for
SSTORE) are implicitly `C.address`. `liftStep C` fills in `C.address` to
produce the corresponding trace-level `EVMStep`. -/

/-- Lift a `FunctionBody.Step` to an `EVMStep` using `C.address` as the
    implicit caller / storage owner. -/
def liftStep (C : Contract) : FunctionBody.Step → EVMStep
  | .sstore key val      => EVMStep.sstore C.address key val
  | .call callee value   => EVMStep.call C.address callee value
  | .ret success         => EVMStep.ret success
  | .revert              => EVMStep.revert

/-- Unfold a function body to a list of trace-level `EVMStep`s. -/
def unfoldBody (C : Contract) (f : FunctionBody) : List EVMStep :=
  f.map (liftStep C)

/-! ## C-frame projection

The C-frame projection extracts, from a trace, the sub-list of steps
that occur while `C` is the currently-executing frame. Sub-frame steps
(where C has called out to another contract β and we are inside β)
are excluded — those are not part of any function body of C. -/

/-- The C-frame projection of `tr` over the half-open range
    `[start, finish)`: the list of `EVMStep`s at trace positions
    `p ∈ [start, finish)` for which `currentFrameAt tr p = some C.address`.

    Implementation: enumerate `[start, start+1, ..., finish-1]`, filter
    to positions where the current frame is `C.address`, then look up
    each filtered position's step in `tr`. -/
def cFrameProjection (C : Contract) (tr : ExecutionTrace)
    (start finish : Nat) : List EVMStep :=
  ((List.range' start (finish - start)).filter
    (fun p => decide (currentFrameAt tr p = some C.address))).filterMap
      (fun p => tr[p]?)

/-! ## Bool step predicates -/

/-- Bool predicate: this step is a CALL. -/
def isCallStep : EVMStep → Bool
  | EVMStep.call _ _ _ => true
  | _ => false

/-- Bool predicate: this step is the lock SSTORE for contract `C`. -/
def isLockStep (C : Contract) : EVMStep → Bool :=
  fun s => decide (s = EVMStep.sstore C.address C.guardSlot C.lockedValue)

/-! ## `unfoldBody` count helpers -/

/-- A `liftStep`-mapped list of body steps with `NoCallInSteps` has zero CALLs. -/
theorem countP_isCallStep_map_liftStep_NoCall
    (C : Contract) (steps : List FunctionBody.Step) (h : NoCallInSteps steps) :
    (steps.map (liftStep C)).countP isCallStep = 0 := by
  induction steps with
  | nil => rfl
  | cons hd tl ih =>
    have h_hd_not_call : ¬ ∃ callee value, hd = FunctionBody.Step.call callee value :=
      h hd (List.mem_cons.mpr (Or.inl rfl))
    have h_tl : NoCallInSteps tl :=
      fun s hs => h s (List.mem_cons.mpr (Or.inr hs))
    have h_ih := ih h_tl
    have h_isCall_hd : isCallStep (liftStep C hd) = false := by
      cases hd with
      | sstore _ _ => rfl
      | call callee value => exact absurd ⟨callee, value, rfl⟩ h_hd_not_call
      | ret _ => rfl
      | revert => rfl
    show ((liftStep C hd) :: tl.map (liftStep C)).countP isCallStep = 0
    rw [List.countP_cons, h_isCall_hd, h_ih]
    rfl

/-- For OZ-guarded f, `unfoldBody C f` contains exactly one CALL element. -/
theorem unfoldBody_countP_isCallStep_eq_one
    (C : Contract) (f : FunctionBody) (h_oz : IsOZGuardedFunction C f) :
    (unfoldBody C f).countP isCallStep = 1 := by
  obtain ⟨pre, callee_outer, value_outer, post, h_eq, _, h_pre_nc,
          h_post_nc, _, _⟩ := h_oz
  unfold unfoldBody
  rw [h_eq]
  simp only [List.map_cons, List.map_append, liftStep,
             List.countP_cons, List.countP_append, isCallStep]
  rw [countP_isCallStep_map_liftStep_NoCall C pre h_pre_nc,
      countP_isCallStep_map_liftStep_NoCall C post h_post_nc]
  simp

/-- Any CALL step in `unfoldBody C f` (for OZ-guarded f) has `callee ≠ C.address`. -/
theorem unfoldBody_call_callee_ne_C
    (C : Contract) (f : FunctionBody) (h_oz : IsOZGuardedFunction C f)
    (caller callee : Address) (value : Word256)
    (h_mem : EVMStep.call caller callee value ∈ unfoldBody C f) :
    callee ≠ C.address := by
  obtain ⟨pre, callee_outer, value_outer, post, h_eq, h_callee_ne, h_pre_nc,
          h_post_nc, _, _⟩ := h_oz
  have h_unf : unfoldBody C f =
      EVMStep.sstore C.address C.guardSlot C.lockedValue ::
        (pre.map (liftStep C) ++
          EVMStep.call C.address callee_outer value_outer ::
          ((post ++
            [FunctionBody.Step.sstore C.guardSlot C.unlockedValue,
             FunctionBody.Step.ret true]).map (liftStep C))) := by
    unfold unfoldBody
    rw [h_eq]
    simp [List.map_cons, List.map_append, liftStep]
  rw [h_unf] at h_mem
  rw [List.mem_cons, List.mem_append, List.mem_cons, List.mem_map,
      List.mem_map] at h_mem
  rcases h_mem with h | h | h | h
  · exact absurd h (by simp)
  · obtain ⟨x, h_x_mem, h_x_eq⟩ := h
    cases x with
    | sstore _ _ => simp [liftStep] at h_x_eq
    | call callee' value' =>
      exact absurd ⟨callee', value', rfl⟩ (h_pre_nc _ h_x_mem)
    | ret _ => simp [liftStep] at h_x_eq
    | revert => simp [liftStep] at h_x_eq
  · injection h with _ h_callee _
    rw [h_callee]; exact h_callee_ne
  · obtain ⟨x, h_x_mem, h_x_eq⟩ := h
    rw [List.mem_append] at h_x_mem
    rcases h_x_mem with h_x_pre | h_x_tail
    · cases x with
      | sstore _ _ => simp [liftStep] at h_x_eq
      | call callee' value' =>
        exact absurd ⟨callee', value', rfl⟩ (h_post_nc _ h_x_pre)
      | ret _ => simp [liftStep] at h_x_eq
      | revert => simp [liftStep] at h_x_eq
    · simp at h_x_tail
      rcases h_x_tail with h_x_eq2 | h_x_eq2 <;> rw [h_x_eq2] at h_x_eq <;>
        simp [liftStep] at h_x_eq

/-! ## Generic `List.countP` lemma -/

/-- A list with two distinct elements satisfying a predicate has `countP ≥ 2`. -/
theorem two_le_countP_of_distinct {α : Type*} {p : α → Bool} {a b : α}
    {l : List α}
    (ha : p a = true) (hb : p b = true) (hab : a ≠ b)
    (ha_mem : a ∈ l) (hb_mem : b ∈ l) (h_nodup : l.Nodup) :
    2 ≤ l.countP p := by
  induction l with
  | nil => simp at ha_mem
  | cons hd tl ih =>
    rw [List.nodup_cons] at h_nodup
    obtain ⟨_, h_tl_nodup⟩ := h_nodup
    rw [List.mem_cons] at ha_mem hb_mem
    rw [List.countP_cons]
    rcases ha_mem with rfl | ha_mem
    · rcases hb_mem with rfl | hb_mem
      · exact absurd rfl hab
      · have h_pos : 0 < tl.countP p := List.countP_pos_iff.mpr ⟨_, hb_mem, hb⟩
        rw [if_pos ha]; omega
    · rcases hb_mem with rfl | hb_mem
      · have h_pos : 0 < tl.countP p := List.countP_pos_iff.mpr ⟨_, ha_mem, ha⟩
        rw [if_pos hb]; omega
      · have ih' := ih ha_mem hb_mem h_tl_nodup
        split_ifs <;> omega

/-! ## `cFrameProjection` count arithmetic -/

/-- Generic countP for `cFrameProjection`. The projection's `P`-count equals
    the count over the underlying range list of "currentFrameAt-and-step-P". -/
theorem cFrameProjection_countP_eq
    (C : Contract) (tr : ExecutionTrace) (start finish : Nat)
    (P : EVMStep → Bool) :
    (cFrameProjection C tr start finish).countP P =
      (List.range' start (finish - start)).countP
        (fun p => decide (currentFrameAt tr p = some C.address) &&
          (match tr[p]? with | some s => P s | none => false)) := by
  unfold cFrameProjection
  generalize List.range' start (finish - start) = L
  induction L with
  | nil => rfl
  | cons hd tl ih =>
    rw [List.filter_cons]
    by_cases h_cf : decide (currentFrameAt tr hd = some C.address) = true
    · rw [if_pos h_cf, List.filterMap_cons, List.countP_cons]
      cases h_get : tr[hd]? with
      | none => rw [ih]; simp [h_cf]
      | some s => rw [List.countP_cons, ih]; simp [h_cf, h_get]
    · rw [if_neg h_cf, ih, List.countP_cons]
      simp at h_cf
      simp [h_cf]

/-- Given two distinct trace positions in `[start, finish)` both at
    `currentFrameAt = some C.address` with `P`-step values, the projection has
    `≥ 2` `P`-elements. -/
theorem cFrameProjection_countP_ge_two
    (C : Contract) (tr : ExecutionTrace) (start finish : Nat)
    (P : EVMStep → Bool)
    (p₁ p₂ : Nat) (h_lt : p₁ < p₂)
    (h_p₁_ge : start ≤ p₁) (h_p₂_lt : p₂ < finish)
    (h_p₁_cf : currentFrameAt tr p₁ = some C.address)
    (h_p₂_cf : currentFrameAt tr p₂ = some C.address)
    (s₁ s₂ : EVMStep)
    (h_p₁_tr : tr[p₁]? = some s₁) (h_p₂_tr : tr[p₂]? = some s₂)
    (h_p₁_P : P s₁ = true) (h_p₂_P : P s₂ = true) :
    2 ≤ (cFrameProjection C tr start finish).countP P := by
  rw [cFrameProjection_countP_eq]
  have h_p₁_lt : p₁ < finish := by omega
  have h_p₂_ge : start ≤ p₂ := by omega
  set Q : Nat → Bool := fun p =>
    decide (currentFrameAt tr p = some C.address) &&
    (match tr[p]? with | some s => P s | none => false) with hQ
  have hQ₁ : Q p₁ = true := by
    rw [hQ]; simp [h_p₁_cf, h_p₁_tr, h_p₁_P]
  have hQ₂ : Q p₂ = true := by
    rw [hQ]; simp [h_p₂_cf, h_p₂_tr, h_p₂_P]
  have h_p₁_mem : p₁ ∈ List.range' start (finish - start) := by
    rw [List.mem_range']
    exact ⟨p₁ - start, by omega, by omega⟩
  have h_p₂_mem : p₂ ∈ List.range' start (finish - start) := by
    rw [List.mem_range']
    exact ⟨p₂ - start, by omega, by omega⟩
  have h_p_ne : p₁ ≠ p₂ := by omega
  have h_nodup : List.Nodup (List.range' start (finish - start)) :=
    List.nodup_range'
  exact two_le_countP_of_distinct hQ₁ hQ₂ h_p_ne h_p₁_mem h_p₂_mem h_nodup

/-! ## Lock-SSTORE counting -/

/-- A `liftStep`-mapped list of body steps with `NoSStoreOnGuardSlotInSteps`
    has zero lock SSTOREs. -/
theorem countP_isLockStep_map_liftStep_NoSStore
    (C : Contract) (steps : List FunctionBody.Step)
    (h : NoSStoreOnGuardSlotInSteps C.guardSlot steps) :
    (steps.map (liftStep C)).countP (isLockStep C) = 0 := by
  induction steps with
  | nil => rfl
  | cons hd tl ih =>
    have h_tl : NoSStoreOnGuardSlotInSteps C.guardSlot tl := fun s hs =>
      h s (List.mem_cons.mpr (Or.inr hs))
    have h_hd : ¬ ∃ val, hd = FunctionBody.Step.sstore C.guardSlot val :=
      h hd (List.mem_cons.mpr (Or.inl rfl))
    have h_isLock_hd : isLockStep C (liftStep C hd) = false := by
      cases hd with
      | sstore key val =>
        simp only [liftStep, isLockStep, decide_eq_false_iff_not]
        intro h_eq_step
        injection h_eq_step with _ h_key _
        exact h_hd ⟨val, by rw [h_key]⟩
      | call _ _ => rfl
      | ret _ => rfl
      | revert => rfl
    show ((liftStep C hd) :: tl.map (liftStep C)).countP (isLockStep C) = 0
    rw [List.countP_cons, h_isLock_hd, ih h_tl]
    rfl

/-- For OZ-guarded f with distinct lock/unlock values, `unfoldBody C f` has
    exactly one occurrence of the lock SSTORE (the lock at index 0). -/
theorem unfoldBody_countP_isLockStep_eq_one
    (C : Contract) (f : FunctionBody) (h_oz : IsOZGuardedFunction C f)
    (h_distinct : C.lockedValue ≠ C.unlockedValue) :
    (unfoldBody C f).countP (isLockStep C) = 1 := by
  obtain ⟨pre, callee_outer, value_outer, post, h_eq, _, _,
          _, h_pre_no_sstore, h_post_no_sstore⟩ := h_oz
  unfold unfoldBody
  rw [h_eq]
  simp only [List.map_cons, List.map_append, liftStep,
             List.countP_cons, List.countP_append]
  rw [countP_isLockStep_map_liftStep_NoSStore C pre h_pre_no_sstore,
      countP_isLockStep_map_liftStep_NoSStore C post h_post_no_sstore]
  have h_lock_true : isLockStep C (EVMStep.sstore C.address C.guardSlot C.lockedValue) = true := by
    simp [isLockStep]
  have h_call_false : isLockStep C (EVMStep.call C.address callee_outer value_outer) = false := by
    simp [isLockStep]
  have h_unlock_false :
      isLockStep C (EVMStep.sstore C.address C.guardSlot C.unlockedValue) = false := by
    simp only [isLockStep, decide_eq_false_iff_not]
    intro h_eq_step
    injection h_eq_step with _ _ h_val
    exact h_distinct h_val.symm
  have h_ret_false : isLockStep C (EVMStep.ret true) = false := by simp [isLockStep]
  rw [h_lock_true, h_call_false, h_unlock_false, h_ret_false]
  simp

/-! ## Projection-head lemma -/

/-- The first element of `cFrameProjection C tr (k+1) finish` (when
    `k+1 < finish` and `currentFrameAt tr (k+1) = some C.address`) is
    `tr[k+1]?`. Standard filterMap-on-cons reasoning. -/
theorem cFrameProjection_head?_at_kplus1
    (C : Contract) (tr : ExecutionTrace) (k finish : Nat)
    (h_lt : k + 1 < finish)
    (h_cf : currentFrameAt tr (k + 1) = some C.address)
    (s : EVMStep) (h_get : tr[k+1]? = some s) :
    (cFrameProjection C tr (k+1) finish).head? = some s := by
  unfold cFrameProjection
  obtain ⟨n, hn⟩ : ∃ n, finish - (k + 1) = n + 1 :=
    ⟨finish - (k + 1) - 1, by omega⟩
  rw [hn]
  have h_dec : decide (currentFrameAt tr (k + 1) = some C.address) = true := by
    rw [h_cf]; simp
  show ((((k + 1) :: List.range' (k + 2) n).filter
          (fun p => decide (currentFrameAt tr p = some C.address))).filterMap
          (fun p => tr[p]?)).head? = some s
  simp only [List.filter_cons, h_dec, if_true, List.filterMap_cons,
             h_get, List.head?_cons]

end QanaryContracts
