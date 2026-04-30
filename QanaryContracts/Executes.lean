/-
  QanaryContracts/Executes.lean

  Phase 5 Session 3 — F4 body-to-trace lift, Step 1 skeleton.

  Defines the operational-semantics predicate `executes_C` characterizing
  traces that are faithful executions of one of `C.functions` from an
  initial state. Per Ray's Phase 5 Session 3 directive (2026-04-28) +
  Q-F4-1..6 confirmation:

  * Q-F4-1 — Style B: universal quantification over C-frame projections
    (reuses currentFrameAt infrastructure; no parallel operational
    machinery).
  * Q-F4-2 — Existential dispatch: ∃ f ∈ C.functions, MatchesBody f segment.
  * Q-F4-3 — Black-box sub-frames: sub-frame contents unconstrained
    beyond ValidExecution.
  * Q-F4-4 — Faithfulness C1-C5 (C1 lift, C2 sanity, C3-C4 named
    limitations, C5 §11 already covered).
  * Q-F4-5 — Single-call bodies only; multi-call is the named F2
    limitation.
  * Q-F4-6 — New file (this); the LIFT theorem
    `ozGuardDiscipline_implies_RTO` lives in `BodyTraceLift.lean`
    (next session).

  This file ships only the definition layer + two sanity lemmas + two
  test cases verifying MatchesBody's distinguishing power. No lift
  theorem; no F2 / F4 substantive proof work.
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

/-! ## Step 0 — projection-index → trace-position bridge

The L1 / L2 / L3 helpers (Phase 5 Session 6) need to convert "the i-th
element of the C-frame projection equals s" into "there is a trace
position p in `[start, finish)` with `currentFrameAt tr p = some C.address`
and `tr[p]? = some s`". This is the only structural fact about
`cFrameProjection` we need to expose; everything else operates on
positions in `tr`. -/

/-- **Step 0 helper.** If `(cFrameProjection C tr start finish)[i]? = some s`,
    then there exists a trace position `p` in `[start, finish)` at which
    `C` is the current frame and `tr[p]? = some s`. -/
private lemma cFrameProjection_get?_eq_some_iff
    (C : Contract) (tr : ExecutionTrace) (start finish : Nat)
    (i : Nat) (s : EVMStep)
    (h : (cFrameProjection C tr start finish)[i]? = some s) :
    ∃ p, start ≤ p ∧ p < finish ∧
         currentFrameAt tr p = some C.address ∧
         tr[p]? = some s := by
  unfold cFrameProjection at h
  have h_mem : s ∈ (((List.range' start (finish - start)).filter
        (fun p => decide (currentFrameAt tr p = some C.address))).filterMap
          (fun p => tr[p]?)) := List.mem_of_getElem? h
  rw [List.mem_filterMap] at h_mem
  obtain ⟨p, h_p_mem_filter, h_p_eq⟩ := h_mem
  rw [List.mem_filter] at h_p_mem_filter
  obtain ⟨h_p_range, h_p_dec⟩ := h_p_mem_filter
  rw [List.mem_range'] at h_p_range
  obtain ⟨j, h_j_lt, h_p_eq_idx⟩ := h_p_range
  refine ⟨p, ?_, ?_, ?_, h_p_eq⟩
  · omega
  · omega
  · have := of_decide_eq_true h_p_dec
    exact this

/-! ## L1 helpers — `unfoldBody` shape under `IsOZGuardedFunction` -/

/-- Bool predicate: this step is a CALL. -/
private def isCallStep : EVMStep → Bool
  | EVMStep.call _ _ _ => true
  | _ => false

/-- A `liftStep`-mapped list of body steps with `NoCallInSteps` has zero CALLs. -/
private lemma countP_isCallStep_map_liftStep_NoCall
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
private lemma unfoldBody_countP_isCallStep_eq_one
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
private lemma unfoldBody_call_callee_ne_C
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

/-- A list with two distinct elements satisfying a predicate has `countP ≥ 2`. -/
private lemma two_le_countP_of_distinct {α : Type*} {p : α → Bool} {a b : α}
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

/-- Generic countP for `cFrameProjection`. The projection's `P`-count equals
    the count over the underlying range list of "currentFrameAt-and-step-P". -/
private lemma cFrameProjection_countP_eq
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
private lemma cFrameProjection_countP_ge_two
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

/-- Bool predicate: this step is the lock SSTORE for contract `C`. -/
private def isLockStep (C : Contract) : EVMStep → Bool :=
  fun s => decide (s = EVMStep.sstore C.address C.guardSlot C.lockedValue)

/-- A `liftStep`-mapped list of body steps with `NoSStoreOnGuardSlotInSteps`
    has zero lock SSTOREs. -/
private lemma countP_isLockStep_map_liftStep_NoSStore
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
private lemma unfoldBody_countP_isLockStep_eq_one
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
  -- isLockStep on each individual step:
  -- lock SSTORE → true; call → false; unlock SSTORE → false (distinct); ret → false
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

/-! ## L1 helper: cFrameProjection head?

The next two helpers are used by L1 (body-faithful traces have no
nested C-frames). The first depends only on `cFrameProjection`; the
others depend on `MatchesBody` and `executes_C` and live below. -/

/-- The first element of `cFrameProjection C tr (k+1) finish` (when
    `k+1 < finish` and `currentFrameAt tr (k+1) = some C.address`) is
    `tr[k+1]?`. Standard filterMap-on-cons reasoning. -/
private lemma cFrameProjection_head?_at_kplus1
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

/-! ## `MatchesBody`

`MatchesBody C f tr entry finish` says that the function body `f` is
faithfully executed by the C-frame opened at the entry CALL at position
`entry` and closed at position `finish`. This is the body-to-trace
*conformance* relation: it tracks neither sub-frame contents (per Q-F4-3)
nor the dispatch oracle (per Q-F4-2 — dispatch is existential at the
`executes_C` level).

Five conjuncts:

1. `entry < finish` — the segment is non-empty.
2. `finish ≤ tr.length` — the segment is in bounds.
3. `tr[entry]?` is a CALL into `C.address` (the entry CALL).
4. `frameDepthAt tr entry = frameDepthAt tr finish` — the C-frame
   opened at `entry` is exactly closed by position `finish`.
5. The C-frame projection of `tr` over `[entry+1, finish)` equals
   `unfoldBody C f` (the body-faithfulness condition). -/

/-- The body-to-trace conformance predicate for a single C-frame. -/
def MatchesBody (C : Contract) (f : FunctionBody) (tr : ExecutionTrace)
    (entry finish : Nat) : Prop :=
  entry < finish ∧
  finish ≤ tr.length ∧
  (∃ caller value, tr[entry]? = some (EVMStep.call caller C.address value)) ∧
  frameDepthAt tr entry = frameDepthAt tr finish ∧
  cFrameProjection C tr (entry + 1) finish = unfoldBody C f

/-! ## `executes_C` -/

/-- `executes_C C s₀ tr` — `tr` is a faithful operational execution of
    `C.functions` from initial state `s₀`. Every entry CALL into
    `C.address` in `tr` dispatches to *some* function in `C.functions`
    whose unfolded body matches the C-frame projection of the
    corresponding C-frame.

    Per Q-F4 confirmations (2026-04-28):
    * Style B (Q-F4-1) — universal quantification over C-frame
      projections.
    * Existential dispatch (Q-F4-2) — `∃ f ∈ C.functions`.
    * Black-box sub-frames (Q-F4-3) — sub-frame contents unconstrained
      beyond `ValidExecution`. -/
def executes_C (C : Contract) (s₀ : EVMState) (tr : ExecutionTrace) : Prop :=
  ValidExecution tr ∧
  InitialGuardUnlocked C s₀ ∧
  ∀ (k : Nat) (caller : Address) (value : Word256),
    k < tr.length →
    tr[k]? = some (EVMStep.call caller C.address value) →
    ∃ (f : FunctionBody) (finish : Nat),
      f ∈ C.functions ∧ MatchesBody C f tr k finish

/-! ## Sanity lemmas (faithfulness criterion C2) -/

/-- `ValidExecution` holds vacuously on the empty trace. Local helper
    for the empty-trace `executes_C` lemma. -/
private theorem validExecution_nil : ValidExecution ([] : ExecutionTrace) := by
  refine ⟨?_, ?_, ?_⟩
  · intro ⟨k, hk⟩
    exact absurd hk (by simp)
  · intro ⟨k, hk⟩
    exact absurd hk (by simp)
  · intro ⟨k, hk⟩
    exact absurd hk (by simp)

/-- **Sanity 1 — empty trace.** The empty trace satisfies `executes_C`
    whenever `s₀` has C's guard unlocked. F4 lift's edge case. -/
theorem executes_C_empty (C : Contract) (s₀ : EVMState)
    (h : InitialGuardUnlocked C s₀) :
    executes_C C s₀ [] := by
  refine ⟨validExecution_nil, h, ?_⟩
  intro k _ _ hk _
  exact absurd hk (by simp)

/-- **Sanity 2 — no entries.** If `tr` contains no CALL into `C.address`,
    then `executes_C` reduces to `ValidExecution + InitialGuardUnlocked`
    (the dispatch obligation discharges vacuously). F4 lift's
    "no-entry" edge case. -/
theorem executes_C_no_C_calls (C : Contract) (s₀ : EVMState)
    (tr : ExecutionTrace)
    (h_valid : ValidExecution tr)
    (h_init : InitialGuardUnlocked C s₀)
    (h_no_calls : ∀ (k : Nat) (caller : Address) (value : Word256),
      tr[k]? ≠ some (EVMStep.call caller C.address value)) :
    executes_C C s₀ tr := by
  refine ⟨h_valid, h_init, ?_⟩
  intro k caller value _ h_call
  exact absurd h_call (h_no_calls k caller value)

/-! ## Test cases — VRVP discipline (Phase 5 Session 3 directive)

Two MatchesBody test cases per Ray's Phase 5 Session 3 directive,
verifying MatchesBody's distinguishing power before any
`BodyTraceLift.lean` lift-theorem work begins:

* **Test 1 (positive):** OZ-shaped body matches the OZ witness trace.
* **Test 2 (negative):** non-OZ body does NOT match the OZ witness
  trace.
-/

/-- **Test 1 (positive — OZ-shaped body matches OZ witness trace).**
    `ozWitnessFunction` (`lock → call → unlock → ret`) matches
    `ozWitnessTrace` via `MatchesBody`, with the entry CALL at
    position 0 and the C-frame closing at position 6 (= trace
    length). C-frame projection at positions [1, 2, 4, 5] (excluding
    sub-frame position 3) equals `unfoldBody ozWitnessContract
    ozWitnessFunction`. -/
theorem ozWitnessFunction_matchesBody :
    MatchesBody ozWitnessContract ozWitnessFunction ozWitnessTrace 0 6 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- 0 < 6
    decide
  · -- 6 ≤ ozWitnessTrace.length (= 6)
    decide
  · -- entry CALL into C
    refine ⟨ozWitnessUser, ⟨0, by decide⟩, ?_⟩
    rfl
  · -- frameDepthAt ozWitnessTrace 0 = frameDepthAt ozWitnessTrace 6
    -- (both = 0; trace is balanced)
    decide
  · -- cFrameProjection ozWitnessContract ozWitnessTrace 1 6
    --   = unfoldBody ozWitnessContract ozWitnessFunction
    decide

/-- A simple non-OZ body — single SSTORE then RET. Lacks the
    `lock → call → unlock → ret` structure of `IsOZGuardedFunction`
    and has only 2 steps (vs. `ozWitnessFunction`'s 4). -/
def simpleNonOZBody : FunctionBody :=
  [FunctionBody.Step.sstore ozWitnessGuardSlot ⟨1, by decide⟩,
   FunctionBody.Step.ret true]

/-- **Test 2 (negative — non-OZ body does not match OZ witness trace).**
    `simpleNonOZBody` (length 2) does NOT match `ozWitnessTrace` via
    `MatchesBody`: its unfolded body has 2 elements while the C-frame
    projection has 4 elements (lock SSTORE, external CALL, unlock
    SSTORE, ret). MatchesBody's body-faithfulness conjunct rejects
    this length mismatch. -/
theorem simpleNonOZBody_does_not_matchBody :
    ¬ MatchesBody ozWitnessContract simpleNonOZBody ozWitnessTrace 0 6 := by
  intro h
  obtain ⟨_, _, _, _, h_eq⟩ := h
  exact absurd h_eq (by decide)

/-! ## L1 — body-faithful traces have no nested C-frames

Phase 5 Session 6, Step 1 (Path B). Under `executes_C` and
`OZGuardDiscipline`, two distinct entry CALLs into `C.address` cannot
be nested. Used by `BodyTraceLift.lean`'s Conjuncts 3 and 4 (via L2
and L3, in the same file). -/

/-- Under `MatchesBody` for OZ-guarded `f`, the trace step at `k+1` is the
    body's lock SSTORE. -/
private lemma matchesBody_implies_tr_kplus1_eq_lock
    (C : Contract) (tr : ExecutionTrace) (k finish : Nat)
    (caller : Address) (value : Word256)
    (h_call : tr[k]? = some (EVMStep.call caller C.address value))
    (f : FunctionBody) (h_oz : IsOZGuardedFunction C f)
    (h_match : MatchesBody C f tr k finish) :
    tr[k+1]? = some (EVMStep.sstore C.address C.guardSlot C.lockedValue) := by
  obtain ⟨_, h_fle, _, _, h_proj⟩ := h_match
  obtain ⟨pre, callee_outer, value_outer, post, h_eq_body, _, _, _, _, _⟩ := h_oz
  have h_cf : currentFrameAt tr (k + 1) = some C.address :=
    currentFrameAt_after_call tr k caller C.address value h_call
  have h_unf : unfoldBody C f =
      EVMStep.sstore C.address C.guardSlot C.lockedValue ::
        (pre.map (liftStep C) ++
          EVMStep.call C.address callee_outer value_outer ::
          ((post ++
            [FunctionBody.Step.sstore C.guardSlot C.unlockedValue,
             FunctionBody.Step.ret true]).map (liftStep C))) := by
    unfold unfoldBody; rw [h_eq_body]; simp [List.map_cons, List.map_append, liftStep]
  have h_unf_head : (unfoldBody C f).head? =
      some (EVMStep.sstore C.address C.guardSlot C.lockedValue) := by
    rw [h_unf]; rfl
  have h_unf_len_ge : (unfoldBody C f).length ≥ 4 := by
    rw [h_unf]; simp [List.length_cons, List.length_append]; omega
  have h_proj_len_eq : (cFrameProjection C tr (k+1) finish).length = (unfoldBody C f).length :=
    by rw [h_proj]
  have h_range_ge : finish - (k+1) ≥ 4 := by
    have h_le : (cFrameProjection C tr (k+1) finish).length ≤ finish - (k+1) := by
      unfold cFrameProjection
      calc (((List.range' (k+1) (finish - (k+1))).filter
                (fun p => decide (currentFrameAt tr p = some C.address))).filterMap
                (fun p => tr[p]?)).length
          ≤ ((List.range' (k+1) (finish - (k+1))).filter
                (fun p => decide (currentFrameAt tr p = some C.address))).length :=
              List.length_filterMap_le _ _
        _ ≤ (List.range' (k+1) (finish - (k+1))).length := List.length_filter_le _ _
        _ = finish - (k+1) := List.length_range'
    rw [h_proj_len_eq] at h_le
    omega
  have hk1_lt_fin : k + 1 < finish := by omega
  have h_some : ∃ s, tr[k+1]? = some s := by
    have hk1_lt_tr : k + 1 < tr.length := lt_of_lt_of_le hk1_lt_fin h_fle
    cases h : tr[k+1]? with
    | none =>
      rw [List.getElem?_eq_none_iff] at h
      omega
    | some s => exact ⟨s, rfl⟩
  obtain ⟨s, h_s⟩ := h_some
  have h_proj_head := cFrameProjection_head?_at_kplus1 C tr k finish hk1_lt_fin h_cf s h_s
  have h_proj_head_eq_unf : (cFrameProjection C tr (k+1) finish).head? =
      (unfoldBody C f).head? := by rw [h_proj]
  rw [h_proj_head_eq_unf, h_unf_head] at h_proj_head
  rw [h_s, h_proj_head]

/-- **L1 (Phase 5 Session 6).** Under `executes_C` and `OZGuardDiscipline`
    with distinct lock/unlock values, two distinct entry CALLs into
    `C.address` cannot be nested. -/
theorem executes_C_no_nested_C_frame
    (C : Contract) (h_oz : OZGuardDiscipline C)
    (h_distinct : C.lockedValue ≠ C.unlockedValue)
    (s₀ : EVMState) (tr : ExecutionTrace)
    (h_exec : executes_C C s₀ tr)
    (k k' : Nat) (hk : k < tr.length) (hk' : k' < tr.length)
    (caller caller' : Address) (value value' : Word256)
    (h_call : tr[k]? = some (EVMStep.call caller C.address value))
    (h_call' : tr[k']? = some (EVMStep.call caller' C.address value'))
    (hkk' : k < k') :
    ¬ NestedAfter tr k k' := by
  intro h_nest
  obtain ⟨_, _, h_dispatch⟩ := h_exec
  obtain ⟨_, h_oz_all⟩ := h_oz
  obtain ⟨f, finish, hf_mem, h_match⟩ := h_dispatch k caller value hk h_call
  obtain ⟨h_klt, h_fle, _, h_depth_eq, h_proj⟩ := h_match
  have h_isOZ : IsOZGuardedFunction C f := h_oz_all f hf_mem
  have hk'_lt_finish : k' < finish := by
    by_contra h_ge; push_neg at h_ge
    have h_d : finish - k - 1 < k' - k := by omega
    have h_n := h_nest ⟨finish - k - 1, h_d⟩
    have h_eq : k + 1 + (finish - k - 1) = finish := by omega
    rw [h_eq] at h_n
    omega
  by_cases h_cf_k' : currentFrameAt tr k' = some C.address
  · -- Case A: tr[k'] is a CALL with callee = C.address; unfoldBody has none.
    have h_in_proj : EVMStep.call caller' C.address value' ∈
        cFrameProjection C tr (k+1) finish := by
      unfold cFrameProjection
      rw [List.mem_filterMap]
      refine ⟨k', ?_, h_call'⟩
      rw [List.mem_filter, List.mem_range']
      refine ⟨⟨k' - (k+1), by omega, by omega⟩, by simp [h_cf_k']⟩
    rw [h_proj] at h_in_proj
    exact unfoldBody_call_callee_ne_C C f h_isOZ caller' C.address value' h_in_proj rfl
  · -- Case B: count lock SSTOREs at positions k+1 and k'+1.
    obtain ⟨f', finish_inner, hf'_mem, h_match'⟩ :=
      h_dispatch k' caller' value' hk' h_call'
    have h_isOZ' : IsOZGuardedFunction C f' := h_oz_all f' hf'_mem
    have h_tr_kp1 := matchesBody_implies_tr_kplus1_eq_lock C tr k finish caller value
                       h_call f h_isOZ ⟨h_klt, h_fle, ⟨caller, value, h_call⟩,
                                          h_depth_eq, h_proj⟩
    have h_tr_kp1' := matchesBody_implies_tr_kplus1_eq_lock C tr k' finish_inner caller' value'
                        h_call' f' h_isOZ' h_match'
    have h_cf_kp1 : currentFrameAt tr (k+1) = some C.address :=
      currentFrameAt_after_call tr k caller C.address value h_call
    have h_cf_kp1' : currentFrameAt tr (k'+1) = some C.address :=
      currentFrameAt_after_call tr k' caller' C.address value' h_call'
    -- k'+1 < finish: if finish = k'+1, depth(finish) = depth(k'+1) = depth(k')+1, but
    -- depth(finish) = depth(k) and NestedAfter at k' gives depth(k') > depth(k).
    have hkp1_lt_finish : k' + 1 < finish := by
      by_contra h_ge
      push_neg at h_ge
      have h_finish_eq : finish = k'+1 := by omega
      rw [h_finish_eq] at h_depth_eq
      have h_dep_kp1 := frameDepthAt_after_call tr k' caller' C.address value' h_call'
      have h_d_k' : k' - k - 1 < k' - k := by omega
      have h_n_k' := h_nest ⟨k' - k - 1, h_d_k'⟩
      have h_eq_k' : k + 1 + (k' - k - 1) = k' := by omega
      rw [h_eq_k'] at h_n_k'
      omega
    have h_count_proj_ge : 2 ≤ (cFrameProjection C tr (k+1) finish).countP (isLockStep C) := by
      apply cFrameProjection_countP_ge_two C tr (k+1) finish (isLockStep C) (k+1) (k'+1)
      · omega
      · omega
      · exact hkp1_lt_finish
      · exact h_cf_kp1
      · exact h_cf_kp1'
      · exact h_tr_kp1
      · exact h_tr_kp1'
      · simp [isLockStep]
      · simp [isLockStep]
    have h_count_unf : (unfoldBody C f).countP (isLockStep C) = 1 :=
      unfoldBody_countP_isLockStep_eq_one C f h_isOZ h_distinct
    rw [h_proj] at h_count_proj_ge
    omega

end QanaryContracts
