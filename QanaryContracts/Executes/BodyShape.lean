/-
  QanaryContracts/Executes/BodyShape.lean

  Phase 5 Session 9 — Family C (body-shape extraction).

  Co-equal sibling of `CountHelpers.lean` (Family A: anti-nesting via
  count arithmetic) and `StackHistory.lean` (Family B: open-frame
  identification). The three-family infrastructure model identified
  at Session 8's close (W7) requires this third family to lift
  `executes_C` body-faithfulness into trace-level guard-value claims
  (L2 / L3 in `BodyTraceLift.lean`).

  Load-bearing exports:

  * `matchesBody_oz_extracts_positions` — central theorem: extract
    `p_call` and `p_unlock` from `MatchesBody` + `IsOZGuardedFunction`,
    with `q + 1 < p_call < p_unlock < finish`, `currentFrameAt`
    identifications, and `tr[]?` values (lock at `q+1`, CALL at
    `p_call`, unlock at `p_unlock`). VRVP-E (an internal session report
    §2) verifies the statement is sound.

  * `c_call_in_C_frame_eq_p_call` — uniqueness corollary: any C-issued
    CALL inside the C-frame is at `p_call` (count-arithmetic argument
    via `unfoldBody_countP_isCallStep_eq_one`).

  * `lock_position_unique_in_C_frame` /
    `unlock_position_unique_in_C_frame` — uniqueness of guard SSTOREs:
    only one lock at `q+1`, only one unlock at `p_unlock`.

  * `guard_sstore_value_in_C_frame` — value characterization: any
    SSTORE on `(C.address, C.guardSlot)` inside the C-frame writes
    `C.lockedValue` (the lock) or `C.unlockedValue` (the unlock); no
    other value is possible.
-/
import QanaryContracts.Executes
import QanaryContracts.Executes.CountHelpers
import QanaryContracts.Executes.StackHistory

namespace QanaryContracts

/-! ## Bool predicate: unlock SSTORE -/

/-- Bool predicate: this step is the unlock SSTORE for contract `C`. -/
def isUnlockStep (C : Contract) : EVMStep → Bool :=
  fun s => decide (s = EVMStep.sstore C.address C.guardSlot C.unlockedValue)

/-! ## `unfoldBody` count helpers (mirroring `isLockStep` counts) -/

/-- A `liftStep`-mapped list of body steps with `NoSStoreOnGuardSlotInSteps`
    has zero unlock SSTOREs. Symmetric to
    `countP_isLockStep_map_liftStep_NoSStore` in `CountHelpers.lean`. -/
theorem countP_isUnlockStep_map_liftStep_NoSStore
    (C : Contract) (steps : List FunctionBody.Step)
    (h : NoSStoreOnGuardSlotInSteps C.guardSlot steps) :
    (steps.map (liftStep C)).countP (isUnlockStep C) = 0 := by
  induction steps with
  | nil => rfl
  | cons hd tl ih =>
    have h_tl : NoSStoreOnGuardSlotInSteps C.guardSlot tl := fun s hs =>
      h s (List.mem_cons.mpr (Or.inr hs))
    have h_hd : ¬ ∃ val, hd = FunctionBody.Step.sstore C.guardSlot val :=
      h hd (List.mem_cons.mpr (Or.inl rfl))
    have h_isUnlock_hd : isUnlockStep C (liftStep C hd) = false := by
      cases hd with
      | sstore key val =>
        simp only [liftStep, isUnlockStep, decide_eq_false_iff_not]
        intro h_eq_step
        injection h_eq_step with _ h_key _
        exact h_hd ⟨val, by rw [h_key]⟩
      | call _ _ => rfl
      | ret _ => rfl
      | revert => rfl
    show ((liftStep C hd) :: tl.map (liftStep C)).countP (isUnlockStep C) = 0
    rw [List.countP_cons, h_isUnlock_hd, ih h_tl]
    rfl

/-- For OZ-guarded f with distinct lock/unlock values, `unfoldBody C f` has
    exactly one occurrence of the unlock SSTORE. Symmetric to
    `unfoldBody_countP_isLockStep_eq_one` in `CountHelpers.lean`. -/
theorem unfoldBody_countP_isUnlockStep_eq_one
    (C : Contract) (f : FunctionBody) (h_oz : IsOZGuardedFunction C f)
    (h_distinct : C.lockedValue ≠ C.unlockedValue) :
    (unfoldBody C f).countP (isUnlockStep C) = 1 := by
  obtain ⟨pre, callee_outer, value_outer, post, h_eq, _, _,
          _, h_pre_no_sstore, h_post_no_sstore⟩ := h_oz
  unfold unfoldBody
  rw [h_eq]
  simp only [List.map_cons, List.map_append, liftStep,
             List.countP_cons, List.countP_append]
  rw [countP_isUnlockStep_map_liftStep_NoSStore C pre h_pre_no_sstore,
      countP_isUnlockStep_map_liftStep_NoSStore C post h_post_no_sstore]
  have h_lock_false :
      isUnlockStep C (EVMStep.sstore C.address C.guardSlot C.lockedValue) = false := by
    simp only [isUnlockStep, decide_eq_false_iff_not]
    intro h_eq_step
    injection h_eq_step with _ _ h_val
    exact h_distinct h_val
  have h_call_false :
      isUnlockStep C (EVMStep.call C.address callee_outer value_outer) = false := by
    simp [isUnlockStep]
  have h_unlock_true :
      isUnlockStep C (EVMStep.sstore C.address C.guardSlot C.unlockedValue) = true := by
    simp [isUnlockStep]
  have h_ret_false : isUnlockStep C (EVMStep.ret true) = false := by simp [isUnlockStep]
  rw [h_lock_false, h_call_false, h_unlock_true, h_ret_false]
  simp

/-! ## Position-list helpers -/

/-- The list of trace positions captured by `cFrameProjection`. -/
def cFrameProjPos
    (C : Contract) (tr : ExecutionTrace) (start finish : Nat) : List Nat :=
  (List.range' start (finish - start)).filter
    (fun p => decide (currentFrameAt tr p = some C.address))

/-- `cFrameProjection` is the filterMap of `tr[]?` over `cFrameProjPos`. -/
theorem cFrameProjection_eq_filterMap_pos
    (C : Contract) (tr : ExecutionTrace) (start finish : Nat) :
    cFrameProjection C tr start finish =
      (cFrameProjPos C tr start finish).filterMap (fun p => tr[p]?) := rfl

/-- Each position in `cFrameProjPos` lies in `[start, finish)` and has
    `currentFrameAt = some C.address`. -/
theorem cFrameProjPos_mem_range
    (C : Contract) (tr : ExecutionTrace) (start finish p : Nat)
    (h : p ∈ cFrameProjPos C tr start finish) :
    start ≤ p ∧ p < finish ∧ currentFrameAt tr p = some C.address := by
  unfold cFrameProjPos at h
  rw [List.mem_filter] at h
  obtain ⟨h_range, h_dec⟩ := h
  rw [List.mem_range'] at h_range
  obtain ⟨_, _, _⟩ := h_range
  refine ⟨?_, ?_, of_decide_eq_true h_dec⟩ <;> omega

/-- `cFrameProjPos` is strictly monotonic. Inherited from `List.range'`'s
    `Pairwise (· < ·)` via `List.Pairwise.filter`. -/
theorem cFrameProjPos_pairwise_lt
    (C : Contract) (tr : ExecutionTrace) (start finish : Nat) :
    (cFrameProjPos C tr start finish).Pairwise (· < ·) := by
  unfold cFrameProjPos
  exact List.Pairwise.filter _ List.pairwise_lt_range'

/-- Generic helper: filterMap preserves length when every element maps to
    `some`. Stated for the specific `(fun p => tr[p]?)` case where every
    `p < tr.length`. -/
private theorem filterMap_tr_get?_via_pos_aux
    (tr : ExecutionTrace) (L : List Nat) (h_all_lt : ∀ p ∈ L, p < tr.length)
    (i : Nat) (s : EVMStep)
    (h : (L.filterMap (fun p => tr[p]?))[i]? = some s) :
    ∃ p, L[i]? = some p ∧ tr[p]? = some s := by
  induction L generalizing i with
  | nil => simp at h
  | cons hd tl ih =>
    have h_hd_lt : hd < tr.length := h_all_lt hd List.mem_cons_self
    have h_hd_some : tr[hd]? = some (tr[hd]'h_hd_lt) := List.getElem?_eq_getElem h_hd_lt
    rw [List.filterMap_cons] at h
    rw [h_hd_some] at h
    cases i with
    | zero =>
      simp at h
      refine ⟨hd, rfl, ?_⟩
      rw [h_hd_some, h]
    | succ i' =>
      simp at h
      have h_tl_lt : ∀ p ∈ tl, p < tr.length := fun p hp =>
        h_all_lt p (List.mem_cons.mpr (Or.inr hp))
      -- IH (after `induction L generalizing i`) expects: h_all_lt then i then h.
      -- (s is fixed from the outer scope.)
      obtain ⟨p, h_p_pos, h_p_tr⟩ := ih h_tl_lt i' h
      refine ⟨p, ?_, h_p_tr⟩
      simp [h_p_pos]

/-- For `finish ≤ tr.length`, the projection's i-th element corresponds
    to `tr[]?` at the i-th trace position in `cFrameProjPos`. -/
theorem cFrameProjection_get?_via_pos
    (C : Contract) (tr : ExecutionTrace) (start finish : Nat)
    (h_finish : finish ≤ tr.length)
    (i : Nat) (s : EVMStep)
    (h : (cFrameProjection C tr start finish)[i]? = some s) :
    ∃ p, (cFrameProjPos C tr start finish)[i]? = some p ∧ tr[p]? = some s := by
  rw [cFrameProjection_eq_filterMap_pos] at h
  apply filterMap_tr_get?_via_pos_aux tr _ ?_ i s h
  intro p hp
  obtain ⟨_, h_lt_finish, _⟩ := cFrameProjPos_mem_range C tr start finish p hp
  omega

/-- Strict monotonicity of trace positions across two projection
    indices, given `finish ≤ tr.length`. -/
theorem cFrameProjection_pos_lt_of_index_lt
    (C : Contract) (tr : ExecutionTrace) (start finish : Nat)
    (h_finish : finish ≤ tr.length)
    (i j : Nat) (h_lt : i < j)
    (s_i s_j : EVMStep)
    (h_i : (cFrameProjection C tr start finish)[i]? = some s_i)
    (h_j : (cFrameProjection C tr start finish)[j]? = some s_j) :
    ∃ p_i p_j,
      (cFrameProjPos C tr start finish)[i]? = some p_i ∧
      (cFrameProjPos C tr start finish)[j]? = some p_j ∧
      p_i < p_j ∧ tr[p_i]? = some s_i ∧ tr[p_j]? = some s_j := by
  obtain ⟨p_i, h_pi, h_tri⟩ := cFrameProjection_get?_via_pos C tr start finish h_finish i s_i h_i
  obtain ⟨p_j, h_pj, h_trj⟩ := cFrameProjection_get?_via_pos C tr start finish h_finish j s_j h_j
  refine ⟨p_i, p_j, h_pi, h_pj, ?_, h_tri, h_trj⟩
  have h_pw := cFrameProjPos_pairwise_lt C tr start finish
  have h_i_lt_len : i < (cFrameProjPos C tr start finish).length := by
    rw [List.getElem?_eq_some_iff] at h_pi
    exact h_pi.1
  have h_j_lt_len : j < (cFrameProjPos C tr start finish).length := by
    rw [List.getElem?_eq_some_iff] at h_pj
    exact h_pj.1
  -- positions[i] < positions[j] when i < j: from Pairwise via List.pairwise_iff_getElem.
  have h_get_i : (cFrameProjPos C tr start finish)[i]'h_i_lt_len = p_i := by
    have := h_pi
    rw [List.getElem?_eq_some_iff] at this
    obtain ⟨_, h_eq⟩ := this
    exact h_eq
  have h_get_j : (cFrameProjPos C tr start finish)[j]'h_j_lt_len = p_j := by
    have := h_pj
    rw [List.getElem?_eq_some_iff] at this
    obtain ⟨_, h_eq⟩ := this
    exact h_eq
  rw [← h_get_i, ← h_get_j]
  exact List.pairwise_iff_getElem.mp h_pw i j h_i_lt_len h_j_lt_len h_lt

/-! ## Body-index → projection-index identifications -/

/-- `unfoldBody C f` (with the OZ decomposition) at body-index `pre.length + 1`
    is the body's external CALL. -/
private theorem unfoldBody_get?_call
    (C : Contract) (pre : List FunctionBody.Step) (callee_outer : Address)
    (value_outer : Word256) (post : List FunctionBody.Step) (f : FunctionBody)
    (h_eq : f =
      (FunctionBody.Step.sstore C.guardSlot C.lockedValue) ::
        (pre ++
          (FunctionBody.Step.call callee_outer value_outer) ::
          (post ++
            [FunctionBody.Step.sstore C.guardSlot C.unlockedValue,
             FunctionBody.Step.ret true]))) :
    (unfoldBody C f)[pre.length + 1]? =
      some (EVMStep.call C.address callee_outer value_outer) := by
  unfold unfoldBody
  rw [h_eq]
  simp only [List.map_cons, List.map_append, liftStep, List.getElem?_cons_succ]
  rw [List.getElem?_append_right (by simp)]
  simp [List.length_map]

/-- `unfoldBody C f` (with the OZ decomposition) at body-index
    `pre.length + post.length + 2` is the unlock SSTORE. -/
private theorem unfoldBody_get?_unlock
    (C : Contract) (pre : List FunctionBody.Step) (callee_outer : Address)
    (value_outer : Word256) (post : List FunctionBody.Step) (f : FunctionBody)
    (h_eq : f =
      (FunctionBody.Step.sstore C.guardSlot C.lockedValue) ::
        (pre ++
          (FunctionBody.Step.call callee_outer value_outer) ::
          (post ++
            [FunctionBody.Step.sstore C.guardSlot C.unlockedValue,
             FunctionBody.Step.ret true]))) :
    (unfoldBody C f)[pre.length + post.length + 2]? =
      some (EVMStep.sstore C.address C.guardSlot C.unlockedValue) := by
  unfold unfoldBody
  rw [h_eq]
  simp only [List.map_cons, List.map_append, liftStep, List.getElem?_cons_succ]
  -- (pre.map ++ CALL :: post.map ++ [unlock, ret])[pre.length+post.length+1]?
  rw [List.getElem?_append_right (by simp [List.length_map]; omega)]
  simp only [List.length_map]
  -- (CALL :: post.map ++ [unlock, ret])[post.length+1]?
  have h_idx : pre.length + post.length + 1 - pre.length = post.length + 1 := by omega
  rw [h_idx]
  simp only [List.getElem?_cons_succ]
  -- (post.map ++ [unlock, ret])[post.length]? = some unlock
  rw [List.getElem?_append_right (by simp [List.length_map])]
  simp [List.length_map]

/-! ## Central theorem -/

/-- **Central theorem (Family C).** Given `MatchesBody C f tr q finish`
    for an OZ-guarded body `f`, extract trace positions `p_call` and
    `p_unlock` with the structural conjuncts. -/
theorem matchesBody_oz_extracts_positions
    (C : Contract)
    (tr : ExecutionTrace) (q finish : Nat)
    (caller : Address) (value : Word256)
    (h_entry : tr[q]? = some (EVMStep.call caller C.address value))
    (f : FunctionBody) (h_oz : IsOZGuardedFunction C f)
    (h_match : MatchesBody C f tr q finish) :
    ∃ p_call p_unlock : Nat,
      q + 1 < p_call ∧ p_call < p_unlock ∧ p_unlock < finish ∧
      currentFrameAt tr (q + 1) = some C.address ∧
      currentFrameAt tr p_call = some C.address ∧
      currentFrameAt tr p_unlock = some C.address ∧
      tr[q + 1]? = some (EVMStep.sstore C.address C.guardSlot C.lockedValue) ∧
      (∃ callee_outer value_outer, callee_outer ≠ C.address ∧
        tr[p_call]? = some (EVMStep.call C.address callee_outer value_outer)) ∧
      tr[p_unlock]? = some (EVMStep.sstore C.address C.guardSlot C.unlockedValue) := by
  -- Compute h_tr_q1 BEFORE destructuring h_oz (which obtain consumes).
  have h_tr_q1 : tr[q + 1]? = some (EVMStep.sstore C.address C.guardSlot C.lockedValue) :=
    matchesBody_implies_tr_kplus1_eq_lock C tr q finish caller value h_entry f h_oz h_match
  obtain ⟨h_q_lt_finish, h_finish_le_tr, _, _, h_proj⟩ := h_match
  obtain ⟨pre, callee_outer, value_outer, post, h_eq, h_callee_ne, _, _, _, _⟩ := h_oz
  have h_cf_q1 : currentFrameAt tr (q + 1) = some C.address :=
    currentFrameAt_after_call tr q caller C.address value h_entry
  have h_unf_call : (unfoldBody C f)[pre.length + 1]? =
      some (EVMStep.call C.address callee_outer value_outer) :=
    unfoldBody_get?_call C pre callee_outer value_outer post f h_eq
  have h_unf_unlock : (unfoldBody C f)[pre.length + post.length + 2]? =
      some (EVMStep.sstore C.address C.guardSlot C.unlockedValue) :=
    unfoldBody_get?_unlock C pre callee_outer value_outer post f h_eq
  have h_proj_call : (cFrameProjection C tr (q + 1) finish)[pre.length + 1]? =
      some (EVMStep.call C.address callee_outer value_outer) := by
    rw [h_proj]; exact h_unf_call
  have h_proj_unlock : (cFrameProjection C tr (q + 1) finish)[pre.length + post.length + 2]? =
      some (EVMStep.sstore C.address C.guardSlot C.unlockedValue) := by
    rw [h_proj]; exact h_unf_unlock
  have h_idx_lt : pre.length + 1 < pre.length + post.length + 2 := by omega
  obtain ⟨p_call, p_unlock, h_pcall_pos, h_punlock_pos, h_pcall_lt_punlock,
          h_tr_pcall, h_tr_punlock⟩ :=
    cFrameProjection_pos_lt_of_index_lt C tr (q + 1) finish h_finish_le_tr
      (pre.length + 1) (pre.length + post.length + 2) h_idx_lt
      _ _ h_proj_call h_proj_unlock
  have h_pcall_mem : p_call ∈ cFrameProjPos C tr (q + 1) finish :=
    List.mem_of_getElem? h_pcall_pos
  have h_punlock_mem : p_unlock ∈ cFrameProjPos C tr (q + 1) finish :=
    List.mem_of_getElem? h_punlock_pos
  obtain ⟨h_pcall_ge, _, h_pcall_cf⟩ :=
    cFrameProjPos_mem_range C tr (q + 1) finish p_call h_pcall_mem
  obtain ⟨_, h_punlock_lt_finish, h_punlock_cf⟩ :=
    cFrameProjPos_mem_range C tr (q + 1) finish p_unlock h_punlock_mem
  -- p_call ≠ q + 1 (CALL ≠ lock at q+1).
  have h_pcall_ne_q1 : p_call ≠ q + 1 := by
    intro h_eq_pos
    rw [h_eq_pos, h_tr_q1] at h_tr_pcall
    cases h_tr_pcall
  have h_pcall_gt_q1 : q + 1 < p_call := by
    rcases lt_or_eq_of_le h_pcall_ge with h | h
    · exact h
    · exfalso; exact h_pcall_ne_q1 h.symm
  refine ⟨p_call, p_unlock, h_pcall_gt_q1, h_pcall_lt_punlock, h_punlock_lt_finish,
          h_cf_q1, h_pcall_cf, h_punlock_cf, h_tr_q1, ?_, h_tr_punlock⟩
  exact ⟨callee_outer, value_outer, h_callee_ne, h_tr_pcall⟩

/-! ## Uniqueness corollaries -/

/-- **Uniqueness of CALL position (Family C).** Any C-issued CALL inside
    the C-frame must be at the body's CALL position `p_call`. -/
theorem c_call_in_C_frame_eq_p_call
    (C : Contract)
    (tr : ExecutionTrace) (q finish : Nat)
    (caller : Address) (value : Word256)
    (h_entry : tr[q]? = some (EVMStep.call caller C.address value))
    (f : FunctionBody) (h_oz : IsOZGuardedFunction C f)
    (h_match : MatchesBody C f tr q finish)
    (k : Nat) (h_qk : q + 1 ≤ k) (h_kf : k < finish)
    (h_cf_k : currentFrameAt tr k = some C.address)
    (callee : Address) (value' : Word256)
    (h_call_k : tr[k]? = some (EVMStep.call C.address callee value')) :
    ∃ p_call p_unlock : Nat,
      k = p_call ∧
      q + 1 < p_call ∧ p_call < p_unlock ∧ p_unlock < finish ∧
      currentFrameAt tr (q + 1) = some C.address ∧
      currentFrameAt tr p_unlock = some C.address ∧
      tr[q + 1]? = some (EVMStep.sstore C.address C.guardSlot C.lockedValue) ∧
      tr[p_unlock]? = some (EVMStep.sstore C.address C.guardSlot C.unlockedValue) := by
  obtain ⟨p_call, p_unlock, h_pc_gt, h_pc_lt_pu, h_pu_lt_f,
          h_cf_q1, h_cf_pc, h_cf_pu, h_tr_q1, ⟨_, _, _, h_tr_pc⟩, h_tr_pu⟩ :=
    matchesBody_oz_extracts_positions C tr q finish caller value h_entry f h_oz h_match
  by_cases h_k_eq_pc : k = p_call
  · subst h_k_eq_pc
    exact ⟨k, p_unlock, rfl, h_pc_gt, h_pc_lt_pu, h_pu_lt_f, h_cf_q1, h_cf_pu,
           h_tr_q1, h_tr_pu⟩
  · -- k ≠ p_call. Two distinct CALL positions in the projection.
    exfalso
    obtain ⟨_, _, _, _, h_proj⟩ := h_match
    have h_count_eq : (unfoldBody C f).countP isCallStep = 1 :=
      unfoldBody_countP_isCallStep_eq_one C f h_oz
    rcases lt_or_gt_of_ne h_k_eq_pc with h_k_lt_pc | h_pc_lt_k
    · have h_count := cFrameProjection_countP_ge_two C tr (q + 1) finish isCallStep
        k p_call h_k_lt_pc h_qk (h_pc_lt_pu.trans h_pu_lt_f)
        h_cf_k h_cf_pc _ _ h_call_k h_tr_pc (by simp [isCallStep]) (by simp [isCallStep])
      rw [h_proj] at h_count
      omega
    · have h_count := cFrameProjection_countP_ge_two C tr (q + 1) finish isCallStep
        p_call k h_pc_lt_k (by omega) h_kf
        h_cf_pc h_cf_k _ _ h_tr_pc h_call_k (by simp [isCallStep]) (by simp [isCallStep])
      rw [h_proj] at h_count
      omega

/-- **Uniqueness of lock position (Family C).** Any SSTORE on
    `(C.address, C.guardSlot)` writing `C.lockedValue` inside the
    C-frame is at position `q + 1`. -/
theorem lock_position_unique_in_C_frame
    (C : Contract) (h_distinct : C.lockedValue ≠ C.unlockedValue)
    (tr : ExecutionTrace) (q finish : Nat)
    (caller : Address) (value : Word256)
    (h_entry : tr[q]? = some (EVMStep.call caller C.address value))
    (f : FunctionBody) (h_oz : IsOZGuardedFunction C f)
    (h_match : MatchesBody C f tr q finish)
    (p : Nat) (h_qp : q + 1 ≤ p) (h_pf : p < finish)
    (h_cf_p : currentFrameAt tr p = some C.address)
    (h_sstore : tr[p]? = some (EVMStep.sstore C.address C.guardSlot C.lockedValue)) :
    p = q + 1 := by
  by_contra h_ne
  have h_tr_q1 : tr[q + 1]? = some (EVMStep.sstore C.address C.guardSlot C.lockedValue) :=
    matchesBody_implies_tr_kplus1_eq_lock C tr q finish caller value h_entry f h_oz h_match
  obtain ⟨_, _, _, _, h_proj⟩ := h_match
  have h_cf_q1 : currentFrameAt tr (q + 1) = some C.address :=
    currentFrameAt_after_call tr q caller C.address value h_entry
  have h_count_eq : (unfoldBody C f).countP (isLockStep C) = 1 :=
    unfoldBody_countP_isLockStep_eq_one C f h_oz h_distinct
  -- p ≠ q + 1 means q + 1 < p (since q + 1 ≤ p).
  have h_p_gt_q1 : q + 1 < p := lt_of_le_of_ne h_qp (Ne.symm h_ne)
  have h_count := cFrameProjection_countP_ge_two C tr (q + 1) finish (isLockStep C)
    (q + 1) p h_p_gt_q1 (le_refl _) h_pf
    h_cf_q1 h_cf_p _ _ h_tr_q1 h_sstore (by simp [isLockStep]) (by simp [isLockStep])
  rw [h_proj] at h_count
  omega

/-- **Uniqueness of unlock position (Family C).** Any SSTORE on
    `(C.address, C.guardSlot)` writing `C.unlockedValue` inside the
    C-frame is at position `p_unlock`. -/
theorem unlock_position_unique_in_C_frame
    (C : Contract) (h_distinct : C.lockedValue ≠ C.unlockedValue)
    (tr : ExecutionTrace) (q finish : Nat)
    (caller : Address) (value : Word256)
    (h_entry : tr[q]? = some (EVMStep.call caller C.address value))
    (f : FunctionBody) (h_oz : IsOZGuardedFunction C f)
    (h_match : MatchesBody C f tr q finish)
    (p p_unlock : Nat) (h_qp : q + 1 ≤ p) (h_pf : p < finish)
    (h_cf_p : currentFrameAt tr p = some C.address)
    (h_sstore : tr[p]? = some (EVMStep.sstore C.address C.guardSlot C.unlockedValue))
    (h_pu_q1 : q + 1 < p_unlock) (h_pu_f : p_unlock < finish)
    (h_cf_pu : currentFrameAt tr p_unlock = some C.address)
    (h_tr_pu : tr[p_unlock]? = some (EVMStep.sstore C.address C.guardSlot C.unlockedValue)) :
    p = p_unlock := by
  by_contra h_ne
  obtain ⟨_, _, _, _, h_proj⟩ := h_match
  have h_count_eq : (unfoldBody C f).countP (isUnlockStep C) = 1 :=
    unfoldBody_countP_isUnlockStep_eq_one C f h_oz h_distinct
  rcases lt_or_gt_of_ne h_ne with h_p_lt | h_p_gt
  · have h_count := cFrameProjection_countP_ge_two C tr (q + 1) finish (isUnlockStep C)
      p p_unlock h_p_lt h_qp h_pu_f
      h_cf_p h_cf_pu _ _ h_sstore h_tr_pu (by simp [isUnlockStep]) (by simp [isUnlockStep])
    rw [h_proj] at h_count
    omega
  · have h_count := cFrameProjection_countP_ge_two C tr (q + 1) finish (isUnlockStep C)
      p_unlock p h_p_gt (by omega) h_pf
      h_cf_pu h_cf_p _ _ h_tr_pu h_sstore (by simp [isUnlockStep]) (by simp [isUnlockStep])
    rw [h_proj] at h_count
    omega

/-- **Guard SSTORE value characterization (Family C).** Any SSTORE on
    `(C.address, C.guardSlot)` inside the C-frame writes either
    `C.lockedValue` or `C.unlockedValue`. -/
theorem guard_sstore_value_in_C_frame
    (C : Contract)
    (tr : ExecutionTrace) (q finish : Nat)
    (f : FunctionBody) (h_oz : IsOZGuardedFunction C f)
    (h_match : MatchesBody C f tr q finish)
    (p : Nat) (h_qp : q + 1 ≤ p) (h_pf : p < finish)
    (h_cf_p : currentFrameAt tr p = some C.address)
    (v : Word256) (h_sstore : tr[p]? = some (EVMStep.sstore C.address C.guardSlot v)) :
    v = C.lockedValue ∨ v = C.unlockedValue := by
  obtain ⟨_, _, _, _, h_proj⟩ := h_match
  -- The step at p is in cFrameProjection (= unfoldBody).
  have h_step_in_proj : EVMStep.sstore C.address C.guardSlot v ∈
      cFrameProjection C tr (q + 1) finish := by
    unfold cFrameProjection
    rw [List.mem_filterMap]
    refine ⟨p, ?_, h_sstore⟩
    rw [List.mem_filter, List.mem_range']
    refine ⟨⟨p - (q + 1), by omega, by omega⟩, by simp [h_cf_p]⟩
  rw [h_proj] at h_step_in_proj
  obtain ⟨pre, callee_outer, value_outer, post, h_eq, _, _,
          _, h_pre_no_sstore, h_post_no_sstore⟩ := h_oz
  -- Concrete unfoldBody form (do NOT split `(post ++ [unlock, ret]).map`).
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
  rw [h_unf] at h_step_in_proj
  rw [List.mem_cons, List.mem_append, List.mem_cons, List.mem_map, List.mem_map]
    at h_step_in_proj
  rcases h_step_in_proj with h_lock | h_pre | h_call | h_tail
  · -- s = lock SSTORE: extract v = lockedValue.
    injection h_lock with _ _ h_v
    left; exact h_v
  · -- ∃ x ∈ pre, liftStep x = s.
    obtain ⟨x, h_x_mem, h_x_eq⟩ := h_pre
    cases x with
    | sstore key val =>
      simp only [liftStep] at h_x_eq
      have h_pre_no := h_pre_no_sstore (FunctionBody.Step.sstore key val) h_x_mem
      injection h_x_eq with _ h_key _
      exact absurd ⟨val, by rw [h_key]⟩ h_pre_no
    | call _ _ => simp [liftStep] at h_x_eq
    | ret _ => simp [liftStep] at h_x_eq
    | revert => simp [liftStep] at h_x_eq
  · -- s = CALL: contradiction (sstore ≠ call).
    cases h_call
  · -- ∃ x ∈ (post ++ [unlock, ret]), liftStep x = s.
    obtain ⟨x, h_x_mem, h_x_eq⟩ := h_tail
    rw [List.mem_append] at h_x_mem
    rcases h_x_mem with h_x_post | h_x_tail2
    · cases x with
      | sstore key val =>
        simp only [liftStep] at h_x_eq
        have h_post_no := h_post_no_sstore (FunctionBody.Step.sstore key val) h_x_post
        injection h_x_eq with _ h_key _
        exact absurd ⟨val, by rw [h_key]⟩ h_post_no
      | call _ _ => simp [liftStep] at h_x_eq
      | ret _ => simp [liftStep] at h_x_eq
      | revert => simp [liftStep] at h_x_eq
    · -- x ∈ [unlock, ret].
      simp at h_x_tail2
      rcases h_x_tail2 with h_x_unlock | h_x_ret
      · rw [h_x_unlock] at h_x_eq
        simp only [liftStep] at h_x_eq
        injection h_x_eq with _ _ h_v
        right; exact h_v.symm
      · rw [h_x_ret] at h_x_eq
        simp [liftStep] at h_x_eq

/-! ## Phase 5 Session 19 — Sub-block γ-1: F2-B propagation lemmas

`_general` variants accepting `IsOZGuardedFunctionGeneral` (Session 15
sub-block β-1's generalized predicate). Co-exist with the original
Category 3 lemmas above; one-to-one structural correspondence.
Per an internal methodology note §1.4 four-way classification
+ PROCEED-2 path-(a) adjudication. Category 4 (W9: matchesBody_oz_extracts_positions,
c_call_in_C_frame_eq_p_call, unfoldBody_get?_call, unfoldBody_get?_unlock)
explicitly out of scope; Session 20 absorbs.
-/

/-- F2-B `_general` variant of `unfoldBody_countP_isUnlockStep_eq_one`.
    Body decomposition is 3-segment (`lock :: body ++ [unlock, ret]`)
    rather than the original 4-segment (`lock :: pre ++ call :: post ++ [unlock, ret]`);
    the proof simplifies accordingly — single `body` span feeds
    `countP_isUnlockStep_map_liftStep_NoSStore`, no central CALL discharge. -/
theorem unfoldBody_countP_isUnlockStep_eq_one_general
    (C : Contract) (f : FunctionBody) (h_oz : IsOZGuardedFunctionGeneral C f)
    (h_distinct : C.lockedValue ≠ C.unlockedValue) :
    (unfoldBody C f).countP (isUnlockStep C) = 1 := by
  obtain ⟨body, h_eq, h_no_sstore_body, _⟩ := h_oz
  unfold unfoldBody
  rw [h_eq]
  simp only [List.map_cons, List.map_append, liftStep,
             List.countP_cons, List.countP_append]
  rw [countP_isUnlockStep_map_liftStep_NoSStore C body h_no_sstore_body]
  have h_lock_false :
      isUnlockStep C (EVMStep.sstore C.address C.guardSlot C.lockedValue) = false := by
    simp only [isUnlockStep, decide_eq_false_iff_not]
    intro h_eq_step
    injection h_eq_step with _ _ h_val
    exact h_distinct h_val
  have h_unlock_true :
      isUnlockStep C (EVMStep.sstore C.address C.guardSlot C.unlockedValue) = true := by
    simp [isUnlockStep]
  have h_ret_false : isUnlockStep C (EVMStep.ret true) = false := by simp [isUnlockStep]
  rw [h_lock_false, h_unlock_true, h_ret_false]
  simp

/-- F2-B path-(a) BodyShape-local helper. Counterpart in CountHelpers
    (`unfoldBody_countP_isLockStep_eq_one`, line 295) takes
    `IsOZGuardedFunction` and is out of scope for γ-1 modification.
    This helper proves the same conclusion against
    `IsOZGuardedFunctionGeneral` directly via the 3-segment body
    decomposition. Captured as deferred-housekeeping architectural
    debt: future cleanup should consolidate both predicate variants
    into a shared module. -/
theorem unfoldBody_countP_isLockStep_eq_one_general
    (C : Contract) (f : FunctionBody) (h_oz : IsOZGuardedFunctionGeneral C f)
    (h_distinct : C.lockedValue ≠ C.unlockedValue) :
    (unfoldBody C f).countP (isLockStep C) = 1 := by
  obtain ⟨body, h_eq, h_no_sstore_body, _⟩ := h_oz
  unfold unfoldBody
  rw [h_eq]
  simp only [List.map_cons, List.map_append, liftStep,
             List.countP_cons, List.countP_append]
  rw [countP_isLockStep_map_liftStep_NoSStore C body h_no_sstore_body]
  have h_lock_true :
      isLockStep C (EVMStep.sstore C.address C.guardSlot C.lockedValue) = true := by
    simp [isLockStep]
  have h_unlock_false :
      isLockStep C (EVMStep.sstore C.address C.guardSlot C.unlockedValue) = false := by
    simp only [isLockStep, decide_eq_false_iff_not]
    intro h_eq_step
    injection h_eq_step with _ _ h_val
    exact h_distinct h_val.symm
  have h_ret_false : isLockStep C (EVMStep.ret true) = false := by simp [isLockStep]
  rw [h_lock_true, h_unlock_false, h_ret_false]
  simp

/-- F2-B path-(α) BodyShape-local helper. Counterpart in
    `Executes.lean` (`matchesBody_implies_tr_kplus1_eq_lock`, line 228)
    takes `IsOZGuardedFunction` and destructures the original's
    4-segment body shape. This helper proves the same conclusion
    against `IsOZGuardedFunctionGeneral`'s 3-segment body decomposition.
    Captured as deferred-housekeeping architectural debt alongside
    `unfoldBody_countP_isLockStep_eq_one_general`. -/
theorem matchesBody_implies_tr_kplus1_eq_lock_general
    (C : Contract) (tr : ExecutionTrace) (k finish : Nat)
    (caller : Address) (value : Word256)
    (h_call : tr[k]? = some (EVMStep.call caller C.address value))
    (f : FunctionBody) (h_oz : IsOZGuardedFunctionGeneral C f)
    (h_match : MatchesBody C f tr k finish) :
    tr[k+1]? = some (EVMStep.sstore C.address C.guardSlot C.lockedValue) := by
  obtain ⟨_, h_fle, _, _, h_proj⟩ := h_match
  obtain ⟨body, h_eq_body, _, _⟩ := h_oz
  have h_cf : currentFrameAt tr (k + 1) = some C.address :=
    currentFrameAt_after_call tr k caller C.address value h_call
  have h_unf : unfoldBody C f =
      EVMStep.sstore C.address C.guardSlot C.lockedValue ::
        (body.map (liftStep C) ++
          [EVMStep.sstore C.address C.guardSlot C.unlockedValue,
           EVMStep.ret true]) := by
    unfold unfoldBody; rw [h_eq_body]
    simp [List.map_cons, List.map_append, liftStep]
  have h_unf_head : (unfoldBody C f).head? =
      some (EVMStep.sstore C.address C.guardSlot C.lockedValue) := by
    rw [h_unf]; rfl
  have h_unf_len_ge : (unfoldBody C f).length ≥ 3 := by
    rw [h_unf]; simp [List.length_cons, List.length_append]
  have h_proj_len_eq : (cFrameProjection C tr (k+1) finish).length = (unfoldBody C f).length :=
    by rw [h_proj]
  have h_range_ge : finish - (k+1) ≥ 3 := by
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

/-- F2-B `_general` variant of survey §1.2.O `lock_position_unique_in_C_frame`.
    Proof structure mirrors original (line 390): by_contra, derive
    h_tr_q1 via the path-(α) helper, count two distinct lock-positions,
    contradict count = 1 from the path-(a) helper. -/
theorem lock_position_unique_in_C_frame_general
    (C : Contract) (h_distinct : C.lockedValue ≠ C.unlockedValue)
    (tr : ExecutionTrace) (q finish : Nat)
    (caller : Address) (value : Word256)
    (h_entry : tr[q]? = some (EVMStep.call caller C.address value))
    (f : FunctionBody) (h_oz : IsOZGuardedFunctionGeneral C f)
    (h_match : MatchesBody C f tr q finish)
    (p : Nat) (h_qp : q + 1 ≤ p) (h_pf : p < finish)
    (h_cf_p : currentFrameAt tr p = some C.address)
    (h_sstore : tr[p]? = some (EVMStep.sstore C.address C.guardSlot C.lockedValue)) :
    p = q + 1 := by
  by_contra h_ne
  have h_tr_q1 : tr[q + 1]? = some (EVMStep.sstore C.address C.guardSlot C.lockedValue) :=
    matchesBody_implies_tr_kplus1_eq_lock_general C tr q finish caller value h_entry f h_oz h_match
  obtain ⟨_, _, _, _, h_proj⟩ := h_match
  have h_cf_q1 : currentFrameAt tr (q + 1) = some C.address :=
    currentFrameAt_after_call tr q caller C.address value h_entry
  have h_count_eq : (unfoldBody C f).countP (isLockStep C) = 1 :=
    unfoldBody_countP_isLockStep_eq_one_general C f h_oz h_distinct
  have h_p_gt_q1 : q + 1 < p := lt_of_le_of_ne h_qp (Ne.symm h_ne)
  have h_count := cFrameProjection_countP_ge_two C tr (q + 1) finish (isLockStep C)
    (q + 1) p h_p_gt_q1 (le_refl _) h_pf
    h_cf_q1 h_cf_p _ _ h_tr_q1 h_sstore (by simp [isLockStep]) (by simp [isLockStep])
  rw [h_proj] at h_count
  omega

/-- F2-B `_general` variant of survey §1.2.P `unlock_position_unique_in_C_frame`.
    Proof structure mirrors original (line 420): by_contra; count = 1
    via Unit 1's `unfoldBody_countP_isUnlockStep_eq_one_general`;
    `lt_or_gt_of_ne` to handle both orderings; contradict via
    `cFrameProjection_countP_ge_two` (Layer-4, predicate-agnostic).

    Vestigial `h_entry`/`caller`/`value` parameters from the original
    (genuinely unused; source of the BodyShape.lean:424:5 baseline
    warning) are omitted — the `_general` variant has a cleaner
    signature with the unused-variable warning eliminated structurally
    rather than suppressed. -/
theorem unlock_position_unique_in_C_frame_general
    (C : Contract) (h_distinct : C.lockedValue ≠ C.unlockedValue)
    (tr : ExecutionTrace) (q finish : Nat)
    (f : FunctionBody) (h_oz : IsOZGuardedFunctionGeneral C f)
    (h_match : MatchesBody C f tr q finish)
    (p p_unlock : Nat) (h_qp : q + 1 ≤ p) (h_pf : p < finish)
    (h_cf_p : currentFrameAt tr p = some C.address)
    (h_sstore : tr[p]? = some (EVMStep.sstore C.address C.guardSlot C.unlockedValue))
    (h_pu_q1 : q + 1 < p_unlock) (h_pu_f : p_unlock < finish)
    (h_cf_pu : currentFrameAt tr p_unlock = some C.address)
    (h_tr_pu : tr[p_unlock]? = some (EVMStep.sstore C.address C.guardSlot C.unlockedValue)) :
    p = p_unlock := by
  by_contra h_ne
  obtain ⟨_, _, _, _, h_proj⟩ := h_match
  have h_count_eq : (unfoldBody C f).countP (isUnlockStep C) = 1 :=
    unfoldBody_countP_isUnlockStep_eq_one_general C f h_oz h_distinct
  rcases lt_or_gt_of_ne h_ne with h_p_lt | h_p_gt
  · have h_count := cFrameProjection_countP_ge_two C tr (q + 1) finish (isUnlockStep C)
      p p_unlock h_p_lt h_qp h_pu_f
      h_cf_p h_cf_pu _ _ h_sstore h_tr_pu (by simp [isUnlockStep]) (by simp [isUnlockStep])
    rw [h_proj] at h_count
    omega
  · have h_count := cFrameProjection_countP_ge_two C tr (q + 1) finish (isUnlockStep C)
      p_unlock p h_p_gt (by omega) h_pf
      h_cf_pu h_cf_p _ _ h_tr_pu h_sstore (by simp [isUnlockStep]) (by simp [isUnlockStep])
    rw [h_proj] at h_count
    omega

/-- F2-B `_general` variant of survey §1.2.Q `guard_sstore_value_in_C_frame`.
    Proof structure simplified per survey §1.2.Q's projection: 3-segment
    body decomposition (`lock :: body ++ [unlock, ret]`) rather than the
    original 4-segment (`lock :: pre ++ call :: post ++ [unlock, ret]`).
    The central CALL case-discharge of the original is absorbed into the
    body case (where CALL membership is handled by `liftStep`-simp like
    any other non-SSTORE body step). Net: one fewer rcases segment. -/
theorem guard_sstore_value_in_C_frame_general
    (C : Contract)
    (tr : ExecutionTrace) (q finish : Nat)
    (f : FunctionBody) (h_oz : IsOZGuardedFunctionGeneral C f)
    (h_match : MatchesBody C f tr q finish)
    (p : Nat) (h_qp : q + 1 ≤ p) (h_pf : p < finish)
    (h_cf_p : currentFrameAt tr p = some C.address)
    (v : Word256) (h_sstore : tr[p]? = some (EVMStep.sstore C.address C.guardSlot v)) :
    v = C.lockedValue ∨ v = C.unlockedValue := by
  obtain ⟨_, _, _, _, h_proj⟩ := h_match
  have h_step_in_proj : EVMStep.sstore C.address C.guardSlot v ∈
      cFrameProjection C tr (q + 1) finish := by
    unfold cFrameProjection
    rw [List.mem_filterMap]
    refine ⟨p, ?_, h_sstore⟩
    rw [List.mem_filter, List.mem_range']
    refine ⟨⟨p - (q + 1), by omega, by omega⟩, by simp [h_cf_p]⟩
  rw [h_proj] at h_step_in_proj
  obtain ⟨body, h_eq, h_no_sstore_body, _⟩ := h_oz
  have h_unf : unfoldBody C f =
      EVMStep.sstore C.address C.guardSlot C.lockedValue ::
        (body.map (liftStep C) ++
          [EVMStep.sstore C.address C.guardSlot C.unlockedValue,
           EVMStep.ret true]) := by
    unfold unfoldBody
    rw [h_eq]
    simp [List.map_cons, List.map_append, liftStep]
  rw [h_unf] at h_step_in_proj
  rw [List.mem_cons, List.mem_append, List.mem_map] at h_step_in_proj
  rcases h_step_in_proj with h_lock | h_body | h_tail
  · -- step = lock-evm: extract v = lockedValue.
    injection h_lock with _ _ h_v
    left; exact h_v
  · -- ∃ x ∈ body, liftStep C x = sstore-step.
    obtain ⟨x, h_x_mem, h_x_eq⟩ := h_body
    cases x with
    | sstore key val =>
      simp only [liftStep] at h_x_eq
      have h_no := h_no_sstore_body (FunctionBody.Step.sstore key val) h_x_mem
      injection h_x_eq with _ h_key _
      exact absurd ⟨val, by rw [h_key]⟩ h_no
    | call _ _ => simp [liftStep] at h_x_eq
    | ret _ => simp [liftStep] at h_x_eq
    | revert => simp [liftStep] at h_x_eq
  · -- step ∈ [unlock-evm, ret-evm].
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h_tail
    rcases h_tail with h_unlock | h_ret
    · -- step = unlock-evm: extract v = unlockedValue.
      injection h_unlock with _ _ h_v
      right; exact h_v
    · -- step = ret-evm: contradiction (sstore ≠ ret).
      cases h_ret

/-! ## Phase 5 Session 21 — Sub-block γ-2: W9 closure under Option (iii)

Three new `_general` artifacts produced (M_general here in BodyShape.lean
plus L_general; Site 3_general lives in BodyTraceLift.lean). Original
M (`matchesBody_oz_extracts_positions`, line 279), K
(`unfoldBody_get?_call`, line 228), L (`unfoldBody_get?_unlock`,
line 248), N (`c_call_in_C_frame_eq_p_call`, line 345) all preserved
unchanged per Interpretation B (coexistence). No K_general or
N_general produced — both deleted-by-omission per Option (iii).

Per an internal reconnaissance note §1.4 specifications + Session 21
PROCEED authorization. -/

/-- F2-B M_general: scope-restricted body-shape extraction under
    `IsOZGuardedFunctionGeneral`. Drops CALL-extraction promise per
    Option (iii); preserves lock/unlock-only existential.

    Coexists with original `matchesBody_oz_extracts_positions`
    (which retains CALL extraction for the single-CALL setting). -/
theorem matchesBody_oz_extracts_positions_general
    (C : Contract)
    (tr : ExecutionTrace) (q finish : Nat)
    (caller : Address) (value : Word256)
    (h_entry : tr[q]? = some (EVMStep.call caller C.address value))
    (f : FunctionBody) (h_oz : IsOZGuardedFunctionGeneral C f)
    (h_match : MatchesBody C f tr q finish) :
    ∃ p_unlock : Nat,
      q + 1 < p_unlock ∧ p_unlock < finish ∧
      currentFrameAt tr (q + 1) = some C.address ∧
      currentFrameAt tr p_unlock = some C.address ∧
      tr[q + 1]? = some (EVMStep.sstore C.address C.guardSlot C.lockedValue) ∧
      tr[p_unlock]? = some (EVMStep.sstore C.address C.guardSlot C.unlockedValue) := by
  have h_tr_q1 : tr[q + 1]? = some (EVMStep.sstore C.address C.guardSlot C.lockedValue) :=
    matchesBody_implies_tr_kplus1_eq_lock_general
      C tr q finish caller value h_entry f h_oz h_match
  obtain ⟨_, h_finish_le_tr, _, _, h_proj⟩ := h_match
  obtain ⟨body, h_eq, _, _⟩ := h_oz
  have h_cf_q1 : currentFrameAt tr (q + 1) = some C.address :=
    currentFrameAt_after_call tr q caller C.address value h_entry
  -- Inline: (unfoldBody C f)[body.length + 1]? = some unlock SSTORE.
  -- Structurally what L_general (defined below) exposes; inlined here
  -- to keep Unit 1 atomic-commit free of forward dependency on Unit 2.
  have h_unf_unlock : (unfoldBody C f)[body.length + 1]? =
      some (EVMStep.sstore C.address C.guardSlot C.unlockedValue) := by
    unfold unfoldBody
    rw [h_eq]
    simp only [List.map_cons, List.map_append, liftStep, List.getElem?_cons_succ]
    rw [List.getElem?_append_right (by simp [List.length_map])]
    simp [List.length_map]
  -- Inline: (unfoldBody C f)[0]? = some lock SSTORE.
  have h_unf_lock : (unfoldBody C f)[0]? =
      some (EVMStep.sstore C.address C.guardSlot C.lockedValue) := by
    unfold unfoldBody
    rw [h_eq]
    simp [List.map_cons, liftStep]
  have h_proj_lock : (cFrameProjection C tr (q + 1) finish)[0]? =
      some (EVMStep.sstore C.address C.guardSlot C.lockedValue) := by
    rw [h_proj]; exact h_unf_lock
  have h_proj_unlock : (cFrameProjection C tr (q + 1) finish)[body.length + 1]? =
      some (EVMStep.sstore C.address C.guardSlot C.unlockedValue) := by
    rw [h_proj]; exact h_unf_unlock
  have h_idx_lt : (0 : Nat) < body.length + 1 := Nat.zero_lt_succ _
  obtain ⟨p_lock, p_unlock, h_plock_pos, h_punlock_pos,
          h_plock_lt_punlock, _h_tr_plock, h_tr_punlock⟩ :=
    cFrameProjection_pos_lt_of_index_lt C tr (q + 1) finish h_finish_le_tr
      0 (body.length + 1) h_idx_lt _ _ h_proj_lock h_proj_unlock
  have h_punlock_mem := List.mem_of_getElem? h_punlock_pos
  obtain ⟨_, h_punlock_lt_finish, h_punlock_cf⟩ :=
    cFrameProjPos_mem_range C tr (q + 1) finish p_unlock h_punlock_mem
  have h_plock_mem := List.mem_of_getElem? h_plock_pos
  obtain ⟨h_plock_ge_q1, _, _⟩ :=
    cFrameProjPos_mem_range C tr (q + 1) finish p_lock h_plock_mem
  have h_q1_lt_punlock : q + 1 < p_unlock :=
    lt_of_le_of_lt h_plock_ge_q1 h_plock_lt_punlock
  exact ⟨p_unlock, h_q1_lt_punlock, h_punlock_lt_finish,
         h_cf_q1, h_punlock_cf, h_tr_q1, h_tr_punlock⟩

/-- F2-B L_general: body-indexed unlock-position helper under the
    `IsOZGuardedFunctionGeneral` 3-segment body decomposition.

    Replaces the original `unfoldBody_get?_unlock`'s
    `pre.length + post.length + 2` indexing (undefined under
    multi-CALL bodies) with `body.length + 1` indexing
    (well-defined for any body shape, including empty).

    Primary consumer: Site 3_general's Strategy B composition
    (`cFrameProjection_pos_lt_of_index_lt` at indices 0 and
    `body.length + 1`). M_general (above) inlines this fact rather
    than invoking L_general to preserve Unit 1 atomic-commit
    discipline; the inline duplication is captured architectural
    debt.

    Original `unfoldBody_get?_unlock` (line 248) preserved unchanged. -/
theorem unfoldBody_get?_unlock_general
    (C : Contract) (body : List FunctionBody.Step) (f : FunctionBody)
    (h_eq : f =
      (FunctionBody.Step.sstore C.guardSlot C.lockedValue) ::
        (body ++
          [FunctionBody.Step.sstore C.guardSlot C.unlockedValue,
           FunctionBody.Step.ret true])) :
    (unfoldBody C f)[body.length + 1]? =
      some (EVMStep.sstore C.address C.guardSlot C.unlockedValue) := by
  unfold unfoldBody
  rw [h_eq]
  simp only [List.map_cons, List.map_append, liftStep, List.getElem?_cons_succ]
  rw [List.getElem?_append_right (by simp [List.length_map])]
  simp [List.length_map]

end QanaryContracts
