/-
  QanaryContracts/Executes.lean

  Phase 5 Session 3 — F4 body-to-trace lift, Step 1 skeleton.
  Phase 5 Session 6 — L1 (`executes_C_no_nested_C_frame`) + Step 0 bridge.
  Phase 5 Session 7 γ — count-arithmetic helpers relocated to
    `QanaryContracts.Executes.CountHelpers`. This file now contains:
      • Step 0 bridge `cFrameProjection_get?_eq_some_iff` (kept adjacent
        to L1 per Session 7 γ directive Part 2.3).
      • `MatchesBody`, `executes_C`, sanity lemmas, MatchesBody tests.
      • L1's L1-specific helper `matchesBody_implies_tr_kplus1_eq_lock`
        (uses `MatchesBody`, hence stays here).
      • L1 itself: `executes_C_no_nested_C_frame`.

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
-/
import QanaryContracts.Executes.CountHelpers

namespace QanaryContracts

/-! ## Step 0 — projection-index → trace-position bridge

The L1 / L2 / L3 helpers (Phase 5 Session 6+) need to convert "the i-th
element of the C-frame projection equals s" into "there is a trace
position p in `[start, finish)` with `currentFrameAt tr p = some C.address`
and `tr[p]? = some s`". This is the only structural fact about
`cFrameProjection` we need to expose; everything else operates on
positions in `tr`.

Kept in `Executes.lean` (rather than `Executes/CountHelpers.lean`) per
the Phase 5 Session 7 γ directive: this helper is L1-specific scaffolding,
not a generic count-arithmetic lemma. -/

/-- **Step 0 helper.** If `(cFrameProjection C tr start finish)[i]? = some s`,
    then there exists a trace position `p` in `[start, finish)` at which
    `C` is the current frame and `tr[p]? = some s`. -/
theorem cFrameProjection_get?_eq_some_iff
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
theorem matchesBody_implies_tr_kplus1_eq_lock
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
