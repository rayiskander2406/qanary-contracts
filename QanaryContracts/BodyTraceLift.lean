/-
  QanaryContracts/BodyTraceLift.lean

  Phase 5 Session 4 Step 3 — F4 lift theorem skeleton.

  The F4 body-to-trace lift connects body-shape predicates (the
  level at which `OZGuardDiscipline`, `NoExternalCalls`, etc. live)
  to the trace-level RTO conjuncts. Once proved, the lift is the
  load-bearing connection between Layer 4 and Layers 3+5+6 of the
  paper:
    * **Layer 3** (Theorem 5*) becomes commercial-grade — `executes_C`
      traces of OZ-disciplined contracts compose through this lift
      into `ReachableTraceOf`, and through Theorem 5* into
      `ReentrancyFree`.
    * **Layer 5** (`oz_completeness_full`) becomes provable bottom-up
      against `ReentrancyFreeGeneral` (which quantifies over
      `executes_C` traces). F4 is what makes the antecedent
      meaningful — not vacuous as in the rejected Tier 1 plan.
    * **Layer 6** (Pendle / Compound) becomes honest — the
      certificate connects deployed Solidity bodies (via
      `executes_C`) to RTO and thence to Theorem 5* through this
      lift.

  Per Ray's confirmations (2026-04-28):
  * Q-VRVP2-1 — `IsOZGuardedFunction` strengthened with
    `NoSStoreOnGuardSlotInSteps` on pre/post; W4 wall closed in
    `OZSoundness.lean` (Phase 5 Session 4 Steps 1+2).
  * Q-VRVP2-2 — `lockedValue ≠ unlockedValue` is a separate
    hypothesis on the lift, matching Theorem 5*'s.
  * Q-VRVP2-3 — final lift signature confirmed (this file).
  * Q-VRVP2-4 — lift lives in this new file, not folded into
    `Reachability.lean` or `OZSoundness.lean`.

  Current contents (post Phase 5 Session 22, sub-block γ closed):

  * F4 lift theorem `ozGuardDiscipline_implies_RTO` — substantively
    proved (no sorry, no axiom). Anchors the body-to-trace lift end
    of the F4 obligation.
  * Site 3 (`executes_C_guard_locked_during_body_call`) —
    original body-call guard-lock site reasoning, preserved per
    Interpretation B (coexistence with the `_general` variant).
  * Site 3_general (`executes_C_guard_locked_during_body_call_general`)
    — Phase 5 Session 22 Unit 2 closure under W9 surface, applying
    Option (iii) + Strategy B + the Option II hoisted-helper variant
    of the path-(α) pattern. Consumes `cFrameProjection_length_eq_pos_length`
    (Phase 5 Session 22 Unit 1, BodyShape.lean) for length-equality
    threading.
  * `slot_unlocked_at_finish_of_C_frame` (Lemma B, Family C
    composition) and surrounding L2/L3 helpers from Phase 5 Session 9.

  Cross-references for the W9 closure path: an internal reconnaissance note
  (W9 reconnaissance survey; cross-module enumeration per M-19.2),
  an internal VRVP methodology note (Unit 2 retry record),
  an internal session report (γ closure 9/9 report). The §10.M-DG
  consolidation in the internal methodology notes documents the
  directive-grounding discipline that produced the clean S22 closure.
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
import QanaryContracts.Executes
import QanaryContracts.Executes.CountHelpers
import QanaryContracts.Executes.StackHistory
import QanaryContracts.Executes.BodyShape

namespace QanaryContracts

/-! ## Phase 5 Session 9 — L2 + L3 helpers (Family C composition)

Lemma B (`slot_unlocked_at_finish_of_C_frame`) — at every C-frame's
`finish` position, the slot is `C.unlockedValue`. Composes BodyShape's
central theorem + uniqueness corollaries with `slot_stable_no_sstore`
(Step.lean) to argue that no SSTORE on `(C.address, C.guardSlot)`
happens in `[p_unlock + 1, finish)`.

The supporting "no SSTORE post-unlock" claim is Family C's payoff:
without `guard_sstore_value_in_C_frame` + `unlock_position_unique`, the
case-split on the SSTOREd value would require enumerating every
sub-frame in the trace. With Family C, it's a 3-line case-split on
`v ∈ {lockedValue, unlockedValue}`. -/

/-- Helper: after applying `sstore a key val`, slot `(a, key)` has value
    `val`. The positive analogue of `slot_unchanged_by_non_sstore`
    (Step.lean). -/
private theorem applyStep_sstore_lookupSlot_eq
    (s : EVMState) (a : Address) (key val : Word256) :
    (applyStep s (EVMStep.sstore a key val)).lookupSlot a key = val := by
  unfold applyStep EVMState.lookupSlot Storage.lookupZ
  simp [Finmap.lookup_insert]

/-- **Lemma B (Phase 5 Session 9, Family C composition).** At the close
    of a C-frame (the `finish` position from `MatchesBody`), the slot
    `(C.address, C.guardSlot)` reads `C.unlockedValue`. -/
private theorem slot_unlocked_at_finish_of_C_frame
    (C : Contract) (h_distinct : C.lockedValue ≠ C.unlockedValue)
    (s₀ : EVMState) (tr : ExecutionTrace) (h_valid : ValidExecution tr)
    (q finish : Nat) (caller : Address) (value : Word256)
    (h_entry : tr[q]? = some (EVMStep.call caller C.address value))
    (f : FunctionBody) (h_oz : IsOZGuardedFunction C f)
    (h_match : MatchesBody C f tr q finish) :
    slotAt s₀ tr finish C.address C.guardSlot = C.unlockedValue := by
  obtain ⟨p_call, p_unlock, h_q1_lt_pc, h_pc_lt_pu, h_pu_lt_f,
          _, _, h_cf_pu, _, _, h_tr_pu⟩ :=
    matchesBody_oz_extracts_positions C tr q finish caller value h_entry f h_oz h_match
  have h_finish_le_tr : finish ≤ tr.length := h_match.2.1
  have h_q1_lt_pu : q + 1 < p_unlock := lt_trans h_q1_lt_pc h_pc_lt_pu
  have h_pu_lt_tr : p_unlock < tr.length := by omega
  -- After the unlock SSTORE at p_unlock, slot = unlockedValue.
  have h_slot_pu_succ : slotAt s₀ tr (p_unlock + 1) C.address C.guardSlot = C.unlockedValue := by
    unfold slotAt stateAt evalState
    have h_take : tr.take (p_unlock + 1) = tr.take p_unlock ++ [tr[p_unlock]'h_pu_lt_tr] := by
      rw [List.take_add_one, List.getElem?_eq_getElem h_pu_lt_tr]; rfl
    rw [h_take, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    have h_step_eq : tr[p_unlock]'h_pu_lt_tr =
        EVMStep.sstore C.address C.guardSlot C.unlockedValue := by
      have := h_tr_pu
      rw [List.getElem?_eq_getElem h_pu_lt_tr] at this
      exact Option.some_inj.mp this
    rw [h_step_eq]
    exact applyStep_sstore_lookupSlot_eq _ _ _ _
  -- No SSTOREs on (C.address, C.guardSlot) in [p_unlock + 1, finish).
  have h_no_sstore_post : ∀ p, p_unlock + 1 ≤ p → p < finish →
      ∀ step, tr[p]? = some step → ¬ step.IsSStoreOn C.address C.guardSlot := by
    intro p h_p_ge h_p_lt step h_step ⟨v, h_eq⟩
    rw [h_eq] at h_step
    have h_p_lt_tr : p < tr.length := by omega
    obtain ⟨h_so, _, _⟩ := h_valid
    have h_cf_p := h_so ⟨p, h_p_lt_tr⟩ C.address C.guardSlot v h_step
    have h_v_in : v = C.lockedValue ∨ v = C.unlockedValue :=
      guard_sstore_value_in_C_frame C tr q finish f h_oz h_match p
        (by omega) h_p_lt h_cf_p v h_step
    rcases h_v_in with h_v_lock | h_v_unlock
    · -- v = lockedValue: lock at q+1, but p > p_unlock > q+1. Contradiction.
      rw [h_v_lock] at h_step
      have h_p_eq := lock_position_unique_in_C_frame C h_distinct tr q finish caller value h_entry
        f h_oz h_match p (by omega) h_p_lt h_cf_p h_step
      have : q + 1 < p := by omega
      omega
    · -- v = unlockedValue: unlock at p_unlock, but p > p_unlock. Contradiction.
      rw [h_v_unlock] at h_step
      have h_p_eq := unlock_position_unique_in_C_frame C h_distinct tr q finish caller value h_entry
        f h_oz h_match p p_unlock (by omega) h_p_lt h_cf_p h_step
        h_q1_lt_pu h_pu_lt_f h_cf_pu h_tr_pu
      omega
  have h_stable := slot_stable_no_sstore s₀ tr C.address C.guardSlot
    (p_unlock + 1) finish (by omega) h_finish_le_tr h_no_sstore_post
  rw [h_stable] at h_slot_pu_succ
  exact h_slot_pu_succ

/-! ## Phase 5 Session 9 — L2: `executes_C_guard_unlocked_at_entry`

The argument: at every entry CALL into C, the guard slot is unlocked.
Strategy: take the largest `pmax < k` with an SSTORE on
`(C.address, C.guardSlot)` (via `Nat.findGreatest`).
* Case 1 (`pmax` doesn't satisfy P): no SSTORE in `[0, k)`, slot stable
  from `0` to `k`, slot at `k` = `unlockedValue` (`InitialGuardUnlocked`).
* Case 2 (`pmax` satisfies P): characterize the SSTOREd value via
  BodyShape's `guard_sstore_value_in_C_frame`. If `unlockedValue`, slot
  at `k` = `unlockedValue`. If `lockedValue`: derive contradiction. The
  q_-frame's unlock is at `p_unlock_ ∈ (pmax, finish_)`. The counting
  argument (two locks at `q_+1` and `k+1` would exceed `countP = 1`)
  forces `finish_ ≤ k + 1`. Hence `p_unlock_ ≤ k`. Since `p_unlock_` is
  an SSTORE and `k` is a CALL, `p_unlock_ < k`. This SSTORE in
  `(pmax, k)` contradicts the maximality of `pmax`. -/

/-- **L2 (Phase 5 Session 9, Layer 4 conjunct 3 helper).** Under
    `executes_C C s₀ tr` and `OZGuardDiscipline C` with distinct
    lock/unlock values, the guard slot of `C` reads `C.unlockedValue`
    at every entry CALL into `C.address`. -/
theorem executes_C_guard_unlocked_at_entry
    (C : Contract) (h_oz : OZGuardDiscipline C)
    (h_distinct : C.lockedValue ≠ C.unlockedValue)
    (s₀ : EVMState) (tr : ExecutionTrace)
    (h_exec : executes_C C s₀ tr)
    (k : Nat) (hk : k < tr.length)
    (caller : Address) (value : Word256)
    (h_call : tr[k]? = some (EVMStep.call caller C.address value)) :
    guardSlotAt s₀ tr k C.address C.guardSlot = C.unlockedValue := by
  classical
  set P : Nat → Prop := fun p =>
    ∃ v, tr[p]? = some (EVMStep.sstore C.address C.guardSlot v) with hP_def
  haveI : DecidablePred P := fun _ => Classical.dec _
  by_cases hk_pos : 0 < k
  · -- k > 0: use Nat.findGreatest over [0, k - 1].
    set pmax := Nat.findGreatest P (k - 1) with hpmax_def
    have h_pmax_le_km1 : pmax ≤ k - 1 := Nat.findGreatest_le _
    have h_pmax_lt_k : pmax < k := by omega
    have h_pmax_is_greatest : ∀ p', pmax < p' → p' ≤ k - 1 → ¬ P p' :=
      fun p' h_lt h_le => Nat.findGreatest_is_greatest h_lt h_le
    by_cases h_pmax_P : P pmax
    · -- pmax has an SSTORE on the guard slot. Extract the value.
      obtain ⟨v_, h_pmax_sstore⟩ := h_pmax_P
      have h_pmax_lt_tr : pmax < tr.length := by omega
      have h_slot_pmax_succ : guardSlotAt s₀ tr (pmax + 1) C.address C.guardSlot = v_ := by
        unfold guardSlotAt slotAt stateAt evalState
        have h_take : tr.take (pmax + 1) = tr.take pmax ++ [tr[pmax]'h_pmax_lt_tr] := by
          rw [List.take_add_one, List.getElem?_eq_getElem h_pmax_lt_tr]; rfl
        rw [h_take, List.foldl_append]
        simp only [List.foldl_cons, List.foldl_nil]
        have h_step_eq : tr[pmax]'h_pmax_lt_tr =
            EVMStep.sstore C.address C.guardSlot v_ := by
          have := h_pmax_sstore
          rw [List.getElem?_eq_getElem h_pmax_lt_tr] at this
          exact Option.some_inj.mp this
        rw [h_step_eq]
        exact applyStep_sstore_lookupSlot_eq _ _ _ _
      have h_no_sstore_post : ∀ p, pmax + 1 ≤ p → p < k → ∀ step, tr[p]? = some step →
          ¬ step.IsSStoreOn C.address C.guardSlot := by
        intro p h_pge h_plt step h_step ⟨v, h_eq⟩
        rw [h_eq] at h_step
        apply h_pmax_is_greatest p (by omega) (by omega)
        exact ⟨v, h_step⟩
      have h_slot_k : guardSlotAt s₀ tr k C.address C.guardSlot = v_ := by
        unfold guardSlotAt
        have h_stab := slot_stable_no_sstore s₀ tr C.address C.guardSlot
          (pmax + 1) k (by omega) (le_of_lt hk) h_no_sstore_post
        rw [← h_stab]; exact h_slot_pmax_succ
      have h_valid : ValidExecution tr := h_exec.1
      have h_dispatch : ∀ (k : Nat) (caller : Address) (value : Word256),
          k < tr.length → tr[k]? = some (EVMStep.call caller C.address value) →
          ∃ (f : FunctionBody) (finish : Nat),
            f ∈ C.functions ∧ MatchesBody C f tr k finish := h_exec.2.2
      have h_so : SStoresInOwnFrame tr := h_valid.1
      have h_cf_pmax : currentFrameAt tr pmax = some C.address :=
        h_so ⟨pmax, h_pmax_lt_tr⟩ C.address C.guardSlot v_ h_pmax_sstore
      have h_pmax_le : pmax ≤ tr.length := le_of_lt h_pmax_lt_tr
      obtain ⟨q_, caller_, value_, hq__lt_pmax, h_call_, h_nest_⟩ :=
        c_frame_open_implies_entry C s₀ tr h_exec pmax h_pmax_le h_cf_pmax
      have hq__lt_tr : q_ < tr.length := by omega
      obtain ⟨f_, finish_, hf__mem, h_match_⟩ :=
        h_dispatch q_ caller_ value_ hq__lt_tr h_call_
      have h_oz_all : ∀ f ∈ C.functions, IsOZGuardedFunction C f := h_oz.2
      have h_isOZ_ : IsOZGuardedFunction C f_ := h_oz_all f_ hf__mem
      have h_q__lt_f : q_ < finish_ := h_match_.1
      have h_finish__le_tr : finish_ ≤ tr.length := h_match_.2.1
      have h_dep_eq_ : frameDepthAt tr q_ = frameDepthAt tr finish_ := h_match_.2.2.2.1
      have h_pmax_lt_finish_ : pmax < finish_ := by
        by_contra h_ge
        push_neg at h_ge
        have h_d : finish_ - q_ - 1 < pmax - q_ := by omega
        have h_n := h_nest_ ⟨finish_ - q_ - 1, h_d⟩
        have h_pos : q_ + 1 + (finish_ - q_ - 1) = finish_ := by omega
        rw [h_pos] at h_n
        omega
      have h_pmax_ge_q1 : q_ + 1 ≤ pmax := by omega
      have h_v__in : v_ = C.lockedValue ∨ v_ = C.unlockedValue :=
        guard_sstore_value_in_C_frame C tr q_ finish_ f_ h_isOZ_ h_match_
          pmax h_pmax_ge_q1 h_pmax_lt_finish_ h_cf_pmax v_ h_pmax_sstore
      rcases h_v__in with h_v_lock | h_v_unlock
      · -- v_ = lockedValue: derive contradiction.
        exfalso
        rw [h_v_lock] at h_pmax_sstore
        have h_pmax_eq : pmax = q_ + 1 :=
          lock_position_unique_in_C_frame C h_distinct tr q_ finish_ caller_ value_ h_call_
            f_ h_isOZ_ h_match_ pmax h_pmax_ge_q1 h_pmax_lt_finish_ h_cf_pmax h_pmax_sstore
        obtain ⟨pcall_, punlock_, h_q1_lt_pc_, h_pc_lt_pu_, h_pu_lt_f_,
                h_cf_q_1, _, h_cf_pu_, h_tr_q_1, _, h_tr_pu_⟩ :=
          matchesBody_oz_extracts_positions C tr q_ finish_ caller_ value_ h_call_
            f_ h_isOZ_ h_match_
        -- Show finish_ ≤ k + 1 via the counting argument.
        have h_finish__le_k1 : finish_ ≤ k + 1 := by
          by_contra h_gt
          push_neg at h_gt
          have h_k1_lt_finish : k + 1 < finish_ := by omega
          have h_cf_k1 : currentFrameAt tr (k + 1) = some C.address :=
            currentFrameAt_after_call tr k caller C.address value h_call
          obtain ⟨f_k, finish_k, hf_k_mem, h_match_k⟩ :=
            h_dispatch k caller value hk h_call
          have h_isOZ_k : IsOZGuardedFunction C f_k := h_oz_all f_k hf_k_mem
          have h_tr_k1_lock : tr[k + 1]? =
              some (EVMStep.sstore C.address C.guardSlot C.lockedValue) :=
            matchesBody_implies_tr_kplus1_eq_lock C tr k finish_k caller value h_call
              f_k h_isOZ_k h_match_k
          have h_q1_lt_k1 : q_ + 1 < k + 1 := by omega
          have h_count := cFrameProjection_countP_ge_two C tr (q_ + 1) finish_ (isLockStep C)
            (q_ + 1) (k + 1) h_q1_lt_k1 (le_refl _) h_k1_lt_finish
            h_cf_q_1 h_cf_k1 _ _ h_tr_q_1 h_tr_k1_lock
            (by simp [isLockStep]) (by simp [isLockStep])
          obtain ⟨_, _, _, _, h_proj_⟩ := h_match_
          rw [h_proj_] at h_count
          have h_count_eq : (unfoldBody C f_).countP (isLockStep C) = 1 :=
            unfoldBody_countP_isLockStep_eq_one C f_ h_isOZ_ h_distinct
          omega
        have h_punlock_le_k : punlock_ ≤ k := by omega
        have h_punlock_ne_k : punlock_ ≠ k := by
          intro h_eq
          rw [h_eq] at h_tr_pu_
          rw [h_tr_pu_] at h_call
          cases h_call
        have h_punlock_lt_k : punlock_ < k := lt_of_le_of_ne h_punlock_le_k h_punlock_ne_k
        apply h_pmax_is_greatest punlock_ (by omega) (by omega)
        exact ⟨C.unlockedValue, h_tr_pu_⟩
      · -- v_ = unlockedValue: slot at k = unlockedValue. Done.
        rw [h_slot_k, h_v_unlock]
    · -- pmax does not satisfy P. By findGreatest_spec, no p ≤ k - 1 satisfies P.
      have h_no_sstore_lt_k : ∀ p, p < k → ¬ P p := by
        intro p hp h_P
        apply h_pmax_P
        have h_le : p ≤ k - 1 := by omega
        exact Nat.findGreatest_spec h_le h_P
      have h_no_sstore : ∀ p, p < k → ∀ step, tr[p]? = some step →
          ¬ step.IsSStoreOn C.address C.guardSlot := by
        intro p hp step h_step ⟨v, h_eq⟩
        rw [h_eq] at h_step
        exact h_no_sstore_lt_k p hp ⟨v, h_step⟩
      have h_stable := slot_stable_no_sstore s₀ tr C.address C.guardSlot 0 k
        (Nat.zero_le _) (le_of_lt hk) (fun p _ hp => h_no_sstore p hp)
      unfold guardSlotAt
      rw [← h_stable]
      obtain ⟨_, h_init, _⟩ := h_exec
      unfold slotAt stateAt evalState
      simp [List.take_zero]
      exact h_init
  · -- k = 0: slot at 0 = initial state's slot = unlockedValue.
    push_neg at hk_pos
    have hk0 : k = 0 := by omega
    subst hk0
    obtain ⟨_, h_init, _⟩ := h_exec
    unfold guardSlotAt slotAt stateAt evalState
    simp [List.take_zero]
    exact h_init

/-! ## Phase 5 Session 25 — L2_general: `executes_C_guard_unlocked_at_entry_general`

`_general` variant of L2 (Phase 5 Session 9, line 177) under
`OZGuardDisciplineGeneral`. Mechanical adaptation per Session 24
survey §3.1 substitution map: predicate substitution
`OZGuardDiscipline → OZGuardDisciplineGeneral`,
`IsOZGuardedFunction → IsOZGuardedFunctionGeneral`, plus the eight
internal helper substitutions to `_general` variants from Sessions
19-22 (`cFrameProjection_countP_ge_two` carries over directly as a
predicate-free counting helper).

The `matchesBody_oz_extracts_positions_general` invocation drops
the `pcall` extract per Option (iii); the line-281-analog omega
closes via the pmax/k-1 chain (Session 24 survey §7.5 prediction
verified at an internal VRVP methodology note §4).

Coexists with original L2; F4 lift_general (Unit 2) consumes
L2_general at Conjunct 3. Original L2 preserved unchanged per
Interpretation B coexistence at the BodyTraceLift layer. -/

/-- **L2_general (Phase 5 Session 25, sub-block δ-1).** Under
    `executes_C C s₀ tr` and `OZGuardDisciplineGeneral C` with
    distinct lock/unlock values, the guard slot of `C` reads
    `C.unlockedValue` at every entry CALL into `C.address`. -/
theorem executes_C_guard_unlocked_at_entry_general
    (C : Contract) (h_oz : OZGuardDisciplineGeneral C)
    (h_distinct : C.lockedValue ≠ C.unlockedValue)
    (s₀ : EVMState) (tr : ExecutionTrace)
    (h_exec : executes_C C s₀ tr)
    (k : Nat) (hk : k < tr.length)
    (caller : Address) (value : Word256)
    (h_call : tr[k]? = some (EVMStep.call caller C.address value)) :
    guardSlotAt s₀ tr k C.address C.guardSlot = C.unlockedValue := by
  classical
  set P : Nat → Prop := fun p =>
    ∃ v, tr[p]? = some (EVMStep.sstore C.address C.guardSlot v) with hP_def
  haveI : DecidablePred P := fun _ => Classical.dec _
  by_cases hk_pos : 0 < k
  · -- k > 0: use Nat.findGreatest over [0, k - 1].
    set pmax := Nat.findGreatest P (k - 1) with hpmax_def
    have h_pmax_le_km1 : pmax ≤ k - 1 := Nat.findGreatest_le _
    have h_pmax_lt_k : pmax < k := by omega
    have h_pmax_is_greatest : ∀ p', pmax < p' → p' ≤ k - 1 → ¬ P p' :=
      fun p' h_lt h_le => Nat.findGreatest_is_greatest h_lt h_le
    by_cases h_pmax_P : P pmax
    · -- pmax has an SSTORE on the guard slot. Extract the value.
      obtain ⟨v_, h_pmax_sstore⟩ := h_pmax_P
      have h_pmax_lt_tr : pmax < tr.length := by omega
      have h_slot_pmax_succ : guardSlotAt s₀ tr (pmax + 1) C.address C.guardSlot = v_ := by
        unfold guardSlotAt slotAt stateAt evalState
        have h_take : tr.take (pmax + 1) = tr.take pmax ++ [tr[pmax]'h_pmax_lt_tr] := by
          rw [List.take_add_one, List.getElem?_eq_getElem h_pmax_lt_tr]; rfl
        rw [h_take, List.foldl_append]
        simp only [List.foldl_cons, List.foldl_nil]
        have h_step_eq : tr[pmax]'h_pmax_lt_tr =
            EVMStep.sstore C.address C.guardSlot v_ := by
          have := h_pmax_sstore
          rw [List.getElem?_eq_getElem h_pmax_lt_tr] at this
          exact Option.some_inj.mp this
        rw [h_step_eq]
        exact applyStep_sstore_lookupSlot_eq _ _ _ _
      have h_no_sstore_post : ∀ p, pmax + 1 ≤ p → p < k → ∀ step, tr[p]? = some step →
          ¬ step.IsSStoreOn C.address C.guardSlot := by
        intro p h_pge h_plt step h_step ⟨v, h_eq⟩
        rw [h_eq] at h_step
        apply h_pmax_is_greatest p (by omega) (by omega)
        exact ⟨v, h_step⟩
      have h_slot_k : guardSlotAt s₀ tr k C.address C.guardSlot = v_ := by
        unfold guardSlotAt
        have h_stab := slot_stable_no_sstore s₀ tr C.address C.guardSlot
          (pmax + 1) k (by omega) (le_of_lt hk) h_no_sstore_post
        rw [← h_stab]; exact h_slot_pmax_succ
      have h_valid : ValidExecution tr := h_exec.1
      have h_dispatch : ∀ (k : Nat) (caller : Address) (value : Word256),
          k < tr.length → tr[k]? = some (EVMStep.call caller C.address value) →
          ∃ (f : FunctionBody) (finish : Nat),
            f ∈ C.functions ∧ MatchesBody C f tr k finish := h_exec.2.2
      have h_so : SStoresInOwnFrame tr := h_valid.1
      have h_cf_pmax : currentFrameAt tr pmax = some C.address :=
        h_so ⟨pmax, h_pmax_lt_tr⟩ C.address C.guardSlot v_ h_pmax_sstore
      have h_pmax_le : pmax ≤ tr.length := le_of_lt h_pmax_lt_tr
      obtain ⟨q_, caller_, value_, hq__lt_pmax, h_call_, h_nest_⟩ :=
        c_frame_open_implies_entry C s₀ tr h_exec pmax h_pmax_le h_cf_pmax
      have hq__lt_tr : q_ < tr.length := by omega
      obtain ⟨f_, finish_, hf__mem, h_match_⟩ :=
        h_dispatch q_ caller_ value_ hq__lt_tr h_call_
      have h_oz_all : ∀ f ∈ C.functions, IsOZGuardedFunctionGeneral C f := h_oz.2
      have h_isOZ_ : IsOZGuardedFunctionGeneral C f_ := h_oz_all f_ hf__mem
      have h_q__lt_f : q_ < finish_ := h_match_.1
      have h_finish__le_tr : finish_ ≤ tr.length := h_match_.2.1
      have h_dep_eq_ : frameDepthAt tr q_ = frameDepthAt tr finish_ := h_match_.2.2.2.1
      have h_pmax_lt_finish_ : pmax < finish_ := by
        by_contra h_ge
        push Not at h_ge
        have h_d : finish_ - q_ - 1 < pmax - q_ := by omega
        have h_n := h_nest_ ⟨finish_ - q_ - 1, h_d⟩
        have h_pos : q_ + 1 + (finish_ - q_ - 1) = finish_ := by omega
        rw [h_pos] at h_n
        omega
      have h_pmax_ge_q1 : q_ + 1 ≤ pmax := by omega
      have h_v__in : v_ = C.lockedValue ∨ v_ = C.unlockedValue :=
        guard_sstore_value_in_C_frame_general C tr q_ finish_ f_ h_isOZ_ h_match_
          pmax h_pmax_ge_q1 h_pmax_lt_finish_ h_cf_pmax v_ h_pmax_sstore
      rcases h_v__in with h_v_lock | h_v_unlock
      · -- v_ = lockedValue: derive contradiction.
        exfalso
        rw [h_v_lock] at h_pmax_sstore
        have h_pmax_eq : pmax = q_ + 1 :=
          lock_position_unique_in_C_frame_general C h_distinct tr q_ finish_ caller_ value_ h_call_
            f_ h_isOZ_ h_match_ pmax h_pmax_ge_q1 h_pmax_lt_finish_ h_cf_pmax h_pmax_sstore
        obtain ⟨punlock_, h_q1_lt_pu_, h_pu_lt_f_, h_cf_q_1, h_cf_pu_, h_tr_q_1, h_tr_pu_⟩ :=
          matchesBody_oz_extracts_positions_general C tr q_ finish_ caller_ value_ h_call_
            f_ h_isOZ_ h_match_
        -- Show finish_ ≤ k + 1 via the counting argument.
        have h_finish__le_k1 : finish_ ≤ k + 1 := by
          by_contra h_gt
          push Not at h_gt
          have h_k1_lt_finish : k + 1 < finish_ := by omega
          have h_cf_k1 : currentFrameAt tr (k + 1) = some C.address :=
            currentFrameAt_after_call tr k caller C.address value h_call
          obtain ⟨f_k, finish_k, hf_k_mem, h_match_k⟩ :=
            h_dispatch k caller value hk h_call
          have h_isOZ_k : IsOZGuardedFunctionGeneral C f_k := h_oz_all f_k hf_k_mem
          have h_tr_k1_lock : tr[k + 1]? =
              some (EVMStep.sstore C.address C.guardSlot C.lockedValue) :=
            matchesBody_implies_tr_kplus1_eq_lock_general C tr k finish_k caller value h_call
              f_k h_isOZ_k h_match_k
          have h_q1_lt_k1 : q_ + 1 < k + 1 := by omega
          have h_count := cFrameProjection_countP_ge_two C tr (q_ + 1) finish_ (isLockStep C)
            (q_ + 1) (k + 1) h_q1_lt_k1 (le_refl _) h_k1_lt_finish
            h_cf_q_1 h_cf_k1 _ _ h_tr_q_1 h_tr_k1_lock
            (by simp [isLockStep]) (by simp [isLockStep])
          obtain ⟨_, _, _, _, h_proj_⟩ := h_match_
          rw [h_proj_] at h_count
          have h_count_eq : (unfoldBody C f_).countP (isLockStep C) = 1 :=
            unfoldBody_countP_isLockStep_eq_one_general C f_ h_isOZ_ h_distinct
          omega
        have h_punlock_le_k : punlock_ ≤ k := by omega
        have h_punlock_ne_k : punlock_ ≠ k := by
          intro h_eq
          rw [h_eq] at h_tr_pu_
          rw [h_tr_pu_] at h_call
          cases h_call
        have h_punlock_lt_k : punlock_ < k := lt_of_le_of_ne h_punlock_le_k h_punlock_ne_k
        apply h_pmax_is_greatest punlock_ (by omega) (by omega)
        exact ⟨C.unlockedValue, h_tr_pu_⟩
      · -- v_ = unlockedValue: slot at k = unlockedValue. Done.
        rw [h_slot_k, h_v_unlock]
    · -- pmax does not satisfy P. By findGreatest_spec, no p ≤ k - 1 satisfies P.
      have h_no_sstore_lt_k : ∀ p, p < k → ¬ P p := by
        intro p hp h_P
        apply h_pmax_P
        have h_le : p ≤ k - 1 := by omega
        exact Nat.findGreatest_spec h_le h_P
      have h_no_sstore : ∀ p, p < k → ∀ step, tr[p]? = some step →
          ¬ step.IsSStoreOn C.address C.guardSlot := by
        intro p hp step h_step ⟨v, h_eq⟩
        rw [h_eq] at h_step
        exact h_no_sstore_lt_k p hp ⟨v, h_step⟩
      have h_stable := slot_stable_no_sstore s₀ tr C.address C.guardSlot 0 k
        (Nat.zero_le _) (le_of_lt hk) (fun p _ hp => h_no_sstore p hp)
      unfold guardSlotAt
      rw [← h_stable]
      obtain ⟨_, h_init, _⟩ := h_exec
      unfold slotAt stateAt evalState
      simp [List.take_zero]
      exact h_init
  · -- k = 0: slot at 0 = initial state's slot = unlockedValue.
    push Not at hk_pos
    have hk0 : k = 0 := by omega
    subst hk0
    obtain ⟨_, h_init, _⟩ := h_exec
    unfold guardSlotAt slotAt stateAt evalState
    simp [List.take_zero]
    exact h_init

/-! ## Phase 5 Session 9 — L3: `executes_C_guard_locked_during_body_call`

The argument: at every C-issued CALL inside a C-frame's body, the
guard slot is locked. Composes BodyShape's `c_call_in_C_frame_eq_p_call`
(any C-issued CALL inside the frame is at `p_call`) with
slot-stability + `lock_position_unique` and `unlock_position_unique`
ruling out other guard SSTOREs in `[q+2, p_call)`.

Note the strict hypothesis `currentFrameAt tr k = some C.address`:
this matches the body-call use case. The looser variant where
`currentFrameAt tr k = none` while `caller = C.address` (the
"phantom CALL" gap in `CallsFromTopFrame`) is outside this lemma's
scope — see Conjunct 4 closure for the case split. -/

/-- **L3 (Phase 5 Session 9, Layer 4 conjunct 4 helper).** Under
    `executes_C C s₀ tr` and `OZGuardDiscipline C` with distinct
    lock/unlock values, the guard slot of `C` reads `C.lockedValue`
    at every CALL with `caller = C.address` AND
    `currentFrameAt tr k = some C.address` (i.e., `C` is genuinely
    executing at position `k`). -/
theorem executes_C_guard_locked_during_body_call
    (C : Contract) (h_oz : OZGuardDiscipline C)
    (h_distinct : C.lockedValue ≠ C.unlockedValue)
    (s₀ : EVMState) (tr : ExecutionTrace)
    (h_exec : executes_C C s₀ tr)
    (k : Nat) (hk : k < tr.length)
    (callee : Address) (value : Word256)
    (h_call : tr[k]? = some (EVMStep.call C.address callee value))
    (h_cf_k : currentFrameAt tr k = some C.address) :
    guardSlotAt s₀ tr k C.address C.guardSlot = C.lockedValue := by
  have h_valid : ValidExecution tr := h_exec.1
  have h_dispatch : ∀ (k : Nat) (caller : Address) (value : Word256),
      k < tr.length → tr[k]? = some (EVMStep.call caller C.address value) →
      ∃ (f : FunctionBody) (finish : Nat),
        f ∈ C.functions ∧ MatchesBody C f tr k finish := h_exec.2.2
  have h_so : SStoresInOwnFrame tr := h_valid.1
  -- C is executing at k, so by c_frame_open_implies_entry there's an entry q < k.
  have hk_le : k ≤ tr.length := le_of_lt hk
  obtain ⟨q, caller_q, value_q, hq_lt_k, h_call_q, h_nest_q⟩ :=
    c_frame_open_implies_entry C s₀ tr h_exec k hk_le h_cf_k
  have hq_lt_tr : q < tr.length := lt_trans hq_lt_k hk
  obtain ⟨f, finish, hf_mem, h_match⟩ := h_dispatch q caller_q value_q hq_lt_tr h_call_q
  have h_oz_all : ∀ f ∈ C.functions, IsOZGuardedFunction C f := h_oz.2
  have h_isOZ : IsOZGuardedFunction C f := h_oz_all f hf_mem
  have h_q_lt_f : q < finish := h_match.1
  have h_finish_le_tr : finish ≤ tr.length := h_match.2.1
  have h_dep_eq : frameDepthAt tr q = frameDepthAt tr finish := h_match.2.2.2.1
  -- k < finish (else NestedAfter at d = finish - q - 1 contradicts depth balance).
  have hk_lt_finish : k < finish := by
    by_contra h_ge
    push_neg at h_ge
    have h_d : finish - q - 1 < k - q := by omega
    have h_n := h_nest_q ⟨finish - q - 1, h_d⟩
    have h_pos : q + 1 + (finish - q - 1) = finish := by omega
    rw [h_pos] at h_n
    omega
  have hq1_le_k : q + 1 ≤ k := by omega
  -- Use c_call_in_C_frame_eq_p_call (BodyShape) to get k = p_call, plus all the
  -- positional information about p_call and p_unlock.
  obtain ⟨pcall, punlock, h_k_eq_pc, h_q1_lt_pc, h_pc_lt_pu, h_pu_lt_f,
          h_cf_q1, h_cf_pu, h_tr_q1, h_tr_pu⟩ :=
    c_call_in_C_frame_eq_p_call C tr q finish caller_q value_q h_call_q f h_isOZ h_match
      k hq1_le_k hk_lt_finish h_cf_k callee value h_call
  -- Slot at q + 2 = lockedValue (after lock SSTORE at q + 1).
  have hq1_lt_tr : q + 1 < tr.length := by omega
  have h_slot_q2 : guardSlotAt s₀ tr (q + 2) C.address C.guardSlot = C.lockedValue := by
    unfold guardSlotAt slotAt stateAt evalState
    have h_take : tr.take (q + 2) = tr.take (q + 1) ++ [tr[q + 1]'hq1_lt_tr] := by
      rw [show q + 2 = (q + 1) + 1 from rfl, List.take_add_one,
          List.getElem?_eq_getElem hq1_lt_tr]
      rfl
    rw [h_take, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    have h_step_eq : tr[q + 1]'hq1_lt_tr =
        EVMStep.sstore C.address C.guardSlot C.lockedValue := by
      have := h_tr_q1
      rw [List.getElem?_eq_getElem hq1_lt_tr] at this
      exact Option.some_inj.mp this
    rw [h_step_eq]
    exact applyStep_sstore_lookupSlot_eq _ _ _ _
  -- No SSTOREs on (C.address, C.guardSlot) in [q + 2, k).
  have h_no_sstore_pre : ∀ p, q + 2 ≤ p → p < k → ∀ step, tr[p]? = some step →
      ¬ step.IsSStoreOn C.address C.guardSlot := by
    intro p h_pge h_plt step h_step ⟨v, h_eq⟩
    rw [h_eq] at h_step
    have h_p_lt_tr : p < tr.length := by omega
    have h_cf_p := h_so ⟨p, h_p_lt_tr⟩ C.address C.guardSlot v h_step
    have h_v_in : v = C.lockedValue ∨ v = C.unlockedValue :=
      guard_sstore_value_in_C_frame C tr q finish f h_isOZ h_match p
        (by omega) (by omega) h_cf_p v h_step
    rcases h_v_in with h_v_lock | h_v_unlock
    · -- v = lockedValue: p = q + 1 (lock_position_unique). But p ≥ q + 2. Contradiction.
      rw [h_v_lock] at h_step
      have h_p_eq := lock_position_unique_in_C_frame C h_distinct tr q finish caller_q value_q
        h_call_q f h_isOZ h_match p (by omega) (by omega) h_cf_p h_step
      omega
    · -- v = unlockedValue: p = punlock (unlock_position_unique). But p < k = pcall < punlock.
      rw [h_v_unlock] at h_step
      have h_q1_lt_pu : q + 1 < punlock := lt_trans h_q1_lt_pc h_pc_lt_pu
      have h_p_eq := unlock_position_unique_in_C_frame C h_distinct tr q finish caller_q value_q
        h_call_q f h_isOZ h_match p punlock (by omega) (by omega) h_cf_p h_step
        h_q1_lt_pu h_pu_lt_f h_cf_pu h_tr_pu
      -- p = punlock. But k = pcall < punlock = p, and p < k. Contradiction.
      omega
  -- Slot at k = slot at q + 2 = lockedValue (by slot stability).
  have hk_gt_q1 : q + 1 < k := by
    -- k = pcall and q + 1 < pcall (from h_q1_lt_pc).
    rw [h_k_eq_pc]; exact h_q1_lt_pc
  have h_stable := slot_stable_no_sstore s₀ tr C.address C.guardSlot
    (q + 2) k (by omega) hk_le h_no_sstore_pre
  unfold guardSlotAt
  rw [← h_stable]
  exact h_slot_q2

/-! ## Phase 5 Session 22 — Sub-block γ-2-residual: Site 3_general

`executes_C_guard_locked_during_body_call_general` — `_general` variant
of L3 (`executes_C_guard_locked_during_body_call`, line 340) under
`OZGuardDisciplineGeneral`. Coexists with the original L3
(Interpretation B; original retains CALL-uniqueness identification for
the single-CALL setting).

Strategy B composition: the `k < punlock` derivation goes through Session
22 Unit 1's `cFrameProjection_length_eq_pos_length` helper (closing the
glue-fact gap that fired Session 21's fallback) plus
`cFrameProjection_get?_via_pos`, `unlock_position_unique_in_C_frame_general`,
and constructor disjointness on `EVMStep.call`/`EVMStep.ret`/`EVMStep.sstore`.

Per Session 21 fallback's preserved analysis (an internal VRVP methodology note)
+ Session 22 VRVP retry (an internal VRVP methodology note). -/

/-- F2-B Site 3_general: trace-level guard-locked-during-body-call lemma
    under `OZGuardDisciplineGeneral`. Multi-CALL bodies admitted (the
    original L3's CALL-uniqueness identification is dropped per
    Option (iii); `k < punlock` is recovered via Strategy B composition
    through `cFrameProjection_length_eq_pos_length` + index-extraction
    chain). -/
theorem executes_C_guard_locked_during_body_call_general
    (C : Contract) (h_oz : OZGuardDisciplineGeneral C)
    (h_distinct : C.lockedValue ≠ C.unlockedValue)
    (s₀ : EVMState) (tr : ExecutionTrace)
    (h_exec : executes_C C s₀ tr)
    (k : Nat) (hk : k < tr.length)
    (callee : Address) (value : Word256)
    (h_call : tr[k]? = some (EVMStep.call C.address callee value))
    (h_cf_k : currentFrameAt tr k = some C.address) :
    guardSlotAt s₀ tr k C.address C.guardSlot = C.lockedValue := by
  have h_valid : ValidExecution tr := h_exec.1
  have h_dispatch : ∀ (k : Nat) (caller : Address) (value : Word256),
      k < tr.length → tr[k]? = some (EVMStep.call caller C.address value) →
      ∃ (f : FunctionBody) (finish : Nat),
        f ∈ C.functions ∧ MatchesBody C f tr k finish := h_exec.2.2
  have h_so : SStoresInOwnFrame tr := h_valid.1
  have hk_le : k ≤ tr.length := le_of_lt hk
  obtain ⟨q, caller_q, value_q, hq_lt_k, h_call_q, h_nest_q⟩ :=
    c_frame_open_implies_entry C s₀ tr h_exec k hk_le h_cf_k
  have hq_lt_tr : q < tr.length := lt_trans hq_lt_k hk
  obtain ⟨f, finish, hf_mem, h_match⟩ := h_dispatch q caller_q value_q hq_lt_tr h_call_q
  have h_oz_all : ∀ f ∈ C.functions, IsOZGuardedFunctionGeneral C f := h_oz.2
  have h_isOZ : IsOZGuardedFunctionGeneral C f := h_oz_all f hf_mem
  have h_q_lt_f : q < finish := h_match.1
  have h_finish_le_tr : finish ≤ tr.length := h_match.2.1
  have h_dep_eq : frameDepthAt tr q = frameDepthAt tr finish := h_match.2.2.2.1
  have hk_lt_finish : k < finish := by
    by_contra h_ge
    push Not at h_ge
    have h_d : finish - q - 1 < k - q := by omega
    have h_n := h_nest_q ⟨finish - q - 1, h_d⟩
    have h_pos : q + 1 + (finish - q - 1) = finish := by omega
    rw [h_pos] at h_n
    omega
  have hq1_le_k : q + 1 ≤ k := by omega
  -- Block F — M_general invocation (replaces original N).
  obtain ⟨punlock, h_q1_lt_pu, h_pu_lt_f, h_cf_q1, h_cf_pu, h_tr_q1, h_tr_pu⟩ :=
    matchesBody_oz_extracts_positions_general
      C tr q finish caller_q value_q h_call_q f h_isOZ h_match
  -- Block G — Slot at q + 2 = lockedValue (carry-over from original L3).
  have hq1_lt_tr : q + 1 < tr.length := by omega
  have h_slot_q2 : guardSlotAt s₀ tr (q + 2) C.address C.guardSlot = C.lockedValue := by
    unfold guardSlotAt slotAt stateAt evalState
    have h_take : tr.take (q + 2) = tr.take (q + 1) ++ [tr[q + 1]'hq1_lt_tr] := by
      rw [show q + 2 = (q + 1) + 1 from rfl, List.take_add_one,
          List.getElem?_eq_getElem hq1_lt_tr]
      rfl
    rw [h_take, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    have h_step_eq : tr[q + 1]'hq1_lt_tr =
        EVMStep.sstore C.address C.guardSlot C.lockedValue := by
      have := h_tr_q1
      rw [List.getElem?_eq_getElem hq1_lt_tr] at this
      exact Option.some_inj.mp this
    rw [h_step_eq]
    exact applyStep_sstore_lookupSlot_eq _ _ _ _
  -- Block H pre — Strategy B composition for k < punlock.
  have h_k_lt_punlock : k < punlock := by
    by_contra h_not_lt
    push Not at h_not_lt
    have h_ne : punlock ≠ k := by
      intro h_eq
      rw [← h_eq] at h_call
      rw [h_call] at h_tr_pu
      cases h_tr_pu
    have h_pu_lt_k : punlock < k := lt_of_le_of_ne h_not_lt h_ne
    -- Save copies of h_isOZ / h_match before destructuring (per
    -- an internal project note GOTCHA: `obtain` consumes the
    -- destructured hypothesis, but unlock_position_unique_in_C_frame_general
    -- needs both unconsumed below).
    have h_isOZ_save := h_isOZ
    have h_match_save := h_match
    obtain ⟨body, h_eq_body, _, _⟩ := h_isOZ
    have h_unf : unfoldBody C f =
        EVMStep.sstore C.address C.guardSlot C.lockedValue ::
          (body.map (liftStep C) ++
            [EVMStep.sstore C.address C.guardSlot C.unlockedValue,
             EVMStep.ret true]) := by
      unfold unfoldBody
      rw [h_eq_body]
      simp [List.map_cons, List.map_append, liftStep]
    have h_unf_len : (unfoldBody C f).length = body.length + 3 := by
      rw [h_unf]
      simp [List.length_cons, List.length_append, List.length_map]
    -- cFrameProjPos.length = body.length + 3 via Unit 1 helper.
    obtain ⟨_, _, _, _, h_proj⟩ := h_match
    have h_pos_len : (cFrameProjPos C tr (q + 1) finish).length = body.length + 3 := by
      rw [← cFrameProjection_length_eq_pos_length C tr (q + 1) finish h_finish_le_tr,
          h_proj, h_unf_len]
    -- k ∈ cFrameProjPos.
    have h_k_in_pos : k ∈ cFrameProjPos C tr (q + 1) finish := by
      unfold cFrameProjPos
      rw [List.mem_filter, List.mem_range']
      refine ⟨⟨k - (q + 1), by omega, by omega⟩, ?_⟩
      simp [h_cf_k]
    rw [List.mem_iff_getElem] at h_k_in_pos
    obtain ⟨m_k, h_m_k_lt, h_pos_m_k⟩ := h_k_in_pos
    have h_pos_m_k_opt : (cFrameProjPos C tr (q + 1) finish)[m_k]? = some k := by
      rw [List.getElem?_eq_getElem h_m_k_lt]
      exact congrArg some h_pos_m_k
    -- Identify punlock at index body.length + 1.
    have h_unf_unlock : (unfoldBody C f)[body.length + 1]? =
        some (EVMStep.sstore C.address C.guardSlot C.unlockedValue) :=
      unfoldBody_get?_unlock_general C body f h_eq_body
    have h_proj_unlock : (cFrameProjection C tr (q + 1) finish)[body.length + 1]? =
        some (EVMStep.sstore C.address C.guardSlot C.unlockedValue) := by
      rw [h_proj]; exact h_unf_unlock
    obtain ⟨p_pu, h_p_pu_pos, h_tr_p_pu⟩ :=
      cFrameProjection_get?_via_pos C tr (q + 1) finish h_finish_le_tr
        (body.length + 1) _ h_proj_unlock
    have h_p_pu_mem := List.mem_of_getElem? h_p_pu_pos
    obtain ⟨h_p_pu_ge, h_p_pu_lt_f, h_cf_p_pu⟩ :=
      cFrameProjPos_mem_range C tr (q + 1) finish p_pu h_p_pu_mem
    have h_p_pu_eq : p_pu = punlock :=
      unlock_position_unique_in_C_frame_general C h_distinct tr q finish
        f h_isOZ_save h_match_save p_pu punlock (by omega) h_p_pu_lt_f h_cf_p_pu h_tr_p_pu
        h_q1_lt_pu h_pu_lt_f h_cf_pu h_tr_pu
    -- Strict monotonicity → m_k > body.length + 1.
    have h_pw := cFrameProjPos_pairwise_lt C tr (q + 1) finish
    have h_blen_lt : body.length + 1 < (cFrameProjPos C tr (q + 1) finish).length := by
      rw [h_pos_len]; omega
    have h_pos_pu_at : (cFrameProjPos C tr (q + 1) finish)[body.length + 1]? = some punlock := by
      rw [← h_p_pu_eq]; exact h_p_pu_pos
    have h_mk_gt : body.length + 1 < m_k := by
      by_contra h_not_lt
      push Not at h_not_lt
      rcases lt_or_eq_of_le h_not_lt with h_lt | h_eq
      · -- m_k < body.length + 1: cFrameProjPos[m_k] < cFrameProjPos[body.length+1] = punlock.
        have h_lt' := List.pairwise_iff_getElem.mp h_pw m_k (body.length + 1)
          h_m_k_lt h_blen_lt h_lt
        rw [List.getElem?_eq_getElem h_m_k_lt] at h_pos_m_k_opt
        rw [List.getElem?_eq_getElem h_blen_lt] at h_pos_pu_at
        have h_lhs := Option.some_inj.mp h_pos_m_k_opt
        have h_rhs := Option.some_inj.mp h_pos_pu_at
        rw [h_lhs, h_rhs] at h_lt'
        omega
      · -- m_k = body.length + 1: cFrameProjPos[m_k] = punlock = k > punlock.
        rw [h_eq] at h_pos_m_k_opt
        rw [h_pos_pu_at] at h_pos_m_k_opt
        have : k = punlock := (Option.some_inj.mp h_pos_m_k_opt).symm
        omega
    have h_mk_lt_total : m_k < body.length + 3 := by rw [← h_pos_len]; exact h_m_k_lt
    have h_mk_eq : m_k = body.length + 2 := by omega
    -- Trace step at projection-index body.length + 2 = ret-evm.
    have h_unf_ret : (unfoldBody C f)[body.length + 2]? = some (EVMStep.ret true) := by
      rw [h_unf]
      simp only [List.getElem?_cons_succ]
      rw [List.getElem?_append_right (by simp [List.length_map])]
      simp [List.length_map]
    have h_proj_ret : (cFrameProjection C tr (q + 1) finish)[body.length + 2]? =
        some (EVMStep.ret true) := by
      rw [h_proj]; exact h_unf_ret
    obtain ⟨p_ret, h_p_ret_pos, h_tr_p_ret⟩ :=
      cFrameProjection_get?_via_pos C tr (q + 1) finish h_finish_le_tr
        (body.length + 2) _ h_proj_ret
    -- p_ret = k via cFrameProjPos[body.length + 2] = both.
    have h_p_ret_eq_k : p_ret = k := by
      have h_pos_m_k_at_blen2 : (cFrameProjPos C tr (q + 1) finish)[body.length + 2]? = some k := by
        rw [← h_mk_eq]; exact h_pos_m_k_opt
      rw [h_p_ret_pos] at h_pos_m_k_at_blen2
      exact Option.some_inj.mp h_pos_m_k_at_blen2
    -- Constructor disjointness: tr[k] = call vs tr[p_ret] = ret.
    rw [h_p_ret_eq_k] at h_tr_p_ret
    rw [h_call] at h_tr_p_ret
    cases h_tr_p_ret
  -- Block H proper — No-SSTOREs in [q + 2, k) (predicate-substituted).
  have h_no_sstore_pre : ∀ p, q + 2 ≤ p → p < k → ∀ step, tr[p]? = some step →
      ¬ step.IsSStoreOn C.address C.guardSlot := by
    intro p h_pge h_plt step h_step ⟨v, h_eq⟩
    rw [h_eq] at h_step
    have h_p_lt_tr : p < tr.length := by omega
    have h_cf_p := h_so ⟨p, h_p_lt_tr⟩ C.address C.guardSlot v h_step
    have h_v_in : v = C.lockedValue ∨ v = C.unlockedValue :=
      guard_sstore_value_in_C_frame_general C tr q finish f h_isOZ h_match p
        (by omega) (by omega) h_cf_p v h_step
    rcases h_v_in with h_v_lock | h_v_unlock
    · rw [h_v_lock] at h_step
      have h_p_eq := lock_position_unique_in_C_frame_general C h_distinct tr q finish
        caller_q value_q h_call_q f h_isOZ h_match p (by omega) (by omega) h_cf_p h_step
      omega
    · rw [h_v_unlock] at h_step
      have h_p_eq := unlock_position_unique_in_C_frame_general C h_distinct tr q finish
        f h_isOZ h_match p punlock (by omega) (by omega) h_cf_p h_step
        h_q1_lt_pu h_pu_lt_f h_cf_pu h_tr_pu
      omega
  -- Block I — q + 1 < k via constructor disjointness on h_tr_q1 vs h_call.
  have hk_gt_q1 : q + 1 < k := by
    have h_ne : k ≠ q + 1 := by
      intro h_eq
      rw [h_eq, h_tr_q1] at h_call
      cases h_call
    exact lt_of_le_of_ne hq1_le_k (Ne.symm h_ne)
  have h_stable := slot_stable_no_sstore s₀ tr C.address C.guardSlot
    (q + 2) k (by omega) hk_le h_no_sstore_pre
  unfold guardSlotAt
  rw [← h_stable]
  exact h_slot_q2

/-! ## The F4 Lift Theorem -/

/-- **F4 Lift Theorem — `ozGuardDiscipline_implies_RTO`.** Every
    body-faithful execution of an OZ-disciplined contract with
    distinct lock/unlock values is `ReachableTraceOf`-conformant.

    Formally: under `OZGuardDiscipline C` (the Phase-5-Session-4
    strengthened version with `NoSStoreOnGuardSlotInSteps` on
    pre/post — see `OZSoundness.lean`) and
    `C.lockedValue ≠ C.unlockedValue`, every trace `tr` for which
    `executes_C C s₀ tr` holds also satisfies
    `ReachableTraceOf C s₀ tr`. Composition with Theorem 5*
    (`reentrancy_free_universal` in `OZSoundness.lean`) then
    delivers
    `ReentrancyFreeGeneral C := ∀ s₀ tr, executes_C C s₀ tr →
    ¬ ReentrancyVulnerableStatefulOn C s₀ tr` — the body-faithful,
    OZ-discipline-aware reentrancy-freeness predicate that Layer 5's
    completeness theorem will quantify over.

    **VRVP-2 catalogued the conjunct derivation status** (per
    an internal methodology note §5 + Phase 5 Session 4 Step 2
    report):
    * Conjunct 1 (`InitialGuardUnlocked`) — built into `executes_C`.
    * Conjunct 2 (`ValidExecution`) — built into `executes_C`.
    * Conjunct 3 (`TraceEntryRevert`) — derived via "body completes
      + no SSTOREs between bodies" + `lockedValue ≠ unlockedValue`.
    * Conjunct 4 (`TraceCCallLocked`) — derived under the strengthened
      `NoSStoreOnGuardSlotInSteps` invariant (W4 wall closed).
    * Conjunct 5 (`TraceCFrameStartsWithLock`) — derived via
      `MatchesBody`'s body-faithfulness conjunct (first projection
      element = first `unfoldBody` element = lock SSTORE).

    *Status:* Phase 5 Session 11 — CLOSED. Conjuncts 3, 4, 5 proven
    via L2 / L3 / MatchesBody-faithfulness. The Conjunct 4 phantom-CALL
    case (W8, named in Session 9 / mechanically witnessed in
    Session 10's `QanaryContracts/W8.lean`) is discharged by the
    `NoPhantomCalls` antecedent added in Session 11. The hypothesis
    is mechanically discharged at deployment time per Layer 6's P4
    work; it states that any CALL with `caller = C.address` has C on
    top of the stack — exactly the EVM-semantic guarantee on a CALL
    opcode's caller field. -/
theorem ozGuardDiscipline_implies_RTO
    (C : Contract)
    (h_oz : OZGuardDiscipline C)
    (h_distinct : C.lockedValue ≠ C.unlockedValue)
    (s₀ : EVMState)
    (tr : ExecutionTrace)
    (h_exec : executes_C C s₀ tr)
    (h_no_phantom : NoPhantomCalls C tr) :
    ReachableTraceOf C s₀ tr := by
  obtain ⟨h_valid, h_init, h_dispatch⟩ := h_exec
  refine ⟨h_init, h_valid, ?_, ?_, ?_⟩
  · -- Conjunct 3 (TraceEntryRevert): direct from L2 (executes_C_guard_unlocked_at_entry).
    intro k caller value h_call
    have hk_lt : k.val < tr.length := k.isLt
    have h_exec' : executes_C C s₀ tr := ⟨h_valid, h_init, h_dispatch⟩
    have h_unlocked := executes_C_guard_unlocked_at_entry C h_oz h_distinct s₀ tr h_exec'
      k.val hk_lt caller value h_call
    rw [h_unlocked]
    exact h_distinct.symm
  · -- Conjunct 4 (TraceCCallLocked): use L3 in the genuine case;
    -- the "phantom CALL" case (currentFrameAt = none with caller = C.address)
    -- is W8 — not provable from the current `executes_C` hypotheses.
    intro k callee value h_call
    have hk_lt : k.val < tr.length := k.isLt
    have h_exec' : executes_C C s₀ tr := ⟨h_valid, h_init, h_dispatch⟩
    -- By CallsFromTopFrame, currentFrameAt = some C.address ∨ none.
    obtain ⟨_, h_calls_from, _⟩ := h_valid
    have h_disj := h_calls_from k C.address callee value h_call
    rcases h_disj with h_cf_some | h_cf_none
    · -- Case 1: currentFrameAt = some C.address. Use L3.
      exact executes_C_guard_locked_during_body_call C h_oz h_distinct s₀ tr h_exec'
        k.val hk_lt callee value h_call h_cf_some
    · -- Case 2: phantom CALL (W8). The `NoPhantomCalls` antecedent
      -- (Session 11 P3 resolution) rules out this case directly: any CALL
      -- with caller = C.address must have currentFrameAt = some C.address,
      -- contradicting the case hypothesis currentFrameAt = none.
      have h_cf_some : currentFrameAt tr k.val = some C.address :=
        h_no_phantom k callee value h_call
      rw [h_cf_none] at h_cf_some
      exact absurd h_cf_some (by simp)
  · -- Conjunct 5 (TraceCFrameStartsWithLock): direct from MatchesBody.
    intro k caller value h_call
    have hk_lt : k.val < tr.length := k.isLt
    obtain ⟨f, finish, hf_mem, h_match⟩ :=
      h_dispatch k.val caller value hk_lt h_call
    obtain ⟨_, h_oz_all⟩ := h_oz
    have h_isOZ : IsOZGuardedFunction C f := h_oz_all f hf_mem
    obtain ⟨pre, callee, val', post, h_eq, _, _, _, _, _⟩ := h_isOZ
    obtain ⟨h_klt, h_fle, _, _, h_proj⟩ := h_match
    -- currentFrameAt at k.val + 1 = some C.address (after the entry CALL pushed C)
    have h_cf : currentFrameAt tr (k.val + 1) = some C.address :=
      currentFrameAt_after_call tr k.val caller C.address value h_call
    -- The unfoldBody of an OZ-guarded body starts with the lock SSTORE.
    have h_unf_eq :
        unfoldBody C f =
          EVMStep.sstore C.address C.guardSlot C.lockedValue ::
            (pre.map (liftStep C) ++
              EVMStep.call C.address callee val' ::
              ((post ++
                [FunctionBody.Step.sstore C.guardSlot C.unlockedValue,
                 FunctionBody.Step.ret true]).map (liftStep C))) := by
      unfold unfoldBody
      rw [h_eq]
      simp [List.map_cons, List.map_append, liftStep]
    -- finish - (k.val + 1) > 0 (body has length ≥ 4, so projection ≥ 4 long, range ≥ 4)
    have h_f_len : f.length = pre.length + post.length + 4 := by
      rw [h_eq]
      simp [List.length_cons, List.length_append]
      omega
    have h_unf_len : (unfoldBody C f).length = f.length := by
      unfold unfoldBody; rw [List.length_map]
    have h_proj_len : (cFrameProjection C tr (k.val + 1) finish).length = f.length := by
      rw [h_proj, h_unf_len]
    -- Projection length ≤ range size, so range size ≥ f.length ≥ 4
    have h_range_ge : finish - (k.val + 1) ≥ f.length := by
      have h_le : (cFrameProjection C tr (k.val + 1) finish).length ≤ finish - (k.val + 1) := by
        unfold cFrameProjection
        calc (((List.range' (k.val + 1) (finish - (k.val + 1))).filter
                  (fun p => decide (currentFrameAt tr p = some C.address))).filterMap
                  (fun p => tr[p]?)).length
            ≤ ((List.range' (k.val + 1) (finish - (k.val + 1))).filter
                  (fun p => decide (currentFrameAt tr p = some C.address))).length :=
                List.length_filterMap_le _ _
          _ ≤ (List.range' (k.val + 1) (finish - (k.val + 1))).length :=
                List.length_filter_le _ _
          _ = finish - (k.val + 1) := List.length_range'
      omega
    have h_range_pos : finish - (k.val + 1) > 0 := by omega
    have h_kp1_lt_fin : k.val + 1 < finish := by omega
    have h_kp1_lt_tr : k.val + 1 < tr.length := lt_of_lt_of_le h_kp1_lt_fin h_fle
    -- Now compute the head of cFrameProjection: it's tr[k.val + 1]?
    -- since position k.val + 1 is in range and currentFrameAt at it = C.address.
    have h_some_get : ∃ s, tr[k.val + 1]? = some s := by
      cases h_some : tr[k.val + 1]? with
      | none =>
        exfalso
        rw [List.getElem?_eq_none_iff] at h_some
        omega
      | some s => exact ⟨s, rfl⟩
    obtain ⟨s_kp1, h_s_kp1⟩ := h_some_get
    have h_proj_head_eq : (cFrameProjection C tr (k.val + 1) finish).head?
        = tr[k.val + 1]? := by
      unfold cFrameProjection
      obtain ⟨n, hn⟩ : ∃ n, finish - (k.val + 1) = n + 1 :=
        ⟨finish - (k.val + 1) - 1, by omega⟩
      rw [hn]
      have h_dec : decide (currentFrameAt tr (k.val + 1) = some C.address) = true := by
        rw [h_cf]; simp
      show ((((k.val + 1) :: List.range' (k.val + 2) n).filter
              (fun p => decide (currentFrameAt tr p = some C.address))).filterMap
              (fun p => tr[p]?)).head? = tr[k.val + 1]?
      simp only [List.filter_cons, h_dec, if_true, List.filterMap_cons,
                 h_s_kp1, List.head?_cons]
    -- The head of unfoldBody is the lock SSTORE
    have h_unf_head : (unfoldBody C f).head? =
        some (EVMStep.sstore C.address C.guardSlot C.lockedValue) := by
      rw [h_unf_eq]
      rfl
    -- Combine: tr[k.val + 1]? = head? of projection = head? of unfoldBody = some (sstore lock)
    rw [← h_proj_head_eq, h_proj, h_unf_head]

/-! ## Phase 5 Session 25 — F4 Lift_general: `ozGuardDiscipline_implies_RTO_general`

`_general` variant of F4 lift (line 706) under `OZGuardDisciplineGeneral`,
composing through L2_general (Unit 1, line 354), Site 3_general
(Phase 5 Session 22 Unit 2, line 467), and the W9-closed surface
from Sessions 19-22.

Mechanical adaptation per Session 24 survey §3 six-category
specification:
* Hypothesis types: `OZGuardDiscipline` → `OZGuardDisciplineGeneral`.
* Site 3 invocation (Conjunct 4) → Site 3_general.
* L2 invocation (Conjunct 3) → L2_general.
* BodyShape Category 3 invocations: not directly invoked by F4 lift
  body (absorbed into L2_general / Site 3_general internals).
* Body-shape decomposition (Conjunct 5): 4-segment → 3-segment via
  Site 3_general's S22 U2 template at lines 540-547.
* Auxiliary lemmas: `currentFrameAt_after_call` + Mathlib generic
  positional helpers carry over directly (predicate-free).

Conjunct 5's destructure adapts from 10-component
(`pre, callee, val', post, h_eq, ...`) to 4-component
(`body, h_eq_body, _, _`). The `h_unf_eq` body shape changes from
4-segment to 3-segment (`lock :: body.map ++ [unlock-step, ret-step]`).
The `h_f_len` adjusts from `pre.length + post.length + 4` to
`body.length + 3` and flows through the positional argument
structurally.

VRVP authored at an internal VRVP methodology note:
six-category walkthrough + composition stress-test against L2_general
+ five anticipated structural surprises resolution + Strategy
composition stress-test + hand-construction + M-22.2 axiom record
prediction (Tier 3 canonical kernel triple).

Coexists with original F4 lift; original preserved unchanged per
Interpretation B coexistence at the F4 lift layer. Composition with
Theorem 5* in OZSoundness delivers the body-faithful, OZ-discipline-
general reentrancy-freeness predicate that Layer 5's completeness
quantifies over. -/

/-- **F4 Lift_general — `ozGuardDiscipline_implies_RTO_general`.**
    Multi-CALL extension of F4 lift (line 706) under
    `OZGuardDisciplineGeneral`. Body-faithful executions of
    OZ-discipline-general contracts with distinct lock/unlock values
    are `ReachableTraceOf`-conformant. -/
theorem ozGuardDiscipline_implies_RTO_general
    (C : Contract)
    (h_oz : OZGuardDisciplineGeneral C)
    (h_distinct : C.lockedValue ≠ C.unlockedValue)
    (s₀ : EVMState)
    (tr : ExecutionTrace)
    (h_exec : executes_C C s₀ tr)
    (h_no_phantom : NoPhantomCalls C tr) :
    ReachableTraceOf C s₀ tr := by
  obtain ⟨h_valid, h_init, h_dispatch⟩ := h_exec
  refine ⟨h_init, h_valid, ?_, ?_, ?_⟩
  · -- Conjunct 3 (TraceEntryRevert): direct from L2_general.
    intro k caller value h_call
    have hk_lt : k.val < tr.length := k.isLt
    have h_exec' : executes_C C s₀ tr := ⟨h_valid, h_init, h_dispatch⟩
    have h_unlocked := executes_C_guard_unlocked_at_entry_general C h_oz h_distinct s₀ tr h_exec'
      k.val hk_lt caller value h_call
    rw [h_unlocked]
    exact h_distinct.symm
  · -- Conjunct 4 (TraceCCallLocked): Site 3_general in the genuine case;
    -- phantom CALL case (W8) discharged by NoPhantomCalls antecedent.
    intro k callee value h_call
    have hk_lt : k.val < tr.length := k.isLt
    have h_exec' : executes_C C s₀ tr := ⟨h_valid, h_init, h_dispatch⟩
    obtain ⟨_, h_calls_from, _⟩ := h_valid
    have h_disj := h_calls_from k C.address callee value h_call
    rcases h_disj with h_cf_some | h_cf_none
    · -- Case 1: currentFrameAt = some C.address. Use Site 3_general.
      exact executes_C_guard_locked_during_body_call_general C h_oz h_distinct s₀ tr h_exec'
        k.val hk_lt callee value h_call h_cf_some
    · -- Case 2: phantom CALL (W8). Discharged via NoPhantomCalls.
      have h_cf_some : currentFrameAt tr k.val = some C.address :=
        h_no_phantom k callee value h_call
      rw [h_cf_none] at h_cf_some
      exact absurd h_cf_some (by simp)
  · -- Conjunct 5 (TraceCFrameStartsWithLock): from MatchesBody, adapted
    -- to IsOZGuardedFunctionGeneral's 4-component destructure + 3-segment
    -- body shape per Site 3_general's S22 U2 template.
    intro k caller value h_call
    have hk_lt : k.val < tr.length := k.isLt
    obtain ⟨f, finish, hf_mem, h_match⟩ :=
      h_dispatch k.val caller value hk_lt h_call
    obtain ⟨_, h_oz_all⟩ := h_oz
    have h_isOZ : IsOZGuardedFunctionGeneral C f := h_oz_all f hf_mem
    obtain ⟨body, h_eq_body, _, _⟩ := h_isOZ
    obtain ⟨h_klt, h_fle, _, _, h_proj⟩ := h_match
    -- currentFrameAt at k.val + 1 = some C.address.
    have h_cf : currentFrameAt tr (k.val + 1) = some C.address :=
      currentFrameAt_after_call tr k.val caller C.address value h_call
    -- 3-segment body shape.
    have h_unf_eq :
        unfoldBody C f =
          EVMStep.sstore C.address C.guardSlot C.lockedValue ::
            (body.map (liftStep C) ++
              [EVMStep.sstore C.address C.guardSlot C.unlockedValue,
               EVMStep.ret true]) := by
      unfold unfoldBody
      rw [h_eq_body]
      simp [List.map_cons, List.map_append, liftStep]
    -- f.length = body.length + 3 (3-segment).
    have h_f_len : f.length = body.length + 3 := by
      rw [h_eq_body]
      simp [List.length_cons, List.length_append]
    have h_unf_len : (unfoldBody C f).length = f.length := by
      unfold unfoldBody; rw [List.length_map]
    have h_proj_len : (cFrameProjection C tr (k.val + 1) finish).length = f.length := by
      rw [h_proj, h_unf_len]
    have h_range_ge : finish - (k.val + 1) ≥ f.length := by
      have h_le : (cFrameProjection C tr (k.val + 1) finish).length ≤ finish - (k.val + 1) := by
        unfold cFrameProjection
        calc (((List.range' (k.val + 1) (finish - (k.val + 1))).filter
                  (fun p => decide (currentFrameAt tr p = some C.address))).filterMap
                  (fun p => tr[p]?)).length
            ≤ ((List.range' (k.val + 1) (finish - (k.val + 1))).filter
                  (fun p => decide (currentFrameAt tr p = some C.address))).length :=
                List.length_filterMap_le _ _
          _ ≤ (List.range' (k.val + 1) (finish - (k.val + 1))).length :=
                List.length_filter_le _ _
          _ = finish - (k.val + 1) := List.length_range'
      omega
    have h_range_pos : finish - (k.val + 1) > 0 := by omega
    have h_kp1_lt_fin : k.val + 1 < finish := by omega
    have h_kp1_lt_tr : k.val + 1 < tr.length := lt_of_lt_of_le h_kp1_lt_fin h_fle
    have h_some_get : ∃ s, tr[k.val + 1]? = some s := by
      cases h_some : tr[k.val + 1]? with
      | none =>
        exfalso
        rw [List.getElem?_eq_none_iff] at h_some
        omega
      | some s => exact ⟨s, rfl⟩
    obtain ⟨s_kp1, h_s_kp1⟩ := h_some_get
    have h_proj_head_eq : (cFrameProjection C tr (k.val + 1) finish).head?
        = tr[k.val + 1]? := by
      unfold cFrameProjection
      obtain ⟨n, hn⟩ : ∃ n, finish - (k.val + 1) = n + 1 :=
        ⟨finish - (k.val + 1) - 1, by omega⟩
      rw [hn]
      have h_dec : decide (currentFrameAt tr (k.val + 1) = some C.address) = true := by
        rw [h_cf]; simp
      show ((((k.val + 1) :: List.range' (k.val + 2) n).filter
              (fun p => decide (currentFrameAt tr p = some C.address))).filterMap
              (fun p => tr[p]?)).head? = tr[k.val + 1]?
      simp only [List.filter_cons, h_dec, if_true, List.filterMap_cons,
                 h_s_kp1, List.head?_cons]
    have h_unf_head : (unfoldBody C f).head? =
        some (EVMStep.sstore C.address C.guardSlot C.lockedValue) := by
      rw [h_unf_eq]
      rfl
    rw [← h_proj_head_eq, h_proj, h_unf_head]

end QanaryContracts
