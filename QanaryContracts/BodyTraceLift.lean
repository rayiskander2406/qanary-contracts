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

  This file ships the theorem statement + `sorry` body. Per Ray's
  Phase 5 Session 4 Step 3 directive (2026-04-28): "Build green with
  sorry. Report before attempting the proof." The substantive proof
  spans Sessions 5+, gated by VRVP-3 confirmation.

  **R2 note:** this is a deliberate, transient deviation from R2's
  "never theorem := sorry" rule, authorized by Ray in the Phase 5
  Session 4 Step 3 directive. The `sorry` body is a typecheck-only
  placeholder; downstream code that depends on this theorem will
  inherit the `sorryAx` axiom (the `#print axioms` audit on any
  downstream theorem will surface that). Sorry will be replaced by
  tactics in Phase 5 Session 5+ once VRVP-3 succeeds and Ray
  authorizes proof work.
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

    *Status:* Phase 5 Session 4 Step 3 SKELETON (`sorry` body).
    Substantive proof is the Phase 5 Session 5+ deliverable, gated
    by VRVP-3. -/
theorem ozGuardDiscipline_implies_RTO
    (C : Contract)
    (h_oz : OZGuardDiscipline C)
    (h_distinct : C.lockedValue ≠ C.unlockedValue)
    (s₀ : EVMState)
    (tr : ExecutionTrace)
    (h_exec : executes_C C s₀ tr) :
    ReachableTraceOf C s₀ tr := by
  obtain ⟨h_valid, h_init, h_dispatch⟩ := h_exec
  refine ⟨h_init, h_valid, ?_, ?_, ?_⟩
  · -- Conjunct 3 (TraceEntryRevert): substantive (Phase B).
    sorry
  · -- Conjunct 4 (TraceCCallLocked): substantive (Phase B).
    sorry
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

end QanaryContracts
