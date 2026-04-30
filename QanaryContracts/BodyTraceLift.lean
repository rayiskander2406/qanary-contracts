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

namespace QanaryContracts

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
