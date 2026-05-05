/-
  QanaryContracts/Completeness.lean

  Phase 5 Session 13 Unit 2 — Layer 5 Completeness foundation module.

  This module houses the four sub-case theorems that compose into the
  eventual constructive completeness disjunction:

    ReentrancyFreeGeneral C ⟸
      (∃ slot, OZGuardConfig C slot) ∨
      SatisfiesCEI_AllPaths C ∨
      NoSStores C ∨
      NoExternalCalls C

  Sub-case naming convention: `no_*_implies_RFG` for the contrapositive
  direction (predicate implies reentrancy-freeness).

  ## Status (Phase 5 Session 13)

  * `no_functions_implies_RFG` : PROVED (vacuous foundational case;
    NoFunctions C ⊆ NoExternalCalls C). The substantive
    `NoExternalCalls` sub-case requires general-frame stack-history
    primitives (a public version of `stackAt_index_has_entry` from
    `Executes/StackHistory.lean`, currently `private`) that will be
    developed during F2 multi-call generalization. Promoting that
    primitive in isolation in this session would trigger
    HS-COMPLETENESS-INFRASTRUCTURE-DRIFT; embedding the full proof
    here would trigger HS-COMPLETENESS-CAP. The vacuous case is
    honestly weaker than the eventual `NoExternalCalls` sub-case but
    provides the Layer 5 architecture (`ReentrancyFreeGeneral`
    predicate + naming convention + file placement) at zero
    infrastructure cost.
  * `no_external_calls_implies_RFG` : DEFERRED to Sessions 14-21
    (post-F2 polish or Session 22 lead-in to F3 instantiation work).
  * `no_sstores_implies_RFG` : DEFERRED to Sessions 26-30.
  * `cei_all_paths_implies_RFG` : DEFERRED to Sessions 26-30.
  * `oz_guard_config_implies_RFG` : DEFERRED to Sessions 26-30
    (essentially Theorem 5's statement restated against the Layer 5
    `ReentrancyFreeGeneral` predicate).

  The disjunction theorem `oz_completeness_full` lands in Sessions 26-30.

  ## Honest framing

  The vacuous `no_functions_implies_RFG` case covers contracts whose
  `functions` field is the empty list. Such contracts cannot be
  "reentered" because there are no functions to call — `executes_C`'s
  dispatch obligation immediately contradicts any CALL into `C.address`.
  The result is a worked example of the vacuous-case proof pattern
  that the four substantive sub-cases will refine; it does NOT cover
  the substantive case where `C.functions` is non-empty but no body
  issues an external CALL. That substantive case (`NoExternalCalls`)
  is a strict superset of `NoFunctions` and lands in Sessions 14-21.

  ## F2 closure status (post-Session-27)

  Substantive completeness sub-cases established:
  * `no_functions_implies_RFG` (line 115) — vacuous foundation
    (Session 13).
  * `no_external_calls_implies_RFG` (line ~245) — substantive sub-case
    via Path (b) NestedAfter induction + cFrameProjection-via-
    MatchesBody body-step identification (Session 27 F2 closure).
    Does not invoke the W9-closed `_general` surface; uses operational
    stack-history infrastructure orthogonal to body-shape soundness.

  Remaining deferred sub-cases (post-F2 work):
  * `NoSStores` predicate, `no_sstores_implies_RFG` theorem.
  * `SatisfiesCEI_AllPaths`, `cei_all_paths_implies_RFG`.
  * `OZGuardConfig`, `oz_guard_config_implies_RFG`.
  * `oz_completeness_full` disjunction theorem.

  These are full constructive completeness work, scheduled after F2
  + Layer 6 instantiation per program trajectory.

  **F2 STRUCTURALLY COMPLETE** at Session 27. The multi-CALL universal
  soundness theorem composes: predicate (Sessions 14-15), body-shape
  soundness (Sessions 17-22), body-to-trace lift (Session 25),
  substantive completeness sub-case (Session 27).
-/
import QanaryContracts.Contract
import QanaryContracts.FunctionBody
import QanaryContracts.EVM
import QanaryContracts.Storage
import QanaryContracts.Reentrancy
import QanaryContracts.ValidExecution
import QanaryContracts.Reachability
import QanaryContracts.Executes
import QanaryContracts.OZSoundness

namespace QanaryContracts

/-! ## Layer 5 reentrancy-freeness predicate -/

/-- The Layer 5 universal reentrancy-freeness predicate, quantifying
    over body-faithful `executes_C` operational executions. The
    four-witness disjunction (future work) targets this predicate.

    Distinct from `ReentrancyFree C` (RTO-quantified): the F4 lift
    `ozGuardDiscipline_implies_RTO` connects `executes_C` to
    `ReachableTraceOf` under a `NoPhantomCalls` antecedent (per W8 P3
    resolution; see the internal paper scaffold §11). `ReentrancyFreeGeneral`
    quantifies over `executes_C` directly, which is the natural
    quantification structure for the four-witness disjunction's
    sub-cases (each sub-case predicate constrains the contract's
    bodies via `C.functions`, and `executes_C`'s dispatch carries
    that constraint into the trace). -/
def ReentrancyFreeGeneral (C : Contract) : Prop :=
  ∀ (s₀ : EVMState) (tr : ExecutionTrace),
    executes_C C s₀ tr → ¬ ReentrancyVulnerableStatefulOn C s₀ tr

/-! ## Vacuous foundational sub-case predicate -/

/-- A contract has no declared functions. Strict subset of the
    eventual `NoExternalCalls C` predicate (a contract with no
    functions trivially has no body issuing external CALLs).

    This predicate supports the vacuous foundational case
    `no_functions_implies_RFG` proved below; the substantive
    `NoExternalCalls` predicate and its sub-case proof land in
    Sessions 14-21. -/
def NoFunctions (C : Contract) : Prop := C.functions = []

/-! ## Substantive sub-case predicate -/

/-- F2-B substantive (Phase 5 Session 27): a contract whose declared
    functions contain no `FunctionBody.Step.call` constructors at all.
    Strict superset of `NoFunctions C` (a contract with no functions
    trivially has no body containing `.call`); strict subset of "only
    self-calls allowed" (Option B at Session 26 survey §3.1).

    Per Session 26 survey §3.1 Option A formulation: the strict
    "no calls at all" form is what makes the body-step-impossibility
    argument (R3 of the substantive sub-case proof) work — under this
    predicate, `unfoldBody C f` for any `f ∈ C.functions` contains no
    `EVMStep.call`, so a trace position carrying a CALL cannot
    correspond to any body step in any matched `f`. -/
def NoExternalCalls (C : Contract) : Prop :=
  ∀ f ∈ C.functions, ∀ step ∈ f, ∀ callee value,
    step ≠ FunctionBody.Step.call callee value

/-! ## Vacuous foundational sub-case theorem -/

/-- **Vacuous foundational sub-case (1 of 4):** a contract with no
    declared functions is body-faithfully reentrancy-free.

    The proof: `executes_C C s₀ tr`'s dispatch obligation requires
    every CALL into `C.address` to dispatch to *some* `f ∈ C.functions`.
    With `C.functions = []`, no such `f` exists. Therefore any CALL
    into `C.address` contradicts `executes_C`. Reentrancy requires
    two such CALLs, so no reentrancy witness can exist.

    Honest framing: `NoFunctions C ⊆ NoExternalCalls C`. The
    substantive `NoExternalCalls` sub-case (where `C.functions ≠ []`
    but no body issues a CALL) is deferred per the module docstring;
    its proof requires general-frame stack-history primitives
    (`stackAt_index_has_entry` made public, plus a "no sub-frames in a
    no-CALL C-frame" lemma) developed during F2 multi-call work. -/
theorem no_functions_implies_RFG
    (C : Contract) (h_no_funcs : NoFunctions C) :
    ReentrancyFreeGeneral C := by
  intro s₀ tr h_exec h_vuln
  obtain ⟨i, j, h_ij, h_jlen, ⟨c1, v1, h_call_i⟩, _, _, _⟩ := h_vuln
  obtain ⟨_, _, h_dispatch⟩ := h_exec
  have hilen : i < tr.length := lt_trans h_ij h_jlen
  obtain ⟨f, _, hf_mem, _⟩ := h_dispatch i c1 v1 hilen h_call_i
  rw [h_no_funcs] at hf_mem
  simp at hf_mem

/-! ## Substantive sub-case theorem -/

/-- Helper for `no_external_calls_implies_RFG`: a step at a position
    inside an open C-frame matched by `MatchesBody` (with
    `currentFrameAt = some C.address` at that position) is in
    `unfoldBody C f`. Phase 5 Session 27 Unit 2.
    Predicate-free; carries over for both `IsOZGuardedFunction` and
    `IsOZGuardedFunctionGeneral` consumers without modification. -/
private theorem step_in_unfoldBody_of_currentFrameAt_at_C
    (C : Contract) (tr : ExecutionTrace) (f : FunctionBody)
    (i finish : Nat) (h_match : MatchesBody C f tr i finish)
    (p : Nat) (h_p_ge : i + 1 ≤ p) (h_p_lt : p < finish)
    (h_cf : currentFrameAt tr p = some C.address)
    (step : EVMStep) (h_step : tr[p]? = some step) :
    step ∈ unfoldBody C f := by
  have h_proj : cFrameProjection C tr (i + 1) finish = unfoldBody C f :=
    h_match.2.2.2.2
  rw [← h_proj]
  unfold cFrameProjection
  rw [List.mem_filterMap]
  refine ⟨p, ?_, h_step⟩
  rw [List.mem_filter]
  refine ⟨?_, ?_⟩
  · rw [List.mem_range']
    exact ⟨p - (i + 1), by omega, by omega⟩
  · simp [h_cf]

/-- **Substantive sub-case (2 of 4) — F2 closure (Phase 5 Session 27):**
    a contract whose declared functions contain no `Step.call` is
    body-faithfully reentrancy-free.

    Path (b) — operational stack-history infrastructure (frameDepthAt,
    currentFrameAt, NestedAfter, CallsFromTopFrame) plus
    cFrameProjection-via-MatchesBody body-step identification. The
    proof does NOT invoke any W9-closed `_general` lemma per Session 26
    survey's infrastructure-bypass framing.

    Three reductions per Session 26 survey §4 / Session 27 VRVP §2-3:

    * **R1+R2 (joint invariant):** induction over (i, j] with
      invariant `currentFrameAt p = some C.address ∧
      frameDepthAt p = frameDepthAt i + 1`. Each non-sstore step at
      p ∈ [i+1, j-1] is impossible (call → contradicts NoExternalCalls
      via cFrameProjection-of-f_i; ret/revert → drops depth to
      depth(i), contradicts NestedAfter at p+1 ≤ j). The invariant
      establishes `currentFrameAt j = some C.address`.

    * **R3 (body-step impossibility):** `tr[j] = call _ C.address _ ∈
      unfoldBody C f_i = f_i.map (liftStep C)`; `List.mem_map` extracts
      `s ∈ f_i` with `liftStep s = call`; only `Step.call` lifts to
      `EVMStep.call`; `NoExternalCalls` forbids `Step.call` in
      `f_i`. Contradiction.

    Original `no_functions_implies_RFG` (vacuous foundation) preserved
    unchanged. The substantive case admits all contracts with
    `C.functions ≠ []` provided no body has `Step.call`.

    F2 closure: with this theorem, the universal soundness theorem for
    the multi-CALL setting is structurally complete (predicate +
    body-shape soundness + body-to-trace lift + substantive
    completeness sub-case). Layer 5 disjunction theorem
    `oz_completeness_full` and remaining sub-cases (NoSStores,
    SatisfiesCEI_AllPaths, OZGuardConfig) are post-F2 / Layer 6
    instantiation work. -/
theorem no_external_calls_implies_RFG
    (C : Contract) (h_no_external : NoExternalCalls C) :
    ReentrancyFreeGeneral C := by
  intro s₀ tr h_exec h_vuln
  obtain ⟨i, j, h_ij, h_jlen, ⟨caller₁, value₁, h_call_i⟩,
          ⟨caller₂, value₂, h_call_j⟩, h_nested, _⟩ := h_vuln
  obtain ⟨h_valid, _, h_dispatch⟩ := h_exec
  obtain ⟨_, h_calls_from, _⟩ := h_valid
  -- Get matched body for i's CALL.
  have h_i_lt_tr : i < tr.length := lt_trans h_ij h_jlen
  obtain ⟨f_i, finish_i, hf_i_mem, h_match_i⟩ :=
    h_dispatch i caller₁ value₁ h_i_lt_tr h_call_i
  -- Derive j < finish_i from NestedAfter + h_match_i depth equality.
  have h_i_lt_finish : i < finish_i := h_match_i.1
  have h_match_i_depth : frameDepthAt tr i = frameDepthAt tr finish_i :=
    h_match_i.2.2.2.1
  have h_j_lt_finish : j < finish_i := by
    by_contra h_ge
    push Not at h_ge
    -- Apply NestedAfter at d := finish_i - i - 1 (position finish_i)
    have h_d_lt : finish_i - i - 1 < j - i := by omega
    have h_n := h_nested ⟨finish_i - i - 1, h_d_lt⟩
    have h_eq : i + 1 + (finish_i - i - 1) = finish_i := by omega
    rw [h_eq] at h_n
    omega
  -- Joint invariant induction over (i, j].
  have h_inv : ∀ d : Nat, i + 1 + d ≤ j →
      currentFrameAt tr (i + 1 + d) = some C.address ∧
      frameDepthAt tr (i + 1 + d) = frameDepthAt tr i + 1 := by
    intro d
    induction d with
    | zero =>
      intro _
      refine ⟨?_, ?_⟩
      · simpa using
          currentFrameAt_after_call tr i caller₁ C.address value₁ h_call_i
      · simpa using
          frameDepthAt_after_call tr i caller₁ C.address value₁ h_call_i
    | succ d' ih =>
      intro h_le
      have h_le' : i + 1 + d' ≤ j := by omega
      obtain ⟨h_cf, h_depth⟩ := ih h_le'
      have h_p_lt_j : i + 1 + d' < j := by omega
      have h_p_lt_tr : i + 1 + d' < tr.length := lt_trans h_p_lt_j h_jlen
      have h_p_lt_finish : i + 1 + d' < finish_i :=
        lt_trans h_p_lt_j h_j_lt_finish
      -- Get tr[p]?
      have h_some : ∃ step, tr[i + 1 + d']? = some step := by
        cases h : tr[i + 1 + d']? with
        | none => rw [List.getElem?_eq_none_iff] at h; omega
        | some s => exact ⟨s, rfl⟩
      obtain ⟨step, h_step⟩ := h_some
      have h_succ_eq : i + 1 + (d' + 1) = i + 1 + d' + 1 := by omega
      rw [h_succ_eq]
      cases step with
      | sstore a key val =>
        refine ⟨?_, ?_⟩
        · rw [currentFrameAt_after_sstore tr (i + 1 + d') a key val h_step]
          exact h_cf
        · rw [frameDepthAt_after_sstore tr (i + 1 + d') a key val h_step]
          exact h_depth
      | call X Y v =>
        exfalso
        -- CallsFromTopFrame: currentFrameAt = some X ∨ none. Combine with h_cf.
        have h_disj :=
          h_calls_from ⟨i + 1 + d', h_p_lt_tr⟩ X Y v h_step
        rcases h_disj with h_eq_some | h_eq_none
        · rw [h_cf] at h_eq_some
          have h_X : X = C.address := by
            have h := Option.some_inj.mp h_eq_some
            exact h.symm
          subst h_X
          have h_in_unfold : EVMStep.call C.address Y v ∈ unfoldBody C f_i :=
            step_in_unfoldBody_of_currentFrameAt_at_C C tr f_i i finish_i
              h_match_i (i + 1 + d') (by omega) h_p_lt_finish h_cf
              (EVMStep.call C.address Y v) h_step
          unfold unfoldBody at h_in_unfold
          rw [List.mem_map] at h_in_unfold
          obtain ⟨s, hs_mem, h_lift⟩ := h_in_unfold
          cases s with
          | sstore _ _ => exact absurd h_lift (by simp [liftStep])
          | call cl vl =>
            exact h_no_external f_i hf_i_mem (FunctionBody.Step.call cl vl)
              hs_mem cl vl rfl
          | ret _ => exact absurd h_lift (by simp [liftStep])
          | revert => exact absurd h_lift (by simp [liftStep])
        · rw [h_cf] at h_eq_none
          simp at h_eq_none
      | ret success =>
        exfalso
        have h_depth' :=
          frameDepthAt_after_ret tr (i + 1 + d') success h_step
        have h_nested_succ :
            frameDepthAt tr (i + 1 + (d' + 1)) > frameDepthAt tr i :=
          h_nested ⟨d' + 1, by omega⟩
        rw [h_succ_eq, h_depth', h_depth] at h_nested_succ
        omega
      | revert =>
        exfalso
        have h_depth' := frameDepthAt_after_revert tr (i + 1 + d') h_step
        have h_nested_succ :
            frameDepthAt tr (i + 1 + (d' + 1)) > frameDepthAt tr i :=
          h_nested ⟨d' + 1, by omega⟩
        rw [h_succ_eq, h_depth', h_depth] at h_nested_succ
        omega
  -- Apply h_inv at d := j - i - 1 to get currentFrameAt j = some C.address.
  have h_d_le : i + 1 + (j - i - 1) ≤ j := by omega
  have h_inv_j := h_inv (j - i - 1) h_d_le
  have h_eq_j : i + 1 + (j - i - 1) = j := by omega
  rw [h_eq_j] at h_inv_j
  obtain ⟨h_cf_j, _⟩ := h_inv_j
  -- R3: j ∈ cFrameProjection of f_i; tr[j] = call → Step.call ∈ f_i; contradicts.
  have h_in_unfold : EVMStep.call caller₂ C.address value₂ ∈ unfoldBody C f_i :=
    step_in_unfoldBody_of_currentFrameAt_at_C C tr f_i i finish_i h_match_i
      j (by omega) h_j_lt_finish h_cf_j
      (EVMStep.call caller₂ C.address value₂) h_call_j
  unfold unfoldBody at h_in_unfold
  rw [List.mem_map] at h_in_unfold
  obtain ⟨s, hs_mem, h_lift⟩ := h_in_unfold
  cases s with
  | sstore _ _ => exact absurd h_lift (by simp [liftStep])
  | call cl vl =>
    exact h_no_external f_i hf_i_mem (FunctionBody.Step.call cl vl) hs_mem
      cl vl rfl
  | ret _ => exact absurd h_lift (by simp [liftStep])
  | revert => exact absurd h_lift (by simp [liftStep])

end QanaryContracts
