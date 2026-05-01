/-
  QanaryContracts/Executes/StackHistory.lean

  Phase 5 Session 8 — open-frame identification module (resolves W5).

  Co-equal sibling of `QanaryContracts/Executes/CountHelpers.lean` in the
  two-family infrastructure model identified at the close of Session 7:

    * Anti-nesting family:   count-arithmetic over `cFrameProjection`
                             (`CountHelpers.lean`, used by L1).
    * Open-frame identification family:  stack-history induction on
                             `stackAt` (this file, used by L2 / L3).

  The load-bearing export is `c_frame_open_implies_entry`: under
  `executes_C` (which carries `ValidExecution`, hence `BalancedFrames`),
  whenever `currentFrameAt tr p = some C.address`, there exists `q < p`
  such that `tr[q]?` is some `(EVMStep.call caller C.address value)` and
  `NestedAfter tr q p` holds. In words: if `C` is the executing frame at
  position `p`, somewhere strictly earlier is the entry CALL that opened
  the still-open `C`-frame.

  The proof is a strengthened induction over a stack-history invariant
  (`stackAt_index_has_entry`): every position in `stackAt tr p`, not just
  the head, has its entry CALL identified, with both the `NestedAfter`
  property and the depth-at-entry equation. The depth equation is what
  makes the induction's `.ret` / `.revert` cases close — without it, the
  inductive step can't show that depth at `k+1` (after a pop) still
  exceeds the entry depth of frames that survive the pop.

  VRVP-D for the lemma statement is documented in
  an internal session report (three candidates: stack-top-without-CALL,
  closed-and-reopened, on-stack-but-not-top — all fail).
-/
import QanaryContracts.Executes
import QanaryContracts.Executes.CountHelpers

namespace QanaryContracts

/-! ## Helper: lifting list-equality through indexed `getElem`

The induction proof rewrites `stackAt tr (k+1)` via the step-evolution
lemmas, then reads off the j-th element. Lean's `rewrite` tactic refuses
those rewrites because the `getElem` proof of bounds depends on the
rewritten list. The cleanest workaround is to lift through `?`-indexing
(which is bound-free), then unwrap. -/

private theorem stackAt_getElem_eq_of_getElem?_eq
    {tr tr' : ExecutionTrace} {p p' j j' : Nat}
    (h? : (stackAt tr p)[j]? = (stackAt tr' p')[j']?)
    (hj : j < (stackAt tr p).length) (hj' : j' < (stackAt tr' p').length) :
    (stackAt tr p)[j]'hj = (stackAt tr' p')[j']'hj' := by
  rw [List.getElem?_eq_getElem hj, List.getElem?_eq_getElem hj'] at h?
  exact Option.some_inj.mp h?

/-! ## Strengthened invariant: every stack index has an entry -/

/-- **Strengthened stack-history invariant.** Under `BalancedFrames`,
    every index `j < (stackAt tr p).length` has an entry CALL position
    `q < p` whose callee is `(stackAt tr p)[j]`, with `NestedAfter tr q p`,
    and with the entry depth `frameDepthAt tr q` equal to
    `(stackAt tr p).length - 1 - j` (the number of frames *below* `j` in
    the stack at `p`).

    The depth equation is load-bearing for the induction — it survives
    `.ret` / `.revert` (which lower depth by 1 and shrink the stack by 1
    in lockstep) precisely because both sides decrement together.

    Proof: induction on `p`, casing on `tr[p-1]` for the step kind. The
    `j` parameter and its bounds proof `hj` are quantified *inside* the
    induction (introduced fresh in each branch) so the IH is `∀ j hj, …`
    rather than the j-fixed specialization. -/
private theorem stackAt_index_has_entry
    (tr : ExecutionTrace) (h_balanced : BalancedFrames tr) :
    ∀ (p : Nat) (_hp : p ≤ tr.length)
      (j : Nat) (hj : j < (stackAt tr p).length),
    ∃ q caller value, q < p ∧
      tr[q]? = some (EVMStep.call caller ((stackAt tr p)[j]'hj) value) ∧
      NestedAfter tr q p ∧
      frameDepthAt tr q = ((stackAt tr p).length : Int) - 1 - j := by
  intro p
  induction p with
  | zero =>
    intro _hp j hj
    -- stackAt tr 0 = [], so j < 0 is false.
    exfalso
    have h_empty : stackAt tr 0 = [] := by unfold stackAt; simp
    rw [h_empty] at hj
    exact absurd hj (by simp)
  | succ k ih =>
    intro hp j hj
    have hk_lt : k < tr.length := hp
    have hk_le : k ≤ tr.length := Nat.le_of_lt hk_lt
    have hstep : tr[k]? = some (tr[k]'hk_lt) := List.getElem?_eq_getElem hk_lt
    cases hstep_case : tr[k]'hk_lt with
    | call caller_k callee_k value_k =>
      have hstep' : tr[k]? = some (EVMStep.call caller_k callee_k value_k) := by
        rw [hstep, hstep_case]
      have h_stack_eq : stackAt tr (k + 1) = callee_k :: stackAt tr k :=
        stackAt_after_call tr k caller_k callee_k value_k hstep'
      have h_dep_eq : frameDepthAt tr (k + 1) = frameDepthAt tr k + 1 :=
        frameDepthAt_after_call tr k caller_k callee_k value_k hstep'
      have h_dep_k_eq : frameDepthAt tr k = ((stackAt tr k).length : Int) :=
        frameDepthAt_eq_length_stackAt tr h_balanced k hk_lt
      have h_len_succ : (stackAt tr (k + 1)).length = (stackAt tr k).length + 1 := by
        rw [h_stack_eq]; simp [List.length_cons]
      by_cases hj0 : j = 0
      · -- j = 0: the new top frame is callee_k. Entry q = k.
        subst hj0
        refine ⟨k, caller_k, value_k, Nat.lt_succ_self k, ?_, ?_, ?_⟩
        · have h_get0 : (stackAt tr (k + 1))[0]'hj = callee_k := by
            apply Option.some_inj.mp
            rw [← List.getElem?_eq_getElem hj, h_stack_eq]
            rfl
          rw [h_get0]; exact hstep'
        · intro d
          have hd : d.val = 0 := by have := d.isLt; omega
          rw [hd, Nat.add_zero, h_dep_eq]; omega
        · rw [h_dep_k_eq, h_len_succ]; push_cast; omega
      · -- j ≥ 1: write j = j' + 1 and apply IH at p = k.
        obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        have hj_k : j' < (stackAt tr k).length := by
          have : j' + 1 < (stackAt tr k).length + 1 := by
            rw [← h_len_succ]; exact hj
          omega
        have h_get_eq :
            (stackAt tr (k + 1))[j' + 1]'hj = (stackAt tr k)[j']'hj_k := by
          apply stackAt_getElem_eq_of_getElem?_eq
          rw [h_stack_eq, List.getElem?_cons_succ]
        obtain ⟨q', caller', value', hq'_lt, h_call', h_nest', h_dep_q'⟩ :=
          ih hk_le j' hj_k
        refine ⟨q', caller', value', Nat.lt_succ_of_lt hq'_lt, ?_, ?_, ?_⟩
        · rw [h_get_eq]; exact h_call'
        · intro d
          have hd_lt : d.val < k + 1 - q' := d.isLt
          by_cases h_d_lt_km : d.val < k - q'
          · exact h_nest' ⟨d.val, h_d_lt_km⟩
          · have h_d_eq : d.val = k - q' := by omega
            have h_pos_eq : q' + 1 + d.val = k + 1 := by rw [h_d_eq]; omega
            rw [h_pos_eq, h_dep_eq]
            have h_km1_lt : k - q' - 1 < k - q' := by omega
            have h_nest_at_k := h_nest' ⟨k - q' - 1, h_km1_lt⟩
            have h_pos_k : q' + 1 + (k - q' - 1) = k := by omega
            rw [h_pos_k] at h_nest_at_k
            omega
        · rw [h_dep_q', h_len_succ]; push_cast; omega
    | ret success =>
      have hstep' : tr[k]? = some (EVMStep.ret success) := by
        rw [hstep, hstep_case]
      have h_stack_eq : stackAt tr (k + 1) = (stackAt tr k).tail :=
        stackAt_after_ret tr k success hstep'
      have h_dep_eq : frameDepthAt tr (k + 1) = frameDepthAt tr k - 1 :=
        frameDepthAt_after_ret tr k success hstep'
      -- Destruct stackAt tr k to make tail-indexing concrete.
      cases h_stack_k : stackAt tr k with
      | nil =>
        exfalso
        rw [h_stack_k] at h_stack_eq; simp at h_stack_eq
        rw [h_stack_eq] at hj; exact absurd hj (by simp)
      | cons hd tl =>
        have h_stack_kp1 : stackAt tr (k + 1) = tl := by
          rw [h_stack_eq, h_stack_k]; rfl
        have h_len_k : (stackAt tr k).length = tl.length + 1 := by
          rw [h_stack_k]; simp
        have h_len_kp1 : (stackAt tr (k + 1)).length = tl.length := by
          rw [h_stack_kp1]
        have hj_k : j + 1 < (stackAt tr k).length := by
          rw [h_len_k]
          have hj' : j < tl.length := by rw [← h_len_kp1]; exact hj
          omega
        have h_get_eq :
            (stackAt tr (k + 1))[j]'hj = (stackAt tr k)[j + 1]'hj_k := by
          apply stackAt_getElem_eq_of_getElem?_eq
          rw [h_stack_kp1, h_stack_k, List.getElem?_cons_succ]
        obtain ⟨q', caller', value', hq'_lt, h_call', h_nest', h_dep_q'⟩ :=
          ih hk_le (j + 1) hj_k
        refine ⟨q', caller', value', Nat.lt_succ_of_lt hq'_lt, ?_, ?_, ?_⟩
        · rw [h_get_eq]; exact h_call'
        · intro d
          have hd_lt : d.val < k + 1 - q' := d.isLt
          by_cases h_d_lt_km : d.val < k - q'
          · exact h_nest' ⟨d.val, h_d_lt_km⟩
          · have h_d_eq : d.val = k - q' := by omega
            have h_pos_eq : q' + 1 + d.val = k + 1 := by rw [h_d_eq]; omega
            rw [h_pos_eq, h_dep_eq]
            have h_dep_k_eq : frameDepthAt tr k = ((stackAt tr k).length : Int) :=
              frameDepthAt_eq_length_stackAt tr h_balanced k hk_lt
            rw [h_dep_q', h_dep_k_eq, h_len_k]; push_cast; omega
        · rw [h_dep_q', h_len_kp1, h_len_k]; push_cast; omega
    | revert =>
      have hstep' : tr[k]? = some EVMStep.revert := by
        rw [hstep, hstep_case]
      have h_stack_eq : stackAt tr (k + 1) = (stackAt tr k).tail :=
        stackAt_after_revert tr k hstep'
      have h_dep_eq : frameDepthAt tr (k + 1) = frameDepthAt tr k - 1 :=
        frameDepthAt_after_revert tr k hstep'
      cases h_stack_k : stackAt tr k with
      | nil =>
        exfalso
        rw [h_stack_k] at h_stack_eq; simp at h_stack_eq
        rw [h_stack_eq] at hj; exact absurd hj (by simp)
      | cons hd tl =>
        have h_stack_kp1 : stackAt tr (k + 1) = tl := by
          rw [h_stack_eq, h_stack_k]; rfl
        have h_len_k : (stackAt tr k).length = tl.length + 1 := by
          rw [h_stack_k]; simp
        have h_len_kp1 : (stackAt tr (k + 1)).length = tl.length := by
          rw [h_stack_kp1]
        have hj_k : j + 1 < (stackAt tr k).length := by
          rw [h_len_k]
          have hj' : j < tl.length := by rw [← h_len_kp1]; exact hj
          omega
        have h_get_eq :
            (stackAt tr (k + 1))[j]'hj = (stackAt tr k)[j + 1]'hj_k := by
          apply stackAt_getElem_eq_of_getElem?_eq
          rw [h_stack_kp1, h_stack_k, List.getElem?_cons_succ]
        obtain ⟨q', caller', value', hq'_lt, h_call', h_nest', h_dep_q'⟩ :=
          ih hk_le (j + 1) hj_k
        refine ⟨q', caller', value', Nat.lt_succ_of_lt hq'_lt, ?_, ?_, ?_⟩
        · rw [h_get_eq]; exact h_call'
        · intro d
          have hd_lt : d.val < k + 1 - q' := d.isLt
          by_cases h_d_lt_km : d.val < k - q'
          · exact h_nest' ⟨d.val, h_d_lt_km⟩
          · have h_d_eq : d.val = k - q' := by omega
            have h_pos_eq : q' + 1 + d.val = k + 1 := by rw [h_d_eq]; omega
            rw [h_pos_eq, h_dep_eq]
            have h_dep_k_eq : frameDepthAt tr k = ((stackAt tr k).length : Int) :=
              frameDepthAt_eq_length_stackAt tr h_balanced k hk_lt
            rw [h_dep_q', h_dep_k_eq, h_len_k]; push_cast; omega
        · rw [h_dep_q', h_len_kp1, h_len_k]; push_cast; omega
    | sstore a key val =>
      have hstep' : tr[k]? = some (EVMStep.sstore a key val) := by
        rw [hstep, hstep_case]
      have h_stack_eq : stackAt tr (k + 1) = stackAt tr k :=
        stackAt_after_sstore tr k a key val hstep'
      have h_dep_eq : frameDepthAt tr (k + 1) = frameDepthAt tr k :=
        frameDepthAt_after_sstore tr k a key val hstep'
      have h_len_eq : (stackAt tr (k + 1)).length = (stackAt tr k).length := by
        rw [h_stack_eq]
      have hj_k : j < (stackAt tr k).length := by rw [← h_len_eq]; exact hj
      have h_get_eq :
          (stackAt tr (k + 1))[j]'hj = (stackAt tr k)[j]'hj_k := by
        apply stackAt_getElem_eq_of_getElem?_eq
        rw [h_stack_eq]
      obtain ⟨q', caller', value', hq'_lt, h_call', h_nest', h_dep_q'⟩ :=
        ih hk_le j hj_k
      refine ⟨q', caller', value', Nat.lt_succ_of_lt hq'_lt, ?_, ?_, ?_⟩
      · rw [h_get_eq]; exact h_call'
      · intro d
        have hd_lt : d.val < k + 1 - q' := d.isLt
        by_cases h_d_lt_km : d.val < k - q'
        · exact h_nest' ⟨d.val, h_d_lt_km⟩
        · have h_d_eq : d.val = k - q' := by omega
          have h_pos_eq : q' + 1 + d.val = k + 1 := by rw [h_d_eq]; omega
          rw [h_pos_eq, h_dep_eq]
          have h_km1_lt : k - q' - 1 < k - q' := by omega
          have h_nest_at_k := h_nest' ⟨k - q' - 1, h_km1_lt⟩
          have h_pos_k : q' + 1 + (k - q' - 1) = k := by omega
          rw [h_pos_k] at h_nest_at_k
          exact h_nest_at_k
      · rw [h_dep_q', h_len_eq]

/-! ## The W5-closing structural lemma -/

/-- **Open-frame identification structural lemma (W5).** Under
    `executes_C C s₀ tr`, whenever `currentFrameAt tr p = some C.address`
    at any position `p ≤ tr.length`, there exists a strictly-earlier
    entry CALL `q < p` into `C` with `NestedAfter tr q p`.

    Specialization of `stackAt_index_has_entry` to `j = 0` (the head /
    top of the stack), composed with the iff
    `currentFrameAt = (stackAt).head?`. Used by L2 (Conjunct 3) and L3
    (Conjunct 4) of `BodyTraceLift.lean`.

    *VRVP-D verdict:* the lemma statement is sound; three candidate
    counter-examples (stack-top-without-CALL, closed-and-reopened,
    on-stack-but-not-top) all fail to refute it. See
    an internal session report for full VRVP-D documentation. -/
theorem c_frame_open_implies_entry
    (C : Contract) (s₀ : EVMState) (tr : ExecutionTrace)
    (h_exec : executes_C C s₀ tr)
    (p : Nat) (hp : p ≤ tr.length)
    (h_cf : currentFrameAt tr p = some C.address) :
    ∃ q caller value, q < p ∧
      tr[q]? = some (EVMStep.call caller C.address value) ∧
      NestedAfter tr q p := by
  obtain ⟨h_valid, _, _⟩ := h_exec
  obtain ⟨_, _, h_balanced⟩ := h_valid
  rw [currentFrameAt_eq_head_stackAt] at h_cf
  -- Stack at p is non-empty with head C.address.
  have h_nonempty : (stackAt tr p).length > 0 := by
    cases h : stackAt tr p with
    | nil => rw [h] at h_cf; simp at h_cf
    | cons _ _ => simp
  obtain ⟨q, caller, value, hq_lt, h_call, h_nest, _⟩ :=
    stackAt_index_has_entry tr h_balanced p hp 0 h_nonempty
  -- (stackAt tr p)[0] equals the head, which equals C.address by h_cf.
  have h_head : (stackAt tr p)[0]'h_nonempty = C.address := by
    have h0? : (stackAt tr p)[0]? = some C.address := by
      cases h_eq : stackAt tr p with
      | nil =>
        exfalso
        rw [h_eq] at h_nonempty; exact absurd h_nonempty (by simp)
      | cons hd tl =>
        rw [h_eq] at h_cf
        simp at h_cf
        -- After cases-substitution, goal is `(hd :: tl)[0]? = some C.address`.
        -- (hd :: tl)[0]? = some hd by rfl, and h_cf : hd = C.address.
        rw [h_cf]; rfl
    have h_get : (stackAt tr p)[0]? = some ((stackAt tr p)[0]'h_nonempty) :=
      List.getElem?_eq_getElem h_nonempty
    rw [h_get] at h0?
    exact Option.some_inj.mp h0?
  rw [h_head] at h_call
  exact ⟨q, caller, value, hq_lt, h_call, h_nest⟩

end QanaryContracts
