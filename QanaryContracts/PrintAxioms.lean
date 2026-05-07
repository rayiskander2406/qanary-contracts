/-
  QanaryContracts/PrintAxioms.lean

  Axiom audit gate. Per Ray (Phase 3, 2026-04-27, Priority 3):
    "Every new file must pass #print axioms check before the session
     closes. Zero project axioms. Only propext and standard kernel
     axioms are acceptable. This is non-negotiable."

  Run via: `lake env lean QanaryContracts/PrintAxioms.lean`
-/
import QanaryContracts.DAOAttack
import QanaryContracts.MultiFunction
import QanaryContracts.Tests
import QanaryContracts.ReentrancyFree
import QanaryContracts.CEISufficiency
import QanaryContracts.Reachability
import QanaryContracts.CEISufficiencyV2
import QanaryContracts.OZSoundness
import QanaryContracts.BodyTraceLift
import QanaryContracts.W8
import QanaryContracts.Completeness
import QanaryContracts.DAOContract
import QanaryContracts.CompoundContract

open QanaryContracts

-- Phase 2 anchor (re-asserted)
#print axioms dao_attack_is_reentrant

-- Phase 3 first session — every public def gets audited via a
-- representative theorem. We do this by re-stating the test-case
-- examples as named theorems so #print axioms can target them.

theorem audit_dao_violates_cei : ¬ SatisfiesCEI daoAttackTrace := by
  native_decide

theorem audit_safe_satisfies_cei : SatisfiesCEI safeWithdrawTrace := by
  native_decide

theorem audit_multifunction_satisfies_cei : SatisfiesCEI multiFunctionTrace := by
  native_decide

theorem audit_dao_stateful_vulnerable :
    hasStatefulReentrancyWitness EVMState.empty daoAttackTrace
      daoVictim 0 2 ozGuardSlot ozUnlockedValue = true := by
  native_decide

theorem audit_guard_protected_blocks_state_aware :
    hasStatefulReentrancyWitness EVMState.empty guardProtectedTrace
      daoVictim 0 3 ozGuardSlot ozUnlockedValue = false := by
  native_decide

#print axioms audit_dao_violates_cei
#print axioms audit_safe_satisfies_cei
#print axioms audit_multifunction_satisfies_cei
#print axioms audit_dao_stateful_vulnerable
#print axioms audit_guard_protected_blocks_state_aware

-- Phase 3 Session 2 (2026-04-27) — named negative completeness theorem
#print axioms reentrancy_free_or_vulnerable_witness

-- Phase 3 Session 3 (2026-04-27) — Theorem 2 (CEI sufficiency, vacuous form)
-- + the "honest wall" lemmas that document the gap.
#print axioms QanaryContracts.daoAttackTrace_validExecution
#print axioms QanaryContracts.daoAttackTrace_violates_cei
#print axioms QanaryContracts.hypothesis_H_is_inconsistent
#print axioms QanaryContracts.cei_implies_no_reentrancy

-- Phase 3 Session 3 (2026-04-27, Decision 2) — W2 counter-example,
-- machine-checked. Documents that ValidExecution + SatisfiesCEI +
-- ReentrancyVulnerableStateful are jointly satisfiable at the
-- current abstraction level, ruling out any naive CEI-only soundness
-- proof strategy.
#print axioms QanaryContracts.statelessReentrancyTrace_validExecution
#print axioms QanaryContracts.statelessReentrancyTrace_satisfies_cei
#print axioms QanaryContracts.statelessReentrancyTrace_is_reentrancy_vulnerable
#print axioms QanaryContracts.stateless_trace_breaks_naive_strategy

-- Phase 4 Session 2 (2026-04-27, Decisions 1+2) — Track A.1 refinement
-- of `ReachableTraceOf` to embed `InitialGuardUnlocked`. The Session 1
-- placeholder universal lemma is now DELETED; in its place we audit
-- the negative result that mechanically witnesses the placeholder
-- breakage, plus the new API helper `reachableTraceOf_of_initialGuardUnlocked`.
--
-- Note: `cei_implies_no_reentrancy_v2` is no longer a `theorem` — it
-- has been refactored to a Prop-valued `def` (`cei_implies_no_reentrancy_v2_target`)
-- pending the substantive Session 3+ proof. No theorem claim, so no
-- audit line for the v2 statement until the proof lands.
#print axioms QanaryContracts.not_initialGuardUnlocked_v4_empty
#print axioms QanaryContracts.not_reachableTraceOf_universal
-- reachableTraceOf_of_initialGuardUnlocked: DELETED Phase 4 Session 6
-- (RTO body now requires more than just InitialGuardUnlocked, so
-- the helper no longer makes sense as written)

-- Phase 4 Session 3 (2026-04-27) — WALL: Track A.1 is insufficient.
-- The v2 universal hypothesis is STILL globally inconsistent under
-- Track A.1 because we can hand-construct an s₀ satisfying
-- `InitialGuardUnlocked` and apply the hypothesis to `daoAttackTrace`.
-- This wall is now machine-checked.
#print axioms QanaryContracts.s₀_initial_satisfies_initialGuardUnlocked
-- hypothesis_H_v2_is_still_inconsistent: DELETED Phase 4 Session 6
-- (Track A.2 RTO cascade made its proof fail to typecheck — the
-- former proof built RTO from just InitialGuardUnlocked, which
-- is now insufficient under the five-conjunct RTO body)

-- Phase 4 Session 4 (2026-04-27, Decisions 1+2) — Theorem 4
-- (CEI/OZ incompatibility) machine-checked + OZGuardDiscipline
-- witness lemmas. Theorem 5 statement is `oz_guard_prevents_reentrancy_target`,
-- a `def : Prop` (no theorem claim yet — substantive proof is
-- Session 5+ work, gated by Vacuity Re-Verification Protocol).
#print axioms QanaryContracts.ozWitnessFunction_isOZGuarded
#print axioms QanaryContracts.ozWitnessContract_OZGuardDiscipline
#print axioms QanaryContracts.ozWitnessTrace_validExecution
#print axioms QanaryContracts.ozWitnessTrace_violates_cei
#print axioms QanaryContracts.cei_oz_incompatible

-- theorem5_falsified_by_arbitrary_a: DELETED Phase 4 Session 6
-- (Track A.2 cascade closed the wall it documented — the
-- previous witness no longer constructs under
-- ReentrancyVulnerableStatefulOn + new ReachableTraceOf).

-- Phase 4 Session 7.1 (2026-04-27/28, post-Session-7-wall) — W3 wall:
-- the Session-6 RTO with `callee ≠ C.address`-restricted call-locked
-- conjunct admits a self-unlock-reentry attack. Fix A in
-- Reachability.lean closes the gap; the wall is preserved as a
-- named theorem (parallel to W2 = `stateless_trace_breaks_naive_strategy`).
#print axioms QanaryContracts.w3_guard_at_0
#print axioms QanaryContracts.w3_guard_at_3
#print axioms QanaryContracts.w3ReentrantTrace_validExecution
#print axioms QanaryContracts.w3ReentrantTrace_traceEntryRevert
#print axioms QanaryContracts.w3ReentrantTrace_traceCCallLocked_weak
#print axioms QanaryContracts.w3ReentrantTrace_traceCFrameStartsWithLock
#print axioms QanaryContracts.w3ReentrantTrace_in_weak_RTO
#print axioms QanaryContracts.w3ReentrantTrace_is_self_unlock_reentry
#print axioms QanaryContracts.weak_rto_admits_self_unlock_reentry

-- Phase 4 Session 7.2 (2026-04-28) — slot-stability infrastructure +
-- self-call exclusion lemma.
#print axioms QanaryContracts.slot_unchanged_by_non_sstore
#print axioms QanaryContracts.slot_stable_no_sstore
#print axioms QanaryContracts.no_self_call_under_RTO

-- Phase 4 Session 7.3 (2026-04-28) — step-evolution helpers for
-- currentFrameAt / frameDepthAt / slotAt.
#print axioms QanaryContracts.currentFrameAt_after_call
#print axioms QanaryContracts.currentFrameAt_after_sstore
#print axioms QanaryContracts.frameDepthAt_after_call
#print axioms QanaryContracts.frameDepthAt_after_ret
#print axioms QanaryContracts.frameDepthAt_after_revert
#print axioms QanaryContracts.frameDepthAt_after_sstore
#print axioms QanaryContracts.guardSlotAt_after_non_sstore

-- Phase 4 Session 7.4 (2026-04-28) — stackAt foundation + iff lemmas
-- + combined inductive invariant + Theorem 5 (main soundness).
#print axioms QanaryContracts.stackAt_after_call
#print axioms QanaryContracts.stackAt_after_ret
#print axioms QanaryContracts.stackAt_after_revert
#print axioms QanaryContracts.stackAt_after_sstore
#print axioms QanaryContracts.currentFrameAt_eq_head_stackAt
#print axioms QanaryContracts.frameDepthAt_eq_length_stackAt
#print axioms QanaryContracts.oz_invariant_holds
#print axioms QanaryContracts.guard_locked_during_call
#print axioms QanaryContracts.oz_guard_prevents_reentrancy

-- Phase 5 Session 2 (2026-04-28) — Theorem 5* (`reentrancy_free_universal`).
-- Path α / Step 0 / γ′: drops the unused OZGuardDiscipline hypothesis from
-- Theorem 5; audit baseline must show the same kernel-axiom profile as
-- Theorem 5 itself (Theorem 5 now delegates to this).
#print axioms QanaryContracts.reentrancy_free_universal

-- Phase 5 Session 4 (2026-04-28) — W4 wall.
-- Q-VRVP2-1 strengthening of IsOZGuardedFunction with
-- NoSStoreOnGuardSlotInSteps on pre/post; the adversarial body that
-- satisfied the Phase-4-Session-6 definition fails the strengthened
-- version. Caught by VRVP-2 before BodyTraceLift.lean code was written.
#print axioms QanaryContracts.adversarial_body_fails_strengthened_oz

-- Phase 5 Session 10 (2026-05-02) — W8 wall mechanization.
-- The phantom-CALL counter-example from Session 9 paper-and-pencil
-- analysis is now machine-checked. The headline negation theorem
-- demonstrates that `ozGuardDiscipline_implies_RTO`'s currently-stated
-- universal claim is FALSE. See QanaryContracts/W8.lean.
#print axioms QanaryContracts.phantomCallTrace_validExecution
#print axioms QanaryContracts.phantom_matchesBody_at_0_6
#print axioms QanaryContracts.phantom_executes_C
#print axioms QanaryContracts.phantom_slot_at_6_eq_unlockedValue
#print axioms QanaryContracts.phantom_violates_TraceCCallLocked
#print axioms QanaryContracts.ozGuardDiscipline_implies_RTO_is_unprovable_as_stated

-- Phase 5 Session 11 (2026-05-02) — W8 P3 resolution: F4 LIFT THEOREM
-- LAYER 4 CLOSURE.
-- ozGuardDiscipline_implies_RTO now closes universally given the
-- NoPhantomCalls antecedent. This is the load-bearing certificate-shape
-- audit: the F4 lift theorem must show only kernel axioms, no sorryAx.
-- The NoPhantomCalls hypothesis is mechanically discharged at deployment
-- time per Layer 6 P4 work.
#print axioms QanaryContracts.ozGuardDiscipline_implies_RTO

-- Phase 5 Session 13 Unit 2 (2026-05-02) — Layer 5 Completeness foundation.
-- Vacuous foundational sub-case `no_functions_implies_RFG` per Option B
-- (HS-COMPLETENESS-CAP adjudication: substantive `no_external_calls_implies_RFG`
-- deferred to Sessions 14-21 because it needs general-frame stack-history
-- primitives developed during F2 multi-call work). The kernel-only axiom
-- record on this theorem is the foundation that the four substantive
-- sub-cases (NoExternalCalls, NoSStores, SatisfiesCEI_AllPaths,
-- OZGuardConfig) and the disjunction theorem `oz_completeness_full` will
-- match in Sessions 14-30.
#print axioms QanaryContracts.no_functions_implies_RFG

-- Phase 5 Session 15 Unit 3 (2026-05-03) — F2-B sub-block β-1 foundation.
-- Two F2-B β-1 theorems gated against axiom drift on every commit.
-- Both theorems have axiom records strictly narrower than the canonical
-- kernel triple [propext, Classical.choice, Quot.sound] used by the four
-- post-Layer-4 / Layer 5 headline theorems above:
--
--   * original_is_general_subset: depends on [propext] only.
--   * f2b_inherits_W4_strengthening: depends on no axioms at all.
--
-- The CI workflow's separate "Verify F2-B β-1 theorem axiom records"
-- step (`.github/workflows/build.yml`) checks each against its
-- per-theorem expected record rather than the canonical triple.
-- Methodology load-bearing claim ("explicit trusted base") extended:
-- both theorems remain within the kernel-only allowlist.
#print axioms QanaryContracts.original_is_general_subset
#print axioms QanaryContracts.f2b_inherits_W4_strengthening

-- Phase 5 Session 17 Unit 4 (2026-05-04) — F2-B sub-block β-2-and-β-3
-- merged foundation. Two new theorems added against the generalized
-- discipline:
--
--   * OZGuardDiscipline_implies_general: depends on [propext] only.
--     Extends Session 15 Unit 3's per-theorem (subset-of-kernel)
--     audit section.
--   * oz_guard_prevents_reentrancy_general: depends on the canonical
--     kernel triple [propext, Classical.choice, Quot.sound] —
--     propagated from reentrancy_free_universal via direct
--     delegation. Matches the original oz_guard_prevents_reentrancy's
--     record exactly. Extends the Session 13 Unit 3 canonical-triple
--     audit array.
--
-- Per an internal VRVP methodology note §4 prediction:
-- best-case ([propext]) for the implication lemma confirmed at
-- runtime. Methodology load-bearing claim ("explicit trusted base")
-- extended to cover sub-block β-2-and-β-3 merged foundation.
#print axioms QanaryContracts.OZGuardDiscipline_implies_general
#print axioms QanaryContracts.oz_guard_prevents_reentrancy_general

-- Phase 5 Session 19 (2026-05-04) — F2-B sub-block γ-1: BodyShape
-- propagation lemmas. Six new `_general` variants in BodyShape.lean
-- accepting IsOZGuardedFunctionGeneral. Co-exist with the original
-- Category 3 lemmas (BodyShape.lean:80, 390, 420, 453); coexistence
-- discipline preserved.
--
-- Axiom records discovered at runtime:
--
--   * unfoldBody_countP_isUnlockStep_eq_one_general    : [propext]
--   * unfoldBody_countP_isLockStep_eq_one_general      : [propext]
--   * matchesBody_implies_tr_kplus1_eq_lock_general    : canonical triple
--   * lock_position_unique_in_C_frame_general          : canonical triple
--   * unlock_position_unique_in_C_frame_general        : canonical triple
--   * guard_sstore_value_in_C_frame_general            : [propext, Quot.sound]
--
-- All within the kernel-only allowlist. Each MATCHES the corresponding
-- original lemma's record exactly (where a corresponding original
-- exists; the two helpers are BodyShape-local path-(α) variants
-- without direct originals in BodyShape itself, but match their
-- Layer-4 source lemmas' records).
--
-- Per PROCEED-3 path-(α) extension: helpers 2a (lock-counting) and 2b
-- (kplus1-eq-lock) are BodyShape-local duplicates of CountHelpers /
-- Executes lemmas, captured as deferred-housekeeping architectural
-- debt. CI gates protect the helpers' axiom records identically to
-- the main lemmas.
#print axioms QanaryContracts.unfoldBody_countP_isUnlockStep_eq_one_general
#print axioms QanaryContracts.unfoldBody_countP_isLockStep_eq_one_general
#print axioms QanaryContracts.matchesBody_implies_tr_kplus1_eq_lock_general
#print axioms QanaryContracts.lock_position_unique_in_C_frame_general
#print axioms QanaryContracts.unlock_position_unique_in_C_frame_general
#print axioms QanaryContracts.guard_sstore_value_in_C_frame_general

-- Phase 5 Sessions 21-22 (2026-05-03 / 04) — F2-B sub-block γ-2 closure
-- (γ-2 + γ-2-residual). Four new `_general` artifacts complete the W9
-- closure stack at the body-shape extraction layer, allowing
-- `IsOZGuardedFunctionGeneral`-typed reasoning to traverse from
-- function-body decomposition through to trace-level guard-locked-during-
-- body-call claims.
--
-- Axiom records discovered at runtime:
--
--   * matchesBody_oz_extracts_positions_general              : canonical triple
--   * unfoldBody_get?_unlock_general                         : canonical triple
--   * cFrameProjection_length_eq_pos_length                  : [propext, Quot.sound]
--   * executes_C_guard_locked_during_body_call_general       : canonical triple
--
-- All within the kernel-only allowlist. The three canonical-triple
-- artifacts gate alongside the headline list; the intermediate one
-- (cFrameProjection_length_eq_pos_length, M-22.2-candidate's "index-bound-
-- only" tactic category) gates alongside guard_sstore_value_in_C_frame_general.
--
-- Session 21 produced M_general (matchesBody_oz_extracts_positions_general)
-- and L_general (unfoldBody_get?_unlock_general), both as scope-restricted
-- variants per Option (iii) of the W9 reconnaissance. Session 22 Unit 1
-- produced cFrameProjection_length_eq_pos_length (path-(α) hoisted-helper
-- variant — architectural addition closing the glue-fact gap identified
-- at Session 21 Unit 3 fallback). Session 22 Unit 2 produced Site 3_general
-- (executes_C_guard_locked_during_body_call_general) consuming the helper
-- to close the γ-2-residual scope cleanly.
--
-- γ closure marker: with these four artifacts the W9 wall is closed at
-- the body-shape layer; IsOZGuardedFunctionGeneral now traverses
-- end-to-end from predicate definition (Session 15) through body-shape
-- extraction (γ-1, γ-2) to trace-level lemmas (γ-2-residual). Original
-- constructs preserved unchanged per Interpretation B (coexistence).
#print axioms QanaryContracts.matchesBody_oz_extracts_positions_general
#print axioms QanaryContracts.unfoldBody_get?_unlock_general
#print axioms QanaryContracts.cFrameProjection_length_eq_pos_length
#print axioms QanaryContracts.executes_C_guard_locked_during_body_call_general

-- Phase 5 Session 25 (2026-05-03) — F2-B sub-block delta-1 closure.
-- Two new `_general` artifacts complete the body-to-trace lift under
-- OZGuardDisciplineGeneral, threading IsOZGuardedFunctionGeneral
-- end-to-end from body-shape extraction (gamma-1 / gamma-2) to the
-- F4 lift theorem itself.
--
-- Axiom records discovered at runtime:
--
--   * executes_C_guard_unlocked_at_entry_general   : canonical triple
--   * ozGuardDiscipline_implies_RTO_general        : canonical triple
--
-- Both within the kernel-only allowlist. Matching M-22.2 Tier 3
-- prediction (existential-bearing tactics with trace projection
-- destructuring + classical for Nat.findGreatest decidability +
-- L2_general / Site 3_general composition).
--
-- L2_general (executes_C_guard_unlocked_at_entry_general) is Unit 1's
-- mechanical adaptation of L2 (line 177) consuming Sessions 19-22
-- _general variants + S19 path-(alpha) helpers + cFrameProjection_countP
-- _ge_two as a predicate-free counting helper. Used by F4 lift_general
-- at Conjunct 3.
--
-- F4 lift_general (ozGuardDiscipline_implies_RTO_general) is Unit 2's
-- six-category adjustment of F4 lift (line 706) composing through
-- L2_general (Conjunct 3) + Site 3_general (Conjunct 4) + 4-component
-- IsOZGuardedFunctionGeneral destructure with 3-segment body shape
-- (Conjunct 5). Original F4 lift preserved unchanged per Interpretation
-- B coexistence; F4 lift_general delivers the multi-CALL extension that
-- Layer 5's general completeness theorem will quantify over.
--
-- delta-1 closure marker: with these two artifacts the F4 lift layer is
-- closed under OZGuardDisciplineGeneral; original F4 lift (line 706) and
-- F4 lift_general coexist; downstream Layer 5 / Layer 6 work can compose
-- against either depending on the consumer's predicate hypothesis.
#print axioms QanaryContracts.executes_C_guard_unlocked_at_entry_general
#print axioms QanaryContracts.ozGuardDiscipline_implies_RTO_general

-- Phase 5 Session 27 (2026-05-03) — F2 CLOSURE. Sub-block δ-2 substantive.
-- The substantive `no_external_calls_implies_RFG` sub-case for
-- ReentrancyFreeGeneral is proven for contracts whose declared functions
-- contain no Step.call (Option A formulation). The proof is the F2
-- closure work: the universal soundness theorem for the multi-CALL
-- setting is structurally complete — predicate (Sessions 14-15), body-
-- shape soundness (Sessions 17-22), body-to-trace lift (Session 25),
-- substantive completeness sub-case (this session).
--
-- Axiom record discovered at runtime:
--
--   * no_external_calls_implies_RFG : canonical kernel triple
--
-- Within the kernel-only allowlist. Matching M-22.2 Tier 3 prediction
-- (existential-bearing tactics with trace projection destructuring +
-- Mathlib List infrastructure threading via cFrameProjection-via-
-- MatchesBody body-step identification).
--
-- INFRASTRUCTURE-BYPASS: this proof uses operational stack-history
-- infrastructure (frameDepthAt, currentFrameAt, NestedAfter,
-- CallsFromTopFrame) plus cFrameProjection-via-MatchesBody — NOT the
-- W9-closed _general surface (Sessions 19-22) and NOT the F4 lift
-- layer (Session 25). F2-B completeness sub-cases compose with body-
-- shape soundness through the eventual oz_completeness_full
-- disjunction theorem but do not depend on the body-shape _general
-- infrastructure for their internal reasoning. Architectural
-- cleanliness preserved.
--
-- F2 closure marker: with this artifact, F2 is structurally complete.
-- Original no_functions_implies_RFG (vacuous foundation, Session 13),
-- ReentrancyFreeGeneral predicate, NoFunctions predicate, NoExternalCalls
-- predicate (Unit 1) all preserved alongside the substantive theorem.
-- Remaining sub-cases (NoSStores, SatisfiesCEI_AllPaths, OZGuardConfig)
-- and the disjunction theorem oz_completeness_full are post-F2 / Layer 6
-- instantiation work per program trajectory.
#print axioms QanaryContracts.no_external_calls_implies_RFG

-- Phase 5 Session 32 (Layer 6-A Phase 3 closure): DAO negative-instance
-- falsification. Units 2/3 zero-axiom; Unit 4 master [propext]-only.
-- CI gating deferred to Session 35 Phase 6 per directive Part 14.
#print axioms QanaryContracts.OZGuardDisciplineGeneral_falsified_at_withdrawRewardFor
#print axioms QanaryContracts.OZGuardDisciplineGeneral_falsified_at_splitDAO
#print axioms QanaryContracts.daoContract_violates_OZGuardDisciplineGeneral

-- Phase 5 Session 33 (Layer 6-A Phase 4 closure): negative-instance
-- certificate's discriminating-power claim. All three new theorems
-- carry [propext]-only axiom records (M-22.2 Tier 1). CI gating
-- defers to Session 35 Phase 6 per Session 32 Unit 4 Option (β) precedent.
#print axioms QanaryContracts.daoContract_predicate_rejected_at_Phase4
#print axioms QanaryContracts.daoAttackTrace_vulnerability_witness_at_Phase4
#print axioms QanaryContracts.daoContract_negative_instance_certificate

-- Phase 5 Session 38 (Layer 6-B Phase 3-4 compressed closure):
-- Compound positive-instance certificate. All three theorems carry
-- [propext]-only axiom records (M-22.2 Tier 1 wrapper-layer absorption,
-- third bidirectional empirical instance after Layer 6-A Phase 3 master
-- and Phase 4 meta-theorem). CI gating at parallel
-- `Verify Layer 6-B theorem axiom records` block per Question 6d
-- Option (2) + Naming (a) per-layer scope convention.
#print axioms QanaryContracts.compoundContract_satisfies_OZGuardDisciplineGeneral
#print axioms QanaryContracts.compoundContract_predicate_accepted_at_PhaseY
#print axioms QanaryContracts.compoundContract_positive_instance_certificate
