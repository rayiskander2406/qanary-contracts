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
