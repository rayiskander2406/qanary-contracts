/-
  QanaryContracts/CEISufficiency.lean

  Phase 3 Session 3 — Theorem 2 (CEI sufficiency / soundness direction).

  Statement (verbatim from handoff):
      ∀ C : Contract,
        (∀ s₀ tr, ValidExecution tr → SatisfiesCEI tr) →
        ReentrancyFree C

  ******************** HONEST WALL — READ FIRST ********************

  Per Ray's 2026-04-27 directive ("An honest wall is better than a
  wrong proof"), this file documents a structural gap surfaced
  during the proof attempt. Full analysis: an internal phase report.
  Summary in three points:

  (W1) The hypothesis quantifies over ALL traces, not over `C`'s
       reachable executions. It is a global property of the trace
       universe, not a property of `C`. In our model the
       hypothesis is provably FALSE, witnessed by `daoAttackTrace`
       (a `ValidExecution` that violates CEI). The implication is
       therefore vacuously true. The substantive soundness theorem
       must restrict the antecedent to `C`'s reachable traces and
       pair it with the OZ guard discipline (Phase 4 Session 1).

  (W2) Even ignoring (W1), the conjuncts
            ValidExecution tr  ∧  SatisfiesCEI tr
                                ∧  ReentrancyVulnerableStateful s₀ tr ...
       are *jointly satisfiable*. Concrete witness — six steps,
       zero SSTOREs:
            tr := [ call attacker victim 0,
                    call victim attacker 0,
                    call attacker victim 0,
                    ret true, ret true, ret true ]
            s₀ := EVMState.empty,  a := victim,  i := 0,  j := 2
       CEI vacuously true (no SSTORE step), call topology has the
       structural reentrancy pattern at (0, 2), and the guard slot
       reads as `Word256.zero` from the empty storage map (matching
       v3-style `unlockedValue = 0`). So at this abstraction level,
       SatisfiesCEI does NOT structurally exclude
       ReentrancyVulnerableStateful.

  (W3) The intended proof strategy ("CEI implies storage is fully
       updated before the CALL") is not supported by the current
       `SatisfiesCEI` predicate. CEI as encoded only ORDERS the
       SSTOREs that exist (no SSTORE-after-external-CALL in the
       same frame); it does NOT require any SSTORE to exist or any
       guard to be set. A guard-less contract is vacuously
       CEI-conformant but not necessarily reentrancy-safe.

  Conclusion: the soundness *content* of "CEI ⟹ no reentrancy"
  lives one level higher, paired with a guard-discipline hypothesis
  (Phase 4). This file proves the literal theorem as a vacuous
  corollary of `hypothesis_H_is_inconsistent`; the real Phase 4
  work is the contract-specific refinement.

  ********************* TECHNICAL NOTE *********************

  `ValidExecution` carries auto-derived `Decidable` instances, but
  the inner universal quantifiers over `Address` (= `Fin (2^160)`)
  and `Word256` (= `Fin (2^256)`) cause `decide` to recurse beyond
  the kernel budget and `native_decide` to stack-overflow during
  compilation. We therefore prove `ValidExecution daoAttackTrace`
  by manual case-split on trace position (`interval_cases`); the
  per-position residuals are tractable.

  ********************* DELIVERABLE STATUS *********************

      * helper lemmas about `daoAttackTrace`         — proved,
                                                       manual
                                                       (decide /
                                                       interval_cases)
      * `daoAttackTrace_validExecution`              — proved
      * `daoAttackTrace_violates_cei`                — proved,
                                                       native_decide
      * `hypothesis_H_is_inconsistent`               — proved
      * `cei_implies_no_reentrancy` (vacuous)        — proved
      * zero `sorry`, zero project axioms

  See an internal phase report for the full wall analysis,
  proposed theorem-statement refinements, and Session 3.2 entry
  conditions.
-/
import QanaryContracts.EVM
import QanaryContracts.Storage
import QanaryContracts.Step
import QanaryContracts.Reentrancy
import QanaryContracts.CEI
import QanaryContracts.Contract
import QanaryContracts.ValidExecution
import QanaryContracts.ReentrancyFree
import QanaryContracts.DAOAttack
import QanaryContracts.MultiFunction
import Mathlib.Tactic.IntervalCases

namespace QanaryContracts

/-! ## Per-conjunct ValidExecution lemmas on `daoAttackTrace`

The auto-derived `Decidable` instance for the conjuncts uses
`∀ addr : Address, ...` — and Address is `Fin (2^160)` — which blows
out the kernel recursion budget for `decide` and stack-overflows
`native_decide`. We therefore prove each conjunct manually:
case-split on the trace position (`interval_cases`), simplify the
hypothesis with `simp [daoAttackTrace]`, and discharge the residuals
with `decide` (which works on the now-position-specific Fin and
Address comparisons).
-/

/-- Every SSTORE in `daoAttackTrace` targets the currently-executing
    contract's storage. The only SSTORE in the trace is at index 7
    (`sstore daoVictim 0 0`); after steps 0–6 the call stack is
    `[daoVictim]`, so `currentFrameAt = some daoVictim` matches. -/
theorem daoAttackTrace_sstores_in_own_frame :
    SStoresInOwnFrame daoAttackTrace := by
  intro ⟨k, hk⟩ addr key val hstep
  have hk9 : k < 9 := hk
  show currentFrameAt daoAttackTrace k = some addr
  interval_cases k
  all_goals simp [daoAttackTrace] at hstep
  obtain ⟨rfl, _, _⟩ := hstep
  decide

/-- Every CALL in `daoAttackTrace` issues from the currently-executing
    contract (or from outside any frame, for the initial entry). The
    four CALLs are at indices 0, 1, 2, 3; per-position frames match
    the caller fields. -/
theorem daoAttackTrace_calls_from_top_frame :
    CallsFromTopFrame daoAttackTrace := by
  intro ⟨k, hk⟩ caller callee value hstep
  have hk9 : k < 9 := hk
  show currentFrameAt daoAttackTrace k = some caller ∨
       currentFrameAt daoAttackTrace k = none
  interval_cases k
  all_goals (
    simp [daoAttackTrace] at hstep
    try (obtain ⟨rfl, rfl, rfl⟩ := hstep))
  all_goals decide

/-- The `daoAttackTrace` call stack never goes below depth 0
    (no orphan RET/REVERT). Per-position depths are
    `0, 1, 2, 3, 4, 3, 2, 1, 1`, all nonnegative. -/
theorem daoAttackTrace_balanced_frames :
    BalancedFrames daoAttackTrace := by
  intro ⟨k, hk⟩
  have hk9 : k < 9 := hk
  show frameDepthAt daoAttackTrace k ≥ 0
  interval_cases k <;> decide

/-- The DAO attack trace is a valid EVM execution. -/
theorem daoAttackTrace_validExecution : ValidExecution daoAttackTrace :=
  ⟨daoAttackTrace_sstores_in_own_frame,
   daoAttackTrace_calls_from_top_frame,
   daoAttackTrace_balanced_frames⟩

/-- The DAO attack trace does NOT satisfy CEI. (Index pair `(1, 7)`
    witnesses: step 1 is `call victim → attacker` from victim's frame;
    step 7 is `sstore daoVictim 0 0` in victim's frame — i.e. an
    SSTORE on victim's storage AFTER an external call from victim.) -/
theorem daoAttackTrace_violates_cei : ¬ SatisfiesCEI daoAttackTrace := by
  native_decide

/-! ## The wall, formalized -/

/-- The universal CEI hypothesis is logically inconsistent in the
    QANARY model. Witness: `daoAttackTrace` is a `ValidExecution`
    that does not satisfy CEI, so any function from valid traces to
    CEI-satisfaction would have to map daoAttackTrace to both
    `SatisfiesCEI daoAttackTrace` (by application) and to the
    impossible (by `daoAttackTrace_violates_cei`).

    Significance: this is the substantive content of the file. Any
    theorem of the form `H → P` where `H` is this universal
    hypothesis is vacuously true. The Phase 4 soundness theorem
    must use a contract-specific reachability hypothesis, not this
    global one. -/
theorem hypothesis_H_is_inconsistent :
    ¬ (∀ (_s₀ : EVMState) (tr : ExecutionTrace),
         ValidExecution tr → SatisfiesCEI tr) := by
  intro hAll
  exact daoAttackTrace_violates_cei
    (hAll EVMState.empty daoAttackTrace daoAttackTrace_validExecution)

/-! ## Theorem 2 — vacuous

The literal theorem from the handoff. The proof reduces to
`hypothesis_H_is_inconsistent`: the antecedent is impossible, so
the implication holds.

This is the *correct* Lean proof of the *literal* statement. It is
NOT the substantive soundness theorem the paper will claim — that
theorem (Phase 4 Session 1) replaces the universal CEI hypothesis
with a contract-specific guard-discipline hypothesis (every reachable
trace of `C` satisfies CEI *and* `C`'s guard slot is set before any
external call). The Phase 4 statement is mathematically rich; this
Phase 3 statement is logical scaffolding.
-/

/-- **Theorem 2 (CEI sufficiency, literal form).** If every valid
    execution satisfies CEI, then every contract is reentrancy-free.

    Vacuously true: the antecedent contradicts
    `hypothesis_H_is_inconsistent`. The substantive soundness
    theorem — `cei_implies_no_reentrancy_for_reachable_traces_of C`
    — is a Phase 4 deliverable that strengthens the antecedent to
    range only over `C`'s reachable traces and pairs it with the OZ
    guard discipline.

    **Do NOT cite this theorem as the paper's soundness result.**
    It exists to satisfy the handoff's literal Phase 3 deliverable
    and to make the wall (W1)–(W3) machine-checked. -/
theorem cei_implies_no_reentrancy (C : Contract) :
    (∀ (_s₀ : EVMState) (tr : ExecutionTrace),
       ValidExecution tr → SatisfiesCEI tr) →
    ReentrancyFree C := by
  intro hAll
  exact absurd hAll hypothesis_H_is_inconsistent

/-! ## W2 counter-example, machine-checked

Per Ray (2026-04-27, Decision 2): "the counter-example shows the
model is precise enough to detect when a proof strategy is wrong.
That is a feature not a bug." This section formalizes the W2
counter-example from the Phase 3 Session 3 report.

We construct a six-step stateless trace where:
  * `ValidExecution` holds (manual proof, same `interval_cases`
    pattern as `daoAttackTrace_validExecution`)
  * `SatisfiesCEI` holds (vacuously — no SSTORE step exists, so
    `CEIViolated` is `False` everywhere; closes by `native_decide`)
  * `ReentrancyVulnerableStateful` holds with `s₀ = EVMState.empty`,
    `a = daoVictim`, `i = 0`, `j = 2` and v3-style `ozUnlockedValue`
    (= `Word256.zero`); witnessed explicitly

The conjunction `stateless_trace_breaks_naive_strategy` rules out
the user's intended strategy ("CEI ⟹ guard locked at the reentry
point") at the abstraction level the current predicates encode.
The substantive Phase 4 soundness theorem must use a stronger
hypothesis (contract-reachable traces + OZ guard discipline).
-/

/-- The W2 counter-example trace: three CALLs forming a
    structural reentrancy pattern, three RETs, zero SSTOREs.
    A guard-less, stateless contract topology. -/
def statelessReentrancyTrace : ExecutionTrace := [
  /- 0 -/ EVMStep.call daoAttacker daoVictim daoValue,
  /- 1 -/ EVMStep.call daoVictim daoAttacker daoValue,
  /- 2 -/ EVMStep.call daoAttacker daoVictim daoValue,  -- REENTRANT
  /- 3 -/ EVMStep.ret true,
  /- 4 -/ EVMStep.ret true,
  /- 5 -/ EVMStep.ret true
]

/-- The stateless trace has no SSTOREs, so `SStoresInOwnFrame` holds
    vacuously: `simp` closes every position because no `tr[k]?` matches
    the `EVMStep.sstore _ _ _` pattern. -/
theorem statelessReentrancyTrace_sstores_in_own_frame :
    SStoresInOwnFrame statelessReentrancyTrace := by
  intro ⟨k, hk⟩ addr key val hstep
  have hk6 : k < 6 := hk
  show currentFrameAt statelessReentrancyTrace k = some addr
  interval_cases k <;> simp [statelessReentrancyTrace] at hstep

/-- CALLs at positions 0–2 issue from frames matching their `caller`
    fields (or from outside any frame, for position 0). RETs at
    positions 3–5 vacuously satisfy the constraint. -/
theorem statelessReentrancyTrace_calls_from_top_frame :
    CallsFromTopFrame statelessReentrancyTrace := by
  intro ⟨k, hk⟩ caller callee value hstep
  have hk6 : k < 6 := hk
  show currentFrameAt statelessReentrancyTrace k = some caller ∨
       currentFrameAt statelessReentrancyTrace k = none
  interval_cases k
  all_goals (
    simp [statelessReentrancyTrace] at hstep
    try (obtain ⟨rfl, rfl, rfl⟩ := hstep))
  all_goals decide

/-- Per-position depths: `0, 1, 2, 3, 2, 1` — all nonnegative. -/
theorem statelessReentrancyTrace_balanced_frames :
    BalancedFrames statelessReentrancyTrace := by
  intro ⟨k, hk⟩
  have hk6 : k < 6 := hk
  show frameDepthAt statelessReentrancyTrace k ≥ 0
  interval_cases k <;> decide

theorem statelessReentrancyTrace_validExecution :
    ValidExecution statelessReentrancyTrace :=
  ⟨statelessReentrancyTrace_sstores_in_own_frame,
   statelessReentrancyTrace_calls_from_top_frame,
   statelessReentrancyTrace_balanced_frames⟩

/-- The stateless trace has zero SSTORE steps, so the antecedent of
    `CEIViolated` (`tr[j]? = some (.sstore ...)`) is `False` for every
    `j`, and the universal predicate `SatisfiesCEI` is vacuously true. -/
theorem statelessReentrancyTrace_satisfies_cei :
    SatisfiesCEI statelessReentrancyTrace := by
  native_decide

/-- The stateless trace exhibits state-aware reentrancy: two CALLs
    targeting `daoVictim` with the second nested in the first's open
    frame; the guard slot at `daoVictim` reads as `Word256.zero` from
    the empty initial storage, matching `ozUnlockedValue = 0`
    (v3-style). Witness: `(a, i, j) = (daoVictim, 0, 2)`. -/
theorem statelessReentrancyTrace_is_reentrancy_vulnerable :
    ReentrancyVulnerableStateful EVMState.empty statelessReentrancyTrace
      ozGuardSlot ozUnlockedValue := by
  refine ⟨daoVictim, 0, 2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide                                      -- 0 < 2
  · decide                                      -- 2 < 6
  · exact ⟨daoAttacker, daoValue, rfl⟩          -- tr[0]? = some (call _ daoVictim _)
  · exact ⟨daoAttacker, daoValue, rfl⟩          -- tr[2]? = some (call _ daoVictim _)
  · decide                                      -- NestedAfter 0 2
  · native_decide                               -- guardSlotAt = unlockedValue (both = 0)

/-- **The W2 wall, machine-checked.** A single trace simultaneously
    satisfies `ValidExecution`, `SatisfiesCEI`, AND
    `ReentrancyVulnerableStateful`. This rules out — at the current
    abstraction level — any proof strategy that tries to derive a
    contradiction from the conjunction of these three predicates
    alone. The substantive Phase 4 soundness theorem must therefore
    strengthen the hypothesis (contract-reachable traces + OZ guard
    discipline), not the conclusion. -/
theorem stateless_trace_breaks_naive_strategy :
    ValidExecution statelessReentrancyTrace ∧
    SatisfiesCEI statelessReentrancyTrace ∧
    ReentrancyVulnerableStateful EVMState.empty statelessReentrancyTrace
      ozGuardSlot ozUnlockedValue :=
  ⟨statelessReentrancyTrace_validExecution,
   statelessReentrancyTrace_satisfies_cei,
   statelessReentrancyTrace_is_reentrancy_vulnerable⟩

end QanaryContracts
