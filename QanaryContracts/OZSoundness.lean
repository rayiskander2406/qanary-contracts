/-
  QanaryContracts/OZSoundness.lean

  Phase 4 Session 4 — OpenZeppelin guard discipline + the v3
  soundness theorem statement (per Ray's 2026-04-27 Decision 1):

      theorem oz_guard_prevents_reentrancy
          (C : Contract) (h : OZGuardDiscipline C) :
          ReentrancyFree C

  This is the paper's Theorem 5 (main soundness result). It avoids
  the CEI/OZ incompatibility wall by hypothesizing the OZ guard
  discipline directly, NOT a CEI hypothesis.

  Ray's framing: *"This is clean, direct, and corresponds to what
  the frozen claim actually says — soundness of OpenZeppelin's
  ReentrancyGuard. Not a CEI theorem that smuggles in the guard.
  A guard theorem directly."*

  This file also lands the paper's Theorem 4 — the
  CEI/OZ incompatibility — as a machine-checked existential.
  Ray's framing: *"The DeFi community conflates CEI and the OZ
  guard constantly. Every Solidity tutorial says 'use CEI or
  ReentrancyGuard.' The implication is they are equivalent. They
  are not. This paper proves it."*
-/
import QanaryContracts.EVM
import QanaryContracts.Storage
import QanaryContracts.Step
import QanaryContracts.Reentrancy
import QanaryContracts.CEI
import QanaryContracts.FunctionBody
import QanaryContracts.Contract
import QanaryContracts.ValidExecution
import QanaryContracts.ReentrancyFree
import QanaryContracts.Reachability
import QanaryContracts.DAOAttack
import QanaryContracts.CEISufficiency
import QanaryContracts.CEISufficiencyV2
import Mathlib.Tactic.IntervalCases

namespace QanaryContracts

/-! ## OZ guard discipline — predicate -/

/-- Predicate: a function-body step list contains no `.call` step.
    Used by tightened `IsOZGuardedFunction` to enforce the
    single-call constraint of Decision 5 (post-Session-4 round).
    Multi-call generalization is future work
    (the internal methodology notes § 8). -/
def NoCallInSteps (steps : List FunctionBody.Step) : Prop :=
  ∀ s ∈ steps, ¬ ∃ callee value, s = FunctionBody.Step.call callee value

/-- Predicate: a function-body step list contains no `.sstore` step
    targeting the given slot. Used by Phase 5 Session 4's
    strengthening of `IsOZGuardedFunction` (Q-VRVP2-1 confirmation,
    2026-04-28) to enforce the body-level guard-slot mutation
    invariant.

    Real OZ-decorated functions never SSTORE the guard slot mid-body
    — only at function entry (the mandatory lock SSTORE) and exit
    (the mandatory unlock SSTORE). Without this constraint,
    `IsOZGuardedFunction` admits adversarial bodies that lock at
    entry, then unlock mid-body via a pre-segment SSTORE, then issue
    the external CALL with the guard already unlocked — violating
    `TraceCCallLocked` at the trace level. The W4 wall
    (`adversarial_body_fails_strengthened_oz`) machine-checks the
    counter-example. -/
def NoSStoreOnGuardSlotInSteps (slot : Word256)
    (steps : List FunctionBody.Step) : Prop :=
  ∀ s ∈ steps, ¬ ∃ val, s = FunctionBody.Step.sstore slot val

/-- A function body follows the OpenZeppelin guard discipline iff
    its body has the shape

      [sstore guardSlot lockedValue] ++ pre
      ++ [call callee value]
      ++ post
      ++ [sstore guardSlot unlockedValue, ret true]

    where:
    * `callee ≠ C.address` (the call is external)
    * `pre` contains no `.call` steps (Decision 5 single-call
      constraint, Phase 4 Session 6 tightening)
    * `post` contains no `.call` steps (Decision 5)

    This is the canonical OZ pattern: lock the guard, do the
    protected work (with exactly ONE external call), unlock the
    guard, return.

    **Phase 4 Session 6 tightening:** the original (Session 4)
    definition allowed `pre`/`post` to contain arbitrary steps
    including additional `.call` steps. Per Decision 5, that
    implicitly violated the single-call scope. The tightened
    definition makes the single-call constraint explicit and
    enforceable.

    **Phase 5 Session 4 strengthening (Q-VRVP2-1, 2026-04-28):** the
    Phase 4 Session 6 definition still allowed `pre`/`post` to
    contain `.sstore` steps targeting the guard slot itself, admitting
    an adversarial body that unlocks mid-body and fires the external
    CALL with the guard unlocked (W4 wall, machine-checked as
    `adversarial_body_fails_strengthened_oz`). The strengthened
    definition adds `NoSStoreOnGuardSlotInSteps C.guardSlot pre/post`,
    matching real-world OZ behavior (production OZ-decorated functions
    never SSTORE the guard slot mid-body) and closing the F4 lift's
    Conjunct-4 sub-case.

    The model intentionally ignores conditional revert-if-locked
    entry checks at this layer; that constraint enters via the
    trace-level `ReachableTraceOf` predicate (`TraceEntryRevert` +
    `TraceCFrameStartsWithLock` in `Reachability.lean`). -/
def IsOZGuardedFunction (C : Contract) (f : FunctionBody) : Prop :=
  ∃ (pre : List FunctionBody.Step) (callee : Address) (value : Word256)
    (post : List FunctionBody.Step),
      f = (FunctionBody.Step.sstore C.guardSlot C.lockedValue) ::
          (pre ++
            (FunctionBody.Step.call callee value) ::
            (post ++
              [FunctionBody.Step.sstore C.guardSlot C.unlockedValue,
               FunctionBody.Step.ret true]))
      ∧ callee ≠ C.address
      ∧ NoCallInSteps pre
      ∧ NoCallInSteps post
      ∧ NoSStoreOnGuardSlotInSteps C.guardSlot pre
      ∧ NoSStoreOnGuardSlotInSteps C.guardSlot post

/-- A contract `C` follows the OZ guard discipline iff every
    declared function body is OZ-guarded (and `C.functions` is
    non-empty — a guard discipline on zero functions is a vacuous
    label). -/
def OZGuardDiscipline (C : Contract) : Prop :=
  C.functions ≠ [] ∧ ∀ f ∈ C.functions, IsOZGuardedFunction C f

/-! ## F2-B (Phase 5 Session 15) — generalized OZ-guarded predicate

The single-call constraint of `IsOZGuardedFunction` (Phase 4 Session 6
Decision 5 tightening, line 124-125 above) excludes legitimate
multi-CALL OZ patterns: batched withdrawals, multi-step settlements,
nested CALLs. Per Session 14's design enumeration
(an internal methodology note) and design-level VRVP stress-test
(an internal VRVP methodology note), candidate **F2-B (single guard span)**
survives soundness VRVP and provides the cleanest generalization
path: drop the segmentation-around-the-CALL framing, admit arbitrary
CALLs in body, retain the W4 strengthening
(`NoSStoreOnGuardSlotInSteps body`) and lift the per-CALL
self-call exclusion (`NoCallToSelfInSteps body`).

This section lands the F2-B predicate definition and the subset
lemma `original_is_general_subset` (paper §4 content). The original
`IsOZGuardedFunction` is preserved unchanged; coexistence is the
sub-block β-1 discipline. Sub-block γ confirms infrastructure
composition before any rename / deprecation of the original.

VRVP at the precise Lean level
(an internal VRVP methodology note) verified the predicate's
soundness against three construction attempts matching Session 14's
design-level VRVP, and verified the F-API-3 self-call rejection
directly. -/

/-- Predicate: a function-body step list contains no `.call` step
    whose `callee` equals the given self-address. F2-B
    (Phase 5 Session 15) per-CALL self-call exclusion helper, parallel
    to `NoCallInSteps` and `NoSStoreOnGuardSlotInSteps`.

    The original `IsOZGuardedFunction` enforces `callee ≠ C.address`
    inline for its single CALL. F2-B's body may contain multiple
    CALLs; the constraint must hold for each, lifted to a list-level
    predicate. -/
def NoCallToSelfInSteps (selfAddr : Address)
    (steps : List FunctionBody.Step) : Prop :=
  ∀ s ∈ steps, ∀ callee value,
    s = FunctionBody.Step.call callee value → callee ≠ selfAddr

/-- F2-B generalized OZ-guarded function predicate (single guard span).

    A function body satisfies `IsOZGuardedFunctionGeneral` iff it has
    the shape

      [sstore guardSlot lockedValue] ++ body
        ++ [sstore guardSlot unlockedValue, ret true]

    where:

    * `body` may contain arbitrary `.call`, `.sstore` (other slots),
      `.ret`, `.revert` steps;
    * `body` contains no `.sstore` on the guard slot
      (`NoSStoreOnGuardSlotInSteps C.guardSlot body` — W4
      strengthening inherited);
    * every `.call` in `body` has `callee ≠ C.address`
      (`NoCallToSelfInSteps C.address body` — F2-B-specific
      per-CALL self-call exclusion).

    **Three load-bearing conjuncts:**

    1. *Body shape* (lock-prefix + body + `[unlock, ret true]` suffix):
       structural anchor; matches an internal methodology note §4.1.
    2. *No guard SSTOREs in body*: inherits Phase 5 Session 4 W4
       strengthening; closes the mid-body unlock attack
       (`adversarial_body_fails_strengthened_oz`).
    3. *No self-calls in body*: F2-B-specific addition over a naive
       multi-call generalization; preserves the original predicate's
       per-CALL `callee ≠ C.address` discipline. Documented as the
       handshake F-API-3 fix in
       an internal VRVP methodology note §4. Without this
       conjunct, the body `[lock, call C.address v, unlock, ret true]`
       would satisfy the structural and W4 conjuncts but
       statically permit a self-call inside the guard span,
       breaking the predicate's intended characterization of
       OZ-disciplined function bodies.

    **Coverage estimate (per design doc §4.6):** ~95% of production
    OpenZeppelin v5 `nonReentrant` usage. Acknowledged ~5% gap is
    pre-CALL guard reset patterns (excluded by W4 strengthening's
    `NoSStoreOnGuardSlotInSteps`); same gap as the original
    predicate. Scaffold §11 documents this as a known limitation.

    **Coexistence with original `IsOZGuardedFunction`:** the original
    is preserved unchanged through sub-block β-1. Sub-block γ
    propagates the generalized predicate through the three-family
    infrastructure (CountHelpers, StackHistory, BodyShape) before
    any rename / deprecation of the original. The
    `original_is_general_subset` lemma below documents the
    relationship explicitly. -/
def IsOZGuardedFunctionGeneral (C : Contract) (f : FunctionBody) : Prop :=
  ∃ (body : List FunctionBody.Step),
    f = (FunctionBody.Step.sstore C.guardSlot C.lockedValue) ::
        (body ++
          [FunctionBody.Step.sstore C.guardSlot C.unlockedValue,
           FunctionBody.Step.ret true])
    ∧ NoSStoreOnGuardSlotInSteps C.guardSlot body
    ∧ NoCallToSelfInSteps C.address body

/-- The original (Phase 4 Session 6 / Phase 5 Session 4) single-call
    `IsOZGuardedFunction` is a subset of the F2-B (Phase 5 Session 15)
    generalized `IsOZGuardedFunctionGeneral`.

    Take `body := pre ++ .call callee value :: post`. The body-shape
    equation matches by list associativity. The W4 invariant
    (`NoSStoreOnGuardSlotInSteps`) follows from the original's two
    `pre`/`post` invariants because the central `.call` step is not
    an SSTORE. The self-call exclusion (`NoCallToSelfInSteps`)
    follows because `pre` and `post` have `NoCallInSteps`
    (no calls at all there), and the central `.call` has
    `callee ≠ C.address` by hypothesis. -/
theorem original_is_general_subset (C : Contract) (f : FunctionBody)
    (h : IsOZGuardedFunction C f) :
    IsOZGuardedFunctionGeneral C f := by
  obtain ⟨pre, callee, value, post, h_eq, h_ext, h_no_call_pre,
          h_no_call_post, h_no_sstore_pre, h_no_sstore_post⟩ := h
  refine ⟨pre ++ FunctionBody.Step.call callee value :: post, ?_, ?_, ?_⟩
  · -- Body shape: equal up to list associativity.
    rw [h_eq]
    simp [List.append_assoc, List.cons_append]
  · -- NoSStoreOnGuardSlotInSteps on (pre ++ call :: post).
    intro s hs
    rw [List.mem_append, List.mem_cons] at hs
    rcases hs with hs_pre | rfl | hs_post
    · exact h_no_sstore_pre s hs_pre
    · -- s = .call callee value: not an .sstore.
      rintro ⟨_, h_call_eq⟩
      cases h_call_eq
    · exact h_no_sstore_post s hs_post
  · -- NoCallToSelfInSteps on (pre ++ call :: post).
    intro s hs callee' value' h_call
    rw [List.mem_append, List.mem_cons] at hs
    rcases hs with hs_pre | rfl | hs_post
    · exact (h_no_call_pre s hs_pre ⟨callee', value', h_call⟩).elim
    · -- s = .call callee value, h_call : .call callee value = .call callee' value'.
      simp only [FunctionBody.Step.call.injEq] at h_call
      obtain ⟨rfl, _⟩ := h_call
      exact h_ext
    · exact (h_no_call_post s hs_post ⟨callee', value', h_call⟩).elim

/-! ## Witness for Theorem 4 — a concrete OZ-disciplined contract
    + a concrete `ValidExecution` trace that violates `SatisfiesCEI`

The witness mechanically demonstrates that an OZ-disciplined
contract's execution trace contains a `lock-CALL-unlock` pattern
that violates CEI as encoded. Unlike Phase 3's `daoAttackTrace`
(which violates CEI because of an SSTORE-after-CALL bug, not by
design), this trace violates CEI BY DESIGN — the contract is
correctly using the OZ guard, and the guard's unlock SSTORE after
the external call is what trips CEI.

This is the paper's Theorem 4 (named result on
[CEI/OZ incompatibility](the internal methodology notes#7-cei-oz-incompatibility)).
-/

def ozWitnessAddress  : Address := ⟨10, by decide⟩
def ozWitnessGuardSlot : Word256 := ⟨7, by decide⟩
def ozWitnessCallee   : Address := ⟨11, by decide⟩
def ozWitnessUser     : Address := ⟨12, by decide⟩

/-- A single OZ-guarded function body: lock → external call → unlock → ret. -/
def ozWitnessFunction : FunctionBody :=
  [FunctionBody.Step.sstore ozWitnessGuardSlot ⟨2, by decide⟩,
   FunctionBody.Step.call ozWitnessCallee ⟨0, by decide⟩,
   FunctionBody.Step.sstore ozWitnessGuardSlot ⟨1, by decide⟩,
   FunctionBody.Step.ret true]

/-- A contract with a single OZ-guarded function. v4-style guard:
    `unlockedValue = 1` (`_NOT_ENTERED`), `lockedValue = 2` (`_ENTERED`). -/
def ozWitnessContract : Contract := {
  address       := ozWitnessAddress,
  guardSlot     := ozWitnessGuardSlot,
  unlockedValue := ⟨1, by decide⟩,
  lockedValue   := ⟨2, by decide⟩,
  functions     := [ozWitnessFunction]
}

/-- An execution trace of `ozWitnessContract` running its OZ-guarded
    function: external entry → lock → external call → callee returns
    → unlock → C returns. The lock and unlock SSTOREs are both in
    `ozWitnessAddress`'s frame; the unlock SSTORE happens AFTER the
    external CALL — exactly the CEI-violating pattern. -/
def ozWitnessTrace : ExecutionTrace := [
  /- 0 -/ EVMStep.call ozWitnessUser ozWitnessAddress ⟨0, by decide⟩,
  /- 1 -/ EVMStep.sstore ozWitnessAddress ozWitnessGuardSlot ⟨2, by decide⟩,
  /- 2 -/ EVMStep.call ozWitnessAddress ozWitnessCallee ⟨0, by decide⟩,
  /- 3 -/ EVMStep.ret true,
  /- 4 -/ EVMStep.sstore ozWitnessAddress ozWitnessGuardSlot ⟨1, by decide⟩,
  /- 5 -/ EVMStep.ret true
]

/-! ## Witness lemmas -/

/-- The witness function body is OZ-guarded. Take `pre = []`, `post = []`,
    `callee = ozWitnessCallee`, `value = ⟨0, _⟩`. The `NoCallInSteps`
    conjuncts (Phase 4 Session 6 tightening) and the
    `NoSStoreOnGuardSlotInSteps` conjuncts (Phase 5 Session 4
    strengthening) all hold vacuously since both `pre` and `post`
    are empty lists. -/
theorem ozWitnessFunction_isOZGuarded :
    IsOZGuardedFunction ozWitnessContract ozWitnessFunction := by
  refine ⟨[], ozWitnessCallee, ⟨0, by decide⟩, [], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · decide
  · -- NoCallInSteps [] — vacuous (no element in [])
    intro s hs; cases hs
  · intro s hs; cases hs
  · -- NoSStoreOnGuardSlotInSteps _ [] — vacuous (no element in [])
    intro s hs; cases hs
  · intro s hs; cases hs

/-- The witness contract follows the OZ guard discipline. -/
theorem ozWitnessContract_OZGuardDiscipline :
    OZGuardDiscipline ozWitnessContract := by
  refine ⟨?_, ?_⟩
  · -- functions ≠ []
    decide
  · -- ∀ f ∈ functions, IsOZGuardedFunction
    intro f hf
    simp [ozWitnessContract] at hf
    subst hf
    exact ozWitnessFunction_isOZGuarded

/-! ## W4 Wall — `adversarial_body_fails_strengthened_oz` (Phase 5 Session 4)

Per Ray's Q-VRVP2-1 confirmation (2026-04-28). The W4 wall — that
the Phase-4-Session-6 `IsOZGuardedFunction` (without
`NoSStoreOnGuardSlotInSteps` on pre/post) admits an adversarial
body shape where pre or post segments SSTORE the guard slot
mid-body — is preserved as a named theorem alongside W1 (vacuous
CEI hypothesis, Session 3), W2 (`stateless_trace_breaks_naive_strategy`,
Session 3), and W3 (`weak_rto_admits_self_unlock_reentry`,
Session 7.1).

### The wall

A function body of shape

  [sstore guardSlot lockedValue,           -- mandatory lock
   sstore guardSlot unlockedValue,         -- pre's mid-body unlock
   call callee value,                      -- single external CALL
   sstore guardSlot lockedValue,           -- post (any)
   sstore guardSlot unlockedValue,         -- mandatory unlock
   ret true]                               -- mandatory ret

satisfies the Phase-4-Session-6 `IsOZGuardedFunction` (with
`pre = [sstore guardSlot unlockedValue]`,
`post = [sstore guardSlot lockedValue]`, `NoCallInSteps` vacuous on
both — neither contains a `.call`). The body's external CALL fires
at trace position 3 with `guardSlotAt = unlockedValue`, violating
`TraceCCallLocked` at the trace level under any genuine execution.

The Phase 5 Session 4 strengthening (Q-VRVP2-1) adds
`NoSStoreOnGuardSlotInSteps C.guardSlot pre` and
`NoSStoreOnGuardSlotInSteps C.guardSlot post` to
`IsOZGuardedFunction`. Under the strengthened definition, the
adversarial body fails the new pre conjunct because the unique
decomposition forces `pre = [sstore guardSlot unlockedValue]` (one
SSTORE on the guard slot).

This wall was caught by the F4 design's VRVP-2 protocol BEFORE any
`BodyTraceLift.lean` Lean code was written —
an internal methodology note §5 + Phase 5 Session 4 Step 2 report.

### Documented as

* This file: `adversarialBody` + `adversarial_body_fails_strengthened_oz`.
* the internal methodology notes § 10 (the W4 wall paragraph).
-/

/-- The W4 adversarial body. Six steps: lock at entry, mid-body
    unlock in `pre`, single external CALL, mid-body relock in
    `post`, mandatory unlock + ret tail. Satisfies the
    Phase-4-Session-6 `IsOZGuardedFunction` shape but FAILS the
    Phase-5-Session-4 strengthening via `NoSStoreOnGuardSlotInSteps`
    on `pre`. -/
def adversarialBody : FunctionBody :=
  [FunctionBody.Step.sstore ozWitnessGuardSlot ⟨2, by decide⟩,
   FunctionBody.Step.sstore ozWitnessGuardSlot ⟨1, by decide⟩,
   FunctionBody.Step.call ozWitnessCallee ⟨0, by decide⟩,
   FunctionBody.Step.sstore ozWitnessGuardSlot ⟨2, by decide⟩,
   FunctionBody.Step.sstore ozWitnessGuardSlot ⟨1, by decide⟩,
   FunctionBody.Step.ret true]

/-- **W4 wall (Theorem-grade methodology exhibit).** The adversarial
    body fails the strengthened `IsOZGuardedFunction`. The unique
    decomposition forces `pre = [sstore guardSlot unlockedValue]` (a
    single SSTORE targeting the guard slot), which violates
    `NoSStoreOnGuardSlotInSteps C.guardSlot pre`. -/
theorem adversarial_body_fails_strengthened_oz :
    ¬ IsOZGuardedFunction ozWitnessContract adversarialBody := by
  rintro ⟨pre, callee, value, post, h_eq, _, _, _, h_pre_ns, _⟩
  cases pre with
  | nil =>
    -- pre = [] forces adversarialBody[1] to be the call. But
    -- adversarialBody[1] is sstore. Contradiction by injection.
    simp only [adversarialBody, ozWitnessContract, List.nil_append] at h_eq
    injection h_eq with _ h_eq2
    injection h_eq2 with h_call _
    cases h_call
  | cons head rest =>
    -- pre = head :: rest. Injection forces head = sstore ⟨7,_⟩ ⟨1,_⟩.
    -- Apply h_pre_ns to head ∈ pre.
    have h_head : head = FunctionBody.Step.sstore ozWitnessGuardSlot ⟨1, by decide⟩ := by
      simp only [adversarialBody, ozWitnessContract, List.cons_append] at h_eq
      injection h_eq with _ h_eq2
      injection h_eq2 with h_head _
      exact h_head.symm
    exact h_pre_ns head (List.mem_cons.mpr (Or.inl rfl)) ⟨⟨1, by decide⟩, h_head⟩

/-- The witness trace's call/return structure is balanced and respects
    `SStoresInOwnFrame` and `CallsFromTopFrame`. Same `interval_cases`
    pattern as `daoAttackTrace_validExecution`. -/
theorem ozWitnessTrace_validExecution : ValidExecution ozWitnessTrace := by
  refine ⟨?_, ?_, ?_⟩
  · -- SStoresInOwnFrame
    intro ⟨k, hk⟩ addr key val hstep
    have hk6 : k < 6 := hk
    show currentFrameAt ozWitnessTrace k = some addr
    interval_cases k
    all_goals simp [ozWitnessTrace] at hstep
    all_goals (obtain ⟨rfl, _, _⟩ := hstep; decide)
  · -- CallsFromTopFrame
    intro ⟨k, hk⟩ caller callee value hstep
    have hk6 : k < 6 := hk
    show currentFrameAt ozWitnessTrace k = some caller ∨
         currentFrameAt ozWitnessTrace k = none
    interval_cases k
    all_goals (
      simp [ozWitnessTrace] at hstep
      try (obtain ⟨rfl, rfl, rfl⟩ := hstep))
    all_goals decide
  · -- BalancedFrames
    intro ⟨k, hk⟩
    have hk6 : k < 6 := hk
    show frameDepthAt ozWitnessTrace k ≥ 0
    interval_cases k <;> decide

/-- The witness trace does NOT satisfy CEI: index pair `(2, 4)`
    witnesses the violation. Step 2 is `call ozWitness ozCallee` from
    `ozWitness`'s frame; step 4 is `sstore ozWitness ozGuardSlot 1`
    in `ozWitness`'s frame — i.e., the OZ guard's unlock SSTORE
    happens AFTER `ozWitness`'s external CALL. -/
theorem ozWitnessTrace_violates_cei : ¬ SatisfiesCEI ozWitnessTrace := by
  native_decide

/-! ## Theorem 4 — CEI and OZ guard are incompatible -/

/-- **Theorem 4 (CEI/OZ incompatibility).** There exists an
    OZ-disciplined contract `C` and a `ValidExecution` trace `tr`
    such that `tr` does NOT satisfy CEI.

    Reading: *the OZ guard pattern produces traces that violate CEI
    as a matter of design — the unlock SSTORE comes after the
    external CALL, by the discipline's own definition.*

    Per Ray (2026-04-27, Decision 2): *"The DeFi community
    conflates CEI and the OZ guard constantly. Every Solidity
    tutorial says 'use CEI or ReentrancyGuard.' The implication is
    they are equivalent. They are not. This paper proves it."*

    The witness is the OZ-disciplined `ozWitnessContract` running
    its single OZ-guarded function in `ozWitnessTrace`. -/
theorem cei_oz_incompatible :
    ∃ (C : Contract) (tr : ExecutionTrace),
      OZGuardDiscipline C ∧
      ValidExecution tr ∧
      ¬ SatisfiesCEI tr :=
  ⟨ozWitnessContract, ozWitnessTrace,
   ozWitnessContract_OZGuardDiscipline,
   ozWitnessTrace_validExecution,
   ozWitnessTrace_violates_cei⟩

/-! ## Theorem 5 statement — main soundness target

The paper's main soundness result. Statement only — substantive
proof is Phase 4 Session 5+ work, gated by Vacuity Re-Verification
Protocol per Ray's Decision 4 (2026-04-27 prework round).

Per R2 (zero `sorry`), we capture the statement as a `def : Prop`
rather than as a `theorem ... := sorry`. The Session 5+ proof will
be:

```lean
theorem oz_guard_prevents_reentrancy (C : Contract) :
    oz_guard_prevents_reentrancy_target C := by
  ...substantive proof...
```

**VRVP run on this statement:** see an internal phase report § 6.
The protocol identifies that the current `ReentrancyFree` predicate
is over-eager (its existential `a` is unconstrained), making the
theorem falsifiable by hand-construction even when `C` is
OZ-disciplined. The fix requires either restricting the predicate
to `a = C.address` or refining `ReachableTraceOf` to enforce
function-body conformance — both Session 5 deliverables.
-/

/-- **Theorem 5 (main soundness target).** If `C` follows the OZ
    guard discipline AND has distinct lock/unlock values, then `C`
    is reentrancy-free.

    *Status:* Prop type captured. Substantive proof is the Phase 4
    Session 7.2+ deliverable. The hypothesis `h_distinct` is per
    Ray's Decision 2 (post-Session-7-wall round) — a contract with
    `lockedValue = unlockedValue` has a trivially broken guard and
    is outside the scope of this theorem. -/
def oz_guard_prevents_reentrancy_target (C : Contract) : Prop :=
  C.lockedValue ≠ C.unlockedValue → OZGuardDiscipline C → ReentrancyFree C

/-! ## Phase 4 Session 6 — `theorem5_falsified_by_arbitrary_a` DELETED

Per Ray's Decision 4 (post-Session-4 round): *"When Session 5's
predicate refinement fixes the false theorem,
`theorem5_falsified_by_arbitrary_a` should fail to compile and
be replaced by the substantive proof. ... The wall theorem
failing to compile after the fix is the confirmation the fix
is doing real work."*

Phase 4 Session 6 (Track A.2 cascade) implemented the predicate
refinements:

* New `ReentrancyVulnerableStatefulOn (C : Contract)` restricts
  the witness's reentered contract to `C.address`
  (`Reentrancy.lean`).
* New `ReachableTraceOf` carries five conjuncts including
  entry-revert + C-frame-starts-with-lock + C-external-call-locked
  (`Reachability.lean`).
* `ReentrancyFree` now quantifies over `ReachableTraceOf` and
  uses `ReentrancyVulnerableStatefulOn` (`ReentrancyFree.lean`).

Under the new predicates, the previous wall witness no longer
constructs:

* `vrvpAttackerS₀` set `daoVictim`'s slot — but does NOT set
  `ozWitnessContract.address`'s slot, so
  `InitialGuardUnlocked ozWitnessContract vrvpAttackerS₀` fails.
* `daoAttackTrace` has no CALLs into `ozWitnessContract.address`,
  so `ReentrancyVulnerableStatefulOn ozWitnessContract` cannot
  fire.

Both halves of the wall witness are mechanically invalidated.
The theorem (and its supporting `vrvpAttackerS₀`) are removed.

The audit-gate has fired as designed. The substantive proof of
`oz_guard_prevents_reentrancy` is the Phase 4 Session 7
deliverable.
-/

/-! ## W3 Wall — `weak_rto_admits_self_unlock_reentry` (Phase 4 Session 7.1)

Per Ray's 2026-04-27 Decision 9 (post-Session-7-wall round). The W3
wall — that the Session-6 RTO with the `callee ≠ C.address`-restricted
call-locked conjunct admitted a self-unlock-reentry attack — is
preserved as a named theorem alongside W1 (vacuous CEI hypothesis,
Session 3) and W2 (`stateless_trace_breaks_naive_strategy`,
Session 3).

### The wall

A contract can lock its guard (per the lock-immediately-after-entry
constraint), unlock it mid-frame via a second SSTORE, and then
self-CALL with the guard unlocked. The Session-6 call-locked
conjunct restricted to `callee ≠ C.address` did not require the
guard to be locked at *self*-CALLs, so the self-call slipped through.
At the moment of the self-call, the guard was unlocked, so the
state-aware reentrancy predicate fires.

This demonstrates that **trace-level OZ guard constraints without
body conformance are insufficient**. Fix A (Phase 4 Session 7.1, in
`Reachability.lean`) drops the `callee ≠ C.address` clause: every
C-issued CALL, regardless of callee, requires guard = lockedValue.

The wall is machine-checked below as
`weak_rto_admits_self_unlock_reentry`.

### Witness construction

* **Contract:** `ozWitnessContract` (already proved `OZGuardDiscipline`
  via `ozWitnessContract_OZGuardDiscipline`).
* **Initial state:** `s₀_initial ozWitnessContract` (singleton Finmap
  with C's guard set to `unlockedValue`; `InitialGuardUnlocked`
  follows from `s₀_initial_satisfies_initialGuardUnlocked`).
* **Trace:** `w3ReentrantTrace`, the 5-step lock / mid-frame unlock /
  self-CALL / inner lock pattern.
-/

/-- The Session 6 `callee ≠ C.address`-restricted call-locked
    conjunct, preserved here only as the artifact for the W3 wall
    theorem. The strict version `TraceCCallLocked` (in
    `Reachability.lean`, Phase 4 Session 7.1) drops the
    `callee ≠ C.address` clause. -/
def TraceCCallLocked_weak (C : Contract) (s₀ : EVMState)
    (tr : ExecutionTrace) : Prop :=
  ∀ k : Fin tr.length, ∀ callee value,
    tr[k.val]? = some (EVMStep.call C.address callee value) →
    callee ≠ C.address →
    guardSlotAt s₀ tr k.val C.address C.guardSlot = C.lockedValue

/-- The Session 6 weak version of `ReachableTraceOf`, preserved
    here as the artifact of the W3 wall. The strict version (in
    `Reachability.lean`) replaces the fourth conjunct with
    `TraceCCallLocked` (Fix A). -/
def ReachableTraceOf_weak (C : Contract) (s₀ : EVMState)
    (tr : ExecutionTrace) : Prop :=
  InitialGuardUnlocked C s₀ ∧
  ValidExecution tr ∧
  TraceEntryRevert C s₀ tr ∧
  TraceCCallLocked_weak C s₀ tr ∧
  TraceCFrameStartsWithLock C tr

/-- The W3 attacker EOA address. -/
def w3AttackerEOA : Address := ⟨13, by decide⟩

/-- The W3 attack trace: external entry → lock → mid-frame unlock →
    self-CALL → inner-frame lock. Five steps, satisfies the weak
    Session-6 RTO, exhibits state-aware reentrancy. -/
def w3ReentrantTrace : ExecutionTrace := [
  /- 0 -/ EVMStep.call w3AttackerEOA ozWitnessAddress ⟨0, by decide⟩,
  /- 1 -/ EVMStep.sstore ozWitnessAddress ozWitnessGuardSlot ⟨2, by decide⟩,
  /- 2 -/ EVMStep.sstore ozWitnessAddress ozWitnessGuardSlot ⟨1, by decide⟩,
  /- 3 -/ EVMStep.call ozWitnessAddress ozWitnessAddress ⟨0, by decide⟩,
  /- 4 -/ EVMStep.sstore ozWitnessAddress ozWitnessGuardSlot ⟨2, by decide⟩
]

/-- Lemma: the guard slot at trace position 3 (the self-CALL) reads
    as `C.unlockedValue` — direct unfolding of the foldl chain
    `s₀ → s₀ (call) → {g↦2} (lock) → {g↦1} (mid-frame unlock)`. -/
theorem w3_guard_at_3 :
    guardSlotAt (s₀_initial ozWitnessContract) w3ReentrantTrace 3
        ozWitnessAddress ozWitnessGuardSlot
      = ozWitnessContract.unlockedValue := by
  unfold guardSlotAt slotAt stateAt evalState s₀_initial
    EVMState.lookupSlot Storage.lookupZ w3ReentrantTrace ozWitnessContract
  simp [List.take, List.foldl, applyStep, Storage.empty,
        Finmap.lookup_insert, Finmap.lookup_singleton_eq]

/-- Lemma: the guard slot at trace position 0 reads as
    `C.unlockedValue` — directly from `s₀_initial`. -/
theorem w3_guard_at_0 :
    guardSlotAt (s₀_initial ozWitnessContract) w3ReentrantTrace 0
        ozWitnessAddress ozWitnessGuardSlot
      = ozWitnessContract.unlockedValue := by
  unfold guardSlotAt slotAt stateAt evalState s₀_initial
    EVMState.lookupSlot Storage.lookupZ ozWitnessContract
  simp [List.take, Finmap.lookup_singleton_eq]

/-- The W3 trace is a `ValidExecution`: SStoresInOwnFrame +
    CallsFromTopFrame + BalancedFrames all hold. Same `interval_cases`
    pattern as `ozWitnessTrace_validExecution`. -/
theorem w3ReentrantTrace_validExecution : ValidExecution w3ReentrantTrace := by
  refine ⟨?_, ?_, ?_⟩
  · -- SStoresInOwnFrame
    intro ⟨k, hk⟩ addr key val hstep
    have hk5 : k < 5 := hk
    show currentFrameAt w3ReentrantTrace k = some addr
    interval_cases k
    all_goals simp [w3ReentrantTrace] at hstep
    all_goals (obtain ⟨rfl, _, _⟩ := hstep; decide)
  · -- CallsFromTopFrame
    intro ⟨k, hk⟩ caller callee value hstep
    have hk5 : k < 5 := hk
    show currentFrameAt w3ReentrantTrace k = some caller ∨
         currentFrameAt w3ReentrantTrace k = none
    interval_cases k
    all_goals (
      simp [w3ReentrantTrace] at hstep
      try (obtain ⟨rfl, rfl, rfl⟩ := hstep))
    all_goals decide
  · -- BalancedFrames
    intro ⟨k, hk⟩
    have hk5 : k < 5 := hk
    show frameDepthAt w3ReentrantTrace k ≥ 0
    interval_cases k <;> decide

/-- The W3 trace satisfies `TraceEntryRevert`: at both calls into
    `ozWitnessContract` (positions 0 and 3), the guard reads as
    `unlockedValue` — which differs from `lockedValue`. -/
theorem w3ReentrantTrace_traceEntryRevert :
    TraceEntryRevert ozWitnessContract (s₀_initial ozWitnessContract)
      w3ReentrantTrace := by
  intro ⟨k, hk⟩ caller value hstep
  have hk5 : k < 5 := hk
  show guardSlotAt (s₀_initial ozWitnessContract) w3ReentrantTrace k
         ozWitnessContract.address ozWitnessContract.guardSlot
       ≠ ozWitnessContract.lockedValue
  interval_cases k
  · -- k=0: call EOA C 0 — guard at 0 = unlocked = 1 ≠ 2
    show guardSlotAt _ _ 0 _ _ ≠ _
    have h0 := w3_guard_at_0
    simp [ozWitnessContract] at *
    rw [h0]
    decide
  · simp [w3ReentrantTrace] at hstep
  · simp [w3ReentrantTrace] at hstep
  · -- k=3: call C C 0 — guard at 3 = unlocked = 1 ≠ 2
    show guardSlotAt _ _ 3 _ _ ≠ _
    have h3 := w3_guard_at_3
    simp [ozWitnessContract] at *
    rw [h3]
    decide
  · simp [w3ReentrantTrace] at hstep

/-- The W3 trace satisfies the *weak* `TraceCCallLocked`: vacuous
    because the only C-issued CALL (position 3) has callee = C, so
    the `callee ≠ C.address` hypothesis is false at that position.
    Positions 0, 1, 2, 4 either are not C-issued CALLs or are not
    CALLs at all. **This is the loophole the wall exhibits.** -/
theorem w3ReentrantTrace_traceCCallLocked_weak :
    TraceCCallLocked_weak ozWitnessContract (s₀_initial ozWitnessContract)
      w3ReentrantTrace := by
  intro ⟨k, hk⟩ callee value hstep hne
  have hk5 : k < 5 := hk
  interval_cases k
  · -- k=0: call w3AttackerEOA ozWitnessAddress 0; caller=EOA≠C, so hstep mismatches
    simp [w3ReentrantTrace, ozWitnessContract, w3AttackerEOA, ozWitnessAddress] at hstep
  · simp [w3ReentrantTrace] at hstep
  · simp [w3ReentrantTrace] at hstep
  · -- k=3: call C C 0; callee=C contradicts hne
    simp [w3ReentrantTrace, ozWitnessContract] at hstep
    obtain ⟨rfl, rfl⟩ := hstep
    exact absurd rfl hne
  · simp [w3ReentrantTrace] at hstep

/-- The W3 trace satisfies `TraceCFrameStartsWithLock`: both calls
    into C (positions 0 and 3) are immediately followed by the
    lock SSTORE. -/
theorem w3ReentrantTrace_traceCFrameStartsWithLock :
    TraceCFrameStartsWithLock ozWitnessContract w3ReentrantTrace := by
  intro ⟨k, hk⟩ caller value hstep
  have hk5 : k < 5 := hk
  interval_cases k
  · -- k=0: tr[1] = sstore C g 2 = lockedValue
    show w3ReentrantTrace[(0 : Nat) + 1]? = _
    rfl
  · simp [w3ReentrantTrace, ozWitnessContract] at hstep
  · simp [w3ReentrantTrace, ozWitnessContract] at hstep
  · -- k=3: tr[4] = sstore C g 2 = lockedValue
    show w3ReentrantTrace[(3 : Nat) + 1]? = _
    rfl
  · simp [w3ReentrantTrace] at hstep

/-- The W3 trace is in the *weak* `ReachableTraceOf` of
    `ozWitnessContract` — every conjunct of the Session-6 RTO holds. -/
theorem w3ReentrantTrace_in_weak_RTO :
    ReachableTraceOf_weak ozWitnessContract (s₀_initial ozWitnessContract)
      w3ReentrantTrace :=
  ⟨s₀_initial_satisfies_initialGuardUnlocked ozWitnessContract,
   w3ReentrantTrace_validExecution,
   w3ReentrantTrace_traceEntryRevert,
   w3ReentrantTrace_traceCCallLocked_weak,
   w3ReentrantTrace_traceCFrameStartsWithLock⟩

/-- The W3 trace exhibits `ReentrancyVulnerableStatefulOn` — there
    are two CALLs into `ozWitnessContract` (at positions 0 and 3),
    the second is nested in the first, and the guard reads as
    `unlockedValue` at the reentry. -/
theorem w3ReentrantTrace_is_self_unlock_reentry :
    ReentrancyVulnerableStatefulOn ozWitnessContract
      (s₀_initial ozWitnessContract) w3ReentrantTrace := by
  refine ⟨0, 3, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · exact ⟨w3AttackerEOA, ⟨0, by decide⟩, rfl⟩
  · exact ⟨ozWitnessAddress, ⟨0, by decide⟩, rfl⟩
  · -- NestedAfter w3ReentrantTrace 0 3 — depth at 1, 2, 3 all > depth at 0 = 0
    decide
  · -- guardSlotAt s₀ tr 3 = C.unlockedValue
    exact w3_guard_at_3

/-! ## Self-call sub-case of Theorem 5 (Phase 4 Session 7.2)

The substantive proof of `oz_guard_prevents_reentrancy` splits into
two cases on the caller of `tr[j]` (the reentrant CALL into C):

* **Case A (self-call):** caller = `C.address`. This case closes
  *directly* from the RTO conjuncts: `TraceCCallLocked` at j gives
  `guard = lockedValue` (since caller = C), and `TraceEntryRevert`
  at j gives `guard ≠ lockedValue`. Contradiction — no `h_distinct`
  or `hVuln` needed.

* **Case B (external reentry):** caller ≠ `C.address`. This case
  requires a chain argument over the call-stack history between
  `i+1` and `j`. The proof is non-trivial (see Phase 4 Session 7.2
  report § "Wall on chain argument").

The lemma below captures Case A. It is independently useful: under
RTO, a contract `C` cannot self-CALL (caller = callee = C.address)
at any position in any trace.
-/

/-- **Self-call lemma (Phase 4 Session 7.2).** Under any reachable
    trace of `C`, no position has a self-CALL (caller = callee =
    `C.address`). The lock-on-entry constraint
    (`TraceCCallLocked`) requires `guard = lockedValue` at every
    C-issued CALL, while the entry-revert constraint
    (`TraceEntryRevert`) requires `guard ≠ lockedValue` at every
    CALL into C. A self-CALL is both — so the conjunction is
    inconsistent.

    This is the *direct* contradiction case of
    `oz_guard_prevents_reentrancy`'s case analysis on `caller_j`. -/
theorem no_self_call_under_RTO (C : Contract) (s₀ : EVMState)
    (tr : ExecutionTrace) (h_reach : ReachableTraceOf C s₀ tr)
    (k : Nat) (hk : k < tr.length) (value : Word256)
    (h_tr_k : tr[k]? = some (EVMStep.call C.address C.address value)) :
    False := by
  obtain ⟨_, _, h_revert, h_call_locked, _⟩ := h_reach
  have h_locked : guardSlotAt s₀ tr k C.address C.guardSlot = C.lockedValue := by
    exact h_call_locked ⟨k, hk⟩ C.address value h_tr_k
  have h_not_locked : guardSlotAt s₀ tr k C.address C.guardSlot ≠ C.lockedValue := by
    exact h_revert ⟨k, hk⟩ C.address value h_tr_k
  exact h_not_locked h_locked

/-! ## `stackAt` — Foundational call-stack helper (Phase 4 Session 7.4)

Per Ray's Decision 1 (post-Session-7.3-escalation round): the
combined inductive invariant for `guard_locked_during_call` needs
access to the full call stack (not just its head, which is what
`currentFrameAt` exposes). `stackAt` exposes the foldl that already
lives implicitly inside `currentFrameAt`'s definition, as a
`List Address`. The iff lemmas below tie this back to the existing
`currentFrameAt` (head) and `frameDepthAt` (length under
BalancedFrames) — so existing proofs and new invariant proofs live
in the same world. -/

/-- The call stack at trace position `k`, as a `List Address`. The
    fold function is the *same* anonymous lambda used in
    `currentFrameAt`'s definition (CEI.lean) — keeping them in lockstep
    is what makes `currentFrameAt_eq_head_stackAt` close by `rfl`. -/
def stackAt (tr : ExecutionTrace) (k : Nat) : List Address :=
  (tr.take k).foldl
    (fun (st : List Address) (s : EVMStep) =>
      match s with
      | .call _ callee _ => callee :: st
      | .ret _           => st.tail
      | .revert          => st.tail
      | .sstore _ _ _    => st)
    []

/-! ## `stackAt` step-evolution lemmas -/

/-- `stackAt` after a CALL pushes the callee onto the stack. -/
theorem stackAt_after_call (tr : ExecutionTrace) (k : Nat)
    (caller callee : Address) (value : Word256)
    (h : tr[k]? = some (EVMStep.call caller callee value)) :
    stackAt tr (k + 1) = callee :: stackAt tr k := by
  unfold stackAt
  have htake : tr.take (k + 1) = tr.take k ++ [EVMStep.call caller callee value] := by
    rw [List.take_add_one, h]; rfl
  rw [htake, List.foldl_append]
  rfl

/-- `stackAt` after a RET pops the top frame. -/
theorem stackAt_after_ret (tr : ExecutionTrace) (k : Nat)
    (success : Bool) (h : tr[k]? = some (EVMStep.ret success)) :
    stackAt tr (k + 1) = (stackAt tr k).tail := by
  unfold stackAt
  have htake : tr.take (k + 1) = tr.take k ++ [EVMStep.ret success] := by
    rw [List.take_add_one, h]; rfl
  rw [htake, List.foldl_append]
  rfl

/-- `stackAt` after a REVERT pops the top frame. -/
theorem stackAt_after_revert (tr : ExecutionTrace) (k : Nat)
    (h : tr[k]? = some EVMStep.revert) :
    stackAt tr (k + 1) = (stackAt tr k).tail := by
  unfold stackAt
  have htake : tr.take (k + 1) = tr.take k ++ [EVMStep.revert] := by
    rw [List.take_add_one, h]; rfl
  rw [htake, List.foldl_append]
  rfl

/-- `stackAt` after an SSTORE is unchanged. -/
theorem stackAt_after_sstore (tr : ExecutionTrace) (k : Nat)
    (a : Address) (key val : Word256)
    (h : tr[k]? = some (EVMStep.sstore a key val)) :
    stackAt tr (k + 1) = stackAt tr k := by
  unfold stackAt
  have htake : tr.take (k + 1) = tr.take k ++ [EVMStep.sstore a key val] := by
    rw [List.take_add_one, h]; rfl
  rw [htake, List.foldl_append]
  rfl

/-! ## iff lemmas — connecting `stackAt` to existing infrastructure

These are **load-bearing** (Decision 3): they preserve compatibility
with the seven existing step-evolution helpers from Session 7.3 and
with `currentFrameAt`/`frameDepthAt` throughout the codebase. -/

/-- `currentFrameAt` is the head of `stackAt`. By `rfl` because the
    fold lambdas match. -/
theorem currentFrameAt_eq_head_stackAt (tr : ExecutionTrace) (k : Nat) :
    currentFrameAt tr k = (stackAt tr k).head? := by
  unfold currentFrameAt stackAt
  rfl

/-! ## Step-evolution helpers (Phase 4 Session 7.3)

The inductive invariant for `guard_locked_during_call` requires
small lemmas about how `currentFrameAt`, `frameDepthAt`, and
`slotAt` evolve across a single trace step. Each is a foldl-append
manipulation: `tr.take (k+1) = tr.take k ++ [tr[k]]`. -/

/-- Helper: at position `k+1`, the call-stack head is the callee of
    `tr[k]` if that step is a CALL. Pushes the callee onto whatever
    stack was there at `k`. -/
theorem currentFrameAt_after_call (tr : ExecutionTrace) (k : Nat)
    (caller callee : Address) (value : Word256)
    (h : tr[k]? = some (EVMStep.call caller callee value)) :
    currentFrameAt tr (k + 1) = some callee := by
  unfold currentFrameAt
  have htake : tr.take (k + 1) = tr.take k ++ [EVMStep.call caller callee value] := by
    rw [List.take_add_one, h]; rfl
  rw [htake, List.foldl_append]
  simp [List.foldl]

/-- Helper: at position `k+1`, the call-stack head after an SSTORE
    is unchanged (SSTORE doesn't touch the stack). -/
theorem currentFrameAt_after_sstore (tr : ExecutionTrace) (k : Nat)
    (a : Address) (key val : Word256)
    (h : tr[k]? = some (EVMStep.sstore a key val)) :
    currentFrameAt tr (k + 1) = currentFrameAt tr k := by
  unfold currentFrameAt
  have htake : tr.take (k + 1) = tr.take k ++ [EVMStep.sstore a key val] := by
    rw [List.take_add_one, h]; rfl
  rw [htake, List.foldl_append]
  simp [List.foldl]

/-- Helper: depth at `k+1` is `depth at k + 1` after a CALL. -/
theorem frameDepthAt_after_call (tr : ExecutionTrace) (k : Nat)
    (caller callee : Address) (value : Word256)
    (h : tr[k]? = some (EVMStep.call caller callee value)) :
    frameDepthAt tr (k + 1) = frameDepthAt tr k + 1 := by
  show frameDepth (tr.take (k + 1)) = frameDepth (tr.take k) + 1
  have htake : tr.take (k + 1) = tr.take k ++ [EVMStep.call caller callee value] := by
    rw [List.take_add_one, h]; rfl
  rw [htake]
  unfold frameDepth
  rw [List.foldl_append]
  simp [List.foldl_cons, List.foldl_nil, EVMStep.depthDelta]

/-- Helper: depth at `k+1` is `depth at k - 1` after a RET. -/
theorem frameDepthAt_after_ret (tr : ExecutionTrace) (k : Nat)
    (success : Bool) (h : tr[k]? = some (EVMStep.ret success)) :
    frameDepthAt tr (k + 1) = frameDepthAt tr k - 1 := by
  show frameDepth (tr.take (k + 1)) = frameDepth (tr.take k) - 1
  have htake : tr.take (k + 1) = tr.take k ++ [EVMStep.ret success] := by
    rw [List.take_add_one, h]; rfl
  rw [htake]
  unfold frameDepth
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, EVMStep.depthDelta]
  rfl

/-- Helper: depth at `k+1` is `depth at k - 1` after a REVERT. -/
theorem frameDepthAt_after_revert (tr : ExecutionTrace) (k : Nat)
    (h : tr[k]? = some EVMStep.revert) :
    frameDepthAt tr (k + 1) = frameDepthAt tr k - 1 := by
  show frameDepth (tr.take (k + 1)) = frameDepth (tr.take k) - 1
  have htake : tr.take (k + 1) = tr.take k ++ [EVMStep.revert] := by
    rw [List.take_add_one, h]; rfl
  rw [htake]
  unfold frameDepth
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, EVMStep.depthDelta]
  rfl

/-- Helper: depth at `k+1` is `depth at k` after an SSTORE. -/
theorem frameDepthAt_after_sstore (tr : ExecutionTrace) (k : Nat)
    (a : Address) (key val : Word256)
    (h : tr[k]? = some (EVMStep.sstore a key val)) :
    frameDepthAt tr (k + 1) = frameDepthAt tr k := by
  show frameDepth (tr.take (k + 1)) = frameDepth (tr.take k)
  have htake : tr.take (k + 1) = tr.take k ++ [EVMStep.sstore a key val] := by
    rw [List.take_add_one, h]; rfl
  rw [htake]
  unfold frameDepth
  rw [List.foldl_append]
  simp [List.foldl_cons, List.foldl_nil, EVMStep.depthDelta]

/-- Helper: trace-level slot stability for a single step. If `tr[k]`
    is not an SSTORE on `(a, key)`, then the slot value is unchanged
    at position `k+1`. Wraps `slot_unchanged_by_non_sstore`. -/
theorem guardSlotAt_after_non_sstore (s₀ : EVMState) (tr : ExecutionTrace)
    (k : Nat) (hk : k < tr.length) (a : Address) (key : Word256)
    (h : ∀ step, tr[k]? = some step → ¬ step.IsSStoreOn a key) :
    slotAt s₀ tr (k + 1) a key = slotAt s₀ tr k a key := by
  apply (slot_stable_no_sstore s₀ tr a key k (k + 1) (Nat.le_succ k) hk _).symm
  intro k' hk'_ge hk'_lt step hstep
  have hk'_eq : k' = k := by omega
  subst hk'_eq
  exact h step hstep

/-! ## Length-vs-depth iff (Phase 4 Session 7.4 Decision 3)

This is the second of the two mandatory iff lemmas. Proved by
induction on `k` using the existing step-evolution helpers (depth
side) and `stackAt`'s step-evolution lemmas (length side). The
ret/revert cases rely on `BalancedFrames` to ensure the stack is
non-empty when popping. -/

/-- Under `BalancedFrames`, the trace's depth equals the stack's
    length (cast to `Int`). Restricted to `k < tr.length` because at
    `k = tr.length` the lemma can fail for traces ending in
    ret-on-empty (which `BalancedFrames` doesn't constrain at the
    boundary). For the invariant proof, all uses are at positions
    `≤ j < tr.length`, so this restriction is harmless. -/
theorem frameDepthAt_eq_length_stackAt (tr : ExecutionTrace)
    (h_balanced : BalancedFrames tr) (k : Nat) (hk : k < tr.length) :
    frameDepthAt tr k = ((stackAt tr k).length : Int) := by
  induction k with
  | zero =>
    show frameDepth (tr.take 0) = ((stackAt tr 0).length : Int)
    unfold stackAt frameDepth
    simp [List.take_zero]
  | succ k ih =>
    have hk_lt : k < tr.length := Nat.lt_of_succ_lt hk
    have ih' := ih hk_lt
    have hstep : tr[k]? = some (tr[k]'hk_lt) := List.getElem?_eq_getElem hk_lt
    cases hstep_case : tr[k]'hk_lt with
    | call caller callee value =>
      have hstep' : tr[k]? = some (EVMStep.call caller callee value) := by
        rw [hstep, hstep_case]
      rw [frameDepthAt_after_call tr k caller callee value hstep',
          stackAt_after_call tr k caller callee value hstep']
      simp [List.length_cons]
      omega
    | ret success =>
      have hstep' : tr[k]? = some (EVMStep.ret success) := by
        rw [hstep, hstep_case]
      rw [frameDepthAt_after_ret tr k success hstep',
          stackAt_after_ret tr k success hstep']
      have h_bal : frameDepthAt tr (k + 1) ≥ 0 := h_balanced ⟨k + 1, hk⟩
      have h_depth_after := frameDepthAt_after_ret tr k success hstep'
      have h_depth_k : frameDepthAt tr k ≥ 1 := by omega
      have h_stack_nonempty : (stackAt tr k).length ≥ 1 := by
        have : ((stackAt tr k).length : Int) ≥ 1 := by rw [← ih']; exact h_depth_k
        omega
      have h_tail : (stackAt tr k).tail.length = (stackAt tr k).length - 1 := by
        cases h_eq : stackAt tr k with
        | nil => simp [h_eq] at h_stack_nonempty
        | cons head tail => simp
      rw [h_tail]
      omega
    | revert =>
      have hstep' : tr[k]? = some EVMStep.revert := by
        rw [hstep, hstep_case]
      rw [frameDepthAt_after_revert tr k hstep',
          stackAt_after_revert tr k hstep']
      have h_bal : frameDepthAt tr (k + 1) ≥ 0 := h_balanced ⟨k + 1, hk⟩
      have h_depth_after := frameDepthAt_after_revert tr k hstep'
      have h_depth_k : frameDepthAt tr k ≥ 1 := by omega
      have h_stack_nonempty : (stackAt tr k).length ≥ 1 := by
        have : ((stackAt tr k).length : Int) ≥ 1 := by rw [← ih']; exact h_depth_k
        omega
      have h_tail : (stackAt tr k).tail.length = (stackAt tr k).length - 1 := by
        cases h_eq : stackAt tr k with
        | nil => simp [h_eq] at h_stack_nonempty
        | cons head tail => simp
      rw [h_tail]
      omega
    | sstore a key val =>
      have hstep' : tr[k]? = some (EVMStep.sstore a key val) := by
        rw [hstep, hstep_case]
      rw [frameDepthAt_after_sstore tr k a key val hstep',
          stackAt_after_sstore tr k a key val hstep']
      exact ih'

/-- **W3 wall (Theorem-grade methodology exhibit).** There exists an
    OZ-disciplined contract `C`, an initial state `s₀`, and an
    execution trace `tr` such that the *Session-6 weak* RTO holds
    AND state-aware reentrancy fires. The strict
    `ReachableTraceOf` (post-Fix-A, in `Reachability.lean`) closes
    this gap by dropping the `callee ≠ C.address` clause from the
    call-locked conjunct.

    Per Ray (2026-04-27, post-Session-7-wall Decision 9):
    *"Three machine-checked demonstrations that the model is precise
    enough to detect its own gaps. This is the methodology section
    of the paper. No other smart contract verification paper has
    this."*

    Cross-references:
    * the internal methodology notes § 10 (the W3 wall paragraph)
    * `Reachability.lean` (the `TraceCCallLocked` strict conjunct
      that closes the gap) -/
theorem weak_rto_admits_self_unlock_reentry :
    ∃ (C : Contract) (s₀ : EVMState) (tr : ExecutionTrace),
      OZGuardDiscipline C ∧
      ReachableTraceOf_weak C s₀ tr ∧
      ReentrancyVulnerableStatefulOn C s₀ tr :=
  ⟨ozWitnessContract, s₀_initial ozWitnessContract, w3ReentrantTrace,
   ozWitnessContract_OZGuardDiscipline,
   w3ReentrantTrace_in_weak_RTO,
   w3ReentrantTrace_is_self_unlock_reentry⟩

/-! ## Combined inductive invariant (Phase 4 Session 7.4)

The §4.2 paper sketch (an internal phase report) of the
`guard_locked_during_call` chain argument. For positions
`p ∈ [i+1, j]` (where `(i, j)` is a nested CALL pair into `C`), the
invariant `OZInv C s₀ tr i p` carries three properties:

* **(A)** If `C` is not the top of the call stack at `p`, the guard
  reads as `C.lockedValue`.
* **(B)** No `CALL` into `C` occurred between positions `i` and `p`
  (i.e., for `q` with `i < q < p`).
* **(C)** The call stack at `p` has the form
  `pre ++ C.address :: stackAt tr i` where `pre` contains no
  `C.address`. This is the operational form of the §4.2 remark
  "the popped C frame must be the i-frame": together with
  `NestedAfter`, it forces any pop of `C` at position `p ≤ j-1` to
  pop the entry-frame `C_i`, which then lowers depth to
  `frameDepthAt tr i` — violating `NestedAfter` at `p+1`.

The §4.2 sketch was originally stated with only (A) and (B);
property (C) is the §4.2 remark made precise. No new foundational
definition (per Decision 4 hard-stop) — `stackAt` was introduced in
the previous step of Session 7.4 and is the only new foundational
object in the invariant phase. -/

/-- The combined inductive invariant for `guard_locked_during_call`.
    See the section doc-comment above for the three properties. -/
def OZInv (C : Contract) (s₀ : EVMState) (tr : ExecutionTrace)
    (i p : Nat) : Prop :=
  (currentFrameAt tr p ≠ some C.address →
    guardSlotAt s₀ tr p C.address C.guardSlot = C.lockedValue) ∧
  (∀ q : Nat, i < q → q < p →
    ∀ caller value, tr[q]? ≠ some (EVMStep.call caller C.address value)) ∧
  (∃ pre : List Address,
    stackAt tr p = pre ++ C.address :: stackAt tr i ∧
    C.address ∉ pre)

/-- **The combined inductive invariant holds.** Given a nested CALL pair
    `(i, j)` into `C` (where `tr[i]` is a CALL into `C`), `OZInv` holds
    at every position `p` with `i+1 ≤ p ≤ j`.

    Proved by `Nat.le_induction` on `p` from `i+1`. The four step cases
    (sstore / call / ret / revert) each preserve all three invariant
    components. The ret/revert cases use `NestedAfter` at `p+1` together
    with property (C) to derive contradiction when `pre = []` (the case
    where the popped frame would be the entry-`C`, lowering depth to
    `frameDepthAt tr i`). -/
theorem oz_invariant_holds (C : Contract) (s₀ : EVMState) (tr : ExecutionTrace)
    (h_reach : ReachableTraceOf C s₀ tr)
    (i j : Nat) (hij : i < j) (hjlen : j < tr.length)
    (caller_i : Address) (value_i : Word256)
    (h_call_i : tr[i]? = some (EVMStep.call caller_i C.address value_i))
    (h_nest : NestedAfter tr i j) :
    ∀ p : Nat, i + 1 ≤ p → p ≤ j → OZInv C s₀ tr i p := by
  obtain ⟨_h_init, h_valid, h_revert, h_call_locked, _h_frame_lock⟩ := h_reach
  obtain ⟨h_sstores, h_calls, h_balanced⟩ := h_valid
  have hi_lt_len : i < tr.length := by omega
  intro p hp
  induction p, hp using Nat.le_induction with
  | base =>
    intro _hpj
    refine ⟨?_, ?_, ?_⟩
    · intro h_ne
      exact absurd
        (currentFrameAt_after_call tr i caller_i C.address value_i h_call_i) h_ne
    · intro q h_iq h_qsucc _ _ _; omega
    · refine ⟨[], ?_, ?_⟩
      · have h := stackAt_after_call tr i caller_i C.address value_i h_call_i
        rw [h]; rfl
      · simp
  | succ p hp ih =>
    intro hpj
    have hp_le_j : p ≤ j := by omega
    obtain ⟨ih_A, ih_B, ih_C⟩ := ih hp_le_j
    have hp_lt_j : p < j := by omega
    have hp_lt_len : p < tr.length := by omega
    have hp1_lt_len : p + 1 < tr.length := by omega
    have h_tr_p : tr[p]? = some (tr[p]'hp_lt_len) :=
      List.getElem?_eq_getElem hp_lt_len
    -- NestedAfter at p+1 (used in ret/revert sub-cases)
    have h_nest_p1 : frameDepthAt tr (p + 1) > frameDepthAt tr i := by
      have hd : p - i < j - i := by omega
      have h_n := h_nest ⟨p - i, hd⟩
      have h_eq : i + 1 + (p - i) = p + 1 := by omega
      rw [h_eq] at h_n
      exact h_n
    have h_depth_p1 :=
      frameDepthAt_eq_length_stackAt tr h_balanced (p + 1) hp1_lt_len
    have h_depth_i :=
      frameDepthAt_eq_length_stackAt tr h_balanced i hi_lt_len
    cases h_step_case : tr[p]'hp_lt_len with
    | sstore a_p k_p v_p =>
      have h_tr_p' : tr[p]? = some (EVMStep.sstore a_p k_p v_p) := by
        rw [h_tr_p, h_step_case]
      refine ⟨?_, ?_, ?_⟩
      · -- (A) at p+1
        intro h_ne_p1
        have h_cf := currentFrameAt_after_sstore tr p a_p k_p v_p h_tr_p'
        rw [h_cf] at h_ne_p1
        have h_guard_p := ih_A h_ne_p1
        have h_sf := h_sstores ⟨p, hp_lt_len⟩ a_p k_p v_p h_tr_p'
        have h_ap_ne : a_p ≠ C.address := by
          intro h_eq
          apply h_ne_p1
          rw [h_sf, h_eq]
        have h_slot_eq : slotAt s₀ tr (p + 1) C.address C.guardSlot
            = slotAt s₀ tr p C.address C.guardSlot := by
          apply guardSlotAt_after_non_sstore s₀ tr p hp_lt_len C.address C.guardSlot
          intro step h_step_some h_isSS
          obtain ⟨val, h_val⟩ := h_isSS
          rw [h_val] at h_step_some
          have h := h_step_some.symm.trans h_tr_p'
          injection h with h'
          injection h' with h_addr _ _
          exact h_ap_ne h_addr.symm
        show guardSlotAt s₀ tr (p + 1) C.address C.guardSlot = C.lockedValue
        unfold guardSlotAt
        rw [h_slot_eq]
        exact h_guard_p
      · -- (B)
        intro q h_iq h_qsucc caller value h_eq
        rcases Nat.lt_or_ge q p with h_qp | h_qp
        · exact ih_B q h_iq h_qp caller value h_eq
        · have h_q_eq : q = p := by omega
          subst h_q_eq
          rw [h_tr_p'] at h_eq
          injection h_eq with h_step
          exact EVMStep.noConfusion h_step
      · -- (C)
        obtain ⟨pre, h_stack_p, h_C_notin⟩ := ih_C
        refine ⟨pre, ?_, h_C_notin⟩
        rw [stackAt_after_sstore tr p a_p k_p v_p h_tr_p', h_stack_p]
    | call caller_p callee_p value_p =>
      have h_tr_p' : tr[p]? = some (EVMStep.call caller_p callee_p value_p) := by
        rw [h_tr_p, h_step_case]
      obtain ⟨pre, h_stack_p, h_C_notin⟩ := ih_C
      have h_stack_p_has_C : C.address ∈ stackAt tr p := by
        rw [h_stack_p]; simp
      have h_cfp_some : ∃ a, currentFrameAt tr p = some a := by
        rw [currentFrameAt_eq_head_stackAt]
        cases h_stk : stackAt tr p with
        | nil => rw [h_stk] at h_stack_p_has_C; cases h_stack_p_has_C
        | cons hd _ => exact ⟨hd, rfl⟩
      have h_caller_eq : currentFrameAt tr p = some caller_p := by
        rcases h_calls ⟨p, hp_lt_len⟩ caller_p callee_p value_p h_tr_p' with h | h
        · exact h
        · obtain ⟨a, ha⟩ := h_cfp_some
          rw [h] at ha
          exact absurd ha (by simp)
      have h_callee_ne : callee_p ≠ C.address := by
        intro h_eq
        subst h_eq
        by_cases h_cc : caller_p = C.address
        · subst h_cc
          exact no_self_call_under_RTO C s₀ tr ⟨_h_init, ⟨h_sstores, h_calls, h_balanced⟩,
            h_revert, h_call_locked, _h_frame_lock⟩ p hp_lt_len value_p h_tr_p'
        · have h_ne : currentFrameAt tr p ≠ some C.address := by
            rw [h_caller_eq]
            intro h_some_eq
            apply h_cc
            injection h_some_eq
          have h_guard_p := ih_A h_ne
          exact (h_revert ⟨p, hp_lt_len⟩ caller_p value_p h_tr_p') h_guard_p
      refine ⟨?_, ?_, ?_⟩
      · -- (A)
        intro _h_ne_p1
        have h_guard_p : guardSlotAt s₀ tr p C.address C.guardSlot = C.lockedValue := by
          by_cases h_cc : caller_p = C.address
          · subst h_cc
            exact h_call_locked ⟨p, hp_lt_len⟩ callee_p value_p h_tr_p'
          · have h_ne : currentFrameAt tr p ≠ some C.address := by
              rw [h_caller_eq]
              intro h_some_eq
              apply h_cc
              injection h_some_eq
            exact ih_A h_ne
        have h_slot_eq : slotAt s₀ tr (p + 1) C.address C.guardSlot
            = slotAt s₀ tr p C.address C.guardSlot := by
          apply guardSlotAt_after_non_sstore s₀ tr p hp_lt_len C.address C.guardSlot
          intro step h_step_some h_isSS
          obtain ⟨val, h_val⟩ := h_isSS
          rw [h_val] at h_step_some
          have h := h_step_some.symm.trans h_tr_p'
          injection h with h'
          exact EVMStep.noConfusion h'
        show guardSlotAt s₀ tr (p + 1) C.address C.guardSlot = C.lockedValue
        unfold guardSlotAt
        rw [h_slot_eq]
        exact h_guard_p
      · -- (B)
        intro q h_iq h_qsucc caller value h_eq
        rcases Nat.lt_or_ge q p with h_qp | h_qp
        · exact ih_B q h_iq h_qp caller value h_eq
        · have h_q_eq : q = p := by omega
          subst h_q_eq
          rw [h_tr_p'] at h_eq
          injection h_eq with h_step
          injection h_step with _ h_callee_eq _
          exact h_callee_ne h_callee_eq
      · -- (C)
        refine ⟨callee_p :: pre, ?_, ?_⟩
        · rw [stackAt_after_call tr p caller_p callee_p value_p h_tr_p', h_stack_p]
          rfl
        · intro h_in
          rcases List.mem_cons.mp h_in with h | h
          · exact h_callee_ne h.symm
          · exact h_C_notin h
    | ret success_p =>
      have h_tr_p' : tr[p]? = some (EVMStep.ret success_p) := by
        rw [h_tr_p, h_step_case]
      obtain ⟨pre, h_stack_p, h_C_notin⟩ := ih_C
      have h_pre_nonempty : pre ≠ [] := by
        intro h_empty
        subst h_empty
        simp at h_stack_p
        have h_stack_p1 : stackAt tr (p + 1) = stackAt tr i := by
          rw [stackAt_after_ret tr p success_p h_tr_p', h_stack_p]; rfl
        rw [h_stack_p1] at h_depth_p1
        omega
      cases h_pre_case : pre with
      | nil => exact absurd h_pre_case h_pre_nonempty
      | cons h_head pre' =>
        rw [h_pre_case] at h_stack_p h_C_notin
        have h_head_ne_C : h_head ≠ C.address := by
          intro h_eq
          apply h_C_notin
          rw [h_eq]
          exact List.mem_cons.mpr (Or.inl rfl)
        refine ⟨?_, ?_, ⟨pre', ?_, ?_⟩⟩
        · -- (A)
          intro _h_ne_p1
          have h_cf_p : currentFrameAt tr p = some h_head := by
            rw [currentFrameAt_eq_head_stackAt, h_stack_p]; rfl
          have h_ne : currentFrameAt tr p ≠ some C.address := by
            rw [h_cf_p]
            intro h_some_eq
            injection h_some_eq with h_eq
            exact h_head_ne_C h_eq
          have h_guard_p := ih_A h_ne
          have h_slot_eq : slotAt s₀ tr (p + 1) C.address C.guardSlot
              = slotAt s₀ tr p C.address C.guardSlot := by
            apply guardSlotAt_after_non_sstore s₀ tr p hp_lt_len C.address C.guardSlot
            intro step h_step_some h_isSS
            obtain ⟨val, h_val⟩ := h_isSS
            rw [h_val] at h_step_some
            have h := h_step_some.symm.trans h_tr_p'
            injection h with h'
            exact EVMStep.noConfusion h'
          show guardSlotAt s₀ tr (p + 1) C.address C.guardSlot = C.lockedValue
          unfold guardSlotAt
          rw [h_slot_eq]
          exact h_guard_p
        · -- (B)
          intro q h_iq h_qsucc caller value h_eq
          rcases Nat.lt_or_ge q p with h_qp | h_qp
          · exact ih_B q h_iq h_qp caller value h_eq
          · have h_q_eq : q = p := by omega
            subst h_q_eq
            rw [h_tr_p'] at h_eq
            injection h_eq with h_step
            exact EVMStep.noConfusion h_step
        · -- (C) stack
          rw [stackAt_after_ret tr p success_p h_tr_p', h_stack_p]; rfl
        · -- (C) C ∉ pre'
          intro h_in
          apply h_C_notin
          exact List.mem_cons.mpr (Or.inr h_in)
    | revert =>
      have h_tr_p' : tr[p]? = some EVMStep.revert := by
        rw [h_tr_p, h_step_case]
      obtain ⟨pre, h_stack_p, h_C_notin⟩ := ih_C
      have h_pre_nonempty : pre ≠ [] := by
        intro h_empty
        subst h_empty
        simp at h_stack_p
        have h_stack_p1 : stackAt tr (p + 1) = stackAt tr i := by
          rw [stackAt_after_revert tr p h_tr_p', h_stack_p]; rfl
        rw [h_stack_p1] at h_depth_p1
        omega
      cases h_pre_case : pre with
      | nil => exact absurd h_pre_case h_pre_nonempty
      | cons h_head pre' =>
        rw [h_pre_case] at h_stack_p h_C_notin
        have h_head_ne_C : h_head ≠ C.address := by
          intro h_eq
          apply h_C_notin
          rw [h_eq]
          exact List.mem_cons.mpr (Or.inl rfl)
        refine ⟨?_, ?_, ⟨pre', ?_, ?_⟩⟩
        · -- (A)
          intro _h_ne_p1
          have h_cf_p : currentFrameAt tr p = some h_head := by
            rw [currentFrameAt_eq_head_stackAt, h_stack_p]; rfl
          have h_ne : currentFrameAt tr p ≠ some C.address := by
            rw [h_cf_p]
            intro h_some_eq
            injection h_some_eq with h_eq
            exact h_head_ne_C h_eq
          have h_guard_p := ih_A h_ne
          have h_slot_eq : slotAt s₀ tr (p + 1) C.address C.guardSlot
              = slotAt s₀ tr p C.address C.guardSlot := by
            apply guardSlotAt_after_non_sstore s₀ tr p hp_lt_len C.address C.guardSlot
            intro step h_step_some h_isSS
            obtain ⟨val, h_val⟩ := h_isSS
            rw [h_val] at h_step_some
            have h := h_step_some.symm.trans h_tr_p'
            injection h with h'
            exact EVMStep.noConfusion h'
          show guardSlotAt s₀ tr (p + 1) C.address C.guardSlot = C.lockedValue
          unfold guardSlotAt
          rw [h_slot_eq]
          exact h_guard_p
        · -- (B)
          intro q h_iq h_qsucc caller value h_eq
          rcases Nat.lt_or_ge q p with h_qp | h_qp
          · exact ih_B q h_iq h_qp caller value h_eq
          · have h_q_eq : q = p := by omega
            subst h_q_eq
            rw [h_tr_p'] at h_eq
            injection h_eq with h_step
            exact EVMStep.noConfusion h_step
        · -- (C) stack
          rw [stackAt_after_revert tr p h_tr_p', h_stack_p]; rfl
        · -- (C) C ∉ pre'
          intro h_in
          apply h_C_notin
          exact List.mem_cons.mpr (Or.inr h_in)

/-! ## `guard_locked_during_call` — corollary of the invariant

The chain-argument lemma the §4.2 sketch was driving toward:
under `ReachableTraceOf` and a `NestedAfter (i, j)` CALL pair into
`C` whose outer-most caller at `j` is *not* `C`, the guard slot at
position `j` reads as `C.lockedValue`. This is Property (A) of
`OZInv` applied at `p = j` together with the standard CallsFromTopFrame
deduction that `currentFrameAt tr j = some caller_j`. -/

/-- **`guard_locked_during_call`.** If `tr[j]` is a CALL into `C` whose
    caller is *not* `C`, and `(i, j)` is a nested CALL pair into `C`,
    then the guard slot reads as `C.lockedValue` at position `j`. -/
theorem guard_locked_during_call (C : Contract) (s₀ : EVMState)
    (tr : ExecutionTrace)
    (h_reach : ReachableTraceOf C s₀ tr)
    (i j : Nat) (hij : i < j) (hjlen : j < tr.length)
    (caller_i : Address) (value_i : Word256)
    (h_call_i : tr[i]? = some (EVMStep.call caller_i C.address value_i))
    (h_nest : NestedAfter tr i j)
    (caller_j : Address) (value_j : Word256)
    (h_call_j : tr[j]? = some (EVMStep.call caller_j C.address value_j))
    (h_caller_j_ne : caller_j ≠ C.address) :
    guardSlotAt s₀ tr j C.address C.guardSlot = C.lockedValue := by
  have h_inv := oz_invariant_holds C s₀ tr h_reach i j hij hjlen
                  caller_i value_i h_call_i h_nest j (Nat.succ_le_of_lt hij)
                  (Nat.le_refl j)
  obtain ⟨h_A, _, _⟩ := h_inv
  obtain ⟨_, h_valid, _, _, _⟩ := h_reach
  obtain ⟨_, h_calls, h_balanced⟩ := h_valid
  have hi_lt_len : i < tr.length := by omega
  -- depth at j > depth at i ≥ 0, so depth at j ≥ 1, so stack at j non-empty
  have h_depth_j_gt : frameDepthAt tr j > frameDepthAt tr i := by
    have hd : j - i - 1 < j - i := by omega
    have h_n := h_nest ⟨j - i - 1, hd⟩
    have h_eq : i + 1 + (j - i - 1) = j := by omega
    rw [h_eq] at h_n
    exact h_n
  have h_dep_i_ge : frameDepthAt tr i ≥ 0 := h_balanced ⟨i, hi_lt_len⟩
  have h_depth_j_eq :=
    frameDepthAt_eq_length_stackAt tr h_balanced j hjlen
  have h_stack_j_nonempty : stackAt tr j ≠ [] := by
    intro h_eq
    rw [h_eq] at h_depth_j_eq
    simp at h_depth_j_eq
    omega
  have h_cfj_some : ∃ a, currentFrameAt tr j = some a := by
    rw [currentFrameAt_eq_head_stackAt]
    cases h_stk : stackAt tr j with
    | nil => exact absurd h_stk h_stack_j_nonempty
    | cons hd _ => exact ⟨hd, rfl⟩
  have h_cfj_eq : currentFrameAt tr j = some caller_j := by
    rcases h_calls ⟨j, hjlen⟩ caller_j C.address value_j h_call_j with h | h
    · exact h
    · obtain ⟨a, ha⟩ := h_cfj_some
      rw [h] at ha
      exact absurd ha (by simp)
  have h_cfj_ne : currentFrameAt tr j ≠ some C.address := by
    rw [h_cfj_eq]
    intro h_some_eq
    apply h_caller_j_ne
    injection h_some_eq
  exact h_A h_cfj_ne

/-! ## Theorem 5* — `reentrancy_free_universal` (Phase 5 Step 0 / Path γ′)

Strict generalization of Theorem 5: if `C.lockedValue ≠ C.unlockedValue`,
then `C` is reentrancy-free under the OZ trace policy — *without* any
body-shape hypothesis. The `OZGuardDiscipline` hypothesis of the
original Theorem 5 statement is genuinely unused in the trace-level
reasoning: `ReachableTraceOf`'s five conjuncts (`InitialGuardUnlocked`,
`ValidExecution`, `TraceEntryRevert`, `TraceCCallLocked`,
`TraceCFrameStartsWithLock`) already encode the OZ guard discipline
at the trace level, so the implication holds for any contract `C`
regardless of body shape.

This is the Phase 5 Step 0 deliverable per
an internal handoff document and the internal completeness strategy's
Path α plan. It closes the unused-hypothesis finding from the
Phase 5 Session 1 VRVP and gives the paper a cleaner, stronger
headline: trace-policy soundness depends only on `l ≠ u`, not on any
body-shape predicate.

VRVP (2026-04-28): hand-construction of `(C, s₀, tr)` with `l ≠ u`,
`ReachableTraceOf C s₀ tr`, AND `ReentrancyVulnerableStatefulOn C s₀ tr`
fails for the same reason Theorem 5's proof closes — both `caller_j =
C.address` (blocked by `no_self_call_under_RTO`) and `caller_j ≠
C.address` (blocked by `guard_locked_during_call` + distinctness)
yield contradictions. No `OZGuardDiscipline` step appears in the
contradiction chain.

Splits on the caller of the reentrant CALL at `j`:

* **Case A (self-call)** — caller = `C.address`. Closes via
  `no_self_call_under_RTO`.
* **Case B (external reentry)** — caller ≠ `C.address`. Closes via
  `guard_locked_during_call` + the distinctness hypothesis. -/

/-- **Theorem 5* (`reentrancy_free_universal`).** For any contract
    `C` with distinct lock/unlock values, `C` is reentrancy-free
    under the OZ trace policy. No body-shape hypothesis required.
    Strict generalization of Theorem 5.

    *Status:* COMPLETE (Phase 5 Session 2, 2026-04-28). -/
theorem reentrancy_free_universal (C : Contract)
    (h_distinct : C.lockedValue ≠ C.unlockedValue) :
    ReentrancyFree C := by
  intro s₀ tr h_reach h_vuln
  obtain ⟨i, j, hij, hjlen, hCalli, hCallj, hNest, hGuardJ⟩ := h_vuln
  obtain ⟨caller_i, value_i, h_tr_i⟩ := hCalli
  obtain ⟨caller_j, value_j, h_tr_j⟩ := hCallj
  by_cases h_caller : caller_j = C.address
  · -- Case A: self-call
    subst h_caller
    exact no_self_call_under_RTO C s₀ tr h_reach j hjlen value_j h_tr_j
  · -- Case B: external reentry
    have h_locked := guard_locked_during_call C s₀ tr h_reach i j hij hjlen
                       caller_i value_i h_tr_i hNest caller_j value_j h_tr_j h_caller
    have h_eq : C.lockedValue = C.unlockedValue := h_locked.symm.trans hGuardJ
    exact h_distinct h_eq

/-! ## Theorem 5 — `oz_guard_prevents_reentrancy` (main soundness)

Phase 5 Session 2 (2026-04-28): re-derived as a one-line corollary of
`reentrancy_free_universal` (Theorem 5*). The original 12-line proof
body is preserved verbatim inside `reentrancy_free_universal`; Theorem 5
now delegates to it and discards the unused `OZGuardDiscipline`
hypothesis. The named theorem `oz_guard_prevents_reentrancy` and its
statement (`oz_guard_prevents_reentrancy_target`) are unchanged — audit
baseline references remain valid (an internal audit transcript,
`PrintAxioms.lean`). -/

/-- **Theorem 5 (main soundness).** If `C.lockedValue ≠ C.unlockedValue`
    and `C` follows the OpenZeppelin guard discipline, then `C` is
    reentrancy-free. Corollary of `reentrancy_free_universal`
    (Theorem 5*) — the `OZGuardDiscipline` hypothesis is unused.

    *Status:* COMPLETE. -/
theorem oz_guard_prevents_reentrancy (C : Contract) :
    oz_guard_prevents_reentrancy_target C := by
  intro h_distinct _h_oz
  exact reentrancy_free_universal C h_distinct

end QanaryContracts
