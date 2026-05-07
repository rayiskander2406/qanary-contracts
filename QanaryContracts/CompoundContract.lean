/-
  QanaryContracts/CompoundContract.lean

  Layer 6-B Compound positive-instance certificate. Module-level docstring
  with full compositional context, abstract cToken pattern semantics, cDAI
  reference exemplar, three-theorem structure, audit-gate scope, and
  Layer 6-B documentation locus closure is authored at Session 38 Unit 5
  per directive Part 8 (post-Phase-3-4 substantive completion).
-/

import QanaryContracts.Contract
import QanaryContracts.FunctionBody
import QanaryContracts.Step
import QanaryContracts.EVM
import QanaryContracts.OZSoundness

namespace QanaryContracts

/-! ## Foundational helpers (Layer 6-B Phase 3, Session 38 Unit 1)

    Address/slot/value definitions parametrizing the abstract cToken
    pattern. Numeric literals chosen distinct from `DAOContract.lean`'s
    literals for reader clarity (the addresses live in disjoint
    `Contract` instances; distinctness is not a soundness requirement).

    cDAI reference exemplar: `0x5d3a536e4d6dbd6114cc1ead35777bab948e3643`
    (Compound v2 cToken family deployment instantiated for the DAI
    underlying token). The numeric standin `⟨7, decide⟩` represents
    cDAI at the abstract pattern layer per Question 5d Option (X-prime)
    confirmation. Specific deployed bytecode semantics are deferred to
    Phase 3 substantive scope. -/

/-- cDAI standin at abstract pattern layer (Layer 6-B reference exemplar). -/
def compoundContractAddress : Address := ⟨7, by decide⟩

/-- DAI standin — the protected external-call target for cToken's
    underlying-token interactions. Must satisfy
    `underlyingTokenAddress ≠ compoundContractAddress` so that
    `NoCallToSelfInSteps` holds for the function bodies that CALL it. -/
def underlyingTokenAddress : Address := ⟨8, by decide⟩

/-- Storage slot for the cToken `_notEntered`-style status flag
    (the reentrancy guard's storage location). -/
def compoundGuardSlot : Word256 := ⟨0, by decide⟩

/-- OZ v4-style `_NOT_ENTERED` value — matches DAOContract.lean's
    `daoUnlockedValue` convention for parallelism with Layer 6-A. -/
def compoundUnlockedValue : Word256 := ⟨1, by decide⟩

/-- OZ v4-style `_ENTERED` value — matches DAOContract.lean's
    `daoLockedValue` convention for parallelism with Layer 6-A. -/
def compoundLockedValue : Word256 := ⟨2, by decide⟩

/-- Storage slot for `transferFrom`'s allowance update step. Distinct
    from `compoundGuardSlot` so that the allowance SSTORE within
    transferFrom's inner body does not violate
    `NoSStoreOnGuardSlotInSteps`. -/
def compoundAllowanceSlot : Word256 := ⟨3, by decide⟩

/-! ## Abstract cToken pattern definition (Layer 6-B Phase 3, Session 38 Unit 1)

    Per Question 5d Option (X-prime) abstract pattern load-bearing
    decision. The pattern is a parameterized `FunctionBody` schema
    capturing the lock-body-unlock-ret structural shape that any
    cToken `nonReentrant`-decorated function follows. Parameterization
    over `innerSteps` allows multiple cToken functions to instantiate
    the same pattern with different inner content:

    * `transfer` (Unit 2): single-step inner = the protected CALL.
    * `transferFrom` (Unit 2): two-step inner = allowance SSTORE +
      protected CALL.

    Future cTokens (cUSDC, cETH, ...) at the abstract layer instantiate
    via the same pattern with different callee addresses; the load-
    bearing argument transmits at the pattern layer per Option X-prime
    framing.

    Structural correspondence to the four directive-required pattern
    elements (per directive Part 4 Action 1.1 §3):

    * SSTORE guard-set step → first list element
      `.sstore C.guardSlot C.lockedValue`.
    * CALL invocation step at protected position → lives within
      `innerSteps`.
    * SSTORE guard-clear step → second-to-last list element
      `.sstore C.guardSlot C.unlockedValue`.
    * Parameterization over protected callee → indirect via
      `innerSteps` carrying `.call <callee> _` steps. -/
def cTokenAbstractPattern (C : Contract) (innerSteps : List FunctionBody.Step) : FunctionBody :=
  FunctionBody.Step.sstore C.guardSlot C.lockedValue ::
  innerSteps ++
  [FunctionBody.Step.sstore C.guardSlot C.unlockedValue,
   FunctionBody.Step.ret true]

/-- F2-B / Layer 6-B Phase 3 abstract-pattern soundness lemma. The
    lemma absorbs the existential body witness at wrapper-layer per
    M-22.2 Tier 1 architectural-cleanliness pattern (Session 36 Unit 3
    refinement); per-function theorems at Unit 2 compose against this
    lemma without reconstructing the existential.

    The structural argument: `cTokenAbstractPattern C innerSteps`
    reduces definitionally to the exact shape that
    `IsOZGuardedFunctionGeneral`'s existential body equation requires
    when the existential witness is `innerSteps` itself. The two
    side conditions (`NoSStoreOnGuardSlotInSteps` and
    `NoCallToSelfInSteps`) on `innerSteps` pass through directly to
    the predicate's two body-step invariants.

    Axiom record (zero-axiom, kernel-only): the proof uses anonymous-
    constructor on `Exists` and `And` plus `rfl` for the body-shape
    equation; no `simp`, no propext-bearing tactics. -/
theorem cTokenAbstractPattern_isOZGuardedFunctionGeneral
    (C : Contract) (innerSteps : List FunctionBody.Step)
    (h_no_sstore : NoSStoreOnGuardSlotInSteps C.guardSlot innerSteps)
    (h_no_self_call : NoCallToSelfInSteps C.address innerSteps) :
    IsOZGuardedFunctionGeneral C (cTokenAbstractPattern C innerSteps) :=
  ⟨innerSteps, rfl, h_no_sstore, h_no_self_call⟩

/-! ## `transfer` formalization (Layer 6-B Phase 3, Session 38 Unit 2)

    DAO-symmetric subset (Question 6b Option (ii)): cToken's `transfer`
    function operates against the underlying ERC-20 token, executing
    a single protected external call within the reentrancy guard span.
    Mirror to Layer 6-A's `withdrawRewardFor` at structural granularity
    — minimal external-call function — but with CEI-honoring rather
    than CEI-violating ordering.

    Body shape (4 steps):
    * `.sstore compoundGuardSlot compoundLockedValue` — guard engage
    * `.call underlyingTokenAddress 0`                — protected external call
    * `.sstore compoundGuardSlot compoundUnlockedValue`— guard disengage
    * `.ret true`                                      — return success

    Inner content relative to abstract pattern's lock-body-unlock-ret
    schema (Unit 1 `cTokenAbstractPattern`): single `.call` step.
    Definitional equality `transfer = cTokenAbstractPattern compoundContract
    [.call underlyingTokenAddress ⟨0, by decide⟩]` recovered at Unit 3's
    per-function predicate proof site.

    See an internal VRVP methodology note §1 for the function shape
    specification and §3 DAO-symmetry mapping. -/
def transfer : FunctionBody :=
  [FunctionBody.Step.sstore compoundGuardSlot compoundLockedValue,
   FunctionBody.Step.call underlyingTokenAddress ⟨0, by decide⟩,
   FunctionBody.Step.sstore compoundGuardSlot compoundUnlockedValue,
   FunctionBody.Step.ret true]

/-! ## `transferFrom` formalization (Layer 6-B Phase 3, Session 38 Unit 2)

    DAO-symmetric subset (Question 6b Option (ii)): cToken's
    `transferFrom` adds the allowance-update state mutation step
    (representing the ERC-20 allowance state mutation) before the
    protected external call. Mirror to Layer 6-A's `splitDAO` at
    structural granularity — longer body with auxiliary state-mutation
    — but with CEI-honoring rather than CEI-violating ordering of the
    sstore-vs-call.

    Body shape (5 steps):
    * `.sstore compoundGuardSlot compoundLockedValue` — guard engage
    * `.sstore compoundAllowanceSlot 0`               — allowance state mutation
                                                        (non-guard slot per Unit 1
                                                        distinctness condition)
    * `.call underlyingTokenAddress 0`                — protected external call
    * `.sstore compoundGuardSlot compoundUnlockedValue`— guard disengage
    * `.ret true`                                      — return success

    Inner content: 2-step inner = allowance SSTORE on
    `compoundAllowanceSlot` (distinct from `compoundGuardSlot` per Unit 1
    §3 distinctness condition) followed by the protected CALL.
    Distinct body from `transfer` — provides the second-function
    structural witness for Unit 3's master theorem composition over
    `compoundContract.functions = [transfer, transferFrom]`.

    See an internal VRVP methodology note §2 for the function shape
    specification and §3 DAO-symmetry mapping. -/
def transferFrom : FunctionBody :=
  [FunctionBody.Step.sstore compoundGuardSlot compoundLockedValue,
   FunctionBody.Step.sstore compoundAllowanceSlot ⟨0, by decide⟩,
   FunctionBody.Step.call underlyingTokenAddress ⟨0, by decide⟩,
   FunctionBody.Step.sstore compoundGuardSlot compoundUnlockedValue,
   FunctionBody.Step.ret true]

end QanaryContracts
