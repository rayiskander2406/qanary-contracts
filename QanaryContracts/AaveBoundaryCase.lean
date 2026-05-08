/-
  QanaryContracts/AaveBoundaryCase.lean

  Aave V3 Pool Boundary Case Paired-Theorem Certificate (Layer 6-C Phase 3-4).

  Per Session 39 reconnaissance survey (an internal reconnaissance note)
  Aave V3 Pool reference exemplar with `flashLoan` as the canonical
  protocol-by-design CEI-correct pattern, deployed at
  `0x87870bca3f3fd6335c3f4ce8392d69350b4fa4e2` (Ethereum mainnet).

  Per Question 8a Option (i) compressed Phase 3-4 framing, Question 8b
  Variation (i) SSTORE-after-CALL DAO-mirror vulnerable pattern, Question
  8c Option (P) M-22.2 Tier 1 wrapper-layer absorption, Question 8d
  Option (2) parallel CI block, Question 8e Framing (a) body-shape-vs-
  trace-layer discrimination, Option (m-prime) single-file, Naming
  (b-prime) distinguished `aaveContract` / `aaveContractAdjacent`
  prefixes — all applied throughout Session 40.

  Coexistence: Sessions 14-39 substantive constructs, DAOContract.lean
  (Layer 6-A negative-instance certificate), DAOAttack.lean (Layer 6-A
  trace-layer prior work), and CompoundContract.lean (Layer 6-B positive-
  instance certificate) are preserved unchanged. M-26.1 compose-from-
  outside umbrella (Session 36 Unit 2 graduation; M-26.1.1 sub-aspect)
  holds across the layer boundary; AaveBoundaryCase.lean composes against
  universal soundness from Sessions 14-27 and against the Layer 6-A / 6-B
  artifacts via compose-from-outside discipline without modification.

  Module-level docstring with §1-§6 sections deferred to Unit 5 per
  directive Part 8 Action 5.5.
-/

import QanaryContracts.Contract
import QanaryContracts.FunctionBody
import QanaryContracts.Step
import QanaryContracts.EVM
import QanaryContracts.OZSoundness

namespace QanaryContracts

/-! ## Foundational helpers (Layer 6-C Phase 3, Session 40 Unit 1)

    Address/slot/value definitions parametrizing both Layer 6-C abstract
    pattern templates. Numeric literals chosen distinct from Layer 6-A
    (`DAOContract.lean`) and Layer 6-B (`CompoundContract.lean`) literals
    to avoid identifier reuse — all three modules live in
    `namespace QanaryContracts` (the addresses live in disjoint
    `Contract` instances; numeric distinctness is for reader clarity,
    not a soundness requirement).

    Aave V3 Pool reference exemplar:
    `0x87870bca3f3fd6335c3f4ce8392d69350b4fa4e2` (Ethereum mainnet
    deployment of the V3 Pool contract managing flashLoan plus the
    `_status` reentrancy guard inherited from OpenZeppelin's
    `ReentrancyGuard`). The numeric standin `⟨9, decide⟩` represents
    the Pool at the abstract pattern layer per Question 8e Framing (a)
    body-shape-vs-trace-layer decision. Specific deployed bytecode
    semantics are deferred to Unit 5 module-level docstring §3 reference. -/

/-- Aave V3 Pool standin at abstract pattern layer (Layer 6-C reference exemplar). -/
def aavePoolAddress : Address := ⟨9, by decide⟩

/-- IFlashLoanReceiver standin — the protected callback target invoked
    inside `flashLoan` (Aave V3's borrower-supplied receiver contract
    implementing `executeOperation`). Distinct from `aavePoolAddress`
    so that `NoCallToSelfInSteps` holds for the protocol-by-design body. -/
def aaveCallbackTargetAddress : Address := ⟨10, by decide⟩

/-- Storage slot for Aave V3's reentrancy guard `_status` flag. -/
def aaveGuardSlot : Word256 := ⟨0, by decide⟩

/-- OZ v4-style `_NOT_ENTERED` value — matches Layer 6-A
    (`daoUnlockedValue`) and Layer 6-B (`compoundUnlockedValue`)
    convention (1 = unlocked) for cross-layer structural consistency. -/
def aaveUnlockedValue : Word256 := ⟨1, by decide⟩

/-- OZ v4-style `_ENTERED` value — matches Layer 6-A (`daoLockedValue`)
    and Layer 6-B (`compoundLockedValue`) convention (2 = locked) for
    cross-layer structural consistency. -/
def aaveLockedValue : Word256 := ⟨2, by decide⟩

/-! ## Abstract pattern templates (Layer 6-C Phase 3, Session 40 Unit 1)

    Two parameterized `FunctionBody` schemas capturing the structural
    discrimination locus at Layer 6-C boundary. Both templates take a
    `Contract` argument and `innerSteps : List FunctionBody.Step`
    (the body content excluding the head/tail SSTORE/RET frame),
    producing a `FunctionBody`.

    The structural distinction at body-shape layer:

    * `aaveProtocolByDesignPattern` — head SSTORE engages guard, inner
      steps execute (including the protected callback CALL), tail SSTORE
      disengages guard, then RET. CEI-correct ordering. Predicate-
      acceptance witness via
      `aaveProtocolByDesignPattern_isOZGuardedFunctionGeneral` below
      (M-22.2 Tier 1 wrapper-layer absorption — fourth empirical
      instance after Layer 6-A Phase 3 master, Layer 6-A Phase 4
      meta-theorem, and Layer 6-B `cTokenAbstractPattern` lemma).

    * `aaveAdjacentVulnerablePattern` — inner steps execute first
      (callback CALL with guard NOT engaged at head), then a single
      tail SSTORE engages the guard AFTER the inner body completes,
      then RET. CEI-violation; structural mirror of DAO 2016's exploited
      feature at the inverse direction (DAO violates because deployed;
      Aave V3 adjacent violates because constructed for boundary case
      demonstration). Predicate-rejection at Unit 3 via head-element
      constructor disjointness when inner steps start with a non-SSTORE
      step (e.g., the callback `.call`). -/

/-- Layer 6-C protocol-by-design abstract pattern. CEI-correct: guard
    engaged before inner body, disengaged after. Mirrors Layer 6-B's
    `cTokenAbstractPattern` at the structural-shape layer; instantiated
    at Unit 2 against `aaveContract` for the `flashLoan` formalization
    with `innerSteps = [.call aaveCallbackTargetAddress 0]`.

    Structural correspondence to the four directive-required pattern
    elements (per directive Part 4 Action 1.1 §4):

    * SSTORE guard-set step → first list element
      `.sstore C.guardSlot C.lockedValue`.
    * CALL invocation step at protected position → lives within
      `innerSteps` (the callback CALL).
    * SSTORE guard-clear step → second-to-last list element
      `.sstore C.guardSlot C.unlockedValue`.
    * Parameterization over protected callee → indirect via
      `innerSteps` carrying `.call <callee> _` steps. -/
def aaveProtocolByDesignPattern (C : Contract) (innerSteps : List FunctionBody.Step) : FunctionBody :=
  FunctionBody.Step.sstore C.guardSlot C.lockedValue ::
  innerSteps ++
  [FunctionBody.Step.sstore C.guardSlot C.unlockedValue,
   FunctionBody.Step.ret true]

/-- Layer 6-C protocol-by-design abstract pattern soundness lemma. The
    lemma absorbs the existential body witness at wrapper-layer per
    M-22.2 Tier 1 architectural-cleanliness pattern (Session 36 Unit 3
    refinement); the Unit 2 per-function lemma composes against this
    lemma directly without reconstructing the existential.

    Fourth empirical instance of M-22.2 Tier 1 wrapper-layer absorption
    after Layer 6-A Phase 3 master + Layer 6-A Phase 4 meta-theorem +
    Layer 6-B `cTokenAbstractPattern_isOZGuardedFunctionGeneral`.
    Tridirectional empirical evidence for the Tier 1 refinement —
    rejection (Layer 6-A) + acceptance (Layer 6-B) + structural-
    neighborhood discrimination (Layer 6-C).

    The structural argument mirrors Layer 6-B's lemma:
    `aaveProtocolByDesignPattern C innerSteps` reduces definitionally
    to the exact shape `IsOZGuardedFunctionGeneral`'s existential body
    equation requires when the existential witness is `innerSteps`
    itself. The two side conditions (`NoSStoreOnGuardSlotInSteps` and
    `NoCallToSelfInSteps`) on `innerSteps` pass through directly to
    the predicate's two body-step invariants.

    Axiom record (zero-axiom, kernel-only): the proof uses anonymous-
    constructor on `Exists` and `And` plus `rfl` for the body-shape
    equation; no `simp`, no propext-bearing tactics. -/
theorem aaveProtocolByDesignPattern_isOZGuardedFunctionGeneral
    (C : Contract) (innerSteps : List FunctionBody.Step)
    (h_no_sstore : NoSStoreOnGuardSlotInSteps C.guardSlot innerSteps)
    (h_no_self_call : NoCallToSelfInSteps C.address innerSteps) :
    IsOZGuardedFunctionGeneral C (aaveProtocolByDesignPattern C innerSteps) :=
  ⟨innerSteps, rfl, h_no_sstore, h_no_self_call⟩

/-- Layer 6-C structurally adjacent vulnerable pattern. CEI-violation:
    the callback CALL fires within `innerSteps` at the head position
    (with guard NOT yet engaged); a single SSTORE engages the guard
    AFTER the inner steps complete, then RET.

    The structural shape `innerSteps ++ [.sstore C.guardSlot
    C.lockedValue, .ret true]` differs from `aaveProtocolByDesignPattern`
    only at the head-frame layer — the head SSTORE engaging the guard
    is absent. When `innerSteps` begins with a non-SSTORE step (e.g.,
    the callback `.call` step at Unit 3), the predicate's required head
    element `.sstore C.guardSlot C.lockedValue` is not at position 0,
    and the existential body-shape equation in
    `IsOZGuardedFunctionGeneral` fails by constructor disjointness
    `.call ≠ .sstore` via `FunctionBody.Step.noConfusion` — the same
    structural-rejection mechanism as Layer 6-A's
    `OZGuardDisciplineGeneral_falsified_at_withdrawRewardFor` and
    `_at_splitDAO`.

    Per Question 8b Variation (i): the SSTORE-after-CALL ordering
    structurally mirrors DAO 2016's exploited feature (state mutation
    after external call). Reviewers reading paper §10 see the boundary
    case as controlled inversion of Layer 6-A's structural argument;
    the discriminating granularity claim grounds at the same structural
    feature across both layers (CEI ordering: CEI-correct accepts;
    CEI-violation rejects).

    Unit 3 produces the per-function rejection lemma at the contract
    layer composing this pattern with `aaveContractAdjacent`. No
    abstract rejection lemma is provided here — the rejection mechanism
    is locally visible at the contract-layer via `unfold` plus
    `injection` plus `noConfusion`, mirroring Layer 6-A's per-function
    falsifications at `withdrawRewardFor` and `splitDAO` directly. -/
def aaveAdjacentVulnerablePattern (C : Contract) (innerSteps : List FunctionBody.Step) : FunctionBody :=
  innerSteps ++
  [FunctionBody.Step.sstore C.guardSlot C.lockedValue,
   FunctionBody.Step.ret true]

end QanaryContracts
