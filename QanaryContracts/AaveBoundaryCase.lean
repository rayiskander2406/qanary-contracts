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

/-! ## `flashLoan` formalization (Layer 6-C Phase 3, Session 40 Unit 2)

    Aave V3 Pool's `flashLoan` function modeled at body-shape layer per
    Question 8e Framing (a) body-shape minimal-scope discipline. Single-
    step inner with the protected callback CALL captures the CEI-correct
    structural feature: head SSTORE engages guard, callback CALL fires
    while guarded, tail SSTORE disengages guard, RET.

    Body shape (4 steps, mirror of Layer 6-B's `transfer` at structural
    granularity):
    * `.sstore aaveGuardSlot aaveLockedValue`   — guard engage (`_status = _ENTERED`)
    * `.call aaveCallbackTargetAddress 0`        — protected callback CALL
                                                   (the IFlashLoanReceiver
                                                    .executeOperation
                                                    invocation)
    * `.sstore aaveGuardSlot aaveUnlockedValue` — guard disengage (`_status = _NOT_ENTERED`)
    * `.ret true`                                — return success

    Auxiliary state mutations (asset transfers, fee accumulation) are
    not modeled — they are inert relative to the predicate's structural-
    acceptance argument at body-shape layer. Layer 6-D cross-protocol
    audit gate work may extend the model with richer auxiliary mutations.

    Definitional equality `flashLoan = aaveProtocolByDesignPattern
    aaveContract [.call aaveCallbackTargetAddress ⟨0, by decide⟩]` holds
    via iota reduction on `aaveContract`'s structure literal projections
    (`.guardSlot → aaveGuardSlot`, `.lockedValue → aaveLockedValue`,
    `.unlockedValue → aaveUnlockedValue`); the per-function lemma below
    relies on this equality at the `refine` site.

    See an internal VRVP methodology note §2 for the body-
    shape specification and §4 body-shape-vs-trace-layer framing. -/
def flashLoan : FunctionBody :=
  [FunctionBody.Step.sstore aaveGuardSlot aaveLockedValue,
   FunctionBody.Step.call aaveCallbackTargetAddress ⟨0, by decide⟩,
   FunctionBody.Step.sstore aaveGuardSlot aaveUnlockedValue,
   FunctionBody.Step.ret true]

/-! ## `aaveContract` Contract definition (Layer 6-C Phase 3, Session 40 Unit 2)

    The protocol-by-design contract literal composing `flashLoan` from
    above with the helper constants from Unit 1. Field literals support
    definitional equality with `aaveProtocolByDesignPattern aaveContract
    [<inner>]` at the per-function lemma proof site:
    `aaveContract.guardSlot` reduces to `aaveGuardSlot` via iota;
    `.lockedValue` to `aaveLockedValue`; `.unlockedValue` to
    `aaveUnlockedValue`; `.address` to `aavePoolAddress`.

    Single-function literal `[flashLoan]` reflects the abstract-pattern-
    layer minimal-scope framing: Aave V3 Pool's flashLoan is the load-
    bearing protocol-by-design exemplar; other Pool functions (supply,
    borrow, repay, ...) are deferred per Question 8e Framing (a)
    discipline (one canonical CEI-correct function suffices for the
    boundary case demonstration). -/
def aaveContract : Contract :=
  { address := aavePoolAddress,
    guardSlot := aaveGuardSlot,
    unlockedValue := aaveUnlockedValue,
    lockedValue := aaveLockedValue,
    functions := [flashLoan] }

/-! ## Per-function predicate at `flashLoan` (Layer 6-C Phase 3, Session 40 Unit 2)

    Layer 6-C positive-instance per-function lemma at the protocol-by-
    design contract. Applies Unit 1's
    `aaveProtocolByDesignPattern_isOZGuardedFunctionGeneral` lemma
    directly per M-22.2 Tier 1 architectural-cleanliness pattern (fourth
    empirical instance). The body shape `flashLoan` reduces definitionally
    to `aaveProtocolByDesignPattern aaveContract [.call
    aaveCallbackTargetAddress ⟨0, by decide⟩]` via iota on
    `aaveContract`'s structure literal projections; the abstract pattern
    lemma absorbs the existential body witness at wrapper-layer.

    Naming per Naming (b-prime): theorem name carries the contract prefix
    `aaveContract_` to disambiguate from Unit 3's rejection lemma at
    `aaveContractAdjacent`. The paired theorem name structure
    (`_at_aaveContract_flashLoan` vs `_at_aaveContractAdjacent_flashLoanVulnerable`)
    reflects the substantive paired-pattern distinction at theorem-name
    granularity per Question 8c Option (P) M-22.2 Tier 1 wrapper-layer
    absorption framing.

    **Body-shape-vs-trace-layer framing (Question 8e Framing (a)):**
    the lemma proves predicate ACCEPTANCE at body-shape layer despite
    the callback CALL appearing as potential reentrancy at trace layer.
    The discriminating-power claim's structural argument operates on
    the body-shape's structural feature (head SSTORE engages guard
    before CALL; tail SSTORE disengages guard after CALL), not on
    whether the callback's runtime behavior actually re-enters. The
    OZ `_status` check would `revert` on reentry; the body shape's
    `[sstore lock, ..., sstore unlock, ret]` schema is the structural
    witness for the protocol invariant.

    Side condition discharges:
    * `NoSStoreOnGuardSlotInSteps`: vacuous on the single `.call` inner
      step via constructor disjointness `.call ≠ .sstore`.
    * `NoCallToSelfInSteps`: holds via `aaveCallbackTargetAddress ≠
      aavePoolAddress` discharged by `decide` (kernel decide; no
      `native_decide` axiom).

    Axiom record target: zero-axiom (kernel-only). The proof uses
    `refine` + `intro` + anonymous-constructor destructuring + `cases`
    + `injection` + `rw` + `decide` — all kernel-only tactics.

    See an internal VRVP methodology note §3 for the proof
    tactic strategy and §3.2 axiom-record projection. -/
theorem IsOZGuardedFunctionGeneral_at_aaveContract_flashLoan :
    IsOZGuardedFunctionGeneral aaveContract flashLoan := by
  refine aaveProtocolByDesignPattern_isOZGuardedFunctionGeneral aaveContract
    [FunctionBody.Step.call aaveCallbackTargetAddress ⟨0, by decide⟩] ?_ ?_
  · -- NoSStoreOnGuardSlotInSteps on [.call ...]
    intro s hs
    rintro ⟨val, h⟩
    cases hs with
    | head _ => cases h
    | tail _ h_tail => cases h_tail
  · -- NoCallToSelfInSteps on [.call ...]
    intro s hs callee value h_call
    cases hs with
    | head _ =>
      injection h_call with h_callee _
      intro h_addr_eq
      rw [← h_callee] at h_addr_eq
      exact absurd h_addr_eq (by decide)
    | tail _ h_tail => cases h_tail

/-! ## `flashLoanVulnerable` formalization (Layer 6-C Phase 3, Session 40 Unit 3)

    The structurally adjacent vulnerable function modeled at body-shape
    layer per Question 8b Variation (i) SSTORE-after-CALL DAO-mirror
    confirmation. Single-step inner = the UNGUARDED callback CALL at
    head position (no guard SSTORE precedes it; OZ `_status` is in its
    initial state, not the `_ENTERED` state required for reentrancy
    protection).

    Body shape (3 steps):
    * `.call aaveCallbackTargetAddress 0`        — UNGUARDED callback CALL
                                                   at head (CEI-violation:
                                                   external CALL fires
                                                   before guard engaged)
    * `.sstore aaveGuardSlot aaveLockedValue`   — guard engage AFTER
                                                   callback returned
                                                   (structurally inert
                                                   against reentrancy:
                                                   guard engaged after
                                                   the protected window)
    * `.ret true`                                — return

    **Structural symmetry mapping with DAO 2016 (paper §10 raw material):**

    | Layer 6-A (`withdrawRewardFor`) | Layer 6-C (`flashLoanVulnerable`) |
    |---|---|
    | `.call daoRewardAccount 0`     | `.call aaveCallbackTargetAddress 0` |
    | `.sstore daoPaidOutSlot 0`     | `.sstore aaveGuardSlot aaveLockedValue` |
    |   (state mutation AFTER CALL  — CEI violation) | (state mutation AFTER CALL — CEI violation) |
    | `.ret true`                    | `.ret true` |
    | Head step `.call` ≠ predicate-required `.sstore` | Head step `.call` ≠ predicate-required `.sstore` |

    Both layers reject at the same head-element-injectivity mechanism:
    head step is `.call`; predicate-required head is
    `.sstore C.guardSlot C.lockedValue`; constructor disjointness
    `.call ≠ .sstore` produces the rejection via
    `FunctionBody.Step.noConfusion`.

    **Inverse direction interpretation:** DAO 2016 violates because
    deployed (the structural feature was in production code attacked
    on June 17 2016); Aave V3 adjacent violates because constructed
    (the structural feature is inserted into a synthetic contract for
    boundary case demonstration — the deployed Aave V3 Pool does NOT
    have this body shape; only the protocol-by-design `flashLoan`
    from Unit 2 corresponds to deployed code).

    The discriminating-power claim's structural-neighborhood granularity
    argument is the bridge: the predicate's decision flips at the
    head-frame layer between protocol-by-design (Unit 2 `flashLoan`,
    accepted) and structurally adjacent vulnerable (Unit 3
    `flashLoanVulnerable`, rejected), demonstrating the predicate
    distinguishes structurally adjacent patterns where small variations
    flip the predicate's decision.

    Definitional equality `flashLoanVulnerable = aaveAdjacentVulnerablePattern
    aaveContractAdjacent [.call aaveCallbackTargetAddress ⟨0, by decide⟩]`
    holds via iota on `aaveContractAdjacent`'s structure literal
    projections; the structural correspondence is recoverable at any
    proof site that benefits from explicit pattern-instantiation framing.

    See an internal VRVP methodology note §2 for the
    body-shape specification and §4 DAO-mirror structural symmetry
    framing. -/
def flashLoanVulnerable : FunctionBody :=
  [FunctionBody.Step.call aaveCallbackTargetAddress ⟨0, by decide⟩,
   FunctionBody.Step.sstore aaveGuardSlot aaveLockedValue,
   FunctionBody.Step.ret true]

/-! ## `aaveContractAdjacent` Contract definition (Layer 6-C Phase 3, Session 40 Unit 3)

    The structurally adjacent vulnerable contract literal differs from
    `aaveContract` (Unit 2) ONLY in the `functions` field — all other
    fields (address, guardSlot, lockedValue, unlockedValue) are
    identical. The structural-adjacency framing makes the boundary case
    argument transparent at reading time: reviewers see two Contract
    records that differ only at `functions`; the predicate's distinct
    decisions on the two contracts isolate the discriminating feature
    to the body shape itself.

    Single-function literal `[flashLoanVulnerable]` mirrors `aaveContract`'s
    single-function literal `[flashLoan]` at the structural symmetry
    layer; the paired-pattern boundary case operates at one-function-
    per-contract granularity for both directions. -/
def aaveContractAdjacent : Contract :=
  { address := aavePoolAddress,
    guardSlot := aaveGuardSlot,
    unlockedValue := aaveUnlockedValue,
    lockedValue := aaveLockedValue,
    functions := [flashLoanVulnerable] }

/-! ## Per-function rejection lemma at `flashLoanVulnerable` (Layer 6-C Phase 3, Session 40 Unit 3)

    Layer 6-C negative-instance per-function lemma at the structurally
    adjacent vulnerable contract. Mirror of Layer 6-A's two falsifications
    at `withdrawRewardFor` and `splitDAO` — same head-element constructor
    disjointness mechanism via the four-tactic reconstruction
    `rintro → unfold → injection → noConfusion`.

    Naming per Naming (b-prime): theorem name carries the contract prefix
    `aaveContractAdjacent_` to disambiguate from Unit 2's per-function
    lemma at `aaveContract`. The paired theorem name structure
    (`_at_aaveContract_flashLoan` for acceptance vs
    `_falsified_at_aaveContractAdjacent_flashLoanVulnerable` for
    rejection) reflects the substantive paired-pattern distinction at
    theorem-name granularity.

    **Proof tactic walkthrough:**

    * `rintro ⟨body, h_eq, _, _⟩`: destructure the
      `IsOZGuardedFunctionGeneral` existential. The two side conditions
      (`NoSStoreOnGuardSlotInSteps` and `NoCallToSelfInSteps`) are
      discarded — the rejection happens at the body-shape equation
      `h_eq` BEFORE side conditions become relevant.
    * `unfold flashLoanVulnerable at h_eq`: reduce to literal body. The
      hypothesis becomes a list-equality between the literal body and
      the predicate's required cons-cell shape.
    * `injection h_eq with h_head _`: list constructor injectivity
      decomposes into head-equality plus tail-equality; `h_head` extracts
      the head equality `.call aaveCallbackTargetAddress _ = .sstore
      aaveContractAdjacent.guardSlot aaveContractAdjacent.lockedValue`.
    * `exact FunctionBody.Step.noConfusion h_head`: auto-generated
      `noConfusion` lemma resolves constructor disjointness `.call ≠
      .sstore`, producing `False` and closing the goal.

    **Independence from Unit 2's per-function lemma:** the rejection
    operates at structurally distinct mechanism layer — Unit 2 applies
    abstract pattern lemma at wrapper-layer absorbing the existential;
    Unit 3 rejects existential at body-shape equation via head-element
    constructor disjointness. Side conditions are never relevant in
    Unit 3's proof. Together they ground Theorem γ (Unit 4 composition
    meta-theorem) at structurally distinct evidence layers — acceptance
    via wrapper-layer absorption + rejection via head-element disjointness.

    Axiom record target: zero-axiom (kernel-only). The proof uses
    `rintro` + `unfold` + `injection` + `exact`/`noConfusion` —
    all kernel operations. No `simp`, no `decide` (not needed —
    rejection is purely structural at constructor layer), no
    `native_decide`.

    See an internal VRVP methodology note §3 for the proof
    tactic walkthrough and §3.2 axiom-record projection. -/
theorem IsOZGuardedFunctionGeneral_falsified_at_aaveContractAdjacent_flashLoanVulnerable :
    ¬ IsOZGuardedFunctionGeneral aaveContractAdjacent flashLoanVulnerable := by
  rintro ⟨body, h_eq, _, _⟩
  unfold flashLoanVulnerable at h_eq
  injection h_eq with h_head _
  exact FunctionBody.Step.noConfusion h_head

/-! ## Theorem α — protocol-by-design positive composition (Layer 6-C Phase 4, Session 41 Unit 1)

    F2-B / Layer 6-C Phase 4 Theorem α: the Aave V3 protocol-by-design
    contract satisfies `OZGuardDisciplineGeneral`. The proof composes
    Session 40 Unit 2's per-function acceptance lemma
    `IsOZGuardedFunctionGeneral_at_aaveContract_flashLoan` (zero-axiom)
    via the predicate's universal-quantification structure at
    contract-level granularity.

    **M-22.2-T1-empirical-instance-4:** This theorem realizes the
    M-22.2 Tier 1 architectural-cleanliness pattern's fourth empirical
    instance after:
    1. Layer 6-A Phase 3 master `daoContract_violates_OZGuardDisciplineGeneral`
       (rejection direction).
    2. Layer 6-A Phase 4 meta-theorem `daoContract_negative_instance_certificate`
       (rejection direction).
    3. Layer 6-B Theorem A `compoundContract_satisfies_OZGuardDisciplineGeneral`
       (acceptance direction).
    4. **This theorem** (structural-neighborhood discrimination at
       acceptance side).

    The fourth empirical instance extends the Tier 1 wrapper-layer
    absorption pattern's empirical evidence from bidirectional
    (Layer 6-A rejection + Layer 6-B acceptance) to **tridirectional**
    (rejection + acceptance + structural-neighborhood discrimination).
    Future post-Layer-6-housekeeping pause point may consider whether
    four-instance evidence strengthens the M-22.2 Tier 1 refinement to
    graduation candidacy.

    Naming per Naming (b-prime): `_at_flashLoan` suffix anchors the
    theorem to its single load-bearing function (vs Layer 6-B's master
    `compoundContract_satisfies_OZGuardDisciplineGeneral` without
    function suffix because Layer 6-B's master covers two functions
    transfer + transferFrom).

    Axiom record target: `[propext]`-only (uses `simp [aaveContract]`
    for membership reduction; mirrors Layer 6-B's master pattern at
    single-function granularity).

    See an internal VRVP methodology note §2 for the proof
    structure specification, §1 architectural symmetry mapping, and
    §2.4 fourth empirical instance documentation. -/
theorem aaveContract_satisfies_OZGuardDisciplineGeneral_at_flashLoan :
    OZGuardDisciplineGeneral aaveContract := by
  refine ⟨?_, ?_⟩
  · -- aaveContract.functions ≠ []
    simp [aaveContract]
  · -- ∀ f ∈ functions, IsOZGuardedFunctionGeneral aaveContract f
    intro f hf
    simp [aaveContract] at hf
    rcases hf with rfl
    exact IsOZGuardedFunctionGeneral_at_aaveContract_flashLoan

/-! ## Theorem β — structurally adjacent negative composition (Layer 6-C Phase 4, Session 41 Unit 1)

    F2-B / Layer 6-C Phase 4 Theorem β: the structurally adjacent
    vulnerable contract violates `OZGuardDisciplineGeneral`. The proof
    composes Session 40 Unit 3's per-function rejection lemma
    `IsOZGuardedFunctionGeneral_falsified_at_aaveContractAdjacent_flashLoanVulnerable`
    (zero-axiom) via the predicate's universal-quantification structure
    at contract-level granularity, mirroring Layer 6-A's master
    rejection proof shape (`daoContract_violates_OZGuardDisciplineGeneral`)
    at the Aave V3 boundary case.

    Proof flow: destructure `OZGuardDisciplineGeneral aaveContractAdjacent`
    as `⟨_h_ne, h_all⟩`; establish flashLoanVulnerable membership;
    apply universal-quantification hypothesis to derive the (refuted)
    per-function predicate; compose with the rejection lemma to derive
    `False`.

    Naming per Naming (b-prime): `_at_flashLoanVulnerable` suffix
    anchors the theorem to the structurally adjacent vulnerable
    function. The paired theorem name structure
    (`aaveContract_satisfies_*_at_flashLoan` vs
    `aaveContractAdjacent_violates_*_at_flashLoanVulnerable`) reflects
    the substantive paired-pattern distinction at theorem-name
    granularity.

    Axiom record target: `[propext]`-only (uses
    `simp [aaveContractAdjacent]` for membership reduction; mirror of
    Layer 6-A's `daoContract_violates_OZGuardDisciplineGeneral` pattern).

    See an internal VRVP methodology note §3 for the proof
    structure specification. -/
theorem aaveContractAdjacent_violates_OZGuardDisciplineGeneral_at_flashLoanVulnerable :
    ¬ OZGuardDisciplineGeneral aaveContractAdjacent := by
  rintro ⟨_h_ne, h_all⟩
  have h_mem : flashLoanVulnerable ∈ aaveContractAdjacent.functions := by
    simp [aaveContractAdjacent]
  exact IsOZGuardedFunctionGeneral_falsified_at_aaveContractAdjacent_flashLoanVulnerable
    (h_all flashLoanVulnerable h_mem)

/-! ## Theorem γ — boundary case composition meta-theorem (Layer 6-C Phase 4, Session 41 Unit 1)

    F2-B / Layer 6-C Phase 4 Theorem γ: the structural-neighborhood
    discriminating-granularity certificate. The certificate's two-
    conjunct structure (`OZGuardDisciplineGeneral aaveContract ∧
    ¬ OZGuardDisciplineGeneral aaveContractAdjacent`) witnesses the
    same predicate deciding differently on two structurally adjacent
    contracts — the discriminating-power claim's structural-neighborhood
    granularity argument's load-bearing terminus at Layer 6-C boundary
    case.

    The two contracts (`aaveContract` and `aaveContractAdjacent`)
    differ ONLY in the `functions` field — same address, same guardSlot,
    same lockedValue, same unlockedValue. The predicate's distinct
    decisions isolate the discriminating feature to the body shape
    itself: protocol-by-design (CEI-correct, head SSTORE before CALL)
    accepts; structurally adjacent vulnerable (CEI-violation, SSTORE-
    after-CALL DAO-mirror) rejects.

    Together with `daoContract_negative_instance_certificate` from
    Layer 6-A and `compoundContract_positive_instance_certificate`
    from Layer 6-B, the **tridirectional** discriminating-power claim
    is structurally grounded:
    - Rejection at deployed historical reference (DAO 2016).
    - Acceptance at deployed production reference (cDAI's Compound v2
      cToken family).
    - Structural-neighborhood discrimination at boundary case (Aave V3
      protocol-by-design vs adjacent vulnerable).

    Direct anonymous-constructor composition. Axiom record target:
    `[propext]`-only (inherited from α and β via direct conjunction;
    no new tactics introduce additional axioms).

    See an internal VRVP methodology note §4 for the
    composition specification and §5 boundary case structural framing
    per Question 8e Framing (a). -/
theorem aaveBoundaryCase_certificate :
    OZGuardDisciplineGeneral aaveContract ∧
    ¬ OZGuardDisciplineGeneral aaveContractAdjacent :=
  ⟨aaveContract_satisfies_OZGuardDisciplineGeneral_at_flashLoan,
   aaveContractAdjacent_violates_OZGuardDisciplineGeneral_at_flashLoanVulnerable⟩

end QanaryContracts
