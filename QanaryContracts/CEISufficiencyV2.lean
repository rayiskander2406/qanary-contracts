/-
  QanaryContracts/CEISufficiencyV2.lean

  Phase 4 Session 2 — Theorem 2 v2 STATEMENT, awaiting substantive proof.

  ******************** WHY THIS FILE WAS REFACTORED ********************

  Phase 4 Session 1 stated v2 as a `theorem` with a vacuous proof
  that depended on `reachableTraceOf_placeholder_universal`
  (ReachableTraceOf := True). Phase 4 Session 2 (Track A.1)
  refined `ReachableTraceOf` to `InitialGuardUnlocked C s₀`, which:

    1. Changed the arity of `ReachableTraceOf` from
       `Contract → ExecutionTrace → Prop` to
       `Contract → EVMState → ExecutionTrace → Prop`.
    2. Made `reachableTraceOf_placeholder_universal` unprovable
       (witnessed mechanically by `not_reachableTraceOf_universal`
       in `Reachability.lean`).

  The Session 1 vacuous proof of `cei_implies_no_reentrancy_v2`
  failed to compile with three concrete errors:

      :92:15  type expected, got (ReachableTraceOf C tr : ExecutionTrace → Prop)
      :101:35 daoAttackTrace has type ExecutionTrace but expected EVMState
      :103:2  No goals to be solved

  This is the **audit gate firing**: the build refused to claim
  v2 was proved once the placeholder it depended on was refined
  to a non-trivial Prop. Per Ray's Decision 5 (2026-04-27),
  this mechanism is named "Build-Gated Proof Development" and is
  a methodology contribution captured in the internal methodology notes.

  ******************** WHAT THIS FILE NOW HOLDS ********************

  Per Ray's Session 2 instruction "Do NOT attempt the full
  cei_implies_no_reentrancy_v2 proof until InitialGuardUnlocked
  is confirmed to break the placeholder" — the breakage is now
  confirmed (see an internal phase report § "Did the placeholder
  break?"). The substantive proof is the Phase 4 Session 3+
  deliverable.

  To return the build to green WITHOUT writing the substantive
  proof and WITHOUT using `sorry` (which R2 forbids), we capture
  v2 as a `def : Prop` — a Prop-valued definition. This compiles
  and locks in the statement's type signature, but does NOT claim
  the statement is true. Session 3+ will write:

      theorem cei_implies_no_reentrancy_v2 (C : Contract) :
          cei_implies_no_reentrancy_v2_target C := by
        ...substantive proof using InitialGuardUnlocked...

  This is the minimum-honesty refactor: no theorem claim is made,
  no `sorry` hides the gap, and the build is the audit gate.
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
import QanaryContracts.Reachability
import QanaryContracts.CEISufficiency

namespace QanaryContracts

/-! ## v2 statement target — Prop-valued, not a theorem claim

`cei_implies_no_reentrancy_v2_target C` is a Prop describing what
the v2 soundness theorem says. It is NOT a claim that the Prop is
true — Lean accepts it as a well-typed Prop without requiring a
proof. Session 3+ will state and prove the theorem
`cei_implies_no_reentrancy_v2 C : cei_implies_no_reentrancy_v2_target C`.

Until then, this file holds only the type. The audit gate is the
absence of a `theorem` declaration: there is nothing to be made
unsoundly true. -/

/-- **Theorem 2 v2 statement target** (Phase 4, Track A.1).
    *Reading*: if every reachable, valid trace of `C` satisfies CEI,
    then `C` is reentrancy-free.

    **Status:** Prop type captured. Substantive proof is a Phase 4
    Session 3+ deliverable. The proof must use `InitialGuardUnlocked`
    (now embedded in `ReachableTraceOf`) to bridge from CEI to the
    guard-discipline contradiction.

    **Migration plan (Session 3+):**

    ```lean
    theorem cei_implies_no_reentrancy_v2 (C : Contract) :
        cei_implies_no_reentrancy_v2_target C := by
      intro h s₀ tr hvalid hvuln
      -- 1. Apply h to (s₀, tr) given a ReachableTraceOf proof.
      -- 2. ReachableTraceOf reduces to InitialGuardUnlocked C s₀.
      -- 3. Combine InitialGuardUnlocked + hvuln (guard reads as
      --    unlockedValue at reentry) → guard was set then unset
      --    in C's frame → SSTORE-after-CALL pattern → CEIViolated.
      -- 4. Contradicts h's conclusion.
      ...
    ```

    The (R3)/(R4) function-body case (guard-less contracts) is
    Track A.2 / Session 4+. -/
def cei_implies_no_reentrancy_v2_target (C : Contract) : Prop :=
  (∀ (s₀ : EVMState) (tr : ExecutionTrace),
     ReachableTraceOf C s₀ tr →
     ValidExecution tr →
     SatisfiesCEI tr) →
  ReentrancyFree C

/-! ## ⚠️ Phase 4 Session 3 — WALL DISCOVERED

Before attempting the `guard_locked_before_call` lemma (Track A.1
substantive proof), we tested whether Track A.1 actually delivers
soundness content. **It does not.** This section formalizes the
wall.

### The wall

The Session 2 placeholder breakage was at the LITERAL Session 1
proof site — an arity mismatch made `reachableTraceOf_placeholder_universal C daoAttackTrace`
syntactically ill-typed. But the underlying vacuity was not
removed. Specifically: for any contract `C`, we can CONSTRUCT an
initial state `s₀_initial C` (a singleton Finmap) such that
`InitialGuardUnlocked C (s₀_initial C)` holds by direct
computation. Combined with `daoAttackTrace_validExecution` and
`daoAttackTrace_violates_cei` (Phase 3 Session 3 results), this
gives:

    H = (∀ s₀ tr, ReachableTraceOf C s₀ tr → ValidExecution tr → SatisfiesCEI tr)
    ↓ instantiate with (s₀_initial C, daoAttackTrace)
    InitialGuardUnlocked C (s₀_initial C)  -- ✓ by construction
    ⟹ ReachableTraceOf C (s₀_initial C) daoAttackTrace
    ValidExecution daoAttackTrace  -- ✓ Phase 3 S3
    ⟹ SatisfiesCEI daoAttackTrace
    ⟹ contradiction with daoAttackTrace_violates_cei

So `H` is GLOBALLY INCONSISTENT under Track A.1, just as it was
under v1. The v2 theorem `H → ReentrancyFree C` is therefore
**vacuously provable for every `C`**, and Track A.1 has delivered
no substantive soundness content.

### Why this happened

Track A.1 only constrains `s₀` (the initial guard state). It does
NOT constrain the TRACE STRUCTURE relative to `C`. The
counter-trace `daoAttackTrace` is "about" `daoAttacker` and
`daoVictim`, not necessarily about `C` — but the v2 hypothesis
universally quantifies over traces, so it applies. Once the
hypothesis applies, its contradictions (CEI failures on
`daoAttackTrace`) make `H` provably false for any `C`.

To make v2 non-vacuous, `ReachableTraceOf C s₀ tr` must **also
constrain `tr` to be a trace `C` could plausibly execute** — i.e.,
SSTOREs on `C.address`'s storage must correspond to writes
declared in `C`'s function bodies, CALLs from `C.address` must be
declared external calls in `C`'s function bodies, and so on. This
is **Track A.2** (function-body model), originally scheduled for
Session 4+.

### The mechanical demonstration

`hypothesis_H_v2_is_still_inconsistent` formalizes the wall: under
Track A.1, the v2 hypothesis remains globally inconsistent. This
is a positive Lean theorem with real content (it documents what's
wrong). It is the Phase 4 Session 3 deliverable.

The `guard_locked_before_call` lemma is NOT attempted in this
session — it would close in some traces but the *theorem it
serves* is vacuously true under Track A.1, so the lemma's proof
would not deliver any soundness content. The right move is to
escalate to Track A.2, which is what this report does.
-/

/-- A specifically-constructed `EVMState` where `C`'s guard slot
    reads as `C.unlockedValue`. Used to show that `InitialGuardUnlocked C`
    is ALWAYS satisfiable for any `C`, by hand-construction. -/
noncomputable def s₀_initial (C : Contract) : EVMState :=
  Finmap.singleton C.address (Finmap.singleton C.guardSlot C.unlockedValue)

/-- For every `C`, `s₀_initial C` satisfies `InitialGuardUnlocked`.
    This is provable by direct unfolding of `lookupSlot` against
    the singleton Finmap construction.

    **Significance:** this lemma shows that Track A.1's constraint
    is *trivially satisfiable* — there is no contract `C` for which
    `InitialGuardUnlocked` cannot be enforced by choosing `s₀`
    appropriately. Therefore Track A.1 cannot prevent the v1
    inconsistency proof from being re-run with a constructed `s₀`. -/
theorem s₀_initial_satisfies_initialGuardUnlocked (C : Contract) :
    InitialGuardUnlocked C (s₀_initial C) := by
  unfold InitialGuardUnlocked EVMState.lookupSlot s₀_initial Storage.lookupZ
  simp [Finmap.lookup_singleton_eq]

/-! **Phase 4 Session 6 — `hypothesis_H_v2_is_still_inconsistent`
    has been DELETED.**

    Why: under Phase 4 Session 6's Track A.2 cascade,
    `ReachableTraceOf C s₀ tr` requires four trace-level
    constraints beyond `InitialGuardUnlocked` (entry-revert,
    C-external-call-locked, C-frame-starts-with-lock,
    `ValidExecution`). The former proof — building `ReachableTraceOf`
    from just `s₀_initial_satisfies_initialGuardUnlocked` — no
    longer typechecks (the application returns
    `InitialGuardUnlocked` but is expected to return
    `ReachableTraceOf`'s now-larger conjunction).

    This is the build-gate firing as designed: Track A.2 closes
    the loophole that the Phase 4 Session 3 theorem documented.
    The theorem no longer reflects reality and is removed. -/

/-! ### Note: NOT committing a vacuous v2 theorem

We deliberately do NOT add a `theorem cei_implies_no_reentrancy_v2`
that exploits `hypothesis_H_v2_is_still_inconsistent` to get a
vacuous proof. Per Ray's Decision 5 (2026-04-27, "Build-Gated
Proof Development"), the build should succeed iff the proof is
mathematically *honest*. A vacuous v2 theorem would be technically
true but methodologically misleading — it would advertise
"v2 proved" while delivering no soundness content.

Instead, the v2 statement remains a `def : Prop`
(`cei_implies_no_reentrancy_v2_target`); the wall is documented
mechanically by `hypothesis_H_v2_is_still_inconsistent`; and the
substantive proof migrates to **Phase 4 Session 4 (Track A.2)**
where `ReachableTraceOf` will be refined to constrain trace
structure relative to `C`'s function bodies. -/

end QanaryContracts
