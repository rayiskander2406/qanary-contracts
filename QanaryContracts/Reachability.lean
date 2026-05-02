/-
  QanaryContracts/Reachability.lean

  Phase 4 Session 7.1 — Fix A applied (per Ray's 2026-04-27
  Decision 7, post-Session-7-wall round). The Session 6 implementation
  of Track A.2 omitted ordered body conformance and used a
  `callee ≠ C.address`-restricted call-locked conjunct, which admitted
  the W3 self-unlock-reentry attack:

      [0] call EOA C 0  [1] sstore C g lockedValue
      [2] sstore C g unlockedValue  [3] call C C 0  [4] sstore C g lockedValue

  Captured in `OZSoundness.lean` as `weak_rto_admits_self_unlock_reentry`.
  Fix A drops the `callee ≠ C.address` clause: every C-issued CALL,
  regardless of callee, must have guard = lockedValue.

  `ReachableTraceOf` now carries:

    1. `InitialGuardUnlocked C s₀` (Phase 4 Session 2 / Track A.1)
    2. `ValidExecution tr` (structural prereq, was implicit before)
    3. **Entry-revert** — every CALL into `C.address` requires
       guard ≠ `C.lockedValue` at that position. (Phase 4 Session 6)
    4. **C-call-locked (Fix A, Session 7.1):** every CALL with
       `caller = C.address` (to *any* callee, self or external)
       requires guard = `C.lockedValue` at that position.
    5. **C-frame-starts-with-lock** — every CALL into `C.address`
       is immediately followed by `sstore C.address C.guardSlot
       C.lockedValue` in the trace. (Phase 4 Session 6)

  Together these constraints encode the OZ guard discipline at the
  trace level: no reachable trace can violate the
  lock-at-entry / locked-during-any-C-issued-call / lock-immediately-
  after-entry protocol.

  ARITY UNCHANGED from Session 2:
      ReachableTraceOf : Contract → EVMState → ExecutionTrace → Prop

  Per Ray's 2026-04-27 Session 5 prework + Session 6 spec + Session 7.1
  Fix A.
-/
import QanaryContracts.EVM
import QanaryContracts.Storage
import QanaryContracts.Step
import QanaryContracts.CEI
import QanaryContracts.Contract
import QanaryContracts.ValidExecution
import QanaryContracts.DAOAttack

namespace QanaryContracts

/-! ## `InitialGuardUnlocked` — initial-state constraint

The canonical entry-state for a guard-disciplined contract: when
execution begins, the guard slot at `C.address` must read as
`C.unlockedValue`. -/

/-- The initial-state guard constraint for contract `C`: at the
    initial state `s₀`, the guard slot of `C.address` reads as
    `C.unlockedValue`. -/
def InitialGuardUnlocked (C : Contract) (s₀ : EVMState) : Prop :=
  s₀.lookupSlot C.address C.guardSlot = C.unlockedValue

/-! ## Track A.2 trace-level constraints (Phase 4 Session 6)

Three new conjuncts, all over `Fin tr.length` to keep
decidability-friendly. -/

/-- **Entry-revert constraint:** every CALL into `C.address` in
    the trace requires the guard slot of `C` at that position to
    NOT equal `C.lockedValue`.

    Models the OZ guard's revert-if-locked behavior at function
    entry. A reentrant call arriving while the guard is locked
    cannot be a "reachable" execution because the contract would
    have reverted. -/
def TraceEntryRevert (C : Contract) (s₀ : EVMState) (tr : ExecutionTrace) : Prop :=
  ∀ k : Fin tr.length, ∀ caller value,
    tr[k.val]? = some (EVMStep.call caller C.address value) →
    guardSlotAt s₀ tr k.val C.address C.guardSlot ≠ C.lockedValue

/-- **C-call-locked constraint (Fix A, Session 7.1):** whenever `C`
    issues a CALL (caller = `C.address`, *any* callee — self or
    external), the guard slot of `C` is `C.lockedValue` at that
    position.

    Models the OZ guard's "lock before any C-issued call" requirement,
    consistent with `nonReentrant` decorators wrapping every external
    interaction. The Session-6 version restricted this to
    `callee ≠ C.address`; the W3 self-unlock-reentry wall
    (`OZSoundness.weak_rto_admits_self_unlock_reentry`) showed that
    restriction admits a reentrancy attack via self-call after a
    mid-frame unlock SSTORE. -/
def TraceCCallLocked (C : Contract) (s₀ : EVMState)
    (tr : ExecutionTrace) : Prop :=
  ∀ k : Fin tr.length, ∀ callee value,
    tr[k.val]? = some (EVMStep.call C.address callee value) →
    guardSlotAt s₀ tr k.val C.address C.guardSlot = C.lockedValue

/-- **C-frame-starts-with-lock constraint:** every CALL into
    `C.address` is immediately followed (at the next trace
    position) by `sstore C.address C.guardSlot C.lockedValue`.

    Models the OZ guard's "first action of any guarded function
    is to lock." Combined with the above two constraints, this
    closes the wall: any reachable trace's structure forces the
    guard to be locked during nested executions, blocking
    reentrancy. -/
def TraceCFrameStartsWithLock (C : Contract) (tr : ExecutionTrace) : Prop :=
  ∀ k : Fin tr.length, ∀ caller value,
    tr[k.val]? = some (EVMStep.call caller C.address value) →
    tr[k.val + 1]? = some (EVMStep.sstore C.address C.guardSlot C.lockedValue)

/-! ## `NoPhantomCalls` — Phase 5 Session 11 (W8 P3 resolution)

Foundation-layer hypothesis required for the F4 lift theorem
`ozGuardDiscipline_implies_RTO`. Closes the W8 phantom-CALL gap
named in Session 9, mechanically witnessed in Session 10
(`QanaryContracts/W8.lean`), and resolved here via P3
antecedent extension.

W8: `CallsFromTopFrame`'s OR-`none` clause permits CALLs with
`caller = C.address` while `currentFrameAt tr k = none` (stack
empty). The OR-`none` clause is load-bearing for legitimate
EOA-entry CALLs (k=0 with caller=EOA), so it cannot be tightened
without breaking entry semantics. The precise refinement is to
require, *as a hypothesis on the lift theorem*, that any CALL
with caller=C.address has C on top of the stack — i.e., no
phantom CALLs originating from C. -/

/-- **No-phantom-call constraint (W8 P3 resolution):** every CALL
    with `caller = C.address` has `C.address` on top of the call
    stack at that position.

    Models the EVM-semantic guarantee that a CALL opcode's caller
    field is the currently-executing contract. Discharged at
    deployment time per-protocol (Layer 6 P4 work). For abstract
    traces, it is an explicit hypothesis on the F4 lift theorem.

    *Minimal* negation of the W8 phantom-CALL counter-example:
    `phantomCallTrace` (`QanaryContracts/W8.lean`) violates this at
    `k=6` (caller=C, currentFrameAt=none). -/
def NoPhantomCalls (C : Contract) (tr : ExecutionTrace) : Prop :=
  ∀ k : Fin tr.length, ∀ callee value,
    tr[k.val]? = some (EVMStep.call C.address callee value) →
    currentFrameAt tr k.val = some C.address

/-! ## `ReachableTraceOf` — Phase 4 Session 7.1 (Track A.2 + Fix A)

A trace is reachable from `C` starting at `s₀` iff all five
conjuncts hold. Per Session 5 VRVP + Session 7.1 Fix-A re-VRVP, this
combination closes the wall: hand-construction of an OZ-disciplined
`C` with a counter-example fails because **either** entry-revert
contradicts the lock that lands immediately after the prior entry,
**or** `TraceCCallLocked` blocks any C-issued CALL whose guard is
unlocked (including self-calls that the Session-6 restricted version
admitted). -/

/-- `ReachableTraceOf C s₀ tr` — the trace `tr` (executing from
    initial state `s₀`) is a possible execution sequence for
    contract `C`. Phase 4 Session 7.1 (Track A.2 + Fix A):
    five-conjunct trace-level OZ guard discipline, with C-issued
    CALLs (any callee) requiring a locked guard. -/
def ReachableTraceOf (C : Contract) (s₀ : EVMState)
    (tr : ExecutionTrace) : Prop :=
  InitialGuardUnlocked C s₀ ∧
  ValidExecution tr ∧
  TraceEntryRevert C s₀ tr ∧
  TraceCCallLocked C s₀ tr ∧
  TraceCFrameStartsWithLock C tr

/-! ## Negative results — placeholder still broken (and now more so) -/

/-- Concrete v4-style contract used to witness the negative result. -/
def negativeWitnessContract : Contract :=
  Contract.ozV4 daoVictim ⟨1, by decide⟩

theorem not_initialGuardUnlocked_v4_empty :
    ¬ InitialGuardUnlocked negativeWitnessContract EVMState.empty := by
  intro h
  unfold InitialGuardUnlocked EVMState.lookupSlot EVMState.empty
    negativeWitnessContract Contract.ozV4 at h
  simp [Finmap.lookup_empty] at h
  exact absurd h (by decide)

/-- The placeholder is broken — there is no universal proof of
    `∀ C s₀ tr, ReachableTraceOf C s₀ tr`. Witness: the v4-style
    `negativeWitnessContract` at `EVMState.empty` violates
    `InitialGuardUnlocked` (just one of the now five RTO
    conjuncts). -/
theorem not_reachableTraceOf_universal :
    ¬ (∀ (C : Contract) (s₀ : EVMState) (tr : ExecutionTrace),
         ReachableTraceOf C s₀ tr) := by
  intro hAll
  -- Pick the v4 witness contract + empty state + empty trace
  have hRTO := hAll negativeWitnessContract EVMState.empty []
  -- Extract InitialGuardUnlocked from the conjunction
  obtain ⟨hInit, _⟩ := hRTO
  exact not_initialGuardUnlocked_v4_empty hInit

end QanaryContracts
