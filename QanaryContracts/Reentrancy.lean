/-
  QanaryContracts/Reentrancy.lean

  Two reentrancy predicates over execution traces:

  1. `ReentrancyVulnerable` — the *structural* predicate (Phase 2):
     two CALLs into the same address with the second nested inside
     the first's still-open frame.

  2. `ReentrancyVulnerableStateful` — the *state-aware* refinement
     (Phase 3, Priority 1, 2026-04-27):
     adds the requirement that at the moment of the reentrant CALL,
     the called contract's *guard slot* is in its UNLOCKED value.

  The state-aware form is what the frozen claim's theorems will be
  about. It instantiates cleanly to OpenZeppelin's `ReentrancyGuard.sol`:
     OZ guard slot = `_status`
     OZ unlocked   = `_NOT_ENTERED` (= 1 in v4+; was 0 in v3)
     OZ locked     = `_ENTERED`     (= 2 in v4+; was 1 in v3)
     The parameterization handles both versions cleanly.

  Per Phase 1 § 1 Q5 / 2026-04-26: predicate is over `ExecutionTrace`,
  not over a `Contract` type. Real-protocol theorems will introduce a
  lightweight `Contract` record at the application level later.
-/
import QanaryContracts.EVM
import QanaryContracts.Storage
import QanaryContracts.Step
import QanaryContracts.Contract

namespace QanaryContracts

/-! ## Structural reentrancy predicate -/

/-- A trace exhibits reentrancy iff there exist two CALL steps targeting
    the same contract address `a`, with the second CALL nested inside
    the first one's still-open frame.

    This is the *structural* characterization. It captures the necessary
    call-graph topology of every known reentrancy attack (DAO, Euler,
    Curve-Vyper, Penpie, ...) but does not yet rule out benign nested
    self-calls where state has been correctly updated. The state-aware
    refinement is added alongside the soundness theorem. -/
def ReentrancyVulnerable (tr : ExecutionTrace) : Prop :=
  ∃ (a : Address) (i j : Nat),
    i < j ∧ j < tr.length ∧
    (∃ caller₁ value₁, tr[i]? = some (EVMStep.call caller₁ a value₁)) ∧
    (∃ caller₂ value₂, tr[j]? = some (EVMStep.call caller₂ a value₂)) ∧
    NestedAfter tr i j

/-! ## Bool-valued witness checker

For decidable witness construction on concrete traces, we provide a
Bool form parameterized by the witness `(a, i, j)`. The user supplies
the witness; the predicate then reduces to a concrete computation. -/

/-- Bool form of the reentrancy witness for an explicit `(a, i, j)`. -/
def hasReentrancyWitness
    (tr : ExecutionTrace) (a : Address) (i j : Nat) : Bool :=
  decide (i < j) &&
  decide (j < tr.length) &&
  (match tr[i]? with
    | some (EVMStep.call _ b _) => decide (b = a)
    | _ => false) &&
  (match tr[j]? with
    | some (EVMStep.call _ b _) => decide (b = a)
    | _ => false) &&
  decide (NestedAfter tr i j)

/-! ## State-aware reentrancy predicate (Phase 3, Priority 1)

The structural predicate above flags every reentrant CALL pair, even
benign ones where the contract has correctly set its guard. The
state-aware refinement adds: *at the moment of the reentrant CALL,
the guard slot of the called contract is observed in its UNLOCKED
state.*

Why this matters: a contract that correctly implements the OZ
`ReentrancyGuard` cannot generate a trace where the guard is unlocked
during a reentrant call into a guarded function — the entry check
would have reverted. So the only way `ReentrancyVulnerableStateful`
holds on a valid trace is if the contract *does not* properly use
the guard. This is the lever for the universal soundness theorem.
-/

/-- Lookup the guard-slot value of address `a` at trace position `k`. -/
def guardSlotAt (s₀ : EVMState) (tr : ExecutionTrace) (k : Nat)
    (a : Address) (slot : Word256) : Word256 :=
  slotAt s₀ tr k a slot

/-- The state-aware reentrancy predicate, parameterized by which slot
    of the called contract is the guard, and which `Word256` value
    indicates UNLOCKED.

    Holds on `tr` (relative to initial state `s₀`) iff there is a
    structural reentrancy pattern AND, at the moment of the reentrant
    CALL, the called contract's guard slot is in its UNLOCKED value.

    OpenZeppelin v4+ instantiation:
      `ReentrancyVulnerableStateful s₀ tr OZ_STATUS_SLOT OZ_NOT_ENTERED`
    where `OZ_STATUS_SLOT` is the contract's `_status` slot index and
    `OZ_NOT_ENTERED = 1`.

    OpenZeppelin v3 instantiation: `unlockedValue = 0` (Boolean guard).
-/
def ReentrancyVulnerableStateful
    (s₀ : EVMState) (tr : ExecutionTrace)
    (guardSlot unlockedValue : Word256) : Prop :=
  ∃ (a : Address) (i j : Nat),
    i < j ∧ j < tr.length ∧
    (∃ caller₁ value₁, tr[i]? = some (EVMStep.call caller₁ a value₁)) ∧
    (∃ caller₂ value₂, tr[j]? = some (EVMStep.call caller₂ a value₂)) ∧
    NestedAfter tr i j ∧
    guardSlotAt s₀ tr j a guardSlot = unlockedValue

/-- Bool form of the state-aware reentrancy witness for an explicit
    `(a, i, j, guardSlot, unlockedValue)`. Decidable on concrete traces. -/
def hasStatefulReentrancyWitness
    (s₀ : EVMState) (tr : ExecutionTrace)
    (a : Address) (i j : Nat)
    (guardSlot unlockedValue : Word256) : Bool :=
  hasReentrancyWitness tr a i j &&
  decide (guardSlotAt s₀ tr j a guardSlot = unlockedValue)

/-! ## C-specific reentrancy predicate (Phase 4 Session 6)

Per Ray's 2026-04-27 Decision 1 (post-Session-5): the universal-`a`
predicate `ReentrancyVulnerableStateful` is *over-eager* — its
existential `a` is unconstrained, allowing a reentrancy on a
*different* contract to fire the predicate with `C`'s guard
parameters (the Phase 4 Session 4 wall).

The C-specific variant restricts `a := C.address`: the witness's
reentered contract MUST be `C` itself. This is the precondition
for the substantive Theorem 5 proof.

The original `ReentrancyVulnerableStateful` is preserved for
backward compatibility with Phase 2/3 lemmas that depended on
the unrestricted form. -/

/-- C-specific state-aware reentrancy: the witness's reentered
    contract is `C.address` itself.

    Holds on `tr` (relative to initial state `s₀`) iff there is a
    structural reentrancy pattern *into `C`* AND, at the moment
    of the reentrant CALL into `C`, the guard slot of `C` is in
    its unlocked value.

    Concrete instantiation (no `guardSlot`/`unlockedValue` params —
    they come from `C` directly): -/
def ReentrancyVulnerableStatefulOn
    (C : Contract) (s₀ : EVMState) (tr : ExecutionTrace) : Prop :=
  ∃ (i j : Nat),
    i < j ∧ j < tr.length ∧
    (∃ caller₁ value₁, tr[i]? = some (EVMStep.call caller₁ C.address value₁)) ∧
    (∃ caller₂ value₂, tr[j]? = some (EVMStep.call caller₂ C.address value₂)) ∧
    NestedAfter tr i j ∧
    guardSlotAt s₀ tr j C.address C.guardSlot = C.unlockedValue

end QanaryContracts
