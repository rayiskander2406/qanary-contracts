/-
  QanaryContracts/Contract.lean

  Application-level `Contract` record. Phase 3 Session 2 (2026-04-27).

  Per Phase 1 § 1 Q5: a `Contract` type is NOT needed at the foundation
  level — universal predicates over `ExecutionTrace` already work without
  it. We introduce `Contract` here as the *application-level* bundle:
  it carries an address (the contract's identity) and the OZ-style guard
  policy (which storage slot is the guard, what value indicates UNLOCKED).

  This bundle is what the `ReentrancyFree` predicate quantifies over.
  Real-protocol theorems (Phase 4+: Curve, Pendle, Compound) instantiate
  `Contract` with the protocol's actual `_status` slot and guard semantics.
-/
import QanaryContracts.EVM
import QanaryContracts.Storage
import QanaryContracts.FunctionBody

namespace QanaryContracts

/-- A contract participating in the reentrancy-safety theorem.

    Fields:
    * `address`        — the contract's EVM address (its on-chain identity).
    * `guardSlot`      — the storage slot used as the OZ-style mutex.
    * `unlockedValue`  — the `Word256` value that indicates "not entered".
    * `lockedValue`    — the `Word256` value that indicates "entered".
                          Companion to `unlockedValue`; needed for the
                          guard-discipline hypothesis in the substantive
                          (non-vacuous) Phase 4 soundness theorem
                          (`cei_implies_no_reentrancy_v2`). The OZ guard
                          discipline writes `lockedValue` to `guardSlot`
                          before the external call and `unlockedValue`
                          after.

    For OpenZeppelin v4+ instantiation:
      `guardSlot     = keccak256("openzeppelin.utils.ReentrancyGuard._status")`
      `unlockedValue = 1` (`_NOT_ENTERED`)
      `lockedValue   = 2` (`_ENTERED`)
    For OpenZeppelin v3 (Boolean) instantiation:
      `unlockedValue = 0` (false)
      `lockedValue   = 1` (true)

    The parameterization preserves the frozen claim's "OpenZeppelin's
    `ReentrancyGuard.sol`" wording across both major library versions. -/
structure Contract where
  address       : Address
  guardSlot     : Word256
  unlockedValue : Word256
  lockedValue   : Word256
  /-- Phase 4 Session 4 (Track A.2 foundation): the contract's
      declared function bodies. Constrains `ReachableTraceOf` to
      execution paths derivable from the contract's actual code,
      preventing the hand-construction attack that defeated
      Track A.1 (Phase 4 Session 3 wall). Per Ray's 2026-04-27
      Decision 2. -/
  functions     : List FunctionBody
  deriving DecidableEq, Repr

namespace Contract

/-- Convenience constructor for a v4+-style OZ contract using slot index `s`.
    `unlockedValue = 1` (_NOT_ENTERED), `lockedValue = 2` (_ENTERED).
    `functions` defaults to `[]`; downstream code that needs declared
    bodies should construct a `Contract` literal directly. -/
def ozV4 (a : Address) (s : Word256) : Contract :=
  { address := a, guardSlot := s,
    unlockedValue := ⟨1, by decide⟩,
    lockedValue   := ⟨2, by decide⟩,
    functions     := [] }

/-- Convenience constructor for a v3-style (Boolean) OZ contract using slot
    index `s`. `unlockedValue = 0` (false), `lockedValue = 1` (true). -/
def ozV3 (a : Address) (s : Word256) : Contract :=
  { address := a, guardSlot := s,
    unlockedValue := ⟨0, by decide⟩,
    lockedValue   := ⟨1, by decide⟩,
    functions     := [] }

end Contract

end QanaryContracts
