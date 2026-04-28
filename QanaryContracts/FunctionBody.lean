/-
  QanaryContracts/FunctionBody.lean

  Phase 4 Session 4 — Track A.2 foundation. Defines the
  declarative function-body model that `Contract.functions` will
  hold. Per Ray's 2026-04-27 Decision 2: "Contract.functions
  constrains reachable traces to execution paths derivable from
  the contract's actual code. This prevents the hand-construction
  attack that defeated Track A.1 — an arbitrary s₀ cannot be
  paired with an arbitrary trace and claim reachability from this
  contract."

  Scope: a function body is a list of declarative steps the
  contract executes when its function is invoked. We mirror the
  EVM step set (`EVMStep`), with two adjustments:

    * SSTORE has no `addr` field — when C executes the step, it
      writes to its own storage (`C.address`). The EVM-level step
      will be `EVMStep.sstore C.address key val`.

    * CALL has no `caller` field — when C issues the step, the
      caller is `C.address`. The EVM-level step will be
      `EVMStep.call C.address callee value`.

  Conditional control flow (revert-if-locked entry checks etc.) is
  NOT modeled at this layer. Phase 4 Session 4 enforces guard
  discipline as a *property* of the function body (every body
  follows lock → ... → unlock → ret pattern); the entry-revert
  guard is enforced at the trace level via `ReachableTraceOf`'s
  reachability constraint.
-/
import QanaryContracts.EVM
import QanaryContracts.Storage

namespace QanaryContracts

/-- A single step in a function body declaration. Mirrors `EVMStep`
    minus the implicit caller/owner (which is the contract executing
    the body). -/
inductive FunctionBody.Step where
  /-- `sstore key val` — write `val` to the contract's own slot `key`. -/
  | sstore (key val : Word256) : Step
  /-- `call callee value` — issue an external call to `callee` with
      `value` wei from the contract's frame. -/
  | call (callee : Address) (value : Word256) : Step
  /-- `ret success` — exit the current function frame. -/
  | ret (success : Bool) : Step
  /-- `revert` — abort and roll back. -/
  | revert : Step
  deriving DecidableEq, Repr

/-- A function body is a finite ordered list of declarative steps. -/
abbrev FunctionBody := List FunctionBody.Step

end QanaryContracts
