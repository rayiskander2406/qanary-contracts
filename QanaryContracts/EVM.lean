/-
  QanaryContracts/EVM.lean

  Minimal EVM execution model for the QANARY Contracts paper. This file
  defines the smallest set of EVM concepts sufficient to express the
  reentrancy property and witness the DAO attack.

  Per Phase 1 / Decision 3 (2026-04-26 hybrid plan): roll-our-own minimal
  model in Phase 2; correspondence to EVMYulLean proven in Phase 3.

  Scope of opcodes:  SSTORE, CALL, RETURN, REVERT.
  Out of scope:      gas, memory, calldata, delegatecall, create, the rest
                     of the ~140-opcode instruction set. None of these
                     affect the call-frame structural property of reentrancy.

  Mathlib-free for the first deliverable. Mathlib (Finmap) becomes
  load-bearing for `Storage`/`EVMState` and the eventual state-aware
  refinement; that lives in later files in this library.
-/

namespace QanaryContracts

/-! ## Address space and word size -/

/-- Ethereum address: 160-bit identifier. Concrete witnesses must
    instantiate `Fin (2^160)` explicitly; the type is too large to
    enumerate by `decide`. -/
abbrev Address : Type := Fin (2 ^ 160)

/-- 256-bit machine word: storage keys and storage values. -/
abbrev Word256 : Type := Fin (2 ^ 256)

/-! ## Execution steps and traces -/

/-- A single observable step of EVM execution. Minimal opcode set
    sufficient to characterize reentrancy. -/
inductive EVMStep where
  /-- `sstore addr key val` — write `val` to slot `key` of contract
      `addr`'s storage. -/
  | sstore (addr : Address) (key val : Word256) : EVMStep
  /-- `call caller callee value` — `caller` invokes `callee`, transferring
      `value` wei. Opens a new call frame. -/
  | call (caller callee : Address) (value : Word256) : EVMStep
  /-- `ret success` — successful exit of the current call frame. -/
  | ret (success : Bool) : EVMStep
  /-- `revert` — unsuccessful exit of the current call frame. -/
  | revert : EVMStep
  deriving DecidableEq, Repr

/-- A finite execution trace is a list of steps. -/
abbrev ExecutionTrace : Type := List EVMStep

/-! ## Frame-depth computation

Reentrancy is fundamentally a property of *call-frame nesting*. Rather
than reify a `CallStack` field in the state and thread it through a Step
relation (deferred to later phases), we compute frame depth directly
from the trace prefix. This is equivalent and keeps the first deliverable
lightweight.
-/

/-- The depth-delta of a single step. CALL opens a frame (+1); RETURN
    and REVERT close one (−1); SSTORE is depth-neutral (0). -/
@[inline]
def EVMStep.depthDelta : EVMStep → Int
  | .call _ _ _   => 1
  | .ret _        => -1
  | .revert       => -1
  | .sstore _ _ _ => 0

/-- `frameDepth tr` is the cumulative depth-delta of executing every
    step in `tr`. In a well-formed *complete* trace this returns to 0;
    the predicate permits unbalanced traces (partial executions). -/
def frameDepth (tr : ExecutionTrace) : Int :=
  tr.foldl (fun acc s => acc + s.depthDelta) 0

/-- `frameDepthAt tr k` is the call-stack depth immediately *before*
    step `tr[k]` would execute. By convention `frameDepthAt tr 0 = 0`. -/
def frameDepthAt (tr : ExecutionTrace) (k : Nat) : Int :=
  frameDepth (tr.take k)

/-! ## Frame nesting

A frame opened at trace position `i` (a CALL) is "still on the stack"
at position `j > i` iff the depth never returns to or below
`frameDepthAt tr i` between `i+1` and `j` inclusive.

We state this with a `Fin (j - i)`-indexed quantifier so that `decide`
reduces it on concrete traces.
-/

/-- `NestedAfter tr i j` holds iff the call frame opened at step `i`
    is still on the stack when step `j` is about to execute.

    The intent: any CALL at index `j` that targets a contract whose
    call frame was opened at `i` is a *reentrant* call into that
    contract.

    Stated with `Fin (j - i)` to make `Decidable` straightforward;
    semantically equivalent to `∀ k, i < k → k ≤ j → ...`. -/
def NestedAfter (tr : ExecutionTrace) (i j : Nat) : Prop :=
  ∀ d : Fin (j - i),
    frameDepthAt tr (i + 1 + d.val) > frameDepthAt tr i

/-- `Decidable` instance: `NestedAfter` is decidable on concrete
    traces because the quantifier is over `Fin n` (finite) and each
    body is a decidable `Int` comparison. -/
instance (tr : ExecutionTrace) (i j : Nat) : Decidable (NestedAfter tr i j) := by
  unfold NestedAfter; infer_instance

end QanaryContracts
