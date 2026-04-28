/-
  QanaryContracts/Storage.lean

  Per-contract storage and global EVM state, using Mathlib's `Finmap`.
  Phase 3 first session — Priority 1 infrastructure (Ray, 2026-04-27).

  EVM convention: storage slots that have never been written read as zero.
  We model storage as a `Finmap` (where missing keys are absent) and bridge
  to the EVM convention via `lookupZ`.
-/
import Mathlib.Data.Finmap
import QanaryContracts.EVM

namespace QanaryContracts

/-- Per-contract storage: 256-bit slot keys mapped to 256-bit values. -/
abbrev Storage : Type := Finmap (fun _ : Word256 => Word256)

/-- Global EVM state: contract address mapped to its storage. -/
abbrev EVMState : Type := Finmap (fun _ : Address => Storage)

/-- The 256-bit zero word. -/
def Word256.zero : Word256 := ⟨0, by decide⟩

/-- Lookup a storage slot, returning `Word256.zero` for unset slots
    (EVM convention: never-written slots read as zero). -/
def Storage.lookupZ (s : Storage) (k : Word256) : Word256 :=
  (s.lookup k).getD Word256.zero

/-- Lookup a slot in the global state, returning `Word256.zero` if either
    the address has no storage or the slot is unset. -/
def EVMState.lookupSlot (s : EVMState) (a : Address) (k : Word256) : Word256 :=
  match s.lookup a with
  | some storage => storage.lookupZ k
  | none         => Word256.zero

/-- The empty storage (no slots set). -/
def Storage.empty : Storage := ∅

/-- The empty global state (no contracts have storage). -/
def EVMState.empty : EVMState := ∅

end QanaryContracts
