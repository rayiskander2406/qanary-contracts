/-
  QanaryContracts/MultiFunction.lean

  A CEI-conformant multi-function contract trace, used as test case (c)
  for the Phase 3 Session 1 verification of `SatisfiesCEI`.

  The contract `multibank` exposes three functions:
    deposit(amount):  state += amount
    transfer(to, n):  state -= n; other_state += n
    withdraw(amount): state -= amount; CALL out

  All three functions follow Checks-Effects-Interactions: any state
  changes (effects) precede any external CALLs (interactions). The
  trace exercises all three sequentially; SatisfiesCEI must hold.

  Plus: a "guard-protected" trace that has a *structural* reentrancy
  shape (two CALLs into the same address with one nested in the other)
  but where the guard slot is observed LOCKED at the reentry point.
  The state-aware predicate must NOT fire on this trace — this is the
  key discrimination test for the refinement.
-/
import QanaryContracts.EVM
import QanaryContracts.Storage
import QanaryContracts.Step
import QanaryContracts.Reentrancy
import QanaryContracts.CEI
import QanaryContracts.DAOAttack

namespace QanaryContracts

/-! ## Test case (c) — multi-function bank, CEI-conformant -/

def user      : Address := ⟨3, by decide⟩
def multibank : Address := ⟨4, by decide⟩
def other     : Address := ⟨5, by decide⟩

/-- `multiFunctionTrace`: deposit → transfer → withdraw, each CEI-conformant.
    No nested same-target CALLs, every SSTORE precedes every external
    CALL within its frame. Should SATISFY CEI. -/
def multiFunctionTrace : ExecutionTrace := [
  -- DEPOSIT(100): just an internal SSTORE
  /- 0 -/ EVMStep.call user multibank ⟨0, by decide⟩,
  /- 1 -/ EVMStep.sstore multibank ⟨0, by decide⟩ ⟨100, by decide⟩,
  /- 2 -/ EVMStep.ret true,
  -- TRANSFER(other, 50): two SSTOREs, no external call
  /- 3 -/ EVMStep.call user multibank ⟨0, by decide⟩,
  /- 4 -/ EVMStep.sstore multibank ⟨0, by decide⟩ ⟨50, by decide⟩,
  /- 5 -/ EVMStep.sstore multibank ⟨1, by decide⟩ ⟨50, by decide⟩,
  /- 6 -/ EVMStep.ret true,
  -- WITHDRAW(50): SSTORE first (effects), then external CALL (interactions)
  /- 7 -/ EVMStep.call user multibank ⟨0, by decide⟩,
  /- 8 -/ EVMStep.sstore multibank ⟨0, by decide⟩ ⟨0, by decide⟩,
  /- 9 -/ EVMStep.call multibank user ⟨50, by decide⟩,
  /-10 -/ EVMStep.ret true,
  /-11 -/ EVMStep.ret true
]

/-! ## Test case (d) — guard-protected, structurally-reentrant trace

This trace has the *structural* reentrancy shape (two CALLs into
`daoVictim` with the second nested in the first), but the guard slot
of `daoVictim` is observed LOCKED at the moment of the reentry. The
state-aware predicate (under `unlockedValue = 0`) must NOT fire here.

This is the discrimination test that justifies the refinement: the
state-aware predicate is strictly stronger than the structural one. -/

/-- The OZ guard slot index. (Concrete choice — paper uses
    `keccak256("openzeppelin.contracts.utils.ReentrancyGuard")` slot
    in real OZ; here a small Fin literal for `decide` speed.) -/
def ozGuardSlot : Word256 := ⟨1, by decide⟩

/-- The OZ guard's "not entered" value. v3 used Boolean (0=unlocked);
    v4+ uses status enum (1=NOT_ENTERED, 2=ENTERED). The predicate is
    parameterized; here we test with v3-style 0=unlocked. -/
def ozUnlockedValue : Word256 := ⟨0, by decide⟩

/-- v3-style locked value. -/
def ozLockedValue : Word256 := ⟨1, by decide⟩

/-- A trace that LOCKS the guard before issuing the external call,
    so that even though a reentrant CALL appears in the trace, the
    state-aware predicate sees `guard = LOCKED` at the reentry point. -/
def guardProtectedTrace : ExecutionTrace := [
  /- 0 -/ EVMStep.call daoAttacker daoVictim daoValue,
  /- 1 -/ EVMStep.sstore daoVictim ozGuardSlot ozLockedValue,    -- LOCK
  /- 2 -/ EVMStep.call daoVictim daoAttacker daoValue,           -- send
  /- 3 -/ EVMStep.call daoAttacker daoVictim daoValue,           -- reentry attempt
  /- 4 -/ EVMStep.ret false,                                      -- (would-have-reverted)
  /- 5 -/ EVMStep.ret true,
  /- 6 -/ EVMStep.sstore daoVictim ozGuardSlot ozUnlockedValue,  -- UNLOCK
  /- 7 -/ EVMStep.ret true
]

end QanaryContracts
