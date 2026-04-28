/-
  QanaryContracts/Tests.lean

  Phase 3 Session 1 verification: the refined predicates produce the
  correct verdict on three test cases (Ray, 2026-04-27, Priority 2):

    (a) DAO attack          — must NOT satisfy CEI; must be stateful-vuln
    (b) Safe withdrawal     — must SATISFY CEI; must NOT be stateful-vuln
    (c) Multi-function      — must SATISFY CEI; must NOT be stateful-vuln
    (d) Guard-protected     — discrimination test: structural fires
                              but state-aware does NOT

  Each verification is by `decide` or `native_decide` on concrete
  literals. No theorem proofs about the universal soundness theorem
  are attempted (per Ray: "Do not attempt CEI or Guard proofs until
  the refined predicate is confirmed correct against all three test
  cases.").
-/
import QanaryContracts.EVM
import QanaryContracts.Storage
import QanaryContracts.Step
import QanaryContracts.Reentrancy
import QanaryContracts.CEI
import QanaryContracts.DAOAttack
import QanaryContracts.MultiFunction

namespace QanaryContracts.Tests

open QanaryContracts

/-! ## Test (a): DAO attack -/

/-- DAO attack does NOT satisfy CEI: step 1 is `call victim → attacker`
    (external call from victim's frame), step 7 is `sstore daoVictim ...`
    (state update on victim's storage AFTER the external call) — both
    in the same frame. CEI violated at (1, 7). -/
example : ¬ SatisfiesCEI daoAttackTrace := by native_decide

/-- DAO attack IS stateful-vulnerable under the OZ-style guard policy:
    at the moment of the reentrant CALL (i=2), the guard slot of
    `daoVictim` was never written, so it reads as 0 = unlocked. -/
example : hasStatefulReentrancyWitness EVMState.empty daoAttackTrace
            daoVictim 0 2 ozGuardSlot ozUnlockedValue = true := by
  native_decide

/-! ## Test (b): Safe withdrawal -/

/-- Safe withdrawal SATISFIES CEI: the only external CALL out (step 2)
    is preceded by the SSTORE (step 1), and no SSTORE follows the CALL
    in the same frame. -/
example : SatisfiesCEI safeWithdrawTrace := by native_decide

/-- Safe withdrawal is NOT stateful-vulnerable: there's no nested
    same-target CALL pattern at all. The structural witness fails. -/
example : hasStatefulReentrancyWitness EVMState.empty safeWithdrawTrace
            daoVictim 0 2 ozGuardSlot ozUnlockedValue = false := by
  native_decide

/-! ## Test (c): Multi-function bank, CEI-conformant -/

/-- The multi-function bank trace SATISFIES CEI: deposit and transfer
    have no external calls; withdraw's external CALL (step 9) is
    preceded by all of its SSTOREs (step 8), and no SSTORE follows in
    the same frame. -/
example : SatisfiesCEI multiFunctionTrace := by native_decide

/-- Multi-function bank trace has no structural reentrancy: each call
    into `multibank` returns before the next, so no nested same-target
    CALL pattern. -/
example : hasReentrancyWitness multiFunctionTrace multibank 0 3 = false := by
  native_decide
example : hasReentrancyWitness multiFunctionTrace multibank 0 7 = false := by
  native_decide
example : hasReentrancyWitness multiFunctionTrace multibank 3 7 = false := by
  native_decide

/-! ## Test (d): Guard-protected, structurally-reentrant trace

The KEY DISCRIMINATION test. The trace has a structural reentrancy
shape (two CALLs into `daoVictim` with the second nested), but the
guard slot is locked at the reentry point. State-aware predicate
must NOT fire even though structural one does. -/

/-- Structural predicate FIRES: steps 0 and 3 both call into `daoVictim`,
    and step 3 is nested inside step 0's still-open frame. -/
example : hasReentrancyWitness guardProtectedTrace daoVictim 0 3 = true := by
  native_decide

/-- State-aware predicate does NOT fire: at step 3, the guard slot of
    `daoVictim` was set to `ozLockedValue = 1` at step 1, so it does
    NOT match `ozUnlockedValue = 0`. The state-aware refinement
    correctly distinguishes guard-protected reentry attempts from
    actual vulnerabilities. -/
example : hasStatefulReentrancyWitness EVMState.empty guardProtectedTrace
            daoVictim 0 3 ozGuardSlot ozUnlockedValue = false := by
  native_decide

/-! ## Sanity: `currentFrameAt` matches the manual stack trace

We manually computed the call-stack evolution for `daoAttackTrace`
and `safeWithdrawTrace` in an internal phase report.
Verifying the helper agrees. -/

example : currentFrameAt daoAttackTrace 0 = none := by native_decide
example : currentFrameAt daoAttackTrace 1 = some daoVictim := by native_decide
example : currentFrameAt daoAttackTrace 7 = some daoVictim := by native_decide
example : currentFrameAt daoAttackTrace 8 = some daoVictim := by native_decide

example : currentFrameAt safeWithdrawTrace 1 = some daoVictim := by native_decide
example : currentFrameAt safeWithdrawTrace 2 = some daoVictim := by native_decide
example : currentFrameAt safeWithdrawTrace 3 = some daoAttacker := by native_decide

end QanaryContracts.Tests
