/-
  QanaryContracts/DAOAttack.lean

  The 2016 DAO attack as a concrete `ExecutionTrace` literal in the
  model from `EVM.lean`, plus a machine-checked witness that
  `ReentrancyVulnerable` holds on the trace.

  This is the FIRST DELIVERABLE of Phase 2 (per Decision 3 / Ray
  2026-04-26): if the model could not express the DAO attack, every
  subsequent theorem about reentrancy would be reasoning about a
  different phenomenon than the one the paper claims to address.

  Trace structure (mirrors the actual DAO attack's call-graph topology):
    i=0  attacker → victim     (open victim's frame)
    i=1  victim   → attacker   (low-level send during withdraw, before SSTORE)
    i=2  attacker → victim     (REENTRANT — fallback re-enters)
    i=3  victim   → attacker   (recursive theft)
    i=4..6  ret                (frames close)
    i=7  sstore victim ...     (state update — TOO LATE)
    i=8  ret                   (outermost frame closes)

  The reentrancy witness uses indices i=0 and j=2 with a = `daoVictim`:
  both CALLs target the victim, and step 2 is nested inside step 0's
  frame (depth at positions 1 and 2 is 1 and 2 respectively, both > 0).
-/
import QanaryContracts.EVM
import QanaryContracts.Reentrancy

namespace QanaryContracts

/-! ## Concrete addresses for the DAO scenario -/

/-- The victim contract (analogue of TheDAO's `splitDAO` entry point). -/
def daoVictim : Address := ⟨1, by decide⟩

/-- The attacker contract whose fallback re-enters the victim. -/
def daoAttacker : Address := ⟨2, by decide⟩

/-- A representative transfer value (in wei). Irrelevant to the
    structural reentrancy property; kept small for `decide` speed. -/
def daoValue : Word256 := ⟨100, by decide⟩

/-! ## The DAO attack trace -/

/-- The DAO attack as a 9-step `ExecutionTrace` literal. -/
def daoAttackTrace : ExecutionTrace := [
  /- 0 -/ EVMStep.call daoAttacker daoVictim daoValue,
  /- 1 -/ EVMStep.call daoVictim daoAttacker daoValue,
  /- 2 -/ EVMStep.call daoAttacker daoVictim daoValue,  -- REENTRANT
  /- 3 -/ EVMStep.call daoVictim daoAttacker daoValue,
  /- 4 -/ EVMStep.ret true,
  /- 5 -/ EVMStep.ret true,
  /- 6 -/ EVMStep.ret true,
  /- 7 -/ EVMStep.sstore daoVictim ⟨0, by decide⟩ ⟨0, by decide⟩,
  /- 8 -/ EVMStep.ret true
]

/-- A correctly-structured `withdraw` that satisfies CEI: state update
    BEFORE external call. The structural reentrancy predicate should
    NOT fire here. (Universal non-reentrancy theorems are Phase 3;
    this trace is preserved as a sanity-check counter-example.) -/
def safeWithdrawTrace : ExecutionTrace := [
  /- 0 -/ EVMStep.call daoAttacker daoVictim daoValue,
  /- 1 -/ EVMStep.sstore daoVictim ⟨0, by decide⟩ ⟨0, by decide⟩,
  /- 2 -/ EVMStep.call daoVictim daoAttacker daoValue,
  /- 3 -/ EVMStep.ret true,
  /- 4 -/ EVMStep.ret true
]

/-! ## The DAO reentrancy witness

We prove that `ReentrancyVulnerable daoAttackTrace` holds with explicit
witnesses `a = daoVictim`, `i = 0`, `j = 2`. Each conjunct reduces by
`decide` on concrete data:

  i < j           : 0 < 2                          [Nat]
  j < |tr|        : 2 < 9                          [Nat]
  tr[0]? is CALL  : tr[0]? = some (call _ daoVictim _)
  tr[2]? is CALL  : tr[2]? = some (call _ daoVictim _)
  NestedAfter     : depth at positions 1, 2 both > depth at 0 (= 0)
-/
theorem dao_attack_is_reentrant : ReentrancyVulnerable daoAttackTrace := by
  refine ⟨daoVictim, 0, 2, ?_, ?_, ?_, ?_, ?_⟩
  · decide                           -- 0 < 2
  · decide                           -- 2 < 9
  · exact ⟨daoAttacker, daoValue, rfl⟩
  · exact ⟨daoAttacker, daoValue, rfl⟩
  · decide                           -- NestedAfter daoAttackTrace 0 2

/-- Same fact via the Bool form, for `native_decide` validation
    (Phase 1 spike 5). Equivalent conclusion, faster reduction. -/
example : hasReentrancyWitness daoAttackTrace daoVictim 0 2 = true := by
  native_decide

/-! ## Sanity: model is faithful

A complementary check that the model can DISTINGUISH the attack from
a safe execution. We don't yet prove `¬ ReentrancyVulnerable` for the
safe trace (that's a Phase 3 theorem, requiring a precise sufficient
condition), but we evaluate the witness function: with the same
indices `(daoVictim, 0, 2)` the safe trace's witness is FALSE (no
nested CALL at index 2). -/
example : hasReentrancyWitness safeWithdrawTrace daoVictim 0 2 = false := by
  native_decide

end QanaryContracts
