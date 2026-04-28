/-
  QanaryContracts/Spikes.lean

  Phase 2 pre-theorem-proof spikes (Phase 1 § 4 + claim freeze § 12).
  Verifies Mathlib infrastructure assumptions at pin 322515540d7f.

  Goal of this file: every #check below must elaborate without error.
  When `lake build` succeeds on this file, all five spikes are PASS.
-/
import QanaryContracts.EVM
import QanaryContracts.Reentrancy
import QanaryContracts.DAOAttack
import Mathlib.Data.List.Pairwise
import Mathlib.Data.List.Basic
import Mathlib.Data.Finmap
import Mathlib.Logic.Relation

namespace QanaryContracts.Spikes

open List

/-! ## Spike 2: List.Pairwise.sublist exists at pin

If this elaborates, `Pairwise.sublist` is reachable in our environment.
This is the workhorse lemma for the eventual CEI sufficiency proof. -/
section Spike2
variable {α : Type*} {R : α → α → Prop} {l₁ l₂ : List α}
#check @List.Pairwise.sublist
example (h : l₁ <+ l₂) (hp : l₂.Pairwise R) : l₁.Pairwise R := hp.sublist h
end Spike2

/-! ## Spike 3: List.IsPrefix and List.takeWhile reachable

`List.IsPrefix` (`<+:`), `List.takeWhile`, `List.dropWhile`. -/
section Spike3
#check @List.IsPrefix
#check @List.takeWhile
#check @List.dropWhile
example : [1, 2] <+: [1, 2, 3] := by decide
end Spike3

/-! ## Spike 5: native_decide on the DAO trace

Already exercised in `DAOAttack.lean` via two `example` invocations.
Re-asserted here for the spike registry: native_decide reduces
`Finmap`-free, `Fin`-based predicates on concrete traces in <1s. -/
section Spike5
example : hasReentrancyWitness daoAttackTrace daoVictim 0 2 = true := by
  native_decide
example : hasReentrancyWitness safeWithdrawTrace daoVictim 0 2 = false := by
  native_decide
example : frameDepthAt daoAttackTrace 1 = 1 := by native_decide
example : frameDepthAt daoAttackTrace 2 = 2 := by native_decide
example : frameDepthAt daoAttackTrace 7 = 1 := by native_decide
end Spike5

/-! ## Mathlib infrastructure for Phase 3 (preview)

These verify that the lemmas the Mathlib inventory recon flagged as
load-bearing are present at pin. We do not USE them yet (Phase 3),
but compiling these `#check`s demonstrates they exist. -/
section MathlibInventory
#check @Finmap.lookup
#check @Finmap.insert
#check @Finmap.erase
#check @Relation.ReflTransGen
#check @Relation.ReflTransGen.head_induction_on
#check @List.Pairwise.imp
#check @List.pairwise_iff_forall_sublist
end MathlibInventory

end QanaryContracts.Spikes
