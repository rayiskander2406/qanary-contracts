/-
  QanaryContracts/ReentrancyFree.lean

  The universal reentrancy-safety predicate `ReentrancyFree`, plus the
  named *negative completeness* theorem (Ray, Phase 3 Session 2,
  Confirmation 3, 2026-04-27):

      "Every contract is either certified safe or comes with a
       machine-checked vulnerability witness. That is a product
       not just a theorem."

  The proof here is classical (uses `Classical.em` via `by_cases`),
  giving a one-line existence claim. The *constructive* version —
  `extractSafetyCertificate : Contract → SafetyWitness` — is a Phase 4
  deliverable per the internal completeness strategy. The named theorem
  reserves the type signature now; the constructive proof replaces
  the classical one without changing the statement.
-/
import QanaryContracts.EVM
import QanaryContracts.Storage
import QanaryContracts.Step
import QanaryContracts.Reentrancy
import QanaryContracts.Contract
import QanaryContracts.ValidExecution
import QanaryContracts.Reachability
import Mathlib.Tactic.Push

namespace QanaryContracts

/-! ## The universal safety predicate

A contract `C` is `ReentrancyFree` iff no valid execution under any
initial state can witness a state-aware reentrancy under `C`'s guard
policy. -/

/-- `ReentrancyFree C` — no *reachable* trace can witness
    C-specific state-aware reentrancy.

    **Phase 4 Session 6 refinement (Decision 5 of post-Session-3
    round + Decision 1 of post-Session-5 round):** quantifies over
    `ReachableTraceOf C s₀ tr` (not `ValidExecution tr` alone) and
    uses the C-specific `ReentrancyVulnerableStatefulOn C` (not
    the over-eager universal-`a` predicate).

    This is the **mathematically correct** definition for the
    intended security property: a contract deployed on Ethereum
    starts in a specific initial state and executes traces
    derivable from its declared functions; reentrancy is safety
    *for that contract*, not for arbitrary contracts whose slot
    values happen to match. -/
def ReentrancyFree (C : Contract) : Prop :=
  ∀ s₀ tr, ReachableTraceOf C s₀ tr →
    ¬ ReentrancyVulnerableStatefulOn C s₀ tr

/-! ## Negative completeness — the named decision theorem

Per Ray's Confirmation 3 (2026-04-27): every contract is either
reentrancy-free OR comes with a witness of its vulnerability. The
disjunction itself is a tautology under classical logic; the
*substantive* content is the constructive `extractSafetyCertificate`
function (Phase 4) that picks the side and exhibits the witness.

This theorem reserves the type signature so subsequent work can
target it. -/

/-- **Named theorem v2 (negative completeness — restricted to
    reachable traces).** Every contract is either reentrancy-safe
    under its guard policy on reachable executions, or there exists
    a reachable trace that witnesses the contrary.

    **Phase 4 Session 6 adaptation (Decision 3 of post-Session-5
    round):** the right disjunct now uses `ReachableTraceOf` rather
    than `ValidExecution`, matching the strengthened
    `ReentrancyFree` body. Per Ray (2026-04-27): *"v2 of
    reentrancy_free_or_vulnerable_witness — restricts to reachable
    execution traces, matching the intended security property for
    deployed contracts. The theorem is more precise after the
    change not weaker."*

    Status: classical proof (uses `Classical.em` via `by_cases` and
    `push Not`). The **constructive** version — exhibiting an
    explicit witness extraction — is a Phase 4 Session 7+
    deliverable. -/
theorem reentrancy_free_or_vulnerable_witness (C : Contract) :
    ReentrancyFree C ∨
    ∃ (s₀ : EVMState) (tr : ExecutionTrace),
      ReachableTraceOf C s₀ tr ∧
      ReentrancyVulnerableStatefulOn C s₀ tr := by
  by_cases h : ReentrancyFree C
  · exact Or.inl h
  · right
    unfold ReentrancyFree at h
    push Not at h
    obtain ⟨s₀, tr, hreach, hvuln⟩ := h
    exact ⟨s₀, tr, hreach, hvuln⟩

/-! ## Sanity: ReentrancyFree is NOT decidable in general

Unlike the trace-level predicates (which are decidable on concrete
traces because the quantifier domain is `Fin tr.length`), the
universal `ReentrancyFree C` quantifies over *all* `EVMState` and
*all* `ExecutionTrace` — neither of which is finite. Decidability
of `ReentrancyFree` requires either (a) restricting to a specific
contract whose finite reachable-trace set we can enumerate, or
(b) the constructive `extractSafetyCertificate` of Phase 4. -/

end QanaryContracts
