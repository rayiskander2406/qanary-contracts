/-
  QanaryContracts/Completeness.lean

  Phase 5 Session 13 Unit 2 — Layer 5 Completeness foundation module.

  This module houses the four sub-case theorems that compose into the
  eventual constructive completeness disjunction:

    ReentrancyFreeGeneral C ⟸
      (∃ slot, OZGuardConfig C slot) ∨
      SatisfiesCEI_AllPaths C ∨
      NoSStores C ∨
      NoExternalCalls C

  Sub-case naming convention: `no_*_implies_RFG` for the contrapositive
  direction (predicate implies reentrancy-freeness).

  ## Status (Phase 5 Session 13)

  * `no_functions_implies_RFG` : PROVED (vacuous foundational case;
    NoFunctions C ⊆ NoExternalCalls C). The substantive
    `NoExternalCalls` sub-case requires general-frame stack-history
    primitives (a public version of `stackAt_index_has_entry` from
    `Executes/StackHistory.lean`, currently `private`) that will be
    developed during F2 multi-call generalization. Promoting that
    primitive in isolation in this session would trigger
    HS-COMPLETENESS-INFRASTRUCTURE-DRIFT; embedding the full proof
    here would trigger HS-COMPLETENESS-CAP. The vacuous case is
    honestly weaker than the eventual `NoExternalCalls` sub-case but
    provides the Layer 5 architecture (`ReentrancyFreeGeneral`
    predicate + naming convention + file placement) at zero
    infrastructure cost.
  * `no_external_calls_implies_RFG` : DEFERRED to Sessions 14-21
    (post-F2 polish or Session 22 lead-in to F3 instantiation work).
  * `no_sstores_implies_RFG` : DEFERRED to Sessions 26-30.
  * `cei_all_paths_implies_RFG` : DEFERRED to Sessions 26-30.
  * `oz_guard_config_implies_RFG` : DEFERRED to Sessions 26-30
    (essentially Theorem 5's statement restated against the Layer 5
    `ReentrancyFreeGeneral` predicate).

  The disjunction theorem `oz_completeness_full` lands in Sessions 26-30.

  ## Honest framing

  The vacuous `no_functions_implies_RFG` case covers contracts whose
  `functions` field is the empty list. Such contracts cannot be
  "reentered" because there are no functions to call — `executes_C`'s
  dispatch obligation immediately contradicts any CALL into `C.address`.
  The result is a worked example of the vacuous-case proof pattern
  that the four substantive sub-cases will refine; it does NOT cover
  the substantive case where `C.functions` is non-empty but no body
  issues an external CALL. That substantive case (`NoExternalCalls`)
  is a strict superset of `NoFunctions` and lands in Sessions 14-21.
-/
import QanaryContracts.Contract
import QanaryContracts.FunctionBody
import QanaryContracts.EVM
import QanaryContracts.Storage
import QanaryContracts.Reentrancy
import QanaryContracts.ValidExecution
import QanaryContracts.Reachability
import QanaryContracts.Executes
import QanaryContracts.OZSoundness

namespace QanaryContracts

/-! ## Layer 5 reentrancy-freeness predicate -/

/-- The Layer 5 universal reentrancy-freeness predicate, quantifying
    over body-faithful `executes_C` operational executions. The
    four-witness disjunction (future work) targets this predicate.

    Distinct from `ReentrancyFree C` (RTO-quantified): the F4 lift
    `ozGuardDiscipline_implies_RTO` connects `executes_C` to
    `ReachableTraceOf` under a `NoPhantomCalls` antecedent (per W8 P3
    resolution; see the internal paper scaffold §11). `ReentrancyFreeGeneral`
    quantifies over `executes_C` directly, which is the natural
    quantification structure for the four-witness disjunction's
    sub-cases (each sub-case predicate constrains the contract's
    bodies via `C.functions`, and `executes_C`'s dispatch carries
    that constraint into the trace). -/
def ReentrancyFreeGeneral (C : Contract) : Prop :=
  ∀ (s₀ : EVMState) (tr : ExecutionTrace),
    executes_C C s₀ tr → ¬ ReentrancyVulnerableStatefulOn C s₀ tr

/-! ## Vacuous foundational sub-case predicate -/

/-- A contract has no declared functions. Strict subset of the
    eventual `NoExternalCalls C` predicate (a contract with no
    functions trivially has no body issuing external CALLs).

    This predicate supports the vacuous foundational case
    `no_functions_implies_RFG` proved below; the substantive
    `NoExternalCalls` predicate and its sub-case proof land in
    Sessions 14-21. -/
def NoFunctions (C : Contract) : Prop := C.functions = []

/-! ## Vacuous foundational sub-case theorem -/

/-- **Vacuous foundational sub-case (1 of 4):** a contract with no
    declared functions is body-faithfully reentrancy-free.

    The proof: `executes_C C s₀ tr`'s dispatch obligation requires
    every CALL into `C.address` to dispatch to *some* `f ∈ C.functions`.
    With `C.functions = []`, no such `f` exists. Therefore any CALL
    into `C.address` contradicts `executes_C`. Reentrancy requires
    two such CALLs, so no reentrancy witness can exist.

    Honest framing: `NoFunctions C ⊆ NoExternalCalls C`. The
    substantive `NoExternalCalls` sub-case (where `C.functions ≠ []`
    but no body issues a CALL) is deferred per the module docstring;
    its proof requires general-frame stack-history primitives
    (`stackAt_index_has_entry` made public, plus a "no sub-frames in a
    no-CALL C-frame" lemma) developed during F2 multi-call work. -/
theorem no_functions_implies_RFG
    (C : Contract) (h_no_funcs : NoFunctions C) :
    ReentrancyFreeGeneral C := by
  intro s₀ tr h_exec h_vuln
  obtain ⟨i, j, h_ij, h_jlen, ⟨c1, v1, h_call_i⟩, _, _, _⟩ := h_vuln
  obtain ⟨_, _, h_dispatch⟩ := h_exec
  have hilen : i < tr.length := lt_trans h_ij h_jlen
  obtain ⟨f, _, hf_mem, _⟩ := h_dispatch i c1 v1 hilen h_call_i
  rw [h_no_funcs] at hf_mem
  simp at hf_mem

end QanaryContracts
