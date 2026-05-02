/-
  QanaryContracts/W8.lean

  **Phase 5 Session 10 — W8 mechanization (the phantom-CALL gap).**

  Phase 5 Session 9 (2026-05-01) attempted to close Conjunct 4
  (`TraceCCallLocked`) of the F4 lift theorem
  `ozGuardDiscipline_implies_RTO`. L3 (strict — under
  `currentFrameAt tr k = some C.address`) closed cleanly. The
  *phantom-CALL* case — where `currentFrameAt tr k = none` while the
  CALL's caller field is `C.address` — was identified as unprovable
  from the current `executes_C` + `OZGuardDiscipline` hypotheses. This
  is W8: a *Model-gap* wall (vs. W5/W7 which were Family-gap walls).
  See an internal session report §6.

  This file mechanizes the paper-and-pencil counter-example as a
  machine-checked Lean theorem. Three deliverables:

  1. `phantomCallTrace : ExecutionTrace` — the 8-step trace from
     an internal session report §6, instantiated on
     `ozWitnessContract`.
  2. `phantom_executes_C` — `executes_C ozWitnessContract
     (s₀_initial ozWitnessContract) phantomCallTrace` holds. Despite
     the phantom CALL at position 6, the trace satisfies
     `ValidExecution`, `InitialGuardUnlocked`, and the dispatch
     obligation (only the entry CALL at position 0 enters
     `ozWitnessAddress`).
  3. `phantom_violates_TraceCCallLocked` — `¬ TraceCCallLocked
     ozWitnessContract (s₀_initial ozWitnessContract)
     phantomCallTrace`. At the phantom CALL position 6, the guard
     slot reads `unlockedValue` (the prior C-frame's unlock SSTORE at
     position 4 left it that way), violating `TraceCCallLocked`'s
     "lockedValue at every C-issued CALL" requirement.

  Headline (Theorem `ozGuardDiscipline_implies_RTO_is_unprovable_as_stated`):
  the F4 lift's would-be universally-quantified statement is FALSE.

  This justifies the W8 sorry remaining at `BodyTraceLift.lean:509`
  and gates the Session 10+ resolution decision (see Session 9
  report §6 for the four resolution options).

  The proof of `phantom_violates_TraceCCallLocked` does NOT
  weaken `CallsFromTopFrame` or `ValidExecution` — the trace
  satisfies both as currently stated. This is exactly the wall: the
  model is too permissive for the lift's conclusion.
-/
import QanaryContracts.EVM
import QanaryContracts.Storage
import QanaryContracts.Step
import QanaryContracts.CEI
import QanaryContracts.Contract
import QanaryContracts.FunctionBody
import QanaryContracts.ValidExecution
import QanaryContracts.Reentrancy
import QanaryContracts.Reachability
import QanaryContracts.OZSoundness
import QanaryContracts.CEISufficiencyV2
import QanaryContracts.Executes
import QanaryContracts.Executes.CountHelpers
import Mathlib.Tactic.IntervalCases

namespace QanaryContracts

/-! ## The phantom CALL trace -/

/-- An additional callee for the phantom CALL — disjoint from
    `ozWitnessCallee` so the phantom isn't mistaken for the body's
    intended external CALL. Address `13`. -/
def ozPhantomCallee : Address := ⟨13, by decide⟩

/-- **The W8 phantom-CALL trace.** Eight steps:

    ```
    0: call ozWitnessUser ozWitnessAddress 0   -- entry into C
    1: sstore C g lockedValue                   -- C-body's lock
    2: call C ozWitnessCallee 0                 -- C-body's external CALL
    3: ret true                                 -- callee returns
    4: sstore C g unlockedValue                 -- C-body's unlock
    5: ret true                                 -- C returns; stack empty
    6: call C ozPhantomCallee 0                 -- PHANTOM: caller=C, currentFrameAt=none
    7: ret true                                 -- phantom returns
    ```

    Positions 0–5 are exactly `ozWitnessTrace`. Positions 6–7 are
    the phantom suffix that exposes W8: a CALL with
    `caller = ozWitnessAddress` AFTER the C-frame closed. -/
def phantomCallTrace : ExecutionTrace := [
  /- 0 -/ EVMStep.call ozWitnessUser ozWitnessAddress ⟨0, by decide⟩,
  /- 1 -/ EVMStep.sstore ozWitnessAddress ozWitnessGuardSlot ⟨2, by decide⟩,
  /- 2 -/ EVMStep.call ozWitnessAddress ozWitnessCallee ⟨0, by decide⟩,
  /- 3 -/ EVMStep.ret true,
  /- 4 -/ EVMStep.sstore ozWitnessAddress ozWitnessGuardSlot ⟨1, by decide⟩,
  /- 5 -/ EVMStep.ret true,
  /- 6 -/ EVMStep.call ozWitnessAddress ozPhantomCallee ⟨0, by decide⟩,
  /- 7 -/ EVMStep.ret true
]

/-! ## ValidExecution -/

/-- The phantom trace satisfies the three structural validity
    constraints. Identical pattern to `ozWitnessTrace_validExecution`,
    extended to 8 positions. The position-6 phantom CALL satisfies
    `CallsFromTopFrame` via the OR-`none` clause: the stack is empty
    after position 5's `ret`. -/
theorem phantomCallTrace_validExecution : ValidExecution phantomCallTrace := by
  refine ⟨?_, ?_, ?_⟩
  · -- SStoresInOwnFrame
    intro ⟨k, hk⟩ addr key val hstep
    have hk8 : k < 8 := hk
    show currentFrameAt phantomCallTrace k = some addr
    interval_cases k
    all_goals simp [phantomCallTrace] at hstep
    all_goals (obtain ⟨rfl, _, _⟩ := hstep; decide)
  · -- CallsFromTopFrame
    intro ⟨k, hk⟩ caller callee value hstep
    have hk8 : k < 8 := hk
    show currentFrameAt phantomCallTrace k = some caller ∨
         currentFrameAt phantomCallTrace k = none
    interval_cases k
    all_goals (
      simp [phantomCallTrace] at hstep
      try (obtain ⟨rfl, rfl, rfl⟩ := hstep))
    all_goals decide
  · -- BalancedFrames
    intro ⟨k, hk⟩
    have hk8 : k < 8 := hk
    show frameDepthAt phantomCallTrace k ≥ 0
    interval_cases k <;> decide

/-! ## MatchesBody at the entry CALL -/

/-- The first 6 positions of `phantomCallTrace` match the OZ witness
    body at `q=0`, `finish=6`. Computationally identical to
    `ozWitnessFunction_matchesBody`: `cFrameProjection` over `[1, 6)`
    filters out sub-frame position 3 and yields the 4-element
    unfolded body. -/
theorem phantom_matchesBody_at_0_6 :
    MatchesBody ozWitnessContract ozWitnessFunction phantomCallTrace 0 6 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · decide  -- 0 < 6
  · decide  -- 6 ≤ 8
  · refine ⟨ozWitnessUser, ⟨0, by decide⟩, ?_⟩; rfl
  · decide  -- frameDepthAt _ 0 = frameDepthAt _ 6 = 0
  · decide  -- cFrameProjection over [1, 6) = unfoldBody

/-! ## `executes_C` -/

/-- The phantom trace is a faithful execution of `ozWitnessContract`
    from `s₀_initial`. The dispatch obligation discharges trivially:
    only `k=0` is an entry CALL into `ozWitnessAddress`; positions
    `2` and `6` are CALLs *issued by* `ozWitnessAddress` (callee ≠
    `ozWitnessAddress`); other positions are not CALLs at all. -/
theorem phantom_executes_C :
    executes_C ozWitnessContract (s₀_initial ozWitnessContract) phantomCallTrace := by
  refine ⟨phantomCallTrace_validExecution,
          s₀_initial_satisfies_initialGuardUnlocked ozWitnessContract, ?_⟩
  intro k caller value hk h_call
  -- Only k=0 has callee = ozWitnessAddress = ozWitnessContract.address.
  have hk8 : k < 8 := hk
  interval_cases k
  · -- k = 0 — the entry CALL. Dispatch to ozWitnessFunction.
    exact ⟨ozWitnessFunction, 6, by simp [ozWitnessContract], phantom_matchesBody_at_0_6⟩
  all_goals (
    exfalso
    simp [phantomCallTrace, ozWitnessContract, ozWitnessAddress, ozWitnessCallee,
          ozPhantomCallee] at h_call)

/-! ## Slot computation at position 6 -/

/-- Inline copy of `BodyTraceLift.applyStep_sstore_lookupSlot_eq` (which
    is `private` upstream). 3-line proof. -/
private theorem applyStep_sstore_lookupSlot_eq_w8
    (s : EVMState) (a : Address) (key val : Word256) :
    (applyStep s (EVMStep.sstore a key val)).lookupSlot a key = val := by
  unfold applyStep EVMState.lookupSlot Storage.lookupZ
  simp [Finmap.lookup_insert]

/-- The guard slot at position 6 of the phantom trace is `unlockedValue`.

    Proof: position 4's SSTORE writes `unlockedValue`; positions 5
    (ret) does not write the guard slot, so the slot is stable from
    `5` to `6` by `slot_stable_no_sstore`. -/
theorem phantom_slot_at_6_eq_unlockedValue :
    slotAt (s₀_initial ozWitnessContract) phantomCallTrace 6
        ozWitnessAddress ozWitnessGuardSlot = ozWitnessContract.unlockedValue := by
  -- Step 1: at position 5, slot reads unlockedValue (after the SSTORE at 4).
  have h_5 : slotAt (s₀_initial ozWitnessContract) phantomCallTrace 5
        ozWitnessAddress ozWitnessGuardSlot = ozWitnessContract.unlockedValue := by
    unfold slotAt stateAt evalState
    have h_4_lt : 4 < phantomCallTrace.length := by decide
    have h_take_5 : phantomCallTrace.take 5 =
        phantomCallTrace.take 4 ++ [phantomCallTrace[4]'h_4_lt] := by
      rw [List.take_add_one, List.getElem?_eq_getElem h_4_lt]; rfl
    rw [h_take_5, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    have h_step_4 : phantomCallTrace[4]'h_4_lt =
        EVMStep.sstore ozWitnessAddress ozWitnessGuardSlot ozWitnessContract.unlockedValue := by
      rfl
    rw [h_step_4]
    exact applyStep_sstore_lookupSlot_eq_w8 _ _ _ _
  -- Step 2: slot stable from 5 to 6 (position 5 is `ret true`, not an SSTORE).
  have h_stable : slotAt (s₀_initial ozWitnessContract) phantomCallTrace 5
        ozWitnessAddress ozWitnessGuardSlot =
      slotAt (s₀_initial ozWitnessContract) phantomCallTrace 6
        ozWitnessAddress ozWitnessGuardSlot := by
    apply slot_stable_no_sstore _ phantomCallTrace ozWitnessAddress ozWitnessGuardSlot
      5 6 (by decide) (by decide)
    intro p h_pge h_plt step h_step
    have hp : p = 5 := by omega
    subst hp
    -- phantomCallTrace[5]? = some (ret true); ret is not an SSTORE.
    have : step = EVMStep.ret true := by
      simp [phantomCallTrace] at h_step; exact h_step.symm
    subst this
    rintro ⟨v, h_eq⟩
    cases h_eq
  rw [← h_stable]; exact h_5

/-! ## ¬ TraceCCallLocked -/

/-- The phantom trace violates `TraceCCallLocked`. At position 6, the
    CALL has `caller = ozWitnessAddress` but the guard slot reads
    `unlockedValue`, not `lockedValue`. -/
theorem phantom_violates_TraceCCallLocked :
    ¬ TraceCCallLocked ozWitnessContract (s₀_initial ozWitnessContract) phantomCallTrace := by
  intro h_tcc
  have h_6_lt : 6 < phantomCallTrace.length := by decide
  let k6 : Fin phantomCallTrace.length := ⟨6, h_6_lt⟩
  have h_call_6 : phantomCallTrace[k6.val]? =
      some (EVMStep.call ozWitnessContract.address ozPhantomCallee ⟨0, by decide⟩) := by
    show phantomCallTrace[6]? = _
    rfl
  have h_locked := h_tcc k6 ozPhantomCallee ⟨0, by decide⟩ h_call_6
  -- h_locked : guardSlotAt _ phantomCallTrace 6 ozWitnessContract.address
  --              ozWitnessContract.guardSlot = ozWitnessContract.lockedValue.
  -- ozWitnessContract.address = ozWitnessAddress and .guardSlot = ozWitnessGuardSlot
  -- definitionally, so the slot-value lemma applies after `show`-normalization.
  unfold guardSlotAt at h_locked
  have h_locked' : slotAt (s₀_initial ozWitnessContract) phantomCallTrace 6
      ozWitnessAddress ozWitnessGuardSlot = ozWitnessContract.lockedValue := h_locked
  rw [phantom_slot_at_6_eq_unlockedValue] at h_locked'
  -- ozWitnessContract.unlockedValue = ⟨1, _⟩, lockedValue = ⟨2, _⟩
  exact absurd h_locked' (by decide)

/-! ## Headline: `ozGuardDiscipline_implies_RTO` is unprovable as stated -/

/-- **W8 mechanization headline.** The would-be F4 lift theorem
    `ozGuardDiscipline_implies_RTO` (currently sorry'd at
    `BodyTraceLift.lean:509` for the phantom case) is FALSE under its
    current statement. Witness: `(ozWitnessContract, s₀_initial
    ozWitnessContract, phantomCallTrace)`.

    The witness contract satisfies `OZGuardDiscipline` (proven in
    `OZSoundness.lean`); `lockedValue ≠ unlockedValue` (`2 ≠ 1`); the
    phantom trace satisfies `executes_C` (above). Yet the trace is
    NOT in `ReachableTraceOf` — its 4th conjunct
    `TraceCCallLocked` fails at the phantom-CALL position 6.

    Therefore no proof of the universally-quantified F4 lift can
    exist without strengthening either the source model
    (`CallsFromTopFrame`'s OR-`none` clause), the target predicate
    (`TraceCCallLocked`), or the lift theorem's hypotheses. See
    an internal session report §6 for the four resolution options. -/
theorem ozGuardDiscipline_implies_RTO_is_unprovable_as_stated :
    ¬ ∀ (C : Contract) (s₀ : EVMState) (tr : ExecutionTrace),
        OZGuardDiscipline C → C.lockedValue ≠ C.unlockedValue →
        executes_C C s₀ tr → ReachableTraceOf C s₀ tr := by
  intro h_universal
  have h_RTO := h_universal ozWitnessContract (s₀_initial ozWitnessContract)
    phantomCallTrace ozWitnessContract_OZGuardDiscipline (by decide) phantom_executes_C
  -- Extract TraceCCallLocked (the 4th conjunct of ReachableTraceOf).
  obtain ⟨_, _, _, h_tcc, _⟩ := h_RTO
  exact phantom_violates_TraceCCallLocked h_tcc

end QanaryContracts
