-- QANARY Contracts — top-level imports
--
-- Frozen claim (revised 2026-04-28 per F1 of the 2026-04-28 R8 audit;
-- expanded 2026-05-02 per Phase 5 Session 12 Unit 3 to propagate Phase 5
-- closures and B4 / N1 / N2 narrowings; canonical text in
-- the internal paper scaffold §1):
--
--   "A machine-checked universal soundness theorem for the
--   single-external-call subset of contracts satisfying `OZGuardDiscipline`
--   (the strengthened 6-conjunct predicate per W4), against a minimal
--   4-opcode EVM call-frame model in Lean 4 + Mathlib, with: (i) a
--   machine-checked CEI/OZ-incompatibility theorem (Theorem 4); (ii) a
--   machine-checked body-to-trace lift (`ozGuardDiscipline_implies_RTO`)
--   carrying a `NoPhantomCalls` antecedent (per W8 P3 resolution); (iii)
--   seven named methodology walls (W1, W2, W3, W4, W5, W7, W8)
--   demonstrating the methodology surfacing infrastructure and foundation
--   gaps as named theorems; and (iv) a wall-typology distinction
--   (infrastructure walls vs foundation walls) as a methodology
--   contribution. Completeness, multi-call generalization, the
--   `NoPhantomCalls` discharge for deployed contracts, deployed-protocol
--   instantiations, and broader EVM coverage (STATICCALL, DELEGATECALL,
--   CREATE/CREATE2, gas, REVERT-rollback, Vyper) are in progress."
--
-- The previous 2026-04-26 frozen claim was found by the 2026-04-28
-- 7-persona audit to be currently false in 4 of 5 substantive modifiers
-- (see an internal audit transcript §4 Q1, §8.1 B1-B5).
-- an internal phase report is marked SUPERSEDED.

import QanaryContracts.EVM
import QanaryContracts.Storage
import QanaryContracts.Step
import QanaryContracts.Reentrancy
import QanaryContracts.CEI
import QanaryContracts.Contract
import QanaryContracts.ValidExecution
import QanaryContracts.ReentrancyFree
import QanaryContracts.DAOAttack
import QanaryContracts.MultiFunction
import QanaryContracts.FunctionBody
import QanaryContracts.CEISufficiency
import QanaryContracts.Reachability
import QanaryContracts.CEISufficiencyV2
import QanaryContracts.OZSoundness
import QanaryContracts.Executes
import QanaryContracts.BodyTraceLift
import QanaryContracts.W8
import QanaryContracts.Completeness
import QanaryContracts.Tests
import QanaryContracts.Spikes
