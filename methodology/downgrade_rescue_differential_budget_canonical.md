# Downgrade-Rescue via Differential Budget Constraint Exploitation — Canonical Specification

**Graduation provenance:** ratified at post-Phase-7-close methodology housekeeping cycle per opening directive Part 5 Unit 1; tagged at `v1.7-methodology-housekeeping`. Empirical base: Session 59 strategic insight + Session 60 SP5 closure execution validation (C4 pattern).
**Methodology framework status:** canonical independent pattern (adjudication-framework refinement; NOT within directive-author-completeness-disciplines family). Companion-methodology-paper content per Decision 18.
**Authored:** 2026-05-20.

---

## §1 Pattern Statement

**Downgrade-rescue via differential budget constraint exploitation:** when multiple budget constraints apply (e.g., body 13pp / refs 5pp / appendix; conditional expansion vs net-neutral vs compression), recognize that compression-first scope may apply to ONE budget while another budget has headroom. The "funding-asset" framing that collapses multiple budgets into one pool can over-constrain rescue scope.

The pattern routes scope items to the unconstrained budget: items that would otherwise downgrade to companion-paper / permanent-deferral can land **minimum-viable** as:

- Citation additions (refs budget).
- Net-neutral hedging (compression headroom).
- Appendix-only landings (refs+appendix budget).

— at compression-budget-neutral cost.

This pattern is **NOT a member** of the directive-author-completeness-disciplines family (per family-level meta-pattern); it is an independent adjudication-framework refinement operating at the Decision 25 four-outcome triage level.

---

## §2 Empirical Instance — Branch C SP5 Canonical Example

| Stage | Session | Application | Outcome |
|---|---|---|---|
| Recognition | S59 SP5 entry | Strategic insight: pre-Branch-C framing collapsed body and refs into "SP5 funding asset" mental model; Branch C re-scoping presumed everything downgrades; SP5 audit corrected | Refs/appendix at ~3pp / 5pp budget has substantial headroom while body is over-constrained |
| Application 1 | S60 SP5 closure Phase 3.4 | A6 Compound v2 OZ hedge expansion at §5.4 | +0.05pp body (within conditional-expansion headroom) |
| Application 2 | S60 SP5 closure Phase 3.4 | C4 capstone Lean theorem statement at §5.6 | +0.10-0.15pp body (within conditional-expansion headroom) |
| Application 3 | S60 SP5 closure Phase 3.4 | C5 §10.5 appendix comparison table | +0.15pp REFS (refs budget; doesn't compete with body ceiling) |
| Application 4 | S60 SP5 closure Phase 3.4 | A11 disclosure hybrid path at §5.4 (co-located with A6) | +0.02pp body (PI-elected Path 3 hybrid; lowest-cost route) |

**FOUR successful applications at Session 60 SP5 closure execution** validating the strategic insight from Session 59.

**Detail of canonical application (Session 60 SP5 closure):**

At Session 59 SP5 entry, the pre-Branch-C SP5 docket projected substantial body-budget consumption across Convergent-1 (in-body theorem statements; ~+0.5-1.0pp), Convergent-6 (in-body comparison table; ~+0.4pp), A-RW (extended related work; ~+0.4pp), A-EV (extended evaluation; ~+0.4pp), and other items. Body was at ~16pp vs 13pp ceiling — ~3pp over.

The Branch C re-scoping presumed most pre-Branch-C SP5 items downgrade to companion-paper or permanent-deferral. The "SP5 funding asset" framing (the prior session's framing) treated body + refs + appendix as a unified ~+0.9-1.0pp budget that could be consumed by any of these items.

The Session 60 SP5 audit corrected the framing:

- *Body budget:* 13pp ceiling; binding constraint; ~3pp OVER at SP5 entry.
- *Refs budget:* 5pp ceiling; ~3pp at SP5 entry; ~2pp headroom available.
- *Appendix budget:* part of refs+appendix 5pp; ~headroom subject to refs+appendix joint constraint.

The differential budget constraint exploitation: instead of full-downgrading items requiring body addition, route to the unconstrained budget:

- *C5 (in-body comparison table):* downgrade to appendix-only `table*` (`§10.5`). Refs+appendix budget has headroom; body budget doesn't. **Compression-budget-neutral on body.**
- *C4 (in-body Lean theorem statements):* downgrade most layers to appendix paraphrase; keep capstone-only in-body Lean theorem. **Minimum-viable on body; full theorem catalog at §10.3.**
- *A-RW (extended related work):* downgrade to citation-only-addition variant (refs budget). Refs budget has headroom; body budget doesn't.
- *A6 (Compound v2 OZ hedge):* minimum-viable expansion (~+0.05pp body) using compression headroom from Phase 3.1 compression.
- *A11 (disclosure):* minimum-viable hybrid path (~+0.02pp body) co-located with A6 (lowest-cost route).

**Aggregate result:** rather than 4-5 full-downgrades to companion-paper, all items landed minimum-viable at conditional-expansion-budget-neutral cost. Body landed at ~12.97pp under ceiling; appendix at ~3pp within budget; both budgets compliant.

---

## §3 Failure Mode Description

**The signature (when pattern is NOT applied):** over-deferral to companion-paper / permanent-deferral when differential-budget headroom is available; loss of substantive coverage when minimum-viable rescues are feasible.

**Operational manifestations:**

- *Best case:* differential-budget analysis surfaces unconstrained budgets; rescue items route to unconstrained budgets; substantive coverage preserved at minimum-viable scope. **(Session 60 SP5 outcome.)**
- *Worse case:* differential-budget analysis missed; items full-downgrade to companion-paper; substantive coverage thin at this paper; companion-paper bears load that current paper could have carried.
- *Worst case:* over-collapse of multiple budgets into unified pool; rescue items deemed infeasible when in fact unconstrained budget exists; cascade of unnecessary deferrals.

**Why differential-budget framing matters:** budget pools are not always fungible. A "13pp body + 5pp refs" budget constraint is NOT a "18pp combined" constraint — items have different natural homes. Body content can sometimes be appendix content; in-body tables can sometimes be appendix tables; in-body theorem statements can sometimes be appendix paraphrases. The differential-budget framing exploits these substitutions.

---

## §4 Operational Protocol

**At Decision 25 four-outcome triage time, run the following analysis:**

1. **Separate budget constraints by binding status.** For each binding budget (e.g., Decision 22 13pp body), and each non-binding budget (e.g., 5pp refs with ~2pp headroom), document current state and remaining capacity.

2. **For each item proposed for Outcome B (downgrade to companion-paper / permanent-deferral):**
   - Evaluate whether minimum-viable variant exists that lands in an unconstrained budget.
   - Candidate routings:
     - *Citation-only* (refs budget): if item is citation-eligible, can it land as 1-3 new citations + brief context?
     - *Appendix-only* (appendix budget): if item is structurally tabular or list-form, can it land as `\table*` or `\verbatim` block in appendix?
     - *Net-neutral-hedging* (compression headroom): if item is a softening or scope-qualification, can it land at zero body delta via wording reformulation?
     - *Hybrid* (co-location with adjacent item): can item co-locate at existing edit site (e.g., A11 + A6 co-location at §5.4)?
   - If minimum-viable variant exists in unconstrained budget, classify as conditional Outcome A (sub-class: conditional expansion).
   - If NO minimum-viable variant lands in unconstrained budget, confirm Outcome B downgrade.

3. **At conditional expansion priority ordering:**
   - Items targeting refs/appendix budget execute first (no body competition).
   - Items targeting body compression headroom execute by reviewer-trust leverage (HIGH leverage first).
   - Items dropping first when budget tight: lowest-leverage body-budget items.

4. **Documentation requirement:** the differential-budget analysis should be recorded at directive Part 5 Outcome A specification (sub-class: conditional expansion) with priority order + drop sequence.

---

## §5 Prospective Application Guidance

**Apply pattern when:**

- Multiple budget constraints apply with different binding status.
- Outcome B items in adjudication include candidates for minimum-viable variants in unconstrained budgets.
- Decision 25 four-outcome triage is being executed for sub-phase closure or similar adjudication-bound scope.

**Skip pattern when:**

- All budgets are uniformly binding (no differential available).
- All Outcome B items are structurally body-required (no minimum-viable variants in other budgets).

**Decision rule:** when in doubt, run the analysis. The differential-budget analysis is procedurally trivial (~minutes); the failure cost is loss of substantive coverage to companion-paper that current paper could have carried.

**Anti-pattern:** treating budget pools as fungible (e.g., "we have +1pp combined to spend") when in fact pools have different natural homes. The "funding-asset" framing collapses pools into a single budget; downgrade-rescue framing keeps pools separated.

---

## §6 Integration with Existing Framework

**Independent from directive-author-completeness-disciplines family.** Downgrade-rescue is an adjudication-framework refinement; not a directive-authoring discipline.

**Decision 25 four-outcome triage relationship:** downgrade-rescue refines the Outcome A categorization to introduce sub-classes:

- Outcome A — compression (Phase 3.1 at Session 60 SP5)
- Outcome A — net-neutral submission-readiness (Phase 3.2)
- **Outcome A — conditional expansion (Phase 3.4; gated by re-measurement headroom)** ← downgrade-rescue lands here

The Branch-C-specific outcome framing introduced at Session 60 Unit 2 SP5 adjudication formalized this sub-class structure; downgrade-rescue is the operational pattern that justifies the sub-class.

**Related canonical artifacts:**

- `page_budget_actual_compile_grounding_canonical.md` — measurement-grounded projections enable the differential-budget analysis (without measurement-ground, the budget separation may not be reliable).
- `cumulative_budget_reconciliation_canonical.md` — operates at directive-authoring-time on per-item ↔ cumulative reconciliation; downgrade-rescue operates at adjudication-time on differential-budget-routing. Both depend on accurate budget accounting.

**Decision 18 relationship:** downgraded items in Outcome B route to companion methodology paper per Decision 18. Downgrade-rescue prevents over-deferral to companion paper when minimum-viable rescues are feasible in current paper. The pattern complements Decision 18 by sharpening the "what belongs in which paper" question.

**PADS integration deferred:** PADS could absorb the differential-budget framing at Decision 25 section; integration deferred per `post_phase_7_integration_notes.md`.

**v2.1 directive template integration deferred:** candidate Decision 25 refinement (Outcome A sub-class structure: compression / net-neutral / conditional expansion with budget-routing specification); integration deferred. Phase 8 Session 61 directive does NOT execute Decision 25 (anonymization is not subject to four-outcome triage); future audit-cycle directives may absorb the refinement.

**Cross-reference:** Phase 7 Session 59 closure report at commit (internal commit) introduces the C4 pattern recognition; Phase 7 Session 60 Unit 2 adjudication at commit (internal commit) formalizes the Branch-C-specific outcome framing; Session 60 Unit 3 commit (internal commit) validates four applications at execution.

---

## §7 Carrying-Forward Observations

**Refinement candidates for future cycles:**

- *Sub-pattern graduation candidate "minimum-viable variant catalog":* the minimum-viable variants surfaced at Session 60 (citation-only, appendix-only, net-neutral-hedging, hybrid co-location) suggest a canonical catalog of substitution options. Future framework cycle could enumerate the catalog more rigorously with operational protocols per variant type.
- *Sub-pattern graduation candidate "leverage-weighted prioritization":* the prioritization order (HIGH-leverage first; LOW-leverage drops first) at Session 60 Phase 3.4 suggests a leverage-weighting framework. Currently leverage is qualitative (FM-trust, SCA-trust, PC-trust); future framework cycle could formalize leverage-weighted priority computation.
- *Cross-budget routing intelligence:* the current downgrade-rescue pattern routes items based on author judgment of natural-home fit. Future framework extension could formalize routing as a constraint-satisfaction problem (items × budgets matrix; capacity constraints; leverage maximization objective).

**Empirical base extension:** ONE strategic-insight instance (Session 59) + FOUR execution-application instances (Session 60). Subsequent applications (e.g., future audit-cycle directives) will accumulate the empirical base.

**Open framework question:** when is full-downgrade to companion-paper actually superior to minimum-viable-rescue? Phase 7 evidence suggests minimum-viable-rescue is almost always preferable when feasible. Future framework cycle may surface counter-examples where full-downgrade strengthens both papers (e.g., Convergent-6 full-comparison-table at companion paper may better serve companion paper than appendix-only at current paper).

**Phase 8 carrying-forward:** Phase 8 (anonymization + ORCID + GenAI + formatting + arXiv v1) does NOT execute Decision 25 four-outcome triage; downgrade-rescue does not directly apply. However, the pattern informs Phase 8 anonymization strategy: when anonymization removes substantive content (author names, GitHub URLs, etc.), the differential-budget framing may help recover coverage via citation, appendix, or hedging substitutions.

---

**Canonization status:** SEALED at post-Phase-7-close housekeeping cycle Unit 3 atomic commit. Independent pattern (adjudication-framework refinement); not within directive-author-completeness-disciplines family.
