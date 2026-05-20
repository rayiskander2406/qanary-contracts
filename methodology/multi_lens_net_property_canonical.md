# Multi-Lens-Net Property — Sub-Phase Execution-Gap Detection via Lens-Consecutiveness — Canonical Specification

**Graduation provenance:** ratified at post-Phase-7-close methodology housekeeping cycle per opening directive Part 5 Unit 1; tagged at `v1.7-methodology-housekeeping`. Empirical base accumulated across Phase 7 Sessions 57+58+59+60.
**Methodology framework status:** canonical independent pattern (audit-framework property; NOT within directive-author-completeness-disciplines family). Companion-methodology-paper content per Decision 18.
**Authored:** 2026-05-20.

---

## §1 Pattern Statement

**Multi-lens-net property:** the multi-lens-net property describes a structural feature of multi-sub-phase audit frameworks: consecutive lenses with different scopes catch what predecessor lenses couldn't, including predecessor execution gaps. Each sub-phase has scope-boundary blindness about what it doesn't audit; the framework's value proposition is that lens-consecutiveness exposes execution gaps not visible to any single lens.

**Two operational variants:**

- *Execution-gap-net:* when a predecessor sub-phase produced an Outcome A revision whose downstream destination was deferred or under-executed, the next sub-phase whose lens covers the destination catches the dangling reference.
- *Scope-coverage-net:* when a predecessor sub-phase's audit scope did NOT include a rendering dimension or compile dimension, the next sub-phase whose lens covers that dimension catches the dimension-dependent defect.

Both variants describe the same structural mechanism: lens-consecutiveness provides cross-coverage that any single lens cannot.

This pattern is **NOT a member** of the directive-author-completeness-disciplines family (per family-level meta-pattern at `directive_author_completeness_disciplines_family_canonical.md`); it is an independent audit-framework property operating at the audit-decomposition design level.

---

## §2 Empirical Instance Enumeration

| Instance | Session | Variant | Cross-coverage demonstrated |
|---:|---|---|---|
| 1 | S57 SP3 A1 | Execution-gap-net | SP1 (Session 53) added §1.3 pointer to §3.3; SP2 (Session 55) deliverable to add §3.3 fifth assumption was not executed; SP3 (Session 57) caught the dangling reference at audit time |
| 2 | S57 SP3 A6 | Scope-coverage-net | SP1 / SP2 did not include mutation-testing-literature engagement scope; SP3 (Session 57) surfaced the absence at argumentation-lens scope |
| 3 | S57 SP3 A7 | Execution-gap-net | SP2 (Session 55) deferred AI-FV citations to SP3; SP3 (Session 57) surfaced and triaged for Outcome A action |
| 4 | **S59 SP5 wide-table** | **Scope-coverage-net** (canonical Phase-7 example) | SP1 (Session 53) audited markdown structure; SP2 (Session 55) audited table content correctness; SP3 (Session 57) audited table rhetoric; NONE audited at actual document-class compile because markdown rendering hides multi-column-incompatibility; SP5 lens at actual IEEEtran-compsoc compile surfaced the layout collision |

**FOUR empirical instances across Sessions 57+58+59+60.** Variant distribution: 2 execution-gap-net + 2 scope-coverage-net.

**Detail of canonical Phase-7 example (Instance 4, SP5 wide-table issue):**

Four wide multi-column tables (§5.2 theorem inventory 5 cols; §6.2 line counts 3 cols; §10.3.2 axiom records 3 cols; §10.4.2 pointer table 3 cols) were present in the manuscript throughout SP1+SP2+SP3 audit lenses. None of these lenses surfaced a defect against the tables because:

- *SP1 (structural lens):* audited markdown structure + section organization + claim-site mapping. Tables in markdown look fine; no structural issue.
- *SP2 (technical lens):* audited table cell content correctness + CI mechanism verification + axiom-record accuracy. Table content was correct.
- *SP3 (argumentation lens):* audited table rhetoric + reviewer-mental-model implications. Tables' rhetorical function was fine.

Only the **SP5 lens at actual IEEEtran-compsoc compile** (pre-Session-59 measurement task) surfaced the wide-table layout collision: forced single-column `tabular` with narrow `p{}` cells producing pathological vertical wrapping = dominant inflation source explaining the ~3pp body overage vs Decision-22 13pp ceiling.

The SP1+SP2+SP3 markdown-rendered audits couldn't surface this because markdown rendering doesn't render multi-column-incompatibility. The defect was structurally invisible to any single pre-SP5 lens because **no pre-SP5 lens audited against actual document-class compile**.

---

## §3 Failure Mode Description

**The signature:** structural defects that single-lens audit cannot detect because they manifest only at downstream-lens scope (e.g., rendering-only-visible defects; cross-sub-phase-execution gaps; compile-time-only-visible defects).

**Why the multi-lens-net property is value-generating:** absent the property, audit frameworks rely on each lens being comprehensive at its scope. With the property, audit frameworks rely on lens-diversity — the lens-consecutiveness structure provides cross-coverage that individual lenses cannot.

**Operational manifestations:**

- *Best case:* multi-lens-net catches the defect at the appropriate downstream lens; framework operates as designed; Phase closes successfully. **(All four Phase 7 instances.)**
- *Worse case:* multi-lens-net structure exists but framework decomposition was poor; consecutive lenses have overlapping scopes; cross-coverage is illusory; defects propagate to closure.
- *Worst case:* multi-lens-net structure is absent (single-lens audit framework); defects accumulate undetected across audit cycles.

**Why this matters at the framework level:** the multi-lens-net property is a structural feature of multi-sub-phase audit framework DESIGN, not a discipline applied at execution time. The pattern informs how to decompose audit work into sub-phases (e.g., the Phase 7 PADS Amendment 3 sub-phase decomposition was designed to maximize lens-diversity), and how to operationalize each lens (e.g., the SP5 lens was operationalized via actual document-class compile, not via markdown render).

---

## §4 Operational Protocol

**At audit framework decomposition (typically authored once per major phase):**

1. **Identify the dimensions to audit:** what aspects of the manuscript / artifact need adversarial + co-creative scrutiny? (E.g., structural, technical, argumentation, submission-readiness for Phase 7.)
2. **Map dimensions to sub-phases:** ensure each sub-phase has a primary lens scope. Decision rule: consecutive lenses should have NON-OVERLAPPING primary scopes; lens-diversity is the goal.
3. **Verify cross-coverage at framework design time:** for each dimension, ensure at least one sub-phase's lens covers it. Surface lens-coverage gaps as framework design defects to address before authoring sub-phase opening directives.
4. **Operationalize each lens distinctively:** for technical lens, ground in repo verification; for argumentation lens, ground in reviewer-archetype anchoring; for submission-readiness lens, ground in actual document-class compile. Lens-distinctiveness is what creates cross-coverage.

**At sub-phase audit execution (per sub-phase):**

1. Apply the sub-phase's lens at its full scope.
2. Note findings that surface predecessor sub-phase Outcome A execution gaps; classify as multi-lens-net findings (per Phase 7 Session 57 example, finding A1 etc.).
3. Document multi-lens-net findings with explicit reference to predecessor sub-phase context.

**At Phase close (housekeeping cycle):**

1. Catalog multi-lens-net instances surfaced during Phase (per this canonical artifact's §2).
2. Evaluate framework decomposition for lens-coverage: were any dimensions under-covered? Surface for next-phase decomposition refinement.

---

## §5 Prospective Application Guidance

**Apply pattern when:**

- Audit framework has 3+ sub-phases with intended lens-diversity.
- Manuscript / artifact has structural complexity that single-lens audit may miss (multi-column tables; cross-section references; rendering-dependent dimensions; submission-readiness dimensions).
- Audit cycle spans multiple sessions with inter-session gaps (where lens-execution may drift from framework-designed scope).

**Skip pattern when:**

- Audit framework is single-lens (no sub-phase decomposition); the property doesn't apply.
- Audit scope is narrow (single dimension); cross-coverage is unnecessary.

**Decision rule:** multi-lens-net property applies to most Phase-7-style extreme-audit frameworks. Single-lens frameworks should consider whether decomposition would add value via the property.

---

## §6 Integration with Existing Framework

**Independent from directive-author-completeness-disciplines family.** Multi-lens-net property is an audit-framework property at the framework-design level; not a directive-authoring discipline.

**Related canonical artifacts:**

- `page_budget_actual_compile_grounding_canonical.md` — operational mechanism that made the SP5 lens efficacious. Multi-lens-net property AND page-budget-actual-compile-grounding reinforce each other: the page-budget grounding ensures SP5 lens has the document-class compile to audit against; multi-lens-net property explains why the SP5 lens catches what SP1+SP2+SP3 markdown lenses couldn't. Both patterns are operationally connected at the SP5 wide-table canonical example.
- `workflow_handoff_completeness_canonical.md` — supports multi-lens-net property by ensuring external-voice findings reach the next sub-phase's consolidation step. The four-way audit voice framework (Decision 24) operationalizes lens-diversity WITHIN each sub-phase; workflow-handoff-completeness ensures the external-voice artifacts arrive intact at next-session consolidation.

**Decision 24 four-way audit voice relationship:** four-way audit voice provides WITHIN-sub-phase lens-diversity (four voices per sub-phase = four within-sub-phase lenses on the same manuscript scope). Multi-lens-net property provides BETWEEN-sub-phase lens-diversity (consecutive sub-phases = different lenses on different scopes). The two patterns are complementary and operate at different levels of lens-diversity.

**Decision 25 four-outcome triage relationship:** multi-lens-net findings typically classify as Outcome A (act-now) under Decision 25 because they surface defects requiring correction at the current sub-phase rather than deferring to a later cycle. The four-outcome triage framework absorbs multi-lens-net findings naturally.

**Phase 7 PADS Amendment 3 v2.0 relationship:** the sub-phase decomposition at PADS Amendment 3 v2.0 (SP1 structural → SP2 technical → SP3 argumentation → SP5 submission-readiness; SP4 absorbed into SP5) was framework-designed to maximize lens-diversity. The multi-lens-net property is the structural justification for the decomposition.

**PADS integration deferred:** PADS could absorb multi-lens-net property at the audit-framework section; integration deferred per `post_phase_7_integration_notes.md`.

**v2.1 directive template integration deferred:** candidate Part 0 Strategic Context framing element for sub-phase audit sessions; integration deferred.

**Cross-reference:** Phase 7 Session 57 closure report at commit (internal commit) introduces the multi-lens-net property concept at SP3 entry; Phase 7 Session 60 closure report §5 documents the canonical Phase-7 example (SP5 wide-table).

---

## §7 Carrying-Forward Observations

**Refinement candidates for future cycles:**

- *Automated lens-coverage gap analysis:* given a sub-phase decomposition (e.g., SP1+SP2+SP3+SP5 at Phase 7), identify which dimensions are NOT covered by any lens. Current framework relies on lens-consecutiveness empirically rather than coverage-analytically. Future framework extension could compute coverage matrices.
- *Cross-phase multi-lens-net property:* the Phase-7 instances are all WITHIN-phase (between sub-phases of Phase 7). Future framework cycle could explore CROSS-phase multi-lens-net (e.g., Phase 7 closure findings surface gaps in Phase 6 manuscript-writing trajectory; Phase 8 anonymization surfaces gaps in Phase 7 closure). Cross-phase multi-lens-net is not yet pattern-graduated but is implicit in the Phase trajectory structure.
- *Multi-lens-net property at within-sub-phase scale:* the four-way audit voice framework (Decision 24) provides four lenses per sub-phase. The multi-lens-net property may apply at this scale too (e.g., Grok catches what Gemini missed; Claude independent fresh catches what Claude session-context missed). Phase 7 closure documents this implicitly via convergence/divergence analysis at Unit 1 consolidation; future framework cycle could formalize within-sub-phase multi-lens-net.

**Empirical base extension:** FOUR empirical instances at graduation across Sessions 57+58+59+60. Future audit frameworks (e.g., second smart-contracts paper; cross-vendor audit paper) will accumulate additional instances.

**Open framework question:** is the multi-lens-net property an emergent property or a designed property? Phase 7 evidence suggests both: the framework was DESIGNED for lens-diversity (PADS Amendment 3 v2.0 sub-phase decomposition), and the property EMERGED as empirically validated at each closure cycle. Future framework cycle may explore the design-vs-emergence distinction more rigorously.

**Phase 8 carrying-forward:** Phase 8 (anonymization + ORCID + GenAI + formatting + arXiv v1) does NOT have a multi-sub-phase audit framework; the multi-lens-net property does not directly apply. However, post-arXiv-v1 community feedback period can be interpreted as a meta-lens (community lens at scope NOT covered by SP1–SP5). Defer cross-phase multi-lens-net property exploration to post-community-feedback cycle.

---

**Canonization status:** SEALED at post-Phase-7-close housekeeping cycle Unit 3 atomic commit. Independent pattern (audit-framework property); not within directive-author-completeness-disciplines family.
