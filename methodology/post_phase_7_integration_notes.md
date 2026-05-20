# Post-Phase-7 Methodology Framework Integration Notes

**Version:** 1.0
**Authored:** 2026-05-20, post-Phase-7-close methodology housekeeping cycle Unit 2.
**Authorizing PI:** Ray Iskander.
**Companion to:** the six canonical artifacts authored at Unit 1 (`directive_author_completeness_disciplines_family_canonical.md`; `cumulative_budget_reconciliation_canonical.md`; `page_budget_actual_compile_grounding_canonical.md`; `workflow_handoff_completeness_canonical.md`; `multi_lens_net_property_canonical.md`; `downgrade_rescue_differential_budget_canonical.md`).

---

## §1 Integration Deferral Rationale

The post-Phase-7-close housekeeping cycle is a **graduation-formalization** cycle, not a **framework-restructuring** cycle. The six canonical artifacts authored at Unit 1 capture patterns already operative at Phase 7 close; they do not introduce novel framework concepts requiring PADS / directive-template restructuring.

PADS + directive template revision should follow downstream-work-driven integration needs, not graduation-driven cycle. Specifically:

- PADS revisions should be triggered when a future Phase opening directive surfaces a PADS gap that one of the graduated patterns would close. Authoring PADS amendments speculatively at the housekeeping cycle risks over-fitting PADS to patterns that may evolve as additional empirical bases accumulate.
- Directive template revisions should be triggered when a future directive authoring would benefit from absorbing one of the patterns as a routine check. Phase 8 Session 61 (anonymization execution; re-measurement against anonymized compile) is a natural candidate for first template-absorbing directive.

This document catalogs absorption candidates for future cycles. It does not execute the absorption at this cycle.

---

## §2 PADS Integration Points (Deferred)

For each graduated artifact, identify specific PADS sections that could absorb the pattern as future amendment:

### §2.1 Multi-lens-net property (Artifact 5)

**PADS section:** audit-framework section (currently part of Amendment 3 v2.0 sub-phase decomposition; Decision 24 four-way audit voice; Decision 25 four-outcome triage).

**Candidate absorption:** PADS amendment could add a "framework decomposition discipline" subsection documenting:
- Sub-phase lens-diversity at decomposition design.
- Lens-coverage gap analysis at decomposition review.
- Multi-lens-net property as structural justification for sub-phase decomposition.

**Trigger:** when a future Phase requires audit-framework decomposition design (e.g., a future paper's Phase 7-equivalent extreme-audit pass), PADS-level absorption of the multi-lens-net property would inform the decomposition.

### §2.2 Workflow-handoff-completeness (Artifact 4)

**PADS section:** session-protocol section (currently part of Amendment 2 inter-session workflow specifications).

**Candidate absorption:** PADS amendment could formalize the three-component protocol (filename convention discipline; verification checkpoint; strategic-thread reminder commitment) as a documented session-protocol routine.

**Trigger:** Phase 8 inter-session transitions (Session 61 → 62 → community feedback period) will continue to apply the discipline; if any inter-session transition surfaces friction despite the discipline, PADS-level formalization would help.

### §2.3 Other artifacts

The cumulative-budget-reconciliation discipline (Artifact 2), page-budget-actual-compile-grounding discipline (Artifact 3), downgrade-rescue differential-budget pattern (Artifact 6), and the family-level umbrella (Artifact 1) are primarily **directive-template-level** patterns rather than **PADS-level** patterns. They operate at directive authoring + execution + adjudication; PADS integration is optional and lower-priority than directive-template integration.

If a future PADS revision occurs (e.g., Amendment 4 for arXiv-v2 cycle or for second QANARY paper), these patterns may inform PADS revision content; absent such revision trigger, PADS integration deferred indefinitely.

---

## §3 Directive Template (v2.1 → Potential v2.2) Integration Points (Deferred)

For each graduated artifact, identify specific template Parts that could absorb the pattern as future revision.

### §3.1 Cumulative-budget-reconciliation (Artifact 2)

**Template integration candidates:**

- **Mode catalog addition:** candidate Mode 12 (cumulative-budget-overcommitment). Mode 12 would fire at directive authoring time when per-item upper bounds sum exceeds cumulative ceiling without reconciliation. Mode catalog at v2.1 currently has Modes 1-8 + 10a/10c + 11; Mode 12 is the natural next addition.
- **Part 5 specification requirement:** add a routine sub-section "Cumulative budget reconciliation check" within Part 5 specifications when item count ≥ 3. Sub-section structure: sum per-item upper bounds; compare to cumulative ceiling; record reconciliation result.
- **Part 6 (Failure mode catalog) extension:** add Mode 12 details + integration with Mode 1 (HS-CUMULATIVE-CAP) escalation path.

**Trigger:** Phase 8 Session 61 directive authoring (or any subsequent directive with multi-item Outcome A specification) is the natural candidate for first invocation of the discipline procedurally.

### §3.2 Page-budget-actual-compile-grounding (Artifact 3)

**Template integration candidates:**

- **Part 3 pre-flight verification:** when document-class is binding via decision constraint, Part 3 specifies "measurement-grounded page-budget projection cited" as a routine pre-flight item. Specific Part 3 specification: "Most recent IEEEtran-compsoc measurement at-or-near-HEAD: [commit hash, page count, measurement date]. If stale by >10% manuscript delta or >2 weeks, schedule re-measurement before directive execution."
- **Part 0 Strategic Context routine:** cite the measurement-grounded projection at Strategic Context (not buried in Part 3) so reviewer-PI can verify at directive review.

**Trigger:** Phase 8 Session 61 directive authoring REQUIRES re-measurement against anonymized IEEEtran-compsoc compile per Session 60 closure report §7.5. That directive is the natural first invocation site.

### §3.3 Workflow-handoff-completeness (Artifact 4)

**Template integration candidates:**

- **Part 3 pre-flight verification:** when external audit findings (or other inter-session-produced artifacts) are expected, Part 3 specifies exact expected file count + filenames + halt criterion. Phase 7 Sessions 54-60 directives already operationalized this; v2.2 template would formalize.
- **Part 5 specification requirement:** when preflight folder population is part of a unit deliverable (e.g., authoring preflight folder README at session N for session N+1 consumption), Part 5 specifies filename convention adherence + strategic-thread reminder commitment.

**Trigger:** Phase 8 does NOT have a four-way audit voice deliverable; the discipline does not invoke at Session 61 directive authoring for audit findings. However, if Phase 8 re-measurement against anonymized compile is treated as an inter-session artifact (operator runs tectonic compile externally and provides PDF to Claude Code), the workflow-handoff-completeness discipline applies. Surface for Session 61 opening directive Part 3 specification.

### §3.4 Multi-lens-net property (Artifact 5)

**Template integration candidates:**

- **Part 0 Strategic Context framing element for sub-phase audit sessions:** when authoring a sub-phase audit session's opening directive, Part 0 Strategic Context cites the multi-lens-net property as the structural justification for the sub-phase's distinct lens. This framing helps Claude operational pair maintain lens-scope discipline at execution.
- **Decision 24 four-way audit voice complement:** at sub-phase audit sessions, four-way audit voice operationalizes WITHIN-sub-phase lens-diversity; multi-lens-net property operationalizes BETWEEN-sub-phase lens-diversity. The two patterns are complementary and should be cross-referenced at directive Part 0.

**Trigger:** future audit-cycle directives (Phase 7-equivalent for second paper) are the natural absorption candidates. Phase 8 does NOT have sub-phase audit decomposition.

### §3.5 Downgrade-rescue differential-budget (Artifact 6)

**Template integration candidates:**

- **Decision 25 four-outcome triage refinement:** add Outcome A sub-class structure to v2.2 template's Decision 25 framing:
  - Outcome A — compression
  - Outcome A — net-neutral submission-readiness
  - Outcome A — conditional expansion (with budget-routing specification)
- **Part 5 conditional-expansion specification:** when conditional expansion items exist, Part 5 specifies budget-routing (body / refs / appendix), priority order, and drop sequence if budget tight.

**Trigger:** future audit-cycle directives that execute Decision 25 four-outcome triage (Phase 7-equivalent for second paper). Phase 8 does NOT execute Decision 25.

### §3.6 Family-level umbrella (Artifact 1)

**Template integration candidates:**

- **Part 0 Strategic Context framing element:** family-level discipline framing at directive authoring time. Cite the family meta-pattern as the structural justification for the three sub-pattern checks (cumulative-budget-reconciliation + page-budget-actual-compile-grounding + workflow-handoff-completeness).
- **Mode catalog framing:** Mode 12 (cumulative-budget) and analogous future modes could be grouped under "family-level discipline modes" within the catalog.

**Trigger:** future template revision cycle (v2.2 or v3.0) authoring is the natural absorption candidate.

---

## §4 Recommended Absorption Sequencing

**Phase 8 Session 61 directive authoring** is the natural first candidate for template-absorbing directive. Specific recommendations:

1. **Mode 12 (cumulative-budget-overcommitment) addition** at Mode catalog if Session 61 directive has multi-item Outcome A specification.
2. **Part 3 measurement-grounding requirement** for re-measurement against anonymized IEEEtran-compsoc compile.
3. **Workflow-handoff-completeness discipline** at Part 3 pre-flight verification if Session 61 has inter-session artifact handoff (e.g., anonymized compile PDF).

**At Phase 8 Session 61 directive authoring**, evaluate whether to:
- (a) author Session 61 directive with manual application of disciplines (no template revision); the disciplines are graduated at canonical artifacts but not yet template-formalized.
- (b) author Session 61 directive AND simultaneously author v2.2 template revision (formal absorption).
- (c) defer template revision until v3.0 cycle (e.g., post-arXiv-v1 or post-venue-submission).

**Recommendation (audit-side preferred technical resolution):** option (a) — manual application at Session 61. Rationale: template revision is best authored after multiple absorbing directives have validated the absorption pattern; one-instance template revision at v2.2 may be premature.

**Subsequent absorption cycles:**

- *Post-arXiv-v1 + community feedback period:* if community feedback surfaces framework gaps, template revision cycle may be appropriate at that point.
- *Second QANARY-Contracts paper authoring* (or *cross-vendor audit paper authoring*): natural cycle for formal v2.2 template revision absorbing all six graduated artifacts. At that point, multi-paper absorption pattern will be more concrete.

---

## §5 Companion-Methodology-Paper Carrying-Forward

Per Decision 18 (methodology paper boundary), the six graduated canonical artifacts are companion-methodology-paper content. Companion paper authoring at future cycle will inherit these artifacts.

**Companion paper structure inheritance candidates:**

- Family-level chapter: directive-author-completeness disciplines family with three sub-pattern sections.
- Audit-framework chapter: multi-lens-net property + Decision 24 four-way audit voice + Decision 25 four-outcome triage.
- Adjudication-framework chapter: downgrade-rescue differential-budget pattern.

**Cross-references:** Phase 7 closure documents (Sessions 53–60 closure reports + pre-Session-59 measurement report) provide narrative empirical bases for each graduated artifact. Companion paper authoring inherits both the canonical artifacts (operational pattern statements) and the closure-report narrative (empirical context).

**Companion paper authoring is deferred to future cycle.** Current trajectory: QANARY-Contracts paper (this paper) → Phase 8 anonymization + arXiv v1 → community feedback → arXiv v2 → IEEE S&P 2027 venue submission. Companion paper authoring slots AFTER this trajectory or in parallel.

---

## §6 Future Graduation Pipeline Observations

**Patterns at lower empirical base (not graduating at this cycle):**

| Pattern | Empirical base | Threshold gap |
|---|---:|---|
| Mode 8 catalog discipline | 3 instances | Below typical 5+ threshold; defer until 4th instance |
| Mode-catalog-update authoring discipline | 1 instance (Mode 8 emergence) | Below threshold; defer until repeat pattern |
| Strategic-context preview-vs-execution alignment discipline | Multiple instances but overlap with cumulative-budget-reconciliation | Defer pattern-typing until distinguishable from family sub-patterns |
| Mid-execution re-scoping discipline (Path A retreat protocol) | 1 instance (Session 58) | Below threshold |
| Per-item-estimate calibration to historical execution | 2 instances (Sessions 58 + 60) | Below threshold; near; defer to next cycle |

**Sub-patterns within graduated artifacts at lower empirical base (future sub-pattern graduation candidates):**

- *Minimum-viable variant catalog* (within downgrade-rescue): 4 sub-variants at Session 60 (citation-only, appendix-only, net-neutral-hedging, hybrid co-location); defer formal catalog graduation until additional variants surface.
- *Leverage-weighted prioritization* (within downgrade-rescue): qualitative leverage at Session 60; formalization at future cycle.
- *Measurement-grade vs submission-grade clarification* (within page-budget-actual-compile-grounding): explicit caveat at pre-Session-59; standalone graduation candidate at future cycle.
- *SHA-256 verification of inter-session artifacts* (within workflow-handoff-completeness): 5 applications across Phase 7; could graduate standalone at future cycle.

**Meta-index recommendation (deferred to future cycle):** as the framework accumulates artifacts, a `methodology/INDEX.md` meta-index document cataloging all graduated artifacts + integration points + operational scope would help framework navigation. Defer to future cycle when artifact count reaches ~12-15.

---

## §7 Cross-References

- Six canonical artifacts authored at Unit 1 of this housekeeping cycle.
- Pre-existing canonical artifacts: `M-22.2_Tier1_canonical.md`; `authoring_layer_estimation_imprecision_canonical.md`.
- Closure report at the internal post-Phase-7 housekeeping closure report (Unit 3 of this cycle).
- Phase 7 closure documents at internal Phase-7 audit documents + internal Phase-7 audit documents (empirical context).
- PADS v1.3 at the internal PADS (unchanged at this cycle).
- v2.1 directive template at the internal v2.1 directive template (unchanged at this cycle).

---

**Document status:** SEALED at post-Phase-7-close housekeeping cycle Unit 3 atomic commit. Integration deferrals documented; absorption sequencing recommended; future graduation pipeline observed. PADS + template absorption to follow downstream-work-driven triggers per recommendations above.
