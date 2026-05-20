# Directive-Author Completeness Disciplines (Family-Level Meta-Pattern) — Canonical Specification

**Graduation provenance:** ratified at post-Phase-7-close methodology housekeeping cycle per opening directive Part 5 Unit 1; tagged at `v1.7-methodology-housekeeping`. Empirical base accumulated across Phase 7 Sessions 53–60 + pre-Session-59 measurement task; FIFTEEN+ single-instance observations — strongest empirical base of any methodology framework candidate at Phase 7 close.
**Methodology framework status:** canonical family-level meta-pattern; umbrella under which three graduated sub-patterns reside (cumulative-budget-reconciliation; page-budget-actual-compile-grounding; workflow-handoff-completeness). Companion-methodology-paper content per Decision 18.
**Authored:** 2026-05-20.

---

## §1 Pattern Statement

**Directive-author completeness disciplines family:** the family captures patterns where directive-authoring rigor at upstream stages prevents execution-time failures at downstream stages. Family members share the structural property that authoring-time effort (analysis, reconciliation, grounding, coordination) costs less than execution-time recovery from author-completeness gaps (hard stops, retreats, scope re-adjudication, mid-trajectory re-classification).

The family currently contains three graduated sub-patterns:

1. **Cumulative-budget-reconciliation discipline** (`cumulative_budget_reconciliation_canonical.md`) — operates at directive-authoring-time on per-item-budget ↔ cumulative-budget reconciliation.
2. **Page-budget-actual-compile-grounding discipline** (`page_budget_actual_compile_grounding_canonical.md`) — operates at directive-authoring-time on document-class-bound page projections.
3. **Workflow-handoff-completeness discipline** (`workflow_handoff_completeness_canonical.md`) — operates at inter-session-coordination protocol level on artifact-handoff completeness.

The family-level recognition is that these three patterns are not coincidentally co-occurring — they are instances of a common structural principle: **author completeness is the cheapest defense against execution-time discovery of constraint violations**.

---

## §2 Family-Level Empirical Base

Aggregate empirical evidence across Phase 7 (Sessions 53–60 + pre-Session-59 measurement task):

| Sub-pattern | Single-instance count | Notable instances |
|---|---:|---|
| Cumulative-budget-reconciliation | 1 hard-stop firing | Session 58 directive Path B exceeded by ~2.5× at execution |
| Page-budget-actual-compile-grounding | 1 measurement vs projection refutation | pre-Session-59 ~16pp actual vs ~13.0pp Path-B projection |
| Workflow-handoff-completeness | 5 prospective applications post-discovery + 2 pre-discovery friction observations | Sessions 54+56 pre-flight friction; Sessions 55+57+58+59+60 successful operationalization |
| **Family-level aggregate** | **15+ single-instance observations** | Strongest empirical base in framework |

**Why the family-level recognition matters:** absent the family-level umbrella, each sub-pattern reads as an isolated discipline. With the family-level umbrella, the patterns are recognized as instances of a common upstream-defense principle, enabling pattern transfer when future work surfaces a fourth sub-pattern instance.

---

## §3 Family-Level Failure Mode

The structural failure mode at the family level: **directive specifications that look complete at authoring time prove incomplete at execution time** because author-completeness gaps were not surfaced upstream. Each sub-pattern manifests this failure mode at a different completeness-gap dimension:

- *Cumulative-budget* gap: per-item upper bounds were not summed against cumulative budget ceiling at authoring time.
- *Page-budget-actual-compile* gap: rendering-realism was not grounded in actual document-class compile at authoring time.
- *Workflow-handoff* gap: filename/file-count expectations were not specified or verified at preflight folder authoring time.

In each case, the failure manifests as execution-time discovery of a constraint violation that author-time discipline could have prevented at near-zero cost.

**Generalization to future patterns:** when surfacing a candidate fourth sub-pattern, ask whether it shares the family signature — *authoring-time rigor preventing execution-time discovery of constraint violation*. If yes, the new pattern is a family member; if no, the new pattern is independent.

---

## §4 Family-Level Operational Protocol

At directive authoring time, run completeness disciplines per sub-pattern catalog before issuing directive:

1. **Cumulative-budget reconciliation check (per sub-pattern 1):** sum per-item upper word/line bounds across Part 5 specification; compare to cumulative budget ceiling per Part 6 Mode 1 cap structure; if sum exceeds ceiling, tighten per-item bounds OR adjust recommended consumption path OR reduce item count.

2. **Page-budget actual-compile grounding (per sub-pattern 2):** when document-class is binding via decision constraint (e.g., Decision 20 IEEEtran-compsoc binding Decision 22 13pp body ceiling), schedule an actual-compile measurement BEFORE authoring directives that depend on page-budget assumptions. Use measurement-grounded projections, not heuristic projections.

3. **Workflow-handoff completeness (per sub-pattern 3):** when next-session work depends on preflight folder artifacts, document exact expected filenames at preflight folder README + specify Part 3 pre-flight verification (file count + filename match) + commit to inter-session strategic-thread reminder.

These three checks are routine at the directive-authoring-time stage; expected aggregate completion time is minutes per directive.

---

## §5 Prospective Application Guidance

**When to invoke the family discipline:** at every directive authoring whose execution depends on either (a) per-item budget aggregation, (b) document-class-rendered page projections, or (c) preflight folder artifact handoff.

**Decision rule:** if the directive's Part 5 specification has more than 3 enumerated items with individual word/line bounds, run sub-pattern 1. If the directive references page-budget compliance per Decision 22, run sub-pattern 2. If the directive's Part 3 pre-flight verification specifies an external folder, run sub-pattern 3.

**Anti-patterns to avoid:** assuming per-item bounds sum to less than cumulative ceiling without bottom-up verification; using markdown line/word heuristics as page-budget proxies when document-class is binding; allowing strategic-thread to surface preflight-folder population without filename discipline.

---

## §6 Integration with Existing Framework

**Cross-references:**

- Sub-pattern artifacts: `cumulative_budget_reconciliation_canonical.md`; `page_budget_actual_compile_grounding_canonical.md`; `workflow_handoff_completeness_canonical.md`.
- Independent canonical artifacts (NOT in this family but graduated at same housekeeping cycle): `multi_lens_net_property_canonical.md` (audit-framework property; not directive-authoring); `downgrade_rescue_differential_budget_canonical.md` (adjudication-framework refinement; not directive-authoring).
- Pre-existing canonical artifacts: `M-22.2_Tier1_canonical.md` (theorem-composition discipline; different family); `authoring_layer_estimation_imprecision_canonical.md` (estimation-imprecision pattern; related family-level meta-pattern at a different stage of authoring discipline).

**PADS integration deferred:** PADS could absorb the family-level recognition at a future amendment; integration deferred per `post_phase_7_integration_notes.md`.

**v2.1 directive template integration deferred:** template could absorb the three sub-pattern checks as Part 3 or Part 5 routine items; integration deferred per `post_phase_7_integration_notes.md`. Phase 8 Session 61 directive authoring is a natural candidate for first family-discipline-aware directive.

---

## §7 Carrying-Forward Observations

**Candidate family-fourth sub-patterns at lower empirical base (future cycles):**

- *Strategic-context preview-vs-execution alignment discipline:* author Part 0 strategic context to match what execution will surface, not what authoring time assumes. Observed at Sessions 58–60 but with substantial overlap with cumulative-budget-reconciliation; defer pattern-typing.
- *Directive-template-version reference discipline:* explicit template version cite at every directive (v2.1 at Phase 7); seen consistently but procedurally trivial; below pattern-graduation threshold.
- *Mode-catalog-update authoring discipline:* when an authored directive encounters a novel failure mode at execution, update Mode catalog before next directive; observed at Mode 8 emergence Session 55–57; ONE-INSTANCE for distinct mode emergence; defer until repeat pattern.

**Related family-level meta-patterns elsewhere in framework:**

- *Authoring-layer estimation imprecision when measurement is determined externally* (`authoring_layer_estimation_imprecision_canonical.md`) — operates at the estimation-imprecision dimension; different family from directive-author-completeness disciplines but shares the structural insight that authoring-time effort can be misdirected when downstream realities are not surfaced upstream.

**Open framework question (carrying forward):** automated directive-completeness-check pre-issue tool. Current discipline is manual at directive authoring; future framework extension could automate sub-pattern checks (e.g., a pre-issue lint that sums per-item word bounds and reports against cumulative ceiling). Defer to future framework engineering cycle.

---

**Canonization status:** SEALED at post-Phase-7-close housekeeping cycle Unit 3 atomic commit. Family-level umbrella enables future pattern transfer when fourth sub-pattern surfaces empirically.
