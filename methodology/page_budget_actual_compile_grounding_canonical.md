# Page-Budget Grounding in Actual Document-Class Compile — Canonical Specification

**Graduation provenance:** ratified at post-Phase-7-close methodology housekeeping cycle per opening directive Part 5 Unit 1; tagged at `v1.7-methodology-housekeeping`. Empirical base: pre-Session-59 measurement task (commit (internal commit)).
**Methodology framework status:** canonical sub-pattern within `directive_author_completeness_disciplines_family_canonical.md` family-level umbrella. Companion-methodology-paper content per Decision 18.
**Authored:** 2026-05-20.

---

## §1 Pattern Statement

**Page-budget grounding in actual document-class compile:** when document-class is binding via decision constraint (e.g., Decision 20 IEEEtran-compsoc binding Decision 22 13pp body ceiling), page-budget models must be grounded in actual document-class compile, not in markdown line/word count heuristics. Markdown-rendered page projections systematically under-estimate document-class actual rendering when wide tables, two-column layouts, references formatting, or other document-class-specific features differ materially from markdown defaults.

The discipline is a member of the **directive-author completeness disciplines family** (per family-level meta-pattern); its operational signature is *rendering-realism grounding at directive-authoring time when document-class is decision-bound*.

---

## §2 Empirical Instance

| Instance | Source | Projected pages | Actual pages | Refutation magnitude |
|---:|---|---:|---:|---:|
| 1 | pre-Session-59 measurement task; commit (internal commit) | Directive Path-B model: **~13.0pp body** (markdown line/word heuristic) | Actual IEEEtran-compsoc tectonic compile: **~16pp body** | **~3.0pp / ~23% under-estimation** |
| 1 (conservative variant) | pre-Session-59 measurement task; same commit | Conservative estimator: **~13.4pp body** (markdown + adjustment factor) | Actual IEEEtran-compsoc tectonic compile: **~16pp body** | **~2.6pp / ~19% under-estimation** |

**Detail of Instance 1 (pre-Session-59 measurement task; Branch C identification):**

The Session 58 SP3 closure directive Path B specification projected manuscript body landing at ~13.0pp post-SP3 execution (Path-B model). At Session 58 close, manuscript was at 585 lines / 15102 words. A conservative estimator (~13.4pp body) was also computed for risk-bounded estimation. Both projections used markdown line/word count heuristics: words-per-page constants derived from previous IEEEtran-compsoc artifact experience.

The pre-Session-59 measurement task (focused-scope; analogous to current housekeeping cycle in structure) ran the actual IEEEtran-compsoc tectonic compile against the post-SP3 manuscript and measured **body §1→§10 ≈ 16pp**. Both projections under-estimated actual rendering by ~2.6–3.0pp (~19–23%).

**Dominant inflation source identified at measurement:** four wide multi-column tables (§5.2 theorem inventory 5 cols; §6.2 line counts 3 cols; §10.3.2 axiom records 3 cols; §10.4.2 pointer table 3 cols) forced single-column `tabular` rendering with narrow `p{}` cells producing pathological vertical wrapping — recoverable via `table*` restructuring + prose collapse but not visible in markdown rendering.

**Consequence: Branch C identification.** Body at ~16pp vs Decision-22 13pp ceiling = ~3pp / ~23% OVER. SP5 was re-scoped from "substantive expansion + compression" to **compression-first** ("Branch C"). Session 60 SP5 closure landed body at ~12.97pp under ceiling via aggressive compression + wide-table restructuring + IEEEtran `\thebibliography` + repetition consolidation + other Phase 3.1 items.

---

## §3 Failure Mode Signature

**The signature:** directive page-budget planning based on optimistic markdown-rendered projections; operational reality at actual compile reveals binding-constraint violation; sub-phase scope re-classification required mid-trajectory.

**Operational manifestations:**

- *Best case:* pre-execution measurement task catches the gap; sub-phase scope re-adjudication occurs at directive-authoring time. **(Pre-Session-59 outcome.)**
- *Worse case:* measurement deferred until Unit 3 execution; mid-trajectory scope re-adjudication required with execution-time effort cost.
- *Worst case:* measurement deferred until closure check; manuscript lands non-compliant against decision-bound constraint; tag application blocked.

**Why pre-execution measurement matters:** markdown line/word counts are heuristic proxies that systematically under-estimate document-class rendering for documents with non-trivial structural complexity (multi-column tables, formal-document references, two-column layout). The measurement task itself is small-scope (~hours of work) compared to the cost of mid-trajectory re-scoping (~sessions of work).

---

## §4 Operational Protocol

**At directive authoring time when document-class is binding via decision constraint:**

1. **Identify the binding constraint:** explicit Decision-bound page budget (e.g., Decision 22 13pp body / 5pp refs); document-class specification (e.g., Decision 20 IEEEtran-compsoc).
2. **Check whether actual-compile measurement exists for current manuscript state:** is there a recent measurement at-or-near-current-HEAD that grounds the page-budget assumption?
3. **If measurement exists and is current:** use measurement-grounded projections; cite the measurement record in the directive's Part 0 Strategic Context.
4. **If measurement is stale or absent:** schedule an actual-compile measurement task BEFORE authoring directives whose execution depends on page-budget assumptions. Measurement task structure: focused-scope; reproducible scaffold; documented in a closure-style report at `paper/Phase{N}_pre_session{N}_measurement_report.md` or equivalent.
5. **Re-measure at intervals when manuscript changes materially:** rule of thumb: re-measure when cumulative manuscript delta since last measurement exceeds ~10% line/word count, OR when any wide-table restructuring / reference reformatting / section structure change has occurred.

**Measurement scaffold reproducibility:** the IEEEtran-compsoc measurement scaffold at `paper/ieeetran-measurement/` (tectonic engine + perl longtable→tabular transform + pandoc wrapper) was authored at pre-Session-59 measurement task and is reusable across subsequent measurements. Future document-class-bound projects should author analogous scaffolds.

**Documentation requirement:** the measurement-grounded projection should be cited at directive Part 0 Strategic Context. If measurement is recent and unchanged, cite by commit hash + page count. If measurement is stale, schedule re-measurement and surface in Part 3 pre-flight verification.

---

## §5 Prospective Application Guidance

**Invoke discipline when:**

- Directive's scope includes manuscript modifications likely to affect page-budget compliance.
- Decision-bound page budget exists (Decision 22 or equivalent).
- Document-class is binding via decision constraint (Decision 20 or equivalent).
- Manuscript has structural complexity (multi-column tables, formal-document references, two-column layout, footnotes).

**Skip discipline only when:**

- No decision-bound page budget exists.
- Document-class is flexible (e.g., arXiv-only release without conference page limits).
- Manuscript is small-scope and structurally simple.

**Decision rule:** when in doubt, invoke. Measurement task cost is ~hours; mid-trajectory re-scoping cost is ~sessions.

**Related anti-pattern:** "we'll just compile at closure and check the page count" — defers the measurement until consequences are baked in. The discipline is upstream-defense by construction.

---

## §6 Integration with Existing Framework

**Family-level umbrella:** `directive_author_completeness_disciplines_family_canonical.md`.

**Sibling sub-patterns within family:**
- `cumulative_budget_reconciliation_canonical.md` (sub-pattern 1; related budget-ceiling-realism dimension).
- `workflow_handoff_completeness_canonical.md` (sub-pattern 4; different completeness dimension).

**Related canonical artifacts (different families):**
- `authoring_layer_estimation_imprecision_canonical.md` — related estimation-imprecision pattern; markdown-line-counts-as-page-budget-proxy is a specific instance of estimation imprecision when measurement is determined externally (the EXTERNAL measurement being the document-class actual compile, not the markdown render).
- `multi_lens_net_property_canonical.md` — pre-Session-59 measurement task and SP5 wide-table issue are connected: the actual-compile measurement is the operational mechanism that made the SP5 lens efficacious. The page-budget grounding discipline and multi-lens-net property reinforce each other.

**PADS integration deferred:** PADS could absorb the page-budget-grounding requirement at Decision 22 or Decision 20 section; integration deferred per `post_phase_7_integration_notes.md`.

**v2.1 directive template integration deferred:** candidate Part 3 pre-flight verification requirement (when document-class is decision-bound); integration deferred. Phase 8 Session 61 directive authoring (anonymization execution) WILL require re-measurement against anonymized IEEEtran-compsoc compile per Session 60 closure report §7.5; that directive is a natural candidate for first formalized invocation of the discipline.

**Cross-reference:** the internal pre-Session-59 measurement report documents the canonical empirical instance; `paper/ieeetran-measurement/README.md` documents the reproducible measurement scaffold.

---

## §7 Carrying-Forward Observations

**Refinement candidates for future cycles:**

- *Automated measurement-grounding pre-issue check:* a directive-authoring-time tool that detects whether a recent measurement record exists at or near current HEAD; surfaces "measurement stale" warning if not. Manual discipline at authoring time is current state.
- *Sub-pattern-3 graduation candidate "measurement-grade vs submission-grade clarification":* at the pre-Session-59 measurement task, an explicit caveat was authored ("Page count is measurement-grade, not submission-grade"). The caveat captures a real distinction (e.g., authentic IEEEtran submission requires final typography tuning that the measurement compile does not perform). Future framework cycle may graduate the discipline of explicitly demarcating measurement-grade from submission-grade artifacts.
- *Calibration of markdown→document-class conversion factor:* empirical experience at pre-Session-59 suggests a ~1.2× markdown-line-count-to-rendered-page-count conversion factor for IEEEtran-compsoc with structural complexity comparable to QANARY-Contracts. Future projects can use this as starting-point calibration before running actual measurement.

**Related framework artifacts emerging from Phase 7:**

- Measurement scaffold at `paper/ieeetran-measurement/` is reusable across future projects. Recommend documenting as a standalone framework artifact (e.g., `methodology/document_class_measurement_scaffold_canonical.md`) at future cycle when a second project applies it.

**Empirical base extension:** ONE empirical instance at graduation. Subsequent applications (e.g., Phase 8 Session 61 re-measurement against anonymized compile) will accumulate the empirical base.

**Open framework question:** at what manuscript-delta threshold should re-measurement be triggered? Phase 7 used the rule "re-measure at Phase boundary"; finer-grained re-measurement (e.g., per-Unit re-measurement during sub-phase execution) was not adopted in Phase 7 but may be appropriate for future high-stakes work near page-budget ceiling.

---

**Canonization status:** SEALED at post-Phase-7-close housekeeping cycle Unit 3 atomic commit. Sub-pattern within directive-author-completeness-disciplines family-level meta-pattern.
