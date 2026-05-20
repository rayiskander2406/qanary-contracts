# Cumulative-Budget-Reconciliation Discipline at Directive Authoring Time — Canonical Specification

**Graduation provenance:** ratified at post-Phase-7-close methodology housekeeping cycle per opening directive Part 5 Unit 1; tagged at `v1.7-methodology-housekeeping`. Empirical base: Session 58 hard-stop firing.
**Methodology framework status:** canonical sub-pattern within `directive_author_completeness_disciplines_family_canonical.md` family-level umbrella. Companion-methodology-paper content per Decision 18.
**Authored:** 2026-05-20.

---

## §1 Pattern Statement

**Cumulative-budget-reconciliation discipline:** when a directive specifies per-item word/line bounds AND a cumulative budget ceiling (e.g., per-finding word allowances against a Decision-22-style page-budget ceiling), the per-item upper bounds must be reconciled against the cumulative ceiling at authoring time. Pre-recommending a budget consumption path (e.g., "Path B at ~+0.45pp ceiling") before bottom-up modeling the sum of per-item upper bounds is the failure mode.

Reconciliation discipline catches infeasibility at directive authoring time rather than at directive execution time, where the only remaining responses are: (a) hard-stop firing followed by retreat, (b) mid-execution scope re-adjudication, or (c) ceiling violation with downstream consequences.

The discipline is a member of the **directive-author completeness disciplines family** (per family-level meta-pattern); its operational signature is *cumulative-budget-aggregation at authoring time*.

---

## §2 Empirical Instance

| Instance | Session | Hard-stop type | Magnitude | Resolution |
|---:|---|---|---:|---|
| 1 | S58 Unit 3 | Page-budget hard-stop firing at cumulative execution trending toward Decision-22 ceiling | Directive Path B model: +480w cumulative; Outcome A 17-item scaffolding summed at upper bounds: ~+1215w; **exceeded recommended Path B ceiling by ~2.5×** | Path A retreat with modification; final body net ~+541w; manuscript 567→585L / 14440→15102w |

**Detail of Instance 1 (Session 58 directive Path B specification + execution gap):**

The Session 58 directive authored a 17-item Outcome A scaffolding for SP3 closure execution. Each Outcome A item had a per-item word/line estimate (~30–250 words per item). The cumulative budget ceiling (Decision 22 13pp body ≤ +480w from baseline per Path B model) was pre-specified at Strategic Context. The 17 per-item upper bounds, summed, would land at ~+1215w — 2.53× the recommended Path B ceiling.

The discipline gap: per-item upper bounds were authored in Part 5 specifications; cumulative budget was discussed in Part 0 Strategic Context; the bottom-up sum was not computed at authoring time. Execution at Unit 3 surfaced the gap as a hard-stop firing per Mode 1 (HS-CUMULATIVE-CAP) when cumulative execution trended toward the Decision-22 13pp body ceiling. The hard stop forced Path A retreat (per directive failure mode protocol), with the net body landing at ~+541w — well within ceiling but 11 of 17 originally-specified Outcome A items completed via Path A retreat rather than the originally-specified Path B execution.

---

## §3 Failure Mode Signature

**The signature:** hard-stop firing at directive execution because cumulative budget proved insufficient for sum of per-item commitments.

**Operational manifestations:**

- *Best case:* hard-stop fires, retreat path is well-specified, manuscript lands compliant. **(Session 58 outcome.)**
- *Worse case:* hard-stop fires, retreat path is poorly-specified, manuscript lands compliant via ad-hoc mid-execution adjudication.
- *Worst case:* hard-stop firing rule is unclear, manuscript lands non-compliant against decision-bound constraint.

**Why the discipline matters even when best-case unfolds:** the Session 58 hard-stop firing cost both authoring-time (Strategic-thread directive authoring) and execution-time (Path A retreat re-scoping) effort that authoring-time reconciliation could have prevented at near-zero cost.

---

## §4 Operational Protocol

**At directive Part 5 specification authoring time, run the following reconciliation:**

1. Sum per-item upper word/line bounds across all Part 5 items.
2. Compare to cumulative budget ceiling per Part 6 Mode 1 cap structure (or to decision-bound budget per Decision 22 or similar).
3. **If sum exceeds ceiling:** before issuing directive, either —
   - tighten per-item upper bounds (e.g., revise from 250 words to 150 words per item),
   - adjust recommended consumption path (e.g., revise from "Path B at +0.45pp" to "Path B at +0.30pp"),
   - reduce item count (e.g., merge two Outcome A items, defer one to subsequent session),
   - or any combination of these.
4. **If sum is within ceiling:** verify margin is at least 10% headroom (recommend ~20% headroom for execution-time variation); if margin is below ~5%, treat as if exceeding ceiling.

**Documentation requirement:** the reconciliation computation should be recorded in the directive itself (typically at Part 0 Strategic Context or Part 5 cap-structure-summary table). This ensures execution-time review can verify the discipline was applied.

**Verification at directive review:** strategic-thread directive author + PI should be able to point to the reconciliation computation; if not present, surface as Mode 8 (HS-PROJECT-KNOWLEDGE-CONTRADICTION) candidate.

---

## §5 Prospective Application Guidance

**Invoke discipline when:**

- Directive Part 5 specification has more than 3 enumerated items with individual word/line bounds.
- Cumulative budget ceiling is binding (Decision 22 page budget, Mode 1 cap, similar decision-bound constraint).
- Per-item upper bounds are likely to vary substantively from midpoint estimates (heterogeneous content; estimation imprecision per `authoring_layer_estimation_imprecision_canonical.md`).

**Skip discipline only when:**

- Directive is small-scale (1–3 items) with low total magnitude.
- Cumulative budget is non-binding (no decision-bound constraint).
- Per-item bounds are tight and homogeneous (low estimation-imprecision variance).

**Decision rule:** when in doubt, invoke. The reconciliation cost is ~minutes per directive; the failure cost is ~hours per Path A retreat.

---

## §6 Integration with Existing Framework

**Family-level umbrella:** `directive_author_completeness_disciplines_family_canonical.md`.

**Sibling sub-patterns within family:**
- `page_budget_actual_compile_grounding_canonical.md` (sub-pattern 2; related to budget-ceiling realism).
- `workflow_handoff_completeness_canonical.md` (sub-pattern 4; different completeness dimension).

**Related canonical artifacts (different families):**
- `authoring_layer_estimation_imprecision_canonical.md` — related estimation-imprecision pattern; cumulative-budget-reconciliation discipline COMPLEMENTS estimation-imprecision discipline (one operates on per-item estimates; the other operates on cumulative aggregation).

**PADS integration deferred:** PADS could absorb the reconciliation check at Decision 22 page-budget section; integration deferred per `post_phase_7_integration_notes.md`.

**v2.1 directive template integration deferred:** candidate Mode 12 addition (cumulative-budget-overcommitment); candidate Part 5 specification requirement; integration deferred. Phase 8 Session 61 directive authoring may be the first directive to absorb the discipline procedurally.

**Cross-reference:** Phase 7 Session 58 closure report at commit (internal commit) documents the Path A retreat execution; Session 60 closure report §7 documents the hard-stop firing's role in Branch C measurement task scoping.

---

## §7 Carrying-Forward Observations

**Refinement candidates for future cycles:**

- *Automated cumulative-budget-reconciliation pre-issue tool:* a pre-issue lint that sums per-item word bounds in Part 5 and reports against Part 6 Mode 1 cap structure or Decision-22-bound budget. Manual discipline at authoring time is current state; automation is future framework engineering.
- *Sub-pattern-2 graduation candidate "per-item-estimate calibration to historical execution":* when per-item estimates systematically overrun or underrun, calibrate via post-session retrospective. ONE-INSTANCE observation at Session 58 (under-estimation) + Session 60 closure report estimate (in-line). Defer pattern-typing until additional instances accumulate.
- *Mode 1 cap structure refinement candidate:* current Trigger A (25% proportional threshold) was authored at v1.0 template; Phase 7 empirical experience suggests 15% may be more appropriate for high-stakes directives. Defer to future template revision cycle.

**Cumulative-budget-reconciliation discipline at scale:** for directives with very large item counts (15+), even bottom-up reconciliation at upper bounds may under-estimate execution-time variance. Consider stochastic-bound modeling at future framework cycle.

**Empirical base extension:** ONE empirical instance at graduation. Subsequent applications (e.g., Phase 8 Session 61 directive) will accumulate the empirical base. The pattern was clearly identifiable from one instance because the hard-stop firing magnitude (~2.5×) was unambiguous; future instances will refine the threshold sensitivity.

---

**Canonization status:** SEALED at post-Phase-7-close housekeeping cycle Unit 3 atomic commit. Sub-pattern within directive-author-completeness-disciplines family-level meta-pattern.
