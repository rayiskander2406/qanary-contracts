# Authoring-Layer Estimation Imprecision When Measurement Is Determined Externally — Canonical Specification

**Graduation provenance:** ratified at Phase 5 Session 44 post-Layer-6 housekeeping cycle per Decision A (Unit 2 graduation enactment adjudication directive v1.0); tagged at `v1.4-methodology-housekeeping`. Graduation review at Phase 5 Session 44 Unit 1 Graduation Review Document commit (internal commit) §16.
**Methodology framework status:** canonical methodology framework artifact; paper §10 Section 10.4 central methodology finding.
**Authored:** 2026-05-11.

---

## §1 Pattern Statement

**Authoring-layer estimation imprecision when measurement is determined externally:** authoring-time line-count or threshold estimates fail when the actual measurement at execution-time is determined by external requirements rather than by the author's discretionary choice.

External-determination mechanisms include:
- Transcription source content (user message content rendered into a directive template artifact).
- Codebase convention adherence (file-header `/-` block sized by codebase pattern, not by directive estimate).
- Paper §10 anchor requirement (citation traceability drives content size).
- Framework enumeration completeness (every empirical instance must be documented; itemization length determined by instance count).
- Cumulative-measurement-vs-snapshot precision gap (commit-message annotation at mid-execution snapshot vs post-hoc cumulative measurement).
- Small-scope content-load-bearing drivers (small fragment scopes with content-load-bearing requirements manifest the pattern at HIGHER relative magnitude due to small-scope-feels-small bias).

The pattern operates **bidirectionally**: estimation imprecision can manifest as both overrun (insufficient estimate vs content-load-bearing reality) and underrun (over-correction after recent overrun adjudication, or content-load-bearing-content authoring less than estimated). Two-instance bidirectional verification at Session 44 close establishes directional repeatability.

---

## §2 Six Empirical Instance Enumeration

Six instances across three structurally distinct authoring layers spanning Sessions 41-44:

| Instance | Session       | Layer                            | Magnitude    | Direction | Mechanism                                                                                  |
|---------:|---------------|----------------------------------|-------------:|-----------|--------------------------------------------------------------------------------------------|
| 1        | S41 retro     | directive-authoring              | +21%         | overrun   | Transcription artifacts; ±5 binary tolerance too tight; provenance-verification recovery   |
| 2        | S42 U1        | substantive-content              | +30%         | overrun   | Content-load-bearing-content authoring (CrossProtocolAudit.lean module docstring + file-header); itemization completeness drives size |
| 3        | S42 post-hoc  | commit-message                   | misannotation severity | overrun (severity)  | Mid-execution-snapshot vs post-hoc cumulative measurement precision gap          |
| 4        | S43 Step 1    | directive-authoring (recurrence) | +78%         | overrun   | Selective-correction-application; small-scope-feels-small bias; internal housekeeping log entry     |
| 5        | S43 Step 2    | substantive-content (bidirectional) | -39%      | underrun  | Post-correction-overcorrection; closure report 427 vs ~700 midpoint                        |
| 6        | **S44 U1**    | substantive-content (bidirectional) | **-25% vs midpoint / -35% vs upper bound** | **underrun** | **Post-correction-overcorrection second observation; Graduation Review Document 523 vs ~700 midpoint estimate / ~800 upper bound; -35% vs upper bound is above 30% threshold from S44 opening directive watchpoint specification.** |

**Bidirectional manifestation two-instance verified:** instances 5 and 6 both lands as substantive underrun vs midpoint estimate. Directional behavior is repeatable, not anomalous.

---

## §3 Three Authoring Layer Enumeration

The family-level meta-pattern operates at three structurally distinct authoring layers:

### §3.1 Directive-Authoring Layer

Empirical evidence: instances 1, 4.

Operating mechanism: directive-author line-count estimates fail when content drivers are spec'd by directive Action items at itemization detail — actual line count is determined by drivers' itemization completeness rather than by directive-author estimate. Mechanism subsumes:

- **Transcription artifacts** (instance 1): directive author estimates based on user message content without rendering visibility. ±5 binary tolerance too tight; provenance-verification + ±20% tolerance + accept-actual-on-verified-transcription is the canonical recovery path.

- **Selective-correction-application across structurally-identical boundaries** (instance 4): directive author applies a previously-learned correction to one boundary but not to an adjacent structurally-identical boundary at the same authoring time. Operating mechanism: **small-scope-feels-small bias** — small-fragment scopes with content-load-bearing drivers manifest the pattern at HIGHER relative magnitude. Empirical data: instance 4 at +78% vs instance 2 at +30% (larger relative magnitude at smaller scope). This is the *directive-author-correction-discipline-incompleteness* meta-observation subsumed under the family-level pattern.

### §3.2 Substantive-Content Authoring Layer

Empirical evidence: instances 2, 5, 6.

Operating mechanism: line-count estimates fail when content is determined by external requirements — codebase convention adherence (file-header `/-` block; AaveBoundaryCase.lean / DAOContract.lean / CompoundContract.lean precedent), paper §10 anchor requirement (citation traceability), or framework enumeration completeness (every empirical instance documented in M-22.2 five-instance enumeration, etc.).

Bidirectional manifestation operates at this layer (instances 5 and 6 vs instance 2). Mechanism for underrun manifestation: **post-correction-overcorrection** — directive author applies directive-content-spec-estimation-precision self-correction at directive-authoring time (estimating higher than prior empirical baseline to absorb anticipated overrun), but the self-correction itself overshoots the empirically appropriate target. Two-instance verification at S43 + S44 establishes directional repeatability.

### §3.3 Commit-Message Authoring Layer

Empirical evidence: instance 3.

Operating mechanism: threshold estimates fail when actual measurement is post-hoc cumulative rather than mid-execution snapshot. Specifically: Mode 2 (HS-SESSION-CAP-SOFT) firing classification annotated at commit-message-authoring time uses mid-execution snapshot of cumulative cap utilization; post-hoc cumulative measurement (after commit lands) may reclassify firing tier (marginal <2% vs substantive >2%). Canonical recovery path: verify session-soft firing classification via cumulative measurement at session close before commit-message annotation.

---

## §4 Bidirectional Manifestation Two-Instance Verification (Decision F Documentation)

Instances 5 (S43 Step 2 -39% vs midpoint) and 6 (S44 Unit 1 -25% vs midpoint / -35% vs upper bound) establish bidirectional manifestation as repeatable pattern.

**Instance 5 — S43 Closure Report:** the internal Layer-6D closure report authored at 427 lines vs ~600-800 directive estimate (midpoint 700). Magnitude -39% vs midpoint. Operating mechanism: directive author applied directive-content-spec-estimation-precision self-correction at Session 43 opening directive authoring time (estimated ~600-800 for closure report explicitly noting prior S41 296-line baseline), but the self-correction overshot the empirically appropriate target.

**Instance 6 — S44 Unit 1 Graduation Review Document:** the internal graduation-review document authored at 523 lines vs ~600-800 directive estimate (midpoint 700; upper bound 800). Magnitude -25% vs midpoint; -35% vs upper bound. The -35% vs upper bound IS above the 30% threshold specified in Session 44 opening directive Part 5 Unit 1 bidirectional manifestation watchpoint:

> If Unit 1 actual lands substantially under estimate (~30%+ underrun), document as bidirectional manifestation second empirical instance; do not adjust expectations during execution.

Ray ratified the classification as bidirectional manifestation second empirical instance per Decision F (Unit 2 graduation enactment adjudication directive v1.0).

**Directional behavior repeatable:** two underrun observations spanning Sessions 43 + 44 at substantive-content authoring layer (closure report + graduation review document) both lands at -25% to -39% vs midpoint estimate. Bidirectional manifestation is not anomalous; it is the expected behavior when directive-content-spec-estimation-precision self-correction is applied at directive authoring time.

**Cap firing classification documented (Action 2.6):** S44 Unit 1 underrun classified as bidirectional manifestation second empirical instance per Decision F. Magnitude transparency: -25% vs midpoint; -35% vs upper bound (above watchpoint threshold). Directional repeatability: two underrun observations (S43 -39% + S44 -25%).

---

## §5 Sub-Pattern Subsumption Mapping

Five queue items retire as subsumed under the graduated family-level meta-pattern; one queue item held-under-graduated as sub-aspect:

| Queue item | Sub-pattern name                                                          | Disposition                                                       | Evidence preserved in instance |
|------------|---------------------------------------------------------------------------|-------------------------------------------------------------------|--------------------------------|
| §3         | Directive-author-estimation-precision (directive-authoring layer)         | Retired-as-subsumed                                               | Instance 1                     |
| §4         | Directive-content-spec-estimation-precision (substantive-content layer)   | Retired-as-subsumed                                               | Instance 2                     |
| §5         | Commit-message-authoring-precision (commit-message layer)                 | Retired-as-subsumed                                               | Instance 3                     |
| §6         | Directive-author-correction-discipline-incompleteness (meta-layer)        | Retired-as-subsumed                                               | Instance 4 (small-scope-feels-small bias mechanism documented at §3.1) |
| §7         | Directive-author-estimation-precision bidirectional manifestation         | Retired-as-subsumed                                               | Instances 5+6                  |
| §15        | Within-session saturation intra-session sub-trajectory sensitivity        | **Held-under-graduated-§16** as sub-aspect of pattern recurrence  | Pattern recurrence dimension not yet operationalized; paper §10 future-extension hook preserved |

Per Decision E: §15 held-under-graduated rather than retired outright. Preserves paper §10 future-extension hook for empirical investigation of intra-session sub-trajectory effects under graduated meta-pattern artifact.

---

## §6 Operational Guidance for Future Directive Authoring

Five principles derived from six-instance evidence base:

1. **Avoid small-scope-feels-small bias.** Small-fragment scopes (~30-60 line estimates) with content-load-bearing drivers manifest the pattern at HIGHER relative magnitude (S43 Step 1 +78% vs S42 U1 +30% at larger scope). Do not implicitly assume small scopes are exempt from the sub-pattern.

2. **Apply directive-content-spec-estimation-precision symmetrically.** Corrections applied at one directive boundary do not eliminate the underlying pattern at adjacent structurally-identical boundaries when small-scope-feels-small bias operates. Pre-authorize accept-actual at moderate tier (5-15%) for all step boundaries within a directive, not selectively.

3. **Expect bidirectional manifestation.** Line-count estimates can fail in either direction when content is externally determined. Post-correction overcorrection produces underrun. Two-instance bidirectional verification at S43+S44 establishes repeatable pattern. Cap structures should accommodate both directions.

4. **Use empirical baselines without over-correcting.** When sizing directive estimates, anchor on prior-session empirical baselines (Session 41 closure report 296 lines; Session 43 closure report 427 lines; etc.). Do not over-correct based on single-instance overrun evidence; expect underrun manifestation as the symmetric failure mode.

5. **When in doubt: target midpoint of estimate; pre-authorize accept-actual at moderate tier (5-15%); halt + classify at structural-scope-surprise tier (>15%) regardless of direction.** Mode 1 graded recovery applies symmetrically to overrun and underrun firings at structural-scope-surprise tier.

### §6.1 Cap Structure Sizing Guidance

For multi-section content-load-bearing-content authoring:
- Estimate range based on prior-session empirical baselines, not absolute targets.
- Target midpoint of estimate range, not upper or lower bound.
- Soft cap at upper bound of estimate range with explicit "lower-end-discount NOT applied per bidirectional manifestation observation" framing.
- Pre-authorize Mode 1 accept-actual at moderate tier (5-15%) bidirectionally.
- Halt + classify at structural-scope-surprise tier (>15%) bidirectionally.

### §6.2 Commit-Message-Authoring Discipline

For Mode 2 (HS-SESSION-CAP-SOFT) firing annotations in commit messages:
- Do NOT annotate firing classification at mid-execution snapshot.
- Verify firing tier via post-hoc cumulative measurement at session close before commit-message authoring.
- Document classification gap explicitly if mid-execution estimate diverges from post-hoc measurement.

---

## §7 Paper §10 Section 10.4 Anchor Traceability

The family-level meta-pattern is paper §10 Section 10.4 (methodology section) central methodology finding. Section 10.4 cites this canonized reference for:

- **Multi-layer-recurrence evidence:** family-level pattern operates across three structurally distinct authoring layers (directive-authoring + substantive-content + commit-message). Layer-recurrence supports portability claim.

- **Bidirectional-manifestation evidence:** two-instance verification (instances 5+6) establishes directional repeatability. Operating mechanism (post-correction-overcorrection) documented.

- **Six-instance evidence base across twelve substantive sessions:** S41-S44 instances accumulated through Layer 6 substantive substrate authoring trajectory. Empirical evidence base is paper §10 raw material at directive-authoring-discipline empirical-validation layer.

- **Meta-layer observation (instance 4):** directive-author-correction-discipline-incompleteness operates at meta-layer above base-layer estimation precision. The framework's portability claim is not "the framework prevents the pattern from recurring" but "the framework makes the pattern's recurrence catchable, attributable, and adjudicable cleanly."

Paper §10 Section 10.4 framing: methodology framework's empirical-validation evidence base accumulated across Phase 5 Sessions 28-43 + crystallized at Session 44 Unit 2 graduation enactments becomes manuscript raw material at §10 boundary. The *paper writes itself* framing applies.

---

## §8 Operational Sub-Aspect (Held-Under-Graduated): Within-Session Saturation

Per Decision E §15 disposition: within-session saturation intra-session sub-trajectory sensitivity (Sessions 38/40 reference) held-under-graduated-§16 as sub-aspect of pattern recurrence rather than retired outright.

The sub-aspect's hook: pattern recurrence may exhibit intra-session sub-trajectory saturation effects — multiple HS-CUMULATIVE-CAP firings within a single session may interact with each other (e.g., a second firing within the same session may be more easily reclassified as substantive due to prior-firing-in-session prior). Operational definition deferred to future empirical investigation.

If a future session surfaces specific intra-session sub-trajectory pattern, document the empirical evidence within this canonical artifact's operational sub-aspect section rather than re-opening §15 as a separate queue item.

---

## §9 Refinement Queue Status Post-Graduation

Pre-graduation queue (Session 44 opening): 15 queue items + 2 cross-cutting candidacies = 17 entries.

Post-graduation queue (Session 44 close, this artifact's canonization point):

| Status                                  | Items                                                 | Count |
|-----------------------------------------|-------------------------------------------------------|------:|
| Graduated                               | §1 (Mode 10 → v2.1), §10 (Option β → v2.1 Mode 4), §16 (family-level → this artifact), §17 (M-22.2 Tier 1 → companion artifact) | 4 |
| Retired-as-subsumed under §16          | §3, §4, §5, §6, §7                                     | 5 |
| Weak-retired                            | §13 (Form A null-action), §14 (session-close-vs-session-open boundary) | 2 |
| Held-under-graduated-§16                | §15 (within-session saturation as sub-aspect)         | 1 |
| Held-at-candidacy                       | §2, §8, §9, §11, §12                                   | 5 |
| **Total accounted for**                 |                                                       | **17** |

Post-graduation queue (held-at-candidacy + held-under-graduated continuing operational monitoring): **6 items**. Down from 17 entries pre-graduation = 65% reduction.

---

## §10 Cross-References

- **Graduation Review Document §16 entry:** the internal graduation-review document at commit (internal commit).
- **Unit 2 graduation enactment adjudication directive v1.0** (six Ray-ratified decisions A-F).
- **Companion canonical artifact:** `methodology/M-22.2_Tier1_canonical.md` (M-22.2 Tier 1 wrapper-layer absorption pattern; substantive theorem-layer methodology framework artifact).
- **v2.1 directive template** (in-place upgrade of the internal v2.1 directive template; Mode 10 + Option β graduations incorporated).
- **Empirical-validation layer evidence trajectory:** Sessions 41-44 (S41 retrospective GOTCHA #2 + S42 Unit 1 Mode 1 adjudication + S42 post-hoc commit-message-authoring-precision finding + S43 Step 1 Mode 1 adjudication + S43 Step 2 underrun observation + S44 Unit 1 underrun classification).
- **Cumulative cap-amendment trajectory:** twenty-three HS-CUMULATIVE-CAP firings + two session-soft firings across Phase 5 Sessions 28-43; bidirectional manifestation verified at S43+S44.

---

**Canonization status:** SEALED at Session 44 Unit 2 graduation enactment commit per Decision A. Paper §10 Section 10.4 central methodology finding finalized.
