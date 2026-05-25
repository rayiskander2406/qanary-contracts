# arXiv v1 Submission Package

This directory contains the arXiv v1 submission package authored at Phase 8
Session 61 Unit 2. Session 62 executes the actual arXiv submission against
this package.

## Contents

| File | Purpose |
|---|---|
| `qanary_contracts_arxiv_v1.tex` | LaTeX wrapper (IEEEtran-compsoc `[10pt,journal,compsoc]`); the primary submission file. |
| `_abstract.md` / `_abstract.tex` | Abstract source (markdown extracted from manuscript) + pandoc-emitted LaTeX. |
| `_body.md` / `_body.tex` / `_body_fixed.tex` | Body source (markdown extracted) + pandoc-emitted LaTeX + longtable-transformed LaTeX. |
| `_fix_longtable.pl` | Transform script that converts pandoc-emitted `longtable` environments to `table*` + `tabular` (longtable is incompatible with IEEEtran two-column). Also hoists any `\caption{}` above the `tabular` and drops the duplicated header pandoc emits for captioned tables. |
| `qanary_contracts_arxiv_v1.pdf` | Compiled PDF (16 pages total; body ~12.85pp + appendix ~3pp + references ~1pp). |
| `qanary_contracts_arxiv_v1.log` | Tectonic compile log (retained for diagnostics). |
| `supplementary_material.md` | Lean source repository pointer + reproducibility tags + CI status + reviewer reproduction path. |
| `arxiv_metadata_draft.md` | Submission-portal metadata draft (title, authors, affiliations, abstract, comments, subject classifications, MSC/ACM, open operational items). |

## Reproduction

From a fresh clone, regenerate this package against the manuscript at
`paper/qanary_contracts_manuscript.md`:

```
cd paper/arxiv_v1_package
sed -n '12,18p' ../qanary_contracts_manuscript.md > _abstract.md
sed -n '22,$p' ../qanary_contracts_manuscript.md > _body.md
pandoc _abstract.md -f markdown -t latex -o _abstract.tex
pandoc _body.md -f markdown -t latex --shift-heading-level-by=-1 -o _body.tex
perl _fix_longtable.pl < _body.tex > _body_fixed.tex
tectonic -X compile qanary_contracts_arxiv_v1.tex --keep-logs
pdfinfo qanary_contracts_arxiv_v1.pdf | grep Pages
```

Line ranges valid at HEAD (internal commit); re-derive if the manuscript
front-matter / abstract / §1 boundaries move.

## Pre-submission readiness verification (Phase 2.4)

| Criterion | Status |
|---|---|
| LaTeX source compiles cleanly | PASS (tectonic; warnings only — see below) |
| PDF generated at submission grade | PASS (16 pages; `qanary_contracts_arxiv_v1.pdf`) |
| Author block populated correctly | PASS (`Ray Iskander` + `` + Verdict Security + via `\IEEEauthorrefmark` per IEEEtran-compsoc convention; not placeholder) |
| Repository pointer accessible | PENDING (`https://github.com/rayiskander2406/qanary-contracts`; verify public visibility at Session 62 pre-submission) |
| Supplementary material organized | PASS (`supplementary_material.md`) |
| arXiv metadata draft complete | PASS (`arxiv_metadata_draft.md`) |
| ORCID readiness | PENDING (Ray to enter at submission portal; ORCID registration verified at Session 62 pre-submission) |
| GenAI disclosure compliance | PASS (§4.5 wording verified compliant at Phase 1.1; names Claude, Grok, Gemini; describes roles; confirms author inspection + Lean 4 kernel verification + CI reproducibility) |
| Body page count Decision 22 compliant | PASS (~12.85pp body; under 13.0pp ceiling per Phase 1.4 actual IEEEtran-compsoc compile measurement) |

## Compile warnings

Tectonic emitted the following non-fatal warnings (acceptable for arXiv
submission; arXiv recompiles from source and emits its own typography
report):

- Two underfull/overfull `hbox` warnings on long `verbatim` lines in
  §10.3.3 reproduction commands — cosmetic, not content-affecting.
- Underfull `vbox` warning during page-break adjustment — IEEEtran-compsoc
  two-column behavior at table breaks; cosmetic.

The PDF renders correctly; these warnings are typical of LaTeX submission
artifacts and do not affect reviewer comprehension.

## Phase 8 trajectory carrying-forward

- **Session 62:** pre-submission verification (repository visibility,
  ORCID values, author endorsement) + arXiv submission portal upload +
  tag (`v1.8-arxiv-v1-submitted` sequential vs `v2.0-arxiv-v1` major
  version bump — decision deferred to Session 62 opening directive).
- **Inter-Session 62 → 63:** community feedback period ~4–8 weeks.
- **Session 63 (TBD):** arXiv v2 incorporating community feedback.
- **Session 64 (TBD):** venue submission packaging including anonymization
  six-vector execution against separate submission branch (per Session 60
  SP5 closure report §7.1 enumeration; deferred per §7.6 binding
  trajectory).
- **Session 65 (TBD):** IEEE Symposium on Security and Privacy 2027 venue
  submission (cycle 2 deadline November 17, 2026).
