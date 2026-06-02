# QANARY Contracts arXiv v2 — Submission Record

- **arXiv ID:** 2606.01794v2
- **Public URL:** https://arxiv.org/abs/2606.01794v2
- **Temporary submission id:** submit/7669000
- **Submitted:** 2026-06-02
- **arXiv announcement:** scheduled Wed, 3 Jun 2026 00:00:00 GMT
- **Version:** v2 (Zenodo reproducibility-chain finalization)
- **Parent version:** v1 (arXiv:2606.01794v1, announced 2026-06-01)
- **Categories:** cs.CR primary, cs.LO + cs.PL cross-list
- **License:** arXiv perpetual non-exclusive
- **Author:** Ray Iskander (Verdict Security) — sole author
- **Repository tag:** v2.1-arxiv-v2 (git reproducibility anchor; no GitHub release)
- **Zenodo concept DOI:** 10.5281/zenodo.20510920
- **Zenodo version DOI (v1 snapshot, tag v2.0-arxiv-v1):** 10.5281/zenodo.20510921

## Zenodo versioning decision

qanary-contracts keeps a **single Zenodo version** (the v1 snapshot, `10.5281/zenodo.20510921`),
matching the seven QANARY PQC papers, which each minted one Zenodo version. No
second deposit is created for the v2 tag: the **concept DOI** `10.5281/zenodo.20510920`
already resolves to the archived artifact, and the manuscript cites the concept
DOI. The `v2.1-arxiv-v2` tag is therefore a git reproducibility anchor with no
attached GitHub release.

## Content delta from v1

- **Appendix A.3 (Reproduction commands):** appended one sentence citing the
  Zenodo concept DOI `10.5281/zenodo.20510920` for the permanent archival
  snapshot. Plain `\texttt{}` rendering (manuscript uses no hyperref), mirroring
  the structural-dependency-analysis v2 "Code and Data Availability" pattern.
- No abstract change (minimal scope; the v2 Comments field notes the addition).

## Repository housekeeping landed in the v2 commit

- Added `.zenodo.json` (sole-author) — canonical deposit metadata (used by Zenodo
  auto-fill on any future release).
- Added `CITATION.cff` (sole-author) — concept + v1-snapshot version DOIs.
- De-staled `README.md` — paper is live; added arXiv + Zenodo DOI badges,
  updated the Citation section, added the arXiv anchor tags to the Tags table.

## What's invariant from v1

- All thirteen theorems, proof structure, and axiom records.
- Lean source corpus untouched (build 901 jobs green; `#print axioms` records
  bounded by `[propext]`; no commits to `QanaryContracts/`, `lakefile.lean`, or
  the proof files).
- All cascade references (v1.3-layer6, v1.6-phase7, v1.7-methodology-housekeeping).
- Manuscript text outside the Appendix A.3 sentence.

## Audit (v2 preview PDF vs. v1 baseline)

- Sole-author scans (khaled / kirah / ain shams / asu.edu / corresponding author): 0.
- Zenodo concept DOI `20510920` present (Appendix A.3, p.14).
- Cascade counts identical to v1 (v1.6-phase7=3, v1.3-layer6=4, appendix a=19, sorry=7).
- Affiliation preserved (verdict security; ray@verdictsecurity).
- 16 pages (unchanged); visual eye-check of the Appendix A.3 page clean.
- Compiled with tectonic (the documented local build engine); authoritative
  pdfLaTeX/TeX Live compile confirmed at the arXiv replacement form (no
  moderation hold).
