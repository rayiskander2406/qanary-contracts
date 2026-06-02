# Session 62 — arXiv Submission Record

Permanent record of the arXiv v1 submission of the QANARY Contracts paper,
*Tridirectional Discriminating-Power Formal Verification of Smart Contract
Reentrancy Defense Against Production-Deployed Solidity Source*.

## Submission identity

| Field | Value |
|-------|-------|
| arXiv ID | **2606.01794** |
| Public URL | http://arxiv.org/abs/2606.01794 |
| Version | v1 |
| Submission timestamp | Mon, 1 Jun 2026 07:13:39 GMT (submitted 03:13:39 EST; announced 07:13:39 GMT) |
| Original submission ticket | submit/7659183 |
| License | arXiv perpetual non-exclusive license to distribute |

## Author

Ray Iskander (Verdict Security, Independent Formal Verification Firm) — **sole author**.

## Classification

- **arXiv categories:** `cs.CR` (primary) + `cs.LO`, `cs.PL` (cross-list) — all three accepted in one submission.
- **ACM CCS (2012):** `D.2.4` (Software Engineering / Software/Program Verification), `F.3.1` (Logics and Meanings of Programs / Specifying and Verifying and Reasoning about Programs), `K.6.5` (Security and Protection).
- **MSC (2020):** `68N30` (primary — mathematical aspects of software engineering), `68Q60` (secondary — specification and verification), `94A60` (tertiary — cryptography).

## Repository state at submission

- **Repository:** https://github.com/rayiskander2406/qanary-contracts
- **Tag at submission:** `v2.0-arxiv-v1`
- **Reproducibility anchors:**
  - `v1.3-layer6-closure` — substantive proof substrate (independently reproducible).
  - `v1.6-phase7-closure` — post-audit content seal (manuscript baseline).
  - `v1.7-methodology-housekeeping`.
  - `v2.0-arxiv-v1` — this tag (the arXiv v1 source state).

## Build & artifact verification

- **Lean build:** `lake build` green @ 901 jobs.
- **Axiom record:** `#print axioms` output, sha256 `d0af10843e5afd4c76a08cb073a385dedef2aa4e3c65a02365d329c672c311aa` (123-line record). Baseline maintained bit-identical since Session 61.8; no Lean source modified this session (M-26.1 scoped exception holds).
- **Submitted source bundle:** `arxiv_source_bundle_upload.tar.gz`, sha256 `7bf073ec9698b59ed0a1c7e91ed6fc8bc71155b62811cc86b0307dde171c1248` (durable on `~/Desktop/LaTeX/`). Contents: `qanary_contracts_arxiv_v1.tex`, `_abstract.tex`, `_body_fixed.tex`.
- **Wrapper-source byte-identity:** the repo wrapper `paper/arxiv_v1_package/qanary_contracts_arxiv_v1.tex` was folded to byte-identity with the submitted bundle at commit `d88b570`; sha256 `1058e94534d6a9c56ec467ed3a9af2f6063fad7e45038d7c54f52e9d65cabb25`. (`_abstract.tex` / `_body_fixed.tex` already matched the bundle.)
- **Locally-compiled pdfLaTeX preview PDF:** sha256 `334a6b42ff6f86332b4e38930dd4f42abda2d904b68ba08144b12a9e4c6688e2` — visually equivalent to arXiv's compile (arXiv compiles from source via pdfLaTeX).
- **Tectonic-compiled PDF** (`paper/arxiv_v1_package/qanary_contracts_arxiv_v1.pdf`): sha256 `42380c7e6d79253c40f9e721d8b756f02457a47c68282aada6cd4baf2e3b2f63`.

## Notes

- arXiv compiles the submission from source with pdfLaTeX. The wrapper compatibility fixes — `fvextra` verbatim `breaklines` (auto-wrapping the long Appendix A.3 reproduction commands at `breakafter=/` so `rayiskander2406` survives the URL break) and the explicit `\newunicodechar{¬}` U+00AC mapping — were applied to the submitted source and folded into the repo at `d88b570` so `paper/arxiv_v1_package/` matches the submitted bundle exactly. The defect was latent under tectonic's narrower Latin Modern fallback and only surfaced under pdfLaTeX's true Courier.
- An arXiv v2 incorporating reviewer feedback is planned before the IEEE S&P 2027 venue submission (deadline 2026-11-17).
