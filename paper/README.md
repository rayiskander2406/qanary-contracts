# `paper/` — manuscript and submission artifacts

| Item | Purpose |
|---|---|
| `qanary_contracts_manuscript.md` | Manuscript source (markdown). The arXiv-hosted PDF is the manuscript of record. |
| `arxiv_v1_package/` | arXiv v1 submission package: LaTeX wrapper + pandoc-emitted body/abstract + compiled PDF + supplementary material + submission metadata. See its own `README.md` for the regeneration pipeline. |
| `ieeetran-measurement/` | IEEEtran-compsoc page-budget measurement scaffold (tectonic + a longtable→tabular transform). Reusable across IEEEtran-bound documents; referenced from `methodology/page_budget_actual_compile_grounding_canonical.md`. See its own `README.md`. |

## Reproducing the arXiv PDF

See `arxiv_v1_package/README.md`. In brief: the package extracts the abstract and
body from `qanary_contracts_manuscript.md`, converts to LaTeX via pandoc, applies a
longtable→`table*` transform for two-column compatibility, and compiles with
tectonic against the IEEEtran-compsoc class.

## Verification artifacts

The substantive verifiable claims live in the Lean source (`../QanaryContracts/`)
and are reproduced per the root `README.md`. The PDF and source here let a reviewer
rebuild the manuscript itself; the theorem corpus is verified independently via
`lake build` + `lake env lean QanaryContracts/PrintAxioms.lean`.
