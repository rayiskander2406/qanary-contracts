# `methodology/` — methodology-framework canonical artifacts

This directory holds the canonical artifacts for the **methodology framework**
underpinning QANARY Contracts. Per the boundary discipline of the paper, the
framework is **presented in full in a companion methodology paper** (separate
arXiv track); these files are the pointer-table targets referenced from the
manuscript's Appendix B, sealed at tag `v1.7-methodology-housekeeping`.

They use the framework's internal pattern labels (e.g. wrapper-layer absorption,
compose-from-outside discipline). The brief operational presentations in the main
paper's §4 are sufficient for its substantive smart-contract-verification claims;
this directory is for readers who encounter those labels and want the canonical
write-ups.

## Artifacts

| File | Pattern / topic | Cited in main paper |
|---|---|---|
| `M-22.2_Tier1_canonical.md` | Wrapper-layer absorption (axiom-record-minimal composition; §4.3) | yes (Appendix B) |
| `multi_lens_net_property_canonical.md` | Multi-lens-net property (different review lenses catch disjoint issues) | referenced |
| `authoring_layer_estimation_imprecision_canonical.md` | Family-level authoring-layer estimation-imprecision meta-pattern | yes (Appendix B) |
| `workflow_handoff_completeness_canonical.md` | Workflow-handoff completeness | — |
| `cumulative_budget_reconciliation_canonical.md` | Cumulative-budget reconciliation | — |
| `downgrade_rescue_differential_budget_canonical.md` | Downgrade-rescue differential budget | — |
| `page_budget_actual_compile_grounding_canonical.md` | Page-budget actual-compile grounding (cites the `paper/ieeetran-measurement/` scaffold) | — |
| `directive_author_completeness_disciplines_family_canonical.md` | Directive-author completeness disciplines family | — |
| `post_phase_7_integration_notes.md` | Integration notes tying the artifacts together | — |

The compose-from-outside / no-retrofit discipline (§4.2) is documented directly in
the Lean source — see `QanaryContracts/CrossProtocolAudit.lean`.

## Note on cross-references

These artifacts were authored as part of the project's internal development record
and contain a few references to internal process documents (the project's PADS,
the directive template, and per-session reports) that are **not part of this public
release**. Those documents' substance is covered in the companion methodology
paper; the cross-references are retained verbatim to preserve the canonical text.
