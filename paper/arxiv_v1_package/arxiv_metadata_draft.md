# arXiv v1 Submission Metadata Draft

Draft of the arXiv submission portal metadata fields for the Phase 8 Session 62
arXiv v1 submission execution. Treat this document as the canonical reference
for the metadata to enter into arxiv.org's submission form; revise inline at
Session 62 if any field needs final adjustment after Ray review.

## §1 Core bibliographic fields

| arXiv field | Content |
|---|---|
| **Title** | Tridirectional Discriminating-Power Formal Verification of Smart Contract Reentrancy Defense Against Production-Deployed Solidity Source |
| **Authors** | Ray Iskander |
| **Affiliations** (entered per-author) | Ray Iskander — Verdict Security, Independent Formal Verification Firm. |
| **ORCID identifiers** (entered per-author in submission portal; not in manuscript body under non-anonymous arXiv v1 framing) | Ray Iskander — ORCID `[Ray to enter]`. — ORCID `[ to enter]`. |
| **Submission category** | Preprint v1 (community-feedback solicitation; venue-submission preparation underway) |

## §2 Abstract (verbatim from manuscript)

> We present the first machine-checked correctness proof of the OpenZeppelin reentrancy-guard pattern against a Lean 4 state-machine model of production-deployed Solidity source with a composition meta-theorem spanning multiple production protocols. All thirteen theorems are machine-checked in Lean 4 with **zero `sorry`, zero user-introduced axioms, and an axiom footprint bounded by `[propext]` across the entire corpus** — propositional extensionality, a standard classical axiom in Lean 4's mathlib4; per-function inner lemmas are kernel-only, master/wrapper theorems carry `[propext]`-only records, and the Layer 6-D capstone composes exactly the union of the prior-layer records by direct conjunction. The corpus is gated under continuous integration across four parallel verification blocks that re-check each theorem and its axiom record on every push.
>
> Smart contract reentrancy has caused over US$500M in cumulative documented losses since 2016, with the DAO 2016 attack alone draining ≈3.6M ETH and forcing a contentious hard fork that split Ethereum into two persistent chains. The OpenZeppelin `ReentrancyGuard` mutex pattern has emerged as the de facto defense across most production DeFi protocols, yet no prior formal verification effort has established its *discriminating power* — the property that the guard pattern blocks attacks against vulnerable instances, preserves correct execution for non-attacking transactions, and distinguishes structurally-adjacent safe and vulnerable variants. Prior work has formalized either guard correctness on toy contracts or attack feasibility on isolated vulnerable instances, but not both directions plus boundary cases against production-deployed source.
>
> The verification covers three production protocol instantiations — DAO 2016, Compound v2 cToken family, and Aave V3 `flashLoan` — together with one constructed minimal-diff mutant of Aave V3's production `flashLoan` (`flashLoanVulnerable`) authored to isolate a single security-critical structural difference for discriminating-power isolation. We apply mutation-testing methodology to formal verification by constructing this minimal-diff mutant, enabling a controlled experiment that naturally-occurring near-misses rarely provide. The resulting tridirectional structure pairs (a) a negative-instance attack reproduction of the DAO 2016 vulnerable pattern, (b) a positive-instance correctness proof against the Compound v2 cToken family, and (c) a boundary-case proof distinguishing Aave V3's safe-by-design `flashLoan` (CEI-correct) from the `flashLoanVulnerable` mutant. A single capstone meta-theorem composes the three protocol instantiations under a *no-retrofit composition discipline* (each protocol-instantiation proof was sealed prior to capstone authoring, with no underlying-proof modifications during composition), establishing a machine-checked composition meta-theorem demonstrated at the first cross-protocol stress test (Compound v2 → Aave V3, within the lending-family domain; broader-family portability is future work, §9.4).
>
> We release the full Lean 4 source, CI gating configuration, and reproduction commands at `https://github.com/rayiskander2406/qanary-contracts` with reproducibility verified at tagged commit `v1.5-phase6-closure` (the Phase 6 closure seal; the substantive proof substrate is independently reproducible at `v1.3-layer6-closure` per §10.3.3).

## §3 Comments field

> Preprint version 1. Manuscript prepared for IEEE Symposium on Security and Privacy 2027 venue submission cycle 2 (deadline November 17, 2026). 13-page body plus appendix; reproducible Lean 4 artifact at `https://github.com/rayiskander2406/qanary-contracts` (tag `v1.6-phase7-closure` is the post-extreme-audit manuscript-baseline tag; substantive proof substrate independently reproducible at `v1.3-layer6-closure`). Community feedback is solicited; an arXiv v2 incorporating reviewer feedback is planned before venue submission.

## §4 Subject classifications

### Primary

- `cs.CR` — Cryptography and Security

### Secondary

- `cs.LO` — Logic in Computer Science
- `cs.PL` — Programming Languages

### Cross-listing rationale

- `cs.CR` captures the smart-contract-security framing and the DeFi-loss
  context that motivates the work.
- `cs.LO` captures the formal-verification framing (Lean 4 theorem proving,
  axiom-record discipline, machine-checked correctness).
- `cs.PL` captures the programming-language-semantics framing (Solidity
  source-level state-machine model, EVM semantics references, CEI-correct
  execution ordering).

## §5 MSC classification (Mathematics Subject Classification, 2020)

- Primary: `68N30` — Mathematical aspects of software engineering
  (specification, verification, metrics, requirements, etc.)
- Secondary: `68Q60` — Specification and verification (program logics,
  model checking, etc.)
- Tertiary: `94A60` — Cryptography (selected for smart-contract-security
  context)

## §6 ACM classification (CCS 2012)

- `D.2.4` — Software Engineering / Software/Program Verification
- `F.3.1` — Logics and Meanings of Programs / Specifying and Verifying and
  Reasoning about Programs
- `K.6.5` — Management of Computing and Information Systems / Security and
  Protection

## §7 Submission artifacts

The arXiv v1 submission package includes:

- `qanary_contracts_arxiv_v1.tex` — LaTeX source (wrapper around
  `_abstract.tex` + `_body_fixed.tex`).
- `_abstract.tex` — abstract content.
- `_body.tex` — pandoc-emitted body LaTeX.
- `_body_fixed.tex` — body LaTeX with `longtable` → `table+tabular`
  transform applied (longtable is incompatible with IEEEtran two-column).
- `_fix_longtable.pl` — the transform script, retained for reproducibility.
- `_abstract.md`, `_body.md` — markdown intermediate files (informational).
- `qanary_contracts_arxiv_v1.pdf` — compiled PDF, 16 pages total
  (body ~12.85pp + appendix ~3pp + references ~1pp; within Decision 22
  page-budget compliance).
- `supplementary_material.md` — Lean source repository pointer + CI status
  + reproduction commands.
- `arxiv_metadata_draft.md` — this document.

arXiv typically accepts a `.tar.gz` of the LaTeX source tree; the `.tex`
sources and `_fix_longtable.pl` are the primary submission contents. The
compiled PDF is included for reviewer convenience but arXiv recompiles from
source.

## §8 Open operational items for Session 62

| Item | Resolution path |
|---|---|
| Ray ORCID value | Ray to enter at submission portal at Session 62. |
| ORCID value | to confirm + provide at Session 62; if absent, register at https://orcid.org before submission. |
| Repository public visibility | If `https://github.com/rayiskander2406/qanary-contracts` is currently private, make public concurrent with arXiv submission. |
| arXiv author endorsement | First-time arXiv submitters may need endorsement; verify Ray have prior arXiv submissions or established author endorsement. |
| Final manuscript review | Pre-submission read-through by Ray to catch last-minute issues before Session 62 submission execution. |
