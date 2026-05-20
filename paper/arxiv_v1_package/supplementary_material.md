# arXiv v1 Supplementary Material

This document organizes the supplementary artifacts that accompany the arXiv v1
preprint submission of *Tridirectional Discriminating-Power Formal Verification
of Smart Contract Reentrancy Defense Against Production-Deployed Solidity
Source* (Ray Iskander).

## §1 Lean 4 source repository

**Repository URL (non-anonymous; arXiv v1 trajectory per project framing):**
`https://github.com/rayiskander2406/qanary-contracts`

**Reproducibility tags:**

- `v1.3-layer6-closure` — the substantive proof substrate (thirteen
  machine-checked theorems across Layer 6-A/B/C/D); the manuscript's
  reproducibility tag for the proof artifact.
- `v1.4-methodology-housekeeping` — methodology framework canonization
  (canonical artifacts at `/methodology/`); referenced at §10.4.
- `v1.5-phase6-closure` — Phase 6 manuscript closure baseline (referenced
  at the abstract).
- `v1.6-phase7-closure` — Phase 7 extreme-audit pass closure (post-Sessions
  53–60 audit-driven manuscript revisions).
- `v1.7-methodology-housekeeping` — post-Phase-7 methodology framework
  housekeeping cycle (5 graduations → 8 canonical artifacts at
  `/methodology/`).

**Reviewer reproduction path** (verbatim from manuscript §10.3.3):

```
git clone https://github.com/rayiskander2406/qanary-contracts.git
cd qanary-contracts
git checkout v1.3-layer6-closure # substantive substrate
lake build # type-checks the corpus at 901 jobs
lake env lean QanaryContracts/PrintAxioms.lean
                                    # emits per-theorem axiom records
```

Reviewers evaluating the methodology framework should additionally check out
`v1.4-methodology-housekeeping` (or `v1.7-methodology-housekeeping` for the
post-Phase-7-graduated state) per §10.4.

## §2 CI verification status

- **Build status:** `lake build` green at 901 jobs (verified at HEAD
  (internal commit), post-Session-61 Unit 1 commit; the underlying Lean source has
  not changed since `v1.3-layer6-closure` per the M-26.1 compose-from-outside
  discipline of §4.2).
- **CI configuration:** four parallel verification blocks at `build.yml`
  lines 287, 356, 408, 464 (one block each for Layer 6-A / 6-B / 6-C / 6-D).
- **Axiom record:** `[propext]`-only at the capstone; per-function inner
  lemmas kernel-only or `[propext]`-only. Zero `sorry`, zero user-introduced
  `axiom` declarations across the entire corpus.

## §3 Repository structure

The repository is organized at three top-level locations:

- `paper/` — manuscript and architectural artifacts (this directory is the
  arXiv v1 package; the manuscript markdown source is at
  `paper/qanary_contracts_manuscript.md`).
- `QanaryContracts/` — Lean 4 source organized by Layer 6-A / 6-B / 6-C / 6-D
  with supporting modules.
- `methodology/` — canonical methodology framework artifacts (referenced
  at §10.4; full presentation in the companion methodology paper).

The continuous-integration configuration sits at `build.yml`.

## §4 Audit and decision artifacts (companion methodology paper material)

The audit framework that produced the manuscript is not a claimed
contribution of this paper and is presented in the companion methodology
paper. For reviewers who wish to inspect the audit trail referenced at §4.5
GenAI disclosure:

- internal Phase-7 audit documents — per-sub-phase
  Claude-session-context audit findings.
- internal Phase-7 audit documents — three-voice raw audit
  outputs (Claude-fresh, Grok, Gemini) per sub-phase.
- internal Phase-7 audit documents — four-way
  consolidation per sub-phase.
- internal Phase-7 audit documents — Decision 25
  four-outcome triage adjudication per sub-phase.
- internal Phase-7 audit documents — sub-phase closure
  reports.
- the internal post-Phase-7 housekeeping closure report — post-Phase-7
  methodology framework graduation cycle closure.
- `methodology/*.md` — canonical methodology framework artifacts
  (8 artifacts: 2 pre-Phase-7 + 6 post-Phase-7-housekeeping; plus
  `post_phase_7_integration_notes.md`).

These are reachable from the tagged commits enumerated in §1 of this
document.

## §5 Operational note for Session 62 submission execution

If the repository is currently private (per project state), it must be made
public before arXiv v1 submission execution at Session 62. Verification of
public accessibility at Session 62 pre-submission is documented in the
Session 61 closure report carrying-forward conditions.
