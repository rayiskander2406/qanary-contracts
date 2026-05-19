# IEEEtran-compsoc Measurement Scaffold (MEASUREMENT-ONLY)

**Not a submission artifact.** This directory exists solely for the
pre-Session-59 page measurement (Decision 20 / Decision 22). Results:
the internal pre-Session-59 measurement report.

## Committed (reproducible scaffold)
- `qanary_contracts_measurement.tex` — IEEEtran-compsoc wrapper (`[10pt,journal,compsoc]`).
- `_fix_longtable.pl` — pandoc `longtable` → `table`+`tabular` transform (longtable is incompatible with IEEEtran two-column).
- `.gitignore` / `README.md`.

## Regeneration (from repo root)
```bash
cd paper/ieeetran-measurement
sed -n '16,22p' ../qanary_contracts_manuscript.md > _abstract.md
sed -n '26,$p'  ../qanary_contracts_manuscript.md > _body.md
pandoc _abstract.md -f markdown -t latex -o _abstract.tex
pandoc _body.md -f markdown -t latex --shift-heading-level-by=-1 -o _body.tex
perl _fix_longtable.pl < _body.tex > _body_fixed.tex
tectonic -X compile qanary_contracts_measurement.tex --keep-logs
pdfinfo qanary_contracts_measurement.pdf | grep Pages
```
(Line ranges valid at manuscript HEAD (internal commit); re-derive if the
manuscript front-matter/abstract/§1 boundaries move.)

## Engine note
Compiled with **tectonic** (XeTeX-based; `pdflatex`/`xelatex`/`lualatex`
absent in environment). Tectonic is a complete LaTeX engine satisfying the
"actual compile" requirement; it auto-fetches IEEEtran from its bundle.

## Known measurement-grade caveats (see report §2, §7)
Wide multi-column tables forced to single-column `tabular` inflate page
count (submission must use `table*`); References as pandoc list; placeholder
title/author; no submission typography tuning. Page count is measurement-
grade, not submission-grade.
