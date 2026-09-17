# Dictators are the most informative Boolean functions

Vu Khac Ky and Tuan Tran · 16 September 2026

This paper proves the exact Courtade–Kumar theorem. Its introduction states the stability theorem and cites the companion paper for that proof. No stability estimate is used in the exact proof.

## Read or compile

The compiled article is `CK-paper.pdf`. The complete editable source is `CK-paper.tex`, with its bibliography embedded. Compile from this folder with a standard TeX Live installation:

```sh
pdflatex -interaction=nonstopmode -halt-on-error CK-paper.tex
pdflatex -interaction=nonstopmode -halt-on-error CK-paper.tex
pdflatex -interaction=nonstopmode -halt-on-error CK-paper.tex
```

No sibling folders, external bibliography files, or prior revisions are required.

## Replay the numerical obligations

Use Python 3.11 or later. Install the pinned requirements in a virtual environment, then run:

```sh
python3 -m pip install -r requirements.txt
python3 verify.py
```

The command first checks `SHA256SUMS`, then runs every stage and prints the location of fresh reports. To choose a new report directory outside this package, pass `--output /absolute/path/to/new-reports`. `--check-only` checks file integrity and does not replay numerical calculations. Python optimization is rejected because assertions are part of the checks.

The compact certificate uses the moving influence cutoff throughout its 24 noise intervals. The endpoint proof reaches the local entropy neighborhood analytically. The replay has 10 stages.

Current rational source partitions are in `certificates/middle/`. Their data retain the original rational values and source hashes; all signs and full coverage are recomputed by the current verifiers. Historical generator hashes inside the data are provenance metadata, not evidence of validity. No obsolete generator or old replay is required.

The independent audits use separately derived formulas. Strict signs are accepted only when the full outward-rounded enclosure has the required sign. The replay verifies numerical hypotheses, partitions, and finite constants; it does not constitute formal verification of the analytic proof.

## Package contents

Only the current paper, the active verifier modules and their input data, the build/replay instructions, the pinned requirements, and the file manifest are included. Superseded drafts, old reports, research diagnostics, historical wrappers, and unused certificates have been removed.
