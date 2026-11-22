# Dictators are most informative

Vu Khac Ky and Tuan Tran

This repository accompanies the proof of the Courtade–Kumar conjecture. Among all Boolean functions of a uniform bit vector, a dictator maximizes the mutual information between the function value and the full vector observed through independent binary noise. Every signed dictator attains the bound.

[Paper (PDF)](CK-paper.pdf) · [Editable LaTeX source](CK-paper.tex) · [Lean 4 proof](lean/README.md)

## Reproduce the arithmetic in the paper

Use Python 3.11 or later. From the repository root:

```sh
python3 -m venv .venv
. .venv/bin/activate
python3 -m pip install -r requirements.txt
python3 verify.py
```

The replay checks `SHA256SUMS`, then writes fresh reports to a temporary directory. Use `--output /path/to/new-directory` to choose a report directory outside the package. The computations use exact rational arithmetic and outward-rounded Arb intervals. Run Python with assertions enabled.

| Paper region | What the replay checks | Inputs |
| --- | --- | --- |
| Low correlation and the two-coordinate moment estimate | Analytic proof constants and exact endpoint signs | [Low-correlation verifier](low_correlation_verify.py), [moment verifier](two_core_moment_verify.py) |
| Middle range through `rho = 49/50` | Cubic scalar gates at band endpoints, coefficient coverage, and 29 profile-clock bounds over 56 integration intervals with 152 supporting-line evaluations | [Rational partitions](certificates/middle), [one-coordinate clocks](convex_source_certificate.json), [two-coordinate clocks](tangent_clock_certificate.json) |
| Compact range in `u = arctanh(rho)` | Whole-interval inequalities on 24 noise intervals, including 96 height-endpoint inequalities. A separate audit checks the original cost formulas on the full height domain | [Compact certificate](qualitative_compact_certificate.json), [Taylor verifier](qualitative_compact_verify.py), [independent audit](qualitative_compact_audit.py) |
| Tail `u >= 8` | Scalar constants used in the analytic argument | [Tail constants verifier](check_qualitative_tail.py) |

The [recorded replay summary](results/verification_summary.json) gives the output of all ten stages, with SHA-256 values for the reports after removing runtime fields. The reports certify the numerical parts of the article. For the derivation of the universal inequality in Lean, see the [Lean proof guide](lean/README.md).

## Update or package the supplement

- `make paper` builds the PDF from `CK-paper.tex` with pdfLaTeX. The LaTeX source contains its bibliography.
- `make check` verifies the input manifest without replaying the arithmetic.
- After editing the manuscript, code or certificates, run `make update-results`. It refreshes the input and linked-certificate hashes, replays all ten stages, and publishes the new summary only after the replay succeeds.
- `make verify` reruns the arithmetic and compares its numerical reports with the recorded summary. Review the source and result diffs together before committing.
- `make bundle` verifies the current revision and creates `CK-exact.zip` from the manuscript, verifiers, data and results. The archive runs independently with the same Python setup and `python3 verify.py`.

The clock certificates link each band to its rational parameters and coefficient partition by SHA-256. Arithmetic validity comes from the checks reconstructed by the verifiers. Edit the rational inputs and supporting-line records alongside the corresponding paper argument and replay them before distributing the revised bundle.
