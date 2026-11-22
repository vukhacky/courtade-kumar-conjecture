# Lean formalization of the Courtade–Kumar conjecture

The formalization proves the main theorem of [Dictators are most informative](../CK-paper.pdf) by Vu Khac Ky and Tuan Tran. Let `X` be uniform on the Boolean cube of any positive dimension and let `Y` be obtained by flipping each coordinate independently with probability `p = (1 - ρ) / 2`, independently of `X`. For every Boolean function and every `ρ ∈ [0, 1]`,

```text
I(f(X); Y) ≤ log 2 − h_binary(p).
```

Every signed dictator attains equality. Entropy uses natural logarithms and the convention `0 log 0 = 0`. See [the theorem written with explicit atom masses and Shannon entropy](CK/PaperStatement.lean).

| Declaration | Statement |
| --- | --- |
| [`CK.main`](CK/Results/Main.lean) | The finite Shannon inequality and signed-dictator attainment. |
| [`CK.mutualInformation_le_binaryEntropy`](CK/Results/Main.lean) | The inequality with the binary-entropy upper bound written explicitly. |
| [`CK.randomMutualInformation_le_binaryEntropy_independent_flips`](CK/Results/Probability.lean) | The inequality on an arbitrary probability space with uniform input and independent Bernoulli flips. |
| [`CK.Paper.stoc_main`](CK/PaperStatement.lean) | Both claims with Shannon entropy and the probability law written explicitly. |

## Build and check

Install [Elan](https://github.com/leanprover/elan), Git and Python 3.11 or newer. Run these commands from the repository root.

```sh
cd lean
python3 scripts/verify_lean.py --fetch-cache
```

The checker uses the [pinned Lean toolchain](lean-toolchain) and [dependency revisions](lake-manifest.json), compiles every local module into a new directory, and checks their transitive axiom dependencies. The only allowed axioms are `propext`, `Classical.choice`, and `Quot.sound`. The proof includes every certificate as Lean source. The kernel checks the exact rational computations.

The build defaults to one Lean process because some modules need several gigabytes of memory. Allow about an hour for a sequential build on a machine with sufficient memory. Use `--jobs 2` to run two Lean processes. When the pinned dependency cache is already installed, omit `--fetch-cache`. For editor use, open `lean/` as the project and run `lake build` to build the library for `import CK`.

## Proof structure

| Part | Lean source |
| --- | --- |
| Finite Shannon mutual information, the binary symmetric channel, and the identity with the entropy functional | [MutualInformation](CK/Basic/MutualInformation.lean), [ShannonBridge](CK/Basic/ShannonBridge.lean), [ProbabilitySpace](CK/ProbabilitySpace.lean) |
| Correlations from zero to `49/50` | [MiddleRange](CK/Results/MiddleRange.lean) |
| Monotone compression and the higher-correlation argument | [Compression](CK/Reduction/Compression.lean), [HighAssembly](CK/Results/HighAssembly.lean), [FinalAssembly](CK/Results/FinalAssembly.lean) |
| Five inequalities on 50 closed rational subintervals in the variable `u = artanh ρ` | [CompactCircuit](CK/Certificate/CompactCircuit.lean), [CompactProgram](CK/Certificate/CompactProgram.lean), [CompactCover](CK/Certificate/CompactCover.lean) |
| Analytic argument for `u ≥ 8` and the endpoint `ρ = 1` | [HighTailRange](CK/Results/HighTailRange.lean), [Tail](CK/High/Tail.lean), [Barrier](CK/Analysis/Barrier.lean) |

The Lean certificates use second-order Taylor enclosures for the five inequalities in the compact range. The manuscript's [Python verification](../README.md) uses its own partition and Taylor bounds for this range. Both routes have their input data in the repository.
