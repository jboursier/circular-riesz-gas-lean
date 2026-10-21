# Independent statement comparisons

The five main results of the paper are each restated here using nothing but Mathlib and the
definitions that the restatement itself contains. Each restatement is proved from the library,
and [leanprover/comparator](https://github.com/leanprover/comparator) checks that the statement
proved from the library is the restated one. A reader who wants to know what a main result says
therefore needs only the corresponding `Challenge.lean`, not the library.

## How a pair is built and checked

Each subdirectory is one comparator pair:

| File | Role |
| --- | --- |
| `Challenge.lean` | The statement. It imports Mathlib only, contains every definition that the statement uses, and has exactly one `sorry`, the proof of the final theorem. **This is the file to read.** |
| `Solution.lean` | The proof. It states the same theorem and proves it from the library. |
| `SolutionBasic.lean` | The definitions of the challenge, copied verbatim and without the final theorem, so that the solution can state the same theorem. |
| `comparator.json` | The comparator configuration: the challenge and solution modules, the theorem name, and the permitted axioms. |

The definitions of a challenge are the files of `Riesz1/Frozen/` that its statement uses,
copied without change and in dependency order, inside the namespace `Riesz1Audit.<Pair>`. For
example, `Riesz1.gibbsMeasure` of the library is `Riesz1Audit.CentralLimitTheorem.Riesz1.gibbsMeasure`
in the challenge of Theorem 3. The namespace lets the solution import both the challenge's
definitions and the library. The solution proves the challenge's theorem `by exact` the theorem
of the library: the two statements agree after unfolding the definitions, and Lean's kernel
checks this.

`SolutionBasic.lean` is proof infrastructure. It adds no hypothesis to the statement: the
comparator compares the theorem in the challenge with the theorem in the solution, together with
every definition that the statement depends on. `comparator.json` permits exactly `propext`,
`Classical.choice` and `Quot.sound`. `scripts/run_comparators.sh` adds the NanoDa and con-ron
kernels bundled with the Lean toolchain, so that the solution is replayed by three independent
kernels. See the [README](../README.md#running-the-comparators) for how to run them.

## The pairs

| Pair | Paper statement | Library declaration |
| --- | --- | --- |
| [`AlmostOptimalRigidity`](AlmostOptimalRigidity/) | Theorem 1 | `Riesz1.almost_optimal_rigidity` |
| [`QuantitativeVariance`](QuantitativeVariance/) | Theorem 2 | `Riesz1.quantitative_variance` |
| [`CentralLimitTheorem`](CentralLimitTheorem/) | Theorem 3 | `Riesz1.central_limit_theorem` |
| [`FluctuationsGapsDiscrepancy`](FluctuationsGapsDiscrepancy/) | Corollary 1 | `Riesz1.fluctuations_gaps_discrepancy` |
| [`PowerLawObservable`](PowerLawObservable/) | Corollary 2 | `Riesz1.power_law_observable` |

The module documentation at the top of each challenge states the result in mathematical
language and explains how its objects are specified.

## Conventions shared by the challenges

- Every result is stated for every `β > 0` and `0 < s < 1`.
- A configuration is its ordered real lift `x_0 < ... < x_{N-1} < x_0 + 1` with `0 ≤ x_0 < 1`,
  and the paper's label 1 is label 0.
- Real-valued definitions are total, so the statements conclude the positivity, finiteness and
  measurability facts that they need. None of them is assumed.
