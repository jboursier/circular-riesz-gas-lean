# Optimal local laws and central limit theorem for the circular Riesz gas

A machine-checked **Lean 4** formalization of the paper

> Jeanne Boursier,
> *Optimal local laws and central limit theorem for the circular Riesz gas*,
> [arXiv:2112.05881](https://arxiv.org/abs/2112.05881).

The five main results of the paper, Theorems 1, 2 and 3 and Corollaries 1 and 2, are proved in
the form in which its introduction states them, **for every inverse temperature `β > 0` and every
Riesz exponent `0 < s < 1`**. The formalization follows the revised version of the paper (2026).
Its numbering of results is used below and may differ from earlier arXiv versions.

The development is built on [mathlib](https://github.com/leanprover-community/mathlib4) alone.

[![CI](https://github.com/jboursier/circular-riesz-gas-lean/actions/workflows/build.yml/badge.svg?branch=main)](https://github.com/jboursier/circular-riesz-gas-lean/actions/workflows/build.yml)
[![Comparator audit](https://github.com/jboursier/circular-riesz-gas-lean/actions/workflows/comparator.yml/badge.svg?branch=main)](https://github.com/jboursier/circular-riesz-gas-lean/actions/workflows/comparator.yml)

## What is proved

The paper studies `N` particles on the circle `T = ℝ/ℤ` at inverse temperature `β > 0`,
interacting through the Riesz kernel of exponent `s ∈ (0, 1)`:

> `g(x) = ζ(s, x) + ζ(s, 1 - x)`,  `H_N = N^{-s} Σ_{i ≠ j} g(x_i - x_j)`,
> `dP_{N,β} = Z_{N,β}^{-1} exp(-β H_N) 1_{D_N} dX_N`.

Here `ζ(s, x)` is the Hurwitz zeta function and `D_N` is the set of configurations whose real
lifts are ordered, `x_1 < ... < x_N < x_1 + 1`, with labels extended by `x_{i+N} = x_i + 1`. The
results quantify the fluctuations of the gas at every scale above the microscopic one: rigidity
of gaps and interval counts, the variance of linear statistics of singular test functions, and
central limit theorems for these statistics, for interval counts and for gaps.

The five main results are stated in [`Riesz1/Frozen/`](Riesz1/Frozen/), one file each, and
`import Riesz1` loads them.

| Paper | Lean declaration | Content |
| --- | --- | --- |
| Theorem 1 | `Riesz1.almost_optimal_rigidity` | Near-optimal rigidity of gaps and of interval counts, with stretched-exponential tails. |
| Theorem 2 | `Riesz1.quantitative_variance` | Variance expansion of singular linear statistics at every scale `ℓ_N ≥ 1/N`. |
| Theorem 3 | `Riesz1.central_limit_theorem` | CLT for singular linear statistics, with a rate in the bounded-Lipschitz distance. |
| Corollary 1 | `Riesz1.fluctuations_gaps_discrepancy` | CLT for the number of particles in an interval and for gaps. |
| Corollary 2 | `Riesz1.power_law_observable` | CLT for the power-law observables `ζ(α, x) + ζ(α, 1 - x)`, `0 < α < s/2`. |

Each statement also concludes that the model is well defined: for every `N ≥ 1` the partition
function `Z_{N,β}` is positive and finite and `P_{N,β}` is a probability measure.

**Theorem 1 (near-optimal rigidity).** There is `ε₀ > 0` such that for every `ε ∈ (0, ε₀)` there
are `c, C > 0` such that, for every `N ≥ 1`:

1. *Gaps.* For every label `i` and every `1 ≤ k ≤ ⌊N/2⌋`,
   `P_{N,β}(|N(x_{i+k} - x_i) - k| ≥ k^{s/2+ε}) ≤ C exp(-c k^{ε/(4(s+2))})`.
2. *Discrepancy in an interval.* For every `x ∈ T` and every `ℓ ∈ (0, 1/4]`, the number `n` of
   particles in `(x - ℓ, x + ℓ)` satisfies
   `P_{N,β}(|n - 2Nℓ| ≥ (Nℓ)^{s/2+ε}) ≤ C exp(-c (Nℓ)^{ε/(4(s+2))})`.

For a test function `ξ` on the circle `ℓ^{-1}T` of length `ℓ^{-1}`, write
`Fluct_N[ξ(ℓ^{-1} ·)] = Σ_i ξ(ℓ^{-1} x_i) - Nℓ ∫ ξ` and
`σ²_ℓ(ξ) = (2π)^{1-s} ℓ^{-s} ‖ξ(ℓ^{-1} ·)‖²_{H^{(1-s)/2}(T)} / (2β c_s)`, with
`c_s = 2^{1-s} √π Γ((1-s)/2) / Γ(s/2)`. For `ξ` supported in `(-1/2, 1/2)`, `σ²_0(ξ)` is the same
expression with the `H^{(1-s)/2}(ℝ)` seminorm of the extension of `ξ` by zero. The test functions
satisfy Assumption 1.1 of the paper: (A1) `ξ` minus its mean is the derivative of a
`C^{1-s+ε}` function, (A2) the transport map `ψ` of `ξ` is `C²` away from finitely many points
`a_j`, (A3) `|ψ''|` is bounded by a multiple of `Σ_j |x - a_j|^{-(2-s+α)}` near the points and of
`|x|^{-(3-s)}` far away, for some `α ∈ [s-1, s/2)`, and (A4) either `ℓ_N = 1` and `ξ` does not
depend on `N` (macroscopic case), or `ℓ_N → 0` and `ξ` is the periodization of one fixed function
supported in a closed subinterval of `(-1/2, 1/2)` (mesoscopic case). The data of the assumption
do not depend on `N`.

**Theorem 2 (variance of singular linear statistics).** Let `ξ` and `(ℓ_N)` satisfy Assumption 1.1
with exponent `α`.

1. For every `N`, `ξ(ℓ_N^{-1} ·)` lies in `H^{(1-s)/2}(T)` and `σ²_{ℓ_N}(ξ)` is finite.
2. For every `ε > 0` there is `C > 0`, depending only on `β`, `s`, `ε` and `ξ` and its data, such
   that for every `N` with `Nℓ_N ≥ 1` the variance of `Fluct_N[ξ(ℓ_N^{-1} ·)]` is finite and
   `|Var Fluct_N[ξ(ℓ_N^{-1} ·)] - (Nℓ_N)^s σ²_{ℓ_N}(ξ)| ≤ C (Nℓ_N)^{max(2s-1, 2α)+ε}`.
3. If `ξ` is supported in `(-1/2, 1/2)`, then `σ²_0(ξ)` is finite and there is `C > 0` with
   `|σ²_a(ξ) - σ²_0(ξ)| ≤ C a^{2-s}` for every scale `a ∈ (0, 1]`.

**Theorem 3 (CLT for singular linear statistics).** Let `ξ` and `(ℓ_N)` satisfy Assumption 1.1 with
exponent `α`, and assume `Nℓ_N → ∞`. Write `G_N = (Nℓ_N)^{-s/2} Fluct_N[ξ(ℓ_N^{-1} ·)]`.

1. *Convergence.* In the macroscopic case, `G_N` converges in law to `N(0, σ²_1(ξ))`. In the
   mesoscopic case, it converges in law to `N(0, σ²_0(ξ))`.
2. *Rate.* Let `r = (2-s)(s-2α)/(2(4+s))`. For every `ε > 0` there is `C > 0` such that, for
   every `N` with `Nℓ_N ≥ 1`,
   `d_BL(Law(G_N), N(0, σ²_{ℓ_N}(ξ))) ≤ C (Nℓ_N)^{ε + max((s-1)/2, -r)}`,
   where `d_BL` is the bounded-Lipschitz distance.

**Corollary 1 (CLT for interval counts and gaps).** Let `σ² = cot(πs/2)/(2βπs)` and
`V_s(t) = ζ(-s, t) + ζ(-s, 1-t) - 2ζ(-s)`.

1. For every `a ∈ (0, 1/2)` and every `(ℓ_N)` in `(0, 1]` with `Nℓ_N → ∞`, the number `n_N` of
   particles in `(-aℓ_N, aℓ_N)` satisfies `(n_N - 2aNℓ_N)/√(N^s V_s(2aℓ_N)) → N(0, σ²)` in law.
2. For every sequence `(k_N)_{N ≥ 2}` with `1 ≤ k_N ≤ ⌊N/2⌋` and `k_N → ∞`,
   `(N(x_{1+k_N} - x_1) - k_N)/√(N^s V_s(k_N/N)) → N(0, σ²)` in law.

**Corollary 2 (CLT for power-law observables).** Let `α ∈ (0, s/2)` and
`ξ(x) = ζ(α, x) + ζ(α, 1-x)` for `0 < x < 1`. Then
`N^{-s/2}(Σ_i ξ(x_i) - N ∫ ξ) → N(0, (2π)^{-1+2α-s} c_α² ζ(1+s-2α)/(β c_s))` in law.

## Standing assumptions and scope

1. **Every theorem holds for every `β > 0` and `0 < s < 1`.** The constants depend only on `β`,
   `s`, `ε` and, in Theorems 2 and 3, on the test function and the data of Assumption 1.1. They
   are chosen before the scale sequence, the number of particles, the label, the gap index and
   the center of the interval, as in the paper.
2. **Axioms and incomplete proofs.** The library contains no `sorry`, no `admit`, no
   `native_decide` and no new `axiom`. The axiom report of each main result consists of exactly
   `propext`, `Classical.choice` and `Quot.sound`. The main results rely on no unproved result.
   The paper cites three classical results that mathlib does not contain: the Prékopa–Leindler
   inequality, the Bakry–Émery criterion for the logarithmic Sobolev inequality, and Pinsker's
   inequality. They are stated in [`Riesz1/Frozen/External/`](Riesz1/Frozen/External/) and proved
   in [`Riesz1/Externals/`](Riesz1/Externals/). Intermediate results take them as explicit
   hypotheses, and the main results supply their proofs.
3. **The model.** The circle of length `L` is mathlib's `AddCircle L`, with arclength measure,
   and Fourier coefficients are mathlib's `fourierCoeff`. A configuration of `N` points is its
   ordered real lift `x_0 < x_1 < ... < x_{N-1} < x_0 + 1` with `0 ≤ x_0 < 1`, and the Gibbs
   measure is `Z_{N,β}^{-1} exp(-β H_N)` times Lebesgue measure on these lifts. The paper's
   label 1 is label 0 in Lean. The kernel is `g(x) = 2 Re ζ_even(x, s)`, written with mathlib's
   even Hurwitz zeta function. The paper's formula for `g` as a limit of truncated lattice sums is
   a proved theorem, not the definition.
4. **Test functions.** A test function is one fixed real `L²` profile on the unit circle, used at
   every scale. In the mesoscopic case it vanishes almost everywhere outside `(-ρ, ρ)` for some
   `0 < ρ < 1/2`, and it is periodized on the circle of length `ℓ_N^{-1}`. Fractional Laplacians,
   Sobolev seminorms and the transport map are defined by their Fourier multipliers, with the
   zero mode set to zero. Derivatives in Assumption 1.1 are distributional.
5. **Scales and limits.** A scale sequence is a map `ℕ+ → (0, 1]`, and `ℓ_N ≫ 1/N` means
   `Nℓ_N → ∞`. Convergence in law is convergence of the integrals of every bounded continuous
   function, along `N = n + 1`. The bounded-Lipschitz distance is the supremum of
   `|∫ f dμ - ∫ f dν|` over `C¹` functions `f` with `|f| ≤ 1` and `|f'| ≤ 1`. `N(0, v)` is
   mathlib's Gaussian measure, which is the Dirac mass at `0` when `v = 0`.
6. **Total definitions.** Lean's real-valued definitions are total: division by zero, a
   non-integrable integral and a non-summable series all have conventional values. Partition
   functions and variances therefore take values in `[0, ∞]`, and the statements conclude their
   finiteness, the positivity of normalizing denominators and the measurability of the
   normalized variables. None of these facts is assumed.
7. **Explicit versus implicit.** Some statements make explicit what the paper leaves implicit,
   such as the well-definedness of the model and the finiteness of the variances. Theorem 2(3)
   assumes that the test function satisfies Assumption 1.1 for some scale sequence, and its
   comparison of `σ²_a(ξ)` with `σ²_0(ξ)` holds for every scale `a ∈ (0, 1]`.
8. **What is not formalized.** The discussion that follows Theorem 3 in the paper (joint
   convergence of smooth pairings through the Cramér–Wold device, and the fractional Gaussian
   field limit of the potential) and the remarks of the introduction are not stated as theorems.
   The intermediate results of the paper are proved along the way, under names of their own.

## Guarantees

- **No `sorry`.** The library has none. The five comparator challenges under
  [`Riesz1Audit/`](Riesz1Audit/) each contain one intentional statement-level `sorry`, which the
  corresponding solution proves.
- **Standard axioms only.** The axiom report of each of the five main results lists exactly
  `propext`, `Classical.choice` and `Quot.sound`.
  [`Riesz1/Meta/AxiomsAudit.lean`](Riesz1/Meta/AxiomsAudit.lean) prints the reports, and
  `scripts/check_axioms.py` fails on any other axiom, on `sorryAx`, and on a missing or an
  unexpected report.
- **Builds from a clean checkout.** `lake build` of this tree, in a fresh build directory,
  completed its 5,629 jobs with 0 warnings and no errors. The continuous-integration build rejects
  any warning. `scripts/check_sources.py` rejects `sorry`, `admit`, new axioms, `opaque`,
  `native_decide`, `implemented_by`, `extern`, kernel type-check bypasses and heartbeat overrides.
- **Independent check of the statements.** The five main results are restated in
  [`Riesz1Audit/`](Riesz1Audit/), one Mathlib-only challenge file per result. Each challenge
  contains every definition its statement uses, so it can be read without the library. The
  solution file proves each restatement from the library, and
  [leanprover/comparator](https://github.com/leanprover/comparator) checks that the statement is
  proved, with only the three standard axioms, and replays the proof with the Lean, NanoDa and
  con-ron kernels. See [`Riesz1Audit/README.md`](Riesz1Audit/README.md).
- **Statements checked before the proofs.** The statements and the definitions they use were
  written before the proofs. Each one was compared with the paper by independent refute-first
  audits, including a blind translation of the Lean text back into mathematics.
  [`Riesz1/Sanity/`](Riesz1/Sanity/) checks the definitions against known values.
- **Pinned toolchain.** Lean and mathlib `v4.35.0`, with the exact revisions recorded in
  [`lake-manifest.json`](lake-manifest.json).

## Size

The library contains 1,535 Lean files with 246,532 physical lines, on top of mathlib. The 15
comparator files under `Riesz1Audit/`, with 6,799 lines, are not included in these counts.

## Building

Install [elan](https://github.com/leanprover/elan). The toolchain is pinned in
[`lean-toolchain`](lean-toolchain), and Lake fetches mathlib.

```bash
lake exe cache get   # prebuilt mathlib
lake build
```

With mathlib downloaded, a fresh build of the library took about 16 minutes on an Apple
M4 machine with 10 cores.

To reproduce the axiom reports:

```bash
lake env lean Riesz1/Meta/AxiomsAudit.lean 2>&1 | tee .lake/axioms-audit.log
python3 scripts/check_axioms.py .lake/axioms-audit.log
```

`scripts/check_all.sh` runs the zero-warning build, the source sweep and the axiom report.

## Running the comparators

Each pair has a configuration `Riesz1Audit/<Pair>/comparator.json` that permits exactly
`propext`, `Classical.choice` and `Quot.sound`. The comparator checks that the solution proves
the challenge statement, that the definitions the statement uses are the same on both sides,
and replays the proof with the Lean, NanoDa and con-ron kernels bundled with the toolchain.

```bash
lake build Riesz1Audit           # the challenges and their solutions
./scripts/run_comparators.sh     # all five pairs, or name some pairs
```

The comparator runs the build inside a `bubblewrap` sandbox, which exists on Linux only. On macOS,
`./scripts/run_comparators.sh --no-sandbox` runs the same checks without the sandbox. Logs are
kept under `.lake/comparator-logs/`.

There are two continuous-integration workflows. **CI** builds the library, rejects any warning
and checks the axiom reports, on every push to `main` that changes code or build configuration.
**Comparator audit** then checks the five pairs, one job per pair. Both can be started by hand
from the [Actions page](https://github.com/jboursier/circular-riesz-gas-lean/actions). See
[`CONTRIBUTING.md`](CONTRIBUTING.md) for build conventions.

## Repository layout

```text
Riesz1.lean                 the root module, importing the five main results
Riesz1/
  Frozen/                   the statements of the main results and every definition they use,
                            one declaration per file
  Frozen/External/          the three classical results the paper cites
  Main/                     the proofs of the main results
  Kernel/                   the Riesz kernel, Fourier analysis on the circle, the transport map
                            and admissible test functions (Sections 1 and 2)
  Gibbs/                    well-definedness and symmetries of the Gibbs measure
  HelfferSjostrand/         the Helffer–Sjöstrand equation, convexity, the Brascamp–Lieb
                            inequality and comparison principles (Section 3)
  Rigidity/                 near-optimal rigidity (Section 4)
  Variance/                 the variance expansion (Section 5)
  CLT/                      the central limit theorem and its corollaries (Section 6)
  Auxiliary/                the auxiliary estimates of Appendix B
  Externals/                proofs of the Prékopa–Leindler inequality, the Bakry–Émery
                            criterion and Pinsker's inequality
  Bridges/, Unconditional/  assembly: intermediate results with their hypotheses discharged
  ToMathlib/                results at mathlib generality (log-concavity, weighted Sobolev
                            spaces, Gaussian measures, ...)
  Sanity/                   checks of the definitions against known values
  Meta/AxiomsAudit.lean     the axiom report, built by `lake build`, not imported by the root
Riesz1Audit/                the Mathlib-only restatements and their solutions
scripts/                    source sweep, axiom check and comparator runner
.github/workflows/          build and comparator workflows
```

## How this was built

The Lean code was written with AI assistance under the direction of the author, who fixed the
statements to be formalized. OpenAI's GPT-6.1 Sol, through the Codex CLI, wrote the statements
and the proofs and audited the statements against the paper. Anthropic's Claude Haiku 5.5 made the
blind back-translations of the statements and mechanical edits, and Claude Opus 5.5 coordinated
the agents, reviewed their work and prepared this release, through Claude Code. The revision of
the paper that this repository formalizes was prepared with GPT-6 Astra and Claude Opus 5.5.
Every proof is checked by the Lean kernel. The models, tooling and review status are disclosed in
[`formalization.yaml`](formalization.yaml), following the
[mathlib-initiative](https://github.com/mathlib-initiative/formalization.yaml) standard.

We thank Scott Armstrong for providing the skill files used for the formalization.

## Author and citation

The Lean development is by **Jeanne Boursier**. To cite it, use [`CITATION.cff`](CITATION.cff).

## License

The Lean development is licensed under the Apache License 2.0. See [`LICENSE`](LICENSE).
