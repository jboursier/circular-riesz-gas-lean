# Contributing and building

This repository is mainly a finished artifact, the formalization of one paper, but issues and
pull requests are welcome.

## Building locally

```bash
lake exe cache get   # prebuilt mathlib oleans
lake build           # the library
```

The toolchain is pinned in `lean-toolchain` and managed by
[elan](https://github.com/leanprover/elan). The library must build with **no warnings**. The only
files that contain a `sorry` are the five comparator challenges `Riesz1Audit/*/Challenge.lean`,
each with exactly one, in its final theorem.

`lake build Riesz1` builds the library alone, and `lake build Riesz1Audit` builds the comparator
files. `scripts/check_all.sh` runs the zero-warning build, the source sweep and the axiom report.

## The main results and the axiom report

The statements of the main results are in `Riesz1/Frozen/`, one declaration per file, together
with every definition they use. Each theorem there is proved `by exact` a theorem of the same name
in `Riesz1/Main/`. Their axiom reports must consist of exactly `propext`, `Classical.choice` and
`Quot.sound`:

```bash
lake env lean Riesz1/Meta/AxiomsAudit.lean 2>&1 | tee .lake/axioms-audit.log
python3 scripts/check_axioms.py .lake/axioms-audit.log
```

`Riesz1/Meta/AxiomsAudit.lean` is not imported by the root module, because a `#print axioms`
command runs again whenever its module is rebuilt.

## Conventions for Lean files

- Every Lean file uses the module system (`module`, `public import`, `@[expose] public section`)
  and has at most 1500 lines.
- No `sorry`, `admit`, `native_decide`, new `axiom`, `opaque` declaration or
  `set_option maxHeartbeats` anywhere in the library. `scripts/check_sources.py` enforces this.
- Keep the statements in `Riesz1/Frozen/` faithful to the paper. A change to one of them must be
  copied into every challenge that uses it and into its `SolutionBasic.lean`, and checked against
  the paper.
- The comparator compares every theorem of `Riesz1/Frozen/` that a main statement uses, such as
  `liftL2`, together with its proof. Such a proof must not create private auxiliary lemmas, whose
  names depend on the module: avoid `omega`, and `simp` with an `↔` lemma, in these proofs and in
  proof terms inside a statement.
- Refer to a result of the paper by its number in the revised version (2026).

## Comparators

Each pair under `Riesz1Audit/` has a Mathlib-only `Challenge.lean`, a `SolutionBasic.lean` that
repeats its definitions, a `Solution.lean` that proves the same statement from the library, and a
`comparator.json` that permits exactly
`propext`, `Classical.choice` and `Quot.sound`. Run all pairs with `scripts/run_comparators.sh`,
as described in the README. A missing pair, a missing tool or a failed kernel check is a failure.
Logs are kept under `.lake/comparator-logs/`.

## Continuous integration

`.github/workflows/build.yml` builds the library, rejects any warning, sweeps the sources and
checks the axiom report. `.github/workflows/comparator.yml` runs after each successful build on
`main` and checks the five comparator pairs with the kernels bundled with the Lean toolchain,
one job per pair.
