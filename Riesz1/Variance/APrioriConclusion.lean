/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Frozen.Circle
public import Riesz1.Frozen.CentralRep
public import Riesz1.Frozen.GibbsMeasure
public import Riesz1.Frozen.ObservationLength
public import Riesz1.Frozen.Scale
public import Riesz1.Frozen.Variance

/-!
# The assertion of Lemma 5.2

`Riesz1.Internal.APrioriConclusion` states every assertion of Lemma 5.2 in terms of the
following objects:

* the Gibbs law `gibbsMeasure P N` on `Configuration N`.
* the variance `variance`, the squared centered lintegral in `ℝ≥0∞`.
* the circle `Circle (observationLength ℓ)` of length `ℓ⁻¹`, on which the test function `f` lives.
* the circle distance `|centralRep (observationLength ℓ) (u - c)|` from the point `c`, which is
  the reading of `|u|` in the envelope (`c = 0` is the origin).

The proposition is the universal form of the lemma. It is a `Prop` definition only: no proof
of Lemma 5.2 is given here. `Riesz1.Internal.aPrioriConclusion_of_externals` proves it, and
`Riesz1.Internal.clt_error1_of_apriori` (a step in the proof of Theorem 3) takes it as its one
hypothesis.

Reading of the lemma, assertion by assertion:

* `0 < s < 1`, `β > 0` and the Gibbs law: the quantifier `P : Parameters`, with `β = P.val.1`
  and `s = P.val.2`.
* `λ ≥ 0`, `ε > 0`, and the constant `C` depending only on `β, s, λ, ε`: the quantifiers
  `lam`, `ε` come first, then `∃ C`, which is chosen before `N`, `ℓ`, `M` and `f`.
* `0 < ℓ ≤ 1` and `Nℓ ≥ 1`: the scale `ℓ : Scale` and the condition `1 ≤ N * ℓ`.
* `f ∈ C¹(ℓ⁻¹ 𝕋)`: `ContDiff ℝ 1` of the lift of `f` to `ℝ`.
* The derivative envelope, with `|u|` the circle distance to the origin and the factor `M ≥ 0`
  (`aPrioriEnvelope`): `1_{|u| ≤ 2} / max(|u|, (Nℓ)⁻¹)^{1+λ} + 1_{|u| ≥ 2} / |u|^{3-s}`.
* The anchored bound `Var Σ_i f((x_i - x_1)/ℓ) ≤ C (Nℓ)^{ε+max(2λ,s)}`, with the factor `M²`:
  `anchoredSum`.
* The non-anchored bound `Var Σ_i f(x_i/ℓ) ≤ C (Nℓ)^{ε+max(2λ,s)}`, with the factor `M²`:
  `plainSum`.
* "A translate of `f` in the non-anchored bound, or a fixed change of the radius two in both, is
  allowed, with constants depending on that change": the envelope is centred at a real `c`
  (`u - c`) and has radius `R > 0` in place of `2`, and the constant `C` may depend on `c` and
  `R`. The anchored bound is asserted for `c = 0` only. The paper obtains the
  translate by rotation invariance, which moves the centre of a plain sum but preserves the
  relative coordinates `x_i - x_1`. The case `c = 0`, `R = 2` is the lemma as written.
* Integrability: the variance is that of an integrable random variable, so `∃ hA` concludes
  integrability before the variance bound.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Riesz1.Internal

/-- The derivative envelope of Lemma 5.2, at circle distance `d` from the centre, with
scale `K = Nℓ`, radius `R`, exponent `λ` and profile exponent `s`:
`1_{d ≤ R} / max(d, K⁻¹)^{1+λ} + 1_{d ≥ R} / d^{3-s}`. -/
def aPrioriEnvelope (s lam K R d : ℝ) : ℝ :=
  (if d ≤ R then ((max d K⁻¹) ^ (1 + lam))⁻¹ else 0) +
    (if R ≤ d then (d ^ (3 - s))⁻¹ else 0)

/-- The anchored sum `Σ_i f((x_i - x_1)/ℓ)` of Lemma 5.2 on configurations, with
`x_1 = X.val ⟨0, N.pos⟩` the first particle. -/
def anchoredSum (ℓ : Scale) (N : ℕ+) (f : Circle (observationLength ℓ) → ℝ)
    (X : Configuration N) : ℝ :=
  ∑ i : Fin (N : ℕ),
    f (((X.val i - X.val ⟨0, N.pos⟩) / ℓ.val : ℝ) : Circle (observationLength ℓ))

/-- The non-anchored sum `Σ_i f(x_i/ℓ)` of Lemma 5.2 on configurations. -/
def plainSum (ℓ : Scale) (N : ℕ+) (f : Circle (observationLength ℓ) → ℝ)
    (X : Configuration N) : ℝ :=
  ∑ i : Fin (N : ℕ), f (((X.val i / ℓ.val : ℝ)) : Circle (observationLength ℓ))

/-- **Assertion of Lemma 5.2.** For every parameters `P` (`β = P.val.1`, `s = P.val.2`),
every `λ ≥ 0`, every `ε > 0`, every radius `R > 0` and every centre `c ∈ ℝ`, there is `C > 0`
depending only on these data, such that for every particle number `N`, every scale `ℓ ∈ (0, 1]`
with `Nℓ ≥ 1`, every `M ≥ 0` and every `C¹` function `f` on `ℓ⁻¹ 𝕋` whose derivative obeys the
envelope with factor `M`, it follows that
`Var_{gibbsMeasure} (plainSum ℓ N f) ≤ C M² (Nℓ)^{ε + max(2λ, s)}`, and, when `c = 0`, that
`Var_{gibbsMeasure} (anchoredSum ℓ N f) ≤ C M² (Nℓ)^{ε + max(2λ, s)}`, with the sums
integrable. The case `c = 0`, `R = 2` is the lemma as written. The translate is allowed only in
the non-anchored bound and the change of radius in both. -/
def APrioriConclusion : Prop :=
  ∀ (P : Parameters) (lam : ℝ), 0 ≤ lam → ∀ ε : ℝ, 0 < ε → ∀ R : ℝ, 0 < R → ∀ c : ℝ,
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (ℓ : Scale), 1 ≤ (N : ℝ) * ℓ.val →
      ∀ M : ℝ, 0 ≤ M → ∀ f : Circle (observationLength ℓ) → ℝ,
        ContDiff ℝ 1 (fun u : ℝ => f (u : Circle (observationLength ℓ))) →
        (∀ u : ℝ, |deriv (fun t : ℝ => f (t : Circle (observationLength ℓ))) u| ≤
          M * aPrioriEnvelope P.val.2 lam ((N : ℝ) * ℓ.val) R
            |centralRep (observationLength ℓ) ((u - c : ℝ) : Circle (observationLength ℓ))|) →
        (c = 0 → ∃ hA : Integrable (anchoredSum ℓ N f) (gibbsMeasure P N),
            variance (gibbsMeasure P N) (anchoredSum ℓ N f) hA ≤
              ENNReal.ofReal (C * M ^ 2 * ((N : ℝ) * ℓ.val) ^ (ε + max (2 * lam) P.val.2))) ∧
        (∃ hB : Integrable (plainSum ℓ N f) (gibbsMeasure P N),
            variance (gibbsMeasure P N) (plainSum ℓ N f) hB ≤
              ENNReal.ofReal (C * M ^ 2 * ((N : ℝ) * ℓ.val) ^ (ε + max (2 * lam) P.val.2)))

end Riesz1.Internal

end
end
