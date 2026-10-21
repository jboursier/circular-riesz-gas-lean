/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Decomposition.Hahn
public import Mathlib.MeasureTheory.Measure.TotalVariation.Basic
public import Riesz1.ToMathlib.TotalVariation.Event

/-!
# Total variation between measures with densities

Let `ρ` be a measure on `Ω`, and let `p, q : Ω → ℝ` be measurable, nonnegative and integrable
for `ρ`. Put `μ = ρ.withDensity (ofReal ∘ p)` and `ν = ρ.withDensity (ofReal ∘ q)`. This file
proves:

* `(etvDist μ ν).toReal = ∫ |p - q| dρ`, with no normalization assumed.
* for probability measures `μ ν`, `(etvDist μ ν).toReal / 2 = 1 - ∫ min (p, q) dρ`.
* (forcing bound) if `ν = μ.withDensity (ofReal ∘ g)` with `∫ g dμ = 1`, and `g ≥ 1` on a
  measurable set `E`, then `(etvDist μ ν).toReal / 2 ≤ μ Eᶜ`.

The proofs use the Hahn set `{p ≤ q}` for the pair `μ, ν`. This set is where `μ ≤ ν`.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace Riesz1

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The mass of a measurable set under `ρ.withDensity (ofReal ∘ p)` is the integral of `p` over
that set, for a measurable nonnegative density `p`. -/
lemma measureReal_withDensity_ofReal_eq (ρ : Measure Ω) {p : Ω → ℝ} (hp : Measurable p)
    (hp0 : ∀ x, 0 ≤ p x) {s : Set Ω} (hs : MeasurableSet s) :
    (ρ.withDensity fun x => ENNReal.ofReal (p x)).real s = ∫ x in s, p x ∂ρ := by
  rw [withDensity_real_apply_eq_integral hp.ennreal_ofReal.aemeasurable.restrict
    (Filter.Eventually.of_forall fun _ _ => ENNReal.ofReal_lt_top) hs.nullMeasurableSet]
  exact setIntegral_congr_fun hs fun x _ => ENNReal.toReal_ofReal (hp0 x)

/-- Density form of the event distance: if `μ = ρ.withDensity (ofReal ∘ p)` and
`ν = ρ.withDensity (ofReal ∘ q)` with `p, q` measurable, nonnegative and `ρ`-integrable, then
`(etvDist μ ν).toReal = ∫ |p - q| dρ`. The Hahn set `{p ≤ q}` for `μ, ν` carries the sign of
`p - q` on each side, so the Hahn formula gives the integral of `|p - q|`. -/
theorem toReal_etvDist_eq_integral_abs (ρ μ ν : Measure Ω) {p q : Ω → ℝ} (hp : Measurable p)
    (hq : Measurable q) (hp0 : ∀ x, 0 ≤ p x) (hq0 : ∀ x, 0 ≤ q x) (hpi : Integrable p ρ)
    (hqi : Integrable q ρ) (hμ : μ = ρ.withDensity fun x => ENNReal.ofReal (p x))
    (hν : ν = ρ.withDensity fun x => ENNReal.ofReal (q x)) :
    (etvDist μ ν).toReal = ∫ x, |p x - q x| ∂ρ := by
  subst hμ hν
  have := isFiniteMeasure_withDensity_ofReal hpi.hasFiniteIntegral
  have := isFiniteMeasure_withDensity_ofReal hqi.hasFiniteIntegral
  have hs : MeasurableSet {x | p x ≤ q x} := measurableSet_le hp hq
  have hH : IsHahnDecomposition (ρ.withDensity fun x => ENNReal.ofReal (p x))
      (ρ.withDensity fun x => ENNReal.ofReal (q x)) {x | p x ≤ q x} :=
    { measurableSet := hs
      le_on := by
        rw [restrict_withDensity hs, restrict_withDensity hs]
        exact withDensity_mono (ae_restrict_of_forall_mem hs fun x hx =>
          ENNReal.ofReal_le_ofReal (show p x ≤ q x from hx))
      ge_on_compl := by
        rw [restrict_withDensity hs.compl, restrict_withDensity hs.compl]
        exact withDensity_mono (ae_restrict_of_forall_mem hs.compl fun x hx =>
          ENNReal.ofReal_le_ofReal (le_of_lt (not_le.mp hx))) }
  have htv := hH.tvDist_eq
  unfold tvDist at htv
  -- Replace each of the four masses by the integral of the density over the matching set.
  rw [htv, measureReal_withDensity_ofReal_eq ρ hq hq0 hs,
    measureReal_withDensity_ofReal_eq ρ hp hp0 hs,
    measureReal_withDensity_ofReal_eq ρ hp hp0 hs.compl,
    measureReal_withDensity_ofReal_eq ρ hq hq0 hs.compl]
  have hint : Integrable (fun x => |p x - q x|) ρ := (hpi.sub hqi).abs
  -- On `{p ≤ q}` the integrand is `q - p`, and on its complement it is `p - q`.
  have hon : ∫ x in {x | p x ≤ q x}, |p x - q x| ∂ρ = ∫ x in {x | p x ≤ q x}, (q x - p x) ∂ρ :=
    setIntegral_congr_fun hs fun x hx => by
      have h : p x ≤ q x := hx
      rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 h)]
  have hoff : ∫ x in {x | p x ≤ q x}ᶜ, |p x - q x| ∂ρ = ∫ x in {x | p x ≤ q x}ᶜ, (p x - q x) ∂ρ :=
    setIntegral_congr_fun hs.compl fun x hx => by
      have h : q x ≤ p x := le_of_lt (not_le.mp hx)
      rw [abs_of_nonneg (sub_nonneg.2 h)]
  rw [← integral_add_compl hs hint, hon, hoff, integral_sub hqi.integrableOn hpi.integrableOn,
    integral_sub hpi.integrableOn hqi.integrableOn]

/-- Probability form: if `μ = ρ.withDensity (ofReal ∘ p)` and `ν = ρ.withDensity (ofReal ∘ q)`
are probability measures, then `(etvDist μ ν).toReal / 2 = 1 - ∫ min (p, q) dρ`. The identity
`|a - b| = a + b - 2 min (a, b)` reduces the total variation to `∫ p + ∫ q - 2 ∫ min`, and both
`∫ p` and `∫ q` equal `1`. -/
theorem half_toReal_etvDist_eq_one_sub_integral_min (ρ μ ν : Measure Ω) {p q : Ω → ℝ}
    (hp : Measurable p) (hq : Measurable q) (hp0 : ∀ x, 0 ≤ p x) (hq0 : ∀ x, 0 ≤ q x)
    (hpi : Integrable p ρ) (hqi : Integrable q ρ)
    (hμ : μ = ρ.withDensity fun x => ENNReal.ofReal (p x))
    (hν : ν = ρ.withDensity fun x => ENNReal.ofReal (q x))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    (etvDist μ ν).toReal / 2 = 1 - ∫ x, min (p x) (q x) ∂ρ := by
  have hint := toReal_etvDist_eq_integral_abs ρ μ ν hp hq hp0 hq0 hpi hqi hμ hν
  have hp1 : ∫ x, p x ∂ρ = 1 := by
    rw [← setIntegral_univ, ← measureReal_withDensity_ofReal_eq ρ hp hp0 MeasurableSet.univ,
      ← hμ, probReal_univ]
  have hq1 : ∫ x, q x ∂ρ = 1 := by
    rw [← setIntegral_univ, ← measureReal_withDensity_ofReal_eq ρ hq hq0 MeasurableSet.univ,
      ← hν, probReal_univ]
  have hmin : Integrable (fun x => min (p x) (q x)) ρ := by
    refine Integrable.mono' hpi (hp.min hq).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hp0 x) (hq0 x))]
    exact min_le_left _ _
  have hpt : ∀ x, |p x - q x| = p x + q x - 2 * min (p x) (q x) := by
    intro x
    rcases le_total (p x) (q x) with h | h
    · rw [min_eq_left h, abs_of_nonpos (by linarith)]
      ring
    · rw [min_eq_right h, abs_of_nonneg (by linarith)]
      ring
  have hint2 : ∫ x, |p x - q x| ∂ρ = (∫ x, p x ∂ρ) + (∫ x, q x ∂ρ)
      - 2 * ∫ x, min (p x) (q x) ∂ρ := by
    have hsub : ∫ x, (p x + q x - 2 * min (p x) (q x)) ∂ρ
        = ∫ x, (p x + q x) ∂ρ - ∫ x, 2 * min (p x) (q x) ∂ρ :=
      integral_sub (hpi.add hqi) (hmin.const_mul 2)
    rw [integral_congr_ae (ae_of_all ρ hpt), hsub, integral_add hpi hqi, integral_const_mul]
  rw [hint, hint2, hp1, hq1]
  ring

/-- Forcing bound: let `μ` be a probability
measure on `Ω`, let `g : Ω → ℝ` be measurable and nonnegative with `∫ g dμ = 1`, and let
`ν = μ.withDensity (ofReal ∘ g)`. If `1 ≤ g x` for every `x` in a measurable set `E`, then
`(etvDist μ ν).toReal / 2 ≤ μ Eᶜ`. The density `ν` is again a probability measure, because its
total mass is `∫ g dμ = 1`. The proof bounds `∫ min (1, g) dμ` below by `μ E`. -/
theorem half_etvDist_le_measure_compl_of_one_le_on (μ ν : Measure Ω) [IsProbabilityMeasure μ]
    {g : Ω → ℝ} {E : Set Ω} (hg : Measurable g) (hg0 : ∀ x, 0 ≤ g x)
    (hg1 : ∫ x, g x ∂μ = 1) (hE : MeasurableSet E) (hgE : ∀ x ∈ E, 1 ≤ g x)
    (hν : ν = μ.withDensity fun x => ENNReal.ofReal (g x)) :
    (etvDist μ ν).toReal / 2 ≤ μ.real Eᶜ := by
  have hgi : Integrable g μ := Integrable.of_integral_ne_zero (by rw [hg1]; exact one_ne_zero)
  have hνuniv : ν univ = 1 := by
    rw [hν, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hgi (Filter.Eventually.of_forall hg0), hg1,
      ENNReal.ofReal_one]
  have : IsProbabilityMeasure ν := ⟨hνuniv⟩
  -- Write `μ` as the density `1` against itself, so the density formula applies to `(μ, ν)`.
  have hμeq : μ = μ.withDensity fun x => ENNReal.ofReal ((fun _ => (1 : ℝ)) x) := by
    simp
  have key := half_toReal_etvDist_eq_one_sub_integral_min μ μ ν measurable_const hg
    (fun _ => zero_le_one) hg0 (integrable_const 1) hgi hμeq hν
  -- The integrand `min (1, g)` is at least the indicator of `E`, because `g ≥ 1` on `E`.
  have hmin_int : Integrable (fun x => min (1 : ℝ) (g x)) μ := by
    refine Integrable.mono' (integrable_const (1 : ℝ))
      (measurable_const.min hg).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min zero_le_one (hg0 x))]
    exact min_le_left _ _
  have hEmass : μ.real E ≤ ∫ x, min (1 : ℝ) (g x) ∂μ := by
    have hind : ∫ x, E.indicator (fun _ => (1 : ℝ)) x ∂μ = μ.real E := by
      rw [integral_indicator hE, setIntegral_const, smul_eq_mul, mul_one]
    rw [← hind]
    refine integral_mono ((integrable_const (1 : ℝ)).indicator hE) hmin_int fun x => ?_
    by_cases hx : x ∈ E
    · simp [Set.indicator_of_mem hx, min_eq_left (hgE x hx)]
    · simp [hx, hg0 x]
  have hcompl : μ.real Eᶜ = 1 - μ.real E := probReal_compl_eq_one_sub hE
  linarith [key, hEmass, hcompl]

end Riesz1
