/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.Window
public import Riesz1.Rigidity.ForcingComparison
public import Riesz1.Rigidity.Gaps
public import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue

/-!
# The nearest-neighbour forcing and its convexified law

Let `I = I_γ` be the window of `Riesz1.window`, and let `θ` be a smooth
forcing cutoff. The nearest-neighbour forcing is
`F_{ε,γ}(X) = ∑_{i, i+1 ∈ I} θ (N (x_{i+1} - x_i) / K^ε)`, and the convexified law is
`dQ = z^{-1} exp (-β F_{ε,γ}) dP` with `z = E_P[exp (-β F_{ε,γ})]`.

* `nearestForcing` is `F_{ε,γ}`. Its summands are the cutoff at the gap `N (x_{i+1} - x_i)`, for
  the pairs `(i, i+1)` of `nearestPairs`.
* `forcedNormalizer` and `forcedLaw` are the normalizer and the law of a general nonnegative forcing
  `G`. `nearestLaw` is `forcedLaw` at `G = nearestForcing`.
* `anchorMap` is the anchoring map `Anch_N` of Definition 3.8, and `nearestAnchoredLaw` is
  the anchored image `Anch_N # Q`.

The normalizer lies in `(0, 1]`, so `nearestLaw` is a probability measure
(`isProbabilityMeasure_forcedLaw`). The total variation between the Gibbs law and `forcedLaw` is at
most the probability that the forcing is positive (`totalVariation_forcedLaw_le`), and this event
lies in the union of the events `{K^ε < N (x_{i+1} - x_i)}` over the pairs
(`measureReal_nearestForcing_pos_le`).
-/

@[expose] public section

open MeasureTheory Set Finset

namespace Riesz1

variable {N : ℕ+}

/-! ### The nearest-neighbour forcing -/

/-- The nearest-neighbour forcing `F_{ε,γ}`, for the cutoff `θ`, the
scale `K`, the exponent `γ` and the exponent `ε`: the sum of `θ (N (x_{i+1} - x_i) / K^ε)` over the
nearest-neighbour pairs `(i, i+1)` of the window `I_γ`. -/
noncomputable def nearestForcing (θ : ℝ → ℝ) (N : ℕ+) (K γ ε : ℝ) (X : Configuration N) : ℝ :=
  ∑ i ∈ nearestPairs N (window N K γ), θ (gap X ((i : ℕ) : ℤ) / K ^ ε)

/-- The normalizer `z = E_P[exp (-β G)]` of a forcing `G` on the Gibbs law of `N` particles, with
`β = P.val.1`. -/
noncomputable def forcedNormalizer (P : Parameters) (N : ℕ+) (G : Configuration N → ℝ) : ℝ :=
  ∫ X, Real.exp (-P.val.1 * G X) ∂(gibbsMeasure P N)

/-- The law `dQ = z^{-1} exp (-β G) dP` of a forcing `G` on the Gibbs law of `N` particles. -/
noncomputable def forcedLaw (P : Parameters) (N : ℕ+) (G : Configuration N → ℝ) :
    Measure (Configuration N) :=
  (gibbsMeasure P N).withDensity fun X =>
    ENNReal.ofReal ((forcedNormalizer P N G)⁻¹ * Real.exp (-P.val.1 * G X))

/-- The nearest-neighbour law `Q`: the law `forcedLaw` of the forcing
`F_{ε,γ}`. -/
noncomputable def nearestLaw (P : Parameters) (θ : ℝ → ℝ) (N : ℕ+) (K γ ε : ℝ) :
    Measure (Configuration N) :=
  forcedLaw P N (nearestForcing θ N K γ ε)

/-- The anchoring map `Anch_N(x) = (x_2 - x_1, …, x_N - x_1)` of Definition 3.8. The paper's
coordinate `x_{j+1}` is the cyclic lift at the index `j`, so coordinate `j` of the map is
`x_{j+1} - x_0` for `j < N - 1`. -/
noncomputable def anchorMap (N : ℕ+) (X : Configuration N) : Fin ((N : ℕ) - 1) → ℝ :=
  fun j => cyclicLift X (((j : ℕ) : ℤ) + 1) - cyclicLift X 0

/-- The anchored image `Anch_N # Q` of the nearest-neighbour law. -/
noncomputable def nearestAnchoredLaw (P : Parameters) (θ : ℝ → ℝ) (N : ℕ+) (K γ ε : ℝ) :
    Measure (Fin ((N : ℕ) - 1) → ℝ) :=
  (nearestLaw P θ N K γ ε).map (anchorMap N)

/-! ### General nonnegative forcings -/

section Forced

variable {P : Parameters} {G : Configuration N → ℝ}

/-- The Boltzmann factor `exp (-β G)` is at most one when `G ≥ 0`. -/
theorem exp_neg_mul_le_one (hG0 : ∀ X, 0 ≤ G X) (X : Configuration N) :
    Real.exp (-P.val.1 * G X) ≤ 1 := by
  rw [Real.exp_le_one_iff]
  have h := mul_nonneg P.property.1.le (hG0 X)
  linarith

/-- The Boltzmann factor `exp (-β G)` is measurable when `G` is. -/
theorem measurable_exp_neg (hG : Measurable G) :
    Measurable fun X => Real.exp (-P.val.1 * G X) :=
  Real.continuous_exp.measurable.comp (hG.const_mul _)

/-- The Boltzmann factor `exp (-β G)` is integrable under the Gibbs law. -/
theorem integrable_exp_neg (hG : Measurable G) (hG0 : ∀ X, 0 ≤ G X) :
    Integrable (fun X => Real.exp (-P.val.1 * G X)) (gibbsMeasure P N) := by
  have := isProbabilityMeasure_gibbsMeasure P N
  refine Integrable.mono' (integrable_const (1 : ℝ)) (measurable_exp_neg hG).aestronglyMeasurable
    (ae_of_all _ fun X => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact exp_neg_mul_le_one hG0 X

/-- The normalizer lies in `(0, 1]`: the integrand is positive and at most one. -/
theorem forcedNormalizer_mem_Ioc (hG : Measurable G) (hG0 : ∀ X, 0 ≤ G X) :
    forcedNormalizer P N G ∈ Ioc (0 : ℝ) 1 := by
  have := isProbabilityMeasure_gibbsMeasure P N
  have hint := integrable_exp_neg (P := P) hG hG0
  constructor
  · unfold forcedNormalizer
    rw [integral_pos_iff_support_of_nonneg (fun X => (Real.exp_pos _).le) hint]
    have hsupp : Function.support (fun X : Configuration N => Real.exp (-P.val.1 * G X)) = univ :=
      Set.eq_univ_of_forall fun X => (Real.exp_pos _).ne'
    rw [hsupp, measure_univ]
    exact one_pos
  · unfold forcedNormalizer
    have h := integral_mono hint (integrable_const (1 : ℝ)) (fun X => exp_neg_mul_le_one hG0 X)
    simpa using h

/-- The density `z^{-1} exp (-β G)` of `forcedLaw` integrates to one under the Gibbs law. -/
theorem integral_forcedDensity (hG : Measurable G) (hG0 : ∀ X, 0 ≤ G X) :
    ∫ X, (forcedNormalizer P N G)⁻¹ * Real.exp (-P.val.1 * G X) ∂(gibbsMeasure P N) = 1 := by
  have hz := (forcedNormalizer_mem_Ioc (P := P) hG hG0).1
  rw [integral_const_mul]
  exact inv_mul_cancel₀ hz.ne'

/-- The forced law is a probability measure. -/
theorem isProbabilityMeasure_forcedLaw (hG : Measurable G) (hG0 : ∀ X, 0 ≤ G X) :
    IsProbabilityMeasure (forcedLaw P N G) := by
  have := isProbabilityMeasure_gibbsMeasure P N
  have hint := integrable_exp_neg (P := P) hG hG0
  have hz := (forcedNormalizer_mem_Ioc (P := P) hG hG0).1
  have hg : Integrable (fun X => (forcedNormalizer P N G)⁻¹ * Real.exp (-P.val.1 * G X))
      (gibbsMeasure P N) :=
    hint.const_mul _
  have hnn : 0 ≤ᵐ[gibbsMeasure P N] fun X =>
      (forcedNormalizer P N G)⁻¹ * Real.exp (-P.val.1 * G X) :=
    ae_of_all _ fun X => mul_nonneg (inv_nonneg.2 hz.le) (Real.exp_pos _).le
  constructor
  unfold forcedLaw
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hg hnn, integral_forcedDensity hG hG0, ENNReal.ofReal_one]

/-- Forcing-event comparison for a general nonnegative forcing: the total variation between the
Gibbs law and `forcedLaw` is at most the Gibbs probability that the forcing is positive. It is
the abstract bound for the event `E = {G = 0}`. -/
theorem totalVariation_forcedLaw_le (hG : Measurable G) (hG0 : ∀ X, 0 ≤ G X) :
    totalVariation (gibbsMeasure P N) (forcedLaw P N G) ≤
      (gibbsMeasure P N).real {X | 0 < G X} := by
  have := isProbabilityMeasure_gibbsMeasure P N
  have hz := forcedNormalizer_mem_Ioc (P := P) hG hG0
  have hgm : Measurable fun X => (forcedNormalizer P N G)⁻¹ * Real.exp (-P.val.1 * G X) :=
    measurable_const.mul (measurable_exp_neg hG)
  have hg0 : ∀ X, 0 ≤ (forcedNormalizer P N G)⁻¹ * Real.exp (-P.val.1 * G X) :=
    fun X => mul_nonneg (inv_nonneg.2 hz.1.le) (Real.exp_pos _).le
  have hE : MeasurableSet {X : Configuration N | G X = 0} := hG (measurableSet_singleton 0)
  have hgE : ∀ X ∈ {X : Configuration N | G X = 0},
      1 ≤ (forcedNormalizer P N G)⁻¹ * Real.exp (-P.val.1 * G X) := by
    intro X hX
    have hX' : G X = 0 := hX
    rw [hX', mul_zero, Real.exp_zero, mul_one]
    exact (one_le_inv₀ hz.1).2 hz.2
  have key := half_etvDist_le_measure_compl_of_one_le_on (gibbsMeasure P N) (forcedLaw P N G)
    hgm hg0 (integral_forcedDensity hG hG0) hE hgE rfl
  have hcompl : {X : Configuration N | G X = 0}ᶜ = {X | 0 < G X} := by
    ext X
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq]
    exact ⟨fun h => lt_of_le_of_ne (hG0 X) (Ne.symm h), fun h => h.ne'⟩
  rw [hcompl] at key
  unfold totalVariation
  exact key

/-- The Radon–Nikodym derivative of `forcedLaw` with respect to the Gibbs law is the density
`z^{-1} exp (-β G)`, almost everywhere. -/
theorem rnDeriv_forcedLaw_ae (hG : Measurable G) :
    (forcedLaw P N G).rnDeriv (gibbsMeasure P N) =ᵐ[gibbsMeasure P N]
      fun X => ENNReal.ofReal ((forcedNormalizer P N G)⁻¹ * Real.exp (-P.val.1 * G X)) := by
  have := isProbabilityMeasure_gibbsMeasure P N
  have hgm : Measurable fun X => (forcedNormalizer P N G)⁻¹ * Real.exp (-P.val.1 * G X) :=
    measurable_const.mul (measurable_exp_neg hG)
  exact Measure.rnDeriv_withDensity _ hgm.ennreal_ofReal

/-- If the normalizer is at least one half, the density of `forcedLaw` is at most two almost
everywhere. -/
theorem ae_rnDeriv_forcedLaw_le_two (hG : Measurable G) (hG0 : ∀ X, 0 ≤ G X)
    (hz : 1 / 2 ≤ forcedNormalizer P N G) :
    ∀ᵐ X ∂(gibbsMeasure P N), (forcedLaw P N G).rnDeriv (gibbsMeasure P N) X ≤ 2 := by
  filter_upwards [rnDeriv_forcedLaw_ae (P := P) hG] with X hX
  rw [hX]
  have hzpos : (0 : ℝ) < forcedNormalizer P N G := lt_of_lt_of_le (by norm_num) hz
  have hinv : (forcedNormalizer P N G)⁻¹ ≤ 2 := by
    have h := inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 2) hz
    norm_num at h
    exact h
  have hval : (forcedNormalizer P N G)⁻¹ * Real.exp (-P.val.1 * G X) ≤ 2 := by
    calc (forcedNormalizer P N G)⁻¹ * Real.exp (-P.val.1 * G X)
        ≤ (forcedNormalizer P N G)⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left (exp_neg_mul_le_one hG0 X) (inv_nonneg.2 hzpos.le)
      _ ≤ 2 := by rw [mul_one]; exact hinv
  calc ENNReal.ofReal ((forcedNormalizer P N G)⁻¹ * Real.exp (-P.val.1 * G X))
      ≤ ENNReal.ofReal 2 := ENNReal.ofReal_le_ofReal hval
    _ = 2 := by simp

/-- The normalizer is at least one half when the forcing is positive with probability at most one
half. The integrand is at least the indicator of `{G = 0}`, whose integral is `1 - P(G > 0)`. -/
theorem half_le_forcedNormalizer (hG : Measurable G) (hG0 : ∀ X, 0 ≤ G X)
    (h : (gibbsMeasure P N).real {X | 0 < G X} ≤ 1 / 2) :
    1 / 2 ≤ forcedNormalizer P N G := by
  have := isProbabilityMeasure_gibbsMeasure P N
  have hE : MeasurableSet {X : Configuration N | G X = 0} := hG (measurableSet_singleton 0)
  have hpos : MeasurableSet {X : Configuration N | 0 < G X} :=
    measurableSet_lt measurable_const hG
  have hle : ∫ X, Set.indicator {X : Configuration N | G X = 0} 1 X ∂(gibbsMeasure P N) ≤
      ∫ X, Real.exp (-P.val.1 * G X) ∂(gibbsMeasure P N) := by
    refine integral_mono ?_ (integrable_exp_neg hG hG0) fun X => ?_
    · exact (integrable_const (1 : ℝ)).indicator hE
    · by_cases hX : G X = 0
      · rw [Set.indicator_of_mem (show X ∈ {X : Configuration N | G X = 0} from hX), hX,
          mul_zero, Real.exp_zero]
        rfl
      · rw [Set.indicator_of_notMem (show X ∉ {X : Configuration N | G X = 0} from hX)]
        exact (Real.exp_pos _).le
  have hind : ∫ X, Set.indicator {X : Configuration N | G X = 0} 1 X ∂(gibbsMeasure P N) =
      (gibbsMeasure P N).real {X | G X = 0} := integral_indicator_one hE
  have hcompl : (gibbsMeasure P N).real {X : Configuration N | G X = 0} =
      1 - (gibbsMeasure P N).real {X | 0 < G X} := by
    have hset : {X : Configuration N | G X = 0} = {X | 0 < G X}ᶜ := by
      ext X
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq]
      exact ⟨fun h => by rw [h]; exact lt_irrefl _,
        fun h => le_antisymm (not_lt.1 h) (hG0 X)⟩
    rw [hset, probReal_compl_eq_one_sub hpos]
  unfold forcedNormalizer
  linarith

end Forced

/-! ### The nearest-neighbour forcing -/

section Nearest

variable {P : Parameters} {θ : ℝ → ℝ} {K γ ε : ℝ}

/-- The nearest-neighbour forcing is nonnegative when `K > 0`, since the cutoff is nonnegative on
`[0, ∞)` and every gap is positive. -/
theorem nearestForcing_nonneg (hθ : IsForcingCutoff θ) (hK : 0 < K) (X : Configuration N) :
    0 ≤ nearestForcing θ N K γ ε X :=
  Finset.sum_nonneg fun _ _ => hθ.2.2.1 _
    (div_nonneg (gap_pos X _).le (Real.rpow_pos_of_pos hK ε).le)

/-- The nearest-neighbour forcing is measurable. -/
theorem measurable_nearestForcing (hθ : IsForcingCutoff θ) :
    Measurable (nearestForcing θ N K γ ε) :=
  Finset.measurable_sum _ fun _ _ =>
    (hθ.1.continuous.measurable).comp ((measurable_gap _).div_const _)

/-- The nearest-neighbour forcing vanishes when every pair has gap at most `K^ε`: each summand is
the cutoff at a point of `[0, 1]`. -/
theorem nearestForcing_eq_zero (hθ : IsForcingCutoff θ) (hK : 0 < K) (X : Configuration N)
    (h : ∀ i ∈ nearestPairs N (window N K γ), gap X ((i : ℕ) : ℤ) ≤ K ^ ε) :
    nearestForcing θ N K γ ε X = 0 := by
  unfold nearestForcing
  refine Finset.sum_eq_zero fun i hi => hθ.2.1 _ ⟨?_, ?_⟩
  · exact div_nonneg (gap_pos X _).le (Real.rpow_pos_of_pos hK ε).le
  · exact (div_le_one (Real.rpow_pos_of_pos hK ε)).2 (h i hi)

/-- The event `{F > 0}` of the nearest-neighbour forcing is covered by the events
`{K^ε < N (x_{i+1} - x_i)}` over the nearest-neighbour pairs. Under the single-gap tail bound
`hTail`, its probability is at most the number of pairs times the tail at `K^ε`. This is the
union bound of Lemma 5.2, with the gap tail as an explicit input. -/
theorem measureReal_nearestForcing_pos_le (hθ : IsForcingCutoff θ) (hK : 0 < K) {A a : ℝ}
    (hTail : ∀ (j : ℤ) (u : ℝ), (gibbsMeasure P N).real {X | u < gap X j} ≤
      A * Real.exp (-a * u)) :
    (gibbsMeasure P N).real {X | 0 < nearestForcing θ N K γ ε X} ≤
      ((nearestPairs N (window N K γ)).card : ℝ) * (A * Real.exp (-a * K ^ ε)) := by
  have := isProbabilityMeasure_gibbsMeasure (P := P) N
  have hsub : {X : Configuration N | 0 < nearestForcing θ N K γ ε X} ⊆
      ⋃ i ∈ nearestPairs N (window N K γ), {X | K ^ ε < gap X ((i : ℕ) : ℤ)} := by
    intro X hX
    by_contra hcon
    simp only [mem_iUnion, mem_ofPred_eq, not_exists, not_lt] at hcon
    have h0 := nearestForcing_eq_zero hθ hK X (fun i hi => hcon i hi)
    have hX' : 0 < nearestForcing θ N K γ ε X := hX
    linarith
  calc (gibbsMeasure P N).real {X | 0 < nearestForcing θ N K γ ε X}
      ≤ (gibbsMeasure P N).real (⋃ i ∈ nearestPairs N (window N K γ),
          {X | K ^ ε < gap X ((i : ℕ) : ℤ)}) :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ i ∈ nearestPairs N (window N K γ),
          (gibbsMeasure P N).real {X | K ^ ε < gap X ((i : ℕ) : ℤ)} :=
        measureReal_biUnion_finset_le _ _
    _ ≤ ∑ i ∈ nearestPairs N (window N K γ), A * Real.exp (-a * K ^ ε) :=
        Finset.sum_le_sum fun _ _ => hTail _ _
    _ = ((nearestPairs N (window N K γ)).card : ℝ) * (A * Real.exp (-a * K ^ ε)) := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- Total variation of the nearest-neighbour law, under the single-gap tail bound `hTail`: it is
at most `8 K^γ` times the tail at `K^ε`, since the window has at most `8 K^γ` pairs. -/
theorem totalVariation_nearestLaw_le (hθ : IsForcingCutoff θ) {A a : ℝ} (hK : 1 ≤ K)
    (hγ : 0 ≤ γ) (hA : 0 ≤ A)
    (hTail : ∀ (j : ℤ) (u : ℝ), (gibbsMeasure P N).real {X | u < gap X j} ≤
      A * Real.exp (-a * u)) :
    totalVariation (gibbsMeasure P N) (nearestLaw P θ N K γ ε) ≤
      8 * K ^ γ * (A * Real.exp (-a * K ^ ε)) := by
  have hK0 : 0 < K := by linarith
  have h1 := totalVariation_forcedLaw_le (P := P)
    (measurable_nearestForcing (N := N) (K := K) (γ := γ) (ε := ε) hθ)
    (nearestForcing_nonneg (N := N) (γ := γ) (ε := ε) hθ hK0)
  have h2 := measureReal_nearestForcing_pos_le (γ := γ) (ε := ε) hθ hK0 hTail
  have h3 := card_nearestPairs_window_le (N := N) (γ := γ) hK hγ
  have hnn : 0 ≤ A * Real.exp (-a * K ^ ε) := mul_nonneg hA (Real.exp_pos _).le
  unfold nearestLaw
  calc totalVariation (gibbsMeasure P N) (forcedLaw P N (nearestForcing θ N K γ ε))
      ≤ (gibbsMeasure P N).real {X | 0 < nearestForcing θ N K γ ε X} := h1
    _ ≤ ((nearestPairs N (window N K γ)).card : ℝ) * (A * Real.exp (-a * K ^ ε)) := h2
    _ ≤ 8 * K ^ γ * (A * Real.exp (-a * K ^ ε)) :=
        mul_le_mul_of_nonneg_right h3 hnn

/-- The normalizer of the nearest-neighbour law lies in `(0, 1]`.
The integrand is positive and at most one. -/
theorem nearestNormalizer_mem_Ioc (hθ : IsForcingCutoff θ) (hK : 0 < K) :
    forcedNormalizer P N (nearestForcing θ N K γ ε) ∈ Ioc (0 : ℝ) 1 :=
  forcedNormalizer_mem_Ioc (measurable_nearestForcing hθ) (nearestForcing_nonneg hθ hK)

/-- The nearest-neighbour law `Q` is a probability measure. -/
theorem isProbabilityMeasure_nearestLaw (hθ : IsForcingCutoff θ) (hK : 0 < K) :
    IsProbabilityMeasure (nearestLaw P θ N K γ ε) :=
  isProbabilityMeasure_forcedLaw (measurable_nearestForcing hθ) (nearestForcing_nonneg hθ hK)

end Nearest

/-! ### The anchored image -/

/-- The anchoring map is measurable: each coordinate is a difference of cyclic lifts. -/
theorem measurable_anchorMap (N : ℕ+) : Measurable (anchorMap N) :=
  Measurable.of_eval fun _ => (measurable_cyclicLift _).sub (measurable_cyclicLift _)

/-- The anchored image `Anch_N # Q` is a probability measure. -/
theorem isProbabilityMeasure_nearestAnchoredLaw (P : Parameters) (θ : ℝ → ℝ) (N : ℕ+) (K γ ε : ℝ)
    (hθ : IsForcingCutoff θ) (hK : 0 < K) :
    IsProbabilityMeasure (nearestAnchoredLaw P θ N K γ ε) := by
  have := isProbabilityMeasure_nearestLaw (P := P) (N := N) (γ := γ) (ε := ε) hθ hK
  unfold nearestAnchoredLaw
  exact (Measure.isProbabilityMeasure_map_iff (measurable_anchorMap N).aemeasurable).2 this

end Riesz1

end
