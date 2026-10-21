/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Rigidity.ForcingPotential
public import Riesz1.Gibbs.WellDefined
public import Riesz1.ToMathlib.TotalVariation.Density
public import Riesz1.ToMathlib.TotalVariation.Map

/-!
# Forcing-event comparison

Write `gibbsMeasure P N` for
the Gibbs law `P`, let `F = forcingPotential θ i0 L R` and let
`Q = constrainedLaw P N θ i0 L R` be the constrained law. The main result is `Riesz1.forcing_event_comparison`:

* `TV(P, Q) ≤ P(F > 0) ≤ P(S_{i0,L} > R)`, where `S_{i0,L}` is the block length.
* every event `A` depending only on the lifted block `π_I` satisfies `|P A - Q A| ≤ P(S_{i0,L} > R)`.
* the block laws satisfy the same bound in total variation.

The proof uses the abstract forcing bound `Riesz1.half_etvDist_le_measure_compl_of_one_le_on`. The
Gibbs law is a probability measure by `Riesz1.modelWellDefined`, and the density of `Q` with respect to
`P` is `z^{-1} exp (-β F)`, which is at least `1` on the event `{F = 0}`.

The statement assumes only `L < N`. The proof uses neither `1 ≤ L` nor `N ≥ 2`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace Riesz1

/-! ### Total variation -/

/-- The total variation distance `TV(μ, ν)`, for probability measures
`μ` and `ν`. Mathlib's total variation norm `etvDist μ ν` is twice this distance, so
`TV(μ, ν) = (etvDist μ ν).toReal / 2`. The supremum formula is `totalVariation_eq_sSup`. -/
noncomputable def totalVariation {Ω : Type*} [MeasurableSpace Ω] (μ ν : Measure Ω) : ℝ :=
  (etvDist μ ν).toReal / 2

/-- For probability measures, the total variation distance is the supremum of `|μ A - ν A|` over
the measurable events `A`. -/
theorem totalVariation_eq_sSup {Ω : Type*} [MeasurableSpace Ω] (μ ν : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    totalVariation μ ν = sSup ((fun A : Set Ω => |μ.real A - ν.real A|) '' {A | MeasurableSet A}) :=
  ((isLUB_abs_measureReal_sub_etvDist μ ν).csSup_eq ⟨_, ⟨∅, MeasurableSet.empty, rfl⟩⟩).symm

/-! ### The Gibbs law and the constrained law -/

/-- The Gibbs law of `N` particles is a probability measure, by `modelWellDefined`. -/
theorem isProbabilityMeasure_gibbsMeasure (P : Parameters) (N : ℕ+) :
    IsProbabilityMeasure (gibbsMeasure P N) :=
  (modelWellDefined P N).2.2

/-- The Boltzmann factor `exp (-β F_{I,R})` is at most one, since `β > 0` and `F_{I,R} ≥ 0`. -/
theorem exp_neg_forcingPotential_le_one (P : Parameters) {θ : ℝ → ℝ} (hθ : IsForcingCutoff θ)
    {R : ℝ} (hR : 0 < R) (N : ℕ+) (i0 : ℤ) (L : ℕ) (X : Configuration N) :
    Real.exp (-P.val.1 * forcingPotential θ i0 L R X) ≤ 1 := by
  rw [Real.exp_le_one_iff]
  have h := mul_nonneg P.property.1.le (forcingPotential_nonneg hθ hR i0 L X)
  linarith

/-- The Boltzmann factor `exp (-β F_{I,R})` is integrable under the Gibbs law. -/
theorem integrable_exp_neg_forcingPotential (P : Parameters) (N : ℕ+) {θ : ℝ → ℝ}
    (hθ : IsForcingCutoff θ) {R : ℝ} (hR : 0 < R) (i0 : ℤ) (L : ℕ) :
    Integrable (fun X : Configuration N => Real.exp (-P.val.1 * forcingPotential θ i0 L R X))
      (gibbsMeasure P N) := by
  have := isProbabilityMeasure_gibbsMeasure P N
  refine Integrable.mono' (integrable_const (1 : ℝ)) ?_ (ae_of_all _ fun X => ?_)
  · have hF : Measurable fun X : Configuration N => forcingPotential θ i0 L R X :=
      measurable_forcingPotential (N := N) hθ i0 L R
    exact (Real.continuous_exp.measurable.comp (hF.const_mul _)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact exp_neg_forcingPotential_le_one P hθ hR N i0 L X

/-- The normalizer `z_{I,R}` lies in `(0, 1]`. -/
theorem constrainedNormalizer_mem_Ioc (P : Parameters) (N : ℕ+) {θ : ℝ → ℝ}
    (hθ : IsForcingCutoff θ) {R : ℝ} (hR : 0 < R) (i0 : ℤ) (L : ℕ) :
    constrainedNormalizer P N θ i0 L R ∈ Set.Ioc (0 : ℝ) 1 := by
  have := isProbabilityMeasure_gibbsMeasure P N
  have hint := integrable_exp_neg_forcingPotential P N hθ hR i0 L
  constructor
  · unfold constrainedNormalizer
    rw [integral_pos_iff_support_of_nonneg (fun X => (Real.exp_pos _).le) hint]
    have hsupp : Function.support (fun X : Configuration N =>
        Real.exp (-P.val.1 * forcingPotential θ i0 L R X)) = univ :=
      Set.eq_univ_of_forall fun X => (Real.exp_pos _).ne'
    rw [hsupp, measure_univ]
    exact one_pos
  · unfold constrainedNormalizer
    have h := integral_mono hint (integrable_const (1 : ℝ))
      (fun X => exp_neg_forcingPotential_le_one P hθ hR N i0 L X)
    simpa using h

/-- The density `z_{I,R}^{-1} exp (-β F_{I,R})` of the constrained law integrates to one under the
Gibbs law. -/
theorem integral_constrainedDensity (P : Parameters) (N : ℕ+) {θ : ℝ → ℝ} (hθ : IsForcingCutoff θ)
    {R : ℝ} (hR : 0 < R) (i0 : ℤ) (L : ℕ) :
    ∫ X, (constrainedNormalizer P N θ i0 L R)⁻¹ *
      Real.exp (-P.val.1 * forcingPotential θ i0 L R X) ∂(gibbsMeasure P N) = 1 := by
  have hz := (constrainedNormalizer_mem_Ioc P N hθ hR i0 L).1
  rw [integral_const_mul]
  exact inv_mul_cancel₀ hz.ne'

/-- The constrained law `Q_{I,R}` is a probability measure. -/
theorem isProbabilityMeasure_constrainedLaw (P : Parameters) (N : ℕ+) {θ : ℝ → ℝ}
    (hθ : IsForcingCutoff θ) {R : ℝ} (hR : 0 < R) (i0 : ℤ) (L : ℕ) :
    IsProbabilityMeasure (constrainedLaw P N θ i0 L R) := by
  have := isProbabilityMeasure_gibbsMeasure P N
  have hz := (constrainedNormalizer_mem_Ioc P N hθ hR i0 L).1
  have hint := integrable_exp_neg_forcingPotential P N hθ hR i0 L
  have hg : Integrable (fun X : Configuration N => (constrainedNormalizer P N θ i0 L R)⁻¹ *
      Real.exp (-P.val.1 * forcingPotential θ i0 L R X)) (gibbsMeasure P N) :=
    hint.const_mul _
  have hnn : 0 ≤ᵐ[gibbsMeasure P N] fun X : Configuration N =>
      (constrainedNormalizer P N θ i0 L R)⁻¹ * Real.exp (-P.val.1 * forcingPotential θ i0 L R X) :=
    ae_of_all _ fun X => mul_nonneg (inv_nonneg.2 hz.le) (Real.exp_pos _).le
  constructor
  unfold constrainedLaw
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hg hnn, integral_constrainedDensity P N hθ hR i0 L,
    ENNReal.ofReal_one]

/-! ### The forcing-event comparison -/

/-- Forcing-event comparison. Let `P : Parameters` encode the pair
`(β, s)`, so that `gibbsMeasure P N` is the Gibbs law. Let `θ` be a forcing cutoff, let `i0 ∈ ℤ`,
let `L < N` be a natural number, and let `R > 0`. Put `I = [i0, i0 + L] ∩ ℤ`, let `F = forcingPotential θ i0 L R` and
let `Q = constrainedLaw P N θ i0 L R` be the constrained law of `I` and `R`. Let `π_I` be the
lifted block of `I`, and let `S_{i0,L} = blockLength · i0 L` be the block length. Then:

* `TV(P, Q) ≤ P(F > 0) ≤ P(S_{i0,L} > R)`.
* every event `π_I⁻¹ B` depending only on the block satisfies `|P(π_I⁻¹ B) - Q(π_I⁻¹ B)| ≤
  P(S_{i0,L} > R)`.
* the block laws `P ∘ π_I⁻¹` and `Q ∘ π_I⁻¹` satisfy `TV ≤ P(S_{i0,L} > R)`. -/
theorem forcing_event_comparison (P : Parameters) (N : ℕ+) (θ : ℝ → ℝ) (hθ : IsForcingCutoff θ)
    (i0 : ℤ) (L : ℕ) (hLN : L < (N : ℕ)) (R : ℝ) (hR : 0 < R) :
    totalVariation (gibbsMeasure P N) (constrainedLaw P N θ i0 L R) ≤
        (gibbsMeasure P N).real {X | 0 < forcingPotential θ i0 L R X} ∧
      (gibbsMeasure P N).real {X | 0 < forcingPotential θ i0 L R X} ≤
        (gibbsMeasure P N).real {X | R < blockLength X i0 L} ∧
      (∀ B : Set (Configuration (Nat.succPNat L)), MeasurableSet B →
        |(gibbsMeasure P N).real (liftedBlock i0 hLN ⁻¹' B) -
            (constrainedLaw P N θ i0 L R).real (liftedBlock i0 hLN ⁻¹' B)| ≤
          (gibbsMeasure P N).real {X | R < blockLength X i0 L}) ∧
      totalVariation ((gibbsMeasure P N).map (liftedBlock i0 hLN))
          ((constrainedLaw P N θ i0 L R).map (liftedBlock i0 hLN)) ≤
        (gibbsMeasure P N).real {X | R < blockLength X i0 L} := by
  have := isProbabilityMeasure_gibbsMeasure P N
  have := isProbabilityMeasure_constrainedLaw P N hθ hR i0 L
  have hFm : Measurable fun X : Configuration N => forcingPotential θ i0 L R X :=
    measurable_forcingPotential (N := N) hθ i0 L R
  have hz0 := (constrainedNormalizer_mem_Ioc P N hθ hR i0 L).1
  have hz1 := (constrainedNormalizer_mem_Ioc P N hθ hR i0 L).2
  -- The density `g = z^{-1} exp (-β F)` of `Q` with respect to `P`.
  have hgm : Measurable fun X : Configuration N =>
      (constrainedNormalizer P N θ i0 L R)⁻¹ * Real.exp (-P.val.1 * forcingPotential θ i0 L R X) :=
    measurable_const.mul (Real.continuous_exp.measurable.comp (hFm.const_mul _))
  have hg0 : ∀ X : Configuration N,
      0 ≤ (constrainedNormalizer P N θ i0 L R)⁻¹ *
        Real.exp (-P.val.1 * forcingPotential θ i0 L R X) :=
    fun X => mul_nonneg (inv_nonneg.2 hz0.le) (Real.exp_pos _).le
  have hg1 := integral_constrainedDensity P N hθ hR i0 L
  -- On the event `E = {F = 0}`, the density is `z^{-1} ≥ 1`.
  have hE : MeasurableSet {X : Configuration N | forcingPotential θ i0 L R X = 0} :=
    hFm (measurableSet_singleton 0)
  have hgE : ∀ X ∈ {X : Configuration N | forcingPotential θ i0 L R X = 0},
      1 ≤ (constrainedNormalizer P N θ i0 L R)⁻¹ *
        Real.exp (-P.val.1 * forcingPotential θ i0 L R X) := by
    intro X hX
    have hX' : forcingPotential θ i0 L R X = 0 := hX
    rw [hX', mul_zero, Real.exp_zero, mul_one]
    exact (one_le_inv₀ hz0).2 hz1
  have key := half_etvDist_le_measure_compl_of_one_le_on (gibbsMeasure P N)
    (constrainedLaw P N θ i0 L R) hgm hg0 hg1 hE hgE rfl
  -- The complement of `E` is the event `{F > 0}`, since `F ≥ 0`.
  have hcompl : {X : Configuration N | forcingPotential θ i0 L R X = 0}ᶜ =
      {X : Configuration N | 0 < forcingPotential θ i0 L R X} := by
    ext X
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq]
    exact ⟨fun h => lt_of_le_of_ne (forcingPotential_nonneg hθ hR i0 L X) (Ne.symm h),
      fun h => h.ne'⟩
  rw [hcompl] at key
  have h1 : totalVariation (gibbsMeasure P N) (constrainedLaw P N θ i0 L R) ≤
      (gibbsMeasure P N).real {X | 0 < forcingPotential θ i0 L R X} := key
  -- The event `{F > 0}` lies in `{S > R}`.
  have h2 : (gibbsMeasure P N).real {X | 0 < forcingPotential θ i0 L R X} ≤
      (gibbsMeasure P N).real {X | R < blockLength X i0 L} :=
    measureReal_mono fun X hX => blockLength_gt_of_forcingPotential_pos hθ hR i0 L X hX
  refine ⟨h1, h2, fun B hB => ?_, ?_⟩
  · exact (abs_measureReal_sub_le_etvDist_div_two (gibbsMeasure P N) (constrainedLaw P N θ i0 L R)
      (measurable_liftedBlock (N := N) i0 hLN hB)).trans (h1.trans h2)
  · have hπ : Measurable (liftedBlock (N := N) i0 hLN) := measurable_liftedBlock i0 hLN
    have hmap := etvDist_map_le_etvDist (gibbsMeasure P N) (constrainedLaw P N θ i0 L R) hπ
    have hfin : etvDist (gibbsMeasure P N) (constrainedLaw P N θ i0 L R) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofNat_ne_top
        (etvDist_le_two (gibbsMeasure P N) (constrainedLaw P N θ i0 L R))
    have hreal := ENNReal.toReal_mono hfin hmap
    have hTV := h1.trans h2
    unfold totalVariation at hTV ⊢
    linarith

end Riesz1

end
