/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.APrioriRotationOriginL2
public import Riesz1.Variance.APrioriRotationTranslationPoint
public import Riesz1.CLT.GapsDiscSelectedCount
public import Riesz1.ToMathlib.VarianceTwoErrors

/-!
# Relabelling the spatial-origin statistic

The exact decomposition and the size-biased marginal used in the unanchored
assertion of Lemma 5.2. All coordinates and measures are those of the rotation part of
Lemma 5.2 and of the translation error `translationError`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Finset
open scoped ENNReal

namespace Riesz1.Internal

/-- The preceding label at the spatial origin is measurable, including
configurations with a particle exactly at zero. -/
theorem measurable_originLabel (N : ℕ+) :
    Measurable (originLabel : Configuration N → ℤ) := by
  refine measurable_to_countable' fun j => ?_
  have he : (originLabel : Configuration N → ℤ) ⁻¹' {j} =
      {X | cyclicLift X j ≤ 0 ∧ 0 < cyclicLift X (j + 1)} := by
    ext X
    exact preceding_eq_iff X le_rfl zero_lt_one j
  rw [he]
  exact (measurableSet_le (measurable_cyclicLift j) measurable_const).inter
    (measurableSet_lt measurable_const (measurable_cyclicLift (j + 1)))

/-- Evaluation of the cyclic lift at the preceding label is measurable. -/
theorem measurable_originLift (N : ℕ+) (j : ℤ) :
    Measurable (fun X : Configuration N => cyclicLift X (originLabel X + j)) := by
  have hm : Measurable (fun p : Configuration N × ℤ => cyclicLift p.1 (p.2 + j)) :=
    measurable_from_prod_countable_left fun k => measurable_cyclicLift (k + j)
  exact hm.comp (measurable_id.prodMk (measurable_originLabel N))

/-- The actual microscopic offset is measurable. -/
theorem measurable_originD (N : ℕ+) : Measurable (originD : Configuration N → ℝ) := by
  change Measurable (fun X : Configuration N => -((N : ℕ) : ℝ) *
    cyclicLift X (originLabel X))
  simpa only [Pi.mul_apply, add_zero] using
    (measurable_originLift N 0).const_mul (-((N : ℕ) : ℝ))

/-- The relabelled anchored positions are measurable. -/
theorem measurable_originPos (N : ℕ+) :
    Measurable (originPos : Configuration N → (Fin (N : ℕ) → ℝ)) := by
  refine measurable_pi_iff.mpr fun i => ?_
  change Measurable (fun X : Configuration N =>
    cyclicLift X (originLabel X + (i : ℕ)) - cyclicLift X (originLabel X))
  have h0 : Measurable (fun X : Configuration N => cyclicLift X (originLabel X)) := by
    simpa only [add_zero] using measurable_originLift N 0
  exact (measurable_originLift N (i : ℕ)).sub h0

/-- Periodicity removes the integer shifts of cyclic real lifts. -/
theorem sum_periodic_cyclicLift {N : ℕ+} {ℓ : ℝ}
    {f : ℝ → ℝ} (hper : Function.Periodic f (1 / ℓ))
    (X : Configuration N) (j : ℤ) :
    ∑ i : Fin (N : ℕ), f (cyclicLift X (j + (i : ℕ)) / ℓ) =
      ∑ i : Fin (N : ℕ), f (X.val i / ℓ) := by
  have hp : ∀ k : ℤ, f (cyclicLift X (k + (N : ℕ)) / ℓ) =
      f (cyclicLift X k / ℓ) := by
    intro k
    rw [cyclicLift_add_N, add_div]
    exact hper _
  have hs := selCnt_sum_shift_invariant
    (fun k : ℤ => f (cyclicLift X k / ℓ)) (N : ℕ) hp j
  rw [← Fin.sum_univ_eq_sum_range, ← Fin.sum_univ_eq_sum_range] at hs
  exact hs.trans (Finset.sum_congr rfl fun i _ => by rw [cyclicLift_natCast])

/-- The full plain sum is the localized anchored sum at the preceding
particle, plus the translation error and joint exterior sum.
This identity holds pointwise, including the zero-offset endpoint. -/
theorem plain_sum_eq_origin_decomposition {N : ℕ+} {ℓ : ℝ} (hℓ : ℓ ≠ 0)
    (γ : ℝ) {f : ℝ → ℝ} (hper : Function.Periodic f (1 / ℓ))
    (X : Configuration N) :
    (∑ i : Fin (N : ℕ), f (X.val i / ℓ)) =
      (∑ i ∈ window N ((N : ℝ) * ℓ) γ, f (originPos X i / ℓ)) +
        translationError N ℓ γ f (originD X) (originPos X) +
        jointExteriorSum N ℓ γ f (originD X) (originPos X) := by
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast N.ne_zero
  have he (i : Fin (N : ℕ)) :
      ((N : ℝ) * originPos X i - originD X) / ((N : ℝ) * ℓ) =
        cyclicLift X (originLabel X + (i : ℕ)) / ℓ := by
    unfold originPos originD
    field_simp
    ring
  rw [← sum_periodic_cyclicLift hper X (originLabel X)]
  unfold translationError jointExteriorSum
  simp_rw [he]
  have hs := Finset.sum_add_sum_compl (window N ((N : ℝ) * ℓ) γ)
    (fun i => f (cyclicLift X (originLabel X + (i : ℕ)) / ℓ))
  linarith only [hs]

/-- The preceding-particle positions have exactly the actual size-biased
anchored law. This is a marginal of the joint law. -/
theorem map_originPos_eq_sizeBiased (P : Parameters) (N : ℕ+)
    (hN : 2 ≤ (N : ℕ)) :
    (gibbsMeasure P N).map originPos =
      (rotAnchoredLaw P N).withDensity
        (fun y => ENNReal.ofReal (sizeBiasWeight N hN y)) := by
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (measurable_originPos N) hs, withDensity_apply _ hs]
  let φ : ℝ → (Fin (N : ℕ) → ℝ) → ℝ≥0∞ := fun _ y => s.indicator 1 y
  have hφ : Measurable (fun p : ℝ × (Fin (N : ℕ) → ℝ) => φ p.1 p.2) :=
    (measurable_const.indicator hs).comp measurable_snd
  have hj := joint_law_rotAnchoredLaw P N hN φ hφ
  have hl : ∫⁻ X, φ (originD X) (originPos X) ∂gibbsMeasure P N =
      gibbsMeasure P N (originPos ⁻¹' s) := by
    change ∫⁻ X, s.indicator 1 (originPos X) ∂gibbsMeasure P N = _
    have he : (fun X : Configuration N =>
        s.indicator (1 : (Fin (N : ℕ) → ℝ) → ℝ≥0∞) (originPos X)) =
        (originPos ⁻¹' s).indicator 1 := by
      funext X
      by_cases hx : originPos X ∈ s <;> simp [hx]
    rw [he, lintegral_indicator (hs.preimage (measurable_originPos N))]
    simp
  have hr : ∀ y : Fin (N : ℕ) → ℝ,
      (∫⁻ D in Ioo (0 : ℝ) (sizeBiasWeight N hN y), φ D y) =
        s.indicator (fun y => ENNReal.ofReal (sizeBiasWeight N hN y)) y := by
    intro y
    by_cases hy : y ∈ s
    · simp [φ, hy, Real.volume_Ioo]
    · simp [φ, hy]
  rw [hl, lintegral_congr hr, lintegral_indicator hs] at hj
  exact hj

/-- The actual size-biased anchored law is a probability. -/
theorem isProbabilityMeasure_sizeBiased_rotAnchoredLaw (P : Parameters)
    (N : ℕ+) (hN : 2 ≤ (N : ℕ)) :
    IsProbabilityMeasure ((rotAnchoredLaw P N).withDensity
      (fun y => ENNReal.ofReal (sizeBiasWeight N hN y))) := by
  rw [← map_originPos_eq_sizeBiased P N hN]
  have := (modelWellDefined P N).2.2
  exact (Measure.isProbabilityMeasure_map_iff (measurable_originPos N).aemeasurable).2
    inferInstance

/-- Transfer an `L²` certificate and the variance from the
size-biased anchored law to the preceding-particle statistic. -/
theorem variance_originPos_eq_sizeBiased (P : Parameters) (N : ℕ+)
    (hN : 2 ≤ (N : ℕ)) {T : (Fin (N : ℕ) → ℝ) → ℝ}
    (hT : MemLp T 2 ((rotAnchoredLaw P N).withDensity
      (fun y => ENNReal.ofReal (sizeBiasWeight N hN y)))) :
    MemLp (T ∘ originPos) 2 (gibbsMeasure P N) ∧
      ∃ hOi : Integrable (T ∘ originPos) (gibbsMeasure P N),
      ∃ hTi : Integrable T ((rotAnchoredLaw P N).withDensity
          (fun y => ENNReal.ofReal (sizeBiasWeight N hN y))),
      Riesz1.variance (gibbsMeasure P N) (T ∘ originPos) hOi =
        Riesz1.variance ((rotAnchoredLaw P N).withDensity
          (fun y => ENNReal.ofReal (sizeBiasWeight N hN y))) T
          hTi := by
  have := (modelWellDefined P N).2.2
  have := isProbabilityMeasure_sizeBiased_rotAnchoredLaw P N hN
  have hm : MemLp T 2 ((gibbsMeasure P N).map originPos) := by
    rwa [map_originPos_eq_sizeBiased P N hN]
  refine ⟨hm.comp_of_map (measurable_originPos N).aemeasurable,
    (hm.comp_of_map (measurable_originPos N).aemeasurable).integrable one_le_two,
    hT.integrable one_le_two, ?_⟩
  exact (variance_eq_of_map (gibbsMeasure P N) _
    (measurable_originPos N).aemeasurable (map_originPos_eq_sizeBiased P N hN)
    hT (hm.comp_of_map (measurable_originPos N).aemeasurable)).symm

end Riesz1.Internal

end
