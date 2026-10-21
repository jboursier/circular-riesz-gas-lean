/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.AnchoredInverse
public import Riesz1.HelfferSjostrand.AnchoredCalculus
public import Riesz1.HelfferSjostrand.BLEnergy

/-!
# The vector Brascamp--Lieb comparison

Lemma 3.5 for every vector in `L²` of
the anchored law. The pointwise Hessian supremum is identified with the
actual inverse Hessian on the simplex. Its integral is finite, and bounds
the inverse energy constructed in `AnchoredInverse`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set InnerProductSpace
open scoped Topology

namespace Riesz1

variable {n : ℕ} {c : ℝ}

/-- The anchored Hessian lower bound, in the source coordinate space. -/
theorem anchoredHessianForm_lower (χ : HsPairPotentials n.succPNat c) (hc : 0 < c)
    {y : AnchoredEuclidean n} (hy : y ∈ anchoredSimplex n) (b : AnchoredEuclidean n) :
    2 * c * ‖b‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (hsAnchoredHamiltonianE χ)) y b b := by
  rw [← inner_anchoredHessianEnergy χ hc (anchorLift_mem_chamber hy),
    real_inner_self_eq_norm_sq]
  exact anchoredHessianEnergy_lower χ hc hy b

/-- The pointwise inverse-Hessian quadratic energy, used only on the simplex. -/
def anchoredHessianInverseEnergy (χ : HsPairPotentials n.succPNat c)
    (y v : AnchoredEuclidean n) : ℝ :=
  sSup (Set.range fun b : AnchoredEuclidean n =>
    2 * inner ℝ v b - fderiv ℝ (fderiv ℝ (hsAnchoredHamiltonianE χ)) y b b)

/-- The pointwise energy is finite, with a bound independent of the point. -/
theorem anchoredHessianInverseEnergy_bounds (χ : HsPairPotentials n.succPNat c) (hc : 0 < c)
    {y : AnchoredEuclidean n} (hy : y ∈ anchoredSimplex n) (v : AnchoredEuclidean n) :
    0 ≤ anchoredHessianInverseEnergy χ y v ∧
      anchoredHessianInverseEnergy χ y v ≤ ‖v‖ ^ 2 / (2 * c) :=
  bl_variational_energy_bounds _ v (by linarith) (anchoredHessianForm_lower χ hc hy)

/-- On its domain the pointwise energy is the actual inverse-Hessian energy. -/
theorem anchoredHessianInverseEnergy_eq_inverse (χ : HsPairPotentials n.succPNat c)
    (hc : 0 < c) {y : AnchoredEuclidean n} (hy : y ∈ anchoredSimplex n)
    (v : AnchoredEuclidean n) :
    ∃ hB : IsCoercive (fderiv ℝ (fderiv ℝ (hsAnchoredHamiltonianE χ)) y),
      anchoredHessianInverseEnergy χ y v = inner ℝ v (hB.continuousLinearEquivOfBilin.symm v) := by
  have hB : IsCoercive (fderiv ℝ (fderiv ℝ (hsAnchoredHamiltonianE χ)) y) :=
    ⟨2 * c, by linarith, fun b => by
      simpa only [pow_two, mul_assoc] using anchoredHessianForm_lower χ hc hy b⟩
  refine ⟨hB, bl_quadratic_sSup_eq_inverse hB ?_ v⟩
  exact ((contDiffOn_hsAnchoredHamiltonianE χ).contDiffAt
    ((isOpen_anchoredSimplex n).mem_nhds hy)).isSymmSndFDerivAt (by simp)

/-- Continuity of the Hessian on the open simplex. -/
theorem continuous_anchoredHessianForm (χ : HsPairPotentials n.succPNat c) :
    Continuous (fun y : anchoredSimplex n =>
      fderiv ℝ (fderiv ℝ (hsAnchoredHamiltonianE χ)) y.val) := by
  have hV : ContDiffOn ℝ 2 (hsAnchoredHamiltonianE χ) (anchoredSimplex n) :=
    (contDiffOn_hsAnchoredHamiltonianE χ).of_le (by simp)
  have hV1 : ContDiffOn ℝ 1 (fderiv ℝ (hsAnchoredHamiltonianE χ)) (anchoredSimplex n) :=
    hV.fderiv_of_isOpen (isOpen_anchoredSimplex n) (by norm_num)
  exact continuousOn_iff_continuous_domRestrict.mp
    (hV1.continuousOn_fderiv_of_isOpen (isOpen_anchoredSimplex n) (by norm_num))

/-- Joint lower semicontinuity avoids any smoothness assumption on the source field. -/
theorem lowerSemicontinuous_anchoredHessianInverseEnergy
    (χ : HsPairPotentials n.succPNat c) (hc : 0 < c) :
    LowerSemicontinuous (fun p : anchoredSimplex n × AnchoredEuclidean n =>
      anchoredHessianInverseEnergy χ p.1 p.2) := by
  apply lowerSemicontinuous_ciSup
  · intro p
    refine ⟨‖p.2‖ ^ 2 / (2 * c), ?_⟩
    rintro _ ⟨b, rfl⟩
    exact bl_quadratic_le_norm_sq_div (by linarith)
      (anchoredHessianForm_lower χ hc p.1.property) p.2 b
  · intro b
    exact ((continuous_const.mul (continuous_snd.inner continuous_const)).sub
      ((((continuous_anchoredHessianForm χ).comp continuous_fst).clm_apply
        continuous_const).clm_apply continuous_const)).lowerSemicontinuous

/-- The pointwise energy is jointly measurable in its point and source vector. -/
theorem measurable_anchoredHessianInverseEnergy_joint
    (χ : HsPairPotentials n.succPNat c) (hc : 0 < c) :
    Measurable (fun p : anchoredSimplex n × AnchoredEuclidean n =>
      anchoredHessianInverseEnergy χ p.1 p.2) :=
  (lowerSemicontinuous_anchoredHessianInverseEnergy χ hc).measurable

/-- Measurability of the pointwise energy for every measurable field on the simplex. -/
theorem measurable_anchoredHessianInverseEnergy (χ : HsPairPotentials n.succPNat c)
    (hc : 0 < c) (v : AnchoredEuclidean n → AnchoredEuclidean n) (hv : Measurable v) :
    Measurable (fun y : anchoredSimplex n => anchoredHessianInverseEnergy χ y (v y)) := by
  have hv' : Measurable (fun y : anchoredSimplex n => (y, v y.val)) :=
    measurable_id.prodMk (hv.comp measurable_subtype_coe)
  exact Measurable.comp
    (g := fun p : anchoredSimplex n × AnchoredEuclidean n =>
      anchoredHessianInverseEnergy χ p.1 p.2)
    (f := fun y : anchoredSimplex n => (y, v y.val))
    (measurable_anchoredHessianInverseEnergy_joint χ hc) hv'

/-- Square integrability of the source field proves integrability of the Hessian energy. -/
theorem integrable_anchoredHessianInverseEnergy (μ : Measure (AnchoredEuclidean n))
    (χ : HsPairPotentials n.succPNat c) (hc : 0 < c)
    (hμ : ∀ᵐ y ∂μ, y ∈ anchoredSimplex n) (v : Lp (AnchoredEuclidean n) 2 μ) :
    Integrable (fun y => anchoredHessianInverseEnergy χ y (v y)) μ := by
  have hm := aemeasurable_restrict_of_measurable_subtype (μ := μ)
    (f := fun y => anchoredHessianInverseEnergy χ y (v y))
    (isOpen_anchoredSimplex n).measurableSet
    (measurable_anchoredHessianInverseEnergy χ hc v (Lp.stronglyMeasurable v).measurable)
  rw [Measure.restrict_eq_self_of_ae_mem hμ] at hm
  apply ((Lp.memLp v).norm.integrable_sq.div_const (2 * c)).mono' hm.aestronglyMeasurable
  filter_upwards [hμ] with y hy
  obtain ⟨h0, hle⟩ := anchoredHessianInverseEnergy_bounds χ hc hy (v y)
  simpa only [Real.norm_eq_abs, abs_of_nonneg h0] using hle

namespace Internal

/-- Internal density step: a bound on core objectives extends to the attained inverse objective. -/
theorem anchoredVectorInverseEnergy_le_of_test_bound (μ : Measure (AnchoredEuclidean n))
    [IsFiniteMeasure μ] (χ : HsPairPotentials n.succPNat c) (hc : 0 < c)
    (hμ : ∀ᵐ y ∂μ, y ∈ anchoredSimplex n) (v : Lp (AnchoredEuclidean n) 2 μ) (C : ℝ)
    (hcore : ∀ t : AnchoredVectorTest n,
      2 * inner ℝ v (anchoredInverseValues μ (anchoredVectorJet χ μ t)) -
        anchoredVectorSobolevForm μ (anchoredVectorJet χ μ t) (anchoredVectorJet χ μ t) ≤ C) :
    anchoredVectorInverseEnergy μ χ hc hμ v ≤ C := by
  have hclosed : IsClosed {w : Lp (AnchoredJetPoint n) 2 μ |
      2 * inner ℝ v (anchoredInverseValues μ w) - anchoredVectorSobolevForm μ w w ≤ C} := by
    simp_rw [← anchoredInverseDerivatives_inner, real_inner_self_eq_norm_sq]
    exact isClosed_le ((continuous_const.mul
      (continuous_const.inner (anchoredInverseValues μ).continuous)).sub
        ((anchoredInverseDerivatives μ).continuous.norm.pow 2)) continuous_const
  have hle : 2 * inner ℝ v
      (anchoredVectorValues μ χ (anchoredVectorInverse μ χ hc hμ v)) -
      anchoredVectorSobolevForm μ (anchoredVectorInverse μ χ hc hμ v).val
        (anchoredVectorInverse μ χ hc hμ v).val ≤ C := by
    apply closure_minimal (s := (LinearMap.range (anchoredVectorJetLin χ μ) : Set _))
      (fun w hw => ?_) hclosed (anchoredVectorInverse μ χ hc hμ v).property
    obtain ⟨t, rfl⟩ := hw
    exact hcore t
  rw [anchoredVectorInverse_solves μ χ hc hμ] at hle
  change inner ℝ v (anchoredVectorValues μ χ (anchoredVectorInverse μ χ hc hμ v)) ≤ C
  linarith

end Internal

/-- Lemma 3.5: the actual inverse energy is at most
the integral of the inverse-Hessian energy, for every vector `L²` field. -/
theorem anchoredInverseEnergy_le_hessian (χ : HsPairPotentials n.succPNat c) (hc : 0 < c)
    (v : Lp (AnchoredEuclidean n) 2 (anchoredMeasureE χ)) :
    anchoredInverseEnergy χ hc v ≤
      ∫ y, anchoredHessianInverseEnergy χ y (v y) ∂anchoredMeasureE χ := by
  have := isProbabilityMeasure_anchoredMeasureE χ hc
  let μ := anchoredMeasureE χ
  have hQ := integrable_anchoredHessianInverseEnergy μ χ hc (ae_mem_anchoredSimplex χ) v
  apply Internal.anchoredVectorInverseEnergy_le_of_test_bound μ χ hc
    (ae_mem_anchoredSimplex χ) v
  intro t
  have hp : Integrable (fun y => inner ℝ (v y) (anchoredTestVector t y)) μ :=
    (L2.integrable_inner v (anchoredInverseValues μ (anchoredVectorJet χ μ t))).congr (by
      filter_upwards [anchoredInverseValues_jet_ae μ χ t] with y hy
      rw [hy])
  have hpair : inner ℝ v (anchoredInverseValues μ (anchoredVectorJet χ μ t)) =
      ∫ y, inner ℝ (v y) (anchoredTestVector t y) ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [anchoredInverseValues_jet_ae μ χ t] with y hy
    rw [hy]
  have hg := integrable_finsetSum Finset.univ (fun i _ => integrable_anchoredGradInner χ μ t t i)
  have he := integrable_anchoredEnergyInner χ μ t t
  rw [hpair, anchoredVectorSobolevForm_jet χ hc,
    anchoredVectorForm_eq_integral χ hc, ← integral_const_mul]
  have hsub := integral_sub (hp.const_mul 2) (hg.add he)
  simp only [Pi.add_apply] at hsub
  change (∫ y, 2 * inner ℝ (v y) (anchoredTestVector t y) ∂μ) -
    (∫ y, (∑ i : Fin n, inner ℝ (gradient (t i : AnchoredEuclidean n → ℝ) y)
      (gradient (t i : AnchoredEuclidean n → ℝ) y)) +
        inner ℝ (anchoredEnergyFun χ t y) (anchoredEnergyFun χ t y) ∂μ) ≤ _
  rw [← hsub]
  apply integral_mono_ae ((hp.const_mul 2).sub (hg.add he)) hQ
  filter_upwards [ae_mem_anchoredSimplex χ] with y hy
  have hbd : BddAbove (Set.range fun b : AnchoredEuclidean n =>
      2 * inner ℝ (v y) b - fderiv ℝ (fderiv ℝ (hsAnchoredHamiltonianE χ)) y b b) := by
    refine ⟨‖v y‖ ^ 2 / (2 * c), ?_⟩
    rintro _ ⟨b, rfl⟩
    exact bl_quadratic_le_norm_sq_div (by linarith) (anchoredHessianForm_lower χ hc hy) (v y) b
  have hs := le_csSup hbd (Set.mem_range_self (anchoredTestVector t y))
  have hn : 0 ≤ ∑ i : Fin n, inner ℝ (gradient (t i : AnchoredEuclidean n → ℝ) y)
      (gradient (t i : AnchoredEuclidean n → ℝ) y) :=
    Finset.sum_nonneg fun i _ => real_inner_self_nonneg
  simp only [Pi.sub_apply, Pi.add_apply]
  rw [anchoredEnergyFun, inner_anchoredHessianEnergy χ hc (anchorLift_mem_chamber hy)]
  exact (by linarith : _ ≤ 2 * inner ℝ (v y) (anchoredTestVector t y) -
    fderiv ℝ (fderiv ℝ (hsAnchoredHamiltonianE χ)) y (anchoredTestVector t y)
      (anchoredTestVector t y)).trans hs

/-- The right side of the vector Brascamp--Lieb bound has the sharp uniform bound of the paper. -/
theorem integral_anchoredHessianInverseEnergy_le (μ : Measure (AnchoredEuclidean n))
    (χ : HsPairPotentials n.succPNat c) (hc : 0 < c)
    (hμ : ∀ᵐ y ∂μ, y ∈ anchoredSimplex n) (v : Lp (AnchoredEuclidean n) 2 μ) :
    (∫ y, anchoredHessianInverseEnergy χ y (v y) ∂μ) ≤ ‖v‖ ^ 2 / (2 * c) := by
  have hn : (∫ y, ‖v y‖ ^ 2 ∂μ) = ‖v‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq (x := v), L2.inner_def]
    simp only [real_inner_self_eq_norm_sq]
  rw [← hn, ← integral_div]
  apply integral_mono_ae (integrable_anchoredHessianInverseEnergy μ χ hc hμ v)
    ((Lp.memLp v).norm.integrable_sq.div_const _)
  filter_upwards [hμ] with y hy
  exact (anchoredHessianInverseEnergy_bounds χ hc hy (v y)).2

/-- All assertions of Lemma 3.5, with the pointwise
inverse-Hessian interpretation supplied by `anchoredHessianInverseEnergy_eq_inverse`. -/
theorem anchored_vector_brascamp_lieb (χ : HsPairPotentials n.succPNat c) (hc : 0 < c)
    (v : Lp (AnchoredEuclidean n) 2 (anchoredMeasureE χ)) :
    letI := isProbabilityMeasure_anchoredMeasureE χ hc
    Integrable (fun y => anchoredHessianInverseEnergy χ y (v y)) (anchoredMeasureE χ) ∧
      anchoredInverseEnergy χ hc v =
        sSup (Set.range fun w : AnchoredVectorSobolev χ (anchoredMeasureE χ) =>
          2 * inner ℝ v (anchoredVectorValues (anchoredMeasureE χ) χ w) -
            anchoredVectorSobolevForm (anchoredMeasureE χ) w.val w.val) ∧
      anchoredInverseEnergy χ hc v ≤
        (∫ y, anchoredHessianInverseEnergy χ y (v y) ∂anchoredMeasureE χ) ∧
      (∫ y, anchoredHessianInverseEnergy χ y (v y) ∂anchoredMeasureE χ) ≤
        ‖v‖ ^ 2 / (2 * c) := by
  have := isProbabilityMeasure_anchoredMeasureE χ hc
  exact ⟨integrable_anchoredHessianInverseEnergy _ χ hc (ae_mem_anchoredSimplex χ) v,
    anchoredInverseEnergy_eq_sSup χ hc v, anchoredInverseEnergy_le_hessian χ hc v,
    integral_anchoredHessianInverseEnergy_le _ χ hc (ae_mem_anchoredSimplex χ) v⟩

end Riesz1

end
