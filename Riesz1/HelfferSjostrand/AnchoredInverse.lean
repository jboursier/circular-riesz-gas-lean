/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.AnchoredInverseSpace
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# The anchored inverse and its inverse energy

The inverse is
constructed on the whole vector `L²` space by the coercivity proved in
`AnchoredInverseSpace`. It is the unique weak solution in the vector
Sobolev completion, with no normalization or compatibility condition.

The construction also works for any finite measure supported on the anchored
simplex, using the given pair Hessian in its form. The named Gibbs-law
specialization has no support hypothesis. The variational identity is the
first equality of Lemma 3.5.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set InnerProductSpace

namespace Riesz1

variable {n : ℕ} {c : ℝ} (μ : Measure (AnchoredEuclidean n)) [IsFiniteMeasure μ]
  (χ : HsPairPotentials n.succPNat c) (hc : 0 < c)
  (hμ : ∀ᵐ y ∂μ, y ∈ anchoredSimplex n)

/-- The continuous value map on the anchored vector Sobolev space. -/
def anchoredVectorValues : AnchoredVectorSobolev χ μ →L[ℝ] Lp (AnchoredEuclidean n) 2 μ :=
  (anchoredInverseValues μ).comp (anchoredVectorSobolevSubmodule χ μ).subtypeL

/-- The unique variational inverse of the vector form on the entire `L²` carrier. -/
def anchoredVectorInverse : Lp (AnchoredEuclidean n) 2 μ →L[ℝ] AnchoredVectorSobolev χ μ :=
  (anchoredInverseBilinear_coercive μ χ hc hμ).continuousLinearEquivOfBilin.symm.toContinuousLinearMap
    |>.comp (anchoredVectorValues μ χ).adjoint

/-- The inverse satisfies the full weak equation, with the existing form. -/
theorem anchoredVectorInverse_solves (v : Lp (AnchoredEuclidean n) 2 μ)
    (w : AnchoredVectorSobolev χ μ) :
    anchoredVectorSobolevForm μ (anchoredVectorInverse μ χ hc hμ v).val w.val =
      inner ℝ v (anchoredVectorValues μ χ w) := by
  rw [← anchoredInverseBilinear_eq]
  let hB := anchoredInverseBilinear_coercive μ χ hc hμ
  change anchoredInverseBilinear μ χ
    (hB.continuousLinearEquivOfBilin.symm ((anchoredVectorValues μ χ).adjoint v)) w = _
  rw [← hB.continuousLinearEquivOfBilin_apply,
    ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearMap.adjoint_inner_left]

/-- No second weak solution exists. -/
theorem anchoredVectorInverse_unique (v : Lp (AnchoredEuclidean n) 2 μ)
    (u : AnchoredVectorSobolev χ μ)
    (hu : ∀ w : AnchoredVectorSobolev χ μ,
      anchoredVectorSobolevForm μ u.val w.val = inner ℝ v (anchoredVectorValues μ χ w)) :
    u = anchoredVectorInverse μ χ hc hμ v := by
  let hB := anchoredInverseBilinear_coercive μ χ hc hμ
  apply hB.continuousLinearEquivOfBilin.injective
  apply ext_inner_right ℝ
  intro w
  rw [hB.continuousLinearEquivOfBilin_apply, anchoredInverseBilinear_eq,
    hB.continuousLinearEquivOfBilin_apply, anchoredInverseBilinear_eq,
    hu, anchoredVectorInverse_solves]

/-- Inverse energy as the `L²` pairing with the unique inverse. -/
def anchoredVectorInverseEnergy (v : Lp (AnchoredEuclidean n) 2 μ) : ℝ :=
  inner ℝ v (anchoredVectorValues μ χ (anchoredVectorInverse μ χ hc hμ v))

/-- The inverse energy is an ordinary integral with an integrable integrand. -/
theorem anchoredVectorInverseEnergy_integrable (v : Lp (AnchoredEuclidean n) 2 μ) :
    Integrable (fun y => inner ℝ (v y)
      (anchoredVectorValues μ χ (anchoredVectorInverse μ χ hc hμ v) y)) μ :=
  L2.integrable_inner _ _

/-- The inverse energy is given by this integral. -/
theorem anchoredVectorInverseEnergy_eq_integral (v : Lp (AnchoredEuclidean n) 2 μ) :
    anchoredVectorInverseEnergy μ χ hc hμ v = ∫ y, inner ℝ (v y)
      (anchoredVectorValues μ χ (anchoredVectorInverse μ χ hc hμ v) y) ∂μ :=
  L2.inner_def _ _

/-- The vector inverse energy is nonnegative. -/
theorem anchoredVectorInverseEnergy_nonneg (v : Lp (AnchoredEuclidean n) 2 μ) :
    0 ≤ anchoredVectorInverseEnergy μ χ hc hμ v := by
  rw [anchoredVectorInverseEnergy, ← anchoredVectorInverse_solves μ χ hc hμ,
    ← anchoredInverseBilinear_eq]
  exact bl_bilin_self_nonneg (anchoredInverseBilinear_coercive μ χ hc hμ) _

/-- Completing the square for the actual inverse, on the whole vector energy space. -/
theorem anchoredVectorInverseEnergy_complete_square (v : Lp (AnchoredEuclidean n) 2 μ)
    (w : AnchoredVectorSobolev χ μ) :
    2 * inner ℝ v (anchoredVectorValues μ χ w) -
        anchoredVectorSobolevForm μ w.val w.val =
      anchoredVectorInverseEnergy μ χ hc hμ v -
        anchoredVectorSobolevForm μ (w - anchoredVectorInverse μ χ hc hμ v).val
          (w - anchoredVectorInverse μ χ hc hμ v).val := by
  simp_rw [← anchoredInverseBilinear_eq]
  let hB := anchoredInverseBilinear_coercive μ χ hc hμ
  have hs (u w : AnchoredVectorSobolev χ μ) :
      anchoredInverseBilinear μ χ u w = anchoredInverseBilinear μ χ w u := by
    change inner ℝ (anchoredInverseDifferential μ χ u) (anchoredInverseDifferential μ χ w) = _
    exact real_inner_comm _ _
  have hh := bl_quadratic_complete_square hB hs ((anchoredVectorValues μ χ).adjoint v) w
  simp only [ContinuousLinearMap.adjoint_inner_left] at hh
  exact hh

/-- The supremum is attained at the unique inverse, so it has no unbounded-supremum convention. -/
theorem anchoredVectorInverseEnergy_isGreatest (v : Lp (AnchoredEuclidean n) 2 μ) :
    IsGreatest (Set.range fun w : AnchoredVectorSobolev χ μ =>
      2 * inner ℝ v (anchoredVectorValues μ χ w) - anchoredVectorSobolevForm μ w.val w.val)
      (anchoredVectorInverseEnergy μ χ hc hμ v) := by
  refine ⟨⟨anchoredVectorInverse μ χ hc hμ v, ?_⟩, ?_⟩
  · dsimp only
    rw [anchoredVectorInverseEnergy_complete_square μ χ hc hμ]
    simp [anchoredVectorSobolevForm]
  · rintro _ ⟨w, rfl⟩
    dsimp only
    rw [anchoredVectorInverseEnergy_complete_square μ χ hc hμ]
    exact sub_le_self _ (by
      rw [← anchoredInverseBilinear_eq]
      exact bl_bilin_self_nonneg (anchoredInverseBilinear_coercive μ χ hc hμ) _)

/-- The variational equality in Lemma 3.5. -/
theorem anchoredVectorInverseEnergy_eq_sSup (v : Lp (AnchoredEuclidean n) 2 μ) :
    anchoredVectorInverseEnergy μ χ hc hμ v =
      sSup (Set.range fun w : AnchoredVectorSobolev χ μ =>
        2 * inner ℝ v (anchoredVectorValues μ χ w) - anchoredVectorSobolevForm μ w.val w.val) :=
  (anchoredVectorInverseEnergy_isGreatest μ χ hc hμ v).csSup_eq.symm

/-- The variational functional has exactly one minimizer. -/
theorem anchoredVectorInverse_minimizer_iff (v : Lp (AnchoredEuclidean n) 2 μ)
    (u : AnchoredVectorSobolev χ μ) :
    (∀ w : AnchoredVectorSobolev χ μ,
      anchoredVectorSobolevForm μ u.val u.val - 2 * inner ℝ v (anchoredVectorValues μ χ u) ≤
        anchoredVectorSobolevForm μ w.val w.val - 2 * inner ℝ v (anchoredVectorValues μ χ w)) ↔
      u = anchoredVectorInverse μ χ hc hμ v := by
  constructor
  · intro hmin
    have hh := hmin (anchoredVectorInverse μ χ hc hμ v)
    have hu := anchoredVectorInverseEnergy_complete_square μ χ hc hμ v u
    have hi := anchoredVectorInverseEnergy_complete_square μ χ hc hμ v
      (anchoredVectorInverse μ χ hc hμ v)
    have hz : anchoredVectorSobolevForm μ
        (u - anchoredVectorInverse μ χ hc hμ v).val
        (u - anchoredVectorInverse μ χ hc hμ v).val ≤ 0 := by
      have hzero : anchoredVectorSobolevForm μ 0 0 = 0 := by
        simp [anchoredVectorSobolevForm]
      simp only [sub_self, Submodule.coe_zero, hzero, sub_zero] at hi
      linarith
    rw [← anchoredInverseBilinear_eq] at hz
    obtain ⟨k, hk, hbound⟩ := anchoredInverseBilinear_coercive μ χ hc hμ
    have hb := hbound (u - anchoredVectorInverse μ χ hc hμ v)
    have hp : k * ‖u - anchoredVectorInverse μ χ hc hμ v‖ ^ 2 ≤ 0 := by
      nlinarith only [hb, hz]
    have hs : ‖u - anchoredVectorInverse μ χ hc hμ v‖ ^ 2 ≤ 0 :=
      nonpos_of_mul_nonpos_right hp hk
    have hn : ‖u - anchoredVectorInverse μ χ hc hμ v‖ = 0 :=
      sq_eq_zero_iff.mp (le_antisymm hs (sq_nonneg _))
    exact sub_eq_zero.mp (norm_eq_zero.mp hn)
  · rintro rfl w
    have hi := (anchoredVectorInverseEnergy_isGreatest μ χ hc hμ v).2
      (Set.mem_range_self w)
    have he := anchoredVectorInverse_solves μ χ hc hμ v (anchoredVectorInverse μ χ hc hμ v)
    dsimp only [anchoredVectorInverseEnergy] at hi
    linarith

/-- The finite inverse-energy bound in Lemma 3.5. -/
theorem anchoredVectorInverseEnergy_le_norm_sq (v : Lp (AnchoredEuclidean n) 2 μ) :
    anchoredVectorInverseEnergy μ χ hc hμ v ≤ ‖v‖ ^ 2 / (2 * c) := by
  let u := anchoredVectorInverse μ χ hc hμ v
  have hval := anchoredInverse_value_bound μ χ hc hμ u
  have hgrad : 2 * c * ‖anchoredVectorValues μ χ u‖ ^ 2 ≤
      anchoredVectorSobolevForm μ u.val u.val := by
    rw [← anchoredInverseDerivatives_inner, real_inner_self_eq_norm_sq]
    exact hval
  have hsol := anchoredVectorInverse_solves μ χ hc hμ v u
  have hcs := real_inner_le_norm v (anchoredVectorValues μ χ u)
  have hs := sq_nonneg (‖v‖ - 2 * c * ‖anchoredVectorValues μ χ u‖)
  change inner ℝ v (anchoredVectorValues μ χ u) ≤ _
  apply (le_div_iff₀ (by linarith : 0 < 2 * c)).mpr
  nlinarith

section Gibbs

/-- The anchored inverse for the canonical anchored Gibbs law. -/
def anchoredInverse :
    letI := isProbabilityMeasure_anchoredMeasureE χ hc
    Lp (AnchoredEuclidean n) 2 (anchoredMeasureE χ) →L[ℝ]
      AnchoredVectorSobolev χ (anchoredMeasureE χ) := by
  letI := isProbabilityMeasure_anchoredMeasureE χ hc
  exact anchoredVectorInverse (anchoredMeasureE χ) χ hc (ae_mem_anchoredSimplex χ)

/-- The anchored inverse energy on the entire vector `L²` space. -/
def anchoredInverseEnergy (v : Lp (AnchoredEuclidean n) 2 (anchoredMeasureE χ)) : ℝ := by
  letI := isProbabilityMeasure_anchoredMeasureE χ hc
  exact anchoredVectorInverseEnergy (anchoredMeasureE χ) χ hc (ae_mem_anchoredSimplex χ) v

/-- The anchored inverse satisfies the variational operator equation. -/
theorem anchoredInverse_solves (v : Lp (AnchoredEuclidean n) 2 (anchoredMeasureE χ))
    : letI := isProbabilityMeasure_anchoredMeasureE χ hc
    ∀ w : AnchoredVectorSobolev χ (anchoredMeasureE χ),
      anchoredVectorSobolevForm (anchoredMeasureE χ) (anchoredInverse χ hc v).val w.val =
        inner ℝ v (anchoredVectorValues (anchoredMeasureE χ) χ w) := by
  have := isProbabilityMeasure_anchoredMeasureE χ hc
  exact anchoredVectorInverse_solves (anchoredMeasureE χ) χ hc (ae_mem_anchoredSimplex χ) v

/-- The attained variational identity for the canonical anchored Gibbs law. -/
theorem anchoredInverseEnergy_eq_sSup (v : Lp (AnchoredEuclidean n) 2 (anchoredMeasureE χ)) :
    letI := isProbabilityMeasure_anchoredMeasureE χ hc
    anchoredInverseEnergy χ hc v =
      sSup (Set.range fun w : AnchoredVectorSobolev χ (anchoredMeasureE χ) =>
        2 * inner ℝ v (anchoredVectorValues (anchoredMeasureE χ) χ w) -
          anchoredVectorSobolevForm (anchoredMeasureE χ) w.val w.val) := by
  have := isProbabilityMeasure_anchoredMeasureE χ hc
  exact anchoredVectorInverseEnergy_eq_sSup (anchoredMeasureE χ) χ hc (ae_mem_anchoredSimplex χ) v

end Gibbs

end Riesz1

end
