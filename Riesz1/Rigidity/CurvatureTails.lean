/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Rigidity.CurvatureConcentration
public import Riesz1.ToMathlib.CenteredConcentration

/-!
# Centered moments and tails for the constrained block law

The concentration and zero-gradient assertions of the curvature lemma,
for every integer block start. The constants use the same `a_s` as the
internal Hessian bound.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped NNReal

namespace Riesz1

/-- The centered moment bound and optimized two-sided tail of
the curvature lemma, including zero tail mass when `B = 0`. -/
theorem curvature_centered_concentration (hBE : External.BakryEmery)
    (hPL : External.PrekopaLeindler) (P : Parameters) (N : ℕ+) (i0 : ℤ) {L : ℕ}
    (hL : L < (N : ℕ)) {θ : ℝ → ℝ} (hθ : IsForcingCutoff θ) {R : ℝ} (hR : 1 ≤ R)
    {F : HsEuclidean L.succPNat → ℝ}
    (hF : DifferentiableOn ℝ F (hsChamber L.succPNat))
    (hrot : ∀ x ∈ hsChamber L.succPNat, ∀ t : ℝ, F (hsTranslate t x) = F x)
    {B : ℝ≥0} (hB : ∀ x ∈ hsChamber L.succPNat, ‖fderiv ℝ F x‖ ≤ B) :
    let Q := constrainedLaw P N θ i0 L R
    let A := fun X => F (WithLp.toLp 2 (liftedBlock i0 hL X).val)
    Integrable A Q ∧
      (∀ t : ℝ, Integrable (fun X => Real.exp (t * (A X - ∫ Y, A Y ∂Q))) Q ∧
        Real.log (∫ X, Real.exp (t * (A X - ∫ Y, A Y ∂Q)) ∂Q) ≤
          R ^ ((parametersExponent P).val + 2) * (B : ℝ) ^ 2 * t ^ 2 /
            (2 * P.val.1 * rigidityCurvatureConstant (parametersExponent P).val *
              (N : ℝ) ^ 2 * (L + 1))) ∧
      (0 < B → ∀ v : ℝ, 0 < v →
        Q.real {X | v ≤ |A X - ∫ Y, A Y ∂Q|} ≤
          2 * Real.exp (-(P.val.1 * rigidityCurvatureConstant (parametersExponent P).val *
            (N : ℝ) ^ 2 * (L + 1) * v ^ 2) /
              (2 * R ^ ((parametersExponent P).val + 2) * (B : ℝ) ^ 2))) ∧
      (B = 0 → ∀ v : ℝ, 0 < v → Q {X | v ≤ |A X - ∫ Y, A Y ∂Q|} = 0) := by
  dsimp only
  let Q := constrainedLaw P N θ i0 L R
  let A := fun X => F (WithLp.toLp 2 (liftedBlock i0 hL X).val)
  let D := P.val.1 * rigidityCurvatureConstant (parametersExponent P).val *
    (N : ℝ) ^ 2 * (L + 1)
  have hD : 0 < D := by
    have := rigidityCurvatureConstant_pos (parametersExponent P)
    have := P.2.1
    have : (0 : ℝ) < N := by exact_mod_cast N.pos
    dsimp [D]
    positivity
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hpow : 0 < R ^ ((parametersExponent P).val + 2) := Real.rpow_pos_of_pos hR0 _
  let K : ℝ≥0 := ⟨R ^ ((parametersExponent P).val + 2) * (B : ℝ) ^ 2 / D,
    div_nonneg (mul_nonneg hpow.le (sq_nonneg _)) hD.le⟩
  have hQ : IsProbabilityMeasure Q := isProbabilityMeasure_constrainedLaw P N hθ hR0 i0 L
  have hm (t : ℝ) := curvature_concentration hBE hPL P N i0 hL hθ hR hF hrot hB t
  have hi (t : ℝ) : Integrable (fun X => Real.exp (t * A X)) Q := (hm t).2.1
  have hcoef (t : ℝ) : (K : ℝ) * t ^ 2 / 2 =
      R ^ ((parametersExponent P).val + 2) * (B : ℝ) ^ 2 * t ^ 2 /
        (2 * P.val.1 * rigidityCurvatureConstant (parametersExponent P).val *
          (N : ℝ) ^ 2 * (L + 1)) := by
    change (R ^ ((parametersExponent P).val + 2) * (B : ℝ) ^ 2 / D) * t ^ 2 / 2 = _
    rw [div_mul_eq_mul_div, div_div]
    congr 1
    dsimp only [D]
    ring
  have hlog (t : ℝ) : Real.log (∫ X, Real.exp (t * A X) ∂Q) ≤
      t * ∫ X, A X ∂Q + (K : ℝ) * t ^ 2 / 2 := by
    rw [hcoef]
    exact (hm t).2.2
  have hg := Internal.centered_subgaussian_of_log_mgf Q hi hlog
  refine ⟨(hm 0).1, ?_, ?_, ?_⟩
  · intro t
    refine ⟨hg.integrable_exp_mul t, ?_⟩
    have h := hg.cgf_le t
    change Real.log (∫ X, Real.exp (t * (A X - ∫ Y, A Y ∂Q)) ∂Q) ≤ _ at h
    change Real.log (∫ X, Real.exp (t * (A X - ∫ Y, A Y ∂Q)) ∂Q) ≤ _
    exact h.trans_eq (hcoef t)
  · intro hB0 v hv
    have htail := Internal.subgaussian_two_sided Q hg hv.le
    convert htail using 1
    congr 2
    change -(P.val.1 * rigidityCurvatureConstant (parametersExponent P).val *
      (N : ℝ) ^ 2 * (L + 1) * v ^ 2) /
        (2 * R ^ ((parametersExponent P).val + 2) * (B : ℝ) ^ 2) =
      -v ^ 2 / (2 * (R ^ ((parametersExponent P).val + 2) * (B : ℝ) ^ 2 / D))
    dsimp only [D]
    have hBpos : (0 : ℝ) < B := hB0
    field_simp
  · intro hB0 v hv
    have hK : K = 0 := by apply Subtype.ext; simp [K, hB0]
    rw [hK] at hg
    exact Internal.subgaussian_zero_tail Q hg hv

/-- The `B = 0` assertion is pointwise constancy, not just almost-everywhere constancy. -/
theorem curvature_observable_eq_of_zero_gradient {N : ℕ+} {L : ℕ}
    (i0 : ℤ) (hL : L < (N : ℕ)) {F : HsEuclidean L.succPNat → ℝ}
    (hF : DifferentiableOn ℝ F (hsChamber L.succPNat))
    (hB : ∀ x ∈ hsChamber L.succPNat, ‖fderiv ℝ F x‖ ≤ 0)
    (X Y : Configuration N) :
    F (WithLp.toLp 2 (liftedBlock i0 hL X).val) =
      F (WithLp.toLp 2 (liftedBlock i0 hL Y).val) := by
  have hx : WithLp.toLp 2 (liftedBlock i0 hL X).val ∈ hsChamber L.succPNat :=
    ⟨(liftedBlock i0 hL X).2.1, (liftedBlock i0 hL X).2.2.2.2⟩
  have hy : WithLp.toLp 2 (liftedBlock i0 hL Y).val ∈ hsChamber L.succPNat :=
    ⟨(liftedBlock i0 hL Y).2.1, (liftedBlock i0 hL Y).2.2.2.2⟩
  have h := (convex_hsChamber L.succPNat).norm_image_sub_le_of_norm_fderiv_le
    (fun x hx => (hF x hx).differentiableAt ((isOpen_hsChamber _).mem_nhds hx)) hB hx hy
  rw [zero_mul] at h
  exact (sub_eq_zero.mp (norm_le_zero_iff.mp h)).symm

end Riesz1

end
