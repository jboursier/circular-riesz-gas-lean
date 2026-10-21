/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.FDeriv.Bilinear
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Uniform Taylor bounds on compact convex sets

These estimates retain control uniformly at points close to the boundary.
They are analytic ingredients of the midpoint second variation in the proof of
Lemma 3.6.
-/

public section

noncomputable section

namespace Riesz1

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup G] [NormedSpace ℝ G]
variable {K : Set E} {f : E → G} {df : E → E →L[ℝ] G}

/-- A continuously differentiable function on a compact convex set has a uniform
first order remainder bound. Derivatives are ordinary derivatives in the ambient space. -/
theorem bl_uniform_first_order (hK : IsCompact K) (hc : Convex ℝ K)
    (hf : ∀ x ∈ K, HasFDerivAt f (df x) x) (hdf : ContinuousOn df K)
    {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ x ∈ K, ∀ y ∈ K, ‖y - x‖ < δ →
      ‖f y - f x - df x (y - x)‖ ≤ η * ‖y - x‖ := by
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff.mp
    (hK.uniformContinuousOn_of_continuous hdf) η hη
  refine ⟨δ, hδ, ?_⟩
  intro x hx y hy hxy
  have hs := hc.segment_subset hx hy
  apply (convex_segment x y).norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (fun z hz => (hf z (hs hz)).hasFDerivWithinAt) ?_
    (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  intro z hz
  apply le_of_lt
  rw [← dist_eq_norm]
  apply hmod z (hs hz) x hx
  rw [dist_eq_norm]
  exact (norm_sub_le_of_mem_segment hz).trans_lt hxy

/-- Derivative of the half quadratic form centered at `x`. -/
theorem bl_hasFDerivAt_half_quadratic (B : E →L[ℝ] E →L[ℝ] G)
    (hs : ∀ v w, B v w = B w v) (x y : E) :
    HasFDerivAt (fun z => (1 / 2 : ℝ) • B (z - x) (z - x)) (B (y - x)) y := by
  have hd := (hasFDerivAt_id (𝕜 := ℝ) y).sub_const x
  convert (B.hasFDerivAt_of_bilinear hd hd).const_smul (1 / 2 : ℝ) using 1
  · rfl
  · ext w
    change B (y - x) w = (1 / 2 : ℝ) • (B (y - x) w + B w (y - x))
    rw [hs w (y - x)]
    module

/-- A continuous symmetric second derivative gives a uniform quadratic remainder
bound on a compact convex set, including its boundary. The coefficient `η` can be
arbitrarily small. No modulus of third derivatives is assumed. -/
theorem bl_uniform_second_order (hK : IsCompact K) (hc : Convex ℝ K)
    (hf : ∀ x ∈ K, HasFDerivAt f (df x) x)
    (d2f : E → E →L[ℝ] E →L[ℝ] G)
    (hdf : ∀ x ∈ K, HasFDerivAt df (d2f x) x)
    (hd2f : ContinuousOn d2f K) (hs : ∀ x ∈ K, ∀ v w, d2f x v w = d2f x w v)
    {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ x ∈ K, ∀ y ∈ K, ‖y - x‖ < δ →
      ‖f y - f x - df x (y - x) - (1 / 2 : ℝ) • d2f x (y - x) (y - x)‖ ≤
        η * ‖y - x‖ ^ 2 := by
  obtain ⟨δ, hδ, hbound⟩ := bl_uniform_first_order hK hc hdf hd2f hη
  refine ⟨δ, hδ, ?_⟩
  intro x hx y hy hxy
  let R (z : E) := f z - f x - df x (z - x) - (1 / 2 : ℝ) • d2f x (z - x) (z - x)
  have hsK := hc.segment_subset hx hy
  have hR : ∀ z ∈ segment ℝ x y,
      HasFDerivWithinAt R (df z - df x - d2f x (z - x)) (segment ℝ x y) z := by
    intro z hz
    have hlin : HasFDerivAt (fun t => df x (t - x)) (df x) z := by
      simpa only [map_sub] using ((df x).hasFDerivAt (x := z)).sub_const (df x x)
    exact (((hf z (hsK hz)).sub_const (f x)).sub hlin |>.sub
      (bl_hasFDerivAt_half_quadratic (d2f x) (hs x hx) x z)).hasFDerivWithinAt
  have hb : ∀ z ∈ segment ℝ x y, ‖df z - df x - d2f x (z - x)‖ ≤ η * ‖y - x‖ := by
    intro z hz
    have hnorm := norm_sub_le_of_mem_segment hz
    exact (hbound x hx z (hsK hz) (hnorm.trans_lt hxy)).trans
      (mul_le_mul_of_nonneg_left hnorm hη.le)
  have h := (convex_segment x y).norm_image_sub_le_of_norm_hasFDerivWithin_le hR hb
    (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  simpa only [R, sub_self, map_zero, smul_zero, sub_zero, pow_two, mul_assoc] using h

/-- Uniform second order Taylor bound from the neighborhood regularity assumed
in the Brascamp–Lieb checkpoint. -/
theorem bl_uniform_second_order_of_contDiffOn {W : Set E}
    (hK : IsCompact K) (hc : Convex ℝ K) (hW : IsOpen W) (hKW : K ⊆ W)
    (hf : ContDiffOn ℝ 2 f W) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ x ∈ K, ∀ y ∈ K, ‖y - x‖ < δ →
      ‖f y - f x - fderiv ℝ f x (y - x) -
        (1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ f) x (y - x) (y - x)‖ ≤
        η * ‖y - x‖ ^ 2 := by
  have hf1 : ContDiffOn ℝ 1 (fderiv ℝ f) W :=
    hf.fderiv_of_isOpen hW (by norm_num)
  apply bl_uniform_second_order hK hc
    (fun x hx => ((hf.differentiableOn (by norm_num)).differentiableAt
      (hW.mem_nhds (hKW hx))).hasFDerivAt)
    (fderiv ℝ (fderiv ℝ f))
    (fun x hx => ((hf1.differentiableOn (by norm_num)).differentiableAt
      (hW.mem_nhds (hKW hx))).hasFDerivAt)
    ((hf1.continuousOn_fderiv_of_isOpen hW (by norm_num)).mono hKW) ?_ hη
  intro x hx
  exact (hf.contDiffAt (hW.mem_nhds (hKW hx))).isSymmSndFDerivAt (by simp)

/-- Uniform expansion of the midpoint perturbation, before optimizing the
displacement. This uses only continuity of the first derivative of `F` and
second derivative of `V`. No third derivatives are needed. -/
theorem bl_uniform_midpoint_remainder {W : Set E} {V F : E → ℝ}
    (hK : IsCompact K) (hc : Convex ℝ K) (hW : IsOpen W) (hKW : K ⊆ W)
    (hV : ContDiffOn ℝ 2 V W) (hF : ContDiffOn ℝ 2 F W)
    {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ z ∈ K, ∀ h : E, z + h ∈ K → z - h ∈ K → ‖h‖ < δ →
      ∀ ε : ℝ,
      |ε / 2 * (F (z + h) - F (z - h)) - (V (z + h) + V (z - h)) / 2 + V z -
        (ε * fderiv ℝ F z h - (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ V) z h h)| ≤
        η * (|ε| * ‖h‖ + ‖h‖ ^ 2) := by
  have hFd : ∀ x ∈ K, HasFDerivAt F (fderiv ℝ F x) x := by
    intro x hx
    exact ((hF.differentiableOn (by norm_num)).differentiableAt
      (hW.mem_nhds (hKW hx))).hasFDerivAt
  have hFc : ContinuousOn (fderiv ℝ F) K :=
    (hF.continuousOn_fderiv_of_isOpen hW (by norm_num)).mono hKW
  obtain ⟨δF, hδF, hbF⟩ := bl_uniform_first_order hK hc hFd hFc hη
  obtain ⟨δV, hδV, hbV⟩ :=
    bl_uniform_second_order_of_contDiffOn hK hc hW hKW hV hη
  refine ⟨min δF δV, lt_min hδF hδV, ?_⟩
  intro z hz h hp hm hnorm ε
  have hplus : z + h - z = h := by abel
  have hminus : z - h - z = -h := by abel
  have hFp := hbF z hz (z + h) hp (by simpa only [hplus] using hnorm.trans_le (min_le_left _ _))
  have hFm := hbF z hz (z - h) hm
    (by simpa only [hminus, norm_neg] using hnorm.trans_le (min_le_left _ _))
  have hVp := hbV z hz (z + h) hp (by simpa only [hplus] using hnorm.trans_le (min_le_right _ _))
  have hVm := hbV z hz (z - h) hm
    (by simpa only [hminus, norm_neg] using hnorm.trans_le (min_le_right _ _))
  simp only [hplus, hminus, map_neg, neg_apply, neg_neg, norm_neg, Real.norm_eq_abs,
    smul_eq_mul] at hFp hFm hVp hVm
  let Rp := F (z + h) - F z - fderiv ℝ F z h
  let Rm := F (z - h) - F z - -(fderiv ℝ F z h)
  let Tp := V (z + h) - V z - fderiv ℝ V z h -
    (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ V) z h h
  let Tm := V (z - h) - V z - -(fderiv ℝ V z h) -
    (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ V) z h h
  calc
    _ = |ε / 2 * (Rp - Rm) - (Tp + Tm) / 2| := by
      congr 1
      dsimp [Rp, Rm, Tp, Tm]
      ring
    _ ≤ |ε / 2 * (Rp - Rm)| + |(Tp + Tm) / 2| := abs_sub _ _
    _ ≤ (|ε| / 2) * (|Rp| + |Rm|) + (|Tp| + |Tm|) / 2 := by
      rw [abs_mul, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_div,
        abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      gcongr
      · exact abs_sub _ _
      · exact abs_add_le _ _
    _ ≤ (|ε| / 2) * (η * ‖h‖ + η * ‖h‖) +
        (η * ‖h‖ ^ 2 + η * ‖h‖ ^ 2) / 2 := by
      gcongr
    _ = _ := by ring

end Riesz1

end
