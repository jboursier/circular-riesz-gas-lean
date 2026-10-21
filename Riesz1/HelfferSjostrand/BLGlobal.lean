/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.BLTaylor
public import Riesz1.HelfferSjostrand.BLEnergy
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Global midpoint estimates for the Brascamp–Lieb second variation

Strong convexity first localizes all positive midpoint perturbations. Uniform
Taylor estimates then give a quadratic-energy majorant for every displacement,
including those for which the midpoint is close to the boundary.
-/

public section

noncomputable section

open Set
open scoped InnerProductSpace

namespace Riesz1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {U W : Set E} {V F : E → ℝ}

/-- A Hessian lower bound gives the strong midpoint convexity estimate without
any assumption on the boundary of the convex domain. -/
theorem bl_midpoint_strong_convexity (hc : Convex ℝ U)
    (hW : IsOpen W) (hUW : U ⊆ W) (hV : ContDiffOn ℝ 2 V W)
    {κ : ℝ} (hb : ∀ x ∈ U, ∀ h, κ * ‖h‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x h h)
    {z h : E} (hp : z + h ∈ U) (hm : z - h ∈ U) :
    V z + κ / 2 * ‖h‖ ^ 2 ≤ (V (z + h) + V (z - h)) / 2 := by
  let p : ℝ → E := fun t => z + t • h
  have hpU : ∀ t ∈ Icc (-1 : ℝ) 1, p t ∈ U := by
    intro t ht
    have he : p t = ((1 - t) / 2) • (z - h) + ((1 + t) / 2) • (z + h) := by
      dsimp [p]
      module
    rw [he]
    exact hc hm hp (by linarith [ht.2]) (by linarith [ht.1]) (by ring)
  have hpD (t : ℝ) : HasDerivAt p h t := by
    simpa [p] using ((hasDerivAt_id t).smul_const h).const_add z
  have hV1 : ContDiffOn ℝ 1 (fderiv ℝ V) W := hV.fderiv_of_isOpen hW (by norm_num)
  have hd (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) :
      HasDerivAt (fun t => V (p t) - κ / 2 * ‖h‖ ^ 2 * t ^ 2)
        (fderiv ℝ V (p t) h - κ * ‖h‖ ^ 2 * t) t := by
    have hv := ((hV.differentiableOn (by norm_num)).differentiableAt
      (hW.mem_nhds (hUW (hpU t ht)))).hasFDerivAt.comp_hasDerivAt t (hpD t)
    convert hv.sub (((hasDerivAt_id t).pow 2).const_mul (κ / 2 * ‖h‖ ^ 2)) using 1
    · rfl
    · dsimp
      ring
  have hdd (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) :
      HasDerivAt (fun t => fderiv ℝ V (p t) h - κ * ‖h‖ ^ 2 * t)
        (fderiv ℝ (fderiv ℝ V) (p t) h h - κ * ‖h‖ ^ 2) t := by
    have hv := ((hV1.differentiableOn (by norm_num)).differentiableAt
      (hW.mem_nhds (hUW (hpU t ht)))).hasFDerivAt.comp_hasDerivAt t (hpD t)
    exact (hv.clm_apply (hasDerivAt_const t h)).sub
      ((hasDerivAt_id t).const_mul (κ * ‖h‖ ^ 2)) |>.congr_deriv (by simp)
  have hconv : ConvexOn ℝ (Icc (-1 : ℝ) 1)
      (fun t => V (p t) - κ / 2 * ‖h‖ ^ 2 * t ^ 2) := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _)
      (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hd t (interior_subset ht)).hasDerivWithinAt)
      (fun t ht => (hdd t (interior_subset ht)).hasDerivWithinAt)
    intro t ht
    exact sub_nonneg.mpr (hb (p t) (hpU t (interior_subset ht)) h)
  have hi := hconv.2 (by norm_num : (-1 : ℝ) ∈ Icc (-1 : ℝ) 1)
    (by norm_num : (1 : ℝ) ∈ Icc (-1 : ℝ) 1)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  norm_num [p, ← sub_eq_add_neg] at hi
  linarith

/-- A derivative bound on a convex set controls the antisymmetric difference
appearing in the midpoint perturbation. -/
theorem bl_midpoint_difference_bound (hc : Convex ℝ U)
    (hW : IsOpen W) (hUW : U ⊆ W) (hF : ContDiffOn ℝ 2 F W)
    {L : ℝ} (hL : ∀ x ∈ U, ‖fderiv ℝ F x‖ ≤ L)
    {z h : E} (hp : z + h ∈ U) (hm : z - h ∈ U) :
    |F (z + h) - F (z - h)| ≤ 2 * L * ‖h‖ := by
  have hi := hc.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun x hx => ((hF.differentiableOn (by norm_num)).differentiableAt
      (hW.mem_nhds (hUW hx))).hasFDerivAt.hasFDerivWithinAt) hL hm hp
  have he : z + h - (z - h) = (2 : ℝ) • h := by module
  simpa [Real.norm_eq_abs, he, norm_smul, mul_left_comm, mul_assoc] using hi

/-- The global quadratic bound preceding localization. -/
theorem bl_midpoint_global_bound (hc : Convex ℝ U)
    (hW : IsOpen W) (hUW : U ⊆ W) (hV : ContDiffOn ℝ 2 V W)
    (hF : ContDiffOn ℝ 2 F W) {κ L : ℝ}
    (hb : ∀ x ∈ U, ∀ h, κ * ‖h‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x h h)
    (hL : ∀ x ∈ U, ‖fderiv ℝ F x‖ ≤ L)
    {z h : E} (hp : z + h ∈ U) (hm : z - h ∈ U) (ε : ℝ) :
    ε / 2 * (F (z + h) - F (z - h)) -
        (V (z + h) + V (z - h)) / 2 + V z ≤
      |ε| * L * ‖h‖ - κ / 2 * ‖h‖ ^ 2 := by
  have hv := bl_midpoint_strong_convexity hc hW hUW hV hb hp hm
  have hf := bl_midpoint_difference_bound hc hW hUW hF hL hp hm
  have he : ε / 2 * (F (z + h) - F (z - h)) ≤ |ε| * L * ‖h‖ := by
    calc
      _ ≤ |ε / 2 * (F (z + h) - F (z - h))| := le_abs_self _
      _ = |ε| / 2 * |F (z + h) - F (z - h)| := by rw [abs_mul, abs_div]; norm_num
      _ ≤ |ε| / 2 * (2 * L * ‖h‖) := mul_le_mul_of_nonneg_left hf (by positivity)
      _ = _ := by ring
  linarith

section InnerProduct

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Rescaling the quadratic variational bound, including the zero parameter. -/
theorem bl_scaled_variational_bound (B : H →L[ℝ] H →L[ℝ] ℝ)
    (g : H →L[ℝ] ℝ) {κ : ℝ} (hκ : 0 < κ)
    (hb : ∀ h, κ * ‖h‖ ^ 2 ≤ B h h) (ε : ℝ) (h : H) :
    ε * g h - (1 / 2 : ℝ) * B h h ≤
      ε ^ 2 / 2 * sSup (Set.range (fun v : H => 2 * g v - B v v)) := by
  let gv := (InnerProductSpace.toDual ℝ H).symm g
  have hg (v : H) : ⟪gv, v⟫_ℝ = g v := InnerProductSpace.toDual_symm_apply
  have hbd : BddAbove (Set.range (fun v : H => 2 * g v - B v v)) := by
    refine ⟨‖gv‖ ^ 2 / κ, ?_⟩
    rintro _ ⟨v, rfl⟩
    simpa only [hg] using bl_quadratic_le_norm_sq_div hκ hb gv v
  by_cases he : ε = 0
  · subst ε
    have hn : 0 ≤ B h h := (by positivity : 0 ≤ κ * ‖h‖ ^ 2).trans (hb h)
    simp only [zero_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      zero_div, sub_le_iff_le_add, zero_add]
    positivity
  · have hi := mul_le_mul_of_nonneg_left
      (le_csSup hbd (Set.mem_range_self ((ε⁻¹) • h)))
      (by positivity : 0 ≤ ε ^ 2 / 2)
    calc
      _ = ε ^ 2 / 2 * (2 * g ((ε⁻¹) • h) - B ((ε⁻¹) • h) ((ε⁻¹) • h)) := by
        simp only [map_smul, smul_apply, smul_eq_mul]
        field_simp [he]
      _ ≤ _ := hi

end InnerProduct

/-- Uniform quadratic majorant for every feasible midpoint displacement. The
error is arbitrarily small relative to the square of the perturbation parameter.
All localization and derivative bounds follow from the original smooth data. -/
theorem bl_uniform_midpoint_majorant
    {d : ℕ} {U W : Set (EuclideanSpace ℝ (Fin d))}
    {V F : EuclideanSpace ℝ (Fin d) → ℝ}
    (hU : Bornology.IsBounded U) (hc : Convex ℝ U)
    (hW : IsOpen W) (hUW : closure U ⊆ W)
    (hV : ContDiffOn ℝ 2 V W) (hF : ContDiffOn ℝ 2 F W)
    {κ : ℝ} (hκ : 0 < κ)
    (hb : ∀ x ∈ U, ∀ h, κ * ‖h‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x h h)
    {a : ℝ} (ha : 0 < a) :
    ∃ ε₀ > 0, ∀ ε : ℝ, |ε| < ε₀ → ∀ z ∈ U,
      ∀ h : EuclideanSpace ℝ (Fin d), z + h ∈ U → z - h ∈ U →
      ε / 2 * (F (z + h) - F (z - h)) -
          (V (z + h) + V (z - h)) / 2 + V z ≤
        ε ^ 2 / 2 * sSup (Set.range (fun v : EuclideanSpace ℝ (Fin d) =>
          2 * fderiv ℝ F z v - fderiv ℝ (fderiv ℝ V) z v v)) + a * ε ^ 2 := by
  have hFc : ContinuousOn (fderiv ℝ F) (closure U) :=
    (hF.continuousOn_fderiv_of_isOpen hW (by norm_num)).mono hUW
  obtain ⟨M, hM⟩ := (hU.isCompact_closure.image_of_continuousOn hFc).isBounded.exists_norm_le
  let L : ℝ := max M 0 + 1
  have hLpos : 0 < L := by dsimp [L]; positivity
  have hL : ∀ x ∈ U, ‖fderiv ℝ F x‖ ≤ L := by
    intro x hx
    exact (hM _ (mem_image_of_mem _ (subset_closure hx))).trans
      (by dsimp [L]; linarith [le_max_left M 0])
  let C : ℝ := 2 * L / κ
  have hC : 0 < C := by dsimp [C]; positivity
  have hCκ : κ * C = 2 * L := by dsimp [C]; field_simp
  let η : ℝ := a / (C + C ^ 2 + 1)
  have hη : 0 < η := by dsimp [η]; positivity
  have hηa : η * (C + C ^ 2) ≤ a := by
    have he : η * (C + C ^ 2 + 1) = a := by
      dsimp [η]
      field_simp
    nlinarith
  obtain ⟨δ, hδ, hTaylor⟩ := bl_uniform_midpoint_remainder
    hU.isCompact_closure hc.closure hW hUW hV hF hη
  refine ⟨δ / (C + 1), by positivity, ?_⟩
  intro ε hε z hz h hp hm
  let A : ℝ := ε / 2 * (F (z + h) - F (z - h)) -
    (V (z + h) + V (z - h)) / 2 + V z
  let Q : ℝ := sSup (Set.range (fun v : EuclideanSpace ℝ (Fin d) =>
    2 * fderiv ℝ F z v - fderiv ℝ (fderiv ℝ V) z v v))
  have hQ : 0 ≤ Q := by
    have ht := (bl_variational_energy_bounds (fderiv ℝ (fderiv ℝ V) z)
      ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm (fderiv ℝ F z))
      hκ (hb z hz)).1
    simpa only [InnerProductSpace.toDual_symm_apply] using ht
  change A ≤ ε ^ 2 / 2 * Q + a * ε ^ 2
  by_cases hA : A ≤ 0
  · exact hA.trans (by positivity)
  have hApos : 0 < A := lt_of_not_ge hA
  have hg : A ≤ |ε| * L * ‖h‖ - κ / 2 * ‖h‖ ^ 2 :=
    bl_midpoint_global_bound hc hW (subset_closure.trans hUW) hV hF hb hL hp hm ε
  have hr : ‖h‖ ≤ C * |ε| := by
    by_contra hn
    have hn' : C * |ε| < ‖h‖ := lt_of_not_ge hn
    have hrpos : 0 < ‖h‖ := lt_of_le_of_lt (by positivity) hn'
    have hfac : 0 < ‖h‖ * (κ * ‖h‖ - 2 * L * |ε|) := by
      apply mul_pos hrpos
      nlinarith [mul_lt_mul_of_pos_left hn' hκ]
    nlinarith
  have hsmall : ‖h‖ < δ := by
    have ht := (lt_div_iff₀ (by positivity : 0 < C + 1)).mp hε
    nlinarith [abs_nonneg ε]
  have ht := (le_abs_self _).trans (hTaylor z (subset_closure hz) h
    (subset_closure hp) (subset_closure hm) hsmall ε)
  have hquad := bl_scaled_variational_bound (fderiv ℝ (fderiv ℝ V) z)
    (fderiv ℝ F z) hκ (hb z hz) ε h
  have he : η * (|ε| * ‖h‖ + ‖h‖ ^ 2) ≤ a * ε ^ 2 := by
    calc
      _ ≤ η * (|ε| * (C * |ε|) + (C * |ε|) ^ 2) := by gcongr
      _ = (η * (C + C ^ 2)) * ε ^ 2 := by rw [← sq_abs ε]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hηa (sq_nonneg ε)
  dsimp [A, Q] at *
  linarith

end Riesz1

end
