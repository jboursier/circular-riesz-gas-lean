/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.APrioriFinalCircle
public import Riesz1.Variance.RegMicroFarRatesKernel

/-!
# Converting microscopic derivatives to the a priori envelope

The marked pieces of Lemma 5.3 have fixed support.
The smooth remainder has either compact support or a bounded circle.
These facts convert the derivative estimates into the actual
majorant used by the proved spatial a priori theorem.
-/

public section

open Set Filter Topology

namespace Riesz1.Internal

/-- The central representative realizes circular distance. -/
theorem regMicro_abs_centralRep_eq_dist (L : Length) (x : Circle L) :
    |centralRep L x| = dist x 0 := by
  have : Fact (0 < L.val) := ⟨L.property⟩
  have hc : ((centralRep L x : ℝ) : Circle L) = x := AddCircle.coe_equivIco
  have hm := (AddCircle.equivIco L.val (-L.val/2) x).property
  have hb : |centralRep L x| ≤ |L.val|/2 := by
    rw [abs_of_pos L.property, abs_le]
    exact ⟨by dsimp only [centralRep]; linarith [hm.1], by
      change (AddCircle.equivIco L.val (-L.val/2) x).val ≤ L.val/2
      linarith [hm.2]⟩
  rw [dist_zero_right]
  conv_rhs => rw [← hc]
  exact ((AddCircle.norm_coe_eq_abs_iff L.val L.property.ne').mpr hb).symm

/-- In particular translated real coordinates give distance to the mark. -/
theorem regMicro_abs_centralRep_sub (L : Length) (u c : ℝ) :
    |centralRep L ((u-c : ℝ) : Circle L)| =
      dist (u : Circle L) (c : Circle L) := by
  rw [regMicro_abs_centralRep_eq_dist, dist_zero_right, AddCircle.coe_sub, dist_eq_norm]

/-- A supported function is locally zero strictly outside its support ball.
No regularity of the function is needed at those points. -/
theorem regMicro_deriv_zero_outside (L : Length) (f : Circle L → ℝ) (c R x : ℝ)
    (hsupp : ∀ z, R ≤ dist z (c : Circle L) → f z = 0)
    (hx : R < dist (x : Circle L) (c : Circle L)) :
    deriv (fun t : ℝ => f (t : Circle L)) x = 0 := by
  have he : (fun t : ℝ => f (t : Circle L)) =ᶠ[𝓝 x] fun _ => 0 := by
    have hcont : Continuous (fun t : ℝ => dist (t : Circle L) (c : Circle L)) :=
      continuous_quot_mk.dist continuous_const
    filter_upwards [hcont.continuousAt.eventually (lt_mem_nhds hx)] with t ht
    exact hsupp _ ht.le
  exact he.deriv_eq.trans (deriv_const x 0)

/-- Reciprocal powers on a radius-two support are bounded by the
closed-indicator majorant, including the boundary at distance two. -/
theorem regMicro_power_to_majorant (L : Length) (K lam s A c : ℝ)
    (hK : 0 < K) (hA : 0 ≤ A) (f : Circle L → ℝ)
    (hsupp : ∀ z, 2 ≤ dist z (c : Circle L) → f z = 0)
    (hd : ∀ x, |deriv (fun t : ℝ => f (t : Circle L)) x| ≤
      A * (max (dist (x : Circle L) (c : Circle L)) K⁻¹)^(-(1+lam))) :
    ∀ x, |deriv (fun t : ℝ => f (t : Circle L)) x| ≤
      A * cutoffMajorant s lam K |centralRep L ((x-c : ℝ) : Circle L)| := by
  intro x
  rw [regMicro_abs_centralRep_sub]
  by_cases hx : dist (x : Circle L) (c : Circle L) ≤ 2
  · apply (hd x).trans
    apply mul_le_mul_of_nonneg_left _ hA
    have hp : 0 < max (dist (x : Circle L) (c : Circle L)) K⁻¹ :=
      lt_of_lt_of_le (inv_pos.mpr hK) (le_max_right _ _)
    rw [cutoffMajorant, majorantNear, ite_eq_left hx, Real.rpow_neg hp.le, one_div]
    exact le_add_of_nonneg_right (majorantFar_nonneg _ _)
  · rw [regMicro_deriv_zero_outside L f c 2 x hsupp (lt_of_not_ge hx), abs_zero]
    exact mul_nonneg hA (cutoffMajorant_nonneg hK _)

/-- On a fixed bounded region the a priori majorant has a uniform
positive lower bound. The constant is independent of the scale. -/
theorem regMicro_one_le_majorant {K R t s lam : ℝ}
    (hK : 1 ≤ K) (hlam : 0 ≤ lam) (hs : s ≤ 3)
    (_ht : 0 ≤ t) (hR : t ≤ R) :
    1 ≤ ((max R 2)^(1+lam) + (max R 2)^(3-s)) * cutoffMajorant s lam K t := by
  have hK0 : 0 < K := by linarith
  have hB : 0 < max R 2 := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (le_max_right _ _)
  have hnear := majorantNear_nonneg (lam := lam) hK0 t
  have hfar := majorantFar_nonneg s t
  by_cases ht2 : t ≤ 2
  · have hz : 0 < max t K⁻¹ := lt_of_lt_of_le (inv_pos.mpr hK0) (le_max_right _ _)
    have hzB : max t K⁻¹ ≤ max R 2 := max_le (hR.trans (le_max_left _ _))
      ((inv_le_one_of_one_le₀ hK).trans (by linarith [le_max_right R 2]))
    have hp := Real.rpow_le_rpow hz.le hzB (by linarith : 0 ≤ 1+lam)
    have hdiv : 1 ≤ (max R 2)^(1+lam) / (max t K⁻¹)^(1+lam) :=
      (one_le_div (Real.rpow_pos_of_pos hz _)).mpr hp
    have he : majorantNear lam K t = 1 / (max t K⁻¹)^(1+lam) := by
      rw [majorantNear, ite_eq_left ht2]
    rw [div_eq_mul_one_div, ← he] at hdiv
    exact hdiv.trans (mul_le_mul (le_add_of_nonneg_right (Real.rpow_nonneg hB.le (3-s)))
      (le_add_of_nonneg_right hfar) hnear (by positivity))
  · have ht0 : 0 < t := by linarith
    have hp := Real.rpow_le_rpow ht0.le (hR.trans (le_max_left R 2)) (by linarith : 0 ≤ 3-s)
    have hdiv : 1 ≤ (max R 2)^(3-s) / t^(3-s) :=
      (one_le_div (Real.rpow_pos_of_pos ht0 _)).mpr hp
    have he : majorantFar s t = 1 / t^(3-s) := by
      rw [majorantFar, ite_eq_left (by linarith)]
    rw [div_eq_mul_one_div, ← he] at hdiv
    exact hdiv.trans (mul_le_mul (le_add_of_nonneg_left (Real.rpow_nonneg hB.le (1+lam)))
      (le_add_of_nonneg_left hnear) hfar (by positivity))

/-- A bounded derivative with fixed support has the correct a priori
envelope. Alternatively it suffices that the circle itself is bounded. -/
theorem regMicro_bounded_to_majorant (L : Length) (K R s lam A : ℝ)
    (hK : 1 ≤ K) (hlam : 0 ≤ lam) (hs : s ≤ 3) (hA : 0 ≤ A)
    (f : Circle L → ℝ)
    (hsupp : L.val/2 ≤ R ∨ (∀ z, R ≤ dist z 0 → f z = 0))
    (hd : ∀ x, |deriv (fun t : ℝ => f (t : Circle L)) x| ≤ A) :
    ∀ x, |deriv (fun t : ℝ => f (t : Circle L)) x| ≤
      (A * ((max R 2)^(1+lam)+(max R 2)^(3-s))) *
        cutoffMajorant s lam K |centralRep L (x : Circle L)| := by
  intro x
  rw [regMicro_abs_centralRep_eq_dist]
  by_cases hx : dist (x : Circle L) 0 ≤ R
  · calc
      _ ≤ A := hd x
      _ ≤ A * (((max R 2)^(1+lam)+(max R 2)^(3-s)) *
          cutoffMajorant s lam K (dist (x : Circle L) 0)) :=
        le_mul_of_one_le_right hA (regMicro_one_le_majorant hK hlam hs dist_nonneg hx)
      _ = _ := by ring
  · have hzero : deriv (fun t : ℝ => f (t : Circle L)) x = 0 := by
      rcases hsupp with hL | hf
      · have hb := AddCircle.norm_le_half_period L.val L.property.ne' (x := (x : Circle L))
        rw [abs_of_pos L.property] at hb
        exact (hx ((show dist (x : Circle L) 0 ≤ L.val/2 by simpa using hb).trans hL)).elim
      · exact regMicro_deriv_zero_outside L f 0 R x (by simpa using hf) (lt_of_not_ge hx)
    rw [hzero, abs_zero]
    exact mul_nonneg (mul_nonneg hA (by positivity)) (cutoffMajorant_nonneg (by linarith) _)

end Riesz1.Internal
