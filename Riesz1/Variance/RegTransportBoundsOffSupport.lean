/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Kernel.AdmissibilityRegularityKernel

/-!
# Quantitative transport bounds at a fixed distance from the support

The kernel derivative bound controls all positive derivative orders at every central
point separated from the compact support by a fixed margin. The constant precedes
the circle length. This makes quantitative the off-support step in the proof of
Lemma 5.1, including points with absolute value below one.
-/

public section

open MeasureTheory Set
open scoped ContDiff

namespace Riesz1.Internal

/-- A central point outside a fixed window stays separated from every periodic image
of that window. The lower bound uses its actual distance from the window. -/
theorem window_separation_of_central {L ρ d x y : ℝ}
    (hd : 0 < d) (hρ : 0 ≤ ρ) (hx : ρ + d ≤ |x|) (hxL : |x| ≤ L / 2)
    (hy : |y| ≤ ρ) (k : ℤ) : d ≤ |x - y - k * L| := by
  have hL : 0 < L := by linarith [abs_nonneg x]
  have hxy : |x| ≤ |x - y| + |y| := by
    simpa only [sub_add_cancel] using abs_add_le (x - y) y
  by_cases hk : k = 0
  · subst hk
    simp only [Int.cast_zero, zero_mul, sub_zero]
    linarith
  · have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast Int.one_le_abs hk
    have hkL : L ≤ |(k : ℝ) * L| := by
      rw [abs_mul, abs_of_pos hL]
      nlinarith
    have htri := abs_sub x y
    have hh := abs_sub_abs_le_abs_sub ((k : ℝ) * L) (x - y)
    rw [abs_sub_comm ((k : ℝ) * L) (x - y)] at hh
    linarith

/-- Every positive derivative order has a uniform off-support bound on central
representatives, even in the bounded region where the kernel tail estimate does not
apply. This internal helper quantifies over representatives with the `transportCoeffs`
coefficients. -/
theorem uniform_transport_deriv_off_support (P : Parameters) (m : ℕ) (hm : 1 ≤ m) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : Profile) (a : Scale)
      (ψ : Circle (observationLength a) → ℝ), Continuous ψ →
      ∀ hψ : MemLp (fun x => (ψ x : ℂ)) 2 (arclength (observationLength a)),
      (∀ k : ℤ, coeff (observationLength a)
        ⟨(fun x => (ψ x : ℂ)), complexL2Integrable _ _ hψ⟩ k =
        transportCoeffs P (observationLength a)
          ⟨periodizedProfile p (observationLength a), periodizedProfileL2 p a⟩ k) →
      ∀ ρ d x : ℝ, 0 < ρ → ρ < 1 / 2 → 0 < d →
        (∀ᵐ y : ℝ, ρ ≤ |y| → zeroExtension p y = 0) →
        ρ + d ≤ |x| → |x| ≤ (observationLength a).val / 2 →
        ContDiffAt ℝ ∞ (fun t : ℝ => ψ (t : Circle (observationLength a))) x ∧
        ‖iteratedDeriv m (fun t : ℝ => ψ (t : Circle (observationLength a))) x‖ ≤
          C * (∫ y : ℝ, |zeroExtension p y|) * d ^ (P.val.2 - 1 - (m : ℝ)) := by
  obtain ⟨D, hD, hkernel⟩ := norm_iteratedDeriv_scaledKernel_le
    P.property.2.1 P.property.2.2 hm
  let C := |transportConst P.val.1 P.val.2| * D
  have hC : 0 < C := mul_pos
    (abs_pos.mpr (transportConst_ne_zero P.property.1 P.property.2.1 P.property.2.2)) hD
  refine ⟨C, hC, fun p a ψ hc hψ hcoeff ρ d x hρ hρ1 hd hsupp hx hxL => ?_⟩
  let L := observationLength a
  have hL1 : 1 ≤ L.val := (one_le_inv₀ a.property.1).mpr a.property.2
  have hxoff : ∀ k : ℤ, ∀ y ∈ Icc (-ρ) ρ, x ≠ y + k * L.val := by
    intro k y hy he
    have hh := window_separation_of_central hd hρ.le hx hxL (abs_le.mpr hy) k
    rw [show x - y - k * L.val = 0 by linarith, abs_zero] at hh
    linarith
  have heq := transport_eventuallyEq_convolution P p a ψ hc hψ hcoeff hρ hρ1 hsupp hxoff
  have hsmooth := (transport_kernel_scaled P p a).2.2.2.1 ρ hρ hρ1 hsupp x hxoff
  refine ⟨hsmooth.congr_of_eventuallyEq heq, ?_⟩
  rw [heq.iteratedDeriv_eq m]
  have hζ := (zeroExtension_integrableOn p L).1.mono_set
    (show Ioc (-ρ) ρ ⊆ Ioc (-(L.val / 2)) (L.val / 2) from
      fun y hy => ⟨by linarith [hy.1], by linarith [hy.2]⟩)
  obtain ⟨η, hη, hsep⟩ := exists_separation L.property hxoff
  rw [iteratedDeriv_transportConv_of_mem (β := P.val.1) P.property.2.1 P.property.2.2
    L.property (by linarith : ρ ≤ L.val / 2) hsupp hζ hη Metric.isOpen_ball hsep m x
    (Metric.mem_ball_self hη), norm_mul, Real.norm_eq_abs]
  have hexp : P.val.2 - 1 - (m : ℝ) ≤ 0 := by
    have hh : (1 : ℝ) ≤ m := by exact_mod_cast hm
    linarith [P.property.2.2]
  have hW : ‖windowConv P.val.2 L.val ρ (zeroExtension p) m x‖ ≤
      D * d ^ (P.val.2 - 1 - (m : ℝ)) * (∫ y in Ioc (-ρ) ρ, |zeroExtension p y|) := by
    unfold windowConv
    rw [← integral_const_mul]
    apply norm_integral_le_of_norm_le (hζ.abs.const_mul _)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    have hy' : |y| ≤ ρ := abs_le.mpr (Ioc_subset_Icc_self hy)
    have hdist : d ≤ latticeDist L.val (x - y) :=
      le_latticeDist (window_separation_of_central hd hρ.le hx hxL hy')
    have hnot : ∀ k : ℤ, x - y ≠ k * L.val := by
      intro k he
      have hh := window_separation_of_central hd hρ.le hx hxL hy' k
      rw [he, sub_self, abs_zero] at hh
      linarith
    rw [norm_mul, Real.norm_eq_abs]
    have hh := (hkernel L.val (x - y) L.property hnot).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hd hdist hexp) hD.le)
    nlinarith [mul_le_mul_of_nonneg_left hh (abs_nonneg (zeroExtension p y))]
  have hint : (∫ y in Ioc (-ρ) ρ, |zeroExtension p y|) = ∫ y : ℝ, |zeroExtension p y| := by
    apply MeasureTheory.setIntegral_eq_integral_of_ae_compl_eq_zero
    filter_upwards [hsupp] with y hy hyn
    rw [hy (le_abs_of_not_mem_Ioc hyn), abs_zero]
  rw [hint] at hW
  have hh := mul_le_mul_of_nonneg_left hW (abs_nonneg (transportConst P.val.1 P.val.2))
  simpa only [C, Real.norm_eq_abs, mul_assoc, mul_comm, mul_left_comm] using hh

end Riesz1.Internal
