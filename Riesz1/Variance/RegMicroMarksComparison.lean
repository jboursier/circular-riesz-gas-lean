/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.RegMicroMarksKernel
public import Riesz1.Variance.RegTransportBoundsComparison
public import Riesz1.ToMathlib.SmoothWindowIntegral

/-!
# Smooth comparison through the support of a compact profile

The transports on different observation circles
have the same possible interior singularities. Their difference is smooth
through the support, with every derivative bounded before either scale.
-/

public section

open MeasureTheory Set Filter
open scoped Topology ContDiff

namespace Riesz1.Internal

/-- Strengthening of the Lipschitz comparison to every derivative.
The representatives are identified by their actual Fourier coefficients.
The coefficient precedes both observation scales. -/
theorem regMicro_transport_difference_smooth (P : Parameters) (p : Profile)
    {r σ : ℝ} (hr : 0 < r) (hσ : σ < 1/2) (hrσ : r < σ)
    (hsupp : ∀ᵐ y : ℝ, r ≤ |y| → zeroExtension p y = 0) :
    ∃ C : ℕ → ℝ, (∀ m, 0 < C m) ∧ ∀ (a a' : Scale)
      (ψ : Circle (observationLength a) → ℝ)
      (ψ' : Circle (observationLength a') → ℝ), Continuous ψ → Continuous ψ' →
      ∀ (hψ : MemLp (fun x => (ψ x : ℂ)) 2 (arclength (observationLength a)))
        (hψ' : MemLp (fun x => (ψ' x : ℂ)) 2 (arclength (observationLength a'))),
      (∀ k, coeff (observationLength a)
        ⟨(fun x => (ψ x : ℂ)), complexL2Integrable _ _ hψ⟩ k =
        transportCoeffs P (observationLength a)
          ⟨periodizedProfile p (observationLength a), periodizedProfileL2 p a⟩ k) →
      (∀ k, coeff (observationLength a')
        ⟨(fun x => (ψ' x : ℂ)), complexL2Integrable _ _ hψ'⟩ k =
        transportCoeffs P (observationLength a')
          ⟨periodizedProfile p (observationLength a'), periodizedProfileL2 p a'⟩ k) →
      let F := fun x : ℝ => ψ (x : Circle (observationLength a)) -
        ψ' (x : Circle (observationLength a'))
      ContDiffOn ℝ ∞ F (Ioo (-σ) σ) ∧
      ∀ m x, x ∈ Ioo (-σ) σ → ‖iteratedDeriv m F x‖ ≤ C m := by
  let θ := (σ+r+1)/2
  have hθ : 0 < θ := by dsimp [θ]; linarith
  have hθ1 : θ < 1 := by dsimp [θ]; linarith
  have hwin : σ+r < θ := by dsimp [θ]; linarith
  obtain ⟨D, hD, hkernel⟩ := regMicro_scaledKernel_smooth_difference
    P.property.2.1 P.property.2.2 hθ hθ1
  let Z := ∫ y in Ioc (-r) r, |zeroExtension p y|
  let A := transportConst P.val.1 P.val.2
  let C := fun m => |A| * (D m*Z)+1
  have hZ : 0 ≤ Z := integral_nonneg fun _ => abs_nonneg _
  have hC (m : ℕ) : 0 < C m := by
    dsimp [C]
    linarith [mul_nonneg (abs_nonneg A) (mul_nonneg (hD m).le hZ)]
  refine ⟨C, hC, fun a a' ψ ψ' hc hc' hψ hψ' hcoeff hcoeff' => ?_⟩
  let L := observationLength a
  let T := observationLength a'
  have hL : 1 ≤ L.val := (one_le_inv₀ a.property.1).mpr a.property.2
  have hT : 1 ≤ T.val := (one_le_inv₀ a'.property.1).mpr a'.property.2
  obtain ⟨H, hH, hbH, heH⟩ := hkernel L.val T.val hL hT
  have hζ := (zeroExtension_integrableOn p L).1.mono_set
    (show Ioc (-r) r ⊆ Ioc (-(L.val/2)) (L.val/2) from
      fun y hy => ⟨by linarith [hy.1], by linarith [hy.2]⟩)
  let G := fun x => ∫ y in Ioc (-r) r, zeroExtension p y*H (x-y)
  obtain ⟨hG, hGder⟩ := smooth_windowIntegral hwin hζ hH D hbH
  have hae : (fun x : ℝ => ψ (x : Circle L)-ψ' (x : Circle T)) =ᵐ[
      volume.restrict (Ioo (-σ) σ)] fun x => A*G x := by
    filter_upwards [transport_ae_convolution_inner P p a ψ hψ hcoeff hσ,
      transport_ae_convolution_inner P p a' ψ' hψ' hcoeff' hσ,
      ae_integrable_transport_window P p a (hrσ.trans hσ) hσ,
      ae_integrable_transport_window P p a' (hrσ.trans hσ) hσ,
      ae_restrict_mem measurableSet_Ioo] with x hx hx' hi hi' hxσ
    rw [hx, hx', transportConv_eq_window (by linarith : r ≤ L.val/2) hsupp,
      transportConv_eq_window (by linarith : r ≤ T.val/2) hsupp]
    simp only [windowConv, iteratedDeriv_zero]
    rw [← mul_sub, ← integral_sub hi hi']
    congr 1
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      ae_restrict_of_ae ((Set.countable_singleton x).ae_notMem volume)] with y hy hyx
    have hxy : |x-y| < θ := (abs_sub x y).trans_lt (by
      linarith [abs_lt.mpr hxσ, abs_le.mpr (Ioc_subset_Icc_self hy)])
    rw [← mul_sub, heH (x-y) hxy (sub_ne_zero.mpr (Ne.symm hyx))]
  have hAG : ContDiffOn ℝ ∞ (fun x => A*G x) (Ioo (-σ) σ) := contDiffOn_const.mul hG
  have heq := Measure.eqOn_open_of_ae_eq hae isOpen_Ioo
    ((hc.comp (AddCircle.continuous_mk' L.val)).sub
      (hc'.comp (AddCircle.continuous_mk' T.val))).continuousOn hAG.continuousOn
  refine ⟨hAG.congr heq, fun m x hx => ?_⟩
  rw [heq.iteratedDeriv_of_isOpen isOpen_Ioo m hx]
  change ‖iteratedDeriv m (A • G) x‖ ≤ C m
  rw [iteratedDeriv_const_smul
    ((hG.contDiffAt (isOpen_Ioo.mem_nhds hx)).of_le (by simp)) A, smul_eq_mul, norm_mul,
    Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left (hGder m x hx).2 (abs_nonneg A)).trans
    (by dsimp [C, Z]; linarith)

end Riesz1.Internal
