/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.SignedPowerRemainder
public import Riesz1.ToMathlib.WindowIntegralLipschitz
public import Riesz1.Kernel.AdmissibilityRegularityKernel

/-!
# Comparing continuous transports through the support

The difference of the transport kernels has no diagonal singularity. Its convolution
is Lipschitz on a fixed neighborhood of the compact support, uniformly in both
circle lengths. Fourier uniqueness transfers this to the actual continuous transports.
This is the bounded-length comparison step of Lemma 5.1.
-/

public section

open MeasureTheory Set Filter
open scoped Topology

namespace Riesz1.Internal

/-- Almost every convolution slice is integrable on the support window. -/
theorem ae_integrable_transport_window (P : Parameters) (p : Profile) (a : Scale)
    {ρ σ : ℝ} (hρ : ρ < 1 / 2) (hσ : σ < 1 / 2) :
    ∀ᵐ x ∂volume.restrict (Ioo (-σ) σ), IntegrableOn
      (fun y => zeroExtension p y * scaledKernel P.val.2 (observationLength a).val (x - y))
      (Ioc (-ρ) ρ) := by
  let L := observationLength a
  have hL : 1 ≤ L.val := (one_le_inv₀ a.property.1).mpr a.property.2
  have hsub : Ioc (-ρ) ρ ⊆ Ioc (-(L.val / 2)) (L.val / 2) := by
    intro y hy
    exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hh := (integrable_kernelRep_prod P.property.2.1 P.property.2.2 L.property
    (zeroExtension_integrableOn p L).1).prod_right_ae
  have hxsub : Ioo (-σ) σ ⊆ Ioc (-(L.val / 2)) (L.val / 2) := by
    intro x hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hxsub hh] with x hx
  have hix : IntegrableOn (fun y => zeroExtension p y * kernelRep P.val.2 L.val (x - y))
      (Ioc (-(L.val / 2)) (L.val / 2)) := hx
  apply (hix.mono_set hsub).congr
  filter_upwards [ae_restrict_of_ae (ae_kernelRep_sub' P.val.2 L.val x)] with y hy
  rw [hy]

/-- Fourier uniqueness identifies the lift and its convolution almost everywhere
on any interval strictly inside the unit central cell. -/
theorem transport_ae_convolution_inner (P : Parameters) (p : Profile) (a : Scale)
    (ψ : Circle (observationLength a) → ℝ)
    (hψ : MemLp (fun x => (ψ x : ℂ)) 2 (arclength (observationLength a)))
    (hcoeff : ∀ k : ℤ, coeff (observationLength a)
      ⟨(fun x => (ψ x : ℂ)), complexL2Integrable _ _ hψ⟩ k =
      transportCoeffs P (observationLength a)
        ⟨periodizedProfile p (observationLength a), periodizedProfileL2 p a⟩ k)
    {σ : ℝ} (hσ : σ < 1 / 2) :
    (fun x : ℝ => ψ (x : Circle (observationLength a))) =ᵐ[volume.restrict (Ioo (-σ) σ)]
      transportConv P.val.1 P.val.2 (observationLength a).val (zeroExtension p) := by
  let L := observationLength a
  have : Fact (0 < L.val) := ⟨L.property⟩
  have hL : 1 ≤ L.val := (one_le_inv₀ a.property.1).mpr a.property.2
  obtain ⟨hconv, hconvCoeff⟩ := (transport_kernel_scaled P p a).2.2.1
  let g : Circle L → ℝ := fun z =>
    transportConv P.val.1 P.val.2 L.val (zeroExtension p) (centralRep L z)
  have heqC := CircleFourier.ae_eq_of_coeff_eq hψ hconv
    (fun k => (hcoeff k).trans (hconvCoeff k).symm)
  have heq : ψ =ᵐ[arclength L] g := by
    filter_upwards [heqC] with z hz using Complex.ofReal_injective hz
  have hh := (AddCircle.measurePreserving_mk L.val (-(L.val / 2))).quasiMeasurePreserving.ae_eq_comp
    (show ψ =ᵐ[volume] g from heq)
  rw [show -(L.val / 2) + L.val = L.val / 2 by ring] at hh
  have hsub : Ioo (-σ) σ ⊆ Ioc (-(L.val / 2)) (L.val / 2) := by
    intro x hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hh] with x hx
  exact hx.trans (transportConv_centralRep _ _ _ _ _)

/-- Transports of the same supported profile on different circles differ by a
uniformly Lipschitz function through the support. The representative premises merely
identify internal analytic objects. The constant precedes both observation scales. -/
theorem uniform_transport_difference_lipschitz (P : Parameters) (p : Profile)
    {ρ σ : ℝ} (hρ : 0 < ρ) (hσ : σ < 1 / 2) (hρσ : ρ < σ)
    (hsupp : ∀ᵐ y : ℝ, ρ ≤ |y| → zeroExtension p y = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a a' : Scale)
      (ψ : Circle (observationLength a) → ℝ) (ψ' : Circle (observationLength a') → ℝ),
      Continuous ψ → Continuous ψ' →
      ∀ (hψ : MemLp (fun x => (ψ x : ℂ)) 2 (arclength (observationLength a)))
        (hψ' : MemLp (fun x => (ψ' x : ℂ)) 2 (arclength (observationLength a'))),
      (∀ k : ℤ, coeff (observationLength a)
        ⟨(fun x => (ψ x : ℂ)), complexL2Integrable _ _ hψ⟩ k =
        transportCoeffs P (observationLength a)
          ⟨periodizedProfile p (observationLength a), periodizedProfileL2 p a⟩ k) →
      (∀ k : ℤ, coeff (observationLength a')
        ⟨(fun x => (ψ' x : ℂ)), complexL2Integrable _ _ hψ'⟩ k =
        transportCoeffs P (observationLength a')
          ⟨periodizedProfile p (observationLength a'), periodizedProfileL2 p a'⟩ k) →
      LipschitzOnWith (Real.toNNReal C)
        (fun x : ℝ => ψ (x : Circle (observationLength a)) -
          ψ' (x : Circle (observationLength a'))) (Ioo (-σ) σ) := by
  let θ := (σ + ρ + 1) / 2
  have hθ : 0 < θ := by dsimp [θ]; linarith
  have hθ1 : θ < 1 := by dsimp [θ]; linarith
  have hσθ : σ + ρ < θ := by dsimp [θ]; linarith
  obtain ⟨D, hD, hkernel⟩ := exists_uniform_scaledKernel_difference
    P.property.2.1 P.property.2.2 hθ hθ1
  let Z := ∫ y in Ioc (-ρ) ρ, |zeroExtension p y|
  let A := transportConst P.val.1 P.val.2
  let C := |A| * (D * Z) + 1
  have hZ : 0 ≤ Z := integral_nonneg fun _ => abs_nonneg _
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, fun a a' ψ ψ' hc hc' hψ hψ' hcoeff hcoeff' => ?_⟩
  let L := observationLength a
  let T := observationLength a'
  have hL : 1 ≤ L.val := (one_le_inv₀ a.property.1).mpr a.property.2
  have hT : 1 ≤ T.val := (one_le_inv₀ a'.property.1).mpr a'.property.2
  obtain ⟨H, hdH, heH⟩ := hkernel L.val T.val hL hT
  have hζ := (zeroExtension_integrableOn p L).1.mono_set
    (show Ioc (-ρ) ρ ⊆ Ioc (-(L.val / 2)) (L.val / 2) from
      fun y hy => ⟨by linarith [hy.1], by linarith [hy.2]⟩)
  let F : ℝ → ℝ := fun x => ∫ y in Ioc (-ρ) ρ, zeroExtension p y * H (x - y)
  have hF := lipschitzOnWith_windowIntegral hD.le hσθ hζ hdH
  have hae : (fun x : ℝ => ψ (x : Circle L) - ψ' (x : Circle T)) =ᵐ[
      volume.restrict (Ioo (-σ) σ)] fun x => A * F x := by
    filter_upwards [transport_ae_convolution_inner P p a ψ hψ hcoeff hσ,
      transport_ae_convolution_inner P p a' ψ' hψ' hcoeff' hσ,
      ae_integrable_transport_window P p a (hρσ.trans hσ) hσ,
      ae_integrable_transport_window P p a' (hρσ.trans hσ) hσ,
      ae_restrict_mem measurableSet_Ioo] with x hx hx' hi hi' hxσ
    rw [hx, hx', transportConv_eq_window (by linarith : ρ ≤ L.val / 2) hsupp,
      transportConv_eq_window (by linarith : ρ ≤ T.val / 2) hsupp]
    simp only [windowConv, iteratedDeriv_zero]
    rw [← mul_sub, ← integral_sub hi hi']
    congr 1
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      ae_restrict_of_ae ((Set.countable_singleton x).ae_notMem volume)] with y hy hyx
    have hxy : |x - y| < θ := (abs_sub x y).trans_lt (by
      have hh := abs_lt.mpr hxσ
      have hh' := abs_le.mpr (Ioc_subset_Icc_self hy)
      linarith)
    rw [← mul_sub, heH (x - y) hxy (sub_ne_zero.mpr (Ne.symm hyx))]
  have hAF : ContinuousOn (fun x => A * F x) (Ioo (-σ) σ) :=
    continuousOn_const.mul hF.continuousOn
  have heq := Measure.eqOn_open_of_ae_eq hae isOpen_Ioo
    ((hc.comp (AddCircle.continuous_mk' L.val)).sub
      (hc'.comp (AddCircle.continuous_mk' T.val))).continuousOn hAF
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx z hz
  have hex : ψ (x : Circle L) - ψ' (x : Circle T) = A * F x := heq hx
  have hez : ψ (z : Circle L) - ψ' (z : Circle T) = A * F z := heq hz
  rw [hex, hez, Real.dist_eq, Real.dist_eq, ← mul_sub, abs_mul]
  have hh := hF.dist_le_mul x hx z hz
  simp only [Real.dist_eq] at hh
  change |F x - F z| ≤ (D * Z) * |x - z| at hh
  rw [Real.coe_toNNReal C hC.le]
  change |A| * |F x - F z| ≤ C * |x - z|
  have hm := mul_le_mul_of_nonneg_left hh (abs_nonneg A)
  dsimp [C]
  nlinarith [abs_nonneg (x - z)]

end Riesz1.Internal
