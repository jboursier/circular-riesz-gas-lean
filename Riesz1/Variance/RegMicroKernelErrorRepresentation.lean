/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.RegMicroKernelDifferentiable
public import Riesz1.ToMathlib.PeriodicConvolutionSmoothing
public import Riesz1.ToMathlib.MollifierPointwise.Smoothing

/-!
# The actual profile error as convolution by the error kernel

Smoothing the inverse representative commutes with convolution by its
integrable kernel. Consequently the actual profile regularization error
equals `(P_L - P_L * ρ_h) * ψ'` at every unmarked point, with absolute
integrability and equality of classical derivatives there. This establishes
the error-convolution identification step in the proof of Lemma 5.3.
-/

public section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace Riesz1

/-- Smoothing an inverse convolution can be moved onto its kernel, pointwise.
The input need only be integrable on a period. -/
theorem circleMollify_inverseConv (P : Parameters) {ρ q : ℝ → ℝ}
    (hρ : IsMollifier ρ) {L h : ℝ} (hL : 0 < L) (hh : 0 < h) (hhL : h ≤ L)
    (hq : IntegrableOn q (Ioc (-(L / 2)) (L / 2))) (x : ℝ) :
    circleMollify ρ L h (inverseConv P L q) x =
      ∫ y in Ioc (-(L / 2)) (L / 2),
        q y * mollifyLine ρ h (inverseKernel P L) (x - y) := by
  have he := circleMollify_periodic_convolution hρ hL hh hhL
    (inverseKernel_periodic P hL) (measurable_inverseKernel P hL) hq
    (integrableOn_inverseKernel_cell P hL) x
  simp_rw [circleMollify_eq_mollifyLine hρ hL hh
    (inverseKernel_locallyIntegrable P hL) (inverseKernel_periodic P hL)] at he
  exact he

/-- The convolution with the smoothed inverse kernel is absolutely integrable
at every point, even at the marks of the input. -/
theorem integrableOn_mul_mollify_inverseKernel (P : Parameters) {ρ q : ℝ → ℝ}
    (hρ : IsMollifier ρ) {L h : ℝ} (hL : 0 < L) (hh : 0 < h)
    (hq : IntegrableOn q (Ioc (-(L / 2)) (L / 2))) (x : ℝ) :
    IntegrableOn (fun y => q y * mollifyLine ρ h (inverseKernel P L) (x - y))
      (Ioc (-(L / 2)) (L / 2)) := by
  have hfun : circleMollify ρ L h (inverseKernel P L) =
      mollifyLine ρ h (inverseKernel P L) :=
    funext (circleMollify_eq_mollifyLine hρ hL hh
      (inverseKernel_locallyIntegrable P hL) (inverseKernel_periodic P hL))
  have hp := Internal.circleMollify_periodic hρ hL hh
    (inverseKernel_locallyIntegrable P hL) (inverseKernel_periodic P hL)
  rw [hfun] at hp
  exact PeriodicConvolution.integrable_mul_continuous hL hq
    (contDiff_mollifyLine_of_locallyIntegrable hρ hh
      (inverseKernel_locallyIntegrable P hL)).continuous hp x

namespace Internal

/-- Algebraic error identity where the unsmoothed inverse integral is
absolutely integrable. This internal helper does not infer that certificate
from an a.e. representative equality. -/
theorem inverseConv_sub_smoothing_of_integrable (P : Parameters) {ρ q : ℝ → ℝ}
    (hρ : IsMollifier ρ) {L h x : ℝ} (hL : 0 < L) (hh : 0 < h) (hhL : h ≤ L)
    (hq : IntegrableOn q (Ioc (-(L / 2)) (L / 2)))
    (hx : IntegrableOn (fun y => q y * inverseKernel P L (x - y))
      (Ioc (-(L / 2)) (L / 2))) :
    IntegrableOn (fun y => q y *
      (inverseKernel P L (x - y) - mollifyLine ρ h (inverseKernel P L) (x - y)))
      (Ioc (-(L / 2)) (L / 2)) ∧
    inverseConv P L q x - circleMollify ρ L h (inverseConv P L q) x =
      ∫ y in Ioc (-(L / 2)) (L / 2), q y *
        (inverseKernel P L (x - y) - mollifyLine ρ h (inverseKernel P L) (x - y)) := by
  have hs := integrableOn_mul_mollify_inverseKernel P hρ hL hh hq x
  constructor
  · refine (hx.sub hs).congr (ae_of_all _ fun y => ?_)
    change q y * inverseKernel P L (x - y) -
      q y * mollifyLine ρ h (inverseKernel P L) (x - y) = _
    dsimp only
    rw [mul_sub]
  · rw [circleMollify_inverseConv P hρ hL hh hhL hq x]
    simp_rw [mul_sub]
    exact (integral_sub hx hs).symm

end Internal

/-- (A1)–(A3) of Assumption 1.1 identify the actual smoothing error with convolution by
the error kernel, pointwise off the marks. Its integral is absolutely
convergent there and its derivative is the actual classical error derivative.
No pointwise bound or error identity is an assumption. -/
theorem regMicroKernel_profile_error_representation (P : Parameters) (L : Length)
    (η B : ℝ) (hη : 0 < η) (hB : 0 ≤ B)
    (f : {f : Circle L → ℝ // MemLp (fun x => (f x : ℂ)) 2 (arclength L)})
    (n : ℕ+) (marks : Fin (n : ℕ) → ℝ) (α C : ℝ)
    (hα0 : P.val.2 - 1 ≤ α) (hα1 : α < P.val.2 / 2) (hC : 0 ≤ C)
    (hprim : PrimitiveRegularity L η P.val.2 B f)
    (hreg : TransportRegularity P L f n marks α C) :
    ∃ ψ : {g : Circle L → ℝ // MemLp (fun x => (g x : ℂ)) 2 (arclength L)},
      Continuous ψ.val ∧
      (∀ k : ℤ, coeff L
        ⟨(fun x => (ψ.val x : ℂ)), complexL2Integrable L _ ψ.property⟩ k =
          transportCoeffs P L f k) ∧
      (let m := (∫ y in Ioc (-(L.val / 2)) (L.val / 2), f.val (y : Circle L)) / L.val
       let q := deriv (fun t : ℝ => ψ.val (t : Circle L))
       (∀ᵐ x : ℝ ∂(volume.restrict (Ioc (-(L.val / 2)) (L.val / 2))),
         f.val (x : Circle L) = m + inverseConv P L.val q x) ∧
       ∀ (ρ : ℝ → ℝ), IsMollifier ρ → ∀ h : ℝ, 0 < h → h ≤ L.val →
         let E := fun t => inverseKernel P L.val t - mollifyLine ρ h (inverseKernel P L.val) t
         let e := fun t => m + inverseConv P L.val q t -
           circleMollify ρ L.val h (fun y => f.val (y : Circle L)) t
         let v := fun t => ∫ y in Ioc (-(L.val / 2)) (L.val / 2), q y * E (t - y)
         ∀ x : ℝ, (∀ j, (x : Circle L) ≠ (marks j : Circle L)) →
           IntegrableOn (fun y => q y * E (x - y)) (Ioc (-(L.val / 2)) (L.val / 2)) ∧
           e x = v x ∧ DifferentiableAt ℝ v x ∧ deriv e x = deriv v x) := by
  have : Fact (0 < L.val) := ⟨L.property⟩
  obtain ⟨ψ, hc, hcoeff, hi, _hAC, hs, hrep, hmoll⟩ :=
    regMicroKernel_profile_representation P L η B hη hB f n marks α C
      hα0 hα1 hC hprim hreg
  let q := deriv (fun t : ℝ => ψ.val (t : Circle L))
  let m := (∫ y in Ioc (-(L.val / 2)) (L.val / 2), f.val (y : Circle L)) / L.val
  have hqi : IntegrableOn q (Ioc (-(L.val / 2)) (L.val / 2)) :=
    (hi.integrableOn_isCompact isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hconvI := PeriodicConvolution.locallyIntegrable_of_period L.property
    (inverseConv_periodic P L.property q) (integrableOn_inverseConv P L.property hqi)
  refine ⟨ψ, hc, hcoeff, hrep, fun ρ hρ h hh hhL => ?_⟩
  let E := fun t => inverseKernel P L.val t - mollifyLine ρ h (inverseKernel P L.val) t
  let e := fun t => m + inverseConv P L.val q t -
    circleMollify ρ L.val h (fun y => f.val (y : Circle L)) t
  let v := fun t => ∫ y in Ioc (-(L.val / 2)) (L.val / 2), q y * E (t - y)
  have he (t : ℝ) : e t = inverseConv P L.val q t -
      circleMollify ρ L.val h (inverseConv P L.val q) t := by
    dsimp [e]
    rw [hmoll ρ h t, circleMollify_const_add hρ L.property hh hconvI
      (inverseConv_periodic P L.property q) m t]
    ring
  have hv (x : ℝ) (hx : ∀ j, (x : Circle L) ≠ (marks j : Circle L)) :
      IntegrableOn (fun y => q y * E (x - y)) (Ioc (-(L.val / 2)) (L.val / 2)) ∧
        e x = v x := by
    have hcI := (Internal.inverseConv_classical_of_transport P L marks ψ.val hi hs hx).1
    obtain ⟨hEi, hE⟩ := Internal.inverseConv_sub_smoothing_of_integrable P hρ L.property
      hh hhL hqi hcI
    exact ⟨hEi, (he x).trans hE⟩
  change ∀ x : ℝ, (∀ j, (x : Circle L) ≠ (marks j : Circle L)) →
    IntegrableOn (fun y => q y * E (x - y)) (Ioc (-(L.val / 2)) (L.val / 2)) ∧
      e x = v x ∧ DifferentiableAt ℝ v x ∧ deriv e x = deriv v x
  intro x hx
  obtain ⟨hEi, hval⟩ := hv x hx
  have hloc : e =ᶠ[𝓝 x] v := by
    filter_upwards [(isOpen_unmarked_lift marks).mem_nhds hx] with t ht
    exact (hv t ht).2
  have hd := (Internal.inverseConv_classical_of_transport P L marks ψ.val hi hs hx).2
  have hfi : Integrable f.val (arclength L) := (complexL2Integrable L _ f.property).re
  have hfl := Internal.locallyIntegrable_circle_lift hfi
  have hfp : Function.Periodic (fun t : ℝ => f.val (t : Circle L)) L.val := fun t => by
    dsimp only
    rw [AddCircle.coe_add_period]
  have hde : DifferentiableAt ℝ e x :=
    (hd.const_add m).sub ((contDiff_circleMollify hρ L.property hh hfl hfp).differentiable
      (by simp) x)
  exact ⟨hEi, hval, hde.congr_of_eventuallyEq hloc.symm, hloc.deriv_eq⟩

end Riesz1
