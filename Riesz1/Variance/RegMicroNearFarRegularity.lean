/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.RegMicroNearFarCutoffs
public import Riesz1.Variance.RegMicroKernelDifferentiable
public import Riesz1.ToMathlib.PeriodicConvolutionLocalC1
public import Riesz1.CLT.IdentityDefs

/-!
# Continuously differentiable far representatives

Local `C¹` regularity of the actual inverse-transport
representative, followed by the fixed and moving cutoff products. The
representative equals the original regularization error almost everywhere
in the fundamental cell. No derivative estimate is made a hypothesis.
-/

public section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace Riesz1.Internal

/-- The actual inverse convolution is locally `C¹` off the transport marks. -/
theorem inverseConv_contDiffAt_of_transport (P : Parameters) (L : Length)
    {ι : Type*} [Finite ι] (marks : ι → ℝ) (ψ : Circle L → ℝ)
    (hi : LocallyIntegrable (deriv (fun t : ℝ => ψ (t : Circle L))) volume)
    (hψ : ∀ x : ℝ, (∀ j, (x : Circle L) ≠ (marks j : Circle L)) →
      ContDiffAt ℝ 2 (fun t : ℝ => ψ (t : Circle L)) x)
    {x : ℝ} (hx : ∀ j, (x : Circle L) ≠ (marks j : Circle L)) :
    ContDiffAt ℝ 1
        (inverseConv P L.val (deriv (fun t : ℝ => ψ (t : Circle L)))) x := by
  have hper : Function.Periodic (fun t : ℝ => ψ (t : Circle L)) L.val := fun t => by
    dsimp only
    rw [AddCircle.coe_add_period]
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (isOpen_unmarked_lift marks) x hx
  have hq : ContDiffOn ℝ 1 (deriv (fun t : ℝ => ψ (t : Circle L)))
      (Ioo (x - r) (x + r)) := by
    intro y hy
    have hym : ∀ j, (y : Circle L) ≠ (marks j : Circle L) := hball (by
      rw [Metric.mem_ball, Real.dist_eq]
      exact abs_lt.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩)
    exact ((hψ y hym).derivWithin (m := 1) (by norm_num)).contDiffWithinAt
  apply PeriodicConvolution.contDiffAt_of_contDiffOn L.property hr
    (deriv_periodic_of hper) (inverseKernel_periodic P L.property)
    (measurable_deriv _) (measurable_inverseKernel P L.property) hi
    (inverseKernel_locallyIntegrable P L.property) hq
  intro t ht htL
  apply (contDiffAt_inverseKernel P L.property ?_).of_le (by simp)
  intro k hk
  by_cases hk0 : k = 0
  · subst hk0
    exact ht (by simpa only [Int.cast_zero, zero_mul] using hk)
  · have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast Int.one_le_abs hk0
    have hmul : |t| = |(k : ℝ)| * L.val := by rw [hk, abs_mul, abs_of_pos L.property]
    nlinarith [L.property]


/-- The far representatives, supplied from
admissibility. This includes the endpoint exponents. `e` is the actual
inverse-transport error, with the existing circle mollification. -/
theorem reg_micro_near_far_representatives (P : Parameters) (L : Length)
    (η B : ℝ) (hη : 0 < η) (hB : 0 ≤ B)
    (f : {f : Circle L → ℝ // MemLp (fun x => (f x : ℂ)) 2 (arclength L)})
    (n : ℕ+) (a : Fin (n : ℕ) → ℝ) (α C₀ : ℝ)
    (hα0 : P.val.2-1 ≤ α) (hα1 : α < P.val.2/2) (hC₀ : 0 ≤ C₀)
    (hprim : PrimitiveRegularity L η P.val.2 B f)
    (hreg : TransportRegularity P L f n a α C₀)
    (ρ : ℝ → ℝ) (hρ : IsMollifier ρ)
    (r₀ h : ℝ) (hr : 0 < r₀) (hh : 0 < h) (hrL : 4*r₀ < L.val) (hhL : 8*h < L.val)
    (hsep : ∀ i j, i ≠ j → 8*h ≤ dist (a i : Circle L) (a j : Circle L)) :
    ∃ ψ : {g : Circle L → ℝ // MemLp (fun x => (g x : ℂ)) 2 (arclength L)},
      Continuous ψ.val ∧
      (∀ k : ℤ, coeff L ⟨fun x => (ψ.val x : ℂ), complexL2Integrable L _ ψ.property⟩ k =
        transportCoeffs P L f k) ∧
      let m := (∫ y in Ioc (-(L.val/2)) (L.val/2), f.val (y : Circle L))/L.val
      let q := deriv (fun t : ℝ => ψ.val (t : Circle L))
      let e := fun z : Circle L => m + inverseConvCircle P L q z - cltRegCircle hρ L hh f z
      (∀ᵐ x : ℝ ∂(volume.restrict (Ioc (-(L.val/2)) (L.val/2))),
        e (x : Circle L) = f.val (x : Circle L) -
          circleMollify ρ L.val h (fun t => f.val (t : Circle L)) x) ∧
      (∀ j, ContDiff ℝ 1 (fun x : ℝ => microFarError L.val r₀ h a e j (x : Circle L))) ∧
      ContDiff ℝ 1 (fun x : ℝ => microFarRemainder L.val r₀ h a e (x : Circle L)) := by
  obtain ⟨ψ, hc, hcoeff, hi, _hAC, hs, hrep, _hmoll⟩ :=
    regMicroKernel_profile_representation P L η B hη hB f n a α C₀
      hα0 hα1 hC₀ hprim hreg
  refine ⟨ψ, hc, hcoeff, ?_⟩
  dsimp only
  let m := (∫ y in Ioc (-(L.val/2)) (L.val/2), f.val (y : Circle L))/L.val
  let q := deriv (fun t : ℝ => ψ.val (t : Circle L))
  let e := fun z : Circle L => m + inverseConvCircle P L q z - cltRegCircle hρ L hh f z
  have he (x : ℝ) (hx : ∀ j, (x : Circle L) ≠ (a j : Circle L)) :
      ContDiffAt ℝ 1 (fun t : ℝ => e (t : Circle L)) x := by
    have hinv := inverseConv_contDiffAt_of_transport P L a ψ.val hi hs hx
    have heq : (fun t : ℝ => e (t : Circle L)) =
        fun t => m + inverseConv P L.val q t - cltRegCircle hρ L hh f (t : Circle L) := by
      funext t
      exact congrArg (fun z => m+z-cltRegCircle hρ L hh f (t : Circle L))
        (inverseConvCircle_coe P L q t)
    rw [heq]
    exact (contDiffAt_const.add hinv).sub
      ((cltRegCircle_contDiff hρ L hh f).of_le (by simp : (1 : ℕ∞ω) ≤ ∞)).contDiffAt
  refine ⟨?_, microFarErrors_contDiff L.property hr hh hrL hhL a hsep e he⟩
  filter_upwards [hrep] with x hx
  change m + inverseConvCircle P L q (x : Circle L) - cltRegCircle hρ L hh f (x : Circle L) = _
  rw [inverseConvCircle_coe, cltRegCircle_coe]
  rw [hx]

end Riesz1.Internal
