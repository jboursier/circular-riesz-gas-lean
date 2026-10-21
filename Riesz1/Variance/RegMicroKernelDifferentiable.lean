/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.RegMicroKernelProfileRepresentation
public import Riesz1.Variance.RegMicroKernelShift
public import Riesz1.ToMathlib.PeriodicConvolutionRegularity
public import Riesz1.ToMathlib.CircleMollifyL2
public import Riesz1.ToMathlib.MollifierPointwise.Derivative

/-!
# Classical inverse representatives off the marked points

The inverse-transport representative in the proof of Lemma 5.3 is
absolutely integrable pointwise and differentiable off the marks. This follows
from the regularity assumptions and a local near/far split of the periodic convolution.
The actual regularization error has a classical derivative there as well.
This file does not assert the quantitative derivative bounds of that lemma.
-/

public section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace Riesz1

/-- The actual inverse kernel, including its specified lattice values, is Borel
measurable. Those countably many values cause no measurability obstruction. -/
theorem measurable_inverseKernel (P : Parameters) {L : ℝ} (hL : 0 < L) :
    Measurable (inverseKernel P L) := by
  apply measurable_of_countable_not_continuousAt
  apply (Set.countable_range (fun k : ℤ => (k : ℝ) * L)).mono
  intro t ht
  by_contra hnot
  exact ht ((contDiffAt_inverseKernel P hL
    (fun k hk => hnot ⟨k, hk.symm⟩)).continuousAt)

namespace Internal

/-- The inverse convolution is meaningful pointwise and has a classical
 derivative wherever the transport is locally `C²`. This is an internal
analytic helper. The result below supplies both hypotheses
from the regularity predicates. -/
theorem inverseConv_classical_of_transport (P : Parameters) (L : Length)
    {ι : Type*} [Finite ι] (marks : ι → ℝ) (ψ : Circle L → ℝ)
    (hi : LocallyIntegrable (deriv (fun t : ℝ => ψ (t : Circle L))) volume)
    (hψ : ∀ x : ℝ, (∀ j, (x : Circle L) ≠ (marks j : Circle L)) →
      ContDiffAt ℝ 2 (fun t : ℝ => ψ (t : Circle L)) x)
    {x : ℝ} (hx : ∀ j, (x : Circle L) ≠ (marks j : Circle L)) :
    IntegrableOn (fun y => deriv (fun t : ℝ => ψ (t : Circle L)) y *
      inverseKernel P L.val (x - y)) (Ioc (-(L.val / 2)) (L.val / 2)) ∧
      DifferentiableAt ℝ
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
  apply PeriodicConvolution.differentiableAt_of_contDiffOn L.property hr
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

end Internal

/-- The inverse representative of the actual profile, derived solely from
(A1)–(A3) of Assumption 1.1, has a classical derivative off the marked points. Its actual
mollification error is differentiable there for every positive smoothing radius.
This proves existence of the displayed derivatives in the proof of Lemma 5.3,
but does not yet prove their uniform quantitative bounds or the extension at marks. -/
theorem regMicroKernel_profile_classical (P : Parameters) (L : Length)
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
      (∀ᵐ x : ℝ ∂(volume.restrict (Ioc (-(L.val / 2)) (L.val / 2))),
        f.val (x : Circle L) =
          (∫ y in Ioc (-(L.val / 2)) (L.val / 2), f.val (y : Circle L)) / L.val +
            inverseConv P L.val (deriv (fun t : ℝ => ψ.val (t : Circle L))) x) ∧
      ∀ x : ℝ, (∀ j, (x : Circle L) ≠ (marks j : Circle L)) →
        IntegrableOn (fun y => deriv (fun t : ℝ => ψ.val (t : Circle L)) y *
          inverseKernel P L.val (x - y)) (Ioc (-(L.val / 2)) (L.val / 2)) ∧
        DifferentiableAt ℝ
          (fun t =>
            (∫ y in Ioc (-(L.val / 2)) (L.val / 2), f.val (y : Circle L)) / L.val +
              inverseConv P L.val (deriv (fun u : ℝ => ψ.val (u : Circle L))) t) x ∧
        ∀ (ρ : ℝ → ℝ), IsMollifier ρ → ∀ h : ℝ, 0 < h →
          DifferentiableAt ℝ
            (fun t =>
              (∫ y in Ioc (-(L.val / 2)) (L.val / 2), f.val (y : Circle L)) / L.val +
                inverseConv P L.val (deriv (fun u : ℝ => ψ.val (u : Circle L))) t -
                  circleMollify ρ L.val h (fun y => f.val (y : Circle L)) t) x := by
  have : Fact (0 < L.val) := ⟨L.property⟩
  obtain ⟨ψ, hc, hcoeff, hi, _hAC, hs, hrep, _hmoll⟩ :=
    regMicroKernel_profile_representation P L η B hη hB f n marks α C
      hα0 hα1 hC hprim hreg
  refine ⟨ψ, hc, hcoeff, hrep, fun x hx => ?_⟩
  obtain ⟨hint, hd⟩ := Internal.inverseConv_classical_of_transport P L marks ψ.val hi hs hx
  have hd' := hd.const_add ((∫ y in Ioc (-(L.val / 2)) (L.val / 2),
    f.val (y : Circle L)) / L.val)
  refine ⟨hint, hd', fun ρ hρ h hh => ?_⟩
  have hfi : Integrable f.val (arclength L) := by
    have hr := (complexL2Integrable L _ f.property).re
    change Integrable (fun x => (f.val x : ℂ).re) (arclength L) at hr
    simpa only [Complex.ofReal_re] using hr
  have hfl : LocallyIntegrable (fun t : ℝ => f.val (t : Circle L)) volume :=
    Internal.locallyIntegrable_circle_lift hfi
  have hfp : Function.Periodic (fun t : ℝ => f.val (t : Circle L)) L.val := fun t => by
    dsimp only
    rw [AddCircle.coe_add_period]
  exact hd'.sub ((contDiff_circleMollify hρ L.property hh hfl hfp).differentiable (by simp) x)

end Riesz1
