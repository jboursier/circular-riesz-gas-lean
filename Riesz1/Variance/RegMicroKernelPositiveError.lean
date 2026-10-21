/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.RegMicroKernelPositiveValue
public import Riesz1.Variance.RegMicroKernelErrorRepresentation
public import Riesz1.ToMathlib.FiniteMarkMollify

/-!
# Positive-exponent regularization errors

The direct inverse-convolution value bound and the finite-mark
regularization bound give the global positive-exponent envelope, including
points closer to a mark than the smoothing radius (Lemma 5.3).
-/

public section

open MeasureTheory Set Filter Topology

namespace Riesz1.Internal

/-- Global smoothing error for the inverse convolution. Both the transport
envelope and its integral bound are internal analytic hypotheses. -/
theorem inverseConv_positive_error_bound (P : Parameters) (ρ : ℝ → ℝ)
    (hρ : IsMollifier ρ) {α : ℝ} (hα : 0 < α) (hα1 : α < P.val.2)
    (ι : Type*) [Fintype ι] [Nonempty ι] :
    ∃ K : ℝ, 0 < K ∧ ∀ (L : ℝ) [Fact (0 < L)], 1 ≤ L →
      ∀ (marks : ι → ℝ) (q : ℝ → ℝ) (A : ℝ), 0 ≤ A → Measurable q →
      IntegrableOn q (Ioc (-(L/2)) (L/2)) →
      (∫ y in Ioc (-(L/2)) (L/2), |q y|) ≤ A →
      (∀ y : ℝ, (∀ j, (y : AddCircle L) ≠ (marks j : AddCircle L)) →
        |q y| ≤ A * cappedMarkDistance (fun j => (marks j : AddCircle L))
          (y : AddCircle L) ^ (-1 + P.val.2 - α)) →
      ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ x : ℝ,
        (∀ j, (x : AddCircle L) ≠ (marks j : AddCircle L)) →
        |inverseConv P L q x - circleMollify ρ L h (inverseConv P L q) x| ≤
          K * A * (h ^ (-α) + ∑ j, dist (x : AddCircle L) (marks j : AddCircle L) ^ (-α)) := by
  classical
  obtain ⟨D, hD, hvalue⟩ := inverseConv_positive_value_bound P hα hα1 ι
  obtain ⟨Q, hQ, hmoll⟩ := circleMollify_finiteMark_bound hρ hα.le
    (hα1.trans P.property.2.2)
  let T := 1 + Q * (1 + Fintype.card ι)
  have hT : 0 < T := by dsimp [T]; positivity
  refine ⟨D*T, mul_pos hD hT, fun L hL hL1 marks q A hA hqm hqi hnorm hq h hh hh1 x hx => ?_⟩
  let F := inverseConv P L q
  have hFi := PeriodicConvolution.locallyIntegrable_of_period hL.out
    (inverseConv_periodic P hL.out q) (integrableOn_inverseConv P hL.out hqi)
  have henv : ∀ᵐ y : ℝ, |F y| ≤ D * A *
      (1 + ∑ j, dist (y : AddCircle L) (marks j : AddCircle L) ^ (-α)) := by
    filter_upwards [((CircleSingularity.countable_marked_lifts (T := L) marks).ae_notMem volume)] with y hy
    apply (hvalue L marks q A hA hqm hqi hnorm hq y ?_).2
    simpa only [mem_ofPred_eq, not_exists] using hy
  have hm := hmoll L hL1 marks (D*A) (mul_nonneg hD.le hA) F
    (inverseConv_periodic P hL.out q) hFi henv h hh hh1 x
  have hsum : (∑ j, max (dist (x : AddCircle L) (marks j : AddCircle L)) h ^ (-α)) ≤
      (Fintype.card ι : ℝ) * h ^ (-α) := by
    calc _ ≤ ∑ _j : ι, h ^ (-α) := Finset.sum_le_sum fun j _ =>
          Real.rpow_le_rpow_of_nonpos hh (le_max_right _ _) (by linarith)
      _ = _ := by simp
  have hhn : 1 ≤ h ^ (-α) := by
    simpa only [Real.one_rpow] using
      Real.rpow_le_rpow_of_nonpos hh hh1 (by linarith : -α ≤ 0)
  have hv := (hvalue L marks q A hA hqm hqi hnorm hq x hx).2
  have hsnon : 0 ≤ ∑ j, dist (x : AddCircle L) (marks j : AddCircle L) ^ (-α) :=
    Finset.sum_nonneg fun j _ => Real.rpow_nonneg dist_nonneg _
  have hm' : |circleMollify ρ L h F x| ≤ Q * (D*A) *
      ((1 + Fintype.card ι) * h ^ (-α)) := by
    apply hm.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ Q * (D*A))
    nlinarith
  calc _ ≤ |F x| + |circleMollify ρ L h F x| := abs_sub _ _
    _ ≤ D*A*(1 + ∑ j, dist (x : AddCircle L) (marks j : AddCircle L) ^ (-α)) +
        Q*(D*A)*((1+Fintype.card ι)*h^(-α)) := add_le_add hv hm'
    _ ≤ _ := by
      dsimp [T]
      nlinarith [mul_le_mul_of_nonneg_left hhn (mul_nonneg hD.le hA),
        mul_nonneg (by positivity : 0 ≤ Q*(1+Fintype.card ι))
          (mul_nonneg (mul_nonneg hD.le hA) hsnon)]

/-- The actual profile smoothing error, on the same inverse representative
as the derivative estimate. No bound on a profile reference value is needed. -/
theorem uniform_inverse_profile_positive_error (P : Parameters) (ρ : ℝ → ℝ)
    (hρ : IsMollifier ρ) (α : ℝ) (hα : 0 < α)
    (hα1 : α < P.val.2 / 2) (n : ℕ+) :
    ∃ K : ℝ, 0 < K ∧ ∀ (L : Length), 1 ≤ L.val →
      ∀ (f : {f : Circle L → ℝ // MemLp (fun x => (f x : ℂ)) 2 (arclength L)})
      (marks : Fin (n : ℕ) → ℝ)
      (ψ : {g : Circle L → ℝ // MemLp (fun x => (g x : ℂ)) 2 (arclength L)}),
      Continuous ψ.val →
      (∀ k : ℤ, coeff L
        ⟨(fun x => (ψ.val x : ℂ)), complexL2Integrable L _ ψ.property⟩ k =
          transportCoeffs P L f k) →
      LocallyIntegrable (deriv (fun t : ℝ => ψ.val (t : Circle L))) volume →
      ∀ A : ℝ, 0 ≤ A →
        (∫ y in Ioc (-(L.val/2)) (L.val/2), |deriv (fun t : ℝ => ψ.val (t : Circle L)) y|) ≤ A →
        (∀ x : ℝ, (∀ j, (x : Circle L) ≠ (marks j : Circle L)) →
          ContDiffAt ℝ 2 (fun t : ℝ => ψ.val (t : Circle L)) x ∧
          |deriv (fun t : ℝ => ψ.val (t : Circle L)) x| ≤ A *
            cappedMarkDistance (fun j => (marks j : Circle L)) (x : Circle L) ^ (-1 + P.val.2 - α) ∧
          |deriv (deriv (fun t : ℝ => ψ.val (t : Circle L))) x| ≤ A *
            cappedMarkDistance (fun j => (marks j : Circle L)) (x : Circle L) ^ (-2 + P.val.2 - α)) →
        let m := (∫ y in Ioc (-(L.val / 2)) (L.val / 2), f.val (y : Circle L)) / L.val
        let q := deriv (fun t : ℝ => ψ.val (t : Circle L))
        (∀ᵐ x : ℝ ∂(volume.restrict (Ioc (-(L.val / 2)) (L.val / 2))),
          f.val (x : Circle L) = m + inverseConv P L.val q x) ∧
        ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ x : ℝ,
          (∀ j, (x : Circle L) ≠ (marks j : Circle L)) →
          |m + inverseConv P L.val q x -
            circleMollify ρ L.val h (fun y => f.val (y : Circle L)) x| ≤
              K * A * (h ^ (-α) + ∑ j, dist (x : Circle L) (marks j : Circle L) ^ (-α)) := by
  have hα0 : P.val.2 - 1 < α := by linarith [P.property.2.2]
  obtain ⟨K, hK, herr⟩ := inverseConv_positive_error_bound P ρ hρ hα
    (by linarith [P.property.2.1] : α < P.val.2) (Fin (n : ℕ))
  obtain ⟨_D, _hD, hprofile⟩ := uniform_inverse_profile_derivative P α hα0 hα1 n
  refine ⟨K, hK, fun L hL f marks ψ hc hcoeff hi A hA hnorm hpoint => ?_⟩
  have : Fact (0 < L.val) := ⟨L.property⟩
  let q := deriv (fun t : ℝ => ψ.val (t : Circle L))
  let m := (∫ y in Ioc (-(L.val / 2)) (L.val / 2), f.val (y : Circle L)) / L.val
  obtain ⟨hrep, _hd⟩ := hprofile L f marks ψ hc hcoeff hi A hA hpoint
  have hqi : IntegrableOn q (Ioc (-(L.val / 2)) (L.val / 2)) :=
    (hi.integrableOn_isCompact isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hconvI := PeriodicConvolution.locallyIntegrable_of_period L.property
    (inverseConv_periodic P L.property q) (integrableOn_inverseConv P L.property hqi)
  refine ⟨hrep, fun h hh hh1 x hx => ?_⟩
  have hmoll : circleMollify ρ L.val h (fun y => f.val (y : Circle L)) x =
      m + circleMollify ρ L.val h (inverseConv P L.val q) x := by
    have he : circleMollify ρ L.val h (fun y => f.val (y : Circle L)) x =
        circleMollify ρ L.val h (fun y => m + inverseConv P L.val q y) x := by
      unfold circleMollify
      rw [intervalIntegral.integral_of_le (by linarith [L.property]),
        intervalIntegral.integral_of_le (by linarith [L.property])]
      apply integral_congr_ae
      filter_upwards [hrep] with y hy
      rw [hy]
    rw [he, circleMollify_const_add hρ L.property hh hconvI
      (inverseConv_periodic P L.property q) m x]
  rw [hmoll, show m + inverseConv P L.val q x -
    (m + circleMollify ρ L.val h (inverseConv P L.val q) x) =
      inverseConv P L.val q x - circleMollify ρ L.val h (inverseConv P L.val q) x by ring]
  exact herr L.val hL marks q A hA (measurable_deriv _) hqi hnorm
    (fun y hy => (hpoint y hy).2.1) h hh hh1 x hx

end Riesz1.Internal
