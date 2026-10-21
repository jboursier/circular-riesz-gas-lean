/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.LogSobolevConditioningApproximation
public import Riesz1.HelfferSjostrand.LogSobolevLogConcave
public import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Identifying the limit for a zero-allowing log-concave density

The probability assumption forces nonempty interior of the positive support. The support
boundary is null, and the interior density agrees almost everywhere with the given density.
The smooth-potential approximation is constructed, including its convergence to that law.
-/

public section

noncomputable section

open Set MeasureTheory Filter Topology
open scoped InnerProductSpace ContDiff

namespace Riesz1.LogSobolevInternal

/-- Internal construction of smooth uniformly convex potentials for a Borel log-concave
Gaussian density on a convex Borel set. Zero values of the density are allowed everywhere.
The positive scalar `c` permits any Gaussian normalization convention. -/
theorem logConcave_gaussian_approximation {d : ℕ} {w : ℝ} (hw : 0 < w)
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : Convex ℝ Ω)
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf0 : ∀ x ∈ Ω, 0 ≤ f x)
    (hlog : ∀ x ∈ Ω, ∀ y ∈ Ω, ∀ t : ℝ, 0 < t → t < 1 →
      f x ^ t * f y ^ (1 - t) ≤ f (t • x + (1 - t) • y))
    {c : ℝ} (hc : 0 < c) (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (hμ : μ = volume.withDensity (fun x => ENNReal.ofReal
      (c * Ω.indicator (fun y => f y * Real.exp (-((2*w)⁻¹ * ‖y‖^2))) x))) :
    ∃ Vn : ℕ → EuclideanSpace ℝ (Fin d) → ℝ,
      (∀ n, ContDiff ℝ ∞ (Vn n)) ∧
      (∀ n x h, w⁻¹ * ‖h‖^2 ≤ (fderiv ℝ (fderiv ℝ (Vn n)) x h) h) ∧
      ∀ H : EuclideanSpace ℝ (Fin d) → ℝ, Continuous H → (∃ C, ∀ x, |H x| ≤ C) →
        Tendsto (fun n => ∫ x, H x ∂volume.withDensity
          (fun x => ENNReal.ofReal (Real.exp (-Vn n x) / ∫ y, Real.exp (-Vn n y))))
          atTop (𝓝 (∫ x, H x ∂μ)) := by
  classical
  let S := {x | x ∈ Ω ∧ 0 < f x}
  let r := Ω.indicator (fun y => f y * Real.exp (-((2*w)⁻¹ * ‖y‖^2)))
  have hSc : Convex ℝ S := convex_positive_support hΩ hlog
  have hr0 : ∀ x, x ∉ S → r x = 0 := by
    intro x hx
    by_cases hxΩ : x ∈ Ω
    · have hfz : f x = 0 := le_antisymm (not_lt.mp (fun hp => hx ⟨hxΩ, hp⟩)) (hf0 x hxΩ)
      simp [r, hxΩ, hfz]
    · simp [r, hxΩ]
  have hnull : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), x ∉ frontier S :=
    ae_iff.mpr (by simpa only [not_not, ofPred_mem_eq] using hSc.addHaar_frontier volume)
  have hSne : (interior S).Nonempty := by
    by_contra hne
    have hempty : interior S = ∅ := not_nonempty_iff_eq_empty.mp hne
    have hrz : (fun x => ENNReal.ofReal (c * r x)) =ᵐ[volume] 0 := by
      filter_upwards [hnull] with x hx
      have hxS : x ∉ S := fun hs => hx ⟨subset_closure hs, by simp [hempty]⟩
      simp [hr0 x hxS]
    have hzero : μ = 0 := by
      rw [hμ]
      exact (withDensity_congr_ae hrz).trans (withDensity_zero)
    have hone := measure_univ (μ := μ)
    rw [hzero] at hone
    norm_num at hone
  have hg : ConvexOn ℝ (interior S) (fun x => -Real.log (f x)) :=
    (convexOn_neg_log_positive_support hΩ hlog).subset interior_subset hSc.interior
  have hcont : ContinuousOn (fun x => -Real.log (f x)) (interior S) :=
    continuousOn_neg_log_positive_support hΩ hlog
  obtain ⟨l, b, hl⟩ := exists_affine_minorant_open isOpen_interior hSne hg hcont
  let a := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm l
  have haff : ∀ x ∈ interior S, ⟪a, x⟫_ℝ + b ≤ -Real.log (f x) := by
    simpa only [a, InnerProductSpace.toDual_symm_apply] using hl
  obtain ⟨hip, hZ, _, Vn, hVn, hHn, hlim⟩ :=
    smooth_potential_approximation_open hw isOpen_interior hSne hg haff
  let p := (interior S).indicator (fun x => Real.exp (-((2*w)⁻¹ * ‖x‖^2 + -Real.log (f x))))
  have hp0 : ∀ x, 0 ≤ p x := fun x => indicator_nonneg (fun _ _ => (Real.exp_pos _).le) x
  have hrp : r =ᵐ[volume] p := by
    filter_upwards [hnull] with x hx
    by_cases hxS : x ∈ S
    · have hxI : x ∈ interior S := by
        by_contra hh
        exact hx ⟨subset_closure hxS, hh⟩
      have hxΩ := hxS.1
      have hfpos := hxS.2
      simp only [r, p, indicator_of_mem hxΩ, indicator_of_mem hxI]
      rw [neg_add, neg_neg, Real.exp_add, Real.exp_log hfpos]
      ring
    · have hxI : x ∉ interior S := fun hh => hxS (interior_subset hh)
      simp only [hr0 x hxS, p, indicator_of_notMem hxI]
  have hμp : μ = volume.withDensity (fun x => ENNReal.ofReal (c * p x)) := by
    rw [hμ]
    apply withDensity_congr_ae
    filter_upwards [hrp] with x hx
    rw [show Ω.indicator (fun y => f y * Real.exp (-((2*w)⁻¹ * ‖y‖^2))) x = r x from rfl, hx]
  have hnorm := Gaussian.eq_normalized_density_of_probability hip hp0 hZ hc hμp
  refine ⟨Vn, hVn, hHn, ?_⟩
  intro H hH hHb
  rw [hnorm]
  exact hlim H hH hHb

end Riesz1.LogSobolevInternal

end
