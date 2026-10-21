/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Externals.BakryEmeryWeighted
public import Riesz1.ToMathlib.ExponentialEntropyLimit
public import Riesz1.ToMathlib.ExponentialEntropyApproximation

/-!
# Exponential entropy bounds for Bakry–Émery

First variation of the weighted integral comparison proves the sharp exponential-test
inequality for the Bakry–Émery criterion `Riesz1.External.BakryEmery`. The Hessian upper bound
on the test is an internal regularity condition, separate from that statement. The method is that of
Bobkov–Ledoux (2000), Proposition 3.1. No external code is copied in this module.
-/

public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff InnerProductSpace

namespace Riesz1.Externals

variable {d : ℕ} {w : ℝ} {V : EuclideanSpace ℝ (Fin d) → ℝ}

/-- Internal exponential-test entropy bound with a globally bounded test Hessian. -/
theorem bakry_emery_exponential_entropy_of_hessian_upper (hd : 0 < d) (hw : 0 < w)
    (hV : ContDiff ℝ ∞ V)
    (hH : ∀ x h, w⁻¹ * ‖h‖ ^ 2 ≤ (fderiv ℝ (fderiv ℝ V) x h) h)
    {g : EuclideanSpace ℝ (Fin d) → ℝ} (hg : ContDiff ℝ 2 g)
    (hbg : Bornology.IsBounded (range g)) (hbG : Bornology.IsBounded (range (gradient g)))
    {M : ℝ} (hgH : ∀ x h, (fderiv ℝ (fderiv ℝ g) x h) h ≤ M * ‖h‖ ^ 2) :
    let ν : Measure (EuclideanSpace ℝ (Fin d)) := volume.withDensity (fun x =>
      ENNReal.ofReal (Real.exp (-V x) / ∫ y, Real.exp (-V y)))
    (∫ x, g x * Real.exp (g x) ∂ν) -
      (∫ x, Real.exp (g x) ∂ν) * Real.log (∫ x, Real.exp (g x) ∂ν) ≤
        w / 2 * ∫ x, Real.exp (g x) * ‖gradient g x‖ ^ 2 ∂ν := by
  let ν : Measure (EuclideanSpace ℝ (Fin d)) := volume.withDensity (fun x =>
    ENNReal.ofReal (Real.exp (-V x) / ∫ y, Real.exp (-V y)))
  let : IsProbabilityMeasure ν := bakry_emery_isProbabilityMeasure hw hV hH
  obtain ⟨K, hK⟩ := hbg.exists_norm_le
  obtain ⟨L, hL⟩ := hbG.exists_norm_le
  have hcG : Continuous (gradient g) :=
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm.continuous.comp
      (hg.continuous_fderiv (by norm_num))
  have hL' (x) : |‖gradient g x‖ ^ 2| ≤ L ^ 2 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hL _ (mem_range_self x)) 2
  have hD : ∀ᶠ s : ℝ in 𝓝 0, 0 < w⁻¹ * (1 - s) - M * s := by
    have hc : ContinuousAt (fun s : ℝ => w⁻¹ * (1 - s) - M * s) 0 := by fun_prop
    exact hc.eventually (lt_mem_nhds (show 0 < w⁻¹ * (1 - (0 : ℝ)) - M * 0 by simpa using inv_pos.mpr hw))
  have hi := exponential_entropy_le_of_comparison (μ := ν) hg.continuous (hcG.norm.pow 2)
    (fun x => hK _ (mem_range_self x)) hL' (inv_pos.mpr hw) (M := M) (by
      filter_upwards [hD.filter_mono nhdsWithin_le_nhds,
        (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds,
        self_mem_nhdsWithin] with s hDs hs1 hs
      exact bakry_emery_interpolation_integral hd hw hV hH hg hbg hbG hgH hs hs1 hDs)
  have he : (2 * w⁻¹)⁻¹ = w / 2 := by field_simp
  simpa only [he, Pi.pow_apply] using hi

/-- Exponential entropy for every bounded smooth test with bounded gradient. -/
theorem bakry_emery_exponential_entropy (hd : 0 < d) (hw : 0 < w)
    (hV : ContDiff ℝ ∞ V)
    (hH : ∀ x h, w⁻¹ * ‖h‖ ^ 2 ≤ (fderiv ℝ (fderiv ℝ V) x h) h)
    {g : EuclideanSpace ℝ (Fin d) → ℝ} (hg : ContDiff ℝ ∞ g)
    (hbg : Bornology.IsBounded (range g)) (hbG : Bornology.IsBounded (range (gradient g))) :
    let ν : Measure (EuclideanSpace ℝ (Fin d)) := volume.withDensity (fun x =>
      ENNReal.ofReal (Real.exp (-V x) / ∫ y, Real.exp (-V y)))
    (∫ x, g x * Real.exp (g x) ∂ν) -
      (∫ x, Real.exp (g x) ∂ν) * Real.log (∫ x, Real.exp (g x) ∂ν) ≤
        w / 2 * ∫ x, Real.exp (g x) * ‖gradient g x‖ ^ 2 ∂ν := by
  let ν : Measure (EuclideanSpace ℝ (Fin d)) := volume.withDensity (fun x =>
    ENNReal.ofReal (Real.exp (-V x) / ∫ y, Real.exp (-V y)))
  let : IsProbabilityMeasure ν := bakry_emery_isProbabilityMeasure hw hV hH
  obtain ⟨K, hK⟩ := hbg.exists_norm_le
  obtain ⟨D, hD⟩ := hbG.exists_norm_le
  have hnorm (f : EuclideanSpace ℝ (Fin d) → ℝ) (x) :
      ‖gradient f x‖ = ‖fderiv ℝ f x‖ := by simp only [gradient, LinearIsometryEquiv.norm_map]
  have hi := exponential_entropy_of_compact_tests (μ := ν) (w / 2) (fun f hf hcs => by
    obtain ⟨M, hM⟩ := exists_hessian_upper_of_hasCompactSupport hf hcs
    obtain ⟨C, hC⟩ := hf.continuous.norm.bounded_above_of_compact_support hcs.norm
    have hcD : Continuous (fun x => ‖fderiv ℝ f x‖) := (hf.continuous_fderiv (by simp)).norm
    have hcsD : HasCompactSupport (fun x => ‖fderiv ℝ f x‖) := (hcs.fderiv (𝕜 := ℝ)).norm
    obtain ⟨D', hD'⟩ := hcD.bounded_above_of_compact_support hcsD
    have hbf : Bornology.IsBounded (range f) := isBounded_iff_forall_norm_le.mpr
      ⟨C, by rintro _ ⟨x, rfl⟩; simpa only [norm_norm] using hC x⟩
    have hbfG : Bornology.IsBounded (range (gradient f)) := isBounded_iff_forall_norm_le.mpr
      ⟨D', by rintro _ ⟨x, rfl⟩; simpa only [hnorm, norm_norm] using hD' x⟩
    simpa only [hnorm] using bakry_emery_exponential_entropy_of_hessian_upper
      hd hw hV hH (hf.of_le (by simp : (2 : ℕ∞ω) ≤ ∞)) hbf hbfG hM)
    hg (fun x => hK _ (mem_range_self x))
    (fun x => by rw [← hnorm]; exact hD _ (mem_range_self x))
  simpa only [hnorm] using hi

end Riesz1.Externals

end
