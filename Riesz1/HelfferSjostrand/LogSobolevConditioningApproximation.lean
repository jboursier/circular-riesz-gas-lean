/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.Convex.LogConcaveRegularization
public import Riesz1.ToMathlib.Gaussian.AffineDensity
public import Riesz1.ToMathlib.Gaussian.DensityLimit
public import Riesz1.HelfferSjostrand.LogSobolevConditioningCurvature
public import Mathlib.Analysis.Convex.Measure

/-!
# Smooth potential approximation for Gaussian convex densities

On a nonempty open convex set, a finite convex perturbation with an affine minorant
admits smooth Gaussian perturbations converging as probability measures. The common
integrable majorant is proved here, rather than supplied as an approximation hypothesis.
-/

public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace ContDiff

namespace Riesz1.LogSobolevInternal

variable {d : ℕ}

/-- Internal construction of the entire smooth-potential approximation, including density
normalization and convergence against bounded continuous tests. -/
theorem smooth_potential_approximation_open {w : ℝ} (hw : 0 < w)
    {S : Set (EuclideanSpace ℝ (Fin d))} {g : EuclideanSpace ℝ (Fin d) → ℝ}
    (hSo : IsOpen S) (hSne : S.Nonempty) (hgc : ConvexOn ℝ S g)
    {a : EuclideanSpace ℝ (Fin d)} {b : ℝ}
    (haff : ∀ x ∈ S, ⟪a, x⟫_ℝ + b ≤ g x) :
    let p := S.indicator (fun x => Real.exp (-((2*w)⁻¹ * ‖x‖^2 + g x)))
    Integrable p volume ∧ 0 < ∫ x, p x ∧
      IsProbabilityMeasure (volume.withDensity (fun x => ENNReal.ofReal (p x / ∫ y, p y))) ∧
      ∃ Vn : ℕ → EuclideanSpace ℝ (Fin d) → ℝ,
        (∀ n, ContDiff ℝ ∞ (Vn n)) ∧
        (∀ n x h, w⁻¹ * ‖h‖ ^ 2 ≤ (fderiv ℝ (fderiv ℝ (Vn n)) x h) h) ∧
        ∀ H : EuclideanSpace ℝ (Fin d) → ℝ, Continuous H → (∃ C, ∀ x, |H x| ≤ C) →
          Tendsto (fun n => ∫ x, H x ∂volume.withDensity
            (fun x => ENNReal.ofReal (Real.exp (-Vn n x) / ∫ y, Real.exp (-Vn n y))))
            atTop (𝓝 (∫ x, H x ∂volume.withDensity
              (fun x => ENNReal.ofReal (p x / ∫ y, p y)))) := by
  classical
  let Q : EuclideanSpace ℝ (Fin d) → ℝ := fun x => (2*w)⁻¹ * ‖x‖^2
  let p := S.indicator (fun x => Real.exp (-(Q x + g x)))
  have hQ : ContDiff ℝ ∞ Q := contDiff_const.mul (contDiff_id.norm_sq ℝ)
  have hcont : ContinuousOn g S := by
    simpa only [hSo.interior_eq] using hgc.continuousOn_interior
  have hp : Measurable p := by
    have hpc := Real.continuous_exp.comp_continuousOn (hQ.continuous.continuousOn.add hcont).neg
    exact hpc.measurable_piecewise continuousOn_const hSo.measurableSet
  have hp0 : ∀ x, 0 ≤ p x := fun x => indicator_nonneg (fun _ _ => (Real.exp_pos _).le) x
  let M : EuclideanSpace ℝ (Fin d) → ℝ := fun x =>
    Real.exp (-(Q x + ⟪a, x⟫_ℝ + (b - ‖a‖^2/2)))
  have hiM : Integrable M volume := Gaussian.integrable_exp_quadratic_affine hw a _
  have hMp : ∀ x, ‖p x‖ ≤ M x := by
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (hp0 x)]
    by_cases hx : x ∈ S
    · simp only [p, indicator_of_mem hx]
      apply Real.exp_le_exp.mpr
      linarith [haff x hx, sq_nonneg ‖a‖]
    · simp only [p, indicator_of_notMem hx]
      exact (Real.exp_pos _).le
  have hip : Integrable p volume := hiM.mono' hp.aestronglyMeasurable (Eventually.of_forall hMp)
  have hZ : 0 < ∫ x, p x := by
    rw [integral_pos_iff_support_of_nonneg hp0 hip]
    have hsupp : Function.support p = S := by
      ext x
      by_cases hx : x ∈ S <;> simp [p, hx, (Real.exp_pos _).ne']
    rw [hsupp]
    exact hSo.measure_pos volume hSne
  obtain ⟨Bn, hBn, hBin, hBout⟩ := convex_regularization_open hSo hSne hgc haff
  let Vn := fun n x => Q x + Bn n x
  have hVn : ∀ n, ContDiff ℝ ∞ (Vn n) := fun n => hQ.add (hBn n).1
  have hHn : ∀ n x h, w⁻¹ * ‖h‖^2 ≤ (fderiv ℝ (fderiv ℝ (Vn n)) x h) h :=
    fun n => gaussian_convex_hessian w (hBn n).1 (hBn n).2.1
  have hMn : ∀ n x, ‖Real.exp (-Vn n x)‖ ≤ M x := by
    intro n x
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    dsimp [M, Vn]
    linarith [(hBn n).2.2 x]
  have hin : ∀ n, Integrable (fun x => Real.exp (-Vn n x)) volume :=
    fun n => hiM.mono' (Real.continuous_exp.comp (hVn n).continuous.neg).aestronglyMeasurable
      (Eventually.of_forall (hMn n))
  have hZn : ∀ n, 0 < ∫ x, Real.exp (-Vn n x) := fun n => integral_exp_pos (hin n)
  have hlim : ∀ᵐ x ∂volume, Tendsto (fun n => Real.exp (-Vn n x)) atTop (𝓝 (p x)) := by
    have hnull : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), x ∉ frontier S :=
      (ae_iff.mpr (by simpa only [not_not, ofPred_mem_eq] using hgc.1.addHaar_frontier volume))
    filter_upwards [hnull] with x hx
    by_cases hxS : x ∈ S
    · have ht := (hBin {x} isCompact_singleton (singleton_subset_iff.mpr hxS)).tendsto_at
        (mem_singleton x)
      simpa only [Function.comp_def, p, indicator_of_mem hxS, Vn] using
        (Real.continuous_exp.tendsto _).comp (tendsto_const_nhds.add ht).neg
    · have hxcl : x ∉ closure S := by
        intro hcl
        exact hx ⟨hcl, by simpa only [hSo.interior_eq] using hxS⟩
      have ht : Tendsto (fun n => -(Q x + Bn n x)) atTop atBot := by
        have ht' := tendsto_neg_atTop_atBot.comp (hBout x hxcl)
        simpa only [Function.comp_def, neg_add, add_comm] using tendsto_atBot_add_const_left atTop (-(Q x)) ht'
      simpa only [Function.comp_def, p, indicator_of_notMem hxS, Vn] using Real.tendsto_exp_atBot.comp ht
  refine ⟨hip, hZ, Gaussian.isProbabilityMeasure_normalized_density hip hp0 hZ,
    Vn, hVn, hHn, ?_⟩
  intro H hH ⟨C, hC⟩
  exact Gaussian.tendsto_integral_normalized_density
    (fun n => (Real.continuous_exp.comp (hVn n).continuous.neg).measurable) hp
    (fun _ _ => (Real.exp_pos _).le) hp0 hZn hZ hiM
    (fun n => Eventually.of_forall (hMn n)) hlim hH.aestronglyMeasurable hC

end Riesz1.LogSobolevInternal

end
