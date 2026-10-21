/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.EllipticRegularity.WeakDerivatives
public import Mathlib.Analysis.Calculus.FDeriv.Pow
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Compact cutoff energy calculation for smooth functions

This is the integration by parts calculation in the interior H² regularity argument,
before the extension to distributional solutions and Lipschitz cutoffs.
All terms are proved integrable, including when the ambient values of the
solution outside the open domain are arbitrary.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ContDiff Laplacian

namespace Riesz1.Internal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [Measure.IsAddHaarMeasure (volume : Measure E)]

/-- The cutoff energy calculation in one fixed Euclidean direction.
This is an internal smooth calculation, not the regularity assertion. -/
theorem smooth_cutoff_directional_energy {U : Set E} (hU : IsOpen U)
    {u b : E → ℝ} (hu : ContDiffOn ℝ ∞ u U) (hb : ContDiff ℝ ∞ b)
    (hbc : HasCompactSupport b) (hbU : tsupport b ⊆ U) (v : E) :
    (∫ x, (fderiv ℝ (fun y => b y * u y) x v) ^ 2) +
      (∫ x, (b x ^ 2 * u x) * fderiv ℝ (fun y => fderiv ℝ u y v) x v) =
      ∫ x, (fderiv ℝ b x v) ^ 2 * u x ^ 2 := by
  let q := fun x => b x ^ 2
  let ψ := fun x => b x ^ 2 * u x
  let a := fun x => b x * u x
  let du := fun x => fderiv ℝ u x v
  have hq : ContDiff ℝ ∞ q := hb.pow 2
  have hqc : HasCompactSupport q := by
    have h : HasCompactSupport (fun x => b x * b x) := hbc.mul_right
    simpa only [q, pow_two] using h
  have hqU : tsupport q ⊆ U := by
    simpa only [q, pow_two] using (tsupport_mul_subset_left (f := b) (g := b)).trans hbU
  have hψ : ContDiff ℝ ∞ ψ := WeightedSobolev.contDiff_cutoff_mul hU hq hqU hu
  have hψc : HasCompactSupport ψ := hqc.mul_right
  have hψU : tsupport ψ ⊆ U := tsupport_mul_subset_left.trans hqU
  have hdu : ContDiffOn ℝ ∞ du U :=
    (hu.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const
  have hdψ : ContDiff ℝ ∞ (fun x => fderiv ℝ ψ x v) :=
    (hψ.fderiv_right (by simp)).clm_apply contDiff_const
  have hdψU : tsupport (fun x => fderiv ℝ ψ x v) ⊆ U :=
    (tsupport_fderiv_apply_subset ℝ v).trans hψU
  have hi : Integrable (fun x => (fderiv ℝ ψ x v) * du x) :=
    (WeightedSobolev.continuous_cutoff_mul hU hdψ.continuous hdψU hdu.continuousOn
      ).integrable_of_hasCompactSupport (hψc.fderiv_apply ℝ v).mul_right
  have hj : Integrable (fun x => (fderiv ℝ b x v) ^ 2 * u x ^ 2) := by
    have hds : tsupport (fun x => (fderiv ℝ b x v) ^ 2) ⊆ U := by
      simpa only [pow_two] using
        (tsupport_mul_subset_left (f := fun x => fderiv ℝ b x v)
          (g := fun x => fderiv ℝ b x v)).trans
            ((tsupport_fderiv_apply_subset ℝ v).trans hbU)
    apply (WeightedSobolev.continuous_cutoff_mul hU
      (((hb.continuous_fderiv (by norm_num)).clm_apply continuous_const).pow 2)
      hds
      (hu.continuousOn.pow 2)).integrable_of_hasCompactSupport
    have h : HasCompactSupport (fun x => (fderiv ℝ b x v) ^ 2) := by
      simp only [pow_two]
      exact (hbc.fderiv_apply ℝ v).mul_right
    exact h.mul_right
  have hpoint (x : E) : (fderiv ℝ a x v) ^ 2 =
      (fderiv ℝ b x v) ^ 2 * u x ^ 2 + (fderiv ℝ ψ x v) * du x := by
    by_cases hx : x ∈ U
    · have hud := (hu.contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num)
      have hbd := hb.differentiable (by norm_num) x
      dsimp [a, ψ, du]
      have hqd : DifferentiableAt ℝ (fun y => b y ^ 2) x :=
        hq.differentiable (by norm_num) x
      rw [fderiv_fun_mul hbd hud, fderiv_fun_mul hqd hud, fderiv_fun_pow 2 hbd]
      simp only [add_apply, smul_apply, smul_eq_mul,
        Nat.reduceSub, pow_one, nsmul_eq_mul, Nat.cast_ofNat]
      ring
    · have hxb : x ∉ tsupport b := fun h => hx (hbU h)
      have hxa : x ∉ tsupport a := fun h => hxb (tsupport_mul_subset_left h)
      have hxψ : x ∉ tsupport ψ := fun h => hx (hψU h)
      rw [fderiv_of_notMem_tsupport ℝ hxa, fderiv_of_notMem_tsupport ℝ hxb,
        fderiv_of_notMem_tsupport ℝ hxψ]
      simp
  have hparts := WeightedSobolev.integral_weighted_fderiv_of_compact_test
    (μ := volume) hU hq hqc hqU hdu hu v
  have hparts' : (∫ x, (b x ^ 2 * u x) * fderiv ℝ du x v) =
      - ∫ x, (fderiv ℝ ψ x v) * du x := by
    simpa only [q, ψ, mul_comm] using hparts
  have he := integral_congr_ae (μ := volume) (Filter.Eventually.of_forall hpoint)
  rw [integral_add hj hi] at he
  change (∫ x, (fderiv ℝ a x v) ^ 2) + (∫ x, (b x ^ 2 * u x) * fderiv ℝ du x v) = _
  rw [he, hparts']
  ring

omit [MeasureSpace E] [BorelSpace E] [Measure.IsAddHaarMeasure (volume : Measure E)] in
/-- Classical second directional derivatives give the Laplacian locally. -/
theorem smooth_laplacian_eq_sum {U : Set E} (hU : IsOpen U) {u : E → ℝ}
    (hu : ContDiffOn ℝ ∞ u U) {x : E} (hx : x ∈ U) :
    (Δ u) x = ∑ i, fderiv ℝ (fun y => fderiv ℝ u y (stdOrthonormalBasis ℝ E i))
      x (stdOrthonormalBasis ℝ E i) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  apply Finset.sum_congr rfl
  intro i _
  have hd := ((hu.fderiv_of_isOpen (m := ∞) hU (by simp)).contDiffAt
    (hU.mem_nhds hx)).differentiableAt (by norm_num)
  rw [fderiv_clm_apply hd (differentiableAt_const _), iteratedFDeriv_two_apply]
  simp

/-- The real smooth compact-cutoff identity, with the forcing written as
`Δ u`. This is an internal smooth subcase of the interior H² regularity argument. -/
theorem smooth_cutoff_energy {U : Set E} (hU : IsOpen U)
    {u b : E → ℝ} (hu : ContDiffOn ℝ ∞ u U) (hb : ContDiff ℝ ∞ b)
    (hbc : HasCompactSupport b) (hbU : tsupport b ⊆ U) :
    (∫ x, ‖gradient (fun y => b y * u y) x‖ ^ 2) +
      (∫ x, (b x ^ 2 * u x) * (Δ u) x) =
      ∫ x, ‖gradient b x‖ ^ 2 * u x ^ 2 := by
  let e := stdOrthonormalBasis ℝ E
  let a := fun x => b x * u x
  have hg (f : E → ℝ) (x : E) :
      (∑ i, (fderiv ℝ f x (e i)) ^ 2) = ‖gradient f x‖ ^ 2 := by
    simpa only [inner_gradient_left] using e.sum_sq_inner_left (gradient f x)
  have ha : ContDiff ℝ ∞ a := WeightedSobolev.contDiff_cutoff_mul hU hb hbU hu
  have hac : HasCompactSupport a := hbc.mul_right
  have hL (i : Fin (Module.finrank ℝ E)) :
      Integrable (fun x => (fderiv ℝ a x (e i)) ^ 2) := by
    have hc : Continuous (fun x => (fderiv ℝ a x (e i)) ^ 2) :=
      ((ha.continuous_fderiv (by norm_num)).clm_apply continuous_const).pow 2
    have hs : HasCompactSupport (fun x => (fderiv ℝ a x (e i)) ^ 2) := by
      simp only [pow_two]
      exact (hac.fderiv_apply ℝ (e i)).mul_right
    exact hc.integrable_of_hasCompactSupport hs
  have hR (i : Fin (Module.finrank ℝ E)) :
      Integrable (fun x => (fderiv ℝ b x (e i)) ^ 2 * u x ^ 2) := by
    have hs : tsupport (fun x => (fderiv ℝ b x (e i)) ^ 2) ⊆ U := by
      simp only [pow_two]
      exact tsupport_mul_subset_left.trans ((tsupport_fderiv_apply_subset ℝ (e i)).trans hbU)
    have hc := WeightedSobolev.continuous_cutoff_mul hU
      (((hb.continuous_fderiv (by norm_num)).clm_apply continuous_const).pow 2) hs
      (hu.continuousOn.pow 2)
    have hs' : HasCompactSupport (fun x => (fderiv ℝ b x (e i)) ^ 2) := by
      simp only [pow_two]
      exact (hbc.fderiv_apply ℝ (e i)).mul_right
    exact hc.integrable_of_hasCompactSupport hs'.mul_right
  have hA (i : Fin (Module.finrank ℝ E)) : Integrable (fun x =>
      (b x ^ 2 * u x) * fderiv ℝ (fun y => fderiv ℝ u y (e i)) x (e i)) := by
    have hd := (hu.fderiv_of_isOpen (m := ∞) hU (by simp)).clm_apply
      (contDiffOn_const (c := e i))
    have hdd := (hd.continuousOn_fderiv_of_isOpen hU (by norm_num)).clm_apply
      (continuousOn_const (c := e i))
    have hs : tsupport (fun x => b x ^ 2) ⊆ U := by
      simpa only [pow_two] using (tsupport_mul_subset_left (f := b) (g := b)).trans hbU
    have hc := WeightedSobolev.continuous_cutoff_mul hU (hb.continuous.pow 2) hs
      (hu.continuousOn.mul hdd)
    have hs' : HasCompactSupport (fun x => b x ^ 2) := by
      simp only [pow_two]
      exact hbc.mul_right
    simpa only [Pi.pow_apply, Pi.mul_apply, mul_assoc] using
      hc.integrable_of_hasCompactSupport hs'.mul_right
  have hsum := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun i _ => smooth_cutoff_directional_energy hU hu hb hbc hbU (e i))
  rw [Finset.sum_add_distrib] at hsum
  have hLe : (∑ i, ∫ x, (fderiv ℝ a x (e i)) ^ 2) =
      ∫ x, ‖gradient a x‖ ^ 2 := by
    rw [← integral_finsetSum _ (fun i _ => hL i)]
    exact integral_congr_ae (Filter.Eventually.of_forall (hg a))
  have hRe : (∑ i, ∫ x, (fderiv ℝ b x (e i)) ^ 2 * u x ^ 2) =
      ∫ x, ‖gradient b x‖ ^ 2 * u x ^ 2 := by
    rw [← integral_finsetSum _ (fun i _ => hR i)]
    apply integral_congr_ae
    filter_upwards with x
    rw [← Finset.sum_mul, hg]
  have hAe : (∑ i, ∫ x, (b x ^ 2 * u x) *
      fderiv ℝ (fun y => fderiv ℝ u y (e i)) x (e i)) =
      ∫ x, (b x ^ 2 * u x) * (Δ u) x := by
    rw [← integral_finsetSum _ (fun i _ => hA i)]
    apply integral_congr_ae
    filter_upwards with x
    rw [← Finset.mul_sum]
    by_cases hx : x ∈ U
    · rw [smooth_laplacian_eq_sum hU hu hx]
    · have hb0 : b x = 0 := image_eq_zero_of_notMem_tsupport
        (fun h => hx (hbU h))
      simp only [hb0, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul]
  change (∫ x, ‖gradient a x‖ ^ 2) + _ = _
  rw [hLe, hAe, hRe] at hsum
  exact hsum

/-- The desired energy identity in the real smooth subcase. The
pointwise equation and smoothness are used only in this internal helper.
They do not replace the distributional hypotheses of the interior H² regularity statement. -/
theorem smooth_cutoff_schrodinger_energy {U : Set E} (hU : IsOpen U)
    {u b W : E → ℝ} (lam : ℝ) (hu : ContDiffOn ℝ ∞ u U) (hb : ContDiff ℝ ∞ b)
    (hbc : HasCompactSupport b) (hbU : tsupport b ⊆ U)
    (heq : ∀ x ∈ U, (Δ u) x = (W x + lam) * u x) :
    (∫ x, ‖gradient (fun y => b y * u y) x‖ ^ 2) +
      (∫ x, (W x + lam) * (b x * u x) ^ 2) =
      ∫ x, ‖gradient b x‖ ^ 2 * u x ^ 2 := by
  have h := smooth_cutoff_energy hU hu hb hbc hbU
  have hp : (∫ x, (b x ^ 2 * u x) * (Δ u) x) =
      ∫ x, (W x + lam) * (b x * u x) ^ 2 := by
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ U
    · rw [heq x hx]
      ring
    · have hb0 : b x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hbU h))
      simp only [hb0, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul,
        mul_zero]
  rwa [hp] at h

end Riesz1.Internal
