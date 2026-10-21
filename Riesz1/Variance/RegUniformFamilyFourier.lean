/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.RegUniformCompactVariance
public import Riesz1.Variance.RegUniformDerivatives

/-! # Uniform smoothing rates from common Fourier bounds

Internal estimates for Lemma 5.1. Their Fourier hypotheses
are discharged for the two fixed families in the modules for the clauses.
-/

public section

open MeasureTheory Filter
open scoped ENNReal ContDiff Topology

namespace Riesz1.Internal

/-- The actual regularization contracts coefficient norms. Its error has at
most twice the original coefficient norm. -/
theorem smoothing_family_coeff_le {ρ : ℝ → ℝ} (hρ : IsMollifier ρ)
    (L : Length) (f g e : {f : Circle L → ℝ //
      MemLp (fun x => (f x : ℂ)) 2 (arclength L)}) {t : ℝ} (ht : 0 < t)
    (hg : ∀ x : ℝ, g.val (x : Circle L) =
      circleMollify ρ L.val t (fun y : ℝ => f.val (y : Circle L)) x)
    (he : ∀ x, e.val x = f.val x - g.val x) (k : ℤ) :
    ‖coeff L ⟨(fun x => (g.val x : ℂ)), complexL2Integrable L _ g.property⟩ k‖ ≤
      ‖coeff L ⟨(fun x => (f.val x : ℂ)), complexL2Integrable L _ f.property⟩ k‖ ∧
    ‖coeff L ⟨(fun x => (e.val x : ℂ)), complexL2Integrable L _ e.property⟩ k‖ ≤
      2 * ‖coeff L ⟨(fun x => (f.val x : ℂ)), complexL2Integrable L _ f.property⟩ k‖ := by
  have : Fact (0 < L.val) := ⟨L.property⟩
  have hi := locallyIntegrable_circle_lift (T := L.val)
    (complexL2Integrable L _ f.property).re
  have hp : Function.Periodic (fun y : ℝ => f.val (y : Circle L)) L.val := by
    intro y; simp only [AddCircle.coe_add_period]
  have hgk := fourierCoeff_circleMollify hρ ht hi hp f.val g.val (fun _ => rfl) hg k
  change coeff L ⟨(fun x => (g.val x : ℂ)), complexL2Integrable L _ g.property⟩ k =
    coeff L ⟨(fun x => (f.val x : ℂ)), complexL2Integrable L _ f.property⟩ k *
      (mollifierFT ρ (t * k / L.val) : ℂ) at hgk
  have hnorm : ‖coeff L ⟨(fun x => (g.val x : ℂ)), complexL2Integrable L _ g.property⟩ k‖ ≤
      ‖coeff L ⟨(fun x => (f.val x : ℂ)), complexL2Integrable L _ f.property⟩ k‖ := by
    rw [hgk, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (norm_nonneg _) (mollifierFT_abs_le_one hρ.isCircleMollifier _)
  refine ⟨hnorm, ?_⟩
  have hek : coeff L ⟨(fun x => (e.val x : ℂ)), complexL2Integrable L _ e.property⟩ k =
      coeff L ⟨(fun x => (f.val x : ℂ)), complexL2Integrable L _ f.property⟩ k -
      coeff L ⟨(fun x => (g.val x : ℂ)), complexL2Integrable L _ g.property⟩ k := by
    have heq : e = ⟨(fun x => f.val x - g.val x), by
      exact (f.property.sub g.property).ae_eq
        (ae_of_all _ fun x => by simp only [Pi.sub_apply, Complex.ofReal_sub])⟩ :=
      Subtype.ext (funext he)
    rw [heq]
    exact coeff_sub_real_L2 L f g k
  rw [hek]
  exact (norm_sub_le _ _).trans (by linarith)

/-- A variance rate with its constant before both the profile and the circle.
The low and high frequency bounds can therefore be inherited by a family. -/
theorem variance_smoothing_of_common_coeff_bounds (P : Parameters) (α ε Z K : ℝ)
    (hα0 : P.val.2 - 1 ≤ α) (hα1 : α < P.val.2 / 2) (hε : 0 < ε)
    (ρ : ℝ → ℝ) (hρ : IsMollifier ρ) :
    let d := P.val.2 / 2 - α
    let r := (max 0 (d - ε) + d) / 2
    let δ := (d - r) / 2
    ∃ C : ℝ, 0 < C ∧ ∀ (a : Scale) (v : Profile),
      (∀ k : ℤ, (observationLength a).val * ‖fourierCoeff (fun x => (v.val x : ℂ)) k‖ ≤ Z) →
      (∀ k : ℤ, 1 ≤ |2 * Real.pi * (k : ℝ) / (observationLength a).val| →
        (observationLength a).val * ‖fourierCoeff (fun x => (v.val x : ℂ)) k‖ ≤
          K * |2 * Real.pi * (k : ℝ) / (observationLength a).val| ^ (α - 1 + δ)) →
      ∀ h : ℝ, 0 < h → h ≤ 1 → ∃ g e : Profile,
        ContDiff ℝ ∞ (fun x : ℝ => g.val (x : UnitAddCircle)) ∧
        (∀ x : ℝ, g.val (x : UnitAddCircle) = circleMollify ρ 1 (h / (observationLength a).val)
          (fun y : ℝ => v.val (y : UnitAddCircle)) x) ∧
        (∀ x, e.val x = v.val x - g.val x) ∧
        ENNReal.ofReal (a.val ^ (-P.val.2)) * circleVariance P e ⟨1, by norm_num⟩ < ⊤ ∧
        Real.sqrt (ENNReal.ofReal (a.val ^ (-P.val.2)) * circleVariance P e ⟨1, by norm_num⟩).toReal ≤
          C * h ^ (P.val.2 / 2 - α - ε) := by
  dsimp only
  let d := P.val.2 / 2 - α
  have hd : 0 < d := by dsimp [d]; linarith
  have hd1 : d < 1 := by dsimp [d]; linarith [P.property.2.1]
  let r := (max 0 (d - ε) + d) / 2
  have hmax : max 0 (d - ε) < d := max_lt hd (by linarith)
  have hrlo : max 0 (d - ε) < r := by dsimp [r]; linarith
  have hrhi : r < d := by dsimp [r]; linarith
  have hr : 0 < r := (le_max_left _ _).trans_lt hrlo
  have hr1 : r ≤ 1 := (hrhi.trans hd1).le
  have hrate : d - ε ≤ r := (le_max_right _ _).trans hrlo.le
  let δ := (d - r) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  let σ := (1 - P.val.2) / 2
  obtain ⟨D, hD, hweighted⟩ := FourierGrid.weighted_coeff_mesh_bound
    (a := 2 * (σ + r)) (g := α - 1 + δ) (Z := Z) (K := K)
    (by dsimp [σ]; linarith [P.property.2.2])
    (by dsimp [σ, δ, d] at *; linarith)
  let A := 1 / (2 * P.val.1 * rieszConstant (parametersExponent P))
  have hA : 0 ≤ A := by
    have hc := rieszConstant_pos (parametersExponent P)
    have hb := P.property.1
    dsimp [A]
    positivity
  let T := A * (16 / (2 * Real.pi) ^ (2 * r) * D)
  have hT : 0 ≤ T := by dsimp [T]; positivity
  let C := Real.sqrt T + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hTC : T ≤ C ^ 2 := by
    dsimp [C]
    nlinarith [Real.sq_sqrt hT, Real.sqrt_nonneg T]
  refine ⟨C, hC, fun a v hlo hhi h hh hh1 => ?_⟩
  let L := observationLength a
  have hL : 0 < L.val := L.property
  have hL1 : 1 ≤ L.val := (one_le_inv₀ a.property.1).mpr a.property.2
  have hhL : h / L.val ≤ 1 := (div_le_one hL).mpr (hh1.trans hL1)
  let f : {f : UnitAddCircle → ℂ // MemLp f 2 volume} :=
    ⟨(fun x => (v.val x : ℂ)), v.property⟩
  obtain ⟨hs, hb⟩ := hweighted L.val hL (fun k => fourierCoeff f.val k) hlo hhi
  have hH := Internal.physical_sobolev_bound hL f hs hb
  obtain ⟨g, hgc, hgs, hgv, hgf⟩ := Internal.exists_circleMollify_L2 hρ unitLength
    (div_pos hh hL) ⟨v.val, v.property⟩
  change Profile at g
  change (∀ x : ℝ, g.val (x : UnitAddCircle) = circleMollify ρ 1 (h / L.val)
    (fun t : ℝ => v.val (t : UnitAddCircle)) x) at hgv
  let e : Profile := ⟨(fun x => v.val x - g.val x), by
    exact ((v.property).sub g.property).ae_eq
      (ae_of_all _ fun x => by simp only [Pi.sub_apply, Complex.ofReal_sub])⟩
  have heq : circleSobolevSq σ ⟨(fun x => (e.val x : ℂ)), e.property⟩ =
      circleSobolevSq σ (subL2 f (regularizeL2 hρ.isCircleMollifier
        ⟨h / L.val, div_pos hh hL⟩ hhL f)) := by
    unfold circleSobolevSq
    apply tsum_congr
    intro k
    by_cases hk : k = 0
    · simp only [hk, ite_true]
    · simp only [hk, ite_false]
      congr 3
      apply congrArg norm
      have hd := Internal.coeff_sub_real_L2 unitLength
        ⟨v.val, v.property⟩ g k
      change fourierCoeff (fun x => (e.val x : ℂ)) k =
        fourierCoeff f.val k - fourierCoeff (fun x => (g.val x : ℂ)) k at hd
      rw [hd, fourierCoeff_subL2, fourierCoeff_regularizeL2]
      have hgk := hgf k
      change fourierCoeff (fun x => (g.val x : ℂ)) k =
        fourierCoeff f.val k * (mollifierFT ρ ((h / L.val) * k / 1) : ℂ) at hgk
      simpa only [div_one] using congrArg (fun z : ℂ => fourierCoeff f.val k - z) hgk
  have hb := Internal.physical_smoothing_bound hρ.isCircleMollifier hL hh hhL hr hr1 f hH
  rw [← heq] at hb
  have hv := mul_le_mul (show ENNReal.ofReal A ≤ ENNReal.ofReal A from le_rfl) hb zero_le zero_le
  rw [show 2 * σ = 1 - P.val.2 by dsimp [σ]; ring] at hv
  rw [← Internal.scaled_unit_variance_eq_physical P a e] at hv
  rw [← ENNReal.ofReal_mul hA] at hv
  have hv' : ENNReal.ofReal (a.val ^ (-P.val.2)) * circleVariance P e ⟨1, by norm_num⟩ ≤
      ENNReal.ofReal (T * h ^ (2 * r)) := by simpa only [T, mul_assoc] using hv
  have hfin := hv'.trans_lt ENNReal.ofReal_lt_top
  refine ⟨g, e, hgs, hgv, fun _ => rfl, hfin, ?_⟩
  have hvreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hv'
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ T * h ^ (2 * r))] at hvreal
  have hpower : h ^ (2 * r) = (h ^ r) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hh.le]
    congr 1
    ring
  have hsqrt : Real.sqrt (ENNReal.ofReal (a.val ^ (-P.val.2)) *
      circleVariance P e ⟨1, by norm_num⟩).toReal ≤ C * h ^ r := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    rw [hpower] at hvreal
    exact hvreal.trans (by rw [mul_pow]; exact mul_le_mul_of_nonneg_right hTC (sq_nonneg _))
  exact hsqrt.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_ge hh hh1 hrate) hC.le)


end Riesz1.Internal
