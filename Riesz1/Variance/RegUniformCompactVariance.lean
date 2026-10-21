/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.RegUniformPrimitive
public import Riesz1.Kernel.AdmissibilityRegularityUniformCompact
public import Riesz1.ToMathlib.PhysicalCircleSobolev
public import Riesz1.ToMathlib.CircleFourierUniqueness

/-!
# Compact-profile variance smoothing rate

The variance clause of Lemma 5.1, uniformly over every
observation circle. The error is displayed after pullback to the unit circle.
Its unit-circle variance is multiplied by the required scale factor.
-/

public section

open MeasureTheory Filter
open scoped ENNReal ContDiff Topology

namespace Riesz1
namespace Internal

theorem smoothed_profile_pullback {ρ : ℝ → ℝ} (hρ : IsMollifier ρ)
    (p : Profile) (a : Scale) {h : ℝ} (hh : 0 < h) (g : Profile)
    (hgc : Continuous g.val)
    (hgf : ∀ k : ℤ, fourierCoeff (fun x => (g.val x : ℂ)) k =
      fourierCoeff (fun x => (testAtScale p a x : ℂ)) k *
        (mollifierFT ρ ((h / (observationLength a).val) * k) : ℂ)) :
    ∀ x : ℝ, g.val (x : UnitAddCircle) =
      circleMollify ρ (observationLength a).val h
        (fun t : ℝ => periodizedProfile p (observationLength a) (t : Circle (observationLength a)))
        ((observationLength a).val * x) := by
  let L := observationLength a
  have : Fact (0 < L.val) := ⟨L.property⟩
  obtain ⟨G, hGc, _, hGv, hGf⟩ := exists_circleMollify_L2 hρ L hh
    ⟨periodizedProfile p L, periodizedProfileL2 p a⟩
  let F : ℝ → ℝ := fun x => G.val ((L.val * x : ℝ) : Circle L)
  have hFc : Continuous F := hGc.comp ((AddCircle.continuous_mk' L.val).comp (continuous_const.mul continuous_id))
  have hFp : Function.Periodic F 1 := by
    intro x
    dsimp [F]
    rw [show L.val * (x + 1) = L.val * x + L.val by ring, AddCircle.coe_add_period]
  let q : UnitAddCircle → ℝ := hFp.lift
  have hqv (x : ℝ) : q (x : UnitAddCircle) = F x := hFp.lift_coe x
  have hqc : Continuous q :=
    (QuotientAddGroup.isQuotientMap_mk (AddSubgroup.zmultiples (1 : ℝ))).continuous_iff.mpr (by
      simpa only [Function.comp_def, hqv] using hFc)
  have hqm : MemLp (fun x => (q x : ℂ)) 2 volume :=
    (Complex.continuous_ofReal.comp hqc).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have heqC := CircleFourier.ae_eq_of_coeff_eq g.property hqm (fun k => by
    rw [CircleFourier.coeff_eq_of_scaled_lifts
      (f := fun y => (G.val y : ℂ)) (g := fun y => (q y : ℂ))
      (fun t _ => congrArg Complex.ofReal (hqv t)) k]
    rw [hgf, testAtScale_coeff_eq_periodized]
    have hk := hGf k
    change fourierCoeff (fun y => (G.val y : ℂ)) k = _ at hk
    rw [hk]
    congr 3
    ring)
  have heq : g.val = q := Measure.eq_of_ae_eq
    (heqC.mono fun _ hx => Complex.ofReal_injective hx) hgc hqc
  intro x
  rw [heq, hqv]
  exact hGv (L.val * x)

theorem scaled_unit_variance_eq_physical (P : Parameters) (a : Scale) (e : Profile) :
    ENNReal.ofReal (a.val ^ (-P.val.2)) * circleVariance P e ⟨1, by norm_num⟩ =
      ENNReal.ofReal (1 / (2 * P.val.1 * rieszConstant (parametersExponent P))) *
        (ENNReal.ofReal ((observationLength a).val *
          (2 * Real.pi / (observationLength a).val) ^ (1 - P.val.2)) *
          circleSobolevSq ((1 - P.val.2) / 2)
            ⟨(fun x => (e.val x : ℂ)), e.property⟩) := by
  have hc : 0 < rieszConstant (parametersExponent P) := rieszConstant_pos _
  have hb : 0 < P.val.1 := P.property.1
  have ha := a.property.1
  have he : a.val ^ (-P.val.2) *
      ((2 * Real.pi) ^ (1 - P.val.2) / (2 * P.val.1 * rieszConstant (parametersExponent P))) =
      (1 / (2 * P.val.1 * rieszConstant (parametersExponent P))) *
        ((observationLength a).val * (2 * Real.pi / (observationLength a).val) ^ (1 - P.val.2)) := by
    change _ = _ * (a.val⁻¹ * (2 * Real.pi / a.val⁻¹) ^ (1 - P.val.2))
    rw [div_inv_eq_mul, Real.mul_rpow (by positivity : 0 ≤ 2 * Real.pi) ha.le]
    have hp : a.val⁻¹ * a.val ^ (1 - P.val.2) = a.val ^ (-P.val.2) := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add ha]
      congr 1
      ring
    calc _ = ((2 * Real.pi) ^ (1 - P.val.2) /
          (2 * P.val.1 * rieszConstant (parametersExponent P))) *
          (a.val⁻¹ * a.val ^ (1 - P.val.2)) := by rw [hp]; ring
      _ = _ := by ring
  simp only [circleVariance, testAtScale, ite_true, Real.one_rpow, mul_one]
  rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg ha.le _), he,
    ENNReal.ofReal_mul (by positivity : 0 ≤ 1 / (2 * P.val.1 * rieszConstant (parametersExponent P))),
    mul_assoc]

end Internal

/-- The compact variance clause of Lemma 5.1. Here `g` regularizes the
actual unit-circle observation at radius `h / L`, corresponding to physical radius
`h` on the profile circle. The scale factor outside the variance restores
exactly `σ_ell`, and the constant precedes the scale sequence and circle length. -/
theorem regUniform_variance_compact (P : Parameters) (p : Profile) (hp : CompactProfile p)
    (η B : ℝ) (n : ℕ+) (marks : Fin (n : ℕ) → ℝ) (α C₀ ε : ℝ)
    (hη : 0 < η) (hB : 0 ≤ B) (hC₀ : 0 ≤ C₀)
    (hα0 : P.val.2 - 1 ≤ α) (hα1 : α < P.val.2 / 2) (hε : 0 < ε)
    (ρ : ℝ → ℝ) (hρ : IsMollifier ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ell : Scales,
      Tendsto (fun k : ℕ => (ell ⟨k + 1, Nat.succ_pos k⟩).val) atTop (𝓝 0) →
      (∀ N, PrimitiveRegularity (observationLength (ell N)) η P.val.2 B
          ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ ∧
        TransportRegularity P (observationLength (ell N))
          ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩
            n marks α C₀) →
      ∀ (a : Scale) (h : ℝ), 0 < h → h ≤ 1 →
        ∃ g e : Profile, ContDiff ℝ ∞ (fun x : ℝ => g.val (x : UnitAddCircle)) ∧
          (∀ x : ℝ, g.val (x : UnitAddCircle) =
            circleMollify ρ 1 (h / (observationLength a).val)
              (fun t : ℝ => testAtScale p a (t : UnitAddCircle)) x) ∧
          (∀ x : ℝ, g.val (x : UnitAddCircle) =
            circleMollify ρ (observationLength a).val h
              (fun t : ℝ => periodizedProfile p (observationLength a)
                (t : Circle (observationLength a))) ((observationLength a).val * x)) ∧
          (∀ x, e.val x = testAtScale p a x - g.val x) ∧
          ENNReal.ofReal (a.val ^ (-P.val.2)) * circleVariance P e ⟨1, by norm_num⟩ < ⊤ ∧
          Real.sqrt (ENNReal.ofReal (a.val ^ (-P.val.2)) *
            circleVariance P e ⟨1, by norm_num⟩).toReal ≤
              C * h ^ (P.val.2 / 2 - α - ε) := by
  let d := P.val.2 / 2 - α
  have hd : 0 < d := by dsimp [d]; linarith
  have hd1 : d < 1 := by dsimp [d]; linarith [P.property.2.1]
  obtain ⟨r, hrlo, hrhi⟩ := exists_between (max_lt hd (by linarith : d - ε < d))
  have hr : 0 < r := (le_max_left _ _).trans_lt hrlo
  have hr1 : r ≤ 1 := (hrhi.trans hd1).le
  have hrate : d - ε ≤ r := (le_max_right _ _).trans hrlo.le
  let δ := (d - r) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  let σ := (1 - P.val.2) / 2
  obtain ⟨K, _, hdec⟩ := uniform_compact_profile_coeff_decay P p hp η B hη hB
    n marks α C₀ hα0 hα1 hC₀ δ hδ
  let Z := ∫ x : ℝ, |zeroExtension p x|
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
  refine ⟨C, hC, fun ell hell hfamily a h hh hh1 => ?_⟩
  let L := observationLength a
  have hL : 0 < L.val := L.property
  have hL1 : 1 ≤ L.val := (one_le_inv₀ a.property.1).mpr a.property.2
  have hhL : h / L.val ≤ 1 := (div_le_one hL).mpr (hh1.trans hL1)
  let f : {f : UnitAddCircle → ℂ // MemLp f 2 volume} :=
    ⟨(fun x => (testAtScale p a x : ℂ)), testAtScaleL2 p a⟩
  have hlo (k : ℤ) : L.val * ‖fourierCoeff f.val k‖ ≤ Z := by
    rw [show fourierCoeff f.val k = coeff L
      ⟨(fun x => (periodizedProfile p L x : ℂ)), complexL2Integrable _ _ (periodizedProfileL2 p a)⟩ k
      from testAtScale_coeff_eq_periodized p a k]
    have hb := norm_zeroExtension_fourierIntegral_le p (2 * Real.pi * (k : ℝ) / L.val)
    rw [← length_mul_periodizedProfile_coeff p a k, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hL] at hb
    exact hb
  have hhi (k : ℤ) (hk : 1 ≤ |2 * Real.pi * (k : ℝ) / L.val|) :
      L.val * ‖fourierCoeff f.val k‖ ≤ K * |2 * Real.pi * (k : ℝ) / L.val| ^ (α - 1 + δ) := by
    rw [show fourierCoeff f.val k = coeff L
      ⟨(fun x => (periodizedProfile p L x : ℂ)), complexL2Integrable _ _ (periodizedProfileL2 p a)⟩ k
      from testAtScale_coeff_eq_periodized p a k]
    have hm := mul_le_mul_of_nonneg_left (hdec ell hell hfamily a k hk) hL.le
    calc _ ≤ L.val * (K * L.val⁻¹ * |2 * Real.pi * (k : ℝ) / L.val| ^ (α - 1 + δ)) := hm
      _ = _ := by field_simp
  obtain ⟨hs, hb⟩ := hweighted L.val hL (fun k => fourierCoeff f.val k) hlo hhi
  have hH := Internal.physical_sobolev_bound hL f hs hb
  obtain ⟨g, hgc, hgs, hgv, hgf⟩ := Internal.exists_circleMollify_L2 hρ unitLength
    (div_pos hh hL) ⟨testAtScale p a, testAtScaleL2 p a⟩
  change Profile at g
  change (∀ x : ℝ, g.val (x : UnitAddCircle) = circleMollify ρ 1 (h / L.val)
    (fun t : ℝ => testAtScale p a (t : UnitAddCircle)) x) at hgv
  let e : Profile := ⟨(fun x => testAtScale p a x - g.val x), by
    exact ((testAtScaleL2 p a).sub g.property).ae_eq
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
        ⟨testAtScale p a, testAtScaleL2 p a⟩ g k
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
  have hphysical := Internal.smoothed_profile_pullback hρ p a hh g hgc (fun k => by
    have hk := hgf k
    change fourierCoeff (fun x => (g.val x : ℂ)) k =
      fourierCoeff f.val k * (mollifierFT ρ ((h / L.val) * k / 1) : ℂ) at hk
    simpa only [div_one] using hk)
  refine ⟨g, e, hgs, hgv, hphysical, fun _ => rfl, hfin, ?_⟩
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

end Riesz1
