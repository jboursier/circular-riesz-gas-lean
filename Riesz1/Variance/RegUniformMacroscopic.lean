/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.RegUniformPrimitive
public import Riesz1.Kernel.AdmissibilityRegularityMembership
public import Riesz1.Frozen.CircleVariance
public import Riesz1.ToMathlib.Mollifier.RegularizationSobolev

/-!
# The macroscopic variance smoothing rate

The first bound of Lemma 5.1 for the macroscopic alternative.
The variance is proved finite before its real square root is bounded.
-/

public section

open MeasureTheory
open scoped ENNReal ContDiff

namespace Riesz1

/-- The variance-smoothing clause of Lemma 5.1 on the unit circle.
The radius-independent constant depends only on the fixed macroscopic data and
the exponent loss. The representative is exactly the regularization. -/
theorem regUniform_variance_macroscopic (P : Parameters) (p : Profile)
    (η B : ℝ) (n : ℕ+) (marks : Fin (n : ℕ) → ℝ) (α C₀ ε : ℝ)
    (hη : 0 < η) (hB : 0 ≤ B) (hC₀ : 0 ≤ C₀)
    (hα0 : P.val.2 - 1 ≤ α) (hα1 : α < P.val.2 / 2) (hε : 0 < ε)
    (hprim : PrimitiveRegularity unitLength η P.val.2 B ⟨p.val, p.property⟩)
    (hreg : TransportRegularity P unitLength ⟨p.val, p.property⟩ n marks α C₀)
    (ρ : ℝ → ℝ) (hρ : IsMollifier ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ h : ℝ, 0 < h → h ≤ 1 →
      ∃ g e : Profile, ContDiff ℝ ∞ (fun x : ℝ => g.val (x : UnitAddCircle)) ∧
        (∀ x : ℝ, g.val (x : UnitAddCircle) =
          circleMollify ρ 1 h (fun t : ℝ => p.val (t : UnitAddCircle)) x) ∧
        (∀ x, e.val x = p.val x - g.val x) ∧
        circleVariance P e ⟨1, by norm_num⟩ < ⊤ ∧
        Real.sqrt (circleVariance P e ⟨1, by norm_num⟩).toReal ≤
          C * h ^ (P.val.2 / 2 - α - ε) := by
  have : Fact (0 < unitLength.val) := ⟨unitLength.property⟩
  let a := P.val.2 / 2 - α
  have ha : 0 < a := by dsimp [a]; linarith
  have ha1 : a < 1 := by dsimp [a]; linarith [P.property.2.1]
  have hmax : max 0 (a - ε) < a := max_lt ha (by linarith)
  obtain ⟨r, hrlo, hrhi⟩ := exists_between hmax
  have hr : 0 < r := (le_max_left _ _).trans_lt hrlo
  have hr1 : r ≤ 1 := (hrhi.trans ha1).le
  have hrate : a - ε ≤ r := (le_max_right _ _).trans hrlo.le
  let δ := (a - r) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  obtain ⟨K, _, hdec⟩ := coeff_decay_of_primitive_transportRegularity P unitLength
    η B hη hB ⟨p.val, p.property⟩ n marks α C₀ hα0 hα1 hC₀ hprim hreg δ hδ
  have hsob := Internal.circleSobolev_of_circle_frequency_decay unitLength
    (s := P.val.2 - 2 * r) (α := α) (ε := δ) (K := K)
    (by dsimp [δ, a] at *; linarith) p.property
    (fun k => coeff unitLength ⟨(fun x => (p.val x : ℂ)),
      complexL2Integrable unitLength _ p.property⟩ k) (fun _ => rfl) hdec
  let σ := (1 - P.val.2) / 2
  let f : {f : UnitAddCircle → ℂ // MemLp f 2 volume} :=
    ⟨(fun x => (p.val x : ℂ)), p.property⟩
  have hH : circleSobolevSq (σ + r) f < ⊤ := by
    have he : σ + r = (1 - (P.val.2 - 2 * r)) / 2 := by dsimp [σ]; ring
    rw [he]
    exact hsob.2
  let A := (2 * Real.pi) ^ (1 - P.val.2) /
    (2 * P.val.1 * rieszConstant (parametersExponent P))
  let H := circleSobolevSq (σ + r) f
  let D := (ENNReal.ofReal A).toReal * 16 * H.toReal
  have hD : 0 ≤ D := by dsimp [D]; positivity
  let C := Real.sqrt D + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hDC : D ≤ C ^ 2 := by
    dsimp [C]
    nlinarith [Real.sq_sqrt hD, Real.sqrt_nonneg D]
  refine ⟨C, hC, fun h hh hh1 => ?_⟩
  obtain ⟨g, _, hgs, hgv, hgf⟩ :=
    Internal.exists_circleMollify_L2 hρ unitLength hh ⟨p.val, p.property⟩
  change Profile at g
  let e : Profile := ⟨(fun x => p.val x - g.val x), by
    exact (p.property.sub g.property).ae_eq
      (ae_of_all _ fun x => by
        change (p.val x : ℂ) - (g.val x : ℂ) = ((p.val x - g.val x : ℝ) : ℂ)
        rw [Complex.ofReal_sub])⟩
  have he (x : UnitAddCircle) : e.val x = p.val x - g.val x := rfl
  refine ⟨g, e, hgs, hgv, he, ?_⟩
  have hcoeff (k : ℤ) : fourierCoeff (fun x => (e.val x : ℂ)) k =
      fourierCoeff (subL2 f (regularizeL2 hρ.isCircleMollifier ⟨h, hh⟩ hh1 f)).val k := by
    have hef : (fun x => (e.val x : ℂ)) =
        (fun x => ((p.val x - g.val x : ℝ) : ℂ)) := by funext x; rw [he x]
    rw [hef]
    have hs := Internal.coeff_sub_real_L2 unitLength ⟨p.val, p.property⟩ g k
    change fourierCoeff (fun x => ((p.val x - g.val x : ℝ) : ℂ)) k =
      fourierCoeff (fun x => (p.val x : ℂ)) k -
        fourierCoeff (fun x => (g.val x : ℂ)) k at hs
    rw [hs, fourierCoeff_subL2, fourierCoeff_regularizeL2]
    have hgk := hgf k
    change fourierCoeff (fun x => (g.val x : ℂ)) k =
      fourierCoeff f.val k * (mollifierFT ρ (h * k / 1) : ℂ) at hgk
    simp only [div_one] at hgk
    exact congrArg (fun z : ℂ => fourierCoeff f.val k - z) hgk
  have heq : circleSobolevSq σ ⟨(fun x => (e.val x : ℂ)), e.property⟩ =
      circleSobolevSq σ (subL2 f (regularizeL2 hρ.isCircleMollifier ⟨h, hh⟩ hh1 f)) := by
    unfold circleSobolevSq
    simp_rw [hcoeff]
  have hbound := circleSobolevSq_subL2_le hρ.isCircleMollifier ⟨h, hh⟩ hh1 f hr hr1
    (σ := σ)
  rw [← heq] at hbound
  have hvar : circleVariance P e ⟨1, by norm_num⟩ ≤
      ENNReal.ofReal A * (ENNReal.ofReal (16 * h ^ (2 * r)) * H) := by
    have hv : circleVariance P e ⟨1, by norm_num⟩ =
        ENNReal.ofReal A * circleSobolevSq σ ⟨(fun x => (e.val x : ℂ)), e.property⟩ := by
      simp only [circleVariance, testAtScale, σ, A, Real.one_rpow, mul_one,
        ite_true]
    rw [hv]
    exact mul_le_mul le_rfl hbound zero_le zero_le
  have hright : ENNReal.ofReal A * (ENNReal.ofReal (16 * h ^ (2 * r)) * H) < ⊤ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hH)
  have hfinite := hvar.trans_lt hright
  refine ⟨hfinite, ?_⟩
  have hv := ENNReal.toReal_mono hright.ne hvar
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 16 * h ^ (2 * r))] at hv
  have hv' : (circleVariance P e ⟨1, by norm_num⟩).toReal ≤ D * h ^ (2 * r) := by
    dsimp only [D]
    nlinarith [hv]
  have hpower : h ^ (2 * r) = (h ^ r) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hh.le]
    congr 1
    ring
  have hsqrt : Real.sqrt (circleVariance P e ⟨1, by norm_num⟩).toReal ≤ C * h ^ r := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    rw [hpower] at hv'
    exact hv'.trans (by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right hDC (sq_nonneg _))
  exact hsqrt.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_ge hh hh1 hrate) hC.le)

end Riesz1
