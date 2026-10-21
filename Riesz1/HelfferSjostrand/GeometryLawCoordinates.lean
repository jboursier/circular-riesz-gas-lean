/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.GeometryLawDensity
public import Riesz1.HelfferSjostrand.SettingQuotient
public import Riesz1.ToMathlib.Chamber.OrthogonalSplit
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Coordinates `(z, ω)` on the cyclic configurations and the fiber integral

These coordinates and the product law are used in the geometry part of the proof of Lemma 3.6. For
`N : ℕ+`, let `e = N^{-1/2} (1, …, 1)` (`hsUnitVector`) and let `e^⊥` be its orthogonal
complement (`hsOrthSubspace`). A lift point splits as `x = z + t e` with `z ∈ e^⊥` and
`t = ⟪x, e⟫`. The circle coordinate `ω` is `t` read modulo `√N` in `AddCircle (√N)`.

The main result of this file is the fiber identity `lintegral_configuration_fiber`: integrating
over the fundamental region equals integrating over the radial domain `B_N ⊂ e^⊥`, times an
integral over the circle. The fiber over each `z ∈ B_N` is an interval of length `√N`, and the
integral of a `√N`-periodic function over such an interval is the circle integral. The product
law is proved from this identity in `Riesz1.HelfferSjostrand.GeometryLawProduct`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Submodule
open scoped ENNReal RealInnerProductSpace

namespace Riesz1

/-- The circle `AddCircle (√N)` carries its Lebesgue volume, of total mass `√N`. -/
instance hsSqrt_fact (N : ℕ+) : Fact (0 < Real.sqrt (N : ℕ)) :=
  ⟨Real.sqrt_pos.mpr (Nat.cast_pos.mpr N.pos)⟩

/-- The unit vector `e = N^{-1/2} (1, …, 1)` has Euclidean length one. -/
theorem hsUnitVector_norm (N : ℕ+) : ‖hsUnitVector N‖ = 1 := by
  have hs : (0 : ℝ) < Real.sqrt (N : ℕ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr N.pos)
  have hr : ‖hsRotationVector N‖ = Real.sqrt (N : ℕ) := by
    rw [EuclideanSpace.norm_eq]
    simp [hsRotationVector]
  rw [hsUnitVector, norm_smul, hr, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs),
    inv_mul_cancel₀ hs.ne']

/-- The hyperplane `e^⊥`, the orthogonal complement of the unit vector `e`. -/
abbrev hsOrthSubspace (N : ℕ+) : Submodule ℝ (HsEuclidean N) := (ℝ ∙ hsUnitVector N)ᗮ

/-- The orthogonal coordinate `z = x - ⟪x, e⟫ e` of a lift point, in `e^⊥`. -/
def hsOrthComp (N : ℕ+) (x : HsEuclidean N) : hsOrthSubspace N :=
  orthComponent (hsUnitVector_norm N) x

/-- The circle coordinate `ω = ⟪x, e⟫ mod √N`, in `AddCircle (√N)`. -/
def hsAngle (N : ℕ+) (x : HsEuclidean N) : AddCircle (Real.sqrt (N : ℕ)) :=
  ((inner ℝ x (hsUnitVector N) : ℝ) : AddCircle (Real.sqrt (N : ℕ)))

/-- The coordinates `(z, ω)` of a lift point. -/
def hsCoord (N : ℕ+) (x : HsEuclidean N) :
    hsOrthSubspace N × AddCircle (Real.sqrt (N : ℕ)) :=
  (hsOrthComp N x, hsAngle N x)

/-- The coordinates `(z, ω)` of a configuration of the fundamental region. -/
def hsConfigCoord (N : ℕ+) (X : Configuration N) :
    hsOrthSubspace N × AddCircle (Real.sqrt (N : ℕ)) :=
  hsCoord N (WithLp.toLp 2 X.val)

/-- The radial domain `B_N = {z ∈ e^⊥ : z ∈ 𝒞_N}`, as a subset of `e^⊥`. -/
def hsRadialDomain (N : ℕ+) : Set (hsOrthSubspace N) :=
  {z | (z : HsEuclidean N) ∈ hsChamber N}

theorem hsOrthComp_add_smul (N : ℕ+) (x : HsEuclidean N) :
    (hsOrthComp N x : HsEuclidean N) + inner ℝ x (hsUnitVector N) • hsUnitVector N = x := by
  change x - inner ℝ x (hsUnitVector N) • hsUnitVector N +
    inner ℝ x (hsUnitVector N) • hsUnitVector N = x
  abel

theorem measurable_hsOrthComp (N : ℕ+) : Measurable (hsOrthComp N) := by
  have hf : Measurable fun x : HsEuclidean N =>
      x - inner ℝ x (hsUnitVector N) • hsUnitVector N := by
    fun_prop
  exact hf.subtype_mk

theorem measurable_hsAngle (N : ℕ+) : Measurable (hsAngle N) :=
  QuotientAddGroup.measurable_coe.comp (continuous_id.inner continuous_const).measurable

theorem measurable_hsCoord (N : ℕ+) : Measurable (hsCoord N) :=
  (measurable_hsOrthComp N).prodMk (measurable_hsAngle N)

/-- Translating along `e` is a real translation of all coordinates by `t / √N`. -/
theorem add_smul_hsUnitVector (N : ℕ+) (z : HsEuclidean N) (t : ℝ) :
    z + t • hsUnitVector N = hsTranslate (t * (Real.sqrt (N : ℕ))⁻¹) z := by
  ext i
  simp [hsUnitVector, hsRotationVector, hsTranslate_apply]

theorem add_smul_hsUnitVector_apply_zero (N : ℕ+) (z : HsEuclidean N) (t : ℝ) :
    (z + t • hsUnitVector N) ⟨0, N.pos⟩ = z ⟨0, N.pos⟩ + t * (Real.sqrt (N : ℕ))⁻¹ := by
  simp [hsUnitVector, hsRotationVector]

/-- The elementary inequality behind the fiber: the condition `0 ≤ z₀ + t / s < 1` is the
interval `-s z₀ ≤ t < -s z₀ + s`. -/
theorem fiber_interval_iff {s z₀ t : ℝ} (hs : 0 < s) :
    (0 ≤ z₀ + t * s⁻¹ ∧ z₀ + t * s⁻¹ < 1) ↔ (-(s * z₀) ≤ t ∧ t < -(s * z₀) + s) := by
  have hk : s * (z₀ + t * s⁻¹) = s * z₀ + t := by
    field_simp
  constructor
  · rintro ⟨h0, h1⟩
    constructor
    · linarith [mul_nonneg hs.le h0]
    · have := mul_lt_mul_of_pos_left h1 hs
      linarith
  · rintro ⟨h0, h1⟩
    constructor
    · exact (mul_nonneg_iff_of_pos_left hs).mp (by linarith)
    · exact lt_of_mul_lt_mul_left (by linarith) hs.le

/-- The fiber of the fundamental region over `z ∈ e^⊥`: the point `z + t e` lies in the
fundamental region exactly when `z` lies in the radial domain and `t` lies in an interval of
length `√N`. -/
theorem add_smul_mem_hsFundamentalRegion_iff (N : ℕ+) (z : hsOrthSubspace N) (t : ℝ) :
    (z : HsEuclidean N) + t • hsUnitVector N ∈ hsFundamentalRegion N ↔
      z ∈ hsRadialDomain N ∧
        t ∈ Ico (-(Real.sqrt (N : ℕ) * (z : HsEuclidean N) ⟨0, N.pos⟩))
          (-(Real.sqrt (N : ℕ) * (z : HsEuclidean N) ⟨0, N.pos⟩) + Real.sqrt (N : ℕ)) := by
  have hs : (0 : ℝ) < Real.sqrt (N : ℕ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr N.pos)
  have hchamber : (z : HsEuclidean N) + t • hsUnitVector N ∈ hsChamber N ↔
      (z : HsEuclidean N) ∈ hsChamber N := by
    rw [add_smul_hsUnitVector]
    exact hsTranslate_mem_chamber_iff _ _
  rw [hsFundamentalRegion, mem_ofPred_eq, hchamber, add_smul_hsUnitVector_apply_zero,
    mem_Ico, ← fiber_interval_iff hs]
  simp only [hsRadialDomain, mem_ofPred_eq, and_comm, and_assoc]

/-- A window `[a, a + √N)` of the real line covers the circle exactly once, so the integral of a
function of the circle coordinate over the window is the integral over the circle. -/
theorem lintegral_Ico_circle (N : ℕ+) (a : ℝ) {G : AddCircle (Real.sqrt (N : ℕ)) → ℝ≥0∞}
    (hG : Measurable G) :
    ∫⁻ t in Ico a (a + Real.sqrt (N : ℕ)), G (t : AddCircle (Real.sqrt (N : ℕ))) = ∫⁻ w, G w := by
  rw [Measure.restrict_congr_set (Ico_ae_eq_Ioc (μ := volume))]
  exact (AddCircle.measurePreserving_mk (Real.sqrt (N : ℕ)) a).lintegral_comp hG

/-- Fiber decomposition over the fundamental region in the lift: the integral of a product
`F₁(z) G₁(ω)` over the fundamental region is `∫_{B_N} F₁` times the integral of `G₁` over the
circle. Each fiber `{t : z + t e ∈ 𝒻}` is a window of length `√N`. -/
theorem lintegral_hsFundamentalRegion_fiber (N : ℕ+) {F₁ : hsOrthSubspace N → ℝ≥0∞}
    (hF : Measurable F₁) {G₁ : AddCircle (Real.sqrt (N : ℕ)) → ℝ≥0∞} (hG : Measurable G₁) :
    ∫⁻ x in hsFundamentalRegion N, F₁ (hsOrthComp N x) * G₁ (hsAngle N x) =
      (∫⁻ z in hsRadialDomain N, F₁ z) * ∫⁻ w, G₁ w := by
  classical
  have hB : MeasurableSet (hsRadialDomain N) := by
    have hopen : IsOpen (Subtype.val ⁻¹' hsChamber N : Set (hsOrthSubspace N)) :=
      (isOpen_hsChamber N).preimage continuous_subtype_val
    exact hopen.measurableSet
  -- the set of split coordinates whose lift lies in the fundamental region
  let Φs : Set (hsOrthSubspace N × ℝ) :=
    {p | (p.1 : HsEuclidean N) + p.2 • hsUnitVector N ∈ hsFundamentalRegion N}
  let h : hsOrthSubspace N × ℝ → ℝ≥0∞ :=
    Φs.indicator (fun p => F₁ p.1 * G₁ ((p.2 : ℝ) : AddCircle (Real.sqrt (N : ℕ))))
  have hΦs : MeasurableSet Φs := by
    refine (measurableSet_hsFundamentalRegion N).preimage ?_
    exact ((continuous_subtype_val.comp continuous_fst).add
      (continuous_snd.smul continuous_const)).measurable
  have hh : Measurable h := by
    refine Measurable.indicator ?_ hΦs
    exact (hF.comp measurable_fst).mul
      (hG.comp (QuotientAddGroup.measurable_coe.comp measurable_snd))
  have hpt : ∀ x : HsEuclidean N,
      (hsFundamentalRegion N).indicator (fun x => F₁ (hsOrthComp N x) * G₁ (hsAngle N x)) x =
        h (hsOrthComp N x, inner ℝ x (hsUnitVector N)) := by
    intro x
    simp only [h, Φs, indicator_apply, mem_ofPred_eq, hsOrthComp_add_smul, hsAngle]
  have hfiber : ∀ z : hsOrthSubspace N, ∫⁻ t, h (z, t) =
      (hsRadialDomain N).indicator (fun z => F₁ z * ∫⁻ w, G₁ w) z := by
    intro z
    by_cases hz : z ∈ hsRadialDomain N
    · rw [indicator_of_mem hz]
      have hwin : ∀ t : ℝ, h (z, t) = (Ico (-(Real.sqrt (N : ℕ) * (z : HsEuclidean N) ⟨0, N.pos⟩))
          (-(Real.sqrt (N : ℕ) * (z : HsEuclidean N) ⟨0, N.pos⟩) + Real.sqrt (N : ℕ))).indicator
          (fun t => F₁ z * G₁ ((t : ℝ) : AddCircle (Real.sqrt (N : ℕ)))) t := by
        intro t
        simp only [h, Φs, indicator_apply, mem_ofPred_eq, add_smul_mem_hsFundamentalRegion_iff,
          hz, true_and]
      have hGt : Measurable fun t : ℝ => G₁ ((t : ℝ) : AddCircle (Real.sqrt (N : ℕ))) :=
        hG.comp QuotientAddGroup.measurable_coe
      simp only [hwin]
      rw [lintegral_indicator measurableSet_Ico, lintegral_const_mul _ hGt,
        lintegral_Ico_circle N _ hG]
    · rw [indicator_of_notMem hz]
      simp only [h, Φs, indicator_apply, mem_ofPred_eq, add_smul_mem_hsFundamentalRegion_iff,
        hz, false_and, ite_false, lintegral_zero]
  calc ∫⁻ x in hsFundamentalRegion N, F₁ (hsOrthComp N x) * G₁ (hsAngle N x)
      = ∫⁻ x, (hsFundamentalRegion N).indicator
          (fun x => F₁ (hsOrthComp N x) * G₁ (hsAngle N x)) x :=
        (lintegral_indicator (measurableSet_hsFundamentalRegion N) _).symm
    _ = ∫⁻ x, h (hsOrthComp N x, inner ℝ x (hsUnitVector N)) := lintegral_congr hpt
    _ = ∫⁻ p, h p ∂(volume.prod volume) :=
        (measurePreserving_orthSplit (hsUnitVector_norm N)).lintegral_comp hh
    _ = ∫⁻ z, ∫⁻ t, h (z, t) := lintegral_prod _ hh.aemeasurable
    _ = ∫⁻ z, (hsRadialDomain N).indicator (fun z => F₁ z * ∫⁻ w, G₁ w) z :=
        lintegral_congr hfiber
    _ = (∫⁻ z in hsRadialDomain N, F₁ z) * ∫⁻ w, G₁ w := by
        rw [lintegral_indicator hB, lintegral_mul_const _ hF]

/-- The fiber identity on the fundamental region carrying the Gibbs probability: for measurable
`F₁` on `e^⊥` and `G₁` on the circle, the integral of `F₁(z) G₁(ω)` over `Configuration N` is
`(∫_{B_N} F₁) (∫_{circle} G₁)`, with `B_N` the radial domain. -/
theorem lintegral_configuration_fiber (N : ℕ+) {F₁ : hsOrthSubspace N → ℝ≥0∞}
    (hF : Measurable F₁) {G₁ : AddCircle (Real.sqrt (N : ℕ)) → ℝ≥0∞} (hG : Measurable G₁) :
    ∫⁻ X : Configuration N, F₁ (hsConfigCoord N X).1 * G₁ (hsConfigCoord N X).2
        ∂configurationVolume N =
      (∫⁻ z in hsRadialDomain N, F₁ z) * ∫⁻ w, G₁ w := by
  have hmeas : Measurable fun y : Fin (N : ℕ) → ℝ =>
      F₁ (hsOrthComp N (WithLp.toLp 2 y)) * G₁ (hsAngle N (WithLp.toLp 2 y)) :=
    (hF.comp ((measurable_hsOrthComp N).comp
      (PiLp.volume_preserving_toLp (Fin (N : ℕ))).measurable)).mul
      (hG.comp ((measurable_hsAngle N).comp (PiLp.volume_preserving_toLp (Fin (N : ℕ))).measurable))
  have key := hsFundamentalRegion_lintegral N _ hmeas
  simp only [WithLp.toLp_ofLp] at key
  rw [← lintegral_hsFundamentalRegion_fiber N hF hG]
  exact key.symm

end Riesz1

end
