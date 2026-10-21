/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.CLT.NondegeneracyRegularized
public import Riesz1.Variance.RegUniformComplete
import all Riesz1.ToMathlib.Mollifier.RegularizationSobolev
import all Riesz1.Variance.LoopMaster

/-!
# Analytic part of the CLT smoothing error

The first assertion of the smoothing step in the proof of Theorem 3, generalized to
every radius in `(0,1]`. All constants precede the scale sequence.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal Topology ContDiff

namespace Riesz1
namespace Internal

lemma smoothing_macro_regularized_eq (p g : Profile)
    {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) {h : ℝ} (hh : 0 < h)
    (hg : ∀ x : ℝ, g.val (x : UnitAddCircle) =
      circleMollify ρ 1 h (fun y : ℝ => p.val (y : UnitAddCircle)) x) :
    g.val = cltScaledLift hρ (⟨1, by norm_num⟩ : Ioc (0 : ℝ) 1) hh
      ⟨periodizedProfile p (observationLength (⟨1, by norm_num⟩ : Ioc (0 : ℝ) 1)),
        periodizedProfileL2 p (⟨1, by norm_num⟩ : Ioc (0 : ℝ) 1)⟩ := by
  have hunit : g.val = cltRegCircle hρ unitLength hh ⟨p.val, p.property⟩ := by
    funext y
    induction y using QuotientAddGroup.induction_on with
    | H x => rw [hg, nondegeneracy_unit_lift_coe]
  have hc : Continuous g.val := by
    rw [hunit]
    exact (QuotientAddGroup.isQuotientMap_mk
      (AddSubgroup.zmultiples (1 : ℝ))).continuous_iff.mpr
        (cltRegCircle_contDiff hρ unitLength hh ⟨p.val, p.property⟩).continuous
  have hlen : (observationLength ((⟨1, by norm_num⟩ : Ioc (0 : ℝ) 1) : Scale)).val = 1 := inv_one
  have hcoeff (k : ℤ) : fourierCoeff (fun x => (g.val x : ℂ)) k =
      fourierCoeff (fun x => (testAtScale p (⟨1, by norm_num⟩ : Ioc (0 : ℝ) 1) x : ℂ)) k *
        (mollifierFT ρ ((h / (observationLength ((⟨1, by norm_num⟩ : Ioc (0 : ℝ) 1) : Scale)).val) * k) : ℂ) := by
    rw [hunit, nondegeneracy_unit_lift_coeff]
    simp only [testAtScale, ite_true, hlen, div_one]
  have hphysical := smoothed_profile_pullback hρ p (⟨1, by norm_num⟩ : Ioc (0 : ℝ) 1) hh g hc hcoeff
  exact nondegeneracy_regularized_eq p g (⟨1, by norm_num⟩ : Ioc (0 : ℝ) 1) hρ hh hphysical


lemma smoothing_variance_macro (P : Parameters) (p : Profile) (α : ℝ) (d : TestData)
    (hα0 : P.val.2 - 1 ≤ α) (hα1 : α < P.val.2 / 2)
    (hη : 0 < d.1) (hB : 0 ≤ d.2.1) (hC : 0 ≤ d.2.2.1)
    (hprim : PrimitiveRegularity unitLength d.1 P.val.2 d.2.1 ⟨p.val, p.property⟩)
    (hreg : TransportRegularity P unitLength ⟨p.val, p.property⟩
      d.2.2.2.1 d.2.2.2.2 α d.2.2.1)
    (ρ : ℝ → ℝ) (hρ : IsMollifier ρ) (τ : ℝ) (hτ : 0 < τ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : Scale), a.val = 1 → ∀ (h : ℝ) (hh : 0 < h), h ≤ 1 →
      let f := (⟨(fun x => (testAtScale p a x : ℂ)), testAtScaleL2 p a⟩ :
        {f : UnitAddCircle → ℂ // MemLp f 2 volume})
      let g := (⟨(fun x => (cltScaledLift hρ a hh
        ⟨periodizedProfile p (observationLength a), periodizedProfileL2 p a⟩ x : ℂ)),
        cltScaledLift_memLp hρ a hh _⟩ : {f : UnitAddCircle → ℂ // MemLp f 2 volume})
      let V := cltVariance P a (subL2 f g)
      V < ⊤ ∧ Real.sqrt V.toReal ≤ C * h ^ (P.val.2 / 2 - α - τ) := by
  obtain ⟨C, hCpos, hb⟩ := regUniform_variance_macroscopic P p d.1 d.2.1
    d.2.2.2.1 d.2.2.2.2 α d.2.2.1 τ hη hB hC hα0 hα1 hτ hprim hreg ρ hρ
  refine ⟨C, hCpos, fun a ha h hh hh1 => ?_⟩
  change Ioc (0 : ℝ) 1 at a
  have hae : a = (⟨1, by norm_num⟩ : Ioc (0 : ℝ) 1) := Subtype.ext ha
  subst a
  obtain ⟨q, e, _, hq, he, hfin, hbound⟩ := hb h hh hh1
  have hqeq := smoothing_macro_regularized_eq p q hρ hh hq
  have heq : subL2
      ⟨(fun x => (testAtScale p (⟨1, by norm_num⟩ : Ioc (0 : ℝ) 1) x : ℂ)), testAtScaleL2 p (⟨1, by norm_num⟩ : Ioc (0 : ℝ) 1)⟩
      ⟨(fun x => (cltScaledLift hρ (⟨1, by norm_num⟩ : Ioc (0 : ℝ) 1) hh
        ⟨periodizedProfile p (observationLength (⟨1, by norm_num⟩ : Ioc (0 : ℝ) 1)), periodizedProfileL2 p (⟨1, by norm_num⟩ : Ioc (0 : ℝ) 1)⟩ x : ℂ)),
        cltScaledLift_memLp hρ (⟨1, by norm_num⟩ : Ioc (0 : ℝ) 1) hh
          ⟨periodizedProfile p (observationLength (⟨1, by norm_num⟩ : Ioc (0 : ℝ) 1)), periodizedProfileL2 p (⟨1, by norm_num⟩ : Ioc (0 : ℝ) 1)⟩⟩ =
      ⟨(fun x => (e.val x : ℂ)), e.property⟩ := by
    apply Subtype.ext
    funext x
    simp only [subL2, testAtScale, ite_true, he, Complex.ofReal_sub, hqeq]
  dsimp only
  rw [heq]
  have hv : cltVariance P (⟨1, by norm_num⟩ : Ioc (0 : ℝ) 1) ⟨(fun x => (e.val x : ℂ)), e.property⟩ =
      circleVariance P e (⟨1, by norm_num⟩ : Ioc (0 : ℝ) 1) := by
    simp only [cltVariance, circleVariance, testAtScale, ite_true]
  rw [hv]
  exact ⟨hfin, hbound⟩

end Internal

/-- The analytic smoothing bound in the smoothing step of the proof of Theorem 3. This stronger
form holds for every radius at most one. The variance is finite before its
real square root is used, including for profiles with zero variance. -/
theorem clt_smoothing_variance (P : Parameters) (p : Profile) (α : ℝ) (d : TestData)
    (ρ : ℝ → ℝ) (hρ : IsMollifier ρ) (τ : ℝ) (hτ : 0 < τ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ell : Scales, Admissible P p ell α d →
      ∀ (N : ℕ+) (h : ℝ) (hh : 0 < h), h ≤ 1 →
        let f := (⟨(fun x => (testAtScale p (ell N) x : ℂ)), testAtScaleL2 p (ell N)⟩ :
          {f : UnitAddCircle → ℂ // MemLp f 2 volume})
        let g := (⟨(fun x => (cltScaledLift hρ (ell N) hh
          ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ x : ℂ)),
          cltScaledLift_memLp hρ (ell N) hh _⟩ : {f : UnitAddCircle → ℂ // MemLp f 2 volume})
        let V := cltVariance P (ell N) (subL2 f g)
        V < ⊤ ∧ Real.sqrt V.toReal ≤ C * h ^ (P.val.2 / 2 - α - τ) := by
  classical
  by_cases hex : ∃ ell : Scales, Admissible P p ell α d
  · obtain ⟨ell₀, h₀⟩ := hex
    have hm : ∃ C : ℝ, 0 < C ∧ ∀ ell : Scales, Admissible P p ell α d →
        (∀ M, (ell M).val = 1) → ∀ (N : ℕ+) (h : ℝ) (hh : 0 < h), h ≤ 1 →
        let f := (⟨(fun x => (testAtScale p (ell N) x : ℂ)), testAtScaleL2 p (ell N)⟩ :
          {f : UnitAddCircle → ℂ // MemLp f 2 volume})
        let g := (⟨(fun x => (cltScaledLift hρ (ell N) hh
          ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ x : ℂ)),
          cltScaledLift_memLp hρ (ell N) hh _⟩ : {f : UnitAddCircle → ℂ // MemLp f 2 volume})
        let V := cltVariance P (ell N) (subL2 f g)
        V < ⊤ ∧ Real.sqrt V.toReal ≤ C * h ^ (P.val.2 / 2 - α - τ) := by
      by_cases hmac : PrimitiveRegularity unitLength d.1 P.val.2 d.2.1 ⟨p.val, p.property⟩ ∧
          TransportRegularity P unitLength ⟨p.val, p.property⟩ d.2.2.2.1 d.2.2.2.2 α d.2.2.1
      · obtain ⟨C, hC, hb⟩ := Internal.smoothing_variance_macro P p α d h₀.1 h₀.2.1
          h₀.2.2.1 h₀.2.2.2.2.1.le h₀.2.2.2.2.2.1.le hmac.1 hmac.2 ρ hρ τ hτ
        exact ⟨C, hC, fun ell _ hmacro N h hh hh1 => hb (ell N) (hmacro N) h hh hh1⟩
      · refine ⟨1, one_pos, fun ell hadm hmacro => ?_⟩
        rcases hadm.2.2.2.2.2.2 with hmacro' | hcompact
        · exact (hmac hmacro'.2).elim
        · have he : Tendsto (fun k : ℕ => (ell ⟨k + 1, Nat.succ_pos k⟩).val) atTop (𝓝 1) := by
            convert (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)) using 1
            funext k
            exact hmacro _
          have hf := tendsto_nhds_unique hcompact.2.1 he
          norm_num at hf
    obtain ⟨Cm, hCm, hm⟩ := hm
    by_cases hp : CompactProfile p
    · obtain ⟨Cc, hCc, hc⟩ := regUniform_variance_compact P p hp d.1 d.2.1
        d.2.2.2.1 d.2.2.2.2 α d.2.2.1 τ h₀.2.2.1 h₀.2.2.2.2.1.le
        h₀.2.2.2.2.2.1.le h₀.1 h₀.2.1 hτ ρ hρ
      refine ⟨max Cm Cc, hCm.trans_le (le_max_left _ _), fun ell hadm N h hh hh1 => ?_⟩
      rcases hadm.2.2.2.2.2.2 with hmacro | hcompact
      · obtain ⟨hf, hb⟩ := hm ell hadm hmacro.1 N h hh hh1
        exact ⟨hf, hb.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))⟩
      · obtain ⟨q, e, _, _, hq, he, hf, hb⟩ := hc ell hcompact.2.1 hcompact.2.2
          (ell N) h hh hh1
        have hqeq := Internal.nondegeneracy_regularized_eq p q (ell N) hρ hh hq
        have heq : subL2
            ⟨(fun x => (testAtScale p (ell N) x : ℂ)), testAtScaleL2 p (ell N)⟩
            ⟨(fun x => (cltScaledLift hρ (ell N) hh
              ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ x : ℂ)),
              cltScaledLift_memLp hρ (ell N) hh _⟩ =
            ⟨(fun x => (e.val x : ℂ)), e.property⟩ := by
          apply Subtype.ext
          funext x
          simp only [subL2, he, Complex.ofReal_sub, hqeq]
        dsimp only
        rw [heq, Internal.nondegeneracy_variance_scaled_unit]
        exact ⟨hf, hb.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))⟩
    · refine ⟨Cm, hCm, fun ell hadm N h hh hh1 => ?_⟩
      rcases hadm.2.2.2.2.2.2 with hmacro | hcompact
      · exact hm ell hadm hmacro.1 N h hh hh1
      · exact (hp hcompact.1).elim
  · exact ⟨1, one_pos, fun ell hadm => (hex ⟨ell, hadm⟩).elim⟩

/-- The CLT radius lies in the analytic smoothing range as soon as `K ≥ 1`. -/
theorem cltDelta_le_one (P : Parameters) (N : ℕ+) (a : Scale)
    (hK : 1 ≤ (N : ℝ) * a.val) : cltDelta P N a ≤ 1 := by
  unfold cltDelta
  apply Real.rpow_le_one_of_one_le_of_nonpos hK
  have hs := P.property.2.2
  have hs0 := P.property.2.1
  have hd : 0 ≤ (2 - P.val.2) / (4 + P.val.2) :=
    div_nonneg (by linarith) (by linarith)
  exact neg_nonpos.mpr hd

/-- Equation (6.1) of the paper, on the CLT radius. One may take `K₀ = 1`.
The range of `τ` in the paper is contained in the stronger range `τ > 0` used here. -/
theorem clt_smoothing_sobolev (P : Parameters) (p : Profile) (α : ℝ) (d : TestData)
    (ρ : ℝ → ℝ) (hρ : IsMollifier ρ) (τ : ℝ) (hτ : 0 < τ) :
    ∃ C K₀ : ℝ, 0 < C ∧ 0 < K₀ ∧
      ∀ ell : Scales, Admissible P p ell α d →
      ∀ N : ℕ+, K₀ ≤ (N : ℝ) * (ell N).val →
        let hh := cltDelta_pos P N (ell N)
        let f := (⟨(fun x => (testAtScale p (ell N) x : ℂ)), testAtScaleL2 p (ell N)⟩ :
          {f : UnitAddCircle → ℂ // MemLp f 2 volume})
        let g := (⟨(fun x => (cltScaledLift hρ (ell N) hh
          ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ x : ℂ)),
          cltScaledLift_memLp hρ (ell N) hh _⟩ : {f : UnitAddCircle → ℂ // MemLp f 2 volume})
        let V := cltVariance P (ell N) (subL2 f g)
        V < ⊤ ∧ Real.sqrt V.toReal ≤
          C * (cltDelta P N (ell N)) ^ (P.val.2 / 2 - α - τ) := by
  obtain ⟨C, hC, hb⟩ := clt_smoothing_variance P p α d ρ hρ τ hτ
  exact ⟨C, 1, hC, one_pos, fun ell hadm N hN =>
    hb ell hadm N _ (cltDelta_pos P N (ell N)) (cltDelta_le_one P N (ell N) hN)⟩

end Riesz1
