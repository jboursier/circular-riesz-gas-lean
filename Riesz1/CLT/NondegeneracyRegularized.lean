/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.CLT.NondegeneracyScale
public import Riesz1.CLT.NondegeneracyMacroscopic
public import Riesz1.CLT.NondegeneracyStatistic
public import Riesz1.ToMathlib.CircleSobolevTwoTerm
import all Riesz1.ToMathlib.Mollifier.RegularizationSobolev

/-!
# Uniform nondegeneracy after compact-profile regularization

The remaining positive compact alternative of the nondegeneracy argument for Theorem 3, using
the regularized lift. Together with the publicly imported macroscopic and zero-variance results,
`clt_nondegeneracy_compact` completes every assertion of the nondegeneracy argument.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff

namespace Riesz1
namespace Internal

lemma nondegeneracy_variance_two_term (P : Parameters) (a : Scale)
    (f g : {f : UnitAddCircle → ℂ // MemLp f 2 volume}) :
    cltVariance P a f ≤ 2 * (cltVariance P a g + cltVariance P a (subL2 f g)) := by
  have hh := mul_le_mul (show ENNReal.ofReal ((2 * Real.pi) ^ (1 - P.val.2) /
      (2 * P.val.1 * rieszConstant (parametersExponent P)) * a.val ^ (-P.val.2)) ≤
      ENNReal.ofReal ((2 * Real.pi) ^ (1 - P.val.2) /
      (2 * P.val.1 * rieszConstant (parametersExponent P)) * a.val ^ (-P.val.2)) from le_rfl)
    (circleSobolevSq_le_two_mul_add ((1 - P.val.2) / 2) f g) zero_le zero_le
  change cltVariance P a f ≤ _ at hh
  exact hh.trans_eq (by unfold cltVariance; ring)

lemma nondegeneracy_variance_scaled_unit (P : Parameters) (a : Scale) (e : Profile) :
    cltVariance P a ⟨(fun x => (e.val x : ℂ)), e.property⟩ =
      ENNReal.ofReal (a.val ^ (-P.val.2)) * circleVariance P e ⟨1, by norm_num⟩ := by
  simp only [cltVariance, circleVariance, testAtScale, ite_true, Real.one_rpow, mul_one]
  rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg a.property.1.le _)]
  congr 2
  ring

lemma nondegeneracy_regularized_eq (p g : Profile) (a : Scale)
    {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) {h : ℝ} (hh : 0 < h)
    (hg : ∀ x : ℝ, g.val (x : UnitAddCircle) =
      circleMollify ρ (observationLength a).val h
        (fun t : ℝ => periodizedProfile p (observationLength a)
          (t : Circle (observationLength a))) ((observationLength a).val * x)) :
    g.val = cltScaledLift hρ a hh
      ⟨periodizedProfile p (observationLength a), periodizedProfileL2 p a⟩ := by
  funext y
  induction y using QuotientAddGroup.induction_on with
  | H x =>
    rw [hg]
    simp only [cltScaledLift, Function.Periodic.lift_coe, cltScaledFun, cltRegCircle_coe]
    congr 1
    change a.val⁻¹ * x = x / a.val
    exact (div_eq_inv_mul x a.val).symm

lemma nondegeneracy_compact_unit_variance (P : Parameters) (p : Profile) (a : Scale)
    (ha : a.val = 1)
    {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) {h : ℝ} (hh : 0 < h) :
    cltVariance P a
      ⟨(fun x => (cltScaledLift hρ a hh
        ⟨periodizedProfile p (observationLength a), periodizedProfileL2 p a⟩ x : ℂ)),
        cltScaledLift_memLp hρ a hh _⟩ =
      cltVariance P a
        ⟨(fun x => (cltRegCircle hρ unitLength hh ⟨p.val, p.property⟩ x : ℂ)),
          nondegeneracy_regCircle_memLp hρ unitLength hh ⟨p.val, p.property⟩⟩ := by
  unfold cltVariance circleSobolevSq
  congr 1
  apply tsum_congr
  intro k
  rw [nondegeneracy_compact_lift_coeff, nondegeneracy_unit_lift_coeff]
  simp only [testAtScale, ha, ite_true, observationLength, inv_one, div_one]

lemma nondegeneracy_compact_family_of_admissible (P : Parameters) (p : Profile)
    (ell : Scales) (α : ℝ) (d : TestData) (h : Admissible P p ell α d)
    (hell : Tendsto (fun k : ℕ => (ell ⟨k + 1, Nat.succ_pos k⟩).val) atTop (𝓝 0)) :
    ∀ N, PrimitiveRegularity (observationLength (ell N)) d.1 P.val.2 d.2.1
        ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ ∧
      TransportRegularity P (observationLength (ell N))
        ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩
          d.2.2.2.1 d.2.2.2.2 α d.2.2.1 := by
  rcases h.2.2.2.2.2.2 with hm | hc
  · have hlim : Tendsto (fun k : ℕ => (ell ⟨k + 1, Nat.succ_pos k⟩).val) atTop (𝓝 1) := by
      convert (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)) using 1
      funext k
      exact hm.1 _
    have he := tendsto_nhds_unique hell hlim
    norm_num at he
  · exact hc.2.2

/-- A small variance of the actual difference preserves a quantitative lower
bound. All finiteness certificates precede conversion to real numbers. -/
lemma nondegeneracy_lower_of_error (P : Parameters) (p g e : Profile) (a : Scale)
    (he : ∀ x, e.val x = testAtScale p a x - g.val x)
    (_hf : circleVariance P p a < ⊤)
    (hg : cltVariance P a ⟨(fun x => (g.val x : ℂ)), g.property⟩ < ⊤)
    (hee : cltVariance P a ⟨(fun x => (e.val x : ℂ)), e.property⟩ < ⊤)
    {c : ℝ} (hc : 0 < c)
    (hlow : c ≤ Real.sqrt (circleVariance P p a).toReal)
    (herr : Real.sqrt (cltVariance P a ⟨(fun x => (e.val x : ℂ)), e.property⟩).toReal ≤ c / 2) :
    c / 2 ≤ Real.sqrt (cltVariance P a ⟨(fun x => (g.val x : ℂ)), g.property⟩).toReal := by
  let f := (⟨(fun x => (testAtScale p a x : ℂ)), testAtScaleL2 p a⟩ :
    {f : UnitAddCircle → ℂ // MemLp f 2 volume})
  let g' := (⟨(fun x => (g.val x : ℂ)), g.property⟩ :
    {f : UnitAddCircle → ℂ // MemLp f 2 volume})
  have heq : subL2 f g' = ⟨(fun x => (e.val x : ℂ)), e.property⟩ := by
    apply Subtype.ext
    funext x
    simp only [subL2, f, g', he, Complex.ofReal_sub]
  have htwo := nondegeneracy_variance_two_term P a f g'
  rw [heq, ← circleVariance_eq_cltVariance] at htwo
  have hright : 2 * (cltVariance P a g' +
      cltVariance P a ⟨(fun x => (e.val x : ℂ)), e.property⟩) ≠ ⊤ :=
    (ENNReal.mul_lt_top (by norm_num) (ENNReal.add_lt_top.mpr ⟨hg, hee⟩)).ne
  have ht := ENNReal.toReal_mono hright htwo
  rw [ENNReal.toReal_mul, ENNReal.toReal_add hg.ne hee.ne] at ht
  norm_num only [ENNReal.toReal_ofNat] at ht
  have hc2 : c ^ 2 ≤ (circleVariance P p a).toReal := by
    nlinarith [Real.sq_sqrt (ENNReal.toReal_nonneg (a := circleVariance P p a))]
  have he2 : (cltVariance P a ⟨(fun x => (e.val x : ℂ)), e.property⟩).toReal ≤ (c / 2) ^ 2 := by
    nlinarith [Real.sq_sqrt (ENNReal.toReal_nonneg
      (a := cltVariance P a ⟨(fun x => (e.val x : ℂ)), e.property⟩)),
      Real.sqrt_nonneg (cltVariance P a ⟨(fun x => (e.val x : ℂ)), e.property⟩).toReal]
  apply (Real.le_sqrt (half_pos hc).le (ENNReal.toReal_nonneg)).mpr
  nlinarith

end Internal

/-- The positive compact alternative of the nondegeneracy argument for Theorem 3,
for shrinking admissible scales. The constants precede the scale sequence and
particle number and depend only on the fixed profile data and mollifier. -/
theorem clt_nondegeneracy_compact_shrinking (P : Parameters) (p : Profile)
    (hp : CompactProfile p) (α : ℝ) (d : TestData)
    (hz : ¬ zeroExtension p =ᵐ[volume] fun _ => 0)
    (ρ : ℝ → ℝ) (hρ : IsMollifier ρ) :
    ∃ c C K₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < K₀ ∧
      ∀ ell : Scales, Admissible P p ell α d →
        Tendsto (fun k : ℕ => (ell ⟨k + 1, Nat.succ_pos k⟩).val) atTop (𝓝 0) →
        ∀ N : ℕ+, K₀ ≤ (N : ℝ) * (ell N).val →
          let hh := cltDelta_pos P N (ell N)
          let V := cltVariance P (ell N)
            ⟨(fun x => (cltScaledLift hρ (ell N) hh
              ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ x : ℂ)),
              cltScaledLift_memLp hρ (ell N) hh _⟩
          V < ⊤ ∧ c ≤ Real.sqrt V.toReal ∧ Real.sqrt V.toReal ≤ C := by
  classical
  by_cases hex : ∃ ell : Scales, Admissible P p ell α d ∧
      Tendsto (fun k : ℕ => (ell ⟨k + 1, Nat.succ_pos k⟩).val) atTop (𝓝 0)
  · obtain ⟨ell₀, hadm₀, _⟩ := hex
    obtain ⟨c₀, hc₀, hlow⟩ := clt_nondegeneracy_compact_unsmoothed P p hp α d hz
    obtain ⟨C, hC, hupp⟩ := clt_nondegeneracy_compact_upper P p hp α d ρ hρ
    let ε := (P.val.2 / 2 - α) / 2
    have hε : 0 < ε := by dsimp [ε]; linarith [hadm₀.2.1]
    obtain ⟨D, hD, herr⟩ := regUniform_variance_compact P p hp d.1 d.2.1
      d.2.2.2.1 d.2.2.2.2 α d.2.2.1 ε hadm₀.2.2.1 hadm₀.2.2.2.2.1.le
      hadm₀.2.2.2.2.2.1.le hadm₀.1 hadm₀.2.1 hε ρ hρ
    have hd : 0 < (2 - P.val.2) / (4 + P.val.2) :=
      div_pos (by linarith [P.property.2.2]) (by linarith [P.property.2.1])
    have hδlim := tendsto_rpow_neg_atTop hd
    have helim : Tendsto (fun K : ℝ => D * (K ^ (-((2 - P.val.2) / (4 + P.val.2)))) ^ ε)
        atTop (𝓝 0) := by
      simpa only [Real.zero_rpow hε.ne', mul_zero] using
        (hδlim.rpow_const (Or.inr hε.le)).const_mul D
    obtain ⟨T, hT⟩ := eventually_atTop.mp (helim.eventually (gt_mem_nhds (half_pos hc₀)))
    refine ⟨c₀ / 2, C, max T 1, half_pos hc₀, hC,
      lt_of_lt_of_le one_pos (le_max_right _ _), fun ell hadm hell N hN => ?_⟩
    let a := ell N
    let h := cltDelta P N a
    have hh : 0 < h := cltDelta_pos P N a
    have hh1 : h ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos
      ((le_max_right T 1).trans hN) (neg_nonpos.mpr hd.le)
    obtain ⟨g, e, _, _, hphysical, he, hefin, heb⟩ := herr ell hell
      (Internal.nondegeneracy_compact_family_of_admissible P p ell α d hadm hell) a h hh hh1
    have heq := Internal.nondegeneracy_regularized_eq p g a hρ hh hphysical
    have hupper := hupp ell hadm a h hh
    have hgfin : cltVariance P a ⟨(fun x => (g.val x : ℂ)), g.property⟩ < ⊤ := by
      simpa only [heq] using hupper.1
    have hefin' : cltVariance P a ⟨(fun x => (e.val x : ℂ)), e.property⟩ < ⊤ := by
      rwa [Internal.nondegeneracy_variance_scaled_unit]
    have herror : Real.sqrt (cltVariance P a ⟨(fun x => (e.val x : ℂ)), e.property⟩).toReal ≤ c₀ / 2 := by
      rw [Internal.nondegeneracy_variance_scaled_unit]
      apply heb.trans
      have heps : P.val.2 / 2 - α - ε = ε := by dsimp [ε]; ring
      rw [heps]
      exact (hT _ ((le_max_left _ _).trans hN)).le
    have hlower := Internal.nondegeneracy_lower_of_error P p g e a he
      (hlow ell hadm a).1 hgfin hefin' hc₀ (hlow ell hadm a).2 herror
    exact ⟨hupper.1, by simpa only [heq] using hlower, hupper.2⟩
  · exact ⟨1, 1, 1, one_pos, one_pos, one_pos,
      fun ell hadm hell => (hex ⟨ell, hadm, hell⟩).elim⟩

/-- The full positive compact-profile assertion of the nondegeneracy argument for Theorem 3.
The bound is uniform before every admissible scale sequence, including
the macroscopic sequence when the compact profile also satisfies its data. -/
theorem clt_nondegeneracy_compact (P : Parameters) (p : Profile)
    (hp : CompactProfile p) (α : ℝ) (d : TestData)
    (hz : ¬ zeroExtension p =ᵐ[volume] fun _ => 0)
    (ρ : ℝ → ℝ) (hρ : IsMollifier ρ) :
    ∃ c C K₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < K₀ ∧
      ∀ ell : Scales, Admissible P p ell α d →
        ∀ N : ℕ+, K₀ ≤ (N : ℝ) * (ell N).val →
          let hh := cltDelta_pos P N (ell N)
          let V := cltVariance P (ell N)
            ⟨(fun x => (cltScaledLift hρ (ell N) hh
              ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ x : ℂ)),
              cltScaledLift_memLp hρ (ell N) hh _⟩
          V < ⊤ ∧ c ≤ Real.sqrt V.toReal ∧ Real.sqrt V.toReal ≤ C := by
  classical
  obtain ⟨cs, Cs, Ks, hcs, hCs, hKs, hs⟩ :=
    clt_nondegeneracy_compact_shrinking P p hp α d hz ρ hρ
  by_cases hex : ∃ ell : Scales, Admissible P p ell α d
  · obtain ⟨ell₀, h₀⟩ := hex
    by_cases hm : PrimitiveRegularity unitLength d.1 P.val.2 d.2.1 ⟨p.val, p.property⟩ ∧
        TransportRegularity P unitLength ⟨p.val, p.property⟩ d.2.2.2.1 d.2.2.2.2 α d.2.2.1
    · have hpnc : ¬ ∃ c : ℝ, p.val =ᵐ[volume] fun _ => c := by
        rintro ⟨c, hc⟩
        apply hz
        apply Internal.nondegeneracy_const_scaled_zero p hp ⟨1, by norm_num⟩
        simpa only [testAtScale, ite_true] using hc
      obtain ⟨cm, Cm, Km, hcm, hCm, hKm, hmacro⟩ := clt_nondegeneracy_macroscopic
        P p d.1 d.2.1 d.2.2.2.1 d.2.2.2.2 α d.2.2.1 h₀.2.2.1
        h₀.2.2.2.2.1.le h₀.2.2.2.2.2.1.le h₀.1 h₀.2.1 hm.1 hm.2 hpnc ρ hρ
      refine ⟨min cs cm, max Cs Cm, max Ks Km, lt_min hcs hcm,
        hCs.trans_le (le_max_left _ _), hKs.trans_le (le_max_left _ _), fun ell hadm N hN => ?_⟩
      rcases hadm.2.2.2.2.2.2 with hmac | hcomp
      · have ha : ell N = ⟨1, by norm_num⟩ := Subtype.ext (hmac.1 N)
        rw [ha] at hN ⊢
        rw [mul_one] at hN
        have hb := hmacro N ((le_max_right _ _).trans hN)
        dsimp only
        rw [Internal.nondegeneracy_compact_unit_variance P p _ rfl]
        exact ⟨hb.1, (min_le_right _ _).trans hb.2.1, hb.2.2.trans (le_max_right _ _)⟩
      · obtain ⟨hf, hl, hu⟩ := hs ell hadm hcomp.2.1 N ((le_max_left _ _).trans hN)
        exact ⟨hf, (min_le_left _ _).trans hl, hu.trans (le_max_left _ _)⟩
    · refine ⟨cs, Cs, Ks, hcs, hCs, hKs, fun ell hadm N hN => ?_⟩
      rcases hadm.2.2.2.2.2.2 with hmac | hcomp
      · exact (hm hmac.2).elim
      · exact hs ell hadm hcomp.2.1 N hN
  · exact ⟨1, 1, 1, one_pos, one_pos, one_pos, fun ell hadm => (hex ⟨ell, hadm⟩).elim⟩

end Riesz1
