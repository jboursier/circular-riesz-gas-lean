/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.CLT.SmoothingVariance
public import Riesz1.CLT.SmoothingBounds
import all Riesz1.ToMathlib.Mollifier.RegularizationSobolev
import all Riesz1.Variance.LoopMaster

/-!
# Smoothing error of the CLT

The random second-norm assertion of the smoothing step in the proof of Theorem 3,
conditional only on the conclusion of uniform quantitative variance.
The analytic and Lipschitz assertions are theorems in the
publicly imported modules and require no such hypothesis.
-/

public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace Riesz1.Internal

lemma smoothing_support_threshold (P : Parameters) (p : Profile) :
    ∃ r T : ℝ, 0 < r ∧ r < 1 / 2 ∧ 0 < T ∧
      ∀ (α : ℝ) (d : TestData) (ell : Scales), Admissible P p ell α d →
      ∀ N : ℕ+, T ≤ (N : ℝ) * (ell N).val →
        ((∀ M, (ell M).val = 1) ∨
          ((∀ᵐ x : ℝ, r ≤ |x| → zeroExtension p x = 0) ∧
            cltDelta P N (ell N) < 1 / 2 - r)) := by
  classical
  by_cases hp : CompactProfile p
  · obtain ⟨r, hr, hrhalf, hsupp⟩ := hp
    have hd : 0 < (2 - P.val.2) / (4 + P.val.2) :=
      div_pos (by linarith [P.property.2.2]) (by linarith [P.property.2.1])
    obtain ⟨T, hT⟩ := eventually_atTop.mp
      ((tendsto_rpow_neg_atTop hd).eventually (gt_mem_nhds (by linarith : 0 < 1 / 2 - r)))
    refine ⟨r, max T 1, hr, hrhalf, one_pos.trans_le (le_max_right _ _),
      fun α d ell _ N hN => Or.inr ⟨hsupp, ?_⟩⟩
    exact hT _ ((le_max_left _ _).trans hN)
  · refine ⟨1 / 4, 1, by norm_num, by norm_num, one_pos, fun α d ell hadm N _ => ?_⟩
    rcases hadm.2.2.2.2.2.2 with hmacro | hcompact
    · exact Or.inl hmacro.1
    · exact (hp hcompact.1).elim

/-- The random smoothing bound, equation (6.2) of the paper.
The constant and threshold precede every scale sequence and particle number.
The only conditional input is the uniform variance conclusion. This form is
slightly stronger: it holds for every `τ > 0`, so in particular for the
range `0 < τ < s/2 - α` of the paper. -/
theorem clt_smoothing_of_variance_uniform
    (hvar : QuantitativeVarianceUniformConclusion)
    (P : Parameters) (p : Profile) (α : ℝ) (d : TestData)
    (ρ : ℝ → ℝ) (hρ : IsMollifier ρ) (τ : ℝ) (hτ : 0 < τ) :
    ∃ C K₀ : ℝ, 0 < C ∧ 0 < K₀ ∧
      ∀ ell : Scales, Admissible P p ell α d →
      ∀ N : ℕ+, K₀ ≤ (N : ℝ) * (ell N).val →
        let G := cltStat P N (ell N)
          (cltScaledFun hρ (ell N) (cltDelta_pos P N (ell N))
            ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩)
        MemLp (fun X => normalizedStatistic P p ell N X - G X) 2 (gibbsMeasure P N) ∧
          (eLpNorm (fun X => normalizedStatistic P p ell N X - G X) 2 (gibbsMeasure P N)).toReal ≤
            C * ((cltDelta P N (ell N)) ^ (P.val.2 / 2 - α - τ) +
              ((N : ℝ) * (ell N).val) ^ (max ((P.val.2 - 1) / 2) (α - P.val.2 / 2) + τ)) := by
  obtain ⟨A, hA, hana⟩ := clt_smoothing_variance P p α d ρ hρ τ hτ
  obtain ⟨r, T, hr, hrhalf, hT, hmargin⟩ := smoothing_support_threshold P p
  obtain ⟨B, hB, hvariance⟩ := hvar P p α d ρ hρ r hr hrhalf (2 * τ) (by positivity)
  refine ⟨A + Real.sqrt B, max T 1, by positivity,
    one_pos.trans_le (le_max_right _ _), fun ell hadm N hN => ?_⟩
  let K := (N : ℝ) * (ell N).val
  have hK1 : 1 ≤ K := (le_max_right T 1).trans hN
  have hK : 0 < K := one_pos.trans_le hK1
  let h := cltDelta P N (ell N)
  have hh : 0 < h := cltDelta_pos P N (ell N)
  have hh1 : h ≤ 1 := cltDelta_le_one P N (ell N) hK1
  let g : Profile := ⟨cltScaledLift hρ (ell N) hh
    ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩,
      cltScaledLift_memLp hρ (ell N) hh _⟩
  let e : Profile := ⟨(fun x => testAtScale p (ell N) x - g.val x), by
    refine ((testAtScaleL2 p (ell N)).sub g.property).ae_eq
      (Filter.Eventually.of_forall fun x => ?_)
    change (testAtScale p (ell N) x : ℂ) - (g.val x : ℂ) =
      ((testAtScale p (ell N) x - g.val x : ℝ) : ℂ)
    rw [Complex.ofReal_sub]⟩
  have hν := hvariance ell hadm h hh hh1
    (hmargin α d ell hadm N ((le_max_left T 1).trans hN)) N hK1 e (Or.inr fun _ => rfl)
  dsimp only at hν
  have he := smoothing_real_memLp e
  have hH := memLp_fluctuation P N he
  have : IsProbabilityMeasure (gibbsMeasure P N) := (modelWellDefined P N).2.2
  let H : Configuration N → ℝ := fun X => fluctuation ⟨e.val, he.integrable one_le_two⟩ X
  let σ := cltVariance P (ell N) ⟨(fun x => (e.val x : ℂ)), e.property⟩
  have hsecond := smoothing_scaled_second_moment (gibbsMeasure P N) hH
    (integral_fluctuation_eq_zero P N he) hK hν.2.2
  have hFG : (fun X => normalizedStatistic P p ell N X -
      cltStat P N (ell N) (cltScaledFun hρ (ell N) hh
        ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩) X) =
      fun X => K ^ (-P.val.2 / 2) * H X := by
    funext X
    rw [smoothing_cltStat_eq]
    change K ^ (-P.val.2 / 2) * fluctuation ⟨testAtScale p (ell N), _⟩ X -
      K ^ (-P.val.2 / 2) * fluctuation ⟨g.val, _⟩ X =
      K ^ (-P.val.2 / 2) * fluctuation ⟨e.val, _⟩ X
    rw [← mul_sub, ← fluctuation_sub_lift]
  have hnorm := (hH.const_mul (K ^ (-P.val.2 / 2)))
  dsimp only
  rw [hFG]
  refine ⟨hnorm, ?_⟩
  have hσ := hana ell hadm N h hh hh1
  have heq : subL2
      ⟨(fun x => (testAtScale p (ell N) x : ℂ)), testAtScaleL2 p (ell N)⟩
      ⟨(fun x => (g.val x : ℂ)), g.property⟩ =
      ⟨(fun x => (e.val x : ℂ)), e.property⟩ := by
    apply Subtype.ext
    funext x
    simp only [subL2, e, Complex.ofReal_sub]
  change cltVariance P (ell N) (subL2 _ ⟨(fun x => (g.val x : ℂ)), g.property⟩) < ⊤ ∧ _ at hσ
  rw [heq] at hσ
  have hσsq : σ.toReal ≤ (A * h ^ (P.val.2 / 2 - α - τ)) ^ 2 := by
    have hs := Real.sq_sqrt (ENNReal.toReal_nonneg (a := σ))
    have hb := hσ.2
    change Real.sqrt σ.toReal ≤ _ at hb
    nlinarith [Real.sqrt_nonneg σ.toReal,
      show 0 ≤ A * h ^ (P.val.2 / 2 - α - τ) by positivity]
  let q := max ((P.val.2 - 1) / 2) (α - P.val.2 / 2) + τ
  have hBsquare : (Real.sqrt B * K ^ q) ^ 2 = B * K ^ (2 * q) := by
    rw [mul_pow, Real.sq_sqrt hB.le, ← Real.rpow_natCast, ← Real.rpow_mul hK.le]
    congr 2
    push_cast
    ring
  have hbnd : (∫ X, (K ^ (-P.val.2 / 2) * H X) ^ 2 ∂gibbsMeasure P N) ≤
      (A * h ^ (P.val.2 / 2 - α - τ)) ^ 2 + (Real.sqrt B * K ^ q) ^ 2 := by
    rw [hBsquare]
    apply hsecond.trans
    rw [smoothing_error_exponent]
    dsimp only [q, σ] at hσsq ⊢
    linarith
  apply (eLpNorm_two_toReal_le_add_of_integral_sq_le hnorm (by positivity) (by positivity) hbnd).trans
  change A * h ^ (P.val.2 / 2 - α - τ) + Real.sqrt B * K ^ q ≤
    (A + Real.sqrt B) * (h ^ (P.val.2 / 2 - α - τ) + K ^ q)
  nlinarith [mul_nonneg hA.le (Real.rpow_nonneg hK.le q),
    mul_nonneg (Real.sqrt_nonneg B) (Real.rpow_nonneg hh.le (P.val.2 / 2 - α - τ))]

/-- Both quantitative assertions of the smoothing step in the proof of Theorem 3, with one
common constant and threshold. The Lipschitz assertion is the unconditional
theorem `Riesz1.clt_smoothing_lipschitz`. -/
theorem clt_smoothing_complete_of_variance_uniform
    (hvar : QuantitativeVarianceUniformConclusion)
    (P : Parameters) (p : Profile) (α : ℝ) (d : TestData)
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
        let G := cltStat P N (ell N) (cltScaledFun hρ (ell N) hh
          ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩)
        V < ⊤ ∧ Real.sqrt V.toReal ≤
          C * (cltDelta P N (ell N)) ^ (P.val.2 / 2 - α - τ) ∧
          MemLp (fun X => normalizedStatistic P p ell N X - G X) 2 (gibbsMeasure P N) ∧
          (eLpNorm (fun X => normalizedStatistic P p ell N X - G X) 2 (gibbsMeasure P N)).toReal ≤
            C * ((cltDelta P N (ell N)) ^ (P.val.2 / 2 - α - τ) +
              ((N : ℝ) * (ell N).val) ^ (max ((P.val.2 - 1) / 2) (α - P.val.2 / 2) + τ)) := by
  obtain ⟨A, Ka, hA, hKa, ha⟩ := clt_smoothing_sobolev P p α d ρ hρ τ hτ
  obtain ⟨B, Kb, hB, hKb, hb⟩ := clt_smoothing_of_variance_uniform hvar P p α d ρ hρ τ hτ
  refine ⟨max A B, max Ka Kb, hA.trans_le (le_max_left _ _),
    hKa.trans_le (le_max_left _ _), fun ell hadm N hN => ?_⟩
  obtain ⟨hv, hsob⟩ := ha ell hadm N ((le_max_left Ka Kb).trans hN)
  obtain ⟨hmem, hnorm⟩ := hb ell hadm N ((le_max_right Ka Kb).trans hN)
  have hδ : 0 < cltDelta P N (ell N) := cltDelta_pos P N (ell N)
  have hK : 0 ≤ (N : ℝ) * (ell N).val := mul_nonneg (by positivity) (ell N).property.1.le
  exact ⟨hv, hsob.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)),
    hmem, hnorm.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))⟩

end Riesz1.Internal
