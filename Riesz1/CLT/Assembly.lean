/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.CLT.AssemblyCases
public import Riesz1.CLT.AssemblyInput
public import Riesz1.CLT.VaryingLimit
public import Riesz1.CLT.TestConvergence
public import Riesz1.Frozen.External.BakryEmery
public import Riesz1.Frozen.Mesoscopic
public import Riesz1.Frozen.StatisticLaws
public import Riesz1.Frozen.ParticleNumber
public import Riesz1.Frozen.ConvergesInLaw
public import Riesz1.Frozen.NormalLaw
public import Riesz1.Frozen.BlDistance

/-!
# Assembly of the central limit theorem (Theorem 3)

`Riesz1.Internal.central_limit_theorem_of_inputs` proves the proposition of
`Riesz1.central_limit_theorem` (`Riesz1/Frozen/CentralLimitTheorem.lean`), copied symbol for
symbol. Its conditional hypotheses are `hBE` (the Bakry–Émery criterion `External.BakryEmery`) and
`hPL` (the Prékopa–Leindler inequality `External.PrekopaLeindler`), and the conclusions of the
earlier results of the chain, stated in `AssemblyInput.lean`: the first and second error bounds in
the proof of Theorem 3, Theorem 2 (copied), and the uniform version of Theorem 2. The hypothesis
`hBE` is not used by the chain, since the identity and the copies depend on `hPL` only. It is kept
as a hypothesis of the statement.

The proof has four parts, matching the proposition:

* **A.** Well-definedness, Sobolev membership, finite variance and measurability.
* **B.** Convergence in law in the macroscopic case, from the bounded-Lipschitz bound of
  `assembly_bl_profile` along `N ↦ N ℓ_N → ∞`.
* **C.** Convergence in law in the compact case, to the line variance, using the line
  approximation of the quantitative variance conclusion.
* **D.** The bounded-Lipschitz rate, which is `assembly_bl_profile`.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ContDiff ENNReal NNReal BoundedContinuousFunction

namespace Riesz1.Internal

/-- A bound `f n ≤ ofReal (C K_n^p)` with `K_n → ∞` and `p < 0` forces `f n → 0`. -/
lemma tendsto_zero_of_le_rpow {f : ℕ → ℝ≥0∞} {K : ℕ → ℝ} {C p : ℝ}
    (hK : Tendsto K atTop atTop) (hp : p < 0)
    (h : ∀ᶠ n in atTop, f n ≤ ENNReal.ofReal (C * K n ^ p)) :
    Tendsto f atTop (𝓝 0) := by
  have hpow : Tendsto (fun n => K n ^ p) atTop (𝓝 0) := by
    have h0 := tendsto_rpow_neg_atTop (y := -p) (neg_pos.mpr hp)
    simp only [neg_neg] at h0
    exact h0.comp hK
  have hlim : Tendsto (fun n => ENNReal.ofReal (C * K n ^ p)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => C * K n ^ p) atTop (𝓝 0) := by
      simpa using hpow.const_mul C
    simpa using ENNReal.tendsto_ofReal h1
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun n => zero_le) h

/-- **Theorem 3** (proposition of `Riesz1.central_limit_theorem`),
proved from the conditional inputs. The body is copied symbol for symbol from
`Riesz1/Frozen/CentralLimitTheorem.lean`. -/
theorem central_limit_theorem_of_inputs (_hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (hErr1 : AssemblyErrorOneConclusion) (hErr2 : AssemblyErrorTwoConclusion)
    (hQV : ∀ (beta s : ℝ) (hbeta : 0 < beta) (hs : 0 < s) (hs1 : s < 1),
      AssemblyVarianceConclusion beta s hbeta hs hs1)
    (hQVU : QuantitativeVarianceUniformConclusion) :
  ∀ (beta s : ℝ) (hbeta : 0 < beta) (hs : 0 < s) (hs1 : s < 1),
    let P : Parameters := ⟨(beta, s), hbeta, hs, hs1⟩
    ∀ (p : Profile) (alpha : ℝ) (d : TestData),
      (∀ ell : Scales, Admissible P p ell alpha d → Mesoscopic ell →
        ModelWellDefined P ∧
        (∀ N, CircleSobolev ((1 - s) / 2) (fun x => (testAtScale p (ell N) x : ℂ)) ∧
          circleVariance P p (ell N) < ⊤ ∧
          AEMeasurable (normalizedStatistic P p ell N) (gibbsMeasure P N)) ∧
        (((∀ N, (ell N).val = 1) →
          ConvergesInLaw (statisticLaws P p ell)
            (normalLaw (circleVariance P p ⟨1, zero_lt_one, le_rfl⟩).toNNReal)) ∧
         ((CompactProfile p ∧
            Tendsto (fun n => (ell (particleNumber n)).val) atTop (𝓝 0)) →
          ∃ f0 : Lp ℂ 2 (volume : Measure ℝ),
            RepresentsZeroExtension p f0 ∧ LineSobolev ((1 - s) / 2) f0 ∧
            lineVariance P f0 < ⊤ ∧
            ConvergesInLaw (statisticLaws P p ell) (normalLaw (lineVariance P f0).toNNReal)))) ∧
      (let r := (2 - s) * (s - 2 * alpha) / (2 * (4 + s))
       ∀ eps : ℝ, 0 < eps → ∃ C : ℝ, 0 < C ∧
        ∀ ell : Scales, Admissible P p ell alpha d → Mesoscopic ell →
          0 < r ∧ ∀ N : ℕ+, 1 ≤ (N : ℝ) * (ell N).val →
            ∃ law : ProbabilityMeasure ℝ,
              (law : Measure ℝ) = (gibbsMeasure P N).map (normalizedStatistic P p ell N) ∧
              blDistance law
                ⟨normalLaw (circleVariance P p (ell N)).toNNReal,
                  by unfold normalLaw; infer_instance⟩ ≤
              ENNReal.ofReal (C * ((N : ℝ) * (ell N).val) ^
                (eps + max ((s - 1) / 2) (-r)))) := by
  intro beta s hbeta hs hs1 P p alpha d
  obtain ⟨ρ, hρ⟩ := assembly_exists_isMollifier
  have hPs0 : 0 < P.val.2 := hs
  have hPs1 : P.val.2 < 1 := hs1
  have hβ : ∀ N : ℕ+, IsProbabilityMeasure (gibbsMeasure P N) := fun N =>
    (modelWellDefined P N).2.2
  obtain ⟨hVarA, -, hVarC⟩ := hQV beta s hbeta hs hs1 p alpha d
  refine ⟨fun ell hadm hmes => ?_, ?_⟩
  · -- Parts A, B and C, for an admissible mesoscopic scale sequence.
    have hA := hVarA ell hadm
    have hα : alpha < P.val.2 / 2 := hadm.2.1
    have hK : Tendsto (fun n => ((particleNumber n : ℕ+) : ℝ) * (ell (particleNumber n)).val)
        atTop atTop := hmes
    refine ⟨modelWellDefined P, fun N => ⟨(hA.2 N).1, (hA.2 N).2,
      (smoothing_statistics_memLp P p ell N hρ).1.aestronglyMeasurable.aemeasurable⟩, ?_, ?_⟩
    · -- Part B: the macroscopic case.
      intro hmacro
      -- Exponents of the rate that make the bound vanish.
      have hr0 : 0 < (2 - P.val.2) * (P.val.2 - 2 * alpha) / (2 * (4 + P.val.2)) :=
        div_pos (mul_pos (by linarith) (by linarith [hα])) (by linarith)
      have heps0 : 0 < min ((1 - P.val.2) / 2) ((2 - P.val.2) * (P.val.2 - 2 * alpha) /
          (2 * (4 + P.val.2))) / 2 :=
        half_pos (lt_min (by linarith) hr0)
      have hp0 : min ((1 - P.val.2) / 2) ((2 - P.val.2) * (P.val.2 - 2 * alpha) /
            (2 * (4 + P.val.2))) / 2 +
          max ((P.val.2 - 1) / 2) (-((2 - P.val.2) * (P.val.2 - 2 * alpha) /
            (2 * (4 + P.val.2)))) < 0 := by
        have h2 : 0 < min ((1 - P.val.2) / 2) ((2 - P.val.2) * (P.val.2 - 2 * alpha) /
            (2 * (4 + P.val.2))) := lt_min (by linarith) hr0
        have h1 : max ((P.val.2 - 1) / 2) (-((2 - P.val.2) * (P.val.2 - 2 * alpha) /
            (2 * (4 + P.val.2)))) ≤ -min ((1 - P.val.2) / 2) ((2 - P.val.2) * (P.val.2 - 2 * alpha) /
              (2 * (4 + P.val.2))) :=
          max_le (by linarith [min_le_left ((1 - P.val.2) / 2) ((2 - P.val.2) * (P.val.2 - 2 * alpha) /
              (2 * (4 + P.val.2)))])
            (by linarith [min_le_right ((1 - P.val.2) / 2) ((2 - P.val.2) * (P.val.2 - 2 * alpha) /
              (2 * (4 + P.val.2)))])
        linarith
      obtain ⟨C, hC, hb⟩ := assembly_bl_profile hPL hErr1 hErr2 hQVU P p alpha d hα _ heps0
      have hcv : ∀ N : ℕ+, circleVariance P p (ell N) =
          circleVariance P p ⟨1, zero_lt_one, le_rfl⟩ := by
        intro N
        congr 1
        exact Subtype.ext (hmacro N)
      let laws : ℕ → ProbabilityMeasure ℝ := fun n =>
        ⟨(gibbsMeasure P (particleNumber n)).map (normalizedStatistic P p ell (particleNumber n)),
          inferInstance⟩
      apply convergesInLaw_of_blDistance_tendsto_zero laws
        ⟨normalLaw (circleVariance P p ⟨1, zero_lt_one, le_rfl⟩).toNNReal,
          by unfold normalLaw; infer_instance⟩
      refine tendsto_zero_of_le_rpow (C := C) (K := fun n => ((particleNumber n : ℕ+) : ℝ) *
        (ell (particleNumber n)).val) hK hp0 ?_
      refine (hK.eventually_ge_atTop 1).mono fun n hn => ?_
      obtain ⟨law, hlaw, hdist⟩ := hb ell hadm (particleNumber n) hn
      have hlaweq : law = laws n := Subtype.ext hlaw
      rw [hlaweq] at hdist
      have hmid : (⟨normalLaw (circleVariance P p (ell (particleNumber n))).toNNReal,
          by unfold normalLaw; infer_instance⟩ : ProbabilityMeasure ℝ) =
          ⟨normalLaw (circleVariance P p ⟨1, zero_lt_one, le_rfl⟩).toNNReal,
            by unfold normalLaw; infer_instance⟩ :=
        Subtype.ext (by unfold normalLaw; rw [hcv (particleNumber n)])
      exact (congrArg (blDistance (laws n)) hmid.symm).le.trans hdist
    · -- Part C: the compact case, converging to the line variance.
      rintro ⟨hcomp, hcomp0⟩
      obtain ⟨f0, hrep, hsob, hfin, C1, hC1, hline⟩ := hVarC ⟨ell, hadm⟩ hcomp
      refine ⟨f0, hrep, hsob, hfin, ?_⟩
      have hr0 : 0 < (2 - P.val.2) * (P.val.2 - 2 * alpha) / (2 * (4 + P.val.2)) :=
        div_pos (mul_pos (by linarith) (by linarith [hα])) (by linarith)
      have heps0 : 0 < min ((1 - P.val.2) / 2) ((2 - P.val.2) * (P.val.2 - 2 * alpha) /
          (2 * (4 + P.val.2))) / 2 :=
        half_pos (lt_min (by linarith) hr0)
      have hp0 : min ((1 - P.val.2) / 2) ((2 - P.val.2) * (P.val.2 - 2 * alpha) /
            (2 * (4 + P.val.2))) / 2 +
          max ((P.val.2 - 1) / 2) (-((2 - P.val.2) * (P.val.2 - 2 * alpha) /
            (2 * (4 + P.val.2)))) < 0 := by
        have h2 : 0 < min ((1 - P.val.2) / 2) ((2 - P.val.2) * (P.val.2 - 2 * alpha) /
            (2 * (4 + P.val.2))) := lt_min (by linarith) hr0
        have h1 : max ((P.val.2 - 1) / 2) (-((2 - P.val.2) * (P.val.2 - 2 * alpha) /
            (2 * (4 + P.val.2)))) ≤ -min ((1 - P.val.2) / 2) ((2 - P.val.2) * (P.val.2 - 2 * alpha) /
              (2 * (4 + P.val.2))) :=
          max_le (by linarith [min_le_left ((1 - P.val.2) / 2) ((2 - P.val.2) * (P.val.2 - 2 * alpha) /
              (2 * (4 + P.val.2)))])
            (by linarith [min_le_right ((1 - P.val.2) / 2) ((2 - P.val.2) * (P.val.2 - 2 * alpha) /
              (2 * (4 + P.val.2)))])
        linarith
      obtain ⟨C, hC, hb⟩ := assembly_bl_profile hPL hErr1 hErr2 hQVU P p alpha d hα _ heps0
      let laws : ℕ → ProbabilityMeasure ℝ := fun n =>
        ⟨(gibbsMeasure P (particleNumber n)).map (normalizedStatistic P p ell (particleNumber n)),
          inferInstance⟩
      let σ : ℕ → ℝ≥0 := fun n =>
        NNReal.sqrt (circleVariance P p (ell (particleNumber n))).toNNReal
      let σ₀ : ℝ≥0 := NNReal.sqrt (lineVariance P f0).toNNReal
      -- The standard deviations converge: the circle variances converge to the line variance.
      have hv : Tendsto (fun n => (circleVariance P p (ell (particleNumber n))).toNNReal) atTop
          (𝓝 (lineVariance P f0).toNNReal) := by
        rw [← NNReal.tendsto_coe]
        have hpow : Tendsto (fun n => (ell (particleNumber n)).val ^ (2 - P.val.2)) atTop (𝓝 0) := by
          have h0 := ((Real.continuous_rpow_const (by linarith : (0 : ℝ) ≤ 2 - P.val.2)).tendsto 0).comp
            hcomp0
          rw [Real.zero_rpow (by linarith : (2 - P.val.2) ≠ 0)] at h0
          exact h0
        have hdiff : Tendsto (fun n => |(circleVariance P p (ell (particleNumber n))).toReal -
            (lineVariance P f0).toReal|) atTop (𝓝 0) := by
          refine squeeze_zero (fun n => abs_nonneg _) (fun n => (hline _).2.2) ?_
          simpa using hpow.const_mul C1
        have hlim : Tendsto (fun n => (circleVariance P p (ell (particleNumber n))).toReal) atTop
            (𝓝 (lineVariance P f0).toReal) := by
          rw [tendsto_iff_norm_sub_tendsto_zero]
          simpa [Real.norm_eq_abs] using hdiff
        exact hlim
      have hσ : Tendsto σ atTop (𝓝 σ₀) :=
        (NNReal.continuous_sqrt.tendsto _).comp hv
      -- The bounded-Lipschitz distance to the Gaussians of the standard deviations tends to zero.
      have hgauss : Tendsto (fun n => blDistance (laws n)
          ⟨gaussianReal 0 (σ n ^ 2), inferInstance⟩) atTop (𝓝 0) := by
        refine tendsto_zero_of_le_rpow (C := C) (K := fun n => ((particleNumber n : ℕ+) : ℝ) *
          (ell (particleNumber n)).val) hK hp0 ?_
        refine (hK.eventually_ge_atTop 1).mono fun n hn => ?_
        obtain ⟨law, hlaw, hdist⟩ := hb ell hadm (particleNumber n) hn
        have hlaweq : law = laws n := Subtype.ext hlaw
        have hgn : (⟨gaussianReal 0 (σ n ^ 2), inferInstance⟩ : ProbabilityMeasure ℝ) =
            ⟨normalLaw (circleVariance P p (ell (particleNumber n))).toNNReal,
              by unfold normalLaw; infer_instance⟩ :=
          Subtype.ext (by
            show gaussianReal 0 (σ n ^ 2) = normalLaw (circleVariance P p (ell (particleNumber n))).toNNReal
            unfold normalLaw
            simp only [σ, NNReal.sq_sqrt])
        rw [hlaweq] at hdist
        exact (congrArg (blDistance (laws n)) hgn).le.trans hdist
      have key := convergesInLaw_of_blDistance_gaussianReal laws σ σ₀ hσ hgauss
      have e2 : gaussianReal 0 (σ₀ ^ 2) = normalLaw (lineVariance P f0).toNNReal := by
        unfold normalLaw
        simp only [σ₀, NNReal.sq_sqrt]
      rw [e2] at key
      exact key
  · -- Part D: the bounded-Lipschitz rate.
    intro r eps heps
    by_cases hex : ∃ ell₀ : Scales, Admissible P p ell₀ alpha d
    · obtain ⟨ell₀, h₀⟩ := hex
      obtain ⟨C, hC, hb⟩ := assembly_bl_profile hPL hErr1 hErr2 hQVU P p alpha d h₀.2.1 eps heps
      refine ⟨C, hC, fun ell hadm _ => ⟨?_, fun N hN => hb ell hadm N hN⟩⟩
      have hα : alpha < P.val.2 / 2 := hadm.2.1
      show 0 < (2 - P.val.2) * (P.val.2 - 2 * alpha) / (2 * (4 + P.val.2))
      exact div_pos (mul_pos (by linarith) (by linarith [hα])) (by linarith)
    · exact ⟨1, one_pos, fun ell hadm _ => (hex ⟨ell, hadm⟩).elim⟩

end Riesz1.Internal

end
end
