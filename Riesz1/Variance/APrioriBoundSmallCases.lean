/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.APrioriRotationTranslationBound
public import Riesz1.ToMathlib.SizeBiasedVariance
public import Riesz1.Gibbs.WellDefined

/-!
# Small particle numbers in the a priori bound

For `N ≤ 2`, the supremum estimate alone gives both variance bounds of
Lemma 5.2, with the required exponent and a constant
chosen before the scale and test function. The statement concludes
first-moment validity and uses the extended variance.
This includes the exceptional one-particle case.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Riesz1.Internal

/-- The normalized kernel supremum with a factor `M ≥ 0`, including
`M = 0`. Direct integration avoids division by `M`. -/
theorem abs_sub_antipode_le_kernelSup_mul {s lam K ε L M : ℝ}
    (hs : s < 2) (hK : 1 ≤ K) (hlam : 0 ≤ lam) (hε : 0 < ε)
    (hL : 0 < L) (hM : 0 ≤ M) {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hper : Function.Periodic f L)
    (hder : ∀ u ∈ Icc (-(L / 2)) (L / 2),
      |deriv f u| ≤ M * cutoffMajorant s lam K |u|) (t : ℝ) :
    |f t - f (L / 2)| ≤ M * kernelSupConst s lam ε * K ^ (lam + ε) := by
  let g : ℝ → ℝ := fun u => f u - f (L / 2)
  have hg : ContDiff ℝ 1 g := hf.sub contDiff_const
  have hgper : Function.Periodic g L := by
    intro u
    dsimp [g]
    rw [hper u]
  obtain ⟨v, hv, he⟩ := hgper.exists_mem_Ico hL t (-(L / 2))
  have hv' : v ∈ Icc (-(L / 2)) (L / 2) := ⟨hv.1, by linarith [hv.2]⟩
  have hB : ∀ᵐ u ∂volume, u ∈ Icc (-(L / 2)) (L / 2) →
      |deriv g u| ≤ M * cutoffMajorant s lam K |u| := by
    exact ae_of_all _ fun u hu => by simpa only [g, deriv_sub_const] using hder u hu
  have hb := abs_le_intervalIntegral_of_periodic hL hg hgper (by simp [g])
    ((cutoffMajorant_intervalIntegrable hs hK hlam 0 (L / 2)).const_mul M) hB hv'
  rw [intervalIntegral.integral_const_mul] at hb
  have ht := integral_cutoffMajorant_tail_le (c := L / 2) hs hK hlam (abs_nonneg v)
  have hi := integral_cutoffMajorant_le hs hK hlam hε (by linarith : 0 ≤ L / 2)
  have hall : |g v| ≤ M * (kernelSupConst s lam ε * K ^ (lam + ε)) :=
    hb.trans (mul_le_mul_of_nonneg_left (ht.trans hi) hM)
  change |g t| ≤ _
  rw [he]
  simpa only [mul_assoc] using hall

/-- A bounded centered finite sum has the corresponding extended
variance bound. This helper permits arbitrary measurable arguments. -/
theorem sum_variance_le_of_centered_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (N : ℕ+)
    (f : ℝ → ℝ) (hf : Measurable f) (g : Fin (N : ℕ) → Ω → ℝ)
    (hg : ∀ i, Measurable (g i)) (a B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ t, |f t - a| ≤ B) :
    ∃ hF : Integrable (fun x => ∑ i, f (g i x)) μ,
      Riesz1.variance μ (fun x => ∑ i, f (g i x)) hF ≤
        ENNReal.ofReal ((((N : ℕ) : ℝ) * B) ^ 2) := by
  let F : Ω → ℝ := fun x => ∑ i, f (g i x)
  let m : ℝ := ((N : ℕ) : ℝ) * a
  have hm : Measurable F := by
    dsimp [F]
    exact Finset.measurable_sum _ fun i _ => hf.comp (hg i)
  have hsum (x : Ω) : |F x - m| ≤ ((N : ℕ) : ℝ) * B := by
    have he : F x - m = ∑ i : Fin (N : ℕ), (f (g i x) - a) := by
      simp [F, m, Finset.sum_sub_distrib]
    rw [he]
    calc _ ≤ ∑ i : Fin (N : ℕ), |f (g i x) - a| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin (N : ℕ), B := Finset.sum_le_sum fun i _ => hb (g i x)
      _ = _ := by simp
  have hL : MemLp (fun x => F x - m) 2 μ :=
    MemLp.of_bound (hm.sub measurable_const).aestronglyMeasurable _
      (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hsum x)
  have hF : MemLp F 2 μ := by
    convert hL.add (memLp_const m) using 1
    ext x
    simp
  refine ⟨hF.integrable one_le_two, (variance_le_lintegral_sq_sub μ hF m).trans ?_⟩
  calc _ ≤ ∫⁻ _x : Ω, ENNReal.ofReal ((((N : ℕ) : ℝ) * B) ^ 2) ∂μ := by
        apply lintegral_mono
        intro x
        apply ENNReal.ofReal_le_ofReal
        have hsq := (sq_le_sq₀ (abs_nonneg (F x - m))
          (show 0 ≤ ((N : ℕ) : ℝ) * B by positivity)).2 (hsum x)
        simpa only [sq_abs] using hsq
    _ = _ := by simp

/-- Both claims of Lemma 5.2, for `N = 1` and
`N = 2`, with no comparison hypothesis and no hypotheses from `Riesz1.External`.
The envelope here has its original center and radius two. -/
theorem a_priori_small_particles (P : Parameters) (lam ε : ℝ)
    (hlam : 0 ≤ lam) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+), (N : ℕ) ≤ 2 →
      ∀ ℓ : ℝ, 0 < ℓ → ℓ ≤ 1 → 1 ≤ ((N : ℕ) : ℝ) * ℓ →
      ∀ M : ℝ, 0 ≤ M → ∀ f : ℝ → ℝ, ContDiff ℝ 1 f → Function.Periodic f (1 / ℓ) →
      (∀ u ∈ Icc (-(1 / ℓ / 2)) (1 / ℓ / 2),
        |deriv f u| ≤ M * cutoffMajorant P.val.2 lam (((N : ℕ) : ℝ) * ℓ) |u|) →
      (∃ hA : Integrable (fun X : Configuration N =>
          ∑ i, f ((X.val i - X.val ⟨0, N.pos⟩) / ℓ)) (gibbsMeasure P N),
        Riesz1.variance (gibbsMeasure P N) (fun X =>
          ∑ i, f ((X.val i - X.val ⟨0, N.pos⟩) / ℓ)) hA ≤
          ENNReal.ofReal (C * M ^ 2 * (((N : ℕ) : ℝ) * ℓ) ^ (ε + max (2 * lam) P.val.2))) ∧
      (∃ hB : Integrable (fun X : Configuration N =>
          ∑ i, f (X.val i / ℓ)) (gibbsMeasure P N),
        Riesz1.variance (gibbsMeasure P N) (fun X => ∑ i, f (X.val i / ℓ)) hB ≤
          ENNReal.ofReal (C * M ^ 2 * (((N : ℕ) : ℝ) * ℓ) ^ (ε + max (2 * lam) P.val.2))) := by
  let A := kernelSupConst P.val.2 lam (ε / 2)
  have hA : 0 ≤ A := by
    dsimp [A, kernelSupConst]
    have : 0 < lam + ε / 2 := by linarith
    have : 0 < 2 - P.val.2 := by linarith [P.2.2.2]
    positivity
  refine ⟨4 * A ^ 2 + 1, by positivity, fun N hN ℓ hℓ _hℓ1 hK M hM f hf hper hder => ?_⟩
  have := (modelWellDefined P N).2.2
  let K := ((N : ℕ) : ℝ) * ℓ
  have hK0 : 0 < K := by dsimp [K]; linarith
  have hsup (t : ℝ) : |f t - f (1 / ℓ / 2)| ≤ M * A * K ^ (lam + ε / 2) :=
    abs_sub_antipode_le_kernelSup_mul (by linarith [P.2.2.2]) hK hlam (by linarith)
      (by positivity) hM hf hper hder t
  have hfactor : ((((N : ℕ) : ℝ) * (A * K ^ (lam + ε / 2))) ^ 2) ≤
      (4 * A ^ 2 + 1) * K ^ (ε + max (2 * lam) P.val.2) := by
    have hN' : (N : ℝ) ≤ 2 := by exact_mod_cast hN
    have hNsq : ((N : ℕ) : ℝ) ^ 2 ≤ 4 := by
      have : (0 : ℝ) ≤ ((N : ℕ) : ℝ) := by positivity
      nlinarith
    have hp : (K ^ (lam + ε / 2)) ^ 2 = K ^ (2 * lam + ε) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hK0.le]
      congr 1
      ring
    have hpow : K ^ (2 * lam + ε) ≤ K ^ (ε + max (2 * lam) P.val.2) :=
      Real.rpow_le_rpow_of_exponent_le hK (by linarith [le_max_left (2 * lam) P.val.2])
    rw [mul_pow, mul_pow, hp]
    calc _ ≤ 4 * A ^ 2 * K ^ (2 * lam + ε) := by
          calc _ ≤ 4 * (A ^ 2 * K ^ (2 * lam + ε)) :=
                  mul_le_mul_of_nonneg_right hNsq (by positivity)
            _ = _ := by ring
      _ ≤ 4 * A ^ 2 * K ^ (ε + max (2 * lam) P.val.2) :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hbound (g : Fin (N : ℕ) → Configuration N → ℝ)
      (hg : ∀ i, Measurable (g i)) :
      ∃ hF : Integrable (fun X => ∑ i, f (g i X)) (gibbsMeasure P N),
        Riesz1.variance (gibbsMeasure P N) (fun X => ∑ i, f (g i X)) hF ≤
          ENNReal.ofReal ((4 * A ^ 2 + 1) * M ^ 2 * K ^ (ε + max (2 * lam) P.val.2)) := by
    obtain ⟨hF, hv⟩ := sum_variance_le_of_centered_bound (gibbsMeasure P N) N f
      hf.continuous.measurable g hg (f (1 / ℓ / 2)) (M * A * K ^ (lam + ε / 2))
      (by positivity) hsup
    refine ⟨hF, hv.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    calc _ = M ^ 2 * ((((N : ℕ) : ℝ) * (A * K ^ (lam + ε / 2))) ^ 2) := by ring
      _ ≤ M ^ 2 * ((4 * A ^ 2 + 1) * K ^ (ε + max (2 * lam) P.val.2)) :=
        mul_le_mul_of_nonneg_left hfactor (sq_nonneg M)
      _ = _ := by ring
  constructor
  · apply hbound (fun i X => (X.val i - X.val ⟨0, N.pos⟩) / ℓ)
    intro i
    have hm (j : Fin (N : ℕ)) : Measurable (fun X : Configuration N => X.val j) :=
      (measurable_pi_apply j).comp measurable_subtype_coe
    exact ((hm i).sub (hm ⟨0, N.pos⟩)).div_const ℓ
  · apply hbound (fun i X => X.val i / ℓ)
    intro i
    have hm : Measurable (fun X : Configuration N => X.val i) :=
      (measurable_pi_apply i).comp measurable_subtype_coe
    exact hm.div_const ℓ

end Riesz1.Internal

end
