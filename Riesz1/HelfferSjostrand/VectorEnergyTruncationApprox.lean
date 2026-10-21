/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.VectorEnergyTruncationTest

/-!
# Approximation of the truncated jets in `L²`

This file proves the `L²` facts about truncated anchored jets that feed the weak compactness
argument in the proof of Lemma 3.4:

* the pointwise squared norm of the jet of a truncated test tuple is at most that of the tuple, so
  the jet norm does not increase under truncation.
* the scalar values of the truncated jets converge in `L²(μ)` to the positive part of the limit
  value, when the approximating test tuples converge in `L²` and the smoothing parameter tends
  to zero.
* the particle values of a jet point are determined by its scalar values, and a jet point is
  determined by its scalar values, gradients and pair energies.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ContDiff InnerProductSpace ENNReal

namespace Riesz1

variable {n : ℕ} {c : ℝ}

/-- The anchor particle of a jet vanishes almost everywhere. -/
theorem anchoredParticleValue_zero_ae (μ : Measure (AnchoredEuclidean n)) [IsFiniteMeasure μ]
    (Ψ : Lp (AnchoredJetPoint n) 2 μ) :
    (anchoredParticleValue μ (0 : Fin (n.succPNat : ℕ)) Ψ : AnchoredEuclidean n → ℝ) =ᵐ[μ] 0 := by
  unfold anchoredParticleValue
  filter_upwards [ContinuousLinearMap.coeFn_compLpL (particleValueL (0 : Fin (n.succPNat : ℕ)))
    (μ := μ) Ψ] with y hy
  rw [hy]
  rfl

/-- The particle `j + 1` of a jet is its `j`-th scalar value, almost everywhere. -/
theorem anchoredParticleValue_succ_ae (μ : Measure (AnchoredEuclidean n)) [IsFiniteMeasure μ]
    (Ψ : Lp (AnchoredJetPoint n) 2 μ) (j : Fin n) :
    (anchoredParticleValue μ j.succ Ψ : AnchoredEuclidean n → ℝ) =ᵐ[μ]
      (anchoredJetValue μ j Ψ : AnchoredEuclidean n → ℝ) := by
  unfold anchoredParticleValue anchoredJetValue
  filter_upwards [ContinuousLinearMap.coeFn_compLpL (particleValueL j.succ) (μ := μ) Ψ,
    ContinuousLinearMap.coeFn_compLpL (jetValueL j) (μ := μ) Ψ] with y hy hy'
  rw [hy, hy']
  rfl

/-- Two jets with a.e. equal scalar values have a.e. equal particle values. -/
theorem anchoredParticleValue_ae_of_value_ae (μ : Measure (AnchoredEuclidean n))
    [IsFiniteMeasure μ] (Ψ Φ : Lp (AnchoredJetPoint n) 2 μ)
    (h : ∀ i : Fin n, (anchoredJetValue μ i Ψ : AnchoredEuclidean n → ℝ) =ᵐ[μ]
      (anchoredJetValue μ i Φ : AnchoredEuclidean n → ℝ))
    (k : Fin (n.succPNat : ℕ)) :
    (anchoredParticleValue μ k Ψ : AnchoredEuclidean n → ℝ) =ᵐ[μ]
      (anchoredParticleValue μ k Φ : AnchoredEuclidean n → ℝ) := by
  induction k using Fin.cases with
  | zero =>
    filter_upwards [anchoredParticleValue_zero_ae μ Ψ, anchoredParticleValue_zero_ae μ Φ]
      with y h1 h2
    exact h1.trans h2.symm
  | succ j =>
    filter_upwards [anchoredParticleValue_succ_ae μ Ψ j, anchoredParticleValue_succ_ae μ Φ j,
      h j] with y h1 h2 h3
    exact h1.trans (h3.trans h2.symm)

/-- A jet point is determined by its scalar values, gradients and pair energies. -/
theorem jetPoint_ext (x y : AnchoredJetPoint n) (hv : ∀ i : Fin n, jetValueL i x = jetValueL i y)
    (hg : ∀ i : Fin n, jetGradL i x = jetGradL i y)
    (he : ∀ p : HsPairIndex n.succPNat, jetEnergyL p x = jetEnergyL p y) : x = y := by
  have h1 : x.ofLp.1 = y.ofLp.1 := by
    ext i
    exact hv i
  have hgv : x.ofLp.2.ofLp.1 = y.ofLp.2.ofLp.1 := by
    refine PiLp.ext fun i => ?_
    exact hg i
  have hen : x.ofLp.2.ofLp.2 = y.ofLp.2.ofLp.2 := by
    ext p
    exact he p
  have h2 : x.ofLp.2 = y.ofLp.2 := WithLp.ofLp_injective (p := 2) (Prod.ext hgv hen)
  exact WithLp.ofLp_injective (p := 2) (Prod.ext h1 h2)

/-- The squared norm of a pair in the Hilbert space `WithLp 2 (E × F)` is the sum of the squared
norms of its components. -/
theorem norm_sq_toLp_prod {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] (a : E)
    (b : F) : ‖(WithLp.toLp 2 (a, b) : WithLp 2 (E × F))‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
  rw [WithLp.prod_norm_sq_eq_of_L2]
  rfl

/-- The pointwise squared norm of a jet of a test tuple: the values, the gradients and the pair
energies, each in its Euclidean norm. -/
theorem norm_sq_anchoredJetFun (χ : HsPairPotentials n.succPNat c) (u : AnchoredVectorTest n)
    (y : AnchoredEuclidean n) :
    ‖anchoredJetFun χ u y‖ ^ 2 = ∑ i : Fin n, (u i : AnchoredEuclidean n → ℝ) y ^ 2 +
      ∑ i : Fin n, ‖gradient (u i : AnchoredEuclidean n → ℝ) y‖ ^ 2 +
      ∑ p : HsPairIndex n.succPNat, anchoredEnergyFun χ u y p ^ 2 := by
  unfold anchoredJetFun
  rw [norm_sq_toLp_prod, norm_sq_toLp_prod]
  simp only [anchoredTestVector, PiLp.norm_sq_eq_of_L2, Real.norm_eq_abs, sq_abs]
  ring

/-- The pointwise jet of a truncated test tuple has squared norm at most that of the tuple. -/
theorem norm_sq_anchoredJetFun_truncTest_le {ε : ℝ} (hε : 0 < ε)
    (χ : HsPairPotentials n.succPNat c) (u : AnchoredVectorTest n) (y : AnchoredEuclidean n) :
    ‖anchoredJetFun χ (truncTest hε u) y‖ ^ 2 ≤ ‖anchoredJetFun χ u y‖ ^ 2 := by
  rw [norm_sq_anchoredJetFun, norm_sq_anchoredJetFun]
  have hval : ∑ i : Fin n, (truncTest hε u i : AnchoredEuclidean n → ℝ) y ^ 2 ≤
      ∑ i : Fin n, (u i : AnchoredEuclidean n → ℝ) y ^ 2 := by
    refine Finset.sum_le_sum fun i _ => ?_
    have h := abs_smoothPosPart_le hε ((u i : AnchoredEuclidean n → ℝ) y)
    have h2 := pow_le_pow_left₀ (abs_nonneg _) h 2
    rw [sq_abs, sq_abs] at h2
    exact h2
  have hgrad : ∑ i : Fin n, ‖gradient (truncTest hε u i : AnchoredEuclidean n → ℝ) y‖ ^ 2 ≤
      ∑ i : Fin n, ‖gradient (u i : AnchoredEuclidean n → ℝ) y‖ ^ 2 := by
    refine Finset.sum_le_sum fun i _ => ?_
    have hg := gradient_smoothPosPartTest hε (u i) y
    change ‖gradient (smoothPosPartTest hε (u i) : AnchoredEuclidean n → ℝ) y‖ ^ 2 ≤ _
    rw [hg, norm_smul, Real.norm_eq_abs, mul_pow]
    have hd : |deriv (smoothPosPart ε) ((u i : AnchoredEuclidean n → ℝ) y)| ^ 2 ≤ 1 := by
      have h1 := abs_deriv_smoothPosPart_le' hε ((u i : AnchoredEuclidean n → ℝ) y)
      have h0 := abs_nonneg (deriv (smoothPosPart ε) ((u i : AnchoredEuclidean n → ℝ) y))
      nlinarith
    exact mul_le_of_le_one_left (sq_nonneg _) hd
  have hen : ∑ p : HsPairIndex n.succPNat, anchoredEnergyFun χ (truncTest hε u) y p ^ 2 ≤
      ∑ p : HsPairIndex n.succPNat, anchoredEnergyFun χ u y p ^ 2 := by
    refine Finset.sum_le_sum fun p _ => ?_
    have h := pow_le_pow_left₀ (abs_nonneg _) (abs_anchoredEnergyFun_truncTest_le hε χ u y p) 2
    rw [sq_abs, sq_abs] at h
    exact h
  linarith

/-- The jet of a truncated test tuple has `L²` norm at most that of the tuple. -/
theorem norm_anchoredVectorJet_truncTest_le {ε : ℝ} (hε : 0 < ε)
    (χ : HsPairPotentials n.succPNat c) (μ : Measure (AnchoredEuclidean n)) [IsFiniteMeasure μ]
    (u : AnchoredVectorTest n) :
    ‖anchoredVectorJet χ μ (truncTest hε u)‖ ≤ ‖anchoredVectorJet χ μ u‖ := by
  unfold anchoredVectorJet
  rw [Lp.norm_def, Lp.norm_def]
  refine ENNReal.toReal_mono (MemLp.eLpNorm_lt_top (Lp.memLp _)).ne ?_
  refine eLpNorm_mono_ae (Lp.aestronglyMeasurable _) ?_
  filter_upwards [(memLp_anchoredJetFun χ μ (truncTest hε u)).coeFn_toLp,
    (memLp_anchoredJetFun χ μ u).coeFn_toLp] with y h1 h2
  rw [h1, h2]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp
    (norm_sq_anchoredJetFun_truncTest_le hε χ u y)

/-- The scalar value of a truncated jet is the smoothed scalar value, almost everywhere. -/
theorem anchoredJetValue_truncTest_ae (χ : HsPairPotentials n.succPNat c)
    (μ : Measure (AnchoredEuclidean n)) [IsFiniteMeasure μ] {ε : ℝ} (hε : 0 < ε)
    (u : AnchoredVectorTest n) (i : Fin n) :
    (anchoredJetValue μ i (anchoredVectorJet χ μ (truncTest hε u)) :
        AnchoredEuclidean n → ℝ) =ᵐ[μ]
      fun y => smoothPosPart ε ((u i : AnchoredEuclidean n → ℝ) y) := by
  filter_upwards [anchoredJetValue_ae χ μ (truncTest hε u) i] with y hy
  rw [hy]
  rfl

/-- The truncated scalar values of a convergent sequence of test jets converge in `L²(μ)` to the
positive part of the scalar value of the limit. The smoothing parameters `ε k` tend to zero. -/
theorem tendsto_truncTest_value (χ : HsPairPotentials n.succPNat c)
    (μ : Measure (AnchoredEuclidean n)) [IsFiniteMeasure μ] (ε : ℕ → ℝ) (hε : ∀ k, 0 < ε k)
    (hε0 : Tendsto ε atTop (𝓝 0)) (v : ℕ → AnchoredVectorTest n)
    {Ψ : Lp (AnchoredJetPoint n) 2 μ}
    (hv : Tendsto (fun k => anchoredVectorJet χ μ (v k)) atTop (𝓝 Ψ)) (i : Fin n) :
    Tendsto (fun k => anchoredJetValue μ i (anchoredVectorJet χ μ (truncTest (hε k) (v k))))
      atTop (𝓝 (Lp.posPart (anchoredJetValue μ i Ψ))) := by
  have hg : Tendsto (fun k => anchoredJetValue μ i (anchoredVectorJet χ μ (v k))) atTop
      (𝓝 (anchoredJetValue μ i Ψ)) :=
    ((anchoredJetValue μ i).continuous.tendsto Ψ).comp hv
  rw [MeasureTheory.Lp.tendsto_Lp_iff_tendsto_eLpNorm']
  -- `B k` is the `L²` distance of the values of the approximations to the limit value.
  have hB := (MeasureTheory.Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mp hg
  -- `A k` is the `L²` norm of the function `fun _ => ε k`.
  set K : ℝ≥0∞ := μ Set.univ ^ (1 / (2 : ℝ≥0∞).toReal) with hK
  have hKtop : K ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) (measure_ne_top μ _)
  have hA : Tendsto (fun k => ‖ε k‖ₑ * K) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k => ‖ε k‖ₑ) atTop (𝓝 0) := by
      have h := (continuous_enorm.tendsto (0 : ℝ)).comp hε0
      simpa [Function.comp_def] using h
    have h2 := ENNReal.Tendsto.mul_const h1 (Or.inr hKtop)
    simpa using h2
  have hsum := hA.add hB
  rw [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun k => zero_le) fun k => ?_
  -- Pointwise: `|F k y − P y| ≤ ε k + |g k y − G y|` almost everywhere.
  have hpt : ∀ᵐ y ∂μ, |(anchoredJetValue μ i (anchoredVectorJet χ μ (truncTest (hε k) (v k))) :
        AnchoredEuclidean n → ℝ) y - (Lp.posPart (anchoredJetValue μ i Ψ) : AnchoredEuclidean n → ℝ) y|
      ≤ ε k + |(anchoredJetValue μ i (anchoredVectorJet χ μ (v k)) : AnchoredEuclidean n → ℝ) y -
        (anchoredJetValue μ i Ψ : AnchoredEuclidean n → ℝ) y| := by
    filter_upwards [anchoredJetValue_truncTest_ae χ μ (hε k) (v k) i,
      anchoredJetValue_ae χ μ (v k) i, Lp.coeFn_posPart (anchoredJetValue μ i Ψ)]
      with y h1 h2 h3
    rw [h1, ← h2, h3]
    calc |smoothPosPart (ε k) ((anchoredJetValue μ i (anchoredVectorJet χ μ (v k)) :
            AnchoredEuclidean n → ℝ) y) - max ((anchoredJetValue μ i Ψ : AnchoredEuclidean n → ℝ) y) 0|
        ≤ |smoothPosPart (ε k) ((anchoredJetValue μ i (anchoredVectorJet χ μ (v k)) :
            AnchoredEuclidean n → ℝ) y) - max ((anchoredJetValue μ i (anchoredVectorJet χ μ (v k)) :
            AnchoredEuclidean n → ℝ) y) 0| + |max ((anchoredJetValue μ i (anchoredVectorJet χ μ (v k)) :
            AnchoredEuclidean n → ℝ) y) 0 - max ((anchoredJetValue μ i Ψ : AnchoredEuclidean n → ℝ) y) 0| :=
          abs_sub_le _ _ _
      _ ≤ ε k + |(anchoredJetValue μ i (anchoredVectorJet χ μ (v k)) : AnchoredEuclidean n → ℝ) y -
            (anchoredJetValue μ i Ψ : AnchoredEuclidean n → ℝ) y| :=
          add_le_add (abs_smoothPosPart_sub_max_le (hε k) _) (abs_max_sub_max_le_abs _ _ _)
  -- The `L²` norm of the difference is at most the norm of the function `ε k` plus the norm of the
  -- difference of the approximations.
  have hmeas : AEStronglyMeasurable
      (⇑(anchoredJetValue μ i (anchoredVectorJet χ μ (v k))) - ⇑(anchoredJetValue μ i Ψ)) μ :=
    ((Lp.aestronglyMeasurable _).sub (Lp.aestronglyMeasurable _))
  calc eLpNorm (⇑(anchoredJetValue μ i (anchoredVectorJet χ μ (truncTest (hε k) (v k)))) -
        ⇑(Lp.posPart (anchoredJetValue μ i Ψ))) 2 μ
      ≤ eLpNorm (fun y => ε k + |(anchoredJetValue μ i (anchoredVectorJet χ μ (v k)) :
          AnchoredEuclidean n → ℝ) y - (anchoredJetValue μ i Ψ : AnchoredEuclidean n → ℝ) y|) 2 μ := by
        refine eLpNorm_mono_ae ((Lp.aestronglyMeasurable _).sub (Lp.aestronglyMeasurable _)) ?_
        filter_upwards [hpt] with y hy
        rw [Real.norm_eq_abs, Real.norm_of_nonneg (add_nonneg (hε k).le (abs_nonneg _))]
        exact hy
    _ ≤ eLpNorm (fun _ : AnchoredEuclidean n => ε k) 2 μ + eLpNorm (fun y =>
          |(anchoredJetValue μ i (anchoredVectorJet χ μ (v k)) : AnchoredEuclidean n → ℝ) y -
            (anchoredJetValue μ i Ψ : AnchoredEuclidean n → ℝ) y|) 2 μ :=
        eLpNorm_add_le one_le_two
    _ = ‖ε k‖ₑ * K + eLpNorm (⇑(anchoredJetValue μ i (anchoredVectorJet χ μ (v k))) -
          ⇑(anchoredJetValue μ i Ψ)) 2 μ := by
        rw [eLpNorm_const' (ε k) two_ne_zero (by simp)]
        congr 1
        have hfun : (fun y => |(anchoredJetValue μ i (anchoredVectorJet χ μ (v k)) :
            AnchoredEuclidean n → ℝ) y - (anchoredJetValue μ i Ψ : AnchoredEuclidean n → ℝ) y|) =
            fun y => ‖(⇑(anchoredJetValue μ i (anchoredVectorJet χ μ (v k))) -
              ⇑(anchoredJetValue μ i Ψ)) y‖ := by
          funext y
          rw [Real.norm_eq_abs]
          rfl
        rw [hfun, eLpNorm_norm _ hmeas]

end Riesz1
