/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.APrioriBoundGradient

/-!
# Inverse energy of the localized cutoff gradient

This is the first inverse-energy estimate in the proof of Lemma 5.2.
The field is the actual Euclidean gradient multiplied
by the cutoff, under the actual tilted anchored law. Its `L²`
membership is concluded. No variance or Sobolev membership is assumed.
-/

public section

noncomputable section

open MeasureTheory Set InnerProductSpace Classical

namespace Riesz1.Internal

/-- Regularity of the literal localized statistic in the anchored
Euclidean coordinates. -/
theorem localizedStatistic_contDiff (n : ℕ) (ℓ : ℝ) (f : ℝ → ℝ)
    (hf : ContDiff ℝ 1 f) (I : Finset (Fin (n + 1))) :
    ContDiff ℝ 1 (fun y : AnchoredEuclidean n =>
      ∑ i ∈ I, f (anchorVector (WithLp.ofLp y) i / ℓ)) := by
  apply ContDiff.sum
  intro i _
  have ha : ContDiff ℝ 1 (fun y : AnchoredEuclidean n => anchorVector (WithLp.ofLp y) i) := by
    induction i using Fin.cases with
    | zero => exact contDiff_const
    | succ j => exact (EuclideanSpace.proj (𝕜 := ℝ) j).contDiff
  exact hf.comp (ha.div_const ℓ)

/-- The exact coordinate comparator inequality, almost everywhere
under the actual tilted law, at every scale. -/
theorem a_priori_cutoff_gradient_bound (P : Parameters) (lam γ ε : ℝ)
    (hlam : 0 ≤ lam) (hγ : 1 < γ) (hε : 0 < ε)
    (hεs : ε ≤ (1 - P.val.2 / 2) / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 1 ≤ n →
      ∀ (θ : ℝ → ℝ) (hθ : IsForcingCutoff θ) (ℓ : ℝ), 0 < ℓ →
      ∀ hK : 1 ≤ ((n : ℝ) + 1) * ℓ,
      ∀ f : ℝ → ℝ, ContDiff ℝ 1 f → Function.Periodic f (1 / ℓ) →
      (∀ u ∈ Icc (-(1 / ℓ / 2)) (1 / ℓ / 2),
        |deriv f u| ≤ cutoffMajorant P.val.2 lam (((n : ℝ) + 1) * ℓ) |u|) →
      let K := ((n : ℝ) + 1) * ℓ
      let χ := nearestTiltedPairs P n.succPNat hθ K γ ε (by linarith)
      let F := fun y : AnchoredEuclidean n =>
        ∑ j ∈ window n.succPNat K γ, f (anchorVector (WithLp.ofLp y) j / ℓ)
      ∀ i : Fin n, ∀ᵐ y ∂anchoredMeasureE χ,
        anchoredCutoff n.succPNat P.val.2 K γ ε (WithLp.ofLp y) * |gradient F y i| ≤
          (C * K ^ ((3 + lam) * ε)) *
            anchoredCutoff n.succPNat P.val.2 K γ ε (WithLp.ofLp y) *
              (((n : ℝ) + 1) * augmentedComparisonWeight n.succPNat K P.val.2 lam ε i.succ) := by
  obtain ⟨C, hC, hb⟩ := a_priori_derivative_on_good P.val.2 lam γ ε
    P.2.2.1 P.2.2.2 hlam hγ hε hεs
  refine ⟨C, hC, ?_⟩
  intro n hn θ hθ ℓ hℓ hK f hf hper hder
  dsimp only
  let K := ((n : ℝ) + 1) * ℓ
  have hK0 : 0 < K := by dsimp [K]; linarith
  let I : Finset (Fin (n + 1)) := window n.succPNat K γ
  let F := fun y : AnchoredEuclidean n =>
    ∑ j ∈ I, f (anchorVector (WithLp.ofLp y) j / ℓ)
  let η := fun y : AnchoredEuclidean n =>
    anchoredCutoff n.succPNat P.val.2 K γ ε (WithLp.ofLp y)
  have hF := localizedStatistic_contDiff n ℓ f hf I
  have hgm : Measurable (gradient F) :=
    ((InnerProductSpace.toDual ℝ (AnchoredEuclidean n)).symm.continuous.comp
      (hF.continuous_fderiv (by norm_num))).measurable
  have hηm : Measurable η :=
    (measurable_anchoredCutoff (N := n.succPNat) P.val.2 K γ ε).comp
      (PiLp.continuous_ofLp 2 (fun _ : Fin n => ℝ)).measurable
  intro i
  have hpred : MeasurableSet {y : AnchoredEuclidean n |
      η y * |gradient F y i| ≤ (C * K ^ ((3 + lam) * ε)) * η y *
        (((n : ℝ) + 1) * augmentedComparisonWeight n.succPNat K P.val.2 lam ε i.succ)} := by
    apply measurableSet_le
    · have hi : Measurable (fun y => gradient F y i) :=
        (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.measurable.comp hgm
      convert hηm.mul hi.norm using 1
    · exact (measurable_const.mul hηm).mul measurable_const
  change ∀ᵐ y ∂anchoredMeasureE (nearestTiltedPairs P n.succPNat hθ K γ ε hK0),
    η y * |gradient F y i| ≤ (C * K ^ ((3 + lam) * ε)) * η y *
      (((n : ℝ) + 1) * augmentedComparisonWeight n.succPNat K P.val.2 lam ε i.succ)
  rw [nearestTiltedPairs_anchoredMeasureE P hn hθ K γ ε hK0]
  change ∀ᵐ y ∂(nearestAnchoredLaw P θ n.succPNat K γ ε).map
    (WithLp.toLp 2 : (Fin n → ℝ) → AnchoredEuclidean n),
    η y * |gradient F y i| ≤ (C * K ^ ((3 + lam) * ε)) * η y *
      (((n : ℝ) + 1) * augmentedComparisonWeight n.succPNat K P.val.2 lam ε i.succ)
  have hm := (PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ)).measurable
  apply (ae_map_iff hm.aemeasurable hpred).mpr
  apply (ae_map_iff (measurable_anchorMap n.succPNat).aemeasurable
    (hpred.preimage hm)).mpr
  apply ae_of_all
  intro X
  let y : AnchoredEuclidean n := WithLp.toLp 2 (anchorMap n.succPNat X)
  change η y * |gradient F y i| ≤ (C * K ^ ((3 + lam) * ε)) * η y *
    (((n : ℝ) + 1) * augmentedComparisonWeight n.succPNat K P.val.2 lam ε i.succ)
  have hηX : η y = goodCutoff n.succPNat P.val.2 K γ ε X := by
    exact anchoredCutoff_anchorMap P.val.2 K γ ε X
  have hη0 : 0 ≤ η y := anchoredCutoff_nonneg _ _ _ _ _
  have hgrad := localizedStatistic_gradient_apply n ℓ f hf I y i
  change gradient F y i = _ at hgrad
  rw [hgrad]
  by_cases hi : i.succ ∈ I
  · rw [ite_eq_left hi]
    by_cases hzero : η y = 0
    · simp only [hzero, zero_mul, mul_zero]
      exact le_rfl
    have hgood : X ∈ goodEvent n.succPNat P.val.2 K γ ε :=
      goodEvent_of_goodCutoff_ne_zero n.succPNat hK0 (hηX ▸ hzero)
    have hi0 : i.succ ≠ (⟨0, n.succPNat.pos⟩ : Fin (n.succPNat : ℕ)) := by
      intro h
      have := congrArg Fin.val h
      simp at this
    have hscale : (((n.succPNat : ℕ) : ℝ) * ℓ) = K := by simp only [K, Nat.succPNat_coe, Nat.cast_succ]
    have hp := hb n.succPNat ℓ hℓ (by simpa only [hscale] using hK)
    rw [hscale] at hp
    have hb' := hp f hper hder X hgood i.succ hi hi0
    have hcoord : y i = X.val i.succ - X.val ⟨0, n.succPNat.pos⟩ := by
      exact congrFun (APrioriComparison.anchorVector_anchorMap n X) i.succ
    rw [hcoord, abs_div, abs_of_pos hℓ]
    have hm := mul_le_mul_of_nonneg_left hb' hη0
    convert hm using 1
    simp only [Nat.succPNat_coe, Nat.cast_succ]
    dsimp only [K]
    ring
  · rw [ite_eq_right hi, abs_zero, mul_zero]
    have hw0 := augmentedComparisonWeight_nonneg (N := n.succPNat)
      (s := P.val.2) (lam := lam) (ε := ε) hK0.le i.succ
    positivity

/-- The localized cutoff gradient is in `L²`, and its actual anchored
inverse energy satisfies the comparison rate. The exponent is chosen
before `ε`. The comparison is given by `Riesz1.a_priori_comparison`. -/
theorem a_priori_localized_gradient_energy (hBE : External.BakryEmery)
    (hPL : External.PrekopaLeindler) (P : Parameters) (lam γ : ℝ)
    (hlam : 0 ≤ lam) (hγ : 1 < γ) :
    ∃ κ ε₀ : ℝ, 0 < κ ∧ 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 1 ≤ n →
      ∀ (θ : ℝ → ℝ) (hθ : IsForcingCutoff θ) (ℓ : ℝ), 0 < ℓ →
      ∀ hK : 1 ≤ ((n : ℝ) + 1) * ℓ,
      ∀ f : ℝ → ℝ, ContDiff ℝ 1 f → Function.Periodic f (1 / ℓ) →
      (∀ u ∈ Icc (-(1 / ℓ / 2)) (1 / ℓ / 2),
        |deriv f u| ≤ cutoffMajorant P.val.2 lam (((n : ℝ) + 1) * ℓ) |u|) →
      let K := ((n : ℝ) + 1) * ℓ
      let χ := nearestTiltedPairs P n.succPNat hθ K γ ε (by linarith)
      let F := fun y : AnchoredEuclidean n =>
        ∑ j ∈ window n.succPNat K γ, f (anchorVector (WithLp.ofLp y) j / ℓ)
      ∃ hv : MemLp (fun y => anchoredCutoff n.succPNat P.val.2 K γ ε (WithLp.ofLp y) • gradient F y)
          2 (anchoredMeasureE χ),
        anchoredInverseEnergy χ
          (hsRieszPairPotentials_curvature_pos n.succPNat P.2.1 (parametersExponent P))
          (hv.toLp (fun y => anchoredCutoff n.succPNat P.val.2 K γ ε (WithLp.ofLp y) • gradient F y)) ≤
            C * K ^ (κ * ε) * (K ^ (2 * lam) + K ^ P.val.2) := by
  obtain ⟨κsum, hκsum, hsum, henergy⟩ := a_priori_comparison hBE hPL P lam γ hlam hγ
  obtain ⟨κ, hκ, hb⟩ := henergy (3 + lam) (by linarith)
  refine ⟨κ, min 1 ((1 - P.val.2 / 2) / 2), hκ,
    lt_min zero_lt_one (by linarith [P.2.2.2]), ?_⟩
  intro ε hε hε0
  have hε1 : ε ≤ 1 := hε0.trans (min_le_left _ _)
  have hεs : ε ≤ (1 - P.val.2 / 2) / 2 := hε0.trans (min_le_right _ _)
  obtain ⟨M, hM, hbound⟩ := a_priori_cutoff_gradient_bound P lam γ ε hlam hγ hε hεs
  obtain ⟨C, hC, hc⟩ := hb ε hε hε1 M hM
  refine ⟨C, hC, ?_⟩
  intro n hn θ hθ ℓ hℓ hK f hf hper hder
  dsimp only
  let K := ((n : ℝ) + 1) * ℓ
  let I : Finset (Fin (n + 1)) := window n.succPNat K γ
  let F := fun y : AnchoredEuclidean n =>
    ∑ j ∈ I, f (anchorVector (WithLp.ofLp y) j / ℓ)
  have hF := localizedStatistic_contDiff n ℓ f hf I
  have hgm : Measurable (gradient F) :=
    ((InnerProductSpace.toDual ℝ (AnchoredEuclidean n)).symm.continuous.comp
      (hF.continuous_fderiv (by norm_num))).measurable
  apply hc n hn θ hθ K hK ((window n.succPNat K γ).erase ⟨0, n.succPNat.pos⟩)
    (Finset.Subset.refl _) (augmentedComparisonWeight n.succPNat K P.val.2 lam ε)
    (Or.inr rfl) (gradient F) hgm
  · intro i
    apply ae_of_all
    intro y hi
    have hgrad := localizedStatistic_gradient_apply n ℓ f hf I y i
    change gradient F y i = _ at hgrad
    rw [hgrad]
    have hnmem : i.succ ∉ I := by
      intro h
      apply hi
      refine Finset.mem_erase.mpr ⟨?_, h⟩
      intro he
      have := congrArg Fin.val he
      simp at this
    exact ite_eq_right hnmem
  · exact hbound n hn θ hθ ℓ hℓ hK f hf hper hder

end Riesz1.Internal

end
