/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.APrioriRotationOriginArc
public import Riesz1.ToMathlib.Moments.LpBounds
public import Riesz1.Variance.APrioriRotationVariance

/-!
# The majorant of the exterior sum seen from the origin

This is part of the `L²` claim in the proof of Lemma 5.2. For a configuration `X`, the exterior sum
`∑_{i ∉ I} f((N y_i - D)/K)` at the origin offset `D ∈ (0, N (x_1 - x_0))` is bounded by the
majorant `originMajorant`, which does not depend on `D` or on `f`. The majorant has finite `L⁴`
norm, uniformly in `N` and `ℓ`, by the tail sums of `APrioriRotationOriginArc`.

The main results are `abs_jointExteriorSum_le_originMajorant` (the pointwise bound) and
`originMajorant_L4` (the uniform `L⁴` bound).
-/

@[expose] public section

open MeasureTheory Finset Set

namespace Riesz1

/-- The joint exterior sum `∑_{i ∉ I} f((N y_i - D)/K)` with `K = N ℓ` and the window `I`,
as a function of the origin offset `D` and the anchored positions `y`. This is used in the
proof of Lemma 5.2. -/
noncomputable def jointExteriorSum (N : ℕ+) (ℓ γ : ℝ) (f : ℝ → ℝ) (D : ℝ)
    (y : Fin (N : ℕ) → ℝ) : ℝ :=
  ∑ i ∈ (window N (((N : ℕ) : ℝ) * ℓ) γ)ᶜ, f ((((N : ℕ) : ℝ) * y i - D) / (((N : ℕ) : ℝ) * ℓ))

/-- The coefficient `α = kernelConst · K^{λ+ε} (2K)^A` of the arc estimate, at scale `K`. -/
noncomputable def originAlpha (s lam ε A K : ℝ) : ℝ :=
  kernelConst s lam ε * K ^ (lam + ε) * (2 * K) ^ A

/-- The coefficient `β = K^{2-s}/(2-s)` of the arc estimate, at scale `K`. -/
noncomputable def originBeta (s K : ℝ) : ℝ := K ^ (2 - s) / (2 - s)

/-- The majorant of the exterior sum seen from the origin: over the exterior labels `i`, the sum
of the four inverse powers of the preceding block `N (x_i - x_1)` (with `i - 1` gaps) and the
following block `N (x_0 + 1 - x_i)` (with `N - i` gaps). -/
noncomputable def originMajorant (N : ℕ+) (ℓ γ s lam ε A : ℝ) (X : Configuration N) : ℝ :=
  ∑ i ∈ (window N (((N : ℕ) : ℝ) * ℓ) γ)ᶜ,
    (originAlpha s lam ε A (((N : ℕ) : ℝ) * ℓ) * blockLength X 1 ((i : ℕ) - 1) ^ (-A) +
      originAlpha s lam ε A (((N : ℕ) : ℝ) * ℓ) *
        blockLength X (i : ℤ) ((N : ℕ) - (i : ℕ)) ^ (-A) +
      originBeta s (((N : ℕ) : ℝ) * ℓ) * blockLength X 1 ((i : ℕ) - 1) ^ (-(2 - s)) +
      originBeta s (((N : ℕ) : ℝ) * ℓ) *
        blockLength X (i : ℤ) ((N : ℕ) - (i : ℕ)) ^ (-(2 - s)))

/-- A block length is nonnegative: it is a sum of positive gaps. -/
theorem blockLength_nonneg {N : ℕ+} (X : Configuration N) (j : ℤ) (L : ℕ) :
    0 ≤ blockLength X j L := by
  rw [blockLength_eq_sum]
  exact Finset.sum_nonneg fun r _ => (gap_pos X (j + r)).le

/-- The majorant is nonnegative on every configuration. -/
theorem originMajorant_nonneg {N : ℕ+} (ℓ γ s lam ε A : ℝ) (hα : 0 ≤ originAlpha s lam ε A
    (((N : ℕ) : ℝ) * ℓ)) (hβ : 0 ≤ originBeta s (((N : ℕ) : ℝ) * ℓ)) (X : Configuration N) :
    0 ≤ originMajorant N ℓ γ s lam ε A X := by
  unfold originMajorant
  refine Finset.sum_nonneg fun i _ => ?_
  have hP := blockLength_nonneg X 1 ((i : ℕ) - 1)
  have hR := blockLength_nonneg X (i : ℤ) ((N : ℕ) - (i : ℕ))
  have := mul_nonneg hα (Real.rpow_nonneg hP (-A))
  have := mul_nonneg hα (Real.rpow_nonneg hR (-A))
  have := mul_nonneg hβ (Real.rpow_nonneg hP (-(2 - s)))
  have := mul_nonneg hβ (Real.rpow_nonneg hR (-(2 - s)))
  linarith

/-- **Pointwise bound.** For a configuration `X` and an origin offset `0 < D < gap X 0`, the joint
exterior sum at the anchored configuration `rotAnchorVec N X` is bounded in absolute value by the
majorant. The bound uses `γ ≥ 0`, so that the window has `J = ⌊K^γ⌋₊ ≥ 1` labels on each side. -/
theorem abs_jointExteriorSum_le_originMajorant {N : ℕ+} (X : Configuration N) {ℓ γ s lam ε A : ℝ}
    (hℓ : 0 < ℓ) (hs : s < 2) (hK : 1 ≤ ((N : ℕ) : ℝ) * ℓ) (hγ : 0 ≤ γ) (hlam : 0 ≤ lam)
    (hε : 0 < ε) (hA : 0 ≤ A) {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hper : Function.Periodic f (1 / ℓ)) (hzero : f (1 / ℓ / 2) = 0)
    (hder : ∀ u ∈ Icc (-(1 / ℓ / 2)) (1 / ℓ / 2),
      |deriv f u| ≤ cutoffMajorant s lam (((N : ℕ) : ℝ) * ℓ) |u|)
    {D : ℝ} (hD0 : 0 < D) (hD1 : D < gap X 0) :
    |jointExteriorSum N ℓ γ f D (rotAnchorVec N X)| ≤ originMajorant N ℓ γ s lam ε A X := by
  unfold jointExteriorSum originMajorant
  have hgap : gap X 0 = blockLength X 0 1 := by simp [gap, blockLength]
  rw [hgap] at hD1
  have hJ1 : 1 ≤ ⌊(((N : ℕ) : ℝ) * ℓ) ^ γ⌋₊ :=
    Nat.le_floor (by rw [Nat.cast_one]; exact Real.one_le_rpow hK hγ)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  obtain ⟨h1, h2⟩ := exterior_label_bounds hK hi
  exact abs_arc_origin (i := (i : ℕ)) X hℓ hs hK hlam hε hA rfl rfl hf hper hzero hder (by omega)
    (by omega)
    hD0 hD1

/-- **Uniform `L⁴` bound of the majorant.** Let `P` be the model parameters, `λ, ε ≥ 0`… more
precisely `λ ≥ 0`, `ε > 0`, and let `γ ≥ (2-s)/(1-s)`. There is `M ≥ 0`, depending only on
`P, λ, ε, γ`, such that for every `N ≥ 2` and `0 < ℓ ≤ 1` with `K = Nℓ ≥ 1`, the majorant has
`∫ |originMajorant|^4 dGi ≤ M^4`. -/
theorem originMajorant_L4 (P : Parameters) (hPL : External.PrekopaLeindler) {lam ε : ℝ}
    (hlam : 0 ≤ lam) (hε : 0 < ε) {γ : ℝ} (hγ : (2 - P.val.2) / (1 - P.val.2) ≤ γ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (N : ℕ+) (ℓ : ℝ), 2 ≤ (N : ℕ) → 0 < ℓ → ℓ ≤ 1 →
      1 ≤ ((N : ℕ) : ℝ) * ℓ →
      ∫⁻ X, ENNReal.ofReal (|originMajorant N ℓ γ P.val.2 lam ε
        ((lam + ε + γ) / (γ - 1) + 2) X| ^ 4) ∂(gibbsMeasure P N) ≤ ENNReal.ofReal (M ^ 4) := by
  have hs0 : 0 < P.val.2 := P.property.2.1
  have hs1 : P.val.2 < 1 := P.property.2.2
  set s := P.val.2 with hs_def
  have hs2 : s < 2 := by linarith
  have hγ0 : 1 < (2 - s) / (1 - s) := by
    rw [lt_div_iff₀ (by linarith)]
    linarith
  have hγ1 : 1 < γ := lt_of_lt_of_le hγ0 hγ
  have hexp2 : 2 - s ≤ γ * (1 - s) := by
    have h := (div_le_iff₀ (by linarith : (0 : ℝ) < 1 - s)).1 hγ
    linarith
  set A : ℝ := (lam + ε + γ) / (γ - 1) + 2 with hA_def
  have hγ1' : 0 < γ - 1 := by linarith
  have hA1 : 1 < A := by
    have h0 : 0 ≤ (lam + ε + γ) / (γ - 1) := div_nonneg (by linarith) hγ1'.le
    rw [hA_def]
    linarith
  have hexpA : lam + ε + γ ≤ A * (γ - 1) := by
    rw [hA_def, add_mul, div_mul_cancel₀ _ hγ1'.ne']
    linarith
  have hA0 : 0 < A := by linarith
  obtain ⟨C₁, hC₁, hmom₁⟩ := exists_eLpNorm_blockLength_rpow_neg_le P hPL (q := A)
    (p := ((4 : ℕ) : ℝ)) hA0 (by norm_num)
  obtain ⟨C₂, hC₂, hmom₂⟩ := exists_eLpNorm_blockLength_rpow_neg_le P hPL (q := 2 - s)
    (p := ((4 : ℕ) : ℝ)) (by linarith) (by norm_num)
  set C₁' : ℝ := C₁ ^ (1 / ((4 : ℕ) : ℝ)) with hC₁'
  set C₂' : ℝ := C₂ ^ (1 / ((4 : ℕ) : ℝ)) with hC₂'
  have hC₁'0 : 0 ≤ C₁' := Real.rpow_nonneg hC₁ _
  have hC₂'0 : 0 ≤ C₂' := Real.rpow_nonneg hC₂ _
  have hkc : 0 ≤ kernelConst s lam ε := kernelConst_nonneg hs2 hlam hε
  set M₀ : ℝ := C₁' * (kernelConst s lam ε * 2 ^ (2 * A - 1)) * (2 ^ A + 1) / (A - 1) +
    C₂' * (2 ^ (1 - s) / (2 - s)) * (2 ^ (2 - s) + 1) / (1 - s) with hM₀
  have hM₀0 : 0 ≤ M₀ := by
    have h1 : 0 ≤ C₁' * (kernelConst s lam ε * 2 ^ (2 * A - 1)) * (2 ^ A + 1) / (A - 1) :=
      div_nonneg (mul_nonneg (mul_nonneg hC₁'0 (mul_nonneg hkc (by positivity))) (by positivity))
        (by linarith)
    have h2 : 0 ≤ C₂' * (2 ^ (1 - s) / (2 - s)) * (2 ^ (2 - s) + 1) / (1 - s) :=
      div_nonneg (mul_nonneg (mul_nonneg hC₂'0 (by positivity)) (by positivity)) (by linarith)
    rw [hM₀]
    linarith
  refine ⟨M₀, hM₀0, fun N ℓ hN hℓ0 hℓ1 hK => ?_⟩
  have hN0 : (0 : ℝ) < ((N : ℕ) : ℝ) := by exact_mod_cast N.pos
  set K : ℝ := ((N : ℕ) : ℝ) * ℓ with hK_def
  have hK0 : 0 < K := by linarith
  have hKγ1 : 1 ≤ K ^ γ := Real.one_le_rpow hK (by linarith)
  set J : ℕ := ⌊K ^ γ⌋₊ with hJ_def
  have hJ1 : 1 ≤ J := Nat.le_floor (by rw [Nat.cast_one]; exact hKγ1)
  have hJ1r : (1 : ℝ) ≤ J := by exact_mod_cast hJ1
  have hJhalf : K ^ γ / 2 ≤ (J : ℝ) := by
    have h := Nat.lt_floor_add_one (K ^ γ)
    rw [← hJ_def] at h
    linarith
  have hα0 : 0 ≤ originAlpha s lam ε A K := by
    unfold originAlpha
    exact mul_nonneg (mul_nonneg hkc (Real.rpow_nonneg hK0.le _)) (Real.rpow_nonneg (by linarith) _)
  have hβ0 : 0 ≤ originBeta s K := by
    unfold originBeta
    exact div_nonneg (Real.rpow_nonneg hK0.le _) (by linarith)
  have hext : ∀ i ∈ (window N K γ)ᶜ, J < (i : ℕ) ∧ J < (N : ℕ) - (i : ℕ) :=
    fun i hi => exterior_label_bounds hK hi
  set E : Finset (Fin (N : ℕ)) := (window N K γ)ᶜ with hE_def
  -- Measurability of the majorant.
  have hmeasB : ∀ (j : ℤ) (L : ℕ) (c a : ℝ),
      Measurable (fun X : Configuration N => c * blockLength X j L ^ a) := fun j L c a =>
    ((measurable_blockLength j L).pow_const a).const_mul c
  have hQmeas : Measurable (fun X : Configuration N => originMajorant N ℓ γ s lam ε A X) := by
    unfold originMajorant
    refine Finset.measurable_sum _ fun i _ => ?_
    exact (((hmeasB _ _ _ _).add (hmeasB _ _ _ _)).add (hmeasB _ _ _ _)).add (hmeasB _ _ _ _)
  have hQnn : ∀ X : Configuration N, 0 ≤ originMajorant N ℓ γ s lam ε A X :=
    fun X => originMajorant_nonneg ℓ γ s lam ε A hα0 hβ0 X
  -- The four families, and the four-term bound per label.
  have hpt : ∀ X : Configuration N,
      |originMajorant N ℓ γ s lam ε A X| ≤ ∑ i ∈ E,
        (originAlpha s lam ε A K * blockLength X 1 ((i : ℕ) - 1) ^ (-A) +
          originAlpha s lam ε A K * blockLength X (i : ℤ) ((N : ℕ) - (i : ℕ)) ^ (-A) +
          originBeta s K * blockLength X 1 ((i : ℕ) - 1) ^ (-(2 - s)) +
          originBeta s K * blockLength X (i : ℤ) ((N : ℕ) - (i : ℕ)) ^ (-(2 - s))) := by
    intro X
    rw [abs_of_nonneg (hQnn X)]
    rfl
  -- The real bound on each label.
  set bt : Fin (N : ℕ) → ℝ := fun i =>
    originAlpha s lam ε A K * C₁' * ((((i : ℕ) - 1 : ℕ)) : ℝ) ^ (-A) +
      originAlpha s lam ε A K * C₁' * (((N : ℕ) - (i : ℕ) : ℕ) : ℝ) ^ (-A) +
      originBeta s K * C₂' * ((((i : ℕ) - 1 : ℕ)) : ℝ) ^ (-(2 - s)) +
      originBeta s K * C₂' * (((N : ℕ) - (i : ℕ) : ℕ) : ℝ) ^ (-(2 - s)) with hbt
  have hbt0 : ∀ i : Fin (N : ℕ), 0 ≤ bt i := by
    intro i
    simp only [hbt]
    have hn1 : 0 ≤ originAlpha s lam ε A K * C₁' * ((((i : ℕ) - 1 : ℕ)) : ℝ) ^ (-A) :=
      mul_nonneg (mul_nonneg hα0 hC₁'0) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    have hn2 : 0 ≤ originAlpha s lam ε A K * C₁' * (((N : ℕ) - (i : ℕ) : ℕ) : ℝ) ^ (-A) :=
      mul_nonneg (mul_nonneg hα0 hC₁'0) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    have hn3 : 0 ≤ originBeta s K * C₂' * ((((i : ℕ) - 1 : ℕ)) : ℝ) ^ (-(2 - s)) :=
      mul_nonneg (mul_nonneg hβ0 hC₂'0) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    have hn4 : 0 ≤ originBeta s K * C₂' * (((N : ℕ) - (i : ℕ) : ℕ) : ℝ) ^ (-(2 - s)) :=
      mul_nonneg (mul_nonneg hβ0 hC₂'0) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    linarith
  have hlabel : ∀ i ∈ E, eLpNorm (fun X : Configuration N =>
          originAlpha s lam ε A K * blockLength X 1 ((i : ℕ) - 1) ^ (-A))
        (ENNReal.ofReal ((4 : ℕ) : ℝ)) (gibbsMeasure P N) +
      eLpNorm (fun X : Configuration N =>
          originAlpha s lam ε A K * blockLength X (i : ℤ) ((N : ℕ) - (i : ℕ)) ^ (-A))
        (ENNReal.ofReal ((4 : ℕ) : ℝ)) (gibbsMeasure P N) +
      eLpNorm (fun X : Configuration N =>
          originBeta s K * blockLength X 1 ((i : ℕ) - 1) ^ (-(2 - s)))
        (ENNReal.ofReal ((4 : ℕ) : ℝ)) (gibbsMeasure P N) +
      eLpNorm (fun X : Configuration N =>
          originBeta s K * blockLength X (i : ℤ) ((N : ℕ) - (i : ℕ)) ^ (-(2 - s)))
        (ENNReal.ofReal ((4 : ℕ) : ℝ)) (gibbsMeasure P N) ≤ ENNReal.ofReal (bt i) := by
    intro i hi
    obtain ⟨hi1, hi2⟩ := hext i hi
    have hL1 : 0 < (i : ℕ) - 1 := by omega
    have hL2 : 0 < (N : ℕ) - (i : ℕ) := by omega
    have e1 := hmom₁ N 1 ((i : ℕ) - 1) hL1 (originAlpha s lam ε A K) hα0
    have e2 := hmom₁ N (i : ℤ) ((N : ℕ) - (i : ℕ)) hL2 (originAlpha s lam ε A K) hα0
    have e3 := hmom₂ N 1 ((i : ℕ) - 1) hL1 (originBeta s K) hβ0
    have e4 := hmom₂ N (i : ℤ) ((N : ℕ) - (i : ℕ)) hL2 (originBeta s K) hβ0
    have hn1 : 0 ≤ originAlpha s lam ε A K * C₁' * ((((i : ℕ) - 1 : ℕ)) : ℝ) ^ (-A) :=
      mul_nonneg (mul_nonneg hα0 hC₁'0) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    have hn2 : 0 ≤ originAlpha s lam ε A K * C₁' * (((N : ℕ) - (i : ℕ) : ℕ) : ℝ) ^ (-A) :=
      mul_nonneg (mul_nonneg hα0 hC₁'0) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    have hn3 : 0 ≤ originBeta s K * C₂' * ((((i : ℕ) - 1 : ℕ)) : ℝ) ^ (-(2 - s)) :=
      mul_nonneg (mul_nonneg hβ0 hC₂'0) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    have hn4 : 0 ≤ originBeta s K * C₂' * (((N : ℕ) - (i : ℕ) : ℕ) : ℝ) ^ (-(2 - s)) :=
      mul_nonneg (mul_nonneg hβ0 hC₂'0) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    simp only [hbt]
    rw [ENNReal.ofReal_add (add_nonneg (add_nonneg hn1 hn2) hn3) hn4,
      ENNReal.ofReal_add (add_nonneg hn1 hn2) hn3, ENNReal.ofReal_add hn1 hn2]
    exact add_le_add (add_le_add (add_le_add e1 e2) e3) e4
  -- The sum of the bounds over the exterior labels.
  have hbM : ∑ i ∈ E, bt i ≤ M₀ := by
    have hsplit : ∑ i ∈ E, bt i =
        ∑ i ∈ E, (originAlpha s lam ε A K * C₁' * ((((i : ℕ) - 1 : ℕ)) : ℝ) ^ (-A) +
          originAlpha s lam ε A K * C₁' * (((N : ℕ) - (i : ℕ) : ℕ) : ℝ) ^ (-A)) +
        ∑ i ∈ E, (originBeta s K * C₂' * ((((i : ℕ) - 1 : ℕ)) : ℝ) ^ (-(2 - s)) +
          originBeta s K * C₂' * (((N : ℕ) - (i : ℕ) : ℕ) : ℝ) ^ (-(2 - s))) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by simp only [hbt]; ring
    have hA_part := sum_pair_rpow_le hA1 (mul_nonneg hα0 hC₁'0) hJ1 E hext
    have hB_part := sum_pair_rpow_le (a := 2 - s) (by linarith) (mul_nonneg hβ0 hC₂'0) hJ1 E hext
    have hTA : originAlpha s lam ε A K * C₁' * (2 ^ A + 1) * ((J : ℝ) ^ (1 - A) / (A - 1)) ≤
        C₁' * (kernelConst s lam ε * 2 ^ (2 * A - 1)) * (2 ^ A + 1) / (A - 1) := by
      have hT := tail_const_A hK hγ1 hlam hA1 hexpA hJhalf
      have hαJ : originAlpha s lam ε A K * (J : ℝ) ^ (1 - A) ≤
          kernelConst s lam ε * 2 ^ (2 * A - 1) := by
        unfold originAlpha
        calc kernelConst s lam ε * K ^ (lam + ε) * (2 * K) ^ A * (J : ℝ) ^ (1 - A)
            = kernelConst s lam ε * (K ^ (lam + ε) * (2 * K) ^ A * (J : ℝ) ^ (1 - A)) := by ring
          _ ≤ kernelConst s lam ε * 2 ^ (2 * A - 1) := mul_le_mul_of_nonneg_left hT hkc
      calc originAlpha s lam ε A K * C₁' * (2 ^ A + 1) * ((J : ℝ) ^ (1 - A) / (A - 1))
          = C₁' * (2 ^ A + 1) / (A - 1) * (originAlpha s lam ε A K * (J : ℝ) ^ (1 - A)) := by
            ring
        _ ≤ C₁' * (2 ^ A + 1) / (A - 1) * (kernelConst s lam ε * 2 ^ (2 * A - 1)) :=
            mul_le_mul_of_nonneg_left hαJ (div_nonneg (mul_nonneg hC₁'0 (by positivity))
              (by linarith))
        _ = C₁' * (kernelConst s lam ε * 2 ^ (2 * A - 1)) * (2 ^ A + 1) / (A - 1) := by ring
    have hTB : originBeta s K * C₂' * (2 ^ (2 - s) + 1) *
        ((J : ℝ) ^ (1 - (2 - s)) / (2 - s - 1)) ≤
        C₂' * (2 ^ (1 - s) / (2 - s)) * (2 ^ (2 - s) + 1) / (1 - s) := by
      have hT := tail_const_B hK (by linarith : (0 : ℝ) ≤ γ) hs1 hexp2 hJhalf
      have e1 : (1 : ℝ) - (2 - s) = s - 1 := by ring
      have e2 : (2 : ℝ) - s - 1 = 1 - s := by ring
      rw [e1, e2]
      have hβJ : originBeta s K * (J : ℝ) ^ (s - 1) ≤ 2 ^ (1 - s) / (2 - s) := by
        unfold originBeta
        calc K ^ (2 - s) / (2 - s) * (J : ℝ) ^ (s - 1)
            = (K ^ (2 - s) * (J : ℝ) ^ (s - 1)) / (2 - s) := by ring
          _ ≤ 2 ^ (1 - s) / (2 - s) := div_le_div_of_nonneg_right hT (by linarith)
      calc originBeta s K * C₂' * (2 ^ (2 - s) + 1) * ((J : ℝ) ^ (s - 1) / (1 - s))
          = C₂' * (2 ^ (2 - s) + 1) / (1 - s) * (originBeta s K * (J : ℝ) ^ (s - 1)) := by
            ring
        _ ≤ C₂' * (2 ^ (2 - s) + 1) / (1 - s) * (2 ^ (1 - s) / (2 - s)) :=
            mul_le_mul_of_nonneg_left hβJ (div_nonneg (mul_nonneg hC₂'0 (by positivity))
              (by linarith))
        _ = C₂' * (2 ^ (1 - s) / (2 - s)) * (2 ^ (2 - s) + 1) / (1 - s) := by ring
    rw [hsplit]
    calc _ ≤ originAlpha s lam ε A K * C₁' * (2 ^ A + 1) * ((J : ℝ) ^ (1 - A) / (A - 1)) +
          originBeta s K * C₂' * (2 ^ (2 - s) + 1) *
            ((J : ℝ) ^ (1 - (2 - s)) / (2 - s - 1)) := add_le_add hA_part hB_part
      _ ≤ M₀ := by rw [hM₀]; exact add_le_add hTA hTB
  -- The `L⁴` norm of the majorant.
  have hsum : eLpNorm (fun X : Configuration N => originMajorant N ℓ γ s lam ε A X)
      (ENNReal.ofReal ((4 : ℕ) : ℝ)) (gibbsMeasure P N) ≤ ENNReal.ofReal M₀ := by
    calc eLpNorm (fun X : Configuration N => originMajorant N ℓ γ s lam ε A X)
          (ENNReal.ofReal ((4 : ℕ) : ℝ)) (gibbsMeasure P N)
        ≤ ∑ i ∈ E, (eLpNorm (fun X : Configuration N =>
          originAlpha s lam ε A K * blockLength X 1 ((i : ℕ) - 1) ^ (-A))
            (ENNReal.ofReal ((4 : ℕ) : ℝ)) (gibbsMeasure P N) +
          eLpNorm (fun X : Configuration N =>
            originAlpha s lam ε A K * blockLength X (i : ℤ) ((N : ℕ) - (i : ℕ)) ^ (-A))
            (ENNReal.ofReal ((4 : ℕ) : ℝ)) (gibbsMeasure P N) +
          eLpNorm (fun X : Configuration N =>
            originBeta s K * blockLength X 1 ((i : ℕ) - 1) ^ (-(2 - s)))
            (ENNReal.ofReal ((4 : ℕ) : ℝ)) (gibbsMeasure P N) +
          eLpNorm (fun X : Configuration N =>
            originBeta s K * blockLength X (i : ℤ) ((N : ℕ) - (i : ℕ)) ^ (-(2 - s)))
            (ENNReal.ofReal ((4 : ℕ) : ℝ)) (gibbsMeasure P N)) :=
          eLpNorm_le_sum_four (gibbsMeasure P N) (ENNReal.one_le_ofReal.2 (by norm_num)) E hQmeas
            (fun i X => originAlpha s lam ε A K * blockLength X 1 ((i : ℕ) - 1) ^ (-A))
            (fun i X => originAlpha s lam ε A K * blockLength X (i : ℤ) ((N : ℕ) - (i : ℕ)) ^ (-A))
            (fun i X => originBeta s K * blockLength X 1 ((i : ℕ) - 1) ^ (-(2 - s)))
            (fun i X => originBeta s K * blockLength X (i : ℤ) ((N : ℕ) - (i : ℕ)) ^ (-(2 - s)))
            hpt
      _ ≤ ∑ i ∈ E, ENNReal.ofReal (bt i) := Finset.sum_le_sum fun i hi => hlabel i hi
      _ = ENNReal.ofReal (∑ i ∈ E, bt i) :=
          (ENNReal.ofReal_sum_of_nonneg fun i _ => hbt0 i).symm
      _ ≤ ENNReal.ofReal M₀ := ENNReal.ofReal_le_ofReal hbM
  exact lintegral_pow_le_of_eLpNorm_le hQmeas (m := 4) (by norm_num) hM₀0 hsum

/-- The majorant is measurable on the configuration space. -/
theorem measurable_originMajorant (N : ℕ+) (ℓ γ s lam ε A : ℝ) :
    Measurable (fun X : Configuration N => originMajorant N ℓ γ s lam ε A X) := by
  unfold originMajorant
  have hmeasB : ∀ (j : ℤ) (L : ℕ) (c a : ℝ),
      Measurable (fun X : Configuration N => c * blockLength X j L ^ a) := fun j L c a =>
    ((measurable_blockLength j L).pow_const a).const_mul c
  refine Finset.measurable_sum _ fun i _ => ?_
  exact (((hmeasB _ _ _ _).add (hmeasB _ _ _ _)).add (hmeasB _ _ _ _)).add (hmeasB _ _ _ _)

end Riesz1

end
