/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.APrioriRotationExterior

/-!
# The exterior tail bound

Part of Lemma 5.2 (the rotation part), first claim. For `γ` large depending on `s, λ, p`, the
exterior sum `E_γ` of `exteriorSum` has `L^p(dGi)` norm at most a constant `C`, uniformly in the
number of particles `N`, the scale `ℓ` and the kernel `f` satisfying the normalized derivative
bound. The constant depends on `P, λ, ε, p, γ` only.
-/

@[expose] public section

open MeasureTheory Finset Set

namespace Riesz1

/-- **Exterior tail with explicit threshold** (part of Lemma 5.2, the rotation part, first claim).
Let `P` be the model parameters, with exponent `s = P.val.2`, let `λ ≥ 0`, `ε > 0` and `p ≥ 2`.
For every `γ ≥ (2 - s)/(1 - s)`, there is `C` with: for every `N ≥ 2`, `0 < ℓ ≤ 1` with
`K = Nℓ ≥ 1`, and every `C¹` function `f` of period `1/ℓ` with `f(1/(2ℓ)) = 0` satisfying the
derivative bound of the kernel, the exterior sum has `L^p` norm at most `C`. -/
theorem exterior_tail_eLpNorm_le_of_ge (P : Parameters) (hPL : External.PrekopaLeindler)
    {lam ε p : ℝ} (hlam : 0 ≤ lam) (hε : 0 < ε) (hp : 2 ≤ p) (γ : ℝ)
    (hγ : (2 - P.val.2) / (1 - P.val.2) ≤ γ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (N : ℕ+) (ℓ : ℝ), 2 ≤ (N : ℕ) → 0 < ℓ → ℓ ≤ 1 → 1 ≤ ((N : ℕ) : ℝ) * ℓ →
        ∀ f : ℝ → ℝ, ContDiff ℝ 1 f → Function.Periodic f (1 / ℓ) → f (1 / ℓ / 2) = 0 →
        (∀ u ∈ Icc (-(1 / ℓ / 2)) (1 / ℓ / 2),
          |deriv f u| ≤ (if |u| ≤ 2 then 1 / (max |u| (((N : ℕ) : ℝ) * ℓ)⁻¹) ^ (1 + lam) else 0) +
            (if 2 ≤ |u| then 1 / |u| ^ (3 - P.val.2) else 0)) →
        eLpNorm (exteriorSum N ℓ γ f) (ENNReal.ofReal p) (gibbsMeasure P N) ≤
          ENNReal.ofReal C := by
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
  obtain ⟨C₁, hC₁, hmom₁⟩ := exists_eLpNorm_blockLength_rpow_neg_le P hPL (q := A) (p := p)
    hA0 (by linarith)
  obtain ⟨C₂, hC₂, hmom₂⟩ := exists_eLpNorm_blockLength_rpow_neg_le P hPL (q := 2 - s) (p := p)
    (by linarith) (by linarith)
  have hC₁p : 0 ≤ C₁ ^ (1 / p) := Real.rpow_nonneg hC₁ _
  have hC₂p : 0 ≤ C₂ ^ (1 / p) := Real.rpow_nonneg hC₂ _
  refine ⟨2 * C₁ ^ (1 / p) * kernelConst s lam ε * 2 ^ (2 * A - 1) / (A - 1) +
      2 * C₂ ^ (1 / p) * 2 ^ (1 - s) / ((2 - s) * (1 - s)), ?_,
    fun N ℓ hN hℓ0 hℓ1 hK f hf hper hzero hder => ?_⟩
  · have h1 : 0 ≤ 2 * C₁ ^ (1 / p) * kernelConst s lam ε * 2 ^ (2 * A - 1) / (A - 1) :=
      div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg two_pos.le hC₁p)
        (kernelConst_nonneg hs2 hlam hε)) (by positivity)) (by linarith)
    have h2 : 0 ≤ 2 * C₂ ^ (1 / p) * 2 ^ (1 - s) / ((2 - s) * (1 - s)) :=
      div_nonneg (mul_nonneg (mul_nonneg two_pos.le hC₂p) (by positivity))
        (mul_nonneg (by linarith) (by linarith))
    linarith
  -- Notation: the window scale `K = Nℓ`, the integer `J = ⌊K^γ⌋`, and the constants.
  unfold exteriorSum
  set K : ℝ := ((N : ℕ) : ℝ) * ℓ with hK_def
  have hN0 : (0 : ℝ) < ((N : ℕ) : ℝ) := by exact_mod_cast N.pos
  have hK0 : 0 < K := mul_pos hN0 hℓ0
  have hL0 : 0 < 1 / ℓ := one_div_pos.mpr hℓ0
  have hKγ1 : 1 ≤ K ^ γ := Real.one_le_rpow hK (by linarith)
  set J : ℕ := ⌊K ^ γ⌋₊ with hJ_def
  have hJ1 : 1 ≤ J := Nat.le_floor (by rw [Nat.cast_one]; exact hKγ1)
  have hJ1r : (1 : ℝ) ≤ J := by exact_mod_cast hJ1
  have hJhalf : K ^ γ / 2 ≤ (J : ℝ) := by
    have h := Nat.lt_floor_add_one (K ^ γ)
    rw [← hJ_def] at h
    linarith
  obtain ⟨α, hα⟩ : ∃ α : ℝ, α = kernelConst s lam ε * K ^ (lam + ε) * (2 * K) ^ A :=
    ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β : ℝ, β = K ^ (2 - s) / (2 - s) := ⟨_, rfl⟩
  have hα0 : 0 ≤ α := by
    rw [hα]
    exact mul_nonneg (mul_nonneg (kernelConst_nonneg hs2 hlam hε)
      (Real.rpow_nonneg hK0.le _)) (Real.rpow_nonneg (by linarith) _)
  have hβ0 : 0 ≤ β := by
    rw [hβ]
    exact div_nonneg (Real.rpow_nonneg hK0.le _) (by linarith)
  -- Exterior labels: both arcs from the origin label exceed `J`.
  have hext : ∀ i ∈ (window N K γ)ᶜ, J < (i : ℕ) ∧ J < (N : ℕ) - (i : ℕ) := by
    intro i hi
    have hi' : i ∉ window N K γ := Finset.mem_compl.1 hi
    have hd := labelDist_gt_of_not_mem_window (K := K) (γ := γ) hi'
    rw [labelDistToOne_eq] at hd
    have hJd : (J : ℝ) ≤ K ^ γ := by
      rw [hJ_def]
      exact Nat.floor_le (Real.rpow_nonneg hK0.le _)
    have hlt : (J : ℝ) < ((min (i : ℕ) ((N : ℕ) - (i : ℕ)) : ℕ) : ℝ) := lt_of_le_of_lt hJd hd
    have hlt' : J < min (i : ℕ) ((N : ℕ) - (i : ℕ)) := by exact_mod_cast hlt
    exact lt_min_iff.1 hlt'
  have hder' : ∀ u ∈ Icc (-(1 / ℓ / 2)) (1 / ℓ / 2), |deriv f u| ≤ cutoffMajorant s lam K |u| :=
    fun u hu => hder u hu
  -- Pointwise bound of each exterior term by inverse powers of the two arcs.
  have hpt : ∀ (X : Configuration N) (i : Fin (N : ℕ)), i ∈ (window N K γ)ᶜ →
      |f ((cyclicLift X (i : ℕ) - cyclicLift X 0) / ℓ)| ≤
        α * blockLength X 0 (i : ℕ) ^ (-A) +
        α * blockLength X ((i : ℕ) : ℤ) ((N : ℕ) - (i : ℕ)) ^ (-A) +
        β * blockLength X 0 (i : ℕ) ^ (-(2 - s)) +
        β * blockLength X ((i : ℕ) : ℤ) ((N : ℕ) - (i : ℕ)) ^ (-(2 - s)) := by
    intro X i hi
    have hiext := hext i hi
    have hi_lt := i.isLt
    have hm1 : 0 < (i : ℕ) := by omega
    have hNm : 0 < (N : ℕ) - (i : ℕ) := by omega
    have hF : 0 < blockLength X 0 (i : ℕ) := blockLength_pos X 0 hm1
    have hG : 0 < blockLength X ((i : ℕ) : ℤ) ((N : ℕ) - (i : ℕ)) :=
      blockLength_pos X _ hNm
    have hFid : blockLength X 0 (i : ℕ) =
        ((N : ℕ) : ℝ) * (cyclicLift X (i : ℕ) - cyclicLift X 0) := by
      unfold blockLength
      simp
    have hcN : cyclicLift X ((N : ℕ) : ℤ) = cyclicLift X 0 + 1 := by
      have h := cyclicLift_add_N X 0
      rwa [zero_add] at h
    have hGid : blockLength X ((i : ℕ) : ℤ) ((N : ℕ) - (i : ℕ)) =
        ((N : ℕ) : ℝ) * (cyclicLift X 0 + 1 - cyclicLift X (i : ℕ)) := by
      unfold blockLength
      have h1 : ((i : ℕ) : ℤ) + (((N : ℕ) - (i : ℕ) : ℕ) : ℤ) = ((N : ℕ) : ℤ) := by omega
      rw [h1, hcN]
    have hN_ne : ((N : ℕ) : ℝ) ≠ 0 := hN0.ne'
    have hx : (cyclicLift X (i : ℕ) - cyclicLift X 0) / ℓ = blockLength X 0 (i : ℕ) / K := by
      rw [hFid, hK_def]
      field_simp
    have hLx : 1 / ℓ - (cyclicLift X (i : ℕ) - cyclicLift X 0) / ℓ =
        blockLength X ((i : ℕ) : ℤ) ((N : ℕ) - (i : ℕ)) / K := by
      rw [hGid, hK_def]
      field_simp
      ring
    have hxpos : 0 < (cyclicLift X (i : ℕ) - cyclicLift X 0) / ℓ := by
      rw [hx]
      exact div_pos hF hK0
    have hxlt : (cyclicLift X (i : ℕ) - cyclicLift X 0) / ℓ < 1 / ℓ := by
      have : 0 < blockLength X ((i : ℕ) : ℤ) ((N : ℕ) - (i : ℕ)) / K := div_pos hG hK0
      linarith
    have key := abs_le_blocks hL0 hs2 hK hlam hε hA0.le hf hper hzero hder' hxpos hxlt hF hG hx
      hLx
    rw [hα, hβ]
    calc _ ≤ _ := key
      _ = _ := by ring
  -- Summation over the exterior labels, with the `L^p` bound for each of the four families.
  set E := (window N K γ)ᶜ with hE_def
  have hEmeas : Measurable (fun X : Configuration N =>
      ∑ i ∈ E, f ((cyclicLift X (i : ℕ) - cyclicLift X 0) / ℓ)) := by
    refine Finset.measurable_sum _ fun i _ => ?_
    exact hf.continuous.measurable.comp
      (((measurable_cyclicLift _).sub (measurable_cyclicLift _)).div_const ℓ)
  have hsumpt : ∀ X : Configuration N,
      |∑ i ∈ E, f ((cyclicLift X (i : ℕ) - cyclicLift X 0) / ℓ)| ≤
        ∑ i ∈ E, (α * blockLength X 0 (i : ℕ) ^ (-A) +
          α * blockLength X ((i : ℕ) : ℤ) ((N : ℕ) - (i : ℕ)) ^ (-A) +
          β * blockLength X 0 (i : ℕ) ^ (-(2 - s)) +
          β * blockLength X ((i : ℕ) : ℤ) ((N : ℕ) - (i : ℕ)) ^ (-(2 - s))) := by
    intro X
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => hpt X i hi)
  have hsplit := eLpNorm_le_sum_four (gibbsMeasure P N) (p := ENNReal.ofReal p)
    (ENNReal.one_le_ofReal.2 (by linarith)) E hEmeas
    (fun i X => α * blockLength X 0 (i : ℕ) ^ (-A))
    (fun i X => α * blockLength X ((i : ℕ) : ℤ) ((N : ℕ) - (i : ℕ)) ^ (-A))
    (fun i X => β * blockLength X 0 (i : ℕ) ^ (-(2 - s)))
    (fun i X => β * blockLength X ((i : ℕ) : ℤ) ((N : ℕ) - (i : ℕ)) ^ (-(2 - s)))
    hsumpt
  -- Nonnegativity of the four real coefficients of each exterior label.
  have hsummand : ∀ i : Fin (N : ℕ), 0 ≤ α * C₁ ^ (1 / p) * ((i : ℕ) : ℝ) ^ (-A) +
      α * C₁ ^ (1 / p) * (((N : ℕ) - (i : ℕ) : ℕ) : ℝ) ^ (-A) +
      β * C₂ ^ (1 / p) * ((i : ℕ) : ℝ) ^ (-(2 - s)) +
      β * C₂ ^ (1 / p) * (((N : ℕ) - (i : ℕ) : ℕ) : ℝ) ^ (-(2 - s)) := fun i =>
    add_nonneg (add_nonneg (add_nonneg
      (mul_nonneg (mul_nonneg hα0 hC₁p) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      (mul_nonneg (mul_nonneg hα0 hC₁p) (Real.rpow_nonneg (Nat.cast_nonneg _) _)))
      (mul_nonneg (mul_nonneg hβ0 hC₂p) (Real.rpow_nonneg (Nat.cast_nonneg _) _)))
      (mul_nonneg (mul_nonneg hβ0 hC₂p) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  -- Each label contributes at most the `ofReal` of its real coefficient sum.
  have hterm : ∀ i ∈ E,
      eLpNorm (fun X : Configuration N => α * blockLength X 0 (i : ℕ) ^ (-A))
          (ENNReal.ofReal p) (gibbsMeasure P N) +
        eLpNorm (fun X : Configuration N =>
          α * blockLength X ((i : ℕ) : ℤ) ((N : ℕ) - (i : ℕ)) ^ (-A))
          (ENNReal.ofReal p) (gibbsMeasure P N) +
        eLpNorm (fun X : Configuration N => β * blockLength X 0 (i : ℕ) ^ (-(2 - s)))
          (ENNReal.ofReal p) (gibbsMeasure P N) +
        eLpNorm (fun X : Configuration N =>
          β * blockLength X ((i : ℕ) : ℤ) ((N : ℕ) - (i : ℕ)) ^ (-(2 - s)))
          (ENNReal.ofReal p) (gibbsMeasure P N) ≤
        ENNReal.ofReal (α * C₁ ^ (1 / p) * ((i : ℕ) : ℝ) ^ (-A) +
          α * C₁ ^ (1 / p) * (((N : ℕ) - (i : ℕ) : ℕ) : ℝ) ^ (-A) +
          β * C₂ ^ (1 / p) * ((i : ℕ) : ℝ) ^ (-(2 - s)) +
          β * C₂ ^ (1 / p) * (((N : ℕ) - (i : ℕ) : ℕ) : ℝ) ^ (-(2 - s))) := by
    intro i hi
    obtain ⟨hi1, hi2⟩ := hext i hi
    have hm1 : 0 < (i : ℕ) := by omega
    have hNm : 0 < (N : ℕ) - (i : ℕ) := by omega
    have h1 := hmom₁ N 0 (i : ℕ) hm1 α hα0
    have h2 := hmom₁ N ((i : ℕ) : ℤ) ((N : ℕ) - (i : ℕ)) hNm α hα0
    have h3 := hmom₂ N 0 (i : ℕ) hm1 β hβ0
    have h4 := hmom₂ N ((i : ℕ) : ℤ) ((N : ℕ) - (i : ℕ)) hNm β hβ0
    have hn1 : 0 ≤ α * C₁ ^ (1 / p) * ((i : ℕ) : ℝ) ^ (-A) :=
      mul_nonneg (mul_nonneg hα0 hC₁p) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    have hn2 : 0 ≤ α * C₁ ^ (1 / p) * (((N : ℕ) - (i : ℕ) : ℕ) : ℝ) ^ (-A) :=
      mul_nonneg (mul_nonneg hα0 hC₁p) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    have hn3 : 0 ≤ β * C₂ ^ (1 / p) * ((i : ℕ) : ℝ) ^ (-(2 - s)) :=
      mul_nonneg (mul_nonneg hβ0 hC₂p) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    have hn4 : 0 ≤ β * C₂ ^ (1 / p) * (((N : ℕ) - (i : ℕ) : ℕ) : ℝ) ^ (-(2 - s)) :=
      mul_nonneg (mul_nonneg hβ0 hC₂p) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    rw [ENNReal.ofReal_add (add_nonneg (add_nonneg hn1 hn2) hn3) hn4,
      ENNReal.ofReal_add (add_nonneg hn1 hn2) hn3, ENNReal.ofReal_add hn1 hn2]
    exact add_le_add (add_le_add (add_le_add h1 h2) h3) h4
  -- The real sum over the exterior labels.
  have hsum_real : ∑ i ∈ E, (α * C₁ ^ (1 / p) * ((i : ℕ) : ℝ) ^ (-A) +
      α * C₁ ^ (1 / p) * (((N : ℕ) - (i : ℕ) : ℕ) : ℝ) ^ (-A) +
      β * C₂ ^ (1 / p) * ((i : ℕ) : ℝ) ^ (-(2 - s)) +
      β * C₂ ^ (1 / p) * (((N : ℕ) - (i : ℕ) : ℕ) : ℝ) ^ (-(2 - s))) ≤
      2 * C₁ ^ (1 / p) * kernelConst s lam ε * 2 ^ (2 * A - 1) / (A - 1) +
        2 * C₂ ^ (1 / p) * 2 ^ (1 - s) / ((2 - s) * (1 - s)) := by
    have hS1 : ∑ i ∈ E, ((i : ℕ) : ℝ) ^ (-A) ≤ (J : ℝ) ^ (1 - A) / (A - 1) :=
      sum_rpow_neg_le_of_injOn hA1 hJ1 E (fun i => (i : ℕ)) (fun i _ j _ h => Fin.ext h)
        (fun i hi => ⟨(hext i hi).1, le_of_lt i.isLt⟩)
    have hS2 : ∑ i ∈ E, (((N : ℕ) - (i : ℕ) : ℕ) : ℝ) ^ (-A) ≤ (J : ℝ) ^ (1 - A) / (A - 1) :=
      sum_rpow_neg_le_of_injOn hA1 hJ1 E (fun i => (N : ℕ) - (i : ℕ))
        (fun i _ j _ h => Fin.ext (by
          have := i.isLt
          have := j.isLt
          dsimp only at h
          omega))
        (fun i hi => ⟨(hext i hi).2, Nat.sub_le _ _⟩)
    have hS3 : ∑ i ∈ E, ((i : ℕ) : ℝ) ^ (-(2 - s)) ≤
        (J : ℝ) ^ (1 - (2 - s)) / ((2 - s) - 1) :=
      sum_rpow_neg_le_of_injOn (by linarith) hJ1 E (fun i => (i : ℕ)) (fun i _ j _ h => Fin.ext h)
        (fun i hi => ⟨(hext i hi).1, le_of_lt i.isLt⟩)
    have hS4 : ∑ i ∈ E, (((N : ℕ) - (i : ℕ) : ℕ) : ℝ) ^ (-(2 - s)) ≤
        (J : ℝ) ^ (1 - (2 - s)) / ((2 - s) - 1) :=
      sum_rpow_neg_le_of_injOn (by linarith) hJ1 E (fun i => (N : ℕ) - (i : ℕ))
        (fun i _ j _ h => Fin.ext (by
          have := i.isLt
          have := j.isLt
          dsimp only at h
          omega))
        (fun i hi => ⟨(hext i hi).2, Nat.sub_le _ _⟩)
    have hsplit2 : ∑ i ∈ E, (α * C₁ ^ (1 / p) * ((i : ℕ) : ℝ) ^ (-A) +
        α * C₁ ^ (1 / p) * (((N : ℕ) - (i : ℕ) : ℕ) : ℝ) ^ (-A) +
        β * C₂ ^ (1 / p) * ((i : ℕ) : ℝ) ^ (-(2 - s)) +
        β * C₂ ^ (1 / p) * (((N : ℕ) - (i : ℕ) : ℕ) : ℝ) ^ (-(2 - s))) =
        (α * C₁ ^ (1 / p)) * (∑ i ∈ E, ((i : ℕ) : ℝ) ^ (-A) +
          ∑ i ∈ E, (((N : ℕ) - (i : ℕ) : ℕ) : ℝ) ^ (-A)) +
        (β * C₂ ^ (1 / p)) * (∑ i ∈ E, ((i : ℕ) : ℝ) ^ (-(2 - s)) +
          ∑ i ∈ E, (((N : ℕ) - (i : ℕ) : ℕ) : ℝ) ^ (-(2 - s))) := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      ring
    have hbA : (α * C₁ ^ (1 / p)) * (∑ i ∈ E, ((i : ℕ) : ℝ) ^ (-A) +
        ∑ i ∈ E, (((N : ℕ) - (i : ℕ) : ℕ) : ℝ) ^ (-A)) ≤
        (α * C₁ ^ (1 / p)) * (2 * ((J : ℝ) ^ (1 - A) / (A - 1))) :=
      mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hα0 hC₁p)
    have hbB : (β * C₂ ^ (1 / p)) * (∑ i ∈ E, ((i : ℕ) : ℝ) ^ (-(2 - s)) +
        ∑ i ∈ E, (((N : ℕ) - (i : ℕ) : ℕ) : ℝ) ^ (-(2 - s))) ≤
        (β * C₂ ^ (1 / p)) * (2 * ((J : ℝ) ^ (1 - (2 - s)) / ((2 - s) - 1))) :=
      mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hβ0 hC₂p)
    have hfirst : (α * C₁ ^ (1 / p)) * (2 * ((J : ℝ) ^ (1 - A) / (A - 1))) ≤
        2 * C₁ ^ (1 / p) * kernelConst s lam ε * 2 ^ (2 * A - 1) / (A - 1) := by
      have hT := tail_const_A hK hγ1 hlam hA1 hexpA hJhalf
      rw [hα]
      calc kernelConst s lam ε * K ^ (lam + ε) * (2 * K) ^ A * C₁ ^ (1 / p) *
            (2 * ((J : ℝ) ^ (1 - A) / (A - 1)))
          = (2 * C₁ ^ (1 / p) / (A - 1)) *
              (kernelConst s lam ε * (K ^ (lam + ε) * (2 * K) ^ A * (J : ℝ) ^ (1 - A))) := by
            ring
        _ ≤ (2 * C₁ ^ (1 / p) / (A - 1)) * (kernelConst s lam ε * 2 ^ (2 * A - 1)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hT (kernelConst_nonneg hs2 hlam hε))
              (div_nonneg (mul_nonneg two_pos.le hC₁p) (by linarith))
        _ = 2 * C₁ ^ (1 / p) * kernelConst s lam ε * 2 ^ (2 * A - 1) / (A - 1) := by
            ring
    have hsecond : (β * C₂ ^ (1 / p)) * (2 * ((J : ℝ) ^ (1 - (2 - s)) / ((2 - s) - 1))) ≤
        2 * C₂ ^ (1 / p) * 2 ^ (1 - s) / ((2 - s) * (1 - s)) := by
      have hT := tail_const_B hK (by linarith : (0 : ℝ) ≤ γ) hs1 hexp2 hJhalf
      have e1 : (1 : ℝ) - (2 - s) = s - 1 := by ring
      have e2 : (2 - s) - 1 = 1 - s := by ring
      rw [e1, e2, hβ]
      calc K ^ (2 - s) / (2 - s) * C₂ ^ (1 / p) * (2 * ((J : ℝ) ^ (s - 1) / (1 - s)))
          = (2 * C₂ ^ (1 / p) / ((2 - s) * (1 - s))) * (K ^ (2 - s) * (J : ℝ) ^ (s - 1)) := by
            simp only [div_eq_mul_inv, mul_inv]
            ring
        _ ≤ (2 * C₂ ^ (1 / p) / ((2 - s) * (1 - s))) * 2 ^ (1 - s) :=
            mul_le_mul_of_nonneg_left hT
              (div_nonneg (mul_nonneg two_pos.le hC₂p) (mul_nonneg (by linarith) (by linarith)))
        _ = 2 * C₂ ^ (1 / p) * 2 ^ (1 - s) / ((2 - s) * (1 - s)) := by
            ring
    calc ∑ i ∈ E, (α * C₁ ^ (1 / p) * ((i : ℕ) : ℝ) ^ (-A) +
          α * C₁ ^ (1 / p) * (((N : ℕ) - (i : ℕ) : ℕ) : ℝ) ^ (-A) +
          β * C₂ ^ (1 / p) * ((i : ℕ) : ℝ) ^ (-(2 - s)) +
          β * C₂ ^ (1 / p) * (((N : ℕ) - (i : ℕ) : ℕ) : ℝ) ^ (-(2 - s)))
        = _ := hsplit2
      _ ≤ _ := add_le_add hbA hbB
      _ ≤ _ := add_le_add hfirst hsecond
  calc eLpNorm (fun X : Configuration N => ∑ i ∈ E, f ((cyclicLift X (i : ℕ) - cyclicLift X 0) / ℓ))
        (ENNReal.ofReal p) (gibbsMeasure P N)
      ≤ ∑ i ∈ E, (eLpNorm (fun X : Configuration N => α * blockLength X 0 (i : ℕ) ^ (-A))
          (ENNReal.ofReal p) (gibbsMeasure P N) +
        eLpNorm (fun X : Configuration N =>
          α * blockLength X ((i : ℕ) : ℤ) ((N : ℕ) - (i : ℕ)) ^ (-A))
          (ENNReal.ofReal p) (gibbsMeasure P N) +
        eLpNorm (fun X : Configuration N => β * blockLength X 0 (i : ℕ) ^ (-(2 - s)))
          (ENNReal.ofReal p) (gibbsMeasure P N) +
        eLpNorm (fun X : Configuration N =>
          β * blockLength X ((i : ℕ) : ℤ) ((N : ℕ) - (i : ℕ)) ^ (-(2 - s)))
          (ENNReal.ofReal p) (gibbsMeasure P N)) := hsplit
    _ ≤ ∑ i ∈ E, ENNReal.ofReal (α * C₁ ^ (1 / p) * ((i : ℕ) : ℝ) ^ (-A) +
          α * C₁ ^ (1 / p) * (((N : ℕ) - (i : ℕ) : ℕ) : ℝ) ^ (-A) +
          β * C₂ ^ (1 / p) * ((i : ℕ) : ℝ) ^ (-(2 - s)) +
          β * C₂ ^ (1 / p) * (((N : ℕ) - (i : ℕ) : ℕ) : ℝ) ^ (-(2 - s))) :=
        Finset.sum_le_sum fun i hi => hterm i hi
    _ = ENNReal.ofReal (∑ i ∈ E, (α * C₁ ^ (1 / p) * ((i : ℕ) : ℝ) ^ (-A) +
          α * C₁ ^ (1 / p) * (((N : ℕ) - (i : ℕ) : ℕ) : ℝ) ^ (-A) +
          β * C₂ ^ (1 / p) * ((i : ℕ) : ℝ) ^ (-(2 - s)) +
          β * C₂ ^ (1 / p) * (((N : ℕ) - (i : ℕ) : ℕ) : ℝ) ^ (-(2 - s)))) :=
        (ENNReal.ofReal_sum_of_nonneg fun i _ => hsummand i).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hsum_real

/-- **Exterior tail** (part of Lemma 5.2, the rotation part, first claim). Let `P` be the model
parameters, with exponent `s = P.val.2`, let `λ ≥ 0`, `ε > 0` and `p ≥ 2`. There is `γ₀ > 1`
depending only on `s` such that, for every `γ ≥ γ₀`, there is `C` with: for every `N ≥ 2`,
`0 < ℓ ≤ 1` with `K = Nℓ ≥ 1`, and every `C¹` function `f` of period `1/ℓ` with `f(1/(2ℓ)) = 0`
satisfying the derivative bound of the kernel, the exterior sum has `L^p` norm at most `C`. -/
theorem exterior_tail_eLpNorm_le (P : Parameters) (hPL : External.PrekopaLeindler) {lam ε p : ℝ}
    (hlam : 0 ≤ lam) (hε : 0 < ε) (hp : 2 ≤ p) :
    ∃ γ₀ : ℝ, 1 < γ₀ ∧ ∀ γ : ℝ, γ₀ ≤ γ → ∃ C : ℝ, 0 ≤ C ∧
      ∀ (N : ℕ+) (ℓ : ℝ), 2 ≤ (N : ℕ) → 0 < ℓ → ℓ ≤ 1 → 1 ≤ ((N : ℕ) : ℝ) * ℓ →
        ∀ f : ℝ → ℝ, ContDiff ℝ 1 f → Function.Periodic f (1 / ℓ) → f (1 / ℓ / 2) = 0 →
        (∀ u ∈ Icc (-(1 / ℓ / 2)) (1 / ℓ / 2),
          |deriv f u| ≤ (if |u| ≤ 2 then 1 / (max |u| (((N : ℕ) : ℝ) * ℓ)⁻¹) ^ (1 + lam) else 0) +
            (if 2 ≤ |u| then 1 / |u| ^ (3 - P.val.2) else 0)) →
        eLpNorm (exteriorSum N ℓ γ f) (ENNReal.ofReal p) (gibbsMeasure P N) ≤
          ENNReal.ofReal C := by
  have hs1 : P.val.2 < 1 := P.property.2.2
  have hγ0 : 1 < (2 - P.val.2) / (1 - P.val.2) := by
    rw [lt_div_iff₀ (by linarith)]
    linarith
  exact ⟨(2 - P.val.2) / (1 - P.val.2), hγ0,
    fun γ hγ => exterior_tail_eLpNorm_le_of_ge P hPL hlam hε hp γ hγ⟩

end Riesz1

end
