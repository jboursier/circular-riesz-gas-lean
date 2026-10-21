/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.APrioriGoodGradientDerivative
public import Riesz1.Variance.APrioriGoodGradientVanishing

/-!
# The derivative of the gap-coordinate cutoff along a coordinate

The gradient claim in the proof of Lemma 5.2. The gap-coordinate cutoff is the product
`P · H` of the pair product `P` and the nearest-neighbour product `H`. Off finitely many affine
hyperplanes every factor is differentiable with the derivative of
`Riesz1/Variance/APrioriGoodGradientDerivative.lean`. This file assembles the product rule and
bounds the derivative along a coordinate vector `e_i = Pi.single i 1`:

`|∂_i η̃| ≤ 4 K^ε + (2 / K^ε) · #{pairs whose arc contains i}`.

The count is bounded in `Riesz1/Variance/APrioriGoodGradientCount.lean`.
-/

@[expose] public section

noncomputable section

open Finset MeasureTheory

namespace Riesz1

variable {N : ℕ+}

/-- Each pair of the good-event cutoff has `0 < |k| < N`, so its arc has fewer than `N` labels. -/
theorem abs_pair_snd_lt_of_mem {I : Finset (Fin (N : ℕ))} {p : Fin (N : ℕ) × ℤ}
    (hp : p ∈ cutoffPairs N I) : |((p.2 : ℤ))| < ((N : ℕ) : ℤ) := by
  have hkIcc : p.2 ∈ Icc (-((((N : ℕ) / 2 : ℕ)) : ℤ)) ((((N : ℕ) / 2 : ℕ)) : ℤ) :=
    (Finset.mem_erase.1 (Finset.mem_product.1 (Finset.mem_filter.1 hp).1).2).2
  have hp2 : p.2 ≠ 0 := (Finset.mem_erase.1 (Finset.mem_product.1 (Finset.mem_filter.1 hp).1).2).1
  rw [Finset.mem_Icc] at hkIcc
  have hN : 0 < (N : ℕ) := N.pos
  rw [abs_lt]
  constructor <;> omega

/-- The tolerance of a pair is at least `K^ε`, for `K ≥ 1`, `ε ≥ 0` and `s ≥ 0`. -/
theorem rpow_le_pairScale {s K ε : ℝ} (hK : 1 ≤ K) (hs : 0 ≤ s)
    {I : Finset (Fin (N : ℕ))} {p : Fin (N : ℕ) × ℤ} (hp : p ∈ cutoffPairs N I) :
    K ^ ε ≤ pairScale s K ε p := by
  have hp2 : p.2 ≠ 0 := (Finset.mem_erase.1 (Finset.mem_product.1 (Finset.mem_filter.1 hp).1).2).1
  have hnat : (1 : ℝ) ≤ ((p.2.natAbs : ℕ) : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hp2)
  have hpow : (1 : ℝ) ≤ ((p.2.natAbs : ℕ) : ℝ) ^ (s / 2) :=
    Real.one_le_rpow hnat (by linarith)
  unfold pairScale
  exact le_mul_of_one_le_right (Real.rpow_nonneg (by linarith) ε) hpow

/-- Each nearest-neighbour factor lies in `[0, 1]`. -/
theorem nearest_factor_mem_unitInterval (K ε : ℝ) (u : ℝ) :
    0 ≤ scalarCutoff (2 * u / K ^ ε) * scalarCutoff (2 / (K ^ ε * u)) ∧
      scalarCutoff (2 * u / K ^ ε) * scalarCutoff (2 / (K ^ ε * u)) ≤ 1 :=
  ⟨mul_nonneg (scalarCutoff_nonneg _) (scalarCutoff_nonneg _),
    mul_le_one_of_unitInterval (scalarCutoff_nonneg _) (scalarCutoff_le_one _)
      (scalarCutoff_le_one _)⟩

/-! ### Elementary bounds for sums -/

/-- A sum of real numbers is bounded by the sum of the absolute values of its terms. -/
theorem abs_sum_le_card_filter_mul {ι : Type*} (t : Finset ι) (x : ι → ℝ) (q : ι → Prop)
    [DecidablePred q] (C : ℝ) (hx : ∀ p ∈ t, |x p| ≤ if q p then C else 0) :
    |∑ p ∈ t, x p| ≤ ((t.filter q).card : ℝ) * C := by
  calc |∑ p ∈ t, x p| ≤ ∑ p ∈ t, |x p| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ t, (if q p then C else 0) := Finset.sum_le_sum hx
    _ = ∑ p ∈ t.filter q, C := by rw [Finset.sum_filter]
    _ = ((t.filter q).card : ℝ) * C := by rw [Finset.sum_const, nsmul_eq_mul]

/-- A sum whose terms vanish except at `i`, where they are bounded by `C`, is bounded by `C`. -/
theorem abs_sum_le_of_single {ι : Type*} [DecidableEq ι] (t : Finset ι) (x : ι → ℝ) (i : ι)
    (C : ℝ) (hC : 0 ≤ C) (hx : ∀ j ∈ t, |x j| ≤ if j = i then C else 0) :
    |∑ j ∈ t, x j| ≤ C := by
  calc |∑ j ∈ t, x j| ≤ ∑ j ∈ t, |x j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ t, (if j = i then C else 0) := Finset.sum_le_sum hx
    _ ≤ C := by
      rw [Finset.sum_ite_eq']
      split_ifs <;> linarith

/-- The sum `∑_j f_j c_j e_i(j)` of the nearest-neighbour derivatives at the unit vector `e_i` is
bounded by `C`, when each `|f_j| ≤ 1` and `|c_i| ≤ C`. -/
theorem abs_sum_mul_single_le {ι : Type*} [DecidableEq ι] (t : Finset ι) (f c : ι → ℝ) (i : ι)
    (C : ℝ) (hC : 0 ≤ C) (hf : ∀ j ∈ t, |f j| ≤ 1) (hc : ∀ j ∈ t, j = i → |c j| ≤ C) :
    |∑ j ∈ t, f j * (c j * (Pi.single i (1 : ℝ) : ι → ℝ) j)| ≤ C := by
  refine abs_sum_le_of_single t _ i C hC fun j hj => ?_
  by_cases hji : j = i
  · subst hji
    rw [ite_eq_left rfl, Pi.single_eq_same, mul_one, abs_mul]
    calc |f j| * |c j| ≤ 1 * C := mul_le_mul (hf j hj) (hc j hj rfl) (abs_nonneg _) zero_le_one
      _ = C := one_mul C
  · rw [ite_eq_right hji, Pi.single_eq_of_ne hji, mul_zero, mul_zero, abs_zero]

/-- A product of two real numbers, one of absolute value at most one, is bounded by the sum of
the absolute values. -/
theorem abs_mul_add_mul_le {a b x y : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1) :
    |a * x + b * y| ≤ |x| + |y| := by
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul]
  nlinarith [abs_nonneg x, abs_nonneg y, abs_nonneg a, abs_nonneg b]

/-! ### The product rule along a coordinate -/

/-- **Derivative of the gap-coordinate cutoff.** Let `K ≥ 1`, `s ≥ 0`, `ε ≥ 0`, and let `z` be a
gap vector at which every pair deviation avoids the kinks of its factor, and every nearest-neighbour
gap avoids the kinks of its factor. Then the cutoff is differentiable at `z`, and its derivative
`f'` along the coordinate vector `e_i` satisfies
`|f'(e_i)| ≤ 4 K^ε + (2 / K^ε) · #{p ∈ cutoffPairs : arc of p contains i}`. -/
theorem gapCutoff_hasFDerivAt (s K γ ε : ℝ) (hK1 : 1 ≤ K) (hs : 0 ≤ s) (hε : 0 ≤ ε)
    (z : Fin (N : ℕ) → ℝ)
    (hpair : ∀ p ∈ cutoffPairs N (window N K γ), gapPairDev N z p ≠ 0 ∧
      2 * |gapPairDev N z p| / pairScale s K ε p ≠ 1 ∧
      2 * |gapPairDev N z p| / pairScale s K ε p ≠ 2)
    (hnear : ∀ i ∈ nearestPairs N (window N K γ), z i ≠ 0 ∧ 2 * z i / K ^ ε ≠ 1 ∧
      2 * z i / K ^ ε ≠ 2 ∧ 2 / (K ^ ε * z i) ≠ 1 ∧ 2 / (K ^ ε * z i) ≠ 2) :
    ∃ f' : (Fin (N : ℕ) → ℝ) →L[ℝ] ℝ, HasFDerivAt (gapCutoff N s K γ ε) f' z ∧
      ∀ i : Fin (N : ℕ), |f' (Pi.single i (1 : ℝ))| ≤
        4 * K ^ ε + (2 / K ^ ε) *
          ((cutoffPairs N (window N K γ)).filter fun p =>
            gapOrientedSum N (Pi.single i (1 : ℝ)) (((p.1 : ℕ) : ℤ))
              (((p.1 : ℕ) : ℤ) + p.2) ≠ 0).card := by
  classical
  have hKpos : 0 < K := by linarith
  have hKε1 : 1 ≤ K ^ ε := Real.one_le_rpow hK1 hε
  have hKεpos : 0 < K ^ ε := by linarith
  -- The pair factors.
  have hpairF : ∀ p ∈ cutoffPairs N (window N K γ), ∃ d : ℝ,
      |d| ≤ 2 / pairScale s K ε p ∧
      HasFDerivAt (fun w : Fin (N : ℕ) → ℝ =>
          scalarCutoff (2 * |gapPairDev N w p| / pairScale s K ε p))
        (d • gapArcCLM N (((p.1 : ℕ) : ℤ)) (((p.1 : ℕ) : ℤ) + p.2)) z := by
    intro p hp
    exact pair_factor_hasFDerivAt N (pairScale_pos_of_mem_cutoffPairs hKpos hp) p z
      (hpair p hp).1 (hpair p hp).2.1 (hpair p hp).2.2
  choose! d hd hF using hpairF
  -- The nearest-neighbour factors.
  have hnearF : ∀ i ∈ nearestPairs N (window N K γ), ∃ c : ℝ, |c| ≤ 4 * K ^ ε ∧
      HasFDerivAt (fun w : Fin (N : ℕ) → ℝ =>
          scalarCutoff (2 * w i / K ^ ε) * scalarCutoff (2 / (K ^ ε * w i)))
        (c • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (N : ℕ) => ℝ) i) z := by
    intro i hi
    obtain ⟨hz0, hz1, hz2, hz3, hz4⟩ := hnear i hi
    obtain ⟨c, hc, hcD⟩ := nearest_scalarCutoff_hasDerivAt hKε1 hz0 hz1 hz2 hz3 hz4
    refine ⟨c, hc, ?_⟩
    have hproj := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (N : ℕ) => ℝ) i).hasFDerivAt
      (x := z)
    exact HasDerivAt.comp_hasFDerivAt (f := fun w : Fin (N : ℕ) → ℝ => w i)
      (h₂ := fun u : ℝ => scalarCutoff (2 * u / K ^ ε) * scalarCutoff (2 / (K ^ ε * u))) z hcD hproj
  choose! c hc hH using hnearF
  -- The two products.
  set P := cutoffPairs N (window N K γ) with hPdef
  set Nr := nearestPairs N (window N K γ) with hNrdef
  have hPF : HasFDerivAt
      (fun w : Fin (N : ℕ) → ℝ => ∏ p ∈ P, scalarCutoff (2 * |gapPairDev N w p| / pairScale s K ε p))
      (∑ p ∈ P, (∏ q ∈ P.erase p, scalarCutoff (2 * |gapPairDev N z q| / pairScale s K ε q)) •
        (d p • gapArcCLM N (((p.1 : ℕ) : ℤ)) (((p.1 : ℕ) : ℤ) + p.2))) z :=
    HasFDerivAt.finsetProd (fun p hp => hF p hp)
  have hHF : HasFDerivAt
      (fun w : Fin (N : ℕ) → ℝ => ∏ i ∈ Nr,
        (scalarCutoff (2 * w i / K ^ ε) * scalarCutoff (2 / (K ^ ε * w i))))
      (∑ i ∈ Nr, (∏ j ∈ Nr.erase i,
          (scalarCutoff (2 * z j / K ^ ε) * scalarCutoff (2 / (K ^ ε * z j)))) •
        (c i • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (N : ℕ) => ℝ) i)) z :=
    HasFDerivAt.finsetProd (fun i hi => hH i hi)
  have hG := hPF.mul hHF
  refine ⟨_, hG, fun i => ?_⟩
  -- Unit-interval bounds on the two products at `z`.
  have hPabs : |∏ p ∈ P, scalarCutoff (2 * |gapPairDev N z p| / pairScale s K ε p)| ≤ 1 := by
    have h := prod_mem_unitInterval P
      (fun p => scalarCutoff (2 * |gapPairDev N z p| / pairScale s K ε p))
      (fun p _ => scalarCutoff_nonneg _) (fun p _ => scalarCutoff_le_one _)
    rw [abs_le]
    exact ⟨by linarith [h.1], h.2⟩
  have hHabs : |∏ j ∈ Nr, (scalarCutoff (2 * z j / K ^ ε) * scalarCutoff (2 / (K ^ ε * z j)))| ≤ 1 := by
    have h := prod_mem_unitInterval Nr
      (fun j => scalarCutoff (2 * z j / K ^ ε) * scalarCutoff (2 / (K ^ ε * z j)))
      (fun j _ => (nearest_factor_mem_unitInterval K ε (z j)).1)
      (fun j _ => (nearest_factor_mem_unitInterval K ε (z j)).2)
    rw [abs_le]
    exact ⟨by linarith [h.1], h.2⟩
  -- The nearest-neighbour part of the derivative at `e_i`.
  have hNsum : |(∑ j ∈ Nr, (∏ l ∈ Nr.erase j,
      (scalarCutoff (2 * z l / K ^ ε) * scalarCutoff (2 / (K ^ ε * z l)))) •
        (c j • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (N : ℕ) => ℝ) j))
      (Pi.single i (1 : ℝ))| ≤ 4 * K ^ ε := by
    simp only [_root_.sum_apply, smul_apply,
      ContinuousLinearMap.proj_apply, smul_eq_mul]
    refine abs_sum_mul_single_le Nr _ c i (4 * K ^ ε) (by linarith) (fun j hj => ?_)
      (fun j hj _ => hc j hj)
    have h := prod_mem_unitInterval (Nr.erase j)
      (fun l => scalarCutoff (2 * z l / K ^ ε) * scalarCutoff (2 / (K ^ ε * z l)))
      (fun l _ => (nearest_factor_mem_unitInterval K ε (z l)).1)
      (fun l _ => (nearest_factor_mem_unitInterval K ε (z l)).2)
    rw [abs_le]
    exact ⟨by linarith [h.1], h.2⟩
  -- The pair part of the derivative at `e_i`: only the pairs whose arc contains `i` contribute.
  have hPsum : |(∑ p ∈ P, (∏ q ∈ P.erase p,
      scalarCutoff (2 * |gapPairDev N z q| / pairScale s K ε q)) •
        (d p • gapArcCLM N (((p.1 : ℕ) : ℤ)) (((p.1 : ℕ) : ℤ) + p.2)))
      (Pi.single i (1 : ℝ))| ≤
      ((P.filter fun p => gapOrientedSum N (Pi.single i (1 : ℝ)) (((p.1 : ℕ) : ℤ))
        (((p.1 : ℕ) : ℤ) + p.2) ≠ 0).card : ℝ) * (2 / K ^ ε) := by
    simp only [_root_.sum_apply, smul_apply, gapArcCLM_apply, smul_eq_mul]
    refine abs_sum_le_card_filter_mul P _ _ (2 / K ^ ε) fun p hp => ?_
    by_cases hq : gapOrientedSum N (Pi.single i (1 : ℝ)) (((p.1 : ℕ) : ℤ))
        (((p.1 : ℕ) : ℤ) + p.2) ≠ 0
    · rw [ite_eq_left hq]
      have hL : |gapOrientedSum N (Pi.single i (1 : ℝ)) (((p.1 : ℕ) : ℤ))
          (((p.1 : ℕ) : ℤ) + p.2)| ≤ 1 :=
        abs_gapOrientedSum_single_le N i _ _ (by rw [add_sub_cancel_left]; exact abs_pair_snd_lt_of_mem hp)
      have hQ : |∏ q ∈ P.erase p,
          scalarCutoff (2 * |gapPairDev N z q| / pairScale s K ε q)| ≤ 1 := by
        have h := prod_mem_unitInterval (P.erase p)
          (fun q => scalarCutoff (2 * |gapPairDev N z q| / pairScale s K ε q))
          (fun q _ => scalarCutoff_nonneg _) (fun q _ => scalarCutoff_le_one _)
        rw [abs_le]
        exact ⟨by linarith [h.1], h.2⟩
      have hd' := hd p hp
      have hM := rpow_le_pairScale (ε := ε) hK1 hs hp
      have hdpos : 0 < pairScale s K ε p := pairScale_pos_of_mem_cutoffPairs hKpos hp
      rw [abs_mul, abs_mul]
      calc |∏ q ∈ P.erase p, scalarCutoff (2 * |gapPairDev N z q| / pairScale s K ε q)| *
            (|d p| * |gapOrientedSum N (Pi.single i (1 : ℝ)) (((p.1 : ℕ) : ℤ))
              (((p.1 : ℕ) : ℤ) + p.2)|)
          ≤ 1 * ((2 / pairScale s K ε p) * 1) :=
            mul_le_mul hQ (mul_le_mul hd' hL (abs_nonneg _) (by positivity)) (by positivity)
              zero_le_one
        _ = 2 * (pairScale s K ε p)⁻¹ := by ring
        _ ≤ 2 / K ^ ε := by
            rw [div_eq_mul_inv]
            exact mul_le_mul_of_nonneg_left (inv_anti₀ hKεpos hM) (by norm_num)
    · rw [ite_eq_right hq]
      have h0 : gapOrientedSum N (Pi.single i (1 : ℝ)) (((p.1 : ℕ) : ℤ))
          (((p.1 : ℕ) : ℤ) + p.2) = 0 := not_not.1 hq
      rw [h0, mul_zero, mul_zero, abs_zero]
  -- Combine the two parts.
  rw [add_apply, smul_apply, smul_apply,
    smul_eq_mul, smul_eq_mul]
  refine (abs_mul_add_mul_le hPabs hHabs).trans ?_
  linarith [hNsum, hPsum]

end Riesz1

end
end
