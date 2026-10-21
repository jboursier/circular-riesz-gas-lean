/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Rigidity.ReductionScalesReflection
public import Riesz1.Rigidity.GapLawMoments

/-!
# Mean of the multiscale increment on a full block

This is part of Lemma 4.4, the mean assertion `|E_{Q_m} G_m| ≤ 1/2` when the block of
`G_m` is full, that is `2 k_{m+1} = N` (and then `k_{m+1} = k = N/2`). Then the scale-`k_{m+1}`
radius satisfies `R_m ≥ N`, so the forcing potential vanishes identically: the constrained law is
the Gibbs law. The mean of `G_m` under the Gibbs law is the difference of two centred averages
`cyclicCentre`, each in `[0, 1/2]` (`cyclicCentre_mem`), which gives the bound.

The main results are `blockLength_lt_N`, `constrainedLaw_eq_gibbs_of_forcingPotential_zero`,
`integral_scaleIncrement_full_eq` and `abs_integral_scaleIncrement_full`.
-/

@[expose] public section

open MeasureTheory Finset

namespace Riesz1

variable {N : ℕ+}

/-! ### Centred averages of the representatives -/

/-- A Gauss sum: `2 ∑_{r < n} (c + r) = 2 n c + n (n - 1)`. -/
theorem sum_range_add_real_mul_two (n : ℕ) (c : ℝ) :
    (∑ r ∈ range n, (c + (r : ℝ))) * 2 = 2 * (n : ℝ) * c + (n : ℝ) * ((n : ℝ) - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, add_mul, ih]
    push_cast
    ring

/-- The centred average of the representatives `J_s(i)` about the particle `i`:
`|J_s(i)|⁻¹ ∑_{j ∈ J_s(i)} (j - i)`. -/
noncomputable def cyclicCentre (N : ℕ+) (s : ℕ) (i : ℤ) : ℝ :=
  ((cyclicRep N s i).card : ℝ)⁻¹ * ∑ j ∈ cyclicRep N s i, ((j : ℝ) - i)

/-- The centred average lies in `[0, 1/2]` for every scale with `2 s ≤ N`: it vanishes when the
block is symmetric about `i` (`2 s < N`) and equals `1/2` when the block is the even full block. -/
theorem cyclicCentre_mem {N : ℕ+} (hN : 2 ≤ (N : ℕ)) {s : ℕ} (hs : 2 * s ≤ (N : ℕ)) (i : ℤ) :
    0 ≤ cyclicCentre N s i ∧ cyclicCentre N s i ≤ 1 / 2 := by
  rcases Nat.eq_zero_or_pos s with rfl | hspos
  · have h0 : cyclicRep N 0 i = {i} := by
      simp [cyclicRep, N.pos]
    simp [cyclicCentre, h0]
  by_cases h : 2 * s < (N : ℕ)
  · have hst : cyclicRepStart N s i = i - s := by
      unfold cyclicRepStart
      rw [ite_eq_left h]
    have hsp : cyclicRepSpan N s = 2 * s := by
      unfold cyclicRepSpan
      rw [ite_eq_left h]
    have hsum : ∑ j ∈ cyclicRep N s i, ((j : ℝ) - i) = 0 := by
      rw [cyclicRep_eq_Icc hspos i, hst, hsp,
        sum_Icc_eq_sum_range_int (fun j : ℤ => (j : ℝ) - i) (i - s) (2 * s)]
      have e1 : ∑ r ∈ range (2 * s + 1), ((((i - s + (r : ℤ)) : ℤ) : ℝ) - i) =
          ∑ r ∈ range (2 * s + 1), (-(s : ℝ) + (r : ℝ)) :=
        Finset.sum_congr rfl fun r _ => by push_cast; ring
      rw [e1]
      have h2 := sum_range_add_real_mul_two (2 * s + 1) (-(s : ℝ))
      have h3 : (∑ r ∈ range (2 * s + 1), (-(s : ℝ) + (r : ℝ))) * 2 = 0 := by
        rw [h2]
        push_cast
        ring
      linarith
    unfold cyclicCentre
    rw [hsum, mul_zero]
    exact ⟨le_rfl, by norm_num⟩
  · have h' : 2 * s = (N : ℕ) := by omega
    have hst : cyclicRepStart N s i = i - s + 1 := by
      unfold cyclicRepStart
      rw [ite_eq_right h]
    have hsp : cyclicRepSpan N s = 2 * s - 1 := by
      unfold cyclicRepSpan
      rw [ite_eq_right h]
    have hcard : (cyclicRep N s i).card = 2 * s := by
      rw [card_cyclicRep, hsp]
      omega
    have hsum : ∑ j ∈ cyclicRep N s i, ((j : ℝ) - i) = (s : ℝ) := by
      rw [cyclicRep_eq_Icc hspos i, hst, hsp,
        sum_Icc_eq_sum_range_int (fun j : ℤ => (j : ℝ) - i) (i - s + 1) (2 * s - 1)]
      rw [show 2 * s - 1 + 1 = 2 * s by omega]
      have e1 : ∑ r ∈ range (2 * s), ((((i - s + 1 + (r : ℤ)) : ℤ) : ℝ) - i) =
          ∑ r ∈ range (2 * s), (1 - (s : ℝ) + (r : ℝ)) :=
        Finset.sum_congr rfl fun r _ => by push_cast; ring
      rw [e1]
      have h2 := sum_range_add_real_mul_two (2 * s) (1 - (s : ℝ))
      push_cast at h2
      linarith
    unfold cyclicCentre
    rw [hcard, hsum]
    have hs0 : (0 : ℝ) < s := by exact_mod_cast hspos
    have h2s : ((2 * s : ℕ) : ℝ) = 2 * (s : ℝ) := by push_cast; ring
    rw [h2s]
    constructor
    · positivity
    · have : (2 * (s : ℝ))⁻¹ * (s : ℝ) = 1 / 2 := by
        field_simp
      linarith

/-- Shifting the reference point of a centred average: `|J|⁻¹ ∑_{j ∈ J} (j - a)` equals
`cyclicCentre` about `i` plus `i - a`, for a nonempty set `J`. -/
theorem centre_shift (J : Finset ℤ) (hne : J.Nonempty) (a i : ℤ) :
    ((J.card : ℕ) : ℝ)⁻¹ * ∑ j ∈ J, ((j : ℝ) - a) =
      ((J.card : ℕ) : ℝ)⁻¹ * ∑ j ∈ J, ((j : ℝ) - i) + ((i : ℝ) - a) := by
  have hcard : ((J.card : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.2 hne).ne'
  have e : ∑ j ∈ J, ((j : ℝ) - a) =
      ∑ j ∈ J, ((j : ℝ) - i) + ((J.card : ℕ) : ℝ) * ((i : ℝ) - a) := by
    have e1 : ∑ j ∈ J, ((j : ℝ) - a) = ∑ j ∈ J, (((j : ℝ) - i) + ((i : ℝ) - a)) :=
      Finset.sum_congr rfl fun j _ => by ring
    rw [e1, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  rw [e, mul_add, ← mul_assoc, inv_mul_cancel₀ hcard, one_mul]

/-- The normalized scaling `N⁻¹ (r · N (x - y)) = (x - y) r` used for the coefficients of `G_m`. -/
theorem inv_mul_scale_eq (N : ℝ) (hN : N ≠ 0) (r x y : ℝ) :
    N⁻¹ * (r * (N * (x - y))) = x * r - y * r := by
  rw [show r * (N * (x - y)) = N * (r * (x - y)) by ring, ← mul_assoc, inv_mul_cancel₀ hN, one_mul]
  ring

/-! ### The mean of the gap sum -/

/-- The sum of the gap coefficients is the weighted sum of the lifted coefficients with weights
the offsets: `∑_{u ≤ L} a_u = N⁻¹ ∑_{r ≤ L} r c_r`. -/
theorem sum_gapCoefOf_eq (N : ℝ) (c : ℕ → ℝ) (L : ℕ) :
    ∑ u ∈ range (L + 1), gapCoefOf N c L u = N⁻¹ * ∑ r ∈ range (L + 1), (r : ℝ) * c r := by
  unfold gapCoefOf
  rw [← Finset.mul_sum, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun r hr => ?_
  have hr' := Finset.mem_range.1 hr
  have hfilt : (range (L + 1)).filter (fun u => u < r) = range r := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, hfilt, Finset.card_range,
    nsmul_eq_mul]

/-! ### Block length and the full block -/

/-- A block of `L < N` consecutive gaps has length less than `N`. -/
theorem blockLength_lt_N (X : Configuration N) (i0 : ℤ) {L : ℕ} (hL : L < (N : ℕ)) :
    blockLength X i0 L < ((N : ℕ) : ℝ) := by
  have h := cyclicLift_strictMono X (show i0 + (L : ℤ) < i0 + ((N : ℕ) : ℤ) by omega)
  rw [cyclicLift_add_N] at h
  have hN0 : (0 : ℝ) < ((N : ℕ) : ℝ) := by exact_mod_cast N.pos
  unfold blockLength
  have hd : cyclicLift X (i0 + (L : ℤ)) - cyclicLift X i0 < 1 := by linarith
  nlinarith

/-- A forcing potential vanishing identically makes the constrained law the Gibbs law. -/
theorem constrainedLaw_eq_gibbs_of_forcingPotential_zero (P : Parameters) (N : ℕ+) (θ : ℝ → ℝ)
    (i0 : ℤ) (L : ℕ) (R : ℝ) (h : ∀ X : Configuration N, forcingPotential θ i0 L R X = 0) :
    constrainedLaw P N θ i0 L R = gibbsMeasure P N := by
  have hz : constrainedNormalizer P N θ i0 L R = 1 := by
    unfold constrainedNormalizer
    simp only [h, mul_zero, Real.exp_zero]
    have := isProbabilityMeasure_gibbsMeasure P N
    simp
  unfold constrainedLaw
  have hfun : (fun X : Configuration N => ENNReal.ofReal
      ((constrainedNormalizer P N θ i0 L R)⁻¹ * Real.exp (-P.val.1 * forcingPotential θ i0 L R X))) = 1 := by
    funext X
    rw [hz, h X]
    simp
  rw [hfun, withDensity_one]

/-- The offset-weighted sum of normalized block weights: for `J ⊆ [a, a + n]`,
`∑_{r ≤ n} w_J(a + r) r = |J|⁻¹ ∑_{j ∈ J} (j - a)`. -/
theorem sum_blockWeight_mul_offset {J : Finset ℤ} {a : ℤ} {n : ℕ}
    (hJ : J ⊆ Finset.Icc a (a + n)) :
    ∑ r ∈ range (n + 1), blockWeight J (a + r) * (r : ℝ) =
      ((J.card : ℕ) : ℝ)⁻¹ * ∑ j ∈ J, ((j : ℝ) - a) := by
  calc ∑ r ∈ range (n + 1), blockWeight J (a + r) * (r : ℝ)
      = ∑ r ∈ range (n + 1), blockWeight J (a + r) * ((((a + (r : ℤ)) : ℤ) : ℝ) - (a : ℝ)) :=
        Finset.sum_congr rfl fun r _ => by push_cast; ring
    _ = ((J.card : ℕ) : ℝ)⁻¹ * ∑ j ∈ J, ((j : ℝ) - a) :=
        sum_blockWeight_mul_range hJ (fun j : ℤ => (j : ℝ) - a)

/-- The mean of the increment `G_m` under the Gibbs law: the difference of the centred averages of the
lower scale and of the block scale, with the common reference point `i`. -/
theorem integral_scaleIncrement_gibbs_eq (P : Parameters) (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (i : ℤ)
    {k q m : ℕ} (hk : 1 ≤ k) (hkN : 2 * k ≤ (N : ℕ)) (hm : m < q) :
    ∫ X, scaleIncrement i k q m X ∂gibbsMeasure P N =
      cyclicCentre N (lowScale k q m) i - cyclicCentre N (scaleIndex k q (m + 1)) i := by
  have hK : 1 ≤ scaleIndex k q (m + 1) := one_le_scaleIndex hk
  have hKk : scaleIndex k q (m + 1) ≤ k := (scaleIndex_mem hk (by omega) (by omega)).2
  have hKN : 2 * scaleIndex k q (m + 1) ≤ (N : ℕ) := by omega
  have hlow : lowScale k q m ≤ scaleIndex k q (m + 1) := lowScale_le hk
  have hsub : cyclicRep N (lowScale k q m) i ⊆
      Finset.Icc (cyclicRepStart N (scaleIndex k q (m + 1)) i)
        (cyclicRepStart N (scaleIndex k q (m + 1)) i + cyclicRepSpan N (scaleIndex k q (m + 1))) := by
    rw [← cyclicRep_eq_Icc hK i]
    exact cyclicRep_subset_of_le hlow hKN i
  have hsubK : cyclicRep N (scaleIndex k q (m + 1)) i ⊆
      Finset.Icc (cyclicRepStart N (scaleIndex k q (m + 1)) i)
        (cyclicRepStart N (scaleIndex k q (m + 1)) i + cyclicRepSpan N (scaleIndex k q (m + 1))) :=
    (cyclicRep_eq_Icc hK i).subset
  have hLz : gapCoefOf ((N : ℕ) : ℝ) (scaleCoef N i k q m)
      (cyclicRepSpan N (scaleIndex k q (m + 1))) (cyclicRepSpan N (scaleIndex k q (m + 1))) = 0 := by
    unfold gapCoefOf
    rw [Finset.sum_eq_zero (fun r hr => ite_eq_right (by have := Finset.mem_range.1 hr; omega)),
      mul_zero]
  -- the integral of the gap form is the sum of the gap coefficients, since each gap has mean one
  have hint : ∫ X, scaleIncrement i k q m X ∂gibbsMeasure P N =
      ∑ u ∈ range (cyclicRepSpan N (scaleIndex k q (m + 1)) + 1),
        gapCoefOf ((N : ℕ) : ℝ) (scaleCoef N i k q m)
          (cyclicRepSpan N (scaleIndex k q (m + 1))) u := by
    simp only [scaleIncrement_eq_gapSum N i hk hkN hm]
    rw [integral_finsetSum]
    · simp only [blockFam, integral_const_mul, integral_gap_gibbsMeasure P N hN, mul_one]
      rw [Finset.sum_range_succ, hLz, add_zero, Finset.sum_range]
    · intro u _
      exact (integrable_gap P N _).const_mul _
  have hN0 : ((N : ℕ) : ℝ) ≠ 0 := by exact_mod_cast N.ne_zero
  rw [hint, sum_gapCoefOf_eq, Finset.mul_sum]
  have hsplit : ∀ r ∈ range (cyclicRepSpan N (scaleIndex k q (m + 1)) + 1),
      ((N : ℕ) : ℝ)⁻¹ * ((r : ℝ) * scaleCoef N i k q m r) =
        blockWeight (cyclicRep N (lowScale k q m) i)
            (cyclicRepStart N (scaleIndex k q (m + 1)) i + r) * (r : ℝ) -
          blockWeight (cyclicRep N (scaleIndex k q (m + 1)) i)
            (cyclicRepStart N (scaleIndex k q (m + 1)) i + r) * (r : ℝ) := by
    intro r _
    unfold scaleCoef
    exact inv_mul_scale_eq _ hN0 _ _ _
  rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib,
    sum_blockWeight_mul_offset hsub, sum_blockWeight_mul_offset hsubK,
    centre_shift (cyclicRep N (lowScale k q m) i) (cyclicRep_nonempty N _ i)
      (cyclicRepStart N (scaleIndex k q (m + 1)) i) i,
    centre_shift (cyclicRep N (scaleIndex k q (m + 1)) i) (cyclicRep_nonempty N _ i)
      (cyclicRepStart N (scaleIndex k q (m + 1)) i) i]
  unfold cyclicCentre
  ring

/-- The mean of the increment `G_m` under the Gibbs law is bounded by `1/2` on a full block. -/
theorem abs_integral_scaleIncrement_full (P : Parameters) (N : ℕ+) (hN : 2 ≤ (N : ℕ))
    {θ : ℝ → ℝ} (hθ : IsForcingCutoff θ) {ε : ℝ} (hε : 0 ≤ ε) (i : ℤ) {k q m : ℕ}
    (hk : 1 ≤ k) (hkN : 2 * k ≤ (N : ℕ)) (hm : m < q)
    (hfull : ¬ 2 * scaleIndex k q (m + 1) < (N : ℕ)) :
    |∫ X, scaleIncrement i k q m X ∂scaleLaw P N θ ε i k q m| ≤ 1 / 2 := by
  have hK : 1 ≤ scaleIndex k q (m + 1) := one_le_scaleIndex hk
  have hKk : scaleIndex k q (m + 1) ≤ k := (scaleIndex_mem hk (by omega) (by omega)).2
  have hKN : 2 * scaleIndex k q (m + 1) = (N : ℕ) := by omega
  have hlow : lowScale k q m ≤ scaleIndex k q (m + 1) := lowScale_le hk
  have hs : 0 < P.val.2 := P.property.2.1
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  -- the radius dominates the length `N` of the full block
  have hR : ((N : ℕ) : ℝ) ≤ scaleRadius P ε k q m := by
    have hK' : (scaleIndex k q (m + 1) : ℝ) ≤ (k : ℝ) ^ (((m + 1 : ℕ) : ℝ) / q) :=
      scaleIndex_le_rpow
    have hmono : (k : ℝ) ^ (((m + 1 : ℕ) : ℝ) / q) ≤
        (k : ℝ) ^ (((m + 1 : ℕ) : ℝ) / q + ε / (P.val.2 + 2)) :=
      Real.rpow_le_rpow_of_exponent_le hk1 (by linarith [div_nonneg hε (by linarith : (0 : ℝ) ≤ P.val.2 + 2)])
    have hNK : ((N : ℕ) : ℝ) = 2 * (scaleIndex k q (m + 1) : ℝ) := by
      exact_mod_cast hKN.symm
    unfold scaleRadius
    linarith
  have hRpos : 0 < scaleRadius P ε k q m := scaleRadius_pos P ε hk q m
  have hzero : ∀ X : Configuration N,
      forcingPotential θ (cyclicRepStart N (scaleIndex k q (m + 1)) i)
        (cyclicRepSpan N (scaleIndex k q (m + 1))) (scaleRadius P ε k q m) X = 0 := by
    intro X
    refine forcingPotential_eq_zero hθ hRpos _ _ X ?_
    have hL : cyclicRepSpan N (scaleIndex k q (m + 1)) < (N : ℕ) :=
      cyclicRepSpan_lt hK (by omega)
    exact (blockLength_lt_N X _ hL).le.trans hR
  unfold scaleLaw
  rw [constrainedLaw_eq_gibbs_of_forcingPotential_zero P N θ _ _ _ hzero,
    integral_scaleIncrement_gibbs_eq P N hN i hk hkN hm]
  obtain ⟨h1, h2⟩ := cyclicCentre_mem hN (show 2 * lowScale k q m ≤ (N : ℕ) by omega) i
  obtain ⟨h3, h4⟩ := cyclicCentre_mem hN hKN.le i
  rw [abs_le]
  constructor <;> linarith

end Riesz1

end
