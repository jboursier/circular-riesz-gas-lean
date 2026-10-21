/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.CLT.GapsDiscInversion
public import Riesz1.CLT.GapsDiscStripsShift
public import Riesz1.CLT.GapsDiscCountsNormal
public import Riesz1.CLT.SelectionBounds
public import Riesz1.Gibbs.FluctuationMoments

/-!
# Tail bound for the selected count

Part of the proof of Corollary 1. For the selected discrepancy `Δ` and
the centred open-arc count `C` of the arc `(0, k/N)`, the probability `P(|Δ - C| > M)` is at most
`C₀/R + 4R/M`, where `C₀` is the square of the second selection moment constant.

The proof has four steps. Markov's inequality bounds the event `R ≤ N |x_J|` by the second
selection moment. Off this event, a deterministic comparison bounds `|Δ - C|` by the number of
particles in two open arcs of radius `R/N`, about `0` and about `k/N`. Uniform marginals give the
expectation of that number, which is `4R`, and Markov's inequality finishes the proof.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Riesz1

variable {N : ℕ+}

/-- The centred open-arc count `C_N(0, k/N)` of the selected count: the open arc of half-width
`k/(2N)` about the centre `k/(2N)`, centred by `k`. -/
def selectedCentredCount (N : ℕ+) (k : ℕ) (X : Configuration N) : ℝ :=
  arcCount (((k : ℝ) / (2 * ((N : ℕ) : ℝ)) : ℝ) : UnitAddCircle)
    ((k : ℝ) / (2 * ((N : ℕ) : ℝ))) X - k

/-! ### Circle geometry -/

lemma selCnt_arcIndicator_nonneg (c : UnitAddCircle) (a : ℝ) (x : UnitAddCircle) :
    0 ≤ arcIndicator c a x := by
  unfold arcIndicator
  split_ifs <;> norm_num

lemma selCnt_arcIndicator_le_one (c : UnitAddCircle) (a : ℝ) (x : UnitAddCircle) :
    arcIndicator c a x ≤ 1 := by
  unfold arcIndicator
  split_ifs <;> norm_num

lemma selCnt_arcIndicator_eq_one (c : UnitAddCircle) (a : ℝ) (x : UnitAddCircle)
    (h : dist x c < a) : arcIndicator c a x = 1 := by
  unfold arcIndicator
  rw [ite_eq_left h]

/-- The circle distance between two real lifts is at most the distance to any integer shift. -/
lemma selCnt_dist_le_abs_sub_int (u v : ℝ) (m : ℤ) :
    dist (u : UnitAddCircle) (v : UnitAddCircle) ≤ |u - v - m| := by
  rw [dist_coe_coe_eq]
  exact round_le (u - v) m

/-- The circle distance from a real lift to `0` is at most the distance to an integer. -/
lemma selCnt_dist_zero_le (u : ℝ) (m : ℤ) : dist (u : UnitAddCircle) 0 ≤ |u - m| := by
  have h := selCnt_dist_le_abs_sub_int u 0 m
  rw [AddCircle.coe_zero, sub_zero] at h
  exact h

/-- **Agreement off the boundary.** Let `ℓ` lie in `(L, L + 1)` with `|L| < r`, and suppose the
circle class of `ℓ` lies at distance at least `r` from `0` and from `t`. Then `ℓ ≤ L + t` holds
exactly when the class of `ℓ` lies in the open arc of half-width `t/2` about `t/2`. -/
lemma selCnt_agree (L t r ℓ : ℝ) (hr4 : r < 1 / 4) (hL : |L| < r) (hlo : L < ℓ)
    (hhi : ℓ < L + 1) (h0 : r ≤ dist (ℓ : UnitAddCircle) 0)
    (ht : r ≤ dist (ℓ : UnitAddCircle) (t : UnitAddCircle)) :
    ℓ ≤ L + t ↔ dist (ℓ : UnitAddCircle) ((t / 2 : ℝ) : UnitAddCircle) < t / 2 := by
  have hLr : L < r := lt_of_le_of_lt (le_abs_self L) hL
  have hLl : -r < L := by linarith [neg_abs_le L]
  constructor
  · intro hle
    rcases le_or_gt ℓ 0 with h1 | h1
    · -- `ℓ ≤ 0`: then `|ℓ| < r`, so the class of `ℓ` is within `r` of `0`
      exfalso
      have hd := selCnt_dist_zero_le ℓ 0
      rw [Int.cast_zero, sub_zero, abs_of_nonpos h1] at hd
      linarith [neg_le_abs L]
    rcases le_or_gt t ℓ with h2 | h2
    · -- `t ≤ ℓ`: then `0 ≤ ℓ - t ≤ L < r`, so the class of `ℓ` is within `r` of `t`
      exfalso
      have hd := selCnt_dist_le_abs_sub_int ℓ t 0
      rw [Int.cast_zero, sub_zero, abs_of_nonneg (by linarith : (0 : ℝ) ≤ ℓ - t)] at hd
      linarith
    · -- `0 < ℓ < t`: the class of `ℓ` lies in the open arc
      have hd := selCnt_dist_le_abs_sub_int ℓ (t / 2) 0
      rw [Int.cast_zero, sub_zero] at hd
      have hlt : |ℓ - t / 2| < t / 2 := abs_lt.mpr ⟨by linarith, by linarith⟩
      exact lt_of_le_of_lt hd hlt
  · intro hd
    by_contra hc
    push Not at hc
    rw [dist_coe_coe_eq] at hd
    have hn := abs_lt.mp hd
    generalize round (ℓ - t / 2) = n at hn
    have hn1 : (-1 : ℝ) < n := by linarith [hn.2]
    have hn2 : (n : ℝ) < 2 := by linarith [hn.1]
    have hn1' : (-1 : ℤ) < n := by exact_mod_cast hn1
    have hn2' : n < 2 := by exact_mod_cast hn2
    rcases (show n = 0 ∨ n = 1 by omega) with rfl | rfl
    · -- `n = 0`: `0 < ℓ < t` and `ℓ - t > -r`, so the class of `ℓ` is within `r` of `t`
      push_cast at hn
      have hd2 := selCnt_dist_le_abs_sub_int ℓ t 0
      rw [Int.cast_zero, sub_zero] at hd2
      have hlt : |ℓ - t| < r := abs_lt.mpr ⟨by linarith, by linarith⟩
      linarith
    · -- `n = 1`: `0 < ℓ - 1 < r`, so the class of `ℓ` is within `r` of `0`
      push_cast at hn
      have hd2 := selCnt_dist_le_abs_sub_int ℓ 0 1
      rw [AddCircle.coe_zero, Int.cast_one, sub_zero] at hd2
      have hlt : |ℓ - 1| < r := abs_lt.mpr ⟨by linarith, by linarith⟩
      linarith

/-- **Pointwise comparison.** For a real `ℓ` in `(L, L + 1]` with `|L| < r`, the difference
between the window indicator `1_{ℓ ≤ L + t}` and the arc indicator of the open arc `(0, t)` is
bounded by the sum of the indicators of the open arcs of radius `r` about `0` and about `t`. -/
lemma selCnt_pointwise (L t r ℓ : ℝ) (hr4 : r < 1 / 4) (hL : |L| < r) (hlo : L < ℓ)
    (hhi : ℓ ≤ L + 1) :
    |(if ℓ ≤ L + t then (1 : ℝ) else 0) -
        arcIndicator ((t / 2 : ℝ) : UnitAddCircle) (t / 2) (ℓ : UnitAddCircle)| ≤
      arcIndicator 0 r (ℓ : UnitAddCircle) + arcIndicator (t : UnitAddCircle) r (ℓ : UnitAddCircle) := by
  by_cases hball : dist (ℓ : UnitAddCircle) 0 < r ∨
      dist (ℓ : UnitAddCircle) (t : UnitAddCircle) < r
  · have hA : 1 ≤ arcIndicator 0 r (ℓ : UnitAddCircle) +
        arcIndicator (t : UnitAddCircle) r (ℓ : UnitAddCircle) := by
      have h1 := selCnt_arcIndicator_nonneg (t : UnitAddCircle) r (ℓ : UnitAddCircle)
      have h2 := selCnt_arcIndicator_nonneg 0 r (ℓ : UnitAddCircle)
      rcases hball with h | h
      · rw [selCnt_arcIndicator_eq_one 0 r _ h]
        linarith
      · rw [selCnt_arcIndicator_eq_one (t : UnitAddCircle) r _ h]
        linarith
    have hg0 : 0 ≤ (if ℓ ≤ L + t then (1 : ℝ) else 0) := by
      split_ifs <;> norm_num
    have hg1 : (if ℓ ≤ L + t then (1 : ℝ) else 0) ≤ 1 := by
      split_ifs <;> norm_num
    have hh0 := selCnt_arcIndicator_nonneg ((t / 2 : ℝ) : UnitAddCircle) (t / 2) (ℓ : UnitAddCircle)
    have hh1 := selCnt_arcIndicator_le_one ((t / 2 : ℝ) : UnitAddCircle) (t / 2) (ℓ : UnitAddCircle)
    rw [abs_le]
    constructor <;> linarith
  · push Not at hball
    obtain ⟨h0, ht⟩ := hball
    have hℓ : ℓ < L + 1 := by
      rcases lt_or_eq_of_le hhi with h | h
      · exact h
      · exfalso
        have hd := selCnt_dist_zero_le ℓ 1
        have e : ℓ - ((1 : ℤ) : ℝ) = L := by
          push_cast
          linarith
        rw [e] at hd
        linarith
    have hag := selCnt_agree L t r ℓ hr4 hL hlo hℓ h0 ht
    have hgh : (if ℓ ≤ L + t then (1 : ℝ) else 0) =
        arcIndicator ((t / 2 : ℝ) : UnitAddCircle) (t / 2) (ℓ : UnitAddCircle) := by
      unfold arcIndicator
      by_cases hle : ℓ ≤ L + t
      · rw [ite_eq_left hle, ite_eq_left (hag.mp hle)]
      · rw [ite_eq_right hle, ite_eq_right (fun h => hle (hag.mpr h))]
    rw [hgh, sub_self, abs_zero]
    exact add_nonneg (selCnt_arcIndicator_nonneg _ _ _) (selCnt_arcIndicator_nonneg _ _ _)

/-! ### Periodic sums over one period of labels -/

/-- Shifting a window of `n` consecutive labels by one leaves its sum unchanged for an
`n`-periodic function. -/
lemma selCnt_shift_step (G : ℤ → ℝ) (n : ℕ) (hG : ∀ j, G (j + n) = G j) (c : ℤ) :
    ∑ a ∈ Finset.range n, G (c + 1 + (a : ℤ)) = ∑ a ∈ Finset.range n, G (c + (a : ℤ)) := by
  have h1 := Finset.sum_range_succ (fun a : ℕ => G (c + (a : ℤ))) n
  have h2 := Finset.sum_range_succ' (fun a : ℕ => G (c + (a : ℤ))) n
  have h3 : ∑ a ∈ Finset.range n, G (c + ((a + 1 : ℕ) : ℤ)) =
      ∑ a ∈ Finset.range n, G (c + 1 + (a : ℤ)) :=
    Finset.sum_congr rfl fun a _ => by
      congr 1
      push_cast
      ring
  have h4 : G (c + (n : ℤ)) = G c := hG c
  rw [h4] at h1
  simp only [Nat.cast_zero, add_zero] at h2
  rw [← h3]
  linarith

/-- For an `n`-periodic function, the window sum of `n` consecutive labels starting at `c` does
not depend on `c`. -/
lemma selCnt_sum_shift_invariant (G : ℤ → ℝ) (n : ℕ) (hG : ∀ j, G (j + n) = G j) (c : ℤ) :
    ∑ a ∈ Finset.range n, G (c + (a : ℤ)) = ∑ a ∈ Finset.range n, G (a : ℤ) := by
  induction c using Int.induction_on with
  | zero => simp
  | succ i ih =>
    rw [selCnt_shift_step G n hG (i : ℤ), ih]
  | pred i ih =>
    have h := selCnt_shift_step G n hG (-(i : ℤ) - 1)
    rw [sub_add_cancel] at h
    rw [← h]
    exact ih

/-- A window of `N` consecutive lifts, read through the circle, is a sum over the particles.
The lifts `cyclicLift X j` with `j` in one period cover each particle once. -/
lemma selCnt_sum_cyclicLift (A : UnitAddCircle → ℝ) (X : Configuration N) (c : ℤ) :
    ∑ a ∈ Finset.range (N : ℕ), A ((cyclicLift X (c + (a : ℤ)) : ℝ) : UnitAddCircle) =
      linearStatistic A X := by
  have hper : ∀ j : ℤ, A ((cyclicLift X (j + ((N : ℕ) : ℤ)) : ℝ) : UnitAddCircle) =
      A ((cyclicLift X j : ℝ) : UnitAddCircle) := by
    intro j
    rw [cyclicLift_add_N]
    congr 1
    exact AddCircle.coe_add_period 1 (cyclicLift X j)
  have key := selCnt_sum_shift_invariant
    (fun j : ℤ => A ((cyclicLift X j : ℝ) : UnitAddCircle)) (N : ℕ) hper c
  have hfin : ∑ a ∈ Finset.range (N : ℕ), A ((cyclicLift X (a : ℤ) : ℝ) : UnitAddCircle) =
      ∑ i : Fin (N : ℕ), A ((X.val i : ℝ) : UnitAddCircle) := by
    rw [← Fin.sum_univ_eq_sum_range (fun a : ℕ => A ((cyclicLift X (a : ℤ) : ℝ) : UnitAddCircle))
      (N : ℕ)]
    exact Finset.sum_congr rfl fun i _ => by rw [cyclicLift_natCast]
  exact key.trans (hfin.trans rfl)

/-! ### The window count as a sum over one period -/

/-- The selected count is the sum over the `N` labels after the nearest label of the indicator
that the lift does not exceed the nearest lift plus `t`. -/
lemma selCnt_sum_window (X : Configuration N) (t : ℝ) (ht1 : t < 1) :
    ((gapWindowIndices X (nearestLabel X) t).card : ℝ) =
      ∑ a ∈ Finset.range (N : ℕ), (if cyclicLift X (nearestLabel X + 1 + (a : ℤ)) ≤
        cyclicLift X (nearestLabel X) + t then (1 : ℝ) else 0) := by
  have hNpos : 0 < (N : ℕ) := N.pos
  have hsplit := Finset.sum_range_succ (fun a : ℕ => (if cyclicLift X (nearestLabel X + 1 + (a : ℤ))
      ≤ cyclicLift X (nearestLabel X) + t then (1 : ℝ) else 0)) ((N : ℕ) - 1)
  rw [show (N : ℕ) - 1 + 1 = (N : ℕ) by omega] at hsplit
  have hlast : (if cyclicLift X (nearestLabel X + 1 + (((N : ℕ) - 1 : ℕ) : ℤ)) ≤
      cyclicLift X (nearestLabel X) + t then (1 : ℝ) else 0) = 0 := by
    have e : nearestLabel X + 1 + (((N : ℕ) - 1 : ℕ) : ℤ) = nearestLabel X + ((N : ℕ) : ℤ) := by
      omega
    have hnot : ¬ (cyclicLift X (nearestLabel X) + 1 ≤ cyclicLift X (nearestLabel X) + t) := by
      intro h
      linarith
    rw [e, cyclicLift_add_N, ite_eq_right hnot]
  rw [hsplit, hlast, add_zero]
  unfold gapWindowIndices
  rw [Finset.card_filter]
  push_cast
  rfl

/-- **Deterministic comparison.** Off the event `|x_J| ≥ R/N`, the window count and the open-arc
count differ by at most the number of particles in the two arcs of radius `r` about `0` and `t`. -/
lemma selCnt_deviation (X : Configuration N) (t r : ℝ) (ht1 : t < 1) (hr4 : r < 1 / 4)
    (hL : |cyclicLift X (nearestLabel X)| < r) :
    |((gapWindowIndices X (nearestLabel X) t).card : ℝ) -
        arcCount ((t / 2 : ℝ) : UnitAddCircle) (t / 2) X| ≤
      linearStatistic (fun x => arcIndicator 0 r x + arcIndicator (t : UnitAddCircle) r x) X := by
  have hArc : arcCount ((t / 2 : ℝ) : UnitAddCircle) (t / 2) X =
      ∑ a ∈ Finset.range (N : ℕ), arcIndicator ((t / 2 : ℝ) : UnitAddCircle) (t / 2)
        ((cyclicLift X (nearestLabel X + 1 + (a : ℤ)) : ℝ) : UnitAddCircle) :=
    (selCnt_sum_cyclicLift (arcIndicator ((t / 2 : ℝ) : UnitAddCircle) (t / 2)) X
      (nearestLabel X + 1)).symm
  rw [selCnt_sum_window X t ht1, hArc, ← Finset.sum_sub_distrib,
    ← selCnt_sum_cyclicLift (fun x => arcIndicator 0 r x + arcIndicator (t : UnitAddCircle) r x) X
      (nearestLabel X + 1)]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a ha => ?_)
  have ha' : a < (N : ℕ) := Finset.mem_range.mp ha
  have hlo : cyclicLift X (nearestLabel X) < cyclicLift X (nearestLabel X + 1 + (a : ℤ)) :=
    cyclicLift_strictMono X (by omega)
  have hhi : cyclicLift X (nearestLabel X + 1 + (a : ℤ)) ≤ cyclicLift X (nearestLabel X) + 1 := by
    have h := (cyclicLift_strictMono X).monotone
      (show nearestLabel X + 1 + (a : ℤ) ≤ nearestLabel X + ((N : ℕ) : ℤ) by omega)
    rwa [cyclicLift_add_N] at h
  exact selCnt_pointwise (cyclicLift X (nearestLabel X)) t r _ hr4 hL hlo hhi

/-! ### Measurability -/

lemma measurable_cyclicLift_nearest (N : ℕ+) :
    Measurable (fun X : Configuration N => cyclicLift X (nearestLabel X)) := by
  have h : Measurable (fun q : Configuration N × ℤ => cyclicLift q.1 q.2) :=
    measurable_from_prod_countable_left (fun j : ℤ => measurable_cyclicLift (N := N) j)
  exact h.comp (measurable_id.prodMk (measurable_nearestLabel N))

/-! ### The tail bound -/

/-- **Selected count tail** (part of the proof of Corollary 1). Under
`External.PrekopaLeindler`, there is a constant `C > 0`, depending only on `beta` and `s`, such
that for all `N`, `1 ≤ k ≤ N/2`, `N ≥ 2`, `R, M > 0` with `R/N < 1/4`, the Gibbs probability of
`|Δ_{N,k} - C_N(0, k/N)| > M` is at most `C/R + 4R/M`. -/
theorem selected_count_tail (hPL : External.PrekopaLeindler) (beta s : ℝ) (hbeta : 0 < beta)
    (hs : 0 < s) (hs1 : s < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (k : ℕ) (hk : k < (N : ℕ)), 1 ≤ k → 2 * k ≤ (N : ℕ) →
      2 ≤ (N : ℕ) → ∀ R M : ℝ, 0 < R → 0 < M → R / (N : ℝ) < 1 / 4 →
        gibbsMeasure ⟨(beta, s), hbeta, hs, hs1⟩ N
          {X | M < |((selectedDiscrepancy X k hk : ℤ) : ℝ) - selectedCentredCount N k X|} ≤
            ENNReal.ofReal (C / R + 4 * R / M) := by
  obtain ⟨Cm, hCm, hmom⟩ := nearest_selection_moments hPL
  refine ⟨Cm ^ 2, pow_pos hCm 2, fun N k hk hk1 hk2 hN2 R M hR hM hRN => ?_⟩
  set P : Parameters := ⟨(beta, s), hbeta, hs, hs1⟩ with hP
  obtain ⟨r, hr_def⟩ : ∃ r : ℝ, r = R / ((N : ℕ) : ℝ) := ⟨_, rfl⟩
  obtain ⟨t, ht_def⟩ : ∃ t : ℝ, t = (k : ℝ) / ((N : ℕ) : ℝ) := ⟨_, rfl⟩
  have hNpos : (0 : ℝ) < ((N : ℕ) : ℝ) := by exact_mod_cast N.pos
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hkN : (k : ℝ) < ((N : ℕ) : ℝ) := by exact_mod_cast hk
  have ht1 : t < 1 := by
    rw [ht_def, div_lt_one hNpos]
    exact hkN
  have hr : 0 < r := by
    rw [hr_def]
    exact div_pos hR hNpos
  have hr4 : r < 1 / 4 := by
    rw [hr_def]
    exact hRN
  have hrR : ((N : ℕ) : ℝ) * r = R := by
    rw [hr_def]
    field_simp
  have hr_half : r ≤ 1 / 2 := by linarith
  -- the centred count is the arc count of the arc about `t/2`
  have hcent : ∀ X : Configuration N, selectedCentredCount N k X =
      arcCount ((t / 2 : ℝ) : UnitAddCircle) (t / 2) X - k := by
    intro X
    have e : (k : ℝ) / (2 * ((N : ℕ) : ℝ)) = ((k : ℝ) / ((N : ℕ) : ℝ)) / 2 := by
      rw [div_div, mul_comm]
    unfold selectedCentredCount
    rw [e, ht_def]
  -- the selected discrepancy is the window count minus `k`
  have hdisc : ∀ X : Configuration N, ((selectedDiscrepancy X k hk : ℤ) : ℝ) =
      ((gapWindowIndices X (nearestLabel X) t).card : ℝ) - k := by
    intro X
    rw [ht_def]
    unfold selectedDiscrepancy selectedCount
    push_cast
    rfl
  -- the arc-indicator sum that dominates the deviation
  set φ : UnitAddCircle → ℝ := fun x => arcIndicator 0 r x + arcIndicator (t : UnitAddCircle) r x
    with hφ
  have hφm : MemLp φ 2 volume :=
    (memLp_arcIndicator_real 0 r).add (memLp_arcIndicator_real (t : UnitAddCircle) r)
  have hφint : ∫ x, φ x = 4 * r := by
    rw [hφ]
    simp only
    rw [integral_add ((memLp_arcIndicator_real 0 r).integrable one_le_two)
      ((memLp_arcIndicator_real (t : UnitAddCircle) r).integrable one_le_two),
      integral_arcIndicator 0 hr.le hr_half,
      integral_arcIndicator (t : UnitAddCircle) hr.le hr_half]
    ring
  have hSint : ∫ X, linearStatistic φ X ∂(gibbsMeasure P N) = 4 * R := by
    rw [integral_linearStatistic P N hφm, hφint, ← hrR]
    ring
  have hSi : Integrable (fun X : Configuration N => linearStatistic φ X) (gibbsMeasure P N) :=
    integrable_linearStatistic P N hφm
  have hS0 : 0 ≤ᵐ[gibbsMeasure P N] (fun X : Configuration N => linearStatistic φ X) :=
    ae_of_all _ fun X => Finset.sum_nonneg fun i _ =>
      add_nonneg (selCnt_arcIndicator_nonneg _ _ _) (selCnt_arcIndicator_nonneg _ _ _)
  -- Markov's inequality for the arc-indicator sum
  have hB_bd : gibbsMeasure P N {X | M ≤ linearStatistic φ X} ≤
      ENNReal.ofReal (4 * R / M) := by
    calc gibbsMeasure P N {X | M ≤ linearStatistic φ X}
        ≤ gibbsMeasure P N {X | ENNReal.ofReal M ≤ ENNReal.ofReal (linearStatistic φ X)} :=
          measure_mono fun X hX => ENNReal.ofReal_le_ofReal hX
      _ ≤ (∫⁻ X, ENNReal.ofReal (linearStatistic φ X) ∂(gibbsMeasure P N)) /
            ENNReal.ofReal M :=
          meas_ge_le_lintegral_div hSi.aemeasurable.ennreal_ofReal
            (ENNReal.ofReal_pos.mpr hM).ne' ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal (4 * R) / ENNReal.ofReal M := by
          rw [← ofReal_integral_eq_lintegral_ofReal hSi hS0, hSint]
      _ = ENNReal.ofReal (4 * R / M) := (ENNReal.ofReal_div_of_pos hM).symm
  -- Markov's inequality for the nearest particle
  have hJmeas : Measurable (fun X : Configuration N =>
      ENNReal.ofReal (((N : ℕ) : ℝ) * |cyclicLift X (nearestLabel X)|)) :=
    ENNReal.measurable_ofReal.comp
      (measurable_const.mul (continuous_abs.measurable.comp (measurable_cyclicLift_nearest N)))
  have hA_bd : gibbsMeasure P N {X | R ≤ ((N : ℕ) : ℝ) * |cyclicLift X (nearestLabel X)|} ≤
      ENNReal.ofReal (Cm ^ 2 / R) := by
    calc gibbsMeasure P N {X | R ≤ ((N : ℕ) : ℝ) * |cyclicLift X (nearestLabel X)|}
        ≤ gibbsMeasure P N {X | ENNReal.ofReal R ≤
            ENNReal.ofReal (((N : ℕ) : ℝ) * |cyclicLift X (nearestLabel X)|)} :=
          measure_mono fun X hX => ENNReal.ofReal_le_ofReal hX
      _ ≤ (∫⁻ X, ENNReal.ofReal (((N : ℕ) : ℝ) * |cyclicLift X (nearestLabel X)|)
            ∂(gibbsMeasure P N)) / ENNReal.ofReal R :=
          meas_ge_le_lintegral_div hJmeas.aemeasurable (ENNReal.ofReal_pos.mpr hR).ne'
            ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (Cm ^ 2) / ENNReal.ofReal R :=
          ENNReal.div_le_div_right ((hmom P N hN2).2) _
      _ = ENNReal.ofReal (Cm ^ 2 / R) := (ENNReal.ofReal_div_of_pos hR).symm
  -- the event is contained in the union of the two Markov events
  have hsub : {X : Configuration N | M < |((selectedDiscrepancy X k hk : ℤ) : ℝ) -
      selectedCentredCount N k X|} ⊆
      {X : Configuration N | R ≤ ((N : ℕ) : ℝ) * |cyclicLift X (nearestLabel X)|} ∪
        {X : Configuration N | M ≤ linearStatistic φ X} := by
    intro X hX
    by_cases hA : R ≤ ((N : ℕ) : ℝ) * |cyclicLift X (nearestLabel X)|
    · exact Or.inl hA
    · right
      push Not at hA
      have hL : |cyclicLift X (nearestLabel X)| < r := by
        rw [hr_def, lt_div_iff₀ hNpos, mul_comm]
        exact hA
      have hdev := selCnt_deviation X t r ht1 hr4 hL
      have key : |((selectedDiscrepancy X k hk : ℤ) : ℝ) - selectedCentredCount N k X| ≤
          linearStatistic φ X := by
        rw [hdisc X, hcent X, show ((gapWindowIndices X (nearestLabel X) t).card : ℝ) - k -
          (arcCount ((t / 2 : ℝ) : UnitAddCircle) (t / 2) X - k) =
          ((gapWindowIndices X (nearestLabel X) t).card : ℝ) -
          arcCount ((t / 2 : ℝ) : UnitAddCircle) (t / 2) X by ring]
        exact hdev
      exact le_of_lt (lt_of_lt_of_le hX key)
  calc gibbsMeasure P N {X : Configuration N | M < |((selectedDiscrepancy X k hk : ℤ) : ℝ) -
        selectedCentredCount N k X|}
      ≤ gibbsMeasure P N ({X : Configuration N | R ≤ ((N : ℕ) : ℝ) * |cyclicLift X (nearestLabel X)|} ∪
          {X : Configuration N | M ≤ linearStatistic φ X}) := measure_mono hsub
    _ ≤ gibbsMeasure P N {X : Configuration N | R ≤ ((N : ℕ) : ℝ) * |cyclicLift X (nearestLabel X)|} +
          gibbsMeasure P N {X : Configuration N | M ≤ linearStatistic φ X} :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal (Cm ^ 2 / R) + ENNReal.ofReal (4 * R / M) := add_le_add hA_bd hB_bd
    _ = ENNReal.ofReal (Cm ^ 2 / R + 4 * R / M) :=
        (ENNReal.ofReal_add (div_nonneg (sq_nonneg _) hR.le)
          (div_nonneg (by linarith) hM.le)).symm

end Riesz1

end
end
