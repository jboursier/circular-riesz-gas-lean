/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Rigidity.GapLaw
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Algebra.Order.Group.Int

/-!
# The nearest particle and its selection weight

For a configuration `X` of `N` particles, the nearest particle is the lift
`x_J` of smallest absolute value, with the smaller lifted position at a tie. Its integer label is
`J`, and the selection weight of label `i` is `w_i = (S_{i-1,1} + S_{i,1}) / 2`.

The label is computed from any lift sequence `L : ℤ → ℝ` that is `N`-periodic up to the shift by
one, `L (j + N) = L j + 1`. It is the least `i` with `0 ≤ L i + L (i+1)`, that is, the first label
whose midpoint with the next lift is nonnegative. Equivalently, it is the label `i` with
`L (i-1) + L i < 0 ≤ L i + L (i+1)` when the lifts are increasing (Lemma `nearestLabelOf_eq_iff`).

Index convention: the label `i` of the paper is the integer label `i - 1` of the lifts
`cyclicLift X`. The index `1` of the paper is the integer `0`, so `w_1` is `selectionWeight X 0`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Riesz1

/-! ### The nearest label of a lift sequence -/

/-- The nearest-particle label of a lift sequence `L`: the least integer `i` with
`0 ≤ L i + L (i+1)`. For increasing lifts this is the label of the lift nearest to `0`, with the
smaller lift chosen at a tie (`nearestLabel_isNearest`). -/
def nearestLabelOf (L : ℤ → ℝ) : ℤ :=
  sInf {i : ℤ | 0 ≤ L i + L (i + 1)}

/-- Shifting the index by a multiple of the period adds the same multiple to the lifts. -/
lemma lift_add_mul_eq {N : ℕ} (L : ℤ → ℝ) (hL : ∀ j, L (j + N) = L j + 1) (j q : ℤ) :
    L (j + (N : ℤ) * q) = L j + q := by
  refine Int.induction_on q ?_ ?_ ?_
  · simp
  · intro i ih
    have h := hL (j + N * i)
    rw [show j + (N : ℤ) * ((i : ℤ) + 1) = j + (N : ℤ) * i + N by ring, h, ih]
    push_cast
    ring
  · intro i ih
    have h := hL (j + N * (-(i : ℤ) - 1))
    rw [show j + (N : ℤ) * (-(i : ℤ) - 1) + N = j + (N : ℤ) * (-(i : ℤ)) by ring, ih] at h
    push_cast at h ⊢
    linarith

/-- The set defining `nearestLabelOf` is nonempty for every periodic lift sequence. -/
lemma nearestSet_nonempty {N : ℕ} (L : ℤ → ℝ) (hL : ∀ j, L (j + N) = L j + 1) :
    {i : ℤ | 0 ≤ L i + L (i + 1)}.Nonempty := by
  refine ⟨(N : ℤ) * ⌈-(L 0 + L 1) / 2⌉, ?_⟩
  have h0 := lift_add_mul_eq L hL 0 ⌈-(L 0 + L 1) / 2⌉
  have h1 := lift_add_mul_eq L hL 1 ⌈-(L 0 + L 1) / 2⌉
  have hc := Int.le_ceil (-(L 0 + L 1) / 2)
  show 0 ≤ L ((N : ℤ) * ⌈-(L 0 + L 1) / 2⌉) + L ((N : ℤ) * ⌈-(L 0 + L 1) / 2⌉ + 1)
  rw [zero_add] at h0
  rw [show (N : ℤ) * ⌈-(L 0 + L 1) / 2⌉ + 1 = 1 + (N : ℤ) * ⌈-(L 0 + L 1) / 2⌉ by ring, h1, h0]
  linarith

/-- The set defining `nearestLabelOf` is bounded below for every periodic lift sequence. -/
lemma nearestSet_bddBelow {N : ℕ} (hN : 0 < N) (L : ℤ → ℝ) (hL : ∀ j, L (j + N) = L j + 1) :
    BddBelow {i : ℤ | 0 ≤ L i + L (i + 1)} := by
  have hNz : (0 : ℤ) < N := by exact_mod_cast hN
  obtain ⟨r0, hr0, hmax⟩ := (Finset.Ico (0 : ℤ) N).exists_max_image (fun r => L r + L (r + 1))
    ⟨0, Finset.mem_Ico.mpr ⟨le_refl _, by exact_mod_cast hN⟩⟩
  set B := L r0 + L (r0 + 1) with hB
  refine ⟨(N : ℤ) * ⌈-B / 2⌉, fun i hi => ?_⟩
  have hi' : (0 : ℝ) ≤ L i + L (i + 1) := hi
  set r := i % N with hr
  set q := i / N with hq
  have hdecomp : i = r + (N : ℤ) * q := by
    have := Int.emod_def i N
    rw [hr, hq]
    linarith
  have hrmem : r ∈ Finset.Ico (0 : ℤ) N := by
    rw [Finset.mem_Ico]
    exact ⟨Int.emod_nonneg i hNz.ne', Int.emod_lt_of_pos i hNz⟩
  have hLi : L i = L r + q := by
    conv_lhs => rw [hdecomp]
    rw [lift_add_mul_eq L hL r q]
  have hLi1 : L (i + 1) = L (r + 1) + q := by
    rw [show i + 1 = (r + 1) + (N : ℤ) * q by rw [hdecomp]; ring, lift_add_mul_eq L hL (r + 1) q]
  have hle : L r + L (r + 1) ≤ B := hmax r hrmem
  have hq' : -B / 2 ≤ (q : ℝ) := by
    have : (0 : ℝ) ≤ (L r + L (r + 1)) + 2 * q := by
      rw [hLi, hLi1] at hi'
      linarith
    linarith
  have hceil : ⌈-B / 2⌉ ≤ q := Int.ceil_le.mpr hq'
  have hr0' : (0 : ℤ) ≤ r := Int.emod_nonneg i hNz.ne'
  have hqN : (N : ℤ) * ⌈-B / 2⌉ ≤ (N : ℤ) * q := mul_le_mul_of_nonneg_left hceil hNz.le
  have hqi : (N : ℤ) * q ≤ i := by
    rw [hdecomp]
    linarith
  exact le_trans hqN hqi

/-- The nearest label is the least element of its defining set. -/
lemma nearestLabelOf_mem {N : ℕ} (hN : 0 < N) (L : ℤ → ℝ) (hL : ∀ j, L (j + N) = L j + 1) :
    0 ≤ L (nearestLabelOf L) + L (nearestLabelOf L + 1) :=
  Int.csInf_mem (nearestSet_nonempty L hL) (nearestSet_bddBelow hN L hL)

/-- The nearest label is at most every element of its defining set. -/
lemma nearestLabelOf_le {N : ℕ} (hN : 0 < N) (L : ℤ → ℝ) (hL : ∀ j, L (j + N) = L j + 1)
    {i : ℤ} (hi : 0 ≤ L i + L (i + 1)) : nearestLabelOf L ≤ i :=
  csInf_le (nearestSet_bddBelow hN L hL) hi

/-- For a periodic lift sequence, the nearest label equals `k` exactly when the pair at `k` is
nonnegative and no smaller index has this property. -/
lemma nearestLabelOf_eq_iff_forall {N : ℕ} (hN : 0 < N) (L : ℤ → ℝ)
    (hL : ∀ j, L (j + N) = L j + 1) (k : ℤ) :
    nearestLabelOf L = k ↔
      0 ≤ L k + L (k + 1) ∧ ∀ i : ℤ, i < k → ¬ 0 ≤ L i + L (i + 1) := by
  constructor
  · rintro rfl
    refine ⟨nearestLabelOf_mem hN L hL, fun i hi hi0 => ?_⟩
    have := nearestLabelOf_le hN L hL hi0
    omega
  · rintro ⟨hk, hlt⟩
    refine le_antisymm (nearestLabelOf_le hN L hL hk) ?_
    by_contra h
    exact hlt _ (not_le.mp h) (nearestLabelOf_mem hN L hL)

/-- For increasing lifts, the nearest label is the unique index with `L (i-1) + L i < 0` and
`0 ≤ L i + L (i+1)`. -/
lemma nearestLabelOf_eq_iff {N : ℕ} (hN : 0 < N) (L : ℤ → ℝ) (hL : ∀ j, L (j + N) = L j + 1)
    (hmono : ∀ j, L j < L (j + 1)) (k : ℤ) :
    nearestLabelOf L = k ↔
      0 ≤ L k + L (k + 1) ∧ L (k - 1) + L k < 0 := by
  rw [nearestLabelOf_eq_iff_forall hN L hL k]
  have hmon : Monotone L := strictMono_int_of_lt_succ hmono |>.monotone
  constructor
  · rintro ⟨hk, hlt⟩
    refine ⟨hk, ?_⟩
    have := hlt (k - 1) (by omega)
    rw [show k - 1 + 1 = k by ring] at this
    linarith [not_le.mp this]
  · rintro ⟨hk, hprev⟩
    refine ⟨hk, fun i hi hi0 => ?_⟩
    have hle : L (i + 1) ≤ L k := hmon (show i + 1 ≤ k by omega)
    have hle' : L i ≤ L (k - 1) := hmon (show i ≤ k - 1 by omega)
    have hmid : L i + L (i + 1) ≤ L (k - 1) + L k := by
      have : L (i + 1) ≤ L k := hle
      have hi2 : L i ≤ L (k - 1) := hle'
      have : L (k - 1 + 1) = L k := by rw [show k - 1 + 1 = k by ring]
      linarith
    linarith

/-! ### The nearest particle of a configuration -/

/-- The nearest particle label `J` of a configuration: the least integer
`J` with `cyclicLift X J + cyclicLift X (J+1) ≥ 0`. -/
def nearestLabel {N : ℕ+} (X : Configuration N) : ℤ :=
  nearestLabelOf (cyclicLift X)

/-- The gap vector of a configuration, relabelled to start at the integer label `i`. -/
def gapFrom {N : ℕ+} (X : Configuration N) (i : ℤ) : Fin (N : ℕ) → ℝ :=
  fun k => gap X (i + k)

/-- The selection weight of the integer label `i`, `w_i = (S_{i-1,1} + S_{i,1}) / 2`, which is
`N (x_{i+1} - x_{i-1}) / 2`. The `w_1` of the paper is `selectionWeight X 0`. -/
def selectionWeight {N : ℕ+} (X : Configuration N) (i : ℤ) : ℝ :=
  (gap X (i - 1) + gap X i) / 2

/-- The lifts of a configuration are `N`-periodic up to the shift by one. -/
lemma cyclicLift_periodic {N : ℕ+} (X : Configuration N) :
    ∀ j : ℤ, cyclicLift X (j + ((N : ℕ) : ℤ)) = cyclicLift X j + 1 :=
  fun j => cyclicLift_add_N X j

/-- The nearest label of a configuration satisfies the two-sided sign condition. -/
lemma nearestLabel_eq_iff {N : ℕ+} (X : Configuration N) (k : ℤ) :
    nearestLabel X = k ↔
      0 ≤ cyclicLift X k + cyclicLift X (k + 1) ∧
        cyclicLift X (k - 1) + cyclicLift X k < 0 :=
  nearestLabelOf_eq_iff (N := (N : ℕ)) N.pos (cyclicLift X) (cyclicLift_periodic X)
    (fun j => cyclicLift_lt_succ X j) k

/-- The nearest particle is at distance at most half the span of its two neighbouring gaps, so
`N |x_J| ≤ w_J`. -/
lemma nearest_abs_le_selectionWeight {N : ℕ+} (X : Configuration N) :
    ((N : ℕ) : ℝ) * |cyclicLift X (nearestLabel X)| ≤ selectionWeight X (nearestLabel X) := by
  set J := nearestLabel X with hJ
  obtain ⟨hA, hB⟩ : 0 ≤ cyclicLift X J + cyclicLift X (J + 1) ∧
      cyclicLift X (J - 1) + cyclicLift X J < 0 :=
    (nearestLabel_eq_iff X J).mp rfl
  have h1 : cyclicLift X J < cyclicLift X (J + 1) := cyclicLift_lt_succ X J
  have h2 : cyclicLift X (J - 1) < cyclicLift X J := by
    have := cyclicLift_lt_succ X (J - 1)
    rwa [sub_add_cancel] at this
  have hbound : |cyclicLift X J| ≤
      (cyclicLift X (J + 1) - cyclicLift X (J - 1)) / 2 := by
    rw [abs_le]
    constructor <;> linarith
  have hN : (0 : ℝ) < ((N : ℕ) : ℝ) := by exact_mod_cast N.pos
  have hw : selectionWeight X J =
      ((N : ℕ) : ℝ) * ((cyclicLift X (J + 1) - cyclicLift X (J - 1)) / 2) := by
    unfold selectionWeight gap
    rw [show J - 1 + 1 = J by ring]
    ring
  rw [hw]
  exact mul_le_mul_of_nonneg_left hbound hN.le

/-- The nearest particle is the lift of smallest absolute value, and at a tie it is the smaller
lift: every other label `j` has `|x_J| < |x_j|`, or `|x_J| = |x_j|` with `x_J < x_j`. -/
lemma nearestLabel_isNearest {N : ℕ+} (X : Configuration N) (j : ℤ) (hj : j ≠ nearestLabel X) :
    |cyclicLift X (nearestLabel X)| < |cyclicLift X j| ∨
      (|cyclicLift X (nearestLabel X)| = |cyclicLift X j| ∧
        cyclicLift X (nearestLabel X) < cyclicLift X j) := by
  set J := nearestLabel X with hJ
  obtain ⟨hA, hB⟩ : 0 ≤ cyclicLift X J + cyclicLift X (J + 1) ∧
      cyclicLift X (J - 1) + cyclicLift X J < 0 :=
    (nearestLabel_eq_iff X J).mp rfl
  have hmon := (cyclicLift_strictMono X).monotone
  rcases lt_or_gt_of_ne hj with hlt | hgt
  · -- the label `j` lies below `J`, so `x_j < x_J` and `x_j ≤ x_{J-1} < -x_J`
    have hxj : cyclicLift X j < cyclicLift X J := cyclicLift_strictMono X (show j < J by omega)
    have hxj' : cyclicLift X j ≤ cyclicLift X (J - 1) := hmon (by omega)
    left
    rcases le_total 0 (cyclicLift X J) with h0 | h0
    · rw [abs_of_nonneg h0, abs_of_neg (show cyclicLift X j < 0 by linarith)]
      linarith
    · rw [abs_of_nonpos h0, abs_of_neg (show cyclicLift X j < 0 by linarith)]
      linarith
  · -- the label `j` lies above `J`, so `x_j ≥ x_{J+1} ≥ -x_J` and `x_J < x_j`
    have hxj : cyclicLift X (J + 1) ≤ cyclicLift X j := hmon (by omega)
    have hlt' : cyclicLift X J < cyclicLift X j := cyclicLift_strictMono X (show J < j by omega)
    rcases le_total 0 (cyclicLift X J) with h0 | h0
    · left
      rw [abs_of_nonneg h0, abs_of_pos (show 0 < cyclicLift X j by linarith)]
      exact hlt'
    · have hpos : 0 ≤ cyclicLift X j := by linarith
      rw [abs_of_nonpos h0, abs_of_nonneg hpos]
      rcases lt_or_eq_of_le (show -cyclicLift X J ≤ cyclicLift X j by linarith) with h | h
      · left
        exact h
      · right
        exact ⟨by linarith, hlt'⟩

end Riesz1

end

end
