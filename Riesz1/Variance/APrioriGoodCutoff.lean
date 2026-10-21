/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.Window
public import Riesz1.Rigidity.Gaps
public import Riesz1.ToMathlib.MollifierPointwise.Circle
public import Riesz1.ToMathlib.Packing.UnitProduct

/-!
# The good-event cutoff and the good event

The scalar cutoff, the good event `A_{ε,γ}` and the good-event cutoff `η_{ε,γ}`, used in the
proof of Lemma 5.2.

The paper's window `I_γ` is `Riesz1.window N K γ` of `Riesz1/Variance/Window.lean`, and the
scale is `K`. The paper's `ℓ = K / N` enters only through `K`. A pair `(i, k)` of the
paper, with `i, i + k ∈ I_γ` and `0 < |k| ≤ ⌊N/2⌋`, is a `Fin N × ℤ` element of
`cutoffPairs N I`, with `i + k` read as the label `labelOf N (i + k)`. The nearest-neighbour
pairs `(i, i + 1)` are `nearestPairs N I` of the window file, and the gap `N (x_{i+1} - x_i)` is
`Riesz1.gap X i`.

* `scalarCutoff r = min(1, max(0, 2 - r))`.
* `pairDev N X p = N (x_{i+k} - x_i) - k` for a pair `p = (i, k)`.
* `goodCutoff N s K γ ε X` is the product of the pair factors and of the two nearest-neighbour
  factors. It is a value in `[0, 1]` for every configuration.
* `goodEvent N s K γ ε` is the set `A_{ε,γ}` of configurations where every pair deviation is at
  most `K^ε |k|^{s/2}` and every nearest gap lies in `[K^{-ε}, K^ε]`.
-/

@[expose] public section

noncomputable section

open Finset

namespace Riesz1

/-! ### The scalar cutoff -/

/-- The scalar cutoff `c(r) = min(1, max(0, 2 - r))`. -/
def scalarCutoff (r : ℝ) : ℝ := min 1 (max 0 (2 - r))

theorem scalarCutoff_nonneg (r : ℝ) : 0 ≤ scalarCutoff r :=
  le_min zero_le_one (le_max_left _ _)

theorem scalarCutoff_le_one (r : ℝ) : scalarCutoff r ≤ 1 :=
  min_le_left _ _

/-- The cutoff equals one on `r ≤ 1`. -/
theorem scalarCutoff_eq_one_of_le_one {r : ℝ} (hr : r ≤ 1) : scalarCutoff r = 1 := by
  unfold scalarCutoff
  exact min_eq_left (le_max_of_le_right (by linarith))

/-- The cutoff equals zero on `2 ≤ r`. -/
theorem scalarCutoff_eq_zero_of_two_le {r : ℝ} (hr : 2 ≤ r) : scalarCutoff r = 0 := by
  unfold scalarCutoff
  have h0 : max 0 (2 - r) = 0 := max_eq_left (by linarith)
  rw [h0, min_eq_right zero_le_one]

/-- The cutoff is strictly below one exactly on `1 < r`. -/
theorem scalarCutoff_lt_one_iff (r : ℝ) : scalarCutoff r < 1 ↔ 1 < r := by
  unfold scalarCutoff
  constructor
  · intro h
    by_contra hr
    push Not at hr
    have h1 : 1 ≤ max 0 (2 - r) := le_max_of_le_right (by linarith)
    have h2 : 1 ≤ min 1 (max 0 (2 - r)) := le_min le_rfl h1
    linarith
  · intro hr
    exact min_lt_iff.2 (Or.inr (max_lt zero_lt_one (by linarith)))

/-! ### The pair index set and the deviations -/

/-- The pairs `(i, k)`: the label `i` and the label `i + k` both lie in
the window `I`, and `0 < |k| ≤ ⌊N/2⌋`. -/
def cutoffPairs (N : ℕ+) (I : Finset (Fin (N : ℕ))) : Finset (Fin (N : ℕ) × ℤ) :=
  (Finset.univ ×ˢ ((Icc (-(((N : ℕ) / 2 : ℕ) : ℤ)) (((N : ℕ) / 2 : ℕ) : ℤ)).erase 0)).filter
    fun p => p.1 ∈ I ∧ labelOf N (((p.1 : ℕ) : ℤ) + p.2) ∈ I

/-- The deviation `N (x_{i+k} - x_i) - k` of a pair `p = (i, k)`. -/
def pairDev (N : ℕ+) (X : Configuration N) (p : Fin (N : ℕ) × ℤ) : ℝ :=
  ((N : ℕ) : ℝ) * (cyclicLift X (((p.1 : ℕ) : ℤ) + p.2) - cyclicLift X ((p.1 : ℕ) : ℤ)) - p.2

/-- The tolerance `K^ε |k|^{s/2}` of a pair `p = (i, k)`. -/
def pairScale {N : ℕ+} (s K ε : ℝ) (p : Fin (N : ℕ) × ℤ) : ℝ :=
  K ^ ε * ((p.2.natAbs : ℕ) : ℝ) ^ (s / 2)

/-! ### The good-event cutoff `η_{ε,γ}` -/

/-- The good-event cutoff `η_{ε,γ}`, evaluated on a configuration.
The first product runs over the pairs of `cutoffPairs`, the second over the nearest-neighbour
pairs of the window. -/
def goodCutoff (N : ℕ+) (s K γ ε : ℝ) (X : Configuration N) : ℝ :=
  (∏ p ∈ cutoffPairs N (window N K γ),
      scalarCutoff (2 * |pairDev N X p| / pairScale s K ε p)) *
    ∏ i ∈ nearestPairs N (window N K γ),
      (scalarCutoff (2 * gap X ((i : ℕ) : ℤ) / K ^ ε) *
        scalarCutoff (2 / (K ^ ε * gap X ((i : ℕ) : ℤ))))

/-- The good event `A_{ε,γ}`: every pair deviation is at most its
tolerance, and every nearest-neighbour gap lies in `[K^{-ε}, K^ε]`. -/
def goodEvent (N : ℕ+) (s K γ ε : ℝ) : Set (Configuration N) :=
  {X | (∀ p ∈ cutoffPairs N (window N K γ), |pairDev N X p| ≤ pairScale s K ε p) ∧
    ∀ i ∈ nearestPairs N (window N K γ),
      K ^ (-ε) ≤ gap X ((i : ℕ) : ℤ) ∧ gap X ((i : ℕ) : ℤ) ≤ K ^ ε}

/-! ### Values and support of `η_{ε,γ}` -/

/-- Each pair factor lies in `[0, 1]`. -/
theorem goodCutoff_nonneg (N : ℕ+) (s K γ ε : ℝ) (X : Configuration N) :
    0 ≤ goodCutoff N s K γ ε X := by
  unfold goodCutoff
  apply mul_nonneg
  · exact Finset.prod_nonneg fun p _ => scalarCutoff_nonneg _
  · exact Finset.prod_nonneg fun i _ => mul_nonneg (scalarCutoff_nonneg _) (scalarCutoff_nonneg _)

/-- The good-event cutoff takes values in `[0, 1]`. -/
theorem goodCutoff_le_one (N : ℕ+) (s K γ ε : ℝ) (X : Configuration N) :
    goodCutoff N s K γ ε X ≤ 1 := by
  unfold goodCutoff
  have h1 := prod_mem_unitInterval (cutoffPairs N (window N K γ))
    (fun p => scalarCutoff (2 * |pairDev N X p| / pairScale s K ε p))
    (fun p _ => scalarCutoff_nonneg _) (fun p _ => scalarCutoff_le_one _)
  have h2 := prod_mem_unitInterval (nearestPairs N (window N K γ))
    (fun i => scalarCutoff (2 * gap X ((i : ℕ) : ℤ) / K ^ ε) *
      scalarCutoff (2 / (K ^ ε * gap X ((i : ℕ) : ℤ))))
    (fun i _ => mul_nonneg (scalarCutoff_nonneg _) (scalarCutoff_nonneg _))
    (fun i _ => mul_le_one_of_unitInterval (scalarCutoff_nonneg _) (scalarCutoff_le_one _)
      (scalarCutoff_le_one _))
  calc (∏ p ∈ cutoffPairs N (window N K γ),
          scalarCutoff (2 * |pairDev N X p| / pairScale s K ε p)) *
        ∏ i ∈ nearestPairs N (window N K γ),
          (scalarCutoff (2 * gap X ((i : ℕ) : ℤ) / K ^ ε) *
            scalarCutoff (2 / (K ^ ε * gap X ((i : ℕ) : ℤ))))
      ≤ 1 * 1 := mul_le_mul h1.2 h2.2 h2.1 zero_le_one
    _ = 1 := one_mul 1

/-- **Failure of the cutoff.** If `η_{ε,γ}(X) ≠ 1`, then one of three events occurs: a pair
deviation exceeds half its tolerance, a nearest-neighbour gap exceeds `K^ε / 2`, or a
nearest-neighbour gap lies below `2 K^{-ε}`. -/
theorem exists_failure_of_goodCutoff_ne_one (N : ℕ+) (s K γ ε : ℝ) (X : Configuration N)
    (h : goodCutoff N s K γ ε X ≠ 1) :
    (∃ p ∈ cutoffPairs N (window N K γ), 1 < 2 * |pairDev N X p| / pairScale s K ε p) ∨
    (∃ i ∈ nearestPairs N (window N K γ), 1 < 2 * gap X ((i : ℕ) : ℤ) / K ^ ε) ∨
    (∃ i ∈ nearestPairs N (window N K γ), 1 < 2 / (K ^ ε * gap X ((i : ℕ) : ℤ))) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hp, hn1, hn2⟩ := hcon
  apply h
  unfold goodCutoff
  rw [Finset.prod_eq_one fun p hp' => scalarCutoff_eq_one_of_le_one (hp p hp'), one_mul,
    Finset.prod_eq_one fun i hi => by
      rw [scalarCutoff_eq_one_of_le_one (hn1 i hi), scalarCutoff_eq_one_of_le_one (hn2 i hi),
        one_mul]]

/-- **Support of the cutoff.** If `η_{ε,γ}(X) ≠ 0`, then the configuration lies in the good event,
provided `K > 0` and `s > 0`. -/
theorem goodEvent_of_goodCutoff_ne_zero (N : ℕ+) {s K γ ε : ℝ} (hK : 0 < K)
    {X : Configuration N} (hX : goodCutoff N s K γ ε X ≠ 0) :
    X ∈ goodEvent N s K γ ε := by
  unfold goodCutoff at hX
  have hP : (∏ p ∈ cutoffPairs N (window N K γ),
      scalarCutoff (2 * |pairDev N X p| / pairScale s K ε p)) ≠ 0 :=
    left_ne_zero_of_mul hX
  have hQ : (∏ i ∈ nearestPairs N (window N K γ),
      (scalarCutoff (2 * gap X ((i : ℕ) : ℤ) / K ^ ε) *
        scalarCutoff (2 / (K ^ ε * gap X ((i : ℕ) : ℤ))))) ≠ 0 :=
    right_ne_zero_of_mul hX
  rw [Finset.prod_ne_zero_iff] at hP hQ
  have hKε : 0 < K ^ ε := Real.rpow_pos_of_pos hK ε
  -- Pair deviations: a nonzero factor forces the argument below two.
  have hpair : ∀ p ∈ cutoffPairs N (window N K γ), |pairDev N X p| ≤ pairScale s K ε p := by
    intro p hp
    have h0 := hP p hp
    have hlt : 2 * |pairDev N X p| / pairScale s K ε p < 2 := by
      by_contra hge
      push Not at hge
      exact h0 (scalarCutoff_eq_zero_of_two_le hge)
    have hk : 0 < pairScale s K ε p := by
      unfold pairScale
      have hnat : (1 : ℝ) ≤ ((p.2.natAbs : ℕ) : ℝ) := by
        have hp2 : p.2 ≠ 0 := by
          have := (Finset.mem_erase.1 (Finset.mem_product.1 (Finset.mem_filter.1 hp).1).2).1
          exact this
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hp2)
      exact mul_pos hKε (Real.rpow_pos_of_pos (by linarith) _)
    rw [div_lt_iff₀ hk] at hlt
    linarith
  refine ⟨hpair, fun i hi => ?_⟩
  have h0 := hQ i hi
  have hgap : 0 < gap X ((i : ℕ) : ℤ) := gap_pos X _
  have hf : scalarCutoff (2 * gap X ((i : ℕ) : ℤ) / K ^ ε) ≠ 0 := (mul_ne_zero_iff.1 h0).1
  have hg : scalarCutoff (2 / (K ^ ε * gap X ((i : ℕ) : ℤ))) ≠ 0 := (mul_ne_zero_iff.1 h0).2
  have hu : 2 * gap X ((i : ℕ) : ℤ) / K ^ ε < 2 := by
    by_contra hge
    push Not at hge
    exact hf (scalarCutoff_eq_zero_of_two_le hge)
  have hv : 2 / (K ^ ε * gap X ((i : ℕ) : ℤ)) < 2 := by
    by_contra hge
    push Not at hge
    exact hg (scalarCutoff_eq_zero_of_two_le hge)
  rw [div_lt_iff₀ hKε] at hu
  rw [div_lt_iff₀ (mul_pos hKε hgap)] at hv
  constructor
  · -- Lower bound: `1 ≤ K^ε z` gives `K^{-ε} ≤ z`.
    have key : 1 ≤ K ^ ε * gap X ((i : ℕ) : ℤ) := by linarith
    rw [Real.rpow_neg hK.le]
    calc (K ^ ε)⁻¹ = (K ^ ε)⁻¹ * 1 := (mul_one _).symm
      _ ≤ (K ^ ε)⁻¹ * (K ^ ε * gap X ((i : ℕ) : ℤ)) :=
          mul_le_mul_of_nonneg_left key (inv_nonneg.2 hKε.le)
      _ = gap X ((i : ℕ) : ℤ) := by field_simp
  · linarith

end Riesz1

end
end
