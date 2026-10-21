/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Rigidity.BlockAverage
public import Riesz1.Rigidity.ForcingComparison

/-!
# Multiscale increments and their constrained laws

This is part of Lemma 4.4. Fix `N ≥ 2`, a label `i`, a scale `1 ≤ k ≤ ⌊N/2⌋`, and an
integer `q ≥ 1`. The definitions below do not need the restriction `q ≥ max(2, 2/ε)` or the
constraints on `s, β, ε`, so the results hold in that generality. This file defines:

* the scales `k_m = ⌊k^{m/q}⌋` (`scaleIndex`), with `k_q = k` (`scaleIndex_self`).
* the increments `G_0 = N (x_i - x_i^{[k_1]})` and `G_m = N (x_i^{[k_m]} - x_i^{[k_{m+1}]})` for
  `m ≥ 1` (`scaleIncrement`).
* the radii `R_m = 2 k^{(m+1)/q + ε/(s+2)}` (`scaleRadius`), with `s = P.val.2`.
* the constrained laws `Q_m` (`scaleLaw`): the constrained law on the block
  `B_m = J_{k_{m+1}}(i)`, with the cutoff `θ` at scale `R_m`. The block is passed to
  `Riesz1.constrainedLaw` as its first label and its gap count.

The results are:

* `sum_scaleIncrement`: the telescoping identity `∑_{m<q} G_m = N (x_i - x_i^{[k]})`.
* `measurable_scaleIncrement`: each `G_m` is measurable, and `scaleIncrement_add_N`: the
  increments are invariant under `i ↦ i + N`.
* `cyclicRep_scaleIndex_bijOn`: the labels of `B_m` have distinct residues modulo `N`.
* `isProbabilityMeasure_scaleLaw`: each `Q_m` is a probability measure.
-/

@[expose] public section

open MeasureTheory Finset

namespace Riesz1

/-! ### Scales and radii -/

/-- The integer scale `k_m = ⌊k^{m/q}⌋` of Lemma 4.4. -/
noncomputable def scaleIndex (k q m : ℕ) : ℕ :=
  ⌊(k : ℝ) ^ ((m : ℝ) / q)⌋₊

/-- The radius `R_m = 2 k^{(m+1)/q + ε/(s+2)}` of Lemma 4.4, with
`s = P.val.2` the exponent of the Gibbs law. -/
noncomputable def scaleRadius (P : Parameters) (ε : ℝ) (k q m : ℕ) : ℝ :=
  2 * (k : ℝ) ^ (((m + 1 : ℕ) : ℝ) / q + ε / (P.val.2 + 2))

/-- The scale `k_q` is `k`. -/
theorem scaleIndex_self {k q : ℕ} (hq : 0 < q) : scaleIndex k q q = k := by
  unfold scaleIndex
  rw [div_self (Nat.cast_ne_zero.2 hq.ne'), Real.rpow_one, Nat.floor_natCast]

/-- For `1 ≤ k` and `m ≤ q`, the scale satisfies `1 ≤ k_m ≤ k`, so `J_{k_m}(i)` is a legitimate block of
the range of Lemma 4.4. -/
theorem scaleIndex_mem {k q m : ℕ} (hk : 1 ≤ k) (hm : m ≤ q) (hq : 0 < q) :
    1 ≤ scaleIndex k q m ∧ scaleIndex k q m ≤ k := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hexp : (m : ℝ) / q ≤ 1 := by
    rw [div_le_one (by exact_mod_cast hq)]
    exact_mod_cast hm
  have hlow : (1 : ℝ) ≤ (k : ℝ) ^ ((m : ℝ) / q) := Real.one_le_rpow hk' (by positivity)
  have hup : (k : ℝ) ^ ((m : ℝ) / q) ≤ k := by
    calc (k : ℝ) ^ ((m : ℝ) / q) ≤ (k : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hk' hexp
      _ = k := Real.rpow_one _
  constructor
  · exact Nat.le_floor (by exact_mod_cast hlow)
  · have h0 : (0 : ℝ) ≤ (k : ℝ) ^ ((m : ℝ) / q) := by positivity
    have := Nat.floor_le h0
    exact_mod_cast this.trans hup

/-- The radius `R_m` is positive when `k ≥ 1`. -/
theorem scaleRadius_pos (P : Parameters) (ε : ℝ) {k : ℕ} (hk : 1 ≤ k) (q m : ℕ) :
    0 < scaleRadius P ε k q m := by
  have hk' : (0 : ℝ) < k := Nat.cast_pos.2 (by omega)
  unfold scaleRadius
  exact mul_pos two_pos (Real.rpow_pos_of_pos hk' _)

/-! ### Increments -/

/-- The multiscale increment `G_m` of Lemma 4.4: `G_0 = N (x_i - x_i^{[k_1]})`
and, for `m ≥ 1`, `G_m = N (x_i^{[k_m]} - x_i^{[k_{m+1}]})`. -/
noncomputable def scaleIncrement {N : ℕ+} (i : ℤ) (k q m : ℕ) (X : Configuration N) : ℝ :=
  if m = 0 then
    ((N : ℕ) : ℝ) * (cyclicLift X i - blockAverage X i (scaleIndex k q 1))
  else
    ((N : ℕ) : ℝ) *
      (blockAverage X i (scaleIndex k q m) - blockAverage X i (scaleIndex k q (m + 1)))

/-- The increments telescope: `G_0 + ⋯ + G_{n-1} = N (x_i - x_i^{[k_n]})` for every `n ≥ 1`. -/
theorem sum_scaleIncrement_range {N : ℕ+} (i : ℤ) (k q : ℕ) (X : Configuration N) {n : ℕ}
    (hn : 1 ≤ n) :
    ∑ m ∈ range n, scaleIncrement i k q m X =
      ((N : ℕ) : ℝ) * (cyclicLift X i - blockAverage X i (scaleIndex k q n)) := by
  induction n, hn using Nat.le_induction with
  | base => simp [scaleIncrement]
  | succ n hn ih =>
    rw [sum_range_succ, ih]
    simp only [scaleIncrement, show n ≠ 0 by omega, ↓reduceIte]
    ring

/-- The telescoping identity of Lemma 4.4:
`∑_{m<q} G_m = N (x_i - x_i^{[k]})`. -/
theorem sum_scaleIncrement {N : ℕ+} (i : ℤ) (k : ℕ) {q : ℕ} (hq : 0 < q) (X : Configuration N) :
    ∑ m ∈ range q, scaleIncrement i k q m X = ((N : ℕ) : ℝ) * (cyclicLift X i - blockAverage X i k) := by
  rw [sum_scaleIncrement_range i k q X hq, scaleIndex_self hq]

/-- Each increment is a measurable function of the configuration. -/
theorem measurable_scaleIncrement {N : ℕ+} (i : ℤ) (k q m : ℕ) :
    Measurable fun X : Configuration N => scaleIncrement i k q m X := by
  unfold scaleIncrement
  by_cases hm : m = 0
  · simp only [hm, ↓reduceIte]
    exact measurable_const.mul ((measurable_cyclicLift i).sub (measurable_blockAverage _ _))
  · simp only [hm, ↓reduceIte]
    exact measurable_const.mul ((measurable_blockAverage _ _).sub (measurable_blockAverage _ _))

/-- Each block average at scale `k_m ≥ 1` is at least one: `1 ≤ k_m`. -/
theorem one_le_scaleIndex {k q m : ℕ} (hk : 1 ≤ k) : 1 ≤ scaleIndex k q m := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  refine Nat.le_floor (by exact_mod_cast Real.one_le_rpow hk' (by positivity))

/-- The increments are invariant under `i ↦ i + N`, since every block average moves by one. -/
theorem scaleIncrement_add_N {N : ℕ+} (i : ℤ) {k q : ℕ} (hk : 1 ≤ k) (m : ℕ)
    (X : Configuration N) :
    scaleIncrement (i + ((N : ℕ) : ℤ)) k q m X = scaleIncrement i k q m X := by
  unfold scaleIncrement
  by_cases hm : m = 0
  · simp only [hm, ↓reduceIte, cyclicLift_add_N]
    rw [blockAverage_add_N X i (one_le_scaleIndex hk)]
    ring
  · simp only [hm, ↓reduceIte]
    rw [blockAverage_add_N X i (one_le_scaleIndex hk), blockAverage_add_N X i (one_le_scaleIndex hk)]
    ring

/-! ### Blocks and constrained laws -/

/-- The labels of the block `B_m = J_{k_{m+1}}(i)` are the interval from `cyclicRepStart` of length
`cyclicRepSpan`, for `1 ≤ k_{m+1}`. This is the block that `constrainedLaw` takes. -/
theorem scaleBlock_eq_Icc {k q m : ℕ} (hk : 1 ≤ k) (hm : m < q) (hq : 0 < q) (N : ℕ+) (i : ℤ) :
    cyclicRep N (scaleIndex k q (m + 1)) i =
      Finset.Icc (cyclicRepStart N (scaleIndex k q (m + 1)) i)
        (cyclicRepStart N (scaleIndex k q (m + 1)) i + cyclicRepSpan N (scaleIndex k q (m + 1))) :=
  cyclicRep_eq_Icc (scaleIndex_mem hk (by omega : m + 1 ≤ q) hq).1 i

/-- The labels of `B_m` have distinct residues modulo `N`, when `2k ≤ N`: the reduction of
`B_m` is a bijection onto its neighbourhood. -/
theorem cyclicRep_scaleIndex_bijOn {N : ℕ+} {k q m : ℕ} (hk : 1 ≤ k) (hkN : 2 * k ≤ (N : ℕ))
    (hm : m < q) (hq : 0 < q) (i : ℤ) :
    Set.BijOn (fun j : ℤ => (j : ZMod (N : ℕ))) (cyclicRep N (scaleIndex k q (m + 1)) i : Set ℤ)
      (cyclicNbhd N (scaleIndex k q (m + 1)) i) := by
  have h : scaleIndex k q (m + 1) ≤ k := (scaleIndex_mem hk (by omega : m + 1 ≤ q) hq).2
  exact cyclicRep_bijOn (by omega) i

/-- The constrained law `Q_m` of Lemma 4.4: the constrained law
on the block `B_m = J_{k_{m+1}}(i)`, with the cutoff `θ` at scale `R_m`. -/
noncomputable def scaleLaw (P : Parameters) (N : ℕ+) (θ : ℝ → ℝ) (ε : ℝ) (i : ℤ) (k q m : ℕ) :
    Measure (Configuration N) :=
  constrainedLaw P N θ (cyclicRepStart N (scaleIndex k q (m + 1)) i)
    (cyclicRepSpan N (scaleIndex k q (m + 1))) (scaleRadius P ε k q m)

/-- Each constrained law `Q_m` is a probability measure, for every forcing cutoff `θ` and `k ≥ 1`. -/
theorem isProbabilityMeasure_scaleLaw (P : Parameters) (N : ℕ+) {θ : ℝ → ℝ}
    (hθ : IsForcingCutoff θ) (ε : ℝ) (i : ℤ) {k : ℕ} (hk : 1 ≤ k) (q m : ℕ) :
    IsProbabilityMeasure (scaleLaw P N θ ε i k q m) :=
  isProbabilityMeasure_constrainedLaw P N hθ (scaleRadius_pos P ε hk q m) _ _

end Riesz1

end
