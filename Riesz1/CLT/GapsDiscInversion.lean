/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.CLT.GapsDiscDefs
public import Riesz1.Rigidity.Inversion

/-!
# Deterministic selected-count inversion

The event identities and signed block identities of the
inversion argument for Corollary 1. No probabilistic hypothesis is needed.
-/

@[expose] public section

noncomputable section

open MeasureTheory Finset

namespace Riesz1

variable {N : ℕ+}

lemma measurable_gapWindowCount (i : ℤ) (t : ℝ) :
    Measurable (fun X : Configuration N => (gapWindowIndices X i t).card) := by
  have hm : Measurable (fun X : Configuration N =>
      ∑ a ∈ range ((N : ℕ) - 1),
        if cyclicLift X (i + 1 + a) ≤ cyclicLift X i + t then (1 : ℕ) else 0) := by
    apply Finset.measurable_sum
    intro a _
    exact Measurable.ite (measurableSet_le (measurable_cyclicLift _)
      ((measurable_cyclicLift _).add_const t)) measurable_const measurable_const
  simpa [gapWindowIndices] using hm

lemma measurable_selectedCount (k : ℕ) (hk : k < (N : ℕ)) :
    Measurable (fun X : Configuration N => selectedCount X k hk) := by
  have hm : Measurable (fun q : Configuration N × ℤ =>
      (gapWindowIndices q.1 q.2 ((k : ℝ) / (N : ℝ))).card) :=
    measurable_from_prod_countable_left (fun i => measurable_gapWindowCount i _)
  exact hm.comp (measurable_id.prodMk (measurable_nearestLabel N))

lemma measurable_selectedDiscrepancy (k : ℕ) (hk : k < (N : ℕ)) :
    Measurable (fun X : Configuration N => selectedDiscrepancy X k hk) :=
  ((Measurable.of_discrete : Measurable (fun n : ℕ => (n : ℤ))).comp
    (measurable_selectedCount k hk)).sub_const _

/-- Membership in the finite window corresponds exactly to a lifted particle in `(x_i,x_i+t]`.
This also certifies that the definition counts all integer labels. -/
lemma gapWindowIndices_spec (X : Configuration N) (i j : ℤ) (t : ℝ) (ht : t < 1) :
    (∃ a ∈ gapWindowIndices X i t, j = i + 1 + a) ↔
      cyclicLift X i < cyclicLift X j ∧ cyclicLift X j ≤ cyclicLift X i + t := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨-, ha⟩ := mem_filter.mp ha
    exact ⟨cyclicLift_strictMono X (by omega), ha⟩
  · rintro ⟨hlo, hhi⟩
    have hij : i < j := (cyclicLift_strictMono X).lt_iff_lt.mp hlo
    have hjN : j < i + (N : ℕ) := by
      apply (cyclicLift_strictMono X).lt_iff_lt.mp
      rw [cyclicLift_add_N]
      linarith
    refine ⟨(j - i - 1).toNat, ?_, ?_⟩
    · apply mem_filter.mpr
      constructor
      · apply mem_range.mpr
        omega
      · have heq : i + 1 + ((j - i - 1).toNat : ℤ) = j := by omega
        simpa only [heq] using hhi
    · omega

lemma selectedCount_window_iff (X : Configuration N) (k : ℕ) (hk : k < (N : ℕ))
    (q : ℕ) (hq0 : 1 ≤ q) (hqN : q < (N : ℕ)) :
    q ≤ selectedCount X k hk ↔
      blockLength X (nearestLabel X) q ≤ k := by
  let p : ℕ → Prop := fun a => cyclicLift X (nearestLabel X + 1 + a) ≤
    cyclicLift X (nearestLabel X) + (k : ℝ) / (N : ℝ)
  have hp : ∀ a b, a ≤ b → p b → p a := by
    intro a b hab hb
    exact ((cyclicLift_strictMono X).monotone (by omega)).trans hb
  have hh := lt_card_filter_iff (M := (N : ℕ) - 1) p hp
    (r := q - 1) (by omega)
  have heq : nearestLabel X + 1 + ((q - 1 : ℕ) : ℤ) = nearestLabel X + q := by
    omega
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  change q ≤ ((range ((N : ℕ) - 1)).filter p).card ↔ _
  rw [show q ≤ ((range ((N : ℕ) - 1)).filter p).card ↔
      q - 1 < ((range ((N : ℕ) - 1)).filter p).card by omega, ← hh]
  dsimp [p]
  rw [heq]
  unfold blockLength
  constructor
  · intro h
    have h' := (le_div_iff₀ hN).mp (show
      cyclicLift X (nearestLabel X + q) - cyclicLift X (nearestLabel X) ≤
        (k : ℝ) / (N : ℝ) by linarith)
    nlinarith
  · intro h
    have h' := (le_div_iff₀ hN).mpr (show
      (cyclicLift X (nearestLabel X + q) - cyclicLift X (nearestLabel X)) * (N : ℝ) ≤ k
        by nlinarith)
    linarith

lemma selectedIncrement_eq_blockLength (X : Configuration N) (k : ℕ) (r : ℤ)
    (hr : 0 ≤ (k : ℤ) + r) :
    selectedIncrement X k r =
      blockLength X (nearestLabel X) ((k : ℤ) + r).toNat -
        blockLength X (nearestLabel X) k - r := by
  unfold selectedIncrement blockLength
  rw [Int.toNat_of_nonneg hr]
  rw [show nearestLabel X + ((k : ℤ) + r) = nearestLabel X + k + r by ring]
  ring

lemma selectedIncrement_zero (X : Configuration N) (k : ℕ) :
    selectedIncrement X k 0 = 0 := by
  simp [selectedIncrement]

lemma selectedIncrement_nonneg_index (X : Configuration N) (k r : ℕ) :
    selectedIncrement X k r = blockLength X (nearestLabel X + k) r - r := by
  rfl

lemma selectedIncrement_neg_index (X : Configuration N) (k r : ℕ) :
    selectedIncrement X k (-(r : ℤ)) =
      -(blockLength X (nearestLabel X + k - r) r - r) := by
  unfold selectedIncrement blockLength
  simp only [Int.cast_neg, Int.cast_natCast]
  rw [show nearestLabel X + k + -(r : ℤ) = nearestLabel X + k - r by ring]
  rw [sub_add_cancel]
  ring

/-- The first event identity of the inversion lemma, including the right endpoint. -/
theorem selectedDiscrepancy_ge_iff (X : Configuration N) (k : ℕ)
    (hk : k < (N : ℕ)) (r : ℤ) (hr0 : 1 ≤ (k : ℤ) + r)
    (hrN : (k : ℤ) + r < (N : ℕ)) :
    r ≤ selectedDiscrepancy X k hk ↔
      blockLength X (nearestLabel X) ((k : ℤ) + r).toNat ≤ k := by
  have hq : (((k : ℤ) + r).toNat : ℤ) = (k : ℤ) + r := Int.toNat_of_nonneg (by omega)
  have hcount := selectedCount_window_iff X k hk ((k : ℤ) + r).toNat
    (by omega) (by omega)
  rw [← hcount]
  unfold selectedDiscrepancy
  omega

/-- Both event identities of the inversion argument for Corollary 1, pointwise. -/
theorem selectedDiscrepancy_inversion (k : ℕ) (hk : k < (N : ℕ)) (r : ℤ)
    (hr0 : 1 ≤ (k : ℤ) + r) (hrN : (k : ℤ) + r < (N : ℕ)) :
    {X : Configuration N | r ≤ selectedDiscrepancy X k hk} =
      {X | blockLength X (nearestLabel X) ((k : ℤ) + r).toNat ≤ k} ∧
    {X : Configuration N | r ≤ selectedDiscrepancy X k hk} =
      {X | blockLength X (nearestLabel X) k - k + (r : ℝ) +
        selectedIncrement X k r ≤ 0} := by
  constructor
  · ext X
    exact selectedDiscrepancy_ge_iff X k hk r hr0 hrN
  · ext X
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, selectedDiscrepancy_ge_iff X k hk r hr0 hrN,
      selectedIncrement_eq_blockLength X k r (by omega)]
    constructor <;> intro h <;> linarith

end Riesz1

end
end
