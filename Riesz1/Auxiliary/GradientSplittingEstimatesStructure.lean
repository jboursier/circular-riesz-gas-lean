/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.GradientSplittingIdentityMain
public import Riesz1.Auxiliary.GradientSplittingGapMain

/-!
# Structural statements and translation of the gradient splitting event

Support, label reindexing, and invariance of the event under common real
translation, for the estimates part of Lemma 5.7.
-/

@[expose] public section

namespace Riesz1

noncomputable section

/-- The label and particle versions of `V` agree on the window. -/
lemma gradEst_Vfield_eq_lab {s ℓ γ : ℝ} {N : ℕ+} (ψ : ℝ → ℝ)
    (X : Fin (N : ℕ) → ℝ) (hℓ : 0 ≤ ℓ) {i : ℤ} (hi : i ∈ gradLabels N ℓ γ) :
    gradVfield s ψ N ℓ γ X (gradIndex N i) = gradVlab s ψ N ℓ γ X i := by
  classical
  unfold gradVfield
  apply Finset.sum_eq_single i
  · intro j hj hji
    obtain ⟨hjI, hjindex⟩ := Finset.mem_filter.mp hj
    exact False.elim ((gradIndex_ne_of_mem_labels hℓ hjI hi hji) hjindex)
  · intro h
    exact False.elim (h (Finset.mem_filter.mpr ⟨hi, rfl⟩))

/-- The two fields vanish at every particle absent from the window. -/
lemma gradEst_fields_support {s ℓ γ : ℝ} {N : ℕ+} (ψ : ℝ → ℝ)
    (X : Fin (N : ℕ) → ℝ) (k : Fin (N : ℕ))
    (hk : ∀ i ∈ gradLabels N ℓ γ, gradIndex N i ≠ k) :
    gradVfield s ψ N ℓ γ X k = 0 ∧ gradWfield s ψ N ℓ γ X k = 0 := by
  classical
  have hfilter : (gradLabels N ℓ γ).filter (fun i => gradIndex N i = k) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    exact hk i (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hi).2
  simp [gradVfield, gradWfield, hfilter]

/-- A gap coefficient can be nonzero only on an edge whose two endpoints
belong to the window, with endpoints interpreted cyclically in a full window. -/
lemma gradEst_gap_support {s ℓ γ : ℝ} {N : ℕ+} (ψ : ℝ → ℝ)
    (X : Fin (N : ℕ) → ℝ) {e : ℤ} (he : e ∈ Finset.Ico (0 : ℤ) N)
    (hout : ¬∃ i ∈ gradLabels N ℓ γ, gradInWindow N ℓ γ (i + 1) ∧ i % (N : ℤ) = e) :
    gradWgap s ψ N ℓ γ X e = 0 := by
  by_cases hP : GradPartial N ℓ γ
  · apply gradWgap_eq_zero_of_partial ψ X hP e
    intro j hj0 hj1 hje
    apply hout
    refine ⟨j, (mem_gradLabels_partial hP j).mpr ⟨hj0, hj1.le⟩, ?_, hje⟩
    intro _
    exact (mem_gradLabels_partial hP (j + 1)).mpr ⟨by omega, by omega⟩
  · exfalso
    apply hout
    have he' := Finset.mem_Ico.mp he
    refine ⟨e, (mem_gradLabels_full hP e).mpr he', fun hp => (hP hp).elim, ?_⟩
    exact Int.emod_eq_of_lt he'.1 he'.2

/-- Summing over particle coordinates is the same as summing over the window labels. -/
lemma gradEst_sum_Vfield {s ℓ γ : ℝ} {N : ℕ+} (ψ : ℝ → ℝ)
    (X : Fin (N : ℕ) → ℝ) :
    ∑ k : Fin (N : ℕ), gradVfield s ψ N ℓ γ X k
      = ∑ i ∈ gradLabels N ℓ γ, gradVlab s ψ N ℓ γ X i := by
  classical
  simp only [gradVfield, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp

/-- A common translation adds the same real number to every cyclic lift. -/
lemma gradEst_lift_translate (N : ℕ+) (X : Fin (N : ℕ) → ℝ) (c : ℝ) (i : ℤ) :
    gradLift N (fun k => X k + c) i = gradLift N X i + c := by
  simp only [gradLift]
  ring

/-- The event depends only on differences and is therefore translation invariant. -/
lemma gradEst_event_translate_iff (s γ ε : ℝ) (N : ℕ+) (ℓ : ℝ)
    (X : Fin (N : ℕ) → ℝ) (c : ℝ) :
    gradEvent s γ ε N ℓ (fun k => X k + c) ↔ gradEvent s γ ε N ℓ X := by
  simp only [gradEvent, gradEst_lift_translate, add_sub_add_right_eq_sub]

/-- Translation preserves the ordered lift chart as long as its anchor stays
in the chart's fundamental interval. -/
lemma gradEst_ordered_translate {N : ℕ+} {X : Fin (N : ℕ) → ℝ}
    (hX : X ∈ orderedDomain N) (c : ℝ)
    (h0 : 0 ≤ X ⟨0, N.pos⟩ + c) (h1 : X ⟨0, N.pos⟩ + c < 1) :
    (fun k => X k + c) ∈ orderedDomain N := by
  refine ⟨fun i j hij => by dsimp; linarith [hX.1 hij], h0, h1, ?_⟩
  intro i
  linarith [hX.2.2.2 i]

end

end Riesz1
