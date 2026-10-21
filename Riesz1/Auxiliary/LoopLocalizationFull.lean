/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopLocalMomentsIntegral
public import Riesz1.Auxiliary.GradientSplittingConvolutionParticle

/-!
# The full-window localization identity

The exact full-window assertion of the localization part of Lemma 5.8.
The preceding-particle lifts are reindexed modulo the microscopic period.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace Riesz1

/-- A periodic test sees the preceding lift as the original particle with the
corresponding residue label. -/
theorem loopPrecedingLift_periodic_eval {N : ℕ+} (X : LoopPrecedingConfiguration N)
    {f : ℝ → ℝ} (hf : Function.Periodic f (N : ℝ)) (j : ℤ) :
    f (loopPrecedingLift X j) =
      f (loopArcPos N X.val (gradIndex N (loopPrecedingLabel X + j))) := by
  have he : loopPrecedingLift X j =
      loopArcPos N X.val (gradIndex N (loopPrecedingLabel X + j)) +
        (((loopPrecedingLabel X + j) / (N : ℤ) : ℤ) : ℝ) * N := by
    unfold loopPrecedingLift cyclicLift loopArcPos gradIndex
    ring
  rw [he]
  exact hf.int_mul ((loopPrecedingLabel X + j) / (N : ℤ)) _

/-- Summing a periodic test over a full preceding-particle window sums each
particle exactly once. -/
theorem sum_loopPrecedingLift_full {N : ℕ+} (X : LoopPrecedingConfiguration N)
    {f : ℝ → ℝ} (hf : Function.Periodic f (N : ℝ)) :
    (∑ j ∈ Finset.Ico (0 : ℤ) (N : ℤ), f (loopPrecedingLift X j)) =
      ∑ i : Fin (N : ℕ), f (loopArcPos N X.val i) := by
  classical
  let J := loopPrecedingLabel X
  have hN : (0 : ℤ) < N := by exact_mod_cast N.pos
  have hcast (j : ℤ) : ((gradIndex N (J + j)).val : ℤ) = (J + j) % (N : ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ hN.ne')
  refine Finset.sum_bij (fun j _ => gradIndex N (J + j)) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro j hj k hk he
    have hr : (j - (-J)) % (N : ℤ) = (k - (-J)) % (N : ℤ) := by
      have h := congrArg (fun i : Fin (N : ℕ) => (i.val : ℤ)) he
      rw [hcast, hcast] at h
      simpa only [sub_neg_eq_add, add_comm] using h
    exact emod_inj_of_abs_sub_lt hr (by
      rw [Finset.mem_Ico] at hj hk
      rw [abs_lt]
      constructor <;> omega)
  · intro i _
    let j : ℤ := ((i.val : ℤ) - J) % (N : ℤ)
    have hj : j ∈ Finset.Ico (0 : ℤ) (N : ℤ) :=
      Finset.mem_Ico.mpr ⟨Int.emod_nonneg _ hN.ne', Int.emod_lt_of_pos _ hN⟩
    refine ⟨j, hj, ?_⟩
    apply Fin.ext
    apply Int.ofNat_inj.mp
    rw [hcast]
    have hi : (i.val : ℤ) < N := by exact_mod_cast i.isLt
    dsimp only [j]
    rw [Int.add_emod, Int.emod_emod, ← Int.add_emod,
      add_sub_cancel, Int.emod_eq_of_lt (by positivity) hi]
  · intro j _
    exact loopPrecedingLift_periodic_eval X hf j

/-- Exact expansion in a full window, for every configuration and every
periodic test. No probabilistic estimate is required. -/
theorem loopLocalization_full_identity {N : ℕ+} {ℓ γ s : ℝ}
    (hF : ¬GradPartial N ℓ γ) {b : ℝ → ℝ}
    (hp : Function.Periodic b (N : ℝ)) (X : LoopPrecedingConfiguration N) :
    loopArcL s N b X.val = loopLocalLoop s N ℓ γ b X +
      loopLocalBackground s N ℓ γ b := by
  classical
  let k := loopArcKernel s N b
  let S := Finset.Ico (0 : ℤ) (N : ℤ)
  have hsums (f : ℝ → ℝ) (hf : Function.Periodic f (N : ℝ)) :
      (∑ j ∈ S, f (loopPrecedingLift X j)) = ∑ i : Fin (N : ℕ), f (loopArcPos N X.val i) :=
    sum_loopPrecedingLift_full X hf
  have hright (z : ℝ) : Function.Periodic (k z) (N : ℝ) :=
    loopLocalKernel_periodic_right hp s z
  have hleft (u : ℝ) : Function.Periodic (fun z => k z u) (N : ℝ) :=
    loopLocalKernel_periodic_left hp s u
  have hpair :
      (∑ i ∈ S, ∑ j ∈ S.erase i, k (loopPrecedingLift X i) (loopPrecedingLift X j)) =
        ∑ i : Fin (N : ℕ), ∑ j : Fin (N : ℕ),
          if j = i then 0 else k (loopArcPos N X.val i) (loopArcPos N X.val j) := by
    have he (i : ℤ) (hi : i ∈ S) :
        (∑ j ∈ S.erase i, k (loopPrecedingLift X i) (loopPrecedingLift X j)) =
          ∑ j ∈ S, k (loopPrecedingLift X i) (loopPrecedingLift X j) := by
      have h := Finset.sum_erase_add S (fun j => k (loopPrecedingLift X i)
        (loopPrecedingLift X j)) hi
      simpa only [k, loopArcKernel, sub_self, zero_mul, add_zero] using h
    calc
      _ = ∑ i ∈ S, ∑ j ∈ S, k (loopPrecedingLift X i) (loopPrecedingLift X j) :=
        Finset.sum_congr rfl he
      _ = ∑ i ∈ S, ∑ j : Fin (N : ℕ), k (loopPrecedingLift X i) (loopArcPos N X.val j) := by
        apply Finset.sum_congr rfl
        intro i _
        exact hsums _ (hright _)
      _ = ∑ i : Fin (N : ℕ), ∑ j : Fin (N : ℕ), k (loopArcPos N X.val i) (loopArcPos N X.val j) := by
        apply hsums (fun z => ∑ j : Fin (N : ℕ), k z (loopArcPos N X.val j))
        intro z
        apply Finset.sum_congr rfl
        intro j _
        exact hleft _ z
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        split_ifs with h
        · subst j
          simp [k, loopArcKernel]
        · rfl
  have hbg :
      (∑ i ∈ S, ∫ u in (0 : ℝ)..(N : ℝ), k (loopPrecedingLift X i) u) =
        ∑ i : Fin (N : ℕ), ∫ u in (0 : ℝ)..(N : ℝ), k (loopArcPos N X.val i) u := by
    apply hsums (fun z => ∫ u in (0 : ℝ)..(N : ℝ), k z u)
    intro z
    exact intervalIntegral.integral_congr fun u _ => hleft u z
  have hswap :
      (∑ j : Fin (N : ℕ), ∫ z in (0 : ℝ)..(N : ℝ), k z (loopArcPos N X.val j)) =
        ∑ j : Fin (N : ℕ), ∫ z in (0 : ℝ)..(N : ℝ), k (loopArcPos N X.val j) z := by
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    funext z
    exact loopLocalKernel_swap s N b _ _
  unfold loopArcL loopLocalLoop loopLocalBackground
  simp only [gradLabels, loopLocalLo, loopLocalHi, hF, ↓reduceIte]
  change _ - _ - _ + _ =
    (∑ i ∈ S, ∑ j ∈ S.erase i, k (loopPrecedingLift X i) (loopPrecedingLift X j)) -
      2 * (∑ i ∈ S, ∫ u in (0 : ℝ)..(N : ℝ), k (loopPrecedingLift X i) u) + _
  rw [hpair, hbg]
  change _ - _ - (∑ j : Fin (N : ℕ), ∫ z in (0 : ℝ)..(N : ℝ), k z (loopArcPos N X.val j)) + _ = _
  rw [hswap]
  ring

/-- The localized transport is unchanged in a full window. -/
theorem loopLocalTransport_full {N : ℕ+} {ℓ γ : ℝ} (hF : ¬GradPartial N ℓ γ)
    (χ ψ : ℝ → ℝ) :
    loopLocalTransport χ N ℓ γ ψ = loopScaleField ((N : ℝ) * ℓ) ψ := by
  funext z
  simp only [loopLocalTransport, loopScaleField, loopTransport, hF, ↓reduceIte]

/-- The localization error vanishes identically in the full-window case of
Lemma 5.8. -/
theorem loopLocalization_full_error_zero {N : ℕ+} {ℓ γ s : ℝ}
    (hF : ¬GradPartial N ℓ γ) (hℓ : 0 < ℓ) (χ : ℝ → ℝ)
    {ψ : ℝ → ℝ} (hp : Function.Periodic ψ ℓ⁻¹)
    (X : LoopPrecedingConfiguration N) :
    loopArcL s N (loopScaleField ((N : ℝ) * ℓ) ψ) X.val -
      loopLocalLoop s N ℓ γ (loopLocalTransport χ N ℓ γ ψ) X -
      loopLocalBackground s N ℓ γ (loopLocalTransport χ N ℓ γ ψ) = 0 := by
  have hper := loopLocalTransport_periodic (N := N) (γ := γ) hℓ χ hp
  rw [loopLocalTransport_full hF χ ψ] at hper ⊢
  rw [loopLocalization_full_identity hF hper X]
  ring

/-- The required two-particle boundary check: every admissible scale has a
full window and hence exactly zero localization error. -/
theorem loopLocalization_two_error_zero {N : ℕ+} (hN : (N : ℕ) = 2)
    {ℓ γ s : ℝ} (hℓ : 0 < ℓ) (hK : 1 ≤ (N : ℝ) * ℓ) (hγ : 0 ≤ γ)
    (χ : ℝ → ℝ) {ψ : ℝ → ℝ} (hp : Function.Periodic ψ ℓ⁻¹)
    (X : LoopPrecedingConfiguration N) :
    loopArcL s N (loopScaleField ((N : ℝ) * ℓ) ψ) X.val -
      loopLocalLoop s N ℓ γ (loopLocalTransport χ N ℓ γ ψ) X -
      loopLocalBackground s N ℓ γ (loopLocalTransport χ N ℓ γ ψ) = 0 :=
  loopLocalization_full_error_zero (not_gradPartial_two hN hK hγ) hℓ χ hp X

end Riesz1

end
