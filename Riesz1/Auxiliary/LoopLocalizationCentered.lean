/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopLocalizationFull
public import Riesz1.Auxiliary.LoopExteriorQuadratureGeometry

/-!
# Centered periods for the localization calculation

The localization part of Lemma 5.8: reindex the empirical measure
by any consecutive period of preceding labels and translate the background
fundamental domain. The formulas include the even-period antipode once.
-/

public section

noncomputable section

open MeasureTheory Set

namespace Riesz1

/-- A periodic test sums to the empirical integral on every consecutive period
of preceding labels. -/
theorem sum_loopPrecedingLift_period {N : ℕ+} (X : LoopPrecedingConfiguration N)
    {f : ℝ → ℝ} (hf : Function.Periodic f (N : ℝ)) (a : ℤ) :
    (∑ j ∈ Finset.Ico a (a + N), f (loopPrecedingLift X j)) =
      ∑ i : Fin (N : ℕ), f (loopArcPos N X.val i) := by
  classical
  let J := loopPrecedingLabel X
  have hN : (0 : ℤ) < N := by exact_mod_cast N.pos
  have hcast (j : ℤ) : ((gradIndex N (J + j)).val : ℤ) = (J + j) % (N : ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ hN.ne')
  refine Finset.sum_bij (fun j _ => gradIndex N (J + j))
    (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
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
    let j : ℤ := a + ((i.val : ℤ) - J - a) % (N : ℤ)
    have hj : j ∈ Finset.Ico a (a + N) := by
      have h0 := Int.emod_nonneg ((i.val : ℤ) - J - a) hN.ne'
      have h1 := Int.emod_lt_of_pos ((i.val : ℤ) - J - a) hN
      exact Finset.mem_Ico.mpr ⟨by dsimp [j]; omega, by dsimp [j]; omega⟩
    refine ⟨j, hj, ?_⟩
    apply Fin.ext
    apply Int.ofNat_inj.mp
    rw [hcast]
    have hi : (i.val : ℤ) < N := by exact_mod_cast i.isLt
    dsimp only [j]
    rw [show J + (a + ((i.val : ℤ) - J - a) % (N : ℤ)) =
      (J + a) + ((i.val : ℤ) - (J + a)) % (N : ℤ) by
        rw [show (i.val : ℤ) - J - a = (i.val : ℤ) - (J + a) by ring]
        ring,
      Int.add_emod, Int.emod_emod, ← Int.add_emod, add_sub_cancel,
      Int.emod_eq_of_lt (by positivity) hi]
  · intro j _
    exact loopPrecedingLift_periodic_eval X hf j

/-- The centered set used in the exterior force is exactly one consecutive period. -/
theorem loopLocalization_centered_labels (N : ℕ+) :
    ((Finset.Icc (-(N : ℤ)) (N : ℤ)).filter
      (fun j => -(N : ℤ) < 2 * j ∧ 2 * j ≤ (N : ℤ))) =
      Finset.Ico (-(((N : ℤ) - 1) / 2)) (-(((N : ℤ) - 1) / 2) + N) := by
  have hN : (0 : ℤ) < N := by exact_mod_cast N.pos
  ext j
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ico]
  omega

/-- The local labels and the exterior labels partition one centered period. -/
theorem loopLocalization_label_partition {N : ℕ+} {ℓ γ : ℝ}
    (hK : 1 ≤ (N : ℝ) * ℓ) (hγ : 0 ≤ γ) (hP : GradPartial N ℓ γ) :
    Disjoint (gradLabels N ℓ γ) (loopExteriorLabels N ℓ γ) ∧
      gradLabels N ℓ γ ∪ loopExteriorLabels N ℓ γ =
        Finset.Ico (-(((N : ℤ) - 1) / 2)) (-(((N : ℤ) - 1) / 2) + N) := by
  classical
  let C := ((Finset.Icc (-(N : ℤ)) (N : ℤ)).filter
    (fun j => -(N : ℤ) < 2 * j ∧ 2 * j ≤ (N : ℤ)))
  have hn0 : (0 : ℤ) ≤ ⌊gradM N ℓ γ⌋ :=
    Int.floor_nonneg.mpr ((Real.one_le_rpow hK hγ).trans' zero_le_one)
  have hnN : 2 * ⌊gradM N ℓ γ⌋ < (N : ℤ) := by
    have hf := Int.floor_le (gradM N ℓ γ)
    have hPr : gradM N ℓ γ < (N : ℝ) / 8 := hP
    have : (2 : ℝ) * (⌊gradM N ℓ γ⌋ : ℤ) < N := by linarith
    exact_mod_cast this
  have hsub : gradLabels N ℓ γ ⊆ C := by
    intro j hj
    simp only [gradLabels, hP, ↓reduceIte, Finset.mem_Icc] at hj
    simp only [C, Finset.mem_filter, Finset.mem_Icc]
    omega
  have hdis : Disjoint (gradLabels N ℓ γ) (loopExteriorLabels N ℓ γ) :=
    Finset.disjoint_left.mpr (fun _ hi he => (Finset.mem_sdiff.mp he).2 hi)
  exact ⟨hdis,
    (Finset.union_sdiff_of_subset hsub).trans (loopLocalization_centered_labels N)⟩

/-- The global loop on an arbitrary label period and an arbitrary background
period. The diagonal is zero, so it may be included in the double sum. -/
theorem loopLocalization_period_expansion {N : ℕ+} {s : ℝ}
    {b : ℝ → ℝ} (hp : Function.Periodic b (N : ℝ))
    (X : LoopPrecedingConfiguration N) (a : ℤ) (t : ℝ) :
    loopArcL s N b X.val =
      (∑ i ∈ Finset.Ico a (a + N), ∑ j ∈ Finset.Ico a (a + N),
        loopArcKernel s N b (loopPrecedingLift X i) (loopPrecedingLift X j)) -
      2 * (∑ i ∈ Finset.Ico a (a + N), ∫ u in t..t + N,
        loopArcKernel s N b (loopPrecedingLift X i) u) +
      ∫ z in t..t + N, ∫ u in t..t + N, loopArcKernel s N b z u := by
  classical
  let k := loopArcKernel s N b
  let S := Finset.Ico a (a + N)
  have hright (z : ℝ) : Function.Periodic (k z) (N : ℝ) :=
    loopLocalKernel_periodic_right hp s z
  have hleft (u : ℝ) : Function.Periodic (fun z => k z u) (N : ℝ) :=
    loopLocalKernel_periodic_left hp s u
  have hi (z : ℝ) : (∫ u in t..t + N, k z u) = ∫ u in (0 : ℝ)..N, k z u := by
    simpa only [zero_add] using (hright z).intervalIntegral_add_eq t 0
  have hpair : (∑ i ∈ S, ∑ j ∈ S, k (loopPrecedingLift X i) (loopPrecedingLift X j)) =
      ∑ i : Fin (N : ℕ), ∑ j : Fin (N : ℕ),
        if j = i then 0 else k (loopArcPos N X.val i) (loopArcPos N X.val j) := by
    calc
      _ = ∑ i ∈ S, ∑ j : Fin (N : ℕ), k (loopPrecedingLift X i) (loopArcPos N X.val j) := by
        apply Finset.sum_congr rfl
        intro i _
        exact sum_loopPrecedingLift_period X (hright _) a
      _ = ∑ i : Fin (N : ℕ), ∑ j : Fin (N : ℕ), k (loopArcPos N X.val i) (loopArcPos N X.val j) := by
        apply sum_loopPrecedingLift_period X
          (f := fun z => ∑ j : Fin (N : ℕ), k z (loopArcPos N X.val j)) _ a
        intro z
        exact Finset.sum_congr rfl (fun j _ => hleft _ z)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        split_ifs with he
        · subst j
          simp [k, loopArcKernel]
        · rfl
  have hbg : (∑ i ∈ S, ∫ u in t..t + N, k (loopPrecedingLift X i) u) =
      ∑ i : Fin (N : ℕ), ∫ u in (0 : ℝ)..N, k (loopArcPos N X.val i) u := by
    simp_rw [hi]
    apply sum_loopPrecedingLift_period X (f := fun z => ∫ u in (0 : ℝ)..N, k z u) _ a
    intro z
    exact intervalIntegral.integral_congr (fun u _ => hleft u z)
  have hbb : (∫ z in t..t + N, ∫ u in t..t + N, k z u) =
      ∫ z in (0 : ℝ)..N, ∫ u in (0 : ℝ)..N, k z u := by
    simp_rw [hi]
    have hper : Function.Periodic (fun z => ∫ u in (0 : ℝ)..N, k z u) (N : ℝ) := by
      intro z
      exact intervalIntegral.integral_congr (fun u _ => hleft u z)
    simpa only [zero_add] using hper.intervalIntegral_add_eq t 0
  have hswap : (∑ j : Fin (N : ℕ), ∫ z in (0 : ℝ)..N, k z (loopArcPos N X.val j)) =
      ∑ j : Fin (N : ℕ), ∫ z in (0 : ℝ)..N, k (loopArcPos N X.val j) z := by
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    funext z
    exact loopLocalKernel_swap s N b _ _
  rw [hpair, hbg, hbb]
  unfold loopArcL
  change _ - _ - (∑ j : Fin (N : ℕ), ∫ z in (0 : ℝ)..N, k z (loopArcPos N X.val j)) + _ = _
  rw [hswap]
  ring

end Riesz1

end
