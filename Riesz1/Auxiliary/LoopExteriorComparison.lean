/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopExteriorCancellation
public import Riesz1.Auxiliary.LoopExteriorProbability
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-!
# Spatial suprema of individual exterior-force differences

The deterministic comparison and measurability ingredients of the per-label estimate
in the exterior part of Lemma 5.8. All suprema use the spatial
carrier and the actual preceding lift.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Riesz1

/-- Every exterior representative has absolute label greater than `M` and at most
half the period. This also gives the natural block length for both signs. -/
theorem loopExteriorLabels_abs {N : ℕ+} {ℓ γ : ℝ}
    (hK : 1 ≤ (N : ℝ) * ℓ) (hγ : 0 ≤ γ) (hP : GradPartial N ℓ γ)
    {j : ℤ} (hj : j ∈ loopExteriorLabels N ℓ γ) :
    gradM N ℓ γ < |(j : ℝ)| ∧ 1 ≤ j.natAbs ∧ j.natAbs ≤ (N : ℕ) / 2 := by
  have hM : 1 ≤ gradM N ℓ γ := Real.one_le_rpow hK hγ
  have hj' := Finset.mem_sdiff.mp hj
  have hrep := (Finset.mem_filter.mp hj'.1).2
  have hout := hj'.2
  simp only [gradLabels, hP, ↓reduceIte, Finset.mem_Icc, not_and_or, not_le] at hout
  have hn : (0 : ℤ) ≤ ⌊gradM N ℓ γ⌋ := Int.floor_nonneg.mpr (by linarith)
  have hab : ⌊gradM N ℓ γ⌋ < |j| := by
    rcases hout with hn | hp
    · rw [abs_of_neg (by omega : j < 0)]
      omega
    · rw [abs_of_pos (by omega : 0 < j)]
      exact hp
  have hMabs : gradM N ℓ γ < |(j : ℝ)| := by
    rw [← Int.cast_abs]
    exact (Int.floor_lt).mp hab
  have hjnat : (j.natAbs : ℤ) = |j| := Int.natCast_natAbs j
  have hnrep : 2 * (j.natAbs : ℤ) ≤ N := by
    rw [hjnat]
    rcases le_or_gt 0 j with hp | hn
    · rw [abs_of_nonneg hp]
      exact hrep.2
    · rw [abs_of_neg hn]
      omega
  have hnNat : 2 * j.natAbs ≤ (N : ℕ) := by exact_mod_cast hnrep
  exact ⟨hMabs, by
    have hh : (1 : ℝ) < j.natAbs := by simpa only [natAbs_cast_eq_abs] using hM.trans_lt hMabs
    exact_mod_cast hh.le, by omega⟩

/-- The reference force obeys the same `M` separation bound as the random exterior
force. The constant is chosen before the period and the window. -/
theorem loopExterior_reference_bound {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ {N : ℕ+} {ℓ γ : ℝ},
      1 ≤ (N : ℝ) * ℓ → 0 ≤ γ → GradPartial N ℓ γ →
      ∀ {j : ℤ}, j ∈ loopExteriorLabels N ℓ γ →
      ∀ {z : ℝ}, z ∈ Icc (-gradM N ℓ γ / 4) (gradM N ℓ γ / 4) →
        |deriv (loopArcG s N) (z - (j : ℝ))| ≤ C * gradM N ℓ γ ^ (-s - 1) := by
  obtain ⟨C, hC, hb⟩ := loopExterior_iteratedDeriv_le_of_separated hs hs1 1
  refine ⟨C * (1 / 4 : ℝ) ^ (-s - 1), by positivity, ?_⟩
  intro N ℓ γ hK hγ hP j hj z hz
  have hM : 0 < gradM N ℓ γ := lt_of_lt_of_le zero_lt_one (Real.one_le_rpow hK hγ)
  obtain ⟨hjM, _, hjN⟩ := loopExteriorLabels_abs hK hγ hP hj
  have hjpos : 0 < |(j : ℝ)| := hM.trans hjM
  have hjN' : |(j : ℝ)| ≤ (N : ℝ) / 2 := by
    rw [← natAbs_cast_eq_abs]
    have : 2 * j.natAbs ≤ (N : ℕ) := by omega
    have hh : (2 : ℝ) * j.natAbs ≤ N := by exact_mod_cast this
    linarith
  have hz' : |z| ≤ |(j : ℝ)| / 4 := by
    apply (abs_le.mpr ⟨by linarith [hz.1], hz.2⟩).trans
    linarith
  have hsep := (loopExterior_segment_separation hjpos hjN' hz'
    (show |(j : ℝ) - (j : ℝ)| ≤ |(j : ℝ)| / 2 by rw [sub_self, abs_zero]; positivity)).1
  have hbd := hb N (z - (j : ℝ)) (gradM N ℓ γ / 4) (by positivity)
    ((by linarith : gradM N ℓ γ / 4 ≤ |(j : ℝ)| / 4).trans hsep)
  simpa only [iteratedDeriv_one, Nat.cast_one, show gradM N ℓ γ / 4 =
    (1 / 4 : ℝ) * gradM N ℓ γ by ring, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 1 / 4) hM.le,
    mul_assoc] using hbd

/-- The spatial absolute difference for a single exterior label is continuous,
bounded, nonnegative at its supremum, and measurable as a function of the good
configuration. In particular, the real supremum has its intended meaning. -/
theorem loopExterior_difference_sup_regular {s : ℝ} (hs : 0 < s) (hs1 : s < 1)
    {N : ℕ+} {ℓ γ : ℝ} (hK : 1 ≤ (N : ℝ) * ℓ) (hγ : 0 ≤ γ)
    (hP : GradPartial N ℓ γ) {j : ℤ} (hj : j ∈ loopExteriorLabels N ℓ γ) :
    let A := Icc (-gradM N ℓ γ / 4) (gradM N ℓ γ / 4)
    let H := fun (X : {X : LoopPrecedingConfiguration N // X ∈ loopExteriorGood N ℓ γ}) (z : A) =>
      |deriv (loopArcG s N) (z.val - loopPrecedingLift X.val j) -
        deriv (loopArcG s N) (z.val - (j : ℝ))|
    (∀ X, Continuous (H X) ∧ BddAbove (range (H X)) ∧ 0 ≤ ⨆ z, H X z) ∧
      Measurable (fun X => ⨆ z, H X z) := by
  let A := Icc (-gradM N ℓ γ / 4) (gradM N ℓ γ / 4)
  let H := fun (X : {X : LoopPrecedingConfiguration N // X ∈ loopExteriorGood N ℓ γ}) (z : A) =>
    |deriv (loopArcG s N) (z.val - loopPrecedingLift X.val j) -
      deriv (loopArcG s N) (z.val - (j : ℝ))|
  have hM : 0 < gradM N ℓ γ := lt_of_lt_of_le zero_lt_one (Real.one_le_rpow hK hγ)
  let z0 : A := ⟨0, by constructor <;> linarith⟩
  have hA : Nonempty A := ⟨z0⟩
  obtain ⟨hjM, _, hjN⟩ := loopExteriorLabels_abs hK hγ hP hj
  have hjpos : 0 < |(j : ℝ)| := hM.trans hjM
  have hjN' : |(j : ℝ)| ≤ (N : ℝ) / 2 := by
    rw [← natAbs_cast_eq_abs]
    have : 2 * j.natAbs ≤ (N : ℕ) := by omega
    have hh : (2 : ℝ) * j.natAbs ≤ N := by exact_mod_cast this
    linarith
  have hc (X) : Continuous (H X) := by
    apply Continuous.abs
    apply Continuous.sub
    · exact (continuousOn_loopExteriorSummand hs hs1 hK hγ hP X.property hj).domRestrict
    · have hcRef : ContinuousOn (fun z : ℝ => deriv (loopArcG s N) (z - (j : ℝ))) A := by
        intro z hz
        have hz' : |z| ≤ |(j : ℝ)| / 4 := by
          apply (abs_le.mpr ⟨by linarith [hz.1], hz.2⟩).trans
          linarith
        have hsep := (loopExterior_segment_separation hjpos hjN' hz'
          (show |(j : ℝ) - (j : ℝ)| ≤ |(j : ℝ)| / 2 by rw [sub_self, abs_zero]; positivity)).2
        exact ((contDiffAt_deriv_loopArcG hs hs1 N hsep).continuousAt.comp
          (f := fun z : ℝ => z - (j : ℝ)) (continuous_id.sub continuous_const).continuousAt).continuousWithinAt
      exact hcRef.domRestrict
  have hb (X) : BddAbove (range (H X)) := by
    simpa only [image_univ] using isCompact_univ.bddAbove_image (hc X).continuousOn
  refine ⟨fun X => ⟨hc X, hb X, (abs_nonneg _).trans (le_ciSup (hb X) z0)⟩, ?_⟩
  obtain ⟨D, hD, hd⟩ := TopologicalSpace.exists_countable_dense A
  have : Countable D := hD.to_subtype
  have he : (fun X => ⨆ z, H X z) = (fun X => ⨆ z : D, H X z.val) := by
    funext X
    exact (hd.ciSup (hc X) (hb X)).symm
  rw [he]
  apply Measurable.iSup
  intro z
  apply continuous_abs.measurable.comp
  apply Measurable.sub_const
  exact (measurable_deriv (loopArcG s N)).comp
    (measurable_const.sub ((measurable_loopPrecedingLift N j).comp measurable_subtype_coe))

/-- A pointwise bound for the spatial supremum: a linear displacement term on the
small-displacement event, and a uniformly bounded force on its complement. -/
theorem loopExterior_difference_sup_bound {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ {N : ℕ+} {ℓ γ : ℝ},
      1 ≤ (N : ℝ) * ℓ → 0 ≤ γ → GradPartial N ℓ γ →
      ∀ {j : ℤ}, j ∈ loopExteriorLabels N ℓ γ →
      ∀ X : {X : LoopPrecedingConfiguration N // X ∈ loopExteriorGood N ℓ γ},
      (⨆ z : Icc (-gradM N ℓ γ / 4) (gradM N ℓ γ / 4),
        |deriv (loopArcG s N) (z.val - loopPrecedingLift X.val j) -
          deriv (loopArcG s N) (z.val - (j : ℝ))|) ≤
        A * |(j : ℝ)| ^ (-s - 2) * |loopPrecedingLift X.val j - (j : ℝ)| +
          {Y : {X : LoopPrecedingConfiguration N // X ∈ loopExteriorGood N ℓ γ} |
            |(j : ℝ)| / 2 ≤ |loopPrecedingLift Y.val j - (j : ℝ)|}.indicator
              (fun _ => B * gradM N ℓ γ ^ (-s - 1)) X := by
  obtain ⟨A, hA, hdiff⟩ := loopExterior_reference_difference_bound hs hs1
  obtain ⟨B, hB, hforce⟩ := loopExteriorSummand_bound hs hs1
  obtain ⟨C, hC, href⟩ := loopExterior_reference_bound hs hs1
  refine ⟨A, B + C, hA, by positivity, ?_⟩
  intro N ℓ γ hK hγ hP j hj X
  have hM : 0 < gradM N ℓ γ := lt_of_lt_of_le zero_lt_one (Real.one_le_rpow hK hγ)
  obtain ⟨hjM, _, hjN⟩ := loopExteriorLabels_abs hK hγ hP hj
  have hjpos : 0 < |(j : ℝ)| := hM.trans hjM
  have hjN' : |(j : ℝ)| ≤ (N : ℝ) / 2 := by
    rw [← natAbs_cast_eq_abs]
    have : 2 * j.natAbs ≤ (N : ℕ) := by omega
    have hh : (2 : ℝ) * j.natAbs ≤ N := by exact_mod_cast this
    linarith
  have : Nonempty (Icc (-gradM N ℓ γ / 4) (gradM N ℓ γ / 4)) :=
    ⟨⟨0, by constructor <;> linarith⟩⟩
  apply ciSup_le
  intro z
  by_cases hX : |(j : ℝ)| / 2 ≤ |loopPrecedingLift X.val j - (j : ℝ)|
  · rw [indicator_of_mem (a := X) hX]
    apply le_trans (abs_sub _ _)
    have h1 := hforce hK hγ hP X.property hj z.property
    have h2 := href hK hγ hP hj z.property
    have h0 : 0 ≤ A * |(j : ℝ)| ^ (-s - 2) * |loopPrecedingLift X.val j - (j : ℝ)| := by
      positivity
    nlinarith
  · rw [indicator_of_notMem (a := X) hX, add_zero]
    apply hdiff N (j : ℝ) (loopPrecedingLift X.val j) z.val hjpos hjN'
    · apply (abs_le.mpr ⟨by linarith [z.property.1], z.property.2⟩).trans
      linarith
    · exact (lt_of_not_ge hX).le

/-- The force is bounded by the sum of the random/reference spatial suprema and
the deterministic reference-lattice/background error. This identity uses the exact
labels, background, and force, including the antipodal representative. -/
theorem loopExteriorForce_bound_by_comparison {s : ℝ} (hs : 0 < s) (hs1 : s < 1)
    {N : ℕ+} {ℓ γ : ℝ} (hK : 1 ≤ (N : ℝ) * ℓ) (hγ : 0 ≤ γ)
    (hP : GradPartial N ℓ γ)
    (X : {X : LoopPrecedingConfiguration N // X ∈ loopExteriorGood N ℓ γ})
    (z : Icc (-gradM N ℓ γ / 4) (gradM N ℓ γ / 4)) :
    |loopExteriorForce s N ℓ γ X z| ≤
      (∑ j ∈ loopExteriorLabels N ℓ γ,
        ⨆ u : Icc (-gradM N ℓ γ / 4) (gradM N ℓ γ / 4),
          |deriv (loopArcG s N) (u.val - loopPrecedingLift X.val j) -
            deriv (loopArcG s N) (u.val - (j : ℝ))|) +
      |(∑ j ∈ loopExteriorLabels N ℓ γ, deriv (loopArcG s N) (z.val - (j : ℝ))) -
        ∫ u in loopExteriorBackground N ℓ γ, deriv (loopArcG s N) (z.val - u)| := by
  let I := loopExteriorLabels N ℓ γ
  let a := ∑ j ∈ I, deriv (loopArcG s N) (z.val - loopPrecedingLift X.val j)
  let b := ∑ j ∈ I, deriv (loopArcG s N) (z.val - (j : ℝ))
  let c := ∫ u in loopExteriorBackground N ℓ γ, deriv (loopArcG s N) (z.val - u)
  have htriangle : |a - c| ≤ |a - b| + |b - c| := by
    calc
      |a - c| = |(a - b) + (b - c)| := by congr 1; ring
      _ ≤ _ := abs_add_le _ _
  apply htriangle.trans
  apply add_le_add _ le_rfl
  calc
    |a - b| = |∑ j ∈ I, (deriv (loopArcG s N) (z.val - loopPrecedingLift X.val j) -
        deriv (loopArcG s N) (z.val - (j : ℝ)))| := by
      rw [Finset.sum_sub_distrib]
    _ ≤ ∑ j ∈ I, |deriv (loopArcG s N) (z.val - loopPrecedingLift X.val j) -
        deriv (loopArcG s N) (z.val - (j : ℝ))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro j hj
      exact le_ciSup ((loopExterior_difference_sup_regular hs hs1 hK hγ hP hj).1 X).2.1 z

end Riesz1

end
