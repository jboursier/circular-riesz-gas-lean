/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopExteriorBackground
public import Mathlib.Topology.Order.IsLUB

/-!
# Continuity and the measurable exterior-force supremum

The regularity assertion in the exterior part of Lemma 5.8.
The background is controlled on a compact product separated from every singularity.
The supremum is taken over the actual compact spatial carrier.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace Riesz1

/-- The background force depends continuously on the central spatial variable. -/
theorem continuousOn_loopExteriorBackground {s : ℝ} (hs : 0 < s) (hs1 : s < 1)
    {N : ℕ+} {ℓ γ : ℝ} (hM : 0 < gradM N ℓ γ) (hP : GradPartial N ℓ γ) :
    ContinuousOn (fun z => ∫ u in loopExteriorBackground N ℓ γ,
      deriv (loopArcG s N) (z - u))
      (Icc (-gradM N ℓ γ / 4) (gradM N ℓ γ / 4)) := by
  let A := Icc (-gradM N ℓ γ / 4) (gradM N ℓ γ / 4)
  let B := Icc (-(N : ℝ) / 2) (-gradM N ℓ γ) ∪
    Icc (gradM N ℓ γ) ((N : ℝ) / 2)
  have hsub : loopExteriorBackground N ℓ γ ⊆ B := by
    intro u hu
    rcases hu with ⟨huN, huM⟩
    by_cases h : u ≤ -gradM N ℓ γ
    · exact Or.inl ⟨huN.1, h⟩
    · exact Or.inr ⟨by
        by_contra hm
        exact huM ⟨le_of_lt (lt_of_not_ge h), le_of_lt (lt_of_not_ge hm)⟩, huN.2⟩
  have hc : ContinuousOn (fun p : ℝ × ℝ => deriv (loopArcG s N) (p.1 - p.2))
      (A ×ˢ B) := by
    intro p hp
    exact ((contDiffAt_deriv_loopArcG hs hs1 N
      (loopExteriorBackground_nonsingular hM hP hp.1 hp.2)).continuousAt.comp (f := fun p : ℝ × ℝ => p.1 - p.2)
        (continuous_fst.sub continuous_snd).continuousAt).continuousWithinAt
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod (isCompact_Icc.union isCompact_Icc)).exists_bound_of_continuousOn hc
  apply continuousOn_of_dominated (bound := fun _ => C)
  · intro z hz
    exact (integrableOn_loopExteriorBackground hs hs1 hM hP hz).aestronglyMeasurable
  · intro z hz
    filter_upwards [ae_restrict_mem (measurableSet_loopExteriorBackground N ℓ γ)] with u hu
    exact hC (z, u) ⟨hz, hsub hu⟩
  · exact integrableOn_const ((measure_mono (show loopExteriorBackground N ℓ γ ⊆
      Icc (-(N : ℝ) / 2) ((N : ℝ) / 2) from fun _ h => h.1)).trans_lt
        measure_Icc_lt_top).ne
  · filter_upwards [ae_restrict_mem (measurableSet_loopExteriorBackground N ℓ γ)] with u hu
    intro z hz
    exact ((contDiffAt_deriv_loopArcG hs hs1 N
      (loopExteriorBackground_nonsingular hM hP hz (hsub hu))).continuousAt.comp (f := fun z : ℝ => z - u)
        (continuous_id.sub continuous_const).continuousAt).continuousWithinAt

/-- Continuity of the entire force on its spatial carrier, including its endpoints. -/
theorem continuous_loopExteriorForce {s : ℝ} (hs : 0 < s) (hs1 : s < 1)
    {N : ℕ+} {ℓ γ : ℝ} (hK : 1 ≤ (N : ℝ) * ℓ) (hγ : 0 ≤ γ)
    (hP : GradPartial N ℓ γ)
    (X : {X : LoopPrecedingConfiguration N // X ∈ loopExteriorGood N ℓ γ}) :
    Continuous (loopExteriorForce s N ℓ γ X) := by
  have hM : 0 < gradM N ℓ γ := lt_of_lt_of_le zero_lt_one (Real.one_le_rpow hK hγ)
  have ha : ContinuousOn (fun z => ∑ j ∈ loopExteriorLabels N ℓ γ,
      deriv (loopArcG s N) (z - loopPrecedingLift X.val j))
      (Icc (-gradM N ℓ γ / 4) (gradM N ℓ γ / 4)) := by
    apply continuousOn_finsetSum
    intro j hj
    exact continuousOn_loopExteriorSummand hs hs1 hK hγ hP X.property hj
  exact (ha.sub (continuousOn_loopExteriorBackground hs hs1 hM hP)).domRestrict

/-- For each spatial point the force is measurable in the good configuration. -/
theorem measurable_loopExteriorForce (s : ℝ) (N : ℕ+) (ℓ γ : ℝ)
    (z : Icc (-gradM N ℓ γ / 4) (gradM N ℓ γ / 4)) :
    Measurable (fun X => loopExteriorForce s N ℓ γ X z) := by
  apply Measurable.sub_const
  apply Finset.measurable_sum
  intro j _
  exact (measurable_deriv (loopArcG s N)).comp
    (measurable_const.sub ((measurable_loopPrecedingLift N j).comp measurable_subtype_coe))

/-- The supremum in the exterior estimate is bounded and attained. In particular its
conditionally complete supremum is the mathematical maximum. -/
theorem loopExteriorForce_max {s : ℝ} (hs : 0 < s) (hs1 : s < 1)
    {N : ℕ+} {ℓ γ : ℝ} (hK : 1 ≤ (N : ℝ) * ℓ) (hγ : 0 ≤ γ)
    (hP : GradPartial N ℓ γ)
    (X : {X : LoopPrecedingConfiguration N // X ∈ loopExteriorGood N ℓ γ}) :
    BddAbove (range (fun z => |loopExteriorForce s N ℓ γ X z|)) ∧
    ∃ z, (⨆ u, |loopExteriorForce s N ℓ γ X u|) = |loopExteriorForce s N ℓ γ X z| := by
  have hM : 0 < gradM N ℓ γ := lt_of_lt_of_le zero_lt_one (Real.one_le_rpow hK hγ)
  have : Nonempty (Icc (-gradM N ℓ γ / 4) (gradM N ℓ γ / 4)) :=
    ⟨⟨0, by constructor <;> linarith⟩⟩
  have hc := (continuous_loopExteriorForce hs hs1 hK hγ hP X).abs
  have hb := isCompact_univ.bddAbove_image hc.continuousOn
  rw [image_univ] at hb
  refine ⟨hb, ?_⟩
  obtain ⟨z, _, hz⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hc.continuousOn
  exact ⟨z, le_antisymm (ciSup_le (fun u => hz (mem_univ u))) (le_ciSup hb z)⟩

/-- The spatial supremum is measurable, by restricting continuous spatial slices to a
countable dense subset of the compact interval. -/
theorem measurable_loopExteriorForce_sup {s : ℝ} (hs : 0 < s) (hs1 : s < 1)
    {N : ℕ+} {ℓ γ : ℝ} (hK : 1 ≤ (N : ℝ) * ℓ) (hγ : 0 ≤ γ)
    (hP : GradPartial N ℓ γ) :
    Measurable (fun X => ⨆ z, |loopExteriorForce s N ℓ γ X z|) := by
  obtain ⟨D, hD, hd⟩ := TopologicalSpace.exists_countable_dense
    (Icc (-gradM N ℓ γ / 4) (gradM N ℓ γ / 4))
  have : Countable D := hD.to_subtype
  have he : (fun X => ⨆ z, |loopExteriorForce s N ℓ γ X z|) =
      (fun X => ⨆ z : D, |loopExteriorForce s N ℓ γ X z.val|) := by
    funext X
    exact (hd.ciSup ((continuous_loopExteriorForce hs hs1 hK hγ hP X).abs)
      (loopExteriorForce_max hs hs1 hK hγ hP X).1).symm
  rw [he]
  exact Measurable.iSup (fun z => continuous_abs.measurable.comp (measurable_loopExteriorForce s N ℓ γ z.val))

end Riesz1

end
