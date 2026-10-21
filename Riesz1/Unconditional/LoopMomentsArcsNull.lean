/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Unconditional.LoopMomentsArcsDefs
public import Riesz1.Gibbs.UniformMarginals
public import Riesz1.ToMathlib.AddCircleNullSingleton

/-!
# Endpoints of arcs are almost surely not occupied

Endpoints of a fixed arc `J` have probability zero, by the uniform one-particle marginal.
This file makes that statement precise.

* `gibbs_loopPos_eq_null`: under the Gibbs law, the microscopic particle `z_i = N x_i` of `N𝕋` sits at
  any fixed point with probability zero.
* `ae_loopPos_ne_pair`: almost surely, no particle sits at two given points of `N𝕋`.
* `volume_eq_of_agree_off_pair`: two subsets of `N𝕋` with the same points away from two points have
  the same Haar measure.
* `IsMicroArc.exists_ae_agree`: an arc `J` of length `r` has the Haar measure of the open arc
  `microArc N a r` for some `a`, and almost surely the same particles in it.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

namespace Riesz1

/-- Under the Gibbs law, the microscopic particle `z_i = N x_i` sits at a fixed point of `N𝕋` with
probability zero. The circle coordinate `[x_i]` is uniform by `map_coord_gibbsMeasure`, and the
event `z_i = c` forces `[x_i]` to equal the single point `[c / N]` of the unit circle. -/
theorem gibbs_loopPos_eq_null (P : Parameters) (N : ℕ+) (i : Fin (N : ℕ))
    (c : AddCircle (N : ℝ)) :
    gibbsMeasure P N {X : Configuration N | loopPos X i = c} = 0 := by
  obtain ⟨c0, rfl⟩ := QuotientAddGroup.mk_surjective c
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hsub : {X : Configuration N | loopPos X i = (c0 : AddCircle (N : ℝ))} ⊆
      (fun X : Configuration N => ((X.val i : ℝ) : UnitAddCircle)) ⁻¹'
        {((c0 / N : ℝ) : UnitAddCircle)} := by
    intro X hX
    have hX' : (((N : ℝ) * X.val i : ℝ) : AddCircle (N : ℝ)) = (c0 : AddCircle (N : ℝ)) := hX
    obtain ⟨n, hn⟩ := (coe_eq_coe_iff_int _ _).mp hX'
    have hx : (X.val i : ℝ) = c0 / N + n := by
      field_simp
      linarith
    show ((X.val i : ℝ) : UnitAddCircle) = ((c0 / N : ℝ) : UnitAddCircle)
    rw [hx]
    simp
  refine le_antisymm ?_ zero_le
  calc gibbsMeasure P N {X : Configuration N | loopPos X i = (c0 : AddCircle (N : ℝ))}
      ≤ gibbsMeasure P N ((fun X : Configuration N => ((X.val i : ℝ) : UnitAddCircle)) ⁻¹'
          {((c0 / N : ℝ) : UnitAddCircle)}) := measure_mono hsub
    _ = (gibbsMeasure P N).map (fun X : Configuration N => ((X.val i : ℝ) : UnitAddCircle))
          {((c0 / N : ℝ) : UnitAddCircle)} :=
        (Measure.map_apply (measurable_coord N i) (measurableSet_singleton _)).symm
    _ = volume ({((c0 / N : ℝ) : UnitAddCircle)} : Set UnitAddCircle) := by
        rw [map_coord_gibbsMeasure]
    _ = 0 := addCircle_volume_singleton 1 _

/-- Almost surely, the particle `z_i` avoids a fixed point of `N𝕋`. -/
theorem ae_loopPos_ne (P : Parameters) (N : ℕ+) (i : Fin (N : ℕ)) (c : AddCircle (N : ℝ)) :
    ∀ᵐ X ∂(gibbsMeasure P N), loopPos X i ≠ c := by
  rw [ae_iff]
  simp only [ne_eq, not_not]
  exact gibbs_loopPos_eq_null P N i c

/-- Almost surely, no particle of the configuration sits at either of two fixed points of `N𝕋`. -/
theorem ae_loopPos_ne_pair (P : Parameters) (N : ℕ+) (p q : AddCircle (N : ℝ)) :
    ∀ᵐ X ∂(gibbsMeasure P N), ∀ i : Fin (N : ℕ), loopPos X i ≠ p ∧ loopPos X i ≠ q := by
  rw [ae_all_iff]
  intro i
  filter_upwards [ae_loopPos_ne P N i p, ae_loopPos_ne P N i q] with X h1 h2
  exact ⟨h1, h2⟩

/-- Two subsets of `N𝕋` that have the same points away from `p` and `q` have the same Haar measure,
because the difference lies in the null set `{p, q}`. -/
theorem volume_eq_of_agree_off_pair {N : ℕ+} {J K : Set (AddCircle (N : ℝ))}
    {p q : AddCircle (N : ℝ)} (h : ∀ x : AddCircle (N : ℝ), x ≠ p → x ≠ q → (x ∈ J ↔ x ∈ K)) :
    volume J = volume K := by
  have hnull : volume (({p} : Set (AddCircle (N : ℝ))) ∪ {q}) = 0 :=
    measure_union_null (addCircle_volume_singleton (N : ℝ) p)
      (addCircle_volume_singleton (N : ℝ) q)
  have hJK : J =ᵐ[volume] K := by
    rw [ae_eq_set]
    refine ⟨measure_mono_null ?_ hnull, measure_mono_null ?_ hnull⟩
    · rintro x ⟨hxJ, hxK⟩
      by_contra hc
      simp only [Set.mem_union, Set.mem_singleton_iff, not_or] at hc
      exact hxK ((h x hc.1 hc.2).mp hxJ)
    · rintro x ⟨hxK, hxJ⟩
      by_contra hc
      simp only [Set.mem_union, Set.mem_singleton_iff, not_or] at hc
      exact hxJ ((h x hc.1 hc.2).mpr hxK)
  exact measure_congr hJK

/-- An arc `J` of length `r` has the Haar measure of an open arc `microArc N a r` with the same
endpoints, and almost surely the same particles in it, at every particle. -/
theorem IsMicroArc.exists_ae_agree (P : Parameters) {N : ℕ+} {r : ℝ}
    {J : Set (AddCircle (N : ℝ))} (hJ : IsMicroArc N r J) :
    ∃ a : ℝ, volume J = volume (microArc N a r) ∧
      ∀ᵐ X ∂(gibbsMeasure P N), ∀ i : Fin (N : ℕ),
        (loopPos X i ∈ J ↔ loopPos X i ∈ microArc N a r) := by
  obtain ⟨a, hagree⟩ := hJ.exists_agree
  refine ⟨a, volume_eq_of_agree_off_pair hagree, ?_⟩
  filter_upwards [ae_loopPos_ne_pair P N (a : AddCircle (N : ℝ))
    ((a + r : ℝ) : AddCircle (N : ℝ))] with X hX
  intro i
  exact hagree _ (hX i).1 (hX i).2

end Riesz1

end
end
