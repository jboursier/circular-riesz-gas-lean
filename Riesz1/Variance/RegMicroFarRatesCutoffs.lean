/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.RegMicroNearFarCutoffs
import all Riesz1.ToMathlib.FiniteMarkDistance
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Derivative bounds and transitions of the actual microscopic cutoffs

Quantitative cutoff facts used in Lemma 5.3. Endpoint
derivatives vanish by the extremum theorem, so the closed transition
boundaries require no exceptional cases.
-/

public section

open Set Filter Topology

namespace Riesz1.Internal

/-- A separated cutoff sum has zero derivative whenever its value is zero. -/
theorem microCutoffSum_deriv_eq_zero_of_zero {ι : Type*} [Fintype ι] {L r : ℝ}
    (hr : 0 < r) (a : ι → ℝ)
    (hsep : ∀ i j, i ≠ j → 4*r ≤ dist (a i : AddCircle L) (a j : AddCircle L))
    {x : ℝ} (hx : microCutoffSum L r a (x : AddCircle L) = 0) :
    deriv (fun t : ℝ => microCutoffSum L r a (t : AddCircle L)) x = 0 := by
  apply IsLocalMin.deriv_eq_zero
  apply Eventually.of_forall
  intro t
  dsimp only
  rw [hx]
  exact (microCutoffSum_mem_Icc hr a hsep (t : AddCircle L)).1

/-- The derivative also vanishes on the plateau at one, including its boundary. -/
theorem microCutoffSum_deriv_eq_zero_of_one {ι : Type*} [Fintype ι] {L r : ℝ}
    (hr : 0 < r) (a : ι → ℝ)
    (hsep : ∀ i j, i ≠ j → 4*r ≤ dist (a i : AddCircle L) (a j : AddCircle L))
    {x : ℝ} (hx : microCutoffSum L r a (x : AddCircle L) = 1) :
    deriv (fun t : ℝ => microCutoffSum L r a (t : AddCircle L)) x = 0 := by
  apply IsLocalMax.deriv_eq_zero
  apply Eventually.of_forall
  intro t
  dsimp only
  rw [hx]
  exact (microCutoffSum_mem_Icc hr a hsep (t : AddCircle L)).2

/-- A single universal constant controls all cutoff sums, with their
actual number of summands. -/
theorem microCutoffSum_deriv_bound {ι : Type*} [Fintype ι] :
    ∃ D : ℝ, 0 < D ∧ ∀ (L r : ℝ), 0 < L → 0 < r → 4*r < L →
      ∀ (a : ι → ℝ) (x : ℝ),
        |deriv (fun t : ℝ => microCutoffSum L r a (t : AddCircle L)) x| ≤
          (Fintype.card ι : ℝ)*D/r := by
  obtain ⟨D, hD, hb⟩ := sum_markCut_cutoffBump_smooth_bounds (ι := ι)
  refine ⟨D, hD, fun L r hL hr hroom a x => ?_⟩
  simp_rw [microCutoffSum_coe]
  exact (hb L r hL hr hroom a).2 x

/-- A nonzero derivative of the moving cutoff can occur only in its
actual transition: all distances exceed the inner radius, and at least
one distance is strictly below the outer radius. -/
theorem microCutoffSum_transition_of_deriv_ne_zero {ι : Type*} [Fintype ι] {L r : ℝ}
    (hr : 0 < r) (a : ι → ℝ)
    (hsep : ∀ i j, i ≠ j → 4*r ≤ dist (a i : AddCircle L) (a j : AddCircle L))
    {x : ℝ}
    (hx : deriv (fun t : ℝ => microCutoffSum L r a (t : AddCircle L)) x ≠ 0) :
    (∀ j, r < dist (x : AddCircle L) (a j : AddCircle L)) ∧
      ∃ j, dist (x : AddCircle L) (a j : AddCircle L) < 2*r := by
  constructor
  · intro j
    by_contra hn
    exact hx (microCutoffSum_deriv_eq_zero_of_one hr a hsep
      (microCutoffSum_eq_one hr a hsep j (le_of_not_gt hn)))
  · by_contra hn
    push Not at hn
    exact hx (microCutoffSum_deriv_eq_zero_of_zero hr a hsep
      (microCutoffSum_eq_zero hr a hn))

/-- Near a separated mark, the capped nearest-mark distance is exactly
the distance to this mark. This converts the kernel envelope to the
individual envelope required by the translated a priori bound. -/
theorem cappedMarkDistance_eq_dist_of_near {X ι : Type*} [MetricSpace X]
    [Fintype ι] [Nonempty ι] {r : ℝ} (a : ι → X)
    (hsep : ∀ i j, i ≠ j → 4*r ≤ dist (a i) (a j))
    (hr : 2*r ≤ 1) {x : X} (j : ι) (hx : dist x (a j) ≤ 2*r) :
    cappedMarkDistance a x = dist x (a j) := by
  apply le_antisymm (cappedMarkDistance_le_dist a x j)
  unfold cappedMarkDistance
  apply le_min (hx.trans hr)
  apply Finset.le_inf'
  intro k _
  by_cases hk : k = j
  · subst k
    exact le_rfl
  · have ht := dist_triangle (a j) x (a k)
    rw [dist_comm (a j) x] at ht
    linarith [hsep j k (Ne.symm hk)]

/-- Below the cap, the nearest distance is attained by a mark. -/
theorem exists_dist_eq_cappedMarkDistance {X ι : Type*} [PseudoMetricSpace X]
    [Fintype ι] [Nonempty ι] (a : ι → X) (x : X)
    (hx : cappedMarkDistance a x < 1) :
    ∃ j, dist x (a j) = cappedMarkDistance a x := by
  classical
  obtain ⟨j, _hj, heq⟩ := Finset.exists_mem_eq_inf' (s := Finset.univ)
    Finset.univ_nonempty (fun j => dist x (a j))
  unfold cappedMarkDistance at hx ⊢
  rw [heq] at hx ⊢
  have hd : dist x (a j) < 1 := (min_lt_iff.mp hx).resolve_left (lt_irrefl _)
  exact ⟨j, (min_eq_right hd.le).symm⟩

/-- Lower bounds on all distances give a lower bound on the capped distance. -/
theorem le_cappedMarkDistance_of_forall_dist {X ι : Type*} [PseudoMetricSpace X]
    [Fintype ι] [Nonempty ι] (a : ι → X) (x : X) {r : ℝ}
    (hr : r ≤ 1) (hd : ∀ j, r ≤ dist x (a j)) :
    r ≤ cappedMarkDistance a x := by
  unfold cappedMarkDistance
  apply le_min hr
  exact (Finset.le_inf'_iff _ _).mpr fun j _ => hd j

end Riesz1.Internal
