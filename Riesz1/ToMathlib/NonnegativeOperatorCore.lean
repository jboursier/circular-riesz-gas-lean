/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# A core criterion for nonnegative operators

A restriction of a closed nonnegative operator is an operator core if
its positively shifted range is dense. This is the functional analytic
step. The criterion is internal because its
kernel hypothesis must be proved from the differential equation.
-/

@[expose] public section

noncomputable section

open Set

namespace Riesz1.Internal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The shifted output of a graph pair. -/
def graphShift (lam : ℝ) : (E × E) →L[ℝ] E :=
  ContinuousLinearMap.snd ℝ E E + lam • ContinuousLinearMap.fst ℝ E E

/-- Positivity controls the input by a positive shift of the output. -/
theorem norm_fst_le_graphShift {lam : ℝ} (hlam : 1 ≤ lam) {p : E × E}
    (hp : 0 ≤ inner ℝ p.2 p.1) : ‖p.1‖ ≤ ‖graphShift lam p‖ := by
  have hi := real_inner_le_norm (p.2 + lam • p.1) p.1
  rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq] at hi
  by_cases hz : ‖p.1‖ = 0
  · rw [hz]
    exact norm_nonneg _
  · have hpos : 0 < ‖p.1‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    change ‖p.1‖ ≤ ‖p.2 + lam • p.1‖
    nlinarith [sq_nonneg ‖p.1‖]

/-- The graph norm is controlled by the shifted output. -/
theorem norm_le_graphShift {lam : ℝ} (hlam : 1 ≤ lam) {p : E × E}
    (hp : 0 ≤ inner ℝ p.2 p.1) : ‖p‖ ≤ (1 + lam) * ‖graphShift lam p‖ := by
  have hf := norm_fst_le_graphShift hlam hp
  have hl : 0 ≤ lam := (by norm_num : (0 : ℝ) ≤ 1).trans hlam
  have hs : ‖p.2‖ ≤ ‖graphShift lam p‖ + lam * ‖p.1‖ := by
    have he : p.2 = graphShift lam p - lam • p.1 := by simp [graphShift]
    calc
      _ = ‖graphShift lam p - lam • p.1‖ := congrArg norm he
      _ ≤ ‖graphShift lam p‖ + ‖lam • p.1‖ := norm_sub_le _ _
      _ = _ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hl]
  rw [Prod.norm_def]
  apply max_le
  · nlinarith [norm_nonneg (graphShift lam p)]
  · nlinarith

/-- Dense shifted range identifies the closure of a restriction with its
closed nonnegative extension. No assertion about a differential core is
hidden in the hypotheses. -/
theorem graph_closure_eq_of_dense_shift [CompleteSpace E] (A G : Submodule ℝ (E × E))
    (hA : IsClosed (A : Set (E × E))) (hGA : G ≤ A)
    (hpos : ∀ p ∈ A, 0 ≤ inner ℝ p.2 p.1)
    {lam : ℝ} (hlam : 1 ≤ lam)
    (hd : Dense ((G.map (graphShift lam).toLinearMap : Submodule ℝ E) : Set E)) :
    G.topologicalClosure = A := by
  let B := G.topologicalClosure
  have hBA : B ≤ A := G.topologicalClosure_minimal hGA hA
  let T : B →L[ℝ] E := (graphShift lam).comp B.subtypeL
  have ha : AntilipschitzWith ⟨1 + lam, by linarith⟩ T := by
    apply T.antilipschitz_of_bound
    intro p
    exact norm_le_graphShift hlam (hpos p.val (hBA p.property))
  have hr : IsClosed (range T) := ha.isClosed_range T.uniformContinuous
  have hsurj : Function.Surjective T := by
    have hsub : (G.map (graphShift lam).toLinearMap : Set E) ⊆ range T := by
      rintro y ⟨p, hp, rfl⟩
      exact ⟨⟨p, G.le_topologicalClosure hp⟩, rfl⟩
    exact fun y => (hr.closure_subset_iff.mpr hsub) (hd y)
  apply le_antisymm hBA
  intro p hp
  obtain ⟨q, hq⟩ := hsurj (graphShift lam p)
  have hz : p - q.val ∈ A := A.sub_mem hp (hBA q.property)
  have he : p = q.val := by
    have hb := norm_le_graphShift hlam (hpos _ hz)
    have hs : graphShift lam (p - q.val) = 0 := by
      rw [map_sub]
      exact sub_eq_zero.mpr hq.symm
    rw [hs, norm_zero, mul_zero] at hb
    exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hb (norm_nonneg _)))
  exact he.symm ▸ q.property

/-- An adjoint-kernel calculation supplies the dense-range hypothesis
in the preceding core criterion. -/
theorem graph_closure_eq_of_shift_kernel [CompleteSpace E] (A G : Submodule ℝ (E × E))
    (hA : IsClosed (A : Set (E × E))) (hGA : G ≤ A)
    (hpos : ∀ p ∈ A, 0 ≤ inner ℝ p.2 p.1)
    {lam : ℝ} (hlam : 1 ≤ lam)
    (hker : ∀ u : E, (∀ p ∈ G, inner ℝ (graphShift lam p) u = 0) → u = 0) :
    G.topologicalClosure = A := by
  apply graph_closure_eq_of_dense_shift A G hA hGA hpos hlam
  let S := G.map (graphShift lam).toLinearMap
  have hb : Sᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro u hu
    change u = 0
    apply hker u
    intro p hp
    exact hu _ ⟨p, hp, rfl⟩
  have ht : S.topologicalClosure = ⊤ := by
    apply Submodule.orthogonal_eq_bot_iff.mp
    rw [Submodule.orthogonal_closure, hb]
  change Dense (S : Set E)
  rw [dense_iff_closure_eq, ← Submodule.topologicalClosure_coe, ht]
  rfl

end Riesz1.Internal
