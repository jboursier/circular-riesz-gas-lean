/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.NeumannOperator
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# The scalar Neumann resolvent and density in the form norm

This is the resolvent step of the boundary argument.
It concerns the full variational operator domain. Density of the
collision-free test class is a separate boundary assertion.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Riesz1

variable {N : ℕ+} (μ : Measure (HsConfiguration N)) [IsFiniteMeasure μ]

/-- The Sobolev inner product is the sum of the value and energy pairings. -/
theorem hsSobolev_inner_eq (f h : HsSobolev μ) :
    inner ℝ f h = inner ℝ (hsSobolevValue μ f) (hsSobolevValue μ h) +
      hsDirichletForm μ f h := by
  exact WithLp.prod_inner_apply f.val h.val

/-- The resolvent of the scalar variational operator at `-1`. Its value is
the Riesz representative of `h ↦ ⟨g, h⟩` in the Sobolev Hilbert space. -/
def hsNeumannResolvent : Lp ℝ 2 μ →L[ℝ] HsSobolev μ :=
  (hsSobolevValue μ).adjoint

/-- The defining resolvent equation, for every Sobolev test. -/
theorem hsNeumannResolvent_equation (g : Lp ℝ 2 μ) (h : HsSobolev μ) :
    hsDirichletForm μ (hsNeumannResolvent μ g) h +
      inner ℝ (hsSobolevValue μ (hsNeumannResolvent μ g)) (hsSobolevValue μ h) =
        inner ℝ g (hsSobolevValue μ h) := by
  rw [add_comm, ← hsSobolev_inner_eq]
  exact (hsSobolevValue μ).adjoint_inner_left h g

/-- Resolvent values belong to the entire variational Neumann graph. -/
theorem hsNeumannResolvent_mem_graph (g : Lp ℝ 2 μ) :
    (hsNeumannResolvent μ g, g - hsSobolevValue μ (hsNeumannResolvent μ g)) ∈
      hsNeumannGraph μ := by
  intro h
  rw [inner_sub_left]
  linarith [hsNeumannResolvent_equation μ g h]

/-- The range of the resolvent is exactly the variational operator domain. -/
theorem range_hsNeumannResolvent :
    range (hsNeumannResolvent μ) = hsNeumannDomain μ := by
  ext f
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨_, hsNeumannResolvent_mem_graph μ g⟩
  · rintro ⟨a, ha⟩
    refine ⟨a + hsSobolevValue μ f, ?_⟩
    apply ext_inner_right ℝ
    intro h
    rw [hsNeumannResolvent, ContinuousLinearMap.adjoint_inner_left, inner_add_left,
      hsSobolev_inner_eq, ← ha h]
    ring

namespace Internal

theorem denseRange_adjoint_of_injective {V E : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (j : V →L[ℝ] E) (hj : Function.Injective j) : DenseRange j.adjoint := by
  rw [denseRange_iff_closure_range]
  change closure (j.adjoint.range : Set V) = univ
  rw [← Submodule.topologicalClosure_coe, ← ContinuousLinearMap.orthogonal_ker,
    LinearMap.ker_eq_bot.mpr hj, Submodule.bot_orthogonal_eq_top]
  rfl

end Internal

/-- The full Neumann domain is dense for the `H¹` norm, as required in the
resolvent step. No boundary-core result is used. -/
theorem dense_hsNeumannDomain {c : ℝ} (χ : HsPairPotentials N c) (hc : 0 < c) :
    Dense (hsNeumannDomain (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))) := by
  let ν := (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))
  have hr : Dense (range (hsNeumannResolvent ν)) :=
    Internal.denseRange_adjoint_of_injective (hsSobolevValue ν) (hsSobolevValue_injective χ hc)
  exact hr.mono (range_hsNeumannResolvent ν).le

end Riesz1
