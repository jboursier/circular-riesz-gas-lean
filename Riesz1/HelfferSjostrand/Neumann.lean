/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.Sobolev
public import Riesz1.HelfferSjostrand.SettingForm

/-!
# The variational Neumann graph and domain

This file specifies the graph and domain. The graph is
closed, symmetric and nonnegative. Defining the single-valued operator
still requires density of `hsSobolevValue` in `L²`. This file does not
assume that density or choose an unproved unique representative.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Topology

namespace Riesz1

variable {N : ℕ+} (μ : Measure (HsConfiguration N)) [IsFiniteMeasure μ]

/-- The full graph of the weak Neumann equation, before selecting its output. -/
def hsNeumannGraph : Submodule ℝ (HsSobolev μ × Lp ℝ 2 μ) where
  carrier := {p | ∀ h, hsDirichletForm μ p.1 h = inner ℝ p.2 (hsSobolevValue μ h)}
  zero_mem' := by simp [hsDirichletForm]
  add_mem' := by
    intro p q hp hq h
    change hsDirichletForm μ (p.1 + q.1) h = inner ℝ (p.2 + q.2) (hsSobolevValue μ h)
    rw [hsDirichletForm_add_left, hp, hq, inner_add_left]
  smul_mem' := by
    intro a p hp h
    change hsDirichletForm μ (a • p.1) h = inner ℝ (a • p.2) (hsSobolevValue μ h)
    rw [hsDirichletForm_smul_left, hp, real_inner_smul_left]

/-- All Sobolev functions admitting an `L²` variational representative. -/
def hsNeumannDomain : Set (HsSobolev μ) :=
  Internal.formOperatorDomain (hsSobolevValue μ) (hsDirichletForm μ)

theorem hsNeumannDomain_iff (f : HsSobolev μ) :
    f ∈ hsNeumannDomain μ ↔ ∃ a : Lp ℝ 2 μ, (f, a) ∈ hsNeumannGraph μ := Iff.rfl

theorem isClosed_hsNeumannGraph :
    IsClosed (hsNeumannGraph μ : Set (HsSobolev μ × Lp ℝ 2 μ)) := by
  change IsClosed {p : HsSobolev μ × Lp ℝ 2 μ |
    ∀ h, hsDirichletForm μ p.1 h = inner ℝ p.2 (hsSobolevValue μ h)}
  simp only [ofPred_forall]
  apply isClosed_iInter
  intro h
  exact isClosed_eq (((hsSobolevGradient μ).continuous.comp continuous_fst).inner continuous_const)
    (continuous_snd.inner continuous_const)

theorem hsNeumannGraph_eq_integral (p : hsNeumannGraph μ) (h : HsSobolev μ) :
    ∫ x, inner ℝ (hsSobolevGradient μ p.val.1 x) (hsSobolevGradient μ h x) ∂μ =
      ∫ x, p.val.2 x * hsSobolevValue μ h x ∂μ := by
  simpa only [hsDirichletForm, L2.inner_def, Real.inner_apply]
    using p.property h

/-- Symmetry of the variational graph, without a choice of representative. -/
theorem hsNeumannGraph_symmetric (p q : hsNeumannGraph μ) :
    inner ℝ p.val.2 (hsSobolevValue μ q.val.1) =
      inner ℝ (hsSobolevValue μ p.val.1) q.val.2 := by
  rw [← p.property, real_inner_comm, ← q.property]
  exact hsDirichletForm_symmetric μ _ _

theorem hsNeumannGraph_nonnegative (p : hsNeumannGraph μ) :
    0 ≤ inner ℝ p.val.2 (hsSobolevValue μ p.val.1) := by
  rw [← p.property]
  exact hsDirichletForm_nonnegative μ _

end Riesz1

end
