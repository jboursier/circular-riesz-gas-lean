/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.Neumann
public import Riesz1.HelfferSjostrand.SobolevClosability

/-!
# The single-valued variational Neumann operator

This uses density in scalar `L²` and the
associated-operator uniqueness theorem. The carrier is the entire
variational domain. Every value is uniquely specified by the weak equation.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Riesz1

variable {N : ℕ+} {c : ℝ} (χ : HsPairPotentials N c) (hc : 0 < c)

/-- The Neumann operator of the Gibbs Dirichlet form, on its full domain. -/
def hsNeumannOperator
    (f : hsNeumannDomain (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))) :
    Lp ℝ 2 (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)) :=
  Internal.formOperator _ (denseRange_hsSobolevValue χ hc) _ f

/-- The value is the unique representative of the variational equation. -/
theorem hsNeumannOperator_eq_iff
    (f : hsNeumannDomain (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)))
    (a : Lp ℝ 2 (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))) :
    hsNeumannOperator χ hc f = a ↔
      (f.val, a) ∈ hsNeumannGraph (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)) :=
  Internal.formOperator_eq_iff _ (denseRange_hsSobolevValue χ hc) _ f a

theorem hsNeumannOperator_mem_graph
    (f : hsNeumannDomain (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))) :
    (f.val, hsNeumannOperator χ hc f) ∈
      hsNeumannGraph (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)) :=
  (hsNeumannOperator_eq_iff χ hc f _).mp rfl

/-- Solving the Neumann equation means exactly the stated integral identity. -/
theorem hsNeumannOperator_eq_iff_integral
    (f : hsNeumannDomain (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)))
    (a : Lp ℝ 2 (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))) :
    hsNeumannOperator χ hc f = a ↔
      ∀ h : HsSobolev (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)),
        ∫ x, inner ℝ (hsSobolevGradient _ f.val x) (hsSobolevGradient _ h x)
          ∂(hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)) =
        ∫ x, a x * hsSobolevValue _ h x
          ∂(hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)) := by
  rw [hsNeumannOperator_eq_iff]
  change (∀ h, hsDirichletForm _ f.val h = inner ℝ a (hsSobolevValue _ h)) ↔ _
  simp only [hsDirichletForm_eq_integral, L2.inner_def, Real.inner_apply]

/-- Symmetry of the variational Neumann operator. This does not identify
the differential expression `hsLangevin` with this operator. -/
theorem hsNeumannOperator_symmetric
    (f g : hsNeumannDomain (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))) :
    inner ℝ (hsNeumannOperator χ hc f) (hsSobolevValue _ g.val) =
      inner ℝ (hsSobolevValue _ f.val) (hsNeumannOperator χ hc g) :=
  Internal.formOperator_symmetric _ (denseRange_hsSobolevValue χ hc) _
    (hsDirichletForm_symmetric _) f g

theorem hsNeumannOperator_nonnegative
    (f : hsNeumannDomain (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))) :
    0 ≤ inner ℝ (hsNeumannOperator χ hc f) (hsSobolevValue _ f.val) :=
  Internal.formOperator_nonnegative _ (denseRange_hsSobolevValue χ hc) _
    (hsDirichletForm_nonnegative _) f

end Riesz1

end
