/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.AnchoredLawSobolev
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# The anchored Neumann operator on its full variational domain

The definition is variational.
Values and gradients are `L²` classes, so uniqueness of the Neumann element
specifies an actual function. Its domain contains precisely the Sobolev
pairs admitting such an element.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Riesz1

variable {n : ℕ} {c : ℝ} (χ : HsPairPotentials n.succPNat c)

/-- The anchored Sobolev completion, represented by its value and gradient classes. -/
def AnchoredSobolev :=
  {p : Lp ℝ 2 (anchoredMeasureE χ) × Lp (AnchoredEuclidean n) 2 (anchoredMeasureE χ) //
    IsAnchoredH1 χ p.1 p.2}

/-- The entire variational domain of the anchored Neumann operator. -/
def anchoredNeumannDomain :=
  {f : AnchoredSobolev χ // ∃ a : Lp ℝ 2 (anchoredMeasureE χ),
    IsAnchoredLangevin χ f.val.1 f.val.2 a}

/-- The uniquely specified Neumann element, as an `L²` class. -/
def anchoredNeumannOperator (f : anchoredNeumannDomain χ) : Lp ℝ 2 (anchoredMeasureE χ) :=
  f.property.choose

/-- The chosen element satisfies the defining weak equation. -/
theorem anchoredNeumannOperator_spec (f : anchoredNeumannDomain χ) :
    IsAnchoredLangevin χ f.val.val.1 f.val.val.2 (anchoredNeumannOperator χ f) :=
  f.property.choose_spec

/-- The operator has exactly the prescribed variational graph. -/
theorem anchoredNeumannOperator_eq_iff (hc : 0 < c) (f : anchoredNeumannDomain χ)
    (a : Lp ℝ 2 (anchoredMeasureE χ)) :
    anchoredNeumannOperator χ f = a ↔ IsAnchoredLangevin χ f.val.val.1 f.val.val.2 a := by
  constructor
  · rintro rfl
    exact anchoredNeumannOperator_spec χ f
  · intro ha
    exact Lp.ext (ae_eq_of_isAnchoredLangevin χ hc (anchoredNeumannOperator_spec χ f) ha)

/-- Solving the anchored Neumann equation is exactly the weak integral identity. -/
theorem anchoredNeumannOperator_eq_iff_integral (hc : 0 < c)
    (f : anchoredNeumannDomain χ) (a : Lp ℝ 2 (anchoredMeasureE χ)) :
    anchoredNeumannOperator χ f = a ↔
      ∀ H K, IsAnchoredH1 χ H K →
        ∫ y, inner ℝ (f.val.val.2 y) (K y) ∂anchoredMeasureE χ =
          ∫ y, a y * H y ∂anchoredMeasureE χ := by
  rw [anchoredNeumannOperator_eq_iff χ hc]
  exact ⟨fun h => h.2.2, fun h => ⟨f.val.property, Lp.memLp a, h⟩⟩

/-- Symmetry of the anchored variational operator. -/
theorem anchoredNeumannOperator_symmetric (f g : anchoredNeumannDomain χ) :
    inner ℝ (anchoredNeumannOperator χ f) g.val.val.1 =
      inner ℝ f.val.val.1 (anchoredNeumannOperator χ g) := by
  have hf := (anchoredNeumannOperator_spec χ f).2.2 _ _ g.val.property
  have hg := (anchoredNeumannOperator_spec χ g).2.2 _ _ f.val.property
  rw [L2.inner_def, L2.inner_def]
  simp only [Real.inner_apply]
  calc
    _ = ∫ y, inner ℝ (f.val.val.2 y) (g.val.val.2 y) ∂anchoredMeasureE χ := by
      simpa only [mul_comm] using hf.symm
    _ = ∫ y, inner ℝ (g.val.val.2 y) (f.val.val.2 y) ∂anchoredMeasureE χ := by
      exact integral_congr_ae (Filter.Eventually.of_forall fun y => real_inner_comm _ _)
    _ = _ := by simpa only [mul_comm] using hg

/-- Nonnegativity of the anchored variational operator. -/
theorem anchoredNeumannOperator_nonnegative (f : anchoredNeumannDomain χ) :
    0 ≤ inner ℝ (anchoredNeumannOperator χ f) f.val.val.1 := by
  have hf := (anchoredNeumannOperator_spec χ f).2.2 _ _ f.val.property
  rw [L2.inner_def]
  simp only [Real.inner_apply]
  rw [← hf]
  exact integral_nonneg fun y => real_inner_self_nonneg

end Riesz1

end
