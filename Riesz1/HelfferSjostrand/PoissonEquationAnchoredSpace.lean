/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.AnchoredNeumannOperator
public import Riesz1.HelfferSjostrand.AnchoredCalculus
public import Riesz1.HelfferSjostrand.ScalarPoincareAnchoredLaw
public import Riesz1.ToMathlib.Variational.EuclideanCompletion
public import Riesz1.ToMathlib.Variational.ProbabilityPoisson

/-! # The Hilbert realization of the anchored Poisson problem

The closed smooth-jet Hilbert space is equivalent to
`AnchoredSobolev`. Its weak equation is precisely the graph of the
anchored Neumann operator, including every Sobolev test.
-/

@[expose] public section

noncomputable section

open MeasureTheory InnerProductSpace

namespace Riesz1

variable {n : ℕ} {c : ℝ} (χ : HsPairPotentials n.succPNat c) (hc : 0 < c)

/-- The anchored Sobolev space with its complete Hilbert norm. -/
abbrev PoissonAnchoredSpace :
    Submodule ℝ (WeightedSobolev.L2Jet (anchoredMeasureE χ) (AnchoredEuclidean n)) := by
  have := isProbabilityMeasure_anchoredMeasureE χ hc
  exact Variational.sobolevSubmodule (anchoredMeasureE χ)
    (anchoredSimplex n) (isBounded_anchoredSimplex n) (ae_mem_anchoredSimplex χ)

/-- The value projection of the anchored completion. -/
abbrev poissonAnchoredValue : PoissonAnchoredSpace χ hc →L[ℝ] Lp ℝ 2 (anchoredMeasureE χ) := by
  have := isProbabilityMeasure_anchoredMeasureE χ hc
  exact Variational.value (anchoredMeasureE χ)
    (anchoredSimplex n) (isBounded_anchoredSimplex n) (ae_mem_anchoredSimplex χ)

/-- The gradient projection of the anchored completion. -/
abbrev poissonAnchoredGradient : PoissonAnchoredSpace χ hc →L[ℝ]
    Lp (AnchoredEuclidean n) 2 (anchoredMeasureE χ) := by
  have := isProbabilityMeasure_anchoredMeasureE χ hc
  exact Variational.grad (anchoredMeasureE χ)
    (anchoredSimplex n) (isBounded_anchoredSimplex n) (ae_mem_anchoredSimplex χ)

/-- The unit of the anchored Sobolev space. -/
abbrev poissonAnchoredUnit : PoissonAnchoredSpace χ hc := by
  have := isProbabilityMeasure_anchoredMeasureE χ hc
  exact Variational.unit (anchoredMeasureE χ)
    (anchoredSimplex n) (isBounded_anchoredSimplex n) (ae_mem_anchoredSimplex χ)

/-- The Hilbert completion and the anchored Sobolev space are exactly equivalent. -/
def poissonAnchoredEquiv : PoissonAnchoredSpace χ hc ≃ AnchoredSobolev χ := by
  have := isProbabilityMeasure_anchoredMeasureE χ hc
  exact {
  toFun f := ⟨(poissonAnchoredValue χ hc f, poissonAnchoredGradient χ hc f),
    Variational.isWeightedH1 _ _ _ _ f⟩
  invFun f := ⟨WithLp.toLp 2 f.val, (Variational.mem_iff _ _ _ _ _ _).mpr f.property⟩
  left_inv _ := by apply Subtype.ext; rfl
  right_inv _ := by apply Subtype.ext; rfl }

/-- The Poisson equation for the actual anchored Neumann operator. -/
def AnchoredPoissonSolves (F : Lp ℝ 2 (anchoredMeasureE χ)) (φ : AnchoredSobolev χ) : Prop := by
  have := isProbabilityMeasure_anchoredMeasureE χ hc
  exact ∃ hφ : ∃ a : Lp ℝ 2 (anchoredMeasureE χ), IsAnchoredLangevin χ φ.val.1 φ.val.2 a,
    anchoredNeumannOperator χ ⟨φ, hφ⟩ = poissonCenter (anchoredMeasureE χ) F

/-- The Poisson energy functional on all of the anchored Sobolev space. -/
def anchoredPoissonEnergy (F : Lp ℝ 2 (anchoredMeasureE χ)) (φ : AnchoredSobolev χ) : ℝ := by
  have := isProbabilityMeasure_anchoredMeasureE χ hc
  exact poissonEnergy (anchoredMeasureE χ) F φ.val.1 φ.val.2

/-- The full weak equation is equivalent to the operator equation. -/
theorem anchoredPoissonSolves_iff (F : Lp ℝ 2 (anchoredMeasureE χ))
    (φ : AnchoredSobolev χ) :
    letI := isProbabilityMeasure_anchoredMeasureE χ hc
    AnchoredPoissonSolves χ hc F φ ↔
      ∀ v : PoissonAnchoredSpace χ hc,
        inner ℝ φ.val.2 (poissonAnchoredGradient χ hc v) =
          inner ℝ (poissonCenter (anchoredMeasureE χ) F) (poissonAnchoredValue χ hc v) := by
  have := isProbabilityMeasure_anchoredMeasureE χ hc
  let μ := anchoredMeasureE χ
  have hi : AnchoredPoissonSolves χ hc F φ ↔
      IsAnchoredLangevin χ φ.val.1 φ.val.2 (poissonCenter μ F) := by
    constructor
    · rintro ⟨hφ, he⟩
      exact (anchoredNeumannOperator_eq_iff χ hc ⟨φ, hφ⟩ _).mp he
    · intro he
      exact ⟨⟨poissonCenter μ F, he⟩,
        (anchoredNeumannOperator_eq_iff χ hc ⟨φ, ⟨_, he⟩⟩ _).mpr he⟩
  rw [hi]
  constructor
  · intro h v
    have hv := Variational.isWeightedH1 (anchoredMeasureE χ) (anchoredSimplex n)
      (isBounded_anchoredSimplex n) (ae_mem_anchoredSimplex χ) v
    rw [L2.inner_def, poisson_inner_eq_integral]
    exact h.2.2 _ _ hv
  · intro h
    refine ⟨φ.property, Lp.memLp _, fun H K hHK => ?_⟩
    have hpair : IsAnchoredH1 χ (hHK.1.toLp H) (hHK.2.1.toLp K) :=
      WeightedSobolev.IsWeightedH1.congr hHK hHK.1.coeFn_toLp.symm hHK.2.1.coeFn_toLp.symm
    let v : PoissonAnchoredSpace χ hc :=
      ⟨WithLp.toLp 2 (hHK.1.toLp H, hHK.2.1.toLp K),
        (Variational.mem_iff _ _ _ _ _ _).mpr hpair⟩
    have hh := h v
    change inner ℝ φ.val.2 (hHK.2.1.toLp K) =
      inner ℝ (poissonCenter μ F) (hHK.1.toLp H) at hh
    rw [L2.inner_def, poisson_inner_eq_integral] at hh
    calc
      _ = ∫ y, inner ℝ (φ.val.2 y) (hHK.2.1.toLp K y) ∂μ :=
        integral_congr_ae (hHK.2.1.coeFn_toLp.mono fun y hy =>
          congrArg (fun k => inner ℝ (φ.val.2 y) k) hy.symm)
      _ = ∫ y, poissonCenter μ F y * hHK.1.toLp H y ∂μ := hh
      _ = _ := integral_congr_ae (hHK.1.coeFn_toLp.mono fun y hy =>
        congrArg (fun r => poissonCenter μ F y * r) hy)

/-- Poincaré in the Hilbert coordinates of the anchored space. -/
theorem poissonAnchored_poincare (hPL : External.PrekopaLeindler) (hn : 0 < n)
    (v : PoissonAnchoredSpace χ hc) :
    letI := isProbabilityMeasure_anchoredMeasureE χ hc
    ‖poissonAnchoredValue χ hc v‖ ^ 2 -
      (poissonMean (anchoredMeasureE χ) (poissonAnchoredValue χ hc v)) ^ 2 ≤
      (2 * c)⁻¹ * ‖poissonAnchoredGradient χ hc v‖ ^ 2 := by
  have := isProbabilityMeasure_anchoredMeasureE χ hc
  have h := scalar_poincare_anchoredLaw hPL hn χ hc
    (Variational.isWeightedH1 (anchoredMeasureE χ) (anchoredSimplex n)
      (isBounded_anchoredSimplex n) (ae_mem_anchoredSimplex χ) v)
  rw [poisson_variance_eq] at h
  have hg : (∫ y, ‖poissonAnchoredGradient χ hc v y‖ ^ 2 ∂anchoredMeasureE χ) =
      ‖poissonAnchoredGradient χ hc v‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    simp only [real_inner_self_eq_norm_sq]
  rw [hg] at h
  exact h

end Riesz1

end
