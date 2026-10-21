/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.PoissonEquationAnchoredSpace

/-! # The scalar Poisson equation for the anchored law

Lemma A.2, anchored clause. The theorem quantifies
over the entire `AnchoredSobolev` space and uses the actual
`anchoredNeumannOperator` on its variational domain.
-/

public section

noncomputable section

open MeasureTheory InnerProductSpace

namespace Riesz1

variable {n : ℕ} {c : ℝ} (χ : HsPairPotentials n.succPNat c) (hc : 0 < c)

/-- **Scalar Poisson equation** (Lemma A.2, anchored law).
Every solution has the displayed value and gradient, and the solutions
are exactly all minimizers over the Sobolev space. -/
theorem scalar_poisson_anchoredLaw (hPL : External.PrekopaLeindler) (hn : 0 < n)
    (F : Lp ℝ 2 (anchoredMeasureE χ)) :
    letI := isProbabilityMeasure_anchoredMeasureE χ hc
    ∃ φ : AnchoredSobolev χ,
      (∫ y, φ.val.1 y ∂anchoredMeasureE χ) = 0 ∧ AnchoredPoissonSolves χ hc F φ ∧
      (∀ ψ : AnchoredSobolev χ, (∫ y, ψ.val.1 y ∂anchoredMeasureE χ) = 0 →
        AnchoredPoissonSolves χ hc F ψ → ψ = φ) ∧
      (∀ ψ : AnchoredSobolev χ, AnchoredPoissonSolves χ hc F ψ ↔
        ∃ a : ℝ, ψ.val.1 = φ.val.1 + a • Lp.const 2 (anchoredMeasureE χ) (1 : ℝ) ∧
          ψ.val.2 = φ.val.2) ∧
      (∀ ψ : AnchoredSobolev χ, (∀ h : AnchoredSobolev χ,
        anchoredPoissonEnergy χ hc F ψ ≤ anchoredPoissonEnergy χ hc F h) ↔
          AnchoredPoissonSolves χ hc F ψ) := by
  have := isProbabilityMeasure_anchoredMeasureE χ hc
  let μ := anchoredMeasureE χ
  let J := poissonAnchoredValue χ hc
  let G := poissonAnchoredGradient χ hc
  let e := poissonAnchoredUnit χ hc
  let q := poissonAnchoredEquiv χ hc
  have he : J e = Lp.const 2 μ (1 : ℝ) := Variational.unit_value _ _ _ _
  have hGe : G e = 0 := Variational.unit_grad _ _ _ _
  obtain ⟨u, hm, hu, hunique, hchar, hmin⟩ := Internal.probability_poisson μ J G e he hGe
    (Variational.norm_sq _ _ _ _) ((2 * c)⁻¹) (by positivity)
    (poissonAnchored_poincare χ hc hPL hn) F
  have hsol (v : PoissonAnchoredSpace χ hc) :
      AnchoredPoissonSolves χ hc F (q v) ↔
        ∀ w, inner ℝ (G v) (G w) = inner ℝ (poissonCenter μ F) (J w) :=
    anchoredPoissonSolves_iff χ hc F (q v)
  have henergy (v : PoissonAnchoredSpace χ hc) :
      anchoredPoissonEnergy χ hc F (q v) =
        ‖G v‖ ^ 2 - 2 * inner ℝ (poissonCenter μ F) (J v) :=
    poissonEnergy_eq μ F (J v) (G v)
  refine ⟨q u, (poissonMean_eq_integral μ _).symm.trans hm,
    (hsol u).mpr hu, ?_, ?_, ?_⟩
  · intro ψ hmean hψ
    have hψ' : AnchoredPoissonSolves χ hc F (q (q.symm ψ)) := by simpa using hψ
    have hmean' : poissonMean μ (J (q.symm ψ)) = 0 :=
      (poissonMean_eq_integral μ _).trans hmean
    have hv := hunique (q.symm ψ) hmean' ((hsol _).mp hψ')
    exact (q.apply_symm_apply ψ).symm.trans (congrArg q hv)
  · intro ψ
    have hψeq : q (q.symm ψ) = ψ := q.apply_symm_apply ψ
    rw [← hψeq, hsol, hchar]
    constructor
    · rintro ⟨a, ha⟩
      refine ⟨a, ?_, ?_⟩
      · change J (q.symm ψ) = J u + a • Lp.const 2 μ (1 : ℝ)
        rw [ha, map_add, map_smul, he]
      · change G (q.symm ψ) = G u
        rw [ha, map_add, map_smul, hGe, smul_zero, add_zero]
    · rintro ⟨a, ha, hg⟩
      refine ⟨a, ?_⟩
      apply Subtype.ext
      apply (WithLp.equiv 2 _).injective
      apply Prod.ext
      · change J (q.symm ψ) = J (u + a • e)
        rw [map_add, map_smul, he]
        exact ha
      · change G (q.symm ψ) = G (u + a • e)
        rw [map_add, map_smul, hGe, smul_zero, add_zero]
        exact hg
  · intro ψ
    have hψeq : q (q.symm ψ) = ψ := q.apply_symm_apply ψ
    rw [← hψeq, hsol]
    have hall : (∀ h : AnchoredSobolev χ,
        anchoredPoissonEnergy χ hc F (q (q.symm ψ)) ≤ anchoredPoissonEnergy χ hc F h) ↔
        (∀ w : PoissonAnchoredSpace χ hc,
          ‖G (q.symm ψ)‖ ^ 2 - 2 * inner ℝ (poissonCenter μ F) (J (q.symm ψ)) ≤
            ‖G w‖ ^ 2 - 2 * inner ℝ (poissonCenter μ F) (J w)) := by
      constructor
      · intro hh w
        simpa only [henergy] using hh (q w)
      · intro hh h
        have hv := hh (q.symm h)
        rw [← henergy, ← henergy, q.apply_symm_apply] at hv
        exact hv
    exact hall.trans (hmin _)

/-- The unique mean-zero solution in the anchored Sobolev space. -/
theorem scalar_poisson_anchoredLaw_existsUnique (hPL : External.PrekopaLeindler)
    (hn : 0 < n) (F : Lp ℝ 2 (anchoredMeasureE χ)) :
    ∃! φ : AnchoredSobolev χ,
      (∫ y, φ.val.1 y ∂anchoredMeasureE χ) = 0 ∧ AnchoredPoissonSolves χ hc F φ := by
  obtain ⟨φ, hm, hs, hu, _⟩ := scalar_poisson_anchoredLaw χ hc hPL hn F
  exact ⟨φ, ⟨hm, hs⟩, fun ψ hψ => hu ψ hψ.1 hψ.2⟩

end Riesz1

end
