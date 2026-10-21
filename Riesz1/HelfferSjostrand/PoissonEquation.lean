/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.NeumannOperator
public import Riesz1.HelfferSjostrand.ScalarPoincareGibbs
public import Riesz1.ToMathlib.Variational.ProbabilityPoisson

/-! # The scalar Poisson equation for the Gibbs probability

Lemma A.2: the mean-zero solution, the affine
space of all solutions, and the minimizers of the Dirichlet functional.
The boundary growth assumption is unnecessary. Positive pair curvature
and the external Prékopa–Leindler statement suffice.
-/

@[expose] public section

noncomputable section

open MeasureTheory InnerProductSpace

namespace Riesz1

variable {N : ℕ+}

/-- The unit function in the actual periodic Sobolev completion. -/
def hsPoissonUnit (μ : Measure (HsConfiguration N)) [IsFiniteMeasure μ] : HsSobolev μ :=
  hsSobolevOfSmooth μ ⟨fun _ => 1,
    ⟨fun _ _ => rfl, Set.univ, isOpen_univ, Set.subset_univ _, contDiffOn_const⟩⟩

theorem hsPoissonUnit_value (μ : Measure (HsConfiguration N)) [IsFiniteMeasure μ] :
    hsSobolevValue μ (hsPoissonUnit μ) = Lp.const 2 μ (1 : ℝ) := by
  apply Lp.ext
  exact ((show HsSmoothOnClosure N (fun _ => (1 : ℝ)) from
    ⟨fun _ _ => rfl, Set.univ, isOpen_univ, Set.subset_univ _, contDiffOn_const⟩).memLp_value μ
    ).coeFn_toLp.trans (Lp.coeFn_const 2 μ (1 : ℝ)).symm

theorem hsPoissonUnit_gradient (μ : Measure (HsConfiguration N)) [IsFiniteMeasure μ] :
    hsSobolevGradient μ (hsPoissonUnit μ) = 0 := by
  have h := (show HsSmoothOnClosure N (fun _ => (1 : ℝ)) from
    ⟨fun _ _ => rfl, Set.univ, isOpen_univ, Set.subset_univ _, contDiffOn_const⟩).memLp_gradient μ
  change h.toLp _ = 0
  apply Lp.ext
  filter_upwards [h.coeFn_toLp, Lp.coeFn_zero (HsEuclidean N) 2 μ] with x hx hz
  rw [hx, hz]
  exact gradient_fun_const _ _

/-- The Dirichlet functional with source `F`, on the entire Sobolev space. -/
def hsPoissonEnergy (μ : Measure (HsConfiguration N)) [IsProbabilityMeasure μ]
    (F : Lp ℝ 2 μ) (h : HsSobolev μ) : ℝ :=
  ∫ x, ‖hsSobolevGradient μ h x‖ ^ 2 -
    2 * hsSobolevValue μ h x * (F x - ∫ y, F y ∂μ) ∂μ

theorem hsPoissonEnergy_eq (μ : Measure (HsConfiguration N)) [IsProbabilityMeasure μ]
    (F : Lp ℝ 2 μ) (h : HsSobolev μ) :
    hsPoissonEnergy μ F h = ‖hsSobolevGradient μ h‖ ^ 2 -
      2 * inner ℝ (poissonCenter μ F) (hsSobolevValue μ h) :=
  poissonEnergy_eq μ F (hsSobolevValue μ h) (hsSobolevGradient μ h)

variable {c : ℝ} (χ : HsPairPotentials N c) (hc : 0 < c)

/-- The Poisson equation for the Neumann operator, including domain membership. -/
def HsPoissonSolves
    (F : Lp ℝ 2 (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)))
    (φ : HsSobolev (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))) : Prop :=
  ∃ hφ : φ ∈ hsNeumannDomain (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)),
    hsNeumannOperator χ hc ⟨φ, hφ⟩ = poissonCenter _ F

theorem hsPoissonSolves_iff
    (F : Lp ℝ 2 (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)))
    (φ : HsSobolev (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))) :
    HsPoissonSolves χ hc F φ ↔ ∀ h,
      inner ℝ (hsSobolevGradient _ φ) (hsSobolevGradient _ h) =
        inner ℝ (poissonCenter _ F) (hsSobolevValue _ h) := by
  constructor
  · rintro ⟨hφ, he⟩
    exact (hsNeumannOperator_eq_iff χ hc ⟨φ, hφ⟩ _).mp he
  · intro hφ
    have hd : φ ∈ hsNeumannDomain _ := ⟨poissonCenter _ F, hφ⟩
    exact ⟨hd, (hsNeumannOperator_eq_iff χ hc ⟨φ, hd⟩ _).mpr hφ⟩

/-- **Scalar Poisson equation** (Lemma A.2, Gibbs law).
The conclusion includes uniqueness after centering, every solution, and
exactly all minimizers over the whole `H¹` space. -/
theorem scalar_poisson_gibbs (hPL : External.PrekopaLeindler) (hN : 2 ≤ (N : ℕ))
    (F : Lp ℝ 2 (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))) :
    let μ : Measure (HsConfiguration N) := hsQuotientGibbsProbability χ hc
    ∃ φ : HsSobolev μ,
      (∫ x, hsSobolevValue μ φ x ∂μ) = 0 ∧ HsPoissonSolves χ hc F φ ∧
      (∀ ψ : HsSobolev μ, (∫ x, hsSobolevValue μ ψ x ∂μ) = 0 →
        HsPoissonSolves χ hc F ψ → ψ = φ) ∧
      (∀ ψ : HsSobolev μ, HsPoissonSolves χ hc F ψ ↔
        ∃ a : ℝ, ψ = φ + a • hsPoissonUnit μ) ∧
      (∀ ψ : HsSobolev μ, (∀ h : HsSobolev μ,
          hsPoissonEnergy μ F ψ ≤ hsPoissonEnergy μ F h) ↔ HsPoissonSolves χ hc F ψ) := by
  let μ : Measure (HsConfiguration N) := hsQuotientGibbsProbability χ hc
  have hp (v : HsSobolev μ) :
      ‖hsSobolevValue μ v‖ ^ 2 - (poissonMean μ (hsSobolevValue μ v)) ^ 2 ≤
        hsPoincareConstant N c * ‖hsSobolevGradient μ v‖ ^ 2 := by
    have h := scalar_poincare_gibbs hPL hN χ hc v
    dsimp only at h
    rw [Internal.hsPoincare_variance_eq] at h
    have hg : (∫ x, ‖hsSobolevGradient μ v x‖ ^ 2 ∂μ) = ‖hsSobolevGradient μ v‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      simp only [real_inner_self_eq_norm_sq]
    change ‖hsSobolevValue μ v‖ ^ 2 -
      (inner ℝ (Lp.const 2 μ (1 : ℝ)) (hsSobolevValue μ v)) ^ 2 ≤
      hsPoincareConstant N c * ∫ x, ‖hsSobolevGradient μ v x‖ ^ 2 ∂μ at h
    rw [hg] at h
    exact h
  obtain ⟨φ, hm, hφ, hu, ha, hmin⟩ := Internal.probability_poisson μ
    (hsSobolevValue μ) (hsSobolevGradient μ) (hsPoissonUnit μ)
    (hsPoissonUnit_value μ) (hsPoissonUnit_gradient μ) (hsSobolev_norm_sq μ)
    (hsPoincareConstant N c) (hsPoincareConstant_pos N c).le hp F
  refine ⟨φ, ?_, (hsPoissonSolves_iff χ hc F φ).mpr hφ, ?_, ?_, ?_⟩
  · exact (poissonMean_eq_integral μ _).symm.trans hm
  · intro ψ hψ hsol
    exact hu ψ ((poissonMean_eq_integral μ _).trans hψ)
      ((hsPoissonSolves_iff χ hc F ψ).mp hsol)
  · intro ψ
    exact (hsPoissonSolves_iff χ hc F ψ).trans (ha ψ)
  · intro ψ
    simpa only [hsPoissonEnergy_eq, hsPoissonSolves_iff] using hmin ψ

/-- The unique mean-zero solution, as an existence-and-uniqueness statement. -/
theorem scalar_poisson_gibbs_existsUnique (hPL : External.PrekopaLeindler)
    (hN : 2 ≤ (N : ℕ))
    (F : Lp ℝ 2 (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))) :
    let μ : Measure (HsConfiguration N) := hsQuotientGibbsProbability χ hc
    ∃! φ : HsSobolev μ,
      (∫ x, hsSobolevValue μ φ x ∂μ) = 0 ∧ HsPoissonSolves χ hc F φ := by
  obtain ⟨φ, hm, hs, hu, _⟩ := scalar_poisson_gibbs χ hc hPL hN F
  exact ⟨φ, ⟨hm, hs⟩, fun ψ hψ => hu ψ hψ.1 hψ.2⟩

end Riesz1

end
