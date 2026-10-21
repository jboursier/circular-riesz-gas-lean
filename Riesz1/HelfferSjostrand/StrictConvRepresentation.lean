/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.StrictConvWeak
public import Riesz1.HelfferSjostrand.PoissonEquationAnchored
public import Riesz1.HelfferSjostrand.AnchoredInverse
public import Riesz1.ToMathlib.CenteredCovariance

/-!
# Anchored existence and representation

Remark 3.2, in full.

* The vector clause: for every `v ∈ L²(μ*; ℝ^{N-1})` the anchored inverse `T* v` is the unique
  weak solution of `A₁ u = v` in `𝒱_{μ*}`, and the minimizers of `q(u,u) - 2∫v·u` are exactly
  these weak solutions. Admissibility is not needed here.
* The representation: for `F, G ∈ H¹(μ*)`, the scalar mean-zero solution `φ` of the anchored
  Poisson equation satisfies `∇φ = T*∇F`, and `Cov_{μ*}(F, G) = ∫ ∇G · T*∇F dμ*`.

The Prékopa–Leindler inequality `External.PrekopaLeindler` enters as an explicit hypothesis,
as does the admissibility of the Hamiltonian in the representation.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology InnerProductSpace

namespace Riesz1

variable {n : ℕ} {c : ℝ}

/-- Remark 3.2, vector clause: for every `v`,
the anchored inverse `T* v` is the unique weak solution in `𝒱_{μ*}`, and a vector minimizes
`q(u,u) - 2∫v·u` exactly when it is this weak solution. -/
theorem anchoredVector_existence_minimization (χ : HsPairPotentials n.succPNat c) (hc : 0 < c) :
    letI := isProbabilityMeasure_anchoredMeasureE χ hc
    ∀ v : Lp (AnchoredEuclidean n) 2 (anchoredMeasureE χ),
      (∀ w : AnchoredVectorSobolev χ (anchoredMeasureE χ),
        anchoredVectorSobolevForm (anchoredMeasureE χ) (anchoredInverse χ hc v).val w.val =
          inner ℝ v (anchoredVectorValues (anchoredMeasureE χ) χ w)) ∧
      (∀ u : AnchoredVectorSobolev χ (anchoredMeasureE χ),
        (∀ w : AnchoredVectorSobolev χ (anchoredMeasureE χ),
          anchoredVectorSobolevForm (anchoredMeasureE χ) u.val w.val =
            inner ℝ v (anchoredVectorValues (anchoredMeasureE χ) χ w)) →
          u = anchoredInverse χ hc v) ∧
      (∀ u : AnchoredVectorSobolev χ (anchoredMeasureE χ),
        (∀ w : AnchoredVectorSobolev χ (anchoredMeasureE χ),
          anchoredVectorSobolevForm (anchoredMeasureE χ) u.val u.val -
              2 * inner ℝ v (anchoredVectorValues (anchoredMeasureE χ) χ u) ≤
            anchoredVectorSobolevForm (anchoredMeasureE χ) w.val w.val -
              2 * inner ℝ v (anchoredVectorValues (anchoredMeasureE χ) χ w)) ↔
        (∀ w : AnchoredVectorSobolev χ (anchoredMeasureE χ),
          anchoredVectorSobolevForm (anchoredMeasureE χ) u.val w.val =
            inner ℝ v (anchoredVectorValues (anchoredMeasureE χ) χ w))) := by
  have := isProbabilityMeasure_anchoredMeasureE χ hc
  intro v
  have hsolve := anchoredInverse_solves χ hc v
  refine ⟨hsolve, fun u hu => ?_, fun u => ⟨fun hmin => ?_, fun hw => ?_⟩⟩
  · exact anchoredVectorInverse_unique (anchoredMeasureE χ) χ hc (ae_mem_anchoredSimplex χ) v u hu
  · have hu := (anchoredVectorInverse_minimizer_iff (anchoredMeasureE χ) χ hc
      (ae_mem_anchoredSimplex χ) v u).mp hmin
    rw [hu]
    exact hsolve
  · have hu := anchoredVectorInverse_unique (anchoredMeasureE χ) χ hc
      (ae_mem_anchoredSimplex χ) v u hw
    rw [hu]
    exact (anchoredVectorInverse_minimizer_iff (anchoredMeasureE χ) χ hc
      (ae_mem_anchoredSimplex χ) v _).mpr rfl

/-- The Poisson right-hand side of an anchored `L²` class, pointwise almost everywhere. -/
theorem anchored_poissonCenter_ae (χ : HsPairPotentials n.succPNat c)
    [IsProbabilityMeasure (anchoredMeasureE χ)] (F : Lp ℝ 2 (anchoredMeasureE χ)) :
    ∀ᵐ y ∂(anchoredMeasureE χ),
      poissonCenter (anchoredMeasureE χ) F y = F y - ∫ x, F x ∂(anchoredMeasureE χ) := by
  have h1 := Lp.coeFn_sub F (poissonMean (anchoredMeasureE χ) F • Lp.const 2 (anchoredMeasureE χ) (1 : ℝ))
  have h2 := Lp.coeFn_smul (poissonMean (anchoredMeasureE χ) F)
    (Lp.const 2 (anchoredMeasureE χ) (1 : ℝ))
  have h3 := Lp.coeFn_const 2 (anchoredMeasureE χ) (1 : ℝ)
  filter_upwards [h1, h2, h3] with y hy1 hy2 hy3
  change (F - poissonMean (anchoredMeasureE χ) F • Lp.const 2 (anchoredMeasureE χ) (1 : ℝ)) y = _
  rw [hy1, Pi.sub_apply, hy2, Pi.smul_apply, smul_eq_mul, hy3, poissonMean_eq_integral,
    Function.const_apply, mul_one]

/-- Remark 3.2, representation. For `F, G ∈ H¹(μ*)`:

* the scalar Poisson problem has a mean-zero solution.
* every solution `φ` has gradient `T*∇F`.
* the covariance is `∫ ∇G · T*∇F dμ*`. -/
theorem anchoredRepresentation (χ : HsPairPotentials n.succPNat c) (hc : 0 < c)
    (hPL : External.PrekopaLeindler) (hn : 0 < n) {C_N : ℝ} (hadm : HsAdmissible χ C_N)
    (F G : AnchoredSobolev χ) :
    letI := isProbabilityMeasure_anchoredMeasureE χ hc
    (∃ φ : AnchoredSobolev χ, (∫ y, φ.val.1 y ∂anchoredMeasureE χ) = 0 ∧
        AnchoredPoissonSolves χ hc F.val.1 φ) ∧
      (∀ φ : AnchoredSobolev χ, AnchoredPoissonSolves χ hc F.val.1 φ →
        φ.val.2 = anchoredInverseValues (anchoredMeasureE χ) (anchoredInverse χ hc F.val.2).val) ∧
      (∫ y, (F.val.1 y - ∫ x, F.val.1 x ∂anchoredMeasureE χ) *
          (G.val.1 y - ∫ x, G.val.1 x ∂anchoredMeasureE χ) ∂anchoredMeasureE χ =
        ∫ y, inner ℝ (G.val.2 y)
          (anchoredInverseValues (anchoredMeasureE χ) (anchoredInverse χ hc F.val.2).val y)
            ∂anchoredMeasureE χ) := by
  have := isProbabilityMeasure_anchoredMeasureE χ hc
  obtain ⟨φ₀, hm₀, hs₀, -⟩ := scalar_poisson_anchoredLaw χ hc hPL hn F.val.1
  refine ⟨⟨φ₀, hm₀, hs₀⟩, fun φ hφ => anchoredPoisson_gradient_eq_inverse χ hc hadm F hφ, ?_⟩
  -- the covariance identity, through the weak equation of `φ₀` tested with `G`
  have hw := anchoredPoisson_gradient_eq_inverse χ hc hadm F hs₀
  have hweak := (anchoredPoissonSolves_iff χ hc F.val.1 φ₀).mp hs₀
    ((poissonAnchoredEquiv χ hc).symm G)
  have hG1 : poissonAnchoredGradient χ hc ((poissonAnchoredEquiv χ hc).symm G) = G.val.2 :=
    congrArg (fun x => x.val.2) ((poissonAnchoredEquiv χ hc).apply_symm_apply G)
  have hG0 : poissonAnchoredValue χ hc ((poissonAnchoredEquiv χ hc).symm G) = G.val.1 :=
    congrArg (fun x => x.val.1) ((poissonAnchoredEquiv χ hc).apply_symm_apply G)
  rw [hG1, hG0, hw] at hweak
  have hF1 : Integrable (fun y => F.val.1 y) (anchoredMeasureE χ) :=
    (Lp.memLp F.val.1).integrable one_le_two
  have hG1i : Integrable (fun y => G.val.1 y) (anchoredMeasureE χ) :=
    (Lp.memLp G.val.1).integrable one_le_two
  have hFG : Integrable (fun y => F.val.1 y * G.val.1 y) (anchoredMeasureE χ) :=
    (Lp.memLp F.val.1).integrable_mul (Lp.memLp G.val.1)
  have hcov : ∫ y, (F.val.1 y - ∫ x, F.val.1 x ∂anchoredMeasureE χ) *
      (G.val.1 y - ∫ x, G.val.1 x ∂anchoredMeasureE χ) ∂anchoredMeasureE χ =
      inner ℝ (poissonCenter (anchoredMeasureE χ) F.val.1) G.val.1 := by
    rw [poisson_inner_eq_integral, integral_centered_mul hF1 hG1i hFG]
    apply integral_congr_ae
    filter_upwards [anchored_poissonCenter_ae χ F.val.1] with y hy
    rw [hy]
  rw [hcov, ← hweak, L2.inner_def]
  apply integral_congr_ae
  filter_upwards with y
  exact real_inner_comm _ _

end Riesz1

end
