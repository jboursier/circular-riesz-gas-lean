/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.ConvexityHessian
public import Riesz1.HelfferSjostrand.ConvexityHessianFrechet
public import Riesz1.ToMathlib.Calculus.FrechetSecondLine

/-!
# Regularized marginal Hessian, Fréchet form (Lemma 3.7)

This file states the Hessian identity of Lemma 3.7 in its Fréchet form. Let
`Q ⊆ ℝ^m × ℝ^n` be open and convex with locally bounded fibers, let `K` be convex and `C^∞` on
`Q`, and let `J(z) = ∫_{Q_z} e^{-K(z,y)} dy` with `J(z) > 0`. Then `-log J` is twice differentiable
at `z` in the Fréchet sense, and for every direction `b`,

`b · D²(-log J)(z) b = E_z[b · K_zz b] - Var_z(b · K_z)`
`≥ E_z[b · (K_zz - K_zy K_yy⁻¹ K_yz) b] ≥ 0`.

The second Fréchet derivative `fderiv ℝ (fderiv ℝ (-log J)) z b b` is identified with the second
derivative along the line `s ↦ z + s • b` (`Riesz1.fderiv_fderiv_apply_eq_deriv_deriv_line`), and
the line identity is `Riesz1.ConvexityHessian.convexity_exterior_hessian`. The twice
differentiability is `Riesz1.ConvexityHessian.twiceDifferentiableAt_neg_log_fiberIntegral`.

The hypothesis that `b · K_z` belongs to the conditional `H¹` space is required for every
direction `b`, as the paper states it ("the functions `b · K_z`").
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ContDiff InnerProductSpace

namespace Riesz1.ConvexityHessian

variable {m n : ℕ}

variable {Q : Set (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n))}
  {K : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n) → ℝ}

/-- **Regularized marginal Hessian** (Lemma 3.7), Fréchet form.
Under the hypotheses of Lemma 3.7, `-log J` is twice differentiable at `z` (differentiable on a
neighbourhood of `z`, with differentiable derivative at `z`), and for every direction `b`, the
second Fréchet derivative satisfies `b · D²(-log J)(z) b = E_z[b · K_zz b] - Var_z(b · K_z)`. The
Schur energy `E_z[b · (K_zz - K_zy K_yy⁻¹ K_yz) b]` (the infimum over `a` in `schurEnergy`) lies
between `0` and that difference. Here `E_z` and `Var_z` are taken under the fiber law
`J(z)⁻¹ e^{-K(z,y)} dy` on `Q_z`. -/
theorem convexity_exterior_hessian_frechet (hPL : External.PrekopaLeindler) (hn : 0 < n)
    (hQo : IsOpen Q) (hQc : Convex ℝ Q)
    (hloc : ∀ z ∈ Prod.fst '' Q, ∃ U ∈ 𝓝 z, Bornology.IsBounded (Q ∩ (U ×ˢ univ)))
    (hK : ContDiffOn ℝ ∞ K Q) (hKc : ConvexOn ℝ Q K)
    (hmaj : ∀ C : Set (EuclideanSpace ℝ (Fin m)), IsCompact C → C ⊆ Prod.fst '' Q →
      ∃ M₀ M₁ M₂ : EuclideanSpace ℝ (Fin n) → ℝ, Integrable M₀ ∧ Integrable M₁ ∧
        Integrable M₂ ∧
        ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), ∀ w ∈ C,
          |zeroExtension Q K (w, y)| ≤ M₀ y ∧
          ‖fderiv ℝ (fun w' => zeroExtension Q K (w', y)) w‖ ≤ M₁ y ∧
          ‖fderiv ℝ (fderiv ℝ (fun w' => zeroExtension Q K (w', y))) w‖ ≤ M₂ y)
    (hsmooth : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      ContDiff ℝ 2 (fun w => zeroExtension Q K (w, y)))
    {a : ℝ} (ha : 0 < a)
    (hyy : ∀ p ∈ Q, ∀ h : EuclideanSpace ℝ (Fin n),
      a * ‖h‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ K) p (0, h) (0, h))
    {z : EuclideanSpace ℝ (Fin m)} (hz : 0 < fiberIntegral Q K z)
    (hH1 : ∀ b : EuclideanSpace ℝ (Fin m), ∃ G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
      Riesz1.WeightedSobolev.IsWeightedH1 (fiberLaw Q K z) (fiber Q z)
        (fun y => fderiv ℝ K (z, y) (b, 0)) G) :
    (∀ᶠ x in 𝓝 z, DifferentiableAt ℝ (fun x => -Real.log (fiberIntegral Q K x)) x) ∧
      DifferentiableAt ℝ (fderiv ℝ (fun x => -Real.log (fiberIntegral Q K x))) z ∧
      ∀ b : EuclideanSpace ℝ (Fin m),
        fderiv ℝ (fderiv ℝ (fun x => -Real.log (fiberIntegral Q K x))) z b b =
            (∫ y, fderiv ℝ (fderiv ℝ K) (z, y) (b, 0) (b, 0) ∂(fiberLaw Q K z)) -
              ∫ y, (fderiv ℝ K (z, y) (b, 0) -
                ∫ y', fderiv ℝ K (z, y') (b, 0) ∂(fiberLaw Q K z)) ^ 2 ∂(fiberLaw Q K z) ∧
          ∫ y, schurEnergy K z b y ∂(fiberLaw Q K z) ≤
            (∫ y, fderiv ℝ (fderiv ℝ K) (z, y) (b, 0) (b, 0) ∂(fiberLaw Q K z)) -
              ∫ y, (fderiv ℝ K (z, y) (b, 0) -
                ∫ y', fderiv ℝ K (z, y') (b, 0) ∂(fiberLaw Q K z)) ^ 2 ∂(fiberLaw Q K z) ∧
          0 ≤ ∫ y, schurEnergy K z b y ∂(fiberLaw Q K z) := by
  obtain ⟨hev, hdiff⟩ := twiceDifferentiableAt_neg_log_fiberIntegral hQo hK hmaj hsmooth hz
  refine ⟨hev, hdiff, fun b => ?_⟩
  obtain ⟨hmain, hle, hnn⟩ :=
    convexity_exterior_hessian hPL hn hQo hQc hloc hK hKc hmaj hsmooth ha hyy b hz (hH1 b)
  have hline := Riesz1.fderiv_fderiv_apply_eq_deriv_deriv_line (b := b) hev hdiff
  exact ⟨hline.trans hmain, hle, hnn⟩

end Riesz1.ConvexityHessian

end

end
