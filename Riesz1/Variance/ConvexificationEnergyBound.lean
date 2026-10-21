/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.ConvexificationEnergyLaw
public import Riesz1.Variance.ConvexificationInverse
public import Riesz1.ToMathlib.HessianLinearComposition

/-!
# Inverse energy for the actual nearest-neighbour tilt

Claim 4 of Lemma 5.2, using the actual inverse
and the exact tilted pair law identified in `ConvexificationEnergyLaw`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped Topology

namespace Riesz1

/-- Inner products in the Euclidean carrier are the coordinate pairing. -/
theorem anchored_inner_eq_dotProd {n : ℕ} (v b : AnchoredEuclidean n) :
    inner ℝ v b = dotProd (WithLp.ofLp v) (WithLp.ofLp b) := by
  simp only [PiLp.inner_apply, Real.inner_apply, dotProd]

/-- The Hessian supremum is unchanged by the Euclidean realization. -/
theorem anchoredHessianInverseEnergy_eq_pi {n : ℕ} {c : ℝ}
    (χ : HsPairPotentials n.succPNat c) {y : AnchoredEuclidean n}
    (hy : y ∈ anchoredSimplex n) (v : AnchoredEuclidean n) :
    anchoredHessianInverseEnergy χ y v =
      anchoredInverseSup (hsAnchoredHamiltonian χ) (WithLp.ofLp y) (WithLp.ofLp v) := by
  let L := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)
  have hf : ContDiffAt ℝ 2 (hsAnchoredHamiltonian χ) (WithLp.ofLp y) := by
    have h := ((contDiffOn_hsAnchoredHamiltonianE χ).contDiffAt
      ((isOpen_anchoredSimplex n).mem_nhds hy)).comp (WithLp.ofLp y) L.symm.contDiff.contDiffAt
    exact h.of_le (by simp)
  have hess (b : AnchoredEuclidean n) :
      fderiv ℝ (fderiv ℝ (hsAnchoredHamiltonianE χ)) y b b =
        fderiv ℝ (fderiv ℝ (hsAnchoredHamiltonian χ)) (WithLp.ofLp y)
          (WithLp.ofLp b) (WithLp.ofLp b) :=
    hessian_comp_continuousLinearMap (hsAnchoredHamiltonian χ) L.toContinuousLinearMap y b b hf
  unfold anchoredHessianInverseEnergy anchoredInverseSup
  congr 1
  ext z
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨WithLp.ofLp b, by dsimp only; rw [hess, anchored_inner_eq_dotProd]⟩
  · rintro ⟨b, rfl⟩
    exact ⟨WithLp.toLp 2 b, by dsimp only; rw [hess, anchored_inner_eq_dotProd]⟩

/-- **Lemma 5.2, claim 4.** The inverse is the
one of the actual tilted law, by `nearestTiltedPairs_anchoredMeasureE`.
The coefficient depends only on the fixed inverse temperature and exponent.
The coefficient fields have square-integrable coordinates, as in the paper.
-/
theorem nearestAnchored_inverse_energy (P : Parameters) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (hn : 1 ≤ n) (θ : ℝ → ℝ) (hθ : IsForcingCutoff θ),
      ∀ (K γ ε : ℝ) (hK : 1 ≤ K), 0 ≤ ε →
      let χ := nearestTiltedPairs P n.succPNat hθ K γ ε (by linarith)
      let μ := anchoredMeasureE χ
      ∀ (v : Lp (AnchoredEuclidean n) 2 μ)
        (a : AnchoredEuclidean n → Fin (n.succPNat : ℕ) → ℝ),
        (∀ e, MemLp (fun y => a y e) 2 μ) →
        (∀ᵐ y ∂μ, ∀ U : Fin n → ℝ, dotProd (WithLp.ofLp (v y)) U =
          ∑ e ∈ nearestPairs n.succPNat (window n.succPNat K γ),
            a y e * (((n : ℝ) + 1) * edgeForm n e U)) →
        anchoredInverseEnergy χ
          (hsRieszPairPotentials_curvature_pos n.succPNat P.2.1 (parametersExponent P)) v ≤
          C * K ^ (((parametersExponent P).val + 2) * ε) *
            ∫ y, (∑ e ∈ nearestPairs n.succPNat (window n.succPNat K γ), a y e ^ 2) ∂μ := by
  obtain ⟨c, hc, hH⟩ := anchoredPotential_hessian_lower P.val.1 P.2.1 (parametersExponent P)
  refine ⟨1 / c, one_div_pos.mpr hc, fun n hn θ hθ K γ ε hK hε v a ha hrep => ?_⟩
  let χ := nearestTiltedPairs P n.succPNat hθ K γ ε (by linarith : 0 < K)
  let μ := anchoredMeasureE χ
  have hχ := hsRieszPairPotentials_curvature_pos n.succPNat P.2.1 (parametersExponent P)
  have hQ := integrable_anchoredHessianInverseEnergy μ χ hχ (ae_mem_anchoredSimplex χ) v
  have haI : Integrable (fun y => ∑ e ∈ nearestPairs n.succPNat (window n.succPNat K γ),
      a y e ^ 2) μ := integrable_finsetSum _ fun e _ => (ha e).integrable_sq
  calc anchoredInverseEnergy χ hχ v
      ≤ ∫ y, anchoredHessianInverseEnergy χ y (v y) ∂μ := anchoredInverseEnergy_le_hessian χ hχ v
    _ ≤ ∫ y, (1 / c * K ^ (((parametersExponent P).val + 2) * ε)) *
        (∑ e ∈ nearestPairs n.succPNat (window n.succPNat K γ), a y e ^ 2) ∂μ := by
      apply integral_mono_ae hQ (haI.const_mul _)
      filter_upwards [ae_mem_anchoredSimplex χ, hrep] with y hy hry
      rw [anchoredHessianInverseEnergy_eq_pi χ hy,
        show hsAnchoredHamiltonian χ = anchoredPotential P.val.1 P.2.1
          (parametersExponent P) θ n K γ ε from
          funext (nearestTiltedPairs_anchoredPotential P hn hθ K γ ε (by linarith))]
      exact anchoredInverseSup_le P.val.1 P.2.1 (parametersExponent P) hc hH θ hθ n hn K γ ε hK hε
        hy (WithLp.ofLp (v y)) (a y) hry
    _ = _ := integral_const_mul _ _

end Riesz1

end
