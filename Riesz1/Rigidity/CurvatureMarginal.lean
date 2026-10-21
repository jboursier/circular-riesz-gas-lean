/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Rigidity.CurvatureGaps
public import Riesz1.HelfferSjostrand.BlockConcentrationCyclic
public import Riesz1.HelfferSjostrand.RieszAdmissiblePairs

/-!
# The convex exterior contribution in internal gap coordinates

The analytic Gaussian factorization step: the
sum of the convexified internal potential and the exterior
potential has curvature `β a_s R^(-s-2)` in the internal gaps. This file
proves convexity of the residual without requiring a classical Hessian
for the exterior potential. It does not assert a push-forward density
identity for `constrainedLaw`.
-/

@[expose] public section

noncomputable section

open Set

namespace Riesz1

/-- Gaussian factorization of the explicit internal-plus-exterior
potential for an initial block. It takes the Prékopa–Leindler inequality
`External.PrekopaLeindler` as a hypothesis. The scale, block size and cutoff do not affect
`a_s`. -/
theorem convexOn_curvatureGapMarginalResidual (hPL : External.PrekopaLeindler)
    (P : Parameters) (N : ℕ+) (L : ℕ) (hL : (L.succPNat : ℕ) ≤ (N : ℕ))
    {θ : ℝ → ℝ} (hθ : IsForcingCutoff θ) {R : ℝ} (hR : 1 ≤ R) :
    let s := parametersExponent P
    let χ := hsRieszPairPotentials N P.val.1 P.2.1 s
    let e := blockInitialEquiv L.succPNat N hL
    ConvexOn ℝ (internalGapDomain N L) (fun v =>
      P.val.1 * internalConvexifiedEnergy N L.succPNat s θ R (internalGapSection N L v) +
        blockTilde χ e (internalGapSection N L v) -
        (P.val.1 * rigidityCurvatureConstant s.val * R ^ (-s.val - 2)) / 2 * ‖v‖ ^ 2) := by
  dsimp only
  let s := parametersExponent P
  let χ := hsRieszPairPotentials N P.val.1 P.2.1 s
  let e := blockInitialEquiv L.succPNat N hL
  have hext := convexOn_blockTilde hPL χ (hsRieszPairPotentials_curvature_pos N P.2.1 s)
    e (blockInitialEquiv_strictMono (M := L.succPNat) (N := N) hL) L.succPNat.pos
      (blockInitialEquiv_zero (M := L.succPNat) (N := N) hL)
  have he : ConvexOn ℝ (internalGapDomain N L)
      (fun v => blockTilde χ e (internalGapSection N L v)) := by
    refine ⟨convex_internalGapDomain N L, fun x hx y hy a b ha hb hab => ?_⟩
    have hx' : internalGapSection N L x ∈ retainedChamber (L.succPNat : ℕ) := by
      rwa [retainedChamber_eq_hsChamber]
    have hy' : internalGapSection N L y ∈ retainedChamber (L.succPNat : ℕ) := by
      rwa [retainedChamber_eq_hsChamber]
    simpa only [map_add, map_smul] using hext.2 hx' hy' ha hb hab
  have hi := (convexOn_internalGapEnergy_residual N L s hθ hR).smul P.2.1.le
  convert hi.add he using 1
  funext v
  dsimp [s, χ, e]
  ring

end Riesz1

end
