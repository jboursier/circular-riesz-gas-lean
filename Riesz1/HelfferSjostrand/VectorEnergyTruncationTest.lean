/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.VectorEnergyAnchoredSobolev
public import Riesz1.ToMathlib.Calculus.SmoothPosPart

/-!
# Truncation of anchored test tuples

For `ε > 0` the smooth approximation `smoothPosPart ε` of the positive part sends every anchored
test tuple `u` to the test tuple `truncTest ε u = (smoothPosPart ε ∘ u_i)_i`. This file records the
pointwise facts that the truncated jets satisfy: the chain rule for the gradient, the energy
identity, and the bound `‖J(truncTest u)(y)‖ ≤ ‖J(u)(y)‖` of the pointwise jet norm.

These are the test-level inputs of the truncation step in the proof of Lemma 3.4.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ContDiff InnerProductSpace

namespace Riesz1

variable {n : ℕ} {c : ℝ}

/-- The smooth truncation `smoothPosPart ε ∘ f` of an anchored test function is again an anchored
test function, because `smoothPosPart ε` vanishes at zero. -/
def smoothPosPartTest {ε : ℝ} (hε : 0 < ε) (f : anchoredTestSubmodule n) :
    anchoredTestSubmodule n :=
  ⟨fun y => smoothPosPart ε ((f : AnchoredEuclidean n → ℝ) y),
    (contDiff_smoothPosPart ε hε).comp f.2.1,
    (f.2.2.1.comp_left (smoothPosPart_zero hε)),
    (tsupport_comp_subset (smoothPosPart_zero hε) (f : AnchoredEuclidean n → ℝ)).trans f.2.2.2⟩

/-- The truncated tuple `(smoothPosPart ε ∘ u_i)_i` of an anchored test tuple. -/
def truncTest {ε : ℝ} (hε : 0 < ε) (u : AnchoredVectorTest n) : AnchoredVectorTest n :=
  fun i => smoothPosPartTest hε (u i)

theorem smoothPosPartTest_apply {ε : ℝ} (hε : 0 < ε) (f : anchoredTestSubmodule n)
    (y : AnchoredEuclidean n) :
    (smoothPosPartTest hε f : AnchoredEuclidean n → ℝ) y =
      smoothPosPart ε ((f : AnchoredEuclidean n → ℝ) y) :=
  rfl

/-- The derivative of the approximation is bounded by one. -/
theorem abs_deriv_smoothPosPart_le' {ε : ℝ} (hε : 0 < ε) (r : ℝ) :
    |deriv (smoothPosPart ε) r| ≤ 1 := by
  rw [(hasDerivAt_smoothPosPart hε r).deriv]
  exact abs_deriv_smoothPosPart_le hε r

/-- The chain rule for the gradient of a scalar function composed with a differentiable map. -/
theorem gradient_comp_of_hasDerivAt {g : ℝ → ℝ} {g' : ℝ} {f : AnchoredEuclidean n → ℝ}
    {y : AnchoredEuclidean n} (hg : HasDerivAt g g' (f y)) (hf : DifferentiableAt ℝ f y) :
    gradient (fun z => g (f z)) y = g' • gradient f y := by
  have hfd : HasFDerivAt f (fderiv ℝ f y) y := hf.hasFDerivAt
  have hc : HasFDerivAt (fun z => g (f z)) (g' • fderiv ℝ f y) y := hg.comp_hasFDerivAt y hfd
  unfold gradient
  rw [hc.fderiv, map_smul]

/-- The gradient of a truncated test function is the chain rule expression. -/
theorem gradient_smoothPosPartTest {ε : ℝ} (hε : 0 < ε) (f : anchoredTestSubmodule n)
    (y : AnchoredEuclidean n) :
    gradient (smoothPosPartTest hε f : AnchoredEuclidean n → ℝ) y =
      deriv (smoothPosPart ε) ((f : AnchoredEuclidean n → ℝ) y) •
        gradient (f : AnchoredEuclidean n → ℝ) y := by
  have hdiff : DifferentiableAt ℝ (f : AnchoredEuclidean n → ℝ) y :=
    (ContDiff.differentiable f.2.1 (by simp)).differentiableAt
  have hg : HasDerivAt (smoothPosPart ε) (deriv (smoothPosPart ε) ((f : AnchoredEuclidean n → ℝ) y))
      ((f : AnchoredEuclidean n → ℝ) y) :=
    ((contDiff_smoothPosPart ε hε).differentiable (by simp) _).hasDerivAt
  exact gradient_comp_of_hasDerivAt hg hdiff

/-- The `k`-th anchored particle value of the truncated tuple is the truncated particle value. -/
theorem anchorLift_smoothPosPart {ε : ℝ} (hε : 0 < ε) (u : AnchoredVectorTest n)
    (y : AnchoredEuclidean n) (k : Fin (n.succPNat : ℕ)) :
    anchorLift n (anchoredTestVector (truncTest hε u) y) k =
      smoothPosPart ε (anchorLift n (anchoredTestVector u y) k) := by
  induction k using Fin.cases with
  | zero =>
    rw [anchorLift_apply, anchorLift_apply]
    simp [anchorVector, smoothPosPart_zero hε]
  | succ j =>
    rw [anchorLift_apply, anchorLift_apply]
    simp [anchorVector, anchoredTestVector, truncTest, smoothPosPartTest_apply]

/-- The pointwise energy of the truncated tuple is bounded by the pointwise energy of the tuple, in
each pair coordinate. -/
theorem abs_anchoredEnergyFun_truncTest_le {ε : ℝ} (hε : 0 < ε) (χ : HsPairPotentials n.succPNat c)
    (u : AnchoredVectorTest n) (y : AnchoredEuclidean n) (p : HsPairIndex n.succPNat) :
    |anchoredEnergyFun χ (truncTest hε u) y p| ≤ |anchoredEnergyFun χ u y p| := by
  unfold anchoredEnergyFun anchoredHessianEnergy hsHessianEnergy
  simp only [abs_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  rw [anchorLift_smoothPosPart hε u y p.1.2, anchorLift_smoothPosPart hε u y p.1.1]
  have h := abs_smoothPosPart_sub_le hε (anchorLift n (anchoredTestVector u y) p.1.2)
    (anchorLift n (anchoredTestVector u y) p.1.1)
  exact h

end Riesz1
