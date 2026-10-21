/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Rigidity.BlockAverage
public import Riesz1.Rigidity.CurvatureTails
public import Riesz1.ToMathlib.CoordinateDifference

/-!
# The block difference as an affine block observable

The local range `3k < N` in the proof of Theorem 1.
The linear functional uses the same two averages as `centeredBlockDiff`.
Its gradient bound remains
valid when the two retained coordinate sets overlap.
-/

@[expose] public section

noncomputable section

open MeasureTheory Finset
open scoped NNReal

namespace Riesz1

/-- The linear part of the difference of two averages inside a block of
`3k+1` lifted coordinates. The constant part of `A` is `-k`. -/
def rigidityBlocksLinear (N : ℕ+) (k : ℕ) : HsEuclidean (3 * k).succPNat →L[ℝ] ℝ :=
  ((N : ℝ) / (2 * k + 1)) • Internal.coordinateDifference
    (fun r : Fin (2 * k + 1) => (⟨r.val, by change r.val < 3 * k + 1; omega⟩ : Fin ((3 * k).succPNat : ℕ)))
    (fun r : Fin (2 * k + 1) => (⟨k + r.val, by change k + r.val < 3 * k + 1; omega⟩ : Fin ((3 * k).succPNat : ℕ)))

theorem rigidityBlocksLinear_apply (N : ℕ+) (k : ℕ)
    (x : HsEuclidean (3 * k).succPNat) :
    rigidityBlocksLinear N k x = ((N : ℝ) / (2 * k + 1)) *
      ((∑ r : Fin (2 * k + 1), x ⟨k + r.val, by change k + r.val < 3 * k + 1; omega⟩) -
        ∑ r : Fin (2 * k + 1), x ⟨r.val, by change r.val < 3 * k + 1; omega⟩) := by
  unfold rigidityBlocksLinear
  rw [smul_apply, Internal.coordinateDifference_apply]
  rfl

/-- The representative of each average is exactly the chosen integer
interval, with no modulo or centering alteration. -/
theorem blockAverage_eq_fin_average {N : ℕ+} (X : Configuration N)
    (i : ℤ) {k : ℕ} (hkN : 2 * k < (N : ℕ)) :
    blockAverage X i k = ((2 * k + 1 : ℕ) : ℝ)⁻¹ *
      ∑ r : Fin (2 * k + 1), cyclicLift X (i - k + r.val) := by
  have hc : (Icc (i - k) (i + k)).card = 2 * k + 1 := by
    rw [Int.card_Icc]
    omega
  have he : i - (k : ℤ) + (2 * k : ℕ) = i + k := by omega
  unfold blockAverage cyclicRep
  rw [ite_eq_left hkN, hc, ← he, ← Internal.sum_integer_block]

/-- The affine observable in retained coordinates is exactly
`centeredBlockDiff` for every integer start, including negative starts. -/
theorem centeredBlockDiff_eq_linear {N : ℕ+} (X : Configuration N)
    (i : ℤ) {k : ℕ} (hkN : 3 * k < (N : ℕ)) :
    centeredBlockDiff X i k =
      rigidityBlocksLinear N k (WithLp.toLp 2 (liftedBlock (i - k) hkN X).val) - k := by
  have htwo : 2 * k < (N : ℕ) := by omega
  rw [centeredBlockDiff, blockAverage_eq_fin_average X _ htwo,
    blockAverage_eq_fin_average X _ htwo, rigidityBlocksLinear_apply]
  change (N : ℝ) *
      ((((2 * k + 1 : ℕ) : ℝ)⁻¹ * ∑ r : Fin (2 * k + 1),
        cyclicLift X (i + k - k + r.val)) -
      (((2 * k + 1 : ℕ) : ℝ)⁻¹ * ∑ r : Fin (2 * k + 1),
        cyclicLift X (i - k + r.val))) - k =
    ((N : ℝ) / (2 * (k : ℝ) + 1)) *
      ((∑ r : Fin (2 * k + 1),
          (cyclicLift X (i - k + (k + r.val : ℕ)) - (⌊cyclicLift X (i - k)⌋ : ℝ))) -
        ∑ r : Fin (2 * k + 1),
          (cyclicLift X (i - k + r.val) - (⌊cyclicLift X (i - k)⌋ : ℝ))) - k
  simp only [Nat.cast_add, sum_sub_distrib, sum_const, nsmul_eq_mul,
    Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, add_sub_cancel_right]
  ring_nf

/-- The derivative sum is zero because the two coordinate lists have
the same cardinality. -/
theorem rigidityBlocksLinear_translate (N : ℕ+) (k : ℕ)
    (x : HsEuclidean (3 * k).succPNat) (t : ℝ) :
    rigidityBlocksLinear N k (hsTranslate (N := (3 * k).succPNat) t x) = rigidityBlocksLinear N k x := by
  simp only [rigidityBlocksLinear_apply, hsTranslate_apply, sum_add_distrib,
    sum_const, nsmul_eq_mul]
  ring

/-- The operator norm is at most `2N/√(2k+1)`. Written without a
division by a square root, this is convenient for squaring the bound. -/
theorem norm_rigidityBlocksLinear_le (N : ℕ+) (k : ℕ) :
    ‖rigidityBlocksLinear N k‖ ≤
      2 * (N : ℝ) * Real.sqrt (2 * k + 1) / (2 * k + 1) := by
  have hf : Function.Injective
      (fun r : Fin (2 * k + 1) => (⟨r.val, by change r.val < 3 * k + 1; omega⟩ : Fin ((3 * k).succPNat : ℕ))) := by
    intro r s h
    exact Fin.ext (congrArg (fun z : Fin ((3 * k).succPNat : ℕ) => z.val) h)
  have hg : Function.Injective
      (fun r : Fin (2 * k + 1) => (⟨k + r.val, by change k + r.val < 3 * k + 1; omega⟩ : Fin ((3 * k).succPNat : ℕ))) := by
    intro r s h
    apply Fin.ext
    have := congrArg Fin.val h
    dsimp at this
    omega
  have hm : (0 : ℝ) < 2 * (k : ℝ) + 1 := by positivity
  let D := Internal.coordinateDifference
    (fun r : Fin (2 * k + 1) => (⟨r.val, by change r.val < 3 * k + 1; omega⟩ : Fin ((3 * k).succPNat : ℕ)))
    (fun r : Fin (2 * k + 1) => (⟨k + r.val, by change k + r.val < 3 * k + 1; omega⟩ : Fin ((3 * k).succPNat : ℕ)))
  have h : ‖D‖ ≤ 2 * Real.sqrt (2 * (k : ℝ) + 1) := by
    simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
      using Internal.norm_coordinateDifference_le _ _ hf hg
  change ‖((N : ℝ) / (2 * k + 1)) • D‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc (N : ℝ) / (2 * k + 1) * ‖D‖ ≤
        (N : ℝ) / (2 * k + 1) * (2 * Real.sqrt (2 * k + 1)) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by ring

/-- The square of the chosen bound is exactly `4N²/(2k+1)`, so in
particular it is at most `4N²/k` for positive `k`. -/
theorem rigidityBlocks_gradient_bound_sq (N : ℕ+) (k : ℕ) :
    (2 * (N : ℝ) * Real.sqrt (2 * k + 1) / (2 * k + 1)) ^ 2 =
      4 * (N : ℝ) ^ 2 / (2 * k + 1) := by
  have hm : (0 : ℝ) < 2 * (k : ℝ) + 1 := by positivity
  rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt hm.le]
  field_simp
  ring

/-- The optimized centered two-sided tail in the local case, before
substituting the radius and removing the bounded mean. -/
theorem rigidityBlocks_local_centered_tail (hBE : External.BakryEmery)
    (hPL : External.PrekopaLeindler) (P : Parameters) (N : ℕ+) (i : ℤ)
    {k : ℕ} (hkN : 3 * k < (N : ℕ))
    {θ : ℝ → ℝ} (hθ : IsForcingCutoff θ) {R : ℝ} (hR : 1 ≤ R)
    {v : ℝ} (hv : 0 < v) :
    let Q := constrainedLaw P N θ (i - k) (3 * k) R
    Q.real {X | v ≤ |centeredBlockDiff X i k - ∫ Y, centeredBlockDiff Y i k ∂Q|} ≤
      2 * Real.exp (-(P.val.1 * rigidityCurvatureConstant (parametersExponent P).val *
          (N : ℝ) ^ 2 * (3 * k + 1) * v ^ 2) /
        (2 * R ^ ((parametersExponent P).val + 2) *
          (2 * (N : ℝ) * Real.sqrt (2 * k + 1) / (2 * k + 1)) ^ 2)) := by
  let F := fun x : HsEuclidean (3 * k).succPNat => rigidityBlocksLinear N k x - k
  let B : ℝ≥0 := ⟨2 * (N : ℝ) * Real.sqrt (2 * k + 1) / (2 * k + 1), by positivity⟩
  have hF : Differentiable ℝ F := (rigidityBlocksLinear N k).differentiable.sub_const _
  have hrot : ∀ x ∈ hsChamber (3 * k).succPNat, ∀ t : ℝ, F (hsTranslate (N := (3 * k).succPNat) t x) = F x := by
    intro x _ t
    dsimp only [F]
    rw [rigidityBlocksLinear_translate]
  have hB : ∀ x ∈ hsChamber (3 * k).succPNat, ‖fderiv ℝ F x‖ ≤ B := by
    intro x _
    rw [show fderiv ℝ F x = rigidityBlocksLinear N k from
      ((rigidityBlocksLinear N k).hasFDerivAt.sub_const (k : ℝ)).fderiv]
    exact norm_rigidityBlocksLinear_le N k
  have hBp : 0 < B := by
    change 0 < 2 * (N : ℝ) * Real.sqrt (2 * k + 1) / (2 * k + 1)
    have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
    positivity
  have h := (curvature_centered_concentration hBE hPL P N (i - k) hkN hθ hR
    hF.differentiableOn hrot hB).2.2.1 hBp v hv
  have he (X : Configuration N) :
      F (WithLp.toLp 2 (liftedBlock (i - k) hkN X).val) = centeredBlockDiff X i k :=
    (centeredBlockDiff_eq_linear X i hkN).symm
  have hBC : (B : ℝ) = 2 * (N : ℝ) * Real.sqrt (2 * k + 1) / (2 * k + 1) := rfl
  simp only [he, hBC] at h
  convert h using 1
  push_cast
  rfl

end Riesz1

end
