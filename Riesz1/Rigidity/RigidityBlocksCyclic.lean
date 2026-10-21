/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Rigidity.RigidityBlocksGeometry
public import Riesz1.Rigidity.RigidityBlocksLinear
public import Mathlib.Data.Nat.ModEq

/-!
# Full-system coordinates for differences of cyclic block averages

The full-system case of the block estimate in Theorem 1.
Both coordinate lists are injective individually, including the even full
block. Integer offsets from crossing the seam form only the constant part
of the affine observable.
-/

@[expose] public section

noncomputable section

open MeasureTheory Finset
open scoped NNReal

namespace Riesz1

/-- The number of retained labels lies between `k` and `N`. -/
theorem rigidityBlocks_span_bounds {N : ℕ+} {k : ℕ} (hk : 1 ≤ k)
    (hkN : 2 * k ≤ (N : ℕ)) :
    k ≤ cyclicRepSpan N k + 1 ∧ cyclicRepSpan N k + 1 ≤ (N : ℕ) := by
  unfold cyclicRepSpan
  split <;> omega

/-- Averages in the existing cyclic representative convention, now indexed
by a finite type in both the ordinary and even full-block cases. -/
theorem blockAverage_eq_fin_cyclic {N : ℕ+} (X : Configuration N)
    (i : ℤ) {k : ℕ} (hk : 1 ≤ k) :
    blockAverage X i k = ((cyclicRepSpan N k + 1 : ℕ) : ℝ)⁻¹ *
      ∑ r : Fin (cyclicRepSpan N k + 1),
        cyclicLift X (cyclicRepStart N k i + r.val) := by
  have hc : (Icc (cyclicRepStart N k i)
      (cyclicRepStart N k i + cyclicRepSpan N k)).card = cyclicRepSpan N k + 1 := by
    rw [Int.card_Icc]
    omega
  unfold blockAverage
  rw [cyclicRep_eq_Icc hk i, hc, ← Internal.sum_integer_block]

theorem cyclicRepStart_add (N : ℕ+) (k : ℕ) (i d : ℤ) :
    cyclicRepStart N k (i + d) = cyclicRepStart N k i + d := by
  unfold cyclicRepStart
  split <;> ring

/-- Reconstruct a cyclic lift from one full block and its uniquely
determined integer offset. -/
theorem cyclicLift_eq_full_block {N : ℕ+} (X : Configuration N) (i : ℤ) (j : ℕ) :
    cyclicLift X (i + j) =
      (liftedBlock i (show (N : ℕ) - 1 < (N : ℕ) by exact Nat.sub_lt N.pos (by norm_num)) X).val
        ⟨j % N, by have := Nat.mod_lt j N.pos; have := N.pos; change j % N < (N : ℕ) - 1 + 1; omega⟩ +
      (⌊cyclicLift X i⌋ : ℝ) + (j / N : ℕ) := by
  change cyclicLift X (i + j) =
    (cyclicLift X (i + (j % N : ℕ)) - (⌊cyclicLift X i⌋ : ℝ)) +
      (⌊cyclicLift X i⌋ : ℝ) + (j / N : ℕ)
  have he : (i + (j % N : ℕ)) + (N : ℕ) * (j / N : ℕ) = i + (j : ℤ) := by
    have h := Nat.mod_add_div j N
    have hcast : ((j % N : ℕ) : ℤ) + (N : ℕ) * (j / N : ℕ) = (j : ℤ) := by exact_mod_cast h
    omega
  rw [← he, Internal.curvature_cyclicLift_add_periods]
  norm_cast
  ring

/-- The linear part of the same observable in one full period of lifts. -/
def rigidityBlocksCyclicLinear (N : ℕ+) (k : ℕ) : HsEuclidean ((N : ℕ) - 1).succPNat →L[ℝ] ℝ :=
  ((N : ℝ) / (cyclicRepSpan N k + 1)) • Internal.coordinateDifference
    (fun r : Fin (cyclicRepSpan N k + 1) => (⟨r.val % N, by have := Nat.mod_lt r.val N.pos; have := N.pos; change _ < (N : ℕ) - 1 + 1; omega⟩ : Fin (((N : ℕ) - 1).succPNat : ℕ)))
    (fun r : Fin (cyclicRepSpan N k + 1) => (⟨(k + r.val) % N, by have := Nat.mod_lt (k + r.val) N.pos; have := N.pos; change _ < (N : ℕ) - 1 + 1; omega⟩ : Fin (((N : ℕ) - 1).succPNat : ℕ)))

theorem rigidityBlocksCyclicLinear_apply (N : ℕ+) (k : ℕ) (x : HsEuclidean ((N : ℕ) - 1).succPNat) :
    rigidityBlocksCyclicLinear N k x = ((N : ℝ) / (cyclicRepSpan N k + 1)) *
      ((∑ r : Fin (cyclicRepSpan N k + 1), x ⟨(k + r.val) % N, by have := Nat.mod_lt (k + r.val) N.pos; have := N.pos; change _ < (N : ℕ) - 1 + 1; omega⟩) -
        ∑ r : Fin (cyclicRepSpan N k + 1), x ⟨r.val % N, by have := Nat.mod_lt r.val N.pos; have := N.pos; change _ < (N : ℕ) - 1 + 1; omega⟩) := by
  unfold rigidityBlocksCyclicLinear
  rw [smul_apply, Internal.coordinateDifference_apply]
  rfl

/-- The constant seam correction in the affine full-period representation. -/
def rigidityBlocksCyclicOffset (N : ℕ+) (k : ℕ) : ℝ :=
  ((N : ℝ) / (cyclicRepSpan N k + 1)) *
    ((∑ r : Fin (cyclicRepSpan N k + 1), (((k + r.val) / N : ℕ) : ℝ)) -
      ∑ r : Fin (cyclicRepSpan N k + 1), ((r.val / N : ℕ) : ℝ)) - k

theorem centeredBlockDiff_eq_cyclic_linear {N : ℕ+} (X : Configuration N)
    (i : ℤ) {k : ℕ} (hk : 1 ≤ k) :
    centeredBlockDiff X i k =
      rigidityBlocksCyclicLinear N k
        (WithLp.toLp 2 (liftedBlock (cyclicRepStart N k i)
          (show (N : ℕ) - 1 < (N : ℕ) by exact Nat.sub_lt N.pos (by norm_num)) X).val) + rigidityBlocksCyclicOffset N k := by
  rw [centeredBlockDiff, blockAverage_eq_fin_cyclic X _ hk,
    blockAverage_eq_fin_cyclic X _ hk, cyclicRepStart_add]
  have he (r : Fin (cyclicRepSpan N k + 1)) :
      cyclicRepStart N k i + (k : ℤ) + r.val = cyclicRepStart N k i + (k + r.val : ℕ) := by omega
  simp_rw [he, cyclicLift_eq_full_block X (cyclicRepStart N k i)]
  rw [rigidityBlocksCyclicLinear_apply, rigidityBlocksCyclicOffset]
  simp only [sum_add_distrib, sum_const, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  ring

theorem rigidityBlocksCyclicLinear_translate (N : ℕ+) (k : ℕ)
    (x : HsEuclidean ((N : ℕ) - 1).succPNat) (t : ℝ) :
    rigidityBlocksCyclicLinear N k (hsTranslate (N := ((N : ℕ) - 1).succPNat) t x) = rigidityBlocksCyclicLinear N k x := by
  simp only [rigidityBlocksCyclicLinear_apply, hsTranslate_apply, sum_add_distrib,
    sum_const, nsmul_eq_mul]
  ring

theorem norm_rigidityBlocksCyclicLinear_le (N : ℕ+) {k : ℕ} (hk : 1 ≤ k)
    (hkN : 2 * k ≤ (N : ℕ)) :
    ‖rigidityBlocksCyclicLinear N k‖ ≤
      2 * (N : ℝ) * Real.sqrt (cyclicRepSpan N k + 1) / (cyclicRepSpan N k + 1) := by
  have hm := (rigidityBlocks_span_bounds hk hkN).2
  have hf : Function.Injective (fun r : Fin (cyclicRepSpan N k + 1) =>
      (⟨r.val % N, by have := Nat.mod_lt r.val N.pos; have := N.pos; change _ < (N : ℕ) - 1 + 1; omega⟩ : Fin (((N : ℕ) - 1).succPNat : ℕ))) := by
    intro r s h
    apply Fin.ext
    have he := congrArg Fin.val h
    dsimp at he
    rwa [Nat.mod_eq_of_lt (r.isLt.trans_le hm), Nat.mod_eq_of_lt (s.isLt.trans_le hm)] at he
  have hg : Function.Injective (fun r : Fin (cyclicRepSpan N k + 1) =>
      (⟨(k + r.val) % N, by have := Nat.mod_lt (k + r.val) N.pos; have := N.pos; change _ < (N : ℕ) - 1 + 1; omega⟩ : Fin (((N : ℕ) - 1).succPNat : ℕ))) := by
    intro r s h
    apply Fin.ext
    have he : Nat.ModEq (N : ℕ) (k + r.val) (k + s.val) := congrArg Fin.val h
    have he' := Nat.ModEq.add_left_cancel' k he
    change r.val % N = s.val % N at he'
    rwa [Nat.mod_eq_of_lt (r.isLt.trans_le hm), Nat.mod_eq_of_lt (s.isLt.trans_le hm)] at he'
  let D := Internal.coordinateDifference
    (fun r : Fin (cyclicRepSpan N k + 1) => (⟨r.val % N, by have := Nat.mod_lt r.val N.pos; have := N.pos; change _ < (N : ℕ) - 1 + 1; omega⟩ : Fin (((N : ℕ) - 1).succPNat : ℕ)))
    (fun r : Fin (cyclicRepSpan N k + 1) => (⟨(k + r.val) % N, by have := Nat.mod_lt (k + r.val) N.pos; have := N.pos; change _ < (N : ℕ) - 1 + 1; omega⟩ : Fin (((N : ℕ) - 1).succPNat : ℕ)))
  have hD : ‖D‖ ≤ 2 * Real.sqrt (cyclicRepSpan N k + 1) := by
    simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_one] using
      Internal.norm_coordinateDifference_le _ _ hf hg
  change ‖((N : ℝ) / (cyclicRepSpan N k + 1)) • D‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc (N : ℝ) / (cyclicRepSpan N k + 1) * ‖D‖ ≤
        (N : ℝ) / (cyclicRepSpan N k + 1) * (2 * Real.sqrt (cyclicRepSpan N k + 1)) :=
      mul_le_mul_of_nonneg_left hD (by positivity)
    _ = _ := by ring

/-- With radius `N`, the forcing on any block of at most `N-1` gaps is
identically zero. Hence the constrained probability is the original law. -/
theorem constrainedLaw_radius_N (P : Parameters) (N : ℕ+)
    {θ : ℝ → ℝ} (hθ : IsForcingCutoff θ) (i : ℤ) {L : ℕ}
    (hL : L < (N : ℕ)) :
    constrainedLaw P N θ i L (N : ℝ) = gibbsMeasure P N := by
  let := isProbabilityMeasure_gibbsMeasure P N
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hz (X : Configuration N) : forcingPotential θ i L (N : ℝ) X = 0 := by
    apply forcingPotential_eq_zero hθ hN
    have hmono := (cyclicLift_strictMono X).monotone
      (show i + (L : ℤ) ≤ i + (N : ℕ) by omega)
    have hmul := mul_le_mul_of_nonneg_left hmono hN.le
    rw [cyclicLift_add_N] at hmul
    unfold blockLength
    nlinarith
  rw [constrainedLaw_eq_tilted]
  simp only [hz, mul_zero]
  exact tilted_const _ 0

/-- The full-system optimized tail. This includes the even full block and
all cyclic seams, and needs no additional admissibility hypothesis. -/
theorem rigidityBlocks_full_tail (hBE : External.BakryEmery)
    (hPL : External.PrekopaLeindler) (P : Parameters) (N : ℕ+)
    (hN : 2 ≤ (N : ℕ)) (i : ℤ) {k : ℕ} (hk : 1 ≤ k)
    (hkN : 2 * k ≤ (N : ℕ)) {v : ℝ} (hv : 0 < v) :
    (gibbsMeasure P N).real {X | v ≤ |centeredBlockDiff X i k|} ≤
      2 * Real.exp (-(P.val.1 * rigidityCurvatureConstant (parametersExponent P).val *
          (N : ℝ) * (cyclicRepSpan N k + 1) * v ^ 2) /
        (8 * (N : ℝ) ^ ((parametersExponent P).val + 2))) := by
  let L := (N : ℕ) - 1
  have hLN : L < (N : ℕ) := Nat.sub_lt N.pos (by norm_num)
  let F := fun x : HsEuclidean L.succPNat =>
    rigidityBlocksCyclicLinear N k x + rigidityBlocksCyclicOffset N k
  let B : ℝ≥0 := ⟨2 * (N : ℝ) * Real.sqrt (cyclicRepSpan N k + 1) /
    (cyclicRepSpan N k + 1), by positivity⟩
  have hF : Differentiable ℝ F := (rigidityBlocksCyclicLinear N k).differentiable.add_const _
  have hrot : ∀ x ∈ hsChamber L.succPNat, ∀ t : ℝ, F (hsTranslate t x) = F x := by
    intro x _ t
    dsimp only [F]
    rw [rigidityBlocksCyclicLinear_translate]
  have hB : ∀ x ∈ hsChamber L.succPNat, ‖fderiv ℝ F x‖ ≤ B := by
    intro x _
    rw [show fderiv ℝ F x = rigidityBlocksCyclicLinear N k from
      ((rigidityBlocksCyclicLinear N k).hasFDerivAt.add_const _).fderiv]
    exact norm_rigidityBlocksCyclicLinear_le N hk hkN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hNp : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ (N : ℕ) by omega)
  have hBp : 0 < B := by
    change 0 < 2 * (N : ℝ) * Real.sqrt (cyclicRepSpan N k + 1) / (cyclicRepSpan N k + 1)
    positivity
  have h := (curvature_centered_concentration hBE hPL P N
    (cyclicRepStart N k i) hLN isForcingCutoff_forcingCutoff hNp
    hF.differentiableOn hrot hB).2.2.1 hBp v hv
  have he (X : Configuration N) :
      F (WithLp.toLp 2 (liftedBlock (cyclicRepStart N k i) hLN X).val) =
        centeredBlockDiff X i k := (centeredBlockDiff_eq_cyclic_linear X i hk).symm
  have hBC : (B : ℝ) = 2 * (N : ℝ) * Real.sqrt (cyclicRepSpan N k + 1) /
      (cyclicRepSpan N k + 1) := rfl
  simp only [he, hBC, constrainedLaw_radius_N P N isForcingCutoff_forcingCutoff _ hLN,
    integral_centeredBlockDiff_gibbsMeasure P N hN i hk, sub_zero] at h
  have hdim : (L : ℝ) + 1 = (N : ℝ) := by
    have hnat : L + 1 = (N : ℕ) := by dsimp [L]; omega
    exact_mod_cast hnat
  rw [hdim] at h
  have hmpos : (0 : ℝ) < cyclicRepSpan N k + 1 := by positivity
  have hsquare : (2 * (N : ℝ) * Real.sqrt (cyclicRepSpan N k + 1) /
      (cyclicRepSpan N k + 1)) ^ 2 = 4 * (N : ℝ) ^ 2 / (cyclicRepSpan N k + 1) := by
    rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt hmpos.le]
    field_simp
    ring
  rw [hsquare] at h
  convert h using 1
  congr 1
  congr 1
  field_simp
  ring

end Riesz1

end
