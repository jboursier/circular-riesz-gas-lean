/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Rigidity.CurvatureLaw
public import Riesz1.HelfferSjostrand.BlockConcentrationCyclic

/-!
# The forced pair datum for an initial block

The cutoff is added exactly to pairs whose two labels are retained.
This is the pair datum of the internal energy `H_I` inside the full system, rather
than a new internal energy. It has the actual constrained Gibbs law.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Finset
open scoped ENNReal ContDiff

namespace Riesz1

namespace Internal

theorem curvature_sum_initial {A : Type*} [AddCommMonoid A] {m n : ℕ}
    (h : m ≤ n) (f : Fin n → A) :
    (∑ i : Fin n, if i.val < m then f i else 0) = ∑ i : Fin m, f (Fin.castLE h i) := by
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun i hi => (⟨i.val, (Finset.mem_filter.mp hi).2⟩ : Fin m))
  · intro i hi
    exact Finset.mem_univ _
  · intro i hi j hj hij
    exact Fin.ext (congrArg (fun x : Fin m => x.val) hij)
  · intro i _
    exact ⟨Fin.castLE h i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, i.isLt⟩, rfl⟩
  · intro i hi
    rfl

theorem curvature_sum_initial_pairs {m n : ℕ} (h : m ≤ n)
    (f : Fin n → Fin n → ℝ) :
    (∑ i : Fin n, ∑ j ∈ univ.filter (i < ·),
      if i.val < m ∧ j.val < m then f i j else 0) =
      ∑ i : Fin m, ∑ j ∈ univ.filter (i < ·), f (Fin.castLE h i) (Fin.castLE h j) := by
  have hi (i : Fin n) : (∑ j ∈ univ.filter (i < ·),
      if i.val < m ∧ j.val < m then f i j else 0) =
      if i.val < m then ∑ j : Fin n, if j.val < m then (if i < j then f i j else 0) else 0
      else 0 := by
    by_cases him : i.val < m
    · simp only [him, true_and, ite_true, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro j _
      split_ifs <;> rfl
    · simp [him]
  simp_rw [hi]
  rw [curvature_sum_initial h]
  congr 1
  funext i
  rw [curvature_sum_initial h]
  simp only [Finset.sum_filter]
  rfl

end Internal

/-- The added pair potential, including inverse temperature, on the initial block.
Pairs outside the block receive no forcing. -/
def curvatureInitialPenalty (P : Parameters) (N : ℕ+) (M : ℕ)
    (θ : ℝ → ℝ) (R : ℝ) (i j : Fin (N : ℕ)) (r : ℝ) : ℝ :=
  if i.val < M ∧ j.val < M then P.val.1 * θ ((N : ℝ) / R * r) else 0

theorem curvatureInitialPenalty_smooth (P : Parameters) (N : ℕ+) (M : ℕ)
    {θ : ℝ → ℝ} (hθ : IsForcingCutoff θ) (R : ℝ) (i j : Fin (N : ℕ)) :
    ContDiff ℝ ∞ (curvatureInitialPenalty P N M θ R i j) := by
  unfold curvatureInitialPenalty
  split_ifs
  · exact contDiff_const.mul (hθ.1.comp (contDiff_const.mul contDiff_id))
  · exact contDiff_const

theorem curvatureInitialPenalty_convex (P : Parameters) (N : ℕ+) (M : ℕ)
    {θ : ℝ → ℝ} (hθ : IsForcingCutoff θ) {R : ℝ} (hR : 0 < R)
    (i j : Fin (N : ℕ)) :
    ConvexOn ℝ (Ioo (0 : ℝ) 1) (curvatureInitialPenalty P N M θ R i j) := by
  unfold curvatureInitialPenalty
  split_ifs
  · apply ConvexOn.smul P.2.1.le
    apply convexOn_of_deriv2_nonneg' (convex_Ioo _ _)
      ((hθ.1.comp (contDiff_const.mul contDiff_id)).differentiable (by simp)).differentiableOn
      (((hθ.1.comp (contDiff_const.mul contDiff_id)).of_le
        (show (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω) by simp)).differentiable_deriv_two).differentiableOn
    intro r hr
    have hd : deriv (fun x => θ ((N : ℝ) / R * x)) =
        fun x => (N : ℝ) / R * deriv θ ((N : ℝ) / R * x) := by
      funext x
      simpa only [Function.comp_def, id_eq, mul_one, one_mul, mul_comm] using
        ((hθ.1.differentiable (by simp) _).hasDerivAt.comp x
          ((hasDerivAt_id x).const_mul ((N : ℝ) / R))).deriv
    change 0 ≤ deriv (deriv (fun x => θ ((N : ℝ) / R * x))) r
    rw [hd]
    have hh := (hθ.1.of_le (show (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω) by simp)).differentiable_deriv_two
    have hdd := (((hh _).hasDerivAt.comp r
      ((hasDerivAt_id r).const_mul ((N : ℝ) / R))).const_mul ((N : ℝ) / R)).deriv
    simp only [Function.comp_def, id_eq, mul_one] at hdd
    rw [hdd]
    have hn : 0 ≤ (N : ℝ) / R := div_nonneg (by positivity) hR.le
    exact mul_nonneg hn (mul_nonneg
      (hθ.2.2.2.1 _ (mul_nonneg hn hr.1.le)).1 hn)
  · exact convexOn_const _ (convex_Ioo _ _)

/-- Full-system Riesz pairs with the cutoff on exactly the retained pairs. -/
def curvatureInitialPairs (P : Parameters) (N : ℕ+) (M : ℕ)
    {θ : ℝ → ℝ} (hθ : IsForcingCutoff θ) {R : ℝ} (hR : 0 < R) :
    HsPairPotentials N
      (P.val.1 * (N : ℝ) ^ (-(parametersExponent P).val) *
        ((parametersExponent P).val * ((parametersExponent P).val + 1))) :=
  (hsRieszPairPotentials N P.val.1 P.2.1 (parametersExponent P)).addConvex
    (curvatureInitialPenalty P N M θ R)
    (fun i j _ => (curvatureInitialPenalty_smooth P N M hθ R i j).contDiffOn)
    (fun i j _ => curvatureInitialPenalty_convex P N M hθ hR i j)

/-- Each retained pair is precisely the convexified internal pair `curvaturePairPotential`. -/
theorem curvatureInitialPairs_retained (P : Parameters) (N : ℕ+) {M : ℕ}
    (hM : M ≤ (N : ℕ)) {θ : ℝ → ℝ} (hθ : IsForcingCutoff θ) {R : ℝ} (hR : 0 < R)
    (i j : Fin M) :
    (curvatureInitialPairs P N M hθ hR).potential (Fin.castLE hM i) (Fin.castLE hM j) =
      fun r => P.val.1 * curvaturePairPotential N (parametersExponent P) θ R r := by
  funext r
  simp only [curvatureInitialPairs, HsPairPotentials.addConvex, curvatureInitialPenalty]
  have hi : (min (Fin.castLE hM i) (Fin.castLE hM j)).val < M := by
    simp
  have hj : (max (Fin.castLE hM i) (Fin.castLE hM j)).val < M := by
    simp
  simp only [hi, hj, and_self, ite_true]
  change P.val.1 * (N : ℝ) ^ (-(parametersExponent P).val) * _ + _ = _
  unfold curvaturePairPotential
  ring

/-- The initial-block forced Hamiltonian uses the original forcing and energy. -/
theorem curvatureInitialPairs_hamiltonian (P : Parameters) (N : ℕ+) {L : ℕ}
    (hL : L < (N : ℕ)) {θ : ℝ → ℝ} (hθ : IsForcingCutoff θ) {R : ℝ} (hR : 0 < R)
    (X : Configuration N) :
    hsFundamentalHamiltonian (curvatureInitialPairs P N (L + 1) hθ hR) X =
      P.val.1 * (energy (parametersExponent P) X + forcingPotential θ 0 L R X) := by
  rw [hsFundamentalHamiltonian, curvatureInitialPairs, hsPairExpression_addConvex]
  change hsFundamentalHamiltonian _ X + _ = _
  rw [hsRieszFundamentalHamiltonian_eq]
  simp only [curvatureInitialPenalty]
  rw [Internal.curvature_sum_initial_pairs (Nat.succ_le_of_lt hL)]
  rw [forcingPotential_eq_liftedBlock θ 0 hL]
  have he (i j : Fin (L + 1)) :
      (liftedBlock 0 hL X).val j - (liftedBlock 0 hL X).val i =
        X.val (Fin.castLE (Nat.succ_le_of_lt hL) j) -
          X.val (Fin.castLE (Nat.succ_le_of_lt hL) i) := by
    change (cyclicLift X (0 + j.val) - _) - (cyclicLift X (0 + i.val) - _) = _
    simp only [zero_add]
    have hi := cyclicLift_natCast X (Fin.castLE (Nat.succ_le_of_lt hL) i)
    have hj := cyclicLift_natCast X (Fin.castLE (Nat.succ_le_of_lt hL) j)
    dsimp only [Fin.val_castLE] at hi hj
    rw [hi, hj]
    ring
  simp_rw [he]
  simp only [div_mul_eq_mul_div, ← Finset.mul_sum]
  ring

/-- The pair datum has the actual normalized constrained law, without a law premise. -/
theorem curvatureInitialPairs_gibbs (P : Parameters) (N : ℕ+) {L : ℕ}
    (hL : L < (N : ℕ)) {θ : ℝ → ℝ} (hθ : IsForcingCutoff θ) {R : ℝ} (hR : 0 < R) :
    (hsGibbsProbability (curvatureInitialPairs P N (L + 1) hθ hR)
      (hsRieszPairPotentials_curvature_pos N P.2.1 (parametersExponent P)) : Measure _) =
      constrainedLaw P N θ 0 L R := by
  rw [Internal.hsGibbs_eq_tilted, constrainedLaw_eq_volume_tilted]
  congr 1
  funext X
  rw [curvatureInitialPairs_hamiltonian P N hL hθ hR]
  ring

/-- The retained curvature coefficient required by circular block concentration. -/
theorem curvatureInitialPairs_lower (P : Parameters) (N : ℕ+) {M : ℕ}
    (hM : M ≤ (N : ℕ)) {θ : ℝ → ℝ} (hθ : IsForcingCutoff θ) {R : ℝ} (hR : 1 ≤ R)
    (i j : Fin M) {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    P.val.1 * rigidityCurvatureConstant (parametersExponent P).val *
        (N : ℝ) ^ 2 * R ^ (-(parametersExponent P).val - 2) / 2 ≤
      deriv (deriv ((curvatureInitialPairs P N M hθ
        (lt_of_lt_of_le zero_lt_one hR)).potential (Fin.castLE hM i) (Fin.castLE hM j))) r := by
  rw [curvatureInitialPairs_retained P N hM hθ, deriv_const_mul_field', deriv_const_mul_field]
  have h := mul_le_mul_of_nonneg_left
    (curvaturePairPotential_lower N (parametersExponent P) hθ hR hr) P.2.1.le
  linarith

/-- The initial-block coordinates are the retained coordinates, exactly. -/
theorem liftedBlock_zero_coords {N : ℕ+} {L : ℕ} (hL : L < (N : ℕ))
    (X : Configuration N) :
    WithLp.toLp 2 (liftedBlock 0 hL X).val =
      retainedCoord (blockInitialEquiv L.succPNat N (Nat.succ_le_of_lt hL)) X := by
  ext i
  change Fin (L + 1) at i
  change cyclicLift X (0 + i.val) - (⌊cyclicLift X 0⌋ : ℝ) =
    X.val (Fin.castLE (Nat.succ_le_of_lt hL) i)
  have hi := cyclicLift_natCast X (Fin.castLE (Nat.succ_le_of_lt hL) i)
  change cyclicLift X (i.val : ℤ) = X.val (Fin.castLE (Nat.succ_le_of_lt hL) i) at hi
  rw [zero_add, hi, cyclicLift_zero]
  have hf : ⌊X.val ⟨0, N.pos⟩⌋ = 0 := Int.floor_eq_zero_iff.mpr ⟨X.2.2.1, X.2.2.2.1⟩
  rw [hf, Int.cast_zero, sub_zero]

end Riesz1

end
