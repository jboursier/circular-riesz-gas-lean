/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.BlockEnergies
public import Riesz1.HelfferSjostrand.GeometryHessian

/-!
# The retained curvature in circular block concentration

The algebraic step of Lemma 3.9: the retained energy has curvature
`c₁ m` on the zero-sum hyperplane when the retained pair curvatures are at least `c₁ / 2`.
These statements include singleton blocks. No admissibility or external theorem is needed.
-/

@[expose] public section

noncomputable section

open Finset Set

namespace Riesz1

variable {N M : ℕ+} {c c₁ : ℝ} {n : ℕ}

/-- Restriction of the pair data to an increasing list of retained labels. -/
def blockPairPotentials (χ : HsPairPotentials N c)
    (e : Fin (M : ℕ) ⊕ Fin n ≃ Fin (N : ℕ))
    (hmono : StrictMono fun a => e (Sum.inl a)) : HsPairPotentials M c where
  potential a b := χ.potential (e (Sum.inl a)) (e (Sum.inl b))
  symmetric _ _ := χ.symmetric _ _
  smooth _ _ hab := χ.smooth _ _ (hmono hab)
  curvature _ _ hab := χ.curvature _ _ (hmono hab)
  leftBoundary _ _ hab := χ.leftBoundary _ _ (hmono hab)
  rightBoundary _ _ hab := χ.rightBoundary _ _ (hmono hab)

theorem blockRetainedEnergy_eq_pairExpression (χ : HsPairPotentials N c)
    (e : Fin (M : ℕ) ⊕ Fin n ≃ Fin (N : ℕ))
    (hmono : StrictMono fun a => e (Sum.inl a)) :
    blockRetainedEnergy χ e = hsPairExpression (blockPairPotentials χ e hmono) := rfl

theorem retainedChamber_eq_hsChamber (M : ℕ+) : retainedChamber (M : ℕ) = hsChamber M := by
  ext z
  constructor
  · rintro ⟨hmono, hlt⟩
    exact ⟨hmono, fun b => hlt ⟨0, M.pos⟩ b⟩
  · rintro ⟨hmono, hlt⟩
    refine ⟨hmono, fun a b => ?_⟩
    have h0 : z ⟨0, M.pos⟩ ≤ z a := hmono.monotone (Fin.zero_le a)
    linarith [hlt b]

/-- The exact Hessian of the retained energy, including its factor two. -/
theorem hessian_blockRetainedEnergy (χ : HsPairPotentials N c)
    (e : Fin (M : ℕ) ⊕ Fin n ≃ Fin (N : ℕ))
    (hmono : StrictMono fun a => e (Sum.inl a))
    {z : HsEuclidean M} (hz : z ∈ retainedChamber (M : ℕ)) (a : HsEuclidean M) :
    fderiv ℝ (fderiv ℝ (blockRetainedEnergy χ e)) z a a =
      2 * ∑ i : Fin (M : ℕ), ∑ j ∈ univ.filter (i < ·),
        deriv (deriv (χ.potential (e (Sum.inl i)) (e (Sum.inl j))))
          (z j - z i) * (a j - a i) ^ 2 := by
  rw [blockRetainedEnergy_eq_pairExpression χ e hmono]
  exact hessian_hsPairExpression_self (blockPairPotentials χ e hmono)
    (by rwa [retainedChamber_eq_hsChamber] at hz) a

/-- The retained Hessian lower bound before restricting to the zero-sum hyperplane. -/
theorem hessian_blockRetainedEnergy_lower (χ : HsPairPotentials N c)
    (e : Fin (M : ℕ) ⊕ Fin n ≃ Fin (N : ℕ))
    (hmono : StrictMono fun a => e (Sum.inl a))
    {z : HsEuclidean M} (hz : z ∈ retainedChamber (M : ℕ))
    (hcurv : ∀ i j : Fin (M : ℕ), i < j → c₁ / 2 ≤
      deriv (deriv (χ.potential (e (Sum.inl i)) (e (Sum.inl j)))) (z j - z i))
    (a : HsEuclidean M) :
    c₁ * ((M : ℝ) * ‖a‖ ^ 2 - (∑ i, a i) ^ 2) ≤
      fderiv ℝ (fderiv ℝ (blockRetainedEnergy χ e)) z a a := by
  have hnorm : ‖a‖ ^ 2 = ∑ i, a i ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Real.norm_eq_abs, sq_abs]
  have hsum := sum_filter_lt_sq_eq (M : ℕ) (fun i => a i)
  have hle : c₁ / 2 * (∑ i : Fin (M : ℕ), ∑ j ∈ univ.filter (i < ·),
      (a j - a i) ^ 2) ≤ ∑ i : Fin (M : ℕ), ∑ j ∈ univ.filter (i < ·),
      deriv (deriv (χ.potential (e (Sum.inl i)) (e (Sum.inl j))))
        (z j - z i) * (a j - a i) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j hj =>
      mul_le_mul_of_nonneg_right (hcurv i j (Finset.mem_filter.mp hj).2) (sq_nonneg _)
  rw [hessian_blockRetainedEnergy χ e hmono hz]
  rw [hsum, ← hnorm] at hle
  linarith

/-- The curvature `c₁ m` used in Lemma 3.9. The hypothesis on `a` is exactly
membership in the hyperplane perpendicular to common translations. -/
theorem hessian_blockRetainedEnergy_zero_sum (χ : HsPairPotentials N c)
    (e : Fin (M : ℕ) ⊕ Fin n ≃ Fin (N : ℕ))
    (hmono : StrictMono fun a => e (Sum.inl a))
    {z : HsEuclidean M} (hz : z ∈ retainedChamber (M : ℕ))
    (hcurv : ∀ i j : Fin (M : ℕ), i < j → c₁ / 2 ≤
      deriv (deriv (χ.potential (e (Sum.inl i)) (e (Sum.inl j)))) (z j - z i))
    (a : HsEuclidean M) (ha : ∑ i, a i = 0) :
    c₁ * M * ‖a‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (blockRetainedEnergy χ e)) z a a := by
  have h := hessian_blockRetainedEnergy_lower χ e hmono hz hcurv a
  simpa only [ha, zero_pow (by norm_num : 2 ≠ 0), sub_zero, mul_assoc] using h

/-- A retained curvature hypothesis on full configurations also holds at every retained
lift. This uses the actual nonempty exterior fiber, without a stronger hypothesis on the
pair potentials away from configurations. -/
theorem block_curvature_of_full_chamber (χ : HsPairPotentials N c)
    (e : Fin (M : ℕ) ⊕ Fin n ≃ Fin (N : ℕ))
    (hmono : StrictMono fun a => e (Sum.inl a))
    (he0 : e (Sum.inl ⟨0, M.pos⟩) = ⟨0, N.pos⟩)
    (hcurv : ∀ x ∈ hsChamber N, ∀ i j : Fin (M : ℕ), i < j → c₁ / 2 ≤
      deriv (deriv (χ.potential (e (Sum.inl i)) (e (Sum.inl j)))) (x (e (Sum.inl j)) - x (e (Sum.inl i))))
    {z : HsEuclidean M} (hz : z ∈ retainedChamber (M : ℕ))
    (i j : Fin (M : ℕ)) (hij : i < j) :
    c₁ / 2 ≤ deriv (deriv (χ.potential (e (Sum.inl i)) (e (Sum.inl j)))) (z j - z i) := by
  obtain ⟨y, hy⟩ := exists_lift_of_mem_retainedChamber e hmono M.pos he0 hz
  simpa only [blockLift_inl] using hcurv (blockLift e (z, y)) hy i j hij

/-- The coefficient check on two particles, where `d = χ''` and the Hessian is
`2 d (a₁-a₀)²`: its zero-sum curvature is at least `2 c₁`. -/
theorem block_concentration_two_particle_curvature {d : ℝ} (hcurv : c₁ / 2 ≤ d)
    (a₀ a₁ : ℝ) (ha : a₀ + a₁ = 0) :
    2 * c₁ * (a₀ ^ 2 + a₁ ^ 2) ≤ 2 * d * (a₁ - a₀) ^ 2 := by
  have h := mul_le_mul_of_nonneg_right hcurv (sq_nonneg (a₁ - a₀))
  have he : (a₁ - a₀) ^ 2 = 2 * (a₀ ^ 2 + a₁ ^ 2) := by nlinarith [sq_nonneg (a₀ + a₁)]
  rw [he] at h ⊢
  linarith

end Riesz1

end
