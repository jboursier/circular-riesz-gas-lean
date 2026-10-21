/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.Poincare.Euclidean
public import Riesz1.HelfferSjostrand.GeometryHessian

/-!
# Scalar Poincaré on the anchored Euclidean simplex

Anchored clause. The coordinates are `Fin n`. For
`N = n + 1`, inserting the fixed coordinate zero is an isometric linear
embedding. The measure is explicitly the normalized density `exp (-H*)`
on `0 < y₁ < ⋯ < yₙ < 1`. Its identification with the pushforward
anchored law is independent of this module.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff InnerProductSpace

namespace Riesz1

/-- Insert the fixed first coordinate zero, preserving the Euclidean metric. -/
def scalarPoincareAnchorEmbedding (n : ℕ) :
    EuclideanSpace ℝ (Fin n) →ₗᵢ[ℝ] HsEuclidean ⟨n + 1, Nat.succ_pos n⟩ where
  toFun y := WithLp.toLp 2 (Fin.cons (α := fun _ => ℝ) 0 y)
  map_add' y z := by
    ext i
    change Fin.cons (α := fun _ => ℝ) 0 (y + z).ofLp i = Fin.cons (α := fun _ => ℝ) 0 y.ofLp i + Fin.cons (α := fun _ => ℝ) 0 z.ofLp i
    cases i using Fin.cases <;> simp
  map_smul' a y := by
    ext i
    change Fin.cons (α := fun _ => ℝ) 0 (a • y).ofLp i = a * Fin.cons (α := fun _ => ℝ) 0 y.ofLp i
    cases i using Fin.cases <;> simp
  norm_map' y := by
    change ‖(WithLp.toLp 2 (Fin.cons (α := fun _ => ℝ) 0 y.ofLp) : EuclideanSpace ℝ (Fin (n + 1)))‖ = ‖y‖
    have h : ‖(WithLp.toLp 2 (Fin.cons (α := fun _ => ℝ) 0 y.ofLp) : EuclideanSpace ℝ (Fin (n + 1)))‖ ^ 2 =
        ‖y‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fin.sum_univ_succ]
      simp
    nlinarith [norm_nonneg y,
      norm_nonneg (WithLp.toLp 2 (Fin.cons (α := fun _ => ℝ) 0 y.ofLp) : EuclideanSpace ℝ (Fin (n + 1)))]

/-- The anchored simplex in its actual `N - 1` Euclidean coordinates. -/
def scalarPoincareAnchorDomain (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  (scalarPoincareAnchorEmbedding n) ⁻¹' hsChamber ⟨n + 1, Nat.succ_pos n⟩

theorem scalarPoincareAnchorDomain_iff {n : ℕ} (y : EuclideanSpace ℝ (Fin n)) :
    y ∈ scalarPoincareAnchorDomain n ↔ StrictMono y ∧ ∀ i, 0 < y i ∧ y i < 1 := by
  change (StrictMono (Fin.cons (α := fun _ => ℝ) 0 y.ofLp) ∧
    ∀ i, Fin.cons (α := fun _ => ℝ) 0 y.ofLp i < Fin.cons (α := fun _ => ℝ) 0 y.ofLp 0 + 1) ↔ _
  constructor
  · rintro ⟨hm, hb⟩
    exact ⟨fun i j hij => hm (Fin.succ_lt_succ_iff.mpr hij), fun i =>
      ⟨hm (Fin.succ_pos i), by simpa using hb i.succ⟩⟩
  · rintro ⟨hm, hb⟩
    constructor
    · exact Fin.strictMono_cons.mpr ⟨fun i => (hb i).1, hm⟩
    · intro i
      cases i using Fin.cases with
      | zero => simp
      | succ i => simpa using (hb i).2

theorem isOpen_scalarPoincareAnchorDomain (n : ℕ) :
    IsOpen (scalarPoincareAnchorDomain n) :=
  (isOpen_hsChamber _).preimage (scalarPoincareAnchorEmbedding n).continuous

theorem convex_scalarPoincareAnchorDomain (n : ℕ) :
    Convex ℝ (scalarPoincareAnchorDomain n) := by
  intro x hx y hy a b ha hb hab
  rw [scalarPoincareAnchorDomain_iff] at hx hy ⊢
  constructor
  · intro i j hij
    change a * x i + b * y i < a * x j + b * y j
    rcases ha.eq_or_lt with h | h
    · have hb1 : b = 1 := by linarith
      simpa [← h, hb1] using hy.1 hij
    · exact add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left (hx.1 hij) h)
        (mul_le_mul_of_nonneg_left (hy.1 hij).le hb)
  · intro i
    change 0 < a * x i + b * y i ∧ a * x i + b * y i < 1
    have hpos : 0 < a * x i + b * y i := by
      rcases ha.eq_or_lt with h | h
      · have hb1 : b = 1 := by linarith
        simpa [← h, hb1] using (hy.2 i).1
      · exact add_pos_of_pos_of_nonneg (mul_pos h (hx.2 i).1)
          (mul_nonneg hb (hy.2 i).1.le)
    refine ⟨hpos, ?_⟩
    rcases ha.eq_or_lt with h | h
    · have hb1 : b = 1 := by linarith
      simpa [← h, hb1] using (hy.2 i).2
    · have := add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left (hx.2 i).2 h)
        (mul_le_mul_of_nonneg_left (hy.2 i).2.le hb)
      nlinarith

theorem bounded_scalarPoincareAnchorDomain (n : ℕ) :
    Bornology.IsBounded (scalarPoincareAnchorDomain n) := by
  let e := PiLp.homeomorph 2 (fun _ : Fin n => ℝ)
  have hbox : Bornology.IsBounded
      (e.symm '' Icc (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ))) :=
    (isCompact_Icc.image e.symm.continuous).isBounded
  apply hbox.subset
  intro y hy
  have h := (scalarPoincareAnchorDomain_iff y).mp hy
  exact ⟨WithLp.ofLp y, ⟨fun i => (h.2 i).1.le, fun i => (h.2 i).2.le⟩, rfl⟩

theorem nonempty_scalarPoincareAnchorDomain (n : ℕ) :
    (scalarPoincareAnchorDomain n).Nonempty := by
  refine ⟨WithLp.toLp 2 (fun i : Fin n => ((i : ℕ) + 1 : ℝ) / (n + 1)), ?_⟩
  rw [scalarPoincareAnchorDomain_iff]
  have hn : (0 : ℝ) < n + 1 := by positivity
  constructor
  · intro i j hij
    exact (div_lt_div_iff_of_pos_right hn).mpr (by exact_mod_cast Nat.succ_lt_succ hij)
  · intro i
    constructor
    · exact div_pos (by positivity) hn
    · apply (div_lt_one hn).mpr
      exact_mod_cast Nat.succ_lt_succ i.isLt

/-- The anchored potential `H*(y) = H(0,y)`, on all Euclidean coordinates. -/
def scalarPoincareAnchorPotential {n : ℕ} {c : ℝ}
    (χ : HsPairPotentials ⟨n + 1, Nat.succ_pos n⟩ c)
    (y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  hsPairExpression χ (scalarPoincareAnchorEmbedding n y)

theorem contDiffOn_scalarPoincareAnchorPotential {n : ℕ} {c : ℝ}
    (χ : HsPairPotentials ⟨n + 1, Nat.succ_pos n⟩ c) :
    ContDiffOn ℝ ∞ (scalarPoincareAnchorPotential χ) (scalarPoincareAnchorDomain n) :=
  (hsPairExpression_contDiffOn χ).comp (scalarPoincareAnchorEmbedding n).contDiff.contDiffOn
    (fun _ hx => hx)

theorem hessian_scalarPoincareAnchorPotential {n : ℕ} {c : ℝ}
    (χ : HsPairPotentials ⟨n + 1, Nat.succ_pos n⟩ c)
    {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ scalarPoincareAnchorDomain n)
    (u v : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (fderiv ℝ (scalarPoincareAnchorPotential χ)) y u v =
      fderiv ℝ (fderiv ℝ (hsPairExpression χ)) (scalarPoincareAnchorEmbedding n y)
        (scalarPoincareAnchorEmbedding n u) (scalarPoincareAnchorEmbedding n v) := by
  let A := (scalarPoincareAnchorEmbedding n).toContinuousLinearMap
  have hgrad : fderiv ℝ (scalarPoincareAnchorPotential χ) =ᶠ[𝓝 y]
      fun z => (hsPairGradient χ (A z)).comp A := by
    filter_upwards [(isOpen_scalarPoincareAnchorDomain n).mem_nhds hy] with z hz
    exact ((hasFDerivAt_hsPairExpression χ hz).comp z A.hasFDerivAt).fderiv
  rw [hgrad.fderiv_eq]
  have hc : HasFDerivAt (fun z => hsPairGradient χ (A z))
      ((hsPairHessian χ (A y)).comp A) y :=
    (hasFDerivAt_hsPairGradient χ hy).comp y A.hasFDerivAt
  rw [(hc.clm_comp (hasFDerivAt_const A y)).fderiv, fderiv_fderiv_hsPairExpression χ hy]
  simp [A, ContinuousLinearMap.comp_apply]
  rfl

theorem hessian_scalarPoincareAnchorPotential_lower {n : ℕ} {c : ℝ}
    (χ : HsPairPotentials ⟨n + 1, Nat.succ_pos n⟩ c) (hc : 0 < c)
    {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ scalarPoincareAnchorDomain n)
    (b : EuclideanSpace ℝ (Fin n)) :
    2 * c * ‖b‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (scalarPoincareAnchorPotential χ)) y b b := by
  rw [hessian_scalarPoincareAnchorPotential χ hy]
  have h := hessian_hsPairExpression_first_lower χ hc hy
    (scalarPoincareAnchorEmbedding n b) (by rfl)
  simpa only [LinearIsometry.norm_map] using h

/-- **Scalar Poincaré, anchored clause.**
For `N = n + 1 ≥ 2`, every function in the Euclidean weighted `H¹` of
the probability proportional to `exp (-H(0,y))` on the ordered simplex
satisfies the inequality with constant `(2c)⁻¹`.

Only pair convexity is needed. The boundary-growth admissibility condition
is therefore unnecessary here. -/
theorem scalar_poincare_anchored (hPL : External.PrekopaLeindler) {n : ℕ} (hn : 0 < n)
    {c : ℝ} (χ : HsPairPotentials ⟨n + 1, Nat.succ_pos n⟩ c) (hc : 0 < c)
    {F : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hFG : WeightedSobolev.IsWeightedH1
      ((volume.restrict (scalarPoincareAnchorDomain n)).tilted
        (fun y => -scalarPoincareAnchorPotential χ y)) (scalarPoincareAnchorDomain n) F G) :
    let ν := (volume.restrict (scalarPoincareAnchorDomain n)).tilted
      (fun y => -scalarPoincareAnchorPotential χ y)
    (∫ y, (F y - ∫ z, F z ∂ν) ^ 2 ∂ν) ≤ (2 * c)⁻¹ * ∫ y, ‖G y‖ ^ 2 ∂ν :=
  poincare_euclidean_H1 hPL hn (bounded_scalarPoincareAnchorDomain n)
    (isOpen_scalarPoincareAnchorDomain n) (nonempty_scalarPoincareAnchorDomain n)
    (convex_scalarPoincareAnchorDomain n) (contDiffOn_scalarPoincareAnchorPotential χ |>.of_le
      (by norm_num)) (mul_pos (by norm_num) hc)
    (fun _ hy b => hessian_scalarPoincareAnchorPotential_lower χ hc hy b) hFG

/-- Normalization of the anchored density is positive and finite, and its
tilt is a probability. These facts precede any real-integral inequality. -/
theorem scalarPoincareAnchor_normalization {n : ℕ} {c : ℝ}
    (χ : HsPairPotentials ⟨n + 1, Nat.succ_pos n⟩ c) (hc : 0 < c) :
    (0 < ∫⁻ y in scalarPoincareAnchorDomain n,
      ENNReal.ofReal (Real.exp (-scalarPoincareAnchorPotential χ y))) ∧
    (∫⁻ y in scalarPoincareAnchorDomain n,
      ENNReal.ofReal (Real.exp (-scalarPoincareAnchorPotential χ y))) < ⊤ ∧
    IsProbabilityMeasure ((volume.restrict (scalarPoincareAnchorDomain n)).tilted
      (fun y => -scalarPoincareAnchorPotential χ y)) := by
  have hV : ContDiffOn ℝ 2 (scalarPoincareAnchorPotential χ) (scalarPoincareAnchorDomain n) :=
    (contDiffOn_scalarPoincareAnchorPotential χ).of_le (by norm_num)
  have hκ : 0 < 2 * c := mul_pos (by norm_num) hc
  have hb := fun y (hy : y ∈ scalarPoincareAnchorDomain n) b =>
    hessian_scalarPoincareAnchorPotential_lower χ hc hy b
  obtain ⟨hp, hf⟩ := bl_convex_lintegral_bounds (bounded_scalarPoincareAnchorDomain n)
    (convex_scalarPoincareAnchorDomain n) (isOpen_scalarPoincareAnchorDomain n)
    (nonempty_scalarPoincareAnchorDomain n) hV hκ hb
  exact ⟨hp, hf, bl_convex_isProbabilityMeasure (bounded_scalarPoincareAnchorDomain n)
    (convex_scalarPoincareAnchorDomain n) (isOpen_scalarPoincareAnchorDomain n)
    (nonempty_scalarPoincareAnchorDomain n) hV hκ hb⟩

end Riesz1

end
