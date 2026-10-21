/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.WeightedSobolev.BoundedProduct
public import Riesz1.HelfferSjostrand.AnchoredSobolevPiecewiseComposition
public import Riesz1.HelfferSjostrand.AnchoredCalculus

/-!
# Sobolev calculus for assembling the cutoff loop

These internal calculus lemmas preserve the anchored completion.
Classical gradient formulas are used only after membership is established
by the completed-graph chain and product rules.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ContDiff

namespace Riesz1.Internal

variable {n : ℕ} {c : ℝ} (Q : HsPairPotentials n.succPNat c) (hc : 0 < c)

include hc

/-- The anchored chain rule without requiring the scalar map to fix zero. -/
theorem varAlAssembly_comp_piecewise
    {F : AnchoredEuclidean n → ℝ} {G : AnchoredEuclidean n → AnchoredEuclidean n}
    (hF : IsAnchoredH1 Q F G) {T : ℝ → ℝ} {C : NNReal}
    (hT : LipschitzWith C T) {B : Set ℝ} (hB : B.Finite)
    (hTC : ContDiffOn ℝ 1 T Bᶜ) :
    IsAnchoredH1 Q (fun x => T (F x)) (fun x => deriv T (F x) • G x) := by
  have := isProbabilityMeasure_anchoredMeasureE Q hc
  have hTS : LipschitzWith C (fun r => T r - T 0) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [dist_sub_right] using hT.dist_le_mul x y
  have hS := hF.comp_piecewise Q hc hTS (by simp) hB
    (hTC.sub contDiffOn_const)
  have hconst : IsAnchoredH1 Q (fun _ => T 0) (fun _ => 0) := by
    change WeightedSobolev.IsWeightedH1 _ _ _ _
    simpa only [gradient_fun_const'] using WeightedSobolev.isWeightedH1_of_smoothNearClosure
      (isBounded_anchoredSimplex n) (ae_mem_anchoredSimplex Q)
      (f := fun _ => T 0) ⟨univ, isOpen_univ, subset_univ _, contDiffOn_const⟩
  have hadd := WeightedSobolev.IsWeightedH1.add (isBounded_anchoredSimplex n)
    (ae_mem_anchoredSimplex Q) hS hconst
  apply hadd.congr
  · exact Eventually.of_forall fun x => sub_add_cancel _ _
  · exact Eventually.of_forall fun x => by simp only [deriv_sub_const, add_zero]

/-- A piecewise smooth chain rule with the classical gradient, when
both classical derivatives exist almost everywhere. Membership is supplied
by the preceding chain rule, rather than inferred from differentiability. -/
theorem varAlAssembly_comp_classical
    {F : AnchoredEuclidean n → ℝ} (hF : IsAnchoredH1 Q F (gradient F))
    (hdF : ∀ᵐ x ∂anchoredMeasureE Q, DifferentiableAt ℝ F x)
    {T : ℝ → ℝ} {C : NNReal} (hT : LipschitzWith C T)
    {B : Set ℝ} (hB : B.Finite) (hTC : ContDiffOn ℝ 1 T Bᶜ)
    (hdT : ∀ᵐ x ∂anchoredMeasureE Q, DifferentiableAt ℝ T (F x)) :
    IsAnchoredH1 Q (fun x => T (F x)) (gradient (fun x => T (F x))) := by
  have h := varAlAssembly_comp_piecewise Q hc hF hT hB hTC
  apply h.congr EventuallyEq.rfl
  filter_upwards [hdF, hdT] with x hx hy
  have he := (hy.hasDerivAt.comp_hasFDerivAt x hx.hasFDerivAt).fderiv
  change fderiv ℝ (fun x => T (F x)) x = _ at he
  change _ = (InnerProductSpace.toDual ℝ (AnchoredEuclidean n)).symm
    (fderiv ℝ (fun x => T (F x)) x)
  rw [he, map_smul]
  rfl

/-- The classical gradient of a bounded product in the anchored completion. -/
theorem varAlAssembly_mul_classical
    {F H : AnchoredEuclidean n → ℝ}
    (hF : IsAnchoredH1 Q F (gradient F)) (hH : IsAnchoredH1 Q H (gradient H))
    (hdF : ∀ᵐ x ∂anchoredMeasureE Q, DifferentiableAt ℝ F x)
    (hdH : ∀ᵐ x ∂anchoredMeasureE Q, DifferentiableAt ℝ H x)
    {M D : ℝ} (hM : 0 ≤ M) (hD : 0 ≤ D)
    (hbF : ∀ᵐ x ∂anchoredMeasureE Q, |F x| ≤ M)
    (hbH : ∀ᵐ x ∂anchoredMeasureE Q, |H x| ≤ D) :
    IsAnchoredH1 Q (fun x => F x * H x) (gradient (fun x => F x * H x)) := by
  have := isProbabilityMeasure_anchoredMeasureE Q hc
  have h := WeightedSobolev.IsWeightedH1.mul_of_bound (isBounded_anchoredSimplex n)
    (ae_mem_anchoredSimplex Q) hF hH hM hD hbF hbH
  apply h.congr EventuallyEq.rfl
  filter_upwards [hdF, hdH] with x hx hy
  change _ = (InnerProductSpace.toDual ℝ (AnchoredEuclidean n)).symm
    (fderiv ℝ (fun x => F x * H x) x)
  have he := (hx.hasFDerivAt.mul hy.hasFDerivAt).fderiv
  change fderiv ℝ (fun x => F x * H x) x = _ at he
  rw [he, map_add, map_smul, map_smul]
  rfl

/-- Finite products of unit-interval Sobolev factors belong to the
anchored completion with the actual gradient. -/
theorem varAlAssembly_prod_classical {ι : Type*} (I : Finset ι)
    (f : ι → AnchoredEuclidean n → ℝ)
    (hf : ∀ i ∈ I, IsAnchoredH1 Q (f i) (gradient (f i)))
    (hd : ∀ i ∈ I, ∀ᵐ x ∂anchoredMeasureE Q, DifferentiableAt ℝ (f i) x)
    (hb : ∀ i ∈ I, ∀ᵐ x ∂anchoredMeasureE Q, f i x ∈ Icc (0 : ℝ) 1) :
    IsAnchoredH1 Q (fun x => ∏ i ∈ I, f i x) (gradient (fun x => ∏ i ∈ I, f i x)) := by
  classical
  have := isProbabilityMeasure_anchoredMeasureE Q hc
  induction I using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    exact WeightedSobolev.isWeightedH1_of_smoothNearClosure
      (isBounded_anchoredSimplex n) (ae_mem_anchoredSimplex Q)
      ⟨univ, isOpen_univ, subset_univ _, contDiffOn_const⟩
  | @insert i I hi ih =>
    simp only [Finset.prod_insert hi]
    have hI : ∀ j ∈ I, j ∈ insert i I := fun _ hj => Finset.mem_insert_of_mem hj
    apply varAlAssembly_mul_classical Q hc (hf i (Finset.mem_insert_self _ _))
      (ih (fun j hj => hf j (hI j hj)) (fun j hj => hd j (hI j hj))
        (fun j hj => hb j (hI j hj))) (hd i (Finset.mem_insert_self _ _))
    · filter_upwards [(ae_ball_iff I.countable_toSet).mpr (fun j hj => hd j (hI j hj))]
        with x hx
      exact (HasFDerivAt.finsetProd (fun j hj => (hx j hj).hasFDerivAt)).differentiableAt
    · exact zero_le_one
    · exact zero_le_one
    · filter_upwards [hb i (Finset.mem_insert_self _ _)] with x hx
      rw [abs_of_nonneg hx.1]
      exact hx.2
    · filter_upwards [(ae_ball_iff I.countable_toSet).mpr (fun j hj => hb j (hI j hj))]
        with x hx
      rw [abs_of_nonneg (Finset.prod_nonneg (fun j hj => (hx j hj).1))]
      exact Finset.prod_le_one₀ (fun j hj => (hx j hj).1) (fun j hj => (hx j hj).2)

/-- Finite unit-interval products, retaining differentiability and the
unit-interval bound for subsequent products. -/
theorem varAlAssembly_prod_bundle {ι : Type*} (I : Finset ι)
    (f : ι → AnchoredEuclidean n → ℝ)
    (hf : ∀ i ∈ I, IsAnchoredH1 Q (f i) (gradient (f i)) ∧
      ∀ᵐ x ∂anchoredMeasureE Q, DifferentiableAt ℝ (f i) x)
    (hb : ∀ i ∈ I, ∀ x, f i x ∈ Icc (0 : ℝ) 1) :
    let F := fun x => ∏ i ∈ I, f i x
    IsAnchoredH1 Q F (gradient F) ∧
      (∀ᵐ x ∂anchoredMeasureE Q, DifferentiableAt ℝ F x) ∧
      ∀ x, F x ∈ Icc (0 : ℝ) 1 := by
  classical
  refine ⟨varAlAssembly_prod_classical Q hc I f (fun i hi => (hf i hi).1)
    (fun i hi => (hf i hi).2) (fun i hi => Eventually.of_forall (hb i hi)), ?_, ?_⟩
  · filter_upwards [(ae_ball_iff I.countable_toSet).mpr (fun i hi => (hf i hi).2)] with x hx
    exact (HasFDerivAt.finsetProd (fun i hi => (hx i hi).hasFDerivAt)).differentiableAt
  · intro x
    exact ⟨Finset.prod_nonneg (fun i hi => (hb i hi x).1),
      Finset.prod_le_one₀ (fun i hi => (hb i hi x).1) (fun i hi => (hb i hi x).2)⟩

end Riesz1.Internal

end
