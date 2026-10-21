/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.AuxiliaryMixedExpansion
public import Riesz1.Unconditional.Bell
public import Riesz1.Frozen.Scale

/-!
# The quadratic-loop term in the variance reduction

Bridge between the Hessian fluctuation expansion and the
quadratic Bell loop, followed by the expectation estimate needed in
Proposition 5.6. The constant is uniform in every smooth
transport, the scale and the particle number. Rigidity is discharged
using the Bakry–Émery criterion `External.BakryEmery` and the Prékopa–Leindler
inequality `External.PrekopaLeindler`, taken as hypotheses.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace Riesz1.Internal

/-- The two pair kernels agree, including on the diagonal. -/
theorem auxiliary_bellPairKernel_eq (s : ℝ) (f : ℝ → ℝ) (x y : ℝ) :
    bellPairKernel s f x y = hessKernel s f x y := by
  simp only [bellPairKernel, hessKernel, iteratedDeriv_succ, iteratedDeriv_zero]

/-- The quadratic loop in the Bell lemma is precisely the normalized
Hessian fluctuation expansion in the mixed variance identity. -/
theorem auxiliary_bellQuadraticLoop_eq (s : RieszExponent) (N : ℕ+) (ℓ : Scale)
    (ψ : LoopScaleProfile ℓ.val) (X : Configuration N) :
    bellQuadraticLoop s N ℓ ψ X = (N : ℝ) ^ (-s.val) *
      hessFluctExpansion s.val (N : ℕ) (loopScaleField ℓ.val ψ.val) X.val := by
  classical
  let f := loopScaleField ℓ.val ψ.val
  have hsum : (∑ p ∈ (Finset.univ : Finset (Fin (N : ℕ))).offDiag,
      bellPairKernel s.val f (X.val p.1) (X.val p.2)) = hessPairSum s.val (N : ℕ) f X.val := by
    have hset : (Finset.univ : Finset (Fin (N : ℕ))).offDiag =
        Finset.univ.filter (fun p : Fin (N : ℕ) × Fin (N : ℕ) => p.1 ≠ p.2) := by
      ext p
      simp
    rw [hset, Finset.sum_filter, Fintype.sum_prod_type]
    unfold hessPairSum
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases hij : j = i
    · simp [hij]
    · rw [ite_eq_left (Ne.symm hij), ite_eq_right hij, auxiliary_bellPairKernel_eq]
  have hright (x : ℝ) : (∫ y in (0 : ℝ)..1, bellPairKernel s.val f x y) =
      hessBackground s.val f x := by simp only [auxiliary_bellPairKernel_eq, hessBackground]
  have hleft (y : ℝ) : (∫ x in (0 : ℝ)..1, bellPairKernel s.val f x y) =
      hessBackground s.val f y := by
    simp_rw [bellPairKernel_symm s.val f, auxiliary_bellPairKernel_eq]
    rfl
  change (N : ℝ) ^ (-s.val) *
    ((∑ p ∈ (Finset.univ : Finset (Fin (N : ℕ))).offDiag,
      bellPairKernel s.val f (X.val p.1) (X.val p.2)) -
      (N : ℝ) * (∑ i, ∫ y in (0 : ℝ)..1, bellPairKernel s.val f (X.val i) y) -
      (N : ℝ) * (∑ j, ∫ x in (0 : ℝ)..1, bellPairKernel s.val f x (X.val j)) +
      (N : ℝ) ^ 2 * (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, bellPairKernel s.val f x y)) = _
  simp_rw [hsum, hright, hleft]
  unfold hessFluctExpansion
  dsimp only [f]
  ring

/-- The expectation estimate used in Proposition 5.6, on exactly the
Hessian expansion of the mixed identity. The constant precedes every
profile as well as `N` and `ℓ`. -/
theorem auxiliary_hessian_expectation (hBE : External.BakryEmery)
    (hPL : External.PrekopaLeindler) (P : Parameters) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (ℓ : Scale) (ψ : LoopScaleProfile ℓ.val),
      1 ≤ (N : ℝ) * ℓ.val → ContDiff ℝ ∞ ψ.val →
      |(N : ℝ) ^ (-P.val.2) * ∫ X : Configuration N,
        hessFluctExpansion P.val.2 (N : ℕ) (loopScaleField ℓ.val ψ.val) X.val ∂gibbsMeasure P N| ≤
        C * (N : ℝ) * ℓ.val * bellEnergy ℓ.val ψ.val := by
  obtain ⟨C, hC, hbell⟩ := bell_energy hBE hPL P.val.1 P.val.2
    P.property.1 P.property.2.1 P.property.2.2
  refine ⟨C, hC, fun N ℓ ψ hK hψ => ?_⟩
  have hb := (hbell N ℓ ψ hK hψ).2
  have he : (∫ X : Configuration N,
      bellQuadraticLoop (parametersExponent P) N ℓ ψ X ∂gibbsMeasure P N) =
      (N : ℝ) ^ (-P.val.2) * ∫ X : Configuration N,
        hessFluctExpansion P.val.2 (N : ℕ) (loopScaleField ℓ.val ψ.val) X.val ∂gibbsMeasure P N := by
    simp_rw [auxiliary_bellQuadraticLoop_eq]
    rw [integral_const_mul]
    rfl
  change |(∫ X : Configuration N,
      bellQuadraticLoop (parametersExponent P) N ℓ ψ X ∂gibbsMeasure P N)| ≤ _ at hb
  rw [he] at hb
  exact hb

end Riesz1.Internal

end
