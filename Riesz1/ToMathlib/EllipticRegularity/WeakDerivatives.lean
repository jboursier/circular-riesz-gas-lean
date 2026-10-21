/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.WeightedSobolev.LocalIntegrationByParts
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Explicit local weak derivatives and local H²

`HasWeakDirectionalDerivativeOn U u g v` uses integration against every
real smooth test with compact support inside `U`. Equality is in the
codomain, so the definition works for both real and complex functions.
Local integrability is included, preventing nonintegrable Bochner
integrals from giving spurious identities.

`IsLocalH2 U u` requires locally square integrable representatives for
`u`, every coordinate weak derivative and every iterated coordinate weak
derivative. Coordinates are an orthonormal basis of the ambient Euclidean
space. In finite dimension these finitely many scalar derivatives are
exactly the usual weak gradient and weak Hessian, and their local L²
conditions are the usual H²_loc conditions. No classical derivative of
an arbitrary representative of `u` is used in this definition.

These are encodings for the interior H² regularity argument. This file does not prove
regularity of a distributional solution.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ContDiff Laplacian

namespace Riesz1

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Local square integrability, tested on every compact subset of the domain. -/
def LocallySquareIntegrableOn (U : Set E) (u : E → F) : Prop :=
  ∀ K : Set E, IsCompact K → K ⊆ U → MemLp u 2 (volume.restrict K)

/-- A distributional first derivative, including local integrability of
both representatives. Test functions are real even for complex `u`. -/
def HasWeakDirectionalDerivativeOn (U : Set E) (u g : E → F) (v : E) : Prop :=
  LocallyIntegrableOn u U ∧ LocallyIntegrableOn g U ∧
    ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
      (∫ x, φ x • g x) = - ∫ x, (fderiv ℝ φ x v) • u x

/-- Local H², with explicit first and second weak partial derivatives. -/
def IsLocalH2 (U : Set E) (u : E → F) : Prop :=
  LocallySquareIntegrableOn U u ∧
    ∃ (g : Fin (Module.finrank ℝ E) → E → F)
      (h : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → E → F),
      ∀ i, LocallySquareIntegrableOn U (g i) ∧
        HasWeakDirectionalDerivativeOn U u (g i) (stdOrthonormalBasis ℝ E i) ∧
        ∀ j, LocallySquareIntegrableOn U (h i j) ∧
          HasWeakDirectionalDerivativeOn U (g i) (h i j) (stdOrthonormalBasis ℝ E j)

/-- The equation `(-Δ + W + λ)u = 0` tested distributionally.
Local integrability makes every displayed test integral meaningful.
The global L² assumption of the interior H² regularity argument is separate
from this predicate. -/
def IsDistributionalSchrodingerSolution (U : Set E) (W : E → ℝ) (lam : ℝ)
    (u : E → F) : Prop :=
  LocallyIntegrableOn u U ∧
    LocallyIntegrableOn (fun x => (W x + lam) • u x) U ∧
    ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
      (∫ x, φ x • ((W x + lam) • u x)) = ∫ x, (Δ φ) x • u x

omit [NormedSpace ℝ F] [CompleteSpace F] in
/-- Continuous functions on the domain are locally square integrable. -/
theorem locallySquareIntegrableOn_of_continuousOn {U : Set E} {u : E → F}
    (hu : ContinuousOn u U) : LocallySquareIntegrableOn U u := by
  intro K hK hKU
  have hc := hu.mono hKU
  exact (memLp_two_iff_integrable_sq_norm (hc.aestronglyMeasurable hK.measurableSet)).mpr
    ((hc.norm.pow 2).integrableOn_compact hK)

omit [NormedSpace ℝ F] [CompleteSpace F] in
/-- Local L² representatives are locally integrable on an open domain. -/
theorem LocallySquareIntegrableOn.locallyIntegrableOn {U : Set E} {u : E → F}
    (hu : LocallySquareIntegrableOn U u) (hU : IsOpen U) : LocallyIntegrableOn u U := by
  rw [locallyIntegrableOn_iff hU.isLocallyClosed]
  intro K hKU hK
  have : IsFiniteMeasure (volume.restrict K) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hK.measure_lt_top (μ := volume)⟩
  exact (hu K hK hKU).integrable (by norm_num)

omit [CompleteSpace F] in
/-- Multiplication by a locally continuous potential preserves local L². -/
theorem LocallySquareIntegrableOn.smul_continuousOn {U : Set E} {u : E → F}
    (hu : LocallySquareIntegrableOn U u) {w : E → ℝ} (hw : ContinuousOn w U) :
    LocallySquareIntegrableOn U (fun x => w x • u x) := by
  intro K hK hKU
  have hc := hw.mono hKU
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc
  have hm : MemLp w ⊤ (volume.restrict K) :=
    memLp_top_of_bound (hc.aestronglyMeasurable hK.measurableSet) C
      ((ae_restrict_mem hK.measurableSet).mono hC)
  exact hm.smul (hu K hK hKU)

/-- For real smooth functions the weak directional derivative is the
classical derivative. The proof reuses local cutoff integration by parts. -/
theorem hasWeakDirectionalDerivativeOn_of_smooth {U : Set E} {u : E → ℝ}
    (hU : IsOpen U) (hu : ContDiffOn ℝ ∞ u U) (v : E) :
    HasWeakDirectionalDerivativeOn U u (fun x => fderiv ℝ u x v) v := by
  have hg : ContinuousOn (fun x => fderiv ℝ u x v) U :=
    (hu.continuousOn_fderiv_of_isOpen hU (by norm_num)).clm_apply continuousOn_const
  refine ⟨hu.continuousOn.locallyIntegrableOn hU.measurableSet,
    hg.locallyIntegrableOn hU.measurableSet, ?_⟩
  intro φ hφ hφc hφU
  have hi := WeightedSobolev.integral_weighted_fderiv_of_compact_test
    (μ := volume) hU hφ hφc hφU hu (contDiffOn_const (c := (1 : ℝ))) v
  simpa only [mul_one, smul_eq_mul, mul_comm] using hi

/-- Smooth real functions belong to the explicit weak-derivative H²_loc
space. No integrability near the boundary of `U` is imposed. -/
theorem isLocalH2_of_smooth {U : Set E} {u : E → ℝ}
    (hU : IsOpen U) (hu : ContDiffOn ℝ ∞ u U) : IsLocalH2 U u := by
  refine ⟨locallySquareIntegrableOn_of_continuousOn hu.continuousOn,
    (fun i x => fderiv ℝ u x (stdOrthonormalBasis ℝ E i)),
    (fun i j x => fderiv ℝ (fun y => fderiv ℝ u y (stdOrthonormalBasis ℝ E i))
      x (stdOrthonormalBasis ℝ E j)), ?_⟩
  intro i
  have hg : ContDiffOn ℝ ∞ (fun x => fderiv ℝ u x (stdOrthonormalBasis ℝ E i)) U :=
    (hu.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const
  refine ⟨locallySquareIntegrableOn_of_continuousOn hg.continuousOn,
    hasWeakDirectionalDerivativeOn_of_smooth hU hu _, ?_⟩
  intro j
  exact ⟨locallySquareIntegrableOn_of_continuousOn
      ((hg.continuousOn_fderiv_of_isOpen hU (by norm_num)).clm_apply continuousOn_const),
    hasWeakDirectionalDerivativeOn_of_smooth hU hg _⟩

end Riesz1
