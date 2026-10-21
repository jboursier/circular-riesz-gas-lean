/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.EllipticRegularity.WeakOperations
public import Riesz1.ToMathlib.EllipticRegularity.LocalTesting
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Continuous linear maps of weak solutions

Real linear maps commute with the local weak predicates from part 1.
This supplies real and complex component bridges for the interior H² regularity argument.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ContDiff Laplacian

namespace Riesz1

variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

omit [CompleteSpace F] [CompleteSpace G] in
/-- Bounded real linear maps preserve local square integrability. -/
theorem LocallySquareIntegrableOn.map {U : Set E} {u : E → F}
    (hu : LocallySquareIntegrableOn U u) (L : F →L[ℝ] G) :
    LocallySquareIntegrableOn U (L ∘ u) :=
  fun K hK hKU => L.comp_memLp' (hu K hK hKU)

/-- Bounded real linear maps commute with weak derivatives. -/
theorem HasWeakDirectionalDerivativeOn.map {U : Set E} {u g : E → F} {v : E}
    (hu : HasWeakDirectionalDerivativeOn U u g v) (L : F →L[ℝ] G) :
    HasWeakDirectionalDerivativeOn U (L ∘ u) (L ∘ g) v := by
  refine ⟨L.locallyIntegrableOn_comp hu.1, L.locallyIntegrableOn_comp hu.2.1, ?_⟩
  intro φ hφ hφc hφU
  have hi := integrable_smul_of_compact_interior hu.2.1 hφ.continuous hφc hφU
  have hj := integrable_smul_of_compact_interior hu.1
    ((hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const)
    (hφc.fderiv_apply ℝ v) ((tsupport_fderiv_apply_subset ℝ v).trans hφU)
  have heq := congrArg L (hu.2.2 φ hφ hφc hφU)
  simpa only [Function.comp_apply, ← L.integral_comp_comm hi,
    ← L.integral_comp_comm hj, map_neg, map_smul] using heq

/-- Bounded real linear maps preserve the original local H² encoding. -/
theorem IsLocalH2.map {U : Set E} {u : E → F} (hu : IsLocalH2 U u)
    (L : F →L[ℝ] G) : IsLocalH2 U (L ∘ u) := by
  obtain ⟨hu, g, h, hd⟩ := hu
  refine ⟨hu.map L, (fun i => L ∘ g i), (fun i j => L ∘ h i j), fun i => ?_⟩
  exact ⟨(hd i).1.map L, (hd i).2.1.map L,
    fun j => ⟨((hd i).2.2 j).1.map L, ((hd i).2.2 j).2.map L⟩⟩

/-- Real linear maps preserve the distributional Schrödinger equation
with real potential, including real and imaginary projections. -/
theorem IsDistributionalSchrodingerSolution.map {U : Set E} {W : E → ℝ} {lam : ℝ}
    {u : E → F} (hu : IsDistributionalSchrodingerSolution U W lam u)
    (L : F →L[ℝ] G) : IsDistributionalSchrodingerSolution U W lam (L ∘ u) := by
  have hpot : (fun x => (W x + lam) • L (u x)) =
      L ∘ (fun x => (W x + lam) • u x) := by
    ext x
    simp only [Function.comp_apply, map_smul]
  refine ⟨L.locallyIntegrableOn_comp hu.1, ?_, ?_⟩
  · change LocallyIntegrableOn (fun x => (W x + lam) • L (u x)) U volume
    rw [hpot]
    exact L.locallyIntegrableOn_comp hu.2.1
  · intro φ hφ hφc hφU
    have hi := integrable_smul_of_compact_interior hu.2.1 hφ.continuous hφc hφU
    have hj := integrable_smul_of_compact_interior hu.1
      (continuous_laplacian_of_compact_smooth hφ hφc)
      (hφc.of_isClosed_subset (isClosed_tsupport _) (tsupport_laplacian_subset φ))
      ((tsupport_laplacian_subset φ).trans hφU)
    have heq := congrArg L (hu.2.2 φ hφ hφc hφU)
    simpa only [Function.comp_apply, ← L.integral_comp_comm hi,
      ← L.integral_comp_comm hj, map_smul] using heq

end Riesz1
