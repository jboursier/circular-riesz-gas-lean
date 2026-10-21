/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.EllipticRegularity.LocalTesting

/-!
# Changing local weak representatives

The local weak-derivative predicates depend only on almost everywhere
values inside the open domain. In particular, zero extension followed by
passage to an L² class does not change the local equation.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ContDiff Laplacian

namespace Riesz1

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in
/-- Interior scalar test integrals depend only on the local equivalence class. -/
theorem integral_smul_congr_on {U : Set E} (hU : MeasurableSet U)
    {u w : E → F} (huw : u =ᵐ[volume.restrict U] w)
    {b : E → ℝ} (hbU : tsupport b ⊆ U) :
    (∫ x, b x • u x) = ∫ x, b x • w x := by
  apply integral_congr_ae
  filter_upwards [(ae_restrict_iff' hU).mp huw] with x hx
  by_cases hxU : x ∈ U
  · rw [hx hxU]
  · have hb0 := image_eq_zero_of_notMem_tsupport (fun h => hxU (hbU h))
    simp only [hb0, zero_smul]

omit [NormedSpace ℝ F] [CompleteSpace F] in
/-- Local L² membership is invariant under changing the representative. -/
theorem LocallySquareIntegrableOn.congr {U : Set E} {u w : E → F}
    (hu : LocallySquareIntegrableOn U u) (huw : u =ᵐ[volume.restrict U] w) :
    LocallySquareIntegrableOn U w := by
  intro K hK hKU
  exact (memLp_congr_ae (ae_restrict_of_ae_restrict_of_subset hKU huw)).mp (hu K hK hKU)

omit [CompleteSpace F] in
/-- Local weak differentiation is invariant under changing either representative. -/
theorem HasWeakDirectionalDerivativeOn.congr {U : Set E} (hU : IsOpen U)
    {u w g k : E → F} {v : E} (hu : HasWeakDirectionalDerivativeOn U u g v)
    (huw : u =ᵐ[volume.restrict U] w) (hgk : g =ᵐ[volume.restrict U] k) :
    HasWeakDirectionalDerivativeOn U w k v := by
  refine ⟨hu.1.congr huw, hu.2.1.congr hgk, ?_⟩
  intro φ hφ hφc hφU
  rw [← integral_smul_congr_on hU.measurableSet hgk hφU,
    hu.2.2 φ hφ hφc hφU,
    integral_smul_congr_on hU.measurableSet huw
      ((tsupport_fderiv_apply_subset ℝ v).trans hφU)]

omit [CompleteSpace F] in
/-- Local H² uses weak representatives, so null set changes are harmless. -/
theorem IsLocalH2.congr {U : Set E} (hU : IsOpen U) {u w : E → F}
    (hu : IsLocalH2 U u) (huw : u =ᵐ[volume.restrict U] w) : IsLocalH2 U w := by
  obtain ⟨hu, g, h, hderiv⟩ := hu
  refine ⟨hu.congr huw, g, h, ?_⟩
  intro i
  exact ⟨(hderiv i).1, (hderiv i).2.1.congr hU huw Filter.EventuallyEq.rfl,
    (hderiv i).2.2⟩

omit [CompleteSpace F] in
/-- The local Schrödinger equation is unchanged by a null set modification. -/
theorem IsDistributionalSchrodingerSolution.congr {U : Set E} (hU : IsOpen U)
    {W : E → ℝ} {lam : ℝ} {u w : E → F}
    (hu : IsDistributionalSchrodingerSolution U W lam u)
    (huw : u =ᵐ[volume.restrict U] w) : IsDistributionalSchrodingerSolution U W lam w := by
  have hpot : (fun x => (W x + lam) • u x) =ᵐ[volume.restrict U]
      (fun x => (W x + lam) • w x) := huw.mono (fun x hx => congrArg ((W x + lam) • ·) hx)
  refine ⟨hu.1.congr huw, hu.2.1.congr hpot, ?_⟩
  intro φ hφ hφc hφU
  rw [← integral_smul_congr_on hU.measurableSet hpot hφU,
    hu.2.2 φ hφ hφc hφU,
    integral_smul_congr_on hU.measurableSet huw
      ((tsupport_laplacian_subset φ).trans hφU)]

end Riesz1
