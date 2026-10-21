/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Rigidity.GapLawMarginalFibers

/-!
# Log-concavity of the one-offset fiber integral

The Euclidean and coordinate product measures agree under `WithLp.ofLp`.
This permits the explicitly supplied midpoint Prékopa–Leindler statement to
be applied to the actual bounded joint density, and continuity then gives
full concavity of the logarithm.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Riesz1

/-- Assemble the first offset and its Euclidean tail into the ordered coordinates. -/
def gapOffsetEuclideanChart (n : ℕ) :
    (ℝ × EuclideanSpace ℝ (Fin n)) →ₗ[ℝ] (Fin (n + 1) → ℝ) where
  toFun p := Fin.cons p.1 (WithLp.ofLp p.2)
  map_add' p q := by
    ext i
    induction i using Fin.cases with
    | zero => rfl
    | succ i => rfl
  map_smul' a p := by
    ext i
    induction i using Fin.cases with
    | zero => rfl
    | succ i => rfl

/-- The very same joint density, in Euclidean fiber coordinates. -/
def gapOffsetEuclideanDensity (P : Parameters) (n : ℕ)
    (p : ℝ × EuclideanSpace ℝ (Fin n)) : ℝ :=
  extendedAnchoredProbabilityDensity P (n + 1) (gapOffsetEuclideanChart n p)

lemma continuous_gapOffsetEuclideanChart (n : ℕ) : Continuous (gapOffsetEuclideanChart n) := by
  exact (gapOffsetEuclideanChart n).continuous_of_finiteDimensional

lemma measurable_gapOffsetEuclideanDensity (P : Parameters) (n : ℕ) :
    Measurable (gapOffsetEuclideanDensity P n) :=
  (measurable_extendedAnchoredProbabilityDensity P (n + 1)).comp
    (continuous_gapOffsetEuclideanChart n).measurable

lemma gapOffsetEuclideanDensity_nonneg (P : Parameters) (n : ℕ)
    (p : ℝ × EuclideanSpace ℝ (Fin n)) : 0 ≤ gapOffsetEuclideanDensity P n p :=
  extendedAnchoredProbabilityDensity_nonneg P _ _

lemma support_gapOffsetEuclideanDensity (P : Parameters) (n : ℕ) :
    Function.support (gapOffsetEuclideanDensity P n) =
      gapOffsetEuclideanChart n ⁻¹' anchoredDomain (n + 1) :=
  congrArg (Set.preimage _) (support_extendedAnchoredProbabilityDensity P (n + 1))

lemma concaveOn_log_gapOffsetEuclideanDensity (P : Parameters) (n : ℕ) :
    ConcaveOn ℝ (Function.support (gapOffsetEuclideanDensity P n))
      (fun p => Real.log (gapOffsetEuclideanDensity P n p)) := by
  rw [support_gapOffsetEuclideanDensity]
  apply ((concaveOn_log_anchoredProbabilityDensity P (n + 1)).comp_linearMap
    (gapOffsetEuclideanChart n)).congr
  intro p hp
  have hv : gapOffsetEuclideanDensity P n p =
      anchoredProbabilityDensity P (n + 1) (gapOffsetEuclideanChart n p) :=
    Set.indicator_of_mem (show gapOffsetEuclideanChart n p ∈ anchoredDomain (n + 1) from hp) _
  exact congrArg Real.log hv.symm

lemma isBounded_range_gapOffsetEuclideanDensity (P : Parameters) (n : ℕ) :
    Bornology.IsBounded (Set.range (gapOffsetEuclideanDensity P n)) := by
  obtain ⟨C, _, hC⟩ := exists_gapOffsetJointDensity_bound P n
  apply (isCompact_Icc (a := (0 : ℝ)) (b := C)).isBounded.subset
  rintro _ ⟨p, rfl⟩
  exact ⟨gapOffsetEuclideanDensity_nonneg P n p, hC (p.1, WithLp.ofLp p.2)⟩

lemma isBounded_support_gapOffsetEuclideanDensity (P : Parameters) (n : ℕ) :
    Bornology.IsBounded (Function.support (gapOffsetEuclideanDensity P n)) := by
  let K : Set (Fin n → ℝ) := Set.univ.pi fun _ => Icc (0 : ℝ) 1
  have hK : IsCompact K := isCompact_univ_pi fun _ => isCompact_Icc
  have himage : IsCompact ((WithLp.toLp 2) '' K) :=
    hK.image (PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ))
  apply (isCompact_Icc.prod himage).isBounded.subset
  intro p hp
  have hmem : gapOffsetEuclideanChart n p ∈ anchoredDomain (n + 1) :=
    (Set.ext_iff.mp (support_gapOffsetEuclideanDensity P n) p).mp hp
  have hcons := (mem_anchoredDomain_cons_iff n p.1 (WithLp.ofLp p.2)).mp hmem
  refine ⟨⟨hcons.1.1.le, hcons.1.2.le⟩, ?_⟩
  refine ⟨WithLp.ofLp p.2, ?_, WithLp.toLp_ofLp 2 p.2⟩
  intro i _
  exact ⟨(hcons.2.1.1 i).1.le, (hcons.2.1.1 i).2.le⟩

lemma integral_gapOffsetEuclideanDensity (P : Parameters) (n : ℕ) (r : ℝ) :
    (∫ z : EuclideanSpace ℝ (Fin n), gapOffsetEuclideanDensity P n (r, z)) =
      gapOffsetMarginalDensity P n r := by
  exact (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin n)).integral_comp'
    (fun z => gapOffsetJointDensity P n (r, z))

/-- Full log-concavity of the actual positive continuous fiber integral for `N ≥ 3`. -/
theorem concaveOn_log_gapOffsetMarginalDensity (hPL : External.PrekopaLeindler)
    (P : Parameters) (n : ℕ) (hn : 0 < n) :
    ConcaveOn ℝ (Ioo (0 : ℝ) 1) (fun r => Real.log (gapOffsetMarginalDensity P n r)) := by
  have heq : (fun r => ∫ z : EuclideanSpace ℝ (Fin n), gapOffsetEuclideanDensity P n (r, z)) =
      gapOffsetMarginalDensity P n := funext (integral_gapOffsetEuclideanDensity P n)
  have hc := marginal_concaveOn_log_of_continuous hPL n hn (gapOffsetEuclideanDensity P n)
    (measurable_gapOffsetEuclideanDensity P n) (gapOffsetEuclideanDensity_nonneg P n)
    (isBounded_range_gapOffsetEuclideanDensity P n) (isBounded_support_gapOffsetEuclideanDensity P n)
    (concaveOn_log_gapOffsetEuclideanDensity P n) (Ioo (0 : ℝ) 1) (convex_Ioo _ _)
    (by intro r hr; rw [integral_gapOffsetEuclideanDensity]; exact gapOffsetMarginalDensity_pos P n hr)
    (by rw [heq]; exact continuousOn_gapOffsetMarginalDensity P n)
  apply hc.congr
  intro r _
  exact congrArg Real.log (integral_gapOffsetEuclideanDensity P n r)

end Riesz1

end
end
