/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.VarAlAssemblySobolev
public import Riesz1.ToMathlib.WeightedSobolev.BoundedGradientCutoff

/-!
# A locally smooth coefficient times an anchored Sobolev cutoff

Only the closure of the nonzero cutoff inside the physical simplex
matters. A smooth extension near that closed set and locality on the
zero level prove the product rule in the actual completion.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set Topology
open scoped ContDiff

namespace Riesz1.Internal

/-- A local coefficient can multiply the cutoff without any hypotheses
on its values outside the physical relative support. -/
theorem varAlAssembly_mul_local {n : ℕ} {c : ℝ}
    (Q : HsPairPotentials n.succPNat c) (hc : 0 < c)
    {η H : AnchoredEuclidean n → ℝ} (hη : IsAnchoredH1 Q η (gradient η))
    {M : ℝ} (hM : 0 ≤ M) (hbη : ∀ᵐ y ∂anchoredMeasureE Q, |η y| ≤ M)
    {O : Set (AnchoredEuclidean n)} (hO : IsOpen O)
    (hSO : closure {y | y ∈ anchoredSimplex n ∧ η y ≠ 0} ⊆ O)
    (hH : ContDiffOn ℝ ∞ H O) :
    IsAnchoredH1 Q (fun y => η y * H y)
      (fun y => η y • gradient H y + H y • gradient η y) := by
  have := isProbabilityMeasure_anchoredMeasureE Q hc
  let A := closure {y | y ∈ anchoredSimplex n ∧ η y ≠ 0}
  obtain ⟨F, hF, hFH⟩ := WeightedSobolev.exists_contDiff_eventuallyEq isClosed_closure hO hSO hH
  have hFh : IsAnchoredH1 Q F (gradient F) :=
    WeightedSobolev.isWeightedH1_of_smoothNearClosure
      (isBounded_anchoredSimplex n) (ae_mem_anchoredSimplex Q)
      ⟨univ, isOpen_univ, subset_univ _, hF.contDiffOn⟩
  obtain ⟨D, hD⟩ := (isBounded_anchoredSimplex n).isCompact_closure.exists_bound_of_continuousOn
    hF.continuous.continuousOn
  have hbF : ∀ᵐ y ∂anchoredMeasureE Q, |F y| ≤ max 0 D := by
    filter_upwards [ae_mem_anchoredSimplex Q] with y hy
    exact (hD y (subset_closure hy)).trans (le_max_right _ _)
  have hp := WeightedSobolev.IsWeightedH1.mul_of_bound (isBounded_anchoredSimplex n)
    (ae_mem_anchoredSimplex Q) hη hFh hM (le_max_left _ _) hbη hbF
  have hzero := hη.gradient_eq_zero_on_level Q hc 0
  apply hp.congr
  · filter_upwards [ae_mem_anchoredSimplex Q] with y hy
    by_cases hηy : η y = 0
    · simp only [hηy, zero_mul]
    · rw [(hFH y (subset_closure ⟨hy, hηy⟩)).eq_of_nhds]
  · filter_upwards [ae_mem_anchoredSimplex Q, hzero] with y hy hz
    by_cases hηy : η y = 0
    · simp only [hηy, hz hηy, zero_smul, smul_zero, add_zero]
    · have he := hFH y (subset_closure ⟨hy, hηy⟩)
      rw [he.eq_of_nhds, he.gradient_eq]

end Riesz1.Internal

end
