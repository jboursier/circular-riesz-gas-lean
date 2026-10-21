/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.QuotientChartWeakGradient
public import Riesz1.ToMathlib.CompactLipschitzZeroExtension

/-!
# Compact quotient cutoffs and their periodic zero extensions

Every compactly supported real Lipschitz function on the actual quotient
has a globally Lipschitz periodic lift supported in the chamber. This
justifies quantification over quotient cutoffs.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory
open scoped NNReal

namespace Riesz1

/-- The chamber is saturated under the quotient projection. -/
theorem hsQuotient_mk_mem_configuration_iff {N : ℕ+} (x : HsEuclidean N) :
    (QuotientAddGroup.mk x : HsCylinder N) ∈ HsConfiguration N ↔ x ∈ hsChamber N := by
  constructor
  · rintro ⟨y, hy, hq⟩
    obtain ⟨k, hk⟩ := (hsPeriodLattice_mem_iff _).mp (QuotientAddGroup.eq_iff_sub_mem.mp hq)
    have hxy : x = hsTranslate (-(k : ℝ)) y := by
      ext i
      have hi := hk i
      change y i - x i = (k : ℝ) at hi
      change x i = y i + -(k : ℝ)
      linarith
    rw [hxy, hsTranslate_mem_chamber_iff]
    exact hy
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- Every compactly supported Lipschitz quotient cutoff has its
canonical periodic interior zero extension on the Euclidean cover. -/
theorem exists_hsQuotient_cutoff_lift {N : ℕ+} {b : HsConfiguration N → ℝ} {C : ℝ≥0}
    (hb : LipschitzWith C b) (hbc : HasCompactSupport b) :
    ∃ (B : HsEuclidean N → ℝ) (D : ℝ≥0), LipschitzWith D B ∧
      (∀ (j : ℤ) x, B (hsTranslate (j : ℝ) x) = B x) ∧
      tsupport B ⊆ hsChamber N ∧
      (∀ x : hsChamber N, B x.val = b (hsChamberProjection x)) ∧
      (∀ x : HsConfiguration N, B (hsLiftPoint N x) = b x) ∧
      (∀ x ∉ hsChamber N, B x = 0) := by
  obtain ⟨F, D, hF, hFx, hFz, _, hFU⟩ :=
    exists_lipschitz_zeroExtension (isOpen_hsConfiguration N) hb hbc
  let B := fun x : HsEuclidean N => F (QuotientAddGroup.mk x)
  have hmk : LipschitzWith 1 (QuotientAddGroup.mk : HsEuclidean N → HsCylinder N) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [NNReal.coe_one, one_mul, dist_eq_norm]
    change ‖(QuotientAddGroup.mk (x - y) : HsCylinder N)‖ ≤ ‖x - y‖
    exact QuotientAddGroup.norm_mk_le_norm
  refine ⟨B, D, by simpa only [mul_one, Function.comp_def, B] using hF.comp hmk,
    fun j x => congrArg F (Internal.hs_quotient_mk_translate j x), ?_,
    fun x => hFx (hsChamberProjection x), ?_, ?_⟩
  · intro x hx
    apply (hsQuotient_mk_mem_configuration_iff x).mp
    exact hFU (tsupport_comp_subset_preimage F QuotientAddGroup.continuous_mk hx)
  · intro x
    change F (QuotientAddGroup.mk (hsLiftPoint N x)) = b x
    have hq : (QuotientAddGroup.mk (hsLiftPoint N x) : HsCylinder N) = x.val :=
      congrArg Subtype.val (hsChamberProjection_liftPoint x)
    rw [hq]
    exact hFx x
  · intro x hx
    exact hFz _ (fun h => hx ((hsQuotient_mk_mem_configuration_iff x).mp h))

end Riesz1
