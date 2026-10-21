/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Rigidity.RigidityBlocksGeometry
public import Riesz1.Rigidity.RigidityBlocksComparison
public import Riesz1.Rigidity.RigidityBlocksLinear

/-!
# A nonasymptotic local block-difference estimate

Supporting the local case of the block estimate of Theorem 1:
the centered tail is transferred
to the original law, after the uniform mean bound removes centering.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Riesz1.Internal

/-- Before the final choice of threshold, the local argument gives this
explicit tail bound. `C` is chosen before the cutoff and all block data.
This is an internal estimate, not the complete block estimate of Theorem 1. -/
theorem rigidityBlocks_local_tail (P : Parameters) {γ : ℝ} (hγ : 0 < γ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (_hBE : External.BakryEmery)
      (_hPL : External.PrekopaLeindler) (N : ℕ+) (_hN : 2 ≤ (N : ℕ))
      (θ : ℝ → ℝ), IsForcingCutoff θ → ∀ (i : ℤ) (k : ℕ),
      1 ≤ k → 3 * k < (N : ℕ) → ∀ v : ℝ, 0 < v → 2 * C ≤ v →
      (gibbsMeasure P N).real {X | v ≤ |centeredBlockDiff X i k|} ≤
        2 * Real.exp (-(P.val.1 * rigidityCurvatureConstant (parametersExponent P).val *
            (3 * (k : ℝ) + 1) * (2 * k + 1) * v ^ 2) /
          (32 * (((3 * k : ℕ) : ℝ) ^ (1 + γ)) ^ ((parametersExponent P).val + 2))) +
        3 * Real.exp (-blockMomentExponent * (k : ℝ) ^ γ) := by
  obtain ⟨C, hC, hm⟩ := centeredBlockDiff_constrained_mean_bound P hγ
  refine ⟨C, hC, ?_⟩
  intro hBE hPL N hN θ hθ i k hk hkN v hv hlarge
  let R := ((3 * k : ℕ) : ℝ) ^ (1 + γ)
  let Q := constrainedLaw P N θ (i - k) (3 * k) R
  let a := ∫ X, centeredBlockDiff X i k ∂Q
  have hkr : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hL : (1 : ℝ) ≤ (3 * k : ℕ) := by exact_mod_cast (show 1 ≤ 3 * k by omega)
  have hR : 1 ≤ R := Real.one_le_rpow hL (by linarith)
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  let _ : IsProbabilityMeasure Q := isProbabilityMeasure_constrainedLaw P N hθ hRpos (i - k) (3 * k)
  have hmean : |a| ≤ C := hm hPL N hN θ hθ i k hk hkN
  have hevent : {X : Configuration N | v ≤ |centeredBlockDiff X i k|} ⊆
      {X | v / 2 ≤ |centeredBlockDiff X i k - a|} := by
    intro X hX
    have htri : |centeredBlockDiff X i k| ≤ |centeredBlockDiff X i k - a| + |a| := by
      simpa only [sub_add_cancel] using abs_add_le (centeredBlockDiff X i k - a) a
    change v ≤ |centeredBlockDiff X i k| at hX
    change v / 2 ≤ |centeredBlockDiff X i k - a|
    linarith
  have htail := rigidityBlocks_local_centered_tail hBE hPL P N i hkN hθ hR
    (show 0 < v / 2 by linarith)
  change Q.real {X | v / 2 ≤ |centeredBlockDiff X i k - a|} ≤ _ at htail
  have hNpos : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hmpos : (0 : ℝ) < 2 * (k : ℝ) + 1 := by positivity
  have hp : 0 < R ^ ((parametersExponent P).val + 2) := Real.rpow_pos_of_pos hRpos _
  have hexp : -(P.val.1 * rigidityCurvatureConstant (parametersExponent P).val *
          (N : ℝ) ^ 2 * (3 * (k : ℝ) + 1) * (v / 2) ^ 2) /
        (2 * R ^ ((parametersExponent P).val + 2) *
          (2 * (N : ℝ) * Real.sqrt (2 * k + 1) / (2 * k + 1)) ^ 2) =
      -(P.val.1 * rigidityCurvatureConstant (parametersExponent P).val *
          (3 * (k : ℝ) + 1) * (2 * k + 1) * v ^ 2) /
        (32 * R ^ ((parametersExponent P).val + 2)) := by
    rw [rigidityBlocks_gradient_bound_sq]
    field_simp
    ring
  rw [hexp] at htail
  have ht := rigidityBlocks_tail_transfer hPL P N hN hθ (i - k) i
    (by omega : 0 < 3 * k) hkN γ k v
  have herr : 3 * Real.exp (-blockMomentExponent * ((3 * k : ℕ) : ℝ) ^ γ) ≤
      3 * Real.exp (-blockMomentExponent * (k : ℝ) ^ γ) := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Real.exp_le_exp.mpr
    have hpow := Real.rpow_le_rpow hkr.le
      (show (k : ℝ) ≤ ((3 * k : ℕ) : ℝ) by push_cast; linarith) hγ.le
    nlinarith [blockMomentExponent_pos]
  exact ht.trans (add_le_add ((measureReal_mono hevent).trans htail) herr)

end Riesz1.Internal

end
