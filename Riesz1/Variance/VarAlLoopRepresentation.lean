/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.APrioriBoundEnergy
public import Riesz1.Variance.VarAlLoopPowers

/-!
# Combining the three inverse energies for the loop

The representation and elementary absorption steps of Proposition 5.9.
The analytic Sobolev premise remains explicit in this internal helper.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Riesz1.Internal

/-- Proposition 5.9, equation (5.28), for an actual Sobolev
gradient split into its singular, gap, and cutoff fields. -/
theorem varAlLoop_variance_le_three_energies_of_h1 {n : ℕ} {c : ℝ}
    (χ : HsPairPotentials n.succPNat c) (hc : 0 < c)
    (hPL : External.PrekopaLeindler) (hn : 0 < n) {C : ℝ} (hadm : HsAdmissible χ C)
    {F : AnchoredEuclidean n → ℝ}
    {v w d : AnchoredEuclidean n → AnchoredEuclidean n}
    (hv : MemLp v 2 (anchoredMeasureE χ)) (hw : MemLp w 2 (anchoredMeasureE χ))
    (hd : MemLp d 2 (anchoredMeasureE χ))
    (hH : IsAnchoredH1 χ F (fun y => v y + w y + d y)) :
    ProbabilityTheory.variance F (anchoredMeasureE χ) ≤
      4 * anchoredInverseEnergy χ hc (hv.toLp v) +
      4 * anchoredInverseEnergy χ hc (hw.toLp w) +
      2 * anchoredInverseEnergy χ hc (hd.toLp d) := by
  have := isProbabilityMeasure_anchoredMeasureE χ hc
  have hF : MemLp F 2 (anchoredMeasureE χ) := hH.1
  have hg : MemLp (fun y => v y + w y + d y) 2 (anchoredMeasureE χ) := (hv.add hw).add hd
  let S : AnchoredSobolev χ := ⟨(hF.toLp F, hg.toLp _),
    WeightedSobolev.IsWeightedH1.congr hH hF.coeFn_toLp.symm hg.coeFn_toLp.symm⟩
  have hgrad : S.val.2 = hv.toLp v + hw.toLp w + hd.toLp d := by
    change ((hv.add hw).add hd).toLp _ = _
    rw [(hv.add hw).toLp_add hd, hv.toLp_add hw]
  have hvar : ProbabilityTheory.variance F (anchoredMeasureE χ) =
      ProbabilityTheory.variance S.val.1 (anchoredMeasureE χ) :=
    ProbabilityTheory.variance_congr hF.coeFn_toLp.symm
  rw [hvar, anchored_variance_eq_inverseEnergy χ hc hPL hn hadm S, hgrad]
  exact (anchoredInverse_symmetry_positivity_subadditivity χ hc).2.2.2.2 _ _ _

/-- The two field estimates and negligible cutoff energy give a single
power bound, uniformly down to `K = 1`. -/
theorem varAlLoop_combine_energies {K b q Cv Cw Cd V Ev Ew Ed : ℝ}
    (hK : 1 ≤ K) (hq : 0 ≤ q) (hCd : 0 ≤ Cd)
    (hV : V ≤ 4 * Ev + 4 * Ew + 2 * Ed)
    (hv : Ev ≤ Cv * K ^ q * (K + K ^ (2 * b)))
    (hw : Ew ≤ Cw * K ^ q * (K + K ^ (2 * b)))
    (hd : Ed ≤ Cd * K ^ (-10 : ℝ)) :
    V ≤ (4 * Cv + 4 * Cw + 2 * Cd) * K ^ q * (K + K ^ (2 * b)) := by
  have hp : 1 ≤ K ^ q := Real.one_le_rpow hK hq
  have hb : 0 ≤ K ^ (2 * b) := Real.rpow_nonneg (by linarith) _
  have hr : K ^ (-10 : ℝ) ≤ K ^ q * (K + K ^ (2 * b)) := by
    calc
      _ ≤ K ^ (0 : ℝ) := Real.rpow_le_rpow_of_exponent_le hK (by linarith)
      _ = 1 := Real.rpow_zero _
      _ ≤ K ^ q * (K + K ^ (2 * b)) := by
        calc
          (1 : ℝ) = 1 * 1 := by ring
          _ ≤ _ := mul_le_mul hp (by linarith) zero_le_one (by positivity)
  have hd' := hd.trans (mul_le_mul_of_nonneg_left hr hCd)
  nlinarith

end Riesz1.Internal

end
