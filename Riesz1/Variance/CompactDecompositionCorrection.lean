/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.PeriodicScaledMarkCutoff
public import Riesz1.Variance.VarAlPiecesEnvelopeCompact
public import Riesz1.Auxiliary.GradientSplittingZWeights
public import Riesz1.ToMathlib.PeriodicDerivativeReconstruction

/-!
# A common period-integral correction on every observation circle

Supporting the compact reduction in Proposition 5.9.
The existing fixed bump has period integral bounded below independently
of the circumference. Its value and derivative satisfy both transport
envelopes about every fixed mark, with no separation requirement.
-/

public section

open MeasureTheory Set Filter
open scoped ContDiff BigOperators

namespace Riesz1.Internal

/-- A single correction function, supported near the origin, works on
every circle of length at least one and about every fixed marked center.
All quantitative bounds precede the circle and microscopic scale. -/
theorem compactDecomposition_correction (n : ℕ) (marks : Fin n → ℝ)
    {s b : ℝ} (hs : s < 1) (hb : 0 ≤ b) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L K : ℝ), 1 ≤ L → 1 ≤ K →
      ∃ u : ℝ → ℝ, ContDiff ℝ ∞ u ∧ Function.Periodic u L ∧
        (1 / 4 ≤ ∫ t in (0 : ℝ)..L, u t) ∧
        (∀ x, 0 ≤ u x) ∧
        (∀ (j : Fin (n + 1)) x,
          |u x| ≤ C * gradWeightOne s b K L (x - Fin.lastCases 0 marks j) ∧
          |deriv u x| ≤ C * gradWeightTwo s b K L (x - Fin.lastCases 0 marks j)) := by
  classical
  let r : ℝ := 1 / 8
  have hr : 0 < r := by norm_num [r]
  obtain ⟨M, _, hM, _⟩ := exists_bounds_deriv_bump (contDiff_cutoffBump r)
    (fun x hx => cutoffBump_eq_zero hr hx)
  let R : ℝ := 2 + ∑ i, |marks i|
  have hR : 2 ≤ R := by
    dsimp [R]
    linarith [Finset.sum_nonneg (s := Finset.univ) (fun i _ => abs_nonneg (marks i))]
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  let C := (1 + M) * (1 + R ^ (3 - s))
  have hC : 0 < C := by dsimp [C]; positivity
  have hbound₁ : 1 ≤ C := by dsimp [C]; nlinarith [Real.rpow_nonneg (by linarith : 0 ≤ R) (3 - s)]
  have hbound₂ : M ≤ C := by dsimp [C]; nlinarith [Real.rpow_nonneg (by linarith : 0 ≤ R) (3 - s)]
  have hRpow : R ^ (2 - s) ≤ R ^ (3 - s) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hbound₃ : R ^ (2 - s) ≤ C := by
    dsimp [C]
    nlinarith [Real.rpow_nonneg (by linarith : 0 ≤ R) (3 - s)]
  have hbound₄ : M * R ^ (3 - s) ≤ C := by
    dsimp [C]
    nlinarith [Real.rpow_nonneg (by linarith : 0 ≤ R) (3 - s)]
  refine ⟨C, hC, fun L K hL hK => ?_⟩
  have hL0 : 0 < L := by linarith
  have hroom : 4 * r < L := by dsimp [r]; linarith
  let u := markCut (cutoffBump r) L 0
  have hu : ContDiff ℝ ∞ u := contDiff_markCut_cutoffBump hL0 hr hroom 0
  have hup : Function.Periodic u L := markCut_add_period hL0 0
  have hun (x : ℝ) : 0 ≤ u x := (cutoffBump_mem_Icc r _).1
  have huv (x : ℝ) : |u x| ≤ 1 := by
    rw [abs_of_nonneg (hun x)]
    exact (cutoffBump_mem_Icc r _).2
  have hud (x : ℝ) : |deriv u x| ≤ M :=
    abs_deriv_markCut_le (fun x hx => cutoffBump_eq_zero hr hx) hL0 hroom hM 0 x
  have hmass : 1 / 4 ≤ ∫ t in (0 : ℝ)..L, u t := by
    have hshift := hup.intervalIntegral_add_eq (-(L / 2)) 0
    rw [show -(L / 2) + L = L / 2 by ring, zero_add] at hshift
    rw [← hshift, intervalIntegral.integral_of_le (by linarith : -(L / 2) ≤ L / 2)]
    have hsub : Ioc (-r) r ⊆ Ioc (-(L / 2)) (L / 2) := by
      intro x hx
      constructor <;> dsimp [r] at * <;> linarith [hx.1, hx.2]
    have hsmall : (∫ t in Ioc (-r) r, u t) = 2 * r := by
      calc
        _ = ∫ _t in Ioc (-r) r, (1 : ℝ) := by
          apply setIntegral_congr_fun measurableSet_Ioc
          intro x hx
          apply cutoffBump_eq_one
          change circDist L (x - 0) ≤ r
          exact (circDist_le_abs' hL0 _).trans (by
            rw [sub_zero, abs_le]
            exact ⟨hx.1.le, hx.2⟩)
        _ = 2 * r := by simp [hr.le]; ring
    have hh := setIntegral_mono_set
      (hu.continuous.intervalIntegrable (μ := volume) (-(L / 2)) (L / 2)).1
      (ae_of_all _ hun) (ae_of_all _ hsub)
    rw [hsmall] at hh
    simpa only [r, mul_one_div, show (2 : ℝ) / 8 = 1 / 4 by norm_num] using hh
  have hcenter (j : Fin (n + 1)) : |Fin.lastCases 0 marks j| ≤ R - 2 := by
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp only [Fin.lastCases_last, abs_zero]; linarith
    · simp only [Fin.lastCases_castSucc]
      dsimp [R]
      simpa only [add_sub_cancel_left] using Finset.single_le_sum
        (f := fun i => |marks i|) (fun i _ => abs_nonneg _) (Finset.mem_univ i)
  have htail (j : Fin (n + 1)) (x : ℝ)
      (hx : R ≤ circDist L (x - Fin.lastCases 0 marks j)) : u x = 0 ∧ deriv u x = 0 := by
    have hdist : circDist L (x - Fin.lastCases 0 marks j) ≤
        circDist L x + |Fin.lastCases 0 marks j| := by
      simpa only [sub_sub_cancel_left, abs_neg] using
        circDist_le_add_abs hL0 (x - Fin.lastCases 0 marks j) x
    have hx' : 2 * r < circDist L (x - 0) := by dsimp [r]; rw [sub_zero]; linarith [hcenter j]
    have he := eventually_markCut_eq_zero hL0 (fun x hx => cutoffBump_eq_zero hr hx) 0 x hx'
    exact ⟨he.self_of_nhds, (deriv_deriv_eq_zero_of_eventually_const he).1⟩
  refine ⟨u, hu, hup, hmass, hun, fun j x => ⟨?_, ?_⟩⟩
  · exact weighted_remainder_bound (circDist_nonneg _ _) hR (by linarith : s < 2)
      (fun hx => one_le_weight_of_lt hx hK (by linarith : -b ≤ 0)) (huv x)
      (fun hx => by rw [(htail j x hx).1, abs_zero, zero_mul])
      (by simpa using hbound₃) hbound₁ (by linarith : (0 : ℝ) ≤ C) hC.le
  · unfold gradWeightTwo
    rw [show -(1 + b) = -1 - b by ring]
    exact weighted_remainder_bound (circDist_nonneg _ _) hR (by linarith : s < 3)
      (fun hx => one_le_weight_of_lt hx hK (by linarith : -1 - b ≤ 0)) (hud x)
      (fun hx => by rw [(htail j x hx).2, abs_zero, zero_mul])
      hbound₄ hbound₂ (by linarith : (0 : ℝ) ≤ C) hC.le

end Riesz1.Internal
