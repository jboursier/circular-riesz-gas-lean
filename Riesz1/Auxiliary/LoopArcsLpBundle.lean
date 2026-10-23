/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopMoments
public import Riesz1.Auxiliary.LoopArcsLpMoments
public import Riesz1.Auxiliary.LoopArcsLpMeasure

/-!
# Discrepancy moments of the arc counts from the rigidity bundle

The moments part of Lemma B.2, the discrepancy clause, in the form used by the cell
estimate of the arcs part of Lemma B.2: for every `p ≥ 1` there are `δ ∈ (0, 1/4)` and `M ≥ 0`
such that, for every `N ≥ 2`, every arc endpoint `a` and every arclength `0 < u ≤ N/2`,

`∫ |loopCount(a, u) - u|^{2p} dμ_N ≤ (M (1 + u)^{s/2+δ})^{2p}`.

The statement is conditional on the rigidity conclusion and takes the Prékopa–Leindler inequality
`External.PrekopaLeindler` as an explicit hypothesis, as the bundle does. The constant
`δ` is `min(s/2, ε₀)/2` for the threshold `ε₀` of the bundle.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Riesz1

/-- **Discrepancy moments of the arc counts**, conditional on the rigidity conclusion. For `p ≥ 1`
there are `δ ∈ (0, 1/4)` and `M ≥ 0` with the moment bound for every `N ≥ 2`, `a` and
`0 < u ≤ N/2`. -/
theorem loopArc_moment_of_rigidity (beta s : ℝ) (hbeta : 0 < beta) (hs : 0 < s) (hs1 : s < 1)
    (hRig : Internal.RigidityConclusion beta s hbeta hs hs1) (p : ℝ) (hp : 1 ≤ p) :
    ∃ δ M : ℝ, 0 < δ ∧ δ < 1 / 4 ∧ 0 ≤ M ∧
      ∀ (_hPL : External.PrekopaLeindler) (N : ℕ+), 2 ≤ (N : ℕ) → ∀ a u : ℝ,
        0 < u → u ≤ (N : ℝ) / 2 →
          ∫⁻ X, ‖loopCount a u X - u‖ₑ ^ (2 * p)
              ∂(gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N)
            ≤ ENNReal.ofReal (M * (1 + u) ^ (s / 2 + δ)) ^ (2 * p) := by
  obtain ⟨hcount, -, -, hdisc⟩ := Internal.auxiliary_Loop_moments_of_rigidity beta s hbeta hs hs1 hRig
  obtain ⟨eps0, heps0, hdiscδ⟩ := hdisc
  set δ : ℝ := min (s / 2) eps0 / 2 with hδ
  have hmin : 0 < min (s / 2) eps0 := lt_min (by linarith) heps0
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hδ1 : δ < 1 / 4 := by
    have : min (s / 2) eps0 ≤ s / 2 := min_le_left _ _
    rw [hδ]
    linarith
  have hδlt : δ < min (s / 2) eps0 := by rw [hδ]; linarith
  obtain ⟨⟨Cd, hCd, hdiscC⟩, -⟩ := hdiscδ δ hδ0 hδlt (2 * p) (by linarith)
  obtain ⟨Cc, hCc, hcountC⟩ := hcount (2 * p) (by linarith)
  refine ⟨δ, max Cd (2 * Cc + 1), hδ0, hδ1, le_trans (by linarith [hCc]) (le_max_right _ _), ?_⟩
  intro hPL N hN a u hu0 huN
  have : IsProbabilityMeasure (gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N) :=
    (modelWellDefined _ N).2.2
  set μ := gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N with hμ
  set σ : ℝ := s / 2 + δ with hσ
  have hσ0 : 0 ≤ σ := by rw [hσ]; linarith
  have hM1 : 0 ≤ max Cd (2 * Cc + 1) := le_trans (by linarith) (le_max_right _ _)
  -- the `eLpNorm` bound for the centred count, in two ranges of `u`
  have hbound : eLpNorm (fun X : Configuration N => loopCount a u X - u) (ENNReal.ofReal (2 * p)) μ
      ≤ ENNReal.ofReal (max Cd (2 * Cc + 1) * (1 + u) ^ σ) := by
    by_cases hu1 : 1 ≤ u
    · have hdN := hdiscC hPL N hN a u hu1 huN
      have hfun : (fun X : Configuration N => loopCount a u X - u)
          = fun X : Configuration N => loopDiscrepancy a u X := by
        funext X
        rw [loopDiscrepancy_eq_sub a u X hu0.le (by linarith)]
      rw [hfun]
      refine le_trans hdN (ENNReal.ofReal_le_ofReal ?_)
      have hrpow : u ^ σ ≤ (1 + u) ^ σ := Real.rpow_le_rpow (by linarith) (by linarith) hσ0
      have hCd' : Cd * u ^ σ ≤ max Cd (2 * Cc + 1) * (1 + u) ^ σ :=
        mul_le_mul (le_max_left _ _) hrpow (Real.rpow_nonneg hu0.le _) (le_trans hCd.le
          (le_max_left _ _))
      rw [hσ] at hCd'
      exact hCd'
    · have hcnt := hcountC hPL N hN a u hu0 (by linarith)
      have hmeas : Measurable (fun X : Configuration N => loopCount a u X) :=
        measurable_loopCount_of (N := N) (c := id) (a := fun _ => a) (r := fun _ => u)
          measurable_const measurable_const measurable_id
      have hconst : eLpNorm (fun _ : Configuration N => u) (ENNReal.ofReal (2 * p)) μ
          = ENNReal.ofReal u := by
        rw [eLpNorm_const u (ENNReal.ofReal_pos.mpr (by linarith)).ne'
          (IsProbabilityMeasure.ne_zero μ)]
        simp [Real.enorm_eq_ofReal hu0.le, measure_univ]
      have hneg : eLpNorm (fun X : Configuration N => loopCount a u X - u)
          (ENNReal.ofReal (2 * p)) μ ≤ eLpNorm (fun X : Configuration N => loopCount a u X)
            (ENNReal.ofReal (2 * p)) μ + eLpNorm (fun _ : Configuration N => u)
            (ENNReal.ofReal (2 * p)) μ :=
        eLpNorm_sub_le (f := fun X : Configuration N => loopCount a u X)
          (g := fun _ : Configuration N => u) (ENNReal.one_le_ofReal.mpr (by linarith))
      refine le_trans hneg (le_trans (add_le_add hcnt (le_of_eq hconst)) ?_)
      have hu1' : u ≤ 1 := le_of_lt (not_le.mp hu1)
      rw [← ENNReal.ofReal_add (mul_nonneg hCc.le (by linarith)) hu0.le]
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 : 1 ≤ (1 + u) ^ σ := Real.one_le_rpow (by linarith) hσ0
      have h2 : 2 * Cc + 1 ≤ max Cd (2 * Cc + 1) := le_max_right _ _
      have h3 : max Cd (2 * Cc + 1) ≤ max Cd (2 * Cc + 1) * (1 + u) ^ σ :=
        le_mul_of_one_le_right hM1 h1
      have h4 : Cc * (1 + u) + u ≤ 2 * Cc + 1 := by
        nlinarith [mul_le_mul_of_nonneg_left hu1' hCc.le]
      linarith
  -- convert the `eLpNorm` bound to the lower integral
  have hlin := lintegral_enorm_rpow_le_of_eLpNorm (μ := μ) (q := 2 * p)
    (c := max Cd (2 * Cc + 1) * (1 + u) ^ σ) (by linarith) hbound
  exact hlin

end Riesz1

end
end
