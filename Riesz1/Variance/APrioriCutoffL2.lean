/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.APrioriCutoffAnchored
public import Riesz1.Variance.APrioriGoodProbability

/-!
# The anchored cutoff in `L²`

The anchored cutoff estimate in the proof of Lemma 5.2 has two conclusions. This file proves the
second one: for every function `T` with `|T| ≤ M K^D` everywhere,
`‖(1 - η*) T‖_{L²(dGi*)} ≤ C K^{-b}`, where `dGi* = Anch_N # dGi` and `K = N ℓ`.

The proof has three steps.

* The anchored cutoff lies in `[0, 1]` and equals `1` off the bad set `S = {η* ≠ 1}`. Hence
  `|(1 - η*) T| ≤ M K^D 𝟙_S` pointwise.
* The bad set has `dGi*`-mass `dGi(η ≠ 1)`, by the bridge `anchoredCutoff_anchorMap`.
* The probability estimate of the good event in the proof of Lemma 5.2
  (`goodCutoff_prob_le_of_rigidity`) with the exponent `B = 2 (D + b)` gives
  `dGi(η ≠ 1) ≤ C_B K^{-B}`. Taking square roots yields the claim.

The rigidity conclusion is the hypothesis `Riesz1.Internal.RigidityConclusion`, and the
Prékopa–Leindler inequality is the explicit argument `External.PrekopaLeindler`. The first
conclusion (the inverse-energy bound) is not proved in this file.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Riesz1.Internal

/-- **Second conclusion of the anchored cutoff estimate in the proof of Lemma 5.2.**
Conditionally on the rigidity
conclusion at `(β, s)`, for `0 < s < 1`, `β > 0`, `γ > 1`, `ε > 0` and `D, M, b > 0`, there is
`C > 0` such that: given the Prékopa–Leindler inequality `External.PrekopaLeindler`, for every
`N ≥ 2` and every `ℓ` with `0 < ℓ ≤ 1` and `K = N ℓ ≥ 1`, and every function `T` with
`|T| ≤ M K^D` everywhere, the `L²(dGi*)`-norm of `(1 - η*) T` is at most `C K^{-b}`. Here `dGi*` is
the image of the Gibbs law
under `Anch_N` and `η*` is the anchored cutoff. -/
theorem anchoredCutoff_L2_of_rigidity (beta s : ℝ) (hbeta : 0 < beta) (hs : 0 < s) (hs1 : s < 1)
    (hRig : Riesz1.Internal.RigidityConclusion beta s hbeta hs hs1) (γ ε : ℝ) (hγ : 1 < γ)
    (hε : 0 < ε) (D M b : ℝ) (hD : 0 < D) (hM : 0 < M) (hb : 0 < b) :
    ∃ C : ℝ, 0 < C ∧ ∀ (_hPL : External.PrekopaLeindler) (N : ℕ+) (ℓ : ℝ),
      2 ≤ (N : ℕ) → 0 < ℓ → ℓ ≤ 1 → 1 ≤ ((N : ℕ) : ℝ) * ℓ →
      ∀ T : (Fin ((N : ℕ) - 1) → ℝ) → ℝ, Measurable T →
        (∀ y, |T y| ≤ M * (((N : ℕ) : ℝ) * ℓ) ^ D) →
        eLpNorm (fun y => (1 - anchoredCutoff N s (((N : ℕ) : ℝ) * ℓ) γ ε y) * T y) 2
            ((gibbsMeasure ⟨(beta, s), hbeta, hs, hs1⟩ N).map (anchorMap N))
          ≤ ENNReal.ofReal (C * (((N : ℕ) : ℝ) * ℓ) ^ (-b)) := by
  have hB : (0 : ℝ) < 2 * (D + b) := by linarith
  obtain ⟨CB, hCB, hprob⟩ :=
    goodCutoff_prob_le_of_rigidity beta s hbeta hs hs1 hRig γ ε hγ hε (2 * (D + b)) hB
  refine ⟨M * Real.sqrt CB, mul_pos hM (Real.sqrt_pos.mpr hCB),
    fun hPL N ℓ hN hℓ0 hℓ1 hK1 T hTm hT => ?_⟩
  set K : ℝ := ((N : ℕ) : ℝ) * ℓ with hKdef
  have hK0 : 0 < K := by linarith
  have hKN : K ≤ ((N : ℕ) : ℝ) := by
    rw [hKdef]
    exact mul_le_of_le_one_right (by positivity) hℓ1
  set μ := (gibbsMeasure ⟨(beta, s), hbeta, hs, hs1⟩ N).map (anchorMap N) with hμ
  set S : Set (Fin ((N : ℕ) - 1) → ℝ) := {y | anchoredCutoff N s K γ ε y ≠ 1} with hSdef
  have hmeasS : MeasurableSet S := (measurable_anchoredCutoff s K γ ε) (measurableSet_singleton 1).compl
  -- Step 1: the mass of the bad set is the Gibbs mass of the good-event complement.
  have hmass : μ S ≤ ENNReal.ofReal (CB * K ^ (-(2 * (D + b)))) := by
    rw [hμ, Measure.map_apply (measurable_anchorMap N) hmeasS]
    have hpre : anchorMap N ⁻¹' S = {X | goodCutoff N s K γ ε X ≠ 1} := by
      ext X
      simp only [hSdef, Set.mem_preimage, Set.mem_ofPred_eq, anchoredCutoff_anchorMap]
    rw [hpre]
    exact hprob hPL N hN K hK1 hKN
  -- Step 2: the integrand is dominated by the indicator of the bad set.
  have hbound : ∀ y, ‖(1 - anchoredCutoff N s K γ ε y) * T y‖ ≤
      S.indicator (fun _ => M * K ^ D) y := by
    intro y
    by_cases hy : anchoredCutoff N s K γ ε y = 1
    · have hyS : y ∉ S := by simp [hSdef, hy]
      rw [Set.indicator_of_notMem hyS, hy]
      simp
    · have hyS : y ∈ S := by simp [hSdef, hy]
      rw [Set.indicator_of_mem hyS, Real.norm_eq_abs, abs_mul]
      have h1 : |1 - anchoredCutoff N s K γ ε y| ≤ 1 := by
        rw [abs_le]
        constructor <;> linarith [anchoredCutoff_nonneg s K γ ε y, anchoredCutoff_le_one s K γ ε y]
      calc |1 - anchoredCutoff N s K γ ε y| * |T y|
          ≤ 1 * (M * K ^ D) := mul_le_mul h1 (hT y) (abs_nonneg _) zero_le_one
        _ = M * K ^ D := one_mul _
  -- Step 3: the `L²` norm of the indicator, and the square root of the mass.
  have hmeasf : AEStronglyMeasurable (fun y => (1 - anchoredCutoff N s K γ ε y) * T y) μ :=
    ((measurable_const.sub (measurable_anchoredCutoff s K γ ε)).mul hTm).aestronglyMeasurable
  refine le_trans (eLpNorm_mono_real hmeasf hbound) ?_
  rw [eLpNorm_indicator_const hmeasS.nullMeasurableSet (by norm_num) (by norm_num)]
  have hexp : (1 / (2 : ENNReal).toReal : ℝ) = 1 / 2 := by norm_num
  rw [hexp]
  have hMK : 0 ≤ M * K ^ D := mul_nonneg hM.le (Real.rpow_nonneg hK0.le _)
  have hX : 0 ≤ CB * K ^ (-(2 * (D + b))) :=
    mul_nonneg hCB.le (Real.rpow_nonneg hK0.le _)
  calc ‖M * K ^ D‖ₑ * μ S ^ (1 / 2 : ℝ)
      ≤ ENNReal.ofReal (M * K ^ D) *
          (ENNReal.ofReal (CB * K ^ (-(2 * (D + b))))) ^ (1 / 2 : ℝ) := by
        rw [Real.enorm_eq_ofReal hMK]
        exact mul_le_mul_right (ENNReal.rpow_le_rpow hmass (by norm_num)) _
    _ = ENNReal.ofReal (M * K ^ D * (CB * K ^ (-(2 * (D + b)))) ^ (1 / 2 : ℝ)) := by
        rw [ENNReal.ofReal_rpow_of_nonneg hX (by norm_num), ENNReal.ofReal_mul hMK]
    _ = ENNReal.ofReal (M * Real.sqrt CB * K ^ (-b)) := by
        congr 1
        rw [Real.mul_rpow hCB.le (Real.rpow_nonneg hK0.le _), ← Real.sqrt_eq_rpow,
          ← Real.rpow_mul hK0.le]
        have hexp2 : K ^ (-(2 * (D + b)) * (1 / 2 : ℝ)) = K ^ (-(D + b)) := by
          congr 1
          ring
        have hsplit : K ^ D * K ^ (-(D + b)) = K ^ (-b) := by
          rw [← Real.rpow_add hK0]
          congr 1
          ring
        rw [hexp2]
        calc M * K ^ D * (Real.sqrt CB * K ^ (-(D + b)))
            = M * Real.sqrt CB * (K ^ D * K ^ (-(D + b))) := by ring
          _ = M * Real.sqrt CB * K ^ (-b) := by rw [hsplit]

end Riesz1.Internal

end
