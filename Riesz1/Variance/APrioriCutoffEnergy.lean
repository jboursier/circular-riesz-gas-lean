/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.APrioriCutoffField
public import Riesz1.Variance.APrioriCutoffProbability

/-!
# Negligible cutoff inverse energy

The first conclusion of the cutoff estimate in Lemma 5.2, for the actual tilted inverse.
It takes the Bakry–Émery criterion `External.BakryEmery` and the Prékopa–Leindler
inequality `External.PrekopaLeindler` as hypotheses.
Membership in its vector `L²` carrier is concluded before taking energy.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Riesz1

/-- **First conclusion of the cutoff estimate in Lemma 5.2.** The
statistic is bounded only where the cutoff gradient is nonzero.
Every particle number at least two is represented as `n + 1`, and
every scale as `1 ≤ K ≤ n + 1`. -/
theorem anchoredCutoff_energy (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (P : Parameters) (γ ε : ℝ) (hγ : 1 < γ) (hε : 0 < ε)
    (D M b : ℝ) (hD : 0 < D) (hM : 0 < M) (hb : 0 < b) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 1 ≤ n → ∀ (θ : ℝ → ℝ) (hθ : IsForcingCutoff θ),
      ∀ (K : ℝ) (hK : 1 ≤ K), K ≤ (n : ℝ) + 1 →
      let χ := nearestTiltedPairs P n.succPNat hθ K γ ε (by linarith)
      ∀ (T : (Fin n → ℝ) → ℝ), Measurable T →
        (∀ y, fderiv ℝ (anchoredCutoff n.succPNat P.val.2 K γ ε) y ≠ 0 → |T y| ≤ M * K ^ D) →
        ∃ hv : MemLp (anchoredCutoffField n P.val.2 K γ ε T) 2 (anchoredMeasureE χ),
          anchoredInverseEnergy χ
            (hsRieszPairPotentials_curvature_pos n.succPNat P.2.1 (parametersExponent P))
            (hv.toLp (anchoredCutoffField n P.val.2 K γ ε T)) ≤ C * K ^ (-b) := by
  let s := P.val.2
  let B := b + 2 * D + 5 * γ + (s + 4) * ε
  have hs : 0 < s := P.2.2.1
  have hB : 0 < B := by dsimp [B]; positivity
  obtain ⟨CE, hCE, henergy⟩ := nearestAnchored_inverse_energy P
  obtain ⟨CB, hCB, hprob⟩ := nearestAnchored_cutoff_probability hBE hPL P γ ε hγ hε B hB
  refine ⟨CE * (8 * 76 ^ 2 * M ^ 2) * CB, by positivity,
    fun n hn θ hθ K hK hKN T hTm hT => ?_⟩
  let χ := nearestTiltedPairs P n.succPNat hθ K γ ε (by linarith : 0 < K)
  have hc := hsRieszPairPotentials_curvature_pos n.succPNat P.2.1 (parametersExponent P)
  have hγ0 : 0 ≤ γ := by linarith
  have hv := memLp_anchoredCutoffField hn χ hc s K γ ε hK hγ0 hs.le hε.le T hTm M D hM.le hT
  refine ⟨hv, ?_⟩
  obtain ⟨ha, hdata⟩ := anchoredCutoff_coefficients_data hn χ hc s K γ ε hK hγ0 hs.le hε.le
    T hTm M D hM.le hT
  have hrep : ∀ᵐ y ∂anchoredMeasureE χ, ∀ U : Fin n → ℝ,
      dotProd (WithLp.ofLp (hv.toLp (anchoredCutoffField n s K γ ε T) y)) U =
        ∑ e ∈ nearestPairs n.succPNat (window n.succPNat K γ),
          anchoredCutoffCoefficients n s K γ ε T y e * (((n : ℝ) + 1) * edgeForm n e U) := by
    filter_upwards [hv.coeFn_toLp, hdata] with y hy hdy U
    rw [hy]
    exact hdy.2 U
  have hE := henergy n hn θ hθ K γ ε hK hε.le
    (hv.toLp (anchoredCutoffField n s K γ ε T)) (anchoredCutoffCoefficients n s K γ ε T) ha hrep
  have hI := integral_anchoredCutoffCoefficients_sq_le hn χ hc s K γ ε hK hγ0 hs.le hε.le
    T hTm M D hM.le hT
  let S := {y : AnchoredEuclidean n | anchoredCutoff n.succPNat s K γ ε (WithLp.ofLp y) ≠ 1}
  have hS : MeasurableSet S :=
    (((measurable_anchoredCutoff (N := n.succPNat) s K γ ε).comp
      (PiLp.continuous_ofLp 2 _).measurable) (measurableSet_singleton 1)).compl
  have hmass : anchoredMeasureE χ S ≤ ENNReal.ofReal (CB * K ^ (-B)) := by
    rw [nearestTiltedPairs_anchoredMeasureE P hn hθ K γ ε (by linarith)]
    erw [Measure.map_apply (PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ)).measurable hS]
    have hpre : WithLp.toLp 2 ⁻¹' S = {y | anchoredCutoff n.succPNat s K γ ε y ≠ 1} := by
      ext y
      rfl
    rw [hpre]
    exact hprob n.succPNat (by simpa using hn) θ hθ K hK (by simpa using hKN)
  have hmassR : (anchoredMeasureE χ).real S ≤ CB * K ^ (-B) := by
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hmass).trans_eq
      (ENNReal.toReal_ofReal (by positivity))
  have hK0 : 0 < K := by linarith
  have hpoly : K ^ ((s + 2) * ε) * (8 * K ^ γ) *
      ((M * K ^ D) * (76 * K ^ (2 * γ + ε))) ^ 2 * (CB * K ^ (-B)) =
      (8 * 76 ^ 2 * M ^ 2) * CB * K ^ (-b) := by
    have hexp : (s + 2) * ε + γ + (D + (2 * γ + ε)) * 2 + -B = -b := by dsimp [B]; ring
    have hpow : K ^ ((s + 2) * ε) * K ^ γ *
        (K ^ D * K ^ (2 * γ + ε)) ^ 2 * K ^ (-B) = K ^ (-b) := by
      rw [← Real.rpow_add hK0, ← Real.rpow_natCast, ← Real.rpow_add hK0,
        ← Real.rpow_mul hK0.le, ← Real.rpow_add hK0, ← Real.rpow_add hK0]
      norm_num only [Nat.cast_ofNat]
      rw [hexp]
    calc _ = (8 * 76 ^ 2 * M ^ 2) * CB *
          (K ^ ((s + 2) * ε) * K ^ γ * (K ^ D * K ^ (2 * γ + ε)) ^ 2 * K ^ (-B)) := by ring
      _ = _ := by rw [hpow]
  calc anchoredInverseEnergy χ hc (hv.toLp (anchoredCutoffField n s K γ ε T))
      ≤ CE * K ^ ((s + 2) * ε) *
          ((8 * K ^ γ) * ((M * K ^ D) * (76 * K ^ (2 * γ + ε))) ^ 2 *
            (anchoredMeasureE χ).real S) :=
        hE.trans (mul_le_mul_of_nonneg_left hI (by positivity))
    _ ≤ CE * K ^ ((s + 2) * ε) *
          ((8 * K ^ γ) * ((M * K ^ D) * (76 * K ^ (2 * γ + ε))) ^ 2 * (CB * K ^ (-B))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmassR (by positivity)) (by positivity)
    _ = (CE * (8 * 76 ^ 2 * M ^ 2) * CB) * K ^ (-b) := by
        calc _ = CE * (K ^ ((s + 2) * ε) * (8 * K ^ γ) *
            ((M * K ^ D) * (76 * K ^ (2 * γ + ε))) ^ 2 * (CB * K ^ (-B))) := by ring
          _ = _ := by rw [hpoly]; ring

end Riesz1

end
