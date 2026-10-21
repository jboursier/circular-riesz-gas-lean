/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopExteriorLabelNorm
public import Riesz1.ToMathlib.Calculus.IntegerPowerTail

/-!
# Summing exterior particle displacements

The complete random/reference comparison in the proof of the exterior part of
Lemma 5.8. Minkowski is applied to the sum of the individual
spatial suprema, which is stronger than the supremum of the summed difference.
The deterministic reference-lattice/background quadrature is a separate step.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Riesz1

/-- The sum of the per-label spatial suprema has the force-decay exponent of the paper.
The constants are uniform in the window exponent. This is the random/reference
part of Lemma 5.8. -/
theorem loopExterior_sum_difference_sup_eLpNorm
    (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (β s : ℝ) (hβ : 0 < β) (hs : 0 < s) (hs1 : s < 1) :
    ∃ eps0 : ℝ, 0 < eps0 ∧ ∀ δ : ℝ, 0 < δ → δ < min (s / 2) eps0 →
      ∀ p : ℝ, 1 ≤ p → ∃ C K0 : ℝ, 0 < C ∧ 1 ≤ K0 ∧
        ∀ (n : ℕ) (ℓ γ : ℝ), K0 ≤ ((n + 1).succPNat : ℝ) * ℓ → 1 ≤ γ →
        GradPartial (n + 1).succPNat ℓ γ →
        let N := (n + 1).succPNat
        let μ := loopPrecedingMeasure (⟨(β, s), hβ, hs, hs1⟩ : Parameters) N
        let ν := μ.comap (Subtype.val : {X // X ∈ loopExteriorGood N ℓ γ} → LoopPrecedingConfiguration N)
        let F := fun X : {X // X ∈ loopExteriorGood N ℓ γ} =>
          ∑ j ∈ loopExteriorLabels N ℓ γ,
            ⨆ z : Icc (-gradM N ℓ γ / 4) (gradM N ℓ γ / 4),
              |deriv (loopArcG s N) (z.val - loopPrecedingLift X.val j) -
                deriv (loopArcG s N) (z.val - (j : ℝ))|
        Measurable F ∧ MemLp F (ENNReal.ofReal p) ν ∧
        eLpNorm F (ENNReal.ofReal p) ν ≤
          ENNReal.ofReal (C * gradM N ℓ γ ^ (-1 - s / 2 + δ)) := by
  obtain ⟨eps0, heps0, ht⟩ := loopExterior_difference_sup_eLpNorm hBE hPL β s hβ hs hs1
  refine ⟨eps0, heps0, fun δ hδ hδ0 p hp => ?_⟩
  obtain ⟨C, c, T, hC, hc, hT, hb⟩ := ht δ hδ hδ0 p hp
  let a := 2 + s / 2 - δ
  have ha : 1 < a := by
    have := lt_of_lt_of_le hδ0 (min_le_left _ _)
    dsimp [a]
    linarith
  have hτ : 0 < δ / (4 * (s + 2)) := by positivity
  obtain ⟨D, hD, hd⟩ := rpow_mul_exp_neg_bounded (β := a) hτ hc
  let B := C * (1 + D)
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨B * (2 * (1 + 1 / (a - 1))), T, by positivity, hT, ?_⟩
  intro n ℓ γ hK hγ hP
  let N := (n + 1).succPNat
  let P : Parameters := ⟨(β, s), hβ, hs, hs1⟩
  let μ := loopPrecedingMeasure P N
  let S := loopExteriorGood N ℓ γ
  let ν := μ.comap (Subtype.val : S → LoopPrecedingConfiguration N)
  let I := loopExteriorLabels N ℓ γ
  let H := fun (j : ℤ) (X : S) => ⨆ z : Icc (-gradM N ℓ γ / 4) (gradM N ℓ γ / 4),
    |deriv (loopArcG s N) (z.val - loopPrecedingLift X.val j) -
      deriv (loopArcG s N) (z.val - (j : ℝ))|
  have hK1 : 1 ≤ (N : ℝ) * ℓ := hT.trans hK
  have hγ0 : 0 ≤ γ := zero_le_one.trans hγ
  have hKM : (N : ℝ) * ℓ ≤ gradM N ℓ γ := Real.self_le_rpow_of_one_le hK1 hγ
  have hM1 : 1 ≤ gradM N ℓ γ := hK1.trans hKM
  have hMn : gradM N ℓ γ ^ (-s - 1) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hM1 (by linarith)
  have hlabel (j : ℤ) (hj : j ∈ I) :
      Measurable (H j) ∧ eLpNorm (H j) (ENNReal.ofReal p) ν ≤ ENNReal.ofReal (B * |(j : ℝ)| ^ (-a)) := by
    have hjM := (loopExteriorLabels_abs hK1 hγ0 hP hj).1
    have hj1 : 1 ≤ |(j : ℝ)| := hM1.trans hjM.le
    obtain ⟨hm, _, hn⟩ := hb n ℓ γ hK1 hγ0 hP j hj (hK.trans (hKM.trans hjM.le))
    refine ⟨hm, hn.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    have hjpos : 0 < |(j : ℝ)| := lt_of_lt_of_le zero_lt_one hj1
    have he : Real.exp (-c * |(j : ℝ)| ^ (δ / (4 * (s + 2)))) ≤ D * |(j : ℝ)| ^ (-a) := by
      calc
        _ = |(j : ℝ)| ^ (-a) * (|(j : ℝ)| ^ a *
            Real.exp (-c * |(j : ℝ)| ^ (δ / (4 * (s + 2))))) := by
          rw [← mul_assoc, ← Real.rpow_add hjpos, neg_add_cancel, Real.rpow_zero, one_mul]
        _ ≤ |(j : ℝ)| ^ (-a) * D :=
          mul_le_mul_of_nonneg_left (hd _ hj1) (Real.rpow_nonneg (abs_nonneg _) _)
        _ = _ := mul_comm _ _
    have hexp := mul_le_mul hMn he (Real.exp_nonneg _) (by positivity : 0 ≤ (1 : ℝ))
    have hexp' : gradM N ℓ γ ^ (-s - 1) *
        Real.exp (-c * |(j : ℝ)| ^ (δ / (4 * (s + 2)))) ≤ D * |(j : ℝ)| ^ (-a) := by
      simpa only [one_mul] using hexp
    have hq : -2 - s / 2 + δ = -a := by dsimp [a]; ring
    rw [hq]
    calc
      _ ≤ C * (|(j : ℝ)| ^ (-a) + D * |(j : ℝ)| ^ (-a)) := by gcongr
      _ = _ := by dsimp [B]; ring
  have hsum : ∑ j ∈ I, |(j : ℝ)| ^ (-a) ≤
      (2 * (1 + 1 / (a - 1))) * gradM N ℓ γ ^ (1 - a) :=
    sum_int_abs_rpow_tail ha hM1 I (fun j hj => (loopExteriorLabels_abs hK1 hγ0 hP hj).1.le)
  have hFm : Measurable (fun X : S => ∑ j ∈ I, H j X) :=
    Finset.measurable_sum I (fun j hj => (hlabel j hj).1)
  have hpE : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp
  have hn : eLpNorm (fun X : S => ∑ j ∈ I, H j X) (ENNReal.ofReal p) ν ≤
      ENNReal.ofReal (B * (2 * (1 + 1 / (a - 1))) * gradM N ℓ γ ^ (-1 - s / 2 + δ)) := by
    calc
      _ ≤ ∑ j ∈ I, eLpNorm (H j) (ENNReal.ofReal p) ν := by
        simpa only [Finset.sum_fn] using eLpNorm_sum_le (μ := ν) (s := I) (f := H) hpE
      _ ≤ ∑ j ∈ I, ENNReal.ofReal (B * |(j : ℝ)| ^ (-a)) :=
        Finset.sum_le_sum (fun j hj => (hlabel j hj).2)
      _ = ENNReal.ofReal (B * ∑ j ∈ I, |(j : ℝ)| ^ (-a)) := by
        rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity), Finset.mul_sum]
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        have he : -1 - s / 2 + δ = 1 - a := by dsimp [a]; ring
        rw [he]
        calc
          _ ≤ B * ((2 * (1 + 1 / (a - 1))) * gradM N ℓ γ ^ (1 - a)) :=
            mul_le_mul_of_nonneg_left hsum hB.le
          _ = _ := by ring
  exact ⟨hFm, hn.trans_lt ENNReal.ofReal_lt_top, hn⟩

end Riesz1

end
