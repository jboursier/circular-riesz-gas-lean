/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopExteriorMoments
public import Riesz1.Auxiliary.LoopExteriorComparison
public import Riesz1.ToMathlib.RestrictedSubtypeLp
import all Mathlib.Data.PNat.Defs
import all Init.Data.Nat.Basic

/-!
# The exterior-force norm for one label

The per-label supremum estimate in the proof of the exterior part of
Lemma 5.8. The measure is the pullback of the restricted
preceding-particle measure to the actual good-event carrier. No renormalization is
made. The exceptional displacement event is controlled by its probability to power
`1/p`, and the complementary event uses the displacement moment.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Riesz1

/-- The per-label estimate of the exterior part of Lemma 5.8, with the
supremum inside the `L^p` norm, both signs of the label, and all measurability and
moment certificates. All constants precede the particle number and window data. -/
theorem loopExterior_difference_sup_eLpNorm
    (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (β s : ℝ) (hβ : 0 < β) (hs : 0 < s) (hs1 : s < 1) :
    ∃ eps0 : ℝ, 0 < eps0 ∧ ∀ δ : ℝ, 0 < δ → δ < min (s / 2) eps0 →
      ∀ p : ℝ, 1 ≤ p → ∃ C c T : ℝ, 0 < C ∧ 0 < c ∧ 1 ≤ T ∧
        ∀ (n : ℕ) (ℓ γ : ℝ), 1 ≤ ((n + 1).succPNat : ℝ) * ℓ → 0 ≤ γ →
        GradPartial (n + 1).succPNat ℓ γ →
        ∀ j ∈ loopExteriorLabels (n + 1).succPNat ℓ γ, T ≤ |(j : ℝ)| →
        let N := (n + 1).succPNat
        let μ := loopPrecedingMeasure (⟨(β, s), hβ, hs, hs1⟩ : Parameters) N
        let ν := μ.comap (Subtype.val : {X // X ∈ loopExteriorGood N ℓ γ} → LoopPrecedingConfiguration N)
        let F := fun X : {X // X ∈ loopExteriorGood N ℓ γ} =>
          ⨆ z : Icc (-gradM N ℓ γ / 4) (gradM N ℓ γ / 4),
            |deriv (loopArcG s N) (z.val - loopPrecedingLift X.val j) -
              deriv (loopArcG s N) (z.val - (j : ℝ))|
        Measurable F ∧ MemLp F (ENNReal.ofReal p) ν ∧
        eLpNorm F (ENNReal.ofReal p) ν ≤ ENNReal.ofReal
          (C * (|(j : ℝ)| ^ (-2 - s / 2 + δ) + gradM N ℓ γ ^ (-s - 1) *
            Real.exp (-c * |(j : ℝ)| ^ (δ / (4 * (s + 2)))))) := by
  obtain ⟨e1, he1, hmom⟩ := loopPrecedingLift_displacement_eLpNorm hBE hPL β s hβ hs hs1
  obtain ⟨e2, he2, htail⟩ := Internal.loopPrecedingLift_displacement_tail_of_rigidity
    β s hβ hs hs1 (Internal.rigidityConclusion_of_externals hBE hPL β s hβ hs hs1)
  obtain ⟨A, B, hA, hB, hpoint⟩ := loopExterior_difference_sup_bound hs hs1
  refine ⟨min e1 e2, lt_min he1 he2, fun δ hδ hδ0 p hp => ?_⟩
  have hδs : δ < s / 2 := lt_of_lt_of_le hδ0 (min_le_left _ _)
  have hδ1 : δ < min (s / 2) e1 := lt_min hδs
    ((lt_of_lt_of_le hδ0 (min_le_right _ _)).trans_le (min_le_left _ _))
  have hδ2 : δ < min (s / 2) e2 := lt_min hδs
    ((lt_of_lt_of_le hδ0 (min_le_right _ _)).trans_le (min_le_right _ _))
  obtain ⟨D, hD, hd⟩ := hmom δ hδ hδ1 p hp
  obtain ⟨b, Q, T, hb, hQ, hT, ht⟩ := htail δ hδ hδ2
  let C := A * D + B * Q ^ (1 / p)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, b / p, T, hC, div_pos hb (by linarith), hT, ?_⟩
  intro n ℓ γ hK hγ hP j hj hjT
  let N := (n + 1).succPNat
  let P : Parameters := ⟨(β, s), hβ, hs, hs1⟩
  let μ := loopPrecedingMeasure P N
  let S := loopExteriorGood N ℓ γ
  let ν := μ.comap (Subtype.val : S → LoopPrecedingConfiguration N)
  let Δ := fun X : LoopPrecedingConfiguration N => loopPrecedingLift X j - (j : ℝ)
  let E : Set S := {X | |(j : ℝ)| / 2 ≤ |Δ X.val|}
  let F := fun X : S => ⨆ z : Icc (-gradM N ℓ γ / 4) (gradM N ℓ γ / 4),
    |deriv (loopArcG s N) (z.val - loopPrecedingLift X.val j) -
      deriv (loopArcG s N) (z.val - (j : ℝ))|
  let τ := δ / (4 * (s + 2))
  have hp0 : 0 < p := by linarith
  have hM : 0 < gradM N ℓ γ := lt_of_lt_of_le zero_lt_one (Real.one_le_rpow hK hγ)
  have hS : MeasurableSet S := measurableSet_loopExteriorGood N ℓ γ
  have hΔ : Measurable Δ := (measurable_loopPrecedingLift N j).sub_const _
  have hE : MeasurableSet E := measurableSet_le measurable_const
    (continuous_abs.measurable.comp (hΔ.comp measurable_subtype_coe))
  have hFm : Measurable F := (loopExterior_difference_sup_regular hs hs1 hK hγ hP hj).2
  have hF0 (X) : 0 ≤ F X := (loopExterior_difference_sup_regular hs hs1 hK hγ hP hj).1 X |>.2.2
  obtain ⟨_, hj1, hjN⟩ := loopExteriorLabels_abs hK hγ hP hj
  have hΔnorm : eLpNorm (fun X : S => |Δ X.val|) (ENNReal.ofReal p) ν ≤
      ENNReal.ofReal (D * |(j : ℝ)| ^ (s / 2 + δ)) := by
    calc
      _ ≤ eLpNorm (fun X => |Δ X|) (ENNReal.ofReal p) μ :=
        eLpNorm_subtype_le μ hS (continuous_abs.measurable.comp hΔ) _
      _ = eLpNorm Δ (ENNReal.ofReal p) μ := by
        change eLpNorm (fun X => ‖Δ X‖) _ _ = _
        exact eLpNorm_norm Δ hΔ.aestronglyMeasurable
      _ ≤ _ := (hd n j hj1 hjN).2
  have hprob : ν E ≤ ENNReal.ofReal (Q * Real.exp (-b * |(j : ℝ)| ^ τ)) := by
    apply (measure_subtype_preimage_le μ hS {X | |(j : ℝ)| / 2 ≤ |Δ X|}).trans
    apply ht hPL n j _ hjN
    simpa only [natAbs_cast_eq_abs] using hjT
  have hEnorm : eLpNorm (E.indicator (fun _ : S => B * gradM N ℓ γ ^ (-s - 1)))
      (ENNReal.ofReal p) ν ≤ ENNReal.ofReal
        (B * Q ^ (1 / p) * gradM N ℓ γ ^ (-s - 1) *
          Real.exp (-(b / p) * |(j : ℝ)| ^ τ)) := by
    rw [eLpNorm_indicator_const hE.nullMeasurableSet
      (ENNReal.ofReal_pos.mpr hp0).ne' ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hp0.le, Real.enorm_eq_ofReal (by positivity)]
    calc
      _ ≤ ENNReal.ofReal (B * gradM N ℓ γ ^ (-s - 1)) *
          ENNReal.ofReal (Q * Real.exp (-b * |(j : ℝ)| ^ τ)) ^ (1 / p) := by
        gcongr
      _ = _ := by
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity),
          ← ENNReal.ofReal_mul (by positivity),
          Real.mul_rpow hQ.le (Real.exp_pos _).le, ← Real.exp_mul]
        congr 1
        have he : (-b * |(j : ℝ)| ^ τ) * (1 / p) = -(b / p) * |(j : ℝ)| ^ τ := by ring
        rw [he]
        ring
  have hAnorm : eLpNorm (fun X : S => A * |(j : ℝ)| ^ (-s - 2) * |Δ X.val|)
      (ENNReal.ofReal p) ν ≤ ENNReal.ofReal (A * D * |(j : ℝ)| ^ (-2 - s / 2 + δ)) := by
    rw [show (fun X : S => A * |(j : ℝ)| ^ (-s - 2) * |Δ X.val|) =
      (A * |(j : ℝ)| ^ (-s - 2)) • (fun X : S => |Δ X.val|) by rfl,
      eLpNorm_const_smul, Real.enorm_eq_ofReal (by positivity)]
    apply (mul_le_mul' le_rfl hΔnorm).trans
    rw [← ENNReal.ofReal_mul (by positivity)]
    apply le_of_eq
    congr 1
    have hjpos : 0 < |(j : ℝ)| := by
      have : (0 : ℝ) < j.natAbs := by exact_mod_cast (show 0 < j.natAbs by omega)
      simpa only [natAbs_cast_eq_abs] using this
    calc
      _ = A * D * (|(j : ℝ)| ^ (-s - 2) * |(j : ℝ)| ^ (s / 2 + δ)) := by ring
      _ = _ := by
        rw [← Real.rpow_add hjpos]
        congr 2
        ring
  have hpE : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp
  have hn : eLpNorm F (ENNReal.ofReal p) ν ≤ ENNReal.ofReal
      (C * (|(j : ℝ)| ^ (-2 - s / 2 + δ) + gradM N ℓ γ ^ (-s - 1) *
        Real.exp (-(b / p) * |(j : ℝ)| ^ τ))) := by
    calc
      _ ≤ eLpNorm (fun X : S => A * |(j : ℝ)| ^ (-s - 2) * |Δ X.val| +
          E.indicator (fun _ => B * gradM N ℓ γ ^ (-s - 1)) X) (ENNReal.ofReal p) ν := by
        apply eLpNorm_mono_real hFm.aestronglyMeasurable
        intro X
        rw [Real.norm_eq_abs, abs_of_nonneg (hF0 X)]
        exact hpoint hK hγ hP hj X
      _ ≤ eLpNorm (fun X : S => A * |(j : ℝ)| ^ (-s - 2) * |Δ X.val|)
          (ENNReal.ofReal p) ν +
          eLpNorm (E.indicator (fun _ : S => B * gradM N ℓ γ ^ (-s - 1)))
            (ENNReal.ofReal p) ν := eLpNorm_add_le hpE
      _ ≤ ENNReal.ofReal (A * D * |(j : ℝ)| ^ (-2 - s / 2 + δ)) +
          ENNReal.ofReal (B * Q ^ (1 / p) * gradM N ℓ γ ^ (-s - 1) *
            Real.exp (-(b / p) * |(j : ℝ)| ^ τ)) := add_le_add hAnorm hEnorm
      _ ≤ _ := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        dsimp only [C]
        nlinarith [Real.rpow_nonneg (abs_nonneg (j : ℝ)) (-2 - s / 2 + δ),
          mul_nonneg (Real.rpow_nonneg hM.le (-s - 1))
            (Real.exp_nonneg (-(b / p) * |(j : ℝ)| ^ τ)),
          mul_nonneg hA.le hD.le,
          mul_nonneg hB.le (Real.rpow_nonneg hQ.le (1 / p))]
  exact ⟨hFm, hn.trans_lt ENNReal.ofReal_lt_top, hn⟩

end Riesz1

end
