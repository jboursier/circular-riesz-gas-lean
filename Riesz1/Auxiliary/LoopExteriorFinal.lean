/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopExteriorQuadrature
public import Riesz1.Auxiliary.LoopExteriorSumNorm

/-!
# The exterior force bound

The exterior part of Lemma 5.8, including the bad-event probability,
measurability, finite moments, and the norm of the spatial supremum.
The good-event law is restricted, without renormalization.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Riesz1

/-- The exterior force bound, with only the Bakry–Émery criterion `External.BakryEmery` and the
Prékopa–Leindler inequality `External.PrekopaLeindler` as additional
inputs. Constants and the scale threshold are uniform in the window exponent. -/
theorem auxiliary_Loop_exterior
    (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (β s : ℝ) (hβ : 0 < β) (hs : 0 < s) (hs1 : s < 1) :
    ∃ eps0 : ℝ, 0 < eps0 ∧ ∀ (p δ : ℝ), 1 ≤ p → 0 < δ → δ < min (s / 2) eps0 →
      ∃ C c lam K0 : ℝ, 0 < C ∧ 0 < c ∧ 0 < lam ∧ 1 ≤ K0 ∧
        lam = δ / (4 * (s + 2)) ∧
        ∀ (N : ℕ+) (ℓ γ : ℝ),
          2 ≤ (N : ℕ) → 0 < ℓ → ℓ ≤ 1 → K0 ≤ (N : ℝ) * ℓ → 1 < γ →
          GradPartial N ℓ γ →
          let μ := loopPrecedingMeasure (⟨(β, s), hβ, hs, hs1⟩ : Parameters) N
          let G := loopExteriorGood N ℓ γ
          let ν := μ.comap (Subtype.val : G → LoopPrecedingConfiguration N)
          let F := fun X : G => ⨆ z, |loopExteriorForce s N ℓ γ X z|
          μ Gᶜ ≤ ENNReal.ofReal (C * Real.exp (-c * gradM N ℓ γ ^ lam)) ∧
          Measurable F ∧ MemLp F (ENNReal.ofReal p) ν ∧
          eLpNorm F (ENNReal.ofReal p) ν ≤
            ENNReal.ofReal (C * gradM N ℓ γ ^ (-1 - s / 2 + δ)) := by
  obtain ⟨epsP, hepsP, hprob⟩ := loopExteriorGood_probability hBE hPL β s hβ hs hs1
  obtain ⟨epsF, hepsF, hsum⟩ := loopExterior_sum_difference_sup_eLpNorm hBE hPL β s hβ hs hs1
  obtain ⟨B, hB, hquad⟩ := loopExterior_reference_quadrature s hs hs1
  refine ⟨min epsP epsF, lt_min hepsP hepsF, fun p δ hp hδ hδ0 => ?_⟩
  have hδP : δ < min (s / 2) epsP := lt_min (lt_of_lt_of_le hδ0 (min_le_left _ _))
    ((lt_of_lt_of_le hδ0 (min_le_right _ _)).trans_le (min_le_left _ _))
  have hδF : δ < min (s / 2) epsF := lt_min (lt_of_lt_of_le hδ0 (min_le_left _ _))
    ((lt_of_lt_of_le hδ0 (min_le_right _ _)).trans_le (min_le_right _ _))
  obtain ⟨c, Cp, Kp, hc, hCp, hKp, hprob⟩ := hprob δ hδ hδP
  obtain ⟨Cf, Kf, hCf, hKf, hsum⟩ := hsum δ hδ hδF p hp
  let C := Cp + Cf + B
  refine ⟨C, c, δ / (4 * (s + 2)), max Kp Kf,
    by dsimp [C]; positivity, hc, by positivity, hKp.trans (le_max_left _ _), rfl, ?_⟩
  intro N ℓ γ hN hℓ hℓ1 hK hγ hP
  have hbad := hprob N ℓ γ hN hℓ hℓ1 ((le_max_left _ _).trans hK) hγ hP
  have hbad' : loopPrecedingMeasure ⟨(β, s), hβ, hs, hs1⟩ N (loopExteriorGood N ℓ γ)ᶜ ≤
      ENNReal.ofReal (C * Real.exp (-c * gradM N ℓ γ ^ (δ / (4 * (s + 2))))) := by
    apply hbad.trans
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (Real.exp_nonneg _)
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, N = (n + 1).succPNat := by
    refine ⟨(N : ℕ) - 2, ?_⟩
    apply Subtype.ext
    change (N : ℕ) = ((N : ℕ) - 2 + 1) + 1
    omega
  let N := (n + 1).succPNat
  let μ := loopPrecedingMeasure (⟨(β, s), hβ, hs, hs1⟩ : Parameters) N
  let G := loopExteriorGood N ℓ γ
  let ν := μ.comap (Subtype.val : G → LoopPrecedingConfiguration N)
  let F := fun X : G => ⨆ z, |loopExteriorForce s N ℓ γ X z|
  let H := fun X : G => ∑ j ∈ loopExteriorLabels N ℓ γ,
    ⨆ z : Icc (-gradM N ℓ γ / 4) (gradM N ℓ γ / 4),
      |deriv (loopArcG s N) (z.val - loopPrecedingLift X.val j) -
        deriv (loopArcG s N) (z.val - (j : ℝ))|
  let M := gradM N ℓ γ
  let q := B * M ^ (-s - 1)
  obtain ⟨_, _, hHnorm⟩ := hsum n ℓ γ ((le_max_right _ _).trans hK) hγ.le hP
  have hK1 : 1 ≤ (N : ℝ) * ℓ := (hKp.trans (le_max_left _ _)).trans hK
  have hγ0 : 0 ≤ γ := by linarith
  have hM1 : 1 ≤ M := Real.one_le_rpow hK1 hγ0
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one hM1
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hm : Measurable F := measurable_loopExteriorForce_sup hs hs1 hK1 hγ0 hP
  have hF0 (X : G) : 0 ≤ F X := by
    let z0 : Icc (-M / 4) (M / 4) := ⟨0, by constructor <;> linarith⟩
    exact (abs_nonneg _).trans (le_ciSup (loopExteriorForce_max hs hs1 hK1 hγ0 hP X).1 z0)
  have : Nonempty (Icc (-gradM N ℓ γ / 4) (gradM N ℓ γ / 4)) :=
    ⟨⟨0, by constructor <;> linarith⟩⟩
  have hpoint (X : G) : F X ≤ H X + q := by
    apply ciSup_le
    intro z
    exact (loopExteriorForce_bound_by_comparison hs hs1 hK1 hγ0 hP X z).trans
      (add_le_add le_rfl (hquad N ℓ γ hK1 hγ0 hP z.val z.property))
  have hp0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr (by linarith)).ne'
  have hpE : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp
  have hqnorm : eLpNorm (fun _ : G => q) (ENNReal.ofReal p) ν ≤ ENNReal.ofReal q := by
    calc
      _ ≤ eLpNorm (fun _ : LoopPrecedingConfiguration N => q) (ENNReal.ofReal p) μ :=
        eLpNorm_subtype_le μ (measurableSet_loopExteriorGood N ℓ γ) measurable_const _
      _ = _ := by
        rw [eLpNorm_const' q hp0 ENNReal.ofReal_ne_top, measure_univ, ENNReal.one_rpow, mul_one,
          Real.enorm_eq_ofReal hq]
  have hpow : M ^ (-s - 1) ≤ M ^ (-1 - s / 2 + δ) :=
    Real.rpow_le_rpow_of_exponent_le hM1 (by linarith)
  have hnorm : eLpNorm F (ENNReal.ofReal p) ν ≤
      ENNReal.ofReal (C * M ^ (-1 - s / 2 + δ)) := by
    calc
      _ ≤ eLpNorm (fun X : G => H X + q) (ENNReal.ofReal p) ν := by
        apply eLpNorm_mono_real hm.aestronglyMeasurable
        intro X
        rw [Real.norm_eq_abs, abs_of_nonneg (hF0 X)]
        exact hpoint X
      _ ≤ eLpNorm H (ENNReal.ofReal p) ν + eLpNorm (fun _ : G => q) (ENNReal.ofReal p) ν :=
        eLpNorm_add_le hpE
      _ ≤ ENNReal.ofReal (Cf * M ^ (-1 - s / 2 + δ)) + ENNReal.ofReal q :=
        add_le_add hHnorm hqnorm
      _ ≤ _ := by
        rw [← ENNReal.ofReal_add (by positivity) hq]
        apply ENNReal.ofReal_le_ofReal
        have hqpow : q ≤ B * M ^ (-1 - s / 2 + δ) := mul_le_mul_of_nonneg_left hpow hB.le
        have hCp0 : 0 ≤ Cp * M ^ (-1 - s / 2 + δ) := by positivity
        dsimp [C]
        nlinarith
  exact ⟨hbad', hm, hnorm.trans_lt ENNReal.ofReal_lt_top, hnorm⟩

end Riesz1

end
