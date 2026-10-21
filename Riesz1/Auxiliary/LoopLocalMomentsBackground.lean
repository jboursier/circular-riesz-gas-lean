/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopLocalMomentsKernel
public import Riesz1.Auxiliary.LoopCutoffPairBound
import all Mathlib.Basic.Real.Basic
import all Mathlib.Basic.NNReal.Defs

/-!
# The deterministic background of the localized loop

The local moments part of Lemma 5.8, the deterministic background term.
Its double integral converges absolutely and is bounded by `C Lip(b) M²`.
The estimate includes full windows, where `N ≤ 8M` is used.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace Riesz1

namespace Internal

/-- A radius estimate for a microscopic pair integral. This conditional helper is used
only with the uniform kernel estimate proved in `loopLocal_pair_kernel_bound`. -/
theorem loopLocal_integral_radius {s C : ℝ} (hs1 : s < 1) (hC : 0 ≤ C)
    (N : ℕ+) {b : ℝ → ℝ} {L : NNReal}
    (hk : ∀ z u : ℝ, |z - u| ≤ (N : ℝ) / 2 →
      |loopArcKernel s N b z u| ≤ C * L * |z - u| ^ (-s))
    {z a c R : ℝ} (hR : 0 ≤ R) (hac : a ≤ c) (ha : z - R ≤ a) (hc : c ≤ z + R)
    (hsmall : ∀ u ∈ Icc a c, |z - u| ≤ (N : ℝ) / 2) :
    |∫ u in a..c, loopArcKernel s N b z u| ≤
      C * L * (2 * R ^ (1 - s) / (1 - s)) := by
  have hi := (intervalIntegrable_abs_sub_rpow_radius hs1 hR hac ha hc).const_mul (C * L)
  have hbound : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ Ioc a c →
      ‖loopArcKernel s N b z u‖ ≤ C * L * |u - z| ^ (-s) := by
    exact Filter.Eventually.of_forall fun u hu => by
      rw [Real.norm_eq_abs, abs_sub_comm u z]
      exact hk z u (hsmall u ⟨hu.1.le, hu.2⟩)
  calc |∫ u in a..c, loopArcKernel s N b z u|
      ≤ ∫ u in a..c, C * L * |u - z| ^ (-s) := by
        simpa only [Real.norm_eq_abs] using
          intervalIntegral.norm_integral_le_of_norm_le hac hbound hi
    _ = C * L * ∫ u in a..c, |u - z| ^ (-s) := intervalIntegral.integral_const_mul _ _
    _ ≤ C * L * (2 * R ^ (1 - s) / (1 - s)) :=
      mul_le_mul_of_nonneg_left (integral_abs_sub_rpow_le_radius hs1 hR hac ha hc) (by positivity)

end Internal

/-- The deterministic background assertion in the local moments part of Lemma 5.8,
for arbitrary smooth periodic microscopic tests, with their Lipschitz constant explicit.
The outer integrability certificate is included, so the integral cannot hide divergence. -/
theorem loopLocalBackground_bound {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (ℓ γ : ℝ) {b : ℝ → ℝ} {L : NNReal},
      2 ≤ (N : ℕ) → 0 ≤ ℓ → 1 ≤ (N : ℝ) * ℓ → 0 ≤ γ → ContDiff ℝ 1 b →
      Function.Periodic b (N : ℝ) → LipschitzWith L b →
      IntervalIntegrable (fun z => ∫ u in loopLocalLo N ℓ γ..loopLocalHi N ℓ γ,
        loopArcKernel s N b z u) volume (loopLocalLo N ℓ γ) (loopLocalHi N ℓ γ) ∧
      |loopLocalBackground s N ℓ γ b| ≤ C * L * (gradM N ℓ γ) ^ 2 := by
  obtain ⟨A, hA, hk⟩ := loopLocal_pair_kernel_bound hs hs1
  refine ⟨128 * A / (1 - s), by positivity, ?_⟩
  intro N ℓ γ b L hN hℓ hK hγ hb hp hL
  have hM : 1 ≤ gradM N ℓ γ := Real.one_le_rpow hK hγ
  have hNreal : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hden : 0 < 1 - s := by linarith
  have hab := loopLocalLo_le_hi N hℓ (γ := γ)
  let D : ℝ := 16 * A * L * gradM N ℓ γ / (1 - s)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hbound : ∀ z ∈ Icc (loopLocalLo N ℓ γ) (loopLocalHi N ℓ γ),
      |∫ u in loopLocalLo N ℓ γ..loopLocalHi N ℓ γ, loopArcKernel s N b z u| ≤ D := by
    intro z hz
    by_cases hP : GradPartial N ℓ γ
    · simp only [loopLocalLo, loopLocalHi, hP, ↓reduceIte, mem_Icc] at hz ⊢
      have hi := Internal.loopLocal_integral_radius hs1 hA.le N (hk N hL)
        (z := z) (a := -gradM N ℓ γ) (c := gradM N ℓ γ) (R := 2 * gradM N ℓ γ)
        (by positivity) (by linarith) (by linarith [hz.2]) (by linarith [hz.1])
        (fun u hu => by
          have hPr : gradM N ℓ γ < (N : ℝ) / 8 := hP
          rw [abs_le]
          constructor <;> linarith [hu.1, hu.2, hz.1, hz.2])
      apply hi.trans
      have hpw : (2 * gradM N ℓ γ) ^ (1 - s) ≤ 2 * gradM N ℓ γ :=
        Real.rpow_le_self_of_one_le (by linarith) (by linarith)
      dsimp [D]
      rw [← mul_div_assoc, div_le_div_iff_of_pos_right hden]
      rw [← (show Real.instPreorder.toLE = Real.partialOrder.toLE from rfl)]
      have hmul := mul_le_mul_of_nonneg_left
        (show 2 * (2 * gradM N ℓ γ) ^ (1 - s) ≤ 16 * gradM N ℓ γ by linarith)
        (mul_nonneg hA.le L.property)
      simpa only [NNReal.toReal, mul_assoc, mul_left_comm, mul_comm] using hmul
    · simp only [loopLocalLo, loopLocalHi, hP, ↓reduceIte] at hz ⊢
      have he := (loopLocalKernel_periodic_right hp s z).intervalIntegral_add_eq
        (z - (N : ℝ) / 2) 0
      have he' : (∫ u in (0 : ℝ)..(N : ℝ), loopArcKernel s N b z u) =
          ∫ u in (z - (N : ℝ) / 2)..(z + (N : ℝ) / 2), loopArcKernel s N b z u := by
        simpa only [zero_add, show z - (N : ℝ) / 2 + N = z + (N : ℝ) / 2 by ring] using he.symm
      rw [he']
      have hi := Internal.loopLocal_integral_radius hs1 hA.le N (hk N hL)
        (z := z) (a := z - (N : ℝ) / 2) (c := z + (N : ℝ) / 2) (R := (N : ℝ) / 2)
        (by positivity) (by linarith) le_rfl le_rfl
        (fun u hu => by rw [abs_le]; constructor <;> linarith [hu.1, hu.2])
      apply hi.trans
      have hpw : ((N : ℝ) / 2) ^ (1 - s) ≤ (N : ℝ) / 2 :=
        Real.rpow_le_self_of_one_le (by linarith) (by linarith)
      have hNM : (N : ℝ) ≤ 8 * gradM N ℓ γ := by
        have := not_lt.mp hP
        linarith
      dsimp [D]
      rw [← mul_div_assoc, div_le_div_iff_of_pos_right hden]
      rw [← (show Real.instPreorder.toLE = Real.partialOrder.toLE from rfl)]
      have hmul := mul_le_mul_of_nonneg_left
        (show 2 * ((N : ℝ) / 2) ^ (1 - s) ≤ 16 * gradM N ℓ γ by linarith)
        (mul_nonneg hA.le L.property)
      simpa only [NNReal.toReal, mul_assoc, mul_left_comm, mul_comm] using hmul
  have hm : Measurable (fun z => ∫ u in loopLocalLo N ℓ γ..loopLocalHi N ℓ γ,
      loopArcKernel s N b z u) := by
    simp_rw [intervalIntegral.integral_of_le hab]
    exact ((measurable_loopLocalKernel hb.continuous s N).stronglyMeasurable.integral_prod_right'
      (ν := volume.restrict (Ioc (loopLocalLo N ℓ γ) (loopLocalHi N ℓ γ)))).measurable
  have hi : IntervalIntegrable (fun z => ∫ u in loopLocalLo N ℓ γ..loopLocalHi N ℓ γ,
      loopArcKernel s N b z u) volume (loopLocalLo N ℓ γ) (loopLocalHi N ℓ γ) := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
    apply IntegrableOn.of_bound (C := D) measure_Icc_lt_top hm.aestronglyMeasurable.restrict
    filter_upwards [ae_restrict_mem measurableSet_Icc] with z hz
    simpa only [Real.norm_eq_abs] using hbound z hz
  refine ⟨hi, ?_⟩
  have hlen : loopLocalHi N ℓ γ - loopLocalLo N ℓ γ ≤ 8 * gradM N ℓ γ := by
    unfold loopLocalHi loopLocalLo
    split_ifs with hP
    · linarith
    · have := not_lt.mp hP
      linarith
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := loopLocalLo N ℓ γ) (b := loopLocalHi N ℓ γ)
    (f := fun z => ∫ u in loopLocalLo N ℓ γ..loopLocalHi N ℓ γ, loopArcKernel s N b z u)
    (C := D) (fun z hz => by
      rw [Real.norm_eq_abs]
      exact hbound z ((uIoc_of_le hab ▸ hz).imp le_of_lt id))
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab)] at hnorm
  calc |loopLocalBackground s N ℓ γ b|
      ≤ D * (loopLocalHi N ℓ γ - loopLocalLo N ℓ γ) := hnorm
    _ ≤ D * (8 * gradM N ℓ γ) := mul_le_mul_of_nonneg_left hlen hD
    _ = (128 * A / (1 - s)) * L * gradM N ℓ γ ^ 2 := by dsimp [D]; ring

end Riesz1

end
