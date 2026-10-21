/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.CLT.GapsDiscScale
public import Riesz1.CLT.GapsDiscIncrements
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Admissibility and probability limits for short increments

The sequence assertions in Corollary 1.
Sequences are allowed to use any particle numbers tending along any index filter.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace Riesz1

/-- Every increment in a fixed multiple of the normalization is eventually admissible. -/
theorem gapsDisc_increment_eventually_admissible (s : RieszExponent)
    {ι : Type*} {l : Filter ι} (N : ι → ℕ+) (k : ι → ℕ)
    (hk : Tendsto k l atTop)
    (hvalid : ∀ᶠ n in l, 1 ≤ k n ∧ k n ≤ (N n : ℕ) / 2)
    (A : ℝ) (_hA : 0 < A) :
    ∀ᶠ n in l, ∀ r : ℤ, (r.natAbs : ℝ) ≤ A * gapScale s (N n) (k n) →
      1 ≤ (k n : ℤ) + r ∧ (k n : ℤ) + r < (N n : ℕ) ∧
        r.natAbs ≤ (N n : ℕ) / 2 := by
  have hlim := (gapsDisc_gapScale_div_tendsto_zero s N k hk hvalid).const_mul A
  have he : ∀ᶠ n in l, A * (gapScale s (N n) (k n) / k n) < 1 / 2 :=
    hlim.eventually (gt_mem_nhds (by norm_num : A * (0 : ℝ) < 1 / 2))
  filter_upwards [hvalid, hk.eventually (eventually_ge_atTop 2), he] with n hn hk2 he
  intro r hr
  have hk0 : (0 : ℝ) < k n := by exact_mod_cast hn.1
  have hb : A * gapScale s (N n) (k n) < (k n : ℝ) / 2 := by
    rw [← mul_div_assoc, div_lt_iff₀ hk0] at he
    linarith
  have hri : 2 * r.natAbs < k n := by
    have : (2 : ℝ) * r.natAbs < k n := by linarith
    exact_mod_cast this
  have habs := Int.natCast_natAbs (n := r)
  have hle : -(r.natAbs : ℤ) ≤ r ∧ r ≤ (r.natAbs : ℤ) := by
    rw [habs]
    exact abs_le.mp le_rfl
  constructor
  · omega
  constructor <;> omega

namespace Internal

/-- The uniform expectation assertion on all increments in a fixed normalized window.
The constant can be chosen before the window size as well as before the sequences. -/
theorem gapsDisc_increment_eventual_expectation_of_rigidity (beta s : ℝ) (hbeta : 0 < beta)
    (hs : 0 < s) (hs1 : s < 1) (hPL : External.PrekopaLeindler)
    (hRig : RigidityConclusion beta s hbeta hs hs1) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} {l : Filter ι} (N : ι → ℕ+) (k : ι → ℕ),
      Tendsto k l atTop → (∀ᶠ n in l, 1 ≤ k n ∧ k n ≤ (N n : ℕ) / 2) →
      ∀ A : ℝ, 0 < A → ∀ᶠ n in l, ∀ r : ℤ,
      (r.natAbs : ℝ) ≤ A * gapScale (⟨s, hs, hs1⟩ : RieszExponent) (N n) (k n) →
      Integrable (fun X : Configuration (N n) => selectedIncrement X (k n) r)
        (gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) (N n)) ∧
      (∫ X, |selectedIncrement X (k n) r|
        ∂gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) (N n)) ≤
          C * (r.natAbs : ℝ) ^ (3 * s / 4) := by
  obtain ⟨C, hC, hb⟩ := gapsDisc_increment_expectation_of_rigidity
    beta s hbeta hs hs1 hPL hRig
  refine ⟨C, hC, fun N k hk hvalid A hA => ?_⟩
  filter_upwards [hvalid, gapsDisc_increment_eventually_admissible
    (⟨s, hs, hs1⟩ : RieszExponent) N k hk hvalid A hA] with n hn hadm
  intro r hr
  have hN : 2 ≤ (N n : ℕ) := by omega
  exact hb (N n) hN (k n) r (hadm r hr).2.2

/-- Short increments divided by the gap scale converge to zero in probability.
The probability is expressed in `ℝ≥0∞`, without a finiteness conversion. -/
theorem gapsDisc_increment_probability_of_rigidity (beta s : ℝ) (hbeta : 0 < beta)
    (hs : 0 < s) (hs1 : s < 1) (hPL : External.PrekopaLeindler)
    (hRig : RigidityConclusion beta s hbeta hs hs1)
    {ι : Type*} {l : Filter ι} (N : ι → ℕ+) (k : ι → ℕ)
    (hk : Tendsto k l atTop)
    (hvalid : ∀ᶠ n in l, 1 ≤ k n ∧ k n ≤ (N n : ℕ) / 2)
    (A : ℝ) (hA : 0 < A) (r : ι → ℤ)
    (hr : ∀ᶠ n in l, ((r n).natAbs : ℝ) ≤ A *
      gapScale (⟨s, hs, hs1⟩ : RieszExponent) (N n) (k n))
    (η : ℝ) (hη : 0 < η) :
    Tendsto (fun n => gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) (N n)
      {X | η ≤ |selectedIncrement X (k n) (r n) /
        gapScale (⟨s, hs, hs1⟩ : RieszExponent) (N n) (k n)|}) l (𝓝 0) := by
  let σ : RieszExponent := ⟨s, hs, hs1⟩
  let P : Parameters := ⟨(beta, s), hbeta, hs, hs1⟩
  let b := fun n => gapScale σ (N n) (k n)
  obtain ⟨C, hC, hb⟩ := gapsDisc_increment_firstMoment_of_rigidity
    beta s hbeta hs hs1 hPL hRig
  have hbt : Tendsto b l atTop := gapsDisc_gapScale_tendsto_atTop σ N k hk hvalid
  have he : 0 < 1 - 3 * s / 4 := by linarith
  have hbound : Tendsto (fun n => ENNReal.ofReal
      ((C * A ^ (3 * s / 4) / η) * b n ^ (3 * s / 4 - 1))) l (𝓝 0) := by
    have ht := (tendsto_rpow_neg_atTop he).comp hbt
    have ht' := ht.const_mul (C * A ^ (3 * s / 4) / η)
    have ht'' : Tendsto (fun n => (C * A ^ (3 * s / 4) / η) *
        b n ^ (3 * s / 4 - 1)) l (𝓝 0) := by
      simpa only [Function.comp_apply, mul_zero,
        show -(1 - 3 * s / 4) = 3 * s / 4 - 1 by ring] using ht'
    simpa only [ENNReal.ofReal_zero, Function.comp_def] using
      (ENNReal.continuous_ofReal.tendsto 0).comp ht''
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbound
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [hvalid, hr, gapsDisc_increment_eventually_admissible σ N k hk hvalid A hA]
    with n hn hrn hadm
  have hbn : 0 < b n := gapsDisc_gapScale_pos σ (N n) (k n) hn.1 hn.2
  have hN : 2 ≤ (N n : ℕ) := by omega
  have hlen := (hadm (r n) hrn).2.2
  let f := fun X : Configuration (N n) => ENNReal.ofReal |selectedIncrement X (k n) (r n)|
  have hf : Measurable f :=
    (continuous_abs.measurable.comp (measurable_selectedIncrement _ _)).ennreal_ofReal
  have hmark := meas_ge_le_lintegral_div (μ := gibbsMeasure P (N n)) hf.aemeasurable
    (ne_of_gt (ENNReal.ofReal_pos.mpr (mul_pos hη hbn))) ENNReal.ofReal_ne_top
  have heq : {X : Configuration (N n) | η ≤ |selectedIncrement X (k n) (r n) / b n|} =
      {X | ENNReal.ofReal (η * b n) ≤ f X} := by
    ext X
    change (η ≤ |selectedIncrement X (k n) (r n) / b n|) ↔
      ENNReal.ofReal (η * b n) ≤ ENNReal.ofReal |selectedIncrement X (k n) (r n)|
    rw [abs_div, abs_of_pos hbn, le_div_iff₀ hbn,
      ENNReal.ofReal_le_ofReal_iff (abs_nonneg _)]
  rw [heq]
  apply hmark.trans
  have hnum : ((r n).natAbs : ℝ) ^ (3 * s / 4) ≤
      (A * b n) ^ (3 * s / 4) :=
    Real.rpow_le_rpow (by positivity) hrn (by positivity)
  have hbound' := (hb (N n) hN (k n) (r n) hlen).trans
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hnum hC.le))
  apply (ENNReal.div_le_div_right hbound' _).trans_eq
  rw [← ENNReal.ofReal_div_of_pos (mul_pos hη hbn)]
  congr 1
  rw [Real.mul_rpow hA.le hbn.le, Real.rpow_sub hbn, Real.rpow_one]
  field_simp

end Internal

end Riesz1

end
end
