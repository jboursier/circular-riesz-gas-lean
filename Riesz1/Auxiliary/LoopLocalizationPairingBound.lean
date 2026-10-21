/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopLocalizationAmplitude
public import Riesz1.Auxiliary.LoopExteriorRegularity
public import Riesz1.Auxiliary.LoopCutoffPairBound

/-!
# The deterministic exterior cross-pairing bound

The localization part of Lemma 5.8: the signed cross pairing is
bounded by the amplitude, the number of local labels, the background length,
and the actual exterior-force supremum on its spatial carrier.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace Riesz1

/-- Local lifts cannot enter a translated copy of the central support on the
good event. Both endpoint barriers are needed for this assertion. -/
theorem loopLocalization_local_lift_barriers {N : ℕ+} {ℓ γ : ℝ}
    (_hK : 1 ≤ (N : ℝ) * ℓ) (_hγ : 0 ≤ γ) (hP : GradPartial N ℓ γ)
    {X : LoopPrecedingConfiguration N} (hX : X ∈ loopExteriorGood N ℓ γ)
    {i : ℤ} (hi : i ∈ gradLabels N ℓ γ) :
    gradM N ℓ γ / 2 - N ≤ loopPrecedingLift X i ∧
      loopPrecedingLift X i ≤ N - gradM N ℓ γ / 2 := by
  have hnN : 2 * ⌊gradM N ℓ γ⌋ < (N : ℤ) := by
    have hf := Int.floor_le (gradM N ℓ γ)
    have hPr : gradM N ℓ γ < (N : ℝ) / 8 := hP
    have : (2 : ℝ) * (⌊gradM N ℓ γ⌋ : ℤ) < N := by linarith
    exact_mod_cast this
  simp only [gradLabels, hP, ↓reduceIte, Finset.mem_Icc] at hi
  have hl := (loopPrecedingLift_strictMono X).monotone
    (show ⌊gradM N ℓ γ⌋ ≤ i + N by omega)
  have hr := (loopPrecedingLift_strictMono X).monotone
    (show i ≤ -⌊gradM N ℓ γ⌋ + N by omega)
  rw [loopPrecedingLift_add_N] at hl hr
  constructor <;> linarith [hX.2.1, hX.2.2]

/-- Outside the real central interval a local lift sees zero cutoff transport,
even when the lift lies outside the centered fundamental domain. -/
theorem loopLocalization_local_transport_zero {N : ℕ+} {ℓ γ : ℝ}
    (hℓ : 0 < ℓ) (hK : 1 ≤ (N : ℝ) * ℓ) (hγ : 0 ≤ γ)
    (hP : GradPartial N ℓ γ) {χ : ℝ → ℝ}
    (hχs : tsupport χ ⊆ Ioo (-(1 / 4)) (1 / 4)) (ψ : ℝ → ℝ)
    {X : LoopPrecedingConfiguration N} (hX : X ∈ loopExteriorGood N ℓ γ)
    {i : ℤ} (hi : i ∈ gradLabels N ℓ γ)
    (hz : loopPrecedingLift X i ∉ Icc (-gradM N ℓ γ / 4) (gradM N ℓ γ / 4)) :
    loopLocalTransport χ N ℓ γ ψ (loopPrecedingLift X i) = 0 := by
  have hM : 0 ≤ gradM N ℓ γ := (Real.one_le_rpow hK hγ).trans' zero_le_one
  have hb := loopLocalization_local_lift_barriers hK hγ hP hX hi
  have hout : gradM N ℓ γ / 4 ≤ |loopPrecedingLift X i| := by
    by_contra! h
    exact hz (by simpa only [mem_Icc, neg_div] using abs_le.mp h.le)
  apply loopLocalTransport_zero_of_circDist hℓ hP hχs ψ
  change gradM N ℓ γ / 4 ≤ latticeDist (N : ℝ) (loopPrecedingLift X i)
  exact loopExterior_latticeDist_lower (by exact_mod_cast N.pos) hout
    (by
      have hab : |loopPrecedingLift X i| ≤ (N : ℝ) - gradM N ℓ γ / 2 :=
        abs_le.mpr ⟨by linarith [hb.1], hb.2⟩
      linarith)

/-- On the local background the cutoff has no support outside the real
central interval. -/
theorem loopLocalization_background_transport_zero {N : ℕ+} {ℓ γ : ℝ}
    (hℓ : 0 < ℓ) (hP : GradPartial N ℓ γ) {χ : ℝ → ℝ}
    (hχs : tsupport χ ⊆ Ioo (-(1 / 4)) (1 / 4)) (ψ : ℝ → ℝ)
    {z : ℝ} (hz : z ∈ Icc (-gradM N ℓ γ) (gradM N ℓ γ))
    (hout : z ∉ Icc (-gradM N ℓ γ / 4) (gradM N ℓ γ / 4)) :
    loopLocalTransport χ N ℓ γ ψ z = 0 := by
  have hM : 0 < gradM N ℓ γ := Real.rpow_pos_of_pos
    (mul_pos (by exact_mod_cast N.pos) hℓ) γ
  apply loopLocalTransport_zero_of_circDist hℓ hP hχs ψ
  change gradM N ℓ γ / 4 ≤ latticeDist (N : ℝ) z
  apply loopExterior_latticeDist_lower (by exact_mod_cast N.pos)
  · by_contra! h
    exact hout (by simpa only [mem_Icc, neg_div] using abs_le.mp h.le)
  · have hPr : gradM N ℓ γ < (N : ℝ) / 8 := hP
    have hab : |z| ≤ gradM N ℓ γ := abs_le.mpr hz
    linarith

/-- The exterior cross kernel at a central spatial point is exactly the
cutoff transport times the force, on the force's original carrier. -/
theorem loopLocalization_cross_kernel_eq_force {s : ℝ} {N : ℕ+} {ℓ γ : ℝ}
    (hℓ : 0 < ℓ) (hK : 1 ≤ (N : ℝ) * ℓ) (hγ : 0 ≤ γ)
    (hP : GradPartial N ℓ γ) {χ : ℝ → ℝ}
    (hχs : tsupport χ ⊆ Ioo (-(1 / 4)) (1 / 4)) (ψ : ℝ → ℝ)
    (X : {X : LoopPrecedingConfiguration N // X ∈ loopExteriorGood N ℓ γ})
    (z : Icc (-gradM N ℓ γ / 4) (gradM N ℓ γ / 4)) :
    (∑ j ∈ loopExteriorLabels N ℓ γ,
      loopArcKernel s N (loopLocalTransport χ N ℓ γ ψ) z.val (loopPrecedingLift X.val j)) -
      (∫ u in loopExteriorBackground N ℓ γ,
        loopArcKernel s N (loopLocalTransport χ N ℓ γ ψ) z.val u) =
    loopLocalTransport χ N ℓ γ ψ z.val * loopExteriorForce s N ℓ γ X z := by
  have ha : (∑ j ∈ loopExteriorLabels N ℓ γ,
      loopArcKernel s N (loopLocalTransport χ N ℓ γ ψ) z.val (loopPrecedingLift X.val j)) =
      loopLocalTransport χ N ℓ γ ψ z.val *
        ∑ j ∈ loopExteriorLabels N ℓ γ, deriv (loopArcG s N) (z.val - loopPrecedingLift X.val j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [loopArcKernel, loopLocalTransport_zero_exterior hℓ hK hγ hP hχs ψ X.property hj,
      sub_zero]
  have hb : (∫ u in loopExteriorBackground N ℓ γ,
      loopArcKernel s N (loopLocalTransport χ N ℓ γ ψ) z.val u) =
      loopLocalTransport χ N ℓ γ ψ z.val * ∫ u in loopExteriorBackground N ℓ γ,
        deriv (loopArcG s N) (z.val - u) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun (measurableSet_loopExteriorBackground N ℓ γ)
    intro u hu
    rw [loopArcKernel, loopLocalTransport_zero_exteriorBackground hℓ hP hχs ψ hu, sub_zero]
  rw [ha, hb, loopExteriorForce, mul_sub]

/-- The actual signed cross pairing is bounded by `20 A C₀ K M` times the
spatial exterior-force supremum. Here `A` is the explicit amplitude constant.
No extension of the force off its spatial carrier occurs in this statement. -/
theorem loopLocalization_cross_pairing_bound {s α : ℝ} (hs : 0 < s) (hs1 : s < 1)
    (hα2 : α < s / 2) {N : ℕ+} {ℓ γ C0 : ℝ}
    (hℓ : 0 < ℓ) (hK : 1 ≤ (N : ℝ) * ℓ) (hγ : 0 ≤ γ)
    (hP : GradPartial N ℓ γ) (hC0 : 0 ≤ C0) {χ ψ : ℝ → ℝ}
    (hχs : tsupport χ ⊆ Ioo (-(1 / 4)) (1 / 4)) (hχ01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1)
    (hψ : ContDiff ℝ ∞ ψ) (hp : Function.Periodic ψ ℓ⁻¹)
    (hd : ∀ t, |deriv ψ t| ≤
      C0 * gradWeightOne s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ t)
    (X : {X : LoopPrecedingConfiguration N // X ∈ loopExteriorGood N ℓ γ}) :
    let b0 := loopLocalTransport χ N ℓ γ ψ
    let q := fun z => (∑ j ∈ loopExteriorLabels N ℓ γ,
      loopArcKernel s N b0 z (loopPrecedingLift X.val j)) -
      ∫ u in loopExteriorBackground N ℓ γ, loopArcKernel s N b0 z u
    |2 * ((∑ i ∈ gradLabels N ℓ γ, q (loopPrecedingLift X.val i)) -
      ∫ z in -gradM N ℓ γ..gradM N ℓ γ, q z)| ≤
    20 * ((1 + 1 / (1 - (1 - s + α))) + 1 / (1 - s)) * C0 * ((N : ℝ) * ℓ) *
      gradM N ℓ γ * (⨆ z, |loopExteriorForce s N ℓ γ X z|) := by
  classical
  let b0 := loopLocalTransport χ N ℓ γ ψ
  let q := fun z => (∑ j ∈ loopExteriorLabels N ℓ γ,
    loopArcKernel s N b0 z (loopPrecedingLift X.val j)) -
    ∫ u in loopExteriorBackground N ℓ γ, loopArcKernel s N b0 z u
  let A := (1 + 1 / (1 - (1 - s + α))) + 1 / (1 - s)
  let H := ⨆ z, |loopExteriorForce s N ℓ γ X z|
  let D := A * C0 * ((N : ℝ) * ℓ) * H
  have hM : 0 < gradM N ℓ γ := lt_of_lt_of_le zero_lt_one (Real.one_le_rpow hK hγ)
  have hA : 0 ≤ A := by
    have ha : 0 < 1 - (1 - s + α) := by linarith
    have hs0 : 0 < 1 - s := by linarith
    dsimp [A]
    positivity
  have hH : 0 ≤ H := by
    let z0 : Icc (-gradM N ℓ γ / 4) (gradM N ℓ γ / 4) :=
      ⟨0, by constructor <;> linarith⟩
    exact (abs_nonneg _).trans (le_ciSup (loopExteriorForce_max hs hs1 hK hγ hP X).1 z0)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hzero {z : ℝ} (hz : b0 z = 0) : q z = 0 := by
    have ha : (∑ j ∈ loopExteriorLabels N ℓ γ,
        loopArcKernel s N b0 z (loopPrecedingLift X.val j)) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      rw [loopArcKernel, hz,
        show b0 (loopPrecedingLift X.val j) = 0 from
          loopLocalTransport_zero_exterior hℓ hK hγ hP hχs ψ X.property hj,
        sub_self, zero_mul]
    have hb : (∫ u in loopExteriorBackground N ℓ γ, loopArcKernel s N b0 z u) = 0 := by
      apply setIntegral_eq_zero_of_forall_eq_zero
      intro u hu
      rw [loopArcKernel, hz, show b0 u = 0 from
        loopLocalTransport_zero_exteriorBackground hℓ hP hχs ψ hu, sub_self, zero_mul]
    exact sub_eq_zero.mpr (ha.trans hb.symm)
  have hcentral {z : ℝ} (hz : z ∈ Icc (-gradM N ℓ γ / 4) (gradM N ℓ γ / 4)) :
      |q z| ≤ D := by
    rw [show q z = b0 z * loopExteriorForce s N ℓ γ X ⟨z, hz⟩ from
      loopLocalization_cross_kernel_eq_force hℓ hK hγ hP hχs ψ X ⟨z, hz⟩, abs_mul]
    exact mul_le_mul (loopLocalTransport_amplitude hs hs1 hα2 hℓ hK hP hC0
      hχ01 hψ hp hd z) (le_ciSup (loopExteriorForce_max hs hs1 hK hγ hP X).1 ⟨z, hz⟩)
      (abs_nonneg _) (by positivity)
  have hlocal (i : ℤ) (hi : i ∈ gradLabels N ℓ γ) : |q (loopPrecedingLift X.val i)| ≤ D := by
    by_cases hz : loopPrecedingLift X.val i ∈ Icc (-gradM N ℓ γ / 4) (gradM N ℓ γ / 4)
    · exact hcentral hz
    · rw [hzero (loopLocalization_local_transport_zero hℓ hK hγ hP hχs ψ X.property hi hz), abs_zero]
      exact hD
  have hbg (z : ℝ) (hz : z ∈ Icc (-gradM N ℓ γ) (gradM N ℓ γ)) : |q z| ≤ D := by
    by_cases hc : z ∈ Icc (-gradM N ℓ γ / 4) (gradM N ℓ γ / 4)
    · exact hcentral hc
    · rw [hzero (loopLocalization_background_transport_zero hℓ hP hχs ψ hz hc), abs_zero]
      exact hD
  have hsum : |∑ i ∈ gradLabels N ℓ γ, q (loopPrecedingLift X.val i)| ≤
      8 * gradM N ℓ γ * D := by
    calc
      _ ≤ ∑ i ∈ gradLabels N ℓ γ, |q (loopPrecedingLift X.val i)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ gradLabels N ℓ γ, D := Finset.sum_le_sum hlocal
      _ = ((gradLabels N ℓ γ).card : ℝ) * D := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (card_gradLabels_le hK hγ) hD
  have hint : |∫ z in -gradM N ℓ γ..gradM N ℓ γ, q z| ≤ 2 * gradM N ℓ γ * D := by
    have hbound : ∀ z ∈ uIoc (-gradM N ℓ γ) (gradM N ℓ γ), ‖q z‖ ≤ D := by
      intro z hz
      rw [Real.norm_eq_abs]
      exact hbg z ((uIoc_of_le
        (by linarith : -gradM N ℓ γ ≤ gradM N ℓ γ) ▸ hz).imp le_of_lt id)
    have hi := intervalIntegral.norm_integral_le_of_norm_le_const hbound
    have h2M : 0 < 2 * gradM N ℓ γ := mul_pos (by norm_num) hM
    simpa only [Real.norm_eq_abs, sub_neg_eq_add, ← two_mul,
      abs_of_pos h2M, mul_comm] using hi
  change |2 * ((∑ i ∈ gradLabels N ℓ γ, q (loopPrecedingLift X.val i)) -
    ∫ z in -gradM N ℓ γ..gradM N ℓ γ, q z)| ≤ _
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    _ ≤ 2 * (|∑ i ∈ gradLabels N ℓ γ, q (loopPrecedingLift X.val i)| +
        |∫ z in -gradM N ℓ γ..gradM N ℓ γ, q z|) :=
      mul_le_mul_of_nonneg_left (abs_sub _ _) (by norm_num)
    _ ≤ 2 * (8 * gradM N ℓ γ * D + 2 * gradM N ℓ γ * D) := by gcongr
    _ = _ := by dsimp [D, A, H]; ring

end Riesz1

end
