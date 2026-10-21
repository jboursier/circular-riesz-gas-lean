/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Algebra.Order.Floor.Ring

/-!
# Periodic Bernoulli functions on unit intervals

Lemma 2.1, proof of equation (2.11). The sawtooth
`B_1(t) = t - ⌊t⌋ - 1/2` and its periodic antiderivative `B_2` satisfy, on every unit
interval `[M, M+1]` with `M ∈ ℕ`, a polynomial formula. Integrating by parts on these intervals
and summing over `[0, M]` by induction gives the finite Euler–Maclaurin identities used in
`Riesz1.EulerIntegralLimit`:

* the trapezoid identity `∫_0^M F + ∫_0^M B_1 F' = ∑_{n<M} (F n + F (n+1))/2`.
* the second-order identity `∫_0^M B_1 G = (G M - G 0)/12 - ∫_0^M B_2 G'`.

The functions `F` and `G` are only required to be differentiable on `[0, ∞)`.
-/

public section

open MeasureTheory Set Filter intervalIntegral

namespace Riesz1

/-- The sawtooth `B_1(t) = t - ⌊t⌋ - 1/2` of equation (2.11). -/
@[expose] noncomputable def sawtoothB1 (t : ℝ) : ℝ := t - ⌊t⌋ - 1 / 2

/-- The periodic second Bernoulli function `B_2(t) = ((t - ⌊t⌋)^2 - (t - ⌊t⌋) + 1/6)/2`. -/
@[expose] noncomputable def sawtoothB2 (t : ℝ) : ℝ := ((t - ⌊t⌋) ^ 2 - (t - ⌊t⌋) + 1 / 6) / 2

lemma sawtoothB1_measurable : Measurable sawtoothB1 := by
  unfold sawtoothB1
  fun_prop

lemma sawtoothB2_measurable : Measurable sawtoothB2 := by
  unfold sawtoothB2
  fun_prop

lemma abs_sawtoothB1_le (t : ℝ) : |sawtoothB1 t| ≤ 1 / 2 := by
  have h0 := Int.fract_nonneg t
  have h1 := Int.fract_lt_one t
  unfold Int.fract at h0 h1
  rw [abs_le]
  unfold sawtoothB1
  constructor <;> linarith

lemma abs_sawtoothB2_le (t : ℝ) : |sawtoothB2 t| ≤ 1 / 12 := by
  have h0 := Int.fract_nonneg t
  have h1 := Int.fract_lt_one t
  unfold Int.fract at h0 h1
  rw [abs_le]
  unfold sawtoothB2
  constructor
  · nlinarith [sq_nonneg (Int.fract t - 1 / 2)]
  · nlinarith [mul_nonneg h0 (sub_nonneg.2 h1.le)]

/-- Integer parts on a unit interval: `⌊t⌋ = M` for `M ≤ t < M + 1`. -/
lemma floor_eq_of_mem_Ico {M : ℕ} {t : ℝ} (h0 : (M : ℝ) ≤ t) (h1 : t < (M : ℝ) + 1) :
    ⌊t⌋ = (M : ℤ) :=
  Int.floor_eq_iff.mpr ⟨by exact_mod_cast h0, by push_cast; exact h1⟩

/-- On `[M, M+1)`, the sawtooth is the polynomial `t - M - 1/2`. -/
lemma sawtoothB1_of_mem_Ico {M : ℕ} {t : ℝ} (h0 : (M : ℝ) ≤ t) (h1 : t < (M : ℝ) + 1) :
    sawtoothB1 t = t - M - 1 / 2 := by
  unfold sawtoothB1
  rw [floor_eq_of_mem_Ico h0 h1]
  push_cast
  ring

/-- On the closed interval `[M, M+1]`, `B_2` is the polynomial `((t - M)^2 - (t - M) + 1/6)/2`:
the two formulas agree at the right endpoint, where both equal `1/12`. -/
lemma sawtoothB2_eq_poly {M : ℕ} {t : ℝ} (h0 : (M : ℝ) ≤ t) (h1 : t ≤ (M : ℝ) + 1) :
    sawtoothB2 t = ((t - M) ^ 2 - (t - M) + 1 / 6) / 2 := by
  rcases eq_or_lt_of_le h1 with h | h
  · subst h
    have hf : ⌊(M : ℝ) + 1⌋ = (M : ℤ) + 1 := by
      rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
    unfold sawtoothB2
    rw [hf]
    push_cast
    ring
  · unfold sawtoothB2
    rw [floor_eq_of_mem_Ico h0 h]
    push_cast
    ring

/-- The sawtooth and the polynomial agree on `(M, M+1)`, so they agree almost everywhere on
`[M, M+1]`. -/
lemma ae_sawtoothB1_piece (M : ℕ) :
    ∀ᵐ t : ℝ ∂volume, t ∈ uIoc (M : ℝ) ((M : ℝ) + 1) →
      sawtoothB1 t = t - M - 1 / 2 := by
  have hne : ∀ᵐ t : ℝ ∂volume, t ∉ ({(M : ℝ) + 1} : Set ℝ) :=
    (Set.countable_singleton _).ae_notMem volume
  filter_upwards [hne] with t ht hmem
  rw [uIoc_of_le (by linarith)] at hmem
  have hlt : t < (M : ℝ) + 1 := lt_of_le_of_ne hmem.2 (fun h => ht (by simp [h]))
  exact sawtoothB1_of_mem_Ico hmem.1.le hlt

/-- Integrability of a bounded measurable multiplier times a function continuous on the
interval. -/
lemma intervalIntegrable_bdd_mul {B : ℝ → ℝ} (hB : Measurable B) {C : ℝ}
    (hC : ∀ t, |B t| ≤ C) {G : ℝ → ℂ} {a b : ℝ} (hG : ContinuousOn G (uIcc a b)) :
    IntervalIntegrable (fun t => (B t : ℂ) * G t) volume a b := by
  rw [intervalIntegrable_iff]
  have hIcc : IntegrableOn G (Icc (min a b) (max a b)) volume := by
    apply ContinuousOn.integrableOn_Icc
    simpa [uIcc] using hG
  have hG' : IntegrableOn G (uIoc a b) volume :=
    (hIcc.mono_set (by
      intro t ht
      rw [uIoc] at ht
      exact ⟨by linarith [ht.1, min_le_left a b, min_le_right a b],
        by linarith [ht.2, le_max_left a b, le_max_right a b]⟩))
  have hbd : IntegrableOn (fun t => (B t : ℂ) * G t) (uIoc a b) volume := by
    refine Integrable.bdd_mul (c := C) hG' ?_ ?_
    · exact (Complex.continuous_ofReal.measurable.comp hB).aestronglyMeasurable
    · exact ae_of_all _ (fun t => by simpa using hC t)
  exact hbd

lemma intervalIntegrable_sawtoothB1_mul {G : ℝ → ℂ} {a b : ℝ} (hG : ContinuousOn G (uIcc a b)) :
    IntervalIntegrable (fun t => (sawtoothB1 t : ℂ) * G t) volume a b :=
  intervalIntegrable_bdd_mul sawtoothB1_measurable (fun t => abs_sawtoothB1_le t) hG

lemma intervalIntegrable_sawtoothB2_mul {G : ℝ → ℂ} {a b : ℝ} (hG : ContinuousOn G (uIcc a b)) :
    IntervalIntegrable (fun t => (sawtoothB2 t : ℂ) * G t) volume a b :=
  intervalIntegrable_bdd_mul sawtoothB2_measurable (fun t => abs_sawtoothB2_le t) hG

/-- The antiderivative `((t - M)^2 - (t - M) + 1/6)/2` of `t - M - 1/2`, as a complex-valued
function of a real variable. -/
lemma hasDerivAt_poly_B2 (M : ℕ) (t : ℝ) :
    HasDerivAt (fun y : ℝ => (((y - M) ^ 2 - (y - M) + 1 / 6) / 2 : ℝ) : ℝ → ℂ)
      ((t - M - 1 / 2 : ℝ) : ℂ) t := by
  have hl : HasDerivAt (fun y : ℝ => y - (M : ℝ)) 1 t := (hasDerivAt_id' t).sub_const _
  have h : HasDerivAt (fun y : ℝ => ((y - M) * (y - M) - (y - M) + 1 / 6) / 2)
      ((1 * (t - M) + (t - M) * 1 - 1) / 2) t :=
    (((hl.mul hl).sub hl).add_const (1 / 6 : ℝ)).div_const 2
  have hd : (1 * (t - M) + (t - M) * 1 - 1) / 2 = t - M - 1 / 2 := by ring
  have hfun : (fun y : ℝ => (((y - M) ^ 2 - (y - M) + 1 / 6) / 2 : ℝ)) =
      (fun y : ℝ => ((y - M) * (y - M) - (y - M) + 1 / 6) / 2) := by
    funext y
    ring
  have h2 : HasDerivAt (fun y : ℝ => (((y - M) ^ 2 - (y - M) + 1 / 6) / 2 : ℝ))
      (t - M - 1 / 2) t := by
    rw [hfun, ← hd]
    exact h
  exact h2.ofReal_comp

/-- Integration by parts on one unit interval, for the sawtooth against a derivative. -/
lemma integral_sawtoothB1_mul_deriv_piece (M : ℕ) {F F' : ℝ → ℂ}
    (hF : ∀ t : ℝ, 0 ≤ t → HasDerivAt F (F' t) t) (hF'c : ContinuousOn F' (Ici 0)) :
    ∫ t in (M : ℝ)..((M : ℝ) + 1), (sawtoothB1 t : ℂ) * F' t =
      (F ((M : ℝ) + 1) + F M) / 2 - ∫ t in (M : ℝ)..((M : ℝ) + 1), F t := by
  have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hsub : uIcc (M : ℝ) ((M : ℝ) + 1) ⊆ Ici 0 := by
    intro t ht
    rw [uIcc_of_le (by linarith)] at ht
    exact le_trans hM ht.1
  have hFc : ContinuousOn F (uIcc (M : ℝ) ((M : ℝ) + 1)) := fun t ht =>
    (hF t (hsub ht)).continuousAt.continuousWithinAt
  have hF'i : ContinuousOn F' (uIcc (M : ℝ) ((M : ℝ) + 1)) := hF'c.mono hsub
  have hcongr : ∫ t in (M : ℝ)..((M : ℝ) + 1), (sawtoothB1 t : ℂ) * F' t =
      ∫ t in (M : ℝ)..((M : ℝ) + 1), ((t - M - 1 / 2 : ℝ) : ℂ) * F' t := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [ae_sawtoothB1_piece M] with t ht hmem
    rw [ht hmem]
  rw [hcongr]
  have hu : ∀ t : ℝ, HasDerivAt (fun y : ℝ => ((y - M - 1 / 2 : ℝ) : ℂ)) 1 t := by
    intro t
    have hl : HasDerivAt (fun y : ℝ => y - (M : ℝ) - 1 / 2) 1 t :=
      ((hasDerivAt_id' t).sub_const _).sub_const _
    simpa using hl.ofReal_comp
  have hIoo : ∀ t ∈ Ioo (min (M : ℝ) ((M : ℝ) + 1)) (max (M : ℝ) ((M : ℝ) + 1)), 0 ≤ t := by
    intro t ht
    rw [min_eq_left (by linarith)] at ht
    linarith [ht.1]
  have hIBP := integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := fun y : ℝ => ((y - M - 1 / 2 : ℝ) : ℂ)) (v := F) (u' := fun _ => (1 : ℂ)) (v' := F')
    (a := (M : ℝ)) (b := (M : ℝ) + 1)
    (by fun_prop) hFc
    (fun t _ => hu t)
    (fun t ht => hF t (hIoo t ht))
    (by simp)
    hF'i.intervalIntegrable
  rw [hIBP]
  simp only [one_mul]
  push_cast
  ring

/-- Integration by parts on one unit interval, against the second Bernoulli function. -/
lemma integral_sawtoothB1_mul_piece (M : ℕ) {G G' : ℝ → ℂ}
    (hG : ∀ t : ℝ, 0 ≤ t → HasDerivAt G (G' t) t) (hG'c : ContinuousOn G' (Ici 0)) :
    ∫ t in (M : ℝ)..((M : ℝ) + 1), (sawtoothB1 t : ℂ) * G t =
      (G ((M : ℝ) + 1) - G M) / 12 - ∫ t in (M : ℝ)..((M : ℝ) + 1), (sawtoothB2 t : ℂ) * G' t := by
  have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hsub : uIcc (M : ℝ) ((M : ℝ) + 1) ⊆ Ici 0 := by
    intro t ht
    rw [uIcc_of_le (by linarith)] at ht
    exact le_trans hM ht.1
  have hGc : ContinuousOn G (uIcc (M : ℝ) ((M : ℝ) + 1)) := fun t ht =>
    (hG t (hsub ht)).continuousAt.continuousWithinAt
  have hG'i : ContinuousOn G' (uIcc (M : ℝ) ((M : ℝ) + 1)) := hG'c.mono hsub
  have hIoo : ∀ t ∈ Ioo (min (M : ℝ) ((M : ℝ) + 1)) (max (M : ℝ) ((M : ℝ) + 1)), 0 ≤ t := by
    intro t ht
    rw [min_eq_left (by linarith)] at ht
    linarith [ht.1]
  have hcongr1 : ∫ t in (M : ℝ)..((M : ℝ) + 1), (sawtoothB1 t : ℂ) * G t =
      ∫ t in (M : ℝ)..((M : ℝ) + 1), G t * ((t - M - 1 / 2 : ℝ) : ℂ) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [ae_sawtoothB1_piece M] with t ht hmem
    rw [ht hmem, mul_comm]
  have hcongr2 : ∫ t in (M : ℝ)..((M : ℝ) + 1), (sawtoothB2 t : ℂ) * G' t =
      ∫ t in (M : ℝ)..((M : ℝ) + 1), G' t *
        ((((t - M) ^ 2 - (t - M) + 1 / 6) / 2 : ℝ) : ℂ) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by linarith)] at ht
    simp only
    rw [sawtoothB2_eq_poly ht.1 ht.2, mul_comm]
  have hv : ContinuousOn (fun y : ℝ => ((((y - M) ^ 2 - (y - M) + 1 / 6) / 2 : ℝ) : ℂ))
      (uIcc (M : ℝ) ((M : ℝ) + 1)) :=
    Continuous.continuousOn (by fun_prop)
  have hw' : ContinuousOn (fun t : ℝ => ((t - M - 1 / 2 : ℝ) : ℂ)) (uIcc (M : ℝ) ((M : ℝ) + 1)) :=
    Continuous.continuousOn (by fun_prop)
  have hIBP := integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := G) (v := fun y : ℝ => ((((y - M) ^ 2 - (y - M) + 1 / 6) / 2 : ℝ) : ℂ))
    (u' := G') (v' := fun t : ℝ => ((t - M - 1 / 2 : ℝ) : ℂ))
    (a := (M : ℝ)) (b := (M : ℝ) + 1) hGc hv
    (fun t ht => hG t (hIoo t ht))
    (fun t _ => hasDerivAt_poly_B2 M t)
    hG'i.intervalIntegrable hw'.intervalIntegrable
  have hw1 : ((((((M : ℝ) + 1) - M) ^ 2 - (((M : ℝ) + 1) - M) + 1 / 6) / 2 : ℝ) : ℂ) = 1 / 12 := by
    push_cast
    ring
  have hw0 : ((((((M : ℝ)) - M) ^ 2 - (((M : ℝ)) - M) + 1 / 6) / 2 : ℝ) : ℂ) = 1 / 12 := by
    push_cast
    ring
  rw [hcongr1, hcongr2, hIBP]
  rw [hw1, hw0]
  ring

/-- The finite trapezoid identity for `∫_0^M F + ∫_0^M B_1 F'`: the sum of the trapezoid values
`(F n + F (n+1))/2` over `n < M`. -/
lemma sum_trapezoid_eq {F F' : ℝ → ℂ}
    (hF : ∀ t : ℝ, 0 ≤ t → HasDerivAt F (F' t) t) (hF'c : ContinuousOn F' (Ici 0)) (M : ℕ) :
    (∫ t in (0 : ℝ)..(M : ℝ), F t) + ∫ t in (0 : ℝ)..(M : ℝ), (sawtoothB1 t : ℂ) * F' t =
      ∑ n ∈ Finset.range M, (F n + F ((n : ℝ) + 1)) / 2 := by
  induction M with
  | zero => simp
  | succ M ih =>
    have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    have hsubA : uIcc (0 : ℝ) (M : ℝ) ⊆ Ici 0 := by
      intro t ht
      rw [uIcc_of_le hM] at ht
      exact ht.1
    have hsubB : uIcc (M : ℝ) ((M : ℝ) + 1) ⊆ Ici 0 := by
      intro t ht
      rw [uIcc_of_le (by linarith)] at ht
      exact le_trans hM ht.1
    have hFA : ContinuousOn F (uIcc (0 : ℝ) (M : ℝ)) := fun t ht =>
      (hF t (hsubA ht)).continuousAt.continuousWithinAt
    have hFB : ContinuousOn F (uIcc (M : ℝ) ((M : ℝ) + 1)) := fun t ht =>
      (hF t (hsubB ht)).continuousAt.continuousWithinAt
    have hsplit1 := intervalIntegral.integral_add_adjacent_intervals
      (μ := volume) (f := F) (a := 0) (b := (M : ℝ)) (c := (M : ℝ) + 1)
      (hFA.intervalIntegrable (μ := volume)) (hFB.intervalIntegrable (μ := volume))
    have hsplit2 := intervalIntegral.integral_add_adjacent_intervals
      (μ := volume) (f := fun t : ℝ => (sawtoothB1 t : ℂ) * F' t) (a := 0) (b := (M : ℝ)) (c := (M : ℝ) + 1)
      (intervalIntegrable_sawtoothB1_mul ((hF'c.mono hsubA)))
      (intervalIntegrable_sawtoothB1_mul ((hF'c.mono hsubB)))
    push_cast
    rw [← hsplit1, ← hsplit2, integral_sawtoothB1_mul_deriv_piece M hF hF'c,
      Finset.sum_range_succ]
    linear_combination ih

/-- The finite second-order identity: `∫_0^M B_1 G = (G M - G 0)/12 - ∫_0^M B_2 G'`. -/
lemma sum_sawtoothB1_mul_eq {G G' : ℝ → ℂ}
    (hG : ∀ t : ℝ, 0 ≤ t → HasDerivAt G (G' t) t) (hG'c : ContinuousOn G' (Ici 0)) (M : ℕ) :
    ∫ t in (0 : ℝ)..(M : ℝ), (sawtoothB1 t : ℂ) * G t =
      (G M - G 0) / 12 - ∫ t in (0 : ℝ)..(M : ℝ), (sawtoothB2 t : ℂ) * G' t := by
  induction M with
  | zero => simp
  | succ M ih =>
    have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    have hsubA : uIcc (0 : ℝ) (M : ℝ) ⊆ Ici 0 := by
      intro t ht
      rw [uIcc_of_le hM] at ht
      exact ht.1
    have hsubB : uIcc (M : ℝ) ((M : ℝ) + 1) ⊆ Ici 0 := by
      intro t ht
      rw [uIcc_of_le (by linarith)] at ht
      exact le_trans hM ht.1
    have hsplit1 := intervalIntegral.integral_add_adjacent_intervals
      (μ := volume) (f := fun t : ℝ => (sawtoothB1 t : ℂ) * G t) (a := 0) (b := (M : ℝ)) (c := (M : ℝ) + 1)
      (intervalIntegrable_sawtoothB1_mul (fun t ht => (hG t (hsubA ht)).continuousAt.continuousWithinAt))
      (intervalIntegrable_sawtoothB1_mul (fun t ht => (hG t (hsubB ht)).continuousAt.continuousWithinAt))
    have hsplit2 := intervalIntegral.integral_add_adjacent_intervals
      (μ := volume) (f := fun t : ℝ => (sawtoothB2 t : ℂ) * G' t) (a := 0) (b := (M : ℝ)) (c := (M : ℝ) + 1)
      (intervalIntegrable_sawtoothB2_mul ((hG'c.mono hsubA)))
      (intervalIntegrable_sawtoothB2_mul ((hG'c.mono hsubB)))
    push_cast
    rw [← hsplit1, ← hsplit2, integral_sawtoothB1_mul_piece M hG hG'c, ih]
    ring

end Riesz1

end
