/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.PuncturedTransportBounds

/-!
# Uniform first derivative estimates on a finite punctured interval

A fixed finite set of real marks, a bound on a primitive, and a second derivative
power bound give uniform pointwise and integral bounds for the first derivative.
All constants precede the function. These are analytic helpers for
Lemma 5.1.
-/

public section

open MeasureTheory Set intervalIntegral

namespace Riesz1.PuncturedDerivative

/-- Two endpoint singularities: the first derivative and its integral are controlled
uniformly over bounded primitives with the same second derivative bound. -/
theorem uniform_deriv_bounds_two_endpoints {a z b C M : ℝ}
    (hb : 0 < b) (hb1 : b < 1) (hC : 0 ≤ C) (hM0 : 0 ≤ M) (haz : a < z) :
    ∃ K : ℝ, 0 < K ∧ ∀ f : ℝ → ℝ,
      (∀ x ∈ Ioo a z, DifferentiableAt ℝ f x) →
      (∀ x ∈ Ioo a z, DifferentiableAt ℝ (deriv f) x) →
      (∀ x ∈ Ioo a z, |f x| ≤ M) →
      (∀ x ∈ Ioo a z, |deriv (deriv f) x| ≤
        C * ((x - a) ^ (-1 - b) + (z - x) ^ (-1 - b))) →
      (∀ x ∈ Ioo a z, |deriv f x| ≤
        K * ((x - a) ^ (-b) + (z - x) ^ (-b))) ∧
      IntervalIntegrable (deriv f) volume a z ∧
      (∫ x in a..z, |deriv f x|) ≤ K := by
  let R := (z - a) / 2
  have hR : 0 < R := by dsimp [R]; linarith
  let Q := 2 * M / ((z - a) / 4) +
    (2 * C * ((z - a) / 4) ^ (-1 - b)) * ((z - a) / 4)
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  let H := Q * R ^ b + (2 * C) / b
  have hH : 0 ≤ H := by dsimp [H]; positivity
  let J := 2 * H * R ^ (1 - b) / (1 - b)
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  refine ⟨H + J + 1, by positivity, fun f hf hq hM hbound => ?_⟩
  have hleft : ∀ t ∈ Ioc 0 R, a + t ∈ Ioo a z := by
    intro t ht
    constructor <;> dsimp [R] at * <;> linarith [ht.1, ht.2]
  have hright : ∀ t ∈ Ioc 0 R, z - t ∈ Ioo a z := by
    intro t ht
    constructor <;> dsimp [R] at * <;> linarith [ht.1, ht.2]
  have hdl : ∀ t ∈ Ioc 0 R, DifferentiableAt ℝ (fun u => deriv f (a + u)) t := by
    intro t ht
    exact (hq (a + t) (hleft t ht)).comp t (by fun_prop)
  have hdr : ∀ t ∈ Ioc 0 R, DifferentiableAt ℝ (fun u => deriv f (z - u)) t := by
    intro t ht
    exact (hq (z - t) (hright t ht)).comp t (by fun_prop)
  have hbl : ∀ t ∈ Ioc 0 R,
      |deriv (fun u => deriv f (a + u)) t| ≤ (2 * C) * t ^ (-1 - b) := by
    intro t ht
    rw [deriv_comp_const_add]
    have hp : (z - (a + t)) ^ (-1 - b) ≤ t ^ (-1 - b) :=
      Real.rpow_le_rpow_of_nonpos ht.1 (by dsimp [R] at ht; linarith [ht.2]) (by linarith)
    have he := hbound (a + t) (hleft t ht)
    simp only [add_sub_cancel_left] at he
    nlinarith [mul_le_mul_of_nonneg_left hp hC]
  have hbr : ∀ t ∈ Ioc 0 R,
      |deriv (fun u => deriv f (z - u)) t| ≤ (2 * C) * t ^ (-1 - b) := by
    intro t ht
    rw [deriv_comp_const_sub, abs_neg]
    have hp : (z - t - a) ^ (-1 - b) ≤ t ^ (-1 - b) :=
      Real.rpow_le_rpow_of_nonpos ht.1 (by dsimp [R] at ht; linarith [ht.2]) (by linarith)
    have he := hbound (z - t) (hright t ht)
    rw [sub_sub_cancel] at he
    nlinarith [mul_le_mul_of_nonneg_left hp hC]
  have href : |deriv f ((a + z) / 2)| ≤ Q :=
    abs_deriv_midpoint_le hb hC haz hf hq hM hbound
  have hraw {q : ℝ → ℝ}
      (hd : ∀ t ∈ Ioc 0 R, DifferentiableAt ℝ q t)
      (hbd : ∀ t ∈ Ioc 0 R, |deriv q t| ≤ (2 * C) * t ^ (-1 - b))
      (hqr : |q R| ≤ Q) (t : ℝ) (ht : t ∈ Ioc 0 R) : |q t| ≤ H * t ^ (-b) := by
    have hh := abs_le_rpow_of_deriv_bound hb (by positivity : 0 ≤ 2 * C) hR hd hbd ht
    have hp : 1 ≤ R ^ b * t ^ (-b) := by
      have hc : t ^ b * t ^ (-b) = 1 := by
        rw [← Real.rpow_add ht.1, add_neg_cancel, Real.rpow_zero]
      rw [← hc]
      exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow ht.1.le ht.2 hb.le) (Real.rpow_nonneg ht.1.le _)
    dsimp [H]
    nlinarith [mul_le_mul_of_nonneg_left hp hQ]
  have hpl := hraw hdl hbl (by simpa only [show a + R = (a + z) / 2 by dsimp [R]; ring] using href)
  have hpr := hraw hdr hbr (by simpa only [show z - R = (a + z) / 2 by dsimp [R]; ring] using href)
  have hil : IntervalIntegrable (fun t => deriv f (a + t)) volume 0 R := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hR.le]
    exact integrableOn_of_deriv_rpow_bound hb hb1 (by positivity) hR hdl hbl
  have hir : IntervalIntegrable (fun t => deriv f (z - t)) volume 0 R := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hR.le]
    exact integrableOn_of_deriv_rpow_bound hb hb1 (by positivity) hR hdr hbr
  have hi₁ : IntervalIntegrable (deriv f) volume a (a + R) := by
    simpa [add_comm, add_left_comm, add_assoc] using hil.comp_add_left (-a)
  have hi₂ : IntervalIntegrable (deriv f) volume (a + R) z := by
    simpa only [show z - R = a + R by dsimp [R]; ring, sub_zero, sub_sub_cancel] using (hir.comp_sub_left z).symm
  refine ⟨?_, hi₁.trans hi₂, ?_⟩
  · intro x hx
    have hnonneg : 0 ≤ (x - a) ^ (-b) + (z - x) ^ (-b) :=
      add_nonneg (Real.rpow_nonneg (by linarith [hx.1]) _)
        (Real.rpow_nonneg (by linarith [hx.2]) _)
    apply le_trans _ (mul_le_mul_of_nonneg_right (show H ≤ H + J + 1 by linarith) hnonneg)
    rcases le_total x (a + R) with hxR | hxR
    · have ht : x - a ∈ Ioc 0 R := ⟨by linarith [hx.1], by linarith⟩
      have hh := hpl (x - a) ht
      simp only [add_sub_cancel] at hh
      exact hh.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (Real.rpow_nonneg (by linarith [hx.2]) _)) hH)
    · have ht : z - x ∈ Ioc 0 R := ⟨by linarith [hx.2], by dsimp [R] at *; linarith⟩
      have hh := hpr (z - x) ht
      simp only [sub_sub_cancel] at hh
      exact hh.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (Real.rpow_nonneg (by linarith [hx.1]) _)) hH)
  · have hpow : IntervalIntegrable (fun t : ℝ => H * t ^ (-b)) volume 0 R :=
      (intervalIntegrable_rpow' (by linarith : -1 < -b)).const_mul H
    have hval : (∫ t in (0 : ℝ)..R, H * t ^ (-b)) = H * R ^ (1 - b) / (1 - b) := by
      rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith : -1 < -b)),
        Real.zero_rpow (by linarith : -b + 1 ≠ 0), sub_zero]
      rw [show -b + 1 = 1 - b by ring]
      ring
    have hl := integral_mono_on_of_le_Ioo hR.le hil.abs hpow
      (fun t ht => hpl t ⟨ht.1, ht.2.le⟩)
    have hr := integral_mono_on_of_le_Ioo hR.le hir.abs hpow
      (fun t ht => hpr t ⟨ht.1, ht.2.le⟩)
    rw [hval, intervalIntegral.integral_comp_add_left (fun t => |deriv f t|) a] at hl
    rw [hval, intervalIntegral.integral_comp_sub_left (fun t => |deriv f t|) z] at hr
    simp only [add_zero, sub_zero, show z - R = a + R by dsimp [R]; ring] at hl hr
    rw [← integral_add_adjacent_intervals hi₁.abs hi₂.abs]
    have hs := add_le_add hl hr
    have heq : H * R ^ (1 - b) / (1 - b) + H * R ^ (1 - b) / (1 - b) = J := by
      dsimp [J]
      ring
    rw [heq] at hs
    exact hs.trans (by linarith)


/-- Fixed finite real marks: uniform power envelopes and integral bounds for the first
 derivative. Endpoints are included in the envelope to permit induction by subdivision. -/
theorem uniform_deriv_bounds_finite {b M : ℝ}
    (hb : 0 < b) (hb1 : b < 1) (hM0 : 0 ≤ M) (S : Finset ℝ)
    {a z C : ℝ} (hC : 0 ≤ C) (haz : a < z) :
    ∃ K : ℝ, 0 < K ∧ ∀ f : ℝ → ℝ,
      (∀ x ∈ Ioo a z \ (S : Set ℝ), DifferentiableAt ℝ f x) →
      (∀ x ∈ Ioo a z \ (S : Set ℝ), DifferentiableAt ℝ (deriv f) x) →
      (∀ x ∈ Ioo a z \ (S : Set ℝ), |f x| ≤ M) →
      (∀ x ∈ Ioo a z \ (S : Set ℝ), |deriv (deriv f) x| ≤
        C * ((x - a) ^ (-1 - b) + (z - x) ^ (-1 - b) +
          ∑ y ∈ S, |x - y| ^ (-1 - b))) →
      (∀ x ∈ Ioo a z \ (S : Set ℝ), |deriv f x| ≤
        K * ((x - a) ^ (-b) + (z - x) ^ (-b) + ∑ y ∈ S, |x - y| ^ (-b))) ∧
      IntervalIntegrable (deriv f) volume a z ∧
      (∫ x in a..z, |deriv f x|) ≤ K := by
  classical
  induction S using Finset.induction_on generalizing a z C with
  | empty =>
    simpa using uniform_deriv_bounds_two_endpoints hb hb1 hC hM0 haz
  | @insert y S hyS ih =>
    have hrestrict {q : ℝ → ℝ}
        (hq : ∀ x ∈ Ioo a z \ (↑(insert y S) : Set ℝ), DifferentiableAt ℝ q x)
        (hbound : ∀ x ∈ Ioo a z \ (↑(insert y S) : Set ℝ),
          |deriv q x| ≤ C * ((x - a) ^ (-1 - b) + (z - x) ^ (-1 - b) +
            ∑ w ∈ insert y S, |x - w| ^ (-1 - b))) (u v : ℝ) (hau : a ≤ u) (hvz : v ≤ z) (hy : y ≤ u ∨ v ≤ y) :
        (∀ x ∈ Ioo u v \ (S : Set ℝ), DifferentiableAt ℝ q x) ∧
        ∀ x ∈ Ioo u v \ (S : Set ℝ),
          |deriv q x| ≤ (2 * C) * ((x - u) ^ (-1 - b) + (v - x) ^ (-1 - b) +
            ∑ w ∈ S, |x - w| ^ (-1 - b)) := by
      have hxorig : ∀ x ∈ Ioo u v \ (S : Set ℝ), x ∈ Ioo a z \ (↑(insert y S) : Set ℝ) := by
        intro x hx
        refine ⟨⟨hau.trans_lt hx.1.1, hx.1.2.trans_le hvz⟩, ?_⟩
        simp only [Finset.coe_insert, mem_insert_iff, Finset.mem_coe, not_or]
        refine ⟨?_, hx.2⟩
        rcases hy with hy | hy <;> linarith [hx.1.1, hx.1.2]
      refine ⟨fun x hx => hq x (hxorig x hx), ?_⟩
      intro x hx
      have horig := hbound x (hxorig x hx)
      rw [Finset.sum_insert hyS] at horig
      have hl : (x - a) ^ (-1 - b) ≤ (x - u) ^ (-1 - b) :=
        Real.rpow_le_rpow_of_nonpos (by linarith [hx.1.1]) (by linarith) (by linarith)
      have hr : (z - x) ^ (-1 - b) ≤ (v - x) ^ (-1 - b) :=
        Real.rpow_le_rpow_of_nonpos (by linarith [hx.1.2]) (by linarith) (by linarith)
      have hm := rpow_abs_le_endpoint_sum (e := -1 - b) (by linarith) hx.1 hy
      have hs : 0 ≤ ∑ w ∈ S, |x - w| ^ (-1 - b) := Finset.sum_nonneg fun _ _ => by positivity
      nlinarith [mul_le_mul_of_nonneg_left hl hC, mul_le_mul_of_nonneg_left hr hC,
        mul_le_mul_of_nonneg_left hm hC, mul_nonneg hC hs]
    have hsubset (u v : ℝ) (hau : a ≤ u) (hvz : v ≤ z) (hy : y ≤ u ∨ v ≤ y) :
        Ioo u v \ (S : Set ℝ) ⊆ Ioo a z \ (↑(insert y S) : Set ℝ) := by
      intro t ht
      refine ⟨⟨hau.trans_lt ht.1.1, ht.1.2.trans_le hvz⟩, ?_⟩
      simp only [Finset.coe_insert, mem_insert_iff, Finset.mem_coe, not_or]
      refine ⟨?_, ht.2⟩
      rcases hy with hy | hy <;> linarith [ht.1.1, ht.1.2]
    by_cases hy : y ∈ Ioo a z
    · obtain ⟨Kl, hKl, hleft⟩ := ih (by positivity : 0 ≤ 2 * C) hy.1
      obtain ⟨Kr, hKr, hright⟩ := ih (by positivity : 0 ≤ 2 * C) hy.2
      refine ⟨Kl + Kr, add_pos hKl hKr, fun f hf hf' hM hbound => ?_⟩
      have hsubL := hsubset a y le_rfl hy.2.le (Or.inr le_rfl)
      have hsubR := hsubset y z hy.1.le le_rfl (Or.inl le_rfl)
      have hl := hrestrict hf' hbound a y le_rfl hy.2.le (Or.inr le_rfl)
      have hr := hrestrict hf' hbound y z hy.1.le le_rfl (Or.inl le_rfl)
      obtain ⟨hpl, hil, hbl⟩ := hleft f (fun t ht => hf t (hsubL ht)) hl.1
        (fun t ht => hM t (hsubL ht)) hl.2
      obtain ⟨hpr, hir, hbr⟩ := hright f (fun t ht => hf t (hsubR ht)) hr.1
        (fun t ht => hM t (hsubR ht)) hr.2
      refine ⟨?_, hil.trans hir, ?_⟩
      · intro x hx
        have hxS : x ∉ (S : Set ℝ) := fun hs => hx.2 (by simp [hs])
        have hxy : x ≠ y := fun he => hx.2 (by simp [he])
        have hs : 0 ≤ ∑ w ∈ S, |x - w| ^ (-b) :=
          Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (abs_nonneg _) _
        rw [Finset.sum_insert hyS]
        rcases lt_or_gt_of_ne hxy with hxy | hyx
        · have hh := hpl x ⟨⟨hx.1.1, hxy⟩, hxS⟩
          rw [abs_of_neg (sub_neg.mpr hxy), neg_sub]
          nlinarith [Real.rpow_nonneg (by linarith [hx.1.1] : 0 ≤ x - a) (-b),
            Real.rpow_nonneg (by linarith [hx.1.2] : 0 ≤ z - x) (-b),
            Real.rpow_nonneg (by linarith : 0 ≤ y - x) (-b)]
        · have hh := hpr x ⟨⟨hyx, hx.1.2⟩, hxS⟩
          rw [abs_of_pos (sub_pos.mpr hyx)]
          nlinarith [Real.rpow_nonneg (by linarith [hx.1.1] : 0 ≤ x - a) (-b),
            Real.rpow_nonneg (by linarith [hx.1.2] : 0 ≤ z - x) (-b),
            Real.rpow_nonneg (by linarith : 0 ≤ x - y) (-b)]
      · rw [← integral_add_adjacent_intervals hil.abs hir.abs]
        linarith
    · have hy' : y ≤ a ∨ z ≤ y := by
        rcases le_or_gt y a with h | h
        · exact Or.inl h
        · exact Or.inr (not_lt.mp fun hz => hy ⟨h, hz⟩)
      obtain ⟨K, hK, hall⟩ := ih (by positivity : 0 ≤ 2 * C) haz
      refine ⟨K, hK, fun f hf hf' hM hbound => ?_⟩
      have hsub := hsubset a z le_rfl le_rfl hy'
      have hr := hrestrict hf' hbound a z le_rfl le_rfl hy'
      obtain ⟨hp, hi, hbnd⟩ := hall f (fun t ht => hf t (hsub ht)) hr.1
        (fun t ht => hM t (hsub ht)) hr.2
      refine ⟨?_, hi, hbnd⟩
      intro x hx
      have hxS : x ∉ (S : Set ℝ) := fun hs => hx.2 (by simp [hs])
      apply (hp x ⟨hx.1, hxS⟩).trans
      apply mul_le_mul_of_nonneg_left _ hK.le
      rw [Finset.sum_insert hyS]
      linarith [Real.rpow_nonneg (abs_nonneg (x - y)) (-b)]

end Riesz1.PuncturedDerivative
