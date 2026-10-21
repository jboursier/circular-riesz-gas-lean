/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.CircleFourierDerivative
public import Mathlib.Analysis.Normed.Group.AddCircle
public import Mathlib.Tactic

/-!
# Uniform bounds for primitives of bounded periodic functions

An integrable, mean-zero periodic function has a continuous circle primitive.
A supremum bound for the derivative and a full-period integral bound give Lipschitz
and supremum bounds for that primitive, independently of the period length.
-/

public section

open MeasureTheory Set Filter Topology intervalIntegral

namespace Riesz1

/-- Every circle point has a real representative whose absolute value is its norm. -/
theorem exists_real_circle_representative_norm {L : ℝ} (z : AddCircle L) :
    ∃ t : ℝ, (t : AddCircle L) = z ∧ |t| = ‖z‖ := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
  let n := round (L⁻¹ * x)
  refine ⟨x - n * L, ?_, ?_⟩
  · rw [AddCircle.coe_sub]
    have hn : (((n : ℝ) * L : ℝ) : AddCircle L) = 0 :=
      (AddCircle.coe_eq_zero_iff L).mpr ⟨n, by simp [zsmul_eq_mul]⟩
    rw [hn, sub_zero]
  · rw [AddCircle.norm_eq]

/-- Bounds on a bounded periodic derivative and its integral norm give a continuous
Lipschitz circle primitive. Off a countable exceptional set the derivative is the original
function. The identity of Fourier coefficients also holds across that set. -/
theorem exists_bounded_periodic_primitive {L K M : ℝ} [hL : Fact (0 < L)]
    {f : ℝ → ℝ} (hp : Function.Periodic f L) (hm : Measurable f)
    (hi : IntervalIntegrable f volume 0 L) (hzero : ∫ t in (0 : ℝ)..L, f t = 0)
    (hb : ∀ t : ℝ, |f t| ≤ K) (hM : ∫ t in (0 : ℝ)..L, |f t| ≤ M)
    {S : Set ℝ} (hS : S.Countable) (hc : ∀ x : ℝ, x ∉ S → ContinuousAt f x) :
    ∃ G : AddCircle L → ℝ, Continuous G ∧
      (∀ x, |G x| ≤ M) ∧
      (∀ x y, |G x - G y| ≤ K * dist x y) ∧
      (∀ x : ℝ, x ∉ S → HasDerivAt (fun t : ℝ => G (t : AddCircle L)) (f x) x) ∧
      ∀ k : ℤ, (2 * Real.pi * Complex.I * (k : ℂ) / L) *
        fourierCoeff (fun x => (G x : ℂ)) k =
          fourierCoeff (fun x => (hp.lift x : ℂ)) k := by
  have hint : ∀ a b : ℝ, IntervalIntegrable f volume a b := hp.intervalIntegrable₀ hL.out.ne' hi
  let F : ℝ → ℝ := fun x => ∫ t in (0 : ℝ)..x, f t
  have hFp : Function.Periodic F L := by
    intro x
    apply sub_eq_zero.mp
    change (∫ t in (0 : ℝ)..(x + L), f t) - (∫ t in (0 : ℝ)..x, f t) = 0
    rw [integral_interval_sub_left (hint _ _) (hint _ _), hp.intervalIntegral_add_eq x 0,
      zero_add, hzero]
  let G : AddCircle L → ℝ := hFp.lift
  have hGcoe (t : ℝ) : G (t : AddCircle L) = F t := hFp.lift_coe t
  have hGc : Continuous G := by
    apply isQuotientMap_quotient_mk'.continuous_iff.mpr
    change Continuous (fun t : ℝ => G (t : AddCircle L))
    exact (continuous_primitive hint 0).congr fun t => (hGcoe t).symm
  have hGd (x : ℝ) (hx : x ∉ S) :
      HasDerivAt (fun t : ℝ => G (t : AddCircle L)) (f x) x := by
    have hd := integral_hasDerivAt_right (hint 0 x)
      hm.stronglyMeasurable.stronglyMeasurableAtFilter (hc x hx)
    simpa only [hGcoe, F] using hd
  refine ⟨G, hGc, ?_, ?_, hGd, ?_⟩
  · intro x
    let t := (AddCircle.equivIco L 0 x).val
    have ht : t ∈ Ico (0 : ℝ) L := by
      simpa only [zero_add] using (AddCircle.equivIco L 0 x).property
    have htx : (t : AddCircle L) = x := AddCircle.coe_equivIco
    rw [← htx, hGcoe]
    calc
      |F t| ≤ ∫ u in (0 : ℝ)..t, |f u| := abs_integral_le_integral_abs ht.1
      _ ≤ ∫ u in (0 : ℝ)..L, |f u| :=
        integral_mono_interval le_rfl ht.1 ht.2.le (ae_of_all _ fun _ => abs_nonneg _) hi.abs
      _ ≤ M := hM
  · intro x y
    obtain ⟨r, hr, hnorm⟩ := exists_real_circle_representative_norm (x - y)
    obtain ⟨t, ht⟩ := QuotientAddGroup.mk_surjective y
    have htx : ((t + r : ℝ) : AddCircle L) = x := by
      rw [AddCircle.coe_add, ht, hr]
      abel
    have hd : |r| = dist x y := by simpa only [dist_eq_norm] using hnorm
    calc
      |G x - G y| = |F (t + r) - F t| := by rw [← htx, ← ht, hGcoe, hGcoe]
      _ = |∫ u in t..t + r, f u| := by
        rw [integral_interval_sub_left (hint _ _) (hint _ _)]
      _ ≤ K * |t + r - t| := by
        simpa only [Real.norm_eq_abs] using
          intervalIntegral.norm_integral_le_of_norm_le_const (f := f) (C := K) (a := t) (b := t + r)
            (fun u _ => by simpa only [Real.norm_eq_abs] using hb u)
      _ = K * dist x y := by rw [add_sub_cancel_left, hd]
  · intro k
    have hnull : ∀ᵐ x : ℝ, x ∉ S := hS.ae_notMem volume
    have hder : deriv (fun t : ℝ => G (t : AddCircle L)) =ᵐ[volume] f := by
      filter_upwards [hnull] with x hx
      exact (hGd x hx).deriv
    have hid : IntervalIntegrable (deriv (fun t : ℝ => G (t : AddCircle L))) volume 0 L :=
      hi.congr_ae (ae_restrict_of_ae hder.symm)
    have he := CircleFourier.integral_deriv_mul_fourier hGc hS
      (fun x hx => (hGd x hx).differentiableAt) hid k
    have hcF := fourierCoeff_eq_intervalIntegral (fun x : AddCircle L => (hp.lift x : ℂ)) k 0
    simp only [zero_add, smul_eq_mul, Complex.real_smul, one_div, Complex.ofReal_inv] at hcF
    have hei : (∫ t in (0 : ℝ)..L,
        ((deriv (fun u : ℝ => G (u : AddCircle L)) t : ℝ) : ℂ) *
          fourier (-k) (t : AddCircle L)) =
        ∫ t in (0 : ℝ)..L, fourier (-k) (t : AddCircle L) * (hp.lift (t : AddCircle L) : ℂ) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hder] with x hx _
      rw [hx, hp.lift_coe]
      exact mul_comm _ _
    rw [hei] at he
    rw [hcF, he]
    have hLC : (L : ℂ) ≠ 0 := by exact_mod_cast hL.out.ne'
    field_simp

end Riesz1
