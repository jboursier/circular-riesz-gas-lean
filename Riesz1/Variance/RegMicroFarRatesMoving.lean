/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.RegMicroFarRatesCutoffs
public import Riesz1.Variance.RegMicroFarRatesPowers

/-!
# Quantitative derivative of the actual moving-cutoff error

The moving transition in Lemma 5.3. The two analytic
hypotheses of this internal lemma are precisely the derivative and
transition-value clauses supplied by `MicroKernelBounds`. All cutoffs are
the actual functions.
-/

public section

open Set Filter Topology

namespace Riesz1.Internal

/-- Multiplication by `1-χ_h` preserves the far derivative rate. The
constant precedes the circle and all microscopic and analytic data. -/
theorem regMicro_moving_deriv_bound (n : ℕ+) :
    ∃ D : ℝ, 0 < D ∧ ∀ (L h : ℝ), 0 < L → 0 < h → 8*h < L → 2*h < 1 →
      ∀ (a : Fin (n : ℕ) → ℝ),
        (∀ i j, i ≠ j → 8*h ≤ dist (a i : AddCircle L) (a j : AddCircle L)) →
      ∀ (s α C : ℝ), 0 ≤ 2-s+α → 0 ≤ C →
      ∀ (e : AddCircle L → ℝ) (x : ℝ),
        (∀ j, (x : AddCircle L) ≠ (a j : AddCircle L)) →
        DifferentiableAt ℝ (fun t : ℝ => e (t : AddCircle L)) x →
      let r := cappedMarkDistance (fun j => (a j : AddCircle L)) (x : AddCircle L)
      (|deriv (fun t : ℝ => e (t : AddCircle L)) x| ≤ C*h^(1-s)*r^(-2+s-α)) →
      (2*h ≤ r → r ≤ 4*h → |e (x : AddCircle L)| ≤ C*h^(-α)) →
        |deriv (fun t : ℝ => (1-microCutoffSum L (2*h) a (t : AddCircle L))*
          e (t : AddCircle L)) x| ≤
          C*(1+(n : ℝ)*D/2*4^(2-s+α))*h^(1-s)*(max r h)^(-2+s-α) := by
  classical
  obtain ⟨D, hD, hb⟩ := microCutoffSum_deriv_bound (ι := Fin (n : ℕ))
  refine ⟨D, hD, fun L h hL hh hhL hh1 a hsep s α C hq hC e x hx he => ?_⟩
  dsimp only
  intro hder htrans
  let r := cappedMarkDistance (fun j => (a j : AddCircle L)) (x : AddCircle L)
  let χ := fun t : ℝ => microCutoffSum L (2*h) a (t : AddCircle L)
  have hsep' : ∀ i j, i ≠ j → 4*(2*h) ≤ dist (a i : AddCircle L) (a j : AddCircle L) := by
    simpa only [show 4*(2*h) = 8*h by ring] using hsep
  have hχ := microCutoffSum_mem_Icc (by positivity : 0 < 2*h) a hsep' (x : AddCircle L)
  have hdχ : DifferentiableAt ℝ χ x :=
    (microCutoffSum_contDiff hL (by positivity : 0 < 2*h) (by linarith) a).differentiable
      (by simp) x
  have hformula : deriv (fun t : ℝ => (1-χ t)*e (t : AddCircle L)) x =
      -deriv χ x*e (x : AddCircle L)+(1-χ x)*deriv (fun t : ℝ => e (t : AddCircle L)) x := by
    have heq : ((fun _ : ℝ => (1 : ℝ))-χ)*(fun t : ℝ => e (t : AddCircle L)) =
        fun t : ℝ => (1-χ t)*e (t : AddCircle L) := by
      ext t
      simp only [Pi.mul_apply, Pi.sub_apply]
    have hd := (((hasDerivAt_const x (1 : ℝ)).sub hdχ.hasDerivAt).mul he.hasDerivAt).deriv
    rw [heq] at hd
    simpa only [Pi.sub_apply, zero_sub] using hd
  by_cases hr : r ≤ 2*h
  · obtain ⟨j, hj⟩ := exists_dist_eq_cappedMarkDistance
      (fun j => (a j : AddCircle L)) (x : AddCircle L) (hr.trans_lt hh1)
    have hone : χ x = 1 := microCutoffSum_eq_one (by positivity) a hsep' j (hj.trans_le hr)
    have hzero : deriv χ x = 0 := microCutoffSum_deriv_eq_zero_of_one (by positivity) a hsep' hone
    rw [hformula, hone, hzero]
    simp only [neg_zero, zero_mul, sub_self, zero_add, abs_zero]
    positivity
  · have hr2 : 2*h ≤ r := (lt_of_not_ge hr).le
    have hr0 : 0 < r := lt_of_lt_of_le (by positivity) hr2
    rw [hformula, max_eq_left (by linarith : h ≤ r)]
    have hfirst : |deriv χ x| * |e (x : AddCircle L)| ≤
        C*((n : ℝ)*D/2*4^(2-s+α))*h^(1-s)*r^(-2+s-α) := by
      by_cases hz : deriv χ x = 0
      · rw [hz, abs_zero, zero_mul]
        positivity
      · obtain ⟨_hinner, j, hj⟩ := microCutoffSum_transition_of_deriv_ne_zero
          (by positivity : 0 < 2*h) a hsep' hz
        have hr4 : r ≤ 4*h := (cappedMarkDistance_le_dist _ _ j).trans (by linarith)
        calc
          _ ≤ ((n : ℝ)*D/(2*h))*(C*h^(-α)) := mul_le_mul
            (by simpa only [Fintype.card_fin] using hb L (2*h) hL (by positivity) (by linarith) a x)
            (htrans hr2 hr4) (abs_nonneg _) (by positivity)
          _ = (C*(n : ℝ)*D/2)*(h⁻¹*h^(-α)) := by ring
          _ ≤ (C*(n : ℝ)*D/2)*(4^(2-s+α)*h^(1-s)*r^(-2+s-α)) :=
            mul_le_mul_of_nonneg_left (regMicro_transition_power hh hr0 hr4 hq) (by positivity)
          _ = _ := by ring
    have hsecond : |1-χ x| * |deriv (fun t : ℝ => e (t : AddCircle L)) x| ≤
        C*h^(1-s)*r^(-2+s-α) := by
      have hχ' : |1-χ x| ≤ 1 := by
        rw [abs_of_nonneg (sub_nonneg.mpr hχ.2)]
        linarith [hχ.1]
      exact (mul_le_of_le_one_left (abs_nonneg _) hχ').trans hder
    calc
      _ ≤ |deriv χ x| * |e (x : AddCircle L)|+
          |1-χ x| * |deriv (fun t : ℝ => e (t : AddCircle L)) x| := by
        simpa only [abs_mul, abs_neg] using
          (abs_add_le (-deriv χ x*e (x : AddCircle L))
            ((1-χ x)*deriv (fun t : ℝ => e (t : AddCircle L)) x))
      _ ≤ C*((n : ℝ)*D/2*4^(2-s+α))*h^(1-s)*r^(-2+s-α)+
          C*h^(1-s)*r^(-2+s-α) := add_le_add hfirst hsecond
      _ = _ := by ring

/-- The bound extends through the marked points: the actual moving
mask vanishes on a neighborhood of each of them. Values of the error
representative at singularities have no effect. -/
theorem regMicro_moving_deriv_bound_everywhere (n : ℕ+) :
    ∃ D : ℝ, 0 < D ∧ ∀ (L h : ℝ), 0 < L → 0 < h → 8*h < L → 2*h < 1 →
      ∀ (a : Fin (n : ℕ) → ℝ),
        (∀ i j, i ≠ j → 8*h ≤ dist (a i : AddCircle L) (a j : AddCircle L)) →
      ∀ (s α C : ℝ), 0 ≤ 2-s+α → 0 ≤ C →
      ∀ (e : AddCircle L → ℝ) (x : ℝ),
        ((∀ j, (x : AddCircle L) ≠ (a j : AddCircle L)) →
          DifferentiableAt ℝ (fun t : ℝ => e (t : AddCircle L)) x ∧
          |deriv (fun t : ℝ => e (t : AddCircle L)) x| ≤
            C*h^(1-s)*(cappedMarkDistance (fun j => (a j : AddCircle L))
              (x : AddCircle L))^(-2+s-α)) →
      (2*h ≤ cappedMarkDistance (fun j => (a j : AddCircle L)) (x : AddCircle L) →
        cappedMarkDistance (fun j => (a j : AddCircle L)) (x : AddCircle L) ≤ 4*h →
        |e (x : AddCircle L)| ≤ C*h^(-α)) →
        |deriv (fun t : ℝ => (1-microCutoffSum L (2*h) a (t : AddCircle L))*
          e (t : AddCircle L)) x| ≤
          C*(1+(n : ℝ)*D/2*4^(2-s+α))*h^(1-s)*
            (max (cappedMarkDistance (fun j => (a j : AddCircle L)) (x : AddCircle L)) h)^(-2+s-α) := by
  obtain ⟨D, hD, hb⟩ := regMicro_moving_deriv_bound n
  refine ⟨D, hD, fun L h hL hh hhL hh1 a hsep s α C hq hC e x he ht => ?_⟩
  by_cases hx : ∀ j, (x : AddCircle L) ≠ (a j : AddCircle L)
  · exact hb L h hL hh hhL hh1 a hsep s α C hq hC e x hx (he hx).1 (he hx).2 ht
  · push Not at hx
    obtain ⟨j, hj⟩ := hx
    have hc : Continuous (fun t : ℝ => dist (t : AddCircle L) (a j : AddCircle L)) := by fun_prop
    have hd : dist (x : AddCircle L) (a j : AddCircle L) < 2*h := by
      rw [hj, dist_self]
      positivity
    have hz : (fun t : ℝ => (1-microCutoffSum L (2*h) a (t : AddCircle L))*
        e (t : AddCircle L)) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [(hc.tendsto x).eventually (Iio_mem_nhds hd)] with t ht
      have hone := microCutoffSum_eq_one (by positivity : 0 < 2*h) a
        (by simpa only [show 4*(2*h) = 8*h by ring] using hsep) j ht.le
      rw [hone, sub_self, zero_mul]
    rw [((hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq hz).deriv, abs_zero]
    positivity

/-- The moving error is differentiable even when the representative is
singular at the marks, because the moving mask is locally zero there. -/
theorem regMicro_moving_differentiable {ι : Type*} [Fintype ι] {L h : ℝ}
    (hL : 0 < L) (hh : 0 < h) (hhL : 8*h < L) (a : ι → ℝ)
    (hsep : ∀ i j, i ≠ j → 8*h ≤ dist (a i : AddCircle L) (a j : AddCircle L))
    (e : AddCircle L → ℝ)
    (he : ∀ x : ℝ, (∀ j, (x : AddCircle L) ≠ (a j : AddCircle L)) →
      DifferentiableAt ℝ (fun t : ℝ => e (t : AddCircle L)) x) :
    Differentiable ℝ (fun t : ℝ =>
      (1-microCutoffSum L (2*h) a (t : AddCircle L))*e (t : AddCircle L)) := by
  intro x
  by_cases hx : ∀ j, (x : AddCircle L) ≠ (a j : AddCircle L)
  · exact ((differentiableAt_const (1 : ℝ)).sub
      ((microCutoffSum_contDiff hL (by positivity : 0 < 2*h) (by linarith) a).differentiable
        (by simp) x)).mul (he x hx)
  · push Not at hx
    obtain ⟨j, hj⟩ := hx
    have hc : Continuous (fun t : ℝ => dist (t : AddCircle L) (a j : AddCircle L)) := by fun_prop
    have hd : dist (x : AddCircle L) (a j : AddCircle L) < 2*h := by
      rw [hj, dist_self]
      positivity
    have hz : (fun t : ℝ => (1-microCutoffSum L (2*h) a (t : AddCircle L))*
        e (t : AddCircle L)) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [(hc.tendsto x).eventually (Iio_mem_nhds hd)] with t ht
      have hone := microCutoffSum_eq_one (by positivity : 0 < 2*h) a
        (by simpa only [show 4*(2*h) = 8*h by ring] using hsep) j ht.le
      rw [hone, sub_self, zero_mul]
    exact (differentiableAt_const (0 : ℝ)).congr_of_eventuallyEq hz

end Riesz1.Internal
