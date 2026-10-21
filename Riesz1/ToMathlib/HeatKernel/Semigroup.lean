/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Elementary semigroup integrals

Two scalar identities behind the semigroup representation of powers of `lam > 0`
(equation (2.4) in Lemma 2.1), together with the integrability of their integrands.

For `γ > 0` and `lam > 0`, the Gamma integral gives
`lam^{-γ} = Γ(γ)^{-1} ∫_0^∞ e^{-lamt} t^{γ-1} dt`, whose integrand is integrable on `(0, ∞)`.

For `0 < γ < 1` and `lam > 0`, the integral `∫_0^∞ (1 - e^{-lamt}) t^{-1-γ} dt` converges and equals
`lam^γ Γ(1 - γ) / γ`. The proof differentiates `-(1 - e^{-lamt}) t^{-γ} / γ`, whose derivative is
`(1 - e^{-lamt}) t^{-1-γ}` minus `lam γ^{-1} e^{-lamt} t^{-γ}`, and integrates it over `(0, ∞)`.
-/

public section

open MeasureTheory Set Filter Topology

namespace Riesz1

/-- The factor `1 - e^{-lamt}` is nonnegative for `lam > 0` and `t > 0`. -/
lemma one_sub_exp_nonneg {lam t : ℝ} (hlam : 0 < lam) (ht : 0 < t) :
    0 ≤ 1 - Real.exp (-lam * t) := by
  have : Real.exp (-lam * t) ≤ 1 := Real.exp_le_one_iff.2 (by
    rw [neg_mul]; exact neg_nonpos.2 (mul_nonneg hlam.le ht.le))
  linarith

/-- The factor `1 - e^{-x}` lies below `x` for every real `x`. -/
lemma one_sub_exp_neg_le (x : ℝ) : 1 - Real.exp (-x) ≤ x := by
  linarith [Real.add_one_le_exp (-x)]

/-- The factor `1 - e^{-lamt}` lies below `lamt` for every real `lam` and `t`. -/
lemma one_sub_exp_le_mul {lam t : ℝ} : 1 - Real.exp (-lam * t) ≤ lam * t := by
  rw [neg_mul]
  exact one_sub_exp_neg_le _

/-- The identity `t · t^{-γ} = t^{1-γ}` for `t > 0`. -/
lemma mul_rpow_neg_eq {t γ : ℝ} (ht : 0 < t) : t * t ^ (-γ) = t ^ (1 - γ) := by
  rw [show (1 - γ) = 1 + -γ by ring, Real.rpow_add ht, Real.rpow_one]

/-- The identity `t · t^{-1-γ} = t^{-γ}` for `t > 0`. -/
lemma mul_rpow_neg_one_sub_eq {t γ : ℝ} (ht : 0 < t) : t * t ^ (-1 - γ) = t ^ (-γ) := by
  rw [show (-γ) = 1 + (-1 - γ) by ring, Real.rpow_add ht, Real.rpow_one]

/-- The integrand `e^{-lamt} t^{γ-1}` is integrable on `(0, ∞)` for `γ > 0` and `lam > 0`. -/
lemma integrableOn_exp_mul_rpow_sub_one {γ lam : ℝ} (hγ : 0 < γ) (hlam : 0 < lam) :
    IntegrableOn (fun t : ℝ => Real.exp (-lam * t) * t ^ (γ - 1)) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := γ - 1) (b := lam)
    (by linarith) one_pos hlam
  simp only [Real.rpow_one] at h
  exact h.congr_fun (fun t _ => mul_comm _ _) measurableSet_Ioi

/-- The scalar identity `lam^{-γ} = Γ(γ)^{-1} ∫_0^∞ e^{-lamt} t^{γ-1} dt`, equation (2.4). -/
theorem rpow_neg_eq_gamma_inv_mul_integral {γ lam : ℝ} (hγ : 0 < γ) (hlam : 0 < lam) :
    lam ^ (-γ) = (Real.Gamma γ)⁻¹ * ∫ t in Ioi (0 : ℝ), Real.exp (-lam * t) * t ^ (γ - 1) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi hγ hlam
  have e : ∫ t in Ioi (0 : ℝ), Real.exp (-lam * t) * t ^ (γ - 1) =
      ∫ t in Ioi (0 : ℝ), t ^ (γ - 1) * Real.exp (-(lam * t)) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    rw [neg_mul]
    ring
  have hΓ : Real.Gamma γ ≠ 0 := (Real.Gamma_pos_of_pos hγ).ne'
  rw [e, h, Real.rpow_neg hlam.le, one_div, Real.inv_rpow hlam.le]
  field_simp

/-- The integrand `(1 - e^{-lamt}) t^{-1-γ}` is integrable on `(0, ∞)` for `0 < γ < 1` and
`lam > 0`. -/
lemma integrableOn_one_sub_exp_mul_rpow_neg_one_sub {γ lam : ℝ} (hγ : 0 < γ) (hγ1 : γ < 1)
    (hlam : 0 < lam) :
    IntegrableOn (fun t : ℝ => (1 - Real.exp (-lam * t)) * t ^ (-1 - γ)) (Ioi 0) := by
  rw [← Set.Ioc_union_Ioi_eq_Ioi zero_le_one]
  refine IntegrableOn.union ?_ ?_
  · have hb : IntegrableOn (fun t : ℝ => lam * t ^ (-γ)) (Ioc 0 1) :=
      ((intervalIntegral.intervalIntegrable_rpow' (by linarith : (-1 : ℝ) < -γ)).const_mul lam).1
    refine Integrable.mono' hb (by fun_prop) ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioc (fun t ht => ?_)
    have ht0 : 0 < t := ht.1
    rw [Real.norm_of_nonneg (mul_nonneg (one_sub_exp_nonneg hlam ht0) (Real.rpow_nonneg ht0.le _))]
    calc (1 - Real.exp (-lam * t)) * t ^ (-1 - γ) ≤ (lam * t) * t ^ (-1 - γ) :=
          mul_le_mul_of_nonneg_right one_sub_exp_le_mul (Real.rpow_nonneg ht0.le _)
      _ = lam * (t * t ^ (-1 - γ)) := by ring
      _ = lam * t ^ (-γ) := by rw [mul_rpow_neg_one_sub_eq ht0]
  · refine Integrable.mono' (integrableOn_Ioi_rpow_of_lt (by linarith : -1 - γ < -1) zero_lt_one)
      (by fun_prop) ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => ?_)
    have ht0 : 0 < t := lt_trans zero_lt_one ht
    have h1 : 0 ≤ 1 - Real.exp (-lam * t) := one_sub_exp_nonneg hlam ht0
    have h2 : 1 - Real.exp (-lam * t) ≤ 1 := by
      have : 0 ≤ Real.exp (-lam * t) := (Real.exp_pos _).le
      linarith
    rw [Real.norm_of_nonneg (mul_nonneg h1 (Real.rpow_nonneg ht0.le _))]
    exact mul_le_of_le_one_left (Real.rpow_nonneg ht0.le _) h2

/-- The Frullani-type identity
`∫_0^∞ (1 - e^{-lamt}) t^{-1-γ} dt = lam^γ Γ(1 - γ) / γ` for `0 < γ < 1` and `lam > 0`,
the companion of equation (2.7) in Lemma 2.1. -/
theorem integral_one_sub_exp_mul_rpow_neg_one_sub {γ lam : ℝ} (hγ : 0 < γ) (hγ1 : γ < 1)
    (hlam : 0 < lam) :
    ∫ t in Ioi (0 : ℝ), (1 - Real.exp (-lam * t)) * t ^ (-1 - γ) =
      lam ^ γ * Real.Gamma (1 - γ) / γ := by
  set G : ℝ → ℝ := fun t => -((1 - Real.exp (-lam * t)) * t ^ (-γ)) / γ with hG
  set H : ℝ → ℝ := fun t => Real.exp (-lam * t) * t ^ (-γ) with hH
  have hγne : γ ≠ 0 := hγ.ne'
  have hFint := integrableOn_one_sub_exp_mul_rpow_neg_one_sub hγ hγ1 hlam
  -- Integrability of the second term `e^{-lamt} t^{-γ}`.
  have hHint : IntegrableOn H (Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := -γ) (b := lam)
      (by linarith) one_pos hlam
    simp only [Real.rpow_one] at h
    exact h.congr_fun (fun t _ => mul_comm _ _) measurableSet_Ioi
  -- Derivative of `G` on `(0, ∞)`.
  have hderiv : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt G
      ((1 - Real.exp (-lam * t)) * t ^ (-1 - γ) - lam / γ * H t) t := by
    intro t ht
    have ht' : (0 : ℝ) < t := ht
    have hA : HasDerivAt (fun s : ℝ => 1 - Real.exp (-lam * s)) (Real.exp (-lam * t) * lam) t := by
      have := ((hasDerivAt_id' t).const_mul (-lam)).exp.const_sub 1
      convert this using 1
      ring
    have hB : HasDerivAt (fun s : ℝ => s ^ (-γ)) ((-γ) * t ^ (-γ - 1)) t :=
      Real.hasDerivAt_rpow_const (Or.inl ht'.ne')
    have hG' := ((hA.mul hB).neg).div_const γ
    convert hG' using 1
    simp only [H]
    rw [show (-1 - γ) = -γ - 1 by ring]
    field_simp
    ring
  -- `G` tends to `0` at infinity, and is continuous from the right at `0` with `G 0 = 0`.
  have hG0 : G 0 = 0 := by
    simp [hG, Real.zero_rpow (neg_ne_zero.2 hγne)]
  have hlim : Tendsto G atTop (𝓝 0) := by
    have hexp : Tendsto (fun t : ℝ => Real.exp (-lam * t)) atTop (𝓝 0) := by
      have hlin : Tendsto (fun t : ℝ => lam * t) atTop atTop :=
        tendsto_id.const_mul_atTop hlam
      have := Real.tendsto_exp_neg_atTop_nhds_zero.comp hlin
      simpa [Function.comp_def, neg_mul] using this
    have h1 : Tendsto (fun t : ℝ => (1 - Real.exp (-lam * t)) * t ^ (-γ)) atTop (𝓝 0) := by
      have h1' : Tendsto (fun t : ℝ => 1 - Real.exp (-lam * t)) atTop (𝓝 1) := by
        simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hexp
      simpa using h1'.mul (tendsto_rpow_neg_atTop hγ)
    have := (h1.neg).div_const γ
    simpa [hG] using this
  have hcont : ContinuousWithinAt G (Ici 0) 0 := by
    rw [← continuousWithinAt_Ioi_iff_Ici]
    unfold ContinuousWithinAt
    rw [hG0]
    -- Squeeze `0 ≤ (1 - e^{-lamt}) t^{-γ} ≤ lam t^{1-γ}` near `0` from the right.
    have hK : Tendsto (fun t : ℝ => (1 - Real.exp (-lam * t)) * t ^ (-γ)) (𝓝[>] 0) (𝓝 0) := by
      have hup : Tendsto (fun t : ℝ => lam * t ^ (1 - γ)) (𝓝[>] 0) (𝓝 0) := by
        have hc : Tendsto (fun t : ℝ => t ^ (1 - γ)) (𝓝 0) (𝓝 0) := by
          have := (Real.continuousAt_rpow_const 0 (1 - γ) (Or.inr (by linarith))).tendsto
          simpa [Real.zero_rpow (by linarith : (1 - γ) ≠ 0)] using this
        simpa using (hc.const_mul lam).mono_left nhdsWithin_le_nhds
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
      · refine eventually_nhdsWithin_of_forall fun t ht => ?_
        exact mul_nonneg (one_sub_exp_nonneg hlam ht) (Real.rpow_nonneg (le_of_lt ht) _)
      · refine eventually_nhdsWithin_of_forall fun t ht => ?_
        have ht0 : (0 : ℝ) < t := ht
        calc (1 - Real.exp (-lam * t)) * t ^ (-γ) ≤ (lam * t) * t ^ (-γ) :=
              mul_le_mul_of_nonneg_right one_sub_exp_le_mul (Real.rpow_nonneg ht0.le _)
          _ = lam * t ^ (1 - γ) := by rw [mul_assoc, mul_rpow_neg_eq ht0]
    have hG' := (hK.neg).div_const γ
    rw [neg_zero, zero_div] at hG'
    exact hG'
  -- Integrate the derivative over `(0, ∞)`.
  have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv
    (hFint.sub (hHint.const_mul (lam / γ))) hlim
  rw [hG0, sub_zero, integral_sub hFint (hHint.const_mul _), integral_const_mul] at hFTC
  have hH_val : ∫ t in Ioi (0 : ℝ), H t = (1 / lam) ^ (1 - γ) * Real.Gamma (1 - γ) := by
    have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 1 - γ) (r := lam) (by linarith) hlam
    rw [show (1 - γ) - 1 = -γ by ring] at h
    rw [← h]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    simp only [H]
    rw [neg_mul]
    exact mul_comm _ _
  rw [hH_val] at hFTC
  -- `lam^γ = lam / lam^{1-γ}` and `(1/lam)^{1-γ} = 1 / lam^{1-γ}`.
  have e2 : lam ^ γ = lam / lam ^ (1 - γ) := by
    have := Real.rpow_sub hlam 1 (1 - γ)
    rw [Real.rpow_one, show (1 : ℝ) - (1 - γ) = γ by ring] at this
    exact this
  have hp : lam ^ (1 - γ) ≠ 0 := (Real.rpow_pos_of_pos hlam _).ne'
  rw [sub_eq_zero] at hFTC
  rw [hFTC, Real.div_rpow zero_le_one hlam.le, Real.one_rpow, e2]
  field_simp

end Riesz1
