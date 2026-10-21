/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.HurwitzKernel.Euler
public import Riesz1.ToMathlib.HurwitzKernel.Reality
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Group.Integral

/-!
# Integrability and mean zero of the Hurwitz kernel

The Euler error series is uniformly convergent on `[0,1]`, and every error
term has integral zero. Isolating the integrable power singularity proves
integrability and mean zero of the Hurwitz zeta function on the unit circle.
Averaging with its reflection gives Lemma 2.1.
-/

public section

open Filter Topology MeasureTheory Set Complex
namespace Riesz1

lemma continuousOn_eulerTerm (z : ℂ) (n : ℕ) :
    ContinuousOn (fun x : ℝ => eulerTerm x z n) (Icc 0 1) := by
  apply continuousOn_of_forall_continuousAt
  intro x hx
  unfold eulerTerm
  have hpos : 0 < (n : ℝ) + 1 + x := by linarith [Nat.cast_nonneg (α := ℝ) n, hx.1]
  have h : ContinuousAt (fun x : ℝ => (((n : ℝ) + 1 + x : ℝ) : ℂ) ^ (-z)) x :=
    (Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr hpos.ne')).comp (by fun_prop)
  have hh := h.sub (continuousAt_const (y :=
    (((n : ℂ) + 2) ^ (1 - z) - ((n : ℂ) + 1) ^ (1 - z)) / (1 - z)))
  simpa only [ofReal_add, ofReal_natCast, ofReal_one, Pi.sub_def] using hh

lemma summable_eulerBound_ofReal (s : ℝ) (hs : 0 < s) :
    Summable (fun n : ℕ => ‖(s : ℂ)‖ * ((n : ℝ) + 1) ^ (-s - 1)) := by
  apply Summable.mul_left
  simpa only [Nat.cast_add, Nat.cast_one] using
    (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr (show -s - 1 < -1 by linarith))

lemma continuousOn_tsum_eulerTerm (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    ContinuousOn (fun x : ℝ => ∑' n, eulerTerm x (s : ℂ) n) (Icc 0 1) := by
  apply continuousOn_tsum (continuousOn_eulerTerm (s : ℂ)) (summable_eulerBound_ofReal s hs0)
  exact fun n x hx => norm_eulerTerm_le x hx.1 hx.2 (s : ℂ) hs0 (by exact_mod_cast hs1.ne) n

lemma integral_eulerTerm (z : ℂ) (hz1 : z ≠ 1) (n : ℕ) :
    ∫ x : ℝ in 0..1, eulerTerm x z n = 0 := by
  have hp : IntervalIntegrable (fun x : ℝ => ((n : ℂ) + 1 + x) ^ (-z)) volume 0 1 := by
    have h := (continuousOn_eulerTerm z n).add (continuousOn_const (c :=
      (((n : ℂ) + 2) ^ (1 - z) - ((n : ℂ) + 1) ^ (1 - z)) / (1 - z)))
    simpa only [eulerTerm, Pi.add_def, sub_add_cancel] using h.intervalIntegrable_of_Icc (μ := volume) zero_le_one
  simp only [eulerTerm]
  rw [intervalIntegral.integral_sub hp intervalIntegrable_const, intervalIntegral.integral_const,
    sub_zero, one_smul]
  have heq : (fun x : ℝ => ((n : ℂ) + 1 + x) ^ (-z)) =
      (fun x : ℝ => (((x + ((n : ℝ) + 1) : ℝ)) : ℂ) ^ (-z)) := by
    funext x
    congr 1
    push_cast
    ring
  rw [heq, intervalIntegral.integral_comp_add_right
    (fun t : ℝ => (t : ℂ) ^ (-z)) ((n : ℝ) + 1)]
  rw [integral_cpow (Or.inr ⟨by intro h; apply hz1; linear_combination -h, ?_⟩)]
  · simp only [zero_add, neg_add_eq_sub, ofReal_add, ofReal_natCast, ofReal_one]
    rw [show (1 : ℂ) + ((n : ℂ) + 1) = (n : ℂ) + 2 by ring]
    exact sub_self _
  · rw [uIcc_of_le (by linarith)]
    simp only [mem_Icc, not_and]
    intro h
    linarith [Nat.cast_nonneg (α := ℝ) n]

lemma integral_tsum_eulerTerm (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    ∫ x : ℝ in 0..1, ∑' n, eulerTerm x (s : ℂ) n = 0 := by
  have hi (n : ℕ) : IntegrableOn (fun x : ℝ => eulerTerm x (s : ℂ) n) (Ioc 0 1) :=
    (continuousOn_eulerTerm (s : ℂ) n).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hnorm (n : ℕ) : (∫ x : ℝ in Ioc 0 1, ‖eulerTerm x (s : ℂ) n‖) ≤
      ‖(s : ℂ)‖ * ((n : ℝ) + 1) ^ (-s - 1) := by
    have hbound := integral_mono_ae (hi n).norm (integrableOn_const (by norm_num : volume (Ioc (0 : ℝ) 1) ≠ ⊤))
      ((ae_restrict_mem measurableSet_Ioc).mono (fun x hx =>
        norm_eulerTerm_le x hx.1.le hx.2 (s : ℂ) hs0 (by exact_mod_cast hs1.ne) n))
    simpa using hbound
  have hsum : Summable (fun n : ℕ => ∫ x : ℝ in Ioc 0 1, ‖eulerTerm x (s : ℂ) n‖) :=
    (summable_eulerBound_ofReal s hs0).of_nonneg_of_le (fun n => integral_nonneg fun x => norm_nonneg _) hnorm
  rw [intervalIntegral.integral_of_le zero_le_one,
    ← integral_tsum_of_summable_integral_norm hi hsum]
  have heq (n : ℕ) : ∫ x : ℝ in Ioc 0 1, eulerTerm x (s : ℂ) n = 0 := by
    rw [← intervalIntegral.integral_of_le zero_le_one]
    exact integral_eulerTerm (s : ℂ) (by exact_mod_cast hs1.ne) n
  simp only [heq, tsum_zero]

lemma hurwitzZeta_re_euler (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1)
    (x : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1) :
    (HurwitzZeta.hurwitzZeta (x : UnitAddCircle) (s : ℂ)).re =
      x ^ (-s) + (∑' n, eulerTerm x (s : ℂ) n).re - 1 / (1 - s) := by
  have h := congrArg Complex.re (euler_eq_hurwitzZeta x hx0 hx1 (s : ℂ) hs0 (by exact_mod_cast hs1.ne))
  rw [← ofReal_neg, ← ofReal_cpow hx0.le] at h
  have hdiv : (1 : ℂ) / (1 - (s : ℂ)) = ((1 / (1 - s) : ℝ) : ℂ) := by push_cast; rfl
  rw [hdiv] at h
  simpa only [add_re, sub_re, ofReal_re] using h.symm

lemma intervalIntegrable_hurwitzZeta_re (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    IntervalIntegrable (fun x : ℝ => (HurwitzZeta.hurwitzZeta (x : UnitAddCircle) (s : ℂ)).re)
      volume 0 1 := by
  have hpow : IntervalIntegrable (fun x : ℝ => x ^ (-s)) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have htail := ((continuous_re.comp_continuousOn (continuousOn_tsum_eulerTerm s hs0 hs1)).intervalIntegrable_of_Icc
    (μ := volume) zero_le_one)
  apply (hpow.add htail |>.sub intervalIntegrable_const).congr
  intro x hx
  rw [uIoc_of_le zero_le_one] at hx
  exact (hurwitzZeta_re_euler s hs0 hs1 x hx.1 hx.2).symm

lemma intervalIntegral_hurwitzZeta_re (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    ∫ x : ℝ in 0..1, (HurwitzZeta.hurwitzZeta (x : UnitAddCircle) (s : ℂ)).re = 0 := by
  have hpow : IntervalIntegrable (fun x : ℝ => x ^ (-s)) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have htail := (continuousOn_tsum_eulerTerm s hs0 hs1).intervalIntegrable_of_Icc
    (μ := volume) zero_le_one
  have htailR := ((continuous_re.comp_continuousOn (continuousOn_tsum_eulerTerm s hs0 hs1)).intervalIntegrable_of_Icc
    (μ := volume) zero_le_one)
  change IntervalIntegrable (fun x : ℝ => (∑' n, eulerTerm x (s : ℂ) n).re) volume 0 1 at htailR
  have htailInt : ∫ x : ℝ in 0..1, (∑' n, eulerTerm x (s : ℂ) n).re = 0 := by
    have hre : (∫ x : ℝ in Ioc 0 1, (∑' n, eulerTerm x (s : ℂ) n).re) =
        (∫ x : ℝ in Ioc 0 1, ∑' n, eulerTerm x (s : ℂ) n).re :=
      Complex.reCLM.integral_comp_comm htail.1
    rw [intervalIntegral.integral_of_le zero_le_one, hre,
      ← intervalIntegral.integral_of_le zero_le_one, integral_tsum_eulerTerm s hs0 hs1, zero_re]
  calc
    _ = ∫ x : ℝ in 0..1, x ^ (-s) + (∑' n, eulerTerm x (s : ℂ) n).re - 1 / (1 - s) := by
      apply intervalIntegral.integral_congr_ae
      apply ae_of_all _
      intro x hx
      rw [uIoc_of_le zero_le_one] at hx
      exact hurwitzZeta_re_euler s hs0 hs1 x hx.1 hx.2
    _ = 0 := by
      rw [intervalIntegral.integral_sub (hpow.add htailR) intervalIntegrable_const,
        intervalIntegral.integral_add hpow htailR, htailInt,
        integral_rpow (Or.inl (by linarith)), intervalIntegral.integral_const]
      simp [Real.zero_rpow (show 1 - s ≠ 0 by linarith), neg_add_eq_sub]

lemma integrable_unitAddCircle_of_interval {F : UnitAddCircle → ℝ}
    (hF : IntervalIntegrable (fun x : ℝ => F (x : UnitAddCircle)) volume 0 1) :
    Integrable F := by
  let e := AddCircle.measurableEquivIoc 1 0
  have hmp : MeasurePreserving (⇑e.symm) (volume.comap (Subtype.val : Ioc (0 : ℝ) (0 + 1) → ℝ)) volume :=
    MeasurePreserving.symm e (AddCircle.measurePreserving_equivIoc 1)
  apply (hmp.integrable_comp_emb e.symm.measurableEmbedding).mp
  change Integrable (fun x : Ioc (0 : ℝ) (0 + 1) => F (x.val : UnitAddCircle)) _
  simpa only [Function.comp_def] using
    (integrableOn_iff_comap_subtypeVal measurableSet_Ioc).mp (show IntegrableOn (fun x : ℝ => F (x : UnitAddCircle)) (Ioc (0 : ℝ) (0 + 1)) volume from by simpa using hF.1)

lemma integrable_hurwitzZeta_re (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    Integrable (fun x : UnitAddCircle => (HurwitzZeta.hurwitzZeta x (s : ℂ)).re) :=
  integrable_unitAddCircle_of_interval (intervalIntegrable_hurwitzZeta_re s hs0 hs1)

lemma integral_hurwitzZeta_re (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    ∫ x : UnitAddCircle, (HurwitzZeta.hurwitzZeta x (s : ℂ)).re = 0 := by
  rw [← AddCircle.intervalIntegral_preimage 1 0]
  simpa only [zero_add] using intervalIntegral_hurwitzZeta_re s hs0 hs1

/-- Integrability of the even Hurwitz zeta kernel (Lemma 2.1). -/
theorem integrable_hurwitzZetaEven_re (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    Integrable (fun x : UnitAddCircle => (HurwitzZeta.hurwitzZetaEven x (s : ℂ)).re) := by
  have hi := integrable_hurwitzZeta_re s hs0 hs1
  have h := (hi.add hi.comp_neg).div_const 2
  convert h using 1
  funext a
  rw [HurwitzZeta.hurwitzZetaEven_eq]
  simp only [Complex.div_ofNat_re, Complex.add_re, Pi.add_def]

/-- The even Hurwitz zeta kernel has mean zero (Lemma 2.1). -/
theorem integral_hurwitzZetaEven_re (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    ∫ x : UnitAddCircle, (HurwitzZeta.hurwitzZetaEven x (s : ℂ)).re = 0 := by
  have hi := integrable_hurwitzZeta_re s hs0 hs1
  simp only [HurwitzZeta.hurwitzZetaEven_eq, Complex.div_ofNat_re, Complex.add_re]
  rw [integral_div, integral_add hi hi.comp_neg,
    integral_neg_eq_self (fun a : UnitAddCircle => (HurwitzZeta.hurwitzZeta a (s : ℂ)).re) volume,
    integral_hurwitzZeta_re s hs0 hs1]
  norm_num

end Riesz1
