/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.MollifierPointwise.Circle
public import Riesz1.ToMathlib.CircleSingularityLocalization
public import Riesz1.ToMathlib.FiniteMarkDistance

/-!
# Convolution bounds for finitely many circle singularities

Finite sums of distance powers can be convolved without assuming that the
input has only one puncture. These are the first derivative envelopes in
Lemma 5.1.
-/

public section

open MeasureTheory Set

namespace Riesz1

/-- Translation preserves local integrability on the line. -/
theorem locallyIntegrable_translate_sub {f : ℝ → ℝ}
    (hf : LocallyIntegrable f volume) (a : ℝ) :
    LocallyIntegrable (fun y => f (y - a)) volume := by
  intro z
  refine ⟨Icc (z - 1) (z + 1), Icc_mem_nhds (by linarith) (by linarith), ?_⟩
  have ht : IntervalIntegrable f volume (z - 1 - a) (z + 1 - a) :=
    IntegrableOn.intervalIntegrable (hf.integrableOn_isCompact isCompact_uIcc)
  have hu : IntervalIntegrable (fun y => f (y - a)) volume (z - 1) (z + 1) := by
    simpa only [sub_add_cancel] using ht.comp_sub_right a
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).mp hu

/-- The two descriptions of circular distance agree. -/
theorem dist_coe_zero_eq_circDist (L x : ℝ) :
    dist (x : AddCircle L) 0 = circDist L x := by
  rw [dist_zero_right, AddCircle.norm_eq]
  unfold circDist
  rw [div_eq_mul_inv, mul_comm x L⁻¹, mul_comm L]

/-- Integrable distance singularities are locally integrable on the periodic lift. -/
theorem locallyIntegrable_circle_dist_rpow {L e : ℝ} (hL : 0 < L) (he : -1 < e) :
    LocallyIntegrable (fun y : ℝ => dist (y : AddCircle L) 0 ^ e) volume := by
  have : Fact (0 < L) := ⟨hL⟩
  let F := fun y : ℝ => dist (y : AddCircle L) 0 ^ e
  have hp : Function.Periodic F L := by intro y; simp only [F, AddCircle.coe_add_period]
  have hi : IntervalIntegrable F volume (-L / 2) (-L / 2 + L) := by
    have ha := integrableOn_abs_rpow he (by linarith : 0 ≤ L / 2)
    have hb : IntegrableOn F (Icc (-L / 2) (L / 2)) := by
      rw [show -L / 2 = -(L / 2) by ring]
      apply ha.congr_fun _ measurableSet_Icc
      intro y hy
      have hdist : dist (y : AddCircle L) 0 = |y| := by
        have hh := CircleSingularity.dist_coe_eq_abs_sub hL
          (x := y) (y := 0) (by simpa only [sub_zero] using abs_le.mpr hy)
        simpa only [AddCircle.coe_zero, sub_zero] using hh
      dsimp only [F]
      rw [hdist]
    rw [show -L / 2 + L = L / 2 by ring]
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).mpr hb
  intro x
  refine ⟨Icc (x - 1) (x + 1), Icc_mem_nhds (by linarith) (by linarith), ?_⟩
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).mp
    (hp.intervalIntegrable hL.ne' hi (x - 1) (x + 1))

/-- A translated distance power has the single-mark regularization bound,
with the constant preceding the circle and the location of the mark. -/
theorem circleMollify_dist_rpow_bound {ρ : ℝ → ℝ} (hρ : IsMollifier ρ)
    {b : ℝ} (hb : 0 ≤ b) (hb1 : b < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ, 1 ≤ L → ∀ a h : ℝ, 0 < h → h ≤ 1 →
      ∀ x : ℝ,
        |circleMollify ρ L h (fun y : ℝ => dist (y : AddCircle L) (a : AddCircle L) ^ (-b)) x| ≤
          C * max (dist (x : AddCircle L) (a : AddCircle L)) h ^ (-b) := by
  obtain ⟨C, hC, hbound⟩ := circleMollify_sup_bound ρ hρ hb hb1
  refine ⟨C, hC, fun L hL a h hh hh1 x => ?_⟩
  have hLp : 0 < L := by linarith
  have : Fact (0 < L) := ⟨hLp⟩
  let F := fun y : ℝ => dist (y : AddCircle L) 0 ^ (-b)
  have hi : LocallyIntegrable F volume := locallyIntegrable_circle_dist_rpow hLp (by linarith)
  have hp : Function.Periodic F L := by intro y; simp only [F, AddCircle.coe_add_period]
  have hs (y : ℝ) : dist (y : AddCircle L) (a : AddCircle L) ^ (-b) = F (y - a) := by
    simp only [F, AddCircle.coe_sub, dist_eq_norm, sub_zero]
  have hshift : LocallyIntegrable (fun y => F (y - a)) volume :=
    locallyIntegrable_translate_sub hi a
  have hpshift : Function.Periodic (fun y => F (y - a)) L := by
    intro y
    change F (y + L - a) = F (y - a)
    rw [show y + L - a = (y - a) + L by ring, hp]
  have he : circleMollify ρ L h (fun y : ℝ => dist (y : AddCircle L) (a : AddCircle L) ^ (-b)) x =
      circleMollify ρ L h F (x - a) := by
    simp_rw [hs]
    rw [circleMollify_eq_mollifyLine hρ hLp hh hshift hpshift,
      circleMollify_eq_mollifyLine hρ hLp hh hi hp, mollifyLine_eq, mollifyLine_eq]
    congr 1
    funext u
    rw [show x - u - a = x - a - u by ring]
  rw [he]
  have hhbound := hbound L hL F hp hi
    (ae_of_all _ fun y _ => by
      rw [← dist_coe_zero_eq_circDist]
      dsimp only [F]
      rw [abs_of_nonneg (by positivity : 0 ≤ dist (y : AddCircle L) 0 ^ (-b))]) h hh hh1 (x - a)
  rw [← dist_coe_zero_eq_circDist, AddCircle.coe_sub, dist_eq_norm, sub_zero] at hhbound
  simpa only [dist_eq_norm] using hhbound

/-- The single-puncture estimate extends to an arbitrary finite sum of
singular envelopes, uniformly in the circle length and the marked locations. -/
theorem circleMollify_finiteMark_bound {ρ : ℝ → ℝ} (hρ : IsMollifier ρ)
    {b : ℝ} (hb : 0 ≤ b) (hb1 : b < 1) :
    ∃ D : ℝ, 0 < D ∧ ∀ (L : ℝ), 1 ≤ L →
      ∀ {ι : Type*} [Fintype ι] (marks : ι → ℝ) (C : ℝ), 0 ≤ C →
      ∀ f : ℝ → ℝ, Function.Periodic f L → LocallyIntegrable f volume →
      (∀ᵐ y : ℝ, |f y| ≤ C * (1 + ∑ j, dist (y : AddCircle L) (marks j : AddCircle L) ^ (-b))) →
      ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ x : ℝ,
        |circleMollify ρ L h f x| ≤ D * C *
          (1 + ∑ j, max (dist (x : AddCircle L) (marks j : AddCircle L)) h ^ (-b)) := by
  obtain ⟨D, hD, hsingle⟩ := circleMollify_dist_rpow_bound hρ hb hb1
  refine ⟨D + 1, by linarith, fun L hL ι _ marks C hC f hp hf henv h hh hh1 x => ?_⟩
  have hLp : 0 < L := by linarith
  have : Fact (0 < L) := ⟨hLp⟩
  let F := fun y : ℝ => dist (y : AddCircle L) 0 ^ (-b)
  let G := fun j (y : ℝ) => dist (y : AddCircle L) (marks j : AddCircle L) ^ (-b)
  have hFi : LocallyIntegrable F volume := locallyIntegrable_circle_dist_rpow hLp (by linarith)
  have hGi (j : ι) : LocallyIntegrable (G j) volume := by
    have hh := locallyIntegrable_translate_sub hFi (marks j)
    simpa only [F, G, AddCircle.coe_sub, dist_eq_norm, sub_zero] using hh
  have hGp (j : ι) : Function.Periodic (G j) L := by
    intro y
    simp only [G, AddCircle.coe_add_period]
  let κ := fun y => scaledMollifier ρ h (x - y)
  have hκi : Integrable κ :=
    ((contDiff_scaledMollifier hρ).continuous.integrable_of_hasCompactSupport
      (hasCompactSupport_scaledMollifier hρ hh)).comp_sub_left x
  have hki (j : ι) : Integrable (fun y => G j y * κ y) :=
    integrable_mul_scaled_sub hρ hh (hGi j) x
  have hκint : (∫ y, κ y) = 1 := by
    rw [show κ = fun y => scaledMollifier ρ h (x - y) from rfl,
      integral_sub_left_eq_self (scaledMollifier ρ h) volume x, integral_scaledMollifier hρ hh]
  have hsum : Integrable (fun y => ∑ j, G j y * κ y) := integrable_finsetSum _ (fun j _ => hki j)
  have hR : Integrable (fun y => C * (1 + ∑ j, G j y) * κ y) := by
    have he : (fun y => C * (1 + ∑ j, G j y) * κ y) =
        fun y => C * (κ y + ∑ j, G j y * κ y) := by
      funext y
      rw [← Finset.sum_mul]
      ring
    rw [he]
    exact (hκi.add hsum).const_mul C
  have hmajor : |mollifyLine ρ h f x| ≤ ∫ y, C * (1 + ∑ j, G j y) * κ y := by
    unfold mollifyLine
    rw [← Real.norm_eq_abs]
    apply norm_integral_le_of_norm_le hR
    filter_upwards [henv] with y hy
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (scaledMollifier_nonneg hρ hh _)]
    exact mul_le_mul_of_nonneg_right hy (scaledMollifier_nonneg hρ hh _)
  have he : (∫ y, C * (1 + ∑ j, G j y) * κ y) =
      C * (1 + ∑ j, circleMollify ρ L h (G j) x) := by
    simp_rw [show ∀ y, C * (1 + ∑ j, G j y) * κ y =
        C * (κ y + ∑ j, G j y * κ y) from fun y => by rw [← Finset.sum_mul]; ring]
    rw [integral_const_mul, integral_add hκi hsum, integral_finsetSum _ (fun j _ => hki j), hκint]
    congr 2
    apply Finset.sum_congr rfl
    intro j _
    exact (circleMollify_eq_mollifyLine hρ hLp hh (hGi j) (hGp j) x).symm
  rw [circleMollify_eq_mollifyLine hρ hLp hh hf hp x]
  have hterm (j : ι) : circleMollify ρ L h (G j) x ≤ D *
      max (dist (x : AddCircle L) (marks j : AddCircle L)) h ^ (-b) :=
    (le_abs_self _).trans (hsingle L hL (marks j) h hh hh1 x)
  have ht := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hterm j)
  rw [← Finset.mul_sum] at ht
  refine (hmajor.trans_eq he).trans ?_
  have hn : 0 ≤ ∑ j, max (dist (x : AddCircle L) (marks j : AddCircle L)) h ^ (-b) := by
    apply Finset.sum_nonneg
    intro j _
    exact Real.rpow_nonneg (le_trans (dist_nonneg) (le_max_left _ _)) _
  nlinarith [mul_nonneg hC hn, mul_nonneg hD.le hn,
    mul_le_mul_of_nonneg_left ht hC]

end Riesz1
