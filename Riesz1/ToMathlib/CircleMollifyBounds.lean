/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.MollifierPointwise.DerivativeIntegral
public import Riesz1.Frozen.HolderBound

/-!
# Supremum and Hölder bounds under circle regularization

Convolution by the nonnegative unit-mass mollifier contracts both bounds in
`HolderBound`. The circle length and smoothing radius are arbitrary
positive numbers. The convolution is `circleMollify`.
-/

public section

open MeasureTheory Set Filter

namespace Riesz1.Internal

theorem holderBound_sub (L : Length) {r B D : ℝ} {f g : Circle L → ℝ}
    (hf : HolderBound L r B f) (hg : HolderBound L r D g) :
    HolderBound L r (B + D) (fun x => f x - g x) := by
  have : Fact (0 < L.val) := ⟨L.property⟩
  refine ⟨hf.1.sub hg.1, fun x => (abs_sub _ _).trans
    (add_le_add (hf.2.1 x) (hg.2.1 x)), fun x y => ?_⟩
  have he : (f x - g x) - (f y - g y) = (f x - f y) - (g x - g y) := by ring
  rw [he, add_mul]
  exact (abs_sub _ _).trans (add_le_add (hf.2.2 x y) (hg.2.2 x y))

theorem mollifyLine_abs_le {ρ f : ℝ → ℝ} (hρ : IsMollifier ρ)
    {h B : ℝ} (hh : 0 < h) (hf : LocallyIntegrable f volume)
    (hB : ∀ x, |f x| ≤ B) (x : ℝ) : |mollifyLine ρ h f x| ≤ B := by
  rw [mollifyLine_eq]
  have hκ : Integrable (scaledMollifier ρ h) :=
    (contDiff_scaledMollifier hρ).continuous.integrable_of_hasCompactSupport
      (hasCompactSupport_scaledMollifier hρ hh)
  have hi : Integrable (fun u => f (x - u) * scaledMollifier ρ h u) := by
    simpa only [sub_sub_cancel] using
      (integrable_mul_scaled_sub hρ hh hf x).comp_sub_left x
  calc |∫ u, f (x - u) * scaledMollifier ρ h u|
      ≤ ∫ u, |f (x - u) * scaledMollifier ρ h u| := by
        simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
          (fun u => f (x - u) * scaledMollifier ρ h u)
    _ ≤ ∫ u, B * scaledMollifier ρ h u := by
      apply integral_mono hi.abs (hκ.const_mul B)
      intro u
      dsimp only
      rw [abs_mul, abs_of_nonneg (scaledMollifier_nonneg hρ hh u)]
      exact mul_le_mul_of_nonneg_right (hB _) (scaledMollifier_nonneg hρ hh u)
    _ = B := by rw [integral_const_mul, integral_scaledMollifier hρ hh, mul_one]

theorem circleMollify_abs_le {ρ f : ℝ → ℝ} (hρ : IsMollifier ρ)
    {L h B : ℝ} (hL : 0 < L) (hh : 0 < h)
    (hf : LocallyIntegrable f volume) (hper : Function.Periodic f L)
    (hB : ∀ x, |f x| ≤ B) (x : ℝ) : |circleMollify ρ L h f x| ≤ B := by
  rw [circleMollify_eq_mollifyLine hρ hL hh hf hper]
  exact mollifyLine_abs_le hρ hh hf hB x

theorem circleMollify_periodic {ρ f : ℝ → ℝ} (hρ : IsMollifier ρ)
    {L h : ℝ} (hL : 0 < L) (hh : 0 < h)
    (hf : LocallyIntegrable f volume) (hper : Function.Periodic f L) :
    Function.Periodic (circleMollify ρ L h f) L := by
  intro x
  simp_rw [circleMollify_eq_mollifyLine hρ hL hh hf hper, mollifyLine_eq]
  apply integral_congr_ae
  exact ae_of_all _ fun u => by
    dsimp only
    rw [show x + L - u = (x - u) + L by ring, hper]

theorem circleMollify_sub {ρ f g : ℝ → ℝ} (hρ : IsMollifier ρ)
    {L h : ℝ} (hL : 0 < L) (hh : 0 < h)
    (hf : LocallyIntegrable f volume) (hg : LocallyIntegrable g volume)
    (hpf : Function.Periodic f L) (hpg : Function.Periodic g L) :
    circleMollify ρ L h (fun x => f x - g x) =
      fun x => circleMollify ρ L h f x - circleMollify ρ L h g x := by
  funext x
  change circleMollify ρ L h (f - g) x = _
  rw [circleMollify_eq_mollifyLine hρ hL hh (hf.sub hg) (hpf.sub hpg),
    circleMollify_eq_mollifyLine hρ hL hh hf hpf,
    circleMollify_eq_mollifyLine hρ hL hh hg hpg, mollifyLine]
  change (∫ y, (f y - g y) * scaledMollifier ρ h (x - y)) = _
  simp_rw [sub_mul]
  exact integral_sub (integrable_mul_scaled_sub hρ hh hf x)
    (integrable_mul_scaled_sub hρ hh hg x)

/-- The descended regularization has the same supremum and Hölder bounds.
The function `g` is identified pointwise with the convolution, not chosen
by its bounds. -/
theorem holderBound_circleMollify {ρ : ℝ → ℝ} (hρ : IsMollifier ρ)
    (L : Length) {r B h : ℝ} (hh : 0 < h) {f : Circle L → ℝ}
    (hf : HolderBound L r B f) :
    ∃ g : Circle L → ℝ, HolderBound L r B g ∧
      ∀ x : ℝ, g (x : Circle L) =
        circleMollify ρ L.val h (fun t : ℝ => f (t : Circle L)) x := by
  have : Fact (0 < L.val) := ⟨L.property⟩
  let F : ℝ → ℝ := fun t => f (t : Circle L)
  have hFc : Continuous F := hf.1.comp (AddCircle.continuous_mk' L.val)
  have hFp : Function.Periodic F L.val := by
    intro x
    simp only [F, AddCircle.coe_add_period]
  have hgp := circleMollify_periodic hρ L.property hh hFc.locallyIntegrable hFp
  let g : Circle L → ℝ := hgp.lift
  have hg (x : ℝ) : g (x : Circle L) = circleMollify ρ L.val h F x := hgp.lift_coe x
  have hgc : Continuous g :=
    (QuotientAddGroup.isQuotientMap_mk (AddSubgroup.zmultiples L.val)).continuous_iff.mpr (by
    change Continuous (fun x : ℝ => g (x : Circle L))
    simpa only [Function.comp_def, hg] using
      (contDiff_circleMollify hρ L.property hh hFc.locallyIntegrable hFp).continuous)
  refine ⟨g, ⟨hgc, ?_, ?_⟩, hg⟩
  · intro x
    induction x using QuotientAddGroup.induction_on with
    | H x =>
      rw [hg]
      exact circleMollify_abs_le hρ L.property hh hFc.locallyIntegrable hFp
        (fun t => hf.2.1 _) x
  · intro x y
    induction x using QuotientAddGroup.induction_on with
    | H x =>
      induction y using QuotientAddGroup.induction_on with
      | H y =>
        rw [hg, hg]
        have hdiff : LocallyIntegrable (fun u => F (x - u) - F (y - u)) volume :=
          ((hFc.comp (continuous_const.sub continuous_id)).sub
            (hFc.comp (continuous_const.sub continuous_id))).locallyIntegrable
        have hbound (u : ℝ) : |F (x - u) - F (y - u)| ≤
            B * dist (x : Circle L) (y : Circle L) ^ r := by
          simpa only [F, AddCircle.coe_sub, dist_sub_right] using
            hf.2.2 ((x - u : ℝ) : Circle L) ((y - u : ℝ) : Circle L)
        simp_rw [circleMollify_eq_mollifyLine hρ L.property hh hFc.locallyIntegrable hFp,
          mollifyLine_eq]
        rw [← integral_sub
          (by simpa only [sub_sub_cancel] using
            (integrable_mul_scaled_sub hρ hh hFc.locallyIntegrable x).comp_sub_left x)
          (by simpa only [sub_sub_cancel] using
            (integrable_mul_scaled_sub hρ hh hFc.locallyIntegrable y).comp_sub_left y)]
        have he : (fun u => F (x - u) * scaledMollifier ρ h u -
            F (y - u) * scaledMollifier ρ h u) =
            (fun u => (F (x - u) - F (y - u)) * scaledMollifier ρ h u) := by
          funext u
          ring
        rw [he]
        have ht := mollifyLine_abs_le hρ hh hdiff hbound 0
        rw [mollifyLine_eq] at ht
        -- Reflection of the integration variable puts the increment at `u`.
        have ht' := integral_neg_eq_self
          (fun u => (F (x - u) - F (y - u)) * scaledMollifier ρ h u)
        have heven (u : ℝ) : scaledMollifier ρ h (-u) = scaledMollifier ρ h u := by
          simp only [scaledMollifier, neg_div, hρ.2.2.1]
        simp only [heven, sub_neg_eq_add, zero_sub] at ht ht'
        simpa only [← ht', heven] using ht

end Riesz1.Internal
