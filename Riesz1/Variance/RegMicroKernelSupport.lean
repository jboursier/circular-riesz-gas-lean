/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.RegUniformSupport
public import Riesz1.Kernel.AdmissibilityRegularityMembership

/-!
# A fixed support interval for the microscopic regularization error

The support assertion of Lemma 5.3, simultaneously
on every circle of length at least one. The profile, its periodization, and
the smoothing operator are used as defined. The error is their actual
difference, with no additional encoding of its `L²` class.
-/

public section

open MeasureTheory Set Filter

namespace Riesz1
namespace Internal

/-- The periodization agrees with the zero extension at every point of
the central half-open cell of a circle of length at least one. -/
theorem regMicroKernel_periodized_coe_eq (p : Profile) (L : Length) (hL : 1 ≤ L.val)
    {x : ℝ} (hx : -L.val / 2 ≤ x ∧ x < L.val / 2) :
    periodizedProfile p L (x : Circle L) = zeroExtension p x := by
  have : Fact (0 < L.val) := ⟨L.property⟩
  rw [admissibility_periodizedProfile_eq_zeroExtension p L hL]
  have hc : x ∈ Ico (-L.val / 2) (-L.val / 2 + L.val) :=
    ⟨hx.1, by linarith [hx.2]⟩
  have hr : centralRep L (x : Circle L) = x :=
    congrArg Subtype.val (AddCircle.equivIco_coe_eq hc)
  rw [hr]

/-- The convolution vanishes outside the original support enlarged by
`h / 2`, uniformly in the circle length. -/
theorem regMicroKernel_mollify_eq_zero_of_support {ρ : ℝ → ℝ} (hρ : IsMollifier ρ)
    (p : Profile) (L : Length) (hL : 1 ≤ L.val) {r h x : ℝ} (hh : 0 < h)
    (hs : ∀ᵐ y : ℝ, r ≤ |y| → zeroExtension p y = 0)
    (hx : |x| ≤ L.val / 2) (hxr : r + h / 2 ≤ |x|) :
    circleMollify ρ L.val h (fun t : ℝ => periodizedProfile p L (t : Circle L)) x = 0 := by
  unfold circleMollify
  rw [intervalIntegral.integral_of_le (by linarith [L.property])]
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_of_ae hs, ae_restrict_mem measurableSet_Ioc,
    ae_restrict_of_ae (show ∀ᵐ y : ℝ, y ≠ L.val / 2 by rw [ae_iff]; simp)]
    with y hy hcell hyend
  change periodizedProfile p L (y : Circle L) * periodMollifier ρ L.val h (x - y) = 0
  have hcy : -L.val / 2 ≤ y ∧ y < L.val / 2 :=
    ⟨by linarith [hcell.1], lt_of_le_of_ne hcell.2 hyend⟩
  rw [regMicroKernel_periodized_coe_eq p L hL hcy]
  by_cases hyr : r ≤ |y|
  · rw [hy hyr, zero_mul]
  · have hyr' : |y| < r := lt_of_not_ge hyr
    have hkernel : periodMollifier ρ L.val h (x - y) = 0 := by
      unfold periodMollifier
      suffices hz : ∀ n : ℤ, scaledMollifier ρ h (x - y + n * L.val) = 0 by
        simp only [hz, tsum_zero]
      intro n
      apply scaledMollifier_eq_zero hρ hh
      by_cases hn : n = 0
      · simp only [hn, Int.cast_zero, zero_mul, add_zero]
        linarith [abs_sub_abs_le_abs_sub x y]
      · have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn
        have hnL : L.val ≤ |(n : ℝ) * L.val| := by
          rw [abs_mul, abs_of_pos L.property]
          nlinarith
        have ht := abs_sub_abs_le_abs_sub ((n : ℝ) * L.val) (-(x - y))
        rw [sub_neg_eq_add, add_comm ((n : ℝ) * L.val), abs_neg] at ht
        linarith [abs_sub x y]
    rw [hkernel, mul_zero]

end Internal

/-- The compact-profile support clause of Lemma 5.3.
One radius cutoff and one support interval work for every enlarged circle.
The smoothing vanishes pointwise there. Its error vanishes a.e., as required
for the actual `L²` profile class. -/
theorem regMicroKernel_compact_support (p : Profile) (hp : CompactProfile p)
    (ρ : ℝ → ℝ) (hρ : IsMollifier ρ) :
    ∃ h₀ r : ℝ, 0 < h₀ ∧ 0 < r ∧ r < 1 / 2 ∧
      ∀ (L : Length), 1 ≤ L.val → ∀ h : ℝ, 0 < h → h ≤ h₀ →
        (∀ x : ℝ, |x| ≤ L.val / 2 → r ≤ |x| →
          circleMollify ρ L.val h
            (fun t : ℝ => periodizedProfile p L (t : Circle L)) x = 0) ∧
        (∀ᵐ x : ℝ ∂(volume.restrict (Ioc (-(L.val / 2)) (L.val / 2))),
          r ≤ |x| → periodizedProfile p L (x : Circle L) -
            circleMollify ρ L.val h
              (fun t : ℝ => periodizedProfile p L (t : Circle L)) x = 0) := by
  obtain ⟨r₀, hr₀, hr₀half, hs⟩ := hp
  let r := (r₀ + 1 / 2) / 2
  let h₀ := r - r₀
  have hr : 0 < r := by dsimp [r]; linarith
  have hrhalf : r < 1 / 2 := by dsimp [r]; linarith
  have hr₀r : r₀ < r := by dsimp [r]; linarith
  refine ⟨h₀, r, by dsimp [h₀]; linarith, hr, hrhalf, fun L hL h hh hh₀ => ?_⟩
  have hzero (x : ℝ) (hx : |x| ≤ L.val / 2) (hxr : r ≤ |x|) :
      circleMollify ρ L.val h
        (fun t : ℝ => periodizedProfile p L (t : Circle L)) x = 0 :=
    Internal.regMicroKernel_mollify_eq_zero_of_support hρ p L hL hh hs hx
      (by dsimp [h₀] at hh₀; linarith)
  refine ⟨hzero, ?_⟩
  filter_upwards [ae_restrict_of_ae hs, ae_restrict_mem measurableSet_Ioc,
    ae_restrict_of_ae (show ∀ᵐ x : ℝ, x ≠ L.val / 2 by rw [ae_iff]; simp)]
    with x hx hcell hxend
  intro hxr
  have hxL : |x| ≤ L.val / 2 := abs_le.mpr ⟨by linarith [hcell.1], hcell.2⟩
  rw [hzero x hxL hxr, sub_zero, Internal.regMicroKernel_periodized_coe_eq p L hL
    ⟨by linarith [hcell.1], lt_of_le_of_ne hcell.2 hxend⟩]
  exact hx (hr₀r.le.trans hxr)

end Riesz1
