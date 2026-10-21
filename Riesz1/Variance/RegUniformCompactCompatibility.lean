/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.RegUniformSupport
public import Riesz1.Kernel.AdmissibilityRegularityMembership

/-!
# Smoothing one fixed compact profile on every enlarged circle

Compatibility with the periodization is required for the compact
families in Lemma 5.1.
-/

public section

open MeasureTheory Set
open scoped ContDiff

namespace Riesz1
namespace Internal

/-- Before the support reaches an endpoint, smoothing the periodization
on the central cell is exactly line smoothing of the fixed zero extension. -/
theorem circleMollify_periodized_eq_line_central {ρ : ℝ → ℝ} (hρ : IsMollifier ρ)
    (p : Profile) (L : Length) (hL : 1 ≤ L.val) {r h x : ℝ} (hh : 0 < h)
    (hmargin : r + h / 2 < 1 / 2)
    (hsupp : ∀ᵐ y : ℝ, r ≤ |y| → zeroExtension p y = 0)
    (hx : |x| ≤ L.val / 2) :
    circleMollify ρ L.val h (fun t : ℝ => periodizedProfile p L (t : Circle L)) x =
      mollifyLine ρ h (zeroExtension p) x := by
  have : Fact (0 < L.val) := ⟨L.property⟩
  unfold circleMollify mollifyLine
  rw [intervalIntegral.integral_of_le (by linarith [L.property])]
  have heq : (∫ y in Ioc (-(L.val / 2)) (L.val / 2),
      periodizedProfile p L (y : Circle L) * periodMollifier ρ L.val h (x - y)) =
      ∫ y in Ioc (-(L.val / 2)) (L.val / 2),
        zeroExtension p y * scaledMollifier ρ h (x - y) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc, ae_restrict_of_ae hsupp,
      ae_restrict_of_ae (show ∀ᵐ y : ℝ, y ≠ L.val / 2 by rw [ae_iff]; simp)] with y hy hs hyend
    have hrep : centralRep L (y : Circle L) = y := by
      unfold centralRep
      have hcell : y ∈ Ico (-L.val / 2) (-L.val / 2 + L.val) :=
        ⟨by linarith [hy.1], by linarith [lt_of_le_of_ne hy.2 hyend]⟩
      exact congrArg Subtype.val (AddCircle.equivIco_coe_eq hcell)
    rw [admissibility_periodizedProfile_eq_zeroExtension p L hL, hrep]
    by_cases hyr : r ≤ |y|
    · simp only [hs hyr, zero_mul]
    · have hylt : |y| < r := lt_of_not_ge hyr
      have hkernel : periodMollifier ρ L.val h (x - y) = scaledMollifier ρ h (x - y) := by
        unfold periodMollifier
        rw [tsum_eq_single (0 : ℤ)]
        · simp only [Int.cast_zero, zero_mul, add_zero]
        · intro n hn
          apply scaledMollifier_eq_zero hρ hh
          have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn
          have hperiod : L.val ≤ |(n : ℝ) * L.val| := by
            rw [abs_mul, abs_of_pos L.property]
            nlinarith
          have ht := abs_sub_abs_le_abs_sub ((n : ℝ) * L.val) (-(x - y))
          rw [sub_neg_eq_add, add_comm ((n : ℝ) * L.val), abs_neg] at ht
          have hxy := abs_sub x y
          linarith
      rw [hkernel]
  rw [heq]
  apply setIntegral_eq_integral_of_ae_compl_eq_zero
  exact ae_of_all _ fun y hy => by
    have hycell : ¬ |y| < 1 / 2 := by
      intro hlt
      apply hy
      obtain ⟨hlo, hhi⟩ := abs_lt.mp hlt
      exact ⟨by linarith, by linarith⟩
    simp only [zeroExtension, hycell, ite_false, zero_mul]

/-- The fixed line convolution vanishes beyond its enlarged support. -/
theorem mollifyLine_zeroExtension_eq_zero {ρ : ℝ → ℝ} (hρ : IsMollifier ρ)
    (p : Profile) {r h x : ℝ} (hh : 0 < h)
    (hsupp : ∀ᵐ y : ℝ, r ≤ |y| → zeroExtension p y = 0)
    (hx : r + h / 2 ≤ |x|) : mollifyLine ρ h (zeroExtension p) x = 0 := by
  unfold mollifyLine
  apply integral_eq_zero_of_ae
  filter_upwards [hsupp] with y hy
  change zeroExtension p y * scaledMollifier ρ h (x - y) = 0
  by_cases hyr : r ≤ |y|
  · simp only [hy hyr, zero_mul]
  · have hkernel : scaledMollifier ρ h (x - y) = 0 := by
      apply scaledMollifier_eq_zero hρ hh
      have ht := abs_sub_abs_le_abs_sub x y
      linarith [lt_of_not_ge hyr]
    simp only [hkernel, mul_zero]

/-- The zero extension of the actual smoothed base profile is one fixed
line convolution, so it does not depend on the enlarged circle. -/
theorem zeroExtension_circleMollify_eq_line {ρ : ℝ → ℝ} (hρ : IsMollifier ρ)
    (p g : Profile) {r h : ℝ} (hh : 0 < h) (hmargin : r + h / 2 < 1 / 2)
    (hsupp : ∀ᵐ y : ℝ, r ≤ |y| → zeroExtension p y = 0)
    (hg : ∀ x : ℝ, g.val (x : Circle unitLength) =
      circleMollify ρ 1 h (fun t : ℝ => p.val (t : Circle unitLength)) x) :
    ∀ x : ℝ, zeroExtension g x = mollifyLine ρ h (zeroExtension p) x := by
  have : Fact (0 < (unitLength).val) := ⟨unitLength.property⟩
  simp only [unitLength] at hg
  intro x
  by_cases hx : |x| < 1 / 2
  · simp only [zeroExtension, hx, ite_true, hg]
    have hc := circleMollify_periodized_eq_line_central hρ p unitLength (by norm_num [unitLength])
      hh hmargin hsupp (x := x) (by simpa only [unitLength] using hx.le)
    -- The two unit-circle lifts differ only on the countable endpoint lifts.
    have hconv : circleMollify ρ 1 h
        (fun t : ℝ => periodizedProfile p unitLength (t : Circle unitLength)) x =
          circleMollify ρ 1 h (fun t : ℝ => p.val (t : Circle unitLength)) x := by
      unfold circleMollify
      rw [intervalIntegral.integral_of_le (by norm_num : -(1 / 2 : ℝ) ≤ 1 / 2)]
      rw [intervalIntegral.integral_of_le (by norm_num : -(1 / 2 : ℝ) ≤ 1 / 2)]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc,
        ae_restrict_of_ae (show ∀ᵐ y : ℝ, y ≠ 1 / 2 by rw [ae_iff]; simp)] with y hy hyend
      have hyabs : |y| < 1 / 2 := abs_lt.mpr ⟨hy.1, lt_of_le_of_ne hy.2 hyend⟩
      have hrep : centralRep unitLength (y : Circle unitLength) = y := by
        unfold centralRep
        have hcell : y ∈ Ico (-(unitLength).val / 2)
            (-(unitLength).val / 2 + (unitLength).val) := by
          norm_num [unitLength]
          exact ⟨hy.1.le, by linarith [lt_of_le_of_ne hy.2 hyend]⟩
        exact congrArg Subtype.val (AddCircle.equivIco_coe_eq hcell)
      rw [admissibility_periodizedProfile_eq_zeroExtension p unitLength (by norm_num [unitLength]),
        hrep]
      simp only [zeroExtension, hyabs, ite_true]
      rfl
    exact hconv.symm.trans hc
  · simp only [zeroExtension, hx, ite_false]
    exact (mollifyLine_zeroExtension_eq_zero hρ p hh hsupp
      (by linarith [le_of_not_gt hx])).symm

end Internal

/-- The compact regularizations and errors are periodizations of one fixed
base profile for each `h`. They retain one support margin and agree pointwise
with smoothing on every observation circle at the physical radius `h`. -/
theorem regUniform_compactCompatibility (p : Profile) (hp : CompactProfile p)
    (ρ : ℝ → ℝ) (hρ : IsMollifier ρ) :
    ∃ h₀ r : ℝ, 0 < h₀ ∧ 0 < r ∧ r < 1 / 2 ∧
      ∀ h : ℝ, 0 < h → h ≤ h₀ →
        ∃ g e : Profile,
          ContDiff ℝ ∞ (fun x : ℝ => g.val (x : Circle unitLength)) ∧
          (∀ x : ℝ, g.val (x : Circle unitLength) =
            circleMollify ρ 1 h (fun t : ℝ => p.val (t : Circle unitLength)) x) ∧
          (∀ x, e.val x = p.val x - g.val x) ∧
          (∀ x : ℝ, r ≤ |x| → zeroExtension g x = 0) ∧
          (∀ᵐ x : ℝ, r ≤ |x| → zeroExtension e x = 0) ∧
          CompactProfile g ∧ CompactProfile e ∧
          ∀ a : Scale, ∀ x : ℝ,
            periodizedProfile g (observationLength a) (x : Circle (observationLength a)) =
              circleMollify ρ (observationLength a).val h
                (fun t : ℝ => periodizedProfile p (observationLength a)
                  (t : Circle (observationLength a))) x ∧
            periodizedProfile e (observationLength a) (x : Circle (observationLength a)) =
              periodizedProfile p (observationLength a) (x : Circle (observationLength a)) -
                circleMollify ρ (observationLength a).val h
                  (fun t : ℝ => periodizedProfile p (observationLength a)
                    (t : Circle (observationLength a))) x := by
  obtain ⟨r₀, hr₀, hr₀half, hsupp⟩ := hp
  obtain ⟨H, r, hH, hr, hrhalf, hsupport⟩ := regUniform_compactSupport p ⟨r₀, hr₀, hr₀half, hsupp⟩ ρ hρ
  refine ⟨min H (1 / 2 - r₀), r, lt_min hH (by linarith), hr, hrhalf, fun h hh hh₀ => ?_⟩
  obtain ⟨g, e, hgs, hgv, hev, hgzero, hezero, hgc, hec⟩ :=
    hsupport h hh (hh₀.trans (min_le_left _ _))
  have hmargin : r₀ + h / 2 < 1 / 2 := by
    have ht := hh₀.trans (min_le_right H (1 / 2 - r₀))
    linarith
  have hline := Internal.zeroExtension_circleMollify_eq_line hρ p g hh hmargin hsupp hgv
  refine ⟨g, e, hgs, hgv, hev, hgzero, hezero, hgc, hec, fun a x => ?_⟩
  let L := observationLength a
  have : Fact (0 < L.val) := ⟨L.property⟩
  have hL : 1 ≤ L.val := (one_le_inv₀ a.property.1).mpr a.property.2
  let z := centralRep L (x : Circle L)
  have hzx : (z : Circle L) = (x : Circle L) := AddCircle.coe_equivIco
  have hzL : |z| ≤ L.val / 2 := by
    have hm := (AddCircle.equivIco L.val (-L.val / 2) (x : Circle L)).property
    change -L.val / 2 ≤ z ∧ z < -L.val / 2 + L.val at hm
    exact abs_le.mpr ⟨by linarith [hm.1], by linarith [hm.2]⟩
  obtain ⟨q, _, _, hqv, _⟩ := Internal.exists_circleMollify_L2 hρ L hh
    ⟨periodizedProfile p L, periodizedProfileL2 p a⟩
  have hgphysical : periodizedProfile g L (x : Circle L) =
      circleMollify ρ L.val h (fun t : ℝ => periodizedProfile p L (t : Circle L)) x := by
    rw [admissibility_periodizedProfile_eq_zeroExtension g L hL]
    change zeroExtension g z = _
    rw [hline]
    rw [← Internal.circleMollify_periodized_eq_line_central hρ p L hL hh hmargin hsupp hzL,
      ← hqv, hzx, hqv]
  refine ⟨hgphysical, ?_⟩
  rw [← hgphysical, admissibility_periodizedProfile_eq_zeroExtension e L hL,
    admissibility_periodizedProfile_eq_zeroExtension p L hL,
    admissibility_periodizedProfile_eq_zeroExtension g L hL]
  dsimp only [zeroExtension]
  split_ifs
  · exact hev _
  · ring

end Riesz1
