/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.CircleMollifyDilation
public import Riesz1.ToMathlib.MollifierPointwise.BridgeCircle
public import Riesz1.ToMathlib.MollifierPointwise.DerivativeIntegral

/-!
# Smoothing a periodic integrable convolution

Fubini moves a bounded periodic smoothing kernel through an integrable
convolution. The identity holds at every evaluation point, including where
the unsmoothed convolution is represented only almost everywhere. Applied to
the inverse transport kernel, it identifies the actual smoothing error with
convolution by the integrable error kernel in Lemma 5.3.
-/

public section

open MeasureTheory Set Filter

namespace Riesz1
namespace PeriodicConvolution

/-- A continuous periodic real function is bounded on the entire cover. -/
theorem exists_norm_bound {κ : ℝ → ℝ} {L : ℝ} (hL : 0 < L)
    (hc : Continuous κ) (hp : Function.Periodic κ L) :
    ∃ B : ℝ, ∀ t, ‖κ t‖ ≤ B := by
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (0 : ℝ) L) hc.continuousOn
  refine ⟨B, fun t => ?_⟩
  let n : ℤ := ⌊t / L⌋
  have ht0 : 0 ≤ t - n * L := by
    have hn' := (le_div_iff₀ hL).mp (Int.floor_le (t / L))
    dsimp [n]
    linarith
  have ht1 : t - n * L ≤ L := by
    have hn' := (div_lt_iff₀ hL).mp (Int.lt_floor_add_one (t / L))
    dsimp [n]
    linarith
  have he : κ (t - n * L) = κ t := (hp.int_mul n).sub_eq t
  rw [← he]
  exact hB _ ⟨ht0, ht1⟩

/-- Multiplying a period-integrable input by a shifted continuous periodic
function preserves absolute integrability, at every shift. -/
theorem integrable_mul_continuous {q κ : ℝ → ℝ} {L : ℝ} (hL : 0 < L)
    (hq : IntegrableOn q (Ioc (-(L / 2)) (L / 2)))
    (hc : Continuous κ) (hp : Function.Periodic κ L) (x : ℝ) :
    IntegrableOn (fun y => q y * κ (x - y)) (Ioc (-(L / 2)) (L / 2)) := by
  obtain ⟨B, hB⟩ := exists_norm_bound hL hc hp
  exact hq.mul_bdd ((hc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
    (ae_of_all _ fun y => hB (x - y))

/-- An integrable periodic function is integrable on every bounded interval. -/
theorem intervalIntegrable_of_period {K : ℝ → ℝ} {L : ℝ} (hL : 0 < L)
    (hp : Function.Periodic K L)
    (hi : IntegrableOn K (Ioc (-(L / 2)) (L / 2))) (a b : ℝ) :
    IntervalIntegrable K volume a b := by
  have hcell : IntervalIntegrable K volume (-(L / 2)) (-(L / 2) + L) := by
    rw [show -(L / 2) + L = L / 2 by ring]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).mpr hi
  exact hp.intervalIntegrable hL.ne' hcell a b

/-- Period-integrability also supplies local integrability across every lift. -/
theorem locallyIntegrable_of_period {K : ℝ → ℝ} {L : ℝ} (hL : 0 < L)
    (hp : Function.Periodic K L)
    (hi : IntegrableOn K (Ioc (-(L / 2)) (L / 2))) : LocallyIntegrable K volume := by
  intro x
  refine ⟨Icc (x - 1) (x + 1), Icc_mem_nhds (by linarith) (by linarith), ?_⟩
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).mp
    (intervalIntegrable_of_period hL hp hi (x - 1) (x + 1))

/-- Absolute integrability of the two-variable periodic convolution integrand. -/
theorem integrable_prod {q K : ℝ → ℝ} {L : ℝ} (hL : 0 < L)
    (hp : Function.Periodic K L) (hKm : Measurable K)
    (hq : IntegrableOn q (Ioc (-(L / 2)) (L / 2)))
    (hK : IntegrableOn K (Ioc (-(L / 2)) (L / 2))) :
    Integrable (fun p : ℝ × ℝ => q p.2 * K (p.1 - p.2))
      ((volume.restrict (Ioc (-(L / 2)) (L / 2))).prod
        (volume.restrict (Ioc (-(L / 2)) (L / 2)))) := by
  have hm : AEStronglyMeasurable (fun p : ℝ × ℝ => q p.2 * K (p.1 - p.2))
      ((volume.restrict (Ioc (-(L / 2)) (L / 2))).prod
        (volume.restrict (Ioc (-(L / 2)) (L / 2)))) :=
    hq.aestronglyMeasurable.comp_snd.mul
      (hKm.comp (measurable_fst.sub measurable_snd)).aestronglyMeasurable
  rw [integrable_prod_iff' hm]
  refine ⟨ae_of_all _ fun y => ?_, ?_⟩
  · have hshift := (intervalIntegrable_of_period hL hp hK
      (-(L / 2) - y) (L / 2 - y)).comp_sub_right y
    rw [sub_add_cancel, sub_add_cancel] at hshift
    change IntegrableOn (fun x => q y * K (x - y)) (Ioc (-(L / 2)) (L / 2))
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).mp hshift).const_mul (q y)
  · have he (y : ℝ) :
        (∫ x in Ioc (-(L / 2)) (L / 2), ‖q y * K (x - y)‖) =
          ‖q y‖ * ∫ x in Ioc (-(L / 2)) (L / 2), ‖K x‖ := by
      simp_rw [norm_mul]
      rw [integral_const_mul, integral_Ioc_sub_shift (f := fun z : ℝ => ‖K z‖)
        hL (fun t => congrArg (fun v : ℝ => ‖v‖) (hp t)) y]
    simp_rw [he]
    exact hq.norm.mul_const _

/-- Associativity with a bounded measurable periodic third factor, pointwise.
No pointwise integrability of the first convolution is assumed. -/
theorem integral_smoothing_assoc {q K κ : ℝ → ℝ} {L B : ℝ} (hL : 0 < L)
    (hKp : Function.Periodic K L) (hκp : Function.Periodic κ L)
    (hKm : Measurable K) (hκm : Measurable κ)
    (hq : IntegrableOn q (Ioc (-(L / 2)) (L / 2)))
    (hK : IntegrableOn K (Ioc (-(L / 2)) (L / 2)))
    (hκ : ∀ t, ‖κ t‖ ≤ B) (x : ℝ) :
    (∫ z in Ioc (-(L / 2)) (L / 2),
      (∫ y in Ioc (-(L / 2)) (L / 2), q y * K (z - y)) * κ (x - z)) =
      ∫ y in Ioc (-(L / 2)) (L / 2), q y *
        ∫ z in Ioc (-(L / 2)) (L / 2), K z * κ (x - y - z) := by
  have hi := (integrable_prod hL hKp hKm hq hK).mul_bdd
    (hκm.comp (measurable_const.sub measurable_fst)).aestronglyMeasurable
    (ae_of_all _ fun p => hκ (x - p.1))
  have hshift (y : ℝ) :
      (∫ z in Ioc (-(L / 2)) (L / 2), K (z - y) * κ (x - z)) =
        ∫ z in Ioc (-(L / 2)) (L / 2), K z * κ (x - y - z) := by
    let H := fun z => K z * κ (x - y - z)
    have hp : Function.Periodic H L := by
      intro z
      dsimp [H]
      rw [hKp z, show x - y - (z + L) = (x - y - z) - L by ring, hκp.sub_eq]
    have he (z : ℝ) : K (z - y) * κ (x - z) = H (z - y) := by
      dsimp [H]
      congr 2
      ring
    simp_rw [he]
    exact integral_Ioc_sub_shift hL hp y
  calc _ = ∫ z in Ioc (-(L / 2)) (L / 2),
        ∫ y in Ioc (-(L / 2)) (L / 2), (q y * K (z - y)) * κ (x - z) := by
          simp_rw [integral_mul_const]
    _ = ∫ y in Ioc (-(L / 2)) (L / 2),
        ∫ z in Ioc (-(L / 2)) (L / 2), (q y * K (z - y)) * κ (x - z) :=
          integral_integral_swap hi
    _ = _ := by
      apply integral_congr_ae
      exact ae_of_all _ fun y => by
        simp_rw [mul_assoc]
        rw [integral_const_mul, hshift]

end PeriodicConvolution

/-- The actual smoothing preserves an added constant, pointwise. -/
theorem circleMollify_const_add {ρ f : ℝ → ℝ} (hρ : IsMollifier ρ)
    {L h : ℝ} (hL : 0 < L) (hh : 0 < h)
    (hf : LocallyIntegrable f volume) (hp : Function.Periodic f L) (c x : ℝ) :
    circleMollify ρ L h (fun t => c + f t) x = c + circleMollify ρ L h f x := by
  have hcp : Function.Periodic (fun t => c + f t) L := fun t => by
    dsimp only
    rw [hp t]
  have hci : LocallyIntegrable (fun t => c + f t) volume :=
    continuous_const.locallyIntegrable.add hf
  rw [circleMollify_eq_mollifyLine hρ hL hh hci hcp,
    circleMollify_eq_mollifyLine hρ hL hh hf hp]
  simp_rw [mollifyLine_eq, add_mul]
  have hκ : Integrable (scaledMollifier ρ h) :=
    (contDiff_scaledMollifier hρ).continuous.integrable_of_hasCompactSupport
      (hasCompactSupport_scaledMollifier hρ hh)
  have hi : Integrable (fun u => f (x - u) * scaledMollifier ρ h u) := by
    simpa only [sub_sub_cancel] using (integrable_mul_scaled_sub hρ hh hf x).comp_sub_left x
  rw [integral_add (hκ.const_mul c) hi, integral_const_mul, integral_scaledMollifier hρ hh,
    mul_one]

/-- The periodized mollifier is continuous at every positive length, in the
range `h ≤ L` needed for microscopic smoothing. -/
theorem continuous_periodMollifier {ρ : ℝ → ℝ} (hρ : IsMollifier ρ)
    {L h : ℝ} (hL : 0 < L) (hh : 0 < h) (hhL : h ≤ L) :
    Continuous (periodMollifier ρ L h) := by
  have hδ : 0 < h / L := div_pos hh hL
  have hδ1 : h / L ≤ 1 := (div_le_one hL).mpr hhL
  have he (z : ℝ) : periodMollifier ρ L h z =
      (circleMollifier ρ ⟨h / L, hδ⟩ hρ.contDiff.continuous
        ((z / L : ℝ) : UnitAddCircle)).re / L := by
    rw [circleMollifier_coe_real hρ hδ hδ1,
      Internal.periodMollifier_dilation ρ hL.ne' hh.ne', Complex.ofReal_re,
      mul_div_cancel₀ z hL.ne']
    field_simp
  rw [show periodMollifier ρ L h = (fun z : ℝ =>
      (circleMollifier ρ ⟨h / L, hδ⟩ hρ.contDiff.continuous
        ((z / L : ℝ) : UnitAddCircle)).re / L) from funext he]
  exact (Complex.continuous_re.comp
    ((continuous_circleMollifier hρ.contDiff.continuous ⟨h / L, hδ⟩).comp
      ((AddCircle.continuous_mk' 1).comp
        ((continuous_id : Continuous (fun z : ℝ => z)).div_const L)))).div_const L

/-- The real periodized mollifier has its stated period. -/
theorem periodMollifier_periodic (ρ : ℝ → ℝ) (L h : ℝ) :
    Function.Periodic (periodMollifier ρ L h) L := by
  intro z
  unfold periodMollifier
  have he (n : ℤ) : scaledMollifier ρ h (z + L + n * L) =
      scaledMollifier ρ h (z + (n + 1 : ℤ) * L) := by
    push_cast
    congr 1
    ring
  simp_rw [he]
  exact Equiv.tsum_eq (Equiv.addRight (1 : ℤ))
    (fun n : ℤ => scaledMollifier ρ h (z + n * L))

/-- Smoothing can be moved from a periodic convolution to its integrable
kernel. This equality is pointwise, for `circleMollify`. -/
theorem circleMollify_periodic_convolution {ρ q K : ℝ → ℝ} (hρ : IsMollifier ρ)
    {L h : ℝ} (hL : 0 < L) (hh : 0 < h) (hhL : h ≤ L)
    (hKp : Function.Periodic K L) (hKm : Measurable K)
    (hq : IntegrableOn q (Ioc (-(L / 2)) (L / 2)))
    (hK : IntegrableOn K (Ioc (-(L / 2)) (L / 2))) (x : ℝ) :
    circleMollify ρ L h
      (fun z => ∫ y in Ioc (-(L / 2)) (L / 2), q y * K (z - y)) x =
      ∫ y in Ioc (-(L / 2)) (L / 2), q y * circleMollify ρ L h K (x - y) := by
  have hc := continuous_periodMollifier hρ hL hh hhL
  have hp := periodMollifier_periodic ρ L h
  obtain ⟨B, hb⟩ := PeriodicConvolution.exists_norm_bound hL hc hp
  unfold circleMollify
  simp_rw [intervalIntegral.integral_of_le (by linarith : -(L / 2) ≤ L / 2)]
  exact PeriodicConvolution.integral_smoothing_assoc hL hKp hp hKm hc.measurable hq hK hb x

end Riesz1
