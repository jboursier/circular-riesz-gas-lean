/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Kernel.AdmissibleExamplesPrimitive
public import Riesz1.Kernel.FundamentalSeries
public import Riesz1.ToMathlib.CircleFourierDerivative
public import Riesz1.Frozen.TransportRegularity

/-!
# Transport regularity of subcritical Riesz profiles

The Riesz-profile transport construction starts with a continuous
periodic primitive of the integrable mean-zero Riesz kernel. The primitive is smooth off
the origin and its Fourier derivative is the kernel, including across that origin.
The correctly normalized mean-zero primitive then supplies the transport and its
second derivative envelope, with exponent equal to the profile power.
-/

public section

open MeasureTheory Set Filter Topology intervalIntegral
open scoped ContDiff

namespace Riesz1
namespace Internal

lemma exists_continuous_riesz_primitive (b : RieszExponent) :
    ∃ H : UnitAddCircle → ℝ, Continuous H ∧
      (∀ x : ℝ, (x : UnitAddCircle) ≠ 0 →
        HasDerivAt (fun u : ℝ => H (u : UnitAddCircle)) (rieszRepresentative b x) x) ∧
      (∀ k : ℤ, (2 * Real.pi * Complex.I * (k : ℂ)) *
        fourierCoeff (fun x => (H x : ℂ)) k =
          fourierCoeff (fun x => (rieszRepresentative b x : ℂ)) k) := by
  let f : ℝ → ℝ := fun x => rieszRepresentative b (x : UnitAddCircle)
  have hper : Function.Periodic f 1 := by
    intro x
    simp only [f, AddCircle.coe_add_period]
  have hint01 : IntervalIntegrable f volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    have hi := (AddCircle.measurePreserving_mk (T := 1) 0).integrable_comp_of_integrable
      (integrable_rieszRepresentative b)
    simpa only [zero_add, Function.comp_def, f, IntegrableOn] using hi
  have hint : ∀ a t : ℝ, IntervalIntegrable f volume a t :=
    hper.intervalIntegrable₀ one_ne_zero hint01
  have hzero : ∫ x in (0 : ℝ)..1, f x = 0 := by
    have he := AddCircle.intervalIntegral_preimage 1 0 (rieszRepresentative b)
    simpa only [zero_add, integral_rieszRepresentative] using he
  let F : ℝ → ℝ := fun t => ∫ x in (0 : ℝ)..t, f x
  have hFp : Function.Periodic F 1 := by
    intro t
    apply sub_eq_zero.mp
    change (∫ x in (0 : ℝ)..(t + 1), f x) - (∫ x in (0 : ℝ)..t, f x) = 0
    rw [integral_interval_sub_left (hint 0 (t + 1)) (hint 0 t),
      hper.intervalIntegral_add_eq t 0, zero_add, hzero]
  let H : UnitAddCircle → ℝ := hFp.lift
  have hHcoe (t : ℝ) : H (t : UnitAddCircle) = F t := hFp.lift_coe t
  have hFc : Continuous F := continuous_primitive hint 0
  have hHc : Continuous H := by
    apply isQuotientMap_quotient_mk'.continuous_iff.mpr
    change Continuous (fun t : ℝ => H (t : UnitAddCircle))
    exact hFc.congr fun t => (hHcoe t).symm
  have hsm : ContDiffOn ℝ ∞ f {x : ℝ | (x : UnitAddCircle) ≠ 0} :=
    (fundamental_series b).2.1
  have hfd (x : ℝ) (hx : (x : UnitAddCircle) ≠ 0) : HasDerivAt F (f x) x := by
    apply integral_hasDerivAt_right (hint 0 x)
    · exact hsm.continuousOn.stronglyMeasurableAtFilter isOpen_nonInt x hx
    · exact (hsm.contDiffAt (isOpen_nonInt.mem_nhds hx)).continuousAt
  have hHd (x : ℝ) (hx : (x : UnitAddCircle) ≠ 0) :
      HasDerivAt (fun u : ℝ => H (u : UnitAddCircle)) (f x) x := by
    simpa only [hHcoe] using hfd x hx
  refine ⟨H, hHc, hHd, ?_⟩
  intro k
  have hnull : ∀ᵐ x : ℝ, (x : UnitAddCircle) ≠ 0 := by
    have hcount : {x : ℝ | (x : UnitAddCircle) = 0}.Countable := by
      apply (Set.countable_range (fun n : ℤ => (n : ℝ))).mono
      intro x hx
      obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff 1).mp hx
      exact ⟨n, by simpa using hn⟩
    simpa only [ae_iff, not_not] using hcount.measure_zero (μ := volume)
  have hderae : deriv (fun u : ℝ => H (u : UnitAddCircle)) =ᵐ[volume] f := by
    filter_upwards [hnull] with x hx
    exact (hHd x hx).deriv
  have hi : IntervalIntegrable (deriv (fun u : ℝ => H (u : UnitAddCircle))) volume 0 1 :=
    hint01.congr_ae (ae_restrict_of_ae hderae.symm)
  have hS : Set.Countable {x : ℝ | (x : UnitAddCircle) = 0} := by
    apply (Set.countable_range (fun n : ℤ => (n : ℝ))).mono
    intro x hx
    obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff 1).mp hx
    exact ⟨n, by simpa using hn⟩
  have he := CircleFourier.integral_deriv_mul_fourier hHc hS
    (fun x hx => (hHd x hx).differentiableAt) hi k
  have hcoeff := fourierCoeff_eq_intervalIntegral (fun x => (rieszRepresentative b x : ℂ)) k 0
  simp only [zero_add, Complex.ofReal_one, one_smul, div_one, one_mul] at he hcoeff
  rw [← he, hcoeff]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [hderae] with x hx _
  simp only [smul_eq_mul, hx, f]
  ring

lemma exists_riesz_transport_derivative (P : Parameters) (a : RieszExponent)
    (ha : a.val < P.val.2 / 2)
    (hf : MemLp (fun x : UnitAddCircle => (rieszRepresentative a x : ℂ)) 2 volume) :
    ∃ psi : UnitAddCircle → ℝ, Continuous psi ∧
      (∀ k : ℤ, fourierCoeff (fun x => (psi x : ℂ)) k =
        transportCoeffs P unitLength ⟨rieszRepresentative a, hf⟩ k) ∧
      ∀ x : ℝ, (x : UnitAddCircle) ≠ 0 →
        HasDerivAt (fun u : ℝ => psi (u : UnitAddCircle))
          (-(rieszConstant a / (2 * P.val.1 * rieszConstant (parametersExponent P) *
            rieszConstant ⟨1 - P.val.2 + a.val, by constructor <;> linarith [P.2.2.2, a.2.1]⟩)) *
              rieszRepresentative ⟨1 - P.val.2 + a.val,
                by constructor <;> linarith [P.2.2.2, a.2.1]⟩ x) x := by
  let b : RieszExponent := ⟨1 - P.val.2 + a.val,
    by constructor <;> linarith [P.2.2.2, a.2.1]⟩
  let M := -(rieszConstant a / (2 * P.val.1 * rieszConstant (parametersExponent P) * rieszConstant b))
  obtain ⟨H, hHc, hHd, hHcoeff⟩ := exists_continuous_riesz_primitive b
  let m : ℝ := ∫ x : UnitAddCircle, H x ∂AddCircle.haarAddCircle
  let psi : UnitAddCircle → ℝ := fun x => M * (H x - m)
  refine ⟨psi, (hHc.sub continuous_const).const_mul M, ?_, ?_⟩
  · intro k
    have hc : fourierCoeff (fun x => (psi x : ℂ)) k = (M : ℂ) *
        (fourierCoeff (fun x => (H x : ℂ)) k -
          (m : ℂ) * fourierCoeff (fun _ : UnitAddCircle => (1 : ℂ)) k) := by
      simp only [psi, Complex.ofReal_mul, Complex.ofReal_sub]
      rw [fourierCoeff.const_mul]
      have hiH : Integrable (fun x : UnitAddCircle => (H x : ℂ)) AddCircle.haarAddCircle :=
        integrable_of_continuous_circle (Complex.continuous_ofReal.comp hHc)
      rw [fourierCoeff_sub_const (f := fun x : UnitAddCircle => (H x : ℂ)) hiH (m : ℂ) k]
    rw [hc]
    by_cases hk : k = 0
    · subst k
      have hmean : fourierCoeff (fun x => (H x : ℂ)) 0 = (m : ℂ) := by
        simp only [fourierCoeff, neg_zero, fourier_zero, one_smul, m, integral_complex_ofReal]
      simp only [hmean, fourierCoeff_one, Pi.single_eq_same, mul_one, sub_self, mul_zero,
        transportCoeffs, ↓reduceIte]
    · rw [fourierCoeff_one]
      simp only [Pi.single_apply, hk, ↓reduceIte, mul_zero, sub_zero]
      rw [transportCoeffs, ite_eq_right hk]
      change (M : ℂ) * fourierCoeff (fun x => (H x : ℂ)) k =
        -((|2 * Real.pi * (k : ℝ) / 1| ^ (1 - P.val.2) : ℝ) : ℂ) /
          ((2 * P.val.1 * rieszConstant (parametersExponent P) : ℝ) *
            (2 * Real.pi * Complex.I * (k : ℂ) / 1)) *
          fourierCoeff (fun x => (rieszRepresentative a x : ℂ)) k
      have hω : (2 * Real.pi * Complex.I * (k : ℂ)) ≠ 0 := by
        apply mul_ne_zero
        · exact mul_ne_zero (by exact_mod_cast (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero)) Complex.I_ne_zero
        · exact_mod_cast hk
      apply mul_left_cancel₀ hω
      rw [show (2 * Real.pi * Complex.I * (k : ℂ)) *
          ((M : ℂ) * fourierCoeff (fun x => (H x : ℂ)) k) =
        (M : ℂ) * ((2 * Real.pi * Complex.I * (k : ℂ)) *
          fourierCoeff (fun x => (H x : ℂ)) k) by ring, hHcoeff]
      rw [fourierCoeff_rieszRepresentative, fourierCoeff_rieszRepresentative]
      simp only [hk, ↓reduceIte, div_one]
      have hfreq : |2 * Real.pi * (k : ℝ)| = 2 * Real.pi * |(k : ℝ)| := by
        rw [abs_mul, abs_of_pos (by positivity)]
      have hpos : 0 < 2 * Real.pi * |(k : ℝ)| := by
        have : 0 < |(k : ℝ)| := abs_pos.mpr (by exact_mod_cast hk)
        positivity
      have hexp : (2 * Real.pi * |(k : ℝ)|) ^ (1 - P.val.2) *
          (2 * Real.pi * |(k : ℝ)|) ^ (a.val - 1) =
            (2 * Real.pi * |(k : ℝ)|) ^ (b.val - 1) := by
        rw [← Real.rpow_add hpos]
        congr 1
        dsimp [b]
        ring
      have hcb : (rieszConstant b : ℂ) ≠ 0 := by exact_mod_cast (rieszConstant_pos b).ne'
      have hcs : (rieszConstant (parametersExponent P) : ℂ) ≠ 0 :=
        by exact_mod_cast (rieszConstant_pos _).ne'
      have hβ : (P.val.1 : ℂ) ≠ 0 := by exact_mod_cast P.property.1.ne'
      rw [hfreq]
      dsimp only [M]
      push_cast
      have hexpc := congrArg (fun x : ℝ => (x : ℂ)) hexp
      push_cast at hexpc
      field_simp [hω, hcb, hcs, hβ]
      rw [← hexpc]
      ring
  · intro x hx
    exact ((hHd x hx).sub_const m).const_mul M

end Internal

/-- The A2–A3 clauses for a subcritical Riesz profile, with exponent `a` and the single
mark zero. -/
theorem transportRegularity_riesz (P : Parameters) (a : RieszExponent)
    (ha : a.val < P.val.2 / 2) :
    ∃ hf : MemLp (fun x : UnitAddCircle => (rieszRepresentative a x : ℂ)) 2 volume,
      ∃ C : ℝ, 0 < C ∧ TransportRegularity P unitLength ⟨rieszRepresentative a, hf⟩
        ⟨1, zero_lt_one⟩ (fun _ => 0) a.val C := by
  have hf := (circleSobolev_riesz_of_lt (parametersExponent P) a ha).1
  let b : RieszExponent := ⟨1 - P.val.2 + a.val,
    by constructor <;> linarith [P.2.2.2, a.2.1]⟩
  let M := -(rieszConstant a / (2 * P.val.1 * rieszConstant (parametersExponent P) * rieszConstant b))
  obtain ⟨psi, hpsic, hpsicoeff, hd⟩ := Internal.exists_riesz_transport_derivative P a ha hf
  have hd' (x : ℝ) (hx : (x : UnitAddCircle) ≠ 0) :
      HasDerivAt (fun u : ℝ => psi (u : UnitAddCircle))
        (M * rieszRepresentative b x) x := hd x hx
  obtain ⟨_, hsm, _, _, _, _, _, _, _, _, hbound, _, _⟩ := fundamental_series b
  obtain ⟨D, hD, hDb⟩ := hbound 1
  have hcd : ContDiffOn ℝ ∞ (fun u : ℝ => psi (u : UnitAddCircle))
      {x : ℝ | (x : UnitAddCircle) ≠ 0} := by
    apply (contDiffOn_infty_iff_deriv_of_isOpen isOpen_nonInt).mpr
    refine ⟨fun x hx => (hd' x hx).differentiableAt.differentiableWithinAt, ?_⟩
    exact (contDiffOn_const.mul hsm).congr fun x hx => (hd' x hx).deriv
  have hdd (x : ℝ) (hx : (x : UnitAddCircle) ≠ 0) :
      deriv (deriv (fun u : ℝ => psi (u : UnitAddCircle))) x =
        M * deriv (fun u : ℝ => rieszRepresentative b u) x := by
    have he : deriv (fun u : ℝ => psi (u : UnitAddCircle)) =ᶠ[𝓝 x]
        fun u : ℝ => M * rieszRepresentative b u := by
      filter_upwards [isOpen_nonInt.mem_nhds hx] with u hu
      exact (hd' u hu).deriv
    rw [he.deriv_eq]
    exact ((hsm.contDiffAt (isOpen_nonInt.mem_nhds hx)).differentiableAt
      (by simp)).hasDerivAt.const_mul M |>.deriv
  have hmem : MemLp (fun x => (psi x : ℂ)) 2 volume :=
    memLp_of_continuous_circle (Complex.continuous_ofReal.comp hpsic)
  refine ⟨hf, |M| * D + 1, by positivity, ?_⟩
  dsimp only [TransportRegularity]
  have hinj : Function.Injective (fun _j : Fin 1 => (0 : UnitAddCircle)) := by
    intro i j _
    apply Fin.ext
    have hi := i.isLt
    have hj := j.isLt
    omega
  refine ⟨hinj, ⟨⟨psi, hmem⟩, hpsicoeff, ?_⟩⟩
  dsimp only
  intro x hx
  have hx0 : (x : UnitAddCircle) ≠ 0 := hx ⟨0, zero_lt_one⟩
  refine ⟨(hcd.contDiffAt (isOpen_nonInt.mem_nhds hx0)).of_le (by simp), ?_⟩
  have hnear : dist (x : UnitAddCircle) 0 ≤ 1 := by
    rw [dist_zero_right]
    exact (AddCircle.norm_le_half_period (p := (1 : ℝ)) one_ne_zero).trans (by norm_num)
  have hfar : ¬ 1 ≤ dist (x : UnitAddCircle) 0 := by
    rw [dist_zero_right]
    have hh := AddCircle.norm_le_half_period (p := (1 : ℝ)) (x := (x : UnitAddCircle)) one_ne_zero
    norm_num at hh
    linarith
  change |deriv (deriv (fun u : ℝ => psi (u : UnitAddCircle))) x| ≤
    (|M| * D + 1) * ((if dist (x : UnitAddCircle) 0 ≤ 1 then
      ∑ _j : Fin 1, dist (x : UnitAddCircle) 0 ^ (-2 + P.val.2 - a.val) else 0) +
      (if 1 ≤ dist (x : UnitAddCircle) 0 then dist (x : UnitAddCircle) 0 ^ (-3 + P.val.2) else 0))
  simp only [hnear, hfar, ↓reduceIte, add_zero, Fin.sum_univ_one]
  rw [hdd x hx0, abs_mul]
  have hh : |deriv (fun u : ℝ => rieszRepresentative b u) x| ≤
      D * dist (x : UnitAddCircle) 0 ^ (-2 + P.val.2 - a.val) := by
    simpa only [iteratedDeriv_one, Nat.cast_one,
      show -b.val - 1 = -2 + P.val.2 - a.val by dsimp [b]; ring] using hDb x hx0
  have hp : 0 ≤ dist (x : UnitAddCircle) 0 ^ (-2 + P.val.2 - a.val) := by positivity
  calc
    |M| * |deriv (fun u : ℝ => rieszRepresentative b u) x|
      ≤ |M| * (D * dist (x : UnitAddCircle) 0 ^ (-2 + P.val.2 - a.val)) :=
        mul_le_mul_of_nonneg_left hh (abs_nonneg _)
    _ ≤ (|M| * D + 1) * dist (x : UnitAddCircle) 0 ^ (-2 + P.val.2 - a.val) := by nlinarith

end Riesz1
