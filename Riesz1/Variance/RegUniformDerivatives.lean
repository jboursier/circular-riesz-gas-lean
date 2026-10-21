/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.RegUniformDerivativeFourier
public import Riesz1.Kernel.AdmissibilityRegularityUniformCompact

/-!
# The profile derivative clauses of uniform regularization

Lemma 5.1, first and second classical derivatives, in
both alternatives. Compact-profile constants precede the scale sequence,
the observation circle and the regularization radius.
-/

public section

open MeasureTheory Filter
open scoped ContDiff Topology

namespace Riesz1

/-- Lemma 5.1: the profile derivative rates for a fixed
macroscopic profile, with no added Fourier or Sobolev hypotheses. -/
theorem regUniform_derivatives_macroscopic (P : Parameters) (p : Profile)
    (η B : ℝ) (n : ℕ+) (marks : Fin (n : ℕ) → ℝ) (α C₀ ε : ℝ)
    (hη : 0 < η) (hB : 0 ≤ B) (hC₀ : 0 ≤ C₀)
    (hα0 : P.val.2 - 1 ≤ α) (hα1 : α < P.val.2 / 2) (hε : 0 < ε)
    (hprim : PrimitiveRegularity unitLength η P.val.2 B ⟨p.val, p.property⟩)
    (hreg : TransportRegularity P unitLength ⟨p.val, p.property⟩ n marks α C₀)
    (ρ : ℝ → ℝ) (hρ : IsMollifier ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ h : ℝ, 0 < h → h ≤ 1 →
      ∃ ph : Profile, Continuous ph.val ∧
        ContDiff ℝ ∞ (fun x : ℝ => ph.val (x : UnitAddCircle)) ∧
        (∀ x : ℝ, ph.val (x : UnitAddCircle) = circleMollify ρ 1 h
          (fun t : ℝ => p.val (t : UnitAddCircle)) x) ∧
        (∀ x : ℝ, |deriv (fun t : ℝ => ph.val (t : UnitAddCircle)) x| ≤
          C * h ^ (-1 - α - ε)) ∧
        ∀ x : ℝ, |deriv (deriv (fun t : ℝ => ph.val (t : UnitAddCircle))) x| ≤
          C * h ^ (-2 - α - ε) := by
  let δ := min ε (1 - α) / 2
  have hδ : 0 < δ := by dsimp [δ]; exact half_pos (lt_min hε (by linarith [P.property.2.2]))
  have hδε : δ ≤ ε := by dsimp [δ]; linarith [min_le_left ε (1 - α)]
  have hδg : α - 1 + δ ≤ 0 := by
    dsimp [δ]
    linarith [min_le_right ε (1 - α), P.property.2.2]
  obtain ⟨K, _, hdec⟩ := coeff_decay_of_primitive_transportRegularity P unitLength
    η B hη hB ⟨p.val, p.property⟩ n marks α C₀ hα0 hα1 hC₀ hprim hreg δ hδ
  let Z := ∫ x : UnitAddCircle, ‖(p.val x : ℂ)‖ ∂AddCircle.haarAddCircle
  have hlo (k : ℤ) : (1 : ℝ) * ‖fourierCoeff (fun x => (p.val x : ℂ)) k‖ ≤ Z := by
    rw [one_mul, fourierCoeff]
    calc _ ≤ ∫ x : UnitAddCircle, ‖fourier (-k) x • (p.val x : ℂ)‖ ∂AddCircle.haarAddCircle :=
        norm_integral_le_integral_norm _
      _ = Z := by simp only [norm_smul, fourier_apply, Circle.norm_coe, one_mul, Z]
  have hhi (k : ℤ) (hk : 1 ≤ |2 * Real.pi * (k : ℝ) / 1|) :
      (1 : ℝ) * ‖fourierCoeff (fun x => (p.val x : ℂ)) k‖ ≤
        K * |2 * Real.pi * (k : ℝ) / 1| ^ (α - 1 + δ) := by
    simpa only [coeff, unitLength, one_mul, inv_one, mul_one] using hdec k hk
  have hbound := Internal.nonzero_coeff_power_bound (by norm_num : (0 : ℝ) < 1)
    hδg hlo hhi
  obtain ⟨C, hC, hb⟩ := Internal.circleMollify_derivative_rates hρ
    (K := (|Z| + |K| + 1) * (2 * Real.pi) ^ (α - 1 + δ))
    (g := α - 1 + δ) (by linarith [P.property.2.1])
  refine ⟨C, hC, fun h hh hh1 => ?_⟩
  obtain ⟨ph, hpc, hps, hpv, hp1, hp2⟩ := hb unitLength ⟨p.val, p.property⟩ hbound h hh
  refine ⟨ph, hpc, hps, hpv, fun x => ?_, fun x => ?_⟩
  · exact (hp1 x).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge hh hh1 (by linarith)) hC.le)
  · exact (hp2 x).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge hh hh1 (by linarith)) hC.le)

/-- Lemma 5.1: compact-profile derivative rates on every
observation circle. The constant precedes the witnessing shrinking sequence
and every observation length, including lengths outside that sequence. -/
theorem regUniform_derivatives_compact (P : Parameters) (p : Profile) (hp : CompactProfile p)
    (η B : ℝ) (n : ℕ+) (marks : Fin (n : ℕ) → ℝ) (α C₀ ε : ℝ)
    (hη : 0 < η) (hB : 0 ≤ B) (hC₀ : 0 ≤ C₀)
    (hα0 : P.val.2 - 1 ≤ α) (hα1 : α < P.val.2 / 2) (hε : 0 < ε)
    (ρ : ℝ → ℝ) (hρ : IsMollifier ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ell : Scales,
      Tendsto (fun k : ℕ => (ell ⟨k + 1, Nat.succ_pos k⟩).val) atTop (𝓝 0) →
      (∀ N, PrimitiveRegularity (observationLength (ell N)) η P.val.2 B
          ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ ∧
        TransportRegularity P (observationLength (ell N))
          ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩
            n marks α C₀) →
      ∀ (a : Scale) (h : ℝ), 0 < h → h ≤ 1 →
        ∃ ph : {f : Circle (observationLength a) → ℝ //
            MemLp (fun x => (f x : ℂ)) 2 (arclength (observationLength a))},
          Continuous ph.val ∧
          ContDiff ℝ ∞ (fun x : ℝ => ph.val (x : Circle (observationLength a))) ∧
          (∀ x : ℝ, ph.val (x : Circle (observationLength a)) =
            circleMollify ρ (observationLength a).val h
              (fun t : ℝ => periodizedProfile p (observationLength a)
                (t : Circle (observationLength a))) x) ∧
          (∀ x : ℝ, |deriv (fun t : ℝ => ph.val (t : Circle (observationLength a))) x| ≤
            C * h ^ (-1 - α - ε)) ∧
          ∀ x : ℝ, |deriv (deriv (fun t : ℝ => ph.val (t : Circle (observationLength a)))) x| ≤
            C * h ^ (-2 - α - ε) := by
  let δ := min ε (1 - α) / 2
  have hδ : 0 < δ := by dsimp [δ]; exact half_pos (lt_min hε (by linarith [P.property.2.2]))
  have hδε : δ ≤ ε := by dsimp [δ]; linarith [min_le_left ε (1 - α)]
  have hδg : α - 1 + δ ≤ 0 := by
    dsimp [δ]
    linarith [min_le_right ε (1 - α), P.property.2.2]
  obtain ⟨K, _, hdec⟩ := uniform_compact_profile_coeff_decay P p hp η B hη hB
    n marks α C₀ hα0 hα1 hC₀ δ hδ
  let Z := ∫ x : ℝ, |zeroExtension p x|
  obtain ⟨C, hC, hb⟩ := Internal.circleMollify_derivative_rates hρ
    (K := (|Z| + |K| + 1) * (2 * Real.pi) ^ (α - 1 + δ))
    (g := α - 1 + δ) (by linarith [P.property.2.1])
  refine ⟨C, hC, fun ell hell hfamily a h hh hh1 => ?_⟩
  let L := observationLength a
  have : Fact (0 < L.val) := ⟨L.property⟩
  let f := (⟨periodizedProfile p L, periodizedProfileL2 p a⟩ :
    {f : Circle L → ℝ // MemLp (fun x => (f x : ℂ)) 2 (arclength L)})
  let c := fun k => coeff L ⟨(fun x => (f.val x : ℂ)), complexL2Integrable L _ f.property⟩ k
  have hlo (k : ℤ) : L.val * ‖c k‖ ≤ Z := by
    have ht := norm_zeroExtension_fourierIntegral_le p (2 * Real.pi * (k : ℝ) / L.val)
    rw [← length_mul_periodizedProfile_coeff p a k, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos L.property] at ht
    exact ht
  have hhi (k : ℤ) (hk : 1 ≤ |2 * Real.pi * (k : ℝ) / L.val|) :
      L.val * ‖c k‖ ≤ K * |2 * Real.pi * (k : ℝ) / L.val| ^ (α - 1 + δ) := by
    have ht := mul_le_mul_of_nonneg_left (hdec ell hell hfamily a k hk) L.property.le
    change L.val * ‖c k‖ ≤ L.val *
      (K * L.val⁻¹ * |2 * Real.pi * (k : ℝ) / L.val| ^ (α - 1 + δ)) at ht
    convert ht using 1
    field_simp [L.property.ne']
  have hbound := Internal.nonzero_coeff_power_bound L.property hδg hlo hhi
  obtain ⟨ph, hpc, hps, hpv, hp1, hp2⟩ := hb L f hbound h hh
  refine ⟨ph, hpc, hps, hpv, fun x => ?_, fun x => ?_⟩
  · exact (hp1 x).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge hh hh1 (by linarith)) hC.le)
  · exact (hp2 x).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge hh hh1 (by linarith)) hC.le)

end Riesz1
