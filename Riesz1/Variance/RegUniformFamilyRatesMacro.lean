/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.RegUniformFamilyFourier

/-! # Analytic smoothing rates uniform over the macroscopic families

Lemma 5.1, with constants before both smoothing parameters.
-/

public section

open MeasureTheory Filter
open scoped ENNReal ContDiff Topology

namespace Riesz1

/-- Variance and profile derivative rates uniform over the regularized
macroscopic profile and its error, at every positive family radius. -/
theorem regUniform_familyRates_macroscopic (P : Parameters) (p : Profile)
    (η B : ℝ) (n : ℕ+) (marks : Fin (n : ℕ) → ℝ) (α C₀ ε : ℝ)
    (hη : 0 < η) (hB : 0 ≤ B) (hC₀ : 0 ≤ C₀)
    (hα0 : P.val.2 - 1 ≤ α) (hα1 : α < P.val.2 / 2) (hε : 0 < ε)
    (hprim : PrimitiveRegularity unitLength η P.val.2 B ⟨p.val, p.property⟩)
    (hreg : TransportRegularity P unitLength ⟨p.val, p.property⟩ n marks α C₀)
    (ρ : ℝ → ℝ) (hρ : IsMollifier ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t → ∃ g e : Profile,
      (∀ x : ℝ, g.val (x : UnitAddCircle) = circleMollify ρ 1 t
        (fun y : ℝ => p.val (y : UnitAddCircle)) x) ∧
      (∀ x, e.val x = p.val x - g.val x) ∧
      ∀ v : Profile, (v = g ∨ v = e) → ∀ h : ℝ, 0 < h → h ≤ 1 →
        ∃ q d : Profile,
          ContDiff ℝ ∞ (fun x : ℝ => q.val (x : UnitAddCircle)) ∧
          (∀ x : ℝ, q.val (x : UnitAddCircle) = circleMollify ρ 1 h
            (fun y : ℝ => v.val (y : UnitAddCircle)) x) ∧
          (∀ x, d.val x = v.val x - q.val x) ∧
          circleVariance P d ⟨1, by norm_num⟩ < ⊤ ∧
          Real.sqrt (circleVariance P d ⟨1, by norm_num⟩).toReal ≤
            C * h ^ (P.val.2 / 2 - α - ε) ∧
          ∀ x : ℝ,
            |deriv (circleMollify ρ 1 h (fun y : ℝ => v.val (y : UnitAddCircle))) x| ≤
              C * h ^ (-1 - α - ε) ∧
            |deriv (deriv (circleMollify ρ 1 h (fun y : ℝ => v.val (y : UnitAddCircle)))) x| ≤
              C * h ^ (-2 - α - ε) := by
  let d := P.val.2 / 2 - α
  let u := (max 0 (d - ε) + d) / 2
  let δ := (d - u) / 2
  have hd : 0 < d := by dsimp [d]; linarith
  have hmax : max 0 (d - ε) < d := max_lt hd (by linarith)
  have hu : u < d := by dsimp [u]; linarith
  have hu0 : 0 < u := by dsimp [u]; linarith [le_max_left 0 (d - ε)]
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hδε : δ ≤ ε := by
    dsimp [δ, u]
    linarith [le_max_right 0 (d - ε)]
  have hδg : α - 1 + δ ≤ 0 := by
    dsimp [δ, d] at *
    linarith [P.property.2.2]
  have hg : -2 < α - 1 + δ := by linarith [P.property.2.1]
  obtain ⟨K, _, hdec⟩ := coeff_decay_of_primitive_transportRegularity P unitLength
    η B hη hB ⟨p.val, p.property⟩ n marks α C₀ hα0 hα1 hC₀ hprim hreg δ hδ
  let Z := ∫ x : UnitAddCircle, ‖(p.val x : ℂ)‖ ∂AddCircle.haarAddCircle
  obtain ⟨V, hV, hvariance⟩ := Internal.variance_smoothing_of_common_coeff_bounds P α ε (2 * Z) (2 * K)
    hα0 hα1 hε ρ hρ
  obtain ⟨D, hD, hderivative⟩ := Internal.circleMollify_derivative_rates hρ
    (K := (|2 * Z| + |2 * K| + 1) * (2 * Real.pi) ^ (α - 1 + δ)) hg
  refine ⟨V + D, by positivity, fun t ht => ?_⟩
  have : Fact (0 < (unitLength).val) := ⟨unitLength.property⟩
  obtain ⟨g, _, _, hgv, _, _⟩ := regUniform_primitive ρ hρ unitLength η P.val.2 B
    ⟨p.val, p.property⟩ hprim t ht
  change Profile at g
  let e : Profile := ⟨(fun x => p.val x - g.val x), by
    exact (p.property.sub g.property).ae_eq
      (ae_of_all _ fun x => by simp only [Pi.sub_apply, Complex.ofReal_sub])⟩
  refine ⟨g, e, hgv, fun _ => rfl, fun v hv h hh hh1 => ?_⟩
  let L := unitLength
  let a : Scale := ⟨1, by norm_num⟩
  let f := (⟨v.val, v.property⟩ :
    {f : Circle L → ℝ // MemLp (fun x => (f x : ℂ)) 2 (arclength L)})
  have hdom (k : ℤ) : ‖coeff L ⟨(fun x => (f.val x : ℂ)), complexL2Integrable L _ f.property⟩ k‖ ≤
      2 * ‖coeff L ⟨(fun x => (p.val x : ℂ)),
        complexL2Integrable L _ p.property⟩ k‖ := by
    have hb := Internal.smoothing_family_coeff_le hρ L
      ⟨p.val, p.property⟩ ⟨g.val, g.property⟩ ⟨e.val, e.property⟩ ht hgv (fun _ => rfl) k
    rcases hv with rfl | rfl
    · exact hb.1.trans (by linarith [norm_nonneg (coeff L ⟨(fun x => (p.val x : ℂ)),
        complexL2Integrable L _ p.property⟩ k)])
    · exact hb.2
  have hlo (k : ℤ) : L.val * ‖coeff L ⟨(fun x => (f.val x : ℂ)),
      complexL2Integrable L _ f.property⟩ k‖ ≤ 2 * Z := by
    have hb : ‖coeff L ⟨(fun x => (p.val x : ℂ)), complexL2Integrable L _ p.property⟩ k‖ ≤ Z := by
      change ‖∫ x : UnitAddCircle, fourier (-k) x • (p.val x : ℂ) ∂AddCircle.haarAddCircle‖ ≤ _
      calc _ ≤ ∫ x : UnitAddCircle, ‖fourier (-k) x • (p.val x : ℂ)‖ ∂AddCircle.haarAddCircle :=
          norm_integral_le_integral_norm _
        _ = Z := by simp only [norm_smul, fourier_apply, Circle.norm_coe, one_mul, Z]
    change (1 : ℝ) * _ ≤ _
    nlinarith [hdom k]
  have hhi (k : ℤ) (hk : 1 ≤ |2 * Real.pi * (k : ℝ) / L.val|) :
      L.val * ‖coeff L ⟨(fun x => (f.val x : ℂ)), complexL2Integrable L _ f.property⟩ k‖ ≤
        (2 * K) * |2 * Real.pi * (k : ℝ) / L.val| ^ (α - 1 + δ) := by
    have hb := hdec k hk
    change ‖coeff L ⟨(fun x => (p.val x : ℂ)), complexL2Integrable L _ p.property⟩ k‖ ≤
      K * (1 : ℝ)⁻¹ * |2 * Real.pi * (k : ℝ) / 1| ^ (α - 1 + δ) at hb
    simp only [inv_one, mul_one] at hb
    change (1 : ℝ) * _ ≤ (2 * K) * |2 * Real.pi * (k : ℝ) / 1| ^ (α - 1 + δ)
    nlinarith [hdom k]
  obtain ⟨q, err, hqs, hqv, herr, hfin, hrate⟩ := hvariance a v (by simpa only [a, observationLength, inv_one, L, unitLength, coeff] using hlo)
    (by simpa only [a, observationLength, inv_one, L, unitLength, coeff] using hhi) h hh hh1
  have hqv' : ∀ x : ℝ, q.val (x : UnitAddCircle) =
      circleMollify ρ 1 h (fun y : ℝ => v.val (y : UnitAddCircle)) x := by
    simpa only [a, observationLength, inv_one, div_one] using hqv
  have hfin' : circleVariance P err ⟨1, by norm_num⟩ < ⊤ := by
    simpa only [a, Real.one_rpow, ENNReal.ofReal_one, one_mul] using hfin
  have hrate' : Real.sqrt (circleVariance P err ⟨1, by norm_num⟩).toReal ≤
      V * h ^ (P.val.2 / 2 - α - ε) := by
    simpa only [a, Real.one_rpow, ENNReal.ofReal_one, one_mul] using hrate
  have hpower := Internal.nonzero_coeff_power_bound L.property hδg hlo hhi
  obtain ⟨ph, _, _, hphv, hph1, hph2⟩ := hderivative L f hpower h hh
  refine ⟨q, err, hqs, hqv', herr, hfin', hrate'.trans ?_, fun x => ?_⟩
  · exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  · have heq : (fun y : ℝ => ph.val (y : Circle L)) =
        circleMollify ρ L.val h (fun y : ℝ => v.val (y : Circle L)) := funext hphv
    have h1 := hph1 x
    have h2 := hph2 x
    rw [heq] at h1 h2
    constructor
    · exact h1.trans ((mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_ge hh hh1 (by linarith : -1 - α - ε ≤ -(α - 1 + δ) - 2)) hD.le).trans
        (mul_le_mul_of_nonneg_right (by linarith : D ≤ V + D) (by positivity)))
    · exact h2.trans ((mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_ge hh hh1 (by linarith : -2 - α - ε ≤ -(α - 1 + δ) - 3)) hD.le).trans
        (mul_le_mul_of_nonneg_right (by linarith : D ≤ V + D) (by positivity)))

end Riesz1
