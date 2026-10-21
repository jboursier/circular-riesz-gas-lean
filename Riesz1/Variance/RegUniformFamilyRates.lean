/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.RegUniformFamilyFourier
public import Riesz1.Variance.RegUniformAdmissibilityCompact

/-! # Analytic smoothing rates uniform over the two compact families

Lemma 5.1: variance and classical profile derivative
rates with constants before both regularization parameters and every circle.
-/

public section

open MeasureTheory Filter
open scoped ENNReal ContDiff Topology

namespace Riesz1

/-- The variance and profile derivative bounds are uniform over both fixed
compact families. The family parameter is `t`. The analytic smoothing parameter
is `h`. All constants and the common support margin precede both parameters. -/
theorem regUniform_familyRates_compact (P : Parameters) (p : Profile)
    (hp : CompactProfile p) (η B : ℝ) (n : ℕ+) (marks : Fin (n : ℕ) → ℝ)
    (α C₀ ε : ℝ) (hη : 0 < η) (hB : 0 ≤ B) (hC₀ : 0 ≤ C₀)
    (hα0 : P.val.2 - 1 ≤ α) (hα1 : α < P.val.2 / 2) (hε : 0 < ε)
    (ρ : ℝ → ℝ) (hρ : IsMollifier ρ) :
    ∃ C H r : ℝ, 0 < C ∧ 0 < H ∧ 0 < r ∧ r < 1 / 2 ∧
      ∀ ell : Scales,
        Tendsto (fun k : ℕ => (ell ⟨k + 1, Nat.succ_pos k⟩).val) atTop (𝓝 0) →
        (∀ N, PrimitiveRegularity (observationLength (ell N)) η P.val.2 B
            ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ ∧
          TransportRegularity P (observationLength (ell N))
            ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩
              n marks α C₀) →
        ∀ t : ℝ, 0 < t → t ≤ H → ∃ g e : Profile,
          (∀ x : ℝ, g.val (x : UnitAddCircle) = circleMollify ρ 1 t
            (fun y : ℝ => p.val (y : UnitAddCircle)) x) ∧
          (∀ x, e.val x = p.val x - g.val x) ∧
          (∀ x : ℝ, r ≤ |x| → zeroExtension g x = 0) ∧
          (∀ᵐ x : ℝ, r ≤ |x| → zeroExtension e x = 0) ∧
          ∀ v : Profile, (v = g ∨ v = e) → ∀ (a : Scale) (h : ℝ), 0 < h → h ≤ 1 →
            ∃ q d : Profile,
              ContDiff ℝ ∞ (fun x : ℝ => q.val (x : UnitAddCircle)) ∧
              (∀ x : ℝ, q.val (x : UnitAddCircle) = circleMollify ρ 1
                (h / (observationLength a).val) (fun y : ℝ => testAtScale v a (y : UnitAddCircle)) x) ∧
              (∀ x, d.val x = testAtScale v a x - q.val x) ∧
              ENNReal.ofReal (a.val ^ (-P.val.2)) * circleVariance P d ⟨1, by norm_num⟩ < ⊤ ∧
              Real.sqrt (ENNReal.ofReal (a.val ^ (-P.val.2)) *
                circleVariance P d ⟨1, by norm_num⟩).toReal ≤ C * h ^ (P.val.2 / 2 - α - ε) ∧
              ∀ x : ℝ,
                |deriv (circleMollify ρ (observationLength a).val h
                  (fun y : ℝ => periodizedProfile v (observationLength a) (y : Circle (observationLength a)))) x| ≤
                    C * h ^ (-1 - α - ε) ∧
                |deriv (deriv (circleMollify ρ (observationLength a).val h
                  (fun y : ℝ => periodizedProfile v (observationLength a) (y : Circle (observationLength a))))) x| ≤
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
  obtain ⟨K, _, hdec⟩ := uniform_compact_profile_coeff_decay P p hp η B hη hB
    n marks α C₀ hα0 hα1 hC₀ δ hδ
  let Z := ∫ x : ℝ, |zeroExtension p x|
  obtain ⟨V, hV, hvariance⟩ := Internal.variance_smoothing_of_common_coeff_bounds P α ε (2 * Z) (2 * K)
    hα0 hα1 hε ρ hρ
  obtain ⟨D, hD, hderivative⟩ := Internal.circleMollify_derivative_rates hρ
    (K := (|2 * Z| + |2 * K| + 1) * (2 * Real.pi) ^ (α - 1 + δ)) hg
  obtain ⟨H, r, hH, hr, hrhalf, hcompat⟩ := regUniform_compactCompatibility p hp ρ hρ
  refine ⟨V + D, H, r, by positivity, hH, hr, hrhalf, fun ell hell hfamily t ht htH => ?_⟩
  obtain ⟨g, e, _, hgv, hev, hgzero, hezero, _, _, hcomp⟩ := hcompat t ht htH
  refine ⟨g, e, hgv, hev, hgzero, hezero, fun v hv a h hh hh1 => ?_⟩
  let L := observationLength a
  have : Fact (0 < L.val) := ⟨L.property⟩
  let f := (⟨periodizedProfile v L, periodizedProfileL2 v a⟩ :
    {f : Circle L → ℝ // MemLp (fun x => (f x : ℂ)) 2 (arclength L)})
  have hdom (k : ℤ) : ‖coeff L ⟨(fun x => (f.val x : ℂ)), complexL2Integrable L _ f.property⟩ k‖ ≤
      2 * ‖coeff L ⟨(fun x => (periodizedProfile p L x : ℂ)),
        complexL2Integrable L _ (periodizedProfileL2 p a)⟩ k‖ := by
    have hb := Internal.smoothing_family_coeff_le hρ L
      ⟨periodizedProfile p L, periodizedProfileL2 p a⟩
      ⟨periodizedProfile g L, periodizedProfileL2 g a⟩
      ⟨periodizedProfile e L, periodizedProfileL2 e a⟩ ht
      (fun x => (hcomp a x).1) (fun y => by
        induction y using Quotient.inductionOn with
        | h x => exact (hcomp a x).2.trans (congrArg
            (fun z => periodizedProfile p L (x : Circle L) - z) (hcomp a x).1.symm)) k
    rcases hv with rfl | rfl
    · exact hb.1.trans (by linarith [norm_nonneg (coeff L ⟨(fun x => (periodizedProfile p L x : ℂ)),
        complexL2Integrable L _ (periodizedProfileL2 p a)⟩ k)])
    · exact hb.2
  have hlo (k : ℤ) : L.val * ‖coeff L ⟨(fun x => (f.val x : ℂ)),
      complexL2Integrable L _ f.property⟩ k‖ ≤ 2 * Z := by
    have hb := norm_zeroExtension_fourierIntegral_le p (2 * Real.pi * (k : ℝ) / L.val)
    rw [← length_mul_periodizedProfile_coeff p a k, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos L.property] at hb
    nlinarith [mul_le_mul_of_nonneg_left (hdom k) L.property.le]
  have hhi (k : ℤ) (hk : 1 ≤ |2 * Real.pi * (k : ℝ) / L.val|) :
      L.val * ‖coeff L ⟨(fun x => (f.val x : ℂ)), complexL2Integrable L _ f.property⟩ k‖ ≤
        (2 * K) * |2 * Real.pi * (k : ℝ) / L.val| ^ (α - 1 + δ) := by
    have hb := mul_le_mul_of_nonneg_left (hdec ell hell hfamily a k hk) L.property.le
    have hid : L.val * (K * L.val⁻¹ * |2 * Real.pi * (k : ℝ) / L.val| ^ (α - 1 + δ)) =
        K * |2 * Real.pi * (k : ℝ) / L.val| ^ (α - 1 + δ) := by field_simp [L.property.ne']
    rw [hid] at hb
    nlinarith [mul_le_mul_of_nonneg_left (hdom k) L.property.le]
  have hw (k : ℤ) : fourierCoeff (fun x => (testAtScale v a x : ℂ)) k =
      coeff L ⟨(fun x => (f.val x : ℂ)), complexL2Integrable L _ f.property⟩ k :=
    testAtScale_coeff_eq_periodized v a k
  obtain ⟨q, err, hqs, hqv, herr, hfin, hrate⟩ := hvariance a
    ⟨testAtScale v a, testAtScaleL2 v a⟩
    (fun k => by rw [hw]; exact hlo k) (fun k hk => by rw [hw]; exact hhi k hk) h hh hh1
  have hpower := Internal.nonzero_coeff_power_bound L.property hδg hlo hhi
  obtain ⟨ph, _, _, hphv, hph1, hph2⟩ := hderivative L f hpower h hh
  refine ⟨q, err, hqs, hqv, herr, hfin, hrate.trans ?_, fun x => ?_⟩
  · exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  · have heq : (fun y : ℝ => ph.val (y : Circle L)) =
        circleMollify ρ L.val h (fun y : ℝ => periodizedProfile v L (y : Circle L)) := funext hphv
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
