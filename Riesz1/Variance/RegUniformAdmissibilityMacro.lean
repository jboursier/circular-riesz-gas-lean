/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.RegUniformSecondTransport
public import Riesz1.Variance.RegUniformPrimitive
public import Riesz1.Frozen.Admissible

/-!
# Uniform macroscopic admissibility after smoothing

The last clause of Lemma 5.1 on the unit circle:
the actual smoothed profile and its difference have uniform (A1)-(A3)
data. The strict exponent is unchanged. The endpoint permits a fixed increase.
-/

public section

open MeasureTheory
open scoped ContDiff

namespace Riesz1
namespace Internal

/-- On the unit circle a nonempty sum of negative marked-distance powers
is at least one away from the marks. -/
theorem unit_mark_power_sum_one_le (n : ℕ+) (marks : Fin (n : ℕ) → ℝ)
    (x : ℝ) (hx : ∀ j, (x : Circle unitLength) ≠ (marks j : Circle unitLength))
    {e : ℝ} (he : e ≤ 0) :
    1 ≤ ∑ j, dist (x : Circle unitLength) (marks j : Circle unitLength) ^ e := by
  let j : Fin (n : ℕ) := ⟨0, n.pos⟩
  have hd : dist (x : Circle unitLength) (marks j : Circle unitLength) ≤ 1 := by
    rw [dist_eq_norm]
    have hh : ‖(x : Circle unitLength) - (marks j : Circle unitLength)‖ ≤
        |(unitLength).val| / 2 := AddCircle.norm_le_half_period _ unitLength.property.ne'
    exact hh.trans (by norm_num [unitLength])
  exact (Real.one_le_rpow_of_pos_of_le_one_of_nonpos (dist_pos.mpr (hx j)) hd he).trans
    (Finset.single_le_sum (f := fun j => dist (x : Circle unitLength)
      (marks j : Circle unitLength) ^ e) (fun _ _ => by positivity) (Finset.mem_univ j))

end Internal

/-- Uniform admissibility data for both macroscopic smoothing families.
The constant precedes `h`. Both functions and both transports are the actual
regularization and difference. Take `α' = α` in the strict case and any permitted
fixed increase at the endpoint. -/
theorem regUniform_admissibility_macroscopic (P : Parameters) (p : Profile)
    (η B : ℝ) (n : ℕ+) (marks : Fin (n : ℕ) → ℝ) (α α' C₀ : ℝ)
    (hη : 0 < η) (hB : 0 ≤ B) (hC₀ : 0 ≤ C₀)
    (hα0 : P.val.2 - 1 ≤ α) (hα1 : α < P.val.2 / 2) (hα' : α ≤ α')
    (hα'0 : P.val.2 - 1 < α') (hα'1 : α' < P.val.2 / 2)
    (hprim : PrimitiveRegularity unitLength η P.val.2 B ⟨p.val, p.property⟩)
    (hreg : TransportRegularity P unitLength ⟨p.val, p.property⟩ n marks α C₀)
    (ρ : ℝ → ℝ) (hρ : IsMollifier ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ h : ℝ, 0 < h → h ≤ 1 →
      ∃ g e : Profile,
        ContDiff ℝ ∞ (fun t : ℝ => g.val (t : Circle unitLength)) ∧
        (∀ x : ℝ, g.val (x : Circle unitLength) =
          circleMollify ρ 1 h (fun t : ℝ => p.val (t : Circle unitLength)) x) ∧
        (∀ x, e.val x = p.val x - g.val x) ∧
        PrimitiveRegularity unitLength η P.val.2 B ⟨g.val, g.property⟩ ∧
        PrimitiveRegularity unitLength η P.val.2 (2 * B) ⟨e.val, e.property⟩ ∧
        TransportRegularity P unitLength ⟨g.val, g.property⟩ n marks α' C ∧
        TransportRegularity P unitLength ⟨e.val, e.property⟩ n marks α' C := by
  have : Fact (0 < (unitLength).val) := ⟨unitLength.property⟩
  obtain ⟨K, hK, ψ, hc, hψ, hcoeff, hi, hAC, _, hpoint⟩ := macroscopic_regTransportBounds
    P p η B n marks α α' C₀ hη hB hC₀ hα0 hα1 hα' hα'0 hprim hreg
  obtain ⟨D, hD, hb⟩ := Internal.smoothed_transport_second_of_capped_bound hρ
    (b := 1 - P.val.2 + α') (by linarith) (by linarith [P.property.2.1])
  let Q := D * K * ((n : ℕ) + 1)
  let C := 2 * (K + Q)
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have he : -2 + P.val.2 - α' ≤ 0 := by linarith
  refine ⟨C, hC, fun h hh hh1 => ?_⟩
  obtain ⟨g, _, hgs, hgv, hgp, hep⟩ := regUniform_primitive ρ hρ unitLength η P.val.2 B
    ⟨p.val, p.property⟩ hprim h hh
  change Profile at g
  let e : Profile := ⟨(fun x => p.val x - g.val x), by
    exact (p.property.sub g.property).ae_eq
      (ae_of_all _ fun x => by simp only [Pi.sub_apply, Complex.ofReal_sub])⟩
  obtain ⟨φ, _, hφs, hφv, hφcoeff⟩ :=
    Internal.exists_circleMollify_L2 hρ unitLength hh ⟨ψ, hψ⟩
  have hfi : LocallyIntegrable (fun t : ℝ => p.val (t : Circle unitLength)) volume :=
    Internal.locallyIntegrable_circle_lift (T := (unitLength).val)
      (f := p.val) (complexL2Integrable unitLength (fun x => (p.val x : ℂ)) p.property).re
  have hfp : Function.Periodic (fun t : ℝ => p.val (t : Circle unitLength)) (unitLength).val := by
    intro t
    simp only [AddCircle.coe_add_period]
  have hgf (k : ℤ) : coeff unitLength ⟨(fun x => (g.val x : ℂ)),
      complexL2Integrable unitLength _ g.property⟩ k =
      coeff unitLength ⟨(fun x => (p.val x : ℂ)), complexL2Integrable unitLength _ p.property⟩ k *
        (mollifierFT ρ (h * k / (unitLength).val) : ℂ) :=
    Internal.fourierCoeff_circleMollify hρ hh hfi hfp p.val g.val (fun _ => rfl) hgv k
  have hφtransport (k : ℤ) : coeff unitLength ⟨(fun x => (φ.val x : ℂ)),
      complexL2Integrable unitLength _ φ.property⟩ k = transportCoeffs P unitLength ⟨g.val, g.property⟩ k := by
    rw [hφcoeff, hcoeff]
    by_cases hk : k = 0
    · simp only [transportCoeffs, hk, ite_true, zero_mul]
    · simp only [transportCoeffs, hk, ite_false]
      rw [hgf]
      ring
  have hφbound (x : ℝ) : |deriv (deriv (fun t : ℝ => φ.val (t : Circle unitLength))) x| ≤
      Q * (1 + ∑ j, max (dist (x : Circle unitLength) (marks j : Circle unitLength)) h ^
        (-2 + P.val.2 - α')) := by
    rw [show (fun t : ℝ => φ.val (t : Circle unitLength)) =
      circleMollify ρ 1 h (fun t : ℝ => ψ (t : Circle unitLength)) from funext hφv]
    have hp := hb unitLength (by norm_num [unitLength]) n marks K hK.le ψ hc hi hAC
      (by simpa only [show -(1 - P.val.2 + α') = -1 + P.val.2 - α' by ring,
        show -1 - (1 - P.val.2 + α') = -2 + P.val.2 - α' by ring] using hpoint) h hh hh1 x
    simpa only [Q, unitLength,
      show -1 - (1 - P.val.2 + α') = -2 + P.val.2 - α' by ring] using hp
  have hinner (x : ℝ) (hx : ∀ j, (x : Circle unitLength) ≠ (marks j : Circle unitLength)) :
      |deriv (deriv (fun t : ℝ => ψ (t : Circle unitLength))) x| ≤
        2 * K * (∑ j, dist (x : Circle unitLength) (marks j : Circle unitLength) ^
          (-2 + P.val.2 - α')) ∧
      |deriv (deriv (fun t : ℝ => φ.val (t : Circle unitLength))) x| ≤
        2 * Q * (∑ j, dist (x : Circle unitLength) (marks j : Circle unitLength) ^
          (-2 + P.val.2 - α')) := by
    have hone := Internal.unit_mark_power_sum_one_le n marks x hx he
    have hp := ((hpoint x hx).2.2).trans (mul_le_mul_of_nonneg_left
      (cappedMarkDistance_rpow_le_one_add_sum _ _ _) hK.le)
    have hm : (∑ j, max (dist (x : Circle unitLength) (marks j : Circle unitLength)) h ^
        (-2 + P.val.2 - α')) ≤
        ∑ j, dist (x : Circle unitLength) (marks j : Circle unitLength) ^ (-2 + P.val.2 - α') := by
      apply Finset.sum_le_sum
      intro j _
      exact Real.rpow_le_rpow_of_nonpos (dist_pos.mpr (hx j)) (le_max_left _ _) he
    constructor
    · nlinarith
    · nlinarith [hφbound x, mul_le_mul_of_nonneg_left hm hQ.le]
  let χ : {f : Circle unitLength → ℝ // MemLp (fun x => (f x : ℂ)) 2 (arclength unitLength)} :=
    ⟨(fun x => ψ x - φ.val x), by
      exact (hψ.sub φ.property).ae_eq
        (ae_of_all _ fun x => by simp only [Pi.sub_apply, Complex.ofReal_sub])⟩
  have hχtransport (k : ℤ) : coeff unitLength ⟨(fun x => (χ.val x : ℂ)),
      complexL2Integrable unitLength _ χ.property⟩ k = transportCoeffs P unitLength ⟨e.val, e.property⟩ k := by
    rw [Internal.coeff_sub_real_L2 unitLength ⟨ψ, hψ⟩ φ, hcoeff, hφtransport]
    by_cases hk : k = 0
    · simp only [transportCoeffs, hk, ite_true, sub_self]
    · simp only [transportCoeffs, hk, ite_false]
      rw [Internal.coeff_sub_real_L2 unitLength ⟨p.val, p.property⟩ g]
      ring
  have hregion (x : ℝ) : dist (x : Circle unitLength) 0 < 1 := by
    rw [dist_zero_right]
    have hh : ‖(x : Circle unitLength)‖ ≤ |(unitLength).val| / 2 :=
      AddCircle.norm_le_half_period _ unitLength.property.ne'
    exact hh.trans_lt (by norm_num [unitLength])
  refine ⟨g, e, hgs, hgv, fun _ => rfl, hgp, hep, ?_, ?_⟩
  · refine ⟨hreg.1, φ, hφtransport, fun x hx => ?_⟩
    refine ⟨(hφs.of_le (by simp)).contDiffAt, ?_⟩
    rw [ite_eq_left (hregion x).le, ite_eq_right (not_le.mpr (hregion x)), add_zero]
    have hs : 0 ≤ ∑ j, dist (x : Circle unitLength) (marks j : Circle unitLength) ^
        (-2 + P.val.2 - α') := by positivity
    exact (hinner x hx).2.trans (by dsimp [C]; nlinarith)
  · refine ⟨hreg.1, χ, hχtransport, fun x hx => ?_⟩
    have hψs := (hpoint x hx).1
    have hφs' : ContDiff ℝ 2 (fun t : ℝ => φ.val (t : Circle unitLength)) := hφs.of_le (by simp)
    refine ⟨hψs.sub hφs'.contDiffAt, ?_⟩
    rw [ite_eq_left (hregion x).le, ite_eq_right (not_le.mpr (hregion x)), add_zero]
    have heq : deriv (deriv (fun t : ℝ => χ.val (t : Circle unitLength))) x =
        deriv (deriv (fun t : ℝ => ψ (t : Circle unitLength))) x -
          deriv (deriv (fun t : ℝ => φ.val (t : Circle unitLength))) x := by
      have hnear := hψs.eventually (by norm_num : (2 : WithTop ℕ∞) ≠ ∞)
      have hd : deriv (fun t : ℝ => χ.val (t : Circle unitLength)) =ᶠ[nhds x]
          fun t => deriv (fun t : ℝ => ψ (t : Circle unitLength)) t -
            deriv (fun t : ℝ => φ.val (t : Circle unitLength)) t := by
        filter_upwards [hnear] with y hy
        exact deriv_fun_sub (hy.differentiableAt (by norm_num))
          (hφs'.differentiable (by norm_num) y)
      rw [hd.deriv_eq]
      exact deriv_fun_sub
        ((hψs.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num))
        ((hφs'.contDiffAt.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num))
    rw [heq]
    exact (abs_sub _ _).trans (by dsimp [C]; linarith [(hinner x hx).1, (hinner x hx).2])

/-- The same macroscopic family conclusion expressed with the complete
`Admissible` predicate and fixed quantitative data for both families. -/
theorem regUniform_admissible_macroscopic (P : Parameters) (p : Profile)
    (η B : ℝ) (n : ℕ+) (marks : Fin (n : ℕ) → ℝ) (α α' C₀ : ℝ)
    (hη : 0 < η) (hηs : η < P.val.2) (hB : 0 < B) (hC₀ : 0 ≤ C₀)
    (hα0 : P.val.2 - 1 ≤ α) (hα1 : α < P.val.2 / 2) (hα' : α ≤ α')
    (hα'0 : P.val.2 - 1 < α') (hα'1 : α' < P.val.2 / 2)
    (hprim : PrimitiveRegularity unitLength η P.val.2 B ⟨p.val, p.property⟩)
    (hreg : TransportRegularity P unitLength ⟨p.val, p.property⟩ n marks α C₀)
    (ρ : ℝ → ℝ) (hρ : IsMollifier ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ h : ℝ, 0 < h → h ≤ 1 →
      ∃ g e : Profile,
        (∀ x : ℝ, g.val (x : Circle unitLength) =
          circleMollify ρ 1 h (fun t : ℝ => p.val (t : Circle unitLength)) x) ∧
        (∀ x, e.val x = p.val x - g.val x) ∧
        ∀ ell : Scales, (∀ N, (ell N).val = 1) →
          Admissible P g ell α' (η, B, C, ⟨n, marks⟩) ∧
          Admissible P e ell α' (η, 2 * B, C, ⟨n, marks⟩) := by
  obtain ⟨C, hC, hb⟩ := regUniform_admissibility_macroscopic P p η B n marks α α' C₀
    hη hB.le hC₀ hα0 hα1 hα' hα'0 hα'1 hprim hreg ρ hρ
  refine ⟨C, hC, fun h hh hh1 => ?_⟩
  obtain ⟨g, e, _, hgv, hev, hgp, hep, hgt, het⟩ := hb h hh hh1
  refine ⟨g, e, hgv, hev, fun ell hell => ?_⟩
  exact ⟨⟨hα'0.le, hα'1, hη, hηs, hB, hC, Or.inl ⟨hell, hgp, hgt⟩⟩,
    ⟨hα'0.le, hα'1, hη, hηs, by positivity, hC, Or.inl ⟨hell, hep, het⟩⟩⟩

end Riesz1
