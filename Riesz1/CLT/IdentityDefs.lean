/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.CircleMollifyL2
public import Riesz1.ToMathlib.CircleMollifyBounds
public import Riesz1.ToMathlib.MollifierPointwise.Derivative
public import Riesz1.Variance.LoopMasterCharacterization
public import Riesz1.Frozen.CircleSobolev

/-!
# Objects of the exact approximate Gaussian identity

These are the objects for the identity in the proof of Theorem 3 that are not defined elsewhere.

* `cltDelta`: the smoothing radius `δ_N = K^{-d}`, with `K = Nℓ` and `d = (2-s)/(4+s)`.
* `cltRegCircle`: the regularized test profile `ξ_reg = ξ ⋆ ρ_δ` on the circle of length `ℓ⁻¹`,
  defined as the descent of `circleMollify`, the convolution with the mollifier.
* `cltScaledProfile`: the unit-circle profile `x ↦ ξ_reg(x/ℓ)`, whose Sobolev seminorm gives the
  variance `σ_reg²`.
* `cltVarianceENN`: the variance functional evaluated on that profile, in
  `ℝ≥0∞` so that no junk value arises when the seminorm is infinite.

Everything is stated for a fixed `Parameters` value `P`, a particle number `N`, a scale
`ℓ ∈ (0, 1]` and a mollifier `ρ`, following the paper.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ContDiff ENNReal

namespace Riesz1

/-- The smoothing radius `δ_N = K^{-d}` with `K = Nℓ` and `d = (2 - s)/(4 + s)`. -/
noncomputable def cltDelta (P : Parameters) (N : ℕ+) (ℓ : Ioc (0 : ℝ) 1) : ℝ :=
  ((N : ℝ) * ℓ.val) ^ (-((2 - P.val.2) / (4 + P.val.2)))

/-- The smoothing radius is positive. -/
lemma cltDelta_pos (P : Parameters) (N : ℕ+) (ℓ : Ioc (0 : ℝ) 1) : 0 < cltDelta P N ℓ := by
  unfold cltDelta
  exact Real.rpow_pos_of_pos (mul_pos (by exact_mod_cast N.pos) ℓ.property.1) _

/-- The periodic regularization of a unit test profile at length `L`, as a function on the
circle: the descent of `circleMollify ρ L h` to `Circle L`. -/
noncomputable def cltRegCircle {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) (L : Length) {h : ℝ} (hh : 0 < h)
    (ξ : {f : Circle L → ℝ // MemLp (fun x => (f x : ℂ)) 2 (arclength L)}) : Circle L → ℝ :=
  haveI : Fact (0 < L.val) := ⟨L.property⟩
  (Internal.circleMollify_periodic hρ L.property hh
    (Internal.locallyIntegrable_circle_lift (complexL2Integrable L _ ξ.property).re)
    (fun x => by simp only [AddCircle.coe_add_period])).lift

/-- The descended regularization evaluates to `circleMollify` on the lift. -/
lemma cltRegCircle_coe {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) (L : Length) {h : ℝ} (hh : 0 < h)
    (ξ : {f : Circle L → ℝ // MemLp (fun x => (f x : ℂ)) 2 (arclength L)}) (x : ℝ) :
    cltRegCircle hρ L hh ξ (x : Circle L) = circleMollify ρ L.val h
      (fun t : ℝ => ξ.val (t : Circle L)) x := by
  unfold cltRegCircle
  exact Function.Periodic.lift_coe _ x

/-- The regularized profile is smooth on the line (`ξ_reg` is `C^∞` on `ℝ`). -/
lemma cltRegCircle_contDiff {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) (L : Length) {h : ℝ} (hh : 0 < h)
    (ξ : {f : Circle L → ℝ // MemLp (fun x => (f x : ℂ)) 2 (arclength L)}) :
    ContDiff ℝ ∞ (fun x : ℝ => cltRegCircle hρ L hh ξ (x : Circle L)) := by
  have : Fact (0 < L.val) := ⟨L.property⟩
  have hF : LocallyIntegrable (fun t : ℝ => ξ.val (t : Circle L)) volume :=
    Internal.locallyIntegrable_circle_lift (complexL2Integrable L _ ξ.property).re
  have hp : Function.Periodic (fun t : ℝ => ξ.val (t : Circle L)) L.val := by
    intro x
    simp only [AddCircle.coe_add_period]
  simp_rw [cltRegCircle_coe hρ L hh ξ]
  exact contDiff_circleMollify hρ L.property hh hF hp

/-- The regularized profile at scale `ℓ` on the line, `u ↦ ξ_reg(u/ℓ)`. It is
one-periodic, since `ξ_reg` has period `ℓ⁻¹`. -/
noncomputable def cltScaledFun {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) (ℓ : Ioc (0 : ℝ) 1) {h : ℝ}
    (hh : 0 < h) (ξ : {f : Circle (loopMasterLength ℓ) → ℝ //
      MemLp (fun x => (f x : ℂ)) 2 (arclength (loopMasterLength ℓ))}) (u : ℝ) : ℝ :=
  cltRegCircle hρ (loopMasterLength ℓ) hh ξ ((u / ℓ.val : ℝ) : Circle (loopMasterLength ℓ))

/-- The scaled regularized profile is one-periodic. -/
lemma cltScaledFun_periodic {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) (ℓ : Ioc (0 : ℝ) 1) {h : ℝ}
    (hh : 0 < h) (ξ : {f : Circle (loopMasterLength ℓ) → ℝ //
      MemLp (fun x => (f x : ℂ)) 2 (arclength (loopMasterLength ℓ))}) :
    Function.Periodic (cltScaledFun hρ ℓ hh ξ) 1 := by
  intro u
  unfold cltScaledFun
  have h1 : (((u + 1) / ℓ.val : ℝ) : Circle (loopMasterLength ℓ)) =
      ((u / ℓ.val : ℝ) : Circle (loopMasterLength ℓ)) := by
    have := AddCircle.coe_add_period (p := (loopMasterLength ℓ).val) (u / ℓ.val)
    rw [add_div, one_div]
    exact this
  rw [h1]

/-- The unit-circle lift of the scaled regularized profile, `UnitAddCircle → ℝ`. -/
noncomputable def cltScaledLift {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) (ℓ : Ioc (0 : ℝ) 1) {h : ℝ}
    (hh : 0 < h) (ξ : {f : Circle (loopMasterLength ℓ) → ℝ //
      MemLp (fun x => (f x : ℂ)) 2 (arclength (loopMasterLength ℓ))}) : UnitAddCircle → ℝ :=
  (cltScaledFun_periodic hρ ℓ hh ξ).lift

/-- The unit-circle lift of the scaled regularized profile is continuous. -/
lemma cltScaledLift_continuous {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) (ℓ : Ioc (0 : ℝ) 1) {h : ℝ}
    (hh : 0 < h) (ξ : {f : Circle (loopMasterLength ℓ) → ℝ //
      MemLp (fun x => (f x : ℂ)) 2 (arclength (loopMasterLength ℓ))}) :
    Continuous (cltScaledLift hρ ℓ hh ξ) := by
  unfold cltScaledLift
  refine Riesz1.continuous_lift_periodic ?_ _
  exact (cltRegCircle_contDiff hρ (loopMasterLength ℓ) hh ξ).continuous.comp
    (continuous_id.div_const ℓ.val)

/-- The scaled regularized profile is square integrable on the unit circle. -/
lemma cltScaledLift_memLp {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) (ℓ : Ioc (0 : ℝ) 1) {h : ℝ}
    (hh : 0 < h) (ξ : {f : Circle (loopMasterLength ℓ) → ℝ //
      MemLp (fun x => (f x : ℂ)) 2 (arclength (loopMasterLength ℓ))}) :
    MemLp (fun x => (cltScaledLift hρ ℓ hh ξ x : ℂ)) 2 volume := by
  have hc := cltScaledLift_continuous hρ ℓ hh ξ
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hc.continuousOn
  have hb : MemLp (fun x => (cltScaledLift hρ ℓ hh ξ x : ℂ)) ⊤ volume := by
    refine memLp_top_of_bound (by fun_prop) C (ae_of_all _ fun x => ?_)
    simpa using hC x (mem_univ x)
  exact hb.mono_exponent le_top

/-- The variance functional `σ_ℓ²`, evaluated on a unit-circle profile `g`: the
constant of `circleVariance` times the Sobolev seminorm of order `(1 - s)/2`. It takes values in
`ℝ≥0∞`, so an infinite seminorm is not replaced by a junk value. -/
noncomputable def cltVariance (P : Parameters) (ℓ : Ioc (0 : ℝ) 1)
    (g : {f : UnitAddCircle → ℂ // MemLp f 2 volume}) : ℝ≥0∞ :=
  ENNReal.ofReal ((2 * Real.pi) ^ (1 - P.val.2) /
    (2 * P.val.1 * rieszConstant (parametersExponent P)) * ℓ.val ^ (-P.val.2)) *
    circleSobolevSq ((1 - P.val.2) / 2) g

end Riesz1

end
