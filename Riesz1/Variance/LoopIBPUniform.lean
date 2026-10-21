/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.LoopIBPMoments
public import Riesz1.Gibbs.UniformMarginals
public import Riesz1.Variance.LoopScaleDifferential
public import Riesz1.ToMathlib.CircleBasics
import all Riesz1.Variance.LoopScale
import all Riesz1.Variance.LoopForceEnergy
import all Riesz1.Variance.LoopForce

/-!
# Integration identities for one particle

Proposition 5.5, the case `N = 1`. For one particle the Gibbs law is
uniform on the circle, the energy and its Hessian vanish, and the operator `𝓛` reduces to
`-Δ`. The first coordinate of the configuration has uniform circle law
(`map_coord_gibbsMeasure`), so every expectation becomes an integral over one period. The
three identities then follow from the periodic integration by parts on one period.

The general-`N` definitions `loopOperatorPotential`, `gibbsCov`, `gradDotPotential` and
`frobeniusSqDiag` are stated for every `N`. The theorems are stated for `N = 1`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology UnitAddCircle
open scoped ContDiff

namespace Riesz1

/-- The operator `𝓛Φ = β ∇H_N·∇Φ - ΔΦ` of Proposition 5.5, with the
potential `Φ = Φ_{ψ,a}`, evaluated on a configuration. -/
noncomputable def loopOperatorPotential (P : Parameters) (N : ℕ+) (ℓ : Ioc (0 : ℝ) 1) (a : ℝ)
    (ψ : LoopScaleProfile ℓ.val) (X : Configuration N) : ℝ :=
  P.val.1 * ∑ k : Fin (N : ℕ), partialDeriv (energyLift (parametersExponent P) (N : ℕ)) k X.val *
      partialDeriv (loopScalePotential ℓ a ψ (N : ℕ)) k X.val
    - laplacian (loopScalePotential ℓ a ψ (N : ℕ)) X.val

/-- The gradient pairing `∇F · ∇Φ` at a lift. -/
noncomputable def gradDotPotential {N : ℕ} (F Φ : (Fin N → ℝ) → ℝ) (x : Fin N → ℝ) : ℝ :=
  ∑ k : Fin N, partialDeriv F k x * partialDeriv Φ k x

/-- The Gibbs covariance `Cov(F, G) = ∫ (F - EF)(G - EG)`. -/
noncomputable def gibbsCov {N : ℕ+} (μ : Measure (Configuration N)) (F G : Configuration N → ℝ) :
    ℝ :=
  ∫ X, (F X - ∫ Y, F Y ∂μ) * (G X - ∫ Y, G Y ∂μ) ∂μ

/-- The Frobenius square of the diagonal matrix `DΨ_ψ = diag(ψ'(xᵢ/ℓ))`. -/
noncomputable def frobeniusSqDiag {N : ℕ+} (ℓ : Ioc (0 : ℝ) 1) (ψ : LoopScaleProfile ℓ.val)
    (X : Configuration N) : ℝ :=
  ∑ k : Fin (N : ℕ), deriv ψ.val (X.val k / ℓ.val) ^ 2

/-- A smooth function on the configuration torus: smooth on `ℝ^N` and one-periodic in each
coordinate. -/
def IsTorusSmooth {N : ℕ} (F : (Fin N → ℝ) → ℝ) : Prop :=
  ContDiff ℝ ∞ F ∧ ∀ (k : Fin N) (x : Fin N → ℝ), F (Function.update x k (x k + 1)) = F x

/-! ### Elementary facts for one particle -/

/-- The lifted energy of one particle vanishes. -/
lemma energyLift_one (s : RieszExponent) (x : Fin 1 → ℝ) : energyLift s 1 x = 0 := by
  unfold energyLift
  simp

/-- The first partial derivative of the lifted energy vanishes for one particle. -/
lemma partialDeriv_energyLift_one (s : RieszExponent) (k : Fin 1) (x : Fin 1 → ℝ) :
    partialDeriv (energyLift s 1) k x = 0 := by
  have h : energyLift s 1 = fun _ => 0 := funext (energyLift_one s)
  rw [h]
  unfold partialDeriv
  simp

/-- The second partial derivative of the lifted energy vanishes for one particle. -/
lemma hessian_energyLift_one (s : RieszExponent) (k l : Fin 1) (x : Fin 1 → ℝ) :
    partialDeriv (fun y => partialDeriv (energyLift s 1) k y) l x = 0 := by
  have h : (fun y => partialDeriv (energyLift s 1) k y) = fun _ => 0 :=
    funext fun y => partialDeriv_energyLift_one s k y
  rw [h]
  unfold partialDeriv
  simp

/-- The Hessian quadratic term vanishes for one particle, since the energy is constant. -/
lemma hessianQuadratic_one (P : Parameters) (ℓ : Ioc (0 : ℝ) 1) (ψ : LoopScaleProfile ℓ.val)
    (X : Configuration 1) : hessianQuadratic P 1 ℓ ψ X = 0 := by
  simp [hessianQuadratic, hessian_energyLift_one]

/-- The coordinate of a configuration of one particle is the constant lift of its first
coordinate. -/
lemma fun_eq_const_of_fin_one (x : Fin 1 → ℝ) : x = fun _ => x 0 := by
  funext i
  rw [Subsingleton.elim i 0]

/-- Updating the unique coordinate of a one-particle lift replaces the whole lift by a constant. -/
lemma update_fin_one (x : Fin 1 → ℝ) (t : ℝ) : Function.update x 0 t = fun _ => t := by
  funext i
  rw [Subsingleton.elim i 0]
  simp

/-- The partial derivative in the unique coordinate is the derivative along the diagonal. -/
lemma partialDeriv_fin_one (F : (Fin 1 → ℝ) → ℝ) (x : Fin 1 → ℝ) :
    partialDeriv F 0 x = deriv (fun t : ℝ => F (fun _ => t)) (x 0) := by
  unfold partialDeriv
  congr 1
  funext t
  rw [update_fin_one]

/-! ### The Gibbs law of one particle -/

/-- Expectations of one-periodic continuous functions of the first coordinate of a configuration
of one particle are integrals over one period. -/
theorem integral_gibbs_one (P : Parameters) {g : ℝ → ℝ} (hg : Continuous g)
    (hp : Function.Periodic g 1) :
    ∫ X : Configuration 1, g (X.val 0) ∂gibbsMeasure P 1 = ∫ t in (0 : ℝ)..1, g t := by
  have hs : ∀ a b : ℝ, QuotientAddGroup.leftRel (AddSubgroup.zmultiples (1 : ℝ)) a b →
      g a = g b := by
    intro a b h'
    rw [QuotientAddGroup.leftRel_apply] at h'
    obtain ⟨k, hk⟩ := h'
    exact (hp.zsmul k _).symm.trans congr(g $(add_eq_of_eq_neg_add hk))
  have hG : Continuous hp.lift := hg.quotient_liftOn' hs
  have hmap := map_coord_gibbsMeasure P 1 0
  have hXeq : (fun X : Configuration 1 => g (X.val 0)) =
      fun X : Configuration 1 => hp.lift ((X.val 0 : ℝ) : UnitAddCircle) := by
    funext X
    rw [Function.Periodic.lift_coe]
  rw [hXeq, ← integral_map (measurable_coord 1 0).aemeasurable
    (f := hp.lift) hG.aestronglyMeasurable, hmap,
    ← UnitAddCircle.intervalIntegral_preimage 0 hp.lift]
  simp only [zero_add]
  exact intervalIntegral.integral_congr fun t _ => Function.Periodic.lift_coe hp t

/-- Composing with division by `ℓ` makes a `ℓ⁻¹`-periodic function one-periodic. -/
lemma periodic_div_scale {ℓ : ℝ} {g : ℝ → ℝ} (hg : Function.Periodic g ℓ⁻¹) :
    Function.Periodic (fun t => g (t / ℓ)) 1 := by
  intro t
  simp only
  rw [add_div, one_div]
  exact hg (t / ℓ)

/-- The derivative of a `ℓ⁻¹`-periodic smooth function integrates to zero over one period of
`t ↦ t/ℓ`, that is over `[0, 1]`. -/
lemma integral_deriv_scale_eq_zero {ℓ : ℝ} (hℓ : 0 < ℓ) {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hp : Function.Periodic ψ ℓ⁻¹) :
    ∫ u in (0 : ℝ)..1, deriv ψ (u / ℓ) = 0 := by
  rw [intervalIntegral.integral_comp_div (deriv ψ) hℓ.ne', zero_div, one_div]
  have hd : ∀ x ∈ uIcc (0 : ℝ) (ℓ⁻¹), HasDerivAt ψ (deriv ψ x) x := fun x _ =>
    ((hψ.differentiable (by simp)) x).hasDerivAt
  have hint : IntervalIntegrable (deriv ψ) volume 0 (ℓ⁻¹) :=
    (hψ.continuous_deriv (by simp)).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint]
  have h0 : ψ ℓ⁻¹ = ψ 0 := by simpa using hp 0
  rw [h0, sub_self, smul_zero]

/-- Integration by parts on one period: `∫₀¹ f'(t) ℓψ(t/ℓ) dt = -∫₀¹ f(t) ψ'(t/ℓ) dt` for a
one-periodic smooth `f` and a `ℓ⁻¹`-periodic smooth `ψ`. -/
lemma integral_ibp_scale {ℓ : ℝ} (hℓ : 0 < ℓ) {f ψ : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfp : Function.Periodic f 1) (hψ : ContDiff ℝ ∞ ψ) (hψp : Function.Periodic ψ ℓ⁻¹) :
    ∫ t in (0 : ℝ)..1, deriv f t * (ℓ * ψ (t / ℓ)) =
      -∫ t in (0 : ℝ)..1, f t * deriv ψ (t / ℓ) := by
  -- The product `G(t) = f(t) ℓψ(t/ℓ)` has derivative `f' ℓψ + f ψ'(t/ℓ)`.
  set G : ℝ → ℝ := fun t => f t * (ℓ * ψ (t / ℓ)) with hG
  have hGd : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt G
      (deriv f t * (ℓ * ψ (t / ℓ)) + f t * deriv ψ (t / ℓ)) t := by
    intro t _
    have hfd : HasDerivAt f (deriv f t) t := ((hf.differentiable (by simp)) t).hasDerivAt
    have hψd : HasDerivAt (fun t => ψ (t / ℓ)) (deriv ψ (t / ℓ) * ℓ⁻¹) t := by
      have h := ((hψ.differentiable (by simp)) (t / ℓ)).hasDerivAt.comp t
        ((hasDerivAt_id t).div_const ℓ)
      simpa [Function.comp_def, div_eq_mul_inv] using h
    have hgd : HasDerivAt (fun t => ℓ * ψ (t / ℓ)) (ℓ * (deriv ψ (t / ℓ) * ℓ⁻¹)) t :=
      hψd.const_mul ℓ
    have hsimp : ℓ * (deriv ψ (t / ℓ) * ℓ⁻¹) = deriv ψ (t / ℓ) := by
      field_simp
    have hprod := hfd.mul hgd
    rw [hsimp] at hprod
    exact hprod
  have hf' : Continuous (deriv f) := hf.continuous_deriv (by simp)
  have hψ' : Continuous (deriv ψ) := hψ.continuous_deriv (by simp)
  have hfc : Continuous f := hf.continuous
  have hψc : Continuous ψ := hψ.continuous
  have hc1 : Continuous (fun t => deriv f t * (ℓ * ψ (t / ℓ))) := by fun_prop
  have hc2 : Continuous (fun t => f t * deriv ψ (t / ℓ)) := by fun_prop
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hGd
    ((hc1.add hc2).intervalIntegrable _ _)
  rw [intervalIntegral.integral_add (hc1.intervalIntegrable _ _) (hc2.intervalIntegrable _ _)]
    at hFTC
  -- Boundary terms cancel by periodicity.
  have hb : G 1 - G 0 = 0 := by
    simp only [hG, zero_div]
    have h1 : f 1 = f 0 := by simpa using hfp 0
    have h2 : ψ (1 / ℓ) = ψ 0 := by
      have := hψp 0
      simpa [one_div] using this
    rw [h1, h2]
    ring
  linarith [hFTC, hb]

/-- A continuous one-periodic function of the first coordinate is integrable under the Gibbs law
of one particle. -/
theorem integrable_gibbs_one (P : Parameters) {g : ℝ → ℝ} (hg : Continuous g)
    (hp : Function.Periodic g 1) :
    Integrable (fun X : Configuration 1 => g (X.val 0)) (gibbsMeasure P 1) := by
  have hs : ∀ a b : ℝ, QuotientAddGroup.leftRel (AddSubgroup.zmultiples (1 : ℝ)) a b →
      g a = g b := by
    intro a b h'
    rw [QuotientAddGroup.leftRel_apply] at h'
    obtain ⟨k, hk⟩ := h'
    exact (hp.zsmul k _).symm.trans congr(g $(add_eq_of_eq_neg_add hk))
  have hG : Continuous hp.lift := hg.quotient_liftOn' hs
  have hmap := map_coord_gibbsMeasure P 1 0
  have hI : Integrable hp.lift ((gibbsMeasure P 1).map
      (fun X : Configuration 1 => ((X.val 0 : ℝ) : UnitAddCircle))) := by
    rw [hmap]
    exact hG.integrable_of_hasCompactSupport (isCompact_univ.of_isClosed_subset
      (isClosed_tsupport _) (subset_univ _))
  have hcomp : (fun X : Configuration 1 => g (X.val 0)) =
      hp.lift ∘ (fun X : Configuration 1 => ((X.val 0 : ℝ) : UnitAddCircle)) := by
    funext X
    exact (Function.Periodic.lift_coe hp _).symm
  rw [hcomp]
  exact (integrable_map_measure hG.aestronglyMeasurable
    (measurable_coord 1 0).aemeasurable).mp hI

/-- The index type of one particle has a single element. -/
lemma fin_one_pnat_eq_zero (x : Fin ((1 : ℕ+) : ℕ)) : x = 0 := by
  have h1 := x.isLt
  have h2 : ((1 : ℕ+) : ℕ) = 1 := rfl
  exact Fin.ext (by omega)

/-- The operator `𝓛Φ` of one particle is `-a ψ'(x/ℓ)`: the lifted energy and its gradient
vanish, and the Laplacian of `Φ_{ψ,a}` is `a` times the mean-free derivative. -/
theorem loopOperatorPotential_one (P : Parameters) (ℓ : Ioc (0 : ℝ) 1) (a : ℝ)
    (ψ : LoopScaleProfile ℓ.val) (hψ : ContDiff ℝ ∞ ψ.val) (X : Configuration 1) :
    loopOperatorPotential P 1 ℓ a ψ X = -(a * deriv ψ.val (X.val 0 / ℓ.val)) := by
  have hgrad : ∀ k : Fin ((1 : ℕ+) : ℕ), partialDeriv (energyLift (parametersExponent P)
      ((1 : ℕ+) : ℕ)) k X.val = 0 := fun k => partialDeriv_energyLift_one _ k X.val
  have hlap : laplacian (loopScalePotential ℓ a ψ ((1 : ℕ+) : ℕ)) X.val =
      a * deriv ψ.val (X.val 0 / ℓ.val) := by
    rw [laplacian_loopScalePotential ℓ a ψ hψ]
    have hmean : ∫ u in (0 : ℝ)..1, deriv ψ.val (u / ℓ.val) = 0 :=
      integral_deriv_scale_eq_zero ℓ.property.1 hψ ψ.property.1
    unfold fluctIntegral
    rw [hmean, Fintype.sum_eq_single (0 : Fin ((1 : ℕ+) : ℕ))
      (fun x hx => absurd (fin_one_pnat_eq_zero x) hx)]
    simp
  unfold loopOperatorPotential
  simp only [hgrad, zero_mul, Finset.sum_const_zero, mul_zero, zero_sub, hlap]

/-- The frobenius square of one particle is the square of the single derivative. -/
lemma frobeniusSqDiag_one (ℓ : Ioc (0 : ℝ) 1) (ψ : LoopScaleProfile ℓ.val)
    (X : Configuration 1) : frobeniusSqDiag ℓ ψ X = deriv ψ.val (X.val 0 / ℓ.val) ^ 2 := by
  unfold frobeniusSqDiag
  rw [Fintype.sum_eq_single (0 : Fin ((1 : ℕ+) : ℕ))
    (fun x hx => absurd (fin_one_pnat_eq_zero x) hx)]

/-- The mean of the operator vanishes for one particle (Proposition 5.5,
clause 1). -/
theorem integral_loopOperatorPotential_one (P : Parameters) (ℓ : Ioc (0 : ℝ) 1) (a : ℝ)
    (ψ : LoopScaleProfile ℓ.val) (hψ : ContDiff ℝ ∞ ψ.val) :
    ∫ X : Configuration 1, loopOperatorPotential P 1 ℓ a ψ X ∂gibbsMeasure P 1 = 0 := by
  have hfun : (fun X : Configuration 1 => loopOperatorPotential P 1 ℓ a ψ X) =
      fun X => -(a * deriv ψ.val (X.val 0 / ℓ.val)) :=
    funext fun X => loopOperatorPotential_one P ℓ a ψ hψ X
  have hdc : Continuous (deriv ψ.val) := hψ.continuous_deriv (by simp)
  have hp1 : Function.Periodic (fun t => deriv ψ.val (t / ℓ.val)) 1 :=
    periodic_div_scale (deriv_periodic_of ψ.property.1)
  have hg : Function.Periodic (fun t => -(a * deriv ψ.val (t / ℓ.val))) 1 := fun t => by
    simp only [hp1 t]
  have hgc : Continuous (fun t => -(a * deriv ψ.val (t / ℓ.val))) := by
    have : Continuous (fun t => deriv ψ.val (t / ℓ.val)) := hdc.comp (by fun_prop)
    fun_prop
  rw [hfun]
  refine (integral_gibbs_one P hgc hg).trans ?_
  rw [intervalIntegral.integral_neg, intervalIntegral.integral_const_mul,
    integral_deriv_scale_eq_zero ℓ.property.1 hψ ψ.property.1]
  simp

/-- The operator of one particle is integrable under the Gibbs law. -/
theorem integrable_loopOperatorPotential_one (P : Parameters) (ℓ : Ioc (0 : ℝ) 1) (a : ℝ)
    (ψ : LoopScaleProfile ℓ.val) (hψ : ContDiff ℝ ∞ ψ.val) :
    Integrable (loopOperatorPotential P 1 ℓ a ψ) (gibbsMeasure P 1) := by
  have hdc : Continuous (deriv ψ.val) := hψ.continuous_deriv (by simp)
  have hp1 : Function.Periodic (fun t => deriv ψ.val (t / ℓ.val)) 1 :=
    periodic_div_scale (deriv_periodic_of ψ.property.1)
  have hg : Function.Periodic (fun t => -(a * deriv ψ.val (t / ℓ.val))) 1 := fun t => by
    simp only [hp1 t]
  have hgc : Continuous (fun t => -(a * deriv ψ.val (t / ℓ.val))) := by
    have : Continuous (fun t => deriv ψ.val (t / ℓ.val)) := hdc.comp (by fun_prop)
    fun_prop
  exact (integrable_gibbs_one P hgc hg).congr
    (Eventually.of_forall fun X => (loopOperatorPotential_one P ℓ a ψ hψ X).symm)

/-- The operator of one particle lies in `L²(P)` (Proposition 5.5,
clause 1). -/
theorem memLp_loopOperatorPotential_one (P : Parameters) (ℓ : Ioc (0 : ℝ) 1) (a : ℝ)
    (ψ : LoopScaleProfile ℓ.val) (hψ : ContDiff ℝ ∞ ψ.val) :
    MemLp (loopOperatorPotential P 1 ℓ a ψ) 2 (gibbsMeasure P 1) := by
  have hmeas : AEStronglyMeasurable (loopOperatorPotential P 1 ℓ a ψ) (gibbsMeasure P 1) :=
    (integrable_loopOperatorPotential_one P ℓ a ψ hψ).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  have hdc : Continuous (deriv ψ.val) := hψ.continuous_deriv (by simp)
  have hp1 : Function.Periodic (fun t => deriv ψ.val (t / ℓ.val)) 1 :=
    periodic_div_scale (deriv_periodic_of ψ.property.1)
  have hgc : Continuous (fun t => (a * deriv ψ.val (t / ℓ.val)) ^ 2) := by
    have : Continuous (fun t => deriv ψ.val (t / ℓ.val)) := hdc.comp (by fun_prop)
    fun_prop
  have hgp : Function.Periodic (fun t => (a * deriv ψ.val (t / ℓ.val)) ^ 2) 1 := fun t => by
    simp only [hp1 t]
  refine (integrable_gibbs_one P hgc hgp).congr (Eventually.of_forall fun X => ?_)
  simp only [loopOperatorPotential_one P ℓ a ψ hψ X, Real.norm_eq_abs, sq_abs]
  ring

/-- The Bochner identity for one particle (Proposition 5.5, clause 3):
`Var(𝓛Φ) = a² E[β Ψ·∇²H Ψ + ‖DΨ‖²]`, here with `∇²H = 0`. -/
theorem variance_loopOperatorPotential_one (P : Parameters) (ℓ : Ioc (0 : ℝ) 1) (a : ℝ)
    (ψ : LoopScaleProfile ℓ.val) (hψ : ContDiff ℝ ∞ ψ.val) :
    gibbsCov (gibbsMeasure P 1) (loopOperatorPotential P 1 ℓ a ψ)
        (loopOperatorPotential P 1 ℓ a ψ) =
      a ^ 2 * ∫ X : Configuration 1,
        (hessianQuadratic P 1 ℓ ψ X + frobeniusSqDiag ℓ ψ X) ∂gibbsMeasure P 1 := by
  unfold gibbsCov
  rw [integral_loopOperatorPotential_one P ℓ a ψ hψ]
  have hpt : ∀ X : Configuration 1, (loopOperatorPotential P 1 ℓ a ψ X - 0) *
      (loopOperatorPotential P 1 ℓ a ψ X - 0) =
      a ^ 2 * (hessianQuadratic P 1 ℓ ψ X + frobeniusSqDiag ℓ ψ X) := by
    intro X
    simp only [sub_zero]
    rw [loopOperatorPotential_one P ℓ a ψ hψ X, hessianQuadratic_one, frobeniusSqDiag_one]
    ring
  simp_rw [hpt]
  rw [integral_const_mul]

/-- The covariance identity for one particle (Proposition 5.5,
clause 2): `Cov(F, 𝓛Φ) = E[∇F · ∇Φ]` for every smooth `F` on the torus. -/
theorem covariance_loopOperatorPotential_one (P : Parameters) (ℓ : Ioc (0 : ℝ) 1) (a : ℝ)
    (ψ : LoopScaleProfile ℓ.val) (hψ : ContDiff ℝ ∞ ψ.val) (F : (Fin 1 → ℝ) → ℝ)
    (hF : IsTorusSmooth F) :
    gibbsCov (gibbsMeasure P 1) (fun X : Configuration 1 => F X.val)
        (loopOperatorPotential P 1 ℓ a ψ) =
      ∫ X : Configuration 1, gradDotPotential F (loopScalePotential ℓ a ψ 1) X.val
        ∂gibbsMeasure P 1 := by
  -- The restriction of `F` to the diagonal line is one-periodic and smooth.
  set f : ℝ → ℝ := fun t => F (fun _ => t) with hf_def
  have hf : ContDiff ℝ ∞ f := hF.1.comp (contDiff_pi.2 fun _ => contDiff_id)
  have hfp : Function.Periodic f 1 := by
    intro t
    have h := hF.2 0 (fun _ => t)
    simp only [update_fin_one] at h
    exact h
  have hFX : ∀ X : Configuration 1, F X.val = f (X.val 0) := fun X => by
    show F X.val = F (fun _ => X.val 0)
    congr 1
    exact fun_eq_const_of_fin_one X.val
  have hgrad_gen : ∀ x : Fin 1 → ℝ, gradDotPotential F (loopScalePotential ℓ a ψ 1) x =
      deriv f (x 0) * (a * ℓ.val * ψ.val (x 0 / ℓ.val)) := by
    intro x
    unfold gradDotPotential
    rw [Fintype.sum_eq_single (0 : Fin 1) (fun y hy => absurd (Subsingleton.elim y 0) hy),
      partialDeriv_loopScalePotential ℓ a ψ 0 x, partialDeriv_fin_one F x]
  have hgrad : ∀ X : Configuration 1, gradDotPotential F (loopScalePotential ℓ a ψ 1) X.val =
      deriv f (X.val 0) * (a * ℓ.val * ψ.val (X.val 0 / ℓ.val)) := fun X => hgrad_gen X.val
  -- Continuity and periodicity of the one-period integrands.
  have hfc : Continuous f := hf.continuous
  have hdf : Continuous (deriv f) := hf.continuous_deriv (by simp)
  have hdfp : Function.Periodic (deriv f) 1 := deriv_periodic_of hfp
  have hdψ : Continuous (deriv ψ.val) := hψ.continuous_deriv (by simp)
  have hpsi : Function.Periodic (fun t => ψ.val (t / ℓ.val)) 1 :=
    periodic_div_scale ψ.property.1
  have hdpsi : Function.Periodic (fun t => deriv ψ.val (t / ℓ.val)) 1 :=
    periodic_div_scale (deriv_periodic_of ψ.property.1)
  have hc_dψ : Continuous (fun t => deriv ψ.val (t / ℓ.val)) := hdψ.comp (by fun_prop)
  have hc_ψ : Continuous (fun t => ψ.val (t / ℓ.val)) := hψ.continuous.comp (by fun_prop)
  have hℓ : (0 : ℝ) < ℓ.val := ℓ.property.1
  -- The left side: the centred covariance integrand is `-a f(X₀) ψ'(X₀/ℓ) + a c ψ'(X₀/ℓ)`.
  set c := ∫ Y : Configuration 1, f (Y.val 0) ∂gibbsMeasure P 1 with hc
  have hE : ∫ Y : Configuration 1, F Y.val ∂gibbsMeasure P 1 = c := by
    refine integral_congr_ae (Eventually.of_forall fun Y => hFX Y)
  have hL : ∀ X : Configuration 1,
      (F X.val - ∫ Y : Configuration 1, F Y.val ∂gibbsMeasure P 1) *
        (loopOperatorPotential P 1 ℓ a ψ X -
          ∫ Y : Configuration 1, loopOperatorPotential P 1 ℓ a ψ Y ∂gibbsMeasure P 1) =
      -a * (f (X.val 0) * deriv ψ.val (X.val 0 / ℓ.val)) +
        (a * c) * deriv ψ.val (X.val 0 / ℓ.val) := by
    intro X
    rw [hE, integral_loopOperatorPotential_one P ℓ a ψ hψ, loopOperatorPotential_one P ℓ a ψ hψ X,
      hFX X]
    ring
  have hint1 : Integrable (fun X : Configuration 1 =>
      f (X.val 0) * deriv ψ.val (X.val 0 / ℓ.val)) (gibbsMeasure P 1) :=
    integrable_gibbs_one P (g := fun t => f t * deriv ψ.val (t / ℓ.val)) (hfc.mul hc_dψ)
      (hfp.mul hdpsi)
  have hint2 : Integrable (fun X : Configuration 1 => deriv ψ.val (X.val 0 / ℓ.val))
      (gibbsMeasure P 1) :=
    integrable_gibbs_one P (g := fun t => deriv ψ.val (t / ℓ.val)) hc_dψ hdpsi
  have hmean2 : ∫ X : Configuration 1, deriv ψ.val (X.val 0 / ℓ.val) ∂gibbsMeasure P 1 = 0 := by
    refine (integral_gibbs_one P (g := fun t => deriv ψ.val (t / ℓ.val)) hc_dψ hdpsi).trans ?_
    exact integral_deriv_scale_eq_zero hℓ hψ ψ.property.1
  have hpart1 : ∫ X : Configuration 1, f (X.val 0) * deriv ψ.val (X.val 0 / ℓ.val)
      ∂gibbsMeasure P 1 = ∫ t in (0 : ℝ)..1, f t * deriv ψ.val (t / ℓ.val) :=
    integral_gibbs_one P (g := fun t => f t * deriv ψ.val (t / ℓ.val)) (hfc.mul hc_dψ)
      (hfp.mul hdpsi)
  -- The right side: `∫ f'(X₀) a ℓ ψ(X₀/ℓ)` is an integral over one period.
  have hright : ∫ X : Configuration 1, gradDotPotential F (loopScalePotential ℓ a ψ 1) X.val
      ∂gibbsMeasure P 1 = ∫ t in (0 : ℝ)..1, a * (deriv f t * (ℓ.val * ψ.val (t / ℓ.val))) := by
    have hperR : Function.Periodic (fun t => deriv f t * (a * ℓ.val * ψ.val (t / ℓ.val))) 1 :=
      fun t => by simp only [hdfp t, hpsi t]
    have hcR : Continuous (fun t => deriv f t * (a * ℓ.val * ψ.val (t / ℓ.val))) :=
      hdf.mul (continuous_const.mul hc_ψ)
    rw [integral_congr_ae (Eventually.of_forall hgrad)]
    rw [integral_gibbs_one P (g := fun t => deriv f t * (a * ℓ.val * ψ.val (t / ℓ.val))) hcR hperR]
    refine intervalIntegral.integral_congr fun t _ => ?_
    ring
  rw [hright]
  unfold gibbsCov
  rw [integral_congr_ae (Eventually.of_forall hL)]
  rw [integral_add (hint1.const_mul (-a)) (hint2.const_mul (a * c)), integral_const_mul,
    integral_const_mul, hmean2, hpart1]
  rw [intervalIntegral.integral_const_mul]
  have hibp := integral_ibp_scale hℓ hf hfp hψ ψ.property.1
  rw [hibp]
  ring

/-- **Clauses 1 to 3 of Proposition 5.5 for one particle.** For `N = 1`, the
operator `𝓛Φ_{ψ,a}` is integrable with mean zero, satisfies the covariance identity against every
smooth function on the torus, and has the variance `a² E[β Ψ·∇²HΨ + ‖DΨ‖²]`. The mean-zero
condition on `ψ` of the paper is not needed for these identities: they involve only derivatives
of `Φ`, and the periodicity of `ψ` suffices. -/
theorem loop_ibp_one (P : Parameters) (ℓ : Ioc (0 : ℝ) 1) (a : ℝ) (ψ : LoopScaleProfile ℓ.val)
    (hψ : ContDiff ℝ ∞ ψ.val) :
    (MemLp (loopOperatorPotential P 1 ℓ a ψ) 2 (gibbsMeasure P 1) ∧
      ∫ X : Configuration 1, loopOperatorPotential P 1 ℓ a ψ X ∂gibbsMeasure P 1 = 0) ∧
    (∀ F : (Fin 1 → ℝ) → ℝ, IsTorusSmooth F →
      gibbsCov (gibbsMeasure P 1) (fun X : Configuration 1 => F X.val)
          (loopOperatorPotential P 1 ℓ a ψ) =
        ∫ X : Configuration 1, gradDotPotential F (loopScalePotential ℓ a ψ 1) X.val
          ∂gibbsMeasure P 1) ∧
    gibbsCov (gibbsMeasure P 1) (loopOperatorPotential P 1 ℓ a ψ)
        (loopOperatorPotential P 1 ℓ a ψ) =
      a ^ 2 * ∫ X : Configuration 1,
        (hessianQuadratic P 1 ℓ ψ X + frobeniusSqDiag ℓ ψ X) ∂gibbsMeasure P 1 :=
  ⟨⟨memLp_loopOperatorPotential_one P ℓ a ψ hψ,
      integral_loopOperatorPotential_one P ℓ a ψ hψ⟩,
    fun F hF => covariance_loopOperatorPotential_one P ℓ a ψ hψ F hF,
    variance_loopOperatorPotential_one P ℓ a ψ hψ⟩

end Riesz1

end
