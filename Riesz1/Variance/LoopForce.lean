/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.LoopForceEnergy
public import Riesz1.Frozen.Fluctuation

/-!
# Expansion of the microscopic force: the loop equations

Proposition 5.5, the force expansion. Let `0 < s < 1`, `β > 0`,
`N ≥ 1`, and let `ψ` and `ξ` be smooth real one-periodic functions. Let `Φ(x) = ∑ᵢ ∫₀^{xᵢ} ψ`
and `F = Fluct_N[ξ]`. Pointwise on the open set where no two lifted coordinates differ by an
integer, where the energy is smooth, the following hold.

* The first display: `∇H_N · ∇Φ = C_ψ - 2 N^(1-s) ∫(g_s' * ψ) dFluct_N + Loop_1[ψ]`, with
  `C_ψ = 0`.
* The second display: `β ∇H_N · ∇Φ - ΔΦ - F = β C_ψ + ∫(-2βN^(1-s) g_s' * ψ - ξ) dFluct_N
  - Fluct_N[ψ'] + β Loop_1[ψ]`.

Here `g_s' * ψ` is the symmetric principal value `pvConv s ψ`. The operator
`L` on the smooth function `Φ` is written out as `β ∇H_N · ∇Φ - ΔΦ`,
with `H = βH_N`.

The loop functional `Loop_1[ψ]` is the ℓ = 1 case of the loop functional. It is written out
in the expansion of the double integral against `Fluct_N ⊗ Fluct_N` over the off-diagonal set:
the particle-particle sum, the two particle-background integrals and the background-background
integral, as in its definition. The integral `∫ f dFluct_N` is `Σᵢ f(xᵢ) - N ∫₀¹ f`.

The identities hold on lifts for any smooth periodic `ψ`. The mean-zero hypothesis of the
paper is recorded in the statement, and it is what makes `Φ` one-periodic (so that it
descends to the torus), but it is not used in the proof.
-/

public section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace Riesz1

/-- The integral of `f` against the fluctuation measure of a configuration with lift `x`:
`∫ f dFluct_N = ∑ᵢ f(xᵢ) - N ∫₀¹ f`. -/
noncomputable def fluctIntegral (f : ℝ → ℝ) (N : ℕ) (x : Fin N → ℝ) : ℝ :=
  ∑ i : Fin N, f (x i) - (N : ℝ) * ∫ u in (0 : ℝ)..1, f u

/-- The Laplacian `Δ F = ∑ₖ ∂ₖ² F` in the lifted coordinates. -/
noncomputable def laplacian {N : ℕ} (F : (Fin N → ℝ) → ℝ) (x : Fin N → ℝ) : ℝ :=
  ∑ k : Fin N, partialDeriv (fun y => partialDeriv F k y) k x

/-- The loop kernel `(ψ(a) - ψ(b)) g_s'(a - b)`. -/
noncomputable def loopKernel (s : ℝ) (ψ : ℝ → ℝ) (a b : ℝ) : ℝ :=
  (ψ a - ψ b) * deriv (hurwitzKernel s) (a - b)

/-- The loop functional `Loop_1[ψ](X)` at `ℓ = 1`. The double integral
against `Fluct_N ⊗ Fluct_N` over `x ≠ y` is expanded as in the definition: the off-diagonal
particle-particle sum, the two particle-background integrals with the factor `N`, and the
background-background integral with the factor `N²`. -/
noncomputable def loopFunctional (s : ℝ) (N : ℕ) (ψ : ℝ → ℝ) (x : Fin N → ℝ) : ℝ :=
  (N : ℝ) ^ (-s) * ((∑ i : Fin N, ∑ j : Fin N,
      (if j = i then 0 else loopKernel s ψ (x i) (x j)))
    - (N : ℝ) * (∑ i : Fin N, ∫ y in (0 : ℝ)..1, loopKernel s ψ (x i) y)
    - (N : ℝ) * (∑ j : Fin N, ∫ u in (0 : ℝ)..1, loopKernel s ψ u (x j))
    + (N : ℝ) ^ 2 * ∫ u in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, loopKernel s ψ u v)

/-- The background-background constant `C_ψ = N^(2-s) ∬ (ψ(x) - ψ(y)) g_s'(x - y) dx dy` of
Proposition 5.5. -/
noncomputable def cPsi (s : ℝ) (N : ℕ) (ψ : ℝ → ℝ) : ℝ :=
  (N : ℝ) ^ (2 - s) * ∫ u in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, loopKernel s ψ u v

/-- The gradient inner product `∇H_N · ∇Φ` at a lift `x`, in the lifted coordinates. -/
noncomputable def gradDot (s : RieszExponent) (N : ℕ) (ψ : ℝ → ℝ) (x : Fin N → ℝ) : ℝ :=
  ∑ k : Fin N, partialDeriv (energyLift s N) k x * partialDeriv (fieldPotential ψ N) k x

/-- The fluctuation integral of the principal value equals the sum of its values at the points,
since its mean vanishes. -/
lemma fluctIntegral_pvConv {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hψp : Function.Periodic ψ 1) (N : ℕ) (x : Fin N → ℝ) :
    fluctIntegral (pvConv s ψ) N x = ∑ i : Fin N, pvConv s ψ (x i) := by
  unfold fluctIntegral
  rw [integral_pvConv_eq_zero hs0 hs1 hψ hψp, mul_zero, sub_zero]

/-- The Laplacian of the field potential is the fluctuation of `ψ'`, since `ψ'` has zero mean. -/
lemma laplacian_fieldPotential {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hψp : Function.Periodic ψ 1) (N : ℕ) (x : Fin N → ℝ) :
    laplacian (fieldPotential ψ N) x = fluctIntegral (deriv ψ) N x := by
  have hint : ∫ u in (0 : ℝ)..1, deriv ψ u = 0 := by
    rw [intervalIntegral.integral_deriv_eq_sub (fun u _ => (hψ.differentiable (by simp)) u)
      ((hψ.continuous_deriv (by simp)).intervalIntegrable 0 1)]
    have h := hψp 0
    simp only [zero_add] at h
    rw [h, sub_self]
  unfold laplacian fluctIntegral
  rw [hint, mul_zero, sub_zero]
  exact Finset.sum_congr rfl fun k _ =>
    partialDeriv_partialDeriv_fieldPotential hψ.continuous x k

/-- `∫ (c f - g) dFluct_N = c ∫ f dFluct_N - ∫ g dFluct_N` for interval integrable `f` and `g`. -/
lemma fluctIntegral_lin {f g : ℝ → ℝ} (c : ℝ) (hf : IntervalIntegrable f volume 0 1)
    (hg : IntervalIntegrable g volume 0 1) (N : ℕ) (x : Fin N → ℝ) :
    fluctIntegral (fun u => c * f u - g u) N x
      = c * fluctIntegral f N x - fluctIntegral g N x := by
  have e1 : ∫ u in (0 : ℝ)..1, c * f u = c * ∫ u in (0 : ℝ)..1, f u :=
    intervalIntegral.integral_const_mul _ _
  have e2 : ∫ u in (0 : ℝ)..1, (c * f u - g u)
      = (∫ u in (0 : ℝ)..1, c * f u) - ∫ u in (0 : ℝ)..1, g u :=
    intervalIntegral.integral_sub (hf.const_mul c) hg
  unfold fluctIntegral
  rw [e2, e1]
  simp only [Finset.sum_sub_distrib, mul_sub, Finset.mul_sum]
  ring

/-- The gradient inner product in terms of the loop functional: `∇H · ∇Φ = Loop_1 - 2 N^(1-s)
∑ᵢ g_s' * ψ(xᵢ)`, where the background-background term is zero. -/
lemma gradDot_eq_loop (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) {N : ℕ} (hN : 0 < N) {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hψp : Function.Periodic ψ 1) (x : Fin N → ℝ)
    (hx : ∀ i j : Fin N, i ≠ j → ((x i - x j : ℝ) : UnitAddCircle) ≠ 0) :
    gradDot ⟨s, hs0, hs1⟩ N ψ x
      = loopFunctional s N ψ x - 2 * (N : ℝ) ^ (1 - s) * ∑ i : Fin N, pvConv s ψ (x i) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hpow : (N : ℝ) ^ (1 - s) = (N : ℝ) * (N : ℝ) ^ (-s) := by
    rw [show 1 - s = 1 + -s by ring, Real.rpow_add hNpos, Real.rpow_one]
  -- The gradient as the particle-particle sum, in the product form of the kernel.
  have hG : gradDot ⟨s, hs0, hs1⟩ N ψ x = (N : ℝ) ^ (-s) *
      ∑ i : Fin N, ∑ j : Fin N, (if j = i then (0 : ℝ) else
        (ψ (x i) - ψ (x j)) * deriv (hurwitzKernel s) (x i - x j)) :=
    gradDot_energy_fieldPotential hs0 hs1 hψ.continuous x hx
  -- The loop functional, unfolded definitionally into its own sums.
  have hLoopEq : loopFunctional s N ψ x = (N : ℝ) ^ (-s) * ((∑ i : Fin N, ∑ j : Fin N,
      (if j = i then (0 : ℝ) else loopKernel s ψ (x i) (x j)))
    - (N : ℝ) * (∑ i : Fin N, ∫ y in (0 : ℝ)..1, loopKernel s ψ (x i) y)
    - (N : ℝ) * (∑ j : Fin N, ∫ u in (0 : ℝ)..1, loopKernel s ψ u (x j))
    + (N : ℝ) ^ 2 * ∫ u in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, loopKernel s ψ u v) := rfl
  have hA : ∑ i : Fin N, ∫ y in (0 : ℝ)..1, loopKernel s ψ (x i) y
      = -∑ i : Fin N, pvConv s ψ (x i) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => integral_kernel_mul_sub_right hs0 hs1 hψ hψp (x i)
  have hB : ∑ j : Fin N, ∫ u in (0 : ℝ)..1, loopKernel s ψ u (x j)
      = -∑ j : Fin N, pvConv s ψ (x j) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ => integral_kernel_mul_sub_left hs0 hs1 hψ hψp (x j)
  have hD : ∫ u in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, loopKernel s ψ u v = 0 :=
    integral_integral_kernel_eq_zero hs0 hs1 hψ hψp
  -- Generic algebra. The sums of the goal are matched by unification with `exact`, which checks
  -- definitional equality (the loop kernel unfolds there).
  have key : ∀ S T1 T2 T3 P : ℝ, T1 = -P → T2 = -P → T3 = 0 →
      (N : ℝ) ^ (-s) * S = (N : ℝ) ^ (-s) * (S - (N : ℝ) * T1 - (N : ℝ) * T2
        + (N : ℝ) ^ 2 * T3) - 2 * ((N : ℝ) * (N : ℝ) ^ (-s)) * P := by
    intro S T1 T2 T3 P h1 h2 h3
    rw [h1, h2, h3]
    ring
  rw [hG, hLoopEq, hpow]
  exact key _ _ _ _ _ hA hB hD

/-- The first display of Proposition 5.5, with the background constant
`C_ψ = 0`, and the second display, for smooth one-periodic `ψ` and `ξ`, at a lift `x` of `N ≥ 1`
points with no two coordinates differing by an integer. -/
theorem loop_equations_force (s : RieszExponent) (β : ℝ) (_hβ : 0 < β) (N : ℕ) (hN : 0 < N)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hψp : Function.Periodic ψ 1)
    (_hψ0 : ∫ u in (0 : ℝ)..1, ψ u = 0)
    (ξ : ℝ → ℝ) (hξ : ContDiff ℝ ∞ ξ) (_hξp : Function.Periodic ξ 1)
    (x : Fin N → ℝ) (hx : ∀ i j : Fin N, i ≠ j → ((x i - x j : ℝ) : UnitAddCircle) ≠ 0) :
    cPsi s.val N ψ = 0 ∧
    gradDot s N ψ x = cPsi s.val N ψ - 2 * (N : ℝ) ^ (1 - s.val)
        * fluctIntegral (pvConv s.val ψ) N x + loopFunctional s.val N ψ x ∧
    β * gradDot s N ψ x - laplacian (fieldPotential ψ N) x - fluctIntegral ξ N x
      = β * cPsi s.val N ψ
        + fluctIntegral (fun u => -(2 * β * (N : ℝ) ^ (1 - s.val)) * pvConv s.val ψ u - ξ u) N x
        - fluctIntegral (deriv ψ) N x + β * loopFunctional s.val N ψ x := by
  obtain ⟨s, hs0, hs1⟩ := s
  dsimp only
  have hC0 : cPsi s N ψ = 0 := by
    unfold cPsi loopKernel
    rw [integral_integral_kernel_eq_zero hs0 hs1 hψ hψp, mul_zero]
  have hgrad := gradDot_eq_loop s hs0 hs1 hN hψ hψp x hx
  have hF := fluctIntegral_pvConv hs0 hs1 hψ hψp N x
  have hlap := laplacian_fieldPotential hψ hψp N x
  have hlin := fluctIntegral_lin (-(2 * β * (N : ℝ) ^ (1 - s)))
    (intervalIntegrable_pvConv hs0 hs1 hψ hψp) (hξ.continuous.intervalIntegrable 0 1) N x
  refine ⟨hC0, ?_, ?_⟩
  · rw [hgrad, hF, hC0]
    ring
  · rw [hC0, hlin, hlap, hgrad, hF]
    ring

/-- A continuous one-periodic function has a continuous lift to the circle `UnitAddCircle`. -/
lemma continuous_lift_periodic {f : ℝ → ℝ} (hf : Continuous f) (hfp : Function.Periodic f 1) :
    Continuous (hfp.lift : UnitAddCircle → ℝ) := by
  unfold Function.Periodic.lift
  exact hf.quotient_liftOn' _

/-- The circle lift of a continuous one-periodic function is integrable. -/
lemma integrable_lift_periodic {f : ℝ → ℝ} (hf : Continuous f) (hfp : Function.Periodic f 1) :
    Integrable (hfp.lift : UnitAddCircle → ℝ) :=
  (continuous_lift_periodic hf hfp).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- The centered statistic `fluctuation` of the circle lift of a
continuous one-periodic `f` is the integral `fluctIntegral f` against `Fluct_N`. -/
lemma fluctuation_eq_fluctIntegral {f : ℝ → ℝ} (hf : Continuous f) (hfp : Function.Periodic f 1)
    {N : ℕ+} (X : Configuration N) :
    fluctuation ⟨(hfp.lift : UnitAddCircle → ℝ), integrable_lift_periodic hf hfp⟩ X
      = fluctIntegral f N X.val := by
  have h1 : ∑ i : Fin (N : ℕ), (hfp.lift : UnitAddCircle → ℝ) (X.val i : UnitAddCircle)
      = ∑ i : Fin (N : ℕ), f (X.val i) :=
    Finset.sum_congr rfl fun i _ => hfp.lift_coe (X.val i)
  have h2 : ∫ x : UnitAddCircle, (hfp.lift : UnitAddCircle → ℝ) x = ∫ u in (0 : ℝ)..1, f u := by
    rw [← AddCircle.intervalIntegral_preimage 1 0]
    simp only [zero_add]
    exact intervalIntegral.integral_congr fun a _ => hfp.lift_coe a
  unfold fluctuation fluctIntegral linearStatistic
  rw [h2]
  exact congrArg₂ (· - ·) h1 rfl

end Riesz1

end
