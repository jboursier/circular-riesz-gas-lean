/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.VectorEnergyTests
public import Riesz1.HelfferSjostrand.SettingQuotient

/-!
# The vector quadratic form

For `u, h ∈ 𝒟_N^N`,
`q_μ(u, h) = ∫ (∑_i ∇u_i · ∇h_i + u · ∇²H h) dμ`.
Here `μ` is the Gibbs probability on the quotient, and the integrand is evaluated at the
fundamental lift of each configuration.

The Hessian term is the pair energy inner product: for every chamber point `y`,
`u · ∇²H(y) h = ⟪E_y(u), E_y(h)⟫`, where `E_y(v) = (√(2 χ_ij''(y_j - y_i)) (v_j - v_i))_{i<j}`.
This identifies the form with a Dirichlet form on the completion of `𝒟_N^N` in
`VectorEnergySobolev`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace Riesz1

/-- The `N`-tuples of test functions `𝒟_N^N`. -/
abbrev HsVectorTest (N : ℕ+) := Fin (N : ℕ) → hsTestSubmodule N

/-- The vector `(u_1(x), …, u_N(x))` of a test tuple at a point of the lift space. -/
def hsTestVector {N : ℕ+} (u : HsVectorTest N) (x : HsEuclidean N) : HsEuclidean N :=
  WithLp.toLp 2 (fun i => (u i : HsEuclidean N → ℝ) x)

/-- The pointwise integrand at a lift point `x`:
`∑_i ∇u_i · ∇h_i + u · ∇²H h`. -/
def vectorFormIntegrand {N : ℕ+} {c : ℝ} (χ : HsPairPotentials N c) (u h : HsVectorTest N)
    (x : HsEuclidean N) : ℝ :=
  ∑ i, inner ℝ (gradient (u i : HsEuclidean N → ℝ) x) (gradient (h i : HsEuclidean N → ℝ) x) +
    fderiv ℝ (fderiv ℝ (hsPairExpression χ)) x (hsTestVector u x) (hsTestVector h x)

/-- The vector quadratic form `q_μ(u, h)`. The measure `μ` is the Gibbs
probability of an admissible pair Hamiltonian, and the integrand is read at the fundamental lift
of each configuration. -/
def vectorForm {N : ℕ+} {c : ℝ} (χ : HsPairPotentials N c) (μ : Measure (HsConfiguration N))
    (u h : HsVectorTest N) : ℝ :=
  ∫ y, vectorFormIntegrand χ u h (hsLiftPoint N y) ∂μ

/-- Summing over the index set `i < j` of the pair energy is the double sum over the
ordered pairs of `Fin N` with `i < j`. -/
theorem sum_hsPairIndex {N : ℕ} (g : Fin N → Fin N → ℝ) :
    ∑ p : {p : Fin N × Fin N // p.1 < p.2}, g p.1.1 p.1.2 =
      ∑ i, ∑ j ∈ Finset.univ.filter (i < ·), g i j := by
  rw [← Finset.sum_subtype (Finset.univ.filter fun q : Fin N × Fin N => q.1 < q.2) (by simp)
    (fun q => g q.1 q.2)]
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_filter]

/-- The inner product of two pair Hessian energies at a chamber point is the Hessian form. -/
theorem inner_hsHessianEnergy {N : ℕ+} {c : ℝ} (χ : HsPairPotentials N c) (hc : 0 < c)
    {x : HsEuclidean N} (hx : x ∈ hsChamber N) (v w : HsEuclidean N) :
    inner ℝ (hsHessianEnergy χ x v) (hsHessianEnergy χ x w) =
      fderiv ℝ (fderiv ℝ (hsPairExpression χ)) x v w := by
  have hnn : ∀ p : HsPairIndex N,
      0 ≤ 2 * deriv (deriv (χ.potential p.1.1 p.1.2)) (x p.1.2 - x p.1.1) := by
    intro p
    have hcurv := χ.curvature p.1.1 p.1.2 p.2 (x p.1.2 - x p.1.1)
      (hsChamber_separation_mem hx p.2)
    linarith [hc.le]
  have hsq : ∀ p : HsPairIndex N, hsEnergyWeight χ p x * hsEnergyWeight χ p x =
      2 * deriv (deriv (χ.potential p.1.1 p.1.2)) (x p.1.2 - x p.1.1) := fun p => by
    unfold hsEnergyWeight
    exact Real.mul_self_sqrt (hnn p)
  have key : ∀ p : HsPairIndex N, inner ℝ (hsHessianEnergy χ x v p) (hsHessianEnergy χ x w p) =
      2 * deriv (deriv (χ.potential p.1.1 p.1.2)) (x p.1.2 - x p.1.1) *
        ((v p.1.2 - v p.1.1) * (w p.1.2 - w p.1.1)) := by
    intro p
    simp only [hsHessianEnergy, PiLp.toLp_apply, RCLike.inner_apply, conj_trivial]
    rw [← hsq p]
    ring
  rw [hessian_hsPairExpression_apply χ hx, PiLp.inner_apply]
  rw [Finset.sum_congr rfl fun p _ => key p,
    sum_hsPairIndex (fun i j => 2 * deriv (deriv (χ.potential i j)) (x j - x i) *
      ((v j - v i) * (w j - w i))), Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

end Riesz1

end
