/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.GradientSplittingWindowDerivative

/-!
# The particle-particle part of the localized loop

The pair term `Z(x_i, x_i + r_ij) h(r_ij)` of `H_γ` equals the kernel `P(a,b) = ℓ(ψ(b/ℓ) - ψ(a/ℓ)) G(b-a)`
(`gradPairKernel`), which is symmetric and invariant under integer shifts of each argument. Its partial
derivatives `P1` (in the first argument) and `P2` (in the second) are the pieces `Z_x h - Z h'` of the
fields `V` and `W`: `P1(a,b) = Z_x(a,b) h(b-a) - Z(a,b) h'(b-a)` (`gradPairP1_eq`).
-/

@[expose] public section

open Set MeasureTheory Filter Topology intervalIntegral
open scoped ContDiff

namespace Riesz1

noncomputable section

/-- The partial derivative of the pair kernel in its first argument. -/
def gradPairP1 (s : ℝ) (ψ : ℝ → ℝ) (ℓ a b : ℝ) : ℝ :=
  -deriv ψ (a / ℓ) * deriv (hurwitzKernel s) (b - a)
    - ℓ * (ψ (b / ℓ) - ψ (a / ℓ)) * deriv (deriv (hurwitzKernel s)) (b - a)

/-- The partial derivative of the pair kernel in its second argument. -/
def gradPairP2 (s : ℝ) (ψ : ℝ → ℝ) (ℓ a b : ℝ) : ℝ :=
  deriv ψ (b / ℓ) * deriv (hurwitzKernel s) (b - a)
    + ℓ * (ψ (b / ℓ) - ψ (a / ℓ)) * deriv (deriv (hurwitzKernel s)) (b - a)

/-- `P1` is the field expression `Z_x h - Z h'`. -/
lemma gradPairP1_eq {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) {ℓ : ℝ} (hℓ : ℓ ≠ 0) {s : ℝ}
    (hs0 : 0 < s) (hs1 : s < 1) (a b : ℝ) (hab : ((b - a : ℝ) : UnitAddCircle) ≠ 0) :
    gradPairP1 s ψ ℓ a b
      = gradZx ψ ℓ a b * gradKernelH s (b - a) - gradZ ψ ℓ a b * deriv (gradKernelH s) (b - a) := by
  unfold gradPairP1
  rw [gradZx_mul_kernelH ψ ℓ s a b, deriv_gradKernelH_eq hs0 hs1 hab,
    iteratedDeriv_two_hurwitzKernel_eq]
  have h := gradZ_mul_sub hψ hℓ a b
  linear_combination (deriv (deriv (hurwitzKernel s)) (b - a)) * h

/-- `P2(a,b) = P1(b,a)`: the second partial is the first partial with the arguments swapped. -/
lemma gradPairP2_eq_swap {ψ : ℝ → ℝ} {ℓ : ℝ} (s : ℝ) (a b : ℝ) :
    gradPairP2 s ψ ℓ a b = gradPairP1 s ψ ℓ b a := by
  have hG2 : deriv (deriv (hurwitzKernel s)) (-(b - a)) = deriv (deriv (hurwitzKernel s)) (b - a) := by
    have hfun : (fun y => deriv (hurwitzKernel s) (-y)) = fun y => -deriv (hurwitzKernel s) y :=
      funext fun y => deriv_hurwitzKernel_neg' s y
    have h1 := deriv_comp_neg (deriv (hurwitzKernel s)) (b - a)
    have h2 : deriv (fun y => -deriv (hurwitzKernel s) y) (b - a)
        = -deriv (deriv (hurwitzKernel s)) (b - a) := deriv.neg
    rw [hfun, h2] at h1
    linarith
  unfold gradPairP1 gradPairP2
  rw [show a - b = -(b - a) by ring, deriv_hurwitzKernel_neg', hG2]
  ring

/-- The derivative of the pair kernel along a line `t ↦ (a + tα, b + tβ)` (off the integers). -/
lemma hasDerivAt_gradPairKernel_line {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) {ℓ : ℝ} (hℓ : ℓ ≠ 0)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (a b α β : ℝ)
    (hab : ((b - a : ℝ) : UnitAddCircle) ≠ 0) :
    HasDerivAt (fun t : ℝ => gradPairKernel s ψ ℓ (a + t * α) (b + t * β))
      (α * gradPairP1 s ψ ℓ a b + β * gradPairP2 s ψ ℓ a b) 0 := by
  have hψd : ∀ u : ℝ, HasDerivAt ψ (deriv ψ u) u := fun u => ((hψ.differentiable (by simp)) u).hasDerivAt
  have hlin : ∀ c γ : ℝ, HasDerivAt (fun t : ℝ => (c + t * γ) / ℓ) (γ / ℓ) 0 := by
    intro c γ
    have := (((hasDerivAt_id (0 : ℝ)).mul_const γ).const_add c).div_const ℓ
    simpa using this
  have hψa : HasDerivAt (fun t : ℝ => ψ ((a + t * α) / ℓ)) (deriv ψ (a / ℓ) * (α / ℓ)) 0 := by
    have h := (hψd ((a + (0 : ℝ) * α) / ℓ)).comp (0 : ℝ) (hlin a α)
    have e : (a + (0 : ℝ) * α) / ℓ = a / ℓ := by ring_nf
    rw [e] at h
    exact h
  have hψb : HasDerivAt (fun t : ℝ => ψ ((b + t * β) / ℓ)) (deriv ψ (b / ℓ) * (β / ℓ)) 0 := by
    have h := (hψd ((b + (0 : ℝ) * β) / ℓ)).comp (0 : ℝ) (hlin b β)
    have e : (b + (0 : ℝ) * β) / ℓ = b / ℓ := by ring_nf
    rw [e] at h
    exact h
  have hr : HasDerivAt (fun t : ℝ => (b + t * β) - (a + t * α)) (β - α) 0 := by
    have h := (((hasDerivAt_id (0 : ℝ)).mul_const β).const_add b).sub
      (((hasDerivAt_id (0 : ℝ)).mul_const α).const_add a)
    convert h using 1 <;> first | rfl | ring
  have hGd : HasDerivAt (deriv (hurwitzKernel s)) (deriv (deriv (hurwitzKernel s)) (b - a)) (b - a) :=
    (((contDiffAt_deriv_hurwitzKernel hs0 hs1 hab).differentiableAt (by simp))).hasDerivAt
  have hG : HasDerivAt (fun t : ℝ => deriv (hurwitzKernel s) ((b + t * β) - (a + t * α)))
      (deriv (deriv (hurwitzKernel s)) (b - a) * (β - α)) 0 := by
    have hGd' : HasDerivAt (deriv (hurwitzKernel s))
        (deriv (deriv (hurwitzKernel s)) (b - a)) ((b + (0 : ℝ) * β) - (a + (0 : ℝ) * α)) := by
      have e : (b + (0 : ℝ) * β) - (a + (0 : ℝ) * α) = b - a := by ring
      rw [e]
      exact hGd
    exact hGd'.comp (0 : ℝ) hr
  have h := ((hψb.sub hψa).const_mul ℓ).mul hG
  refine h.congr_deriv ?_
  unfold gradPairP1 gradPairP2
  simp only [zero_mul, add_zero, Pi.sub_apply, add_zero]
  field_simp
  ring

/-- `deriv (deriv g)` is one-periodic. -/
lemma deriv_deriv_hurwitzKernel_periodic (s : ℝ) :
    Function.Periodic (deriv (deriv (hurwitzKernel s))) 1 := by
  intro x
  have hfun : (fun y => deriv (hurwitzKernel s) (y + 1)) = deriv (hurwitzKernel s) :=
    funext fun y => deriv_hurwitzKernel_add_one' s y
  have h := deriv_comp_add_const (f := deriv (hurwitzKernel s)) (a := 1) x
  rw [hfun] at h
  exact h.symm

/-- The pair kernel is invariant under integer shifts of its second argument. -/
lemma gradPairKernel_add_int_right {ψ : ℝ → ℝ} {ℓ : ℝ} (hp : Function.Periodic ψ (1 / ℓ)) (s : ℝ)
    (a b : ℝ) (n : ℤ) : gradPairKernel s ψ ℓ a (b + n) = gradPairKernel s ψ ℓ a b := by
  have h : Function.Periodic (fun y => gradPairKernel s ψ ℓ a y) 1 :=
    fun y => gradPairKernel_add_one_right hp s a y
  have h2 := h.int_mul n b
  simp only [mul_one] at h2
  exact h2

/-- `P1` is invariant under integer shifts of its second argument. -/
lemma gradPairP1_add_int_right {ψ : ℝ → ℝ} {ℓ : ℝ} (hp : Function.Periodic ψ (1 / ℓ)) (s : ℝ)
    (a b : ℝ) (n : ℤ) : gradPairP1 s ψ ℓ a (b + n) = gradPairP1 s ψ ℓ a b := by
  unfold gradPairP1
  have hG : deriv (hurwitzKernel s) (b + n - a) = deriv (hurwitzKernel s) (b - a) := by
    have h := (deriv_hurwitzKernel_periodic' s).int_mul n (b - a)
    rw [show (b - a) + (n : ℝ) * 1 = b + n - a by ring] at h
    exact h
  have hG2 : deriv (deriv (hurwitzKernel s)) (b + n - a) = deriv (deriv (hurwitzKernel s)) (b - a) := by
    have h := (deriv_deriv_hurwitzKernel_periodic s).int_mul n (b - a)
    rw [show (b - a) + (n : ℝ) * 1 = b + n - a by ring] at h
    exact h
  have hψ : ψ ((b + n) / ℓ) = ψ (b / ℓ) := by
    have h := hp.int_mul n (b / ℓ)
    rw [show (b + n) / ℓ = b / ℓ + (n : ℝ) * (1 / ℓ) by field_simp] 
    simpa using h
  rw [hG, hG2, hψ]

end

end Riesz1
