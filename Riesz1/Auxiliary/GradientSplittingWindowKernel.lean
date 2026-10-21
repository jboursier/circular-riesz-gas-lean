/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.GradientSplittingWindowDefs
public import Riesz1.Variance.LoopForceKernel

/-!
# Kernel identities for the localized loop

Algebra of the divided difference `Z` against the kernel `h(r) = r g'(r)`,
with `g = hurwitzKernel s` and `G = deriv g`. Writing `p(y) = ψ(y/ℓ)`, the fundamental theorem of
calculus gives `Z(x,y)(y - x) = ℓ(p(y) - p(x))` (`gradZ_mul_sub`). From this:

* `Z(x,y) h(y - x) = ℓ(p(y) - p(x)) G(y - x)` for all `x, y` (`gradZ_mul_kernelH`).
* `Z_x(x,y) h(y - x) = (Z(x,y) - ψ'(x/ℓ)) G(y - x)` for all `x, y` (`gradZx_mul_kernelH`).
* `h'(r) = G(r) + r g''(r)` off the integers (`deriv_gradKernelH_eq`).

Also: the pair kernel `F(a,b) = ℓ(ψ(b/ℓ) - ψ(a/ℓ)) G(b - a)` is symmetric and invariant under integer
shifts of either argument (`gradPairKernel_symm`, `gradPairKernel_add_one_left`,
`gradPairKernel_add_one_right`). It is smooth off the integers (`contDiffAt_gradPairKernel`).
-/

@[expose] public section

open Set MeasureTheory Filter Topology intervalIntegral
open scoped ContDiff

namespace Riesz1

noncomputable section

/-- The fundamental theorem of calculus in the segment variable: `Z(x,y)(y - x) = ℓ(ψ(y/ℓ) - ψ(x/ℓ))`
for every `x, y` (the identity behind `Z h = ℓ(ψ(y/ℓ) - ψ(x/ℓ)) g'`). -/
lemma gradZ_mul_sub {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) {ℓ : ℝ} (hℓ : ℓ ≠ 0) (x y : ℝ) :
    gradZ ψ ℓ x y * (y - x) = ℓ * (ψ (y / ℓ) - ψ (x / ℓ)) := by
  have hderiv : ∀ θ ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun θ : ℝ => ℓ * ψ ((x + θ * (y - x)) / ℓ))
      (deriv ψ ((x + θ * (y - x)) / ℓ) * (y - x)) θ := by
    intro θ _
    have h1 : HasDerivAt (fun θ : ℝ => (x + θ * (y - x)) / ℓ) ((y - x) / ℓ) θ := by
      have := (((hasDerivAt_id θ).mul_const (y - x)).const_add x).div_const ℓ
      simpa using this
    have h2 : HasDerivAt ψ (deriv ψ ((x + θ * (y - x)) / ℓ)) ((x + θ * (y - x)) / ℓ) :=
      ((hψ.differentiable (by simp)) _).hasDerivAt
    have h3 := (h2.comp θ h1).const_mul ℓ
    have e : ℓ * (deriv ψ ((x + θ * (y - x)) / ℓ) * ((y - x) / ℓ))
        = deriv ψ ((x + θ * (y - x)) / ℓ) * (y - x) := by
      field_simp
    rw [e] at h3
    exact h3
  have hcont : Continuous (fun θ : ℝ => deriv ψ ((x + θ * (y - x)) / ℓ) * (y - x)) :=
    ((hψ.continuous_deriv (by simp)).comp (by fun_prop)).mul continuous_const
  have key := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ hθ => hderiv θ hθ)
    (hcont.intervalIntegrable 0 1)
  have e1 : (x + 1 * (y - x)) / ℓ = y / ℓ := by ring_nf
  have e0 : (x + 0 * (y - x)) / ℓ = x / ℓ := by ring_nf
  rw [e1, e0] at key
  unfold gradZ
  rw [← intervalIntegral.integral_mul_const, key]
  ring

/-- On the diagonal the divided difference is the derivative: `Z(x,x) = ψ'(x/ℓ)`. -/
lemma gradZ_self (ψ : ℝ → ℝ) (ℓ x : ℝ) : gradZ ψ ℓ x x = deriv ψ (x / ℓ) := by
  unfold gradZ
  simp

/-- The modified kernel is `h(r) = r G(r)` with `G = deriv (hurwitzKernel s)`. -/
lemma gradKernelH_eq_mul (s r : ℝ) : gradKernelH s r = r * deriv (hurwitzKernel s) r := rfl

/-- The product identity `Z(x,y) h(y - x) = ℓ(ψ(y/ℓ) - ψ(x/ℓ)) G(y - x)` for every `x, y`. -/
lemma gradZ_mul_kernelH {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) {ℓ : ℝ} (hℓ : ℓ ≠ 0) (s x y : ℝ) :
    gradZ ψ ℓ x y * gradKernelH s (y - x)
      = ℓ * (ψ (y / ℓ) - ψ (x / ℓ)) * deriv (hurwitzKernel s) (y - x) := by
  rw [gradKernelH_eq_mul, ← gradZ_mul_sub hψ hℓ x y]
  ring

/-- The product identity `Z_x(x,y) h(y - x) = (Z(x,y) - ψ'(x/ℓ)) G(y - x)` for every `x, y`. On the
diagonal both sides vanish. -/
lemma gradZx_mul_kernelH (ψ : ℝ → ℝ) (ℓ : ℝ) (s x y : ℝ) :
    gradZx ψ ℓ x y * gradKernelH s (y - x)
      = (gradZ ψ ℓ x y - deriv ψ (x / ℓ)) * deriv (hurwitzKernel s) (y - x) := by
  by_cases hxy : y - x = 0
  · have hyx : y = x := sub_eq_zero.mp hxy
    subst hyx
    simp [gradZx, gradKernelH_eq_mul, gradZ_self]
  · unfold gradZx
    rw [gradKernelH_eq_mul]
    field_simp

/-- For `r` off the integers, `h'(r) = G(r) + r g''(r)` with `g'' = iteratedDeriv 2 g`. -/
lemma deriv_gradKernelH_eq {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {r : ℝ} (hr : (r : UnitAddCircle) ≠ 0) :
    deriv (gradKernelH s) r
      = deriv (hurwitzKernel s) r + r * iteratedDeriv 2 (hurwitzKernel s) r := by
  have h := gradSplit_iteratedDeriv_one_gradKernelH s hs0 hs1 hr
  simp only [iteratedDeriv_one] at h
  exact h

/-- The derivative `G = deriv g` is smooth off the integers. -/
lemma contDiffAt_deriv_hurwitzKernel {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {r : ℝ}
    (hr : (r : UnitAddCircle) ≠ 0) : ContDiffAt ℝ ∞ (deriv (hurwitzKernel s)) r := by
  have h := (gradSplit_contDiffOn_iteratedDeriv s hs0 hs1 1).contDiffAt
    (gradSplit_isOpen_nonInt.mem_nhds hr)
  simpa only [iteratedDeriv_one] using h

/-- The second derivative `g'' = iteratedDeriv 2 g` is smooth off the integers. -/
lemma contDiffAt_iteratedDeriv_two_hurwitzKernel {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {r : ℝ}
    (hr : (r : UnitAddCircle) ≠ 0) : ContDiffAt ℝ ∞ (iteratedDeriv 2 (hurwitzKernel s)) r :=
  (gradSplit_contDiffOn_iteratedDeriv s hs0 hs1 2).contDiffAt (gradSplit_isOpen_nonInt.mem_nhds hr)

/-- The pair kernel `F(a,b) = ℓ(ψ(b/ℓ) - ψ(a/ℓ)) G(b - a)` of the particle-particle sum. By
`gradZ_mul_kernelH`, `F(a,b) = Z(a,b) h(b - a)` for all `a, b`. -/
def gradPairKernel (s : ℝ) (ψ : ℝ → ℝ) (ℓ a b : ℝ) : ℝ :=
  ℓ * (ψ (b / ℓ) - ψ (a / ℓ)) * deriv (hurwitzKernel s) (b - a)

/-- The pair kernel is symmetric in its two arguments (`G` is odd). -/
lemma gradPairKernel_symm (s : ℝ) (ψ : ℝ → ℝ) (ℓ a b : ℝ) :
    gradPairKernel s ψ ℓ a b = gradPairKernel s ψ ℓ b a := by
  unfold gradPairKernel
  rw [show a - b = -(b - a) by ring, deriv_hurwitzKernel_neg']
  ring

/-- Invariance of the pair kernel under `a ↦ a + 1`, for a `1/ℓ`-periodic `ψ`. -/
lemma gradPairKernel_add_one_left {ψ : ℝ → ℝ} {ℓ : ℝ} (hp : Function.Periodic ψ (1 / ℓ)) (s : ℝ)
    (a b : ℝ) : gradPairKernel s ψ ℓ (a + 1) b = gradPairKernel s ψ ℓ a b := by
  unfold gradPairKernel
  have h1 : ψ ((a + 1) / ℓ) = ψ (a / ℓ) := by
    rw [show (a + 1) / ℓ = a / ℓ + 1 / ℓ by ring]
    exact hp _
  have h2 : b - (a + 1) = (b - a) - 1 := by ring
  rw [h1, h2, ← deriv_hurwitzKernel_add_one' s (b - a - 1), sub_add_cancel]

/-- Invariance of the pair kernel under `b ↦ b + 1`, for a `1/ℓ`-periodic `ψ`. -/
lemma gradPairKernel_add_one_right {ψ : ℝ → ℝ} {ℓ : ℝ} (hp : Function.Periodic ψ (1 / ℓ)) (s : ℝ)
    (a b : ℝ) : gradPairKernel s ψ ℓ a (b + 1) = gradPairKernel s ψ ℓ a b := by
  unfold gradPairKernel
  have h1 : ψ ((b + 1) / ℓ) = ψ (b / ℓ) := by
    rw [show (b + 1) / ℓ = b / ℓ + 1 / ℓ by ring]
    exact hp _
  have h2 : b + 1 - a = (b - a) + 1 := by ring
  rw [h1, h2, deriv_hurwitzKernel_add_one']

/-- The pair kernel is smooth at every pair with `b - a` off the integers. -/
lemma contDiffAt_gradPairKernel {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) {ℓ : ℝ} (a b : ℝ) (hab : ((b - a : ℝ) : UnitAddCircle) ≠ 0) :
    ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => gradPairKernel s ψ ℓ p.1 p.2) (a, b) := by
  unfold gradPairKernel
  have hψa : ∀ u : ℝ, ContDiffAt ℝ ∞ ψ u := fun u => hψ.contDiffAt
  have h1 : ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => ψ (p.2 / ℓ)) (a, b) :=
    (hψa _).comp (a, b) (contDiffAt_snd.div_const ℓ)
  have h2 : ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => ψ (p.1 / ℓ)) (a, b) :=
    (hψa _).comp (a, b) (contDiffAt_fst.div_const ℓ)
  have h3 : ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => deriv (hurwitzKernel s) (p.2 - p.1)) (a, b) :=
    (contDiffAt_deriv_hurwitzKernel hs0 hs1 hab).comp (a, b)
      (contDiffAt_snd.sub contDiffAt_fst)
  exact ((contDiffAt_const.mul (h1.sub h2))).mul h3

end

end Riesz1
