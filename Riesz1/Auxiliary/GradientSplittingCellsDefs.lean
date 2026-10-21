/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.GradientSplittingKernel
public import Riesz1.Auxiliary.GradientSplittingZDifferences

/-!
# Definitions of the one-cell quadrature integrands

The functions `F_x` and `R_x` on the cells `0 < |v| < N`,
built from the kernel `g = hurwitzKernel s`, the modified kernel `h = gradKernelH s`, and the
divided differences `Z`, `Z_x`, `Z_xy` of `GradientSplittingZDifferences.lean`.

The file proves the claims about `F_x` and `R_x`: the identity `F_x = -N^{-s} ψ'(x/ℓ) h' + R_x` of
the cell part of Lemma 5.7, and the smoothness of `F_x` and `R_x` on the open set of `v` with
`v/N` non-integral. Here `v/N` is non-integral exactly when `v ∉ Nℤ`.
-/

@[expose] public section

open Set Filter Topology
open scoped ContDiff

namespace Riesz1

/-- The integrand `F_x(v) = N^{-s}(Z_x(x, x+v/N) h(v/N) - Z(x, x+v/N) h'(v/N))`. Here `Z`,
`Z_x` are `gradZ`, `gradZx` for the data `ψ` and `ℓ`, and `h` is
`gradKernelH s`. The value at `v ∈ Nℤ` is not meaningful and is never used. -/
noncomputable def gradCellF (s : ℝ) (N : ℕ) (ℓ : ℝ) (ψ : ℝ → ℝ) (x v : ℝ) : ℝ :=
  (N : ℝ) ^ (-s) * (gradZx ψ ℓ x (x + v / N) * gradKernelH s (v / N)
    - gradZ ψ ℓ x (x + v / N) * iteratedDeriv 1 (gradKernelH s) (v / N))

/-- The remainder `R_x(v) = -N^{-s}(v/N)^2 Z_x(x, x+v/N) g''(v/N)`, with
`g = hurwitzKernel s`. The value at `v ∈ Nℤ` is not meaningful and is never used. -/
noncomputable def gradCellR (s : ℝ) (N : ℕ) (ℓ : ℝ) (ψ : ℝ → ℝ) (x v : ℝ) : ℝ :=
  -(N : ℝ) ^ (-s) * (v / N) ^ 2 * gradZx ψ ℓ x (x + v / N) *
    iteratedDeriv 2 (hurwitzKernel s) (v / N)

/-- The open set of `v` with `v/N` non-integral. This is the set on which `F_x` and `R_x` are
smooth. -/
def gradCellSet (N : ℕ) : Set ℝ := {v : ℝ | ((v / (N : ℝ) : ℝ) : UnitAddCircle) ≠ 0}

lemma gradCellSet_isOpen (N : ℕ) : IsOpen (gradCellSet N) :=
  gradSplit_isOpen_nonInt.preimage (continuous_id.div_const (N : ℝ))

/-- A point of `gradCellSet N` has `v / N ≠ 0`, and so `v ≠ 0`. -/
lemma gradCellSet_div_ne_zero {N : ℕ} {v : ℝ} (hv : v ∈ gradCellSet N) : v / (N : ℝ) ≠ 0 := by
  intro h
  apply hv
  simp [h]

/-- The divided difference `Z(x,y)` is the difference quotient `ℓ(ψ(y/ℓ) - ψ(x/ℓ))/(y-x)` for
`y ≠ x`. -/
lemma gradZ_eq_quot {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) {ℓ x y : ℝ} (hℓ : 0 < ℓ) (hxy : y ≠ x) :
    gradZ ψ ℓ x y = ℓ * (ψ (y / ℓ) - ψ (x / ℓ)) / (y - x) := by
  have hne : x / ℓ ≠ y / ℓ := fun h => hxy ((div_left_inj' hℓ.ne').mp h).symm
  rw [gradZ_eq_gradZavg, gradZavg_eq_div hψ hne]
  rw [show y / ℓ - x / ℓ = (y - x) / ℓ by ring, div_div_eq_mul_div]
  ring

/-- The derivative of `Z(x,·)` at `y ≠ x` is `Z_y(x,y) = (ψ'(y/ℓ) - Z(x,y))/(y-x)`. -/
lemma hasDerivAt_gradZ {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) {ℓ x y : ℝ} (hℓ : 0 < ℓ)
    (hxy : y ≠ x) :
    HasDerivAt (fun t => gradZ ψ ℓ x t) (gradZy ψ ℓ x y) y := by
  have hℓ0 : ℓ ≠ 0 := hℓ.ne'
  have hyx : y - x ≠ 0 := sub_ne_zero.mpr hxy
  have hpsi : HasDerivAt (fun t : ℝ => ψ (t / ℓ)) (deriv ψ (y / ℓ) * (1 / ℓ)) y := by
    have h1 : HasDerivAt (fun t : ℝ => t / ℓ) (1 / ℓ) y := (hasDerivAt_id y).div_const ℓ
    exact (hψ.differentiable (by simp) (y / ℓ)).hasDerivAt.comp y h1
  have hnum : HasDerivAt (fun t : ℝ => ℓ * (ψ (t / ℓ) - ψ (x / ℓ)))
      (ℓ * (deriv ψ (y / ℓ) * (1 / ℓ))) y :=
    (hpsi.sub_const (ψ (x / ℓ))).const_mul ℓ
  have hden : HasDerivAt (fun t : ℝ => t - x) 1 y := (hasDerivAt_id y).sub_const x
  have hd := hnum.div hden hyx
  have hD : (ℓ * (deriv ψ (y / ℓ) * (1 / ℓ)) * (y - x) - ℓ * (ψ (y / ℓ) - ψ (x / ℓ)) * 1) /
      (y - x) ^ 2 = gradZy ψ ℓ x y := by
    unfold gradZy
    rw [gradZ_eq_quot hψ hℓ hxy]
    field_simp
  rw [← hD]
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [eventually_ne_nhds hxy] with t ht
  exact gradZ_eq_quot hψ hℓ ht

/-- The derivative of `Z_x(x,·)` at `y ≠ x` is `Z_xy(x,y) = (Z_y - Z_x)/(y-x)`. -/
lemma hasDerivAt_gradZx {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) {ℓ x y : ℝ} (hℓ : 0 < ℓ)
    (hxy : y ≠ x) :
    HasDerivAt (fun t => gradZx ψ ℓ x t) (gradZxy ψ ℓ x y) y := by
  have hyx : y - x ≠ 0 := sub_ne_zero.mpr hxy
  have hnum : HasDerivAt (fun t => gradZ ψ ℓ x t - deriv ψ (x / ℓ)) (gradZy ψ ℓ x y) y :=
    (hasDerivAt_gradZ hψ hℓ hxy).sub_const _
  have hden : HasDerivAt (fun t : ℝ => t - x) 1 y := (hasDerivAt_id y).sub_const x
  have hd := hnum.div hden hyx
  have hD : (gradZy ψ ℓ x y * (y - x) - (gradZ ψ ℓ x y - deriv ψ (x / ℓ)) * 1) / (y - x) ^ 2 =
      gradZxy ψ ℓ x y := by
    unfold gradZxy gradZx
    field_simp
  rw [← hD]
  exact hd

/-- `Z(x,·)` is smooth on `{t ≠ x}`. -/
lemma contDiffOn_gradZ {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) {ℓ x : ℝ} (hℓ : 0 < ℓ) :
    ContDiffOn ℝ ∞ (fun t => gradZ ψ ℓ x t) {t : ℝ | t ≠ x} := by
  have hψ1 : ContDiff ℝ ∞ (fun t : ℝ => ψ (t / ℓ)) := hψ.comp (contDiff_id.div_const ℓ)
  have hd1 : ContDiffOn ℝ ∞ (fun t : ℝ => t - x) {t : ℝ | t ≠ x} :=
    (contDiff_id.sub contDiff_const).contDiffOn
  have hq : ContDiffOn ℝ ∞ (fun t : ℝ => ℓ * (ψ (t / ℓ) - ψ (x / ℓ)) / (t - x))
      {t : ℝ | t ≠ x} :=
    ((contDiff_const.mul (hψ1.sub contDiff_const)).contDiffOn).div hd1
      (fun t ht => sub_ne_zero.mpr ht)
  refine hq.congr ?_
  intro t ht
  exact gradZ_eq_quot hψ hℓ ht

/-- `Z_x(x,·)` is smooth on `{t ≠ x}`. -/
lemma contDiffOn_gradZx {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) {ℓ x : ℝ} (hℓ : 0 < ℓ) :
    ContDiffOn ℝ ∞ (fun t => gradZx ψ ℓ x t) {t : ℝ | t ≠ x} := by
  have hd1 : ContDiffOn ℝ ∞ (fun t : ℝ => t - x) {t : ℝ | t ≠ x} :=
    (contDiff_id.sub contDiff_const).contDiffOn
  have hZx : ContDiffOn ℝ ∞ (fun t : ℝ => (gradZ ψ ℓ x t - deriv ψ (x / ℓ)) / (t - x))
      {t : ℝ | t ≠ x} :=
    ((contDiffOn_gradZ hψ hℓ).sub contDiffOn_const).div hd1
      (fun t ht => sub_ne_zero.mpr ht)
  exact hZx

/-- The modified kernel `h = gradKernelH s` is smooth on the non-integers. -/
lemma contDiffOn_gradKernelH {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    ContDiffOn ℝ ∞ (gradKernelH s) {r : ℝ | (r : UnitAddCircle) ≠ 0} := by
  rw [gradKernelH_eq s]
  exact contDiffOn_id.mul (gradSplit_contDiffOn_iteratedDeriv s hs0 hs1 1)

/-- The derivative `h' = iteratedDeriv 1 h` is smooth on the non-integers. -/
lemma contDiffOn_iteratedDeriv_gradKernelH {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    ContDiffOn ℝ ∞ (iteratedDeriv 1 (gradKernelH s)) {r : ℝ | (r : UnitAddCircle) ≠ 0} := by
  rw [iteratedDeriv_one]
  exact (contDiffOn_gradKernelH hs0 hs1).deriv_of_isOpen gradSplit_isOpen_nonInt (by simp)

/-- The remainder `R_x` is smooth on `gradCellSet N`, that is off the multiples of `N`. -/
lemma contDiffOn_gradCellR {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) {ℓ : ℝ} (hℓ : 0 < ℓ) (N : ℕ) (x : ℝ) :
    ContDiffOn ℝ ∞ (gradCellR s N ℓ ψ x) (gradCellSet N) := by
  have hmaps : MapsTo (fun v : ℝ => x + v / (N : ℝ)) (gradCellSet N) {t : ℝ | t ≠ x} := by
    intro v hv
    show x + v / (N : ℝ) ≠ x
    intro h
    exact gradCellSet_div_ne_zero hv (by linarith)
  have hZx : ContDiffOn ℝ ∞ (fun v : ℝ => gradZx ψ ℓ x (x + v / (N : ℝ))) (gradCellSet N) :=
    (contDiffOn_gradZx hψ hℓ).comp
      ((contDiff_const.add (contDiff_id.div_const (N : ℝ))).contDiffOn) hmaps
  have hg2 : ContDiffOn ℝ ∞ (fun v : ℝ => iteratedDeriv 2 (hurwitzKernel s) (v / (N : ℝ)))
      (gradCellSet N) :=
    (gradSplit_contDiffOn_iteratedDeriv s hs0 hs1 2).comp
      ((contDiff_id.div_const (N : ℝ)).contDiffOn) (fun _ hv => hv)
  have hp : ContDiffOn ℝ ∞ (fun v : ℝ => (v / (N : ℝ)) ^ 2) (gradCellSet N) :=
    ((contDiff_id.div_const (N : ℝ)).pow 2).contDiffOn
  exact ((contDiffOn_const.mul hp).mul hZx).mul hg2

/-- The integrand `F_x` is smooth on `gradCellSet N`, that is off the multiples of `N`. -/
lemma contDiffOn_gradCellF {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) {ℓ : ℝ} (hℓ : 0 < ℓ) (N : ℕ) (x : ℝ) :
    ContDiffOn ℝ ∞ (gradCellF s N ℓ ψ x) (gradCellSet N) := by
  have hmaps : MapsTo (fun v : ℝ => x + v / (N : ℝ)) (gradCellSet N) {t : ℝ | t ≠ x} := by
    intro v hv
    show x + v / (N : ℝ) ≠ x
    intro h
    exact gradCellSet_div_ne_zero hv (by linarith)
  have hZx : ContDiffOn ℝ ∞ (fun v : ℝ => gradZx ψ ℓ x (x + v / (N : ℝ))) (gradCellSet N) :=
    (contDiffOn_gradZx hψ hℓ).comp
      ((contDiff_const.add (contDiff_id.div_const (N : ℝ))).contDiffOn) hmaps
  have hZ : ContDiffOn ℝ ∞ (fun v : ℝ => gradZ ψ ℓ x (x + v / (N : ℝ))) (gradCellSet N) :=
    (contDiffOn_gradZ hψ hℓ).comp
      ((contDiff_const.add (contDiff_id.div_const (N : ℝ))).contDiffOn) hmaps
  have hh : ContDiffOn ℝ ∞ (fun v : ℝ => gradKernelH s (v / (N : ℝ))) (gradCellSet N) :=
    (contDiffOn_gradKernelH hs0 hs1).comp
      ((contDiff_id.div_const (N : ℝ)).contDiffOn) (fun _ hv => hv)
  have hh' : ContDiffOn ℝ ∞ (fun v : ℝ => iteratedDeriv 1 (gradKernelH s) (v / (N : ℝ)))
      (gradCellSet N) :=
    (contDiffOn_iteratedDeriv_gradKernelH hs0 hs1).comp
      ((contDiff_id.div_const (N : ℝ)).contDiffOn) (fun _ hv => hv)
  exact contDiffOn_const.mul ((hZx.mul hh).sub (hZ.mul hh'))

/-- The identity of the cell part of Lemma 5.7: for `v ∈ gradCellSet N`,
`F_x(v) = -N^{-s} ψ'(x/ℓ) h'(v/N) + R_x(v)`. -/
lemma gradCellF_eq {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {ψ : ℝ → ℝ} {ℓ : ℝ} (N : ℕ) (x : ℝ)
    {v : ℝ} (hv : v ∈ gradCellSet N) :
    gradCellF s N ℓ ψ x v = -(N : ℝ) ^ (-s) * deriv ψ (x / ℓ) *
      iteratedDeriv 1 (gradKernelH s) (v / N) + gradCellR s N ℓ ψ x v := by
  have hr : v / (N : ℝ) ≠ 0 := gradCellSet_div_ne_zero hv
  have hr' : ((v / (N : ℝ) : ℝ) : UnitAddCircle) ≠ 0 := hv
  have hN0 : (N : ℝ) ≠ 0 := fun h => hr (by simp [h])
  have hv0 : v ≠ 0 := fun h => hr (by simp [h])
  -- `Z(x, x+r) = ψ'(x/ℓ) + r Z_x(x, x+r)` with `r = v/N`, since `(x + r) - x = r ≠ 0`.
  have hZ : gradZ ψ ℓ x (x + v / (N : ℝ)) =
      deriv ψ (x / ℓ) + v / (N : ℝ) * gradZx ψ ℓ x (x + v / (N : ℝ)) := by
    unfold gradZx
    rw [show x + v / (N : ℝ) - x = v / (N : ℝ) by ring]
    field_simp
    ring
  -- `h(r) = r g'(r)` and `h'(r) = g'(r) + r g''(r)` at the non-integer `r = v/N`.
  have hh : gradKernelH s (v / (N : ℝ)) = v / (N : ℝ) * iteratedDeriv 1 (hurwitzKernel s) (v / (N : ℝ)) :=
    congrFun (gradKernelH_eq s) (v / (N : ℝ))
  have hh' : iteratedDeriv 1 (gradKernelH s) (v / (N : ℝ)) =
      iteratedDeriv 1 (hurwitzKernel s) (v / (N : ℝ)) +
        v / (N : ℝ) * iteratedDeriv 2 (hurwitzKernel s) (v / (N : ℝ)) :=
    gradSplit_iteratedDeriv_one_gradKernelH s hs0 hs1 hr'
  unfold gradCellF gradCellR
  rw [hZ, hh, hh']
  ring

end Riesz1

end
