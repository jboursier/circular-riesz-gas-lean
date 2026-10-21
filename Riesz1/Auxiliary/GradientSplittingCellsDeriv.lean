/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.GradientSplittingCellsDefs

/-!
# Derivative of the remainder of the one-cell quadrature

The derivative bound of the cell part of Lemma 5.7 on `1/2 ≤ |v| ≤ 3N/4`. The file
computes the derivative of `R_x` in `v` on `gradCellSet N`, and proves the bound
`|R_x'(v)| ≤ 4 D D_g C_0 ℓ^{-1} (w_2(x/ℓ) + w_2((x+v/N)/ℓ)) |v|^{-1-s}`, where `D` bounds the
divided differences `Z_x, Z_xy` and `D_g` bounds the kernel derivatives `g'', g'''`.
The constants enter as hypotheses, so that the main theorem can take them from the lemmas.
-/

@[expose] public section

open Set Filter Topology
open scoped ContDiff

namespace Riesz1

/-- The derivative of `R_x` in `v` on `gradCellSet N`. With `r = v/N` and `y = x + r`, the chain
rule gives `R_x'(v) = -N^{-s} N^{-1} (2 r Z_x g'' + r^2 Z_xy g'' + r^2 Z_x g''')`. -/
lemma hasDerivAt_gradCellR {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) {ℓ : ℝ} (hℓ : 0 < ℓ) (N : ℕ) (x : ℝ) {v : ℝ}
    (hv : v ∈ gradCellSet N) :
    HasDerivAt (gradCellR s N ℓ ψ x)
      (-(N : ℝ) ^ (-s) * (2 * (v / N) * (1 / N) * gradZx ψ ℓ x (x + v / N) *
          iteratedDeriv 2 (hurwitzKernel s) (v / N) +
        (v / N) ^ 2 * (gradZxy ψ ℓ x (x + v / N) * (1 / N)) *
          iteratedDeriv 2 (hurwitzKernel s) (v / N) +
        (v / N) ^ 2 * gradZx ψ ℓ x (x + v / N) *
          (iteratedDeriv 3 (hurwitzKernel s) (v / N) * (1 / N)))) v := by
  have hr : v / (N : ℝ) ≠ 0 := gradCellSet_div_ne_zero hv
  have hr' : ((v / (N : ℝ) : ℝ) : UnitAddCircle) ≠ 0 := hv
  have hy : x + v / (N : ℝ) ≠ x := fun h => hr (by linarith)
  have hlin : HasDerivAt (fun t : ℝ => t / (N : ℝ)) (1 / (N : ℝ)) v :=
    (hasDerivAt_id v).div_const _
  have hp : HasDerivAt (fun t : ℝ => (t / (N : ℝ)) ^ 2) (2 * (v / N) * (1 / N)) v :=
    (hlin.pow 2).congr_deriv (by norm_num)
  have hgap : HasDerivAt (fun t : ℝ => x + t / (N : ℝ)) (1 / (N : ℝ)) v := hlin.const_add x
  have hZx := (hasDerivAt_gradZx hψ hℓ hy).comp v hgap
  have hg := (gradSplit_hasDerivAt_iteratedDeriv s hs0 hs1 2 hr').comp v hlin
  have hall := ((hp.const_mul (-(N : ℝ) ^ (-s))).mul hZx).mul hg
  have e3 : (2 : ℕ) + 1 = 3 := rfl
  refine hall.congr_deriv ?_
  simp only [Pi.mul_apply, Function.comp_apply, e3]
  ring

/-- Algebraic core of the derivative bound. With `m = N^{-s}` and `c = 1/N` nonnegative, if
`|Z_x| ≤ E`, `|Z_xy| ≤ E |r|^{-1}`, `|g''(r)| ≤ D_g |r|^{-2-s}` and `|g'''(r)| ≤ D_g |r|^{-3-s}`,
then the bracket of the derivative is at most `m · 4 E D_g c |r|^{-1-s}` in absolute value. -/
lemma gradCell_deriv_alg {s m c r Zx Zxy g2 g3 E Dg : ℝ} (hr : r ≠ 0)
    (hm : 0 ≤ m) (hc : 0 ≤ c) (hE : 0 ≤ E) (hZx : |Zx| ≤ E)
    (hZxy : |Zxy| ≤ E * |r|⁻¹) (hg2 : |g2| ≤ Dg * |r| ^ (-s - 2))
    (hg3 : |g3| ≤ Dg * |r| ^ (-s - 3)) :
    |-m * (2 * r * c * Zx * g2 + r ^ 2 * (Zxy * c) * g2 + r ^ 2 * Zx * (g3 * c))| ≤
      m * (4 * E * Dg * c * |r| ^ (-s - 1)) := by
  have hT : 0 < |r| := abs_pos.mpr hr
  have hTne : |r| ≠ 0 := hT.ne'
  -- Powers of `|r|`: each product collapses to `|r|^(-s-1)`.
  have h1 : |r| * |r| ^ (-s - 2) = |r| ^ (-s - 1) := by
    rw [show -s - 1 = 1 + (-s - 2) by ring, Real.rpow_add hT, Real.rpow_one]
  have h2 : |r| ^ 2 * |r| ^ (-s - 3) = |r| ^ (-s - 1) := by
    rw [show -s - 1 = (2 : ℝ) + (-s - 3) by ring, Real.rpow_add hT, Real.rpow_two]
  have hinv : |r| ^ 2 * |r|⁻¹ = |r| := by
    field_simp
  have h3 : |r| ^ 2 * |r|⁻¹ * |r| ^ (-s - 2) = |r| ^ (-s - 1) := by
    rw [hinv, h1]
  -- The three terms of the bracket.
  have hA : |2 * r * c * Zx * g2| ≤ 2 * E * Dg * c * |r| ^ (-s - 1) := by
    have e : |2 * r * c * Zx * g2| = 2 * |r| * c * |Zx| * |g2| := by
      simp only [abs_mul, abs_of_nonneg hc, abs_two]
    rw [e]
    calc 2 * |r| * c * |Zx| * |g2|
        ≤ 2 * |r| * c * E * (Dg * |r| ^ (-s - 2)) := by
          gcongr
      _ = 2 * E * Dg * c * (|r| * |r| ^ (-s - 2)) := by ring
      _ = 2 * E * Dg * c * |r| ^ (-s - 1) := by rw [h1]
  have hB : |r ^ 2 * (Zxy * c) * g2| ≤ E * Dg * c * |r| ^ (-s - 1) := by
    have e : |r ^ 2 * (Zxy * c) * g2| = |r| ^ 2 * |Zxy| * c * |g2| := by
      simp only [abs_mul, abs_pow, abs_of_nonneg hc]
      ring
    rw [e]
    calc |r| ^ 2 * |Zxy| * c * |g2|
        ≤ |r| ^ 2 * (E * |r|⁻¹) * c * (Dg * |r| ^ (-s - 2)) := by
          gcongr
      _ = E * Dg * c * (|r| ^ 2 * |r|⁻¹ * |r| ^ (-s - 2)) := by ring
      _ = E * Dg * c * |r| ^ (-s - 1) := by rw [h3]
  have hC : |r ^ 2 * Zx * (g3 * c)| ≤ E * Dg * c * |r| ^ (-s - 1) := by
    have e : |r ^ 2 * Zx * (g3 * c)| = |r| ^ 2 * |Zx| * c * |g3| := by
      simp only [abs_mul, abs_pow, abs_of_nonneg hc]
      ring
    rw [e]
    calc |r| ^ 2 * |Zx| * c * |g3|
        ≤ |r| ^ 2 * E * c * (Dg * |r| ^ (-s - 3)) := by
          gcongr
      _ = E * Dg * c * (|r| ^ 2 * |r| ^ (-s - 3)) := by ring
      _ = E * Dg * c * |r| ^ (-s - 1) := by rw [h2]
  -- Combine the three terms.
  rw [abs_mul, abs_neg, abs_of_nonneg hm]
  calc m * |2 * r * c * Zx * g2 + r ^ 2 * (Zxy * c) * g2 + r ^ 2 * Zx * (g3 * c)|
      ≤ m * (|2 * r * c * Zx * g2| + |r ^ 2 * (Zxy * c) * g2| + |r ^ 2 * Zx * (g3 * c)|) := by
        gcongr
        exact abs_add_three _ _ _
    _ ≤ m * (2 * E * Dg * c * |r| ^ (-s - 1) + E * Dg * c * |r| ^ (-s - 1) +
          E * Dg * c * |r| ^ (-s - 1)) := by
        gcongr
    _ = m * (4 * E * Dg * c * |r| ^ (-s - 1)) := by ring

/-- The scaling identity: `N^{-s} N^{-1} |v/N|^{-1-s} = |v|^{-1-s}`, written with `-s-1`. -/
lemma gradCell_scale {s N v : ℝ} (hN : 0 < N) :
    N ^ (-s) * (1 / N) * |v / N| ^ (-s - 1) = |v| ^ (-s - 1) := by
  rw [abs_div, abs_of_pos hN, Real.div_rpow (abs_nonneg v) hN.le]
  have hNs : N ^ (-s) = N ^ (-s - 1) * N := by
    rw [← Real.rpow_add_one hN.ne' (-s - 1)]
    congr 1
    ring
  have hA : N ^ (-s - 1) ≠ 0 := (Real.rpow_pos_of_pos hN _).ne'
  have hNne : N ≠ 0 := hN.ne'
  rw [hNs]
  generalize N ^ (-s - 1) = A at hA ⊢
  generalize |v| ^ (-s - 1) = B
  field_simp

/-- The derivative bound of the cell part of Lemma 5.7 on `1/2 ≤ |v| ≤ 3N/4`:
`|R_x'(v)| ≤ 4 D D_g C_0 ℓ^{-1} (w_2(x/ℓ) + w_2((x+v/N)/ℓ)) |v|^{-1-s}`. The hypotheses `hZ`,
`hZxy` are the bounds on `Z_x, Z_xy` of the differences part of Lemma 5.7, and `hg2`, `hg3`
are the kernel bounds of the kernel part of Lemma 5.7. -/
lemma gradCellR_deriv_bound {s a : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) {ℓ : ℝ} (hℓ : 0 < ℓ) (N : ℕ) (hN : 2 ≤ N) (x : ℝ) {v : ℝ}
    (hv : v ∈ gradCellSet N) (hv2 : |v| ≤ 3 * N / 4)
    {C0 D Dg : ℝ} (hC0 : 0 ≤ C0) (hD : 0 ≤ D)
    (hW : ∀ y : ℝ, 0 ≤ gradWeightTwo s a ((N : ℝ) * ℓ) ℓ⁻¹ (y / ℓ))
    (hZ : ∀ y : ℝ, 0 < |y - x| → |gradZx ψ ℓ x y| ≤ D * C0 * ℓ⁻¹ *
      (gradWeightTwo s a ((N : ℝ) * ℓ) ℓ⁻¹ (x / ℓ) + gradWeightTwo s a ((N : ℝ) * ℓ) ℓ⁻¹ (y / ℓ)))
    (hZxy : ∀ y : ℝ, 0 < |y - x| → |gradZxy ψ ℓ x y| ≤ D * C0 * ℓ⁻¹ * |y - x|⁻¹ *
      (gradWeightTwo s a ((N : ℝ) * ℓ) ℓ⁻¹ (x / ℓ) + gradWeightTwo s a ((N : ℝ) * ℓ) ℓ⁻¹ (y / ℓ)))
    (hg2 : ∀ r : ℝ, 0 < |r| → |r| ≤ 3 / 4 → |iteratedDeriv 2 (hurwitzKernel s) r| ≤
      Dg * |r| ^ (-s - 2))
    (hg3 : ∀ r : ℝ, 0 < |r| → |r| ≤ 3 / 4 → |iteratedDeriv 3 (hurwitzKernel s) r| ≤
      Dg * |r| ^ (-s - 3)) :
    |deriv (gradCellR s N ℓ ψ x) v| ≤ 4 * D * Dg * (C0 * ℓ⁻¹ *
      (gradWeightTwo s a ((N : ℝ) * ℓ) ℓ⁻¹ (x / ℓ) +
        gradWeightTwo s a ((N : ℝ) * ℓ) ℓ⁻¹ ((x + v / N) / ℓ))) * |v| ^ (-1 - s) := by
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hr : v / (N : ℝ) ≠ 0 := gradCellSet_div_ne_zero hv
  have hv0 : v ≠ 0 := fun h => hr (by simp [h])
  have hrabs : |v / (N : ℝ)| ≤ 3 / 4 := by
    rw [abs_div, abs_of_pos hNpos, div_le_iff₀ hNpos]
    linarith
  have hTpos : 0 < |v / (N : ℝ)| := abs_pos.mpr hr
  have hy : x + v / (N : ℝ) - x = v / (N : ℝ) := by ring
  have hℓi : 0 ≤ ℓ⁻¹ := inv_nonneg.mpr hℓ.le
  have hW0 : 0 ≤ gradWeightTwo s a ((N : ℝ) * ℓ) ℓ⁻¹ (x / ℓ) +
      gradWeightTwo s a ((N : ℝ) * ℓ) ℓ⁻¹ ((x + v / N) / ℓ) :=
    add_nonneg (hW _) (hW _)
  have hE : 0 ≤ D * C0 * ℓ⁻¹ * (gradWeightTwo s a ((N : ℝ) * ℓ) ℓ⁻¹ (x / ℓ) +
      gradWeightTwo s a ((N : ℝ) * ℓ) ℓ⁻¹ ((x + v / N) / ℓ)) :=
    mul_nonneg (mul_nonneg (mul_nonneg hD hC0) hℓi) hW0
  have hZx : |gradZx ψ ℓ x (x + v / (N : ℝ))| ≤ D * C0 * ℓ⁻¹ *
      (gradWeightTwo s a ((N : ℝ) * ℓ) ℓ⁻¹ (x / ℓ) +
        gradWeightTwo s a ((N : ℝ) * ℓ) ℓ⁻¹ ((x + v / N) / ℓ)) :=
    hZ (x + v / N) (by rw [hy]; exact abs_pos.mpr hr)
  have hZxy' : |gradZxy ψ ℓ x (x + v / (N : ℝ))| ≤ D * C0 * ℓ⁻¹ * |v / (N : ℝ)|⁻¹ *
      (gradWeightTwo s a ((N : ℝ) * ℓ) ℓ⁻¹ (x / ℓ) +
        gradWeightTwo s a ((N : ℝ) * ℓ) ℓ⁻¹ ((x + v / N) / ℓ)) := by
    have h := hZxy (x + v / N) (by rw [hy]; exact abs_pos.mpr hr)
    rwa [hy] at h
  have hZxy'' : |gradZxy ψ ℓ x (x + v / (N : ℝ))| ≤
      (D * C0 * ℓ⁻¹ * (gradWeightTwo s a ((N : ℝ) * ℓ) ℓ⁻¹ (x / ℓ) +
        gradWeightTwo s a ((N : ℝ) * ℓ) ℓ⁻¹ ((x + v / N) / ℓ))) * |v / (N : ℝ)|⁻¹ := by
    refine hZxy'.trans (le_of_eq ?_)
    ring
  have key := gradCell_deriv_alg (s := s) (m := (N : ℝ) ^ (-s)) (c := 1 / (N : ℝ))
    (r := v / (N : ℝ)) (E := D * C0 * ℓ⁻¹ * (gradWeightTwo s a ((N : ℝ) * ℓ) ℓ⁻¹ (x / ℓ) +
        gradWeightTwo s a ((N : ℝ) * ℓ) ℓ⁻¹ ((x + v / N) / ℓ)))
    (Dg := Dg) hr (Real.rpow_nonneg hNpos.le _) (by positivity) hE hZx hZxy''
    (hg2 _ hTpos hrabs) (hg3 _ hTpos hrabs)
  rw [hasDerivAt_gradCellR hs0 hs1 hψ hℓ N x hv |>.deriv]
  have hscale := gradCell_scale (s := s) (v := v) hNpos
  calc _ ≤ _ := key
    _ = 4 * (D * C0 * ℓ⁻¹ * (gradWeightTwo s a ((N : ℝ) * ℓ) ℓ⁻¹ (x / ℓ) +
        gradWeightTwo s a ((N : ℝ) * ℓ) ℓ⁻¹ ((x + v / N) / ℓ))) * Dg *
          ((N : ℝ) ^ (-s) * (1 / (N : ℝ)) * |v / (N : ℝ)| ^ (-s - 1)) := by ring
    _ = 4 * (D * C0 * ℓ⁻¹ * (gradWeightTwo s a ((N : ℝ) * ℓ) ℓ⁻¹ (x / ℓ) +
        gradWeightTwo s a ((N : ℝ) * ℓ) ℓ⁻¹ ((x + v / N) / ℓ))) * Dg * |v| ^ (-s - 1) := by
          rw [hscale]
    _ = 4 * D * Dg * (C0 * ℓ⁻¹ *
        (gradWeightTwo s a ((N : ℝ) * ℓ) ℓ⁻¹ (x / ℓ) +
          gradWeightTwo s a ((N : ℝ) * ℓ) ℓ⁻¹ ((x + v / N) / ℓ))) * |v| ^ (-1 - s) := by
          rw [show (-1 - s) = -s - 1 by ring]
          ring

end Riesz1

end
