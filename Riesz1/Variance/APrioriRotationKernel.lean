/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.Calculus.CutoffMajorant
public import Riesz1.ToMathlib.Calculus.PeriodicDerivativeTail

/-!
# Pointwise bound for the exterior kernel

The exterior tail in the proof of Lemma 5.2. For a `C¹` function `f` of period `L`, with
`f (L/2) = 0` and the derivative bound of the kernel, every point `x ∈ (0, L)` satisfies
`|f x| ≤ C K^{λ+ε} (2/r)^A + r^{s-2}/(2-s)` with `r = min(x, L - x)`.

When `x = F/K` and `L - x = G/K` for arc lengths `F, G > 0`, this becomes a bound by the
inverse powers of `F` and `G`, which the Gibbs moments control (`abs_le_blocks`).
-/

@[expose] public section

open MeasureTheory Set

namespace Riesz1

/-- The constant of the kernel bound: `∫_0^c` of the majorant is at most
`kernelConst s λ ε · K^{λ+ε}`. -/
noncomputable def kernelConst (s lam ε : ℝ) : ℝ :=
  2 ^ (ε + (1 + lam + ε)) / (lam + ε) + 2 ^ (3 - s) / (2 - s)

/-- The constant `kernelConst` is nonnegative. -/
theorem kernelConst_nonneg {s lam ε : ℝ} (hs : s < 2) (hlam : 0 ≤ lam) (hε : 0 < ε) :
    0 ≤ kernelConst s lam ε := by
  unfold kernelConst
  have h1 : 0 ≤ 2 ^ (ε + (1 + lam + ε)) / (lam + ε) :=
    div_nonneg (by positivity) (by linarith)
  have h2 : 0 ≤ 2 ^ (3 - s) / (2 - s) := div_nonneg (by positivity) (by linarith)
  linarith

/-- Every point of `(0, L)` is a periodic translate of a point of `[-L/2, L/2]` whose absolute
value is the distance `min(x, L - x)` to the lattice `L ℤ`. -/
theorem exists_rep_periodic {L : ℝ} {f : ℝ → ℝ} (hper : Function.Periodic f L)
    {x : ℝ} (hx0 : 0 < x) (hxL : x < L) :
    ∃ u ∈ Icc (-(L / 2)) (L / 2), f x = f u ∧ |u| = min x (L - x) := by
  by_cases h : x ≤ L / 2
  · refine ⟨x, ⟨by linarith, h⟩, rfl, ?_⟩
    rw [abs_of_pos hx0, min_eq_left (by linarith)]
  · have h' : L / 2 < x := lt_of_not_ge h
    refine ⟨x - L, ⟨by linarith, by linarith⟩, (hper.sub_eq x).symm, ?_⟩
    rw [abs_of_neg (by linarith), min_eq_right (by linarith)]
    ring

/-- **Pointwise kernel bound.** Under the hypotheses of the exterior tail, with `K ≥ 1`,
`λ ≥ 0`, `ε > 0`, `A ≥ 0`, every `u` in `[-L/2, L/2]` with `u ≠ 0` satisfies
`|f u| ≤ kernelConst · K^{λ+ε} (2/|u|)^A + |u|^{s-2}/(2-s)`. -/
theorem abs_le_kernel {L s lam K ε A : ℝ} (hL : 0 < L) (hs : s < 2) (hK : 1 ≤ K)
    (hlam : 0 ≤ lam) (hε : 0 < ε) (hA : 0 ≤ A) {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hper : Function.Periodic f L) (hzero : f (L / 2) = 0)
    (hder : ∀ u ∈ Icc (-(L / 2)) (L / 2), |deriv f u| ≤ cutoffMajorant s lam K |u|)
    {u : ℝ} (hu : u ∈ Icc (-(L / 2)) (L / 2)) (hu0 : 0 < |u|) :
    |f u| ≤ kernelConst s lam ε * K ^ (lam + ε) * (2 / |u|) ^ A + |u| ^ (s - 2) / (2 - s) := by
  have hK0 : 0 < K := by linarith
  have hB : ∀ᵐ t ∂volume, t ∈ Icc (-(L / 2)) (L / 2) → |deriv f t| ≤ cutoffMajorant s lam K |t| :=
    ae_of_all _ fun t ht => hder t ht
  have hbase := abs_le_intervalIntegral_of_periodic hL hf hper hzero
    (cutoffMajorant_intervalIntegrable hs hK hlam 0 (L / 2)) hB hu
  have hL2 : 0 ≤ L / 2 := by linarith
  have hur : |u| ≤ L / 2 := abs_le.2 ⟨by linarith [hu.1], hu.2⟩
  have hpow : 0 ≤ (2 / |u|) ^ A := Real.rpow_nonneg (by positivity) _
  have hnn : 0 ≤ |u| ^ (s - 2) / (2 - s) :=
    div_nonneg (Real.rpow_nonneg (abs_nonneg u) _) (by linarith)
  have hMK : 0 ≤ kernelConst s lam ε * K ^ (lam + ε) :=
    mul_nonneg (kernelConst_nonneg hs hlam hε) (Real.rpow_nonneg hK0.le _)
  rcases le_total |u| 2 with h2 | h2
  · -- Near case: the integral from `|u|` is at most the integral from `0`.
    have h1 := integral_cutoffMajorant_tail_le (r := |u|) (c := L / 2) hs hK hlam (abs_nonneg u)
    have h2' := integral_cutoffMajorant_le (c := L / 2) hs hK hlam hε hL2
    have hge : 1 ≤ (2 / |u|) ^ A := Real.one_le_rpow ((one_le_div hu0).2 h2) hA
    have hmul : kernelConst s lam ε * K ^ (lam + ε) ≤
        kernelConst s lam ε * K ^ (lam + ε) * (2 / |u|) ^ A :=
      le_mul_of_one_le_right hMK hge
    have hkc : (2 ^ (ε + (1 + lam + ε)) / (lam + ε) + 2 ^ (3 - s) / (2 - s)) * K ^ (lam + ε) =
        kernelConst s lam ε * K ^ (lam + ε) := rfl
    rw [hkc] at h2'
    linarith
  · -- Far case: the integral from `|u| ≥ 2` is at most `|u|^{s-2}/(2-s)`.
    have h1 := integral_cutoffMajorant_tail (lam := lam) (K := K) hs h2 hur
    have hm : 0 ≤ kernelConst s lam ε * K ^ (lam + ε) * (2 / |u|) ^ A := mul_nonneg hMK hpow
    linarith

/-- The minimum of two positive numbers, raised to a nonpositive power `-q` with `q ≥ 0`, is at
most the sum of the two powers. -/
theorem min_rpow_neg_le_add {F G q : ℝ} (hF : 0 < F) (hG : 0 < G) (_hq : 0 ≤ q) :
    (min F G) ^ (-q) ≤ F ^ (-q) + G ^ (-q) := by
  have hFq : 0 ≤ F ^ (-q) := Real.rpow_nonneg hF.le _
  have hGq : 0 ≤ G ^ (-q) := Real.rpow_nonneg hG.le _
  rcases min_choice F G with h | h <;> rw [h]
  · linarith
  · linarith

/-- Division rule for real powers: `(c / D)^A = c^A · D^{-A}` for `c ≥ 0` and `D > 0`. -/
theorem kernel_div_rpow_eq_mul_rpow_neg {c D A : ℝ} (hc : 0 ≤ c) (hD : 0 < D) :
    (c / D) ^ A = c ^ A * D ^ (-A) := by
  rw [Real.div_rpow hc hD.le, Real.rpow_neg hD.le, div_eq_mul_inv]

/-- Rescaled power: `(D/K)^{s-2} = K^{2-s} · D^{s-2}` for `D, K > 0`. -/
theorem div_rpow_sub_two_eq {D K s : ℝ} (hD : 0 < D) (hK : 0 < K) :
    (D / K) ^ (s - 2) = K ^ (2 - s) * D ^ (s - 2) := by
  rw [Real.div_rpow hD.le hK.le, show s - 2 = -(2 - s) by ring, Real.rpow_neg hK.le]
  rw [show -(2 - s) = s - 2 by ring]
  rw [div_eq_mul_inv, inv_inv, mul_comm]

/-- **Pointwise bound by the arc lengths.** Let `F, G > 0` with `x = F/K` and `L - x = G/K`, so
that `F + G = K L`. Then `|f x|` is at most `α(F^{-A} + G^{-A}) + β(F^{-(2-s)} + G^{-(2-s)})`,
where `α = kernelConst · K^{λ+ε} (2K)^A` and `β = K^{2-s}/(2-s)`. -/
theorem abs_le_blocks {L s lam K ε A : ℝ} (hL : 0 < L) (hs : s < 2) (hK : 1 ≤ K)
    (hlam : 0 ≤ lam) (hε : 0 < ε) (hA : 0 ≤ A) {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hper : Function.Periodic f L) (hzero : f (L / 2) = 0)
    (hder : ∀ u ∈ Icc (-(L / 2)) (L / 2), |deriv f u| ≤ cutoffMajorant s lam K |u|)
    {x F G : ℝ} (hx0 : 0 < x) (hxL : x < L) (hF : 0 < F) (hG : 0 < G)
    (hxF : x = F / K) (hLx : L - x = G / K) :
    |f x| ≤ kernelConst s lam ε * K ^ (lam + ε) * (2 * K) ^ A * (F ^ (-A) + G ^ (-A)) +
      K ^ (2 - s) / (2 - s) * (F ^ (-(2 - s)) + G ^ (-(2 - s))) := by
  have hK0 : 0 < K := by linarith
  obtain ⟨u, hu, hfu, hru⟩ := exists_rep_periodic hper hx0 hxL
  have hD : 0 < min F G := lt_min hF hG
  have hr : |u| = min F G / K := by
    rw [hru, hLx, hxF, min_div_div_right hK0.le]
  have hu0 : 0 < |u| := by
    rw [hr]
    exact div_pos hD hK0
  have hk := abs_le_kernel hL hs hK hlam hε hA hf hper hzero hder hu hu0
  rw [hfu]
  set D := min F G with hDdef
  have hK0' : (0 : ℝ) ≤ 2 * K := by linarith
  have hA_eq : (2 / |u|) ^ A = (2 * K) ^ A * D ^ (-A) := by
    rw [hr, div_div_eq_mul_div]
    exact kernel_div_rpow_eq_mul_rpow_neg hK0' hD
  have hB_eq : |u| ^ (s - 2) = K ^ (2 - s) * D ^ (s - 2) := by
    rw [hr]
    exact div_rpow_sub_two_eq hD hK0
  have hmin1 : D ^ (-A) ≤ F ^ (-A) + G ^ (-A) := min_rpow_neg_le_add hF hG hA
  have hmin2 : D ^ (s - 2) ≤ F ^ (-(2 - s)) + G ^ (-(2 - s)) := by
    rw [show s - 2 = -(2 - s) by ring]
    exact min_rpow_neg_le_add hF hG (by linarith)
  have hc1 : 0 ≤ kernelConst s lam ε * K ^ (lam + ε) * (2 * K) ^ A :=
    mul_nonneg (mul_nonneg (kernelConst_nonneg hs hlam hε) (Real.rpow_nonneg hK0.le _))
      (Real.rpow_nonneg hK0' _)
  have hc2 : 0 ≤ K ^ (2 - s) / (2 - s) :=
    div_nonneg (Real.rpow_nonneg hK0.le _) (by linarith)
  calc |f u| ≤ kernelConst s lam ε * K ^ (lam + ε) * (2 / |u|) ^ A + |u| ^ (s - 2) / (2 - s) := hk
    _ = kernelConst s lam ε * K ^ (lam + ε) * (2 * K) ^ A * D ^ (-A) +
          K ^ (2 - s) / (2 - s) * D ^ (s - 2) := by
        rw [hA_eq, hB_eq]
        ring
    _ ≤ kernelConst s lam ε * K ^ (lam + ε) * (2 * K) ^ A * (F ^ (-A) + G ^ (-A)) +
          K ^ (2 - s) / (2 - s) * (F ^ (-(2 - s)) + G ^ (-(2 - s))) :=
        add_le_add (mul_le_mul_of_nonneg_left hmin1 hc1) (mul_le_mul_of_nonneg_left hmin2 hc2)

end Riesz1

end
