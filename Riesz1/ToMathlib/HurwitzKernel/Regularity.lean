/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.HurwitzKernel.Mean
public import Riesz1.ToMathlib.HurwitzKernel.Symmetric
public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Analysis.Analytic.IteratedFDeriv

/-!
# Spatial regularity of the Hurwitz kernel

The unit-interval Euler errors extend to a locally uniformly summable
holomorphic series on `-1/2 < re w`. This proves smoothness off the integers
and a smooth remainder after removing the singularity of the project kernel
`2 * re (hurwitzZetaEven x s)`, as in Lemma 2.1.
Compactness supplies a lower bound. The singular power gives the collision limit.
-/

public section

open Filter Topology MeasureTheory Set Complex
open scoped ContDiff
namespace Riesz1

/-- The Euler unit-interval error with a complex spatial parameter. -/
@[expose] noncomputable def eulerTermC (s : ℝ) (w : ℂ) (n : ℕ) : ℂ :=
  ((n : ℂ) + 1 + w) ^ (-(s : ℂ)) -
    (((n : ℂ) + 2) ^ (1 - (s : ℂ)) - ((n : ℂ) + 1) ^ (1 - (s : ℂ))) / (1 - (s : ℂ))

lemma norm_cpow_sub_halfplane (s : ℝ) (hs : 0 < s) (A : ℝ) (hA : 0 < A)
    (w : ℂ) (hw : A / 2 ≤ w.re) :
    ‖w ^ (-(s : ℂ)) - (A : ℂ) ^ (-(s : ℂ))‖ ≤
      s * (A / 2) ^ (-s - 1) * ‖w - (A : ℂ)‖ := by
  have hd (v : ℂ) (hv : A / 2 ≤ v.re) :
      HasDerivAt (fun v : ℂ => v ^ (-(s : ℂ)))
        (-(s : ℂ) * v ^ (-(s : ℂ) - 1)) v := by
    have hv0 : v ∈ slitPlane := Or.inl (by linarith)
    simpa only [mul_one, id_eq] using (hasDerivAt_id v).cpow_const hv0
  have hb (v : ℂ) (hv : A / 2 ≤ v.re) :
      ‖-(s : ℂ) * v ^ (-(s : ℂ) - 1)‖ ≤ s * (A / 2) ^ (-s - 1) := by
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg hs.le]
    rw [show -(s : ℂ) - 1 = ((-s - 1 : ℝ) : ℂ) by push_cast; rfl, norm_cpow_real]
    apply mul_le_mul_of_nonneg_left _ hs.le
    exact Real.rpow_le_rpow_of_nonpos (by linarith) (hv.trans (Complex.re_le_norm v)) (by linarith)
  exact Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (𝕜 := ℂ) (s := {v : ℂ | A / 2 ≤ v.re})
    (fun v hv => (hd v hv).hasFDerivAt.hasFDerivWithinAt)
    (fun v hv => by simpa only [ContinuousLinearMap.norm_toSpanSingleton] using hb v hv)
    (convex_halfSpace_re_ge _) (by simp; linarith) hw

lemma norm_eulerTermC_le (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1)
    (R : ℝ) (_hR : 0 ≤ R) (w : ℂ) (hw : -(1 / 2 : ℝ) < w.re) (hwR : ‖w‖ ≤ R) (n : ℕ) :
    ‖eulerTermC s w n‖ ≤ (s + s * 2 ^ (s + 1) * R) * ((n : ℝ) + 1) ^ (-s - 1) := by
  have hA : 0 < (n : ℝ) + 1 := by positivity
  have h := norm_cpow_sub_halfplane s hs0 ((n : ℝ) + 1) hA ((n : ℂ) + 1 + w) (by
    simp only [add_re, natCast_re, one_re]
    linarith [Nat.cast_nonneg (α := ℝ) n])
  have hnorm : ‖(n : ℂ) + 1 + w - (((n : ℝ) + 1 : ℝ) : ℂ)‖ = ‖w‖ := by
    congr 1
    push_cast
    ring
  rw [hnorm] at h
  have hscale : (((n : ℝ) + 1) / 2) ^ (-s - 1) =
      ((n : ℝ) + 1) ^ (-s - 1) * 2 ^ (s + 1) := by
    rw [Real.div_rpow hA.le (by norm_num)]
    rw [show -s - 1 = -(s + 1) by ring, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    simp only [div_inv_eq_mul]
  have h0 := norm_eulerTerm_le 0 le_rfl zero_le_one (s : ℂ) hs0 (by exact_mod_cast hs1.ne) n
  simp only [ofReal_re, Complex.norm_real, Real.norm_of_nonneg hs0.le] at h0
  have hsplit : eulerTermC s w n = eulerTerm 0 (s : ℂ) n +
      (((n : ℂ) + 1 + w) ^ (-(s : ℂ)) - (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-(s : ℂ))) := by
    unfold eulerTermC eulerTerm
    push_cast
    ring_nf
  rw [hsplit]
  apply (norm_add_le _ _).trans
  apply (add_le_add h0 (h.trans (mul_le_mul_of_nonneg_left hwR (by positivity)))).trans
  rw [hscale]
  apply le_of_eq
  ring

lemma differentiableAt_tsum_eulerTermC (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1)
    (w : ℂ) (hw : -(1 / 2 : ℝ) < w.re) :
    DifferentiableAt ℂ (fun w => ∑' n, eulerTermC s w n) w := by
  let R := ‖w‖ + 1
  let U := {v : ℂ | -(1 / 2 : ℝ) < v.re ∧ ‖v‖ < R}
  have hU : IsOpen U := (isOpen_lt continuous_const continuous_re).inter
    (isOpen_lt continuous_norm continuous_const)
  have hwU : w ∈ U := ⟨hw, by dsimp [R]; linarith⟩
  have hs : Summable (fun n : ℕ => (s + s * 2 ^ (s + 1) * R) * ((n : ℝ) + 1) ^ (-s - 1)) := by
    apply Summable.mul_left
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr (show -s - 1 < -1 by linarith))
  apply (differentiableOn_tsum_of_summable_norm hs (fun n v hv => ?_) hU
    (fun n v hv => norm_eulerTermC_le s hs0 hs1 R (by dsimp [R]; positivity) v hv.1 hv.2.le n)).differentiableAt
    (hU.mem_nhds hwU)
  have hslit : (n : ℂ) + 1 + v ∈ slitPlane := by
    apply Or.inl
    simp only [add_re, natCast_re, one_re]
    linarith [hv.1, Nat.cast_nonneg (α := ℝ) n]
  unfold eulerTermC
  exact (((differentiableAt_const _).add differentiableAt_id).cpow_const hslit |>.sub
    (differentiableAt_const _)).differentiableWithinAt

lemma contDiffAt_euler_remainder (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1)
    (x : ℝ) (hx : -(1 / 2 : ℝ) < x) :
    ContDiffAt ℝ ∞ (fun x : ℝ => (∑' n, eulerTermC s (x : ℂ) n).re) x := by
  have hD : DifferentiableOn ℂ (fun w => ∑' n, eulerTermC s w n)
      {w : ℂ | -(1 / 2 : ℝ) < w.re} :=
    fun w hw => (differentiableAt_tsum_eulerTermC s hs0 hs1 w hw).differentiableWithinAt
  have hU : IsOpen {w : ℂ | -(1 / 2 : ℝ) < w.re} := isOpen_lt continuous_const continuous_re
  have hCD : ContDiffAt ℂ ∞ (fun w => ∑' n, eulerTermC s w n) (x : ℂ) :=
    (hD.contDiffOn hU).contDiffAt (hU.mem_nhds hx)
  exact Complex.reCLM.contDiff.contDiffAt.comp x
    ((hCD.restrict_scalars ℝ).comp x Complex.ofRealCLM.contDiff.contDiffAt)

/-- Evenness of the kernel on the real line (Lemma 2.1). -/
theorem hurwitzZetaEven_re_even (s : ℂ) :
    Function.Even (fun x : ℝ => (HurwitzZeta.hurwitzZetaEven (x : UnitAddCircle) s).re) := by
  intro x
  simp [HurwitzZeta.hurwitzZetaEven_neg]

/-- Period one of the kernel (Lemma 2.1). -/
theorem hurwitzZetaEven_re_periodic (s : ℂ) :
    Function.Periodic (fun x : ℝ => (HurwitzZeta.hurwitzZetaEven (x : UnitAddCircle) s).re) 1 := by
  intro x
  simp

/-- The sum of the two Hurwitz values equals the project kernel, with its real
value embedded in `ℂ` (Lemma 2.1). Periodicity makes
the identity valid for every real lift, including the assigned collision value. -/
theorem hurwitzZetaEven_re_eq_hurwitzZeta_add (s x : ℝ) :
    ((2 * (HurwitzZeta.hurwitzZetaEven (x : UnitAddCircle) (s : ℂ)).re : ℝ) : ℂ) =
      HurwitzZeta.hurwitzZeta (x : UnitAddCircle) (s : ℂ) +
      HurwitzZeta.hurwitzZeta ((1 - x : ℝ) : UnitAddCircle) (s : ℂ) := by
  have hcoe : ((1 - x : ℝ) : UnitAddCircle) = -(x : UnitAddCircle) := by simp
  have heq : 2 * HurwitzZeta.hurwitzZetaEven (x : UnitAddCircle) (s : ℂ) =
      HurwitzZeta.hurwitzZeta (x : UnitAddCircle) (s : ℂ) +
      HurwitzZeta.hurwitzZeta ((1 - x : ℝ) : UnitAddCircle) (s : ℂ) := by
    rw [hcoe, HurwitzZeta.hurwitzZetaEven_eq]
    ring
  rw [← heq]
  apply Complex.ext <;> simp [hurwitzZetaEven_ofReal_im]

/-- Euler-series expression of the project kernel on `(0,1)`
(Lemma 2.1). -/
lemma hurwitzZetaEven_re_euler (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1)
    (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    2 * (HurwitzZeta.hurwitzZetaEven (x : UnitAddCircle) (s : ℂ)).re =
      x ^ (-s) + (1 - x) ^ (-s) +
      (∑' n, eulerTermC s (x : ℂ) n).re + (∑' n, eulerTermC s ((1 - x : ℝ) : ℂ) n).re -
        2 / (1 - s) := by
  rw [hurwitzZetaEven_re_expression, hurwitzZeta_re_euler s hs0 hs1 x hx0 hx1.le,
    hurwitzZeta_re_euler s hs0 hs1 (1 - x) (by linarith) (by linarith)]
  change x ^ (-s) + (∑' n, eulerTermC s (x : ℂ) n).re - 1 / (1 - s) +
      ((1 - x) ^ (-s) + (∑' n, eulerTermC s ((1 - x : ℝ) : ℂ) n).re - 1 / (1 - s)) = _
  ring

lemma contDiffAt_hurwitzZetaEven_re_of_mem_Ioo (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1)
    (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    ContDiffAt ℝ ∞ (fun x : ℝ => (HurwitzZeta.hurwitzZetaEven (x : UnitAddCircle) (s : ℂ)).re) x := by
  have hQ := contDiffAt_euler_remainder s hs0 hs1 x (by linarith)
  have hQ' := (contDiffAt_euler_remainder s hs0 hs1 (1 - x) (by linarith)).comp x
    (contDiffAt_const.sub contDiffAt_id)
  have hp : ContDiffAt ℝ ∞ (fun x : ℝ => x ^ (-s)) x :=
    Real.contDiffAt_rpow_const_of_ne hx0.ne'
  have hp' : ContDiffAt ℝ ∞ (fun x : ℝ => (1 - x) ^ (-s)) x :=
    (Real.contDiffAt_rpow_const_of_ne (show 1 - x ≠ 0 by linarith)).comp x
      (contDiffAt_const.sub contDiffAt_id)
  have h := (((hp.add hp').add hQ).add hQ' |>.sub (contDiffAt_const (c := 2 / (1 - s)))).div_const 2
  apply h.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds (show x ∈ Ioo 0 1 from ⟨hx0, hx1⟩)] with y hy
  dsimp only [Pi.add_apply, Pi.sub_apply, Function.comp_def]
  have heq := hurwitzZetaEven_re_euler s hs0 hs1 y hy.1 hy.2
  linarith

/-- Smoothness off the integers (Lemma 2.1). -/
theorem contDiffOn_hurwitzZetaEven_re (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    ContDiffOn ℝ ∞ (fun x : ℝ => (HurwitzZeta.hurwitzZetaEven (x : UnitAddCircle) (s : ℂ)).re)
      {x : ℝ | (x : UnitAddCircle) ≠ 0} := by
  intro x hx
  have hx0 : 0 < Int.fract x := by
    apply lt_of_le_of_ne (Int.fract_nonneg x)
    intro h
    apply hx
    have heq := AddCircle.coe_fract x
    rw [← h, AddCircle.coe_zero] at heq
    exact heq.symm
  have haff : ContDiffAt ℝ ∞ (fun t : ℝ => t - (⌊x⌋ : ℝ)) x :=
    contDiffAt_id.sub contDiffAt_const
  have h := contDiffAt_hurwitzZetaEven_re_of_mem_Ioo s hs0 hs1 (Int.fract x) hx0 (Int.fract_lt_one x)
  rw [Int.fract] at h
  have h := h.comp x haff
  dsimp only [Function.comp_def] at h
  have heq : (fun t : ℝ => (HurwitzZeta.hurwitzZetaEven ((t - (⌊x⌋ : ℝ) : ℝ) : UnitAddCircle) (s : ℂ)).re) =
      (fun t : ℝ => (HurwitzZeta.hurwitzZetaEven (t : UnitAddCircle) (s : ℂ)).re) := by
    funext t
    have hzero : (((⌊x⌋ : ℤ) : ℝ) : UnitAddCircle) = 0 := by
      apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr
      exact ⟨⌊x⌋, by simp⟩
    simp [hzero]
  rw [heq] at h
  exact h.contDiffWithinAt

lemma summable_eulerTermC (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1)
    (w : ℂ) (hw : -(1 / 2 : ℝ) < w.re) : Summable (eulerTermC s w) := by
  have hs : Summable (fun n : ℕ => (s + s * 2 ^ (s + 1) * ‖w‖) * ((n : ℝ) + 1) ^ (-s - 1)) := by
    apply Summable.mul_left
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr (show -s - 1 < -1 by linarith))
  exact hs.of_norm_bounded (fun n => norm_eulerTermC_le s hs0 hs1 ‖w‖ (norm_nonneg _) w hw le_rfl n)

lemma tendsto_nat_add_cpow_zero (s : ℝ) (hs : 0 < s) (w : ℂ) :
    Tendsto (fun n : ℕ => ((n : ℂ) + 1 + w) ^ (-(s : ℂ))) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp only [← ofReal_neg, norm_cpow_real]
  apply (tendsto_rpow_neg_atTop hs).comp
  apply tendsto_atTop_mono (fun n : ℕ => Complex.re_le_norm ((n : ℂ) + 1 + w))
  simp only [add_re, natCast_re, one_re]
  exact tendsto_atTop_add_const_right _ _ (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)

lemma tsum_eulerTermC_add_one (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1)
    (w : ℂ) (hw : -(1 / 2 : ℝ) < w.re) :
    (∑' n, eulerTermC s (w + 1) n) - (∑' n, eulerTermC s w n) =
      -((1 : ℂ) + w) ^ (-(s : ℂ)) := by
  have hw1 : -(1 / 2 : ℝ) < (w + 1).re := by simp only [add_re, one_re]; linarith
  have hsum := ((summable_eulerTermC s hs0 hs1 (w + 1) hw1).hasSum.sub
    (summable_eulerTermC s hs0 hs1 w hw).hasSum).tendsto_sum_nat
  have hfin (M : ℕ) : (∑ n ∈ Finset.range M, (eulerTermC s (w + 1) n - eulerTermC s w n)) =
      ((M : ℂ) + 1 + w) ^ (-(s : ℂ)) - (1 + w) ^ (-(s : ℂ)) := by
    have h := Finset.sum_range_sub (fun n : ℕ => ((n : ℂ) + 1 + w) ^ (-(s : ℂ))) M
    simp only [Nat.cast_zero, zero_add] at h
    rw [← h]
    apply Finset.sum_congr rfl
    intro n hn
    simp only [eulerTermC, Nat.cast_add, Nat.cast_one]
    rw [show (n : ℂ) + 1 + (w + 1) = (n : ℂ) + 1 + 1 + w by ring]
    ring
  simp only [hfin] at hsum
  have hzero := (tendsto_nat_add_cpow_zero s hs0 w).sub_const ((1 + w) ^ (-(s : ℂ)))
  simp only [zero_sub] at hzero
  exact tendsto_nhds_unique hsum hzero

lemma euler_remainder_add_one (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1)
    (x : ℝ) (hx : -(1 / 2 : ℝ) < x) :
    (∑' n, eulerTermC s ((x + 1 : ℝ) : ℂ) n).re - (∑' n, eulerTermC s (x : ℂ) n).re =
      -(x + 1) ^ (-s) := by
  have h := congrArg Complex.re (tsum_eulerTermC_add_one s hs0 hs1 (x : ℂ) hx)
  have hp : ((1 : ℂ) + (x : ℂ)) ^ (-(s : ℂ)) = (((x + 1) ^ (-s) : ℝ) : ℂ) := by
    rw [ofReal_cpow (by linarith : 0 ≤ x + 1) (-s)]
    push_cast
    rw [add_comm]
  rw [hp] at h
  simpa only [ofReal_add, ofReal_one, sub_re, neg_re, ofReal_re] using h

/-- The singular part of the project kernel has a smooth remainder across zero
(Lemma 2.1). -/
theorem exists_smooth_hurwitzZetaEven_re_remainder (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    ∃ h : ℝ → ℝ, ContDiffOn ℝ ∞ h (Ioo (-(1 / 2)) (1 / 2)) ∧
      ∀ x ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2), x ≠ 0 →
        h x = 2 * (HurwitzZeta.hurwitzZetaEven (x : UnitAddCircle) (s : ℂ)).re - |x| ^ (-s) := by
  let Q : ℝ → ℝ := fun x => (∑' n, eulerTermC s (x : ℂ) n).re
  let h : ℝ → ℝ := fun x => Q x + Q (-x) - 2 / (1 - s)
  have hsmooth : ContDiffOn ℝ ∞ h (Ioo (-(1 / 2)) (1 / 2)) := by
    intro x hx
    exact (((contDiffAt_euler_remainder s hs0 hs1 x hx.1).add
      ((contDiffAt_euler_remainder s hs0 hs1 (-x) (by linarith [hx.2])).comp x
        contDiffAt_id.neg)).sub contDiffAt_const).contDiffWithinAt
  have hpos (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1 / 2) :
      h x = 2 * (HurwitzZeta.hurwitzZetaEven (x : UnitAddCircle) (s : ℂ)).re - |x| ^ (-s) := by
    have heq := hurwitzZetaEven_re_euler s hs0 hs1 x hx0 (by linarith)
    have hrec := euler_remainder_add_one s hs0 hs1 (-x) (by linarith)
    rw [show -x + 1 = 1 - x by ring] at hrec
    rw [abs_of_pos hx0]
    dsimp only [h, Q]
    linarith
  refine ⟨h, hsmooth, ?_⟩
  intro x hx hx0
  rcases lt_or_gt_of_ne hx0 with hneg | hposx
  · have heq := hpos (-x) (by linarith) (by linarith [hx.1])
    have hsym : h (-x) = h x := by dsimp [h]; simp only [neg_neg]; ring
    rw [hsym] at heq
    simpa only [AddCircle.coe_neg, HurwitzZeta.hurwitzZetaEven_neg, abs_neg] using heq
  · exact hpos x hposx hx.2

/-- The project kernel is bounded below uniformly in the circle variable
(Lemma 2.1). -/
theorem hurwitzZetaEven_re_bounded_below (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    ∃ B : ℝ, ∀ x : ℝ, (x : UnitAddCircle) ≠ 0 →
      B ≤ 2 * (HurwitzZeta.hurwitzZetaEven (x : UnitAddCircle) (s : ℂ)).re := by
  let Q : ℝ → ℝ := fun x => (∑' n, eulerTermC s (x : ℂ) n).re
  have hQ : ContinuousOn Q (Icc 0 1) := by
    have h := continuous_re.comp_continuousOn (continuousOn_tsum_eulerTerm s hs0 hs1)
    change ContinuousOn Q (Icc 0 1) at h
    exact h
  obtain ⟨B, hB⟩ := isCompact_Icc.bddBelow_image hQ
  refine ⟨2 * B - 2 / (1 - s), ?_⟩
  intro x hx
  have hx0 : 0 < Int.fract x := by
    apply lt_of_le_of_ne (Int.fract_nonneg x)
    intro h
    apply hx
    have heq := AddCircle.coe_fract x
    rw [← h, AddCircle.coe_zero] at heq
    exact heq.symm
  have hx1 := Int.fract_lt_one x
  have heq := hurwitzZetaEven_re_euler s hs0 hs1 (Int.fract x) hx0 hx1
  rw [AddCircle.coe_fract] at heq
  have hB1 : B ≤ Q (Int.fract x) := hB ⟨Int.fract x, ⟨hx0.le, hx1.le⟩, rfl⟩
  have hB2 : B ≤ Q (1 - Int.fract x) := hB ⟨1 - Int.fract x, ⟨by linarith, by linarith⟩, rfl⟩
  have hp : 0 ≤ (Int.fract x) ^ (-s) := Real.rpow_nonneg hx0.le _
  have hp' : 0 ≤ (1 - Int.fract x) ^ (-s) := Real.rpow_nonneg (by linarith) _
  dsimp only [Q] at hB1 hB2
  linarith

/-- The project kernel tends to positive infinity at the collision
(Lemma 2.1). -/
theorem tendsto_hurwitzZetaEven_re_at_zero (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    Tendsto (fun x : ℝ => 2 * (HurwitzZeta.hurwitzZetaEven (x : UnitAddCircle) (s : ℂ)).re)
      (𝓝[≠] 0) atTop := by
  obtain ⟨h, hCD, heq⟩ := exists_smooth_hurwitzZetaEven_re_remainder s hs0 hs1
  have hmem : Ioo (-(1 / 2 : ℝ)) (1 / 2) ∈ 𝓝 (0 : ℝ) :=
    isOpen_Ioo.mem_nhds ⟨by norm_num, by norm_num⟩
  have hlim : Tendsto h (𝓝[≠] 0) (𝓝 (h 0)) :=
    ((hCD.contDiffAt hmem).continuousAt.tendsto).mono_left nhdsWithin_le_nhds
  have hpow : Tendsto (fun x : ℝ => |x| ^ (-s)) (𝓝[≠] 0) atTop :=
    (tendsto_rpow_neg_nhdsGT_zero (neg_lt_zero.mpr hs0)).comp tendsto_abs_nhdsNE_zero
  apply (hpow.atTop_add hlim).congr'
  have hmem' : ∀ᶠ x : ℝ in 𝓝[≠] 0, x ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2) :=
    nhdsWithin_le_nhds hmem
  filter_upwards [hmem', self_mem_nhdsWithin] with x hx hx0
  have h := heq x hx hx0
  linarith

end Riesz1
