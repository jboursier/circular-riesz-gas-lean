/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.HurwitzKernel.EulerIntegralFormula
public import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Analytic continuation of the Hurwitz zeta integral formula to `Re z > -1`

Lemma 2.1. For `x > 0` the function `z ↦ ζ(z, x)` is given on
`Re z > 0` by the integral formula of `Riesz1.EulerIntegralFormula`. The second-order integral
`zetaB2Int z x = ∫_0^∞ B_2(t) (t+x)^{-2-z} dt` converges absolutely on the whole half plane
`Re z > -1` and is holomorphic there, so the identity `ζ = zetaRhs` extends to `Re z > -1` by the
identity theorem. Here `zetaRhs z x` is the right-hand side of the continued formula.

The file proves: holomorphy of `zetaB2Int` in `z`, and the identity
`hurwitzZetaPos z x = zetaRhs z x` for `Re z > -1` and `z ≠ 1`.
-/

public section

open MeasureTheory Set Filter Topology Complex

namespace Riesz1

/-! ### Elementary bounds -/

/-- Integrability of `(t + x)^p` on `(0, ∞)` for real `p < -1` and `x > 0`. -/
lemma integrableOn_Ioi_add_rpow {x p : ℝ} (hx : 0 < x) (hp : p < -1) :
    IntegrableOn (fun t : ℝ => (t + x) ^ p) (Ioi 0) := by
  have h1 : IntegrableOn (fun u : ℝ => u ^ p) (Ioi x) := integrableOn_Ioi_rpow_of_lt hp hx
  have h2 : Integrable ((Ioi x).indicator fun u : ℝ => u ^ p) :=
    (integrable_indicator_iff measurableSet_Ioi).mpr h1
  have h3 := h2.comp_add_right x
  refine (h3.integrableOn).congr_fun ?_ measurableSet_Ioi
  intro t ht
  have hpos : x < t + x := by linarith [mem_Ioi.mp ht]
  simp [Set.indicator, hpos]

/-- Power bound: for `u > 0` and an exponent `e` between `lo` and `hi`, `u^e ≤ u^lo + u^hi`. -/
lemma rpow_le_rpow_add_rpow {u lo e hi : ℝ} (hu : 0 < u) (hlo : lo ≤ e) (hhi : e ≤ hi) :
    u ^ e ≤ u ^ lo + u ^ hi := by
  have hlo0 : 0 ≤ u ^ lo := Real.rpow_nonneg hu.le lo
  have hhi0 : 0 ≤ u ^ hi := Real.rpow_nonneg hu.le hi
  rcases le_total 1 u with h | h
  · have := Real.rpow_le_rpow_of_exponent_le h hhi
    linarith
  · have := Real.rpow_le_rpow_of_exponent_ge hu h hlo
    linarith

/-- `|log u| ≤ (u^ε + u^{-ε})/ε` for `u > 0` and `ε > 0`. -/
lemma abs_log_le_rpow_add {u ε : ℝ} (hu : 0 < u) (hε : 0 < ε) :
    |Real.log u| ≤ (u ^ ε + u ^ (-ε)) / ε := by
  have h1 : Real.log u ≤ u ^ ε / ε := Real.log_le_rpow_div hu.le hε
  have h2 : Real.log u⁻¹ ≤ (u⁻¹) ^ ε / ε := Real.log_le_rpow_div (inv_nonneg.mpr hu.le) hε
  have h3 : (u⁻¹) ^ ε = u ^ (-ε) := by
    rw [Real.inv_rpow hu.le, Real.rpow_neg hu.le]
  rw [Real.log_inv, h3] at h2
  have hp1 : 0 ≤ u ^ ε / ε := div_nonneg (Real.rpow_nonneg hu.le ε) hε.le
  have hp2 : 0 ≤ u ^ (-ε) / ε := div_nonneg (Real.rpow_nonneg hu.le _) hε.le
  rw [add_div, abs_le]
  constructor <;> linarith

/-! ### The second-order integral and the continued formula -/

/-- The second-order integral `∫_0^∞ B_2(t) (t + x)^{-2-z} dt` (proof of Lemma 2.1,
second Bernoulli function). It converges absolutely for `Re z > -1`. -/
@[expose] noncomputable def zetaB2Int (z : ℂ) (x : ℝ) : ℂ :=
  ∫ t in Ioi (0 : ℝ), (sawtoothB2 t : ℂ) * ((t : ℂ) + x) ^ (-(2 + z))

/-- The right-hand side of the integral formula for `ζ(z, x)`, with the second-order integral.
For `Re z > 0` it equals `hurwitzZetaPos z x` (see `hurwitzZetaPos_eq_zetaRhs`). -/
@[expose] noncomputable def zetaRhs (z : ℂ) (x : ℝ) : ℂ :=
  (x : ℂ) ^ (1 - z) / (z - 1) + (x : ℂ) ^ (-z) / 2 + z * (x : ℂ) ^ (-(1 + z)) / 12 -
    z * (1 + z) * zetaB2Int z x

/-- The integral formula in second-order form, for `Re z > 0` and `z ≠ 1`. -/
theorem hurwitzZetaPos_eq_zetaRhs {x : ℝ} (hx : 0 < x) {z : ℂ} (hz : 0 < z.re) (hz1 : z ≠ 1) :
    hurwitzZetaPos z x = zetaRhs z x := by
  have hJ : ∫ t in Ioi (0 : ℝ), ((sawtoothB1 t : ℝ) : ℂ) / ((t : ℂ) + x) ^ (1 + z) =
      -((x : ℂ) ^ (-(1 + z))) / 12 + (1 + z) * zetaB2Int z x := by
    unfold zetaB2Int
    rw [← integral_sawtoothB1_eq_B2 hx hz]
    congr 1
    funext t
    rw [Complex.cpow_neg, div_eq_mul_inv]
  rw [hurwitzZetaPos_eq_integral hx hz hz1, hJ]
  unfold zetaRhs
  ring

/-! ### Holomorphy of the second-order integral in `z` -/

/-- The `z`-derivative integrand of `(t + x)^{-2-z}`. -/
lemma hasDerivAt_zetaB2_integrand (x t : ℝ) (htx : 0 < t + x) (z : ℂ) :
    HasDerivAt (fun w : ℂ => (sawtoothB2 t : ℂ) * ((t : ℂ) + x) ^ (-(2 + w)))
      ((sawtoothB2 t : ℂ) * (((t : ℂ) + x) ^ (-(2 + z)) * Complex.log ((t : ℂ) + x) * (-1))) z := by
  have hc : ((t : ℂ) + x) ≠ 0 := by
    intro h
    have : ((t + x : ℝ) : ℂ) = 0 := by push_cast; exact h
    exact htx.ne' (by exact_mod_cast this)
  have hf : HasDerivAt (fun w : ℂ => -(2 + w)) (-1) z := by
    exact ((hasDerivAt_id z).const_add (2 : ℂ)).neg
  have h := (hf.const_cpow (c := (t : ℂ) + x) (Or.inl hc)).const_mul (sawtoothB2 t : ℂ)
  exact h


/-- Measurability of the integrand of `zetaB2Int`, in `t`. -/
lemma measurable_zetaB2_integrand (x : ℝ) (w : ℂ) :
    Measurable (fun t : ℝ => (sawtoothB2 t : ℂ) * ((t : ℂ) + x) ^ (-(2 + w))) := by
  apply Measurable.mul
  · exact Complex.continuous_ofReal.measurable.comp sawtoothB2_measurable
  · exact Measurable.pow_const (by fun_prop) _

/-- Measurability of the `z`-derivative integrand, in `t`. -/
lemma measurable_zetaB2_deriv_integrand (x : ℝ) (w : ℂ) :
    Measurable (fun t : ℝ => (sawtoothB2 t : ℂ) *
      (((t : ℂ) + x) ^ (-(2 + w)) * Complex.log ((t : ℂ) + x) * (-1))) := by
  apply Measurable.mul
  · exact Complex.continuous_ofReal.measurable.comp sawtoothB2_measurable
  · apply Measurable.mul _ measurable_const
    apply Measurable.mul
    · exact Measurable.pow_const (by fun_prop) _
    · exact Complex.measurable_log.comp (by fun_prop)

/-- The second-order integral is differentiable in `z` on `Re z > -1`: dominated differentiation
on a ball around `z0`, with the dominating function built from the four powers
`(t + x)^{-(2+a) ± ε}`, `(t + x)^{-(2+b) ± ε}` where `a < Re z < b` on the ball. -/
lemma differentiableAt_zetaB2Int {x : ℝ} (hx : 0 < x) {z0 : ℂ} (hz0 : -1 < z0.re) :
    DifferentiableAt ℂ (fun z => zetaB2Int z x) z0 := by
  set r := z0.re with hr
  set δ : ℝ := (r + 1) / 2 with hδdef
  set a : ℝ := (r - 1) / 2 with hadef
  set b : ℝ := r + δ with hbdef
  set ε : ℝ := (1 + a) / 2 with hεdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  have hεpos : 0 < ε := by rw [hεdef, hadef]; linarith
  have hab : a ≤ b := by rw [hbdef, hδdef, hadef]; linarith
  have he1 : -(2 + a) + ε < -1 := by rw [hεdef, hadef]; linarith
  have he2 : -(2 + a) - ε < -1 := by linarith
  have he3 : -(2 + b) + ε < -1 := by linarith
  have he4 : -(2 + b) - ε < -1 := by linarith
  set G : ℝ → ℝ := fun t => (1 / (12 * ε)) *
    ((t + x) ^ (-(2 + a) + ε) + (t + x) ^ (-(2 + a) - ε) +
      ((t + x) ^ (-(2 + b) + ε) + (t + x) ^ (-(2 + b) - ε))) with hGdef
  have hG_int : IntegrableOn G (Ioi 0) := by
    have h := ((integrableOn_Ioi_add_rpow hx he1).add (integrableOn_Ioi_add_rpow hx he2)).add
      ((integrableOn_Ioi_add_rpow hx he3).add (integrableOn_Ioi_add_rpow hx he4))
    exact h.const_mul (1 / (12 * ε))
  have hball : Metric.ball z0 δ ∈ 𝓝 z0 := Metric.ball_mem_nhds z0 hδ
  have hre : ∀ z ∈ Metric.ball z0 δ, a ≤ z.re ∧ z.re ≤ b := by
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz
    have h := Complex.abs_re_le_norm (z - z0)
    rw [Complex.sub_re] at h
    have h2 : |z.re - r| < δ := lt_of_le_of_lt h hz
    rw [abs_lt] at h2
    constructor
    · linarith [h2.1]
    · linarith [h2.2]
  have hbound : ∀ z ∈ Metric.ball z0 δ, ∀ t : ℝ, 0 < t →
      ‖(sawtoothB2 t : ℂ) * (((t : ℂ) + x) ^ (-(2 + z)) * Complex.log ((t : ℂ) + x) * (-1))‖ ≤
        G t := by
    intro z hz t ht
    have hu : 0 < t + x := by linarith
    have hre' := hre z hz
    have hcplx : ((t : ℂ) + x) = (((t + x : ℝ)) : ℂ) := by push_cast; ring
    have hnorm_pow : ‖((t : ℂ) + x) ^ (-(2 + z))‖ = (t + x) ^ (-(2 + z.re)) := by
      rw [hcplx, Complex.norm_cpow_eq_rpow_re_of_pos hu]
      congr 1
    have hnorm_log : ‖Complex.log ((t : ℂ) + x)‖ = |Real.log (t + x)| := by
      rw [hcplx, ← Complex.ofReal_log hu.le, Complex.norm_real, Real.norm_eq_abs]
    have hB2 : ‖(sawtoothB2 t : ℂ)‖ ≤ 1 / 12 := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact abs_sawtoothB2_le t
    have hP : (t + x) ^ (-(2 + z.re)) ≤ (t + x) ^ (-(2 + b)) + (t + x) ^ (-(2 + a)) :=
      rpow_le_rpow_add_rpow hu (by linarith [hre'.2]) (by linarith [hre'.1])
    have hQ : |Real.log (t + x)| ≤ ((t + x) ^ ε + (t + x) ^ (-ε)) / ε :=
      abs_log_le_rpow_add hu hεpos
    have hQnn : 0 ≤ |Real.log (t + x)| := abs_nonneg _
    calc ‖(sawtoothB2 t : ℂ) * (((t : ℂ) + x) ^ (-(2 + z)) * Complex.log ((t : ℂ) + x) * (-1))‖
        = ‖(sawtoothB2 t : ℂ)‖ * (‖((t : ℂ) + x) ^ (-(2 + z))‖ * ‖Complex.log ((t : ℂ) + x)‖) := by
          rw [norm_mul, norm_mul, norm_mul, norm_neg, norm_one, mul_one]
      _ ≤ (1 / 12) * ((t + x) ^ (-(2 + z.re)) * |Real.log (t + x)|) := by
          rw [hnorm_pow, hnorm_log]
          exact mul_le_mul hB2 (le_refl _) (by positivity) (by norm_num)
      _ ≤ (1 / 12) * (((t + x) ^ (-(2 + b)) + (t + x) ^ (-(2 + a))) *
            (((t + x) ^ ε + (t + x) ^ (-ε)) / ε)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact mul_le_mul hP hQ hQnn (by positivity)
      _ = G t := by
          simp only [hGdef]
          simp only [Real.rpow_add hu, Real.rpow_sub hu, Real.rpow_neg hu.le]
          field_simp
          ring
  have hre0 : (-(2 + z0)).re < -1 := by simp; linarith
  have hF_meas : ∀ᶠ w in 𝓝 z0, AEStronglyMeasurable
      (fun t : ℝ => (sawtoothB2 t : ℂ) * ((t : ℂ) + x) ^ (-(2 + w)))
      (volume.restrict (Ioi (0 : ℝ))) :=
    Eventually.of_forall (fun w => (measurable_zetaB2_integrand x w).aestronglyMeasurable)
  have hF_int : Integrable (fun t : ℝ => (sawtoothB2 t : ℂ) * ((t : ℂ) + x) ^ (-(2 + z0)))
      (volume.restrict (Ioi (0 : ℝ))) := by
    refine Integrable.bdd_mul (c := 1 / 12) (integrableOn_Ioi_add_cpow hx hre0) ?_ ?_
    · exact (Complex.continuous_ofReal.measurable.comp sawtoothB2_measurable).aestronglyMeasurable
    · exact ae_of_all _ (fun t => by
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact abs_sawtoothB2_le t)
  have hF'_meas : AEStronglyMeasurable
      (fun t : ℝ => (sawtoothB2 t : ℂ) *
        (((t : ℂ) + x) ^ (-(2 + z0)) * Complex.log ((t : ℂ) + x) * (-1)))
      (volume.restrict (Ioi (0 : ℝ))) :=
    (measurable_zetaB2_deriv_integrand x z0).aestronglyMeasurable
  have h_bound : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), ∀ w ∈ Metric.ball z0 δ,
      ‖(sawtoothB2 t : ℂ) * (((t : ℂ) + x) ^ (-(2 + w)) * Complex.log ((t : ℂ) + x) * (-1))‖ ≤
        G t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    intro w hw
    exact hbound w hw t ht
  have h_diff : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), ∀ w ∈ Metric.ball z0 δ,
      HasDerivAt (fun w : ℂ => (sawtoothB2 t : ℂ) * ((t : ℂ) + x) ^ (-(2 + w)))
        ((sawtoothB2 t : ℂ) * (((t : ℂ) + x) ^ (-(2 + w)) * Complex.log ((t : ℂ) + x) * (-1))) w := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    intro w _
    exact hasDerivAt_zetaB2_integrand x t (by linarith [mem_Ioi.mp ht]) w
  have hdiff := hasDerivAt_integral_of_dominated_loc_of_deriv_le hball hF_meas hF_int hF'_meas
    h_bound hG_int h_diff
  exact hdiff.2.differentiableAt

/-! ### Holomorphy of the two sides and the identity theorem -/

/-- `ζ(z, x)` is holomorphic in `z` away from the pole `z = 1`. -/
lemma differentiableAt_hurwitzZetaPos {x : ℝ} (hx : 0 < x) {w : ℂ} (hw : w ≠ 1) :
    DifferentiableAt ℂ (fun w : ℂ => hurwitzZetaPos w x) w := by
  unfold hurwitzZetaPos
  have hpos : 0 < x - (⌈x⌉₊ : ℝ) + 1 := by
    have := Nat.ceil_lt_add_one hx.le
    linarith
  refine DifferentiableAt.sub (HurwitzZeta.differentiableAt_hurwitzZeta _ hw) ?_
  apply DifferentiableAt.fun_sum
  intro j _
  have hne : ((x - (⌈x⌉₊ : ℝ) + 1 + j : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < x - (⌈x⌉₊ : ℝ) + 1 + j := by
      have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      linarith
    exact_mod_cast this.ne'
  exact (differentiableAt_id.neg).const_cpow (Or.inl hne)

/-- The continued right-hand side is holomorphic in `z` on `Re z > -1` away from `z = 1`. -/
lemma differentiableAt_zetaRhs {x : ℝ} (hx : 0 < x) {w : ℂ} (hw0 : -1 < w.re) (hw1 : w ≠ 1) :
    DifferentiableAt ℂ (fun w : ℂ => zetaRhs w x) w := by
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hd1 : DifferentiableAt ℂ (fun w : ℂ => (x : ℂ) ^ (1 - w)) w :=
    ((differentiableAt_const (1 : ℂ)).sub differentiableAt_id).const_cpow (Or.inl hx0)
  have hd2 : DifferentiableAt ℂ (fun w : ℂ => (x : ℂ) ^ (-w)) w :=
    (differentiableAt_id.neg).const_cpow (Or.inl hx0)
  have hd3 : DifferentiableAt ℂ (fun w : ℂ => (x : ℂ) ^ (-(1 + w))) w :=
    (((differentiableAt_const (1 : ℂ)).add differentiableAt_id).neg).const_cpow (Or.inl hx0)
  have hd4 : DifferentiableAt ℂ (fun w : ℂ => zetaB2Int w x) w := differentiableAt_zetaB2Int hx hw0
  have hw1' : w - 1 ≠ 0 := sub_ne_zero.mpr hw1
  unfold zetaRhs
  refine ((((hd1.div ((differentiableAt_id).sub (differentiableAt_const _)) hw1').add
    (hd2.div_const 2)).add ((differentiableAt_id.mul hd3).div_const 12)).sub
    ((((differentiableAt_id.mul ((differentiableAt_const _).add differentiableAt_id)))).mul hd4))

/-- The set `{Re z > -1, z ≠ 1}` is open. -/
lemma isOpen_halfPlane_compl_one :
    IsOpen {w : ℂ | -1 < w.re ∧ w ≠ 1} :=
  (isOpen_lt continuous_const continuous_re).inter isOpen_compl_singleton

/-- The identity `ζ(z, x) = zetaRhs z x` on `Re z > -1`, `z ≠ 1`, by the identity theorem
(Lemma 2.1, analytic continuation to `Re z > -1`). -/
theorem hurwitzZetaPos_eq_zetaRhs_of_re_gt {x : ℝ} (hx : 0 < x) {z0 : ℂ} (hz0 : -1 < z0.re)
    (hz1 : z0 ≠ 1) : hurwitzZetaPos z0 x = zetaRhs z0 x := by
  set c : ℝ := min (-1 / 2 : ℝ) z0.re with hcdef
  have hc1 : -1 < c := lt_min (by norm_num) hz0
  have hcz : c ≤ z0.re := min_le_right _ _
  have hc2 : c ≤ -1 / 2 := min_le_left _ _
  let f : ℂ → ℂ := fun w => ((max c w.re : ℝ) : ℂ) + (w.im : ℂ) * Complex.I
  have hf : Continuous f := by dsimp [f]; fun_prop
  let U : Set ℂ := f '' {1}ᶜ
  let V : Set ℂ := {w : ℂ | -1 < w.re ∧ w ≠ 1}
  have hU : IsPreconnected U :=
    (isConnected_compl_singleton_of_one_lt_rank (by simp) (1 : ℂ)).isPreconnected.image f
      hf.continuousOn
  have hmem : ∀ w ∈ U, -1 < w.re ∧ w ≠ 1 := by
    intro w hw
    obtain ⟨v, hv, rfl⟩ := hw
    constructor
    · simp only [f, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero]
      linarith [le_max_left c v.re]
    · intro heq
      have hre := congrArg Complex.re heq
      have him := congrArg Complex.im heq
      simp only [f, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, Complex.one_re] at hre
      simp only [f, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_re, Complex.I_im, mul_zero, zero_add, mul_one, add_zero, Complex.one_im] at him
      rcases le_total c v.re with h | h
      · rw [max_eq_right h] at hre
        have hv1 : v.re = 1 := by norm_num at hre; linarith
        exact hv (Complex.ext (by simp [hv1]) (by simpa using him))
      · rw [max_eq_left h] at hre
        linarith
  have hzU : z0 ∈ U := by
    refine ⟨z0, hz1, ?_⟩
    apply Complex.ext <;> simp [f, max_eq_right hcz]
  have h2U : (2 : ℂ) ∈ U := by
    refine ⟨2, by norm_num, ?_⟩
    apply Complex.ext <;> simp [f, max_eq_right (by linarith : c ≤ 2)]
  have hUV : U ⊆ V := fun w hw => hmem w hw
  have hV : IsOpen V := isOpen_halfPlane_compl_one
  have hleftD : DifferentiableOn ℂ (fun w : ℂ => hurwitzZetaPos w x) V := fun w hw =>
    (differentiableAt_hurwitzZetaPos hx hw.2).differentiableWithinAt
  have hrightD : DifferentiableOn ℂ (fun w : ℂ => zetaRhs w x) V := fun w hw =>
    (differentiableAt_zetaRhs hx hw.1 hw.2).differentiableWithinAt
  have hleft := (hleftD.analyticOnNhd hV).mono hUV
  have hright := (hrightD.analyticOnNhd hV).mono hUV
  have hopen : IsOpen {w : ℂ | 0 < w.re ∧ w ≠ 1} :=
    (isOpen_lt continuous_const continuous_re).inter isOpen_compl_singleton
  have hev : (fun w : ℂ => hurwitzZetaPos w x) =ᶠ[𝓝 (2 : ℂ)] (fun w : ℂ => zetaRhs w x) := by
    refine Filter.eventually_of_mem (hopen.mem_nhds ⟨by norm_num, by norm_num⟩) ?_
    intro w hw
    exact hurwitzZetaPos_eq_zetaRhs hx hw.1 hw.2
  have hEq := hleft.eqOn_of_preconnected_of_eventuallyEq hright hU h2U hev
  exact hEq hzU

end Riesz1

end
