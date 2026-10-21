/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.LoopIBPLimit
public import Riesz1.HelfferSjostrand.IntegrationByPartsConsequences
public import Riesz1.HelfferSjostrand.NeumannOperator

/-!
# The field potential lies in the Neumann graph

Proposition 5.5: the field potential `Φ = Φ_{ψ,a}`
belongs to the scalar Neumann domain of the quotient Gibbs measure, with operator value the
`L²` class of `𝓛Φ`.

The proof approximates `Φ` by the smooth collision cutoffs `χ_h Φ`. Their Langevin expressions
are `L²`-convergent to `𝓛Φ`, and the Sobolev lifts converge in the Hilbert norm. The variational
graph is closed (`isClosed_hsNeumannGraph`), so the limit lies in the graph.

* `integral_rieszProb_liftPoint` transfers integrals on the quotient to the Gibbs law.
* `exists_gibbs_strip_real_le` and `exists_gibbs_weighted_strip_le` bound the collision strip.
* `exists_cutoff_sub_sobolev_bound` and `exists_cutoff_langevin_error_bound` are the pointwise
  estimates of the cutoff errors.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace Riesz1

variable {N : ℕ+}

/-- The Gibbs law is a finite measure. -/
instance isFiniteMeasure_gibbsMeasure (P : Parameters) (N : ℕ+) :
    IsFiniteMeasure (gibbsMeasure P N) := by
  have := (modelWellDefined P N).2.2
  infer_instance

/-- Integrals of a function of the lifted point against the quotient Gibbs law are integrals of
the same function of the ordered real lift against the Gibbs law. -/
theorem integral_rieszProb_liftPoint (P : Parameters) (N : ℕ+) (G : HsEuclidean N → ℝ) :
    ∫ y, G (hsLiftPoint N y) ∂(rieszProb P N : Measure (HsConfiguration N)) =
      ∫ X, G (WithLp.toLp 2 X.val) ∂gibbsMeasure P N := by
  rw [integral_rieszProb P N (F := fun y => G (hsLiftPoint N y))]
  simp only [hsLiftPoint_configurationMap]

/-- The collision strip at scale `h` has Gibbs mass at most a multiple of `h ^ 10`. -/
theorem exists_gibbs_strip_real_le (P : Parameters) (hPL : External.PrekopaLeindler) (N : ℕ+) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : ℝ, 0 < h →
      (gibbsMeasure P N).real {X : Configuration N | ∃ j : Fin (N : ℕ), gap X (j : ℕ) ≤ 2 * h * N}
        ≤ C * h ^ 10 := by
  obtain ⟨C, hC, hstrip⟩ := exists_gibbs_strip_le P hPL (p := 10) (by norm_num) N
  refine ⟨C * (2 * (N : ℝ)) ^ 10, by positivity, fun h hh => ?_⟩
  have hu : 0 < 2 * h * (N : ℝ) := by
    have : (0 : ℝ) < N := by exact_mod_cast N.pos
    positivity
  have hm := hstrip hu
  have hreal : (gibbsMeasure P N).real
      {X : Configuration N | ∃ j : Fin (N : ℕ), gap X (j : ℕ) ≤ 2 * h * N} ≤
        C * (2 * h * (N : ℝ)) ^ (10 : ℝ) :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) hm
  have hpow : (2 * h * (N : ℝ)) ^ (10 : ℝ) = (2 * (N : ℝ)) ^ 10 * h ^ 10 := by
    rw [show (10 : ℝ) = ((10 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    ring
  rw [hpow] at hreal
  calc _ ≤ C * ((2 * (N : ℝ)) ^ 10 * h ^ 10) := hreal
    _ = C * (2 * (N : ℝ)) ^ 10 * h ^ 10 := by ring

/-- The weight `(1 + Σ gap^{-r})²` is square integrable under the Gibbs law. -/
theorem memLp_two_weight (P : Parameters) (hPL : External.PrekopaLeindler) (N : ℕ+) {r : ℝ}
    (hr : 0 < r) :
    MemLp (fun X : Configuration N => (1 + gapPowerSum r X) ^ 2) 2 (gibbsMeasure P N) := by
  have hm : Measurable (fun X : Configuration N => (1 + gapPowerSum r X) ^ 2) :=
    (measurable_const.add (measurable_gapPowerSum r)).pow_const 2
  rw [memLp_two_iff_integrable_sq hm.aestronglyMeasurable]
  have hr4 : 0 < r * ((4 : ℕ) : ℝ) := by positivity
  have hI : Integrable (fun X : Configuration N => gapPowerSum (r * ((4 : ℕ) : ℝ)) X)
      (gibbsMeasure P N) :=
    integrable_gapPowerSum P hPL hr4 N
  have hdom : Integrable (fun X : Configuration N =>
      8 + 8 * (N : ℝ) ^ 4 * gapPowerSum (r * ((4 : ℕ) : ℝ)) X) (gibbsMeasure P N) :=
    (integrable_const _).add (hI.const_mul _)
  refine hdom.mono' (hm.pow_const 2).aestronglyMeasurable (Filter.Eventually.of_forall fun X => ?_)
  have hpow : gapPowerSum r X ^ 4 ≤ (N : ℝ) ^ 4 * gapPowerSum (r * ((4 : ℕ) : ℝ)) X := by
    have h := gapPowerSum_rpow_le X (r := r) (p := ((4 : ℕ) : ℝ)) (by positivity)
    rwa [Real.rpow_natCast, Real.rpow_natCast] at h
  have hg0 : 0 ≤ gapPowerSum r X := gapPowerSum_nonneg r X
  have hpoly : (1 + gapPowerSum r X) ^ 4 ≤ 8 * (1 + gapPowerSum r X ^ 4) := by
    nlinarith [mul_nonneg (sq_nonneg (gapPowerSum r X - 1))
      (show (0 : ℝ) ≤ 7 * gapPowerSum r X ^ 2 + 10 * gapPowerSum r X + 7 by positivity)]
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h4 : ((1 + gapPowerSum r X) ^ 2) ^ 2 = (1 + gapPowerSum r X) ^ 4 := by ring
  rw [h4]
  nlinarith [hpoly, hpow]

/-- The collision strip carries a weighted mass of order `h ^ 5`, by Cauchy–Schwarz. -/
theorem exists_gibbs_weighted_strip_le (P : Parameters) (hPL : External.PrekopaLeindler)
    (N : ℕ+) {r : ℝ} (hr : 0 < r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : ℝ, 0 < h → h ≤ 1 →
      ∫ X, {X : Configuration N | ∃ j : Fin (N : ℕ), gap X (j : ℕ) ≤ 2 * h * N}.indicator
          (fun X : Configuration N => (1 + gapPowerSum r X) ^ 2) X ∂gibbsMeasure P N ≤ C * h ^ 5 := by
  obtain ⟨Cs, hCs0, hCs⟩ := exists_gibbs_strip_real_le P hPL N
  have hW := memLp_two_weight P hPL N hr
  have hW0 : ∀ X : Configuration N, 0 ≤ (1 + gapPowerSum r X) ^ 2 := fun X => sq_nonneg _
  set CW : ℝ := (∫ X, ((1 + gapPowerSum r X) ^ 2) ^ 2 ∂gibbsMeasure P N) ^ (1 / 2 : ℝ) with hCW
  have hCW0 : 0 ≤ CW := Real.rpow_nonneg (integral_nonneg fun X => sq_nonneg _) _
  refine ⟨CW * Real.sqrt Cs, mul_nonneg hCW0 (Real.sqrt_nonneg _), fun h hh h1 => ?_⟩
  have hcs := integral_indicator_le_sqrt_mul (gibbsMeasure P N)
    (measurableSet_strip (N := N) (2 * h * (N : ℝ))) hW0 hW
  have hmass := hCs h hh
  have hnn : (gibbsMeasure P N).real {X : Configuration N | ∃ j : Fin (N : ℕ),
      gap X (j : ℕ) ≤ 2 * h * N} ^ (1 / 2 : ℝ) ≤ Real.sqrt Cs * h ^ 5 := by
    have hnn0 : 0 ≤ (gibbsMeasure P N).real {X : Configuration N | ∃ j : Fin (N : ℕ),
        gap X (j : ℕ) ≤ 2 * h * N} := measureReal_nonneg
    calc _ ≤ (Cs * h ^ 10) ^ (1 / 2 : ℝ) := Real.rpow_le_rpow hnn0 hmass (by norm_num)
      _ = Real.sqrt (Cs * h ^ 10) := (Real.sqrt_eq_rpow _).symm
      _ = Real.sqrt Cs * h ^ 5 := by
          rw [Real.sqrt_mul hCs0, show h ^ 10 = (h ^ 5) ^ 2 by ring,
            Real.sqrt_sq (by positivity)]
  calc ∫ X, {X : Configuration N | ∃ j : Fin (N : ℕ), gap X (j : ℕ) ≤ 2 * h * N}.indicator
          (fun X : Configuration N => (1 + gapPowerSum r X) ^ 2) X ∂gibbsMeasure P N
      ≤ CW * (gibbsMeasure P N).real {X : Configuration N | ∃ j : Fin (N : ℕ),
          gap X (j : ℕ) ≤ 2 * h * N} ^ (1 / 2 : ℝ) := hcs
    _ ≤ CW * (Real.sqrt Cs * h ^ 5) := mul_le_mul_of_nonneg_left hnn hCW0
    _ = CW * Real.sqrt Cs * h ^ 5 := by ring

/-- The gradient of a function on the lift has squared norm the sum of its squared partial
derivatives. -/
theorem norm_gradient_sq_eq_sum (F : HsEuclidean N → ℝ) (x : HsEuclidean N) :
    ‖gradient F x‖ ^ 2 = ∑ k : Fin (N : ℕ), hsPartial F k x ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_gradient_eq_sum_hsPartial]
  simp only [sq]

/-- The partial derivative of a difference of differentiable functions. -/
theorem hsPartial_sub_fun {F G : HsEuclidean N → ℝ} {x : HsEuclidean N}
    (hF : DifferentiableAt ℝ F x) (hG : DifferentiableAt ℝ G x) (k : Fin (N : ℕ)) :
    hsPartial (fun y => F y - G y) k x = hsPartial F k x - hsPartial G k x := by
  unfold hsPartial
  rw [fderiv_fun_sub hF hG]
  rfl

/-- The cutoff minus one is bounded by the strip indicator. -/
theorem abs_cutoff_sub_one_le (N : ℕ+) {h : ℝ} (hh : 0 < h) (X : Configuration N) :
    |hsUnitGapCutoff N h (WithLp.toLp 2 X.val) - 1| ≤
      {X : Configuration N | ∃ j : Fin (N : ℕ), gap X (j : ℕ) ≤ 2 * h * N}.indicator
        (fun _ : Configuration N => (1 : ℝ)) X := by
  by_cases hX : ∃ j : Fin (N : ℕ), gap X (j : ℕ) ≤ 2 * h * N
  · rw [indicator_of_mem (show X ∈ {X : Configuration N | ∃ j : Fin (N : ℕ),
        gap X (j : ℕ) ≤ 2 * h * N} from hX)]
    have h0 := hsUnitGapCutoff_nonneg N h (WithLp.toLp 2 X.val)
    have h1 := hsUnitGapCutoff_le_one N h (WithLp.toLp 2 X.val)
    rw [abs_le]
    constructor <;> linarith
  · rw [indicator_of_notMem (show X ∉ {X : Configuration N | ∃ j : Fin (N : ℕ),
        gap X (j : ℕ) ≤ 2 * h * N} from hX)]
    have hx : ∀ j : Fin (N : ℕ), 2 * h ≤ hsUnitGap N j (WithLp.toLp 2 X.val) := by
      intro j
      rw [hsUnitGap_liftConfiguration, le_div_iff₀ (by exact_mod_cast N.pos : (0 : ℝ) < N)]
      exact (not_le.mp (not_exists.mp hX j)).le
    rw [hsUnitGapCutoff_eq_one_of_le hh hx, sub_self, abs_zero]


/-- The cutoff difference `χ_h Φ − Φ` has value and gradient controlled by the strip, with the
energy coefficient of order `h ^ -2`. -/
theorem exists_cutoff_sub_sobolev_bound {Φ : HsEuclidean N → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    (hΦ0 : ∃ M0 : ℝ, 0 ≤ M0 ∧ ∀ x : HsEuclidean N, |Φ x| ≤ M0)
    (hΦ1 : ∃ M1 : ℝ, 0 ≤ M1 ∧ ∀ (k : Fin (N : ℕ)) (x : HsEuclidean N), |hsPartial Φ k x| ≤ M1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ X : Configuration N,
      (hsUnitGapCutoff N h (WithLp.toLp 2 X.val) * Φ (WithLp.toLp 2 X.val) -
          Φ (WithLp.toLp 2 X.val)) ^ 2 +
        ‖gradient (fun y => hsUnitGapCutoff N h y * Φ y - Φ y) (WithLp.toLp 2 X.val)‖ ^ 2 ≤
      K * h⁻¹ ^ 2 * {X : Configuration N | ∃ j : Fin (N : ℕ), gap X (j : ℕ) ≤ 2 * h * N}.indicator
        (fun _ : Configuration N => (1 : ℝ)) X := by
  obtain ⟨M0, hM0, hM0b⟩ := hΦ0
  obtain ⟨M1, hM1, hM1b⟩ := hΦ1
  obtain ⟨C, hC0, hCb⟩ := exists_bound_deriv_loopStep
  set K1 : ℝ := 2 * C * N * M0 + M1 with hK1
  have hK1' : 0 ≤ K1 := by positivity
  refine ⟨M0 ^ 2 + N * K1 ^ 2, by positivity, fun h hh h1 X => ?_⟩
  set x : HsEuclidean N := WithLp.toLp 2 X.val with hx
  set I : ℝ := {X : Configuration N | ∃ j : Fin (N : ℕ), gap X (j : ℕ) ≤ 2 * h * N}.indicator
    (fun _ : Configuration N => (1 : ℝ)) X with hIdef
  have hI01 : I = 0 ∨ I = 1 := by
    rw [hIdef]
    unfold indicator
    split_ifs <;> simp
  have hI0 : 0 ≤ I := by
    rcases hI01 with h0 | h0 <;> simp [h0]
  have hI2 : I ^ 2 = I := by
    rcases hI01 with h0 | h0 <;> simp [h0]
  have hχ : |hsUnitGapCutoff N h x - 1| ≤ I := abs_cutoff_sub_one_le N hh X
  have hχd : ∀ k : Fin (N : ℕ), |hsPartial (hsUnitGapCutoff N h) k x| ≤ N * (2 * C * h⁻¹) * I :=
    fun k => abs_hsPartial_hsUnitGapCutoff_strip_le N (fun t => (hCb t).1) hh k X
  have hinv1 : 1 ≤ h⁻¹ := (one_le_inv₀ hh).mpr h1
  have hinv2 : 1 ≤ h⁻¹ ^ 2 := by nlinarith
  -- the value
  have hval : (hsUnitGapCutoff N h x * Φ x - Φ x) ^ 2 ≤ I * M0 ^ 2 := by
    have hfac : hsUnitGapCutoff N h x * Φ x - Φ x = (hsUnitGapCutoff N h x - 1) * Φ x := by ring
    have habs : |(hsUnitGapCutoff N h x - 1) * Φ x| ≤ I * M0 := by
      rw [abs_mul]
      exact mul_le_mul hχ (hM0b x) (abs_nonneg _) hI0
    calc (hsUnitGapCutoff N h x * Φ x - Φ x) ^ 2 = |(hsUnitGapCutoff N h x - 1) * Φ x| ^ 2 := by
          rw [sq_abs, hfac]
      _ ≤ (I * M0) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) habs 2
      _ = I * M0 ^ 2 := by rw [mul_pow, hI2]
  -- the partial derivatives of the difference
  have hdiffχ : DifferentiableAt ℝ (hsUnitGapCutoff N h) x :=
    (contDiff_hsUnitGapCutoff N h).differentiable (by simp) x
  have hdiffΦ : DifferentiableAt ℝ Φ x := hΦ.differentiable (by simp) x
  have hdiffP : DifferentiableAt ℝ (fun y => hsUnitGapCutoff N h y * Φ y) x := hdiffχ.mul hdiffΦ
  have hpart : ∀ k : Fin (N : ℕ), |hsPartial (fun y => hsUnitGapCutoff N h y * Φ y - Φ y) k x| ≤
      I * K1 * h⁻¹ := by
    intro k
    have hD : hsPartial (fun y => hsUnitGapCutoff N h y * Φ y - Φ y) k x =
        hsPartial (hsUnitGapCutoff N h) k x * Φ x + (hsUnitGapCutoff N h x - 1) * hsPartial Φ k x := by
      rw [hsPartial_sub_fun hdiffP hdiffΦ k, hsPartial_mul hdiffχ hdiffΦ k]
      ring
    have e1 : |hsPartial (hsUnitGapCutoff N h) k x * Φ x| ≤ N * (2 * C * h⁻¹) * I * M0 := by
      rw [abs_mul]
      exact mul_le_mul (hχd k) (hM0b x) (abs_nonneg _) (by positivity)
    have e2 : |(hsUnitGapCutoff N h x - 1) * hsPartial Φ k x| ≤ I * M1 := by
      rw [abs_mul]
      exact mul_le_mul hχ (hM1b k x) (abs_nonneg _) hI0
    have hIM1 : I * M1 ≤ I * M1 * h⁻¹ := le_mul_of_one_le_right (mul_nonneg hI0 hM1) hinv1
    rw [hD]
    calc |hsPartial (hsUnitGapCutoff N h) k x * Φ x + (hsUnitGapCutoff N h x - 1) * hsPartial Φ k x|
        ≤ |hsPartial (hsUnitGapCutoff N h) k x * Φ x| +
          |(hsUnitGapCutoff N h x - 1) * hsPartial Φ k x| := abs_add_le _ _
      _ ≤ N * (2 * C * h⁻¹) * I * M0 + I * M1 := add_le_add e1 e2
      _ ≤ I * K1 * h⁻¹ := by rw [hK1]; nlinarith [hIM1]
  -- the gradient
  have hgrad : ‖gradient (fun y => hsUnitGapCutoff N h y * Φ y - Φ y) x‖ ^ 2 ≤
      N * (I * K1 * h⁻¹) ^ 2 := by
    rw [norm_gradient_sq_eq_sum]
    calc ∑ k : Fin (N : ℕ), hsPartial (fun y => hsUnitGapCutoff N h y * Φ y - Φ y) k x ^ 2
        ≤ ∑ _k : Fin (N : ℕ), (I * K1 * h⁻¹) ^ 2 := by
          refine Finset.sum_le_sum fun k _ => ?_
          have := pow_le_pow_left₀ (abs_nonneg _) (hpart k) 2
          rwa [sq_abs] at this
      _ = N * (I * K1 * h⁻¹) ^ 2 := by simp
  have hIsq : (I * K1 * h⁻¹) ^ 2 = I * K1 ^ 2 * h⁻¹ ^ 2 := by
    rw [show (I * K1 * h⁻¹) ^ 2 = I ^ 2 * K1 ^ 2 * h⁻¹ ^ 2 by ring, hI2]
  have hIM0 : I * M0 ^ 2 ≤ I * M0 ^ 2 * h⁻¹ ^ 2 := le_mul_of_one_le_right (mul_nonneg hI0 (sq_nonneg _)) hinv2
  have hfinal : (M0 ^ 2 + N * K1 ^ 2) * h⁻¹ ^ 2 * I = I * M0 ^ 2 * h⁻¹ ^ 2 +
      N * (I * K1 ^ 2 * h⁻¹ ^ 2) := by ring
  rw [hfinal]
  rw [hIsq] at hgrad
  nlinarith [hval, hgrad, hIM0]


/-- The cutoff error of the Langevin expression, `(χ_h − 1) 𝓛Φ + error`, is bounded in square by
the weighted strip indicator, with coefficient of order `h ^ -4`. -/
theorem exists_cutoff_langevin_error_bound (P : Parameters)
    (ℓ : Ioc (0 : ℝ) 1) (a : ℝ) (ψ : LoopScaleProfile ℓ.val) (hψ : ContDiff ℝ ∞ ψ.val)
    (hmean : ∫ t in (0 : ℝ)..ℓ.val⁻¹, ψ.val t = 0) (N : ℕ+) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ X : Configuration N,
      ((hsUnitGapCutoff N h (WithLp.toLp 2 X.val) - 1) *
          loopLHS P N ℓ a ψ (WithLp.toLp 2 X.val) +
        loopError P N ℓ a ψ h (WithLp.toLp 2 X.val)) ^ 2 ≤
      K * h⁻¹ ^ 4 * {X : Configuration N | ∃ j : Fin (N : ℕ), gap X (j : ℕ) ≤ 2 * h * N}.indicator
        (fun X : Configuration N => (1 + gapPowerSum ((parametersExponent P).val + 1) X) ^ 2) X := by
  obtain ⟨KL, hKL, hLb⟩ := exists_abs_loopLHS_le P ℓ a ψ hψ N
  obtain ⟨KE, hKE, hEb⟩ := exists_loopError_bound P ℓ a ψ hψ hmean N
  refine ⟨(KL + 2 * KE) ^ 2, by positivity, fun h hh h1 X => ?_⟩
  set r : ℝ := (parametersExponent P).val + 1 with hr
  set g : ℝ := gapPowerSum r X with hg
  have hg0 : 0 ≤ g := gapPowerSum_nonneg r X
  set I : ℝ := {X : Configuration N | ∃ j : Fin (N : ℕ), gap X (j : ℕ) ≤ 2 * h * N}.indicator
    (fun _ : Configuration N => (1 : ℝ)) X with hIdef
  have hI01 : I = 0 ∨ I = 1 := by
    rw [hIdef]
    unfold indicator
    split_ifs <;> simp
  have hI0 : 0 ≤ I := by
    rcases hI01 with h0 | h0 <;> simp [h0]
  have hI2 : I ^ 2 = I := by
    rcases hI01 with h0 | h0 <;> simp [h0]
  have hJ : {X : Configuration N | ∃ j : Fin (N : ℕ), gap X (j : ℕ) ≤ 2 * h * N}.indicator
      (fun X : Configuration N => 1 + gapPowerSum r X) X = I * (1 + g) := by
    rw [hIdef]
    unfold indicator
    split_ifs <;> simp [hg]
  have hW : {X : Configuration N | ∃ j : Fin (N : ℕ), gap X (j : ℕ) ≤ 2 * h * N}.indicator
      (fun X : Configuration N => (1 + gapPowerSum r X) ^ 2) X = I * (1 + g) ^ 2 := by
    rw [hIdef]
    unfold indicator
    split_ifs <;> simp [hg]
  have hχ : |hsUnitGapCutoff N h (WithLp.toLp 2 X.val) - 1| ≤ I := abs_cutoff_sub_one_le N hh X
  have hE := hEb h hh X
  rw [hJ] at hE
  have hL : |loopLHS P N ℓ a ψ (WithLp.toLp 2 X.val)| ≤ KL * (1 + g) := hLb X
  have hinv1 : 1 ≤ h⁻¹ := (one_le_inv₀ hh).mpr h1
  have hinv2 : 1 ≤ h⁻¹ ^ 2 := by nlinarith
  have hinv12 : h⁻¹ ≤ h⁻¹ ^ 2 := by nlinarith
  have hQ : 0 ≤ I * (1 + g) := mul_nonneg hI0 (by linarith)
  set G : ℝ := (hsUnitGapCutoff N h (WithLp.toLp 2 X.val) - 1) *
      loopLHS P N ℓ a ψ (WithLp.toLp 2 X.val) +
    loopError P N ℓ a ψ h (WithLp.toLp 2 X.val) with hGdef
  have hc1 : |(hsUnitGapCutoff N h (WithLp.toLp 2 X.val) - 1) *
      loopLHS P N ℓ a ψ (WithLp.toLp 2 X.val)| ≤ I * (KL * (1 + g)) := by
    rw [abs_mul]
    exact mul_le_mul hχ hL (abs_nonneg _) hI0
  have hc2 : |loopError P N ℓ a ψ h (WithLp.toLp 2 X.val)| ≤
      KE * (h⁻¹ + h⁻¹ ^ 2) * (I * (1 + g)) := hE
  have hbound : |G| ≤ (KL + 2 * KE) * h⁻¹ ^ 2 * (I * (1 + g)) := by
    have hsplit : |G| ≤ I * (KL * (1 + g)) + KE * (h⁻¹ + h⁻¹ ^ 2) * (I * (1 + g)) :=
      (abs_add_le _ _).trans (add_le_add hc1 hc2)
    have hd1 : 0 ≤ KL * (h⁻¹ ^ 2 - 1) * (I * (1 + g)) :=
      mul_nonneg (mul_nonneg hKL (by linarith)) hQ
    have hd2 : 0 ≤ KE * (h⁻¹ ^ 2 - h⁻¹) * (I * (1 + g)) :=
      mul_nonneg (mul_nonneg hKE (by linarith)) hQ
    nlinarith [hsplit, hd1, hd2]
  have hsq : G ^ 2 ≤ ((KL + 2 * KE) * h⁻¹ ^ 2 * (I * (1 + g))) ^ 2 := by
    rw [← sq_abs G]
    exact pow_le_pow_left₀ (abs_nonneg _) hbound 2
  have hid : ((KL + 2 * KE) * h⁻¹ ^ 2 * (I * (1 + g))) ^ 2 =
      (KL + 2 * KE) ^ 2 * h⁻¹ ^ 4 * (I * (1 + g) ^ 2) := by
    linear_combination ((KL + 2 * KE) ^ 2 * h⁻¹ ^ 4 * (1 + g) ^ 2) * hI2
  rw [hW]
  rw [hid] at hsq
  exact hsq

/-- The first lift of the field potential's Langevin expression is a bounded `L²` function on the
quotient. -/
theorem memLp_loopLHS (P : Parameters) (hPL : External.PrekopaLeindler) (ℓ : Ioc (0 : ℝ) 1)
    (a : ℝ) (ψ : LoopScaleProfile ℓ.val) (hψ : ContDiff ℝ ∞ ψ.val) (N : ℕ+) :
    MemLp (fun x : HsConfiguration N => loopLHS P N ℓ a ψ (hsLiftPoint N x)) 2
      (rieszProb P N : Measure (HsConfiguration N)) := by
  have hcomp : (fun x : HsConfiguration N => loopLHS P N ℓ a ψ (hsLiftPoint N x)) ∘
      hsConfigurationMap N = fun X : Configuration N => loopLHS P N ℓ a ψ (WithLp.toLp 2 X.val) := by
    funext X
    simp only [Function.comp_apply, hsLiftPoint_configurationMap]
  rw [rieszProb_eq_map, (measurableEmbedding_hsConfigurationMap N).memLp_map_measure_iff, hcomp]
  have hr : 0 < (parametersExponent P).val + 1 := by
    have := (parametersExponent P).property.1
    linarith
  obtain ⟨K, hK, hb⟩ := exists_abs_loopLHS_le P ℓ a ψ hψ N
  have hgL : MemLp (fun X : Configuration N => K * (1 + gapPowerSum ((parametersExponent P).val + 1) X))
      2 (gibbsMeasure P N) :=
    ((memLp_const (1 : ℝ)).add (memLp_two_gapPowerSum P hPL N hr)).const_mul K
  refine MemLp.of_le hgL (continuous_loopLHS_config P ℓ a ψ hψ).aestronglyMeasurable
    (Filter.Eventually.of_forall fun X => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hK (by
    linarith [gapPowerSum_nonneg ((parametersExponent P).val + 1) X]))]
  exact hb X

/-- The field potential is smooth and periodic on the closed chamber. -/
theorem hsSmoothOnClosure_loopHS (ℓ : Ioc (0 : ℝ) 1) (a : ℝ) (ψ : LoopScaleProfile ℓ.val)
    (hψ : ContDiff ℝ ∞ ψ.val) (hmean : ∫ t in (0 : ℝ)..ℓ.val⁻¹, ψ.val t = 0) (N : ℕ+) :
    HsSmoothOnClosure N (loopHS ℓ a ψ N) :=
  ⟨fun k x => loopHS_periodic ℓ a ψ hψ hmean N k x, univ, isOpen_univ, subset_univ _,
    (contDiff_loopHS ℓ a ψ hψ N).contDiffOn⟩

/-- Squared `L²` norm of the class of a square-integrable function. -/
theorem norm_sq_toLp_eq {α : Type*} [MeasurableSpace α] (μ : Measure α) {φ : α → ℝ}
    (hφ : MemLp φ 2 μ) : ‖hφ.toLp φ‖ ^ 2 = ∫ x, φ x ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hφ.coeFn_toLp] with x hx
  rw [hx]
  simp [sq]

/-- The Sobolev norm of a smooth core element is the Gibbs integral of its value and gradient
at the ordered lift. -/
theorem norm_sq_hsSobolevOfSmooth_eq (P : Parameters) (N : ℕ+) (g : hsSmoothCore N) :
    ‖hsSobolevOfSmooth (rieszProb P N : Measure (HsConfiguration N)) g‖ ^ 2 =
      ∫ X, (g.val (WithLp.toLp 2 X.val)) ^ 2 + ‖gradient g.val (WithLp.toLp 2 X.val)‖ ^ 2
        ∂gibbsMeasure P N := by
  rw [hsSobolev_norm_sq_eq_integral]
  refine Eq.trans ?_ (integral_rieszProb_liftPoint P N
    (fun x => g.val x ^ 2 + ‖gradient g.val x‖ ^ 2))
  apply integral_congr_ae
  have hv : (hsSobolevValue (rieszProb P N : Measure (HsConfiguration N))
      (hsSobolevOfSmooth (rieszProb P N : Measure (HsConfiguration N)) g) :
        HsConfiguration N → ℝ) =ᵐ[(rieszProb P N : Measure (HsConfiguration N))]
      hsSmoothValue g.val :=
    (g.property.memLp_value _).coeFn_toLp
  have hg : (hsSobolevGradient (rieszProb P N : Measure (HsConfiguration N))
      (hsSobolevOfSmooth (rieszProb P N : Measure (HsConfiguration N)) g) :
        HsConfiguration N → HsEuclidean N) =ᵐ[(rieszProb P N : Measure (HsConfiguration N))]
      hsSmoothGradient g :=
    (g.property.memLp_gradient _).coeFn_toLp
  filter_upwards [hv, hg] with y hy1 hy2
  rw [hy1, hy2]
  rfl


/-- The field potential bounds: a uniform bound on the field and on its first partial derivatives. -/
theorem exists_bounds_loopHS (ℓ : Ioc (0 : ℝ) 1) (a : ℝ) (ψ : LoopScaleProfile ℓ.val)
    (hψ : ContDiff ℝ ∞ ψ.val) (hmean : ∫ t in (0 : ℝ)..ℓ.val⁻¹, ψ.val t = 0) (N : ℕ+) :
    (∃ M0 : ℝ, 0 ≤ M0 ∧ ∀ x : HsEuclidean N, |loopHS ℓ a ψ N x| ≤ M0) ∧
      ∃ M1 : ℝ, 0 ≤ M1 ∧ ∀ (k : Fin (N : ℕ)) (x : HsEuclidean N), |hsPartial (loopHS ℓ a ψ N) k x| ≤ M1 := by
  refine ⟨exists_abs_loopHS_le ℓ a ψ hψ hmean N, ?_⟩
  obtain ⟨Mψ, hMψ0, hMψb⟩ := exists_abs_le_of_continuous_periodic (inv_pos.mpr ℓ.property.1)
    hψ.continuous ψ.property.1
  refine ⟨|a| * ℓ.val * Mψ, mul_nonneg (mul_nonneg (abs_nonneg a) ℓ.property.1.le) hMψ0,
    fun k x => ?_⟩
  rw [hsPartial_loopHS ℓ a ψ hψ N k x]
  exact abs_partialDeriv_loopScalePotential_le ℓ a ψ hMψb k _

/-- The field potential as a smooth core element. -/
def loopCore (ℓ : Ioc (0 : ℝ) 1) (a : ℝ) (ψ : LoopScaleProfile ℓ.val) (hψ : ContDiff ℝ ∞ ψ.val)
    (hmean : ∫ t in (0 : ℝ)..ℓ.val⁻¹, ψ.val t = 0) (N : ℕ+) : hsSmoothCore N :=
  ⟨loopHS ℓ a ψ N, hsSmoothOnClosure_loopHS ℓ a ψ hψ hmean N⟩

/-- The cutoff `χ_h Φ` of the field potential at scale `h`, as a smooth core element. Its
smoothness and periodicity hold for every real scale. -/
theorem hsSmoothOnClosure_cutoff (ℓ : Ioc (0 : ℝ) 1) (a : ℝ) (ψ : LoopScaleProfile ℓ.val)
    (hψ : ContDiff ℝ ∞ ψ.val) (hmean : ∫ t in (0 : ℝ)..ℓ.val⁻¹, ψ.val t = 0) (N : ℕ+) (h : ℝ) :
    HsSmoothOnClosure N (fun x => hsUnitGapCutoff N h x * loopHS ℓ a ψ N x) :=
  ⟨fun k x => by simp only [hsUnitGapCutoff_translate, loopHS_periodic ℓ a ψ hψ hmean N k x], univ,
    isOpen_univ, subset_univ _, ((contDiff_hsUnitGapCutoff N h).mul
      (contDiff_loopHS ℓ a ψ hψ N)).contDiffOn⟩

/-- The cutoff smooth core `χ_h Φ` at scale `h`. -/
def cutoffCore (ℓ : Ioc (0 : ℝ) 1) (a : ℝ) (ψ : LoopScaleProfile ℓ.val) (hψ : ContDiff ℝ ∞ ψ.val)
    (hmean : ∫ t in (0 : ℝ)..ℓ.val⁻¹, ψ.val t = 0) (N : ℕ+) (h : ℝ) : hsSmoothCore N :=
  ⟨fun x => hsUnitGapCutoff N h x * loopHS ℓ a ψ N x, hsSmoothOnClosure_cutoff ℓ a ψ hψ hmean N h⟩

/-- The cutoff test function `χ_h Φ` at a positive scale `h`. -/
def cutoffTest (ℓ : Ioc (0 : ℝ) 1) (a : ℝ) (ψ : LoopScaleProfile ℓ.val) (hψ : ContDiff ℝ ∞ ψ.val)
    (hmean : ∫ t in (0 : ℝ)..ℓ.val⁻¹, ψ.val t = 0) (N : ℕ+) {h : ℝ} (hh : 0 < h) :
    HsTestFunction N :=
  hsUnitGapCutoffTest hh (loopHS ℓ a ψ N) (contDiff_loopHS ℓ a ψ hψ N)
    (fun k x => loopHS_periodic ℓ a ψ hψ hmean N k x)

/-- The Langevin expression of the cutoff test at a quotient point, split into the cutoff times
`𝓛Φ` and the error. -/
theorem hsLangevin_cutoffTest_eq (P : Parameters) (N : ℕ+) (ℓ : Ioc (0 : ℝ) 1) (a : ℝ)
    (ψ : LoopScaleProfile ℓ.val) (hψ : ContDiff ℝ ∞ ψ.val)
    (hmean : ∫ t in (0 : ℝ)..ℓ.val⁻¹, ψ.val t = 0) {h : ℝ} (hh : 0 < h)
    (y : HsConfiguration N) :
    hsLangevin (rieszPairs P N) (cutoffTest ℓ a ψ hψ hmean N hh) y =
      hsUnitGapCutoff N h (hsLiftPoint N y) * loopLHS P N ℓ a ψ (hsLiftPoint N y) +
        loopError P N ℓ a ψ h (hsLiftPoint N y) := by
  rw [hsLangevin_eq_of_symm (rieszPairs P N) _ y ((hsConfigurationEquiv N).symm y) rfl]
  unfold hsLangevinLift
  exact langevin_cutoff_eq P N ℓ a ψ hψ h (hsLiftPoint N y)

/-- Sobolev convergence of the cutoffs `χ_h Φ` to `Φ`, along any sequence of scales tending to
zero from above. -/
theorem tendsto_cutoff_sobolev (P : Parameters) (hPL : External.PrekopaLeindler)
    (ℓ : Ioc (0 : ℝ) 1) (a : ℝ) (ψ : LoopScaleProfile ℓ.val) (hψ : ContDiff ℝ ∞ ψ.val)
    (hmean : ∫ t in (0 : ℝ)..ℓ.val⁻¹, ψ.val t = 0) (N : ℕ+) (h : ℕ → ℝ)
    (hpos : ∀ n, 0 < h n) (hle : ∀ n, h n ≤ 1) (hlim : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun n => hsSobolevOfSmooth (rieszProb P N : Measure (HsConfiguration N))
        (cutoffCore ℓ a ψ hψ hmean N (h n))) atTop
      (𝓝 (hsSobolevOfSmooth (rieszProb P N : Measure (HsConfiguration N))
        (loopCore ℓ a ψ hψ hmean N))) := by
  obtain ⟨⟨M0, hM0, hM0b⟩, ⟨M1, hM1, hM1b⟩⟩ := exists_bounds_loopHS ℓ a ψ hψ hmean N
  obtain ⟨K, hK, hKb⟩ := exists_cutoff_sub_sobolev_bound (contDiff_loopHS ℓ a ψ hψ N)
    ⟨M0, hM0, hM0b⟩ ⟨M1, hM1, hM1b⟩
  obtain ⟨Cs, hCs0, hCs⟩ := exists_gibbs_strip_real_le P hPL N
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hbound : ∀ n, ‖hsSobolevOfSmooth (rieszProb P N : Measure (HsConfiguration N))
        (cutoffCore ℓ a ψ hψ hmean N (h n)) -
      hsSobolevOfSmooth (rieszProb P N : Measure (HsConfiguration N))
        (loopCore ℓ a ψ hψ hmean N)‖ ≤ Real.sqrt (K * Cs * h n ^ 8) := by
    intro n
    rw [← map_sub]
    have hsq : ‖hsSobolevOfSmooth (rieszProb P N : Measure (HsConfiguration N))
        (cutoffCore ℓ a ψ hψ hmean N (h n) - loopCore ℓ a ψ hψ hmean N)‖ ^ 2 ≤
        K * Cs * h n ^ 8 := by
      rw [norm_sq_hsSobolevOfSmooth_eq P N]
      have hS : MeasurableSet {X : Configuration N | ∃ j : Fin (N : ℕ),
          gap X (j : ℕ) ≤ 2 * h n * N} := measurableSet_strip (N := N) (2 * h n * (N : ℝ))
      have hint : Integrable (fun X : Configuration N =>
          K * (h n)⁻¹ ^ 2 * {X : Configuration N | ∃ j : Fin (N : ℕ),
            gap X (j : ℕ) ≤ 2 * h n * N}.indicator (fun _ : Configuration N => (1 : ℝ)) X)
          (gibbsMeasure P N) :=
        (((integrable_const (1 : ℝ)).indicator hS).const_mul _)
      calc _ ≤ ∫ X : Configuration N, K * (h n)⁻¹ ^ 2 * {X : Configuration N |
              ∃ j : Fin (N : ℕ), gap X (j : ℕ) ≤ 2 * h n * N}.indicator
                (fun _ : Configuration N => (1 : ℝ)) X ∂gibbsMeasure P N :=
            integral_mono_of_nonneg (Filter.Eventually.of_forall fun X => by positivity) hint
              (Filter.Eventually.of_forall fun X => hKb (h n) (hpos n) (hle n) X)
        _ = K * (h n)⁻¹ ^ 2 * (gibbsMeasure P N).real {X : Configuration N |
              ∃ j : Fin (N : ℕ), gap X (j : ℕ) ≤ 2 * h n * N} := by
            rw [integral_const_mul]
            congr 1
            exact integral_indicator_one hS
        _ ≤ K * (h n)⁻¹ ^ 2 * (Cs * h n ^ 10) :=
            mul_le_mul_of_nonneg_left (hCs (h n) (hpos n)) (by positivity)
        _ = K * Cs * h n ^ 8 := by
            have hn : h n ≠ 0 := (hpos n).ne'
            field_simp
    calc ‖hsSobolevOfSmooth (rieszProb P N : Measure (HsConfiguration N))
          (cutoffCore ℓ a ψ hψ hmean N (h n) - loopCore ℓ a ψ hψ hmean N)‖
        = |‖hsSobolevOfSmooth (rieszProb P N : Measure (HsConfiguration N))
          (cutoffCore ℓ a ψ hψ hmean N (h n) - loopCore ℓ a ψ hψ hmean N)‖| :=
          (abs_of_nonneg (norm_nonneg _)).symm
      _ ≤ Real.sqrt (K * Cs * h n ^ 8) := Real.abs_le_sqrt hsq
  refine squeeze_zero (fun n => norm_nonneg _) hbound ?_
  have h1 : Tendsto (fun n => K * Cs * h n ^ 8) atTop (𝓝 (K * Cs * 0 ^ 8)) :=
    (hlim.pow 8).const_mul _
  have h2 := (Real.continuous_sqrt.tendsto _).comp h1
  simpa [Function.comp_def] using h2

/-- The `L²` convergence of the Langevin expressions of the cutoffs to `𝓛Φ`, along any sequence of
scales tending to zero from above. -/
theorem tendsto_cutoff_langevin (P : Parameters) (hPL : External.PrekopaLeindler)
    (ℓ : Ioc (0 : ℝ) 1) (a : ℝ) (ψ : LoopScaleProfile ℓ.val) (hψ : ContDiff ℝ ∞ ψ.val)
    (hmean : ∫ t in (0 : ℝ)..ℓ.val⁻¹, ψ.val t = 0) (N : ℕ+) (hN : 2 ≤ (N : ℕ))
    (h : ℕ → ℝ) (hpos : ∀ n, 0 < h n) (hle : ∀ n, h n ≤ 1) (hlim : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun n => (memLp_hsLangevin hN (rieszPairs P N)
        (cutoffTest ℓ a ψ hψ hmean N (hpos n)) (rieszProb P N : Measure (HsConfiguration N))).toLp
        (hsLangevin (rieszPairs P N) (cutoffTest ℓ a ψ hψ hmean N (hpos n)))) atTop
      (𝓝 ((memLp_loopLHS P hPL ℓ a ψ hψ N).toLp
        (fun x : HsConfiguration N => loopLHS P N ℓ a ψ (hsLiftPoint N x)))) := by
  obtain ⟨Kc, hKc, hKcb⟩ := exists_cutoff_langevin_error_bound P ℓ a ψ hψ hmean N
  have hr : 0 < (parametersExponent P).val + 1 := by
    have := (parametersExponent P).property.1
    linarith
  obtain ⟨Cw, hCw0, hCwb⟩ := exists_gibbs_weighted_strip_le P hPL N hr
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hbound : ∀ n, ‖(memLp_hsLangevin hN (rieszPairs P N)
        (cutoffTest ℓ a ψ hψ hmean N (hpos n)) (rieszProb P N : Measure (HsConfiguration N))).toLp
        (hsLangevin (rieszPairs P N) (cutoffTest ℓ a ψ hψ hmean N (hpos n))) -
      (memLp_loopLHS P hPL ℓ a ψ hψ N).toLp
        (fun x : HsConfiguration N => loopLHS P N ℓ a ψ (hsLiftPoint N x))‖ ≤
      Real.sqrt (Kc * Cw * h n) := by
    intro n
    have hf := memLp_hsLangevin hN (rieszPairs P N)
      (cutoffTest ℓ a ψ hψ hmean N (hpos n)) (rieszProb P N : Measure (HsConfiguration N))
    have hg := memLp_loopLHS P hPL ℓ a ψ hψ N
    have hsq : ‖hf.toLp (hsLangevin (rieszPairs P N) (cutoffTest ℓ a ψ hψ hmean N (hpos n))) -
        hg.toLp (fun x : HsConfiguration N => loopLHS P N ℓ a ψ (hsLiftPoint N x))‖ ^ 2 ≤
        Kc * Cw * h n := by
      rw [← MemLp.toLp_sub hf hg, norm_sq_toLp_eq _ (hf.sub hg)]
      have hS : MeasurableSet {X : Configuration N | ∃ j : Fin (N : ℕ),
          gap X (j : ℕ) ≤ 2 * h n * N} := measurableSet_strip (N := N) (2 * h n * (N : ℝ))
      have hW : Integrable (fun X : Configuration N =>
          Kc * (h n)⁻¹ ^ 4 * {X : Configuration N | ∃ j : Fin (N : ℕ),
            gap X (j : ℕ) ≤ 2 * h n * N}.indicator
              (fun X : Configuration N => (1 + gapPowerSum ((parametersExponent P).val + 1) X) ^ 2)
              X) (gibbsMeasure P N) :=
        (((memLp_two_weight P hPL N hr).integrable one_le_two).indicator hS).const_mul _
      calc ∫ y, (hsLangevin (rieszPairs P N) (cutoffTest ℓ a ψ hψ hmean N (hpos n)) -
            (fun x : HsConfiguration N => loopLHS P N ℓ a ψ (hsLiftPoint N x))) y ^ 2
              ∂(rieszProb P N : Measure (HsConfiguration N))
          = ∫ y, ((hsUnitGapCutoff N (h n) (hsLiftPoint N y) - 1) *
              loopLHS P N ℓ a ψ (hsLiftPoint N y) +
              loopError P N ℓ a ψ (h n) (hsLiftPoint N y)) ^ 2
              ∂(rieszProb P N : Measure (HsConfiguration N)) := by
            apply integral_congr_ae
            refine Filter.Eventually.of_forall fun y => ?_
            simp only [Pi.sub_apply]
            rw [hsLangevin_cutoffTest_eq P N ℓ a ψ hψ hmean (hpos n) y]
            ring
        _ = ∫ X : Configuration N, ((hsUnitGapCutoff N (h n) (WithLp.toLp 2 X.val) - 1) *
              loopLHS P N ℓ a ψ (WithLp.toLp 2 X.val) +
              loopError P N ℓ a ψ (h n) (WithLp.toLp 2 X.val)) ^ 2 ∂gibbsMeasure P N :=
            integral_rieszProb_liftPoint P N (fun x => ((hsUnitGapCutoff N (h n) x - 1) *
              loopLHS P N ℓ a ψ x + loopError P N ℓ a ψ (h n) x) ^ 2)
        _ ≤ ∫ X : Configuration N, Kc * (h n)⁻¹ ^ 4 * {X : Configuration N | ∃ j : Fin (N : ℕ),
              gap X (j : ℕ) ≤ 2 * h n * N}.indicator
                (fun X : Configuration N => (1 + gapPowerSum ((parametersExponent P).val + 1) X) ^ 2)
                X ∂gibbsMeasure P N :=
            integral_mono_of_nonneg (Filter.Eventually.of_forall fun X => sq_nonneg _) hW
              (Filter.Eventually.of_forall fun X => hKcb (h n) (hpos n) (hle n) X)
        _ = Kc * (h n)⁻¹ ^ 4 * ∫ X : Configuration N, {X : Configuration N | ∃ j : Fin (N : ℕ),
              gap X (j : ℕ) ≤ 2 * h n * N}.indicator
                (fun X : Configuration N => (1 + gapPowerSum ((parametersExponent P).val + 1) X) ^ 2)
                X ∂gibbsMeasure P N :=
            integral_const_mul _ _
        _ ≤ Kc * (h n)⁻¹ ^ 4 * (Cw * h n ^ 5) :=
            mul_le_mul_of_nonneg_left (hCwb (h n) (hpos n) (hle n)) (by positivity)
        _ = Kc * Cw * h n := by
            have hn : h n ≠ 0 := (hpos n).ne'
            field_simp
    calc ‖hf.toLp (hsLangevin (rieszPairs P N) (cutoffTest ℓ a ψ hψ hmean N (hpos n))) -
          hg.toLp (fun x : HsConfiguration N => loopLHS P N ℓ a ψ (hsLiftPoint N x))‖
        = |‖hf.toLp (hsLangevin (rieszPairs P N) (cutoffTest ℓ a ψ hψ hmean N (hpos n))) -
          hg.toLp (fun x : HsConfiguration N => loopLHS P N ℓ a ψ (hsLiftPoint N x))‖| :=
          (abs_of_nonneg (norm_nonneg _)).symm
      _ ≤ Real.sqrt (Kc * Cw * h n) := Real.abs_le_sqrt hsq
  refine squeeze_zero (fun n => norm_nonneg _) hbound ?_
  have h1 : Tendsto (fun n => Kc * Cw * h n) atTop (𝓝 (Kc * Cw * 0)) := hlim.const_mul _
  have h2 := (Real.continuous_sqrt.tendsto _).comp h1
  simpa [Function.comp_def] using h2

/-- **Graph membership.** The field potential `Φ = Φ_{ψ,a}` lies in the variational Neumann graph
of the quotient Gibbs measure, paired with the `L²` class of `𝓛Φ`. -/
theorem loopPhi_mem_neumannGraph (P : Parameters) (hPL : External.PrekopaLeindler) (N : ℕ+)
    (hN : 2 ≤ (N : ℕ)) (ℓ : Ioc (0 : ℝ) 1) (a : ℝ) (ψ : LoopScaleProfile ℓ.val)
    (hψ : ContDiff ℝ ∞ ψ.val) (hmean : ∫ t in (0 : ℝ)..ℓ.val⁻¹, ψ.val t = 0) :
    (hsSobolevOfSmooth (rieszProb P N : Measure (HsConfiguration N))
        (loopCore ℓ a ψ hψ hmean N),
      (memLp_loopLHS P hPL ℓ a ψ hψ N).toLp
        (fun x : HsConfiguration N => loopLHS P N ℓ a ψ (hsLiftPoint N x))) ∈
      hsNeumannGraph (rieszProb P N : Measure (HsConfiguration N)) := by
  have hc := hsRieszPairPotentials_curvature_pos N P.property.1 (parametersExponent P)
  have hpos : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  have hle : ∀ n : ℕ, 1 / ((n : ℝ) + 1) ≤ 1 := fun n => by
    rw [div_le_one (by positivity)]
    linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  have hlim : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hS := tendsto_cutoff_sobolev P hPL ℓ a ψ hψ hmean N (fun n : ℕ => 1 / ((n : ℝ) + 1))
    hpos hle hlim
  have hL := tendsto_cutoff_langevin P hPL ℓ a ψ hψ hmean N hN (fun n : ℕ => 1 / ((n : ℝ) + 1))
    hpos hle hlim
  refine (isClosed_hsNeumannGraph _).mem_of_tendsto (hS.prodMk_nhds hL)
    (Filter.Eventually.of_forall fun n => ?_)
  exact hsLangevin_mem_neumannGraph hN (rieszPairs P N) hc
    (cutoffTest ℓ a ψ hψ hmean N (hpos n))

/-- **Domain and value.** The field potential `Φ = Φ_{ψ,a}` lies in the scalar Neumann domain of the
quotient Gibbs measure, and the Neumann operator at `Φ` is the `L²` class of `𝓛Φ` on the
quotient. -/
theorem loopPhi_hsNeumannOperator (P : Parameters) (hPL : External.PrekopaLeindler) (N : ℕ+)
    (hN : 2 ≤ (N : ℕ)) (ℓ : Ioc (0 : ℝ) 1) (a : ℝ) (ψ : LoopScaleProfile ℓ.val)
    (hψ : ContDiff ℝ ∞ ψ.val) (hmean : ∫ t in (0 : ℝ)..ℓ.val⁻¹, ψ.val t = 0) :
    ∃ hΦ : hsSobolevOfSmooth (rieszProb P N : Measure (HsConfiguration N))
        (loopCore ℓ a ψ hψ hmean N) ∈
          hsNeumannDomain (rieszProb P N : Measure (HsConfiguration N)),
      hsNeumannOperator (rieszPairs P N)
          (hsRieszPairPotentials_curvature_pos N P.property.1 (parametersExponent P)) ⟨_, hΦ⟩ =
        (memLp_loopLHS P hPL ℓ a ψ hψ N).toLp
          (fun x : HsConfiguration N => loopLHS P N ℓ a ψ (hsLiftPoint N x)) := by
  have hG := loopPhi_mem_neumannGraph P hPL N hN ℓ a ψ hψ hmean
  exact ⟨(hsNeumannDomain_iff _ _).mpr ⟨_, hG⟩, (hsNeumannOperator_eq_iff _ _ _ _).mpr hG⟩

end Riesz1

end
