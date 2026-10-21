/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopMomentsChain
public import Riesz1.Auxiliary.LoopMomentsRooted
public import Riesz1.Variance.MicroLocalIndependence
public import Riesz1.Rigidity.InverseBlocks
public import Riesz1.Gibbs.UniformMarginals
public import Riesz1.ToMathlib.Moments.LpBounds
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Count moments of microscopic arcs

The moments part of Lemma 5.8, the claim `‖M_J‖_{L^p} ≤ C (1 + r)` for an arc `J` of
microscopic length `r ≤ N`.

The pointwise bound `(M_J - 1)_+^{q+1} ≤ r^q ∑_{i ∈ J} y_i^{-q}` is `loopCount_pow_le_sum`.
Its right side has expectation at most `r` times the inverse block moment, by rotation
averaging: the rotation of particle `i` is independent of its gap, and the rotated arc has
measure at most `r/N`, inside the closed ball of the same measure around the arc centre.
-/

@[expose] public section

noncomputable section

open MeasureTheory Finset Set ProbabilityTheory
open scoped ENNReal

attribute [local instance] Classical.propDecidable

namespace Riesz1

variable {N : ℕ+}

/-- The centre `x₀ = (a + r/2)/N` of the arc `microArc N a r`, on the unit circle. -/
def arcCentre (N : ℕ+) (a r : ℝ) : UnitAddCircle := (((a + r / 2) / (N : ℝ) : ℝ) : UnitAddCircle)

/-- The half length `ℓ = r/(2N)` of the arc `microArc N a r`, on the unit circle. -/
def arcRadius (N : ℕ+) (r : ℝ) : ℝ := r / (2 * (N : ℝ))

/-- A particle in the arc lies in the closed ball of the unit circle around the arc centre. -/
theorem cyclicLift_mem_closedBall_of_mem {a r : ℝ} (hN : (0 : ℝ) < N) (X : Configuration N)
    (i : Fin (N : ℕ)) (hi : loopPos X i ∈ microArc N a r) :
    (cyclicLift X (i : ℕ) : UnitAddCircle) ∈
      Metric.closedBall (arcCentre N a r) (arcRadius N r) := by
  obtain ⟨n, h1, h2⟩ := (mem_microArc_iff_lift a r X i).mp hi
  rw [cyclicLift_add_int_mul, cyclicLift_natCast] at h1 h2
  rw [cyclicLift_natCast]
  set t : ℝ := X.val i with ht
  set x0 : ℝ := (a + r / 2) / (N : ℝ) with hx0
  have hNx0 : (N : ℝ) * x0 = a + r / 2 := by
    rw [hx0]
    field_simp
  have hℓN : arcRadius N r * (N : ℝ) = r / 2 := by
    unfold arcRadius
    field_simp
  have hd : |t - x0 - (((-(n : ℤ)) : ℤ) : ℝ)| < arcRadius N r := by
    rw [abs_lt]
    constructor
    · refine lt_of_mul_lt_mul_left ?_ hN.le
      push_cast
      nlinarith
    · refine lt_of_mul_lt_mul_left ?_ hN.le
      push_cast
      nlinarith
  rw [Metric.mem_closedBall, dist_eq_norm, arcCentre, ← AddCircle.coe_sub, UnitAddCircle.norm_eq]
  exact ((round_le (t - x0) (-(n : ℤ))).trans_lt hd).le

/-- The closed ball of the arc has arclength `r/N`, for `0 < r ≤ N`. -/
theorem volume_closedBall_arc {a r : ℝ} (hr : 0 < r) (hrN : r ≤ N) :
    volume (Metric.closedBall (arcCentre N a r) (arcRadius N r)) = ENNReal.ofReal (r / (N : ℝ)) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  unfold arcCentre arcRadius
  rw [AddCircle.volume_closedBall 1]
  congr 1
  have h2 : 2 * (r / (2 * (N : ℝ))) = r / N := by field_simp
  rw [h2, min_eq_right]
  rw [div_le_one hN]
  exact hrN

/-- **Rotation averaging.** The rotation `cyclicLift X i` is independent of the block of particle
`i`, so the integral of a closed-ball indicator of the rotation against a function of the gap
is the volume of the ball times the integral of that function. -/
theorem lintegral_rotation_mul_closedBall (P : Parameters) (N : ℕ+) (i : ℤ) (x0 : UnitAddCircle)
    (ℓ : ℝ) (G : ℝ → ℝ≥0∞) (hG : Measurable G) :
    (∫⁻ X : Configuration N, (Metric.closedBall x0 ℓ).indicator 1 (cyclicLift X i : UnitAddCircle) *
      G (blockLength X i 1) ∂gibbsMeasure P N) =
      volume (Metric.closedBall x0 ℓ) * ∫⁻ X : Configuration N, G (blockLength X i 1)
        ∂gibbsMeasure P N := by
  have hF : Measurable ((Metric.closedBall x0 ℓ).indicator (1 : UnitAddCircle → ℝ≥0∞)) :=
    measurable_const.indicator measurableSet_closedBall
  have hI := (indepFun_cyclicLift_blockLength P N i i 1).comp hF hG
  have hcyc : Measurable (fun X : Configuration N => (cyclicLift X i : UnitAddCircle)) :=
    measurable_coe_circle.comp (measurable_cyclicLift i)
  have he := lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun''
    (hF.comp hcyc).aemeasurable ((hG.comp (measurable_blockLength i 1))).aemeasurable hI
  simp only [Function.comp_apply] at he
  rw [he]
  congr 1
  rw [← lintegral_indicator_one measurableSet_closedBall]
  refine (lintegral_map hF hcyc).symm.trans ?_
  rw [map_cyclicLift_gibbsMeasure P N i]

/-- The microscopic arc is open, hence measurable. -/
theorem measurableSet_microArc (N : ℕ+) (a r : ℝ) : MeasurableSet (microArc N a r) :=
  (QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo).measurableSet

/-- A negative integer power is a negative real power, on positive reals. -/
theorem zpow_neg_natCast_eq_rpow {x : ℝ} (q : ℕ) : x ^ (-(q : ℤ)) = x ^ (-(q : ℝ)) := by
  rw [← Real.rpow_intCast]
  congr 1
  push_cast
  ring

/-- **Expectation of the particle sum.** The sum over the particles of the arc of the inverse
gap powers has expectation at most `r` times a constant, uniformly in `N`, the arc and `hPL`. -/
theorem lintegral_sum_inv_pow_le (P : Parameters) {q : ℕ} (hq : 1 ≤ q) :
    ∃ D : ℝ, 0 < D ∧ ∀ (_hPL : External.PrekopaLeindler) (N : ℕ+) (a r : ℝ), 0 < r → r ≤ N →
      (∫⁻ X : Configuration N, ENNReal.ofReal (∑ i : Fin (N : ℕ),
        if loopPos X i ∈ microArc N a r then gap X (i : ℕ) ^ (-(q : ℤ)) else 0)
          ∂gibbsMeasure P N) ≤ ENNReal.ofReal (r * D) := by
  obtain ⟨C, hC, hblock⟩ := inverse_blocks_uniform P (p := (q : ℝ))
    (by exact_mod_cast hq)
  refine ⟨C, hC, fun hPL N a r hr hrN => ?_⟩
  have := (modelWellDefined P N).2.2
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  set G : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (t ^ (-(q : ℝ))) with hG_def
  have hGm : Measurable G := (measurable_id.pow_const _).ennreal_ofReal
  -- Each summand is dominated by the closed-ball indicator of the rotation, times `G` of the gap.
  have hterm : ∀ i : Fin (N : ℕ), ∀ X : Configuration N,
      ENNReal.ofReal (if loopPos X i ∈ microArc N a r then gap X (i : ℕ) ^ (-(q : ℤ)) else 0) ≤
        (Metric.closedBall (arcCentre N a r) (arcRadius N r)).indicator (1 : UnitAddCircle → ℝ≥0∞)
          (cyclicLift X ((i : ℕ) : ℤ) : UnitAddCircle) * G (blockLength X ((i : ℕ) : ℤ) 1) := by
    intro i X
    by_cases hm : loopPos X i ∈ microArc N a r
    · rw [ite_eq_left hm, Set.indicator_of_mem (cyclicLift_mem_closedBall_of_mem hN X i hm), Pi.one_apply,
        one_mul, hG_def, ← gap_eq_blockLength_one, zpow_neg_natCast_eq_rpow q]
    · rw [ite_eq_right hm, ENNReal.ofReal_zero]
      exact zero_le
  have hmeas_term : ∀ i : Fin (N : ℕ), Measurable (fun X : Configuration N =>
      ENNReal.ofReal (if loopPos X i ∈ microArc N a r then gap X (i : ℕ) ^ (-(q : ℤ)) else 0)) := by
    intro i
    refine Measurable.ennreal_ofReal (Measurable.ite ?_ ?_ measurable_const)
    · exact measurable_loopPos i (measurableSet_microArc N a r)
    · have hfun : (fun X : Configuration N => gap X (i : ℕ) ^ (-(q : ℤ))) =
          fun X => blockLength X ((i : ℕ) : ℤ) 1 ^ (-(q : ℝ)) := by
        funext X
        rw [gap_eq_blockLength_one, zpow_neg_natCast_eq_rpow q]
      rw [hfun]
      exact (measurable_blockLength _ _).pow_const _
  have hnn : ∀ (X : Configuration N) (i : Fin (N : ℕ)),
      0 ≤ (if loopPos X i ∈ microArc N a r then gap X (i : ℕ) ^ (-(q : ℤ)) else 0) := by
    intro X i
    split_ifs
    · exact zpow_nonneg (gap_pos X _).le _
    · exact le_rfl
  have hGi : ∀ i : Fin (N : ℕ), ∫⁻ X : Configuration N, G (blockLength X ((i : ℕ) : ℤ) 1)
      ∂gibbsMeasure P N ≤ ENNReal.ofReal C := by
    intro i
    obtain ⟨-, h⟩ := hblock hPL N ((i : ℕ) : ℤ) 1 one_pos
    simpa [hG_def] using h
  calc ∫⁻ X : Configuration N, ENNReal.ofReal (∑ i : Fin (N : ℕ),
        if loopPos X i ∈ microArc N a r then gap X (i : ℕ) ^ (-(q : ℤ)) else 0)
          ∂gibbsMeasure P N
      = ∫⁻ X : Configuration N, ∑ i : Fin (N : ℕ), ENNReal.ofReal
          (if loopPos X i ∈ microArc N a r then gap X (i : ℕ) ^ (-(q : ℤ)) else 0)
            ∂gibbsMeasure P N := by
        refine lintegral_congr (fun X => ?_)
        exact ENNReal.ofReal_sum_of_nonneg (fun i _ => hnn X i)
    _ = ∑ i : Fin (N : ℕ), ∫⁻ X : Configuration N, ENNReal.ofReal
          (if loopPos X i ∈ microArc N a r then gap X (i : ℕ) ^ (-(q : ℤ)) else 0)
            ∂gibbsMeasure P N := lintegral_finsetSum _ (fun i _ => hmeas_term i)
    _ ≤ ∑ i : Fin (N : ℕ), ∫⁻ X : Configuration N,
          (Metric.closedBall (arcCentre N a r) (arcRadius N r)).indicator (1 : UnitAddCircle → ℝ≥0∞)
            (cyclicLift X ((i : ℕ) : ℤ) : UnitAddCircle) * G (blockLength X ((i : ℕ) : ℤ) 1)
              ∂gibbsMeasure P N :=
        Finset.sum_le_sum (fun i _ => lintegral_mono (fun X => hterm i X))
    _ = ∑ i : Fin (N : ℕ), volume (Metric.closedBall (arcCentre N a r) (arcRadius N r)) *
          ∫⁻ X : Configuration N, G (blockLength X ((i : ℕ) : ℤ) 1) ∂gibbsMeasure P N :=
        Finset.sum_congr rfl (fun i _ => lintegral_rotation_mul_closedBall P N ((i : ℕ) : ℤ)
          (arcCentre N a r) (arcRadius N r) G hGm)
    _ ≤ ∑ i : Fin (N : ℕ), ENNReal.ofReal (r / (N : ℝ)) * ENNReal.ofReal C :=
        Finset.sum_le_sum (fun i _ => by
          rw [volume_closedBall_arc hr hrN]
          exact mul_le_mul_of_nonneg_left (hGi i) zero_le)
    _ = ENNReal.ofReal (r * C) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul
            (by positivity)]
        congr 1
        field_simp

theorem loopCount_nonneg (a r : ℝ) (X : Configuration N) : 0 ≤ loopCount a r X :=
  Finset.sum_nonneg (fun i _ => by split_ifs <;> norm_num)

theorem measurable_loopCount (a r : ℝ) :
    Measurable (fun X : Configuration N => loopCount a r X) := by
  unfold loopCount
  refine Finset.measurable_sum _ (fun i _ => ?_)
  exact Measurable.ite (measurable_loopPos i (measurableSet_microArc N a r)) measurable_const
    measurable_const

/-- **Count moments**, the moments part of Lemma 5.8 (the claim `‖M_J‖_{L^p} ≤ C(1+r)`).
For every `p ≥ 1` there is `C > 0`, depending only on `β, s, p`, such that every `N ≥ 2` and
every arc of microscopic length `0 < r ≤ N` satisfy `‖M_J‖_{L^p} ≤ C (1 + r)`. -/
theorem loopCount_eLpNorm (P : Parameters) {p : ℝ} (_hp : 1 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (_hPL : External.PrekopaLeindler) (N : ℕ+), 2 ≤ (N : ℕ) →
      ∀ (a r : ℝ), 0 < r → r ≤ N →
        eLpNorm (fun X : Configuration N => loopCount a r X) (ENNReal.ofReal p)
          (gibbsMeasure P N) ≤ ENNReal.ofReal (C * (1 + r)) := by
  set m : ℕ := max 2 ⌈p⌉₊ with hm_def
  have hm2 : 2 ≤ m := le_max_left _ _
  have hpm : p ≤ (m : ℝ) := le_trans (Nat.le_ceil p) (by exact_mod_cast le_max_right _ _)
  set q : ℕ := m - 1 with hq_def
  have hq1 : 1 ≤ q := by omega
  have hmq : q + 1 = m := by omega
  have hr1 : 1 ≤ m := by omega
  obtain ⟨D, hD, hsum⟩ := lintegral_sum_inv_pow_le P hq1
  set K : ℝ := 2 ^ (m - 1) * (1 + D) with hK_def
  have hK : 0 < K := by positivity
  refine ⟨K ^ ((m : ℝ)⁻¹), by positivity, fun hPL N hN a r hr hrN => ?_⟩
  have hprob : IsProbabilityMeasure (gibbsMeasure P N) := (modelWellDefined P N).2.2
  -- Pointwise: `M^m ≤ 2^{m-1} (1 + r^q ∑ 1_J(z_i) y_i^{-q})`.
  have hpt : ∀ X : Configuration N, (loopCount a r X) ^ m ≤
      2 ^ (m - 1) * (1 + r ^ q * ∑ i : Fin (N : ℕ),
        if loopPos X i ∈ microArc N a r then gap X (i : ℕ) ^ (-(q : ℤ)) else 0) := by
    intro X
    have hM0 := loopCount_nonneg a r X
    have hw0 : 0 ≤ max (loopCount a r X - 1) 0 := le_max_right _ _
    have hMw : loopCount a r X ≤ 1 + max (loopCount a r X - 1) 0 := by
      have := le_max_left (loopCount a r X - 1) (0 : ℝ)
      linarith
    have h1 : (loopCount a r X) ^ m ≤ (1 + max (loopCount a r X - 1) 0) ^ m :=
      pow_le_pow_left₀ hM0 hMw m
    have h2 : (1 + max (loopCount a r X - 1) 0) ^ m ≤
        2 ^ (m - 1) * (1 ^ m + (max (loopCount a r X - 1) 0) ^ m) :=
      add_pow_le zero_le_one hw0 m
    have h3 : (max (loopCount a r X - 1) 0) ^ m ≤ r ^ q * ∑ i : Fin (N : ℕ),
        if loopPos X i ∈ microArc N a r then gap X (i : ℕ) ^ (-(q : ℤ)) else 0 := by
      rw [← hmq]
      exact loopCount_pow_le_sum a r hr hrN X q
    rw [one_pow] at h2
    calc (loopCount a r X) ^ m ≤ (1 + max (loopCount a r X - 1) 0) ^ m := h1
      _ ≤ 2 ^ (m - 1) * (1 + (max (loopCount a r X - 1) 0) ^ m) := h2
      _ ≤ 2 ^ (m - 1) * (1 + r ^ q * ∑ i : Fin (N : ℕ),
          if loopPos X i ∈ microArc N a r then gap X (i : ℕ) ^ (-(q : ℤ)) else 0) := by
          gcongr
  -- Integrate the pointwise bound: `M^m ≤ c1 + c2 Y` with `c1 = 2^{m-1}`, `c2 = c1 r^q`.
  set c1 : ℝ := 2 ^ (m - 1) with hc1
  set c2 : ℝ := 2 ^ (m - 1) * r ^ q with hc2
  have hc1pos : 0 ≤ c1 := by positivity
  have hc2pos : 0 ≤ c2 := by positivity
  have hYbound := hsum hPL N a r hr hrN
  have hYnn : ∀ X : Configuration N, 0 ≤ ∑ i : Fin (N : ℕ),
      (if loopPos X i ∈ microArc N a r then gap X (i : ℕ) ^ (-(q : ℤ)) else 0) := fun X =>
    Finset.sum_nonneg (fun i _ => by
      split_ifs
      · exact zpow_nonneg (gap_pos X _).le _
      · exact le_rfl)
  have hpt' : ∀ X : Configuration N, ENNReal.ofReal ((loopCount a r X) ^ m) ≤
      ENNReal.ofReal c1 + ENNReal.ofReal c2 * ENNReal.ofReal
        (∑ i : Fin (N : ℕ), if loopPos X i ∈ microArc N a r then gap X (i : ℕ) ^
          (-(q : ℤ)) else 0) := by
    intro X
    calc ENNReal.ofReal ((loopCount a r X) ^ m)
        ≤ ENNReal.ofReal (c1 + c2 * ∑ i : Fin (N : ℕ),
            if loopPos X i ∈ microArc N a r then gap X (i : ℕ) ^ (-(q : ℤ)) else 0) := by
          refine ENNReal.ofReal_le_ofReal ((hpt X).trans (le_of_eq ?_))
          rw [hc2]
          ring
      _ = ENNReal.ofReal c1 + ENNReal.ofReal c2 * ENNReal.ofReal
            (∑ i : Fin (N : ℕ), if loopPos X i ∈ microArc N a r then gap X (i : ℕ) ^
              (-(q : ℤ)) else 0) := by
          rw [ENNReal.ofReal_add hc1pos (mul_nonneg hc2pos (hYnn X)),
            ENNReal.ofReal_mul hc2pos]
  have hint_lint : ∫⁻ X : Configuration N, ENNReal.ofReal ((loopCount a r X) ^ m)
      ∂gibbsMeasure P N ≤ ENNReal.ofReal c1 + ENNReal.ofReal c2 * ENNReal.ofReal (r * D) := by
    calc ∫⁻ X : Configuration N, ENNReal.ofReal ((loopCount a r X) ^ m) ∂gibbsMeasure P N
        ≤ ∫⁻ X : Configuration N, (ENNReal.ofReal c1 + ENNReal.ofReal c2 * ENNReal.ofReal
            (∑ i : Fin (N : ℕ), if loopPos X i ∈ microArc N a r then gap X (i : ℕ) ^
              (-(q : ℤ)) else 0)) ∂gibbsMeasure P N := lintegral_mono hpt'
      _ = ENNReal.ofReal c1 + ENNReal.ofReal c2 * ∫⁻ X : Configuration N, ENNReal.ofReal
            (∑ i : Fin (N : ℕ), if loopPos X i ∈ microArc N a r then gap X (i : ℕ) ^
              (-(q : ℤ)) else 0) ∂gibbsMeasure P N := by
          rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal c1 + ENNReal.ofReal c2 * ENNReal.ofReal (r * D) := by
          gcongr
  -- The constants: `c1 + c2 r D = c1 (1 + D r^m) ≤ K (1+r)^m`.
  have hrm : r ^ m ≤ (1 + r) ^ m := pow_le_pow_left₀ hr.le (by linarith) m
  have h1r : 1 ≤ (1 + r) ^ m := one_le_pow₀ (by linarith)
  have hconst : c1 + c2 * (r * D) ≤ K * (1 + r) ^ m := by
    have e : c1 + c2 * (r * D) = c1 * (1 + D * r ^ m) := by
      rw [hc2, show r ^ m = r ^ q * r by rw [← hmq, pow_succ]]
      ring
    have hk : K * (1 + r) ^ m = c1 * ((1 + D) * (1 + r) ^ m) := by
      rw [hK_def]
      ring
    rw [e, hk]
    refine mul_le_mul_of_nonneg_left ?_ hc1pos
    nlinarith
  have hint : ∫⁻ X : Configuration N, ENNReal.ofReal ((loopCount a r X) ^ m)
      ∂gibbsMeasure P N ≤ ENNReal.ofReal (K * (1 + r) ^ m) := by
    refine hint_lint.trans ?_
    rw [← ENNReal.ofReal_mul hc2pos, ← ENNReal.ofReal_add hc1pos
      (mul_nonneg hc2pos (mul_nonneg hr.le hD.le))]
    exact ENNReal.ofReal_le_ofReal hconst
  -- Conclude for the `L^m` norm, then for `L^p` by monotonicity.
  have hB0 : 0 ≤ K ^ ((m : ℝ)⁻¹) * (1 + r) := by positivity
  have hKm : (K ^ ((m : ℝ)⁻¹) * (1 + r)) ^ m = K * (1 + r) ^ m := by
    rw [mul_pow, Real.rpow_inv_natCast_pow hK.le (by omega)]
  have hE := eLpNorm_le_of_lintegral_pow_le (μ := gibbsMeasure P N)
    (measurable_loopCount a r) hr1 hB0 (by
      rw [hKm]
      calc ∫⁻ X : Configuration N, ENNReal.ofReal (|loopCount a r X| ^ m) ∂gibbsMeasure P N
          = ∫⁻ X : Configuration N, ENNReal.ofReal ((loopCount a r X) ^ m) ∂gibbsMeasure P N :=
            lintegral_congr (fun X => by rw [abs_of_nonneg (loopCount_nonneg a r X)])
        _ ≤ ENNReal.ofReal (K * (1 + r) ^ m) := hint)
  calc eLpNorm (fun X : Configuration N => loopCount a r X) (ENNReal.ofReal p) (gibbsMeasure P N)
      ≤ eLpNorm (fun X : Configuration N => loopCount a r X) (ENNReal.ofReal m)
          (gibbsMeasure P N) := eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal hpm)
    _ ≤ ENNReal.ofReal (K ^ ((m : ℝ)⁻¹) * (1 + r)) := hE

end Riesz1

end
end
