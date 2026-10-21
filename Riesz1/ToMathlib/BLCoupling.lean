/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.CLT.BLDistance

/-!
# Scaling and coupling bounds for the bounded-Lipschitz distance

Two general facts about the bounded-Lipschitz distance `blDistance`.

The first fact states that the dilation `x ↦ κ * x` changes the distance by at most the factor
`max 1 κ`. The second fact bounds the distance between the laws of two real random variables by
the mean absolute difference of the variables, which is the usual coupling bound. The proofs use
only the supremum definition of `blDistance` and the elementary Lipschitz estimate for test
functions in `BLTest`.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace Riesz1

/-- A bounded-Lipschitz test function `f` moves two points by at most their distance, so
`|f a - f b| ≤ |a - b|`. -/
lemma blTest_abs_sub_le_abs_sub {f : ℝ → ℝ} (hf : BLTest f) (a b : ℝ) :
    |f a - f b| ≤ |a - b| := by
  obtain ⟨h1, -, h2⟩ := hf
  have key : ‖f a - f b‖ ≤ 1 * ‖a - b‖ :=
    Convex.norm_image_sub_le_of_norm_deriv_le (f := f) (s := Set.univ) (x := b) (y := a) (C := 1)
      (fun x _ => (h1.differentiable (by norm_num)) x)
      (fun x _ => by simpa [Real.norm_eq_abs] using h2 x) convex_univ (Set.mem_univ _)
      (Set.mem_univ _)
  simpa [Real.norm_eq_abs] using key

/-- Dilating a bounded-Lipschitz test function by `x ↦ κ * x` and dividing by `max 1 κ` gives
again a bounded-Lipschitz test function. The division keeps the bound `|f| ≤ 1`, and the factor
`κ` in the derivative is at most `max 1 κ`. -/
lemma blTest_dilate_div {κ : ℝ} (hκ : 0 < κ) {f : ℝ → ℝ} (hf : BLTest f) :
    BLTest (fun x => f (κ * x) / max 1 κ) := by
  have hM : 0 < max 1 κ := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hM1 : 1 ≤ max 1 κ := le_max_left _ _
  have hκM : κ ≤ max 1 κ := le_max_right _ _
  obtain ⟨h1, h2, h3⟩ := hf
  refine ⟨?_, ?_, ?_⟩
  · have hl : ContDiff ℝ 1 (fun x : ℝ => κ * x) := contDiff_const.mul contDiff_id
    exact (h1.comp hl).div_const _
  · intro x
    rw [abs_div, abs_of_pos hM, div_le_one hM]
    exact (h2 _).trans hM1
  · intro x
    have hf' : HasDerivAt f (deriv f (κ * x)) (κ * x) :=
      ((h1.differentiable (by norm_num)) (κ * x)).hasDerivAt
    have hl : HasDerivAt (fun y : ℝ => κ * y) κ x := by
      have := (hasDerivAt_id' x).const_mul κ
      rwa [mul_one] at this
    have hd : HasDerivAt (fun y => f (κ * y) / max 1 κ) (deriv f (κ * x) * κ / max 1 κ) x :=
      (hf'.comp x hl).div_const _
    rw [hd.deriv, abs_div, abs_mul, abs_of_pos hκ, abs_of_pos hM, div_le_one hM]
    calc |deriv f (κ * x)| * κ ≤ 1 * κ := mul_le_mul_of_nonneg_right (h3 _) hκ.le
      _ ≤ max 1 κ := by linarith

/-- The integral of a bounded-Lipschitz test function against the law `μ.map (κ * ·)` equals the
integral of the dilated function `x ↦ f (κ * x)` against `μ`. -/
lemma integral_map_mul_left {κ : ℝ} (μ : ProbabilityMeasure ℝ) {f : ℝ → ℝ} (hf : BLTest f) :
    ∫ x, f x ∂((μ.map (κ * ·) : ProbabilityMeasure ℝ) : Measure ℝ) =
      ∫ x, f (κ * x) ∂(μ : Measure ℝ) :=
  integral_map (measurable_const_mul κ).aemeasurable hf.1.continuous.aestronglyMeasurable

/-- Dilating both laws by `x ↦ κ * x` multiplies the bounded-Lipschitz distance by at most
`max 1 κ`. For a test function `f`, the dilated test function `x ↦ f (κ * x) / max 1 κ` is again
a bounded-Lipschitz test function, and its integral differences are the dilated ones divided by
`max 1 κ`. -/
lemma blDistance_map_mul_left_le {κ : ℝ} (hκ : 0 < κ) (μ ν : ProbabilityMeasure ℝ) :
    blDistance (μ.map (κ * ·)) (ν.map (κ * ·)) ≤ ENNReal.ofReal (max 1 κ) * blDistance μ ν := by
  have hM : 0 < max 1 κ := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hM0 : max 1 κ ≠ 0 := hM.ne'
  -- The integral of `f` against the dilated law is `max 1 κ` times the integral of the rescaled
  -- test function against the original law.
  have key : ∀ (ρ : ProbabilityMeasure ℝ) (f : {f : ℝ → ℝ // BLTest f}),
      ∫ x, f.val x ∂((ρ.map (κ * ·) : ProbabilityMeasure ℝ) : Measure ℝ) =
        max 1 κ * ∫ x, f.val (κ * x) / max 1 κ ∂(ρ : Measure ℝ) := by
    intro ρ f
    rw [integral_map_mul_left ρ f.property, ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    dsimp only
    rw [mul_div_assoc', mul_div_cancel_left₀ _ hM0]
  refine iSup_le fun f => ?_
  have hg := blTest_dilate_div hκ f.property
  calc ENNReal.ofReal |(∫ x, f.val x ∂((μ.map (κ * ·) : ProbabilityMeasure ℝ) : Measure ℝ)) -
        ∫ x, f.val x ∂((ν.map (κ * ·) : ProbabilityMeasure ℝ) : Measure ℝ)|
      = ENNReal.ofReal (max 1 κ) * ENNReal.ofReal |(∫ x, f.val (κ * x) / max 1 κ ∂(μ : Measure ℝ)) -
          ∫ x, f.val (κ * x) / max 1 κ ∂(ν : Measure ℝ)| := by
        rw [key μ f, key ν f, ← mul_sub, abs_mul, abs_of_pos hM, ENNReal.ofReal_mul hM.le]
    _ ≤ ENNReal.ofReal (max 1 κ) * blDistance μ ν := by
        gcongr
        exact ofReal_abs_integral_sub_le_blDistance μ ν hg

/-- The laws of two real random variables `X` and `Y` on a probability space are within the mean
absolute difference `∫ |X - Y|` in the bounded-Lipschitz distance. Each bounded-Lipschitz test
function changes by at most `|X - Y|` pointwise, so its integral difference is at most `∫ |X - Y|`.
Here the laws are `P.map X` and `P.map Y`. -/
theorem blDistance_map_le_ofReal_integral_abs_sub {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X Y : Ω → ℝ} (hX : Measurable X)
    (hY : Measurable Y) (hXY : Integrable (fun ω => |X ω - Y ω|) P) :
    blDistance (ProbabilityMeasure.map (⟨P, inferInstance⟩ : ProbabilityMeasure Ω) X)
        (ProbabilityMeasure.map (⟨P, inferInstance⟩ : ProbabilityMeasure Ω) Y) ≤
      ENNReal.ofReal (∫ ω, |X ω - Y ω| ∂P) := by
  refine iSup_le fun f => ?_
  have hfm : Measurable f.val := f.property.1.continuous.measurable
  -- Each composition `f ∘ X` is bounded by `1` and measurable, hence integrable.
  have hIX : Integrable (fun ω => f.val (X ω)) P :=
    (integrable_const (1 : ℝ)).mono' (hfm.comp hX).aestronglyMeasurable
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact f.property.2.1 (X ω))
  have hIY : Integrable (fun ω => f.val (Y ω)) P :=
    (integrable_const (1 : ℝ)).mono' (hfm.comp hY).aestronglyMeasurable
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact f.property.2.1 (Y ω))
  -- The integrals against the laws are integrals of the compositions on `Ω`.
  have eX : ∫ x, f.val x ∂(ProbabilityMeasure.map (⟨P, inferInstance⟩ : ProbabilityMeasure Ω) X
      : Measure ℝ) = ∫ ω, f.val (X ω) ∂P :=
    integral_map hX.aemeasurable hfm.aestronglyMeasurable
  have eY : ∫ x, f.val x ∂(ProbabilityMeasure.map (⟨P, inferInstance⟩ : ProbabilityMeasure Ω) Y
      : Measure ℝ) = ∫ ω, f.val (Y ω) ∂P :=
    integral_map hY.aemeasurable hfm.aestronglyMeasurable
  -- Pointwise, the test function is `1`-Lipschitz, so the difference of compositions is at most
  -- `|X - Y|`, and the norm of its integral is at most the integral of `|X - Y|`.
  have hpt : ∀ ω, ‖f.val (X ω) - f.val (Y ω)‖ ≤ |X ω - Y ω| := fun ω => by
    rw [Real.norm_eq_abs]
    exact blTest_abs_sub_le_abs_sub f.property (X ω) (Y ω)
  have hdiff := norm_integral_le_of_norm_le hXY (ae_of_all _ hpt)
  rw [integral_sub hIX hIY, Real.norm_eq_abs] at hdiff
  rw [eX, eY]
  exact ENNReal.ofReal_le_ofReal hdiff

/-- Two probability measures with the same integrals against every bounded-Lipschitz test function
have the same bounded-Lipschitz distance to every third probability measure. -/
theorem blDistance_eq_of_integral_eq {μ μ' ν : ProbabilityMeasure ℝ}
    (h : ∀ f : ℝ → ℝ, BLTest f → ∫ x, f x ∂(μ : Measure ℝ) = ∫ x, f x ∂(μ' : Measure ℝ)) :
    blDistance μ ν = blDistance μ' ν := by
  unfold blDistance
  refine iSup_congr fun f => ?_
  rw [h f.val f.property]

/-- The laws of two real random variables are close when they agree except on an event of small
probability. If `X` and `Y` differ by at most `ε` outside the event `{ε < |X - Y|}`, then the
bounded-Lipschitz distance of their laws is at most `ε` plus twice the probability of that event.
Each test function changes by at most `ε` off the event, and by at most `2` on it. -/
theorem blDistance_map_le_of_measure_gt {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X Y : Ω → ℝ} (hX : Measurable X)
    (hY : Measurable Y) {ε : ℝ} (hε : 0 ≤ ε) :
    blDistance (ProbabilityMeasure.map (⟨P, inferInstance⟩ : ProbabilityMeasure Ω) X)
        (ProbabilityMeasure.map (⟨P, inferInstance⟩ : ProbabilityMeasure Ω) Y) ≤
      ENNReal.ofReal (ε + 2 * (P {ω | ε < |X ω - Y ω|}).toReal) := by
  have hXY : Measurable (fun ω => |X ω - Y ω|) :=
    continuous_abs.measurable.comp (hX.sub hY)
  have hS : MeasurableSet {ω | ε < |X ω - Y ω|} := measurableSet_lt measurable_const hXY
  refine iSup_le fun f => ?_
  have hfm : Measurable f.val := f.property.1.continuous.measurable
  have hIX : Integrable (fun ω => f.val (X ω)) P :=
    (integrable_const (1 : ℝ)).mono' (hfm.comp hX).aestronglyMeasurable
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact f.property.2.1 (X ω))
  have hIY : Integrable (fun ω => f.val (Y ω)) P :=
    (integrable_const (1 : ℝ)).mono' (hfm.comp hY).aestronglyMeasurable
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact f.property.2.1 (Y ω))
  have eX : ∫ x, f.val x ∂(ProbabilityMeasure.map (⟨P, inferInstance⟩ : ProbabilityMeasure Ω) X
      : Measure ℝ) = ∫ ω, f.val (X ω) ∂P :=
    integral_map hX.aemeasurable hfm.aestronglyMeasurable
  have eY : ∫ x, f.val x ∂(ProbabilityMeasure.map (⟨P, inferInstance⟩ : ProbabilityMeasure Ω) Y
      : Measure ℝ) = ∫ ω, f.val (Y ω) ∂P :=
    integral_map hY.aemeasurable hfm.aestronglyMeasurable
  -- Pointwise: off the event the test function moves by at most `ε`. On the event, it moves by at most `2`.
  have hpt : ∀ ω, ‖f.val (X ω) - f.val (Y ω)‖ ≤
      ε + 2 * {ω | ε < |X ω - Y ω|}.indicator 1 ω := by
    intro ω
    rw [Real.norm_eq_abs]
    by_cases h : ε < |X ω - Y ω|
    · have hmem : ω ∈ {ω | ε < |X ω - Y ω|} := h
      rw [Set.indicator_of_mem hmem, Pi.one_apply]
      have h1 := f.property.2.1 (X ω)
      have h2 := f.property.2.1 (Y ω)
      have h3 : |f.val (X ω) - f.val (Y ω)| ≤ |f.val (X ω)| + |f.val (Y ω)| :=
        abs_sub _ _
      linarith
    · have hmem : ω ∉ {ω | ε < |X ω - Y ω|} := h
      rw [Set.indicator_of_notMem hmem]
      have hle : |X ω - Y ω| ≤ ε := not_lt.mp h
      have := blTest_abs_sub_le_abs_sub f.property (X ω) (Y ω)
      linarith
  have hind : Integrable (fun ω => {ω | ε < |X ω - Y ω|}.indicator (1 : Ω → ℝ) ω) P :=
    (integrable_indicator_iff hS).2 (integrable_const (1 : ℝ))
  have hbound : Integrable (fun ω => ε + 2 * {ω | ε < |X ω - Y ω|}.indicator 1 ω) P :=
    (integrable_const ε).add (hind.const_mul 2)
  have hdiff : ‖∫ ω, f.val (X ω) ∂P - ∫ ω, f.val (Y ω) ∂P‖ ≤
      ε + 2 * (P {ω | ε < |X ω - Y ω|}).toReal := by
    rw [← integral_sub hIX hIY]
    calc ‖∫ ω, (f.val (X ω) - f.val (Y ω)) ∂P‖
        ≤ ∫ ω, ‖f.val (X ω) - f.val (Y ω)‖ ∂P := norm_integral_le_integral_norm _
      _ ≤ ∫ ω, (ε + 2 * {ω | ε < |X ω - Y ω|}.indicator 1 ω) ∂P :=
          integral_mono_of_nonneg (ae_of_all _ fun ω => norm_nonneg _) hbound
            (ae_of_all _ hpt)
      _ = ε + 2 * (P {ω | ε < |X ω - Y ω|}).toReal := by
          rw [integral_add (integrable_const ε) (hind.const_mul 2), integral_const,
            integral_const_mul, integral_indicator_one hS]
          simp [measureReal_def]
  rw [eX, eY]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [Real.norm_eq_abs] at hdiff
  exact hdiff

end Riesz1
