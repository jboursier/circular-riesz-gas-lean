/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.PeriodicBoundedPrimitive
public import Riesz1.Frozen.CentralRep

/-!
# Primitive of the periodized interval indicator on enlarged circles

On the circle `Circle ℓ` of length `ℓ ≥ 1`, let `1_{(u,v)}` be the indicator of an open interval
with `-1/2 < u < v < 1/2`, and let `z ↦ 1_{(u,v)}(centralRep z)` be its periodization. Its mean
is `(v - u)/ℓ`. Subtracting the mean gives a mean-zero periodic function bounded by one, whose
continuous periodic primitive is bounded by `2 (v - u)` and is `1`-Lipschitz, uniformly in `ℓ`.
The primitive has the Fourier relation of `PrimitiveRegularity` for every nonzero mode.
-/

public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace Riesz1

/-- The periodized indicator of `(u, v)` on the circle of length `ℓ`: the indicator of `(u, v)`
at the central representative. -/
@[expose] noncomputable def periodicIndicator (ℓ : Length) (u v : ℝ) (z : Circle ℓ) : ℝ :=
  (Ioo u v).indicator (fun _ => (1 : ℝ)) (centralRep ℓ z)

/-- The central representative of a point of the central interval is that point. -/
lemma centralRep_coe_of_mem (ℓ : Length) {t : ℝ} (ht : t ∈ Ico (-(ℓ.val / 2)) (ℓ.val / 2)) :
    centralRep ℓ (t : Circle ℓ) = t := by
  have : Fact (0 < ℓ.val) := ⟨ℓ.property⟩
  unfold centralRep
  exact AddCircle.equivIco_coe_of_mem (a := -ℓ.val / 2)
    ⟨by linarith [ht.1], by linarith [ht.2]⟩

/-- Shifting a real by an integer multiple of the period does not change its class on the circle. -/
lemma coe_add_int_mul_eq (ℓ : Length) (t : ℝ) (n : ℤ) :
    ((t + n * ℓ.val : ℝ) : Circle ℓ) = (t : Circle ℓ) := by
  have : Fact (0 < ℓ.val) := ⟨ℓ.property⟩
  rw [show t + (n : ℝ) * ℓ.val = t + n • ℓ.val by rw [zsmul_eq_mul], AddCircle.coe_add,
    AddCircle.coe_zsmul, AddCircle.coe_period, zsmul_zero, add_zero]

/-- The periodized indicator is a function of the class of its argument. -/
lemma periodicIndicator_coe_add_int_mul (ℓ : Length) (u v t : ℝ) (n : ℤ) :
    periodicIndicator ℓ u v ((t + n * ℓ.val : ℝ) : Circle ℓ) = periodicIndicator ℓ u v (t : Circle ℓ) := by
  unfold periodicIndicator
  rw [coe_add_int_mul_eq]

/-- The periodized indicator is `ℓ`-periodic as a function of the real variable. -/
lemma periodicIndicator_periodic (ℓ : Length) (u v : ℝ) :
    Function.Periodic (fun t : ℝ => periodicIndicator ℓ u v (t : Circle ℓ)) ℓ.val := by
  intro t
  show periodicIndicator ℓ u v ((t + ℓ.val : ℝ) : Circle ℓ) = periodicIndicator ℓ u v (t : Circle ℓ)
  rw [AddCircle.coe_add_period]

/-- The periodized indicator is measurable. -/
lemma measurable_periodicIndicator (ℓ : Length) (u v : ℝ) :
    Measurable (fun t : ℝ => periodicIndicator ℓ u v (t : Circle ℓ)) := by
  have : Fact (0 < ℓ.val) := ⟨ℓ.property⟩
  have hc : Measurable (fun t : ℝ => centralRep ℓ (t : Circle ℓ)) := by
    unfold centralRep
    exact measurable_subtype_coe.comp
      ((AddCircle.measurableEquivIco ℓ.val (-ℓ.val / 2)).measurable.comp AddCircle.measurable_mk')
  exact ((measurable_const.indicator measurableSet_Ioo)).comp hc

/-- The indicator of an open interval is continuous at every point other than its endpoints. -/
lemma continuousAt_interval_indicator {u v y : ℝ} (hyu : y ≠ u) (hyv : y ≠ v) :
    ContinuousAt ((Ioo u v).indicator (fun _ => (1 : ℝ))) y := by
  by_cases h : y ∈ Ioo u v
  · exact (continuousAt_const : ContinuousAt (fun _ : ℝ => (1 : ℝ)) y).congr
      (Filter.eventually_of_mem (Ioo_mem_nhds h.1 h.2) fun z hz =>
        (indicator_of_mem hz (fun _ : ℝ => (1 : ℝ))).symm)
  · have hy : y < u ∨ v < y := by
      by_contra hc
      rw [not_or, not_lt, not_lt] at hc
      exact h ⟨lt_of_le_of_ne hc.1 (Ne.symm hyu), lt_of_le_of_ne hc.2 hyv⟩
    rcases hy with hlt | hgt
    · exact (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : ℝ)) y).congr
        (Filter.eventually_of_mem (Iio_mem_nhds hlt) fun z hz =>
          (indicator_of_notMem (fun hm => (not_lt.2 hz.le) hm.1) (fun _ : ℝ => (1 : ℝ))).symm)
    · exact (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : ℝ)) y).congr
        (Filter.eventually_of_mem (Ioi_mem_nhds hgt) fun z hz =>
          (indicator_of_notMem (fun hm => (not_lt.2 hm.2.le) hz) (fun _ : ℝ => (1 : ℝ))).symm)

/-- The marks of the periodized indicator: the translates of the endpoints and of the half-period
points, where the central representative jumps or the indicator is discontinuous. -/
lemma countable_periodicIndicator_marks (ℓ : Length) (u v : ℝ) :
    ({t : ℝ | ∃ k : ℤ, t = u + k * ℓ.val ∨ t = v + k * ℓ.val ∨ t = (k + 1 / 2) * ℓ.val}).Countable := by
  have h : {t : ℝ | ∃ k : ℤ, t = u + k * ℓ.val ∨ t = v + k * ℓ.val ∨ t = (k + 1 / 2) * ℓ.val} =
      (Set.range fun k : ℤ => u + k * ℓ.val) ∪ (Set.range fun k : ℤ => v + k * ℓ.val) ∪
        Set.range fun k : ℤ => ((k : ℝ) + 1 / 2) * ℓ.val := by
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_range]
    constructor
    · rintro ⟨k, hk | hk | hk⟩
      · exact Or.inl (Or.inl ⟨k, hk.symm⟩)
      · exact Or.inl (Or.inr ⟨k, hk.symm⟩)
      · exact Or.inr ⟨k, hk.symm⟩
    · rintro ((⟨k, hk⟩ | ⟨k, hk⟩) | ⟨k, hk⟩)
      · exact ⟨k, Or.inl hk.symm⟩
      · exact ⟨k, Or.inr (Or.inl hk.symm)⟩
      · exact ⟨k, Or.inr (Or.inr hk.symm)⟩
  rw [h]
  exact ((Set.countable_range _).union (Set.countable_range _)).union (Set.countable_range _)

/-- Away from the marks, the periodized indicator is continuous. -/
lemma continuousAt_periodicIndicator {ℓ : Length} {u v t0 : ℝ} (hℓ : 1 ≤ ℓ.val)
    (hmark : t0 ∉ {t : ℝ | ∃ k : ℤ, t = u + k * ℓ.val ∨ t = v + k * ℓ.val ∨ t = (k + 1 / 2) * ℓ.val}) :
    ContinuousAt (fun t : ℝ => periodicIndicator ℓ u v (t : Circle ℓ)) t0 := by
  have hℓ0 : 0 < ℓ.val := by linarith
  set N : ℤ := round (t0 / ℓ.val) with hN
  have hnot : ∀ k : ℤ, t0 ≠ u + k * ℓ.val ∧ t0 ≠ v + k * ℓ.val ∧ t0 ≠ (k + 1 / 2) * ℓ.val := by
    intro k
    refine ⟨fun h => hmark ⟨k, Or.inl h⟩, fun h => hmark ⟨k, Or.inr (Or.inl h)⟩,
      fun h => hmark ⟨k, Or.inr (Or.inr h)⟩⟩
  have hround : |t0 / ℓ.val - N| ≤ 1 / 2 := abs_sub_round _
  have hhalf : |t0 / ℓ.val - N| ≠ 1 / 2 := by
    intro h
    rcases abs_eq (by norm_num : (0 : ℝ) ≤ 1 / 2) |>.1 h with h1 | h1
    · apply (hnot N).2.2
      field_simp at h1 ⊢
      linarith
    · apply (hnot (N - 1)).2.2
      have : t0 / ℓ.val = (N - 1 : ℤ) + 1 / 2 := by push_cast; linarith
      field_simp at this ⊢
      linarith
  have hlt : |t0 / ℓ.val - N| < 1 / 2 := lt_of_le_of_ne hround hhalf
  have hdist : |t0 - N * ℓ.val| < ℓ.val / 2 := by
    have e : t0 - N * ℓ.val = ℓ.val * (t0 / ℓ.val - N) := by field_simp
    rw [e, abs_mul, abs_of_pos hℓ0]
    nlinarith
  have hyu : t0 - N * ℓ.val ≠ u := fun h => (hnot N).1 (by linarith)
  have hyv : t0 - N * ℓ.val ≠ v := fun h => (hnot N).2.1 (by linarith)
  have hcont : ContinuousAt (fun t : ℝ => (Ioo u v).indicator (fun _ => (1 : ℝ)) (t - N * ℓ.val)) t0 :=
    ContinuousAt.comp (f := fun t : ℝ => t - N * ℓ.val) (continuousAt_interval_indicator hyu hyv)
      (continuous_sub_right _).continuousAt
  have hev : ∀ᶠ t in 𝓝 t0, |t - N * ℓ.val| < ℓ.val / 2 :=
    ((continuous_id.sub continuous_const).abs.continuousAt).eventually_lt continuousAt_const hdist
  refine hcont.congr ?_
  filter_upwards [hev] with t ht
  have hmem : t - N * ℓ.val ∈ Ico (-(ℓ.val / 2)) (ℓ.val / 2) :=
    ⟨by linarith [(abs_lt.1 ht).1], by linarith [(abs_lt.1 ht).2]⟩
  unfold periodicIndicator
  have hshift : ((t : ℝ) : Circle ℓ) = ((t - N * ℓ.val : ℝ) : Circle ℓ) := by
    rw [← coe_add_int_mul_eq ℓ (t - N * ℓ.val) N]
    congr 1
    ring
  rw [hshift, centralRep_coe_of_mem ℓ hmem]

/-- A bounded measurable function is interval integrable. -/
lemma intervalIntegrable_of_bounded_measurable {g : ℝ → ℝ} (hg : Measurable g) {B : ℝ} (hB : 0 ≤ B)
    (hgB : ∀ t, |g t| ≤ B) (a b : ℝ) : IntervalIntegrable g volume a b := by
  refine IntervalIntegrable.mono_fun (intervalIntegrable_const (c := B)) hg.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun t => by
    show ‖g t‖ ≤ |B|
    rw [Real.norm_eq_abs, abs_of_nonneg hB]
    exact hgB t

/-- The periodized indicator is bounded by one, and nonnegative. -/
lemma periodicIndicator_mem_Icc (ℓ : Length) (u v t : ℝ) :
    0 ≤ periodicIndicator ℓ u v (t : Circle ℓ) ∧ periodicIndicator ℓ u v (t : Circle ℓ) ≤ 1 := by
  unfold periodicIndicator
  by_cases h : centralRep ℓ (t : Circle ℓ) ∈ Ioo u v
  · rw [Set.indicator_of_mem h]
    exact ⟨zero_le_one, le_rfl⟩
  · rw [Set.indicator_of_notMem h]
    exact ⟨le_rfl, zero_le_one⟩

/-- The periodized indicator is measurable and bounded, so it is interval integrable. -/
lemma intervalIntegrable_periodicIndicator (ℓ : Length) (u v : ℝ) (a b : ℝ) :
    IntervalIntegrable (fun t : ℝ => periodicIndicator ℓ u v (t : Circle ℓ)) volume a b :=
  intervalIntegrable_of_bounded_measurable (measurable_periodicIndicator ℓ u v) zero_le_one
    (fun t => by
      rw [abs_of_nonneg (periodicIndicator_mem_Icc ℓ u v t).1]
      exact (periodicIndicator_mem_Icc ℓ u v t).2) a b

/-- The integral of the periodized indicator over one period is the length of the interval. -/
lemma integral_periodicIndicator_period (ℓ : Length) (hℓ : 1 ≤ ℓ.val) {u v : ℝ}
    (hu : -(1 / 2) < u) (huv : u < v) (hv : v < 1 / 2) :
    ∫ t in (0 : ℝ)..ℓ.val, periodicIndicator ℓ u v (t : Circle ℓ) = v - u := by
  have hsub : Ioo u v ⊆ Ioc (-(ℓ.val / 2)) (ℓ.val / 2) := fun y hy =>
    ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hshift := (periodicIndicator_periodic ℓ u v).intervalIntegral_add_eq 0 (-(ℓ.val / 2))
  rw [zero_add, show -(ℓ.val / 2) + ℓ.val = ℓ.val / 2 by ring] at hshift
  rw [hshift]
  have hae : ∀ᵐ t : ℝ, t ∈ Set.uIoc (-(ℓ.val / 2)) (ℓ.val / 2) →
      periodicIndicator ℓ u v (t : Circle ℓ) = (Ioo u v).indicator (fun _ => (1 : ℝ)) t := by
    filter_upwards [(Set.countable_singleton (ℓ.val / 2)).ae_notMem volume] with t ht hI
    rw [Set.uIoc_of_le (by linarith)] at hI
    have htI : t ∈ Ico (-(ℓ.val / 2)) (ℓ.val / 2) :=
      ⟨by linarith [hI.1], lt_of_le_of_ne hI.2 (fun h => ht (Set.mem_singleton_iff.2 h))⟩
    unfold periodicIndicator
    rw [centralRep_coe_of_mem ℓ htI]
  rw [intervalIntegral.integral_congr_ae hae, intervalIntegral.integral_of_le (by linarith),
    setIntegral_indicator measurableSet_Ioo, Set.inter_eq_right.mpr hsub, setIntegral_const,
    Measure.real, Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith), smul_eq_mul, mul_one]

/-- The periodized indicator with its mean removed, on the central cell of length `ℓ`. -/
lemma integral_centred_periodicIndicator (ℓ : Length) (hℓ : 1 ≤ ℓ.val) {u v : ℝ}
    (hu : -(1 / 2) < u) (huv : u < v) (hv : v < 1 / 2) :
    ∫ t in (0 : ℝ)..ℓ.val, (periodicIndicator ℓ u v (t : Circle ℓ) - (v - u) / ℓ.val) = 0 := by
  have hℓ0 : 0 < ℓ.val := by linarith
  rw [intervalIntegral.integral_sub (intervalIntegrable_periodicIndicator ℓ u v 0 ℓ.val)
    intervalIntegrable_const, integral_periodicIndicator_period ℓ hℓ hu huv hv,
    intervalIntegral.integral_const, smul_eq_mul]
  field_simp
  ring

/-- The centred periodized indicator is bounded by one. -/
lemma abs_centred_periodicIndicator_le (ℓ : Length) (hℓ : 1 ≤ ℓ.val) {u v : ℝ}
    (hu : -(1 / 2) < u) (huv : u < v) (hv : v < 1 / 2) (t : ℝ) :
    |periodicIndicator ℓ u v (t : Circle ℓ) - (v - u) / ℓ.val| ≤ 1 := by
  have hℓ0 : 0 < ℓ.val := by linarith
  have hc0 : 0 ≤ (v - u) / ℓ.val := div_nonneg (by linarith) hℓ0.le
  have hc1 : (v - u) / ℓ.val ≤ 1 := (div_le_one hℓ0).2 (by linarith)
  have h := periodicIndicator_mem_Icc ℓ u v t
  rw [abs_le]
  constructor <;> linarith [h.1, h.2]

/-- The centred periodized indicator is dominated by the uncentred one plus its mean, pointwise. -/
lemma abs_centred_periodicIndicator_le_add (ℓ : Length) (hℓ : 1 ≤ ℓ.val) {u v : ℝ}
    (hu : -(1 / 2) < u) (huv : u < v) (hv : v < 1 / 2) (t : ℝ) :
    |periodicIndicator ℓ u v (t : Circle ℓ) - (v - u) / ℓ.val| ≤
      periodicIndicator ℓ u v (t : Circle ℓ) + (v - u) / ℓ.val := by
  have hℓ0 : 0 < ℓ.val := by linarith
  have hc0 : 0 ≤ (v - u) / ℓ.val := div_nonneg (by linarith) hℓ0.le
  have h := periodicIndicator_mem_Icc ℓ u v t
  rw [abs_le]
  constructor <;> linarith [h.1, h.2]

/-- The integral of the absolute value of the centred periodized indicator is at most `2 (v - u)`. -/
lemma integral_abs_centred_periodicIndicator_le (ℓ : Length) (hℓ : 1 ≤ ℓ.val) {u v : ℝ}
    (hu : -(1 / 2) < u) (huv : u < v) (hv : v < 1 / 2) :
    ∫ t in (0 : ℝ)..ℓ.val, |periodicIndicator ℓ u v (t : Circle ℓ) - (v - u) / ℓ.val| ≤
      2 * (v - u) := by
  have hℓ0 : 0 < ℓ.val := by linarith
  have hmeas : Measurable (fun t : ℝ => |periodicIndicator ℓ u v (t : Circle ℓ) - (v - u) / ℓ.val|) :=
    continuous_abs.measurable.comp ((measurable_periodicIndicator ℓ u v).sub measurable_const)
  have hint_abs : IntervalIntegrable
      (fun t : ℝ => |periodicIndicator ℓ u v (t : Circle ℓ) - (v - u) / ℓ.val|) volume 0 ℓ.val :=
    intervalIntegrable_of_bounded_measurable hmeas zero_le_one
      (fun t => by
        rw [abs_abs]
        exact abs_centred_periodicIndicator_le ℓ hℓ hu huv hv t) 0 ℓ.val
  have hint_add : IntervalIntegrable
      (fun t : ℝ => periodicIndicator ℓ u v (t : Circle ℓ) + (v - u) / ℓ.val) volume 0 ℓ.val :=
    (intervalIntegrable_periodicIndicator ℓ u v 0 ℓ.val).add intervalIntegrable_const
  calc ∫ t in (0 : ℝ)..ℓ.val, |periodicIndicator ℓ u v (t : Circle ℓ) - (v - u) / ℓ.val|
      ≤ ∫ t in (0 : ℝ)..ℓ.val, (periodicIndicator ℓ u v (t : Circle ℓ) + (v - u) / ℓ.val) :=
        intervalIntegral.integral_mono_on hℓ0.le hint_abs hint_add
          (fun t _ => abs_centred_periodicIndicator_le_add ℓ hℓ hu huv hv t)
    _ = 2 * (v - u) := by
        rw [intervalIntegral.integral_add (intervalIntegrable_periodicIndicator ℓ u v 0 ℓ.val)
          intervalIntegrable_const, integral_periodicIndicator_period ℓ hℓ hu huv hv,
          intervalIntegral.integral_const, smul_eq_mul]
        field_simp
        ring

/-- The periodized indicator is measurable on the circle. -/
lemma measurable_periodicIndicator_circle (ℓ : Length) (u v : ℝ) :
    Measurable (periodicIndicator ℓ u v) := by
  have : Fact (0 < ℓ.val) := ⟨ℓ.property⟩
  unfold periodicIndicator centralRep
  exact (measurable_const.indicator measurableSet_Ioo).comp
    (measurable_subtype_coe.comp (AddCircle.measurableEquivIco ℓ.val (-ℓ.val / 2)).measurable)

/-- The periodized indicator takes values in `[0, 1]` at every point of the circle. -/
lemma periodicIndicator_bounds (ℓ : Length) (u v : ℝ) (z : Circle ℓ) :
    |periodicIndicator ℓ u v z| ≤ 1 := by
  unfold periodicIndicator
  by_cases h : centralRep ℓ z ∈ Ioo u v
  · rw [Set.indicator_of_mem h, abs_one]
  · rw [Set.indicator_of_notMem h, abs_zero]
    exact zero_le_one

/-- Removing a constant changes no nonzero Fourier coefficient of a bounded measurable function
on the circle `AddCircle ℓ`. -/
lemma fourierCoeff_sub_const_of_ne_zero {ℓ : ℝ} [Fact (0 < ℓ)] (g : AddCircle ℓ → ℝ)
    (hg : Measurable g) {B : ℝ} (hB : ∀ z, |g z| ≤ B) (c : ℝ) {k : ℤ} (hk : k ≠ 0) :
    fourierCoeff (fun z => ((g z - c : ℝ) : ℂ)) k = fourierCoeff (fun z => (g z : ℂ)) k := by
  have hfour_le : ∀ z : AddCircle ℓ, ‖fourier (-k) z‖ ≤ 1 := fun z =>
    (ContinuousMap.norm_coe_le_norm (fourier (-k)) z).trans (fourier_norm (-k)).le
  have hfour : Integrable (fun z : AddCircle ℓ => fourier (-k) z) AddCircle.haarAddCircle :=
    Integrable.of_bound (fourier (-k)).continuous.aestronglyMeasurable 1
      (ae_of_all _ hfour_le)
  have hgC : Integrable (fun z : AddCircle ℓ => fourier (-k) z • (g z : ℂ))
      AddCircle.haarAddCircle :=
    Integrable.of_bound
      (((fourier (-k)).continuous.measurable.smul (Complex.measurable_ofReal.comp hg)).aestronglyMeasurable)
      B (ae_of_all _ fun z => by
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
        exact (mul_le_mul_of_nonneg_right (hfour_le z) (abs_nonneg _)).trans
          (by rw [one_mul]; exact hB z))
  have hzero : ∫ z : AddCircle ℓ, fourier (-k) z ∂AddCircle.haarAddCircle = 0 := by
    have h0 : fourierCoeff (fun z : AddCircle ℓ => fourier (0 : ℤ) z) k = 0 := by
      have : (fun z : AddCircle ℓ => fourier (0 : ℤ) z) = ⇑(fourier (0 : ℤ)) := rfl
      rw [this, fourierCoeff_fourier]
      simp [hk]
    simp only [fourierCoeff, fourier_zero, smul_eq_mul, mul_one] at h0
    exact h0
  simp only [fourierCoeff]
  have e : (fun z : AddCircle ℓ => fourier (-k) z • ((g z - c : ℝ) : ℂ)) =
      fun z => fourier (-k) z • (g z : ℂ) - (c : ℂ) • fourier (-k) z := by
    funext z
    simp only [Complex.ofReal_sub, smul_eq_mul]
    ring
  have hcf : Integrable (fun z : AddCircle ℓ => (c : ℂ) • fourier (-k) z)
      AddCircle.haarAddCircle := hfour.smul (c : ℂ)
  rw [e, integral_sub hgC hcf, integral_smul, hzero, smul_zero, sub_zero]

/-- The periodized indicator on an enlarged circle has a `1`-Lipschitz, uniformly bounded
primitive. Its derivative is the centred periodized indicator, and its Fourier coefficients
agree with those of the periodized indicator at every nonzero mode. -/
theorem exists_compact_indicator_primitive (ℓ : Length) [Fact (0 < ℓ.val)] (hℓ : 1 ≤ ℓ.val)
    {u v : ℝ} (hu : -(1 / 2) < u) (huv : u < v) (hv : v < 1 / 2) :
    ∃ G : Circle ℓ → ℝ, Continuous G ∧ (∀ z, |G z| ≤ 2 * (v - u)) ∧
      (∀ z w, |G z - G w| ≤ dist z w) ∧
      ∀ k : ℤ, k ≠ 0 →
        (2 * Real.pi * Complex.I * (k : ℂ) / ℓ.val) * fourierCoeff (fun z => (G z : ℂ)) k =
          fourierCoeff (fun z => (periodicIndicator ℓ u v z : ℂ)) k := by
  have hℓ0 : 0 < ℓ.val := by linarith
  set c : ℝ := (v - u) / ℓ.val with hc
  set fc : ℝ → ℝ := fun t => periodicIndicator ℓ u v (t : Circle ℓ) - c with hfc
  have hper : Function.Periodic fc ℓ.val := by
    intro t
    show periodicIndicator ℓ u v ((t + ℓ.val : ℝ) : Circle ℓ) - c =
      periodicIndicator ℓ u v (t : Circle ℓ) - c
    rw [AddCircle.coe_add_period]
  have hfm : Measurable fc := (measurable_periodicIndicator ℓ u v).sub measurable_const
  have hfi : IntervalIntegrable fc volume 0 ℓ.val :=
    (intervalIntegrable_periodicIndicator ℓ u v 0 ℓ.val).sub intervalIntegrable_const
  have hfz : ∫ t in (0 : ℝ)..ℓ.val, fc t = 0 := integral_centred_periodicIndicator ℓ hℓ hu huv hv
  have hfb : ∀ t, |fc t| ≤ 1 := fun t => abs_centred_periodicIndicator_le ℓ hℓ hu huv hv t
  have hfM : ∫ t in (0 : ℝ)..ℓ.val, |fc t| ≤ 2 * (v - u) :=
    integral_abs_centred_periodicIndicator_le ℓ hℓ hu huv hv
  have hS := countable_periodicIndicator_marks ℓ u v
  have hcont : ∀ t ∉ {t : ℝ | ∃ k : ℤ, t = u + k * ℓ.val ∨ t = v + k * ℓ.val ∨
      t = (k + 1 / 2) * ℓ.val}, ContinuousAt fc t :=
    fun t ht => (continuousAt_periodicIndicator hℓ ht).sub continuousAt_const
  obtain ⟨G, hGc, hGb, hGL, -, hF⟩ :=
    exists_bounded_periodic_primitive hper hfm hfi hfz hfb hfM hS hcont
  refine ⟨G, hGc, hGb, fun z w => ?_, fun k hk => ?_⟩
  · have h := hGL z w
    rwa [one_mul] at h
  · have hlift : ∀ z : Circle ℓ, hper.lift z = periodicIndicator ℓ u v z - c := by
      intro z
      obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective z
      exact hper.lift_coe t
    have hfun : (fun x : Circle ℓ => ((hper.lift x : ℝ) : ℂ)) =
        fun x => ((periodicIndicator ℓ u v x - c : ℝ) : ℂ) := by
      funext x
      rw [hlift x]
    rw [hF k, hfun]
    exact fourierCoeff_sub_const_of_ne_zero (ℓ := ℓ.val) (periodicIndicator ℓ u v)
      (measurable_periodicIndicator_circle ℓ u v) (B := 1) (periodicIndicator_bounds ℓ u v) c hk

end Riesz1

end
