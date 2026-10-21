/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.PeriodicScaledMarkCutoff
public import Riesz1.ToMathlib.FiniteMarkDistance
public import Mathlib.Topology.Instances.AddCircle.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Function.Floor

/-!
# The actual near and far errors

The moving cutoff is the sum of the periodic
bumps of inner radius `2h`. The fixed cutoffs use inner radius `r₀`.
All three errors are functions on the circle, with their literal product
formulas everywhere. Their sum is the original error pointwise, including
at marks for any chosen measurable representative.
-/

@[expose] public section

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace Riesz1

/-- The finite sum of the existing periodic cutoffs, descended to the circle. -/
def microCutoffSum {ι : Type*} [Fintype ι] (L r : ℝ) (a : ι → ℝ) : AddCircle L → ℝ :=
  (show Function.Periodic (fun x => ∑ j, markCut (cutoffBump r) L (a j) x) L from
    fun x => Finset.sum_congr rfl (fun j _ => by
      unfold markCut cutRep
      by_cases hL : L = 0
      · simp [hL]
      · have he : x + L - a j = (x - a j) + (1 : ℤ) * L := by simp; ring
        rw [he]
        rw [add_div, mul_div_cancel_right₀ _ hL, round_add_intCast]
        push_cast
        congr 1
        ring)).lift

theorem microCutoffSum_coe {ι : Type*} [Fintype ι] (L r : ℝ) (a : ι → ℝ) (x : ℝ) :
    microCutoffSum L r a (x : AddCircle L) = ∑ j, markCut (cutoffBump r) L (a j) x :=
  Function.Periodic.lift_coe _ x

/-- The near error `χ_h e`. -/
def microNearError {ι : Type*} [Fintype ι] (L h : ℝ) (a : ι → ℝ)
    (e : AddCircle L → ℝ) (x : AddCircle L) : ℝ :=
  microCutoffSum L (2*h) a x * e x

/-- The far error at the `j`th fixed mark, `χ_j (1-χ_h) e`. -/
def microFarError {ι : Type*} [Fintype ι] (L r₀ h : ℝ) (a : ι → ℝ)
    (e : AddCircle L → ℝ) (j : ι) (x : AddCircle L) : ℝ :=
  microCutoffSum L r₀ (fun _ : Unit => a j) x *
    (1 - microCutoffSum L (2*h) a x) * e x

/-- The smooth remainder away from the fixed marked neighborhoods. -/
def microFarRemainder {ι : Type*} [Fintype ι] (L r₀ h : ℝ) (a : ι → ℝ)
    (e : AddCircle L → ℝ) (x : AddCircle L) : ℝ :=
  (1 - microCutoffSum L r₀ a x) * (1 - microCutoffSum L (2*h) a x) * e x

namespace Internal

/-- No regularity or separation is required for the exact partition identity. -/
theorem micro_near_far_decomposition {ι : Type*} [Fintype ι]
    (L r₀ h : ℝ) (a : ι → ℝ) (e : AddCircle L → ℝ) (x : AddCircle L) :
    microNearError L h a e x + (∑ j, microFarError L r₀ h a e j x) +
      microFarRemainder L r₀ h a e x = e x := by
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective x
  simp only [microNearError, microFarError, microFarRemainder, microCutoffSum_coe,
    Fintype.sum_unique]
  rw [← Finset.sum_mul, ← Finset.sum_mul]
  ring

theorem microCutoffSum_mem_Icc {ι : Type*} [Fintype ι] {L r : ℝ}
    (hr : 0 < r) (a : ι → ℝ)
    (hsep : ∀ i j, i ≠ j → 4*r ≤ dist (a i : AddCircle L) (a j : AddCircle L))
    (x : AddCircle L) : microCutoffSum L r a x ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective x
  rw [microCutoffSum_coe]
  exact sum_markCut_cutoffBump_mem_Icc hr a hsep t

theorem microCutoffSum_eq_one {ι : Type*} [Fintype ι] {L r : ℝ}
    (hr : 0 < r) (a : ι → ℝ)
    (hsep : ∀ i j, i ≠ j → 4*r ≤ dist (a i : AddCircle L) (a j : AddCircle L))
    {x : AddCircle L} (j : ι) (hx : dist x (a j : AddCircle L) ≤ r) :
    microCutoffSum L r a x = 1 := by
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective x
  rw [microCutoffSum_coe]
  exact sum_markCut_cutoffBump_eq_one hr a hsep j hx

theorem microCutoffSum_eq_zero {ι : Type*} [Fintype ι] {L r : ℝ}
    (hr : 0 < r) (a : ι → ℝ) {x : AddCircle L}
    (hx : ∀ j, 2*r ≤ dist x (a j : AddCircle L)) : microCutoffSum L r a x = 0 := by
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective x
  rw [microCutoffSum_coe]
  exact sum_markCut_cutoffBump_eq_zero hr a hx

/-- The near error is supported in the actual `4h` profile neighborhoods. -/
theorem microNearError_eq_zero_of_far {ι : Type*} [Fintype ι] {L h : ℝ}
    (hh : 0 < h) (a : ι → ℝ) (e : AddCircle L → ℝ) {x : AddCircle L}
    (hx : ∀ j, 4*h ≤ dist x (a j : AddCircle L)) : microNearError L h a e x = 0 := by
  unfold microNearError
  rw [microCutoffSum_eq_zero (by positivity) a (by simpa only [show 2*(2*h) = 4*h by ring] using hx), zero_mul]

/-- Every far error vanishes in every `2h` inner neighborhood. -/
theorem microFarErrors_eq_zero_of_near {ι : Type*} [Fintype ι] {L r₀ h : ℝ}
    (hh : 0 < h) (a : ι → ℝ)
    (hsep : ∀ i j, i ≠ j → 8*h ≤ dist (a i : AddCircle L) (a j : AddCircle L))
    (e : AddCircle L → ℝ) {x : AddCircle L} (j : ι)
    (hx : dist x (a j : AddCircle L) ≤ 2*h) :
    (∀ k, microFarError L r₀ h a e k x = 0) ∧ microFarRemainder L r₀ h a e x = 0 := by
  have hone := microCutoffSum_eq_one (by positivity : 0 < 2*h) a
    (by simpa only [show 4*(2*h) = 8*h by ring] using hsep) j hx
  simp only [microFarError, microFarRemainder, hone, sub_self, mul_zero, zero_mul,
    implies_true, and_self]

theorem microFarError_eq_zero_of_far {ι : Type*} [Fintype ι] {L r₀ h : ℝ}
    (hr : 0 < r₀) (a : ι → ℝ) (e : AddCircle L → ℝ) (j : ι) {x : AddCircle L}
    (hx : 2*r₀ ≤ dist x (a j : AddCircle L)) : microFarError L r₀ h a e j x = 0 := by
  unfold microFarError
  rw [microCutoffSum_eq_zero hr (fun _ : Unit => a j) (fun _ => hx), zero_mul, zero_mul]

theorem microNearError_abs_le {ι : Type*} [Fintype ι] {L h : ℝ}
    (hh : 0 < h) (a : ι → ℝ)
    (hsep : ∀ i j, i ≠ j → 8*h ≤ dist (a i : AddCircle L) (a j : AddCircle L))
    (e : AddCircle L → ℝ) (x : AddCircle L) : |microNearError L h a e x| ≤ |e x| := by
  have hb := microCutoffSum_mem_Icc (by positivity : 0 < 2*h) a
    (by simpa only [show 4*(2*h) = 8*h by ring] using hsep) x
  rw [microNearError, abs_mul, abs_of_nonneg hb.1]
  exact mul_le_of_le_one_left (abs_nonneg _) hb.2

theorem microCutoffSum_contDiff {ι : Type*} [Fintype ι] {L r : ℝ}
    (hL : 0 < L) (hr : 0 < r) (hroom : 4*r < L) (a : ι → ℝ) :
    ContDiff ℝ ∞ (fun x : ℝ => microCutoffSum L r a (x : AddCircle L)) := by
  simp_rw [microCutoffSum_coe]
  exact ContDiff.sum (fun j _ => contDiff_markCut_cutoffBump hL hr hroom (a j))

theorem microCutoffSum_continuous {ι : Type*} [Fintype ι] {L r : ℝ}
    (hL : 0 < L) (hr : 0 < r) (hroom : 4*r < L) (a : ι → ℝ) :
    Continuous (microCutoffSum L r a) :=
  (QuotientAddGroup.isQuotientMap_mk _).continuous_iff.2
    (microCutoffSum_contDiff hL hr hroom a).continuous

/-- Measurability holds even when the cutoff radius is larger than the circle. -/
theorem microCutoffSum_measurable {ι : Type*} [Fintype ι] {L : ℝ}
    (hL : 0 < L) (r : ℝ) (a : ι → ℝ) : Measurable (microCutoffSum L r a) := by
  have : Fact (0 < L) := ⟨hL⟩
  have hround : Measurable (round : ℝ → ℤ) := by
    change Measurable (fun x : ℝ => round x)
    simp_rw [round_eq]
    exact (measurable_id.add_const (1/2 : ℝ)).floor
  have hcast : Measurable (fun z : ℤ => (z : ℝ)) := measurable_of_countable _
  have hl : Measurable (fun x : ℝ => ∑ j, markCut (cutoffBump r) L (a j) x) := by
    apply Finset.measurable_sum
    intro j _
    unfold markCut
    apply (contDiff_cutoffBump r).continuous.measurable.comp
    unfold cutRep
    exact (measurable_id.sub_const _).sub
      (((hcast.comp hround).comp ((measurable_id.sub_const _).div_const L)).const_mul L)
  have he : microCutoffSum L r a = fun x =>
      ∑ j, markCut (cutoffBump r) L (a j) (AddCircle.measurableEquivIoc L 0 x).val := by
    funext x
    have hh := microCutoffSum_coe L r a (AddCircle.measurableEquivIoc L 0 x).val
    rw [show (((AddCircle.measurableEquivIoc L 0 x).val : ℝ) : AddCircle L) = x from
      AddCircle.coe_equivIoc] at hh
    exact hh
  rw [he]
  exact hl.comp (measurable_subtype_coe.comp (AddCircle.measurableEquivIoc L 0).measurable)

/-- An arbitrary differentiable representative off the marks yields globally
differentiable far pieces: the missing values lie in open zero regions. -/
theorem microFarErrors_differentiable {ι : Type*} [Fintype ι] {L r₀ h : ℝ}
    (hL : 0 < L) (hr : 0 < r₀) (hh : 0 < h) (hrL : 4*r₀ < L) (hhL : 8*h < L)
    (a : ι → ℝ)
    (hsep : ∀ i j, i ≠ j → 8*h ≤ dist (a i : AddCircle L) (a j : AddCircle L))
    (e : AddCircle L → ℝ)
    (he : ∀ x : ℝ, (∀ j, (x : AddCircle L) ≠ (a j : AddCircle L)) →
      DifferentiableAt ℝ (fun t : ℝ => e (t : AddCircle L)) x) :
    (∀ j, Differentiable ℝ (fun x : ℝ => microFarError L r₀ h a e j (x : AddCircle L))) ∧
      Differentiable ℝ (fun x : ℝ => microFarRemainder L r₀ h a e (x : AddCircle L)) := by
  have hmove := microCutoffSum_contDiff hL (by positivity : 0 < 2*h) (by linarith) a
  have hfixed := microCutoffSum_contDiff hL hr hrL a
  have hsingle (j : ι) := microCutoffSum_contDiff hL hr hrL (fun _ : Unit => a j)
  have hzero {x : ℝ} (j : ι) (hx : (x : AddCircle L) = (a j : AddCircle L)) :
      ∀ᶠ (t : ℝ) in 𝓝 x, microCutoffSum L (2*h) a (t : AddCircle L) = 1 := by
    have hc : Continuous (fun t : ℝ => dist (t : AddCircle L) (a j : AddCircle L)) := by
      fun_prop
    have hd : dist (x : AddCircle L) (a j : AddCircle L) < 2*h := by rw [hx, dist_self]; positivity
    filter_upwards [(hc.tendsto x).eventually (Iio_mem_nhds hd)] with t ht
    exact microCutoffSum_eq_one (by positivity) a (by simpa only [show 4*(2*h) = 8*h by ring] using hsep) j ht.le
  constructor
  · intro j x
    by_cases hx : ∀ k, (x : AddCircle L) ≠ (a k : AddCircle L)
    · exact (((hsingle j).differentiable (by simp) x).mul
        ((differentiableAt_const 1).sub (hmove.differentiable (by simp) x))).mul (he x hx)
    · push Not at hx
      obtain ⟨k, hk⟩ := hx
      have hz : (fun t : ℝ => microFarError L r₀ h a e j (t : AddCircle L)) =ᶠ[𝓝 x]
          fun _ => 0 := by
        filter_upwards [hzero k hk] with t ht
        simp [microFarError, ht]
      exact (differentiableAt_const (0 : ℝ)).congr_of_eventuallyEq hz
  · intro x
    by_cases hx : ∀ k, (x : AddCircle L) ≠ (a k : AddCircle L)
    · exact (((differentiableAt_const 1).sub (hfixed.differentiable (by simp) x)).mul
        ((differentiableAt_const 1).sub (hmove.differentiable (by simp) x))).mul (he x hx)
    · push Not at hx
      obtain ⟨k, hk⟩ := hx
      have hz : (fun t : ℝ => microFarRemainder L r₀ h a e (t : AddCircle L)) =ᶠ[𝓝 x]
          fun _ => 0 := by
        filter_upwards [hzero k hk] with t ht
        simp [microFarRemainder, ht]
      exact (differentiableAt_const (0 : ℝ)).congr_of_eventuallyEq hz

/-- The same removal of marked neighborhoods preserves `C¹`
regularity when the representative is locally `C¹` off the marks. -/
theorem microFarErrors_contDiff {ι : Type*} [Fintype ι] {L r₀ h : ℝ}
    (hL : 0 < L) (hr : 0 < r₀) (hh : 0 < h) (hrL : 4*r₀ < L) (hhL : 8*h < L)
    (a : ι → ℝ)
    (hsep : ∀ i j, i ≠ j → 8*h ≤ dist (a i : AddCircle L) (a j : AddCircle L))
    (e : AddCircle L → ℝ)
    (he : ∀ x : ℝ, (∀ j, (x : AddCircle L) ≠ (a j : AddCircle L)) →
      ContDiffAt ℝ 1 (fun t : ℝ => e (t : AddCircle L)) x) :
    (∀ j, ContDiff ℝ 1 (fun x : ℝ => microFarError L r₀ h a e j (x : AddCircle L))) ∧
      ContDiff ℝ 1 (fun x : ℝ => microFarRemainder L r₀ h a e (x : AddCircle L)) := by
  have hmove := (microCutoffSum_contDiff hL (by positivity : 0 < 2*h) (by linarith) a).of_le (by norm_num : (1 : ℕ∞ω) ≤ ∞)
  have hfixed := (microCutoffSum_contDiff hL hr hrL a).of_le (by norm_num : (1 : ℕ∞ω) ≤ ∞)
  have hsingle (j : ι) := (microCutoffSum_contDiff hL hr hrL (fun _ : Unit => a j)).of_le (by norm_num : (1 : ℕ∞ω) ≤ ∞)
  have hzero {x : ℝ} (j : ι) (hx : (x : AddCircle L) = (a j : AddCircle L)) :
      ∀ᶠ (t : ℝ) in 𝓝 x, microCutoffSum L (2*h) a (t : AddCircle L) = 1 := by
    have hc : Continuous (fun t : ℝ => dist (t : AddCircle L) (a j : AddCircle L)) := by
      fun_prop
    have hd : dist (x : AddCircle L) (a j : AddCircle L) < 2*h := by rw [hx, dist_self]; positivity
    filter_upwards [(hc.tendsto x).eventually (Iio_mem_nhds hd)] with t ht
    exact microCutoffSum_eq_one (by positivity) a (by simpa only [show 4*(2*h) = 8*h by ring] using hsep) j ht.le
  constructor
  · intro j
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : ∀ k, (x : AddCircle L) ≠ (a k : AddCircle L)
    · exact (((hsingle j).contDiffAt).mul
        (contDiffAt_const.sub (hmove.contDiffAt))).mul (he x hx)
    · push Not at hx
      obtain ⟨k, hk⟩ := hx
      have hz : (fun t : ℝ => microFarError L r₀ h a e j (t : AddCircle L)) =ᶠ[𝓝 x]
          fun _ => 0 := by
        filter_upwards [hzero k hk] with t ht
        simp [microFarError, ht]
      exact contDiffAt_const.congr_of_eventuallyEq hz
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : ∀ k, (x : AddCircle L) ≠ (a k : AddCircle L)
    · exact ((contDiffAt_const.sub (hfixed.contDiffAt)).mul
        (contDiffAt_const.sub (hmove.contDiffAt))).mul (he x hx)
    · push Not at hx
      obtain ⟨k, hk⟩ := hx
      have hz : (fun t : ℝ => microFarRemainder L r₀ h a e (t : AddCircle L)) =ᶠ[𝓝 x]
          fun _ => 0 := by
        filter_upwards [hzero k hk] with t ht
        simp [microFarRemainder, ht]
      exact contDiffAt_const.congr_of_eventuallyEq hz

end Internal
end Riesz1

end
