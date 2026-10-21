/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.Analysis.Convex.Continuous
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
public import Mathlib.Order.Filter.AtTopBot.Field

/-!
# Single-gap integration by parts

Let `0 < N`, `0 < β`, `0 < s`, and let `V` be convex on `(0, N)`. Let `f y = exp (-2 β y ^ (-s) - V y)`
on `(0, N)`, with `f y ≤ C exp (-2 β (y ^ (-s) + (N - y) ^ (-s)))` there. This file proves the
integration by parts identity of [Boursier, *Optimal local laws and central limit theorem for the
circular Riesz gas*, Lemma 4.5]: for `q > 0` and `h` differentiable on `(0, N)`
with `|h y| ≤ A (1 + y ^ (-q))` and `|h' y| ≤ A (1 + y ^ (-q - 1))`, the functions `h' f` and
`h (V'₊ - 2 β s y ^ (-s - 1)) f` are integrable on `(0, N)`, and their integrals agree. Here
`V'₊ y = derivWithin V (Ioi y) y` is the right derivative of `V`.

The proof has three parts. First, the right derivative of `V` is monotone, so the factor
`w y = V'₊ y - 2 β s y ^ (-s - 1)` is monotone. Hence `w` changes sign once, at its supremum `m`.
Second, on each sign piece the function `w G` with `G y = (1 + y ^ (-q)) f y` is a derivative up to
an integrable term, which bounds `∫ |w G|` uniformly on subintervals of `(0, N)`. Third, the
integration by parts identity on `[a, b]` passes to the limit `a ↓ 0`, `b ↑ N`, where the boundary
terms vanish by the endpoint limits of `f`.
-/

public section

open MeasureTheory Set Filter Topology

namespace Riesz1


lemma gap_exp_neg_mul_le {γ p : ℝ} (hγ : 0 < γ) (hp : 0 ≤ p) :
    ∃ K : ℝ, 0 < K ∧ ∀ t : ℝ, 0 < t → Real.exp (-γ * t) ≤ K * t ^ (-p) := by
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.1
    ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero p γ hγ).eventually (gt_mem_nhds one_pos))
  set S : ℝ := max T 1 with hS
  have hSpos : 0 < S := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hSp : 0 ≤ S ^ p := Real.rpow_nonneg hSpos.le p
  have hbound : ∀ t : ℝ, 0 < t → t ^ p * Real.exp (-γ * t) ≤ 1 + S ^ p := by
    intro t ht
    rcases le_or_gt T t with htT | htT
    · linarith [hT t htT]
    · have h1 : t ^ p ≤ S ^ p := Real.rpow_le_rpow ht.le (htT.le.trans (le_max_left _ _)) hp
      have h2 : Real.exp (-γ * t) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
      have h3 : 0 ≤ t ^ p := Real.rpow_nonneg ht.le p
      nlinarith [Real.exp_pos (-γ * t)]
  refine ⟨1 + S ^ p, by linarith, fun t ht => ?_⟩
  have hpos : t ^ p ≠ 0 := (Real.rpow_pos_of_pos ht p).ne'
  have key : Real.exp (-γ * t) = (t ^ p * Real.exp (-γ * t)) * t ^ (-p) := by
    rw [Real.rpow_neg ht.le]
    field_simp
  rw [key]
  exact mul_le_mul_of_nonneg_right (hbound t ht) (Real.rpow_nonneg ht.le _)

lemma gap_C_nonneg {N β s C : ℝ} {V f : ℝ → ℝ} (hN : 0 < N)
    (hf : ∀ y ∈ Ioo 0 N, f y = Real.exp (-2 * β * y ^ (-s) - V y))
    (hC : ∀ y ∈ Ioo 0 N, f y ≤ C * Real.exp (-2 * β * (y ^ (-s) + (N - y) ^ (-s)))) :
    0 ≤ C := by
  have hmem : N / 2 ∈ Ioo 0 N := ⟨by positivity, by linarith⟩
  have h0 : 0 < f (N / 2) := by rw [hf _ hmem]; exact Real.exp_pos _
  have h1 := hC _ hmem
  by_contra hneg
  have hneg' : C < 0 := lt_of_not_ge hneg
  have := mul_neg_of_neg_of_pos hneg' (Real.exp_pos (-2 * β * ((N / 2) ^ (-s) + (N - N / 2) ^ (-s))))
  linarith

lemma gap_f_continuousOn {N β s : ℝ} {V f : ℝ → ℝ}
    (hV : ConvexOn ℝ (Ioo 0 N) V)
    (hf : ∀ y ∈ Ioo 0 N, f y = Real.exp (-2 * β * y ^ (-s) - V y)) :
    ContinuousOn f (Ioo 0 N) := by
  have hpow : ContinuousOn (fun y : ℝ => -2 * β * y ^ (-s)) (Ioo 0 N) := fun y hy =>
    (continuousAt_const.mul (Real.continuousAt_rpow_const y (-s) (Or.inl hy.1.ne'))).continuousWithinAt
  have hVc : ContinuousOn V (Ioo 0 N) := by
    have := hV.continuousOn_interior
    rwa [interior_Ioo] at this
  have hexp : ContinuousOn (fun y : ℝ => Real.exp (-2 * β * y ^ (-s) - V y)) (Ioo 0 N) :=
    Real.continuous_exp.comp_continuousOn (hpow.sub hVc)
  exact hexp.congr hf

lemma gap_f_pos {N β s : ℝ} {V f : ℝ → ℝ}
    (hf : ∀ y ∈ Ioo 0 N, f y = Real.exp (-2 * β * y ^ (-s) - V y)) :
    ∀ y ∈ Ioo 0 N, 0 < f y := fun y hy => by
  rw [hf y hy]; exact Real.exp_pos _

lemma gap_f_le_C {N β s C : ℝ} {f : ℝ → ℝ} (hβ : 0 < β) (hC0 : 0 ≤ C)
    (hC : ∀ y ∈ Ioo 0 N, f y ≤ C * Real.exp (-2 * β * (y ^ (-s) + (N - y) ^ (-s)))) :
    ∀ y ∈ Ioo 0 N, f y ≤ C := by
  intro y hy
  have hA : 0 ≤ y ^ (-s) := Real.rpow_nonneg hy.1.le _
  have hB : 0 ≤ (N - y) ^ (-s) := Real.rpow_nonneg (sub_pos.2 hy.2).le _
  have hE : Real.exp (-2 * β * (y ^ (-s) + (N - y) ^ (-s))) ≤ 1 :=
    Real.exp_le_one_iff.2 (by nlinarith)
  exact (hC y hy).trans (mul_le_of_le_one_right hC0 hE)

lemma gap_f_le_exp {N β s C : ℝ} {f : ℝ → ℝ} (hβ : 0 < β)
    (hC : ∀ y ∈ Ioo 0 N, f y ≤ C * Real.exp (-2 * β * (y ^ (-s) + (N - y) ^ (-s)))) (hC0 : 0 ≤ C) :
    ∀ y ∈ Ioo 0 N, f y ≤ C * Real.exp (-2 * β * y ^ (-s)) := by
  intro y hy
  have hB : 0 ≤ (N - y) ^ (-s) := Real.rpow_nonneg (sub_pos.2 hy.2).le _
  have hE : Real.exp (-2 * β * (y ^ (-s) + (N - y) ^ (-s))) ≤ Real.exp (-2 * β * y ^ (-s)) :=
    Real.exp_le_exp.2 (by nlinarith)
  exact (hC y hy).trans (mul_le_mul_of_nonneg_left hE hC0)

lemma gap_rpow_mul_f_le {N β s C r : ℝ} {f : ℝ → ℝ} (hs : 0 < s) (hβ : 0 < β)
    (hr : 0 ≤ r) (hC0 : 0 ≤ C)
    (hC : ∀ y ∈ Ioo 0 N, f y ≤ C * Real.exp (-2 * β * y ^ (-s))) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y ∈ Ioo 0 N, y ^ (-r) * f y ≤ M * y := by
  obtain ⟨K, hK0, hK⟩ := gap_exp_neg_mul_le (γ := 2 * β) (p := (r + 1) / s)
    (by positivity) (by positivity)
  refine ⟨C * K, mul_nonneg hC0 hK0.le, fun y hy => ?_⟩
  have hyp : 0 < y := hy.1
  have ht : 0 < y ^ (-s) := Real.rpow_pos_of_pos hyp _
  have hexp : Real.exp (-2 * β * y ^ (-s)) ≤ K * y ^ (r + 1) := by
    have h1 := hK (y ^ (-s)) ht
    have h2 : -2 * β * y ^ (-s) = -(2 * β) * y ^ (-s) := by ring
    have h3 : (y ^ (-s)) ^ (-((r + 1) / s)) = y ^ (r + 1) := by
      rw [← Real.rpow_mul hyp.le]
      congr 1
      field_simp
    rw [h2]
    rw [h3] at h1
    exact h1
  have hyr : y ^ (-r) * y ^ (r + 1) = y := by
    rw [← Real.rpow_add hyp]
    norm_num
  calc y ^ (-r) * f y ≤ y ^ (-r) * (C * Real.exp (-2 * β * y ^ (-s))) :=
        mul_le_mul_of_nonneg_left (hC y hy) (Real.rpow_nonneg hyp.le _)
    _ ≤ y ^ (-r) * (C * (K * y ^ (r + 1))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp hC0)
          (Real.rpow_nonneg hyp.le _)
    _ = C * K * (y ^ (-r) * y ^ (r + 1)) := by ring
    _ = C * K * y := by rw [hyr]


/-- Endpoint zero at the left: `f y → 0` as `y ↓ 0`. -/
lemma gap_f_tendsto_zero_left {N β s C : ℝ} {f : ℝ → ℝ} (hN : 0 < N) (hs : 0 < s) (hβ : 0 < β)
    (hf : ∀ y ∈ Ioo 0 N, 0 < f y)
    (hC : ∀ y ∈ Ioo 0 N, f y ≤ C * Real.exp (-2 * β * y ^ (-s))) :
    Tendsto f (𝓝[>] 0) (𝓝 0) := by
  have hpow : Tendsto (fun y : ℝ => y ^ (-s)) (𝓝[>] 0) atTop :=
    tendsto_rpow_neg_nhdsGT_zero (by linarith)
  have hlin : Tendsto (fun y : ℝ => -(2 * β) * y ^ (-s)) (𝓝[>] 0) atBot :=
    Filter.Tendsto.const_mul_atTop_of_neg (by linarith) hpow
  have hexp : Tendsto (fun y : ℝ => Real.exp (-2 * β * y ^ (-s))) (𝓝[>] 0) (𝓝 0) := by
    refine Real.tendsto_exp_atBot.comp (hlin.congr fun y => ?_)
    ring
  have hup : Tendsto (fun y : ℝ => C * Real.exp (-2 * β * y ^ (-s))) (𝓝[>] 0) (𝓝 0) := by
    simpa using hexp.const_mul C
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [Ioo_mem_nhdsGT hN] with y hy
    exact (hf y hy).le
  · filter_upwards [Ioo_mem_nhdsGT hN] with y hy
    exact hC y hy

/-- Endpoint zero at the right: `f y → 0` as `y ↑ N`. -/
lemma gap_f_tendsto_zero_right {N β s C : ℝ} {f : ℝ → ℝ} (hN : 0 < N) (hs : 0 < s) (hβ : 0 < β)
    (hf : ∀ y ∈ Ioo 0 N, 0 < f y) (hC0 : 0 ≤ C)
    (hC : ∀ y ∈ Ioo 0 N, f y ≤ C * Real.exp (-2 * β * (y ^ (-s) + (N - y) ^ (-s)))) :
    Tendsto f (𝓝[<] N) (𝓝 0) := by
  have hcont : Tendsto (fun y : ℝ => N - y) (𝓝[<] N) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun y : ℝ => N - y) (𝓝 N) (𝓝 (N - N)) :=
        (continuous_const.sub continuous_id).tendsto N
      rw [sub_self] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with y hy
      exact sub_pos.2 (mem_Iio.1 hy)
  have hpow : Tendsto (fun y : ℝ => (N - y) ^ (-s)) (𝓝[<] N) atTop :=
    (tendsto_rpow_neg_nhdsGT_zero (by linarith)).comp hcont
  have hlin : Tendsto (fun y : ℝ => -(2 * β) * (N - y) ^ (-s)) (𝓝[<] N) atBot :=
    Filter.Tendsto.const_mul_atTop_of_neg (by linarith) hpow
  have hexp : Tendsto (fun y : ℝ => Real.exp (-2 * β * (N - y) ^ (-s))) (𝓝[<] N) (𝓝 0) := by
    refine Real.tendsto_exp_atBot.comp (hlin.congr fun y => ?_)
    ring
  have hup : Tendsto (fun y : ℝ => C * Real.exp (-2 * β * (N - y) ^ (-s))) (𝓝[<] N) (𝓝 0) := by
    simpa using hexp.const_mul C
  have hmem : Ioo (N / 2) N ∈ 𝓝[<] N := Ioo_mem_nhdsLT (by linarith)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [hmem] with y hy
    exact (hf y ⟨by linarith [hy.1], hy.2⟩).le
  · filter_upwards [hmem] with y hy
    have hy' : y ∈ Ioo 0 N := ⟨by linarith [hy.1], hy.2⟩
    refine (hC y hy').trans (mul_le_mul_of_nonneg_left ?_ hC0)
    refine Real.exp_le_exp.2 ?_
    have hA : 0 ≤ y ^ (-s) := Real.rpow_nonneg hy'.1.le _
    nlinarith


/-- The right derivative of a convex function on `(0, N)` exists at each point. -/
lemma gap_V_hasDerivWithinAt {N : ℝ} {V : ℝ → ℝ} (hV : ConvexOn ℝ (Ioo 0 N) V) {y : ℝ}
    (hy : y ∈ Ioo 0 N) : HasDerivWithinAt V (derivWithin V (Ioi y) y) (Ioi y) y := by
  have hy' : y ∈ interior (Ioo 0 N) := by rwa [interior_Ioo]
  exact hV.hasDerivWithinAt_rightDeriv_of_mem_interior hy'

/-- The right derivative of a convex function on `(0, N)` is nondecreasing. -/
lemma gap_rightDeriv_monotoneOn {N : ℝ} {V : ℝ → ℝ} (hV : ConvexOn ℝ (Ioo 0 N) V) :
    MonotoneOn (fun y => derivWithin V (Ioi y) y) (Ioo 0 N) := by
  have := hV.monotoneOn_rightDeriv
  rwa [interior_Ioo] at this

/-- The factor `w y = V'₊ y - 2 β s y ^ (-s - 1)` is nondecreasing on `(0, N)`. -/
lemma gap_w_monotoneOn {N β s : ℝ} {V : ℝ → ℝ} (hβ : 0 < β) (hs : 0 < s)
    (hV : ConvexOn ℝ (Ioo 0 N) V) :
    MonotoneOn (fun y => derivWithin V (Ioi y) y - 2 * β * s * y ^ (-s - 1)) (Ioo 0 N) := by
  intro x hx y hy hxy
  have h1 : derivWithin V (Ioi x) x ≤ derivWithin V (Ioi y) y :=
    gap_rightDeriv_monotoneOn hV hx hy hxy
  have h2 : y ^ (-s - 1) ≤ x ^ (-s - 1) := Real.rpow_le_rpow_of_nonpos hx.1 hxy (by linarith)
  have h3 : 2 * β * s * y ^ (-s - 1) ≤ 2 * β * s * x ^ (-s - 1) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  show derivWithin V (Ioi x) x - 2 * β * s * x ^ (-s - 1) ≤
    derivWithin V (Ioi y) y - 2 * β * s * y ^ (-s - 1)
  linarith

/-- The right derivative of `f` at `y`, namely `-f y * w y`. -/
lemma gap_f_hasDerivWithinAt {N β s : ℝ} {V f : ℝ → ℝ} (hV : ConvexOn ℝ (Ioo 0 N) V)
    (hf : ∀ y ∈ Ioo 0 N, f y = Real.exp (-2 * β * y ^ (-s) - V y)) {y : ℝ} (hy : y ∈ Ioo 0 N) :
    HasDerivWithinAt f (-(f y * (derivWithin V (Ioi y) y - 2 * β * s * y ^ (-s - 1))))
      (Ioi y) y := by
  have h1 : HasDerivWithinAt (fun x : ℝ => -2 * β * x ^ (-s))
      (-2 * β * ((-s) * y ^ (-s - 1))) (Ioi y) y :=
    ((Real.hasDerivAt_rpow_const (Or.inl hy.1.ne')).const_mul (-2 * β)).hasDerivWithinAt
  have h2 := h1.sub (gap_V_hasDerivWithinAt hV hy)
  have h3 := h2.exp
  have h4 : f =ᶠ[𝓝[Ioi y] y] fun x => Real.exp (-2 * β * x ^ (-s) - V x) :=
    eventually_nhdsWithin_of_eventually_nhds
      (Filter.eventually_of_mem (Ioo_mem_nhds hy.1 hy.2) fun x hx => hf x hx)
  have h5 := h3.congr_of_eventuallyEq h4 (hf y hy)
  refine h5.congr_deriv ?_
  simp only [Pi.sub_apply]
  rw [hf y hy]
  ring

/-- The weighted function `y ↦ y ^ (-r) * f y` is integrable on `(0, N)` for each `r ≥ 0`. -/
lemma gap_integrableOn_rpow_mul_f {N β s C r : ℝ} {V f : ℝ → ℝ} (hβ : 0 < β) (hs : 0 < s)
    (hV : ConvexOn ℝ (Ioo 0 N) V)
    (hf : ∀ y ∈ Ioo 0 N, f y = Real.exp (-2 * β * y ^ (-s) - V y))
    (hr : 0 ≤ r) (hC0 : 0 ≤ C)
    (hCexp : ∀ y ∈ Ioo 0 N, f y ≤ C * Real.exp (-2 * β * y ^ (-s))) :
    IntegrableOn (fun y => y ^ (-r) * f y) (Ioo 0 N) := by
  obtain ⟨M, hM0, hM⟩ := gap_rpow_mul_f_le hs hβ hr hC0 hCexp
  have hpow : ContinuousOn (fun y : ℝ => y ^ (-r)) (Ioo 0 N) := fun y hy =>
    (Real.continuousAt_rpow_const y (-r) (Or.inl hy.1.ne')).continuousWithinAt
  have hcont : ContinuousOn (fun y => y ^ (-r) * f y) (Ioo 0 N) :=
    hpow.mul (gap_f_continuousOn hV hf)
  have hg : IntegrableOn (fun y : ℝ => M * y) (Ioo 0 N) :=
    ((continuous_const.mul continuous_id).integrableOn_Icc).mono_set Ioo_subset_Icc_self
  refine Integrable.mono' hg (hcont.aestronglyMeasurable measurableSet_Ioo) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
  have hfpos : 0 < f y := by rw [hf y hy]; exact Real.exp_pos _
  rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg hy.1.le _) hfpos.le)]
  exact hM y hy


lemma gap_uIcc_subset {N a c : ℝ} (ha : 0 < a) (hac : a ≤ c) (hc : c < N) :
    uIcc a c ⊆ Ioo 0 N := by
  intro x hx
  rw [uIcc_of_le hac] at hx
  exact ⟨lt_of_lt_of_le ha hx.1, lt_of_le_of_lt hx.2 hc⟩

/-- Sign-split bound: `∫ |w G| ≤ 2 K₁ + q ∫ Y` for a nondecreasing `w`. -/
lemma gap_sign_split {N q K₁ : ℝ} {w G Y : ℝ → ℝ} (hq : 0 < q)
    (hwm : MonotoneOn w (Ioo 0 N)) (hGc : ContinuousOn G (Ioo 0 N))
    (hG0 : ∀ y ∈ Ioo 0 N, 0 ≤ G y) (hGK : ∀ y ∈ Ioo 0 N, G y ≤ K₁)
    (hY0 : ∀ y ∈ Ioo 0 N, 0 ≤ Y y) (hYint : IntegrableOn Y (Ioo 0 N))
    (hFTC : ∀ a c : ℝ, 0 < a → a ≤ c → c < N →
      ∫ x in a..c, w x * G x = G a - G c - q * ∫ x in a..c, Y x)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < N) :
    ∫ x in a..b, |w x * G x| ≤ 2 * K₁ + q * ∫ x in Ioo 0 N, Y x := by
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = sSup {y | y ∈ Ioo 0 N ∧ w y ≤ 0} := ⟨_, rfl⟩
  have hBdd : BddAbove {y | y ∈ Ioo 0 N ∧ w y ≤ 0} := ⟨N, fun y hy => hy.1.2.le⟩
  -- `w` is positive strictly to the right of `m`
  have hwpos : ∀ y ∈ Ioo 0 N, m < y → 0 < w y := by
    intro y hy hmy
    by_contra hneg
    have hle : w y ≤ 0 := not_lt.1 hneg
    have : y ≤ m := hm ▸ le_csSup hBdd ⟨hy, hle⟩
    linarith
  -- `w` is nonpositive strictly to the left of `m`
  have hwneg : ∀ y ∈ Ioo 0 N, y < m → w y ≤ 0 := by
    intro y hy hym
    have hne : {z | z ∈ Ioo 0 N ∧ w z ≤ 0}.Nonempty := by
      by_contra hE
      rw [Set.not_nonempty_iff_eq_empty] at hE
      rw [hm, hE, Real.sSup_empty] at hym
      linarith [hy.1]
    obtain ⟨z, hz, hyz⟩ := exists_lt_of_lt_csSup hne (hm ▸ hym)
    exact (hwm hy hz.1 hyz.le).trans hz.2
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = min (max a m) b := ⟨_, rfl⟩
  have hac : a ≤ c := hc ▸ le_min (le_max_left a m) hab
  have hcb : c ≤ b := hc ▸ min_le_right _ _
  have hcN : c < N := lt_of_le_of_lt hcb hb
  have hc0 : 0 < c := lt_of_lt_of_le ha hac
  have hcmax : c ≤ max a m := hc ▸ min_le_left _ _
  -- the sign of `w` on the two pieces
  have hleft : ∀ x ∈ Ioo a c, w x ≤ 0 := by
    intro x hx
    have hxm : x < m := by
      by_contra hmx
      have h1 : max a m ≤ x := max_le hx.1.le (not_lt.1 hmx)
      have h2 : c ≤ x := hcmax.trans h1
      linarith [hx.2]
    exact hwneg x ⟨lt_trans ha hx.1, lt_trans hx.2 hcN⟩ hxm
  have hright : ∀ x ∈ Ioc c b, 0 < w x := by
    intro x hx
    have hxm : m < x := by
      by_contra hxm
      have hxm' : x ≤ m := not_lt.1 hxm
      have h1 : x ≤ max a m := hxm'.trans (le_max_right a m)
      have h2 : x ≤ c := by rw [hc]; exact le_min h1 hx.2
      linarith [hx.1]
    exact hwpos x ⟨lt_trans hc0 hx.1, lt_of_le_of_lt hx.2 hb⟩ hxm
  -- interval integrability of `w G` on the subintervals of `(0, N)`
  have hwG : ∀ u v : ℝ, 0 < u → u ≤ v → v < N →
      IntervalIntegrable (fun x => w x * G x) volume u v := by
    intro u v hu huv hv
    have hsub := gap_uIcc_subset hu huv hv
    exact (hwm.mono hsub).intervalIntegrable.mul_continuousOn (hGc.mono hsub)
  have hint1 := hwG a c ha hac hcN
  have hint2 := hwG c b hc0 hcb hb
  have hint1' : IntervalIntegrable (fun x => |w x * G x|) volume a c := hint1.abs
  have hint2' : IntervalIntegrable (fun x => |w x * G x|) volume c b := hint2.abs
  have hsplit : (∫ x in a..b, |w x * G x|) =
      (∫ x in a..c, |w x * G x|) + ∫ x in c..b, |w x * G x| := by
    rw [intervalIntegral.integral_add_adjacent_intervals hint1' hint2']
  have hL : ∫ x in a..c, |w x * G x| = ∫ x in a..c, -(w x * G x) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [(Set.countable_singleton c).ae_notMem volume] with x hxc hx
    rw [Set.uIoc_of_le hac] at hx
    have hxne : x ≠ c := by simpa using hxc
    have hxlt : x < c := lt_of_le_of_ne hx.2 hxne
    have hxI : x ∈ Ioo 0 N := ⟨lt_trans ha hx.1, lt_trans hxlt hcN⟩
    have hwx : w x ≤ 0 := hleft x ⟨hx.1, hxlt⟩
    have hGx : 0 ≤ G x := hG0 x hxI
    have hX : w x * G x ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hwx hGx
    exact abs_of_nonpos hX
  have hR : ∫ x in c..b, |w x * G x| = ∫ x in c..b, w x * G x := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with x hx
    rw [Set.uIoc_of_le hcb] at hx
    have hxI : x ∈ Ioo 0 N := ⟨lt_trans hc0 hx.1, lt_of_le_of_lt hx.2 hb⟩
    have hwx : 0 < w x := hright x ⟨hx.1, hx.2⟩
    exact abs_of_nonneg (mul_nonneg hwx.le (hG0 x hxI))
  have hFa := hFTC a c ha hac hcN
  have hFb := hFTC c b hc0 hcb hb
  rw [hsplit, hL, hR, intervalIntegral.integral_neg]
  have hIac : ∫ x in a..c, Y x ≤ ∫ x in Ioo 0 N, Y x := by
    rw [intervalIntegral.integral_of_le hac]
    refine setIntegral_mono_set hYint ?_ ?_
    · exact (ae_restrict_iff' measurableSet_Ioo).2 (ae_of_all _ fun x hx => hY0 x hx)
    · refine ae_of_all _ fun x hx => ?_
      exact ⟨lt_trans ha hx.1, lt_of_le_of_lt hx.2 hcN⟩
  have hIcb : 0 ≤ ∫ x in c..b, Y x :=
    intervalIntegral.integral_nonneg hcb fun x hx => hY0 x ⟨lt_of_lt_of_le hc0 hx.1, lt_of_le_of_lt hx.2 hb⟩
  have hqI := mul_le_mul_of_nonneg_left hIac hq.le
  have hqI' : 0 ≤ q * ∫ x in c..b, Y x := mul_nonneg hq.le hIcb
  have hGa := hG0 a ⟨ha, lt_of_le_of_lt hac hcN⟩
  have hGb := hG0 b ⟨lt_of_lt_of_le ha hab, hb⟩
  have hGc := hG0 c ⟨hc0, hcN⟩
  have hGcK := hGK c ⟨hc0, hcN⟩
  linarith


/-- The integral identity `∫ w G = G a - G c - q ∫ Y` on `[a, c]`, where `G y = (1 + y ^ (-q)) f y`
and `w y = V'₊ y - 2 β s y ^ (-s - 1)`. -/
lemma gap_wG_integral {N β s : ℝ} {V f : ℝ → ℝ} (hβ : 0 < β) (hs : 0 < s)
    (hV : ConvexOn ℝ (Ioo 0 N) V)
    (hf : ∀ y ∈ Ioo 0 N, f y = Real.exp (-2 * β * y ^ (-s) - V y)) {q a c : ℝ}
    (ha : 0 < a) (hac : a ≤ c) (hc : c < N) :
    ∫ x in a..c, (derivWithin V (Ioi x) x - 2 * β * s * x ^ (-s - 1)) * ((1 + x ^ (-q)) * f x)
      = (1 + a ^ (-q)) * f a - (1 + c ^ (-q)) * f c
        - q * ∫ x in a..c, x ^ (-q - 1) * f x := by
  have hsub := gap_uIcc_subset ha hac hc
  have hpow : ContinuousOn (fun y : ℝ => 1 + y ^ (-q)) (Ioo 0 N) := fun y hy =>
    (continuousAt_const.add (Real.continuousAt_rpow_const y (-q) (Or.inl hy.1.ne'))).continuousWithinAt
  have hGc : ContinuousOn (fun y => (1 + y ^ (-q)) * f y) (Ioo 0 N) :=
    hpow.mul (gap_f_continuousOn hV hf)
  have hpow2 : ContinuousOn (fun y : ℝ => y ^ (-q - 1)) (Ioo 0 N) := fun y hy =>
    (Real.continuousAt_rpow_const y (-q - 1) (Or.inl hy.1.ne')).continuousWithinAt
  have hYc : ContinuousOn (fun y => y ^ (-q - 1) * f y) (Ioo 0 N) :=
    hpow2.mul (gap_f_continuousOn hV hf)
  have hwm := gap_w_monotoneOn hβ hs hV
  have hX : IntervalIntegrable
      (fun x => (derivWithin V (Ioi x) x - 2 * β * s * x ^ (-s - 1)) * ((1 + x ^ (-q)) * f x))
      volume a c :=
    ((hwm.mono hsub).intervalIntegrable).mul_continuousOn (hGc.mono hsub)
  have hY : IntervalIntegrable (fun x => x ^ (-q - 1) * f x) volume a c :=
    (hYc.mono hsub).intervalIntegrable
  have hGcont : ContinuousOn (fun y => (1 + y ^ (-q)) * f y) (Icc a c) :=
    hGc.mono fun x hx => ⟨lt_of_lt_of_le ha hx.1, lt_of_le_of_lt hx.2 hc⟩
  have hderiv : ∀ x ∈ Ioo a c, HasDerivWithinAt (fun y => (1 + y ^ (-q)) * f y)
      (-((derivWithin V (Ioi x) x - 2 * β * s * x ^ (-s - 1)) * ((1 + x ^ (-q)) * f x))
        - q * (x ^ (-q - 1) * f x)) (Ioi x) x := by
    intro x hx
    have hxI : x ∈ Ioo 0 N := ⟨lt_trans ha hx.1, lt_trans hx.2 hc⟩
    have hc1 : HasDerivAt (fun y => 1 + y ^ (-q)) (-q * x ^ (-q - 1)) x :=
      (Real.hasDerivAt_rpow_const (Or.inl hxI.1.ne')).const_add 1
    have := hc1.hasDerivWithinAt.mul (gap_f_hasDerivWithinAt hV hf hxI)
    exact this.congr_deriv (by ring)
  have hΦ : IntervalIntegrable (fun x =>
      -((derivWithin V (Ioi x) x - 2 * β * s * x ^ (-s - 1)) * ((1 + x ^ (-q)) * f x))
        - q * (x ^ (-q - 1) * f x)) volume a c :=
    hX.neg.sub (hY.const_mul q)
  have hint := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hac hGcont hderiv hΦ
  have hXn : IntervalIntegrable (fun x => -((derivWithin V (Ioi x) x - 2 * β * s * x ^ (-s - 1))
      * ((1 + x ^ (-q)) * f x))) volume a c := hX.neg
  have hYq : IntervalIntegrable (fun x => q * (x ^ (-q - 1) * f x)) volume a c := hY.const_mul q
  rw [intervalIntegral.integral_sub hXn hYq, intervalIntegral.integral_neg,
    intervalIntegral.integral_const_mul] at hint
  linarith

/-- Restricted-to-subinterval version of the convergence of set integrals along `Ioc (a n) (b n)`. -/
lemma gap_tendsto_Ioc_integral {N : ℝ} {φ : ℝ → ℝ} (hφ : IntegrableOn φ (Ioc 0 N)) {a b : ℕ → ℝ}
    (hsub : ∀ n, Ioc (a n) (b n) ⊆ Ioc 0 N) (ha : Tendsto a atTop (𝓝 0))
    (hb : Tendsto b atTop (𝓝 N)) :
    Tendsto (fun n => ∫ x in Ioc (a n) (b n), φ x) atTop (𝓝 (∫ x in Ioc 0 N, φ x)) := by
  have hcov := aecover_Ioc_of_Ioc (μ := volume) ha hb
  have key := hcov.integral_tendsto_of_countably_generated hφ
  refine Tendsto.congr (fun n => ?_) key
  rw [Measure.restrict_restrict measurableSet_Ioc, inter_eq_left.2 (hsub n)]

/-- Explicit `N / (n + 3)` sequence bounds for the exhaustion of `(0, N)`. -/
lemma gap_seq_bounds {N : ℝ} (hN : 0 < N) (n : ℕ) :
    0 < N / ((n : ℝ) + 3) ∧ N / ((n : ℝ) + 3) ≤ N - N / ((n : ℝ) + 3) ∧
      N - N / ((n : ℝ) + 3) < N := by
  have h3 : (3 : ℝ) ≤ (n : ℝ) + 3 := by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  have hpos : 0 < N / ((n : ℝ) + 3) := div_pos hN (by positivity)
  have hle : N / ((n : ℝ) + 3) ≤ N / 3 := div_le_div_of_nonneg_left hN.le (by norm_num) h3
  refine ⟨hpos, by linarith, by linarith⟩


/-- **Single-gap integration by parts (abstract form).** Let `0 < N`, `0 < β`, `0 < s`, and let `V`
be convex on `(0, N)` with `f y = exp (-2 β y ^ (-s) - V y)` on `(0, N)`. Let `f y ≤ C exp (-2 β
(y ^ (-s) + (N - y) ^ (-s)))` on `(0, N)`. Let `q > 0`, and let `h`, `h'` satisfy `HasDerivAt h (h' y) y`
on `(0, N)`, `|h y| ≤ A (1 + y ^ (-q))`, and `|h' y| ≤ A (1 + y ^ (-q - 1))` on `(0, N)`. Then the
functions `h' f` and `h (V'₊ - 2 β s y ^ (-s - 1)) f` are integrable on `(0, N)`, and their integrals
agree. -/
theorem gap_ibp {N β s q A C : ℝ} {V f h h' : ℝ → ℝ} (hN : 0 < N) (hβ : 0 < β) (hs : 0 < s)
    (hV : ConvexOn ℝ (Ioo 0 N) V)
    (hf : ∀ y ∈ Ioo 0 N, f y = Real.exp (-2 * β * y ^ (-s) - V y))
    (hC : ∀ y ∈ Ioo 0 N, f y ≤ C * Real.exp (-2 * β * (y ^ (-s) + (N - y) ^ (-s))))
    (hq : 0 < q)
    (hder : ∀ y ∈ Ioo 0 N, HasDerivAt h (h' y) y)
    (hh : ∀ y ∈ Ioo 0 N, |h y| ≤ A * (1 + y ^ (-q)))
    (hh' : ∀ y ∈ Ioo 0 N, |h' y| ≤ A * (1 + y ^ (-q - 1))) :
    IntegrableOn (fun y => h' y * f y) (Ioo 0 N) ∧
      IntegrableOn (fun y => h y * (derivWithin V (Ioi y) y - 2 * β * s * y ^ (-s - 1)) * f y)
        (Ioo 0 N) ∧
      ∫ y in Ioo 0 N, h' y * f y =
        ∫ y in Ioo 0 N, h y * (derivWithin V (Ioi y) y - 2 * β * s * y ^ (-s - 1)) * f y := by
  obtain ⟨w, hw⟩ : ∃ w : ℝ → ℝ, ∀ y, w y = derivWithin V (Ioi y) y - 2 * β * s * y ^ (-s - 1) :=
    ⟨_, fun y => rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : ℝ → ℝ, ∀ y, G y = (1 + y ^ (-q)) * f y := ⟨_, fun y => rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y : ℝ → ℝ, ∀ y, Y y = y ^ (-q - 1) * f y := ⟨_, fun y => rfl⟩
  simp only [← hw]
  -- basic facts about `f`, `w`, `G`, `Y`
  have hC0 : 0 ≤ C := gap_C_nonneg hN hf hC
  have hfpos : ∀ y ∈ Ioo 0 N, 0 < f y := gap_f_pos hf
  have hCexp := gap_f_le_exp hβ hC hC0
  have hfle := gap_f_le_C hβ hC0 hC
  have hfc := gap_f_continuousOn hV hf
  have hf0 := gap_f_tendsto_zero_left hN hs hβ hfpos hCexp
  have hfN := gap_f_tendsto_zero_right hN hs hβ hfpos hC0 hC
  obtain ⟨M, hM0, hM⟩ := gap_rpow_mul_f_le hs hβ hq.le hC0 hCexp
  have hA0 : 0 ≤ A := by
    have hmid : N / 2 ∈ Ioo 0 N := ⟨by positivity, by linarith⟩
    have h1 := (abs_nonneg (h (N / 2))).trans (hh (N / 2) hmid)
    have h2 : 0 < 1 + (N / 2) ^ (-q) := by linarith [Real.rpow_nonneg hmid.1.le (-q)]
    by_contra hneg
    have : A * (1 + (N / 2) ^ (-q)) < 0 := mul_neg_of_neg_of_pos (lt_of_not_ge hneg) h2
    linarith
  have hwm : MonotoneOn w (Ioo 0 N) := by
    have e : w = fun y => derivWithin V (Ioi y) y - 2 * β * s * y ^ (-s - 1) := funext hw
    rw [e]
    exact gap_w_monotoneOn hβ hs hV
  have hGc : ContinuousOn G (Ioo 0 N) := by
    have e : G = fun y => (1 + y ^ (-q)) * f y := funext hG
    rw [e]
    have hpow : ContinuousOn (fun y : ℝ => 1 + y ^ (-q)) (Ioo 0 N) := fun y hy =>
      (continuousAt_const.add (Real.continuousAt_rpow_const y (-q) (Or.inl hy.1.ne'))).continuousWithinAt
    exact hpow.mul hfc
  have hG0 : ∀ y ∈ Ioo 0 N, 0 ≤ G y := fun y hy => by
    rw [hG y]
    exact mul_nonneg (by linarith [Real.rpow_nonneg hy.1.le (-q)]) (hfpos y hy).le
  have hGK : ∀ y ∈ Ioo 0 N, G y ≤ C + M * N := by
    intro y hy
    have h1 := hM y hy
    have h2 : M * y ≤ M * N := mul_le_mul_of_nonneg_left hy.2.le hM0
    have h3 := hfle y hy
    rw [hG y]
    calc (1 + y ^ (-q)) * f y = f y + y ^ (-q) * f y := by ring
      _ ≤ C + M * N := by linarith
  have hY0 : ∀ y ∈ Ioo 0 N, 0 ≤ Y y := fun y hy => by
    rw [hY y]
    exact mul_nonneg (Real.rpow_nonneg hy.1.le _) (hfpos y hy).le
  have hYint : IntegrableOn Y (Ioo 0 N) := by
    have e : Y = fun y => y ^ (-(q + 1)) * f y :=
      funext fun y => by rw [hY y, show -(q + 1) = -q - 1 by ring]
    rw [e]
    exact gap_integrableOn_rpow_mul_f hβ hs hV hf (by linarith) hC0 hCexp
  have hYint' : IntegrableOn (fun y => y ^ (-q - 1) * f y) (Ioo 0 N) := by
    have e : (fun y => y ^ (-q - 1) * f y) = Y := funext fun y => (hY y).symm
    rw [e]
    exact hYint
  have hf0int : IntegrableOn f (Ioo 0 N) := by
    simpa using gap_integrableOn_rpow_mul_f hβ hs hV hf (r := 0) le_rfl hC0 hCexp
  have hFTC : ∀ a c : ℝ, 0 < a → a ≤ c → c < N →
      ∫ x in a..c, w x * G x = G a - G c - q * ∫ x in a..c, Y x := by
    intro a c ha hac hc
    simp only [hw, hG, hY]
    exact gap_wG_integral hβ hs hV hf ha hac hc
  have hbound : ∀ a b : ℝ, 0 < a → a ≤ b → b < N →
      ∫ x in a..b, |w x * G x| ≤ 2 * (C + M * N) + q * ∫ x in Ioo 0 N, Y x :=
    fun a b ha hab hb => gap_sign_split hq hwm hGc hG0 hGK hY0 hYint hFTC ha hab hb
  -- integrability of `h w f` on the subintervals of `(0, N)`
  have hpt : ∀ u v : ℝ, 0 < u → u ≤ v → v < N →
      IntervalIntegrable (fun x => h x * w x * f x) volume u v := by
    intro u v hu huv hv
    have hsub := gap_uIcc_subset hu huv hv
    have hhc : ContinuousOn h (uIcc u v) := fun x hx =>
      (hder x (hsub hx)).continuousAt.continuousWithinAt
    exact ((hwm.mono hsub).intervalIntegrable.continuousOn_mul hhc).mul_continuousOn
      (hfc.mono hsub)
  have hbd : ∀ a b : ℝ, 0 < a → a ≤ b → b < N →
      ∫ x in a..b, ‖h x * w x * f x‖ ≤ A * (2 * (C + M * N) + q * ∫ x in Ioo 0 N, Y x) := by
    intro a b ha hab hb
    have hsub := gap_uIcc_subset ha hab hb
    have hwG : IntervalIntegrable (fun x => w x * G x) volume a b :=
      ((hwm.mono hsub).intervalIntegrable).mul_continuousOn (hGc.mono hsub)
    have hle : ∫ x in a..b, ‖h x * w x * f x‖ ≤ ∫ x in a..b, A * |w x * G x| := by
      refine intervalIntegral.integral_mono_on hab (hpt a b ha hab hb).norm
        (hwG.abs.const_mul A) fun x hx => ?_
      have hxI : x ∈ Ioo 0 N := hsub (by rw [uIcc_of_le hab]; exact hx)
      have hw0 : 0 ≤ |w x| := abs_nonneg _
      have hf0 : 0 ≤ f x := (hfpos x hxI).le
      have key : |h x| * |w x| * f x ≤ A * (1 + x ^ (-q)) * |w x| * f x :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hh x hxI) hw0) hf0
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_nonneg (hG0 x hxI),
        abs_of_pos (hfpos x hxI), hG x]
      calc |h x| * |w x| * f x ≤ A * (1 + x ^ (-q)) * |w x| * f x := key
        _ = A * (|w x| * ((1 + x ^ (-q)) * f x)) := by ring
    calc ∫ x in a..b, ‖h x * w x * f x‖ ≤ ∫ x in a..b, A * |w x * G x| := hle
      _ = A * ∫ x in a..b, |w x * G x| := intervalIntegral.integral_const_mul A _
      _ ≤ A * (2 * (C + M * N) + q * ∫ x in Ioo 0 N, Y x) :=
        mul_le_mul_of_nonneg_left (hbound a b ha hab hb) hA0
  -- the exhaustion `a n ↓ 0`, `b n ↑ N`
  obtain ⟨a, ha⟩ : ∃ a : ℕ → ℝ, ∀ n, a n = N / ((n : ℝ) + 3) := ⟨_, fun n => rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℕ → ℝ, ∀ n, b n = N - a n := ⟨_, fun n => rfl⟩
  have hseq : ∀ n, 0 < a n ∧ a n ≤ b n ∧ b n < N := by
    intro n
    have := gap_seq_bounds hN n
    rw [hb n, ha n]
    exact this
  have ha_tend : Tendsto a atTop (𝓝 0) := by
    have e : a = fun n : ℕ => N / ((n : ℝ) + 3) := funext ha
    rw [e]
    exact tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ 3 tendsto_natCast_atTop_atTop)
  have hb_tend : Tendsto b atTop (𝓝 N) := by
    have e : b = fun n => N - a n := funext hb
    rw [e]
    simpa using (tendsto_const_nhds (x := N)).sub ha_tend
  -- integrability of `h w f` on `(0, N)`
  have hwfIoc : IntegrableOn (fun y => h y * w y * f y) (Ioc 0 N) := by
    refine integrableOn_Ioc_of_intervalIntegral_norm_bounded (a := a) (b := b) (l := atTop)
      (I := A * (2 * (C + M * N) + q * ∫ x in Ioo 0 N, Y x)) (fun n => ?_) ha_tend hb_tend ?_
    · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (hseq n).2.1).1
        (hpt _ _ (hseq n).1 (hseq n).2.1 (hseq n).2.2)
    · refine Eventually.of_forall fun n => ?_
      rw [← intervalIntegral.integral_of_le (hseq n).2.1]
      exact hbd _ _ (hseq n).1 (hseq n).2.1 (hseq n).2.2
  have hwfIoo : IntegrableOn (fun y => h y * w y * f y) (Ioo 0 N) :=
    hwfIoc.congr_set_ae Ioo_ae_eq_Ioc
  -- integrability of `h' f` on `(0, N)`
  have hh'int : IntegrableOn (fun y => h' y * f y) (Ioo 0 N) := by
    have hg : IntegrableOn (fun y => A * (f y + y ^ (-q - 1) * f y)) (Ioo 0 N) :=
      (hf0int.add hYint').const_mul A
    have hmeas : AEStronglyMeasurable (fun y => h' y * f y) (volume.restrict (Ioo 0 N)) := by
      have h1 : AEStronglyMeasurable (fun y => deriv h y * f y) (volume.restrict (Ioo 0 N)) :=
        (measurable_deriv h).aestronglyMeasurable.mul
          (hfc.aestronglyMeasurable measurableSet_Ioo)
      refine h1.congr ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
      rw [(hder y hy).deriv]
    refine Integrable.mono' hg hmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
    have hfy := (hfpos y hy).le
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hfy]
    calc |h' y| * f y ≤ A * (1 + y ^ (-q - 1)) * f y := mul_le_mul_of_nonneg_right (hh' y hy) hfy
      _ = A * (f y + y ^ (-q - 1) * f y) := by ring
  -- the integration by parts identity on each `[a, b] ⊂ (0, N)`
  have hidentity : ∀ a b : ℝ, 0 < a → a ≤ b → b < N →
      (∫ x in a..b, h' x * f x) - ∫ x in a..b, h x * w x * f x = h b * f b - h a * f a := by
    intro a b ha hab hb
    have hsub : Ioc a b ⊆ Ioo 0 N := fun x hx => ⟨lt_trans ha hx.1, lt_of_le_of_lt hx.2 hb⟩
    have hsubI : Icc a b ⊆ Ioo 0 N := fun x hx =>
      ⟨lt_of_lt_of_le ha hx.1, lt_of_le_of_lt hx.2 hb⟩
    have hI1 : IntervalIntegrable (fun x => h' x * f x) volume a b := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
      exact hh'int.mono_set hsub
    have hI2 : IntervalIntegrable (fun x => h x * w x * f x) volume a b :=
      hpt a b ha hab hb
    have hcont : ContinuousOn (fun x => h x * f x) (Icc a b) := by
      have hhc : ContinuousOn h (Icc a b) := fun x hx =>
        (hder x (hsubI hx)).continuousAt.continuousWithinAt
      exact hhc.mul (hfc.mono hsubI)
    have hderivF : ∀ x ∈ Ioo a b,
        HasDerivWithinAt (fun x => h x * f x) (h' x * f x - h x * w x * f x) (Ioi x) x := by
      intro x hx
      have hxI : x ∈ Ioo 0 N := ⟨lt_trans ha hx.1, lt_trans hx.2 hb⟩
      have := (hder x hxI).hasDerivWithinAt.mul (gap_f_hasDerivWithinAt hV hf hxI)
      refine this.congr_deriv ?_
      rw [hw x]
      ring
    have hFTC' := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab hcont hderivF
      (hI1.sub hI2)
    rw [intervalIntegral.integral_sub hI1 hI2] at hFTC'
    exact hFTC'
  -- the limit `n → ∞` of the identity
  have hsub_n : ∀ n, Ioc (a n) (b n) ⊆ Ioc 0 N := fun n x hx =>
    ⟨lt_trans (hseq n).1 hx.1, (hx.2.trans_lt (hseq n).2.2).le⟩
  have hL1 := gap_tendsto_Ioc_integral
    (hh'int.congr_set_ae Ioo_ae_eq_Ioc.symm) hsub_n ha_tend hb_tend
  have hL2 := gap_tendsto_Ioc_integral
    (hwfIoo.congr_set_ae Ioo_ae_eq_Ioc.symm) hsub_n ha_tend hb_tend
  have hFlim0 : Tendsto (fun t => h t * f t) (𝓝[>] 0) (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun t => A * (f t + M * t)) ?_ ?_
    · filter_upwards [Ioo_mem_nhdsGT hN] with t ht
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hfpos t ht).le]
      calc |h t| * f t ≤ A * (1 + t ^ (-q)) * f t :=
            mul_le_mul_of_nonneg_right (hh t ht) (hfpos t ht).le
        _ = A * (f t + t ^ (-q) * f t) := by ring
        _ ≤ A * (f t + M * t) := mul_le_mul_of_nonneg_left (by linarith [hM t ht]) hA0
    · have hMt : Tendsto (fun t : ℝ => M * t) (𝓝[>] 0) (𝓝 0) := by
        have hc : Continuous (fun t : ℝ => M * t) := continuous_const.mul continuous_id
        have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
        simpa using this
      have := (hf0.add hMt).const_mul A
      simpa using this
  have hFlimN : Tendsto (fun t => h t * f t) (𝓝[<] N) (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun t => A * (1 + t ^ (-q)) * f t) ?_ ?_
    · filter_upwards [Ioo_mem_nhdsLT (show N / 2 < N by linarith)] with t ht
      have ht' : t ∈ Ioo 0 N := ⟨by linarith [ht.1], ht.2⟩
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hfpos t ht').le]
      exact mul_le_mul_of_nonneg_right (hh t ht') (hfpos t ht').le
    · have hp : Tendsto (fun t : ℝ => t ^ (-q)) (𝓝[<] N) (𝓝 (N ^ (-q))) :=
        ((Real.continuousAt_rpow_const N (-q) (Or.inl hN.ne')).tendsto).mono_left
          nhdsWithin_le_nhds
      have := (((tendsto_const_nhds (x := (1 : ℝ))).add hp).const_mul A).mul hfN
      simpa using this
  have hFa : Tendsto (fun n => h (a n) * f (a n)) atTop (𝓝 0) :=
    hFlim0.comp (tendsto_nhdsWithin_iff.2 ⟨ha_tend, Eventually.of_forall fun n => (hseq n).1⟩)
  have hFb : Tendsto (fun n => h (b n) * f (b n)) atTop (𝓝 0) :=
    hFlimN.comp (tendsto_nhdsWithin_iff.2 ⟨hb_tend, Eventually.of_forall fun n => (hseq n).2.2⟩)
  have hrhs : Tendsto (fun n => (∫ x in Ioc (a n) (b n), h' x * f x) -
      ∫ x in Ioc (a n) (b n), h x * w x * f x) atTop (𝓝 0) := by
    have := hFb.sub hFa
    rw [sub_self] at this
    refine Tendsto.congr (fun n => ?_) this
    have hid := hidentity (a n) (b n) (hseq n).1 (hseq n).2.1 (hseq n).2.2
    rw [intervalIntegral.integral_of_le (hseq n).2.1,
      intervalIntegral.integral_of_le (hseq n).2.1] at hid
    exact hid.symm
  have hdiff := hL1.sub hL2
  have hIdiff : (∫ x in Ioc 0 N, h' x * f x) = ∫ x in Ioc 0 N, h x * w x * f x :=
    sub_eq_zero.1 (tendsto_nhds_unique hdiff hrhs)
  refine ⟨hh'int, hwfIoo, ?_⟩
  rw [setIntegral_congr_set Ioo_ae_eq_Ioc, setIntegral_congr_set Ioo_ae_eq_Ioc]
  exact hIdiff


/-- **Single-gap integration by parts, `h = 1`.** The corollary of `gap_ibp` for `h y = 1`, with
`h' = 0`. -/
theorem gap_ibp_one {N β s q C : ℝ} {V f : ℝ → ℝ} (hN : 0 < N) (hβ : 0 < β) (hs : 0 < s)
    (hV : ConvexOn ℝ (Ioo 0 N) V)
    (hf : ∀ y ∈ Ioo 0 N, f y = Real.exp (-2 * β * y ^ (-s) - V y))
    (hC : ∀ y ∈ Ioo 0 N, f y ≤ C * Real.exp (-2 * β * (y ^ (-s) + (N - y) ^ (-s))))
    (hq : 0 < q) :
    IntegrableOn (fun y => (0 : ℝ) * f y) (Ioo 0 N) ∧
      IntegrableOn (fun y => (1 : ℝ) * (derivWithin V (Ioi y) y - 2 * β * s * y ^ (-s - 1)) * f y)
        (Ioo 0 N) ∧
      ∫ y in Ioo 0 N, (0 : ℝ) * f y =
        ∫ y in Ioo 0 N, (1 : ℝ) * (derivWithin V (Ioi y) y - 2 * β * s * y ^ (-s - 1)) * f y :=
  gap_ibp hN hβ hs hV hf hC hq (h := fun _ => 1) (h' := fun _ => 0) (A := 1)
    (fun y _ => hasDerivAt_const y 1)
    (fun y hy => by
      show |(1 : ℝ)| ≤ 1 * (1 + y ^ (-q))
      rw [abs_one, one_mul]
      linarith [Real.rpow_nonneg hy.1.le (-q)])
    (fun y hy => by
      show |(0 : ℝ)| ≤ 1 * (1 + y ^ (-q - 1))
      rw [abs_zero, one_mul]
      linarith [Real.rpow_nonneg hy.1.le (-q - 1)])

/-- **Single-gap integration by parts, `h y = y`.** The corollary of `gap_ibp` with `h' = 1`. -/
theorem gap_ibp_id {N β s q C : ℝ} {V f : ℝ → ℝ} (hN : 0 < N) (hβ : 0 < β) (hs : 0 < s)
    (hV : ConvexOn ℝ (Ioo 0 N) V)
    (hf : ∀ y ∈ Ioo 0 N, f y = Real.exp (-2 * β * y ^ (-s) - V y))
    (hC : ∀ y ∈ Ioo 0 N, f y ≤ C * Real.exp (-2 * β * (y ^ (-s) + (N - y) ^ (-s))))
    (hq : 0 < q) :
    IntegrableOn (fun y => (1 : ℝ) * f y) (Ioo 0 N) ∧
      IntegrableOn (fun y => y * (derivWithin V (Ioi y) y - 2 * β * s * y ^ (-s - 1)) * f y)
        (Ioo 0 N) ∧
      ∫ y in Ioo 0 N, (1 : ℝ) * f y =
        ∫ y in Ioo 0 N, y * (derivWithin V (Ioi y) y - 2 * β * s * y ^ (-s - 1)) * f y :=
  gap_ibp hN hβ hs hV hf hC hq (h := fun y => y) (h' := fun _ => 1) (A := N + 1)
    (fun y _ => hasDerivAt_id' y)
    (fun y hy => by
      show |y| ≤ (N + 1) * (1 + y ^ (-q))
      rw [abs_of_pos hy.1]
      have := mul_nonneg (show (0 : ℝ) ≤ N + 1 by linarith) (Real.rpow_nonneg hy.1.le (-q))
      nlinarith [hy.2])
    (fun y hy => by
      show |(1 : ℝ)| ≤ (N + 1) * (1 + y ^ (-q - 1))
      rw [abs_one]
      have := mul_nonneg (show (0 : ℝ) ≤ N + 1 by linarith) (Real.rpow_nonneg hy.1.le (-q - 1))
      nlinarith)

/-- **Single-gap integration by parts, `h y = y ^ (-q)`.** The corollary of `gap_ibp` with
`h' y = -q y ^ (-q - 1)` and `A = q + 1`. -/
theorem gap_ibp_pow {N β s q C : ℝ} {V f : ℝ → ℝ} (hN : 0 < N) (hβ : 0 < β) (hs : 0 < s)
    (hV : ConvexOn ℝ (Ioo 0 N) V)
    (hf : ∀ y ∈ Ioo 0 N, f y = Real.exp (-2 * β * y ^ (-s) - V y))
    (hC : ∀ y ∈ Ioo 0 N, f y ≤ C * Real.exp (-2 * β * (y ^ (-s) + (N - y) ^ (-s))))
    (hq : 0 < q) :
    IntegrableOn (fun y => (-q * y ^ (-q - 1)) * f y) (Ioo 0 N) ∧
      IntegrableOn (fun y => y ^ (-q) * (derivWithin V (Ioi y) y - 2 * β * s * y ^ (-s - 1)) * f y)
        (Ioo 0 N) ∧
      ∫ y in Ioo 0 N, (-q * y ^ (-q - 1)) * f y =
        ∫ y in Ioo 0 N, y ^ (-q) * (derivWithin V (Ioi y) y - 2 * β * s * y ^ (-s - 1)) * f y :=
  gap_ibp hN hβ hs hV hf hC hq (h := fun y => y ^ (-q)) (h' := fun y => -q * y ^ (-q - 1))
    (A := q + 1)
    (fun y hy => Real.hasDerivAt_rpow_const (Or.inl hy.1.ne'))
    (fun y hy => by
      show |y ^ (-q)| ≤ (q + 1) * (1 + y ^ (-q))
      rw [abs_of_nonneg (Real.rpow_nonneg hy.1.le _)]
      nlinarith [mul_nonneg hq.le (Real.rpow_nonneg hy.1.le (-q))])
    (fun y hy => by
      show |-q * y ^ (-q - 1)| ≤ (q + 1) * (1 + y ^ (-q - 1))
      have ht := Real.rpow_nonneg hy.1.le (-q - 1)
      rw [abs_mul, abs_neg, abs_of_pos hq, abs_of_nonneg ht]
      nlinarith)

/-- **Endpoint limits and inverse moments of a single gap.** The density `f` tends to zero at both
endpoints of `(0, N)`, and `∫ y ^ (-q) f y` is finite for each `q > 0`. -/
theorem gap_density_endpoints {N β s C : ℝ} {V f : ℝ → ℝ} (hN : 0 < N) (hβ : 0 < β)
    (hs : 0 < s) (hV : ConvexOn ℝ (Ioo 0 N) V)
    (hf : ∀ y ∈ Ioo 0 N, f y = Real.exp (-2 * β * y ^ (-s) - V y))
    (hC : ∀ y ∈ Ioo 0 N, f y ≤ C * Real.exp (-2 * β * (y ^ (-s) + (N - y) ^ (-s)))) :
    Tendsto f (𝓝[>] 0) (𝓝 0) ∧ Tendsto f (𝓝[<] N) (𝓝 0) ∧
      ∀ q : ℝ, 0 < q → IntegrableOn (fun y => y ^ (-q) * f y) (Ioo 0 N) := by
  have hC0 := gap_C_nonneg hN hf hC
  have hfpos := gap_f_pos hf
  have hCexp := gap_f_le_exp hβ hC hC0
  exact ⟨gap_f_tendsto_zero_left hN hs hβ hfpos hCexp,
    gap_f_tendsto_zero_right hN hs hβ hfpos hC0 hC,
    fun q hq => gap_integrableOn_rpow_mul_f hβ hs hV hf hq.le hC0 hCexp⟩

end Riesz1
