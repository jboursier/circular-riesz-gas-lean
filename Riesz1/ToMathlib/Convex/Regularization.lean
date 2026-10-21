/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.Convex.RegularizationEnvelope
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.Convolution
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Convex regularization by smooth convex functions

This is Lemma 3.7 of the paper.

Let `B : E → EReal` be proper, lower semicontinuous and convex on a finite-dimensional real inner
product space `E`, with `B x ≥ ⟪a, x⟫ + b` for all `x`. Then there are finite smooth convex
functions `B_k : E → ℝ` with `B_k x ≥ ⟪a, x⟫ + b - ‖a‖² / 2`, such that `B_k` converges uniformly to
`B` on compact subsets of the interior of the domain, and `B_k x → +∞` for each `x` outside the
closure of the domain.

The construction has two steps. First, the infimal convolution `moreauEnvelope` of
`Riesz1/ToMathlib/Convex/RegularizationEnvelope.lean` gives convex approximations with parameter
`θ = k + 1`, which are finite, continuous and increase to `B`. Second, mollification
`mollify F φ x = ∫ F (x - z) φ z dz` against an even smooth probability density `φ` supported in a
small ball makes them smooth. The index `k` of `Bk` runs over all natural numbers, which is
stronger than the integers `k ≥ 1` of the paper: the function `Bk k` is built from the envelope with
parameter `θ = k + 1`, and the three conclusions hold for every `k`.
-/

public section

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace ContDiff

namespace Riesz1

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [FiniteDimensional ℝ E]

/-- Existence of an even smooth probability density, with compact support in the closed ball of
radius `ρ`. It is a normalized bump function. -/
lemma exists_even_mollifier {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ φ : E → ℝ, ContDiff ℝ ∞ φ ∧ (∀ z, 0 ≤ φ z) ∧ HasCompactSupport φ ∧
      tsupport φ ⊆ Metric.closedBall 0 ρ ∧ (∀ z, φ (-z) = φ z) ∧ ∫ z, φ z = 1 := by
  let c : ContDiffBump (0 : E) :=
    { rIn := ρ / 2, rOut := ρ, rIn_pos := by positivity, rIn_lt_rOut := by linarith }
  exact ⟨c.normed volume, c.contDiff_normed, c.nonneg_normed, c.hasCompactSupport_normed,
    c.tsupport_normed_eq.subset, c.normed_neg, c.integral_normed⟩

/-- The mollification `x ↦ ∫ F (x - z) φ z dz` of `F` by `φ`, the convolution with `φ`. -/
noncomputable def mollify (F φ : E → ℝ) : E → ℝ :=
  convolution F φ (ContinuousLinearMap.lsmul ℝ ℝ) volume

lemma mollify_apply (F φ : E → ℝ) (x : E) : mollify F φ x = ∫ z, F (x - z) * φ z := by
  unfold mollify
  simp only [convolution, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  rw [← integral_sub_left_eq_self (fun t => F t * φ (x - t)) volume x]
  simp only [sub_sub_cancel]

lemma integrable_mul_mollifier {φ : E → ℝ} (hφc : Continuous φ) (hφs : HasCompactSupport φ)
    {h : E → ℝ} (hh : Continuous h) : Integrable (fun z => h z * φ z) volume :=
  (hh.mul hφc).integrable_of_hasCompactSupport hφs.mul_left

lemma contDiff_mollify {F φ : E → ℝ} (hF : Continuous F) (hφs : HasCompactSupport φ)
    (hφ : ContDiff ℝ ∞ φ) : ContDiff ℝ ∞ (mollify F φ) :=
  hφs.contDiff_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) hF.locallyIntegrable hφ

/-- Convexity is preserved by mollification with a nonnegative density. -/
lemma convexOn_mollify {F φ : E → ℝ} (hF : Continuous F) (hFc : ConvexOn ℝ univ F)
    (hφc : Continuous φ) (hφs : HasCompactSupport φ) (hφ0 : ∀ z, 0 ≤ φ z) :
    ConvexOn ℝ univ (mollify F φ) := by
  refine ⟨convex_univ, fun x _ y _ s t hs ht hst => ?_⟩
  obtain rfl : t = 1 - s := by linarith
  simp only [mollify_apply, smul_eq_mul]
  have hFx : Continuous fun z => F (x - z) := hF.comp (by fun_prop)
  have hFy : Continuous fun z => F (y - z) := hF.comp (by fun_prop)
  have hFxy : Continuous fun z => F (s • x + (1 - s) • y - z) :=
    hF.comp (by fun_prop)
  have hpt : ∀ z, F (s • x + (1 - s) • y - z) * φ z ≤
      s * (F (x - z) * φ z) + (1 - s) * (F (y - z) * φ z) := by
    intro z
    have h1 := hFc.2 (mem_univ (x - z)) (mem_univ (y - z)) hs ht (by ring)
    have e : s • (x - z) + (1 - s) • (y - z) = s • x + (1 - s) • y - z := by
      module
    rw [e, smul_eq_mul, smul_eq_mul] at h1
    have h2 := mul_le_mul_of_nonneg_right h1 (hφ0 z)
    linarith
  have hi₁ := (integrable_mul_mollifier hφc hφs hFx).const_mul s
  have hi₂ := (integrable_mul_mollifier hφc hφs hFy).const_mul (1 - s)
  have hsplit : ∫ z, (s * (F (x - z) * φ z) + (1 - s) * (F (y - z) * φ z)) =
      s * (∫ z, F (x - z) * φ z) + (1 - s) * (∫ z, F (y - z) * φ z) := by
    rw [integral_add hi₁ hi₂, integral_const_mul, integral_const_mul]
  exact (integral_mono (integrable_mul_mollifier hφc hφs hFxy) (hi₁.add hi₂) hpt).trans
    hsplit.le

/-- Pointwise domination by a constant on the support of `φ` gives the same domination for the
mollification, since `∫ φ = 1`. -/
lemma mollify_le_of_le_on {F φ : E → ℝ} (hF : Continuous F) (hφc : Continuous φ)
    (hφs : HasCompactSupport φ) (hφ0 : ∀ z, 0 ≤ φ z) (hφ1 : ∫ z, φ z = 1) (x : E) {c : ℝ}
    (h : ∀ z, φ z ≠ 0 → F (x - z) ≤ c) : mollify F φ x ≤ c := by
  rw [mollify_apply]
  have hFx : Continuous fun z => F (x - z) := hF.comp (by fun_prop)
  have hpt : ∀ z, F (x - z) * φ z ≤ c * φ z := by
    intro z
    by_cases hz : φ z = 0
    · simp [hz]
    · exact mul_le_mul_of_nonneg_right (h z hz) (hφ0 z)
  calc ∫ z, F (x - z) * φ z ≤ ∫ z, c * φ z :=
        integral_mono (integrable_mul_mollifier hφc hφs hFx)
          (integrable_mul_mollifier hφc hφs continuous_const) hpt
    _ = c := by rw [integral_const_mul, hφ1, mul_one]

/-- A constant lower bound on the support of `φ` gives the same lower bound for the
mollification. -/
lemma le_mollify_of_le_on {F φ : E → ℝ} (hF : Continuous F) (hφc : Continuous φ)
    (hφs : HasCompactSupport φ) (hφ0 : ∀ z, 0 ≤ φ z) (hφ1 : ∫ z, φ z = 1) (x : E) {c : ℝ}
    (h : ∀ z, φ z ≠ 0 → c ≤ F (x - z)) : c ≤ mollify F φ x := by
  rw [mollify_apply]
  have hFx : Continuous fun z => F (x - z) := hF.comp (by fun_prop)
  have hpt : ∀ z, c * φ z ≤ F (x - z) * φ z := by
    intro z
    by_cases hz : φ z = 0
    · simp [hz]
    · exact mul_le_mul_of_nonneg_right (h z hz) (hφ0 z)
  calc c = ∫ z, c * φ z := by rw [integral_const_mul, hφ1, mul_one]
    _ ≤ ∫ z, F (x - z) * φ z :=
        integral_mono (integrable_mul_mollifier hφc hφs continuous_const)
          (integrable_mul_mollifier hφc hφs hFx) hpt

/-- Uniform closeness: if `F` is within `ε` of its value at `x` on the ball of radius `ρ`, and the
density is supported there, then the mollification is within `ε` of `F x`. -/
lemma abs_mollify_sub_le {F φ : E → ℝ} (hF : Continuous F) (hφc : Continuous φ)
    (hφs : HasCompactSupport φ) (hφ0 : ∀ z, 0 ≤ φ z) (hφ1 : ∫ z, φ z = 1) (x : E) {ρ ε : ℝ}
    (hsupp : ∀ z, φ z ≠ 0 → ‖z‖ ≤ ρ) (hnear : ∀ z, ‖z‖ ≤ ρ → |F (x - z) - F x| ≤ ε) :
    |mollify F φ x - F x| ≤ ε := by
  have hup : ∀ z, φ z ≠ 0 → F (x - z) ≤ F x + ε := fun z hz =>
    by linarith [le_abs_self (F (x - z) - F x), hnear z (hsupp z hz)]
  have hlo : ∀ z, φ z ≠ 0 → F x - ε ≤ F (x - z) := fun z hz =>
    by linarith [neg_abs_le (F (x - z) - F x), hnear z (hsupp z hz)]
  have h1 := mollify_le_of_le_on hF hφc hφs hφ0 hφ1 x hup
  have h2 := le_mollify_of_le_on hF hφc hφs hφ0 hφ1 x hlo
  rw [abs_le]
  constructor <;> linarith

/-- The affine lower bound passes to the mollification. The first moment `∫ ⟪a, z⟫ φ z` vanishes
because `φ` is even. -/
lemma affine_le_mollify {F φ : E → ℝ} {a : E} {b c : ℝ} (hF : Continuous F) (hφc : Continuous φ)
    (hφs : HasCompactSupport φ) (hφ0 : ∀ z, 0 ≤ φ z) (hφ1 : ∫ z, φ z = 1)
    (hφeven : ∀ z, φ (-z) = φ z) (hlow : ∀ y, ⟪a, y⟫_ℝ + b - c ≤ F y) (x : E) :
    ⟪a, x⟫_ℝ + b - c ≤ mollify F φ x := by
  -- The first moment vanishes: the integrand is odd under `z ↦ -z`.
  have hmoment : ∫ z, ⟪a, z⟫_ℝ * φ z = 0 := by
    have h := integral_neg_eq_self (fun z => ⟪a, z⟫_ℝ * φ z) volume
    simp only [inner_neg_right, hφeven, neg_mul] at h
    rw [integral_neg] at h
    linarith
  set K := ⟪a, x⟫_ℝ + b - c with hK
  have hi1 : Integrable (fun z => K * φ z) volume :=
    integrable_mul_mollifier hφc hφs continuous_const
  have hi2 : Integrable (fun z => ⟪a, z⟫_ℝ * φ z) volume :=
    integrable_mul_mollifier hφc hφs (continuous_const.inner continuous_id)
  have hFx : Continuous fun z => F (x - z) := hF.comp (by fun_prop)
  have hint : Integrable (fun z => F (x - z) * φ z) volume :=
    integrable_mul_mollifier hφc hφs hFx
  have hlhs : K = ∫ z, (K * φ z - ⟪a, z⟫_ℝ * φ z) := by
    rw [integral_sub hi1 hi2, integral_const_mul, hmoment, hφ1, mul_one, sub_zero]
  rw [mollify_apply]
  calc K = ∫ z, (K * φ z - ⟪a, z⟫_ℝ * φ z) := hlhs
    _ ≤ ∫ z, F (x - z) * φ z := by
        refine integral_mono (hi1.sub hi2) hint (fun z => ?_)
        have h1 := hlow (x - z)
        rw [inner_sub_right] at h1
        have h2 := mul_le_mul_of_nonneg_right h1 (hφ0 z)
        simp only [hK]
        linarith

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Convex regularization** (Lemma 3.7).

Let `B : E → EReal` be proper (`B x < ⊤` for some `x`), lower semicontinuous and convex, with the
affine minorant `B x ≥ ⟪a, x⟫ + b` for all `x`. Then there are finite smooth convex functions `Bk k`
with `Bk k x ≥ ⟪a, x⟫ + b - ‖a‖² / 2`, which converge uniformly to `B` on each compact subset of the
interior of the domain `{x | B x < ⊤}`, and satisfy `Bk k x → +∞` for each `x` outside the closure
of the domain. -/
theorem convex_regularization (B : E → EReal) (a : E) (b : ℝ)
    (h_proper : ∃ x, B x < ⊤)
    (h_lsc : LowerSemicontinuous B)
    (h_convex : ∀ x y : E, ∀ t : ℝ, 0 < t → t < 1 →
      B (t • x + (1 - t) • y) ≤ (t : EReal) * B x + ((1 - t : ℝ) : EReal) * B y)
    (h_affine : ∀ x : E, ((⟪a, x⟫_ℝ + b : ℝ) : EReal) ≤ B x) :
    ∃ Bk : ℕ → E → ℝ,
      (∀ k : ℕ, ContDiff ℝ ∞ (Bk k) ∧ ConvexOn ℝ univ (Bk k) ∧
        ∀ x : E, ⟪a, x⟫_ℝ + b - ‖a‖ ^ 2 / 2 ≤ Bk k x) ∧
      (∀ K : Set E, IsCompact K → K ⊆ interior {x | B x < ⊤} →
        TendstoUniformlyOn Bk (fun x => (B x).toReal) atTop K) ∧
      (∀ x : E, x ∉ closure {x | B x < ⊤} → Tendsto (fun k => Bk k x) atTop atTop) := by
  -- The Borel structure on `E` is used only to define the Lebesgue measure `volume` below.
  let _ : MeasurableSpace E := borel E
  have _ : BorelSpace E := ⟨rfl⟩
  -- The domain `S` and the real restriction `g` of `B`, finite on `S`.
  set S : Set E := {x | B x < ⊤}
  set g : E → ℝ := fun x => (B x).toReal
  have hBfin : ∀ x ∈ S, B x = (g x : EReal) := by
    intro x hx
    have hbot : B x ≠ ⊥ := by
      intro h
      have h' := h_affine x
      rw [h] at h'
      exact not_le.2 (EReal.bot_lt_coe _) h'
    exact (EReal.coe_toReal (show B x < ⊤ from hx).ne hbot).symm
  have hg_aff : ∀ y ∈ S, ⟪a, y⟫_ℝ + b ≤ g y := by
    intro y hy
    have h := h_affine y
    rw [hBfin y hy] at h
    exact EReal.coe_le_coe_iff.1 h
  -- Convex combinations of points of `S` stay in `S`, and `g` is convex on `S`.
  have hcomb : ∀ x ∈ S, ∀ y ∈ S, ∀ t : ℝ, 0 < t → t < 1 →
      t • x + (1 - t) • y ∈ S ∧ g (t • x + (1 - t) • y) ≤ t * g x + (1 - t) * g y := by
    intro x hx y hy t ht0 ht1
    have hlt : B (t • x + (1 - t) • y) ≤ ((t * g x + (1 - t) * g y : ℝ) : EReal) := by
      refine (h_convex x y t ht0 ht1).trans (le_of_eq ?_)
      rw [hBfin x hx, hBfin y hy, EReal.coe_add, EReal.coe_mul, EReal.coe_mul]
    have hmem : t • x + (1 - t) • y ∈ S := lt_of_le_of_lt hlt (EReal.coe_lt_top _)
    refine ⟨hmem, ?_⟩
    have h2 : ((g (t • x + (1 - t) • y) : ℝ) : EReal) ≤
        ((t * g x + (1 - t) * g y : ℝ) : EReal) := by
      rw [← hBfin _ hmem]
      exact hlt
    exact EReal.coe_le_coe_iff.1 h2
  have hSconv : Convex ℝ S := by
    intro x hx y hy s t hs ht hst
    obtain rfl : t = 1 - s := by linarith
    rcases hs.eq_or_lt with rfl | hs'
    · simpa using hy
    rcases ht.eq_or_lt with h0 | ht'
    · obtain rfl : s = 1 := by linarith
      simpa using hx
    exact (hcomb x hx y hy s hs' (by linarith)).1
  have hgc : ConvexOn ℝ S g := by
    refine ⟨hSconv, fun x hx y hy s t hs ht hst => ?_⟩
    obtain rfl : t = 1 - s := by linarith
    rcases hs.eq_or_lt with rfl | hs'
    · simp
    rcases ht.eq_or_lt with h0 | ht'
    · obtain rfl : s = 1 := by linarith
      simp
    exact (hcomb x hx y hy s hs' (by linarith)).2
  -- Lower semicontinuity of `g` on `S`, from that of `B`.
  have hlsc : ∀ x ∈ S, ∀ c < g x, ∃ r > 0, ∀ y ∈ S, dist y x < r → c < g y := by
    intro x hx c hc
    have hlt : ((c : ℝ) : EReal) < B x := by
      rw [hBfin x hx]
      exact EReal.coe_lt_coe_iff.2 hc
    obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.1 (h_lsc x _ hlt)
    refine ⟨r, hr, fun y hy hxy => ?_⟩
    have h : ((c : ℝ) : EReal) < B y := hball hxy
    rw [hBfin y hy] at h
    exact EReal.coe_lt_coe_iff.1 h
  obtain ⟨x₀, hx₀⟩ := h_proper
  have hSne : S.Nonempty := ⟨x₀, hx₀⟩
  -- The envelopes with parameter `k + 1`: continuous, convex, and uniformly continuous on balls.
  have hθ : ∀ k : ℕ, (0 : ℝ) < (k : ℝ) + 1 := fun k => by positivity
  have hEc : ∀ k : ℕ, Continuous (moreauEnvelope S g ((k : ℝ) + 1)) := fun k =>
    continuous_moreauEnvelope (hθ k) hSconv hgc hSne hg_aff
  have hmod : ∀ k : ℕ, ∃ δ > 0, ∀ u ∈ Metric.closedBall (0 : E) ((k : ℝ) + 1),
      ∀ v ∈ Metric.closedBall (0 : E) ((k : ℝ) + 1), dist u v < δ →
        dist (moreauEnvelope S g ((k : ℝ) + 1) u) (moreauEnvelope S g ((k : ℝ) + 1) v) <
          1 / ((k : ℝ) + 1) := by
    intro k
    exact Metric.uniformContinuousOn_iff.1
      ((isCompact_closedBall (0 : E) ((k : ℝ) + 1)).uniformContinuousOn_of_continuous
        (hEc k).continuousOn) (1 / ((k : ℝ) + 1)) (by positivity)
  choose δ hδ_pos hδ using hmod
  -- Mollifiers supported in balls of radius `min (δ k) (1 / (k + 1)) / 2`.
  have hρ_pos : ∀ k : ℕ, 0 < min (δ k) (1 / ((k : ℝ) + 1)) / 2 := fun k =>
    half_pos (lt_min (hδ_pos k) (by positivity))
  choose φ hφ using fun k : ℕ => exists_even_mollifier (E := E) (hρ_pos k)
  -- Closeness of the mollified envelope to the envelope, on balls of radius `k`.
  have closeness : ∀ k : ℕ, ∀ x : E, ‖x‖ ≤ (k : ℝ) →
      |mollify (moreauEnvelope S g ((k : ℝ) + 1)) (φ k) x -
        moreauEnvelope S g ((k : ℝ) + 1) x| ≤ 1 / ((k : ℝ) + 1) := by
    intro k x hx
    obtain ⟨hφsm, hφ0, hφcs, hφsupp, hφeven, hφ1⟩ := hφ k
    have hk1 : 1 / ((k : ℝ) + 1) ≤ 1 :=
      (div_le_one (by positivity)).2 (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
    have hρ1 : min (δ k) (1 / ((k : ℝ) + 1)) / 2 ≤ 1 := by
      linarith [min_le_right (δ k) (1 / ((k : ℝ) + 1))]
    apply abs_mollify_sub_le (hEc k) hφsm.continuous hφcs hφ0 hφ1 x
      (ρ := min (δ k) (1 / ((k : ℝ) + 1)) / 2) (ε := 1 / ((k : ℝ) + 1))
    · intro z hz
      exact mem_closedBall_zero_iff.1 (hφsupp (subset_tsupport _ (Function.mem_support.2 hz)))
    · intro z hzρ
      have hmem1 : x - z ∈ Metric.closedBall (0 : E) ((k : ℝ) + 1) := by
        rw [mem_closedBall_zero_iff]
        have := norm_sub_le x z
        linarith
      have hmem2 : x ∈ Metric.closedBall (0 : E) ((k : ℝ) + 1) := by
        rw [mem_closedBall_zero_iff]
        linarith
      have hd : dist (x - z) x < δ k := by
        rw [dist_eq_norm, sub_sub_cancel_left, norm_neg]
        linarith [min_le_left (δ k) (1 / ((k : ℝ) + 1)), hδ_pos k]
      have h := hδ k (x - z) hmem1 x hmem2 hd
      rw [Real.dist_eq] at h
      exact h.le
  -- The approximations.
  refine ⟨fun k => mollify (moreauEnvelope S g ((k : ℝ) + 1)) (φ k), ?_, ?_, ?_⟩
  · intro k
    obtain ⟨hφsm, hφ0, hφcs, _, hφeven, hφ1⟩ := hφ k
    have hφc : Continuous (φ k) := hφsm.continuous
    refine ⟨contDiff_mollify (hEc k) hφcs hφsm,
      convexOn_mollify (hEc k) (convexOn_moreauEnvelope (hθ k) hSconv hgc hSne hg_aff) hφc hφcs hφ0,
      fun x => ?_⟩
    have hc : ‖a‖ ^ 2 / (2 * ((k : ℝ) + 1)) ≤ ‖a‖ ^ 2 / 2 :=
      div_le_div_of_nonneg_left (sq_nonneg _) (by norm_num)
        (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
    have h := affine_le_mollify (hEc k) hφc hφcs hφ0 hφ1 hφeven
      (fun y => le_moreauEnvelope (hθ k) hSne hg_aff y) x
    show ⟪a, x⟫_ℝ + b - ‖a‖ ^ 2 / 2 ≤ mollify (moreauEnvelope S g ((k : ℝ) + 1)) (φ k) x
    linarith
  · intro K hK hKS
    obtain ⟨R, hKR⟩ := hK.isBounded.subset_closedBall (0 : E)
    have hDini := tendstoUniformlyOn_moreauEnvelope hSconv hgc hSne hg_aff hlsc hK hKS
    rw [Metric.tendstoUniformlyOn_iff] at hDini ⊢
    intro ε hε
    have hdini := hDini (ε / 2) (half_pos hε)
    have hcl : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) < ε / 2 :=
      tendsto_one_div_add_atTop_nhds_zero_nat.eventually (gt_mem_nhds (half_pos hε))
    have hR : ∀ᶠ n : ℕ in atTop, R ≤ (n : ℝ) :=
      tendsto_natCast_atTop_atTop.eventually_ge_atTop R
    filter_upwards [hdini, hcl, hR] with n hn hnl hnR x hx
    have hxR : ‖x‖ ≤ (n : ℝ) := le_trans (mem_closedBall_zero_iff.1 (hKR hx)) hnR
    have hmol := closeness n x hxR
    have h1 := hn x hx
    rw [Real.dist_eq] at h1 ⊢
    have htri := abs_sub_le ((B x).toReal) (moreauEnvelope S g ((n : ℝ) + 1) x)
      (mollify (moreauEnvelope S g ((n : ℝ) + 1)) (φ n) x)
    rw [abs_sub_comm (moreauEnvelope S g ((n : ℝ) + 1) x)] at htri
    show |(B x).toReal - mollify (moreauEnvelope S g ((n : ℝ) + 1)) (φ n) x| < ε
    linarith
  · intro x hx
    -- A ball around `x` misses `S`.
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 isClosed_closure.isOpen_compl x hx
    have hgap : ∀ w ∈ S, r ≤ dist w x := by
      intro w hw
      by_contra hlt
      exact hball (Metric.mem_ball.2 (not_le.1 hlt)) (subset_closure hw)
    -- For large `k`, the gap and the mollifier support are compatible with the bound.
    have hk : ∀ᶠ k : ℕ in atTop, 16 * ‖a‖ / r + 1 / r ≤ (k : ℝ) :=
      tendsto_natCast_atTop_atTop.eventually_ge_atTop _
    have hlow : ∀ᶠ k : ℕ in atTop,
        ⟪a, x⟫_ℝ + b + ((k : ℝ) + 1) * (r ^ 2 / 16) ≤ mollify (moreauEnvelope S g ((k : ℝ) + 1)) (φ k) x := by
      filter_upwards [hk] with k hk'
      have hkr : 16 * ‖a‖ ≤ ((k : ℝ) + 1) * r := by
        have : 16 * ‖a‖ / r ≤ (k : ℝ) := le_trans (le_add_of_nonneg_right (by positivity)) hk'
        rw [div_le_iff₀ hr] at this
        nlinarith
      have hρr : min (δ k) (1 / ((k : ℝ) + 1)) / 2 < r / 2 := by
        have h1r : 1 / ((k : ℝ) + 1) < r := by
          have : 1 / r ≤ (k : ℝ) := le_trans (le_add_of_nonneg_left (by positivity)) hk'
          rw [div_le_iff₀ hr] at this
          rw [div_lt_iff₀ (by positivity)]
          nlinarith
        linarith [min_le_right (δ k) (1 / ((k : ℝ) + 1))]
      obtain ⟨hφsm, hφ0, hφcs, hφsupp, hφeven, hφ1⟩ := hφ k
      have hφc : Continuous (φ k) := hφsm.continuous
      have := le_mollify_of_le_on (hEc k) hφc hφcs hφ0 hφ1 x
        (c := ⟪a, x⟫_ℝ + b + ((k : ℝ) + 1) * r ^ 2 / 16) (fun z hz => by
          have hzρ : ‖z‖ ≤ min (δ k) (1 / ((k : ℝ) + 1)) / 2 :=
            mem_closedBall_zero_iff.1 (hφsupp (subset_tsupport _ (Function.mem_support.2 hz)))
          have hy : dist (x - z) x < r / 2 := by
            rw [dist_eq_norm, sub_sub_cancel_left, norm_neg]
            linarith
          exact le_moreauEnvelope_of_gap hr hkr hSne hg_aff hgap hy)
      linarith [this]
    have hlim : Tendsto (fun k : ℕ => ⟪a, x⟫_ℝ + b + ((k : ℝ) + 1) * (r ^ 2 / 16)) atTop atTop :=
      tendsto_atTop_add_const_left _ _
        ((tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop).atTop_mul_const
          (by positivity))
    exact tendsto_atTop_mono' _ hlow hlim

end Riesz1
