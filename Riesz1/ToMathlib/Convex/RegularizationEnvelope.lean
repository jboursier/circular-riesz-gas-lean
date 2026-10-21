/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Convex.Continuous
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Topology.UniformSpace.Dini

/-!
# Infimal convolution with a quadratic: convexity and limits

Let `E` be a real inner product space, `S ⊆ E` a nonempty convex set, and `g : E → ℝ` a convex
function on `S` with an affine minorant `x ↦ ⟪a, x⟫ + b` on `S`. For `θ > 0` the infimal
convolution

`moreauEnvelope S g θ x = inf_{y ∈ S} (g y + (θ / 2) ‖x - y‖²)`

is a finite convex function on `E` (Lemma `convexOn_moreauEnvelope`). It is nondecreasing in `θ`,
it lies below `g` on `S`, and it increases to `g` pointwise on `S` as `θ → ∞` where `g` is lower
semicontinuous (Lemma `eventually_le_moreauEnvelope`). On each compact subset of the interior of
`S` the convergence is uniform by Dini's theorem (Lemma `tendstoUniformlyOn_moreauEnvelope`). Outside
the closure of `S` the envelope tends to `+∞` on a neighbourhood of each point, uniformly for
`θ` large (Lemma `le_moreauEnvelope_of_gap`).

These are the convex-analysis ingredients of Lemma 3.7. The mollification step is in
`Riesz1/ToMathlib/Convex/Regularization.lean`.
-/

public section

open Set Filter Topology
open scoped InnerProductSpace

namespace Riesz1

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The infimal convolution `x ↦ inf_{y ∈ S} (g y + (θ / 2) ‖x - y‖²)`, with the infimum taken over
the set `S`. Under the standing hypotheses of this file (`S` nonempty, and `g` bounded below on `S`
by an affine function) the set of values is bounded below, so `sInf` is its infimum. -/
noncomputable def moreauEnvelope (S : Set E) (g : E → ℝ) (θ : ℝ) (x : E) : ℝ :=
  sInf ((fun y => g y + θ / 2 * ‖x - y‖ ^ 2) '' S)

variable {S : Set E} {g : E → ℝ} {a : E} {b : ℝ}

/-- Completing the square: for `θ > 0` and `x, y ∈ E`, the value at `y` of the quadratic penalty
is at least `⟪a, x⟫ - ‖a‖² / (2θ)` minus the linear term, that is
`⟪a, x⟫ - ‖a‖² / (2θ) - ⟪a, y⟫ ≤ (θ / 2) ‖x - y‖²`. -/
lemma affine_sub_le_quadratic {θ : ℝ} (hθ : 0 < θ) (x y : E) :
    ⟪a, x⟫_ℝ - ‖a‖ ^ 2 / (2 * θ) ≤ ⟪a, y⟫_ℝ + θ / 2 * ‖x - y‖ ^ 2 := by
  have hu : ⟪a, x⟫_ℝ = ⟪a, y⟫_ℝ + ⟪a, x - y⟫_ℝ := by
    rw [← inner_add_right, add_sub_cancel]
  -- `‖θ (x - y) - a‖² = θ² ‖x - y‖² - 2 θ ⟪a, x - y⟫ + ‖a‖² ≥ 0`
  have key : 0 ≤ ‖θ • (x - y) - a‖ ^ 2 := by positivity
  have hc := real_inner_comm a (x - y)
  rw [norm_sub_sq_real, norm_smul, real_inner_smul_left, mul_pow, Real.norm_eq_abs, sq_abs,
    hc] at key
  have h2 : ⟪a, x - y⟫_ℝ - θ / 2 * ‖x - y‖ ^ 2 ≤ ‖a‖ ^ 2 / (2 * θ) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [key]
  linarith

/-- The infimum defining `moreauEnvelope` is bounded below by its affine lower bound. -/
lemma envelope_image_bddBelow {θ : ℝ} (hθ : 0 < θ) (hg : ∀ y ∈ S, ⟪a, y⟫_ℝ + b ≤ g y) (x : E) :
    BddBelow ((fun y => g y + θ / 2 * ‖x - y‖ ^ 2) '' S) := by
  refine ⟨⟪a, x⟫_ℝ + b - ‖a‖ ^ 2 / (2 * θ), ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  have h1 := affine_sub_le_quadratic (a := a) hθ x y
  have h2 := hg y hy
  show _ ≤ g y + θ / 2 * ‖x - y‖ ^ 2
  linarith

/-- The infimal convolution is at least `⟪a, x⟫ + b - ‖a‖² / (2θ)`. -/
lemma le_moreauEnvelope {θ : ℝ} (hθ : 0 < θ) (hS : S.Nonempty)
    (hg : ∀ y ∈ S, ⟪a, y⟫_ℝ + b ≤ g y) (x : E) :
    ⟪a, x⟫_ℝ + b - ‖a‖ ^ 2 / (2 * θ) ≤ moreauEnvelope S g θ x := by
  refine le_csInf (hS.image _) ?_
  rintro _ ⟨y, hy, rfl⟩
  have h1 := affine_sub_le_quadratic (a := a) hθ x y
  have h2 := hg y hy
  show _ ≤ g y + θ / 2 * ‖x - y‖ ^ 2
  linarith

/-- The infimal convolution is at most the value `g y + (θ / 2) ‖x - y‖²` at each `y ∈ S`. -/
lemma moreauEnvelope_le {θ : ℝ} (hθ : 0 < θ) (hg : ∀ y ∈ S, ⟪a, y⟫_ℝ + b ≤ g y) {y : E}
    (hy : y ∈ S) (x : E) :
    moreauEnvelope S g θ x ≤ g y + θ / 2 * ‖x - y‖ ^ 2 :=
  csInf_le (envelope_image_bddBelow hθ hg x) ⟨y, hy, rfl⟩

/-- On `S` the infimal convolution is at most `g`. -/
lemma moreauEnvelope_le_self {θ : ℝ} (hθ : 0 < θ) (hg : ∀ y ∈ S, ⟪a, y⟫_ℝ + b ≤ g y) {x : E}
    (hx : x ∈ S) : moreauEnvelope S g θ x ≤ g x := by
  simpa using moreauEnvelope_le hθ hg hx x

/-- The infimal convolution increases with the parameter `θ`. -/
lemma moreauEnvelope_mono {θ₁ θ₂ : ℝ} (hθ₁ : 0 < θ₁) (hθ : θ₁ ≤ θ₂) (hS : S.Nonempty)
    (hg : ∀ y ∈ S, ⟪a, y⟫_ℝ + b ≤ g y) (x : E) :
    moreauEnvelope S g θ₁ x ≤ moreauEnvelope S g θ₂ x := by
  refine le_csInf (hS.image _) ?_
  rintro _ ⟨y, hy, rfl⟩
  refine (moreauEnvelope_le hθ₁ hg hy x).trans ?_
  show _ ≤ g y + θ₂ / 2 * ‖x - y‖ ^ 2
  gcongr

/-- The squared norm of a convex combination is at most the convex combination of the squared
norms. -/
lemma norm_sq_convex_combination_le {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t = 1)
    (u v : E) : ‖s • u + t • v‖ ^ 2 ≤ s * ‖u‖ ^ 2 + t * ‖v‖ ^ 2 := by
  obtain rfl : t = 1 - s := by linarith
  -- The defect `s t ‖u - v‖²` is nonnegative.
  have e1 := norm_add_sq_real (s • u) ((1 - s) • v)
  rw [norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right, mul_pow, mul_pow,
    Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs] at e1
  have e2 := norm_sub_sq_real u v
  have e3 : s * (1 - s) * ‖u - v‖ ^ 2 = s * (1 - s) * (‖u‖ ^ 2 - 2 * ⟪u, v⟫_ℝ + ‖v‖ ^ 2) := by
    rw [e2]
  have hprod : 0 ≤ s * (1 - s) * ‖u - v‖ ^ 2 := mul_nonneg (mul_nonneg hs ht) (sq_nonneg _)
  nlinarith [e1, e3, hprod]

/-- The infimal convolution is convex on the whole space when `g` is convex on `S`. -/
lemma convexOn_moreauEnvelope {θ : ℝ} (hθ : 0 < θ) (hSc : Convex ℝ S) (hgc : ConvexOn ℝ S g)
    (hS : S.Nonempty) (hg : ∀ y ∈ S, ⟪a, y⟫_ℝ + b ≤ g y) :
    ConvexOn ℝ univ (moreauEnvelope S g θ) := by
  refine ⟨convex_univ, fun x₁ _ x₂ _ s t hs ht hst => ?_⟩
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨_, ⟨y₁, hy₁, rfl⟩, hr₁⟩ :=
    exists_lt_of_csInf_lt (hS.image _) (lt_add_of_pos_right (moreauEnvelope S g θ x₁) (half_pos hε))
  obtain ⟨_, ⟨y₂, hy₂, rfl⟩, hr₂⟩ :=
    exists_lt_of_csInf_lt (hS.image _) (lt_add_of_pos_right (moreauEnvelope S g θ x₂) (half_pos hε))
  dsimp only at hr₁ hr₂
  -- The point `s y₁ + t y₂` is admissible for the envelope at `s x₁ + t x₂`.
  have hyS : s • y₁ + t • y₂ ∈ S := hSc hy₁ hy₂ hs ht hst
  have hgy : g (s • y₁ + t • y₂) ≤ s * g y₁ + t * g y₂ := hgc.2 hy₁ hy₂ hs ht hst
  have hE := moreauEnvelope_le hθ hg hyS (s • x₁ + t • x₂)
  have hrw : s • x₁ + t • x₂ - (s • y₁ + t • y₂) = s • (x₁ - y₁) + t • (x₂ - y₂) := by
    module
  rw [hrw] at hE
  have hnorm := norm_sq_convex_combination_le hs ht hst (x₁ - y₁) (x₂ - y₂)
  have hθ2 : 0 ≤ θ / 2 := by positivity
  have hq := mul_le_mul_of_nonneg_left hnorm hθ2
  have hs₁ := mul_le_mul_of_nonneg_left hr₁.le hs
  have ht₂ := mul_le_mul_of_nonneg_left hr₂.le ht
  have hsum : s * (ε / 2) + t * (ε / 2) = ε / 2 := by linear_combination (ε / 2) * hst
  simp only [smul_eq_mul]
  nlinarith [hE, hgy, hq, hs₁, ht₂, hsum]

/-- The infimal convolution is continuous when it is convex on `E`, since a finite convex function
on a finite-dimensional space is continuous. -/
lemma continuous_moreauEnvelope [FiniteDimensional ℝ E] {θ : ℝ} (hθ : 0 < θ) (hSc : Convex ℝ S)
    (hgc : ConvexOn ℝ S g) (hS : S.Nonempty) (hg : ∀ y ∈ S, ⟪a, y⟫_ℝ + b ≤ g y) :
    Continuous (moreauEnvelope S g θ) := by
  have h := (convexOn_moreauEnvelope hθ hSc hgc hS hg).continuousOn_interior
  rw [interior_univ] at h
  exact continuousOn_univ.1 h

/-- Pointwise lower limit. If `g` is lower semicontinuous on `S` at `x ∈ S` in the sense that
values exceeding `c < g x` persist near `x` on `S`, then the infimal convolution at `x` eventually
exceeds `c` as `θ → ∞`. The penalty `(θ / 2) ‖x - y‖²` dominates the linear term
`‖a‖ ‖x - y‖` once `θ` is large, uniformly for `y` outside a ball of radius `r`. -/
lemma eventually_le_moreauEnvelope (hg : ∀ y ∈ S, ⟪a, y⟫_ℝ + b ≤ g y) {x : E} (hx : x ∈ S)
    (hlsc : ∀ c < g x, ∃ r > 0, ∀ y ∈ S, dist y x < r → c < g y) {c : ℝ} (hc : c < g x) :
    ∀ᶠ θ in atTop, c ≤ moreauEnvelope S g θ x := by
  obtain ⟨r, hr, hball⟩ := hlsc c hc
  set M : ℝ := |c - ⟪a, x⟫_ℝ - b| + 1 with hM_def
  have hM : 0 < M := by positivity
  filter_upwards [eventually_ge_atTop (4 * M / r ^ 2 + 4 * ‖a‖ / r)] with θ hθ
  have hθ0 : 0 ≤ θ := le_trans (by positivity) hθ
  have hθr : 4 * ‖a‖ ≤ θ * r := by
    have h : 4 * ‖a‖ / r ≤ θ := le_trans (le_add_of_nonneg_left (by positivity)) hθ
    rwa [div_le_iff₀ hr] at h
  have hθr2 : 4 * M ≤ θ * r ^ 2 := by
    have h : 4 * M / r ^ 2 ≤ θ := le_trans (le_add_of_nonneg_right (by positivity)) hθ
    rwa [div_le_iff₀ (by positivity)] at h
  have hSne : S.Nonempty := ⟨x, hx⟩
  refine le_csInf (hSne.image _) ?_
  rintro _ ⟨y, hy, rfl⟩
  show c ≤ g y + θ / 2 * ‖x - y‖ ^ 2
  by_cases hxy : dist y x < r
  · have h1 := hball y hy hxy
    have h2 : 0 ≤ θ / 2 * ‖x - y‖ ^ 2 := by positivity
    linarith
  · have hsr : r ≤ ‖x - y‖ := by
      rw [norm_sub_rev, ← dist_eq_norm]
      exact not_lt.mp hxy
    have hu : ⟪a, x⟫_ℝ = ⟪a, y⟫_ℝ + ⟪a, x - y⟫_ℝ := by
      rw [← inner_add_right, add_sub_cancel]
    have hP : ⟪a, x - y⟫_ℝ ≤ ‖a‖ * ‖x - y‖ := real_inner_le_norm a (x - y)
    have hgy := hg y hy
    have hMc : c - ⟪a, x⟫_ℝ - b < M := by
      have := le_abs_self (c - ⟪a, x⟫_ℝ - b)
      rw [hM_def]
      linarith
    have hs0 : 0 ≤ ‖x - y‖ := norm_nonneg _
    -- With `s = ‖x - y‖ ≥ r`: `4 ‖a‖ ≤ θ s` and `4 M ≤ θ s²`.
    have h4 : 4 * ‖a‖ ≤ θ * ‖x - y‖ :=
      le_trans hθr (mul_le_mul_of_nonneg_left hsr hθ0)
    have hA : 4 * ‖a‖ * ‖x - y‖ ≤ θ * ‖x - y‖ ^ 2 := by
      have := mul_le_mul_of_nonneg_right h4 hs0
      linarith [sq ‖x - y‖]
    have hB : 4 * M ≤ θ * ‖x - y‖ ^ 2 :=
      le_trans hθr2 (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr.le hsr 2) hθ0)
    -- Chain: `g y + (θ/2) s² ≥ ⟪a, x⟫ + b - ‖a‖ s + (θ/2) s² ≥ ⟪a, x⟫ + b + M > c`.
    linarith

/-- Large values away from `S`. If every point of `S` lies at distance at least `r` from `x`, then
for `θ` with `16 ‖a‖ ≤ θ r` and every `y` with `dist y x < r / 2`, the infimal convolution at `y` is
at least `⟪a, x⟫ + b + θ r² / 16`. Every admissible point `w ∈ S` is far from `y`, so its penalty
`(θ / 2) ‖y - w‖²` beats the linear term, and the bound does not depend on `y`. -/
lemma le_moreauEnvelope_of_gap {θ r : ℝ} (hr : 0 < r) (hθ : 16 * ‖a‖ ≤ θ * r) (hS : S.Nonempty)
    (hg : ∀ y ∈ S, ⟪a, y⟫_ℝ + b ≤ g y) {x : E} (hgap : ∀ w ∈ S, r ≤ dist w x) {y : E}
    (hy : dist y x < r / 2) :
    ⟪a, x⟫_ℝ + b + θ * r ^ 2 / 16 ≤ moreauEnvelope S g θ y := by
  refine le_csInf (hS.image _) ?_
  rintro _ ⟨w, hw, rfl⟩
  show _ ≤ g w + θ / 2 * ‖y - w‖ ^ 2
  have hθ0 : 0 ≤ θ := by
    by_contra h
    nlinarith [mul_neg_of_neg_of_pos (not_le.mp h) hr, norm_nonneg a]
  have hs : r ≤ ‖w - x‖ := by
    have := hgap w hw
    rwa [dist_eq_norm] at this
  have hyx : ‖y - x‖ < r / 2 := by
    rwa [dist_eq_norm] at hy
  have htri : ‖w - x‖ ≤ ‖w - y‖ + ‖y - x‖ := by
    have := norm_add_le (w - y) (y - x)
    rwa [sub_add_sub_cancel] at this
  -- Distance from `y` to `w` is at least half the distance from `x` to `w`.
  have hwy : ‖w - x‖ / 2 ≤ ‖y - w‖ := by
    rw [norm_sub_rev y w]
    linarith
  have hsq : (‖w - x‖ / 2) ^ 2 ≤ ‖y - w‖ ^ 2 := pow_le_pow_left₀ (by positivity) hwy 2
  have hpen : θ / 2 * (‖w - x‖ / 2) ^ 2 ≤ θ / 2 * ‖y - w‖ ^ 2 :=
    mul_le_mul_of_nonneg_left hsq (by positivity)
  -- Affine lower bound at `w`, expanded around `x`.
  have hgw := hg w hw
  have hu : ⟪a, w⟫_ℝ = ⟪a, x⟫_ℝ + ⟪a, w - x⟫_ℝ := by
    rw [← inner_add_right, add_sub_cancel]
  have hC : -(‖a‖ * ‖w - x‖) ≤ ⟪a, w - x⟫_ℝ := by
    have := abs_real_inner_le_norm a (w - x)
    linarith [neg_abs_le ⟪a, w - x⟫_ℝ]
  -- `16 ‖a‖ ‖w - x‖ ≤ θ ‖w - x‖²`, and `θ r² ≤ θ ‖w - x‖²`.
  have hNs : 16 * ‖a‖ * ‖w - x‖ ≤ θ * ‖w - x‖ ^ 2 := by
    have h16 : 16 * ‖a‖ ≤ θ * ‖w - x‖ := le_trans hθ (mul_le_mul_of_nonneg_left hs hθ0)
    have := mul_le_mul_of_nonneg_right h16 (norm_nonneg (w - x))
    linarith [sq ‖w - x‖]
  have hr2 : θ * r ^ 2 ≤ θ * ‖w - x‖ ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr.le hs 2) hθ0
  -- Chain: `g w + (θ/2)‖y - w‖² ≥ ⟪a, x⟫ + b - ‖a‖ s + θ s² / 8 ≥ ⟪a, x⟫ + b + θ r² / 16`.
  linarith

/-- Dini's theorem for the infimal convolution. Let `S` be convex with `g` convex on `S` and
lower semicontinuous on `S`. Then the envelopes `moreauEnvelope S g (n + 1)` converge to `g`
uniformly on every compact subset of the interior of `S`. -/
lemma tendstoUniformlyOn_moreauEnvelope [FiniteDimensional ℝ E] (hSc : Convex ℝ S)
    (hgc : ConvexOn ℝ S g) (hS : S.Nonempty) (hg : ∀ y ∈ S, ⟪a, y⟫_ℝ + b ≤ g y)
    (hlsc : ∀ x ∈ S, ∀ c < g x, ∃ r > 0, ∀ y ∈ S, dist y x < r → c < g y) {K : Set E}
    (hK : IsCompact K) (hKS : K ⊆ interior S) :
    TendstoUniformlyOn (fun n : ℕ => moreauEnvelope S g ((n : ℝ) + 1)) g atTop K := by
  have hθ : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => by positivity
  refine Monotone.tendstoUniformlyOn_of_forall_tendsto hK (fun n => ?_)
    (fun x _ n m hnm => moreauEnvelope_mono (hθ n)
      (by have := (Nat.cast_le (α := ℝ)).2 hnm; linarith) hS hg x) ?_ (fun x hx => ?_)
  · exact (continuous_moreauEnvelope (hθ n) hSc hgc hS hg).continuousOn
  · exact (hgc.continuousOn_interior).mono hKS
  · have hxS : x ∈ S := interior_subset (hKS hx)
    rw [tendsto_order]
    refine ⟨fun c hc => ?_, fun c hc => Eventually.of_forall fun n => ?_⟩
    · have hc' : (c + g x) / 2 < g x := by linarith
      have hev := eventually_le_moreauEnvelope hg hxS (hlsc x hxS) hc'
      have hcast : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
        tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
      filter_upwards [hcast.eventually hev] with n hn
      show c < moreauEnvelope S g ((n : ℝ) + 1) x
      linarith
    · exact lt_of_le_of_lt (moreauEnvelope_le_self (hθ n) hg hxS) hc

end Riesz1
