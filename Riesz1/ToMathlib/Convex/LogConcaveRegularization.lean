/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.Convex.Regularization

/-!
# Smooth convex approximation on an open domain

The Moreau envelopes can be mollified directly on the finite open domain. This avoids
constructing an extended-real lower-semicontinuous closure when only interior convergence
and divergence outside the closed domain are needed. The mollification construction follows
`convex_regularization`, using the same envelope and convolution lemmas.
-/

public section

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace ContDiff

namespace Riesz1

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

/-- Smooth convex approximation of a finite convex function on a nonempty open convex
set, with a uniform affine lower bound and divergence away from its closure. -/
theorem convex_regularization_open {S : Set E} {g : E → ℝ} {a : E} {b : ℝ}
    (hSo : IsOpen S) (hSne : S.Nonempty) (hgc : ConvexOn ℝ S g)
    (hg_aff : ∀ x ∈ S, ⟪a, x⟫_ℝ + b ≤ g x) :
    ∃ Bk : ℕ → E → ℝ,
      (∀ k, ContDiff ℝ ∞ (Bk k) ∧ ConvexOn ℝ univ (Bk k) ∧
        ∀ x, ⟪a, x⟫_ℝ + b - ‖a‖ ^ 2 / 2 ≤ Bk k x) ∧
      (∀ K : Set E, IsCompact K → K ⊆ S → TendstoUniformlyOn Bk g atTop K) ∧
      (∀ x, x ∉ closure S → Tendsto (fun k => Bk k x) atTop atTop) := by
  classical
  have hSconv := hgc.1
  have hcont : ContinuousOn g S := by
    simpa only [hSo.interior_eq] using hgc.continuousOn_interior
  have hlsc : ∀ x ∈ S, ∀ c < g x, ∃ r > 0, ∀ y ∈ S, dist y x < r → c < g y := by
    intro x hx c hc
    obtain ⟨r, hr, hnear⟩ := Metric.continuousWithinAt_iff.1 (hcont x hx) (g x - c)
      (sub_pos.mpr hc)
    refine ⟨r, hr, fun y hy hxy => ?_⟩
    have hh := hnear hy hxy
    rw [Real.dist_eq] at hh
    linarith [neg_abs_le (g y - g x)]
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
    have hDini := tendstoUniformlyOn_moreauEnvelope hSconv hgc hSne hg_aff hlsc hK (by simpa only [hSo.interior_eq] using hKS)
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
    have htri := abs_sub_le (g x) (moreauEnvelope S g ((n : ℝ) + 1) x)
      (mollify (moreauEnvelope S g ((n : ℝ) + 1)) (φ n) x)
    rw [abs_sub_comm (moreauEnvelope S g ((n : ℝ) + 1) x)] at htri
    show |g x - mollify (moreauEnvelope S g ((n : ℝ) + 1)) (φ n) x| < ε
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
