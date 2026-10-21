/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Convex.Continuous
public import Mathlib.Analysis.Convex.Measure
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.LocallyConvex.Separation

/-!
# Positive support of a log-concave density

The log-concavity assumption is imposed on the whole convex domain, including points where
the density vanishes. On the positive support it implies convexity of the negative logarithm.
The support boundary is Lebesgue null. These are initial steps in the convex conditioning
argument, not the logarithmic Sobolev inequality itself.
-/

public section

open Set MeasureTheory

namespace Riesz1.LogSobolevInternal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {Ω : Set E} {f : E → ℝ}

/-- Log-concavity on all of a convex domain makes its positive-density support convex. -/
theorem convex_positive_support (hΩ : Convex ℝ Ω)
    (hlog : ∀ x ∈ Ω, ∀ y ∈ Ω, ∀ t : ℝ, 0 < t → t < 1 →
      f x ^ t * f y ^ (1 - t) ≤ f (t • x + (1 - t) • y)) :
    Convex ℝ {x | x ∈ Ω ∧ 0 < f x} := by
  intro x hx y hy s t hs ht hst
  refine ⟨hΩ hx.1 hy.1 hs ht hst, ?_⟩
  rcases hs.eq_or_lt with rfl | hs'
  · simpa [show t = 1 by linarith] using hy.2
  rcases ht.eq_or_lt with rfl | ht'
  · simpa [show s = 1 by linarith] using hx.2
  have htdef : t = 1 - s := by linarith
  rw [htdef]
  exact (mul_pos (Real.rpow_pos_of_pos hx.2 _) (Real.rpow_pos_of_pos hy.2 _)).trans_le
    (hlog x hx.1 y hy.1 s hs' (by linarith))

/-- The negative logarithm is convex wherever a log-concave density is positive. This
statement never uses a real logarithm at a zero-density point. -/
theorem convexOn_neg_log_positive_support (hΩ : Convex ℝ Ω)
    (hlog : ∀ x ∈ Ω, ∀ y ∈ Ω, ∀ t : ℝ, 0 < t → t < 1 →
      f x ^ t * f y ^ (1 - t) ≤ f (t • x + (1 - t) • y)) :
    ConvexOn ℝ {x | x ∈ Ω ∧ 0 < f x} (fun x => -Real.log (f x)) := by
  refine ⟨convex_positive_support hΩ hlog, ?_⟩
  intro x hx y hy s t hs ht hst
  rcases hs.eq_or_lt with rfl | hs'
  · simp [show t = 1 by linarith]
  rcases ht.eq_or_lt with rfl | ht'
  · simp [show s = 1 by linarith]
  have htdef : t = 1 - s := by linarith
  have hr := hlog x hx.1 y hy.1 s hs' (by linarith)
  have hl := Real.log_le_log
    (mul_pos (Real.rpow_pos_of_pos hx.2 _) (Real.rpow_pos_of_pos hy.2 _)) hr
  rw [Real.log_mul (Real.rpow_pos_of_pos hx.2 _).ne'
    (Real.rpow_pos_of_pos hy.2 _).ne', Real.log_rpow hx.2, Real.log_rpow hy.2] at hl
  simp only [smul_eq_mul]
  rw [htdef]
  linarith

/-- Convexity gives continuity of the negative logarithm on the support interior. -/
theorem continuousOn_neg_log_positive_support [FiniteDimensional ℝ E]
    (hΩ : Convex ℝ Ω)
    (hlog : ∀ x ∈ Ω, ∀ y ∈ Ω, ∀ t : ℝ, 0 < t → t < 1 →
      f x ^ t * f y ^ (1 - t) ≤ f (t • x + (1 - t) • y)) :
    ContinuousOn (fun x => -Real.log (f x)) (interior {x | x ∈ Ω ∧ 0 < f x}) :=
  (convexOn_neg_log_positive_support hΩ hlog).continuousOn_interior

/-- The positive support's boundary is null even when the conditioning domain is neither
open nor closed and the density vanishes on part of it. -/
theorem addHaar_frontier_positive_support [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (hΩ : Convex ℝ Ω)
    (hlog : ∀ x ∈ Ω, ∀ y ∈ Ω, ∀ t : ℝ, 0 < t → t < 1 →
      f x ^ t * f y ^ (1 - t) ≤ f (t • x + (1 - t) • y)) :
    μ (frontier {x | x ∈ Ω ∧ 0 < f x}) = 0 :=
  (convex_positive_support hΩ hlog).addHaar_frontier μ

/-- Separation of the strict epigraph supplies an affine minorant on an open convex domain.
This step does not require a differentiable log-concave density. -/
theorem exists_affine_minorant_open {S : Set E} {g : E → ℝ}
    (hS : IsOpen S) (hne : S.Nonempty) (hg : ConvexOn ℝ S g)
    (hgc : ContinuousOn g S) :
    ∃ (l : E →L[ℝ] ℝ) (b : ℝ), ∀ x ∈ S, l x + b ≤ g x := by
  let A : Set (E × ℝ) := {p | p.1 ∈ S ∧ g p.1 < p.2}
  have hAc : Convex ℝ A := hg.convex_strict_epigraph
  have hAo : IsOpen A := by
    have hc : ContinuousOn (fun p : E × ℝ => g p.1 - p.2) (S ×ˢ univ) :=
      (hgc.comp continuous_fst.continuousOn (fun _ hp => hp.1)).sub continuous_snd.continuousOn
    have heq : A = (S ×ˢ univ) ∩ (fun p : E × ℝ => g p.1 - p.2) ⁻¹' Iio 0 := by
      ext p
      simp only [A, mem_ofPred_eq, mem_inter_iff, mem_prod, mem_univ, and_true,
        mem_preimage, mem_Iio, sub_lt_zero]
    rw [heq]
    exact hc.isOpen_inter_preimage (hS.prod isOpen_univ) isOpen_Iio
  obtain ⟨x₀, hx₀⟩ := hne
  obtain ⟨L, hL⟩ := geometric_hahn_banach_point_open hAc hAo
    (show (x₀, g x₀ - 1) ∉ A by simp [A])
  let c : ℝ := L (0, 1)
  have hsplit (x : E) (r : ℝ) : L (x, r) = L (x, 0) + r * c := by
    have heq : (x, r) = (x, 0) + r • (0, (1 : ℝ)) := by ext <;> simp
    rw [heq, map_add, map_smul]
    rfl
  have hc : 0 < c := by
    have hh := hL (x₀, g x₀ + 1) ⟨hx₀, by linarith⟩
    rw [hsplit x₀ (g x₀ - 1), hsplit x₀ (g x₀ + 1)] at hh
    nlinarith
  let l : E →L[ℝ] ℝ := -c⁻¹ • L.comp (ContinuousLinearMap.inl ℝ E ℝ)
  let b : ℝ := L (x₀, g x₀ - 1) / c
  refine ⟨l, b, fun x hx => ?_⟩
  have hlow : (L (x₀, g x₀ - 1) - L (x, 0)) / c ≤ g x := by
    apply le_of_forall_pos_le_add
    intro ε hε
    have hh := hL (x, g x + ε) ⟨hx, by linarith⟩
    rw [hsplit x (g x + ε)] at hh
    apply le_of_lt
    rw [div_lt_iff₀ hc]
    nlinarith
  convert hlow using 1
  simp only [l, b, smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inl_apply, smul_eq_mul]
  ring

end Riesz1.LogSobolevInternal
