/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.MetricSpace.Cauchy
public import Mathlib.Tactic.Linarith

/-! # Cauchy sequences under a graph energy identity

A linear map whose squared norm is the sum of two graph energies carries
sequences Cauchy in both graph coordinates to Cauchy sequences.
-/

public section

open Filter

namespace Riesz1

theorem cauchySeq_of_linear_graph_energy {T V E W : Type*}
    [AddCommGroup T] [Module ℝ T]
    [NormedAddCommGroup V] [Module ℝ V]
    [NormedAddCommGroup E] [Module ℝ E]
    [NormedAddCommGroup W] [Module ℝ W]
    (F : T →ₗ[ℝ] V) (G : T →ₗ[ℝ] E) (A : T →ₗ[ℝ] W)
    (h : ∀ t, ‖F t‖ ^ 2 = ‖G t‖ ^ 2 + ‖A t‖ ^ 2) (f : ℕ → T)
    (hg : CauchySeq (G ∘ f)) (ha : CauchySeq (A ∘ f)) : CauchySeq (F ∘ f) := by
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  obtain ⟨K, hK⟩ := Metric.cauchySeq_iff.mp hg (ε / 2) (by linarith)
  obtain ⟨J, hJ⟩ := Metric.cauchySeq_iff.mp ha (ε / 2) (by linarith)
  refine ⟨max K J, fun m hm n hn => ?_⟩
  have hG := hK m ((le_max_left K J).trans hm) n ((le_max_left K J).trans hn)
  have hA := hJ m ((le_max_right K J).trans hm) n ((le_max_right K J).trans hn)
  have hnorm := h (f m - f n)
  simp only [map_sub] at hnorm
  simp only [Function.comp_apply, dist_eq_norm] at hG hA ⊢
  have hG0 := norm_nonneg (G (f m) - G (f n))
  have hA0 := norm_nonneg (A (f m) - A (f n))
  have hF0 := norm_nonneg (F (f m) - F (f n))
  nlinarith only [hG, hA, hnorm, hG0, hA0, hF0, hε]

end Riesz1
