/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.GradientSplittingWindowPVLimit

/-!
# Principal value of `Φ g'` with integer endpoints

`tendsto_truncated_by_parts` needs non-integer endpoints. In a partial window the endpoints of the
background integral can be integers (when a particle sits at distance `t` from the anchor). There
the coefficient `Φ` vanishes on a neighbourhood of the integer endpoint, and the integrand is zero
near it. This file moves each integer endpoint to a nearby non-integer point, applies
`tendsto_truncated_by_parts`, and transfers the boundary terms, which vanish with `Φ`.
-/

@[expose] public section

open Set MeasureTheory Filter Topology intervalIntegral
open scoped ContDiff

namespace Riesz1

noncomputable section

/-- If `Φ` vanishes on an open ball, then `Φ`, `Φ'` and `Φ''` vanish at its points. -/
lemma zero_triple_of_ball {Φ : ℝ → ℝ} {c ε v : ℝ} (hv : v ∈ Metric.ball c ε)
    (hΦ : ∀ ⦃y : ℝ⦄, dist y c < ε → Φ y = 0) :
    Φ v = 0 ∧ deriv Φ v = 0 ∧ deriv (deriv Φ) v = 0 := by
  have hU : Metric.ball c ε ∈ 𝓝 v := Metric.isOpen_ball.mem_nhds hv
  have hΦe : Φ =ᶠ[𝓝 v] fun _ => (0 : ℝ) := by
    filter_upwards [hU] with w hw
    exact hΦ (Metric.mem_ball.1 hw)
  have hdeq : deriv Φ =ᶠ[𝓝 v] fun _ => (0 : ℝ) := by
    filter_upwards [hU] with w hw
    have hΦw : Φ =ᶠ[𝓝 w] fun _ => (0 : ℝ) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hw] with y hy
      exact hΦ (Metric.mem_ball.1 hy)
    exact (hΦw.deriv_eq).trans (deriv_const w 0)
  exact ⟨hΦe.self_of_nhds, (hΦe.deriv_eq).trans (deriv_const v 0),
    (hdeq.deriv_eq).trans (deriv_const v 0)⟩

/-- Moving a left endpoint `a` into the interior: there is `a' ∈ [a, a + (b-a)/4]`, not an integer,
such that either `a' = a`, or `Φ` and `Φ'` vanish on `[a, a']`. -/
lemma exists_shrink_left {Φ : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (ha : (∃ m : ℤ, a = m) → ∀ᶠ v in 𝓝 a, Φ v = 0) :
    ∃ a' : ℝ, a ≤ a' ∧ a' ≤ a + (b - a) / 4 ∧ (∀ m : ℤ, a' ≠ m) ∧
      (a' = a ∨ ∀ v ∈ Icc a a', Φ v = 0 ∧ deriv Φ v = 0 ∧ deriv (deriv Φ) v = 0) := by
  by_cases hint : ∃ m : ℤ, a = m
  · obtain ⟨n, hn⟩ := hint
    obtain ⟨ε, hε, hΦ⟩ := Metric.eventually_nhds_iff.1 (ha ⟨n, hn⟩)
    set η : ℝ := min (1 / 2) (min (ε / 2) ((b - a) / 4)) with hη
    have hηpos : 0 < η := lt_min (by norm_num) (lt_min (by linarith) (by linarith))
    have hη1 : η ≤ 1 / 2 := min_le_left _ _
    have hηε : η ≤ ε / 2 := (min_le_right _ _).trans (min_le_left _ _)
    have hηb : η ≤ (b - a) / 4 := (min_le_right _ _).trans (min_le_right _ _)
    refine ⟨a + η, by linarith, by linarith, ?_, Or.inr ?_⟩
    · intro m hm
      have h1 : ((m - n : ℤ) : ℝ) = η := by push_cast; linarith
      have h2 : (0 : ℝ) < ((m - n : ℤ) : ℝ) := by rw [h1]; exact hηpos
      have h3 : ((m - n : ℤ) : ℝ) < 1 := by rw [h1]; linarith
      have h2' : (0 : ℤ) < m - n := by exact_mod_cast h2
      have h3' : m - n < 1 := by exact_mod_cast h3
      omega
    · intro v hv
      have hvmem : v ∈ Metric.ball a ε := by
        rw [Metric.mem_ball, Real.dist_eq, abs_lt]
        constructor
        · linarith [hv.1]
        · linarith [hv.2]
      exact zero_triple_of_ball hvmem hΦ
  · refine ⟨a, le_rfl, by linarith [show (0 : ℝ) ≤ (b - a) / 4 by linarith], ?_, Or.inl rfl⟩
    intro m hm
    exact hint ⟨m, hm⟩

/-- Moving a right endpoint `b` into the interior: there is `b' ∈ [b - (b-a)/4, b]`, not an integer,
such that either `b' = b`, or `Φ` and `Φ'` vanish on `[b', b]`. -/
lemma exists_shrink_right {Φ : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hb : (∃ m : ℤ, b = m) → ∀ᶠ v in 𝓝 b, Φ v = 0) :
    ∃ b' : ℝ, b - (b - a) / 4 ≤ b' ∧ b' ≤ b ∧ (∀ m : ℤ, b' ≠ m) ∧
      (b' = b ∨ ∀ v ∈ Icc b' b, Φ v = 0 ∧ deriv Φ v = 0 ∧ deriv (deriv Φ) v = 0) := by
  by_cases hint : ∃ m : ℤ, b = m
  · obtain ⟨n, hn⟩ := hint
    obtain ⟨ε, hε, hΦ⟩ := Metric.eventually_nhds_iff.1 (hb ⟨n, hn⟩)
    set η : ℝ := min (1 / 2) (min (ε / 2) ((b - a) / 4)) with hη
    have hηpos : 0 < η := lt_min (by norm_num) (lt_min (by linarith) (by linarith))
    have hη1 : η ≤ 1 / 2 := min_le_left _ _
    have hηε : η ≤ ε / 2 := (min_le_right _ _).trans (min_le_left _ _)
    have hηb : η ≤ (b - a) / 4 := (min_le_right _ _).trans (min_le_right _ _)
    refine ⟨b - η, by linarith, by linarith, ?_, Or.inr ?_⟩
    · intro m hm
      have h1 : ((n - m : ℤ) : ℝ) = η := by push_cast; linarith
      have h2 : (0 : ℝ) < ((n - m : ℤ) : ℝ) := by rw [h1]; exact hηpos
      have h3 : ((n - m : ℤ) : ℝ) < 1 := by rw [h1]; linarith
      have h2' : (0 : ℤ) < n - m := by exact_mod_cast h2
      have h3' : n - m < 1 := by exact_mod_cast h3
      omega
    · intro v hv
      have hvmem : v ∈ Metric.ball b ε := by
        rw [Metric.mem_ball, Real.dist_eq, abs_lt]
        constructor
        · linarith [hv.1]
        · linarith [hv.2]
      exact zero_triple_of_ball hvmem hΦ
  · refine ⟨b, by linarith [show (0 : ℝ) ≤ (b - a) / 4 by linarith], le_rfl, ?_, Or.inl rfl⟩
    intro m hm
    exact hint ⟨m, hm⟩

/-- Integrals over `[a, b]` and `[a', b']` agree when the integrand vanishes on the removed pieces. -/
lemma integral_eq_of_zero_pieces {F : ℝ → ℝ} {a a' b' b : ℝ} (hF : IntervalIntegrable F volume a b)
    (ha : a ≤ a') (hab' : a' ≤ b') (hb : b' ≤ b)
    (hl : a' = a ∨ ∀ v ∈ Icc a a', F v = 0) (hr : b' = b ∨ ∀ v ∈ Icc b' b, F v = 0) :
    ∫ v in a..b, F v = ∫ v in a'..b', F v := by
  have hsub : ∀ c d : ℝ, a ≤ c → c ≤ b → a ≤ d → d ≤ b → IntervalIntegrable F volume c d :=
    fun c d h1 h2 h3 h4 => hF.mono_set (Set.uIcc_subset_uIcc
      (by rw [uIcc_of_le (h1.trans h2)]; exact ⟨h1, h2⟩)
      (by rw [uIcc_of_le (h3.trans h4)]; exact ⟨h3, h4⟩))
  have hal : a ≤ b := ha.trans (hab'.trans hb)
  have hbl : a' ≤ b := hab'.trans hb
  have hal' : a ≤ b' := ha.trans hab'
  have h1 : ∫ v in a..a', F v = 0 := by
    rcases hl with h | h
    · rw [h, intervalIntegral.integral_same]
    · rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) (fun v hv => h v (by
        rw [uIcc_of_le ha] at hv; exact hv)), intervalIntegral.integral_zero]
  have h3 : ∫ v in b'..b, F v = 0 := by
    rcases hr with h | h
    · rw [h, intervalIntegral.integral_same]
    · rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) (fun v hv => h v (by
        rw [uIcc_of_le hb] at hv; exact hv)), intervalIntegral.integral_zero]
  have eq1 : ∫ v in a..b, F v = (∫ v in a..a', F v) + ∫ v in a'..b, F v :=
    (intervalIntegral.integral_add_adjacent_intervals (hsub a a' le_rfl hal ha hbl)
      (hsub a' b ha hbl hal le_rfl)).symm
  have eq2 : ∫ v in a'..b, F v = (∫ v in a'..b', F v) + ∫ v in b'..b, F v :=
    (intervalIntegral.integral_add_adjacent_intervals (hsub a' b' ha hbl hal' hb)
      (hsub b' b hal' hb hal le_rfl)).symm
  rw [eq1, eq2, h1, h3, zero_add, add_zero]

/-- **Principal value of `Φ g'` with possibly integer endpoints.** For a `C¹` coefficient `Φ`, and
`a < b`, if `Φ` vanishes near an integer endpoint, the truncated integrals over the allowed set
converge to `Φ(b) g(b) - Φ(a) g(a) - ∫_a^b Φ' g`. -/
theorem tendsto_truncated_by_parts_gen {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {Φ : ℝ → ℝ}
    (hΦ : ContDiff ℝ 1 Φ) {a b : ℝ} (hab : a < b)
    (ha : (∃ m : ℤ, a = m) → ∀ᶠ v in 𝓝 a, Φ v = 0)
    (hb : (∃ m : ℤ, b = m) → ∀ᶠ v in 𝓝 b, Φ v = 0) :
    Tendsto (fun δ : ℝ => ∫ v in a..b,
        (gradAllowed δ).indicator (fun v => Φ v * deriv (hurwitzKernel s) v) v) (𝓝[>] 0)
      (𝓝 (Φ b * hurwitzKernel s b - Φ a * hurwitzKernel s a
        - ∫ v in a..b, deriv Φ v * hurwitzKernel s v)) := by
  obtain ⟨a', ha1, ha2, ha3, ha4⟩ := exists_shrink_left hab ha
  obtain ⟨b', hb1, hb2, hb3, hb4⟩ := exists_shrink_right hab hb
  have hab' : a' < b' := by linarith
  have hmain := tendsto_truncated_by_parts hs0 hs1 hΦ hab'.le ha3 hb3
  -- boundary values agree
  have hΦa : Φ a' * hurwitzKernel s a' = Φ a * hurwitzKernel s a := by
    rcases ha4 with h | h
    · rw [h]
    · rw [(h a ⟨le_rfl, ha1⟩).1, (h a' ⟨ha1, le_rfl⟩).1]
      ring
  have hΦb : Φ b' * hurwitzKernel s b' = Φ b * hurwitzKernel s b := by
    rcases hb4 with h | h
    · rw [h]
    · rw [(h b ⟨hb2, le_rfl⟩).1, (h b' ⟨le_rfl, hb2⟩).1]
      ring
  -- the derivative part is unchanged
  have hint2 : IntervalIntegrable (fun v => deriv Φ v * hurwitzKernel s v) volume a b :=
    (hurwitzKernel_intervalIntegrable_all hs0 hs1 a b).continuousOn_mul
      (hΦ.continuous_deriv le_rfl).continuousOn
  have hdA : ∫ v in a..b, deriv Φ v * hurwitzKernel s v
      = ∫ v in a'..b', deriv Φ v * hurwitzKernel s v :=
    integral_eq_of_zero_pieces hint2 ha1 hab'.le hb2
      (ha4.imp_right fun h v hv => by simp [(h v hv).2.1])
      (hb4.imp_right fun h v hv => by simp [(h v hv).2.1])
  -- the principal-value part agrees for every δ > 0
  have hF1 : ∀ δ : ℝ, 0 < δ → ∫ v in a..b,
      (gradAllowed δ).indicator (fun v => Φ v * deriv (hurwitzKernel s) v) v
        = ∫ v in a'..b', (gradAllowed δ).indicator (fun v => Φ v * deriv (hurwitzKernel s) v) v := by
    intro δ hδ
    have hGc : ContinuousOn (deriv (hurwitzKernel s)) (gradAllowed δ) := fun v hv =>
      (contDiffAt_deriv_hurwitzKernel hs0 hs1 (coe_ne_zero_of_mem_gradAllowed hδ hv)).continuousAt
        |>.continuousWithinAt
    have hcont : ContinuousOn (fun v => Φ v * deriv (hurwitzKernel s) v) (gradAllowed δ) :=
      hΦ.continuous.continuousOn.mul hGc
    have hI := intervalIntegrable_indicator_of_continuousOn (gradAllowed_isClosed δ) hcont a b
    exact integral_eq_of_zero_pieces hI ha1 hab'.le hb2
      (ha4.imp_right fun h v hv => by simp [(h v hv).1])
      (hb4.imp_right fun h v hv => by simp [(h v hv).1])
  have hint : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∫ v in a'..b',
      (gradAllowed δ).indicator (fun v => Φ v * deriv (hurwitzKernel s) v) v
        = ∫ v in a..b, (gradAllowed δ).indicator (fun v => Φ v * deriv (hurwitzKernel s) v) v := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact (hF1 δ hδ).symm
  have hvalue : Φ b' * hurwitzKernel s b' - Φ a' * hurwitzKernel s a'
      - ∫ v in a'..b', deriv Φ v * hurwitzKernel s v
      = Φ b * hurwitzKernel s b - Φ a * hurwitzKernel s a
        - ∫ v in a..b, deriv Φ v * hurwitzKernel s v := by
    rw [hΦb, hΦa, hdA]
  rw [← hvalue]
  exact hmain.congr' hint

end

end Riesz1
