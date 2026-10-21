/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.LogConcave.MarginalMidpoint
public import Mathlib.Topology.Order.Compact

/-!
# From the midpoint marginal inequality to full log-concavity

A continuous midpoint-concave function is concave. The proof uses the minimum
of its difference from a chord on a compact segment. Applying this to the
logarithm of a positive continuous marginal upgrades the midpoint
Prékopa–Leindler inequality to all interpolation parameters.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Riesz1

/-- A continuous midpoint-concave real function lies above each of its chords. -/
theorem concaveOn_of_continuousOn_midpoint {s : Set ℝ} {g : ℝ → ℝ}
    (hs : Convex ℝ s) (hg : ContinuousOn g s)
    (hmid : ∀ x ∈ s, ∀ y ∈ s, (g x + g y) / 2 ≤ g ((x + y) / 2)) :
    ConcaveOn ℝ s g := by
  refine ⟨hs, ?_⟩
  intro x hx y hy a b ha hb hab
  let p : ℝ → ℝ := fun t => (1 - t) * x + t * y
  let q : ℝ → ℝ := fun t => g (p t) - ((1 - t) * g x + t * g y)
  have hp (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : p t ∈ s :=
    hs hx hy (sub_nonneg.mpr ht.2) ht.1 (by ring)
  have hpc : Continuous p := by fun_prop
  have hqc : ContinuousOn q (Icc (0 : ℝ) 1) :=
    (hg.comp hpc.continuousOn hp).sub (by fun_prop)
  obtain ⟨t, ht, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr zero_le_one) hqc
  have hnonneg : 0 ≤ q t := by
    by_contra hn
    have hneg : q t < 0 := lt_of_not_ge hn
    by_cases ht2 : t ≤ 1 / 2
    · have hu : 2 * t ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht.1], by linarith⟩
      have hm := hmid (p 0) (hp 0 (by norm_num)) (p (2 * t)) (hp _ hu)
      have hpm : (p 0 + p (2 * t)) / 2 = p t := by dsimp [p]; ring
      rw [hpm] at hm
      have hmu := hmin hu
      change q t ≤ q (2 * t) at hmu
      dsimp only [q] at hmu hneg ⊢
      have he : (1 - 2 * t) * g x + (2 * t) * g y =
          2 * ((1 - t) * g x + t * g y) - g x := by ring
      rw [he] at hmu
      have hp0 : p 0 = x := by simp [p]
      rw [hp0] at hm
      linarith
    · have hu : 2 * t - 1 ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith [ht.2]⟩
      have hm := hmid (p (2 * t - 1)) (hp _ hu) (p 1) (hp 1 (by norm_num))
      have hpm : (p (2 * t - 1) + p 1) / 2 = p t := by dsimp [p]; ring
      rw [hpm] at hm
      have hmu := hmin hu
      change q t ≤ q (2 * t - 1) at hmu
      dsimp only [q] at hmu hneg ⊢
      have he : (1 - (2 * t - 1)) * g x + (2 * t - 1) * g y =
          2 * ((1 - t) * g x + t * g y) - g y := by ring
      rw [he] at hmu
      have hp1 : p 1 = y := by simp [p]
      rw [hp1] at hm
      linarith
  have hb1 : b ≤ 1 := by linarith
  have hqb := hmin (show b ∈ Icc (0 : ℝ) 1 from ⟨hb, hb1⟩)
  have hq : 0 ≤ q b := hnonneg.trans hqb
  have haeq : a = 1 - b := by linarith
  simpa only [q, p, haeq, smul_eq_mul, sub_nonneg] using hq

/-- Positive continuous marginals of bounded, compactly supported joint log-concave
functions have concave logarithms. Continuity and positivity here are explicit helper
hypotheses. Applications must establish them for their fiber integral.
-/
theorem marginal_concaveOn_log_of_continuous (hPL : External.PrekopaLeindler)
    (d : ℕ) (hd : 0 < d) (F : ℝ × EuclideanSpace ℝ (Fin d) → ℝ)
    (hF : Measurable F) (hpos : ∀ p, 0 ≤ F p)
    (hbounded : Bornology.IsBounded (Set.range F))
    (hsupport : Bornology.IsBounded (Function.support F))
    (hlog : ConcaveOn ℝ (Function.support F) (fun p => Real.log (F p)))
    (s : Set ℝ) (hs : Convex ℝ s)
    (hpositive : ∀ x ∈ s, 0 < ∫ z, F (x, z))
    (hcontinuous : ContinuousOn (fun x => ∫ z, F (x, z)) s) :
    ConcaveOn ℝ s (fun x => Real.log (∫ z, F (x, z))) := by
  apply concaveOn_of_continuousOn_midpoint hs
    (hcontinuous.log (fun x hx => (hpositive x hx).ne'))
  intro x hx y hy
  obtain ⟨_, _, _, hm⟩ := marginal_midpoint_sqrt_le hPL d hd F hF hpos hbounded hsupport hlog x y
  have hmpos := hpositive ((x + y) / 2) (by
    have h := hs hx hy (a := (1 / 2 : ℝ)) (b := (1 / 2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num)
    convert h using 1
    simp only [smul_eq_mul]
    ring)
  have hxpos := hpositive x hx
  have hypos := hpositive y hy
  have h := (Real.log_le_log_iff (Real.sqrt_pos.mpr (mul_pos hxpos hypos)) hmpos).mpr hm
  rw [Real.log_sqrt (mul_pos hxpos hypos).le, Real.log_mul hxpos.ne' hypos.ne'] at h
  exact h

end Riesz1

end
end
