/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.LintegralPowerTail

/-!
# The pair term of the small-region estimate

The arcs part of Lemma 5.8, small region `u + v < 1` of the cell estimate. For two
real lifts `ℓ₁ < ℓ₂` of microscopic particles, the indicator product

`1[ℓ₁ < t < ℓ₂] 1[t - ℓ₁ < u] 1[ℓ₂ - t < v] 1[u + v < 1] (u + v)^{-s-3}`

is the integrand of the pair `(ℓ₁, ℓ₂)` in `n₋(t,u) n₊(t,v) (u+v)^{-s-3}`, where
`n₋(t,u)` counts the particles in `(t - u, t)` and `n₊(t,v)` those in `(t, t + v)`.
`lintegral_pairIntegrand_le` bounds its integral over `t` in a unit cell and over `(u, v)` by
`c (ℓ₂ - ℓ₁)^{-s}` when `ℓ₁` lies in the window `(m - 1, m + 1)` and `0 < ℓ₂ - ℓ₁ < 1`, and by `0`
otherwise. The constant is `1 / ((s+1)(s+2))`, independent of the cell.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Riesz1

/-- The integrand of one lift pair in the small-region estimate: `(u+v)^{-s-3}` on the event
that `ℓ₁ < t < ℓ₂`, `t - ℓ₁ < u`, `ℓ₂ - t < v` and `u + v < 1`, and `0` otherwise. -/
def pairIntegrand (s ℓ₁ ℓ₂ t u v : ℝ) : ℝ≥0∞ :=
  if ℓ₁ < t ∧ t < ℓ₂ ∧ t - ℓ₁ < u ∧ ℓ₂ - t < v ∧ u + v < 1 then
    ENNReal.ofReal ((u + v) ^ (-s - 3)) else 0

/-- **Pair term.** The `t`-integral over the unit cell `(m, m+1]` of the `(u,v)`-integral of
`pairIntegrand` is at most `(ℓ₂ - ℓ₁)^{-s} / ((s+1)(s+2))` when `ℓ₁ ∈ (m-1, m+1)` and
`0 < ℓ₂ - ℓ₁ < 1`, and vanishes otherwise. -/
theorem lintegral_pairIntegrand_le {s : ℝ} (hs0 : 0 < s) (m ℓ₁ ℓ₂ : ℝ) :
    ∫⁻ t in Ioc m (m + 1), ∫⁻ u, ∫⁻ v, pairIntegrand s ℓ₁ ℓ₂ t u v
      ≤ if (m - 1 < ℓ₁ ∧ ℓ₁ < m + 1) ∧ (0 < ℓ₂ - ℓ₁ ∧ ℓ₂ - ℓ₁ < 1) then
          ENNReal.ofReal ((ℓ₂ - ℓ₁) ^ (-s) / ((s + 1) * (s + 2)))
        else 0 := by
  classical
  set G : ℝ → ℝ≥0∞ := fun t => ∫⁻ u, ∫⁻ v, pairIntegrand s ℓ₁ ℓ₂ t u v with hG
  -- `G` vanishes off the open interval `(ℓ₁, ℓ₂)`.
  have hG_out : ∀ t, t ∉ Ioo ℓ₁ ℓ₂ → G t = 0 := by
    intro t ht
    have hz : ∀ u v, pairIntegrand s ℓ₁ ℓ₂ t u v = 0 := by
      intro u v
      unfold pairIntegrand
      rw [ite_eq_right]
      intro h
      exact ht ⟨h.1, h.2.1⟩
    simp [hG, hz]
  by_cases hcond : (m - 1 < ℓ₁ ∧ ℓ₁ < m + 1) ∧ (0 < ℓ₂ - ℓ₁ ∧ ℓ₂ - ℓ₁ < 1)
  · rw [ite_eq_left hcond]
    obtain ⟨⟨hm1, hm2⟩, hd0, hd1⟩ := hcond
    -- For `t ∈ (ℓ₁, ℓ₂)`, the `(u,v)`-integral is at most the quadrant integral.
    have hG_in : ∀ t ∈ Ioo ℓ₁ ℓ₂, G t ≤ ENNReal.ofReal ((ℓ₂ - ℓ₁) ^ (-s - 1)
        / ((s + 1) * (s + 2))) := by
      intro t ht
      obtain ⟨ht1, ht2⟩ := ht
      have ha : 0 < t - ℓ₁ := by linarith
      have hb : 0 < ℓ₂ - t := by linarith
      -- pointwise in `v`, for each `u`
      have hpt2 : ∀ u v, pairIntegrand s ℓ₁ ℓ₂ t u v
          ≤ (Ioi (ℓ₂ - t)).indicator (fun v => ENNReal.ofReal ((u + v) ^ (-s - 3))) v := by
        intro u v
        unfold pairIntegrand
        by_cases hv : ℓ₂ - t < v
        · rw [Set.indicator_of_mem (mem_Ioi.mpr hv)]
          split_ifs
          · exact le_rfl
          · exact zero_le
        · rw [Set.indicator_of_notMem (show v ∉ Ioi (ℓ₂ - t) from fun h => hv h)]
          split_ifs with h
          · exact absurd h.2.2.2.1 hv
          · exact le_rfl
      have hu_part : ∀ u, ∫⁻ v, pairIntegrand s ℓ₁ ℓ₂ t u v
          ≤ (Ioi (t - ℓ₁)).indicator (fun u => ∫⁻ v in Ioi (ℓ₂ - t),
              ENNReal.ofReal ((u + v) ^ (-s - 3))) u := by
        intro u
        by_cases hu : t - ℓ₁ < u
        · rw [Set.indicator_of_mem (mem_Ioi.mpr hu)]
          calc ∫⁻ v, pairIntegrand s ℓ₁ ℓ₂ t u v
              ≤ ∫⁻ v, (Ioi (ℓ₂ - t)).indicator
                  (fun v => ENNReal.ofReal ((u + v) ^ (-s - 3))) v :=
                lintegral_mono fun v => hpt2 u v
            _ = ∫⁻ v in Ioi (ℓ₂ - t), ENNReal.ofReal ((u + v) ^ (-s - 3)) :=
                lintegral_indicator measurableSet_Ioi _
        · rw [Set.indicator_of_notMem (show u ∉ Ioi (t - ℓ₁) from fun h => hu h)]
          have hz : ∀ v, pairIntegrand s ℓ₁ ℓ₂ t u v = 0 := fun v => by
            unfold pairIntegrand
            rw [ite_eq_right (fun h => hu h.2.2.1)]
          simp [hz]
      calc G t = ∫⁻ u, ∫⁻ v, pairIntegrand s ℓ₁ ℓ₂ t u v := rfl
        _ ≤ ∫⁻ u, (Ioi (t - ℓ₁)).indicator (fun u => ∫⁻ v in Ioi (ℓ₂ - t),
              ENNReal.ofReal ((u + v) ^ (-s - 3))) u := lintegral_mono hu_part
        _ = ∫⁻ u in Ioi (t - ℓ₁), ∫⁻ v in Ioi (ℓ₂ - t), ENNReal.ofReal ((u + v) ^ (-s - 3)) :=
                lintegral_indicator measurableSet_Ioi _
        _ = ENNReal.ofReal ((ℓ₂ - ℓ₁) ^ (-s - 1) / ((s + 1) * (s + 2))) := by
            rw [lintegral_quadrant_rpow hs0 ha hb]
            congr 2
            ring_nf
    -- Integrate over the cell, which lies in the interval `(ℓ₁ - ...)`. Drop the cell restriction.
    have hint : ∫⁻ t in Ioc m (m + 1), G t ≤ ∫⁻ t in Ioo ℓ₁ ℓ₂, G t := by
      calc ∫⁻ t in Ioc m (m + 1), G t ≤ ∫⁻ t, G t := setLIntegral_le_lintegral _ _
        _ = ∫⁻ t, (Ioo ℓ₁ ℓ₂).indicator G t := by
            congr 1
            ext t
            by_cases ht : t ∈ Ioo ℓ₁ ℓ₂
            · rw [Set.indicator_of_mem ht]
            · rw [Set.indicator_of_notMem ht, hG_out t ht]
        _ = ∫⁻ t in Ioo ℓ₁ ℓ₂, G t := lintegral_indicator measurableSet_Ioo _
    refine hint.trans ?_
    calc ∫⁻ t in Ioo ℓ₁ ℓ₂, G t
        ≤ ∫⁻ t in Ioo ℓ₁ ℓ₂, ENNReal.ofReal ((ℓ₂ - ℓ₁) ^ (-s - 1) / ((s + 1) * (s + 2))) :=
          setLIntegral_mono measurable_const fun t ht => hG_in t ht
      _ = ENNReal.ofReal ((ℓ₂ - ℓ₁) ^ (-s - 1) / ((s + 1) * (s + 2))) * ENNReal.ofReal (ℓ₂ - ℓ₁) := by
          rw [setLIntegral_const, Real.volume_Ioo]
      _ = ENNReal.ofReal ((ℓ₂ - ℓ₁) ^ (-s) / ((s + 1) * (s + 2))) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          have e : (ℓ₂ - ℓ₁) ^ (-s - 1) * (ℓ₂ - ℓ₁) = (ℓ₂ - ℓ₁) ^ (-s) := by
            rw [← Real.rpow_add_one hd0.ne']
            congr 1
            ring
          rw [← e]
          ring
  · rw [ite_eq_right hcond]
    -- Off the window or the range `0 < ℓ₂ - ℓ₁ < 1`, the integrand vanishes on the cell.
    have hzero : ∀ t ∈ Ioc m (m + 1), ∀ u v, pairIntegrand s ℓ₁ ℓ₂ t u v = 0 := by
      intro t ht u v
      unfold pairIntegrand
      rw [ite_eq_right]
      rintro ⟨h1, h2, h3, h4, h5⟩
      apply hcond
      have hv : 0 < v := by linarith
      refine ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩, by linarith, by linarith⟩
    have hGz : ∀ t ∈ Ioc m (m + 1), G t = 0 := fun t ht => by
      simp [hG, hzero t ht]
    have hzero_int : ∫⁻ t in Ioc m (m + 1), G t = 0 := by
      rw [setLIntegral_congr_fun measurableSet_Ioc (g := fun _ => (0 : ℝ≥0∞))
        (fun t ht => hGz t ht)]
      simp
    exact hzero_int.le

end Riesz1

end
end
