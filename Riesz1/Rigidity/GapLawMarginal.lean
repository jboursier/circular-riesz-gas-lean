/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Rigidity.GapLawMarginalLaw

/-!
# Positive continuous log-concave one-gap marginals

The fiber formula, its continuity and positivity, and the midpoint marginal
inequality are assembled here. Two particles are handled directly, without
invoking a positive-dimensional external inequality on an empty fiber.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Riesz1

lemma gapOffsetMarginalDensity_zero_dim (P : Parameters) {r : ℝ}
    (hr : r ∈ Ioo (0 : ℝ) 1) :
    gapOffsetMarginalDensity P 0 r = anchoredProbabilityDensity P 1 (fun _ => r) := by
  unfold gapOffsetMarginalDensity
  rw [Measure.volume_pi_eq_dirac (0 : Fin 0 → ℝ), integral_dirac]
  have he : (Fin.cons r (0 : Fin 0 → ℝ) : Fin 1 → ℝ) = fun _ => r := by
    ext i
    have hi : i = 0 := Fin.ext (by have := i.isLt; omega)
    rw [hi]
    rfl
  change (anchoredDomain 1).indicator (anchoredProbabilityDensity P 1) (Fin.cons r 0) = _
  rw [he, Set.indicator_of_mem ((mem_anchoredDomain_one r).mpr hr)]

lemma gapMarginalProbabilityDensity_zero_dim (P : Parameters) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 2) :
    gapMarginalProbabilityDensity P 0 t = twoGapProbabilityDensity P t := by
  have hr : t / 2 ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  unfold gapMarginalProbabilityDensity twoGapProbabilityDensity
  norm_num only [Nat.cast_zero, zero_add]
  rw [gapOffsetMarginalDensity_zero_dim P hr]

theorem gapMarginalProbabilityDensity_pos (P : Parameters) (n : ℕ) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) (n + 2 : ℝ)) : 0 < gapMarginalProbabilityDensity P n t := by
  have hN : (0 : ℝ) < n + 2 := by positivity
  have hr : t / (n + 2 : ℝ) ∈ Ioo (0 : ℝ) 1 :=
    ⟨div_pos ht.1 hN, (div_lt_one hN).mpr ht.2⟩
  exact div_pos (gapOffsetMarginalDensity_pos P n hr) hN

theorem continuousOn_gapMarginalProbabilityDensity (P : Parameters) (n : ℕ) :
    ContinuousOn (gapMarginalProbabilityDensity P n) (Ioo (0 : ℝ) (n + 2 : ℝ)) := by
  have hN : (0 : ℝ) < n + 2 := by positivity
  have hc : ContinuousOn (fun t => gapOffsetMarginalDensity P n (t / (n + 2 : ℝ)))
      (Ioo (0 : ℝ) (n + 2 : ℝ)) :=
    (continuousOn_gapOffsetMarginalDensity P n).comp (by fun_prop)
      (fun t ht => ⟨div_pos ht.1 hN, (div_lt_one hN).mpr ht.2⟩)
  exact hc.div_const _

theorem concaveOn_log_gapMarginalProbabilityDensity (hPL : External.PrekopaLeindler)
    (P : Parameters) (n : ℕ) :
    ConcaveOn ℝ (Ioo (0 : ℝ) (n + 2 : ℝ))
      (fun t => Real.log (gapMarginalProbabilityDensity P n t)) := by
  cases n with
  | zero =>
    norm_num only [Nat.cast_zero, zero_add]
    apply (concaveOn_log_twoGapProbabilityDensity P).congr
    intro t ht
    exact congrArg Real.log (gapMarginalProbabilityDensity_zero_dim P ht).symm
  | succ n =>
    have hN : (0 : ℝ) < (n + 1 : ℕ) + 2 := by positivity
    have hm (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) ((n + 1 : ℕ) + 2 : ℝ)) :
        t / ((n + 1 : ℕ) + 2 : ℝ) ∈ Ioo (0 : ℝ) 1 :=
      ⟨div_pos ht.1 hN, (div_lt_one hN).mpr ht.2⟩
    have hlog (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) ((n + 1 : ℕ) + 2 : ℝ)) :
        Real.log (gapMarginalProbabilityDensity P (n + 1) t) =
          Real.log (gapOffsetMarginalDensity P (n + 1) (t / ((n + 1 : ℕ) + 2 : ℝ))) -
            Real.log ((n + 1 : ℕ) + 2 : ℝ) := by
      exact Real.log_div (gapOffsetMarginalDensity_pos P (n + 1) (hm t ht)).ne' hN.ne'
    refine ⟨convex_Ioo _ _, ?_⟩
    intro x hx y hy a b ha hb hab
    have hcomb := (convex_Ioo (0 : ℝ) ((n + 1 : ℕ) + 2 : ℝ)) hx hy ha hb hab
    change a * Real.log (gapMarginalProbabilityDensity P (n + 1) x) +
      b * Real.log (gapMarginalProbabilityDensity P (n + 1) y) ≤
        Real.log (gapMarginalProbabilityDensity P (n + 1) (a * x + b * y))
    simp only [smul_eq_mul] at hcomb
    rw [hlog _ hcomb, hlog x hx, hlog y hy]
    have h := (concaveOn_log_gapOffsetMarginalDensity hPL P (n + 1) (by omega)).2
      (hm x hx) (hm y hy) ha hb hab
    have he : a • (x / ((n + 1 : ℕ) + 2 : ℝ)) + b • (y / ((n + 1 : ℕ) + 2 : ℝ)) =
        (a * x + b * y) / ((n + 1 : ℕ) + 2 : ℝ) := by simp only [smul_eq_mul]; ring
    rw [he] at h
    simp only [smul_eq_mul] at h ⊢
    have hc : a * Real.log ((n + 1 : ℕ) + 2 : ℝ) + b * Real.log ((n + 1 : ℕ) + 2 : ℝ) =
        Real.log ((n + 1 : ℕ) + 2 : ℝ) := by rw [← add_mul, hab, one_mul]
    nlinarith only [h, hc]

/-- Uniqueness of the continuous nonnegative density on its open support. -/
theorem gapMarginalProbabilityDensity_unique (P : Parameters) (n : ℕ) (j : ℤ) (f : ℝ → ℝ)
    (hf : ContinuousOn f (Ioo (0 : ℝ) (n + 2 : ℝ)))
    (hfn : ∀ t ∈ Ioo (0 : ℝ) (n + 2 : ℝ), 0 ≤ f t)
    (hlaw : (gibbsMeasure P (n + 1).succPNat).map (fun X => gap X j) =
      (volume.restrict (Ioo (0 : ℝ) (n + 2 : ℝ))).withDensity (fun t => ENNReal.ofReal (f t))) :
    EqOn f (gapMarginalProbabilityDensity P n) (Ioo (0 : ℝ) (n + 2 : ℝ)) := by
  exact continuous_interval_density_unique hf (continuousOn_gapMarginalProbabilityDensity P n)
    hfn (fun t ht => (gapMarginalProbabilityDensity_pos P n ht).le)
    (hlaw.symm.trans (map_gap_gibbsMeasure_marginal_density P n j))

/-- Item 5 of the gap-law lemma, for every `N ≥ 2` and every integer gap label.
The only external hypothesis is used to prove marginal log-concavity.
-/
theorem exists_gap_density (hPL : External.PrekopaLeindler) (P : Parameters)
    (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (j : ℤ) :
    ∃ f : ℝ → ℝ,
      (gibbsMeasure P N).map (fun X => gap X j) =
        (volume.restrict (Ioo (0 : ℝ) ((N : ℕ) : ℝ))).withDensity
          (fun t => ENNReal.ofReal (f t)) ∧
      ContinuousOn f (Ioo (0 : ℝ) ((N : ℕ) : ℝ)) ∧
      (∀ t ∈ Ioo (0 : ℝ) ((N : ℕ) : ℝ), 0 < f t) ∧
      ConcaveOn ℝ (Ioo (0 : ℝ) ((N : ℕ) : ℝ)) (fun t => Real.log (f t)) ∧
      ∀ g : ℝ → ℝ, ContinuousOn g (Ioo (0 : ℝ) ((N : ℕ) : ℝ)) →
        (∀ t ∈ Ioo (0 : ℝ) ((N : ℕ) : ℝ), 0 ≤ g t) →
        (gibbsMeasure P N).map (fun X => gap X j) =
          (volume.restrict (Ioo (0 : ℝ) ((N : ℕ) : ℝ))).withDensity
            (fun t => ENNReal.ofReal (g t)) →
        EqOn g f (Ioo (0 : ℝ) ((N : ℕ) : ℝ)) := by
  let n : ℕ := (N : ℕ) - 2
  have hNeq : N = (n + 1).succPNat := by
    apply PNat.coe_injective
    change (N : ℕ) = n + 1 + 1
    dsimp only [n]
    omega
  have hcast : (((n + 1).succPNat : ℕ) : ℝ) = (n + 2 : ℝ) := by
    simp only [Nat.succPNat_coe, Nat.cast_succ]
    ring
  rw [hNeq, hcast]
  exact ⟨gapMarginalProbabilityDensity P n, map_gap_gibbsMeasure_marginal_density P n j,
    continuousOn_gapMarginalProbabilityDensity P n,
    fun t ht => gapMarginalProbabilityDensity_pos P n ht,
    concaveOn_log_gapMarginalProbabilityDensity hPL P n,
    fun g hg hgn hglaw => gapMarginalProbabilityDensity_unique P n j g hg hgn hglaw⟩

end Riesz1

end
end
