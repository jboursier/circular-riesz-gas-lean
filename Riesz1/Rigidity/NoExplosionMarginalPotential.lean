/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Rigidity.NoExplosionConvexity
public import Riesz1.Rigidity.NoExplosionDensity
public import Riesz1.ToMathlib.LogConcave.MarginalAllDimensions

/-!
# Convexity of the single-gap potential

The singularity-removed joint density is bounded on its bounded support.
Applying the Prékopa–Leindler inequality `External.PrekopaLeindler`, which is
supplied as a hypothesis, proves convexity of the potential in Lemma 4.5.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Riesz1

/-- The actual joint density after removing the first pair singularity. -/
def gapResidualEuclideanDensity (P : Parameters) (n : ℕ)
    (p : ℝ × EuclideanSpace ℝ (Fin n)) : ℝ :=
  Real.exp (2 * P.val.1 * (n + 2 : ℝ) ^ (-P.val.2) * p.1 ^ (-P.val.2)) *
    gapOffsetEuclideanDensity P n p

lemma support_gapResidualEuclideanDensity (P : Parameters) (n : ℕ) :
    Function.support (gapResidualEuclideanDensity P n) =
      Function.support (gapOffsetEuclideanDensity P n) := by
  ext p
  simp only [gapResidualEuclideanDensity, Function.mem_support, ne_eq, mul_eq_zero,
    Real.exp_ne_zero, false_or]

lemma gapResidualEuclideanDensity_eq (P : Parameters) (n : ℕ)
    (p : ℝ × EuclideanSpace ℝ (Fin n))
    (hp : p ∈ Function.support (gapOffsetEuclideanDensity P n)) :
    gapResidualEuclideanDensity P n p =
      (partitionFunction P (n + 1).succPNat).toReal⁻¹ *
      Real.exp (-P.val.1 * (anchoredEnergy (parametersExponent P) (n + 1)
        (gapOffsetEuclideanChart n p) -
          2 * (n + 2 : ℝ) ^ (-P.val.2) * p.1 ^ (-P.val.2))) := by
  have hm : gapOffsetEuclideanChart n p ∈ anchoredDomain (n + 1) := by
    rwa [support_gapOffsetEuclideanDensity] at hp
  unfold gapResidualEuclideanDensity gapOffsetEuclideanDensity extendedAnchoredProbabilityDensity
  rw [Set.indicator_of_mem hm, anchoredProbabilityDensity]
  rw [mul_left_comm, mul_assoc, ← Real.exp_add]
  congr 2
  ring

lemma concaveOn_log_gapResidualEuclideanDensity (P : Parameters) (n : ℕ) :
    ConcaveOn ℝ (Function.support (gapResidualEuclideanDensity P n))
      (fun p => Real.log (gapResidualEuclideanDensity P n p)) := by
  let B : (ℝ × EuclideanSpace ℝ (Fin n)) → ℝ := fun p =>
    anchoredEnergy (parametersExponent P) (n + 1) (gapOffsetEuclideanChart n p) -
      2 * (n + 2 : ℝ) ^ (-P.val.2) * p.1 ^ (-P.val.2)
  have hc : ConvexOn ℝ (Function.support (gapResidualEuclideanDensity P n)) B := by
    rw [support_gapResidualEuclideanDensity, support_gapOffsetEuclideanDensity]
    exact (convexOn_anchoredEnergy_sub_first_singularity (parametersExponent P) n).comp_linearMap
      (gapOffsetEuclideanChart n)
  have hZ : 0 < (partitionFunction P (n + 1).succPNat).toReal⁻¹ := inv_pos.mpr
    (ENNReal.toReal_pos (partitionFunction_pos P _).ne' (partitionFunction_lt_top P _).ne)
  have he (p : ℝ × EuclideanSpace ℝ (Fin n))
      (hp : p ∈ Function.support (gapResidualEuclideanDensity P n)) :
      Real.log (gapResidualEuclideanDensity P n p) =
        Real.log ((partitionFunction P (n + 1).succPNat).toReal⁻¹) - P.val.1 * B p := by
    rw [gapResidualEuclideanDensity_eq P n p (by rwa [support_gapResidualEuclideanDensity] at hp),
      Real.log_mul hZ.ne' (Real.exp_ne_zero _), Real.log_exp]
    dsimp only [B]
    ring
  refine ⟨hc.1, ?_⟩
  intro p hp q hq a b ha hb hab
  have hpq := hc.1 hp hq ha hb hab
  dsimp only
  rw [he p hp, he q hq, he _ hpq]
  have h := hc.2 hp hq ha hb hab
  simp only [smul_eq_mul] at h ⊢
  have hm := mul_le_mul_of_nonneg_left h P.2.1.le
  have hconst := congrArg (fun t : ℝ =>
    t * Real.log ((partitionFunction P (n + 1).succPNat).toReal⁻¹)) hab
  nlinarith only [hm, hconst]

lemma exists_gapResidualEuclideanDensity_bound (P : Parameters) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ p, 0 ≤ gapResidualEuclideanDensity P n p ∧
      gapResidualEuclideanDensity P n p ≤ C := by
  obtain ⟨B, hB⟩ := exists_anchoredEnergy_endpoint_lower_bound (parametersExponent P) n
  let Z : ℝ := (partitionFunction P (n + 1).succPNat).toReal⁻¹
  have hZ : 0 < Z := inv_pos.mpr
    (ENNReal.toReal_pos (partitionFunction_pos P _).ne' (partitionFunction_lt_top P _).ne)
  refine ⟨Z * Real.exp (-P.val.1 * B), mul_pos hZ (Real.exp_pos _), ?_⟩
  intro p
  have hn : 0 ≤ gapResidualEuclideanDensity P n p :=
    mul_nonneg (Real.exp_pos _).le (gapOffsetEuclideanDensity_nonneg P n p)
  refine ⟨hn, ?_⟩
  by_cases hp : p ∈ Function.support (gapOffsetEuclideanDensity P n)
  · have hy : gapOffsetEuclideanChart n p ∈ anchoredDomain (n + 1) := by
      rwa [support_gapOffsetEuclideanDensity] at hp
    have hb := hB _ hy
    change 2 * (n + 2 : ℝ) ^ (-P.val.2) *
      (p.1 ^ (-P.val.2) + (1 - p.1) ^ (-P.val.2)) + B ≤ _ at hb
    have hp1 : p.1 < 1 := (hy.1 0).2
    have hnn := mul_nonneg
      (Real.rpow_nonneg (show (0 : ℝ) ≤ n + 2 by positivity) (-P.val.2))
      (Real.rpow_nonneg (show 0 ≤ 1 - p.1 by linarith) (-P.val.2))
    rw [gapResidualEuclideanDensity_eq P n p hp]
    apply mul_le_mul_of_nonneg_left _ hZ.le
    apply Real.exp_le_exp.mpr
    have hlow : B ≤ anchoredEnergy (parametersExponent P) (n + 1) (gapOffsetEuclideanChart n p) -
        2 * (n + 2 : ℝ) ^ (-P.val.2) * p.1 ^ (-P.val.2) := by nlinarith only [hb, hnn]
    exact mul_le_mul_of_nonpos_left hlow (neg_nonpos.mpr P.2.1.le)
  · have hz : gapOffsetEuclideanDensity P n p = 0 := by simpa only [Function.mem_support, not_not] using hp
    rw [gapResidualEuclideanDensity, hz, mul_zero]
    exact (mul_pos hZ (Real.exp_pos _)).le

lemma integral_gapResidualEuclideanDensity (P : Parameters) (n : ℕ) (r : ℝ) :
    (∫ z, gapResidualEuclideanDensity P n (r, z)) =
      Real.exp (2 * P.val.1 * (n + 2 : ℝ) ^ (-P.val.2) * r ^ (-P.val.2)) *
        gapOffsetMarginalDensity P n r := by
  change (∫ z, Real.exp (2 * P.val.1 * (n + 2 : ℝ) ^ (-P.val.2) * r ^ (-P.val.2)) *
    gapOffsetEuclideanDensity P n (r, z)) = _
  rw [integral_const_mul, integral_gapOffsetEuclideanDensity]

theorem concaveOn_log_gapResidualMarginal (hPL : External.PrekopaLeindler)
    (P : Parameters) (n : ℕ) :
    ConcaveOn ℝ (Ioo (0 : ℝ) 1) (fun r => Real.log
      (Real.exp (2 * P.val.1 * (n + 2 : ℝ) ^ (-P.val.2) * r ^ (-P.val.2)) *
        gapOffsetMarginalDensity P n r)) := by
  have hm : Measurable (gapResidualEuclideanDensity P n) :=
    ((measurable_const.mul (measurable_fst.pow_const _)).exp).mul
      (measurable_gapOffsetEuclideanDensity P n)
  obtain ⟨C, hC, hb⟩ := exists_gapResidualEuclideanDensity_bound P n
  have hbounded : Bornology.IsBounded (range (gapResidualEuclideanDensity P n)) := by
    apply (isCompact_Icc (a := (0 : ℝ)) (b := C)).isBounded.subset
    rintro _ ⟨p, rfl⟩
    exact hb p
  have hsupport : Bornology.IsBounded (Function.support (gapResidualEuclideanDensity P n)) := by
    rw [support_gapResidualEuclideanDensity]
    exact isBounded_support_gapOffsetEuclideanDensity P n
  have he := fun r => integral_gapResidualEuclideanDensity P n r
  have hpos : ∀ r ∈ Ioo (0 : ℝ) 1, 0 < ∫ z, gapResidualEuclideanDensity P n (r, z) := by
    intro r hr
    rw [he]
    exact mul_pos (Real.exp_pos _) (gapOffsetMarginalDensity_pos P n hr)
  have hpowc : ContinuousOn (fun r : ℝ => r ^ (-P.val.2)) (Ioo (0 : ℝ) 1) :=
    fun r hr => (Real.continuousAt_rpow_const r (-P.val.2) (Or.inl hr.1.ne')).continuousWithinAt
  have hcont : ContinuousOn (fun r => ∫ z, gapResidualEuclideanDensity P n (r, z)) (Ioo (0 : ℝ) 1) := by
    simp_rw [he]
    exact (Real.continuous_exp.comp_continuousOn (hpowc.const_mul _)).mul
      (continuousOn_gapOffsetMarginalDensity P n)
  have hc := marginal_concaveOn_log_all_dimensions hPL n _ hm (fun p => (hb p).1)
    hbounded hsupport (concaveOn_log_gapResidualEuclideanDensity P n) _ (convex_Ioo _ _) hpos hcont
  simpa only [integral_gapResidualEuclideanDensity] using hc

/-- Convexity of the potential on its entire open support. -/
theorem convexOn_gapPotential (hPL : External.PrekopaLeindler) (P : Parameters) (n : ℕ) :
    ConvexOn ℝ (Ioo (0 : ℝ) (n + 2 : ℝ)) (fun t =>
      -Real.log (gapMarginalProbabilityDensity P n t) - 2 * P.val.1 * t ^ (-P.val.2)) := by
  have hN : (0 : ℝ) < n + 2 := by positivity
  let J : ℝ → ℝ := fun r => Real.exp
    (2 * P.val.1 * (n + 2 : ℝ) ^ (-P.val.2) * r ^ (-P.val.2)) * gapOffsetMarginalDensity P n r
  have hm (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) (n + 2 : ℝ)) :
      t / (n + 2 : ℝ) ∈ Ioo (0 : ℝ) 1 :=
    ⟨div_pos ht.1 hN, (div_lt_one hN).mpr ht.2⟩
  have he (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) (n + 2 : ℝ)) :
      -Real.log (gapMarginalProbabilityDensity P n t) - 2 * P.val.1 * t ^ (-P.val.2) =
        Real.log (n + 2 : ℝ) - Real.log (J (t / (n + 2 : ℝ))) := by
    have hmp := gapOffsetMarginalDensity_pos P n (hm t ht)
    have hscale : (n + 2 : ℝ) ^ (-P.val.2) * (t / (n + 2 : ℝ)) ^ (-P.val.2) =
        t ^ (-P.val.2) := by
      rw [Real.div_rpow ht.1.le hN.le]
      exact mul_div_cancel₀ _ (Real.rpow_pos_of_pos hN _).ne'
    rw [gapMarginalProbabilityDensity, Real.log_div hmp.ne' hN.ne']
    dsimp only [J]
    rw [Real.log_mul (Real.exp_ne_zero _) hmp.ne', Real.log_exp]
    linear_combination 2 * P.val.1 * hscale
  refine ⟨convex_Ioo _ _, ?_⟩
  intro t ht u hu a b ha hb hab
  have hcomb := (convex_Ioo (0 : ℝ) (n + 2 : ℝ)) ht hu ha hb hab
  dsimp only
  rw [he _ hcomb, he t ht, he u hu]
  have h := (concaveOn_log_gapResidualMarginal hPL P n).2 (hm t ht) (hm u hu) ha hb hab
  have heq : a • (t / (n + 2 : ℝ)) + b • (u / (n + 2 : ℝ)) =
      (a • t + b • u) / (n + 2 : ℝ) := by simp only [smul_eq_mul]; ring
  rw [heq] at h
  change a • Real.log (J (t / (n + 2 : ℝ))) + b • Real.log (J (u / (n + 2 : ℝ))) ≤
    Real.log (J ((a • t + b • u) / (n + 2 : ℝ))) at h
  simp only [smul_eq_mul] at h ⊢
  have hconst := congrArg (fun r : ℝ => r * Real.log (n + 2 : ℝ)) hab
  nlinarith only [h, hconst]

/-- **Single-gap density and endpoints**, Lemma 4.5.
Here `N = n + 2`, so every allowed particle number is included, including two.
The Prékopa–Leindler inequality `External.PrekopaLeindler` is the only hypothesis.
It is used for marginal convexity. -/
theorem no_explosion_density (hPL : External.PrekopaLeindler) (P : Parameters) (n : ℕ) :
    ConvexOn ℝ (Ioo (0 : ℝ) (n + 2 : ℝ)) (fun t =>
      -Real.log (gapMarginalProbabilityDensity P n t) - 2 * P.val.1 * t ^ (-P.val.2)) ∧
    (∀ y : Ioo (0 : ℝ) (n + 2 : ℝ), gapMarginalProbabilityDensity P n y =
      Real.exp (-2 * P.val.1 * (y : ℝ) ^ (-P.val.2) - gapPotential P n y)) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ t ∈ Ioo (0 : ℝ) (n + 2 : ℝ),
      gapMarginalProbabilityDensity P n t ≤ C * Real.exp
        (-2 * P.val.1 * (t ^ (-P.val.2) + (n + 2 - t) ^ (-P.val.2)))) ∧
    (∀ a b : ℝ, 0 < a → a ≤ b → b < n + 2 →
      AbsolutelyContinuousOnInterval (gapMarginalProbabilityDensity P n) a b) ∧
    Filter.Tendsto (gapMarginalProbabilityDensity P n) (nhdsWithin 0 (Ioi 0)) (nhds 0) ∧
    Filter.Tendsto (gapMarginalProbabilityDensity P n)
      (nhdsWithin (n + 2 : ℝ) (Iio (n + 2 : ℝ))) (nhds 0) ∧
    ∀ (j : ℤ) (p : ℝ), 0 < p →
      (∫⁻ X : Configuration (n + 1).succPNat, ENNReal.ofReal (gap X j ^ (-p))
        ∂gibbsMeasure P (n + 1).succPNat) < ⊤ := by
  have hend := gapMarginalProbabilityDensity_endpoints P n
  exact ⟨convexOn_gapPotential hPL P n,
    gapMarginalProbabilityDensity_eq_exp_potential P n,
    gapMarginalProbabilityDensity_endpoint_bound P n,
    fun _ _ ha hab hb => gapMarginalProbabilityDensity_absolutelyContinuous hPL P n ha hab hb,
    hend.1, hend.2.1, fun j p hp => gap_inverse_moment_lt_top P n j hp.le⟩

end Riesz1

end
end
