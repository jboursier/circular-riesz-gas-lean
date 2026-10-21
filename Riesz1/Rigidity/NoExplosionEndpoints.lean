/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Rigidity.NoExplosionKernel
public import Riesz1.Rigidity.GapLawMarginal
public import Riesz1.ToMathlib.LogConcave.GapIBP

/-!
# Endpoint lower bounds in the actual cumulative gap chart

The first interaction supplies both endpoint singularities. The remaining
interactions have a common lower bound. These are the energy estimates
used in Lemma 4.5.
-/

public section

noncomputable section

open MeasureTheory Set Filter Topology

namespace Riesz1

lemma hurwitzKernel_abs (s x : ℝ) : hurwitzKernel s |x| = hurwitzKernel s x := by
  rcases le_or_gt 0 x with hx | hx
  · rw [abs_of_nonneg hx]
  · rw [abs_of_neg hx]
    exact congrArg (fun t : ℝ => 2 * t) (hurwitzZetaEven_re_even (s : ℂ) x)

/-- A uniform lower bound retaining both singularities of the first offset. -/
theorem exists_anchoredEnergy_endpoint_lower_bound (s : RieszExponent) (n : ℕ) :
    ∃ B : ℝ, ∀ y ∈ anchoredDomain (n + 1),
      2 * (n + 2 : ℝ) ^ (-s.val) *
        ((y 0) ^ (-s.val) + (1 - y 0) ^ (-s.val)) + B ≤
        anchoredEnergy s (n + 1) y := by
  obtain ⟨C, hC, hrem⟩ := exists_hurwitzKernel_endpoint_remainder_bound s.val s.2.1 s.2.2
  let m := n + 2
  let A : ℝ := (m : ℝ) ^ (-s.val)
  refine ⟨-A * ((m : ℝ) * (m - 1 : ℝ) * C), ?_⟩
  intro y hy
  let g : Fin m → Fin m → ℝ := fun i j =>
    hurwitzKernel s.val (anchorVector y i - anchorVector y j)
  have hg (i j : Fin m) (hij : i ≠ j) : 0 ≤ g i j + C := by
    have hi := anchorVector_mem_Ico hy i
    have hj := anchorVector_mem_Ico hy j
    have hne : anchorVector y i - anchorVector y j ≠ 0 :=
      sub_ne_zero.mpr ((strictMono_anchorVector hy).injective.ne hij)
    have ha : |anchorVector y i - anchorVector y j| ∈ Ioo (0 : ℝ) 1 :=
      ⟨abs_pos.mpr hne, abs_lt.mpr ⟨by linarith [hi.1, hj.2], by linarith [hj.1, hi.2]⟩⟩
    have hb := (abs_le.mp (hrem _ ha)).1
    rw [hurwitzKernel_abs] at hb
    dsimp only [g]
    linarith [Real.rpow_nonneg ha.1.le (-s.val),
      Real.rpow_nonneg (show 0 ≤ 1 - |anchorVector y i - anchorVector y j| by linarith [ha.2]) (-s.val)]
  have h01 : g 0 1 = hurwitzKernel s.val (y 0) := by
    simpa [g, m, anchorVector, hurwitzKernel] using
      congrArg (fun t : ℝ => 2 * t) (hurwitzZetaEven_re_even (s : ℂ) (y 0))
  have h10 : g 1 0 = hurwitzKernel s.val (y 0) := by
    simp [g, m, anchorVector]
  have h01mem : (1 : Fin m) ∈ Finset.univ.erase (0 : Fin m) := by
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    exact Fin.ne_of_val_ne (by simp [m])
  have h10mem : (0 : Fin m) ∈ Finset.univ.erase (1 : Fin m) := by
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    exact (Fin.ne_of_val_ne (by simp [m]) : (1 : Fin m) ≠ 0).symm
  have hone : (0 : Fin m) ≠ 1 := (Fin.ne_of_val_ne (by simp [m]) : (1 : Fin m) ≠ 0).symm
  have hinner (i : Fin m) : 0 ≤ ∑ j ∈ Finset.univ.erase i, (g i j + C) :=
    Finset.sum_nonneg fun j hj => hg i j (Finset.ne_of_mem_erase hj).symm
  have hpair : (g 0 1 + C) + (g 1 0 + C) ≤
      ∑ i : Fin m, ∑ j ∈ Finset.univ.erase i, (g i j + C) := by
    have h0 := Finset.single_le_sum (fun j hj => hg 0 j (Finset.ne_of_mem_erase hj).symm) h01mem
    have h1 := Finset.single_le_sum (fun j hj => hg 1 j (Finset.ne_of_mem_erase hj).symm) h10mem
    have hout := Finset.sum_le_univ_sum_of_nonneg
      (s := ({0, 1} : Finset (Fin m))) (fun i => hinner i)
    rw [Finset.sum_pair hone] at hout
    exact (add_le_add h0 h1).trans hout
  have hsum : (∑ i : Fin m, ∑ j ∈ Finset.univ.erase i, (g i j + C)) =
      (∑ i : Fin m, ∑ j ∈ Finset.univ.erase i, g i j) + (m : ℝ) * (m - 1 : ℝ) * C := by
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [Nat.cast_sub (show 1 ≤ m by dsimp [m]; omega), Nat.cast_one]
    ring
  rw [hsum, h01, h10] at hpair
  have hb := (abs_le.mp (hrem (y 0) (hy.1 0))).1
  have hA : 0 ≤ A := Real.rpow_nonneg (by positivity) _
  have hlow : 2 * ((y 0) ^ (-s.val) + (1 - y 0) ^ (-s.val)) -
      (m : ℝ) * (m - 1 : ℝ) * C ≤ ∑ i : Fin m, ∑ j ∈ Finset.univ.erase i, g i j := by
    linarith
  have hfinal := mul_le_mul_of_nonneg_left hlow hA
  have hfinal' : A * (2 * ((y 0) ^ (-s.val) + (1 - y 0) ^ (-s.val)) -
      (m : ℝ) * (m - 1 : ℝ) * C) ≤ anchoredEnergy s (n + 1) y := by
    unfold anchoredEnergy
    have hcoe : (((n + 1).succPNat : ℕ) : ℝ) = (m : ℝ) := by simp [m]; ring
    rw [hcoe]
    exact hfinal
  have hc : (n + 2 : ℝ) ^ (-s.val) = A := by simp [A, m]
  rw [hc]
  nlinarith only [hfinal']

lemma exists_anchoredProbabilityDensity_endpoint_bound (P : Parameters) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ y ∈ anchoredDomain (n + 1),
      anchoredProbabilityDensity P (n + 1) y ≤ C * Real.exp
        (-2 * P.val.1 * (n + 2 : ℝ) ^ (-P.val.2) *
          ((y 0) ^ (-P.val.2) + (1 - y 0) ^ (-P.val.2))) := by
  obtain ⟨B, hB⟩ := exists_anchoredEnergy_endpoint_lower_bound (parametersExponent P) n
  let Z : ℝ := (partitionFunction P (n + 1).succPNat).toReal⁻¹
  have hZ : 0 < Z := inv_pos.mpr
    (ENNReal.toReal_pos (partitionFunction_pos P _).ne' (partitionFunction_lt_top P _).ne)
  refine ⟨Z * Real.exp (-P.val.1 * B), mul_pos hZ (Real.exp_pos _), ?_⟩
  intro y hy
  have hlow := hB y hy
  change 2 * (n + 2 : ℝ) ^ (-P.val.2) *
    (y 0 ^ (-P.val.2) + (1 - y 0) ^ (-P.val.2)) + B ≤
      anchoredEnergy (parametersExponent P) (n + 1) y at hlow
  have hb := mul_le_mul_of_nonpos_left hlow (neg_nonpos.mpr P.2.1.le)
  unfold anchoredProbabilityDensity
  change Z * Real.exp _ ≤ _
  rw [mul_assoc, ← Real.exp_add]
  apply mul_le_mul_of_nonneg_left _ hZ.le
  apply Real.exp_le_exp.mpr
  nlinarith only [hb]

/-- The true continuous marginal satisfies the endpoint estimate of
Lemma 4.5, with a constant depending on `N, β, s`. -/
theorem gapMarginalProbabilityDensity_endpoint_bound (P : Parameters) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t ∈ Ioo (0 : ℝ) (n + 2 : ℝ),
      gapMarginalProbabilityDensity P n t ≤ C * Real.exp
        (-2 * P.val.1 * (t ^ (-P.val.2) + (n + 2 - t) ^ (-P.val.2))) := by
  obtain ⟨C, hC, hbound⟩ := exists_anchoredProbabilityDensity_endpoint_bound P n
  have hN : (0 : ℝ) < n + 2 := by positivity
  have hoff (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) 1) :
      gapOffsetMarginalDensity P n r ≤ C * Real.exp
        (-2 * P.val.1 * (n + 2 : ℝ) ^ (-P.val.2) *
          (r ^ (-P.val.2) + (1 - r) ^ (-P.val.2))) := by
    let K : Set (Fin n → ℝ) := univ.pi fun _ => Icc (0 : ℝ) 1
    have hK : IsCompact K := isCompact_univ_pi fun _ => isCompact_Icc
    let M : ℝ := C * Real.exp (-2 * P.val.1 * (n + 2 : ℝ) ^ (-P.val.2) *
      (r ^ (-P.val.2) + (1 - r) ^ (-P.val.2)))
    have hp (z : Fin n → ℝ) : gapOffsetJointDensity P n (r, z) ≤ M := by
      by_cases hz : Fin.cons r z ∈ anchoredDomain (n + 1)
      · change extendedAnchoredProbabilityDensity P (n + 1) (Fin.cons r z) ≤ M
        rw [extendedAnchoredProbabilityDensity, Set.indicator_of_mem hz]
        simpa only [Fin.cons_zero] using hbound (Fin.cons r z) hz
      · change (anchoredDomain (n + 1)).indicator _ (Fin.cons r z) ≤ M
        rw [Set.indicator_of_notMem hz]
        exact (mul_pos hC (Real.exp_pos _)).le
    have heq : (∫ z in K, gapOffsetJointDensity P n (r, z)) = gapOffsetMarginalDensity P n r := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro z hz
      by_contra h
      exact hz (gapOffsetJointDensity_fiber_support_subset P n r h)
    have hvol : volume K = (1 : ENNReal) := by
      rw [show K = univ.pi (fun _ : Fin n => Icc (0 : ℝ) 1) from rfl, volume_pi_pi]
      simp
    have hi : IntegrableOn (fun _z : Fin n → ℝ => M) K :=
      integrableOn_const hK.measure_lt_top.ne
    have hm := setIntegral_mono_on (integrable_gapOffsetJointDensity_fiber P n r).integrableOn hi
      hK.measurableSet (fun z _ => hp z)
    rw [heq] at hm
    simpa only [integral_const, Measure.real, Measure.restrict_apply MeasurableSet.univ,
      univ_inter, hvol, ENNReal.toReal_one, smul_eq_mul, one_mul] using hm
  refine ⟨C / (n + 2 : ℝ), div_pos hC hN, ?_⟩
  intro t ht
  have hr : t / (n + 2 : ℝ) ∈ Ioo (0 : ℝ) 1 :=
    ⟨div_pos ht.1 hN, (div_lt_one hN).mpr ht.2⟩
  have hs : (n + 2 : ℝ) ^ (-P.val.2) *
      ((t / (n + 2)) ^ (-P.val.2) + (1 - t / (n + 2)) ^ (-P.val.2)) =
      t ^ (-P.val.2) + (n + 2 - t) ^ (-P.val.2) := by
    rw [show 1 - t / (n + 2 : ℝ) = (n + 2 - t) / (n + 2) by field_simp]
    rw [Real.div_rpow ht.1.le hN.le,
      Real.div_rpow (sub_pos.mpr ht.2).le hN.le]
    field_simp
  have hm := div_le_div_of_nonneg_right (hoff _ hr) hN.le
  change gapOffsetMarginalDensity P n (t / (n + 2 : ℝ)) / (n + 2) ≤ _
  have he : -2 * P.val.1 * (n + 2 : ℝ) ^ (-P.val.2) *
      ((t / (n + 2)) ^ (-P.val.2) + (1 - t / (n + 2)) ^ (-P.val.2)) =
      -2 * P.val.1 * (t ^ (-P.val.2) + (n + 2 - t) ^ (-P.val.2)) := by
    rw [mul_assoc, hs]
  simpa only [he, mul_div_right_comm] using hm

/-- Endpoint limits and fixed-size inverse integrability of the canonical gap density.
No marginal concavity hypothesis is needed for these consequences of the endpoint bound. -/
theorem gapMarginalProbabilityDensity_endpoints (P : Parameters) (n : ℕ) :
    Tendsto (gapMarginalProbabilityDensity P n) (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (gapMarginalProbabilityDensity P n) (𝓝[<] (n + 2 : ℝ)) (𝓝 0) ∧
      ∀ p : ℝ, 0 ≤ p → IntegrableOn
        (fun t => t ^ (-p) * gapMarginalProbabilityDensity P n t) (Ioo (0 : ℝ) (n + 2 : ℝ)) := by
  obtain ⟨C, hC, hb⟩ := gapMarginalProbabilityDensity_endpoint_bound P n
  have hN : (0 : ℝ) < n + 2 := by positivity
  have hpos := fun t ht => gapMarginalProbabilityDensity_pos P n (t := t) ht
  have hβ := P.property.1
  have hs : 0 < P.val.2 := P.property.2.1
  have hb' := gap_f_le_exp hβ hb hC.le
  refine ⟨gap_f_tendsto_zero_left hN hs hβ hpos hb',
    gap_f_tendsto_zero_right hN hs hβ hpos hC.le hb, ?_⟩
  intro p hp
  obtain ⟨M, hM, hbound⟩ := gap_rpow_mul_f_le hs hβ hp hC.le hb'
  have hpowc : ContinuousOn (fun t : ℝ => t ^ (-p)) (Ioo (0 : ℝ) (n + 2 : ℝ)) :=
    fun t ht => (Real.continuousAt_rpow_const t (-p) (Or.inl ht.1.ne')).continuousWithinAt
  have hc : ContinuousOn (fun t => t ^ (-p) * gapMarginalProbabilityDensity P n t)
      (Ioo (0 : ℝ) (n + 2 : ℝ)) :=
    hpowc.mul (continuousOn_gapMarginalProbabilityDensity P n)
  have hi : IntegrableOn (fun t : ℝ => M * t) (Ioo (0 : ℝ) (n + 2 : ℝ)) :=
    ((continuous_const.mul continuous_id).integrableOn_Icc).mono_set Ioo_subset_Icc_self
  refine hi.mono' (hc.aestronglyMeasurable measurableSet_Ioo) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg ht.1.le _) (hpos t ht).le)]
  exact hbound t ht

/-- All inverse gap moments are finite for every fixed `N ≥ 2` and integer label.
This is the fixed-`N` finiteness assertion of Lemma 4.5.
It does not assert a bound uniform in `N`. -/
theorem integrable_gap_inverse_rpow (P : Parameters) (n : ℕ) (j : ℤ) {p : ℝ} (hp : 0 ≤ p) :
    Integrable (fun X : Configuration (n + 1).succPNat => gap X j ^ (-p))
      (gibbsMeasure P (n + 1).succPNat) := by
  have hm : Measurable (gapMarginalProbabilityDensity P n) :=
    ((measurable_gapOffsetMarginalDensity P n).comp
      (measurable_id.div_const (n + 2 : ℝ))).div_const (n + 2 : ℝ)
  have hi := (gapMarginalProbabilityDensity_endpoints P n).2.2 p hp
  have hnn (t : ℝ) : 0 ≤ gapMarginalProbabilityDensity P n t :=
    div_nonneg (gapOffsetMarginalDensity_nonneg P n _) (by positivity)
  have hpow : Measurable (fun t : ℝ => t ^ (-p)) := measurable_id.pow_const _
  apply (integrable_map_measure hpow.aestronglyMeasurable (measurable_gap j).aemeasurable).mp
  rw [map_gap_gibbsMeasure_marginal_density P n j,
    integrable_withDensity_iff_integrable_smul' hm.ennreal_ofReal
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  change Integrable (fun t => t ^ (-p) * gapMarginalProbabilityDensity P n t)
    (volume.restrict (Ioo (0 : ℝ) (n + 2 : ℝ))) at hi
  exact hi.congr (ae_of_all _ fun t => by
    dsimp only
    rw [ENNReal.toReal_ofReal (hnn t), smul_eq_mul, mul_comm])

/-- The nonnegative inverse moment is finite, without conversion of an infinite integral to ℝ. -/
theorem gap_inverse_moment_lt_top (P : Parameters) (n : ℕ) (j : ℤ) {p : ℝ} (hp : 0 ≤ p) :
    (∫⁻ X : Configuration (n + 1).succPNat, ENNReal.ofReal (gap X j ^ (-p))
      ∂gibbsMeasure P (n + 1).succPNat) < ⊤ := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_gap_inverse_rpow P n j hp)
    (ae_of_all _ fun X => Real.rpow_nonneg (gap_pos X j).le _)]
  exact ENNReal.ofReal_lt_top

end Riesz1

end
