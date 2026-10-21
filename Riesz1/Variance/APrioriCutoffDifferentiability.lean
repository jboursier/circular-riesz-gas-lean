/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.APrioriCutoffChain
public import Riesz1.Variance.APrioriCutoffSupport
public import Riesz1.Variance.APrioriGoodGradientBound
public import Riesz1.Variance.ConvexificationEnergyLaw

/-!
# Differentiating the cutoff along the anchored gap hyperplane

For the cutoff part of Lemma 5.2, the ambient kink hyperplanes
have null pullbacks under the anchored gap map. Their linear parts
are differences of distinct anchored coordinates, so none vanishes.
-/

@[expose] public section

noncomputable section

open Finset MeasureTheory

namespace Riesz1

/-- Two-particle check: the affine gap hyperplane is parametrized by
`(2y, 2(1-y))`. Its wrapping coordinate has nonzero slope. -/
theorem anchoredGapVector_two (y : Fin 1 → ℝ) :
    anchoredGapVector 1 y 0 = 2 * y 0 ∧
      anchoredGapVector 1 y 1 = 2 * (1 - y 0) := by
  have h0 : anchoredCyclicOffset 1 y 0 = 0 :=
    (anchoredCyclicOffset_natCast 1 y 0).trans (anchorVector_zero y)
  have h1 : anchoredCyclicOffset 1 y 1 = y 0 :=
    (anchoredCyclicOffset_natCast 1 y (Fin.succ 0)).trans (anchorVector_succ y 0)
  have h2 : anchoredCyclicOffset 1 y 2 = 1 := by
    have h := anchoredCyclicOffset_period 1 y 0
    norm_num only [Nat.succPNat_coe, Nat.cast_ofNat, zero_add, h0] at h
    exact h
  constructor
  · unfold anchoredGapVector
    norm_num [Nat.succPNat_coe, h0, h1]
  · unfold anchoredGapVector
    norm_num [Nat.succPNat_coe, h1, h2]

/-- The cyclic gap at any integer equals the gap at its residue label,
on the whole ambient anchored carrier. -/
theorem anchoredGapVector_labelOf (n : ℕ) (y : Fin n → ℝ) (j : ℤ) :
    anchoredGapVector n y (labelOf n.succPNat j) = anchoredGapAt n y j := by
  have hdecomp : j % (n.succPNat : ℕ) + (n.succPNat : ℕ) * (j / (n.succPNat : ℕ)) = j := by
    rw [Int.emod_def]
    ring
  have hperiod (r q : ℤ) : anchoredGapAt n y (r + (n.succPNat : ℕ) * q) =
      anchoredGapAt n y r := by
    unfold anchoredGapAt
    rw [show r + (n.succPNat : ℕ) * q + 1 = (r + 1) + (n.succPNat : ℕ) * q by ring,
      anchoredCyclicOffset_add_mul, anchoredCyclicOffset_add_mul]
    ring
  change anchoredGapAt n y (((labelOf n.succPNat j : ℕ) : ℤ)) = _
  rw [labelOf_val_int]
  conv_rhs => rw [← hdecomp]
  exact (hperiod _ _).symm

/-- Telescoping remains exact off the simplex, and includes winding
offsets. -/
theorem gapOrientedSum_anchoredGapVector (n : ℕ) (y : Fin n → ℝ) (a b : ℤ) :
    gapOrientedSum n.succPNat (anchoredGapVector n y) a b =
      ((n : ℝ) + 1) * (anchoredCyclicOffset n y b - anchoredCyclicOffset n y a) := by
  have ht {a b : ℤ} (h : a ≤ b) :
      ∑ r ∈ Ico a b, anchoredGapAt n y r =
        ((n : ℝ) + 1) * (anchoredCyclicOffset n y b - anchoredCyclicOffset n y a) := by
    obtain ⟨m, rfl⟩ : ∃ m : ℕ, b = a + m := ⟨(b - a).toNat, by omega⟩
    have heq (r : ℤ) : anchoredGapAt n y r =
        ((n : ℝ) + 1) * anchoredCyclicOffset n y (r + 1) -
          ((n : ℝ) + 1) * anchoredCyclicOffset n y r := by
      unfold anchoredGapAt
      ring
    simp_rw [heq]
    rw [sum_Ico_telescope_nat (fun r => ((n : ℝ) + 1) * anchoredCyclicOffset n y r) a m]
    ring
  unfold gapOrientedSum
  simp_rw [anchoredGapVector_labelOf]
  rcases le_total a b with h | h
  · rw [Finset.Ico_eq_empty_of_le h, Finset.sum_empty, sub_zero, ht h]
  · rw [Finset.Ico_eq_empty_of_le h, Finset.sum_empty, zero_sub, ht h]
    ring

/-- The anchored pair deviation is its endpoint linear functional plus
its exact winding offset. -/
theorem gapPairDev_anchoredGapVector (n : ℕ) (y : Fin n → ℝ)
    (p : Fin (n.succPNat : ℕ) × ℤ) :
    gapPairDev n.succPNat (anchoredGapVector n y) p =
      (((n : ℝ) + 1) • (anchorCoord n (labelOf n.succPNat (((p.1 : ℕ) : ℤ) + p.2)) -
        anchorCoord n p.1)) y +
        (((n : ℝ) + 1) * (((((p.1 : ℕ) : ℤ) + p.2) / (n.succPNat : ℕ) : ℤ) : ℝ) - p.2) := by
  unfold gapPairDev
  rw [gapOrientedSum_anchoredGapVector, anchoredCyclicOffset_natCast]
  simp only [smul_apply, sub_apply,
    smul_eq_mul, anchorCoord_apply]
  change ((n : ℝ) + 1) * ((anchorVector y (labelOf n.succPNat _) + _) - _) - _ = _
  ring

/-- Distinct labels give distinct anchored coordinate functionals,
including when one of the labels is the pinned coordinate. -/
theorem anchorCoord_sub_ne_zero {n : ℕ} {i j : Fin (n.succPNat : ℕ)} (hij : i ≠ j) :
    anchorCoord n j - anchorCoord n i ≠ 0 := by
  intro h
  have heq : anchorCoord n j = anchorCoord n i := sub_eq_zero.mp h
  induction i using Fin.cases with
  | zero =>
    induction j using Fin.cases with
    | zero => exact hij rfl
    | succ j =>
      have hv := congrArg (fun L : (Fin n → ℝ) →L[ℝ] ℝ => L (Pi.single j 1)) heq
      simp [anchorCoord] at hv
  | succ i =>
    induction j using Fin.cases with
    | zero =>
      have hv := congrArg (fun L : (Fin n → ℝ) →L[ℝ] ℝ => L (Pi.single i 1)) heq
      simp [anchorCoord] at hv
    | succ j =>
      have hji : j ≠ i := fun h => hij (congrArg Fin.succ h.symm)
      have hv := congrArg (fun L : (Fin n → ℝ) →L[ℝ] ℝ => L (Pi.single j 1)) heq
      simp [anchorCoord, Pi.single_eq_of_ne hji.symm] at hv

/-- A short nonempty cutoff pair has distinct endpoint labels. -/
theorem cutoffPair_endpoint_ne {N : ℕ+} {I : Finset (Fin (N : ℕ))}
    {p : Fin (N : ℕ) × ℤ} (hp : p ∈ cutoffPairs N I) :
    p.1 ≠ labelOf N (((p.1 : ℕ) : ℤ) + p.2) := by
  intro heq
  have hd := dvd_of_labelOf_eq N ((labelOf_natCast N p.1).trans heq)
  rw [add_sub_cancel_left] at hd
  have hz := Int.eq_zero_of_abs_lt_dvd hd (abs_pair_snd_lt_of_mem hp)
  exact (Finset.mem_erase.1 (Finset.mem_product.1 (Finset.mem_filter.1 hp).1).2).1 hz

/-- Every affine level of a pair deviation has null pullback to anchored
coordinates. Ambient nullity alone would not imply this assertion. -/
theorem volume_anchored_pair_level_eq_zero (n : ℕ) {I : Finset (Fin (n.succPNat : ℕ))}
    {p : Fin (n.succPNat : ℕ) × ℤ} (hp : p ∈ cutoffPairs n.succPNat I) (c : ℝ) :
    volume {y : Fin n → ℝ | gapPairDev n.succPNat (anchoredGapVector n y) p = c} = 0 := by
  let L := ((n : ℝ) + 1) •
    (anchorCoord n (labelOf n.succPNat (((p.1 : ℕ) : ℤ) + p.2)) - anchorCoord n p.1)
  have hL : L ≠ 0 := smul_ne_zero (by positivity)
    (anchorCoord_sub_ne_zero (cutoffPair_endpoint_ne hp))
  let t : ℝ := ((n : ℝ) + 1) *
    (((((p.1 : ℕ) : ℤ) + p.2) / (n.succPNat : ℕ) : ℤ) : ℝ) - p.2
  have hset : {y : Fin n → ℝ | gapPairDev n.succPNat (anchoredGapVector n y) p = c} =
      {y : Fin n → ℝ | L y = c - t} := by
    ext y
    rw [Set.mem_ofPred_eq, gapPairDev_anchoredGapVector]
    change L y + t = c ↔ L y = c - t
    constructor <;> intro h <;> linarith
  rw [hset]
  exact addHaar_linear_level_set_eq_zero volume L hL _

/-- Every affine gap level is null in anchored coordinates for at least
two particles. -/
theorem volume_anchored_gap_level_eq_zero (n : ℕ) (hn : 1 ≤ n)
    (e : Fin (n.succPNat : ℕ)) (c : ℝ) :
    volume {y : Fin n → ℝ | anchoredGapVector n y e = c} = 0 := by
  let L := ((n : ℝ) + 1) • edgeForm n e
  have hL : L ≠ 0 := smul_ne_zero (by positivity)
    (anchorCoord_sub_ne_zero (nextLabel_ne_self (by simpa using hn) e).symm)
  have hset : {y : Fin n → ℝ | anchoredGapVector n y e = c} =
      {y : Fin n → ℝ | L y = c - ((n : ℝ) + 1) * wrapOffset n e} := by
    ext y
    change anchoredGapAt n y (e : ℕ) = c ↔ _
    rw [anchoredGapAt_label]
    change ((n : ℝ) + 1) * (edgeForm n e y + wrapOffset n e) = c ↔
      ((n : ℝ) + 1) * edgeForm n e y = c - ((n : ℝ) + 1) * wrapOffset n e
    constructor <;> intro h <;> nlinarith
  rw [hset]
  exact addHaar_linear_level_set_eq_zero volume L hL _

/-- The kink set has null pullback to the anchored gap hyperplane. -/
theorem anchoredGapVector_preimage_gapKinkSet_volume_zero (n : ℕ) (hn : 1 ≤ n)
    (s K γ ε : ℝ) :
    volume (anchoredGapVector n ⁻¹' gapKinkSet n.succPNat s K γ ε) = 0 := by
  simp only [gapKinkSet, Set.preimage_union, Set.preimage_iUnion]
  apply measure_union_null
  · apply (measure_biUnion_null_iff (cutoffPairs n.succPNat (window n.succPNat K γ)).countable_toSet).2
    intro p hp
    have hset : anchoredGapVector n ⁻¹'
        {z | ∃ c ∈ pairKinkOffsets n.succPNat s K ε p, gapPairDev n.succPNat z p = c} =
        ⋃ c ∈ pairKinkOffsets n.succPNat s K ε p,
          {y | gapPairDev n.succPNat (anchoredGapVector n y) p = c} := by
      ext y
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]
    rw [hset]
    exact (measure_biUnion_null_iff (pairKinkOffsets n.succPNat s K ε p).countable_toSet).2
      fun c _ => volume_anchored_pair_level_eq_zero n hp c
  · apply (measure_biUnion_null_iff (nearestPairs n.succPNat (window n.succPNat K γ)).countable_toSet).2
    intro e _
    have hset : anchoredGapVector n ⁻¹'
        {z | ∃ c ∈ nearKinkValues K ε, z e = c} =
        ⋃ c ∈ nearKinkValues K ε, {y | anchoredGapVector n y e = c} := by
      ext y
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]
    rw [hset]
    exact (measure_biUnion_null_iff (nearKinkValues K ε).countable_toSet).2
      fun c _ => volume_anchored_gap_level_eq_zero n hn e c

/-- Off the kink set the ambient gap cutoff is differentiable. -/
theorem differentiableAt_gapCutoff_of_not_mem_gapKinkSet {N : ℕ+}
    (s K γ ε : ℝ) (hK : 1 ≤ K) (hs : 0 ≤ s) (hε : 0 ≤ ε)
    (z : Fin (N : ℕ) → ℝ) (hz : z ∉ gapKinkSet N s K γ ε) :
    DifferentiableAt ℝ (gapCutoff N s K γ ε) z := by
  have hK0 : 0 < K := by linarith
  have hκ := Real.rpow_pos_of_pos hK0 ε
  have hp : ∀ p ∈ cutoffPairs N (window N K γ), gapPairDev N z p ≠ 0 ∧
      2 * |gapPairDev N z p| / pairScale s K ε p ≠ 1 ∧
      2 * |gapPairDev N z p| / pairScale s K ε p ≠ 2 := by
    intro p hp
    have hA : ∀ c ∈ pairKinkOffsets N s K ε p, gapPairDev N z p ≠ c :=
      fun c hc heq => hz (Or.inl (Set.mem_iUnion₂.2 ⟨p, hp, c, hc, heq⟩))
    exact pair_conditions_of_ne (pairScale_pos_of_mem_cutoffPairs hK0 hp)
      (hA 0 (by simp [pairKinkOffsets])) (hA _ (by simp [pairKinkOffsets]))
      (hA _ (by simp [pairKinkOffsets])) (hA _ (by simp [pairKinkOffsets]))
      (hA _ (by simp [pairKinkOffsets]))
  have hn : ∀ e ∈ nearestPairs N (window N K γ), z e ≠ 0 ∧ 2 * z e / K ^ ε ≠ 1 ∧
      2 * z e / K ^ ε ≠ 2 ∧ 2 / (K ^ ε * z e) ≠ 1 ∧ 2 / (K ^ ε * z e) ≠ 2 := by
    intro e he
    have hB : ∀ c ∈ nearKinkValues K ε, z e ≠ c :=
      fun c hc heq => hz (Or.inr (Set.mem_iUnion₂.2 ⟨e, he, c, hc, heq⟩))
    have hm : K ^ ε * K ^ (-ε) = 1 := by
      rw [Real.rpow_neg hK0.le, mul_inv_cancel₀ hκ.ne']
    exact ⟨hB 0 (by simp [nearKinkValues]), near_conditions_of_ne hκ hm
      (hB 0 (by simp [nearKinkValues])) (hB _ (by simp [nearKinkValues]))
      (hB _ (by simp [nearKinkValues])) (hB _ (by simp [nearKinkValues]))
      (hB _ (by simp [nearKinkValues]))⟩
  obtain ⟨L, hL, _⟩ := gapCutoff_hasFDerivAt s K γ ε hK hs hε z hp hn
  exact hL.differentiableAt

/-- The ambient cutoff is differentiable at almost every anchored gap
vector, with its uniform coordinate bounds and exact selected-edge
chain formula. The law can be any anchored pair law. -/
theorem anchoredMeasureE_cutoff_chain_ae {n : ℕ} (hn : 1 ≤ n) {c : ℝ}
    (χ : HsPairPotentials n.succPNat c) (s K γ ε : ℝ) (hK : 1 ≤ K)
    (hγ : 0 ≤ γ) (hs : 0 ≤ s) (hε : 0 ≤ ε) :
    ∀ᵐ y ∂anchoredMeasureE χ,
      DifferentiableAt ℝ (gapCutoff n.succPNat s K γ ε) (anchoredGapVector n (WithLp.ofLp y)) ∧
      (∀ e, |fderiv ℝ (gapCutoff n.succPNat s K γ ε)
        (anchoredGapVector n (WithLp.ofLp y)) (Pi.single e (1 : ℝ))| ≤ 76 * K ^ (2 * γ + ε)) ∧
      (∀ U : Fin n → ℝ, fderiv ℝ (anchoredCutoff n.succPNat s K γ ε) (WithLp.ofLp y) U =
        ∑ e ∈ nearestPairs n.succPNat (window n.succPNat K γ),
          fderiv ℝ (gapCutoff n.succPNat s K γ ε) (anchoredGapVector n (WithLp.ofLp y))
            (Pi.single e (1 : ℝ)) * (((n : ℝ) + 1) * edgeForm n e U)) := by
  have hac : hsAnchoredLaw χ ≪ (volume : Measure (Fin n → ℝ)) := by
    exact (Measure.smul_absolutelyContinuous.trans (withDensity_absolutelyContinuous _ _)).trans
      (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
  have hz : ∀ᵐ y ∂(volume : Measure (Fin n → ℝ)),
      anchoredGapVector n y ∉ gapKinkSet n.succPNat s K γ ε := by
    rw [ae_iff]
    simpa only [Set.preimage, not_not] using anchoredGapVector_preimage_gapKinkSet_volume_zero n hn s K γ ε
  have hze : ∀ᵐ y ∂anchoredMeasureE χ,
      anchoredGapVector n (WithLp.ofLp y) ∉ gapKinkSet n.succPNat s K γ ε := by
    exact (PiLp.homeomorph 2 (fun _ : Fin n => ℝ)).symm.measurableEmbedding.ae_map_iff.mpr
      (hac.ae_le hz)
  filter_upwards [hze] with y hy
  have hd := differentiableAt_gapCutoff_of_not_mem_gapKinkSet s K γ ε hK hs hε _ hy
  refine ⟨hd, fun e => gapCutoff_fderiv_bound_of_not_mem s K γ ε hK hγ hs hε _ hy e, fun U => ?_⟩
  rw [Internal.anchoredCutoff_chain_of_differentiable n s K γ ε _ hd U]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro e _ he
  rw [fderiv_gapCutoff_single_eq_zero_of_not_mem_nearestPairs s K γ ε hK hγ _ he, zero_mul]

end Riesz1

end
