/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.APrioriGoodGradientProduct
public import Riesz1.ToMathlib.Packing.GradientHyperplane

/-!
# Almost-everywhere derivative bound for the gap-coordinate cutoff

The gradient claim in the proof of Lemma 5.2: the cutoff `η̃`, written in the gaps
`z_i = N (x_{i+1} - x_i)`, has derivative of size at most `C K^A` in each gap coordinate, almost
everywhere, with `C` absolute and `A = 2 γ + ε`. The bound does not depend on `N`.

The cutoff is differentiable off the exceptional set `gapKinkSet`, a finite union of affine
hyperplanes (the kinks of the scalar cutoff and the poles of the gap factors). Each hyperplane is
Lebesgue-null by `Riesz1/ToMathlib/Packing/GradientHyperplane.lean`, so the bound holds for
almost every gap vector.

* `gapKinkSet_volume_zero`: the exceptional set is null.
* `gapCutoff_fderiv_bound_of_not_mem`: off the exceptional set, `|∂_i η̃| ≤ 76 K^{2γ+ε}`.
* `gapCutoff_ae_fderiv_bound`: the almost-everywhere form.
-/

@[expose] public section

noncomputable section

open Finset MeasureTheory

namespace Riesz1

variable {N : ℕ+}

/-! ### Nonvanishing of the arc functionals -/

/-- The coordinate functional `w ↦ w i` is nonzero. -/
theorem proj_ne_zero_of_label (i : Fin (N : ℕ)) :
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (N : ℕ) => ℝ) i) ≠ 0 := by
  intro h
  have h1 := congrArg (fun L : (Fin (N : ℕ) → ℝ) →L[ℝ] ℝ => L (Pi.single i (1 : ℝ))) h
  simp at h1

/-- The oriented arc functional over `[a, b)` minus `[b, a)` is nonzero when `a ≠ b`. -/
theorem gapArcCLM_ne_zero {a b : ℤ} (hab : a ≠ b) : gapArcCLM N a b ≠ 0 := by
  intro h
  have hnonneg : ∀ j : Fin (N : ℕ), ∀ r : ℤ,
      0 ≤ (Pi.single j (1 : ℝ) : Fin (N : ℕ) → ℝ) (labelOf N r) := by
    intro j r
    rw [Pi.single_apply]
    split_ifs <;> norm_num
  rcases lt_or_gt_of_ne hab with hlt | hlt
  · -- `a < b`: the sum over `[b, a)` is empty, and the sum over `[a, b)` contains `a`.
    have h0 := congrArg (fun L : (Fin (N : ℕ) → ℝ) →L[ℝ] ℝ =>
      L (Pi.single (labelOf N a) (1 : ℝ))) h
    simp only [zero_apply] at h0
    rw [gapArcCLM_apply] at h0
    unfold gapOrientedSum at h0
    rw [Finset.Ico_eq_empty_of_le hlt.le, Finset.sum_empty, sub_zero] at h0
    have hge : (Pi.single (labelOf N a) (1 : ℝ) : Fin (N : ℕ) → ℝ) (labelOf N a) ≤
        ∑ r ∈ Ico a b, (Pi.single (labelOf N a) (1 : ℝ) : Fin (N : ℕ) → ℝ) (labelOf N r) :=
      Finset.single_le_sum (fun r _ => hnonneg (labelOf N a) r) (Finset.mem_Ico.2 ⟨le_refl a, hlt⟩)
    rw [Pi.single_eq_same] at hge
    linarith
  · -- `b < a`: the sum over `[a, b)` is empty, and the sum over `[b, a)` contains `b`.
    have h0 := congrArg (fun L : (Fin (N : ℕ) → ℝ) →L[ℝ] ℝ =>
      L (Pi.single (labelOf N b) (1 : ℝ))) h
    simp only [zero_apply] at h0
    rw [gapArcCLM_apply] at h0
    unfold gapOrientedSum at h0
    rw [Finset.Ico_eq_empty_of_le hlt.le, Finset.sum_empty, zero_sub] at h0
    have hge : (Pi.single (labelOf N b) (1 : ℝ) : Fin (N : ℕ) → ℝ) (labelOf N b) ≤
        ∑ r ∈ Ico b a, (Pi.single (labelOf N b) (1 : ℝ) : Fin (N : ℕ) → ℝ) (labelOf N r) :=
      Finset.single_le_sum (fun r _ => hnonneg (labelOf N b) r) (Finset.mem_Ico.2 ⟨le_refl b, hlt⟩)
    rw [Pi.single_eq_same] at hge
    linarith

/-! ### Null sets -/

/-- A finite union of level sets of a nonzero linear functional, shifted by `t`, is null. -/
theorem volume_exists_mem_linear_sub_eq_zero (L : (Fin (N : ℕ) → ℝ) →L[ℝ] ℝ) (hL : L ≠ 0)
    (C : Finset ℝ) (t : ℝ) :
    volume {z : Fin (N : ℕ) → ℝ | ∃ c ∈ C, L z - t = c} = 0 := by
  have hset : {z : Fin (N : ℕ) → ℝ | ∃ c ∈ C, L z - t = c} =
      ⋃ c ∈ (C : Set ℝ), {z : Fin (N : ℕ) → ℝ | L z = c + t} := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_coe, exists_prop]
    constructor
    · rintro ⟨c, hc, hz⟩
      exact ⟨c, hc, by linarith⟩
    · rintro ⟨c, hc, hz⟩
      exact ⟨c, hc, by linarith⟩
  rw [hset, measure_biUnion_null_iff (C.finite_toSet.countable)]
  intro c _
  exact addHaar_linear_level_set_eq_zero volume L hL (c + t)

/-! ### The exceptional set -/

/-- The offsets `c` at which the pair deviation `D` of `p` meets a kink, `D = c`: the points
`0` and `±M/2`, `±M` for the tolerance `M = K^ε |k|^{s/2}` of the pair. -/
def pairKinkOffsets (N : ℕ+) (s K ε : ℝ) (p : Fin (N : ℕ) × ℤ) : Finset ℝ :=
  {0, pairScale s K ε p / 2, -(pairScale s K ε p / 2), pairScale s K ε p, -(pairScale s K ε p)}

/-- The values of a nearest-neighbour gap `z_i` at which one of its two factors has a kink or a
pole. -/
def nearKinkValues (K ε : ℝ) : Finset ℝ :=
  {0, K ^ (-ε), 2 * K ^ (-ε), K ^ ε / 2, K ^ ε}

/-- The exceptional set of the gap-coordinate cutoff: the gap vectors at which some pair deviation
or some nearest-neighbour gap meets a kink of its factor. It is a finite union of affine
hyperplanes. -/
def gapKinkSet (N : ℕ+) (s K γ ε : ℝ) : Set (Fin (N : ℕ) → ℝ) :=
  (⋃ p ∈ cutoffPairs N (window N K γ), {z | ∃ c ∈ pairKinkOffsets N s K ε p,
      gapPairDev N z p = c}) ∪
    ⋃ i ∈ nearestPairs N (window N K γ), {z | ∃ c ∈ nearKinkValues K ε, z i = c}

/-- **The exceptional set is null.** -/
theorem gapKinkSet_volume_zero (s K γ ε : ℝ) :
    volume (gapKinkSet N s K γ ε) = 0 := by
  unfold gapKinkSet
  apply measure_union_null
  · refine (measure_biUnion_null_iff (cutoffPairs N (window N K γ)).countable_toSet).2
      fun p hp => ?_
    have hp2 : p.2 ≠ 0 :=
      (Finset.mem_erase.1 (Finset.mem_product.1 (Finset.mem_filter.1 hp).1).2).1
    have hfun : (fun z : Fin (N : ℕ) → ℝ => gapPairDev N z p) =
        fun z => gapArcCLM N (((p.1 : ℕ) : ℤ)) (((p.1 : ℕ) : ℤ) + p.2) z - p.2 :=
      gapPairDev_eq_arc N p
    have hset : {z : Fin (N : ℕ) → ℝ | ∃ c ∈ pairKinkOffsets N s K ε p,
        gapPairDev N z p = c} =
        {z | ∃ c ∈ pairKinkOffsets N s K ε p,
          gapArcCLM N (((p.1 : ℕ) : ℤ)) (((p.1 : ℕ) : ℤ) + p.2) z - p.2 = c} := by
      ext z
      simp only [Set.mem_ofPred_eq]
      rw [show gapPairDev N z p = gapArcCLM N (((p.1 : ℕ) : ℤ)) (((p.1 : ℕ) : ℤ) + p.2) z - p.2 from
        congrFun hfun z]
    rw [hset]
    exact volume_exists_mem_linear_sub_eq_zero _
      (gapArcCLM_ne_zero (by intro h; apply hp2; linarith)) _ _
  · refine (measure_biUnion_null_iff (nearestPairs N (window N K γ)).countable_toSet).2
      fun i _ => ?_
    have h := volume_exists_mem_linear_sub_eq_zero
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (N : ℕ) => ℝ) i)
      (proj_ne_zero_of_label i) (nearKinkValues K ε) 0
    simpa using h

/-! ### Elementary conditions off the kinks -/

/-- A pair deviation off the five kink values has the three properties needed for differentiation
of its factor. -/
theorem pair_conditions_of_ne {D M : ℝ} (hM : 0 < M) (h0 : D ≠ 0) (h1 : D ≠ M / 2)
    (h2 : D ≠ -(M / 2)) (h3 : D ≠ M) (h4 : D ≠ -M) :
    D ≠ 0 ∧ 2 * |D| / M ≠ 1 ∧ 2 * |D| / M ≠ 2 := by
  refine ⟨h0, fun h => ?_, fun h => ?_⟩
  · rw [div_eq_iff hM.ne'] at h
    rcases (abs_eq (by linarith)).1 (by linarith : |D| = M / 2) with h' | h'
    · exact h1 h'
    · exact h2 h'
  · rw [div_eq_iff hM.ne'] at h
    rcases (abs_eq (by linarith)).1 (by linarith : |D| = M) with h' | h'
    · exact h3 h'
    · exact h4 h'

/-- The nearest-neighbour conditions off the kinks: the factors `c(2 z / κ)` and `c(2 / (κ z))`
are differentiable at `z`, where `κ m = 1`. -/
theorem near_conditions_of_ne {κ m z : ℝ} (hκ : 0 < κ) (hm : κ * m = 1) (h0 : z ≠ 0)
    (h1 : z ≠ κ / 2) (h2 : z ≠ κ) (h3 : z ≠ 2 * m) (h4 : z ≠ m) :
    2 * z / κ ≠ 1 ∧ 2 * z / κ ≠ 2 ∧ 2 / (κ * z) ≠ 1 ∧ 2 / (κ * z) ≠ 2 := by
  have hκz : κ * z ≠ 0 := mul_ne_zero hκ.ne' h0
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · rw [div_eq_iff hκ.ne'] at h
    exact h1 (by linarith)
  · rw [div_eq_iff hκ.ne'] at h
    exact h2 (by linarith)
  · rw [div_eq_iff hκz] at h
    exact h3 (by linear_combination (-z) * hm + (-m) * h)
  · rw [div_eq_iff hκz] at h
    exact h4 (by linear_combination (-z) * hm + (-m / 2) * h)

/-! ### Numerical bound -/

/-- The numerical estimate: `4 K^ε + (2 / K^ε) c ≤ 76 K^{2γ+ε}` when `c ≤ (2m + 1) m` and
`m ≤ 4 K^γ`. -/
theorem gradient_numeric_bound {K γ ε : ℝ} (hK1 : 1 ≤ K) (hγ : 0 ≤ γ) (hε : 0 ≤ ε)
    (m : ℕ) (hm : (m : ℝ) ≤ 4 * K ^ γ) (c : ℝ) (hc0 : 0 ≤ c)
    (hc : c ≤ (2 * (m : ℝ) + 1) * m) :
    4 * K ^ ε + (2 / K ^ ε) * c ≤ 76 * K ^ (2 * γ + ε) := by
  have hKγ1 : 1 ≤ K ^ γ := Real.one_le_rpow hK1 hγ
  have hKε1 : 1 ≤ K ^ ε := Real.one_le_rpow hK1 hε
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hsq : K ^ (2 * γ) = (K ^ γ) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith), mul_comm]
    norm_num
  -- `(2m + 1) m ≤ 36 (K^γ)^2`
  have hcount : (2 * (m : ℝ) + 1) * m ≤ 36 * (K ^ γ) ^ 2 := by
    nlinarith
  have hdiv : (2 / K ^ ε) * c ≤ 2 * c := by
    have h2 : 2 / K ^ ε ≤ 2 := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    exact mul_le_mul_of_nonneg_right h2 hc0
  have hA1 : K ^ (2 * γ) ≤ K ^ (2 * γ + ε) :=
    Real.rpow_le_rpow_of_exponent_le hK1 (by linarith)
  have hA2 : K ^ ε ≤ K ^ (2 * γ + ε) :=
    Real.rpow_le_rpow_of_exponent_le hK1 (by linarith)
  rw [hsq] at hA1
  nlinarith

/-! ### The derivative bound off the exceptional set -/

/-- **Derivative bound off the exceptional set.** Let `K ≥ 1`, `γ ≥ 0`, `s ≥ 0`, `ε ≥ 0`, and let
`z` be a gap vector outside `gapKinkSet`. Then the derivative of the gap-coordinate cutoff at `z`
in the coordinate direction `e_i` is at most `76 K^{2γ+ε}` in absolute value, for every `N`. -/
theorem gapCutoff_fderiv_bound_of_not_mem (s K γ ε : ℝ) (hK1 : 1 ≤ K) (hγ : 0 ≤ γ) (hs : 0 ≤ s)
    (hε : 0 ≤ ε) (z : Fin (N : ℕ) → ℝ) (hz : z ∉ gapKinkSet N s K γ ε) (i : Fin (N : ℕ)) :
    |fderiv ℝ (gapCutoff N s K γ ε) z (Pi.single i (1 : ℝ))| ≤ 76 * K ^ (2 * γ + ε) := by
  have hK0 : 0 < K := by linarith
  have hKε1 : 1 ≤ K ^ ε := Real.one_le_rpow hK1 hε
  have hKεpos : 0 < K ^ ε := by linarith
  have hpair : ∀ p ∈ cutoffPairs N (window N K γ), gapPairDev N z p ≠ 0 ∧
      2 * |gapPairDev N z p| / pairScale s K ε p ≠ 1 ∧
      2 * |gapPairDev N z p| / pairScale s K ε p ≠ 2 := by
    intro p hp
    have hA : ∀ c ∈ pairKinkOffsets N s K ε p, gapPairDev N z p ≠ c :=
      fun c hc heq => hz (Or.inl (Set.mem_iUnion₂.2 ⟨p, hp, c, hc, heq⟩))
    have hM := pairScale_pos_of_mem_cutoffPairs (s := s) (ε := ε) hK0 hp
    refine pair_conditions_of_ne hM ?_ ?_ ?_ ?_ ?_
    · exact hA 0 (by simp [pairKinkOffsets])
    · exact hA _ (by simp [pairKinkOffsets])
    · exact hA _ (by simp [pairKinkOffsets])
    · exact hA _ (by simp [pairKinkOffsets])
    · exact hA _ (by simp [pairKinkOffsets])
  have hnear : ∀ j ∈ nearestPairs N (window N K γ), z j ≠ 0 ∧ 2 * z j / K ^ ε ≠ 1 ∧
      2 * z j / K ^ ε ≠ 2 ∧ 2 / (K ^ ε * z j) ≠ 1 ∧ 2 / (K ^ ε * z j) ≠ 2 := by
    intro j hj
    have hB : ∀ c ∈ nearKinkValues K ε, z j ≠ c :=
      fun c hc heq => hz (Or.inr (Set.mem_iUnion₂.2 ⟨j, hj, c, hc, heq⟩))
    have hm : K ^ ε * K ^ (-ε) = 1 := by
      rw [Real.rpow_neg hK0.le, mul_inv_cancel₀ hKεpos.ne']
    have hc := near_conditions_of_ne hKεpos hm (hB 0 (by simp [nearKinkValues]))
      (hB (K ^ ε / 2) (by simp [nearKinkValues]))
      (hB (K ^ ε) (by simp [nearKinkValues]))
      (hB (2 * K ^ (-ε)) (by simp [nearKinkValues]))
      (hB (K ^ (-ε)) (by simp [nearKinkValues]))
    exact ⟨hB 0 (by simp [nearKinkValues]), hc.1, hc.2.1, hc.2.2.1, hc.2.2.2⟩
  obtain ⟨f', hf', hbd⟩ := gapCutoff_hasFDerivAt s K γ ε hK1 hs hε z hpair hnear
  rw [hf'.fderiv]
  -- Count the pairs whose arc contains `i`, and apply the numerical estimate.
  set m : ℕ := ⌊4 * K ^ γ⌋₊ with hmdef
  have hcard := gradient_card_arc_ne_zero N i (cutoffPairs N (window N K γ)) m
    (gradient_pair_bound hK1 hγ N)
  have hcardR : ((((cutoffPairs N (window N K γ)).filter fun p =>
      gapOrientedSum N (Pi.single i (1 : ℝ)) (((p.1 : ℕ) : ℤ))
        (((p.1 : ℕ) : ℤ) + p.2) ≠ 0).card : ℕ) : ℝ) ≤ (2 * (m : ℝ) + 1) * m := by
    exact_mod_cast hcard
  have hmR : (m : ℝ) ≤ 4 * K ^ γ := Nat.floor_le (by linarith [Real.one_le_rpow hK1 hγ])
  have hnum := gradient_numeric_bound hK1 hγ hε m hmR _ (Nat.cast_nonneg _) hcardR
  exact (hbd i).trans (by linarith [hnum])

/-- **Almost-everywhere derivative bound.** Let `K ≥ 1`, `γ ≥ 0`, `s ≥ 0` and `ε ≥ 0`. For every
`N` and every gap index `i`, the derivative of the gap-coordinate cutoff in the coordinate direction
`e_i` is at most `76 K^{2γ+ε}` in absolute value, for almost every gap vector `z`. The numerical factor
`76` and the exponent `2γ + ε` do not depend on `N`. -/
theorem gapCutoff_ae_fderiv_bound (s K γ ε : ℝ) (hK1 : 1 ≤ K) (hγ : 0 ≤ γ) (hs : 0 ≤ s)
    (hε : 0 ≤ ε) (i : Fin (N : ℕ)) :
    ∀ᵐ z ∂(volume : Measure (Fin (N : ℕ) → ℝ)),
      |fderiv ℝ (gapCutoff N s K γ ε) z (Pi.single i (1 : ℝ))| ≤ 76 * K ^ (2 * γ + ε) := by
  have hnull : ∀ᵐ z ∂(volume : Measure (Fin (N : ℕ) → ℝ)), z ∉ gapKinkSet N s K γ ε := by
    rw [ae_iff]
    simpa using gapKinkSet_volume_zero (N := N) s K γ ε
  filter_upwards [hnull] with z hz
  exact gapCutoff_fderiv_bound_of_not_mem s K γ ε hK1 hγ hs hε z hz i

end Riesz1

end
end
