/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Rigidity.GapLawDensity
public import Mathlib.Algebra.BigOperators.Fin

/-!
# The cumulative chart of the gap simplex

The inverse chart consists of normalized partial sums of the gaps. All chart
identities hold on the ambient spaces. Positivity is used only for the domains.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Riesz1

/-- Normalized partial sums of a vector of `n + 1` gaps. -/
def gapCumulative (n : ℕ) (v : Fin (n + 1) → ℝ) : Fin n → ℝ :=
  fun i => Fin.partialSum v i.succ.castSucc / (n + 1 : ℝ)

lemma anchorVector_gapCumulative (n : ℕ) (v : Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) :
    anchorVector (gapCumulative n v) i = Fin.partialSum v i.castSucc / (n + 1 : ℝ) := by
  induction i using Fin.cases with
  | zero => simp [anchorVector]
  | succ i => rfl

lemma partialSum_last_real {m : ℕ} (v : Fin m → ℝ) :
    Fin.partialSum v (Fin.last m) = ∑ i, v i := by
  simp [Fin.partialSum, List.take_of_length_le (by simp : (List.ofFn v).length ≤ m),
    List.sum_ofFn]

lemma partialSum_eq_sum_filter_real {m : ℕ} (v : Fin m → ℝ) (i : Fin (m + 1)) :
    Fin.partialSum v i = ∑ k : Fin m with k.val < i.val, v k := by
  classical
  induction i using Fin.inductionOn with
  | zero => simp
  | succ i ih =>
    rw [Fin.partialSum_succ, ih]
    have he : (Finset.univ.filter fun k : Fin m => k.val < i.succ.val) =
        insert i (Finset.univ.filter fun k : Fin m => k.val < i.castSucc.val) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Fin.val_succ, Fin.val_castSucc]
      constructor
      · intro h
        rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | h
        · exact Or.inr h
        · exact Or.inl (Fin.ext h)
      · rintro (rfl | h) <;> omega
    rw [he, Finset.sum_insert]
    · ring
    · simp

/-- Differences of partial sums are the consecutive gap sums in the formula of the paper. -/
lemma partialSum_sub_eq_sum_Ico {m : ℕ} (v : Fin m → ℝ) (i j : Fin m) (hij : i ≤ j) :
    Fin.partialSum v j.castSucc - Fin.partialSum v i.castSucc =
      ∑ k ∈ Finset.Ico i j, v k := by
  classical
  rw [partialSum_eq_sum_filter_real, partialSum_eq_sum_filter_real]
  have hsub : (Finset.univ.filter fun k : Fin m => k.val < i.castSucc.val) ⊆
      Finset.univ.filter fun k : Fin m => k.val < j.castSucc.val := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_castSucc] at hk ⊢
    exact lt_of_lt_of_le hk hij
  rw [← Finset.sum_sdiff hsub]
  rw [add_sub_cancel_right]
  apply Finset.sum_congr
  · ext k
    simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.val_castSucc, Finset.mem_Ico, not_lt, Fin.le_def, Fin.lt_def]
    exact and_comm
  · intro k _
    rfl

lemma continuous_partialSum_real {m : ℕ} (i : Fin (m + 1)) :
    Continuous (fun v : Fin m → ℝ => Fin.partialSum v i) := by
  induction i using Fin.inductionOn with
  | zero => simpa only [Fin.partialSum_zero] using continuous_const (y := (0 : ℝ))
  | succ i ih =>
    simp only [Fin.partialSum_succ]
    exact ih.add (continuous_apply i)

lemma continuous_gapCumulative (n : ℕ) : Continuous (gapCumulative n) := by
  exact continuous_pi fun i => (continuous_partialSum_real i.succ.castSucc).div_const _

lemma gapCumulative_combo (n : ℕ) (v w : Fin (n + 1) → ℝ) (a b : ℝ) :
    gapCumulative n (a • v + b • w) = a • gapCumulative n v + b • gapCumulative n w := by
  have hsum (i : Fin (n + 2)) :
      Fin.partialSum (a • v + b • w) i =
        a * Fin.partialSum v i + b * Fin.partialSum w i := by
    induction i using Fin.inductionOn with
    | zero => simp
    | succ i ih =>
      simp only [Fin.partialSum_succ, ih, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
  ext i
  simp only [gapCumulative, hsum, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

lemma anchoredGapVector_castSucc (n : ℕ) (y : Fin n → ℝ) (i : Fin n) :
    anchoredGapVector n y i.castSucc =
      (n + 1 : ℝ) * (anchorVector y i.succ - anchorVector y i.castSucc) := by
  unfold anchoredGapVector
  dsimp only [Nat.succPNat_coe]
  rw [show ((i.castSucc : Fin (n + 1)) : ℤ) + 1 = (i.succ : ℕ) by simp]
  exact congrArg (fun t => (n + 1 : ℝ) * t)
    (congrArg₂ (· - ·) (anchoredCyclicOffset_natCast n y i.succ)
      (anchoredCyclicOffset_natCast n y i.castSucc))

lemma anchoredGapVector_last (n : ℕ) (y : Fin n → ℝ) :
    anchoredGapVector n y (Fin.last n) =
      (n + 1 : ℝ) * (1 - anchorVector y (Fin.last n)) := by
  unfold anchoredGapVector
  dsimp only [Nat.succPNat_coe]
  have hper := anchoredCyclicOffset_period n y 0
  have hz : anchoredCyclicOffset n y 0 = 0 := anchoredCyclicOffset_natCast n y 0
  simp only [zero_add, Nat.succPNat_coe, hz, zero_add] at hper
  simp only [Nat.cast_succ] at hper
  rw [show ((Fin.last n : Fin (n + 1)) : ℤ) + 1 = (n.succPNat : ℕ) by simp]
  change (n + 1 : ℝ) * (anchoredCyclicOffset n y (n + 1) - _) = _
  exact congrArg (fun t => (n + 1 : ℝ) * t)
    (congrArg₂ (· - ·) hper (anchoredCyclicOffset_natCast n y (Fin.last n)))

lemma partialSum_anchoredGapVector (n : ℕ) (y : Fin n → ℝ) (i : Fin (n + 1)) :
    Fin.partialSum (anchoredGapVector n y) i.castSucc =
      (n + 1 : ℝ) * anchorVector y i := by
  let v : Fin (n + 1) → ℝ := anchoredGapVector n y
  let w : Fin (n + 1) → ℝ := anchorVector y
  change Fin.partialSum v i.castSucc = (n + 1 : ℝ) * w i
  induction i using Fin.inductionOn with
  | zero => simp [w, anchorVector]
  | succ i ih =>
    have hv : v i.castSucc = (n + 1 : ℝ) * (w i.succ - w i.castSucc) :=
      anchoredGapVector_castSucc n y i
    rw [← Fin.succ_castSucc, Fin.partialSum_succ, ih, hv]
    ring

/-- Recover every cumulative coordinate from its consecutive gaps. -/
theorem gapCumulative_anchoredGapVector (n : ℕ) (y : Fin n → ℝ) :
    gapCumulative n (anchoredGapVector n y) = y := by
  ext i
  change Fin.partialSum (anchoredGapVector n y) i.succ.castSucc / (n + 1 : ℝ) = y i
  rw [partialSum_anchoredGapVector]
  simp [anchorVector, mul_div_cancel_left₀, show (n + 1 : ℝ) ≠ 0 by positivity]

/-- On the hyperplane of total mass `n + 1`, the two charts are inverse. -/
theorem anchoredGapVector_gapCumulative (n : ℕ) (v : Fin (n + 1) → ℝ)
    (hv : ∑ i, v i = (n + 1 : ℝ)) :
    anchoredGapVector n (gapCumulative n v) = v := by
  ext i
  induction i using Fin.lastCases with
  | last =>
    rw [anchoredGapVector_last, anchorVector_gapCumulative]
    have hs := Fin.partialSum_succ v (Fin.last n)
    rw [show (Fin.last n).succ = Fin.last (n + 1) by rfl, partialSum_last_real, hv] at hs
    field_simp
    nlinarith
  | cast i =>
    rw [anchoredGapVector_castSucc, anchorVector_gapCumulative, anchorVector_gapCumulative,
      ← Fin.succ_castSucc, Fin.partialSum_succ]
    field_simp
    ring

lemma strictMono_partialSum_of_pos {m : ℕ} (v : Fin m → ℝ) (hv : ∀ i, 0 < v i) :
    StrictMono (Fin.partialSum v) := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  rw [Fin.partialSum_succ]
  exact lt_add_of_pos_right _ (hv i)

/-- The inverse chart takes the entire positive simplex to the ordered domain. -/
theorem gapCumulative_mem_anchoredDomain (n : ℕ) {v : Fin (n + 1) → ℝ}
    (hv : v ∈ gapSimplex n.succPNat) : gapCumulative n v ∈ anchoredDomain n := by
  have hN : (0 : ℝ) < n + 1 := by positivity
  have hmono := strictMono_partialSum_of_pos v hv.1
  have htotal : Fin.partialSum v (Fin.last (n + 1)) = (n + 1 : ℝ) := by
    rw [partialSum_last_real]
    exact hv.2.trans (by simp only [Nat.succPNat_coe, Nat.cast_succ])
  refine ⟨fun i => ⟨?_, ?_⟩, ?_⟩
  · apply div_pos _ hN
    have h := hmono (show (0 : Fin (n + 2)) < i.succ.castSucc by simp)
    simpa only [Fin.partialSum_zero] using h
  · apply (div_lt_one hN).mpr
    rw [← htotal]
    exact hmono (by simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ, Fin.val_last]; omega)
  · intro i j hij
    exact (div_lt_div_iff_of_pos_right hN).mpr (hmono (by
      simpa only [Fin.castSucc_lt_castSucc_iff, Fin.succ_lt_succ_iff] using hij))

/-- The chart covers precisely the full open gap simplex. -/
theorem image_anchoredGapVector_anchoredDomain (n : ℕ) :
    anchoredGapVector n '' anchoredDomain n = gapSimplex n.succPNat := by
  apply Set.Subset.antisymm
  · rintro v ⟨y, hy, rfl⟩
    exact anchoredGapVector_mem_gapSimplex n hy
  · intro v hv
    exact ⟨gapCumulative n v, gapCumulative_mem_anchoredDomain n hv,
      anchoredGapVector_gapCumulative n v (hv.2.trans (by
        simp only [Nat.succPNat_coe, Nat.cast_succ]))⟩

theorem convex_gapSimplex (N : ℕ+) : Convex ℝ (gapSimplex N) := by
  intro v hv w hw a b ha hb hab
  refine ⟨fun i => ?_, ?_⟩
  · change 0 < a * v i + b * w i
    rcases eq_or_lt_of_le ha with rfl | ha'
    · have hb' : b = 1 := by linarith
      simpa only [zero_mul, zero_add, hb', one_mul] using hw.1 i
    · exact add_pos_of_pos_of_nonneg (mul_pos ha' (hv.1 i)) (mul_nonneg hb (hw.1 i).le)
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, hv.2, hw.2, ← add_mul, hab, one_mul]

/-- Splitting a symmetric off-diagonal sum into its upper triangle. -/
lemma sum_offDiagonal_eq_two_sum_lt {m : ℕ} (f : Fin m → Fin m → ℝ)
    (hf : ∀ i j, f i j = f j i) :
    (∑ i, ∑ j ∈ Finset.univ.erase i, f i j) =
      2 * ∑ i, ∑ j with i < j, f i j := by
  classical
  have hs (i : Fin m) : (∑ j ∈ Finset.univ.erase i, f i j) =
      (∑ j with i < j, f i j) + ∑ j with j < i, f i j := by
    have he : Finset.univ.erase i =
        (Finset.univ.filter fun j => i < j) ∪ (Finset.univ.filter fun j => j < i) := by
      ext j
      simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_union,
        Finset.mem_filter, true_and]
      exact ne_iff_lt_or_gt (a := j) (b := i) |>.trans or_comm
    rw [he, Finset.sum_union]
    exact Finset.disjoint_filter.mpr (fun j _ h₁ h₂ => (lt_asymm h₁ h₂).elim)
  simp_rw [hs]
  rw [Finset.sum_add_distrib]
  have hswap : (∑ i : Fin m, ∑ j with j < i, f i j) =
      ∑ i : Fin m, ∑ j with i < j, f i j := by
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
    simp_rw [hf]
  rw [hswap]
  ring

/-- The pair-energy formula in gap coordinates, using differences of partial sums.
For `i < j`, the difference is exactly the consecutive sum of gaps from `i` to `j-1`.
-/
def gapEnergy (s : RieszExponent) (n : ℕ) (v : Fin (n + 1) → ℝ) : ℝ :=
  2 * (n + 1 : ℝ) ^ (-s.val) *
    ∑ i : Fin (n + 1), ∑ j with i < j,
      rieszRepresentative s (((Fin.partialSum v j.castSucc -
        Fin.partialSum v i.castSucc) / (n + 1 : ℝ) : ℝ) : UnitAddCircle)

/-- The explicit gap energy is the cumulative-coordinate energy. -/
theorem gapEnergy_eq_anchoredEnergy (s : RieszExponent) (n : ℕ)
    (v : Fin (n + 1) → ℝ) :
    gapEnergy s n v = anchoredEnergy s n (gapCumulative n v) := by
  let f : Fin (n + 1) → Fin (n + 1) → ℝ := fun i j =>
    rieszRepresentative s ((anchorVector (gapCumulative n v) i -
      anchorVector (gapCumulative n v) j : ℝ) : UnitAddCircle)
  have hf (i j) : f i j = f j i := by
    dsimp only [f]
    rw [show anchorVector (gapCumulative n v) i - anchorVector (gapCumulative n v) j =
      -(anchorVector (gapCumulative n v) j - anchorVector (gapCumulative n v) i) by ring,
      AddCircle.coe_neg, rieszRepresentative_neg]
  have hsum := sum_offDiagonal_eq_two_sum_lt f hf
  have hterm (i j) : f i j = rieszRepresentative s
      (((Fin.partialSum v j.castSucc - Fin.partialSum v i.castSucc) /
        (n + 1 : ℝ) : ℝ) : UnitAddCircle) := by
    rw [hf i j]
    dsimp only [f]
    rw [anchorVector_gapCumulative, anchorVector_gapCumulative, ← sub_div]
  unfold anchoredEnergy
  simp only [Nat.succPNat_coe, Nat.cast_succ]
  change _ = (n + 1 : ℝ) ^ (-s.val) * ∑ i, ∑ j ∈ Finset.univ.erase i, f i j
  rw [hsum]
  simp_rw [hterm]
  unfold gapEnergy
  ring

theorem gapEnergy_anchoredGapVector (s : RieszExponent) (n : ℕ) (y : Fin n → ℝ) :
    gapEnergy s n (anchoredGapVector n y) = anchoredEnergy s n y := by
  calc
    _ = anchoredEnergy s n (gapCumulative n (anchoredGapVector n y)) :=
      gapEnergy_eq_anchoredEnergy s n (anchoredGapVector n y)
    _ = _ := congrArg (anchoredEnergy s n) (gapCumulative_anchoredGapVector n y)

/-- The gap-energy formula of the paper equals the original energy of every configuration. -/
theorem gapEnergy_gapVector (s : RieszExponent) (n : ℕ) (X : Configuration n.succPNat) :
    gapEnergy s n (gapVector X) = energy s X := by
  calc
    _ = gapEnergy s n (anchoredGapVector n (anchorCoords n X.val).2) :=
      congrArg (gapEnergy s n) (gapVector_eq_anchoredGapVector n X)
    _ = anchoredEnergy s n (anchorCoords n X.val).2 := gapEnergy_anchoredGapVector s n _
    _ = energy s X := (energy_eq_anchoredEnergy s n X).symm

/-- Convexity of the explicit gap energy on the full simplex. -/
theorem convexOn_gapEnergy (s : RieszExponent) (n : ℕ) :
    ConvexOn ℝ (gapSimplex n.succPNat) (gapEnergy s n) := by
  let S : Set (Fin (n + 1) → ℝ) := gapSimplex n.succPNat
  change ConvexOn ℝ S (gapEnergy s n)
  refine ⟨convex_gapSimplex _, ?_⟩
  intro v hv w hw a b ha hb hab
  simp_rw [gapEnergy_eq_anchoredEnergy]
  rw [gapCumulative_combo]
  exact (convexOn_anchoredEnergy s n).2 (gapCumulative_mem_anchoredDomain n hv)
    (gapCumulative_mem_anchoredDomain n hw) ha hb hab

/-- The explicit consecutive-sum form of the gap energy. -/
theorem gapEnergy_eq_sum_Ico (s : RieszExponent) (n : ℕ) (v : Fin (n + 1) → ℝ) :
    gapEnergy s n v = 2 * (n + 1 : ℝ) ^ (-s.val) *
      ∑ i : Fin (n + 1), ∑ j with i < j,
        rieszRepresentative s (((∑ k ∈ Finset.Ico i j, v k) /
          (n + 1 : ℝ) : ℝ) : UnitAddCircle) := by
  unfold gapEnergy
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j hj
  rw [partialSum_sub_eq_sum_Ico v i j (Finset.mem_filter.mp hj).2.le]

/-- Simplex measure in the concrete chart of normalized cumulative gaps.
It is the image of `(n)`-dimensional Lebesgue measure on the ordered offset domain.
-/
def gapSimplexVolume (n : ℕ) : Measure (Fin (n + 1) → ℝ) :=
  (volume.restrict (anchoredDomain n)).map (anchoredGapVector n)

/-- The normalized density on the gap simplex for the cumulative chart measure. -/
def gapProbabilityDensity (P : Parameters) (n : ℕ) (v : Fin (n + 1) → ℝ) : ℝ :=
  (partitionFunction P n.succPNat).toReal⁻¹ *
    Real.exp (-P.val.1 * gapEnergy (parametersExponent P) n v)

lemma gapProbabilityDensity_eq (P : Parameters) (n : ℕ) (v : Fin (n + 1) → ℝ) :
    gapProbabilityDensity P n v = anchoredProbabilityDensity P n (gapCumulative n v) := by
  rw [gapProbabilityDensity, gapEnergy_eq_anchoredEnergy]
  rfl

theorem gapProbabilityDensity_pos (P : Parameters) (n : ℕ) (v : Fin (n + 1) → ℝ) :
    0 < gapProbabilityDensity P n v := by
  rw [gapProbabilityDensity_eq]
  exact anchoredProbabilityDensity_pos P n _

lemma measurable_gapProbabilityDensity (P : Parameters) (n : ℕ) :
    Measurable (gapProbabilityDensity P n) := by
  have he : Measurable (gapEnergy (parametersExponent P) n) := by
    have heq : gapEnergy (parametersExponent P) n =
        anchoredEnergy (parametersExponent P) n ∘ gapCumulative n :=
      funext (gapEnergy_eq_anchoredEnergy _ _)
    rw [heq]
    exact (measurable_anchoredEnergy _ _).comp (continuous_gapCumulative n).measurable
  exact measurable_const.mul (Real.measurable_exp.comp (he.const_mul _))

/-- The full gap law has a positive exponential density for the explicit simplex measure. -/
theorem map_gapVector_gibbsMeasure_simplex (P : Parameters) (n : ℕ) :
    (gibbsMeasure P n.succPNat).map gapVector =
      (gapSimplexVolume n).withDensity (fun v => ENNReal.ofReal (gapProbabilityDensity P n v)) := by
  rw [map_gapVector_gibbsMeasure_density]
  let F : (Fin n → ℝ) → (Fin (n + 1) → ℝ) := anchoredGapVector n
  let ρ : (Fin (n + 1) → ℝ) → ENNReal :=
    fun v => ENNReal.ofReal (gapProbabilityDensity P n v)
  have hcomp : (fun y => ENNReal.ofReal (anchoredProbabilityDensity P n y)) =
      fun y => ρ (F y) := by
    funext y
    apply congrArg ENNReal.ofReal
    exact ((gapProbabilityDensity_eq P n (F y)).trans
      (congrArg (anchoredProbabilityDensity P n) (gapCumulative_anchoredGapVector n y))).symm
  change ((volume.restrict (anchoredDomain n)).withDensity _).map F =
    ((volume.restrict (anchoredDomain n)).map F).withDensity ρ
  rw [hcomp]
  have hF : Measurable F := measurable_anchoredGapVector n
  have hρ : Measurable ρ :=
    ENNReal.measurable_ofReal.comp (measurable_gapProbabilityDensity P n)
  exact map_withDensity_comp (volume.restrict (anchoredDomain n)) hF hρ

/-- The logarithm of the positive simplex density is concave on the entire simplex. -/
theorem concaveOn_log_gapProbabilityDensity (P : Parameters) (n : ℕ) :
    ConcaveOn ℝ (gapSimplex n.succPNat) (fun v => Real.log (gapProbabilityDensity P n v)) := by
  let S : Set (Fin (n + 1) → ℝ) := gapSimplex n.succPNat
  change ConcaveOn ℝ S _
  refine ⟨convex_gapSimplex _, ?_⟩
  intro v hv w hw a b ha hb hab
  simp_rw [gapProbabilityDensity_eq]
  rw [gapCumulative_combo]
  exact (concaveOn_log_anchoredProbabilityDensity P n).2
    (gapCumulative_mem_anchoredDomain n hv) (gapCumulative_mem_anchoredDomain n hw) ha hb hab

end Riesz1

end
end
