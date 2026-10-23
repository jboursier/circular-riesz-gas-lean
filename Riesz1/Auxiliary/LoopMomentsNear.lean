/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopMomentsCount
public import Riesz1.Auxiliary.LoopMomentsRooted

/-!
# Short arcs and the rooted energy

The moments part of Lemma B.2, the claim on `∑_{z_i ∈ J} E_i` for an arc of length
`r ≤ 3`. Two particles of such an arc are at circular distance at most `r ≤ 3`, so each
other particle of the arc contributes at least `3^{-s}` to the rooted energy of a particle `i`
of the arc. This gives `M_J - 1 ≤ 3^s E_i` pointwise.
-/

@[expose] public section

noncomputable section

open MeasureTheory Finset Set ProbabilityTheory
open scoped ENNReal

attribute [local instance] Classical.propDecidable

namespace Riesz1

variable {N : ℕ+}

/-- The circular norm of a real is at most its absolute value. -/
theorem norm_coe_le_abs' (x : ℝ) : ‖(x : AddCircle (N : ℝ))‖ ≤ |x| := by
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  rw [AddCircle.norm_eq, inv_mul_eq_div]
  have e : x - round (x / (N : ℝ)) * (N : ℝ) = (N : ℝ) * (x / (N : ℝ) - round (x / (N : ℝ))) := by
    field_simp
  rw [e, abs_mul, abs_of_pos hN]
  have h := round_le (x / (N : ℝ)) 0
  simp only [Int.cast_zero, sub_zero] at h
  calc (N : ℝ) * |x / (N : ℝ) - round (x / (N : ℝ))| ≤ (N : ℝ) * |x / (N : ℝ)| :=
        mul_le_mul_of_nonneg_left (by simpa using h) hN.le
    _ = |x| := by
        rw [abs_div, abs_of_pos hN]
        field_simp

/-- Two particles of a microscopic arc of length `r` are at circular distance at most `r`. -/
theorem dist_loopPos_le_of_mem {a r : ℝ} (X : Configuration N) (i j : Fin (N : ℕ))
    (hi : loopPos X i ∈ microArc N a r) (hj : loopPos X j ∈ microArc N a r) :
    dist (loopPos X i) (loopPos X j) ≤ r := by
  obtain ⟨n, hn1, hn2⟩ := (coe_mem_microArc_iff a r ((N : ℝ) * X.val i)).mp hi
  obtain ⟨n', hn1', hn2'⟩ := (coe_mem_microArc_iff a r ((N : ℝ) * X.val j)).mp hj
  have eq_i : loopPos X i = ((((N : ℝ) * X.val i + n * N) : ℝ) : AddCircle (N : ℝ)) := by
    unfold loopPos
    exact (coe_eq_coe_iff_int _ _).mpr ⟨-n, by push_cast; ring⟩
  have eq_j : loopPos X j = ((((N : ℝ) * X.val j + n' * N) : ℝ) : AddCircle (N : ℝ)) := by
    unfold loopPos
    exact (coe_eq_coe_iff_int _ _).mpr ⟨-n', by push_cast; ring⟩
  rw [eq_i, eq_j, dist_eq_norm, ← AddCircle.coe_sub]
  refine (norm_coe_le_abs' _).trans ?_
  exact (abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩).le

/-- Distinct particles are at positive circular distance. -/
theorem dist_loopPos_pos (X : Configuration N) (i j : Fin (N : ℕ)) (hji : j ≠ i) :
    0 < dist (loopPos X i) (loopPos X j) := by
  set k := rootedIndex i j with hk_def
  have hk1 : 0 < k := Nat.pos_of_ne_zero (rootedIndex_ne_zero i j hji)
  have hkN : k < (N : ℕ) := rootedIndex_lt i j
  have hS := blockLength_pos X (i : ℕ) hk1
  have hS' := blockLength_pos X ((i : ℕ) + k) (show 0 < (N : ℕ) - k by omega)
  have hcomp := blockLength_complement X (i : ℕ) (show k ≤ (N : ℕ) by omega)
  have hj : loopPos X j = loopPos X ⟨((i : ℕ) + k) % (N : ℕ), Nat.mod_lt _ N.pos⟩ := by
    congr 1
    exact (Fin.ext (add_rootedIndex_mod i j).symm)
  have hSlt : blockLength X (i : ℕ) k < (N : ℝ) := by
    rw [hcomp] at hS'
    linarith
  rw [hj, dist_loopPos_eq_block, norm_coe_block hS hSlt]
  exact lt_min hS (by rw [hcomp] at hS'; linarith)

/-- A nonzero distance `d ≤ 3` gives `1 ≤ 3^s d^{-s}`. -/
theorem one_le_three_rpow_mul_inv {s d : ℝ} (hs : 0 < s) (hd0 : 0 < d) (hd3 : d ≤ 3) :
    1 ≤ (3 : ℝ) ^ s * d ^ (-s) := by
  have h1 : (3 : ℝ) ^ (-s) ≤ d ^ (-s) :=
    Real.rpow_le_rpow_of_nonpos hd0 hd3 (by linarith)
  have h2 : (3 : ℝ) ^ s * (3 : ℝ) ^ (-s) = 1 := by
    rw [← Real.rpow_add (by norm_num)]
    simp
  calc (1 : ℝ) = (3 : ℝ) ^ s * (3 : ℝ) ^ (-s) := h2.symm
    _ ≤ (3 : ℝ) ^ s * d ^ (-s) := mul_le_mul_of_nonneg_left h1 (by positivity)

/-- **Count against rooted energy.** For an arc of length `r ≤ 3` and a particle `i` of the arc,
`M_J - 1 ≤ 3^s E_i`. -/
theorem loopCount_sub_one_le_rootedEnergy {a r : ℝ} (hr3 : r ≤ 3) {s : ℝ} (hs : 0 < s)
    (X : Configuration N) (i : Fin (N : ℕ)) (hi : loopPos X i ∈ microArc N a r) :
    loopCount a r X - 1 ≤ (3 : ℝ) ^ s * rootedEnergy s X i := by
  set P : Finset (Fin (N : ℕ)) := univ.filter (fun j => loopPos X j ∈ microArc N a r) with hP
  set Q : Finset (Fin (N : ℕ)) :=
    univ.filter (fun j => j ≠ i ∧ dist (loopPos X i) (loopPos X j) ≤ 3) with hQ
  have hiP : i ∈ P := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
  have hcount : loopCount a r X = ((P.erase i).card : ℝ) + 1 := by
    have h1 : loopCount a r X = (P.card : ℝ) := by
      unfold loopCount
      rw [Finset.sum_boole]
    rw [h1]
    exact_mod_cast (Finset.card_erase_add_one hiP).symm
  have hsub : P.erase i ⊆ Q := by
    intro j hj
    obtain ⟨hji, hjP⟩ := Finset.mem_erase.mp hj
    rw [hP, Finset.mem_filter] at hjP
    rw [hQ, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, hji, ?_⟩
    exact (dist_loopPos_le_of_mem X i j hi hjP.2).trans hr3
  have hterm : ∀ j ∈ P.erase i, (1 : ℝ) ≤ (3 : ℝ) ^ s * dist (loopPos X i) (loopPos X j) ^ (-s) := by
    intro j hj
    obtain ⟨hji, hjP⟩ := Finset.mem_erase.mp hj
    rw [hP, Finset.mem_filter] at hjP
    have hd3 : dist (loopPos X i) (loopPos X j) ≤ 3 :=
      (dist_loopPos_le_of_mem X i j hi hjP.2).trans hr3
    have hdpos : 0 < dist (loopPos X i) (loopPos X j) := dist_loopPos_pos X i j hji
    exact one_le_three_rpow_mul_inv hs hdpos hd3
  have hnn : ∀ j ∈ Q, 0 ≤ (3 : ℝ) ^ s * dist (loopPos X i) (loopPos X j) ^ (-s) := fun j _ =>
    mul_nonneg (by positivity) (Real.rpow_nonneg dist_nonneg _)
  calc loopCount a r X - 1 = ∑ _j ∈ P.erase i, (1 : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one, hcount]
        ring
    _ ≤ ∑ j ∈ P.erase i, (3 : ℝ) ^ s * dist (loopPos X i) (loopPos X j) ^ (-s) :=
        Finset.sum_le_sum hterm
    _ ≤ ∑ j ∈ Q, (3 : ℝ) ^ s * dist (loopPos X i) (loopPos X j) ^ (-s) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j hj _ => hnn j hj)
    _ = (3 : ℝ) ^ s * rootedEnergy s X i := by
        rw [rootedEnergy, Finset.mul_sum]

/-! ### A block majorant of the rooted energy -/

/-- The block sum `∑_{1 ≤ k < N} (q(S_{i,k}) + q(S_{i+k,N-k}))` of the near kernel over the blocks
from the particle `i`. It majorises the rooted energy, and it is a function of the block lengths
only, so that rotation averaging applies to it. -/
def blockSumEnergy (s : ℝ) {N : ℕ+} (X : Configuration N) (i : Fin (N : ℕ)) : ℝ :=
  ∑ k ∈ Finset.Ico 1 (N : ℕ),
    (nearKernel s (blockLength X (i : ℕ) k) +
      nearKernel s (blockLength X ((i : ℕ) + k) ((N : ℕ) - k)))

theorem blockSumEnergy_nonneg (s : ℝ) {N : ℕ+} (X : Configuration N) (i : Fin (N : ℕ)) :
    0 ≤ blockSumEnergy s X i := by
  unfold blockSumEnergy
  refine Finset.sum_nonneg (fun k hk => ?_)
  rw [Finset.mem_Ico] at hk
  exact add_nonneg (nearKernel_block_nonneg s X _ (by omega))
    (nearKernel_block_nonneg s X _ (by omega))

theorem rootedEnergy_le_blockSumEnergy (s : ℝ) {N : ℕ+} (X : Configuration N) (i : Fin (N : ℕ)) :
    rootedEnergy s X i ≤ blockSumEnergy s X i :=
  rootedEnergy_le_sum s X i

theorem measurable_blockSumEnergy (s : ℝ) {N : ℕ+} (i : Fin (N : ℕ)) :
    Measurable (fun X : Configuration N => blockSumEnergy s X i) := by
  unfold blockSumEnergy
  refine Finset.measurable_sum _ (fun k _ => ?_)
  exact ((measurable_nearKernel s).comp (measurable_blockLength _ _)).add
    ((measurable_nearKernel s).comp (measurable_blockLength _ _))

/-- **Moments of the block majorant**, uniform in `N`, the label and `hPL`. -/
theorem blockSumEnergy_eLpNorm (P : Parameters) {s : ℝ} (hs : 0 < s) {p : ℝ} (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (_hPL : External.PrekopaLeindler) (N : ℕ+) (i : Fin (N : ℕ)),
      eLpNorm (fun X : Configuration N => blockSumEnergy s X i) (ENNReal.ofReal p)
        (gibbsMeasure P N) ≤ ENNReal.ofReal C := by
  set m : ℕ := ⌈p⌉₊ with hm_def
  have hm1 : 1 ≤ m := by
    have : (1 : ℝ) ≤ m := hp.trans (Nat.le_ceil p)
    exact_mod_cast this
  have hpm : p ≤ (m : ℝ) := Nat.le_ceil p
  obtain ⟨K0, hK0, hblock⟩ := nearKernel_block_eLpNorm P hs hm1
  set Z : ℝ := ∑' n : ℕ, (n : ℝ) ^ (-(s + 2)) with hZ_def
  have hsum := summable_rpow_neg_two_add hs
  have hZnn : 0 ≤ Z := tsum_nonneg (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _)
  refine ⟨2 * K0 * (Z + 1), by positivity, ?_⟩
  intro hPL N i
  have hprob : IsProbabilityMeasure (gibbsMeasure P N) := (modelWellDefined P N).2.2
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal m := by
    rw [ENNReal.one_le_ofReal]
    exact_mod_cast hm1
  have hsum_k : ∑ k ∈ Finset.Ico 1 (N : ℕ), ((k : ℕ) : ℝ) ^ (-(s + 2)) ≤ Z := by
    have h := sum_image_le_tsum (s := Finset.Ico 1 (N : ℕ)) (g := fun k => k)
      (fun _ _ _ _ h => h) (φ := fun n : ℕ => (n : ℝ) ^ (-(s + 2)))
      (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _) hsum
    exact h
  have hsum_N : ∑ k ∈ Finset.Ico 1 (N : ℕ), (((N : ℕ) - k : ℕ) : ℝ) ^ (-(s + 2)) ≤ Z := by
    have h := sum_image_le_tsum (s := Finset.Ico 1 (N : ℕ)) (g := fun k => (N : ℕ) - k)
      (fun a ha b hb h => by
        rw [Finset.mem_coe, Finset.mem_Ico] at ha hb
        simp only at h
        omega)
      (φ := fun n : ℕ => (n : ℝ) ^ (-(s + 2)))
      (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _) hsum
    exact h
  have hmeas := measurable_blockSumEnergy s (N := N) i
  calc eLpNorm (fun X : Configuration N => blockSumEnergy s X i) (ENNReal.ofReal p)
        (gibbsMeasure P N)
      ≤ eLpNorm (fun X : Configuration N => blockSumEnergy s X i) (ENNReal.ofReal m)
          (gibbsMeasure P N) := eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal hpm)
    _ = eLpNorm (∑ k ∈ Finset.Ico 1 (N : ℕ), fun X : Configuration N =>
          (nearKernel s (blockLength X (i : ℕ) k) +
            nearKernel s (blockLength X ((i : ℕ) + k) ((N : ℕ) - k)))) (ENNReal.ofReal m)
          (gibbsMeasure P N) := by
        congr 1
        ext X
        simp [blockSumEnergy, Finset.sum_apply]
    _ ≤ ∑ k ∈ Finset.Ico 1 (N : ℕ), eLpNorm (fun X : Configuration N =>
          (nearKernel s (blockLength X (i : ℕ) k) +
            nearKernel s (blockLength X ((i : ℕ) + k) ((N : ℕ) - k)))) (ENNReal.ofReal m)
          (gibbsMeasure P N) := eLpNorm_sum_le hp1
    _ ≤ ∑ k ∈ Finset.Ico 1 (N : ℕ), (ENNReal.ofReal (K0 * ((k : ℕ) : ℝ) ^ (-(s + 2))) +
          ENNReal.ofReal (K0 * (((N : ℕ) - k : ℕ) : ℝ) ^ (-(s + 2)))) := by
        refine Finset.sum_le_sum (fun k hk => ?_)
        rw [Finset.mem_Ico] at hk
        have hk0 : 0 < k := by omega
        have hkN : 0 < (N : ℕ) - k := by omega
        refine (eLpNorm_add_le hp1).trans (add_le_add ?_ ?_)
        · exact hblock hPL N _ _ hk0
        · exact hblock hPL N _ _ hkN
    _ = ENNReal.ofReal (∑ k ∈ Finset.Ico 1 (N : ℕ), (K0 * ((k : ℕ) : ℝ) ^ (-(s + 2)) +
          K0 * (((N : ℕ) - k : ℕ) : ℝ) ^ (-(s + 2)))) := by
        rw [ENNReal.ofReal_sum_of_nonneg]
        · refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [ENNReal.ofReal_add]
          · positivity
          · positivity
        · intro k _
          positivity
    _ ≤ ENNReal.ofReal (2 * K0 * (Z + 1)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        have h1 := mul_le_mul_of_nonneg_left hsum_k hK0.le
        have h2 := mul_le_mul_of_nonneg_left hsum_N hK0.le
        nlinarith

/-- An elementary bound `(1 + x)^k ≤ 2^k (1 + x^k)` for `x ≥ 0`. -/
theorem add_one_pow_le_two_pow (x : ℝ) (hx : 0 ≤ x) (k : ℕ) :
    (1 + x) ^ k ≤ 2 ^ k * (1 + x ^ k) := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    simp
  · have h := add_pow_le zero_le_one hx k
    rw [one_pow] at h
    refine h.trans ?_
    gcongr
    · norm_num
    · omega

/-- **Power mean over a finite sum.** For nonnegative terms and `m ≥ 1`,
`(∑ a_i)^m ≤ (card S)^{m-1} ∑ a_i^m`. -/
theorem sum_pow_le_card_pow_mul_sum {ι : Type*} (S : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ S, 0 ≤ a i) {m : ℕ} (hm : 1 ≤ m) :
    (∑ i ∈ S, a i) ^ m ≤ (S.card : ℝ) ^ (m - 1) * ∑ i ∈ S, a i ^ m := by
  rcases Nat.eq_zero_or_pos S.card with hcard | hcard
  · rw [Finset.card_eq_zero.mp hcard]
    rw [Finset.sum_empty, zero_pow (by omega)]
    simp
  set n : ℝ := (S.card : ℝ) with hn_def
  have hnpos : 0 < n := by rw [hn_def]; exact_mod_cast hcard
  have hw1 : ∑ _i ∈ S, (1 / n) = 1 := by
    rw [Finset.sum_const, nsmul_eq_mul, hn_def]
    field_simp
  have key := Real.pow_arith_mean_le_arith_mean_pow S (fun _ => 1 / n) a
    (fun _ _ => by positivity) hw1 ha m
  beta_reduce at key
  have e1 : ∑ i ∈ S, (1 / n) * a i = (∑ i ∈ S, a i) / n := by
    rw [← Finset.mul_sum]
    ring
  have e2 : ∑ i ∈ S, (1 / n) * a i ^ m = (1 / n) * ∑ i ∈ S, a i ^ m := by
    rw [← Finset.mul_sum]
  rw [e1, e2, div_pow, div_le_iff₀ (pow_pos hnpos m)] at key
  calc (∑ i ∈ S, a i) ^ m ≤ (1 / n) * (∑ i ∈ S, a i ^ m) * n ^ m := key
    _ = n ^ (m - 1) * ∑ i ∈ S, a i ^ m := by
        rw [show n ^ m = n ^ (m - 1) * n by
          rw [← pow_succ]
          congr 1
          omega]
        field_simp

/-- **Pointwise domination of the short-arc energy.** For an arc of length `0 < r ≤ 3` and
`m ≥ 1`, the `m`-th power of the sum of the rooted energies of the particles of the arc is at most
the sum of `Ẽ_i^m (1 + 3^s Ẽ_i)^{m-1}` over the particles of the arc, where `Ẽ` is the block
majorant. -/
theorem sum_rootedEnergy_pow_le {a r : ℝ} (hr3 : r ≤ 3) {s : ℝ} (hs : 0 < s) {m : ℕ}
    (hm : 1 ≤ m) (X : Configuration N) :
    (∑ i : Fin (N : ℕ), if loopPos X i ∈ microArc N a r then rootedEnergy s X i else 0) ^ m ≤
      ∑ i : Fin (N : ℕ), if loopPos X i ∈ microArc N a r then
        blockSumEnergy s X i ^ m * (1 + (3 : ℝ) ^ s * blockSumEnergy s X i) ^ (m - 1) else 0 := by
  set P : Finset (Fin (N : ℕ)) := univ.filter (fun j => loopPos X j ∈ microArc N a r) with hP
  have hLHS : (∑ i : Fin (N : ℕ), if loopPos X i ∈ microArc N a r then rootedEnergy s X i else 0) =
      ∑ i ∈ P, rootedEnergy s X i := by
    rw [hP, Finset.sum_filter]
  have hRHS : (∑ i : Fin (N : ℕ), if loopPos X i ∈ microArc N a r then
      blockSumEnergy s X i ^ m * (1 + (3 : ℝ) ^ s * blockSumEnergy s X i) ^ (m - 1) else 0) =
      ∑ i ∈ P, blockSumEnergy s X i ^ m * (1 + (3 : ℝ) ^ s * blockSumEnergy s X i) ^ (m - 1) := by
    rw [hP, Finset.sum_filter]
  rw [hLHS, hRHS]
  have hE0 : ∀ i ∈ P, 0 ≤ rootedEnergy s X i := fun i _ => rootedEnergy_nonneg s X i
  have hcardP : (P.card : ℝ) = loopCount a r X := by
    unfold loopCount
    rw [hP, Finset.sum_boole]
  -- The power mean over the particles of the arc.
  have hpm := sum_pow_le_card_pow_mul_sum P (fun i => rootedEnergy s X i) hE0 hm
  refine hpm.trans ?_
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hiJ : loopPos X i ∈ microArc N a r := (Finset.mem_filter.mp hi).2
  have hcount : (P.card : ℝ) ≤ 1 + (3 : ℝ) ^ s * blockSumEnergy s X i := by
    rw [hcardP]
    have h1 := loopCount_sub_one_le_rootedEnergy hr3 hs X i hiJ
    have h2 : (3 : ℝ) ^ s * rootedEnergy s X i ≤ (3 : ℝ) ^ s * blockSumEnergy s X i :=
      mul_le_mul_of_nonneg_left (rootedEnergy_le_blockSumEnergy s X i) (by positivity)
    linarith
  have hpow : ((P.card : ℕ) : ℝ) ^ (m - 1) ≤ (1 + (3 : ℝ) ^ s * blockSumEnergy s X i) ^ (m - 1) :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hcount _
  have hEB : rootedEnergy s X i ^ m ≤ blockSumEnergy s X i ^ m :=
    pow_le_pow_left₀ (rootedEnergy_nonneg s X i) (rootedEnergy_le_blockSumEnergy s X i) m
  calc ((P.card : ℝ) ^ (m - 1)) * rootedEnergy s X i ^ m
      ≤ (1 + (3 : ℝ) ^ s * blockSumEnergy s X i) ^ (m - 1) * blockSumEnergy s X i ^ m :=
        mul_le_mul hpow hEB (pow_nonneg (rootedEnergy_nonneg s X i) m)
          (pow_nonneg (add_nonneg zero_le_one (mul_nonneg (by positivity)
            (blockSumEnergy_nonneg s X i))) _)
    _ = blockSumEnergy s X i ^ m * (1 + (3 : ℝ) ^ s * blockSumEnergy s X i) ^ (m - 1) := by ring

/-! ### The block majorant as a function of the gap vector -/

/-- A block length is the sum of the gap-vector entries of its residues. -/
theorem blockLength_eq_gapVector (X : Configuration N) (j : ℤ) (L : ℕ) :
    blockLength X j L = ∑ r ∈ Finset.range L, gapVector X (residueFin N (j + (r : ℤ))) := by
  rw [blockLength_eq_sum]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  unfold gapVector
  exact gap_eq_residueFin X _

/-- The block majorant, written as a function of the gap vector `γ`. -/
def blockSumGap (s : ℝ) (N : ℕ+) (i : Fin (N : ℕ)) (γ : Fin (N : ℕ) → ℝ) : ℝ :=
  ∑ k ∈ Finset.Ico 1 (N : ℕ),
    (nearKernel s (∑ r ∈ Finset.range k, γ (residueFin N ((i : ℕ) + (r : ℤ)))) +
      nearKernel s (∑ r ∈ Finset.range ((N : ℕ) - k),
        γ (residueFin N (((i : ℕ) + (k : ℤ)) + (r : ℤ)))))

theorem blockSumEnergy_eq_gap (s : ℝ) (X : Configuration N) (i : Fin (N : ℕ)) :
    blockSumEnergy s X i = blockSumGap s N i (gapVector X) := by
  unfold blockSumEnergy blockSumGap
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [blockLength_eq_gapVector, blockLength_eq_gapVector]

theorem measurable_blockSumGap (s : ℝ) (N : ℕ+) (i : Fin (N : ℕ)) :
    Measurable (blockSumGap s N i) := by
  unfold blockSumGap
  refine Finset.measurable_sum _ (fun k _ => ?_)
  refine Measurable.add ?_ ?_
  · exact (measurable_nearKernel s).comp (Finset.measurable_sum _ (fun r _ => measurable_pi_apply _))
  · exact (measurable_nearKernel s).comp (Finset.measurable_sum _ (fun r _ => measurable_pi_apply _))

/-- **Rotation averaging against a function of the gaps.** The rotation of particle `i` is
independent of the gap vector. -/
theorem lintegral_rotation_mul_gapFun (P : Parameters) (N : ℕ+) (i : ℤ) (x0 : UnitAddCircle)
    (ℓ : ℝ) (Φ : (Fin (N : ℕ) → ℝ) → ℝ≥0∞) (hΦ : Measurable Φ) :
    (∫⁻ X : Configuration N, (Metric.closedBall x0 ℓ).indicator 1 (cyclicLift X i : UnitAddCircle) *
      Φ (gapVector X) ∂gibbsMeasure P N) =
      volume (Metric.closedBall x0 ℓ) * ∫⁻ X : Configuration N, Φ (gapVector X)
        ∂gibbsMeasure P N := by
  have hF : Measurable ((Metric.closedBall x0 ℓ).indicator (1 : UnitAddCircle → ℝ≥0∞)) :=
    measurable_const.indicator measurableSet_closedBall
  have hI := (indepFun_cyclicLift_gapVector P N i).comp hF hΦ
  have hcyc : Measurable (fun X : Configuration N => (cyclicLift X i : UnitAddCircle)) :=
    measurable_coe_circle.comp (measurable_cyclicLift i)
  have he := lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun''
    (hF.comp hcyc).aemeasurable ((hΦ.comp (measurable_gapVector N))).aemeasurable hI
  simp only [Function.comp_apply] at he
  rw [he]
  congr 1
  rw [← lintegral_indicator_one measurableSet_closedBall]
  refine (lintegral_map hF hcyc).symm.trans ?_
  rw [map_cyclicLift_gibbsMeasure P N i]

/-- **Moment of the short-arc integrand.** The integral of `Ẽ^m (1 + 3^s Ẽ)^{m-1}` is bounded
uniformly in `N`, the label and `hPL`. -/
theorem lintegral_blockSum_power_le (P : Parameters) {s : ℝ} (hs : 0 < s) {m : ℕ} (hm : 1 ≤ m) :
    ∃ KG : ℝ, 0 < KG ∧ ∀ (_hPL : External.PrekopaLeindler) (N : ℕ+) (i : Fin (N : ℕ)),
      ∫⁻ X : Configuration N, ENNReal.ofReal (blockSumEnergy s X i ^ m *
        (1 + (3 : ℝ) ^ s * blockSumEnergy s X i) ^ (m - 1)) ∂gibbsMeasure P N ≤
        ENNReal.ofReal KG := by
  obtain ⟨C1, hC1, h1⟩ := blockSumEnergy_eLpNorm P hs (p := (m : ℝ)) (by exact_mod_cast hm)
  obtain ⟨C2, hC2, h2⟩ := blockSumEnergy_eLpNorm P hs (p := ((2 * m - 1 : ℕ) : ℝ))
    (by exact_mod_cast (show 1 ≤ 2 * m - 1 by omega))
  set c : ℝ := (3 : ℝ) ^ s with hc_def
  have hc : 0 ≤ c := by positivity
  refine ⟨2 ^ (m - 1) * (C1 ^ m + c ^ (m - 1) * C2 ^ (2 * m - 1)), by positivity, ?_⟩
  intro hPL N i
  have hprob : IsProbabilityMeasure (gibbsMeasure P N) := (modelWellDefined P N).2.2
  have hmeasE := measurable_blockSumEnergy s (N := N) i
  have hE0 : ∀ X : Configuration N, 0 ≤ blockSumEnergy s X i := fun X => blockSumEnergy_nonneg s X i
  have hM1 : ∫⁻ X : Configuration N, ENNReal.ofReal (blockSumEnergy s X i ^ m)
      ∂gibbsMeasure P N ≤ ENNReal.ofReal (C1 ^ m) := by
    have h := lintegral_pow_le_of_eLpNorm_le (μ := gibbsMeasure P N) hmeasE hm hC1.le
      (h1 hPL N i)
    simpa only [abs_of_nonneg (hE0 _)] using h
  have hM2 : ∫⁻ X : Configuration N, ENNReal.ofReal (blockSumEnergy s X i ^ (2 * m - 1))
      ∂gibbsMeasure P N ≤ ENNReal.ofReal (C2 ^ (2 * m - 1)) := by
    have h := lintegral_pow_le_of_eLpNorm_le (μ := gibbsMeasure P N) hmeasE
      (show 1 ≤ 2 * m - 1 by omega) hC2.le (h2 hPL N i)
    simpa only [abs_of_nonneg (hE0 _)] using h
  have hpt : ∀ X : Configuration N, ENNReal.ofReal (blockSumEnergy s X i ^ m *
      (1 + c * blockSumEnergy s X i) ^ (m - 1)) ≤ ENNReal.ofReal (2 ^ (m - 1)) *
        (ENNReal.ofReal (blockSumEnergy s X i ^ m) + ENNReal.ofReal (c ^ (m - 1)) *
          ENNReal.ofReal (blockSumEnergy s X i ^ (2 * m - 1))) := by
    intro X
    set E := blockSumEnergy s X i with hEdef
    have hE : 0 ≤ E := hE0 X
    have hb : (1 + c * E) ^ (m - 1) ≤ 2 ^ (m - 1) * (1 + (c * E) ^ (m - 1)) :=
      add_one_pow_le_two_pow (c * E) (mul_nonneg hc hE) (m - 1)
    have hq : E ^ m * (1 + c * E) ^ (m - 1) ≤
        2 ^ (m - 1) * (E ^ m + c ^ (m - 1) * E ^ (2 * m - 1)) := by
      have h3 : E ^ m * (2 ^ (m - 1) * (1 + (c * E) ^ (m - 1))) =
          2 ^ (m - 1) * (E ^ m + c ^ (m - 1) * E ^ (2 * m - 1)) := by
        rw [mul_pow, show 2 * m - 1 = m + (m - 1) by omega, pow_add]
        ring
      rw [← h3]
      exact mul_le_mul_of_nonneg_left hb (pow_nonneg hE m)
    calc ENNReal.ofReal (E ^ m * (1 + c * E) ^ (m - 1))
        ≤ ENNReal.ofReal (2 ^ (m - 1) * (E ^ m + c ^ (m - 1) * E ^ (2 * m - 1))) :=
          ENNReal.ofReal_le_ofReal hq
      _ = ENNReal.ofReal (2 ^ (m - 1)) * (ENNReal.ofReal (E ^ m) +
            ENNReal.ofReal (c ^ (m - 1)) * ENNReal.ofReal (E ^ (2 * m - 1))) := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_add (pow_nonneg hE m)
            (mul_nonneg (pow_nonneg hc _) (pow_nonneg hE _)), ENNReal.ofReal_mul (pow_nonneg hc _)]
  calc ∫⁻ X : Configuration N, ENNReal.ofReal (blockSumEnergy s X i ^ m *
        (1 + c * blockSumEnergy s X i) ^ (m - 1)) ∂gibbsMeasure P N
      ≤ ∫⁻ X : Configuration N, ENNReal.ofReal (2 ^ (m - 1)) * (ENNReal.ofReal
          (blockSumEnergy s X i ^ m) + ENNReal.ofReal (c ^ (m - 1)) *
            ENNReal.ofReal (blockSumEnergy s X i ^ (2 * m - 1))) ∂gibbsMeasure P N :=
        lintegral_mono hpt
    _ = ENNReal.ofReal (2 ^ (m - 1)) * (∫⁻ X : Configuration N,
          ENNReal.ofReal (blockSumEnergy s X i ^ m) ∂gibbsMeasure P N +
          ENNReal.ofReal (c ^ (m - 1)) * ∫⁻ X : Configuration N,
            ENNReal.ofReal (blockSumEnergy s X i ^ (2 * m - 1)) ∂gibbsMeasure P N) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_add_left ((hmeasE.pow_const _).ennreal_ofReal),
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal (2 ^ (m - 1)) * (ENNReal.ofReal (C1 ^ m) +
          ENNReal.ofReal (c ^ (m - 1)) * ENNReal.ofReal (C2 ^ (2 * m - 1))) := by
        gcongr
    _ = ENNReal.ofReal (2 ^ (m - 1) * (C1 ^ m + c ^ (m - 1) * C2 ^ (2 * m - 1))) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_mul (by positivity)]

/-- **Expectation of the short-arc sum.** The integral of the power of the block majorant summed
over the particles of the arc is at most `r` times a constant, by rotation averaging. -/
theorem lintegral_sum_short_arc_le (P : Parameters) {s : ℝ} (hs : 0 < s) {m : ℕ} (hm : 1 ≤ m) :
    ∃ K : ℝ, 0 < K ∧ ∀ (_hPL : External.PrekopaLeindler) (N : ℕ+) (a r : ℝ), 0 < r → r ≤ N →
      ∫⁻ X : Configuration N, ENNReal.ofReal (∑ i : Fin (N : ℕ),
        if loopPos X i ∈ microArc N a r then blockSumEnergy s X i ^ m *
          (1 + (3 : ℝ) ^ s * blockSumEnergy s X i) ^ (m - 1) else 0) ∂gibbsMeasure P N ≤
        ENNReal.ofReal (r * K) := by
  obtain ⟨KG, hKG, hG⟩ := lintegral_blockSum_power_le P hs hm
  refine ⟨KG, hKG, fun hPL N a r hr hrN => ?_⟩
  have hprob : IsProbabilityMeasure (gibbsMeasure P N) := (modelWellDefined P N).2.2
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  set c : ℝ := (3 : ℝ) ^ s with hc_def
  have hGnn : ∀ (i : Fin (N : ℕ)) (X : Configuration N), 0 ≤ blockSumEnergy s X i ^ m *
      (1 + c * blockSumEnergy s X i) ^ (m - 1) := fun i X =>
    mul_nonneg (pow_nonneg (blockSumEnergy_nonneg s X i) m)
      (pow_nonneg (add_nonneg zero_le_one (mul_nonneg (by positivity)
        (blockSumEnergy_nonneg s X i))) _)
  have hmeasG : ∀ i : Fin (N : ℕ), Measurable (fun X : Configuration N => blockSumEnergy s X i ^ m *
      (1 + c * blockSumEnergy s X i) ^ (m - 1)) := fun i =>
    ((measurable_blockSumEnergy s i).pow_const m).mul
      ((measurable_const.add (measurable_const.mul (measurable_blockSumEnergy s i))).pow_const _)
  have hmeas_ite : ∀ i : Fin (N : ℕ), Measurable (fun X : Configuration N =>
      ENNReal.ofReal (if loopPos X i ∈ microArc N a r then blockSumEnergy s X i ^ m *
        (1 + c * blockSumEnergy s X i) ^ (m - 1) else 0)) := fun i => by
    refine Measurable.ennreal_ofReal (Measurable.ite ?_ (hmeasG i) measurable_const)
    exact measurable_loopPos i (measurableSet_microArc N a r)
  -- Each particle: rotation averaging of its indicator against its block power.
  have hparticle : ∀ i : Fin (N : ℕ), ∫⁻ X : Configuration N, ENNReal.ofReal
      (if loopPos X i ∈ microArc N a r then blockSumEnergy s X i ^ m *
        (1 + c * blockSumEnergy s X i) ^ (m - 1) else 0) ∂gibbsMeasure P N ≤
      ENNReal.ofReal (r / (N : ℝ)) * ENNReal.ofReal KG := by
    intro i
    set Φ : (Fin (N : ℕ) → ℝ) → ℝ≥0∞ := fun γ => ENNReal.ofReal (blockSumGap s N i γ ^ m *
      (1 + c * blockSumGap s N i γ) ^ (m - 1)) with hΦ_def
    have hΦm : Measurable Φ := by
      refine Measurable.ennreal_ofReal ?_
      exact ((measurable_blockSumGap s N i).pow_const m).mul
        ((measurable_const.add (measurable_const.mul (measurable_blockSumGap s N i))).pow_const _)
    have hpt : ∀ X : Configuration N, ENNReal.ofReal
        (if loopPos X i ∈ microArc N a r then blockSumEnergy s X i ^ m *
          (1 + c * blockSumEnergy s X i) ^ (m - 1) else 0) ≤
        (Metric.closedBall (arcCentre N a r) (arcRadius N r)).indicator (1 : UnitAddCircle → ℝ≥0∞)
          (cyclicLift X ((i : ℕ) : ℤ) : UnitAddCircle) * Φ (gapVector X) := by
      intro X
      by_cases hm' : loopPos X i ∈ microArc N a r
      · rw [ite_eq_left hm', Set.indicator_of_mem (cyclicLift_mem_closedBall_of_mem hN X i hm'),
          Pi.one_apply, one_mul, hΦ_def, blockSumEnergy_eq_gap]
      · rw [ite_eq_right hm', ENNReal.ofReal_zero]
        exact zero_le
    have hrot := lintegral_rotation_mul_gapFun P N ((i : ℕ) : ℤ) (arcCentre N a r) (arcRadius N r)
      Φ hΦm
    have hΦeq : ∀ X : Configuration N, Φ (gapVector X) = ENNReal.ofReal (blockSumEnergy s X i ^ m *
        (1 + c * blockSumEnergy s X i) ^ (m - 1)) := fun X => by
      rw [hΦ_def, blockSumEnergy_eq_gap]
    calc ∫⁻ X : Configuration N, ENNReal.ofReal
          (if loopPos X i ∈ microArc N a r then blockSumEnergy s X i ^ m *
            (1 + c * blockSumEnergy s X i) ^ (m - 1) else 0) ∂gibbsMeasure P N
        ≤ ∫⁻ X : Configuration N, (Metric.closedBall (arcCentre N a r) (arcRadius N r)).indicator
            (1 : UnitAddCircle → ℝ≥0∞) (cyclicLift X ((i : ℕ) : ℤ) : UnitAddCircle) *
              Φ (gapVector X) ∂gibbsMeasure P N := lintegral_mono hpt
      _ = volume (Metric.closedBall (arcCentre N a r) (arcRadius N r)) *
            ∫⁻ X : Configuration N, Φ (gapVector X) ∂gibbsMeasure P N := hrot
      _ = ENNReal.ofReal (r / (N : ℝ)) * ∫⁻ X : Configuration N, ENNReal.ofReal
            (blockSumEnergy s X i ^ m * (1 + c * blockSumEnergy s X i) ^ (m - 1))
              ∂gibbsMeasure P N := by
          rw [volume_closedBall_arc hr hrN]
          congr 1
          exact lintegral_congr hΦeq
      _ ≤ ENNReal.ofReal (r / (N : ℝ)) * ENNReal.ofReal KG := by
          exact mul_le_mul_of_nonneg_left (hG hPL N i) zero_le
  -- Sum over the particles.
  calc ∫⁻ X : Configuration N, ENNReal.ofReal (∑ i : Fin (N : ℕ),
        if loopPos X i ∈ microArc N a r then blockSumEnergy s X i ^ m *
          (1 + c * blockSumEnergy s X i) ^ (m - 1) else 0) ∂gibbsMeasure P N
      = ∫⁻ X : Configuration N, ∑ i : Fin (N : ℕ), ENNReal.ofReal
          (if loopPos X i ∈ microArc N a r then blockSumEnergy s X i ^ m *
            (1 + c * blockSumEnergy s X i) ^ (m - 1) else 0) ∂gibbsMeasure P N := by
        refine lintegral_congr (fun X => ?_)
        exact ENNReal.ofReal_sum_of_nonneg (fun i _ => by
          split_ifs
          · exact hGnn i X
          · exact le_rfl)
    _ = ∑ i : Fin (N : ℕ), ∫⁻ X : Configuration N, ENNReal.ofReal
          (if loopPos X i ∈ microArc N a r then blockSumEnergy s X i ^ m *
            (1 + c * blockSumEnergy s X i) ^ (m - 1) else 0) ∂gibbsMeasure P N :=
        lintegral_finsetSum _ (fun i _ => hmeas_ite i)
    _ ≤ ∑ i : Fin (N : ℕ), ENNReal.ofReal (r / (N : ℝ)) * ENNReal.ofReal KG :=
        Finset.sum_le_sum (fun i _ => hparticle i)
    _ = ENNReal.ofReal (r * KG) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp

/-- **Short-arc energy**, the moments part of Lemma B.2 (the claim on
`∑_{z_i ∈ J} E_i` for `r ≤ 3`). For every `p ≥ 1` there is `C > 0`, depending only on `β, s, p`,
such that every `N ≥ 2` and every arc of length `0 < r ≤ min(3, N)` satisfy
`‖∑_{z_i ∈ J} E_i‖_{L^p} ≤ C`. -/
theorem shortArc_rootedEnergy_eLpNorm (P : Parameters) {s : ℝ} (hs : 0 < s) {p : ℝ} (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (_hPL : External.PrekopaLeindler) (N : ℕ+), 2 ≤ (N : ℕ) →
      ∀ (a r : ℝ), 0 < r → r ≤ 3 → r ≤ N →
        eLpNorm (fun X : Configuration N => ∑ i : Fin (N : ℕ),
          if loopPos X i ∈ microArc N a r then rootedEnergy s X i else 0) (ENNReal.ofReal p)
          (gibbsMeasure P N) ≤ ENNReal.ofReal C := by
  set m : ℕ := ⌈p⌉₊ with hm_def
  have hm1 : 1 ≤ m := by
    have : (1 : ℝ) ≤ m := hp.trans (Nat.le_ceil p)
    exact_mod_cast this
  have hpm : p ≤ (m : ℝ) := Nat.le_ceil p
  obtain ⟨K, hK, hsum⟩ := lintegral_sum_short_arc_le P hs (m := m) hm1
  refine ⟨(3 * K) ^ ((m : ℝ)⁻¹), by positivity, fun hPL N _hN a r hr hr3 hrN => ?_⟩
  have hprob : IsProbabilityMeasure (gibbsMeasure P N) := (modelWellDefined P N).2.2
  have hZmeas : Measurable (fun X : Configuration N => ∑ i : Fin (N : ℕ),
      if loopPos X i ∈ microArc N a r then rootedEnergy s X i else 0) := by
    refine Finset.measurable_sum _ (fun i _ => ?_)
    exact Measurable.ite (measurable_loopPos i (measurableSet_microArc N a r))
      (measurable_rootedEnergy s i) measurable_const
  have hZ0 : ∀ X : Configuration N, 0 ≤ ∑ i : Fin (N : ℕ),
      if loopPos X i ∈ microArc N a r then rootedEnergy s X i else 0 := fun X =>
    Finset.sum_nonneg (fun i _ => by
      split_ifs
      · exact rootedEnergy_nonneg s X i
      · exact le_rfl)
  have hB_pow : ((3 * K) ^ ((m : ℝ)⁻¹)) ^ m = 3 * K :=
    Real.rpow_inv_natCast_pow (by positivity) (by omega)
  have hint : ∫⁻ X : Configuration N, ENNReal.ofReal (|∑ i : Fin (N : ℕ),
      if loopPos X i ∈ microArc N a r then rootedEnergy s X i else 0| ^ m)
        ∂gibbsMeasure P N ≤ ENNReal.ofReal (((3 * K) ^ ((m : ℝ)⁻¹)) ^ m) := by
    rw [hB_pow]
    calc ∫⁻ X : Configuration N, ENNReal.ofReal (|∑ i : Fin (N : ℕ),
          if loopPos X i ∈ microArc N a r then rootedEnergy s X i else 0| ^ m) ∂gibbsMeasure P N
        ≤ ∫⁻ X : Configuration N, ENNReal.ofReal (∑ i : Fin (N : ℕ),
          if loopPos X i ∈ microArc N a r then blockSumEnergy s X i ^ m *
            (1 + (3 : ℝ) ^ s * blockSumEnergy s X i) ^ (m - 1) else 0) ∂gibbsMeasure P N := by
          refine lintegral_mono (fun X => ENNReal.ofReal_le_ofReal ?_)
          rw [abs_of_nonneg (hZ0 X)]
          exact sum_rootedEnergy_pow_le hr3 hs hm1 X
      _ ≤ ENNReal.ofReal (r * K) := hsum hPL N a r hr hrN
      _ ≤ ENNReal.ofReal (3 * K) := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hr3 hK.le)
  have hE := eLpNorm_le_of_lintegral_pow_le (μ := gibbsMeasure P N) hZmeas hm1
    (by positivity) hint
  calc eLpNorm (fun X : Configuration N => ∑ i : Fin (N : ℕ),
          if loopPos X i ∈ microArc N a r then rootedEnergy s X i else 0) (ENNReal.ofReal p)
        (gibbsMeasure P N)
      ≤ eLpNorm (fun X : Configuration N => ∑ i : Fin (N : ℕ),
          if loopPos X i ∈ microArc N a r then rootedEnergy s X i else 0) (ENNReal.ofReal m)
          (gibbsMeasure P N) := eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal hpm)
    _ ≤ ENNReal.ofReal ((3 * K) ^ ((m : ℝ)⁻¹)) := hE

end Riesz1

end
end
