/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopMomentsDefs
public import Riesz1.ToMathlib.Moments.LpBounds
public import Riesz1.Rigidity.InverseBlocks
public import Riesz1.Rigidity.BlockMoments

/-!
# Moments of the rooted local inverse energy

The moments part of Lemma 5.8, the claim `‖E_i‖_{L^p} ≤ C_{β,s,p}` for the rooted
energy `E_i = ∑_{j ≠ i, dist(z_i, z_j) ≤ 3} dist(z_i, z_j)^{-s}`.

The distance from `z_i` to `z_j` is the norm of the block `S_{i,k} = N (x_{i+k} - x_i)`, where
`k` is the residue of `j - i` modulo `N`. The complementary block has length `N - k`. Each
term is bounded by the kernel `t ↦ t^{-s} 1_{t ≤ 3}` of both blocks. The inverse block moments
of `Riesz1.inverse_blocks_uniform` at order `s + 2` make the sum over `k` converge.
-/

@[expose] public section

noncomputable section

open MeasureTheory Finset Set
open scoped ENNReal

attribute [local instance] Classical.propDecidable

namespace Riesz1

/-- The kernel `t ↦ t^{-s}` restricted to the near range `t ≤ 3`. -/
def nearKernel (s t : ℝ) : ℝ := if t ≤ 3 then t ^ (-s) else 0

theorem nearKernel_nonneg (s : ℝ) {t : ℝ} (ht : 0 < t) : 0 ≤ nearKernel s t := by
  unfold nearKernel
  split_ifs
  · exact Real.rpow_nonneg ht.le _
  · exact le_rfl

theorem measurable_nearKernel (s : ℝ) : Measurable (nearKernel s) := by
  unfold nearKernel
  exact Measurable.ite measurableSet_Iic (measurable_id.pow_const _) measurable_const

/-- For `0 < t ≤ 3`, the `m`-th power of the kernel is at most `9^m t^{-(s+2)m}`. -/
theorem nearKernel_pow_le (s : ℝ) {t : ℝ} (ht : 0 < t) (ht3 : t ≤ 3) (m : ℕ) :
    nearKernel s t ^ m ≤ 9 ^ m * t ^ (-(s + 2) * (m : ℝ)) := by
  unfold nearKernel
  rw [ite_eq_left ht3]
  set u : ℝ := t ^ (-(2 : ℝ)) with hu_def
  have hu : u = (t ^ 2)⁻¹ := by rw [hu_def, Real.rpow_neg ht.le, Real.rpow_two]
  have hu9 : 1 ≤ 9 * u := by
    rw [hu, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    nlinarith
  have hpos : 0 < t ^ (-s) := Real.rpow_pos_of_pos ht _
  have hsplit : t ^ (-(s + 2) * (m : ℝ)) = (t ^ (-s)) ^ m * u ^ m := by
    rw [← Real.rpow_natCast (t ^ (-s)) m, ← Real.rpow_natCast u m, hu_def,
      ← Real.rpow_mul ht.le, ← Real.rpow_mul ht.le, ← Real.rpow_add ht]
    congr 1
    ring
  rw [hsplit]
  have h1 : 1 ≤ (9 * u) ^ m := one_le_pow₀ hu9
  calc (t ^ (-s)) ^ m = (t ^ (-s)) ^ m * 1 := (mul_one _).symm
    _ ≤ (t ^ (-s)) ^ m * (9 * u) ^ m := mul_le_mul_of_nonneg_left h1 (pow_nonneg hpos.le m)
    _ = 9 ^ m * ((t ^ (-s)) ^ m * u ^ m) := by rw [mul_pow]; ring

/-- **Kernel moments of one block.** For `0 < s` and every natural `m ≥ 1` there is `K > 0`
such that for every `N`, every `j : ℤ` and every `L ≥ 1`, the `L^m` norm of the near kernel of
the block `S_{j,L}` is at most `K L^{-(s+2)}`. -/
theorem nearKernel_block_eLpNorm (P : Parameters) {s : ℝ} (hs : 0 < s) {m : ℕ} (hm : 1 ≤ m) :
    ∃ K : ℝ, 0 < K ∧ ∀ (_hPL : External.PrekopaLeindler) (N : ℕ+) (j : ℤ) (L : ℕ), 0 < L →
      eLpNorm (fun X : Configuration N => nearKernel s (blockLength X j L))
        (ENNReal.ofReal m) (gibbsMeasure P N) ≤ ENNReal.ofReal (K * (L : ℝ) ^ (-(s + 2))) := by
  have hp : 0 < (s + 2) * (m : ℝ) := by
    have : (0 : ℝ) < m := by exact_mod_cast hm
    positivity
  obtain ⟨C, hC, hblock⟩ := inverse_blocks_uniform P hp
  set D : ℝ := 9 ^ m * C with hD
  have hDpos : 0 < D := by positivity
  refine ⟨D ^ ((m : ℝ)⁻¹), by positivity, ?_⟩
  intro hPL N j L hL
  let := (modelWellDefined P N).2.2
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hKm : ((D ^ ((m : ℝ)⁻¹)) * (L : ℝ) ^ (-(s + 2))) ^ m =
      D * (L : ℝ) ^ (-((s + 2) * (m : ℝ))) := by
    rw [mul_pow, Real.rpow_inv_natCast_pow hDpos.le (by omega), ← Real.rpow_natCast,
      ← Real.rpow_mul hLr.le]
    congr 2
    ring
  apply eLpNorm_le_of_lintegral_pow_le (f := fun X : Configuration N =>
    nearKernel s (blockLength X j L)) (μ := gibbsMeasure P N) (hf := ?_) (hm := hm)
  · exact (mul_nonneg (by positivity) (Real.rpow_nonneg hLr.le _))
  · rw [hKm]
    have hpt : ∀ X : Configuration N, ENNReal.ofReal (|nearKernel s (blockLength X j L)| ^ m) ≤
        ENNReal.ofReal (9 ^ m * blockLength X j L ^ (-((s + 2) * (m : ℝ)))) := by
      intro X
      apply ENNReal.ofReal_le_ofReal
      have hS := blockLength_pos X j hL
      rw [abs_of_nonneg (nearKernel_nonneg s hS)]
      by_cases h3 : blockLength X j L ≤ 3
      · have h := nearKernel_pow_le s hS h3 m
        rw [neg_mul] at h
        exact h
      · unfold nearKernel
        rw [ite_eq_right h3, zero_pow (by omega)]
        positivity
    obtain ⟨-, hint⟩ := hblock hPL N j L hL
    calc ∫⁻ X, ENNReal.ofReal (|nearKernel s (blockLength X j L)| ^ m) ∂gibbsMeasure P N
        ≤ ∫⁻ X, ENNReal.ofReal (9 ^ m * blockLength X j L ^ (-((s + 2) * (m : ℝ))))
            ∂gibbsMeasure P N := lintegral_mono hpt
      _ = ENNReal.ofReal (9 ^ m) * ∫⁻ X, ENNReal.ofReal (blockLength X j L ^
            (-((s + 2) * (m : ℝ)))) ∂gibbsMeasure P N := by
          simp_rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 9 ^ m)]
          exact lintegral_const_mul _ ((measurable_blockLength j L).pow_const _).ennreal_ofReal
      _ ≤ ENNReal.ofReal (9 ^ m) * ENNReal.ofReal (C * (L : ℝ) ^ (-((s + 2) * (m : ℝ)))) :=
          mul_le_mul_of_nonneg_left hint zero_le
      _ = ENNReal.ofReal (D * (L : ℝ) ^ (-((s + 2) * (m : ℝ)))) := by
          rw [← ENNReal.ofReal_mul (by positivity), hD]
          congr 1
          ring
  · exact (measurable_nearKernel s).comp (measurable_blockLength j L)

/-! ### Indexing the particles seen from `i` -/

/-- The residue of `2N` reduction: for `x < 2N`, `x % N` is `x` or `x - N`. -/
theorem mod_eq_of_lt_two_mul {N : ℕ} (x : ℕ) (hx : x < 2 * N) :
    x % N = if x < N then x else x - N := by
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · rw [Nat.mod_eq_sub_mod (by omega)]
    exact Nat.mod_eq_of_lt (by omega)

/-- The block index of the particle `j` seen from the particle `i`: the residue of `j - i`
modulo `N`. For `j ≠ i` it lies in `{1, …, N - 1}`. -/
def rootedIndex {N : ℕ+} (i j : Fin (N : ℕ)) : ℕ := ((j : ℕ) + (N : ℕ) - (i : ℕ)) % (N : ℕ)

theorem rootedIndex_lt {N : ℕ+} (i j : Fin (N : ℕ)) : rootedIndex i j < (N : ℕ) :=
  Nat.mod_lt _ N.pos

theorem add_rootedIndex_mod {N : ℕ+} (i j : Fin (N : ℕ)) :
    ((i : ℕ) + rootedIndex i j) % (N : ℕ) = j := by
  have hi := i.isLt
  have hj := j.isLt
  unfold rootedIndex
  rw [mod_eq_of_lt_two_mul ((j : ℕ) + (N : ℕ) - (i : ℕ)) (by omega)]
  split_ifs with h
  · rw [show (i : ℕ) + ((j : ℕ) + (N : ℕ) - (i : ℕ)) = (j : ℕ) + (N : ℕ) by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt j.isLt]
  · rw [show (i : ℕ) + ((j : ℕ) + (N : ℕ) - (i : ℕ) - N) = (j : ℕ) by omega, Nat.mod_eq_of_lt j.isLt]

theorem rootedIndex_injective {N : ℕ+} (i : Fin (N : ℕ)) :
    Function.Injective (rootedIndex (N := N) i) := by
  intro j j' h
  have hi := i.isLt
  have hj := j.isLt
  have hj' := j'.isLt
  unfold rootedIndex at h
  rw [mod_eq_of_lt_two_mul ((j : ℕ) + (N : ℕ) - (i : ℕ)) (by omega),
    mod_eq_of_lt_two_mul ((j' : ℕ) + (N : ℕ) - (i : ℕ)) (by omega)] at h
  apply Fin.ext
  split_ifs at h <;> omega

theorem rootedIndex_ne_zero {N : ℕ+} (i j : Fin (N : ℕ)) (hji : j ≠ i) :
    rootedIndex i j ≠ 0 := by
  intro h
  have hmod := add_rootedIndex_mod i j
  rw [h, add_zero, Nat.mod_eq_of_lt i.isLt] at hmod
  exact hji (Fin.ext hmod.symm)

/-- The complementary block: the block of length `N - k` from `i + k` has length `N - S_{i,k}`. -/
theorem blockLength_complement {N : ℕ+} (X : Configuration N) (i : ℤ) {k : ℕ} (hk : k ≤ (N : ℕ)) :
    blockLength X (i + k) ((N : ℕ) - k) = (N : ℝ) - blockLength X i k := by
  unfold blockLength
  have h : i + (k : ℤ) + (((N : ℕ) - k : ℕ) : ℤ) = i + ((N : ℕ) : ℤ) := by
    push_cast [Nat.cast_sub hk]
    ring
  rw [h, cyclicLift_add_N]
  ring

/-- Summing a nonnegative function over an injective image is bounded by the full series. -/
theorem sum_image_le_tsum {s : Finset ℕ} {g : ℕ → ℕ} (hg : Set.InjOn g s) {φ : ℕ → ℝ}
    (hφ : ∀ n, 0 ≤ φ n) (hsum : Summable φ) :
    ∑ k ∈ s, φ (g k) ≤ ∑' n, φ n := by
  rw [← Finset.sum_image hg]
  exact hsum.sum_le_tsum _ (fun n _ => hφ n)

/-! ### Pointwise bound of the rooted energy -/

theorem nearKernel_block_nonneg {N : ℕ+} (s : ℝ) (X : Configuration N) (j : ℤ) {L : ℕ} (hL : 0 < L) :
    0 ≤ nearKernel s (blockLength X j L) :=
  nearKernel_nonneg s (blockLength_pos X j hL)

/-- One term of the rooted energy is bounded by the kernels of the two complementary blocks. -/
theorem rootedTerm_le {N : ℕ+} (s : ℝ) (X : Configuration N) (i j : Fin (N : ℕ)) (hji : j ≠ i)
    (hd : dist (loopPos X i) (loopPos X j) ≤ 3) :
    dist (loopPos X i) (loopPos X j) ^ (-s) ≤
      nearKernel s (blockLength X (i : ℕ) (rootedIndex i j)) +
        nearKernel s (blockLength X ((i : ℕ) + rootedIndex i j) ((N : ℕ) - rootedIndex i j)) := by
  set k := rootedIndex i j with hk_def
  have hk1 : 0 < k := Nat.pos_of_ne_zero (rootedIndex_ne_zero i j hji)
  have hkN : k < (N : ℕ) := rootedIndex_lt i j
  have hS := blockLength_pos X (i : ℕ) hk1
  have hS' := blockLength_pos X ((i : ℕ) + k) (show 0 < (N : ℕ) - k by omega)
  have hcomp := blockLength_complement X (i : ℕ) (show k ≤ (N : ℕ) by omega)
  have hj : loopPos X j = loopPos X ⟨((i : ℕ) + k) % (N : ℕ), Nat.mod_lt _ N.pos⟩ := by
    congr 1
    exact (Fin.ext (add_rootedIndex_mod i j).symm)
  have hdist : dist (loopPos X i) (loopPos X j) = ‖((blockLength X (i : ℕ) k : ℝ) :
      AddCircle (N : ℝ))‖ := by
    rw [hj, dist_loopPos_eq_block]
  have hSlt : blockLength X (i : ℕ) k < (N : ℝ) := by
    rw [hcomp] at hS'
    linarith
  rw [hdist, norm_coe_block hS hSlt] at hd ⊢
  rw [hcomp]
  rcases le_total (blockLength X (i : ℕ) k) ((N : ℝ) - blockLength X (i : ℕ) k) with h | h
  · rw [min_eq_left h] at hd ⊢
    have hnear : nearKernel s (blockLength X (i : ℕ) k) = blockLength X (i : ℕ) k ^ (-s) :=
      ite_eq_left hd
    rw [hnear]
    exact le_add_of_nonneg_right (nearKernel_nonneg s (by rw [hcomp] at hS'; exact hS'))
  · rw [min_eq_right h] at hd ⊢
    have hnear : nearKernel s ((N : ℝ) - blockLength X (i : ℕ) k) =
        ((N : ℝ) - blockLength X (i : ℕ) k) ^ (-s) := ite_eq_left hd
    rw [hnear]
    exact le_add_of_nonneg_left (nearKernel_nonneg s hS)

/-! ### The rooted energy as a sum over block indices -/

theorem rootedEnergy_nonneg (s : ℝ) {N : ℕ+} (X : Configuration N) (i : Fin (N : ℕ)) :
    0 ≤ rootedEnergy s X i :=
  Finset.sum_nonneg (fun _ _ => Real.rpow_nonneg dist_nonneg _)

/-- **Rooted energy by blocks.** The rooted energy is at most the sum, over the block indices
`1 ≤ k < N`, of the near kernels of the block `S_{i,k}` and of its complement. -/
theorem rootedEnergy_le_sum {N : ℕ+} (s : ℝ) (X : Configuration N) (i : Fin (N : ℕ)) :
    rootedEnergy s X i ≤ ∑ k ∈ Finset.Ico 1 (N : ℕ),
      (nearKernel s (blockLength X (i : ℕ) k) +
        nearKernel s (blockLength X ((i : ℕ) + k) ((N : ℕ) - k))) := by
  unfold rootedEnergy
  have hnn : ∀ k ∈ Finset.Ico 1 (N : ℕ), 0 ≤ nearKernel s (blockLength X (i : ℕ) k) +
      nearKernel s (blockLength X ((i : ℕ) + k) ((N : ℕ) - k)) := by
    intro k hk
    rw [Finset.mem_Ico] at hk
    exact add_nonneg (nearKernel_block_nonneg s X _ (by omega))
      (nearKernel_block_nonneg s X _ (by omega))
  calc ∑ j ∈ univ.filter (fun j => j ≠ i ∧ dist (loopPos X i) (loopPos X j) ≤ 3),
        dist (loopPos X i) (loopPos X j) ^ (-s)
      ≤ ∑ j ∈ univ.filter (fun j => j ≠ i ∧ dist (loopPos X i) (loopPos X j) ≤ 3),
          (nearKernel s (blockLength X (i : ℕ) (rootedIndex i j)) +
            nearKernel s (blockLength X ((i : ℕ) + rootedIndex i j)
              ((N : ℕ) - rootedIndex i j))) := by
        refine Finset.sum_le_sum (fun j hj => ?_)
        rw [Finset.mem_filter] at hj
        exact rootedTerm_le s X i j hj.2.1 hj.2.2
    _ = ∑ k ∈ (univ.filter (fun j => j ≠ i ∧ dist (loopPos X i) (loopPos X j) ≤ 3)).image
          (rootedIndex i), (nearKernel s (blockLength X (i : ℕ) k) +
            nearKernel s (blockLength X ((i : ℕ) + k) ((N : ℕ) - k))) := by
        rw [Finset.sum_image (fun _ _ _ _ h => rootedIndex_injective i h)]
    _ ≤ ∑ k ∈ Finset.Ico 1 (N : ℕ), (nearKernel s (blockLength X (i : ℕ) k) +
            nearKernel s (blockLength X ((i : ℕ) + k) ((N : ℕ) - k))) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro k hk
          rw [Finset.mem_image] at hk
          obtain ⟨j, hj, rfl⟩ := hk
          rw [Finset.mem_filter] at hj
          rw [Finset.mem_Ico]
          exact ⟨Nat.pos_of_ne_zero (rootedIndex_ne_zero i j hj.2.1), rootedIndex_lt i j⟩
        · intro k hk _
          exact hnn k hk

/-- The coercion of the positions to the microscopic circle is measurable. -/
theorem measurable_loopPos {N : ℕ+} (j : Fin (N : ℕ)) :
    Measurable (fun X : Configuration N => loopPos X j) := by
  have hc : Measurable (fun t : ℝ => (t : AddCircle (N : ℝ))) := AddCircle.measurable_mk'
  have hX : Measurable (fun X : Configuration N => X.val j) :=
    (measurable_pi_apply j).comp measurable_subtype_coe
  exact hc.comp (measurable_const.mul hX)

theorem measurable_rootedEnergy (s : ℝ) {N : ℕ+} (i : Fin (N : ℕ)) :
    Measurable (fun X : Configuration N => rootedEnergy s X i) := by
  unfold rootedEnergy
  simp_rw [Finset.sum_filter]
  refine Finset.measurable_sum _ (fun j _ => ?_)
  have hd : Measurable (fun X : Configuration N => dist (loopPos X i) (loopPos X j)) :=
    (measurable_loopPos i).dist (measurable_loopPos j)
  refine Measurable.ite ?_ (hd.pow_const _) measurable_const
  by_cases hji : j = i
  · simp [hji]
  · simp only [hji, ne_eq, not_false_eq_true, true_and]
    exact measurableSet_le hd measurable_const

/-- The shifted inverse-power series `∑_{n} n^{-(s+2)}` is summable for `s > 0`. -/
theorem summable_rpow_neg_two_add {s : ℝ} (hs : 0 < s) :
    Summable (fun n : ℕ => (n : ℝ) ^ (-(s + 2))) :=
  Real.summable_nat_rpow.mpr (by linarith)

/-- **Rooted moments**, the moments part of Lemma 5.8 (the bound `‖E_i‖_p ≤ C`).
For every `p ≥ 1` there is `C > 0`, depending only on `β`, `s` and `p`, such that every
particle number `N`, every label `i` and every `hPL` satisfy `‖E_i‖_{L^p} ≤ C`. -/
theorem rootedEnergy_eLpNorm (P : Parameters) {s : ℝ} (hs : 0 < s) {p : ℝ} (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (_hPL : External.PrekopaLeindler) (N : ℕ+) (i : Fin (N : ℕ)),
      eLpNorm (fun X : Configuration N => rootedEnergy s X i) (ENNReal.ofReal p)
        (gibbsMeasure P N) ≤ ENNReal.ofReal C := by
  set m : ℕ := ⌈p⌉₊ with hm_def
  have hm1 : 1 ≤ m := by
    have : (1 : ℝ) ≤ m := hp.trans (Nat.le_ceil p)
    exact_mod_cast this
  have hpm : p ≤ (m : ℝ) := Nat.le_ceil p
  obtain ⟨K0, hK0, hblock⟩ := nearKernel_block_eLpNorm P hs hm1
  set Z : ℝ := ∑' n : ℕ, (n : ℝ) ^ (-(s + 2)) with hZ_def
  have hsum := summable_rpow_neg_two_add hs
  have hZpos : 0 < Z := hsum.tsum_pos (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _) 1
    (by simp)
  refine ⟨2 * K0 * Z, by positivity, ?_⟩
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
  calc eLpNorm (fun X : Configuration N => rootedEnergy s X i) (ENNReal.ofReal p)
        (gibbsMeasure P N)
      ≤ eLpNorm (fun X : Configuration N => rootedEnergy s X i) (ENNReal.ofReal m)
          (gibbsMeasure P N) := eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal hpm)
    _ ≤ eLpNorm (fun X : Configuration N => ∑ k ∈ Finset.Ico 1 (N : ℕ),
          (nearKernel s (blockLength X (i : ℕ) k) +
            nearKernel s (blockLength X ((i : ℕ) + k) ((N : ℕ) - k)))) (ENNReal.ofReal m)
          (gibbsMeasure P N) :=
        eLpNorm_mono_real (measurable_rootedEnergy s i).aestronglyMeasurable (fun X => by
          rw [Real.norm_eq_abs, abs_of_nonneg (rootedEnergy_nonneg s X i)]
          exact rootedEnergy_le_sum s X i)
    _ = eLpNorm (∑ k ∈ Finset.Ico 1 (N : ℕ), fun X : Configuration N =>
          (nearKernel s (blockLength X (i : ℕ) k) +
            nearKernel s (blockLength X ((i : ℕ) + k) ((N : ℕ) - k)))) (ENNReal.ofReal m)
          (gibbsMeasure P N) := by
        congr 1
        ext X
        simp [Finset.sum_apply]
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
    _ ≤ ENNReal.ofReal (2 * K0 * Z) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        have h1 := mul_le_mul_of_nonneg_left hsum_k hK0.le
        have h2 := mul_le_mul_of_nonneg_left hsum_N hK0.le
        linarith

end Riesz1

end
end
