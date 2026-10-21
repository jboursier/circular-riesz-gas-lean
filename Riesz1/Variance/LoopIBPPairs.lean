/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Rigidity.NoExplosionUniform
public import Riesz1.Rigidity.Gaps
public import Riesz1.Rigidity.Inversion
public import Riesz1.Kernel.MeanFieldEnergyKernel
public import Riesz1.Variance.LoopForceKernel

/-!
# Pair distances on a configuration and the gap power sums

Proposition 5.5, moment clause. For a configuration `X` the
circular distance between two distinct particles is at least `N⁻¹` times the smaller of their
two gaps (the gaps are normalised to sum to `N`). Hence every negative power of a pair
distance is bounded by a constant multiple of the power sum `∑ₖ gapₖ^{-r}`, whose integrability
under the Gibbs law is the uniform inverse-moment bound `no_explosion_uniform`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology UnitAddCircle

namespace Riesz1

variable {N : ℕ+}

/-- The power sum `∑ₖ gapₖ^{-r}` over the `N` gaps of one period. -/
noncomputable def gapPowerSum (r : ℝ) (X : Configuration N) : ℝ :=
  ∑ k : Fin (N : ℕ), gap X (k : ℕ) ^ (-r)

/-- The cyclic lift at index `N` is the first lift plus one. -/
lemma cyclicLift_N (X : Configuration N) :
    cyclicLift X ((N : ℕ) : ℤ) = X.val ⟨0, N.pos⟩ + 1 := by
  have h := cyclicLift_add_N X 0
  rw [zero_add, cyclicLift_zero] at h
  exact h

/-- The gap, divided by `N`, is the difference of consecutive cyclic lifts. -/
lemma gap_div_eq (X : Configuration N) (j : ℤ) :
    gap X j / (N : ℝ) = cyclicLift X (j + 1) - cyclicLift X j := by
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast N.ne_zero
  unfold gap
  field_simp

/-- For `i < j`, the difference of the two particles is a sum of arcs, and each of the two
arcs contains one gap. -/
lemma dist_ge_of_lt (X : Configuration N) {i j : Fin (N : ℕ)} (hij : i < j) :
    (N : ℝ)⁻¹ * min (gap X (i : ℕ)) (gap X (j : ℕ)) ≤
      dist ((X.val j - X.val i : ℝ) : UnitAddCircle) 0 := by
  have hmono := cyclicLift_strictMono X
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast N.pos
  have hci : cyclicLift X ((i : ℕ) : ℤ) = X.val i := cyclicLift_natCast X i
  have hcj : cyclicLift X ((j : ℕ) : ℤ) = X.val j := cyclicLift_natCast X j
  have hc0 := cyclicLift_zero X
  have hcN := cyclicLift_N X
  have hij' : (i : ℕ) < (j : ℕ) := hij
  have hjN : (j : ℕ) < (N : ℕ) := j.isLt
  -- The difference `S` lies strictly between `0` and `1`.
  have hS0 : 0 < X.val j - X.val i := by
    have h := config_strictMono X hij
    linarith
  have hS1 : X.val j - X.val i < 1 := by
    have h1 := config_lt_first_add_one X j
    have h2 : X.val ⟨0, N.pos⟩ ≤ X.val i := (config_strictMono X).monotone (Fin.zero_le _)
    linarith
  -- The arc from `i` to `j` contains the gap at `i`.
  have harc : gap X (i : ℕ) / (N : ℝ) ≤ X.val j - X.val i := by
    rw [gap_div_eq, hci, ← hcj]
    have hle : cyclicLift X (((i : ℕ) : ℤ) + 1) ≤ cyclicLift X ((j : ℕ) : ℤ) :=
      hmono.monotone (by omega)
    linarith
  -- The complementary arc, from `j` to the first lift plus one, contains the gap at `j`.
  have hcomp : gap X (j : ℕ) / (N : ℝ) ≤ 1 - (X.val j - X.val i) := by
    rw [gap_div_eq]
    have hle : cyclicLift X (((j : ℕ) : ℤ) + 1) ≤ cyclicLift X ((N : ℕ) : ℤ) :=
      hmono.monotone (by omega)
    have hi0 : cyclicLift X 0 ≤ cyclicLift X ((i : ℕ) : ℤ) :=
      hmono.monotone (by simp [Nat.cast_nonneg])
    rw [hcN] at hle
    rw [hc0, hci] at hi0
    rw [hcj]
    linarith
  -- The distance is the smaller of the two arcs.
  rw [dist_coe_eq_min hS0 hS1, ← div_eq_inv_mul]
  apply le_min
  · exact le_trans (div_le_div_of_nonneg_right (min_le_left _ _) hNpos.le) harc
  · exact le_trans (div_le_div_of_nonneg_right (min_le_right _ _) hNpos.le) hcomp

/-- For distinct particles, the circular distance is at least `N⁻¹` times the smaller gap. -/
lemma dist_ge (X : Configuration N) {i j : Fin (N : ℕ)} (hij : i ≠ j) :
    (N : ℝ)⁻¹ * min (gap X (i : ℕ)) (gap X (j : ℕ)) ≤
      dist ((X.val i - X.val j : ℝ) : UnitAddCircle) 0 := by
  rcases lt_or_gt_of_ne hij with h | h
  · rw [show X.val i - X.val j = -(X.val j - X.val i) by ring, AddCircle.coe_neg,
      dist_zero_right, norm_neg, ← dist_zero_right]
    exact dist_ge_of_lt X h
  · have h' := dist_ge_of_lt X h
    rw [min_comm]
    exact h'

/-- Distinct particles never collide on the circle. -/
lemma coe_sub_ne_zero (X : Configuration N) {i j : Fin (N : ℕ)} (hij : i ≠ j) :
    ((X.val i - X.val j : ℝ) : UnitAddCircle) ≠ 0 := by
  intro h
  have h1 := dist_ge X hij
  rw [h, dist_self] at h1
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast N.pos
  have hpos : 0 < (N : ℝ)⁻¹ * min (gap X (i : ℕ)) (gap X (j : ℕ)) :=
    mul_pos (inv_pos.mpr hNpos) (lt_min (gap_pos X _) (gap_pos X _))
  linarith

/-- Every negative power of a pair distance is at most `N^r` times the power sum. -/
lemma dist_rpow_le_gapPowerSum (X : Configuration N) {i j : Fin (N : ℕ)} (hij : i ≠ j)
    {r : ℝ} (hr : 0 ≤ r) :
    dist ((X.val i - X.val j : ℝ) : UnitAddCircle) 0 ^ (-r) ≤
      (N : ℝ) ^ r * gapPowerSum r X := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast N.pos
  have hm : 0 < (N : ℝ)⁻¹ * min (gap X (i : ℕ)) (gap X (j : ℕ)) :=
    mul_pos (inv_pos.mpr hNpos) (lt_min (gap_pos X _) (gap_pos X _))
  -- Monotonicity of `x ↦ x^(-r)` and the scaling `N⁻¹`.
  have h1 : dist ((X.val i - X.val j : ℝ) : UnitAddCircle) 0 ^ (-r) ≤
      ((N : ℝ)⁻¹ * min (gap X (i : ℕ)) (gap X (j : ℕ))) ^ (-r) :=
    Real.rpow_le_rpow_of_nonpos hm (dist_ge X hij) (neg_nonpos.mpr hr)
  have h2 : ((N : ℝ)⁻¹ * min (gap X (i : ℕ)) (gap X (j : ℕ))) ^ (-r) =
      (N : ℝ) ^ r * min (gap X (i : ℕ)) (gap X (j : ℕ)) ^ (-r) := by
    rw [Real.mul_rpow (inv_nonneg.mpr hNpos.le) ((lt_min (gap_pos X _) (gap_pos X _)).le),
      Real.inv_rpow hNpos.le, Real.rpow_neg hNpos.le, inv_inv]
  have h3 : min (gap X (i : ℕ)) (gap X (j : ℕ)) ^ (-r) ≤
      gap X (i : ℕ) ^ (-r) + gap X (j : ℕ) ^ (-r) := by
    have hi : 0 ≤ gap X (i : ℕ) ^ (-r) := Real.rpow_nonneg (gap_pos X _).le _
    have hj : 0 ≤ gap X (j : ℕ) ^ (-r) := Real.rpow_nonneg (gap_pos X _).le _
    rcases min_cases (gap X (i : ℕ)) (gap X (j : ℕ)) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> linarith
  have h4 : gap X (i : ℕ) ^ (-r) + gap X (j : ℕ) ^ (-r) ≤ gapPowerSum r X := by
    have hpair : ∑ k ∈ ({i, j} : Finset (Fin (N : ℕ))), gap X (k : ℕ) ^ (-r) =
        gap X (i : ℕ) ^ (-r) + gap X (j : ℕ) ^ (-r) := Finset.sum_pair hij
    rw [← hpair]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun k _ _ => Real.rpow_nonneg (gap_pos X _).le _)
  have h5 : (0 : ℝ) ≤ (N : ℝ) ^ r := Real.rpow_nonneg hNpos.le _
  calc dist ((X.val i - X.val j : ℝ) : UnitAddCircle) 0 ^ (-r)
      ≤ (N : ℝ) ^ r * min (gap X (i : ℕ)) (gap X (j : ℕ)) ^ (-r) := h2 ▸ h1
    _ ≤ (N : ℝ) ^ r * (gap X (i : ℕ) ^ (-r) + gap X (j : ℕ) ^ (-r)) :=
        mul_le_mul_of_nonneg_left h3 h5
    _ ≤ (N : ℝ) ^ r * gapPowerSum r X := mul_le_mul_of_nonneg_left h4 h5

/-- The power sum `∑ₖ gapₖ^{-r}` is integrable under the Gibbs law for every `r > 0`, by the
uniform inverse-moment bound of `no_explosion_uniform`. -/
theorem integrable_gapPowerSum (P : Parameters) (hPL : External.PrekopaLeindler)
    {r : ℝ} (hr : 0 < r) (N : ℕ+) :
    Integrable (fun X : Configuration N => gapPowerSum r X) (gibbsMeasure P N) := by
  obtain ⟨_, _, h⟩ := no_explosion_uniform P hr
  unfold gapPowerSum
  apply integrable_finsetSum
  intro k _
  obtain ⟨hI, _⟩ := h hPL N (k : ℕ)
  exact hI

/-- The power sum is nonnegative. -/
theorem gapPowerSum_nonneg (r : ℝ) (X : Configuration N) : 0 ≤ gapPowerSum r X := by
  unfold gapPowerSum
  exact Finset.sum_nonneg fun k _ => Real.rpow_nonneg (gap_pos X _).le _

/-- The power sum is measurable on the configuration space. -/
theorem measurable_gapPowerSum (r : ℝ) : Measurable (fun X : Configuration N => gapPowerSum r X) := by
  unfold gapPowerSum
  exact Finset.measurable_sum _ fun k _ => (measurable_gap _).pow_const _

/-- Raising the power sum to a power `p ≥ 0` is at most `N^p` times the power sum of the `p`-th
powers. The proof bounds the sum by `N` times its largest term. -/
theorem gapPowerSum_rpow_le (X : Configuration N) {r p : ℝ} (hp : 0 ≤ p) :
    gapPowerSum r X ^ p ≤ (N : ℝ) ^ p * gapPowerSum (r * p) X := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast N.pos
  have hnonneg : ∀ k : Fin (N : ℕ), 0 ≤ gap X (k : ℕ) ^ (-r) := fun k =>
    Real.rpow_nonneg (gap_pos X _).le _
  obtain ⟨k0, -, hk0⟩ := Finset.exists_max_image Finset.univ
    (fun k : Fin (N : ℕ) => gap X (k : ℕ) ^ (-r)) Finset.univ_nonempty
  have hA0 : 0 ≤ gapPowerSum r X := by
    unfold gapPowerSum
    exact Finset.sum_nonneg fun k _ => hnonneg k
  have hA : gapPowerSum r X ≤ (N : ℝ) * gap X (k0 : ℕ) ^ (-r) := by
    unfold gapPowerSum
    have h := Finset.sum_le_card_nsmul Finset.univ
      (fun k : Fin (N : ℕ) => gap X (k : ℕ) ^ (-r)) (gap X (k0 : ℕ) ^ (-r))
      (fun k _ => hk0 k (Finset.mem_univ _))
    simpa [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using h
  have hpw : ∀ k : Fin (N : ℕ), (gap X (k : ℕ) ^ (-r)) ^ p = gap X (k : ℕ) ^ (-(r * p)) :=
    fun k => by rw [← Real.rpow_mul (gap_pos X _).le, neg_mul]
  have hpow : (gap X (k0 : ℕ) ^ (-r)) ^ p ≤ gapPowerSum (r * p) X := by
    have hsingle : (gap X (k0 : ℕ) ^ (-r)) ^ p ≤ ∑ k : Fin (N : ℕ), (gap X (k : ℕ) ^ (-r)) ^ p :=
      Finset.single_le_sum (f := fun k : Fin (N : ℕ) => (gap X (k : ℕ) ^ (-r)) ^ p)
        (fun k _ => Real.rpow_nonneg (hnonneg k) _) (Finset.mem_univ k0)
    calc (gap X (k0 : ℕ) ^ (-r)) ^ p ≤ ∑ k : Fin (N : ℕ), (gap X (k : ℕ) ^ (-r)) ^ p := hsingle
      _ = ∑ k : Fin (N : ℕ), gap X (k : ℕ) ^ (-(r * p)) :=
          Finset.sum_congr rfl fun k _ => hpw k
      _ = gapPowerSum (r * p) X := rfl
  calc gapPowerSum r X ^ p ≤ ((N : ℝ) * gap X (k0 : ℕ) ^ (-r)) ^ p :=
        Real.rpow_le_rpow hA0 hA hp
    _ = (N : ℝ) ^ p * (gap X (k0 : ℕ) ^ (-r)) ^ p :=
        Real.mul_rpow hNpos.le (hnonneg k0)
    _ ≤ (N : ℝ) ^ p * gapPowerSum (r * p) X :=
        mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hNpos.le _)

end Riesz1

end
