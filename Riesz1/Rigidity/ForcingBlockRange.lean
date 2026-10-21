/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Rigidity.ForcingPotential

/-!
# The range of the lifted block

The lifted block `π_I` has range the ordered chamber `D_{L+1}`.
The inclusion of the range in `D_{L+1}` is part of the definition `Riesz1.liftedBlock`. This file
proves the converse: every point of `D_{L+1}` is the lifted block of some configuration.

The construction uses one period of lifts. A chamber point `y` of `L + 1` particles gives the profile
`Φ` on `[0, N)`: it equals `y_r` for `r ≤ L`, and it is affine on `[L, N)` with slope making
`Φ N = y_0 + 1`. The periodic extension `Ψ k = Φ (k mod N) + ⌊k / N⌋` is strictly increasing and
satisfies `Ψ (k + N) = Ψ k + 1`. Shifting by an integer so that the first label lies in `[0, 1)`
gives the lifts of a configuration, whose lifted block is `y`.
-/

@[expose] public section

open Finset

namespace Riesz1

variable {N : ℕ+}

/-! ### The profile of one period -/

/-- The profile `Φ` of one period: `Φ r = y_r` for `r ≤ L`, and `Φ` is affine on `[L, N]`, with
`Φ L = y_L` and slope `(y_0 + 1 - y_L) / (N - L)` (so that `Φ N = y_0 + 1`). -/
noncomputable def blockProfile (N : ℕ+) {L : ℕ} (y : Fin (L + 1) → ℝ) (r : ℕ) : ℝ :=
  if h : r ≤ L then y ⟨r, Nat.lt_succ_of_le h⟩ else
    y (Fin.last L) + ((y 0 + 1 - y (Fin.last L)) / ((N : ℝ) - L)) * ((r : ℝ) - L)

/-- The profile equals the block coordinate on `[0, L]`. -/
theorem blockProfile_of_le (N : ℕ+) {L : ℕ} (y : Fin (L + 1) → ℝ) {r : ℕ} (h : r ≤ L) :
    blockProfile N y r = y ⟨r, Nat.lt_succ_of_le h⟩ := by
  unfold blockProfile
  simp only [h, ↓reduceDIte]

/-- The profile is strictly increasing on `[0, N)`, given that `y` is a chamber point. -/
theorem blockProfile_strictMonoOn {L : ℕ} (hL : L < (N : ℕ)) {y : Fin (L + 1) → ℝ}
    (hmono : StrictMono y) (hlt : ∀ i, y i < y 0 + 1) {r s : ℕ} (hrs : r < s) :
    blockProfile N y r < blockProfile N y s := by
  have hslope : 0 < (y 0 + 1 - y (Fin.last L)) / ((N : ℝ) - L) := by
    apply div_pos
    · linarith [hlt (Fin.last L)]
    · have : (L : ℝ) < (N : ℝ) := by exact_mod_cast hL
      linarith
  by_cases hr : r ≤ L
  · by_cases hsL : s ≤ L
    · rw [blockProfile_of_le N y hr, blockProfile_of_le N y hsL]
      exact hmono (Fin.mk_lt_mk.2 hrs)
    · have hlast : L < s := not_le.1 hsL
      unfold blockProfile
      simp only [hr, hsL, ↓reduceDIte]
      have h1 : y ⟨r, Nat.lt_succ_of_le hr⟩ ≤ y (Fin.last L) :=
        hmono.monotone (Fin.le_last _)
      have h2 : (0 : ℝ) < (s : ℝ) - L := by
        have : (L : ℝ) < (s : ℝ) := by exact_mod_cast hlast
        linarith
      have h3 := mul_pos hslope h2
      linarith
  · have hLr : L < r := not_le.1 hr
    unfold blockProfile
    have hsL : ¬ s ≤ L := fun h => absurd (lt_of_lt_of_le hLr (le_of_lt hrs)) (not_lt.2 h)
    simp only [hr, hsL, ↓reduceDIte]
    have h2 : (r : ℝ) - L < (s : ℝ) - L := by
      have : (r : ℝ) < (s : ℝ) := by exact_mod_cast hrs
      linarith
    have h3 := mul_lt_mul_of_pos_left h2 hslope
    linarith

/-- The profile is below `y_0 + 1` on `[0, N)`. -/
theorem blockProfile_lt_succ {L : ℕ} (hL : L < (N : ℕ)) {y : Fin (L + 1) → ℝ}
    (hlt : ∀ i, y i < y 0 + 1) {r : ℕ} (hr : r < (N : ℕ)) :
    blockProfile N y r < blockProfile N y 0 + 1 := by
  have hzero : blockProfile N y 0 = y 0 := blockProfile_of_le N y (Nat.zero_le L)
  rw [hzero]
  by_cases hrL : r ≤ L
  · rw [blockProfile_of_le N y hrL]
    exact hlt _
  · have hLr : L < r := not_le.1 hrL
    unfold blockProfile
    simp only [hrL, ↓reduceDIte]
    have hNL : (0 : ℝ) < (N : ℝ) - L := by
      have : (L : ℝ) < (N : ℝ) := by exact_mod_cast hL
      linarith
    have hslope : 0 < (y 0 + 1 - y (Fin.last L)) / ((N : ℝ) - L) := by
      apply div_pos
      · linarith [hlt (Fin.last L)]
      · exact hNL
    have h2 : (r : ℝ) - L < (N : ℝ) - L := by
      have : (r : ℝ) < (N : ℝ) := by exact_mod_cast hr
      linarith
    have h3 := mul_lt_mul_of_pos_left h2 hslope
    have h4 : (y 0 + 1 - y (Fin.last L)) / ((N : ℝ) - L) * ((N : ℝ) - L) =
        y 0 + 1 - y (Fin.last L) := div_mul_cancel₀ _ hNL.ne'
    linarith

/-! ### The periodic lifts -/

/-- The periodic lifts `Ψ k = Φ (k mod N) + ⌊k / N⌋`, for every integer `k`. -/
noncomputable def periodicLift (N : ℕ+) {L : ℕ} (y : Fin (L + 1) → ℝ) (k : ℤ) : ℝ :=
  blockProfile N y ((k % ((N : ℕ) : ℤ)).toNat) + (((k / ((N : ℕ) : ℤ)) : ℤ) : ℝ)

/-- Adding `N` to the label adds one to the periodic lift. -/
theorem periodicLift_add_N {L : ℕ} (y : Fin (L + 1) → ℝ) (k : ℤ) :
    periodicLift N y (k + ((N : ℕ) : ℤ)) = periodicLift N y k + 1 := by
  have hN : (0 : ℤ) < ((N : ℕ) : ℤ) := by exact_mod_cast N.pos
  unfold periodicLift
  have h1 : (k + ((N : ℕ) : ℤ)) % ((N : ℕ) : ℤ) = k % ((N : ℕ) : ℤ) := by
    rw [show k + ((N : ℕ) : ℤ) = k + ((N : ℕ) : ℤ) * 1 by ring, Int.add_mul_emod_self_left]
  have h2 : (k + ((N : ℕ) : ℤ)) / ((N : ℕ) : ℤ) = k / ((N : ℕ) : ℤ) + 1 := by
    rw [show k + ((N : ℕ) : ℤ) = k + 1 * ((N : ℕ) : ℤ) by ring,
      Int.add_mul_ediv_right _ _ hN.ne']
  rw [h1, h2]
  push_cast
  ring

/-- Multiplying the period by `q` adds `q` to the periodic lift. -/
theorem periodicLift_add_mul {L : ℕ} (y : Fin (L + 1) → ℝ) (k q : ℤ) :
    periodicLift N y (k + ((N : ℕ) : ℤ) * q) = periodicLift N y k + q := by
  refine Int.induction_on q ?_ ?_ ?_
  · simp
  · intro n ih
    rw [show k + ((N : ℕ) : ℤ) * ((n : ℤ) + 1) = (k + ((N : ℕ) : ℤ) * n) + ((N : ℕ) : ℤ) by ring,
      periodicLift_add_N, ih]
    push_cast
    ring
  · intro n ih
    have h := periodicLift_add_N (N := N) y (k + ((N : ℕ) : ℤ) * (-(n : ℤ) - 1))
    rw [show k + ((N : ℕ) : ℤ) * (-(n : ℤ) - 1) + ((N : ℕ) : ℤ) = k + ((N : ℕ) : ℤ) * (-(n : ℤ))
      by ring, ih] at h
    push_cast at h ⊢
    linarith

/-- On the labels `0 ≤ i < N`, the periodic lift is the profile. -/
theorem periodicLift_natCast {L : ℕ} (y : Fin (L + 1) → ℝ) {i : ℕ} (hi : i < (N : ℕ)) :
    periodicLift N y (i : ℤ) = blockProfile N y i := by
  unfold periodicLift
  have hi' : (i : ℤ) < ((N : ℕ) : ℤ) := by exact_mod_cast hi
  rw [Int.emod_eq_of_lt (Int.natCast_nonneg i) hi', Int.ediv_eq_zero_of_lt (Int.natCast_nonneg i) hi',
    Int.toNat_natCast]
  simp

/-- The residue and quotient of `a + N q` for `0 ≤ a < N`. -/
theorem emod_ediv_add_mul (N : ℕ+) {a : ℤ} (ha0 : 0 ≤ a) (haN : a < ((N : ℕ) : ℤ)) (q : ℤ) :
    (a + ((N : ℕ) : ℤ) * q) % ((N : ℕ) : ℤ) = a ∧ (a + ((N : ℕ) : ℤ) * q) / ((N : ℕ) : ℤ) = q := by
  have hN : (0 : ℤ) < ((N : ℕ) : ℤ) := by exact_mod_cast N.pos
  constructor
  · rw [Int.add_mul_emod_self_left, Int.emod_eq_of_lt ha0 haN]
  · rw [Int.add_mul_ediv_left _ _ hN.ne', Int.ediv_eq_zero_of_lt ha0 haN, zero_add]

/-- The periodic lift is strictly increasing on `ℤ`, given that `y` is a chamber point. -/
theorem periodicLift_strictMono {L : ℕ} (hL : L < (N : ℕ)) {y : Fin (L + 1) → ℝ}
    (hmono : StrictMono y) (hlt : ∀ i, y i < y 0 + 1) : StrictMono (periodicLift N y) := by
  refine strictMono_int_of_lt_succ fun k => ?_
  have hN : (0 : ℤ) < ((N : ℕ) : ℤ) := by exact_mod_cast N.pos
  have hk0 : 0 ≤ k % ((N : ℕ) : ℤ) := Int.emod_nonneg k hN.ne'
  have hkN : k % ((N : ℕ) : ℤ) < ((N : ℕ) : ℤ) := Int.emod_lt_of_pos k hN
  have hdecomp : k % ((N : ℕ) : ℤ) + ((N : ℕ) : ℤ) * (k / ((N : ℕ) : ℤ)) = k := by
    rw [mul_comm]
    exact Int.emod_add_ediv_mul k _
  unfold periodicLift
  generalize k % ((N : ℕ) : ℤ) = a at hk0 hkN hdecomp ⊢
  generalize k / ((N : ℕ) : ℤ) = q at hdecomp ⊢
  by_cases hA : a + 1 < ((N : ℕ) : ℤ)
  · have hk1 : k + 1 = (a + 1) + ((N : ℕ) : ℤ) * q := by linarith
    obtain ⟨h1, h2⟩ := emod_ediv_add_mul N (a := a + 1) (by omega) hA q
    rw [hk1, h1, h2]
    have hrs : a.toNat < (a + 1).toNat := by omega
    have := blockProfile_strictMonoOn hL hmono hlt hrs
    linarith
  · have hA' : a + 1 = ((N : ℕ) : ℤ) := by omega
    have hk1 : k + 1 = 0 + ((N : ℕ) : ℤ) * (q + 1) := by linear_combination hA' - hdecomp
    obtain ⟨h1, h2⟩ := emod_ediv_add_mul N (a := 0) le_rfl hN (q + 1)
    rw [hk1, h1, h2, Int.toNat_zero]
    have hlt' := blockProfile_lt_succ hL hlt (r := a.toNat) (by omega)
    push_cast
    linarith

/-! ### The shifted lifts and the configuration -/

/-- The lifts `g k = Ψ (k - i0) - ⌊Ψ (-i0)⌋`. They start the block at the label `i0`, and the shift
makes the lift of the label `0` lie in `[0, 1)`. -/
noncomputable def shiftedLift (N : ℕ+) {L : ℕ} (y : Fin (L + 1) → ℝ) (i0 k : ℤ) : ℝ :=
  periodicLift N y (k - i0) - (((⌊periodicLift N y (-i0)⌋) : ℤ) : ℝ)

/-- The shifted lifts satisfy the period relation. -/
theorem shiftedLift_add_mul {L : ℕ} (y : Fin (L + 1) → ℝ) (i0 k q : ℤ) :
    shiftedLift N y i0 (k + ((N : ℕ) : ℤ) * q) = shiftedLift N y i0 k + q := by
  unfold shiftedLift
  rw [show k + ((N : ℕ) : ℤ) * q - i0 = (k - i0) + ((N : ℕ) : ℤ) * q by ring,
    periodicLift_add_mul]
  ring

/-- The shifted lifts are strictly increasing. -/
theorem shiftedLift_strictMono {L : ℕ} (hL : L < (N : ℕ)) {y : Fin (L + 1) → ℝ}
    (hmono : StrictMono y) (hlt : ∀ i, y i < y 0 + 1) (i0 : ℤ) :
    StrictMono (shiftedLift N y i0) := by
  intro a b hab
  have h := periodicLift_strictMono hL hmono hlt (show a - i0 < b - i0 by linarith)
  unfold shiftedLift
  linarith

/-- The shifted lift of the label `0` is the fractional part of `Ψ (-i0)`. -/
theorem shiftedLift_zero {L : ℕ} (y : Fin (L + 1) → ℝ) (i0 : ℤ) :
    shiftedLift N y i0 0 = periodicLift N y (-i0) - (((⌊periodicLift N y (-i0)⌋) : ℤ) : ℝ) := by
  unfold shiftedLift
  rw [zero_sub]

/-- The shifted lifts, on the labels `0, …, N - 1`, form a point of `D_N`. -/
theorem shiftedLift_mem {L : ℕ} (hL : L < (N : ℕ)) {y : Fin (L + 1) → ℝ}
    (hmono : StrictMono y) (hlt : ∀ i, y i < y 0 + 1) (i0 : ℤ) :
    (fun k : Fin (N : ℕ) => shiftedLift N y i0 (k : ℤ)) ∈ orderedDomain N := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b hab
    exact shiftedLift_strictMono hL hmono hlt i0 (by exact_mod_cast hab)
  · show (0 : ℝ) ≤ shiftedLift N y i0 ((0 : ℕ) : ℤ)
    rw [Nat.cast_zero, shiftedLift_zero]
    linarith [Int.floor_le (periodicLift N y (-i0))]
  · show shiftedLift N y i0 ((0 : ℕ) : ℤ) < 1
    rw [Nat.cast_zero, shiftedLift_zero]
    linarith [Int.lt_floor_add_one (periodicLift N y (-i0))]
  · intro i
    show shiftedLift N y i0 ((i : ℕ) : ℤ) < shiftedLift N y i0 ((0 : ℕ) : ℤ) + 1
    have hi : ((i : ℕ) : ℤ) < ((N : ℕ) : ℤ) := by exact_mod_cast i.isLt
    have h := periodicLift_strictMono hL hmono hlt
      (show ((i : ℕ) : ℤ) - i0 < -i0 + ((N : ℕ) : ℤ) by linarith)
    rw [periodicLift_add_N] at h
    rw [Nat.cast_zero, shiftedLift_zero]
    unfold shiftedLift
    linarith

/-- The configuration of `N` particles whose lifts are the shifted periodic lifts. -/
noncomputable def shiftedConfig (N : ℕ+) {L : ℕ} (hL : L < (N : ℕ)) {y : Fin (L + 1) → ℝ}
    (hmono : StrictMono y) (hlt : ∀ i, y i < y 0 + 1) (i0 : ℤ) : Configuration N :=
  ⟨fun k : Fin (N : ℕ) => shiftedLift N y i0 (k : ℤ), shiftedLift_mem hL hmono hlt i0⟩

/-- The cyclic lifts of the shifted configuration are the shifted lifts, at every integer label. -/
theorem cyclicLift_shiftedConfig {L : ℕ} (hL : L < (N : ℕ)) {y : Fin (L + 1) → ℝ}
    (hmono : StrictMono y) (hlt : ∀ i, y i < y 0 + 1) (i0 m : ℤ) :
    cyclicLift (shiftedConfig N hL hmono hlt i0) m = shiftedLift N y i0 m := by
  obtain ⟨i, hi, q, rfl⟩ := exists_nat_add_mul (N := N) m
  rw [cyclicLift_add_mul _ hi q, shiftedLift_add_mul]
  rfl

/-- Every point of the ordered chamber `D_{L + 1}` is the lifted block of a configuration of `N`
particles. Together with `measurable_liftedBlock`, this is the range claim:
the lifted block `π_I` has range `D_{L + 1}`. -/
theorem liftedBlock_surjective (i0 : ℤ) {L : ℕ} (hL : L < (N : ℕ)) :
    Function.Surjective (liftedBlock (N := N) i0 hL) := by
  have key : ∀ y : Fin (L + 1) → ℝ, y ∈ orderedDomain (Nat.succPNat L) →
      ∃ X : Configuration N, liftedBlockCoords i0 L X = y := by
    intro y hy
    have hmono : StrictMono y := hy.1
    have hlt : ∀ i, y i < y 0 + 1 := hy.2.2.2
    have h0 : 0 ≤ y 0 := hy.2.1
    have h1 : y 0 < 1 := hy.2.2.1
    -- The profile at `0` is `y 0`, which lies in `[0, 1)`, so its floor vanishes.
    have hP0 : periodicLift N y 0 = y 0 := by
      have := periodicLift_natCast y (i := 0) N.pos
      simp only [Nat.cast_zero] at this
      rw [this]
      exact blockProfile_of_le N y (Nat.zero_le L)
    have hfl : ⌊periodicLift N y 0⌋ = 0 :=
      Int.floor_eq_zero_iff.2 ⟨by rw [hP0]; exact h0, by rw [hP0]; exact h1⟩
    refine ⟨shiftedConfig N hL hmono hlt i0, ?_⟩
    funext r
    have hrN : (r : ℕ) < (N : ℕ) := lt_of_le_of_lt (Nat.lt_succ_iff.mp r.isLt) hL
    have hr : periodicLift N y ((r : ℕ) : ℤ) = y r := by
      rw [periodicLift_natCast y hrN, blockProfile_of_le N y (Nat.lt_succ_iff.mp r.isLt)]
    unfold liftedBlockCoords
    rw [cyclicLift_shiftedConfig, cyclicLift_shiftedConfig]
    unfold shiftedLift
    rw [add_sub_cancel_left, sub_self, Int.floor_sub_intCast, hfl, hr]
    push_cast
    ring
  rintro ⟨y, hy⟩
  obtain ⟨X, hX⟩ := key y hy
  exact ⟨X, Subtype.ext hX⟩

end Riesz1

end
