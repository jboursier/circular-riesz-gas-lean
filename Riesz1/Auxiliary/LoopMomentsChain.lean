/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopMomentsLifts

/-!
# The particles of a microscopic arc

For a configuration `X` and an arc `microArc N a r` with `0 < r ≤ N`, the integer lifts
`j` whose positions `N cyclicLift X j` lie in `(a, a + r)` form a run of consecutive integers
`c, c+1, …, d`. The `m` particles of the arc therefore have `m - 1` consecutive gaps, whose sum
is less than `r`. This is the deterministic core of the count moment estimate of
Lemma 5.8, the bound `(M_J - 1)_+^{q+1} ≤ r^q ∑ 1_J(z_i) y_i^{-q}`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Finset Set

attribute [local instance] Classical.propDecidable

namespace Riesz1

variable {N : ℕ+}

/-- The lifted positions `N cyclicLift X j` are bounded below by any level, along the integers
in the negative direction. -/
theorem exists_lift_le (X : Configuration N) (a : ℝ) :
    ∃ j0 : ℤ, (N : ℝ) * cyclicLift X j0 ≤ a := by
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  set n : ℕ := ⌈cyclicLift X 0 - a / N⌉₊ with hn
  refine ⟨0 + (-(n : ℤ)) * ((N : ℕ) : ℤ), ?_⟩
  rw [cyclicLift_add_int_mul]
  have hceil : cyclicLift X 0 - a / N ≤ (n : ℝ) := Nat.le_ceil _
  have hmul : (N : ℝ) * (cyclicLift X 0 + ((-(n : ℤ)) : ℤ)) ≤ a := by
    push_cast
    have h := mul_le_mul_of_nonneg_left hceil hN.le
    rw [mul_sub, mul_div_cancel₀ _ hN.ne'] at h
    linarith
  exact hmul

/-- The lifted positions reach every level, along the integers in the positive direction. -/
theorem exists_lift_ge (X : Configuration N) (b : ℝ) :
    ∃ j1 : ℤ, b ≤ (N : ℝ) * cyclicLift X j1 := by
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  set n : ℕ := ⌈b / N - cyclicLift X 0⌉₊ with hn
  refine ⟨0 + (n : ℤ) * ((N : ℕ) : ℤ), ?_⟩
  rw [cyclicLift_add_int_mul]
  have hceil : b / N - cyclicLift X 0 ≤ (n : ℝ) := Nat.le_ceil _
  have hmul : b ≤ (N : ℝ) * (cyclicLift X 0 + ((n : ℤ) : ℤ)) := by
    push_cast
    have h := mul_le_mul_of_nonneg_left hceil hN.le
    rw [mul_sub, mul_div_cancel₀ _ hN.ne'] at h
    linarith
  exact hmul

/-- The lifts are strictly increasing, so a lift below the level `a` lies before every lift
above it. -/
theorem lt_of_lift_lt {X : Configuration N} {j j' : ℤ} (h : (N : ℝ) * cyclicLift X j <
    (N : ℝ) * cyclicLift X j') : j < j' := by
  by_contra hcon
  rw [not_lt] at hcon
  have hle : cyclicLift X j' ≤ cyclicLift X j := (cyclicLift_strictMono X).monotone hcon
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  nlinarith

/-- The positions of the lifts agree with the gap sums: the total gap over `c, …, d - 1` is
`N (cyclicLift X d - cyclicLift X c)`. -/
theorem sum_gap_eq_lift_sub (X : Configuration N) (c : ℤ) (L : ℕ) :
    ∑ r ∈ Finset.range L, gap X (c + r) = (N : ℝ) * (cyclicLift X (c + L) - cyclicLift X c) := by
  rw [sum_gap_range_eq_blockLength]
  rfl

/-- Positive lifts: a gap is positive. -/
theorem gap_pos' (X : Configuration N) (j : ℤ) : 0 < gap X j := Riesz1.gap_pos X j

/-- A gap is `N`-periodic, so it agrees with the gap of its residue. -/
theorem gap_eq_residueFin (X : Configuration N) (j : ℤ) :
    gap X j = gap X (((residueFin N j : Fin (N : ℕ)) : ℕ) : ℤ) := by
  have h : j = (((residueFin N j : Fin (N : ℕ)) : ℕ) : ℤ) + (j / ((N : ℕ) : ℤ)) * ((N : ℕ) : ℤ) := by
    have hd := Int.emod_def j ((N : ℕ) : ℤ)
    rw [natCast_residueFin]
    linarith
  conv_lhs => rw [h]
  exact gap_add_int_mul X _ _

/-- The particle `i` lies in the arc exactly when some integer translate of its lift does. -/
theorem mem_microArc_iff_lift (a r : ℝ) (X : Configuration N) (i : Fin (N : ℕ)) :
    loopPos X i ∈ microArc N a r ↔
      ∃ n : ℤ, a < (N : ℝ) * cyclicLift X ((i : ℕ) + n * ((N : ℕ) : ℤ)) ∧
        (N : ℝ) * cyclicLift X ((i : ℕ) + n * ((N : ℕ) : ℤ)) < a + r := by
  have key : ∀ n : ℤ, (N : ℝ) * cyclicLift X ((i : ℕ) + n * ((N : ℕ) : ℤ)) =
      (N : ℝ) * X.val i + n * (N : ℝ) := by
    intro n
    rw [cyclicLift_add_int_mul, cyclicLift_natCast]
    ring
  unfold loopPos
  rw [coe_mem_microArc_iff]
  simp only [key]

/-- The microscopic arc length is at most the period, so the run of lifts in the arc spans less
than one period. -/
theorem span_lt_period {X : Configuration N} {a r : ℝ} (hrN : r ≤ N) {c d : ℤ} (_hcd : c ≤ d)
    (hc : a < (N : ℝ) * cyclicLift X c) (hd : (N : ℝ) * cyclicLift X d < a + r) :
    d - c < ((N : ℕ) : ℤ) := by
  by_contra hcon
  rw [not_lt] at hcon
  have h1 : c + ((N : ℕ) : ℤ) ≤ d := by omega
  have h2 : cyclicLift X (c + ((N : ℕ) : ℤ)) ≤ cyclicLift X d :=
    (cyclicLift_strictMono X).monotone h1
  rw [cyclicLift_add_N] at h2
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  nlinarith

/-- **The count of an arc against its gaps.** For an arc of microscopic length `0 < r ≤ N`,
the count `M_J` of particles satisfies `(M_J - 1)_+^{q+1} ≤ r^q ∑_{i ∈ J} y_i^{-q}`, where
`y_i = gap X i` and the sum runs over the particles in the arc. -/
theorem loopCount_pow_le_sum (a r : ℝ) (hr : 0 < r) (hrN : r ≤ N) (X : Configuration N)
    (q : ℕ) :
    (max (loopCount a r X - 1) 0) ^ (q + 1) ≤
      r ^ q * ∑ i : Fin (N : ℕ),
        if loopPos X i ∈ microArc N a r then gap X (i : ℕ) ^ (-(q : ℤ)) else 0 := by
  set P : Finset (Fin (N : ℕ)) := univ.filter (fun i => loopPos X i ∈ microArc N a r) with hP
  have hcount : loopCount a r X = (P.card : ℝ) := by
    unfold loopCount
    rw [hP, Finset.sum_boole]
  have hRHS : ∑ i : Fin (N : ℕ), (if loopPos X i ∈ microArc N a r then gap X (i : ℕ) ^
      (-(q : ℤ)) else 0) = ∑ i ∈ P, gap X (i : ℕ) ^ (-(q : ℤ)) := by
    rw [hP, Finset.sum_filter]
  rw [hRHS]
  have hr_nonneg : 0 ≤ r ^ q := pow_nonneg hr.le q
  -- The lifts of the particles of the arc, with the bounds `j0 < j < j1`.
  set u : ℤ → ℝ := fun j => (N : ℝ) * cyclicLift X j with hu
  obtain ⟨j0, hj0⟩ := exists_lift_le X a
  obtain ⟨j1, hj1⟩ := exists_lift_ge X (a + r)
  have hbounds : ∀ j : ℤ, a < u j → u j < a + r → j0 < j ∧ j < j1 := by
    intro j h1 h2
    exact ⟨lt_of_lift_lt (lt_of_le_of_lt hj0 h1), lt_of_lift_lt (lt_of_lt_of_le h2 hj1)⟩
  set F : Finset ℤ := (Finset.Ioo j0 j1).filter (fun j => a < u j ∧ u j < a + r) with hF
  have hmemF : ∀ j : ℤ, j ∈ F ↔ a < u j ∧ u j < a + r := by
    intro j
    rw [hF, Finset.mem_filter, Finset.mem_Ioo]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨hbounds j h.1 h.2, h⟩
  -- Particles of the arc in terms of the lifts.
  have hPmem : ∀ i : Fin (N : ℕ), i ∈ P ↔ ∃ n : ℤ, ((i : ℕ) + n * ((N : ℕ) : ℤ)) ∈ F := by
    intro i
    rw [hP, Finset.mem_filter, mem_microArc_iff_lift]
    simp only [Finset.mem_univ, true_and]
    constructor
    · rintro ⟨n, h1, h2⟩
      exact ⟨n, (hmemF _).mpr ⟨h1, h2⟩⟩
    · rintro ⟨n, hn⟩
      obtain ⟨h1, h2⟩ := (hmemF _).mp hn
      exact ⟨n, h1, h2⟩
  rcases Finset.eq_empty_or_nonempty F with hempty | hne
  · -- No lift lies in the arc: the arc is empty.
    have hPempty : P = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro i hi
      obtain ⟨n, hn⟩ := (hPmem i).mp hi
      rw [hempty] at hn
      exact Finset.notMem_empty _ hn
    rw [hcount, hPempty, Finset.card_empty, Nat.cast_zero, Finset.sum_empty, mul_zero]
    norm_num
  set c : ℤ := F.min' hne with hc_def
  set d : ℤ := F.max' hne with hd_def
  have hc_mem : c ∈ F := Finset.min'_mem F hne
  have hd_mem : d ∈ F := Finset.max'_mem F hne
  obtain ⟨hc1, hc2⟩ := (hmemF c).mp hc_mem
  obtain ⟨hd1, hd2⟩ := (hmemF d).mp hd_mem
  have hcd : c ≤ d := Finset.min'_le F d hd_mem
  -- Every lift between `c` and `d` lies in the arc.
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have hu_mono : Monotone (fun j : ℤ => (N : ℝ) * cyclicLift X j) :=
    fun x y hxy => mul_le_mul_of_nonneg_left ((cyclicLift_strictMono X).monotone hxy) hN0
  have hbetween : ∀ j : ℤ, c ≤ j → j ≤ d → a < (N : ℝ) * cyclicLift X j ∧
      (N : ℝ) * cyclicLift X j < a + r := by
    intro j h1 h2
    exact ⟨lt_of_lt_of_le hc1 (hu_mono h1), lt_of_le_of_lt (hu_mono h2) hd2⟩
  have hspan : d - c < ((N : ℕ) : ℤ) := span_lt_period hrN hcd hc1 hd2
  set L : ℕ := (d - c).toNat with hL_def
  have hL : c + (L : ℤ) = d := by omega
  have hLN : L < (N : ℕ) := by omega
  -- Particles of the arc are the residues of the run `c, …, d`.
  have hPimg : ∀ i : Fin (N : ℕ), i ∈ P ↔ ∃ j ∈ Finset.Icc c d, residueFin N j = i := by
    intro i
    constructor
    · intro hi
      obtain ⟨n, hn⟩ := (hPmem i).mp hi
      refine ⟨(i : ℕ) + n * ((N : ℕ) : ℤ), ?_, residueFin_add_int_mul i n⟩
      rw [Finset.mem_Icc]
      exact ⟨Finset.min'_le F _ hn, Finset.le_max' F _ hn⟩
    · rintro ⟨j, hj, hmod⟩
      rw [Finset.mem_Icc] at hj
      have hjT := hbetween j hj.1 hj.2
      have hmi : residueFin N ((i : ℕ) : ℤ) = i := by simpa using residueFin_add_int_mul i 0
      obtain ⟨n, hn⟩ := exists_int_mul_of_residueFin_eq (N := N) (j := j) (j' := ((i : ℕ) : ℤ))
        (by rw [hmod, hmi])
      rw [hPmem]
      refine ⟨-n, ?_⟩
      have hshift : (i : ℕ) + (-n) * ((N : ℕ) : ℤ) = j := by linarith
      rw [hshift, hmemF]
      exact hjT
  have hPeq : P = (Finset.Icc c d).image (residueFin N) := by
    ext i
    rw [Finset.mem_image]
    exact hPimg i
  -- The residues of the run are distinct, since the run spans less than one period.
  have hinj : Set.InjOn (residueFin N) (Finset.Icc c d : Set ℤ) := by
    intro j hj j' hj' hjj'
    rw [Finset.mem_coe, Finset.mem_Icc] at hj hj'
    obtain ⟨n, hn⟩ := exists_int_mul_of_residueFin_eq hjj'
    have hn0 : n = 0 := by
      rcases lt_trichotomy n 0 with h | h | h
      · exfalso
        nlinarith
      · exact h
      · exfalso
        nlinarith
    simp only [hn0, zero_mul, add_zero] at hn
    exact hn.symm
  have hcardP : P.card = L + 1 := by
    rw [hPeq, Finset.card_image_of_injOn hinj, Int.card_Icc]
    omega
  -- The gaps of the run sum to less than `r`.
  have hsum_lt : ∑ r ∈ Finset.range L, gap X (c + (r : ℤ)) < r := by
    rw [sum_gap_eq_lift_sub, hL, mul_sub]
    simp only [hu] at hc1 hd2
    linarith
  have hJ := card_pow_le_sum_inv_pow (Finset.range L) (fun r : ℕ => gap X (c + (r : ℤ)))
    (fun r _ => gap_pos X _) q hr hsum_lt.le
  rw [Finset.card_range] at hJ
  -- Comparing the run with the particles of the arc.
  have hcomp : ∑ r ∈ Finset.range L, gap X (c + (r : ℤ)) ^ (-(q : ℤ)) ≤
      ∑ i ∈ P, gap X (i : ℕ) ^ (-(q : ℤ)) := by
    have hφP : ∀ r ∈ Finset.range L, residueFin N (c + (r : ℤ)) ∈ P := by
      intro r hr
      rw [hPimg]
      have hrL : r < L := Finset.mem_range.mp hr
      exact ⟨c + (r : ℤ), by rw [Finset.mem_Icc]; constructor <;> omega, rfl⟩
    have hφinj : Set.InjOn (fun r : ℕ => residueFin N (c + (r : ℤ))) (Finset.range L : Set ℕ) := by
      intro r hr r' hr' h
      rw [Finset.mem_coe, Finset.mem_range] at hr hr'
      have hx : c + (r : ℤ) ∈ (Finset.Icc c d : Set ℤ) := by
        rw [Finset.mem_coe, Finset.mem_Icc]; constructor <;> omega
      have hx' : c + (r' : ℤ) ∈ (Finset.Icc c d : Set ℤ) := by
        rw [Finset.mem_coe, Finset.mem_Icc]; constructor <;> omega
      have := hinj hx hx' h
      omega
    calc ∑ r ∈ Finset.range L, gap X (c + (r : ℤ)) ^ (-(q : ℤ))
        = ∑ r ∈ Finset.range L, gap X (((residueFin N (c + (r : ℤ)) : Fin (N : ℕ)) : ℕ) : ℤ) ^
            (-(q : ℤ)) := by
          refine Finset.sum_congr rfl (fun r _ => ?_)
          rw [gap_eq_residueFin]
      _ = ∑ i ∈ (Finset.range L).image (fun r : ℕ => residueFin N (c + (r : ℤ))),
            gap X ((i : ℕ) : ℤ) ^ (-(q : ℤ)) := by
          rw [Finset.sum_image hφinj]
      _ ≤ ∑ i ∈ P, gap X (i : ℕ) ^ (-(q : ℤ)) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => ?_)
          · intro i hi
            rw [Finset.mem_image] at hi
            obtain ⟨r, hr, rfl⟩ := hi
            exact hφP r hr
          · exact zpow_nonneg (gap_pos X _).le _
  -- Conclusion.
  have hLHS : max (loopCount a r X - 1) 0 = (L : ℝ) := by
    have h1 : (P.card : ℝ) - 1 = (L : ℝ) := by
      rw [hcardP]
      push_cast
      ring
    rw [hcount, h1, max_eq_left (Nat.cast_nonneg L)]
  rw [hLHS]
  calc (L : ℝ) ^ (q + 1) ≤ r ^ q * ∑ r ∈ Finset.range L, gap X (c + (r : ℤ)) ^ (-(q : ℤ)) := hJ
    _ ≤ r ^ q * ∑ i ∈ P, gap X (i : ℕ) ^ (-(q : ℤ)) := mul_le_mul_of_nonneg_left hcomp hr_nonneg

end Riesz1

end
end
