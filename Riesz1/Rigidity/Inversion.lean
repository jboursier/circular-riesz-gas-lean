/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Rigidity.Gaps
public import Riesz1.Frozen.ArcCount
public import Mathlib.Analysis.Normed.Group.AddCircle

/-!
# Count inversion at an interval boundary

This is part of Theorem 1. The preceding label `J`
of the left endpoint `a - ℓ` is the largest integer `j` with `x_j ≤ a - ℓ`, computed in the
real lift `leftLift a ℓ ∈ [0, 1)` of `a - ℓ`. The open arc count `M` of `arcCount`
equals the number of particles `x_{J+1}, …, x_{J+N}` that lie below `a - ℓ + 2ℓ`. A count
`M` above `2K + λ` (or below `2K - λ`) then forces a block of gaps or the gap `y_J` to deviate.
-/

@[expose] public section

open MeasureTheory Finset

namespace Riesz1

variable {N : ℕ+}

/-! ### The real lift of the left endpoint -/

/-- The representative of the left endpoint `a - ℓ` in `[0, 1)`. -/
noncomputable def leftLift (a : UnitAddCircle) (ℓ : ℝ) : ℝ :=
  (AddCircle.equivIco (1 : ℝ) 0 (a - (ℓ : UnitAddCircle)) : ℝ)

/-- The lift `leftLift a ℓ` lies in `[0, 1)`. -/
theorem leftLift_mem (a : UnitAddCircle) (ℓ : ℝ) : 0 ≤ leftLift a ℓ ∧ leftLift a ℓ < 1 := by
  have h := (AddCircle.equivIco (1 : ℝ) 0 (a - (ℓ : UnitAddCircle))).2
  simpa [leftLift, Set.mem_Ico] using h

/-- The lift `leftLift a ℓ` projects to the left endpoint `a - ℓ` on the circle. -/
theorem coe_leftLift (a : UnitAddCircle) (ℓ : ℝ) :
    ((leftLift a ℓ : ℝ) : UnitAddCircle) = a - (ℓ : UnitAddCircle) := by
  simp [leftLift]

/-- Adding `ℓ` to the lift of `a - ℓ` gives a lift of `a`. -/
theorem coe_leftLift_add (a : UnitAddCircle) (ℓ : ℝ) :
    ((leftLift a ℓ + ℓ : ℝ) : UnitAddCircle) = a := by
  rw [AddCircle.coe_add, coe_leftLift, sub_add_cancel]

/-! ### The preceding label -/

/-- The preceding label `J` of the left endpoint `a - ℓ`: the largest integer `j` with
`x_j ≤ leftLift a ℓ`. Its value is unique, so it is canonical. The gap and block-length
functions depend on `J` only through its class modulo `N`. -/
noncomputable def precedingLabel (a : UnitAddCircle) (ℓ : ℝ) (X : Configuration N) : ℤ :=
  sSup {j : ℤ | cyclicLift X j ≤ leftLift a ℓ}

/-! ### Properties of the preceding label -/

/-- The lift at index zero is the paper's `x_1`. -/
theorem cyclicLift_zero (X : Configuration N) : cyclicLift X 0 = X.val ⟨0, N.pos⟩ := by
  simpa using cyclicLift_add_mul X N.pos 0

/-- The first lift lies in `[0, 1)`. -/
theorem cyclicLift_zero_mem (X : Configuration N) :
    0 ≤ cyclicLift X 0 ∧ cyclicLift X 0 < 1 := by
  rw [cyclicLift_zero]
  obtain ⟨-, h0, h1, -⟩ := X.2
  exact ⟨h0, h1⟩

/-- The set of indices whose lifts do not exceed `b ∈ [0, 1)` is nonempty. -/
theorem liftSet_nonempty (X : Configuration N) {b : ℝ} (hb : 0 ≤ b) :
    {j : ℤ | cyclicLift X j ≤ b}.Nonempty := by
  refine ⟨-((N : ℕ) : ℤ), ?_⟩
  have h := cyclicLift_add_N X (-((N : ℕ) : ℤ))
  rw [neg_add_cancel] at h
  have h0 := cyclicLift_zero_mem X
  show cyclicLift X (-((N : ℕ) : ℤ)) ≤ b
  linarith [h0.1, h0.2]

/-- The set of indices whose lifts do not exceed `b ∈ [0, 1)` is bounded above by `N`. -/
theorem liftSet_bddAbove (X : Configuration N) {b : ℝ} (hb : b < 1) :
    BddAbove {j : ℤ | cyclicLift X j ≤ b} := by
  refine ⟨((N : ℕ) : ℤ), fun j hj => ?_⟩
  by_contra hlt
  have hlt' : ((N : ℕ) : ℤ) < j := not_le.mp hlt
  have hj' : cyclicLift X j ≤ b := hj
  have h1 : cyclicLift X ((N : ℕ) : ℤ) ≤ cyclicLift X j :=
    (cyclicLift_strictMono X).monotone hlt'.le
  have h2 := cyclicLift_add_N X 0
  rw [zero_add] at h2
  have h3 := cyclicLift_zero_mem X
  linarith [h3.1]

/-- The supremum of the indices whose lifts do not exceed `b ∈ [0, 1)` is one such index,
and the next index lies strictly above `b`. -/
theorem preceding_spec (X : Configuration N) {b : ℝ} (hb : 0 ≤ b) (hb' : b < 1) :
    cyclicLift X (sSup {j : ℤ | cyclicLift X j ≤ b}) ≤ b ∧
      b < cyclicLift X (sSup {j : ℤ | cyclicLift X j ≤ b} + 1) := by
  have hmem := Int.csSup_mem (liftSet_nonempty X hb) (liftSet_bddAbove X hb')
  refine ⟨hmem, ?_⟩
  by_contra h
  rw [not_lt] at h
  have hmem2 : sSup {j : ℤ | cyclicLift X j ≤ b} + 1 ∈ {j : ℤ | cyclicLift X j ≤ b} := h
  have hle := le_csSup (liftSet_bddAbove X hb') hmem2
  linarith

/-- The supremum of the indices whose lifts do not exceed `b ∈ [0, 1)` equals `n` exactly
when `x_n ≤ b < x_{n+1}`. -/
theorem preceding_eq_iff (X : Configuration N) {b : ℝ} (hb : 0 ≤ b) (hb' : b < 1) (n : ℤ) :
    sSup {j : ℤ | cyclicLift X j ≤ b} = n ↔
      cyclicLift X n ≤ b ∧ b < cyclicLift X (n + 1) := by
  constructor
  · rintro rfl
    exact preceding_spec X hb hb'
  · rintro ⟨h1, h2⟩
    refine IsGreatest.csSup_eq ⟨h1, fun j hj => ?_⟩
    have hj' : cyclicLift X j ≤ b := hj
    by_contra hlt
    have hlt' : n < j := not_le.mp hlt
    have := (cyclicLift_strictMono X).monotone (show n + 1 ≤ j by omega)
    linarith

/-- The preceding label is a measurable function of the configuration. -/
theorem measurable_precedingLabel (a : UnitAddCircle) (ℓ : ℝ) :
    Measurable fun X : Configuration N => precedingLabel a ℓ X := by
  have hb := leftLift_mem a ℓ
  refine measurable_to_countable' fun n => ?_
  have hset : (fun X : Configuration N => precedingLabel a ℓ X) ⁻¹' {n}
      = {X : Configuration N | cyclicLift X n ≤ leftLift a ℓ ∧
          leftLift a ℓ < cyclicLift X (n + 1)} := by
    ext X
    exact preceding_eq_iff X hb.1 hb.2 n
  rw [hset]
  exact (measurableSet_le (measurable_cyclicLift n) measurable_const).inter
    (measurableSet_lt measurable_const (measurable_cyclicLift (n + 1)))

/-! ### Distance to an arc on the circle -/

/-- For a point `u` in `(b, b + 1]`, its distance to the center `b + ℓ` is below `ℓ` exactly
when `u` lies below `b + 2ℓ`. The arc `(b, b + 2ℓ)` is the open arc of radius `ℓ`. -/
theorem dist_window_iff {b ℓ u : ℝ} (hℓ : 0 < ℓ) (hℓ2 : ℓ ≤ 1 / 2) (hu0 : b < u)
    (hu1 : u ≤ b + 1) :
    dist (u : UnitAddCircle) ((b + ℓ : ℝ) : UnitAddCircle) < ℓ ↔ u < b + 2 * ℓ := by
  have hsub : (u : UnitAddCircle) - ((b + ℓ : ℝ) : UnitAddCircle)
      = ((u - (b + ℓ) : ℝ) : UnitAddCircle) := by
    rw [AddCircle.coe_sub]
  rw [dist_eq_norm, hsub, UnitAddCircle.norm_eq]
  set t := u - (b + ℓ) with ht
  have ht1 : -ℓ < t := by linarith
  have ht2 : t ≤ 1 - ℓ := by linarith
  rcases lt_or_ge t (1 / 2) with h | h
  · have hr : round t = 0 := by
      rw [round_eq, Int.floor_eq_zero_iff, Set.mem_Ico]
      constructor <;> linarith
    rw [hr, Int.cast_zero, sub_zero, abs_lt]
    constructor
    · rintro ⟨-, h2⟩
      linarith
    · intro h'
      exact ⟨ht1, by linarith⟩
  · have hr : round t = 1 := by
      rw [round_eq, Int.floor_eq_iff]
      constructor <;> norm_num <;> linarith
    rw [hr, Int.cast_one, abs_lt]
    constructor
    · rintro ⟨h1, -⟩
      exfalso
      linarith
    · intro h'
      exfalso
      linarith

/-- For a lift `cyclicLift X j` in `(leftLift a ℓ, leftLift a ℓ + 1]`, the particle lies in the
open arc of radius `ℓ` about `a` exactly when its lift lies below `leftLift a ℓ + 2ℓ`. -/
theorem cyclicLift_window_iff {ℓ : ℝ} (hℓ : 0 < ℓ) (hℓ2 : ℓ ≤ 1 / 2) (a : UnitAddCircle)
    (X : Configuration N) (j : ℤ) (hj0 : leftLift a ℓ < cyclicLift X j)
    (hj1 : cyclicLift X j ≤ leftLift a ℓ + 1) :
    dist (cyclicLift X j : UnitAddCircle) a < ℓ ↔
      cyclicLift X j < leftLift a ℓ + 2 * ℓ := by
  have h := dist_window_iff (b := leftLift a ℓ) hℓ hℓ2 hj0 hj1
  rwa [coe_leftLift_add] at h

/-! ### Counting the particles in the arc -/

/-- For a downward closed predicate `p` on `ℕ`, the predicate `p r` holds for `r < N` exactly when
`r` is below the number of `s < N` with `p s`. -/
theorem lt_card_filter_iff {M : ℕ} (p : ℕ → Prop) [DecidablePred p]
    (hp : ∀ r r', r ≤ r' → p r' → p r) {r : ℕ} (hr : r < M) :
    p r ↔ r < ((range M).filter p).card := by
  constructor
  · intro h
    have hsub : range (r + 1) ⊆ (range M).filter p := by
      intro s hs
      rw [mem_range] at hs
      rw [mem_filter, mem_range]
      exact ⟨by omega, hp s r (by omega) h⟩
    have := Finset.card_le_card hsub
    rw [card_range] at this
    omega
  · intro h
    by_contra hpr
    have hsub : (range M).filter p ⊆ range r := by
      intro s hs
      rw [mem_filter] at hs
      rw [mem_range]
      by_contra hsr
      exact hpr (hp r s (not_lt.mp hsr) hs.2)
    have := Finset.card_le_card hsub
    rw [card_range] at this
    omega

/-- A sum of an `N`-periodic function over `N` consecutive integers does not depend on the start. -/
theorem sum_range_shift (G : ℤ → ℝ) (hG : ∀ j, G (j + ((N : ℕ) : ℤ)) = G j) (c : ℤ) :
    ∑ r ∈ range (N : ℕ), G (c + r) = ∑ r ∈ range (N : ℕ), G r := by
  have key : ∀ c : ℤ, ∑ r ∈ range (N : ℕ), G (c + 1 + r)
      = ∑ r ∈ range (N : ℕ), G (c + r) := by
    intro c
    have h1 := Finset.sum_range_succ' (fun r : ℕ => G (c + r)) (N : ℕ)
    have h2 := Finset.sum_range_succ (fun r : ℕ => G (c + r)) (N : ℕ)
    have h3 : ∑ r ∈ range (N : ℕ), G (c + 1 + r)
        = ∑ r ∈ range (N : ℕ), G (c + ((r + 1 : ℕ) : ℤ)) :=
      Finset.sum_congr rfl fun r _ => by
        congr 1
        push_cast
        ring
    have h4 : G (c + ((N : ℕ) : ℤ)) = G c := hG c
    rw [h3]
    simp only [Nat.cast_zero, add_zero] at h1
    linarith
  have hconst : ∀ c : ℤ, ∑ r ∈ range (N : ℕ), G (c + r) = ∑ r ∈ range (N : ℕ), G (0 + r) := by
    intro c
    refine Int.induction_on c ?_ ?_ ?_
    · simp
    · intro i ih
      exact (key _).trans ih
    · intro i ih
      have h := key (-(i : ℤ) - 1)
      rw [sub_add_cancel] at h
      rw [← h]
      exact ih
  rw [hconst c]
  simp only [zero_add]

/-- The number of particles in the open arc equals the number of indices `r < N` whose lift
`x_{J+1+r}` lies below `leftLift a ℓ + 2ℓ`. -/
theorem arcCount_eq_card (a : UnitAddCircle) (ℓ : ℝ) (X : Configuration N) (hℓ : 0 < ℓ)
    (hℓ2 : ℓ ≤ 1 / 2) :
    arcCount a ℓ X = (((range (N : ℕ)).filter
      (fun r : ℕ => cyclicLift X (precedingLabel a ℓ X + 1 + r)
        < leftLift a ℓ + 2 * ℓ)).card : ℝ) := by
  have hb := leftLift_mem a ℓ
  obtain ⟨hJ1, hJ2⟩ : cyclicLift X (precedingLabel a ℓ X) ≤ leftLift a ℓ ∧
      leftLift a ℓ < cyclicLift X (precedingLabel a ℓ X + 1) :=
    preceding_spec X hb.1 hb.2
  set J := precedingLabel a ℓ X with hJ
  set b := leftLift a ℓ with hbdef
  set G : ℤ → ℝ := fun j => if dist (cyclicLift X j : UnitAddCircle) a < ℓ then 1 else 0
    with hG
  have hGper : ∀ j, G (j + ((N : ℕ) : ℤ)) = G j := by
    intro j
    simp only [hG, cyclicLift_add_N, AddCircle.coe_add_period]
  have hcard : arcCount a ℓ X = ∑ n ∈ range (N : ℕ), G (n : ℤ) := by
    rw [← Fin.sum_univ_eq_sum_range]
    unfold arcCount
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [hG, cyclicLift_natCast]
  have hshift : ∑ n ∈ range (N : ℕ), G (n : ℤ) = ∑ r ∈ range (N : ℕ), G (J + 1 + r) :=
    (sum_range_shift G hGper (J + 1)).symm
  have hwin : ∑ r ∈ range (N : ℕ), G (J + 1 + r)
      = ∑ r ∈ range (N : ℕ), (if cyclicLift X (J + 1 + r) < b + 2 * ℓ then (1 : ℝ) else 0) := by
    refine Finset.sum_congr rfl fun r hr => ?_
    have hr' : (r : ℤ) < ((N : ℕ) : ℤ) := by
      have := Finset.mem_range.mp hr
      exact_mod_cast this
    have hlo : b < cyclicLift X (J + 1 + r) :=
      lt_of_lt_of_le hJ2 ((cyclicLift_strictMono X).monotone (by omega))
    have hhi : cyclicLift X (J + 1 + r) ≤ b + 1 := by
      have h1 : cyclicLift X (J + 1 + r) ≤ cyclicLift X (J + ((N : ℕ) : ℤ)) :=
        (cyclicLift_strictMono X).monotone (by omega)
      rw [cyclicLift_add_N] at h1
      linarith
    simp only [hG, hbdef, cyclicLift_window_iff hℓ hℓ2 a X (J + 1 + r) hlo hhi]
  have hcount : ∑ r ∈ range (N : ℕ),
      (if cyclicLift X (J + 1 + r) < b + 2 * ℓ then (1 : ℝ) else 0)
      = (((range (N : ℕ)).filter
          (fun r : ℕ => cyclicLift X (J + 1 + r) < b + 2 * ℓ)).card : ℝ) :=
    Finset.sum_boole _ _
  rw [hcard, hshift, hwin, hcount]

/-- The window count: for `1 ≤ k ≤ N`, the lift `x_{J+k}` lies below `leftLift a ℓ + 2ℓ` exactly
when `k` is at most the number `M` of particles in the open arc. -/
theorem window_iff (a : UnitAddCircle) (ℓ : ℝ) (X : Configuration N) {k : ℕ} (hk1 : 1 ≤ k)
    (hkN : k ≤ (N : ℕ)) :
    cyclicLift X (precedingLabel a ℓ X + k) < leftLift a ℓ + 2 * ℓ ↔
      k ≤ ((range (N : ℕ)).filter
        (fun r : ℕ => cyclicLift X (precedingLabel a ℓ X + 1 + r)
          < leftLift a ℓ + 2 * ℓ)).card := by
  have hb := leftLift_mem a ℓ
  obtain ⟨hJ1, hJ2⟩ : cyclicLift X (precedingLabel a ℓ X) ≤ leftLift a ℓ ∧
      leftLift a ℓ < cyclicLift X (precedingLabel a ℓ X + 1) :=
    preceding_spec X hb.1 hb.2
  obtain ⟨r, rfl⟩ : ∃ r, k = r + 1 := ⟨k - 1, by omega⟩
  have hr : r < (N : ℕ) := by omega
  have hshift : precedingLabel a ℓ X + ((r + 1 : ℕ) : ℤ)
      = precedingLabel a ℓ X + 1 + (r : ℤ) := by
    push_cast
    ring
  rw [hshift, Nat.add_one_le_iff]
  refine lt_card_filter_iff (M := (N : ℕ))
    (fun r : ℕ => cyclicLift X (precedingLabel a ℓ X + 1 + r) < leftLift a ℓ + 2 * ℓ)
    (fun r r' hrr' h => ?_) hr
  have h1 : precedingLabel a ℓ X + 1 + (r : ℤ) ≤ precedingLabel a ℓ X + 1 + (r' : ℤ) := by
    have : (r : ℤ) ≤ (r' : ℤ) := by exact_mod_cast hrr'
    omega
  exact lt_of_le_of_lt ((cyclicLift_strictMono X).monotone h1) h

/-! ### Index arithmetic -/

/-- The indices `k₊ = ⌈2K + λ⌉` lie in `[1, N)` and satisfy `K ≤ min(k₊, N - k₊) ≤ 3K`. -/
theorem plus_index_bounds (N : ℕ+) {lam K : ℝ} (hlam : 2 ≤ lam)
    (hK4 : K ≤ ((N : ℕ) : ℝ) / 4) (hKlam : lam + 1 ≤ K) :
    1 ≤ ⌈2 * K + lam⌉₊ ∧ ⌈2 * K + lam⌉₊ < (N : ℕ) ∧
      K ≤ min (⌈2 * K + lam⌉₊ : ℝ) (((N : ℕ) : ℝ) - ⌈2 * K + lam⌉₊) ∧
      min (⌈2 * K + lam⌉₊ : ℝ) (((N : ℕ) : ℝ) - ⌈2 * K + lam⌉₊) ≤ 3 * K := by
  have hk1 : 2 * K + lam ≤ (⌈2 * K + lam⌉₊ : ℝ) := Nat.le_ceil _
  have hk2 : (⌈2 * K + lam⌉₊ : ℝ) < 2 * K + lam + 1 :=
    Nat.ceil_lt_add_one (by linarith)
  have hK3 : 3 ≤ K := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · have : (1 : ℝ) ≤ (⌈2 * K + lam⌉₊ : ℝ) := by linarith
    exact_mod_cast this
  · have : (⌈2 * K + lam⌉₊ : ℝ) < ((N : ℕ) : ℝ) := by linarith
    exact_mod_cast this
  · exact le_min (by linarith) (by linarith)
  · exact le_trans (min_le_left _ _) (by linarith)

/-- The indices `k₋ = ⌊2K - λ⌋ + 1` lie in `[1, N)` and satisfy `K ≤ min(k₋, N - k₋) ≤ 3K`. -/
theorem minus_index_bounds (N : ℕ+) {lam K : ℝ} (hlam : 2 ≤ lam)
    (hK4 : K ≤ ((N : ℕ) : ℝ) / 4) (hKlam : lam + 1 ≤ K) :
    1 ≤ ⌊2 * K - lam⌋₊ + 1 ∧ ⌊2 * K - lam⌋₊ + 1 < (N : ℕ) ∧
      K ≤ min ((⌊2 * K - lam⌋₊ + 1 : ℕ) : ℝ) (((N : ℕ) : ℝ) - ((⌊2 * K - lam⌋₊ + 1 : ℕ) : ℝ)) ∧
      min ((⌊2 * K - lam⌋₊ + 1 : ℕ) : ℝ) (((N : ℕ) : ℝ) - ((⌊2 * K - lam⌋₊ + 1 : ℕ) : ℝ))
        ≤ 3 * K := by
  have hf1 : ((⌊2 * K - lam⌋₊ : ℕ) : ℝ) ≤ 2 * K - lam :=
    Nat.floor_le (by linarith)
  have hf2 : 2 * K - lam < (⌊2 * K - lam⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hK3 : 3 ≤ K := by linarith
  have hcast : ((⌊2 * K - lam⌋₊ + 1 : ℕ) : ℝ) = (⌊2 * K - lam⌋₊ : ℝ) + 1 := by
    push_cast
    ring
  refine ⟨Nat.succ_pos _, ?_, ?_, ?_⟩
  · have : ((⌊2 * K - lam⌋₊ + 1 : ℕ) : ℝ) < ((N : ℕ) : ℝ) := by
      rw [hcast]
      linarith
    exact_mod_cast this
  · rw [hcast]
    exact le_min (by linarith) (by linarith)
  · rw [hcast]
    exact le_trans (min_le_left _ _) (by linarith)

/-! ### The deterministic count inversion -/

/-- Deterministic count inversion (part of Theorem 1).
Let `K = Nℓ` and `λ ≥ 2` with `λ + 1 ≤ K`, and let `X` have no particle at the endpoints
`a ± ℓ`. If the open arc count `M` satisfies `|M - 2K| ≥ λ`, then either the gap `y_J` of the
preceding label exceeds `λ/2`, or one of the block lengths `S_{J,k₊}`, `S_{J,k₋}` deviates from
its index by at least `λ/2`.

The endpoint hypothesis `_hX` is a null-event assumption. The proof does not use
it: the preceding label is defined by the weak inequality `x_J ≤ a - ℓ`, which covers a particle
at either endpoint. -/
theorem almost_optimal_rigidity_inversion (N : ℕ+) (a : UnitAddCircle) {ℓ lam K : ℝ}
    (hℓ : 0 < ℓ) (hℓ4 : ℓ ≤ 1 / 4) (hlam : 2 ≤ lam) (hK : K = ((N : ℕ) : ℝ) * ℓ)
    (hKlam : lam + 1 ≤ K) (X : Configuration N)
    (_hX : ∀ i : Fin (N : ℕ), ((X.val i : ℝ) : UnitAddCircle) ≠ a - ℓ ∧
      ((X.val i : ℝ) : UnitAddCircle) ≠ a + ℓ) :
    lam ≤ |arcCount a ℓ X - 2 * K| →
      lam / 2 < gap X (precedingLabel a ℓ X) ∨
        lam / 2 ≤ |blockLength X (precedingLabel a ℓ X) ⌈2 * K + lam⌉₊
          - ((⌈2 * K + lam⌉₊ : ℕ) : ℝ)| ∨
        lam / 2 ≤ |blockLength X (precedingLabel a ℓ X) (⌊2 * K - lam⌋₊ + 1)
          - ((⌊2 * K - lam⌋₊ + 1 : ℕ) : ℝ)| := by
  intro hM
  have hN0 : (0 : ℝ) < ((N : ℕ) : ℝ) := by exact_mod_cast N.pos
  have hℓ2 : ℓ ≤ 1 / 2 := by linarith
  have hN4 : K ≤ ((N : ℕ) : ℝ) / 4 := by
    rw [hK]
    have := mul_le_mul_of_nonneg_left hℓ4 hN0.le
    linarith
  have hb := leftLift_mem a ℓ
  obtain ⟨hJ1, hJ2⟩ : cyclicLift X (precedingLabel a ℓ X) ≤ leftLift a ℓ ∧
      leftLift a ℓ < cyclicLift X (precedingLabel a ℓ X + 1) :=
    preceding_spec X hb.1 hb.2
  obtain ⟨hp1, hpN, -, -⟩ := plus_index_bounds N hlam hN4 hKlam
  obtain ⟨hm1, hmN, -, -⟩ := minus_index_bounds N hlam hN4 hKlam
  obtain ⟨m, hm⟩ : ∃ m : ℕ, ((range (N : ℕ)).filter
      (fun r : ℕ => cyclicLift X (precedingLabel a ℓ X + 1 + r)
        < leftLift a ℓ + 2 * ℓ)).card = m :=
    ⟨_, rfl⟩
  rw [arcCount_eq_card a ℓ X hℓ hℓ2, hm] at hM
  have hgap_d : ((N : ℕ) : ℝ) * (leftLift a ℓ - cyclicLift X (precedingLabel a ℓ X))
      < gap X (precedingLabel a ℓ X) := by
    have hg : gap X (precedingLabel a ℓ X)
        = ((N : ℕ) : ℝ) * (cyclicLift X (precedingLabel a ℓ X + 1)
          - cyclicLift X (precedingLabel a ℓ X)) := rfl
    rw [hg]
    exact mul_lt_mul_of_pos_left (by linarith) hN0
  have hd_nonneg : 0 ≤ ((N : ℕ) : ℝ) * (leftLift a ℓ - cyclicLift X (precedingLabel a ℓ X)) :=
    mul_nonneg hN0.le (by linarith)
  rcases le_abs.mp hM with hA | hB
  · -- Case `M ≥ 2K + λ`: the particle `J + k₊` lies in the arc.
    have hkm : ⌈2 * K + lam⌉₊ ≤ m := Nat.ceil_le.mpr (by linarith)
    have hlt : cyclicLift X (precedingLabel a ℓ X + (⌈2 * K + lam⌉₊ : ℕ)) < leftLift a ℓ + 2 * ℓ := by
      rw [window_iff a ℓ X hp1 hpN.le, hm]
      exact hkm
    have hS_lt : blockLength X (precedingLabel a ℓ X) ⌈2 * K + lam⌉₊
        < 2 * K + ((N : ℕ) : ℝ) * (leftLift a ℓ - cyclicLift X (precedingLabel a ℓ X)) := by
      have hS : blockLength X (precedingLabel a ℓ X) ⌈2 * K + lam⌉₊
          = ((N : ℕ) : ℝ) * (cyclicLift X (precedingLabel a ℓ X + (⌈2 * K + lam⌉₊ : ℕ))
            - cyclicLift X (precedingLabel a ℓ X)) := rfl
      rw [hS]
      have h := mul_lt_mul_of_pos_left hlt hN0
      linarith
    by_cases hg : lam / 2 < gap X (precedingLabel a ℓ X)
    · exact Or.inl hg
    · right
      left
      rw [not_lt] at hg
      have hk_ge : 2 * K + lam ≤ ((⌈2 * K + lam⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
      have h' : lam / 2 ≤ -(blockLength X (precedingLabel a ℓ X) ⌈2 * K + lam⌉₊
          - ((⌈2 * K + lam⌉₊ : ℕ) : ℝ)) := by
        linarith
      exact le_abs.mpr (Or.inr h')
  · -- Case `M ≤ 2K - λ`: the particle `J + k₋` lies beyond the arc.
    have hmle : (m : ℝ) ≤ 2 * K - lam := by linarith
    have hmfl : m ≤ ⌊2 * K - lam⌋₊ := Nat.le_floor hmle
    have hnot : ¬ cyclicLift X (precedingLabel a ℓ X + ((⌊2 * K - lam⌋₊ + 1 : ℕ) : ℤ))
        < leftLift a ℓ + 2 * ℓ := by
      rw [window_iff a ℓ X hm1 hmN.le, hm]
      omega
    have hnot' : leftLift a ℓ + 2 * ℓ
        ≤ cyclicLift X (precedingLabel a ℓ X + ((⌊2 * K - lam⌋₊ + 1 : ℕ) : ℤ)) :=
      not_lt.mp hnot
    have hS_ge : 2 * K ≤ blockLength X (precedingLabel a ℓ X) (⌊2 * K - lam⌋₊ + 1) := by
      have hS : blockLength X (precedingLabel a ℓ X) (⌊2 * K - lam⌋₊ + 1)
          = ((N : ℕ) : ℝ) * (cyclicLift X (precedingLabel a ℓ X + ((⌊2 * K - lam⌋₊ + 1 : ℕ) : ℤ))
            - cyclicLift X (precedingLabel a ℓ X)) := rfl
      rw [hS]
      have h := mul_le_mul_of_nonneg_left hnot' hN0.le
      linarith
    have hk_le : ((⌊2 * K - lam⌋₊ + 1 : ℕ) : ℝ) ≤ 2 * K - lam + 1 := by
      have := Nat.floor_le (show 0 ≤ 2 * K - lam by linarith)
      push_cast
      linarith
    right
    right
    have h' : lam / 2 ≤ blockLength X (precedingLabel a ℓ X) (⌊2 * K - lam⌋₊ + 1)
        - ((⌊2 * K - lam⌋₊ + 1 : ℕ) : ℝ) := by
      linarith
    exact le_abs.mpr (Or.inl h')

end Riesz1

end
