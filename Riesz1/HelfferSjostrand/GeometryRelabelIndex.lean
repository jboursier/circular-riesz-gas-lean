/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.GeometryHessian

/-!
# Cyclic relabeling of lifts: index arithmetic, chamber and boundary distance

A cyclic relabeling by `k` sends a lift `x` to `T_k x` with coordinates
`(T_k x)_i = x_{(i+k) mod N} + ⌊(i+k)/N⌋`, the convention of `cyclicLift`.
This file proves that `T_k` is an isometry of the Euclidean lift space which maps the open
chamber onto itself, and that it preserves the boundary distance. The pair-potential
identity and the admissibility transport are in the sibling files `GeometryRelabelPairs`
and `GeometryRelabelAdmissible`.

This is part of the proof of Lemma 3.6 (the cyclic relabeling
assertion).
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Finset
open scoped Topology

namespace Riesz1

/-- The cyclic index `(i + k) mod N`. -/
def hsCycIdx (N : ℕ+) (k : ℕ) (i : Fin (N : ℕ)) : Fin (N : ℕ) :=
  ⟨(i.val + k) % (N : ℕ), Nat.mod_lt _ N.pos⟩

/-- The integer shift `⌊(i + k)/N⌋` attached to the label `i`. -/
def hsCycShift (N : ℕ+) (k : ℕ) (i : Fin (N : ℕ)) : ℕ :=
  (i.val + k) / (N : ℕ)

/-- Cyclic relabeling of lifts: `(T_k x)_i = x_{(i+k) mod N} + ⌊(i+k)/N⌋`. -/
def hsRelabel (N : ℕ+) (k : ℕ) (x : HsEuclidean N) : HsEuclidean N :=
  WithLp.toLp 2 (fun i => x (hsCycIdx N k i) + (hsCycShift N k i : ℝ))

theorem hsRelabel_apply (N : ℕ+) (k : ℕ) (x : HsEuclidean N) (i : Fin (N : ℕ)) :
    hsRelabel N k x i = x (hsCycIdx N k i) + (hsCycShift N k i : ℝ) := rfl

/-- The index map is injective, hence bijective on the finite label set. -/
theorem hsCycIdx_injective (N : ℕ+) (k : ℕ) : Function.Injective (hsCycIdx N k) := by
  intro i j h
  have h' : (i.val + k) % (N : ℕ) = (j.val + k) % (N : ℕ) := congrArg Fin.val h
  have hm : i.val % (N : ℕ) = j.val % (N : ℕ) := Nat.ModEq.add_right_cancel' k h'
  apply Fin.ext
  calc i.val = i.val % (N : ℕ) := (Nat.mod_eq_of_lt i.isLt).symm
    _ = j.val % (N : ℕ) := hm
    _ = j.val := Nat.mod_eq_of_lt j.isLt

theorem hsCycIdx_bijective (N : ℕ+) (k : ℕ) : Function.Bijective (hsCycIdx N k) :=
  Finite.injective_iff_bijective.mp (hsCycIdx_injective N k)

/-- The label permutation of the cyclic relabeling by `k`. -/
def hsCycEquiv (N : ℕ+) (k : ℕ) : Fin (N : ℕ) ≃ Fin (N : ℕ) :=
  Equiv.ofBijective (hsCycIdx N k) (hsCycIdx_bijective N k)

/-- Pure arithmetic: for `i < j < n`, the shifted labels either share their quotient and keep
their order, or the larger one wraps, gaining one unit of shift and losing its order. -/
theorem cyc_dichotomy (n k i j : ℕ) (hn : 0 < n) (hj : j < n) (hij : i < j) :
    ((j + k) / n = (i + k) / n ∧ (i + k) % n < (j + k) % n) ∨
      ((j + k) / n = (i + k) / n + 1 ∧ (j + k) % n < (i + k) % n) := by
  have hA := Nat.div_add_mod (i + k) n
  have hB := Nat.div_add_mod (j + k) n
  have hr := Nat.mod_lt (i + k) hn
  have hs := Nat.mod_lt (j + k) hn
  generalize (i + k) / n = p at *
  generalize (j + k) / n = q at *
  generalize (i + k) % n = r at *
  generalize (j + k) % n = s at *
  have hpq : p ≤ q := by
    by_contra h
    push Not at h
    nlinarith
  have hqp : q ≤ p + 1 := by
    by_contra h
    push Not at h
    nlinarith
  rcases Nat.lt_or_ge q (p + 1) with h | h
  · have hq : q = p := by omega
    subst hq
    left
    refine ⟨rfl, ?_⟩
    nlinarith
  · have hq : q = p + 1 := by omega
    subst hq
    right
    refine ⟨rfl, ?_⟩
    nlinarith

/-- Coordinate order is preserved on pairs which do not wrap, and reversed on those that do. -/
theorem hsCycShift_sub_cases (N : ℕ+) (k : ℕ) {i j : Fin (N : ℕ)} (hij : i < j) :
    (hsCycShift N k j = hsCycShift N k i ∧ hsCycIdx N k i < hsCycIdx N k j) ∨
      (hsCycShift N k j = hsCycShift N k i + 1 ∧ hsCycIdx N k j < hsCycIdx N k i) := by
  have hi : i.val < (N : ℕ) := i.isLt
  have hj : j.val < (N : ℕ) := j.isLt
  have hlt : i.val < j.val := hij
  rcases cyc_dichotomy (N : ℕ) k i.val j.val N.pos hj hlt with h | h
  · left
    refine ⟨h.1, ?_⟩
    exact Fin.mk_lt_mk.mpr h.2
  · right
    refine ⟨?_, ?_⟩
    · unfold hsCycShift
      exact h.1
    · exact Fin.mk_lt_mk.mpr h.2

/-- The relabeled coordinates are strictly increasing on the chamber. -/
theorem hsRelabel_strictMono (N : ℕ+) (k : ℕ) {x : HsEuclidean N} (hx : x ∈ hsChamber N) :
    StrictMono (hsRelabel N k x) := by
  intro i j hij
  rw [hsRelabel_apply, hsRelabel_apply]
  rcases hsCycShift_sub_cases N k hij with ⟨hs, hlt⟩ | ⟨hs, hlt⟩
  · rw [hs]
    linarith [hx.1 hlt]
  · rw [hs]
    have h0 : x ⟨0, N.pos⟩ ≤ x (hsCycIdx N k j) :=
      hx.1.monotone (Fin.mk_le_mk.mpr (Nat.zero_le _))
    have h1 := hx.2 (hsCycIdx N k i)
    push_cast
    linarith [hx.1 hlt]

/-- Every relabeled coordinate lies less than one unit above the first one. -/
theorem hsRelabel_lt_zero_add_one (N : ℕ+) (k : ℕ) {x : HsEuclidean N} (hx : x ∈ hsChamber N)
    (j : Fin (N : ℕ)) : hsRelabel N k x j < hsRelabel N k x ⟨0, N.pos⟩ + 1 := by
  by_cases hj : j = ⟨0, N.pos⟩
  · subst hj
    linarith
  · have hlt : (⟨0, N.pos⟩ : Fin (N : ℕ)) < j :=
      lt_of_le_of_ne (Fin.le_iff_val_le_val.mpr (Nat.zero_le _)) (Ne.symm hj)
    rw [hsRelabel_apply, hsRelabel_apply]
    rcases hsCycShift_sub_cases N k hlt with ⟨hs, hord⟩ | ⟨hs, hord⟩
    · rw [hs]
      have h0 : x ⟨0, N.pos⟩ ≤ x (hsCycIdx N k ⟨0, N.pos⟩) :=
        hx.1.monotone (Fin.mk_le_mk.mpr (Nat.zero_le _))
      have h1 := hx.2 (hsCycIdx N k j)
      linarith [hx.1 hord]
    · rw [hs]
      push_cast
      linarith [hx.1 hord]

/-- The cyclic relabeling maps the open chamber into itself. -/
theorem hsRelabel_mem_chamber (N : ℕ+) (k : ℕ) {x : HsEuclidean N} (hx : x ∈ hsChamber N) :
    hsRelabel N k x ∈ hsChamber N :=
  ⟨hsRelabel_strictMono N k hx, fun j => hsRelabel_lt_zero_add_one N k hx j⟩

/-- Relabeling commutes with simultaneous real translations. -/
theorem hsRelabel_translate (N : ℕ+) (k : ℕ) (t : ℝ) (x : HsEuclidean N) :
    hsRelabel N k (hsTranslate t x) = hsTranslate t (hsRelabel N k x) := by
  ext i
  rw [hsRelabel_apply, hsTranslate_apply, hsTranslate_apply, hsRelabel_apply]
  ring

/-- Index identity: the second relabeling by `k'` undoes the first one up to the lattice. -/
theorem hsCycIdx_comp (N : ℕ+) (k k' t : ℕ) (hk : k + k' = (N : ℕ) * t) (i : Fin (N : ℕ)) :
    hsCycIdx N k' (hsCycIdx N k i) = i := by
  apply Fin.ext
  unfold hsCycIdx
  simp only
  rw [Nat.mod_add_mod, show i.val + k + k' = i.val + (N : ℕ) * t by omega,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt i.isLt]

/-- The shifts of the composite relabeling add up to the lattice translation `t`. -/
theorem cyc_shift_sum (N : ℕ+) (k k' t : ℕ) (hk : k + k' = (N : ℕ) * t) (i : Fin (N : ℕ)) :
    hsCycShift N k' (hsCycIdx N k i) + hsCycShift N k i = t := by
  unfold hsCycShift hsCycIdx
  simp only
  have hn : 0 < (N : ℕ) := N.pos
  have hA := Nat.div_add_mod (i.val + k) (N : ℕ)
  have hi := i.isLt
  have hq : (i.val + k) / (N : ℕ) ≤ t := by
    by_contra h
    push Not at h
    have hmul : (N : ℕ) * (t + 1) ≤ (N : ℕ) * ((i.val + k) / (N : ℕ)) :=
      Nat.mul_le_mul_left _ h
    have hexp : (N : ℕ) * (t + 1) = (N : ℕ) * t + (N : ℕ) := by ring
    linarith [Nat.zero_le ((i.val + k) % (N : ℕ)), Nat.zero_le k']
  obtain ⟨d, hd⟩ : ∃ d, t = (i.val + k) / (N : ℕ) + d := ⟨t - (i.val + k) / (N : ℕ), by omega⟩
  have hrk : (i.val + k) % (N : ℕ) + k' = i.val + (N : ℕ) * d := by
    nlinarith
  rw [hrk, Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt hi, zero_add, hd]
  ring

/-- Translating back and forth: the composite relabeling is a lattice translation. -/
theorem hsRelabel_relabel (N : ℕ+) (k k' t : ℕ) (hk : k + k' = (N : ℕ) * t)
    (y : HsEuclidean N) : hsRelabel N k (hsRelabel N k' y) = hsTranslate (t : ℝ) y := by
  ext i
  rw [hsRelabel_apply, hsRelabel_apply, hsTranslate_apply, hsCycIdx_comp N k k' t hk i]
  have hs : (hsCycShift N k' (hsCycIdx N k i) : ℝ) + (hsCycShift N k i : ℝ) = t := by
    exact_mod_cast cyc_shift_sum N k k' t hk i
  linarith

/-- The relabeling is an isometry of the Euclidean lift space. -/
theorem dist_hsRelabel (N : ℕ+) (k : ℕ) (x y : HsEuclidean N) :
    dist (hsRelabel N k x) (hsRelabel N k y) = dist x y := by
  rw [EuclideanSpace.dist_eq, EuclideanSpace.dist_eq]
  congr 1
  simp only [hsRelabel_apply, dist_add_right]
  exact (hsCycIdx_bijective N k).sum_comp (fun m => dist (x m) (y m) ^ 2)

theorem isometry_hsRelabel (N : ℕ+) (k : ℕ) : Isometry (hsRelabel N k) :=
  Isometry.of_dist_eq fun x y => dist_hsRelabel N k x y

/-- For every `k` there is a complementary shift `k'` with `k + k'` a multiple `N t` of `N`. -/
theorem exists_cyc_complement (N : ℕ+) (k : ℕ) : ∃ k' t : ℕ, k + k' = (N : ℕ) * t := by
  have hkk : k ≤ (N : ℕ) * (k / (N : ℕ) + 1) := by
    have h := Nat.div_add_mod k (N : ℕ)
    have hr := Nat.mod_lt k N.pos
    nlinarith
  exact ⟨(N : ℕ) * (k / (N : ℕ) + 1) - k, k / (N : ℕ) + 1, Nat.add_sub_cancel' hkk⟩

/-- Every point of the lift space is a relabeled point: the preimage is the composite relabeling
followed by the lattice translation back. -/
theorem hsRelabel_surjective (N : ℕ+) (k : ℕ) : Function.Surjective (hsRelabel N k) := by
  obtain ⟨k', t, hk⟩ := exists_cyc_complement N k
  intro y
  refine ⟨hsTranslate (-(t : ℝ)) (hsRelabel N k' y), ?_⟩
  rw [hsRelabel_translate, hsRelabel_relabel N k k' t hk, hsTranslate_add, neg_add_cancel,
    hsTranslate_zero]

/-- A point of the chamber has a preimage in the chamber. -/
theorem hsRelabel_exists_preimage (N : ℕ+) (k : ℕ) {y : HsEuclidean N} (hy : y ∈ hsChamber N) :
    ∃ x ∈ hsChamber N, hsRelabel N k x = y := by
  obtain ⟨k', t, hk⟩ := exists_cyc_complement N k
  refine ⟨hsTranslate (-(t : ℝ)) (hsRelabel N k' y), ?_, ?_⟩
  · exact (hsTranslate_mem_chamber_iff _ _).mpr (hsRelabel_mem_chamber N k' hy)
  · rw [hsRelabel_translate, hsRelabel_relabel N k k' t hk, hsTranslate_add, neg_add_cancel,
      hsTranslate_zero]

/-- The relabeling permutes the open chamber. -/
theorem hsRelabel_image_chamber (N : ℕ+) (k : ℕ) :
    hsRelabel N k '' hsChamber N = hsChamber N := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact hsRelabel_mem_chamber N k hx
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := hsRelabel_exists_preimage N k hy
    exact ⟨x, hx, rfl⟩

/-- The relabeling permutes the complement of the chamber. -/
theorem hsRelabel_image_compl (N : ℕ+) (k : ℕ) :
    hsRelabel N k '' (hsChamber N)ᶜ = (hsChamber N)ᶜ := by
  have hbij : Function.Bijective (hsRelabel N k) :=
    ⟨(isometry_hsRelabel N k).injective, hsRelabel_surjective N k⟩
  rw [Set.image_compl_eq hbij, hsRelabel_image_chamber]

/-- The boundary distance is invariant under cyclic relabeling. -/
theorem hsBoundaryDistance_relabel (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (k : ℕ) (x : HsEuclidean N) :
    hsBoundaryDistance N hN (hsRelabel N k x) = hsBoundaryDistance N hN x := by
  unfold hsBoundaryDistance
  conv_lhs => rw [← hsRelabel_image_compl N k]
  exact Metric.infDist_image (isometry_hsRelabel N k)

end Riesz1

end
