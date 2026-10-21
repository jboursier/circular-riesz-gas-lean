/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.SettingGeometry
public import Riesz1.Rigidity.GapLawSimplex

/-!
# The cyclic gap map on the configuration manifold

For `N ≥ 2` and a lift `x` of a configuration, the cyclic gap map is
`Gap_N(x) = N (x_2 - x_1, …, x_N - x_{N-1}, 1 + x_1 - x_N)`, written here with labels starting at
zero. Its carrier is the open simplex `{a ∈ (0, ∞)^N : ∑ a_i = N}`, which is `gapSimplex N`.

The gap map is defined on the whole Euclidean lift space, by the formula, and it is invariant under
every common real translation. On the fundamental region it is `gapVector`.
The image statements reuse the anchored chart `anchoredGapVector` and its inverse `gapCumulative`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Finset

namespace Riesz1

variable {N : ℕ+}

/-- The cyclic lift of a vector at an integer label: the entry at `j % N` shifted by `j / N`, so
that `x_{j + N} = x_j + 1`. This is `cyclicLift` for an arbitrary Euclidean vector, with no ordering
constraint. -/
def hsCyclicLift (x : HsEuclidean N) (j : ℤ) : ℝ :=
  x ⟨(j % (N : ℕ)).toNat, by
    have h := Int.emod_lt_of_pos j (show (0 : ℤ) < (N : ℕ) by exact_mod_cast N.pos)
    exact_mod_cast (Int.toNat_lt (Int.emod_nonneg j (by exact_mod_cast N.ne_zero))).mpr h⟩ +
      ((j / (N : ℕ) : ℤ) : ℝ)

/-- The cyclic gap map `Gap_N(x)_i = N (x_{i+1} - x_i)` with `x_N = x_0 + 1`, defined on the whole
Euclidean lift space. -/
def hsGap (x : HsEuclidean N) : Fin (N : ℕ) → ℝ :=
  fun i => ((N : ℕ) : ℝ) * (hsCyclicLift x (((i : ℕ) + 1 : ℕ) : ℤ) - hsCyclicLift x ((i : ℕ) : ℤ))

/-- For a label below `N`, the cyclic lift is the entry itself. -/
theorem hsCyclicLift_nat (x : HsEuclidean N) {m : ℕ} (hm : m < (N : ℕ)) :
    hsCyclicLift x (m : ℤ) = x ⟨m, hm⟩ := by
  have hm0 : (0 : ℤ) ≤ (m : ℤ) := by positivity
  have hmN : (m : ℤ) < (N : ℕ) := by exact_mod_cast hm
  unfold hsCyclicLift
  simp only [Int.emod_eq_of_lt hm0 hmN, Int.ediv_eq_zero_of_lt hm0 hmN, Int.toNat_natCast,
    Int.cast_zero, add_zero]

/-- At the label `N` the cyclic lift is the first entry shifted by one period. -/
theorem hsCyclicLift_card (x : HsEuclidean N) :
    hsCyclicLift x ((N : ℕ) : ℤ) = x ⟨0, N.pos⟩ + 1 := by
  have hN : ((N : ℕ) : ℤ) ≠ 0 := by exact_mod_cast N.ne_zero
  unfold hsCyclicLift
  simp

/-- Common real translations shift every cyclic lift by the same amount. -/
theorem hsCyclicLift_translate (t : ℝ) (x : HsEuclidean N) (j : ℤ) :
    hsCyclicLift (hsTranslate t x) j = hsCyclicLift x j + t := by
  unfold hsCyclicLift
  simp only [hsTranslate_apply]
  ring

/-- The cyclic gap map is invariant under every common real translation. -/
theorem hsGap_translate (t : ℝ) (x : HsEuclidean N) :
    hsGap (hsTranslate t x) = hsGap x := by
  funext i
  simp only [hsGap, hsCyclicLift_translate]
  ring

/-- The gaps sum to `N`, for every lift, by telescoping around the period. -/
theorem sum_hsGap (x : HsEuclidean N) : ∑ i, hsGap x i = ((N : ℕ) : ℝ) := by
  have htel := Finset.sum_range_sub (fun k : ℕ => hsCyclicLift x (k : ℤ)) (N : ℕ)
  have hfirst : hsCyclicLift x ((0 : ℕ) : ℤ) = x ⟨0, N.pos⟩ := hsCyclicLift_nat x N.pos
  have hlast : hsCyclicLift x ((N : ℕ) : ℤ) = x ⟨0, N.pos⟩ + 1 := hsCyclicLift_card x
  rw [hfirst, hlast] at htel
  have hsplit : ∑ i : Fin (N : ℕ), hsGap x i =
      ((N : ℕ) : ℝ) * ∑ i ∈ range (N : ℕ),
        (hsCyclicLift x (((i + 1 : ℕ)) : ℤ) - hsCyclicLift x (i : ℤ)) := by
    simp only [hsGap]
    rw [← Finset.mul_sum]
    congr 1
    exact Fin.sum_univ_eq_sum_range
      (fun i => hsCyclicLift x (((i + 1 : ℕ)) : ℤ) - hsCyclicLift x (i : ℤ)) (N : ℕ)
  rw [hsplit, htel]
  ring

/-- The gap map is the rigidity gap vector on the fundamental region. -/
theorem hsGap_eq_gapVector (X : Configuration N) :
    hsGap (WithLp.toLp 2 X.val) = gapVector X := by
  funext i
  simp only [hsGap, gapVector, gap, cyclicLift, hsCyclicLift]
  push_cast
  rfl

/-- On anchored lifts `(0, y)` the gap map is the anchored gap vector. -/
theorem hsGap_toLp_anchorVector (n : ℕ) (y : Fin n → ℝ) :
    hsGap (WithLp.toLp 2 (anchorVector y) : HsEuclidean n.succPNat) =
      anchoredGapVector n y := by
  funext i
  simp only [hsGap, anchoredGapVector, anchoredCyclicOffset, hsCyclicLift, Nat.succPNat_coe,
    Nat.cast_succ]

/-- The gap map of a chamber point is an element of the open simplex, with `N` the sum. -/
theorem hsGap_mem_gapSimplex {x : HsEuclidean N} (hx : x ∈ hsChamber N) :
    hsGap x ∈ gapSimplex N := by
  refine ⟨fun i => ?_, sum_hsGap x⟩
  have hi : (i : ℕ) < (N : ℕ) := i.isLt
  simp only [hsGap]
  apply mul_pos (by exact_mod_cast N.pos)
  by_cases hsucc : (i : ℕ) + 1 < (N : ℕ)
  · rw [hsCyclicLift_nat x hsucc, hsCyclicLift_nat x hi]
    have hlt : (⟨(i : ℕ), hi⟩ : Fin (N : ℕ)) < ⟨(i : ℕ) + 1, hsucc⟩ :=
      Fin.mk_lt_mk.mpr (Nat.lt_succ_self _)
    exact sub_pos.mpr (hx.1 hlt)
  · have hiN : (i : ℕ) + 1 = (N : ℕ) := by omega
    rw [hiN, hsCyclicLift_card, hsCyclicLift_nat x hi]
    have h := hx.2 ⟨(i : ℕ), hi⟩
    linarith

/-- The cyclic gap map is continuous, being affine on the Euclidean lift space. -/
theorem continuous_hsGap : Continuous (fun x : HsEuclidean N => hsGap x) := by
  refine continuous_pi fun i => ?_
  have hcont : ∀ j : ℤ, Continuous (fun x : HsEuclidean N => hsCyclicLift x j) := by
    intro j
    unfold hsCyclicLift
    exact (EuclideanSpace.proj _).continuous.add continuous_const
  simp only [hsGap]
  exact continuous_const.mul ((hcont _).sub (hcont _))

/-- Every point of the open simplex is the gap vector of a configuration of the fundamental
region. The configuration has first coordinate zero, and its other coordinates are the cumulative
gaps `gapCumulative`, which invert the anchored gap chart. -/
theorem exists_configuration_gapVector (a : Fin (N : ℕ) → ℝ) (ha : a ∈ gapSimplex N) :
    ∃ X : Configuration N, gapVector X = a := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, N = n.succPNat := ⟨N.natPred, (PNat.succPNat_natPred N).symm⟩
  have hdom := gapCumulative_mem_anchoredDomain n ha
  have hsum : ∑ i, a i = (n + 1 : ℝ) := ha.2.trans (by simp only [Nat.succPNat_coe, Nat.cast_succ])
  have hmem : anchorInverse n (0, gapCumulative n a) ∈ orderedDomain n.succPNat :=
    anchorInverse_mem n ⟨⟨le_refl 0, zero_lt_one⟩, hdom⟩
  refine ⟨⟨anchorInverse n (0, gapCumulative n a), hmem⟩, ?_⟩
  rw [gapVector_eq_anchoredGapVector]
  show anchoredGapVector n (anchorCoords n (anchorInverse n (0, gapCumulative n a))).2 = a
  rw [anchorCoords_anchorInverse]
  exact anchoredGapVector_gapCumulative n a hsum

/-- Every point of the open simplex is the gap vector of a chamber point. -/
theorem exists_hsGap_eq (a : Fin (N : ℕ) → ℝ) (ha : a ∈ gapSimplex N) :
    ∃ x ∈ hsChamber N, hsGap x = a := by
  obtain ⟨X, hX⟩ := exists_configuration_gapVector a ha
  obtain ⟨hmono, -, -, hlt⟩ := X.2
  refine ⟨WithLp.toLp 2 X.val, ⟨hmono, hlt⟩, ?_⟩
  rw [hsGap_eq_gapVector, hX]

/-- The cyclic gap map sends the chamber onto the open simplex `gapSimplex N`. The
image lies in the simplex (`hsGap_mem_gapSimplex`), and every point of the
simplex is attained. -/
theorem image_hsGap_chamber : hsGap '' hsChamber N = gapSimplex N := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact hsGap_mem_gapSimplex hx
  · intro a ha
    obtain ⟨x, hx, rfl⟩ := exists_hsGap_eq a ha
    exact ⟨x, hx, rfl⟩

/-- On the fundamental region, the gap map is onto the open simplex. Each configuration of the
fundamental region is the unique lift of a point of `D_N`, so this is the carrier statement. -/
theorem range_gapVector_eq_gapSimplex :
    Set.range (fun X : Configuration N => gapVector X) = gapSimplex N := by
  apply Set.Subset.antisymm
  · rintro _ ⟨X, rfl⟩
    show gapVector X ∈ gapSimplex N
    rw [← hsGap_eq_gapVector]
    obtain ⟨hmono, -, -, hlt⟩ := X.2
    exact hsGap_mem_gapSimplex (x := WithLp.toLp 2 X.val) ⟨hmono, hlt⟩
  · rintro a ha
    obtain ⟨X, hX⟩ := exists_configuration_gapVector a ha
    exact ⟨X, hX⟩

end Riesz1

end
end
