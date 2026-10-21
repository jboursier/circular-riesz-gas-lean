/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.GapMap
public import Riesz1.HelfferSjostrand.RadialDomainGeometry

/-!
# Gaps determine the radial coordinate, and functions of the gaps are rotation invariant

The gaps determine `z` uniquely on `e^⊥`, because the
successive differences fix `z` up to a common constant, and the zero-sum condition fixes that
constant. A measurable function of the gaps is the same as a measurable function invariant under
every common real translation `x ↦ x + t𝟏`.

The equivalence is stated on the chamber, which is the convention for functions on
`D_N`: a function on `D_N` is a function on the chamber invariant under the integer translations.
Here the invariance is under all real translations, the rotation group.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Riesz1

variable {N : ℕ+}

/-- Two vectors of `e^⊥` with equal gap vectors are equal. The gaps fix all successive
differences, so `z - w` is a constant vector. The zero-sum condition makes that constant zero. -/
theorem eq_of_hsGap_eq_of_mem_orth {z w : HsEuclidean N} (hz : z ∈ hsOrthSubspace N)
    (hw : w ∈ hsOrthSubspace N) (h : hsGap z = hsGap w) : z = w := by
  have hstep : ∀ k : ℕ, (hk : k + 1 < (N : ℕ)) →
      z ⟨k + 1, hk⟩ - z ⟨k, by omega⟩ = w ⟨k + 1, hk⟩ - w ⟨k, by omega⟩ := by
    intro k hk
    have hki : k < (N : ℕ) := by omega
    have hg := congrFun h ⟨k, hki⟩
    simp only [hsGap] at hg
    rw [hsCyclicLift_nat z hk, hsCyclicLift_nat z hki, hsCyclicLift_nat w hk,
      hsCyclicLift_nat w hki] at hg
    have hN0 : ((N : ℕ) : ℝ) ≠ 0 := by exact_mod_cast N.ne_zero
    exact mul_left_cancel₀ hN0 hg
  have hconst : ∀ k : ℕ, ∀ (hk : k < (N : ℕ)),
      z ⟨k, hk⟩ - w ⟨k, hk⟩ = z ⟨0, N.pos⟩ - w ⟨0, N.pos⟩ := by
    intro k
    induction k with
    | zero => intro hk; rfl
    | succ k ih =>
      intro hk
      have hk' : k < (N : ℕ) := by omega
      have h1 := ih hk'
      have h2 := hstep k hk
      linarith
  have hsum0 : ∑ i : Fin (N : ℕ), (z i - w i) = 0 := by
    simp only [Finset.sum_sub_distrib, sum_coord_eq_zero_of_mem_orth z hz,
      sum_coord_eq_zero_of_mem_orth w hw, sub_zero]
  have hsumC : ∑ i : Fin (N : ℕ), (z i - w i) =
      ∑ _i : Fin (N : ℕ), (z ⟨0, N.pos⟩ - w ⟨0, N.pos⟩) :=
    Finset.sum_congr rfl fun i _ => hconst i.1 i.2
  have hc : z ⟨0, N.pos⟩ - w ⟨0, N.pos⟩ = 0 := by
    have h1 := hsumC.symm.trans hsum0
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact absurd (by exact_mod_cast h2 : (N : ℕ) = 0) N.ne_zero
    · exact h2
  ext i
  have hi := hconst i.1 i.2
  linarith

/-- On the radial domain `B_N`, the gap map is injective: the gaps determine `z` uniquely. -/
theorem injOn_hsGap_radialDomain (N : ℕ+) :
    Set.InjOn (fun z : hsOrthSubspace N => hsGap (z : HsEuclidean N)) (hsRadialDomain N) := by
  intro z _ w _ h
  exact Subtype.ext (eq_of_hsGap_eq_of_mem_orth z.2 w.2 h)

/-- A common real translation of a chamber point stays in the chamber. -/
theorem translate_mem_hsChamber {x : HsEuclidean N} (hx : x ∈ hsChamber N) (t : ℝ) :
    hsTranslate t x ∈ hsChamber N :=
  (hsTranslate_mem_chamber_iff t x).mpr hx

/-- **Rotation invariance.** Let `f` be a function on the chamber, which is
the lift of `D_N`, measurable there. Then `f` is a measurable function of the cyclic gaps, that is
`f = g ∘ Gap_N` for some measurable `g`, if and only if `f` is invariant under every common real
translation `x ↦ x + t𝟏` of chamber points.

The gap map is a function of the rotation orbit, and conversely the orbit of a chamber point meets
the anchored section `s(a) = (0, ∑_{k<i} a_k / N)_i` in a single point, so the function can be read
off on the simplex by `s`. The chamber indicator is used so that `f` is only required to be
measurable on the chamber. -/
theorem exists_gapFunction_iff_rotation_invariant (f : HsEuclidean N → ℝ)
    (hf : Measurable ((hsChamber N).indicator f)) :
    (∃ g : (Fin (N : ℕ) → ℝ) → ℝ, Measurable g ∧ ∀ x ∈ hsChamber N, f x = g (hsGap x)) ↔
      ∀ x ∈ hsChamber N, ∀ t : ℝ, f (hsTranslate t x) = f x := by
  constructor
  · rintro ⟨g, -, hg⟩ x hx t
    rw [hg (hsTranslate t x) (translate_mem_hsChamber hx t), hg x hx, hsGap_translate]
  · intro hinv
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, N = n.succPNat := ⟨N.natPred, (PNat.succPNat_natPred N).symm⟩
    have hmeas : Measurable (fun a : Fin (n.succPNat : ℕ) → ℝ =>
        (WithLp.toLp 2 (anchorVector (gapCumulative n a)) : HsEuclidean n.succPNat)) :=
      (PiLp.continuous_toLp 2 _).measurable.comp
        ((measurable_anchorVector n).comp (continuous_gapCumulative n).measurable)
    refine ⟨fun a => (hsChamber n.succPNat).indicator f
        (WithLp.toLp 2 (anchorVector (gapCumulative n a))),
      hf.comp hmeas, ?_⟩
    intro x hx
    set y : Fin n → ℝ := fun j => x j.succ - x 0 with hy
    have hXy : WithLp.toLp 2 (anchorVector y) = hsTranslate (-x 0) x := by
      ext i
      induction i using Fin.cases with
      | zero =>
        change anchorVector y 0 = x 0 + -x 0
        rw [anchorVector_zero]
        ring
      | succ j =>
        change anchorVector y j.succ = x j.succ + -x 0
        rw [anchorVector_succ, hy]
        ring
    have hgap : hsGap x = anchoredGapVector n y := by
      rw [← hsGap_toLp_anchorVector, hXy, hsGap_translate]
    simp only
    rw [hgap, gapCumulative_anchoredGapVector, hXy,
      Set.indicator_of_mem (translate_mem_hsChamber hx (-x 0))]
    exact (hinv x hx (-x 0)).symm

end Riesz1

end
end
