/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.Sobolev
public import Riesz1.ToMathlib.Chamber.Periodization

/-!
# Periodic smooth tests from compactly supported Euclidean tests

Periodization gives elements of the smooth core of the Sobolev completion and of
the test class. Tests supported in the open
fundamental strip are unchanged in the fundamental representative.
-/

@[expose] public section

noncomputable section

open Set Function Metric Topology
open scoped ENNReal ContDiff

namespace Riesz1

theorem hsRotationVector_ne_zero (N : ℕ+) : hsRotationVector N ≠ 0 := by
  intro h
  have := congrArg (fun x : HsEuclidean N => x ⟨0, N.pos⟩) h
  simp [hsRotationVector] at this

theorem hsTranslate_eq_add_rotation {N : ℕ+} (t : ℝ) (x : HsEuclidean N) :
    hsTranslate t x = x + t • hsRotationVector N := by
  ext i
  simp [hsTranslate_apply, hsRotationVector]

theorem hsSmoothOnClosure_vectorPeriodize {N : ℕ+} {f : HsEuclidean N → ℝ}
    (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) :
    HsSmoothOnClosure N (vectorPeriodize (hsRotationVector N) (hsRotationVector_ne_zero N) f hs) :=
  ⟨fun k x => by
      rw [hsTranslate_eq_add_rotation]
      exact vectorPeriodize_periodic _ _ _ _ k x,
    univ, isOpen_univ, subset_univ _,
    (contDiff_vectorPeriodize (hsRotationVector_ne_zero N) hf hs).contDiffOn⟩

theorem hsSmoothValue_vectorPeriodize {N : ℕ+} {f : HsEuclidean N → ℝ}
    (hs : HasCompactSupport f)
    (hf : support f ⊆ {x | x ⟨0, N.pos⟩ ∈ Ioo (0 : ℝ) 1}) :
    hsSmoothValue (vectorPeriodize (hsRotationVector N) (hsRotationVector_ne_zero N) f hs) =
      hsSmoothValue f := by
  funext x
  apply vectorPeriodize_eq_on_strip (hsRotationVector_ne_zero N)
    (EuclideanSpace.proj ⟨0, N.pos⟩) (by simp [hsRotationVector]) hs hf
  exact (hsLiftPoint_mem_fundamentalRegion N x).2

/-- Compact interior support remains separated from all collision faces
after periodization, producing a member of the test class. -/
def hsTestFunctionOfCompact {N : ℕ+} (hN : 2 ≤ (N : ℕ)) {f : HsEuclidean N → ℝ}
    (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) (hU : tsupport f ⊆ hsChamber N) :
    HsTestFunction N where
  toFun := vectorPeriodize (hsRotationVector N) (hsRotationVector_ne_zero N) f hs
  smooth := contDiff_vectorPeriodize (hsRotationVector_ne_zero N) hf hs
  periodic k x := by
    rw [hsTranslate_eq_add_rotation]
    exact vectorPeriodize_periodic _ _ _ _ k x
  boundarySupport := by
    by_cases hne : (tsupport f).Nonempty
    · obtain ⟨y, hy, hmin⟩ := hs.isCompact.exists_isMinOn hne
        (hsBoundaryDistance_lipschitz N hN).continuous.continuousOn
      refine ⟨hsBoundaryDistance N hN y, hsBoundaryDistance_pos hN (hU hy), fun x hx => ?_⟩
      have hex : ∃ k : ℤ, f (x + (k : ℝ) • hsRotationVector N) ≠ 0 := by
        by_contra! h
        exact hx (by simp [vectorPeriodize, h])
      obtain ⟨k, hk⟩ := hex
      apply (ENNReal.ofReal_le_iff_le_toReal
        (infEDist_ne_top (hsChamber_compl_nonempty hN))).mpr
      have hm := hmin (subset_closure hk)
      change hsBoundaryDistance N hN y ≤
        hsBoundaryDistance N hN (x + (k : ℝ) • hsRotationVector N) at hm
      rw [← hsTranslate_eq_add_rotation, hsBoundaryDistance_translate] at hm
      exact hm
    · refine ⟨1, zero_lt_one, fun x hx => ?_⟩
      have hz : f = 0 := by
        funext y
        by_contra hy
        exact hne ⟨y, subset_closure hy⟩
      exact False.elim (hx (by simp [vectorPeriodize, hz]))

end Riesz1

end
