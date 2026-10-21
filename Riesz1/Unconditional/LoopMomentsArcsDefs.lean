/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopMomentsDefs

/-!
# Arcs of every endpoint type in `N𝕋`

The moment bounds of Lemma 5.8 quantify over every deterministic arc `J` of length `r`. The counts
`loopCount` and discrepancies `loopDiscrepancy` are defined for open arcs `microArc N a r` only.
This file defines

* `circleImage N I`, the image in `N𝕋` of a real set `I`,
* `IsMicroArc N r J`, the predicate that `J` is an arc of length `r`: the image of the open, closed
  or half-open interval with endpoints `a` and `a + r`, for some real `a`,
* `arcLoopCount J X` and `arcLoopDiscrepancy J X`, the count and the discrepancy of an arbitrary set
  `J ⊆ N𝕋`. The case `J = microArc N a r` gives `loopCount a r X` and `loopDiscrepancy a r X`.

It proves that an arc agrees with the open arc of the same endpoints at every point other than the
two endpoint images.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

namespace Riesz1

/-- The image in `N𝕋` of a real set `I`. -/
def circleImage (N : ℕ+) (I : Set ℝ) : Set (AddCircle (N : ℝ)) :=
  (fun t : ℝ => (t : AddCircle (N : ℝ))) '' I

/-- `J` is a deterministic arc of length `r` in `N𝕋`: for some real `a`, the set `J` is the image of
the open, closed or half-open interval with endpoints `a` and `a + r`. -/
def IsMicroArc (N : ℕ+) (r : ℝ) (J : Set (AddCircle (N : ℝ))) : Prop :=
  ∃ a : ℝ, J = circleImage N (Ioo a (a + r)) ∨ J = circleImage N (Icc a (a + r)) ∨
    J = circleImage N (Ico a (a + r)) ∨ J = circleImage N (Ioc a (a + r))

/-- The count `M_J = ∑_i 1_J(z_i)` of microscopic particles in an arbitrary set `J ⊆ N𝕋`. -/
def arcLoopCount {N : ℕ+} (J : Set (AddCircle (N : ℝ))) (X : Configuration N) : ℝ :=
  ∑ i : Fin (N : ℕ), if loopPos X i ∈ J then 1 else 0

/-- The discrepancy `ν(J) = M_J - |J|` of an arbitrary set `J ⊆ N𝕋`, where `|J|` is the Haar measure
of `J`, the arclength. -/
def arcLoopDiscrepancy {N : ℕ+} (J : Set (AddCircle (N : ℝ))) (X : Configuration N) : ℝ :=
  arcLoopCount J X - (volume J).toReal

/-! ### Open arcs are the special case -/

theorem circleImage_Ioo_eq_microArc (N : ℕ+) (a r : ℝ) :
    circleImage N (Ioo a (a + r)) = microArc N a r :=
  rfl

theorem arcLoopCount_microArc {N : ℕ+} (a r : ℝ) (X : Configuration N) :
    arcLoopCount (microArc N a r) X = loopCount a r X :=
  rfl

theorem arcLoopDiscrepancy_microArc {N : ℕ+} (a r : ℝ) (X : Configuration N) :
    arcLoopDiscrepancy (microArc N a r) X = loopDiscrepancy a r X :=
  rfl

/-! ### Arcs agree with the open arc away from the endpoints -/

/-- Let `I` lie between the open interval `(a, b)` and the closed interval `[a, b]`. A point of
`N𝕋` other than the images of `a` and `b` lies in the image of `I` exactly when it lies in the image
of `(a, b)`. -/
theorem mem_circleImage_iff_of_ne {N : ℕ+} {I : Set ℝ} {a b : ℝ}
    (h1 : Ioo a b ⊆ I) (h2 : I ⊆ Icc a b) {x : AddCircle (N : ℝ)}
    (ha : x ≠ (a : AddCircle (N : ℝ))) (hb : x ≠ (b : AddCircle (N : ℝ))) :
    x ∈ circleImage N I ↔ x ∈ circleImage N (Ioo a b) := by
  constructor
  · rintro ⟨t, ht, rfl⟩
    have hta : t ≠ a := fun h => ha (by rw [h])
    have htb : t ≠ b := fun h => hb (by rw [h])
    exact ⟨t, ⟨lt_of_le_of_ne (h2 ht).1 (Ne.symm hta), lt_of_le_of_ne (h2 ht).2 htb⟩, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, h1 ht, rfl⟩

/-- An arc `J` of length `r`, with endpoints `a` and `a + r`, agrees with the open arc `microArc N a r`
at every point of `N𝕋` other than the images of `a` and `a + r`. -/
theorem IsMicroArc.exists_agree {N : ℕ+} {r : ℝ} {J : Set (AddCircle (N : ℝ))}
    (hJ : IsMicroArc N r J) :
    ∃ a : ℝ, ∀ x : AddCircle (N : ℝ), x ≠ (a : AddCircle (N : ℝ)) →
      x ≠ ((a + r : ℝ) : AddCircle (N : ℝ)) → (x ∈ J ↔ x ∈ microArc N a r) := by
  obtain ⟨a, h⟩ := hJ
  refine ⟨a, fun x ha hb => ?_⟩
  rcases h with rfl | rfl | rfl | rfl
  · exact mem_circleImage_iff_of_ne subset_rfl Ioo_subset_Icc_self ha hb
  · exact mem_circleImage_iff_of_ne Ioo_subset_Icc_self subset_rfl ha hb
  · exact mem_circleImage_iff_of_ne Ioo_subset_Ico_self Ico_subset_Icc_self ha hb
  · exact mem_circleImage_iff_of_ne Ioo_subset_Ioc_self Ioc_subset_Icc_self ha hb

end Riesz1

end
end
