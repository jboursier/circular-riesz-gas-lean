/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.APrioriGoodGradientVanishing
public import Riesz1.Variance.NearestForcing

/-!
# The anchored good-event cutoff `η*`

The proof of Lemma 5.2 works with the anchored cutoff `η*(y) = η(0, y)`: the good-event cutoff
evaluated at the anchored configuration whose first particle sits at `0`. The anchored
coordinates `y` are those of `Anch_N` (`anchorMap`), so `y_j = x_{j+1} - x_1`.

The cutoff must be a total function of `y` on `Fin (N - 1) → ℝ` (the carrier of the anchored law),
so `η*` is defined through the gap vector of the lift `(0, y)` on all of `Fin N → ℝ`, with the
cyclic convention of `cyclicLift`. On the image of `anchorMap` this agrees with `goodCutoff`
(`anchoredCutoff_anchorMap`). The file also records measurability and the range `[0, 1]`.

Main declarations: `Riesz1.anchoredLift`, `Riesz1.liftedAt`, `Riesz1.vectorGap`,
`Riesz1.anchoredCutoff`, with `Riesz1.anchoredCutoff_anchorMap`, `Riesz1.measurable_anchoredCutoff`,
`Riesz1.anchoredCutoff_nonneg` and `Riesz1.anchoredCutoff_le_one`.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Riesz1

variable {N : ℕ+}

/-- The lift `(0, y_1, …, y_{N-1})` of an anchored vector `y`: the anchor sits at index `0`, and
index `k ≥ 1` carries `y_{k-1}`. -/
def anchoredLift (N : ℕ+) (y : Fin ((N : ℕ) - 1) → ℝ) : Fin (N : ℕ) → ℝ :=
  fun k => if h : (k : ℕ) = 0 then 0 else y ⟨(k : ℕ) - 1, by have := k.isLt; omega⟩

/-- The cyclic lift `j ↦ x_{j mod N} + ⌊j / N⌋` of a vector `x` on `N` labels, with the convention
of `cyclicLift`. For a configuration `X` it is `cyclicLift X j`. -/
def liftedAt (N : ℕ+) (x : Fin (N : ℕ) → ℝ) (j : ℤ) : ℝ :=
  x ⟨(j % (N : ℕ)).toNat, by
    have h := Int.emod_lt_of_pos j (show (0 : ℤ) < (N : ℕ) by exact_mod_cast N.pos)
    exact_mod_cast (Int.toNat_lt (Int.emod_nonneg j (by exact_mod_cast N.ne_zero))).mpr h⟩ +
      (j / (N : ℕ) : ℤ)

/-- The gap `N (x_{i+1} - x_i)` of a vector `x` at the label `i`, with the cyclic lift of `liftedAt`.
For a configuration `X` this is `gap X i`. -/
def vectorGap (N : ℕ+) (x : Fin (N : ℕ) → ℝ) (i : Fin (N : ℕ)) : ℝ :=
  ((N : ℕ) : ℝ) * (liftedAt N x (((i : ℕ) : ℤ) + 1) - liftedAt N x ((i : ℕ) : ℤ))

/-- The anchored cutoff `η*(y) = η(0, y)`: the good-event cutoff with
parameters `s`, `K`, `γ`, `ε`, evaluated at the gap vector of the lift `(0, y)`. It is defined on
all of `Fin (N - 1) → ℝ`. -/
def anchoredCutoff (N : ℕ+) (s K γ ε : ℝ) (y : Fin ((N : ℕ) - 1) → ℝ) : ℝ :=
  gapCutoff N s K γ ε (vectorGap N (anchoredLift N y))

/-! ### Bridge to the good-event cutoff -/

/-- The lift of the anchored image of a configuration is the configuration shifted by its first
coordinate. -/
theorem anchoredLift_anchorMap (X : Configuration N) :
    anchoredLift N (anchorMap N X) = fun k => X.val k - X.val ⟨0, N.pos⟩ := by
  funext k
  unfold anchoredLift
  by_cases h : (k : ℕ) = 0
  · have hk : k = ⟨0, N.pos⟩ := Fin.ext h
    subst hk
    simp
  · simp only [h, ↓reduceDIte]
    have hk : (((k : ℕ) - 1 : ℕ) : ℤ) + 1 = ((k : ℕ) : ℤ) := by omega
    have hzero : cyclicLift X 0 = X.val ⟨0, N.pos⟩ := by
      simpa using cyclicLift_natCast X ⟨0, N.pos⟩
    show cyclicLift X ((((k : ℕ) - 1 : ℕ) : ℤ) + 1) - cyclicLift X 0 =
      X.val k - X.val ⟨0, N.pos⟩
    rw [hk, cyclicLift_natCast X k, hzero]

/-- The lift of a shifted configuration is the cyclic lift of the configuration minus its first
coordinate. -/
theorem liftedAt_sub (X : Configuration N) (j : ℤ) :
    liftedAt N (fun k => X.val k - X.val ⟨0, N.pos⟩) j =
      cyclicLift X j - X.val ⟨0, N.pos⟩ := by
  simp only [liftedAt, cyclicLift]
  ring

/-- On the anchored image, the gap vector of the lift is the gap vector of the configuration. -/
theorem vectorGap_anchorMap (X : Configuration N) (i : Fin (N : ℕ)) :
    vectorGap N (anchoredLift N (anchorMap N X)) i = gap X ((i : ℕ) : ℤ) := by
  rw [anchoredLift_anchorMap]
  unfold vectorGap gap
  rw [liftedAt_sub, liftedAt_sub]
  ring

/-- **Bridge.** The anchored cutoff at the anchored image of a configuration is the good-event
cutoff of that configuration, so `η*(Anch_N X) = η(X)`. -/
theorem anchoredCutoff_anchorMap (s K γ ε : ℝ) (X : Configuration N) :
    anchoredCutoff N s K γ ε (anchorMap N X) = goodCutoff N s K γ ε X := by
  rw [goodCutoff_eq_gapCutoff]
  unfold anchoredCutoff
  congr 1
  funext i
  exact vectorGap_anchorMap X i

/-! ### Range and measurability -/

/-- The anchored cutoff is nonnegative at every anchored vector. -/
theorem anchoredCutoff_nonneg (s K γ ε : ℝ) (y : Fin ((N : ℕ) - 1) → ℝ) :
    0 ≤ anchoredCutoff N s K γ ε y :=
  gapCutoff_nonneg s K γ ε _

/-- The anchored cutoff is at most one at every anchored vector. -/
theorem anchoredCutoff_le_one (s K γ ε : ℝ) (y : Fin ((N : ℕ) - 1) → ℝ) :
    anchoredCutoff N s K γ ε y ≤ 1 :=
  gapCutoff_le_one s K γ ε _

/-- Each coordinate of the anchored lift is measurable in `y`. -/
theorem measurable_anchoredLift_apply (k : Fin (N : ℕ)) :
    Measurable fun y : Fin ((N : ℕ) - 1) → ℝ => anchoredLift N y k := by
  by_cases h : (k : ℕ) = 0
  · unfold anchoredLift
    simp only [h, ↓reduceDIte]
    exact measurable_const
  · unfold anchoredLift
    simp only [h, ↓reduceDIte]
    exact measurable_pi_apply _

/-- Each entry of the gap vector of the anchored lift is measurable in `y`. -/
theorem measurable_vectorGap (i : Fin (N : ℕ)) :
    Measurable fun y : Fin ((N : ℕ) - 1) → ℝ => vectorGap N (anchoredLift N y) i := by
  unfold vectorGap liftedAt
  refine measurable_const.mul ((Measurable.add_const ?_ _).sub (Measurable.add_const ?_ _))
  · exact measurable_anchoredLift_apply _
  · exact measurable_anchoredLift_apply _

/-- The gap cutoff, as a function of the gap vector, is measurable. -/
theorem measurable_gapPairDev_fun (p : Fin (N : ℕ) × ℤ) :
    Measurable fun z : Fin (N : ℕ) → ℝ => gapPairDev N z p := by
  unfold gapPairDev gapOrientedSum
  exact (((Finset.measurable_sum _ fun r _ => measurable_pi_apply (labelOf N r)).sub
    (Finset.measurable_sum _ fun r _ => measurable_pi_apply (labelOf N r))).sub measurable_const)

/-- The gap cutoff is measurable on the space of gap vectors. -/
theorem measurable_gapCutoff (s K γ ε : ℝ) :
    Measurable fun z : Fin (N : ℕ) → ℝ => gapCutoff N s K γ ε z := by
  have hsc : Measurable scalarCutoff := by
    unfold scalarCutoff
    fun_prop
  have hcoord : ∀ i : Fin (N : ℕ), Measurable fun z : Fin (N : ℕ) → ℝ => z i :=
    fun i => measurable_pi_apply i
  have hpair : ∀ p : Fin (N : ℕ) × ℤ, Measurable fun z : Fin (N : ℕ) → ℝ =>
      scalarCutoff (2 * |gapPairDev N z p| / pairScale s K ε p) := by
    intro p
    have hdev := measurable_gapPairDev_fun p
    fun_prop
  unfold gapCutoff
  refine Measurable.mul (Finset.measurable_prod _ fun p _ => hpair p) ?_
  refine Finset.measurable_prod _ fun i _ => ?_
  refine Measurable.mul ?_ ?_
  · exact hsc.comp (((hcoord i).const_mul 2).div_const _)
  · exact hsc.comp (measurable_const.div (measurable_const.mul (hcoord i)))

/-- The anchored cutoff is measurable as a function of the anchored vector. -/
theorem measurable_anchoredCutoff (s K γ ε : ℝ) :
    Measurable fun y : Fin ((N : ℕ) - 1) → ℝ => anchoredCutoff N s K γ ε y :=
  (measurable_gapCutoff s K γ ε).comp (Measurable.of_eval fun i => measurable_vectorGap i)

end Riesz1

end
