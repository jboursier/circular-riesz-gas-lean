/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.APrioriRotationVariance
public import Riesz1.Gibbs.AnchoredCoordinates

/-!
# The anchored law `μ*` and the anchored law `anchoredLaw`

Part of Lemma 5.2 (the rotation part). The anchored law `μ*` of `APrioriRotationVariance` lives on
`Fin N → ℝ` with the coordinate of label zero fixed at `0`. The law `anchoredLaw P n` lives on
`Fin n → ℝ` with `n = N - 1`, the gaps `(x_{j+1} - x_0)_j` of the same configuration. The two
correspond through the prepended anchor `anchorVector = Fin.cons 0`, which is a measurable
embedding with left inverse `Fin.tail`:

* `rotAnchoredLaw_eq_map_anchorVector`: `μ* = (anchoredLaw P n).map anchorVector`.
* `map_tail_rotAnchoredLaw`: `μ*.map Fin.tail = anchoredLaw P n`.

The size-biasing weight on `anchoredLaw P n` is `w(y) = N y_1` (Lean index `0`, the paper's `y_2`),
and the mass and variance claims of `APrioriRotationVariance` hold on `anchoredLaw P n` with this
weight.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace Riesz1

/-- The prepended anchor is measurable, with codomain the type `Fin N → ℝ` of the anchored law. -/
theorem measurable_anchorVec (n : ℕ) :
    Measurable (anchorVector : (Fin n → ℝ) → (Fin (n.succPNat : ℕ) → ℝ)) :=
  measurable_anchorVector n

/-- The prepended anchored vector of a configuration is the anchored coordinates `(0, y)`. -/
theorem rotAnchorVec_eq_anchorVector (n : ℕ) (X : Configuration n.succPNat) :
    rotAnchorVec n.succPNat X = anchorVector (anchorCoords n X.val).2 := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [rotAnchorVec, anchorVector]
  · have h1 : cyclicLift X ((Fin.succ j : Fin (n.succPNat : ℕ)) : ℕ) = X.val (Fin.succ j) :=
      cyclicLift_natCast X _
    have h0 : cyclicLift X 0 = X.val 0 := cyclicLift_zero X
    show cyclicLift X ((Fin.succ j : Fin (n.succPNat : ℕ)) : ℕ) - cyclicLift X 0 =
      X.val (Fin.succ j) - X.val 0
    rw [h1, h0]

/-- The anchored law `μ*` is the image of `anchoredLaw P n` under the prepended anchor. -/
theorem rotAnchoredLaw_eq_map_anchorVector (P : Parameters) (n : ℕ) :
    rotAnchoredLaw P n.succPNat = (anchoredLaw P n).map anchorVector := by
  have hg : Measurable (fun X : Configuration n.succPNat => (anchorCoords n X.val).2) :=
    measurable_snd.comp (measurable_anchorCoords_config n)
  have hcomp : rotAnchorVec n.succPNat =
      anchorVector ∘ (fun X : Configuration n.succPNat => (anchorCoords n X.val).2) :=
    funext fun X => rotAnchorVec_eq_anchorVector n X
  unfold rotAnchoredLaw
  rw [hcomp, ← Measure.map_map (measurable_anchorVec n) hg, map_snd_gibbsMeasure]

/-- Removing the anchor from the anchored law `μ*` gives `anchoredLaw P n`. -/
theorem map_tail_rotAnchoredLaw (P : Parameters) (n : ℕ) :
    (rotAnchoredLaw P n.succPNat).map (Fin.tail : (Fin (n.succPNat : ℕ) → ℝ) → (Fin n → ℝ)) =
      anchoredLaw P n := by
  have hT : Measurable (Fin.tail : (Fin (n.succPNat : ℕ) → ℝ) → (Fin n → ℝ)) :=
    Measurable.of_eval fun i => measurable_pi_apply i.succ
  have hid : (Fin.tail : (Fin (n.succPNat : ℕ) → ℝ) → (Fin n → ℝ)) ∘ anchorVector = id :=
    funext fun y => funext fun i => anchorVector_succ y i
  calc (rotAnchoredLaw P n.succPNat).map (Fin.tail : (Fin (n.succPNat : ℕ) → ℝ) → (Fin n → ℝ))
      = ((anchoredLaw P n).map anchorVector).map Fin.tail := by
        rw [rotAnchoredLaw_eq_map_anchorVector]
    _ = (anchoredLaw P n).map (Fin.tail ∘ anchorVector) :=
        Measure.map_map hT (measurable_anchorVec n)
    _ = (anchoredLaw P n).map id := congrArg (fun f => (anchoredLaw P n).map f) hid
    _ = anchoredLaw P n := Measure.map_id

/-- The size-biasing weight `w(y) = N y_1`, with `y_1` the coordinate of index zero, that is
the paper's `y_2`. -/
def anchoredSizeWeight (n : ℕ) (hn : 0 < n) (y : Fin n → ℝ) : ℝ :=
  ((n.succPNat : ℕ) : ℝ) * y ⟨0, hn⟩

/-- The weight is the size-biasing weight of the anchored law at the prepended anchor. -/
theorem anchoredSizeWeight_eq (n : ℕ) (hn : 0 < n) (y : Fin n → ℝ) :
    anchoredSizeWeight n hn y =
      sizeBiasWeight n.succPNat (by simp; omega) (anchorVector y) := by
  unfold anchoredSizeWeight sizeBiasWeight anchorVector
  rfl

/-- The weight is measurable. -/
theorem measurable_anchoredSizeWeight (n : ℕ) (hn : 0 < n) :
    Measurable (anchoredSizeWeight n hn) :=
  measurable_const.mul (measurable_pi_apply _)

/-- **Mass claim on the anchored law**: `E_{μ*} N y_1 = 1` for `μ* = anchoredLaw`. -/
theorem integral_anchoredSizeWeight (P : Parameters) (n : ℕ) (hn : 0 < n) :
    ∫ y, anchoredSizeWeight n hn y ∂(anchoredLaw P n) = 1 := by
  have hN : 2 ≤ (n.succPNat : ℕ) := by simp; omega
  have hmap := integral_map (μ := anchoredLaw P n) (measurable_anchorVec n).aemeasurable
    (measurable_sizeBiasWeight n.succPNat hN).aestronglyMeasurable
  rw [← rotAnchoredLaw_eq_map_anchorVector,
    integral_sizeBiasWeight_rotAnchoredLaw P n.succPNat hN] at hmap
  simp only [anchoredSizeWeight_eq]
  exact hmap.symm

/-- The positive part of the weight has unit mean under the anchored law. -/
theorem integral_max_anchoredSizeWeight (P : Parameters) (n : ℕ) (hn : 0 < n) :
    ∫ y, max (anchoredSizeWeight n hn y) 0 ∂(anchoredLaw P n) = 1 := by
  have hN : 2 ≤ (n.succPNat : ℕ) := by simp; omega
  have hmeas : Measurable (fun z => max (sizeBiasWeight n.succPNat hN z) 0) :=
    (measurable_sizeBiasWeight _ hN).max measurable_const
  have hmap := integral_map (μ := anchoredLaw P n) (measurable_anchorVec n).aemeasurable
    hmeas.aestronglyMeasurable
  rw [← rotAnchoredLaw_eq_map_anchorVector, integral_max_sizeBiasWeight_rotAnchoredLaw P n.succPNat hN]
    at hmap
  simp only [anchoredSizeWeight_eq]
  exact hmap.symm

/-- The positive part of the weight is integrable under the anchored law. -/
theorem integrable_max_anchoredSizeWeight (P : Parameters) (n : ℕ) (hn : 0 < n) :
    Integrable (fun y => max (anchoredSizeWeight n hn y) 0) (anchoredLaw P n) := by
  have hN : 2 ≤ (n.succPNat : ℕ) := by simp; omega
  have hmeas : Measurable (fun z => max (sizeBiasWeight n.succPNat hN z) 0) :=
    (measurable_sizeBiasWeight _ hN).max measurable_const
  have hint : Integrable (fun z => max (sizeBiasWeight n.succPNat hN z) 0)
      ((anchoredLaw P n).map anchorVector) := by
    rw [← rotAnchoredLaw_eq_map_anchorVector]
    exact (integrable_sizeBiasWeight_rotAnchoredLaw P n.succPNat hN).pos_part
  have hcomp : (fun y => max (anchoredSizeWeight n hn y) 0) =
      (fun z => max (sizeBiasWeight n.succPNat hN z) 0) ∘ anchorVector :=
    funext fun y => by simp only [Function.comp_apply, anchoredSizeWeight_eq]
  rw [hcomp]
  exact (integrable_map_measure hmeas.aestronglyMeasurable
    (measurable_anchorVec n).aemeasurable).mp hint

/-- **Variance claim on the anchored law**: for a bounded measurable `T` on `Fin n → ℝ` with
`|T| ≤ M` and `κ > 0`,
`Var_{wμ*}(T) ≤ κ Var_{μ*}(T) + 4M² E_{μ*}[w 1_{w>κ}]`, with `w(y) = N y_1` and `μ* = anchoredLaw`. -/
theorem variance_anchoredSizeWeight (P : Parameters) (n : ℕ) (hn : 0 < n)
    {T : (Fin n → ℝ) → ℝ} (hT : Measurable T) {M : ℝ} (hTM : ∀ y, |T y| ≤ M) {κ : ℝ} (hκ : 0 < κ) :
    variance T ((anchoredLaw P n).withDensity fun y => ENNReal.ofReal (anchoredSizeWeight n hn y)) ≤
      κ * variance T (anchoredLaw P n) + 4 * M ^ 2 *
        ∫ y in {y | κ < anchoredSizeWeight n hn y}, anchoredSizeWeight n hn y ∂(anchoredLaw P n) := by
  have := isProbabilityMeasure_anchoredLaw P n
  set w := anchoredSizeWeight n hn with hw_def
  have hwm : Measurable (fun y => max (w y) 0) :=
    (measurable_anchoredSizeWeight n hn).max measurable_const
  have hofReal : ∀ x : ℝ, ENNReal.ofReal x = ENNReal.ofReal (max x 0) := by
    intro x
    rcases le_total x 0 with h | h
    · rw [max_eq_right h, ENNReal.ofReal_of_nonpos h, ENNReal.ofReal_zero]
    · rw [max_eq_left h]
  have hdens : (anchoredLaw P n).withDensity (fun y => ENNReal.ofReal (w y)) =
      (anchoredLaw P n).withDensity (fun y => ENNReal.ofReal (max (w y) 0)) := by
    have hfun : (fun y => ENNReal.ofReal (w y)) = (fun y => ENNReal.ofReal (max (w y) 0)) :=
      funext fun y => hofReal (w y)
    rw [hfun]
  have hset : {y | κ < max (w y) 0} = {y | κ < w y} := by
    ext y
    constructor
    · intro h
      have h0 : κ < max (w y) 0 := h
      rcases lt_max_iff.1 h0 with h' | h'
      · exact h'
      · exact absurd h' (not_lt.2 hκ.le)
    · intro h
      have h0 : κ < w y := h
      exact lt_max_of_lt_left h0
  have hint : ∫ y in {y | κ < w y}, max (w y) 0 ∂(anchoredLaw P n) =
      ∫ y in {y | κ < w y}, w y ∂(anchoredLaw P n) := by
    refine setIntegral_congr_fun ?_ fun y hy => ?_
    · exact measurableSet_lt measurable_const (measurable_anchoredSizeWeight n hn)
    · have hy' : κ < w y := hy
      exact max_eq_left (by linarith)
  rw [hdens]
  calc variance T ((anchoredLaw P n).withDensity fun y => ENNReal.ofReal (max (w y) 0))
      ≤ κ * variance T (anchoredLaw P n) + 4 * M ^ 2 *
          ∫ y in {y | κ < max (w y) 0}, max (w y) 0 ∂(anchoredLaw P n) :=
        variance_sizeBiased_le (anchoredLaw P n) hwm (fun y => le_max_right _ _)
          (integrable_max_anchoredSizeWeight P n hn) (integral_max_anchoredSizeWeight P n hn) hT hTM hκ
    _ = κ * variance T (anchoredLaw P n) + 4 * M ^ 2 *
        ∫ y in {y | κ < w y}, w y ∂(anchoredLaw P n) := by
        rw [hset, hint]

end Riesz1

end

end
