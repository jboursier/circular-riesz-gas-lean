/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.CLT.SelectionCyclic
public import Riesz1.CLT.SelectionVoronoi
public import Riesz1.Gibbs.AnchoredCoordinates
public import Riesz1.Rigidity.GapLaw

/-!
# The nearest-particle selection law

Part of the proof of Corollary 1, first claim of the selection argument: for every Borel `F` of
the gap vector that is nonnegative, `E F_J = E[w_1 F_1]`, where `J` is the nearest-particle label
and `F_i` is `F` applied to the gaps starting at label `i`. The bounded real case follows by
splitting `F` into its positive and negative parts.

The proof has three steps.

1. *Rotation.* The common rotation `X_0 (mod 1)` is uniform and independent of the anchored gap
   vector (`map_cyclicLift_anchorCoords_gibbsMeasure`). Conditioning on the gap vector and
   integrating the rotation gives, for every configuration, the Voronoi identity of
   `lintegral_nearestLabel_Ioc`: the nearest-label cells have lengths `w_i / N`.
2. *Cyclic invariance.* Each term `w_i F_i` has the same expectation as `w_0 F_0`
   (`lintegral_shiftFin_gapVector`), so the `N` terms with weight `1/N` sum to `E[w_0 F_0]`.
3. *Assembly.* The steps above give the identity for nonnegative `F`, and the real version for
   bounded `F`.

The external hypothesis `External.PrekopaLeindler` is not used here: the identity holds for every
Gibbs measure. It enters only in the moment bounds of the next file.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped ENNReal

namespace Riesz1

/-! ### The anchored offsets and gaps -/

/-- The anchored gap sequence is `(n+1)`-periodic in the label. -/
lemma anchoredGapAt_add_period (n : ℕ) (y : Fin n → ℝ) (j : ℤ) :
    anchoredGapAt n y (j + ((n.succPNat : ℕ) : ℤ)) = anchoredGapAt n y j := by
  unfold anchoredGapAt
  rw [show j + ((n.succPNat : ℕ) : ℤ) + 1 = (j + 1) + ((n.succPNat : ℕ) : ℤ) by ring,
    anchoredCyclicOffset_period, anchoredCyclicOffset_period]
  ring

/-- The anchored offsets increase whenever the anchored gaps are positive. -/
lemma anchoredCyclicOffset_strict (n : ℕ) (y : Fin n → ℝ) (hpos : ∀ j : ℤ, 0 < anchoredGapAt n y j)
    (j : ℤ) : anchoredCyclicOffset n y j < anchoredCyclicOffset n y (j + 1) := by
  have h := hpos j
  unfold anchoredGapAt at h
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have := (mul_pos_iff_of_pos_left hn).mp h
  linarith

/-! ### Measurability of the nearest label on the anchored coordinates -/

/-- The nearest label of the shifted anchored lifts is measurable in the shift and the anchored
coordinates. -/
lemma measurable_nearestLabel_anchored (n : ℕ) :
    Measurable (fun p : ℝ × (Fin n → ℝ) =>
      nearestLabelOf (fun j => p.1 + anchoredCyclicOffset n p.2 j)) := by
  have hLmeas : ∀ j : ℤ, Measurable (fun p : ℝ × (Fin n → ℝ) =>
      p.1 + anchoredCyclicOffset n p.2 j) := fun j =>
    measurable_fst.add ((measurable_anchoredCyclicOffset n j).comp measurable_snd)
  refine measurable_to_countable' fun k => ?_
  have hset : (fun p : ℝ × (Fin n → ℝ) =>
      nearestLabelOf (fun j => p.1 + anchoredCyclicOffset n p.2 j)) ⁻¹' {k} =
      {p | 0 ≤ (p.1 + anchoredCyclicOffset n p.2 k) + (p.1 + anchoredCyclicOffset n p.2 (k + 1))} ∩
        ⋂ i : ℤ, ⋂ (_ : i < k),
          {p | ¬ 0 ≤ (p.1 + anchoredCyclicOffset n p.2 i) +
            (p.1 + anchoredCyclicOffset n p.2 (i + 1))} := by
    ext p
    have hL : ∀ j : ℤ, (p.1 + anchoredCyclicOffset n p.2 (j + ((n.succPNat : ℕ) : ℤ))) =
        (p.1 + anchoredCyclicOffset n p.2 j) + 1 := fun j => by
      rw [anchoredCyclicOffset_period]
      ring
    have := nearestLabelOf_eq_iff_forall (N := (n.succPNat : ℕ)) (n.succPNat).pos
      (fun j => p.1 + anchoredCyclicOffset n p.2 j) hL k
    simp only [mem_preimage, mem_singleton_iff, mem_inter_iff, mem_ofPred_eq, mem_iInter]
    rw [this]
  rw [hset]
  refine (measurableSet_le measurable_const ((hLmeas k).add (hLmeas (k + 1)))).inter ?_
  refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ => ?_
  exact (measurableSet_le measurable_const ((hLmeas i).add (hLmeas (i + 1)))).compl

/-! ### The nearest-particle integrand on the anchored coordinates -/

/-- The integrand of the nearest-particle identity on the anchored coordinates: at shift `t` and
anchored gaps `y`, it is `F` of the gaps starting at the nearest label of the lifts `t + offset`. -/
def nearestIntegrand (n : ℕ) (F : (Fin (n.succPNat : ℕ) → ℝ) → ℝ) (t : ℝ) (y : Fin n → ℝ) :
    ℝ≥0∞ :=
  ENNReal.ofReal (F (fun k => anchoredGapAt n y
    (nearestLabelOf (fun j => t + anchoredCyclicOffset n y j) + ((k : ℕ) : ℤ))))

/-- The nearest-particle integrand is jointly measurable in the shift and the anchored
coordinates. -/
lemma measurable_nearestIntegrand (n : ℕ) (F : (Fin (n.succPNat : ℕ) → ℝ) → ℝ)
    (hF : Measurable F) :
    Measurable (fun p : ℝ × (Fin n → ℝ) => nearestIntegrand n F p.1 p.2) := by
  -- for each fixed label `j`, the gaps starting at `j` are measurable in the anchored coordinates
  have hslice : ∀ j : ℤ, Measurable (fun x : ℝ × (Fin n → ℝ) =>
      ENNReal.ofReal (F (fun k => anchoredGapAt n x.2 (j + ((k : ℕ) : ℤ))))) := by
    intro j
    have hgaps : Measurable (fun x : ℝ × (Fin n → ℝ) =>
        (fun k : Fin (n.succPNat : ℕ) => anchoredGapAt n x.2 (j + ((k : ℕ) : ℤ)))) :=
      Measurable.of_eval fun k => (measurable_anchoredGapAt n _).comp measurable_snd
    exact ENNReal.measurable_ofReal.comp (hF.comp hgaps)
  have hH : Measurable (fun q : (ℝ × (Fin n → ℝ)) × ℤ =>
      ENNReal.ofReal (F (fun k => anchoredGapAt n q.1.2 (q.2 + ((k : ℕ) : ℤ))))) :=
    measurable_from_prod_countable_left hslice
  have hJ := measurable_nearestLabel_anchored n
  have hcomp : Measurable (fun p : ℝ × (Fin n → ℝ) =>
      ((p, nearestLabelOf (fun j => p.1 + anchoredCyclicOffset n p.2 j)) :
        (ℝ × (Fin n → ℝ)) × ℤ)) :=
    measurable_id.prodMk hJ
  exact hH.comp hcomp

/-! ### The circle representative in `[0, 1)` -/

/-- The representative in `[0, 1)` of a point of the unit circle. -/
def circleRep (u : UnitAddCircle) : ℝ :=
  ((AddCircle.measurableEquivIco 1 0 u : Ico (0 : ℝ) (0 + 1)) : ℝ)

lemma measurable_circleRep : Measurable circleRep :=
  measurable_subtype_coe.comp (AddCircle.measurableEquivIco 1 0).measurable

lemma circleRep_coe {x : ℝ} (hx : x ∈ Ico (0 : ℝ) (0 + 1)) :
    circleRep (x : UnitAddCircle) = x := by
  unfold circleRep
  change ((AddCircle.equivIco 1 0 (x : UnitAddCircle) : Ico (0 : ℝ) (0 + 1)) : ℝ) = x
  rw [AddCircle.equivIco_coe_eq hx]

/-- The integral over the unit circle is the integral of the lift over `[0, 1)`. -/
lemma lintegral_circle_eq_Ico (f : UnitAddCircle → ℝ≥0∞) :
    ∫⁻ u, f u = ∫⁻ x in Ico (0 : ℝ) 1, f (x : UnitAddCircle) := by
  have h := UnitAddCircle.lintegral_preimage 0 f
  rw [zero_add] at h
  rw [← h, Measure.restrict_congr_set Ico_ae_eq_Ioc]

/-! ### The Voronoi identity for one configuration -/

/-- The offsets over two steps are the selection weight divided by the period. -/
lemma anchored_offset_weight {n : ℕ} (X : Configuration n.succPNat) (i : ℤ) :
    (anchoredCyclicOffset n (anchorCoords n X.val).2 (i + 1) -
      anchoredCyclicOffset n (anchorCoords n X.val).2 (i - 1)) / 2 =
      selectionWeight X i / ((n.succPNat : ℕ) : ℝ) := by
  have hg1 := gap_eq_anchoredGapAt n X i
  have hg0 := gap_eq_anchoredGapAt n X (i - 1)
  unfold selectionWeight
  rw [hg0, hg1]
  unfold anchoredGapAt
  rw [sub_add_cancel]
  have hN : ((n.succPNat : ℕ) : ℝ) = (n : ℝ) + 1 := by simp
  rw [hN]
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- The nearest-particle integral over one period, for positive anchored gaps. -/
lemma nearestIntegral_eq_sum (n : ℕ) (F : (Fin (n.succPNat : ℕ) → ℝ) → ℝ)
    (y : Fin n → ℝ) (hpos : ∀ j : ℤ, 0 < anchoredGapAt n y j) :
    ∫⁻ x in Ico (0 : ℝ) 1, nearestIntegrand n F x y =
      ∑ i : Fin (n.succPNat : ℕ),
        ENNReal.ofReal (F (fun k => anchoredGapAt n y (((i : ℕ) : ℤ) + ((k : ℕ) : ℤ)))) *
          ENNReal.ofReal ((anchoredCyclicOffset n y (((i : ℕ) : ℤ) + 1) -
            anchoredCyclicOffset n y (((i : ℕ) : ℤ) - 1)) / 2) := by
  have hper : ∀ j : ℤ, anchoredCyclicOffset n y (j + ((n.succPNat : ℕ) : ℤ)) =
      anchoredCyclicOffset n y j + 1 := fun j => anchoredCyclicOffset_period n y j
  have hmono : ∀ j : ℤ, anchoredCyclicOffset n y j < anchoredCyclicOffset n y (j + 1) :=
    fun j => anchoredCyclicOffset_strict n y hpos j
  have hc : ∀ j : ℤ, ENNReal.ofReal (F (fun k : Fin (n.succPNat : ℕ) =>
      anchoredGapAt n y (j + ((n.succPNat : ℕ) : ℤ) + ((k : ℕ) : ℤ)))) =
      ENNReal.ofReal (F (fun k : Fin (n.succPNat : ℕ) => anchoredGapAt n y (j + ((k : ℕ) : ℤ)))) := by
    intro j
    congr 3
    funext k
    rw [show j + ((n.succPNat : ℕ) : ℤ) + ((k : ℕ) : ℤ) = (j + ((k : ℕ) : ℤ)) +
      ((n.succPNat : ℕ) : ℤ) by ring, anchoredGapAt_add_period]
  rw [Measure.restrict_congr_set Ico_ae_eq_Ioc]
  exact lintegral_nearestLabel_Ioc (N := (n.succPNat : ℕ)) (n.succPNat).pos
    (anchoredCyclicOffset n y) hmono hper
    (fun j => ENNReal.ofReal (F (fun k : Fin (n.succPNat : ℕ) => anchoredGapAt n y (j + ((k : ℕ) : ℤ)))))
    hc

/-- The nearest-particle integral over one period of the rotation, at fixed anchored gaps. -/
def nearestIntegral (n : ℕ) (F : (Fin (n.succPNat : ℕ) → ℝ) → ℝ) (y : Fin n → ℝ) : ℝ≥0∞ :=
  ∫⁻ x in Ico (0 : ℝ) 1, nearestIntegrand n F x y

lemma measurable_nearestIntegral (n : ℕ) (F : (Fin (n.succPNat : ℕ) → ℝ) → ℝ)
    (hF : Measurable F) : Measurable (nearestIntegral n F) :=
  (measurable_nearestIntegrand n F hF).lintegral_prod_left'

/-- **Rotation Fubini.** Integrating the nearest-particle integrand over the configurations, with
the rotation `X_0 (mod 1)` and the anchored gaps independent and uniform, gives the integral of
the one-period integral over the anchored gaps. -/
lemma lintegral_nearestIntegrand_eq_nearestIntegral (P : Parameters) (n : ℕ)
    (F : (Fin (n.succPNat : ℕ) → ℝ) → ℝ) (hF : Measurable F) :
    ∫⁻ X : Configuration n.succPNat, nearestIntegrand n F (cyclicLift X 0)
        (anchorCoords n X.val).2 ∂(gibbsMeasure P n.succPNat) =
      ∫⁻ X : Configuration n.succPNat, nearestIntegral n F (anchorCoords n X.val).2
        ∂(gibbsMeasure P n.succPNat) := by
  have := isProbabilityMeasure_anchoredLaw P n
  set Φ : UnitAddCircle × (Fin n → ℝ) → ℝ≥0∞ :=
    fun p => nearestIntegrand n F (circleRep p.1) p.2 with hΦ
  have hΦm : Measurable Φ :=
    (measurable_nearestIntegrand n F hF).comp
      ((measurable_circleRep.comp measurable_fst).prodMk measurable_snd)
  have hmapX : Measurable (fun X : Configuration n.succPNat =>
      ((cyclicLift X 0 : UnitAddCircle), (anchorCoords n X.val).2)) :=
    (measurable_coe_circle.comp (measurable_cyclicLift 0)).prodMk
      (measurable_snd.comp (measurable_anchorCoords_config n))
  have hmapY : Measurable (fun X : Configuration n.succPNat => (anchorCoords n X.val).2) :=
    measurable_snd.comp (measurable_anchorCoords_config n)
  -- the rotation of a configuration lies in `[0, 1)`, where the representative is the identity
  have step1 : ∀ X : Configuration n.succPNat,
      nearestIntegrand n F (cyclicLift X 0) (anchorCoords n X.val).2 =
        Φ ((cyclicLift X 0 : UnitAddCircle), (anchorCoords n X.val).2) := by
    intro X
    have hmem : cyclicLift X 0 ∈ Ico (0 : ℝ) (0 + 1) := by
      obtain ⟨h1, h2⟩ := cyclicLift_zero_mem X
      exact ⟨h1, by rw [zero_add]; exact h2⟩
    rw [hΦ]
    simp only
    rw [circleRep_coe hmem]
  calc ∫⁻ X : Configuration n.succPNat, nearestIntegrand n F (cyclicLift X 0)
        (anchorCoords n X.val).2 ∂(gibbsMeasure P n.succPNat)
      = ∫⁻ X : Configuration n.succPNat, Φ ((cyclicLift X 0 : UnitAddCircle),
          (anchorCoords n X.val).2) ∂(gibbsMeasure P n.succPNat) :=
        lintegral_congr fun X => step1 X
    _ = ∫⁻ p, Φ p ∂((volume : Measure UnitAddCircle).prod (anchoredLaw P n)) := by
        rw [← map_cyclicLift_anchorCoords_gibbsMeasure P n 0, lintegral_map hΦm hmapX]
    _ = ∫⁻ y, ∫⁻ u, Φ (u, y) ∂(volume : Measure UnitAddCircle) ∂(anchoredLaw P n) :=
        lintegral_prod_symm Φ hΦm.aemeasurable
    _ = ∫⁻ y, nearestIntegral n F y ∂(anchoredLaw P n) := by
        refine lintegral_congr fun y => ?_
        rw [lintegral_circle_eq_Ico]
        refine setLIntegral_congr_fun measurableSet_Ico fun x hx => ?_
        rw [hΦ]
        simp only
        rw [circleRep_coe (by rw [zero_add]; exact hx)]
    _ = ∫⁻ X : Configuration n.succPNat, nearestIntegral n F (anchorCoords n X.val).2
          ∂(gibbsMeasure P n.succPNat) := by
        rw [← map_snd_gibbsMeasure P n, lintegral_map (measurable_nearestIntegral n F hF) hmapY]

/-- The one-period integral at the anchored gaps of a configuration: the sum over the labels `i`
of `F_i` times the selection weight `w_i / N`. -/
lemma nearestIntegral_anchor {n : ℕ} (F : (Fin (n.succPNat : ℕ) → ℝ) → ℝ)
    (X : Configuration n.succPNat) :
    nearestIntegral n F (anchorCoords n X.val).2 =
      ∑ i : Fin (n.succPNat : ℕ), ENNReal.ofReal (F (gapFrom X ((i : ℕ) : ℤ))) *
        ENNReal.ofReal (selectionWeight X ((i : ℕ) : ℤ) / ((n.succPNat : ℕ) : ℝ)) := by
  have hpos : ∀ j : ℤ, 0 < anchoredGapAt n (anchorCoords n X.val).2 j := fun j => by
    rw [← gap_eq_anchoredGapAt]
    exact gap_pos X j
  unfold nearestIntegral
  rw [nearestIntegral_eq_sum n F _ hpos]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  · congr 2
    funext k
    unfold gapFrom
    rw [gap_eq_anchoredGapAt]
  · rw [anchored_offset_weight X ((i : ℕ) : ℤ)]

/-- The cyclic kernel: the selection weight times `F`, evaluated on a gap vector. -/
def selectionKernel {N : ℕ+} (F : (Fin (N : ℕ) → ℝ) → ℝ) (h : Fin (N : ℕ) → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (((gapOf h (-1) + gapOf h 0) / 2) * F h)

lemma measurable_selectionKernel {N : ℕ+} (F : (Fin (N : ℕ) → ℝ) → ℝ) (hF : Measurable F) :
    Measurable (selectionKernel F) := by
  unfold selectionKernel
  refine ENNReal.measurable_ofReal.comp (Measurable.mul ?_ hF)
  refine Measurable.div_const (Measurable.add ?_ ?_) 2
  · exact measurable_pi_apply _
  · exact measurable_pi_apply _

/-- The cyclic kernel at the relabelled gap vector is the selection weight times `F_i`. -/
lemma selectionKernel_shiftFin {N : ℕ+} (F : (Fin (N : ℕ) → ℝ) → ℝ) (X : Configuration N)
    (i : ℤ) :
    selectionKernel F (shiftFin N i (gapVector X)) =
      ENNReal.ofReal (selectionWeight X i * F (gapFrom X i)) := by
  unfold selectionKernel
  rw [gapOf_shiftFin_selectionWeight, ← gapFrom_eq_shiftFin]

/-- The selection integral of `F_i` against the weight `w_i` does not depend on the label. -/
lemma lintegral_selectionWeight_eq {N : ℕ+} (P : Parameters) (hN : 2 ≤ (N : ℕ))
    (F : (Fin (N : ℕ) → ℝ) → ℝ) (hF : Measurable F) (i : ℕ) :
    ∫⁻ X, ENNReal.ofReal (selectionWeight X (i : ℤ) * F (gapFrom X (i : ℤ)))
        ∂(gibbsMeasure P N) =
      ∫⁻ X, selectionKernel F (gapVector X) ∂(gibbsMeasure P N) := by
  have h := lintegral_shiftFin_gapVector P hN (selectionKernel F)
    (measurable_selectionKernel F hF) i
  rw [← h]
  refine lintegral_congr fun X => ?_
  rw [selectionKernel_shiftFin]

/-- **Nearest-particle selection law** (part of the proof of Corollary 1), for
nonnegative `F`. The expectation of `F` at the nearest-particle label equals the expectation of
`w_1 F_1`, where `w_1 = selectionWeight X 0` and `F_1 = F (gapFrom X 0)` are the weight and the
gaps starting at the index `1` of the paper. -/
theorem nearest_selection_nonneg (P : Parameters) (N : ℕ+) (hN : 2 ≤ (N : ℕ))
    (F : (Fin (N : ℕ) → ℝ) → ℝ) (hF : Measurable F) (hF0 : ∀ g, 0 ≤ F g) :
    ∫⁻ X, ENNReal.ofReal (F (gapFrom X (nearestLabel X))) ∂(gibbsMeasure P N) =
      ∫⁻ X, ENNReal.ofReal (selectionWeight X 0 * F (gapFrom X 0)) ∂(gibbsMeasure P N) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, N = n.succPNat := ⟨N.natPred, (PNat.succPNat_natPred N).symm⟩
  have hL : ∀ X : Configuration n.succPNat, nearestLabel X =
      nearestLabelOf (fun j => cyclicLift X 0 + anchoredCyclicOffset n (anchorCoords n X.val).2 j) := by
    intro X
    unfold nearestLabel
    congr 1
    funext j
    rw [cyclicLift_eq_anchor_add n X j, cyclicLift_zero]
    rfl
  have hpt : ∀ X : Configuration n.succPNat,
      ENNReal.ofReal (F (gapFrom X (nearestLabel X))) =
        nearestIntegrand n F (cyclicLift X 0) (anchorCoords n X.val).2 := by
    intro X
    unfold nearestIntegrand
    rw [hL X]
    congr 2
    funext k
    unfold gapFrom
    rw [gap_eq_anchoredGapAt]
  have hM : (0 : ℝ) < ((n.succPNat : ℕ) : ℝ) := by exact_mod_cast (n.succPNat).pos
  -- the weight `1 / N` of each of the `N` labels
  have hterm : ∀ i : Fin (n.succPNat : ℕ), ∀ X : Configuration n.succPNat,
      ENNReal.ofReal (F (gapFrom X ((i : ℕ) : ℤ))) *
        ENNReal.ofReal (selectionWeight X ((i : ℕ) : ℤ) / ((n.succPNat : ℕ) : ℝ)) =
      ENNReal.ofReal (((n.succPNat : ℕ) : ℝ)⁻¹) *
        ENNReal.ofReal (selectionWeight X ((i : ℕ) : ℤ) * F (gapFrom X ((i : ℕ) : ℤ))) := by
    intro i X
    rw [← ENNReal.ofReal_mul (hF0 _), ← ENNReal.ofReal_mul (inv_nonneg.mpr hM.le)]
    congr 1
    ring
  have hmeasG : ∀ i : ℤ, Measurable (fun X : Configuration n.succPNat => gapFrom X i) := by
    intro i
    refine Measurable.of_eval fun k => ?_
    exact measurable_gap _
  have hmeasW : ∀ i : ℤ, Measurable (fun X : Configuration n.succPNat => selectionWeight X i) := by
    intro i
    unfold selectionWeight
    exact ((measurable_gap _).add (measurable_gap _)).div_const 2
  have hmeasT : ∀ i : ℕ, Measurable (fun X : Configuration n.succPNat =>
      ENNReal.ofReal (selectionWeight X ((i : ℕ) : ℤ) * F (gapFrom X ((i : ℕ) : ℤ)))) := by
    intro i
    refine ENNReal.measurable_ofReal.comp (Measurable.mul (hmeasW _) ?_)
    exact hF.comp (hmeasG _)
  have hmeasS : ∀ i : Fin (n.succPNat : ℕ), Measurable (fun X : Configuration n.succPNat =>
      ENNReal.ofReal (F (gapFrom X ((i : ℕ) : ℤ))) *
        ENNReal.ofReal (selectionWeight X ((i : ℕ) : ℤ) / ((n.succPNat : ℕ) : ℝ))) := by
    intro i
    refine Measurable.mul (ENNReal.measurable_ofReal.comp (hF.comp (hmeasG _))) ?_
    exact ENNReal.measurable_ofReal.comp ((hmeasW _).div_const _)
  rw [lintegral_congr hpt, lintegral_nearestIntegrand_eq_nearestIntegral P n F hF]
  simp_rw [nearestIntegral_anchor F]
  rw [lintegral_finsetSum _ fun i _ => hmeasS i]
  have hconst : ∀ i : Fin (n.succPNat : ℕ),
      ∫⁻ X, ENNReal.ofReal (F (gapFrom X ((i : ℕ) : ℤ))) *
        ENNReal.ofReal (selectionWeight X ((i : ℕ) : ℤ) / ((n.succPNat : ℕ) : ℝ))
          ∂(gibbsMeasure P n.succPNat) =
      ENNReal.ofReal (((n.succPNat : ℕ) : ℝ)⁻¹) *
        ∫⁻ X, selectionKernel F (gapVector X) ∂(gibbsMeasure P n.succPNat) := by
    intro i
    rw [lintegral_congr (hterm i), lintegral_const_mul _ (hmeasT i),
      lintegral_selectionWeight_eq P hN F hF i]
  simp_rw [hconst]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hK : (((n.succPNat : ℕ) : ℝ≥0∞)) * ENNReal.ofReal (((n.succPNat : ℕ) : ℝ)⁻¹) = 1 := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
      mul_inv_cancel₀ hM.ne', ENNReal.ofReal_one]
  rw [← mul_assoc, hK, one_mul]
  exact (lintegral_selectionWeight_eq P hN F hF 0).symm

end Riesz1

end

end
