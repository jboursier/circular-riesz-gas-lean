/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.CLT.SelectionLaw
public import Riesz1.Rigidity.BlockMoments

/-!
# Bounded selection identity and moments of the selection weight

Part of the proof of Corollary 1, the remaining claims on the nearest-particle selection.

* `nearest_selection_bounded`: for every bounded real Borel `F` of the gaps,
  `E F_J = E[w_1 F_1]`. The nonnegative identity of `SelectionLaw` gives the integrability of
  `w_1` with no external input, because `F = 1` gives `E w_1 = 1`.
* `nearest_selection_moments`: under `External.PrekopaLeindler`, the weight satisfies
  `‖w_1‖_2 ≤ C` and `E[N |x_J|] ≤ E w_1^2 ≤ C^2`, with an absolute constant `C`.

The weight `w_i` is `selectionWeight X i`, so the `w_1` of the paper is `selectionWeight X 0`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Riesz1

variable {N : ℕ+}

/-- The selection weight, as a nonnegative function of the gap vector. It agrees with the
selection weight on gap vectors of configurations. -/
def nonnegWeight (h : Fin (N : ℕ) → ℝ) : ℝ :=
  max ((gapOf h (-1) + gapOf h 0) / 2) 0

lemma measurable_nonnegWeight : Measurable (nonnegWeight (N := N)) := by
  unfold nonnegWeight
  refine Measurable.max (Measurable.div_const (Measurable.add ?_ ?_) 2) measurable_const
  · exact measurable_pi_apply _
  · exact measurable_pi_apply _

lemma nonnegWeight_nonneg (h : Fin (N : ℕ) → ℝ) : 0 ≤ nonnegWeight h :=
  le_max_right _ _

/-- The selection weight of a configuration is measurable. -/
lemma measurable_selectionWeight (i : ℤ) :
    Measurable (fun X : Configuration N => selectionWeight X i) := by
  unfold selectionWeight
  exact ((measurable_gap _).add (measurable_gap _)).div_const 2

/-- The square of a half-sum is at most the average of the squares. -/
lemma sq_half_sum_le (a b : ℝ) : ((a + b) / 2) ^ 2 ≤ 1 / 2 * a ^ 2 + 1 / 2 * b ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

/-- The gap-relabelled weight is the selection weight of the configuration. -/
lemma gapOf_gapFrom_selectionWeight (X : Configuration N) (i : ℤ) :
    (gapOf (gapFrom X i) (-1) + gapOf (gapFrom X i) 0) / 2 = selectionWeight X i := by
  rw [gapFrom_eq_shiftFin, gapOf_shiftFin_selectionWeight]

/-- The selection weight is nonnegative, since every gap is positive. -/
lemma selectionWeight_nonneg (X : Configuration N) (i : ℤ) : 0 ≤ selectionWeight X i := by
  unfold selectionWeight
  have h1 := gap_pos X (i - 1)
  have h2 := gap_pos X i
  linarith

/-- The nonnegative weight of the relabelled gap vector is the selection weight. -/
lemma nonnegWeight_gapFrom (X : Configuration N) (i : ℤ) :
    nonnegWeight (gapFrom X i) = selectionWeight X i := by
  unfold nonnegWeight
  rw [gapOf_gapFrom_selectionWeight]
  exact max_eq_left (selectionWeight_nonneg X i)

/-- **Selection identity for the weight at the nearest label.** The weight `w_J` has the same
expectation as `w_1 * w_1`. -/
lemma lintegral_selectionWeight_nearest (P : Parameters) (hN : 2 ≤ (N : ℕ)) :
    ∫⁻ X, ENNReal.ofReal (selectionWeight X (nearestLabel X)) ∂(gibbsMeasure P N) =
      ∫⁻ X, ENNReal.ofReal (selectionWeight X 0 * selectionWeight X 0) ∂(gibbsMeasure P N) := by
  have h := nearest_selection_nonneg P N hN nonnegWeight measurable_nonnegWeight
    nonnegWeight_nonneg
  simp only [nonnegWeight_gapFrom] at h
  exact h

/-- The selection weight is integrable, since `E w_1 = 1` by the selection identity with `F = 1`.
No external input is used. -/
lemma integrable_selectionWeight (P : Parameters) (hN : 2 ≤ (N : ℕ)) :
    Integrable (fun X : Configuration N => selectionWeight X 0) (gibbsMeasure P N) := by
  have := (modelWellDefined P N).2.2
  have h := nearest_selection_nonneg P N hN (fun _ => 1) measurable_const
    (fun _ => zero_le_one)
  simp only [lintegral_const, measure_univ, mul_one, ENNReal.ofReal_one] at h
  refine ⟨(measurable_selectionWeight 0).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun X => selectionWeight_nonneg X 0)]
  rw [← h]
  exact ENNReal.one_lt_top

/-! ### Measurability -/

/-- The nearest label of a configuration is measurable. -/
lemma measurable_nearestLabel (N : ℕ+) : Measurable (fun X : Configuration N => nearestLabel X) := by
  refine measurable_to_countable' fun k => ?_
  have hset : (fun X : Configuration N => nearestLabel X) ⁻¹' {k} =
      {X : Configuration N | 0 ≤ cyclicLift X k + cyclicLift X (k + 1)} ∩
        ⋂ i : ℤ, ⋂ (_ : i < k),
          {X : Configuration N | ¬ 0 ≤ cyclicLift X i + cyclicLift X (i + 1)} := by
    ext X
    simp only [mem_preimage, mem_singleton_iff, mem_inter_iff, mem_ofPred_eq, mem_iInter]
    unfold nearestLabel
    exact nearestLabelOf_eq_iff_forall (N := (N : ℕ)) N.pos (cyclicLift X)
      (cyclicLift_periodic X) k
  rw [hset]
  refine (measurableSet_le measurable_const
    ((measurable_cyclicLift k).add (measurable_cyclicLift (k + 1)))).inter ?_
  refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ => ?_
  exact (measurableSet_le measurable_const
    ((measurable_cyclicLift i).add (measurable_cyclicLift (i + 1)))).compl

/-- The gaps starting at a fixed label are measurable functions of the configuration. -/
lemma measurable_gapFrom_fixed (i : ℤ) :
    Measurable (fun X : Configuration N => gapFrom X i) :=
  Measurable.of_eval fun _ => measurable_gap _

/-- A function of the gaps starting at the nearest label is measurable. -/
lemma measurable_gapFrom_nearest {G : (Fin (N : ℕ) → ℝ) → ℝ} (hG : Measurable G) :
    Measurable (fun X : Configuration N => G (gapFrom X (nearestLabel X))) := by
  have hH : Measurable (fun q : Configuration N × ℤ => G (gapFrom q.1 q.2)) :=
    measurable_from_prod_countable_left fun j => hG.comp (measurable_gapFrom_fixed j)
  exact hH.comp (measurable_id.prodMk (measurable_nearestLabel N))

/-! ### The real selection identity -/

/-- The real selection identity for a nonnegative measurable `G` of the gaps. -/
lemma integral_nearest_nonneg (P : Parameters) (hN : 2 ≤ (N : ℕ))
    (G : (Fin (N : ℕ) → ℝ) → ℝ) (hG : Measurable G) (hG0 : ∀ g, 0 ≤ G g) :
    ∫ X, G (gapFrom X (nearestLabel X)) ∂(gibbsMeasure P N) =
      ∫ X, selectionWeight X 0 * G (gapFrom X 0) ∂(gibbsMeasure P N) := by
  have hL : ∀ X : Configuration N, 0 ≤ G (gapFrom X (nearestLabel X)) := fun X => hG0 _
  have hR : ∀ X : Configuration N, 0 ≤ selectionWeight X 0 * G (gapFrom X 0) := fun X =>
    mul_nonneg (selectionWeight_nonneg X 0) (hG0 _)
  have hmeasR : Measurable (fun X : Configuration N => selectionWeight X 0 * G (gapFrom X 0)) :=
    (measurable_selectionWeight 0).mul (hG.comp (measurable_gapFrom_fixed 0))
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hL)
      (measurable_gapFrom_nearest hG).aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hR) hmeasR.aestronglyMeasurable]
  congr 1
  exact nearest_selection_nonneg P N hN G hG hG0

/-! ### Integrability of bounded functions on configurations -/

lemma integrable_of_abs_le (P : Parameters)
    (f : Configuration N → ℝ) (hf : Measurable f) (M : ℝ) (hM : ∀ X, |f X| ≤ M) :
    Integrable f (gibbsMeasure P N) := by
  have := (modelWellDefined P N).2.2
  refine (integrable_const M).mono' hf.aestronglyMeasurable (ae_of_all _ fun X => ?_)
  rw [Real.norm_eq_abs]
  exact hM X

/-! ### The bounded real selection identity -/

/-- **Nearest-particle selection law** (part of the proof of Corollary 1),
for bounded real `F`: `E F_J = E[w_1 F_1]`. -/
theorem nearest_selection_bounded (P : Parameters) (hN : 2 ≤ (N : ℕ))
    (F : (Fin (N : ℕ) → ℝ) → ℝ) (hF : Measurable F) (M : ℝ) (hM : ∀ g, |F g| ≤ M) :
    ∫ X, F (gapFrom X (nearestLabel X)) ∂(gibbsMeasure P N) =
      ∫ X, selectionWeight X 0 * F (gapFrom X 0) ∂(gibbsMeasure P N) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  set Fp : (Fin (N : ℕ) → ℝ) → ℝ := fun g => max (F g) 0 with hFp
  set Fm : (Fin (N : ℕ) → ℝ) → ℝ := fun g => max (-F g) 0 with hFm
  have hsplit : ∀ g, F g = Fp g - Fm g := fun g => by
    rw [hFp, hFm]
    exact (max_zero_sub_max_neg_zero_eq_self (F g)).symm
  have hFpm : Measurable Fp := hF.max measurable_const
  have hFmm : Measurable Fm := hF.neg.max measurable_const
  have hFp0 : ∀ g, 0 ≤ Fp g := fun g => le_max_right _ _
  have hFm0 : ∀ g, 0 ≤ Fm g := fun g => le_max_right _ _
  have hFpb : ∀ g, |Fp g| ≤ M := fun g => by
    rw [abs_of_nonneg (hFp0 g)]
    exact max_le ((le_abs_self _).trans (hM g)) hM0
  have hFmb : ∀ g, |Fm g| ≤ M := fun g => by
    rw [abs_of_nonneg (hFm0 g)]
    exact max_le ((neg_le_abs _).trans (hM g)) hM0
  -- integrability of the gap functionals and of the weighted ones
  have hJ : ∀ G : (Fin (N : ℕ) → ℝ) → ℝ, Measurable G → (∀ g, |G g| ≤ M) →
      Integrable (fun X : Configuration N => G (gapFrom X (nearestLabel X))) (gibbsMeasure P N) :=
    fun G hG hGb => integrable_of_abs_le P _ (measurable_gapFrom_nearest hG) M
      fun X => hGb _
  have hW : ∀ G : (Fin (N : ℕ) → ℝ) → ℝ, Measurable G → (∀ g, |G g| ≤ M) →
      Integrable (fun X : Configuration N => selectionWeight X 0 * G (gapFrom X 0))
        (gibbsMeasure P N) := by
    intro G hG hGb
    refine ((integrable_selectionWeight P hN).const_mul M).mono'
      ((measurable_selectionWeight 0).mul (hG.comp (measurable_gapFrom_fixed 0))).aestronglyMeasurable
      (ae_of_all _ fun X => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (selectionWeight_nonneg X 0), mul_comm M]
    exact mul_le_mul_of_nonneg_left (hGb _) (selectionWeight_nonneg X 0)
  have hsplitF : (fun X : Configuration N => F (gapFrom X (nearestLabel X))) =
      fun X => Fp (gapFrom X (nearestLabel X)) - Fm (gapFrom X (nearestLabel X)) := by
    funext X
    exact hsplit _
  have hsplitW : (fun X : Configuration N => selectionWeight X 0 * F (gapFrom X 0)) =
      fun X => selectionWeight X 0 * Fp (gapFrom X 0) - selectionWeight X 0 * Fm (gapFrom X 0) := by
    funext X
    rw [hsplit (gapFrom X 0), mul_sub]
  rw [hsplitF, hsplitW, integral_sub (hJ Fp hFpm hFpb) (hJ Fm hFmm hFmb),
    integral_sub (hW Fp hFpm hFpb) (hW Fm hFmm hFmb),
    integral_nearest_nonneg P hN Fp hFpm hFp0, integral_nearest_nonneg P hN Fm hFmm hFm0]

/-! ### Moments of the selection weight -/

/-- **Moment bounds** (part of the proof of Corollary 1). Under
`External.PrekopaLeindler`, there is an absolute constant `C > 0` such that, for every `P` and every
`N ≥ 2`, the weight satisfies `‖w_1‖_2 ≤ C`, and `E[N |x_J|] ≤ E w_1^2 ≤ C^2`. -/
theorem nearest_selection_moments (hPL : External.PrekopaLeindler) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Parameters) (N : ℕ+), 2 ≤ (N : ℕ) →
      ∫⁻ X, ENNReal.ofReal (selectionWeight X 0 ^ 2) ∂(gibbsMeasure P N) ≤ ENNReal.ofReal (C ^ 2) ∧
      ∫⁻ X, ENNReal.ofReal (((N : ℕ) : ℝ) * |cyclicLift X (nearestLabel X)|)
        ∂(gibbsMeasure P N) ≤ ENNReal.ofReal (C ^ 2) := by
  obtain ⟨C₂, hC₂, hb⟩ := blockLength_moments 2 two_pos
  refine ⟨Real.sqrt C₂, Real.sqrt_pos.2 hC₂, fun P N hN => ?_⟩
  have hsq : Real.sqrt C₂ ^ 2 = C₂ := Real.sq_sqrt hC₂.le
  rw [hsq]
  -- second moment of a single gap
  have hgap : ∀ j : ℤ, ∫⁻ X, ENNReal.ofReal (gap X j ^ 2) ∂(gibbsMeasure P N) ≤
      ENNReal.ofReal C₂ := by
    intro j
    have h := (hb hPL P N hN j 1 one_pos).2
    have e1 : ∀ X : Configuration N, blockLength X j 1 = gap X j := fun X => by
      simp [blockLength_eq_sum]
    simp only [e1, Real.rpow_two, Nat.cast_one, one_pow, mul_one] at h
    exact h
  have hgapM : ∀ j : ℤ, Measurable (fun X : Configuration N => ENNReal.ofReal (gap X j ^ 2)) :=
    fun j => ENNReal.measurable_ofReal.comp ((measurable_gap j).pow_const 2)
  -- the weight squared is at most the average of the squares of its two gaps
  have hw2 : ∫⁻ X, ENNReal.ofReal (selectionWeight X 0 ^ 2) ∂(gibbsMeasure P N) ≤
      ENNReal.ofReal C₂ := by
    have hpt : ∀ X : Configuration N, ENNReal.ofReal (selectionWeight X 0 ^ 2) ≤
        ENNReal.ofReal (1 / 2) * ENNReal.ofReal (gap X (0 - 1) ^ 2) +
          ENNReal.ofReal (1 / 2) * ENNReal.ofReal (gap X 0 ^ 2) := by
      intro X
      rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      unfold selectionWeight
      exact sq_half_sum_le _ _
    calc ∫⁻ X, ENNReal.ofReal (selectionWeight X 0 ^ 2) ∂(gibbsMeasure P N)
        ≤ ∫⁻ X, (ENNReal.ofReal (1 / 2) * ENNReal.ofReal (gap X (0 - 1) ^ 2) +
          ENNReal.ofReal (1 / 2) * ENNReal.ofReal (gap X 0 ^ 2)) ∂(gibbsMeasure P N) :=
          lintegral_mono hpt
      _ = ENNReal.ofReal (1 / 2) * ∫⁻ X, ENNReal.ofReal (gap X (0 - 1) ^ 2)
            ∂(gibbsMeasure P N) +
          ENNReal.ofReal (1 / 2) * ∫⁻ X, ENNReal.ofReal (gap X 0 ^ 2) ∂(gibbsMeasure P N) := by
          rw [lintegral_add_left ((hgapM _).const_mul _), lintegral_const_mul _ (hgapM _),
            lintegral_const_mul _ (hgapM _)]
      _ ≤ ENNReal.ofReal (1 / 2) * ENNReal.ofReal C₂ + ENNReal.ofReal (1 / 2) * ENNReal.ofReal C₂ :=
          add_le_add (by gcongr; exact hgap _) (by gcongr; exact hgap _)
      _ = ENNReal.ofReal C₂ := by
          rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          ring
  refine ⟨hw2, ?_⟩
  calc ∫⁻ X, ENNReal.ofReal (((N : ℕ) : ℝ) * |cyclicLift X (nearestLabel X)|)
        ∂(gibbsMeasure P N)
      ≤ ∫⁻ X, ENNReal.ofReal (selectionWeight X (nearestLabel X)) ∂(gibbsMeasure P N) :=
        lintegral_mono fun X => ENNReal.ofReal_le_ofReal (nearest_abs_le_selectionWeight X)
    _ = ∫⁻ X, ENNReal.ofReal (selectionWeight X 0 * selectionWeight X 0)
          ∂(gibbsMeasure P N) := lintegral_selectionWeight_nearest P hN
    _ ≤ ∫⁻ X, ENNReal.ofReal (selectionWeight X 0 ^ 2) ∂(gibbsMeasure P N) :=
        lintegral_mono fun X => ENNReal.ofReal_le_ofReal (le_of_eq (by ring))
    _ ≤ ENNReal.ofReal C₂ := hw2

end Riesz1

end

end
