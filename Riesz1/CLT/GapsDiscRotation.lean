/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Gibbs.AnchoredCoordinates
public import Riesz1.Gibbs.UniformMarginals
public import Riesz1.Frozen.LinearStatistic
public import Riesz1.Frozen.GibbsMeasure

/-!
# Rotation invariance of the Gibbs law for linear statistics

For a function `g` on the unit circle and a rotation `θ`, the linear statistic of `x ↦ g (x + θ)`
under the Gibbs law has the same distribution as the linear statistic of `g`. The proof uses the
product law of the anchored coordinates (`map_gibbsMeasure_anchorCoords`): the anchor is uniform
on `[0, 1)` and independent of the gaps, and the rotation shifts only the anchor. Lebesgue measure
on the circle is invariant under this shift.

This is the stationarity used in the strip estimates and in the selected-count estimate for
Corollary 1, where arcs with arbitrary centres are compared
with arcs centred at `0`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter

namespace Riesz1

/-- The linear statistic of `g` in anchored coordinates: `z` is the circle position of the anchor
and `y` the gap vector, so the particle `i` sits at `z + [anchorVector y i]`. -/
def anchoredStatistic {n : ℕ} (g : UnitAddCircle → ℝ) (z : UnitAddCircle) (y : Fin n → ℝ) : ℝ :=
  ∑ i : Fin (n.succPNat : ℕ), g (z + ((anchorVector y i : ℝ) : UnitAddCircle))

/-- The anchored statistic of a rotated function is the anchored statistic of `g` at the rotated
anchor. -/
lemma anchoredStatistic_rotate {n : ℕ} (g : UnitAddCircle → ℝ) (θ z : UnitAddCircle)
    (y : Fin n → ℝ) :
    anchoredStatistic (fun x => g (x + θ)) z y = anchoredStatistic g (z + θ) y := by
  unfold anchoredStatistic
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [add_right_comm]

/-- The linear statistic of `g` is the anchored statistic at the circle position of the anchor
`X_0`, with the gap vector of `anchorCoords`. -/
lemma linearStatistic_eq_anchoredStatistic {n : ℕ} (g : UnitAddCircle → ℝ)
    (X : Configuration n.succPNat) :
    linearStatistic g X = anchoredStatistic g ((X.val 0 : ℝ) : UnitAddCircle)
      (anchorCoords n X.val).2 := by
  unfold linearStatistic anchoredStatistic
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  rw [apply_eq_anchor_add n X.val i]
  simp only [anchorCoords]
  rw [QuotientAddGroup.mk_add]

/-- The product `volume ⊗ anchoredLaw`, obtained from the uniform anchor on `[0, 1)` by taking
its circle class. -/
lemma map_uniform_prod_circle (P : Parameters) (n : ℕ) :
    ((volume.restrict (Ico (0 : ℝ) 1)).prod (anchoredLaw P n)).map
      (fun p : ℝ × (Fin n → ℝ) => (((p.1 : ℝ) : UnitAddCircle), p.2)) =
        (volume : Measure UnitAddCircle).prod (anchoredLaw P n) := by
  have : IsProbabilityMeasure (anchoredLaw P n) := isProbabilityMeasure_anchoredLaw P n
  have hcoe : (volume.restrict (Ico (0 : ℝ) 1)).map (fun t : ℝ => (t : UnitAddCircle)) =
      volume := by
    have h := (AddCircle.measurePreserving_mk (1 : ℝ) 0).map_eq
    rw [zero_add] at h
    rw [Measure.restrict_congr_set Ico_ae_eq_Ioc]
    exact h
  have h := Measure.map_prod_map (volume.restrict (Ico (0 : ℝ) 1)) (anchoredLaw P n)
    measurable_coe_circle (measurable_id (α := Fin n → ℝ))
  rw [hcoe, Measure.map_id] at h
  exact h.symm

/-- **Change of variables to anchored coordinates.** The integral of `Φ` of a linear statistic
under the Gibbs law is the integral of `Φ` of the anchored statistic under `volume ⊗ anchoredLaw`. -/
theorem integral_linearStatistic_eq_anchored (P : Parameters) (n : ℕ) (g : UnitAddCircle → ℝ)
    (Φ : ℝ → ℝ) (hΦ : Measurable Φ) (hg : Measurable g) :
    ∫ X : Configuration n.succPNat, Φ (linearStatistic g X) ∂(gibbsMeasure P n.succPNat) =
      ∫ q : UnitAddCircle × (Fin n → ℝ), Φ (anchoredStatistic g q.1 q.2)
        ∂((volume : Measure UnitAddCircle).prod (anchoredLaw P n)) := by
  have hA : Measurable (fun X : Configuration n.succPNat => anchorCoords n X.val) :=
    measurable_anchorCoords_config n
  have hT : Measurable (fun p : ℝ × (Fin n → ℝ) => (((p.1 : ℝ) : UnitAddCircle), p.2)) :=
    (measurable_coe_circle.comp measurable_fst).prodMk measurable_snd
  have hw : ∀ i : Fin (n.succPNat : ℕ), Measurable (fun q : UnitAddCircle × (Fin n → ℝ) =>
      ((anchorVector q.2 i : ℝ) : UnitAddCircle)) := fun i =>
    measurable_coe_circle.comp ((measurable_pi_apply i).comp
      ((measurable_anchorVector n).comp measurable_snd))
  have hstat : Measurable (fun q : UnitAddCircle × (Fin n → ℝ) =>
      Φ (anchoredStatistic g q.1 q.2)) := by
    refine hΦ.comp ?_
    unfold anchoredStatistic
    exact Finset.measurable_sum _ fun i _ => hg.comp (measurable_fst.add (hw i))
  have hpt : ∀ X : Configuration n.succPNat,
      Φ (linearStatistic g X) = (fun q : UnitAddCircle × (Fin n → ℝ) =>
        Φ (anchoredStatistic g q.1 q.2))
        ((fun p : ℝ × (Fin n → ℝ) => (((p.1 : ℝ) : UnitAddCircle), p.2))
          (anchorCoords n X.val)) := by
    intro X
    rw [linearStatistic_eq_anchoredStatistic]
    rfl
  calc ∫ X : Configuration n.succPNat, Φ (linearStatistic g X) ∂(gibbsMeasure P n.succPNat)
      = ∫ X : Configuration n.succPNat, (fun q : UnitAddCircle × (Fin n → ℝ) =>
          Φ (anchoredStatistic g q.1 q.2))
          ((fun p : ℝ × (Fin n → ℝ) => (((p.1 : ℝ) : UnitAddCircle), p.2))
            (anchorCoords n X.val)) ∂(gibbsMeasure P n.succPNat) :=
        integral_congr_ae (Eventually.of_forall fun X => hpt X)
    _ = ∫ p : ℝ × (Fin n → ℝ), (fun q : UnitAddCircle × (Fin n → ℝ) =>
          Φ (anchoredStatistic g q.1 q.2))
          ((fun p : ℝ × (Fin n → ℝ) => (((p.1 : ℝ) : UnitAddCircle), p.2)) p)
          ∂((gibbsMeasure P n.succPNat).map (fun X : Configuration n.succPNat =>
            anchorCoords n X.val)) :=
        (integral_map hA.aemeasurable (hstat.comp hT).aestronglyMeasurable).symm
    _ = ∫ p : ℝ × (Fin n → ℝ), (fun q : UnitAddCircle × (Fin n → ℝ) =>
          Φ (anchoredStatistic g q.1 q.2))
          ((fun p : ℝ × (Fin n → ℝ) => (((p.1 : ℝ) : UnitAddCircle), p.2)) p)
          ∂((volume.restrict (Ico (0 : ℝ) 1)).prod (anchoredLaw P n)) := by
        rw [map_gibbsMeasure_anchorCoords]
    _ = ∫ q : UnitAddCircle × (Fin n → ℝ), Φ (anchoredStatistic g q.1 q.2)
          ∂(((volume.restrict (Ico (0 : ℝ) 1)).prod (anchoredLaw P n)).map
            (fun p : ℝ × (Fin n → ℝ) => (((p.1 : ℝ) : UnitAddCircle), p.2))) :=
        (integral_map hT.aemeasurable hstat.aestronglyMeasurable).symm
    _ = ∫ q : UnitAddCircle × (Fin n → ℝ), Φ (anchoredStatistic g q.1 q.2)
          ∂((volume : Measure UnitAddCircle).prod (anchoredLaw P n)) := by
        rw [map_uniform_prod_circle]

/-- **Rotation invariance of the Gibbs law for linear statistics.** For every rotation `θ` of the
circle, the linear statistic of `x ↦ g (x + θ)` under the Gibbs law has the same law as the linear
statistic of `g`: `E Φ(Fluct_N[g(· + θ)]) = E Φ(Fluct_N[g])`-type identities hold for every
measurable `Φ`. -/
theorem integral_rotate_linearStatistic (P : Parameters) (N : ℕ+) (g : UnitAddCircle → ℝ)
    (θ : UnitAddCircle) (Φ : ℝ → ℝ) (hΦ : Measurable Φ) (hg : Measurable g) :
    ∫ X, Φ (linearStatistic (fun x => g (x + θ)) X) ∂(gibbsMeasure P N) =
      ∫ X, Φ (linearStatistic g X) ∂(gibbsMeasure P N) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, N = n.succPNat := ⟨N.natPred, (PNat.succPNat_natPred N).symm⟩
  have : IsProbabilityMeasure (anchoredLaw P n) := isProbabilityMeasure_anchoredLaw P n
  have hgθ : Measurable (fun x => g (x + θ)) := hg.comp (measurable_id.add_const θ)
  rw [integral_linearStatistic_eq_anchored P n (fun x => g (x + θ)) Φ hΦ hgθ,
    integral_linearStatistic_eq_anchored P n g Φ hΦ hg]
  simp only [anchoredStatistic_rotate]
  have hmp : MeasurePreserving (fun q : UnitAddCircle × (Fin n → ℝ) => (q.1 + θ, q.2))
      ((volume : Measure UnitAddCircle).prod (anchoredLaw P n))
      ((volume : Measure UnitAddCircle).prod (anchoredLaw P n)) :=
    (measurePreserving_add_right (volume : Measure UnitAddCircle) θ).prod
      (MeasurePreserving.id _)
  have hF : Measurable (fun q : UnitAddCircle × (Fin n → ℝ) =>
      Φ (anchoredStatistic g q.1 q.2)) := by
    refine hΦ.comp ?_
    unfold anchoredStatistic
    refine Finset.measurable_sum _ fun i _ => hg.comp (measurable_fst.add ?_)
    exact measurable_coe_circle.comp ((measurable_pi_apply i).comp
      ((measurable_anchorVector n).comp measurable_snd))
  calc ∫ q : UnitAddCircle × (Fin n → ℝ), Φ (anchoredStatistic g (q.1 + θ) q.2)
        ∂((volume : Measure UnitAddCircle).prod (anchoredLaw P n))
      = ∫ q : UnitAddCircle × (Fin n → ℝ), Φ (anchoredStatistic g q.1 q.2)
          ∂(((volume : Measure UnitAddCircle).prod (anchoredLaw P n)).map
            (fun q : UnitAddCircle × (Fin n → ℝ) => (q.1 + θ, q.2))) :=
        (integral_map hmp.measurable.aemeasurable hF.aestronglyMeasurable).symm
    _ = ∫ q : UnitAddCircle × (Fin n → ℝ), Φ (anchoredStatistic g q.1 q.2)
          ∂((volume : Measure UnitAddCircle).prod (anchoredLaw P n)) := by
        rw [hmp.map_eq]

end Riesz1

end
end
