/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Gibbs.AnchoredCoordinates

/-!
# Uniform marginals of the Gibbs law

The marginal statement: for every particle `i`, the circle coordinate
`[X_i] ∈ 𝕋` has law `dx` under the Gibbs law. By the product law of `AnchoredCoordinates`, the
coordinate `X_i` is the uniform common rotation `X_0` shifted by the independent anchored offset
`X_i - X_0`. Haar measure on the circle is invariant under translation, so the shifted law is still
uniform.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal

namespace Riesz1

/-- The coordinate map to the circle is measurable. -/
lemma measurable_coe_circle : Measurable (fun t : ℝ => (t : UnitAddCircle)) := by
  fun_prop

/-- The uniform law on `[0, 1)`, shifted by a real number `a` and reduced modulo one, is
Lebesgue measure on the circle. -/
lemma map_circle_translate_uniform (a : ℝ) :
    (volume.restrict (Ico (0 : ℝ) 1)).map (fun t : ℝ => ((t + a : ℝ) : UnitAddCircle)) =
      volume := by
  have hcoe : (volume.restrict (Ico (0 : ℝ) 1)).map (fun t : ℝ => (t : UnitAddCircle)) =
      volume := by
    have h := (AddCircle.measurePreserving_mk (1 : ℝ) 0).map_eq
    rw [zero_add] at h
    rw [Measure.restrict_congr_set Ico_ae_eq_Ioc]
    exact h
  have hcomp : (fun t : ℝ => ((t + a : ℝ) : UnitAddCircle)) =
      (fun u : UnitAddCircle => u + (a : UnitAddCircle)) ∘ (fun t : ℝ => (t : UnitAddCircle)) := by
    funext t
    simp [QuotientAddGroup.mk_add]
  have hg : Measurable (fun u : UnitAddCircle => u + (a : UnitAddCircle)) := by
    fun_prop
  rw [hcomp, ← Measure.map_map hg measurable_coe_circle, hcoe]
  exact map_add_right_eq_self volume _

/-- Translating the uniform law on `[0, 1)` by an offset `a(y)` that depends measurably on an
independent variable `y` gives Lebesgue measure on the circle. -/
lemma map_circle_uniform_shift {n : ℕ} (a : (Fin n → ℝ) → ℝ) (ha : Measurable a)
    (ν : Measure (Fin n → ℝ)) [IsProbabilityMeasure ν] :
    ((volume.restrict (Ico (0 : ℝ) 1)).prod ν).map
      (fun p : ℝ × (Fin n → ℝ) => ((p.1 + a p.2 : ℝ) : UnitAddCircle)) = volume := by
  have hΦ : Measurable (fun p : ℝ × (Fin n → ℝ) => ((p.1 + a p.2 : ℝ) : UnitAddCircle)) :=
    measurable_coe_circle.comp (measurable_fst.add (ha.comp measurable_snd))
  ext B hB
  rw [Measure.map_apply hΦ hB, Measure.prod_apply_symm (hΦ hB)]
  have hinner : ∀ y : Fin n → ℝ,
      (volume.restrict (Ico (0 : ℝ) 1))
          ((fun t : ℝ => (t, y)) ⁻¹' ((fun p : ℝ × (Fin n → ℝ) =>
            ((p.1 + a p.2 : ℝ) : UnitAddCircle)) ⁻¹' B)) = volume B := by
    intro y
    have hψ : Measurable (fun t : ℝ => ((t + a y : ℝ) : UnitAddCircle)) :=
      measurable_coe_circle.comp (measurable_id.add_const _)
    rw [← map_circle_translate_uniform (a y), Measure.map_apply hψ hB]
    rfl
  rw [lintegral_congr hinner, lintegral_const, measure_univ, mul_one]

/-- The circle coordinate `[X_i]` is measurable on the configuration space. -/
lemma measurable_coord (N : ℕ+) (i : Fin (N : ℕ)) :
    Measurable (fun X : Configuration N => ((X.val i : ℝ) : UnitAddCircle)) :=
  measurable_coe_circle.comp ((measurable_pi_apply i).comp measurable_subtype_coe)

/-- **Uniform marginals.** For every particle `i`, the circle coordinate
`[X_i]` of the Gibbs law has law `volume`, the Haar probability on the circle. -/
theorem map_coord_gibbsMeasure (P : Parameters) (N : ℕ+) (i : Fin (N : ℕ)) :
    (gibbsMeasure P N).map (fun X : Configuration N => ((X.val i : ℝ) : UnitAddCircle)) =
      volume := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, N = n.succPNat := ⟨N.natPred, (PNat.succPNat_natPred N).symm⟩
  have : IsProbabilityMeasure (anchoredLaw P n) := isProbabilityMeasure_anchoredLaw P n
  have hΦ : Measurable (fun p : ℝ × (Fin n → ℝ) => ((p.1 + anchorVector p.2 i : ℝ) : UnitAddCircle)) :=
    measurable_coe_circle.comp (measurable_fst.add
      (((measurable_pi_apply i).comp (measurable_anchorVector n)).comp measurable_snd))
  have hfun : (fun X : Configuration n.succPNat => ((X.val i : ℝ) : UnitAddCircle)) =
      (fun p : ℝ × (Fin n → ℝ) => ((p.1 + anchorVector p.2 i : ℝ) : UnitAddCircle)) ∘
        (fun X : Configuration n.succPNat => anchorCoords n X.val) := by
    funext X
    exact congrArg (fun t : ℝ => (t : UnitAddCircle)) (apply_eq_anchor_add n X.val i)
  rw [hfun, ← Measure.map_map hΦ (measurable_anchorCoords_config n),
    map_gibbsMeasure_anchorCoords]
  exact map_circle_uniform_shift (fun y => anchorVector y i)
    ((measurable_pi_apply i).comp (measurable_anchorVector n)) (anchoredLaw P n)

end Riesz1

end
end
