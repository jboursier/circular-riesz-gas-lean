/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Rigidity.RigidityTheoremBoundary
public import Riesz1.Rigidity.RigidityTheoremScales

/-!
# Probabilistic count inversion

The three events in the proof of Theorem 1
bound the count discrepancy. The endpoints are null by the uniform
particle marginals. The selected block tails use the square-root
boundary estimate and the complementary-block part of the gap theorem.
-/

public section

noncomputable section

open MeasureTheory Filter Set

namespace Riesz1.Internal

theorem rigidity_volume_singleton (z : UnitAddCircle) :
    (volume : Measure UnitAddCircle) {z} = 0 := by
  let w := AddCircle.equivIoc (1 : ℝ) 0 z
  have hmp := AddCircle.measurePreserving_mk (1 : ℝ) 0
  rw [← hmp.measure_preimage (measurableSet_singleton z).nullMeasurableSet,
    Measure.restrict_apply' measurableSet_Ioc]
  refine measure_mono_null (t := {(w : ℝ)}) ?_ (measure_singleton _)
  rintro y ⟨hy1, hy2⟩
  apply (AddCircle.coe_eq_coe_iff_of_mem_Ioc hy2 w.property).mp
  simpa only [Set.mem_preimage, Set.mem_singleton_iff, w, AddCircle.coe_equivIoc] using hy1

theorem rigidity_ae_avoid_endpoints (P : Parameters) (N : ℕ+)
    (a : UnitAddCircle) (ell : ℝ) :
    ∀ᵐ X ∂gibbsMeasure P N, ∀ i : Fin (N : ℕ),
      ((X.val i : ℝ) : UnitAddCircle) ≠ a - ell ∧
        ((X.val i : ℝ) : UnitAddCircle) ≠ a + ell := by
  apply ae_all_iff.mpr
  intro i
  have hz (z : UnitAddCircle) :
      ∀ᵐ X ∂gibbsMeasure P N, ((X.val i : ℝ) : UnitAddCircle) ≠ z := by
    have hzero : (gibbsMeasure P N) {X | ((X.val i : ℝ) : UnitAddCircle) = z} = 0 := by
      have he := congrArg (fun μ : Measure UnitAddCircle => μ {z}) (map_coord_gibbsMeasure P N i)
      rw [Measure.map_apply (measurable_coord N i) (measurableSet_singleton z),
        rigidity_volume_singleton] at he
      exact he
    simpa only [ae_iff, not_not] using hzero
  exact (hz _).and (hz _)

/-- The union estimate for the count event, including the null endpoint sets. -/
theorem rigidity_count_union_bound (P : Parameters) (N : ℕ+) (a : UnitAddCircle)
    {ell lam K : ℝ} (hell : 0 < ell) (hell4 : ell ≤ 1 / 4) (hlam : 2 ≤ lam)
    (hK : K = (N : ℝ) * ell) (hKlam : lam + 1 ≤ K) :
    (gibbsMeasure P N).real {X | lam ≤ |arcCount a ell X - 2 * K|} ≤
      (gibbsMeasure P N).real {X | lam / 2 < gap X (precedingLabel a ell X)} +
        ((gibbsMeasure P N).real {X | lam / 2 ≤
          |blockLength X (precedingLabel a ell X) ⌈2 * K + lam⌉₊ - (⌈2 * K + lam⌉₊ : ℝ)|} +
        (gibbsMeasure P N).real {X | lam / 2 ≤
          |blockLength X (precedingLabel a ell X) (⌊2 * K - lam⌋₊ + 1) -
            ((⌊2 * K - lam⌋₊ + 1 : ℕ) : ℝ)|}) := by
  let := (modelWellDefined P N).2.2
  have he : {X : Configuration N | lam ≤ |arcCount a ell X - 2 * K|} ≤ᵐ[gibbsMeasure P N]
      {X | lam / 2 < gap X (precedingLabel a ell X)} ∪
        ({X | lam / 2 ≤ |blockLength X (precedingLabel a ell X) ⌈2 * K + lam⌉₊ -
          (⌈2 * K + lam⌉₊ : ℝ)|} ∪
        {X | lam / 2 ≤ |blockLength X (precedingLabel a ell X) (⌊2 * K - lam⌋₊ + 1) -
          ((⌊2 * K - lam⌋₊ + 1 : ℕ) : ℝ)|}) := by
    filter_upwards [rigidity_ae_avoid_endpoints P N a ell] with X hX
    exact almost_optimal_rigidity_inversion N a hell hell4 hlam hK hKlam X hX
  exact (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae he)).trans
    ((measureReal_union_le _ _).trans (add_le_add le_rfl (measureReal_union_le _ _)))

/-- A deterministic block tail yields a selected block tail on every comparable scale.
This is an internal conditional estimate, used with the proved gap theorem. -/
theorem rigidity_selected_block_tail (P : Parameters) (N : ℕ+) (a : UnitAddCircle) (ell : ℝ)
    {k : ℕ} {t K r b delta B C c : ℝ} (hK : 0 ≤ K) (hKr : K ≤ r) (hr3 : r ≤ 3 * K)
    (hb : 0 ≤ b) (hd : 0 ≤ delta) (hB : 0 ≤ B) (hC : 0 ≤ C) (hc : 0 ≤ c)
    (hT : (3 * K) ^ b ≤ t)
    (hgap : (gibbsMeasure P N).real {X | r ^ b ≤ |blockLength X 0 k - k|} ≤
      C * Real.exp (-c * r ^ delta))
    (hsel : (gibbsMeasure P N).real {X | t ≤ |blockLength X (precedingLabel a ell X) k - k|} ≤
      B * ((gibbsMeasure P N).real {X | t ≤ |blockLength X 0 k - k|}) ^ (1 / (2 : ℝ))) :
    (gibbsMeasure P N).real {X | t ≤ |blockLength X (precedingLabel a ell X) k - k|} ≤
      B * C ^ (1 / (2 : ℝ)) * Real.exp (-(c / 2) * K ^ delta) := by
  let := (modelWellDefined P N).2.2
  have hrt : r ^ b ≤ t :=
    (Real.rpow_le_rpow (hK.trans hKr) hr3 hb).trans hT
  have he : (gibbsMeasure P N).real {X | t ≤ |blockLength X 0 k - k|} ≤
      C * Real.exp (-c * r ^ delta) :=
    (measureReal_mono fun _ hX => hrt.trans hX).trans hgap
  have hs := rigidity_sqrt_tail measureReal_nonneg hB hC he
  have hpow : K ^ delta ≤ r ^ delta := Real.rpow_le_rpow hK hKr hd
  have hexp : Real.exp (-(c / 2) * r ^ delta) ≤ Real.exp (-(c / 2) * K ^ delta) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  exact (hsel.trans hs).trans (mul_le_mul_of_nonneg_left hexp
    (mul_nonneg hB (Real.rpow_nonneg hC _)))

end Riesz1.Internal

end
