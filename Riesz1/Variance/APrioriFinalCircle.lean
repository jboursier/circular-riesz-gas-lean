/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.APrioriFinalOrigin

/-!
# The proved a priori clauses on the circle objects

Both bounds of Lemma 5.2 at centre zero and every
positive radius, and the plain-sum bound at every translated centre.
The final latter constant is uniform in the centre. This also discharges
`RegMicroAPrioriInput` without a conclusion-shaped hypothesis.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Riesz1.Internal

/-- On the closed central interval, the absolute central representative
equals the absolute real coordinate, including the antipodal endpoint. -/
theorem abs_centralRep_coe_of_mem_Icc (L : Length) {u : ℝ}
    (hu : u ∈ Icc (-(L.val / 2)) (L.val / 2)) :
    |centralRep L (u : Circle L)| = |u| := by
  have : Fact (0 < L.val) := ⟨L.property⟩
  have hrep {v : ℝ} (hv : v ∈ Ico (-(L.val / 2)) (L.val / 2)) :
      centralRep L (v : Circle L) = v := by
    unfold centralRep
    exact AddCircle.equivIco_coe_of_mem (a := -L.val / 2)
      ⟨by linarith [hv.1], by linarith [hv.2]⟩
  by_cases ht : u < L.val / 2
  · rw [hrep ⟨hu.1, ht⟩]
  · have he : u = L.val / 2 := le_antisymm hu.2 (le_of_not_gt ht)
    have hc : ((L.val / 2 : ℝ) : Circle L) = ((-(L.val / 2) : ℝ) : Circle L) := by
      calc ((L.val / 2 : ℝ) : Circle L) =
          ((-(L.val / 2) + L.val : ℝ) : Circle L) := by congr 1; ring
        _ = _ := AddCircle.coe_add_period L.val (-(L.val / 2))
    rw [he, hc, hrep ⟨le_rfl, by linarith [L.property]⟩, abs_neg]

end Riesz1.Internal

namespace Riesz1

/-- The centre-zero specialization of `APrioriConclusion`, with every
fixed radius, both variances and the factor `M²`. -/
theorem a_priori_at_origin_circle
    (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (P : Parameters) (lam ε R : ℝ) (hlam : 0 ≤ lam) (hε : 0 < ε) (hR : 0 < R) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (ℓ : Scale), 1 ≤ (N : ℝ) * ℓ.val →
      ∀ M : ℝ, 0 ≤ M → ∀ f : Circle (observationLength ℓ) → ℝ,
      ContDiff ℝ 1 (fun u : ℝ => f (u : Circle (observationLength ℓ))) →
      (∀ u : ℝ, |deriv (fun t : ℝ => f (t : Circle (observationLength ℓ))) u| ≤
        M * Internal.aPrioriEnvelope P.val.2 lam ((N : ℝ) * ℓ.val) R
          |centralRep (observationLength ℓ) ((u - 0 : ℝ) : Circle (observationLength ℓ))|) →
      (∃ hA : Integrable (Internal.anchoredSum ℓ N f) (gibbsMeasure P N),
        variance (gibbsMeasure P N) (Internal.anchoredSum ℓ N f) hA ≤
          ENNReal.ofReal (C * M ^ 2 * ((N : ℝ) * ℓ.val) ^ (ε + max (2 * lam) P.val.2))) ∧
      (∃ hB : Integrable (Internal.plainSum ℓ N f) (gibbsMeasure P N),
        variance (gibbsMeasure P N) (Internal.plainSum ℓ N f) hB ≤
          ENNReal.ofReal (C * M ^ 2 * ((N : ℝ) * ℓ.val) ^ (ε + max (2 * lam) P.val.2))) := by
  obtain ⟨C, hC, hb⟩ := a_priori_at_origin hBE hPL P lam ε R hlam hε hR
  refine ⟨C, hC, ?_⟩
  intro N ℓ hK M hM f hf hder
  have hp : Function.Periodic (fun u : ℝ => f (u : Circle (observationLength ℓ))) (1 / ℓ.val) := by
    intro u
    change f ((u + 1 / ℓ.val : ℝ) : Circle (observationLength ℓ)) =
      f (u : Circle (observationLength ℓ))
    have he : 1 / ℓ.val = (observationLength ℓ).val := by simp [observationLength]
    rw [he]
    exact congrArg f (AddCircle.coe_add_period (observationLength ℓ).val u)
  apply hb N ℓ.val ℓ.2.1 ℓ.2.2 hK M hM
    (fun u : ℝ => f (u : Circle (observationLength ℓ))) hf hp
  intro u hu
  have huL : u ∈ Icc (-((observationLength ℓ).val / 2)) ((observationLength ℓ).val / 2) := by
    simpa only [observationLength, one_div] using hu
  simpa only [sub_zero, Internal.abs_centralRep_coe_of_mem_Icc (observationLength ℓ) huL]
    using hder u

/-- The translated plain-sum clause of Lemma 5.2, for every
fixed radius. The variance constant can be chosen before the centre. -/
theorem a_priori_plain_translate
    (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (P : Parameters) (lam ε R : ℝ) (hlam : 0 ≤ lam) (hε : 0 < ε) (hR : 0 < R) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (ℓ : Scale), 1 ≤ (N : ℝ) * ℓ.val →
      ∀ M : ℝ, 0 ≤ M → ∀ (c : ℝ) (f : Circle (observationLength ℓ) → ℝ),
      ContDiff ℝ 1 (fun u : ℝ => f (u : Circle (observationLength ℓ))) →
      (∀ u : ℝ, |deriv (fun t : ℝ => f (t : Circle (observationLength ℓ))) u| ≤
        M * Internal.aPrioriEnvelope P.val.2 lam ((N : ℝ) * ℓ.val) R
          |centralRep (observationLength ℓ) ((u - c : ℝ) : Circle (observationLength ℓ))|) →
      ∃ hB : Integrable (Internal.plainSum ℓ N f) (gibbsMeasure P N),
        variance (gibbsMeasure P N) (Internal.plainSum ℓ N f) hB ≤
          ENNReal.ofReal (C * M ^ 2 * ((N : ℝ) * ℓ.val) ^ (ε + max (2 * lam) P.val.2)) := by
  obtain ⟨C, hC, hb⟩ := a_priori_at_origin_circle hBE hPL P lam ε R hlam hε hR
  refine ⟨C, hC, ?_⟩
  intro N ℓ hK M hM c f hf hder
  have hfcont : Continuous f := continuous_circle_of_lift hf.continuous
  let g := fun z : Circle (observationLength ℓ) => f (z + (c : Circle (observationLength ℓ)))
  have hgfun : (fun u : ℝ => g (u : Circle (observationLength ℓ))) =
      fun u : ℝ => f ((u + c : ℝ) : Circle (observationLength ℓ)) := by
    funext u
    rw [AddCircle.coe_add]
  have hg : ContDiff ℝ 1 (fun u : ℝ => g (u : Circle (observationLength ℓ))) := by
    rw [hgfun]
    exact hf.comp (contDiff_id.add contDiff_const)
  have hgd : ∀ u : ℝ, |deriv (fun t : ℝ => g (t : Circle (observationLength ℓ))) u| ≤
      M * Internal.aPrioriEnvelope P.val.2 lam ((N : ℝ) * ℓ.val) R
        |centralRep (observationLength ℓ) ((u - 0 : ℝ) : Circle (observationLength ℓ))| := by
    intro u
    have he : deriv (fun t : ℝ => f ((t + c : ℝ) : Circle (observationLength ℓ))) u =
        deriv (fun t : ℝ => f (t : Circle (observationLength ℓ))) (u + c) :=
      deriv_comp_add_const (fun t : ℝ => f (t : Circle (observationLength ℓ))) c u
    rw [hgfun, he, sub_zero]
    have hd := hder (u + c)
    simpa only [add_sub_cancel_right] using hd
  obtain ⟨hBi, hBv⟩ := (hb N ℓ hK M hM g hg hgd).2
  have hgcont : Continuous g := hfcont.comp (continuous_id.add continuous_const)
  have hmeas := Internal.measurable_plainSum ℓ N hfcont.measurable
  have hmeasg := Internal.measurable_plainSum ℓ N hgcont.measurable
  have hlaw := Internal.map_plainSum_eq_map_translate P N ℓ hfcont c
  have hFi : Integrable (Internal.plainSum ℓ N f) (gibbsMeasure P N) :=
    (integrable_iff_of_map_eq hmeas hmeasg hlaw).2 hBi
  exact ⟨hFi, (variance_eq_of_map_eq hmeas hmeasg hlaw hFi hBi).trans_le hBv⟩

end Riesz1

namespace Riesz1.Internal

/-- The microscopic variance input follows from the proved
plain-sum bound. No a priori conclusion is assumed. -/
theorem regMicroAPrioriInput_of_externals
    (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler) :
    RegMicroAPrioriInput := by
  intro P lam hlam ε hε
  obtain ⟨C, hC, hb⟩ := a_priori_plain_translate hBE hPL P lam ε 2 hlam hε two_pos
  refine ⟨C, hC, ?_⟩
  intro N ℓ hK M hM c f hf hder
  exact hb N ℓ hK M hM c f hf (by
    simpa only [cutoffMajorant_eq_aPrioriEnvelope] using hder)

end Riesz1.Internal

end
