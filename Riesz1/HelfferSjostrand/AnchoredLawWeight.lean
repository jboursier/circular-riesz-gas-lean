/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.AnchoredHamiltonian

/-!
# The anchored law `μ*` of a general Gibbs probability

For an admissible pair potential `χ` and the Gibbs probability `μ` of the
fundamental region, the anchored law is `μ* = (Anch_N)_# μ`, where `Anch_N(x) = (x_2 - x_1, …,
x_N - x_1)`. This file proves the following, all for the general pair potential.

* The configuration volume, pushed forward by the anchored coordinates, is the product of the
  uniform law on `[0, 1)` and Lebesgue measure on `D_N^*`. The coordinate change has determinant
  one, so it preserves Lebesgue measure (`measurePreserving_anchorCoords`).
* Therefore `x_1 mod 1` is uniform on `[0, 1)`, independent of `Anch_N`, and `μ*` has density
  `e^{-H*} / Z` with respect to Lebesgue measure on `D_N^*`.

The density `e^{-H*}` is continuous on `D_N^*` but not known to be measurable on the whole space,
so the pushforward lemma assumes only almost-everywhere measurability on `D_N^*`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal

namespace Riesz1

variable {n : ℕ} {c : ℝ}

/-- The anchored density `e^{-H*(y)}` as an extended nonnegative real. -/
def hsAnchoredDensity (χ : HsPairPotentials n.succPNat c) (y : Fin n → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-hsAnchoredHamiltonian χ y))

/-- The unnormalized anchored weight: Lebesgue measure on `D_N^*` with density `e^{-H*}`. -/
def hsAnchoredWeight (χ : HsPairPotentials n.succPNat c) : Measure (Fin n → ℝ) :=
  (volume.restrict (anchoredDomain n)).withDensity (hsAnchoredDensity χ)

instance sFinite_hsAnchoredWeight (χ : HsPairPotentials n.succPNat c) :
    SFinite (hsAnchoredWeight χ) := by
  unfold hsAnchoredWeight
  infer_instance

/-- The anchored density is almost everywhere measurable on `D_N^*`, where it is continuous. -/
theorem aemeasurable_hsAnchoredDensity (χ : HsPairPotentials n.succPNat c) :
    AEMeasurable (hsAnchoredDensity χ) (volume.restrict (anchoredDomain n)) := by
  have hcont : ContinuousOn (hsAnchoredDensity χ) (anchoredDomain n) :=
    ENNReal.continuous_ofReal.comp_continuousOn
      (Real.continuous_exp.comp_continuousOn (continuousOn_hsAnchoredHamiltonian χ).neg)
  exact hcont.aemeasurable (measurableSet_anchoredDomain n)

/-- Pushing a density on the fundamental region forward by the anchored coordinates gives the
product of the uniform law on `[0, 1)` with the density `g` on `D_N^*`. The density `g` is only
required to be almost everywhere measurable on `D_N^*`. -/
theorem map_withDensity_anchorCoords (g : (Fin n → ℝ) → ℝ≥0∞)
    (hg : AEMeasurable g (volume.restrict (anchoredDomain n))) :
    ((configurationVolume n.succPNat).withDensity
        (fun X => g (anchorCoords n X.val).2)).map (fun X => anchorCoords n X.val) =
      (volume.restrict (Ico (0 : ℝ) 1)).prod
        ((volume.restrict (anchoredDomain n)).withDensity g) := by
  have hF : Measurable (fun X : Configuration n.succPNat => anchorCoords n X.val) :=
    measurable_anchorCoords_config n
  have hρ := map_anchorCoords_configurationVolume n
  have hG2 : AEMeasurable (fun p : ℝ × (Fin n → ℝ) => g p.2)
      ((configurationVolume n.succPNat).map (fun X => anchorCoords n X.val)) := by
    rw [hρ]
    exact hg.comp_snd
  calc ((configurationVolume n.succPNat).withDensity
          (fun X => g (anchorCoords n X.val).2)).map (fun X => anchorCoords n X.val)
      = ((configurationVolume n.succPNat).map (fun X => anchorCoords n X.val)).withDensity
          (fun p => g p.2) := by
        ext B hB
        rw [Measure.map_apply hF hB, withDensity_apply _ (hF hB), withDensity_apply _ hB,
          ← lintegral_indicator (hF hB), ← lintegral_indicator hB,
          lintegral_map' (hG2.indicator hB) hF.aemeasurable]
        refine lintegral_congr fun X => ?_
        by_cases h : anchorCoords n X.val ∈ B
        · rw [Set.indicator_of_mem (show X ∈ (fun X : Configuration n.succPNat =>
              anchorCoords n X.val) ⁻¹' B from h), Set.indicator_of_mem h]
        · rw [Set.indicator_of_notMem (show X ∉ (fun X : Configuration n.succPNat =>
              anchorCoords n X.val) ⁻¹' B from h), Set.indicator_of_notMem h]
    _ = (volume.restrict (Ico (0 : ℝ) 1)).prod
          ((volume.restrict (anchoredDomain n)).withDensity g) := by
        rw [hρ]
        exact (prod_withDensity_right₀ hg).symm

/-- The Gibbs weight of the fundamental region, pushed forward by the anchored coordinates, is the
product of the uniform law on `[0, 1)` and the anchored weight. -/
theorem map_hsFundamentalWeight (χ : HsPairPotentials n.succPNat c) :
    (hsFundamentalWeight χ).map (fun X => anchorCoords n X.val) =
      (volume.restrict (Ico (0 : ℝ) 1)).prod (hsAnchoredWeight χ) := by
  have hden : hsFundamentalWeight χ = (configurationVolume n.succPNat).withDensity
      (fun X => hsAnchoredDensity χ (anchorCoords n X.val).2) := by
    unfold hsFundamentalWeight hsAnchoredDensity
    congr 1
    funext X
    rw [hsFundamentalHamiltonian_eq_anchored]
  rw [hden, map_withDensity_anchorCoords _ (aemeasurable_hsAnchoredDensity χ)]
  rfl

/-- The partition function is the total mass of the anchored weight, since `x_1 mod 1` has total
mass one. -/
theorem hsPartitionFunction_eq_hsAnchoredWeight (χ : HsPairPotentials n.succPNat c) :
    hsPartitionFunction χ = hsAnchoredWeight χ univ := by
  have hF : Measurable (fun X : Configuration n.succPNat => anchorCoords n X.val) :=
    measurable_anchorCoords_config n
  calc hsPartitionFunction χ = hsFundamentalWeight χ univ := rfl
    _ = (hsFundamentalWeight χ).map (fun X => anchorCoords n X.val) univ := by
        rw [Measure.map_apply hF MeasurableSet.univ, preimage_univ]
    _ = ((volume.restrict (Ico (0 : ℝ) 1)).prod (hsAnchoredWeight χ)) univ := by
        rw [map_hsFundamentalWeight]
    _ = hsAnchoredWeight χ univ := by
        rw [← univ_prod_univ, Measure.prod_prod, measure_restrict_Ico_univ, one_mul]

/-- The normalized anchored law: the density `e^{-H*} / Z` on `D_N^*`. The law `μ*` has density
proportional to `e^{-H*}` on `D_N^*`, with the constant fixed by total mass one. -/
def hsAnchoredLaw (χ : HsPairPotentials n.succPNat c) : Measure (Fin n → ℝ) :=
  (hsAnchoredWeight χ univ)⁻¹ • hsAnchoredWeight χ

/-- The anchored law is a probability measure. -/
theorem isProbabilityMeasure_hsAnchoredLaw (χ : HsPairPotentials n.succPNat c) (hc : 0 < c) :
    IsProbabilityMeasure (hsAnchoredLaw χ) := by
  have hpos : 0 < hsAnchoredWeight χ univ := by
    rw [← hsPartitionFunction_eq_hsAnchoredWeight]
    exact hsPartitionFunction_pos χ
  have hfin : hsAnchoredWeight χ univ < ⊤ := by
    rw [← hsPartitionFunction_eq_hsAnchoredWeight]
    exact hsPartitionFunction_lt_top χ hc
  refine ⟨?_⟩
  unfold hsAnchoredLaw
  rw [Measure.smul_apply, smul_eq_mul]
  exact ENNReal.inv_mul_cancel hpos.ne' hfin.ne

/-- **Anchored law.** The Gibbs probability `μ` of the fundamental region,
pushed forward by the anchored coordinates, is the product of the uniform law on `[0, 1)` and the
normalized anchored law `μ*`. -/
theorem coe_hsGibbsProbability (χ : HsPairPotentials n.succPNat c) (hc : 0 < c) :
    ((hsGibbsProbability χ hc : ProbabilityMeasure (Configuration n.succPNat)) :
        Measure (Configuration n.succPNat)) =
      (hsPartitionFunction χ)⁻¹ • hsFundamentalWeight χ :=
  rfl

theorem map_hsGibbs_anchorCoords (χ : HsPairPotentials n.succPNat c) (hc : 0 < c) :
    (((hsGibbsProbability χ hc : ProbabilityMeasure (Configuration n.succPNat))) :
        Measure (Configuration n.succPNat)).map (fun X => anchorCoords n X.val) =
      (volume.restrict (Ico (0 : ℝ) 1)).prod (hsAnchoredLaw χ) := by
  have hF : AEMeasurable (fun X : Configuration n.succPNat => anchorCoords n X.val)
      (hsFundamentalWeight χ) := (measurable_anchorCoords_config n).aemeasurable
  rw [coe_hsGibbsProbability, Measure.map_smul _ hF, map_hsFundamentalWeight,
    hsPartitionFunction_eq_hsAnchoredWeight, hsAnchoredLaw, ← Measure.prod_smul_right]

/-- The first coordinate `x_1` of a configuration is uniform on `[0, 1)` under the Gibbs
probability, so `x_1 mod 1` is uniform on the circle. -/
theorem map_fst_hsGibbs (χ : HsPairPotentials n.succPNat c) (hc : 0 < c) :
    (((hsGibbsProbability χ hc : ProbabilityMeasure (Configuration n.succPNat))) :
        Measure (Configuration n.succPNat)).map (fun X => X.val 0) =
      volume.restrict (Ico (0 : ℝ) 1) := by
  have := isProbabilityMeasure_hsAnchoredLaw χ hc (n := n)
  have h := congrArg (Measure.map Prod.fst) (map_hsGibbs_anchorCoords χ hc (n := n))
  rw [Measure.map_map measurable_fst (measurable_anchorCoords_config n),
    Measure.map_fst_prod, measure_univ, one_smul] at h
  exact h

/-- The anchored gap vector has the law `μ*` under the Gibbs probability. -/
theorem map_snd_hsGibbs (χ : HsPairPotentials n.succPNat c) (hc : 0 < c) :
    (((hsGibbsProbability χ hc : ProbabilityMeasure (Configuration n.succPNat))) :
        Measure (Configuration n.succPNat)).map
      (fun X : Configuration n.succPNat => (anchorCoords n X.val).2) =
      hsAnchoredLaw χ := by
  have := isProbabilityMeasure_hsAnchoredLaw χ hc (n := n)
  have h := congrArg (Measure.map Prod.snd) (map_hsGibbs_anchorCoords χ hc (n := n))
  rw [Measure.map_map measurable_snd (measurable_anchorCoords_config n),
    Measure.map_snd_prod, measure_restrict_Ico_univ, one_smul] at h
  exact h

/-- **Independence.** Under the Gibbs probability, `x_1 mod 1` and the
anchored coordinates `Anch_N` are independent. -/
theorem indepFun_hsGibbs (χ : HsPairPotentials n.succPNat c) (hc : 0 < c) :
    IndepFun (fun X : Configuration n.succPNat => X.val 0)
      (fun X : Configuration n.succPNat => (anchorCoords n X.val).2)
      (hsGibbsProbability χ hc : Measure (Configuration n.succPNat)) := by
  have : IsProbabilityMeasure (hsGibbsProbability χ hc : Measure (Configuration n.succPNat)) :=
    inferInstance
  have hf : Measurable (fun X : Configuration n.succPNat => X.val 0) :=
    (measurable_pi_apply 0).comp measurable_subtype_coe
  have hg : Measurable (fun X : Configuration n.succPNat => (anchorCoords n X.val).2) :=
    measurable_snd.comp (measurable_anchorCoords_config n)
  rw [indepFun_iff_map_prod_eq_prod_map_map hf.aemeasurable hg.aemeasurable,
    map_fst_hsGibbs χ hc, map_snd_hsGibbs χ hc]
  exact map_hsGibbs_anchorCoords χ hc

end Riesz1

end
end
