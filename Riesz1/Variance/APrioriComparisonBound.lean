/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.APrioriComparisonRepresentation
public import Riesz1.Variance.APrioriComparisonEnergy
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-!
# Measurable-field comparison with the affine gradient

The energy step of the comparison assertion in the proof of Lemma 5.2, for arbitrary
nonnegative fixed weights. This internal helper retains the coordinate
bound from the paper and imposes no differentiability on the field.
-/

@[expose] public section

noncomputable section

open MeasureTheory InnerProductSpace Classical

namespace Riesz1.APrioriComparison

variable {n : ℕ} {c : ℝ}

/-- Coordinate domination of the cutoff field by the full affine gradient.
The scalar second moment controls its inverse energy through representation.
This helper is conditional on admissibility. The actual tilted potentials
are supplied in `Riesz1.a_priori_comparison_energy`. -/
theorem cutoff_energy_le_comparator (χ : HsPairPotentials n.succPNat c) (hc : 0 < c)
    (hPL : External.PrekopaLeindler) (hn : 0 < n) {C : ℝ} (hadm : HsAdmissible χ C)
    (s K γ ε t : ℝ) (ht : 0 ≤ t) (J : Finset (Fin (n + 1)))
    (w : Fin (n + 1) → ℝ) (hw : ∀ i, 0 ≤ w i)
    (v : AnchoredEuclidean n → AnchoredEuclidean n) (hvm : Measurable v)
    (hz : ∀ i, ∀ᵐ y ∂anchoredMeasureE χ, i.succ ∉ J → v y i = 0)
    (hb : ∀ i, ∀ᵐ y ∂anchoredMeasureE χ,
      anchoredCutoff n.succPNat s K γ ε (WithLp.ofLp y) * |v y i| ≤
        t * anchoredCutoff n.succPNat s K γ ε (WithLp.ofLp y) *
          (((n : ℝ) + 1) * w i.succ)) :
    ∃ hv : MemLp (fun y => anchoredCutoff n.succPNat s K γ ε (WithLp.ofLp y) • v y)
        2 (anchoredMeasureE χ),
      anchoredInverseEnergy χ hc
        (hv.toLp (fun y => anchoredCutoff n.succPNat s K γ ε (WithLp.ofLp y) • v y)) ≤
          t ^ 2 * ∫ y, (∑ i ∈ J, w i *
            (((n : ℝ) + 1) * anchorVector (WithLp.ofLp y) i - (i : ℕ))) ^ 2
              ∂anchoredMeasureE χ := by
  have := isProbabilityMeasure_anchoredMeasureE χ hc
  let f := fun y : AnchoredEuclidean n =>
    ∑ i ∈ J, w i * (((n : ℝ) + 1) * anchorVector (WithLp.ofLp y) i - (i : ℕ))
  let u := fun y : AnchoredEuclidean n => anchoredCutoff n.succPNat s K γ ε (WithLp.ofLp y) • v y
  have hum : Measurable u :=
    ((measurable_anchoredCutoff (N := n.succPNat) s K γ ε).comp (PiLp.continuous_ofLp 2 _).measurable).smul hvm
  have hu (i : Fin n) : ∀ᵐ y ∂anchoredMeasureE χ,
      |u y i| ≤ t * (if i.succ ∈ J then ((n : ℝ) + 1) * w i.succ else 0) := by
    filter_upwards [hz i, hb i] with y hy0 hyb
    have hη0 := anchoredCutoff_nonneg (N := n.succPNat) s K γ ε (WithLp.ofLp y)
    have hη1 := anchoredCutoff_le_one (N := n.succPNat) s K γ ε (WithLp.ofLp y)
    by_cases hi : i.succ ∈ J
    · rw [ite_eq_left hi]
      change |anchoredCutoff n.succPNat s K γ ε (WithLp.ofLp y) * v y i| ≤ _
      rw [abs_mul, abs_of_nonneg hη0]
      apply hyb.trans
      calc _ = anchoredCutoff n.succPNat s K γ ε (WithLp.ofLp y) *
          (t * (((n : ℝ) + 1) * w i.succ)) := by ring
        _ ≤ 1 * (t * (((n : ℝ) + 1) * w i.succ)) :=
          mul_le_mul_of_nonneg_right hη1 (mul_nonneg ht (mul_nonneg (by positivity) (hw _)))
        _ = _ := one_mul _
    · rw [ite_eq_right hi]
      change |anchoredCutoff n.succPNat s K γ ε (WithLp.ofLp y) * v y i| ≤ _
      rw [hy0 hi]
      simp
  have huL : MemLp u 2 (anchoredMeasureE χ) := by
    apply MemLp.of_eval_piLp
    intro i
    apply MemLp.of_bound ((measurable_pi_apply i).comp ((PiLp.continuous_ofLp 2 _).measurable.comp hum)).aestronglyMeasurable
      (t * (if i.succ ∈ J then ((n : ℝ) + 1) * w i.succ else 0))
    simpa only [Function.comp_def, Real.norm_eq_abs] using hu i
  obtain ⟨hg, hge⟩ := smooth_gradient_energy_le_secondMoment χ hc hPL hn hadm f (comparator_smooth n J w)
  refine ⟨huL, ?_⟩
  have hcmp := inverseEnergy_le_scaled χ hc (huL.toLp u) (hg.toLp (gradient f)) t (fun i => ?_)
  · exact hcmp.trans (mul_le_mul_of_nonneg_left hge (sq_nonneg t))
  · filter_upwards [hu i, huL.coeFn_toLp, hg.coeFn_toLp] with y hy hyu hyg
    rw [hyu, hyg]
    rw [show gradient f y i = _ from comparator_gradient_apply n J w y i]
    exact hy

end Riesz1.APrioriComparison

end
