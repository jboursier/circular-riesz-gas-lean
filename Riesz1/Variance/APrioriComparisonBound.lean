/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.APrioriComparisonProduct
public import Riesz1.HelfferSjostrand.AnchoredInverseEnergy
public import Riesz1.Variance.APrioriComparisonEnergy
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-!
# Measurable-field comparison with the cutoff comparator

The energy step of the comparison assertion in the proof of Lemma 5.2, for arbitrary
nonnegative fixed weights. This internal helper retains the coordinate
bound from the paper and imposes no differentiability on the field.
-/

@[expose] public section

noncomputable section

open MeasureTheory InnerProductSpace Set Classical

namespace Riesz1.APrioriComparison

variable {n : ℕ} {c : ℝ}

/-- Coordinate domination compares the cutoff field with the cutoff
comparator gradient. Sub-additivity then separates its variance and the
energy of the comparator times the cutoff gradient. -/
theorem cutoff_energy_le_comparator (χ : HsPairPotentials n.succPNat c) (hc : 0 < c)
    (hPL : External.PrekopaLeindler) (hn : 0 < n) {C : ℝ} (hadm : HsAdmissible χ C)
    (s K γ ε t : ℝ) (hK : 1 ≤ K) (hε : 0 ≤ ε) (ht : 0 ≤ t) (J : Finset (Fin (n + 1)))
    (w : Fin (n + 1) → ℝ) (hw : ∀ i, 0 ≤ w i)
    (v : AnchoredEuclidean n → AnchoredEuclidean n) (hvm : Measurable v)
    (hz : ∀ i, ∀ᵐ y ∂anchoredMeasureE χ, i.succ ∉ J → v y i = 0)
    (hb : ∀ i, ∀ᵐ y ∂anchoredMeasureE χ,
      anchoredCutoff n.succPNat s K γ ε (WithLp.ofLp y) * |v y i| ≤
        t * anchoredCutoff n.succPNat s K γ ε (WithLp.ofLp y) *
          (((n : ℝ) + 1) * w i.succ))
    (he : MemLp (fun y =>
      (∑ i ∈ J, w i * (((n : ℝ) + 1) * anchorVector (WithLp.ofLp y) i - (i : ℕ))) •
        gradient (fun z : AnchoredEuclidean n =>
          anchoredCutoff n.succPNat s K γ ε (WithLp.ofLp z)) y) 2 (anchoredMeasureE χ)) :
    ∃ hv : MemLp (fun y => anchoredCutoff n.succPNat s K γ ε (WithLp.ofLp y) • v y)
        2 (anchoredMeasureE χ),
      anchoredInverseEnergy χ hc
        (hv.toLp (fun y => anchoredCutoff n.succPNat s K γ ε (WithLp.ofLp y) • v y)) ≤
          2 * t ^ 2 * ProbabilityTheory.variance (fun y =>
            anchoredCutoff n.succPNat s K γ ε (WithLp.ofLp y) *
              ∑ i ∈ J, w i * (((n : ℝ) + 1) * anchorVector (WithLp.ofLp y) i - (i : ℕ)))
            (anchoredMeasureE χ) +
          2 * t ^ 2 * anchoredInverseEnergy χ hc (he.toLp _) := by
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
  let η := fun y : AnchoredEuclidean n => anchoredCutoff n.succPNat s K γ ε (WithLp.ofLp y)
  let g := fun y => η y • gradient f y
  let e := fun y => f y • gradient η y
  have hηm : Measurable η :=
    (measurable_anchoredCutoff (N := n.succPNat) s K γ ε).comp
      (measurable_pi_iff.mpr fun i => (EuclideanSpace.proj (𝕜 := ℝ) i).measurable)
  have hg : MemLp g 2 (anchoredMeasureE χ) := by
    have hgrad := (WeightedSobolev.memLp_of_smoothNearClosure
      (isBounded_anchoredSimplex n) (ae_mem_anchoredSimplex χ)
      ⟨Set.univ, isOpen_univ, subset_univ _, (comparator_smooth n J w).contDiffOn⟩).2
    apply hgrad.mono (show AEStronglyMeasurable g (anchoredMeasureE χ) from
      hηm.aestronglyMeasurable.smul hgrad.aestronglyMeasurable)
    exact Filter.Eventually.of_forall fun y => by
      change ‖η y • gradient f y‖ ≤ ‖gradient f y‖
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (anchoredCutoff_nonneg s K γ ε _)]
      exact mul_le_of_le_one_left (norm_nonneg _) (anchoredCutoff_le_one s K γ ε _)
  have hH := cutoff_comparator_h1 χ hc (by omega) s K γ ε hK hε f (comparator_smooth n J w)
  have hsum : IsAnchoredH1 χ (fun y => η y * f y) (fun y => g y + e y) := hH
  let S : AnchoredSobolev χ := ⟨(hsum.1.toLp _, (hg.add he).toLp _),
    hsum.congr hsum.1.coeFn_toLp.symm (hg.add he).coeFn_toLp.symm⟩
  have hS : S.val.2 = hg.toLp g + he.toLp e := hg.toLp_add he
  have hge : anchoredInverseEnergy χ hc (hg.toLp g) ≤
      2 * ProbabilityTheory.variance (fun y => η y * f y) (anchoredMeasureE χ) +
        2 * anchoredInverseEnergy χ hc (he.toLp e) := by
    have hid : hg.toLp g = S.val.2 + (-1 : ℝ) • he.toLp e := by rw [hS]; module
    rw [hid]
    have hs := (anchoredInverse_symmetry_positivity_subadditivity χ hc).2.2.2.1
      S.val.2 ((-1 : ℝ) • he.toLp e)
    rw [inverseEnergy_smul, gradient_energy_eq_variance χ hc hPL hn hadm S] at hs
    have hv := ProbabilityTheory.variance_congr hsum.1.coeFn_toLp
    dsimp only [S] at hs
    rw [hv] at hs
    norm_num only [even_two, Even.neg_pow, one_pow, one_mul] at hs
    exact hs
  refine ⟨huL, ?_⟩
  change anchoredInverseEnergy χ hc (huL.toLp u) ≤
    2 * t ^ 2 * ProbabilityTheory.variance (fun y => η y * f y) (anchoredMeasureE χ) +
      2 * t ^ 2 * anchoredInverseEnergy χ hc (he.toLp e)
  have hcmp := inverseEnergy_le_scaled χ hc (huL.toLp u) (hg.toLp g) t (fun i => ?_)
  · exact (hcmp.trans (mul_le_mul_of_nonneg_left hge (sq_nonneg t))).trans_eq (by ring)
  · filter_upwards [hz i, hb i, huL.coeFn_toLp, hg.coeFn_toLp] with y hy0 hyb hyu hyg
    rw [hyu, hyg]
    change |η y * v y i| ≤ t * (η y * gradient f y i)
    rw [abs_mul, abs_of_nonneg (anchoredCutoff_nonneg s K γ ε _),
      show gradient f y i = _ from comparator_gradient_apply n J w y i]
    by_cases hi : i.succ ∈ J
    · rw [ite_eq_left hi]
      exact hyb.trans_eq (by ring)
    · rw [ite_eq_right hi, hy0 hi]
      simp

end Riesz1.APrioriComparison

end
