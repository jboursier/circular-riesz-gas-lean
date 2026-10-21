/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Rigidity.GapLawSimplex
public import Riesz1.Rigidity.GapLawMoments
public import Riesz1.ToMathlib.LogConcave.MarginalContinuous
public import Mathlib.Analysis.Convex.Continuous

/-!
# The two-particle one-gap density

For two particles there is no fiber to integrate. The first gap is twice the
single anchored coordinate, and its density has the corresponding factor `1/2`.
The result applies to every integer label by the proved cyclic symmetry.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Riesz1

/-- The normalized one-gap density for two particles. -/
def twoGapProbabilityDensity (P : Parameters) (t : ℝ) : ℝ :=
  anchoredProbabilityDensity P 1 (fun _ => t / 2) / 2

lemma measurable_anchoredProbabilityDensity (P : Parameters) (n : ℕ) :
    Measurable (anchoredProbabilityDensity P n) := by
  exact measurable_const.mul (Real.measurable_exp.comp
    ((measurable_anchoredEnergy _ _).const_mul _))

lemma mem_anchoredDomain_one (t : ℝ) :
    (fun _ : Fin 1 => t) ∈ anchoredDomain 1 ↔ t ∈ Ioo (0 : ℝ) 1 := by
  constructor
  · intro h
    exact h.1 0
  · intro h
    refine ⟨fun _ => h, ?_⟩
    intro i j hij
    exact (not_lt_of_ge (le_of_eq (Subsingleton.elim j i)) hij).elim

theorem twoGapProbabilityDensity_pos (P : Parameters) (t : ℝ) :
    0 < twoGapProbabilityDensity P t :=
  div_pos (anchoredProbabilityDensity_pos P 1 _) (by norm_num)

theorem concaveOn_log_twoGapProbabilityDensity (P : Parameters) :
    ConcaveOn ℝ (Ioo (0 : ℝ) 2) (fun t => Real.log (twoGapProbabilityDensity P t)) := by
  have hm (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 2) :
      (fun _ : Fin 1 => t / 2) ∈ anchoredDomain 1 :=
    (mem_anchoredDomain_one _).mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hlog (t : ℝ) : Real.log (twoGapProbabilityDensity P t) =
      Real.log (anchoredProbabilityDensity P 1 (fun _ => t / 2)) - Real.log 2 := by
    rw [twoGapProbabilityDensity, Real.log_div (anchoredProbabilityDensity_pos P 1 _).ne'
      (by norm_num : (2 : ℝ) ≠ 0)]
  refine ⟨convex_Ioo _ _, ?_⟩
  intro x hx y hy a b ha hb hab
  simp_rw [hlog]
  have h := (concaveOn_log_anchoredProbabilityDensity P 1).2 (hm x hx) (hm y hy) ha hb hab
  have he : a • (fun _ : Fin 1 => x / 2) + b • (fun _ : Fin 1 => y / 2) =
      (fun _ : Fin 1 => (a * x + b * y) / 2) := by ext; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  rw [he] at h
  simp only [smul_eq_mul] at h ⊢
  have hc : a * Real.log 2 + b * Real.log 2 = Real.log 2 := by
    rw [← add_mul, hab, one_mul]
  nlinarith only [h, hc]

theorem continuousOn_twoGapProbabilityDensity (P : Parameters) :
    ContinuousOn (twoGapProbabilityDensity P) (Ioo (0 : ℝ) 2) := by
  have hc := (concaveOn_log_twoGapProbabilityDensity P).continuousOn isOpen_Ioo
  have he : EqOn (fun t => Real.exp (Real.log (twoGapProbabilityDensity P t)))
      (twoGapProbabilityDensity P) (Ioo (0 : ℝ) 2) := by
    intro t _
    exact Real.exp_log (twoGapProbabilityDensity_pos P t)
  exact (Real.continuous_exp.comp_continuousOn hc).congr he.symm

lemma map_anchoredLaw_one_eval (P : Parameters) :
    (anchoredLaw P 1).map (fun y => y 0) =
      (volume.restrict (Ioo (0 : ℝ) 1)).withDensity
        (fun t => ENNReal.ofReal (anchoredProbabilityDensity P 1 (fun _ => t))) := by
  let e : (Fin 1 → ℝ) ≃ᵐ ℝ := MeasurableEquiv.funUnique (Fin 1) ℝ
  have he (y : Fin 1 → ℝ) : e y = y 0 := rfl
  have hD : e ⁻¹' Ioo (0 : ℝ) 1 = anchoredDomain 1 := by
    ext y
    have hy : (fun _ : Fin 1 => y 0) = y := by ext i; exact congrArg y (Subsingleton.elim _ _)
    rw [← hy]
    exact (mem_anchoredDomain_one (y 0)).symm
  have hevol : (volume : Measure (Fin 1 → ℝ)).map e = volume :=
    (volume_preserving_funUnique (Fin 1) ℝ).map_eq
  have hvol : (volume.restrict (anchoredDomain 1)).map e =
      volume.restrict (Ioo (0 : ℝ) 1) := by
    rw [← hD, ← Measure.restrict_map e.measurable measurableSet_Ioo, hevol]
  have hm : Measurable (fun t : ℝ => ENNReal.ofReal
      (anchoredProbabilityDensity P 1 (fun _ => t))) :=
    ENNReal.measurable_ofReal.comp ((measurable_anchoredProbabilityDensity P 1).comp
      (Measurable.of_eval fun _ => measurable_id))
  rw [anchoredLaw_eq_withDensity]
  change ((volume.restrict (anchoredDomain 1)).withDensity _).map e = _
  have hcomp : (fun y => ENNReal.ofReal (anchoredProbabilityDensity P 1 y)) =
      fun y => ENNReal.ofReal (anchoredProbabilityDensity P 1 (fun _ => e y)) := by
    ext y
    congr 2
    ext i
    exact congrArg y (Subsingleton.elim _ _)
  rw [hcomp, map_withDensity_comp _ e.measurable hm, hvol]

lemma map_interval_withDensity_mul_two (f : ℝ → ℝ) (hf : Measurable f) :
    ((volume.restrict (Ioo (0 : ℝ) 1)).withDensity (fun t => ENNReal.ofReal (f t))).map
      (fun t => 2 * t) =
      (volume.restrict (Ioo (0 : ℝ) 2)).withDensity
        (fun t => ENNReal.ofReal (f (t / 2) / 2)) := by
  have hpre : (fun t : ℝ => 2 * t) ⁻¹' Ioo (0 : ℝ) 2 = Ioo (0 : ℝ) 1 := by
    ext t
    simp only [mem_preimage, mem_Ioo]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  have hmap : (volume.restrict (Ioo (0 : ℝ) 1)).map (fun t => 2 * t) =
      ENNReal.ofReal (1 / 2 : ℝ) • volume.restrict (Ioo (0 : ℝ) 2) := by
    rw [← hpre, ← Measure.restrict_map (by fun_prop) measurableSet_Ioo,
      Real.map_volume_mul_left (by norm_num : (2 : ℝ) ≠ 0), Measure.restrict_smul]
    norm_num
  have hcomp : (fun t : ℝ => ENNReal.ofReal (f t)) =
      fun t => ENNReal.ofReal (f ((2 * t) / 2)) := by
    ext t
    congr 2
    ring
  have hm : Measurable (fun t : ℝ => ENNReal.ofReal (f (t / 2))) :=
    ENNReal.measurable_ofReal.comp (hf.comp (by fun_prop))
  rw [hcomp, map_withDensity_comp _ (by fun_prop) hm, hmap, withDensity_smul_measure]
  have hd : (fun t => ENNReal.ofReal (f (t / 2) / 2)) =
      ENNReal.ofReal (1 / 2 : ℝ) • (fun t => ENNReal.ofReal (f (t / 2))) := by
    ext t
    change ENNReal.ofReal (f (t / 2) / 2) =
      ENNReal.ofReal (1 / 2 : ℝ) * ENNReal.ofReal (f (t / 2))
    rw [show f (t / 2) / 2 = (1 / 2 : ℝ) * f (t / 2) by ring,
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  rw [hd, withDensity_smul _ hm]

/-- Every two-particle gap has the explicit positive continuous log-concave density. -/
theorem map_gap_gibbsMeasure_two_density (P : Parameters) (j : ℤ) :
    (gibbsMeasure P (2 : ℕ+)).map (fun X => gap X j) =
      (volume.restrict (Ioo (0 : ℝ) 2)).withDensity
        (fun t => ENNReal.ofReal (twoGapProbabilityDensity P t)) := by
  rw [map_gap_gibbsMeasure_eq P 2 (by norm_num) j]
  have hgap : (fun y : Fin 1 → ℝ => anchoredGapAt 1 y 0) = fun y => 2 * y 0 := by
    ext y
    unfold anchoredGapAt
    have h₀ : anchoredCyclicOffset 1 y 0 = 0 := anchoredCyclicOffset_natCast 1 y 0
    have h₁ : anchoredCyclicOffset 1 y 1 = y 0 := anchoredCyclicOffset_natCast 1 y 1
    simp only [zero_add, h₀, h₁, sub_zero, Nat.cast_one]
    ring
  rw [show (2 : ℕ+) = Nat.succPNat 1 from rfl, map_gap_eq_map_anchoredGapAt, hgap]
  change (anchoredLaw P 1).map ((fun t : ℝ => 2 * t) ∘ (fun y : Fin 1 → ℝ => y 0)) = _
  rw [← Measure.map_map (f := fun y : Fin 1 → ℝ => y 0) (by fun_prop) (by fun_prop),
    map_anchoredLaw_one_eval]
  exact map_interval_withDensity_mul_two _ ((measurable_anchoredProbabilityDensity P 1).comp
    (Measurable.of_eval fun _ => measurable_id))

/-- Uniqueness means equality on the open support. Values elsewhere are unrestricted. -/
theorem twoGapProbabilityDensity_unique (P : Parameters) (j : ℤ) (f : ℝ → ℝ)
    (hf : ContinuousOn f (Ioo (0 : ℝ) 2)) (hfn : ∀ t ∈ Ioo (0 : ℝ) 2, 0 ≤ f t)
    (hlaw : (gibbsMeasure P (2 : ℕ+)).map (fun X => gap X j) =
      (volume.restrict (Ioo (0 : ℝ) 2)).withDensity (fun t => ENNReal.ofReal (f t))) :
    EqOn f (twoGapProbabilityDensity P) (Ioo (0 : ℝ) 2) := by
  exact continuous_interval_density_unique hf (continuousOn_twoGapProbabilityDensity P)
    hfn (fun t _ => (twoGapProbabilityDensity_pos P t).le)
    (hlaw.symm.trans (map_gap_gibbsMeasure_two_density P j))

end Riesz1

end
end
