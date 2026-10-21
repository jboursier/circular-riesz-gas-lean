/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Rigidity.GapLawReversal
public import Riesz1.ToMathlib.HurwitzKernel.Derivatives

/-!
# Convexity of the Gibbs energy in cumulative gap coordinates

The ordered offsets `0 < z₁ < ⋯ < zₙ < 1` parametrize the gap simplex by
`(n+1) (z₁, z₂-z₁, …, zₙ-zₙ₋₁, 1-zₙ)`. In these affine coordinates
the energy is convex and its normalized exponential is positive and log-concave.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal

namespace Riesz1

/-- The open simplex of positive gaps with total length `N`. -/
def gapSimplex (N : ℕ+) : Set (Fin (N : ℕ) → ℝ) :=
  {v | (∀ i, 0 < v i) ∧ ∑ i, v i = ((N : ℕ) : ℝ)}

/-- The cumulative-gap parametrization is injective even on its ambient vector space. -/
lemma injective_anchoredGapVector (n : ℕ) : Function.Injective (anchoredGapVector n) := by
  intro y z h
  have hdiff (k : ℕ) (hk : k < n + 1) :
      anchoredCyclicOffset n y (k + 1) - anchoredCyclicOffset n y k =
        anchoredCyclicOffset n z (k + 1) - anchoredCyclicOffset n z k := by
    have hi : k < (n.succPNat : ℕ) := hk
    have hh := congrFun h ⟨k, hi⟩
    change (n + 1 : ℝ) * _ = (n + 1 : ℝ) * _ at hh
    exact mul_left_cancel₀ (by positivity : (n + 1 : ℝ) ≠ 0) hh
  have heq (k : ℕ) : k ≤ n → anchoredCyclicOffset n y k = anchoredCyclicOffset n z k := by
    induction k with
    | zero =>
      intro _
      have hy := anchoredCyclicOffset_natCast n y 0
      have hz := anchoredCyclicOffset_natCast n z 0
      change anchoredCyclicOffset n y 0 = 0 at hy
      change anchoredCyclicOffset n z 0 = 0 at hz
      exact hy.trans hz.symm
    | succ k ih =>
      intro hk
      have hd := hdiff k (by omega)
      have hi := ih (by omega)
      push_cast
      linarith
  funext i
  have hi := heq (i.succ : ℕ) (by have := i.isLt; simp only [Fin.val_succ]; omega)
  rw [anchoredCyclicOffset_natCast n y i.succ,
    anchoredCyclicOffset_natCast n z i.succ] at hi
  exact hi

/-- Valid ordered offsets give positive gaps whose sum is the circumference `N`. -/
lemma anchoredGapVector_mem_gapSimplex (n : ℕ) {y : Fin n → ℝ}
    (hy : y ∈ anchoredDomain n) : anchoredGapVector n y ∈ gapSimplex n.succPNat := by
  let X : Configuration n.succPNat :=
    ⟨anchorInverse n (0, y), anchorInverse_mem n ⟨by norm_num, hy⟩⟩
  have hcoords : (anchorCoords n X.val).2 = y :=
    congrArg Prod.snd (anchorCoords_anchorInverse n (0, y))
  have hvec : gapVector X = anchoredGapVector n y := by
    rw [gapVector_eq_anchoredGapVector, hcoords]
  rw [← hvec]
  refine ⟨fun i => gap_pos X (i : ℕ), ?_⟩
  change (∑ i : Fin (n.succPNat : ℕ), gap X (i : ℕ)) = _
  exact (Fin.sum_univ_eq_sum_range (fun r : ℕ => gap X (r : ℤ))
    (n.succPNat : ℕ)).trans (sum_gap_eq X)

lemma convex_anchoredDomain (n : ℕ) : Convex ℝ (anchoredDomain n) := by
  intro y hy z hz a b ha hb hab
  refine ⟨?_, ?_⟩
  · intro i
    exact (convex_Ioo (0 : ℝ) 1) (hy.1 i) (hz.1 i) ha hb hab
  · intro i j hij
    change a * y i + b * z i < a * y j + b * z j
    have hyij := hy.2 hij
    have hzij := hz.2 hij
    rcases eq_or_lt_of_le ha with rfl | ha'
    · have hb' : b = 1 := by linarith
      simpa [hb'] using hzij
    · nlinarith

lemma strictMono_anchorVector {n : ℕ} {y : Fin n → ℝ} (hy : y ∈ anchoredDomain n) :
    StrictMono (anchorVector y) := by
  exact Fin.strictMono_cons.mpr ⟨fun i => (hy.1 i).1, hy.2⟩

lemma anchorVector_combo {n : ℕ} (y z : Fin n → ℝ) (a b : ℝ)
    (i : Fin (n.succPNat : ℕ)) :
    anchorVector (a • y + b • z) i = a * anchorVector y i + b * anchorVector z i := by
  induction i using Fin.cases with
  | zero => simp [anchorVector]
  | succ i => rfl

lemma convexOn_anchored_pair (s : RieszExponent) (n : ℕ)
    (i j : Fin (n.succPNat : ℕ)) (hij : i ≠ j) :
    ConvexOn ℝ (anchoredDomain n) (fun y =>
      rieszRepresentative s ((anchorVector y i - anchorVector y j : ℝ) : UnitAddCircle)) := by
  refine ⟨convex_anchoredDomain n, ?_⟩
  intro y hy z hz a b ha hb hab
  have hyi := anchorVector_mem_Ico hy i
  have hyj := anchorVector_mem_Ico hy j
  have hzi := anchorVector_mem_Ico hz i
  have hzj := anchorVector_mem_Ico hz j
  rcases hyi with ⟨hyi0, hyi1⟩
  rcases hyj with ⟨hyj0, hyj1⟩
  rcases hzi with ⟨hzi0, hzi1⟩
  rcases hzj with ⟨hzj0, hzj1⟩
  have harg : anchorVector (a • y + b • z) i - anchorVector (a • y + b • z) j =
      a * (anchorVector y i - anchorVector y j) +
        b * (anchorVector z i - anchorVector z j) := by
    rw [anchorVector_combo, anchorVector_combo]
    ring
  change hurwitzKernel s.val (anchorVector (a • y + b • z) i -
      anchorVector (a • y + b • z) j) ≤
    a * hurwitzKernel s.val (anchorVector y i - anchorVector y j) +
      b * hurwitzKernel s.val (anchorVector z i - anchorVector z j)
  rw [harg]
  rcases lt_or_gt_of_ne hij with hij | hji
  · have hc : ConvexOn ℝ (Ioo (-1 : ℝ) 0) (hurwitzKernel s.val) := by
      simpa using (strictConvexOn_hurwitzKernel s.val s.2.1 s.2.2 (-1)).convexOn
    have hym := strictMono_anchorVector hy hij
    have hzm := strictMono_anchorVector hz hij
    exact hc.2 ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ ha hb hab
  · have hc : ConvexOn ℝ (Ioo (0 : ℝ) 1) (hurwitzKernel s.val) := by
      simpa using (strictConvexOn_hurwitzKernel s.val s.2.1 s.2.2 0).convexOn
    have hym := strictMono_anchorVector hy hji
    have hzm := strictMono_anchorVector hz hji
    exact hc.2 ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ ha hb hab

/-- Convexity of the energy in cumulative gap coordinates, with no analytic hypothesis. -/
theorem convexOn_anchoredEnergy (s : RieszExponent) (n : ℕ) :
    ConvexOn ℝ (anchoredDomain n) (anchoredEnergy s n) := by
  refine ⟨convex_anchoredDomain n, ?_⟩
  intro y hy z hz a b ha hb hab
  have hsum : (∑ i : Fin (n.succPNat : ℕ), ∑ j ∈ Finset.univ.erase i,
      rieszRepresentative s ((anchorVector (a • y + b • z) i -
        anchorVector (a • y + b • z) j : ℝ) : UnitAddCircle)) ≤
      ∑ i : Fin (n.succPNat : ℕ), ∑ j ∈ Finset.univ.erase i,
        (a * rieszRepresentative s ((anchorVector y i - anchorVector y j : ℝ) : UnitAddCircle) +
          b * rieszRepresentative s ((anchorVector z i - anchorVector z j : ℝ) : UnitAddCircle)) := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j hj
    exact (convexOn_anchored_pair s n i j (Finset.ne_of_mem_erase hj).symm).2 hy hz ha hb hab
  have hnonneg : 0 ≤ ((n.succPNat : ℕ) : ℝ) ^ (-s.val) := Real.rpow_nonneg (by positivity) _
  have h := mul_le_mul_of_nonneg_left hsum hnonneg
  simpa only [anchoredEnergy, Finset.sum_add_distrib, ← Finset.mul_sum, smul_eq_mul,
    mul_add, mul_left_comm] using h

/-- The real normalized Gibbs density in cumulative gap coordinates. -/
def anchoredProbabilityDensity (P : Parameters) (n : ℕ) (y : Fin n → ℝ) : ℝ :=
  (partitionFunction P n.succPNat).toReal⁻¹ *
    Real.exp (-P.val.1 * anchoredEnergy (parametersExponent P) n y)

lemma anchoredProbabilityDensity_pos (P : Parameters) (n : ℕ) (y : Fin n → ℝ) :
    0 < anchoredProbabilityDensity P n y := by
  have hZ : 0 < (partitionFunction P n.succPNat).toReal :=
    ENNReal.toReal_pos (partitionFunction_pos P _).ne' (partitionFunction_lt_top P _).ne
  exact mul_pos (inv_pos.mpr hZ) (Real.exp_pos _)

/-- The cumulative-gap chart has exactly the stated normalized exponential density. -/
theorem anchoredLaw_eq_withDensity (P : Parameters) (n : ℕ) :
    anchoredLaw P n = (volume.restrict (anchoredDomain n)).withDensity
      (fun y => ENNReal.ofReal (anchoredProbabilityDensity P n y)) := by
  have hZ : 0 < (partitionFunction P n.succPNat).toReal :=
    ENNReal.toReal_pos (partitionFunction_pos P _).ne' (partitionFunction_lt_top P _).ne
  have hd : (fun y => ENNReal.ofReal (anchoredProbabilityDensity P n y)) =
      (partitionFunction P n.succPNat)⁻¹ • anchoredDensity P n := by
    funext y
    simp only [anchoredProbabilityDensity, anchoredDensity, Pi.smul_apply, smul_eq_mul,
      ENNReal.ofReal_mul (inv_pos.mpr hZ).le, ENNReal.ofReal_inv_of_pos hZ,
      ENNReal.ofReal_toReal (partitionFunction_lt_top P _).ne]
  rw [hd, withDensity_smul _ (measurable_anchoredDensity P n)]
  unfold anchoredLaw anchoredWeight
  rw [partitionFunction_eq_anchoredWeight]
  rfl

/-- The joint gap law is the image of the positive density in the cumulative-gap chart. -/
theorem map_gapVector_gibbsMeasure_density (P : Parameters) (n : ℕ) :
    (gibbsMeasure P n.succPNat).map gapVector =
      ((volume.restrict (anchoredDomain n)).withDensity
        (fun y => ENNReal.ofReal (anchoredProbabilityDensity P n y))).map
        (anchoredGapVector n) := by
  have hS : Measurable (fun X : Configuration n.succPNat => (anchorCoords n X.val).2) :=
    measurable_snd.comp (measurable_anchorCoords_config n)
  rw [← anchoredLaw_eq_withDensity, ← map_snd_gibbsMeasure P n,
    Measure.map_map (measurable_anchoredGapVector n) hS]
  congr 1
  funext X
  exact gapVector_eq_anchoredGapVector n X

/-- The logarithm of the normalized joint density is concave. -/
theorem concaveOn_log_anchoredProbabilityDensity (P : Parameters) (n : ℕ) :
    ConcaveOn ℝ (anchoredDomain n) (fun y => Real.log (anchoredProbabilityDensity P n y)) := by
  have hZ : 0 < (partitionFunction P n.succPNat).toReal :=
    ENNReal.toReal_pos (partitionFunction_pos P _).ne' (partitionFunction_lt_top P _).ne
  have heq : (fun y => Real.log (anchoredProbabilityDensity P n y)) =
      (fun y => P.val.1 * (-anchoredEnergy (parametersExponent P) n y) +
        Real.log ((partitionFunction P n.succPNat).toReal⁻¹)) := by
    funext y
    rw [anchoredProbabilityDensity, Real.log_mul (inv_pos.mpr hZ).ne' (Real.exp_pos _).ne',
      Real.log_exp]
    ring
  rw [heq]
  exact ((convexOn_anchoredEnergy (parametersExponent P) n).neg.smul P.2.1.le).add_const _

end Riesz1

end
end
