/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Rigidity.GapLawMarginalTwo
public import Riesz1.ToMathlib.LogConcave.MarginalConcave
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Fibers of the anchored gap density

The first coordinate here is an unscaled offset in `(0,1)`. Its physical
gap is `(n+2)` times that coordinate. The density is extended by zero off
the ordered chamber, so its fibers are honest functions on all of Euclidean space.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Riesz1

lemma continuousOn_anchoredProbabilityDensity (P : Parameters) (n : ℕ) :
    ContinuousOn (anchoredProbabilityDensity P n) (anchoredDomain n) := by
  have hc := (concaveOn_log_anchoredProbabilityDensity P n).continuousOn (isOpen_anchoredDomain n)
  have he : EqOn (fun y => Real.exp (Real.log (anchoredProbabilityDensity P n y)))
      (anchoredProbabilityDensity P n) (anchoredDomain n) :=
    fun y _ => Real.exp_log (anchoredProbabilityDensity_pos P n y)
  exact (Real.continuous_exp.comp_continuousOn hc).congr he.symm

lemma exists_anchoredProbabilityDensity_bound (P : Parameters) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ y ∈ anchoredDomain n, anchoredProbabilityDensity P n y ≤ C := by
  obtain ⟨L, hL⟩ := exists_energy_lower_bound (parametersExponent P) n.succPNat
  let C := (partitionFunction P n.succPNat).toReal⁻¹ * Real.exp (-P.val.1 * L)
  have hZ : 0 < (partitionFunction P n.succPNat).toReal⁻¹ := by
    apply inv_pos.mpr
    exact ENNReal.toReal_pos (partitionFunction_pos P _).ne' (partitionFunction_lt_top P _).ne
  refine ⟨C, mul_pos hZ (Real.exp_pos _), ?_⟩
  intro y hy
  let X : Configuration n.succPNat :=
    ⟨anchorInverse n (0, y), anchorInverse_mem n ⟨by norm_num, hy⟩⟩
  have hcoords : (anchorCoords n X.val).2 = y :=
    congrArg Prod.snd (anchorCoords_anchorInverse n (0, y))
  have hE : energy (parametersExponent P) X = anchoredEnergy (parametersExponent P) n y := by
    rw [energy_eq_anchoredEnergy, hcoords]
  have hlow : L ≤ anchoredEnergy (parametersExponent P) n y := hE ▸ hL X
  apply mul_le_mul_of_nonneg_left _ hZ.le
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hlow (neg_nonpos.mpr P.2.1.le))

/-- The zero extension of the normalized cumulative-coordinate density. -/
def extendedAnchoredProbabilityDensity (P : Parameters) (n : ℕ) : (Fin n → ℝ) → ℝ :=
  (anchoredDomain n).indicator (anchoredProbabilityDensity P n)

lemma measurable_extendedAnchoredProbabilityDensity (P : Parameters) (n : ℕ) :
    Measurable (extendedAnchoredProbabilityDensity P n) :=
  (measurable_anchoredProbabilityDensity P n).indicator (measurableSet_anchoredDomain n)

lemma extendedAnchoredProbabilityDensity_nonneg (P : Parameters) (n : ℕ) (y : Fin n → ℝ) :
    0 ≤ extendedAnchoredProbabilityDensity P n y := by
  exact Set.indicator_nonneg (fun y _ => (anchoredProbabilityDensity_pos P n y).le) _

lemma support_extendedAnchoredProbabilityDensity (P : Parameters) (n : ℕ) :
    Function.support (extendedAnchoredProbabilityDensity P n) = anchoredDomain n := by
  ext y
  simp only [extendedAnchoredProbabilityDensity, Function.mem_support]
  by_cases hy : y ∈ anchoredDomain n
  · rw [Set.indicator_of_mem hy]
    exact iff_of_true (anchoredProbabilityDensity_pos P n y).ne' hy
  · rw [Set.indicator_of_notMem hy]
    simp only [hy, ne_eq, not_true_eq_false]

/-- The joint density in the first-offset/tail splitting. -/
def gapOffsetJointDensity (P : Parameters) (n : ℕ) (p : ℝ × (Fin n → ℝ)) : ℝ :=
  extendedAnchoredProbabilityDensity P (n + 1) (Fin.cons p.1 p.2)

lemma continuous_cons_real (n : ℕ) :
    Continuous (fun p : ℝ × (Fin n → ℝ) => (Fin.cons p.1 p.2 : Fin (n + 1) → ℝ)) := by
  apply continuous_pi
  intro i
  induction i using Fin.cases with
  | zero => simpa only [Fin.cons_zero] using continuous_fst
  | succ i =>
    change Continuous (fun p : ℝ × (Fin n → ℝ) => p.2 i)
    fun_prop

lemma measurable_gapOffsetJointDensity (P : Parameters) (n : ℕ) :
    Measurable (gapOffsetJointDensity P n) :=
  (measurable_extendedAnchoredProbabilityDensity P (n + 1)).comp
    (continuous_cons_real n).measurable

lemma gapOffsetJointDensity_nonneg (P : Parameters) (n : ℕ) (p : ℝ × (Fin n → ℝ)) :
    0 ≤ gapOffsetJointDensity P n p := extendedAnchoredProbabilityDensity_nonneg P _ _

lemma exists_gapOffsetJointDensity_bound (P : Parameters) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ p, gapOffsetJointDensity P n p ≤ C := by
  obtain ⟨C, hC, hbound⟩ := exists_anchoredProbabilityDensity_bound P (n + 1)
  refine ⟨C, hC, fun p => ?_⟩
  unfold gapOffsetJointDensity extendedAnchoredProbabilityDensity
  by_cases hp : Fin.cons p.1 p.2 ∈ anchoredDomain (n + 1)
  · rw [Set.indicator_of_mem hp]
    exact hbound _ hp
  · rw [Set.indicator_of_notMem hp]
    exact hC.le

lemma support_gapOffsetJointDensity (P : Parameters) (n : ℕ) :
    Function.support (gapOffsetJointDensity P n) =
      (fun p : ℝ × (Fin n → ℝ) => Fin.cons p.1 p.2) ⁻¹' anchoredDomain (n + 1) := by
  exact congrArg (Set.preimage _) (support_extendedAnchoredProbabilityDensity P (n + 1))

lemma isOpen_support_gapOffsetJointDensity (P : Parameters) (n : ℕ) :
    IsOpen (Function.support (gapOffsetJointDensity P n)) := by
  rw [support_gapOffsetJointDensity]
  exact (isOpen_anchoredDomain _).preimage (continuous_cons_real n)

/-- Every offset fiber is integrable, including the fibers outside `(0,1)` which vanish. -/
theorem integrable_gapOffsetJointDensity_fiber (P : Parameters) (n : ℕ) (r : ℝ) :
    Integrable (fun z => gapOffsetJointDensity P n (r, z)) volume := by
  obtain ⟨C, hC, hbound⟩ := exists_gapOffsetJointDensity_bound P n
  let K : Set (Fin n → ℝ) := Set.univ.pi fun _ => Icc (0 : ℝ) 1
  have hK : IsCompact K := isCompact_univ_pi fun _ => isCompact_Icc
  have hs : Function.support (fun z => gapOffsetJointDensity P n (r, z)) ⊆ K := by
    intro z hz
    have hmem : Fin.cons r z ∈ anchoredDomain (n + 1) := by
      have h := congrArg (fun s => (r, z) ∈ s) (support_gapOffsetJointDensity P n)
      exact h.mp hz
    intro i _
    exact ⟨(hmem.1 i.succ).1.le, (hmem.1 i.succ).2.le⟩
  have hm : Measurable (fun z => gapOffsetJointDensity P n (r, z)) :=
    (measurable_gapOffsetJointDensity P n).comp (measurable_const.prodMk measurable_id)
  apply (integrableOn_iff_integrable_of_support_subset hs).mp
  apply IntegrableOn.of_bound hK.measure_lt_top hm.aestronglyMeasurable.restrict C
  exact Filter.Eventually.of_forall fun _z => by
    rw [Real.norm_eq_abs, abs_of_nonneg (gapOffsetJointDensity_nonneg P n _)]
    exact hbound _

/-- The real fiber integral. The preceding theorem certifies every fiber's integrability. -/
def gapOffsetMarginalDensity (P : Parameters) (n : ℕ) (r : ℝ) : ℝ :=
  ∫ z, gapOffsetJointDensity P n (r, z)

theorem gapOffsetMarginalDensity_nonneg (P : Parameters) (n : ℕ) (r : ℝ) :
    0 ≤ gapOffsetMarginalDensity P n r := integral_nonneg fun _z => gapOffsetJointDensity_nonneg P n _

lemma mem_anchoredDomain_cons_iff (n : ℕ) (r : ℝ) (z : Fin n → ℝ) :
    Fin.cons r z ∈ anchoredDomain (n + 1) ↔
      r ∈ Ioo (0 : ℝ) 1 ∧ z ∈ anchoredDomain n ∧ ∀ i, r < z i := by
  constructor
  · intro h
    refine ⟨h.1 0, ⟨fun i => h.1 i.succ, ?_⟩, ?_⟩
    · exact (Fin.strictMono_cons.mp h.2).2
    · exact (Fin.strictMono_cons.mp h.2).1
  · rintro ⟨hr, hz, hlt⟩
    refine ⟨?_, Fin.strictMono_cons.mpr ⟨hlt, hz.2⟩⟩
    intro i
    induction i using Fin.cases with
    | zero => exact hr
    | succ i => exact hz.1 i

lemma gapOffsetJointDensity_fiber_support_subset (P : Parameters) (n : ℕ) (r : ℝ) :
    Function.support (fun z => gapOffsetJointDensity P n (r, z)) ⊆
      Set.univ.pi (fun _ : Fin n => Icc (0 : ℝ) 1) := by
  intro z hz
  have hm : Fin.cons r z ∈ anchoredDomain (n + 1) := by
    exact (Set.ext_iff.mp (support_gapOffsetJointDensity P n) (r, z)).mp hz
  intro i _
  exact ⟨(hm.1 i.succ).1.le, (hm.1 i.succ).2.le⟩

lemma exists_gapOffsetJointDensity_fiber_mem (n : ℕ) {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    ∃ z : Fin n → ℝ, Fin.cons r z ∈ anchoredDomain (n + 1) := by
  let z : Fin n → ℝ := fun i => r + (1 - r) * ((i.val + 1 : ℝ) / (n + 1 : ℝ))
  have hN : (0 : ℝ) < n + 1 := by positivity
  have hrN : 0 < 1 - r := sub_pos.mpr hr.2
  have hlt (i : Fin n) : r < z i := by
    apply lt_add_of_pos_right
    exact mul_pos hrN (div_pos (by positivity) hN)
  refine ⟨z, (mem_anchoredDomain_cons_iff n r z).mpr ⟨hr, ⟨fun i => ⟨?_, ?_⟩, ?_⟩, hlt⟩⟩
  · exact hr.1.trans (hlt i)
  · have hi : (i.val + 1 : ℝ) < n + 1 := by
      have h : (i.val : ℝ) < n := by exact_mod_cast i.isLt
      linarith
    have hratio : (i.val + 1 : ℝ) / (n + 1 : ℝ) < 1 := (div_lt_one hN).mpr hi
    dsimp only [z]
    nlinarith
  · intro i j hij
    dsimp only [z]
    have h : (i.val : ℝ) < j.val := by exact_mod_cast hij
    have hratio : (i.val + 1 : ℝ) / (n + 1 : ℝ) < (j.val + 1 : ℝ) / (n + 1 : ℝ) :=
      (div_lt_div_iff_of_pos_right hN).mpr (by linarith)
    nlinarith

theorem gapOffsetMarginalDensity_pos (P : Parameters) (n : ℕ) {r : ℝ}
    (hr : r ∈ Ioo (0 : ℝ) 1) : 0 < gapOffsetMarginalDensity P n r := by
  change 0 < ∫ z, gapOffsetJointDensity P n (r, z) ∂volume
  apply (integral_pos_iff_support_of_nonneg (μ := volume)
    (fun z => gapOffsetJointDensity_nonneg P n (r, z))
    (integrable_gapOffsetJointDensity_fiber P n r)).mpr
  have hopen : IsOpen (Function.support (fun z => gapOffsetJointDensity P n (r, z))) :=
    (isOpen_support_gapOffsetJointDensity P n).preimage (continuous_const.prodMk continuous_id)
  obtain ⟨z, hz⟩ := exists_gapOffsetJointDensity_fiber_mem n hr
  exact hopen.measure_pos (μ := volume)
    ⟨z, (Set.ext_iff.mp (support_gapOffsetJointDensity P n) (r, z)).mpr hz⟩

lemma continuousAt_gapOffsetJointDensity_fiber (P : Parameters) (n : ℕ) {r : ℝ}
    (hr : r ∈ Ioo (0 : ℝ) 1) (z : Fin n → ℝ) (hne : ∀ i, z i ≠ r) :
    ContinuousAt (fun t => gapOffsetJointDensity P n (t, z)) r := by
  have hpath : Continuous (fun t : ℝ => (Fin.cons t z : Fin (n + 1) → ℝ)) :=
    (continuous_cons_real n).comp (continuous_id.prodMk continuous_const)
  by_cases hz : z ∈ anchoredDomain n
  · by_cases hd : Fin.cons r z ∈ anchoredDomain (n + 1)
    · have hnhds : ∀ᶠ t in nhds r, Fin.cons t z ∈ anchoredDomain (n + 1) :=
        hpath.continuousAt.preimage_mem_nhds ((isOpen_anchoredDomain _).mem_nhds hd)
      have houter : ContinuousAt (anchoredProbabilityDensity P (n + 1)) (Fin.cons r z) :=
        (continuousOn_anchoredProbabilityDensity P (n + 1)).continuousAt
          ((isOpen_anchoredDomain _).mem_nhds hd)
      have hc : ContinuousAt (fun t => anchoredProbabilityDensity P (n + 1) (Fin.cons t z)) r :=
        houter.comp (f := fun t : ℝ => (Fin.cons t z : Fin (n + 1) → ℝ)) hpath.continuousAt
      apply hc.congr_of_eventuallyEq
      filter_upwards [hnhds] with t ht
      exact Set.indicator_of_mem ht _
    · have hbad : ∃ i, z i < r := by
        have hnot : ¬ ∀ i, r < z i := by
          intro h
          exact hd ((mem_anchoredDomain_cons_iff n r z).mpr ⟨hr, hz, h⟩)
        push Not at hnot
        obtain ⟨i, hi⟩ := hnot
        exact ⟨i, lt_of_le_of_ne hi (hne i)⟩
      obtain ⟨i, hi⟩ := hbad
      apply continuousAt_const.congr_of_eventuallyEq
      filter_upwards [isOpen_Ioi.mem_nhds hi] with t ht
      apply Set.indicator_of_notMem
      intro htmem
      exact (lt_asymm ht (((mem_anchoredDomain_cons_iff n t z).mp htmem).2.2 i)).elim
  · have heq : (fun t => gapOffsetJointDensity P n (t, z)) = fun _ => 0 := by
      ext t
      apply Set.indicator_of_notMem
      intro ht
      exact hz ((mem_anchoredDomain_cons_iff n t z).mp ht).2.1
    rw [heq]
    exact continuousAt_const

/-- Continuity is obtained from dominated convergence, with coordinate hyperplanes
removed from the fiber variable's null exceptional set. -/
theorem continuousOn_gapOffsetMarginalDensity (P : Parameters) (n : ℕ) :
    ContinuousOn (gapOffsetMarginalDensity P n) (Ioo (0 : ℝ) 1) := by
  obtain ⟨C, hC, hbound⟩ := exists_gapOffsetJointDensity_bound P n
  let K : Set (Fin n → ℝ) := Set.univ.pi fun _ => Icc (0 : ℝ) 1
  have hK : IsCompact K := isCompact_univ_pi fun _ => isCompact_Icc
  let B : (Fin n → ℝ) → ℝ := K.indicator fun _ => C
  have hB : Integrable B volume := by
    apply (integrable_indicator_iff hK.measurableSet).mpr
    exact integrableOn_const hK.measure_lt_top.ne
  have hdom (r : ℝ) (z : Fin n → ℝ) : ‖gapOffsetJointDensity P n (r, z)‖ ≤ B z := by
    rw [Real.norm_eq_abs, abs_of_nonneg (gapOffsetJointDensity_nonneg P n _)]
    by_cases hz : z ∈ K
    · rw [show B z = C from Set.indicator_of_mem hz _]
      exact hbound _
    · have hf : gapOffsetJointDensity P n (r, z) = 0 := by
        by_contra hn
        exact hz (gapOffsetJointDensity_fiber_support_subset P n r hn)
      rw [hf, show B z = 0 from Set.indicator_of_notMem hz _]
  intro r hr
  apply ContinuousAt.continuousWithinAt
  apply continuousAt_of_dominated
    (Filter.Eventually.of_forall fun t => (integrable_gapOffsetJointDensity_fiber P n t).1)
    (Filter.Eventually.of_forall fun t => Filter.Eventually.of_forall (hdom t)) hB
  have hne : ∀ᵐ z : Fin n → ℝ ∂volume, ∀ i, z i ≠ r := by
    apply ae_all_iff.mpr
    intro i
    exact Measure.ae_eval_ne (fun _ : Fin n => (volume : Measure ℝ)) i r
  filter_upwards [hne] with z hz
  exact continuousAt_gapOffsetJointDensity_fiber P n hr z hz

end Riesz1

end
end
