/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Frozen.ModelWellDefined
public import Riesz1.ToMathlib.Elementary.OrderedSimplex
public import Riesz1.ToMathlib.HurwitzKernel.Regularity

/-!
# The Gibbs model is well defined

For every `N ≥ 1` and admissible parameters, the partition function lies in `(0, ∞)` and the
normalized Gibbs law is a probability measure.

Every pair of distinct coordinates of an ordered configuration differs by a non-integer, so the
energy is continuous on the configuration space. The kernel is bounded below, which bounds the
density `exp(-β H_N)` above uniformly, and the domain has finite volume. The density is
strictly positive everywhere, which gives positivity of the partition function.
-/

public section

open MeasureTheory Set

namespace Riesz1

/-- Two coordinates of an ordered configuration differ by less than one in absolute value. -/
lemma abs_sub_lt_one_of_mem_orderedDomain {N : ℕ+} {x : Fin (N : ℕ) → ℝ}
    (hx : x ∈ orderedDomain N) (i j : Fin (N : ℕ)) : |x i - x j| < 1 := by
  obtain ⟨hmono, -, -, hlt⟩ := hx
  have hi : x ⟨0, N.pos⟩ ≤ x i := hmono.monotone (Fin.le_def.2 (Nat.zero_le _))
  have hj : x ⟨0, N.pos⟩ ≤ x j := hmono.monotone (Fin.le_def.2 (Nat.zero_le _))
  rw [abs_sub_lt_iff]
  constructor <;> linarith [hlt i, hlt j]

/-- Distinct coordinates of an ordered configuration are not identified on the circle. -/
lemma coe_sub_ne_zero_of_mem_orderedDomain {N : ℕ+} {x : Fin (N : ℕ) → ℝ}
    (hx : x ∈ orderedDomain N) {i j : Fin (N : ℕ)} (hij : i ≠ j) :
    ((x i - x j : ℝ) : UnitAddCircle) ≠ 0 := by
  intro h
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).1 h
  rw [zsmul_eq_mul, mul_one] at hn
  have hpos : 0 < |(n : ℝ)| := by
    rw [hn]
    exact abs_pos.2 (sub_ne_zero.2 (hx.1.injective.ne hij))
  have hlt : |(n : ℝ)| < 1 := by
    rw [hn]
    exact abs_sub_lt_one_of_mem_orderedDomain hx i j
  have hlt' : |n| < 1 := by exact_mod_cast hlt
  obtain ⟨h1, h2⟩ := abs_lt.1 hlt'
  have hn0 : n = 0 := by omega
  subst hn0
  simp at hpos

/-- The kernel is continuous at every point whose image on the circle is nonzero. -/
lemma continuousAt_rieszRepresentative (s : RieszExponent) {t : ℝ}
    (ht : (t : UnitAddCircle) ≠ 0) :
    ContinuousAt (fun u : ℝ => rieszRepresentative s (u : UnitAddCircle)) t := by
  have hopen : IsOpen {u : ℝ | (u : UnitAddCircle) ≠ 0} :=
    isOpen_compl_singleton.preimage (AddCircle.continuous_mk' 1)
  have hc : ContinuousOn
      (fun u : ℝ => (HurwitzZeta.hurwitzZetaEven (u : UnitAddCircle) (s.val : ℂ)).re)
      {u : ℝ | (u : UnitAddCircle) ≠ 0} :=
    (contDiffOn_hurwitzZetaEven_re s.val s.property.1 s.property.2).continuousOn
  unfold rieszRepresentative
  exact (hc.continuousAt (hopen.mem_nhds ht)).const_mul 2

/-- The energy is continuous on the configuration space. -/
lemma continuous_energy (s : RieszExponent) (N : ℕ+) :
    Continuous fun X : Configuration N => energy s X := by
  have hpair : ∀ i j : Fin (N : ℕ), i ≠ j →
      Continuous fun X : Configuration N =>
        rieszRepresentative s ((X.val i - X.val j : ℝ) : UnitAddCircle) := by
    intro i j hij
    refine continuous_iff_continuousAt.2 fun X => ?_
    have hX : ContinuousAt (fun X : Configuration N => X.val i - X.val j) X :=
      (((continuous_apply i).comp continuous_subtype_val).sub
        ((continuous_apply j).comp continuous_subtype_val)).continuousAt
    have hg := continuousAt_rieszRepresentative s (coe_sub_ne_zero_of_mem_orderedDomain X.2 hij)
    exact ContinuousAt.comp (g := fun u : ℝ => rieszRepresentative s (u : UnitAddCircle))
      (f := fun X : Configuration N => X.val i - X.val j) hg hX
  unfold energy
  exact continuous_const.mul (continuous_finsetSum _ fun i _ =>
    continuous_finsetSum _ fun j hj => hpair i j (Finset.ne_of_mem_erase hj).symm)

/-- The energy is measurable on the configuration space. -/
lemma measurable_energy (s : RieszExponent) (N : ℕ+) :
    Measurable fun X : Configuration N => energy s X :=
  (continuous_energy s N).measurable

/-- The energy is bounded below on the configuration space, uniformly in the configuration. -/
lemma exists_energy_lower_bound (s : RieszExponent) (N : ℕ+) :
    ∃ L : ℝ, ∀ X : Configuration N, L ≤ energy s X := by
  obtain ⟨B, hB⟩ := hurwitzZetaEven_re_bounded_below s.val s.property.1 s.property.2
  refine ⟨(N : ℝ) ^ (-s.val) * ((N : ℝ) * (((N : ℝ) - 1) * B)), fun X => ?_⟩
  have hterm : ∀ i j : Fin (N : ℕ), i ≠ j →
      B ≤ rieszRepresentative s ((X.val i - X.val j : ℝ) : UnitAddCircle) := fun i j hij =>
    hB _ (coe_sub_ne_zero_of_mem_orderedDomain X.2 hij)
  have hN : 1 ≤ (N : ℕ) := N.pos
  have hcard : ∀ i : Fin (N : ℕ), (((Finset.univ.erase i).card : ℕ) : ℝ) = (N : ℝ) - 1 := by
    intro i
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin,
      Nat.cast_sub hN, Nat.cast_one]
  have hsum : (N : ℝ) * (((N : ℝ) - 1) * B) ≤
      ∑ i : Fin (N : ℕ), ∑ j ∈ Finset.univ.erase i,
        rieszRepresentative s ((X.val i - X.val j : ℝ) : UnitAddCircle) := by
    calc (N : ℝ) * (((N : ℝ) - 1) * B)
        = ∑ _i : Fin (N : ℕ), ((N : ℝ) - 1) * B := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ = ∑ i : Fin (N : ℕ), ∑ _j ∈ Finset.univ.erase i, B :=
          Finset.sum_congr rfl fun i _ => by rw [Finset.sum_const, nsmul_eq_mul, hcard i]
      _ ≤ _ := Finset.sum_le_sum fun i _ =>
          Finset.sum_le_sum fun j hj => hterm i j (Finset.ne_of_mem_erase hj).symm
  unfold energy
  exact mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-- The ordered domain is measurable. -/
lemma measurableSet_orderedDomain (N : ℕ+) : MeasurableSet (orderedDomain N) := by
  have hi : ∀ i : Fin (N : ℕ), MeasurableSet {x : Fin (N : ℕ) → ℝ | x i < x ⟨0, N.pos⟩ + 1} :=
    fun i => measurableSet_lt (measurable_pi_apply i) ((measurable_pi_apply _).add_const 1)
  have h0 : MeasurableSet {x : Fin (N : ℕ) → ℝ | 0 ≤ x ⟨0, N.pos⟩} :=
    measurableSet_le measurable_const (measurable_pi_apply _)
  have h1 : MeasurableSet {x : Fin (N : ℕ) → ℝ | x ⟨0, N.pos⟩ < 1} :=
    measurableSet_lt (measurable_pi_apply _) measurable_const
  have hset : orderedDomain N = {x | StrictMono x} ∩
      ({x | 0 ≤ x ⟨0, N.pos⟩} ∩ ({x | x ⟨0, N.pos⟩ < 1} ∩ ⋂ i, {x | x i < x ⟨0, N.pos⟩ + 1})) := by
    ext x
    simp [orderedDomain]
  rw [hset]
  exact (measurableSet_strictMono _).inter (h0.inter (h1.inter (MeasurableSet.iInter hi)))

/-- The ordered domain has volume `1 / (N - 1)!`. -/
lemma volume_orderedDomain (N : ℕ+) :
    volume (orderedDomain N) = ENNReal.ofReal (1 / (((N : ℕ) - 1).factorial : ℝ)) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, N = n.succPNat := ⟨N.natPred, (PNat.succPNat_natPred N).symm⟩
  have hset : orderedDomain n.succPNat =
      {x : Fin (n + 1) → ℝ | (0 ≤ x 0 ∧ x 0 < 1) ∧ StrictMono x ∧ x (Fin.last n) < x 0 + 1} := by
    ext x
    simp only [orderedDomain, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hmono, h0, h1, hall⟩
      exact ⟨⟨h0, h1⟩, hmono, hall (Fin.last n)⟩
    · rintro ⟨⟨h0, h1⟩, hmono, hlast⟩
      exact ⟨hmono, h0, h1, fun i => lt_of_le_of_lt (hmono.monotone (Fin.le_last i)) hlast⟩
  -- The two sides live in `Fin (n + 1) → ℝ` and `Fin ↑n.succPNat → ℝ`, which agree only up to
  -- definitional unfolding, so the equation is transported by `Eq.trans` rather than `rw`.
  exact (congrArg (fun s : Set (Fin (n.succPNat : ℕ) → ℝ) => volume s) hset).trans
    ((volume_circle_ordered_simplex n).trans (by simp))

/-- The configuration volume of the whole configuration space is `1 / (N - 1)!`. -/
lemma configurationVolume_univ (N : ℕ+) :
    configurationVolume N univ = ENNReal.ofReal (1 / (((N : ℕ) - 1).factorial : ℝ)) := by
  unfold configurationVolume
  rw [(MeasurableEmbedding.subtype_coe (measurableSet_orderedDomain N)).comap_apply,
    Set.image_univ, Subtype.range_coe]
  exact volume_orderedDomain N

/-- The partition function is the Gibbs density integrated against the configuration volume. -/
lemma partitionFunction_eq_lintegral (P : Parameters) (N : ℕ+) :
    partitionFunction P N = ∫⁻ X, ENNReal.ofReal
      (Real.exp (-P.val.1 * energy (parametersExponent P) X)) ∂(configurationVolume N) := by
  unfold partitionFunction gibbsWeight
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]

/-- The Gibbs density is continuous on the configuration space, hence measurable. -/
lemma continuous_gibbsDensity (P : Parameters) (N : ℕ+) :
    Continuous fun X : Configuration N =>
      ENNReal.ofReal (Real.exp (-P.val.1 * energy (parametersExponent P) X)) :=
  ENNReal.continuous_ofReal.comp
    (Real.continuous_exp.comp (continuous_const.mul (continuous_energy _ N)))

/-- The partition function is finite. -/
lemma partitionFunction_lt_top (P : Parameters) (N : ℕ+) : partitionFunction P N < ⊤ := by
  obtain ⟨L, hL⟩ := exists_energy_lower_bound (parametersExponent P) N
  have hβ : 0 < P.val.1 := P.property.1
  have hbound : ∀ X : Configuration N,
      ENNReal.ofReal (Real.exp (-P.val.1 * energy (parametersExponent P) X)) ≤
        ENNReal.ofReal (Real.exp (-P.val.1 * L)) := fun X =>
    ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (by
      have := mul_le_mul_of_nonneg_left (hL X) hβ.le
      linarith))
  rw [partitionFunction_eq_lintegral]
  refine (lintegral_mono hbound).trans_lt ?_
  rw [lintegral_const, configurationVolume_univ]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

/-- The partition function is strictly positive. -/
lemma partitionFunction_pos (P : Parameters) (N : ℕ+) : 0 < partitionFunction P N := by
  rw [partitionFunction_eq_lintegral,
    lintegral_pos_iff_support (continuous_gibbsDensity P N).measurable]
  have hsupp : Function.support (fun X : Configuration N =>
      ENNReal.ofReal (Real.exp (-P.val.1 * energy (parametersExponent P) X))) = univ :=
    Set.eq_univ_of_forall fun X => by simp [Function.mem_support, Real.exp_pos]
  rw [hsupp, configurationVolume_univ]
  exact ENNReal.ofReal_pos.2 (one_div_pos.2 (Nat.cast_pos.2 (Nat.factorial_pos _)))

/-- The Gibbs model is well defined: for every `N`, the partition function lies in `(0, ∞)` and
the Gibbs law is a probability measure. -/
theorem modelWellDefined (P : Parameters) : ModelWellDefined P := by
  unfold ModelWellDefined
  intro N
  refine ⟨partitionFunction_pos P N, partitionFunction_lt_top P N, ?_⟩
  rw [isProbabilityMeasure_iff]
  unfold gibbsMeasure
  rw [Measure.smul_apply, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (partitionFunction_pos P N).ne' (partitionFunction_lt_top P N).ne

end Riesz1
