/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Gibbs.WellDefined
public import Riesz1.ToMathlib.Elementary.OrderedSimplex

/-!
# Anchored coordinates and the product law of the Gibbs measure

Rotation decomposition. Fix `n : ℕ`, so that `Configuration n.succPNat` has
`n + 1` particles. The map `X ↦ (X_0, (X_{j+1} - X_0)_j)` is a measurable bijection of the
configuration space onto `Set.Ico 0 1 ×ˢ anchoredDomain n`, where `anchoredDomain n` is the set of
strictly increasing gap vectors with entries in `(0, 1)`. It carries the configuration volume to
the product of Lebesgue measure on `[0, 1)` and Lebesgue measure on `anchoredDomain n`. The energy
depends only on the gap vector. Hence the Gibbs law is the product of the uniform law on `[0, 1)`
and the normalized density `exp(-β E_s)` on `anchoredDomain n`.

Every `N : ℕ+` equals `n.succPNat` for `n = N.natPred`, so the case `N = 1` is the case `n = 0`.
Vectors indexed by `Fin (n.succPNat : ℕ)` are the configurations themselves, so the statements
use that index type throughout.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal

namespace Riesz1

/-- The anchored gap domain: strictly increasing vectors `0 < y_1 < ⋯ < y_n < 1`. -/
def anchoredDomain (n : ℕ) : Set (Fin n → ℝ) :=
  {y | (∀ j, 0 < y j ∧ y j < 1) ∧ StrictMono y}

/-- The vector `(0, y_1, …, y_n)` on `n + 1` particles, with the anchor `0` in position `0`. -/
def anchorVector {n : ℕ} (y : Fin n → ℝ) : Fin (n.succPNat : ℕ) → ℝ :=
  Fin.cons 0 y

/-- The anchored coordinates `(x_0, (x_{j+1} - x_0)_j)` of a vector of `n + 1` entries. -/
def anchorCoords (n : ℕ) (x : Fin (n.succPNat : ℕ) → ℝ) : ℝ × (Fin n → ℝ) :=
  (x 0, fun j => x j.succ - x 0)

/-- The energy of the anchored configuration `(0, y_1, …, y_n)`, with `n + 1` particles. -/
def anchoredEnergy (s : RieszExponent) (n : ℕ) (y : Fin n → ℝ) : ℝ :=
  ((n.succPNat : ℕ) : ℝ) ^ (-s.val) *
    ∑ i : Fin (n.succPNat : ℕ), ∑ j ∈ Finset.univ.erase i,
      rieszRepresentative s ((anchorVector y i - anchorVector y j : ℝ) : UnitAddCircle)

/-- The density `exp(-β E_s)` on the anchored gap domain. -/
def anchoredDensity (P : Parameters) (n : ℕ) (y : Fin n → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-P.val.1 * anchoredEnergy (parametersExponent P) n y))

/-- The unnormalized anchored law: Lebesgue measure on `anchoredDomain n` with density
`anchoredDensity`. -/
def anchoredWeight (P : Parameters) (n : ℕ) : Measure (Fin n → ℝ) :=
  (volume.restrict (anchoredDomain n)).withDensity (anchoredDensity P n)

/-- The normalized anchored law: the probability measure on `anchoredDomain n` with density
proportional to `exp(-β E_s)`. -/
def anchoredLaw (P : Parameters) (n : ℕ) : Measure (Fin n → ℝ) :=
  (anchoredWeight P n univ)⁻¹ • anchoredWeight P n

/-! ### The anchor vector and the anchored coordinates -/

/-- The anchor of `anchorVector` is zero. -/
lemma anchorVector_zero {n : ℕ} (y : Fin n → ℝ) : anchorVector y 0 = 0 :=
  Fin.cons_zero _ _

/-- Position `j + 1` of `anchorVector y` is the gap `y_j`. -/
lemma anchorVector_succ {n : ℕ} (y : Fin n → ℝ) (j : Fin n) :
    anchorVector y j.succ = y j := by
  simp [anchorVector]

/-- Every coordinate of a vector is its anchor plus its anchored offset. -/
lemma apply_eq_anchor_add (n : ℕ) (x : Fin (n.succPNat : ℕ) → ℝ) (i : Fin (n.succPNat : ℕ)) :
    x i = x 0 + anchorVector (anchorCoords n x).2 i := by
  induction i using Fin.cases with
  | zero =>
    show x 0 = x 0 + anchorVector (anchorCoords n x).2 0
    rw [anchorVector_zero, add_zero]
  | succ j =>
    show x j.succ = x 0 + anchorVector (anchorCoords n x).2 j.succ
    rw [anchorVector_succ]
    simp [anchorCoords]

/-- The anchored vector depends measurably on the gap vector. -/
lemma measurable_anchorVector (n : ℕ) :
    Measurable (fun y : Fin n → ℝ => anchorVector y) := by
  refine Measurable.of_eval fun i => ?_
  induction i using Fin.cases with
  | zero =>
    show Measurable fun y : Fin n → ℝ => anchorVector y 0
    simp only [anchorVector_zero]
    exact measurable_const
  | succ j =>
    show Measurable fun y : Fin n → ℝ => anchorVector y j.succ
    simp only [anchorVector_succ]
    exact measurable_pi_apply j

/-- The anchored coordinates are measurable. -/
lemma measurable_anchorCoords (n : ℕ) : Measurable (anchorCoords n) := by
  unfold anchorCoords
  fun_prop

/-- The anchored coordinates of a configuration, as a function on the configuration space. -/
lemma measurable_anchorCoords_config (n : ℕ) :
    Measurable (fun X : Configuration n.succPNat => anchorCoords n X.val) :=
  (measurable_anchorCoords n).comp measurable_subtype_coe

/-! ### The configuration space as `[0, 1) × A_n` -/

/-- A vector lies in the ordered domain exactly when its anchored coordinates lie in
`Ico 0 1 ×ˢ anchoredDomain n`. -/
lemma mem_orderedDomain_iff (n : ℕ) (x : Fin (n.succPNat : ℕ) → ℝ) :
    x ∈ orderedDomain n.succPNat ↔ (0 ≤ x 0 ∧ x 0 < 1) ∧
      (∀ j : Fin n, 0 < x j.succ - x 0 ∧ x j.succ - x 0 < 1) ∧
        StrictMono (fun j : Fin n => x j.succ - x 0) := by
  constructor
  · rintro ⟨hmono, h0, h1, hall⟩
    have hall' : ∀ i, x i < x 0 + 1 := hall
    refine ⟨⟨h0, h1⟩, fun j => ⟨?_, ?_⟩, ?_⟩
    · have h : x 0 < x j.succ := hmono (Fin.succ_pos j)
      linarith
    · have h : x j.succ < x 0 + 1 := hall' j.succ
      linarith
    · intro a b hab
      have h : x a.succ < x b.succ := hmono (Fin.succ_lt_succ_iff.2 hab)
      show x a.succ - x 0 < x b.succ - x 0
      linarith
  · rintro ⟨⟨h0, h1⟩, hy, hymono⟩
    refine ⟨?_, h0, h1, ?_⟩
    · intro a b hab
      induction a using Fin.cases with
      | zero =>
        induction b using Fin.cases with
        | zero => exact absurd hab (lt_irrefl _)
        | succ j =>
          have h : 0 < x j.succ - x 0 := (hy j).1
          show x 0 < x j.succ
          linarith
      | succ i =>
        induction b using Fin.cases with
        | zero => exact absurd hab (Fin.not_lt_zero _)
        | succ j =>
          have h : x i.succ - x 0 < x j.succ - x 0 := hymono (Fin.succ_lt_succ_iff.1 hab)
          show x i.succ < x j.succ
          linarith
    · intro i
      induction i using Fin.cases with
      | zero =>
        show x 0 < x 0 + 1
        exact lt_add_one _
      | succ j =>
        have h : x j.succ - x 0 < 1 := (hy j).2
        show x j.succ < x 0 + 1
        linarith

/-- The ordered domain is the preimage of `Ico 0 1 ×ˢ anchoredDomain n` under the anchored
coordinates. -/
lemma orderedDomain_eq_preimage (n : ℕ) :
    orderedDomain n.succPNat = anchorCoords n ⁻¹' (Ico (0 : ℝ) 1 ×ˢ anchoredDomain n) := by
  ext x
  exact mem_orderedDomain_iff n x

/-- The inverse of the anchored coordinates: `(t, y) ↦ (t, t + y_1, …, t + y_n)`. -/
def anchorInverse (n : ℕ) (p : ℝ × (Fin n → ℝ)) : Fin (n.succPNat : ℕ) → ℝ :=
  fun i => p.1 + anchorVector p.2 i

/-- The anchored coordinates invert `anchorInverse`. -/
lemma anchorCoords_anchorInverse (n : ℕ) (p : ℝ × (Fin n → ℝ)) :
    anchorCoords n (anchorInverse n p) = p := by
  refine Prod.ext ?_ ?_
  · simp [anchorCoords, anchorInverse, anchorVector_zero]
  · funext j
    simp [anchorCoords, anchorInverse, anchorVector_zero, anchorVector_succ]

/-- Every point of `Ico 0 1 ×ˢ anchoredDomain n` is the anchored image of a configuration. -/
lemma anchorInverse_mem (n : ℕ) {p : ℝ × (Fin n → ℝ)}
    (hp : p ∈ Ico (0 : ℝ) 1 ×ˢ anchoredDomain n) :
    anchorInverse n p ∈ orderedDomain n.succPNat := by
  rw [orderedDomain_eq_preimage, mem_preimage, anchorCoords_anchorInverse]
  exact hp

/-- The anchored coordinates map the configuration space onto `Ico 0 1 ×ˢ anchoredDomain n`. -/
lemma range_anchorCoords (n : ℕ) :
    Set.range (fun X : Configuration n.succPNat => anchorCoords n X.val) =
      Ico (0 : ℝ) 1 ×ˢ anchoredDomain n := by
  ext p
  constructor
  · rintro ⟨X, rfl⟩
    have hX : X.val ∈ orderedDomain n.succPNat := X.2
    rw [orderedDomain_eq_preimage] at hX
    exact hX
  · intro hp
    exact ⟨⟨anchorInverse n p, anchorInverse_mem n hp⟩, anchorCoords_anchorInverse n p⟩

/-- The anchored coordinates are injective on the configuration space. -/
lemma injective_anchorCoords (n : ℕ) :
    Function.Injective (fun X : Configuration n.succPNat => anchorCoords n X.val) := by
  intro X Y hXY
  have hXY' : anchorCoords n X.val = anchorCoords n Y.val := hXY
  obtain ⟨h0, hy⟩ := Prod.mk.inj hXY'
  apply Subtype.ext
  funext i
  induction i using Fin.cases with
  | zero => exact h0
  | succ j =>
    have hj : X.val j.succ - X.val 0 = Y.val j.succ - Y.val 0 := congrFun hy j
    show X.val j.succ = Y.val j.succ
    linarith

/-! ### Measure preservation -/

/-- The shear `(t, z) ↦ (t, z + (-t) 𝟙)` preserves Lebesgue measure on `ℝ × (Fin n → ℝ)`. -/
lemma measurePreserving_shear (n : ℕ) :
    MeasurePreserving (fun p : ℝ × (Fin n → ℝ) => (p.1, p.2 + fun _ => -p.1))
      (volume.prod volume) (volume.prod volume) := by
  refine (MeasurePreserving.id (volume : Measure ℝ)).skew_product
    (g := fun (t : ℝ) (z : Fin n → ℝ) => z + fun _ => -t) ?_ ?_
  · fun_prop
  · exact ae_of_all _ fun t => map_add_right_eq_self volume _

/-- The anchored coordinates carry Lebesgue measure on `Fin (n + 1) → ℝ` to the product of
Lebesgue measures on `ℝ` and `Fin n → ℝ`. -/
lemma measurePreserving_anchorCoords (n : ℕ) :
    MeasurePreserving (anchorCoords n) volume (volume.prod volume) := by
  have h := (measurePreserving_shear n).comp
    (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0)
  have heq : anchorCoords n = (fun p : ℝ × (Fin n → ℝ) => (p.1, p.2 + fun _ => -p.1)) ∘
      MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0 := by
    funext x
    refine Prod.ext rfl (funext fun j => ?_)
    show x j.succ - x 0 = x j.succ + -x 0
    rw [sub_eq_add_neg]
  rw [heq]
  exact h

/-- The anchored gap domain is measurable. -/
lemma measurableSet_anchoredDomain (n : ℕ) : MeasurableSet (anchoredDomain n) :=
  measurableSet_ordered_simplex n

/-- The configuration volume is carried by the anchored coordinates to the product of Lebesgue
measure on `[0, 1)` and Lebesgue measure on `anchoredDomain n`. -/
lemma map_anchorCoords_configurationVolume (n : ℕ) :
    (configurationVolume n.succPNat).map (fun X => anchorCoords n X.val) =
      (volume.restrict (Ico (0 : ℝ) 1)).prod (volume.restrict (anchoredDomain n)) := by
  rw [Measure.prod_restrict]
  ext B hB
  rw [Measure.map_apply (measurable_anchorCoords_config n) hB, Measure.restrict_apply hB]
  unfold configurationVolume
  rw [(MeasurableEmbedding.subtype_coe (measurableSet_orderedDomain _)).comap_apply]
  have himage : Subtype.val '' ((fun X : Configuration n.succPNat => anchorCoords n X.val) ⁻¹' B)
      = anchorCoords n ⁻¹' (B ∩ (Ico (0 : ℝ) 1 ×ˢ anchoredDomain n)) := by
    ext x
    constructor
    · rintro ⟨X, hX, rfl⟩
      have hD : anchorCoords n X.val ∈ Ico (0 : ℝ) 1 ×ˢ anchoredDomain n := by
        have hXD : X.val ∈ orderedDomain n.succPNat := X.2
        rw [orderedDomain_eq_preimage] at hXD
        exact hXD
      exact ⟨hX, hD⟩
    · rintro ⟨hB', hx⟩
      have hxD : x ∈ orderedDomain n.succPNat := by
        rw [orderedDomain_eq_preimage]
        exact hx
      exact ⟨⟨x, hxD⟩, hB', rfl⟩
  rw [himage]
  exact (measurePreserving_anchorCoords n).measure_preimage
    (hB.inter (measurableSet_Ico.prod (measurableSet_anchoredDomain n))).nullMeasurableSet

/-! ### The energy depends only on the anchored coordinates -/

/-- The energy of a configuration is the anchored energy of its gap vector. -/
lemma energy_eq_anchoredEnergy (s : RieszExponent) (n : ℕ) (X : Configuration n.succPNat) :
    energy s X = anchoredEnergy s n (anchorCoords n X.val).2 := by
  have hdiff : ∀ i j : Fin (n.succPNat : ℕ), X.val i - X.val j =
      anchorVector (anchorCoords n X.val).2 i - anchorVector (anchorCoords n X.val).2 j := by
    intro i j
    have hi := apply_eq_anchor_add n X.val i
    have hj := apply_eq_anchor_add n X.val j
    linarith
  unfold energy anchoredEnergy
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hdiff i j]

/-- The unnormalized Gibbs law is the anchored density pulled back along the anchored
coordinates. -/
lemma gibbsWeight_eq (P : Parameters) (n : ℕ) :
    gibbsWeight P n.succPNat = (configurationVolume n.succPNat).withDensity
      (fun X => anchoredDensity P n (anchorCoords n X.val).2) := by
  unfold gibbsWeight anchoredDensity
  congr 1
  funext X
  rw [energy_eq_anchoredEnergy]

/-- The Riesz representative, as a function of a real lift, is measurable. It is continuous off
the collision points, and every collision point takes the value at `0`. -/
lemma measurable_rieszRepresentative_real (s : RieszExponent) :
    Measurable fun u : ℝ => rieszRepresentative s (u : UnitAddCircle) := by
  classical
  have hs : MeasurableSet {u : ℝ | (u : UnitAddCircle) ≠ 0} :=
    (isOpen_compl_singleton.preimage (AddCircle.continuous_mk' 1)).measurableSet
  have hcont : ContinuousOn (fun u : ℝ => rieszRepresentative s (u : UnitAddCircle))
      {u : ℝ | (u : UnitAddCircle) ≠ 0} := fun t ht =>
    (continuousAt_rieszRepresentative s ht).continuousWithinAt
  have heq : (fun u : ℝ => rieszRepresentative s (u : UnitAddCircle)) =
      {u : ℝ | (u : UnitAddCircle) ≠ 0}.piecewise
        (fun u : ℝ => rieszRepresentative s (u : UnitAddCircle))
        (fun _ : ℝ => rieszRepresentative s 0) := by
    funext u
    by_cases hu : (u : UnitAddCircle) = 0
    · simp [Set.piecewise, hu]
    · have hu' : u ∈ {u : ℝ | (u : UnitAddCircle) ≠ 0} := hu
      rw [Set.piecewise_eq_of_mem _ _ _ hu']
  rw [heq]
  exact ContinuousOn.measurable_piecewise hcont continuousOn_const hs

/-- The anchored energy is measurable. -/
lemma measurable_anchoredEnergy (s : RieszExponent) (n : ℕ) :
    Measurable (anchoredEnergy s n) := by
  unfold anchoredEnergy
  refine Measurable.const_mul ?_ _
  refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_
  have hdiff : Measurable fun y : Fin n → ℝ => anchorVector y i - anchorVector y j :=
    ((measurable_pi_apply i).comp (measurable_anchorVector n)).sub
      ((measurable_pi_apply j).comp (measurable_anchorVector n))
  exact (measurable_rieszRepresentative_real s).comp hdiff

/-- The anchored density is measurable. -/
lemma measurable_anchoredDensity (P : Parameters) (n : ℕ) :
    Measurable (anchoredDensity P n) :=
  ENNReal.measurable_ofReal.comp
    (Real.measurable_exp.comp ((measurable_anchoredEnergy _ _).const_mul _))

/-! ### Pushing forward the weight and the normalization -/

/-- Pushing forward a measure with density along a measurable map gives the density pushed
forward. -/
lemma map_withDensity_comp {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) {F : α → β} (hF : Measurable F) {g : β → ℝ≥0∞} (hg : Measurable g) :
    (μ.withDensity fun x => g (F x)).map F = (μ.map F).withDensity g := by
  ext B hB
  rw [Measure.map_apply hF hB, withDensity_apply _ (hF hB), withDensity_apply _ hB,
    setLIntegral_map hB hg hF]

/-- The anchored weight is a finite measure on the gap domain: it has finite total mass, as the
partition function does. -/
instance sFinite_anchoredWeight (P : Parameters) (n : ℕ) : SFinite (anchoredWeight P n) := by
  unfold anchoredWeight
  infer_instance

/-- The unnormalized Gibbs law, pushed forward by the anchored coordinates, is the product of the
uniform law on `[0, 1)` and the anchored weight. -/
lemma map_gibbsWeight (P : Parameters) (n : ℕ) :
    (gibbsWeight P n.succPNat).map (fun X => anchorCoords n X.val) =
      (volume.restrict (Ico (0 : ℝ) 1)).prod (anchoredWeight P n) := by
  have hD : Measurable (anchoredDensity P n) := measurable_anchoredDensity P n
  have hG : Measurable (fun p : ℝ × (Fin n → ℝ) => anchoredDensity P n p.2) :=
    hD.comp measurable_snd
  unfold anchoredWeight
  rw [prod_withDensity_right hD, ← map_anchorCoords_configurationVolume,
    ← map_withDensity_comp _ (measurable_anchorCoords_config n) hG, gibbsWeight_eq]

/-- The uniform law on `[0, 1)` has total mass one. -/
lemma measure_restrict_Ico_univ : (volume.restrict (Ico (0 : ℝ) 1)) univ = 1 := by
  rw [Measure.restrict_apply_univ, Real.volume_Ico]
  simp

/-- The partition function is the total mass of the anchored weight. -/
lemma partitionFunction_eq_anchoredWeight (P : Parameters) (n : ℕ) :
    partitionFunction P n.succPNat = anchoredWeight P n univ := by
  have hF : Measurable (fun X : Configuration n.succPNat => anchorCoords n X.val) :=
    measurable_anchorCoords_config n
  have hprod : ((volume.restrict (Ico (0 : ℝ) 1)).prod (anchoredWeight P n)) univ
      = (volume.restrict (Ico (0 : ℝ) 1)) univ * anchoredWeight P n univ := by
    calc ((volume.restrict (Ico (0 : ℝ) 1)).prod (anchoredWeight P n)) univ
        = ((volume.restrict (Ico (0 : ℝ) 1)).prod (anchoredWeight P n)) (univ ×ˢ univ) := by
          rw [univ_prod_univ]
      _ = _ := Measure.prod_prod _ _
  have h : gibbsWeight P n.succPNat univ =
      ((volume.restrict (Ico (0 : ℝ) 1)).prod (anchoredWeight P n)) univ := by
    rw [← map_gibbsWeight, Measure.map_apply hF MeasurableSet.univ, preimage_univ]
  unfold partitionFunction
  rw [h, hprod, measure_restrict_Ico_univ, one_mul]

/-- The normalized anchored law is a probability measure. -/
lemma isProbabilityMeasure_anchoredLaw (P : Parameters) (n : ℕ) :
    IsProbabilityMeasure (anchoredLaw P n) := by
  have hpos : 0 < anchoredWeight P n univ := by
    rw [← partitionFunction_eq_anchoredWeight]
    exact (modelWellDefined P n.succPNat).1
  have hfin : anchoredWeight P n univ < ⊤ := by
    rw [← partitionFunction_eq_anchoredWeight]
    exact (modelWellDefined P n.succPNat).2.1
  refine ⟨?_⟩
  unfold anchoredLaw
  rw [Measure.smul_apply, smul_eq_mul]
  exact ENNReal.inv_mul_cancel hpos.ne' hfin.ne

/-! ### The product law -/

/-- **Product law** (rotation decomposition). Under the Gibbs law, the anchored
coordinates `(X_0, (X_{j+1} - X_0)_j)` have the product law: the uniform law on `[0, 1)` for
the first coordinate, and the normalized density `exp(-β E_s)` on `anchoredDomain n` for the gap
vector. -/
theorem map_gibbsMeasure_anchorCoords (P : Parameters) (n : ℕ) :
    (gibbsMeasure P n.succPNat).map (fun X => anchorCoords n X.val) =
      (volume.restrict (Ico (0 : ℝ) 1)).prod (anchoredLaw P n) := by
  have hF : AEMeasurable (fun X : Configuration n.succPNat => anchorCoords n X.val)
      (gibbsWeight P n.succPNat) := (measurable_anchorCoords_config n).aemeasurable
  unfold gibbsMeasure
  rw [Measure.map_smul _ hF, map_gibbsWeight, partitionFunction_eq_anchoredWeight,
    ← Measure.prod_smul_right]
  rfl

/-- The first coordinate `X_0` is uniform on `[0, 1)` under the Gibbs law. -/
theorem map_fst_gibbsMeasure (P : Parameters) (n : ℕ) :
    (gibbsMeasure P n.succPNat).map (fun X : Configuration n.succPNat => X.val 0) =
      volume.restrict (Ico (0 : ℝ) 1) := by
  have := isProbabilityMeasure_anchoredLaw P n
  have h := congrArg (Measure.map Prod.fst) (map_gibbsMeasure_anchorCoords P n)
  rw [Measure.map_map measurable_fst (measurable_anchorCoords_config n),
    Measure.map_fst_prod, measure_univ, one_smul] at h
  exact h

/-- The anchored gap vector has the law `anchoredLaw` under the Gibbs law. -/
theorem map_snd_gibbsMeasure (P : Parameters) (n : ℕ) :
    (gibbsMeasure P n.succPNat).map (fun X : Configuration n.succPNat => (anchorCoords n X.val).2) =
      anchoredLaw P n := by
  have := isProbabilityMeasure_anchoredLaw P n
  have h := congrArg (Measure.map Prod.snd) (map_gibbsMeasure_anchorCoords P n)
  rw [Measure.map_map measurable_snd (measurable_anchorCoords_config n),
    Measure.map_snd_prod, measure_restrict_Ico_univ, one_smul] at h
  exact h

/-- **Independence.** Under the Gibbs law, the first coordinate `X_0` and
the anchored gap vector are independent. -/
theorem indepFun_gibbsMeasure (P : Parameters) (n : ℕ) :
    IndepFun (fun X : Configuration n.succPNat => X.val 0)
      (fun X : Configuration n.succPNat => (anchorCoords n X.val).2)
      (gibbsMeasure P n.succPNat) := by
  have : IsProbabilityMeasure (gibbsMeasure P n.succPNat) :=
    (modelWellDefined P n.succPNat).2.2
  have hf : Measurable (fun X : Configuration n.succPNat => X.val 0) :=
    (measurable_pi_apply 0).comp measurable_subtype_coe
  have hg : Measurable (fun X : Configuration n.succPNat => (anchorCoords n X.val).2) :=
    measurable_snd.comp (measurable_anchorCoords_config n)
  rw [indepFun_iff_map_prod_eq_prod_map_map hf.aemeasurable hg.aemeasurable,
    map_fst_gibbsMeasure, map_snd_gibbsMeasure]
  exact map_gibbsMeasure_anchorCoords P n

lemma anchorVector_mem_Ico {n : ℕ} {y : Fin n → ℝ} (hy : y ∈ anchoredDomain n)
    (i : Fin (n.succPNat : ℕ)) : anchorVector y i ∈ Ico (0 : ℝ) 1 := by
  induction i using Fin.cases with
  | zero => simp [anchorVector]
  | succ i => exact ⟨(hy.1 i).1.le, (hy.1 i).2⟩

lemma isOpen_anchoredDomain (n : ℕ) : IsOpen (anchoredDomain n) := by
  have he : anchoredDomain n =
      (⋂ i : Fin n, {y : Fin n → ℝ | 0 < y i ∧ y i < 1}) ∩
      ⋂ i : Fin n, ⋂ j : Fin n, {y : Fin n → ℝ | i < j → y i < y j} := by
    ext y
    simp only [anchoredDomain, mem_ofPred_eq, mem_inter_iff, mem_iInter]
    rfl
  rw [he]
  apply IsOpen.inter
  · apply isOpen_iInter_of_finite
    intro i
    exact (isOpen_lt continuous_const (continuous_apply i)).inter
      (isOpen_lt (continuous_apply i) continuous_const)
  · apply isOpen_iInter_of_finite
    intro i
    apply isOpen_iInter_of_finite
    intro j
    by_cases hij : i < j
    · simpa only [hij, true_implies] using isOpen_lt (continuous_apply i) (continuous_apply j)
    · simp only [hij, false_implies, ofPred_true, isOpen_univ]

end Riesz1

end
end
