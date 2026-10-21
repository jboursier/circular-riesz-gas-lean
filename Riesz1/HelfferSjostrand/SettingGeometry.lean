/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Gibbs.WellDefined
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Calculus.Rademacher
public import Mathlib.Analysis.Normed.Group.Quotient
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Euclidean lifted chamber for the Helffer–Sjöstrand setting

The chamber uses the Euclidean norm, rather than the sup norm on a function
space. Its half-open fundamental region is exactly the ordered domain.
The distance function below is defined on the entire Euclidean space as the
distance to the complement. Its restriction to the chamber is the boundary
distance.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Metric
open scoped Topology ENNReal

namespace Riesz1

/-- The Euclidean lift space with the paper's labelled coordinates. -/
abbrev HsEuclidean (N : ℕ+) := EuclideanSpace ℝ (Fin (N : ℕ))

/-- The open lifted chamber, including the singleton convention `𝒞₁ = ℝ`. -/
def hsChamber (N : ℕ+) : Set (HsEuclidean N) :=
  {x | StrictMono x ∧ ∀ i, x i < x ⟨0, N.pos⟩ + 1}

/-- The Euclidean half-open fundamental region `0 ≤ x₀ < 1`. -/
def hsFundamentalRegion (N : ℕ+) : Set (HsEuclidean N) :=
  {x ∈ hsChamber N | 0 ≤ x ⟨0, N.pos⟩ ∧ x ⟨0, N.pos⟩ < 1}

theorem hsFundamentalRegion_eq_preimage (N : ℕ+) :
    hsFundamentalRegion N = WithLp.ofLp ⁻¹' orderedDomain N := by
  ext x
  simp only [hsFundamentalRegion, hsChamber, orderedDomain, mem_ofPred_eq, mem_preimage]
  tauto

/-- Simultaneous real translation of all the coordinates. -/
def hsTranslate {N : ℕ+} (t : ℝ) (x : HsEuclidean N) : HsEuclidean N :=
  WithLp.toLp 2 (fun i => x i + t)

theorem hsTranslate_apply {N : ℕ+} (t : ℝ) (x : HsEuclidean N) (i : Fin (N : ℕ)) :
    hsTranslate t x i = x i + t := rfl

theorem hsTranslate_zero {N : ℕ+} (x : HsEuclidean N) : hsTranslate 0 x = x := by
  ext i
  simp only [hsTranslate_apply, add_zero]

theorem hsTranslate_add {N : ℕ+} (t u : ℝ) (x : HsEuclidean N) :
    hsTranslate t (hsTranslate u x) = hsTranslate (t + u) x := by
  ext i
  simp only [hsTranslate_apply]
  ring

theorem isometry_hsTranslate (N : ℕ+) (t : ℝ) :
    Isometry (hsTranslate (N := N) t) := by
  have heq : hsTranslate (N := N) t =
      fun x => x + WithLp.toLp 2 (fun _ : Fin (N : ℕ) => t) := rfl
  rw [heq]
  exact isometry_add_right _

theorem hsTranslate_mem_chamber_iff {N : ℕ+} (t : ℝ) (x : HsEuclidean N) :
    hsTranslate t x ∈ hsChamber N ↔ x ∈ hsChamber N := by
  constructor
  · rintro ⟨hm, hb⟩
    constructor
    · intro i j hij
      have := hm hij
      simpa only [hsTranslate_apply, add_lt_add_iff_right] using this
    · intro i
      have := hb i
      simp only [hsTranslate_apply] at this
      linarith
  · rintro ⟨hm, hb⟩
    constructor
    · intro i j hij
      change x i + t < x j + t
      linarith [hm hij]
    · intro i
      change x i + t < x ⟨0, N.pos⟩ + t + 1
      linarith [hb i]

theorem isOpen_hsChamber (N : ℕ+) : IsOpen (hsChamber N) := by
  have he (i : Fin (N : ℕ)) : Continuous (fun x : HsEuclidean N => x i) :=
    (PiLp.continuous_apply 2 _ i)
  have heq : hsChamber N =
      (⋂ i, ⋂ j, {x : HsEuclidean N | i < j → x i < x j}) ∩
        ⋂ i, {x : HsEuclidean N | x i < x ⟨0, N.pos⟩ + 1} := by
    ext x
    simp [hsChamber, StrictMono]
  rw [heq]
  refine (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_).inter
    (isOpen_iInter_of_finite fun i => isOpen_lt (he i) ((he _).add continuous_const))
  by_cases hij : i < j
  · simpa only [hij, true_implies] using isOpen_lt (he i) (he j)
  · simp only [hij, false_implies, ofPred_true]
    exact isOpen_univ

theorem measurableSet_hsFundamentalRegion (N : ℕ+) :
    MeasurableSet (hsFundamentalRegion N) := by
  rw [hsFundamentalRegion_eq_preimage]
  exact (measurableSet_orderedDomain N).preimage
    (PiLp.volume_preserving_ofLp (Fin (N : ℕ))).measurable

/-- Reducing the first coordinate modulo one gives the representative. -/
def hsRepresentative {N : ℕ+} (x : hsChamber N) : Configuration N :=
  ⟨fun i => x.val i - (⌊x.val ⟨0, N.pos⟩⌋ : ℤ), by
    refine ⟨fun i j hij => sub_lt_sub_right (x.property.1 hij) _, ?_, ?_, ?_⟩
    · exact sub_nonneg.mpr (Int.floor_le _)
    · have := Int.lt_floor_add_one (x.val ⟨0, N.pos⟩)
      linarith
    · intro i
      linarith [x.property.2 i]⟩

theorem hsRepresentative_apply {N : ℕ+} (x : hsChamber N) (i : Fin (N : ℕ)) :
    (hsRepresentative x).val i = x.val i - (⌊x.val ⟨0, N.pos⟩⌋ : ℤ) := rfl

/-- The constant vector that generates the simultaneous integer translations. -/
def hsRotationVector (N : ℕ+) : HsEuclidean N := WithLp.toLp 2 (fun _ => 1)

/-- The discrete period subgroup, with no quotient by relabelling. -/
def hsPeriodLattice (N : ℕ+) : AddSubgroup (HsEuclidean N) :=
  AddSubgroup.zmultiples (hsRotationVector N)

instance (N : ℕ+) : DiscreteTopology (hsPeriodLattice N) :=
  NormedSpace.discreteTopology_zmultiples _

instance (N : ℕ+) : IsClosed (hsPeriodLattice N : Set (HsEuclidean N)) :=
  AddSubgroup.isClosed_of_discreteTopology

/-- The ambient flat cylinder with its quotient Euclidean metric. -/
abbrev HsCylinder (N : ℕ+) := HsEuclidean N ⧸ hsPeriodLattice N

/-- The configuration manifold as an open subset of the Euclidean cylinder. -/
def HsConfiguration (N : ℕ+) :=
  (QuotientAddGroup.mk '' hsChamber N : Set (HsCylinder N))

theorem isOpen_hsConfiguration (N : ℕ+) :
    IsOpen (QuotientAddGroup.mk '' hsChamber N : Set (HsCylinder N)) :=
  QuotientAddGroup.isOpenMap_coe _ (isOpen_hsChamber N)

/-- Distance to the collision complement on the entire Euclidean lift space for `N ≥ 2`.
The particle-number certificate excludes the empty collision complement of the singleton. -/
def hsBoundaryDistance (N : ℕ+) (_hN : 2 ≤ (N : ℕ)) (x : HsEuclidean N) : ℝ :=
  infDist x (hsChamber N)ᶜ

theorem hsBoundaryDistance_nonneg (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (x : HsEuclidean N) :
    0 ≤ hsBoundaryDistance N hN x := infDist_nonneg

theorem hsBoundaryDistance_lipschitz (N : ℕ+) (hN : 2 ≤ (N : ℕ)) :
    LipschitzWith 1 (hsBoundaryDistance N hN) := lipschitz_infDist_pt _

/-- The lift distance is invariant under every common rotation. -/
theorem hsBoundaryDistance_translate (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (t : ℝ) (x : HsEuclidean N) :
    hsBoundaryDistance N hN (hsTranslate t x) = hsBoundaryDistance N hN x := by
  have heq : hsTranslate t '' (hsChamber N)ᶜ = (hsChamber N)ᶜ := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact fun h => hz ((hsTranslate_mem_chamber_iff t z).mp h)
    · intro hy
      refine ⟨hsTranslate (-t) y,
        fun h => hy ((hsTranslate_mem_chamber_iff (-t) y).mp h), ?_⟩
      rw [hsTranslate_add, add_neg_cancel, hsTranslate_zero]
  unfold hsBoundaryDistance
  conv_lhs => rw [← heq]
  exact infDist_image (isometry_hsTranslate N t)

theorem hsChamber_compl_nonempty {N : ℕ+} (hN : 2 ≤ (N : ℕ)) :
    (hsChamber N)ᶜ.Nonempty := by
  refine ⟨0, ?_⟩
  intro h
  have := h.1 (show (⟨0, N.pos⟩ : Fin (N : ℕ)) < ⟨1, by omega⟩ from by
    exact Fin.mk_lt_mk.mpr (by omega))
  simp at this

theorem hsBoundaryDistance_pos {N : ℕ+} (hN : 2 ≤ (N : ℕ))
    {x : HsEuclidean N} (hx : x ∈ hsChamber N) : 0 < hsBoundaryDistance N hN x :=
  ((isOpen_hsChamber N).isClosed_compl.notMem_iff_infDist_pos
    (hsChamber_compl_nonempty hN)).mp (not_not.mpr hx)

/-- A uniform bound on the chamber, obtained by closing the first gap. -/
theorem hsBoundaryDistance_le_one {N : ℕ+} (hN : 2 ≤ (N : ℕ))
    {x : HsEuclidean N} (hx : x ∈ hsChamber N) : hsBoundaryDistance N hN x ≤ 1 := by
  let i : Fin (N : ℕ) := ⟨1, by omega⟩
  let j : Fin (N : ℕ) := ⟨0, N.pos⟩
  have hji : j < i := by exact Fin.mk_lt_mk.mpr (by omega)
  have hne : j ≠ i := ne_of_lt hji
  let v : HsEuclidean N := PiLp.single 2 i (x j - x i)
  have hi : (x + v) i = x j := by simp [v]
  have hj : (x + v) j = x j := by simp [v, hne]
  have hy : x + v ∈ (hsChamber N)ᶜ := by
    intro hy
    have := hy.1 hji
    rw [hi, hj] at this
    exact lt_irrefl _ this
  calc hsBoundaryDistance N hN x ≤ dist x (x + v) := infDist_le_dist_of_mem hy
    _ = |x j - x i| := by
      rw [dist_eq_norm, sub_add_cancel_left, norm_neg, PiLp.norm_single, Real.norm_eq_abs]
    _ ≤ 1 := by
      rw [abs_of_nonpos (sub_nonpos.mpr (hx.1 hji).le)]
      have := hx.2 i
      change x i < x j + 1 at this
      linarith

/-- In the interior this is also the distance to the topological boundary. -/
theorem hsBoundaryDistance_eq_frontier {N : ℕ+} (hN : 2 ≤ (N : ℕ))
    {x : HsEuclidean N} (hx : x ∈ hsChamber N) :
    hsBoundaryDistance N hN x = infDist x (frontier (hsChamber N)) := by
  have hne : hsChamber N ≠ univ := nonempty_compl.mp (hsChamber_compl_nonempty hN)
  obtain ⟨y, hy, hxy⟩ := exists_mem_frontier_infDist_compl_eq_dist hx hne
  apply le_antisymm
  · exact infDist_le_infDist_of_subset
      (by rw [(isOpen_hsChamber N).frontier_eq]; exact inter_subset_right) ⟨y, hy⟩
  · exact (infDist_le_dist_of_mem hy).trans_eq hxy.symm

/-- The boundary distance has an actual derivative almost everywhere. -/
theorem hsBoundaryDistance_ae_differentiable (N : ℕ+) (hN : 2 ≤ (N : ℕ)) :
    ∀ᵐ x ∂(volume : Measure (HsEuclidean N)),
      DifferentiableAt ℝ (hsBoundaryDistance N hN) x :=
  (hsBoundaryDistance_lipschitz N hN).ae_differentiableAt

/-- The Euclidean gradient of the distance has norm at most one. -/
theorem hsBoundaryDistance_gradient_norm_le (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (x : HsEuclidean N) :
    ‖gradient (hsBoundaryDistance N hN) x‖ ≤ 1 := by
  simpa only [gradient, LinearIsometryEquiv.norm_map, NNReal.coe_one] using
    (norm_fderiv_le_of_lipschitz ℝ (x₀ := x) (hsBoundaryDistance_lipschitz N hN))

/-- The chamber is convex: it is cut out by strict linear inequalities. -/
theorem convex_hsChamber (N : ℕ+) : Convex ℝ (hsChamber N) := by
  intro x hx y hy a b ha hb hab
  have hcoord : ∀ i, (a • x + b • y) i = a * x i + b * y i := fun i => by simp
  refine ⟨?_, fun i => ?_⟩
  · intro i j hij
    change (a • x + b • y) i < (a • x + b • y) j
    rw [hcoord, hcoord]
    have hp : 0 < x j - x i := sub_pos.mpr (hx.1 hij)
    have hq : 0 < y j - y i := sub_pos.mpr (hy.1 hij)
    rcases le_total (x j - x i) (y j - y i) with hpq | hpq
    · nlinarith [mul_nonneg hb (sub_nonneg.mpr hpq)]
    · nlinarith [mul_nonneg ha (sub_nonneg.mpr hpq)]
  · rw [hcoord, hcoord]
    have hp : x i - x ⟨0, N.pos⟩ - 1 < 0 := by linarith [hx.2 i]
    have hq : y i - y ⟨0, N.pos⟩ - 1 < 0 := by linarith [hy.2 i]
    have key : a * (x i - x ⟨0, N.pos⟩ - 1) + b * (y i - y ⟨0, N.pos⟩ - 1) < 0 := by
      rcases le_total (x i - x ⟨0, N.pos⟩ - 1) (y i - y ⟨0, N.pos⟩ - 1) with hpq | hpq
      · nlinarith [mul_nonneg ha (sub_nonneg.mpr hpq)]
      · nlinarith [mul_nonneg hb (sub_nonneg.mpr hpq)]
    nlinarith [key, hab]

end Riesz1

end
