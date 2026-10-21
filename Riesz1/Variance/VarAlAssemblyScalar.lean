/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.VarAlAssemblySobolev
public import Riesz1.Variance.APrioriCutoffDifferentiability
public import Riesz1.ToMathlib.PositiveClampedInverse

/-!
# Scalar cutoff calculus in the anchored completion

The scalar good-event cutoff, absolute value, and positive-clamped inverse
act on the actual weighted Sobolev completion with their classical gradients.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ContDiff

namespace Riesz1.Internal

theorem varAlAssembly_lipschitz_scalarCutoff : LipschitzWith 1 scalarCutoff := by
  have hl : LipschitzWith 1 (fun r : ℝ => 2 - r) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [NNReal.coe_one, one_mul, dist_sub_left, le_refl]
  exact (hl.const_max 0).const_min 1

theorem varAlAssembly_contDiffAt_scalarCutoff {r : ℝ} (h1 : r ≠ 1) (h2 : r ≠ 2) :
    ContDiffAt ℝ ∞ scalarCutoff r := by
  rcases lt_or_gt_of_ne h1 with hr1 | hr1
  · apply (contDiffAt_const (c := (1 : ℝ))).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hr1] with t ht
    exact scalarCutoff_eq_one_of_le_one ht.le
  · rcases lt_or_gt_of_ne h2 with hr2 | hr2
    · apply ((contDiffAt_const (c := (2 : ℝ))).sub contDiffAt_id).congr_of_eventuallyEq
      filter_upwards [Ioo_mem_nhds hr1 hr2] with t ht
      unfold scalarCutoff
      rw [max_eq_right (by linarith [ht.2]), min_eq_right (by linarith [ht.1])]
      rfl
    · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [Ioi_mem_nhds hr2] with t ht
      exact scalarCutoff_eq_zero_of_two_le ht.le

variable {n : ℕ} {c : ℝ} (Q : HsPairPotentials n.succPNat c) (hc : 0 < c)

include hc

theorem varAlAssembly_scalarCutoff_classical {F : AnchoredEuclidean n → ℝ}
    (hF : IsAnchoredH1 Q F (gradient F))
    (hdF : ∀ᵐ x ∂anchoredMeasureE Q, DifferentiableAt ℝ F x)
    (h1 : ∀ᵐ x ∂anchoredMeasureE Q, F x ≠ 1)
    (h2 : ∀ᵐ x ∂anchoredMeasureE Q, F x ≠ 2) :
    IsAnchoredH1 Q (fun x => scalarCutoff (F x)) (gradient (fun x => scalarCutoff (F x))) := by
  apply varAlAssembly_comp_classical Q hc hF hdF varAlAssembly_lipschitz_scalarCutoff
    (B := {1, 2}) (by simp) ?_ ?_
  · intro r hr
    have hr' : r ≠ 1 ∧ r ≠ 2 := by simpa using hr
    exact (varAlAssembly_contDiffAt_scalarCutoff hr'.1 hr'.2).contDiffWithinAt.of_le (by simp)
  · filter_upwards [h1, h2] with x hx hy
    exact (varAlAssembly_contDiffAt_scalarCutoff hx hy).differentiableAt (by simp)

theorem varAlAssembly_abs_classical {F : AnchoredEuclidean n → ℝ}
    (hF : IsAnchoredH1 Q F (gradient F))
    (hdF : ∀ᵐ x ∂anchoredMeasureE Q, DifferentiableAt ℝ F x)
    (hne : ∀ᵐ x ∂anchoredMeasureE Q, F x ≠ 0) :
    IsAnchoredH1 Q (fun x => |F x|) (gradient (fun x => |F x|)) := by
  apply varAlAssembly_comp_classical Q hc hF hdF
    (lipschitzWith_one_norm : LipschitzWith 1 (fun r : ℝ => |r|))
    (B := {0}) (finite_singleton _) ?_ ?_
  · exact contDiffOn_abs (n := 1) (fun r hr => by simpa using hr)
  · filter_upwards [hne] with x hx
    exact (contDiffAt_abs (n := 1) hx).differentiableAt (by norm_num)

theorem varAlAssembly_scale_classical {F : AnchoredEuclidean n → ℝ}
    (hF : IsAnchoredH1 Q F (gradient F))
    (hdF : ∀ᵐ x ∂anchoredMeasureE Q, DifferentiableAt ℝ F x) (a : ℝ) :
    IsAnchoredH1 Q (fun x => a * F x) (gradient (fun x => a * F x)) := by
  have := isProbabilityMeasure_anchoredMeasureE Q hc
  have h := WeightedSobolev.IsWeightedH1.const_smul (isBounded_anchoredSimplex n)
    (ae_mem_anchoredSimplex Q) hF a
  apply h.congr EventuallyEq.rfl
  filter_upwards [hdF] with x hx
  have he := (hx.hasFDerivAt.const_mul a).fderiv
  change fderiv ℝ (fun x => a * F x) x = _ at he
  change _ = (InnerProductSpace.toDual ℝ (AnchoredEuclidean n)).symm _
  rw [he, map_smul]
  rfl

theorem varAlAssembly_inv_max_classical {F : AnchoredEuclidean n → ℝ}
    (hF : IsAnchoredH1 Q F (gradient F))
    (hdF : ∀ᵐ x ∂anchoredMeasureE Q, DifferentiableAt ℝ F x)
    {a : ℝ} (ha : 0 < a) (hne : ∀ᵐ x ∂anchoredMeasureE Q, F x ≠ a) :
    IsAnchoredH1 Q (fun x => (max a (F x))⁻¹) (gradient (fun x => (max a (F x))⁻¹)) := by
  apply varAlAssembly_comp_classical Q hc hF hdF (lipschitzWith_inv_max ha)
    (B := {a}) (finite_singleton _) ((contDiffOn_inv_max ha).of_le (by simp))
  filter_upwards [hne] with x hx
  exact ((contDiffOn_inv_max ha).contDiffAt
    ((isClosed_singleton.isOpen_compl).mem_nhds (by simpa using hx))).differentiableAt (by simp)

omit hc in
/-- An affine gap coordinate avoids every prescribed level almost everywhere
under any anchored pair law with at least two particles. -/
theorem varAlAssembly_gap_ne (hn : 1 ≤ n) (e : Fin (n.succPNat : ℕ)) (t : ℝ) :
    ∀ᵐ y ∂anchoredMeasureE Q, anchoredGapVector n (WithLp.ofLp y) e ≠ t := by
  have hac : hsAnchoredLaw Q ≪ (volume : Measure (Fin n → ℝ)) :=
    (Measure.smul_absolutelyContinuous.trans (withDensity_absolutelyContinuous _ _)).trans
      (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
  have hz : ∀ᵐ y ∂(volume : Measure (Fin n → ℝ)), anchoredGapVector n y e ≠ t := by
    rw [ae_iff]
    simpa only [not_not] using volume_anchored_gap_level_eq_zero n hn e t
  exact (PiLp.homeomorph 2 (fun _ : Fin n => ℝ)).symm.measurableEmbedding.ae_map_iff.mpr
    (hac.ae_le hz)

omit hc in
/-- Every pair factor in the cutoff avoids each of its exceptional affine
levels almost everywhere under the anchored law. -/
theorem varAlAssembly_pair_ne {I : Finset (Fin (n.succPNat : ℕ))}
    {p : Fin (n.succPNat : ℕ) × ℤ} (hp : p ∈ cutoffPairs n.succPNat I) (t : ℝ) :
    ∀ᵐ y ∂anchoredMeasureE Q,
      gapPairDev n.succPNat (anchoredGapVector n (WithLp.ofLp y)) p ≠ t := by
  have hac : hsAnchoredLaw Q ≪ (volume : Measure (Fin n → ℝ)) :=
    (Measure.smul_absolutelyContinuous.trans (withDensity_absolutelyContinuous _ _)).trans
      (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
  have hz : ∀ᵐ y ∂(volume : Measure (Fin n → ℝ)),
      gapPairDev n.succPNat (anchoredGapVector n y) p ≠ t := by
    rw [ae_iff]
    simpa only [not_not] using volume_anchored_pair_level_eq_zero n hp t
  exact (PiLp.homeomorph 2 (fun _ : Fin n => ℝ)).symm.measurableEmbedding.ae_map_iff.mpr
    (hac.ae_le hz)

end Riesz1.Internal

end
