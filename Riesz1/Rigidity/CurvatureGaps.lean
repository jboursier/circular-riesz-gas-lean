/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Rigidity.Curvature
public import Riesz1.ToMathlib.ConvexHessian

/-!
# Internal gap coordinates and curvature

The linear section `x₀ = 0`, `xᵣ = N⁻¹ ∑_{p<r} vₚ`, and its Hessian bound.
These are curvature statements about the internal energy. Identification of the marginal law
requires the exterior density and the change of variables as well.
-/

@[expose] public section

noncomputable section

open Set Filter Finset
open scoped Topology ContDiff

namespace Riesz1

/-- The internal gaps, in Euclidean coordinates. -/
def internalBlockGaps (N : ℕ+) (L : ℕ) (z : HsEuclidean L.succPNat) :
    EuclideanSpace ℝ (Fin L) :=
  WithLp.toLp 2 (fun i => (N : ℝ) * (z i.succ - z i.castSucc))

/-- The section of the internal gap map with first coordinate zero. -/
def internalGapSection (N : ℕ+) (L : ℕ) :
    EuclideanSpace ℝ (Fin L) →L[ℝ] HsEuclidean L.succPNat :=
  LinearMap.toContinuousLinearMap {
    toFun := fun v => WithLp.toLp 2 (fun r =>
      (∑ p ∈ univ.filter (fun p : Fin L => p.val < r.val), v p) / (N : ℝ))
    map_add' := by
      intro v w
      ext r
      simp only [PiLp.add_apply, Finset.sum_add_distrib, add_div]
    map_smul' := by
      intro c v
      ext r
      simp only [PiLp.smul_apply, smul_eq_mul, ← Finset.mul_sum,
        mul_div_assoc, RingHom.id_apply] }

theorem internalGapSection_apply (N : ℕ+) (L : ℕ) (v : EuclideanSpace ℝ (Fin L))
    (r : Fin (L.succPNat : ℕ)) :
    internalGapSection N L v r =
      (∑ p ∈ univ.filter (fun p : Fin L => p.val < r.val), v p) / (N : ℝ) := rfl

theorem internalGapSection_zero (N : ℕ+) (L : ℕ) (v : EuclideanSpace ℝ (Fin L)) :
    internalGapSection N L v 0 = 0 := by
  change (∑ p ∈ univ.filter (fun p : Fin L =>
    p.val < (0 : Fin (L.succPNat : ℕ)).val), v p) / (N : ℝ) = 0
  simp

theorem internalGapSection_succ (N : ℕ+) (L : ℕ) (v : EuclideanSpace ℝ (Fin L))
    (i : Fin L) :
    internalGapSection N L v i.succ - internalGapSection N L v i.castSucc = v i / N := by
  have hset : (Finset.univ.filter (fun p : Fin L => p.val < i.succ.val)) =
      (insert i (Finset.univ.filter (fun p : Fin L => p.val < i.castSucc.val)) : Finset (Fin L)) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Fin.val_succ, Fin.val_castSucc]
    constructor
    · intro h
      by_cases hp : p = i
      · exact Or.inl hp
      · exact Or.inr (by have : p.val ≠ i.val := fun h => hp (Fin.ext h); omega)
    · rintro (rfl | h) <;> omega
  have hnot : i ∉ univ.filter (fun p : Fin L => p.val < i.castSucc.val) := by simp
  change (∑ p ∈ univ.filter (fun p : Fin L => p.val < i.succ.val), v p) / (N : ℝ) -
    (∑ p ∈ univ.filter (fun p : Fin L => p.val < i.castSucc.val), v p) / (N : ℝ) = _
  rw [hset, Finset.sum_insert hnot]
  ring

theorem internalBlockGaps_section (N : ℕ+) (L : ℕ) (v : EuclideanSpace ℝ (Fin L)) :
    internalBlockGaps N L (internalGapSection N L v) = v := by
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast N.ne_zero
  ext i
  change (N : ℝ) * (internalGapSection N L v i.succ - internalGapSection N L v i.castSucc) = v i
  rw [internalGapSection_succ]
  field_simp

/-- Reconstruct a lift from its internal gaps, modulo its free rotation. -/
theorem internalGapSection_reconstruct (N : ℕ+) (L : ℕ) (z : HsEuclidean L.succPNat)
    (r : Fin (L.succPNat : ℕ)) :
    internalGapSection N L (internalBlockGaps N L z) r = z r - z 0 := by
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast N.ne_zero
  induction r using Fin.induction with
  | zero =>
    change internalGapSection N L (internalBlockGaps N L z) (0 : Fin (L.succPNat : ℕ)) =
      z (0 : Fin (L.succPNat : ℕ)) - z (0 : Fin (L.succPNat : ℕ))
    rw [sub_self, internalGapSection_zero]
  | succ i ih =>
    have hh := internalGapSection_succ N L (internalBlockGaps N L z) i
    have hg : internalBlockGaps N L z i = (N : ℝ) * (z i.succ - z i.castSucc) := rfl
    rw [hg, mul_div_cancel_left₀ _ hN, ih] at hh
    linarith

/-- On the lifted block, the internal gap map consists of the
already defined microscopic gaps. It has no separate cyclic convention. -/
theorem internalBlockGaps_liftedBlock {N : ℕ+} (i0 : ℤ) {L : ℕ}
    (hL : L < (N : ℕ)) (X : Configuration N) (i : Fin L) :
    internalBlockGaps N L (WithLp.toLp 2 (liftedBlock i0 hL X).val) i = gap X (i0 + i.val) := by
  unfold internalBlockGaps gap liftedBlock liftedBlockCoords
  change (N : ℝ) * ((cyclicLift X (i0 + (i.succ.val : ℤ)) - (⌊cyclicLift X i0⌋ : ℝ)) -
      (cyclicLift X (i0 + (i.castSucc.val : ℤ)) - (⌊cyclicLift X i0⌋ : ℝ))) =
    (N : ℝ) * (cyclicLift X (i0 + i.val + 1) - cyclicLift X (i0 + i.val))
  simp only [Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one, ← add_assoc]
  ring

/-- The internal gap chamber, using the section with first coordinate zero. -/
def internalGapDomain (N : ℕ+) (L : ℕ) : Set (EuclideanSpace ℝ (Fin L)) :=
  internalGapSection N L ⁻¹' hsChamber L.succPNat

theorem isOpen_internalGapDomain (N : ℕ+) (L : ℕ) : IsOpen (internalGapDomain N L) :=
  (isOpen_hsChamber L.succPNat).preimage (internalGapSection N L).continuous

theorem convex_internalGapDomain (N : ℕ+) (L : ℕ) : Convex ℝ (internalGapDomain N L) :=
  (convex_hsChamber L.succPNat).linear_preimage (internalGapSection N L).toLinearMap

theorem internalBlockGaps_mem_internalGapDomain (N : ℕ+) (L : ℕ)
    {z : HsEuclidean L.succPNat} (hz : z ∈ hsChamber L.succPNat) :
    internalBlockGaps N L z ∈ internalGapDomain N L := by
  change StrictMono (internalGapSection N L (internalBlockGaps N L z)) ∧ _
  constructor
  · intro i j hij
    rw [internalGapSection_reconstruct, internalGapSection_reconstruct]
    exact sub_lt_sub_right (hz.1 hij) _
  · intro i
    rw [internalGapSection_reconstruct, internalGapSection_reconstruct]
    have h := hz.2 i
    linarith

/-- The carrier is precisely the open simplex, including
the empty-vector convention at `L = 0`. -/
theorem mem_internalGapDomain (N : ℕ+) (L : ℕ) (v : EuclideanSpace ℝ (Fin L)) :
    v ∈ internalGapDomain N L ↔ (∀ i, 0 < v i) ∧ ∑ i, v i < (N : ℝ) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hlast : internalGapSection N L v (Fin.last L) = (∑ i, v i) / N := by
    change (∑ p ∈ univ.filter (fun p : Fin L => p.val < (Fin.last L).val), v p) /
      (N : ℝ) = (∑ i, v i) / N
    congr 1
    apply Finset.sum_congr
    · ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_last]
      exact iff_true_intro i.isLt
    · intro i _
      rfl
  change (StrictMono (internalGapSection N L v) ∧
    ∀ i, internalGapSection N L v i < internalGapSection N L v ⟨0, L.succPNat.pos⟩ + 1) ↔ _
  have hz : internalGapSection N L v ⟨0, L.succPNat.pos⟩ = 0 := by
    change (∑ p ∈ univ.filter (fun p : Fin L => p.val < 0), v p) / (N : ℝ) = 0
    simp
  rw [hz]
  constructor
  · rintro ⟨hm, hb⟩
    refine ⟨fun i => ?_, ?_⟩
    · have hs := sub_pos.mpr (hm (Fin.castSucc_lt_succ (i := i)))
      rw [internalGapSection_succ] at hs
      exact (div_pos_iff_of_pos_right hN).mp hs
    · have hs := hb (Fin.last L)
      rw [hlast, zero_add] at hs
      exact (div_lt_one hN).mp hs
  · rintro ⟨hp, hs⟩
    have hm : StrictMono (internalGapSection N L v) := by
      apply Fin.strictMono_iff_lt_succ.mpr
      intro i
      apply sub_pos.mp
      rw [internalGapSection_succ]
      exact div_pos (hp i) hN
    refine ⟨hm, fun i => ?_⟩
    calc internalGapSection N L v i ≤ internalGapSection N L v (Fin.last L) :=
          hm.monotone (Fin.le_last i)
      _ < 0 + 1 := by rw [hlast, zero_add]; exact (div_lt_one hN).mpr hs

namespace Internal

/-- Adjacent pairs form a subset of all the unordered pairs. -/
theorem curvature_adjacent_sum_le (L : ℕ) (u : HsEuclidean L.succPNat) :
    (∑ i : Fin L, (u i.succ - u i.castSucc) ^ 2) ≤
      ∑ i : Fin (L + 1), ∑ j ∈ univ.filter (i < ·), (u j - u i) ^ 2 := by
  calc _ ≤ ∑ i : Fin L, ∑ j ∈ univ.filter (i.castSucc < ·), (u j - u i.castSucc) ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        exact Finset.single_le_sum (fun (j : Fin (L + 1)) _ => sq_nonneg (u j - u i.castSucc))
          (mem_filter.mpr ⟨mem_univ _, Fin.castSucc_lt_succ⟩)
    _ ≤ (∑ i : Fin L, ∑ j ∈ univ.filter (i.castSucc < ·), (u j - u i.castSucc) ^ 2) +
        ∑ j ∈ univ.filter (Fin.last L < ·), (u j - u (Fin.last L)) ^ 2 :=
      le_add_of_nonneg_right (Finset.sum_nonneg fun j _ => sq_nonneg _)
    _ = _ := (Fin.sum_univ_castSucc
      (fun i : Fin (L + 1) => ∑ j ∈ univ.filter (i < ·), (u j - u i) ^ 2)).symm

end Internal

/-- Exact Hessian under the linear internal-gap section. -/
theorem internalGapEnergy_hessian (N : ℕ+) (L : ℕ) (s : RieszExponent)
    {θ : ℝ → ℝ} (hθ : IsForcingCutoff θ) {R : ℝ} (hR : 1 ≤ R)
    {v : EuclideanSpace ℝ (Fin L)} (hv : v ∈ internalGapDomain N L)
    (w : EuclideanSpace ℝ (Fin L)) :
    fderiv ℝ (fderiv ℝ (fun v => internalConvexifiedEnergy N L.succPNat s θ R
        (internalGapSection N L v))) v w w =
      fderiv ℝ (fderiv ℝ (internalConvexifiedEnergy N L.succPNat s θ R))
        (internalGapSection N L v) (internalGapSection N L w) (internalGapSection N L w) := by
  let A := internalGapSection N L
  let χ := curvaturePairPotentials N L.succPNat s hθ hR
  change fderiv ℝ (fderiv ℝ (fun v => hsPairExpression χ (A v))) v w w =
    fderiv ℝ (fderiv ℝ (hsPairExpression χ)) (A v) (A w) (A w)
  have hgrad : fderiv ℝ (fun v => hsPairExpression χ (A v)) =ᶠ[𝓝 v]
      fun z => (hsPairGradient χ (A z)).comp A := by
    filter_upwards [(isOpen_internalGapDomain N L).mem_nhds hv] with z hz
    exact ((hasFDerivAt_hsPairExpression χ hz).comp z A.hasFDerivAt).fderiv
  rw [hgrad.fderiv_eq]
  have hc : HasFDerivAt (fun z => hsPairGradient χ (A z))
      ((hsPairHessian χ (A v)).comp A) v :=
    (hasFDerivAt_hsPairGradient χ hv).comp v A.hasFDerivAt
  rw [(hc.clm_comp (hasFDerivAt_const A v)).fderiv, fderiv_fderiv_hsPairExpression χ hv]
  simp [A]
  rfl

/-- The internal-energy contribution has gap curvature `a_s R^(-s-2)`.
The full marginal additionally contains the convex exterior contribution. -/
theorem internalGapEnergy_hessian_lower (N : ℕ+) (L : ℕ) (s : RieszExponent)
    {θ : ℝ → ℝ} (hθ : IsForcingCutoff θ) {R : ℝ} (hR : 1 ≤ R)
    {v : EuclideanSpace ℝ (Fin L)} (hv : v ∈ internalGapDomain N L)
    (w : EuclideanSpace ℝ (Fin L)) :
    rigidityCurvatureConstant s.val * R ^ (-s.val - 2) * ‖w‖ ^ 2 ≤
      fderiv ℝ (fderiv ℝ (fun v => internalConvexifiedEnergy N L.succPNat s θ R
        (internalGapSection N L v))) v w w := by
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast N.ne_zero
  have hc : 0 ≤ rigidityCurvatureConstant s.val * (N : ℝ) ^ 2 * R ^ (-s.val - 2) :=
    mul_nonneg (mul_nonneg (rigidityCurvatureConstant_pos s).le (sq_nonneg _))
      (Real.rpow_nonneg (by linarith) _)
  have hsum := mul_le_mul_of_nonneg_left
    (Internal.curvature_adjacent_sum_le L (internalGapSection N L w)) hc
  have hb := internalConvexifiedEnergy_hessian_lower N L.succPNat s hθ hR hv
    (internalGapSection N L w)
  rw [internalGapEnergy_hessian N L s hθ hR hv w]
  apply le_trans _ (hsum.trans hb)
  simp only [internalGapSection_succ, div_pow, ← Finset.sum_div]
  have hnorm : ‖w‖ ^ 2 = ∑ i, w i ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Real.norm_eq_abs, sq_abs]
  rw [hnorm]
  apply le_of_eq
  field_simp

/-- Convex Gaussian residual of the internal gap energy. -/
theorem convexOn_internalGapEnergy_residual (N : ℕ+) (L : ℕ) (s : RieszExponent)
    {θ : ℝ → ℝ} (hθ : IsForcingCutoff θ) {R : ℝ} (hR : 1 ≤ R) :
    ConvexOn ℝ (internalGapDomain N L) (fun v =>
      internalConvexifiedEnergy N L.succPNat s θ R (internalGapSection N L v) -
        (rigidityCurvatureConstant s.val * R ^ (-s.val - 2)) / 2 * ‖v‖ ^ 2) := by
  apply convexOn_sub_norm_sq_of_hessian_lower (convex_internalGapDomain N L)
    (isOpen_internalGapDomain N L)
  · exact ((hsPairExpression_contDiffOn (curvaturePairPotentials N L.succPNat s hθ hR)).comp
      (internalGapSection N L).contDiff.contDiffOn (fun _ hv => hv)).of_le (by norm_num)
  · exact fun v hv w => internalGapEnergy_hessian_lower N L s hθ hR hv w

end Riesz1

end
