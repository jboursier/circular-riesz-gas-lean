/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.APrioriMembershipInput
public import Riesz1.Variance.APrioriBoundGradientEnergy
public import Riesz1.HelfferSjostrand.AnchoredLipschitzH1

/-!
# Completion membership of the actual localized cutoff product

The reciprocal cutoff has a continuous representative obtained by clamping
its positive denominator below one. The representative agrees with the
cutoff on the open positive-gap domain. This supplies the actual
completion membership, including the product-rule gradient.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology InnerProductSpace

namespace Riesz1.Internal

/-- The inverse of a denominator clamped below one is Lipschitz. -/
theorem a_priori_lipschitz_inverse_clamp :
    LipschitzWith 1 (fun x : ℝ => (max x 1)⁻¹) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hx : 0 < max x 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hy : 0 < max y 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hp : 1 ≤ max x 1 * max y 1 :=
    one_le_mul_of_one_le_of_one_le (le_max_right _ _) (le_max_right _ _)
  rw [Real.dist_eq, Real.dist_eq, inv_sub_inv hx.ne' hy.ne', abs_div,
    abs_of_pos (mul_pos hx hy), abs_sub_comm]
  simp only [NNReal.coe_one, one_mul]
  exact (div_le_self (abs_nonneg _) hp).trans (abs_max_sub_max_le_abs x y 1)

/-- Multiplication preserves local Lipschitz regularity for real functions. -/
theorem a_priori_locallyLipschitz_mul {E : Type*} [PseudoEMetricSpace E]
    {f g : E → ℝ} (hf : LocallyLipschitz f) (hg : LocallyLipschitz g) :
    LocallyLipschitz (fun x => f x * g x) :=
  locallyLipschitzOn_univ.mp (WeightedSobolev.locallyLipschitzOn_mul_real
    hf.locallyLipschitzOn hg.locallyLipschitzOn)

/-- A finite product of real locally Lipschitz functions is locally Lipschitz. -/
theorem a_priori_locallyLipschitz_prod {E ι : Type*} [PseudoEMetricSpace E]
    (I : Finset ι) (f : ι → E → ℝ) (hf : ∀ i ∈ I, LocallyLipschitz (f i)) :
    LocallyLipschitz (fun x => ∏ i ∈ I, f i x) := by
  classical
  induction I using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty] using (LocallyLipschitz.const (1 : ℝ))
  | @insert i I hi ih =>
      simp only [Finset.prod_insert hi]
      exact a_priori_locallyLipschitz_mul (hf i (Finset.mem_insert_self _ _))
        (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

/-- The continuous reciprocal-cutoff representative agrees on positive inputs. -/
theorem a_priori_reciprocal_cutoff_eq {r : ℝ} (hr : 0 < r) :
    scalarCutoff (2 * (max r 1)⁻¹) = scalarCutoff (2 / r) := by
  by_cases h : 1 ≤ r
  · rw [max_eq_left h, div_eq_mul_inv]
  · have hsmall : r ≤ 1 := le_of_lt (lt_of_not_ge h)
    rw [max_eq_right hsmall, inv_one, mul_one,
      scalarCutoff_eq_zero_of_two_le le_rfl,
      scalarCutoff_eq_zero_of_two_le ((le_div_iff₀ hr).mpr (by linarith))]

/-- The gradient in the Euclidean realization has exactly the differential
coordinates used by the cutoff field. -/
theorem anchoredCutoffField_eq_smul_gradient {n : ℕ} (s K γ ε : ℝ)
    (T : (Fin n → ℝ) → ℝ) (y : AnchoredEuclidean n)
    (hd : DifferentiableAt ℝ (anchoredCutoff n.succPNat s K γ ε) (WithLp.ofLp y)) :
    anchoredCutoffField n s K γ ε T y = T (WithLp.ofLp y) •
      gradient (fun z : AnchoredEuclidean n =>
        anchoredCutoff n.succPNat s K γ ε (WithLp.ofLp z)) y := by
  have hd' := hd.hasFDerivAt.comp y
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).hasFDerivAt
  apply PiLp.ext
  intro i
  have he := hd'.differentiableAt.hasGradientAt.fderiv_apply (y := EuclideanSpace.single i 1)
  rw [hd'.fderiv] at he
  have hinner : inner ℝ (gradient (fun z : AnchoredEuclidean n =>
      anchoredCutoff n.succPNat s K γ ε (WithLp.ofLp z)) y)
        (EuclideanSpace.single i 1) =
      gradient (fun z : AnchoredEuclidean n =>
        anchoredCutoff n.succPNat s K γ ε (WithLp.ofLp z)) y i := by
    rw [EuclideanSpace.inner_single_right]
    simp only [RCLike.conj_to_real, one_mul]
  change _ = inner ℝ (gradient (fun z : AnchoredEuclidean n =>
    anchoredCutoff n.succPNat s K γ ε (WithLp.ofLp z)) y) (EuclideanSpace.single i 1) at he
  rw [hinner] at he
  change T (WithLp.ofLp y) * _ = T (WithLp.ofLp y) * _
  congr 1

/-- The literal cutoff product belongs to the anchored completion.
The clamped expression is used only to establish membership. The conclusion
uses the cutoff and field on their original carriers. -/
theorem a_priori_membership_input : APrioriMembershipInput := by
  intro P n hn θ hθ ℓ hℓ hK γ ε hγ hε f hf
  dsimp only
  let K := ((n : ℝ) + 1) * ℓ
  let χ := nearestTiltedPairs P n.succPNat hθ K γ ε (by dsimp [K]; linarith)
  let F := fun y : AnchoredEuclidean n =>
    ∑ j ∈ window n.succPNat K γ, f (anchorVector (WithLp.ofLp y) j / ℓ)
  let η := fun y : AnchoredEuclidean n =>
    anchoredCutoff n.succPNat P.val.2 K γ ε (WithLp.ofLp y)
  let Z := fun y : AnchoredEuclidean n => anchoredGapVector n (WithLp.ofLp y)
  let ηc := fun y : AnchoredEuclidean n =>
    (∏ p ∈ cutoffPairs n.succPNat (window n.succPNat K γ),
      scalarCutoff (2 * |gapPairDev n.succPNat (Z y) p| / pairScale P.val.2 K ε p)) *
    ∏ i ∈ nearestPairs n.succPNat (window n.succPNat K γ),
      (scalarCutoff (2 * Z y i / K ^ ε) * scalarCutoff (2 * (max (K ^ ε * Z y i) 1)⁻¹))
  have hF := localizedStatistic_contDiff n ℓ f hf (window n.succPNat K γ)
  have hZ : ContDiff ℝ 1 Z := by
    have hd : ContDiff ℝ 1 (anchoredGapVector n) := by
      have heq : anchoredGapVector n = fun y => anchoredGapLinear n y + anchoredGapVector n 0 := by
        funext y
        ext i
        change anchoredGapAt n y (i : ℕ) = ((n : ℝ) + 1) * edgeForm n i y +
          anchoredGapAt n 0 (i : ℕ)
        rw [anchoredGapAt_label, anchoredGapAt_label]
        simp only [map_zero]
        ring
      rw [heq]
      exact (anchoredGapLinear n).contDiff.add contDiff_const
    exact hd.comp (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).contDiff
  have hscalar : LocallyLipschitz scalarCutoff := by
    have hsub : ContDiff ℝ 1 (fun r : ℝ => 2 - r) := contDiff_const.sub contDiff_id
    exact (hsub.locallyLipschitz.const_max 0).const_min 1
  have hηc : LocallyLipschitz ηc := by
    apply a_priori_locallyLipschitz_mul
    · apply a_priori_locallyLipschitz_prod
      intro p _
      have hdev : ContDiff ℝ 1 (fun y => gapPairDev n.succPNat (Z y) p) := by
        unfold gapPairDev gapOrientedSum
        fun_prop
      have hAbsLip : LipschitzWith 1 (fun r : ℝ => |r|) := by
        apply LipschitzWith.of_dist_le_mul
        intro x y
        simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using abs_abs_sub_abs_le_abs_sub x y
      have habs := hAbsLip.locallyLipschitz.comp hdev.locallyLipschitz
      have hscale : ContDiff ℝ 1 (fun r : ℝ => 2 * r / pairScale P.val.2 K ε p) := by fun_prop
      exact hscalar.comp (hscale.locallyLipschitz.comp habs)
    · apply a_priori_locallyLipschitz_prod
      intro i _
      have hzi : ContDiff ℝ 1 (fun y => Z y i) := (contDiff_pi.mp hZ) i
      apply a_priori_locallyLipschitz_mul
      · exact hscalar.comp ((contDiff_const.mul hzi |>.div_const (K ^ ε)).locallyLipschitz)
      · have hmul : ContDiff ℝ 1 (fun y => K ^ ε * Z y i) := contDiff_const.mul hzi
        have htwo : ContDiff ℝ 1 (fun r : ℝ => 2 * r) := contDiff_const.mul contDiff_id
        exact hscalar.comp (htwo.locallyLipschitz.comp
          (a_priori_lipschitz_inverse_clamp.locallyLipschitz.comp hmul.locallyLipschitz))
  have heq (y : AnchoredEuclidean n) (hy : y ∈ anchoredSimplex n) : ηc y = η y := by
    have hp (e : Fin (n.succPNat : ℕ)) : 0 < Z y e := by
      have ha : anchorVector (WithLp.ofLp y) ∈ orderedDomain n.succPNat := by
        have hyd : (WithLp.ofLp y) ∈ anchoredDomain n := hy
        refine ⟨?_, ?_, ?_, ?_⟩
        · exact Fin.strictMono_cons.mpr ⟨fun j => (hyd.1 j).1, hyd.2⟩
        · change (0 : ℝ) ≤ 0
          rfl
        · change (0 : ℝ) < 1
          norm_num
        · intro i
          induction i using Fin.cases with
          | zero => change (0 : ℝ) < 0 + 1; norm_num
          | succ j =>
              change (WithLp.ofLp y) j < 0 + 1
              simpa only [zero_add] using (hyd.1 j).2
      let X : Configuration n.succPNat := ⟨anchorVector (WithLp.ofLp y), ha⟩
      change 0 < anchoredGapVector n (WithLp.ofLp y) e
      rw [← vectorGap_anchoredLift_eq, anchoredLift_eq_anchorVector]
      exact gap_pos X (e : ℕ)
    dsimp only [ηc, η]
    rw [anchoredCutoff_eq_comp_gapVector]
    unfold gapCutoff
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    rw [a_priori_reciprocal_cutoff_eq (mul_pos (Real.rpow_pos_of_pos (by dsimp [K]; linarith) _) (hp i))]
  have hH := isAnchoredH1_of_locallyLipschitzOn χ
    (hsRieszPairPotentials_curvature_pos n.succPNat P.2.1 (parametersExponent P))
    isOpen_univ (subset_univ _) (a_priori_locallyLipschitz_mul hηc hF.locallyLipschitz).locallyLipschitzOn
  have hae := anchoredMeasureE_cutoff_chain_ae hn χ P.val.2 K γ ε hK
    (by linarith) P.2.2.1.le hε.le
  apply hH.congr
  · filter_upwards [ae_mem_anchoredSimplex χ] with y hy
    exact congrArg (fun r => r * F y) (heq y hy)
  · filter_upwards [ae_mem_anchoredSimplex χ, hae] with y hy hd
    change gradient (fun z => ηc z * F z) y =
      η y • gradient F y + anchoredCutoffField n P.val.2 K γ ε
        (fun z : Fin n → ℝ => ∑ j ∈ window n.succPNat K γ, f (anchorVector z j / ℓ)) y
    have hηd : DifferentiableAt ℝ (anchoredCutoff n.succPNat P.val.2 K γ ε) (WithLp.ofLp y) := by
      rw [anchoredCutoff_eq_comp_gapVector]
      exact hd.1.comp _ (anchoredGapVector_hasFDerivAt n _).differentiableAt
    have hdη := hηd.comp y (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).differentiableAt
    have hev : (fun z => ηc z * F z) =ᶠ[𝓝 y] (fun z => η z * F z) := by
      filter_upwards [(isOpen_anchoredSimplex n).mem_nhds hy] with z hz
      rw [heq z hz]
    rw [hev.gradient_eq]
    have hprod := (hdη.hasFDerivAt.mul (hF.differentiable one_ne_zero y).hasFDerivAt).fderiv
    change fderiv ℝ (fun z => η z * F z) y = _ at hprod
    rw [anchoredCutoffField_eq_smul_gradient _ _ _ _ _ y hηd]
    change gradient (fun z => η z * F z) y = η y • gradient F y + F y • gradient η y
    simp only [gradient]
    rw [hprod]
    simp only [map_add, map_smul]
    rfl

end Riesz1.Internal

end
