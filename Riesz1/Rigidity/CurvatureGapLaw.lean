/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Rigidity.CurvatureGapCoordinates
public import Riesz1.Rigidity.CurvatureRelabel
public import Riesz1.ToMathlib.LinearTilted

/-!
# The normalized constrained internal-gap law

The marginal density and Gaussian convex factorization of the constrained law.
The exterior potential is `blockTilde` of the full forced pair datum.
Its convexity is derived from the Prékopa–Leindler inequality
`External.PrekopaLeindler`, which is taken as a hypothesis.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Riesz1.Internal

/-- Translation invariance of the whole marginal potential. -/
theorem curvature_blockPotential_translate {N M : ℕ+} {n : ℕ} {c : ℝ}
    (χ : HsPairPotentials N c) (e : Fin (M : ℕ) ⊕ Fin n ≃ Fin (N : ℕ))
    (hmono : StrictMono fun a => e (Sum.inl a)) (z : HsEuclidean M) (t : ℝ) :
    blockRetainedEnergy χ e (hsTranslate t z) + blockTilde χ e (hsTranslate t z) =
      blockRetainedEnergy χ e z + blockTilde χ e z := by
  rw [blockRetainedEnergy_eq_pairExpression χ e hmono,
    hsPairExpression_translate]
  have he : hsTranslate t z = z + constVec (M : ℕ) t := by
    ext i
    simp only [hsTranslate_apply, PiLp.add_apply, constVec_apply]
  rw [he, blockTilde_translate]

/-- The radial-to-gap Jacobian is constant and cancels on normalization. -/
theorem blockRadialProbability_map_internalGaps (hPL : External.PrekopaLeindler)
    {N : ℕ+} {L n : ℕ} {c : ℝ} (χ : HsPairPotentials N c) (hc : 0 < c)
    (e : Fin (L.succPNat : ℕ) ⊕ Fin n ≃ Fin (N : ℕ))
    (hmono : StrictMono fun a => e (Sum.inl a))
    (he0 : e (Sum.inl ⟨0, L.succPNat.pos⟩) = ⟨0, N.pos⟩) (Ns : ℕ+) :
    (blockRadialProbability hPL χ hc e hmono he0 : Measure _).map
      (fun z : hsOrthSubspace L.succPNat => internalBlockGaps Ns L z.val) =
      (volume.restrict (internalGapDomain Ns L)).tilted (fun v =>
        -(blockRetainedEnergy χ e (internalGapSection Ns L v) +
          blockTilde χ e (internalGapSection Ns L v))) := by
  let T := (internalGapRadialEquiv Ns L).toContinuousLinearEquiv.symm
  let V := fun v => -(blockRetainedEnergy χ e (internalGapSection Ns L v) +
    blockTilde χ e (internalGapSection Ns L v))
  have hdom : T ⁻¹' internalGapDomain Ns L = hsRadialDomain L.succPNat := by
    ext z
    have h := internalGapRadialEquiv_mem Ns L ((internalGapRadialEquiv Ns L).symm z)
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.symm
  have hpot (z : hsOrthSubspace L.succPNat) :
      V (T z) = -(blockRetainedEnergy χ e z.val + blockTilde χ e z.val) := by
    have he : internalGapSection Ns L (internalBlockGaps Ns L z.val) =
        hsTranslate (-z.val 0) z.val := by
      ext r
      rw [internalGapSection_reconstruct]
      simp only [hsTranslate_apply, sub_eq_add_neg]
    change -(blockRetainedEnergy χ e (internalGapSection Ns L (internalBlockGaps Ns L z.val)) +
      blockTilde χ e (internalGapSection Ns L (internalBlockGaps Ns L z.val))) = _
    rw [he, curvature_blockPotential_translate χ e hmono]
  have h := linearEquiv_map_tilted T (internalGapDomain Ns L) V
  rw [hdom] at h
  simp_rw [hpot] at h
  rw [← blockRadialProbability_eq_tilted hPL χ hc e hmono he0] at h
  exact h

end Riesz1.Internal

namespace Riesz1

/-- The retained part of the full forced Hamiltonian is exactly `β H_I`. -/
theorem curvatureInitialPairs_retainedEnergy (P : Parameters) (N : ℕ+) {L : ℕ}
    (hL : L < (N : ℕ)) {θ : ℝ → ℝ} (hθ : IsForcingCutoff θ) {R : ℝ} (hR : 0 < R)
    (z : HsEuclidean L.succPNat) :
    blockRetainedEnergy (curvatureInitialPairs P N (L + 1) hθ hR)
      (blockInitialEquiv L.succPNat N (Nat.succ_le_of_lt hL)) z =
      P.val.1 * internalConvexifiedEnergy N L.succPNat (parametersExponent P) θ R z := by
  change 2 * (∑ i : Fin (L + 1), ∑ j ∈ Finset.univ.filter (i < ·),
    (curvatureInitialPairs P N (L + 1) hθ hR).potential
      (Fin.castLE (Nat.succ_le_of_lt hL) i) (Fin.castLE (Nat.succ_le_of_lt hL) j)
        (z j - z i)) = _
  simp_rw [curvatureInitialPairs_retained P N (Nat.succ_le_of_lt hL) hθ hR]
  change 2 * (∑ i : Fin (L + 1), ∑ j ∈ Finset.univ.filter (i < ·),
      P.val.1 * curvaturePairPotential N (parametersExponent P) θ R (z j - z i)) =
    P.val.1 * (2 * (∑ i : Fin (L + 1), ∑ j ∈ Finset.univ.filter (i < ·),
      curvaturePairPotential N (parametersExponent P) θ R (z j - z i)))
  simp only [← Finset.mul_sum]
  ring

/-- The normalized gap law, for every integer start.
Its density is the normalized exponential of `β H_I + H̃` in the specified section. -/
theorem constrainedLaw_internalGap_density (hPL : External.PrekopaLeindler)
    (P : Parameters) (N : ℕ+) (i0 : ℤ) {L : ℕ} (hL : L < (N : ℕ))
    {θ : ℝ → ℝ} (hθ : IsForcingCutoff θ) {R : ℝ} (hR : 0 < R) :
    let χ := curvatureInitialPairs P N (L + 1) hθ hR
    let e := blockInitialEquiv L.succPNat N (Nat.succ_le_of_lt hL)
    (constrainedLaw P N θ i0 L R).map
      (fun X => internalBlockGaps N L (WithLp.toLp 2 (liftedBlock i0 hL X).val)) =
      (volume.restrict (internalGapDomain N L)).tilted (fun v =>
        -(P.val.1 * internalConvexifiedEnergy N L.succPNat (parametersExponent P) θ R
          (internalGapSection N L v) + blockTilde χ e (internalGapSection N L v))) := by
  dsimp only
  let χ := curvatureInitialPairs P N (L + 1) hθ hR
  let e := blockInitialEquiv L.succPNat N (Nat.succ_le_of_lt hL)
  have hc := hsRieszPairPotentials_curvature_pos N P.2.1 (parametersExponent P)
  have hmono := blockInitialEquiv_strictMono (M := L.succPNat) (N := N) (Nat.succ_le_of_lt hL)
  have he0 := blockInitialEquiv_zero (M := L.succPNat) (N := N) (Nat.succ_le_of_lt hL)
  have hinit : (constrainedLaw P N θ 0 L R).map
      (fun X => internalBlockGaps N L (WithLp.toLp 2 (liftedBlock 0 hL X).val)) =
      (volume.restrict (internalGapDomain N L)).tilted (fun v =>
        -(P.val.1 * internalConvexifiedEnergy N L.succPNat (parametersExponent P) θ R
          (internalGapSection N L v) + blockTilde χ e (internalGapSection N L v))) := by
    have hp := hsGibbs_blockRadial_measurePreserving hPL χ hc e hmono he0
    have hm : Measurable (fun z : hsOrthSubspace L.succPNat => internalBlockGaps N L z.val) := by
      unfold internalBlockGaps
      fun_prop
    have h := congrArg (fun μ : Measure (hsOrthSubspace L.succPNat) =>
      μ.map (fun z => internalBlockGaps N L z.val)) hp.map_eq
    rw [Measure.map_map hm hp.measurable, curvatureInitialPairs_gibbs P N hL hθ hR,
      Internal.blockRadialProbability_map_internalGaps hPL χ hc e hmono he0 N] at h
    have hfun : (fun X => internalBlockGaps N L (hsOrthComp L.succPNat (retainedCoord e X))) =
        fun X => internalBlockGaps N L (WithLp.toLp 2 (liftedBlock 0 hL X).val) := by
      funext X
      change internalBlockGaps N L (hsOrthProj L.succPNat (retainedCoord e X)) = _
      rw [hsOrthProj_eq_translate, internalBlockGaps_translate, liftedBlock_zero_coords]
    simp only [Function.comp_def] at h
    rw [hfun] at h
    dsimp only [χ, e] at h
    simp_rw [curvatureInitialPairs_retainedEnergy P N hL hθ hR] at h
    exact h
  obtain ⟨k, _, q, hi0⟩ := exists_nat_add_mul (N := N) i0
  have hm : Measurable (fun X : Configuration N =>
      internalBlockGaps N L (WithLp.toLp 2 (liftedBlock 0 hL X).val)) := by
    have hb := measurable_liftedBlock (N := N) 0 hL
    have hG : Measurable (fun z : HsEuclidean L.succPNat => internalBlockGaps N L z) := by
      unfold internalBlockGaps
      fun_prop
    exact hG.comp (((PiLp.continuous_toLp 2 _).measurable.comp measurable_subtype_coe).comp hb)
  have h := congrArg (fun μ : Measure (Configuration N) => μ.map
    (fun X => internalBlockGaps N L (WithLp.toLp 2 (liftedBlock 0 hL X).val)))
      (map_constrainedLaw_relabel P N i0 hi0 hL hθ R)
  rw [Measure.map_map hm (measurable_hsRelabelConfiguration N k), hinit] at h
  simpa only [Function.comp_def, ← liftedBlock_eq_relabel i0 hi0 hL] using h

/-- The potential of the actual constrained internal-gap law has the asserted
Gaussian convex factorization, including when no classical exterior Hessian exists. -/
theorem convexOn_constrainedGap_residual (hPL : External.PrekopaLeindler)
    (P : Parameters) (N : ℕ+) {L : ℕ} (hL : L < (N : ℕ))
    {θ : ℝ → ℝ} (hθ : IsForcingCutoff θ) {R : ℝ} (hR : 1 ≤ R) :
    let χ := curvatureInitialPairs P N (L + 1) hθ (lt_of_lt_of_le zero_lt_one hR)
    let e := blockInitialEquiv L.succPNat N (Nat.succ_le_of_lt hL)
    ConvexOn ℝ (internalGapDomain N L) (fun v =>
      P.val.1 * internalConvexifiedEnergy N L.succPNat (parametersExponent P) θ R
        (internalGapSection N L v) + blockTilde χ e (internalGapSection N L v) -
          (P.val.1 * rigidityCurvatureConstant (parametersExponent P).val *
            R ^ (-(parametersExponent P).val - 2)) / 2 * ‖v‖ ^ 2) := by
  dsimp only
  let χ := curvatureInitialPairs P N (L + 1) hθ (lt_of_lt_of_le zero_lt_one hR)
  let e := blockInitialEquiv L.succPNat N (Nat.succ_le_of_lt hL)
  have hc := hsRieszPairPotentials_curvature_pos N P.2.1 (parametersExponent P)
  have hext := convexOn_blockTilde hPL χ hc e (blockInitialEquiv_strictMono _)
    L.succPNat.pos (blockInitialEquiv_zero _)
  have he : ConvexOn ℝ (internalGapDomain N L)
      (fun v => blockTilde χ e (internalGapSection N L v)) := by
    refine ⟨convex_internalGapDomain N L, fun x hx y hy a b ha hb hab => ?_⟩
    have hx' : internalGapSection N L x ∈ retainedChamber (L.succPNat : ℕ) := by
      rwa [retainedChamber_eq_hsChamber]
    have hy' : internalGapSection N L y ∈ retainedChamber (L.succPNat : ℕ) := by
      rwa [retainedChamber_eq_hsChamber]
    simpa only [map_add, map_smul] using hext.2 hx' hy' ha hb hab
  have hi := (convexOn_internalGapEnergy_residual N L (parametersExponent P) hθ hR).smul P.2.1.le
  convert hi.add he using 1
  funext v
  dsimp [χ, e]
  ring

/-- The gap-law assertion, with a finite positive normalizer and
the convex residual expressing its Hessian lower bound.
The density is with respect to Lebesgue measure on the specified gap chamber. -/
theorem curvature_internalGap_law (hPL : External.PrekopaLeindler)
    (P : Parameters) (N : ℕ+) (i0 : ℤ) {L : ℕ} (hL : L < (N : ℕ))
    {θ : ℝ → ℝ} (hθ : IsForcingCutoff θ) {R : ℝ} (hR : 1 ≤ R) :
    ∃ V : EuclideanSpace ℝ (Fin L) → ℝ,
      IntegrableOn (fun v => Real.exp (-V v)) (internalGapDomain N L) ∧
      0 < ∫ v in internalGapDomain N L, Real.exp (-V v) ∧
      (constrainedLaw P N θ i0 L R).map
        (fun X => internalBlockGaps N L (WithLp.toLp 2 (liftedBlock i0 hL X).val)) =
        (volume.restrict (internalGapDomain N L)).withDensity (fun v => ENNReal.ofReal
          (Real.exp (-V v) / ∫ w in internalGapDomain N L, Real.exp (-V w))) ∧
      ConvexOn ℝ (internalGapDomain N L) (fun v => V v -
        (P.val.1 * rigidityCurvatureConstant (parametersExponent P).val *
          R ^ (-(parametersExponent P).val - 2)) / 2 * ‖v‖ ^ 2) := by
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  let χ := curvatureInitialPairs P N (L + 1) hθ hR0
  let e := blockInitialEquiv L.succPNat N (Nat.succ_le_of_lt hL)
  let V := fun v => P.val.1 * internalConvexifiedEnergy N L.succPNat
    (parametersExponent P) θ R (internalGapSection N L v) +
      blockTilde χ e (internalGapSection N L v)
  have hden := constrainedLaw_internalGap_density hPL P N i0 hL hθ hR0
  change (constrainedLaw P N θ i0 L R).map
    (fun X => internalBlockGaps N L (WithLp.toLp 2 (liftedBlock i0 hL X).val)) =
      (volume.restrict (internalGapDomain N L)).tilted (fun v => -V v) at hden
  have hQ := isProbabilityMeasure_constrainedLaw P N hθ hR0 i0 L
  have hm : Measurable (fun X : Configuration N =>
      internalBlockGaps N L (WithLp.toLp 2 (liftedBlock i0 hL X).val)) := by
    have hG : Measurable (fun z : HsEuclidean L.succPNat => internalBlockGaps N L z) := by
      unfold internalBlockGaps
      fun_prop
    exact hG.comp (((PiLp.continuous_toLp 2 _).measurable.comp measurable_subtype_coe).comp
      (measurable_liftedBlock i0 hL))
  have hprob : IsProbabilityMeasure
      ((volume.restrict (internalGapDomain N L)).tilted (fun v => -V v)) := by
    rw [← hden]
    exact (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).mpr hQ
  obtain ⟨hi, hz⟩ := normalization_of_probability_tilted
    (volume.restrict (internalGapDomain N L)) (fun v => -V v)
  exact ⟨V, hi, hz, hden, convexOn_constrainedGap_residual hPL P N hL hθ hR⟩

end Riesz1

end
