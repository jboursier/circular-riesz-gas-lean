/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Rigidity.CurvatureForcedPairs
public import Riesz1.Rigidity.CurvatureRelabel
public import Riesz1.ToMathlib.ConvexPotentialConcentration

/-!
# Differentiable block observables under the actual constrained law

The radial Lipschitz proof of the exponential moment bound
for block observables, for an initial block. Differentiability and the
gradient bound are required only on the open lifted chamber.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace Riesz1.Internal

/-- Direct radial proof, with no Sobolev membership premise on the observable. -/
theorem block_differentiable_concentration (hBE : External.BakryEmery)
    (hPL : External.PrekopaLeindler) {N M : ℕ+} {n : ℕ} {c c₁ : ℝ}
    (χ : HsPairPotentials N c) (hc : 0 < c) (hc₁ : 0 < c₁)
    (e : Fin (M : ℕ) ⊕ Fin n ≃ Fin (N : ℕ))
    (hmono : StrictMono fun a => e (Sum.inl a))
    (he0 : e (Sum.inl ⟨0, M.pos⟩) = ⟨0, N.pos⟩)
    (hcurv : ∀ x ∈ hsChamber N, ∀ i j : Fin (M : ℕ), i < j → c₁ / 2 ≤
      deriv (deriv (χ.potential (e (Sum.inl i)) (e (Sum.inl j))))
        (x (e (Sum.inl j)) - x (e (Sum.inl i))))
    {F : HsEuclidean M → ℝ} (hF : DifferentiableOn ℝ F (hsChamber M))
    (hrot : ∀ x ∈ hsChamber M, ∀ t : ℝ, F (hsTranslate t x) = F x)
    {B : ℝ≥0} (hB : ∀ x ∈ hsChamber M, ‖fderiv ℝ F x‖ ≤ B) (t : ℝ) :
    let A := fun X => F (retainedCoord e X)
    Integrable A (hsGibbsProbability χ hc : Measure _) ∧
      Integrable (fun X => Real.exp (t * A X)) (hsGibbsProbability χ hc : Measure _) ∧
      Real.log (∫ X, Real.exp (t * A X) ∂(hsGibbsProbability χ hc : Measure _)) ≤
        t * ∫ X, A X ∂(hsGibbsProbability χ hc : Measure _) +
          t ^ 2 * (B : ℝ) ^ 2 / (2 * c₁ * M) := by
  let basis := stdOrthonormalBasis ℝ (hsOrthSubspace M)
  let J := scalarPoincareRadialEmbedding basis
  let chart := scalarPoincareRadialChart basis
  let U := scalarPoincareRadialDomain basis
  let ν := (volume.restrict U).tilted (fun q => -blockRadialPotential χ e basis q)
  have hFD (q) (hq : q ∈ U) : DifferentiableAt ℝ F (J q) :=
    (hF (J q) hq).differentiableAt ((isOpen_hsChamber M).mem_nhds hq)
  have hLip : LipschitzOnWith B (fun q => F (J q)) U := by
    apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le
      (fun q hq => (hFD q hq).comp q J.toContinuousLinearMap.differentiableAt) _
      (convex_scalarPoincareRadialDomain basis)
    intro q hq
    apply NNReal.coe_le_coe.mp
    change ‖fderiv ℝ (F ∘ J) q‖ ≤ (B : ℝ)
    rw [fderiv_comp q (hFD q hq) J.toContinuousLinearMap.differentiableAt]
    have hJd : fderiv ℝ (J : _ → _) q = J.toContinuousLinearMap :=
      J.toContinuousLinearMap.hasFDerivAt.fderiv
    rw [hJd]
    apply ContinuousLinearMap.opNorm_le_bound _ B.coe_nonneg
    intro v
    change ‖fderiv ℝ F (J q) (J v)‖ ≤ _
    calc ‖fderiv ℝ F (J q) (J v)‖ ≤ ‖fderiv ℝ F (J q)‖ * ‖J v‖ :=
          (fderiv ℝ F (J q)).le_opNorm _
      _ ≤ B * ‖v‖ := by rw [J.norm_map]; exact mul_le_mul_of_nonneg_right (hB _ hq) (norm_nonneg _)
  obtain ⟨_, hAi, hEi, hmgf⟩ := convex_potential_lipschitz_concentration hBE
    (isOpen_scalarPoincareRadialDomain basis) (convex_scalarPoincareRadialDomain basis)
    (bounded_scalarPoincareRadialDomain basis) (nonempty_scalarPoincareRadialDomain basis)
    (mul_pos hc₁ (Nat.cast_pos.mpr M.pos))
    (convexOn_blockRadialResidual hPL χ hc e hmono he0 basis hcurv) hLip t
  change Integrable (fun q => F (J q)) ν at hAi
  change Integrable (fun q => Real.exp (t * F (J q))) ν at hEi
  have hchart : ν.map chart = (blockRadialProbability hPL χ hc e hmono he0 : Measure _) :=
    blockRadialChart_map hPL χ hc e hmono he0 basis
  have hback : MeasurePreserving chart.symm
      (blockRadialProbability hPL χ hc e hmono he0 : Measure _) ν := by
    refine ⟨chart.symm.continuous.measurable, ?_⟩
    rw [← hchart, Measure.map_map chart.symm.continuous.measurable chart.continuous.measurable]
    have hid : (chart.symm ∘ chart : _ → _) = id := by
      funext x
      exact chart.symm_apply_apply x
    rw [hid]
    exact Measure.map_id
  have hp := hback.comp (hsGibbs_blockRadial_measurePreserving hPL χ hc e hmono he0)
  have hval (X : Configuration N) :
      F (J (chart.symm (hsOrthComp M (retainedCoord e X)))) = F (retainedCoord e X) := by
    have hz : retainedCoord e X ∈ hsChamber M := by
      constructor
      · intro i j hij
        exact X.2.1 (hmono hij)
      · intro i
        change X.val (e (Sum.inl i)) < X.val (e (Sum.inl ⟨0, M.pos⟩)) + 1
        rw [he0]
        exact X.2.2.2.2 _
    have hJ : J (chart.symm (hsOrthComp M (retainedCoord e X))) =
        hsOrthProj M (retainedCoord e X) := by
      change (chart (chart.symm _) : HsEuclidean M) = _
      rw [chart.apply_symm_apply]
      rfl
    rw [hJ, hsOrthProj_eq_translate]
    exact hrot _ hz _
  obtain ⟨hA, hIA⟩ := integrable_integral_comp_measurePreserving hp hAi
  obtain ⟨hE, hIE⟩ := integrable_integral_comp_measurePreserving hp hEi
  simp only [Function.comp_def, hval] at hA hE hIA hIE
  refine ⟨hA, hE, ?_⟩
  rw [hIA, hIE]
  simpa only [mul_assoc] using hmgf

end Riesz1.Internal

namespace Riesz1

/-- The exponential moment bound for the initial block,
under the constrained law. The ambient representative is used
only on its chamber. -/
theorem curvature_initial_concentration (hBE : External.BakryEmery)
    (hPL : External.PrekopaLeindler) (P : Parameters) (N : ℕ+) {L : ℕ}
    (hL : L < (N : ℕ)) {θ : ℝ → ℝ} (hθ : IsForcingCutoff θ) {R : ℝ} (hR : 1 ≤ R)
    {F : HsEuclidean L.succPNat → ℝ}
    (hF : DifferentiableOn ℝ F (hsChamber L.succPNat))
    (hrot : ∀ x ∈ hsChamber L.succPNat, ∀ t : ℝ, F (hsTranslate t x) = F x)
    {B : ℝ≥0} (hB : ∀ x ∈ hsChamber L.succPNat, ‖fderiv ℝ F x‖ ≤ B) (t : ℝ) :
    let A := fun X => F (WithLp.toLp 2 (liftedBlock 0 hL X).val)
    Integrable A (constrainedLaw P N θ 0 L R) ∧
      Integrable (fun X => Real.exp (t * A X)) (constrainedLaw P N θ 0 L R) ∧
      Real.log (∫ X, Real.exp (t * A X) ∂constrainedLaw P N θ 0 L R) ≤
        t * ∫ X, A X ∂constrainedLaw P N θ 0 L R +
          t ^ 2 * (B : ℝ) ^ 2 /
            (2 * (P.val.1 * rigidityCurvatureConstant (parametersExponent P).val *
              (N : ℝ) ^ 2 * R ^ (-(parametersExponent P).val - 2)) * (L + 1)) := by
  let e := blockInitialEquiv L.succPNat N (Nat.succ_le_of_lt hL)
  let χ := curvatureInitialPairs P N (L + 1) hθ (lt_of_lt_of_le zero_lt_one hR)
  have hc := hsRieszPairPotentials_curvature_pos N P.2.1 (parametersExponent P)
  have hκ : 0 < P.val.1 * rigidityCurvatureConstant (parametersExponent P).val *
      (N : ℝ) ^ 2 * R ^ (-(parametersExponent P).val - 2) := by
    have := rigidityCurvatureConstant_pos (parametersExponent P)
    have := P.2.1
    have : (0 : ℝ) < N := by exact_mod_cast N.pos
    positivity
  have hcurv : ∀ x ∈ hsChamber N, ∀ i j : Fin (L.succPNat : ℕ), i < j →
      (P.val.1 * rigidityCurvatureConstant (parametersExponent P).val *
        (N : ℝ) ^ 2 * R ^ (-(parametersExponent P).val - 2)) / 2 ≤
      deriv (deriv (χ.potential (e (Sum.inl i)) (e (Sum.inl j))))
        (x (e (Sum.inl j)) - x (e (Sum.inl i))) := by
    intro x hx i j hij
    exact curvatureInitialPairs_lower P N (Nat.succ_le_of_lt hL) hθ hR i j
      (hsChamber_separation_mem hx hij)
  have h := Internal.block_differentiable_concentration hBE hPL χ hc hκ e
    (blockInitialEquiv_strictMono _) (blockInitialEquiv_zero _) hcurv hF hrot hB t
  rw [curvatureInitialPairs_gibbs P N hL hθ] at h
  dsimp only
  simp_rw [liftedBlock_zero_coords]
  simpa only [e, Nat.succPNat_coe, Nat.cast_succ] using h

/-- The exponential moment bound for every integer starting label.
Both integrability statements concern the actual constrained probability. -/
theorem curvature_concentration (hBE : External.BakryEmery)
    (hPL : External.PrekopaLeindler) (P : Parameters) (N : ℕ+) (i0 : ℤ) {L : ℕ}
    (hL : L < (N : ℕ)) {θ : ℝ → ℝ} (hθ : IsForcingCutoff θ) {R : ℝ} (hR : 1 ≤ R)
    {F : HsEuclidean L.succPNat → ℝ}
    (hF : DifferentiableOn ℝ F (hsChamber L.succPNat))
    (hrot : ∀ x ∈ hsChamber L.succPNat, ∀ t : ℝ, F (hsTranslate t x) = F x)
    {B : ℝ≥0} (hB : ∀ x ∈ hsChamber L.succPNat, ‖fderiv ℝ F x‖ ≤ B) (t : ℝ) :
    let A := fun X => F (WithLp.toLp 2 (liftedBlock i0 hL X).val)
    Integrable A (constrainedLaw P N θ i0 L R) ∧
      Integrable (fun X => Real.exp (t * A X)) (constrainedLaw P N θ i0 L R) ∧
      Real.log (∫ X, Real.exp (t * A X) ∂constrainedLaw P N θ i0 L R) ≤
        t * ∫ X, A X ∂constrainedLaw P N θ i0 L R +
          R ^ ((parametersExponent P).val + 2) * (B : ℝ) ^ 2 * t ^ 2 /
            (2 * P.val.1 * rigidityCurvatureConstant (parametersExponent P).val *
              (N : ℝ) ^ 2 * (L + 1)) := by
  obtain ⟨k, _, q, hi0⟩ := exists_nat_add_mul (N := N) i0
  have hp : MeasurePreserving (hsRelabelConfiguration N k)
      (constrainedLaw P N θ i0 L R) (constrainedLaw P N θ 0 L R) :=
    ⟨measurable_hsRelabelConfiguration N k, map_constrainedLaw_relabel P N i0 hi0 hL hθ R⟩
  obtain ⟨hI, hE, hmgf⟩ := curvature_initial_concentration hBE hPL P N hL hθ hR hF hrot hB t
  obtain ⟨hIi, hIi_eq⟩ := integrable_integral_comp_measurePreserving hp hI
  obtain ⟨hEi, hEi_eq⟩ := integrable_integral_comp_measurePreserving hp hE
  simp only [← liftedBlock_eq_relabel i0 hi0 hL] at hIi hIi_eq hEi hEi_eq
  refine ⟨hIi, hEi, ?_⟩
  rw [hIi_eq, hEi_eq]
  apply hmgf.trans_eq
  congr 1
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  rw [show -(parametersExponent P).val - 2 = -((parametersExponent P).val + 2) by ring,
    Real.rpow_neg hR0.le]
  field_simp

end Riesz1

end
