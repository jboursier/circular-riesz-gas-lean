/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.ConvexityExterior
public import Riesz1.HelfferSjostrand.SettingQuotient
public import Riesz1.Frozen.External.PrekopaLeindler

/-!
# The density of the retained coordinates under the Gibbs measure

Let `χ` be a pair Hamiltonian, `e : Fin m ⊕ Fin n ≃ Fin N` a block decomposition with label `1`
retained, and `Z` the partition function. The law of the retained coordinates of a configuration
under the Gibbs probability has density `Z⁻¹ e^{-H₁ - H̃}` with respect to Lebesgue measure on the
retained chamber, restricted to the strip `0 ≤ z₀ < 1`. Here `H₁` is the retained energy and `H̃`
the block energy of `BlockEnergies.lean`.

The proof moves the integral to the Euclidean fundamental region, changes variables by the
measure-preserving block lift, and applies Fubini. For a fixed retained point `z`, the fiber
integral of `e^{-H₂}` equals `e^{-H̃(z)}`, by the definition of `H̃` and the positivity of the
fiber integral from `ConvexityExterior.lean`. The only external input is the Prékopa–Leindler
inequality `Riesz1.External.PrekopaLeindler`, passed as an explicit hypothesis.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter

open scoped ENNReal

namespace Riesz1

/-- The retained coordinates of a configuration: the entries at the retained labels. -/
def retainedCoord {N : ℕ+} {m n : ℕ} (e : Fin m ⊕ Fin n ≃ Fin (N : ℕ)) (X : Configuration N) :
    EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 (fun a => X.val (e (Sum.inl a)))

/-! ### Auxiliary facts about the Gibbs density and the block lift -/

/-- The Gibbs density on the Euclidean space, in a measurable version. It equals
`exp(-hsPairExpression χ)` on the chamber, which contains the fundamental region. -/
theorem blockDensity_exists_kk {N : ℕ+} {c : ℝ} (χ : HsPairPotentials N c) :
    ∃ kk : EuclideanSpace ℝ (Fin (N : ℕ)) → ENNReal, Measurable kk ∧
      ∀ x ∈ hsChamber N, kk x = ENNReal.ofReal (Real.exp (-hsPairExpression χ x)) := by
  classical
  refine ⟨(hsChamber N).piecewise (fun x => ENNReal.ofReal (Real.exp (-hsPairExpression χ x)))
    (fun _ => 0), ?_, fun x hx => Set.piecewise_eq_of_mem _ _ _ hx⟩
  apply ContinuousOn.measurable_piecewise
  · exact ENNReal.continuous_ofReal.comp_continuousOn
      (Real.continuous_exp.comp_continuousOn (hsPairExpression_contDiffOn χ).continuousOn.neg)
  · exact continuousOn_const
  · exact (isOpen_hsChamber N).measurableSet

theorem blockDensity_continuous_retained {m n N : ℕ} (e : Fin m ⊕ Fin n ≃ Fin N) :
    Continuous fun x : EuclideanSpace ℝ (Fin N) =>
      (WithLp.toLp 2 (fun a => x (e (Sum.inl a))) : EuclideanSpace ℝ (Fin m)) :=
  (PiLp.continuous_toLp 2 _).comp
    (continuous_pi fun a => PiLp.continuous_apply 2 _ (e (Sum.inl a)))

theorem blockDensity_continuous_retainedCoord {N : ℕ+} {m n : ℕ}
    (e : Fin m ⊕ Fin n ≃ Fin (N : ℕ)) : Continuous (retainedCoord e) :=
  (PiLp.continuous_toLp 2 _).comp
    (continuous_pi fun a => (continuous_apply (e (Sum.inl a))).comp continuous_subtype_val)

/-- The retained block of a lift is the retained part of the pair. -/
theorem blockDensity_retained_blockLift {m n N : ℕ} (e : Fin m ⊕ Fin n ≃ Fin N)
    (p : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) :
    (WithLp.toLp 2 (fun a => blockLift e p (e (Sum.inl a))) : EuclideanSpace ℝ (Fin m)) = p.1 := by
  ext a
  exact blockLift_inl e p a

/-- A lift lies in the fundamental region exactly when it lies in the chamber and its first
retained coordinate lies in `[0, 1)`. -/
theorem blockDensity_mem_region {N : ℕ+} {m n : ℕ} (e : Fin m ⊕ Fin n ≃ Fin (N : ℕ))
    (hm : 0 < m) (he0 : e (Sum.inl ⟨0, hm⟩) = ⟨0, N.pos⟩)
    (p : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) :
    blockLift e p ∈ hsFundamentalRegion N ↔
      blockLift e p ∈ hsChamber N ∧ 0 ≤ p.1 ⟨0, hm⟩ ∧ p.1 ⟨0, hm⟩ < 1 := by
  have h0 : blockLift e p ⟨0, N.pos⟩ = p.1 ⟨0, hm⟩ := by
    rw [← he0, blockLift_inl]
  change (blockLift e p ∈ hsChamber N ∧ 0 ≤ blockLift e p ⟨0, N.pos⟩ ∧
    blockLift e p ⟨0, N.pos⟩ < 1) ↔ _
  rw [h0]

/-- For `z` in the retained chamber, the exterior integral of the Gibbs density over the fiber
above `z` is the block energy factor `e^{-H̃(z)}`, times the constant `a`. -/
theorem blockDensity_fiber_lintegral (hPL : External.PrekopaLeindler) {N : ℕ+} {c : ℝ}
    (χ : HsPairPotentials N c) (hc : 0 < c) {m n : ℕ} (e : Fin m ⊕ Fin n ≃ Fin (N : ℕ))
    (hmono : StrictMono fun a => e (Sum.inl a)) (hm : 0 < m)
    (he0 : e (Sum.inl ⟨0, hm⟩) = ⟨0, N.pos⟩) {z : EuclideanSpace ℝ (Fin m)}
    (hz : z ∈ retainedChamber m) (a : ENNReal) {kk : EuclideanSpace ℝ (Fin (N : ℕ)) → ENNReal}
    (hkm : Measurable kk)
    (hkk : ∀ x ∈ hsChamber N, kk x = ENNReal.ofReal (Real.exp (-hsPairExpression χ x))) :
    ∫⁻ y in {y : EuclideanSpace ℝ (Fin n) | blockLift e (z, y) ∈ hsChamber N},
        a * kk (blockLift e (z, y)) =
      a * ENNReal.ofReal (Real.exp (-(blockRetainedEnergy χ e z + blockTilde χ e z))) := by
  obtain ⟨hint, hpos⟩ := fiber_integrable_pos hPL χ hc e hmono hm he0 hz
  have hT : MeasurableSet {y : EuclideanSpace ℝ (Fin n) | blockLift e (z, y) ∈ hsChamber N} :=
    (isOpen_fiber e z).measurableSet
  have hmeas : Measurable fun y : EuclideanSpace ℝ (Fin n) => kk (blockLift e (z, y)) :=
    hkm.comp ((measurable_blockLift e).comp measurable_prodMk_left)
  -- The pointwise factorization of the Gibbs density on the fiber.
  have hsplit : ∀ y : EuclideanSpace ℝ (Fin n), blockLift e (z, y) ∈ hsChamber N →
      kk (blockLift e (z, y)) = ENNReal.ofReal (Real.exp (-blockRetainedEnergy χ e z)) *
        ENNReal.ofReal (Real.exp (-blockExteriorEnergy χ e (z, y))) := by
    intro y hy
    have hexp : -hsPairExpression χ (blockLift e (z, y)) =
        -blockRetainedEnergy χ e z + -blockExteriorEnergy χ e (z, y) := by
      simp only [blockExteriorEnergy]
      ring
    rw [hkk _ hy, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, hexp]
  -- The block energy is the negative logarithm of the fiber integral.
  have hexpT : Real.exp (-blockTilde χ e z) =
      ∫ y in {y : EuclideanSpace ℝ (Fin n) | blockLift e (z, y) ∈ hsChamber N},
        Real.exp (-blockExteriorEnergy χ e (z, y)) := by
    unfold blockTilde
    rw [neg_neg, Real.exp_log hpos]
  calc ∫⁻ y in {y : EuclideanSpace ℝ (Fin n) | blockLift e (z, y) ∈ hsChamber N},
        a * kk (blockLift e (z, y))
      = a * ∫⁻ y in {y : EuclideanSpace ℝ (Fin n) | blockLift e (z, y) ∈ hsChamber N},
          kk (blockLift e (z, y)) := lintegral_const_mul a hmeas
    _ = a * ∫⁻ y in {y : EuclideanSpace ℝ (Fin n) | blockLift e (z, y) ∈ hsChamber N},
          (ENNReal.ofReal (Real.exp (-blockRetainedEnergy χ e z)) *
            ENNReal.ofReal (Real.exp (-blockExteriorEnergy χ e (z, y)))) :=
        congrArg (fun t => a * t) (setLIntegral_congr_fun hT hsplit)
    _ = a * (ENNReal.ofReal (Real.exp (-blockRetainedEnergy χ e z)) *
          ∫⁻ y in {y : EuclideanSpace ℝ (Fin n) | blockLift e (z, y) ∈ hsChamber N},
            ENNReal.ofReal (Real.exp (-blockExteriorEnergy χ e (z, y)))) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = a * (ENNReal.ofReal (Real.exp (-blockRetainedEnergy χ e z)) *
          ENNReal.ofReal (∫ y in {y : EuclideanSpace ℝ (Fin n) | blockLift e (z, y) ∈ hsChamber N},
            Real.exp (-blockExteriorEnergy χ e (z, y)))) := by
        rw [ofReal_integral_eq_lintegral_ofReal hint
          (Filter.Eventually.of_forall fun y => (Real.exp_pos _).le)]
    _ = a * ENNReal.ofReal (Real.exp (-(blockRetainedEnergy χ e z + blockTilde χ e z))) := by
        rw [neg_add, Real.exp_add, hexpT, ENNReal.ofReal_mul (Real.exp_pos _).le]

/-! ### The law of the retained coordinates -/

/-- The retained coordinates of a configuration have, under the Gibbs probability, the density
`Z⁻¹ e^{-H₁ - H̃}` on the retained chamber within the strip `0 ≤ z₀ < 1`. -/
theorem hsGibbs_retainedCoord_lintegral {N : ℕ+} {c : ℝ} (χ : HsPairPotentials N c) (hc : 0 < c)
    {m n : ℕ} (e : Fin m ⊕ Fin n ≃ Fin (N : ℕ)) (hmono : StrictMono fun a => e (Sum.inl a))
    (hm : 0 < m) (he0 : e (Sum.inl ⟨0, hm⟩) = ⟨0, N.pos⟩)
    (hPL : External.PrekopaLeindler)
    (g : EuclideanSpace ℝ (Fin m) → ENNReal) (hg : Measurable g) :
    ∫⁻ X, g (retainedCoord e X) ∂(hsGibbsProbability χ hc : Measure (Configuration N)) =
      (hsPartitionFunction χ)⁻¹ *
        ∫⁻ z in retainedChamber m ∩ {z | 0 ≤ z ⟨0, hm⟩ ∧ z ⟨0, hm⟩ < 1},
          g z * ENNReal.ofReal (Real.exp (-(blockRetainedEnergy χ e z + blockTilde χ e z))) := by
  obtain ⟨kk, hkm, hkk⟩ := blockDensity_exists_kk χ
  -- The integrand on the Euclidean fundamental region, and the integrand on the lifted pairs.
  obtain ⟨Ψ, hΨdef⟩ : ∃ Ψ : EuclideanSpace ℝ (Fin (N : ℕ)) → ENNReal,
      Ψ = fun x => g (WithLp.toLp 2 (fun a => x (e (Sum.inl a)))) * kk x := ⟨_, rfl⟩
  obtain ⟨F, hFdef⟩ : ∃ F : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n) → ENNReal,
      F = (blockLift e ⁻¹' hsFundamentalRegion N).indicator
        (fun p => g p.1 * kk (blockLift e p)) := ⟨_, rfl⟩
  -- Measurability.
  have hR : MeasurableSet (hsFundamentalRegion N) := by
    rw [hsFundamentalRegion_eq_preimage]
    exact (measurableSet_orderedDomain N).preimage
      (PiLp.volume_preserving_ofLp (Fin (N : ℕ))).measurable
  have hΨm : Measurable Ψ := by
    rw [hΨdef]
    exact (hg.comp (blockDensity_continuous_retained e).measurable).mul hkm
  have hΦm : Measurable fun p : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n) =>
      g p.1 * kk (blockLift e p) :=
    (hg.comp measurable_fst).mul (hkm.comp (measurable_blockLift e))
  have hFm : Measurable F := by
    rw [hFdef]
    exact hΦm.indicator (hR.preimage (measurable_blockLift e))
  have hhm : Measurable fun X : Configuration N =>
      ENNReal.ofReal (Real.exp (-hsFundamentalHamiltonian χ X)) :=
    (ENNReal.continuous_ofReal.comp
      (Real.continuous_exp.comp (continuous_hsFundamentalHamiltonian χ).neg)).measurable
  have hgm : Measurable fun X : Configuration N => g (retainedCoord e X) :=
    hg.comp (blockDensity_continuous_retainedCoord e).measurable
  have hA_meas : MeasurableSet
      (retainedChamber m ∩ {z : EuclideanSpace ℝ (Fin m) | 0 ≤ z ⟨0, hm⟩ ∧ z ⟨0, hm⟩ < 1}) := by
    refine (isOpen_retainedChamber m).measurableSet.inter ?_
    have hcoord : Measurable fun z : EuclideanSpace ℝ (Fin m) => z ⟨0, hm⟩ :=
      (PiLp.continuous_apply 2 _ _).measurable
    exact (measurableSet_le measurable_const hcoord).inter
      (measurableSet_lt hcoord measurable_const)
  -- Pointwise identity on the configurations.
  have hX : ∀ X : Configuration N,
      (WithLp.toLp 2 X.val : EuclideanSpace ℝ (Fin (N : ℕ))) ∈ hsChamber N :=
    fun X => ⟨X.property.1, fun i => X.property.2.2.2 i⟩
  have hcfg : ∀ X : Configuration N,
      ENNReal.ofReal (Real.exp (-hsFundamentalHamiltonian χ X)) * g (retainedCoord e X) =
        Ψ (WithLp.toLp 2 X.val) := by
    intro X
    rw [hΨdef]
    show ENNReal.ofReal (Real.exp (-hsFundamentalHamiltonian χ X)) * g (retainedCoord e X) =
      g (WithLp.toLp 2 (fun a => (WithLp.toLp 2 X.val : EuclideanSpace ℝ (Fin (N : ℕ)))
        (e (Sum.inl a)))) * kk (WithLp.toLp 2 X.val)
    rw [hkk _ (hX X), mul_comm]
    rfl
  -- The indicator on the lifted pairs agrees with the integrand of the fundamental region.
  have hF_pt : ∀ p : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n),
      (hsFundamentalRegion N).indicator Ψ (blockLift e p) = F p := by
    intro p
    rw [hFdef]
    by_cases hp : blockLift e p ∈ hsFundamentalRegion N
    · have hp' : p ∈ blockLift e ⁻¹' hsFundamentalRegion N := hp
      rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp', hΨdef]
      dsimp only
      rw [blockDensity_retained_blockLift]
    · have hp' : p ∉ blockLift e ⁻¹' hsFundamentalRegion N := hp
      rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hp']
  -- A lifted pair lies over the retained chamber in the strip.
  have hnot : ∀ (z : EuclideanSpace ℝ (Fin m)) (y : EuclideanSpace ℝ (Fin n)),
      (z, y) ∈ blockLift e ⁻¹' hsFundamentalRegion N →
        z ∈ retainedChamber m ∩ {z : EuclideanSpace ℝ (Fin m) | 0 ≤ z ⟨0, hm⟩ ∧ z ⟨0, hm⟩ < 1} := by
    intro z y h
    obtain ⟨hC, hS0, hS1⟩ := (blockDensity_mem_region e hm he0 (z, y)).1 h
    have hfst : z ∈ Prod.fst '' liftChamber e := ⟨(z, y), hC, rfl⟩
    rw [fst_image_liftChamber e hmono hm he0] at hfst
    exact ⟨hfst, hS0, hS1⟩
  -- The fiber integral over each retained point.
  have hz_pt : ∀ z : EuclideanSpace ℝ (Fin m),
      ∫⁻ y, F (z, y) = (retainedChamber m ∩
          {z : EuclideanSpace ℝ (Fin m) | 0 ≤ z ⟨0, hm⟩ ∧ z ⟨0, hm⟩ < 1}).indicator
        (fun z => g z * ENNReal.ofReal (Real.exp (-(blockRetainedEnergy χ e z +
          blockTilde χ e z)))) z := by
    intro z
    by_cases hz : z ∈ retainedChamber m ∩
        {z : EuclideanSpace ℝ (Fin m) | 0 ≤ z ⟨0, hm⟩ ∧ z ⟨0, hm⟩ < 1}
    · rw [Set.indicator_of_mem hz]
      have hzC : z ∈ retainedChamber m := hz.1
      have hzS0 : 0 ≤ z ⟨0, hm⟩ := hz.2.1
      have hzS1 : z ⟨0, hm⟩ < 1 := hz.2.2
      have hT : MeasurableSet {y : EuclideanSpace ℝ (Fin n) | blockLift e (z, y) ∈ hsChamber N} :=
        (isOpen_fiber e z).measurableSet
      have hfun : (fun y => F (z, y)) = {y : EuclideanSpace ℝ (Fin n) |
          blockLift e (z, y) ∈ hsChamber N}.indicator
            (fun y => g z * kk (blockLift e (z, y))) := by
        funext y
        rw [hFdef]
        by_cases hy : blockLift e (z, y) ∈ hsChamber N
        · have hmem : (z, y) ∈ blockLift e ⁻¹' hsFundamentalRegion N :=
            (blockDensity_mem_region e hm he0 (z, y)).2 ⟨hy, hzS0, hzS1⟩
          have hy' : y ∈ {y : EuclideanSpace ℝ (Fin n) | blockLift e (z, y) ∈ hsChamber N} := hy
          rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hy']
        · have hmem : (z, y) ∉ blockLift e ⁻¹' hsFundamentalRegion N :=
            fun h => hy ((blockDensity_mem_region e hm he0 (z, y)).1 h).1
          have hy' : y ∉ {y : EuclideanSpace ℝ (Fin n) | blockLift e (z, y) ∈ hsChamber N} := hy
          rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hy']
      rw [hfun, lintegral_indicator hT]
      exact blockDensity_fiber_lintegral hPL χ hc e hmono hm he0 hzC (g z) hkm hkk
    · rw [Set.indicator_of_notMem hz]
      have hzero : ∀ y : EuclideanSpace ℝ (Fin n), F (z, y) = 0 := fun y => by
        rw [hFdef]
        exact Set.indicator_of_notMem (fun h => hz (hnot z y h)) _
      simp only [hzero, lintegral_zero]
  -- The chain of equalities.
  have key : ∫⁻ X : Configuration N,
        ENNReal.ofReal (Real.exp (-hsFundamentalHamiltonian χ X)) * g (retainedCoord e X)
          ∂configurationVolume N =
      ∫⁻ z in retainedChamber m ∩ {z : EuclideanSpace ℝ (Fin m) | 0 ≤ z ⟨0, hm⟩ ∧ z ⟨0, hm⟩ < 1},
        g z * ENNReal.ofReal (Real.exp (-(blockRetainedEnergy χ e z + blockTilde χ e z))) := by
    calc ∫⁻ X : Configuration N,
          ENNReal.ofReal (Real.exp (-hsFundamentalHamiltonian χ X)) * g (retainedCoord e X)
            ∂configurationVolume N
        = ∫⁻ X : Configuration N, Ψ (WithLp.toLp 2 X.val) ∂configurationVolume N :=
          lintegral_congr hcfg
      _ = ∫⁻ x in hsFundamentalRegion N, Ψ x := by
          have h := hsFundamentalRegion_lintegral N (fun v => Ψ (WithLp.toLp 2 v))
            (hΨm.comp (PiLp.continuous_toLp 2 _).measurable)
          simp only [WithLp.toLp_ofLp] at h
          exact h.symm
      _ = ∫⁻ x, (hsFundamentalRegion N).indicator Ψ x := (lintegral_indicator hR Ψ).symm
      _ = ∫⁻ p, (hsFundamentalRegion N).indicator Ψ (blockLift e p) :=
          ((measurePreserving_blockLift e).lintegral_comp (hΨm.indicator hR)).symm
      _ = ∫⁻ p, F p := lintegral_congr hF_pt
      _ = ∫⁻ z, ∫⁻ y, F (z, y) := by
          rw [Measure.volume_eq_prod]
          exact lintegral_prod F hFm.aemeasurable
      _ = ∫⁻ z, (retainedChamber m ∩
            {z : EuclideanSpace ℝ (Fin m) | 0 ≤ z ⟨0, hm⟩ ∧ z ⟨0, hm⟩ < 1}).indicator
          (fun z => g z * ENNReal.ofReal (Real.exp (-(blockRetainedEnergy χ e z +
            blockTilde χ e z)))) z := lintegral_congr hz_pt
      _ = ∫⁻ z in retainedChamber m ∩
            {z : EuclideanSpace ℝ (Fin m) | 0 ≤ z ⟨0, hm⟩ ∧ z ⟨0, hm⟩ < 1},
          g z * ENNReal.ofReal (Real.exp (-(blockRetainedEnergy χ e z + blockTilde χ e z))) :=
          lintegral_indicator hA_meas _
  -- The Gibbs probability is the normalized fundamental weight.
  rw [show ((hsGibbsProbability χ hc : ProbabilityMeasure (Configuration N)) :
      Measure (Configuration N)) = (hsPartitionFunction χ)⁻¹ •
        (configurationVolume N).withDensity
          (fun X => ENNReal.ofReal (Real.exp (-hsFundamentalHamiltonian χ X))) from rfl]
  rw [lintegral_smul_measure, smul_eq_mul,
    lintegral_withDensity_eq_lintegral_mul _ hhm hgm]
  exact congrArg (fun t => (hsPartitionFunction χ)⁻¹ * t) key

end Riesz1

end
end
