/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.GradientConvergenceVector
public import Riesz1.HelfferSjostrand.NonGradientGap
public import Riesz1.HelfferSjostrand.BoundaryCoreAnchoredGeometry
public import Riesz1.HelfferSjostrand.BoundaryCoreQuotient
public import Riesz1.HelfferSjostrand.PoissonEquation
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Riesz1.Externals.PrekopaLeindlerProof

/-! # Existence and representation for the general Gibbs measure

Scalar operator-core approximation and the commutator place the scalar Poisson
gradient in the vector energy space. Its weak equation and normalization give
uniqueness and the quadratic minimum. Testing the scalar equation represents
covariances. Rotation invariance preserves dependence on the cyclic gaps and
forces the weak common-rotation derivative to vanish.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology InnerProductSpace
open scoped ContDiff Laplacian

namespace Riesz1.Internal

variable {N : ℕ+} {c : ℝ}

variable (χ : HsPairPotentials N c) (hN : 2 ≤ (N : ℕ)) (hc : 0 < c)

local notation "μ" => (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))

local instance : NormedAddCommGroup (HsSobolev μ) := inferInstance
local instance : NormedSpace ℝ (HsSobolev μ) := inferInstance
local instance : InnerProductSpace ℝ (HsSobolev μ) := inferInstance
local instance : InnerProductSpace ℝ (PiLp 2 (fun _ : Fin (N : ℕ) => HsSobolev μ)) := inferInstance
local instance : NormedAddCommGroup (HsVectorJet μ) := inferInstance
local instance : NormedSpace ℝ (HsVectorJet μ) := inferInstance
local instance : InnerProductSpace ℝ (HsVectorJet μ) := inferInstance
local instance : NormedAddCommGroup (HsVectorSobolev χ hN hc μ) := inferInstance
local instance : NormedSpace ℝ (HsVectorSobolev χ hN hc μ) := inferInstance
local instance : InnerProductSpace ℝ (HsVectorSobolev χ hN hc μ) := inferInstance

include hN

/-- Weighted integration by parts with a scalar test in an arbitrary direction. -/
private theorem hsExistence_directional (f : HsTestFunction N) (h : HsSobolev μ)
    (v : HsEuclidean N) :
    (∫ x, hsSmoothValue f.toFun x * inner ℝ (hsSobolevGradient μ h x) v ∂μ) =
      ∫ x, hsSobolevValue μ h x * hsSmoothValue (fun y =>
        f.toFun y * fderiv ℝ (hsPairExpression χ) y v - fderiv ℝ f.toFun y v) x ∂μ := by
  let ℓ := EuclideanSpace.proj (𝕜 := ℝ) (⟨0, N.pos⟩ : Fin (N : ℕ))
  let ψ := fun y => periodicCutoff (ℓ y) * f.toFun y
  have hψc : HasCompactSupport ψ :=
    hasCompactSupport_hsPeriodicCutoff_mul (f.tsupport_subset_chamber hN)
  have hψ : ContDiff ℝ ∞ ψ := (contDiff_periodicCutoff.comp ℓ.contDiff).mul f.smooth
  have hψU : tsupport ψ ⊆ hsChamber N := tsupport_mul_subset_right.trans
    (f.tsupport_subset_chamber hN)
  have hp (k : ℤ) (x : HsEuclidean N) :
      f.toFun (x + (k : ℝ) • hsRotationVector N) = f.toFun x := by
    rw [← hsTranslate_eq_add_rotation]
    exact f.periodic k x
  have hP : vectorPeriodize (hsRotationVector N) (hsRotationVector_ne_zero N) ψ hψc = f.toFun :=
    vectorPeriodize_periodicCutoff_mul (hsRotationVector_ne_zero N) ℓ
      (by simp [ℓ, hsRotationVector]) hp hψc
  have hi := hsSobolev_periodized_integrationByParts hN χ hc h hψ hψc hψU v
  dsimp only at hi
  rw [hP] at hi
  exact hi

/-- The weighted divergence coefficient of a vector test. -/
private def hsExistenceCoeff (u : HsVectorTest N) (x : HsConfiguration N) : ℝ :=
  ∑ i : Fin (N : ℕ), hsSmoothValue (fun y =>
    (u i).val y * fderiv ℝ (hsPairExpression χ) y (EuclideanSpace.single i 1) -
      fderiv ℝ (u i).val y (EuclideanSpace.single i 1)) x

/-- A directional weighted divergence coefficient is square integrable. -/
private theorem hsExistence_direction_mem (f : hsTestSubmodule N) (v : HsEuclidean N) :
    MemLp (hsSmoothValue (fun y => f.val y * fderiv ℝ (hsPairExpression χ) y v -
      fderiv ℝ f.val y v)) 2 μ :=
  memLp_hsLiftPoint (f := fun y => f.val y * fderiv ℝ (hsPairExpression χ) y v -
    fderiv ℝ f.val y v) μ 2
    (continuous_hsLocalCoefficient χ f.property.1
      ((hsGradientSourceOfTest f).tsupport_subset_chamber hN) v).continuousOn

/-- The weighted divergence of a vector test is square integrable. -/
private theorem hsExistence_coeff_mem (u : HsVectorTest N) : MemLp (hsExistenceCoeff χ u) 2 μ :=
  memLp_finsetSum Finset.univ (fun i _ =>
    hsExistence_direction_mem χ hN hc (u i) (EuclideanSpace.single i 1))

/-- The ordinary gradient pairing equals the weighted divergence pairing. -/
private theorem hsExistence_pairing (F : HsSobolev μ) (u : HsVectorTest N) :
    hsNonGradientPairing μ (hsSobolevGradient μ F) (hsVectorJet χ hN hc μ u) =
      inner ℝ (hsSobolevValue μ F) ((hsExistence_coeff_mem χ hN hc u).toLp
        (hsExistenceCoeff χ u)) := by
  rw [hsNonGradientPairing_eq_integral, poisson_inner_eq_integral]
  have hv (i : Fin (N : ℕ)) :
      (hsJetValue μ i (hsVectorJet χ hN hc μ u) : HsConfiguration N → ℝ) =ᵐ[μ]
        hsSmoothValue (u i).val := ((HsTestSubmodule.smoothOnClosure (u i).property).memLp_value μ).coeFn_toLp
  have hm (i : Fin (N : ℕ)) : MemLp (hsSmoothValue (fun y =>
      (u i).val y * fderiv ℝ (hsPairExpression χ) y (EuclideanSpace.single i 1) -
        fderiv ℝ (u i).val y (EuclideanSpace.single i 1))) 2 μ :=
    hsExistence_direction_mem χ hN hc (u i) (EuclideanSpace.single i 1)
  have hi (i : Fin (N : ℕ)) := hsExistence_directional χ hN hc (hsGradientSourceOfTest (u i)) F
    (EuclideanSpace.single i 1)
  have hl : (∫ x, ∑ i : Fin (N : ℕ), hsSobolevGradient μ F x i *
      hsJetValue μ i (hsVectorJet χ hN hc μ u) x ∂μ) =
      ∑ i : Fin (N : ℕ), ∫ x, hsSmoothValue (u i).val x *
        inner ℝ (hsSobolevGradient μ F x) (EuclideanSpace.single i 1) ∂μ := by
    calc
      _ = ∫ x, ∑ i : Fin (N : ℕ), hsSmoothValue (u i).val x *
          inner ℝ (hsSobolevGradient μ F x) (EuclideanSpace.single i 1) ∂μ := by
        apply integral_congr_ae
        filter_upwards [ae_all_iff.mpr hv] with x hx
        apply Finset.sum_congr rfl
        intro i _
        rw [hx i, EuclideanSpace.inner_single_right]
        simp only [starRingEnd_apply, star_trivial, one_mul]
        exact mul_comm (hsSobolevGradient μ F x i) (hsSmoothValue (u i).val x)
      _ = _ := integral_finsetSum Finset.univ (fun i _ =>
        ((HsTestSubmodule.smoothOnClosure (u i).property).memLp_value μ).integrable_mul
          ((Lp.memLp (hsSobolevGradient μ F)).inner_const (EuclideanSpace.single i 1)))
  rw [hl]
  change (∑ i, ∫ x, hsSmoothValue (hsGradientSourceOfTest (u i)).toFun x *
    inner ℝ (hsSobolevGradient μ F x) (EuclideanSpace.single i 1) ∂μ) = _
  simp_rw [hi]
  dsimp only [hsGradientSourceOfTest] at hi
  change (∑ i, ∫ x, hsSobolevValue μ F x * hsSmoothValue (fun y =>
    (u i).val y * fderiv ℝ (hsPairExpression χ) y (EuclideanSpace.single i 1) -
    fderiv ℝ (u i).val y (EuclideanSpace.single i 1)) x ∂μ) = _
  have hR (i : Fin (N : ℕ)) : Integrable (fun x => hsSobolevValue μ F x *
      hsSmoothValue (fun y => (u i).val y * fderiv ℝ (hsPairExpression χ) y
        (EuclideanSpace.single i 1) - fderiv ℝ (u i).val y (EuclideanSpace.single i 1)) x) μ :=
    (Lp.memLp (hsSobolevValue μ F)).integrable_mul (hm i)
  rw [← integral_finsetSum Finset.univ (fun i _ => hR i)]
  apply integral_congr_ae
  filter_upwards [(hsExistence_coeff_mem χ hN hc u).coeFn_toLp] with x hx
  rw [hx, hsExistenceCoeff, Finset.mul_sum]

/-- Constants pair to zero with weighted divergences. -/
private theorem hsExistence_center_coeff (F : Lp ℝ 2 μ) (u : HsVectorTest N) :
    inner ℝ (poissonCenter μ F) ((hsExistence_coeff_mem χ hN hc u).toLp (hsExistenceCoeff χ u)) =
      inner ℝ F ((hsExistence_coeff_mem χ hN hc u).toLp (hsExistenceCoeff χ u)) := by
  have hz := hsExistence_pairing χ hN hc (hsPoissonUnit μ) u
  rw [hsPoissonUnit_value, hsPoissonUnit_gradient, hsNonGradientPairing, map_zero,
    inner_zero_left] at hz
  rw [poissonCenter, inner_sub_left, real_inner_smul_left, ← hz, mul_zero, sub_zero]

/-- The Hessian contraction with a gradient is the coordinate commutator. -/
private theorem hsExistence_hessian (f : HsTestFunction N) {x : HsEuclidean N}
    (hx : x ∈ hsChamber N) (w : HsEuclidean N) :
    fderiv ℝ (fderiv ℝ (hsPairExpression χ)) x (gradient f.toFun x) w =
      ∑ i : Fin (N : ℕ),
        ((hsGradientTestDirection hN (hsLangevinTest hN χ f) (EuclideanSpace.single i 1)).toFun x -
          (hsLangevinTest hN χ (hsGradientTestDirection hN f (EuclideanSpace.single i 1))).toFun x) *
            w i := by
  have hH := (hsPairExpression_contDiffOn χ).contDiffAt ((isOpen_hsChamber N).mem_nhds hx)
  have hsym := hH.isSymmSndFDerivAt (by simp)
  rw [hsCommutator_linear_coordinates
    (fderiv ℝ (fderiv ℝ (hsPairExpression χ)) x (gradient f.toFun x)) w]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact (hsym _ _).trans
    (langevin_direction_commutator hH f.smooth (EuclideanSpace.single i 1)).symm

/-- The integrated commutator against an arbitrary vector test. -/
private theorem hsExistence_commutator (f : HsTestFunction N) (u : HsVectorTest N) :
    hsVectorSobolevForm χ hN hc μ
      (hsVectorJetElt χ hN hc μ (hsGradientTestTuple hN f)) (hsVectorJetElt χ hN hc μ u) =
      inner ℝ ((memLp_hsLangevin hN χ f μ).toLp (hsLangevin χ f))
        ((hsExistence_coeff_mem χ hN hc u).toLp (hsExistenceCoeff χ u)) := by
  let L := hsLangevinTest hN χ f
  let g (i : Fin (N : ℕ)) := hsGradientTestDirection hN f (EuclideanSpace.single i 1)
  let A (i : Fin (N : ℕ)) := hsLangevin χ (g i)
  let B (i : Fin (N : ℕ)) := hsSmoothValue (u i).val
  let C (i : Fin (N : ℕ)) := hsTestOnQuotient
    (hsGradientTestDirection hN L (EuclideanSpace.single i 1))
  let D (i : Fin (N : ℕ)) := fun y : HsConfiguration N =>
    inner ℝ (gradient (g i).toFun (hsLiftPoint N y)) (gradient (u i).val (hsLiftPoint N y))
  have hA (i) : MemLp (A i) 2 μ := memLp_hsLangevin hN χ (g i) μ
  have hB (i) : MemLp (B i) 2 μ := (HsTestSubmodule.smoothOnClosure (u i).property).memLp_value μ
  have hC (i) : MemLp (C i) 2 μ :=
    (hsGradientTestDirection hN L (EuclideanSpace.single i 1)).smoothOnClosure.memLp_value μ
  have hD (i) : Integrable (D i) μ := by
    have hi : Integrable (fun y => inner ℝ
      (hsSobolevGradient μ (hsSobolevOfSmooth μ ⟨(g i).toFun, (g i).smoothOnClosure⟩) y)
      (hsSobolevGradient μ (hsTestSobolev μ (u i)) y)) μ := L2.integrable_inner
      (hsSobolevGradient μ (hsSobolevOfSmooth μ ⟨(g i).toFun, (g i).smoothOnClosure⟩))
      (hsSobolevGradient μ (hsTestSobolev μ (u i)))
    apply hi.congr
    filter_upwards [((g i).smoothOnClosure.memLp_gradient μ).coeFn_toLp,
      hsSobolevGradient_hsTestSobolev_ae μ (u i)] with y hy hz
    change inner ℝ (((g i).smoothOnClosure.memLp_gradient μ).toLp _ y) _ = _
    rw [hy, hz]
    rfl
  have hab (i) : Integrable (fun y => A i y * B i y) μ := (hA i).integrable_mul (hB i)
  have hdiff (i : Fin (N : ℕ)) : Integrable (fun y => (C i y - A i y) * B i y) μ :=
    ((hC i).sub (hA i)).integrable_mul (hB i)
  have hi (i : Fin (N : ℕ)) : (∫ y, D i y ∂μ) = ∫ y, A i y * B i y ∂μ := by
    have h := hsIntegrationByParts_smooth hN χ hc (g i) (hsGradientSourceOfTest (u i))
    rw [hsGradient_dirichlet_tests] at h
    exact h.symm
  have hpoint (y : HsConfiguration N) :
      vectorFormIntegrand χ (hsGradientTestTuple hN f) u (hsLiftPoint N y) =
        (∑ i, D i y) + ∑ i, (C i y - A i y) * B i y := by
    unfold vectorFormIntegrand
    rw [hsTestVector_gradientTestTuple, hsExistence_hessian χ hN f (hsLiftPoint_mem_chamber N y)]
    rfl
  have hpair : hsNonGradientPairing μ
      (hsSobolevGradient μ (hsSobolevOfSmooth μ ⟨L.toFun, L.smoothOnClosure⟩))
      (hsVectorJet χ hN hc μ u) = ∫ y, ∑ i, C i y * B i y ∂μ := by
    rw [hsNonGradientPairing_eq_integral]
    apply integral_congr_ae
    have hv (i : Fin (N : ℕ)) :
        (hsJetValue μ i (hsVectorJet χ hN hc μ u) : HsConfiguration N → ℝ) =ᵐ[μ] B i :=
      (hB i).coeFn_toLp
    filter_upwards [(L.smoothOnClosure.memLp_gradient μ).coeFn_toLp, ae_all_iff.mpr hv] with y hy hz
    change (∑ i, ((L.smoothOnClosure.memLp_gradient μ).toLp _ y) i * _) = _
    rw [hy]
    apply Finset.sum_congr rfl
    intro i _
    rw [hz i]
    change gradient L.toFun (hsLiftPoint N y) i * _ = _
    rw [← hsGradientTestTuple_apply hN L]
    rfl
  have hLval : hsSobolevValue μ (hsSobolevOfSmooth μ ⟨L.toFun, L.smoothOnClosure⟩) =
      (memLp_hsLangevin hN χ f μ).toLp (hsLangevin χ f) := by
    apply Lp.ext
    exact (L.smoothOnClosure.memLp_value μ).coeFn_toLp.trans
      (memLp_hsLangevin hN χ f μ).coeFn_toLp.symm
  rw [← hLval]
  rw [← hsExistence_pairing χ hN hc (hsSobolevOfSmooth μ ⟨L.toFun, L.smoothOnClosure⟩) u, hpair]
  rw [hsVectorSobolevForm_jet, vectorForm]
  simp_rw [hpoint]
  rw [integral_add (integrable_finsetSum Finset.univ (fun i _ => hD i))
    (integrable_finsetSum Finset.univ (fun i _ => hdiff i)),
    integral_finsetSum Finset.univ (fun i _ => hD i)]
  simp_rw [hi]
  rw [← integral_finsetSum Finset.univ (fun i _ => hab i),
    ← integral_add (integrable_finsetSum Finset.univ (fun i _ => hab i))
      (integrable_finsetSum Finset.univ (fun i _ => hdiff i))]
  apply integral_congr_ae
  filter_upwards with y
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

end Riesz1.Internal

namespace Riesz1.Internal

variable {N : ℕ+} {c C_N : ℝ}
variable (χ : HsPairPotentials N c) (hN : 2 ≤ (N : ℕ)) (hc : 0 < c)

local notation "μ" => (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))

/-- Every scalar Poisson graph point admits collision-free test approximation. -/
private theorem hsExistence_approx (hadm : HsAdmissible χ C_N) (F : Lp ℝ 2 μ)
    {φ : HsSobolev μ} (hφ : HsPoissonSolves χ hc F φ) :
    ∃ f : ℕ → HsTestFunction N,
      Tendsto (fun k => hsSobolevValue μ
        (hsSobolevOfSmooth μ ⟨(f k).toFun, (f k).smoothOnClosure⟩)) atTop (𝓝 (hsSobolevValue μ φ)) ∧
      Tendsto (fun k => (memLp_hsLangevin hN χ (f k) μ).toLp (hsLangevin χ (f k)))
        atTop (𝓝 (poissonCenter μ F)) := by
  have hgraph : (hsTestL2Operator χ hc).graph.topologicalClosure =
      (hsNeumannL2Operator χ hc).graph := by
    rw [(hsTestL2Operator_isClosable χ hc).graph_closure_eq_closure_graph,
      (scalar_boundary_core_L3219_quotient_real χ hc hadm).1]
  have hmem : (hsSobolevValue μ φ, poissonCenter μ F) ∈
      closure ((hsTestL2Operator χ hc).graph : Set (Lp ℝ 2 μ × Lp ℝ 2 μ)) := by
    rw [← Submodule.topologicalClosure_coe, hgraph]
    obtain ⟨hd, he⟩ := hφ
    rw [← he]
    exact hsNeumannL2Operator_on_domain χ hc ⟨φ, hd⟩
  obtain ⟨p, hp, hlim⟩ := mem_closure_iff_seq_limit.mp hmem
  have hpt (k : ℕ) : ∃ f : HsTestFunction N,
      hsSobolevValue μ (hsSobolevOfSmooth μ ⟨f.toFun, f.smoothOnClosure⟩) = (p k).1 ∧
      (memLp_hsLangevin hN χ f μ).toLp (hsLangevin χ f) = (p k).2 := by
    obtain ⟨h, hh1, hh2⟩ := (LinearPMap.mem_graph_iff _).mp (hp k)
    have hd : (h : Lp ℝ 2 μ) ∈ hsTestL2Domain μ := (hsTestL2Operator_domain hN χ hc).le h.2
    obtain ⟨f, hf⟩ := (mem_hsTestL2Domain μ _).mp hd
    have hs : hsGradientSourceDomainLin χ hN hc (hsGradientTestOfSource f) = h := Subtype.ext hf
    refine ⟨f, hf.trans hh1, ?_⟩
    rw [← hsGradientSourceOperatorLin_of_source χ hN hc f]
    change hsTestL2Operator χ hc (hsGradientSourceDomainLin χ hN hc (hsGradientTestOfSource f)) = _
    rw [hs]
    exact hh2
  choose f hf1 hf2 using hpt
  exact ⟨f, Tendsto.congr (fun k => (hf1 k).symm) ((continuous_fst.tendsto _).comp hlim),
    Tendsto.congr (fun k => (hf2 k).symm) ((continuous_snd.tendsto _).comp hlim)⟩

/-- The vector equation extends from test tuples by density in the energy norm. -/
private theorem hsExistence_weak_of_tests (v : Lp (HsEuclidean N) 2 μ)
    (G : HsVectorSobolev χ hN hc μ)
    (ht : ∀ u : HsVectorTest N,
      hsVectorSobolevForm χ hN hc μ G (hsVectorJetElt χ hN hc μ u) =
        hsNonGradientPairing μ v (hsVectorJet χ hN hc μ u)) :
    HsNonGradientSolves χ hN hc v G := by
  intro w
  have hw : w.val ∈ closure (LinearMap.range (hsVectorJetLin χ hN hc μ) : Set (HsVectorJet μ)) := by
    rw [← Submodule.topologicalClosure_coe]
    exact w.property
  obtain ⟨p, hp, hlim⟩ := mem_closure_iff_seq_limit.mp hw
  choose u hu using hp
  have hseq : Tendsto (fun k => hsVectorJetElt χ hN hc μ (u k)) atTop (𝓝 w) := by
    apply tendsto_subtype_rng.mpr
    exact Tendsto.congr (fun k => (hu k).symm) hlim
  have hL := (((hsNonGradientFullBilinear χ hN hc μ G).continuous.tendsto w).comp hseq)
  have hR : Continuous (fun z : HsVectorSobolev χ hN hc μ =>
      inner ℝ (hsL2Coordinates μ v) (hsNonGradientValues μ z.val)) :=
    continuous_const.inner ((hsNonGradientValues μ).continuous.comp
      (hsVectorSobolevSubmodule χ hN hc μ).subtypeL.continuous)
  have hR' := (hR.tendsto w).comp hseq
  have he (k : ℕ) : hsNonGradientFullBilinear χ hN hc μ G (hsVectorJetElt χ hN hc μ (u k)) =
      hsNonGradientPairing μ v (hsVectorJet χ hN hc μ (u k)) :=
    (hsNonGradientFullBilinear_eq χ hN hc μ _ _).trans (ht (u k))
  change Tendsto (fun k => hsNonGradientFullBilinear χ hN hc μ G
    (hsVectorJetElt χ hN hc μ (u k))) atTop
      (𝓝 (hsNonGradientFullBilinear χ hN hc μ G w)) at hL
  change Tendsto (fun k => hsNonGradientPairing μ v (hsVectorJet χ hN hc μ (u k)))
    atTop (𝓝 (hsNonGradientPairing μ v w.val)) at hR'
  exact (hsNonGradientFullBilinear_eq χ hN hc μ G w).symm.trans
    (tendsto_nhds_unique hL (Tendsto.congr (fun k => (he k).symm) hR'))

/-- The operator graph limit satisfies the commutator identity on every vector test. -/
private theorem hsExistence_limit_weak (F : HsSobolev μ) (f : ℕ → HsTestFunction N)
    (G : HsVectorSobolev χ hN hc μ)
    (ha : Tendsto (fun k => (memLp_hsLangevin hN χ (f k) μ).toLp (hsLangevin χ (f k)))
      atTop (𝓝 (poissonCenter μ (hsSobolevValue μ F))))
    (hG : Tendsto (fun k => hsVectorJetElt χ hN hc μ (hsGradientTestTuple hN (f k)))
      atTop (𝓝 G)) : HsNonGradientSolves χ hN hc (hsSobolevGradient μ F) G := by
  apply hsExistence_weak_of_tests χ hN hc
  intro u
  let a := (hsExistence_coeff_mem χ hN hc u).toLp (hsExistenceCoeff χ u)
  have hL := (((hsNonGradientFullBilinear χ hN hc μ).flip
    (hsVectorJetElt χ hN hc μ u)).continuous.tendsto G).comp hG
  have hR : Tendsto (fun k => inner ℝ
      ((memLp_hsLangevin hN χ (f k) μ).toLp (hsLangevin χ (f k))) a)
      atTop (𝓝 (inner ℝ (poissonCenter μ (hsSobolevValue μ F)) a)) :=
    ha.inner tendsto_const_nhds
  have hseq (k : ℕ) : hsNonGradientFullBilinear χ hN hc μ
      (hsVectorJetElt χ hN hc μ (hsGradientTestTuple hN (f k)))
      (hsVectorJetElt χ hN hc μ u) =
      inner ℝ ((memLp_hsLangevin hN χ (f k) μ).toLp (hsLangevin χ (f k))) a :=
    (hsNonGradientFullBilinear_eq χ hN hc μ _ _).trans (hsExistence_commutator χ hN hc (f k) u)
  change Tendsto (fun k => hsNonGradientFullBilinear χ hN hc μ
    (hsVectorJetElt χ hN hc μ (hsGradientTestTuple hN (f k)))
    (hsVectorJetElt χ hN hc μ u)) atTop
      (𝓝 (hsNonGradientFullBilinear χ hN hc μ G (hsVectorJetElt χ hN hc μ u))) at hL
  have he := tendsto_nhds_unique hL (Tendsto.congr (fun k => (hseq k).symm) hR)
  rw [hsNonGradientFullBilinear_eq] at he
  exact he.trans ((hsExistence_center_coeff χ hN hc (hsSobolevValue μ F) u).trans
    (hsExistence_pairing χ hN hc F u).symm)

/-- The gradient of a scalar solution belongs to the vector form domain and solves its equation. -/
private theorem hsExistence_gradient_weak (hadm : HsAdmissible χ C_N) (F : HsSobolev μ)
    {φ : HsSobolev μ} (hφ : HsPoissonSolves χ hc (hsSobolevValue μ F) φ) :
    ∃ G : HsVectorSobolev χ hN hc μ,
      (∀ i : Fin (N : ℕ), hsJetValue μ i G.val =
        (EuclideanSpace.proj (𝕜 := ℝ) i).compLpL 2 μ (hsSobolevGradient μ φ)) ∧
      HsNonGradientSolves χ hN hc (hsSobolevGradient μ F) G := by
  obtain ⟨f, hv, ha⟩ := hsExistence_approx χ hN hc hadm (hsSobolevValue μ F) hφ
  have hg := hsGradient_graph_convergence hN χ hc f
    (hsSobolevValue μ φ) (poissonCenter μ (hsSobolevValue μ F)) hv ha
  dsimp only at hg
  obtain ⟨φ', G, hval, -, hvalues, hG⟩ := hg
  have hφ' : φ' = φ := hsSobolevValue_injective χ hc hval
  subst φ'
  exact ⟨G, hvalues, hsExistence_limit_weak χ hN hc F f G ha hG⟩

end Riesz1.Internal

namespace Riesz1.Internal

variable {N : ℕ+} {c C_N : ℝ}
variable (χ : HsPairPotentials N c) (hN : 2 ≤ (N : ℕ)) (hc : 0 < c)

local notation "μ" => (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))

local instance : NormedAddCommGroup (HsSobolev μ) := inferInstance
local instance : NormedSpace ℝ (HsSobolev μ) := inferInstance
local instance : InnerProductSpace ℝ (HsSobolev μ) := inferInstance
local instance : InnerProductSpace ℝ (PiLp 2 (fun _ : Fin (N : ℕ) => HsSobolev μ)) := inferInstance
local instance : NormedAddCommGroup (HsVectorJet μ) := inferInstance
local instance : NormedSpace ℝ (HsVectorJet μ) := inferInstance
local instance : InnerProductSpace ℝ (HsVectorJet μ) := inferInstance
local instance : NormedAddCommGroup (HsVectorSobolev χ hN hc μ) := inferInstance
local instance : NormedSpace ℝ (HsVectorSobolev χ hN hc μ) := inferInstance
local instance : InnerProductSpace ℝ (HsVectorSobolev χ hN hc μ) := inferInstance

/-- Pairing with the common rotation is the coordinate sum. -/
private theorem hsExistence_rotation_inner (w : HsEuclidean N) :
    inner ℝ w (hsRotationVector N) = ∑ i : Fin (N : ℕ), w i := by
  simp only [PiLp.inner_apply, hsRotationVector, Real.inner_apply, mul_one]

/-- The Hamiltonian has zero derivative in the common-rotation direction. -/
private theorem hsExistence_rotation_H (x : HsConfiguration N) :
    fderiv ℝ (hsPairExpression χ) (hsLiftPoint N x) (hsRotationVector N) = 0 := by
  rw [← inner_gradient_left, hsExistence_rotation_inner]
  exact boundaryCore_gradient_sum χ (hsLiftPoint_mem_chamber N x)

include hN in
/-- Periodicity and weighted integration by parts give zero mean derivative on the core. -/
private theorem hsExistence_test_mean (f : HsTestFunction N) :
    hsL2Mean μ (hsSobolevGradient μ (hsSobolevOfSmooth μ ⟨f.toFun, f.smoothOnClosure⟩)) = 0 := by
  have hi := hsExistence_directional χ hN hc f (hsPoissonUnit μ) (hsRotationVector N)
  have hleft : (∫ x, hsSmoothValue f.toFun x *
      inner ℝ (hsSobolevGradient μ (hsPoissonUnit μ) x) (hsRotationVector N) ∂μ) = 0 := by
    apply integral_eq_zero_of_ae
    rw [hsPoissonUnit_gradient]
    filter_upwards [Lp.coeFn_zero (HsEuclidean N) 2 μ] with x hx
    simp only [hx, Pi.zero_apply, inner_zero_left, mul_zero]
  have hright : (∫ x, hsSobolevValue μ (hsPoissonUnit μ) x * hsSmoothValue (fun y =>
      f.toFun y * fderiv ℝ (hsPairExpression χ) y (hsRotationVector N) -
        fderiv ℝ f.toFun y (hsRotationVector N)) x ∂μ) =
      -(∫ x, hsSmoothValue (fun y => fderiv ℝ f.toFun y (hsRotationVector N)) x ∂μ) := by
    rw [← integral_neg]
    apply integral_congr_ae
    have hu : (hsSobolevValue μ (hsPoissonUnit μ) : HsConfiguration N → ℝ) =ᵐ[μ] fun _ => 1 := by
      rw [hsPoissonUnit_value]
      exact Lp.coeFn_const 2 μ (1 : ℝ)
    filter_upwards [hu] with x hx
    rw [hx]
    change 1 * (f.toFun (hsLiftPoint N x) *
      fderiv ℝ (hsPairExpression χ) (hsLiftPoint N x) (hsRotationVector N) - _) = _
    rw [hsExistence_rotation_H χ, mul_zero, zero_sub, one_mul]
    rfl
  rw [hsL2Mean_eq_integral]
  have he : (∫ x, ∑ i : Fin (N : ℕ),
      hsSobolevGradient μ (hsSobolevOfSmooth μ ⟨f.toFun, f.smoothOnClosure⟩) x i ∂μ) =
      ∫ x, hsSmoothValue (fun y => fderiv ℝ f.toFun y (hsRotationVector N)) x ∂μ := by
    apply integral_congr_ae
    filter_upwards [(f.smoothOnClosure.memLp_gradient μ).coeFn_toLp] with x hx
    change (∑ i, ((f.smoothOnClosure.memLp_gradient μ).toLp _ x) i) = _
    rw [hx, ← hsExistence_rotation_inner]
    change inner ℝ (gradient f.toFun (hsLiftPoint N x)) (hsRotationVector N) =
      fderiv ℝ f.toFun (hsLiftPoint N x) (hsRotationVector N)
    exact inner_gradient_left
  rw [he]
  rw [hleft, hright] at hi
  linarith only [hi]

include hN in
/-- Every scalar Sobolev gradient satisfies the mean rotation normalization. -/
private theorem hsExistence_gradient_mean (hadm : HsAdmissible χ C_N) (f : HsSobolev μ) :
    hsL2Mean μ (hsSobolevGradient μ f) = 0 := by
  have hc0 : IsClosed {g : HsSobolev μ | hsL2Mean μ (hsSobolevGradient μ g) = 0} :=
    isClosed_eq ((hsL2Mean μ).continuous.comp (hsSobolevGradient μ).continuous) continuous_const
  have hsub : (hsSourceTestSobolev μ : Set (HsSobolev μ)) ⊆
      {g : HsSobolev μ | hsL2Mean μ (hsSobolevGradient μ g) = 0} := by
    rintro _ ⟨g, rfl⟩
    exact hsExistence_test_mean χ hN hc g
  exact closure_minimal hsub hc0 ((scalar_boundary_core_L3219_quotient_real χ hc hadm).2.2.2 f)

/-- The vector realization of a scalar gradient has the same expected coordinate sum. -/
private theorem hsExistence_vector_mean (φ : HsSobolev μ) (G : HsVectorSobolev χ hN hc μ)
    (hv : ∀ i : Fin (N : ℕ), hsJetValue μ i G.val =
      (EuclideanSpace.proj (𝕜 := ℝ) i).compLpL 2 μ (hsSobolevGradient μ φ)) :
    hsNonGradientMean χ hN hc μ G = hsL2Mean μ (hsSobolevGradient μ φ) := by
  change hsVectorMean μ G.val = _
  rw [hsVectorMean_eq_sum]
  simp_rw [hv]
  simp only [hsL2Mean, sum_apply, ContinuousLinearMap.comp_apply]

end Riesz1.Internal

namespace Riesz1.Internal

variable {N : ℕ+} {c C_N : ℝ}
variable (χ : HsPairPotentials N c) (hN : 2 ≤ (N : ℕ)) (hc : 0 < c)

local notation "μ" => (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))

local instance : NormedAddCommGroup (HsSobolev μ) := inferInstance
local instance : NormedSpace ℝ (HsSobolev μ) := inferInstance
local instance : InnerProductSpace ℝ (HsSobolev μ) := inferInstance
local instance : InnerProductSpace ℝ (PiLp 2 (fun _ : Fin (N : ℕ) => HsSobolev μ)) := inferInstance
local instance : NormedAddCommGroup (HsVectorJet μ) := inferInstance
local instance : NormedSpace ℝ (HsVectorJet μ) := inferInstance
local instance : InnerProductSpace ℝ (HsVectorJet μ) := inferInstance
local instance : NormedAddCommGroup (HsVectorSobolev χ hN hc μ) := inferInstance
local instance : NormedSpace ℝ (HsVectorSobolev χ hN hc μ) := inferInstance
local instance : InnerProductSpace ℝ (HsVectorSobolev χ hN hc μ) := inferInstance

/-- The scalar Sobolev rotations have inverse rotations. -/
private theorem hsExistence_pull_neg (t : ℝ) (f : HsSobolev μ) :
    hsGapSobolevPull χ hc t (hsGapSobolevPull χ hc (-t) f) = f := by
  apply hsSobolevValue_injective χ hc
  rw [hsGapSobolevPull_value, hsGapSobolevPull_value, hsGapLpPull_neg]

/-- Constants are invariant under rotation on scalar square-integrable classes. -/
private theorem hsExistence_pull_unit (t : ℝ) :
    hsGapLpPull χ hc ℝ t (Lp.const 2 μ (1 : ℝ)) = Lp.const 2 μ (1 : ℝ) := by
  apply Lp.ext
  have ht := (measurePreserving_hsGapRotate χ hc t).quasiMeasurePreserving.ae
    (Lp.coeFn_const 2 μ (1 : ℝ))
  filter_upwards [hsGapLpPull_ae χ hc ℝ t (Lp.const 2 μ (1 : ℝ)), ht,
    Lp.coeFn_const 2 μ (1 : ℝ)] with x hx hy hz
  exact hx.trans (hy.trans hz.symm)

/-- Centering commutes with common rotation. -/
private theorem hsExistence_pull_center (t : ℝ) (f : Lp ℝ 2 μ) :
    hsGapLpPull χ hc ℝ t (poissonCenter μ f) = poissonCenter μ (hsGapLpPull χ hc ℝ t f) := by
  rw [poissonCenter, map_sub, map_smul, hsExistence_pull_unit χ hc,
    poissonCenter, hsGapLpPull_mean]

/-- A fixed source gives the same scalar equation after rotation. -/
private theorem hsExistence_rotation_solves (F : HsSobolev μ) {φ : HsSobolev μ}
    (hφ : HsPoissonSolves χ hc (hsSobolevValue μ F) φ) (t : ℝ)
    (hF : hsGapLpPull χ hc ℝ t (hsSobolevValue μ F) = hsSobolevValue μ F) :
    HsPoissonSolves χ hc (hsSobolevValue μ F) (hsGapSobolevPull χ hc t φ) := by
  apply (hsPoissonSolves_iff χ hc _ _).mpr
  intro h
  have hh := hsExistence_pull_neg χ hc t h
  have hfix : hsGapLpPull χ hc ℝ t (poissonCenter μ (hsSobolevValue μ F)) =
      poissonCenter μ (hsSobolevValue μ F) := by
    rw [hsExistence_pull_center, hF]
  calc
    _ = inner ℝ (hsSobolevGradient μ (hsGapSobolevPull χ hc t φ))
        (hsSobolevGradient μ (hsGapSobolevPull χ hc t (hsGapSobolevPull χ hc (-t) h))) :=
      congrArg (inner ℝ (hsSobolevGradient μ (hsGapSobolevPull χ hc t φ)))
        (congrArg (hsSobolevGradient μ) hh.symm)
    _ = inner ℝ (hsSobolevGradient μ φ)
        (hsSobolevGradient μ (hsGapSobolevPull χ hc (-t) h)) :=
      (hsGapLpPull χ hc (HsEuclidean N) t).inner_map_map _ _
    _ = inner ℝ (poissonCenter μ (hsSobolevValue μ F))
        (hsSobolevValue μ (hsGapSobolevPull χ hc (-t) h)) :=
      (hsPoissonSolves_iff χ hc _ _).mp hφ _
    _ = inner ℝ (hsGapLpPull χ hc ℝ t (poissonCenter μ (hsSobolevValue μ F)))
        (hsGapLpPull χ hc ℝ t (hsSobolevValue μ (hsGapSobolevPull χ hc (-t) h))) :=
      ((hsGapLpPull χ hc ℝ t).inner_map_map _ _).symm
    _ = _ := by rw [hfix, ← hsGapSobolevPull_value, hh]

include hN in
/-- Uniqueness preserves a fixed source on the mean-zero scalar solution. -/
private theorem hsExistence_rotation_fixed (hPL : External.PrekopaLeindler) (F : HsSobolev μ)
    {φ : HsSobolev μ} (hm : (∫ x, hsSobolevValue μ φ x ∂μ) = 0)
    (hφ : HsPoissonSolves χ hc (hsSobolevValue μ F) φ) (t : ℝ)
    (hF : hsGapLpPull χ hc ℝ t (hsSobolevValue μ F) = hsSobolevValue μ F) :
    hsGapSobolevPull χ hc t φ = φ := by
  obtain ⟨ψ, -, hu⟩ := scalar_poisson_gibbs_existsUnique χ hc hPL hN (hsSobolevValue μ F)
  have hmean : (∫ x, hsSobolevValue μ (hsGapSobolevPull χ hc t φ) x ∂μ) = 0 := by
    rw [← poissonMean_eq_integral, hsGapSobolevPull_value, hsGapLpPull_mean,
      poissonMean_eq_integral, hm]
  exact (hu _ ⟨hmean, hsExistence_rotation_solves χ hc F hφ t hF⟩).trans
    (hu φ ⟨hm, hφ⟩).symm

/-- Measurable functions of the cyclic gaps are fixed by each rotation. -/
private theorem hsExistence_gap_fixed (f : Lp ℝ 2 μ)
    (hf : ∃ g : (Fin (N : ℕ) → ℝ) → ℝ, Measurable g ∧
      (f : HsConfiguration N → ℝ) =ᵐ[μ] fun x => g (hsGap (hsLiftPoint N x))) (t : ℝ) :
    hsGapLpPull χ hc ℝ t f = f := by
  obtain ⟨g, -, hg⟩ := hf
  have ht := (measurePreserving_hsGapRotate χ hc t).quasiMeasurePreserving.ae hg
  apply Lp.ext
  filter_upwards [hsGapLpPull_ae χ hc ℝ t f, hg, ht] with x hx hy hz
  exact hx.trans (hz.trans ((congrArg g (hsGapRotate_gap t x)).trans hy.symm))

include hN in
/-- The normalized scalar solution preserves measurable dependence on the gaps. -/
private theorem hsExistence_gap_solution (hPL : External.PrekopaLeindler) (F : HsSobolev μ)
    {φ : HsSobolev μ} (hm : (∫ x, hsSobolevValue μ φ x ∂μ) = 0)
    (hφ : HsPoissonSolves χ hc (hsSobolevValue μ F) φ)
    (hF : ∃ g : (Fin (N : ℕ) → ℝ) → ℝ, Measurable g ∧
      (hsSobolevValue μ F : HsConfiguration N → ℝ) =ᵐ[μ] fun x => g (hsGap (hsLiftPoint N x))) :
    ∃ g : (Fin (N : ℕ) → ℝ) → ℝ, Measurable g ∧
      (hsSobolevValue μ φ : HsConfiguration N → ℝ) =ᵐ[μ] fun x => g (hsGap (hsLiftPoint N x)) := by
  apply (hsLp_gap_factorization_iff_rotation χ hc _).mpr
  intro t
  apply hsGapLpPull_fixed_ae χ hc t
  exact (hsGapSobolevPull_value χ hc t φ).symm.trans
    (congrArg (hsSobolevValue μ) (hsExistence_rotation_fixed χ hN hc hPL F hm hφ t
      (hsExistence_gap_fixed χ hc _ hF t)))

end Riesz1.Internal

namespace Riesz1.Internal

variable {N : ℕ+} {c C_N : ℝ}
variable (χ : HsPairPotentials N c) (hN : 2 ≤ (N : ℕ)) (hc : 0 < c)

local notation "μ" => (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))

local instance : NormedAddCommGroup (HsSobolev μ) := inferInstance
local instance : NormedSpace ℝ (HsSobolev μ) := inferInstance
local instance : InnerProductSpace ℝ (HsSobolev μ) := inferInstance
local instance : InnerProductSpace ℝ (PiLp 2 (fun _ : Fin (N : ℕ) => HsSobolev μ)) := inferInstance
local instance : NormedAddCommGroup (HsVectorJet μ) := inferInstance
local instance : NormedSpace ℝ (HsVectorJet μ) := inferInstance
local instance : InnerProductSpace ℝ (HsVectorJet μ) := inferInstance
local instance : NormedAddCommGroup (HsVectorSobolev χ hN hc μ) := inferInstance
local instance : NormedSpace ℝ (HsVectorSobolev χ hN hc μ) := inferInstance
local instance : InnerProductSpace ℝ (HsVectorSobolev χ hN hc μ) := inferInstance

/-- Differentiating a smooth test along the common-rotation orbit. -/
private theorem hsExistence_translate_deriv (f : HsTestFunction N) (x : HsConfiguration N) (t : ℝ) :
    HasDerivAt (fun s => f.toFun (hsTranslate s (hsLiftPoint N x)))
      (fderiv ℝ f.toFun (hsTranslate t (hsLiftPoint N x)) (hsRotationVector N)) t := by
  have hline : HasDerivAt (fun s : ℝ => hsTranslate s (hsLiftPoint N x)) (hsRotationVector N) t := by
    simp only [hsTranslate_eq_add_rotation]
    simpa only [id_eq, one_smul] using
      ((hasDerivAt_id t).smul_const (hsRotationVector N)).const_add (hsLiftPoint N x)
  exact (f.smooth.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt t hline

/-- Pairing an invariant observable with a rotated smooth test is constant. -/
private theorem hsExistence_invariant_pairing (a : Lp ℝ 2 μ)
    (ha : ∀ t : ℝ, hsGapLpPull χ hc ℝ t a = a) (f : HsTestFunction N) (t : ℝ) :
    (∫ x, a x * f.toFun (hsTranslate t (hsLiftPoint N x)) ∂μ) =
      inner ℝ a (hsSobolevValue μ (hsSobolevOfSmooth μ ⟨f.toFun, f.smoothOnClosure⟩)) := by
  let b := hsSobolevValue μ (hsSobolevOfSmooth μ ⟨f.toFun, f.smoothOnClosure⟩)
  have hb : (b : HsConfiguration N → ℝ) =ᵐ[μ] hsSmoothValue f.toFun :=
    (f.smoothOnClosure.memLp_value μ).coeFn_toLp
  have ht := (measurePreserving_hsGapRotate χ hc t).quasiMeasurePreserving.ae hb
  have he : (∫ x, a x * f.toFun (hsTranslate t (hsLiftPoint N x)) ∂μ) =
      inner ℝ a (hsGapLpPull χ hc ℝ t b) := by
    rw [poisson_inner_eq_integral]
    apply integral_congr_ae
    filter_upwards [hsGapLpPull_ae χ hc ℝ t b, ht] with x hx hy
    rw [hx, hy]
    exact congrArg (a x * ·) (hsGap_periodic_pull f.toFun f.periodic t x).symm
  exact he.trans ((congrArg (fun z => inner ℝ z (hsGapLpPull χ hc ℝ t b)) (ha t)).symm.trans
    ((hsGapLpPull χ hc ℝ t).inner_map_map a b))

include hN in
/-- Differentiating the constant orbit pairing gives zero against rotation derivatives. -/
private theorem hsExistence_invariant_test_derivative (a : Lp ℝ 2 μ)
    (ha : ∀ t : ℝ, hsGapLpPull χ hc ℝ t a = a) (f : HsTestFunction N) :
    (∫ x, a x * hsSmoothValue (fun y => fderiv ℝ f.toFun y (hsRotationVector N)) x ∂μ) = 0 := by
  let g := hsGradientTestDirection hN f (hsRotationVector N)
  let A := fun t x => a x * f.toFun (hsTranslate t (hsLiftPoint N x))
  let B := fun t x => a x * g.toFun (hsTranslate t (hsLiftPoint N x))
  obtain ⟨C, hC⟩ := (isCompact_closure_hsFundamentalRegion N).exists_bound_of_continuousOn
    g.smooth.continuous.continuousOn
  have hm (t : ℝ) (h : HsTestFunction N) :
      AEStronglyMeasurable (fun x => h.toFun (hsTranslate t (hsLiftPoint N x))) μ := by
    have hcont : Continuous (hsTranslate (N := N) t) := by
      have he : hsTranslate (N := N) t =
          fun y => y + WithLp.toLp 2 (fun _ : Fin (N : ℕ) => t) :=
        funext (hsGap_translate_eq_add t)
      rw [he]
      exact continuous_id.add continuous_const
    exact (h.smooth.continuous.measurable.comp
      (hcont.measurable.comp (measurable_hsLiftPoint N))).aestronglyMeasurable
  have hA : ∀ᶠ t in 𝓝 (0 : ℝ), AEStronglyMeasurable (A t) μ :=
    Eventually.of_forall (fun t => (Lp.aestronglyMeasurable a).mul (hm t f))
  have hAi : Integrable (A 0) μ := by
    have hi : Integrable (fun x => a x * hsSmoothValue f.toFun x) μ :=
      (Lp.memLp a).integrable_mul (f.smoothOnClosure.memLp_value μ)
    simpa only [A, hsTranslate_zero, hsSmoothValue] using hi
  have hB : AEStronglyMeasurable (B 0) μ := (Lp.aestronglyMeasurable a).mul (hm 0 g)
  have hb : ∀ᵐ x ∂μ, ∀ t ∈ (univ : Set ℝ), ‖B t x‖ ≤ ‖a x‖ * C := by
    filter_upwards with x
    intro t _
    change ‖a x * g.toFun (hsTranslate t (hsLiftPoint N x))‖ ≤ ‖a x‖ * C
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    rw [← hsGap_periodic_pull g.toFun g.periodic t x]
    exact hC _ (subset_closure (hsLiftPoint_mem_fundamentalRegion N _))
  have hbi : Integrable (fun x => ‖a x‖ * C) μ :=
    ((Lp.memLp a).integrable one_le_two).norm.mul_const C
  have hd : ∀ᵐ x ∂μ, ∀ t ∈ (univ : Set ℝ), HasDerivAt (fun s => A s x) (B t x) t := by
    filter_upwards with x
    intro t _
    exact (hsExistence_translate_deriv f x t).const_mul (a x)
  have hder := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := univ) (x₀ := (0 : ℝ)) (bound := fun x => ‖a x‖ * C)
    (Filter.univ_mem) hA hAi hB hb hbi hd).2
  have he : (fun t => ∫ x, A t x ∂μ) = fun _ : ℝ =>
      inner ℝ a (hsSobolevValue μ (hsSobolevOfSmooth μ ⟨f.toFun, f.smoothOnClosure⟩)) :=
    funext (hsExistence_invariant_pairing χ hc a ha f)
  rw [he] at hder
  have hz := hder.unique (hasDerivAt_const (0 : ℝ)
    (inner ℝ a (hsSobolevValue μ (hsSobolevOfSmooth μ ⟨f.toFun, f.smoothOnClosure⟩))))
  simpa only [B, hsTranslate_zero, g, hsGradientTestDirection, hsSmoothValue] using hz

include hN in
/-- The scalar weak derivative in the rotation direction pairs to zero with every test. -/
private theorem hsExistence_invariant_gradient_test (φ : HsSobolev μ)
    (hφ : ∀ t : ℝ, hsGapLpPull χ hc ℝ t (hsSobolevValue μ φ) = hsSobolevValue μ φ)
    (f : HsTestFunction N) :
    (∫ x, hsSmoothValue f.toFun x * inner ℝ (hsSobolevGradient μ φ x)
      (hsRotationVector N) ∂μ) = 0 := by
  rw [hsExistence_directional χ hN hc f φ (hsRotationVector N)]
  have he : (∫ x, hsSobolevValue μ φ x * hsSmoothValue (fun y =>
      f.toFun y * fderiv ℝ (hsPairExpression χ) y (hsRotationVector N) -
        fderiv ℝ f.toFun y (hsRotationVector N)) x ∂μ) =
      -(∫ x, hsSobolevValue μ φ x * hsSmoothValue (fun y =>
        fderiv ℝ f.toFun y (hsRotationVector N)) x ∂μ) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards with x
    change hsSobolevValue μ φ x * (f.toFun (hsLiftPoint N x) *
      fderiv ℝ (hsPairExpression χ) (hsLiftPoint N x) (hsRotationVector N) - _) = _
    rw [hsExistence_rotation_H χ x, mul_zero, zero_sub, mul_neg]
    rfl
  rw [he, hsExistence_invariant_test_derivative χ hN hc _ hφ f, neg_zero]

include hN in
/-- Every rotation-invariant Sobolev observable has zero coordinate sum of its weak gradient. -/
private theorem hsExistence_invariant_gradient_sum (φ : HsSobolev μ)
    (hφ : ∀ t : ℝ, hsGapLpPull χ hc ℝ t (hsSobolevValue μ φ) = hsSobolevValue μ φ) :
    ∀ᵐ x ∂μ, ∑ i : Fin (N : ℕ), hsSobolevGradient μ φ x i = 0 := by
  let d := (innerSL ℝ (hsRotationVector N)).compLpL 2 μ (hsSobolevGradient μ φ)
  have hd : (d : HsConfiguration N → ℝ) =ᵐ[μ]
      fun x => inner ℝ (hsSobolevGradient μ φ x) (hsRotationVector N) := by
    filter_upwards [ContinuousLinearMap.coeFn_compLpL (innerSL ℝ (hsRotationVector N))
      (hsSobolevGradient μ φ)] with x hx
    simp only [innerSL_apply_apply] at hx
    exact hx.trans (real_inner_comm (hsSobolevGradient μ φ x) (hsRotationVector N))
  have ht : ∀ b ∈ hsTestL2Domain μ, inner ℝ b d = 0 := by
    intro b hb
    obtain ⟨f, rfl⟩ := (mem_hsTestL2Domain μ b).mp hb
    rw [poisson_inner_eq_integral]
    have he : (∫ x, hsSobolevValue μ
        (hsSobolevOfSmooth μ ⟨f.toFun, f.smoothOnClosure⟩) x * d x ∂μ) =
        ∫ x, hsSmoothValue f.toFun x * inner ℝ (hsSobolevGradient μ φ x)
          (hsRotationVector N) ∂μ := by
      apply integral_congr_ae
      filter_upwards [(f.smoothOnClosure.memLp_value μ).coeFn_toLp, hd] with x hx hy
      change ((f.smoothOnClosure.memLp_value μ).toLp _ x) * _ = _
      rw [hx, hy]
    exact he.trans (hsExistence_invariant_gradient_test χ hN hc φ hφ f)
  have hall : ∀ b : Lp ℝ 2 μ, inner ℝ b d = 0 := fun b =>
    closure_minimal ht (isClosed_eq (continuous_id.inner continuous_const) continuous_const)
      (dense_hsTestL2Domain hN χ hc b)
  have hz : d = 0 := inner_self_eq_zero.mp (hall d)
  have hae : (d : HsConfiguration N → ℝ) =ᵐ[μ] 0 := by
    rw [hz]
    exact Lp.coeFn_zero ℝ 2 μ
  filter_upwards [hd, hae] with x hx hy
  exact (hsExistence_rotation_inner (hsSobolevGradient μ φ x)).symm.trans (hx.symm.trans hy)

end Riesz1.Internal

namespace Riesz1

namespace Internal

variable {N : ℕ+} {c C_N : ℝ}
variable (χ : HsPairPotentials N c) (hN : 2 ≤ (N : ℕ)) (hc : 0 < c)

local notation "μ" => (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))

/-- Zero vector energy and normalization remove the constant rotation field. -/
private theorem hsExistence_normalized_kernel (hPL : External.PrekopaLeindler)
    (hadm : HsAdmissible χ C_N) (u : HsVectorSobolev χ hadm.choose hc μ)
    (hm : hsNonGradientMean χ hadm.choose hc μ u = 0)
    (hu : hsVectorSobolevForm χ hadm.choose hc μ u u = 0) : u = 0 := by
  obtain ⟨a, ha⟩ := (hsVector_form_eq_zero_iff hPL χ hc hadm u).mp hu
  have hm' : hsVectorMean μ u.val = 0 := hm
  rw [ha, hsVectorMean_rotationUnit] at hm'
  have hz : a = 0 := (mul_eq_zero.mp hm').resolve_right (sqrt_N_pos N).ne'
  exact ha.trans ((congrArg (fun r : ℝ => hsRotationField χ hc hadm (r • hsPoissonUnit μ)) hz).trans
    ((congrArg (hsRotationField χ hc hadm) (zero_smul ℝ (hsPoissonUnit μ))).trans
      (hsRotationField χ hc hadm).map_zero))

/-- Two normalized weak vector solutions agree by the zero-energy kernel. -/
private theorem hsExistence_eq_inverse (hPL : External.PrekopaLeindler) (hadm : HsAdmissible χ C_N)
    (v : hsMeanZeroL2 μ) (u : hsMeanZeroVector χ hadm.choose hc μ)
    (hs : HsNonGradientSolves χ hadm.choose hc v.val u.val) :
    u = hsInverse hPL χ hadm.choose hc v := by
  let w := (hsInverse hPL χ hadm.choose hc v).val
  let d := u.val - w
  have hq : hsVectorSobolevForm χ hadm.choose hc μ d d = 0 := by
    have hd := congrArg (fun L : HsVectorSobolev χ hadm.choose hc μ →L[ℝ] ℝ => L d)
      ((hsNonGradientFullBilinear χ hadm.choose hc μ).map_sub u.val w)
    change hsNonGradientFullBilinear χ hadm.choose hc μ d d =
      hsNonGradientFullBilinear χ hadm.choose hc μ u.val d -
        hsNonGradientFullBilinear χ hadm.choose hc μ w d at hd
    have h1 := (hsNonGradientFullBilinear_eq χ hadm.choose hc μ u.val d).trans (hs d)
    have h2 := (hsNonGradientFullBilinear_eq χ hadm.choose hc μ w d).trans
      (hsInverse_solves hPL χ hadm.choose hc hadm v d)
    exact (hsNonGradientFullBilinear_eq χ hadm.choose hc μ d d).symm.trans
      (hd.trans (sub_eq_zero.mpr (h1.trans h2.symm)))
  have hm : hsNonGradientMean χ hadm.choose hc μ d = 0 :=
    ((hsNonGradientMean χ hadm.choose hc μ).map_sub u.val w).trans
      ((congrArg₂ (· - ·) u.property (hsInverse hPL χ hadm.choose hc v).property).trans (sub_self 0))
  exact Subtype.ext (sub_eq_zero.mp (hsExistence_normalized_kernel χ hc hPL hadm d hm hq))

/-- The scalar gradient is the unique normalized vector minimizer. -/
private theorem hsExistence_minimizer (hPL : External.PrekopaLeindler) (hadm : HsAdmissible χ C_N)
    (F : HsSobolev μ) {φ : HsSobolev μ} (hφ : HsPoissonSolves χ hc (hsSobolevValue μ F) φ) :
    ∃ G : hsMeanZeroVector χ hadm.choose hc μ,
      (∀ i : Fin (N : ℕ), hsJetValue μ i G.val.val =
        (EuclideanSpace.proj (𝕜 := ℝ) i).compLpL 2 μ (hsSobolevGradient μ φ)) ∧
      HsNonGradientSolves χ hadm.choose hc (hsSobolevGradient μ F) G.val ∧
      (∀ u : hsMeanZeroVector χ hadm.choose hc μ,
        (∀ w : hsMeanZeroVector χ hadm.choose hc μ,
          hsVectorSobolevForm χ hadm.choose hc μ u.val u.val -
              2 * hsNonGradientPairing μ (hsSobolevGradient μ F) u.val.val ≤
            hsVectorSobolevForm χ hadm.choose hc μ w.val w.val -
              2 * hsNonGradientPairing μ (hsSobolevGradient μ F) w.val.val) ↔ u = G) := by
  have hg := hsExistence_gradient_weak χ hadm.choose hc hadm F (φ := φ) hφ
  obtain ⟨G, hv, hs⟩ := hg
  have hm : hsNonGradientMean χ hadm.choose hc μ G = 0 :=
    (hsExistence_vector_mean χ hadm.choose hc φ G hv).trans (hsExistence_gradient_mean χ hadm.choose hc hadm φ)
  let u : hsMeanZeroVector χ hadm.choose hc μ := ⟨G, hm⟩
  let v : hsMeanZeroL2 μ := ⟨hsSobolevGradient μ F, hsExistence_gradient_mean χ hadm.choose hc hadm F⟩
  have he : u = hsInverse hPL χ hadm.choose hc v :=
    hsExistence_eq_inverse χ hc hPL hadm v u hs
  refine ⟨u, hv, hs, ?_⟩
  intro w
  change (∀ z : hsMeanZeroVector χ hadm.choose hc μ,
    hsNonGradientFunctional χ hadm.choose hc v w ≤ hsNonGradientFunctional χ hadm.choose hc v z) ↔ w = u
  rw [he]
  exact hsInverse_minimizer_iff hPL χ hadm.choose hc v w

/-- Testing the scalar equation with a centered observable gives its covariance. -/
private theorem hsExistence_covariance (F : HsSobolev μ) {φ : HsSobolev μ}
    (hφ : HsPoissonSolves χ hc (hsSobolevValue μ F) φ) (G : HsSobolev μ) :
    (∫ x, (hsSobolevValue μ F x - ∫ y, hsSobolevValue μ F y ∂μ) *
      (hsSobolevValue μ G x - ∫ y, hsSobolevValue μ G y ∂μ) ∂μ) =
      ∫ x, inner ℝ (hsSobolevGradient μ φ x) (hsSobolevGradient μ G x) ∂μ := by
  let h := G - poissonMean μ (hsSobolevValue μ G) • hsPoissonUnit μ
  have hv : hsSobolevValue μ h = poissonCenter μ (hsSobolevValue μ G) := by
    rw [map_sub, map_smul, hsPoissonUnit_value]
    rfl
  have hg : hsSobolevGradient μ h = hsSobolevGradient μ G := by
    rw [map_sub, map_smul, hsPoissonUnit_gradient, smul_zero, sub_zero]
  have he := (hsPoissonSolves_iff χ hc _ _).mp hφ h
  rw [hg, hv, L2.inner_def, poisson_inner_eq_integral] at he
  refine (integral_congr_ae ?_).trans he.symm
  filter_upwards [poissonCenter_ae μ (hsSobolevValue μ F),
    poissonCenter_ae μ (hsSobolevValue μ G)] with x hx hy
  rw [hx, hy]

/-- The mean-zero scalar solution and its full affine space of solutions. -/
private theorem hsExistence_scalar (hadm : HsAdmissible χ C_N) (F : HsSobolev μ) :
    ∃ φ : HsSobolev μ, (∫ x, hsSobolevValue μ φ x ∂μ) = 0 ∧
      HsPoissonSolves χ hc (hsSobolevValue μ F) φ ∧
      (∀ ψ : HsSobolev μ, HsPoissonSolves χ hc (hsSobolevValue μ F) ψ ↔
        ∃ a : ℝ, ψ = φ + a • hsPoissonUnit μ) := by
  have hex := scalar_poisson_gibbs χ hc Externals.prekopa_leindler_proof hadm.choose
    (hsSobolevValue μ F)
  dsimp only at hex
  obtain ⟨φ, hm, hs, -, ha, -⟩ := hex
  exact ⟨φ, hm, hs, ha⟩

/-- The vector realization and the expected scalar derivative sum use the same normalization. -/
private theorem hsExistence_gradient (hadm : HsAdmissible χ C_N) (F : HsSobolev μ)
    {φ : HsSobolev μ} (hφ : HsPoissonSolves χ hc (hsSobolevValue μ F) φ) :
    ∃ G : hsMeanZeroVector χ hadm.choose hc μ,
      (∀ i : Fin (N : ℕ), hsJetValue μ i G.val.val =
        (EuclideanSpace.proj (𝕜 := ℝ) i).compLpL 2 μ (hsSobolevGradient μ φ)) ∧
      HsNonGradientSolves χ hadm.choose hc (hsSobolevGradient μ F) G.val ∧
      (∫ x, ∑ i : Fin (N : ℕ), hsSobolevGradient μ φ x i ∂μ) = 0 := by
  have hex := hsExistence_gradient_weak χ hadm.choose hc hadm F (φ := φ) hφ
  obtain ⟨G, hv, hs⟩ := hex
  have hm := hsExistence_gradient_mean χ hadm.choose hc hadm φ
  have hG : hsNonGradientMean χ hadm.choose hc μ G = 0 :=
    (hsExistence_vector_mean χ hadm.choose hc φ G hv).trans hm
  rw [hsL2Mean_eq_integral] at hm
  exact ⟨⟨G, hG⟩, hv, hs, hm⟩

end Internal

variable {N : ℕ+} {c C_N : ℝ}

/-- The scalar Poisson equation has a unique mean-zero solution, and every solution differs
from it by a constant. -/
theorem existence_representation_scalar (χ : HsPairPotentials N c) (hc : 0 < c)
    (hadm : HsAdmissible χ C_N) (F : HsSobolev
      (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))) :
    let μ : Measure (HsConfiguration N) := hsQuotientGibbsProbability χ hc
    ∃ φ : HsSobolev μ, (∫ x, hsSobolevValue μ φ x ∂μ) = 0 ∧
      HsPoissonSolves χ hc (hsSobolevValue μ F) φ ∧
      (∀ ψ : HsSobolev μ, HsPoissonSolves χ hc (hsSobolevValue μ F) ψ ↔
        ∃ a : ℝ, ψ = φ + a • hsPoissonUnit μ) :=
  Internal.hsExistence_scalar χ hc hadm F

/-- The scalar solution has a normalized vector-energy gradient solving the full vector
weak equation. Its expected coordinate sum vanishes. -/
theorem existence_representation_gradient (χ : HsPairPotentials N c) (hc : 0 < c)
    (hadm : HsAdmissible χ C_N)
    (F : HsSobolev (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)))
    {φ : HsSobolev (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))}
    (hφ : HsPoissonSolves χ hc (hsSobolevValue _ F) φ) :
    let μ : Measure (HsConfiguration N) := hsQuotientGibbsProbability χ hc
    ∃ G : hsMeanZeroVector χ hadm.choose hc μ,
      (∀ i : Fin (N : ℕ), hsJetValue μ i G.val.val =
        (EuclideanSpace.proj (𝕜 := ℝ) i).compLpL 2 μ (hsSobolevGradient μ φ)) ∧
      HsNonGradientSolves χ hadm.choose hc (hsSobolevGradient μ F) G.val ∧
      (∫ x, ∑ i : Fin (N : ℕ), hsSobolevGradient μ φ x i ∂μ) = 0 :=
  Internal.hsExistence_gradient χ hc hadm F (φ := φ) hφ

/-- The scalar gradient is the unique minimizer of the normalized vector quadratic functional. -/
theorem existence_representation_minimizer (χ : HsPairPotentials N c) (hc : 0 < c)
    (hadm : HsAdmissible χ C_N)
    (F : HsSobolev (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)))
    {φ : HsSobolev (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))}
    (hφ : HsPoissonSolves χ hc (hsSobolevValue (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)) F) φ) :
    let μ : Measure (HsConfiguration N) := hsQuotientGibbsProbability χ hc
    ∃ G : hsMeanZeroVector χ hadm.choose hc μ,
      (∀ i : Fin (N : ℕ), hsJetValue μ i G.val.val =
        (EuclideanSpace.proj (𝕜 := ℝ) i).compLpL 2 μ (hsSobolevGradient μ φ)) ∧
      HsNonGradientSolves χ hadm.choose hc (hsSobolevGradient μ F) G.val ∧
      (∀ u : hsMeanZeroVector χ hadm.choose hc μ,
        (∀ w : hsMeanZeroVector χ hadm.choose hc μ,
          hsVectorSobolevForm χ hadm.choose hc μ u.val u.val -
              2 * hsNonGradientPairing μ (hsSobolevGradient μ F) u.val.val ≤
            hsVectorSobolevForm χ hadm.choose hc μ w.val w.val -
              2 * hsNonGradientPairing μ (hsSobolevGradient μ F) w.val.val) ↔ u = G) :=
  Internal.hsExistence_minimizer χ hc Externals.prekopa_leindler_proof hadm F (φ := φ) hφ

/-- Testing the scalar equation gives the covariance representation for every Sobolev test. -/
theorem existence_representation_covariance (χ : HsPairPotentials N c) (hc : 0 < c)
    (F : HsSobolev (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)))
    {φ : HsSobolev (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))}
    (hφ : HsPoissonSolves χ hc (hsSobolevValue _ F) φ)
    (K : HsSobolev (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))) :
    let μ : Measure (HsConfiguration N) := hsQuotientGibbsProbability χ hc
    (∫ x, (hsSobolevValue μ F x - ∫ y, hsSobolevValue μ F y ∂μ) *
      (hsSobolevValue μ K x - ∫ y, hsSobolevValue μ K y ∂μ) ∂μ) =
      ∫ x, inner ℝ (hsSobolevGradient μ φ x) (hsSobolevGradient μ K x) ∂μ :=
  Internal.hsExistence_covariance χ hc F (φ := φ) hφ K

/-- The covariance representation at the source itself is the variance representation. -/
theorem existence_representation_variance (χ : HsPairPotentials N c) (hc : 0 < c)
    (F : HsSobolev (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)))
    {φ : HsSobolev (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))}
    (hφ : HsPoissonSolves χ hc (hsSobolevValue _ F) φ) :
    let μ : Measure (HsConfiguration N) := hsQuotientGibbsProbability χ hc
    (∫ x, (hsSobolevValue μ F x - ∫ y, hsSobolevValue μ F y ∂μ) ^ 2 ∂μ) =
      ∫ x, inner ℝ (hsSobolevGradient μ φ x) (hsSobolevGradient μ F x) ∂μ := by
  simpa only [pow_two] using existence_representation_covariance χ hc F (φ := φ) hφ F

/-- Every scalar solution with a gap-dependent source depends on the gaps and has zero
weak derivative in the common-rotation direction. -/
theorem existence_representation_gaps (χ : HsPairPotentials N c) (hc : 0 < c)
    (hadm : HsAdmissible χ C_N)
    (F : HsSobolev (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)))
    {φ : HsSobolev (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))}
    (hφ : HsPoissonSolves χ hc (hsSobolevValue _ F) φ)
    (hF : ∃ g : (Fin (N : ℕ) → ℝ) → ℝ, Measurable g ∧
      (hsSobolevValue _ F : HsConfiguration N → ℝ) =ᵐ[(hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))]
        fun x => g (hsGap (hsLiftPoint N x))) :
    let μ : Measure (HsConfiguration N) := hsQuotientGibbsProbability χ hc
    (∃ g : (Fin (N : ℕ) → ℝ) → ℝ, Measurable g ∧
      (hsSobolevValue μ φ : HsConfiguration N → ℝ) =ᵐ[μ] fun x => g (hsGap (hsLiftPoint N x))) ∧
      ∀ᵐ x ∂μ, ∑ i : Fin (N : ℕ), hsSobolevGradient μ φ x i = 0 := by
  let μ : Measure (HsConfiguration N) := hsQuotientGibbsProbability χ hc
  obtain ⟨ψ, hm, hψ, ha⟩ := existence_representation_scalar χ hc hadm F
  obtain ⟨a, hφa⟩ := (ha φ).mp hφ
  have hfix (t : ℝ) : hsGapLpPull χ hc ℝ t (hsSobolevValue μ ψ) = hsSobolevValue μ ψ :=
    (hsGapSobolevPull_value χ hc t ψ).symm.trans
      (congrArg (hsSobolevValue μ) (Internal.hsExistence_rotation_fixed χ hadm.choose hc
        Externals.prekopa_leindler_proof F (φ := ψ) hm hψ t (Internal.hsExistence_gap_fixed χ hc _ hF t)))
  have hgrad : hsSobolevGradient μ φ = hsSobolevGradient μ ψ := by
    rw [hφa, map_add, map_smul, hsPoissonUnit_gradient, smul_zero, add_zero]
  have hsum := Internal.hsExistence_invariant_gradient_sum χ hadm.choose hc ψ hfix
  refine ⟨?_, ?_⟩
  · obtain ⟨g, hgm, hg⟩ := Internal.hsExistence_gap_solution χ hadm.choose hc
      Externals.prekopa_leindler_proof F (φ := ψ) hm hψ hF
    refine ⟨fun z => g z + a, hgm.add measurable_const, ?_⟩
    have hv : hsSobolevValue μ φ = hsSobolevValue μ ψ + a • Lp.const 2 μ (1 : ℝ) := by
      rw [hφa, map_add, map_smul, hsPoissonUnit_value]
    rw [hv]
    filter_upwards [hg, Lp.coeFn_add (hsSobolevValue μ ψ) (a • Lp.const 2 μ (1 : ℝ)),
      Lp.coeFn_smul a (Lp.const 2 μ (1 : ℝ)), Lp.coeFn_const 2 μ (1 : ℝ)] with x hx hy hz h1
    simp only [hy, Pi.add_apply, hz, Pi.smul_apply, h1, Function.const_apply, smul_eq_mul, mul_one]
    exact congrArg (· + a) hx
  · rw [hgrad]
    exact hsum

end Riesz1
