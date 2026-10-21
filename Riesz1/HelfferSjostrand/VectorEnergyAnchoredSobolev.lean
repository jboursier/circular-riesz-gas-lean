/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.VectorEnergyAnchoredForm
public import Riesz1.HelfferSjostrand.AnchoredIntegrationByParts
public import Riesz1.ToMathlib.WeightedSobolev.Graph
public import Riesz1.ToMathlib.WeightedSobolev.TestDensity
public import Riesz1.ToMathlib.WeightedSobolev.TruncatedIdentity

/-!
# The anchored vector energy space `𝒱_{μ*}`

The space `𝒱_{μ*}` for the anchored law `μ*` is the completion
of the anchored test tuples `𝒟_N^*` for `‖u‖² = ∫|u|² dμ* + q_{μ*}(u, u)`. It is realized, as the
Gibbs space `𝒱_μ` of `VectorEnergySobolev`, as the closure of the jets of test tuples in a Hilbert
space. Here a jet consists of, at each anchored point,
* the values `(u_1, …, u_n)` of the tuple,
* the gradients `(∇u_1, …, ∇u_n)`,
* the pair Hessian energy `(√(2 χ_ij''(x_j - x_i)) (x_j - x_i)-entries)_{i<j}` of the lifted tuple,

all in `L²(μ*)`. The norm of a jet is `∫|u|² + q_{μ*}(u, u)`, because the Hessian energy
reproduces the Hessian part of `q_{μ*}` (`inner_anchoredHessianEnergy`).

The scalar components of a limit have weak gradients: each closure element is a limit of jets, and
the graph characterization `isGraphH1_iff_mem_closure` turns this into `IsAnchoredH1`. The
Hessian energy of a limit is the pair weight times the particle differences, almost everywhere. The
completion is closable: a limit with zero values is zero, by the directional integration by parts
`anchoredH1_directional_integrationByParts` and the energy identity.

The lift is the anchored one: the anchor is particle `0` with value zero, and the component `j` of a
tuple is particle `j + 1`. The energy of a pair `(i, j)` uses the particle values, not the component
values.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal ContDiff InnerProductSpace

namespace Riesz1

variable {n : ℕ} {c : ℝ}

/-- The gradient tuple and the pair energy of an anchored jet point, as one Hilbert vector. -/
abbrev AnchoredJetPair (n : ℕ) :=
  WithLp 2 (PiLp 2 (fun _ : Fin n => AnchoredEuclidean n) ×
    EuclideanSpace ℝ (HsPairIndex n.succPNat))

/-- The pointwise jet space: the values `ℝ^n` and the pair `(gradients, energies)`. -/
abbrev AnchoredJetPoint (n : ℕ) :=
  WithLp 2 (EuclideanSpace ℝ (Fin n) × AnchoredJetPair n)

/-- The `i`-th value of a jet point. -/
def jetValueL (i : Fin n) : AnchoredJetPoint n →L[ℝ] ℝ :=
  (EuclideanSpace.proj (𝕜 := ℝ) i).comp (WithLp.fstL 2 ℝ _ _)

/-- The pair `(gradients, energies)` of a jet point. -/
def jetPairL : AnchoredJetPoint n →L[ℝ] AnchoredJetPair n :=
  WithLp.sndL 2 ℝ _ _

/-- The gradient tuple of a jet point. -/
def jetGradVecL : AnchoredJetPoint n →L[ℝ] PiLp 2 (fun _ : Fin n => AnchoredEuclidean n) :=
  (WithLp.fstL 2 ℝ _ _).comp jetPairL

/-- The `i`-th gradient of a jet point. -/
def jetGradL (i : Fin n) : AnchoredJetPoint n →L[ℝ] AnchoredEuclidean n :=
  (PiLp.proj 2 (fun _ : Fin n => AnchoredEuclidean n) i).comp jetGradVecL

/-- The pair energy vector of a jet point. -/
def jetEnergyVecL : AnchoredJetPoint n →L[ℝ] EuclideanSpace ℝ (HsPairIndex n.succPNat) :=
  (WithLp.sndL 2 ℝ _ _).comp jetPairL

/-- The pair energy coordinate `p` of a jet point. -/
def jetEnergyL (p : HsPairIndex n.succPNat) : AnchoredJetPoint n →L[ℝ] ℝ :=
  (EuclideanSpace.proj (𝕜 := ℝ) p).comp jetEnergyVecL

/-- The `k`-th particle value of a jet point: the anchor `0` has value zero, and particle `j + 1`
carries the value `u_j`. -/
def particleValueL (k : Fin (n.succPNat : ℕ)) : AnchoredJetPoint n →L[ℝ] ℝ :=
  Fin.cases 0 (fun j => jetValueL j) k

/-- The pointwise jet of a test tuple: its values, gradients and pair energy at `y`. -/
def anchoredJetFun (χ : HsPairPotentials n.succPNat c) (u : AnchoredVectorTest n)
    (y : AnchoredEuclidean n) : AnchoredJetPoint n :=
  WithLp.toLp 2 (anchoredTestVector u y, WithLp.toLp 2
    (WithLp.toLp 2 (fun i => gradient (u i : AnchoredEuclidean n → ℝ) y),
      anchoredEnergyFun χ u y))

/-- The gradient of a smooth test function is continuous. -/
theorem continuous_gradient_anchoredTest (f : anchoredTestSubmodule n) :
    Continuous (gradient (f : AnchoredEuclidean n → ℝ)) :=
  (InnerProductSpace.toDual ℝ (AnchoredEuclidean n)).symm.continuous.comp
    (f.2.1.continuous_fderiv (by simp))

/-- The gradient of a function vanishes outside its topological support. -/
theorem gradient_eq_zero_of_notMem_tsupport {f : AnchoredEuclidean n → ℝ}
    {y : AnchoredEuclidean n} (hy : y ∉ tsupport f) : gradient f y = 0 := by
  unfold gradient
  rw [fderiv_of_notMem_tsupport ℝ hy, map_zero]

/-- The gradient of a sum of functions differentiable at `y`. -/
theorem gradient_add_of_differentiableAt {f g : AnchoredEuclidean n → ℝ} {y : AnchoredEuclidean n}
    (hf : DifferentiableAt ℝ f y) (hg : DifferentiableAt ℝ g y) :
    gradient (f + g) y = gradient f y + gradient g y := by
  have hd : fderiv ℝ (f + g) y = fderiv ℝ f y + fderiv ℝ g y := fderiv_add hf hg
  unfold gradient
  rw [hd, map_add]

/-- The gradient of a scalar multiple of a function differentiable at `y`. -/
theorem gradient_smul_of_differentiableAt (a : ℝ) {f : AnchoredEuclidean n → ℝ}
    {y : AnchoredEuclidean n} (hf : DifferentiableAt ℝ f y) :
    gradient (a • f) y = a • gradient f y := by
  have hd : fderiv ℝ (a • f) y = a • fderiv ℝ f y := fderiv_const_smul hf a
  unfold gradient
  rw [hd, map_smul]

/-- The pointwise jet of a test tuple is continuous. -/
theorem continuous_anchoredJetFun (χ : HsPairPotentials n.succPNat c) (u : AnchoredVectorTest n) :
    Continuous (anchoredJetFun χ u) := by
  unfold anchoredJetFun
  have hgrad : Continuous (fun y : AnchoredEuclidean n =>
      (WithLp.toLp 2 (fun i => gradient (u i : AnchoredEuclidean n → ℝ) y) :
        PiLp 2 (fun _ : Fin n => AnchoredEuclidean n))) :=
    (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => continuous_gradient_anchoredTest (u i))
  have hpair : Continuous (fun y : AnchoredEuclidean n =>
      ((WithLp.toLp 2 (fun i => gradient (u i : AnchoredEuclidean n → ℝ) y) :
        PiLp 2 (fun _ : Fin n => AnchoredEuclidean n)), anchoredEnergyFun χ u y)) :=
    hgrad.prodMk (continuous_anchoredEnergyFun χ u)
  exact (WithLp.prod_continuous_toLp 2 _ _).comp
    ((continuous_anchoredTestVector u).prodMk ((WithLp.prod_continuous_toLp 2 _ _).comp hpair))

/-- The pointwise jet of a test tuple has compact support. -/
theorem hasCompactSupport_anchoredJetFun (χ : HsPairPotentials n.succPNat c)
    (u : AnchoredVectorTest n) : HasCompactSupport (anchoredJetFun χ u) :=
  HasCompactSupport.intro (isCompact_anchoredSupportUnion u) fun y hy => by
    have hv : ∀ i, y ∉ tsupport (u i : AnchoredEuclidean n → ℝ) :=
      fun i hi => hy (mem_iUnion.mpr ⟨i, hi⟩)
    have hvec : anchoredTestVector u y = 0 := by
      ext i
      simp [anchoredTestVector, image_eq_zero_of_notMem_tsupport (hv i)]
    have hg : ∀ i, gradient (u i : AnchoredEuclidean n → ℝ) y = 0 :=
      fun i => gradient_eq_zero_of_notMem_tsupport (hv i)
    unfold anchoredJetFun
    rw [anchoredEnergyFun_eq_zero χ u hv, hvec]
    simp [hg]
    rfl

/-- The pointwise jet of a test tuple is square integrable against a finite measure. -/
theorem memLp_anchoredJetFun (χ : HsPairPotentials n.succPNat c) (μ : Measure (AnchoredEuclidean n))
    [IsFiniteMeasure μ] (u : AnchoredVectorTest n) : MemLp (anchoredJetFun χ u) 2 μ :=
  (continuous_anchoredJetFun χ u).memLp_of_hasCompactSupport (hasCompactSupport_anchoredJetFun χ u)

/-- The jet of an anchored test tuple in `L²(μ)`. -/
def anchoredVectorJet (χ : HsPairPotentials n.succPNat c) (μ : Measure (AnchoredEuclidean n))
    [IsFiniteMeasure μ] (u : AnchoredVectorTest n) : Lp (AnchoredJetPoint n) 2 μ :=
  (memLp_anchoredJetFun χ μ u).toLp (anchoredJetFun χ u)

/-- The pointwise jet is additive in the tuple. -/
theorem anchoredJetFun_add (χ : HsPairPotentials n.succPNat c) (u v : AnchoredVectorTest n)
    (y : AnchoredEuclidean n) :
    anchoredJetFun χ (u + v) y = anchoredJetFun χ u y + anchoredJetFun χ v y := by
  unfold anchoredJetFun
  have hg : ∀ i : Fin n, gradient ((u + v) i : AnchoredEuclidean n → ℝ) y =
      gradient (u i : AnchoredEuclidean n → ℝ) y + gradient (v i : AnchoredEuclidean n → ℝ) y :=
    fun i => gradient_add_of_differentiableAt ((ContDiff.differentiable (u i).2.1 (by simp)).differentiableAt)
      ((ContDiff.differentiable (v i).2.1 (by simp)).differentiableAt)
  simp only [anchoredTestVector_add, anchoredEnergyFun_add, hg]
  rfl

/-- The pointwise jet is homogeneous in the tuple. -/
theorem anchoredJetFun_smul (χ : HsPairPotentials n.succPNat c) (a : ℝ) (u : AnchoredVectorTest n)
    (y : AnchoredEuclidean n) :
    anchoredJetFun χ (a • u) y = a • anchoredJetFun χ u y := by
  unfold anchoredJetFun
  have hg : ∀ i : Fin n, gradient ((a • u) i : AnchoredEuclidean n → ℝ) y =
      a • gradient (u i : AnchoredEuclidean n → ℝ) y :=
    fun i => gradient_smul_of_differentiableAt a
      ((ContDiff.differentiable (u i).2.1 (by simp)).differentiableAt)
  simp only [anchoredTestVector_smul, anchoredEnergyFun_smul, hg]
  rfl

/-- The jet of test tuples is linear in the tuple. -/
theorem anchoredVectorJet_add (χ : HsPairPotentials n.succPNat c)
    (μ : Measure (AnchoredEuclidean n)) [IsFiniteMeasure μ] (u v : AnchoredVectorTest n) :
    anchoredVectorJet χ μ (u + v) = anchoredVectorJet χ μ u + anchoredVectorJet χ μ v := by
  unfold anchoredVectorJet
  rw [← MemLp.toLp_add]
  exact MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun y => anchoredJetFun_add χ u v y)

/-- The jet of test tuples is homogeneous in the tuple. -/
theorem anchoredVectorJet_smul (χ : HsPairPotentials n.succPNat c)
    (μ : Measure (AnchoredEuclidean n)) [IsFiniteMeasure μ] (a : ℝ) (u : AnchoredVectorTest n) :
    anchoredVectorJet χ μ (a • u) = a • anchoredVectorJet χ μ u := by
  unfold anchoredVectorJet
  rw [← MemLp.toLp_const_smul]
  exact MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun y => anchoredJetFun_smul χ a u y)

/-- The linear map from anchored test tuples to jets. -/
def anchoredVectorJetLin (χ : HsPairPotentials n.succPNat c) (μ : Measure (AnchoredEuclidean n))
    [IsFiniteMeasure μ] : AnchoredVectorTest n →ₗ[ℝ] Lp (AnchoredJetPoint n) 2 μ where
  toFun := anchoredVectorJet χ μ
  map_add' := anchoredVectorJet_add χ μ
  map_smul' := anchoredVectorJet_smul χ μ

/-- The vector energy space `𝒱_{μ*}`: the closure of the jets of anchored
test tuples in the Hilbert space of `L²` jets. -/
def anchoredVectorSobolevSubmodule (χ : HsPairPotentials n.succPNat c)
    (μ : Measure (AnchoredEuclidean n)) [IsFiniteMeasure μ] :
    Submodule ℝ (Lp (AnchoredJetPoint n) 2 μ) :=
  (LinearMap.range (anchoredVectorJetLin χ μ)).topologicalClosure

/-- The vector energy space as a type. -/
abbrev AnchoredVectorSobolev (χ : HsPairPotentials n.succPNat c)
    (μ : Measure (AnchoredEuclidean n)) [IsFiniteMeasure μ] :=
  anchoredVectorSobolevSubmodule χ μ

instance (χ : HsPairPotentials n.succPNat c) (μ : Measure (AnchoredEuclidean n))
    [IsFiniteMeasure μ] : CompleteSpace (AnchoredVectorSobolev χ μ) := by
  unfold AnchoredVectorSobolev anchoredVectorSobolevSubmodule
  infer_instance

/-- The `i`-th value of an element of `L²` of jets, as an element of `L²(μ)`. -/
def anchoredJetValue (μ : Measure (AnchoredEuclidean n)) [IsFiniteMeasure μ] (i : Fin n) :
    Lp (AnchoredJetPoint n) 2 μ →L[ℝ] Lp ℝ 2 μ :=
  (jetValueL i).compLpL 2 μ

/-- The `k`-th particle value of an element of `L²` of jets, as an element of `L²(μ)`. -/
def anchoredParticleValue (μ : Measure (AnchoredEuclidean n)) [IsFiniteMeasure μ]
    (k : Fin (n.succPNat : ℕ)) : Lp (AnchoredJetPoint n) 2 μ →L[ℝ] Lp ℝ 2 μ :=
  (particleValueL k).compLpL 2 μ

/-- The `i`-th gradient of an element of `L²` of jets, as an element of `L²(μ; ℝ^n)`. -/
def anchoredJetGrad (μ : Measure (AnchoredEuclidean n)) [IsFiniteMeasure μ] (i : Fin n) :
    Lp (AnchoredJetPoint n) 2 μ →L[ℝ] Lp (AnchoredEuclidean n) 2 μ :=
  (jetGradL i).compLpL 2 μ

/-- The pair energy coordinate of an element of `L²` of jets, as an element of `L²(μ)`. -/
def anchoredJetEnergy (μ : Measure (AnchoredEuclidean n)) [IsFiniteMeasure μ]
    (p : HsPairIndex n.succPNat) : Lp (AnchoredJetPoint n) 2 μ →L[ℝ] Lp ℝ 2 μ :=
  (jetEnergyL p).compLpL 2 μ

/-- The particle value of a jet point is the `k`-th entry of the anchored lift of its values. -/
theorem particleValueL_jet (χ : HsPairPotentials n.succPNat c) (u : AnchoredVectorTest n)
    (y : AnchoredEuclidean n) (k : Fin (n.succPNat : ℕ)) :
    particleValueL k (anchoredJetFun χ u y) = anchorLift n (anchoredTestVector u y) k := by
  induction k using Fin.cases with
  | zero => simp [particleValueL, anchorLift_apply, anchorVector]
  | succ j => simp [particleValueL, jetValueL, anchorLift_apply, anchorVector, anchoredJetFun]


/-- The `i`-th value of a jet of a test tuple is the `i`-th component, almost everywhere. -/
theorem anchoredJetValue_ae (χ : HsPairPotentials n.succPNat c) (μ : Measure (AnchoredEuclidean n))
    [IsFiniteMeasure μ] (u : AnchoredVectorTest n) (i : Fin n) :
    (anchoredJetValue μ i (anchoredVectorJet χ μ u) : AnchoredEuclidean n → ℝ) =ᵐ[μ]
      fun y => (u i : AnchoredEuclidean n → ℝ) y := by
  unfold anchoredJetValue anchoredVectorJet
  filter_upwards [ContinuousLinearMap.coeFn_compLpL (jetValueL i)
      ((memLp_anchoredJetFun χ μ u).toLp (anchoredJetFun χ u)),
    MemLp.coeFn_toLp (memLp_anchoredJetFun χ μ u)] with y hy1 hy2
  rw [hy1, hy2]
  rfl

/-- The `i`-th gradient of a jet of a test tuple is the gradient of the `i`-th component, almost
everywhere. -/
theorem anchoredJetGrad_ae (χ : HsPairPotentials n.succPNat c) (μ : Measure (AnchoredEuclidean n))
    [IsFiniteMeasure μ] (u : AnchoredVectorTest n) (i : Fin n) :
    (anchoredJetGrad μ i (anchoredVectorJet χ μ u) : AnchoredEuclidean n → AnchoredEuclidean n)
      =ᵐ[μ] fun y => gradient (u i : AnchoredEuclidean n → ℝ) y := by
  unfold anchoredJetGrad anchoredVectorJet
  filter_upwards [ContinuousLinearMap.coeFn_compLpL (jetGradL i)
      ((memLp_anchoredJetFun χ μ u).toLp (anchoredJetFun χ u)),
    MemLp.coeFn_toLp (memLp_anchoredJetFun χ μ u)] with y hy1 hy2
  rw [hy1, hy2]
  rfl

/-- The pair energy coordinate of a jet of a test tuple is the pointwise energy, almost everywhere.
-/
theorem anchoredJetEnergy_ae (χ : HsPairPotentials n.succPNat c) (μ : Measure (AnchoredEuclidean n))
    [IsFiniteMeasure μ] (u : AnchoredVectorTest n) (p : HsPairIndex n.succPNat) :
    (anchoredJetEnergy μ p (anchoredVectorJet χ μ u) : AnchoredEuclidean n → ℝ) =ᵐ[μ]
      fun y => anchoredEnergyFun χ u y p := by
  unfold anchoredJetEnergy anchoredVectorJet
  filter_upwards [ContinuousLinearMap.coeFn_compLpL (jetEnergyL p)
      ((memLp_anchoredJetFun χ μ u).toLp (anchoredJetFun χ u)),
    MemLp.coeFn_toLp (memLp_anchoredJetFun χ μ u)] with y hy1 hy2
  rw [hy1, hy2]
  rfl

/-- The `k`-th particle value of a jet of a test tuple is the `k`-th entry of the anchored lift of
its values, almost everywhere. -/
theorem anchoredParticleValue_ae (χ : HsPairPotentials n.succPNat c)
    (μ : Measure (AnchoredEuclidean n)) [IsFiniteMeasure μ] (u : AnchoredVectorTest n)
    (k : Fin (n.succPNat : ℕ)) :
    (anchoredParticleValue μ k (anchoredVectorJet χ μ u) : AnchoredEuclidean n → ℝ) =ᵐ[μ]
      fun y => anchorLift n (anchoredTestVector u y) k := by
  unfold anchoredParticleValue anchoredVectorJet
  filter_upwards [ContinuousLinearMap.coeFn_compLpL (particleValueL k)
      ((memLp_anchoredJetFun χ μ u).toLp (anchoredJetFun χ u)),
    MemLp.coeFn_toLp (memLp_anchoredJetFun χ μ u)] with y hy1 hy2
  rw [hy1, hy2, particleValueL_jet]

/-- Every element of `𝒱_{μ*}` is a limit of jets of anchored test tuples. -/
theorem exists_seq_anchoredVectorJet (χ : HsPairPotentials n.succPNat c)
    (μ : Measure (AnchoredEuclidean n)) [IsFiniteMeasure μ] (Ψ : AnchoredVectorSobolev χ μ) :
    ∃ u : ℕ → AnchoredVectorTest n,
      Tendsto (fun k => anchoredVectorJet χ μ (u k)) atTop
        (𝓝 (Ψ : Lp (AnchoredJetPoint n) 2 μ)) := by
  have hmem : (Ψ : Lp (AnchoredJetPoint n) 2 μ) ∈ closure
      ((LinearMap.range (anchoredVectorJetLin χ μ) : Submodule ℝ (Lp (AnchoredJetPoint n) 2 μ)) :
        Set (Lp (AnchoredJetPoint n) 2 μ)) := by
    rw [← Submodule.topologicalClosure_coe]
    exact Ψ.2
  obtain ⟨x, hx, hlim⟩ := mem_closure_iff_seq_limit.mp hmem
  choose u hu using fun k => (LinearMap.mem_range.mp (hx k))
  refine ⟨u, ?_⟩
  have hx' : x = fun k => anchoredVectorJet χ μ (u k) := by
    funext k
    exact (hu k).symm
  rw [← hx']
  exact hlim

/-- The anchored pair weight is measurable in the anchored coordinate. -/
theorem measurable_anchoredEnergyWeight (χ : HsPairPotentials n.succPNat c)
    (p : HsPairIndex n.succPNat) :
    Measurable (fun y : AnchoredEuclidean n => hsEnergyWeight χ p (anchorLift n y)) := by
  unfold hsEnergyWeight
  refine Real.continuous_sqrt.measurable.comp (measurable_const.mul ?_)
  refine (measurable_deriv (deriv (χ.potential p.1.1 p.1.2))).comp ?_
  exact (((EuclideanSpace.proj p.1.2).continuous.comp (anchorLift n).continuous).measurable).sub
    ((EuclideanSpace.proj p.1.1).continuous.comp (anchorLift n).continuous).measurable

/-- Identification of the pair Hessian energy of `𝒱_{μ*}`: for every
element `Ψ` of the completion, the pair energy `p = (i, j)` is `√(2 χ_ij''(y_j - y_i)) (w_j - w_i)`
almost everywhere, where `w` is the vector of particle values of `Ψ`, with `w_0 = 0`. -/
theorem anchoredVectorSobolev_energy_ae (χ : HsPairPotentials n.succPNat c)
    (μ : Measure (AnchoredEuclidean n)) [IsFiniteMeasure μ] (Ψ : AnchoredVectorSobolev χ μ)
    (p : HsPairIndex n.succPNat) :
    (anchoredJetEnergy μ p (Ψ : Lp (AnchoredJetPoint n) 2 μ) : AnchoredEuclidean n → ℝ) =ᵐ[μ]
      fun y => hsEnergyWeight χ p (anchorLift n y) *
        ((anchoredParticleValue μ p.1.2 (Ψ : Lp (AnchoredJetPoint n) 2 μ) :
            AnchoredEuclidean n → ℝ) y -
          (anchoredParticleValue μ p.1.1 (Ψ : Lp (AnchoredJetPoint n) 2 μ) :
            AnchoredEuclidean n → ℝ) y) := by
  obtain ⟨u, hu⟩ := exists_seq_anchoredVectorJet χ μ Ψ
  have hv : ∀ k : Fin (n.succPNat : ℕ), Tendsto
      (fun j => anchoredParticleValue μ k (anchoredVectorJet χ μ (u j))) atTop
      (𝓝 (anchoredParticleValue μ k (Ψ : Lp (AnchoredJetPoint n) 2 μ))) :=
    fun k => ((anchoredParticleValue μ k).continuous.tendsto _).comp hu
  have he : Tendsto (fun j => anchoredJetEnergy μ p (anchoredVectorJet χ μ (u j))) atTop
      (𝓝 (anchoredJetEnergy μ p (Ψ : Lp (AnchoredJetPoint n) 2 μ))) :=
    ((anchoredJetEnergy μ p).continuous.tendsto _).comp hu
  exact WeightedSobolev.ae_eq_mul_diff_of_eLpNorm_tendsto
    (F := (anchoredJetEnergy μ p (Ψ : Lp (AnchoredJetPoint n) 2 μ) : AnchoredEuclidean n → ℝ))
    (s := fun y => hsEnergyWeight χ p (anchorLift n y))
    (Vj0 := (anchoredParticleValue μ p.1.2 (Ψ : Lp (AnchoredJetPoint n) 2 μ) :
      AnchoredEuclidean n → ℝ))
    (Vi0 := (anchoredParticleValue μ p.1.1 (Ψ : Lp (AnchoredJetPoint n) 2 μ) :
      AnchoredEuclidean n → ℝ))
    (G := fun j => (anchoredJetEnergy μ p (anchoredVectorJet χ μ (u j)) :
      AnchoredEuclidean n → ℝ))
    (Vj := fun j => (anchoredParticleValue μ p.1.2 (anchoredVectorJet χ μ (u j)) :
      AnchoredEuclidean n → ℝ))
    (Vi := fun j => (anchoredParticleValue μ p.1.1 (anchoredVectorJet χ μ (u j)) :
      AnchoredEuclidean n → ℝ))
    (Uj := fun j y => anchorLift n (anchoredTestVector (u j) y) p.1.2)
    (Ui := fun j y => anchorLift n (anchoredTestVector (u j) y) p.1.1)
    (measurable_anchoredEnergyWeight χ p)
    (fun y => Real.sqrt_nonneg _)
    (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _)
    (fun j => Lp.aestronglyMeasurable _) (fun j => Lp.aestronglyMeasurable _)
    (fun j => Lp.aestronglyMeasurable _)
    ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mp he)
    ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mp (hv p.1.2))
    ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mp (hv p.1.1))
    (fun j => by
      filter_upwards [anchoredJetEnergy_ae χ μ (u j) p] with y hy
      rw [hy]
      rfl)
    (fun j => anchoredParticleValue_ae χ μ (u j) p.1.2)
    (fun j => anchoredParticleValue_ae χ μ (u j) p.1.1)


/-- The graph predicate of smooth compactly supported anchored test functions, with `L²(μ)` values
and gradients. The weak derivatives of `𝒱_{μ*}` are identified through it. -/
def AnchoredGraphTest (μ : Measure (AnchoredEuclidean n)) (t : AnchoredEuclidean n → ℝ) : Prop :=
  WeightedSobolev.SmoothNearClosure (anchoredSimplex n) t ∧ MemLp t 2 μ ∧ MemLp (gradient t) 2 μ

/-- The gradient of a test function has compact support. -/
theorem hasCompactSupport_gradient_anchoredTest (f : anchoredTestSubmodule n) :
    HasCompactSupport (gradient (f : AnchoredEuclidean n → ℝ)) := by
  have hcs : HasCompactSupport (f : AnchoredEuclidean n → ℝ) := f.2.2.1
  exact (hcs.fderiv (𝕜 := ℝ)).comp_left
    (g := (InnerProductSpace.toDual ℝ (AnchoredEuclidean n)).symm) (map_zero _)

/-- An anchored test function satisfies the graph predicate. -/
theorem anchoredGraphTest_of_test (μ : Measure (AnchoredEuclidean n)) [IsFiniteMeasure μ]
    (f : anchoredTestSubmodule n) : AnchoredGraphTest μ (f : AnchoredEuclidean n → ℝ) := by
  have hf : ContDiff ℝ ∞ (f : AnchoredEuclidean n → ℝ) := f.2.1
  have hcs : HasCompactSupport (f : AnchoredEuclidean n → ℝ) := f.2.2.1
  exact ⟨⟨univ, isOpen_univ, subset_univ _, hf.contDiffOn⟩,
    hf.continuous.memLp_of_hasCompactSupport hcs,
    (continuous_gradient_anchoredTest f).memLp_of_hasCompactSupport
      (hasCompactSupport_gradient_anchoredTest f)⟩

/-- Enlarging the admissible test class preserves the graph predicate. -/
theorem isGraphH1_mono_of_test {μ : Measure (AnchoredEuclidean n)}
    {P Q : (AnchoredEuclidean n → ℝ) → Prop} (hPQ : ∀ t, P t → Q t)
    {F : AnchoredEuclidean n → ℝ} {G : AnchoredEuclidean n → AnchoredEuclidean n}
    (h : WeightedSobolev.IsGraphH1 μ P (fun t : AnchoredEuclidean n → ℝ => t) gradient F G) :
    WeightedSobolev.IsGraphH1 μ Q (fun t : AnchoredEuclidean n → ℝ => t) gradient F G := by
  obtain ⟨hv, hg, φ, hφ, hφv, hφg⟩ := h
  exact ⟨hv, hg, φ, fun k => hPQ _ (hφ k), hφv, hφg⟩

/-- The `i`-th scalar component of an element of `𝒱_{μ*}` is in the weighted Sobolev space, with
the `i`-th gradient as its weak gradient. -/
theorem isWeightedH1_anchoredVectorSobolev (χ : HsPairPotentials n.succPNat c)
    (μ : Measure (AnchoredEuclidean n)) [IsFiniteMeasure μ] (Ψ : AnchoredVectorSobolev χ μ)
    (i : Fin n) :
    WeightedSobolev.IsWeightedH1 μ (anchoredSimplex n)
      (anchoredJetValue μ i (Ψ : Lp (AnchoredJetPoint n) 2 μ) : AnchoredEuclidean n → ℝ)
      (anchoredJetGrad μ i (Ψ : Lp (AnchoredJetPoint n) 2 μ) :
        AnchoredEuclidean n → AnchoredEuclidean n) := by
  set Φ : Lp (AnchoredJetPoint n) 2 μ → WeightedSobolev.L2Jet μ (AnchoredEuclidean n) :=
    fun x => WithLp.toLp 2 (anchoredJetValue μ i x, anchoredJetGrad μ i x) with hΦ
  have hcont : Continuous Φ :=
    (WithLp.prod_continuous_toLp 2 _ _).comp
      ((anchoredJetValue μ i).continuous.prodMk (anchoredJetGrad μ i).continuous)
  have hsub : Φ '' (LinearMap.range (anchoredVectorJetLin χ μ) :
      Set (Lp (AnchoredJetPoint n) 2 μ)) ⊆
      WeightedSobolev.jetCore μ (AnchoredGraphTest μ) (fun t : AnchoredEuclidean n → ℝ => t)
        gradient := by
    rintro _ ⟨x, ⟨u, rfl⟩, rfl⟩
    have hfm : MemLp (u i : AnchoredEuclidean n → ℝ) 2 μ :=
      (anchoredGraphTest_of_test μ (u i)).2.1
    have hgm : MemLp (gradient (u i : AnchoredEuclidean n → ℝ)) 2 μ :=
      (anchoredGraphTest_of_test μ (u i)).2.2
    refine ⟨(u i : AnchoredEuclidean n → ℝ), anchoredGraphTest_of_test μ (u i), hfm, hgm, ?_⟩
    have hA : anchoredJetValue μ i (anchoredVectorJetLin χ μ u) = hfm.toLp _ :=
      Lp.ext ((anchoredJetValue_ae χ μ u i).trans hfm.coeFn_toLp.symm)
    have hB : anchoredJetGrad μ i (anchoredVectorJetLin χ μ u) = hgm.toLp _ :=
      Lp.ext ((anchoredJetGrad_ae χ μ u i).trans hgm.coeFn_toLp.symm)
    simp only [hΦ]
    rw [hA, hB]
  have hΨ : (Ψ : Lp (AnchoredJetPoint n) 2 μ) ∈ closure
      ((LinearMap.range (anchoredVectorJetLin χ μ) : Submodule ℝ (Lp (AnchoredJetPoint n) 2 μ)) :
        Set (Lp (AnchoredJetPoint n) 2 μ)) := by
    rw [← Submodule.topologicalClosure_coe]
    exact Ψ.2
  have hmem : Φ (Ψ : Lp (AnchoredJetPoint n) 2 μ) ∈ closure
      (WeightedSobolev.jetCore μ (AnchoredGraphTest μ) (fun t : AnchoredEuclidean n → ℝ => t)
        gradient) :=
    closure_mono hsub (image_closure_subset_closure_image hcont ⟨_, hΨ, rfl⟩)
  have hF : MemLp (anchoredJetValue μ i (Ψ : Lp (AnchoredJetPoint n) 2 μ) :
      AnchoredEuclidean n → ℝ) 2 μ := Lp.memLp _
  have hG : MemLp (anchoredJetGrad μ i (Ψ : Lp (AnchoredJetPoint n) 2 μ) :
      AnchoredEuclidean n → AnchoredEuclidean n) 2 μ := Lp.memLp _
  have hgraph := (WeightedSobolev.isGraphH1_iff_mem_closure
    (P := AnchoredGraphTest μ) (value := fun t : AnchoredEuclidean n → ℝ => t)
    (derivative := gradient) (fun t ht => ht.2.1) (fun t ht => ht.2.2) _ _ hF hG).mpr (by
      rw [MeasureTheory.Lp.toLp_coeFn _ hF, MeasureTheory.Lp.toLp_coeFn _ hG]
      exact hmem)
  exact isGraphH1_mono_of_test (fun t ht => ht.1) hgraph


/-- A jet point whose value, gradient and energy coordinates all vanish is zero. -/
theorem jetPoint_eq_zero (x : AnchoredJetPoint n) (hv : ∀ i : Fin n, jetValueL i x = 0)
    (hg : ∀ i : Fin n, jetGradL i x = 0)
    (he : ∀ p : HsPairIndex n.succPNat, jetEnergyL p x = 0) : x = 0 := by
  have h1 : x.ofLp.1 = 0 := by
    ext i
    exact hv i
  have hgv : x.ofLp.2.ofLp.1 = 0 := by
    refine PiLp.ext fun i => ?_
    exact hg i
  have hen : x.ofLp.2.ofLp.2 = 0 := by
    ext p
    exact he p
  have h2 : x.ofLp.2 = 0 := by
    rw [← WithLp.ofLp_eq_zero]
    exact Prod.ext hgv hen
  rw [← WithLp.ofLp_eq_zero]
  exact Prod.ext h1 h2

/-- Closability of `𝒱_{μ*}`: an element whose scalar values all vanish is
zero. The gradients vanish by the directional integration by parts
`anchoredH1_directional_integrationByParts`, and the energies vanish by the identification
`anchoredVectorSobolev_energy_ae`. -/
theorem anchoredVectorSobolev_eq_zero_of_values (χ : HsPairPotentials n.succPNat c) (hc : 0 < c)
    [IsFiniteMeasure (anchoredMeasureE χ)]
    (Ψ : AnchoredVectorSobolev χ (anchoredMeasureE χ))
    (hΨ : ∀ i : Fin n, anchoredJetValue (anchoredMeasureE χ) i
      (Ψ : Lp (AnchoredJetPoint n) 2 (anchoredMeasureE χ)) = 0) :
    Ψ = 0 := by
  -- the scalar values vanish almost everywhere
  have hval : ∀ i : Fin n, (anchoredJetValue (anchoredMeasureE χ) i
      (Ψ : Lp (AnchoredJetPoint n) 2 (anchoredMeasureE χ)) : AnchoredEuclidean n → ℝ)
        =ᵐ[anchoredMeasureE χ] 0 := by
    intro i
    rw [hΨ i]
    exact Lp.coeFn_zero ℝ 2 _
  -- the gradients vanish almost everywhere, by pairing with the coordinate vectors
  have hgrad : ∀ i : Fin n, (anchoredJetGrad (anchoredMeasureE χ) i
      (Ψ : Lp (AnchoredJetPoint n) 2 (anchoredMeasureE χ)) :
        AnchoredEuclidean n → AnchoredEuclidean n) =ᵐ[anchoredMeasureE χ] 0 := by
    intro i
    have hH := isWeightedH1_anchoredVectorSobolev χ (anchoredMeasureE χ) Ψ i
    have hcomp : ∀ k : Fin n, ∀ᵐ y ∂(anchoredMeasureE χ), inner ℝ
        (EuclideanSpace.single k (1 : ℝ))
        ((anchoredJetGrad (anchoredMeasureE χ) i
          (Ψ : Lp (AnchoredJetPoint n) 2 (anchoredMeasureE χ)) :
            AnchoredEuclidean n → AnchoredEuclidean n) y) = 0 := by
      intro k
      have ha : ∀ᵐ y ∂(anchoredMeasureE χ), ((innerSL ℝ (EuclideanSpace.single k (1 : ℝ))).compLpL
          2 (anchoredMeasureE χ) (anchoredJetGrad (anchoredMeasureE χ) i
            (Ψ : Lp (AnchoredJetPoint n) 2 (anchoredMeasureE χ))) : AnchoredEuclidean n → ℝ) y
          = inner ℝ (EuclideanSpace.single k (1 : ℝ)) ((anchoredJetGrad (anchoredMeasureE χ) i
            (Ψ : Lp (AnchoredJetPoint n) 2 (anchoredMeasureE χ)) :
              AnchoredEuclidean n → AnchoredEuclidean n) y) := by
        filter_upwards [ContinuousLinearMap.coeFn_compLpL
          (innerSL ℝ (EuclideanSpace.single k (1 : ℝ)))
          (anchoredJetGrad (anchoredMeasureE χ) i (Ψ : Lp (AnchoredJetPoint n) 2 (anchoredMeasureE χ)))]
          with y hy
        rw [hy]
        rfl
      have hzero : (innerSL ℝ (EuclideanSpace.single k (1 : ℝ))).compLpL 2
          (anchoredMeasureE χ) (anchoredJetGrad (anchoredMeasureE χ) i
            (Ψ : Lp (AnchoredJetPoint n) 2 (anchoredMeasureE χ))) = 0 := by
        refine Internal.eq_zero_of_chart_tests (anchoredMeasureE χ) (fun y => y)
          MeasurableEmbedding.id (anchoredSimplex n) (isOpen_anchoredSimplex n)
          (ae_mem_anchoredSimplex χ) _ ?_
        intro g hg hgcs hgsupp
        have hint := anchoredH1_directional_integrationByParts χ hc hH hg hgcs hgsupp
          (EuclideanSpace.single k (1 : ℝ))
        calc ∫ x, g ((fun y => y) x) * ((innerSL ℝ (EuclideanSpace.single k (1 : ℝ))).compLpL 2
              (anchoredMeasureE χ) (anchoredJetGrad (anchoredMeasureE χ) i
                (Ψ : Lp (AnchoredJetPoint n) 2 (anchoredMeasureE χ))) : AnchoredEuclidean n → ℝ) x
              ∂(anchoredMeasureE χ)
            = ∫ y, g y * inner ℝ (((anchoredJetGrad (anchoredMeasureE χ) i
                (Ψ : Lp (AnchoredJetPoint n) 2 (anchoredMeasureE χ)) :
                  AnchoredEuclidean n → AnchoredEuclidean n) y))
                (EuclideanSpace.single k (1 : ℝ)) ∂(anchoredMeasureE χ) := by
              refine integral_congr_ae ?_
              filter_upwards [ha] with y hy
              simp only [hy]
              rw [real_inner_comm]
          _ = ∫ y, (anchoredJetValue (anchoredMeasureE χ) i
                (Ψ : Lp (AnchoredJetPoint n) 2 (anchoredMeasureE χ)) : AnchoredEuclidean n → ℝ) y *
                (g y * fderiv ℝ (hsAnchoredHamiltonianE χ) y (EuclideanSpace.single k (1 : ℝ)) -
                  fderiv ℝ g y (EuclideanSpace.single k (1 : ℝ))) ∂(anchoredMeasureE χ) := hint
          _ = 0 := by
              refine integral_eq_zero_of_ae ?_
              filter_upwards [hval i] with y hy
              simp [hy]
      have hae : ((innerSL ℝ (EuclideanSpace.single k (1 : ℝ))).compLpL 2
          (anchoredMeasureE χ) (anchoredJetGrad (anchoredMeasureE χ) i
            (Ψ : Lp (AnchoredJetPoint n) 2 (anchoredMeasureE χ))) : AnchoredEuclidean n → ℝ)
          =ᵐ[anchoredMeasureE χ] 0 := by
        rw [hzero]
        exact Lp.coeFn_zero ℝ 2 _
      filter_upwards [hae, ha] with y h1 h2
      rw [← h2]
      simpa using h1
    filter_upwards [ae_all_iff.mpr hcomp] with y hy
    ext k
    simpa [EuclideanSpace.inner_single_left] using hy k
  -- the particle values vanish almost everywhere
  have hpart : ∀ k : Fin (n.succPNat : ℕ), (anchoredParticleValue (anchoredMeasureE χ) k
      (Ψ : Lp (AnchoredJetPoint n) 2 (anchoredMeasureE χ)) : AnchoredEuclidean n → ℝ)
        =ᵐ[anchoredMeasureE χ] 0 := by
    intro k
    induction k using Fin.cases with
    | zero =>
      change (((particleValueL 0).compLpL 2 (anchoredMeasureE χ)
        (Ψ : Lp (AnchoredJetPoint n) 2 (anchoredMeasureE χ)) : Lp ℝ 2 (anchoredMeasureE χ)) :
          AnchoredEuclidean n → ℝ) =ᵐ[anchoredMeasureE χ] 0
      filter_upwards [ContinuousLinearMap.coeFn_compLpL (particleValueL 0)
        (Ψ : Lp (AnchoredJetPoint n) 2 (anchoredMeasureE χ))] with y hy
      rw [hy]
      rfl
    | succ j => exact hval j
  -- the energies vanish almost everywhere, by the energy identity
  have hen : ∀ p : HsPairIndex n.succPNat, (anchoredJetEnergy (anchoredMeasureE χ) p
      (Ψ : Lp (AnchoredJetPoint n) 2 (anchoredMeasureE χ)) : AnchoredEuclidean n → ℝ)
        =ᵐ[anchoredMeasureE χ] 0 := by
    intro p
    filter_upwards [anchoredVectorSobolev_energy_ae χ (anchoredMeasureE χ) Ψ p,
      hpart p.1.2, hpart p.1.1] with y h1 h2 h3
    rw [h1, h2, h3]
    simp
  -- the coordinates of the limit vanish almost everywhere
  have hvc : ∀ i : Fin n, ∀ᵐ y ∂(anchoredMeasureE χ), jetValueL i
      ((Ψ : Lp (AnchoredJetPoint n) 2 (anchoredMeasureE χ)) y) = 0 := by
    intro i
    have hcoe : (anchoredJetValue (anchoredMeasureE χ) i
        (Ψ : Lp (AnchoredJetPoint n) 2 (anchoredMeasureE χ)) : AnchoredEuclidean n → ℝ) =ᵐ[
          anchoredMeasureE χ] fun y => jetValueL i
            ((Ψ : Lp (AnchoredJetPoint n) 2 (anchoredMeasureE χ)) y) :=
      ContinuousLinearMap.coeFn_compLpL (jetValueL i)
        (Ψ : Lp (AnchoredJetPoint n) 2 (anchoredMeasureE χ))
    filter_upwards [hcoe, hval i] with y h1 h2
    rw [← h1]
    simpa using h2
  have hgc : ∀ i : Fin n, ∀ᵐ y ∂(anchoredMeasureE χ), jetGradL i
      ((Ψ : Lp (AnchoredJetPoint n) 2 (anchoredMeasureE χ)) y) = 0 := by
    intro i
    have hcoe : (anchoredJetGrad (anchoredMeasureE χ) i
        (Ψ : Lp (AnchoredJetPoint n) 2 (anchoredMeasureE χ)) :
          AnchoredEuclidean n → AnchoredEuclidean n) =ᵐ[anchoredMeasureE χ] fun y => jetGradL i
            ((Ψ : Lp (AnchoredJetPoint n) 2 (anchoredMeasureE χ)) y) :=
      ContinuousLinearMap.coeFn_compLpL (jetGradL i)
        (Ψ : Lp (AnchoredJetPoint n) 2 (anchoredMeasureE χ))
    filter_upwards [hcoe, hgrad i] with y h1 h2
    rw [← h1]
    simpa using h2
  have hec : ∀ p : HsPairIndex n.succPNat, ∀ᵐ y ∂(anchoredMeasureE χ), jetEnergyL p
      ((Ψ : Lp (AnchoredJetPoint n) 2 (anchoredMeasureE χ)) y) = 0 := by
    intro p
    have hcoe : (anchoredJetEnergy (anchoredMeasureE χ) p
        (Ψ : Lp (AnchoredJetPoint n) 2 (anchoredMeasureE χ)) : AnchoredEuclidean n → ℝ)
          =ᵐ[anchoredMeasureE χ] fun y => jetEnergyL p
            ((Ψ : Lp (AnchoredJetPoint n) 2 (anchoredMeasureE χ)) y) :=
      ContinuousLinearMap.coeFn_compLpL (jetEnergyL p)
        (Ψ : Lp (AnchoredJetPoint n) 2 (anchoredMeasureE χ))
    filter_upwards [hcoe, hen p] with y h1 h2
    rw [← h1]
    simpa using h2
  -- hence the limit is zero in `L²`
  have hzero : (Ψ : Lp (AnchoredJetPoint n) 2 (anchoredMeasureE χ)) = 0 := by
    refine Lp.ext ?_
    filter_upwards [ae_all_iff.mpr hvc, ae_all_iff.mpr hgc, ae_all_iff.mpr hec,
      Lp.coeFn_zero (AnchoredJetPoint n) 2 (anchoredMeasureE χ)] with y h1 h2 h3 h4
    rw [h4]
    exact jetPoint_eq_zero _ h1 h2 h3
  exact Subtype.ext hzero

/-- The pair energy vector of an element of `L²` of jets, as an element of `L²(μ)`. -/
def anchoredJetEnergyVec (μ : Measure (AnchoredEuclidean n)) [IsFiniteMeasure μ] :
    Lp (AnchoredJetPoint n) 2 μ →L[ℝ] Lp (EuclideanSpace ℝ (HsPairIndex n.succPNat)) 2 μ :=
  jetEnergyVecL.compLpL 2 μ

/-- The continuous extension of `q_{μ*}` to `𝒱_{μ*}`: the sum of the
`L²(μ)` inner products of the componentwise gradients, plus the `L²(μ)` inner product of the pair
energies. On jets of test tuples it is the integrand of the vector quadratic form. -/
def anchoredVectorSobolevForm (μ : Measure (AnchoredEuclidean n)) [IsFiniteMeasure μ]
    (Ψ Φ : Lp (AnchoredJetPoint n) 2 μ) : ℝ :=
  ∑ i : Fin n, inner ℝ (anchoredJetGrad μ i Ψ) (anchoredJetGrad μ i Φ) +
    inner ℝ (anchoredJetEnergyVec μ Ψ) (anchoredJetEnergyVec μ Φ)

/-- The pair energy vector of a jet of a test tuple is the pointwise energy, almost everywhere. -/
theorem anchoredJetEnergyVec_ae (χ : HsPairPotentials n.succPNat c)
    (μ : Measure (AnchoredEuclidean n)) [IsFiniteMeasure μ] (u : AnchoredVectorTest n) :
    (anchoredJetEnergyVec μ (anchoredVectorJet χ μ u) :
        AnchoredEuclidean n → EuclideanSpace ℝ (HsPairIndex n.succPNat)) =ᵐ[μ]
      fun y => anchoredEnergyFun χ u y := by
  unfold anchoredJetEnergyVec anchoredVectorJet
  filter_upwards [ContinuousLinearMap.coeFn_compLpL jetEnergyVecL
      ((memLp_anchoredJetFun χ μ u).toLp (anchoredJetFun χ u)),
    MemLp.coeFn_toLp (memLp_anchoredJetFun χ μ u)] with y hy1 hy2
  rw [hy1, hy2]
  rfl

/-- The pointwise gradient pairing of two anchored test tuples is integrable. -/
theorem integrable_anchoredGradInner (χ : HsPairPotentials n.succPNat c)
    (μ : Measure (AnchoredEuclidean n)) [IsFiniteMeasure μ] (u h : AnchoredVectorTest n)
    (i : Fin n) : Integrable (fun y : AnchoredEuclidean n =>
      inner ℝ (gradient (u i : AnchoredEuclidean n → ℝ) y)
        (gradient (h i : AnchoredEuclidean n → ℝ) y)) μ :=
  (L2.integrable_inner (anchoredJetGrad μ i (anchoredVectorJet χ μ u))
    (anchoredJetGrad μ i (anchoredVectorJet χ μ h))).congr (by
      filter_upwards [anchoredJetGrad_ae χ μ u i, anchoredJetGrad_ae χ μ h i] with y h1 h2
      rw [h1, h2])

/-- The pointwise energy pairing of two anchored test tuples is integrable. -/
theorem integrable_anchoredEnergyInner (χ : HsPairPotentials n.succPNat c)
    (μ : Measure (AnchoredEuclidean n)) [IsFiniteMeasure μ] (u h : AnchoredVectorTest n) :
    Integrable (fun y : AnchoredEuclidean n =>
      inner ℝ (anchoredEnergyFun χ u y) (anchoredEnergyFun χ h y)) μ :=
  (L2.integrable_inner (anchoredJetEnergyVec μ (anchoredVectorJet χ μ u))
    (anchoredJetEnergyVec μ (anchoredVectorJet χ μ h))).congr (by
      filter_upwards [anchoredJetEnergyVec_ae χ μ u, anchoredJetEnergyVec_ae χ μ h] with y h1 h2
      rw [h1, h2])

/-- The anchored form `q_{μ*}` is the integral of the gradient and energy
pairings, since `μ*` lives on the simplex where the Hessian identity holds. -/
theorem anchoredVectorForm_eq_integral (χ : HsPairPotentials n.succPNat c) (hc : 0 < c)
    (u h : AnchoredVectorTest n) :
    anchoredVectorForm χ u h = ∫ y, (∑ i : Fin n, inner ℝ
        (gradient (u i : AnchoredEuclidean n → ℝ) y) (gradient (h i : AnchoredEuclidean n → ℝ) y) +
      inner ℝ (anchoredEnergyFun χ u y) (anchoredEnergyFun χ h y)) ∂(anchoredMeasureE χ) := by
  unfold anchoredVectorForm
  refine integral_congr_ae ?_
  filter_upwards [ae_mem_anchoredSimplex χ] with y hy
  exact anchoredVectorFormIntegrand_eq χ hc (anchorLift_mem_chamber hy)

/-- On jets of test tuples, the extended form is the integral of the anchored integrand of
the vector quadratic form. This identifies the continuous extension with `q_{μ*}`. -/
theorem anchoredVectorSobolevForm_jet (χ : HsPairPotentials n.succPNat c) (hc : 0 < c)
    [IsFiniteMeasure (anchoredMeasureE χ)] (u h : AnchoredVectorTest n) :
    anchoredVectorSobolevForm (anchoredMeasureE χ) (anchoredVectorJet χ (anchoredMeasureE χ) u)
      (anchoredVectorJet χ (anchoredMeasureE χ) h) = anchoredVectorForm χ u h := by
  have hgrad : ∀ i : Fin n, inner ℝ (anchoredJetGrad (anchoredMeasureE χ) i
      (anchoredVectorJet χ (anchoredMeasureE χ) u))
        (anchoredJetGrad (anchoredMeasureE χ) i (anchoredVectorJet χ (anchoredMeasureE χ) h)) =
      ∫ y, inner ℝ (gradient (u i : AnchoredEuclidean n → ℝ) y)
        (gradient (h i : AnchoredEuclidean n → ℝ) y) ∂(anchoredMeasureE χ) := fun i => by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [anchoredJetGrad_ae χ (anchoredMeasureE χ) u i,
      anchoredJetGrad_ae χ (anchoredMeasureE χ) h i] with y h1 h2
    rw [h1, h2]
  have hen : inner ℝ (anchoredJetEnergyVec (anchoredMeasureE χ)
      (anchoredVectorJet χ (anchoredMeasureE χ) u))
        (anchoredJetEnergyVec (anchoredMeasureE χ) (anchoredVectorJet χ (anchoredMeasureE χ) h)) =
      ∫ y, inner ℝ (anchoredEnergyFun χ u y) (anchoredEnergyFun χ h y) ∂(anchoredMeasureE χ) := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [anchoredJetEnergyVec_ae χ (anchoredMeasureE χ) u,
      anchoredJetEnergyVec_ae χ (anchoredMeasureE χ) h] with y h1 h2
    rw [h1, h2]
  unfold anchoredVectorSobolevForm
  rw [hen, Finset.sum_congr rfl (fun i _ => hgrad i), anchoredVectorForm_eq_integral χ hc u h,
    integral_add (integrable_finsetSum _ fun i _ => integrable_anchoredGradInner χ _ u h i)
      (integrable_anchoredEnergyInner χ _ u h),
    integral_finsetSum _ fun i _ => integrable_anchoredGradInner χ _ u h i]

/-- The pointwise squared norm of the jet of a test tuple: the squared values, the squared
gradients and the squared pair energy. -/
theorem inner_anchoredJetFun_self (χ : HsPairPotentials n.succPNat c) (u : AnchoredVectorTest n)
    (y : AnchoredEuclidean n) :
    inner ℝ (anchoredJetFun χ u y) (anchoredJetFun χ u y) =
      ∑ i : Fin n, (u i : AnchoredEuclidean n → ℝ) y ^ 2 +
        (∑ i : Fin n, inner ℝ (gradient (u i : AnchoredEuclidean n → ℝ) y)
            (gradient (u i : AnchoredEuclidean n → ℝ) y) +
          inner ℝ (anchoredEnergyFun χ u y) (anchoredEnergyFun χ u y)) := by
  unfold anchoredJetFun
  simp only [WithLp.prod_inner_apply, PiLp.inner_apply, anchoredTestVector,
    RCLike.inner_apply, conj_trivial, sq]

/-- The squared values of a test tuple are integrable. -/
theorem integrable_sum_sq_anchoredTest (μ : Measure (AnchoredEuclidean n)) [IsFiniteMeasure μ]
    (u : AnchoredVectorTest n) :
    Integrable (fun y : AnchoredEuclidean n =>
      ∑ i : Fin n, (u i : AnchoredEuclidean n → ℝ) y ^ 2) μ := by
  refine Continuous.integrable_of_hasCompactSupport
    (continuous_finsetSum _ fun i _ => ((u i).2.1.continuous).pow 2) ?_
  refine HasCompactSupport.intro (isCompact_anchoredSupportUnion u) fun y hy => ?_
  refine Finset.sum_eq_zero fun i _ => ?_
  simp [image_eq_zero_of_notMem_tsupport (fun hi => hy (mem_iUnion.mpr ⟨i, hi⟩))]

/-- The norm identity of `𝒱_{μ*}`: the jet of an anchored test tuple has
squared norm `∫|u|² dμ* + q_{μ*}(u, u)`. -/
theorem norm_sq_anchoredVectorJet (χ : HsPairPotentials n.succPNat c) (hc : 0 < c)
    [IsFiniteMeasure (anchoredMeasureE χ)] (u : AnchoredVectorTest n) :
    ‖anchoredVectorJet χ (anchoredMeasureE χ) u‖ ^ 2 =
      ∫ y, ∑ i : Fin n, (u i : AnchoredEuclidean n → ℝ) y ^ 2 ∂(anchoredMeasureE χ) +
        anchoredVectorForm χ u u := by
  have hcoe : ⇑(anchoredVectorJet χ (anchoredMeasureE χ) u) =ᵐ[anchoredMeasureE χ]
      anchoredJetFun χ u :=
    MemLp.coeFn_toLp (memLp_anchoredJetFun χ (anchoredMeasureE χ) u)
  have hrest : Integrable (fun y : AnchoredEuclidean n =>
      ∑ i : Fin n, inner ℝ (gradient (u i : AnchoredEuclidean n → ℝ) y)
          (gradient (u i : AnchoredEuclidean n → ℝ) y) +
        inner ℝ (anchoredEnergyFun χ u y) (anchoredEnergyFun χ u y)) (anchoredMeasureE χ) :=
    (integrable_finsetSum _ fun i _ => integrable_anchoredGradInner χ _ u u i).add
      (integrable_anchoredEnergyInner χ _ u u)
  have hcongr : (fun a => inner ℝ (anchoredVectorJet χ (anchoredMeasureE χ) u a)
      (anchoredVectorJet χ (anchoredMeasureE χ) u a)) =ᵐ[anchoredMeasureE χ]
        fun y => inner ℝ (anchoredJetFun χ u y) (anchoredJetFun χ u y) := by
    filter_upwards [hcoe] with y hy
    rw [hy]
  rw [anchoredVectorForm_eq_integral χ hc u u, ← real_inner_self_eq_norm_sq, L2.inner_def,
    integral_congr_ae hcongr]
  simp_rw [inner_anchoredJetFun_self]
  exact integral_add (integrable_sum_sq_anchoredTest _ u) hrest

end Riesz1

end
