/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.VectorEnergyForm
public import Riesz1.HelfferSjostrand.SobolevClosability
public import Riesz1.ToMathlib.WeightedSobolev.TruncatedIdentity

/-!
# The vector energy space on the Gibbs measure

Consider the Gibbs probability `μ` of an admissible pair Hamiltonian. The space
`𝒱_μ` is the completion of `𝒟_N^N` for `‖u‖² = ∫|u|² dμ + q_μ(u, u)`. It is realized as the
closure, in the Hilbert space of jets, of the images of test tuples. A jet consists of

* the `N` scalar Sobolev components `HsSobolev μ`, whose values and weak
  gradients give `∫|u|²` and the gradient part of `q_μ`.
* the pair Hessian energy `(√(2 χ_ij''(y_j - y_i)) (u_j - u_i))_{i<j}` in `L²(μ)`, whose
  squared norm is the Hessian part `∫ u · ∇²H u dμ` of `q_μ`.

The completion is closable: a limit with zero values is zero. The file proves this by the scalar
closability of `SobolevClosability`, together with the identification of the Hessian energy
`F_ij = √(2 χ_ij''(y_j - y_i)) (w_j - w_i)` of every limit with values `w`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal ContDiff

namespace Riesz1

variable {N : ℕ+} {c : ℝ}

/-- The scalar Sobolev class of a test function, in the completion `HsSobolev μ`. -/
def hsTestSobolev (μ : Measure (HsConfiguration N)) [IsFiniteMeasure μ] :
    hsTestSubmodule N →ₗ[ℝ] HsSobolev μ :=
  (hsSobolevOfSmooth μ).comp <| LinearMap.codRestrict (hsSmoothCore N) (hsTestSubmodule N).subtype
    fun u => HsTestSubmodule.smoothOnClosure u.2

theorem hsSobolevValue_hsSobolevOfSmooth (μ : Measure (HsConfiguration N)) [IsFiniteMeasure μ]
    (f : hsSmoothCore N) :
    hsSobolevValue μ (hsSobolevOfSmooth μ f) = (f.2.memLp_value μ).toLp (hsSmoothValue f.1) :=
  rfl

/-- The value of a test class is the test function evaluated at the fundamental lift. -/
theorem hsSobolevValue_hsTestSobolev (μ : Measure (HsConfiguration N)) [IsFiniteMeasure μ]
    (u : hsTestSubmodule N) :
    (hsSobolevValue μ (hsTestSobolev μ u) : HsConfiguration N → ℝ) =ᵐ[μ]
      fun y => (u : HsEuclidean N → ℝ) (hsLiftPoint N y) := by
  change ((hsSobolevOfSmooth μ ⟨(u : HsEuclidean N → ℝ), _⟩ |> hsSobolevValue μ) :
    HsConfiguration N → ℝ) =ᵐ[μ] _
  rw [hsSobolevValue_hsSobolevOfSmooth]
  exact MemLp.coeFn_toLp _

/-- The weight of the pair Hessian energy is measurable in the point. -/
theorem measurable_hsEnergyWeight (χ : HsPairPotentials N c) (p : HsPairIndex N) :
    Measurable (fun y : HsEuclidean N => hsEnergyWeight χ p y) := by
  unfold hsEnergyWeight
  refine Real.continuous_sqrt.measurable.comp (measurable_const.mul ?_)
  refine (measurable_deriv (deriv (χ.potential p.1.1 p.1.2))).comp ?_
  exact ((EuclideanSpace.proj p.1.2).continuous.measurable).sub
    ((EuclideanSpace.proj p.1.1).continuous.measurable)

/-- The pair Hessian energy of a test tuple at the fundamental lift of a configuration. -/
def hsTestEnergyFun (χ : HsPairPotentials N c) (u : HsVectorTest N) (y : HsConfiguration N) :
    EuclideanSpace ℝ (HsPairIndex N) :=
  hsHessianEnergy χ (hsLiftPoint N y) (hsTestVector u (hsLiftPoint N y))

theorem measurable_hsTestEnergyFun (χ : HsPairPotentials N c) (u : HsVectorTest N) :
    Measurable (hsTestEnergyFun χ u) := by
  have hw : ∀ p : HsPairIndex N, Measurable (fun y : HsConfiguration N =>
      hsEnergyWeight χ p (hsLiftPoint N y)) := fun p =>
    (measurable_hsEnergyWeight χ p).comp (measurable_hsLiftPoint N)
  have hv : ∀ i : Fin (N : ℕ), Measurable (fun y : HsConfiguration N =>
      (u i : HsEuclidean N → ℝ) (hsLiftPoint N y)) := fun i =>
    ((u i).2.1.continuous.measurable).comp (measurable_hsLiftPoint N)
  have hmeas : Measurable (fun y : HsConfiguration N =>
      (fun p : HsPairIndex N => hsEnergyWeight χ p (hsLiftPoint N y) *
        (hsTestVector u (hsLiftPoint N y) p.1.2 - hsTestVector u (hsLiftPoint N y) p.1.1))) := by
    refine measurable_pi_iff.mpr fun p => (hw p).mul ?_
    exact ((hv p.1.2).sub (hv p.1.1))
  exact (EuclideanSpace.equiv (HsPairIndex N) ℝ).symm.continuous.measurable.comp hmeas

theorem memLp_hsTestEnergyFun (χ : HsPairPotentials N c) (hN : 2 ≤ (N : ℕ)) (hc : 0 < c)
    (μ : Measure (HsConfiguration N)) [IsFiniteMeasure μ] (u : HsVectorTest N) :
    MemLp (hsTestEnergyFun χ u) 2 μ := by
  obtain ⟨B, hB⟩ := hsHessianEnergy_bounded χ hc hN (fun i => (u i : HsEuclidean N → ℝ))
    (fun i => (u i).2)
  exact MemLp.of_bound (measurable_hsTestEnergyFun χ u).aestronglyMeasurable B
    (Filter.Eventually.of_forall fun y => hB _ (hsLiftPoint_mem_fundamentalRegion N y))

/-- The ambient Hilbert space of the vector energy jets: `N` scalar Sobolev components together
with the pair Hessian energy in `L²(μ)`. -/
abbrev HsVectorJet (μ : Measure (HsConfiguration N)) [IsFiniteMeasure μ] :=
  WithLp 2 (PiLp 2 (fun _ : Fin (N : ℕ) => HsSobolev μ) ×
    Lp (EuclideanSpace ℝ (HsPairIndex N)) 2 μ)

/-- The jet of a test tuple: its scalar Sobolev components and its Hessian energy. -/
def hsVectorJet (χ : HsPairPotentials N c) (hN : 2 ≤ (N : ℕ)) (hc : 0 < c)
    (μ : Measure (HsConfiguration N)) [IsFiniteMeasure μ] (u : HsVectorTest N) :
    HsVectorJet μ :=
  WithLp.toLp 2 (WithLp.toLp 2 (fun i => hsTestSobolev μ (u i)),
    (memLp_hsTestEnergyFun χ hN hc μ u).toLp (hsTestEnergyFun χ u))

theorem hsTestVector_add (u v : HsVectorTest N) (x : HsEuclidean N) :
    hsTestVector (u + v) x = hsTestVector u x + hsTestVector v x := by
  ext i
  simp [hsTestVector]

theorem hsTestVector_smul (a : ℝ) (u : HsVectorTest N) (x : HsEuclidean N) :
    hsTestVector (a • u) x = a • hsTestVector u x := by
  ext i
  simp [hsTestVector]

theorem hsVectorJet_add (χ : HsPairPotentials N c) (hN : 2 ≤ (N : ℕ)) (hc : 0 < c)
    (μ : Measure (HsConfiguration N)) [IsFiniteMeasure μ] (u v : HsVectorTest N) :
    hsVectorJet χ hN hc μ (u + v) = hsVectorJet χ hN hc μ u + hsVectorJet χ hN hc μ v := by
  have hE : hsTestEnergyFun χ (u + v) = hsTestEnergyFun χ u + hsTestEnergyFun χ v := by
    funext y
    simp only [hsTestEnergyFun, Pi.add_apply, hsTestVector_add]
    exact hsHessianEnergy_add χ _ _ _
  have hA : (WithLp.toLp 2 (fun i => hsTestSobolev μ ((u + v) i)) : PiLp 2 _) =
      WithLp.toLp 2 (fun i => hsTestSobolev μ (u i)) +
        WithLp.toLp 2 (fun i => hsTestSobolev μ (v i)) := by
    ext i
    simp [map_add]
  have hB : (memLp_hsTestEnergyFun χ hN hc μ (u + v)).toLp (hsTestEnergyFun χ (u + v)) =
      (memLp_hsTestEnergyFun χ hN hc μ u).toLp (hsTestEnergyFun χ u) +
        (memLp_hsTestEnergyFun χ hN hc μ v).toLp (hsTestEnergyFun χ v) := by
    rw [← MemLp.toLp_add]
    exact MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun y => congrFun hE y)
  unfold hsVectorJet
  rw [← WithLp.toLp_add, Prod.mk_add_mk, hA, hB]

theorem hsVectorJet_smul (χ : HsPairPotentials N c) (hN : 2 ≤ (N : ℕ)) (hc : 0 < c)
    (μ : Measure (HsConfiguration N)) [IsFiniteMeasure μ] (a : ℝ) (u : HsVectorTest N) :
    hsVectorJet χ hN hc μ (a • u) = a • hsVectorJet χ hN hc μ u := by
  have hE : hsTestEnergyFun χ (a • u) = a • hsTestEnergyFun χ u := by
    funext y
    simp only [hsTestEnergyFun, Pi.smul_apply, hsTestVector_smul]
    exact hsHessianEnergy_smul χ _ _ _
  have hA : (WithLp.toLp 2 (fun i => hsTestSobolev μ ((a • u) i)) : PiLp 2 _) =
      a • WithLp.toLp 2 (fun i => hsTestSobolev μ (u i)) := by
    ext i
    simp [map_smul]
  have hB : (memLp_hsTestEnergyFun χ hN hc μ (a • u)).toLp (hsTestEnergyFun χ (a • u)) =
      a • (memLp_hsTestEnergyFun χ hN hc μ u).toLp (hsTestEnergyFun χ u) := by
    rw [← MemLp.toLp_const_smul]
    exact MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun y => congrFun hE y)
  unfold hsVectorJet
  rw [← WithLp.toLp_smul, Prod.smul_mk, hA, hB]

/-- The linear map from test tuples to vector energy jets. -/
def hsVectorJetLin (χ : HsPairPotentials N c) (hN : 2 ≤ (N : ℕ)) (hc : 0 < c)
    (μ : Measure (HsConfiguration N)) [IsFiniteMeasure μ] :
    HsVectorTest N →ₗ[ℝ] HsVectorJet μ where
  toFun := hsVectorJet χ hN hc μ
  map_add' := hsVectorJet_add χ hN hc μ
  map_smul' := hsVectorJet_smul χ hN hc μ

/-- The vector energy space `𝒱_μ`: the closure of the jets of test
tuples in the Hilbert space of jets. -/
def hsVectorSobolevSubmodule (χ : HsPairPotentials N c) (hN : 2 ≤ (N : ℕ)) (hc : 0 < c)
    (μ : Measure (HsConfiguration N)) [IsFiniteMeasure μ] : Submodule ℝ (HsVectorJet μ) :=
  (LinearMap.range (hsVectorJetLin χ hN hc μ)).topologicalClosure

/-- The vector energy space as a type. -/
abbrev HsVectorSobolev (χ : HsPairPotentials N c) (hN : 2 ≤ (N : ℕ)) (hc : 0 < c)
    (μ : Measure (HsConfiguration N)) [IsFiniteMeasure μ] :=
  hsVectorSobolevSubmodule χ hN hc μ

instance (χ : HsPairPotentials N c) (hN : 2 ≤ (N : ℕ)) (hc : 0 < c)
    (μ : Measure (HsConfiguration N)) [IsFiniteMeasure μ] :
    CompleteSpace (HsVectorSobolev χ hN hc μ) := by
  unfold HsVectorSobolev hsVectorSobolevSubmodule
  infer_instance

/-- The `i`-th scalar value of a jet, as an element of `L²(μ)`. -/
def hsJetValue (μ : Measure (HsConfiguration N)) [IsFiniteMeasure μ] (i : Fin (N : ℕ)) :
    HsVectorJet μ →L[ℝ] Lp ℝ 2 μ :=
  (hsSobolevValue μ).comp
    ((PiLp.proj 2 (fun _ : Fin (N : ℕ) => HsSobolev μ) i).comp (WithLp.fstL 2 ℝ _ _))

/-- The pair Hessian energy of a jet, as an element of `L²(μ)`. -/
def hsJetEnergy (μ : Measure (HsConfiguration N)) [IsFiniteMeasure μ] (p : HsPairIndex N) :
    HsVectorJet μ →L[ℝ] Lp ℝ 2 μ :=
  (EuclideanSpace.proj (𝕜 := ℝ) p).compLpL 2 μ ∘L WithLp.sndL 2 ℝ _ _

theorem hsJetValue_hsVectorJet (χ : HsPairPotentials N c) (hN : 2 ≤ (N : ℕ)) (hc : 0 < c)
    (μ : Measure (HsConfiguration N)) [IsFiniteMeasure μ] (u : HsVectorTest N) (i : Fin (N : ℕ)) :
    hsJetValue μ i (hsVectorJet χ hN hc μ u) = hsSobolevValue μ (hsTestSobolev μ (u i)) := rfl

/-- The energy component of a jet of test tuples, as the projection of its second entry. -/
theorem hsJetEnergy_hsVectorJet_eq (χ : HsPairPotentials N c) (hN : 2 ≤ (N : ℕ)) (hc : 0 < c)
    (μ : Measure (HsConfiguration N)) [IsFiniteMeasure μ] (u : HsVectorTest N)
    (p : HsPairIndex N) :
    hsJetEnergy μ p (hsVectorJet χ hN hc μ u) =
      (EuclideanSpace.proj (𝕜 := ℝ) p).compLpL 2 μ
        ((memLp_hsTestEnergyFun χ hN hc μ u).toLp (hsTestEnergyFun χ u)) := rfl

/-- The energy of a jet of test tuples is the pointwise energy, almost everywhere. -/
theorem hsJetEnergy_hsVectorJet_ae (χ : HsPairPotentials N c) (hN : 2 ≤ (N : ℕ)) (hc : 0 < c)
    (μ : Measure (HsConfiguration N)) [IsFiniteMeasure μ] (u : HsVectorTest N)
    (p : HsPairIndex N) :
    (hsJetEnergy μ p (hsVectorJet χ hN hc μ u) : HsConfiguration N → ℝ) =ᵐ[μ]
      fun y => hsTestEnergyFun χ u y p := by
  rw [hsJetEnergy_hsVectorJet_eq]
  filter_upwards [ContinuousLinearMap.coeFn_compLpL (EuclideanSpace.proj (𝕜 := ℝ) p)
      ((memLp_hsTestEnergyFun χ hN hc μ u).toLp (hsTestEnergyFun χ u)),
    MemLp.coeFn_toLp (memLp_hsTestEnergyFun χ hN hc μ u)] with y hy1 hy2
  rw [hy1, hy2]
  rfl

/-- Every element of `𝒱_μ` is a limit of jets of test tuples. -/
theorem exists_seq_hsVectorJet (χ : HsPairPotentials N c) (hN : 2 ≤ (N : ℕ)) (hc : 0 < c)
    (μ : Measure (HsConfiguration N)) [IsFiniteMeasure μ] (Ψ : HsVectorSobolev χ hN hc μ) :
    ∃ u : ℕ → HsVectorTest N,
      Tendsto (fun k => hsVectorJet χ hN hc μ (u k)) atTop (𝓝 (Ψ : HsVectorJet μ)) := by
  have hmem : (Ψ : HsVectorJet μ) ∈ closure ((LinearMap.range (hsVectorJetLin χ hN hc μ) :
      Submodule ℝ (HsVectorJet μ)) : Set (HsVectorJet μ)) := by
    rw [← Submodule.topologicalClosure_coe]
    exact Ψ.2
  obtain ⟨x, hx, hlim⟩ := mem_closure_iff_seq_limit.mp hmem
  choose u hu using fun k => (LinearMap.mem_range.mp (hx k))
  refine ⟨u, ?_⟩
  have hx' : x = fun k => hsVectorJet χ hN hc μ (u k) := by
    funext k
    exact (hu k).symm
  rw [← hx']
  exact hlim

/-- Identification of the Hessian energy of `𝒱_μ`: for every element `Ψ`
of the completion, the pair energy is `√(2 χ_ij''(y_j - y_i)) (w_j - w_i)` almost everywhere, where
`w` is the vector of scalar values of `Ψ`. -/
theorem hsVectorSobolev_energy_ae (χ : HsPairPotentials N c) (hN : 2 ≤ (N : ℕ)) (hc : 0 < c)
    (μ : Measure (HsConfiguration N)) [IsFiniteMeasure μ] (Ψ : HsVectorSobolev χ hN hc μ)
    (p : HsPairIndex N) :
    (hsJetEnergy μ p (Ψ : HsVectorJet μ) : HsConfiguration N → ℝ) =ᵐ[μ] fun y =>
      hsEnergyWeight χ p (hsLiftPoint N y) *
        ((hsJetValue μ p.1.2 (Ψ : HsVectorJet μ) : HsConfiguration N → ℝ) y -
          (hsJetValue μ p.1.1 (Ψ : HsVectorJet μ) : HsConfiguration N → ℝ) y) := by
  obtain ⟨u, hu⟩ := exists_seq_hsVectorJet χ hN hc μ Ψ
  have hv : ∀ l : Fin (N : ℕ), Tendsto (fun k => hsJetValue μ l (hsVectorJet χ hN hc μ (u k)))
      atTop (𝓝 (hsJetValue μ l (Ψ : HsVectorJet μ))) := fun l =>
    ((hsJetValue μ l).continuous.tendsto _).comp hu
  have he : Tendsto (fun k => hsJetEnergy μ p (hsVectorJet χ hN hc μ (u k)))
      atTop (𝓝 (hsJetEnergy μ p (Ψ : HsVectorJet μ))) :=
    ((hsJetEnergy μ p).continuous.tendsto _).comp hu
  exact WeightedSobolev.ae_eq_mul_diff_of_eLpNorm_tendsto
    (F := (hsJetEnergy μ p (Ψ : HsVectorJet μ) : HsConfiguration N → ℝ))
    (s := fun y => hsEnergyWeight χ p (hsLiftPoint N y))
    (Vj0 := (hsJetValue μ p.1.2 (Ψ : HsVectorJet μ) : HsConfiguration N → ℝ))
    (Vi0 := (hsJetValue μ p.1.1 (Ψ : HsVectorJet μ) : HsConfiguration N → ℝ))
    (G := fun k => (hsJetEnergy μ p (hsVectorJet χ hN hc μ (u k)) : HsConfiguration N → ℝ))
    (Vj := fun k => (hsJetValue μ p.1.2 (hsVectorJet χ hN hc μ (u k)) :
      HsConfiguration N → ℝ))
    (Vi := fun k => (hsJetValue μ p.1.1 (hsVectorJet χ hN hc μ (u k)) :
      HsConfiguration N → ℝ))
    (Uj := fun k y => (u k p.1.2 : HsEuclidean N → ℝ) (hsLiftPoint N y))
    (Ui := fun k y => (u k p.1.1 : HsEuclidean N → ℝ) (hsLiftPoint N y))
    ((measurable_hsEnergyWeight χ p).comp (measurable_hsLiftPoint N))
    (fun y => Real.sqrt_nonneg _)
    (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _)
    (fun k => Lp.aestronglyMeasurable _) (fun k => Lp.aestronglyMeasurable _)
    (fun k => Lp.aestronglyMeasurable _)
    ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mp he)
    ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mp (hv p.1.2))
    ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mp (hv p.1.1))
    (fun k => by
      filter_upwards [hsJetEnergy_hsVectorJet_ae χ hN hc μ (u k) p] with y hy
      rw [hy]
      rfl)
    (fun k => by
      filter_upwards [hsSobolevValue_hsTestSobolev μ (u k p.1.2)] with y hy
      exact hy)
    (fun k => by
      filter_upwards [hsSobolevValue_hsTestSobolev μ (u k p.1.1)] with y hy
      exact hy)

/-- Closability of `𝒱_μ` on the Gibbs probability: an element whose
scalar values all vanish is zero. The scalar components vanish by `hsSobolevValue_injective`, and
the Hessian energy vanishes by the identification `hsVectorSobolev_energy_ae`. -/
theorem hsVectorSobolev_eq_zero_of_values (χ : HsPairPotentials N c) (hN : 2 ≤ (N : ℕ))
    (hc : 0 < c)
    (Ψ : HsVectorSobolev χ hN hc (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)))
    (hΨ : ∀ i : Fin (N : ℕ),
      hsJetValue (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)) i
        (Ψ : HsVectorJet (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))) = 0) :
    Ψ = 0 := by
  set μ : Measure (HsConfiguration N) := (hsQuotientGibbsProbability χ hc :
    Measure (HsConfiguration N)) with hμ
  have hcomp : ∀ i : Fin (N : ℕ), (Ψ : HsVectorJet μ).ofLp.1 i = 0 := by
    intro i
    apply hsSobolevValue_injective χ hc
    rw [map_zero]
    exact hΨ i
  have hcomp' : (Ψ : HsVectorJet μ).ofLp.1 = 0 := by
    ext i
    simpa using hcomp i
  have hz : ∀ l : Fin (N : ℕ), (hsJetValue μ l (Ψ : HsVectorJet μ) : HsConfiguration N → ℝ) =ᵐ[μ] 0 :=
    fun l => by
      rw [hΨ l]
      exact Lp.coeFn_zero ℝ 2 μ
  have henergy : ∀ p : HsPairIndex N, hsJetEnergy μ p (Ψ : HsVectorJet μ) = 0 := by
    intro p
    refine Lp.ext ?_
    filter_upwards [hsVectorSobolev_energy_ae χ hN hc μ Ψ p, hz p.1.2, hz p.1.1,
      Lp.coeFn_zero ℝ 2 μ] with y h1 h2 h3 _
    simp [h1, h2, h3]
  have hsnd : (Ψ : HsVectorJet μ).ofLp.2 = 0 := by
    refine Lp.ext ?_
    have hp : ∀ p : HsPairIndex N, ∀ᵐ y ∂μ, (Ψ : HsVectorJet μ).ofLp.2 y p = 0 := fun p => by
      have h2 : (EuclideanSpace.proj (𝕜 := ℝ) p).compLpL 2 μ (Ψ : HsVectorJet μ).ofLp.2 = 0 :=
        henergy p
      filter_upwards [ContinuousLinearMap.coeFn_compLpL (EuclideanSpace.proj (𝕜 := ℝ) p)
        (Ψ : HsVectorJet μ).ofLp.2, (by rw [h2]; exact Lp.coeFn_zero ℝ 2 μ :
          (((EuclideanSpace.proj (𝕜 := ℝ) p).compLpL 2 μ (Ψ : HsVectorJet μ).ofLp.2 :
            Lp ℝ 2 μ) : HsConfiguration N → ℝ) =ᵐ[μ] 0)] with y hy1 hy2
      rw [hy1] at hy2
      simpa using hy2
    filter_upwards [ae_all_iff.mpr hp] with y hy
    ext p
    simpa using hy p
  apply Subtype.ext
  apply (WithLp.equiv 2 _).injective
  apply Prod.ext
  · simpa using hcomp'
  · simpa using hsnd

/-- The gradient of the scalar class of a test function is its gradient, almost everywhere. -/
theorem hsSobolevGradient_hsTestSobolev_ae (μ : Measure (HsConfiguration N)) [IsFiniteMeasure μ]
    (u : hsTestSubmodule N) :
    (hsSobolevGradient μ (hsTestSobolev μ u) : HsConfiguration N → HsEuclidean N) =ᵐ[μ]
      fun y => gradient (u : HsEuclidean N → ℝ) (hsLiftPoint N y) := by
  change ((hsSobolevGradient μ (hsSobolevOfSmooth μ ⟨(u : HsEuclidean N → ℝ),
    HsTestSubmodule.smoothOnClosure u.2⟩) : Lp (HsEuclidean N) 2 μ) : HsConfiguration N → _) =ᵐ[μ] _
  have hG : hsSobolevGradient μ (hsSobolevOfSmooth μ ⟨(u : HsEuclidean N → ℝ),
      HsTestSubmodule.smoothOnClosure u.2⟩) =
      ((HsTestSubmodule.smoothOnClosure u.2).memLp_gradient μ).toLp
        (hsSmoothGradient ⟨(u : HsEuclidean N → ℝ), HsTestSubmodule.smoothOnClosure u.2⟩) :=
    rfl
  rw [hG]
  exact MemLp.coeFn_toLp _

/-- The vector form on `𝒱_μ`: the continuous extension of `q_μ`, given by
the inner products of the componentwise gradients and of the Hessian energies. -/
def hsVectorSobolevForm (χ : HsPairPotentials N c) (hN : 2 ≤ (N : ℕ)) (hc : 0 < c)
    (μ : Measure (HsConfiguration N)) [IsFiniteMeasure μ]
    (Ψ Ψ' : HsVectorSobolev χ hN hc μ) : ℝ :=
  ∑ i : Fin (N : ℕ), inner ℝ (hsSobolevGradient μ ((Ψ : HsVectorJet μ).ofLp.1 i))
      (hsSobolevGradient μ ((Ψ' : HsVectorJet μ).ofLp.1 i)) +
    inner ℝ ((Ψ : HsVectorJet μ).ofLp.2) ((Ψ' : HsVectorJet μ).ofLp.2)

/-- The jet of a test tuple lies in the vector energy space. -/
theorem hsVectorJet_mem_submodule (χ : HsPairPotentials N c) (hN : 2 ≤ (N : ℕ)) (hc : 0 < c)
    (μ : Measure (HsConfiguration N)) [IsFiniteMeasure μ] (u : HsVectorTest N) :
    hsVectorJet χ hN hc μ u ∈ hsVectorSobolevSubmodule χ hN hc μ := by
  unfold hsVectorSobolevSubmodule
  exact Submodule.le_topologicalClosure _ ⟨u, rfl⟩

/-- The jet of a test tuple, as an element of the vector energy space. -/
def hsVectorJetElt (χ : HsPairPotentials N c) (hN : 2 ≤ (N : ℕ)) (hc : 0 < c)
    (μ : Measure (HsConfiguration N)) [IsFiniteMeasure μ] (u : HsVectorTest N) :
    HsVectorSobolev χ hN hc μ :=
  ⟨hsVectorJet χ hN hc μ u, hsVectorJet_mem_submodule χ hN hc μ u⟩

/-- On test tuples the extended form is the integral formula. -/
theorem hsVectorSobolevForm_jet (χ : HsPairPotentials N c) (hN : 2 ≤ (N : ℕ)) (hc : 0 < c)
    (μ : Measure (HsConfiguration N)) [IsFiniteMeasure μ] (u v : HsVectorTest N) :
    hsVectorSobolevForm χ hN hc μ (hsVectorJetElt χ hN hc μ u) (hsVectorJetElt χ hN hc μ v) =
      vectorForm χ μ u v := by
  have hgI : ∀ i : Fin (N : ℕ), Integrable (fun y : HsConfiguration N =>
      inner ℝ (gradient (u i : HsEuclidean N → ℝ) (hsLiftPoint N y))
        (gradient (v i : HsEuclidean N → ℝ) (hsLiftPoint N y))) μ := fun i =>
    (L2.integrable_inner (hsSobolevGradient μ (hsTestSobolev μ (u i)))
      (hsSobolevGradient μ (hsTestSobolev μ (v i)))).congr (by
        filter_upwards [hsSobolevGradient_hsTestSobolev_ae μ (u i),
          hsSobolevGradient_hsTestSobolev_ae μ (v i)] with y h1 h2
        rw [h1, h2])
  have heI : Integrable (fun y : HsConfiguration N =>
      inner ℝ (hsTestEnergyFun χ u y) (hsTestEnergyFun χ v y)) μ :=
    (L2.integrable_inner ((memLp_hsTestEnergyFun χ hN hc μ u).toLp (hsTestEnergyFun χ u))
      ((memLp_hsTestEnergyFun χ hN hc μ v).toLp (hsTestEnergyFun χ v))).congr (by
        filter_upwards [MemLp.coeFn_toLp (memLp_hsTestEnergyFun χ hN hc μ u),
          MemLp.coeFn_toLp (memLp_hsTestEnergyFun χ hN hc μ v)] with y h1 h2
        rw [h1, h2])
  have hpt : (fun y : HsConfiguration N => vectorFormIntegrand χ u v (hsLiftPoint N y)) =
      fun y => (∑ i : Fin (N : ℕ), inner ℝ (gradient (u i : HsEuclidean N → ℝ) (hsLiftPoint N y))
        (gradient (v i : HsEuclidean N → ℝ) (hsLiftPoint N y))) +
          inner ℝ (hsTestEnergyFun χ u y) (hsTestEnergyFun χ v y) := by
    funext y
    unfold vectorFormIntegrand
    rw [hsTestEnergyFun, hsTestEnergyFun, inner_hsHessianEnergy χ hc
      (hsLiftPoint_mem_chamber N y)]
  have hgrad : ∀ i : Fin (N : ℕ), inner ℝ (hsSobolevGradient μ (hsTestSobolev μ (u i)))
      (hsSobolevGradient μ (hsTestSobolev μ (v i))) =
        ∫ y, inner ℝ (gradient (u i : HsEuclidean N → ℝ) (hsLiftPoint N y))
          (gradient (v i : HsEuclidean N → ℝ) (hsLiftPoint N y)) ∂μ := fun i => by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hsSobolevGradient_hsTestSobolev_ae μ (u i),
      hsSobolevGradient_hsTestSobolev_ae μ (v i)] with y h1 h2
    rw [h1, h2]
  have hen : inner ℝ ((memLp_hsTestEnergyFun χ hN hc μ u).toLp (hsTestEnergyFun χ u))
      ((memLp_hsTestEnergyFun χ hN hc μ v).toLp (hsTestEnergyFun χ v)) =
        ∫ y, inner ℝ (hsTestEnergyFun χ u y) (hsTestEnergyFun χ v y) ∂μ := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp (memLp_hsTestEnergyFun χ hN hc μ u),
      MemLp.coeFn_toLp (memLp_hsTestEnergyFun χ hN hc μ v)] with y h1 h2
    rw [h1, h2]
  unfold vectorForm
  rw [hpt, integral_add (integrable_finsetSum _ fun i _ => hgI i) heI,
    integral_finsetSum _ fun i _ => hgI i]
  unfold hsVectorSobolevForm hsVectorJetElt
  show ∑ i : Fin (N : ℕ), inner ℝ (hsSobolevGradient μ (hsTestSobolev μ (u i)))
      (hsSobolevGradient μ (hsTestSobolev μ (v i))) +
    inner ℝ ((memLp_hsTestEnergyFun χ hN hc μ u).toLp (hsTestEnergyFun χ u))
      ((memLp_hsTestEnergyFun χ hN hc μ v).toLp (hsTestEnergyFun χ v)) =
    ∑ i : Fin (N : ℕ), (∫ y, inner ℝ (gradient (u i : HsEuclidean N → ℝ) (hsLiftPoint N y))
      (gradient (v i : HsEuclidean N → ℝ) (hsLiftPoint N y)) ∂μ) +
      ∫ y, inner ℝ (hsTestEnergyFun χ u y) (hsTestEnergyFun χ v y) ∂μ
  rw [hen]
  congr 1
  exact Finset.sum_congr rfl fun i _ => hgrad i

end Riesz1

end
