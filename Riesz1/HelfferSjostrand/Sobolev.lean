/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.SobolevLifts
public import Riesz1.HelfferSjostrand.SettingGibbs
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Add

/-!
# The periodic weighted Sobolev graph completion

The completion, as a closed subspace of the
Hilbert space of values and gradients. Its norm is the prescribed energy
norm. Gradient closability, and hence injectivity of the value projection,
is a separate analytic claim and is not proved here.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Topology
open scoped ENNReal ContDiff

namespace Riesz1

theorem HsSmoothOnClosure.differentiableAt {N : ℕ+} {f : HsEuclidean N → ℝ}
    (hf : HsSmoothOnClosure N f) {x : HsEuclidean N} (hx : x ∈ hsChamber N) :
    DifferentiableAt ℝ f x := by
  obtain ⟨_, U, hU, hs, hfU⟩ := hf
  exact (hfU.differentiableOn (by norm_num)).differentiableAt
    (hU.mem_nhds (hs (subset_closure hx)))

theorem hsSmoothGradient_add {N : ℕ+} {f g : HsEuclidean N → ℝ}
    (hf : HsSmoothOnClosure N f) (hg : HsSmoothOnClosure N g) :
    hsSmoothGradient ⟨f + g, hf.add hg⟩ =
      hsSmoothGradient ⟨f, hf⟩ + hsSmoothGradient ⟨g, hg⟩ := by
  funext x
  dsimp [hsSmoothGradient]
  rw [gradient, fderiv_add (hf.differentiableAt (hsLiftPoint_mem_chamber N x))
    (hg.differentiableAt (hsLiftPoint_mem_chamber N x)), map_add]
  rfl

theorem hsSmoothGradient_smul {N : ℕ+} {f : HsEuclidean N → ℝ}
    (hf : HsSmoothOnClosure N f) (a : ℝ) :
    hsSmoothGradient ⟨a • f, hf.smul a⟩ = a • hsSmoothGradient ⟨f, hf⟩ := by
  funext x
  dsimp [hsSmoothGradient]
  rw [gradient, fderiv_const_smul (hf.differentiableAt (hsLiftPoint_mem_chamber N x)), map_smul]
  rfl

variable {N : ℕ+} (μ : Measure (HsConfiguration N)) [IsFiniteMeasure μ]

/-- The smooth value/gradient map into the ambient Hilbert space. -/
def hsSmoothJet : hsSmoothCore N →ₗ[ℝ] WeightedSobolev.L2Jet μ (HsEuclidean N) where
  toFun f := WithLp.toLp 2 ((f.property.memLp_value μ).toLp (hsSmoothValue f.val),
    (f.property.memLp_gradient μ).toLp (hsSmoothGradient f))
  map_add' f g := by
    apply (WithLp.equiv 2 _).injective
    apply Prod.ext
    · exact MemLp.toLp_add (f.property.memLp_value μ) (g.property.memLp_value μ)
    · change ((f.property.add g.property).memLp_gradient μ).toLp
        (hsSmoothGradient (f + g)) = _
      exact (MemLp.toLp_congr _ ((f.property.memLp_gradient μ).add
        (g.property.memLp_gradient μ)) (Filter.Eventually.of_forall
          (congrFun (hsSmoothGradient_add f.property g.property)))).trans
        (MemLp.toLp_add (f.property.memLp_gradient μ) (g.property.memLp_gradient μ))
  map_smul' a f := by
    apply (WithLp.equiv 2 _).injective
    apply Prod.ext
    · exact MemLp.toLp_const_smul a (f.property.memLp_value μ)
    · change ((f.property.smul a).memLp_gradient μ).toLp (hsSmoothGradient (a • f)) = _
      exact (MemLp.toLp_congr _ ((f.property.memLp_gradient μ).const_smul a)
        (Filter.Eventually.of_forall (congrFun (hsSmoothGradient_smul f.property a)))).trans
        (MemLp.toLp_const_smul a (f.property.memLp_gradient μ))

theorem hsSmoothJet_range :
    (LinearMap.range (hsSmoothJet μ) : Set (WeightedSobolev.L2Jet μ (HsEuclidean N))) =
      WeightedSobolev.jetCore μ (fun _ : hsSmoothCore N => True)
        (fun f => hsSmoothValue f.val) hsSmoothGradient := by
  ext u
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨f, trivial, f.property.memLp_value μ, f.property.memLp_gradient μ, rfl⟩
  · rintro ⟨f, hf, hv, hg, rfl⟩
    exact ⟨f, rfl⟩

/-- The closed smooth-jet subspace. Its Hilbert norm is the Sobolev norm. -/
def hsSobolevSubmodule : Submodule ℝ (WeightedSobolev.L2Jet μ (HsEuclidean N)) :=
  (hsSmoothJet μ).range.topologicalClosure

/-- Completion of smooth periodic functions for the weighted `H¹` norm. -/
abbrev HsSobolev := hsSobolevSubmodule μ

instance : CompleteSpace (HsSobolev μ) := by
  unfold HsSobolev hsSobolevSubmodule
  infer_instance

/-- The canonical map from the smooth core into its completion. -/
def hsSobolevOfSmooth : hsSmoothCore N →ₗ[ℝ] HsSobolev μ :=
  (hsSmoothJet μ).codRestrict (hsSobolevSubmodule μ)
    (fun f => Submodule.le_topologicalClosure _ ⟨f, rfl⟩)

theorem denseRange_hsSobolevOfSmooth : DenseRange (hsSobolevOfSmooth μ) := by
  rw [denseRange_iff_closure_range]
  apply Set.eq_univ_of_forall
  intro f
  rw [(Topology.IsEmbedding.subtypeVal : Topology.IsEmbedding
    (Subtype.val : HsSobolev μ → WeightedSobolev.L2Jet μ (HsEuclidean N))).closure_eq_preimage_closure_image]
  change f.val ∈ closure (Subtype.val '' range (hsSobolevOfSmooth μ))
  have heq : Subtype.val '' range (hsSobolevOfSmooth μ) = range (hsSmoothJet μ) := by
    ext u
    constructor
    · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
      exact ⟨g, rfl⟩
    · rintro ⟨g, rfl⟩
      exact ⟨hsSobolevOfSmooth μ g, ⟨g, rfl⟩, rfl⟩
  rw [heq, ← LinearMap.coe_range]
  exact f.property

/-- The continuous projection of a Sobolev jet to its `L²` function. -/
def hsSobolevValue : HsSobolev μ →L[ℝ] Lp ℝ 2 μ :=
  WithLp.fstL 2 ℝ _ _ ∘L (hsSobolevSubmodule μ).subtypeL

/-- The continuous projection to the limiting gradient. -/
def hsSobolevGradient : HsSobolev μ →L[ℝ] Lp (HsEuclidean N) 2 μ :=
  WithLp.sndL 2 ℝ _ _ ∘L (hsSobolevSubmodule μ).subtypeL

/-- The sequential criterion uses precisely the generalized encoding. -/
theorem hsSobolev_iff_graph (F : HsConfiguration N → ℝ)
    (G : HsConfiguration N → HsEuclidean N) (hF : MemLp F 2 μ) (hG : MemLp G 2 μ) :
    WithLp.toLp 2 (hF.toLp F, hG.toLp G) ∈ hsSobolevSubmodule μ ↔
      WeightedSobolev.IsGraphH1 μ (fun _ : hsSmoothCore N => True)
        (fun f => hsSmoothValue f.val) hsSmoothGradient F G := by
  change WithLp.toLp 2 (hF.toLp F, hG.toLp G) ∈
    closure ((hsSmoothJet μ).range : Set _) ↔ _
  rw [hsSmoothJet_range]
  exact (WeightedSobolev.isGraphH1_iff_mem_closure (fun f _ => f.property.memLp_value μ)
    (fun f _ => f.property.memLp_gradient μ) F G hF hG).symm

/-- The completion has exactly the prescribed sum-of-squares norm. -/
theorem hsSobolev_norm_sq (f : HsSobolev μ) :
    ‖f‖ ^ 2 = ‖hsSobolevValue μ f‖ ^ 2 + ‖hsSobolevGradient μ f‖ ^ 2 :=
  WithLp.prod_norm_sq_eq_of_L2 f.val

/-- The completed norm is the integral of the sum of squares. -/
theorem hsSobolev_norm_sq_eq_integral (f : HsSobolev μ) :
    ‖f‖ ^ 2 = ∫ x, (hsSobolevValue μ f x) ^ 2 + ‖hsSobolevGradient μ f x‖ ^ 2 ∂μ := by
  rw [integral_add (Lp.memLp _).integrable_sq (Lp.memLp _).norm.integrable_sq,
    hsSobolev_norm_sq, ← real_inner_self_eq_norm_sq (hsSobolevValue μ f),
    ← real_inner_self_eq_norm_sq (hsSobolevGradient μ f), L2.inner_def, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

/-- The scalar energy form on the whole completed Sobolev space. -/
def hsDirichletForm (f h : HsSobolev μ) : ℝ :=
  inner ℝ (hsSobolevGradient μ f) (hsSobolevGradient μ h)

theorem hsDirichletForm_eq_integral (f h : HsSobolev μ) :
    hsDirichletForm μ f h =
      ∫ x, inner ℝ (hsSobolevGradient μ f x) (hsSobolevGradient μ h x) ∂μ := rfl

theorem continuous_hsDirichletForm (f : HsSobolev μ) :
    Continuous (hsDirichletForm μ f) :=
  continuous_const.inner (hsSobolevGradient μ).continuous

theorem hsDirichletForm_add_left (f g h : HsSobolev μ) :
    hsDirichletForm μ (f + g) h = hsDirichletForm μ f h + hsDirichletForm μ g h := by
  simp only [hsDirichletForm, map_add, inner_add_left]

theorem hsDirichletForm_smul_left (a : ℝ) (f h : HsSobolev μ) :
    hsDirichletForm μ (a • f) h = a * hsDirichletForm μ f h := by
  simp only [hsDirichletForm, map_smul, real_inner_smul_left]

theorem hsDirichletForm_symmetric (f h : HsSobolev μ) :
    hsDirichletForm μ f h = hsDirichletForm μ h f := real_inner_comm _ _

theorem hsDirichletForm_nonnegative (f : HsSobolev μ) : 0 ≤ hsDirichletForm μ f f :=
  real_inner_self_nonneg

end Riesz1

end
