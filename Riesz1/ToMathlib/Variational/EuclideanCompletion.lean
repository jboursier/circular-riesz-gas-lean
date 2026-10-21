/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.WeightedSobolev.VariationalPairing
public import Mathlib.Topology.Algebra.Module.ClosedSubmodule
public import Mathlib.Analysis.Calculus.FDeriv.Add

/-! # A Hilbert realization of the Euclidean weighted Sobolev completion

On a bounded open domain, with a finite measure carried by it, the
sequential Sobolev predicate is exactly a closed linear subspace of the
Hilbert space of value–gradient jets.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Topology
open scoped ContDiff

namespace Riesz1.Variational

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Smooth functions near the closed domain form a real vector space. -/
@[reducible] def smoothCore (U : Set E) : Submodule ℝ (E → ℝ) where
  carrier := {f | WeightedSobolev.SmoothNearClosure U f}
  zero_mem' := ⟨univ, isOpen_univ, subset_univ _, contDiffOn_const⟩
  add_mem' := by
    rintro f g ⟨A, hA, hUA, hf⟩ ⟨B, hB, hUB, hg⟩
    exact ⟨A ∩ B, hA.inter hB, subset_inter hUA hUB,
      (hf.mono inter_subset_left).add (hg.mono inter_subset_right)⟩
  smul_mem' := by
    rintro a f ⟨A, hA, hUA, hf⟩
    exact ⟨A, hA, hUA, hf.const_smul a⟩

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem smoothCore_differentiableAt {U : Set E} (f : smoothCore U) {x : E} (hx : x ∈ U) :
    DifferentiableAt ℝ f.val x := by
  obtain ⟨A, hA, hUA, hf⟩ := f.property
  exact (hf.differentiableOn (by norm_num)).differentiableAt
    (hA.mem_nhds (hUA (subset_closure hx)))

variable (μ : Measure E) [IsFiniteMeasure μ] (U : Set E)
  (hU : Bornology.IsBounded U) (hμ : ∀ᵐ x ∂μ, x ∈ U)

/-- The smooth value–gradient map into the Hilbert space of jets. -/
def smoothJet : smoothCore U →ₗ[ℝ] WeightedSobolev.L2Jet μ E where
  toFun f := WithLp.toLp 2
    (((WeightedSobolev.memLp_of_smoothNearClosure hU hμ f.property).1).toLp f.val,
     ((WeightedSobolev.memLp_of_smoothNearClosure hU hμ f.property).2).toLp (gradient f.val))
  map_add' f g := by
    apply (WithLp.equiv 2 _).injective
    apply Prod.ext
    · exact MemLp.toLp_add
        (WeightedSobolev.memLp_of_smoothNearClosure hU hμ f.property).1
        (WeightedSobolev.memLp_of_smoothNearClosure hU hμ g.property).1
    · change (WeightedSobolev.memLp_of_smoothNearClosure hU hμ (f + g).property).2.toLp
          (gradient (f + g).val) =
        (WeightedSobolev.memLp_of_smoothNearClosure hU hμ f.property).2.toLp (gradient f.val) +
        (WeightedSobolev.memLp_of_smoothNearClosure hU hμ g.property).2.toLp (gradient g.val)
      apply Lp.ext
      have hf := (WeightedSobolev.memLp_of_smoothNearClosure hU hμ f.property).2.coeFn_toLp
      have hg := (WeightedSobolev.memLp_of_smoothNearClosure hU hμ g.property).2.coeFn_toLp
      have hfg := (WeightedSobolev.memLp_of_smoothNearClosure hU hμ (f + g).property).2.coeFn_toLp
      filter_upwards [hμ, hf, hg, hfg, Lp.coeFn_add
        ((WeightedSobolev.memLp_of_smoothNearClosure hU hμ f.property).2.toLp (gradient f.val))
        ((WeightedSobolev.memLp_of_smoothNearClosure hU hμ g.property).2.toLp (gradient g.val))]
        with x hx hfx hgx hfgx hadd
      change _ = _ at hadd
      rw [hadd]
      change _ = _ at hfgx
      rw [hfgx]
      simp only [Pi.add_apply]
      rw [hfx, hgx]
      change gradient (f.val + g.val) x = gradient f.val x + gradient g.val x
      rw [gradient, fderiv_add (smoothCore_differentiableAt f hx)
        (smoothCore_differentiableAt g hx), map_add]
      rfl
  map_smul' a f := by
    apply (WithLp.equiv 2 _).injective
    apply Prod.ext
    · exact MemLp.toLp_const_smul a
        (WeightedSobolev.memLp_of_smoothNearClosure hU hμ f.property).1
    · change (WeightedSobolev.memLp_of_smoothNearClosure hU hμ (a • f).property).2.toLp
          (gradient (a • f).val) =
        a • (WeightedSobolev.memLp_of_smoothNearClosure hU hμ f.property).2.toLp (gradient f.val)
      apply Lp.ext
      have hf := (WeightedSobolev.memLp_of_smoothNearClosure hU hμ f.property).2.coeFn_toLp
      have haf := (WeightedSobolev.memLp_of_smoothNearClosure hU hμ (a • f).property).2.coeFn_toLp
      filter_upwards [hμ, hf, haf, Lp.coeFn_smul a
        ((WeightedSobolev.memLp_of_smoothNearClosure hU hμ f.property).2.toLp (gradient f.val))]
        with x hx hfx hafx hsmul
      rw [hsmul]
      rw [hafx]
      simp only [Pi.smul_apply]
      rw [hfx]
      change gradient (a • f.val) x = a • gradient f.val x
      rw [gradient, fderiv_const_smul (smoothCore_differentiableAt f hx), map_smul]
      rfl

/-- The weighted Euclidean Sobolev space, with its prescribed Hilbert norm. -/
def sobolevSubmodule : Submodule ℝ (WeightedSobolev.L2Jet μ E) :=
  (smoothJet μ U hU hμ).range.topologicalClosure

instance : CompleteSpace (sobolevSubmodule μ U hU hμ) := by
  unfold sobolevSubmodule
  infer_instance

/-- The value projection. -/
def value : sobolevSubmodule μ U hU hμ →L[ℝ] Lp ℝ 2 μ :=
  WithLp.fstL 2 ℝ _ _ ∘L (sobolevSubmodule μ U hU hμ).subtypeL

/-- The gradient projection. -/
def grad : sobolevSubmodule μ U hU hμ →L[ℝ] Lp E 2 μ :=
  WithLp.sndL 2 ℝ _ _ ∘L (sobolevSubmodule μ U hU hμ).subtypeL

theorem norm_sq (f : sobolevSubmodule μ U hU hμ) :
    ‖f‖ ^ 2 = ‖value μ U hU hμ f‖ ^ 2 + ‖grad μ U hU hμ f‖ ^ 2 :=
  WithLp.prod_norm_sq_eq_of_L2 f.val

theorem smoothJet_range :
    ((smoothJet μ U hU hμ).range : Set (WeightedSobolev.L2Jet μ E)) =
      WeightedSobolev.jetCore μ (WeightedSobolev.SmoothNearClosure U) id gradient := by
  ext p
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨f.val, f.property, _, _, rfl⟩
  · rintro ⟨f, hf, hv, hg, rfl⟩
    exact ⟨⟨f, hf⟩, rfl⟩

/-- This Hilbert realization is exactly the sequential completion. -/
theorem mem_iff (f : Lp ℝ 2 μ) (g : Lp E 2 μ) :
    WithLp.toLp 2 (f, g) ∈ sobolevSubmodule μ U hU hμ ↔
      WeightedSobolev.IsWeightedH1 μ U f g := by
  change WithLp.toLp 2 (f, g) ∈ closure ((smoothJet μ U hU hμ).range : Set _) ↔ _
  rw [smoothJet_range]
  have h := WeightedSobolev.isGraphH1_iff_mem_closure
    (P := WeightedSobolev.SmoothNearClosure U) (value := id) (derivative := gradient)
    (fun f hf => (WeightedSobolev.memLp_of_smoothNearClosure hU hμ hf).1)
    (fun f hf => (WeightedSobolev.memLp_of_smoothNearClosure hU hμ hf).2)
    f g (Lp.memLp f) (Lp.memLp g)
  change WithLp.toLp 2 (f, g) ∈ closure _ ↔
    WeightedSobolev.IsGraphH1 μ (WeightedSobolev.SmoothNearClosure U) id gradient f g
  simpa only [Lp.toLp_coeFn] using h.symm

/-- Every Hilbert jet satisfies the original Sobolev predicate. -/
theorem isWeightedH1 (f : sobolevSubmodule μ U hU hμ) :
    WeightedSobolev.IsWeightedH1 μ U (value μ U hU hμ f) (grad μ U hU hμ f) :=
  (mem_iff μ U hU hμ _ _).mp f.property

/-- The constant unit is represented by its actual smooth jet. -/
def unit : sobolevSubmodule μ U hU hμ :=
  ⟨smoothJet μ U hU hμ ⟨fun _ => 1,
    ⟨univ, isOpen_univ, subset_univ _, contDiffOn_const⟩⟩,
    Submodule.le_topologicalClosure _ ⟨_, rfl⟩⟩

theorem unit_value : value μ U hU hμ (unit μ U hU hμ) = Lp.const 2 μ (1 : ℝ) := by
  apply Lp.ext
  exact ((WeightedSobolev.memLp_of_smoothNearClosure hU hμ
    (show WeightedSobolev.SmoothNearClosure U (fun _ => (1 : ℝ)) from
      ⟨univ, isOpen_univ, subset_univ _, contDiffOn_const⟩)).1.coeFn_toLp).trans
    (Lp.coeFn_const 2 μ (1 : ℝ)).symm

theorem unit_grad : grad μ U hU hμ (unit μ U hU hμ) = 0 := by
  have h := (WeightedSobolev.memLp_of_smoothNearClosure hU hμ
    (show WeightedSobolev.SmoothNearClosure U (fun _ => (1 : ℝ)) from
      ⟨univ, isOpen_univ, subset_univ _, contDiffOn_const⟩)).2
  change h.toLp _ = 0
  apply Lp.ext
  filter_upwards [h.coeFn_toLp, Lp.coeFn_zero E 2 μ] with x hx hz
  rw [hx, hz]
  exact gradient_fun_const _ _

end Riesz1.Variational

end
