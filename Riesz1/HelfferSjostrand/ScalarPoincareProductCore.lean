/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.ScalarPoincareSlices
public import Riesz1.HelfferSjostrand.ScalarPoincareRadialLaw
public import Riesz1.ToMathlib.Poincare.SmoothCore
public import Riesz1.ToMathlib.Poincare.CircleProbability
public import Riesz1.ToMathlib.Poincare.Product

/-!
# Measurable smooth-core tests in product coordinates

For the scalar Poincaré inequality, the radial domain is extended by zero when
applying variance tensorization on the ambient product. The circle
representative is the unique one in `(0, √N]`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff InnerProductSpace

namespace Riesz1

variable {N : ℕ+}
variable (basis : OrthonormalBasis (Fin (Module.finrank ℝ (hsOrthSubspace N))) ℝ (hsOrthSubspace N))

local instance : Fact (0 < Real.sqrt (N : ℕ)) := ⟨sqrt_N_pos N⟩

/-- The real lift of product coordinates with common-rotation coordinate in `(0, √N]`. -/
def scalarPoincareProductLift
    (p : EuclideanSpace ℝ (Fin (Module.finrank ℝ (hsOrthSubspace N))) ×
      AddCircle (Real.sqrt (N : ℕ))) : HsEuclidean N :=
  scalarPoincareRadialEmbedding basis p.1 +
    (AddCircle.equivIoc (Real.sqrt (N : ℕ)) 0 p.2 : ℝ) • hsUnitVector N

/-- Zero extension from the radial domain, used only for integration on
the ambient product space. -/
def scalarPoincareProductExtension {V : Type*} [Zero V] (f : HsEuclidean N → V)
    (p : EuclideanSpace ℝ (Fin (Module.finrank ℝ (hsOrthSubspace N))) ×
      AddCircle (Real.sqrt (N : ℕ))) : V :=
  (scalarPoincareRadialDomain basis ×ˢ univ).indicator
    (fun p => f (scalarPoincareProductLift basis p)) p

theorem scalarPoincareProductExtension_of_mem {V : Type*} [Zero V]
    (f : HsEuclidean N → V)
    {q : EuclideanSpace ℝ (Fin (Module.finrank ℝ (hsOrthSubspace N)))}
    (hq : q ∈ scalarPoincareRadialDomain basis) (w : AddCircle (Real.sqrt (N : ℕ))) :
    scalarPoincareProductExtension basis f (q, w) =
      f (scalarPoincareProductLift basis (q, w)) := by
  classical
  exact indicator_of_mem (s := scalarPoincareRadialDomain basis ×ˢ univ)
    ⟨hq, mem_univ _⟩ _

/-- Smooth-core values and gradients give bounded measurable functions
on the product. No regularity outside the chamber is assumed. -/
theorem scalarPoincareProductExtension_properties {V : Type*} [NormedAddCommGroup V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    (f : HsEuclidean N → V) (hf : ContinuousOn f (closure (hsChamber N))) :
    StronglyMeasurable (scalarPoincareProductExtension basis f) ∧
      ∃ C : ℝ, ∀ p, ‖scalarPoincareProductExtension basis f p‖ ≤ C := by
  classical
  let A := fun p : EuclideanSpace ℝ (Fin (Module.finrank ℝ (hsOrthSubspace N))) × ℝ =>
    scalarPoincareRadialEmbedding basis p.1 + p.2 • hsUnitVector N
  have hA : Continuous A := ((scalarPoincareRadialEmbedding basis).continuous.comp
    continuous_fst).add (continuous_snd.smul continuous_const)
  have hmap : ∀ q ∈ closure (scalarPoincareRadialDomain basis), ∀ t : ℝ,
      A (q, t) ∈ closure (hsChamber N) := by
    intro q hq t
    have hm : MapsTo (fun p => scalarPoincareRadialEmbedding basis p + t • hsUnitVector N)
        (scalarPoincareRadialDomain basis) (hsChamber N) :=
      fun _ hp => scalarPoincare_slice_mem basis hp t
    exact hm.closure
      ((scalarPoincareRadialEmbedding basis).continuous.add continuous_const) hq
  have hcont : ContinuousOn (fun p => f (A p))
      (scalarPoincareRadialDomain basis ×ˢ (univ : Set ℝ)) :=
    hf.comp hA.continuousOn (fun p hp => hmap p.1 (subset_closure hp.1) p.2)
  have hmeas : Measurable ((scalarPoincareRadialDomain basis ×ˢ (univ : Set ℝ)).indicator
      (fun p => f (A p))) :=
    by
      rw [← piecewise_eq_indicator]
      exact hcont.measurable_piecewise continuousOn_const
        ((isOpen_scalarPoincareRadialDomain basis).measurableSet.prod MeasurableSet.univ)
  have hrep : Measurable (fun p : EuclideanSpace ℝ
      (Fin (Module.finrank ℝ (hsOrthSubspace N))) × AddCircle (Real.sqrt (N : ℕ)) =>
      (p.1, (AddCircle.equivIoc (Real.sqrt (N : ℕ)) 0 p.2 : ℝ))) :=
    measurable_fst.prodMk (measurable_subtype_coe.comp
      ((AddCircle.measurableEquivIoc (Real.sqrt (N : ℕ)) 0).measurable.comp measurable_snd))
  have heq : scalarPoincareProductExtension basis f =
      ((scalarPoincareRadialDomain basis ×ˢ (univ : Set ℝ)).indicator
        (fun p => f (A p))) ∘ (fun p =>
          (p.1, (AddCircle.equivIoc (Real.sqrt (N : ℕ)) 0 p.2 : ℝ))) := by
    funext p
    simp only [scalarPoincareProductExtension, indicator_apply, mem_prod, mem_univ,
      and_true, Function.comp_apply, scalarPoincareProductLift, A]
  refine ⟨(heq ▸ hmeas.comp hrep).stronglyMeasurable, ?_⟩
  let K := closure (scalarPoincareRadialDomain basis) ×ˢ Icc (0 : ℝ) (Real.sqrt (N : ℕ))
  have hK : IsCompact K := (bounded_scalarPoincareRadialDomain basis).isCompact_closure.prod
    isCompact_Icc
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
    (hf.comp hA.continuousOn (fun p hp => hmap p.1 hp.1 p.2))
  refine ⟨max C 0, fun p => ?_⟩
  by_cases hq : p.1 ∈ scalarPoincareRadialDomain basis
  · rw [scalarPoincareProductExtension_of_mem basis f hq]
    exact (hC (p.1, (AddCircle.equivIoc (Real.sqrt (N : ℕ)) 0 p.2 : ℝ))
      ⟨subset_closure hq, by
        have ht := (AddCircle.equivIoc (Real.sqrt (N : ℕ)) 0 p.2).property
        exact ⟨ht.1.le, by simpa using ht.2⟩⟩).trans (le_max_left _ _)
  · rw [scalarPoincareProductExtension, indicator_of_notMem (by simpa using hq), norm_zero]
    exact le_max_right _ _

/-- The radial factor is concentrated on the open radial domain. -/
theorem scalarPoincareRadial_ae_mem {c : ℝ} (χ : HsPairPotentials N c) :
    ∀ᵐ q ∂((volume.restrict (scalarPoincareRadialDomain basis)).tilted
      (fun y => -scalarPoincareRadialPotential basis χ y)),
      q ∈ scalarPoincareRadialDomain basis :=
  (withDensity_absolutelyContinuous _ _).ae_le
    (ae_restrict_mem (isOpen_scalarPoincareRadialDomain basis).measurableSet)

/-- Integer translation invariance passes to the Euclidean gradient. -/
theorem scalarPoincare_gradient_translate {f : HsEuclidean N → ℝ}
    (hf : HsSmoothOnClosure N f) (k : ℤ) (x : HsEuclidean N) :
    gradient f (hsTranslate (k : ℝ) x) = gradient f x := by
  have heq : (fun y => f (y + WithLp.toLp 2 (fun _ : Fin (N : ℕ) => (k : ℝ)))) = f :=
    funext (hf.1 k)
  unfold gradient
  change (InnerProductSpace.toDual ℝ (HsEuclidean N)).symm
    (fderiv ℝ f (x + WithLp.toLp 2 (fun _ : Fin (N : ℕ) => (k : ℝ)))) = _
  rw [← fderiv_comp_add_right, heq]

/-- Any integer-periodic lift descends along the common-rotation circle. -/
theorem scalarPoincare_periodic_slice {V : Type*} (f : HsEuclidean N → V)
    (hf : ∀ (k : ℤ) (x : HsEuclidean N), f (hsTranslate (k : ℝ) x) = f x)
    (q : EuclideanSpace ℝ (Fin (Module.finrank ℝ (hsOrthSubspace N)))) :
    Function.Periodic (fun t : ℝ =>
      f (scalarPoincareRadialEmbedding basis q + t • hsUnitVector N))
      (Real.sqrt (N : ℕ)) := by
  intro t
  have hx : scalarPoincareRadialEmbedding basis q + (t + Real.sqrt (N : ℕ)) • hsUnitVector N =
      hsTranslate 1 (scalarPoincareRadialEmbedding basis q + t • hsUnitVector N) := by
    ext i
    simp only [PiLp.add_apply, PiLp.smul_apply, hsUnitVector, hsRotationVector,
      smul_eq_mul, hsTranslate_apply]
    field_simp
    ring
  dsimp only
  rw [hx]
  simpa only [Int.cast_one] using hf 1
    (scalarPoincareRadialEmbedding basis q + t • hsUnitVector N)

theorem scalarPoincareProductLift_coe {V : Type*} (f : HsEuclidean N → V)
    (hf : ∀ (k : ℤ) (x : HsEuclidean N), f (hsTranslate (k : ℝ) x) = f x)
    (q : EuclideanSpace ℝ (Fin (Module.finrank ℝ (hsOrthSubspace N)))) (t : ℝ) :
    f (scalarPoincareProductLift basis (q, (t : AddCircle (Real.sqrt (N : ℕ))))) =
      f (scalarPoincareRadialEmbedding basis q + t • hsUnitVector N) := by
  let hp := scalarPoincare_periodic_slice basis f hf q
  have hrep := hp.lift_coe (AddCircle.equivIoc (Real.sqrt (N : ℕ)) 0
    (t : AddCircle (Real.sqrt (N : ℕ))) : ℝ)
  rw [AddCircle.coe_equivIoc, hp.lift_coe] at hrep
  exact hrep.symm

/-- Evaluation in product coordinates agrees with evaluation in the
unique fundamental representative. -/
theorem scalarPoincareProductExtension_config {V : Type*} [Zero V]
    (f : HsEuclidean N → V)
    (hf : ∀ (k : ℤ) (x : HsEuclidean N), f (hsTranslate (k : ℝ) x) = f x)
    (X : Configuration N) :
    scalarPoincareProductExtension basis f
      ((scalarPoincareRadialChart basis).symm (hsConfigCoord N X).1, (hsConfigCoord N X).2) =
      f (WithLp.toLp 2 X.val) := by
  have hq : (scalarPoincareRadialChart basis).symm (hsConfigCoord N X).1 ∈
      scalarPoincareRadialDomain basis := by
    change ((scalarPoincareRadialChart basis)
      ((scalarPoincareRadialChart basis).symm (hsConfigCoord N X).1) : HsEuclidean N) ∈ hsChamber N
    rw [LinearIsometryEquiv.apply_symm_apply]
    exact hsConfigCoord_fst_mem N X
  rw [scalarPoincareProductExtension_of_mem basis f hq]
  change f (scalarPoincareProductLift basis (_, (inner ℝ (WithLp.toLp 2 X.val)
    (hsUnitVector N) : AddCircle (Real.sqrt (N : ℕ))))) = _
  rw [scalarPoincareProductLift_coe basis f hf]
  have he : scalarPoincareRadialEmbedding basis
      ((scalarPoincareRadialChart basis).symm (hsConfigCoord N X).1) =
      (hsOrthComp N (WithLp.toLp 2 X.val) : HsEuclidean N) := by
    change ((scalarPoincareRadialChart basis)
      ((scalarPoincareRadialChart basis).symm (hsConfigCoord N X).1) : HsEuclidean N) = _
    rw [LinearIsometryEquiv.apply_symm_apply]
    rfl
  rw [he, hsOrthComp_add_smul]

end Riesz1

end
