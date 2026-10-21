/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.Convex.ProductSlice
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Tilted
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Fibers, the zero extension, and the fiber integral (Lemma 3.7)

For an open convex set `Q ⊆ ℝ^m × ℝ^n` and a function `K` on `Q`, this file defines

* the zero extension `zeroExtension Q K` of the density `e^{-K}` from `Q` to the whole product.
* the fiber `fiber Q z = {y | (z, y) ∈ Q}`.
* the fiber integral `fiberIntegral Q K z = J(z) = ∫_{Q_z} e^{-K(z,y)} dy`.
* the normalized fiber law `fiberLaw Q K z`, the probability `J(z)⁻¹ e^{-K(z,y)} dy` on `Q_z`.

It proves the elementary facts about these objects used in the Hessian lemma. Fibers are open,
convex, bounded (under the locally bounded fiber hypothesis) and nonempty over the projected
interior. The fiber integral is the integral of the zero extension. It is positive over the
projected interior. For almost every `y` the point `(z, y)` lies in `Q` or outside its closure.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology

namespace Riesz1.ConvexityHessian

variable {m n : ℕ}

/-- The zero extension of the density `e^{-K}` from `Q` to the whole product space. -/
def zeroExtension (Q : Set (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)))
    (K : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n) → ℝ) :
    EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n) → ℝ :=
  Q.indicator fun p => Real.exp (-K p)

/-- The fiber `Q_z = {y | (z, y) ∈ Q}` of `Q` over `z`. -/
def fiber (Q : Set (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)))
    (z : EuclideanSpace ℝ (Fin m)) : Set (EuclideanSpace ℝ (Fin n)) :=
  {y | (z, y) ∈ Q}

/-- The fiber integral `J(z) = ∫_{Q_z} e^{-K(z,y)} dy`. -/
def fiberIntegral (Q : Set (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)))
    (K : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n) → ℝ)
    (z : EuclideanSpace ℝ (Fin m)) : ℝ :=
  ∫ y in fiber Q z, Real.exp (-K (z, y))

/-- The normalized fiber law `J(z)⁻¹ e^{-K(z,y)} dy` on the fiber `Q_z`, the tilted measure of
`volume.restrict (Q_z)` by `-K(z, ·)`. -/
def fiberLaw (Q : Set (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)))
    (K : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n) → ℝ)
    (z : EuclideanSpace ℝ (Fin m)) : Measure (EuclideanSpace ℝ (Fin n)) :=
  (volume.restrict (fiber Q z)).tilted fun y => -K (z, y)

variable {Q : Set (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n))}
  {K : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n) → ℝ}

theorem isOpen_fiber (hQo : IsOpen Q) (z : EuclideanSpace ℝ (Fin m)) : IsOpen (fiber Q z) :=
  hQo.preimage (by fun_prop)

theorem convex_fiber (hQc : Convex ℝ Q) (z : EuclideanSpace ℝ (Fin m)) :
    Convex ℝ (fiber Q z) := by
  intro x hx y hy a b ha hb hab
  show (z, a • x + b • y) ∈ Q
  have hcomb : (z, a • x + b • y) = a • (z, x) + b • (z, y) := by
    ext
    · simp [← add_smul, hab]
    · simp
  rw [hcomb]
  exact hQc hx hy ha hb hab

/-- The projection of `Q` is the set of points over which the fiber is nonempty. -/
theorem fiber_nonempty {z : EuclideanSpace ℝ (Fin m)} (hz : z ∈ Prod.fst '' Q) :
    (fiber Q z).Nonempty := by
  obtain ⟨⟨w, y⟩, hq, rfl⟩ := hz
  exact ⟨y, hq⟩

/-- Locally bounded fibers over the projected interior give bounded fibers. -/
theorem isBounded_fiber
    (hloc : ∀ z ∈ Prod.fst '' Q, ∃ U ∈ 𝓝 z, Bornology.IsBounded (Q ∩ (U ×ˢ univ)))
    {z : EuclideanSpace ℝ (Fin m)} (hz : z ∈ Prod.fst '' Q) :
    Bornology.IsBounded (fiber Q z) := by
  obtain ⟨U, hU, hb⟩ := hloc z hz
  have hzU : z ∈ U := mem_of_mem_nhds hU
  have hsub : ({z} : Set (EuclideanSpace ℝ (Fin m))) ×ˢ fiber Q z ⊆ Q ∩ (U ×ˢ univ) := by
    rintro ⟨w, y⟩ ⟨hw, hy⟩
    rw [mem_singleton_iff] at hw
    subst hw
    exact ⟨hy, hzU, mem_univ _⟩
  exact Bornology.IsBounded.snd_of_prod (hb.subset hsub) (singleton_nonempty z)

theorem zeroExtension_of_mem {p : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)}
    (hp : p ∈ Q) : zeroExtension Q K p = Real.exp (-K p) :=
  Set.indicator_of_mem hp _

theorem zeroExtension_of_notMem {p : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)}
    (hp : p ∉ Q) : zeroExtension Q K p = 0 :=
  Set.indicator_of_notMem hp _

/-- The fiber integral is the integral over the whole space of the zero extension. -/
theorem fiberIntegral_eq_integral (hQo : IsOpen Q) (z : EuclideanSpace ℝ (Fin m)) :
    fiberIntegral Q K z = ∫ y, zeroExtension Q K (z, y) := by
  unfold fiberIntegral
  rw [← integral_indicator (isOpen_fiber hQo z).measurableSet]
  rfl

/-- The fiber integral is positive over the projected interior, where the fibers are nonempty
open sets, provided the fiber integrand is integrable there. -/
theorem fiberIntegral_pos (hQo : IsOpen Q) {z : EuclideanSpace ℝ (Fin m)}
    (hz : z ∈ Prod.fst '' Q)
    (hint : IntegrableOn (fun y => Real.exp (-K (z, y))) (fiber Q z)) :
    0 < fiberIntegral Q K z := by
  unfold fiberIntegral
  rw [setIntegral_pos_iff_support_of_nonneg_ae (Eventually.of_forall fun y => (Real.exp_pos _).le)
    hint]
  have hpos : 0 < volume (fiber Q z) :=
    (isOpen_fiber hQo z).measure_pos volume (fiber_nonempty hz)
  refine lt_of_lt_of_le hpos (measure_mono fun y hy => ⟨(Real.exp_pos _).ne', hy⟩)

/-- A function continuous on `Q` gives an a.e. strongly measurable fiber slice of its zero
extension. -/
theorem aestronglyMeasurable_indicator_slice {g : EuclideanSpace ℝ (Fin m) ×
      EuclideanSpace ℝ (Fin n) → ℝ} (hQo : IsOpen Q) (hg : ContinuousOn g Q)
    (z : EuclideanSpace ℝ (Fin m)) :
    AEStronglyMeasurable (fun y => Q.indicator g (z, y)) volume := by
  have hmeas : MeasurableSet (fiber Q z) := (isOpen_fiber hQo z).measurableSet
  have hc : ContinuousOn (fun y => g (z, y)) (fiber Q z) :=
    hg.comp (by fun_prop : Continuous fun y : EuclideanSpace ℝ (Fin n) => (z, y)).continuousOn
      fun _ hy => hy
  have heq : (fun y => Q.indicator g (z, y)) = (fiber Q z).indicator (fun y => g (z, y)) := by
    funext y
    rfl
  rw [heq]
  exact (aestronglyMeasurable_indicator_iff hmeas).2 (hc.aestronglyMeasurable hmeas)

/-- For almost every `y`, the point `(z, y)` lies in `Q` or outside the closure of `Q`. -/
theorem ae_mem_or_notMem_closure (hQo : IsOpen Q) (hQc : Convex ℝ Q)
    {z : EuclideanSpace ℝ (Fin m)} (hz : z ∈ Prod.fst '' Q) :
    ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (z, y) ∈ Q ∨ (z, y) ∉ closure Q := by
  have hnull := measure_slice_closure_diff_eq_zero volume hQo hQc hz
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with y hy
  by_cases h : (z, y) ∈ Q
  · exact Or.inl h
  · exact Or.inr fun hc => hy ⟨hc, h⟩

end Riesz1.ConvexityHessian

end

end
