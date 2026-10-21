/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.CircleAEFromCell
public import Riesz1.Variance.RegMicroNearFarRegularity
public import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-!
# The inverse error is the original circle `L²` error

The kernel theorem identifies representatives on a fundamental interval.
This file promotes that identity to the full circle and proves `L²`
membership of the actual inverse error of Lemma 5.3.
-/

public section

open MeasureTheory Set

namespace Riesz1.Internal

/-- The actual inverse error agrees almost everywhere on the entire circle
with the original regularization error, and inherits its `L²` certificate.
The sole representation hypothesis is the identity supplied by the
kernel and qualitative regularity theorems. -/
theorem regMicro_inverse_error_memLp (P : Parameters) (L : Length)
    (f ψ : {f : Circle L → ℝ // MemLp (fun x => (f x : ℂ)) 2 (arclength L)})
    (ρ : ℝ → ℝ) (hρ : IsMollifier ρ) {h : ℝ} (hh : 0 < h)
    (hrep : ∀ᵐ x : ℝ ∂volume.restrict (Ioc (-(L.val/2)) (L.val/2)),
      f.val (x : Circle L) =
        (∫ y in Ioc (-(L.val/2)) (L.val/2), f.val (y : Circle L))/L.val +
          inverseConv P L.val (deriv (fun t : ℝ => ψ.val (t : Circle L))) x) :
    let m := (∫ y in Ioc (-(L.val/2)) (L.val/2), f.val (y : Circle L))/L.val
    let e := fun z : Circle L => m + inverseConvCircle P L
      (deriv (fun t : ℝ => ψ.val (t : Circle L))) z - cltRegCircle hρ L hh f z
    (e =ᵐ[arclength L] fun z => f.val z-cltRegCircle hρ L hh f z) ∧
      MemLp (fun z => (e z : ℂ)) 2 (arclength L) := by
  dsimp only
  have : Fact (0 < L.val) := ⟨L.property⟩
  have : IsFiniteMeasure (arclength L) := by unfold arclength; infer_instance
  let m := (∫ y in Ioc (-(L.val/2)) (L.val/2), f.val (y : Circle L))/L.val
  let e := fun z : Circle L => m + inverseConvCircle P L
    (deriv (fun t : ℝ => ψ.val (t : Circle L))) z - cltRegCircle hρ L hh f z
  have hrc : Continuous (cltRegCircle hρ L hh f) :=
    (QuotientAddGroup.isQuotientMap_mk _).continuous_iff.2
      (cltRegCircle_contDiff hρ L hh f).continuous
  have hem : Measurable e :=
    (measurable_const.add (measurable_inverseConvCircle P L (measurable_deriv _))).sub hrc.measurable
  have hfm : AEMeasurable f.val (arclength L) := by
    have hfr : MemLp f.val 2 (arclength L) := by
      simpa using f.property.re
    exact hfr.aestronglyMeasurable.aemeasurable
  have heq : e =ᵐ[arclength L] fun z => f.val z-cltRegCircle hρ L hh f z := by
    apply ae_circle_of_ae_cell hem.aemeasurable (hfm.sub hrc.measurable.aemeasurable)
    filter_upwards [hrep] with x hx
    dsimp only [e]
    rw [inverseConvCircle_coe, ← hx]
    simp only [Pi.sub_apply]
  have hrL2 : MemLp (fun z => (cltRegCircle hρ L hh f z : ℂ)) 2 (arclength L) :=
    (Complex.continuous_ofReal.comp hrc).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hsub : MemLp (fun z => (f.val z : ℂ)-(cltRegCircle hρ L hh f z : ℂ))
      2 (arclength L) := by
    convert f.property.sub hrL2 using 1
  have hae : (fun z => (f.val z : ℂ)-(cltRegCircle hρ L hh f z : ℂ)) =ᵐ[arclength L]
      (fun z => (e z : ℂ)) := by
    filter_upwards [heq] with z hz
    rw [hz, Complex.ofReal_sub]
  exact ⟨heq, (memLp_congr_ae hae).1 hsub⟩

end Riesz1.Internal
