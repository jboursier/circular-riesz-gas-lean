/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.CircleMollifyFourier
public import Riesz1.Frozen.PrimitiveRegularity

/-!
# Smooth real representatives of circle regularizations

The input uses the real `L²` carrier. The output is identified pointwise
with the convolution and has its exact Fourier multiplier at every length.
-/

public section

open MeasureTheory Set
open scoped ContDiff

namespace Riesz1.Internal

theorem locallyIntegrable_circle_lift {T : ℝ} [hT : Fact (0 < T)]
    {E : Type*} [NormedAddCommGroup E] {f : AddCircle T → E}
    (hf : Integrable f volume) : LocallyIntegrable (fun t : ℝ => f (t : AddCircle T)) volume := by
  intro x
  refine ⟨Ioc (x - T / 2) (x - T / 2 + T),
    Ioc_mem_nhds (by linarith [hT.out]) (by linarith [hT.out]), ?_⟩
  exact ((AddCircle.measurePreserving_mk T (x - T / 2)).integrable_comp
    hf.aestronglyMeasurable).mpr hf

/-- No representative is picked by a bound: `g` is the descent of `circleMollify`.
The smoothing radius has no upper restriction in this result. -/
theorem exists_circleMollify_L2 {ρ : ℝ → ℝ} (hρ : IsMollifier ρ)
    (L : Length) {h : ℝ} (hh : 0 < h)
    (f : {f : Circle L → ℝ // MemLp (fun x => (f x : ℂ)) 2 (arclength L)}) :
    ∃ g : {g : Circle L → ℝ // MemLp (fun x => (g x : ℂ)) 2 (arclength L)},
      Continuous g.val ∧ ContDiff ℝ ∞ (fun x : ℝ => g.val (x : Circle L)) ∧
      (∀ x : ℝ, g.val (x : Circle L) =
        circleMollify ρ L.val h (fun t : ℝ => f.val (t : Circle L)) x) ∧
      ∀ k : ℤ, coeff L ⟨(fun x => (g.val x : ℂ)), complexL2Integrable L _ g.property⟩ k =
        coeff L ⟨(fun x => (f.val x : ℂ)), complexL2Integrable L _ f.property⟩ k *
          (mollifierFT ρ (h * k / L.val) : ℂ) := by
  have : Fact (0 < L.val) := ⟨L.property⟩
  let F : ℝ → ℝ := fun t => f.val (t : Circle L)
  have hfi : Integrable f.val (arclength L) := (complexL2Integrable L _ f.property).re
  have hF : LocallyIntegrable F volume := locallyIntegrable_circle_lift hfi
  have hp : Function.Periodic F L.val := by intro x; simp only [F, AddCircle.coe_add_period]
  have hgp := circleMollify_periodic hρ L.property hh hF hp
  let g : Circle L → ℝ := hgp.lift
  have hg (x : ℝ) : g (x : Circle L) = circleMollify ρ L.val h F x := hgp.lift_coe x
  have hs : ContDiff ℝ ∞ (fun x : ℝ => g (x : Circle L)) := by
    simpa only [hg] using contDiff_circleMollify hρ L.property hh hF hp
  have hc : Continuous g :=
    (QuotientAddGroup.isQuotientMap_mk (AddSubgroup.zmultiples L.val)).continuous_iff.mpr
      hs.continuous
  have hgm : MemLp (fun x => (g x : ℂ)) 2 (arclength L) := by
    change MemLp (fun x => (g x : ℂ)) 2 volume
    exact (Complex.continuous_ofReal.comp hc).memLp_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  refine ⟨⟨g, hgm⟩, hc, hs, hg, fun k => ?_⟩
  exact fourierCoeff_circleMollify hρ hh hF hp f.val g (fun _ => rfl) hg k

end Riesz1.Internal
