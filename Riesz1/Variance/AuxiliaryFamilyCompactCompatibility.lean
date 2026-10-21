/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.RegUniformCompactCompatibility
public import Riesz1.ToMathlib.MollifyLineIntegralNorm
public import Riesz1.CLT.IdentityDefs
public import Riesz1.Kernel.AdmissibilityRegularityProfileFourier
public import Riesz1.Kernel.TransportScaledConvolution

/-!
# Compact family compatibility on the entire permitted radius interval

The compact branches of `OptimalScalingTest` and
Theorem 2. The actual enlarged support
remains within the unit cell for every radius in `OptimalScalingTest`.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace Riesz1.Internal

/-- Smoothing a fixed compact profile commutes with every observation
periodization whenever its support stays in the unit cell. The line
integral norm contracts, throughout the full permitted radius interval. -/
theorem auxiliary_family_compact_compatibility (p : Profile)
    {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) {r t : ℝ}
    (hr : 0 < r) (hmargin : r + t / 2 < 1 / 2) (ht : 0 < t)
    (hsupp : ∀ᵐ x : ℝ, r ≤ |x| → zeroExtension p x = 0) :
    ∃ g : Profile,
      ContDiff ℝ ∞ (fun x : ℝ => g.val (x : Circle unitLength)) ∧
      CompactProfile g ∧
      (∀ x : ℝ, g.val (x : Circle unitLength) =
        circleMollify ρ 1 t (fun y : ℝ => p.val (y : Circle unitLength)) x) ∧
      (∫ x : ℝ, |zeroExtension g x|) ≤ ∫ x : ℝ, |zeroExtension p x| ∧
      ∀ a : Scale, ∀ x : ℝ,
        periodizedProfile g (observationLength a) (x : Circle (observationLength a)) =
          circleMollify ρ (observationLength a).val t
            (fun y : ℝ => periodizedProfile p (observationLength a)
              (y : Circle (observationLength a))) x := by
  obtain ⟨g₀, _, hgs, hgv, _⟩ := exists_circleMollify_L2 hρ unitLength ht
    ⟨p.val, p.property⟩
  let g : Profile := ⟨g₀.val, g₀.property⟩
  have hgv' (x : ℝ) : g.val (x : Circle unitLength) =
      circleMollify ρ 1 t (fun y : ℝ => p.val (y : Circle unitLength)) x := hgv x
  have hline := zeroExtension_circleMollify_eq_line hρ p g ht hmargin hsupp hgv'
  have hgc : CompactProfile g := by
    refine ⟨r + t / 2, by linarith, hmargin, ?_⟩
    exact ae_of_all _ fun x hx => by
      rw [hline]
      exact mollifyLine_zeroExtension_eq_zero hρ p ht hsupp hx
  have hnorm : (∫ x : ℝ, |zeroExtension g x|) ≤ ∫ x : ℝ, |zeroExtension p x| := by
    simp_rw [hline]
    exact integral_abs_mollifyLine_le hρ ht (zeroExtension_integrable p)
  refine ⟨g, hgs, hgc, hgv', hnorm, fun a x => ?_⟩
  let L := observationLength a
  have : Fact (0 < L.val) := ⟨L.property⟩
  have hL : 1 ≤ L.val := (one_le_inv₀ a.property.1).mpr a.property.2
  let z := centralRep L (x : Circle L)
  have hzx : (z : Circle L) = (x : Circle L) := AddCircle.coe_equivIco
  have hzL : |z| ≤ L.val / 2 := by
    have hm := centralRep_mem_Ico L (x : Circle L)
    exact abs_le.mpr ⟨hm.1, hm.2.le⟩
  obtain ⟨q, _, _, hqv, _⟩ := exists_circleMollify_L2 hρ L ht
    ⟨periodizedProfile p L, periodizedProfileL2 p a⟩
  rw [admissibility_periodizedProfile_eq_zeroExtension g L hL]
  change zeroExtension g z = _
  rw [hline]
  rw [← circleMollify_periodized_eq_line_central hρ p L hL ht hmargin hsupp hzL,
    ← hqv, hzx, hqv]

end Riesz1.Internal

end
