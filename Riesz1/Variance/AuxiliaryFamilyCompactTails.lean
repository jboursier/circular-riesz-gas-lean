/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.AuxiliaryFamilyCompactCompatibility
public import Riesz1.Variance.RegUniformIntegralTails
public import Riesz1.Variance.AuxiliaryFamilyMacroBounds

/-!
# Compact transport tails for every permitted family radius

The uniform compact-tail step of Theorem 2
as needed in Proposition 5.6. Compact compatibility and contraction of
the line integral norm remove the small-radius restriction.
-/

public section

noncomputable section

open MeasureTheory
open scoped ContDiff

namespace Riesz1.Internal

/-- Tails of the transport of a smoothed compact test, uniformly over
the entire family radius interval that retains the support margin.
Only coefficient identities identifying the actual transports are inputs. -/
theorem auxiliary_family_compact_transport_tails (P : Parameters) (p : Profile)
    {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) :
    ∃ T : ℝ, 0 < T ∧ ∀ (a : Scale) (r t : ℝ), 0 < r → ∀ ht : 0 < t,
      r + t / 2 < 1 / 2 →
      (∀ᵐ x : ℝ, r ≤ |x| → zeroExtension p x = 0) →
      ∀ (φ : {f : Circle (observationLength a) → ℝ //
          MemLp (fun x => (f x : ℂ)) 2 (arclength (observationLength a))}),
        ContDiff ℝ ∞ (fun x : ℝ => φ.val (x : Circle (observationLength a))) →
        (∀ k, coeff (observationLength a) ⟨(fun x => (φ.val x : ℂ)),
          complexL2Integrable _ _ φ.property⟩ k =
            transportCoeffs P (observationLength a)
              (loopMasterLengthTest _
                (cltRegCircle hρ _ ht
                  ⟨periodizedProfile p (observationLength a), periodizedProfileL2 p a⟩)
                (cltRegCircle_contDiff hρ _ ht _)) k) →
        ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ x : ℝ,
          2 ≤ circDist (observationLength a).val x →
          |deriv (circleMollify ρ (observationLength a).val h
            (fun y : ℝ => φ.val (y : Circle (observationLength a)))) x| ≤
              T * circDist (observationLength a).val x ^ (P.val.2 - 2) ∧
          |deriv (deriv (circleMollify ρ (observationLength a).val h
            (fun y : ℝ => φ.val (y : Circle (observationLength a))))) x| ≤
              T * circDist (observationLength a).val x ^ (P.val.2 - 3) := by
  let Z := ∫ x : ℝ, |zeroExtension p x|
  obtain ⟨T, hT, htail⟩ := compact_smoothed_tails_of_integral_bound P Z
    (integral_nonneg fun _ => abs_nonneg _) ρ hρ
  refine ⟨T, hT, fun a r t hr ht hmargin hsupp φ hφ hcoeff h hh hh1 x hx => ?_⟩
  obtain ⟨g, _, hgc, _, hgn, hcompat⟩ := auxiliary_family_compact_compatibility p hρ
    hr hmargin ht hsupp
  let L := observationLength a
  let ξ := (⟨periodizedProfile p L, periodizedProfileL2 p a⟩ :
    {f : Circle L → ℝ // MemLp (fun x => (f x : ℂ)) 2 (arclength L)})
  let gt := loopMasterLengthTest L (cltRegCircle hρ L ht ξ)
    (cltRegCircle_contDiff hρ L ht ξ)
  have hgt : gt = ⟨periodizedProfile g L, periodizedProfileL2 g a⟩ := by
    apply Subtype.ext
    funext z
    induction z using Quotient.inductionOn with
    | h y => exact (cltRegCircle_coe hρ L ht ξ y).trans (hcompat a y).symm
  have hf (k : ℤ) : coeff L ⟨(fun y => (φ.val y : ℂ)),
      complexL2Integrable _ _ φ.property⟩ k =
        transportCoeffs P L ⟨periodizedProfile g L, periodizedProfileL2 g a⟩ k := by
    have hk := hcoeff k
    change _ = transportCoeffs P L gt k at hk
    rwa [hgt] at hk
  have hφc : Continuous φ.val := continuous_circle_of_lift L hφ.continuous
  have hφi : LocallyIntegrable (deriv (fun y : ℝ => φ.val (y : Circle L))) volume :=
    (hφ.continuous_deriv (by simp)).locallyIntegrable
  have hφAC (u v : ℝ) : AbsolutelyContinuousOnInterval
      (fun y : ℝ => φ.val (y : Circle L)) u v :=
    (hφ.of_le (by simp : (1 : WithTop ℕ∞) ≤ ∞)).contDiffOn.absolutelyContinuousOnInterval
  have hb := htail g hgc hgn a φ.val hφc φ.property hf hφi hφAC h hh hh1 x
  have hx' : 2 ≤ dist (x : Circle L) 0 := by
    simpa only [dist_coe_zero_eq_circDist] using hx
  simpa only [dist_coe_zero_eq_circDist] using hb hx'

end Riesz1.Internal

end
