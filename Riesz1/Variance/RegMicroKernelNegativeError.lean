/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.RegMicroKernelContinuous
public import Riesz1.Variance.RegMicroKernelProfileDerivative
public import Riesz1.ToMathlib.FiniteMarkHolder

/-!
# Global regularization errors for negative exponents

The unique continuous extension has sharp Hölder increments through the
marks, obtained by integrating the first derivative bound. Its
smoothing error is `O(h^(-α))` everywhere, uniformly over compact scales.
This proves the negative-exponent value clause of Lemma 5.3.
-/

public section

open MeasureTheory Set Filter Topology

namespace Riesz1.Internal

/-- Apply the continuous-extension and marked Hölder lemmas to the same
inverse representative as the derivative estimate. The analytic hypotheses
here are supplied inside the statements below. -/
theorem negative_error_of_inverse_derivative (P : Parameters) (L : Length) (hL : 1 ≤ L.val)
    (ρ : ℝ → ℝ) (hρ : IsMollifier ρ)
    (η B : ℝ) (hη : 0 < η) (hB : 0 ≤ B)
    (f : {f : Circle L → ℝ // MemLp (fun x => (f x : ℂ)) 2 (arclength L)})
    (n : ℕ+) (marks : Fin (n : ℕ) → ℝ) (α C : ℝ)
    (hα0 : P.val.2 - 1 ≤ α) (hα1 : α < P.val.2 / 2) (hαneg : α < 0) (hC : 0 ≤ C)
    (hprim : PrimitiveRegularity L η P.val.2 B f)
    (hreg : TransportRegularity P L f n marks α C)
    (q : ℝ → ℝ) (hqm : Measurable q) (A : ℝ) (hA : 0 ≤ A)
    (hrep : ∀ᵐ x : ℝ ∂(volume.restrict (Ioc (-(L.val / 2)) (L.val / 2))),
      f.val (x : Circle L) =
        (∫ y in Ioc (-(L.val / 2)) (L.val / 2), f.val (y : Circle L)) / L.val + inverseConv P L.val q x)
    (hd : let m := (∫ y in Ioc (-(L.val / 2)) (L.val / 2), f.val (y : Circle L)) / L.val
      ∀ x : ℝ, (∀ j, (x : Circle L) ≠ (marks j : Circle L)) →
        DifferentiableAt ℝ (fun t => m + inverseConv P L.val q t) x ∧
        |deriv (fun t => m + inverseConv P L.val q t) x| ≤
          A * cappedMarkDistance (fun j => (marks j : Circle L)) (x : Circle L) ^ (-1 - α)) :
    ∃ g : C(Circle L, ℝ), ((g : Circle L → ℝ) =ᵐ[arclength L] f.val) ∧
      (let m := (∫ y in Ioc (-(L.val / 2)) (L.val / 2), f.val (y : Circle L)) / L.val
       ∀ x : ℝ, (∀ j, (x : Circle L) ≠ (marks j : Circle L)) →
         g (x : Circle L) = m + inverseConv P L.val q x) ∧
      ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ x : ℝ,
        |g (x : Circle L) - circleMollify ρ L.val h (fun y => f.val (y : Circle L)) x| ≤
          A * (1 + (n : ℝ) * (1 + 2 / (-α))) * h ^ (-α) := by
  have : Fact (0 < L.val) := ⟨L.property⟩
  let m := (∫ y in Ioc (-(L.val / 2)) (L.val / 2), f.val (y : Circle L)) / L.val
  obtain ⟨g, hg, _huniq⟩ := regMicroKernel_continuous_profile_of_neg P L η B hη hB
    f n marks α C hα0 hα1 hαneg hC hprim hreg
  have heq := inverse_representative_eq_continuous P L marks q hqm f.val g m hg hrep
    (fun x hx => (hd x hx).1)
  have hderiv (x : ℝ) (hx : ∀ j, (x : Circle L) ≠ (marks j : Circle L)) :
      DifferentiableAt ℝ (fun t : ℝ => g (t : Circle L)) x ∧
      |deriv (fun t : ℝ => g (t : Circle L)) x| ≤
        A * cappedMarkDistance (fun j => (marks j : Circle L)) (x : Circle L) ^ (-(1 + α)) := by
    refine ⟨(hd x hx).1.congr_of_eventuallyEq (heq x hx), ?_⟩
    rw [(heq x hx).deriv_eq]
    rw [show -(1 + α) = -1 - α by ring]
    exact (hd x hx).2
  refine ⟨g, hg, fun x hx => (heq x hx).self_of_nhds, fun h hh hh1 x => ?_⟩
  have hmoll : circleMollify ρ L.val h (fun y => f.val (y : Circle L)) x =
      circleMollify ρ L.val h (fun y => g (y : Circle L)) x := by
    have hgcell := (AddCircle.measurePreserving_mk L.val (-(L.val / 2))).quasiMeasurePreserving.ae_eq_comp hg
    rw [show -(L.val / 2) + L.val = L.val / 2 by ring] at hgcell
    unfold circleMollify
    rw [intervalIntegral.integral_of_le (by linarith [L.property]),
      intervalIntegral.integral_of_le (by linarith [L.property])]
    apply integral_congr_ae
    filter_upwards [hgcell] with y hy
    change g (y : Circle L) = f.val (y : Circle L) at hy
    rw [hy]
  rw [hmoll]
  have hp : Function.Periodic (fun t : ℝ => g (t : Circle L)) L.val := fun t => by
    dsimp only
    rw [AddCircle.coe_add_period]
  have hv := circleMollify_sub_le_of_marked_integrable_deriv
    (f := fun t : ℝ => g (t : Circle L)) hL marks hρ
    (g.continuous.comp (AddCircle.continuous_mk' L.val)) hp hA
    (by linarith [P.property.2.1] : 0 ≤ 1 + α) (by linarith : 1 + α < 1)
    hderiv hh hh1 x
  simpa only [show 1 - (1 + α) = -α by ring, Fintype.card_fin] using hv

end Riesz1.Internal

namespace Riesz1

/-- The global negative-exponent smoothing error from macroscopic data,
including evaluation at every mark of the unique continuous representative. -/
theorem regMicroKernel_error_negative_macroscopic (P : Parameters) (ρ : ℝ → ℝ) (hρ : IsMollifier ρ) (p : Profile)
    (η B : ℝ) (n : ℕ+) (marks : Fin (n : ℕ) → ℝ) (α C₀ : ℝ)
    (hη : 0 < η) (hB : 0 ≤ B) (hC₀ : 0 ≤ C₀)
    (hα0 : P.val.2 - 1 < α) (hα1 : α < P.val.2 / 2) (hαneg : α < 0)
    (hprim : PrimitiveRegularity unitLength η P.val.2 B ⟨p.val, p.property⟩)
    (hreg : TransportRegularity P unitLength ⟨p.val, p.property⟩ n marks α C₀) :
    ∃ C : ℝ, 0 < C ∧
      ∃ ψ : {g : Circle unitLength → ℝ // MemLp (fun x => (g x : ℂ)) 2 (arclength unitLength)},
        Continuous ψ.val ∧
        (∀ k : ℤ, coeff unitLength
          ⟨(fun x => (ψ.val x : ℂ)), complexL2Integrable unitLength _ ψ.property⟩ k =
            transportCoeffs P unitLength ⟨p.val, p.property⟩ k) ∧
        ∃ g : C(Circle unitLength, ℝ), ((g : Circle unitLength → ℝ) =ᵐ[arclength unitLength] p.val) ∧
          (let L := unitLength
           let m := (∫ y in Ioc (-(L.val / 2)) (L.val / 2), p.val (y : Circle L)) / L.val
           let q := deriv (fun t : ℝ => ψ.val (t : Circle L))
           ∀ x : ℝ, (∀ j, (x : Circle L) ≠ (marks j : Circle L)) →
             g (x : Circle L) = m + inverseConv P L.val q x) ∧
          ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ x : ℝ,
            |g (x : Circle unitLength) -
              circleMollify ρ unitLength.val h (fun y => p.val (y : Circle unitLength)) x| ≤ C * h ^ (-α) := by
  obtain ⟨D, hD, ψ, hc, hcoeff, hrep, hd⟩ := regMicroKernel_profile_derivative_macroscopic P p
    η B n marks α C₀ hη hB hC₀ hα0 hα1 hprim hreg
  have hfactor : 0 < 1 + (n : ℝ) * (1 + 2 / (-α)) := by
    have ha : 0 < -α := neg_pos.mpr hαneg
    have hn : 0 < (n : ℝ) := by exact_mod_cast n.property
    positivity
  refine ⟨D * (1 + (n : ℝ) * (1 + 2 / (-α))), mul_pos hD hfactor, ψ, hc, hcoeff, ?_⟩
  exact Internal.negative_error_of_inverse_derivative P unitLength (by norm_num [unitLength])
    ρ hρ η B hη hB ⟨p.val, p.property⟩ n marks α C₀ hα0.le hα1 hαneg hC₀ hprim hreg
    (deriv (fun t : ℝ => ψ.val (t : Circle unitLength))) (measurable_deriv _) D hD.le hrep
    (fun x hx => (hd x hx).2)

/-- The global negative-exponent smoothing error for compact profiles.
The constant precedes the shrinking sequence, its particle index, and every
additional observation scale satisfying the same regularity data. -/
theorem regMicroKernel_error_negative_compact (P : Parameters)
    (ρ : ℝ → ℝ) (hρ : IsMollifier ρ) (p : Profile) (hp : CompactProfile p) (η B : ℝ)
    (n : ℕ+) (marks : Fin (n : ℕ) → ℝ) (α C₀ : ℝ)
    (hη : 0 < η) (hB : 0 ≤ B) (hC₀ : 0 ≤ C₀)
    (hα0 : P.val.2 - 1 < α) (hα1 : α < P.val.2 / 2) (hαneg : α < 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ ell : Scales,
      Tendsto (fun k : ℕ => (ell ⟨k + 1, Nat.succ_pos k⟩).val) atTop (𝓝 0) →
      (∀ N, PrimitiveRegularity (observationLength (ell N)) η P.val.2 B
          ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ ∧
        TransportRegularity P (observationLength (ell N))
          ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩
            n marks α C₀) → ∀ a : Scale,
      PrimitiveRegularity (observationLength a) η P.val.2 B
        ⟨periodizedProfile p (observationLength a), periodizedProfileL2 p a⟩ →
      TransportRegularity P (observationLength a)
        ⟨periodizedProfile p (observationLength a), periodizedProfileL2 p a⟩ n marks α C₀ →
      let L := observationLength a
      ∃ ψ : {g : Circle L → ℝ // MemLp (fun x => (g x : ℂ)) 2 (arclength L)},
        Continuous ψ.val ∧
        (∀ k : ℤ, coeff L
          ⟨(fun x => (ψ.val x : ℂ)), complexL2Integrable L _ ψ.property⟩ k =
            transportCoeffs P L ⟨periodizedProfile p L, periodizedProfileL2 p a⟩ k) ∧
        ∃ g : C(Circle L, ℝ), ((g : Circle L → ℝ) =ᵐ[arclength L] periodizedProfile p L) ∧
          (let m := (∫ y in Ioc (-(L.val / 2)) (L.val / 2), periodizedProfile p L (y : Circle L)) / L.val
           let q := deriv (fun t : ℝ => ψ.val (t : Circle L))
           ∀ x : ℝ, (∀ j, (x : Circle L) ≠ (marks j : Circle L)) →
             g (x : Circle L) = m + inverseConv P L.val q x) ∧
          ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ x : ℝ,
            |g (x : Circle L) - circleMollify ρ L.val h (fun y => periodizedProfile p L (y : Circle L)) x| ≤
              C * h ^ (-α) := by
  obtain ⟨D, hD, hprofile⟩ := regMicroKernel_profile_derivative_compact P p hp
    η B n marks α C₀ hη hB hC₀ hα0 hα1
  have hfactor : 0 < 1 + (n : ℝ) * (1 + 2 / (-α)) := by
    have ha : 0 < -α := neg_pos.mpr hαneg
    have hn : 0 < (n : ℝ) := by exact_mod_cast n.property
    positivity
  refine ⟨D * (1 + (n : ℝ) * (1 + 2 / (-α))), mul_pos hD hfactor,
    fun ell hell hfamily a hprim hreg => ?_⟩
  obtain ⟨ψ, hc, hcoeff, hrep, hd⟩ := hprofile ell hell hfamily a hprim hreg
  refine ⟨ψ, hc, hcoeff, ?_⟩
  have hL : 1 ≤ (observationLength a).val := by
    change 1 ≤ a.val⁻¹
    exact (one_le_inv₀ a.property.1).mpr a.property.2
  exact Internal.negative_error_of_inverse_derivative P (observationLength a) hL
    ρ hρ η B hη hB ⟨periodizedProfile p (observationLength a), periodizedProfileL2 p a⟩
    n marks α C₀ hα0.le hα1 hαneg hC₀ hprim hreg
    (deriv (fun t : ℝ => ψ.val (t : Circle (observationLength a)))) (measurable_deriv _) D hD.le hrep
    (fun x hx => (hd x hx).2)

end Riesz1
