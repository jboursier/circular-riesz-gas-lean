/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.RegMicroKernelBounds
public import Riesz1.Variance.RegMicroKernelSupport

/-!
# Pointwise profiles and microscopic regularization errors

Every assertion of the kernel step in the proof of Lemma 5.3, in the macroscopic
and compact regimes. The compact constants and support interval precede
every scale sequence, and in fact cover every additional observation circle
with the same admissibility data.
-/

public section

open MeasureTheory Set Filter Topology

namespace Riesz1

/-- All pointwise microscopic kernel bounds in the macroscopic regime. -/
theorem regMicroKernel_complete_macroscopic (P : Parameters) (ρ : ℝ → ℝ)
    (hρ : IsMollifier ρ) (p : Profile) (η B : ℝ) (n : ℕ+)
    (marks : Fin (n : ℕ) → ℝ) (α C₀ : ℝ)
    (hη : 0 < η) (hB : 0 ≤ B) (hC₀ : 0 ≤ C₀)
    (hα0 : P.val.2-1 < α) (hα1 : α < P.val.2/2)
    (hprim : PrimitiveRegularity unitLength η P.val.2 B ⟨p.val, p.property⟩)
    (hreg : TransportRegularity P unitLength ⟨p.val, p.property⟩ n marks α C₀) :
    ∃ C H : ℝ, 0 < C ∧ 0 < H ∧
      MicroKernelBounds P ρ α C H n marks unitLength ⟨p.val, p.property⟩ := by
  obtain ⟨K, hK, hbounds⟩ := Internal.uniform_inverse_microKernelBounds P ρ hρ α hα0 hα1 n
  obtain ⟨A, hA, ψ, hc, hψ, hcoeff, hi, _hAC, hsup, hpoint⟩ :=
    macroscopic_regTransportBounds P p η B n marks α α C₀ hη hB hC₀ hα0.le hα1 le_rfl hα0
      hprim hreg
  let q := deriv (fun t : ℝ => ψ (t : Circle unitLength))
  have hqp : Function.Periodic q 1 := deriv_periodic_of (fun t => by
    change ψ ((t+1 : ℝ) : UnitAddCircle) = ψ (t : UnitAddCircle)
    rw [AddCircle.coe_add_period])
  have heq := (show Function.Periodic (fun t => |q t|) 1 from
    fun t => congrArg abs (hqp t)).intervalIntegral_add_eq (-(1/2)) 0
  norm_num only [neg_add_cancel_left, zero_add, show -(1/2 : ℝ)+1 = 1/2 by norm_num] at heq
  have hnorm : (∫ y in Ioc (-(unitLength.val/2)) (unitLength.val/2), |q y|) ≤ A := by
    have hh := hsup (0 : Circle unitLength)
    change |ψ 0| + (∫ t in (0 : ℝ)..1, |q t|) ≤ A at hh
    rw [intervalIntegral.integral_of_le (by norm_num)] at heq
    change (∫ y in Ioc (-(1/2 : ℝ)) (1/2), |q y|) ≤ A
    linarith [abs_nonneg (ψ 0)]
  refine ⟨K*A, 1/4, mul_pos hK hA, by norm_num, ?_⟩
  exact hbounds unitLength (by norm_num [unitLength]) η B C₀ hη hB hC₀
    ⟨p.val, p.property⟩ marks hprim hreg ⟨ψ, hψ⟩ hc hcoeff hi A hA hnorm hpoint (1/4) le_rfl

/-- All pointwise bounds and the fixed compact support, with constants
chosen before every shrinking scale sequence and observation circle. -/
theorem regMicroKernel_complete_compact (P : Parameters) (ρ : ℝ → ℝ)
    (hρ : IsMollifier ρ) (p : Profile) (hp : CompactProfile p)
    (η B : ℝ) (n : ℕ+) (marks : Fin (n : ℕ) → ℝ) (α C₀ : ℝ)
    (hη : 0 < η) (hB : 0 ≤ B) (hC₀ : 0 ≤ C₀)
    (hα0 : P.val.2-1 < α) (hα1 : α < P.val.2/2) :
    ∃ C H r : ℝ, 0 < C ∧ 0 < H ∧ 0 < r ∧ r < 1/2 ∧
      (∀ (L : Length), 1 ≤ L.val → ∀ h : ℝ, 0 < h → h ≤ H →
        (∀ x : ℝ, |x| ≤ L.val/2 → r ≤ |x| →
          circleMollify ρ L.val h (fun t => periodizedProfile p L (t : Circle L)) x = 0) ∧
        (∀ᵐ x : ℝ ∂(volume.restrict (Ioc (-(L.val/2)) (L.val/2))),
          r ≤ |x| → periodizedProfile p L (x : Circle L) -
            circleMollify ρ L.val h (fun t => periodizedProfile p L (t : Circle L)) x = 0)) ∧
      ∀ ell : Scales,
        Tendsto (fun k : ℕ => (ell ⟨k+1, Nat.succ_pos k⟩).val) atTop (𝓝 0) →
        (∀ N, PrimitiveRegularity (observationLength (ell N)) η P.val.2 B
            ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ ∧
          TransportRegularity P (observationLength (ell N))
            ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ n marks α C₀) →
        ∀ a : Scale,
          PrimitiveRegularity (observationLength a) η P.val.2 B
            ⟨periodizedProfile p (observationLength a), periodizedProfileL2 p a⟩ →
          TransportRegularity P (observationLength a)
            ⟨periodizedProfile p (observationLength a), periodizedProfileL2 p a⟩ n marks α C₀ →
          MicroKernelBounds P ρ α C H n marks (observationLength a)
            ⟨periodizedProfile p (observationLength a), periodizedProfileL2 p a⟩ := by
  obtain ⟨K, hK, hbounds⟩ := Internal.uniform_inverse_microKernelBounds P ρ hρ α hα0 hα1 n
  obtain ⟨A, hA, htransport⟩ := compact_regTransportBounds P p hp η B n marks α α C₀
    hη hB hC₀ hα0.le hα1 le_rfl hα0 hα1
  obtain ⟨H₀, r, hH₀, hr, hrhalf, hsupp⟩ := regMicroKernel_compact_support p hp ρ hρ
  let H := min H₀ (1/4)
  have hH : 0 < H := lt_min hH₀ (by norm_num)
  refine ⟨K*A, H, r, mul_pos hK hA, hH, hr, hrhalf,
    fun L hL h hh hhH => hsupp L hL h hh (hhH.trans (min_le_left _ _)),
    fun ell hell hfamily a hprim hreg => ?_⟩
  obtain ⟨ψ, hc, hψ, hcoeff, hi, _hAC, hsup, hpoint, _htail⟩ :=
    htransport ell hell hfamily a hprim hreg
  let L := observationLength a
  have hL : 1 ≤ L.val := (one_le_inv₀ a.property.1).mpr a.property.2
  have hnorm : (∫ y in Ioc (-(L.val/2)) (L.val/2),
      |deriv (fun t : ℝ => ψ (t : Circle L)) y|) ≤ A := by
    have hh := hsup (0 : Circle L)
    rw [intervalIntegral.integral_of_le (by linarith [L.property])] at hh
    have he : -L.val/2 = -(L.val/2) := by ring
    rw [he] at hh
    linarith [abs_nonneg (ψ 0)]
  exact hbounds L hL η B C₀ hη hB hC₀
    ⟨periodizedProfile p L, periodizedProfileL2 p a⟩ marks hprim hreg
    ⟨ψ, hψ⟩ hc hcoeff hi A hA hnorm hpoint H (min_le_right _ _)

/-- The kernel step in the proof of Lemma 5.3, every assertion in both profile
regimes. `MicroKernelBounds` spells out the inverse representative, its
absolute integrability and a.e. identity, both classical derivative bounds,
the unique negative-exponent continuous extension and everywhere error,
the positive-exponent global envelope, transition bound and away-region
bound. The compact clause also gives one fixed support interval.
All compact constants precede the scale sequence and observation scale.
The derivative bound for the error holds at all unmarked points, which
strengthens the required restriction `r ≥ 2h`. -/
theorem reg_micro_kernel :
  (∀ (P : Parameters) (ρ : ℝ → ℝ)
    (_hρ : IsMollifier ρ) (p : Profile) (η B : ℝ) (n : ℕ+)
    (marks : Fin (n : ℕ) → ℝ) (α C₀ : ℝ)
    (_hη : 0 < η) (_hB : 0 ≤ B) (_hC₀ : 0 ≤ C₀)
    (_hα0 : P.val.2-1 < α) (_hα1 : α < P.val.2/2)
    (_hprim : PrimitiveRegularity unitLength η P.val.2 B ⟨p.val, p.property⟩)
    (_hreg : TransportRegularity P unitLength ⟨p.val, p.property⟩ n marks α C₀),
    ∃ C H : ℝ, 0 < C ∧ 0 < H ∧
      MicroKernelBounds P ρ α C H n marks unitLength ⟨p.val, p.property⟩) ∧
  (∀ (P : Parameters) (ρ : ℝ → ℝ)
    (_hρ : IsMollifier ρ) (p : Profile) (_hp : CompactProfile p)
    (η B : ℝ) (n : ℕ+) (marks : Fin (n : ℕ) → ℝ) (α C₀ : ℝ)
    (_hη : 0 < η) (_hB : 0 ≤ B) (_hC₀ : 0 ≤ C₀)
    (_hα0 : P.val.2-1 < α) (_hα1 : α < P.val.2/2),
    ∃ C H r : ℝ, 0 < C ∧ 0 < H ∧ 0 < r ∧ r < 1/2 ∧
      (∀ (L : Length), 1 ≤ L.val → ∀ h : ℝ, 0 < h → h ≤ H →
        (∀ x : ℝ, |x| ≤ L.val/2 → r ≤ |x| →
          circleMollify ρ L.val h (fun t => periodizedProfile p L (t : Circle L)) x = 0) ∧
        (∀ᵐ x : ℝ ∂(volume.restrict (Ioc (-(L.val/2)) (L.val/2))),
          r ≤ |x| → periodizedProfile p L (x : Circle L) -
            circleMollify ρ L.val h (fun t => periodizedProfile p L (t : Circle L)) x = 0)) ∧
      ∀ ell : Scales,
        Tendsto (fun k : ℕ => (ell ⟨k+1, Nat.succ_pos k⟩).val) atTop (𝓝 0) →
        (∀ N, PrimitiveRegularity (observationLength (ell N)) η P.val.2 B
            ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ ∧
          TransportRegularity P (observationLength (ell N))
            ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ n marks α C₀) →
        ∀ a : Scale,
          PrimitiveRegularity (observationLength a) η P.val.2 B
            ⟨periodizedProfile p (observationLength a), periodizedProfileL2 p a⟩ →
          TransportRegularity P (observationLength a)
            ⟨periodizedProfile p (observationLength a), periodizedProfileL2 p a⟩ n marks α C₀ →
          MicroKernelBounds P ρ α C H n marks (observationLength a)
            ⟨periodizedProfile p (observationLength a), periodizedProfileL2 p a⟩) := by
  exact ⟨regMicroKernel_complete_macroscopic, regMicroKernel_complete_compact⟩

end Riesz1
