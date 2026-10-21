/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.RegMicroFinalStatistics
public import Riesz1.Variance.RegMicroAssemblyL2
public import Riesz1.Variance.RegMicroAssemblyRepresentatives
public import Riesz1.Variance.RegMicroNearFarNegative
public import Riesz1.Variance.RegMicroPositiveKernel

/-!
# One near-variance statement for either sign of the singularity

The two nonexceptional near estimates of Lemma 5.3
on the same inverse representative. In the negative case its values at
the marks may differ from the continuous extension. Almost everywhere
equality, transported to the Gibbs law, removes this discrepancy.
-/

public section

open MeasureTheory Set Filter

namespace Riesz1.Internal

/-- Every continuous transport witness gives the same original `L²`
error, independent of the witness used in the kernel theorem. -/
theorem regMicro_error_memLp_of_kernel (P : Parameters) (L : Length)
    (f ψ : {f : Circle L → ℝ // MemLp (fun z => (f z : ℂ)) 2 (arclength L)})
    (n : ℕ+) (a : Fin (n : ℕ) → ℝ) (α C H : ℝ)
    (ρ : ℝ → ℝ) (hρ : IsMollifier ρ) (h : ℝ) (hh : 0 < h)
    (hc : Continuous ψ.val)
    (hcoeff : ∀ k : ℤ, coeff L
      ⟨fun z => (ψ.val z : ℂ), complexL2Integrable L _ ψ.property⟩ k = transportCoeffs P L f k)
    (hkernel : MicroKernelBounds P ρ α C H n a L f) :
    let m := (∫ y in Ioc (-(L.val/2)) (L.val/2), f.val (y : Circle L))/L.val
    let e := fun z : Circle L => m + inverseConvCircle P L
      (deriv (fun t : ℝ => ψ.val (t : Circle L))) z - cltRegCircle hρ L hh f z
    (e =ᵐ[arclength L] fun z => f.val z-cltRegCircle hρ L hh f z) ∧
      MemLp (fun z => (e z : ℂ)) 2 (arclength L) := by
  rcases hkernel with ⟨ψ₀, hc₀, hcoeff₀, hrep, _⟩
  have heq := regMicro_transport_unique P L f ψ₀ ψ hc₀ hc hcoeff₀ hcoeff
  subst ψ₀
  exact regMicro_inverse_error_memLp P L f ψ ρ hρ hh hrep

/-- The actual inverse error's near sum has variance `D C² K^(2α)`
for both signs of `α`. This includes `N=1` and balls filling the circle.
The sole analytic input is the kernel conclusion. -/
theorem regMicro_near_variance_of_kernel (P : Parameters) (n : ℕ+) (α : ℝ)
    (hα : α ≠ 0) (hα1 : α < 1/2) :
    ∃ D : ℝ, 0 < D ∧ ∀ (hPL : External.PrekopaLeindler) (N : ℕ+) (ℓ : Scale),
      1 ≤ (N : ℝ)*ℓ.val →
      let L := observationLength ℓ
      let K := (N : ℝ)*ℓ.val
      ∀ (ρ : ℝ → ℝ) (hρ : IsMollifier ρ) (C H : ℝ), 0 ≤ C → K⁻¹ ≤ H →
      ∀ (a : Fin (n : ℕ) → ℝ),
        (∀ i j, i ≠ j → 8*K⁻¹ ≤ dist (a i : Circle L) (a j : Circle L)) →
      ∀ f : {f : Circle L → ℝ // MemLp (fun z => (f z : ℂ)) 2 (arclength L)},
        MicroKernelBounds P ρ α C H n a L f →
      ∀ ψ : {g : Circle L → ℝ // MemLp (fun z => (g z : ℂ)) 2 (arclength L)},
        Continuous ψ.val →
        (∀ k : ℤ, coeff L
          ⟨fun z => (ψ.val z : ℂ), complexL2Integrable L _ ψ.property⟩ k = transportCoeffs P L f k) →
      let m := (∫ y in Ioc (-(L.val/2)) (L.val/2), f.val (y : Circle L))/L.val
      let e := fun z : Circle L => m + inverseConvCircle P L
        (deriv (fun t : ℝ => ψ.val (t : Circle L))) z -
          cltRegCircle hρ L (show 0<K⁻¹ from
            inv_pos.mpr (mul_pos (by exact_mod_cast N.pos) ℓ.property.1)) f z
      ∃ hF : Integrable (fun X : Configuration N => ∑ i : Fin (N : ℕ),
          microNearError L.val K⁻¹ a e ((X.val i/ℓ.val : ℝ) : Circle L)) (gibbsMeasure P N),
        variance (gibbsMeasure P N) _ hF ≤ ENNReal.ofReal (D*C^2*K^(2*α)) := by
  rcases lt_or_gt_of_ne hα with hneg | hpos
  · obtain ⟨D, hD, hb⟩ := micro_near_negative_of_kernel P n
    refine ⟨D, hD, fun hPL N ℓ hK => ?_⟩
    dsimp only
    intro ρ hρ C H hC hH a hsep f hkernel ψ hc hcoeff
    let L := observationLength ℓ
    let K := (N : ℝ)*ℓ.val
    have hh : 0 < K⁻¹ := inv_pos.mpr (mul_pos (by exact_mod_cast N.pos) ℓ.property.1)
    obtain ⟨g, hg, hF, hv⟩ := hb hPL N ℓ hK ρ hρ α C H hneg hC hH a hsep f hkernel
    have he := (regMicro_error_memLp_of_kernel P L f ψ n a α C H ρ hρ K⁻¹ hh hc hcoeff hkernel).1
    have heq : (fun z : Circle L =>
        microNearError L.val K⁻¹ a
          (fun z => (∫ y in Ioc (-(L.val/2)) (L.val/2), f.val (y : Circle L))/L.val +
            inverseConvCircle P L (deriv (fun t : ℝ => ψ.val (t : Circle L))) z -
              cltRegCircle hρ L hh f z) z) =ᵐ[arclength L]
        microNearError L.val K⁻¹ a (fun z => g z-cltRegCircle hρ L hh f z) := by
      filter_upwards [he, hg] with z hz hgz
      change g z = f.val z at hgz
      simp only [microNearError, hz, hgz]
    have hstat := regMicro_plainSum_ae_eq P N ℓ heq
    refine ⟨hF.congr hstat.symm, ?_⟩
    exact (auxiliary_variance_congr _ hF hstat).trans_le hv
  · obtain ⟨D, hD, hb⟩ := micro_near_positive_of_kernel P n α hpos hα1
    refine ⟨D, hD, fun hPL N ℓ hK => ?_⟩
    dsimp only
    intro ρ hρ C H hC hH a hsep f hkernel ψ hc hcoeff
    obtain ⟨ψ₀, hc₀, hcoeff₀, _, _, hF, hv⟩ := hb hPL N ℓ hK ρ hρ C H hC hH a hsep f hkernel
    have heq := regMicro_transport_unique P (observationLength ℓ) f ψ₀ ψ hc₀ hc hcoeff₀ hcoeff
    subst ψ₀
    exact ⟨hF, hv⟩

end Riesz1.Internal
