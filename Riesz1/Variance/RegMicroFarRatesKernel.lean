/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.RegMicroFarRatesFixed
public import Riesz1.Variance.RegMicroAssemblyRepresentatives
public import Riesz1.Variance.RegMicroKernelBounds

/-!
# Quantitative derivatives of the actual far pieces

Apply the kernel conclusion to the moving and fixed cutoffs.
Both far derivatives in Lemma 5.3 are
estimated, with constants independent of the microscopic radius.
-/

public section

open MeasureTheory Set

namespace Riesz1.Internal

/-- Both quantitative far derivative bounds on the same transport as
the kernel bounds, together with `C¹` representatives. The
kernel proposition is an already proved internal analytic input.
No variance estimate is a hypothesis. -/
theorem regMicro_far_derivatives_of_kernel (n : ℕ+) :
    ∃ Dₘ Dⱼ Dᵣ : ℝ, 0 < Dₘ ∧ 0 < Dⱼ ∧ 0 < Dᵣ ∧
    ∀ (P : Parameters) (L : Length) (η B₀ : ℝ), 0 < η → 0 ≤ B₀ →
    ∀ (f : {f : Circle L → ℝ // MemLp (fun x => (f x : ℂ)) 2 (arclength L)})
      (a : Fin (n : ℕ) → ℝ) (α C₀ : ℝ),
      P.val.2-1 ≤ α → α < P.val.2/2 → 0 ≤ C₀ →
      PrimitiveRegularity L η P.val.2 B₀ f → TransportRegularity P L f n a α C₀ →
    ∀ (ρ : ℝ → ℝ) (hρ : IsMollifier ρ) (C H : ℝ), 0 ≤ C →
      MicroKernelBounds P ρ α C H n a L f →
    ∀ (r₀ h : ℝ), 0 < r₀ → 4*r₀ < L.val → 2*r₀ ≤ 1 →
      ∀ hh : 0 < h, h ≤ r₀ → h ≤ 1 → h ≤ H → 8*h < L.val → 2*h < 1 →
      (∀ i j, i ≠ j → 4*r₀ ≤ dist (a i : Circle L) (a j : Circle L)) →
      (∀ i j, i ≠ j → 8*h ≤ dist (a i : Circle L) (a j : Circle L)) →
    ∃ ψ : {g : Circle L → ℝ // MemLp (fun x => (g x : ℂ)) 2 (arclength L)},
      Continuous ψ.val ∧
      (∀ k : ℤ, coeff L
        ⟨fun x => (ψ.val x : ℂ), complexL2Integrable L _ ψ.property⟩ k = transportCoeffs P L f k) ∧
    let m := (∫ y in Ioc (-(L.val/2)) (L.val/2), f.val (y : Circle L))/L.val
    let e := fun z : Circle L => m + inverseConvCircle P L
      (deriv (fun t : ℝ => ψ.val (t : Circle L))) z - cltRegCircle hρ L hh f z
    let q := 2-P.val.2+α
    let A := C*(1+(n : ℝ)*Dₘ/2*4^q)
    let B := C*r₀^(-1-α)
    (∀ᵐ x : ℝ ∂volume.restrict (Ioc (-(L.val/2)) (L.val/2)),
      e (x : Circle L) = f.val (x : Circle L) -
        circleMollify ρ L.val h (fun t => f.val (t : Circle L)) x) ∧
    (∀ j, ContDiff ℝ 1 (fun x : ℝ => microFarError L.val r₀ h a e j (x : Circle L))) ∧
    ContDiff ℝ 1 (fun x : ℝ => microFarRemainder L.val r₀ h a e (x : Circle L)) ∧
    (∀ j x, |deriv (fun t : ℝ => microFarError L.val r₀ h a e j (t : Circle L)) x| ≤
      (A+Dⱼ/r₀*B*(2*r₀)^q)*h^(1-P.val.2)*
        (max (dist (x : Circle L) (a j : Circle L)) h)^(-q)) ∧
    (∀ x, |deriv (fun t : ℝ => microFarRemainder L.val r₀ h a e (t : Circle L)) x| ≤
      (A*r₀^(-q)+(n : ℝ)*Dᵣ/r₀*B)*h^(1-P.val.2)) := by
  obtain ⟨Dₘ, hDₘ, hm⟩ := regMicro_moving_deriv_bound_everywhere n
  obtain ⟨Dⱼ, hDⱼ, hj⟩ := regMicro_fixed_deriv_bound n
  obtain ⟨Dᵣ, hDᵣ, hr⟩ := regMicro_remainder_deriv_bound n
  refine ⟨Dₘ, Dⱼ, Dᵣ, hDₘ, hDⱼ, hDᵣ,
    fun P L η B₀ hη hB₀ f a α C₀ hα0 hα1 hC₀ hprim hreg ρ hρ C H hC hkernel
      r₀ h hr₀ hrL hr1 hh hhr hh1 hhH hhL hhcap hsep₀ hsep => ?_⟩
  rcases hkernel with ⟨ψ, hc, hcoeff, _hrep, _hmoll, _hder, herror,
    _hnegative, _hpositive, _hloc, htrans, haway⟩
  refine ⟨ψ, hc, hcoeff, ?_⟩
  dsimp only
  let m := (∫ y in Ioc (-(L.val/2)) (L.val/2), f.val (y : Circle L))/L.val
  let e : Circle L → ℝ := fun z => m + inverseConvCircle P L
    (deriv (fun t : ℝ => ψ.val (t : Circle L))) z - cltRegCircle hρ L hh f z
  let q := 2-P.val.2+α
  let A := C*(1+(n : ℝ)*Dₘ/2*4^q)
  let B := C*r₀^(-1-α)
  let g : Circle L → ℝ := fun z => (1-microCutoffSum L.val (2*h) a z)*e z
  have hq : 0 ≤ q := by dsimp [q]; linarith
  have hqeq : -q = -2+P.val.2-α := by dsimp [q]; ring
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have heq : (fun t : ℝ => e (t : Circle L)) = fun t =>
      m + inverseConv P L.val (deriv (fun t : ℝ => ψ.val (t : Circle L))) t -
        circleMollify ρ L.val h (fun t => f.val (t : Circle L)) t := by
    funext t
    dsimp [e]
    rw [inverseConvCircle_coe, cltRegCircle_coe]
  have he (x : ℝ) (hx : ∀ j, (x : Circle L) ≠ (a j : Circle L)) :
      DifferentiableAt ℝ (fun t : ℝ => e (t : Circle L)) x ∧
      |deriv (fun t : ℝ => e (t : Circle L)) x| ≤
        C*h^(1-P.val.2)*(cappedMarkDistance (fun j => (a j : Circle L)) (x : Circle L))^(-q) := by
    rw [heq]
    simpa only [hqeq] using herror h hh hhH x hx
  have ht (x : ℝ) : 2*h ≤ cappedMarkDistance (fun j => (a j : Circle L)) (x : Circle L) →
      cappedMarkDistance (fun j => (a j : Circle L)) (x : Circle L) ≤ 4*h →
      |e (x : Circle L)| ≤ C*h^(-α) := by
    intro hx hy
    change |(fun t : ℝ => e (t : Circle L)) x| ≤ _
    rw [heq]
    exact htrans h hh hhH x hx hy
  have hg := regMicro_moving_differentiable L.property hh hhL a hsep e (fun x hx => (he x hx).1)
  have hgd (x : ℝ) : |deriv (fun t : ℝ => g (t : Circle L)) x| ≤
      A*h^(1-P.val.2)*(max (cappedMarkDistance (fun j => (a j : Circle L))
        (x : Circle L)) h)^(-q) := by
    simpa only [g, A, hqeq] using
      (hm L.val h L.property hh hhL hhcap a hsep P.val.2 α C hq hC e x
        (by simpa only [hqeq] using he x) (ht x))
  have hgv (x : ℝ) (hx : r₀ ≤ cappedMarkDistance (fun j => (a j : Circle L)) (x : Circle L)) :
      |g (x : Circle L)| ≤ B*h := by
    have hc := microCutoffSum_mem_Icc (by positivity : 0 < 2*h) a
      (by simpa only [show 4*(2*h) = 8*h by ring] using hsep) (x : Circle L)
    have hmask : |1-microCutoffSum L.val (2*h) a (x : Circle L)| ≤ 1 := by
      rw [abs_of_nonneg (sub_nonneg.mpr hc.2)]
      linarith [hc.1]
    have hv := haway r₀ hr₀ h hh hhH hhr x hx
    have hv' : |e (x : Circle L)| ≤ B*h := by
      change |(fun t : ℝ => e (t : Circle L)) x| ≤ _
      rw [heq]
      exact hv
    exact (by
      dsimp only [g]
      rw [abs_mul]
      exact (mul_le_of_le_one_left (abs_nonneg _) hmask).trans hv')
  obtain ⟨hrep, hjc, hrc⟩ := regMicro_far_contDiff_of_transport P L η B₀ hη hB₀ f n a α C₀
    hα0 hα1 hC₀ hprim hreg ρ hρ r₀ h hr₀ hh hrL hhL hsep ψ hc hcoeff
  refine ⟨hrep, hjc, hrc, ?_, ?_⟩
  · intro j x
    have hv := hj L.val r₀ h L.property hr₀ hrL hr1 hh hhr hh1 a hsep₀
      P.val.2 q A B P.property.2.1.le hq hA hB g x (hg x) (hgd x) (hgv x) j
    simpa only [microFarError, g, e, m, A, B, q, mul_assoc] using hv
  · intro x
    have hv := hr L.val r₀ h L.property hr₀ hrL (by linarith) hh hh1 a hsep₀
      P.val.2 q A B P.property.2.1.le hq hA hB g x (hg x) (hgd x) (hgv x)
    simpa only [microFarRemainder, g, e, m, A, B, q, mul_assoc] using hv

end Riesz1.Internal
