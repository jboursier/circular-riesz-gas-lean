/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.RegMicroKernelPositiveError
public import Riesz1.Variance.RegMicroKernelNegativeError
public import Riesz1.Variance.RegMicroKernelProfileErrorDerivative
public import Riesz1.Variance.RegMicroKernelProfileLocalError

/-!
# All pointwise microscopic bounds on one circle

The conclusion predicate records every analytic clause of the kernel step in the
proof of Lemma 5.3, using the actual profile, transport
coefficients, inverse convolution and circle mollification.
-/

@[expose] public section

open MeasureTheory Set Filter Topology

namespace Riesz1

/-- All pointwise clauses of the kernel step in the proof of Lemma 5.3 for one circle.
The local value bound explicitly includes its transition and away-region
consequences. Compact support is stated separately in the complete theorem. -/
def MicroKernelBounds (P : Parameters) (ρ : ℝ → ℝ) (α C H : ℝ)
    (n : ℕ+) (marks : Fin (n : ℕ) → ℝ) (L : Length)
    (f : {f : Circle L → ℝ // MemLp (fun x => (f x : ℂ)) 2 (arclength L)}) : Prop := by
  haveI : Fact (0 < L.val) := ⟨L.property⟩
  exact ∃ ψ : {g : Circle L → ℝ // MemLp (fun x => (g x : ℂ)) 2 (arclength L)},
    Continuous ψ.val ∧
    (∀ k : ℤ, coeff L
      ⟨(fun x => (ψ.val x : ℂ)), complexL2Integrable L _ ψ.property⟩ k =
        transportCoeffs P L f k) ∧
    let m := (∫ y in Ioc (-(L.val/2)) (L.val/2), f.val (y : Circle L)) / L.val
    let q := deriv (fun t : ℝ => ψ.val (t : Circle L))
    let F := fun t => m + inverseConv P L.val q t
    let e := fun h t => F t - circleMollify ρ L.val h (fun y => f.val (y : Circle L)) t
    let r := fun t : ℝ => cappedMarkDistance (fun j => (marks j : Circle L)) (t : Circle L)
    (∀ᵐ x : ℝ ∂(volume.restrict (Ioc (-(L.val/2)) (L.val/2))), f.val (x : Circle L) = F x) ∧
    (∀ h : ℝ, 0 < h → ∀ x : ℝ,
      circleMollify ρ L.val h F x = circleMollify ρ L.val h (fun y => f.val (y : Circle L)) x) ∧
    (∀ x : ℝ, (∀ j, (x : Circle L) ≠ (marks j : Circle L)) →
      IntegrableOn (fun y => q y * inverseKernel P L.val (x-y)) (Ioc (-(L.val/2)) (L.val/2)) ∧
      DifferentiableAt ℝ F x ∧ |deriv F x| ≤ C * r x ^ (-1-α)) ∧
    (∀ h : ℝ, 0 < h → h ≤ H → ∀ x : ℝ,
      (∀ j, (x : Circle L) ≠ (marks j : Circle L)) →
      DifferentiableAt ℝ (e h) x ∧
      |deriv (e h) x| ≤ C * h ^ (1-P.val.2) * r x ^ (-2+P.val.2-α)) ∧
    (α < 0 → ∃! g : C(Circle L, ℝ),
      ((g : Circle L → ℝ) =ᵐ[arclength L] f.val) ∧
      (∀ x : ℝ, (∀ j, (x : Circle L) ≠ (marks j : Circle L)) → g (x : Circle L) = F x) ∧
      ∀ h : ℝ, 0 < h → h ≤ H → ∀ x : ℝ,
        |g (x : Circle L) - circleMollify ρ L.val h (fun y => f.val (y : Circle L)) x| ≤ C * h ^ (-α)) ∧
    (0 < α → ∀ h : ℝ, 0 < h → h ≤ H →
      (∀ x : ℝ, (∀ j, (x : Circle L) ≠ (marks j : Circle L)) →
        |e h x| ≤ C * (h ^ (-α) + ∑ j, dist (x : Circle L) (marks j : Circle L) ^ (-α))) ∧
      (∀ᵐ x : ℝ ∂(volume.restrict (Ioc (-(L.val/2)) (L.val/2))),
        |f.val (x : Circle L) - circleMollify ρ L.val h (fun y => f.val (y : Circle L)) x| ≤
          C * (h ^ (-α) + ∑ j, dist (x : Circle L) (marks j : Circle L) ^ (-α)))) ∧
    (∀ h : ℝ, 0 < h → h ≤ H → ∀ x : ℝ,
      (∀ j, (x : Circle L) ≠ (marks j : Circle L)) → h ≤ r x →
      |e h x| ≤ C * h * r x ^ (-1-α)) ∧
    (∀ h : ℝ, 0 < h → h ≤ H → ∀ x : ℝ,
      2*h ≤ r x → r x ≤ 4*h → |e h x| ≤ C * h ^ (-α)) ∧
    ∀ δ : ℝ, 0 < δ → ∀ h : ℝ, 0 < h → h ≤ H → h ≤ δ →
      ∀ x : ℝ, δ ≤ r x → |e h x| ≤ (C * δ ^ (-1-α)) * h

namespace Internal

/-- Assemble all analytic clauses on one transport. The hypotheses about
that transport belong only to this internal helper. -/
theorem uniform_inverse_microKernelBounds (P : Parameters) (ρ : ℝ → ℝ)
    (hρ : IsMollifier ρ) (α : ℝ) (hα0 : P.val.2-1 < α)
    (hα1 : α < P.val.2/2) (n : ℕ+) :
    ∃ K : ℝ, 0 < K ∧ ∀ (L : Length), 1 ≤ L.val →
      ∀ (η B C₀ : ℝ), 0 < η → 0 ≤ B → 0 ≤ C₀ →
      ∀ (f : {f : Circle L → ℝ // MemLp (fun x => (f x : ℂ)) 2 (arclength L)})
      (marks : Fin (n : ℕ) → ℝ),
      PrimitiveRegularity L η P.val.2 B f → TransportRegularity P L f n marks α C₀ →
      ∀ (ψ : {g : Circle L → ℝ // MemLp (fun x => (g x : ℂ)) 2 (arclength L)}),
      Continuous ψ.val →
      (∀ k : ℤ, coeff L
        ⟨(fun x => (ψ.val x : ℂ)), complexL2Integrable L _ ψ.property⟩ k = transportCoeffs P L f k) →
      LocallyIntegrable (deriv (fun t : ℝ => ψ.val (t : Circle L))) volume →
      ∀ A : ℝ, 0 < A →
      (∫ y in Ioc (-(L.val/2)) (L.val/2), |deriv (fun t : ℝ => ψ.val (t : Circle L)) y|) ≤ A →
      (∀ x : ℝ, (∀ j, (x : Circle L) ≠ (marks j : Circle L)) →
        ContDiffAt ℝ 2 (fun t : ℝ => ψ.val (t : Circle L)) x ∧
        |deriv (fun t : ℝ => ψ.val (t : Circle L)) x| ≤ A *
          cappedMarkDistance (fun j => (marks j : Circle L)) (x : Circle L) ^ (-1+P.val.2-α) ∧
        |deriv (deriv (fun t : ℝ => ψ.val (t : Circle L))) x| ≤ A *
          cappedMarkDistance (fun j => (marks j : Circle L)) (x : Circle L) ^ (-2+P.val.2-α)) →
      ∀ H : ℝ, H ≤ 1/4 → MicroKernelBounds P ρ α (K*A) H n marks L f := by
  obtain ⟨D, hD, hderiv⟩ := uniform_inverse_profile_error_derivative P ρ hρ α hα0 hα1 n
  obtain ⟨J, hJ, hlocal⟩ := uniform_inverse_profile_local_error P ρ hρ α hα0 hα1 n
  have hpos : ∃ V : ℝ, 0 < V ∧ (0 < α →
      ∀ (L : Length), 1 ≤ L.val →
      ∀ (f : {f : Circle L → ℝ // MemLp (fun x => (f x : ℂ)) 2 (arclength L)})
      (marks : Fin (n : ℕ) → ℝ)
      (ψ : {g : Circle L → ℝ // MemLp (fun x => (g x : ℂ)) 2 (arclength L)}),
      Continuous ψ.val →
      (∀ k : ℤ, coeff L ⟨(fun x => (ψ.val x : ℂ)), complexL2Integrable L _ ψ.property⟩ k = transportCoeffs P L f k) →
      LocallyIntegrable (deriv (fun t : ℝ => ψ.val (t : Circle L))) volume →
      ∀ A : ℝ, 0 ≤ A →
      (∫ y in Ioc (-(L.val/2)) (L.val/2), |deriv (fun t : ℝ => ψ.val (t : Circle L)) y|) ≤ A →
      (∀ x : ℝ, (∀ j, (x : Circle L) ≠ (marks j : Circle L)) →
        ContDiffAt ℝ 2 (fun t : ℝ => ψ.val (t : Circle L)) x ∧
        |deriv (fun t : ℝ => ψ.val (t : Circle L)) x| ≤ A *
          cappedMarkDistance (fun j => (marks j : Circle L)) (x : Circle L) ^ (-1+P.val.2-α) ∧
        |deriv (deriv (fun t : ℝ => ψ.val (t : Circle L))) x| ≤ A *
          cappedMarkDistance (fun j => (marks j : Circle L)) (x : Circle L) ^ (-2+P.val.2-α)) →
      let m := (∫ y in Ioc (-(L.val/2)) (L.val/2), f.val (y : Circle L)) / L.val
      let q := deriv (fun t : ℝ => ψ.val (t : Circle L))
      (∀ᵐ x : ℝ ∂(volume.restrict (Ioc (-(L.val/2)) (L.val/2))), f.val (x : Circle L) = m + inverseConv P L.val q x) ∧
      ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ x : ℝ,
        (∀ j, (x : Circle L) ≠ (marks j : Circle L)) →
        |m + inverseConv P L.val q x - circleMollify ρ L.val h (fun y => f.val (y : Circle L)) x| ≤
          V*A*(h^(-α) + ∑ j, dist (x : Circle L) (marks j : Circle L)^(-α))) := by
    by_cases ha : 0 < α
    · obtain ⟨V, hV, hv⟩ := uniform_inverse_profile_positive_error P ρ hρ α ha hα1 n
      exact ⟨V, hV, fun _ => hv⟩
    · exact ⟨1, by norm_num, fun ha' => (ha ha').elim⟩
  obtain ⟨V, hV, hpositive⟩ := hpos
  let T := 1 + (n : ℝ) * (1 + 2 / |α|)
  have hT : 0 ≤ T := by dsimp [T]; positivity
  let K := D + J + V + D*T + 1
  have hK : 0 < K := by dsimp [K]; positivity
  have hDT : 0 ≤ D*T := mul_nonneg hD.le hT
  have hDK : D ≤ K := by dsimp [K]; linarith
  have hJK : J ≤ K := by dsimp [K]; linarith
  have hVK : V ≤ K := by dsimp [K]; linarith
  have hTK : D*T ≤ K := by dsimp [K]; linarith
  refine ⟨K, hK, fun L hL η B C₀ hη hB hC₀ f marks hp hr ψ hc hcoeff hi A hA hnorm hpoint H hH => ?_⟩
  have : Fact (0 < L.val) := ⟨L.property⟩
  let q := deriv (fun t : ℝ => ψ.val (t : Circle L))
  let m := (∫ y in Ioc (-(L.val/2)) (L.val/2), f.val (y : Circle L)) / L.val
  let F := fun t => m + inverseConv P L.val q t
  let e := fun h t => F t - circleMollify ρ L.val h (fun y => f.val (y : Circle L)) t
  let r := fun t : ℝ => cappedMarkDistance (fun j => (marks j : Circle L)) (t : Circle L)
  obtain ⟨hrep, hd, he⟩ := hderiv L f marks ψ hc hcoeff hi A hA.le hpoint
  obtain ⟨_hrep, hl⟩ := hlocal L f marks ψ hc hcoeff hi A hA.le hpoint
  have hDA : D*A ≤ K*A := mul_le_mul_of_nonneg_right hDK hA.le
  have hJA : J*A ≤ K*A := mul_le_mul_of_nonneg_right hJK hA.le
  have hVA : V*A ≤ K*A := mul_le_mul_of_nonneg_right hVK hA.le
  have hloc (h : ℝ) (hh : 0 < h) (x : ℝ)
      (hx : ∀ j, (x : Circle L) ≠ (marks j : Circle L)) (hhr : h ≤ r x) :
      |e h x| ≤ K*A*h*r x^(-1-α) :=
    (hl h hh x hx hhr).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hJA hh.le) (Real.rpow_nonneg (cappedMarkDistance_pos _ _ hx).le _))
  refine ⟨ψ, hc, hcoeff, hrep, ?_, ?_, ?_, ?_, ?_,
    fun h hh _hH x hx hhr => hloc h hh x hx hhr, ?_, ?_⟩
  · intro h _hh x
    unfold circleMollify
    rw [intervalIntegral.integral_of_le (by linarith [L.property]),
      intervalIntegral.integral_of_le (by linarith [L.property])]
    apply integral_congr_ae
    filter_upwards [hrep] with y hy
    rw [hy]
  · intro x hx
    refine ⟨(inverseConv_classical_of_transport P L marks ψ.val hi
      (fun y hy => (hpoint y hy).1) hx).1, ?_⟩
    exact ⟨(hd x hx).1, (hd x hx).2.trans
      (mul_le_mul_of_nonneg_right hDA (Real.rpow_nonneg (cappedMarkDistance_pos _ _ hx).le _))⟩
  · intro h hh hhH x hx
    obtain ⟨hed, heb⟩ := he h hh (by linarith) x hx
    exact ⟨hed, heb.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hDA (Real.rpow_nonneg hh.le _))
      (Real.rpow_nonneg (cappedMarkDistance_pos _ _ hx).le _))⟩
  · intro hneg
    obtain ⟨g, hg, hgF, hgerr⟩ := negative_error_of_inverse_derivative P L hL ρ hρ η B hη hB
      f n marks α C₀ hα0.le hα1 hneg hC₀ hp hr q (measurable_deriv _) (D*A)
      (by positivity) hrep hd
    refine ⟨g, ⟨hg, hgF, fun h hh hhH x => (hgerr h hh (by linarith) x).trans ?_⟩, ?_⟩
    · have ht : 1 + (n : ℝ) * (1 + 2 / (-α)) = T := by
        dsimp [T]; rw [abs_of_neg hneg]
      rw [ht]
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hh.le _)
      nlinarith [mul_le_mul_of_nonneg_right hTK hA.le]
    · intro v hv
      apply ContinuousMap.coe_injective
      exact (Continuous.ae_eq_iff_eq volume v.continuous g.continuous).mp (hv.1.trans hg.symm)
  · intro hapos h hh hhH
    obtain ⟨_rep, hv⟩ := hpositive hapos L hL f marks ψ hc hcoeff hi A hA.le hnorm hpoint
    have hb (x : ℝ) (hx : ∀ j, (x : Circle L) ≠ (marks j : Circle L)) :
        |e h x| ≤ K*A*(h^(-α) + ∑ j, dist (x : Circle L) (marks j : Circle L)^(-α)) := by
      apply (hv h hh (by linarith) x hx).trans
      apply mul_le_mul_of_nonneg_right hVA
      exact add_nonneg (Real.rpow_nonneg hh.le _) (Finset.sum_nonneg fun _ _ => Real.rpow_nonneg dist_nonneg _)
    refine ⟨hb, ?_⟩
    filter_upwards [hrep, ae_restrict_of_ae
      ((CircleSingularity.countable_marked_lifts (T := L.val) marks).ae_notMem volume)] with x hfx hx
    rw [hfx]
    apply hb
    simpa only [mem_ofPred_eq, not_exists] using hx
  · intro h hh _hhH x hxr _hrx
    have hx : ∀ j, (x : Circle L) ≠ (marks j : Circle L) := by
      intro j hj
      have hh' := hxr.trans (cappedMarkDistance_le_dist _ _ j)
      rw [hj, dist_self] at hh'
      linarith
    exact marked_local_error_transition (by positivity) hh (by linarith)
      (by linarith [P.property.2.1] : -1 ≤ α) (hloc h hh x hx (by linarith))
  · intro δ hδ h hh _hhH hhδ x hδr
    have hx : ∀ j, (x : Circle L) ≠ (marks j : Circle L) := by
      intro j hj
      have hh' := hδr.trans (cappedMarkDistance_le_dist _ _ j)
      rw [hj, dist_self] at hh'
      linarith
    exact marked_local_error_away (by positivity) hh.le hδ hδr
      (by linarith [P.property.2.1] : -1 ≤ α) (hloc h hh x hx (hhδ.trans hδr))

end Internal
end Riesz1
