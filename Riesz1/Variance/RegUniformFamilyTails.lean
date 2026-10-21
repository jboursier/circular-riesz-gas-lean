/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.RegUniformIntegralTails
public import Riesz1.Variance.RegUniformAdmissibilityCompact
public import Riesz1.ToMathlib.MollifyLineIntegralNorm
public import Riesz1.Kernel.AdmissibilityRegularityProfileFourier

/-! # Compact derivative tails uniform over both fixed smoothing families

The last family-uniform tail clause of Lemma 5.1.
-/

public section

open MeasureTheory Filter
open scoped ContDiff Topology

namespace Riesz1

/-- The actual compact smoothing families have uniformly bounded line integral
norms and uniformly bounded first and second smoothed transport tails. All
constants precede the sequence, both smoothing parameters and the circle. -/
theorem regUniform_familyTails_compact (P : Parameters) (p : Profile)
    (hp : CompactProfile p) (η B : ℝ) (n : ℕ+) (marks : Fin (n : ℕ) → ℝ)
    (α α' C₀ : ℝ) (hη : 0 < η) (hB : 0 ≤ B) (hC₀ : 0 ≤ C₀)
    (hα0 : P.val.2 - 1 ≤ α) (hα1 : α < P.val.2 / 2) (hα' : α ≤ α')
    (hα'0 : P.val.2 - 1 < α') (hα'1 : α' < P.val.2 / 2)
    (ρ : ℝ → ℝ) (hρ : IsMollifier ρ) :
    ∃ C H r : ℝ, 0 < C ∧ 0 < H ∧ 0 < r ∧ r < 1 / 2 ∧
      ∀ ell : Scales,
        Tendsto (fun k : ℕ => (ell ⟨k + 1, Nat.succ_pos k⟩).val) atTop (𝓝 0) →
        (∀ N, PrimitiveRegularity (observationLength (ell N)) η P.val.2 B
            ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ ∧
          TransportRegularity P (observationLength (ell N))
            ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ n marks α C₀) →
        ∀ t : ℝ, 0 < t → t ≤ H → ∃ g e : Profile,
          (∀ x : ℝ, g.val (x : UnitAddCircle) = circleMollify ρ 1 t
            (fun y : ℝ => p.val (y : UnitAddCircle)) x) ∧
          (∀ x, e.val x = p.val x - g.val x) ∧
          (∀ x : ℝ, r ≤ |x| → zeroExtension g x = 0) ∧
          (∀ᵐ x : ℝ, r ≤ |x| → zeroExtension e x = 0) ∧
          ∀ v : Profile, (v = g ∨ v = e) →
            (∫ x : ℝ, |zeroExtension v x|) ≤ 2 * ∫ x : ℝ, |zeroExtension p x| ∧
            ∀ a : Scale,
              PrimitiveRegularity (observationLength a) η P.val.2 B
                ⟨periodizedProfile p (observationLength a), periodizedProfileL2 p a⟩ →
              TransportRegularity P (observationLength a)
                ⟨periodizedProfile p (observationLength a), periodizedProfileL2 p a⟩ n marks α C₀ →
              ∃ ψ : Circle (observationLength a) → ℝ, Continuous ψ ∧
                ∃ hψ : MemLp (fun x => (ψ x : ℂ)) 2 (arclength (observationLength a)),
                  (∀ k, coeff (observationLength a) ⟨(fun x => (ψ x : ℂ)), complexL2Integrable _ _ hψ⟩ k =
                    transportCoeffs P (observationLength a)
                      ⟨periodizedProfile v (observationLength a), periodizedProfileL2 v a⟩ k) ∧
                  ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ x : ℝ,
                    2 ≤ dist (x : Circle (observationLength a)) 0 →
                    |deriv (circleMollify ρ (observationLength a).val h
                      (fun y : ℝ => ψ (y : Circle (observationLength a)))) x| ≤
                        C * dist (x : Circle (observationLength a)) 0 ^ (P.val.2 - 2) ∧
                    |deriv (deriv (circleMollify ρ (observationLength a).val h
                      (fun y : ℝ => ψ (y : Circle (observationLength a))))) x| ≤
                        C * dist (x : Circle (observationLength a)) 0 ^ (P.val.2 - 3) := by
  let Z := ∫ x : ℝ, |zeroExtension p x|
  have hZ : 0 ≤ Z := integral_nonneg fun _ => abs_nonneg _
  obtain ⟨C, hC, htail⟩ := Internal.compact_smoothed_tails_of_integral_bound P (2 * Z) (by positivity) ρ hρ
  obtain ⟨A, H, r, hA, hH, _, hr, hrhalf, hfamily⟩ :=
    regUniform_admissibility_compact P p hp η B n marks α α' C₀ hη hB hC₀ hα0 hα1 hα' hα'0 hα'1 ρ hρ
  obtain ⟨r₀, hr₀, hr₀half, hsupp⟩ := hp
  refine ⟨C, min H (1 / 2 - r₀), r, hC, lt_min hH (by linarith), hr, hrhalf,
    fun ell hell hdata t ht htH => ?_⟩
  have htH' : t ≤ H := htH.trans (min_le_left _ _)
  have hmargin : r₀ + t / 2 < 1 / 2 := by linarith [htH.trans (min_le_right H (1 / 2 - r₀))]
  obtain ⟨g, e, _, hgv, hev, hgzero, hezero, hgc, hec, hadm⟩ := hfamily ell hell hdata t ht htH'
  have hline := Internal.zeroExtension_circleMollify_eq_line hρ p g ht hmargin hsupp hgv
  have hgZ : (∫ x : ℝ, |zeroExtension g x|) ≤ Z := by
    simp_rw [hline]
    exact integral_abs_mollifyLine_le hρ ht (zeroExtension_integrable p)
  have hext : zeroExtension e = fun x => zeroExtension p x - zeroExtension g x := by
    funext x
    unfold zeroExtension
    split_ifs
    · exact hev _
    · ring
  have heZ : (∫ x : ℝ, |zeroExtension e x|) ≤ 2 * Z := by
    have hm := integral_mono (zeroExtension_integrable e).abs
      ((zeroExtension_integrable p).abs.add (zeroExtension_integrable g).abs)
      (fun x => by rw [hext]; exact abs_sub _ _)
    simp only [Pi.add_apply] at hm
    rw [integral_add (zeroExtension_integrable p).abs (zeroExtension_integrable g).abs] at hm
    linarith
  refine ⟨g, e, hgv, hev, hgzero, hezero, fun v hv => ?_⟩
  have hvZ : (∫ x : ℝ, |zeroExtension v x|) ≤ 2 * Z := by
    rcases hv with rfl | rfl
    · linarith
    · exact heZ
  have hvc : CompactProfile v := by rcases hv with rfl | rfl; exact hgc; exact hec
  refine ⟨hvZ, fun a hprim hreg => ?_⟩
  have hvdata := hadm a hprim hreg
  have hex : ∃ ψ : Circle (observationLength a) → ℝ, Continuous ψ ∧
      ∃ hψ : MemLp (fun x => (ψ x : ℂ)) 2 (arclength (observationLength a)),
        (∀ k, coeff (observationLength a) ⟨(fun x => (ψ x : ℂ)), complexL2Integrable _ _ hψ⟩ k =
          transportCoeffs P (observationLength a)
            ⟨periodizedProfile v (observationLength a), periodizedProfileL2 v a⟩ k) ∧
        LocallyIntegrable (deriv (fun y : ℝ => ψ (y : Circle (observationLength a)))) volume ∧
        ∀ u w, AbsolutelyContinuousOnInterval (fun y : ℝ => ψ (y : Circle (observationLength a))) u w := by
    rcases hv with rfl | rfl
    · exact exists_absolutelyContinuous_transport P (observationLength a) η B hη hB ⟨periodizedProfile v (observationLength a), periodizedProfileL2 v a⟩ n marks α' A
        hα'0.le hα'1 hA.le hvdata.1 hvdata.2.2.1
    · exact exists_absolutelyContinuous_transport P (observationLength a) η (2 * B) hη (by positivity) ⟨periodizedProfile v (observationLength a), periodizedProfileL2 v a⟩ n marks α' A
        hα'0.le hα'1 hA.le hvdata.2.1 hvdata.2.2.2
  obtain ⟨ψ, hc, hψ, hcoeff, hi, hAC⟩ := hex
  exact ⟨ψ, hc, hψ, hcoeff, htail v hvc hvZ a ψ hc hψ hcoeff hi hAC⟩

end Riesz1
