/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.VarAlPieces
public import Riesz1.Variance.RegUniformFirstTransport
public import Riesz1.ToMathlib.CircleMollifyAE
public import Riesz1.Auxiliary.GradientSplittingZWeights

/-!
# Reduction to one singularity, macroscopic circle: the final form

Proposition 5.9, macroscopic case (`ℓ = 1`, `K = N`). Compared with `varAl_pieces_macro`
(`VarAlPieces.lean`), this file makes two changes.

1. The hypothesis `Continuous ψ.val` is removed. The argument `ψ` ranges over every `L²` representative
   of the transport. Such a `ψ` agrees almost everywhere with the continuous transport `ψ₁` that
   `regUniform_firstTransport_macroscopic` produces from the admissibility hypotheses. The circular
   mollification depends only on the almost-everywhere class (`circleMollify_congr_circle`), so the
   decomposition for `ψ₁` transfers to `ψ`.
2. The envelopes are written with `gradWeightOne` and `gradWeightTwo` (`K = N`, `L = 1`). Their defining
   expressions are the `if` expressions of `varAl_pieces_macro`, as recorded in `gradWeightOne_eq_if` and
   `gradWeightTwo_eq_if`.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal ContDiff

namespace Riesz1

/-- The weight `w_1` of Lemma 5.7, unfolded: the envelope of
Proposition 5.9 with `a = 1 - s + α` and `K = N`. -/
theorem gradWeightOne_eq_if (s a K L u : ℝ) :
    gradWeightOne s a K L u =
      if circDist L u < 1 then max (circDist L u) K⁻¹ ^ (-a) else circDist L u ^ (s - 2) :=
  rfl

/-- The weight `w_2` of Lemma 5.7, unfolded: the envelope of the second
derivative in Proposition 5.9 with `a = 1 - s + α` and `K = N`. -/
theorem gradWeightTwo_eq_if (s a K L u : ℝ) :
    gradWeightTwo s a K L u =
      if circDist L u < 1 then max (circDist L u) K⁻¹ ^ (-(1 + a)) else circDist L u ^ (s - 3) :=
  rfl

/-- Proposition 5.9, macroscopic case, in final form. For every `N` with `1 ≤ N` and every
`h` in `[N⁻¹, 1]`, and for every `L²` representative `ψ` of the transport, the regularized transport
`circleMollify ρ 1 h ψ` is a sum of `m` smooth periodic pieces. After translating each piece, its
derivatives are bounded by `C` times `gradWeightOne` and `gradWeightTwo` at `K = N` and `L = 1`. The loop
variance of the transport is at most `m` times the sum of the piece variances, and translating a piece
leaves its variance unchanged. The constants `m` and `C` do not depend on `N`, `h` or `ψ`. -/
theorem varAl_pieces_macro_complete (P : Parameters) (hPL : External.PrekopaLeindler)
    (p : Profile) (η B C₀ : ℝ) (n : ℕ+) (marks : Fin (n : ℕ) → ℝ) (α : ℝ)
    (hη : 0 < η) (hB : 0 < B) (hC₀ : 0 < C₀)
    (hα0 : P.val.2 - 1 < α) (hα1 : α < P.val.2 / 2)
    (hprim : PrimitiveRegularity unitLength η P.val.2 B ⟨p.val, p.property⟩)
    (hreg : TransportRegularity P unitLength ⟨p.val, p.property⟩ n marks α C₀)
    (ρ : ℝ → ℝ) (hρ : IsMollifier ρ) :
    ∃ (m : ℕ) (C : ℝ), 0 < C ∧ ∀ (N : ℕ+) (h : ℝ), 1 ≤ (N : ℝ) → ((N : ℝ))⁻¹ ≤ h → h ≤ 1 →
      ∀ ψ : {g : Circle unitLength → ℝ // MemLp (fun x => (g x : ℂ)) 2 (arclength unitLength)},
        (∀ k : ℤ, coeff unitLength ⟨(fun x => (ψ.val x : ℂ)), complexL2Integrable _ _ ψ.property⟩ k
            = transportCoeffs P unitLength ⟨p.val, p.property⟩ k) →
        ∃ φ : Fin m → ℝ → ℝ,
          (∀ j, ContDiff ℝ ∞ (φ j) ∧ Function.Periodic (φ j) unitLength.val ∧
              ∃ C' : NNReal, LipschitzWith C' (φ j)) ∧
          (∀ x : ℝ, circleMollify ρ unitLength.val h
              (fun t : ℝ => ψ.val (t : Circle unitLength)) x = ∑ j, φ j x) ∧
          (∀ j, ∃ a : ℝ,
              (∀ x : ℝ, |deriv (fun t => φ j (t + a)) x| ≤
                  C * gradWeightOne P.val.2 (1 - P.val.2 + α) (N : ℝ) unitLength.val x) ∧
              (∀ x : ℝ, |deriv (deriv (fun t => φ j (t + a))) x| ≤
                  C * gradWeightTwo P.val.2 (1 - P.val.2 + α) (N : ℝ) unitLength.val x)) ∧
          (∃ h1 : Integrable (fun X : Configuration N => loopFunctional P.val.2 (N : ℕ)
                (loopScaleField 1 (fun x : ℝ => circleMollify ρ unitLength.val h
                  (fun t : ℝ => ψ.val (t : Circle unitLength)) x)) X.val) (gibbsMeasure P N),
              ∃ h2 : ∀ j, Integrable (fun X : Configuration N => loopFunctional P.val.2 (N : ℕ)
                  (loopScaleField 1 (φ j)) X.val) (gibbsMeasure P N),
                variance (gibbsMeasure P N) _ h1 ≤
                  (m : ℝ≥0∞) * ∑ j, variance (gibbsMeasure P N) _ (h2 j)) ∧
          (∀ (j : Fin m) (a : ℝ), ∃ h1 : Integrable (fun X : Configuration N =>
                loopFunctional P.val.2 (N : ℕ) (loopScaleField 1 (fun t => φ j (t + a))) X.val)
                  (gibbsMeasure P N),
              ∃ h2 : Integrable (fun X : Configuration N =>
                  loopFunctional P.val.2 (N : ℕ) (loopScaleField 1 (φ j)) X.val) (gibbsMeasure P N),
                variance (gibbsMeasure P N) _ h1 = variance (gibbsMeasure P N) _ h2) := by
  classical
  -- The theorem for continuous transports, and a continuous transport `ψ₁` from the hypotheses.
  obtain ⟨m, C, hC, hall⟩ :=
    varAl_pieces_macro P hPL p η B C₀ n marks α hη hB hC₀ hα0 hα1 hprim hreg ρ hρ
  obtain ⟨-, -, ψ₁, hψ₁c, hψ₁L2, hψ₁coeff, -⟩ :=
    regUniform_firstTransport_macroscopic P p η B n marks α α C₀ hη hB.le hC₀.le hα0.le hα1 le_rfl
      hα0 hα1 hprim hreg ρ hρ
  refine ⟨m, C, hC, fun N h hN1 hN2 hh ψ hψcoeff => ?_⟩
  obtain ⟨φ, hφp, hφsum, hφd, hV, hT⟩ := hall N h hN1 hN2 hh ⟨ψ₁, hψ₁L2⟩ hψ₁coeff hψ₁c
  -- The representative `ψ` equals `ψ₁` almost everywhere, so their mollifications agree.
  have hae : ψ.val =ᵐ[arclength unitLength] ψ₁ :=
    ae_eq_of_coeff_eq_real ψ.property hψ₁L2 (fun k => (hψcoeff k).trans (hψ₁coeff k).symm)
  have hmoll : ∀ x : ℝ, circleMollify ρ unitLength.val h
      (fun t : ℝ => ψ.val (t : Circle unitLength)) x =
        circleMollify ρ unitLength.val h (fun t : ℝ => ψ₁ (t : Circle unitLength)) x :=
    fun x => congrFun (circleMollify_congr_circle ρ unitLength h hae) x
  have hfun : (fun x : ℝ => circleMollify ρ unitLength.val h
      (fun t : ℝ => ψ.val (t : Circle unitLength)) x) =
        (fun x : ℝ => circleMollify ρ unitLength.val h (fun t : ℝ => ψ₁ (t : Circle unitLength)) x) :=
    funext hmoll
  rw [hfun]
  exact ⟨φ, hφp, fun x => (hmoll x).trans (hφsum x), hφd, hV, hT⟩

end Riesz1

end
