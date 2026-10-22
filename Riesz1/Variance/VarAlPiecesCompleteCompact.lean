/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.VarAlPieces
public import Riesz1.Variance.VarAlPiecesCompleteMacro
public import Riesz1.Variance.RegUniformFirstTransport
public import Riesz1.ToMathlib.CircleMollifyAE
public import Riesz1.Auxiliary.GradientSplittingZWeights

/-!
# Compact cutoff pieces for every transport representative

The fixed-cutoff decomposition passes from the continuous transport to
any representative of its L² class because circular mollification
preserves almost-everywhere equality. The translated derivative bounds
are expressed by the first and second gradient weights. All constants
precede the scale sequence, particle number and smoothing radius.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal ContDiff

namespace Riesz1

/-- Proposition 5.9, compact case, in final form. For every `N` with `1 ≤ N ℓ_N` and every
`h` in `[(N ℓ_N)⁻¹, 1]`, and for every `L²` representative `ψ` of the transport on the circle `ℓ_N⁻¹ 𝕋`,
the regularized transport is a sum of `m` smooth periodic pieces. After translating each piece, its
derivatives are bounded by `C` times `gradWeightOne` and `gradWeightTwo` at `K = N ℓ_N` and `L = ℓ_N⁻¹`. The
loop variance of the transport is at most `m` times the sum of the piece variances, and translating a piece
leaves its variance unchanged. The constants `m` and `C` precede the scale sequence
and do not depend on `N`, `h` or `ψ`. -/
theorem varAl_pieces_compact_complete (P : Parameters) (hPL : External.PrekopaLeindler)
    (p : Profile) (hp : CompactProfile p) (η B C₀ : ℝ) (n : ℕ+) (marks : Fin (n : ℕ) → ℝ) (α α' : ℝ)
    (hη : 0 < η) (hB : 0 ≤ B) (hC₀ : 0 ≤ C₀) (hα0 : P.val.2 - 1 ≤ α) (hα1 : α < P.val.2 / 2)
    (hαα' : α ≤ α') (hα'0 : P.val.2 - 1 < α') (hα'1 : α' < P.val.2 / 2)
    (ρ : ℝ → ℝ) (hρ : IsMollifier ρ) :
    ∃ (m : ℕ) (C : ℝ), 0 < C ∧ ∀ ell : Scales,
      Filter.Tendsto (fun k : ℕ => (ell ⟨k + 1, Nat.succ_pos k⟩).val) Filter.atTop (nhds 0) →
      (∀ N : ℕ+,
      PrimitiveRegularity (observationLength (ell N)) η P.val.2 B
          ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ ∧
        TransportRegularity P (observationLength (ell N))
          ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ n marks α C₀) →
      ∀ (N : ℕ+) (h : ℝ),
      1 ≤ (N : ℝ) * (ell N).val → ((N : ℝ) * (ell N).val)⁻¹ ≤ h → h ≤ 1 →
      ∀ ψ : {g : Circle (observationLength (ell N)) → ℝ //
          MemLp (fun x => (g x : ℂ)) 2 (arclength (observationLength (ell N)))},
        (∀ k : ℤ, coeff (observationLength (ell N)) ⟨(fun x => (ψ.val x : ℂ)),
            complexL2Integrable _ _ ψ.property⟩ k
            = transportCoeffs P (observationLength (ell N))
                ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ k) →
        ∃ φ : Fin m → ℝ → ℝ,
          (∀ j, ContDiff ℝ ∞ (φ j) ∧ Function.Periodic (φ j) (observationLength (ell N)).val ∧
              ∃ C' : NNReal, LipschitzWith C' (φ j)) ∧
          (∀ x : ℝ, circleMollify ρ (observationLength (ell N)).val h
              (fun t : ℝ => ψ.val (t : Circle (observationLength (ell N)))) x = ∑ j, φ j x) ∧
          (∀ j, ∃ a : ℝ,
              (∀ x : ℝ, |deriv (fun t => φ j (t + a)) x| ≤
                  C * gradWeightOne P.val.2 (1 - P.val.2 + α') ((N : ℝ) * (ell N).val)
                    ((ell N).val)⁻¹ x) ∧
              (∀ x : ℝ, |deriv (deriv (fun t => φ j (t + a))) x| ≤
                  C * gradWeightTwo P.val.2 (1 - P.val.2 + α') ((N : ℝ) * (ell N).val)
                    ((ell N).val)⁻¹ x)) ∧
          (∃ h1 : Integrable (fun X : Configuration N => loopFunctional P.val.2 (N : ℕ)
                (loopScaleField (ell N).val (fun x : ℝ => circleMollify ρ (observationLength (ell N)).val h
                  (fun t : ℝ => ψ.val (t : Circle (observationLength (ell N)))) x)) X.val)
                (gibbsMeasure P N),
              ∃ h2 : ∀ j, Integrable (fun X : Configuration N => loopFunctional P.val.2 (N : ℕ)
                  (loopScaleField (ell N).val (φ j)) X.val) (gibbsMeasure P N),
                variance (gibbsMeasure P N) _ h1 ≤
                  (m : ℝ≥0∞) * ∑ j, variance (gibbsMeasure P N) _ (h2 j)) ∧
          (∀ (j : Fin m) (a : ℝ), ∃ h1 : Integrable (fun X : Configuration N =>
                loopFunctional P.val.2 (N : ℕ) (loopScaleField (ell N).val (fun t => φ j (t + a))) X.val)
                  (gibbsMeasure P N),
              ∃ h2 : Integrable (fun X : Configuration N =>
                  loopFunctional P.val.2 (N : ℕ) (loopScaleField (ell N).val (φ j)) X.val)
                  (gibbsMeasure P N),
                variance (gibbsMeasure P N) _ h1 = variance (gibbsMeasure P N) _ h2) := by
  classical
  -- The theorem for continuous transports, and a continuous transport at each scale `ℓ_N`.
  obtain ⟨m, C, hC, hall⟩ :=
    varAl_pieces_compact P hPL p hp η B C₀ n marks α α' hη hB hC₀ hα0 hα1
      hαα' hα'0 hα'1 ρ hρ
  obtain ⟨_C₁, _hC₁, hT⟩ :=
    regUniform_firstTransport_compact P p hp η B n marks α α' C₀ hη hB hC₀ hα0 hα1 hαα'
      hα'0 hα'1 ρ hρ
  refine ⟨m, C, hC, fun ell hell hreg N h hN1 hN2 hh ψ hψcoeff => ?_⟩
  obtain ⟨ψ₁, hψ₁c, hψ₁L2, hψ₁coeff, -⟩ := hT ell hell hreg (ell N) (hreg N).1 (hreg N).2
  obtain ⟨φ, hφp, hφsum, hφd, hV, hT'⟩ :=
    hall ell hell hreg N h hN1 hN2 hh ⟨ψ₁, hψ₁L2⟩ hψ₁coeff hψ₁c
  -- The representative `ψ` equals `ψ₁` almost everywhere, so their mollifications agree.
  have hae : ψ.val =ᵐ[arclength (observationLength (ell N))] ψ₁ :=
    ae_eq_of_coeff_eq_real ψ.property hψ₁L2 (fun k => (hψcoeff k).trans (hψ₁coeff k).symm)
  have hmoll : ∀ x : ℝ, circleMollify ρ (observationLength (ell N)).val h
      (fun t : ℝ => ψ.val (t : Circle (observationLength (ell N)))) x =
        circleMollify ρ (observationLength (ell N)).val h
          (fun t : ℝ => ψ₁ (t : Circle (observationLength (ell N)))) x :=
    fun x => congrFun (circleMollify_congr_circle ρ (observationLength (ell N)) h hae) x
  have hfun : (fun x : ℝ => circleMollify ρ (observationLength (ell N)).val h
      (fun t : ℝ => ψ.val (t : Circle (observationLength (ell N)))) x) =
        (fun x : ℝ => circleMollify ρ (observationLength (ell N)).val h
          (fun t : ℝ => ψ₁ (t : Circle (observationLength (ell N)))) x) :=
    funext hmoll
  rw [hfun]
  refine ⟨φ, hφp, fun x => (hmoll x).trans (hφsum x), ?_, hV, hT'⟩
  simp only [gradWeightOne_eq_if, gradWeightTwo_eq_if]
  exact hφd

end Riesz1

end
