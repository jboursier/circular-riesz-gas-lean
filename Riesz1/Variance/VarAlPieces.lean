/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.VarAlPiecesEnvelopeCompact
public import Riesz1.Variance.VarAlPiecesEnvelopeMacro
public import Riesz1.Variance.VarAlPiecesLoopVariance

/-!
# Reduction to one singularity: macroscopic and compact cases

Proposition 5.9, macroscopic and compact cases. The regularized transport `ψ_h` is a sum of
a fixed number `m` of smooth periodic pieces, with the derivative envelopes of `gradWeightOne` and
`gradWeightTwo` after translating each singular piece to its mark. The loop variance of `ψ_h` is at most
`m` times the sum of the loop variances of the pieces, and translating one piece does not change its loop
variance.

The decomposition and the envelopes come from `varAl_envelope_macro` and `varAl_envelope_compact`
(`VarAlPiecesEnvelope*.lean`). The variance assertions come from `varAl_pieces_loop_variance`
(`VarAlPiecesLoopVariance.lean`), applied to the same pieces. The loop variance part takes `External.PrekopaLeindler`
as an explicit hypothesis.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace Riesz1

/-- Proposition 5.9, macroscopic case (`ℓ = 1`, `K = N`): decomposition, derivative envelopes
and loop variance of the regularized transport on the unit circle. -/
theorem varAl_pieces_macro (P : Parameters) (hPL : External.PrekopaLeindler)
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
        Continuous ψ.val →
        ∃ φ : Fin m → ℝ → ℝ,
          (∀ j, ContDiff ℝ ∞ (φ j) ∧ Function.Periodic (φ j) unitLength.val ∧
              ∃ C' : NNReal, LipschitzWith C' (φ j)) ∧
          (∀ x : ℝ, circleMollify ρ unitLength.val h
              (fun t : ℝ => ψ.val (t : Circle unitLength)) x = ∑ j, φ j x) ∧
          (∀ j, ∃ a : ℝ,
              (∀ x : ℝ, |deriv (fun t => φ j (t + a)) x| ≤
                  C * (if circDist unitLength.val x < 1 then
                    max (circDist unitLength.val x) (N : ℝ)⁻¹ ^ (-(1 - P.val.2 + α))
                    else circDist unitLength.val x ^ (P.val.2 - 2))) ∧
              (∀ x : ℝ, |deriv (deriv (fun t => φ j (t + a))) x| ≤
                  C * (if circDist unitLength.val x < 1 then
                    max (circDist unitLength.val x) (N : ℝ)⁻¹ ^ (-(1 + (1 - P.val.2 + α)))
                    else circDist unitLength.val x ^ (P.val.2 - 3)))) ∧
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
  obtain ⟨m, C, hC, hEnv⟩ :=
    varAl_envelope_macro P p η B C₀ n marks α hη hB hC₀ hα0 hα1 hprim hreg ρ hρ
  refine ⟨m, C, hC, fun N h hN1 hN2 hh ψ hcoef hcont => ?_⟩
  obtain ⟨φ, hφp, hφsum, hφd⟩ := hEnv N h hN1 hN2 hh ψ hcoef hcont
  have hℓ0 : (0 : ℝ) < 1 := one_pos
  have hper : ∀ j, Function.Periodic (φ j) (1 : ℝ)⁻¹ := fun j => by
    rw [inv_one]
    exact (hφp j).2.1
  have hlip : ∀ j, ∃ C' : NNReal, LipschitzWith C' (φ j) := fun j => (hφp j).2.2
  obtain ⟨hV, hT⟩ := varAl_pieces_loop_variance P hPL N P.property.2.1 P.property.2.2 hℓ0 le_rfl m
    (fun x : ℝ => circleMollify ρ unitLength.val h (fun t : ℝ => ψ.val (t : Circle unitLength)) x)
    φ hφsum hper hlip
  exact ⟨φ, hφp, hφsum, hφd, hV, hT⟩

/-- Proposition 5.9, compact case (scale sequence `ℓ_N → 0`, `K = N ℓ_N`, observation length
`ℓ_N⁻¹`): decomposition, derivative envelopes and loop variance of the regularized transport. -/
theorem varAl_pieces_compact (P : Parameters) (hPL : External.PrekopaLeindler)
    (p : Profile) (hp : CompactProfile p) (η B C₀ : ℝ) (n : ℕ+) (marks : Fin (n : ℕ) → ℝ) (α : ℝ)
    (hη : 0 < η) (hB : 0 < B) (hC₀ : 0 < C₀) (hα0 : P.val.2 - 1 < α) (hα1 : α < P.val.2 / 2)
    (ell : Scales)
    (hell : Filter.Tendsto (fun k : ℕ => (ell ⟨k + 1, Nat.succ_pos k⟩).val) Filter.atTop (nhds 0))
    (hreg : ∀ N : ℕ+,
      PrimitiveRegularity (observationLength (ell N)) η P.val.2 B
          ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ ∧
        TransportRegularity P (observationLength (ell N))
          ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ n marks α C₀)
    (ρ : ℝ → ℝ) (hρ : IsMollifier ρ) :
    ∃ (m : ℕ) (C : ℝ), 0 < C ∧ ∀ (N : ℕ+) (h : ℝ),
      1 ≤ (N : ℝ) * (ell N).val → ((N : ℝ) * (ell N).val)⁻¹ ≤ h → h ≤ 1 →
      ∀ ψ : {g : Circle (observationLength (ell N)) → ℝ //
          MemLp (fun x => (g x : ℂ)) 2 (arclength (observationLength (ell N)))},
        (∀ k : ℤ, coeff (observationLength (ell N)) ⟨(fun x => (ψ.val x : ℂ)),
            complexL2Integrable _ _ ψ.property⟩ k
            = transportCoeffs P (observationLength (ell N))
                ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ k) →
        Continuous ψ.val →
        ∃ φ : Fin m → ℝ → ℝ,
          (∀ j, ContDiff ℝ ∞ (φ j) ∧ Function.Periodic (φ j) (observationLength (ell N)).val ∧
              ∃ C' : NNReal, LipschitzWith C' (φ j)) ∧
          (∀ x : ℝ, circleMollify ρ (observationLength (ell N)).val h
              (fun t : ℝ => ψ.val (t : Circle (observationLength (ell N)))) x = ∑ j, φ j x) ∧
          (∀ j, ∃ a : ℝ,
              (∀ x : ℝ, |deriv (fun t => φ j (t + a)) x| ≤
                  C * (if circDist (observationLength (ell N)).val x < 1 then
                    max (circDist (observationLength (ell N)).val x)
                      ((N : ℝ) * (ell N).val)⁻¹ ^ (-(1 - P.val.2 + α))
                    else circDist (observationLength (ell N)).val x ^ (P.val.2 - 2))) ∧
              (∀ x : ℝ, |deriv (deriv (fun t => φ j (t + a))) x| ≤
                  C * (if circDist (observationLength (ell N)).val x < 1 then
                    max (circDist (observationLength (ell N)).val x)
                      ((N : ℝ) * (ell N).val)⁻¹ ^ (-(1 + (1 - P.val.2 + α)))
                    else circDist (observationLength (ell N)).val x ^ (P.val.2 - 3)))) ∧
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
                  loopFunctional P.val.2 (N : ℕ) (loopScaleField (ell N).val (φ j)) X.val) (gibbsMeasure P N),
                variance (gibbsMeasure P N) _ h1 = variance (gibbsMeasure P N) _ h2) := by
  classical
  obtain ⟨m, C, hC, hEnv⟩ :=
    varAl_envelope_compact P p hp η B C₀ n marks α hη hB hC₀ hα0 hα1 ell hell hreg ρ hρ
  refine ⟨m, C, hC, fun N h hN1 hN2 hh ψ hcoef hcont => ?_⟩
  obtain ⟨φ, hφp, hφsum, hφd⟩ := hEnv N h hN1 hN2 hh ψ hcoef hcont
  have hℓ0 : (0 : ℝ) < (ell N).val := (ell N).property.1
  have hℓ1 : (ell N).val ≤ 1 := (ell N).property.2
  have hper : ∀ j, Function.Periodic (φ j) (ell N).val⁻¹ := fun j => (hφp j).2.1
  have hlip : ∀ j, ∃ C' : NNReal, LipschitzWith C' (φ j) := fun j => (hφp j).2.2
  obtain ⟨hV, hT⟩ := varAl_pieces_loop_variance P hPL N P.property.2.1 P.property.2.2 hℓ0 hℓ1 m
    (fun x : ℝ => circleMollify ρ (observationLength (ell N)).val h
      (fun t : ℝ => ψ.val (t : Circle (observationLength (ell N)))) x)
    φ hφsum hper hlip
  exact ⟨φ, hφp, hφsum, hφd, hV, hT⟩

end Riesz1

end
