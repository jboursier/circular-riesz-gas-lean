/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.VarAlPiecesLoopLinear
public import Riesz1.Variance.VarAlPiecesLoopMemLp
public import Riesz1.Variance.VarAlPiecesLoopRotation
public import Riesz1.ToMathlib.VarianceFiniteSum

/-!
# The variance clause of Proposition 5.9

Proposition 5.9, variance assertion. Let `ψ = ∑ⱼ φⱼ` be a finite sum of
Lipschitz one-periodic-after-scaling profiles on the circle of length `ℓ⁻¹`, with `0 < ℓ ≤ 1`.
Then:

* the variance of the loop of `ψ` under the Gibbs law is at most `m` times the sum of the
  variances of the loops of the pieces `φⱼ`.
* translating a single piece `φⱼ` by a real `a` does not change the variance of its loop.

The first clause combines additivity of the loop in the profile, square integrability, and the
finite-sum variance inequality. The second clause is the translation invariance of the Gibbs
variance, applied to the scaled profile `ℓ φⱼ(·/ℓ)` with shift `ℓ a`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Riesz1

/-- Variances of two random variables that agree as functions coincide. -/
lemma variance_congr_fun_eq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {F G : Ω → ℝ} (hFG : F = G) (hF : Integrable F μ) (hG : Integrable G μ) :
    variance μ F hF = variance μ G hG := by
  subst hFG
  rfl

/-- The scaled field of a translated profile is the scaled field at a shifted point:
`ℓ φ(t + a)` at `u / ℓ` is `ℓ φ(·)` at `(u + ℓ a) / ℓ`. -/
lemma loopScaleField_translate {ℓ : ℝ} (hℓ0 : 0 < ℓ) (φ : ℝ → ℝ) (a : ℝ) :
    (fun u => loopScaleField ℓ φ (u + ℓ * a)) = loopScaleField ℓ (fun t => φ (t + a)) := by
  funext u
  unfold loopScaleField
  have hℓ : ℓ ≠ 0 := ne_of_gt hℓ0
  rw [add_div, mul_div_cancel_left₀ a hℓ]

/-- **The variance clause of Proposition 5.9.** Let `0 < s < 1`, `0 < ℓ ≤ 1`, and let
`ψ = ∑ⱼ φⱼ` be a finite sum over `Fin m` of Lipschitz profiles `φⱼ` that are periodic of period
`ℓ⁻¹`. Under the Gibbs law:

* the loop of `ψ` at scale `ℓ` is integrable, and its variance is at most `m` times the sum of
  the variances of the loops of the pieces, each of which is integrable.
* for every piece `j` and every real `a`, the loop of the translate `φⱼ(· + a)` at scale `ℓ` is
  integrable with the same variance as the loop of `φⱼ`. -/
theorem varAl_pieces_loop_variance (P : Parameters) (hPL : External.PrekopaLeindler)
    (N : ℕ+) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {ℓ : ℝ} (hℓ0 : 0 < ℓ) (_hℓ1 : ℓ ≤ 1)
    (m : ℕ) (ψ : ℝ → ℝ) (φ : Fin m → ℝ → ℝ) (hsum : ∀ x, ψ x = ∑ j, φ j x)
    (hper : ∀ j, Function.Periodic (φ j) ℓ⁻¹) (hlip : ∀ j, ∃ C : NNReal, LipschitzWith C (φ j)) :
    (∃ h1 : Integrable (fun X : Configuration N =>
          loopFunctional s (N : ℕ) (loopScaleField ℓ ψ) X.val) (gibbsMeasure P N),
        ∃ h2 : ∀ j, Integrable (fun X : Configuration N =>
            loopFunctional s (N : ℕ) (loopScaleField ℓ (φ j)) X.val) (gibbsMeasure P N),
          variance (gibbsMeasure P N) _ h1 ≤
            (m : ℝ≥0∞) * ∑ j, variance (gibbsMeasure P N) _ (h2 j)) ∧
    (∀ (j : Fin m) (a : ℝ), ∃ h1 : Integrable (fun X : Configuration N =>
          loopFunctional s (N : ℕ) (loopScaleField ℓ (fun t => φ j (t + a))) X.val)
            (gibbsMeasure P N),
        ∃ h2 : Integrable (fun X : Configuration N =>
            loopFunctional s (N : ℕ) (loopScaleField ℓ (φ j)) X.val) (gibbsMeasure P N),
          variance (gibbsMeasure P N) _ h1 = variance (gibbsMeasure P N) _ h2) := by
  have : IsFiniteMeasure (gibbsMeasure P N) := by
    have := (modelWellDefined P N).2.2
    infer_instance
  -- Each scaled piece is Lipschitz and one-periodic, and is square integrable under the Gibbs law.
  have hLip : ∀ j, ∃ M : NNReal, LipschitzWith M (loopScaleField ℓ (φ j)) := fun j =>
    loopScaleField_lipschitz (⟨φ j, hper j, hlip j⟩ : LoopScaleProfile ℓ)
  have hPer : ∀ j, Function.Periodic (loopScaleField ℓ (φ j)) 1 := fun j =>
    loopScaleField_periodic (hper j)
  have hF : ∀ j, MemLp (fun X : Configuration N =>
      loopFunctional s (N : ℕ) (loopScaleField ℓ (φ j)) X.val) 2 (gibbsMeasure P N) := by
    intro j
    obtain ⟨M, hM⟩ := hLip j
    exact memLp_loopFunctional_gibbs P hPL N hs0 hs1 hM (hPer j)
  -- The scaled profile of the sum is the sum of the scaled profiles.
  have hψ : ψ = fun x => ∑ j, φ j x := funext hsum
  have hfield : loopScaleField ℓ ψ = fun u => ∑ j, loopScaleField ℓ (φ j) u := by
    funext u
    unfold loopScaleField
    rw [hψ, Finset.mul_sum]
  have hsumF : ∀ X : Configuration N, loopFunctional s (N : ℕ) (loopScaleField ℓ ψ) X.val =
      ∑ j, loopFunctional s (N : ℕ) (loopScaleField ℓ (φ j)) X.val := fun X => by
    rw [hfield]
    exact loopFunctional_finsetSum hs0 hs1 (N : ℕ) Finset.univ (fun j => loopScaleField ℓ (φ j))
      hLip hPer X.val
  have hFun : (fun X : Configuration N => loopFunctional s (N : ℕ) (loopScaleField ℓ ψ) X.val) =
      (fun ω => ∑ j, (fun X : Configuration N =>
        loopFunctional s (N : ℕ) (loopScaleField ℓ (φ j)) X.val) ω) := funext hsumF
  constructor
  · -- Clause one: the variance of the sum is at most `m` times the sum of the variances.
    obtain ⟨hS, hle⟩ := variance_finsetSum_le (gibbsMeasure P N) m
      (fun j X => loopFunctional s (N : ℕ) (loopScaleField ℓ (φ j)) X.val) hF
    have h1 : Integrable (fun X : Configuration N =>
        loopFunctional s (N : ℕ) (loopScaleField ℓ ψ) X.val) (gibbsMeasure P N) := by
      rw [hFun]
      exact hS
    refine ⟨h1, fun j => (hF j).integrable one_le_two, ?_⟩
    calc variance (gibbsMeasure P N) _ h1
        = variance (gibbsMeasure P N) _ hS := variance_congr_fun_eq _ hFun h1 hS
      _ ≤ _ := hle
  · -- Clause two: a translated piece has the same loop variance as the piece.
    intro j a
    obtain ⟨M, hM⟩ := hLip j
    obtain ⟨h1', h2', heq⟩ := variance_loopFunctional_shift P hPL N hs0 hs1 hM (hPer j) (ℓ * a)
    have hcongr : (fun X : Configuration N =>
        loopFunctional s (N : ℕ) (loopScaleField ℓ (fun t => φ j (t + a))) X.val) =
        (fun X : Configuration N =>
          loopFunctional s (N : ℕ) (fun u => loopScaleField ℓ (φ j) (u + ℓ * a)) X.val) := by
      rw [loopScaleField_translate hℓ0 (φ j) a]
    have h1 : Integrable (fun X : Configuration N =>
        loopFunctional s (N : ℕ) (loopScaleField ℓ (fun t => φ j (t + a))) X.val)
        (gibbsMeasure P N) := by
      rw [hcongr]
      exact h1'
    refine ⟨h1, h2', ?_⟩
    exact (variance_congr_fun_eq _ hcongr h1 h1').trans heq

end Riesz1

end
