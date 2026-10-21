/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Kernel.AdmissibilityRegularityRepresentative
public import Riesz1.ToMathlib.CircleSingularityLocalization
public import Riesz1.ToMathlib.LocallyIntegrablePuncturedDerivative

/-!
# Absolute continuity of the admissible transport

This proves the absolute-continuity and locally-integrable-derivative clauses of the
regularity supplied by admissibility. Localizing (A3) gives a punctured power bound at every
real point.
The exponent is increased slightly to include the logarithmic endpoint. The derivative
is locally integrable, and the continuous representative is reconstructed from its integral.
-/

public section

open MeasureTheory Filter Set
open scoped Topology

namespace Riesz1
namespace Internal

/-- The pointwise (A2)–(A3) bounds imply local integrability of the derivative.
This helper applies to real functions and has no Fourier or representative hypotheses. -/
theorem locallyIntegrable_deriv_of_transport_bound (P : Parameters) (L : Length)
    {ι : Type*} [Fintype ι] (marks : ι → ℝ) (α C : ℝ)
    (hα0 : P.val.2 - 1 ≤ α) (hα1 : α < P.val.2 / 2) (hC : 0 ≤ C)
    (ψ : ℝ → ℝ)
    (hreg : ∀ x : ℝ, (∀ j, (x : Circle L) ≠ (marks j : Circle L)) →
      ContDiffAt ℝ 2 ψ x ∧
      |deriv (deriv ψ) x| ≤ C *
        ((if dist (x : Circle L) 0 ≤ 1 then
            ∑ j, dist (x : Circle L) (marks j : Circle L) ^ (-2 + P.val.2 - α)
          else 0) +
         (if 1 ≤ dist (x : Circle L) 0 then
            dist (x : Circle L) 0 ^ (-3 + P.val.2) else 0))) :
    LocallyIntegrable (deriv ψ) volume := by
  have : Fact (0 < L.val) := ⟨L.property⟩
  let b := 1 - P.val.2 + α
  let b' := (b + 1) / 2
  have hb : 0 ≤ b := by dsimp [b]; linarith
  have hb1 : b < 1 := by dsimp [b]; linarith [P.property.2.1]
  have hb' : 0 < b' := by dsimp [b']; linarith
  have hb'1 : b' < 1 := by dsimp [b']; linarith
  apply PuncturedDerivative.locallyIntegrable_of_punctured_deriv_bound hb' hb'1
  intro a
  obtain ⟨R, D, hR, hR1, hD, hlocal⟩ :=
    CircleSingularity.exists_punctured_power_bound L.property
      (fun j => (marks j : Circle L)) (e := -1 - b) (by linarith) a
  refine ⟨R, C * (D + 1), hR, mul_nonneg hC (by linarith), ?_, ?_⟩
  · intro t ht htR
    exact ((hreg t (hlocal t ht htR).1).1.derivWithin (m := 1) (by norm_num)).differentiableAt
      (by norm_num)
  · intro t ht htR
    obtain ⟨hmarks, hsum⟩ := hlocal t ht htR
    have htp : 1 ≤ |t - a| ^ (-1 - b) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht (htR.trans hR1) (by linarith)
    have hsum' :
        (if dist (t : Circle L) 0 ≤ 1 then
          ∑ j, dist (t : Circle L) (marks j : Circle L) ^ (-2 + P.val.2 - α)
        else 0) ≤ D * |t - a| ^ (-1 - b) := by
      rw [show -2 + P.val.2 - α = -1 - b by dsimp [b]; ring]
      split_ifs
      · exact hsum
      · positivity
    have htail : (if 1 ≤ dist (t : Circle L) 0 then
        dist (t : Circle L) 0 ^ (-3 + P.val.2) else 0) ≤ |t - a| ^ (-1 - b) := by
      split_ifs with hd
      · exact (Real.rpow_le_one_of_one_le_of_nonpos hd (by linarith [P.property.2.2])).trans htp
      · positivity
    calc |deriv (deriv ψ) t|
        ≤ C * ((if dist (t : Circle L) 0 ≤ 1 then
              ∑ j, dist (t : Circle L) (marks j : Circle L) ^ (-2 + P.val.2 - α)
            else 0) +
           (if 1 ≤ dist (t : Circle L) 0 then
              dist (t : Circle L) 0 ^ (-3 + P.val.2) else 0)) := (hreg t hmarks).2
      _ ≤ C * ((D + 1) * |t - a| ^ (-1 - b)) := by
        apply mul_le_mul_of_nonneg_left _ hC
        nlinarith [hsum', htail]
      _ = (C * (D + 1)) * |t - a| ^ (-1 - b) := by ring
      _ ≤ (C * (D + 1)) * |t - a| ^ (-1 - b') := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC (by linarith))
        exact Real.rpow_le_rpow_of_exponent_ge ht (htR.trans hR1) (by dsimp [b']; linarith)

end Internal

/-- (A1)–(A3) supply a continuous transport representative whose real lift is absolutely
continuous on every compact interval and whose derivative is locally integrable across
all marked points. This is the first assertion of the regularity supplied by admissibility. -/
theorem exists_absolutelyContinuous_transport (P : Parameters) (L : Length)
    (η B : ℝ) (hη : 0 < η) (hB : 0 ≤ B)
    (f : {f : Circle L → ℝ // MemLp (fun x => (f x : ℂ)) 2 (arclength L)})
    (p : ℕ+) (marks : Fin (p : ℕ) → ℝ) (α C : ℝ)
    (hα0 : P.val.2 - 1 ≤ α) (hα1 : α < P.val.2 / 2) (hC : 0 ≤ C)
    (hprim : PrimitiveRegularity L η P.val.2 B f)
    (hreg : TransportRegularity P L f p marks α C) :
    ∃ ψ : Circle L → ℝ, Continuous ψ ∧
      ∃ hψ : MemLp (fun x => (ψ x : ℂ)) 2 (arclength L),
        (∀ k : ℤ, coeff L ⟨(fun x => (ψ x : ℂ)), complexL2Integrable L _ hψ⟩ k =
          transportCoeffs P L f k) ∧
        LocallyIntegrable (deriv (fun t : ℝ => ψ (t : Circle L))) volume ∧
        ∀ a b : ℝ, AbsolutelyContinuousOnInterval (fun t : ℝ => ψ (t : Circle L)) a b := by
  have : Fact (0 < L.val) := ⟨L.property⟩
  obtain ⟨ψ, hc, hψ, hcoef, hpoint⟩ :=
    exists_continuous_transport_with_regularity P L η B hη hB f p marks α C hprim hreg
  have hi := Internal.locallyIntegrable_deriv_of_transport_bound P L marks α C
    hα0 hα1 hC _ hpoint
  refine ⟨ψ, hc, hψ, hcoef, hi, ?_⟩
  apply PuncturedDerivative.absolutelyContinuousOnInterval_of_countable_exceptional
    (hc.comp (AddCircle.continuous_mk' L.val))
    (CircleSingularity.countable_marked_lifts (T := L.val) marks) _ hi
  intro x hx
  exact (hpoint x (by simpa only [mem_ofPred_eq, not_exists] using hx)).1.differentiableAt
    (by norm_num)

end Riesz1
