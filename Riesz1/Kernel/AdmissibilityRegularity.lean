/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Kernel.AdmissibilityRegularityUniform

/-!
# Regularity supplied by admissibility

Collected statement of the regularity of admissible data: continuous and absolutely
continuous transport, local integrability across the marks, circle and line Sobolev
membership, finite variances, Fourier decay with constants before the scale sequence,
and convergence of the compact-profile variance.
-/

public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace Riesz1

/-- The regularity supplied by admissibility, in full. The Fourier constant is uniform over
every scale sequence satisfying the same fixed profile data. The compact conclusion includes
the quantitative variance comparison at every scale and convergence along every filter. -/
theorem admissibility_regularity (P : Parameters) (p : Profile) (ell : Scales)
    (α : ℝ) (d : TestData) (h : Admissible P p ell α d) :
    (((∀ N, (ell N).val = 1) ∧
      ∃ ψ : Circle unitLength → ℝ, Continuous ψ ∧
        ∃ hψ : MemLp (fun x => (ψ x : ℂ)) 2 (arclength unitLength),
          (∀ k : ℤ, coeff unitLength
            ⟨(fun x => (ψ x : ℂ)), complexL2Integrable unitLength _ hψ⟩ k =
              transportCoeffs P unitLength ⟨p.val, p.property⟩ k) ∧
          LocallyIntegrable (deriv (fun t : ℝ => ψ (t : Circle unitLength))) volume ∧
          ∀ a b : ℝ, AbsolutelyContinuousOnInterval
            (fun t : ℝ => ψ (t : Circle unitLength)) a b) ∨
     (CompactProfile p ∧
      Tendsto (fun n : ℕ => (ell ⟨n + 1, Nat.succ_pos n⟩).val) atTop (𝓝 0) ∧
      ∀ N, ∃ ψ : Circle (observationLength (ell N)) → ℝ, Continuous ψ ∧
        ∃ hψ : MemLp (fun x => (ψ x : ℂ)) 2 (arclength (observationLength (ell N))),
          (∀ k : ℤ, coeff (observationLength (ell N))
            ⟨(fun x => (ψ x : ℂ)), complexL2Integrable (observationLength (ell N)) _ hψ⟩ k =
              transportCoeffs P (observationLength (ell N))
                ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ k) ∧
          LocallyIntegrable (deriv (fun t : ℝ => ψ (t : Circle (observationLength (ell N)))))
            volume ∧
          ∀ a b : ℝ, AbsolutelyContinuousOnInterval
            (fun t : ℝ => ψ (t : Circle (observationLength (ell N)))) a b)) ∧
    (∀ N : ℕ+, CircleSobolev ((1 - P.val.2) / 2)
      (fun x => (testAtScale p (ell N) x : ℂ))) ∧
    (∀ N : ℕ+, circleVariance P p (ell N) < ⊤) ∧
    (∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 < K ∧ ∀ ell' : Scales, Admissible P p ell' α d →
      ∀ (N : ℕ+) (k : ℤ),
        1 ≤ |2 * Real.pi * (k : ℝ) / (observationLength (ell' N)).val| →
        ‖fourierCoeff (fun x => (testAtScale p (ell' N) x : ℂ)) k‖ ≤
          K * (observationLength (ell' N)).val⁻¹ *
            |2 * Real.pi * (k : ℝ) / (observationLength (ell' N)).val| ^ (α - 1 + ε)) ∧
    (CompactProfile p → ∀ (f0 : Lp ℂ 2 (volume : Measure ℝ)), RepresentsZeroExtension p f0 →
      LineSobolev ((1 - P.val.2) / 2) f0 ∧ lineVariance P f0 < ⊤ ∧
      (∃ C : ℝ, 0 < C ∧ ∀ a : Scale,
        CircleSobolev ((1 - P.val.2) / 2) (fun x => (testAtScale p a x : ℂ)) ∧
          circleVariance P p a < ⊤ ∧
          |(circleVariance P p a).toReal - (lineVariance P f0).toReal| ≤
            C * a.val ^ (2 - P.val.2)) ∧
      ∀ {ι : Type*} {l : Filter ι} (a : ι → Scale),
        Tendsto (fun i => (a i).val) l (𝓝 0) →
        Tendsto (fun i => (circleVariance P p (a i)).toReal) l (𝓝 (lineVariance P f0).toReal)) := by
  refine ⟨admissible_transport_absolutelyContinuous P p ell α d h,
    admissible_circleSobolev P p ell α d h, admissible_circleVariance_finite P p ell α d h,
    fun ε hε => admissible_coeff_decay_uniform P p α d ε hε, fun hp f0 hf0 => ?_⟩
  obtain ⟨hline, hfin, hrate⟩ := admissible_compact_variance P p hp ell α d h f0 hf0
  exact ⟨hline, hfin, hrate, fun a ha =>
    admissible_compact_variance_tendsto P p hp ell α d h f0 hf0 a ha⟩

end Riesz1
