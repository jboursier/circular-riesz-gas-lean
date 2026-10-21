/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Kernel.AdmissibilityRegularityAbsoluteContinuity
public import Riesz1.Frozen.Admissible

/-!
# Continuous and absolutely continuous transport from admissibility

The regularity assertion for transport, for both alternatives in the
`Admissible` predicate. Every relevant circle has a real continuous representative with
the transport coefficients, a locally integrable derivative, and an absolutely
continuous lift on every compact interval. No Sobolev membership premise is used.
-/

public section

open MeasureTheory Filter
open scoped Topology

namespace Riesz1

/-- The regularity clauses on every circle selected by `Admissible`.
The two alternatives retain exactly the macroscopic and shrinking-scale cases of
`Admissible`. -/
theorem admissible_transport_absolutelyContinuous (P : Parameters) (p : Profile)
    (ell : Scales) (α : ℝ) (d : TestData) (h : Admissible P p ell α d) :
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
            (fun t : ℝ => ψ (t : Circle (observationLength (ell N)))) a b)) := by
  obtain ⟨hα0, hα1, hη, _, hB, hC, hcases⟩ := h
  rcases hcases with ⟨hell, hprim, hreg⟩ | ⟨hp, hell, hreg⟩
  · left
    refine ⟨hell, ?_⟩
    exact exists_absolutelyContinuous_transport P unitLength d.1 d.2.1 hη hB.le
      ⟨p.val, p.property⟩ d.2.2.2.1 d.2.2.2.2 α d.2.2.1 hα0 hα1 hC.le hprim hreg
  · right
    refine ⟨hp, hell, fun N => ?_⟩
    exact exists_absolutelyContinuous_transport P (observationLength (ell N)) d.1 d.2.1 hη hB.le
      ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩
      d.2.2.2.1 d.2.2.2.2 α d.2.2.1 hα0 hα1 hC.le (hreg N).1 (hreg N).2

end Riesz1
