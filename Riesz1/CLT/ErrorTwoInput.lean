/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.CLT.Identity
public import Riesz1.Frozen.Admissible
public import Riesz1.Frozen.Variance
public import Riesz1.Frozen.CentralRep

/-!
# Conditional loop-variance input

The conclusion of Proposition 5.9, stated as a hypothesis for the results that
use it. This is the needed assertion on the objects of the project. The
constant precedes the scale sequence. The transport is specified by its
Fourier coefficients, exactly as in `clt_identity`, so that no new
encoding or choice of transport is introduced.

The smoothing radius is arbitrary in `[K⁻¹, 1]`. The explicit positivity
certificate is redundant on that interval and makes its convolution
well-defined in the signature. This file supplies no proof of the input.
-/

@[expose] public section

open MeasureTheory
open scoped ContDiff

namespace Riesz1.Internal

/-- A copy of the full assertion of Lemma 5.2. Every quantity is
on the circle and Gibbs law of the project. The envelope and both particle sums
are written inline, so this introduces no alternative object definitions.
The radius `R` and the centre `c` are arbitrary. The anchored
bound is asserted at centre `c = 0` only. -/
def ErrorTwoAPrioriInput : Prop :=
  ∀ (P : Parameters) (lam : ℝ), 0 ≤ lam → ∀ ε : ℝ, 0 < ε →
    ∀ R : ℝ, 0 < R → ∀ c : ℝ,
      ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (a : Scale), 1 ≤ (N : ℝ) * a.val →
        ∀ M : ℝ, 0 ≤ M → ∀ f : Circle (observationLength a) → ℝ,
          ContDiff ℝ 1 (fun u : ℝ => f (u : Circle (observationLength a))) →
          (∀ u : ℝ, |deriv (fun t : ℝ => f (t : Circle (observationLength a))) u| ≤
            M * ((if |centralRep (observationLength a) ((u - c : ℝ) : Circle (observationLength a))| ≤ R
              then ((max |centralRep (observationLength a) ((u - c : ℝ) : Circle (observationLength a))|
                ((N : ℝ) * a.val)⁻¹) ^ (1 + lam))⁻¹ else 0) +
              (if R ≤ |centralRep (observationLength a) ((u - c : ℝ) : Circle (observationLength a))|
                then (|centralRep (observationLength a) ((u - c : ℝ) : Circle (observationLength a))| ^
                  (3 - P.val.2))⁻¹ else 0))) →
          let FA : Configuration N → ℝ := fun X => ∑ i : Fin (N : ℕ),
            f (((X.val i - X.val ⟨0, N.pos⟩) / a.val : ℝ) : Circle (observationLength a))
          let FB : Configuration N → ℝ := fun X => ∑ i : Fin (N : ℕ),
            f (((X.val i / a.val : ℝ)) : Circle (observationLength a))
          (c = 0 → ∃ hA : Integrable FA (gibbsMeasure P N), variance (gibbsMeasure P N) FA hA ≤
            ENNReal.ofReal (C * M ^ 2 * ((N : ℝ) * a.val) ^ (ε + max (2 * lam) P.val.2))) ∧
          (∃ hB : Integrable FB (gibbsMeasure P N), variance (gibbsMeasure P N) FB hB ≤
            ENNReal.ofReal (C * M ^ 2 * ((N : ℝ) * a.val) ^ (ε + max (2 * lam) P.val.2)))

/-- The uniform regularized loop-variance assertion of Proposition 5.9,
including integrability and the quantifier order of the paper. -/
def ErrorTwoLoopVarianceInput : Prop :=
  ∀ (P : Parameters) (p : Profile) (α : ℝ) (d : TestData)
    (ρ : ℝ → ℝ) (hρ : IsMollifier ρ) (ε : ℝ), 0 < ε →
    ∃ C : ℝ, 0 < C ∧ ∀ ell : Scales, Admissible P p ell α d →
      ∀ (N : ℕ+) (h : ℝ) (hh : 0 < h),
        1 ≤ (N : ℝ) * (ell N).val → ((N : ℝ) * (ell N).val)⁻¹ ≤ h → h ≤ 1 →
        ∀ ψ : Circle (loopMasterLength (ell N)) → ℝ,
          ∀ hψ : ContDiff ℝ ∞ (fun t : ℝ => ψ (t : Circle (loopMasterLength (ell N)))),
            (∀ k : ℤ, coeff (loopMasterLength (ell N))
              ⟨(fun z => (ψ z : ℂ)), complexL2Integrable _ _
                (loopMasterLengthTest _ ψ hψ).property⟩ k =
              transportCoeffs P (loopMasterLength (ell N))
                (loopMasterLengthTest _
                  (cltRegCircle hρ (loopMasterLength (ell N)) hh
                    ⟨periodizedProfile p (observationLength (ell N)),
                      periodizedProfileL2 p (ell N)⟩)
                  (cltRegCircle_contDiff hρ (loopMasterLength (ell N)) hh _)) k) →
            ∃ hL : Integrable
              (loopOnConfiguration (parametersExponent P) N (ell N)
                (loopMasterProfile (ell N) ψ hψ)) (gibbsMeasure P N),
              variance (gibbsMeasure P N) _ hL ≤
                ENNReal.ofReal (C * ((N : ℝ) * (ell N).val) ^
                  (ε + max 1 (2 * (1 - P.val.2 + α))))

end Riesz1.Internal
