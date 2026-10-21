/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.EllipticRegularity.Exhaustion
public import Mathlib.Analysis.Calculus.Rademacher

/-!
# Weak derivatives of Lipschitz cutoffs

Rademacher's derivative of a real Lipschitz cutoff satisfies exactly the
weak-derivative predicate used for the interior H² regularity argument. This does not
yet extend the solution's test identity to products with that cutoff.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ContDiff NNReal ENNReal

namespace Riesz1

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- A Lipschitz function has its almost everywhere classical directional
derivative as its weak derivative in the part 1 encoding. -/
theorem hasWeakDirectionalDerivativeOn_of_lipschitz {b : E → ℝ} {C : ℝ≥0}
    (hb : LipschitzWith C b) (U : Set E) (v : E) :
    HasWeakDirectionalDerivativeOn U b (fun x => fderiv ℝ b x v) v := by
  have he : (fun x => lineDeriv ℝ b x v) =ᵐ[volume] (fun x => fderiv ℝ b x v) := by
    filter_upwards [hb.ae_differentiableAt (μ := volume)] with x hx
    exact hx.lineDeriv_eq_fderiv
  have hd : HasWeakDirectionalDerivativeOn univ b (fun x => lineDeriv ℝ b x v) v := by
    refine ⟨hb.continuous.locallyIntegrable.locallyIntegrableOn univ,
      (hb.locallyIntegrable_lineDeriv (μ := volume) v).locallyIntegrableOn univ, ?_⟩
    intro φ hφ hφc _
    obtain ⟨D, hD⟩ := hφ.lipschitzWith_of_hasCompactSupport hφc (by simp)
    have hi := hb.integral_lineDeriv_mul_eq (μ := volume) hD hφc v
    have hdφ (x : E) : lineDeriv ℝ φ x (-v) = -(fderiv ℝ φ x v) := by
      rw [(hφ.differentiable (by norm_num) x).lineDeriv_eq_fderiv, map_neg]
    simpa only [smul_eq_mul, hdφ, neg_mul, mul_neg, integral_neg, mul_comm] using hi
  exact (hd.congr isOpen_univ Filter.EventuallyEq.rfl (ae_restrict_of_ae he)).mono
    (subset_univ U)

/-- Directional derivatives of a Lipschitz function are locally L².
This includes the Rademacher derivative of a nonsmooth cutoff. -/
theorem locallySquareIntegrableOn_fderiv_of_lipschitz {b : E → ℝ} {C : ℝ≥0}
    (hb : LipschitzWith C b) (U : Set E) (v : E) :
    LocallySquareIntegrableOn U (fun x => fderiv ℝ b x v) := by
  have he : (fun x => lineDeriv ℝ b x v) =ᵐ[volume] (fun x => fderiv ℝ b x v) := by
    filter_upwards [hb.ae_differentiableAt (μ := volume)] with x hx
    exact hx.lineDeriv_eq_fderiv
  intro K hK _
  let : IsFiniteMeasure (volume.restrict K) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hK.measure_lt_top (μ := volume)⟩
  have hm := ((hb.memLp_lineDeriv (μ := volume) v).restrict K).mono_exponent
    (show (2 : ℝ≥0∞) ≤ ⊤ from le_top)
  exact (memLp_congr_ae (ae_restrict_of_ae he)).mp hm

end Riesz1
