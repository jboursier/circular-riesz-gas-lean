/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopAnchoringCutoff
public import Riesz1.Auxiliary.GradientSplittingEstimatesStructure

/-!
# The physical translation path in the anchoring argument

The anchoring part of Lemma 5.8. On the support of the cutoff,
the preceding-particle displacement is less than `K^ε`. The physical path
has length `D/N`, preserves every gap condition, and stays within the
claimed anchor bound. Its interior has negative anchor, so it does not
belong to the fundamental-region chart `orderedDomain`.
-/

public section

noncomputable section

namespace Riesz1

/-- Positive cutoff forces the displacement bound in the anchoring proof. -/
theorem loopAnchoring_displacement_lt {n : ℕ} {s γ ε ℓ : ℝ}
    (hℓ : 0 < ℓ) (hK : 1 ≤ ((n + 1).succPNat : ℝ) * ℓ) (hγ : 0 ≤ γ)
    (X : LoopPrecedingConfiguration (n + 1).succPNat)
    (hη : 0 < loopCutoff s γ ε (n + 1).succPNat ℓ (loopPrecedingY X)) :
    loopPrecedingD X < (((n + 1).succPNat : ℝ) * ℓ) ^ ε := by
  have hw : loopSizeWeight n (loopPrecedingOffsets X) <
      (((n + 1).succPNat : ℝ) * ℓ) ^ ε := by
    by_contra hh
    have hz := loopAnchoring_cutoff_zero (s := s) hℓ hK hγ
      (loopPrecedingOffsets X) (not_lt.mp hh)
    have he := congrArg (loopCutoff s γ ε (n + 1).succPNat ℓ)
      (loopPrecedingY_eq_anchorVector n X)
    have hzY : loopCutoff s γ ε (n + 1).succPNat ℓ (loopPrecedingY X) = 0 := he.trans hz
    linarith
  exact (loopPrecedingD_mem_weight n X).2.trans hw

/-- The physical translation has anchor within the stated microscopic bound. -/
theorem loopAnchoring_path_anchor_bound {N : ℕ+}
    (X : LoopPrecedingConfiguration N) {T v : ℝ}
    (hD : loopPrecedingD X ≤ T) (hv : 0 ≤ v) (hvD : v ≤ loopPrecedingD X) :
    |(N : ℝ) * gradLift N
      (fun k => loopPrecedingY X k + (v - loopPrecedingD X) / N) 0| ≤ T := by
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hz : gradLift N (loopPrecedingY X) 0 = 0 :=
    gradLift_zero_of_anchor (loopPrecedingY_zero X)
  rw [gradLift_add_const, hz, zero_add, mul_div_cancel₀ _ hN.ne']
  rw [abs_of_nonpos (sub_nonpos.mpr hvD)]
  linarith

/-- All gap inequalities are unchanged along the physical translation path. -/
theorem loopAnchoring_path_event_iff {N : ℕ+}
    (X : LoopPrecedingConfiguration N) (s γ ε ℓ v : ℝ) :
    gradEvent s γ ε N ℓ
      (fun k => loopPrecedingY X k + (v - loopPrecedingD X) / N) ↔
      gradEvent s γ ε N ℓ (loopPrecedingY X) :=
  gradEst_event_translate_iff s γ ε N ℓ _ _

/-- Before its endpoint the anchoring path lies outside the ordered
fundamental region. This identifies the domain extension needed to use the
gradient bound along the path. -/
theorem loopAnchoring_path_not_mem_orderedDomain {N : ℕ+}
    (X : LoopPrecedingConfiguration N) {v : ℝ} (hv : v < loopPrecedingD X) :
    (fun k => loopPrecedingY X k + (v - loopPrecedingD X) / N) ∉ orderedDomain N := by
  intro h
  have h0 := h.2.1
  change 0 ≤ loopPrecedingY X ⟨0, N.pos⟩ + (v - loopPrecedingD X) / N at h0
  rw [loopPrecedingY_zero, zero_add] at h0
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hneg : (v - loopPrecedingD X) / (N : ℝ) < 0 := div_neg_of_neg_of_pos (sub_neg.mpr hv) hN
  exact (not_lt.mpr h0) hneg

end Riesz1

end
