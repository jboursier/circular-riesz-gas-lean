/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopAnchoringCutoff
public import Riesz1.Auxiliary.GradientSplittingIdentityMain

/-!
# Measurability of the anchored cutoff loop

The localized transport has the support required by the gradient splitting
identity. Consequently the cutoff loop is continuous on the anchored simplex
and is measurable for both the base law and the size-biased law.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace Riesz1

/-- The localized profile satisfies the circular support condition of the
gradient splitting identity, including the boundary of its support. -/
theorem loopAnchoring_transport_support {χ ψ : ℝ → ℝ}
    (hχs : tsupport χ ⊆ Ioo (-(1 / 4)) (1 / 4)) {N : ℕ+} {ℓ γ : ℝ}
    (hℓ : 0 < ℓ) (hP : GradPartial N ℓ γ) (y : ℝ)
    (hfar : ∀ m : ℤ, gradT N ℓ γ / 4 ≤ |y - m|) :
    loopTransport χ N ℓ γ ψ (y / ℓ) = 0 := by
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  have ht : 0 < gradT N ℓ γ := by
    simp only [gradT, hP, ↓reduceIte]
    exact div_pos (Real.rpow_pos_of_pos (mul_pos hN hℓ) _) hN
  have he : ℓ * loopCircleRep ℓ (y / ℓ) = y - (⌊y + 1 / 2⌋ : ℤ) := by
    unfold loopCircleRep
    rw [mul_sub, mul_div_cancel₀ _ hℓ.ne', mul_div_cancel₀ _ hℓ.ne']
  have hnot : ℓ * loopCircleRep ℓ (y / ℓ) / gradT N ℓ γ ∉ tsupport χ := by
    intro hh
    have ha := abs_lt.mpr (hχs hh)
    rw [he, abs_div, abs_of_pos ht, div_lt_iff₀ ht] at ha
    linarith [hfar ⌊y + 1 / 2⌋]
  simp only [loopTransport, hP, ↓reduceIte,
    image_eq_zero_of_notMem_tsupport hnot, zero_mul]

/-- The zero-anchored vector is in the ordered lift domain. -/
theorem loopAnchoring_anchorVector_mem {n : ℕ} {y : Fin n → ℝ}
    (hy : y ∈ anchoredDomain n) : anchorVector y ∈ orderedDomain n.succPNat := by
  rw [mem_orderedDomain_iff]
  simpa only [anchorVector_zero, anchorVector_succ, sub_zero] using
    (show (0 ≤ (0 : ℝ) ∧ (0 : ℝ) < 1) ∧
      (∀ j, 0 < y j ∧ y j < 1) ∧ StrictMono y from ⟨⟨le_rfl, zero_lt_one⟩, hy⟩)

/-- Continuity of the actual cutoff loop on its anchored domain. -/
theorem loopAnchoring_F_continuousOn {s γ ε ℓ : ℝ} {χ ψ : ℝ → ℝ}
    (hs : 0 < s) (hs1 : s < 1) (hℓ : 0 < ℓ)
    (hχ : ContDiff ℝ ∞ χ) (hψ : ContDiff ℝ ∞ ψ)
    (hχs : tsupport χ ⊆ Ioo (-(1 / 4)) (1 / 4))
    (hp : Function.Periodic ψ ℓ⁻¹) (n : ℕ) :
    ContinuousOn (fun y : Fin n → ℝ =>
      loopCutoffF χ s γ ε n.succPNat ℓ ψ (anchorVector y)) (anchoredDomain n) := by
  have hcont : Continuous (fun y : Fin n → ℝ => anchorVector y) := by
    unfold anchorVector
    fun_prop
  have hloop := (gradient_splitting_identity
    (contDiff_loopTransport hχ hψ hχs n.succPNat hℓ γ) hℓ
    (by simpa only [one_div] using loopTransport_periodic (N := n.succPNat) (γ := γ) hℓ χ hp)
    hs hs1 (loopAnchoring_transport_support hχs hℓ)).1.continuousOn
  have hη := (loopCutoff_locallyLipschitzOn s γ ε n.succPNat hℓ).continuousOn
  exact (hη.mul hloop).comp hcont.continuousOn (fun _ hy => loopAnchoring_anchorVector_mem hy)

/-- The anchored cutoff loop is almost everywhere strongly measurable under
the base anchored law. No values outside the anchored simplex are used. -/
theorem loopAnchoring_F_aestronglyMeasurable {s γ ε ℓ : ℝ} {χ ψ : ℝ → ℝ}
    (hs : 0 < s) (hs1 : s < 1) (hℓ : 0 < ℓ)
    (hχ : ContDiff ℝ ∞ χ) (hψ : ContDiff ℝ ∞ ψ)
    (hχs : tsupport χ ⊆ Ioo (-(1 / 4)) (1 / 4))
    (hp : Function.Periodic ψ ℓ⁻¹) (P : Parameters) (n : ℕ) :
    AEStronglyMeasurable (fun y : Fin n → ℝ =>
      loopCutoffF χ s γ ε n.succPNat ℓ ψ (anchorVector y)) (anchoredLaw P n) := by
  have hm := (loopAnchoring_F_continuousOn (γ := γ) (ε := ε) hs hs1 hℓ hχ hψ hχs hp n).aestronglyMeasurable
    (μ := volume) (measurableSet_anchoredDomain n)
  exact (hm.mono_ac (withDensity_absolutelyContinuous _ _)).smul_measure _

/-- The anchored simplex has full measure for its normalized law. -/
theorem loopAnchoring_ae_domain (P : Parameters) (n : ℕ) :
    ∀ᵐ y ∂anchoredLaw P n, y ∈ anchoredDomain n := by
  have ha : ∀ᵐ y ∂(volume.restrict (anchoredDomain n)), y ∈ anchoredDomain n :=
    ae_restrict_mem (measurableSet_anchoredDomain n)
  exact Measure.ae_smul_measure ((withDensity_absolutelyContinuous _ _).ae_le ha) _

end Riesz1

end
