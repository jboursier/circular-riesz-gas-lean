/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopAnchoringGradient
public import Riesz1.Auxiliary.LoopAnchoringRescaling
public import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Deterministic anchoring by common translation

The physical path in the anchoring part of Lemma 5.8 has length
`D/N`. Its derivative is controlled on the collision-free real lift chart.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace Riesz1

/-- The cutoff's larger-window event implies the gradient event on the
smaller window, with cyclic labels handled in either window regime. -/
theorem loopAnchoring_event_restrict {s γ ε ℓ : ℝ} {N : ℕ+}
    {X : Fin (N : ℕ) → ℝ} (hℓ : 0 < ℓ) (hK : 1 ≤ (N : ℝ) * ℓ) (hγ : 0 ≤ γ)
    (hX : gradEvent s (2 * γ) ε N ℓ X) : gradEvent s γ ε N ℓ X := by
  have hwin (i j : ℤ) (hi : i ∈ gradLabels N ℓ γ) (hj : gradInWindow N ℓ γ j) :
      ¬GradPartial N ℓ (2 * γ) ∨
        (i ∈ gradLabels N ℓ (2 * γ) ∧ j ∈ gradLabels N ℓ (2 * γ)) := by
    apply loop_pair_window_two hK hγ
    by_cases hP : GradPartial N ℓ γ
    · exact Or.inr ⟨hi, hj hP⟩
    · exact Or.inl hP
  exact ⟨fun i hi k hk _ hkN => gradEvent_pair_bound hX hℓ i k hkN (hwin i (i + k) hi hk),
    fun i hi hj => gradEvent_edge_bounds hX i (hwin i (i + 1) hi hj)⟩

/-- The gradient of the loop along common physical translation is its sum
of coordinate derivatives. -/
theorem loopAnchoring_hasDerivAt_translation {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    {ℓ γ : ℝ} (hℓ : 0 < ℓ) (hp : Function.Periodic ψ ℓ⁻¹)
    {s : ℝ} (hs : 0 < s) (hs1 : s < 1) {N : ℕ+}
    (hsupp : GradPartial N ℓ γ → ∀ y : ℝ,
      (∀ m : ℤ, gradT N ℓ γ / 4 ≤ |y - m|) → ψ (y / ℓ) = 0)
    (X : LoopPrecedingConfiguration N) (c : ℝ) :
    HasDerivAt (fun t : ℝ => gradLoop s ψ N ℓ γ (fun k => loopPrecedingY X k + t))
      (∑ k : Fin (N : ℕ), fderiv ℝ (gradLoop s ψ N ℓ γ)
        (fun k => loopPrecedingY X k + c) (Pi.single k 1)) c := by
  let q := fun t : ℝ => fun k => loopPrecedingY X k + t
  have hq : HasDerivAt q (fun _ => (1 : ℝ)) c :=
    hasDerivAt_pi.mpr fun k => (hasDerivAt_id c).const_add (loopPrecedingY X k)
  have hH := (contDiffAt_gradLoop hψ hℓ (by simpa only [one_div] using hp) hs hs1 hsupp
    (loopAnchoring_path_nonInt hℓ.le X c)).differentiableAt (by simp)
  have h := hH.hasFDerivAt.comp_hasDerivAt c hq
  have hone : (fun _ : Fin (N : ℕ) => (1 : ℝ)) = ∑ k : Fin (N : ℕ), Pi.single k 1 := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  simpa only [q, Function.comp_def, hone, map_sum] using h

/-- The deterministic translation error needed in the anchoring proof,
with the sharp leading power and constants before all configuration data. -/
theorem loopAnchoring_translation_error {s α γ : ℝ}
    (hs : 0 < s) (hs1 : s < 1) (hα : s - 1 ≤ α) (hα2 : α < s / 2)
    (hγ : max 4 (2 / s) ≤ γ) :
    ∃ εstar : ℝ, 0 < εstar ∧ ∃ κ : ℝ, 0 < κ ∧ ∀ ε : ℝ, 0 < ε → ε < εstar →
      ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (ℓ C₀ : ℝ) (ψ : ℝ → ℝ),
        2 ≤ (N : ℕ) → 0 < ℓ → ℓ ≤ 1 → 1 ≤ (N : ℝ) * ℓ → 0 ≤ C₀ →
        ContDiff ℝ ∞ ψ → Function.Periodic ψ ℓ⁻¹ →
        (∀ t, |deriv ψ t| ≤ C₀ * gradWeightOne s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ t) →
        (∀ t, |deriv (deriv ψ) t| ≤ C₀ * gradWeightTwo s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ t) →
        (GradPartial N ℓ γ → ∀ y : ℝ,
          (∀ m : ℤ, gradT N ℓ γ / 4 ≤ |y - m|) → ψ (y / ℓ) = 0) →
        ∀ X : LoopPrecedingConfiguration N,
          gradEvent s γ ε N ℓ (loopPrecedingY X) →
          loopPrecedingD X ≤ ((N : ℝ) * ℓ) ^ ε →
          |loopLocalLoop s N ℓ γ (loopScaleField ((N : ℝ) * ℓ) ψ) X -
            gradLoop s ψ N ℓ γ (loopPrecedingY X)| ≤
            C * C₀ * ((N : ℝ) * ℓ) ^ (1 - s + α + κ * ε) := by
  obtain ⟨εstar, hεstar, κ, hκ, hb⟩ := loopAnchoring_translation_gradient hs hs1 hα hα2 hγ
  refine ⟨εstar, hεstar, κ + 1, by linarith, fun ε hε hεs => ?_⟩
  obtain ⟨C, hC, hbound⟩ := hb ε hε hεs
  refine ⟨C, hC, fun N ℓ C₀ ψ hN hℓ hℓ1 hK hC₀ hψ hp h1 h2 hsupp X hX hD => ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hK0 : 0 < (N : ℝ) * ℓ := by linarith
  have hD0 := (loopPrecedingD_mem X).1
  let a := -loopPrecedingD X / (N : ℝ)
  let q := fun t : ℝ => fun k => loopPrecedingY X k + t
  let F := fun t : ℝ => gradLoop s ψ N ℓ γ (q t)
  let F' := fun t : ℝ => ∑ k : Fin (N : ℕ),
    fderiv ℝ (gradLoop s ψ N ℓ γ) (q t) (Pi.single k 1)
  have ha : a ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hN0.le
  have hder (t : ℝ) : HasDerivAt F (F' t) t :=
    loopAnchoring_hasDerivAt_translation hψ hℓ hp hs hs1 hsupp X t
  have hbd (t : ℝ) (ht : t ∈ Ico a 0) :
      ‖F' t‖ ≤ C * C₀ * (N : ℝ) * ((N : ℝ) * ℓ) ^ (1 - s + α + κ * ε) := by
    rw [Real.norm_eq_abs]
    apply hbound N ℓ C₀ ψ hN hℓ hℓ1 hK hC₀ hψ hp h1 h2 hsupp (q t)
      (loopAnchoring_path_nonInt hℓ.le X t)
      ((gradEst_event_translate_iff s γ ε N ℓ (loopPrecedingY X) t).mpr hX)
    rw [gradLift_add_const, gradLift_zero_of_anchor (loopPrecedingY_zero X), zero_add,
      abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hN0.le ht.2.le)]
    have htt : -loopPrecedingD X ≤ (N : ℝ) * t := by
      have := (div_le_iff₀ hN0).mp ht.1
      simpa only [mul_comm] using this
    linarith
  have he := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun t _ => (hder t).hasDerivWithinAt) hbd 0 ⟨ha, le_rfl⟩
  have hstart : F a = loopLocalLoop s N ℓ γ (loopScaleField ((N : ℝ) * ℓ) ψ) X := by
    simpa only [F, q, a, zero_sub, neg_div] using
      (loopAnchoring_localLoop_eq_gradLoop hψ hℓ hp s N X).symm
  have hend : F 0 = gradLoop s ψ N ℓ γ (loopPrecedingY X) := by simp only [F, q, add_zero]
  rw [hstart, hend, Real.norm_eq_abs, abs_sub_comm] at he
  have hpow : ((N : ℝ) * ℓ) ^ (1 - s + α + κ * ε) * ((N : ℝ) * ℓ) ^ ε =
      ((N : ℝ) * ℓ) ^ (1 - s + α + (κ + 1) * ε) := by
    rw [← Real.rpow_add hK0]
    congr 1
    ring
  calc
    _ ≤ C * C₀ * (N : ℝ) * ((N : ℝ) * ℓ) ^ (1 - s + α + κ * ε) * (0 - a) := he
    _ = C * C₀ * ((N : ℝ) * ℓ) ^ (1 - s + α + κ * ε) * loopPrecedingD X := by
      dsimp [a]
      field_simp
      ring
    _ ≤ C * C₀ * ((N : ℝ) * ℓ) ^ (1 - s + α + κ * ε) * ((N : ℝ) * ℓ) ^ ε := by
      gcongr
    _ = _ := by rw [mul_assoc, mul_assoc, hpow]; ring

end Riesz1

end
