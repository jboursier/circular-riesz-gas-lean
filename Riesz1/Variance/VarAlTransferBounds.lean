/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopCutoffExplicitBound
public import Riesz1.Auxiliary.LoopCutoffSmooth
public import Riesz1.Auxiliary.GradientSplittingIdentityMain

/-!
# Polynomial local loop bounds

The deterministic assertions of Proposition 5.9. The uncut
loop is bounded on the entire larger-window good event, before multiplication
by the cutoff. All objects are the actual auxiliary objects.
-/

@[expose] public section

noncomputable section

open Set
open scoped ContDiff

namespace Riesz1

/-- At two particles every admissible window is full. -/
theorem varAl_not_partial_two {ℓ γ : ℝ} (hK : 1 ≤ (2 : ℝ) * ℓ) (hγ : 0 ≤ γ) :
    ¬GradPartial (2 : ℕ+) ℓ γ := by
  have h := Real.one_le_rpow hK hγ
  change ¬((2 : ℝ) * ℓ) ^ γ < (2 : ℝ) / 8
  linarith

/-- The loop itself has a polynomial bound on the larger-window good
event. The coefficient is chosen before the envelope constant and the scale. -/
theorem varAl_loop_good_bound {s α γ ε : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hα : s - 1 ≤ α) (hα2 : α < s / 2) (hγ : 1 < γ)
    (hε : 0 < ε) (hεs : ε ≤ 1 - s / 2) {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hχs : tsupport χ ⊆ Ioo (-(1 / 4)) (1 / 4))
    (hχ1 : ∀ x : ℝ, |x| ≤ 1 / 8 → χ x = 1)
    (hχ01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (C₀ : ℝ) (N : ℕ+) (ℓ : ℝ) (ψ : ℝ → ℝ),
      0 ≤ C₀ → 0 < ℓ → 1 ≤ (N : ℝ) * ℓ →
      ContDiff ℝ ∞ ψ → Function.Periodic ψ ℓ⁻¹ →
      (∀ t, |deriv ψ t| ≤ C₀ * gradWeightOne s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ t) →
      (∀ t, |deriv (deriv ψ) t| ≤
        C₀ * gradWeightTwo s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ t) →
      ∀ X : Fin (N : ℕ) → ℝ, gradEvent s (2 * γ) ε N ℓ X → X ⟨0, N.pos⟩ = 0 →
        |gradLoop s (loopTransport χ N ℓ γ ψ) N ℓ γ X| ≤
          C * C₀ * ((N : ℝ) * ℓ) ^ ((1 - s + α) + 2 * γ + ε * (s + 1)) := by
  obtain ⟨Ce, hCe, he⟩ := loopTransport_envelope hs0 hs1 hα hα2 hχ hχc hχs hχ1 hχ01
  obtain ⟨Cb, hCb, hb1, hb2⟩ := gradKernelH_bound hs0 hs1
  let A := Cb * (64 * 2 ^ (s + 1) + 256 / (1 - s))
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨A * Ce, mul_nonneg hA hCe, ?_⟩
  intro C₀ N ℓ ψ hC₀ hℓ hK hψ hp h1 h2 X hX hX0
  have hK0 : 0 < (N : ℝ) * ℓ := by linarith
  have hZ : ∀ x y : ℝ, |gradZ (loopTransport χ N ℓ γ ψ) ℓ x y| ≤
      Ce * C₀ * ((N : ℝ) * ℓ) ^ (1 - s + α) := by
    intro x y
    apply gradZ_abs_le_const
    intro t
    exact ((he N ℓ γ ψ C₀ hℓ hK hγ hC₀ hψ hp h1 h2 t).1).trans
      (mul_le_mul_of_nonneg_left (gradWeightOne_le_rpow hs1 hK (by linarith))
        (mul_nonneg hCe hC₀))
  have hb := loopGradLoop_bound hs0 hs1 hCb.le
    (mul_nonneg (mul_nonneg hCe hC₀) (Real.rpow_nonneg hK0.le _))
    hb1 hb2 hZ hγ.le hε hεs hℓ hK hX hX0
  have hm : gradM N ℓ γ ^ 2 = ((N : ℝ) * ℓ) ^ (2 * γ) := by
    unfold gradM
    rw [← Real.rpow_natCast, ← Real.rpow_mul hK0.le]
    congr 1
    push_cast
    ring
  have heps : (((N : ℝ) * ℓ) ^ ε) ^ (s + 1) =
      ((N : ℝ) * ℓ) ^ (ε * (s + 1)) := (Real.rpow_mul hK0.le _ _).symm
  have hpow : ((N : ℝ) * ℓ) ^ (1 - s + α) * ((N : ℝ) * ℓ) ^ (2 * γ) *
      ((N : ℝ) * ℓ) ^ (ε * (s + 1)) =
      ((N : ℝ) * ℓ) ^ ((1 - s + α) + 2 * γ + ε * (s + 1)) := by
    rw [← Real.rpow_add hK0, ← Real.rpow_add hK0]
  calc |gradLoop s (loopTransport χ N ℓ γ ψ) N ℓ γ X|
      ≤ A * (Ce * C₀ * ((N : ℝ) * ℓ) ^ (1 - s + α)) * gradM N ℓ γ ^ 2 *
          (((N : ℝ) * ℓ) ^ ε) ^ (s + 1) := hb
    _ = A * Ce * C₀ * ((N : ℝ) * ℓ) ^
        ((1 - s + α) + 2 * γ + ε * (s + 1)) := by
      rw [hm, heps, ← hpow]
      ring

/-- A nonzero differential of the cutoff implies strict positivity of
the cutoff: its zero set consists of global minima. -/
theorem varAl_loopCutoff_pos_of_fderiv_ne_zero {s γ ε ℓ : ℝ} {N : ℕ+}
    {X : Fin (N : ℕ) → ℝ} (hX : fderiv ℝ (loopCutoff s γ ε N ℓ) X ≠ 0) :
    0 < loopCutoff s γ ε N ℓ X := by
  have hn := (loopCutoff_mem_Icc s γ ε ℓ X).1
  apply lt_of_le_of_ne hn
  intro heq
  apply hX
  apply IsLocalMin.fderiv_eq_zero
  exact Filter.Eventually.of_forall fun Y => by
    rw [← heq]
    exact (loopCutoff_mem_Icc s γ ε ℓ Y).1

/-- The larger-window good event is closed on the ambient lift space. -/
theorem varAl_isClosed_gradEvent (s γ ε ℓ : ℝ) (N : ℕ+) :
    IsClosed {X : Fin (N : ℕ) → ℝ | gradEvent s γ ε N ℓ X} := by
  have hc (j : ℤ) : Continuous (fun X : Fin (N : ℕ) → ℝ => gradLift N X j) := by
    unfold gradLift
    fun_prop
  simp only [gradEvent, ofPred_and, ofPred_forall]
  apply IsClosed.inter
  · exact isClosed_iInter fun i => isClosed_iInter fun _hi => isClosed_iInter fun k =>
      isClosed_iInter fun _hk => isClosed_iInter fun _hk0 => isClosed_iInter fun _hkN =>
        isClosed_le (by fun_prop) continuous_const
  · exact isClosed_iInter fun i => isClosed_iInter fun _hi => isClosed_iInter fun _hk =>
      (isClosed_le continuous_const (by fun_prop)).inter
        (isClosed_le (by fun_prop) continuous_const)

/-- The support of the cutoff differential, relative to the physical
ordered chart, lies in the larger-window good event. -/
theorem varAl_gradEvent_of_mem_gradient_support {s γ ε ℓ : ℝ} {N : ℕ+}
    (hℓ : 0 < ℓ) {X : Fin (N : ℕ) → ℝ}
    (hX : X ∈ closure {Y : Fin (N : ℕ) → ℝ |
      Y ∈ orderedDomain N ∧ fderiv ℝ (loopCutoff s γ ε N ℓ) Y ≠ 0}) :
    gradEvent s (2 * γ) ε N ℓ X := by
  apply closure_minimal (t := {Y | gradEvent s (2 * γ) ε N ℓ Y}) ?_
    (varAl_isClosed_gradEvent s (2 * γ) ε ℓ N) hX
  intro Y hY
  exact gradEvent_of_loopCutoff_pos hℓ (⟨Y, hY.1⟩ : Configuration N)
    (varAl_loopCutoff_pos_of_fderiv_ne_zero hY.2)

end Riesz1

end
