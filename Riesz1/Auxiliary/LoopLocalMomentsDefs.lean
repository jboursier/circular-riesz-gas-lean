/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopExteriorDefs
public import Riesz1.Auxiliary.LoopCutoffSmooth
public import Riesz1.Variance.LoopScale

/-!
# The localized microscopic loop and its deterministic background

The window and localized profile reuse `gradLabels` and
`loopTransport`. The pair kernel is `loopArcKernel`. Real lifts retain
the displacement from the preceding particle to zero. This is essential in a partial
window. Full windows integrate over one entire microscopic period.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace Riesz1

/-- The microscopic localized transport `b₀(z) = K ψ_γ(z/K)`. -/
def loopLocalTransport (χ : ℝ → ℝ) (N : ℕ+) (ℓ γ : ℝ) (ψ : ℝ → ℝ) (z : ℝ) : ℝ :=
  loopScaleField ((N : ℝ) * ℓ) (loopTransport χ N ℓ γ ψ) z

/-- The lower endpoint of the microscopic background: `-M` in a partial window,
and zero in a full window. -/
def loopLocalLo (N : ℕ+) (ℓ γ : ℝ) : ℝ :=
  if GradPartial N ℓ γ then -gradM N ℓ γ else 0

/-- The upper endpoint of the microscopic background: `M` in a partial window,
and `N` in a full window. -/
def loopLocalHi (N : ℕ+) (ℓ γ : ℝ) : ℝ :=
  if GradPartial N ℓ γ then gradM N ℓ γ else N

/-- The localized loop `L_{I_J}(b)`, for any microscopic test `b`.
The ordered pair sum omits the atomic diagonal. -/
def loopLocalLoop (s : ℝ) (N : ℕ+) (ℓ γ : ℝ) (b : ℝ → ℝ)
    (X : LoopPrecedingConfiguration N) : ℝ :=
  (∑ i ∈ gradLabels N ℓ γ, ∑ j ∈ (gradLabels N ℓ γ).erase i,
    loopArcKernel s N b (loopPrecedingLift X i) (loopPrecedingLift X j)) -
  2 * ∑ i ∈ gradLabels N ℓ γ, ∫ u in loopLocalLo N ℓ γ..loopLocalHi N ℓ γ,
    loopArcKernel s N b (loopPrecedingLift X i) u

/-- The deterministic background term `C_bg`. -/
def loopLocalBackground (s : ℝ) (N : ℕ+) (ℓ γ : ℝ) (b : ℝ → ℝ) : ℝ :=
  ∫ z in loopLocalLo N ℓ γ..loopLocalHi N ℓ γ,
    ∫ u in loopLocalLo N ℓ γ..loopLocalHi N ℓ γ, loopArcKernel s N b z u

theorem contDiff_loopLocalTransport {χ ψ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hψ : ContDiff ℝ ∞ ψ) (hχs : tsupport χ ⊆ Ioo (-(1 / 4)) (1 / 4))
    (N : ℕ+) {ℓ : ℝ} (hℓ : 0 < ℓ) (γ : ℝ) :
    ContDiff ℝ ∞ (loopLocalTransport χ N ℓ γ ψ) :=
  contDiff_const.mul ((contDiff_loopTransport hχ hψ hχs N hℓ γ).comp
    (contDiff_id.div_const _))

theorem loopLocalTransport_periodic {N : ℕ+} {ℓ γ : ℝ} (hℓ : 0 < ℓ) (χ : ℝ → ℝ)
    {ψ : ℝ → ℝ} (hp : Function.Periodic ψ ℓ⁻¹) :
    Function.Periodic (loopLocalTransport χ N ℓ γ ψ) (N : ℝ) := by
  intro z
  have he : (z + N) / ((N : ℝ) * ℓ) = z / ((N : ℝ) * ℓ) + ℓ⁻¹ := by
    field_simp
  simp only [loopLocalTransport, loopScaleField, he]
  rw [(loopTransport_periodic hℓ χ hp) _]

/-- The microscopic rescaling cancels in the first derivative. -/
theorem deriv_loopLocalTransport {χ ψ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hψ : ContDiff ℝ ∞ ψ) (hχs : tsupport χ ⊆ Ioo (-(1 / 4)) (1 / 4))
    (N : ℕ+) {ℓ : ℝ} (hℓ : 0 < ℓ) (γ z : ℝ) :
    deriv (loopLocalTransport χ N ℓ γ ψ) z =
      deriv (loopTransport χ N ℓ γ ψ) (z / ((N : ℝ) * ℓ)) := by
  have hK : ((N : ℝ) * ℓ) ≠ 0 := mul_ne_zero (by exact_mod_cast N.ne_zero) hℓ.ne'
  have ht : HasDerivAt (loopTransport χ N ℓ γ ψ)
      (deriv (loopTransport χ N ℓ γ ψ) (z / ((N : ℝ) * ℓ))) (z / ((N : ℝ) * ℓ)) :=
    ((contDiff_loopTransport hχ hψ hχs N hℓ γ).differentiable
      (by simp)).differentiableAt.hasDerivAt
  have hl : HasDerivAt (fun z : ℝ => z / ((N : ℝ) * ℓ)) (((N : ℝ) * ℓ)⁻¹) z := by
    simpa [div_eq_mul_inv] using (hasDerivAt_id z).mul_const (((N : ℝ) * ℓ)⁻¹)
  have hf := (ht.comp z hl).const_mul ((N : ℝ) * ℓ)
  unfold loopLocalTransport loopScaleField
  simpa only [Function.comp_def, mul_left_comm ((N : ℝ) * ℓ), mul_inv_cancel₀ hK,
    mul_one] using hf.deriv

theorem loopLocalLo_le_hi (N : ℕ+) {ℓ γ : ℝ} (hℓ : 0 ≤ ℓ) :
    loopLocalLo N ℓ γ ≤ loopLocalHi N ℓ γ := by
  have hM : 0 ≤ gradM N ℓ γ := Real.rpow_nonneg (mul_nonneg (by positivity) hℓ) _
  unfold loopLocalLo loopLocalHi
  split_ifs <;> linarith [show (0 : ℝ) < N by exact_mod_cast N.pos]

end Riesz1

end
