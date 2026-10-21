/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.Sobolev
public import Riesz1.ToMathlib.WeightedSobolev.L2Facts

/-!
# The scalar Poincaré constant and extension to the completion

The scalar Poincaré constant and the last approximation step in extending the inequality.
The extension criterion is an internal helper. It does not assert the
smooth-core Poincaré inequality for the Gibbs law.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Topology

namespace Riesz1

/-- The scalar Poincaré constant. -/
def hsPoincareConstant (N : ℕ+) (c : ℝ) : ℝ :=
  max ((N : ℝ) / (4 * Real.pi ^ 2)) (2 * c * (N : ℝ))⁻¹

theorem hsPoincareConstant_pos (N : ℕ+) (c : ℝ) : 0 < hsPoincareConstant N c :=
  (div_pos (Nat.cast_pos.mpr N.pos) (by positivity)).trans_le (le_max_left _ _)

theorem hsPoincareConstant_two (c : ℝ) :
    hsPoincareConstant 2 c = max (1 / (2 * Real.pi ^ 2)) (4 * c)⁻¹ := by
  unfold hsPoincareConstant
  change max ((2 : ℝ) / (4 * Real.pi ^ 2)) (2 * c * 2)⁻¹ = _
  congr 1 <;> ring

namespace Internal

variable {N : ℕ+} (μ : Measure (HsConfiguration N)) [IsProbabilityMeasure μ]

/-- The integral mean is a continuous functional on scalar `L²` of a probability. -/
theorem hsPoincare_mean_eq_inner (f : Lp ℝ 2 μ) :
    (∫ x, f x ∂μ) = inner ℝ (Lp.const 2 μ (1 : ℝ)) f := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_const 2 μ (1 : ℝ)] with x hx
  simp

/-- The centered second moment of a scalar `L²` function, in Hilbert coordinates. -/
theorem hsPoincare_variance_eq (f : Lp ℝ 2 μ) :
    (∫ x, (f x - ∫ y, f y ∂μ) ^ 2 ∂μ) =
      ‖f‖ ^ 2 - (inner ℝ (Lp.const 2 μ (1 : ℝ)) f) ^ 2 := by
  rw [WeightedSobolev.integral_sub_mean_sq (Lp.memLp f), hsPoincare_mean_eq_inner]
  congr 1
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by simp

/-- Extension of a Poincaré inequality on the periodic smooth core to the
actual Hilbert completion. The premise is internal and remains a separate
obligation when this helper is used for a Gibbs measure. -/
theorem hsPoincare_of_smooth {C : ℝ}
    (h : ∀ φ : hsSmoothCore N,
      (∫ x, (hsSmoothValue φ.val x - ∫ y, hsSmoothValue φ.val y ∂μ) ^ 2 ∂μ) ≤
        C * ∫ x, ‖hsSmoothGradient φ x‖ ^ 2 ∂μ)
    (f : HsSobolev μ) :
    (∫ x, (hsSobolevValue μ f x - ∫ y, hsSobolevValue μ f y ∂μ) ^ 2 ∂μ) ≤
      C * ∫ x, ‖hsSobolevGradient μ f x‖ ^ 2 ∂μ := by
  have hgrad (g : HsSobolev μ) :
      (∫ x, ‖hsSobolevGradient μ g x‖ ^ 2 ∂μ) = ‖hsSobolevGradient μ g‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    simp only [real_inner_self_eq_norm_sq]
  rw [hsPoincare_variance_eq, hgrad]
  have hclosed : IsClosed {g : HsSobolev μ |
      ‖hsSobolevValue μ g‖ ^ 2 -
        (inner ℝ (Lp.const 2 μ (1 : ℝ)) (hsSobolevValue μ g)) ^ 2 ≤
          C * ‖hsSobolevGradient μ g‖ ^ 2} :=
    isClosed_le (((hsSobolevValue μ).continuous.norm.pow 2).sub
      ((continuous_const.inner (hsSobolevValue μ).continuous).pow 2))
      (continuous_const.mul ((hsSobolevGradient μ).continuous.norm.pow 2))
  apply hclosed.closure_subset_iff.mpr ?_ ((denseRange_hsSobolevOfSmooth μ) f)
  rintro _ ⟨φ, rfl⟩
  change ‖hsSobolevValue μ (hsSobolevOfSmooth μ φ)‖ ^ 2 -
      (inner ℝ (Lp.const 2 μ (1 : ℝ)) (hsSobolevValue μ (hsSobolevOfSmooth μ φ))) ^ 2 ≤
        C * ‖hsSobolevGradient μ (hsSobolevOfSmooth μ φ)‖ ^ 2
  rw [← hsPoincare_variance_eq, ← hgrad]
  have hv : hsSobolevValue μ (hsSobolevOfSmooth μ φ) =ᵐ[μ] hsSmoothValue φ.val :=
    (φ.property.memLp_value μ).coeFn_toLp
  have hg : hsSobolevGradient μ (hsSobolevOfSmooth μ φ) =ᵐ[μ] hsSmoothGradient φ :=
    (φ.property.memLp_gradient μ).coeFn_toLp
  have hm := integral_congr_ae hv
  have hvar : (∫ x, (hsSobolevValue μ (hsSobolevOfSmooth μ φ) x -
      ∫ y, hsSobolevValue μ (hsSobolevOfSmooth μ φ) y ∂μ) ^ 2 ∂μ) =
      ∫ x, (hsSmoothValue φ.val x - ∫ y, hsSmoothValue φ.val y ∂μ) ^ 2 ∂μ := by
    apply integral_congr_ae
    filter_upwards [hv] with x hx
    rw [hx, hm]
  have henergy : (∫ x, ‖hsSobolevGradient μ (hsSobolevOfSmooth μ φ) x‖ ^ 2 ∂μ) =
      ∫ x, ‖hsSmoothGradient φ x‖ ^ 2 ∂μ :=
    integral_congr_ae (hg.mono fun _ hx => congrArg (fun v => ‖v‖ ^ 2) hx)
  simpa only [hvar, henergy] using h φ

end Internal

end Riesz1

end
