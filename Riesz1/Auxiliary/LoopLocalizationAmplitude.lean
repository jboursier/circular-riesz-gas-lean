/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopLocalizationSupport
public import Riesz1.Auxiliary.LoopCutoffEnvelope
public import Riesz1.Auxiliary.GradientSplittingConvolutionCell

/-!
# Amplitude and derivative support of the localized transport

The amplitude step of the localization part of Lemma 5.8 uses the
integrable first derivative envelope and subtraction at the antipode.
-/

public section

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace Riesz1

/-- The opposite-point subtraction bounds the amplitude independently of the
period. Only the first derivative envelope is needed. -/
theorem loopLocalization_antipode_amplitude {s a K L C0 : ℝ}
    (hs : 0 < s) (hs1 : s < 1) (ha1 : a < 1) (hK : 1 ≤ K) (hL : 0 < L)
    (hC0 : 0 ≤ C0) {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hp : Function.Periodic ψ L)
    (hd : ∀ t, |deriv ψ t| ≤ C0 * gradWeightOne s a K L t)
    {u : ℝ} (hu : |u| ≤ L / 2) :
    |ψ u - ψ (L / 2)| ≤ C0 * ((1 + 1 / (1 - a)) + 1 / (1 - s)) := by
  rw [abs_sub_comm]
  exact (psi_sub_half_le hψ hK hL hp hd hu).trans
    (mul_le_mul_of_nonneg_left
      (integral_gradWeightOne_tail_le hs hs1 ha1 hK hL (abs_nonneg u) hu) hC0)

/-- The partial-window amplitude estimate `|b₀| ≤ C C₀ K`. The explicit
constant depends only on the two fixed exponents. -/
theorem loopLocalTransport_amplitude {s α : ℝ} (hs : 0 < s) (hs1 : s < 1)
    (hα2 : α < s / 2) {N : ℕ+} {ℓ γ C0 : ℝ}
    (hℓ : 0 < ℓ) (hK : 1 ≤ (N : ℝ) * ℓ) (hP : GradPartial N ℓ γ)
    (hC0 : 0 ≤ C0) {χ ψ : ℝ → ℝ} (hχ01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1)
    (hψ : ContDiff ℝ ∞ ψ) (hp : Function.Periodic ψ ℓ⁻¹)
    (hd : ∀ t, |deriv ψ t| ≤
      C0 * gradWeightOne s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ t) (z : ℝ) :
    |loopLocalTransport χ N ℓ γ ψ z| ≤
      (((1 + 1 / (1 - (1 - s + α))) + 1 / (1 - s))) * C0 * ((N : ℝ) * ℓ) := by
  let K := (N : ℝ) * ℓ
  let q := loopCircleRep ℓ (z / K)
  have hK0 : 0 < K := by dsimp [K]; linarith
  have hq : |q| ≤ ℓ⁻¹ / 2 := by
    have h := loopCircleRep_mem_Ico hℓ (z / K)
    have he : 1 / (2 * ℓ) = ℓ⁻¹ / 2 := by field_simp
    rw [he] at h
    exact abs_le.mpr ⟨h.1, h.2.le⟩
  have hb := loopLocalization_antipode_amplitude hs hs1
    (by linarith : 1 - s + α < 1) hK (inv_pos.mpr hℓ) hC0 hψ hp hd hq
  have hhalf : ℓ⁻¹ / 2 = 1 / (2 * ℓ) := by field_simp
  rw [hhalf] at hb
  have hχa : |χ (ℓ * q / gradT N ℓ γ)| ≤ 1 := by
    rw [abs_of_nonneg (hχ01 _).1]
    exact (hχ01 _).2
  change |K * (if GradPartial N ℓ γ then
    χ (ℓ * q / gradT N ℓ γ) * (ψ q - ψ (1 / (2 * ℓ))) else ψ (z / K))| ≤ _
  rw [ite_eq_left hP, abs_mul, abs_of_pos hK0, abs_mul]
  calc
    _ ≤ K * (1 * (C0 * ((1 + 1 / (1 - (1 - s + α))) + 1 / (1 - s)))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul hχa hb (abs_nonneg _) zero_le_one) hK0.le
    _ = _ := by dsimp [K]; ring

/-- Outside the central support ball the derivative vanishes too. The strict
inequality suffices for all cells disjoint from that ball. -/
theorem loopLocalTransport_deriv_zero_of_circDist {N : ℕ+} {ℓ γ : ℝ}
    (hℓ : 0 < ℓ) (hP : GradPartial N ℓ γ) {χ : ℝ → ℝ}
    (hχs : tsupport χ ⊆ Ioo (-(1 / 4)) (1 / 4)) (ψ : ℝ → ℝ)
    {z : ℝ} (hz : gradM N ℓ γ / 4 < circDist (N : ℝ) z) :
    deriv (loopLocalTransport χ N ℓ γ ψ) z = 0 := by
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hc : Continuous (circDist (N : ℝ)) := by
    apply LipschitzWith.continuous (K := 1)
    rw [lipschitzWith_iff_dist_le_mul]
    intro x y
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using
      ((abs_circDist_sub_circDist_le (a := x) (b := y) hN).trans
        (circDist_le_abs_self hN _))
  have he : loopLocalTransport χ N ℓ γ ψ =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
    filter_upwards [(isOpen_lt continuous_const hc).mem_nhds hz] with u hu
    exact loopLocalTransport_zero_of_circDist hℓ hP hχs ψ hu.le
  rw [he.deriv_eq, deriv_const]

end Riesz1

end
