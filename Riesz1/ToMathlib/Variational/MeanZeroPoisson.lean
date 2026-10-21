/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.InnerProductSpace.LaxMilgram
public import Mathlib.Topology.Algebra.Module.ClosedSubmodule

/-! # Poisson equations with a one-dimensional kernel

An internal Hilbert-space argument for a gradient form with a Poincaré
bound on the kernel of a continuous mean functional.
-/

public section

noncomputable section

namespace Riesz1.Internal

open InnerProductSpace

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]

/-- The gradient pairing as a continuous bilinear form. -/
def gradientBilinear (G : V →L[ℝ] W) : V →L[ℝ] V →L[ℝ] ℝ :=
  ((ContinuousLinearMap.compL ℝ V W ℝ).flip G).comp ((innerSL ℝ).comp G)

/-- A Poincaré estimate on the mean-zero subspace solves the full weak equation. -/
theorem exists_meanZero_poisson [CompleteSpace V]
    (M : V →L[ℝ] ℝ) (G : V →L[ℝ] W) (e : V)
    (he : M e = 1) (hGe : G e = 0)
    (C : ℝ) (hC : 0 < C)
    (hP : ∀ v, M v = 0 → ‖v‖ ^ 2 ≤ C * ‖G v‖ ^ 2)
    (ℓ : V →L[ℝ] ℝ) (hℓ : ℓ e = 0) :
    ∃ u : V, M u = 0 ∧ ∀ v, inner ℝ (G u) (G v) = ℓ v := by
  let K := M.ker
  have : CompleteSpace K := M.isClosed_ker.completeSpace_coe
  let D : K →L[ℝ] W := G.comp K.subtypeL
  let B := gradientBilinear D
  have hB : IsCoercive B := by
    refine ⟨C⁻¹, inv_pos.mpr hC, fun v => ?_⟩
    have hp := hP v.val v.property
    change C⁻¹ * ‖v‖ * ‖v‖ ≤ inner ℝ (D v) (D v)
    rw [real_inner_self_eq_norm_sq]
    have hv : ‖v‖ ^ 2 ≤ C * ‖D v‖ ^ 2 := hp
    nlinarith [mul_le_mul_of_nonneg_left hv (inv_pos.mpr hC).le,
      inv_mul_cancel₀ hC.ne']
  let f : StrongDual ℝ K := ℓ.comp K.subtypeL
  let u : K := hB.continuousLinearEquivOfBilin.symm ((toDual ℝ K).symm f)
  have hu (v : K) : inner ℝ (D u) (D v) = ℓ v.val := by
    have hh := hB.continuousLinearEquivOfBilin_apply u v
    have hu' : hB.continuousLinearEquivOfBilin u = (toDual ℝ K).symm f :=
      hB.continuousLinearEquivOfBilin.apply_symm_apply _
    rw [hu'] at hh
    exact hh.symm.trans (by change (toDual ℝ K) ((toDual ℝ K).symm f) v = _; simp [f])
  refine ⟨u.val, u.property, fun v => ?_⟩
  let v₀ : K := ⟨v - M v • e, by simp [K, he]⟩
  have hv := hu v₀
  simpa [D, v₀, hGe, hℓ] using hv

/-- Vanishing gradient means an element is its mean times the unit. -/
theorem eq_mean_smul_of_gradient_eq_zero
    (M : V →L[ℝ] ℝ) (G : V →L[ℝ] W) (e : V)
    (he : M e = 1) (hGe : G e = 0) (C : ℝ)
    (hP : ∀ v, M v = 0 → ‖v‖ ^ 2 ≤ C * ‖G v‖ ^ 2)
    {v : V} (hv : G v = 0) : v = M v • e := by
  have hp := hP (v - M v • e) (by simp [he])
  simp only [map_sub, map_smul, hGe, hv, smul_zero, sub_zero, norm_zero,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] at hp
  have hz : v - M v • e = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg (v - M v • e)])
  exact sub_eq_zero.mp hz

/-- All solutions of the weak equation differ from one solution by a scalar unit. -/
theorem poisson_solutions_iff
    (M : V →L[ℝ] ℝ) (G : V →L[ℝ] W) (e : V)
    (he : M e = 1) (hGe : G e = 0) (C : ℝ)
    (hP : ∀ v, M v = 0 → ‖v‖ ^ 2 ≤ C * ‖G v‖ ^ 2)
    (ℓ : V →L[ℝ] ℝ) {u : V}
    (hu : ∀ v, inner ℝ (G u) (G v) = ℓ v) (v : V) :
    (∀ w, inner ℝ (G v) (G w) = ℓ w) ↔ ∃ a : ℝ, v = u + a • e := by
  constructor
  · intro hv
    have hz : G (v - u) = 0 := by
      apply (inner_self_eq_zero (𝕜 := ℝ)).mp
      calc
        inner ℝ (G (v - u)) (G (v - u)) =
            inner ℝ (G v) (G (v - u)) - inner ℝ (G u) (G (v - u)) := by
              rw [map_sub, inner_sub_left]
        _ = 0 := by rw [hv, hu, sub_self]
    exact ⟨M (v - u), (sub_eq_iff_eq_add.mp
      (eq_mean_smul_of_gradient_eq_zero M G e he hGe C hP hz)).trans (add_comm _ _)⟩
  · rintro ⟨a, rfl⟩
    simpa [hGe] using hu

/-- Completing the square for a weak solution. -/
theorem poisson_energy_identity (G : V →L[ℝ] W) (ℓ : V →L[ℝ] ℝ) {u : V}
    (hu : ∀ v, inner ℝ (G u) (G v) = ℓ v) (v : V) :
    ‖G v‖ ^ 2 - 2 * ℓ v =
      (‖G u‖ ^ 2 - 2 * ℓ u) + ‖G (v - u)‖ ^ 2 := by
  have huv : inner ℝ (G v) (G u) = ℓ v := (real_inner_comm _ _).trans (hu v)
  rw [map_sub, norm_sub_sq_real, huv]
  nlinarith [hu u, real_inner_self_eq_norm_sq (G u)]

/-- The minimizers of the Dirichlet functional are precisely the weak solutions. -/
theorem poisson_minimizer_iff (G : V →L[ℝ] W) (ℓ : V →L[ℝ] ℝ) {u : V}
    (hu : ∀ v, inner ℝ (G u) (G v) = ℓ v) (v : V) :
    (∀ w, ‖G v‖ ^ 2 - 2 * ℓ v ≤ ‖G w‖ ^ 2 - 2 * ℓ w) ↔
      (∀ w, inner ℝ (G v) (G w) = ℓ w) := by
  constructor
  · intro hv
    have hz : G (v - u) = 0 := by
      have h := hv u
      rw [poisson_energy_identity G ℓ hu v] at h
      have hn : ‖G (v - u)‖ = 0 := by nlinarith [norm_nonneg (G (v - u))]
      exact norm_eq_zero.mp hn
    have heq : G v = G u := sub_eq_zero.mp (by simpa using hz)
    simpa only [heq] using hu
  · intro hv w
    rw [poisson_energy_identity G ℓ hv w]
    exact le_add_of_nonneg_right (sq_nonneg _)

end Riesz1.Internal

end
