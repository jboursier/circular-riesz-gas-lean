/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.WindowIntegralLipschitz
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Smooth convolution on an interior window

An integrable density on a fixed interval can be convolved with a kernel
smooth on the reached displacements. Bounds for every derivative give
smoothness and the exact differentiated integrals, including at the diagonal.
-/

public section

open MeasureTheory Set Filter
open scoped Topology ContDiff

namespace Riesz1

/-- Local smoothness and differentiation under a fixed-window integral.
No global regularity of the kernel or the density is required. -/
theorem smooth_windowIntegral {r σ θ : ℝ} {ζ H : ℝ → ℝ}
    (hwin : σ+r < θ) (hζ : IntegrableOn ζ (Ioc (-r) r))
    (hH : ContDiffOn ℝ ∞ H (Ioo (-θ) θ)) (C : ℕ → ℝ)
    (hb : ∀ m x, |x| < θ → ‖iteratedDeriv m H x‖ ≤ C m) :
    ContDiffOn ℝ ∞ (fun x => ∫ y in Ioc (-r) r, ζ y*H (x-y)) (Ioo (-σ) σ) ∧
    ∀ m x, x ∈ Ioo (-σ) σ →
      iteratedDeriv m (fun x => ∫ y in Ioc (-r) r, ζ y*H (x-y)) x =
        ∫ y in Ioc (-r) r, ζ y*iteratedDeriv m H (x-y) ∧
      ‖iteratedDeriv m (fun x => ∫ y in Ioc (-r) r, ζ y*H (x-y)) x‖ ≤
        C m*(∫ y in Ioc (-r) r, |ζ y|) := by
  let G := fun m x => ∫ y in Ioc (-r) r, ζ y*iteratedDeriv m H (x-y)
  have hdH (m : ℕ) : ContDiffOn ℝ ∞ (iteratedDeriv m H) (Ioo (-θ) θ) := by
    induction m with
    | zero => exact hH
    | succ m ih =>
      rw [iteratedDeriv_succ]
      exact ((contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioo).mp ih).2
  have hreach (x y : ℝ) (hx : x ∈ Ioo (-σ) σ) (hy : y ∈ Icc (-r) r) : |x-y| < θ :=
    (abs_sub x y).trans_lt (by linarith [abs_lt.mpr hx, abs_le.mpr hy])
  have hc (m : ℕ) (x : ℝ) (hx : x ∈ Ioo (-σ) σ) :
      ContinuousOn (fun y => iteratedDeriv m H (x-y)) (Icc (-r) r) := by
    intro y hy
    exact (((hdH m).contDiffAt (isOpen_Ioo.mem_nhds (abs_lt.mp (hreach x y hx hy)))).continuousAt.comp
      (continuous_const.sub continuous_id).continuousAt).continuousWithinAt
  have hi (m : ℕ) (x : ℝ) (hx : x ∈ Ioo (-σ) σ) :
      IntegrableOn (fun y => ζ y*iteratedDeriv m H (x-y)) (Ioc (-r) r) :=
    integrableOn_window_mul hζ (hc m x hx)
  have hder (m : ℕ) (x : ℝ) (hx : x ∈ Ioo (-σ) σ) : HasDerivAt (G m) (G (m+1) x) x := by
    apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume.restrict (Ioc (-r) r)) (s := Ioo (-σ) σ)
      (F := fun x y => ζ y*iteratedDeriv m H (x-y))
      (F' := fun x y => ζ y*iteratedDeriv (m+1) H (x-y))
      (bound := fun y => |ζ y| * C (m+1)) (isOpen_Ioo.mem_nhds hx)
      (Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hx) fun z hz => (hi m z hz).aestronglyMeasurable)
      (hi m x hx) (hi (m+1) x hx).aestronglyMeasurable ?_ (hζ.abs.mul_const _) ?_).2
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy z hz
      rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hb (m+1) _ (hreach z y hz (Ioc_subset_Icc_self hy))) (abs_nonneg _)
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy z hz
      have hd := ((hdH m).contDiffAt
        (isOpen_Ioo.mem_nhds (abs_lt.mp (hreach z y hz (Ioc_subset_Icc_self hy))))).differentiableAt (by simp)
      have hh : HasDerivAt (iteratedDeriv m H) (iteratedDeriv (m+1) H (z-y)) (z-y) := by
        simpa only [iteratedDeriv_succ] using hd.hasDerivAt
      exact (hh.comp_sub_const z y).const_mul (ζ y)
  have hsm : ∀ n : ℕ, ∀ m : ℕ, ContDiffOn ℝ n (G m) (Ioo (-σ) σ) := by
    intro n
    induction n with
    | zero => exact fun m => contDiffOn_zero.mpr fun x hx => (hder m x hx).continuousAt.continuousWithinAt
    | succ n ih =>
      intro m
      rw [show ((n+1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞)+1 by norm_cast,
        contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
      exact ⟨fun x hx => (hder m x hx).differentiableAt.differentiableWithinAt,
        fun h => absurd h WithTop.coe_ne_top, (ih (m+1)).congr (fun x hx => (hder m x hx).deriv)⟩
  have heq (m : ℕ) : ∀ x ∈ Ioo (-σ) σ, iteratedDeriv m (G 0) x = G m x := by
    induction m with
    | zero => exact fun _ _ => rfl
    | succ m ih =>
      intro x hx
      have hh : iteratedDeriv m (G 0) =ᶠ[𝓝 x] G m :=
        Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hx) fun y hy => ih y hy
      rw [iteratedDeriv_succ, hh.deriv_eq, (hder m x hx).deriv]
  refine ⟨contDiffOn_infty.mpr (fun n => hsm n 0), fun m x hx => ⟨heq m x hx, ?_⟩⟩
  change ‖iteratedDeriv m (G 0) x‖ ≤ _
  rw [heq m x hx]
  have hh := norm_integral_le_of_norm_le
    (f := fun y => ζ y * iteratedDeriv m H (x-y))
    (hζ.abs.const_mul (C m)) (by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    rw [norm_mul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left (hb m _ (hreach x y hx (Ioc_subset_Icc_self hy)))
      (abs_nonneg _)).trans_eq (mul_comm _ _))
  simpa only [G, integral_const_mul] using hh

end Riesz1
