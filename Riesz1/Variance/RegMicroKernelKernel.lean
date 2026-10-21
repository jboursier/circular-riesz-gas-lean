/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Kernel.FundamentalSeries
public import Riesz1.Kernel.TransportScaledLattice
public import Riesz1.Frozen.Parameters
public import Riesz1.Frozen.ParametersExponent

/-!
# The inverse-transport kernel and its derivative bounds

This file starts the proof of Lemma 5.3. For `L > 0` the kernel
`P_L(t) = -2β L^{-s} g_s(t/L)` is built from the Riesz kernel `g_s`
(`Riesz1.rieszRepresentative`). It is `L`-periodic, and its `m`-th derivative satisfies
`|P_L^{(m)}(t)| ≤ C dist(t, Lℤ)^{-s-m}` with `C` independent of `L` and `t`
(`Riesz1.inverseKernel_iteratedDeriv_bound`). These are the kernel estimates that the proof of
Lemma 5.3 uses for `m = 0, 1, 2`.
-/

public section

open MeasureTheory Set Filter Topology
open scoped ContDiff Real

namespace Riesz1

/-- The inverse-transport kernel `P_L(t) = -2β L^{-s} g_s(t/L)` on the line, where `β` and `s`
are the entries of the parameters and `g_s` is the Riesz kernel
(Lemma 5.3). -/
@[expose] noncomputable def inverseKernel (P : Parameters) (L t : ℝ) : ℝ :=
  -(2 * P.val.1 * L ^ (-P.val.2)) *
    rieszRepresentative (parametersExponent P) ((t / L : ℝ) : UnitAddCircle)

/-- The kernel `g_s` is continuous off the integers, so its composition with `t ↦ t/L` is smooth
off the lattice `Lℤ`. The set `{x | (x : UnitAddCircle) ≠ 0}` is open. -/
lemma isOpen_unitAddCircle_ne_zero : IsOpen {x : ℝ | (x : UnitAddCircle) ≠ 0} :=
  isOpen_compl_singleton.preimage (AddCircle.continuous_mk' _)

/-- `P_L` is `L`-periodic. -/
lemma inverseKernel_periodic (P : Parameters) {L : ℝ} (hL : 0 < L) :
    Function.Periodic (inverseKernel P L) L := by
  intro t
  have hper : Function.Periodic (fun x : ℝ => rieszRepresentative (parametersExponent P) x) 1 :=
    (fundamental_series (parametersExponent P)).2.2.2.1
  have hdiv : (t + L) / L = t / L + 1 := by
    rw [add_div, div_self hL.ne']
  unfold inverseKernel
  rw [hdiv]
  exact congrArg (fun y => -(2 * P.val.1 * L ^ (-P.val.2)) * y) (hper (t / L))

/-- A point `t` off the lattice `Lℤ` gives a point `t/L` off the integers. -/
lemma unitAddCircle_ne_zero_of_not_lattice {L t : ℝ} (hL : 0 < L)
    (ht : ∀ k : ℤ, t ≠ k * L) : ((t / L : ℝ) : UnitAddCircle) ≠ 0 := by
  intro h
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).1 h
  rw [zsmul_eq_mul, mul_one] at hn
  apply ht n
  rw [hn, div_mul_cancel₀ t hL.ne']

/-- Off the lattice `Lℤ`, the `m`-th derivative of `P_L` is the scaled derivative of `g_s`:
`P_L^{(m)}(t) = -2β L^{-s} L^{-m} g_s^{(m)}(t/L)`. -/
lemma iteratedDeriv_inverseKernel (P : Parameters) {L : ℝ} (hL : 0 < L) (m : ℕ) (t : ℝ)
    (ht : ∀ k : ℤ, t ≠ k * L) :
    iteratedDeriv m (inverseKernel P L) t =
      -(2 * P.val.1 * L ^ (-P.val.2)) * (1 / L) ^ m *
        iteratedDeriv m (fun x : ℝ => rieszRepresentative (parametersExponent P) x) (t / L) := by
  have hsmooth : ContDiffOn ℝ ∞ (fun x : ℝ => rieszRepresentative (parametersExponent P) x)
      {x : ℝ | (x : UnitAddCircle) ≠ 0} :=
    (fundamental_series (parametersExponent P)).2.1
  have hmem : (1 / L) * t ∈ {x : ℝ | (x : UnitAddCircle) ≠ 0} := by
    rw [show (1 / L) * t = t / L by ring]
    exact unitAddCircle_ne_zero_of_not_lattice hL ht
  have key := iteratedDeriv_comp_mul_of_contDiffOn isOpen_unitAddCircle_ne_zero (1 / L) m
    (fun x : ℝ => rieszRepresentative (parametersExponent P) x) hsmooth t hmem
  have hfun : (fun x : ℝ => rieszRepresentative (parametersExponent P) ((x / L : ℝ) : UnitAddCircle))
      = fun x : ℝ => rieszRepresentative (parametersExponent P) ((1 / L * x : ℝ) : UnitAddCircle) := by
    funext x
    congr 2
    ring
  have e1 : iteratedDeriv m (inverseKernel P L) t =
      -(2 * P.val.1 * L ^ (-P.val.2)) * iteratedDeriv m
        (fun x : ℝ => rieszRepresentative (parametersExponent P) ((x / L : ℝ) : UnitAddCircle)) t :=
    iteratedDeriv_const_mul_field _ _
  rw [e1, hfun]
  rw [show (1 / L) * t = t / L by ring] at key
  rw [key]
  ring

/-- The distance from `t/L` to the integers, measured on the unit circle, is `latticeDist L t / L`.
-/
lemma dist_unitAddCircle_div_zero {L t : ℝ} (hL : 0 < L) :
    dist ((t / L : ℝ) : UnitAddCircle) 0 = latticeDist L t / L := by
  rw [dist_zero_right, UnitAddCircle.norm_eq]
  unfold latticeDist
  rw [show t - L * round (t / L) = L * (t / L - round (t / L)) by field_simp, abs_mul,
    abs_of_pos hL]
  field_simp

/-- Derivative bounds for `P_L`: for each order `m` there is a constant `C`, independent of the
length `L` and of the point `t`, with `|P_L^{(m)}(t)| ≤ C dist(t, Lℤ)^{-s-m}` off the lattice
`Lℤ`. Here `dist(t, Lℤ)` is `latticeDist L t`. For `m = 0, 1, 2` these are the kernel estimates
used in Lemma 5.3. -/
theorem inverseKernel_iteratedDeriv_bound (P : Parameters) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ L t : ℝ, 0 < L → (∀ k : ℤ, t ≠ k * L) →
      |iteratedDeriv m (inverseKernel P L) t| ≤
        C * latticeDist L t ^ (-P.val.2 - (m : ℝ)) := by
  obtain ⟨Cg, hCg, hbd⟩ :=
    (fundamental_series (parametersExponent P)).2.2.2.2.2.2.2.2.2.2.1 m
  have hβ : 0 < P.val.1 := P.property.1
  refine ⟨2 * P.val.1 * Cg, by positivity, ?_⟩
  intro L t hL ht
  have hx := unitAddCircle_ne_zero_of_not_lattice hL ht
  have hb : |iteratedDeriv m (fun x : ℝ => rieszRepresentative (parametersExponent P) x) (t / L)| ≤
      Cg * (latticeDist L t / L) ^ (-P.val.2 - (m : ℝ)) := by
    have h := hbd (t / L) hx
    rw [dist_unitAddCircle_div_zero hL] at h
    exact h
  have hld : 0 ≤ latticeDist L t := by
    unfold latticeDist
    exact abs_nonneg _
  have hLs : 0 < L ^ (-P.val.2) := Real.rpow_pos_of_pos hL _
  have hLm : 0 < (1 / L) ^ m := by positivity
  have hz : L ^ (-P.val.2 - (m : ℝ)) = L ^ (-P.val.2) * (1 / L) ^ m := by
    rw [sub_eq_add_neg, Real.rpow_add hL, Real.rpow_neg hL.le, Real.rpow_neg hL.le,
      Real.rpow_natCast, one_div, inv_pow]
  rw [iteratedDeriv_inverseKernel P hL m t ht, abs_mul, abs_mul, abs_neg,
    abs_of_pos (by positivity : 0 < 2 * P.val.1 * L ^ (-P.val.2)), abs_of_pos hLm]
  have hdiv : (latticeDist L t / L) ^ (-P.val.2 - (m : ℝ)) =
      latticeDist L t ^ (-P.val.2 - (m : ℝ)) / L ^ (-P.val.2 - (m : ℝ)) :=
    Real.div_rpow hld hL.le _
  calc 2 * P.val.1 * L ^ (-P.val.2) * (1 / L) ^ m *
        |iteratedDeriv m (fun x : ℝ => rieszRepresentative (parametersExponent P) x) (t / L)|
      ≤ 2 * P.val.1 * L ^ (-P.val.2) * (1 / L) ^ m *
          (Cg * (latticeDist L t / L) ^ (-P.val.2 - (m : ℝ))) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = 2 * P.val.1 * Cg * latticeDist L t ^ (-P.val.2 - (m : ℝ)) := by
        rw [hdiv, hz]
        field_simp

end Riesz1

end
