/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.LoopIBPHS
public import Riesz1.Variance.LoopIBPGibbs
public import Riesz1.Variance.LoopIBPUniform
import all Riesz1.Variance.LoopForceEnergy
import all Riesz1.Variance.LoopForce
import all Riesz1.Variance.LoopScale
public import Riesz1.Variance.LoopIBPCutoff

/-!
# Error terms of the collision cutoffs for the diagonal field

For the field potential `Φ = Φ_{ψ,a}`, the Langevin expression of the
cutoff test `χ_h Φ` splits as `χ_h 𝓛Φ` plus an error supported on the collision strip. This file
proves the splitting in the lifted coordinates and the strip bound of the error.

* `loopHS` is `Φ_{ψ,a}` on the Euclidean lift, `rieszH` the Riesz Hamiltonian on the lift.
* `loopLHS` is the pointwise expression of `𝓛Φ` in partial derivatives, identified with
  `loopOperatorPotential` on configurations.
* `loopError` is the error term. `exists_loopError_bound` bounds it by the strip indicator.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace Riesz1

variable {N : ℕ+}

/-- The primitive of a smooth function is smooth. -/
theorem contDiff_primitive {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) :
    ContDiff ℝ ∞ (fun u : ℝ => ∫ t in (0 : ℝ)..u, ψ t) := by
  rw [contDiff_infty_iff_deriv]
  have hd : deriv (fun u : ℝ => ∫ t in (0 : ℝ)..u, ψ t) = ψ := by
    funext u
    exact (hψ.continuous.integral_hasStrictDerivAt 0 u).hasDerivAt.deriv
  refine ⟨fun u => (hψ.continuous.integral_hasStrictDerivAt 0 u).hasDerivAt.differentiableAt, ?_⟩
  rw [hd]
  exact hψ

/-- A primitive of a continuous `T`-periodic function with zero mean over a period is
`T`-periodic. -/
theorem periodic_primitive {ψ : ℝ → ℝ} {T : ℝ} (hc : Continuous ψ)
    (hψ : Function.Periodic ψ T) (hmean : ∫ t in (0 : ℝ)..T, ψ t = 0) :
    Function.Periodic (fun u : ℝ => ∫ t in (0 : ℝ)..u, ψ t) T := by
  intro u
  have hsplit : ∫ t in (0 : ℝ)..(u + T), ψ t =
      (∫ t in (0 : ℝ)..u, ψ t) + ∫ t in u..(u + T), ψ t :=
    (intervalIntegral.integral_add_adjacent_intervals (μ := volume) (hc.intervalIntegrable 0 u)
      (hc.intervalIntegrable u (u + T))).symm
  have hshift : ∫ t in u..(u + T), ψ t = ∫ t in (0 : ℝ)..T, ψ t := by
    have := hψ.intervalIntegral_add_eq u 0
    simpa using this
  simp only
  rw [hsplit, hshift, hmean]
  simp

/-- The lifted field potential `Φ_{ψ,a}` on the Euclidean lift. -/
def loopHS (ℓ : Ioc (0 : ℝ) 1) (a : ℝ) (ψ : LoopScaleProfile ℓ.val) (N : ℕ+)
    (x : HsEuclidean N) : ℝ :=
  loopScalePotential ℓ a ψ (N : ℕ) (WithLp.ofLp x)

/-- The Riesz Hamiltonian on the Euclidean lift, `β · energy`. -/
def rieszH (P : Parameters) (N : ℕ+) : HsEuclidean N → ℝ :=
  hsPairExpression (hsRieszPairPotentials N P.val.1 P.property.1 (parametersExponent P))

/-- The expression `Σ_k ∂_kH ∂_kΦ − Δ Φ` of `𝓛Φ` in partial derivatives on the lift. -/
def loopLHS (P : Parameters) (N : ℕ+) (ℓ : Ioc (0 : ℝ) 1) (a : ℝ) (ψ : LoopScaleProfile ℓ.val)
    (x : HsEuclidean N) : ℝ :=
  ∑ k : Fin (N : ℕ), hsPartial (rieszH P N) k x * hsPartial (loopHS ℓ a ψ N) k x -
    ∑ k : Fin (N : ℕ), hsPartial (hsPartial (loopHS ℓ a ψ N) k) k x

theorem contDiff_loopScalePotential (ℓ : Ioc (0 : ℝ) 1) (a : ℝ) (ψ : LoopScaleProfile ℓ.val)
    (hψ : ContDiff ℝ ∞ ψ.val) (N : ℕ) : ContDiff ℝ ∞ (loopScalePotential ℓ a ψ N) := by
  unfold loopScalePotential
  refine contDiff_const.mul (ContDiff.sum fun i _ => ?_)
  exact (contDiff_primitive hψ).comp
    ((ContinuousLinearMap.proj i : (Fin N → ℝ) →L[ℝ] ℝ).contDiff.div_const ℓ.val)

theorem contDiff_loopHS (ℓ : Ioc (0 : ℝ) 1) (a : ℝ) (ψ : LoopScaleProfile ℓ.val)
    (hψ : ContDiff ℝ ∞ ψ.val) (N : ℕ+) : ContDiff ℝ ∞ (loopHS ℓ a ψ N) := by
  have hof : ContDiff ℝ ∞ (fun x : HsEuclidean N => (WithLp.ofLp x : Fin (N : ℕ) → ℝ)) :=
    contDiff_pi.mpr fun i => (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff
  exact (contDiff_loopScalePotential ℓ a ψ hψ (N : ℕ)).comp hof

/-- The field potential is bounded on the whole lift, by the periodic primitive of the profile
(mean zero, so that the primitive is periodic). -/
theorem exists_abs_loopHS_le (ℓ : Ioc (0 : ℝ) 1) (a : ℝ) (ψ : LoopScaleProfile ℓ.val)
    (hψ : ContDiff ℝ ∞ ψ.val) (hmean : ∫ t in (0 : ℝ)..ℓ.val⁻¹, ψ.val t = 0) (N : ℕ+) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x : HsEuclidean N, |loopHS ℓ a ψ N x| ≤ M := by
  have hℓ : 0 < ℓ.val⁻¹ := inv_pos.mpr ℓ.property.1
  have hP := exists_abs_le_of_continuous_periodic hℓ
    (contDiff_primitive hψ).continuous
    (periodic_primitive hψ.continuous ψ.property.1 hmean)
  obtain ⟨MP, hMP0, hMP⟩ := hP
  refine ⟨|a| * ℓ.val ^ 2 * (N : ℝ) * MP, by positivity, fun x => ?_⟩
  unfold loopHS loopScalePotential
  have hsum : |∑ i : Fin (N : ℕ), ∫ u in (0 : ℝ)..((WithLp.ofLp x : Fin (N : ℕ) → ℝ) i / ℓ.val),
      ψ.val u| ≤ (N : ℝ) * MP := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i : Fin (N : ℕ), |∫ u in (0 : ℝ)..((WithLp.ofLp x : Fin (N : ℕ) → ℝ) i / ℓ.val),
          ψ.val u| ≤ ∑ _i : Fin (N : ℕ), MP := Finset.sum_le_sum fun i _ => hMP _
      _ = (N : ℝ) * MP := by simp
  calc |a * ℓ.val ^ 2 * ∑ i : Fin (N : ℕ), ∫ u in (0 : ℝ)..((WithLp.ofLp x : Fin (N : ℕ) → ℝ) i /
          ℓ.val), ψ.val u|
      = |a| * ℓ.val ^ 2 * |∑ i : Fin (N : ℕ), ∫ u in (0 : ℝ)..((WithLp.ofLp x : Fin (N : ℕ) → ℝ) i /
          ℓ.val), ψ.val u| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg ℓ.val)]
    _ ≤ |a| * ℓ.val ^ 2 * ((N : ℝ) * MP) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = |a| * ℓ.val ^ 2 * (N : ℝ) * MP := by ring

/-- The first partial derivatives of the field potential on the lift are those of
the field potential on the coordinates. -/
theorem hsPartial_loopHS (ℓ : Ioc (0 : ℝ) 1) (a : ℝ) (ψ : LoopScaleProfile ℓ.val)
    (hψ : ContDiff ℝ ∞ ψ.val) (N : ℕ+) (k : Fin (N : ℕ)) (x : HsEuclidean N) :
    hsPartial (loopHS ℓ a ψ N) k x =
      partialDeriv (loopScalePotential ℓ a ψ (N : ℕ)) k (WithLp.ofLp x) :=
  hsPartial_eq_partialDeriv (G := loopScalePotential ℓ a ψ (N : ℕ)) (U := univ) univ_mem
    (fun _ _ => rfl) ((contDiff_loopHS ℓ a ψ hψ N).differentiable (by simp) x) k

/-- The second partial derivatives of the field potential on the lift. -/
theorem hsPartial_hsPartial_loopHS (ℓ : Ioc (0 : ℝ) 1) (a : ℝ) (ψ : LoopScaleProfile ℓ.val)
    (hψ : ContDiff ℝ ∞ ψ.val) (N : ℕ+) (k l : Fin (N : ℕ)) (x : HsEuclidean N) :
    hsPartial (hsPartial (loopHS ℓ a ψ N) k) l x =
      partialDeriv (partialDeriv (loopScalePotential ℓ a ψ (N : ℕ)) k) l (WithLp.ofLp x) := by
  have hfun : hsPartial (loopHS ℓ a ψ N) k =
      fun y => partialDeriv (loopScalePotential ℓ a ψ (N : ℕ)) k (WithLp.ofLp y) :=
    funext fun y => hsPartial_loopHS ℓ a ψ hψ N k y
  exact hsPartial_eq_partialDeriv (G := partialDeriv (loopScalePotential ℓ a ψ (N : ℕ)) k)
    (U := univ) univ_mem (fun y _ => congrFun hfun y)
    ((contDiff_hsPartial (contDiff_loopHS ℓ a ψ hψ N) k).differentiable (by simp) x) l

/-- Configurations lift into the open chamber. -/
theorem mem_hsChamber_configuration (X : Configuration N) :
    (WithLp.toLp 2 X.val : HsEuclidean N) ∈ hsChamber N := by
  apply mem_hsChamber_of_hsUnitGap_pos
  intro j
  rw [hsUnitGap_liftConfiguration]
  exact div_pos (gap_pos X _) (by exact_mod_cast N.pos)

/-- The Langevin expression of the field potential is the partial-derivative expression of
`𝓛Φ` at every configuration. -/
theorem loopLHS_eq_loopOperatorPotential (P : Parameters) (N : ℕ+) (ℓ : Ioc (0 : ℝ) 1) (a : ℝ)
    (ψ : LoopScaleProfile ℓ.val) (hψ : ContDiff ℝ ∞ ψ.val) (X : Configuration N) :
    loopLHS P N ℓ a ψ (WithLp.toLp 2 X.val) = loopOperatorPotential P N ℓ a ψ X := by
  have hx := mem_hsChamber_configuration X
  have hH : ∀ k : Fin (N : ℕ), hsPartial (rieszH P N) k (WithLp.toLp 2 X.val) =
      P.val.1 * partialDeriv (energyLift (parametersExponent P) (N : ℕ)) k X.val := fun k =>
    hsPartial_hsPairExpression_of_mem_chamber N P.val.1 P.property.1 (parametersExponent P) hx k
  unfold loopLHS loopOperatorPotential
  rw [Finset.mul_sum]
  unfold laplacian
  congr 1
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [hH k, hsPartial_loopHS ℓ a ψ hψ N k (WithLp.toLp 2 X.val), WithLp.ofLp_toLp]
    ring
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [hsPartial_hsPartial_loopHS ℓ a ψ hψ N k k (WithLp.toLp 2 X.val), WithLp.ofLp_toLp]

/-- The error term of the cutoff Langevin expression of `χ_h Φ`: `Φ (Σ ∂_kH ∂_kχ − Δχ) −
2 Σ ∂_kχ ∂_kΦ`. It vanishes wherever the cutoff is locally constant. -/
def loopError (P : Parameters) (N : ℕ+) (ℓ : Ioc (0 : ℝ) 1) (a : ℝ) (ψ : LoopScaleProfile ℓ.val)
    (h : ℝ) (x : HsEuclidean N) : ℝ :=
  loopHS ℓ a ψ N x * (∑ k : Fin (N : ℕ), hsPartial (rieszH P N) k x *
      hsPartial (hsUnitGapCutoff N h) k x -
    ∑ k : Fin (N : ℕ), hsPartial (hsPartial (hsUnitGapCutoff N h) k) k x) -
  2 * ∑ k : Fin (N : ℕ), hsPartial (hsUnitGapCutoff N h) k x * hsPartial (loopHS ℓ a ψ N) k x

/-- The Langevin expression of the cutoff test, split into the cutoff times `𝓛Φ` and the error. -/
theorem langevin_cutoff_eq (P : Parameters) (N : ℕ+) (ℓ : Ioc (0 : ℝ) 1) (a : ℝ)
    (ψ : LoopScaleProfile ℓ.val) (hψ : ContDiff ℝ ∞ ψ.val) (h : ℝ) (x : HsEuclidean N) :
    inner ℝ (gradient (rieszH P N) x)
        (gradient (fun y => hsUnitGapCutoff N h y * loopHS ℓ a ψ N y) x) -
      Laplacian.laplacian (fun y => hsUnitGapCutoff N h y * loopHS ℓ a ψ N y) x =
      hsUnitGapCutoff N h x * loopLHS P N ℓ a ψ x + loopError P N ℓ a ψ h x := by
  rw [hsGradientCutoffIdentity h (loopHS ℓ a ψ N) (rieszH P N) (contDiff_loopHS ℓ a ψ hψ N) x]
  unfold loopLHS loopError
  ring

/-- Where every gap exceeds `2h`, the error term vanishes. -/
theorem loopError_eq_zero {P : Parameters} {N : ℕ+} {ℓ : Ioc (0 : ℝ) 1} {a : ℝ}
    {ψ : LoopScaleProfile ℓ.val} {h : ℝ} (hh : 0 < h) {x : HsEuclidean N}
    (hx : ∀ j : Fin (N : ℕ), 2 * h < hsUnitGap N j x) : loopError P N ℓ a ψ h x = 0 := by
  unfold loopError
  simp only [hsPartial_hsUnitGapCutoff_eq_zero hh hx, hsPartial_hsPartial_hsUnitGapCutoff_eq_zero hh hx,
    mul_zero, zero_mul, Finset.sum_const_zero, sub_self, mul_zero]

/-- A sum of `M` terms each bounded by `B` is bounded by `M B`. -/
theorem abs_sum_le_card_mul {M : ℕ} {f : Fin M → ℝ} {B : ℝ} (hf : ∀ k, |f k| ≤ B) :
    |∑ k, f k| ≤ (M : ℝ) * B := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ k, |f k| ≤ ∑ _k : Fin M, B := Finset.sum_le_sum fun k _ => hf k
    _ = (M : ℝ) * B := by simp

/-- The error term is bounded, uniformly on the lift, by a constant times the power sum of
gaps of order `s + 1` and the cutoff scales `h⁻¹ + h⁻²`. -/
theorem abs_loopError_le (P : Parameters) (ℓ : Ioc (0 : ℝ) 1) (a : ℝ)
    (ψ : LoopScaleProfile ℓ.val) (hψ : ContDiff ℝ ∞ ψ.val)
    (hmean : ∫ t in (0 : ℝ)..ℓ.val⁻¹, ψ.val t = 0) (N : ℕ+) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (h : ℝ), 0 < h → ∀ X : Configuration N,
      |loopError P N ℓ a ψ h (WithLp.toLp 2 X.val)| ≤
        K * (h⁻¹ + h⁻¹ ^ 2) * (1 + gapPowerSum ((parametersExponent P).val + 1) X) := by
  obtain ⟨C₀, hC₀, hC₀b⟩ := exists_bound_deriv_loopStep
  obtain ⟨CE, hCE, hEb⟩ := exists_abs_partialDeriv_energyLift_le (parametersExponent P) N
  obtain ⟨M0, hM0, hM0b⟩ := exists_abs_loopHS_le ℓ a ψ hψ hmean N
  obtain ⟨Mψ, hMψ0, hMψb⟩ := exists_abs_le_of_continuous_periodic (inv_pos.mpr ℓ.property.1)
    hψ.continuous ψ.property.1
  have hβ : 0 ≤ P.val.1 := P.property.1.le
  have hNr : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
  set β := P.val.1 with hβdef
  set M1 := |a| * ℓ.val * Mψ with hM1def
  have hM1 : 0 ≤ M1 := by
    have := ℓ.property.1
    positivity
  set K₁ := M0 * (N : ℝ) ^ 2 * (2 * β * CE * C₀) with hK₁
  set K₂ := M0 * (N : ℝ) ^ 2 * (4 * C₀ + 4 * (N : ℝ) * C₀ ^ 2) with hK₂
  set K₃ := 4 * (N : ℝ) ^ 2 * C₀ * M1 with hK₃
  have hK₁0 : 0 ≤ K₁ := by positivity
  have hK₂0 : 0 ≤ K₂ := by positivity
  have hK₃0 : 0 ≤ K₃ := by positivity
  refine ⟨K₁ + K₂ + K₃, by positivity, fun h hh X => ?_⟩
  set x : HsEuclidean N := WithLp.toLp 2 X.val with hxdef
  set g := gapPowerSum ((parametersExponent P).val + 1) X with hgdef
  have hg0 : 0 ≤ g := gapPowerSum_nonneg _ X
  have hC : ∀ t, |deriv loopStep t| ≤ C₀ := fun t => (hC₀b t).1
  -- the bounds on the individual factors
  have hHk : ∀ k : Fin (N : ℕ), |hsPartial (rieszH P N) k x| ≤ β * CE * g := by
    intro k
    have hHk' : hsPartial (rieszH P N) k x = P.val.1 *
        partialDeriv (energyLift (parametersExponent P) (N : ℕ)) k X.val :=
      hsPartial_hsPairExpression_of_mem_chamber N P.val.1 P.property.1 (parametersExponent P)
        (mem_hsChamber_configuration X) k
    rw [hxdef, hHk', abs_mul, abs_of_nonneg hβ]
    exact (mul_le_mul_of_nonneg_left (hEb X k) hβ).trans_eq (by ring)
  have hχ1 : ∀ k : Fin (N : ℕ), |hsPartial (hsUnitGapCutoff N h) k x| ≤ (N : ℝ) * (2 * C₀ / h) :=
    fun k => abs_hsPartial_hsUnitGapCutoff_le N hC hh k x
  have hχ2 : ∀ k l : Fin (N : ℕ), |hsPartial (hsPartial (hsUnitGapCutoff N h) l) k x| ≤
      (N : ℝ) * ((4 * C₀ + 4 * (N : ℝ) * C₀ ^ 2) / h ^ 2) :=
    fun k l => abs_hsPartial_hsPartial_hsUnitGapCutoff_le N hC₀b hh l k x
  have hΦk : ∀ k : Fin (N : ℕ), |hsPartial (loopHS ℓ a ψ N) k x| ≤ M1 := fun k => by
    rw [hsPartial_loopHS ℓ a ψ hψ N k x]
    exact abs_partialDeriv_loopScalePotential_le ℓ a ψ hMψb k _
  -- the three sums of the error term
  set A := ∑ k : Fin (N : ℕ), hsPartial (rieszH P N) k x * hsPartial (hsUnitGapCutoff N h) k x
    with hAdef
  set B := ∑ k : Fin (N : ℕ), hsPartial (hsPartial (hsUnitGapCutoff N h) k) k x with hBdef
  set C := ∑ k : Fin (N : ℕ), hsPartial (hsUnitGapCutoff N h) k x * hsPartial (loopHS ℓ a ψ N) k x
    with hCdef
  have hu : 0 ≤ h⁻¹ := (inv_pos.mpr hh).le
  have hA : |A| ≤ (N : ℝ) * ((β * CE * g) * ((N : ℝ) * (2 * C₀ / h))) := by
    refine abs_sum_le_card_mul fun k => ?_
    rw [abs_mul]
    exact mul_le_mul (hHk k) (hχ1 k) (abs_nonneg _)
      (mul_nonneg (mul_nonneg hβ hCE) hg0)
  have hB : |B| ≤ (N : ℝ) * ((N : ℝ) * ((4 * C₀ + 4 * (N : ℝ) * C₀ ^ 2) / h ^ 2)) := by
    refine abs_sum_le_card_mul fun k => ?_
    exact hχ2 k k
  have hCb : |C| ≤ (N : ℝ) * ((N : ℝ) * (2 * C₀ / h) * M1) := by
    refine abs_sum_le_card_mul fun k => ?_
    rw [abs_mul]
    exact mul_le_mul (hχ1 k) (hΦk k) (abs_nonneg _)
      (mul_nonneg hNr (div_nonneg (mul_nonneg (by norm_num) hC₀) hh.le))
  -- the error term is `Φ (A − B) − 2 C`
  have hEq : loopError P N ℓ a ψ h x = loopHS ℓ a ψ N x * (A - B) - 2 * C := rfl
  have hL : |loopHS ℓ a ψ N x| ≤ M0 := hM0b x
  have hAB : |A - B| ≤ |A| + |B| := abs_sub _ _
  have hprod : |loopHS ℓ a ψ N x| * |A - B| ≤ M0 * (|A| + |B|) :=
    mul_le_mul hL hAB (abs_nonneg _) hM0
  have hmain : |loopError P N ℓ a ψ h x| ≤ M0 * (|A| + |B|) + 2 * |C| := by
    rw [hEq]
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_mul, abs_two]
    linarith [hprod]
  -- the explicit bounds of the three sums
  have hsum_bound : M0 * (|A| + |B|) + 2 * |C| ≤
      K₁ * g * h⁻¹ + K₂ * h⁻¹ ^ 2 + K₃ * h⁻¹ := by
    have e1 : (N : ℝ) * ((β * CE * g) * ((N : ℝ) * (2 * C₀ / h))) =
        (N : ℝ) ^ 2 * (2 * β * CE * C₀) * g * h⁻¹ := by
      rw [div_eq_mul_inv]; ring
    have e2 : (N : ℝ) * ((N : ℝ) * ((4 * C₀ + 4 * (N : ℝ) * C₀ ^ 2) / h ^ 2)) =
        (N : ℝ) ^ 2 * (4 * C₀ + 4 * (N : ℝ) * C₀ ^ 2) * h⁻¹ ^ 2 := by
      rw [div_eq_mul_inv, inv_pow]; ring
    have e3 : 2 * ((N : ℝ) * ((N : ℝ) * (2 * C₀ / h) * M1)) =
        4 * (N : ℝ) ^ 2 * C₀ * M1 * h⁻¹ := by
      rw [div_eq_mul_inv]; ring
    have hA' := hA.trans_eq e1
    have hB' := hB.trans_eq e2
    have hC' := mul_le_mul_of_nonneg_left hCb (by norm_num : (0 : ℝ) ≤ 2)
    rw [e3] at hC'
    have hM : M0 * (|A| + |B|) ≤ M0 * ((N : ℝ) ^ 2 * (2 * β * CE * C₀) * g * h⁻¹ +
        (N : ℝ) ^ 2 * (4 * C₀ + 4 * (N : ℝ) * C₀ ^ 2) * h⁻¹ ^ 2) :=
      mul_le_mul_of_nonneg_left (add_le_add hA' hB') hM0
    have hK : K₁ * g * h⁻¹ + K₂ * h⁻¹ ^ 2 + K₃ * h⁻¹ = M0 * ((N : ℝ) ^ 2 * (2 * β * CE * C₀) * g * h⁻¹ +
        (N : ℝ) ^ 2 * (4 * C₀ + 4 * (N : ℝ) * C₀ ^ 2) * h⁻¹ ^ 2) + 4 * (N : ℝ) ^ 2 * C₀ * M1 * h⁻¹ := by
      rw [hK₁, hK₂, hK₃]; ring
    rw [hK]
    linarith [hM, hC']
  -- the final estimate with the coefficient `K = K₁ + K₂ + K₃`
  have hfin : K₁ * g * h⁻¹ + K₂ * h⁻¹ ^ 2 + K₃ * h⁻¹ ≤
      (K₁ + K₂ + K₃) * (h⁻¹ + h⁻¹ ^ 2) * (1 + g) := by
    have hd : (K₁ + K₂ + K₃) * (h⁻¹ + h⁻¹ ^ 2) * (1 + g) - (K₁ * g * h⁻¹ + K₂ * h⁻¹ ^ 2 + K₃ * h⁻¹) =
        K₁ * h⁻¹ + K₂ * h⁻¹ + K₁ * h⁻¹ ^ 2 + K₃ * h⁻¹ ^ 2 + K₂ * g * h⁻¹ + K₃ * g * h⁻¹ +
          K₁ * g * h⁻¹ ^ 2 + K₂ * g * h⁻¹ ^ 2 + K₃ * g * h⁻¹ ^ 2 := by ring
    have hnn : 0 ≤ K₁ * h⁻¹ + K₂ * h⁻¹ + K₁ * h⁻¹ ^ 2 + K₃ * h⁻¹ ^ 2 + K₂ * g * h⁻¹ +
        K₃ * g * h⁻¹ + K₁ * g * h⁻¹ ^ 2 + K₂ * g * h⁻¹ ^ 2 + K₃ * g * h⁻¹ ^ 2 := by
      have := hK₁0; have := hK₂0; have := hK₃0
      positivity
    linarith [hd, hnn]
  calc |loopError P N ℓ a ψ h x| ≤ M0 * (|A| + |B|) + 2 * |C| := hmain
    _ ≤ K₁ * g * h⁻¹ + K₂ * h⁻¹ ^ 2 + K₃ * h⁻¹ := hsum_bound
    _ ≤ (K₁ + K₂ + K₃) * (h⁻¹ + h⁻¹ ^ 2) * (1 + g) := hfin

/-- The error term vanishes off the collision strip, and on it is bounded by the power sum
of gaps, so that its bound is the strip indicator of `1 + gapPowerSum (s + 1)`. -/
theorem exists_loopError_bound (P : Parameters) (ℓ : Ioc (0 : ℝ) 1) (a : ℝ)
    (ψ : LoopScaleProfile ℓ.val) (hψ : ContDiff ℝ ∞ ψ.val)
    (hmean : ∫ t in (0 : ℝ)..ℓ.val⁻¹, ψ.val t = 0) (N : ℕ+) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (h : ℝ), 0 < h → ∀ X : Configuration N,
      |loopError P N ℓ a ψ h (WithLp.toLp 2 X.val)| ≤
        K * (h⁻¹ + h⁻¹ ^ 2) * {X : Configuration N | ∃ j : Fin (N : ℕ),
          gap X (j : ℕ) ≤ 2 * h * N}.indicator
            (fun X : Configuration N => 1 + gapPowerSum ((parametersExponent P).val + 1) X) X := by
  obtain ⟨K, hK, hb⟩ := abs_loopError_le P ℓ a ψ hψ hmean N
  refine ⟨K, hK, fun h hh X => ?_⟩
  by_cases hX : ∃ j : Fin (N : ℕ), gap X (j : ℕ) ≤ 2 * h * N
  · rw [indicator_of_mem (show X ∈ {X : Configuration N | ∃ j : Fin (N : ℕ),
        gap X (j : ℕ) ≤ 2 * h * N} from hX)]
    exact hb h hh X
  · rw [indicator_of_notMem (show X ∉ {X : Configuration N | ∃ j : Fin (N : ℕ),
        gap X (j : ℕ) ≤ 2 * h * N} from hX), mul_zero]
    have hx : ∀ j : Fin (N : ℕ), 2 * h < hsUnitGap N j (WithLp.toLp 2 X.val) := by
      intro j
      rw [hsUnitGap_liftConfiguration, lt_div_iff₀ (by exact_mod_cast N.pos : (0 : ℝ) < N)]
      exact not_le.mp (not_exists.mp hX j)
    rw [loopError_eq_zero hh hx, abs_zero]

end Riesz1
