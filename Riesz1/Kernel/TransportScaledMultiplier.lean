/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Kernel.TransportScaledFubini
public import Riesz1.Kernel.TransportFormula

/-!
# The transport multiplier on circles of arbitrary length

Let `A = -1/(4πβ tan(πs/2))` (`transportConst`) and let `J_L(k) = ∫_{C_L} K_{s,L}(u) e_k(u) du`
(`kernelCoeff`). The transport coefficients equal `transportMult · coeff`, where
`transportMult` is the prefactor of `Riesz1.transportCoeffs`. This file proves
`A · J_L(k) = transportMult P L k` for `k ≠ 0` (`transportConst_mul_kernelCoeff`).

The unit case `L = 1` comes from the pointwise transport formula `transport_pointwise_formula`,
tested against the cosine `ξ(z) = Re e_k(z)`. The general case follows from the change of variables
`u = Lv`, which multiplies both `J_L` and the multiplier by `L^s`.
-/

public section

open MeasureTheory Set intervalIntegral Filter Topology Complex
open scoped ContDiff Real

namespace Riesz1

/-- The transport constant `A_s = -1/(4πβ tan(πs/2))`. -/
@[expose] noncomputable def transportConst (β s : ℝ) : ℝ := -(1 / (4 * π * β * Real.tan (π * s / 2)))

/-- The Fourier integral `J_L(k) = ∫_{C_L} K_{s,L}(u) e_k(u) du` over the cell `C_L = (-L/2, L/2]`. -/
@[expose] noncomputable def kernelCoeff (s L : ℝ) (k : ℤ) : ℂ :=
  ∫ u in Ioc (-(L / 2)) (L / 2), (scaledKernel s L u : ℂ) * charE L k u

/-- The multiplier of the transport coefficients on the circle of length `L`: the prefactor
of `Riesz1.transportCoeffs`. -/
@[expose] noncomputable def transportMult (P : Parameters) (L : ℝ) (k : ℤ) : ℂ :=
  -((|2 * π * (k : ℝ) / L| ^ (1 - P.val.2) : ℝ) : ℂ) /
    ((2 * P.val.1 * rieszConstant (parametersExponent P) : ℝ) * (2 * π * I * (k : ℂ) / L))

/-- For fixed `x`, almost every `y` has `x - y ∉ L ℤ`, so `kernelRep` is the scaled kernel. -/
lemma ae_kernelRep_sub' (s L x : ℝ) :
    ∀ᵐ y : ℝ, kernelRep s L (x - y) = scaledKernel s L (x - y) := by
  have hcount : (Set.range fun k : ℤ => x - k * L).Countable := Set.countable_range _
  filter_upwards [hcount.ae_notMem volume] with y hy
  exact kernelRep_of_ne fun k h => hy ⟨k, by linarith⟩

/-- For fixed `x`, almost every `y` has `kernelRep s 1 (x - y) = K_s(x - y)`. -/
lemma ae_kernelRep_one_sub (s x : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    ∀ᵐ y : ℝ, kernelRep s 1 (x - y) = periodicKernel s (x - y) := by
  have hcount : (Set.range fun k : ℤ => x - k * 1).Countable := Set.countable_range _
  filter_upwards [hcount.ae_notMem volume] with y hy
  have hr : ∀ k : ℤ, x - y ≠ k * 1 := fun k h => hy ⟨k, by linarith⟩
  rw [kernelRep_of_ne hr, scaledKernel_eq_periodic hs0 hs1 one_pos hr, Real.one_rpow, one_mul,
    div_one]

/-- The scaled kernel is `L^{s-1} K_s(u/L)` for almost every `u`. -/
lemma ae_scaledKernel_eq_periodic {s L : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hL : 0 < L) :
    ∀ᵐ u : ℝ, scaledKernel s L u = L ^ (s - 1) * periodicKernel s (u / L) := by
  have hcount : (Set.range fun k : ℤ => (k : ℝ) * L).Countable := Set.countable_range _
  filter_upwards [hcount.ae_notMem volume] with u hu
  exact scaledKernel_eq_periodic hs0 hs1 hL fun k h => hu ⟨k, h.symm⟩

/-- The character rescales: `e_{L,k}(u) = e_{1,k}(u/L)`. -/
lemma charE_div_eq {L : ℝ} (hL : L ≠ 0) (k : ℤ) (u : ℝ) :
    charE L k u = charE 1 k (u / L) := by
  unfold charE
  rw [show 2 * π * ((-k : ℤ) : ℝ) * u / L = 2 * π * ((-k : ℤ) : ℝ) * (u / L) / 1 by
    field_simp]

/-- **Scaling of the Fourier integral of the kernel.** `J_L(k) = L^s J_1(k)`. -/
lemma kernelCoeff_scale {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {L : ℝ} (hL : 0 < L) (k : ℤ) :
    kernelCoeff s L k = ((L ^ s : ℝ) : ℂ) * kernelCoeff s 1 k := by
  have hle : -(L / 2) ≤ L / 2 := by linarith
  have hle1 : -(1 / 2 : ℝ) ≤ 1 / 2 := by norm_num
  have hLne : L ≠ 0 := hL.ne'
  have hJ1 : kernelCoeff s 1 k = ∫ v in Ioc (-(1 / 2 : ℝ)) (1 / 2),
      ((periodicKernel s v : ℝ) : ℂ) * charE 1 k v := by
    unfold kernelCoeff
    refine setIntegral_congr_ae measurableSet_Ioc ?_
    filter_upwards [ae_scaledKernel_eq_periodic hs0 hs1 one_pos] with v hv _
    rw [hv, Real.one_rpow, div_one, one_mul]
  have step1 : kernelCoeff s L k = ∫ u in Ioc (-(L / 2)) (L / 2),
      ((L ^ (s - 1) : ℝ) : ℂ) * ((periodicKernel s (u / L) : ℝ) : ℂ) * charE 1 k (u / L) := by
    unfold kernelCoeff
    refine setIntegral_congr_ae measurableSet_Ioc ?_
    filter_upwards [ae_scaledKernel_eq_periodic hs0 hs1 hL] with u hu _
    rw [hu, charE_div_eq hLne k u]
    push_cast
    ring
  have step2 : ∫ u in Ioc (-(L / 2)) (L / 2),
      ((L ^ (s - 1) : ℝ) : ℂ) * ((periodicKernel s (u / L) : ℝ) : ℂ) * charE 1 k (u / L) =
      (L : ℂ) * ∫ v in Ioc (-(1 / 2 : ℝ)) (1 / 2),
        ((L ^ (s - 1) : ℝ) : ℂ) * ((periodicKernel s v : ℝ) : ℂ) * charE 1 k v := by
    rw [← intervalIntegral.integral_of_le hle, ← intervalIntegral.integral_of_le hle1]
    have h := intervalIntegral.integral_comp_div (a := -(L / 2)) (b := L / 2) (c := L)
      (fun v : ℝ => ((L ^ (s - 1) : ℝ) : ℂ) * ((periodicKernel s v : ℝ) : ℂ) * charE 1 k v) hLne
    rw [show -(L / 2) / L = -(1 / 2 : ℝ) by field_simp,
      show L / 2 / L = (1 / 2 : ℝ) by field_simp, Complex.real_smul] at h
    exact h
  have hLs : L ^ s = L ^ (s - 1) * L := by
    have h := Real.rpow_add_one hL.ne' (s - 1)
    rwa [sub_add_cancel] at h
  have hint : ∀ v : ℝ, ((L ^ (s - 1) : ℝ) : ℂ) * ((periodicKernel s v : ℝ) : ℂ) * charE 1 k v =
      ((L ^ (s - 1) : ℝ) : ℂ) * (((periodicKernel s v : ℝ) : ℂ) * charE 1 k v) :=
    fun v => mul_assoc _ _ _
  rw [step1, step2, hJ1]
  simp_rw [hint]
  rw [MeasureTheory.integral_const_mul, hLs]
  push_cast
  ring

/-- The multiplier scales as `L^s`: `transportMult P L k = L^s transportMult P 1 k`. -/
lemma transportMult_scale (P : Parameters) {L : ℝ} (hL : 0 < L) {k : ℤ} (hk : k ≠ 0) :
    transportMult P L k = ((L ^ P.val.2 : ℝ) : ℂ) * transportMult P 1 k := by
  have hs1 : P.val.2 < 1 := P.property.2.2
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  have hpos : 0 < |2 * π * (k : ℝ)| :=
    abs_pos.2 (mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) hk')
  have hrel : L ^ (1 - P.val.2) * L ^ P.val.2 = L := by
    rw [← Real.rpow_add hL, show (1 - P.val.2) + P.val.2 = 1 by ring, Real.rpow_one]
  have hrelC : ((L ^ (1 - P.val.2) : ℝ) : ℂ) * ((L ^ P.val.2 : ℝ) : ℂ) = (L : ℂ) := by
    exact_mod_cast hrel
  have hpowC : ((L ^ (1 - P.val.2) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.rpow_pos_of_pos hL _).ne'
  have hℓ : ((L ^ P.val.2 : ℝ) : ℂ) = (L : ℂ) / ((L ^ (1 - P.val.2) : ℝ) : ℂ) := by
    rw [eq_div_iff hpowC]
    linear_combination hrelC
  have hLC : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have hY : (2 * π * I * (k : ℂ)) ≠ 0 := by
    have hk'' : (k : ℂ) ≠ 0 := by exact_mod_cast hk
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero))
      Complex.I_ne_zero) hk''
  have hD : ((2 * P.val.1 * rieszConstant (parametersExponent P) : ℝ) : ℂ) ≠ 0 := by
    have hD' : (2 * P.val.1 * rieszConstant (parametersExponent P) : ℝ) ≠ 0 :=
      mul_ne_zero (mul_ne_zero two_ne_zero P.property.1.ne')
        (rieszConstant_parametersExponent_pos P).ne'
    exact_mod_cast hD'
  have habs : |2 * π * (k : ℝ) / L| = |2 * π * (k : ℝ)| / L := by
    rw [abs_div, abs_of_pos hL]
  unfold transportMult
  simp only [div_one, Complex.ofReal_one]
  rw [habs, Real.div_rpow hpos.le hL.le, Complex.ofReal_div, hℓ]
  field_simp

/-- The real cosine test `ξ(z) = Re e_k(z)` on the unit circle. -/
noncomputable def cosTest (k : ℤ) (z : UnitAddCircle) : ℝ := (fourier k z).re

lemma cosTest_coe (k : ℤ) (x : ℝ) : cosTest k (x : UnitAddCircle) = Real.cos (2 * π * k * x) := by
  unfold cosTest
  rw [fourier_coe_apply]
  have e : 2 * (π : ℂ) * I * (k : ℂ) * (x : ℂ) / ((1 : ℝ) : ℂ) = ((2 * π * k * x : ℝ) : ℂ) * I := by
    push_cast
    ring
  rw [e, Complex.exp_ofReal_mul_I_re]

lemma cosTest_smooth (k : ℤ) : IsSmoothCircle (cosTest k) := by
  have h : (fun x : ℝ => cosTest k (x : UnitAddCircle)) = fun x : ℝ => Real.cos (2 * π * k * x) :=
    funext (cosTest_coe k)
  unfold IsSmoothCircle
  rw [h]
  exact Real.contDiff_cos.comp (contDiff_const.mul contDiff_id)

/-- The Fourier coefficient of a function on the unit circle, as an integral over the cell
`(-1/2, 1/2]` against the character `e_k`. -/
lemma circleCoeff_eq_interval (f : UnitAddCircle → ℝ) (k : ℤ) :
    circleCoeff f k = ∫ y in Ioc (-(1 / 2 : ℝ)) (1 / 2),
      ((f (y : UnitAddCircle) : ℝ) : ℂ) * charE 1 k y := by
  have hE : ∀ x : ℝ, fourier (-k) (x : UnitAddCircle) = charE 1 k x := by
    intro x
    rw [fourier_coe_apply]
    unfold charE
    congr 1
    push_cast
    ring
  unfold circleCoeff
  rw [fourierCoeff_eq_intervalIntegral _ k (-(1 / 2 : ℝ)), show -(1 / 2 : ℝ) + 1 = 1 / 2 by norm_num,
    intervalIntegral.integral_of_le (by norm_num), div_one, one_smul]
  congr 1
  funext y
  rw [hE y, smul_eq_mul, mul_comm]

/-- The cosine test has Fourier coefficient `1/2` at `k ≠ 0`. -/
lemma circleCoeff_cosTest {k : ℤ} (hk : k ≠ 0) : circleCoeff (cosTest k) k = 1 / 2 := by
  have hfun : (fun z : UnitAddCircle => ((cosTest k z : ℝ) : ℂ)) =
      fun z => (1 / 2 : ℂ) * (fourier k z + fourier (-k) z) := by
    funext z
    unfold cosTest
    rw [fourier_neg, Complex.re_eq_add_conj]
    ring
  have hi : ∀ n : ℤ, Integrable (⇑(fourier n) : UnitAddCircle → ℂ) AddCircle.haarAddCircle :=
    fun n => (fourier n).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  unfold circleCoeff
  rw [hfun, fourierCoeff.const_mul,
    show (fun z : UnitAddCircle => fourier k z + fourier (-k) z) =
      ⇑(fourier k) + ⇑(fourier (-k)) from rfl,
    fourierCoeff.add (hi k) (hi (-k)), fourierCoeff_fourier, fourierCoeff_fourier]
  have hne : -k ≠ k := fun h => hk (by omega)
  simp [hne]

/-- On the unit circle the transport coefficient is the multiplier times the Fourier coefficient
of the datum (`transportCoeffs` with `L = 1`). -/
lemma transportCoeffs_unit (P : Parameters) {ξ : UnitAddCircle → ℝ} (hξ : IsSmoothCircle ξ)
    {k : ℤ} (hk : k ≠ 0) :
    transportCoeffs P unitLength ⟨unitFun ξ, memLp_of_isSmoothCircle hξ⟩ k =
      transportMult P 1 k * circleCoeff ξ k := by
  rw [transportCoeffs_eq_mul hξ P k, primitiveCoeff_eq_mul hξ P.val.2 hk,
    circleCoeff_primitive_eq hξ hk]
  have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk
  have hY : (2 * π * I * (k : ℂ)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero))
      Complex.I_ne_zero) hk'
  have hD : ((2 * P.val.1 * rieszConstant (parametersExponent P) : ℝ) : ℂ) ≠ 0 := by
    have hD' : (2 * P.val.1 * rieszConstant (parametersExponent P) : ℝ) ≠ 0 :=
      mul_ne_zero (mul_ne_zero two_ne_zero P.property.1.ne')
        (rieszConstant_parametersExponent_pos P).ne'
    exact_mod_cast hD'
  unfold transportMult
  simp only [div_one, Complex.ofReal_one]
  push_cast
  field_simp

/-- **Unit multiplier.** For `k ≠ 0`, `A · J_1(k) = transportMult P 1 k`. This is the unit-circle
case of the transport multiplier, obtained from `transport_pointwise_formula`. -/
theorem unit_multiplier (P : Parameters) {k : ℤ} (hk : k ≠ 0) :
    ((transportConst P.val.1 P.val.2 : ℝ) : ℂ) * kernelCoeff P.val.2 1 k = transportMult P 1 k := by
  have hs0 : 0 < P.val.2 := P.property.2.1
  have hs1 : P.val.2 < 1 := P.property.2.2
  have hξ : IsSmoothCircle (cosTest k) := cosTest_smooth k
  obtain ⟨ψ, -, hψc, hψx⟩ := transport_pointwise_formula P (cosTest k) hξ
  -- the pointwise transport as a kernel integral over the unit cell
  have hψpt : ∀ x : ℝ, ψ (x : UnitAddCircle) = transportConst P.val.1 P.val.2 *
      ∫ y in Ioc (-(1 / 2 : ℝ)) (1 / 2),
        cosTest k (y : UnitAddCircle) * kernelRep P.val.2 1 (x - y) := by
    intro x
    rw [(hψx x).2, tsum_centered_eq_integral_kernel hs0 hs1 hξ x]
    unfold transportConst
    congr 1
    have hper : Function.Periodic (fun y : ℝ => cosTest k (y : UnitAddCircle) *
        periodicKernel P.val.2 (x - y)) 1 := by
      intro y
      have h1 : ((y + 1 : ℝ) : UnitAddCircle) = (y : UnitAddCircle) := AddCircle.coe_add_period (1 : ℝ) y
      simp only [h1]
      rw [show x - (y + 1) = (x - y) + ((-1 : ℤ) : ℝ) by push_cast; ring, periodicKernel_add_int]
    have hsh := hper.intervalIntegral_add_eq (-(1 / 2 : ℝ)) 0
    rw [show -(1 / 2 : ℝ) + 1 = 1 / 2 by norm_num, show (0 : ℝ) + 1 = 1 by norm_num] at hsh
    rw [← hsh, intervalIntegral.integral_of_le (by norm_num)]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae (ae_kernelRep_one_sub P.val.2 x hs0 hs1)] with y hy
    rw [hy]
  have hc : Continuous (fun y : ℝ => cosTest k (y : UnitAddCircle)) := (cosTest_smooth k).continuous
  have hg : IntegrableOn (fun y : ℝ => cosTest k (y : UnitAddCircle))
      (Ioc (-(1 / 2 : ℝ)) (1 / 2)) :=
    (hc.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  -- the Fourier coefficient of ψ, computed by Fubini
  have hcoef : circleCoeff ψ k = ((transportConst P.val.1 P.val.2 : ℝ) : ℂ) *
      circleCoeff (cosTest k) k * kernelCoeff P.val.2 1 k := by
    rw [circleCoeff_eq_interval ψ k, circleCoeff_eq_interval (cosTest k) k]
    have h2 : ∫ y in Ioc (-(1 / 2 : ℝ)) (1 / 2), ((ψ (y : UnitAddCircle) : ℝ) : ℂ) * charE 1 k y =
        ((transportConst P.val.1 P.val.2 : ℝ) : ℂ) * ∫ y in Ioc (-(1 / 2 : ℝ)) (1 / 2),
          ((∫ z in Ioc (-(1 / 2 : ℝ)) (1 / 2), cosTest k (z : UnitAddCircle) *
            kernelRep P.val.2 1 (y - z) : ℝ) : ℂ) * charE 1 k y := by
      rw [← MeasureTheory.integral_const_mul]
      refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun y => ?_)
      dsimp only
      rw [hψpt y]
      push_cast
      ring
    rw [h2, integral_kernel_charE hs0 hs1 zero_lt_one k hg]
    unfold kernelCoeff
    ring
  have key : circleCoeff ψ k = transportMult P 1 k * circleCoeff (cosTest k) k :=
    (hψc k).trans (transportCoeffs_unit P hξ hk)
  rw [hcoef, circleCoeff_cosTest hk] at key
  have h12 : (1 / 2 : ℂ) ≠ 0 := by norm_num
  apply mul_right_cancel₀ h12
  linear_combination key

/-- **Transport multiplier, general circle.** For `k ≠ 0`, `A · J_L(k) = transportMult P L k`. -/
theorem transportConst_mul_kernelCoeff (P : Parameters) {L : ℝ} (hL : 0 < L) {k : ℤ} (hk : k ≠ 0) :
    ((transportConst P.val.1 P.val.2 : ℝ) : ℂ) * kernelCoeff P.val.2 L k = transportMult P L k := by
  rw [kernelCoeff_scale P.property.2.1 P.property.2.2 hL k, transportMult_scale P hL hk,
    ← unit_multiplier P hk]
  ring

end Riesz1
