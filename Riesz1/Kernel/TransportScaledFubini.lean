/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Kernel.TransportScaledLocal

/-!
# Fubini identities for the scaled transport kernel

For `L > 0` let `C_L = (-L/2, L/2]`. This file proves the integrability and Fubini identities used
to compute Fourier coefficients of the transport convolution `∫_{C_L} g(y) K_{s,L}(x - y) dy`:

* `kernelRep` is a Borel function equal to `K_{s,L}` off the lattice `L ℤ`. It is used to get
  measurability of `(x, y) ↦ K_{s,L}(x - y)`, and it changes nothing in the `x`-integrals.
* the product `(x, y) ↦ g(y) K_{s,L}(x - y)` is integrable on `C_L × C_L` for `g ∈ L¹(C_L)`.
* for the character `e_k(x) = exp(2πi(-k)x/L)`, the Fourier coefficient of the convolution factors as
  `(∫ g e_k)(∫ K_{s,L} e_k)`.
-/

public section

open MeasureTheory Set intervalIntegral Filter Topology Complex
open scoped ContDiff Real

namespace Riesz1

open Classical in
/-- The scaled kernel with its values on the lattice `L ℤ` replaced by `0`. It is Borel measurable
and agrees with `K_{s,L}` off the lattice. -/
@[expose] noncomputable def kernelRep (s L : ℝ) : ℝ → ℝ :=
  {r : ℝ | ∀ k : ℤ, r ≠ k * L}.piecewise (scaledKernel s L) (fun _ => 0)

open Classical in
/-- The representative `kernelRep` is Borel measurable. -/
lemma measurable_kernelRep {s L : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hL : 0 < L) :
    Measurable (kernelRep s L) := by
  unfold kernelRep
  exact ContinuousOn.measurable_piecewise
    (fun _ hr => (scaledKernel_contDiffAt hs0 hs1 hL hr).continuousAt.continuousWithinAt)
    continuousOn_const (isOpen_lattice_compl hL).measurableSet

open Classical in
/-- Off the lattice, `kernelRep` is the scaled kernel. -/
lemma kernelRep_of_ne {s L r : ℝ} (hr : ∀ k : ℤ, r ≠ k * L) :
    kernelRep s L r = scaledKernel s L r :=
  Set.piecewise_eq_of_mem _ _ _ hr

/-- For fixed `y`, the representative `kernelRep (x - y)` agrees with `K_{s,L}(x - y)` for almost
every `x`, since the exceptional set `{x | x - y ∈ L ℤ}` is countable. -/
lemma ae_kernelRep_sub (s L y : ℝ) :
    ∀ᵐ x : ℝ, kernelRep s L (x - y) = scaledKernel s L (x - y) := by
  have hcount : (Set.range fun k : ℤ => y + k * L).Countable := Set.countable_range _
  filter_upwards [hcount.ae_notMem volume] with x hx
  exact kernelRep_of_ne fun k h => hx ⟨k, by linarith⟩

/-- The character `x ↦ exp(2πi(-k)x/L)` on the circle of length `L`, as a function of `x ∈ ℝ`. -/
@[expose] noncomputable def charE (L : ℝ) (k : ℤ) (x : ℝ) : ℂ :=
  Complex.exp (((2 * π * (-k : ℤ) * x / L : ℝ) : ℂ) * I)

lemma norm_charE (L : ℝ) (k : ℤ) (x : ℝ) : ‖charE L k x‖ = 1 := by
  unfold charE
  exact Complex.norm_exp_ofReal_mul_I _

lemma charE_mul (L : ℝ) (k : ℤ) (x y : ℝ) :
    charE L k x = charE L k (x - y) * charE L k y := by
  unfold charE
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma charE_add_period {L : ℝ} (hL : L ≠ 0) (k : ℤ) (x : ℝ) :
    charE L k (x + L) = charE L k x := by
  unfold charE
  have hreal : 2 * π * (-k : ℤ) * (x + L) / L = 2 * π * (-k : ℤ) * x / L + (-k : ℤ) * (2 * π) := by
    field_simp
  have h : (((2 * π * (-k : ℤ) * (x + L) / L : ℝ) : ℂ) * I) =
      ((2 * π * (-k : ℤ) * x / L : ℝ) : ℂ) * I + ((-k : ℤ) : ℂ) * (2 * π * I) := by
    rw [hreal]
    push_cast
    ring
  rw [h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- The integral over a period of a periodic function is independent of the window. -/
lemma integral_comp_sub_periodic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℝ → E} {L : ℝ} (hF : Function.Periodic F L) (y : ℝ) :
    ∫ x in (-(L / 2))..(L / 2), F (x - y) = ∫ x in (-(L / 2))..(L / 2), F x := by
  rw [intervalIntegral.integral_comp_sub_right F y]
  have h := hF.intervalIntegral_add_eq (-(L / 2) - y) (-(L / 2))
  rw [show -(L / 2) - y + L = L / 2 - y by ring, show -(L / 2) + L = L / 2 by ring] at h
  exact h

/-- The scaled kernel is `L`-periodic on all of `ℝ`. -/
lemma scaledKernel_periodic {s L : ℝ} (hL : 0 < L) : Function.Periodic (scaledKernel s L) L :=
  fun r => scaledKernel_add_period hL r

/-- The absolute scaled kernel: `∫_{C_L} |K_{s,L}(x - y)| dx` does not depend on `y`. -/
lemma setIntegral_abs_kernelRep_sub {s L : ℝ} (hL : 0 < L) (y : ℝ) :
    ∫ x in Ioc (-(L / 2)) (L / 2), |kernelRep s L (x - y)| =
      ∫ x in Ioc (-(L / 2)) (L / 2), |scaledKernel s L x| := by
  have hle : -(L / 2) ≤ L / 2 := by linarith
  have h1 : ∫ x in Ioc (-(L / 2)) (L / 2), |kernelRep s L (x - y)| =
      ∫ x in Ioc (-(L / 2)) (L / 2), |scaledKernel s L (x - y)| := by
    refine setIntegral_congr_ae measurableSet_Ioc ?_
    filter_upwards [ae_kernelRep_sub s L y] with x hx _
    rw [hx]
  have hper : Function.Periodic (fun x => |scaledKernel s L x|) L :=
    fun r => by simp only [scaledKernel_add_period hL r]
  rw [h1, ← intervalIntegral.integral_of_le hle, ← intervalIntegral.integral_of_le hle]
  exact integral_comp_sub_periodic hper y

/-- **Integrability of the transport product.** For `g` integrable on `C_L`, the function
`(x, y) ↦ g(y) K_{s,L}(x - y)` is integrable on `C_L × C_L`. -/
lemma integrable_kernelRep_prod {s L : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hL : 0 < L) {g : ℝ → ℝ}
    (hg : IntegrableOn g (Ioc (-(L / 2)) (L / 2))) :
    Integrable (fun p : ℝ × ℝ => g p.2 * kernelRep s L (p.1 - p.2))
      ((volume.restrict (Ioc (-(L / 2)) (L / 2))).prod
        (volume.restrict (Ioc (-(L / 2)) (L / 2)))) := by
  have hle : -(L / 2) ≤ L / 2 := by linarith
  have hmeas : AEStronglyMeasurable (fun p : ℝ × ℝ => g p.2 * kernelRep s L (p.1 - p.2))
      ((volume.restrict (Ioc (-(L / 2)) (L / 2))).prod
        (volume.restrict (Ioc (-(L / 2)) (L / 2)))) :=
    (hg.aestronglyMeasurable.comp_snd).mul
      ((((measurable_kernelRep hs0 hs1 hL).comp (measurable_fst.sub measurable_snd))).aestronglyMeasurable)
  rw [integrable_prod_iff' hmeas]
  refine ⟨Eventually.of_forall fun y => ?_, ?_⟩
  · have hKshift : IntegrableOn (fun x => scaledKernel s L (x - y)) (Ioc (-(L / 2)) (L / 2)) := by
      have h := (intervalIntegrable_scaledKernel hs0 hs1 hL (-(L / 2) - y) (L / 2 - y)).comp_sub_right y
      rw [sub_add_cancel, sub_add_cancel] at h
      rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hle]
      exact h
    have hx : Integrable (fun x => kernelRep s L (x - y))
        (volume.restrict (Ioc (-(L / 2)) (L / 2))) :=
      Integrable.congr hKshift (by
        filter_upwards [ae_restrict_of_ae (ae_kernelRep_sub s L y)] with x hx
        exact hx.symm)
    exact hx.const_mul (g y)
  · have hN : ∀ y : ℝ, ∫ x in Ioc (-(L / 2)) (L / 2), ‖g y * kernelRep s L (x - y)‖ =
        ‖g y‖ * ∫ x in Ioc (-(L / 2)) (L / 2), |scaledKernel s L x| := by
      intro y
      simp_rw [norm_mul, Real.norm_eq_abs]
      rw [MeasureTheory.integral_const_mul, setIntegral_abs_kernelRep_sub hL y]
    have hfun : (fun y : ℝ => ∫ x in Ioc (-(L / 2)) (L / 2), ‖g y * kernelRep s L (x - y)‖) =
        fun y => ‖g y‖ * ∫ x in Ioc (-(L / 2)) (L / 2), |scaledKernel s L x| := funext hN
    rw [hfun]
    exact hg.norm.mul_const _

/-- **Fourier coefficient of the transport convolution.** For `g` integrable on `C_L`,
`∫_{C_L} (∫_{C_L} g(y) K_{s,L}(x - y) dy) e_k(x) dx = (∫_{C_L} g e_k)(∫_{C_L} K_{s,L} e_k)`. -/
lemma integral_kernel_charE {s L : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hL : 0 < L) (k : ℤ)
    {g : ℝ → ℝ} (hg : IntegrableOn g (Ioc (-(L / 2)) (L / 2))) :
    ∫ x in Ioc (-(L / 2)) (L / 2),
        ((∫ y in Ioc (-(L / 2)) (L / 2), g y * kernelRep s L (x - y) : ℝ) : ℂ) * charE L k x =
      (∫ y in Ioc (-(L / 2)) (L / 2), (g y : ℂ) * charE L k y) *
        ∫ u in Ioc (-(L / 2)) (L / 2), (scaledKernel s L u : ℂ) * charE L k u := by
  have hle : -(L / 2) ≤ L / 2 := by linarith
  have hEc : Continuous (charE L k) := by
    unfold charE
    fun_prop
  have hF : Function.Periodic (fun u : ℝ => (scaledKernel s L u : ℂ) * charE L k u) L :=
    fun u => by simp only [scaledKernel_add_period hL u, charE_add_period hL.ne' k u]
  have step1 : ∀ x : ℝ, ((∫ y in Ioc (-(L / 2)) (L / 2), g y * kernelRep s L (x - y) : ℝ) : ℂ) *
      charE L k x = ∫ y in Ioc (-(L / 2)) (L / 2), ((g y * kernelRep s L (x - y) : ℝ) : ℂ) *
        charE L k x := by
    intro x
    rw [← integral_complex_ofReal, ← MeasureTheory.integral_mul_const]
  have hint : Integrable (Function.uncurry fun x y =>
      ((g y * kernelRep s L (x - y) : ℝ) : ℂ) * charE L k x)
      ((volume.restrict (Ioc (-(L / 2)) (L / 2))).prod
        (volume.restrict (Ioc (-(L / 2)) (L / 2)))) := by
    have h1 : Integrable (fun p : ℝ × ℝ => ((g p.2 * kernelRep s L (p.1 - p.2) : ℝ) : ℂ))
        ((volume.restrict (Ioc (-(L / 2)) (L / 2))).prod
          (volume.restrict (Ioc (-(L / 2)) (L / 2)))) :=
      (integrable_kernelRep_prod hs0 hs1 hL hg).ofReal
    have hE : AEStronglyMeasurable (fun p : ℝ × ℝ => charE L k p.1)
        ((volume.restrict (Ioc (-(L / 2)) (L / 2))).prod
          (volume.restrict (Ioc (-(L / 2)) (L / 2)))) :=
      (hEc.measurable.comp measurable_fst).aestronglyMeasurable
    exact h1.mul_bdd hE (Eventually.of_forall fun p => (norm_charE L k p.1).le)
  have step3 : ∀ y : ℝ, ∫ x in Ioc (-(L / 2)) (L / 2),
      ((g y * kernelRep s L (x - y) : ℝ) : ℂ) * charE L k x =
      ((g y : ℂ) * charE L k y) *
        ∫ u in Ioc (-(L / 2)) (L / 2), (scaledKernel s L u : ℂ) * charE L k u := by
    intro y
    have ha : ∀ᵐ x ∂(volume.restrict (Ioc (-(L / 2)) (L / 2))),
        ((g y * kernelRep s L (x - y) : ℝ) : ℂ) * charE L k x =
          ((g y : ℂ) * charE L k y) * ((scaledKernel s L (x - y) : ℂ) * charE L k (x - y)) := by
      filter_upwards [ae_restrict_of_ae (ae_kernelRep_sub s L y)] with x hx
      rw [hx, charE_mul L k x y]
      push_cast
      ring
    rw [integral_congr_ae ha, MeasureTheory.integral_const_mul, ← intervalIntegral.integral_of_le hle,
      ← intervalIntegral.integral_of_le hle]
    congr 1
    have hsh := integral_comp_sub_periodic hF y
    simpa only using hsh
  calc ∫ x in Ioc (-(L / 2)) (L / 2),
        ((∫ y in Ioc (-(L / 2)) (L / 2), g y * kernelRep s L (x - y) : ℝ) : ℂ) * charE L k x
      = ∫ x in Ioc (-(L / 2)) (L / 2), ∫ y in Ioc (-(L / 2)) (L / 2),
          ((g y * kernelRep s L (x - y) : ℝ) : ℂ) * charE L k x := by
        simp_rw [step1]
    _ = ∫ y in Ioc (-(L / 2)) (L / 2), ∫ x in Ioc (-(L / 2)) (L / 2),
          ((g y * kernelRep s L (x - y) : ℝ) : ℂ) * charE L k x :=
        integral_integral_swap hint
    _ = ∫ y in Ioc (-(L / 2)) (L / 2), ((g y : ℂ) * charE L k y) *
          ∫ u in Ioc (-(L / 2)) (L / 2), (scaledKernel s L u : ℂ) * charE L k u := by
        simp_rw [step3]
    _ = _ := MeasureTheory.integral_mul_const _ _

end Riesz1
