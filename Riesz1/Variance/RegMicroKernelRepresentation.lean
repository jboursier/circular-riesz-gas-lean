/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.RegMicroKernelCoeff
public import Riesz1.ToMathlib.CircleFourierDerivative
public import Riesz1.ToMathlib.CircleFourierL1Uniqueness
public import Riesz1.ToMathlib.CircleBasics
public import Riesz1.Kernel.TransportScaledConvolution
public import Riesz1.Frozen.TransportCoeffs
public import Riesz1.Frozen.TransportRegularity
public import Riesz1.Frozen.Coeff
public import Riesz1.Frozen.Arclength
public import Riesz1.Frozen.ComplexL2Integrable

/-!
# The inverse-transport representation of an admissible profile

This file proves the representation step of Lemma 5.3: the profile `ξ`
equals its mean plus the convolution of `P_L` with `q = ψ'`, almost everywhere, where `ψ` is the
transport of `ξ` (`Riesz1.TransportRegularity`). The convolution is
`inverseConv P L q x = ∫_C q(y) P_L(x - y) dy` on the cell `C = (-L/2, L/2]`.

The proof compares Fourier coefficients. The coefficient of `q` comes from integration by parts
(`Riesz1.CircleFourier.integral_deriv_mul_fourier`) and the transport relation. The coefficient of
the convolution is the product of the two cell coefficients (`integral_inverseKernel_charE`), and
the normalization `L^{1-s} |2πk/L|^{1-s} = |2πk|^{1-s}` makes the product equal to `ξ`'s
coefficient. The difference is an integrable function with vanishing coefficients, so it vanishes
almost everywhere by `Riesz1.CircleFourier.ae_eq_zero_of_integrable_fourierCoeff_eq_zero`.
-/

public section

open MeasureTheory Set intervalIntegral Filter Topology Complex
open scoped ContDiff Real

namespace Riesz1

/-- The inverse-transport convolution `x ↦ ∫_C q(y) P_L(x - y) dy` on the cell `C = (-L/2, L/2]`
(Lemma 5.3). -/
@[expose] noncomputable def inverseConv (P : Parameters) (L : ℝ) (q : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y in Ioc (-(L / 2)) (L / 2), q y * inverseKernel P L (x - y)

/-- The convolution is `L`-periodic in `x`, because `P_L` is. -/
lemma inverseConv_periodic (P : Parameters) {L : ℝ} (hL : 0 < L) (q : ℝ → ℝ) :
    Function.Periodic (inverseConv P L q) L := by
  intro x
  unfold inverseConv
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  show q y * inverseKernel P L (x + L - y) = q y * inverseKernel P L (x - y)
  rw [show x + L - y = (x - y) + L by ring, inverseKernel_periodic P hL (x - y)]

/-- For every `x`, the convolution equals the integral against the Borel version `inverseKernelRep`,
which agrees with `inverseKernel` off the countable lattice. -/
lemma inverseConv_eq_rep (P : Parameters) {L : ℝ} (_hL : 0 < L) (q : ℝ → ℝ) (x : ℝ) :
    inverseConv P L q x =
      ∫ y in Ioc (-(L / 2)) (L / 2), q y * inverseKernelRep P L (x - y) := by
  unfold inverseConv
  refine integral_congr_ae ?_
  have hcount : (Set.range fun k : ℤ => x - k * L).Countable := Set.countable_range _
  filter_upwards [ae_restrict_of_ae (hcount.ae_notMem volume)] with y hy
  rw [inverseKernelRep_of_ne fun k h => hy ⟨k, by linarith⟩]

/-- The convolution is integrable on the cell, when the density `q` is. -/
lemma integrableOn_inverseConv (P : Parameters) {L : ℝ} (hL : 0 < L) {q : ℝ → ℝ}
    (hq : IntegrableOn q (Ioc (-(L / 2)) (L / 2))) :
    IntegrableOn (inverseConv P L q) (Ioc (-(L / 2)) (L / 2)) := by
  have h := (integrable_inverseKernelRep_prod P hL hq).integral_prod_left
  refine h.congr ?_
  filter_upwards with x
  exact (inverseConv_eq_rep P hL q x).symm

/-- **Coefficient of the convolution on the cell.** For `q` integrable on the cell,
`∫_C (P_L ∗ q)(x) e_k(x) dx = (∫_C q e_k) (∫_C P_L e_k)`. -/
lemma integral_inverseConv_charE (P : Parameters) {L : ℝ} (hL : 0 < L) (k : ℤ) {q : ℝ → ℝ}
    (hq : IntegrableOn q (Ioc (-(L / 2)) (L / 2))) :
    ∫ x in Ioc (-(L / 2)) (L / 2), (inverseConv P L q x : ℂ) * charE L k x =
      (∫ y in Ioc (-(L / 2)) (L / 2), (q y : ℂ) * charE L k y) *
        ∫ u in Ioc (-(L / 2)) (L / 2), (inverseKernel P L u : ℂ) * charE L k u := by
  have h := integral_inverseKernel_charE P hL k hq
  simp_rw [inverseConv_eq_rep P hL q]
  exact h

/-- **Coefficient of the derivative on the cell.** For `ψ` continuous on the circle of length `L`,
differentiable off a countable set with integrable derivative on a period, and every integer `k`,
the cell integral of `ψ'(x) e_k(x)` equals `L · (2πik/L) · ψ̂(k)`. -/
lemma integral_deriv_charE (L : Length) [Fact (0 < L.val)] (ψ : Circle L → ℝ)
    (hψc : Continuous ψ) {S : Set ℝ}
    (hS : S.Countable)
    (hψd : ∀ x : ℝ, x ∉ S → DifferentiableAt ℝ (fun t : ℝ => ψ (t : Circle L)) x)
    (hψi : IntervalIntegrable (deriv (fun t : ℝ => ψ (t : Circle L))) volume 0 L.val) (k : ℤ) :
    ∫ x in Ioc (-(L.val / 2)) (L.val / 2),
        ((deriv (fun t : ℝ => ψ (t : Circle L)) x : ℝ) : ℂ) * charE L.val k x =
      (L.val : ℂ) * (2 * Real.pi * Complex.I * (k : ℂ) / L.val) *
        fourierCoeff (fun z : Circle L => (ψ z : ℂ)) k := by
  have hT : 0 < L.val := L.property
  have hle : -(L.val / 2) ≤ L.val / 2 := by linarith
  have hper : Function.Periodic (fun t : ℝ => ψ (t : Circle L)) L.val := fun t => by
    show ψ ((t + L.val : ℝ) : Circle L) = ψ (t : Circle L)
    rw [AddCircle.coe_add_period]
  have hdper := deriv_periodic_of hper
  have hGper : Function.Periodic
      (fun x : ℝ => ((deriv (fun t : ℝ => ψ (t : Circle L)) x : ℝ) : ℂ) * charE L.val k x)
      L.val := fun t => by
    simp only [hdper t, charE_add_period hT.ne' k t]
  have hshift : ∫ x in Ioc (-(L.val / 2)) (L.val / 2),
      ((deriv (fun t : ℝ => ψ (t : Circle L)) x : ℝ) : ℂ) * charE L.val k x =
      ∫ x in (0 : ℝ)..L.val,
        ((deriv (fun t : ℝ => ψ (t : Circle L)) x : ℝ) : ℂ) * charE L.val k x := by
    rw [← intervalIntegral.integral_of_le hle]
    have h := hGper.intervalIntegral_add_eq (-(L.val / 2)) 0
    rw [show -(L.val / 2) + L.val = L.val / 2 by ring, show (0 : ℝ) + L.val = L.val by ring] at h
    exact h
  have hcharE : ∀ x : ℝ, charE L.val k x = fourier (-k) (x : AddCircle L.val) :=
    fun x => (fourier_neg_coe_eq_charE L.val k x).symm
  rw [hshift]
  simp_rw [hcharE]
  exact CircleFourier.integral_deriv_mul_fourier (T := L.val) hψc hS hψd hψi k

/-- **Normalization of the kernel against the transport multiplier.** For `0 < s < 1`, `L > 0` and
`k ≠ 0`, the product `L · L^{-s} · |2πk/L|^{1-s} · (2π|k|)^{s-1}` equals one. -/
lemma rpow_normalization {s L : ℝ} (_hs0 : 0 < s) (_hs1 : s < 1) (hL : 0 < L) {k : ℤ}
    (hk : k ≠ 0) :
    L * L ^ (-s) * |2 * Real.pi * k / L| ^ (1 - s) * (2 * Real.pi * |(k : ℝ)|) ^ (s - 1) = 1 := by
  have hk' : (0 : ℝ) < |(k : ℝ)| := abs_pos.2 (Int.cast_ne_zero.2 hk)
  have hpos : 0 < 2 * Real.pi * |(k : ℝ)| := by positivity
  have h1 : L ^ (1 - s) = L * L ^ (-s) := by
    rw [show (1 - s) = 1 + -s by ring, Real.rpow_add hL, Real.rpow_one]
  have hsub : |2 * Real.pi * k / L| = 2 * Real.pi * |(k : ℝ)| / L := by
    rw [abs_div, abs_mul, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hL]
    norm_num
  have h2 : L ^ (1 - s) * |2 * Real.pi * k / L| ^ (1 - s) = (2 * Real.pi * |(k : ℝ)|) ^ (1 - s) := by
    rw [← Real.mul_rpow hL.le (by positivity), hsub]
    congr 1
    field_simp
  have h3 : (2 * Real.pi * |(k : ℝ)|) ^ (1 - s) * (2 * Real.pi * |(k : ℝ)|) ^ (s - 1) = 1 := by
    rw [← Real.rpow_add hpos, show (1 - s) + (s - 1) = (0 : ℝ) by ring, Real.rpow_zero]
  calc L * L ^ (-s) * |2 * Real.pi * k / L| ^ (1 - s) * (2 * Real.pi * |(k : ℝ)|) ^ (s - 1)
      = (L ^ (1 - s) * |2 * Real.pi * k / L| ^ (1 - s)) * (2 * Real.pi * |(k : ℝ)|) ^ (s - 1) := by
        rw [h1]
    _ = 1 := by rw [h2, h3]

/-- **Transport coefficient of the derivative.** For `ψ` continuous on the circle with the
transport relation `ψ̂(k) = transportCoeffs P L f k`, the cell integral of `ψ'(x) e_k(x)` equals
`L · (2πik/L) · transportCoeffs P L f k` for every integer `k`. -/
lemma integral_deriv_charE_transport (P : Parameters) (L : Length) [Fact (0 < L.val)]
    (f : {f : Circle L → ℝ // MemLp (fun x => (f x : ℂ)) 2 (arclength L)})
    (ψ : {ψ : Circle L → ℝ // MemLp (fun x => (ψ x : ℂ)) 2 (arclength L)})
    (hψc : Continuous ψ.val) {S : Set ℝ} (hS : S.Countable)
    (hψd : ∀ x : ℝ, x ∉ S → DifferentiableAt ℝ (fun t : ℝ => ψ.val (t : Circle L)) x)
    (hψi : IntervalIntegrable (deriv (fun t : ℝ => ψ.val (t : Circle L))) volume 0 L.val)
    (hψ : ∀ k : ℤ, coeff L ⟨(fun x => (ψ.val x : ℂ)), complexL2Integrable L _ ψ.property⟩ k =
      transportCoeffs P L f k) (k : ℤ) :
    ∫ x in Ioc (-(L.val / 2)) (L.val / 2),
        ((deriv (fun t : ℝ => ψ.val (t : Circle L)) x : ℝ) : ℂ) * charE L.val k x =
      (L.val : ℂ) * (2 * Real.pi * Complex.I * (k : ℂ) / L.val) * transportCoeffs P L f k := by
  rw [integral_deriv_charE L ψ.val hψc hS hψd hψi k, ← hψ k]
  rfl

/-- **Product of the two cell coefficients.** For `k ≠ 0`, the normalized coefficient
`(1/L) (L · 2πik/L · T)(L · (-2βL^{-s}) · ĝ_s(k))` of the convolution equals `F`, when `T` is the
transport coefficient `-|2πk/L|^{1-s}/(2βc · 2πik/L) · F` and `ĝ_s(k) = c (2π|k|)^{s-1}`. -/
lemma convolution_coefficient_algebra {s L β c : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hL : 0 < L)
    (hβ : 0 < β) (hc : 0 < c) {k : ℤ} (hk : k ≠ 0) (F : ℂ) :
    (1 / (L : ℂ)) * (((L : ℂ) * (2 * Real.pi * Complex.I * (k : ℂ) / L) *
          (-((|2 * Real.pi * k / L| ^ (1 - s) : ℝ) : ℂ) /
            (((2 * β * c : ℝ) : ℂ) * (2 * Real.pi * Complex.I * (k : ℂ) / L)) * F)) * ((L : ℂ) * ((-(2 * β * L ^ (-s)) : ℝ) : ℂ) *
        ((c * (2 * Real.pi * |(k : ℝ)|) ^ (s - 1) : ℝ) : ℂ))) = F := by
  have hnorm := rpow_normalization (L := L) hs0 hs1 hL hk
  have key : (L : ℂ) * ((L ^ (-s) : ℝ) : ℂ) * ((|2 * Real.pi * k / L| ^ (1 - s) : ℝ) : ℂ) *
      (((2 * Real.pi * |(k : ℝ)|) ^ (s - 1) : ℝ) : ℂ) = 1 := by
    have := congrArg (fun x : ℝ => (x : ℂ)) hnorm
    push_cast at this ⊢
    exact this
  have hLc : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have hkc : (k : ℂ) ≠ 0 := by exact_mod_cast hk
  have hB : ((2 * β * c : ℝ) : ℂ) ≠ 0 := by
    have : (2 * β * c : ℝ) ≠ 0 := by positivity
    exact_mod_cast this
  have hM : 2 * Real.pi * Complex.I * (k : ℂ) / L ≠ 0 := by
    have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    refine div_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero this) Complex.I_ne_zero)
      hkc) hLc
  have hβc : (β : ℂ) ≠ 0 := by exact_mod_cast hβ.ne'
  have hcc : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  push_cast at key hB ⊢
  field_simp
  linear_combination F * key

/-- The cell integral of `q` against `e_k` for the derivative `q = ψ'`, with `ψ` the lift of a circle
function, and the convolution coefficient. Shared hypotheses of the coefficient lemmas below. -/
lemma integrableOn_deriv_cell (L : Length) (ψ : Circle L → ℝ)
    (hψi : IntervalIntegrable (deriv (fun t : ℝ => ψ (t : Circle L))) volume 0 L.val) :
    IntegrableOn (deriv (fun t : ℝ => ψ (t : Circle L)))
      (Ioc (-(L.val / 2)) (L.val / 2)) := by
  have hT : L.val ≠ 0 := L.property.ne'
  have hper : Function.Periodic (fun t : ℝ => ψ (t : Circle L)) L.val := fun t => by
    show ψ ((t + L.val : ℝ) : Circle L) = ψ (t : Circle L)
    rw [AddCircle.coe_add_period]
  have h := (deriv_periodic_of hper).intervalIntegrable (t := 0) hT (by simpa using hψi)
    (-(L.val / 2)) (L.val / 2)
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith [L.property])).1 h

/-- **Convolution coefficient for `k ≠ 0`.** The normalized coefficient of `P_L ∗ q` is the
coefficient of `ψ`'s profile `f`, under the transport relation. -/
lemma inverseConv_coeff_ne_zero (P : Parameters) (L : Length) [Fact (0 < L.val)]
    (f : {f : Circle L → ℝ // MemLp (fun x => (f x : ℂ)) 2 (arclength L)})
    (ψ : {ψ : Circle L → ℝ // MemLp (fun x => (ψ x : ℂ)) 2 (arclength L)})
    (hψc : Continuous ψ.val) {S : Set ℝ} (hS : S.Countable)
    (hψd : ∀ x : ℝ, x ∉ S → DifferentiableAt ℝ (fun t : ℝ => ψ.val (t : Circle L)) x)
    (hψi : IntervalIntegrable (deriv (fun t : ℝ => ψ.val (t : Circle L))) volume 0 L.val)
    (hψ : ∀ k : ℤ, coeff L ⟨(fun x => (ψ.val x : ℂ)), complexL2Integrable L _ ψ.property⟩ k =
      transportCoeffs P L f k) {k : ℤ} (hk : k ≠ 0) :
    (1 / (L.val : ℂ)) * ∫ x in Ioc (-(L.val / 2)) (L.val / 2),
        (inverseConv P L.val (deriv (fun t : ℝ => ψ.val (t : Circle L))) x : ℂ) * charE L.val k x =
      fourierCoeff (fun z : Circle L => (f.val z : ℂ)) k := by
  have hL : 0 < L.val := L.property
  have hq := integrableOn_deriv_cell L ψ.val hψi
  rw [integral_inverseConv_charE P hL k hq,
    integral_deriv_charE_transport P L f ψ hψc hS hψd hψi hψ k,
    integral_inverseKernel_charE_cell P hL k, (fundamental (parametersExponent P)).1 k]
  simp only [hk, ↓reduceIte]
  have hcoeff : coeff L ⟨(fun x => (f.val x : ℂ)), complexL2Integrable L _ f.property⟩ k =
      fourierCoeff (fun z : Circle L => (f.val z : ℂ)) k := rfl
  unfold transportCoeffs
  simp only [hk, ↓reduceIte]
  rw [← hcoeff]
  have hpe : (parametersExponent P).val = P.val.2 := rfl
  rw [hpe]
  exact convolution_coefficient_algebra (P.property.2.1) (P.property.2.2) hL P.property.1
    (rieszConstant_parametersExponent_pos P) hk _

/-- **Convolution coefficient for `k = 0`.** The mean of `P_L` vanishes, so `P_L ∗ q` has zero
mean. -/
lemma inverseConv_coeff_zero (P : Parameters) (L : Length) [Fact (0 < L.val)]
    (ψ : {ψ : Circle L → ℝ // MemLp (fun x => (ψ x : ℂ)) 2 (arclength L)})
    (hψi : IntervalIntegrable (deriv (fun t : ℝ => ψ.val (t : Circle L))) volume 0 L.val) :
    (1 / (L.val : ℂ)) * ∫ x in Ioc (-(L.val / 2)) (L.val / 2),
        (inverseConv P L.val (deriv (fun t : ℝ => ψ.val (t : Circle L))) x : ℂ) *
          charE L.val 0 x = 0 := by
  have hL : 0 < L.val := L.property
  have hq := integrableOn_deriv_cell L ψ.val hψi
  rw [integral_inverseConv_charE P hL 0 hq, integral_inverseKernel_charE_cell P hL 0,
    (fundamental (parametersExponent P)).1 0]
  simp

/-- The periodic lift of the convolution `P_L ∗ q` to the circle `Circle L`. -/
@[expose] noncomputable def inverseConvCircle (P : Parameters) (L : Length) (q : ℝ → ℝ) :
    Circle L → ℝ :=
  (inverseConv_periodic P L.property q).lift

/-- The lift of the convolution to the circle agrees with the convolution on the line. -/
lemma inverseConvCircle_coe (P : Parameters) (L : Length) (q : ℝ → ℝ) (x : ℝ) :
    inverseConvCircle P L q (x : Circle L) = inverseConv P L.val q x :=
  Function.Periodic.lift_coe _ x

/-- The convolution `P_L ∗ q` is Borel measurable when `q` is. -/
lemma measurable_inverseConv (P : Parameters) {L : ℝ} (hL : 0 < L) {q : ℝ → ℝ}
    (hq : Measurable q) : Measurable (inverseConv P L q) := by
  have hfun : inverseConv P L q = fun x => ∫ y in Ioc (-(L / 2)) (L / 2),
      q y * inverseKernelRep P L (x - y) :=
    funext (inverseConv_eq_rep P hL q)
  rw [hfun]
  have hF : Measurable (fun p : ℝ × ℝ => q p.2 * inverseKernelRep P L (p.1 - p.2)) :=
    (hq.comp measurable_snd).mul ((measurable_inverseKernelRep P hL).comp
      (measurable_fst.sub measurable_snd))
  exact (hF.stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Ioc (-(L / 2)) (L / 2)))).measurable

/-- The periodic lift of the convolution is measurable on the circle. -/
lemma measurable_inverseConvCircle (P : Parameters) (L : Length) [Fact (0 < L.val)] {q : ℝ → ℝ}
    (hq : Measurable q) :
    Measurable (inverseConvCircle P L q) := by
  have hL := L.property
  apply (MeasurableEquiv.measurable_comp_iff
    (AddCircle.measurableEquivIoc L.val (-(L.val / 2))).symm).1
  have hfun : (inverseConvCircle P L q) ∘
      ((AddCircle.measurableEquivIoc L.val (-(L.val / 2))).symm) =
      fun x : Ioc (-(L.val / 2)) (-(L.val / 2) + L.val) => inverseConv P L.val q (x : ℝ) :=
    funext fun x => inverseConvCircle_coe P L q x
  rw [hfun]
  exact (measurable_inverseConv P hL hq).comp measurable_subtype_coe

/-- The lift of the convolution is integrable on the circle when the density is integrable on the
cell. -/
lemma integrable_inverseConvCircle (P : Parameters) (L : Length) [Fact (0 < L.val)] {q : ℝ → ℝ}
    (hq : Measurable q)
    (hqi : IntegrableOn q (Ioc (-(L.val / 2)) (L.val / 2))) :
    Integrable (inverseConvCircle P L q) (arclength L) := by
  have hL := L.property
  have hcomp : Integrable (inverseConvCircle P L q ∘ ((↑) : ℝ → Circle L))
      (volume.restrict (Ioc (-(L.val / 2)) (-(L.val / 2) + L.val))) := by
    rw [show -(L.val / 2) + L.val = L.val / 2 by ring]
    have hfun : (inverseConvCircle P L q ∘ ((↑) : ℝ → Circle L)) = inverseConv P L.val q :=
      funext fun x => inverseConvCircle_coe P L q x
    rw [hfun]
    exact integrableOn_inverseConv P hL hqi
  exact ((AddCircle.measurePreserving_mk L.val (-(L.val / 2))).integrable_comp
    (measurable_inverseConvCircle P L hq).aestronglyMeasurable).mp hcomp

/-- **Fourier coefficient of the periodic convolution.** The normalized coefficient of the lift of
`P_L ∗ q` is the normalized cell integral of `P_L ∗ q` against `e_k`. -/
lemma fourierCoeff_inverseConvCircle (P : Parameters) (L : Length) [Fact (0 < L.val)] (q : ℝ → ℝ)
    (k : ℤ) :
    fourierCoeff (fun z : Circle L => (inverseConvCircle P L q z : ℂ)) k =
      (1 / (L.val : ℂ)) * ∫ x in Ioc (-(L.val / 2)) (L.val / 2),
        (inverseConv P L.val q x : ℂ) * charE L.val k x := by
  have hL : 0 < L.val := L.property
  have hle : -(L.val / 2) ≤ L.val / 2 := by linarith
  rw [fourierCoeff_eq_intervalIntegral _ k (-(L.val / 2)),
    show -(L.val / 2) + L.val = L.val / 2 by ring]
  rw [intervalIntegral.integral_congr (g := fun x : ℝ =>
      (inverseConv P L.val q x : ℂ) * charE L.val k x) (fun x _ => ?_),
    intervalIntegral.integral_of_le hle, Complex.real_smul]
  · push_cast
    ring
  · show fourier (-k) (x : AddCircle L.val) • (inverseConvCircle P L q (x : Circle L) : ℂ) =
      (inverseConv P L.val q x : ℂ) * charE L.val k x
    rw [fourier_neg_coe_eq_charE, inverseConvCircle_coe, smul_eq_mul, mul_comm]

/-- **Fourier coefficient of a difference.** -/
lemma fourierCoeff_sub_eq {T : ℝ} [Fact (0 < T)] {f g : AddCircle T → ℂ}
    (hf : Integrable f AddCircle.haarAddCircle) (hg : Integrable g AddCircle.haarAddCircle)
    (k : ℤ) : fourierCoeff (fun x => f x - g x) k = fourierCoeff f k - fourierCoeff g k := by
  unfold fourierCoeff
  simp only [smul_sub]
  exact integral_sub (hf.fourier_smul _) (hg.fourier_smul _)

/-- **Fourier coefficient of a constant.** -/
lemma fourierCoeff_const_eq {T : ℝ} [Fact (0 < T)] (c : ℂ) (k : ℤ) :
    fourierCoeff (fun _ : AddCircle T => c) k = if k = 0 then c else 0 := by
  have h : (fun _ : AddCircle T => c) = fun x => c * fourier (0 : ℤ) x := by
    funext x
    simp
  rw [h, fourierCoeff.const_mul, fourierCoeff_fourier]
  by_cases hk : k = 0
  · subst hk
    simp
  · simp [hk]

/-- **Mean of the profile as a Fourier coefficient.** The zeroth normalized coefficient is the
mean over the cell. -/
lemma fourierCoeff_zero_eq_mean (L : Length) [Fact (0 < L.val)]
    (f : Circle L → ℝ) :
    fourierCoeff (fun z : Circle L => (f z : ℂ)) 0 =
      ((((∫ y in Ioc (-(L.val / 2)) (L.val / 2), f (y : Circle L)) / L.val : ℝ)) : ℂ) := by
  have hL : 0 < L.val := L.property
  have hle : -(L.val / 2) ≤ L.val / 2 := by linarith
  rw [fourierCoeff_eq_intervalIntegral _ 0 (-(L.val / 2)),
    show -(L.val / 2) + L.val = L.val / 2 by ring]
  rw [intervalIntegral.integral_congr (g := fun x : ℝ => (f (x : Circle L) : ℂ)) (fun x _ => ?_),
    intervalIntegral.integral_of_le hle, integral_complex_ofReal, Complex.real_smul]
  · push_cast
    ring
  · show fourier (-(0 : ℤ)) (x : AddCircle L.val) • (f (x : Circle L) : ℂ) = (f (x : Circle L) : ℂ)
    simp

/-- Integrability with respect to the circle volume gives integrability with respect to the
normalized Haar measure, because the two measures differ by a finite positive constant. -/
lemma integrable_haar_of_volume {T : ℝ} [Fact (0 < T)] {g : AddCircle T → ℂ}
    (hg : Integrable g volume) : Integrable g AddCircle.haarAddCircle := by
  rw [AddCircle.volume_eq_smul_haarAddCircle] at hg
  exact (integrable_smul_measure (ENNReal.ofReal_pos.2 (Fact.out)).ne'
    ENNReal.ofReal_ne_top).1 hg

/-- **Inverse-transport representation of the profile.** Let `ψ` be the transport of the profile
`f`, with `ψ` continuous, differentiable off a countable set, and with integrable derivative on a
period. Then for almost every point `x` of the cell `(-L/2, L/2]`, the profile at `x` equals its
mean over the cell plus the convolution of `P_L` with `ψ'`. -/
theorem inverse_representation (P : Parameters) (L : Length) [Fact (0 < L.val)]
    (f : {f : Circle L → ℝ // MemLp (fun x => (f x : ℂ)) 2 (arclength L)})
    (ψ : {ψ : Circle L → ℝ // MemLp (fun x => (ψ x : ℂ)) 2 (arclength L)})
    (hψc : Continuous ψ.val) {S : Set ℝ} (hS : S.Countable)
    (hψd : ∀ x : ℝ, x ∉ S → DifferentiableAt ℝ (fun t : ℝ => ψ.val (t : Circle L)) x)
    (hψi : IntervalIntegrable (deriv (fun t : ℝ => ψ.val (t : Circle L))) volume 0 L.val)
    (hψ : ∀ k : ℤ, coeff L ⟨(fun x => (ψ.val x : ℂ)), complexL2Integrable L _ ψ.property⟩ k =
      transportCoeffs P L f k) :
    ∀ᵐ x : ℝ ∂(volume.restrict (Ioc (-(L.val / 2)) (L.val / 2))),
      f.val (x : Circle L) = (∫ y in Ioc (-(L.val / 2)) (L.val / 2), f.val (y : Circle L)) / L.val +
        inverseConv P L.val (deriv (fun t : ℝ => ψ.val (t : Circle L))) x := by
  have : IsFiniteMeasure (arclength L) := by unfold arclength; infer_instance
  have hL : 0 < L.val := L.property
  have hqm : Measurable (deriv (fun t : ℝ => ψ.val (t : Circle L))) := measurable_deriv _
  have hqi := integrableOn_deriv_cell L ψ.val hψi
  have hfi : Integrable f.val (arclength L) := (complexL2Integrable L _ f.property).re
  have hconvi := integrable_inverseConvCircle P L hqm hqi
  set m : ℝ := (∫ y in Ioc (-(L.val / 2)) (L.val / 2), f.val (y : Circle L)) / L.val with hm
  set H : Circle L → ℝ := fun z => f.val z - m - inverseConvCircle P L
    (deriv (fun t : ℝ => ψ.val (t : Circle L))) z with hH
  have hHi : Integrable H (arclength L) := (hfi.sub (integrable_const _)).sub hconvi
  have hfc : Integrable (fun z : Circle L => (f.val z : ℂ)) AddCircle.haarAddCircle :=
    integrable_haar_of_volume (hfi.ofReal)
  have hconst : Integrable (fun _ : Circle L => (m : ℂ)) AddCircle.haarAddCircle :=
    integrable_const _
  have hconvC : Integrable (fun z : Circle L => (inverseConvCircle P L
      (deriv (fun t : ℝ => ψ.val (t : Circle L))) z : ℂ)) AddCircle.haarAddCircle :=
    integrable_haar_of_volume (hconvi.ofReal)
  have hcoef : ∀ k : ℤ, fourierCoeff (fun z : Circle L => (H z : ℂ)) k = 0 := by
    intro k
    have hsplit : (fun z : Circle L => (H z : ℂ)) =
        fun z => ((f.val z : ℂ) - (m : ℂ)) - (inverseConvCircle P L
          (deriv (fun t : ℝ => ψ.val (t : Circle L))) z : ℂ) := by
      funext z
      simp only [hH]
      push_cast
      ring
    have hA : Integrable (fun z : Circle L => (f.val z : ℂ) - (m : ℂ)) AddCircle.haarAddCircle :=
      hfc.sub hconst
    rw [hsplit, fourierCoeff_sub_eq hA hconvC k, fourierCoeff_sub_eq hfc hconst k,
      fourierCoeff_const_eq, fourierCoeff_inverseConvCircle]
    by_cases hk : k = 0
    · subst hk
      rw [fourierCoeff_zero_eq_mean L f.val, inverseConv_coeff_zero P L ψ hψi, hm]
      simp only [↓reduceIte]
      push_cast
      ring
    · simp only [hk, ↓reduceIte]
      rw [inverseConv_coeff_ne_zero P L f ψ hψc hS hψd hψi hψ hk]
      simp
  have hae : H =ᵐ[volume] 0 :=
    CircleFourier.ae_eq_zero_of_integrable_fourierCoeff_eq_zero hHi hcoef
  have hcell := (AddCircle.measurePreserving_mk L.val (-(L.val / 2))).quasiMeasurePreserving.ae_eq_comp
    hae
  rw [show -(L.val / 2) + L.val = L.val / 2 by ring] at hcell
  filter_upwards [hcell] with x hx
  have hx' : H (x : Circle L) = 0 := hx
  simp only [hH, inverseConvCircle_coe] at hx'
  linarith

end Riesz1

end
