/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Kernel.TransportScaledMultiplier
public import Riesz1.Frozen.PeriodizedProfile
public import Riesz1.Frozen.LiftL2
public import Riesz1.Frozen.ZeroExtension
public import Riesz1.Frozen.Coeff
public import Riesz1.Frozen.TransportCoeffs
public import Riesz1.Frozen.CompactProfile

/-!
# The transport convolution on a circle and its `L²` bound

For `L > 0` and a real profile `ζ`, the transport convolution is
`Ψ(x) = A_s ∫_{C_L} ζ(y) K_{s,L}(x - y) dy` over the cell `C_L = (-L/2, L/2]`
(`transportConv`). This file proves that `Ψ` is `L`-periodic and that `Ψ ∈ L²(C_L)` when
`ζ ∈ L²(C_L)`, through a weighted Cauchy–Schwarz inequality and Fubini (`transportConv_sq_le`).
-/

public section

open MeasureTheory Set intervalIntegral Filter Topology Complex
open scoped ContDiff Real

namespace Riesz1

/-- The transport convolution `Ψ(x) = A_s ∫_{C_L} ζ(y) K_{s,L}(x - y) dy` on the cell `C_L`. -/
@[expose] noncomputable def transportConv (β s L : ℝ) (ζ : ℝ → ℝ) (x : ℝ) : ℝ :=
  transportConst β s * ∫ y in Ioc (-(L / 2)) (L / 2), ζ y * scaledKernel s L (x - y)

/-- The transport convolution is `L`-periodic. -/
lemma transportConv_periodic (β s : ℝ) {L : ℝ} (hL : 0 < L) (ζ : ℝ → ℝ) :
    Function.Periodic (transportConv β s L ζ) L := by
  intro x
  unfold transportConv
  congr 1
  refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun y => ?_)
  show ζ y * scaledKernel s L (x + L - y) = ζ y * scaledKernel s L (x - y)
  rw [show x + L - y = (x - y) + L by ring, scaledKernel_add_period hL]

/-- **Weighted Cauchy–Schwarz inequality.** For a nonnegative integrable weight `w`,
`(∫ |f| w)² ≤ (∫ w)(∫ f² w)`. -/
lemma sq_integral_abs_mul_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {f w : α → ℝ}
    (hw0 : 0 ≤ᵐ[μ] w) (hw : Integrable w μ) (hfw : Integrable (fun a => f a ^ 2 * w a) μ)
    (hfw' : Integrable (fun a => |f a| * w a) μ) :
    (∫ a, |f a| * w a ∂μ) ^ 2 ≤ (∫ a, w a ∂μ) * ∫ a, f a ^ 2 * w a ∂μ := by
  set I := ∫ a, w a ∂μ with hI
  set J := ∫ a, |f a| * w a ∂μ with hJ
  set Q := ∫ a, f a ^ 2 * w a ∂μ with hQ
  have hI0 : 0 ≤ I := integral_nonneg_of_ae hw0
  rcases hI0.eq_or_lt with h0 | hpos
  · have hw_zero : w =ᵐ[μ] 0 := (integral_eq_zero_iff_of_nonneg_ae hw0 hw).1 h0.symm
    have hJ0 : J = 0 := by
      rw [hJ]
      apply integral_eq_zero_of_ae
      filter_upwards [hw_zero] with a ha
      simp [ha]
    rw [hJ0, ← h0]
    simp
  · set t := J / I with ht
    have htI : t * I = J := div_mul_cancel₀ J hpos.ne'
    have hexp : ∀ a, (|f a| - t) ^ 2 * w a =
        f a ^ 2 * w a - (2 * t) * (|f a| * w a) + t ^ 2 * w a := by
      intro a
      rw [show (|f a| - t) ^ 2 * w a = (|f a| ^ 2 - 2 * t * |f a| + t ^ 2) * w a by ring,
        sq_abs]
      ring
    have hnonneg : 0 ≤ ∫ a, (|f a| - t) ^ 2 * w a ∂μ :=
      integral_nonneg_of_ae (by
        filter_upwards [hw0] with a ha
        exact mul_nonneg (sq_nonneg _) ha)
    have hA : Integrable (fun a => f a ^ 2 * w a - 2 * t * (|f a| * w a)) μ :=
      hfw.sub (hfw'.const_mul (2 * t))
    have hint : ∫ a, (|f a| - t) ^ 2 * w a ∂μ = Q - (2 * t) * J + t ^ 2 * I := by
      simp_rw [hexp]
      rw [MeasureTheory.integral_add hA (hw.const_mul (t ^ 2)),
        MeasureTheory.integral_sub hfw (hfw'.const_mul (2 * t)),
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    rw [hint, ← htI] at hnonneg
    have h1 : t ^ 2 * I ≤ Q := by nlinarith [hnonneg]
    calc J ^ 2 = (t ^ 2 * I) * I := by rw [← htI]; ring
      _ ≤ Q * I := mul_le_mul_of_nonneg_right h1 hpos.le
      _ = I * Q := by ring

/-- The absolute kernel `y ↦ |K_{s,L}(x - y)|` is integrable on the cell, for every `x`. -/
lemma integrableOn_abs_kernelRep_sub {s L : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hL : 0 < L)
    (x : ℝ) : IntegrableOn (fun y => |kernelRep s L (x - y)|) (Ioc (-(L / 2)) (L / 2)) := by
  have hle : -(L / 2) ≤ L / 2 := by linarith
  have h := (intervalIntegrable_scaledKernel hs0 hs1 hL (x - L / 2) (x + L / 2)).comp_sub_left x
  rw [show x - (x + L / 2) = -(L / 2) by ring, show x - (x - L / 2) = L / 2 by ring] at h
  have h1 : IntegrableOn (fun y => |scaledKernel s L (x - y)|) (Ioc (-(L / 2)) (L / 2)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hle).1 h.abs.symm
  refine h1.congr ?_
  filter_upwards [ae_restrict_of_ae (ae_kernelRep_sub' s L x)] with y hy
  rw [hy]

/-- The shift identity for the absolute kernel: `∫_{C_L} |K_{s,L}(x - y)| dy = ∫_{C_L} |K_{s,L}|`. -/
lemma setIntegral_abs_kernelRep_sub_y {s L : ℝ} (hL : 0 < L) (x : ℝ) :
    ∫ y in Ioc (-(L / 2)) (L / 2), |kernelRep s L (x - y)| =
      ∫ u in Ioc (-(L / 2)) (L / 2), |scaledKernel s L u| := by
  have hle : -(L / 2) ≤ L / 2 := by linarith
  have hper : Function.Periodic (fun u => |scaledKernel s L u|) L :=
    fun r => by simp only [scaledKernel_add_period hL r]
  have h1 : ∫ y in Ioc (-(L / 2)) (L / 2), |kernelRep s L (x - y)| =
      ∫ y in Ioc (-(L / 2)) (L / 2), |scaledKernel s L (x - y)| := by
    refine MeasureTheory.setIntegral_congr_ae measurableSet_Ioc ?_
    filter_upwards [ae_kernelRep_sub' s L x] with y hy _
    rw [hy]
  rw [h1, ← intervalIntegral.integral_of_le hle, ← intervalIntegral.integral_of_le hle,
    intervalIntegral.integral_comp_sub_left (fun u => |scaledKernel s L u|) x]
  have h := hper.intervalIntegral_add_eq (x - L / 2) (-(L / 2))
  rw [show -(L / 2) + L = L / 2 by ring] at h
  rw [show x - -(L / 2) = x - L / 2 + L by ring]
  exact h

/-- The product `(x, y) ↦ g(y) |K_{s,L}(x - y)|` is integrable on `C_L × C_L` for `g ≥ 0`
integrable on the cell. -/
lemma integrable_abs_kernelRep_prod {s L : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hL : 0 < L)
    {g : ℝ → ℝ} (hg : IntegrableOn g (Ioc (-(L / 2)) (L / 2))) (hg0 : ∀ y, 0 ≤ g y) :
    Integrable (fun p : ℝ × ℝ => g p.2 * |kernelRep s L (p.1 - p.2)|)
      ((volume.restrict (Ioc (-(L / 2)) (L / 2))).prod
        (volume.restrict (Ioc (-(L / 2)) (L / 2)))) := by
  refine ((integrable_kernelRep_prod hs0 hs1 hL hg).norm).congr (Eventually.of_forall fun p => ?_)
  simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hg0 p.2)]

/-- **Mass identity.** Fubini gives `∫_{C} ∫_{C} ζ(y)² |K(x - y)| dy dx = (∫_C |K|)(∫_C ζ²)`. -/
lemma integral_sq_abs_kernelRep {s L : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hL : 0 < L)
    {ζ : ℝ → ℝ} (hζ2 : IntegrableOn (fun y => ζ y ^ 2) (Ioc (-(L / 2)) (L / 2))) :
    ∫ x in Ioc (-(L / 2)) (L / 2), ∫ y in Ioc (-(L / 2)) (L / 2),
        ζ y ^ 2 * |kernelRep s L (x - y)| =
      (∫ u in Ioc (-(L / 2)) (L / 2), |scaledKernel s L u|) *
        ∫ y in Ioc (-(L / 2)) (L / 2), ζ y ^ 2 := by
  have hint := integrable_abs_kernelRep_prod hs0 hs1 hL hζ2 (fun y => sq_nonneg (ζ y))
  rw [integral_integral_swap (f := fun x y => ζ y ^ 2 * |kernelRep s L (x - y)|) hint]
  have h : ∀ y, ∫ x in Ioc (-(L / 2)) (L / 2), ζ y ^ 2 * |kernelRep s L (x - y)| =
      ζ y ^ 2 * ∫ u in Ioc (-(L / 2)) (L / 2), |scaledKernel s L u| := by
    intro y
    rw [MeasureTheory.integral_const_mul]
    congr 1
    rw [show (fun x => |kernelRep s L (x - y)|) = fun x => |kernelRep s L (x - y)| from rfl]
    exact setIntegral_abs_kernelRep_sub hL y
  simp_rw [h]
  rw [MeasureTheory.integral_mul_const]
  ring

/-- **Weighted Cauchy–Schwarz at a fixed point.** For every `x`, `(∫_{C} ζ(y) K(x-y) dy)² ≤
(∫_C |K|)(∫_C ζ(y)² |K(x-y)| dy)`, whenever the slices are integrable. -/
lemma sq_integral_kernelRep_le {s L : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hL : 0 < L)
    {ζ : ℝ → ℝ} (x : ℝ)
    (hw1 : Integrable (fun y => |ζ y| * |kernelRep s L (x - y)|)
      (volume.restrict (Ioc (-(L / 2)) (L / 2))))
    (hw2 : Integrable (fun y => ζ y ^ 2 * |kernelRep s L (x - y)|)
      (volume.restrict (Ioc (-(L / 2)) (L / 2)))) :
    (∫ y in Ioc (-(L / 2)) (L / 2), ζ y * kernelRep s L (x - y)) ^ 2 ≤
      (∫ u in Ioc (-(L / 2)) (L / 2), |scaledKernel s L u|) *
        ∫ y in Ioc (-(L / 2)) (L / 2), ζ y ^ 2 * |kernelRep s L (x - y)| := by
  have hw : Integrable (fun y => |kernelRep s L (x - y)|)
      (volume.restrict (Ioc (-(L / 2)) (L / 2))) := integrableOn_abs_kernelRep_sub hs0 hs1 hL x
  have habs : |∫ y in Ioc (-(L / 2)) (L / 2), ζ y * kernelRep s L (x - y)| ≤
      ∫ y in Ioc (-(L / 2)) (L / 2), |ζ y| * |kernelRep s L (x - y)| := by
    calc |∫ y in Ioc (-(L / 2)) (L / 2), ζ y * kernelRep s L (x - y)|
        ≤ ∫ y in Ioc (-(L / 2)) (L / 2), |ζ y * kernelRep s L (x - y)| :=
          MeasureTheory.abs_integral_le_integral_abs
      _ = ∫ y in Ioc (-(L / 2)) (L / 2), |ζ y| * |kernelRep s L (x - y)| := by
          simp_rw [abs_mul]
  have hCS := sq_integral_abs_mul_le (μ := volume.restrict (Ioc (-(L / 2)) (L / 2)))
    (f := ζ) (w := fun y => |kernelRep s L (x - y)|)
    (Eventually.of_forall fun y => abs_nonneg _) hw hw2 hw1
  rw [show (∫ y in Ioc (-(L / 2)) (L / 2), ζ y * kernelRep s L (x - y)) ^ 2 =
      |∫ y in Ioc (-(L / 2)) (L / 2), ζ y * kernelRep s L (x - y)| ^ 2 from (sq_abs _).symm]
  have hmass : ∫ y in Ioc (-(L / 2)) (L / 2), |kernelRep s L (x - y)| =
      ∫ u in Ioc (-(L / 2)) (L / 2), |scaledKernel s L u| :=
    setIntegral_abs_kernelRep_sub_y hL x
  calc |∫ y in Ioc (-(L / 2)) (L / 2), ζ y * kernelRep s L (x - y)| ^ 2
      ≤ (∫ y in Ioc (-(L / 2)) (L / 2), |ζ y| * |kernelRep s L (x - y)|) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) habs 2
    _ ≤ (∫ y in Ioc (-(L / 2)) (L / 2), |kernelRep s L (x - y)|) *
        ∫ y in Ioc (-(L / 2)) (L / 2), ζ y ^ 2 * |kernelRep s L (x - y)| := hCS
    _ = _ := by rw [hmass]

/-- The transport convolution with the kernel replaced by its Borel representative. -/
lemma transportConv_eq_kernelRep (β s L : ℝ) (ζ : ℝ → ℝ) (x : ℝ) :
    transportConv β s L ζ x =
      transportConst β s * ∫ y in Ioc (-(L / 2)) (L / 2), ζ y * kernelRep s L (x - y) := by
  unfold transportConv
  congr 1
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [ae_restrict_of_ae (ae_kernelRep_sub' s L x)] with y hy
  rw [hy]

/-- **`L²` membership of the transport convolution on the cell.** For `ζ ∈ L¹ ∩ L²` on the cell
`C_L`, the function `Ψ = transportConv` is square integrable on `C_L`. -/
lemma memLp_transportConv {s L β : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hL : 0 < L) {ζ : ℝ → ℝ}
    (hζ1 : IntegrableOn ζ (Ioc (-(L / 2)) (L / 2)))
    (hζ2 : IntegrableOn (fun y => ζ y ^ 2) (Ioc (-(L / 2)) (L / 2))) :
    MemLp (fun x => (transportConv β s L ζ x : ℂ)) 2
      (volume.restrict (Ioc (-(L / 2)) (L / 2))) := by
  set μ := volume.restrict (Ioc (-(L / 2)) (L / 2)) with hμ
  have hmeas : AEStronglyMeasurable (fun x => transportConv β s L ζ x) μ := by
    have h := (integrable_kernelRep_prod hs0 hs1 hL hζ1).aestronglyMeasurable.integral_prod_right'
    refine (h.const_mul (transportConst β s)).congr (Eventually.of_forall fun x => ?_)
    exact (transportConv_eq_kernelRep β s L ζ x).symm
  have hmeasC : AEStronglyMeasurable (fun x => (transportConv β s L ζ x : ℂ)) μ :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable hmeas
  have hae1 : ∀ᵐ x ∂μ, Integrable (fun y => |ζ y| * |kernelRep s L (x - y)|) μ :=
    (integrable_abs_kernelRep_prod hs0 hs1 hL hζ1.abs (fun y => abs_nonneg _)).prod_right_ae
  have hae2 : ∀ᵐ x ∂μ, Integrable (fun y => ζ y ^ 2 * |kernelRep s L (x - y)|) μ :=
    (integrable_abs_kernelRep_prod hs0 hs1 hL hζ2 (fun y => sq_nonneg _)).prod_right_ae
  have hG := (integrable_abs_kernelRep_prod hs0 hs1 hL hζ2 (fun y => sq_nonneg _)).integral_prod_left
  have hbound : ∀ᵐ x ∂μ, ‖(transportConv β s L ζ x : ℂ)‖ ^ 2 ≤
      (transportConst β s ^ 2 * ∫ u in Ioc (-(L / 2)) (L / 2), |scaledKernel s L u|) *
        ∫ y in Ioc (-(L / 2)) (L / 2), ζ y ^ 2 * |kernelRep s L (x - y)| := by
    filter_upwards [hae1, hae2] with x h1 h2
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, transportConv_eq_kernelRep, mul_pow]
    have hcs := sq_integral_kernelRep_le hs0 hs1 hL x h1 h2
    calc transportConst β s ^ 2 * (∫ y in Ioc (-(L / 2)) (L / 2), ζ y * kernelRep s L (x - y)) ^ 2
        ≤ transportConst β s ^ 2 * ((∫ u in Ioc (-(L / 2)) (L / 2), |scaledKernel s L u|) *
          ∫ y in Ioc (-(L / 2)) (L / 2), ζ y ^ 2 * |kernelRep s L (x - y)|) :=
          mul_le_mul_of_nonneg_left hcs (sq_nonneg _)
      _ = _ := by ring
  rw [memLp_two_iff_integrable_sq_norm hmeasC]
  refine Integrable.mono' (hG.const_mul (transportConst β s ^ 2 *
    ∫ u in Ioc (-(L / 2)) (L / 2), |scaledKernel s L u|)) (hmeasC.norm.pow 2) ?_
  filter_upwards [hbound] with x hx
  rw [Real.norm_of_nonneg (by positivity)]
  exact hx

/-- The central representative lies in `[-L/2, L/2)`. -/
lemma centralRep_mem_Ico (ℓ : Length) (z : Circle ℓ) :
    centralRep ℓ z ∈ Ico (-(ℓ.val / 2)) (ℓ.val / 2) := by
  have : Fact (0 < ℓ.val) := ⟨ℓ.property⟩
  unfold centralRep
  have h := (AddCircle.equivIco ℓ.val (-ℓ.val / 2) z).property
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- The central representative of `↑x` differs from `x` by an integer multiple of the period. -/
lemma centralRep_coe_eq (ℓ : Length) (x : ℝ) :
    ∃ n : ℤ, centralRep ℓ (x : Circle ℓ) = x - n * ℓ.val := by
  have : Fact (0 < ℓ.val) := ⟨ℓ.property⟩
  have hcoe : ((centralRep ℓ (x : Circle ℓ) : ℝ) : AddCircle ℓ.val) = (x : AddCircle ℓ.val) := by
    unfold centralRep
    exact AddCircle.coe_equivIco
  obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.1 (QuotientAddGroup.eq.1 hcoe)
  refine ⟨n, ?_⟩
  rw [zsmul_eq_mul] at hn
  linarith

/-- The transport convolution is invariant under the central representative. -/
lemma transportConv_centralRep (β s : ℝ) (ℓ : Length) (ζ : ℝ → ℝ) (x : ℝ) :
    transportConv β s ℓ.val ζ (centralRep ℓ (x : Circle ℓ)) = transportConv β s ℓ.val ζ x := by
  obtain ⟨n, hn⟩ := centralRep_coe_eq ℓ x
  rw [hn]
  exact (transportConv_periodic β s ℓ.property ζ).sub_int_mul_eq n

/-- The character on the circle: `fourier(-k)(↑x) = e_{L,k}(x)`. -/
lemma fourier_neg_coe_eq_charE (L : ℝ) (k : ℤ) (x : ℝ) :
    fourier (-k) (x : AddCircle L) = charE L k x := by
  rw [fourier_coe_apply]
  unfold charE
  congr 1
  push_cast
  ring

/-- **Fourier coefficient of the transport convolution on the circle.** The coefficient of the
convolution equals `A_s · J_L(k)` times the coefficient of the profile on the circle. -/
lemma coeff_transportConv {s β : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (ℓ : Length) {ζ : ℝ → ℝ}
    (hζ1 : IntegrableOn ζ (Ioc (-(ℓ.val / 2)) (ℓ.val / 2))) (k : ℤ)
    (h1 : Integrable (fun z : Circle ℓ => ((transportConv β s ℓ.val ζ (centralRep ℓ z) : ℝ) : ℂ))
      (arclength ℓ))
    (h2 : Integrable (fun z : Circle ℓ => ((ζ (centralRep ℓ z) : ℝ) : ℂ)) (arclength ℓ)) :
    coeff ℓ ⟨fun z : Circle ℓ => ((transportConv β s ℓ.val ζ (centralRep ℓ z) : ℝ) : ℂ), h1⟩ k =
      ((transportConst β s : ℝ) : ℂ) * kernelCoeff s ℓ.val k *
        coeff ℓ ⟨fun z : Circle ℓ => ((ζ (centralRep ℓ z) : ℝ) : ℂ), h2⟩ k := by
  have hL : 0 < ℓ.val := ℓ.property
  have : Fact (0 < ℓ.val) := ⟨ℓ.property⟩
  have hle : -(ℓ.val / 2) ≤ ℓ.val / 2 := by linarith
  have hLHS : coeff ℓ ⟨fun z : Circle ℓ => ((transportConv β s ℓ.val ζ (centralRep ℓ z) : ℝ) : ℂ),
      h1⟩ k = (1 / ℓ.val : ℝ) • ∫ x in (-(ℓ.val / 2))..(ℓ.val / 2),
        charE ℓ.val k x * ((transportConv β s ℓ.val ζ x : ℝ) : ℂ) := by
    unfold coeff
    rw [fourierCoeff_eq_intervalIntegral _ k (-(ℓ.val / 2)),
      show -(ℓ.val / 2) + ℓ.val = ℓ.val / 2 by ring]
    congr 1
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    show fourier (-k) (x : AddCircle ℓ.val) • ((transportConv β s ℓ.val ζ
      (centralRep ℓ (x : Circle ℓ)) : ℝ) : ℂ) = charE ℓ.val k x *
      ((transportConv β s ℓ.val ζ x : ℝ) : ℂ)
    rw [transportConv_centralRep, smul_eq_mul, fourier_neg_coe_eq_charE, mul_comm]
  have hRHS : coeff ℓ ⟨fun z : Circle ℓ => ((ζ (centralRep ℓ z) : ℝ) : ℂ), h2⟩ k =
      (1 / ℓ.val : ℝ) • ∫ x in (-(ℓ.val / 2))..(ℓ.val / 2), charE ℓ.val k x * ((ζ x : ℝ) : ℂ) := by
    unfold coeff
    rw [fourierCoeff_eq_intervalIntegral _ k (-(ℓ.val / 2)),
      show -(ℓ.val / 2) + ℓ.val = ℓ.val / 2 by ring]
    congr 1
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [(Set.countable_singleton (ℓ.val / 2)).ae_notMem volume] with x hx hxmem
    rw [Set.uIoc_of_le hle] at hxmem
    have hxIco : x ∈ Ico (-(ℓ.val / 2)) (ℓ.val / 2) := ⟨hxmem.1.le, lt_of_le_of_ne hxmem.2 hx⟩
    have hc : centralRep ℓ (x : Circle ℓ) = x := by
      unfold centralRep
      have hmem : x ∈ Set.Ico (-ℓ.val / 2) (-ℓ.val / 2 + ℓ.val) :=
        ⟨by linarith [hxIco.1], by linarith [hxIco.2]⟩
      rw [AddCircle.equivIco_coe_eq hmem]
    show fourier (-k) (x : AddCircle ℓ.val) • ((ζ (centralRep ℓ (x : Circle ℓ)) : ℝ) : ℂ) = charE ℓ.val k x * ((ζ x : ℝ) : ℂ)
    rw [hc, smul_eq_mul, fourier_neg_coe_eq_charE, mul_comm]
  have hΨ : ∀ x : ℝ, ((transportConv β s ℓ.val ζ x : ℝ) : ℂ) =
      ((transportConst β s : ℝ) : ℂ) * ((∫ y in Ioc (-(ℓ.val / 2)) (ℓ.val / 2),
        ζ y * kernelRep s ℓ.val (x - y) : ℝ) : ℂ) := by
    intro x
    rw [transportConv_eq_kernelRep, Complex.ofReal_mul]
  have hX : ∫ x in (-(ℓ.val / 2))..(ℓ.val / 2), charE ℓ.val k x *
      ((transportConv β s ℓ.val ζ x : ℝ) : ℂ) =
      ((transportConst β s : ℝ) : ℂ) * ((∫ y in Ioc (-(ℓ.val / 2)) (ℓ.val / 2),
        (ζ y : ℂ) * charE ℓ.val k y) * kernelCoeff s ℓ.val k) := by
    rw [intervalIntegral.integral_of_le hle]
    have hpt : ∀ x : ℝ, charE ℓ.val k x * ((transportConv β s ℓ.val ζ x : ℝ) : ℂ) =
        ((transportConst β s : ℝ) : ℂ) * (((∫ y in Ioc (-(ℓ.val / 2)) (ℓ.val / 2),
          ζ y * kernelRep s ℓ.val (x - y) : ℝ) : ℂ) * charE ℓ.val k x) := by
      intro x
      rw [hΨ x]
      ring
    simp_rw [hpt]
    rw [MeasureTheory.integral_const_mul,
      integral_kernel_charE hs0 hs1 hL k hζ1]
    rfl
  have hZ : ∫ x in (-(ℓ.val / 2))..(ℓ.val / 2), charE ℓ.val k x * ((ζ x : ℝ) : ℂ) =
      ∫ y in Ioc (-(ℓ.val / 2)) (ℓ.val / 2), (ζ y : ℂ) * charE ℓ.val k y := by
    rw [intervalIntegral.integral_of_le hle]
    refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun y => ?_)
    show charE ℓ.val k y * ((ζ y : ℝ) : ℂ) = ((ζ y : ℝ) : ℂ) * charE ℓ.val k y
    ring
  rw [hLHS, hRHS, hX, hZ, Complex.real_smul, Complex.real_smul]
  ring

/-- **Periodization bridge.** For `L ≥ 1`, the periodized profile equals the central zero extension:
all the translates `n ≠ 0` vanish on the central cell. -/
lemma periodizedProfile_eq_zeroExtension (p : Profile) (ℓ : Length) (hℓ : 1 ≤ ℓ.val)
    (z : Circle ℓ) : periodizedProfile p ℓ z = zeroExtension p (centralRep ℓ z) := by
  have hc := centralRep_mem_Ico ℓ z
  unfold periodizedProfile
  rw [tsum_eq_single (0 : ℤ)]
  · simp
  · intro n hn
    have hL : 0 < ℓ.val := by linarith
    have hnot : ¬ (|centralRep ℓ z + (n : ℝ) * ℓ.val| < 1 / 2) := by
      rw [not_lt]
      rcases lt_or_gt_of_ne hn with h | h
      · have h1 : (n : ℝ) ≤ -1 := by exact_mod_cast (show n ≤ -1 by omega)
        have h2 : (n : ℝ) * ℓ.val ≤ -ℓ.val := by nlinarith
        exact le_abs.2 (Or.inr (by linarith [hc.2]))
      · have h1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
        have h2 : ℓ.val ≤ (n : ℝ) * ℓ.val := by nlinarith
        exact le_abs.2 (Or.inl (by linarith [hc.1]))
    unfold zeroExtension
    rw [ite_eq_right_iff.2 fun h => absurd h hnot]

/-- The periodized profile is the zero extension of the central representative (as functions). -/
lemma coeff_congr_fun {ℓ : Length} (k : ℤ) {f g : Circle ℓ → ℂ} (hf : Integrable f (arclength ℓ))
    (hg : Integrable g (arclength ℓ)) (hfg : f = g) :
    coeff ℓ ⟨f, hf⟩ k = coeff ℓ ⟨g, hg⟩ k := by
  subst hfg
  rfl

/-- **`L²` membership on the circle.** The transport convolution, composed with the central
representative, is square integrable on the observation circle `Circle ℓ`. -/
lemma memLp_transportConv_circle {s β : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (ℓ : Length)
    {ζ : ℝ → ℝ} (hζ1 : IntegrableOn ζ (Ioc (-(ℓ.val / 2)) (ℓ.val / 2)))
    (hζ2 : IntegrableOn (fun y => ζ y ^ 2) (Ioc (-(ℓ.val / 2)) (ℓ.val / 2))) :
    MemLp (fun z : Circle ℓ => ((transportConv β s ℓ.val ζ (centralRep ℓ z) : ℝ) : ℂ))
      2 (arclength ℓ) := by
  have hL : 0 < ℓ.val := ℓ.property
  have hΨ := memLp_transportConv (β := β) hs0 hs1 hL hζ1 hζ2
  have hIco : MemLp (fun x => (transportConv β s ℓ.val ζ x : ℂ)) 2
      (volume.restrict (Ico (-(ℓ.val / 2)) (ℓ.val / 2))) := by
    rw [Measure.restrict_congr_set Ico_ae_eq_Ioc]
    exact hΨ
  have hg : MemLp ((Ico (-(ℓ.val / 2)) (ℓ.val / 2)).indicator
      (fun x => (transportConv β s ℓ.val ζ x : ℂ))) 2 volume :=
    (memLp_indicator_iff_restrict measurableSet_Ico.nullMeasurableSet).2 hIco
  have hlift := liftL2 ℓ _ hg
  have heq : (fun z : Circle ℓ => (Ico (-(ℓ.val / 2)) (ℓ.val / 2)).indicator
      (fun x => (transportConv β s ℓ.val ζ x : ℂ)) (centralRep ℓ z)) =
      fun z : Circle ℓ => ((transportConv β s ℓ.val ζ (centralRep ℓ z) : ℝ) : ℂ) :=
    funext fun z => Set.indicator_of_mem (centralRep_mem_Ico ℓ z) _
  rw [heq] at hlift
  exact hlift

end Riesz1
