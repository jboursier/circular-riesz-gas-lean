/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Kernel.TransportScaledSmooth
public import Riesz1.Frozen.ZeroExtensionL2
public import Riesz1.Frozen.PeriodizedProfileL2
public import Riesz1.Frozen.CompactProfile
public import Riesz1.Frozen.TransportCoeffs

/-!
# The scaled transport kernel: the collected statement

The main theorem `Riesz1.transport_kernel_scaled` collects the claims
for the scaled kernel `K_{s,L}` and for the transport of a compact
profile on the observation circle.
-/

public section

open MeasureTheory Set intervalIntegral Filter Topology
open scoped ContDiff Real

namespace Riesz1

/-- The kernel integral `J_L(0)` vanishes: the kernel has mean zero over a period. -/
lemma kernelCoeff_zero (s L : ℝ) (hL : 0 < L) : kernelCoeff s L 0 = 0 := by
  have hle : -(L / 2) ≤ L / 2 := by linarith
  unfold kernelCoeff
  have h1 : ∀ u : ℝ, (scaledKernel s L u : ℂ) * charE L 0 u = ((scaledKernel s L u : ℝ) : ℂ) := by
    intro u
    unfold charE
    simp
  simp_rw [h1]
  rw [← intervalIntegral.integral_of_le hle, intervalIntegral.integral_ofReal,
    integral_scaledKernel_period hL]
  simp

/-- The transport coefficient for `k ≠ 0` is the multiplier times the Fourier coefficient. -/
lemma transportCoeffs_eq_mult (P : Parameters) (ℓ : Length)
    (f : {f : Circle ℓ → ℝ // MemLp (fun x => (f x : ℂ)) 2 (arclength ℓ)}) {k : ℤ} (hk : k ≠ 0) :
    transportCoeffs P ℓ f k = transportMult P ℓ.val k * coeff ℓ ⟨fun x => (f.val x : ℂ),
      complexL2Integrable ℓ _ f.property⟩ k := by
  unfold transportCoeffs transportMult
  simp only [hk, ite_false]

/-- The zero extension of a compact profile is square integrable on every cell. -/
lemma zeroExtension_integrableOn (p : Profile) (ℓ : Length) :
    IntegrableOn (zeroExtension p) (Ioc (-(ℓ.val / 2)) (ℓ.val / 2)) ∧
      IntegrableOn (fun y => zeroExtension p y ^ 2) (Ioc (-(ℓ.val / 2)) (ℓ.val / 2)) := by
  have hL2 : MemLp (fun x => (zeroExtension p x : ℂ)) 2
      (volume.restrict (Ioc (-(ℓ.val / 2)) (ℓ.val / 2))) := (zeroExtensionL2 p).restrict _
  have hint : Integrable (fun x => (zeroExtension p x : ℂ))
      (volume.restrict (Ioc (-(ℓ.val / 2)) (ℓ.val / 2))) := hL2.integrable (by norm_num)
  constructor
  · refine hint.re.congr (Eventually.of_forall fun y => ?_)
    simp
  · have hsq := (memLp_two_iff_integrable_sq_norm hL2.aestronglyMeasurable).1 hL2
    refine hsq.congr (Eventually.of_forall fun y => ?_)
    show ‖((zeroExtension p y : ℝ) : ℂ)‖ ^ 2 = zeroExtension p y ^ 2
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- The arclength measure of a circle of positive length is finite. -/
instance isFiniteMeasure_arclength (ℓ : Length) : IsFiniteMeasure (arclength ℓ) := by
  have : Fact (0 < ℓ.val) := ⟨ℓ.property⟩
  unfold arclength
  infer_instance

/-- If `y ∉ (-ρ, ρ]` then `ρ ≤ |y|`. -/
lemma le_abs_of_not_mem_Ioc {ρ y : ℝ} (hy : y ∉ Ioc (-ρ) ρ) : ρ ≤ |y| := by
  rcases le_or_gt y (-ρ) with h1 | h1
  · exact le_abs.2 (Or.inr (by linarith))
  · have h2 : ρ < y := by
      by_contra h2
      exact hy ⟨h1, not_lt.1 h2⟩
    exact le_abs.2 (Or.inl h2.le)

/-- **Transport kernel on circles of arbitrary length.**

Let `P = (β, s)` be the model parameters, `p` a real `L²` profile, and `ell ∈ (0, 1]` a scale, with observation length `L = 1/ell ≥ 1`. Write
`ζ = zeroExtension p` and `Ψ = transportConv β s L ζ` for the transport convolution on the cell.
The compact-support hypothesis of `CompactProfile p` enters through the admissible margins `ρ`
in claim (S).

The statement collects:

* **(K)** for every `0 < s < 1` and `L ≥ 1`: the scaled kernel `K_{s,L}` is interval integrable,
  has mean zero over a period, is `L`-periodic and `C^∞` off `L ℤ`, and its symmetric sums converge
  locally uniformly off `L ℤ` and in `L¹` over a period.
* **(D)** for every `m ≥ 1` a constant `C_{s,m} > 0`, independent of `L`, with
  `|K^{(m)}_{s,L}(r)| ≤ C_{s,m} dist(r, Lℤ)^{s-1-m}` off the lattice.
* **(T)** the transport of the periodized profile is square integrable on the observation circle,
  and its Fourier coefficients are the transport coefficients `transportCoeffs`.
* **(S)** for every admissible margin `ρ` (`0 < ρ < 1/2`, `ζ = 0` a.e. on `|x| ≥ ρ`), `Ψ` is
  `C^∞` off `[-ρ, ρ] + Lℤ`. For every `m ≥ 1` there is `C_{s,m,β} > 0`, independent of `L`, `ζ`
  and `ρ`, with `|Ψ^{(m)}(x)| ≤ C_{s,m,β} ‖ζ‖₁ |x|^{s-1-m}` for `1 ≤ |x| ≤ L/2`.

The constants `C_{s,m}` and `C_{s,m,β}` are existentially quantified before the parameters they do not
depend on. The claims hold for every admissible `ρ`. -/
theorem transport_kernel_scaled (P : Parameters) (p : Profile) (ell : Scale) :
    -- (K) the scaled kernel on every circle of length `L ≥ 1`
    (∀ s : ℝ, 0 < s → s < 1 → ∀ L : ℝ, 1 ≤ L →
      (∀ a b : ℝ, IntervalIntegrable (scaledKernel s L) volume a b) ∧
      (∫ r in (-(L / 2))..(L / 2), scaledKernel s L r = 0) ∧
      Function.Periodic (scaledKernel s L) L ∧
      (∀ r : ℝ, (∀ k : ℤ, r ≠ k * L) → ContDiffAt ℝ ∞ (scaledKernel s L) r) ∧
      TendstoLocallyUniformlyOn (fun (M : ℕ) (r : ℝ) =>
          ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), signPow s (r - k * L))
        (scaledKernel s L) atTop {r : ℝ | ∀ k : ℤ, r ≠ k * L} ∧
      Tendsto (fun M : ℕ => ∫ r in (-(L / 2))..(L / 2),
          |∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), signPow s (r - k * L) - scaledKernel s L r|)
        atTop (𝓝 0)) ∧
    -- (D) the derivative bounds, with a constant independent of `L`
    (∀ s : ℝ, 0 < s → s < 1 → ∀ m : ℕ, 1 ≤ m → ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ, 1 ≤ L →
      ∀ r : ℝ, (∀ k : ℤ, r ≠ k * L) →
        ‖iteratedDeriv m (scaledKernel s L) r‖ ≤ C * latticeDist L r ^ (s - 1 - (m : ℝ))) ∧
    -- (T) the transport of the periodized profile on the observation circle
    (∃ hL2 : MemLp (fun z : Circle (observationLength ell) =>
        ((transportConv P.val.1 P.val.2 (observationLength ell).val (zeroExtension p)
          (centralRep (observationLength ell) z) : ℝ) : ℂ)) 2 (arclength (observationLength ell)),
      ∀ k : ℤ, coeff (observationLength ell)
          ⟨_, hL2.integrable (by norm_num)⟩ k =
        transportCoeffs P (observationLength ell)
          ⟨periodizedProfile p (observationLength ell), periodizedProfileL2 p ell⟩ k) ∧
    -- (S) smoothness off the periodized support, and derivative bounds
    (∀ ρ : ℝ, 0 < ρ → ρ < 1 / 2 → (∀ᵐ x : ℝ, ρ ≤ |x| → zeroExtension p x = 0) →
      ∀ x0 : ℝ, (∀ k : ℤ, ∀ y ∈ Icc (-ρ) ρ, x0 ≠ y + k * (observationLength ell).val) →
        ContDiffAt ℝ ∞ (transportConv P.val.1 P.val.2 (observationLength ell).val
          (zeroExtension p)) x0) ∧
    (∀ m : ℕ, 1 ≤ m → ∃ C : ℝ, 0 < C ∧ ∀ (L : ℝ) (ζ : ℝ → ℝ) (ρ x0 : ℝ), 0 < ρ → ρ < 1 / 2 →
      1 ≤ |x0| → |x0| ≤ L / 2 → IntegrableOn ζ (Ioc (-ρ) ρ) →
      (∀ᵐ y : ℝ, ρ ≤ |y| → ζ y = 0) →
      ‖iteratedDeriv m (transportConv P.val.1 P.val.2 L ζ) x0‖ ≤
        C * (∫ y, |ζ y|) * |x0| ^ (P.val.2 - 1 - (m : ℝ))) := by
  have hβ : 0 < P.val.1 := P.property.1
  have hs0 : 0 < P.val.2 := P.property.2.1
  have hs1 : P.val.2 < 1 := P.property.2.2
  refine ⟨fun s hs0' hs1' L hL1 => ?_, fun s hs0' hs1' m hm => ?_, ?_, ?_, ?_⟩
  · have hL : 0 < L := by linarith
    exact ⟨fun a b => intervalIntegrable_scaledKernel hs0' hs1' hL a b,
      integral_scaledKernel_period hL,
      scaledKernel_periodic hL,
      fun r hr => scaledKernel_contDiffAt hs0' hs1' hL hr,
      tendstoLocallyUniformlyOn_scaled_signPow hs0' hs1' hL,
      tendsto_scaled_signPow_L1 hs0' hs1' hL⟩
  · obtain ⟨C, hC, hb⟩ := norm_iteratedDeriv_scaledKernel_le hs0' hs1' hm
    exact ⟨C, hC, fun L hL1 r hr => hb L r (by linarith) hr⟩
  · have hℓ1 : 1 ≤ (observationLength ell).val := (one_le_inv₀ ell.property.1).mpr ell.property.2
    have hℓ0 : 0 < (observationLength ell).val := by linarith
    obtain ⟨hζ1, hζ2⟩ := zeroExtension_integrableOn p (observationLength ell)
    have hL2 := memLp_transportConv_circle (β := P.val.1) hs0 hs1 (observationLength ell) hζ1 hζ2
    refine ⟨hL2, fun k => ?_⟩
    have hper : (fun z : Circle (observationLength ell) =>
        ((periodizedProfile p (observationLength ell) z : ℝ) : ℂ)) =
        fun z => ((zeroExtension p (centralRep (observationLength ell) z) : ℝ) : ℂ) :=
      funext fun z => by rw [periodizedProfile_eq_zeroExtension p _ hℓ1 z]
    have h2 : Integrable (fun z : Circle (observationLength ell) =>
        ((zeroExtension p (centralRep (observationLength ell) z) : ℝ) : ℂ))
        (arclength (observationLength ell)) := by
      rw [← hper]
      exact (periodizedProfileL2 p ell).integrable (by norm_num)
    by_cases hk : k = 0
    · subst hk
      have h0 : transportCoeffs P (observationLength ell)
          ⟨periodizedProfile p (observationLength ell), periodizedProfileL2 p ell⟩ 0 = 0 := by
        unfold transportCoeffs
        simp
      rw [h0, coeff_transportConv hs0 hs1 (observationLength ell) hζ1 0 _ h2,
        kernelCoeff_zero _ _ hℓ0]
      simp
    · have hmul := transportConst_mul_kernelCoeff P hℓ0 hk
      rw [coeff_transportConv hs0 hs1 (observationLength ell) hζ1 k _ h2,
        transportCoeffs_eq_mult P (observationLength ell) _ hk, ← hmul]
      congr 1
      exact coeff_congr_fun k _ _ hper.symm
  · intro ρ hρ0 hρ1 hsupp x0 hx0
    have hℓ1 : 1 ≤ (observationLength ell).val := (one_le_inv₀ ell.property.1).mpr ell.property.2
    have hℓ0 : 0 < (observationLength ell).val := by linarith
    obtain ⟨hζ1, -⟩ := zeroExtension_integrableOn p (observationLength ell)
    have hsub : Ioc (-ρ) ρ ⊆ Ioc (-((observationLength ell).val / 2)) ((observationLength ell).val / 2) :=
      fun y hy => ⟨by linarith [hy.1], by linarith [hy.2]⟩
    exact contDiffAt_transportConv (β := P.val.1) hs0 hs1 hℓ0 (by linarith) hsupp
      (hζ1.mono_set hsub) hx0
  · intro m hm
    obtain ⟨C, hC, hb⟩ := norm_iteratedDeriv_transportConv_le (β := P.val.1) hs0 hs1 hβ hm
    refine ⟨C, hC, fun L ζ ρ x0 hρ0 hρ1 hx1 hxL hζ hsupp => ?_⟩
    have hconv : ∫ y in Ioc (-ρ) ρ, |ζ y| = ∫ y, |ζ y| :=
      MeasureTheory.setIntegral_eq_integral_of_ae_compl_eq_zero (by
        filter_upwards [hsupp] with y hy hyn
        rw [hy (le_abs_of_not_mem_Ioc hyn), abs_zero])
    rw [← hconv]
    exact hb L ζ ρ x0 hρ0 hρ1 hx1 hxL hζ hsupp

end Riesz1
