/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.RegMicroFinalSmall
public import Riesz1.Variance.RegMicroFinalBounded
public import Riesz1.Variance.RegMicroNearFarExponent
public import Riesz1.Variance.RegTransportBoundsFixedCircle

/-!
# Microscopic regularization variance at a fixed observation scale

Lemma 5.3 on a fixed circle, including both exceptional
exponents, bounded particle number and `N=1`. The coefficient precedes
every particle number. Its dependence on the fixed scale is explicit.
The scale-uniform compact-profile theorem requires additional work.
-/

public section

open MeasureTheory Set Filter

namespace Riesz1.Internal

/-- A nonexceptional interior exponent with arbitrarily small power loss. -/
theorem regMicro_interior_exponent {s α ε : ℝ} (hα0 : s-1 ≤ α)
    (hα1 : α < s/2) (hε : 0 < ε) :
    ∃ α' : ℝ, s-1 < α' ∧ α' < s/2 ∧ α ≤ α' ∧ α' ≠ 0 ∧ 2*(α'-α) ≤ ε/2 := by
  let δ := min ((s/2-α)/2) (ε/8)
  have hδ : 0 < δ := lt_min (by linarith) (by linarith)
  obtain ⟨a, ha0, ha1⟩ := exists_between (show α < α+δ by linarith)
  have ha2 : a < s/2 := by dsimp [δ] at ha1; linarith [min_le_left ((s/2-α)/2) (ε/8)]
  have haε : 2*(a-α) ≤ ε/2 := by dsimp [δ] at ha1; linarith [min_le_right ((s/2-α)/2) (ε/8)]
  by_cases ha : a = 0
  · refine ⟨α/2, by linarith, by linarith, by linarith, by linarith, by linarith⟩
  · exact ⟨a, lt_of_le_of_lt hα0 ha0, ha2, ha0.le, ha, haε⟩

/-- The full kernel conclusion on any fixed observation circle.
Only the primitive and transport hypotheses are assumed. -/
theorem regMicro_kernel_fixed_circle (P : Parameters) (L : Length) (hL : 1 ≤ L.val)
    (η B : ℝ) (n : ℕ+) (a : Fin (n : ℕ) → ℝ) (α C₀ : ℝ)
    (hη : 0 < η) (hB : 0 ≤ B) (hC₀ : 0 ≤ C₀)
    (hα0 : P.val.2-1 < α) (hα1 : α < P.val.2/2)
    (f : {f : Circle L → ℝ // MemLp (fun z => (f z : ℂ)) 2 (arclength L)})
    (hprim : PrimitiveRegularity L η P.val.2 B f)
    (hreg : TransportRegularity P L f n a α C₀)
    (ρ : ℝ → ℝ) (hρ : IsMollifier ρ) :
    ∃ C : ℝ, 0 < C ∧ MicroKernelBounds P ρ α C (1/4) n a L f := by
  obtain ⟨J, hJ, hj⟩ := uniform_inverse_microKernelBounds P ρ hρ α hα0 hα1 n
  obtain ⟨A, hA, ψ, hc, hψ, hcoeff, hi, _hAC, hsup, hpoint⟩ :=
    fixed_circle_regTransportBounds P L η B n a α α C₀ hη hB hC₀ hα0.le hα1
      le_rfl hα0 f hprim hreg
  let q := deriv (fun t : ℝ => ψ (t : Circle L))
  have hqp : Function.Periodic q L.val := deriv_periodic_of (fun t => by
    rw [AddCircle.coe_add_period])
  have heq := (show Function.Periodic (fun t => |q t|) L.val from
    fun t => congrArg abs (hqp t)).intervalIntegral_add_eq (-(L.val/2)) 0
  rw [show -(L.val/2)+L.val = L.val/2 by ring, zero_add,
    intervalIntegral.integral_of_le (by linarith [L.property])] at heq
  have hnorm : (∫ y in Ioc (-(L.val/2)) (L.val/2), |q y|) ≤ A := by
    have hh := hsup (0 : Circle L)
    change |ψ 0|+(∫ t in (0 : ℝ)..L.val, |q t|) ≤ A at hh
    rw [heq]
    linarith [abs_nonneg (ψ 0)]
  exact ⟨J*A, mul_pos hJ hA, hj L hL η B C₀ hη hB hC₀ f a hprim hreg
    ⟨ψ, hψ⟩ hc hcoeff hi A hA hnorm hpoint (1/4) le_rfl⟩

end Riesz1.Internal

namespace Riesz1

/-- Lemma 5.3 for a fixed observation scale. All
exponent cases and particle numbers are included. At macroscopic scale
the circle is fixed, so this proves that entire regime of the lemma.
The coefficient here may depend on the fixed scale. This theorem alone
does not provide the shrinking-scale compact-profile assertion. -/
theorem reg_micro_fixed_scale
    (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (P : Parameters) (ℓ : Scale) (α : ℝ) (η B C₀ : ℝ) (n : ℕ+)
    (a : Fin (n : ℕ) → ℝ)
    (hα0 : P.val.2-1 ≤ α) (hα1 : α < P.val.2/2)
    (hη : 0 < η) (hB : 0 ≤ B) (hC₀ : 0 ≤ C₀)
    (f : {f : Circle (observationLength ℓ) → ℝ //
      MemLp (fun z => (f z : ℂ)) 2 (arclength (observationLength ℓ))})
    (hprim : PrimitiveRegularity (observationLength ℓ) η P.val.2 B f)
    (hreg : TransportRegularity P (observationLength ℓ) f n a α C₀)
    (ρ : ℝ → ℝ) (hρ : IsMollifier ρ) (ε : ℝ) (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ N : ℕ+, 1 ≤ cltK N ℓ →
      ∃ hE : MemLp (mixedStat P N ℓ (subCircleL2 f (mixedReg hρ N ℓ f))) 2 (gibbsMeasure P N),
        variance (gibbsMeasure P N) _ (hE.integrable one_le_two) ≤
          ENNReal.ofReal (D*cltK N ℓ^ε*(cltK N ℓ^(2*α)+cltK N ℓ^(3*P.val.2-2))) := by
  obtain ⟨α', hα'0, hα'1, hαα', hα'ne, hloss⟩ :=
    Internal.regMicro_interior_exponent hα0 hα1 hε
  let L := observationLength ℓ
  let C₀' := C₀*(1+∑ j, |a j|)^(α'-α)
  have hC₀' : 0 ≤ C₀' := by dsimp [C₀']; positivity
  have hreg' := Internal.transportRegularity_increase_exponent P L f n a hαα' hC₀ hreg
  have hL : 1 ≤ L.val := (one_le_inv₀ ℓ.property.1).mpr ℓ.property.2
  obtain ⟨C, hC, hkernel⟩ := Internal.regMicro_kernel_fixed_circle P L hL η B n a α' C₀'
    hη hB hC₀' hα'0 hα'1 f hprim hreg' ρ hρ
  obtain ⟨δ, hδ, hsep⟩ := exists_pos_le_dist_of_injective hreg.1
  let r₀ := min (δ/8) (1/16)
  have hr₀ : 0 < r₀ := lt_min (by linarith) (by norm_num)
  have hr₀small : r₀ < 1/8 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hsep' : ∀ i j, i ≠ j → 4*r₀ ≤ dist (a i : Circle L) (a j : Circle L) := by
    intro i j hij
    have hh : r₀ ≤ δ/8 := min_le_left _ _
    linarith [hsep i j hij]
  obtain ⟨Dsmall, hDsmall, hsmall⟩ := Internal.regMicro_small_radius_of_kernel
    hBE hPL P α' (ε/2) hα'0.le hα'1 hα'ne (by linarith) n η B C₀' hη hB hC₀'
      ρ hρ C (1/4) r₀ (L.val/2) hC.le hr₀ hr₀small
  let H := min (1/4 : ℝ) (r₀/8)
  have hH : 0 < H := lt_min (by norm_num) (by linarith)
  let K₀ := max 1 H⁻¹
  have hK₀ : 1 ≤ K₀ := le_max_left _ _
  let Q := ∫ z : UnitAddCircle, (loopMasterPullback L f.val z)^2
  have hQ : 0 ≤ Q := integral_nonneg fun _ => sq_nonneg _
  obtain ⟨Db, hDb, hb⟩ := Internal.regMicro_bounded_length_rate K₀
    (16*(K₀/ℓ.val)^2*Q) P.val.2 α ε hK₀ hε.le
  refine ⟨Dsmall+Db, add_pos hDsmall hDb, fun N hK => ?_⟩
  let K := cltK N ℓ
  have hK0 : 0 < K := cltK_pos N ℓ
  have hR : 0 ≤ K^ε*(K^(2*α)+K^(3*P.val.2-2)) := by positivity
  by_cases hh : K⁻¹ ≤ H
  · obtain ⟨hE, hv⟩ := hsmall N ℓ hK a hsep' f hprim hreg' hkernel
      (hh.trans (min_le_left _ _)) (hh.trans (min_le_right _ _)) (Or.inl le_rfl)
    refine ⟨hE, hv.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    have hp : K^(ε/2)*(K^(2*α')+K^(3*P.val.2-2)) ≤
        K^ε*(K^(2*α)+K^(3*P.val.2-2)) := by
      have ht := Internal.regMicro_endpoint_rate (s := P.val.2) (α := α)
        (δ := α'-α) hK hloss hε.le
      simpa only [add_sub_cancel] using ht
    calc
      _ ≤ Dsmall*(K^ε*(K^(2*α)+K^(3*P.val.2-2))) := by
        simpa only [K, cltK, mul_assoc] using mul_le_mul_of_nonneg_left hp hDsmall.le
      _ ≤ (Dsmall+Db)*(K^ε*(K^(2*α)+K^(3*P.val.2-2))) :=
        mul_le_mul_of_nonneg_right (by linarith) hR
      _ = _ := by ring
  · have hKK : K ≤ K₀ := by
      have hinv : H < K⁻¹ := lt_of_not_ge hh
      have hk : K < H⁻¹ := (lt_inv_comm₀ hK0 hH).mpr hinv
      exact hk.le.trans (le_max_right _ _)
    have hN : (N : ℝ) ≤ K₀/ℓ.val := (le_div_iff₀ ℓ.property.1).mpr hKK
    obtain ⟨hE, hv⟩ := Internal.regMicro_error_variance_l2 P N ℓ hρ f
    refine ⟨hE, hv.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    have hp : 16*(N : ℝ)^2*Q ≤ 16*(K₀/ℓ.val)^2*Q := by
      have hN0 : 0 ≤ (N : ℝ) := by positivity
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hN0 hN 2) (by norm_num)) hQ
    have hp' := hb K hK hKK
    calc
      _ ≤ 16*(K₀/ℓ.val)^2*Q := hp
      _ ≤ Db*K^ε*(K^(2*α)+K^(3*P.val.2-2)) := hp'
      _ ≤ (Dsmall+Db)*K^ε*(K^(2*α)+K^(3*P.val.2-2)) := by
        nlinarith [mul_nonneg hDsmall.le hR]

end Riesz1
