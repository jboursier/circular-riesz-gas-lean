/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopLocalizationIntegrability
public import Riesz1.Auxiliary.LoopLocalizationPairingBound
public import Riesz1.ToMathlib.QuadraticDiscrepancySplit

/-!
# The exact partial-window exterior cross pairing

The localization part of Lemma 5.8. The centered empirical period
and the centered background are split into their local and exterior pieces.
Symmetry combines the two cross terms with their correct factor of two.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace Riesz1

/-- Exact partial-window expansion on the exterior good event. The right
side uses the pair kernel, so it is defined everywhere without
extending the force beyond its good-event or spatial carrier. -/
theorem loopLocalization_partial_expansion {s : ℝ} (hs : 0 < s) (hs1 : s < 1)
    {N : ℕ+} {ℓ γ : ℝ} (hℓ : 0 < ℓ) (hK : 1 ≤ (N : ℝ) * ℓ)
    (hγ : 0 ≤ γ) (hP : GradPartial N ℓ γ) {χ ψ : ℝ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hχs : tsupport χ ⊆ Ioo (-(1 / 4)) (1 / 4))
    (hψ : ContDiff ℝ ∞ ψ) (hpψ : Function.Periodic ψ ℓ⁻¹)
    (X : {X : LoopPrecedingConfiguration N // X ∈ loopExteriorGood N ℓ γ}) :
    let b0 := loopLocalTransport χ N ℓ γ ψ
    let q := fun z => (∑ j ∈ loopExteriorLabels N ℓ γ,
      loopArcKernel s N b0 z (loopPrecedingLift X.val j)) -
      ∫ u in loopExteriorBackground N ℓ γ, loopArcKernel s N b0 z u
    loopArcL s N b0 X.val.val - loopLocalLoop s N ℓ γ b0 X.val -
      loopLocalBackground s N ℓ γ b0 =
      2 * ((∑ i ∈ gradLabels N ℓ γ, q (loopPrecedingLift X.val i)) -
        ∫ z in -gradM N ℓ γ..gradM N ℓ γ, q z) := by
  classical
  let b0 := loopLocalTransport χ N ℓ γ ψ
  let k := loopArcKernel s N b0
  let M := gradM N ℓ γ
  let D := Icc (-(N : ℝ) / 2) ((N : ℝ) / 2)
  let B := Icc (-M) M
  let C := loopExteriorBackground N ℓ γ
  let μ := (volume : Measure ℝ).restrict B
  let ν := (volume : Measure ℝ).restrict C
  let I := gradLabels N ℓ γ
  let E := loopExteriorLabels N ℓ γ
  let a : ℤ := -(((N : ℤ) - 1) / 2)
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one (Real.one_le_rpow hK hγ)
  have hNr : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hPr : M < (N : ℝ) / 8 := hP
  have hBD : B ⊆ D := by intro z hz; constructor <;> linarith [hz.1, hz.2]
  have hCD : C ⊆ D := fun _ h => h.1
  have hmB : MeasurableSet B := measurableSet_Icc
  have hmC : MeasurableSet C := measurableSet_loopExteriorBackground N ℓ γ
  have hμ : (volume : Measure ℝ).restrict D = μ + ν := by
    dsimp only [μ, ν, C, loopExteriorBackground]
    rw [← Measure.restrict_inter_add_sdiff D hmB, inter_eq_right.mpr hBD]
  have hb : ContDiff ℝ 1 b0 := (contDiff_loopLocalTransport hχ hψ hχs N hℓ γ).of_le (by simp)
  have hp : Function.Periodic b0 (N : ℝ) := loopLocalTransport_periodic hℓ χ hpψ
  have hi := loopLocalization_kernel_integrable_centered hs hs1 hb hp
  have hBB : Integrable (fun p : ℝ × ℝ => k p.1 p.2) (μ.prod μ) :=
    hi.mono_measure (Measure.prod_mono (Measure.restrict_mono hBD le_rfl)
      (Measure.restrict_mono hBD le_rfl))
  have hBC : Integrable (fun p : ℝ × ℝ => k p.1 p.2) (μ.prod ν) :=
    hi.mono_measure (Measure.prod_mono (Measure.restrict_mono hBD le_rfl)
      (Measure.restrict_mono hCD le_rfl))
  have hCC : Integrable (fun p : ℝ × ℝ => k p.1 p.2) (ν.prod ν) :=
    hi.mono_measure (Measure.prod_mono (Measure.restrict_mono hCD le_rfl)
      (Measure.restrict_mono hCD le_rfl))
  have hslice (z : ℝ) : Integrable (k z) μ ∧ Integrable (k z) ν := by
    have hi : IntegrableOn (k z) D :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).mp
        (loopLocalKernel_intervalIntegrable hs hs1 N hb hp z (-(N : ℝ) / 2) ((N : ℝ) / 2))
    exact ⟨hi.mono_set hBD, hi.mono_set hCD⟩
  have hzeroE (j : ℤ) (hj : j ∈ E) : b0 (loopPrecedingLift X.val j) = 0 :=
    loopLocalTransport_zero_exterior hℓ hK hγ hP hχs ψ X.property hj
  have hzeroC (u : ℝ) (hu : u ∈ C) : b0 u = 0 :=
    loopLocalTransport_zero_exteriorBackground hℓ hP hχs ψ hu
  have hEE : ∀ i ∈ E, ∀ j ∈ E, k (loopPrecedingLift X.val i) (loopPrecedingLift X.val j) = 0 := by
    intro i hi j hj
    simp only [k, loopArcKernel, hzeroE i hi, hzeroE j hj, sub_self, zero_mul]
  have hEC : ∀ i ∈ E, ∀ᵐ u ∂ν, k (loopPrecedingLift X.val i) u = 0 := by
    intro i hi
    filter_upwards [ae_restrict_mem hmC] with u hu
    simp only [k, loopArcKernel, hzeroE i hi, hzeroC u hu, sub_self, zero_mul]
  have hCC0 : ∀ᵐ z ∂ν, ∀ᵐ u ∂ν, k z u = 0 := by
    filter_upwards [ae_restrict_mem hmC] with z hz
    filter_upwards [ae_restrict_mem hmC] with u hu
    simp only [k, loopArcKernel, hzeroC z hz, hzeroC u hu, sub_self, zero_mul]
  obtain ⟨hIE, hpart⟩ := loopLocalization_label_partition hK hγ hP
  have hgen := quadratic_discrepancy_split I E hIE (loopPrecedingLift X.val) μ ν k
    (fun x y => (loopLocalKernel_swap s N b0 x y).symm) hslice hBB hBC hCC hEE hEC hCC0
  have heqD (f : ℝ → ℝ) : (∫ z in D, f z) = ∫ z in (-(N : ℝ) / 2)..((N : ℝ) / 2), f z := by
    rw [intervalIntegral.integral_of_le (by linarith : -(N : ℝ) / 2 ≤ (N : ℝ) / 2)]
    exact integral_Icc_eq_integral_Ioc
  have heqB (f : ℝ → ℝ) : (∫ z, f z ∂μ) = ∫ z in (-M)..M, f z := by
    rw [intervalIntegral.integral_of_le (by linarith : -M ≤ M)]
    exact integral_Icc_eq_integral_Ioc
  have hglobal : ((∑ i ∈ I ∪ E, ∑ j ∈ I ∪ E,
      k (loopPrecedingLift X.val i) (loopPrecedingLift X.val j)) -
      2 * (∑ i ∈ I ∪ E, ∫ u, k (loopPrecedingLift X.val i) u ∂(μ + ν)) +
      ∫ z, ∫ u, k z u ∂(μ + ν) ∂(μ + ν)) = loopArcL s N b0 X.val.val := by
    rw [← hμ]
    simp_rw [heqD]
    rw [hpart]
    have hg := loopLocalization_period_expansion (s := s) hp X.val a (-(N : ℝ) / 2)
    simpa only [show -(N : ℝ) / 2 + N = (N : ℝ) / 2 by ring] using hg.symm
  have hlocal : ((∑ i ∈ I, ∑ j ∈ I,
      k (loopPrecedingLift X.val i) (loopPrecedingLift X.val j)) -
      2 * (∑ i ∈ I, ∫ u, k (loopPrecedingLift X.val i) u ∂μ) +
      ∫ z, ∫ u, k z u ∂μ ∂μ) =
      loopLocalLoop s N ℓ γ b0 X.val + loopLocalBackground s N ℓ γ b0 := by
    have hpair : (∑ i ∈ I, ∑ j ∈ I, k (loopPrecedingLift X.val i) (loopPrecedingLift X.val j)) =
        ∑ i ∈ I, ∑ j ∈ I.erase i, k (loopPrecedingLift X.val i) (loopPrecedingLift X.val j) := by
      apply Finset.sum_congr rfl
      intro i hi
      have he := Finset.sum_erase_add I (fun j => k (loopPrecedingLift X.val i)
        (loopPrecedingLift X.val j)) hi
      simpa only [k, loopArcKernel, sub_self, zero_mul, add_zero] using he.symm
    simp_rw [heqB]
    rw [hpair]
    simp only [loopLocalLoop, loopLocalBackground, loopLocalLo, loopLocalHi, hP, ↓reduceIte]
    rfl
  rw [hglobal, hlocal] at hgen
  simp_rw [heqB] at hgen
  dsimp only [ν, C, k, I, E, M] at hgen
  dsimp only
  linarith only [hgen]

end Riesz1

end
