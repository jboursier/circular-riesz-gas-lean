/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.RegMicroPositiveNear
public import Riesz1.CLT.IdentityDefs
public import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-!
# Positive-exponent near variance for the actual inverse representative

The positive branch of Lemma 5.3. The input is the kernel conclusion, and the
output retains its transport witness and its almost everywhere identification
on the fundamental cell.
-/

public section

open MeasureTheory Set

namespace Riesz1.Internal

/-- Apply the positive singular envelope of the kernel theorem to the actual
near error. The constant precedes the circle, mollifier and kernel constant. -/
theorem micro_near_positive_of_kernel (P : Parameters) (n : ℕ+) (α : ℝ)
    (hα0 : 0 < α) (hα1 : α < 1/2) :
    ∃ D : ℝ, 0 < D ∧ ∀ (hPL : External.PrekopaLeindler) (N : ℕ+) (ℓ : Scale),
      1 ≤ (N : ℝ)*ℓ.val →
      let L := observationLength ℓ
      let K := (N : ℝ)*ℓ.val
      ∀ (ρ : ℝ → ℝ) (hρ : IsMollifier ρ) (C H : ℝ),
        0 ≤ C → K⁻¹ ≤ H →
      ∀ (a : Fin (n : ℕ) → ℝ),
        (∀ i j, i ≠ j → 8*K⁻¹ ≤ dist (a i : Circle L) (a j : Circle L)) →
      ∀ f : {f : Circle L → ℝ // MemLp (fun x => (f x : ℂ)) 2 (arclength L)},
        MicroKernelBounds P ρ α C H n a L f →
      ∃ ψ : {g : Circle L → ℝ // MemLp (fun x => (g x : ℂ)) 2 (arclength L)},
        Continuous ψ.val ∧
        (∀ k : ℤ, coeff L
          ⟨fun x => (ψ.val x : ℂ), complexL2Integrable L _ ψ.property⟩ k =
            transportCoeffs P L f k) ∧
      let m := (∫ y in Ioc (-(L.val/2)) (L.val/2), f.val (y : Circle L))/L.val
      let q := deriv (fun t : ℝ => ψ.val (t : Circle L))
      let e := fun z : Circle L => m + inverseConvCircle P L q z -
        cltRegCircle hρ L (show 0<K⁻¹ from inv_pos.mpr
          (mul_pos (by exact_mod_cast N.pos) ℓ.property.1)) f z
      Measurable e ∧
      (∀ᵐ x : ℝ ∂volume.restrict (Ioc (-(L.val/2)) (L.val/2)),
        e (x : Circle L) = f.val (x : Circle L) -
          circleMollify ρ L.val K⁻¹ (fun t => f.val (t : Circle L)) x) ∧
      ∃ hF : Integrable (fun X : Configuration N => ∑ i : Fin (N : ℕ),
          microNearError L.val K⁻¹ a e ((X.val i/ℓ.val : ℝ) : Circle L)) (gibbsMeasure P N),
        variance (gibbsMeasure P N) (fun X => ∑ i : Fin (N : ℕ),
          microNearError L.val K⁻¹ a e ((X.val i/ℓ.val : ℝ) : Circle L)) hF ≤
            ENNReal.ofReal (D*C^2*K^(2*α)) := by
  obtain ⟨D, hD, hb⟩ := micro_near_positive_of_envelope P n α hα0.le hα1
  refine ⟨D, hD, fun hPL N ℓ hK => ?_⟩
  dsimp only
  intro ρ hρ C H hC hH a hsep f hkernel
  let L := observationLength ℓ
  let K := (N : ℝ)*ℓ.val
  have : Fact (0 < L.val) := ⟨L.property⟩
  have hh : 0 < K⁻¹ := inv_pos.mpr (mul_pos (by exact_mod_cast N.pos) ℓ.property.1)
  rcases hkernel with ⟨ψ, hc, hcoeff, hrep, _hmoll, _hder, _herr,
    _hnegative, hpositive, _hloc, _htrans, _haway⟩
  let m := (∫ y in Ioc (-(L.val/2)) (L.val/2), f.val (y : Circle L))/L.val
  let q := deriv (fun t : ℝ => ψ.val (t : Circle L))
  let e : Circle L → ℝ := fun z => m + inverseConvCircle P L q z - cltRegCircle hρ L hh f z
  have hregc : Continuous (cltRegCircle hρ L hh f) :=
    (QuotientAddGroup.isQuotientMap_mk _).continuous_iff.2
      (cltRegCircle_contDiff hρ L hh f).continuous
  have he : Measurable e :=
    (measurable_const.add (measurable_inverseConvCircle P L (measurable_deriv _))).sub hregc.measurable
  have hbound (z : Circle L) (hz : ∀ j, z ≠ (a j : Circle L)) :
      |e z| ≤ C*(K⁻¹^(-α) + ∑ j, dist z (a j : Circle L)^(-α)) := by
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
    dsimp only [e]
    rw [inverseConvCircle_coe, cltRegCircle_coe]
    exact (hpositive hα0 K⁻¹ hh hH).1 x hz
  obtain ⟨hF, hv⟩ := hb hPL N ℓ hK a hsep C hC e he hbound
  refine ⟨ψ, hc, hcoeff, he, ?_, hF, hv⟩
  filter_upwards [hrep] with x hx
  rw [inverseConvCircle_coe, cltRegCircle_coe, ← hx]

end Riesz1.Internal
