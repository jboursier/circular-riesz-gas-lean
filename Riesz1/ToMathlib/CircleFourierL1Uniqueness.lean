/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

/-!
# Fourier uniqueness for integrable real functions on a circle

An integrable real function on `AddCircle T` whose Fourier coefficients all vanish is zero almost
everywhere. This is the `L¹` version of `Riesz1.CircleFourier.ae_eq_of_coeff_eq`, which needs
square integrability. The proof has three steps. Trigonometric polynomials are uniformly dense in the
continuous functions, so the pairing with every continuous real test function vanishes. Then the
finite measures with densities `f⁺` and `f⁻` agree on bounded continuous functions, hence coincide,
and so `f⁺ = f⁻` almost everywhere, which forces `f = 0`.
-/

public section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace Riesz1.CircleFourier

variable {T : ℝ} [hT : Fact (0 < T)]

/-- An integrable real function times a continuous complex function on the circle is
integrable. -/
lemma integrable_ofReal_mul_continuous {f : AddCircle T → ℝ} (hf : Integrable f)
    (p : C(AddCircle T, ℂ)) : Integrable (fun x => (f x : ℂ) * p x) :=
  (hf.ofReal).mul_bdd p.continuous.aestronglyMeasurable (ae_of_all _ fun x => p.norm_coe_le_norm x)

/-- The pairing of an integrable function with a trigonometric polynomial vanishes when all Fourier
coefficients of the function vanish. -/
lemma integral_mul_span_fourier_eq_zero {f : AddCircle T → ℝ} (hf : Integrable f)
    (h : ∀ k : ℤ, fourierCoeff (fun x => (f x : ℂ)) k = 0) {p : C(AddCircle T, ℂ)}
    (hp : p ∈ Submodule.span ℂ (Set.range (fourier (T := T)))) :
    ∫ x, (f x : ℂ) * p x = 0 := by
  induction hp using Submodule.span_induction with
  | mem q hq =>
    obtain ⟨k, rfl⟩ := hq
    have h0 : ∫ x : AddCircle T, (f x : ℂ) * (fourier k : C(AddCircle T, ℂ)) x
        ∂AddCircle.haarAddCircle = 0 := by
      have hk := h (-k)
      unfold fourierCoeff at hk
      rw [neg_neg] at hk
      rw [← hk]
      congr 1
      funext x
      simp only [smul_eq_mul]
      ring
    rw [AddCircle.volume_eq_smul_haarAddCircle, integral_smul_measure, h0, smul_zero]
  | zero => simp
  | add q r _ _ hq hr =>
    show ∫ x, (f x : ℂ) * (q x + r x) = 0
    have hiq := integrable_ofReal_mul_continuous hf q
    have hir := integrable_ofReal_mul_continuous hf r
    simp only [mul_add]
    rw [integral_add hiq hir, hq, hr, add_zero]
  | smul c q _ hq =>
    show ∫ x, (f x : ℂ) * (c • q) x = 0
    have hc : (fun x => (f x : ℂ) * (c • q) x) = fun x => c * ((f x : ℂ) * q x) :=
      funext fun x => by simp only [ContinuousMap.smul_apply, smul_eq_mul]; ring
    rw [hc, integral_const_mul, hq, mul_zero]

/-- The pairing of an integrable real function with a continuous real test function vanishes when
all its Fourier coefficients vanish. Trigonometric polynomials approximate the test function
uniformly, and the pairing with each of them vanishes. -/
lemma integral_mul_continuous_eq_zero {f : AddCircle T → ℝ} (hf : Integrable f)
    (h : ∀ k : ℤ, fourierCoeff (fun x => (f x : ℂ)) k = 0) (φ : C(AddCircle T, ℝ)) :
    ∫ x, f x * φ x = 0 := by
  set φc : C(AddCircle T, ℂ) := ⟨fun x => (φ x : ℂ), Complex.continuous_ofReal.comp φ.continuous⟩
    with hφc
  have hcl : φc ∈ closure (Submodule.span ℂ (Set.range (fourier (T := T))) : Set C(AddCircle T, ℂ)) := by
    rw [← Submodule.topologicalClosure_coe, span_fourier_closure_eq_top]
    exact Set.mem_univ _
  set A : ℝ := ∫ x, ‖f x‖ with hA
  -- For every `η > 0`, the pairing with `φc` is at most `η A` in norm.
  have key : ∀ η : ℝ, 0 < η → ‖∫ x, (f x : ℂ) * φc x‖ ≤ η * A := by
    intro η hη
    obtain ⟨p, hp, hd⟩ := Metric.mem_closure_iff.1 hcl η hη
    have hzero := integral_mul_span_fourier_eq_zero hf h hp
    have hsplit : (fun x => (f x : ℂ) * φc x) =
        fun x => (f x : ℂ) * (φc - p) x + (f x : ℂ) * p x := by
      funext x
      simp only [ContinuousMap.sub_apply]
      ring
    have hint1 := integrable_ofReal_mul_continuous hf (φc - p)
    have hint2 := integrable_ofReal_mul_continuous hf p
    rw [hsplit, integral_add hint1 hint2, hzero, add_zero]
    have hbound : ∀ x, ‖(f x : ℂ) * (φc - p) x‖ ≤ η * ‖f x‖ := by
      intro x
      have hx : ‖(φc - p) x‖ ≤ η := by
        rw [ContinuousMap.sub_apply, ← dist_eq_norm]
        exact (ContinuousMap.dist_apply_le_dist x).trans hd.le
      rw [norm_mul, Complex.norm_real]
      have := mul_le_mul_of_nonneg_left hx (norm_nonneg (f x))
      linarith [mul_comm (‖f x‖) η]
    have hg : Integrable (fun x => η * ‖f x‖) := hf.norm.const_mul η
    calc ‖∫ x, (f x : ℂ) * (φc - p) x‖ ≤ ∫ x, η * ‖f x‖ :=
          norm_integral_le_of_norm_le hg (ae_of_all _ hbound)
      _ = η * A := by rw [integral_const_mul]
  -- Since `η` is arbitrary, the pairing with `φc` vanishes.
  have hC : ∫ x, (f x : ℂ) * φc x = 0 := by
    have hA0 : 0 ≤ A := integral_nonneg fun x => norm_nonneg _
    apply norm_le_zero_iff.1
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hη : 0 < ε / (A + 1) := div_pos hε (by linarith)
    have h1 := key _ hη
    have h2 : ε / (A + 1) * A ≤ ε := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
      nlinarith
    linarith
  have hreal : ((∫ x, f x * φ x : ℝ) : ℂ) = 0 := by
    rw [← integral_complex_ofReal]
    simpa [hφc, Complex.ofReal_mul] using hC
  exact_mod_cast hreal

/-- **Fourier uniqueness in `L¹`.** An integrable real function on `AddCircle T` whose Fourier
coefficients all vanish is zero almost everywhere. -/
theorem ae_eq_zero_of_integrable_fourierCoeff_eq_zero {f : AddCircle T → ℝ} (hf : Integrable f)
    (h : ∀ k : ℤ, fourierCoeff (fun x => (f x : ℂ)) k = 0) : f =ᵐ[volume] 0 := by
  have hmeas : AEMeasurable fun x => ENNReal.ofReal (f x) := hf.aemeasurable.ennreal_ofReal
  have hmeas' : AEMeasurable fun x => ENNReal.ofReal (-f x) :=
    hf.aemeasurable.neg.ennreal_ofReal
  have : IsFiniteMeasure (volume.withDensity fun x => ENNReal.ofReal (f x)) :=
    isFiniteMeasure_withDensity_ofReal hf.hasFiniteIntegral
  have : IsFiniteMeasure (volume.withDensity fun x => ENNReal.ofReal (-f x)) :=
    isFiniteMeasure_withDensity_ofReal hf.neg.hasFiniteIntegral
  have heq : volume.withDensity (fun x => ENNReal.ofReal (f x)) =
      volume.withDensity (fun x => ENNReal.ofReal (-f x)) := by
    refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun F => ?_
    rw [integral_withDensity_eq_integral_toReal_smul₀ hmeas
        (ae_of_all _ fun x => ENNReal.ofReal_lt_top),
      integral_withDensity_eq_integral_toReal_smul₀ hmeas'
        (ae_of_all _ fun x => ENNReal.ofReal_lt_top)]
    simp only [ENNReal.toReal_ofReal', smul_eq_mul]
    have hi1 : Integrable (fun x => max (f x) 0 * F x) :=
      hf.pos_part.mul_bdd F.continuous.aestronglyMeasurable (ae_of_all _ F.norm_coe_le_norm)
    have hi2 : Integrable (fun x => max (-f x) 0 * F x) :=
      hf.neg.pos_part.mul_bdd F.continuous.aestronglyMeasurable (ae_of_all _ F.norm_coe_le_norm)
    have hpair : ∫ x, f x * F x = 0 := integral_mul_continuous_eq_zero hf h F.toContinuousMap
    have hdiff : (∫ x, max (f x) 0 * F x) - ∫ x, max (-f x) 0 * F x = 0 := by
      rw [← integral_sub hi1 hi2]
      have hfun : (fun x => max (f x) 0 * F x - max (-f x) 0 * F x) = fun x => f x * F x := by
        funext x
        rw [← sub_mul, max_zero_sub_max_neg_zero_eq_self]
      rw [hfun]
      exact hpair
    exact sub_eq_zero.1 hdiff
  have hfin : ∫⁻ x, ENNReal.ofReal (f x) ≠ ⊤ := by
    refine ne_top_of_le_ne_top hf.hasFiniteIntegral.ne (lintegral_mono fun x => ?_)
    exact Real.ofReal_le_enorm (f x)
  have hae := (withDensity_eq_iff hmeas hmeas' hfin).1 heq
  filter_upwards [hae] with x hx
  have h2 := congrArg ENNReal.toReal hx
  rw [ENNReal.toReal_ofReal', ENNReal.toReal_ofReal'] at h2
  have h3 := max_zero_sub_max_neg_zero_eq_self (f x)
  rw [h2, sub_self] at h3
  exact h3.symm

end Riesz1.CircleFourier

end
