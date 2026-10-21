/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Const
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Convex.Continuous
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Tactic

/-!
# The distributional Hessian of a convex function is positive semidefinite

Let `f` be convex on an open convex set `U` in a finite-dimensional real Euclidean space, and
let `φ` be a nonnegative `C²` function with compact support contained in `U`. Then, for every
vector `b`, the integral `∫ f(z) D²φ(z)(b,b) dz` is nonnegative.

The proof compares symmetric second differences of `φ` with the midpoint inequality for `f`.
A translation of the integration variable moves the difference from `φ` onto `f`, where
convexity gives a nonnegative integrand. Taylor's formula along the line `z + t b` shows that
the symmetric second difference of `φ` divided by `h²` converges uniformly to `D²φ(z)(b,b)`.
Passing to the limit gives the claim.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Riesz1

/-- Symmetric second difference of a real function, controlled by a bound on its second
derivative near the base point. -/
theorem convexOn_hessian_symdiff_bound (g g1 g2 : ℝ → ℝ)
    (hg : ∀ t, HasDerivAt g (g1 t) t) (hg1 : ∀ t, HasDerivAt g1 (g2 t) t)
    (c M R : ℝ) (hM : ∀ t, |t| ≤ R → |g2 t - c| ≤ M) (h : ℝ) (hh : |h| ≤ R) :
    |g h + g (-h) - 2 * g 0 - c * h ^ 2| ≤ 2 * M * h ^ 2 := by
  have hR0 : 0 ≤ R := (abs_nonneg h).trans hh
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 (by simpa using hR0))
  have hq' : ∀ t, HasDerivAt (fun s => g1 s - g1 0 - c * s) (g2 t - c) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => c * s) c t := by
      simpa using (hasDerivAt_id t).const_mul c
    exact (((hg1 t).sub_const (g1 0)).sub h1).congr_deriv (by ring)
  have hq : ∀ t, HasDerivAt (fun s => g s - g 0 - g1 0 * s - c * s ^ 2 / 2)
      (g1 t - g1 0 - c * t) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => g1 0 * s) (g1 0) t := by
      simpa using (hasDerivAt_id t).const_mul (g1 0)
    have h2 : HasDerivAt (fun s : ℝ => c * s ^ 2 / 2) (c * t) t := by
      have h3 := ((hasDerivAt_pow 2 t).const_mul c).div_const 2
      convert h3 using 1
      simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
      ring
    exact ((((hg t).sub_const (g 0)).sub h1).sub h2).congr_deriv (by ring)
  -- Step 1: the derivative of the remainder is at most `M |s|` near the origin.
  have step1 : ∀ s : ℝ, |s| ≤ R → |g1 s - g1 0 - c * s| ≤ M * |s| := by
    intro s hs
    have key := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun t => g1 t - g1 0 - c * t) (f' := fun t => g2 t - c) (C := M)
      (s := Set.Icc (-R) R) (x := 0) (y := s)
      (fun t _ => (hq' t).hasDerivWithinAt)
      (fun t ht => by
        rw [Real.norm_eq_abs]
        exact hM t (abs_le.mpr ht))
      (convex_Icc (-R) R) ⟨by linarith, hR0⟩ (abs_le.mp hs)
    simpa [Real.norm_eq_abs] using key
  -- Step 2: the remainder is at most `M |h| |y|` on the segment between `0` and `y`.
  have step2 : ∀ y : ℝ, |y| ≤ |h| → |g y - g 0 - g1 0 * y - c * y ^ 2 / 2| ≤ M * |h| * |y| := by
    intro y hy
    have key := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun s => g s - g 0 - g1 0 * s - c * s ^ 2 / 2)
      (f' := fun t => g1 t - g1 0 - c * t) (C := M * |h|)
      (s := Set.Icc (-|h|) |h|) (x := 0) (y := y)
      (fun t _ => (hq t).hasDerivWithinAt)
      (fun t ht => by
        rw [Real.norm_eq_abs]
        have ht' : |t| ≤ |h| := abs_le.mpr ht
        calc |g1 t - g1 0 - c * t| ≤ M * |t| := step1 t (ht'.trans hh)
          _ ≤ M * |h| := mul_le_mul_of_nonneg_left ht' hM0)
      (convex_Icc _ _) ⟨by linarith [abs_nonneg h], abs_nonneg h⟩ (abs_le.mp hy)
    simpa [Real.norm_eq_abs] using key
  -- Step 3: combine the two remainders at `h` and `-h`.
  have hh1 := step2 h le_rfl
  have hh2 := step2 (-h) (by rw [abs_neg])
  have hsq : |h| * |h| = h ^ 2 := by rw [← sq, sq_abs]
  have hid : g h + g (-h) - 2 * g 0 - c * h ^ 2 =
      (g h - g 0 - g1 0 * h - c * h ^ 2 / 2) + (g (-h) - g 0 - g1 0 * (-h) - c * (-h) ^ 2 / 2) := by
    ring
  rw [hid]
  calc |(g h - g 0 - g1 0 * h - c * h ^ 2 / 2) + (g (-h) - g 0 - g1 0 * (-h) - c * (-h) ^ 2 / 2)|
      ≤ |g h - g 0 - g1 0 * h - c * h ^ 2 / 2| +
        |g (-h) - g 0 - g1 0 * (-h) - c * (-h) ^ 2 / 2| := abs_add_le _ _
    _ ≤ M * |h| * |h| + M * |h| * |-h| := add_le_add hh1 hh2
    _ = 2 * M * h ^ 2 := by
      rw [abs_neg]
      calc M * |h| * |h| + M * |h| * |h| = 2 * M * (|h| * |h|) := by ring
        _ = 2 * M * h ^ 2 := by rw [hsq]

/-- The restriction of a `C²` function to a line has the expected first derivative. -/
theorem convexOn_hessian_hasDerivAt_line {m : ℕ} {φ : EuclideanSpace ℝ (Fin m) → ℝ}
    (hφ : ContDiff ℝ 2 φ) (z b : EuclideanSpace ℝ (Fin m)) (t : ℝ) :
    HasDerivAt (fun s : ℝ => φ (z + s • b)) (fderiv ℝ φ (z + t • b) b) t := by
  have hd : DifferentiableAt ℝ φ (z + t • b) := (hφ.differentiable (by norm_num)) _
  have hline : HasDerivAt (fun s : ℝ => z + s • b) b t := by
    simpa using ((hasDerivAt_id' t).smul_const b).const_add z
  exact hd.hasFDerivAt.comp_hasDerivAt t hline

/-- The first derivative along a line is differentiable with the expected derivative. -/
theorem convexOn_hessian_hasDerivAt_grad {m : ℕ} {φ : EuclideanSpace ℝ (Fin m) → ℝ}
    (hφ : ContDiff ℝ 2 φ) (z b : EuclideanSpace ℝ (Fin m)) (t : ℝ) :
    HasDerivAt (fun s : ℝ => fderiv ℝ φ (z + s • b) b)
      (fderiv ℝ (fderiv ℝ φ) (z + t • b) b b) t := by
  have hD : ContDiff ℝ 1 (fderiv ℝ φ) := hφ.fderiv_right (by norm_num)
  have hDd : DifferentiableAt ℝ (fderiv ℝ φ) (z + t • b) := (hD.differentiable (by norm_num)) _
  have hline : HasDerivAt (fun s : ℝ => z + s • b) b t := by
    simpa using ((hasDerivAt_id' t).smul_const b).const_add z
  have hev := (ContinuousLinearMap.apply ℝ ℝ b).hasFDerivAt.comp (z + t • b) hDd.hasFDerivAt
  exact hev.comp_hasDerivAt t hline

/-- The second derivative of a `C²` function is continuous. -/
theorem convexOn_hessian_continuous_hess {m : ℕ} {φ : EuclideanSpace ℝ (Fin m) → ℝ}
    (hφ : ContDiff ℝ 2 φ) : Continuous (fderiv ℝ (fderiv ℝ φ)) := by
  have hD : ContDiff ℝ 1 (fderiv ℝ φ) := hφ.fderiv_right (by norm_num)
  exact hD.continuous_fderiv (by norm_num)

/-- A function `f` that is continuous on an open set `U` multiplied by a continuous function `ψ`
vanishing outside a compact set `S ⊆ U` is integrable. -/
theorem convexOn_hessian_integrable {m : ℕ} {U : Set (EuclideanSpace ℝ (Fin m))}
    {f : EuclideanSpace ℝ (Fin m) → ℝ} (hfc : ContinuousOn f U)
    {S : Set (EuclideanSpace ℝ (Fin m))} (hS : IsCompact S) (hSU : S ⊆ U)
    {ψ : EuclideanSpace ℝ (Fin m) → ℝ} (hψ : Continuous ψ) (hψS : ∀ z, z ∉ S → ψ z = 0) :
    Integrable (fun z => f z * ψ z) := by
  have hsupp : Function.support (fun z => f z * ψ z) ⊆ S := by
    intro z hz
    by_contra hzS
    exact hz (by simp [hψS z hzS])
  rw [← integrableOn_iff_integrable_of_support_subset hsupp]
  exact ContinuousOn.integrableOn_compact hS ((hfc.mono hSU).mul hψ.continuousOn)

/-- Uniform second-order Taylor estimate: the symmetric second difference of `φ` at `z` in the
direction `b`, divided by `h²`, is within `η` of `D²φ(z)(b,b)`, uniformly in `z`. -/
theorem convexOn_hessian_uniform {m : ℕ} {φ : EuclideanSpace ℝ (Fin m) → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) (b : EuclideanSpace ℝ (Fin m))
    {η : ℝ} (hη : 0 < η) :
    ∃ R > 0, ∀ h : ℝ, |h| ≤ R → ∀ z : EuclideanSpace ℝ (Fin m),
      |φ (z + h • b) + φ (z - h • b) - 2 * φ z - h ^ 2 * fderiv ℝ (fderiv ℝ φ) z b b|
        ≤ η * h ^ 2 := by
  have hUC : UniformContinuous (fderiv ℝ (fderiv ℝ φ)) :=
    ((hφc.fderiv ℝ).fderiv ℝ).uniformContinuous_of_continuous (convexOn_hessian_continuous_hess hφ)
  set ε : ℝ := η / (2 * (‖b‖ ^ 2 + 1)) with hε
  have hεpos : 0 < ε := by positivity
  have hεeq : ε * (2 * (‖b‖ ^ 2 + 1)) = η := div_mul_cancel₀ η (by positivity)
  have hUCε : ∀ ε' > 0, ∃ δ' > 0, ∀ {a c : EuclideanSpace ℝ (Fin m)}, dist a c < δ' →
      dist (fderiv ℝ (fderiv ℝ φ) a) (fderiv ℝ (fderiv ℝ φ) c) < ε' :=
    Metric.uniformContinuous_iff.mp hUC
  obtain ⟨δ, hδ, hδD⟩ := hUCε ε hεpos
  set R : ℝ := δ / (2 * (‖b‖ + 1)) with hR
  have hRpos : 0 < R := by positivity
  -- The second derivative along the segment from `z` stays within `ε` of its value at `z`.
  have hM : ∀ z : EuclideanSpace ℝ (Fin m), ∀ t : ℝ, |t| ≤ R →
      |fderiv ℝ (fderiv ℝ φ) (z + t • b) b b - fderiv ℝ (fderiv ℝ φ) z b b| ≤ ε * ‖b‖ ^ 2 := by
    intro z t ht
    have hdist : dist (z + t • b) z < δ := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
      have h1 : |t| * ‖b‖ ≤ R * ‖b‖ := mul_le_mul_of_nonneg_right ht (norm_nonneg b)
      have h2 : R * ‖b‖ < δ := by
        rw [hR, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith [norm_nonneg b]
      linarith
    have hA : ‖fderiv ℝ (fderiv ℝ φ) (z + t • b) - fderiv ℝ (fderiv ℝ φ) z‖ < ε :=
      (dist_eq_norm (fderiv ℝ (fderiv ℝ φ) (z + t • b)) (fderiv ℝ (fderiv ℝ φ) z)).symm.trans_lt
        (hδD hdist)
    have hAb : fderiv ℝ (fderiv ℝ φ) (z + t • b) b b - fderiv ℝ (fderiv ℝ φ) z b b
        = (fderiv ℝ (fderiv ℝ φ) (z + t • b) - fderiv ℝ (fderiv ℝ φ) z) b b := by
      simp
    rw [hAb, ← Real.norm_eq_abs]
    calc ‖(fderiv ℝ (fderiv ℝ φ) (z + t • b) - fderiv ℝ (fderiv ℝ φ) z) b b‖
        ≤ ‖(fderiv ℝ (fderiv ℝ φ) (z + t • b) - fderiv ℝ (fderiv ℝ φ) z) b‖ * ‖b‖ :=
          ((fderiv ℝ (fderiv ℝ φ) (z + t • b) - fderiv ℝ (fderiv ℝ φ) z) b).le_opNorm b
      _ ≤ (‖fderiv ℝ (fderiv ℝ φ) (z + t • b) - fderiv ℝ (fderiv ℝ φ) z‖ * ‖b‖) * ‖b‖ :=
          mul_le_mul_of_nonneg_right
            ((fderiv ℝ (fderiv ℝ φ) (z + t • b) - fderiv ℝ (fderiv ℝ φ) z).le_opNorm b)
            (norm_nonneg b)
      _ ≤ (ε * ‖b‖) * ‖b‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hA.le (norm_nonneg b))
            (norm_nonneg b)
      _ = ε * ‖b‖ ^ 2 := by ring
  refine ⟨R, hRpos, fun h hh z => ?_⟩
  have hsymm := convexOn_hessian_symdiff_bound (fun s => φ (z + s • b))
    (fun s => fderiv ℝ φ (z + s • b) b) (fun s => fderiv ℝ (fderiv ℝ φ) (z + s • b) b b)
    (fun t => convexOn_hessian_hasDerivAt_line hφ z b t)
    (fun t => convexOn_hessian_hasDerivAt_grad hφ z b t)
    (fderiv ℝ (fderiv ℝ φ) z b b) (ε * ‖b‖ ^ 2) R (fun t ht => hM z t ht) h hh
  have e1 : z + (-h) • b = z - h • b := by rw [neg_smul, sub_eq_add_neg]
  have e0 : z + (0 : ℝ) • b = z := by simp
  simp only [e1, e0] at hsymm
  have hb : 2 * (ε * ‖b‖ ^ 2) * h ^ 2 ≤ η * h ^ 2 := by
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg h)
    nlinarith [hεeq, hεpos, sq_nonneg ‖b‖]
  have hfin : |φ (z + h • b) + φ (z - h • b) - 2 * φ z - h ^ 2 * fderiv ℝ (fderiv ℝ φ) z b b|
      ≤ 2 * (ε * ‖b‖ ^ 2) * h ^ 2 := by
    rw [mul_comm (h ^ 2)]
    exact hsymm
  exact hfin.trans hb

/-- **Distributional Hessian of a convex function.** Let `f` be convex on an open convex set `U`,
and let `φ` be a nonnegative `C²` function with compact support contained in `U`. Then the
integral of `f(z) D²φ(z)(b,b)` over `z` is nonnegative for every vector `b`. -/
theorem convexOn_distributional_hessian_nonneg {m : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin m))} (hUo : IsOpen U) (_hUc : Convex ℝ U)
    {f : EuclideanSpace ℝ (Fin m) → ℝ} (hf : ConvexOn ℝ U f)
    {φ : EuclideanSpace ℝ (Fin m) → ℝ} (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U) (hφ0 : ∀ z, 0 ≤ φ z) (b : EuclideanSpace ℝ (Fin m)) :
    0 ≤ ∫ z, f z * fderiv ℝ (fderiv ℝ φ) z b b := by
  obtain ⟨ε₀, hε₀, hK'U⟩ := hφc.isCompact.exists_cthickening_subset_open hUo hφU
  set K := tsupport φ with hKdef
  set K' := Metric.cthickening ε₀ K with hK'def
  have hK : IsCompact K := hφc.isCompact
  have hK'c : IsCompact K' := hK.cthickening
  have hKK' : K ⊆ K' := Metric.self_subset_cthickening K
  have hφcont : Continuous φ := hφ.continuous
  have hD2c : Continuous (fun z => fderiv ℝ (fderiv ℝ φ) z b b) :=
    ((convexOn_hessian_continuous_hess hφ).clm_apply continuous_const).clm_apply continuous_const
  have hfc : ContinuousOn f U := hf.continuousOn hUo
  obtain ⟨Mf, hMf⟩ := hK'c.exists_bound_of_continuousOn (hfc.mono hK'U)
  set M : ℝ := max Mf 0 with hMdef
  have hM0 : 0 ≤ M := le_max_right _ _
  have hMbound : ∀ z ∈ K', ‖f z‖ ≤ M := fun z hz => (hMf z hz).trans (le_max_left _ _)
  -- Points within distance `ε₀` of `K` lie in `K'`.
  have hmemK' : ∀ w ∈ K, ∀ z : EuclideanSpace ℝ (Fin m), ‖z - w‖ ≤ ε₀ → z ∈ K' := by
    intro w hw z hz
    exact Metric.mem_cthickening_of_dist_le z w ε₀ K hw (by rwa [dist_eq_norm])
  have hshift : ∀ v : EuclideanSpace ℝ (Fin m), ‖v‖ ≤ ε₀ → ∀ w ∈ K, w + v ∈ K' ∧ w - v ∈ K' := by
    intro v hv w hw
    refine ⟨hmemK' w hw _ ?_, hmemK' w hw _ ?_⟩
    · simpa using hv
    · simpa using hv
  have hφout : ∀ z, z ∉ K' → φ z = 0 :=
    fun z hz => image_eq_zero_of_notMem_tsupport (fun hzK => hz (hKK' hzK))
  -- Outside `K'`, the functions `φ(· ± v)` and `D²φ` vanish.
  have hout : ∀ v : EuclideanSpace ℝ (Fin m), ‖v‖ ≤ ε₀ → ∀ z, z ∉ K' →
      φ (z + v) = 0 ∧ φ (z - v) = 0 ∧ φ z = 0 := by
    intro v hv z hz
    refine ⟨image_eq_zero_of_notMem_tsupport (fun hzK => hz (hmemK' (z + v) hzK z ?_)),
      image_eq_zero_of_notMem_tsupport (fun hzK => hz (hmemK' (z - v) hzK z ?_)),
      hφout z hz⟩
    · simpa [norm_neg] using hv
    · simpa using hv
  have hD2out : ∀ z, z ∉ K' → fderiv ℝ (fderiv ℝ φ) z = 0 := by
    intro z hz
    apply image_eq_zero_of_notMem_tsupport
    intro hzK
    have hsub1 : tsupport (fderiv ℝ (fderiv ℝ φ)) ⊆ tsupport (fderiv ℝ φ) :=
      tsupport_fderiv_subset ℝ
    have hsub2 : tsupport (fderiv ℝ φ) ⊆ tsupport φ := tsupport_fderiv_subset ℝ
    exact hz (hKK' (hsub2 (hsub1 hzK)))
  -- Nonnegativity of the second symmetric difference, after translating `φ` onto `f`.
  have hnonneg : ∀ v : EuclideanSpace ℝ (Fin m), ‖v‖ ≤ ε₀ →
      0 ≤ ∫ z, f z * (φ (z + v) + φ (z - v) - 2 * φ z) := by
    intro v hv
    have hIp : Integrable (fun z => f z * φ (z + v)) :=
      convexOn_hessian_integrable hfc hK'c hK'U (hφcont.comp (continuous_id.add continuous_const))
        (fun z hz => (hout v hv z hz).1)
    have hIm : Integrable (fun z => f z * φ (z - v)) :=
      convexOn_hessian_integrable hfc hK'c hK'U (hφcont.comp (continuous_id.sub continuous_const))
        (fun z hz => (hout v hv z hz).2.1)
    have hI₀ : Integrable (fun z => f z * φ z) :=
      convexOn_hessian_integrable hfc hK'c hK'U hφcont (fun z hz => by simp [hφout z hz])
    have eA : ∫ z, f z * φ (z + v) = ∫ w, f (w - v) * φ w := by
      have := integral_add_right_eq_self (μ := (volume : Measure (EuclideanSpace ℝ (Fin m))))
        (fun w => f (w - v) * φ w) v
      simpa using this
    have eC : ∫ z, f z * φ (z - v) = ∫ w, f (w + v) * φ w := by
      have := integral_sub_right_eq_self (μ := (volume : Measure (EuclideanSpace ℝ (Fin m))))
        (fun w => f (w + v) * φ w) v
      simpa using this
    have hA : Integrable (fun w => f (w - v) * φ w) := by
      have := hIp.comp_sub_right v
      simpa using this
    have hC : Integrable (fun w => f (w + v) * φ w) := by
      have := hIm.comp_add_right v
      simpa using this
    have hdec : ∫ z, f z * (φ (z + v) + φ (z - v) - 2 * φ z)
        = ∫ w, (f (w - v) * φ w + f (w + v) * φ w - 2 * (f w * φ w)) := by
      have h1 : ∫ z, f z * (φ (z + v) + φ (z - v) - 2 * φ z)
          = ∫ z, (f z * φ (z + v) + f z * φ (z - v) - 2 * (f z * φ z)) := by
        congr 1
        ext z
        ring
      have hIs : Integrable (fun z => f z * φ (z + v) + f z * φ (z - v)) := hIp.add hIm
      have hI2 : Integrable (fun z => 2 * (f z * φ z)) := hI₀.const_mul 2
      have hAs : Integrable (fun w => f (w - v) * φ w + f (w + v) * φ w) := hA.add hC
      rw [h1, integral_sub hIs hI2, integral_add hIp hIm, integral_const_mul, eA, eC]
      rw [integral_sub hAs hI2, integral_add hA hC, integral_const_mul]
    rw [hdec]
    apply integral_nonneg
    intro w
    show (0 : ℝ) ≤ f (w - v) * φ w + f (w + v) * φ w - 2 * (f w * φ w)
    by_cases hw : w ∈ K
    · have hp : w + v ∈ U := hK'U ((hshift v hv w hw).1)
      have hm : w - v ∈ U := hK'U ((hshift v hv w hw).2)
      have hmid := hf.2 hp hm (by norm_num : (0:ℝ) ≤ 1 / 2) (by norm_num : (0:ℝ) ≤ 1 / 2)
        (by norm_num)
      have hc : (1 / 2 : ℝ) • (w + v) + (1 / 2 : ℝ) • (w - v) = w := by module
      rw [hc, smul_eq_mul, smul_eq_mul] at hmid
      have hbr : 0 ≤ f (w - v) + f (w + v) - 2 * f w := by linarith
      have hfac : f (w - v) * φ w + f (w + v) * φ w - 2 * (f w * φ w)
          = φ w * (f (w - v) + f (w + v) - 2 * f w) := by ring
      rw [hfac]
      exact mul_nonneg (hφ0 w) hbr
    · have h0 : φ w = 0 := image_eq_zero_of_notMem_tsupport hw
      simp [h0]
  -- Shifts of size at most `ε₀ / (‖b‖ + 1)` have norm at most `ε₀` after scaling by `b`.
  have hvb : ∀ h : ℝ, |h| ≤ ε₀ / (‖b‖ + 1) → ‖h • b‖ ≤ ε₀ := by
    intro h hh
    rw [norm_smul, Real.norm_eq_abs]
    have h1 : |h| * (‖b‖ + 1) ≤ ε₀ := (le_div_iff₀ (by positivity)).mp hh
    nlinarith [abs_nonneg h, norm_nonneg b]
  -- The difference quotient is close to `L` for small steps, with an explicit bound.
  have hclaim : ∀ η : ℝ, 0 < η → ∃ R > 0, ∀ h : ℝ, |h| ≤ R →
      |(∫ z, f z * (φ (z + h • b) + φ (z - h • b) - 2 * φ z))
        - h ^ 2 * ∫ z, f z * fderiv ℝ (fderiv ℝ φ) z b b| ≤ η * h ^ 2 := by
    intro η hη
    set V : ℝ := (volume K').toReal with hVdef
    have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
    set η' : ℝ := η / (M * V + 1) with hη'def
    have hMV0 : 0 ≤ M * V := mul_nonneg hM0 hV0
    have hη'pos : 0 < η' := div_pos hη (by linarith)
    have hη'eq : η' * (M * V + 1) = η := div_mul_cancel₀ η (by linarith)
    have hMV : M * η' * V ≤ η := by nlinarith
    obtain ⟨R₁, hR₁, hR₁b⟩ := convexOn_hessian_uniform hφ hφc b hη'pos
    have hR₀ : 0 < ε₀ / (‖b‖ + 1) := by positivity
    refine ⟨min R₁ (ε₀ / (‖b‖ + 1)), lt_min hR₁ hR₀, fun h hh => ?_⟩
    have hhR₁ : |h| ≤ R₁ := hh.trans (min_le_left _ _)
    have hhR₀ : |h| ≤ ε₀ / (‖b‖ + 1) := hh.trans (min_le_right _ _)
    have hvh := hvb h hhR₀
    have hIΔ : Integrable (fun z => f z * (φ (z + h • b) + φ (z - h • b) - 2 * φ z)) := by
      refine convexOn_hessian_integrable hfc hK'c hK'U ?_ ?_
      · fun_prop
      · intro z hz
        obtain ⟨h1, h2, h3⟩ := hout (h • b) hvh z hz
        simp [h1, h2, h3]
    have hID : Integrable (fun z => f z * fderiv ℝ (fderiv ℝ φ) z b b) :=
      convexOn_hessian_integrable hfc hK'c hK'U hD2c (fun z hz => by simp [hD2out z hz])
    have hdiff : (∫ z, f z * (φ (z + h • b) + φ (z - h • b) - 2 * φ z))
        - h ^ 2 * ∫ z, f z * fderiv ℝ (fderiv ℝ φ) z b b
        = ∫ z, f z * (φ (z + h • b) + φ (z - h • b) - 2 * φ z
            - h ^ 2 * fderiv ℝ (fderiv ℝ φ) z b b) := by
      have h1 : ∫ z, f z * (φ (z + h • b) + φ (z - h • b) - 2 * φ z
            - h ^ 2 * fderiv ℝ (fderiv ℝ φ) z b b)
          = ∫ z, (f z * (φ (z + h • b) + φ (z - h • b) - 2 * φ z)
            - h ^ 2 * (f z * fderiv ℝ (fderiv ℝ φ) z b b)) := by
        congr 1
        ext z
        ring
      have hI2 : Integrable (fun z => h ^ 2 * (f z * fderiv ℝ (fderiv ℝ φ) z b b)) :=
        hID.const_mul (h ^ 2)
      rw [h1, integral_sub hIΔ hI2, integral_const_mul]
    rw [hdiff, ← Real.norm_eq_abs]
    have hbound : ‖∫ z, f z * (φ (z + h • b) + φ (z - h • b) - 2 * φ z
            - h ^ 2 * fderiv ℝ (fderiv ℝ φ) z b b)‖
        ≤ ∫ z, K'.indicator (fun _ => M * (η' * h ^ 2)) z := by
      apply norm_integral_le_of_norm_le
      · exact (integrableOn_const hK'c.measure_lt_top.ne).integrable_indicator hK'c.measurableSet
      · refine Filter.Eventually.of_forall (fun z => ?_)
        by_cases hz : z ∈ K'
        · rw [Set.indicator_of_mem hz, norm_mul]
          have h1 := hR₁b h hhR₁ z
          rw [Real.norm_eq_abs]
          exact mul_le_mul (hMbound z hz) h1 (norm_nonneg _) hM0
        · obtain ⟨h1, h2, h3⟩ := hout (h • b) hvh z hz
          have h4 := hD2out z hz
          simp [h1, h2, h3, h4, hz]
    have hint : ∫ z, K'.indicator (fun _ => M * (η' * h ^ 2)) z = M * (η' * h ^ 2) * V := by
      rw [integral_indicator_const _ hK'c.measurableSet, smul_eq_mul, mul_comm]
      rfl
    calc ‖∫ z, f z * (φ (z + h • b) + φ (z - h • b) - 2 * φ z
            - h ^ 2 * fderiv ℝ (fderiv ℝ φ) z b b)‖
        ≤ ∫ z, K'.indicator (fun _ => M * (η' * h ^ 2)) z := hbound
      _ = M * (η' * h ^ 2) * V := hint
      _ = (M * η' * V) * h ^ 2 := by ring
      _ ≤ η * h ^ 2 := mul_le_mul_of_nonneg_right hMV (sq_nonneg h)
  -- Conclusion: a negative integral would contradict the two estimates at a small step `h`.
  by_contra hneg
  have hneg' : ∫ z, f z * fderiv ℝ (fderiv ℝ φ) z b b < 0 := not_le.mp hneg
  obtain ⟨R, hR, hRb⟩ := hclaim (-(∫ z, f z * fderiv ℝ (fderiv ℝ φ) z b b) / 2) (by linarith)
  set h : ℝ := min R (ε₀ / (‖b‖ + 1)) with hhdef
  have hpos : 0 < h := lt_min hR (by positivity)
  have hh1 : |h| ≤ R := by rw [abs_of_pos hpos]; exact min_le_left _ _
  have hh2 : |h| ≤ ε₀ / (‖b‖ + 1) := by rw [abs_of_pos hpos]; exact min_le_right _ _
  have hnn := hnonneg (h • b) (hvb h hh2)
  have hup := (abs_le.mp (hRb h hh1)).2
  have hh2pos : 0 < h ^ 2 := by positivity
  nlinarith [mul_pos hh2pos (neg_pos.mpr hneg')]

end Riesz1
