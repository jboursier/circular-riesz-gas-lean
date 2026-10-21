/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.ConvexityHessianFiber
public import Riesz1.ToMathlib.Calculus.ConvexLineHessian
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Derivatives of the zero extension along a line in the retained variables

Let `Q ⊆ ℝ^m × ℝ^n` be open, let `K` be `C²` on `Q`, and let `b ∈ ℝ^m`. Write
`∂K(p) = DK(p)(b, 0)` and `∂²K(p) = D²K(p)((b, 0), (b, 0))`. For a point `(w, y)` the zero
extension of `e^{-K}` along the line `s ↦ (w + s b, y)` has the following derivatives.

* `firstCoef Q K b p = -e^{-K(p)} ∂K(p)` on `Q`, and `0` off `Q`, is the first derivative.
* `secondCoef Q K b p = e^{-K(p)} ((∂K(p))² - ∂²K(p))` on `Q`, and `0` off `Q`, is the second
  derivative at the base point.

Off `Q` the zero extension vanishes near the point when the point lies outside the closure of
`Q`. The remaining points, on the boundary of `Q`, form a null set of `y` for a fixed projected
point, by `measure_slice_closure_diff_eq_zero`. Hence the derivative formulas hold for almost
every `y`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology

namespace Riesz1.ConvexityHessian

variable {m n : ℕ}

/-- The first-order coefficient `-e^{-K} ∂_b K` of the zero extension of `e^{-K}`, on `Q`. -/
def firstCoef (Q : Set (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)))
    (K : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n) → ℝ)
    (b : EuclideanSpace ℝ (Fin m))
    (p : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) : ℝ :=
  Q.indicator (fun q => -(Real.exp (-K q) * fderiv ℝ K q (b, 0))) p

/-- The second-order coefficient `e^{-K} ((∂_b K)² - ∂_b² K)` of the zero extension, on `Q`. -/
def secondCoef (Q : Set (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)))
    (K : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n) → ℝ)
    (b : EuclideanSpace ℝ (Fin m))
    (p : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) : ℝ :=
  Q.indicator (fun q => Real.exp (-K q) *
    (fderiv ℝ K q (b, 0) ^ 2 - fderiv ℝ (fderiv ℝ K) q (b, 0) (b, 0))) p

variable {Q : Set (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n))}
  {K : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n) → ℝ}
  (b : EuclideanSpace ℝ (Fin m))

/-- The point on the line `s ↦ (z + s b, y)` is the translate of `(z, y)` by `s (b, 0)`. -/
theorem line_eq_add (z : EuclideanSpace ℝ (Fin m)) (y : EuclideanSpace ℝ (Fin n)) (s : ℝ) :
    (z + s • b, y) = (z, y) + s • ((b, 0) : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) := by
  ext <;> simp

/-- The line `s ↦ (z + s b, y)` stays in `Q` near a parameter `t₀` where it lies in `Q`. -/
theorem eventually_mem_line {z : EuclideanSpace ℝ (Fin m)} {y : EuclideanSpace ℝ (Fin n)}
    (hQo : IsOpen Q) {t₀ : ℝ} (hmem : (z + t₀ • b, y) ∈ Q) :
    ∀ᶠ s in 𝓝 t₀, (z + s • b, y) ∈ Q :=
  (hQo.preimage (by fun_prop : Continuous fun s : ℝ => (z + s • b, y))).mem_nhds hmem

theorem differentiableAt_K (hQo : IsOpen Q) (hK : ContDiffOn ℝ 2 K Q) {p : _ × _} (hp : p ∈ Q) :
    DifferentiableAt ℝ K p :=
  (hK.differentiableOn (by norm_num)).differentiableAt (hQo.mem_nhds hp)

/-- Along the line `s ↦ (z + s b, y)`, `K` has derivative `DK(·)(b, 0)`. -/
theorem hasDerivAt_K_line (hQo : IsOpen Q) (hK : ContDiffOn ℝ 2 K Q)
    (z : EuclideanSpace ℝ (Fin m)) (y : EuclideanSpace ℝ (Fin n)) {t₀ : ℝ}
    (hmem : (z + t₀ • b, y) ∈ Q) :
    HasDerivAt (fun s : ℝ => K (z + s • b, y)) (fderiv ℝ K (z + t₀ • b, y) (b, 0)) t₀ := by
  have hfun : (fun s : ℝ => K (z + s • b, y)) =
      fun s : ℝ => K ((z, y) + s • ((b, 0) : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n))) :=
    funext fun s => by rw [line_eq_add]
  have hp : (z, y) + t₀ • ((b, 0) : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) =
      (z + t₀ • b, y) := (line_eq_add b z y t₀).symm
  rw [hfun, ← hp]
  exact hasDerivAt_comp_line (by rw [hp]; exact differentiableAt_K hQo hK hmem)

/-- The exponential of `-K` along the line `s ↦ (z + s b, y)`. -/
theorem hasDerivAt_exp_line (hQo : IsOpen Q) (hK : ContDiffOn ℝ 2 K Q)
    (z : EuclideanSpace ℝ (Fin m)) (y : EuclideanSpace ℝ (Fin n)) {t₀ : ℝ}
    (hmem : (z + t₀ • b, y) ∈ Q) :
    HasDerivAt (fun s : ℝ => Real.exp (-K (z + s • b, y)))
      (Real.exp (-K (z + t₀ • b, y)) * -fderiv ℝ K (z + t₀ • b, y) (b, 0)) t₀ :=
  HasDerivAt.exp (hasDerivAt_K_line b hQo hK z y hmem).neg

/-- The derivative `∂K` along the line `s ↦ (z + s b, y)` is `D²K(·)((b, 0), (b, 0))`. -/
theorem hasDerivAt_dK_line (hQo : IsOpen Q) (hK : ContDiffOn ℝ 2 K Q)
    (z : EuclideanSpace ℝ (Fin m)) (y : EuclideanSpace ℝ (Fin n)) {t₀ : ℝ}
    (hmem : (z + t₀ • b, y) ∈ Q) :
    HasDerivAt (fun s : ℝ => fderiv ℝ K (z + s • b, y) (b, 0))
      (fderiv ℝ (fderiv ℝ K) (z + t₀ • b, y) (b, 0) (b, 0)) t₀ := by
  have hK1 : ContDiffOn ℝ 1 (fderiv ℝ K) Q := hK.fderiv_of_isOpen hQo (m := 1) (by norm_num)
  have hdiff : DifferentiableAt ℝ (fderiv ℝ K)
      ((z, y) + t₀ • ((b, 0) : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n))) := by
    rw [← line_eq_add b z y t₀]
    exact (hK1.differentiableOn (by norm_num)).differentiableAt (hQo.mem_nhds hmem)
  have hfun : (fun s : ℝ => fderiv ℝ K (z + s • b, y) (b, 0)) =
      fun s : ℝ => fderiv ℝ K ((z, y) + s • ((b, 0) : EuclideanSpace ℝ (Fin m) ×
        EuclideanSpace ℝ (Fin n))) (b, 0) :=
    funext fun s => by rw [line_eq_add]
  rw [hfun, line_eq_add b z y t₀]
  exact hasDerivAt_fderiv_comp_line_at hdiff

/-- Near a parameter where the line lies in `Q`, the zero extension equals `e^{-K}`. -/
theorem eventually_zeroExtension_eq_exp (hQo : IsOpen Q) {z : EuclideanSpace ℝ (Fin m)}
    {y : EuclideanSpace ℝ (Fin n)} {t₀ : ℝ} (hmem : (z + t₀ • b, y) ∈ Q) :
    (fun s : ℝ => zeroExtension Q K (z + s • b, y)) =ᶠ[𝓝 t₀]
      fun s : ℝ => Real.exp (-K (z + s • b, y)) := by
  filter_upwards [eventually_mem_line b hQo hmem] with s hs
  exact zeroExtension_of_mem hs

/-- The first derivative of the zero extension along the line, at a point of `Q`. -/
theorem hasDerivAt_zeroExtension_line_of_mem (hQo : IsOpen Q) (hK : ContDiffOn ℝ 2 K Q)
    (z : EuclideanSpace ℝ (Fin m)) (y : EuclideanSpace ℝ (Fin n)) {t₀ : ℝ}
    (hmem : (z + t₀ • b, y) ∈ Q) :
    HasDerivAt (fun s : ℝ => zeroExtension Q K (z + s • b, y))
      (firstCoef Q K b (z + t₀ • b, y)) t₀ := by
  refine ((hasDerivAt_exp_line b hQo hK z y hmem).congr_of_eventuallyEq
    (eventually_zeroExtension_eq_exp b hQo hmem)).congr_deriv ?_
  unfold firstCoef
  rw [Set.indicator_of_mem hmem]
  ring

/-- The first derivative of the zero extension along the line, at a point outside the closure
of `Q`, is zero. -/
theorem hasDerivAt_zeroExtension_line_of_notMem (z : EuclideanSpace ℝ (Fin m))
    (y : EuclideanSpace ℝ (Fin n)) {t₀ : ℝ} (hnot : (z + t₀ • b, y) ∉ closure Q) :
    HasDerivAt (fun s : ℝ => zeroExtension Q K (z + s • b, y))
      (firstCoef Q K b (z + t₀ • b, y)) t₀ := by
  have hopen : IsOpen {s : ℝ | (z + s • b, y) ∉ closure Q} :=
    (isClosed_closure.preimage (by fun_prop : Continuous fun s : ℝ => (z + s • b, y))).isOpen_compl
  have hev : (fun s : ℝ => zeroExtension Q K (z + s • b, y)) =ᶠ[𝓝 t₀] fun _ => (0 : ℝ) := by
    filter_upwards [hopen.mem_nhds (x := t₀) hnot] with s hs
    exact zeroExtension_of_notMem fun h => hs (subset_closure h)
  have hval : firstCoef Q K b (z + t₀ • b, y) = 0 :=
    Set.indicator_of_notMem (fun h => hnot (subset_closure h)) _
  rw [hval]
  exact (hasDerivAt_const t₀ (0 : ℝ)).congr_of_eventuallyEq hev

/-- For almost every `y`, the first derivative of the zero extension along the line through `z`
at parameter `t₀` is `firstCoef`, whenever `z + t₀ b` projects into the projected interior. -/
theorem ae_hasDerivAt_zeroExtension_line (hQo : IsOpen Q) (hQc : Convex ℝ Q)
    (hK : ContDiffOn ℝ 2 K Q) (z : EuclideanSpace ℝ (Fin m)) {t₀ : ℝ}
    (hz : z + t₀ • b ∈ Prod.fst '' Q) :
    ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      HasDerivAt (fun s : ℝ => zeroExtension Q K (z + s • b, y))
        (firstCoef Q K b (z + t₀ • b, y)) t₀ := by
  filter_upwards [ae_mem_or_notMem_closure hQo hQc hz] with y hy
  rcases hy with h | h
  · exact hasDerivAt_zeroExtension_line_of_mem b hQo hK z y h
  · exact hasDerivAt_zeroExtension_line_of_notMem b z y h

/-- The first-order coefficient is continuous on `Q`. -/
theorem continuousOn_firstCoef_fun (hQo : IsOpen Q) (hK : ContDiffOn ℝ 2 K Q) :
    ContinuousOn (fun q => -(Real.exp (-K q) * fderiv ℝ K q (b, 0))) Q := by
  have hdK : ContinuousOn (fun q => fderiv ℝ K q (b, 0)) Q :=
    (hK.continuousOn_fderiv_of_isOpen hQo (by norm_num)).clm_apply continuousOn_const
  exact ((Real.continuous_exp.comp_continuousOn hK.continuousOn.neg).mul hdK).neg

/-- The second-order coefficient is continuous on `Q`. -/
theorem continuousOn_secondCoef_fun (hQo : IsOpen Q) (hK : ContDiffOn ℝ 2 K Q) :
    ContinuousOn (fun q => Real.exp (-K q) *
      (fderiv ℝ K q (b, 0) ^ 2 - fderiv ℝ (fderiv ℝ K) q (b, 0) (b, 0))) Q := by
  have hK1 : ContDiffOn ℝ 1 (fderiv ℝ K) Q := hK.fderiv_of_isOpen hQo (m := 1) (by norm_num)
  have hdK : ContinuousOn (fun q => fderiv ℝ K q (b, 0)) Q :=
    (hK.continuousOn_fderiv_of_isOpen hQo (by norm_num)).clm_apply continuousOn_const
  have hddK : ContinuousOn (fun q => fderiv ℝ (fderiv ℝ K) q (b, 0) (b, 0)) Q :=
    ((hK1.continuousOn_fderiv_of_isOpen hQo (by norm_num)).clm_apply continuousOn_const).clm_apply
      continuousOn_const
  exact (Real.continuous_exp.comp_continuousOn hK.continuousOn.neg).mul
    ((hdK.pow 2).sub hddK)

/-- The first-order coefficient is a.e. strongly measurable in `y`. -/
theorem aestronglyMeasurable_firstCoef (hQo : IsOpen Q) (hK : ContDiffOn ℝ 2 K Q)
    (z : EuclideanSpace ℝ (Fin m)) :
    AEStronglyMeasurable (fun y => firstCoef Q K b (z, y)) volume :=
  aestronglyMeasurable_indicator_slice hQo (continuousOn_firstCoef_fun b hQo hK) z

/-- The second-order coefficient is a.e. strongly measurable in `y`. -/
theorem aestronglyMeasurable_secondCoef (hQo : IsOpen Q) (hK : ContDiffOn ℝ 2 K Q)
    (z : EuclideanSpace ℝ (Fin m)) :
    AEStronglyMeasurable (fun y => secondCoef Q K b (z, y)) volume :=
  aestronglyMeasurable_indicator_slice hQo (continuousOn_secondCoef_fun b hQo hK) z

/-- The second derivative of the zero extension at the base point, for almost every `y`: the
function `s ↦ d/ds (zeroExtension (z + s b, y))` has derivative `secondCoef` at `s = 0`. -/
theorem ae_hasDerivAt_deriv_zeroExtension_line (hQo : IsOpen Q) (hQc : Convex ℝ Q)
    (hK : ContDiffOn ℝ 2 K Q) (z : EuclideanSpace ℝ (Fin m)) (hz : z ∈ Prod.fst '' Q) :
    ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      HasDerivAt (fun s : ℝ => deriv (fun t : ℝ => zeroExtension Q K (z + t • b, y)) s)
        (secondCoef Q K b (z, y)) 0 := by
  have hz0 : z + (0 : ℝ) • b ∈ Prod.fst '' Q := by simpa using hz
  filter_upwards [ae_mem_or_notMem_closure hQo hQc hz] with y hy
  have hmem0 : (z + (0 : ℝ) • b, y) ∈ Q ∨ (z + (0 : ℝ) • b, y) ∉ closure Q := by
    simpa using hy
  rcases hmem0 with h | h
  · -- The point lies in `Q`: the zero extension is `e^{-K}` near the base point.
    have hd1 : deriv (fun t : ℝ => zeroExtension Q K (z + t • b, y)) =ᶠ[𝓝 0]
        deriv (fun t : ℝ => Real.exp (-K (z + t • b, y))) :=
      (eventually_zeroExtension_eq_exp b hQo h).deriv
    have hd2 : deriv (fun t : ℝ => Real.exp (-K (z + t • b, y))) =ᶠ[𝓝 0]
        fun t : ℝ => Real.exp (-K (z + t • b, y)) * -fderiv ℝ K (z + t • b, y) (b, 0) := by
      filter_upwards [eventually_mem_line b hQo h] with t ht
      exact (hasDerivAt_exp_line b hQo hK z y ht).deriv
    have hg := (hasDerivAt_exp_line b hQo hK z y h).mul
      (hasDerivAt_dK_line b hQo hK z y h).neg
    have h' : (z, y) ∈ Q := by simpa using h
    refine (hg.congr_deriv ?_).congr_of_eventuallyEq (hd1.trans hd2)
    simp only [zero_smul, add_zero, Pi.neg_apply]
    unfold secondCoef
    rw [Set.indicator_of_mem h']
    ring
  · -- The point lies outside the closure: the zero extension vanishes near the base point.
    have hev : (fun t : ℝ => zeroExtension Q K (z + t • b, y)) =ᶠ[𝓝 0] fun _ => (0 : ℝ) := by
      have hopen : IsOpen {t : ℝ | (z + t • b, y) ∉ closure Q} :=
        (isClosed_closure.preimage (by fun_prop : Continuous fun t : ℝ => (z + t • b, y))).isOpen_compl
      have h0 : (0 : ℝ) ∈ {t : ℝ | (z + t • b, y) ∉ closure Q} := by simpa using h
      filter_upwards [hopen.mem_nhds h0] with t ht
      exact zeroExtension_of_notMem fun hq => ht (subset_closure hq)
    have hd : (fun s : ℝ => deriv (fun t : ℝ => zeroExtension Q K (z + t • b, y)) s) =ᶠ[𝓝 0]
        fun _ => (0 : ℝ) := by
      filter_upwards [hev.deriv] with s hs
      simpa using hs
    have hval : secondCoef Q K b (z, y) = 0 := by
      have hnot : (z, y) ∉ Q := fun hq => h (subset_closure (by simpa using hq))
      exact Set.indicator_of_notMem hnot _
    rw [hval]
    exact (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq hd

end Riesz1.ConvexityHessian

end

end
