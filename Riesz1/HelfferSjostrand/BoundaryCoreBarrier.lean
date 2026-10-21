/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.InteriorRegularityRealEnergy
public import Riesz1.ToMathlib.BoundaryBarrierLimit
public import Mathlib.Topology.Order.Compact
public import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# Positive-part distance cutoffs for the scalar boundary argument

The Euclidean inverse-square barrier argument.
It uses the interior energy identity, with no boundary regularity.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Metric
open scoped Topology ContDiff

namespace Riesz1

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

namespace Internal

/-- The positive part of distance minus a positive boundary margin. -/
def boundaryCoreCutoff (U : Set E) (ε : ℝ) (x : E) : ℝ :=
  max (infDist x Uᶜ - ε) 0

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem boundaryCoreCutoff_lipschitz (U : Set E) (ε : ℝ) :
    LipschitzWith 1 (boundaryCoreCutoff U ε) := by
  have ht : LipschitzWith 1 (fun x : E => infDist x Uᶜ - ε) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [Real.dist_eq, sub_sub_sub_cancel_right] using
      (lipschitz_infDist_pt Uᶜ).dist_le_mul x y
  exact ht.max_const 0

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem boundaryCoreCutoff_tsupport {U : Set E} {ε : ℝ} (hε : 0 < ε) :
    tsupport (boundaryCoreCutoff U ε) ⊆ U := by
  have hs : tsupport (boundaryCoreCutoff U ε) ⊆ {x : E | ε ≤ infDist x Uᶜ} := by
    apply closure_minimal _ (isClosed_le continuous_const (continuous_infDist_pt _))
    intro x hx
    have hh : max (infDist x Uᶜ - ε) 0 ≠ 0 := hx
    have : 0 < infDist x Uᶜ - ε := by
      by_contra hn
      exact hh (max_eq_right (le_of_not_gt hn))
    change ε ≤ infDist x Uᶜ
    linarith
  intro x hx
  have hdist := hs hx
  change ε ≤ infDist x Uᶜ at hdist
  by_contra hxu
  rw [infDist_zero_of_mem hxu] at hdist
  linarith

omit [MeasurableSpace E] [BorelSpace E] in
theorem boundaryCoreCutoff_compact {U : Set E} (hB : Bornology.IsBounded U)
    {ε : ℝ} (hε : 0 < ε) : HasCompactSupport (boundaryCoreCutoff U ε) :=
  isCompact_iff_isClosed_bounded.mpr
    ⟨isClosed_tsupport _, hB.subset (boundaryCoreCutoff_tsupport hε)⟩

omit [MeasurableSpace E] [BorelSpace E] in
/-- The sum of squared orthonormal directional derivatives of a
one-Lipschitz real function is at most one, at every point. -/
theorem sum_sq_fderiv_le_one {b : E → ℝ} (hb : LipschitzWith 1 b) (x : E) :
    (∑ i, (fderiv ℝ b x (stdOrthonormalBasis ℝ E i)) ^ 2) ≤ 1 := by
  have hs := (stdOrthonormalBasis ℝ E).sum_sq_norm_inner_left (gradient b x)
  simp only [inner_gradient_left, Real.norm_eq_abs, sq_abs] at hs
  rw [hs]
  have hn : ‖gradient b x‖ ≤ 1 := by
    calc
      ‖gradient b x‖ = ‖fderiv ℝ b x‖ := (InnerProductSpace.toDual ℝ E).symm.norm_map _
      _ ≤ 1 := norm_fderiv_le_of_lipschitz ℝ hb
  nlinarith [norm_nonneg (gradient b x)]

/-- Real distributional solutions on a bounded Euclidean domain vanish
under the inverse-square barrier and a sufficiently positive shift. -/
theorem schrodinger_eq_zero_of_boundary_barrier {U : Set E} (hU : IsOpen U)
    (hB : Bornology.IsBounded U) (hUc : Uᶜ.Nonempty)
    {W : E → ℝ} (hW : ContDiffOn ℝ ∞ W U) {C lam : ℝ} (hlam : C < lam)
    (hbar : ∀ x ∈ U, (infDist x Uᶜ)⁻¹ ^ 2 - C ≤ W x)
    {u : E → ℝ} (huL : MemLp u 2 (volume.restrict U))
    (hu : IsDistributionalSchrodingerSolution U W lam u) :
    u =ᵐ[volume.restrict U] 0 := by
  let d : E → ℝ := fun x => infDist x Uᶜ
  obtain ⟨R, hR⟩ := hB.isCompact_closure.bddAbove_image (continuous_infDist_pt Uᶜ).continuousOn
  have hdpos (x : E) (hx : x ∈ U) : 0 < d x :=
    (hU.isClosed_compl.notMem_iff_infDist_pos hUc).mp (not_not.mpr hx)
  have hd : ∀ᵐ x ∂(volume.restrict U), 0 < d x ∧ d x ≤ R := by
    filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
    exact ⟨hdpos x hx, hR (mem_image_of_mem _ (subset_closure hx))⟩
  have hsq := huL.integrable_sq
  have hz : (fun x => u x ^ 2) =ᵐ[volume.restrict U] 0 := by
    apply eq_zero_of_boundary_barrier_estimates (continuous_infDist_pt Uᶜ).measurable
      hd hsq (Eventually.of_forall fun x => sq_nonneg (u x)) (sub_pos.mpr hlam)
    intro ε hε
    let b := boundaryCoreCutoff U ε
    have hb : LipschitzWith 1 b := boundaryCoreCutoff_lipschitz U ε
    have hbU : tsupport b ⊆ U := boundaryCoreCutoff_tsupport hε
    obtain ⟨_, g, _, hkin, hpot, hrhs, he⟩ := interiorRegularity_real_energy hU hW lam huL hu
      hb (boundaryCoreCutoff_compact hB hε) hbU
    let A : E → ℝ := fun x =>
      ((max (d x - ε) 0 / d x) ^ 2 + (lam - C) * max (d x - ε) 0 ^ 2) * u x ^ 2
    have hAint : Integrable A (volume.restrict U) := by
      apply Integrable.mono' (hsq.const_mul (1 + (lam - C) * R ^ 2))
      · exact (((((continuous_infDist_pt Uᶜ).measurable.sub_const ε).max measurable_const).div
          (continuous_infDist_pt Uᶜ).measurable).aestronglyMeasurable.pow 2 |>.add
            (aestronglyMeasurable_const.mul
              ((((continuous_infDist_pt Uᶜ).measurable.sub_const ε).max
                measurable_const).aestronglyMeasurable.pow 2))).mul
                  (huL.aestronglyMeasurable.pow 2)
      · filter_upwards [hd] with x hx
        have hbound := boundary_barrier_cutoff_bound hx.1 hx.2 hε.le (sub_pos.mpr hlam).le
          (sq_nonneg (u x))
        change ‖A x‖ ≤ _
        rw [Real.norm_eq_abs, abs_of_nonneg hbound.1]
        exact hbound.2
    have hApot : ∀ᵐ x ∂(volume.restrict U), A x ≤ (W x + lam) * (b x * u x) ^ 2 := by
      filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
      have hh := mul_le_mul_of_nonneg_right (hbar x hx)
        (sq_nonneg (b x * u x))
      dsimp [A, b, boundaryCoreCutoff, d]
      dsimp [b, boundaryCoreCutoff] at hh
      simp only [div_eq_mul_inv] at *
      nlinarith
    have hpoteq : (∫ x in U, (W x + lam) * (b x * u x) ^ 2) =
        ∫ x, (W x + lam) * (b x * u x) ^ 2 := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hbU h))]
      simp
    have hrhseq : (∫ x in U,
        (∑ i, (fderiv ℝ b x (stdOrthonormalBasis ℝ E i)) ^ 2) * u x ^ 2) =
        ∫ x, (∑ i, (fderiv ℝ b x (stdOrthonormalBasis ℝ E i)) ^ 2) * u x ^ 2 := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      rw [fderiv_of_notMem_tsupport ℝ (fun h => hx (hbU h))]
      simp
    calc
      (∫ x, A x ∂(volume.restrict U)) ≤ ∫ x in U, (W x + lam) * (b x * u x) ^ 2 :=
        integral_mono_ae hAint hpot.restrict hApot
      _ ≤ ∫ x in U, (∑ i, (fderiv ℝ b x (stdOrthonormalBasis ℝ E i)) ^ 2) * u x ^ 2 := by
        rw [hpoteq, hrhseq]
        have hkn : 0 ≤ ∫ x, ∑ i, (g i x) ^ 2 :=
          integral_nonneg fun x => Finset.sum_nonneg fun i _ => sq_nonneg (g i x)
        linarith
      _ ≤ ∫ x in U, u x ^ 2 := by
        apply integral_mono_ae hrhs.restrict hsq
        exact Eventually.of_forall fun x =>
          mul_le_of_le_one_left (sq_nonneg _) (sum_sq_fderiv_le_one hb x)
  filter_upwards [hz] with x hx
  exact sq_eq_zero_iff.mp hx

/-- The same boundary uniqueness assertion for complex solutions. -/
theorem schrodinger_complex_eq_zero_of_boundary_barrier {U : Set E} (hU : IsOpen U)
    (hB : Bornology.IsBounded U) (hUc : Uᶜ.Nonempty)
    {W : E → ℝ} (hW : ContDiffOn ℝ ∞ W U) {C lam : ℝ} (hlam : C < lam)
    (hbar : ∀ x ∈ U, (infDist x Uᶜ)⁻¹ ^ 2 - C ≤ W x)
    {u : E → ℂ} (huL : MemLp u 2 (volume.restrict U))
    (hu : IsDistributionalSchrodingerSolution U W lam u) :
    u =ᵐ[volume.restrict U] 0 := by
  have hre := schrodinger_eq_zero_of_boundary_barrier hU hB hUc hW hlam hbar
    (Complex.reCLM.comp_memLp' huL) (hu.map Complex.reCLM)
  have him := schrodinger_eq_zero_of_boundary_barrier hU hB hUc hW hlam hbar
    (Complex.imCLM.comp_memLp' huL) (hu.map Complex.imCLM)
  filter_upwards [hre, him] with x hx hy
  exact Complex.ext hx hy

end Internal

end Riesz1
