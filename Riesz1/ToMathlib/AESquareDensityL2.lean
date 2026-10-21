/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Ground-state multiplication for an almost everywhere measurable density

The square-density construction with only almost everywhere measurability.
This applies to smooth interior Hamiltonians whose total formulas need not
be measurable away from the support of the measure. No extension or selected
measurable representative is used in the multiplier formula.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter

namespace Riesz1

variable {α F : Type*} [MeasurableSpace α]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {μ ν : Measure α} {w : α → ℝ}

namespace Internal

theorem aeSquareDensity_ac (hw : AEMeasurable w μ) (hpos : ∀ x, 0 < w x)
    (hν : ν = μ.withDensity (fun x => ENNReal.ofReal (w x ^ 2))) : μ ≪ ν := by
  rw [hν]
  exact withDensity_absolutelyContinuous' (hw.pow_const 2).ennreal_ofReal
    (Eventually.of_forall fun x => (ENNReal.ofReal_pos.mpr (sq_pos_of_pos (hpos x))).ne')

theorem memLp_aeSquareDensity_mul_iff (hw : AEMeasurable w μ)
    (hν : ν = μ.withDensity (fun x => ENNReal.ofReal (w x ^ 2)))
    {f : α → F} (hf : AEStronglyMeasurable f μ) :
    MemLp (fun x => w x • f x) 2 μ ↔ MemLp f 2 ν := by
  have hfm := hf.mono_ac (hν ▸ withDensity_absolutelyContinuous μ _)
  have hm : AEStronglyMeasurable (fun x => w x • f x) μ :=
    hw.aestronglyMeasurable.smul hf
  rw [memLp_two_iff_integrable_sq_norm hm,
    memLp_two_iff_integrable_sq_norm hfm, hν,
    integrable_withDensity_iff_integrable_smul₀' (hw.pow_const 2).ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul]

theorem integral_aeSquareDensity (hw : AEMeasurable w μ)
    (hν : ν = μ.withDensity (fun x => ENNReal.ofReal (w x ^ 2))) (g : α → ℝ) :
    ∫ x, g x ∂ν = ∫ x, w x ^ 2 * g x ∂μ := by
  rw [hν, integral_withDensity_eq_integral_toReal_smul₀
    (hw.pow_const 2).ennreal_ofReal (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul]

theorem memLp_aeSquareDensity_mul (hw : AEMeasurable w μ) (hpos : ∀ x, 0 < w x)
    (hν : ν = μ.withDensity (fun x => ENNReal.ofReal (w x ^ 2)))
    (u : Lp F 2 ν) : MemLp (fun x => w x • u x) 2 μ :=
  (memLp_aeSquareDensity_mul_iff hw hν
    ((Lp.aestronglyMeasurable u).mono_ac (aeSquareDensity_ac hw hpos hν))).mpr (Lp.memLp u)

end Internal

/-- Multiplication by a positive square-root density, on all of weighted `L²`. -/
def aeSquareDensityL2Isometry (hw : AEMeasurable w μ) (hpos : ∀ x, 0 < w x)
    (hν : ν = μ.withDensity (fun x => ENNReal.ofReal (w x ^ 2))) :
    Lp F 2 ν →ₗᵢ[ℝ] Lp F 2 μ where
  toFun u := (Internal.memLp_aeSquareDensity_mul hw hpos hν u).toLp _
  map_add' u v := by
    apply Lp.ext
    filter_upwards [(Internal.memLp_aeSquareDensity_mul hw hpos hν (u + v)).coeFn_toLp,
      (Internal.memLp_aeSquareDensity_mul hw hpos hν u).coeFn_toLp,
      (Internal.memLp_aeSquareDensity_mul hw hpos hν v).coeFn_toLp,
      (Internal.aeSquareDensity_ac hw hpos hν).ae_le (Lp.coeFn_add u v),
      Lp.coeFn_add ((Internal.memLp_aeSquareDensity_mul hw hpos hν u).toLp _)
        ((Internal.memLp_aeSquareDensity_mul hw hpos hν v).toLp _)] with x ha hu hv huv hsum
    rw [ha, hsum, Pi.add_apply, hu, hv, huv, Pi.add_apply, smul_add]
  map_smul' a u := by
    apply Lp.ext
    filter_upwards [(Internal.memLp_aeSquareDensity_mul hw hpos hν (a • u)).coeFn_toLp,
      (Internal.memLp_aeSquareDensity_mul hw hpos hν u).coeFn_toLp,
      (Internal.aeSquareDensity_ac hw hpos hν).ae_le (Lp.coeFn_smul a u),
      Lp.coeFn_smul a ((Internal.memLp_aeSquareDensity_mul hw hpos hν u).toLp _)]
      with x ha hu hau hsmul
    simp only [RingHom.id_apply]
    rw [ha, hsmul, Pi.smul_apply, hu, hau, Pi.smul_apply, smul_comm]
  norm_map' u := by
    change ‖(Internal.memLp_aeSquareDensity_mul hw hpos hν u).toLp _‖ = ‖u‖
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, L2.inner_def, L2.inner_def]
    rw [Internal.integral_aeSquareDensity hw hν]
    apply integral_congr_ae
    filter_upwards [(Internal.memLp_aeSquareDensity_mul hw hpos hν u).coeFn_toLp] with x hx
    rw [hx]
    simp only [real_inner_smul_left, real_inner_smul_right]
    ring

theorem aeSquareDensityL2Isometry_coeFn (hw : AEMeasurable w μ) (hpos : ∀ x, 0 < w x)
    (hν : ν = μ.withDensity (fun x => ENNReal.ofReal (w x ^ 2))) (u : Lp F 2 ν) :
    (aeSquareDensityL2Isometry hw hpos hν u : α → F) =ᵐ[μ] fun x => w x • u x :=
  (Internal.memLp_aeSquareDensity_mul hw hpos hν u).coeFn_toLp

theorem aeSquareDensityL2Isometry_surjective (hw : AEMeasurable w μ) (hpos : ∀ x, 0 < w x)
    (hν : ν = μ.withDensity (fun x => ENNReal.ofReal (w x ^ 2))) :
    Function.Surjective (aeSquareDensityL2Isometry (F := F) hw hpos hν) := by
  intro v
  let f : α → F := fun x => (w x)⁻¹ • v x
  have hfm : AEStronglyMeasurable f μ := hw.inv.aestronglyMeasurable.smul (Lp.aestronglyMeasurable v)
  have hf : MemLp f 2 ν := by
    apply (Internal.memLp_aeSquareDensity_mul_iff hw hν hfm).mp
    convert Lp.memLp v using 1
    funext x
    exact smul_inv_smul₀ (hpos x).ne' (v x)
  refine ⟨hf.toLp f, ?_⟩
  apply Lp.ext
  filter_upwards [aeSquareDensityL2Isometry_coeFn hw hpos hν (hf.toLp f),
    (Internal.aeSquareDensity_ac hw hpos hν).ae_le hf.coeFn_toLp] with x hx hfx
  rw [hx, hfx]
  exact smul_inv_smul₀ (hpos x).ne' (v x)

/-- The inverse is multiplication by the reciprocal square root, uniquely specified
by the inverse of the surjective linear isometry. -/
def aeSquareDensityL2Equiv (hw : AEMeasurable w μ) (hpos : ∀ x, 0 < w x)
    (hν : ν = μ.withDensity (fun x => ENNReal.ofReal (w x ^ 2))) :
    Lp F 2 ν ≃ₗᵢ[ℝ] Lp F 2 μ :=
  LinearIsometryEquiv.ofSurjective (aeSquareDensityL2Isometry hw hpos hν)
    (aeSquareDensityL2Isometry_surjective hw hpos hν)

theorem aeSquareDensityL2Equiv_coeFn (hw : AEMeasurable w μ) (hpos : ∀ x, 0 < w x)
    (hν : ν = μ.withDensity (fun x => ENNReal.ofReal (w x ^ 2))) (u : Lp F 2 ν) :
    (aeSquareDensityL2Equiv hw hpos hν u : α → F) =ᵐ[μ] fun x => w x • u x :=
  aeSquareDensityL2Isometry_coeFn hw hpos hν u

/-- The same equivalence is linear over any additional scalar field
whose action commutes with multiplication by real numbers. -/
def aeSquareDensityL2ScalarEquiv (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]
    (hw : AEMeasurable w μ) (hpos : ∀ x, 0 < w x)
    (hν : ν = μ.withDensity (fun x => ENNReal.ofReal (w x ^ 2))) :
    Lp F 2 ν ≃ₗᵢ[𝕜] Lp F 2 μ where
  toEquiv := (aeSquareDensityL2Equiv hw hpos hν).toEquiv
  map_add' := (aeSquareDensityL2Equiv hw hpos hν).map_add
  map_smul' a u := by
    change aeSquareDensityL2Equiv hw hpos hν (a • u) =
      a • aeSquareDensityL2Equiv hw hpos hν u
    apply Lp.ext
    filter_upwards [aeSquareDensityL2Equiv_coeFn hw hpos hν (a • u),
      aeSquareDensityL2Equiv_coeFn hw hpos hν u,
      (Internal.aeSquareDensity_ac hw hpos hν).ae_le (Lp.coeFn_smul a u),
      Lp.coeFn_smul a (aeSquareDensityL2Equiv hw hpos hν u)] with x ha hu hau hsmul
    rw [ha, hsmul, Pi.smul_apply, hu, hau, Pi.smul_apply, smul_comm]
  norm_map' := (aeSquareDensityL2Equiv hw hpos hν).norm_map

end Riesz1
