/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.EllipticRegularity.WeakEnergy

/-!
# Lipschitz cutoff energy from an L² Laplacian

The global L² calculation used after localization in the interior H² regularity argument.
The gradient is represented by the original weak directional derivatives.
-/

@[expose] public section

noncomputable section

open MeasureTheory TemperedDistribution Set
open scoped SchwartzMap LineDeriv Laplacian ContDiff ComplexInnerProductSpace NNReal

namespace Riesz1.Internal

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- An L² function with L² Laplacian has L² first and diagonal second
derivatives, and their sum is the prescribed Laplacian. -/
theorem coordinate_derivatives_of_laplacian
    (u f : Lp ℂ 2 (volume : Measure E))
    (hu : Δ (u : 𝓢'(E, ℂ)) = (f : 𝓢'(E, ℂ))) :
    ∃ g h : Fin (Module.finrank ℝ E) → Lp ℂ 2 (volume : Measure E),
      (∀ i, ∂_{stdOrthonormalBasis ℝ E i} (u : 𝓢'(E, ℂ)) = (g i : 𝓢'(E, ℂ)) ∧
        ∂_{stdOrthonormalBasis ℝ E i} (g i : 𝓢'(E, ℂ)) = (h i : 𝓢'(E, ℂ))) ∧
      ∑ i, h i = f := by
  classical
  have h0 : MemSobolev 0 2 (u : 𝓢'(E, ℂ)) := memSobolev_zero_iff.mpr ⟨u, rfl⟩
  have hΔ : MemSobolev 0 2 (Δ (u : 𝓢'(E, ℂ))) := memSobolev_zero_iff.mpr ⟨f, hu⟩
  have hd (i : Fin (Module.finrank ℝ E)) :=
    exists_l2_derivatives_of_laplacian h0 hΔ
      (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E i)
  choose g hg using fun i => (hd i).1
  have hh (i : Fin (Module.finrank ℝ E)) :
      ∃ h : Lp ℂ 2 (volume : Measure E),
        ∂_{stdOrthonormalBasis ℝ E i} (g i : 𝓢'(E, ℂ)) = (h : 𝓢'(E, ℂ)) := by
    simpa only [hg i] using (hd i).2
  choose h hh using hh
  refine ⟨g, h, fun i => ⟨hg i, hh i⟩, ?_⟩
  have he : ((∑ i, h i : Lp ℂ 2 (volume : Measure E)) : 𝓢'(E, ℂ)) =
      (f : 𝓢'(E, ℂ)) := by
    calc
      _ = ∑ i, (h i : 𝓢'(E, ℂ)) :=
        map_sum (Lp.toTemperedDistributionCLM ℂ volume 2) h Finset.univ
      _ = Δ (u : 𝓢'(E, ℂ)) := by
        rw [TemperedDistribution.laplacian_eq_sum (stdOrthonormalBasis ℝ E)]
        simp only [hg, hh]
      _ = _ := hu
  exact (LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot
    (F := ℂ) (μ := (volume : Measure E)) (p := 2))) he

/-- The complete finite-dimensional cutoff energy calculation with an
L² Laplacian. Every coordinate of the product has an L² weak derivative,
and all three energy integrands are integrable. -/
theorem lipschitz_cutoff_laplacian_energy
    (u f : Lp ℂ 2 (volume : Measure E))
    (hu : Δ (u : 𝓢'(E, ℂ)) = (f : 𝓢'(E, ℂ)))
    {b : E → ℝ} {C : ℝ≥0} (hb : LipschitzWith C b) (hbc : HasCompactSupport b) :
    ∃ g : Fin (Module.finrank ℝ E) → E → ℂ,
      (∀ i, MemLp (g i) 2 volume ∧
        HasWeakDirectionalDerivativeOn univ (fun x => b x • u x) (g i)
          (stdOrthonormalBasis ℝ E i)) ∧
      Integrable (fun x => ∑ i, ‖g i x‖ ^ 2) ∧
      Integrable (fun x => RCLike.re (⟪b x ^ 2 • u x, f x⟫ : ℂ)) ∧
      Integrable (fun x => (∑ i, (fderiv ℝ b x (stdOrthonormalBasis ℝ E i)) ^ 2) *
        ‖u x‖ ^ 2) ∧
      (∫ x, ∑ i, ‖g i x‖ ^ 2) +
        (∫ x, RCLike.re (⟪b x ^ 2 • u x, f x⟫ : ℂ)) =
        ∫ x, (∑ i, (fderiv ℝ b x (stdOrthonormalBasis ℝ E i)) ^ 2) * ‖u x‖ ^ 2 := by
  classical
  obtain ⟨g, h, hder, hsum⟩ := coordinate_derivatives_of_laplacian u f hu
  let e := stdOrthonormalBasis ℝ E
  let k := fun i x => fderiv ℝ b x (e i) • u x + b x • g i x
  have he (i : Fin (Module.finrank ℝ E)) :=
    lipschitz_cutoff_directional_energy (hder i).1 (hder i).2 hb hbc
  have hk (i : Fin (Module.finrank ℝ E)) :=
    (lipschitz_mul_tempered_weak (hder i).1 hb hbc).2
  have hp (x : E) : (∑ i, RCLike.re (⟪b x ^ 2 • u x, h i x⟫ : ℂ)) =
      RCLike.re (⟪b x ^ 2 • u x, ∑ i, h i x⟫ : ℂ) := by
    rw [inner_sum, map_sum]
  have hsumAe : (fun x => ∑ i, h i x) =ᵐ[volume] (f : E → ℂ) := by
    have hs := Lp.coeFn_finsetSum Finset.univ h
    rw [hsum] at hs
    filter_upwards [hs] with x hx
    simpa only [Finset.sum_apply] using hx.symm
  have hpotAe : (fun x => ∑ i, RCLike.re (⟪b x ^ 2 • u x, h i x⟫ : ℂ)) =ᵐ[volume]
      (fun x => RCLike.re (⟪b x ^ 2 • u x, f x⟫ : ℂ)) := by
    filter_upwards [hsumAe] with x hx
    rw [hp, hx]
  have hpotS : Integrable (fun x => ∑ i, RCLike.re (⟪b x ^ 2 • u x, h i x⟫ : ℂ)) :=
    integrable_finsetSum _ (fun i _ => (he i).2.1)
  have hrhs (x : E) : (∑ i, (fderiv ℝ b x (e i)) ^ 2 * ‖u x‖ ^ 2) =
      (∑ i, (fderiv ℝ b x (e i)) ^ 2) * ‖u x‖ ^ 2 := by rw [Finset.sum_mul]
  have hR : Integrable (fun x => (∑ i, (fderiv ℝ b x (e i)) ^ 2) * ‖u x‖ ^ 2) := by
    simpa only [← Finset.sum_mul, e] using
      integrable_finsetSum Finset.univ (fun i _ => (he i).2.2.1)
  refine ⟨k, fun i => ⟨(hk i).1, (hk i).2⟩,
    integrable_finsetSum _ (fun i _ => (he i).1), hpotS.congr hpotAe, hR, ?_⟩
  have hE := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun i _ => (he i).2.2.2)
  rw [Finset.sum_add_distrib,
    ← integral_finsetSum _ (fun i _ => (he i).1),
    ← integral_finsetSum _ (fun i _ => (he i).2.1),
    ← integral_finsetSum _ (fun i _ => (he i).2.2.1),
    integral_congr_ae hpotAe] at hE
  simpa only [← Finset.sum_mul, k, e] using hE

end Riesz1.Internal
