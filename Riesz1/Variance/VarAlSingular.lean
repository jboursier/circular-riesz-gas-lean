/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.VarAlSingularField
public import Riesz1.Variance.VarAlGapCutoffBridge
public import Riesz1.Variance.APrioriComparisonEstimate
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-!
# Singular-field comparison for the loop

Proposition 5.9. The field is the coordinate restriction
at the fixed anchor zero. The inverse is the actual anchored inverse for
the nearest-neighbour convexification on the larger window `I_{2γ}`.
The only analytic inputs are `External.BakryEmery` and `External.PrekopaLeindler`.
The exponent and epsilon threshold precede beta, the envelope amplitude,
the spatial cutoff, the particle number, scale and transport.
-/

@[expose] public section

noncomputable section

open MeasureTheory Finset Set
open scoped ContDiff

namespace Riesz1

/-- **Proposition 5.9, singular-field assertions.** The loss exponent
depends only on `s`, `α`, `γ`. The coefficient can depend on beta, epsilon,
the envelope amplitude and the spatial cutoff. Square integrability is
concluded before the energy is evaluated. -/
theorem varAl_singular (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (s : RieszExponent) {α γ : ℝ} (hα : s.val - 1 < α) (hα2 : α < s.val / 2)
    (hγ : max 4 (2 / s.val) ≤ γ) :
    ∃ εstar κ : ℝ, 0 < εstar ∧ 0 < κ ∧
      ∀ (β : ℝ) (hβ : 0 < β) (C₀ : ℝ), 0 < C₀ →
      ∀ (χ : ℝ → ℝ), ContDiff ℝ ∞ χ → HasCompactSupport χ →
        tsupport χ ⊆ Ioo (-(1 / 4)) (1 / 4) →
        (∀ x : ℝ, |x| ≤ 1 / 8 → χ x = 1) → (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) →
      ∀ ε : ℝ, 0 < ε → ε < εstar → ∃ C : ℝ, 0 < C ∧
        ∀ (n : ℕ), 1 ≤ n → ∀ (θ : ℝ → ℝ) (hθ : IsForcingCutoff θ)
          (ℓ : ℝ), 0 < ℓ → ℓ ≤ 1 → ∀ (hK : 1 ≤ (n.succPNat : ℝ) * ℓ),
        ∀ (ψ : ℝ → ℝ), ContDiff ℝ ∞ ψ → Function.Periodic ψ ℓ⁻¹ →
          (∀ t, |deriv ψ t| ≤ C₀ * gradWeightOne s.val (1 - s.val + α)
            ((n.succPNat : ℝ) * ℓ) ℓ⁻¹ t) →
          (∀ t, |deriv (deriv ψ) t| ≤ C₀ * gradWeightTwo s.val (1 - s.val + α)
            ((n.succPNat : ℝ) * ℓ) ℓ⁻¹ t) →
          let P : Parameters := ⟨(β, s.val), hβ, s.property⟩
          let K := (n.succPNat : ℝ) * ℓ
          let Q := nearestTiltedPairs P n.succPNat hθ K (2 * γ) ε (by linarith)
          let v := fun y : AnchoredEuclidean n => WithLp.toLp 2 fun i : Fin n =>
            loopCutoff s.val γ ε n.succPNat ℓ (anchorVector (WithLp.ofLp y)) *
              gradVfield s.val (loopTransport χ n.succPNat ℓ γ ψ)
                n.succPNat ℓ γ (anchorVector (WithLp.ofLp y)) i.succ
          ∃ hv : MemLp v 2 (anchoredMeasureE Q),
            anchoredInverseEnergy Q
              (hsRieszPairPotentials_curvature_pos n.succPNat P.2.1 (parametersExponent P))
              (hv.toLp v) ≤ C * K ^ (κ * ε) * (K + K ^ (2 * (1 - s.val + α))) := by
  classical
  have hγ1 : 1 < γ := by have := (le_max_left _ _).trans hγ; linarith
  obtain ⟨εf, κf, hεf, hκf, hf⟩ := varAlSingular_field_bound s.property.1 s.property.2 hα.le hα2 hγ
  refine ⟨min εf 1, 2 * κf + 4 + 2 * (2 * γ), lt_min hεf zero_lt_one, by linarith, ?_⟩
  intro β hβ C₀ hC₀ χ hχ hχc hχs hχ1 hχ01 ε hε hεstar
  have hεf' : ε < εf := hεstar.trans_le (min_le_left _ _)
  have hε1 : ε ≤ 1 := (hεstar.trans_le (min_le_right _ _)).le
  obtain ⟨Cf, hCf, hfield⟩ := hf χ hχ hχc hχs hχ1 hχ01 ε hε hεf'
  let P : Parameters := ⟨(β, s.val), hβ, s.property⟩
  let b := 1 - s.val + α
  obtain ⟨C, hC, henergy⟩ := a_priori_comparison_energy hBE hPL P b (2 * γ) (Cf * C₀) κf
    (by dsimp [b]; linarith) (by linarith) (mul_pos hCf hC₀) hκf ε hε hε1
  refine ⟨C, hC, ?_⟩
  intro n hn θ hθ ℓ hℓ hℓ1 hK ψ hψ hp h1 h2
  let N := n.succPNat
  let K := (N : ℝ) * ℓ
  have hK0 : 0 < K := by dsimp [K]; linarith
  let Q := nearestTiltedPairs P N hθ K (2 * γ) ε hK0
  let μ := anchoredMeasureE Q
  let J := (window N K (2 * γ)).erase ⟨0, N.pos⟩
  let ψγ := loopTransport χ N ℓ γ ψ
  let η := fun y : AnchoredEuclidean n => loopCutoff s.val γ ε N ℓ (anchorVector (WithLp.ofLp y))
  let v := fun y : AnchoredEuclidean n => WithLp.toLp 2 fun i : Fin n =>
    gradVfield s.val ψγ N ℓ γ (anchorVector (WithLp.ofLp y)) i.succ
  let u := fun y : AnchoredEuclidean n => η y • v y
  have hav : Continuous (fun y : AnchoredEuclidean n => anchorVector (WithLp.ofLp y)) :=
    (continuous_pi fun k => continuous_anchorVector_apply k).comp (PiLp.continuous_ofLp 2 _)
  have hψγ : ContDiff ℝ ∞ ψγ := contDiff_loopTransport hχ hψ hχs N hℓ γ
  have hpγ : Function.Periodic ψγ (1 / ℓ) := by
    simpa only [one_div] using loopTransport_periodic (N := N) (γ := γ) hℓ χ hp
  have hvc : ContinuousOn v (anchoredSimplex n) := by
    apply (PiLp.continuous_toLp 2 _).comp_continuousOn
    apply continuousOn_pi.mpr
    intro i
    exact (continuousOn_gradVfield hψγ hℓ hpγ s.property.1 s.property.2
      (varAlSingular_transport_support hχs hℓ ψ) i.succ).comp hav.continuousOn
        (fun _ hy => varAl_anchorVector_mem hy)
  have hvm : AEStronglyMeasurable v μ := by
    change AEStronglyMeasurable v (anchoredMeasureE Q)
    rw [← Measure.restrict_eq_self_of_ae_mem (ae_mem_anchoredSimplex Q)]
    exact hvc.aestronglyMeasurable (isOpen_anchoredSimplex n).measurableSet
  let v₀ := hvm.mk v
  have hcut : ∀ᵐ y ∂μ, η y = anchoredCutoff N s.val K (2 * γ) ε (WithLp.ofLp y) := by
    filter_upwards [ae_mem_anchoredSimplex Q] with y hy
    exact varAlGap_loopCutoff_eq_anchoredCutoff hn hK s.val ε hy
  have hz (i : Fin n) : ∀ᵐ y ∂μ, i.succ ∉ J → v₀ y i = 0 := by
    filter_upwards [hvm.ae_eq_mk] with y hy hi
    change v y = v₀ y at hy
    rw [← hy]
    apply (gradEst_fields_support (s := s.val) ψγ (anchorVector (WithLp.ofLp y)) i.succ ?_).1
    intro j hj hji
    apply hi
    apply Finset.mem_erase.mpr
    refine ⟨by
      intro heq
      have hh := congrArg Fin.val heq
      change i.val + 1 = 0 at hh
      omega, ?_⟩
    rw [← hji]
    by_cases hpart : GradPartial N ℓ (2 * γ)
    · rw [varAlGap_window_eq hK]
      exact Finset.mem_image_of_mem _
        (varAl_gradInWindow_mono hK (by linarith : γ ≤ 2 * γ) (fun _ => hj) hpart)
    · rw [window_full hpart]
      exact Finset.mem_univ _
  have hb (i : Fin n) : ∀ᵐ y ∂μ,
      anchoredCutoff N s.val K (2 * γ) ε (WithLp.ofLp y) * |v₀ y i| ≤
        (Cf * C₀ * K ^ (κf * ε)) * anchoredCutoff N s.val K (2 * γ) ε (WithLp.ofLp y) *
          (((n : ℝ) + 1) * augmentedComparisonWeight N K s.val b ε i.succ) := by
    filter_upwards [ae_mem_anchoredSimplex Q, hvm.ae_eq_mk, hcut] with y hy heq hη
    change v y = v₀ y at heq
    rw [← hη, ← heq]
    simpa only [N, Nat.succPNat_coe, Nat.cast_succ, v, ψγ, K, η, b] using
      hfield N ℓ C₀ ψ (by simpa [N] using hn) hℓ hℓ1 hK hC₀.le hψ hp h1 h2
        _ (varAl_anchorVector_mem hy) (anchorVector_zero _) i.succ
  obtain ⟨hv₀, hE⟩ := henergy n hn θ hθ K hK J (Finset.Subset.refl _)
    (augmentedComparisonWeight N K s.val b ε) (Or.inr rfl)
    v₀ hvm.measurable_mk hz hb
  have hueq : u =ᵐ[μ] fun y => anchoredCutoff N s.val K (2 * γ) ε (WithLp.ofLp y) • v₀ y := by
    filter_upwards [hvm.ae_eq_mk, hcut] with y hyv hyη
    change η y • v y = _
    rw [hyv, hyη]
  have hu : MemLp u 2 μ := hv₀.ae_eq hueq.symm
  have hLp := hu.toLp_congr hv₀ hueq
  change ∃ hu : MemLp u 2 μ, _
  refine ⟨hu, ?_⟩
  change anchoredInverseEnergy Q
    (hsRieszPairPotentials_curvature_pos N P.2.1 (parametersExponent P)) (hu.toLp u) ≤
      C * K ^ ((2 * κf + 4 + 2 * (2 * γ)) * ε) * (K + K ^ (2 * (1 - s.val + α)))
  rw [hLp]
  apply hE.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ C * K ^ ((2 * κf + 4 + 2 * (2 * γ)) * ε))
  have hsK : K ^ s.val ≤ K := by
    calc K ^ s.val ≤ K ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hK s.property.2.le
      _ = K := Real.rpow_one _
  dsimp [b]
  linarith

end Riesz1

end
