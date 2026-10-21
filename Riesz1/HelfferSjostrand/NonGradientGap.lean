/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.NonGradientGapEquiv

/-!
# Gap preservation and the full non-gradient proposition

Proposition 3.2: the inverse preserves
measurable functions of the cyclic gaps. The last theorem
assembles all assertions using the existing inverse and energy.
-/

@[expose] public section

noncomputable section

open MeasureTheory InnerProductSpace

namespace Riesz1

variable {N : ℕ+} {c C_N : ℝ} (χ : HsPairPotentials N c) (hN : 2 ≤ (N : ℕ)) (hc : 0 < c)

local notation "μ" => (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))

local instance : NormedAddCommGroup (HsSobolev μ) := inferInstance
local instance : NormedSpace ℝ (HsSobolev μ) := inferInstance
local instance : InnerProductSpace ℝ (HsSobolev μ) := inferInstance
local instance : InnerProductSpace ℝ (PiLp 2 (fun _ : Fin (N : ℕ) => HsSobolev μ)) := inferInstance
local instance : NormedAddCommGroup (HsVectorJet μ) := inferInstance
local instance : NormedSpace ℝ (HsVectorJet μ) := inferInstance
local instance : InnerProductSpace ℝ (HsVectorJet μ) := inferInstance
local instance : NormedAddCommGroup (HsVectorSobolev χ hN hc μ) := inferInstance
local instance : NormedSpace ℝ (HsVectorSobolev χ hN hc μ) := inferInstance
local instance : InnerProductSpace ℝ (HsVectorSobolev χ hN hc μ) := inferInstance

namespace Internal

theorem hsNonGradient_rotation_solves (v : Lp (HsEuclidean N) 2 μ)
    (u : HsVectorSobolev χ hN hc μ) (hsol : HsNonGradientSolves χ hN hc v u) (t : ℝ)
    (hv : hsGapLpPull χ hc (HsEuclidean N) t v = v) :
    HsNonGradientSolves χ hN hc v (hsGapVectorPull χ hc hN t u) := by
  intro w
  have hw := hsGapVectorPull_neg χ hc hN t w
  have hpair := hsGapVectorPull_pairing_fixed χ hc hN t v hv (hsGapVectorPull χ hc hN (-t) w)
  calc
    _ = hsVectorSobolevForm χ hN hc μ (hsGapVectorPull χ hc hN t u)
        (hsGapVectorPull χ hc hN t (hsGapVectorPull χ hc hN (-t) w)) :=
      congrArg (hsVectorSobolevForm χ hN hc μ (hsGapVectorPull χ hc hN t u)) hw.symm
    _ = hsVectorSobolevForm χ hN hc μ u (hsGapVectorPull χ hc hN (-t) w) :=
      hsGapVectorPull_form χ hc hN t u (hsGapVectorPull χ hc hN (-t) w)
    _ = hsNonGradientPairing μ v (hsGapVectorPull χ hc hN (-t) w).val :=
      hsol (hsGapVectorPull χ hc hN (-t) w)
    _ = hsNonGradientPairing μ v w.val := hpair.symm.trans
      (congrArg (fun z : HsVectorSobolev χ hN hc μ => hsNonGradientPairing μ v z.val) hw)

theorem hsInverse_rotation_fixed (hPL : External.PrekopaLeindler)
    (hadm : HsAdmissible χ C_N) (v : hsMeanZeroL2 μ) (t : ℝ)
    (hv : hsGapLpPull χ hc (HsEuclidean N) t v.val = v.val) :
    hsGapNormalizedPull χ hc hN t (hsInverse hPL χ hN hc v) = hsInverse hPL χ hN hc v := by
  have hsol := hsNonGradient_rotation_solves χ hN hc v.val (hsInverse hPL χ hN hc v).val
    (hsInverse_solves hPL χ hN hc hadm v) t hv
  exact hsInverse_unique hPL χ hN hc v
    (hsGapNormalizedPull χ hc hN t (hsInverse hPL χ hN hc v)) (fun w => hsol w.val)

theorem hsGapLpPull_fixed_of_gap (v : Lp (HsEuclidean N) 2 μ)
    (hv : ∀ i : Fin (N : ℕ), ∃ g : (Fin (N : ℕ) → ℝ) → ℝ, Measurable g ∧
      (fun x => v x i) =ᵐ[μ] fun x => g (hsGap (hsLiftPoint N x))) (t : ℝ) :
    hsGapLpPull χ hc (HsEuclidean N) t v = v := by
  have hvi (j : Fin (N : ℕ)) : ∀ᵐ x ∂μ, v (hsGapRotate t x) j = v x j := by
    obtain ⟨g, -, hg⟩ := hv j
    have ht := (measurePreserving_hsGapRotate χ hc t).quasiMeasurePreserving.ae hg
    filter_upwards [hg, ht] with x hx htx
    exact htx.trans ((congrArg g (hsGapRotate_gap t x)).trans hx.symm)
  apply Lp.ext
  filter_upwards [hsGapLpPull_ae χ hc (HsEuclidean N) t v, ae_all_iff.mpr hvi]
    with x hx hx'
  rw [hx]
  ext j
  exact hx' j


end Internal

/-- The remaining assertion of Proposition 3.2, on the
inverse and the cyclic gap map. -/
theorem hsInverse_gap_dependent (hPL : External.PrekopaLeindler)
    (hadm : HsAdmissible χ C_N) (v : hsMeanZeroL2 μ)
    (hv : ∀ i : Fin (N : ℕ), ∃ g : (Fin (N : ℕ) → ℝ) → ℝ, Measurable g ∧
      (fun x => v.val x i) =ᵐ[μ] fun x => g (hsGap (hsLiftPoint N x))) :
    ∀ i : Fin (N : ℕ), ∃ g : (Fin (N : ℕ) → ℝ) → ℝ, Measurable g ∧
      (hsJetValue μ i (hsInverse hPL χ hN hc v).val.val : HsConfiguration N → ℝ) =ᵐ[μ]
        fun x => g (hsGap (hsLiftPoint N x)) := by
  intro i
  apply (hsLp_gap_factorization_iff_rotation χ hc _).mpr
  intro t
  have hfix := Internal.hsGapLpPull_fixed_of_gap χ hc v.val hv t
  have hu := Internal.hsInverse_rotation_fixed χ hN hc hPL hadm v t hfix
  exact Internal.hsGapNormalizedPull_value_fixed χ hc hN t (hsInverse hPL χ hN hc v) hu i

/-- **Non-gradient fields**, Proposition 3.2, in full.
The zero-sum assertion is generalized to every pointwise zero-sum input.
`T` and its energy are the existing definitions. -/
theorem well_posed_non_grad (hPL : External.PrekopaLeindler)
    (hadm : HsAdmissible χ C_N) (v : hsMeanZeroL2 μ) :
    (∃! u : hsMeanZeroVector χ hN hc μ, HsNonGradientSolves χ hN hc v.val u.val) ∧
    (∀ u : hsMeanZeroVector χ hN hc μ,
      (∀ w : hsMeanZeroVector χ hN hc μ,
        hsNonGradientFunctional χ hN hc v u ≤ hsNonGradientFunctional χ hN hc v w) ↔
          u = hsInverse hPL χ hN hc v) ∧
    ((∀ i : Fin (N : ℕ), ∃ g : (Fin (N : ℕ) → ℝ) → ℝ, Measurable g ∧
      (fun x => v.val x i) =ᵐ[μ] fun x => g (hsGap (hsLiftPoint N x))) →
      ∀ i : Fin (N : ℕ), ∃ g : (Fin (N : ℕ) → ℝ) → ℝ, Measurable g ∧
        (hsJetValue μ i (hsInverse hPL χ hN hc v).val.val : HsConfiguration N → ℝ) =ᵐ[μ]
          fun x => g (hsGap (hsLiftPoint N x))) ∧
    ((∀ᵐ x ∂μ, ∑ i : Fin (N : ℕ), v.val x i = 0) →
      ∀ᵐ x ∂μ, ∑ i : Fin (N : ℕ), hsJetValue μ i (hsInverse hPL χ hN hc v).val.val x = 0) := by
  exact ⟨hs_non_gradient_existsUnique χ hN hc hPL hadm v,
    hsInverse_minimizer_iff hPL χ hN hc v,
    hsInverse_gap_dependent χ hN hc hPL hadm v,
    hsInverse_sum_zero χ hN hc hPL hadm v⟩

end Riesz1
