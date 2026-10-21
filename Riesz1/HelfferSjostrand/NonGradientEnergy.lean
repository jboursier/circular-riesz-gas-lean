/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.NonGradientInverse
public import Riesz1.ToMathlib.Variational.QuadraticMinimum

/-!
# The quotient inverse energy and its minimizer

The quotient case of the inverse energy and the minimization assertion of
Proposition 3.2. The energy is the integral pairing with the unique
normalized inverse on its entire carrier.
-/

@[expose] public section

noncomputable section

open MeasureTheory InnerProductSpace

namespace Riesz1

variable {N : ℕ+} {c : ℝ}

local instance (μ : Measure (HsConfiguration N)) [IsFiniteMeasure μ] :
    InnerProductSpace ℝ (HsSobolev μ) := inferInstance
local instance (μ : Measure (HsConfiguration N)) [IsFiniteMeasure μ] :
    NormedSpace ℝ (HsSobolev μ) := inferInstance
local instance (μ : Measure (HsConfiguration N)) [IsFiniteMeasure μ] :
    InnerProductSpace ℝ (PiLp 2 (fun _ : Fin (N : ℕ) => HsSobolev μ)) := inferInstance
local instance (μ : Measure (HsConfiguration N)) [IsFiniteMeasure μ] :
    InnerProductSpace ℝ (HsVectorJet μ) := inferInstance
local instance (μ : Measure (HsConfiguration N)) [IsFiniteMeasure μ] :
    NormedSpace ℝ (HsVectorJet μ) := inferInstance

variable (hPL : External.PrekopaLeindler)
  (χ : HsPairPotentials N c) (hN : 2 ≤ (N : ℕ)) (hc : 0 < c)

local notation "μ" => (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))

local instance : NormedAddCommGroup (HsSobolev μ) := inferInstance
local instance : InnerProductSpace ℝ (HsSobolev μ) := inferInstance
local instance : NormedSpace ℝ (HsSobolev μ) := inferInstance
local instance : NormedAddCommGroup (HsVectorJet μ) := inferInstance
local instance : InnerProductSpace ℝ (HsVectorJet μ) := inferInstance
local instance : NormedSpace ℝ (HsVectorJet μ) := inferInstance
local instance : NormedAddCommGroup (HsVectorSobolev χ hN hc μ) := inferInstance
local instance : InnerProductSpace ℝ (HsVectorSobolev χ hN hc μ) := inferInstance
local instance : NormedSpace ℝ (HsVectorSobolev χ hN hc μ) := inferInstance


/-- `𝒥_μ`, on the full compatible `L²` carrier. -/
def hsInverseEnergy (v : hsMeanZeroL2 μ) : ℝ :=
  hsNonGradientPairing μ v.val (hsInverse hPL χ hN hc v).val.val

theorem hsInverseEnergy_eq_integral (v : hsMeanZeroL2 μ) :
    hsInverseEnergy hPL χ hN hc v = ∫ x, ∑ i : Fin (N : ℕ),
      v.val x i * hsJetValue μ i (hsInverse hPL χ hN hc v).val.val x ∂μ :=
  hsNonGradientPairing_eq_integral μ v.val _

/-- The functional minimized in Proposition 3.2. -/
def hsNonGradientFunctional (v : hsMeanZeroL2 μ) (u : hsMeanZeroVector χ hN hc μ) : ℝ :=
  hsVectorSobolevForm χ hN hc μ u.val u.val - 2 * hsNonGradientPairing μ v.val u.val.val

/-- Exact expansion at the inverse, with no regularity restriction on the competitor. -/
theorem hsInverse_complete_square (v : hsMeanZeroL2 μ) (w : hsMeanZeroVector χ hN hc μ) :
    hsNonGradientFunctional χ hN hc v w =
      -hsInverseEnergy hPL χ hN hc v +
        hsVectorSobolevForm χ hN hc μ (w - hsInverse hPL χ hN hc v).val
          (w - hsInverse hPL χ hN hc v).val := by
  have hu := hsInverse_normalized_solves hPL χ hN hc v (hsInverse hPL χ hN hc v)
  have hw := hsInverse_normalized_solves hPL χ hN hc v w
  have he := Internal.quadratic_pairing_identity (hsNonGradientFullBilinear χ hN hc μ)
    (hsInverse hPL χ hN hc v).val w.val
    (hsNonGradientPairing μ v.val (hsInverse hPL χ hN hc v).val.val)
    (hsNonGradientPairing μ v.val w.val.val)
    ((hsNonGradientFullBilinear_eq χ hN hc μ _ _).trans hu)
    ((hsNonGradientFullBilinear_eq χ hN hc μ _ _).trans hw)
    (hsNonGradientFullBilinear_symm χ hN hc μ _ _)
  simp only [hsNonGradientFullBilinear_eq] at he
  exact he

namespace Internal

theorem hsNonGradient_form_nonneg (u : HsVectorSobolev χ hN hc μ) :
    0 ≤ hsVectorSobolevForm χ hN hc μ u u := by
  change 0 ≤ (∑ i : Fin (N : ℕ), inner ℝ _ _) + inner ℝ _ _
  exact add_nonneg (Finset.sum_nonneg fun i _ => real_inner_self_nonneg) real_inner_self_nonneg

theorem hsNonGradient_normalized_form_nonpos (hPL : External.PrekopaLeindler)
    (u : hsMeanZeroVector χ hN hc μ) (hq : hsVectorSobolevForm χ hN hc μ u.val u.val ≤ 0) : u = 0 := by
  have hb := hsNonGradient_norm_bound χ hN hc hPL u.val u.property
  have hC : 0 < 1 + hsPoincareConstant N c := by linarith [hsPoincareConstant_pos N c]
  have hns : ‖u.val‖ ^ 2 ≤ 0 := hb.trans (mul_nonpos_of_nonneg_of_nonpos hC.le hq)
  have hn : ‖u.val‖ ^ 2 = 0 := le_antisymm hns (sq_nonneg _)
  exact Subtype.ext (norm_eq_zero.mp (sq_eq_zero_iff.mp hn))

end Internal

theorem hsInverseFunctional_at_inverse (v : hsMeanZeroL2 μ) :
    hsNonGradientFunctional χ hN hc v (hsInverse hPL χ hN hc v) = -hsInverseEnergy hPL χ hN hc v := by
  have hs := hsInverse_normalized_solves hPL χ hN hc v (hsInverse hPL χ hN hc v)
  change hsVectorSobolevForm χ hN hc μ (hsInverse hPL χ hN hc v).val (hsInverse hPL χ hN hc v).val -
    2 * hsNonGradientPairing μ v.val (hsInverse hPL χ hN hc v).val.val =
      -hsNonGradientPairing μ v.val (hsInverse hPL χ hN hc v).val.val
  linarith only [hs]

/-- The normalized inverse is exactly the unique minimizer. -/
theorem hsInverse_minimizer_iff (v : hsMeanZeroL2 μ) (u : hsMeanZeroVector χ hN hc μ) :
    (∀ w : hsMeanZeroVector χ hN hc μ,
      hsNonGradientFunctional χ hN hc v u ≤ hsNonGradientFunctional χ hN hc v w) ↔
      u = hsInverse hPL χ hN hc v := by
  apply Internal.minimizer_iff_of_square_difference (hsNonGradientFunctional χ hN hc v)
    (fun w => hsVectorSobolevForm χ hN hc μ w.val w.val) (hsInverse hPL χ hN hc v)
    (fun w => (hsInverse_complete_square hPL χ hN hc v w).trans
      (congrArg (· + hsVectorSobolevForm χ hN hc μ (w - hsInverse hPL χ hN hc v).val
        (w - hsInverse hPL χ hN hc v).val) (hsInverseFunctional_at_inverse hPL χ hN hc v).symm))
    (fun w => Internal.hsNonGradient_form_nonneg χ hN hc w.val)
    (fun w => Internal.hsNonGradient_normalized_form_nonpos χ hN hc hPL w) u

theorem hsInverseEnergy_nonneg (v : hsMeanZeroL2 μ) : 0 ≤ hsInverseEnergy hPL χ hN hc v := by
  rw [hsInverseEnergy, ← hsInverse_normalized_solves hPL χ hN hc v (hsInverse hPL χ hN hc v),
    ← hsNonGradientFullBilinear_eq]
  change 0 ≤ inner ℝ (hsNonGradientDifferential χ hN hc μ _) (hsNonGradientDifferential χ hN hc μ _)
  exact real_inner_self_nonneg

end Riesz1
