/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.NonGradient

/-!
# Linearity, symmetry, positivity and sub-additivity of the quotient inverse

Quotient part, for the Gibbs probability `μ` and the inverse
`T = (A₁^μ)⁻¹` on `L²₀(μ; ℝᴺ)`. The energy is `𝒥_μ(v) = ∫ v · Tv dμ`.

Write `B` for the bilinear form `𝔮_μ` on the compatible vector space
(`hsNonGradientFullBilinear`). The defining equation of `T` gives `𝒥_μ(v) = B(Tv, Tv)` and
`∫ v · Tw dμ = B(Tv, Tw)`. Symmetry of `B` then gives the symmetry of the pairing. The
two-field bound follows from `𝒥_μ(w - v) ≥ 0`, and the three-field bound from applying the
two-field bound twice.
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

/-- The map `T` is linear on `L²₀(μ; ℝᴺ)`, so it respects linear combinations of
mean-zero fields. -/
theorem hsInverse_linear (a b : ℝ) (v w : hsMeanZeroL2 μ) :
    hsInverse hPL χ hN hc (a • v + b • w) =
      a • hsInverse hPL χ hN hc v + b • hsInverse hPL χ hN hc w := by
  simp only [map_add, map_smul]

/-- Symmetry: `∫ v · Tw dμ = ∫ w · Tv dμ` for mean-zero fields `v, w`.
Both sides equal the form `B(Tv, Tw)`, which is symmetric. -/
theorem hsInverse_integral_symm (v w : hsMeanZeroL2 μ) :
    ∫ x, ∑ i : Fin (N : ℕ), v.val x i * hsJetValue μ i (hsInverse hPL χ hN hc w).val.val x ∂μ =
      ∫ x, ∑ i : Fin (N : ℕ), w.val x i * hsJetValue μ i (hsInverse hPL χ hN hc v).val.val x ∂μ := by
  have hpair : hsNonGradientPairing μ v.val (hsInverse hPL χ hN hc w).val.val =
      hsNonGradientPairing μ w.val (hsInverse hPL χ hN hc v).val.val :=
    (hsInverse_normalized_solves hPL χ hN hc v (hsInverse hPL χ hN hc w)).symm.trans
      ((hsNonGradientFullBilinear_eq χ hN hc μ _ _).symm.trans
        ((hsNonGradientFullBilinear_symm χ hN hc μ _ _).trans
          ((hsNonGradientFullBilinear_eq χ hN hc μ _ _).trans
            (hsInverse_normalized_solves hPL χ hN hc w (hsInverse hPL χ hN hc v)))))
  exact (hsNonGradientPairing_eq_integral μ v.val _).symm.trans
    (hpair.trans (hsNonGradientPairing_eq_integral μ w.val _))

/-- The energy `𝒥_μ(v)` is the form of the inverse with
itself. -/
theorem hsInverseEnergy_eq_form (v : hsMeanZeroL2 μ) :
    hsInverseEnergy hPL χ hN hc v = hsNonGradientFullBilinear χ hN hc μ
      (hsInverse hPL χ hN hc v).val (hsInverse hPL χ hN hc v).val :=
  ((hsInverse_normalized_solves hPL χ hN hc v (hsInverse hPL χ hN hc v)).symm).trans
    (hsNonGradientFullBilinear_eq χ hN hc μ _ _).symm

/-- Expansion of the energy of a sum: `𝒥(v + w) = 𝒥(v) + 2 B(Tv, Tw) + 𝒥(w)`. -/
theorem hsInverseEnergy_add (v w : hsMeanZeroL2 μ) :
    hsInverseEnergy hPL χ hN hc (v + w) = hsInverseEnergy hPL χ hN hc v +
      2 * hsNonGradientFullBilinear χ hN hc μ (hsInverse hPL χ hN hc v).val
        (hsInverse hPL χ hN hc w).val + hsInverseEnergy hPL χ hN hc w := by
  have hsym := hsNonGradientFullBilinear_symm χ hN hc μ (hsInverse hPL χ hN hc v).val
    (hsInverse hPL χ hN hc w).val
  simp only [hsInverseEnergy_eq_form, map_add, add_apply, Submodule.coe_add]
  linarith [hsym]

/-- Values: `T(w - v) = Tw - Tv`. -/
theorem hsInverse_sub_val (v w : hsMeanZeroL2 μ) :
    (hsInverse hPL χ hN hc (w - v)).val =
      (hsInverse hPL χ hN hc w).val - (hsInverse hPL χ hN hc v).val := by
  simp only [map_sub, Submodule.coe_sub]

/-- The energy of a difference is the form of `Tw - Tv` with itself. -/
theorem hsInverseEnergy_sub_eq_form (v w : hsMeanZeroL2 μ) :
    hsInverseEnergy hPL χ hN hc (w - v) = hsNonGradientFullBilinear χ hN hc μ
      ((hsInverse hPL χ hN hc w).val - (hsInverse hPL χ hN hc v).val)
      ((hsInverse hPL χ hN hc w).val - (hsInverse hPL χ hN hc v).val) := by
  exact (hsInverseEnergy_eq_form hPL χ hN hc (w - v)).trans
    (congrArg₂ (fun x y => hsNonGradientFullBilinear χ hN hc μ x y)
      (hsInverse_sub_val hPL χ hN hc v w) (hsInverse_sub_val hPL χ hN hc v w))

/-- The expansion of `B(Tw - Tv, Tw - Tv)` used for sub-additivity:
`B(Tw, Tw) - 2 B(Tv, Tw) = -𝒥(v) + B(Tw - Tv, Tw - Tv)`. -/
theorem hsInverse_riesz_identity (v w : hsMeanZeroL2 μ) :
    hsNonGradientFullBilinear χ hN hc μ (hsInverse hPL χ hN hc w).val (hsInverse hPL χ hN hc w).val -
      2 * hsNonGradientFullBilinear χ hN hc μ (hsInverse hPL χ hN hc v).val
        (hsInverse hPL χ hN hc w).val =
      -hsInverseEnergy hPL χ hN hc v + hsNonGradientFullBilinear χ hN hc μ
        ((hsInverse hPL χ hN hc w).val - (hsInverse hPL χ hN hc v).val)
        ((hsInverse hPL χ hN hc w).val - (hsInverse hPL χ hN hc v).val) :=
  Internal.quadratic_pairing_identity (hsNonGradientFullBilinear χ hN hc μ)
    (hsInverse hPL χ hN hc v).val (hsInverse hPL χ hN hc w).val
    (hsInverseEnergy hPL χ hN hc v)
    (hsNonGradientFullBilinear χ hN hc μ (hsInverse hPL χ hN hc v).val
      (hsInverse hPL χ hN hc w).val)
    (hsInverseEnergy_eq_form hPL χ hN hc v).symm rfl
    (hsNonGradientFullBilinear_symm χ hN hc μ (hsInverse hPL χ hN hc w).val
      (hsInverse hPL χ hN hc v).val)

/-- Real arithmetic closing the two-field bound from the energy expansion, the Riesz identity and
the nonnegativity of the form of the difference. -/
theorem two_field_bound_of_expansions (Jv Jw X Bww Q Jvw : ℝ) (hsum : Jvw = Jv + 2 * X + Jw)
    (hriesz : Bww - 2 * X = -Jv + Q) (hQ : 0 ≤ Q) (hJw : Jw = Bww) :
    Jvw ≤ 2 * Jv + 2 * Jw := by
  linarith

/-- Two-field sub-additivity: `𝒥_μ(v + w) ≤ 2 𝒥_μ(v) + 2 𝒥_μ(w)`.
The form of `Tw - Tv` is nonnegative, which bounds the cross term by the two energies. -/
theorem hsInverseEnergy_subadd (v w : hsMeanZeroL2 μ) :
    hsInverseEnergy hPL χ hN hc (v + w) ≤
      2 * hsInverseEnergy hPL χ hN hc v + 2 * hsInverseEnergy hPL χ hN hc w := by
  have hnn := hsInverseEnergy_nonneg hPL χ hN hc (w - v)
  rw [hsInverseEnergy_sub_eq_form hPL χ hN hc v w] at hnn
  exact two_field_bound_of_expansions _ _ _ _ _ _ (hsInverseEnergy_add hPL χ hN hc v w)
    (hsInverse_riesz_identity hPL χ hN hc v w) hnn (hsInverseEnergy_eq_form hPL χ hN hc w)

/-- Three-field sub-additivity:
`𝒥_μ(a + b + d) ≤ 4 𝒥_μ(a) + 4 𝒥_μ(b) + 2 𝒥_μ(d)`. -/
theorem hsInverseEnergy_subadd_three (a b d : hsMeanZeroL2 μ) :
    hsInverseEnergy hPL χ hN hc (a + b + d) ≤
      4 * hsInverseEnergy hPL χ hN hc a + 4 * hsInverseEnergy hPL χ hN hc b +
        2 * hsInverseEnergy hPL χ hN hc d := by
  have h1 := hsInverseEnergy_subadd hPL χ hN hc (a + b) d
  have h2 := hsInverseEnergy_subadd hPL χ hN hc a b
  linarith only [h1, h2]

end Riesz1

end
