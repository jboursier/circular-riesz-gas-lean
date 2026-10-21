/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.EllipticRegularity.Exhaustion
public import Mathlib.MeasureTheory.Group.Integral

/-!
# Translations of local weak derivatives

Weak derivatives commute with translations. In an invariant open domain,
uniqueness therefore makes every weak derivative of a periodic function
periodic almost everywhere. These results apply to real and complex values.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace Riesz1

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [NormedSpace ℝ F] [CompleteSpace F] in
/-- Local square integrability transports to the translated domain. -/
theorem LocallySquareIntegrableOn.comp_add_right {U : Set E} {u : E → F}
    (hu : LocallySquareIntegrableOn U u) (a : E) :
    LocallySquareIntegrableOn ((fun x => x + a) ⁻¹' U) (fun x => u (x + a)) := by
  intro K hK hKU
  have hI := hu ((fun x => x + a) '' K) (hK.image (continuous_id.add continuous_const))
    (by rintro _ ⟨x, hx, rfl⟩; exact hKU hx)
  have hm := (measurePreserving_add_right (volume : Measure E) a).restrict_preimage
    (s := (fun x => x + a) '' K)
    (hK.image (continuous_id.add (continuous_const (y := a)))).measurableSet
  have he : (fun x => x + a) ⁻¹' ((fun x => x + a) '' K) = K :=
    preimage_image_eq K (add_left_injective a)
  rw [he] at hm
  exact hI.comp_measurePreserving hm

omit [CompleteSpace F] in
/-- Local weak differentiation commutes with translation, using local L²
certificates to transport the local integrability of both representatives. -/
theorem HasWeakDirectionalDerivativeOn.comp_add_right {U : Set E} (hU : IsOpen U)
    {u g : E → F} {v : E} (hd : HasWeakDirectionalDerivativeOn U u g v)
    (hu : LocallySquareIntegrableOn U u) (hg : LocallySquareIntegrableOn U g) (a : E) :
    HasWeakDirectionalDerivativeOn ((fun x => x + a) ⁻¹' U)
      (fun x => u (x + a)) (fun x => g (x + a)) v := by
  have hV : IsOpen ((fun x => x + a) ⁻¹' U) :=
    hU.preimage (continuous_id.add continuous_const)
  refine ⟨(hu.comp_add_right a).locallyIntegrableOn hV,
    (hg.comp_add_right a).locallyIntegrableOn hV, ?_⟩
  intro φ hφ hφc hφV
  have hc : HasCompactSupport (fun x => φ (x + -a)) :=
    hφc.comp_homeomorph (Homeomorph.addRight (-a))
  have hs : tsupport (fun x => φ (x + -a)) ⊆ U := by
    intro x hx
    have hx' : x + -a ∈ tsupport φ := by
      change x ∈ closure ((fun x => x + -a) ⁻¹' Function.support φ) at hx
      exact (continuous_id.add (continuous_const (y := -a))).closure_preimage_subset
        (Function.support φ) hx
    have hy : (x + -a) + a ∈ U := hφV hx'
    simpa only [neg_add_cancel_right] using hy
  have ht := hd.2.2 (fun x => φ (x + -a))
    (hφ.comp (contDiff_id.add contDiff_const)) hc hs
  have he₁ : (∫ x, φ x • g (x + a)) = ∫ x, φ (x + -a) • g x := by
    simpa only [add_neg_cancel_right] using
      integral_add_right_eq_self (fun x => φ (x + -a) • g x) a
  have he₂ : (∫ x, fderiv ℝ φ x v • u (x + a)) =
      ∫ x, fderiv ℝ (fun y => φ (y + -a)) x v • u x := by
    simpa only [fderiv_comp_add_right, add_neg_cancel_right] using
      integral_add_right_eq_self (fun x => fderiv ℝ φ (x + -a) v • u x) a
  rw [he₁, he₂, ht]

/-- Periodicity of a function forces periodicity of its weak derivative
almost everywhere, including on charts across a fundamental-region seam. -/
theorem HasWeakDirectionalDerivativeOn.ae_periodic {U : Set E} (hU : IsOpen U)
    {u g : E → F} {v a : E} (hd : HasWeakDirectionalDerivativeOn U u g v)
    (hu : LocallySquareIntegrableOn U u) (hg : LocallySquareIntegrableOn U g)
    (hUa : ∀ x, x + a ∈ U ↔ x ∈ U)
    (hua : ∀ x ∈ U, u (x + a) = u x) :
    (fun x => g (x + a)) =ᵐ[volume.restrict U] g := by
  have he : (fun x => x + a) ⁻¹' U = U := Set.ext hUa
  have ht := hd.comp_add_right hU hu hg a
  rw [he] at ht
  have hue : (fun x => u (x + a)) =ᵐ[volume.restrict U] u :=
    (ae_restrict_mem hU.measurableSet).mono (fun x hx => hua x hx)
  exact (ht.congr hU hue Filter.EventuallyEq.rfl).unique hU hd

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [NormedSpace ℝ F] [CompleteSpace F] in
/-- Normalization to a half-open strip is unchanged by an integer period. -/
theorem vectorStrip_normalize_periodic (v : E) (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ v = 1)
    (k : ℤ) (x : E) :
    (x + (k : ℝ) • v) + (-((⌊ℓ (x + (k : ℝ) • v)⌋ : ℤ) : ℝ)) • v =
      x + (-((⌊ℓ x⌋ : ℤ) : ℝ)) • v := by
  rw [map_add, map_smul, hℓ, smul_eq_mul, mul_one, Int.floor_add_intCast,
    Int.cast_add, neg_add, add_smul]
  module

omit [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] in
/-- An almost everywhere periodic representative agrees almost everywhere
with its values at the canonical representatives of the integer orbits.
Countability of the period group is essential to this argument. -/
theorem ae_eq_vectorStrip_normalize {U : Set E}
    (v : E) (ℓ : E →L[ℝ] ℝ) {g : E → F}
    (hg : ∀ k : ℤ, (fun x => g (x + (k : ℝ) • v)) =ᵐ[volume.restrict U] g) :
    (fun x => g (x + (-((⌊ℓ x⌋ : ℤ) : ℝ)) • v)) =ᵐ[volume.restrict U] g := by
  have ha := ae_all_iff.mpr hg
  filter_upwards [ha] with x hx
  simpa only [Int.cast_neg] using hx (-⌊ℓ x⌋)

/-- A periodic function with locally L² weak derivative has a pointwise
periodic representative of that derivative. No derivative is prescribed
as an additional hypothesis. It is normalized using uniqueness. -/
theorem HasWeakDirectionalDerivativeOn.periodic_representative {U : Set E} (hU : IsOpen U)
    {u g : E → F} {v w : E} (hd : HasWeakDirectionalDerivativeOn U u g w)
    (hu : LocallySquareIntegrableOn U u) (hg : LocallySquareIntegrableOn U g)
    (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ v = 1)
    (hUv : ∀ (k : ℤ) x, x + (k : ℝ) • v ∈ U ↔ x ∈ U)
    (hp : ∀ (k : ℤ) x, u (x + (k : ℝ) • v) = u x) :
    ∃ G : E → F, (∀ (k : ℤ) x, G (x + (k : ℝ) • v) = G x) ∧
      G =ᵐ[volume.restrict U] g ∧ LocallySquareIntegrableOn U G ∧
      HasWeakDirectionalDerivativeOn U u G w := by
  let G := fun x => g (x + (-((⌊ℓ x⌋ : ℤ) : ℝ)) • v)
  have he : G =ᵐ[volume.restrict U] g :=
    ae_eq_vectorStrip_normalize v ℓ
      (fun k => hd.ae_periodic hU hu hg (hUv k) (fun x _ => hp k x))
  exact ⟨G, fun k x => congrArg g (vectorStrip_normalize_periodic v ℓ hℓ k x),
    he, hg.congr he.symm, hd.congr hU Filter.EventuallyEq.rfl he.symm⟩

/-- Both orders of derivatives in local H² admit coherent pointwise
periodic representatives. Uniqueness on overlaps supplies their coherence. -/
theorem IsLocalH2.periodic_representatives {U : Set E} (hU : IsOpen U)
    {u : E → F} (hu : IsLocalH2 U u) {v : E}
    (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ v = 1)
    (hUv : ∀ (k : ℤ) x, x + (k : ℝ) • v ∈ U ↔ x ∈ U)
    (hp : ∀ (k : ℤ) x, u (x + (k : ℝ) • v) = u x) :
    ∃ (g : Fin (Module.finrank ℝ E) → E → F)
      (h : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → E → F),
      (∀ i (k : ℤ) x, g i (x + (k : ℝ) • v) = g i x) ∧
      (∀ i j (k : ℤ) x, h i j (x + (k : ℝ) • v) = h i j x) ∧
      ∀ i, LocallySquareIntegrableOn U (g i) ∧
        HasWeakDirectionalDerivativeOn U u (g i) (stdOrthonormalBasis ℝ E i) ∧
        ∀ j, LocallySquareIntegrableOn U (h i j) ∧
          HasWeakDirectionalDerivativeOn U (g i) (h i j) (stdOrthonormalBasis ℝ E j) := by
  classical
  obtain ⟨huL, g₀, h₀, hd⟩ := hu
  choose g hgp hge hgL hgd using fun i =>
    ((hd i).2.1).periodic_representative hU huL (hd i).1 ℓ hℓ hUv hp
  have hsecond (i j) :
      HasWeakDirectionalDerivativeOn U (g i) (h₀ i j) (stdOrthonormalBasis ℝ E j) :=
    (((hd i).2.2 j).2).congr hU (hge i).symm Filter.EventuallyEq.rfl
  choose h hhp _ hhL hhd using fun i j =>
    (hsecond i j).periodic_representative hU (hgL i) (((hd i).2.2 j).1)
      ℓ hℓ hUv (hgp i)
  exact ⟨g, h, hgp, hhp, fun i => ⟨hgL i, hgd i, fun j => ⟨hhL i j, hhd i j⟩⟩⟩

end Riesz1
