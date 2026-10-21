/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.SettingHamiltonian

/-!
# Smooth lifts and the scalar Langevin expression

This file covers the smooth lifts and the differential expression.
Tests are globally smooth periodic lifts, with support separated from the
collision complement. For `N ≥ 2` this is the smooth zero extension of a
test on the chamber. Using extended distance also treats `N = 1`, whose
collision complement is empty, without an artificial boundary condition.
This file does not construct the weighted Sobolev completion.
-/

@[expose] public section

noncomputable section

open Set Metric
open scoped ENNReal ContDiff

namespace Riesz1

/-- A periodic lift smooth on a neighborhood of the closed lifted chamber. -/
def HsSmoothOnClosure (N : ℕ+) (f : HsEuclidean N → ℝ) : Prop :=
  (∀ (k : ℤ) x, f (hsTranslate (k : ℝ) x) = f x) ∧
    ∃ U : Set (HsEuclidean N), IsOpen U ∧ closure (hsChamber N) ⊆ U ∧ ContDiffOn ℝ ∞ f U

/-- Smooth tests on the quotient, encoded by their smooth periodic zero extensions. -/
structure HsTestFunction (N : ℕ+) where
  toFun : HsEuclidean N → ℝ
  smooth : ContDiff ℝ ∞ toFun
  periodic : ∀ (k : ℤ) x, toFun (hsTranslate (k : ℝ) x) = toFun x
  boundarySupport : ∃ δ : ℝ, 0 < δ ∧ ∀ x, toFun x ≠ 0 →
    ENNReal.ofReal δ ≤ infEDist x (hsChamber N)ᶜ

instance (N : ℕ+) : CoeFun (HsTestFunction N) (fun _ => HsEuclidean N → ℝ) := ⟨fun f => f.toFun⟩

theorem HsTestFunction.smoothOnClosure {N : ℕ+} (f : HsTestFunction N) :
    HsSmoothOnClosure N f :=
  ⟨f.periodic, univ, isOpen_univ, subset_univ _, f.smooth.contDiffOn⟩

theorem HsTestFunction.eq_zero_of_not_mem {N : ℕ+} (f : HsTestFunction N)
    {x : HsEuclidean N} (hx : x ∉ hsChamber N) : f x = 0 := by
  by_contra hf
  obtain ⟨δ, hδ, hs⟩ := f.boundarySupport
  have := hs x hf
  rw [infEDist_zero_of_mem hx] at this
  exact (ENNReal.ofReal_pos.mpr hδ).not_ge this

theorem HsTestFunction.support_distance {N : ℕ+} (hN : 2 ≤ (N : ℕ)) (f : HsTestFunction N) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x, f x ≠ 0 → δ ≤ hsBoundaryDistance N hN x := by
  obtain ⟨δ, hδ, hs⟩ := f.boundarySupport
  refine ⟨δ, hδ, fun x hx => ?_⟩
  exact (ENNReal.ofReal_le_iff_le_toReal
    (infEDist_ne_top (hsChamber_compl_nonempty hN))).mp (hs x hx)

/-- A test evaluated on the quotient, through its unique fundamental representative. -/
def hsTestOnQuotient {N : ℕ+} (f : HsTestFunction N) (x : HsConfiguration N) : ℝ :=
  f (WithLp.toLp 2 ((hsConfigurationEquiv N).symm x).val)

theorem hsTestOnQuotient_configurationMap {N : ℕ+} (f : HsTestFunction N)
    (X : Configuration N) :
    hsTestOnQuotient f (hsConfigurationMap N X) = f (WithLp.toLp 2 X.val) := by
  change f (WithLp.toLp 2 ((hsConfigurationEquiv N).symm ((hsConfigurationEquiv N) X)).val) = _
  rw [Equiv.symm_apply_apply]

/-- The scalar Langevin differential expression on the entire chamber. -/
def hsLangevinLift {N : ℕ+} {c : ℝ} (χ : HsPairPotentials N c) (f : HsTestFunction N)
    (x : hsChamber N) : ℝ :=
  inner ℝ (gradient (hsPairExpression χ) x.val) (gradient f x.val) - Laplacian.laplacian f.toFun x.val

/-- The same expression as a function on the cyclic quotient. -/
def hsLangevin {N : ℕ+} {c : ℝ} (χ : HsPairPotentials N c) (f : HsTestFunction N)
    (x : HsConfiguration N) : ℝ :=
  let X := (hsConfigurationEquiv N).symm x
  hsLangevinLift χ f ⟨WithLp.toLp 2 X.val, ⟨X.property.1, X.property.2.2.2⟩⟩

end Riesz1

end
