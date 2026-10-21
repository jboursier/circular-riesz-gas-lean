/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.AnchoredLawSobolev
public import Riesz1.HelfferSjostrand.VectorEnergyForm

/-!
# The anchored vector quadratic form

For the anchored law `μ*` one uses `N - 1`
components, the test class `𝒟_N^* = C_c^∞(D_N^*)` on the open Euclidean simplex, the anchored
Hamiltonian `H*` and the same formula `q_{μ*}(u, h) = ∫ (∑_i ∇u_i · ∇h_i + u · ∇²H* h) dμ*`.

This file gives the definitions only. The completion `𝒱_{μ*}`, its closability, and the identity
of the anchored Hessian energy with `√(2 χ_ij''(y_j - y_i)) (w_j - w_i)` are not proved here.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace Riesz1

/-- The anchored test class `𝒟_N^* = C_c^∞(D_N^*)`: smooth functions with
compact support contained in the open Euclidean simplex `D_N^*`. -/
def anchoredTestSubmodule (n : ℕ) : Submodule ℝ (AnchoredEuclidean n → ℝ) where
  carrier := {f | ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ tsupport f ⊆ anchoredSimplex n}
  zero_mem' := ⟨contDiff_const, HasCompactSupport.zero, by simp⟩
  add_mem' := by
    rintro f g ⟨hf, hfc, hfs⟩ ⟨hg, hgc, hgs⟩
    refine ⟨hf.add hg, hfc.add hgc, (tsupport_add f g).trans (union_subset hfs hgs)⟩
  smul_mem' a f hf := by
    obtain ⟨hs, hc, hsup⟩ := hf
    refine ⟨hs.const_smul a, hc.smul_left, ?_⟩
    exact (tsupport_smul_subset_right (fun _ => a) f).trans hsup

/-- The `n`-tuples of anchored test functions, that is `N - 1` components for `n = N - 1`. -/
abbrev AnchoredVectorTest (n : ℕ) := Fin n → anchoredTestSubmodule n

/-- The vector `(u_1(y), …, u_n(y))` of an anchored tuple. -/
def anchoredTestVector {n : ℕ} (u : AnchoredVectorTest n) (y : AnchoredEuclidean n) :
    AnchoredEuclidean n :=
  WithLp.toLp 2 (fun i => (u i : AnchoredEuclidean n → ℝ) y)

/-- The pointwise integrand of the anchored form:
`∑_i ∇u_i · ∇h_i + u · ∇²H* h`, with `H* = hsAnchoredHamiltonianE`. -/
def anchoredVectorFormIntegrand {n : ℕ} {c : ℝ} (χ : HsPairPotentials n.succPNat c)
    (u h : AnchoredVectorTest n) (y : AnchoredEuclidean n) : ℝ :=
  ∑ i, inner ℝ (gradient (u i : AnchoredEuclidean n → ℝ) y)
      (gradient (h i : AnchoredEuclidean n → ℝ) y) +
    fderiv ℝ (fderiv ℝ (hsAnchoredHamiltonianE χ)) y (anchoredTestVector u y)
      (anchoredTestVector h y)

/-- The anchored vector quadratic form `q_{μ*}(u, h)`, integrated against
the anchored law `μ*`. -/
def anchoredVectorForm {n : ℕ} {c : ℝ} (χ : HsPairPotentials n.succPNat c)
    (u h : AnchoredVectorTest n) : ℝ :=
  ∫ y, anchoredVectorFormIntegrand χ u h y ∂(anchoredMeasureE χ)

end Riesz1

end
