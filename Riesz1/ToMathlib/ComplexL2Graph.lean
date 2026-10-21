/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.ComplexL2
public import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-!
# Complexification of real L² operator graphs

The complex graph consists exactly of the pairs whose real and imaginary
parts lie in the real graph. Closure and self-adjointness transfer through
these continuous coordinates.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Riesz1

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)

/-- Complexification of an actual real L² subspace, by its two coordinates. -/
def complexifyL2Submodule (S : Submodule ℝ (Lp ℝ 2 μ)) : Submodule ℂ (Lp ℂ 2 μ) where
  carrier := {f | complexL2Re μ f ∈ S ∧ complexL2Im μ f ∈ S}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg
    change complexL2Re μ (f + g) ∈ S ∧ complexL2Im μ (f + g) ∈ S
    simpa only [map_add] using And.intro (S.add_mem hf.1 hg.1) (S.add_mem hf.2 hg.2)
  smul_mem' := by
    intro z f hf
    change complexL2Re μ (z • f) ∈ S ∧ complexL2Im μ (z • f) ∈ S
    rw [complexL2Re_smul, complexL2Im_smul]
    exact ⟨S.sub_mem (S.smul_mem _ hf.1) (S.smul_mem _ hf.2),
      S.add_mem (S.smul_mem _ hf.2) (S.smul_mem _ hf.1)⟩

/-- Real coordinates of a complex graph pair. -/
def complexL2GraphRe : (Lp ℂ 2 μ × Lp ℂ 2 μ) →L[ℝ] (Lp ℝ 2 μ × Lp ℝ 2 μ) :=
  (complexL2Re μ).prodMap (complexL2Re μ)

/-- Imaginary coordinates of a complex graph pair. -/
def complexL2GraphIm : (Lp ℂ 2 μ × Lp ℂ 2 μ) →L[ℝ] (Lp ℝ 2 μ × Lp ℝ 2 μ) :=
  (complexL2Im μ).prodMap (complexL2Im μ)

/-- Reconstruction of a graph pair from its real and imaginary graph coordinates. -/
def complexL2GraphOfPair :
    ((Lp ℝ 2 μ × Lp ℝ 2 μ) × (Lp ℝ 2 μ × Lp ℝ 2 μ)) →L[ℝ]
      (Lp ℂ 2 μ × Lp ℂ 2 μ) :=
  ((complexL2OfPair μ).comp
    ((ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.fst ℝ _ _) |>.prod
      ((ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _)))).prod
    ((complexL2OfPair μ).comp
      ((ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.fst ℝ _ _) |>.prod
        ((ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _))))

/-- The complex-linear graph of the componentwise complexification. -/
def complexifyL2Graph (G : Submodule ℝ (Lp ℝ 2 μ × Lp ℝ 2 μ)) :
    Submodule ℂ (Lp ℂ 2 μ × Lp ℂ 2 μ) where
  carrier := {p | complexL2GraphRe μ p ∈ G ∧ complexL2GraphIm μ p ∈ G}
  zero_mem' := by simp
  add_mem' := by
    intro p q hp hq
    change complexL2GraphRe μ (p + q) ∈ G ∧ complexL2GraphIm μ (p + q) ∈ G
    simpa only [map_add] using And.intro (G.add_mem hp.1 hq.1) (G.add_mem hp.2 hq.2)
  smul_mem' := by
    intro z p hp
    have hr : complexL2GraphRe μ (z • p) =
        z.re • complexL2GraphRe μ p - z.im • complexL2GraphIm μ p := by
      exact Prod.ext (complexL2Re_smul μ z p.1) (complexL2Re_smul μ z p.2)
    have hi : complexL2GraphIm μ (z • p) =
        z.re • complexL2GraphIm μ p + z.im • complexL2GraphRe μ p := by
      exact Prod.ext (complexL2Im_smul μ z p.1) (complexL2Im_smul μ z p.2)
    change complexL2GraphRe μ (z • p) ∈ G ∧ complexL2GraphIm μ (z • p) ∈ G
    rw [hr, hi]
    exact ⟨G.sub_mem (G.smul_mem _ hp.1) (G.smul_mem _ hp.2),
      G.add_mem (G.smul_mem _ hp.2) (G.smul_mem _ hp.1)⟩

theorem complexifyL2Graph_isClosed {G : Submodule ℝ (Lp ℝ 2 μ × Lp ℝ 2 μ)}
    (hG : IsClosed (G : Set (Lp ℝ 2 μ × Lp ℝ 2 μ))) : IsClosed (complexifyL2Graph μ G : Set (Lp ℂ 2 μ × Lp ℂ 2 μ)) :=
  (hG.preimage (complexL2GraphRe μ).continuous).inter
    (hG.preimage (complexL2GraphIm μ).continuous)

/-- Complexification commutes with graph closure. -/
theorem complexifyL2Graph_closure (G : Submodule ℝ (Lp ℝ 2 μ × Lp ℝ 2 μ)) :
    (complexifyL2Graph μ G).topologicalClosure = complexifyL2Graph μ G.topologicalClosure := by
  apply le_antisymm
  · have hm : complexifyL2Graph μ G ≤ complexifyL2Graph μ G.topologicalClosure := by
      intro p hp
      exact ⟨G.le_topologicalClosure hp.1, G.le_topologicalClosure hp.2⟩
    exact (complexifyL2Graph μ G).topologicalClosure_minimal hm
      (complexifyL2Graph_isClosed μ G.isClosed_topologicalClosure)
  · intro p hp
    have hri : (complexL2GraphRe μ p, complexL2GraphIm μ p) ∈
        closure ((G : Set (Lp ℝ 2 μ × Lp ℝ 2 μ)) ×ˢ (G : Set (Lp ℝ 2 μ × Lp ℝ 2 μ))) := by
      rw [closure_prod_eq]
      exact hp
    have himage := image_closure_subset_closure_image (complexL2GraphOfPair μ).continuous
      ⟨_, hri, rfl⟩
    have he : complexL2GraphOfPair μ (complexL2GraphRe μ p, complexL2GraphIm μ p) = p :=
      Prod.ext (complexL2OfPair_re_im μ p.1) (complexL2OfPair_re_im μ p.2)
    rw [he] at himage
    apply closure_mono (s := complexL2GraphOfPair μ '' ((G : Set (Lp ℝ 2 μ × Lp ℝ 2 μ)) ×ˢ (G : Set (Lp ℝ 2 μ × Lp ℝ 2 μ)))) ?_ himage
    rintro _ ⟨⟨r, i⟩, ⟨hr, hi⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · have he : complexL2GraphRe μ (complexL2GraphOfPair μ (r, i)) = r :=
        Prod.ext (complexL2Re_ofPair μ _) (complexL2Re_ofPair μ _)
      rw [he]
      exact hr
    · have he : complexL2GraphIm μ (complexL2GraphOfPair μ (r, i)) = i :=
        Prod.ext (complexL2Im_ofPair μ _) (complexL2Im_ofPair μ _)
      rw [he]
      exact hi

/-- A self-adjoint real graph has a self-adjoint complex graph. -/
theorem complexifyL2Graph_adjoint {G : Submodule ℝ (Lp ℝ 2 μ × Lp ℝ 2 μ)}
    (hG : G.adjoint = G) : (complexifyL2Graph μ G).adjoint = complexifyL2Graph μ G := by
  apply le_antisymm
  · rintro ⟨f, a⟩ hp
    have hp' := (Submodule.mem_adjoint_iff _ _).mp hp
    have htest (b d : Lp ℝ 2 μ) (hbd : (b, d) ∈ G) :
        inner ℂ (realL2Complex μ d) f - inner ℂ (realL2Complex μ b) a = 0 := by
      apply hp' _ _
      change (complexL2Re μ (realL2Complex μ b), complexL2Re μ (realL2Complex μ d)) ∈ G ∧
        (complexL2Im μ (realL2Complex μ b), complexL2Im μ (realL2Complex μ d)) ∈ G
      simp only [complexL2Re_ofReal, complexL2Im_ofReal]
      exact ⟨hbd, G.zero_mem⟩
    constructor
    · rw [← hG]
      apply (Submodule.mem_adjoint_iff _ _).mpr
      intro b d hbd
      change inner ℝ d (complexL2Re μ f) - inner ℝ b (complexL2Re μ a) = 0
      have h := congrArg Complex.re (htest b d hbd)
      simpa only [Complex.sub_re, Complex.zero_re, complexL2_inner_re,
        complexL2Re_ofReal, complexL2Im_ofReal, inner_zero_left, add_zero] using h
    · rw [← hG]
      apply (Submodule.mem_adjoint_iff _ _).mpr
      intro b d hbd
      change inner ℝ d (complexL2Im μ f) - inner ℝ b (complexL2Im μ a) = 0
      have h := congrArg Complex.im (htest b d hbd)
      simpa only [Complex.sub_im, Complex.zero_im, complexL2_inner_im,
        complexL2Re_ofReal, complexL2Im_ofReal, inner_zero_left, sub_zero] using h
  · rintro ⟨f, a⟩ hp
    have hpr : complexL2GraphRe μ (f, a) ∈ G.adjoint := by rw [hG]; exact hp.1
    have hpi : complexL2GraphIm μ (f, a) ∈ G.adjoint := by rw [hG]; exact hp.2
    apply (Submodule.mem_adjoint_iff _ _).mpr
    intro b d hbd
    have hrr := (Submodule.mem_adjoint_iff _ _).mp hpr _ _ hbd.1
    have hii := (Submodule.mem_adjoint_iff _ _).mp hpi _ _ hbd.2
    have hri := (Submodule.mem_adjoint_iff _ _).mp hpi _ _ hbd.1
    have hir := (Submodule.mem_adjoint_iff _ _).mp hpr _ _ hbd.2
    apply Complex.ext
    · simp only [Complex.sub_re, Complex.zero_re, complexL2_inner_re]
      change inner ℝ (complexL2Re μ d) (complexL2Re μ f) -
        inner ℝ (complexL2Re μ b) (complexL2Re μ a) = 0 at hrr
      change inner ℝ (complexL2Im μ d) (complexL2Im μ f) -
        inner ℝ (complexL2Im μ b) (complexL2Im μ a) = 0 at hii
      linarith
    · simp only [Complex.sub_im, Complex.zero_im, complexL2_inner_im]
      change inner ℝ (complexL2Re μ d) (complexL2Im μ f) -
        inner ℝ (complexL2Re μ b) (complexL2Im μ a) = 0 at hri
      change inner ℝ (complexL2Im μ d) (complexL2Re μ f) -
        inner ℝ (complexL2Im μ b) (complexL2Re μ a) = 0 at hir
      linarith

end Riesz1
