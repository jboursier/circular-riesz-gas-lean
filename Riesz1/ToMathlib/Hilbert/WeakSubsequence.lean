/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Normed.Module.WeakDual
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Algebra.Module.Basic

/-!
# Weakly convergent subsequences of bounded sequences in a real Hilbert space

Every bounded sequence `x` in a real Hilbert space has a subsequence `x ∘ φ` that converges weakly
to some vector `x₀`, that is, `⟪x (φ m), y⟫ → ⟪x₀, y⟫` for every `y`.

Mathlib has no weak sequential compactness for Hilbert spaces, but it has the sequential
Banach–Alaoglu theorem `WeakDual.isSeqCompact_closedBall` for separable normed spaces. The proof
applies that theorem in the closed span `S` of the sequence, which is separable. The Riesz
representation `InnerProductSpace.toDual` turns weak-star limits of functionals into weak limits
of vectors in `S`. The limit then passes to the whole space through the orthogonal projection onto
`S`, because the sequence and its limit both lie in `S`.
-/

@[expose] public section

noncomputable section

open Filter Topology

namespace Riesz1

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A bounded sequence in a real Hilbert space has a weakly convergent subsequence: there are a
strictly increasing `φ` and a vector `x₀` with `⟪x (φ m), y⟫ → ⟪x₀, y⟫` for every `y`. -/
theorem exists_weak_subsequence_tendsto [CompleteSpace H] {x : ℕ → H} {C : ℝ}
    (hx : ∀ k, ‖x k‖ ≤ C) :
    ∃ (φ : ℕ → ℕ) (x₀ : H), StrictMono φ ∧
      ∀ y : H, Tendsto (fun m => inner ℝ (x (φ m)) y) atTop (𝓝 (inner ℝ x₀ y)) := by
  -- The closed span of the sequence is a closed, hence complete, separable subspace.
  let S : Submodule ℝ H := (Submodule.span ℝ (Set.range x)).topologicalClosure
  have hSclosed : IsClosed (S : Set H) := Submodule.isClosed_topologicalClosure _
  have : CompleteSpace S := hSclosed.completeSpace_coe
  have hsep : TopologicalSpace.IsSeparable (S : Set H) :=
    ((Set.countable_range x).isSeparable.span).closure
  have : TopologicalSpace.SeparableSpace S := hsep.separableSpace
  have hxS : ∀ k, x k ∈ S := fun k =>
    Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨k, rfl⟩)
  let xs : ℕ → S := fun k => ⟨x k, hxS k⟩
  -- The Riesz functionals of the sequence lie in a closed ball of the dual of `S`.
  let f : ℕ → WeakDual ℝ S := fun k =>
    StrongDual.toWeakDual (InnerProductSpace.toDual ℝ S (xs k))
  have hf : ∀ k, f k ∈ WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℝ S) C := by
    intro k
    have hnorm : ‖InnerProductSpace.toDual ℝ S (xs k)‖ ≤ C := by
      rw [LinearIsometryEquiv.norm_map]
      exact hx k
    have e : WeakDual.toStrongDual (f k) = InnerProductSpace.toDual ℝ S (xs k) :=
      StrongDual.toStrongDual_toWeakDual _
    rw [Set.mem_preimage, e]
    exact mem_closedBall_zero_iff.mpr hnorm
  obtain ⟨a, -, ψ, hψ, hlim⟩ := (WeakDual.isSeqCompact_closedBall ℝ S 0 C) hf
  -- The weak-star limit `a` is the Riesz functional of a vector `x₀S` of `S`.
  let x₀S : S := (InnerProductSpace.toDual ℝ S).symm (WeakDual.toStrongDual a)
  have hweak : ∀ z : S, Tendsto (fun m => inner ℝ (xs (ψ m)) z) atTop
      (𝓝 (inner ℝ x₀S z)) := by
    intro z
    have hz := ((WeakDual.eval_continuous z).tendsto a).comp hlim
    have hlimeq : a z = inner ℝ x₀S z :=
      (InnerProductSpace.toDual_symm_apply (x := z) (y := WeakDual.toStrongDual a)).symm
    rw [← hlimeq]
    refine hz.congr fun m => ?_
    simp [f, InnerProductSpace.toDual_apply_apply]
  refine ⟨ψ, (x₀S : H), hψ, fun y => ?_⟩
  -- Pass from `S` to `H`: the orthogonal projection `P` of `y` onto `S` satisfies
  -- `⟪v, y⟫ = ⟪v, P⟫` for every `v ∈ S`, because `y - P ∈ Sᗮ`.
  let P : H := S.starProjection y
  have hPS : P ∈ S := S.starProjection_apply_mem y
  have hperp : y - P ∈ Sᗮ := S.sub_starProjection_mem_orthogonal y
  have hproj : ∀ v : H, v ∈ S → inner ℝ v y = inner ℝ v P := by
    intro v hv
    have h0 := Submodule.inner_right_of_mem_orthogonal hv hperp
    rw [inner_sub_right, sub_eq_zero] at h0
    exact h0
  have hfun : (fun m => inner ℝ (x (ψ m)) y) = fun m => inner ℝ (xs (ψ m) : H) P := by
    funext m
    exact hproj (x (ψ m)) (hxS (ψ m))
  rw [hfun, hproj (x₀S : H) x₀S.2]
  have hP := hweak ⟨P, hPS⟩
  simpa [Submodule.coe_inner] using hP

end Riesz1
