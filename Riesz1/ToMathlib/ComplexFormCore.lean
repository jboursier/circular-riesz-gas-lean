/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Topology.Algebra.Module.Basic

/-!
# Form cores in real and imaginary coordinates

The complex form topology is the sum-of-squares topology on its two real
components. Density of a real core therefore gives density of its pairs.
-/

@[expose] public section

noncomputable section

open Set

namespace Riesz1

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Source forms with real and imaginary parts in the prescribed real core. -/
def complexFormTests (S : Submodule ℝ V) : Set (WithLp 2 (V × V)) :=
  {v | v.ofLp.1 ∈ S ∧ v.ofLp.2 ∈ S}

/-- Density for the complex form norm follows from density for the real form norm. -/
theorem dense_complexFormTests {S : Submodule ℝ V} (hS : Dense (S : Set V)) :
    Dense (complexFormTests S) := by
  have hdS : DenseRange S.subtype := by
    intro x
    apply closure_mono (s := (S : Set V)) ?_ (hS x)
    intro y hy
    exact ⟨⟨y, hy⟩, rfl⟩
  let e := WithLp.homeomorphProd 2 V V
  have hd : DenseRange (fun p : S × S => (p.1.val, p.2.val)) := hdS.prodMap hdS
  have he : DenseRange e.symm := e.symm.surjective.denseRange
  apply (he.comp hd e.symm.continuous).mono
  rintro _ ⟨⟨r, i⟩, rfl⟩
  exact ⟨r.property, i.property⟩

end Riesz1
