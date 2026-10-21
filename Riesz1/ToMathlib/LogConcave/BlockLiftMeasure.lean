/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Block assembly of labelled configurations preserves Lebesgue measure

Two blocks of coordinates, indexed by `Fin m` and by `Fin n`, are glued along a
bijection `e : Fin m ⊕ Fin n ≃ Fin N` into one configuration on `Fin N`. The gluing
is linear in the pair of blocks, and it is measure preserving from the product of two
Euclidean spaces onto one Euclidean space.

The proof composes three volume-preserving identifications: the forgetful map from
each Euclidean space to the pi type, the identification of a product of two pi types
with a pi type indexed by the sum, and the reindexing of coordinates along `e`. The
final identification back to `EuclideanSpace` closes the chain.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Riesz1

/-- Assemble a labelled configuration on `Fin N` from a block `p.1` (indexed by `Fin m`) and a
block `p.2` (indexed by `Fin n`), along a bijection `e : Fin m ⊕ Fin n ≃ Fin N`: coordinate `i`
is the entry of the block at the position `e.symm i`. -/
def blockLift {m n N : ℕ} (e : Fin m ⊕ Fin n ≃ Fin N)
    (p : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin N) :=
  WithLp.toLp 2 (fun i => Sum.elim (fun a => p.1 a) (fun b => p.2 b) (e.symm i))

theorem blockLift_apply {m n N : ℕ} (e : Fin m ⊕ Fin n ≃ Fin N)
    (p : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) (i : Fin N) :
    blockLift e p i = Sum.elim (fun a => p.1 a) (fun b => p.2 b) (e.symm i) := rfl

/-- Reindexing a real function on `Fin m ⊕ Fin n` along `e` reads off its value at `e.symm i`
at the coordinate `i` of `Fin N`. The statement holds up to a `cast` which is trivial here
because every coordinate has type `ℝ`. -/
theorem piCongrLeft_real_apply {m n N : ℕ} (e : Fin m ⊕ Fin n ≃ Fin N)
    (g : Fin m ⊕ Fin n → ℝ) (i : Fin N) :
    MeasurableEquiv.piCongrLeft (fun _ : Fin N => ℝ) e g i = g (e.symm i) := by
  rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast, cast_eq]

/-- Forgetting the Euclidean structure on both blocks preserves measure, from the product of
two Euclidean spaces to the product of the two underlying pi types. -/
theorem measurePreserving_ofLp_prod (m n : ℕ) :
    MeasurePreserving (Prod.map WithLp.ofLp WithLp.ofLp)
      (volume : Measure (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)))
      ((volume : Measure (Fin m → ℝ)).prod (volume : Measure (Fin n → ℝ))) :=
  (PiLp.volume_preserving_ofLp (Fin m)).prod (PiLp.volume_preserving_ofLp (Fin n))

/-- The assembly map is measure preserving from the product of two Euclidean spaces onto the
Euclidean space on `Fin N`. -/
theorem measurePreserving_blockLift {m n N : ℕ} (e : Fin m ⊕ Fin n ≃ Fin N) :
    MeasurePreserving (blockLift e)
      (volume : Measure (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)))
      (volume : Measure (EuclideanSpace ℝ (Fin N))) := by
  -- The chain is: forget the Euclidean structure, split the sum index, reindex along `e`,
  -- and restore the Euclidean structure on `Fin N`.
  have hcomp := (PiLp.volume_preserving_toLp (Fin N)).comp
    ((volume_measurePreserving_piCongrLeft (fun _ : Fin N => ℝ) e).comp
      ((volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin m ⊕ Fin n => ℝ)).comp
        (measurePreserving_ofLp_prod m n)))
  -- The composite agrees with `blockLift e` coordinatewise, by unfolding the definitions.
  convert hcomp using 1
  funext p
  refine congrArg (WithLp.toLp 2) (funext fun i => ?_)
  simp only [Function.comp_apply]
  rw [piCongrLeft_real_apply]
  rfl

theorem measurable_blockLift {m n N : ℕ} (e : Fin m ⊕ Fin n ≃ Fin N) :
    Measurable (blockLift e) :=
  (measurePreserving_blockLift e).measurable

theorem blockLift_add {m n N : ℕ} (e : Fin m ⊕ Fin n ≃ Fin N)
    (p q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) :
    blockLift e (p + q) = blockLift e p + blockLift e q := by
  ext i
  simp only [blockLift_apply, PiLp.add_apply, Prod.fst_add, Prod.snd_add]
  rcases e.symm i with a | b <;> simp

theorem blockLift_smul {m n N : ℕ} (e : Fin m ⊕ Fin n ≃ Fin N) (c : ℝ)
    (p : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) :
    blockLift e (c • p) = c • blockLift e p := by
  ext i
  simp only [blockLift_apply, PiLp.smul_apply, Prod.smul_fst, Prod.smul_snd]
  rcases e.symm i with a | b <;> simp

end Riesz1
