/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.LogConcave.PrekopaMarginalConvex
public import Riesz1.Frozen.External.PrekopaLeindler

/-!
# Convex marginal on a polytope (Lemma 3.7)

For an open convex set `Q ⊆ ℝ^m × ℝ^n` with `0 < n` and a finite convex potential `V` on `Q`,
the fiber integral `J(z) = ∫_{Q_z} e^{-V(z,y)} dy` is finite and positive on the projected
interior `π(Q)`, and `z ↦ -log J(z)` is convex there. Boundedness of `Q` is assumed in this
file. The bounded open convex sets include all bounded open convex polytopes, which are the
finite intersections of open half-spaces. The corollary `convexity_exterior_polytope_halfspaces`
states the polytope form literally. The unbounded case with locally bounded fibers is in
`Riesz1.HelfferSjostrand.ConvexityPolytopeLocal`.

The only external input is the midpoint Prékopa–Leindler inequality
`Riesz1.External.PrekopaLeindler`, passed explicitly as the hypothesis `hPL`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Topology Filter

namespace Riesz1

/-- The set integral of `e^{-V(z, ·)}` over the fiber of `Q` over `z` equals the integral of the
zero extension of `e^{-V}` on `Q`. -/
theorem setIntegral_fiber_eq_integral_indicator {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] {n : ℕ}
    {Q : Set (E × EuclideanSpace ℝ (Fin n))} {V : E × EuclideanSpace ℝ (Fin n) → ℝ}
    (hQo : IsOpen Q) (z : E) :
    ∫ y in {y : EuclideanSpace ℝ (Fin n) | (z, y) ∈ Q}, Real.exp (-V (z, y)) =
      ∫ y, Q.indicator (fun p => Real.exp (-V p)) (z, y) := by
  have hmeas : MeasurableSet {y : EuclideanSpace ℝ (Fin n) | (z, y) ∈ Q} :=
    (hQo.preimage (by fun_prop)).measurableSet
  rw [← integral_indicator hmeas]
  rfl

/-- The fiber integrand is integrable on the fiber, in the set-integral form. -/
theorem integrableOn_fiber_exp {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {n : ℕ}
    {Q : Set (E × EuclideanSpace ℝ (Fin n))} {V : E × EuclideanSpace ℝ (Fin n) → ℝ}
    (hQo : IsOpen Q) (hQb : Bornology.IsBounded Q) (hV : ConvexOn ℝ Q V) (z : E) :
    IntegrableOn (fun y => Real.exp (-V (z, y))) {y : EuclideanSpace ℝ (Fin n) | (z, y) ∈ Q} := by
  have hmeas : MeasurableSet {y : EuclideanSpace ℝ (Fin n) | (z, y) ∈ Q} :=
    (hQo.preimage (by fun_prop)).measurableSet
  have hint := integrable_fiber_exp_indicator (E := E) hQo hQb hV z
  have heq : (fun y => Q.indicator (fun p => Real.exp (-V p)) (z, y)) =
      {y : EuclideanSpace ℝ (Fin n) | (z, y) ∈ Q}.indicator
        (fun y => Real.exp (-V (z, y))) := by
    funext y
    rfl
  rw [heq] at hint
  exact (integrable_indicator_iff hmeas).1 hint

/-- **Convex marginal on a bounded open convex set** (part of Lemma 3.7,
generalized from polytopes to all bounded open convex
sets). For a bounded open convex set `Q` in `ℝ^m × ℝ^n` with `0 < n`, and a finite convex `V`
on `Q`, every fiber integral `J(z) = ∫_{Q_z} e^{-V(z,y)} dy` over the projected interior
`Prod.fst '' Q` is integrable and positive, and `z ↦ -log J(z)` is convex on that projected
interior. -/
theorem convexity_exterior_polytope_bounded (hPL : External.PrekopaLeindler) {m n : ℕ}
    (hn : 0 < n) (Q : Set (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)))
    (hQo : IsOpen Q) (hQc : Convex ℝ Q) (hQb : Bornology.IsBounded Q)
    (V : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n) → ℝ) (hV : ConvexOn ℝ Q V) :
    (∀ z ∈ Prod.fst '' Q,
      IntegrableOn (fun y => Real.exp (-V (z, y))) {y | (z, y) ∈ Q} ∧
        0 < ∫ y in {y | (z, y) ∈ Q}, Real.exp (-V (z, y))) ∧
    ConvexOn ℝ (Prod.fst '' Q)
      (fun z => -Real.log (∫ y in {y | (z, y) ∈ Q}, Real.exp (-V (z, y)))) := by
  have hfun : (fun z => -Real.log (∫ y in {y | (z, y) ∈ Q}, Real.exp (-V (z, y)))) =
      (fun z => -Real.log (∫ y, Q.indicator (fun p => Real.exp (-V p)) (z, y))) := by
    funext z
    rw [setIntegral_fiber_eq_integral_indicator hQo z]
  refine ⟨fun z hz => ⟨integrableOn_fiber_exp hQo hQb hV z, ?_⟩, ?_⟩
  · rw [setIntegral_fiber_eq_integral_indicator hQo z]
    exact marginal_exp_indicator_pos hQo hQb hV (exists_fiber_of_mem_fst_image hz)
  · rw [hfun]
    exact convexOn_neg_log_marginal_exp_of_bounded hPL hn hQo hQc hQb hV

/-- **Convex marginal on a bounded open convex polytope** (part of Lemma 3.7,
polytope form). The polytope `Q` is the
intersection of finitely many open half-spaces `{p | c j < ℓ j p}` for continuous linear
functionals `ℓ j` and constants `c j`, and it is bounded. -/
theorem convexity_exterior_polytope_halfspaces (hPL : External.PrekopaLeindler) {m n r : ℕ}
    (hn : 0 < n) (ℓ : Fin r → (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ)
    (c : Fin r → ℝ) (Q : Set (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)))
    (hQ : Q = {p | ∀ j, c j < ℓ j p}) (hQb : Bornology.IsBounded Q)
    (V : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n) → ℝ) (hV : ConvexOn ℝ Q V) :
    (∀ z ∈ Prod.fst '' Q,
      IntegrableOn (fun y => Real.exp (-V (z, y))) {y | (z, y) ∈ Q} ∧
        0 < ∫ y in {y | (z, y) ∈ Q}, Real.exp (-V (z, y))) ∧
    ConvexOn ℝ (Prod.fst '' Q)
      (fun z => -Real.log (∫ y in {y | (z, y) ∈ Q}, Real.exp (-V (z, y)))) := by
  have hset : Q = ⋂ j, {p | c j < ℓ j p} := by
    rw [hQ]
    ext p
    simp
  have hQo : IsOpen Q := by
    rw [hset]
    exact isOpen_iInter_of_finite fun j => isOpen_lt continuous_const (ℓ j).continuous
  have hQc : Convex ℝ Q := by
    rw [hset]
    exact convex_iInter fun j => convex_halfSpace_gt (ℓ j).toLinearMap.isLinear (c j)
  exact convexity_exterior_polytope_bounded hPL hn Q hQo hQc hQb V hV

end Riesz1

end
end
