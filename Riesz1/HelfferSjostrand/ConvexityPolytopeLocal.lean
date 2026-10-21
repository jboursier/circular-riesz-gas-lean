/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.ConvexityPolytope

/-!
# Convex marginal with locally bounded fibers (part of Lemma 3.7)

Let `Q ⊆ ℝ^m × ℝ^n` be open and convex, with `0 < n`, and let `V` be finite and convex on `Q`.
Suppose every point `z` of the projected interior has a neighborhood `U` such that
`Q ∩ (U × ℝⁿ)` is bounded (the fibers are locally bounded). Then the fiber integral
`J(z) = ∫_{Q_z} e^{-V(z,y)} dy` is integrable and positive on the projected interior, and
`z ↦ -log J(z)` is convex there.

The domain `Q` need not be bounded. The proof restricts `Q` to a bounded open convex piece
`Q ∩ (W × ℝⁿ)` with `W` a thickening of a given compact convex set. The fiber integrals agree
with those of `Q` over `W`, and the bounded theorem applies to the piece.

The translation hypothesis of Lemma 3.7 (a common translation variable making `V` and `Q`
invariant) is not needed, so the statement here is more general.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Topology Filter

namespace Riesz1

/-- Locally bounded fibers give a bounded open convex neighborhood `W` of a compact convex
set `K` in the projected interior, with `Q ∩ (W × ℝⁿ)` bounded. -/
theorem exists_thickening_bounded_fibers {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {n : ℕ}
    {Q : Set (E × EuclideanSpace ℝ (Fin n))} (hQo : IsOpen Q)
    (hloc : ∀ z ∈ Prod.fst '' Q, ∃ U ∈ 𝓝 z, Bornology.IsBounded (Q ∩ (U ×ˢ univ)))
    {K : Set E} (hKc : IsCompact K) (hKconv : Convex ℝ K) (hKP : K ⊆ Prod.fst '' Q) :
    ∃ W : Set E, IsOpen W ∧ Convex ℝ W ∧ K ⊆ W ∧ Bornology.IsBounded (Q ∩ (W ×ˢ univ)) := by
  have hPo : IsOpen (Prod.fst '' Q) := isOpenMap_fst Q hQo
  obtain ⟨δ, hδ, hsub⟩ := hKc.exists_cthickening_subset_open hPo hKP
  refine ⟨Metric.thickening δ K, Metric.isOpen_thickening, hKconv.thickening δ,
    Metric.self_subset_thickening hδ K, ?_⟩
  have hSsub : closure (Metric.thickening δ K) ⊆ Metric.cthickening δ K :=
    Metric.closure_thickening_subset_cthickening δ K
  have hScpt : IsCompact (closure (Metric.thickening δ K)) :=
    (hKc.cthickening).of_isClosed_subset isClosed_closure hSsub
  have hSP : ∀ z ∈ closure (Metric.thickening δ K), z ∈ Prod.fst '' Q :=
    fun z hz => hsub (hSsub hz)
  -- Cover the compact closure by finitely many neighborhoods with bounded fibers.
  choose U hUn hUb using fun z (hz : z ∈ closure (Metric.thickening δ K)) => hloc z (hSP z hz)
  obtain ⟨t, ht⟩ := hScpt.elim_nhds_subcover' U hUn
  refine ((Bornology.isBounded_biUnion_finset t).2 fun x _ => hUb x x.2).subset ?_
  rintro p ⟨hpQ, hpW⟩
  have hp1 : p.1 ∈ closure (Metric.thickening δ K) :=
    subset_closure (hpW.1 : p.1 ∈ Metric.thickening δ K)
  obtain ⟨x, hx, hpx⟩ := Set.mem_iUnion₂.1 (ht hp1)
  exact Set.mem_iUnion₂.2 ⟨x, hx, ⟨hpQ, hpx, mem_univ _⟩⟩

/-- A bounded open convex piece of `Q` that agrees with `Q` over a compact convex set `K` in the
projected interior. -/
theorem exists_bounded_piece {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {n : ℕ}
    {Q : Set (E × EuclideanSpace ℝ (Fin n))} (hQo : IsOpen Q) (hQc : Convex ℝ Q)
    (hloc : ∀ z ∈ Prod.fst '' Q, ∃ U ∈ 𝓝 z, Bornology.IsBounded (Q ∩ (U ×ˢ univ)))
    {K : Set E} (hKc : IsCompact K) (hKconv : Convex ℝ K) (hKP : K ⊆ Prod.fst '' Q) :
    ∃ Q' : Set (E × EuclideanSpace ℝ (Fin n)), IsOpen Q' ∧ Convex ℝ Q' ∧
      Bornology.IsBounded Q' ∧ Q' ⊆ Q ∧ K ⊆ Prod.fst '' Q' ∧
      ∀ z ∈ K, ∀ y, (z, y) ∈ Q' ↔ (z, y) ∈ Q := by
  obtain ⟨W, hWo, hWc, hKW, hWb⟩ := exists_thickening_bounded_fibers hQo hloc hKc hKconv hKP
  refine ⟨Q ∩ (W ×ˢ univ), hQo.inter (hWo.prod isOpen_univ), hQc.inter (hWc.prod convex_univ),
    hWb, Set.inter_subset_left, ?_, ?_⟩
  · intro z hz
    obtain ⟨y, hy⟩ := exists_fiber_of_mem_fst_image (hKP hz)
    exact ⟨(z, y), ⟨hy, hKW hz, mem_univ _⟩, rfl⟩
  · intro z hz y
    exact ⟨fun h => h.1, fun h => ⟨h, hKW hz, mem_univ _⟩⟩

/-- **Convex marginal with locally bounded fibers** (part of Lemma 3.7).
The domain `Q` is open and convex, and every point of its projected interior has a
neighborhood over which the fibers are jointly bounded. -/
theorem convexity_exterior_polytope_local (hPL : External.PrekopaLeindler) {m n : ℕ}
    (hn : 0 < n) (Q : Set (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)))
    (hQo : IsOpen Q) (hQc : Convex ℝ Q)
    (hloc : ∀ z ∈ Prod.fst '' Q, ∃ U ∈ 𝓝 z,
      Bornology.IsBounded (Q ∩ (U ×ˢ univ)))
    (V : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n) → ℝ) (hV : ConvexOn ℝ Q V) :
    (∀ z ∈ Prod.fst '' Q,
      IntegrableOn (fun y => Real.exp (-V (z, y))) {y | (z, y) ∈ Q} ∧
        0 < ∫ y in {y | (z, y) ∈ Q}, Real.exp (-V (z, y))) ∧
    ConvexOn ℝ (Prod.fst '' Q)
      (fun z => -Real.log (∫ y in {y | (z, y) ∈ Q}, Real.exp (-V (z, y)))) := by
  have hPconv : Convex ℝ (Prod.fst '' Q) := convex_fst_image_prod hQc
  -- Integrability and positivity at a point, from a piece with `K = {z}`.
  have hpoint : ∀ z ∈ Prod.fst '' Q,
      IntegrableOn (fun y => Real.exp (-V (z, y))) {y | (z, y) ∈ Q} ∧
        0 < ∫ y in {y | (z, y) ∈ Q}, Real.exp (-V (z, y)) := by
    intro z hz
    -- The piece built from `K = {z}` agrees with `Q` over `z`.
    obtain ⟨Q', hQ'o, hQ'c, hQ'b, hQ'sub, hKQ', hiff⟩ :=
      exists_bounded_piece hQo hQc hloc isCompact_singleton (convex_singleton z)
        (singleton_subset_iff.2 hz)
    have hV' : ConvexOn ℝ Q' V := hV.subset hQ'sub hQ'c
    have hbd := (convexity_exterior_polytope_bounded hPL hn Q' hQ'o hQ'c hQ'b V hV').1 z
      (hKQ' (mem_singleton z))
    have hset : {y | (z, y) ∈ Q'} = {y | (z, y) ∈ Q} :=
      Set.ext fun y => hiff z (mem_singleton z) y
    rw [hset] at hbd
    exact hbd
  refine ⟨hpoint, hPconv, fun x hx y hy a b ha hb hab => ?_⟩
  dsimp only
  -- The segment from `x` to `y` is compact and lies in the projected interior.
  have hKc : IsCompact (segment ℝ x y) := by
    rw [segment_eq_image']
    exact isCompact_Icc.image (by fun_prop)
  have hKP : segment ℝ x y ⊆ Prod.fst '' Q := hPconv.segment_subset hx hy
  obtain ⟨Q', hQ'o, hQ'c, hQ'b, hQ'sub, hKQ', hiff⟩ :=
    exists_bounded_piece hQo hQc hloc hKc (convex_segment x y) hKP
  have hV' : ConvexOn ℝ Q' V := hV.subset hQ'sub hQ'c
  have hcvx := (convexity_exterior_polytope_bounded hPL hn Q' hQ'o hQ'c hQ'b V hV').2
  have hfib : ∀ z ∈ segment ℝ x y, {w | (z, w) ∈ Q'} = {w | (z, w) ∈ Q} :=
    fun z hz => Set.ext fun w => hiff z hz w
  have key := hcvx.2 (hKQ' (left_mem_segment ℝ x y)) (hKQ' (right_mem_segment ℝ x y)) ha hb hab
  dsimp only at key
  rw [hfib x (left_mem_segment ℝ x y), hfib y (right_mem_segment ℝ x y),
    hfib (a • x + b • y) ⟨a, b, ha, hb, hab, rfl⟩] at key
  simpa only [smul_eq_mul] using key

end Riesz1

end
end
