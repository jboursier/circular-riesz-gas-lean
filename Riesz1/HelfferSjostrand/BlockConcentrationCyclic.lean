/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.BlockConcentrationRetained
public import Riesz1.HelfferSjostrand.SettingRelabelGibbs

/-!
# Circular concentration for every nonempty cyclic interval

Lemma 3.9. A block of size `M` starting at cyclic label `k`
is obtained by relabeling and retaining the first `M` coordinates. The
marginal is the push-forward of the original Gibbs law. Its Sobolev space
is the periodic Hilbert completion, including singleton blocks.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace Riesz1

variable {N M : ℕ+} {c c₁ : ℝ}

/-- Retain the first `M` labels and enumerate the exterior in its original order. -/
def blockInitialEquiv (M N : ℕ+) (hm : (M : ℕ) ≤ N) :
    Fin (M : ℕ) ⊕ Fin ((N : ℕ) - M) ≃ Fin (N : ℕ) :=
  finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le hm))

theorem blockInitialEquiv_inl (hm : (M : ℕ) ≤ N) (i : Fin (M : ℕ)) :
    blockInitialEquiv M N hm (Sum.inl i) = Fin.castLE hm i := rfl

theorem blockInitialEquiv_strictMono (hm : (M : ℕ) ≤ N) :
    StrictMono fun i => blockInitialEquiv M N hm (Sum.inl i) := by
  intro i j hij
  exact hij

theorem blockInitialEquiv_zero (hm : (M : ℕ) ≤ N) :
    blockInitialEquiv M N hm (Sum.inl ⟨0, M.pos⟩) = ⟨0, N.pos⟩ := rfl

/-- Projection to the consecutive cyclic lifts starting at label `k`, read modulo
simultaneous integer translation. No ordering assumption on the original block is needed. -/
def blockCyclicProjection (M N : ℕ+) (hm : (M : ℕ) ≤ N) (k : ℕ)
    (X : Configuration N) : HsConfiguration M :=
  blockQuotientProjection (blockInitialEquiv M N hm)
    (blockInitialEquiv_strictMono hm) (blockInitialEquiv_zero hm)
    (hsRelabelConfiguration N k X)

theorem measurable_blockCyclicProjection (hm : (M : ℕ) ≤ N) (k : ℕ) :
    Measurable (blockCyclicProjection M N hm k) :=
  (measurable_blockQuotientProjection _ (blockInitialEquiv_strictMono hm)
    (blockInitialEquiv_zero hm)).comp (measurable_hsRelabelConfiguration N k)

/-- The projection is exactly the consecutive cyclic lift, modulo a common integer.
Taking a fundamental representative introduces no change on the retained quotient. -/
theorem blockCyclicProjection_val (hm : (M : ℕ) ≤ N) (k : ℕ) (X : Configuration N) :
    (blockCyclicProjection M N hm k X).val =
      (QuotientAddGroup.mk (WithLp.toLp 2 (fun i : Fin (M : ℕ) =>
        hsRelabel N k (WithLp.toLp 2 X.val) (Fin.castLE hm i))) : HsCylinder M) := by
  apply QuotientAddGroup.eq_iff_sub_mem.mpr
  apply (hsPeriodLattice_mem_iff _).mpr
  refine ⟨-⌊hsRelabel N k (WithLp.toLp 2 X.val) ⟨0, N.pos⟩⌋, fun i => ?_⟩
  change (hsRelabelConfiguration N k X).val
      (blockInitialEquiv M N hm (Sum.inl i)) -
    hsRelabel N k (WithLp.toLp 2 X.val) (Fin.castLE hm i) = _
  rw [blockInitialEquiv_inl]
  change (hsRepresentative _).val _ - _ = _
  rw [hsRepresentative_apply, Int.cast_neg]
  ring

/-- The actual cyclic-block marginal of the original law. -/
def blockCyclicMarginal (χ : HsPairPotentials N c) (hc : 0 < c)
    (hm : (M : ℕ) ≤ N) (k : ℕ) : ProbabilityMeasure (HsConfiguration M) :=
  (hsGibbsProbability χ hc).map (blockCyclicProjection M N hm k)

/-- The cyclic marginal equals the initial-block marginal for the reflected pair family. -/
theorem blockCyclicMarginal_eq (χ : HsPairPotentials N c) (hc : 0 < c)
    (hm : (M : ℕ) ≤ N) (k : ℕ) :
    (blockCyclicMarginal χ hc hm k : Measure (HsConfiguration M)) =
      (blockQuotientMarginal (hsRelabelPairs χ k) hc (blockInitialEquiv M N hm)
        (blockInitialEquiv_strictMono hm) (blockInitialEquiv_zero hm) : Measure (HsConfiguration M)) := by
  change (hsGibbsProbability χ hc : Measure _).map
    (blockQuotientProjection _ _ _ ∘ hsRelabelConfiguration N k) = _
  rw [← Measure.map_map (measurable_blockQuotientProjection _ _ _)
    (measurable_hsRelabelConfiguration N k), hsGibbsProbability_map_relabel]
  rfl

namespace Internal

/-- Completed-graph form of circular block concentration, with the original marginal.
The curvature is tested on the original chamber after the prescribed cyclic lift map. -/
theorem block_cyclic_concentration_graph (hBE : External.BakryEmery)
    (hPL : External.PrekopaLeindler) (χ : HsPairPotentials N c) (hc : 0 < c) (hc₁ : 0 < c₁)
    (hm : (M : ℕ) ≤ N) (k : ℕ)
    (hcurv : ∀ x ∈ hsChamber N, ∀ i j : Fin (M : ℕ), i < j → c₁ / 2 ≤
      deriv (deriv ((hsRelabelPairs χ k).potential (Fin.castLE hm i) (Fin.castLE hm j)))
        (hsRelabel N k x (Fin.castLE hm j) - hsRelabel N k x (Fin.castLE hm i)))
    {F : HsConfiguration M → ℝ} {G : HsConfiguration M → HsEuclidean M}
    (hFG : WeightedSobolev.IsGraphH1 (blockCyclicMarginal χ hc hm k : Measure _)
      (fun _ : hsSmoothCore M => True) (fun f => hsSmoothValue f.val) hsSmoothGradient F G)
    (hzero : ∀ᵐ x ∂(blockCyclicMarginal χ hc hm k : Measure _),
      ∑ i, G x i = 0)
    {L : ℝ} (hL : ∀ᵐ x ∂(blockCyclicMarginal χ hc hm k : Measure _), ‖G x‖ ≤ L)
    (t : ℝ) :
    let f := fun X => F (blockCyclicProjection M N hm k X)
    Integrable f (hsGibbsProbability χ hc : Measure _) ∧
      Integrable (fun X => Real.exp (t * f X)) (hsGibbsProbability χ hc : Measure _) ∧
      Real.log (∫ X, Real.exp (t * f X) ∂(hsGibbsProbability χ hc : Measure _)) ≤
        t * (∫ X, f X ∂(hsGibbsProbability χ hc : Measure _)) +
          t ^ 2 * L ^ 2 / (2 * c₁ * M) := by
  let e := blockInitialEquiv M N hm
  let μI : Measure (HsConfiguration M) := blockCyclicMarginal χ hc hm k
  have hcurv' : ∀ x ∈ hsChamber N, ∀ i j : Fin (M : ℕ), i < j → c₁ / 2 ≤
      deriv (deriv ((hsRelabelPairs χ k).potential (e (Sum.inl i)) (e (Sum.inl j))))
        (x (e (Sum.inl j)) - x (e (Sum.inl i))) := by
    intro y hy i j hij
    obtain ⟨x, hx, rfl⟩ := hsRelabel_exists_preimage N k hy
    exact hcurv x hx i j hij
  have hz : ∀ᵐ x ∂μI, inner ℝ (G x) (hsUnitVector M) = 0 := by
    filter_upwards [hzero] with x hx
    have he : inner ℝ (G x) (hsUnitVector M) =
        (Real.sqrt (M : ℕ))⁻¹ * ∑ i, G x i := by
      simp [hsUnitVector, hsRotationVector, PiLp.inner_apply, inner_smul_right, Finset.mul_sum]
    rw [he, hx, mul_zero]
  have he := blockCyclicMarginal_eq χ hc hm k
  have hg := hFG
  have hb := hL
  change ∀ᵐ x ∂(blockCyclicMarginal χ hc hm k : Measure _),
    inner ℝ (G x) (hsUnitVector M) = 0 at hz
  rw [he] at hg hz hb
  obtain ⟨hFi, hEi, hmgf⟩ := block_marginal_concentration hBE hPL (hsRelabelPairs χ k)
    hc hc₁ e (blockInitialEquiv_strictMono hm) (blockInitialEquiv_zero hm)
    hcurv' hg hz hb t
  rw [← he] at hFi hEi hmgf
  have hπ : MeasurePreserving (blockCyclicProjection M N hm k)
      (hsGibbsProbability χ hc : Measure _) μI :=
    ⟨measurable_blockCyclicProjection hm k, rfl⟩
  obtain ⟨hF, hv⟩ := integrable_integral_comp_measurePreserving hπ hFi
  obtain ⟨hE, heE⟩ := integrable_integral_comp_measurePreserving hπ hEi
  refine ⟨hF, hE, ?_⟩
  rw [heE, hv]
  exact hmgf

end Internal

/-- Circular block concentration (Lemma 3.9) for every nonempty cyclic interval.
The weak derivative sum and gradient bound are under the original Gibbs probability.
The gradient is expressed in the retained cyclic coordinates. The bound may be any
finite essential bound, hence in particular the essential supremum used in the paper.
Neither admissibility nor `N ≥ 2` is needed beyond the pair-potential hypotheses. -/
theorem block_concentration (hBE : External.BakryEmery)
    (hPL : External.PrekopaLeindler) (χ : HsPairPotentials N c) (hc : 0 < c) (hc₁ : 0 < c₁)
    (hm : (M : ℕ) ≤ N) (k : ℕ)
    (hcurv : ∀ x ∈ hsChamber N, ∀ i j : Fin (M : ℕ), i < j → c₁ / 2 ≤
      deriv (deriv ((hsRelabelPairs χ k).potential (Fin.castLE hm i) (Fin.castLE hm j)))
        (hsRelabel N k x (Fin.castLE hm j) - hsRelabel N k x (Fin.castLE hm i)))
    (g : HsSobolev (blockCyclicMarginal χ hc hm k : Measure _))
    (hzero : ∀ᵐ X ∂(hsGibbsProbability χ hc : Measure _),
      ∑ i, hsSobolevGradient _ g (blockCyclicProjection M N hm k X) i = 0)
    {L : ℝ} (hL : ∀ᵐ X ∂(hsGibbsProbability χ hc : Measure _),
      ‖hsSobolevGradient _ g (blockCyclicProjection M N hm k X)‖ ≤ L) (t : ℝ) :
    let F := fun X => hsSobolevValue _ g (blockCyclicProjection M N hm k X)
    Integrable F (hsGibbsProbability χ hc : Measure _) ∧
      Integrable (fun X => Real.exp (t * F X)) (hsGibbsProbability χ hc : Measure _) ∧
      Real.log (∫ X, Real.exp (t * F X) ∂(hsGibbsProbability χ hc : Measure _)) ≤
        t * (∫ X, F X ∂(hsGibbsProbability χ hc : Measure _)) +
          t ^ 2 * L ^ 2 / (2 * c₁ * M) := by
  let μI : Measure (HsConfiguration M) := blockCyclicMarginal χ hc hm k
  have hgraph := (hsSobolev_iff_graph μI (hsSobolevValue μI g) (hsSobolevGradient μI g)
    (Lp.memLp _) (Lp.memLp _)).mp (by
      simp only [Lp.toLp_coeFn]
      change WithLp.toLp 2 ((WithLp.ofLp g.val).1, (WithLp.ofLp g.val).2) ∈ hsSobolevSubmodule μI
      simpa only [Prod.mk.eta, WithLp.toLp_ofLp] using g.property)
  have hgrad : Measurable (hsSobolevGradient μI g) := (Lp.stronglyMeasurable _).measurable
  have hz : ∀ᵐ x ∂μI, ∑ i, hsSobolevGradient μI g x i = 0 := by
    apply (ae_map_iff (measurable_blockCyclicProjection hm k).aemeasurable
      (measurableSet_eq_fun (by fun_prop) measurable_const)).mpr hzero
  have hb : ∀ᵐ x ∂μI, ‖hsSobolevGradient μI g x‖ ≤ L := by
    exact (ae_map_iff (measurable_blockCyclicProjection hm k).aemeasurable
      (measurableSet_le hgrad.norm measurable_const)).mpr hL
  exact Internal.block_cyclic_concentration_graph hBE hPL χ hc hc₁ hm k hcurv hgraph hz hb t

end Riesz1

end
