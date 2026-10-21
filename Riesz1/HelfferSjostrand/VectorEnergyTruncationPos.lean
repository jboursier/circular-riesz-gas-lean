/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.VectorEnergyTruncationApprox
public import Riesz1.HelfferSjostrand.VectorEnergyTruncationGradient
public import Riesz1.ToMathlib.Hilbert.WeakSubsequence
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Positive and negative parts in the vector energy space `𝒱_{μ*}`

For `u ∈ 𝒱_{μ*}` we construct the positive part `u⁺` and the negative part `u⁻` as elements of
`𝒱_{μ*}` (Lemma 3.4). The argument has three steps.

1. For a jet `u` of anchored test tuples `v_k → u`, the truncations `truncTest (ε_k) v_k` are test
   jets, hence lie in `𝒱_{μ*}`, and their norms are bounded.
2. A bounded sequence in the Hilbert space `𝒱_{μ*}` has a weakly convergent subsequence
   (`exists_weak_subsequence_tendsto`). Its limit `x₀` lies in `𝒱_{μ*}` because the space is closed.
   The scalar values of `x₀` are `max (u_i) 0`, because the scalar values of the truncations
   converge strongly in `L²`, and the weak limit of a strongly convergent sequence is its limit.
3. The gradient of `x₀` is `1_{u_i > 0} ∇u_i`, by uniqueness of the weak gradient of a given
   value (`IsAnchoredH1.grad_ae_eq_of_value_ae_eq`) applied to the chain rule
   `IsAnchoredH1.comp_piecewise`.

The negative part is the positive part of `-u`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ContDiff InnerProductSpace

namespace Riesz1

variable {n : ℕ} {c : ℝ}

/-- The `i`-th scalar value of `Ψ ∈ 𝒱_{μ*}`, as a function on the anchored simplex. -/
abbrev vecValue (χ : HsPairPotentials n.succPNat c) [IsFiniteMeasure (anchoredMeasureE χ)]
    (i : Fin n) (Ψ : AnchoredVectorSobolev χ (anchoredMeasureE χ)) :
    AnchoredEuclidean n → ℝ :=
  (anchoredJetValue (anchoredMeasureE χ) i
    (Ψ : Lp (AnchoredJetPoint n) 2 (anchoredMeasureE χ)) : AnchoredEuclidean n → ℝ)

/-- The `i`-th weak gradient of `Ψ ∈ 𝒱_{μ*}`, as a function on the anchored simplex. -/
abbrev vecGrad (χ : HsPairPotentials n.succPNat c) [IsFiniteMeasure (anchoredMeasureE χ)]
    (i : Fin n) (Ψ : AnchoredVectorSobolev χ (anchoredMeasureE χ)) :
    AnchoredEuclidean n → AnchoredEuclidean n :=
  (anchoredJetGrad (anchoredMeasureE χ) i
    (Ψ : Lp (AnchoredJetPoint n) 2 (anchoredMeasureE χ)) : AnchoredEuclidean n → AnchoredEuclidean n)

/-- `up` is the positive part `u⁺` of `u` in `𝒱_{μ*}`: each scalar value of `up` is
`max (u_i) 0`, and each weak gradient of `up` is `1_{u_i > 0} ∇u_i`, almost everywhere. -/
def IsAnchoredPosPart (χ : HsPairPotentials n.succPNat c) [IsFiniteMeasure (anchoredMeasureE χ)]
    (u up : AnchoredVectorSobolev χ (anchoredMeasureE χ)) : Prop :=
  (∀ i : Fin n, vecValue χ i up =ᵐ[anchoredMeasureE χ] fun y => max (vecValue χ i u y) 0) ∧
    ∀ i : Fin n, vecGrad χ i up =ᵐ[anchoredMeasureE χ] fun y =>
      Set.indicator {y' : AnchoredEuclidean n | 0 < vecValue χ i u y'} (vecGrad χ i u) y

/-- `um` is the negative part `u⁻` of `u` in `𝒱_{μ*}`: each scalar value of `um` is
`max (-u_i) 0`, and each weak gradient of `um` is `-1_{u_i < 0} ∇u_i`, almost everywhere. -/
def IsAnchoredNegPart (χ : HsPairPotentials n.succPNat c) [IsFiniteMeasure (anchoredMeasureE χ)]
    (u um : AnchoredVectorSobolev χ (anchoredMeasureE χ)) : Prop :=
  (∀ i : Fin n, vecValue χ i um =ᵐ[anchoredMeasureE χ] fun y => max (-(vecValue χ i u y)) 0) ∧
    ∀ i : Fin n, vecGrad χ i um =ᵐ[anchoredMeasureE χ] fun y =>
      Set.indicator {y' : AnchoredEuclidean n | vecValue χ i u y' < 0}
        (fun y' => -(vecGrad χ i u y')) y

/-- The jet of a truncated test tuple lies in `𝒱_{μ*}`. -/
theorem anchoredVectorJet_truncTest_mem (χ : HsPairPotentials n.succPNat c)
    (μ : Measure (AnchoredEuclidean n)) [IsFiniteMeasure μ] {ε : ℝ} (hε : 0 < ε)
    (u : AnchoredVectorTest n) :
    anchoredVectorJet χ μ (truncTest hε u) ∈ anchoredVectorSobolevSubmodule χ μ :=
  Submodule.le_topologicalClosure _ ⟨truncTest hε u, rfl⟩

/-- The positive part exists in `𝒱_{μ*}` (Lemma 3.4, first
claim). -/
theorem exists_anchoredPosPart (χ : HsPairPotentials n.succPNat c) (hc : 0 < c)
    [IsFiniteMeasure (anchoredMeasureE χ)] (u : AnchoredVectorSobolev χ (anchoredMeasureE χ)) :
    ∃ up : AnchoredVectorSobolev χ (anchoredMeasureE χ), IsAnchoredPosPart χ u up := by
  have := isProbabilityMeasure_anchoredMeasureE χ hc
  set μ := anchoredMeasureE χ with hμ
  obtain ⟨v, hv⟩ := exists_seq_anchoredVectorJet χ μ u
  let ε : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hε : ∀ k, 0 < ε k := fun k => by positivity
  have hε0 : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  -- The truncated test jets, as elements of `𝒱_{μ*}`.
  let x : ℕ → AnchoredVectorSobolev χ μ := fun k =>
    ⟨anchoredVectorJet χ μ (truncTest (hε k) (v k)), anchoredVectorJet_truncTest_mem χ μ (hε k) (v k)⟩
  -- Their norms are bounded, because the jets of `v k` converge.
  obtain ⟨C, hC⟩ : ∃ C, ∀ k, ‖anchoredVectorJet χ μ (v k)‖ ≤ C := by
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp (Metric.isBounded_range_of_tendsto _ hv)
    exact ⟨C, fun k => hC _ ⟨k, rfl⟩⟩
  have hxC : ∀ k, ‖((x k : AnchoredVectorSobolev χ μ) : Lp (AnchoredJetPoint n) 2 μ)‖ ≤ C :=
    fun k => (norm_anchoredVectorJet_truncTest_le (hε k) χ μ (v k)).trans (hC k)
  -- A weakly convergent subsequence of the truncations.
  obtain ⟨φ, x₀, hφ, hweak⟩ := exists_weak_subsequence_tendsto hxC
  -- The weak limit lies in the closed subspace `𝒱_{μ*}`.
  have hx₀ : x₀ ∈ anchoredVectorSobolevSubmodule χ μ := by
    rw [← Submodule.orthogonal_orthogonal (anchoredVectorSobolevSubmodule χ μ), Submodule.mem_orthogonal]
    intro y hy
    have hzero : ∀ m, inner ℝ ((x (φ m) : AnchoredVectorSobolev χ μ) : Lp (AnchoredJetPoint n) 2 μ) y
        = 0 := fun m => Submodule.inner_right_of_mem_orthogonal (x (φ m)).2 hy
    have hlim := tendsto_nhds_unique (hweak y) (by simp only [hzero]; exact tendsto_const_nhds)
    rw [real_inner_comm]
    exact hlim
  let up : AnchoredVectorSobolev χ μ := ⟨x₀, hx₀⟩
  -- The scalar values of the weak limit are the positive parts of the scalar values of `u`. The
  -- adjoint of the value map identifies the weak limit of the values with their strong limit.
  have hval : ∀ i : Fin n, anchoredJetValue μ i x₀ =
      Lp.posPart (anchoredJetValue μ i (u : Lp (AnchoredJetPoint n) 2 μ)) := by
    intro i
    have hlimv := (tendsto_truncTest_value χ μ ε hε hε0 v hv i).comp hφ.tendsto_atTop
    have key : ∀ g : Lp ℝ 2 μ, inner ℝ (anchoredJetValue μ i x₀) g =
        inner ℝ (Lp.posPart (anchoredJetValue μ i (u : Lp (AnchoredJetPoint n) 2 μ))) g := by
      intro g
      have l₁ := (hweak (ContinuousLinearMap.adjoint (anchoredJetValue μ i) g)).congr
        (fun m => (ContinuousLinearMap.adjoint_inner_right (anchoredJetValue μ i) _ g))
      have l₂ : Tendsto (fun m => inner ℝ (anchoredJetValue μ i (x (φ m) :
          Lp (AnchoredJetPoint n) 2 μ)) g) atTop
          (𝓝 (inner ℝ (Lp.posPart (anchoredJetValue μ i (u : Lp (AnchoredJetPoint n) 2 μ))) g)) :=
        Tendsto.inner hlimv tendsto_const_nhds
      exact (ContinuousLinearMap.adjoint_inner_right (anchoredJetValue μ i) x₀ g).symm.trans
        (tendsto_nhds_unique l₁ l₂)
    have hd : inner ℝ (anchoredJetValue μ i x₀ - Lp.posPart (anchoredJetValue μ i
        (u : Lp (AnchoredJetPoint n) 2 μ))) (anchoredJetValue μ i x₀ - Lp.posPart
        (anchoredJetValue μ i (u : Lp (AnchoredJetPoint n) 2 μ))) = 0 := by
      rw [inner_sub_left]
      exact sub_eq_zero.mpr (key _)
    exact sub_eq_zero.mp (inner_self_eq_zero.mp hd)
  have hvalae : ∀ i : Fin n, vecValue χ i up =ᵐ[μ] fun y => max (vecValue χ i u y) 0 := by
    intro i
    show (anchoredJetValue μ i x₀ : AnchoredEuclidean n → ℝ) =ᵐ[μ] _
    rw [hval i]
    exact Lp.coeFn_posPart _
  refine ⟨up, hvalae, fun i => ?_⟩
  -- The weak gradient of `up` is determined by its value, which is the value of the chain rule.
  have hA : IsAnchoredH1 χ (vecValue χ i up) (vecGrad χ i up) :=
    isWeightedH1_anchoredVectorSobolev χ μ up i
  have hB : IsAnchoredH1 χ (vecValue χ i u) (vecGrad χ i u) :=
    isWeightedH1_anchoredVectorSobolev χ μ u i
  have hC := IsAnchoredH1.comp_piecewise χ hc hB lipschitzWith_max_zero (by simp)
    (Set.finite_singleton 0) contDiffOn_max_zero_compl
  have hD := IsAnchoredH1.grad_ae_eq_of_value_ae_eq χ hc hA hC (hvalae i)
  have hL := IsAnchoredH1.gradient_eq_zero_on_level χ hc hB 0
  filter_upwards [hD, hL] with y hy hy0
  rw [hy]
  by_cases hpos : 0 < vecValue χ i u y
  · rw [(hasDerivAt_max_zero_of_pos hpos).deriv, one_smul,
      Set.indicator_of_mem (show y ∈ {y' : AnchoredEuclidean n | 0 < vecValue χ i u y'} from hpos)]
  · by_cases hneg : vecValue χ i u y < 0
    · rw [(hasDerivAt_max_zero_of_neg hneg).deriv, zero_smul,
        Set.indicator_of_notMem (show y ∉ {y' : AnchoredEuclidean n | 0 < vecValue χ i u y'} from
          not_lt.mpr hneg.le)]
    · have h0 : vecValue χ i u y = 0 := le_antisymm (not_lt.mp hpos) (not_lt.mp hneg)
      rw [hy0 h0, smul_zero, Set.indicator_of_notMem (show y ∉
        {y' : AnchoredEuclidean n | 0 < vecValue χ i u y'} from by simp [h0])]

/-- The negative part exists in `𝒱_{μ*}`: it is the positive part of `-u`. -/
theorem exists_anchoredNegPart (χ : HsPairPotentials n.succPNat c) (hc : 0 < c)
    [IsFiniteMeasure (anchoredMeasureE χ)] (u : AnchoredVectorSobolev χ (anchoredMeasureE χ)) :
    ∃ um : AnchoredVectorSobolev χ (anchoredMeasureE χ), IsAnchoredNegPart χ u um := by
  obtain ⟨w, hw⟩ := exists_anchoredPosPart χ hc (-u)
  have hnegv : ∀ i : Fin n, vecValue χ i (-u) =ᵐ[anchoredMeasureE χ]
      fun y => -(vecValue χ i u y) := by
    intro i
    show (anchoredJetValue (anchoredMeasureE χ) i (-(u : Lp (AnchoredJetPoint n) 2 _)) :
      AnchoredEuclidean n → ℝ) =ᵐ[anchoredMeasureE χ] _
    rw [map_neg]
    exact Lp.coeFn_neg _
  have hnegg : ∀ i : Fin n, vecGrad χ i (-u) =ᵐ[anchoredMeasureE χ]
      fun y => -(vecGrad χ i u y) := by
    intro i
    show (anchoredJetGrad (anchoredMeasureE χ) i (-(u : Lp (AnchoredJetPoint n) 2 _)) :
      AnchoredEuclidean n → AnchoredEuclidean n) =ᵐ[anchoredMeasureE χ] _
    rw [map_neg]
    exact Lp.coeFn_neg _
  refine ⟨w, fun i => ?_, fun i => ?_⟩
  · filter_upwards [hw.1 i, hnegv i] with y h1 h2
    rw [h1, h2]
  · filter_upwards [hw.2 i, hnegv i, hnegg i] with y h1 h2 h3
    rw [h1]
    by_cases hp : vecValue χ i u y < 0
    · rw [Set.indicator_of_mem (show y ∈ {y' : AnchoredEuclidean n | 0 < vecValue χ i (-u) y'} from
        by simp [h2, hp]), h3,
        Set.indicator_of_mem (show y ∈ {y' : AnchoredEuclidean n | vecValue χ i u y' < 0} from hp)]
    · rw [Set.indicator_of_notMem (show y ∉ {y' : AnchoredEuclidean n | 0 < vecValue χ i (-u) y'}
        from by simp [h2, not_lt.mpr (not_lt.mp hp)]),
        Set.indicator_of_notMem (show y ∉ {y' : AnchoredEuclidean n | vecValue χ i u y' < 0} from hp)]

end Riesz1
