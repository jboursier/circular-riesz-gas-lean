/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.APrioriComparisonRepresentation
public import Riesz1.Variance.VarAlAssemblyCutoff
public import Riesz1.Variance.APrioriCutoffField

/-!
# The cutoff comparator in the anchored Sobolev space

The affine comparator is smooth on the bounded simplex. Multiplication
by the Sobolev cutoff gives its cutoff product and the weak product rule.
-/

@[expose] public section

noncomputable section

open MeasureTheory InnerProductSpace Filter Set Topology Classical
open scoped ContDiff

namespace Riesz1.APrioriComparison

variable {n : ℕ} {c : ℝ}

/-- Multiplying a smooth comparator by the cutoff in the completed graph. -/
theorem cutoff_comparator_h1 (χ : HsPairPotentials n.succPNat c) (hc : 0 < c)
    (hn : 1 ≤ n) (s K γ ε : ℝ) (hK : 1 ≤ K) (hε : 0 ≤ ε)
    (f : AnchoredEuclidean n → ℝ) (hf : ContDiff ℝ ∞ f) :
    let η := fun y : AnchoredEuclidean n => anchoredCutoff n.succPNat s K γ ε (WithLp.ofLp y)
    IsAnchoredH1 χ (fun y => η y * f y)
      (fun y => η y • gradient f y + f y • gradient η y) := by
  have := isProbabilityMeasure_anchoredMeasureE χ hc
  have hη := Internal.varAlAssembly_anchoredCutoff_h1 χ hc hn s K γ ε hK hε
  have hF : IsAnchoredH1 χ f (gradient f) :=
    WeightedSobolev.isWeightedH1_of_smoothNearClosure (isBounded_anchoredSimplex n)
      (ae_mem_anchoredSimplex χ) ⟨univ, isOpen_univ, subset_univ _, hf.contDiffOn⟩
  obtain ⟨B, hB⟩ := (isBounded_anchoredSimplex n).isCompact_closure.exists_bound_of_continuousOn
    hf.continuous.continuousOn
  apply hη.mul_of_bound (isBounded_anchoredSimplex n) (ae_mem_anchoredSimplex χ) hF
    zero_le_one (le_max_left 0 B)
  · exact Eventually.of_forall fun y => by
      rw [abs_of_nonneg (anchoredCutoff_nonneg s K γ ε _)]
      exact anchoredCutoff_le_one s K γ ε _
  · filter_upwards [ae_mem_anchoredSimplex χ] with y hy
    exact (show |f y| ≤ B from hB y (subset_closure hy)).trans (le_max_right 0 B)

/-- The comparator bound holds wherever the cutoff is nonzero. -/
theorem comparator_bound_on_cutoff_support (χ : HsPairPotentials n.succPNat c)
    {s K γ ε B : ℝ} (hK : 0 < K)
    (f : AnchoredEuclidean n → ℝ)
    (hb : ∀ X : Configuration n.succPNat, X ∈ goodEvent n.succPNat s K γ ε →
      |f (WithLp.toLp 2 (anchorMap n.succPNat X))| ≤ B) :
    ∀ᵐ y ∂anchoredMeasureE χ,
      anchoredCutoff n.succPNat s K γ ε (WithLp.ofLp y) ≠ 0 → |f y| ≤ B := by
  filter_upwards [ae_mem_anchoredSimplex χ] with y hy
  let X : Configuration n.succPNat := ⟨anchorVector (WithLp.ofLp y), varAl_anchorVector_mem hy⟩
  have hmap : anchorMap n.succPNat X = WithLp.ofLp y := by
    have h := anchorVector_anchorMap n X
    apply funext
    intro i
    have hi := congrFun h i.succ
    change anchorMap n.succPNat X i = WithLp.ofLp y i - 0 at hi
    simpa only [sub_zero] using hi
  have hη : goodCutoff n.succPNat s K γ ε X =
      anchoredCutoff n.succPNat s K γ ε (WithLp.ofLp y) := by
    rw [← anchoredCutoff_anchorMap, hmap]
  intro hz
  have hf := hb X (goodEvent_of_goodCutoff_ne_zero _ hK (by rwa [hη]))
  rw [hmap] at hf
  exact hf

/-- The cutoff product inherits the deterministic good-event bound. -/
theorem cutoff_comparator_bound (χ : HsPairPotentials n.succPNat c)
    {s K γ ε B : ℝ} (hB : 0 ≤ B) (f : AnchoredEuclidean n → ℝ)
    (hb : ∀ᵐ y ∂anchoredMeasureE χ,
      anchoredCutoff n.succPNat s K γ ε (WithLp.ofLp y) ≠ 0 → |f y| ≤ B) :
    ∀ᵐ y ∂anchoredMeasureE χ,
      |anchoredCutoff n.succPNat s K γ ε (WithLp.ofLp y) * f y| ≤ B := by
  filter_upwards [hb] with y hy
  by_cases hz : anchoredCutoff n.succPNat s K γ ε (WithLp.ofLp y) = 0
  · rw [hz, zero_mul, abs_zero]
    exact hB
  · rw [abs_mul, abs_of_nonneg (anchoredCutoff_nonneg s K γ ε _)]
    exact (mul_le_mul_of_nonneg_right (anchoredCutoff_le_one s K γ ε _) (abs_nonneg _)).trans
      (by simpa only [one_mul] using hy hz)

/-- The gradient in the Euclidean realization has exactly the differential
coordinates used by the cutoff field. -/
theorem comparatorCutoffField_eq_smul_gradient {n : ℕ} (s K γ ε : ℝ)
    (T : (Fin n → ℝ) → ℝ) (y : AnchoredEuclidean n)
    (hd : DifferentiableAt ℝ (anchoredCutoff n.succPNat s K γ ε) (WithLp.ofLp y)) :
    anchoredCutoffField n s K γ ε T y = T (WithLp.ofLp y) •
      gradient (fun z : AnchoredEuclidean n =>
        anchoredCutoff n.succPNat s K γ ε (WithLp.ofLp z)) y := by
  have hd' := hd.hasFDerivAt.comp y
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).hasFDerivAt
  apply PiLp.ext
  intro i
  have he := hd'.differentiableAt.hasGradientAt.fderiv_apply (y := EuclideanSpace.single i 1)
  rw [hd'.fderiv] at he
  have hinner : inner ℝ (gradient (fun z : AnchoredEuclidean n =>
      anchoredCutoff n.succPNat s K γ ε (WithLp.ofLp z)) y)
        (EuclideanSpace.single i 1) =
      gradient (fun z : AnchoredEuclidean n =>
        anchoredCutoff n.succPNat s K γ ε (WithLp.ofLp z)) y i := by
    rw [EuclideanSpace.inner_single_right]
    simp only [RCLike.conj_to_real, one_mul]
  change _ = inner ℝ (gradient (fun z : AnchoredEuclidean n =>
    anchoredCutoff n.succPNat s K γ ε (WithLp.ofLp z)) y) (EuclideanSpace.single i 1) at he
  rw [hinner] at he
  change T (WithLp.ofLp y) * _ = T (WithLp.ofLp y) * _
  congr 1

/-- Clamping the comparator preserves its cutoff-gradient field.
At a zero of the nonnegative cutoff its derivative vanishes. -/
theorem clamped_comparator_cutoff_field (χ : HsPairPotentials n.succPNat c)
    (hn : 1 ≤ n) (s K γ ε : ℝ) (hK : 1 ≤ K) (hγ : 0 ≤ γ)
    (hs : 0 ≤ s) (hε : 0 ≤ ε) {B : ℝ}
    (f : AnchoredEuclidean n → ℝ)
    (hb : ∀ᵐ y ∂anchoredMeasureE χ,
      anchoredCutoff n.succPNat s K γ ε (WithLp.ofLp y) ≠ 0 → |f y| ≤ B) :
    ∀ᵐ y ∂anchoredMeasureE χ,
      anchoredCutoffField n s K γ ε
        (fun z => max (-B) (min B (f (WithLp.toLp 2 z)))) y =
      f y • gradient (fun z : AnchoredEuclidean n =>
        anchoredCutoff n.succPNat s K γ ε (WithLp.ofLp z)) y := by
  filter_upwards [hb, anchoredMeasureE_cutoff_chain_ae hn χ s K γ ε hK hγ hs hε] with y hy hd
  have hηd := hd.1.comp (WithLp.ofLp y) (anchoredGapVector_hasFDerivAt n _).differentiableAt
  change DifferentiableAt ℝ (fun z => gapCutoff n.succPNat s K γ ε (anchoredGapVector n z)) _ at hηd
  rw [← anchoredCutoff_eq_comp_gapVector] at hηd
  rw [comparatorCutoffField_eq_smul_gradient _ _ _ _ _ y hηd]
  by_cases hz : anchoredCutoff n.succPNat s K γ ε (WithLp.ofLp y) = 0
  · have hzero : fderiv ℝ (fun z : AnchoredEuclidean n =>
        anchoredCutoff n.succPNat s K γ ε (WithLp.ofLp z)) y = 0 := by
      apply IsLocalMin.fderiv_eq_zero
      exact Eventually.of_forall fun z => by
        change anchoredCutoff n.succPNat s K γ ε (WithLp.ofLp y) ≤ _
        rw [hz]
        exact anchoredCutoff_nonneg s K γ ε _
    simp only [gradient, hzero, map_zero, smul_zero]
  · have hbound := abs_le.mp (hy hz)
    change max (-B) (min B (f y)) • _ = _
    rw [min_eq_right hbound.2, max_eq_right hbound.1]

end Riesz1.APrioriComparison

end
