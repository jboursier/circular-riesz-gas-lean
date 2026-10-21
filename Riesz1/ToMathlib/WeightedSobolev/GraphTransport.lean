/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.WeightedSobolev.Graph

/-!
# Transport of completed jets

Precomposition by a measure-preserving map and bounded linear transformations of the
derivative commute with the completion of a prescribed family of first-order jets.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace Riesz1.WeightedSobolev

variable {Ω Ω' T E E' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {μ : Measure Ω} {ν : Measure Ω'} {P : T → Prop}
  {value : T → Ω → ℝ} {derivative : T → Ω → E} {F : Ω → ℝ} {G : Ω → E}

omit [NormedSpace ℝ E] in
/-- A measurable embedding transports a completed graph to prescribed jets on the
target, provided their pullbacks are the original jets. Representatives are extended
only as an auxiliary measure-theoretic construction. The target law is supported on
the image. -/
theorem IsGraphH1.exists_map (h : IsGraphH1 μ P value derivative F G)
    {r : Ω → Ω'} (hr : MeasurableEmbedding r)
    (value' : T → Ω' → ℝ) (derivative' : T → Ω' → E)
    (hv : ∀ t, P t → ∀ x, value' t (r x) = value t x)
    (hg : ∀ t, P t → ∀ x, derivative' t (r x) = derivative t x) :
    ∃ F' G', IsGraphH1 (μ.map r) P value' derivative' F' G' ∧
      (∀ x, F' (r x) = F x) ∧ (∀ x, G' (r x) = G x) := by
  obtain ⟨hF, hG, φ, hφ, hφv, hφg⟩ := h
  let F' := Function.extend r F (fun _ => 0)
  let G' := Function.extend r G (fun _ => 0)
  have heF (x : Ω) : F' (r x) = F x := hr.injective.extend_apply _ _ x
  have heG (x : Ω) : G' (r x) = G x := hr.injective.extend_apply _ _ x
  refine ⟨F', G', ⟨?_, ?_, φ, hφ, ?_, ?_⟩, heF, heG⟩
  · exact hr.memLp_map_measure_iff.mpr (by simpa only [Function.comp_def, heF] using hF)
  · exact hr.memLp_map_measure_iff.mpr (by simpa only [Function.comp_def, heG] using hG)
  · convert hφv using 1
    funext k
    rw [hr.lintegral_map]
    simp only [hv _ (hφ k), heF]
  · convert hφg using 1
    funext k
    rw [hr.lintegral_map]
    simp only [hg _ (hφ k), heG]

/-- A bounded linear transformation of the derivative passes to the completed graph. -/
theorem IsGraphH1.map_derivative (h : IsGraphH1 μ P value derivative F G)
    (hg : ∀ t, P t → MemLp (derivative t) 2 μ) (A : E →L[ℝ] E') :
    IsGraphH1 μ P value (fun t x => A (derivative t x)) F (fun x => A (G x)) := by
  obtain ⟨hF, hG, φ, hφ, hv, hd⟩ := h
  have hA := hG.continuousLinearMap_comp A
  have hφA (k : ℕ) := (hg _ (hφ k)).continuousLinearMap_comp A
  refine ⟨hF, hA, φ, hφ, hv, ?_⟩
  apply (tendsto_toLp_iff_lintegral_sq _ hφA _ hA).mp
  have ht := (A.compLpL 2 μ).continuous.tendsto _ |>.comp
    ((tendsto_toLp_iff_lintegral_sq _ (fun k => hg _ (hφ k)) G hG).mpr hd)
  have he {g : Ω → E} (hm : MemLp g 2 μ) :
      A.compLp (hm.toLp g) = (hm.continuousLinearMap_comp A).toLp (fun x => A (g x)) := by
    apply Lp.ext
    filter_upwards [A.coeFn_compLp (hm.toLp g), hm.coeFn_toLp,
      (hm.continuousLinearMap_comp A).coeFn_toLp] with x hx hy hz
    rw [hx, hy, hz]
  change Tendsto (fun k => A.compLp ((hg _ (hφ k)).toLp (derivative (φ k)))) atTop
    (𝓝 (A.compLp (hG.toLp G))) at ht
  simpa only [he] using ht

omit [NormedSpace ℝ E] in
/-- Measure-preserving precomposition transports the entire completed graph. -/
theorem IsGraphH1.comp_measurePreserving (h : IsGraphH1 μ P value derivative F G)
    (hv : ∀ t, P t → MemLp (value t) 2 μ)
    (hg : ∀ t, P t → MemLp (derivative t) 2 μ)
    {r : Ω' → Ω} (hr : MeasurePreserving r ν μ) :
    IsGraphH1 ν P (fun t x => value t (r x)) (fun t x => derivative t (r x))
      (fun x => F (r x)) (fun x => G (r x)) := by
  obtain ⟨hF, hG, φ, hφ, hφv, hφg⟩ := h
  refine ⟨hF.comp_measurePreserving hr, hG.comp_measurePreserving hr, φ, hφ, ?_, ?_⟩
  · convert hφv using 1
    funext k
    have hm : AEMeasurable (fun x => ‖value (φ k) x - F x‖ₑ ^ 2) (ν.map r) :=
      hr.map_eq.symm ▸ ((hv _ (hφ k)).sub hF).aestronglyMeasurable.enorm.pow_const 2
    exact (lintegral_map' hm hr.measurable.aemeasurable).symm.trans
      (congrArg (fun m => ∫⁻ x, ‖value (φ k) x - F x‖ₑ ^ 2 ∂m) hr.map_eq)
  · convert hφg using 1
    funext k
    have hm : AEMeasurable (fun x => ‖derivative (φ k) x - G x‖ₑ ^ 2) (ν.map r) :=
      hr.map_eq.symm ▸ ((hg _ (hφ k)).sub hG).aestronglyMeasurable.enorm.pow_const 2
    exact (lintegral_map' hm hr.measurable.aemeasurable).symm.trans
      (congrArg (fun m => ∫⁻ x, ‖derivative (φ k) x - G x‖ₑ ^ 2 ∂m) hr.map_eq)

end Riesz1.WeightedSobolev

end
