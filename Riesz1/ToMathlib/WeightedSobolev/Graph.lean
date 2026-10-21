/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.WeightedSobolev.Completion
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Topology.Sequences

/-!
# Completion of a family of first order jets

The sequential encoding of `IsWeightedH1`, with the smooth lifts separated
from the measured space. This permits periodic lifts on a covering space.
The Euclidean encoding is exactly a special case. No gradient uniqueness
is asserted without a closability proof.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace Riesz1.WeightedSobolev

variable {Ω T E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E]

/-- The sequential closure of the value/derivative graph of a family of tests. -/
def IsGraphH1 (μ : Measure Ω) (P : T → Prop) (value : T → Ω → ℝ)
    (derivative : T → Ω → E) (F : Ω → ℝ) (G : Ω → E) : Prop :=
  MemLp F 2 μ ∧ MemLp G 2 μ ∧
    ∃ φ : ℕ → T, (∀ k, P (φ k)) ∧
      Tendsto (fun k => ∫⁻ x, ‖value (φ k) x - F x‖ₑ ^ 2 ∂μ) atTop (𝓝 0) ∧
      Tendsto (fun k => ∫⁻ x, ‖derivative (φ k) x - G x‖ₑ ^ 2 ∂μ) atTop (𝓝 0)

/-- The Euclidean Sobolev predicate is an instance of the jet encoding. -/
theorem isWeightedH1_iff_isGraphH1 [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] (μ : Measure E) (U : Set E)
    (F : E → ℝ) (G : E → E) :
    IsWeightedH1 μ U F G ↔ IsGraphH1 μ (SmoothNearClosure U) id gradient F G :=
  Iff.rfl

namespace IsGraphH1

variable {μ : Measure Ω} {P : T → Prop} {value : T → Ω → ℝ}
  {derivative : T → Ω → E} {F F' : Ω → ℝ} {G G' : Ω → E}

theorem memLp_fun (h : IsGraphH1 μ P value derivative F G) : MemLp F 2 μ := h.1

theorem memLp_grad (h : IsGraphH1 μ P value derivative F G) : MemLp G 2 μ := h.2.1

/-- Smooth finite-norm jets belong to their graph completion. -/
theorem of_test {t : T} (ht : P t) (hv : MemLp (value t) 2 μ)
    (hg : MemLp (derivative t) 2 μ) :
    IsGraphH1 μ P value derivative (value t) (derivative t) := by
  refine ⟨hv, hg, fun _ => t, fun _ => ht, ?_, ?_⟩ <;> simp

/-- Membership depends only on the two almost everywhere equivalence classes. -/
theorem congr (h : IsGraphH1 μ P value derivative F G)
    (hF : F =ᵐ[μ] F') (hG : G =ᵐ[μ] G') : IsGraphH1 μ P value derivative F' G' := by
  obtain ⟨hv, hg, φ, hφ, hφv, hφg⟩ := h
  refine ⟨hv.ae_eq hF, hg.ae_eq hG, φ, hφ, ?_, ?_⟩
  · convert hφv using 1
    ext k
    exact lintegral_congr_ae (hF.mono fun x hx => by dsimp; rw [hx])
  · convert hφg using 1
    ext k
    exact lintegral_congr_ae (hG.mono fun x hx => by dsimp; rw [hx])

end IsGraphH1

/-- Square-integrable value/derivative pairs with the sum-of-squares norm.
This is a Hilbert space when `E` is a real Hilbert space. -/
abbrev L2Jet (μ : Measure Ω) (E : Type*) [NormedAddCommGroup E] :=
  WithLp 2 (Lp ℝ 2 μ × Lp E 2 μ)

/-- The finite-norm jets of the prescribed tests, in the ambient normed space. -/
def jetCore (μ : Measure Ω) (P : T → Prop) (value : T → Ω → ℝ)
    (derivative : T → Ω → E) : Set (L2Jet μ E) :=
  {u | ∃ t, P t ∧ ∃ (hv : MemLp (value t) 2 μ) (hg : MemLp (derivative t) 2 μ),
    u = WithLp.toLp 2 (hv.toLp (value t), hg.toLp (derivative t))}

/-- The closed graph completion, with the induced sum-of-squares metric. -/
def JetCompletion (μ : Measure Ω) (P : T → Prop) (value : T → Ω → ℝ)
    (derivative : T → Ω → E) := closure (jetCore μ P value derivative)

instance [CompleteSpace E] (μ : Measure Ω) (P : T → Prop) (value : T → Ω → ℝ)
    (derivative : T → Ω → E) : CompleteSpace (JetCompletion μ P value derivative) :=
  isClosed_closure.completeSpace_coe

/-- The squared-integral convergence used in the encoding is exactly
convergence of the associated `L²` classes. -/
theorem tendsto_toLp_iff_lintegral_sq {μ : Measure Ω} (f : ℕ → Ω → E)
    (hf : ∀ k, MemLp (f k) 2 μ) (F : Ω → E) (hF : MemLp F 2 μ) :
    Tendsto (fun k => (hf k).toLp (f k)) atTop (𝓝 (hF.toLp F)) ↔
      Tendsto (fun k => ∫⁻ x, ‖f k x - F x‖ₑ ^ 2 ∂μ) atTop (𝓝 0) := by
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'']
  have hn (k : ℕ) : eLpNorm (f k - F) 2 μ =
      (∫⁻ x, ‖f k x - F x‖ₑ ^ 2 ∂μ) ^ (1 / (2 : ℝ)) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by simp)
      ((hf k).sub hF).aestronglyMeasurable]
    simp
  have hs (k : ℕ) : (eLpNorm (f k - F) 2 μ) ^ (2 : ℝ) =
      ∫⁻ x, ‖f k x - F x‖ₑ ^ 2 ∂μ := by
    simpa [ENNReal.rpow_natCast] using
      (eLpNorm_nnreal_pow_eq_lintegral (p := 2) (by norm_num)
        ((hf k).sub hF).aestronglyMeasurable)
  constructor
  · intro h
    have := (ENNReal.continuous_rpow_const (y := 2)).continuousAt.tendsto.comp h
    simpa only [Function.comp_def, hs,
      ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 2)] using this
  · intro h
    have := (ENNReal.continuous_rpow_const (y := 1 / 2)).continuousAt.tendsto.comp h
    simpa only [Function.comp_def, ← hn,
      ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] using this

/-- If all prescribed tests have finite norm, the sequential predicate is
exactly membership in the norm closure of their jets. -/
theorem isGraphH1_iff_mem_closure {μ : Measure Ω} {P : T → Prop}
    {value : T → Ω → ℝ} {derivative : T → Ω → E}
    (hvalue : ∀ t, P t → MemLp (value t) 2 μ)
    (hderivative : ∀ t, P t → MemLp (derivative t) 2 μ)
    (F : Ω → ℝ) (G : Ω → E) (hF : MemLp F 2 μ) (hG : MemLp G 2 μ) :
    IsGraphH1 μ P value derivative F G ↔
      WithLp.toLp 2 (hF.toLp F, hG.toLp G) ∈ closure (jetCore μ P value derivative) := by
  constructor
  · rintro ⟨_, _, φ, hφ, hv, hg⟩
    have hv' := (tendsto_toLp_iff_lintegral_sq (fun k => value (φ k))
      (fun k => hvalue _ (hφ k)) F hF).mpr hv
    have hg' := (tendsto_toLp_iff_lintegral_sq (fun k => derivative (φ k))
      (fun k => hderivative _ (hφ k)) G hG).mpr hg
    apply mem_closure_of_tendsto
      ((WithLp.prod_continuous_toLp 2 (Lp ℝ 2 μ) (Lp E 2 μ)).tendsto
        (hF.toLp F, hG.toLp G) |>.comp (hv'.prodMk_nhds hg'))
    exact Eventually.of_forall fun k => ⟨φ k, hφ k, hvalue _ (hφ k), hderivative _ (hφ k), rfl⟩
  · intro h
    obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.mp h
    choose φ hφ hv hg heq using hu
    refine ⟨hF, hG, φ, hφ, ?_, ?_⟩
    · apply (tendsto_toLp_iff_lintegral_sq _ hv F hF).mp
      have := (WithLp.continuous_fst 2 (Lp ℝ 2 μ) (Lp E 2 μ)).tendsto _ |>.comp hlim
      simpa only [Function.comp_def, heq, WithLp.fst, WithLp.ofLp_toLp] using this
    · apply (tendsto_toLp_iff_lintegral_sq _ hg G hG).mp
      have := (WithLp.continuous_snd 2 (Lp ℝ 2 μ) (Lp E 2 μ)).tendsto _ |>.comp hlim
      simpa only [Function.comp_def, heq, WithLp.snd, WithLp.ofLp_toLp] using this

end Riesz1.WeightedSobolev

end
