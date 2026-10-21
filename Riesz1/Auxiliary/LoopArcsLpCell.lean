/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopArcsLpLarge
public import Riesz1.Auxiliary.LoopArcsLpAtom
public import Riesz1.Auxiliary.LoopArcsLpSmall
public import Riesz1.Auxiliary.LoopArcsDerivs

/-!
# Pointwise majorant of the arc-crossing representation

The arcs part of Lemma 5.8, the reduction of the cell estimate to lower integrals. The
representation `Λ(t)` is bounded in the lower-integral form by the iterated
integral of the enorms of its integrands, for every `t` and every configuration. This is the
first step of the `L^p` bound. The small, large and atomic parts are then estimated separately.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

attribute [local instance] Classical.propDecidable

namespace Riesz1

/-- **Pointwise majorant of `Λ`.** For `N ≥ 1`, every configuration `X` and every `t`:
`‖Λ(t)‖ₑ ≤ ∫⁻_{u∈(0,R]} ∫⁻_{v∈(0,R-u]} ‖g_N'''(u+v)‖ₑ ‖A‖ₑ ‖B‖ₑ + ‖g_N''(R)‖ₑ ∫⁻_{u∈(0,R]} ‖A'‖ₑ ‖B'‖ₑ`,
with the discrepancies replaced by counts minus arclengths, `R = N/2`. -/
theorem enorm_loopArcLambda_le (s : ℝ) (N : ℕ+) (X : Configuration N) (t : ℝ) :
    ‖loopArcLambda s N X t‖ₑ
      ≤ (∫⁻ u in Ioc (0 : ℝ) ((N : ℝ) / 2), ∫⁻ v in Ioc (0 : ℝ) ((N : ℝ) / 2 - u),
          ‖iteratedDeriv 3 (loopArcG s N) (u + v)‖ₑ * ‖loopCount (t - u) u X - u‖ₑ
            * ‖loopCount t v X - v‖ₑ)
        + ‖iteratedDeriv 2 (loopArcG s N) ((N : ℝ) / 2)‖ₑ
          * ∫⁻ u in Ioc (0 : ℝ) ((N : ℝ) / 2),
              ‖loopCount (t - u) u X - u‖ₑ * ‖loopCount t ((N : ℝ) / 2 - u) X - ((N : ℝ) / 2 - u)‖ₑ := by
  have hR0 : (0 : ℝ) ≤ (N : ℝ) / 2 := by positivity
  rw [loopArcLambda_eq_replace]
  refine (enorm_add_le _ _).trans (add_le_add ?_ ?_)
  · have hpt : ∀ u ∈ Ioc (0 : ℝ) ((N : ℝ) / 2),
        ‖∫ v in (0 : ℝ)..((N : ℝ) / 2 - u),
          -iteratedDeriv 3 (loopArcG s N) (u + v) * (loopCount (t - u) u X - u)
            * (loopCount t v X - v)‖ₑ
          ≤ ∫⁻ v in Ioc (0 : ℝ) ((N : ℝ) / 2 - u),
              ‖iteratedDeriv 3 (loopArcG s N) (u + v)‖ₑ * ‖loopCount (t - u) u X - u‖ₑ
                * ‖loopCount t v X - v‖ₑ := by
      intro u hu
      rw [intervalIntegral.integral_of_le (by linarith [hu.2])]
      refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq (lintegral_congr fun v => ?_))
      simp only [enorm_mul, enorm_neg]
    rw [intervalIntegral.integral_of_le hR0]
    exact (enorm_integral_le_lintegral_enorm _).trans (setLIntegral_mono' measurableSet_Ioc hpt)
  · rw [enorm_mul, intervalIntegral.integral_of_le hR0]
    refine mul_le_mul' le_rfl ?_
    exact (enorm_integral_le_lintegral_enorm _).trans (le_of_eq (lintegral_congr fun u => by
      simp only [enorm_mul]))

/-- The base region of the cell estimate: `0 < u ≤ R` and `0 < v ≤ R - u`. -/
def baseRegion (R : ℝ) : Set (ℝ × ℝ × ℝ) :=
  {θ | (0 < θ.2.1 ∧ θ.2.1 ≤ R) ∧ (0 < θ.2.2 ∧ θ.2.2 ≤ R - θ.2.1)}

/-- The full integrand of the cell estimate on the base region, before the split at `u + v = 1`. -/
def fullIntegrand (s : ℝ) (N : ℕ+) (θ : ℝ × ℝ × ℝ) (X : Configuration N) : ℝ≥0∞ :=
  (baseRegion ((N : ℝ) / 2)).indicator (fun θ =>
    ‖iteratedDeriv 3 (loopArcG s N) (θ.2.1 + θ.2.2)‖ₑ
      * ‖loopCount (θ.1 - θ.2.1) θ.2.1 X - θ.2.1‖ₑ
      * ‖loopCount θ.1 θ.2.2 X - θ.2.2‖ₑ) θ

theorem measurableSet_baseRegion (R : ℝ) : MeasurableSet (baseRegion R) := by
  have hu : Measurable (fun θ : ℝ × ℝ × ℝ => θ.2.1) := measurable_fst.comp measurable_snd
  have hv : Measurable (fun θ : ℝ × ℝ × ℝ => θ.2.2) := measurable_snd.comp measurable_snd
  have hP1 : MeasurableSet {θ : ℝ × ℝ × ℝ | 0 < θ.2.1} := measurableSet_lt measurable_const hu
  have hP2 : MeasurableSet {θ : ℝ × ℝ × ℝ | θ.2.1 ≤ R} := measurableSet_le hu measurable_const
  have hP3 : MeasurableSet {θ : ℝ × ℝ × ℝ | 0 < θ.2.2} := measurableSet_lt measurable_const hv
  have hP4 : MeasurableSet {θ : ℝ × ℝ × ℝ | θ.2.2 ≤ R - θ.2.1} :=
    measurableSet_le hv (measurable_const.sub hu)
  have key : baseRegion R = ({θ : ℝ × ℝ × ℝ | 0 < θ.2.1} ∩ {θ | θ.2.1 ≤ R})
      ∩ ({θ : ℝ × ℝ × ℝ | 0 < θ.2.2} ∩ {θ | θ.2.2 ≤ R - θ.2.1}) := by
    ext θ
    simp only [baseRegion, mem_ofPred_eq, Set.mem_inter_iff, and_assoc]
  rw [key]
  exact (hP1.inter hP2).inter (hP3.inter hP4)

/-- Measurability of the full integrand in the parameter and the configuration. -/
theorem measurable_fullIntegrand (s : ℝ) (N : ℕ+) :
    Measurable (fun q : (ℝ × ℝ × ℝ) × Configuration N => fullIntegrand s N q.1 q.2) := by
  have hu : Measurable (fun q : (ℝ × ℝ × ℝ) × Configuration N => q.1.2.1) := by fun_prop
  have hv : Measurable (fun q : (ℝ × ℝ × ℝ) × Configuration N => q.1.2.2) := by fun_prop
  have ht : Measurable (fun q : (ℝ × ℝ × ℝ) × Configuration N => q.1.1) := by fun_prop
  have hX : Measurable (fun q : (ℝ × ℝ × ℝ) × Configuration N => q.2) := by fun_prop
  have hg3 := measurable_iteratedDeriv_three s N
  have hc1 := measurable_loopCount_of (N := N) (c := fun q => q.2)
    (a := fun q : (ℝ × ℝ × ℝ) × Configuration N => q.1.1 - q.1.2.1)
    (r := fun q : (ℝ × ℝ × ℝ) × Configuration N => q.1.2.1) (ht.sub hu) hu hX
  have hc2 := measurable_loopCount_of (N := N) (c := fun q => q.2)
    (a := fun q : (ℝ × ℝ × ℝ) × Configuration N => q.1.1)
    (r := fun q : (ℝ × ℝ × ℝ) × Configuration N => q.1.2.2) ht hv hX
  have hG : Measurable (fun q : (ℝ × ℝ × ℝ) × Configuration N =>
      ‖iteratedDeriv 3 (loopArcG s N) (q.1.2.1 + q.1.2.2)‖ₑ
        * ‖loopCount (q.1.1 - q.1.2.1) q.1.2.1 q.2 - q.1.2.1‖ₑ
        * ‖loopCount q.1.1 q.1.2.2 q.2 - q.1.2.2‖ₑ) :=
    ((hg3.comp (hu.add hv)).enorm.mul ((hc1.sub hu).enorm)).mul ((hc2.sub hv).enorm)
  have hS : MeasurableSet {q : (ℝ × ℝ × ℝ) × Configuration N | q.1 ∈ baseRegion ((N : ℝ) / 2)} :=
    (measurableSet_baseRegion _).preimage measurable_fst
  have heq : (fun q : (ℝ × ℝ × ℝ) × Configuration N => fullIntegrand s N q.1 q.2)
      = {q : (ℝ × ℝ × ℝ) × Configuration N | q.1 ∈ baseRegion ((N : ℝ) / 2)}.indicator
          (fun q => ‖iteratedDeriv 3 (loopArcG s N) (q.1.2.1 + q.1.2.2)‖ₑ
            * ‖loopCount (q.1.1 - q.1.2.1) q.1.2.1 q.2 - q.1.2.1‖ₑ
            * ‖loopCount q.1.1 q.1.2.2 q.2 - q.1.2.2‖ₑ) := by
    funext q
    by_cases h : q.1 ∈ baseRegion ((N : ℝ) / 2)
    · rw [fullIntegrand, Set.indicator_of_mem h,
        Set.indicator_of_mem (show q ∈ {q : (ℝ × ℝ × ℝ) × Configuration N | q.1 ∈ baseRegion ((N : ℝ) / 2)} from h)]
    · rw [fullIntegrand, Set.indicator_of_notMem h,
        Set.indicator_of_notMem (show q ∉ {q : (ℝ × ℝ × ℝ) × Configuration N | q.1 ∈ baseRegion ((N : ℝ) / 2)} from h)]
  rw [heq]
  exact hG.indicator hS

/-- The large-region set is the base region intersected with `u + v ≥ 1`. -/
theorem largeRegion_eq_base_inter (R : ℝ) :
    largeRegion R = baseRegion R ∩ {θ : ℝ × ℝ × ℝ | 1 ≤ θ.2.1 + θ.2.2} := by
  ext θ
  simp only [largeRegion, baseRegion, mem_ofPred_eq, Set.mem_inter_iff, and_assoc]

/-- The large-region integrand is the full integrand restricted to `u + v ≥ 1`. -/
theorem largeIntegrand_eq_indicator (s : ℝ) (N : ℕ+) (θ : ℝ × ℝ × ℝ) (X : Configuration N) :
    largeIntegrand s N θ X
      = {θ : ℝ × ℝ × ℝ | 1 ≤ θ.2.1 + θ.2.2}.indicator (fun θ => fullIntegrand s N θ X) θ := by
  unfold largeIntegrand fullIntegrand
  rw [largeRegion_eq_base_inter]
  by_cases h1 : 1 ≤ θ.2.1 + θ.2.2
  · by_cases h2 : θ ∈ baseRegion ((N : ℝ) / 2)
    · rw [Set.indicator_of_mem (show θ ∈ baseRegion ((N : ℝ) / 2) ∩ {θ : ℝ × ℝ × ℝ | 1 ≤ θ.2.1 + θ.2.2} from ⟨h2, h1⟩),
        Set.indicator_of_mem (show θ ∈ {θ : ℝ × ℝ × ℝ | 1 ≤ θ.2.1 + θ.2.2} from h1),
        Set.indicator_of_mem h2]
    · rw [Set.indicator_of_notMem (show θ ∉ baseRegion ((N : ℝ) / 2) ∩ {θ : ℝ × ℝ × ℝ | 1 ≤ θ.2.1 + θ.2.2} from fun h => h2 h.1),
        Set.indicator_of_mem (show θ ∈ {θ : ℝ × ℝ × ℝ | 1 ≤ θ.2.1 + θ.2.2} from h1),
        Set.indicator_of_notMem h2]
  · rw [Set.indicator_of_notMem (show θ ∉ baseRegion ((N : ℝ) / 2) ∩ {θ : ℝ × ℝ × ℝ | 1 ≤ θ.2.1 + θ.2.2} from fun h => h1 h.2),
      Set.indicator_of_notMem (show θ ∉ {θ : ℝ × ℝ × ℝ | 1 ≤ θ.2.1 + θ.2.2} from h1)]

/-- **Restriction in the second variable.** A lower integral over `μ ⊗ ν` of an integrand that
vanishes off `S` in its second variable equals the one over `μ ⊗ (ν|_S)`. -/
theorem lintegral_prod_restrict_of_zero {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν] (S : Set β) (_hS : MeasurableSet S)
    (f : α × β → ℝ≥0∞) (hf : Measurable f) (h0 : ∀ a b, b ∉ S → f (a, b) = 0) :
    ∫⁻ z, f z ∂(μ.prod (ν.restrict S)) = ∫⁻ z, f z ∂(μ.prod ν) := by
  rw [lintegral_prod _ hf.aemeasurable, lintegral_prod _ hf.aemeasurable]
  refine lintegral_congr fun a => ?_
  have hsupp : Function.support (fun b => f (a, b)) ⊆ S := by
    intro b hb
    by_contra hbS
    exact hb (h0 a b hbS)
  rw [← setLIntegral_eq_of_support_subset (μ := ν) hsupp]

/-- The iterated integral over the base region equals the integral of the full integrand. -/
theorem lintegral_Ioc_iterated_eq_full (s : ℝ) (N : ℕ+) (X : Configuration N) (t : ℝ) :
    ∫⁻ u in Ioc (0 : ℝ) ((N : ℝ) / 2), ∫⁻ v in Ioc (0 : ℝ) ((N : ℝ) / 2 - u),
        ‖iteratedDeriv 3 (loopArcG s N) (u + v)‖ₑ * ‖loopCount (t - u) u X - u‖ₑ
          * ‖loopCount t v X - v‖ₑ
      = ∫⁻ u, ∫⁻ v, fullIntegrand s N (t, u, v) X := by
  rw [← lintegral_indicator measurableSet_Ioc]
  refine lintegral_congr fun u => ?_
  by_cases hu : u ∈ Ioc (0 : ℝ) ((N : ℝ) / 2)
  · rw [Set.indicator_of_mem hu, ← lintegral_indicator measurableSet_Ioc]
    refine lintegral_congr fun v => ?_
    unfold fullIntegrand
    by_cases hv : v ∈ Ioc (0 : ℝ) ((N : ℝ) / 2 - u)
    · rw [Set.indicator_of_mem hv, Set.indicator_of_mem
        (show (t, u, v) ∈ baseRegion ((N : ℝ) / 2) from ⟨⟨hu.1, hu.2⟩, ⟨hv.1, hv.2⟩⟩)]
    · rw [Set.indicator_of_notMem hv, Set.indicator_of_notMem
        (show (t, u, v) ∉ baseRegion ((N : ℝ) / 2) from fun h => hv ⟨h.2.1, h.2.2⟩)]
  · rw [Set.indicator_of_notMem hu]
    refine Eq.symm ((lintegral_congr fun v => ?_).trans lintegral_zero)
    unfold fullIntegrand
    rw [Set.indicator_of_notMem (show (t, u, v) ∉ baseRegion ((N : ℝ) / 2) from
      fun h => hu ⟨h.1.1, h.1.2⟩)]

/-- The full integrand is measurable in the parameter, for a fixed configuration. -/
theorem measurable_fullIntegrand_fixed (s : ℝ) (N : ℕ+) (X : Configuration N) :
    Measurable (fun θ : ℝ × ℝ × ℝ => fullIntegrand s N θ X) := by
  have hu : Measurable (fun θ : ℝ × ℝ × ℝ => θ.2.1) := measurable_fst.comp measurable_snd
  have hv : Measurable (fun θ : ℝ × ℝ × ℝ => θ.2.2) := measurable_snd.comp measurable_snd
  have ht : Measurable (fun θ : ℝ × ℝ × ℝ => θ.1) := measurable_fst
  have hg3 := measurable_iteratedDeriv_three s N
  have hc1 := measurable_loopCount_of (N := N) (c := fun _ => X)
    (a := fun θ : ℝ × ℝ × ℝ => θ.1 - θ.2.1) (r := fun θ : ℝ × ℝ × ℝ => θ.2.1)
    (ht.sub hu) hu measurable_const
  have hc2 := measurable_loopCount_of (N := N) (c := fun _ => X)
    (a := fun θ : ℝ × ℝ × ℝ => θ.1) (r := fun θ : ℝ × ℝ × ℝ => θ.2.2) ht hv measurable_const
  have hG : Measurable (fun θ : ℝ × ℝ × ℝ =>
      ‖iteratedDeriv 3 (loopArcG s N) (θ.2.1 + θ.2.2)‖ₑ
        * ‖loopCount (θ.1 - θ.2.1) θ.2.1 X - θ.2.1‖ₑ
        * ‖loopCount θ.1 θ.2.2 X - θ.2.2‖ₑ) :=
    ((hg3.comp (hu.add hv)).enorm.mul ((hc1.sub hu).enorm)).mul ((hc2.sub hv).enorm)
  unfold fullIntegrand
  exact hG.indicator (measurableSet_baseRegion _)

/-- The atomic integrand is measurable in the parameter, for a fixed configuration. -/
theorem measurable_atomIntegrand_fixed (s : ℝ) (N : ℕ+) (X : Configuration N) :
    Measurable (fun θ : ℝ × ℝ => atomIntegrand s N θ X) := by
  have hu : Measurable (fun θ : ℝ × ℝ => θ.2) := measurable_snd
  have ht : Measurable (fun θ : ℝ × ℝ => θ.1) := measurable_fst
  have hR : Measurable (fun θ : ℝ × ℝ => (N : ℝ) / 2 - θ.2) := measurable_const.sub hu
  have hc1 := measurable_loopCount_of (N := N) (c := fun _ => X)
    (a := fun θ : ℝ × ℝ => θ.1 - θ.2) (r := fun θ : ℝ × ℝ => θ.2) (ht.sub hu) hu measurable_const
  have hc2 := measurable_loopCount_of (N := N) (c := fun _ => X)
    (a := fun θ : ℝ × ℝ => θ.1) (r := fun θ : ℝ × ℝ => (N : ℝ) / 2 - θ.2) ht hR measurable_const
  have hF : Measurable (fun θ : ℝ × ℝ =>
      ‖loopCount (θ.1 - θ.2) θ.2 X - θ.2‖ₑ
        * ‖loopCount θ.1 ((N : ℝ) / 2 - θ.2) X - ((N : ℝ) / 2 - θ.2)‖ₑ) :=
    ((hc1.sub hu).enorm).mul ((hc2.sub hR).enorm)
  unfold atomIntegrand
  have hS : MeasurableSet {θ : ℝ × ℝ | θ.2 ∈ Ioc (0 : ℝ) ((N : ℝ) / 2)} :=
    measurableSet_Ioc.preimage hu
  have heq : (fun θ : ℝ × ℝ => (Ioc (0 : ℝ) ((N : ℝ) / 2)).indicator (fun u =>
      ‖loopCount (θ.1 - u) u X - u‖ₑ * ‖loopCount θ.1 ((N : ℝ) / 2 - u) X - ((N : ℝ) / 2 - u)‖ₑ) θ.2)
      = {θ : ℝ × ℝ | θ.2 ∈ Ioc (0 : ℝ) ((N : ℝ) / 2)}.indicator (fun θ : ℝ × ℝ =>
          ‖loopCount (θ.1 - θ.2) θ.2 X - θ.2‖ₑ
            * ‖loopCount θ.1 ((N : ℝ) / 2 - θ.2) X - ((N : ℝ) / 2 - θ.2)‖ₑ) := by
    funext θ
    by_cases h : θ.2 ∈ Ioc (0 : ℝ) ((N : ℝ) / 2)
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (show θ ∈ {θ : ℝ × ℝ | θ.2 ∈ Ioc (0 : ℝ) ((N : ℝ) / 2)} from h)]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (show θ ∉ {θ : ℝ × ℝ | θ.2 ∈ Ioc (0 : ℝ) ((N : ℝ) / 2)} from h)]
  rw [heq]
  exact hF.indicator hS

/-- The product-form pointwise majorant of `‖Λ(t)‖ₑ`. -/
theorem enorm_loopArcLambda_le_full (s : ℝ) (N : ℕ+) (X : Configuration N) (t : ℝ) :
    ‖loopArcLambda s N X t‖ₑ
      ≤ (∫⁻ θ' : ℝ × ℝ, fullIntegrand s N (t, θ') X ∂(volume.prod volume))
        + ‖iteratedDeriv 2 (loopArcG s N) ((N : ℝ) / 2)‖ₑ
          * ∫⁻ u, atomIntegrand s N (t, u) X ∂volume := by
  refine (enorm_loopArcLambda_le s N X t).trans (add_le_add ?_ ?_)
  · have hmeas : Measurable (fun θ' : ℝ × ℝ => fullIntegrand s N (t, θ') X) :=
      (measurable_fullIntegrand_fixed s N X).comp (measurable_const.prodMk measurable_id)
    rw [lintegral_prod _ hmeas.aemeasurable]
    exact (lintegral_Ioc_iterated_eq_full s N X t).le
  · refine mul_le_mul' le_rfl (le_of_eq ?_)
    exact (lintegral_indicator measurableSet_Ioc _).symm

/-- **Cell bound in product form.** The `t`-integral over the cell of the enorm of `Λ` is bounded
by the full integrand over the cell and the atomic integrand. -/
theorem lintegral_cell_enorm_le (s : ℝ) (N : ℕ+) (X : Configuration N) (m : ℝ) :
    ∫⁻ t in Ioc m (m + 1), ‖loopArcLambda s N X t‖ₑ
      ≤ (∫⁻ θ, fullIntegrand s N θ X ∂((volume.restrict (Ioc m (m + 1))).prod (volume.prod volume)))
        + ‖iteratedDeriv 2 (loopArcG s N) ((N : ℝ) / 2)‖ₑ
          * ∫⁻ θ, atomIntegrand s N θ X ∂((volume.restrict (Ioc m (m + 1))).prod volume) := by
  have hF1 : Measurable (fun t : ℝ => ∫⁻ θ' : ℝ × ℝ, fullIntegrand s N (t, θ') X
      ∂(volume.prod volume)) :=
    Measurable.lintegral_prod_right' (f := fun z : ℝ × (ℝ × ℝ) => fullIntegrand s N z X)
      (measurable_fullIntegrand_fixed s N X)
  have hF2 : Measurable (fun t : ℝ => ∫⁻ u, atomIntegrand s N (t, u) X ∂volume) :=
    Measurable.lintegral_prod_right' (f := fun z : ℝ × ℝ => atomIntegrand s N z X)
      (measurable_atomIntegrand_fixed s N X)
  have e1 : ∫⁻ θ, fullIntegrand s N θ X ∂((volume.restrict (Ioc m (m + 1))).prod (volume.prod volume))
      = ∫⁻ t in Ioc m (m + 1), ∫⁻ θ' : ℝ × ℝ, fullIntegrand s N (t, θ') X ∂(volume.prod volume) :=
    lintegral_prod _ (measurable_fullIntegrand_fixed s N X).aemeasurable
  have e2 : ∫⁻ θ, atomIntegrand s N θ X ∂((volume.restrict (Ioc m (m + 1))).prod volume)
      = ∫⁻ t in Ioc m (m + 1), ∫⁻ u, atomIntegrand s N (t, u) X ∂volume :=
    lintegral_prod _ (measurable_atomIntegrand_fixed s N X).aemeasurable
  rw [e1, e2]
  calc ∫⁻ t in Ioc m (m + 1), ‖loopArcLambda s N X t‖ₑ
      ≤ ∫⁻ t in Ioc m (m + 1), ((∫⁻ θ' : ℝ × ℝ, fullIntegrand s N (t, θ') X ∂(volume.prod volume))
          + ‖iteratedDeriv 2 (loopArcG s N) ((N : ℝ) / 2)‖ₑ
            * ∫⁻ u, atomIntegrand s N (t, u) X ∂volume) :=
        lintegral_mono fun t => enorm_loopArcLambda_le_full s N X t
    _ = (∫⁻ t in Ioc m (m + 1), ∫⁻ θ' : ℝ × ℝ, fullIntegrand s N (t, θ') X ∂(volume.prod volume))
          + ∫⁻ t in Ioc m (m + 1), ‖iteratedDeriv 2 (loopArcG s N) ((N : ℝ) / 2)‖ₑ
            * ∫⁻ u, atomIntegrand s N (t, u) X ∂volume :=
        lintegral_add_left hF1 _
    _ = (∫⁻ t in Ioc m (m + 1), ∫⁻ θ' : ℝ × ℝ, fullIntegrand s N (t, θ') X ∂(volume.prod volume))
          + ‖iteratedDeriv 2 (loopArcG s N) ((N : ℝ) / 2)‖ₑ
            * ∫⁻ t in Ioc m (m + 1), ∫⁻ u, atomIntegrand s N (t, u) X ∂volume := by
        rw [lintegral_const_mul _ hF2]

/-- The enorm of a centred count is at most the count plus the arclength. -/
theorem enorm_sub_le_ofReal_add {x u : ℝ} (hx : 0 ≤ x) (hu : 0 ≤ u) :
    ‖x - u‖ₑ ≤ ENNReal.ofReal (x + u) := by
  rw [Real.enorm_eq_ofReal_abs]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [abs_sub_le_iff]
  constructor <;> linarith

/-- The large-region integrand vanishes off the product of the two arclength intervals. -/
theorem largeIntegrand_eq_zero_of_not_mem_prod (s : ℝ) (N : ℕ+) (X : Configuration N) (a : ℝ)
    (b : ℝ × ℝ) (hb : b ∉ Ioc (0 : ℝ) ((N : ℝ) / 2) ×ˢ Ioc (0 : ℝ) ((N : ℝ) / 2)) :
    largeIntegrand s N (a, b) X = 0 := by
  unfold largeIntegrand
  rw [Set.indicator_of_notMem]
  intro h
  apply hb
  obtain ⟨⟨hu0, huR⟩, ⟨hv0, hvR⟩, _⟩ := h
  exact ⟨⟨hu0, huR⟩, ⟨hv0, by linarith⟩⟩

/-- **Large part of the cell bound.** The large part of the full integrand over the cell has the
integral of the large-region integrand over the large-region measure. -/
theorem lintegral_large_part_eq (s : ℝ) (N : ℕ+) (X : Configuration N) (m : ℝ) :
    ∫⁻ θ, {θ : ℝ × ℝ × ℝ | 1 ≤ θ.2.1 + θ.2.2}.indicator (fun θ => fullIntegrand s N θ X) θ
        ∂((volume.restrict (Ioc m (m + 1))).prod (volume.prod volume))
      = ∫⁻ θ, largeIntegrand s N θ X ∂(loopArcLargeMeasure m N) := by
  unfold loopArcLargeMeasure
  rw [Measure.prod_restrict (Ioc (0 : ℝ) ((N : ℝ) / 2)) (Ioc (0 : ℝ) ((N : ℝ) / 2))]
  rw [lintegral_prod_restrict_of_zero (volume.restrict (Ioc m (m + 1))) (volume.prod volume)
    (Ioc (0 : ℝ) ((N : ℝ) / 2) ×ˢ Ioc (0 : ℝ) ((N : ℝ) / 2)) (measurableSet_Ioc.prod measurableSet_Ioc)
    (fun θ => largeIntegrand s N θ X) ?_ ?_]
  · refine lintegral_congr fun θ => ?_
    exact (largeIntegrand_eq_indicator s N θ X).symm
  · have hind : Measurable (fun θ : ℝ × ℝ × ℝ => largeIntegrand s N θ X) := by
      simp_rw [largeIntegrand_eq_indicator s N _ X]
      exact (measurable_fullIntegrand_fixed s N X).indicator
        (measurableSet_le measurable_const (measurable_fst.comp measurable_snd |>.add
          (measurable_snd.comp measurable_snd)))
    exact hind
  · intro a b hb
    exact largeIntegrand_eq_zero_of_not_mem_prod s N X a b hb

/-- The atomic integrand over the cell measure equals its integral over the atom measure. -/
theorem atom_part_eq (s : ℝ) (N : ℕ+) (X : Configuration N) (m : ℝ) :
    ∫⁻ θ, atomIntegrand s N θ X ∂((volume.restrict (Ioc m (m + 1))).prod volume)
      = ∫⁻ θ, atomIntegrand s N θ X ∂(atomMeasure m N) := by
  unfold atomMeasure
  refine (lintegral_prod_restrict_of_zero (volume.restrict (Ioc m (m + 1))) volume
    (Ioc (0 : ℝ) ((N : ℝ) / 2)) measurableSet_Ioc (fun z => atomIntegrand s N z X)
    (measurable_atomIntegrand_fixed s N X) ?_).symm
  intro a b hb
  unfold atomIntegrand
  rw [Set.indicator_of_notMem hb]

/-- **Small part of the cell bound.** For `C ≥ 0` and the bound `|g_N'''| ≤ C r^{-s-3}`, the
small part of the full integrand over the cell is bounded by the small-region constant times
the counts and the rooted energies of the window. -/
theorem finS_part_le {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {C : ℝ} (hC : 0 ≤ C)
    (hgC : ∀ (N : ℕ+) (r : ℝ), 0 < r → r ≤ (N : ℝ) / 2 →
      ‖iteratedDeriv 3 (loopArcG s N) r‖ₑ ≤ ENNReal.ofReal (C * r ^ (-s - 3))) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (N : ℕ+), 2 ≤ (N : ℕ) → ∀ (X : Configuration N) (m : ℝ),
      ∫⁻ θ, {θ : ℝ × ℝ × ℝ | θ.2.1 + θ.2.2 < 1}.indicator (fun θ => fullIntegrand s N θ X) θ
          ∂((volume.restrict (Ioc m (m + 1))).prod (volume.prod volume))
        ≤ ENNReal.ofReal K * (1 + ENNReal.ofReal (loopCount m 2 X)
            + ENNReal.ofReal (loopCount (m - 1) 2 X)
            + ∑ i : Fin (N : ℕ), (if loopPos X i ∈ microArc N (m - 1) 2 then
                ENNReal.ofReal (rootedEnergy s X i) else 0)) := by
  obtain ⟨K, hK0, hK⟩ := smallRegion_lintegral_le (s := s) (C := C) hs0 hs1 hC
  refine ⟨K, hK0, fun N hN X m => ?_⟩
  have hR1 : (1 : ℝ) ≤ (N : ℝ) / 2 := by
    have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  set FS : ℝ × ℝ × ℝ → ℝ≥0∞ := fun θ => {θ : ℝ × ℝ × ℝ | θ.2.1 + θ.2.2 < 1}.indicator
    (fun θ => fullIntegrand s N θ X) θ with hFS
  have hu : Measurable (fun θ : ℝ × ℝ × ℝ => θ.2.1) := measurable_fst.comp measurable_snd
  have hv : Measurable (fun θ : ℝ × ℝ × ℝ => θ.2.2) := measurable_snd.comp measurable_snd
  have hSset : MeasurableSet {θ : ℝ × ℝ × ℝ | θ.2.1 + θ.2.2 < 1} :=
    measurableSet_lt (hu.add hv) measurable_const
  have hmeasFS : Measurable FS := (measurable_fullIntegrand_fixed s N X).indicator hSset
  -- the zero set of the integrand off the quadrant
  have hu0 : ∀ (t u v : ℝ), u ∉ Ioi (0 : ℝ) → FS (t, u, v) = 0 := by
    intro t u v h
    simp only [hFS]
    by_cases hS : u + v < 1
    · rw [Set.indicator_of_mem (show (t, u, v) ∈ {θ : ℝ × ℝ × ℝ | θ.2.1 + θ.2.2 < 1} from hS)]
      unfold fullIntegrand
      rw [Set.indicator_of_notMem (show (t, u, v) ∉ baseRegion ((N : ℝ) / 2) from
        fun hb => h hb.1.1)]
    · rw [Set.indicator_of_notMem (show (t, u, v) ∉ {θ : ℝ × ℝ × ℝ | θ.2.1 + θ.2.2 < 1} from hS)]
  have hv0 : ∀ (t u v : ℝ), v ∉ Ioi (0 : ℝ) → FS (t, u, v) = 0 := by
    intro t u v h
    simp only [hFS]
    by_cases hS : u + v < 1
    · rw [Set.indicator_of_mem (show (t, u, v) ∈ {θ : ℝ × ℝ × ℝ | θ.2.1 + θ.2.2 < 1} from hS)]
      unfold fullIntegrand
      rw [Set.indicator_of_notMem (show (t, u, v) ∉ baseRegion ((N : ℝ) / 2) from
        fun hb => h hb.2.1)]
    · rw [Set.indicator_of_notMem (show (t, u, v) ∉ {θ : ℝ × ℝ × ℝ | θ.2.1 + θ.2.2 < 1} from hS)]
  -- the pointwise comparison on the quadrant
  have hle : ∀ (t u v : ℝ), 0 < u → 0 < v →
      FS (t, u, v) ≤ (if u + v < 1 then ENNReal.ofReal (C * (u + v) ^ (-s - 3))
          * ENNReal.ofReal (loopCount (t - u) u X + u)
          * ENNReal.ofReal (loopCount t v X + v) else 0) := by
    intro t u v hu0' hv0'
    by_cases hS : u + v < 1
    · rw [ite_eq_left hS]
      simp only [hFS]
      rw [Set.indicator_of_mem (show (t, u, v) ∈ {θ : ℝ × ℝ × ℝ | θ.2.1 + θ.2.2 < 1} from hS)]
      unfold fullIntegrand
      have hbase : (t, u, v) ∈ baseRegion ((N : ℝ) / 2) :=
        ⟨⟨hu0', by linarith⟩, ⟨hv0', by linarith⟩⟩
      rw [Set.indicator_of_mem hbase]
      exact mul_le_mul' (mul_le_mul' (hgC N (u + v) (by linarith) (by linarith))
        (enorm_sub_le_ofReal_add (loopCount_nonneg _ _ _) hu0'.le))
        (enorm_sub_le_ofReal_add (loopCount_nonneg _ _ _) hv0'.le)
    · rw [ite_eq_right hS]
      simp only [hFS]
      rw [Set.indicator_of_notMem (show (t, u, v) ∉ {θ : ℝ × ℝ × ℝ | θ.2.1 + θ.2.2 < 1} from hS)]
  -- the iterated form and the quadrant bound
  have hpt : ∀ t : ℝ, ∫⁻ u, ∫⁻ v, FS (t, u, v)
      ≤ ∫⁻ u in Ioi (0 : ℝ), ∫⁻ v in Ioi (0 : ℝ), (if u + v < 1 then ENNReal.ofReal (C * (u + v) ^ (-s - 3))
          * ENNReal.ofReal (loopCount (t - u) u X + u)
          * ENNReal.ofReal (loopCount t v X + v) else 0) := by
    intro t
    have hinner : ∀ u : ℝ, ∫⁻ v, FS (t, u, v) = ∫⁻ v in Ioi (0 : ℝ), FS (t, u, v) := by
      intro u
      by_cases hu' : u ∈ Ioi (0 : ℝ)
      · refine (setLIntegral_eq_of_support_subset ?_).symm
        intro v hv
        by_contra hvI
        exact hv (hv0 t u v hvI)
      · simp only [hu0 t u _ hu', lintegral_zero]
    have hsupp : Function.support (fun u : ℝ => ∫⁻ v in Ioi (0 : ℝ), FS (t, u, v)) ⊆ Ioi (0 : ℝ) := by
      intro u hu'
      by_contra huI
      apply hu'
      simp only [hu0 t u _ huI, lintegral_zero]
    rw [lintegral_congr hinner, ← setLIntegral_eq_of_support_subset hsupp]
    exact setLIntegral_mono' measurableSet_Ioi fun u hu' =>
      setLIntegral_mono' measurableSet_Ioi fun v hv => hle t u v hu' hv
  rw [lintegral_prod _ hmeasFS.aemeasurable]
  refine (lintegral_mono fun t => ?_).trans (hK N hN X m)
  have hmeasT : Measurable (fun θ' : ℝ × ℝ => FS (t, θ')) :=
    hmeasFS.comp (measurable_const.prodMk measurable_id)
  rw [lintegral_prod (fun θ' : ℝ × ℝ => FS (t, θ')) hmeasT.aemeasurable]
  exact hpt t

/-- **Cell bound.** There is a constant `K ≥ 0` such that for every `N ≥ 2`, configuration `X`
and cell origin `m`, the `t`-integral over `(m, m+1]` of `‖Λ‖ₑ` is bounded by the small
counts and energies, the large-region integral and the atomic integral. -/
theorem lintegral_cell_three_bound {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (N : ℕ+), 2 ≤ (N : ℕ) → ∀ (X : Configuration N) (m : ℝ),
      ∫⁻ t in Ioc m (m + 1), ‖loopArcLambda s N X t‖ₑ
        ≤ ENNReal.ofReal K * (1 + ENNReal.ofReal (loopCount m 2 X)
            + ENNReal.ofReal (loopCount (m - 1) 2 X)
            + ∑ i : Fin (N : ℕ), (if loopPos X i ∈ microArc N (m - 1) 2 then
                ENNReal.ofReal (rootedEnergy s X i) else 0))
          + ∫⁻ θ, largeIntegrand s N θ X ∂(loopArcLargeMeasure m N)
          + ‖iteratedDeriv 2 (loopArcG s N) ((N : ℝ) / 2)‖ₑ
            * ∫⁻ θ, atomIntegrand s N θ X ∂(atomMeasure m N) := by
  obtain ⟨C, hC, hgC'⟩ := norm_iteratedDeriv_loopArcG_le s hs0 hs1
  have hgC : ∀ (N : ℕ+) (r : ℝ), 0 < r → r ≤ (N : ℝ) / 2 →
      ‖iteratedDeriv 3 (loopArcG s N) r‖ₑ ≤ ENNReal.ofReal (C * r ^ (-s - 3)) := by
    intro N r hr hrN
    have h := hgC' N 3 (by norm_num) (by norm_num) r hr hrN
    rw [Real.enorm_eq_ofReal_abs]
    refine ENNReal.ofReal_le_ofReal (h.trans (le_of_eq ?_))
    norm_num
  obtain ⟨K, hK0, hK⟩ := finS_part_le hs0 hs1 hC.le hgC
  refine ⟨K, hK0, fun N hN X m => ?_⟩
  have hu : Measurable (fun θ : ℝ × ℝ × ℝ => θ.2.1) := measurable_fst.comp measurable_snd
  have hv : Measurable (fun θ : ℝ × ℝ × ℝ => θ.2.2) := measurable_snd.comp measurable_snd
  have hSset : MeasurableSet {θ : ℝ × ℝ × ℝ | θ.2.1 + θ.2.2 < 1} :=
    measurableSet_lt (hu.add hv) measurable_const
  have hLset : MeasurableSet {θ : ℝ × ℝ × ℝ | 1 ≤ θ.2.1 + θ.2.2} :=
    measurableSet_le measurable_const (hu.add hv)
  set FS : ℝ × ℝ × ℝ → ℝ≥0∞ := fun θ => {θ : ℝ × ℝ × ℝ | θ.2.1 + θ.2.2 < 1}.indicator
    (fun θ => fullIntegrand s N θ X) θ with hFS
  set FL : ℝ × ℝ × ℝ → ℝ≥0∞ := fun θ => {θ : ℝ × ℝ × ℝ | 1 ≤ θ.2.1 + θ.2.2}.indicator
    (fun θ => fullIntegrand s N θ X) θ with hFL
  have hmFS : Measurable FS := (measurable_fullIntegrand_fixed s N X).indicator hSset
  have hsplit : ∀ θ : ℝ × ℝ × ℝ, fullIntegrand s N θ X = FS θ + FL θ := by
    intro θ
    by_cases h : θ.2.1 + θ.2.2 < 1
    · have h' : ¬ 1 ≤ θ.2.1 + θ.2.2 := not_le.mpr h
      simp only [hFS, hFL]
      rw [Set.indicator_of_mem (show θ ∈ {θ : ℝ × ℝ × ℝ | θ.2.1 + θ.2.2 < 1} from h),
        Set.indicator_of_notMem (show θ ∉ {θ : ℝ × ℝ × ℝ | 1 ≤ θ.2.1 + θ.2.2} from h'), add_zero]
    · have h' : 1 ≤ θ.2.1 + θ.2.2 := not_lt.mp h
      simp only [hFS, hFL]
      rw [Set.indicator_of_notMem (show θ ∉ {θ : ℝ × ℝ × ℝ | θ.2.1 + θ.2.2 < 1} from h),
        Set.indicator_of_mem (show θ ∈ {θ : ℝ × ℝ × ℝ | 1 ≤ θ.2.1 + θ.2.2} from h'), zero_add]
  have hmFL : Measurable FL := (measurable_fullIntegrand_fixed s N X).indicator hLset
  have hsplitInt : ∫⁻ θ, fullIntegrand s N θ X ∂((volume.restrict (Ioc m (m + 1))).prod (volume.prod volume))
      = (∫⁻ θ, FS θ ∂((volume.restrict (Ioc m (m + 1))).prod (volume.prod volume)))
        + ∫⁻ θ, FL θ ∂((volume.restrict (Ioc m (m + 1))).prod (volume.prod volume)) := by
    rw [← lintegral_add_left hmFS]
    exact lintegral_congr fun θ => hsplit θ
  calc ∫⁻ t in Ioc m (m + 1), ‖loopArcLambda s N X t‖ₑ
      ≤ (∫⁻ θ, fullIntegrand s N θ X ∂((volume.restrict (Ioc m (m + 1))).prod (volume.prod volume)))
        + ‖iteratedDeriv 2 (loopArcG s N) ((N : ℝ) / 2)‖ₑ
          * ∫⁻ θ, atomIntegrand s N θ X ∂((volume.restrict (Ioc m (m + 1))).prod volume) :=
        lintegral_cell_enorm_le s N X m
    _ = (∫⁻ θ, FS θ ∂((volume.restrict (Ioc m (m + 1))).prod (volume.prod volume)))
        + (∫⁻ θ, largeIntegrand s N θ X ∂(loopArcLargeMeasure m N))
        + ‖iteratedDeriv 2 (loopArcG s N) ((N : ℝ) / 2)‖ₑ
          * ∫⁻ θ, atomIntegrand s N θ X ∂(atomMeasure m N) := by
        rw [hsplitInt, lintegral_large_part_eq s N X m, atom_part_eq s N X m]
    _ ≤ ENNReal.ofReal K * (1 + ENNReal.ofReal (loopCount m 2 X)
            + ENNReal.ofReal (loopCount (m - 1) 2 X)
            + ∑ i : Fin (N : ℕ), (if loopPos X i ∈ microArc N (m - 1) 2 then
                ENNReal.ofReal (rootedEnergy s X i) else 0))
          + ∫⁻ θ, largeIntegrand s N θ X ∂(loopArcLargeMeasure m N)
          + ‖iteratedDeriv 2 (loopArcG s N) ((N : ℝ) / 2)‖ₑ
            * ∫⁻ θ, atomIntegrand s N θ X ∂(atomMeasure m N) := by
        gcongr
        exact hK N hN X m

end Riesz1

end
end
