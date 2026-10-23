/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopArcsLpCell
public import Riesz1.Auxiliary.LoopArcsLpBundle
public import Riesz1.Auxiliary.LoopArcsLpAtom
public import Riesz1.Auxiliary.LoopArcsLpMoments
public import Riesz1.Auxiliary.LoopArcsIdentity

/-!
# The `L^p` bound of the arc-crossing representation over a cell

The arcs part of Lemma B.2, the `L^p` clause: for `N ≥ 2`, every integer `0 ≤ m < N`,
`‖∫_m^{m+1} |Λ(t)| dt‖_p ≤ C_{β,s,p}`, with `C` chosen before `N`, `m` and the smooth periodic
test function. The cell bound `lintegral_cell_three_bound` splits the `t`-integral into the small
counts and energies, the large region and the atom. Each part has a bounded `p`-th moment by the
rigidity bundle or by the explicit estimates of the large and atomic regions.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Finset
open scoped ENNReal

attribute [local instance] Classical.propDecidable

namespace Riesz1

/-- **Power of a sum of four terms.** For `p ≥ 1`, `(a+b+c+d)^p ≤ 4^{p-1} (a^p+b^p+c^p+d^p)`. -/
theorem ennreal_add_four_rpow_le {p : ℝ} (hp : 1 ≤ p) (a b c d : ℝ≥0∞) :
    (a + b + c + d) ^ p ≤ 4 ^ (p - 1) * (a ^ p + b ^ p + c ^ p + d ^ p) := by
  have h1 := ENNReal.rpow_add_le_mul_rpow_add_rpow (a + b) (c + d) hp
  have h2 := ENNReal.rpow_add_le_mul_rpow_add_rpow a b hp
  have h3 := ENNReal.rpow_add_le_mul_rpow_add_rpow c d hp
  have h4 : (2 : ℝ≥0∞) ^ (p - 1) * (2 : ℝ≥0∞) ^ (p - 1) = 4 ^ (p - 1) := by
    rw [← ENNReal.mul_rpow_of_nonneg _ _ (by linarith : (0 : ℝ) ≤ p - 1)]
    norm_num
  calc (a + b + c + d) ^ p = ((a + b) + (c + d)) ^ p := by ring_nf
    _ ≤ 2 ^ (p - 1) * ((a + b) ^ p + (c + d) ^ p) := h1
    _ ≤ 2 ^ (p - 1) * (2 ^ (p - 1) * (a ^ p + b ^ p) + 2 ^ (p - 1) * (c ^ p + d ^ p)) := by
        gcongr
    _ = 4 ^ (p - 1) * (a ^ p + b ^ p + c ^ p + d ^ p) := by
        rw [← h4]
        ring

/-- **Power of a sum of three terms.** -/
theorem ennreal_add_three_rpow_le {p : ℝ} (hp : 1 ≤ p) (a b c : ℝ≥0∞) :
    (a + b + c) ^ p ≤ 4 ^ (p - 1) * (a ^ p + b ^ p + c ^ p) := by
  have hp0 : 0 < p := by linarith
  have := ennreal_add_four_rpow_le hp a b c 0
  rw [add_zero, ENNReal.zero_rpow_of_pos hp0, add_zero] at this
  exact this

/-- The window sum of rooted energies, as a real function of the configuration. -/
def windowSum (s : ℝ) (N : ℕ+) (a r : ℝ) (X : Configuration N) : ℝ :=
  ∑ i : Fin (N : ℕ), if loopPos X i ∈ microArc N a r then rootedEnergy s X i else 0

/-- The window sum is measurable in the configuration. -/
theorem measurable_windowSum (s : ℝ) (N : ℕ+) (a r : ℝ) :
    Measurable (windowSum s N a r) := by
  unfold windowSum
  refine Finset.measurable_sum _ (fun i _ => ?_)
  exact Measurable.ite (measurable_loopPos i (measurableSet_microArc N a r))
    (measurable_rootedEnergy s i) measurable_const

/-- The window sum of the ENNReal-valued rooted energies is the `ofReal` of the real window sum. -/
theorem ofReal_windowSum (s : ℝ) (N : ℕ+) (a r : ℝ) (X : Configuration N) :
    (∑ i : Fin (N : ℕ), (if loopPos X i ∈ microArc N a r then
        ENNReal.ofReal (rootedEnergy s X i) else 0))
      = ENNReal.ofReal (windowSum s N a r X) := by
  unfold windowSum
  rw [ENNReal.ofReal_sum_of_nonneg]
  · refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs
    · rfl
    · simp
  · intro i _
    split_ifs
    · unfold rootedEnergy
      exact Finset.sum_nonneg fun j _ => Real.rpow_nonneg dist_nonneg _
    · exact le_rfl

/-- The rooted energy is nonnegative. -/
theorem rootedEnergy_nonneg' (s : ℝ) {N : ℕ+} (X : Configuration N) (i : Fin (N : ℕ)) :
    0 ≤ rootedEnergy s X i := by
  unfold rootedEnergy
  exact Finset.sum_nonneg fun j _ => Real.rpow_nonneg dist_nonneg _

/-- The window sum is nonnegative. -/
theorem windowSum_nonneg (s : ℝ) (N : ℕ+) (a r : ℝ) (X : Configuration N) :
    0 ≤ windowSum s N a r X := by
  unfold windowSum
  refine Finset.sum_nonneg fun i _ => ?_
  split_ifs
  · exact rootedEnergy_nonneg' s X i
  · exact le_rfl

/-- The large-region integrand, with the configuration first, is measurable. -/
theorem measurable_largeIntegrand_swap (s : ℝ) (N : ℕ+) :
    Measurable (fun z : Configuration N × (ℝ × ℝ × ℝ) => largeIntegrand s N z.2 z.1) := by
  have hu : Measurable (fun z : Configuration N × (ℝ × ℝ × ℝ) => z.2.2.1) := by fun_prop
  have hv : Measurable (fun z : Configuration N × (ℝ × ℝ × ℝ) => z.2.2.2) := by fun_prop
  have ht : Measurable (fun z : Configuration N × (ℝ × ℝ × ℝ) => z.2.1) := by fun_prop
  have hX : Measurable (fun z : Configuration N × (ℝ × ℝ × ℝ) => z.1) := by fun_prop
  have hg3 := measurable_iteratedDeriv_three s N
  have hc1 := measurable_loopCount_of (N := N) (c := fun z => z.1)
    (a := fun z : Configuration N × (ℝ × ℝ × ℝ) => z.2.1 - z.2.2.1)
    (r := fun z : Configuration N × (ℝ × ℝ × ℝ) => z.2.2.1) (ht.sub hu) hu hX
  have hc2 := measurable_loopCount_of (N := N) (c := fun z => z.1)
    (a := fun z : Configuration N × (ℝ × ℝ × ℝ) => z.2.1)
    (r := fun z : Configuration N × (ℝ × ℝ × ℝ) => z.2.2.2) ht hv hX
  have hG : Measurable (fun z : Configuration N × (ℝ × ℝ × ℝ) =>
      ‖iteratedDeriv 3 (loopArcG s N) (z.2.2.1 + z.2.2.2)‖ₑ
        * ‖loopCount (z.2.1 - z.2.2.1) z.2.2.1 z.1 - z.2.2.1‖ₑ
        * ‖loopCount z.2.1 z.2.2.2 z.1 - z.2.2.2‖ₑ) := by
    refine ((hg3.comp (hu.add hv)).enorm.mul ((hc1.sub hu).enorm)).mul ((hc2.sub hv).enorm)
  have hS : MeasurableSet {z : Configuration N × (ℝ × ℝ × ℝ) | z.2 ∈ largeRegion ((N : ℝ) / 2)} :=
    (measurableSet_largeRegion _).preimage measurable_snd
  have heq : (fun z : Configuration N × (ℝ × ℝ × ℝ) => largeIntegrand s N z.2 z.1)
      = {z : Configuration N × (ℝ × ℝ × ℝ) | z.2 ∈ largeRegion ((N : ℝ) / 2)}.indicator
          (fun z => ‖iteratedDeriv 3 (loopArcG s N) (z.2.2.1 + z.2.2.2)‖ₑ
            * ‖loopCount (z.2.1 - z.2.2.1) z.2.2.1 z.1 - z.2.2.1‖ₑ
            * ‖loopCount z.2.1 z.2.2.2 z.1 - z.2.2.2‖ₑ) := by
    funext z
    by_cases h : z.2 ∈ largeRegion ((N : ℝ) / 2)
    · simp only [largeIntegrand, Set.indicator_of_mem h, Set.indicator_of_mem (show z ∈ {z : Configuration N × (ℝ × ℝ × ℝ) | z.2 ∈ largeRegion ((N : ℝ) / 2)} from h)]
    · simp only [largeIntegrand, Set.indicator_of_notMem h,
        Set.indicator_of_notMem (show z ∉ {z : Configuration N × (ℝ × ℝ × ℝ) | z.2 ∈ largeRegion ((N : ℝ) / 2)} from h)]
  rw [heq]
  exact hG.indicator hS

/-- The large-region parametric integral is measurable in the configuration. -/
theorem measurable_largeMoment (s : ℝ) (N : ℕ+) (m : ℝ) :
    Measurable (fun X : Configuration N => ∫⁻ θ, largeIntegrand s N θ X ∂(loopArcLargeMeasure m N)) := by
  have := sFinite_loopArcLargeMeasure m N
  exact Measurable.lintegral_prod_right' (f := fun z : Configuration N × (ℝ × ℝ × ℝ) =>
    largeIntegrand s N z.2 z.1) (measurable_largeIntegrand_swap s N)

/-- The atomic integrand, with the configuration first, is measurable. -/
theorem measurable_atomIntegrand_swap (s : ℝ) (N : ℕ+) :
    Measurable (fun z : Configuration N × (ℝ × ℝ) => atomIntegrand s N z.2 z.1) := by
  have hu : Measurable (fun z : Configuration N × (ℝ × ℝ) => z.2.2) := by fun_prop
  have ht : Measurable (fun z : Configuration N × (ℝ × ℝ) => z.2.1) := by fun_prop
  have hX : Measurable (fun z : Configuration N × (ℝ × ℝ) => z.1) := by fun_prop
  have hc1 := measurable_loopCount_of (N := N) (c := fun z => z.1)
    (a := fun z : Configuration N × (ℝ × ℝ) => z.2.1 - z.2.2)
    (r := fun z : Configuration N × (ℝ × ℝ) => z.2.2) (ht.sub hu) hu hX
  have hR : Measurable (fun z : Configuration N × (ℝ × ℝ) => (N : ℝ) / 2 - z.2.2) :=
    measurable_const.sub hu
  have hc2 := measurable_loopCount_of (N := N) (c := fun z => z.1)
    (a := fun z : Configuration N × (ℝ × ℝ) => z.2.1)
    (r := fun z : Configuration N × (ℝ × ℝ) => (N : ℝ) / 2 - z.2.2) ht hR hX
  have hF : Measurable (fun z : Configuration N × (ℝ × ℝ) =>
      ‖loopCount (z.2.1 - z.2.2) z.2.2 z.1 - z.2.2‖ₑ
        * ‖loopCount z.2.1 ((N : ℝ) / 2 - z.2.2) z.1 - ((N : ℝ) / 2 - z.2.2)‖ₑ) :=
    ((hc1.sub hu).enorm).mul ((hc2.sub hR).enorm)
  have hS : MeasurableSet {z : Configuration N × (ℝ × ℝ) | z.2.2 ∈ Ioc (0 : ℝ) ((N : ℝ) / 2)} :=
    (measurableSet_Ioc.preimage (measurable_snd.comp measurable_snd))
  have heq : (fun z : Configuration N × (ℝ × ℝ) => atomIntegrand s N z.2 z.1)
      = {z : Configuration N × (ℝ × ℝ) | z.2.2 ∈ Ioc (0 : ℝ) ((N : ℝ) / 2)}.indicator
          (fun z => ‖loopCount (z.2.1 - z.2.2) z.2.2 z.1 - z.2.2‖ₑ
            * ‖loopCount z.2.1 ((N : ℝ) / 2 - z.2.2) z.1 - ((N : ℝ) / 2 - z.2.2)‖ₑ) := by
    funext z
    by_cases h : z.2.2 ∈ Ioc (0 : ℝ) ((N : ℝ) / 2)
    · have h' : z ∈ {z : Configuration N × (ℝ × ℝ) | z.2.2 ∈ Ioc (0 : ℝ) ((N : ℝ) / 2)} := h
      rw [atomIntegrand, Set.indicator_of_mem h', Set.indicator_of_mem h]
    · have h' : z ∉ {z : Configuration N × (ℝ × ℝ) | z.2.2 ∈ Ioc (0 : ℝ) ((N : ℝ) / 2)} := h
      rw [atomIntegrand, Set.indicator_of_notMem h', Set.indicator_of_notMem h]
  rw [heq]
  exact hF.indicator hS

/-- The atomic parametric integral is measurable in the configuration. -/
theorem measurable_atomMoment (s : ℝ) (N : ℕ+) (m : ℝ) :
    Measurable (fun X : Configuration N => ∫⁻ θ, atomIntegrand s N θ X ∂(atomMeasure m N)) := by
  have := sFinite_atomMeasure m N
  exact Measurable.lintegral_prod_right' (f := fun z : Configuration N × (ℝ × ℝ) =>
    atomIntegrand s N z.2 z.1) (measurable_atomIntegrand_swap s N)

/-- The count is measurable and its enorm is the `ofReal` of the count. -/
theorem enorm_loopCount_eq_ofReal {N : ℕ+} (a r : ℝ) (X : Configuration N) :
    ENNReal.ofReal (loopCount a r X) = ‖loopCount a r X‖ₑ := by
  rw [Real.enorm_eq_ofReal (loopCount_nonneg a r X)]

/-- Lower integral of a sum of three terms, the first two measurable. -/
theorem lintegral_add_three' {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {f g h : Ω → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) (_hh : Measurable h) :
    ∫⁻ x, f x + g x + h x ∂μ = ∫⁻ x, f x ∂μ + ∫⁻ x, g x ∂μ + ∫⁻ x, h x ∂μ := by
  have h1 : Measurable (fun x => f x + g x) := hf.add hg
  calc ∫⁻ x, f x + g x + h x ∂μ = ∫⁻ x, (fun x => f x + g x) x + h x ∂μ := rfl
    _ = ∫⁻ x, (fun x => f x + g x) x ∂μ + ∫⁻ x, h x ∂μ := lintegral_add_left h1 h
    _ = ∫⁻ x, f x ∂μ + ∫⁻ x, g x ∂μ + ∫⁻ x, h x ∂μ := by
        rw [show (∫⁻ x, (fun x => f x + g x) x ∂μ) = ∫⁻ x, f x + g x ∂μ from rfl,
          lintegral_add_left hf g]

/-- Lower integral of a sum of four terms, the first three measurable. -/
theorem lintegral_add_four' {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {f g h k : Ω → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h) :
    ∫⁻ x, f x + g x + h x + k x ∂μ = ∫⁻ x, f x ∂μ + ∫⁻ x, g x ∂μ + ∫⁻ x, h x ∂μ
      + ∫⁻ x, k x ∂μ := by
  have h1 : Measurable (fun x => f x + g x + h x) := (hf.add hg).add hh
  calc ∫⁻ x, f x + g x + h x + k x ∂μ = ∫⁻ x, (fun x => f x + g x + h x) x + k x ∂μ := rfl
    _ = ∫⁻ x, (fun x => f x + g x + h x) x ∂μ + ∫⁻ x, k x ∂μ := lintegral_add_left h1 k
    _ = _ := by rw [show (∫⁻ x, (fun x => f x + g x + h x) x ∂μ)
          = ∫⁻ x, f x + g x + h x ∂μ from rfl, lintegral_add_three' μ hf hg hh]

/-- **The `L^p` clause of the arcs part of Lemma B.2, conditional on rigidity.** For `p ≥ 1` there
is `C > 0` such that for every `N ≥ 2`, every integer `0 ≤ m < N` and the Prékopa–Leindler inequality
`External.PrekopaLeindler`, the `L^p` norm over the configuration of `∫_m^{m+1} |Λ(t)| dt` is at
most `C`. The constant does not depend on `N`, `m`. -/
theorem loopArcLambda_cell_lp_of_rigidity {beta s : ℝ} (hbeta : 0 < beta) (hs : 0 < s)
    (hs1 : s < 1) (hRig : Internal.RigidityConclusion beta s hbeta hs hs1) {p : ℝ} (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (_hPL : External.PrekopaLeindler) (N : ℕ+), 2 ≤ (N : ℕ) →
      ∀ (m : ℕ), m < N →
        eLpNorm (fun X : Configuration N =>
            ∫ t in Ioc (m : ℝ) ((m : ℝ) + 1), |loopArcLambda s N X t|)
          (ENNReal.ofReal p) (gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N)
          ≤ ENNReal.ofReal C := by
  have hp0 : 0 < p := by linarith
  obtain ⟨δ, M, hδ0, hδ1, hM0, hmom⟩ := loopArc_moment_of_rigidity beta s hbeta hs hs1 hRig p hp
  obtain ⟨hcount_b, -, hwin_b, -⟩ := Internal.auxiliary_Loop_moments_of_rigidity beta s hbeta hs hs1 hRig
  obtain ⟨Cc, hCc, hcount⟩ := hcount_b p hp
  obtain ⟨Cw, hCw, hwin⟩ := hwin_b p hp
  obtain ⟨Cg, hCg, hgC'⟩ := norm_iteratedDeriv_loopArcG_le s hs hs1
  have hg3 : ∀ (N : ℕ+) (r : ℝ), 0 < r → r ≤ (N : ℝ) / 2 →
      ‖iteratedDeriv 3 (loopArcG s N) r‖ₑ ≤ ENNReal.ofReal (Cg * r ^ (-s - 3)) := by
    intro N r hr hrN
    have h := hgC' N 3 (by norm_num) (by norm_num) r hr hrN
    rw [Real.enorm_eq_ofReal_abs]
    refine ENNReal.ofReal_le_ofReal (h.trans (le_of_eq ?_))
    norm_num
  have hg2 : ∀ (N : ℕ+) (r : ℝ), 0 < r → r ≤ (N : ℝ) / 2 →
      ‖iteratedDeriv 2 (loopArcG s N) r‖ₑ ≤ ENNReal.ofReal (Cg * r ^ (-s - 2)) := by
    intro N r hr hrN
    have h := hgC' N 2 (by norm_num) (by norm_num) r hr hrN
    rw [Real.enorm_eq_ofReal_abs]
    refine ENNReal.ofReal_le_ofReal (h.trans (le_of_eq ?_))
    norm_num
  obtain ⟨K, hK0, hK⟩ := lintegral_cell_three_bound hs hs1
  -- the large-region and atomic constants, uniform in `N`, `m` and the configuration measure
  obtain ⟨KL, hKLtop, hKL⟩ : ∃ KL : ℝ≥0∞, KL ≠ ⊤ ∧ ∀ (N : ℕ+) (m : ℝ)
      (μ : Measure (Configuration N)) [IsFiniteMeasure μ],
      (∀ a u : ℝ, 0 < u → u ≤ (N : ℝ) / 2 →
        ∫⁻ X, ‖loopCount a u X - u‖ₑ ^ (2 * p) ∂μ
          ≤ ENNReal.ofReal (M * (1 + u) ^ (s / 2 + δ)) ^ (2 * p)) →
      (∀ r : ℝ, 0 < r → r ≤ (N : ℝ) / 2 →
        ‖iteratedDeriv 3 (loopArcG s N) r‖ₑ ≤ ENNReal.ofReal (Cg * r ^ (-s - 3))) →
      ∫⁻ X, (∫⁻ θ, largeIntegrand s N θ X ∂(loopArcLargeMeasure m N)) ^ p ∂μ ≤ KL :=
    ⟨_, by finiteness, fun N m μ _ hmo hgc =>
      lintegral_largeIntegrand_lp_le hs (by linarith) hp hM0 hCg.le m hmo hgc⟩
  obtain ⟨KA, hKAtop, hKA⟩ : ∃ KA : ℝ≥0∞, KA ≠ ⊤ ∧ ∀ (N : ℕ+) (m : ℝ)
      (μ : Measure (Configuration N)) [IsFiniteMeasure μ], 2 ≤ (N : ℕ) →
      (∀ a u : ℝ, 0 < u → u ≤ (N : ℝ) / 2 →
        ∫⁻ X, ‖loopCount a u X - u‖ₑ ^ (2 * p) ∂μ
          ≤ ENNReal.ofReal (M * (1 + u) ^ (s / 2 + δ)) ^ (2 * p)) →
      (∀ r : ℝ, 0 < r → r ≤ (N : ℝ) / 2 →
        ‖iteratedDeriv 2 (loopArcG s N) r‖ₑ ≤ ENNReal.ofReal (Cg * r ^ (-s - 2))) →
      ∫⁻ X, (‖iteratedDeriv 2 (loopArcG s N) ((N : ℝ) / 2)‖ₑ
          * ∫⁻ θ, atomIntegrand s N θ X ∂(atomMeasure m N)) ^ p ∂μ ≤ KA :=
    ⟨_, by finiteness, fun N m μ _ hN hmo hgc =>
      loopArc_atom_lp_le hs hδ0 (by linarith) hp hM0 hCg.le m hN hmo hgc⟩
  -- the constant of the `L^p` bound
  set KS : ℝ≥0∞ := ENNReal.ofReal K ^ p * 4 ^ (p - 1) * (1 + ENNReal.ofReal (Cc * (1 + 2)) ^ p
    + ENNReal.ofReal (Cc * (1 + 2)) ^ p + ENNReal.ofReal Cw ^ p) with hKS
  have hKStop : KS ≠ ⊤ := by
    rw [hKS]
    finiteness
  set Ktot : ℝ≥0∞ := 4 ^ (p - 1) * (KS + KL + KA) with hKtot
  have hKtot_top : Ktot ≠ ⊤ := by
    rw [hKtot]
    finiteness
  -- the constant `C`
  set κ : ℝ := Ktot.toReal ^ (1 / p) + 1 with hκ
  have hκpos : 0 < κ := by
    have : (0 : ℝ) ≤ Ktot.toReal ^ (1 / p) := Real.rpow_nonneg ENNReal.toReal_nonneg _
    rw [hκ]
    linarith
  refine ⟨κ, hκpos, fun hPL N hN m hm => ?_⟩
  have : IsProbabilityMeasure (gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N) :=
    (modelWellDefined _ N).2.2
  set μ := gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N with hμ
  have hmr0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hmN : (m : ℝ) + 1 ≤ (N : ℝ) := by
    have : m + 1 ≤ N := hm
    exact_mod_cast this
  have hN2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hmom' : ∀ a u : ℝ, 0 < u → u ≤ (N : ℝ) / 2 →
      ∫⁻ X, ‖loopCount a u X - u‖ₑ ^ (2 * p) ∂μ
        ≤ ENNReal.ofReal (M * (1 + u) ^ (s / 2 + δ)) ^ (2 * p) :=
    fun a u h1 h2 => hmom hPL N hN a u h1 h2
  have hg3' : ∀ r : ℝ, 0 < r → r ≤ (N : ℝ) / 2 →
      ‖iteratedDeriv 3 (loopArcG s N) r‖ₑ ≤ ENNReal.ofReal (Cg * r ^ (-s - 3)) :=
    fun r h1 h2 => hg3 N r h1 h2
  have hg2' : ∀ r : ℝ, 0 < r → r ≤ (N : ℝ) / 2 →
      ‖iteratedDeriv 2 (loopArcG s N) r‖ₑ ≤ ENNReal.ofReal (Cg * r ^ (-s - 2)) :=
    fun r h1 h2 => hg2 N r h1 h2
  -- the three parts of the cell bound
  set S : Configuration N → ℝ≥0∞ := fun X => ENNReal.ofReal K * (1 + ENNReal.ofReal (loopCount (m : ℝ) 2 X)
      + ENNReal.ofReal (loopCount ((m : ℝ) - 1) 2 X)
      + ENNReal.ofReal (windowSum s N ((m : ℝ) - 1) 2 X)) with hS
  have hSeq : ∀ X : Configuration N, ENNReal.ofReal K * (1 + ENNReal.ofReal (loopCount (m : ℝ) 2 X)
      + ENNReal.ofReal (loopCount ((m : ℝ) - 1) 2 X)
      + ∑ i : Fin (N : ℕ), (if loopPos X i ∈ microArc N ((m : ℝ) - 1) 2 then
          ENNReal.ofReal (rootedEnergy s X i) else 0)) = S X := by
    intro X
    rw [hS]
    simp only
    rw [ofReal_windowSum]
  set JL : Configuration N → ℝ≥0∞ := fun X =>
    ∫⁻ θ, largeIntegrand s N θ X ∂(loopArcLargeMeasure (m : ℝ) N) with hJL
  set JA : Configuration N → ℝ≥0∞ := fun X => ‖iteratedDeriv 2 (loopArcG s N) ((N : ℝ) / 2)‖ₑ
      * ∫⁻ θ, atomIntegrand s N θ X ∂(atomMeasure (m : ℝ) N) with hJA
  set Ψ : Configuration N → ℝ≥0∞ := fun X =>
    ∫⁻ t in Ioc (m : ℝ) ((m : ℝ) + 1), ‖loopArcLambda s N X t‖ₑ with hΨ
  have hΨle : ∀ X, Ψ X ≤ S X + JL X + JA X := fun X => by
    have h := hK N hN X (m : ℝ)
    rw [hSeq X] at h
    exact h
  -- measurability of the three parts
  have hcnt_meas : ∀ a : ℝ, Measurable (fun X : Configuration N => loopCount a 2 X) := fun a =>
    measurable_loopCount_of (N := N) (c := id) (a := fun _ => a) (r := fun _ => (2 : ℝ))
      measurable_const measurable_const measurable_id
  have hmS : Measurable S := by
    have h1 : Measurable (fun X : Configuration N => ENNReal.ofReal (loopCount (m : ℝ) 2 X)) :=
      ENNReal.measurable_ofReal.comp (hcnt_meas (m : ℝ))
    have h2 : Measurable (fun X : Configuration N => ENNReal.ofReal (loopCount ((m : ℝ) - 1) 2 X)) :=
      ENNReal.measurable_ofReal.comp (hcnt_meas ((m : ℝ) - 1))
    have h3 : Measurable (fun X : Configuration N => ENNReal.ofReal (windowSum s N ((m : ℝ) - 1) 2 X)) :=
      ENNReal.measurable_ofReal.comp (measurable_windowSum s N ((m : ℝ) - 1) 2)
    rw [hS]
    exact measurable_const.mul ((((measurable_const.add h1).add h2).add h3))
  have hmJL : Measurable JL := measurable_largeMoment s N (m : ℝ)
  have hmJA : Measurable JA := (measurable_atomMoment s N (m : ℝ)).const_mul _
  -- the moments of the counts and the window sum
  have hcnt : ∀ a r : ℝ, 0 < r → r ≤ (N : ℝ) →
      ∫⁻ X, ENNReal.ofReal (loopCount a r X) ^ p ∂μ ≤ ENNReal.ofReal (Cc * (1 + r)) ^ p := by
    intro a r hr hrN
    have h := lintegral_enorm_rpow_le_of_eLpNorm (μ := μ) hp (hcount hPL N hN a r hr hrN)
    have e : ∀ X : Configuration N, ENNReal.ofReal (loopCount a r X) = ‖loopCount a r X‖ₑ :=
      fun X => enorm_loopCount_eq_ofReal a r X
    simp_rw [e]
    exact h
  have hwin_bd : ∫⁻ X, ENNReal.ofReal (windowSum s N ((m : ℝ) - 1) 2 X) ^ p ∂μ
      ≤ ENNReal.ofReal Cw ^ p := by
    have h := lintegral_enorm_rpow_le_of_eLpNorm (μ := μ) hp
      (hwin hPL N hN ((m : ℝ) - 1) 2 (by norm_num) (by norm_num) (by linarith))
    have e : ∀ X : Configuration N, ENNReal.ofReal (windowSum s N ((m : ℝ) - 1) 2 X)
        = ‖windowSum s N ((m : ℝ) - 1) 2 X‖ₑ :=
      fun X => (Real.enorm_eq_ofReal (windowSum_nonneg s N _ _ X)).symm
    simp_rw [e]
    exact h
  -- the `p`-th moment of the counts and the window sum, with the cell weight `K`
  have hc_ne : ENNReal.ofReal K ^ p * 4 ^ (p - 1) ≠ ⊤ := by finiteness
  have hSpt : ∀ X : Configuration N, S X ^ p ≤ ENNReal.ofReal K ^ p * 4 ^ (p - 1)
      * (1 ^ p + ENNReal.ofReal (loopCount (m : ℝ) 2 X) ^ p
        + ENNReal.ofReal (loopCount ((m : ℝ) - 1) 2 X) ^ p
        + ENNReal.ofReal (windowSum s N ((m : ℝ) - 1) 2 X) ^ p) := by
    intro X
    rw [hS]
    simp only
    rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, mul_assoc]
    exact mul_le_mul' le_rfl (ennreal_add_four_rpow_le hp _ _ _ _)
  have hmeas1 : Measurable (fun X : Configuration N => ENNReal.ofReal (loopCount (m : ℝ) 2 X) ^ p) :=
    (ENNReal.measurable_ofReal.comp (hcnt_meas (m : ℝ))).pow_const p
  have hmeas2 : Measurable (fun X : Configuration N =>
      ENNReal.ofReal (loopCount ((m : ℝ) - 1) 2 X) ^ p) :=
    (ENNReal.measurable_ofReal.comp (hcnt_meas ((m : ℝ) - 1))).pow_const p
  have hmeas3 : Measurable (fun X : Configuration N =>
      ENNReal.ofReal (windowSum s N ((m : ℝ) - 1) 2 X) ^ p) :=
    (ENNReal.measurable_ofReal.comp (measurable_windowSum s N ((m : ℝ) - 1) 2)).pow_const p
  have hSp : ∫⁻ X, S X ^ p ∂μ ≤ KS := by
    have hone : ∫⁻ _X : Configuration N, (1 : ℝ≥0∞) ^ p ∂μ = 1 := by
      rw [lintegral_const, measure_univ, ENNReal.one_rpow, mul_one]
    calc ∫⁻ X, S X ^ p ∂μ
        ≤ ∫⁻ X, ENNReal.ofReal K ^ p * 4 ^ (p - 1)
            * (1 ^ p + ENNReal.ofReal (loopCount (m : ℝ) 2 X) ^ p
              + ENNReal.ofReal (loopCount ((m : ℝ) - 1) 2 X) ^ p
              + ENNReal.ofReal (windowSum s N ((m : ℝ) - 1) 2 X) ^ p) ∂μ :=
          lintegral_mono hSpt
      _ = ENNReal.ofReal K ^ p * 4 ^ (p - 1)
            * ∫⁻ X, (1 ^ p + ENNReal.ofReal (loopCount (m : ℝ) 2 X) ^ p
              + ENNReal.ofReal (loopCount ((m : ℝ) - 1) 2 X) ^ p
              + ENNReal.ofReal (windowSum s N ((m : ℝ) - 1) 2 X) ^ p) ∂μ :=
          lintegral_const_mul' _ _ hc_ne
      _ = ENNReal.ofReal K ^ p * 4 ^ (p - 1)
            * ((∫⁻ _X : Configuration N, (1 : ℝ≥0∞) ^ p ∂μ)
              + ∫⁻ X, ENNReal.ofReal (loopCount (m : ℝ) 2 X) ^ p ∂μ
              + ∫⁻ X, ENNReal.ofReal (loopCount ((m : ℝ) - 1) 2 X) ^ p ∂μ
              + ∫⁻ X, ENNReal.ofReal (windowSum s N ((m : ℝ) - 1) 2 X) ^ p ∂μ) := by
          congr 1
          exact lintegral_add_four' μ measurable_const hmeas1 hmeas2
      _ ≤ ENNReal.ofReal K ^ p * 4 ^ (p - 1)
            * (1 + ENNReal.ofReal (Cc * (1 + 2)) ^ p + ENNReal.ofReal (Cc * (1 + 2)) ^ p
              + ENNReal.ofReal Cw ^ p) := by
          rw [hone]
          gcongr
          · exact hcnt (m : ℝ) 2 (by norm_num) hN2
          · exact hcnt ((m : ℝ) - 1) 2 (by norm_num) hN2
      _ = KS := rfl
  -- the large and atomic moments
  have hJLp : ∫⁻ X, JL X ^ p ∂μ ≤ KL := hKL N (m : ℝ) μ hmom' hg3'
  have hJAp : ∫⁻ X, JA X ^ p ∂μ ≤ KA := hKA N (m : ℝ) μ hN hmom' hg2'
  -- the `p`-th moment of `Ψ`
  have hΨp : ∀ X, Ψ X ^ p ≤ 4 ^ (p - 1) * (S X ^ p + JL X ^ p + JA X ^ p) := fun X =>
    (ENNReal.rpow_le_rpow (hΨle X) hp0.le).trans (ennreal_add_three_rpow_le hp _ _ _)
  have hΨint : ∫⁻ X, Ψ X ^ p ∂μ ≤ Ktot := by
    have h4 : (4 : ℝ≥0∞) ^ (p - 1) ≠ ⊤ := by finiteness
    calc ∫⁻ X, Ψ X ^ p ∂μ ≤ ∫⁻ X, 4 ^ (p - 1) * (S X ^ p + JL X ^ p + JA X ^ p) ∂μ :=
          lintegral_mono hΨp
      _ = 4 ^ (p - 1) * (∫⁻ X, S X ^ p ∂μ + ∫⁻ X, JL X ^ p ∂μ + ∫⁻ X, JA X ^ p ∂μ) := by
          rw [lintegral_const_mul' _ _ h4, lintegral_add_three' μ (hmS.pow_const p)
            (hmJL.pow_const p) (hmJA.pow_const p)]
      _ ≤ 4 ^ (p - 1) * (KS + KL + KA) :=
          mul_le_mul' le_rfl (add_le_add (add_le_add hSp hJLp) hJAp)
      _ = Ktot := rfl
  -- conversion to the `eLpNorm` of the real cell integral
  have hfnn : ∀ X : Configuration N, 0 ≤ ∫ t in Ioc (m : ℝ) ((m : ℝ) + 1), |loopArcLambda s N X t| :=
    fun X => integral_nonneg fun t => abs_nonneg _
  have hfΨ : ∀ X : Configuration N,
      ENNReal.ofReal (∫ t in Ioc (m : ℝ) ((m : ℝ) + 1), |loopArcLambda s N X t|) = Ψ X := by
    intro X
    have hint : IntegrableOn (fun t => |loopArcLambda s N X t|) (Ioc (m : ℝ) ((m : ℝ) + 1)) :=
      ((integrable_loopArcLambda s hs hs1 N X).mono_set (Set.Ioc_subset_Ioc hmr0 hmN)).abs
    rw [ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun t => abs_nonneg _)]
    refine lintegral_congr fun t => ?_
    rw [Real.enorm_eq_ofReal_abs]
  have hmeasf : AEStronglyMeasurable
      (fun X : Configuration N => ∫ t in Ioc (m : ℝ) ((m : ℝ) + 1), |loopArcLambda s N X t|) μ := by
    have hsm : StronglyMeasurable (fun z : Configuration N × ℝ => |loopArcLambda s N z.1 z.2|) := by
      have h0 := (stronglyMeasurable_loopArcLambda s N).norm
      simpa only [Real.norm_eq_abs] using h0
    exact (hsm.integral_prod_right' (ν := volume.restrict (Ioc (m : ℝ) ((m : ℝ) + 1)))).aestronglyMeasurable
  have hEL : eLpNorm (fun X : Configuration N => ∫ t in Ioc (m : ℝ) ((m : ℝ) + 1), |loopArcLambda s N X t|)
      (ENNReal.ofReal p) μ = (∫⁻ X, Ψ X ^ p ∂μ) ^ (1 / p) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.mpr hp0).ne' ENNReal.ofReal_ne_top hmeasf,
      ENNReal.toReal_ofReal hp0.le]
    congr 1
    refine lintegral_congr fun X => ?_
    rw [Real.enorm_eq_ofReal (hfnn X), hfΨ X]
  rw [hEL]
  calc (∫⁻ X, Ψ X ^ p ∂μ) ^ (1 / p) ≤ Ktot ^ (1 / p) :=
        ENNReal.rpow_le_rpow hΨint (div_nonneg zero_le_one hp0.le)
    _ = ENNReal.ofReal (Ktot.toReal ^ (1 / p)) := by
        conv_lhs => rw [← ENNReal.ofReal_toReal hKtot_top]
        rw [ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (div_nonneg zero_le_one hp0.le)]
    _ ≤ ENNReal.ofReal κ := ENNReal.ofReal_le_ofReal (by rw [hκ]; linarith)

end Riesz1

end
end
