/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopAnchoringTranslation
public import Riesz1.Auxiliary.LoopAnchoringBadEvent

/-!
# The second-moment anchoring bound

The first assertion of the anchoring part of Lemma 5.8. The
smallness threshold and power loss are chosen before the thermodynamic
parameters and cutoff, expressing their dependence only on `s, α, γ`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal ContDiff

namespace Riesz1

/-- The `L²` anchoring assertion, with its second-moment certificate.
Only the Bakry–Émery criterion `External.BakryEmery` and the Prékopa–Leindler inequality
`External.PrekopaLeindler` are supplied as analytic hypotheses. -/
theorem loopAnchoring_l2 {s α γ : ℝ}
    (hs : 0 < s) (hs1 : s < 1) (hα : s - 1 ≤ α) (hα2 : α < s / 2)
    (hγ : max 4 (2 / s) ≤ γ) :
    ∃ εstar : ℝ, 0 < εstar ∧ ∃ κ : ℝ, 0 < κ ∧
      ∀ (β : ℝ) (hβ : 0 < β) (_hBE : External.BakryEmery) (_hPL : External.PrekopaLeindler)
        (χ : ℝ → ℝ), ContDiff ℝ ∞ χ → HasCompactSupport χ →
        tsupport χ ⊆ Ioo (-(1 / 4)) (1 / 4) →
        (∀ x : ℝ, |x| ≤ 1 / 8 → χ x = 1) → (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) →
        ∀ ε : ℝ, 0 < ε → ε < εstar → ∃ C : ℝ, 0 < C ∧
          ∀ (n : ℕ) (ℓ C₀ : ℝ) (ψ : ℝ → ℝ),
            0 < ℓ → ℓ ≤ 1 → 1 ≤ ((n + 1).succPNat : ℝ) * ℓ → 0 ≤ C₀ →
            ContDiff ℝ ∞ ψ → Function.Periodic ψ ℓ⁻¹ →
            (∀ t, |deriv ψ t| ≤ C₀ * gradWeightOne s (1 - s + α)
              (((n + 1).succPNat : ℝ) * ℓ) ℓ⁻¹ t) →
            (∀ t, |deriv (deriv ψ) t| ≤ C₀ * gradWeightTwo s (1 - s + α)
              (((n + 1).succPNat : ℝ) * ℓ) ℓ⁻¹ t) →
            let μ := loopPrecedingMeasure ⟨(β, s), hβ, hs, hs1⟩ (n + 1).succPNat
            let E := fun X : LoopPrecedingConfiguration (n + 1).succPNat =>
              loopLocalLoop s (n + 1).succPNat ℓ γ (loopLocalTransport χ (n + 1).succPNat ℓ γ ψ) X -
                loopCutoffF χ s γ ε (n + 1).succPNat ℓ ψ (loopPrecedingY X)
            MemLp E 2 μ ∧ eLpNorm E 2 μ ≤
              ENNReal.ofReal (C * C₀ * (((n + 1).succPNat : ℝ) * ℓ) ^ (1 - s + α + κ * ε)) := by
  have hγ4 := (le_max_left _ _).trans hγ
  have hγ1 : 1 < γ := by linarith
  obtain ⟨εt, hεt, κ, hκ, ht⟩ := loopAnchoring_translation_error hs hs1 hα hα2 hγ
  refine ⟨min εt (min (1 / 8) ((1 - s / 2) / 8)), by
    have : 0 < (1 - s / 2) / 8 := by linarith
    positivity, κ, hκ, ?_⟩
  intro β hβ hBE hPL χ hχ hχc hχs hχ1 hχ01 ε hε hεstar
  have hεt' := hεstar.trans_le (min_le_left _ _)
  have hεs := hεstar.trans_le (min_le_right _ _)
  have hεs' : ε ≤ 1 - s / 2 := by
    have := hεs.trans_le (min_le_right _ _)
    linarith
  obtain ⟨Ct, hCt, htrans⟩ := ht ε hε hεt'
  obtain ⟨Ce, hCe, henv⟩ := loopTransport_envelope hs hs1 hα hα2 hχ hχc hχs hχ1 hχ01
  obtain ⟨Cb, hCb, hbad⟩ := loopAnchoring_bad_error hBE hPL β s hβ hs hs1
    hα hα2 hγ1 hε hεs hχ hχc hχs hχ1 hχ01
  obtain ⟨Cm, _, hmom⟩ := loopAnchoring_error_four hPL β s hβ hs hs1
    hα hα2 hγ1 hε hεs' hχ hχc hχs hχ1 hχ01
  refine ⟨Ct * Ce + Cb, by nlinarith, ?_⟩
  intro n ℓ C₀ ψ hℓ hℓ1 hK hC₀ hψ hp hd hdd
  let N := (n + 1).succPNat
  let P : Parameters := ⟨(β, s), hβ, hs, hs1⟩
  let μ := loopPrecedingMeasure P N
  let K : ℝ := (N : ℝ) * ℓ
  let ψ₀ := loopTransport χ N ℓ γ ψ
  let S := {X : LoopPrecedingConfiguration N | loopCutoff s γ ε N ℓ (loopPrecedingY X) ≠ 1}
  let E := fun X : LoopPrecedingConfiguration N =>
    loopLocalLoop s N ℓ γ (loopLocalTransport χ N ℓ γ ψ) X -
      loopCutoffF χ s γ ε N ℓ ψ (loopPrecedingY X)
  have hE4 : MemLp E 4 μ := (hmom n ℓ C₀ ψ hℓ hK hC₀ hψ hp hd hdd).1
  have hE : MemLp E 2 μ := hE4.mono_exponent (by norm_num)
  have hS : MeasurableSet S := (measurableSet_eq_fun
    ((measurable_loopCutoff s γ ε N ℓ).comp (measurable_loopPrecedingY n)) measurable_const).compl
  have henv' := henv N ℓ γ ψ C₀ hℓ hK hγ1 hC₀ hψ hp hd hdd
  have hψ₀ : ContDiff ℝ ∞ ψ₀ := contDiff_loopTransport hχ hψ hχs N hℓ γ
  have hp₀ : Function.Periodic ψ₀ ℓ⁻¹ := loopTransport_periodic hℓ χ hp
  have hgood : ∀ X ∈ Sᶜ, ‖E X‖ ≤ Ct * Ce * C₀ * K ^ (1 - s + α + κ * ε) := by
    intro X hX
    have hη : loopCutoff s γ ε N ℓ (loopPrecedingY X) = 1 := by
      simpa only [S, mem_compl_iff, mem_ofPred_eq, not_not] using hX
    have hηpos : 0 < loopCutoff s γ ε N ℓ (loopPrecedingY X) := by rw [hη]; norm_num
    have hev := loopAnchoring_event_restrict hℓ hK (by linarith : 0 ≤ γ)
      (gradEvent_of_loopCutoff_pos hℓ ⟨loopPrecedingY X, loopAnchoring_preceding_mem X⟩ hηpos)
    have hD := (loopAnchoring_displacement_lt hℓ hK (by linarith : 0 ≤ γ) X hηpos).le
    have hh := htrans N ℓ (Ce * C₀) ψ₀ (by simp [N]) hℓ hℓ1 hK (mul_nonneg hCe hC₀)
      hψ₀ hp₀ (fun t => (henv' t).1) (fun t => (henv' t).2)
      (loopAnchoring_transport_support hχs hℓ) X hev hD
    change |loopLocalLoop s N ℓ γ (loopLocalTransport χ N ℓ γ ψ) X -
      loopCutoffF χ s γ ε N ℓ ψ (loopPrecedingY X)| ≤ _
    unfold loopCutoffF
    rw [hη, one_mul]
    calc
      _ ≤ Ct * (Ce * C₀) * K ^ (1 - s + α + κ * ε) := hh
      _ = _ := by ring
  have hgoodn : eLpNorm E 2 (μ.restrict Sᶜ) ≤
      ENNReal.ofReal (Ct * Ce * C₀ * K ^ (1 - s + α + κ * ε)) := by
    have hh := eLpNorm_le_of_ae_bound hE.aestronglyMeasurable.restrict
      ((ae_restrict_mem hS.compl).mono fun X hX => hgood X hX) (p := (2 : ℝ≥0∞))
    apply hh.trans
    have hm : (μ.restrict Sᶜ) univ ≤ 1 := by
      rw [Measure.restrict_apply_univ]
      calc μ Sᶜ ≤ μ univ := measure_mono (subset_univ _)
           _ = 1 := measure_univ
    exact mul_le_of_le_one_left' (ENNReal.rpow_le_one hm (by positivity))
  have hbadn := hbad n ℓ C₀ ψ hℓ hℓ1 hK hC₀ hψ hp hd hdd
  have hsplit : E = Sᶜ.indicator E + S.indicator E := by
    ext X
    by_cases hX : X ∈ S <;> simp [hX]
  have hpow : K ^ (-10 : ℝ) ≤ K ^ (1 - s + α + κ * ε) :=
    Real.rpow_le_rpow_of_exponent_le hK (by nlinarith)
  refine ⟨hE, ?_⟩
  calc
    _ ≤ eLpNorm E 2 (μ.restrict Sᶜ) + eLpNorm E 2 (μ.restrict S) := by
      change eLpNorm E 2 μ ≤ _
      conv_lhs => rw [hsplit]
      apply (eLpNorm_add_le (by norm_num : (1 : ℝ≥0∞) ≤ 2)).trans
      rw [eLpNorm_indicator_eq_eLpNorm_restrict hS.compl.nullMeasurableSet,
        eLpNorm_indicator_eq_eLpNorm_restrict hS.nullMeasurableSet]
    _ ≤ ENNReal.ofReal (Ct * Ce * C₀ * K ^ (1 - s + α + κ * ε)) +
        ENNReal.ofReal (Cb * C₀ * K ^ (-10 : ℝ)) := add_le_add hgoodn hbadn
    _ ≤ ENNReal.ofReal ((Ct * Ce + Cb) * C₀ * K ^ (1 - s + α + κ * ε)) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have hh := mul_le_mul_of_nonneg_left hpow (mul_nonneg hCb.le hC₀)
      nlinarith

end Riesz1

end
