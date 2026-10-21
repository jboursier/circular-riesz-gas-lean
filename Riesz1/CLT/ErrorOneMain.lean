/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.CLT.ErrorOneChain
public import Riesz1.Frozen.Admissible

/-!
# First error bound in the proof of Theorem 3: the product error and the variance of `q_N`

`clt_error1_of_apriori` is the first error bound in the proof of Theorem 3 for an admissible
profile (`Admissible`), with the conditional hypothesis `APrioriConclusion` (Lemma 5.2)
as its only input. For every `τ > 0`, there are a constant `C` and a threshold `K₀` such that for
every admissible scale sequence and every particle number `N` with `Nℓ_N ≥ K₀`, the conclusion
`ErrorOneConclusion` holds: the sup bounds of `q_N` and `q_N'` with `δ_N^{-2-α-τ}`, the variance
bound of `Fluct_N[q_N(ℓ_N⁻¹ ·)]` with `K^{s+2τ} δ_N^{-2(2+α+τ)}` (`K = Nℓ_N`), and the bound of
`Error¹_N(u)` with `K^{s/2-1+τ} δ_N^{-2-α-τ}`, for every transport `ψ` of the regularized profile
and every `σ` with `σ² = σ_reg²`.

The exponent of the analytic bounds is `η = min (τ/2) ((s/2 - α)/2)`. The two cases of
`Admissible` are treated separately (`errorOne_macro_final`, `errorOne_compact_final`), each with its
own constant. The theorem takes their sum plus one as the common constant.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal

namespace Riesz1.Internal

/-- The smoothing radius `δ_N = (Nℓ_N)^{-d}` is below any fixed positive margin once `Nℓ_N` is
large. The threshold depends only on the product `Nℓ_N`. -/
lemma cltDelta_lt_of_large (P : Parameters) {r : ℝ} (hr : r < 1 / 2) :
    ∃ T : ℝ, 0 < T ∧ ∀ (N : ℕ+) (ℓ : Ioc (0 : ℝ) 1), T ≤ (N : ℝ) * ℓ.val →
      cltDelta P N ℓ < 1 / 2 - r := by
  have hd : 0 < (2 - P.val.2) / (4 + P.val.2) :=
    div_pos (by linarith [P.property.2.2]) (by linarith [P.property.2.1])
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    ((tendsto_rpow_neg_atTop hd).eventually (gt_mem_nhds (by linarith : (0 : ℝ) < 1 / 2 - r)))
  refine ⟨max T 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun N ℓ hK => ?_⟩
  unfold cltDelta
  exact hT _ ((le_max_left _ _).trans hK)

/-- In the macroscopic case the circle `Circle (observationLength ℓ)` has length one, so every
central representative lies in `[-1/2, 1/2)` and has absolute value below two. -/
lemma errorOne_vanish_of_macro (ℓ : Ioc (0 : ℝ) 1) (hL : (observationLength ℓ).val = 1)
    (x : ℝ) : ¬ (2 ≤ |centralRep (observationLength ℓ) (x : Circle (observationLength ℓ))|) := by
  intro hx
  have hmem := centralRep_mem_Ico (observationLength ℓ) (x : Circle (observationLength ℓ))
  have : |centralRep (observationLength ℓ) (x : Circle (observationLength ℓ))| ≤ 1 / 2 := by
    rw [abs_le]
    constructor <;> linarith [hmem.1, hmem.2, hL]
  linarith

/-- The derivative bound `APrioriConclusion` for the periodic product, with the variance constant
`CV` and the radius two (Lemma 5.2 with `λ = 0`). -/
lemma errorOne_apriori_of (hA : APrioriConclusion) (P : Parameters) (τ : ℝ) (hτ : 0 < τ) :
    ∃ CV : ℝ, 0 ≤ CV ∧ ∀ (N : ℕ+) (ℓ : Scale), 1 ≤ (N : ℝ) * ℓ.val → ∀ M : ℝ, 0 ≤ M →
      ∀ f : Circle (observationLength ℓ) → ℝ,
        ContDiff ℝ 1 (fun u : ℝ => f (u : Circle (observationLength ℓ))) →
        (∀ u : ℝ, |deriv (fun t : ℝ => f (t : Circle (observationLength ℓ))) u| ≤
          M * aPrioriEnvelope P.val.2 0 ((N : ℝ) * ℓ.val) 2
            |centralRep (observationLength ℓ) ((u - 0 : ℝ) : Circle (observationLength ℓ))|) →
        ∃ hB : Integrable (plainSum ℓ N f) (gibbsMeasure P N),
          variance (gibbsMeasure P N) (plainSum ℓ N f) hB ≤
            ENNReal.ofReal (CV * M ^ 2 * ((N : ℝ) * ℓ.val) ^ (2 * τ + max (2 * 0) P.val.2)) := by
  obtain ⟨CV, hCV, hAP⟩ := hA P 0 le_rfl (2 * τ) (by positivity) 2 two_pos 0
  exact ⟨CV, hCV.le, fun N ℓ hK M hM f hf hb => (hAP N ℓ hK M hM f hf hb).2⟩

/-- The exponent of the analytic bounds, `η = min (τ/2) ((s/2 - α)/2)`, has the properties used by
`errorOne_conclusion_of_facts`. -/
lemma errorOne_exponent (P : Parameters) (α τ : ℝ) (hτ : 0 < τ) (hα0 : P.val.2 - 1 ≤ α)
    (hαs : α < P.val.2 / 2) :
    0 < min (τ / 2) ((P.val.2 / 2 - α) / 2) ∧
    min (τ / 2) ((P.val.2 / 2 - α) / 2) ≤ τ ∧
    α + min (τ / 2) ((P.val.2 / 2 - α) / 2) < P.val.2 / 2 ∧
    P.val.2 - 1 < α + min (τ / 2) ((P.val.2 / 2 - α) / 2) ∧
    α - P.val.2 + 2 * min (τ / 2) ((P.val.2 / 2 - α) / 2) ≤ τ := by
  have hαpos : 0 < (P.val.2 / 2 - α) / 2 := by linarith
  have hm1 := min_le_left (τ / 2) ((P.val.2 / 2 - α) / 2)
  have hm2 := min_le_right (τ / 2) ((P.val.2 / 2 - α) / 2)
  have hpos : 0 < min (τ / 2) ((P.val.2 / 2 - α) / 2) := lt_min (by linarith) hαpos
  refine ⟨hpos, by linarith, by linarith, by linarith, by linarith [P.property.2.1]⟩

/-- **Macroscopic case.** For the unit-circle regularity data of the macroscopic profile, the
conclusion holds with a constant `Cm` and a threshold `K₁`, for every constant `C ≥ Cm`, every scale
sequence with `ℓ_N = 1` and every `N` with `Nℓ_N ≥ K₁`. -/
lemma errorOne_macro_final (hA : APrioriConclusion) (P : Parameters) (p : Profile) (α τ : ℝ)
    (hτ : 0 < τ) (hα0 : P.val.2 - 1 ≤ α) (hαs : α < P.val.2 / 2)
    {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) (d : TestData)
    (hd : 0 < d.1 ∧ d.1 < P.val.2 ∧ 0 < d.2.1 ∧ 0 < d.2.2.1) :
    ∃ Cm K₁ : ℝ, 0 ≤ Cm ∧ 0 < K₁ ∧ ∀ C : ℝ, Cm ≤ C → ∀ ell : Scales,
      (PrimitiveRegularity unitLength d.1 P.val.2 d.2.1 ⟨p.val, p.property⟩ ∧
        TransportRegularity P unitLength ⟨p.val, p.property⟩ d.2.2.2.1 d.2.2.2.2 α d.2.2.1) →
      (∀ N, (ell N).val = 1) → ∀ N : ℕ+, K₁ ≤ (N : ℝ) * (ell N).val →
        ErrorOneConclusion hρ P p α τ C ell N := by
  by_cases hU : PrimitiveRegularity unitLength d.1 P.val.2 d.2.1 ⟨p.val, p.property⟩ ∧
      TransportRegularity P unitLength ⟨p.val, p.property⟩ d.2.2.2.1 d.2.2.2.2 α d.2.2.1
  swap
  · exact ⟨0, 1, le_rfl, one_pos, fun C _ ell hU' => absurd hU' hU⟩
  obtain ⟨hd1, -, hB, hC₀⟩ := hd
  obtain ⟨CV, hCV, hAP⟩ := errorOne_apriori_of hA P τ hτ
  obtain ⟨hη, hητ, hηα, hηs, hτα⟩ := errorOne_exponent P α τ hτ hα0 hαs
  obtain ⟨C₁, C₂, C₃, C₄, hC₁, hC₂, hC₃, hC₄, hfacts⟩ :=
    errorOne_macro_facts hρ P p α _ d hα0 (by linarith) hη hηα hηs hd1 hB.le hC₀.le hU.1 hU.2
  refine ⟨(C₁ * C₃ + C₁ * C₄ * (1 + ((d.2.2.2.1 : ℕ) : ℝ)) + C₂ * C₃) +
      4 * CV * (C₁ * C₃ + C₁ * C₄ * (1 + ((d.2.2.2.1 : ℕ) : ℝ)) + C₂ * C₃) ^ 2 +
      2 * Real.sqrt CV * (C₁ * C₃ + C₁ * C₄ * (1 + ((d.2.2.2.1 : ℕ) : ℝ)) + C₂ * C₃),
    1, by positivity, one_pos, fun C hCC ell _ hone N hN => ?_⟩
  obtain ⟨ψ0, hψ0m, hψ0, hH, hsup, hder⟩ := hfacts ell hone N hN
  exact errorOne_conclusion_of_facts hρ P p α τ hτ hα0 hαs ell N hN _ hη hητ hτα hηs
    C₁ C₂ C₃ C₄ hC₁ hC₂ hC₃ hC₄ ((d.2.2.2.1 : ℕ)) d.2.2.2.2 ψ0 hψ0m hψ0 hH hsup hder
    CV hCV hAP
    (fun x hx => absurd hx (errorOne_vanish_of_macro (ell N) (by
      show (ell N).val⁻¹ = 1
      rw [hone N, inv_one]) x)) C hCC

/-- **Compact case.** For a compact profile, the conclusion holds with a constant `Cc` and a
threshold `K₂`, for every constant `C ≥ Cc`, every admissible scale sequence tending to zero and
every `N` with `Nℓ_N ≥ K₂`. -/
lemma errorOne_compact_final (hA : APrioriConclusion) (P : Parameters) (p : Profile) (α τ : ℝ)
    (hτ : 0 < τ) (hα0 : P.val.2 - 1 ≤ α) (hαs : α < P.val.2 / 2)
    {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) (d : TestData)
    (hd : 0 < d.1 ∧ d.1 < P.val.2 ∧ 0 < d.2.1 ∧ 0 < d.2.2.1) :
    ∃ Cc K₂ : ℝ, 0 ≤ Cc ∧ 0 < K₂ ∧ ∀ C : ℝ, Cc ≤ C → ∀ ell : Scales,
      CompactProfile p →
      Tendsto (fun k : ℕ => (ell ⟨k + 1, Nat.succ_pos k⟩).val) atTop (𝓝 0) →
      (∀ N, PrimitiveRegularity (observationLength (ell N)) d.1 P.val.2 d.2.1
          ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ ∧
        TransportRegularity P (observationLength (ell N))
          ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩
            d.2.2.2.1 d.2.2.2.2 α d.2.2.1) →
      ∀ N : ℕ+, K₂ ≤ (N : ℝ) * (ell N).val → ErrorOneConclusion hρ P p α τ C ell N := by
  by_cases hp : CompactProfile p
  swap
  · exact ⟨0, 1, le_rfl, one_pos, fun C _ ell hp' => absurd hp' hp⟩
  obtain ⟨r0, hr0, hr0h, hsupp0⟩ := id hp
  obtain ⟨T, hT, hTδ⟩ := cltDelta_lt_of_large P (r := r0) (by linarith)
  obtain ⟨hd1, -, hB, hC₀⟩ := hd
  obtain ⟨CV, hCV, hAP⟩ := errorOne_apriori_of hA P τ hτ
  obtain ⟨hη, hητ, hηα, hηs, hτα⟩ := errorOne_exponent P α τ hτ hα0 hαs
  obtain ⟨C₁, C₂, C₃, C₄, hC₁, hC₂, hC₃, hC₄, hfacts⟩ :=
    errorOne_compact_facts hρ P p hp α _ d hα0 hαs hη hηα hηs hd1 hB.le hC₀.le
  refine ⟨(C₁ * C₃ + C₁ * C₄ * (1 + ((d.2.2.2.1 : ℕ) : ℝ)) + C₂ * C₃) +
      4 * CV * (C₁ * C₃ + C₁ * C₄ * (1 + ((d.2.2.2.1 : ℕ) : ℝ)) + C₂ * C₃) ^ 2 +
      2 * Real.sqrt CV * (C₁ * C₃ + C₁ * C₄ * (1 + ((d.2.2.2.1 : ℕ) : ℝ)) + C₂ * C₃),
    max 1 T, by positivity, lt_of_lt_of_le one_pos (le_max_left _ _),
    fun C hCC ell hp' htend hadmN N hN => ?_⟩
  have hK1 : 1 ≤ (N : ℝ) * (ell N).val := (le_max_left _ _).trans hN
  have hKT : T ≤ (N : ℝ) * (ell N).val := (le_max_right _ _).trans hN
  obtain ⟨ψ0, hψ0m, hψ0, hH, hsup, hder⟩ := hfacts ell htend hadmN N hK1
  exact errorOne_conclusion_of_facts hρ P p α τ hτ hα0 hαs ell N hK1 _ hη hητ hτα hηs
    C₁ C₂ C₃ C₄ hC₁ hC₂ hC₃ hC₄ ((d.2.2.2.1 : ℕ)) d.2.2.2.2 ψ0 hψ0m hψ0 hH hsup hder
    CV hCV hAP
    (fun x hx => errorOne_vanish_of_compact hρ P N (ell N) p hr0 hsupp0
      (hTδ N (ell N) hKT) x hx) C hCC

/-- **First error bound in the proof of Theorem 3.** Let `0 < s < 1`, `β > 0` and an admissible
profile `p` with exponent
`α` be given, and let `τ > 0`. Then there are a constant `C` and a threshold `K₀` such that, for
every admissible scale sequence and every particle number `N` with `Nℓ_N ≥ K₀`, the sup bounds of
`q_N` and `q_N'`, the variance bound of `Fluct_N[q_N(ℓ_N⁻¹ ·)]` and the bound of `Error¹_N(u)`
hold (`ErrorOneConclusion`). The only conditional hypothesis is `APrioriConclusion`
(Lemma 5.2). The regularization bounds are those of Lemma 5.1. -/
theorem clt_error1_of_apriori (hA : APrioriConclusion) (P : Parameters) (p : Profile) (α : ℝ)
    (d : TestData) {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) (τ : ℝ) (hτ : 0 < τ) :
    ∃ C K₀ : ℝ, 0 < C ∧ 0 < K₀ ∧
      ∀ ell : Scales, Admissible P p ell α d → ∀ N : ℕ+, K₀ ≤ (N : ℝ) * (ell N).val →
        ErrorOneConclusion hρ P p α τ C ell N := by
  by_cases hdata : (P.val.2 - 1 ≤ α ∧ α < P.val.2 / 2) ∧
      (0 < d.1 ∧ d.1 < P.val.2 ∧ 0 < d.2.1 ∧ 0 < d.2.2.1)
  swap
  · exact ⟨1, 1, one_pos, one_pos, fun ell hadm =>
      absurd ⟨⟨hadm.1, hadm.2.1⟩, hadm.2.2.1, hadm.2.2.2.1, hadm.2.2.2.2.1, hadm.2.2.2.2.2.1⟩ hdata⟩
  obtain ⟨⟨hα0, hαs⟩, hd⟩ := hdata
  obtain ⟨Cm, K₁, hCm, hK₁, hm⟩ := errorOne_macro_final hA P p α τ hτ hα0 hαs hρ d hd
  obtain ⟨Cc, K₂, hCc, hK₂, hc⟩ := errorOne_compact_final hA P p α τ hτ hα0 hαs hρ d hd
  refine ⟨Cm + Cc + 1, max K₁ K₂, by linarith, lt_of_lt_of_le hK₁ (le_max_left _ _),
    fun ell hadm N hN => ?_⟩
  have hK₁N : K₁ ≤ (N : ℝ) * (ell N).val := (le_max_left _ _).trans hN
  have hK₂N : K₂ ≤ (N : ℝ) * (ell N).val := (le_max_right _ _).trans hN
  rcases hadm.2.2.2.2.2.2 with ⟨hone, hprim, hreg⟩ | ⟨hcp, htend, hadmN⟩
  · exact hm (Cm + Cc + 1) (by linarith) ell ⟨hprim, hreg⟩ hone N hK₁N
  · exact hc (Cm + Cc + 1) (by linarith) ell hcp htend hadmN N hK₂N

end Riesz1.Internal

end
end
