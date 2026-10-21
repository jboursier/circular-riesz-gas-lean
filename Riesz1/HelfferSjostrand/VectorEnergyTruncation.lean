/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.VectorEnergyTruncationPos

/-!
# Positive and negative parts in the vector energy space: the identities

The truncation part of Lemma 3.4, in full. For `u ∈ 𝒱_{μ*}` let `u⁺` and `u⁻` be
elements of `𝒱_{μ*}` with the scalar values and weak gradients of the positive and negative parts
(`IsAnchoredPosPart`, `IsAnchoredNegPart`). Existence is `exists_anchoredPosPart` and
`exists_anchoredNegPart`. Then, for every such pair:

* `u⁺ - u⁻ = u` in `𝒱_{μ*}`.
* `∑_i ∇u_i⁺ · ∇u_i⁻ = 0` almost everywhere.
* `q_{μ*}(u⁺, u⁻) ≤ 0`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ContDiff InnerProductSpace

namespace Riesz1

variable {n : ℕ} {c : ℝ}

/-- An element of `L²` of jets is determined, almost everywhere, by its scalar values, gradients
and pair energies. -/
theorem eq_of_jet_components (μ : Measure (AnchoredEuclidean n)) [IsFiniteMeasure μ]
    {Ψ Φ : Lp (AnchoredJetPoint n) 2 μ}
    (hv : ∀ i : Fin n, anchoredJetValue μ i Ψ =ᵐ[μ] anchoredJetValue μ i Φ)
    (hg : ∀ i : Fin n, anchoredJetGrad μ i Ψ =ᵐ[μ] anchoredJetGrad μ i Φ)
    (he : ∀ p : HsPairIndex n.succPNat, anchoredJetEnergy μ p Ψ =ᵐ[μ] anchoredJetEnergy μ p Φ) :
    Ψ = Φ := by
  apply Lp.ext
  have hcomp (Θ : Lp (AnchoredJetPoint n) 2 μ) : ∀ᵐ y ∂μ,
      (∀ i : Fin n, (anchoredJetValue μ i Θ : AnchoredEuclidean n → ℝ) y = jetValueL i (Θ y)) ∧
      (∀ i : Fin n, (anchoredJetGrad μ i Θ : AnchoredEuclidean n → AnchoredEuclidean n) y =
        jetGradL i (Θ y)) ∧
      (∀ p : HsPairIndex n.succPNat, (anchoredJetEnergy μ p Θ : AnchoredEuclidean n → ℝ) y =
        jetEnergyL p (Θ y)) := by
    have h1 : ∀ᵐ y ∂μ, ∀ i : Fin n, (anchoredJetValue μ i Θ : AnchoredEuclidean n → ℝ) y =
        jetValueL i (Θ y) := ae_all_iff.mpr fun i => ContinuousLinearMap.coeFn_compLpL _ _
    have h2 : ∀ᵐ y ∂μ, ∀ i : Fin n,
        (anchoredJetGrad μ i Θ : AnchoredEuclidean n → AnchoredEuclidean n) y = jetGradL i (Θ y) :=
      ae_all_iff.mpr fun i => ContinuousLinearMap.coeFn_compLpL _ _
    have h3 : ∀ᵐ y ∂μ, ∀ p : HsPairIndex n.succPNat,
        (anchoredJetEnergy μ p Θ : AnchoredEuclidean n → ℝ) y = jetEnergyL p (Θ y) :=
      ae_all_iff.mpr fun p => ContinuousLinearMap.coeFn_compLpL _ _
    filter_upwards [h1, h2, h3] with y e1 e2 e3
    exact ⟨e1, e2, e3⟩
  filter_upwards [ae_all_iff.mpr hv, ae_all_iff.mpr hg, ae_all_iff.mpr he, hcomp Ψ, hcomp Φ]
    with y e1 e2 e3 hΨ hΦ
  apply jetPoint_ext
  · intro i
    rw [← hΨ.1 i, ← hΦ.1 i]
    exact e1 i
  · intro i
    rw [← hΨ.2.1 i, ← hΦ.2.1 i]
    exact e2 i
  · intro p
    rw [← hΨ.2.2 p, ← hΦ.2.2 p]
    exact e3 p

/-- The positive part of a real number minus the positive part of its negative is the number. -/
theorem max_sub_max_neg_eq (a : ℝ) : max a 0 - max (-a) 0 = a := by
  rcases le_total 0 a with h | h
  · rw [max_eq_left h, max_eq_right (by linarith : -a ≤ 0)]
    ring
  · rw [max_eq_right h, max_eq_left (by linarith : 0 ≤ -a)]
    ring

/-- The positive part of a real number times the positive part of its negative vanishes. -/
theorem max_mul_max_neg_eq_zero (a : ℝ) : max a 0 * max (-a) 0 = 0 := by
  rcases le_total 0 a with h | h
  · rw [max_eq_right (by linarith : -a ≤ 0), mul_zero]
  · rw [max_eq_right h, zero_mul]

/-- The particles of `Ψ - Φ` are the differences of the particles, almost everywhere. -/
theorem anchoredParticleValue_sub_ae (μ : Measure (AnchoredEuclidean n)) [IsFiniteMeasure μ]
    (Ψ Φ : Lp (AnchoredJetPoint n) 2 μ) (k : Fin (n.succPNat : ℕ)) :
    (anchoredParticleValue μ k (Ψ - Φ) : AnchoredEuclidean n → ℝ) =ᵐ[μ]
      fun y => (anchoredParticleValue μ k Ψ : AnchoredEuclidean n → ℝ) y -
        (anchoredParticleValue μ k Φ : AnchoredEuclidean n → ℝ) y := by
  rw [map_sub]
  filter_upwards [Lp.coeFn_sub (anchoredParticleValue μ k Ψ) (anchoredParticleValue μ k Φ)]
    with y hy
  rw [hy]
  rfl

/-- The positive and negative parts of the scalar values are nonnegative and have vanishing
products, so the particle values of `u⁺` and `u⁻` have the same properties, almost everywhere. -/
theorem particle_sign_ae (μ : Measure (AnchoredEuclidean n)) [IsFiniteMeasure μ]
    (Ψ Φ : Lp (AnchoredJetPoint n) 2 μ)
    (hΨ : ∀ i : Fin n, ∀ᵐ y ∂μ, 0 ≤ (anchoredJetValue μ i Ψ : AnchoredEuclidean n → ℝ) y)
    (hΦ : ∀ i : Fin n, ∀ᵐ y ∂μ, 0 ≤ (anchoredJetValue μ i Φ : AnchoredEuclidean n → ℝ) y)
    (hprod : ∀ i : Fin n, ∀ᵐ y ∂μ, (anchoredJetValue μ i Ψ : AnchoredEuclidean n → ℝ) y *
      (anchoredJetValue μ i Φ : AnchoredEuclidean n → ℝ) y = 0)
    (k : Fin (n.succPNat : ℕ)) :
    ∀ᵐ y ∂μ, 0 ≤ (anchoredParticleValue μ k Ψ : AnchoredEuclidean n → ℝ) y ∧
      0 ≤ (anchoredParticleValue μ k Φ : AnchoredEuclidean n → ℝ) y ∧
      (anchoredParticleValue μ k Ψ : AnchoredEuclidean n → ℝ) y *
        (anchoredParticleValue μ k Φ : AnchoredEuclidean n → ℝ) y = 0 := by
  induction k using Fin.cases with
  | zero =>
    filter_upwards [anchoredParticleValue_zero_ae μ Ψ, anchoredParticleValue_zero_ae μ Φ]
      with y h1 h2
    exact ⟨le_of_eq (h1.trans (Pi.zero_apply y)).symm, le_of_eq (h2.trans (Pi.zero_apply y)).symm,
      mul_eq_zero.mpr (Or.inl (h1.trans (Pi.zero_apply y)))⟩
  | succ j =>
    filter_upwards [anchoredParticleValue_succ_ae μ Ψ j, anchoredParticleValue_succ_ae μ Φ j,
      hΨ j, hΦ j, hprod j] with y h1 h2 h3 h4 h5
    rw [h1, h2]
    exact ⟨h3, h4, h5⟩

/-- The product of the energy weights is nonnegative times a product of differences: the
pair energies of `u⁺` and `u⁻` have nonpositive product. -/
theorem energy_product_nonpos (w a1 a2 b1 b2 : ℝ) (ha1 : 0 ≤ a1) (ha2 : 0 ≤ a2) (hb1 : 0 ≤ b1)
    (hb2 : 0 ≤ b2) (hab1 : a1 * b1 = 0) (hab2 : a2 * b2 = 0) :
    (w * (a2 - a1)) * (w * (b2 - b1)) ≤ 0 := by
  have h : (a2 - a1) * (b2 - b1) ≤ 0 := by
    nlinarith [mul_nonneg ha2 hb1, mul_nonneg ha1 hb2]
  have hw : 0 ≤ w * w := mul_self_nonneg w
  calc (w * (a2 - a1)) * (w * (b2 - b1)) = (w * w) * ((a2 - a1) * (b2 - b1)) := by ring
    _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hw h

/-- The gradient pairing of `u⁺` and `u⁻` vanishes almost everywhere, coordinatewise. -/
theorem inner_grad_positive_negative_ae (χ : HsPairPotentials n.succPNat c)
    [IsFiniteMeasure (anchoredMeasureE χ)] (u up um : AnchoredVectorSobolev χ (anchoredMeasureE χ))
    (hup : IsAnchoredPosPart χ u up) (hum : IsAnchoredNegPart χ u um) :
    ∀ᵐ y ∂(anchoredMeasureE χ), ∀ i : Fin n,
      inner ℝ (vecGrad χ i up y) (vecGrad χ i um y) = 0 := by
  rw [ae_all_iff]
  intro i
  filter_upwards [hup.2 i, hum.2 i] with y h1 h2
  rw [h1, h2]
  by_cases hp : 0 < vecValue χ i u y
  · rw [Set.indicator_of_notMem (show y ∉ {y' : AnchoredEuclidean n | vecValue χ i u y' < 0} from
      not_lt.mpr hp.le), inner_zero_right]
  · by_cases hn : vecValue χ i u y < 0
    · rw [Set.indicator_of_notMem (show y ∉ {y' : AnchoredEuclidean n | 0 < vecValue χ i u y'}
        from not_lt.mpr hn.le), inner_zero_left]
    · rw [Set.indicator_of_notMem (show y ∉ {y' : AnchoredEuclidean n | 0 < vecValue χ i u y'}
        from hp), inner_zero_left]

/-- The pair energy coordinates of an element of `L²` of jets, as a vector, agree with the
coordinates of the individual energies, almost everywhere. -/
theorem anchoredJetEnergyVec_apply_ae (μ : Measure (AnchoredEuclidean n)) [IsFiniteMeasure μ]
    (Ψ : Lp (AnchoredJetPoint n) 2 μ) (p : HsPairIndex n.succPNat) :
    ∀ᵐ y ∂μ, (anchoredJetEnergyVec μ Ψ : AnchoredEuclidean n → EuclideanSpace ℝ
      (HsPairIndex n.succPNat)) y p = (anchoredJetEnergy μ p Ψ : AnchoredEuclidean n → ℝ) y := by
  filter_upwards [ContinuousLinearMap.coeFn_compLpL jetEnergyVecL (μ := μ) Ψ,
    ContinuousLinearMap.coeFn_compLpL (jetEnergyL p) (μ := μ) Ψ] with y h1 h2
  unfold anchoredJetEnergyVec anchoredJetEnergy
  rw [h1, h2]
  rfl

/-- The scalar values of `u⁺` are nonnegative, almost everywhere. -/
theorem vecValue_pos_ae (χ : HsPairPotentials n.succPNat c)
    [IsFiniteMeasure (anchoredMeasureE χ)]
    (u up : AnchoredVectorSobolev χ (anchoredMeasureE χ)) (hup : IsAnchoredPosPart χ u up)
    (i : Fin n) : ∀ᵐ y ∂(anchoredMeasureE χ), 0 ≤ vecValue χ i up y := by
  filter_upwards [hup.1 i] with y hy
  rw [hy]
  exact le_max_right _ _

/-- The scalar values of `u⁻` are nonnegative, almost everywhere. -/
theorem vecValue_neg_ae (χ : HsPairPotentials n.succPNat c)
    [IsFiniteMeasure (anchoredMeasureE χ)]
    (u um : AnchoredVectorSobolev χ (anchoredMeasureE χ)) (hum : IsAnchoredNegPart χ u um)
    (i : Fin n) : ∀ᵐ y ∂(anchoredMeasureE χ), 0 ≤ vecValue χ i um y := by
  filter_upwards [hum.1 i] with y hy
  rw [hy]
  exact le_max_right _ _

/-- The scalar values of `u⁺` and `u⁻` have vanishing products, almost everywhere. -/
theorem vecValue_mul_ae (χ : HsPairPotentials n.succPNat c)
    [IsFiniteMeasure (anchoredMeasureE χ)]
    (u up um : AnchoredVectorSobolev χ (anchoredMeasureE χ)) (hup : IsAnchoredPosPart χ u up)
    (hum : IsAnchoredNegPart χ u um) (i : Fin n) :
    ∀ᵐ y ∂(anchoredMeasureE χ), vecValue χ i up y * vecValue χ i um y = 0 := by
  filter_upwards [hup.1 i, hum.1 i] with y h1 h2
  rw [h1, h2]
  exact max_mul_max_neg_eq_zero _

/-- The energy of `u⁺` against the energy of `u⁻` is nonpositive, almost everywhere, pair by pair.
The sign facts are supplied as hypotheses, so that this step only combines the energy identity
with the pure real inequality `energy_product_nonpos`. -/
theorem anchoredPart_energy_term_ae (χ : HsPairPotentials n.succPNat c)
    [IsFiniteMeasure (anchoredMeasureE χ)] (up um : AnchoredVectorSobolev χ (anchoredMeasureE χ))
    (hΨ : ∀ i : Fin n, ∀ᵐ y ∂(anchoredMeasureE χ), 0 ≤ vecValue χ i up y)
    (hΦ : ∀ i : Fin n, ∀ᵐ y ∂(anchoredMeasureE χ), 0 ≤ vecValue χ i um y)
    (hprod : ∀ i : Fin n, ∀ᵐ y ∂(anchoredMeasureE χ), vecValue χ i up y * vecValue χ i um y = 0)
    (p : HsPairIndex n.succPNat) :
    ∀ᵐ y ∂(anchoredMeasureE χ), (anchoredJetEnergy (anchoredMeasureE χ) p
        (up : Lp (AnchoredJetPoint n) 2 (anchoredMeasureE χ)) : AnchoredEuclidean n → ℝ) y *
      (anchoredJetEnergy (anchoredMeasureE χ) p
        (um : Lp (AnchoredJetPoint n) 2 (anchoredMeasureE χ)) : AnchoredEuclidean n → ℝ) y ≤ 0 := by
  filter_upwards [anchoredVectorSobolev_energy_ae χ (anchoredMeasureE χ) up p,
    anchoredVectorSobolev_energy_ae χ (anchoredMeasureE χ) um p,
    particle_sign_ae (anchoredMeasureE χ) (up : Lp (AnchoredJetPoint n) 2 (anchoredMeasureE χ))
      (um : Lp (AnchoredJetPoint n) 2 (anchoredMeasureE χ)) hΨ hΦ hprod p.1.1,
    particle_sign_ae (anchoredMeasureE χ) (up : Lp (AnchoredJetPoint n) 2 (anchoredMeasureE χ))
      (um : Lp (AnchoredJetPoint n) 2 (anchoredMeasureE χ)) hΨ hΦ hprod p.1.2] with y h1 h2 s1 s2
  exact (congrArg₂ (· * ·) h1 h2).trans_le
    (energy_product_nonpos _ _ _ _ _ s1.1 s2.1 s1.2.1 s2.2.1 s1.2.2 s2.2.2)

/-- The form `q_{μ*}(u⁺, u⁻)` is nonpositive. The gradient part vanishes because the gradients of
`u⁺` and `u⁻` have disjoint supports, and the energy part is nonpositive pair by pair. -/
theorem anchoredPart_form_nonpos (χ : HsPairPotentials n.succPNat c) (hc : 0 < c)
    [IsFiniteMeasure (anchoredMeasureE χ)] (u up um : AnchoredVectorSobolev χ (anchoredMeasureE χ))
    (hup : IsAnchoredPosPart χ u up) (hum : IsAnchoredNegPart χ u um) :
    anchoredVectorSobolevForm (anchoredMeasureE χ)
      (up : Lp (AnchoredJetPoint n) 2 (anchoredMeasureE χ))
      (um : Lp (AnchoredJetPoint n) 2 (anchoredMeasureE χ)) ≤ 0 := by
  have := isProbabilityMeasure_anchoredMeasureE χ hc
  unfold anchoredVectorSobolevForm
  have hg : ∀ i : Fin n, inner ℝ (anchoredJetGrad (anchoredMeasureE χ) i
      (up : Lp (AnchoredJetPoint n) 2 (anchoredMeasureE χ)))
      (anchoredJetGrad (anchoredMeasureE χ) i (um : Lp (AnchoredJetPoint n) 2 _)) = 0 := by
    intro i
    rw [L2.inner_def]
    apply integral_eq_zero_of_ae
    filter_upwards [inner_grad_positive_negative_ae χ u up um hup hum] with y hy
    exact hy i
  have he : inner ℝ (anchoredJetEnergyVec (anchoredMeasureE χ)
      (up : Lp (AnchoredJetPoint n) 2 (anchoredMeasureE χ)))
      (anchoredJetEnergyVec (anchoredMeasureE χ) (um : Lp (AnchoredJetPoint n) 2 _)) ≤ 0 := by
    rw [L2.inner_def]
    apply integral_nonpos_of_ae
    have hall : ∀ᵐ y ∂(anchoredMeasureE χ), ∀ p : HsPairIndex n.succPNat,
        anchoredJetEnergy (anchoredMeasureE χ) p (up : Lp (AnchoredJetPoint n) 2 _) y *
          anchoredJetEnergy (anchoredMeasureE χ) p (um : Lp (AnchoredJetPoint n) 2 _) y ≤ 0 :=
      ae_all_iff.mpr fun p => anchoredPart_energy_term_ae χ up um
        (fun i => vecValue_pos_ae χ u up hup i) (fun i => vecValue_neg_ae χ u um hum i)
        (fun i => vecValue_mul_ae χ u up um hup hum i) p
    have hcoord : ∀ᵐ y ∂(anchoredMeasureE χ), ∀ p : HsPairIndex n.succPNat,
        (anchoredJetEnergyVec (anchoredMeasureE χ) (up : Lp (AnchoredJetPoint n) 2 _) y) p =
          (anchoredJetEnergy (anchoredMeasureE χ) p (up : Lp (AnchoredJetPoint n) 2 _)) y ∧
        (anchoredJetEnergyVec (anchoredMeasureE χ) (um : Lp (AnchoredJetPoint n) 2 _) y) p =
          (anchoredJetEnergy (anchoredMeasureE χ) p (um : Lp (AnchoredJetPoint n) 2 _)) y := by
      have h1 : ∀ᵐ y ∂(anchoredMeasureE χ), ∀ p : HsPairIndex n.succPNat,
          (anchoredJetEnergyVec (anchoredMeasureE χ) (up : Lp (AnchoredJetPoint n) 2 _) y) p =
            (anchoredJetEnergy (anchoredMeasureE χ) p (up : Lp (AnchoredJetPoint n) 2 _)) y :=
        ae_all_iff.mpr fun p => anchoredJetEnergyVec_apply_ae _ _ p
      have h2 : ∀ᵐ y ∂(anchoredMeasureE χ), ∀ p : HsPairIndex n.succPNat,
          (anchoredJetEnergyVec (anchoredMeasureE χ) (um : Lp (AnchoredJetPoint n) 2 _) y) p =
            (anchoredJetEnergy (anchoredMeasureE χ) p (um : Lp (AnchoredJetPoint n) 2 _)) y :=
        ae_all_iff.mpr fun p => anchoredJetEnergyVec_apply_ae _ _ p
      filter_upwards [h1, h2] with y e1 e2
      exact fun p => ⟨e1 p, e2 p⟩
    filter_upwards [hall, hcoord] with y hy hc'
    rw [PiLp.inner_apply]
    apply Finset.sum_nonpos
    intro p _
    rw [RCLike.inner_apply, conj_trivial, (hc' p).1, (hc' p).2, mul_comm]
    exact hy p
  rw [Finset.sum_eq_zero fun i _ => hg i, zero_add]
  exact he

/-- `u⁺ - u⁻ = u` in `𝒱_{μ*}`, for the positive and negative parts. The scalar values agree
because `max a 0 - max (-a) 0 = a`. The gradients agree because `∇u = 0` almost everywhere on
`{u = 0}`, by `IsAnchoredH1.gradient_eq_zero_on_level`. The energies agree by the energy identity
applied to `u⁺`, `u⁻` and `u`, since the particle values of `u⁺ - u⁻` are those of `u`. -/
theorem anchoredPart_sub_eq (χ : HsPairPotentials n.succPNat c) (hc : 0 < c)
    [IsFiniteMeasure (anchoredMeasureE χ)] (u up um : AnchoredVectorSobolev χ (anchoredMeasureE χ))
    (hup : IsAnchoredPosPart χ u up) (hum : IsAnchoredNegPart χ u um) : up - um = u := by
  have := isProbabilityMeasure_anchoredMeasureE χ hc
  obtain ⟨hup1, hup2⟩ := hup
  obtain ⟨hum1, hum2⟩ := hum
  have hB : ∀ i : Fin n, IsAnchoredH1 χ (vecValue χ i u) (vecGrad χ i u) := fun i =>
    isWeightedH1_anchoredVectorSobolev χ (anchoredMeasureE χ) u i
  have hL : ∀ i : Fin n, ∀ᵐ y ∂(anchoredMeasureE χ), vecValue χ i u y = 0 → vecGrad χ i u y = 0 :=
    fun i => IsAnchoredH1.gradient_eq_zero_on_level χ hc (hB i) 0
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : Lp (AnchoredJetPoint n) 2 (anchoredMeasureE χ),
      Ψ = (up : Lp (AnchoredJetPoint n) 2 (anchoredMeasureE χ)) -
        (um : Lp (AnchoredJetPoint n) 2 (anchoredMeasureE χ)) := ⟨_, rfl⟩
  -- The scalar values of `Ψ` are those of `u`.
  have hv : ∀ i : Fin n, anchoredJetValue (anchoredMeasureE χ) i Ψ =ᵐ[anchoredMeasureE χ]
      anchoredJetValue (anchoredMeasureE χ) i (u : Lp (AnchoredJetPoint n) 2 _) := by
    intro i
    rw [hΨ, map_sub]
    filter_upwards [Lp.coeFn_sub (anchoredJetValue (anchoredMeasureE χ) i
      (up : Lp (AnchoredJetPoint n) 2 _)) (anchoredJetValue (anchoredMeasureE χ) i
      (um : Lp (AnchoredJetPoint n) 2 _)), hup1 i, hum1 i] with y h1 h2 h3
    rw [h1, Pi.sub_apply]
    have h2' : (anchoredJetValue (anchoredMeasureE χ) i (up : Lp (AnchoredJetPoint n) 2 _)
        : AnchoredEuclidean n → ℝ) y = max (vecValue χ i u y) 0 := h2
    have h3' : (anchoredJetValue (anchoredMeasureE χ) i (um : Lp (AnchoredJetPoint n) 2 _)
        : AnchoredEuclidean n → ℝ) y = max (-(vecValue χ i u y)) 0 := h3
    rw [h2', h3']
    exact max_sub_max_neg_eq _
  -- The gradients of `Ψ` are those of `u`: on `{u_i > 0}` and `{u_i < 0}` by the formulas, and on
  -- `{u_i = 0}` because the gradient of `u_i` vanishes there.
  have hg : ∀ i : Fin n, anchoredJetGrad (anchoredMeasureE χ) i Ψ =ᵐ[anchoredMeasureE χ]
      anchoredJetGrad (anchoredMeasureE χ) i (u : Lp (AnchoredJetPoint n) 2 _) := by
    intro i
    rw [hΨ, map_sub]
    filter_upwards [Lp.coeFn_sub (anchoredJetGrad (anchoredMeasureE χ) i
      (up : Lp (AnchoredJetPoint n) 2 _)) (anchoredJetGrad (anchoredMeasureE χ) i
      (um : Lp (AnchoredJetPoint n) 2 _)), hup2 i, hum2 i, hL i] with y h1 h2 h3 h4
    rw [h1, Pi.sub_apply]
    have h2' : (anchoredJetGrad (anchoredMeasureE χ) i (up : Lp (AnchoredJetPoint n) 2 _)
        : AnchoredEuclidean n → AnchoredEuclidean n) y =
        Set.indicator {y' : AnchoredEuclidean n | 0 < vecValue χ i u y'} (vecGrad χ i u) y := h2
    have h3' : (anchoredJetGrad (anchoredMeasureE χ) i (um : Lp (AnchoredJetPoint n) 2 _)
        : AnchoredEuclidean n → AnchoredEuclidean n) y =
        Set.indicator {y' : AnchoredEuclidean n | vecValue χ i u y' < 0}
          (fun y' => -(vecGrad χ i u y')) y := h3
    rw [h2', h3']
    by_cases hp : 0 < vecValue χ i u y
    · rw [Set.indicator_of_mem (show y ∈ {y' : AnchoredEuclidean n | 0 < vecValue χ i u y'} from hp),
        Set.indicator_of_notMem (show y ∉ {y' : AnchoredEuclidean n | vecValue χ i u y' < 0} from
          not_lt.mpr hp.le), sub_zero]
    · by_cases hn : vecValue χ i u y < 0
      · rw [Set.indicator_of_notMem (show y ∉ {y' : AnchoredEuclidean n | 0 < vecValue χ i u y'}
          from not_lt.mpr hn.le), Set.indicator_of_mem
          (show y ∈ {y' : AnchoredEuclidean n | vecValue χ i u y' < 0} from hn), zero_sub, neg_neg]
      · have h0 : vecValue χ i u y = 0 := le_antisymm (not_lt.mp hp) (not_lt.mp hn)
        have h4' : (anchoredJetGrad (anchoredMeasureE χ) i (u : Lp (AnchoredJetPoint n) 2 _) :
            AnchoredEuclidean n → AnchoredEuclidean n) y = 0 := h4 h0
        rw [Set.indicator_of_notMem (show y ∉ {y' : AnchoredEuclidean n | 0 < vecValue χ i u y'}
          from hp), Set.indicator_of_notMem (show y ∉ {y' : AnchoredEuclidean n |
          vecValue χ i u y' < 0} from hn), h4', sub_self]
  -- The energies of `Ψ` are those of `u`, by the energy identity and the particle relations.
  have he : ∀ p : HsPairIndex n.succPNat, anchoredJetEnergy (anchoredMeasureE χ) p Ψ =ᵐ[anchoredMeasureE χ]
      anchoredJetEnergy (anchoredMeasureE χ) p (u : Lp (AnchoredJetPoint n) 2 _) := by
    intro p
    have hpart : ∀ k : Fin (n.succPNat : ℕ), ∀ᵐ y ∂(anchoredMeasureE χ),
        (anchoredParticleValue (anchoredMeasureE χ) k Ψ : AnchoredEuclidean n → ℝ) y =
          (anchoredParticleValue (anchoredMeasureE χ) k (u : Lp (AnchoredJetPoint n) 2 _) :
            AnchoredEuclidean n → ℝ) y := fun k =>
      anchoredParticleValue_ae_of_value_ae (anchoredMeasureE χ) Ψ _ hv k
    have hsub : ∀ k : Fin (n.succPNat : ℕ), ∀ᵐ y ∂(anchoredMeasureE χ),
        (anchoredParticleValue (anchoredMeasureE χ) k Ψ : AnchoredEuclidean n → ℝ) y =
          (anchoredParticleValue (anchoredMeasureE χ) k (up : Lp (AnchoredJetPoint n) 2 _) :
            AnchoredEuclidean n → ℝ) y -
          (anchoredParticleValue (anchoredMeasureE χ) k (um : Lp (AnchoredJetPoint n) 2 _) :
            AnchoredEuclidean n → ℝ) y := fun k => by
      rw [hΨ]
      exact anchoredParticleValue_sub_ae (anchoredMeasureE χ) _ _ k
    rw [hΨ, map_sub]
    filter_upwards [Lp.coeFn_sub (anchoredJetEnergy (anchoredMeasureE χ) p
      (up : Lp (AnchoredJetPoint n) 2 _)) (anchoredJetEnergy (anchoredMeasureE χ) p
      (um : Lp (AnchoredJetPoint n) 2 _)), anchoredVectorSobolev_energy_ae χ (anchoredMeasureE χ) up p,
      anchoredVectorSobolev_energy_ae χ (anchoredMeasureE χ) um p,
      anchoredVectorSobolev_energy_ae χ (anchoredMeasureE χ) u p, hsub p.1.2, hsub p.1.1,
      hpart p.1.2, hpart p.1.1] with y h1 h2 h3 h4 hs2 hs1 hp2 hp1
    rw [h1, Pi.sub_apply, h2, h3, h4]
    have d2 : (anchoredParticleValue (anchoredMeasureE χ) p.1.2 (up : Lp (AnchoredJetPoint n) 2 _) :
        AnchoredEuclidean n → ℝ) y - (anchoredParticleValue (anchoredMeasureE χ) p.1.2
        (um : Lp (AnchoredJetPoint n) 2 _) : AnchoredEuclidean n → ℝ) y =
        (anchoredParticleValue (anchoredMeasureE χ) p.1.2 (u : Lp (AnchoredJetPoint n) 2 _) :
          AnchoredEuclidean n → ℝ) y := by
      rw [← hs2, hp2]
    have d1 : (anchoredParticleValue (anchoredMeasureE χ) p.1.1 (up : Lp (AnchoredJetPoint n) 2 _) :
        AnchoredEuclidean n → ℝ) y - (anchoredParticleValue (anchoredMeasureE χ) p.1.1
        (um : Lp (AnchoredJetPoint n) 2 _) : AnchoredEuclidean n → ℝ) y =
        (anchoredParticleValue (anchoredMeasureE χ) p.1.1 (u : Lp (AnchoredJetPoint n) 2 _) :
          AnchoredEuclidean n → ℝ) y := by
      rw [← hs1, hp1]
    linear_combination (hsEnergyWeight χ p (anchorLift n y)) * (d2 - d1)
  refine Subtype.ext ?_
  rw [Submodule.coe_sub, ← hΨ]
  exact eq_of_jet_components (anchoredMeasureE χ) hv hg he

/-- The truncation part of Lemma 3.4. For `u ∈ 𝒱_{μ*}` the positive part `u⁺` and the
negative part `u⁻` exist in `𝒱_{μ*}`. For every such pair, `u = u⁺ - u⁻`,
`∑_i ∇u_i⁺ · ∇u_i⁻ = 0` almost everywhere, and `q_{μ*}(u⁺, u⁻) ≤ 0`. -/
theorem anchoredVectorSobolev_truncation (χ : HsPairPotentials n.succPNat c) (hc : 0 < c)
    [IsFiniteMeasure (anchoredMeasureE χ)] (u : AnchoredVectorSobolev χ (anchoredMeasureE χ)) :
    (∃ up : AnchoredVectorSobolev χ (anchoredMeasureE χ), IsAnchoredPosPart χ u up) ∧
    (∃ um : AnchoredVectorSobolev χ (anchoredMeasureE χ), IsAnchoredNegPart χ u um) ∧
    ∀ up um : AnchoredVectorSobolev χ (anchoredMeasureE χ),
      IsAnchoredPosPart χ u up → IsAnchoredNegPart χ u um →
        up - um = u ∧
        (∀ᵐ y ∂(anchoredMeasureE χ), ∑ i : Fin n,
          inner ℝ (vecGrad χ i up y) (vecGrad χ i um y) = 0) ∧
        anchoredVectorSobolevForm (anchoredMeasureE χ)
          (up : Lp (AnchoredJetPoint n) 2 (anchoredMeasureE χ))
          (um : Lp (AnchoredJetPoint n) 2 (anchoredMeasureE χ)) ≤ 0 := by
  refine ⟨exists_anchoredPosPart χ hc u, exists_anchoredNegPart χ hc u, fun up um hup hum => ?_⟩
  refine ⟨anchoredPart_sub_eq χ hc u up um hup hum, ?_,
    anchoredPart_form_nonpos χ hc u up um hup hum⟩
  filter_upwards [inner_grad_positive_negative_ae χ u up um hup hum] with y hy
  exact Finset.sum_eq_zero fun i _ => hy i

end Riesz1
