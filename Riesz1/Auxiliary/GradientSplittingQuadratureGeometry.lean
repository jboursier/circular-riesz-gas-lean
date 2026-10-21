/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.GradientSplittingDisplacementEvent
public import Riesz1.Auxiliary.GradientSplittingWindowSupport
public import Riesz1.Auxiliary.GradientSplittingCellsDefs

/-!
# Geometry of partial-window quadrature

The quadrature part of Lemma 5.7. The strip endpoints must be compared in
physical coordinates: they are near `±M/N`, independently of the position of `x_i`.
This module derives the anchor error from the event, bounds the background interval, and
locates both strips outside the support once the relative anchor error is small.
-/

@[expose] public section

open Set Filter Topology
open scoped ContDiff

namespace Riesz1

noncomputable section

/-- The event and the anchor control the error of every partial-window label. -/
lemma gradPartial_anchor_error {s γ ε ℓ : ℝ} {N : ℕ+} {X : Fin (N : ℕ) → ℝ}
    (hs : 0 < s) (hP : GradPartial N ℓ γ) (hX : gradEvent s γ ε N ℓ X)
    (hanchor : |(N : ℝ) * gradLift N X 0| ≤ ((N : ℝ) * ℓ) ^ ε)
    {i : ℤ} (hi : i ∈ gradLabels N ℓ γ) :
    |(N : ℝ) * gradLift N X i - (i : ℝ)| ≤
      ((N : ℝ) * ℓ) ^ ε * (1 + |(i : ℝ)| ^ (s / 2)) := by
  have hi' := (mem_gradLabels_partial hP i).mp hi
  have hn : (0 : ℤ) ≤ ⌊gradM N ℓ γ⌋ := by omega
  have hzero : (0 : ℤ) ∈ gradLabels N ℓ γ :=
    (mem_gradLabels_partial hP 0).mpr (by omega)
  by_cases hi0 : i = 0
  · subst i
    simpa [Real.zero_rpow (by linarith : s / 2 ≠ 0)] using hanchor
  · have he := gradSep_event_bound hX hzero hi hi0
    have hk : gradPathIncr N ℓ γ 0 i = i := by simp [gradPathIncr, hP]
    have hr : gradSep N ℓ γ X 0 i = gradLift N X i - gradLift N X 0 := by
      simp [gradSep, hk]
    rw [hk, hr] at he
    calc |(N : ℝ) * gradLift N X i - (i : ℝ)|
        = |((N : ℝ) * (gradLift N X i - gradLift N X 0) - (i : ℝ))
            + (N : ℝ) * gradLift N X 0| := by congr 1; ring
      _ ≤ |(N : ℝ) * (gradLift N X i - gradLift N X 0) - (i : ℝ)|
            + |(N : ℝ) * gradLift N X 0| := abs_add_le _ _
      _ ≤ ((N : ℝ) * ℓ) ^ ε * |(i : ℝ)| ^ (s / 2) + ((N : ℝ) * ℓ) ^ ε :=
        add_le_add he hanchor
      _ = _ := by ring

/-- Both contributions to the anchor error are bounded by `M = K^γ`. -/
lemma gradPartial_scale_error_le {s γ ε K r : ℝ} (hs0 : 0 ≤ s)
    (hγ : 0 ≤ γ) (hε : ε ≤ γ * (1 - s / 2)) (hK : 1 ≤ K)
    (hr0 : 0 ≤ r) (hr : r ≤ K ^ γ) :
    K ^ ε * (1 + r ^ (s / 2)) ≤ 2 * K ^ γ := by
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have heγ : ε ≤ γ := by nlinarith
  have h1 : K ^ ε ≤ K ^ γ := Real.rpow_le_rpow_of_exponent_le hK heγ
  have h2 : K ^ ε * r ^ (s / 2) ≤ K ^ γ := by
    calc K ^ ε * r ^ (s / 2)
        ≤ K ^ ε * (K ^ γ) ^ (s / 2) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hr0 hr (by linarith))
            (Real.rpow_nonneg hK0.le _)
      _ = K ^ (ε + γ * (s / 2)) := by
        rw [← Real.rpow_mul hK0.le, ← Real.rpow_add hK0]
      _ ≤ K ^ γ := Real.rpow_le_rpow_of_exponent_le hK (by nlinarith)
  nlinarith

/-- The absolute lift bound needed for every background and strip integral, for all `K ≥ 1`. -/
lemma gradPartial_anchor_lift_bound {s γ ε ℓ : ℝ} {N : ℕ+} {X : Fin (N : ℕ) → ℝ}
    (hs0 : 0 < s) (hγ : 0 ≤ γ) (hε : ε ≤ γ * (1 - s / 2))
    (hK : 1 ≤ (N : ℝ) * ℓ) (hP : GradPartial N ℓ γ) (hX : gradEvent s γ ε N ℓ X)
    (hanchor : |(N : ℝ) * gradLift N X 0| ≤ ((N : ℝ) * ℓ) ^ ε)
    {i : ℤ} (hi : i ∈ gradLabels N ℓ γ) :
    |(N : ℝ) * gradLift N X i| ≤ 3 * gradM N ℓ γ := by
  have he := gradPartial_anchor_error hs0 hP hX hanchor hi
  have hi' := (mem_gradLabels_partial hP i).mp hi
  have hir : |(i : ℝ)| ≤ (⌊gradM N ℓ γ⌋ : ℝ) := by
    rw [← Int.cast_abs]
    exact_mod_cast (abs_le.mpr ⟨by omega, hi'.2⟩)
  have hiM := hir.trans (Int.floor_le _)
  have hscale := gradPartial_scale_error_le hs0.le hγ hε hK (abs_nonneg _) hiM
  have htri := abs_add_le ((N : ℝ) * gradLift N X i - (i : ℝ)) (i : ℝ)
  rw [sub_add_cancel] at htri
  change _ ≤ 3 * ((N : ℝ) * ℓ) ^ γ
  change |(i : ℝ)| ≤ ((N : ℝ) * ℓ) ^ γ at hiM
  linarith

/-- All points of the partial background interval stay within the kernel range `|v| < N/2`. -/
lemma gradPartial_background_range {N : ℕ+} {ℓ γ x : ℝ} (hP : GradPartial N ℓ γ)
    (hx : |(N : ℝ) * x| ≤ 3 * gradM N ℓ γ) {v : ℝ}
    (hv : v ∈ Icc (-gradM N ℓ γ - (N : ℝ) * x) (gradM N ℓ γ - (N : ℝ) * x)) :
    |v| ≤ 4 * gradM N ℓ γ ∧ |v| < (N : ℝ) / 2 := by
  have hv' : |v + (N : ℝ) * x| ≤ gradM N ℓ γ := by
    rw [abs_le]
    constructor <;> linarith [hv.1, hv.2]
  have ht := abs_sub (v + (N : ℝ) * x) ((N : ℝ) * x)
  rw [add_sub_cancel_right] at ht
  constructor <;> linarith [show gradM N ℓ γ < (N : ℝ) / 8 from hP]

/-- The strip length is bounded by the floor error plus the anchor error. -/
lemma gradPartial_strip_length {M u : ℝ} (i : ℤ) :
    |(-M - u) - (-(⌊M⌋ : ℝ) - (i : ℝ) - 1 / 2)| ≤ 1 + |u - (i : ℝ)| ∧
      |(M - u) - ((⌊M⌋ : ℝ) - (i : ℝ) + 1 / 2)| ≤ 1 + |u - (i : ℝ)| := by
  have hf := Int.floor_le M
  have hf' := Int.lt_floor_add_one M
  have he : |M - (⌊M⌋ : ℝ) - 1 / 2| ≤ 1 / 2 := by
    rw [abs_le]; constructor <;> linarith
  constructor
  · calc _ = |-(M - (⌊M⌋ : ℝ) - 1 / 2) - (u - (i : ℝ))| := by congr 1; ring
      _ ≤ |-(M - (⌊M⌋ : ℝ) - 1 / 2)| + |u - (i : ℝ)| := abs_sub _ _
      _ ≤ _ := by rw [abs_neg]; linarith
  · calc _ = |(M - (⌊M⌋ : ℝ) - 1 / 2) - (u - (i : ℝ))| := by congr 1; ring
      _ ≤ |M - (⌊M⌋ : ℝ) - 1 / 2| + |u - (i : ℝ)| := abs_sub _ _
      _ ≤ _ := by linarith

/-- In physical microscopic coordinates, every strip point is close to one of `±M`.
The statement includes labels at the edges of the window. -/
lemma gradPartial_strip_location {M u v : ℝ} (hM : 0 ≤ M) (i : ℤ)
    (hv : v ∈ uIcc (-M - u) (-(⌊M⌋ : ℝ) - (i : ℝ) - 1 / 2) ∨
      v ∈ uIcc (M - u) ((⌊M⌋ : ℝ) - (i : ℝ) + 1 / 2)) :
    M - (1 + |u - (i : ℝ)|) ≤ |u + v| ∧
      |u + v| ≤ M + (1 + |u - (i : ℝ)|) := by
  have hl := gradPartial_strip_length (M := M) (u := u) i
  have herr : |u + v - (-M)| ≤ 1 + |u - (i : ℝ)| ∨
      |u + v - M| ≤ 1 + |u - (i : ℝ)| := by
    rcases hv with hv | hv
    · left
      rcases (mem_uIcc.mp hv) with hv | hv
      all_goals
        have hb := abs_le.mp hl.1
        rw [abs_le]
        constructor <;> linarith [hv.1, hv.2]
    · right
      rcases (mem_uIcc.mp hv) with hv | hv
      all_goals
        have hb := abs_le.mp hl.2
        rw [abs_le]
        constructor <;> linarith [hv.1, hv.2]
  rcases herr with he | he
  · have he' := abs_le.mp he
    constructor
    · linarith [neg_le_abs (u + v)]
    · rw [abs_le]; constructor <;> linarith [abs_nonneg (u - (i : ℝ))]
  · have he' := abs_le.mp he
    constructor
    · linarith [le_abs_self (u + v)]
    · rw [abs_le]; constructor <;> linarith [abs_nonneg (u - (i : ℝ))]

/-- A uniform threshold after which the floor and anchor errors are less than half the window.
It depends only on `s, γ, ε`. -/
lemma gradPartial_small_relative_error {s γ ε : ℝ} (hs : 0 ≤ s) (hγ : 0 ≤ γ)
    (hε0 : 0 ≤ ε) (hε : ε < γ * (1 - s / 2)) :
    ∃ K₀ : ℝ, 1 ≤ K₀ ∧ ∀ K : ℝ, K₀ ≤ K →
      1 + K ^ ε * (1 + (K ^ γ) ^ (s / 2)) ≤ K ^ γ / 2 := by
  let p := ε + γ * (s / 2)
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have hd : 0 < γ - p := by dsimp [p]; nlinarith
  obtain ⟨L, hL⟩ := eventually_atTop.1
    ((tendsto_rpow_atTop hd).eventually (eventually_ge_atTop (6 : ℝ)))
  refine ⟨max 1 L, le_max_left _ _, fun K hK => ?_⟩
  have hK1 : 1 ≤ K := (le_max_left _ _).trans hK
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK1
  have hpow := hL K ((le_max_right _ _).trans hK)
  have h1 : 1 ≤ K ^ p := Real.one_le_rpow hK1 hp
  have he : K ^ ε ≤ K ^ p := Real.rpow_le_rpow_of_exponent_le hK1
    (by dsimp [p]; nlinarith [mul_nonneg hγ hs])
  have hprod : K ^ ε * (K ^ γ) ^ (s / 2) = K ^ p := by
    rw [← Real.rpow_mul hK0.le, ← Real.rpow_add hK0]
  have hM : K ^ γ = K ^ (γ - p) * K ^ p := by
    rw [← Real.rpow_add hK0, sub_add_cancel]
  have h6 : 6 * K ^ p ≤ K ^ γ := by
    rw [hM]
    exact mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hK0.le p)
  nlinarith [hprod]

/-- In the central period, real distance bounded below also bounds every integer image. -/
lemma gradPartial_far_from_int {t y : ℝ} (ht : t ≤ 1 / 2)
    (hy0 : t / 4 ≤ |y|) (hy1 : |y| ≤ 1 / 2) : ∀ m : ℤ, t / 4 ≤ |y - m| := by
  intro m
  by_cases hm : m = 0
  · simpa [hm] using hy0
  have hm1 : (1 : ℝ) ≤ |(m : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hm
  have htri := abs_sub_abs_le_abs_sub (m : ℝ) y
  rw [abs_sub_comm] at htri
  linarith

/-- The support vanishes on both strips, including when the particle is near an endpoint.
Only a small relative anchor error is needed. -/
lemma gradPartial_strip_support {ψ : ℝ → ℝ} {ℓ γ : ℝ} {N : ℕ+}
    (hP : GradPartial N ℓ γ) (hM : 0 ≤ gradM N ℓ γ)
    (hsupp : ∀ y : ℝ, (∀ m : ℤ, gradT N ℓ γ / 4 ≤ |y - m|) → ψ (y / ℓ) = 0)
    {x v : ℝ} (i : ℤ) (he : 1 + |(N : ℝ) * x - (i : ℝ)| ≤ gradM N ℓ γ / 2)
    (hv : v ∈ uIcc (-gradM N ℓ γ - (N : ℝ) * x)
        (-(⌊gradM N ℓ γ⌋ : ℝ) - (i : ℝ) - 1 / 2) ∨
      v ∈ uIcc (gradM N ℓ γ - (N : ℝ) * x)
        ((⌊gradM N ℓ γ⌋ : ℝ) - (i : ℝ) + 1 / 2)) :
    ψ ((x + v / (N : ℝ)) / ℓ) = 0 := by
  have hloc := gradPartial_strip_location hM i hv
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  have ht : gradT N ℓ γ = gradM N ℓ γ / N := by simp [gradT, hP]
  apply hsupp
  apply gradPartial_far_from_int
  · rw [ht]; apply (div_le_iff₀ hN).mpr; linarith [hP]
  · rw [ht, show x + v / (N : ℝ) = ((N : ℝ) * x + v) / N by field_simp,
      abs_div, abs_of_pos hN]
    apply (le_div_iff₀ hN).mpr
    have : gradM N ℓ γ / (N : ℝ) / 4 * N = gradM N ℓ γ / 4 := by field_simp
    rw [this]
    linarith [hloc.1]
  · rw [show x + v / (N : ℝ) = ((N : ℝ) * x + v) / N by field_simp,
      abs_div, abs_of_pos hN]
    apply (div_le_iff₀ hN).mpr
    linarith [hloc.2, hP]

/-- A zero profile at both endpoints and a zero first derivative kill both cell integrands.
This also treats the origin using the diagonal formula for `Z`. -/
lemma gradPartial_cell_vanish {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (s : ℝ) (N : ℕ) (x v : ℝ) (hx : ψ (x / ℓ) = 0)
    (hq : deriv ψ (x / ℓ) = 0) (hy : ψ ((x + v / N) / ℓ) = 0) :
    gradCellF s N ℓ ψ x v = 0 ∧ gradCellR s N ℓ ψ x v = 0 := by
  have hZ : gradZ ψ ℓ x (x + v / N) = 0 := by
    by_cases he : x + v / (N : ℝ) = x
    · rw [he, gradZ_self, hq]
    · rw [gradZ_eq_quot hψ hℓ he, hy, hx]; simp
  have hZx : gradZx ψ ℓ x (x + v / N) = 0 := by simp [gradZx, hZ, hq]
  simp [gradCellF, gradCellR, hZ, hZx]

/-- Uniform eventual support separation on both strips, derived from the event and anchor. -/
theorem gradPartial_strips_outside_support {s γ ε : ℝ} (hs : 0 < s) (hγ : 0 ≤ γ)
    (hε0 : 0 ≤ ε) (hε : ε < γ * (1 - s / 2)) :
    ∃ K₀ : ℝ, 1 ≤ K₀ ∧ ∀ (N : ℕ+) (ℓ : ℝ) (X : Fin (N : ℕ) → ℝ) (ψ : ℝ → ℝ),
      K₀ ≤ (N : ℝ) * ℓ → GradPartial N ℓ γ → gradEvent s γ ε N ℓ X →
      |(N : ℝ) * gradLift N X 0| ≤ ((N : ℝ) * ℓ) ^ ε →
      (∀ y : ℝ, (∀ m : ℤ, gradT N ℓ γ / 4 ≤ |y - m|) → ψ (y / ℓ) = 0) →
      ∀ i ∈ gradLabels N ℓ γ, ∀ v : ℝ,
        (v ∈ uIcc (-gradM N ℓ γ - (N : ℝ) * gradLift N X i)
            (-(⌊gradM N ℓ γ⌋ : ℝ) - (i : ℝ) - 1 / 2) ∨
          v ∈ uIcc (gradM N ℓ γ - (N : ℝ) * gradLift N X i)
            ((⌊gradM N ℓ γ⌋ : ℝ) - (i : ℝ) + 1 / 2)) →
        ψ ((gradLift N X i + v / (N : ℝ)) / ℓ) = 0 := by
  obtain ⟨K₀, hK₀, hsmall⟩ := gradPartial_small_relative_error hs.le hγ hε0 hε
  refine ⟨K₀, hK₀, ?_⟩
  intro N ℓ X ψ hK hP hX hanchor hsupp i hi v hv
  have hK1 := hK₀.trans hK
  have hM : 0 ≤ gradM N ℓ γ := Real.rpow_nonneg (by linarith) _
  have hi' := (mem_gradLabels_partial hP i).mp hi
  have hiM : |(i : ℝ)| ≤ gradM N ℓ γ := by
    have hiR : |(i : ℝ)| ≤ (⌊gradM N ℓ γ⌋ : ℝ) := by
      rw [← Int.cast_abs]
      exact_mod_cast (abs_le.mpr ⟨hi'.1, hi'.2⟩)
    exact hiR.trans (Int.floor_le _)
  have he := gradPartial_anchor_error hs hP hX hanchor hi
  have hp := Real.rpow_le_rpow (abs_nonneg (i : ℝ)) hiM (by linarith : 0 ≤ s / 2)
  have hmul := mul_le_mul_of_nonneg_left hp
    (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ N * ℓ) ε)
  apply gradPartial_strip_support hP hM hsupp i _ hv
  have hsm := hsmall ((N : ℝ) * ℓ) hK
  change 1 + ((N : ℝ) * ℓ) ^ ε * (1 + (gradM N ℓ γ) ^ (s / 2))
    ≤ gradM N ℓ γ / 2 at hsm
  nlinarith

/-- The coefficient of a possible endpoint singularity is zero. -/
lemma gradPartial_endpoint_deriv_zero {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    {N : ℕ+} {ℓ γ x : ℝ} (hℓ : ℓ ≠ 0) (hP : GradPartial N ℓ γ)
    (hM : 0 < gradM N ℓ γ)
    (hsupp : ∀ y : ℝ, (∀ m : ℤ, gradT N ℓ γ / 4 ≤ |y - m|) → ψ (y / ℓ) = 0)
    (hx : x = -gradT N ℓ γ ∨ x = gradT N ℓ γ) : deriv ψ (x / ℓ) = 0 := by
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  have ht : 0 < gradT N ℓ γ := by simpa [gradT, hP] using div_pos hM hN
  have ht2 : gradT N ℓ γ ≤ 1 / 2 := by
    simp only [gradT, hP, ↓reduceIte]
    apply (div_le_iff₀ hN).mpr
    linarith [hP]
  have hfar : ∀ m : ℤ, gradT N ℓ γ ≤ |x - m| := by
    apply far_of_endpoint ht ht2
    rcases hx with hx | hx
    · exact Or.inl ⟨0, by simpa using hx⟩
    · exact Or.inr ⟨0, by simpa using hx⟩
  exact deriv_psi_zero_of_eventually hℓ (eventually_psi_zero_near ht hsupp hfar)
    (hψ.differentiable (by simp) _)

end

end Riesz1
