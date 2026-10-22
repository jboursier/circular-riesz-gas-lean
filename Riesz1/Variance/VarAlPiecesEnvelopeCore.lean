/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.PeriodicMarkCutoff
public import Riesz1.ToMathlib.MollifierPointwise.Circle

/-!
# Decomposition of a smoothed transport into pieces with envelopes

Proposition 5.9, decomposition and derivative envelopes. Given a smooth
`L`-periodic function `F` whose derivatives are bounded by the marked envelopes of
Lemma 5.1, the pieces `χ_i F` (one per mark) and `(1 - ∑ χ_i) F` (the remainder)
add up to `F`. Each singular piece, translated to its mark, has the envelope of its singularity.
The remainder has bounded derivatives. The constants depend only on the cutoff, the separation of
the marks, and the envelope data, not on the period `L`.
-/

public section

open Set Filter Topology
open scoped ContDiff

namespace Riesz1

/-! ## Circular distance -/

/-- The circular distance is even. -/
lemma circDist_neg_eq {L : ℝ} (hL : 0 < L) (t : ℝ) : circDist L (-t) = circDist L t := by
  have key : ∀ u : ℝ, circDist L (-u) ≤ circDist L u := by
    intro u
    have h1 : circDist L (-u) ≤ |-u - ((-round (u / L) : ℤ) : ℝ) * L| :=
      abs_cutRep_le_abs_sub_int_mul hL (-u) (-round (u / L))
    have e : -u - ((-round (u / L) : ℤ) : ℝ) * L = -(u - L * round (u / L)) := by
      push_cast
      ring
    rw [e, abs_neg] at h1
    exact h1
  exact le_antisymm (key t) (by simpa only [neg_neg] using key (-t))

/-- The circular distance is subadditive. -/
lemma circDist_add_le {L : ℝ} (hL : 0 < L) (s t : ℝ) :
    circDist L (s + t) ≤ circDist L s + circDist L t := by
  have h1 : circDist L (s + t) ≤
      |s + t - ((round (s / L) + round (t / L) : ℤ) : ℝ) * L| :=
    abs_cutRep_le_abs_sub_int_mul hL (s + t) (round (s / L) + round (t / L))
  have e : s + t - ((round (s / L) + round (t / L) : ℤ) : ℝ) * L =
      (s - L * round (s / L)) + (t - L * round (t / L)) := by
    push_cast
    ring
  rw [e] at h1
  exact h1.trans (abs_add_le _ _)

/-- The circular distance of a difference is at most the sum of the two distances. -/
lemma circDist_sub_le {L : ℝ} (hL : 0 < L) (s t : ℝ) :
    circDist L (s - t) ≤ circDist L s + circDist L t := by
  calc circDist L (s - t) = circDist L (s + -t) := by rw [sub_eq_add_neg]
    _ ≤ circDist L s + circDist L (-t) := circDist_add_le hL s (-t)
    _ = circDist L s + circDist L t := by rw [circDist_neg_eq hL]

/-! ## Calculus on the line -/

lemma diff_of_contDiff {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (x : ℝ) :
    DifferentiableAt ℝ f x :=
  (hf.differentiable (by simp)).differentiableAt

lemma contDiff_deriv_of {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (deriv f) :=
  (contDiff_infty_iff_deriv.mp hf).2

lemma deriv_mul_of_contDiff {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x : ℝ) :
    deriv (fun t => f t * g t) x = deriv f x * g x + f x * deriv g x :=
  deriv_mul (diff_of_contDiff hf x) (diff_of_contDiff hg x)

/-- The second derivative of a product of two smooth functions. -/
lemma deriv_deriv_mul_of_contDiff {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (x : ℝ) :
    deriv (deriv (fun t => f t * g t)) x =
      deriv (deriv f) x * g x + 2 * (deriv f x * deriv g x) + f x * deriv (deriv g) x := by
  have hfun : deriv (fun t => f t * g t) = fun t => deriv f t * g t + f t * deriv g t :=
    funext fun t => deriv_mul_of_contDiff hf hg t
  have dA : DifferentiableAt ℝ (fun t => deriv f t * g t) x :=
    (diff_of_contDiff (contDiff_deriv_of hf) x).mul (diff_of_contDiff hg x)
  have dB : DifferentiableAt ℝ (fun t => f t * deriv g t) x :=
    (diff_of_contDiff hf x).mul (diff_of_contDiff (contDiff_deriv_of hg) x)
  rw [hfun, show (fun t => deriv f t * g t + f t * deriv g t) =
      (fun t => deriv f t * g t) + (fun t => f t * deriv g t) from rfl, deriv_add dA dB,
    deriv_mul_of_contDiff (contDiff_deriv_of hf) hg x,
    deriv_mul_of_contDiff hf (contDiff_deriv_of hg) x]
  ring

/-- The derivative of a periodic function is periodic. -/
lemma varAlPieces_periodic_deriv_of {f : ℝ → ℝ} {L : ℝ} (hper : Function.Periodic f L) :
    Function.Periodic (deriv f) L := by
  intro x
  have hfun : (fun y => f (y + L)) = f := funext hper
  have h := deriv_comp_add_const (f := f) (a := L) (x := x)
  rw [hfun] at h
  exact h.symm

/-- A continuous periodic function is bounded. -/
lemma exists_abs_le_of_periodic_continuous {g : ℝ → ℝ} {L : ℝ} (hL : 0 < L) (hg : Continuous g)
    (hper : Function.Periodic g L) : ∃ C : ℝ, ∀ x, |g x| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := 0) (b := L)).exists_bound_of_continuousOn
    hg.continuousOn
  refine ⟨C, fun x => ?_⟩
  obtain ⟨y, hy, hxy⟩ := hper.exists_mem_Ico₀ hL x
  have := hC y (Ico_subset_Icc_self hy)
  rw [Real.norm_eq_abs] at this
  rw [hxy]
  exact this

/-- A smooth periodic function is Lipschitz on the line. -/
lemma lipschitz_of_periodic_contDiff {f : ℝ → ℝ} {L : ℝ} (hL : 0 < L) (hf : ContDiff ℝ ∞ f)
    (hper : Function.Periodic f L) : ∃ C : NNReal, LipschitzWith C f := by
  obtain ⟨C, hC⟩ := exists_abs_le_of_periodic_continuous hL (contDiff_deriv_of hf).continuous
    (varAlPieces_periodic_deriv_of hper)
  refine ⟨⟨max C 0, le_max_right _ _⟩, lipschitzWith_of_nnnorm_deriv_le
    (fun x => diff_of_contDiff hf x) (fun x => ?_)⟩
  refine NNReal.coe_le_coe.mp ?_
  rw [coe_nnnorm, Real.norm_eq_abs]
  exact (hC x).trans (le_max_left _ _)

/-- The sum of finitely many smooth functions has the sum of their derivatives. -/
lemma hasDerivAt_sum_fun {p : ℕ} {f : Fin p → ℝ → ℝ} (hf : ∀ i, ContDiff ℝ ∞ (f i))
    (t : ℝ) : HasDerivAt (fun s => ∑ i, f i s) (∑ i, deriv (f i) t) t :=
  by
    have h := HasDerivAt.sum (u := Finset.univ) (A := f) (A' := fun i => deriv (f i) t)
      (x := t) (fun i _ => (diff_of_contDiff (hf i) t).hasDerivAt)
    convert h using 2
    simp [Finset.sum_apply]

/-- A bound on each term of a finite sum gives a bound on the sum. -/
lemma varAlPieces_abs_sum_le_card_mul {p : ℕ} {f : Fin p → ℝ} {B : ℝ} (h : ∀ i, |f i| ≤ B) :
    |∑ i, f i| ≤ p * B := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have : ∑ i, |f i| ≤ ∑ _i : Fin p, B := Finset.sum_le_sum fun i _ => h i
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using this

/-- A sum of nonnegative terms each bounded by `B` is bounded by `p * B`. -/
lemma sum_le_card_mul {p : ℕ} {f : Fin p → ℝ} {B : ℝ} (h : ∀ i, f i ≤ B) :
    ∑ i, f i ≤ p * B := by
  have : ∑ i, f i ≤ ∑ _i : Fin p, B := Finset.sum_le_sum fun i _ => h i
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using this

/-! ## The decomposition -/

/-- The pieces of the decomposition: the cutoff pieces `χ_i F` for the `p` marks `a_i`, then the
remainder `(1 - ∑ χ_i) F`, indexed by `Fin (p + 1)` with the remainder last. -/
noncomputable def varAlPiece (ζ : ℝ → ℝ) (L : ℝ) {p : ℕ} (a : Fin p → ℝ) (F : ℝ → ℝ) :
    Fin (p + 1) → ℝ → ℝ :=
  Fin.lastCases (motive := fun _ => ℝ → ℝ)
    (fun x => (1 - ∑ i, markCut ζ L (a i) x) * F x)
    (fun i x => markCut ζ L (a i) x * F x)

lemma varAlPiece_last (ζ : ℝ → ℝ) (L : ℝ) {p : ℕ} (a : Fin p → ℝ) (F : ℝ → ℝ) :
    varAlPiece ζ L a F (Fin.last p) = fun x => (1 - ∑ i, markCut ζ L (a i) x) * F x := by
  simp only [varAlPiece, Fin.lastCases_last]

lemma varAlPiece_castSucc (ζ : ℝ → ℝ) (L : ℝ) {p : ℕ} (a : Fin p → ℝ) (F : ℝ → ℝ) (i : Fin p) :
    varAlPiece ζ L a F (Fin.castSucc i) = fun x => markCut ζ L (a i) x * F x := by
  simp only [varAlPiece, Fin.lastCases_castSucc]

/-- The pieces add up to `F`. -/
lemma sum_varAlPiece (ζ : ℝ → ℝ) (L : ℝ) {p : ℕ} (a : Fin p → ℝ) (F : ℝ → ℝ) (x : ℝ) :
    ∑ j, varAlPiece ζ L a F j x = F x := by
  rw [Fin.sum_univ_castSucc]
  simp only [varAlPiece_castSucc, varAlPiece_last]
  rw [← Finset.sum_mul]
  ring

/-- Each piece is smooth when the bump is smooth and `4 r < L`. -/
lemma contDiff_varAlPiece {ζ : ℝ → ℝ} {r L : ℝ} (hζ : ContDiff ℝ ∞ ζ)
    (hζ0 : ∀ s, 2 * r ≤ |s| → ζ s = 0) (hL : 0 < L) (hLr : 4 * r < L) {p : ℕ}
    (a : Fin p → ℝ) {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (j : Fin (p + 1)) :
    ContDiff ℝ ∞ (varAlPiece ζ L a F j) := by
  refine Fin.lastCases ?_ (fun i => ?_) j
  · rw [varAlPiece_last]
    exact (contDiff_const.sub (ContDiff.sum fun i _ =>
      contDiff_markCut hζ hζ0 hL hLr (a i))).mul hF
  · rw [varAlPiece_castSucc]
    exact (contDiff_markCut hζ hζ0 hL hLr (a i)).mul hF

/-- Each piece is `L`-periodic when `F` is. -/
lemma periodic_varAlPiece {ζ : ℝ → ℝ} {L : ℝ} (hL : 0 < L) {p : ℕ} (a : Fin p → ℝ)
    {F : ℝ → ℝ} (hF : Function.Periodic F L) (j : Fin (p + 1)) :
    Function.Periodic (varAlPiece ζ L a F j) L := by
  refine Fin.lastCases ?_ (fun i => ?_) j
  · rw [varAlPiece_last]
    intro x
    simp only [markCut_add_period hL, hF x]
  · rw [varAlPiece_castSucc]
    intro x
    simp only [markCut_add_period hL, hF x]

/-! ## Envelopes of the singular pieces -/

/-- The modulus of a smooth cutoff is at most one. -/
lemma abs_markCut_le_one {ζ : ℝ → ℝ} (hζ01 : ∀ s, 0 ≤ ζ s ∧ ζ s ≤ 1) (L a x : ℝ) :
    |markCut ζ L a x| ≤ 1 := by
  unfold markCut
  rw [abs_le]
  constructor <;> linarith [hζ01 (cutRep L (x - a))]

/-- The first and second derivatives of a singular piece, translated to its mark, satisfy the
envelopes with the weights `max(d, K⁻¹)^(-b)` and `max(d, K⁻¹)^(-1-b)` on the unit scale. -/
theorem sing_envelope {ζ : ℝ → ℝ} {r δ : ℝ} (hζ : ContDiff ℝ ∞ ζ)
    (hζ0 : ∀ s, 2 * r ≤ |s| → ζ s = 0)
    (hζ01 : ∀ s, 0 ≤ ζ s ∧ ζ s ≤ 1) {M1 M2 : ℝ}
    (hM1 : ∀ s, |deriv ζ s| ≤ M1) (hM2 : ∀ s, |deriv (deriv ζ) s| ≤ M2)
    {L : ℝ} (hL : 1 ≤ L) {p : ℕ} (a : Fin p → ℝ)
    (hsep : ∀ i k, i ≠ k → δ ≤ circDist L (a i - a k))
    (hr : 0 < r) (hr16 : r ≤ 1 / 16) (hδ : 6 * r ≤ δ)
    {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) {S : ℝ} (hS : ∀ x, |F x| ≤ S)
    {A b K h : ℝ} (hA : 0 ≤ A) (hb : 0 < b) (hK : 1 ≤ K) (hh : K⁻¹ ≤ h)
    (hD1 : ∀ x, |deriv F x| ≤ A * (1 + ∑ k, max (circDist L (x - a k)) h ^ (-b)))
    (hD2 : ∀ x, |deriv (deriv F) x| ≤ A * (1 + ∑ k, max (circDist L (x - a k)) h ^ (-1 - b)))
    (i : Fin p) (x : ℝ) :
    |deriv (varAlPiece ζ L a F (Fin.castSucc i)) (x + a i)| ≤
        (M1 * S + A * (1 + p + p * (4 * r) ^ (-b))) *
          (if circDist L x < 1 then max (circDist L x) K⁻¹ ^ (-b) else 0) ∧
      |deriv (deriv (varAlPiece ζ L a F (Fin.castSucc i))) (x + a i)| ≤
        (M2 * S + 2 * M1 * (A * (1 + p + p * (4 * r) ^ (-b))) +
          A * (1 + p + p * (4 * r) ^ (-1 - b))) *
          (if circDist L x < 1 then max (circDist L x) K⁻¹ ^ (-1 - b) else 0) := by
  have hL0 : 0 < L := by linarith
  have hLr : 4 * r < L := by linarith
  have hM1nn : 0 ≤ M1 := (abs_nonneg _).trans (hM1 0)
  have hM2nn : 0 ≤ M2 := (abs_nonneg _).trans (hM2 0)
  have hSnn : 0 ≤ S := (abs_nonneg _).trans (hS 0)
  have hK0 : 0 < K := by linarith
  have hKinv0 : 0 < K⁻¹ := inv_pos.mpr hK0
  have hKinv1 : K⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hK
  have hc : 0 ≤ (4 * r) ^ (-b) := Real.rpow_nonneg (by linarith) _
  have hc2 : 0 ≤ (4 * r) ^ (-1 - b) := Real.rpow_nonneg (by linarith) _
  have hp : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hpc : 0 ≤ (p : ℝ) * (4 * r) ^ (-b) := mul_nonneg hp hc
  have hpc2 : 0 ≤ (p : ℝ) * (4 * r) ^ (-1 - b) := mul_nonneg hp hc2
  have hconst1 : 0 ≤ M1 * S + A * (1 + p + p * (4 * r) ^ (-b)) := by
    have : 0 ≤ 1 + (p : ℝ) + p * (4 * r) ^ (-b) := by linarith
    exact add_nonneg (mul_nonneg hM1nn hSnn) (mul_nonneg hA this)
  have hconst2 : 0 ≤ M2 * S + 2 * M1 * (A * (1 + p + p * (4 * r) ^ (-b))) +
      A * (1 + p + p * (4 * r) ^ (-1 - b)) := by
    have h1 : 0 ≤ 1 + (p : ℝ) + p * (4 * r) ^ (-b) := by linarith
    have h2 : 0 ≤ 1 + (p : ℝ) + p * (4 * r) ^ (-1 - b) := by linarith
    have h3 := mul_nonneg hA h1
    have h4 := mul_nonneg hA h2
    have h5 := mul_nonneg hM2nn hSnn
    have h6 := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hM1nn) h3
    linarith
  have hχC : ∀ j : Fin p, ContDiff ℝ ∞ (markCut ζ L (a j)) := fun j =>
    contDiff_markCut hζ hζ0 hL0 hLr (a j)
  -- The weight is nonnegative in both branches.
  have hW0 : ∀ e : ℝ, 0 ≤ (if circDist L x < 1 then max (circDist L x) K⁻¹ ^ e else 0) := by
    intro e
    split_ifs
    · exact Real.rpow_nonneg (le_max_of_le_right hKinv0.le) _
    · exact le_rfl
  by_cases hfar : 2 * r < circDist L x
  · -- Far from the mark the piece vanishes near the translation point.
    have hx : 2 * r < |cutRep L (x + a i - a i)| := by
      rw [add_sub_cancel_right]
      exact hfar
    have hev : ∀ᶠ t in 𝓝 (x + a i), varAlPiece ζ L a F (Fin.castSucc i) t = 0 := by
      filter_upwards [eventually_markCut_eq_zero hL0 hζ0 (a i) (x + a i) hx] with t ht
      rw [varAlPiece_castSucc]
      simp [ht]
    obtain ⟨h1, h2⟩ := deriv_deriv_eq_zero_of_eventually_const hev
    simp only [h1, h2, abs_zero]
    exact ⟨mul_nonneg hconst1 (hW0 _), mul_nonneg hconst2 (hW0 _)⟩
  · -- Near the mark: all estimates are available.
    have hfar' : circDist L x ≤ 2 * r := not_lt.mp hfar
    have hd1 : circDist L x < 1 := by linarith
    simp only [hd1, ↓reduceIte]
    have hmaxpos : 0 < max (circDist L x) K⁻¹ := lt_max_of_lt_right hKinv0
    have hmax1 : max (circDist L x) K⁻¹ ≤ 1 := max_le hd1.le hKinv1
    have hW1 : 1 ≤ max (circDist L x) K⁻¹ ^ (-b) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hmaxpos hmax1 (by linarith)
    have hW21 : 1 ≤ max (circDist L x) K⁻¹ ^ (-1 - b) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hmaxpos hmax1 (by linarith)
    have hWW2 : max (circDist L x) K⁻¹ ^ (-b) ≤ max (circDist L x) K⁻¹ ^ (-1 - b) :=
      Real.rpow_le_rpow_of_exponent_ge hmaxpos hmax1 (by linarith)
    -- Distances of the translation point to the other marks.
    have hother : ∀ k, k ≠ i → 4 * r ≤ circDist L (x + a i - a k) := by
      intro k hk
      have h1 := hsep i k (Ne.symm hk)
      have h2 := circDist_sub_le hL0 (x + a i - a k) x
      have e : x + a i - a k - x = a i - a k := by ring
      rw [e] at h2
      linarith
    -- Each term of the sum over marks is bounded by the weight plus a constant.
    have hterm1 : ∀ k, max (circDist L (x + a i - a k)) h ^ (-b) ≤
        max (circDist L x) K⁻¹ ^ (-b) + (4 * r) ^ (-b) := by
      intro k
      by_cases hk : k = i
      · rw [hk, add_sub_cancel_right]
        have : max (circDist L x) h ^ (-b) ≤ max (circDist L x) K⁻¹ ^ (-b) :=
          Real.rpow_le_rpow_of_nonpos hmaxpos (max_le_max le_rfl hh) (by linarith)
        linarith [hc]
      · have h4 := hother k hk
        have h5 : 4 * r ≤ max (circDist L (x + a i - a k)) h := le_max_of_le_left h4
        have h6 : max (circDist L (x + a i - a k)) h ^ (-b) ≤ (4 * r) ^ (-b) :=
          Real.rpow_le_rpow_of_nonpos (by linarith) h5 (by linarith)
        linarith
    have hterm2 : ∀ k, max (circDist L (x + a i - a k)) h ^ (-1 - b) ≤
        max (circDist L x) K⁻¹ ^ (-1 - b) + (4 * r) ^ (-1 - b) := by
      intro k
      by_cases hk : k = i
      · rw [hk, add_sub_cancel_right]
        have : max (circDist L x) h ^ (-1 - b) ≤ max (circDist L x) K⁻¹ ^ (-1 - b) :=
          Real.rpow_le_rpow_of_nonpos hmaxpos (max_le_max le_rfl hh) (by linarith)
        linarith [hc2]
      · have h4 := hother k hk
        have h5 : 4 * r ≤ max (circDist L (x + a i - a k)) h := le_max_of_le_left h4
        have h6 : max (circDist L (x + a i - a k)) h ^ (-1 - b) ≤ (4 * r) ^ (-1 - b) :=
          Real.rpow_le_rpow_of_nonpos (by linarith) h5 (by linarith)
        linarith
    have hsum1 : ∑ k, max (circDist L (x + a i - a k)) h ^ (-b) ≤
        p * (max (circDist L x) K⁻¹ ^ (-b) + (4 * r) ^ (-b)) := sum_le_card_mul hterm1
    have hsum2 : ∑ k, max (circDist L (x + a i - a k)) h ^ (-1 - b) ≤
        p * (max (circDist L x) K⁻¹ ^ (-1 - b) + (4 * r) ^ (-1 - b)) := sum_le_card_mul hterm2
    -- Bounds on `F'` and `F''` at the translation point.
    have hF1 : |deriv F (x + a i)| ≤
        A * (1 + p * (max (circDist L x) K⁻¹ ^ (-b) + (4 * r) ^ (-b))) :=
      (hD1 _).trans (mul_le_mul_of_nonneg_left (by linarith) hA)
    have hF2 : |deriv (deriv F) (x + a i)| ≤
        A * (1 + p * (max (circDist L x) K⁻¹ ^ (-1 - b) + (4 * r) ^ (-1 - b))) :=
      (hD2 _).trans (mul_le_mul_of_nonneg_left (by linarith) hA)
    have hchi := abs_markCut_le_one hζ01 (a i) (L := L) (x := x + a i)
    -- Algebraic comparisons of the weights.
    set W := max (circDist L x) K⁻¹ ^ (-b) with hWdef
    set W2 := max (circDist L x) K⁻¹ ^ (-1 - b) with hW2def
    set c := (4 * r) ^ (-b) with hcdef
    set c2 := (4 * r) ^ (-1 - b) with hc2def
    have hpos1 : 0 ≤ 1 + (p : ℝ) + p * c := by linarith
    have hpos2 : 0 ≤ 1 + (p : ℝ) + p * c2 := by linarith
    have hineq1 : 1 + (p : ℝ) * (W + c) ≤ (1 + p + p * c) * W := by
      have e : (1 + (p : ℝ) + p * c) * W - (1 + (p : ℝ) * (W + c)) = (1 + p * c) * (W - 1) := by
        ring
      have : 0 ≤ (1 + p * c) * (W - 1) := mul_nonneg (by linarith) (sub_nonneg.2 hW1)
      linarith
    have hineq2 : 1 + (p : ℝ) * (W2 + c2) ≤ (1 + p + p * c2) * W2 := by
      have e : (1 + (p : ℝ) + p * c2) * W2 - (1 + (p : ℝ) * (W2 + c2)) =
          (1 + p * c2) * (W2 - 1) := by
        ring
      have : 0 ≤ (1 + p * c2) * (W2 - 1) := mul_nonneg (by linarith) (sub_nonneg.2 hW21)
      linarith
    have hineq1' : 1 + (p : ℝ) * (W + c) ≤ (1 + p + p * c) * W2 :=
      hineq1.trans (mul_le_mul_of_nonneg_left hWW2 hpos1)
    constructor
    · -- First derivative.
      rw [varAlPiece_castSucc, deriv_mul_of_contDiff (hχC i) hF]
      have e1 : |deriv (markCut ζ L (a i)) (x + a i) * F (x + a i)| ≤ M1 * S := by
        rw [abs_mul]
        exact mul_le_mul (abs_deriv_markCut_le hζ0 hL0 hLr hM1 (a i) (x + a i)) (hS _)
          (abs_nonneg _) hM1nn
      have e2 : |markCut ζ L (a i) (x + a i) * deriv F (x + a i)| ≤
          A * (1 + p * (W + c)) := by
        rw [abs_mul]
        calc |markCut ζ L (a i) (x + a i)| * |deriv F (x + a i)|
            ≤ 1 * (A * (1 + p * (W + c))) := mul_le_mul hchi hF1 (abs_nonneg _) zero_le_one
          _ = A * (1 + p * (W + c)) := one_mul _
      have hfin : A * (1 + p * (W + c)) ≤ A * ((1 + p + p * c) * W) :=
        mul_le_mul_of_nonneg_left hineq1 hA
      have hM : M1 * S ≤ M1 * S * W := le_mul_of_one_le_right (mul_nonneg hM1nn hSnn) hW1
      have hsplit : (M1 * S + A * (1 + p + p * c)) * W =
          M1 * S * W + A * ((1 + p + p * c) * W) := by
        ring
      calc |deriv (markCut ζ L (a i)) (x + a i) * F (x + a i) +
            markCut ζ L (a i) (x + a i) * deriv F (x + a i)|
          ≤ |deriv (markCut ζ L (a i)) (x + a i) * F (x + a i)| +
            |markCut ζ L (a i) (x + a i) * deriv F (x + a i)| := abs_add_le _ _
        _ ≤ M1 * S + A * (1 + p * (W + c)) := add_le_add e1 e2
        _ ≤ M1 * S * W + A * ((1 + p + p * c) * W) := add_le_add hM hfin
        _ = (M1 * S + A * (1 + p + p * c)) * W := hsplit.symm
    · -- Second derivative.
      rw [varAlPiece_castSucc, deriv_deriv_mul_of_contDiff (hχC i) hF]
      have e1 : |deriv (deriv (markCut ζ L (a i))) (x + a i) * F (x + a i)| ≤ M2 * S := by
        rw [abs_mul]
        exact mul_le_mul (abs_deriv_deriv_markCut_le hζ0 hL0 hLr hM2 (a i) (x + a i))
          (hS _) (abs_nonneg _) hM2nn
      have e2 : |2 * (deriv (markCut ζ L (a i)) (x + a i) * deriv F (x + a i))| ≤
          2 * M1 * (A * (1 + p * (W + c))) := by
        rw [abs_mul, abs_two, abs_mul]
        have h := mul_le_mul (abs_deriv_markCut_le hζ0 hL0 hLr hM1 (a i) (x + a i)) hF1
          (abs_nonneg _) hM1nn
        linarith [h]
      have e3 : |markCut ζ L (a i) (x + a i) * deriv (deriv F) (x + a i)| ≤
          A * (1 + p * (W2 + c2)) := by
        rw [abs_mul]
        calc |markCut ζ L (a i) (x + a i)| * |deriv (deriv F) (x + a i)|
            ≤ 1 * (A * (1 + p * (W2 + c2))) := mul_le_mul hchi hF2 (abs_nonneg _) zero_le_one
          _ = A * (1 + p * (W2 + c2)) := one_mul _
      have hfin2 : A * (1 + p * (W2 + c2)) ≤ A * ((1 + p + p * c2) * W2) :=
        mul_le_mul_of_nonneg_left hineq2 hA
      have hfin1 : 2 * M1 * (A * (1 + p * (W + c))) ≤ 2 * M1 * (A * ((1 + p + p * c) * W2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hineq1' hA)
          (mul_nonneg (by norm_num) hM1nn)
      have hM : M2 * S ≤ M2 * S * W2 := le_mul_of_one_le_right (mul_nonneg hM2nn hSnn) hW21
      have hsplit : (M2 * S + 2 * M1 * (A * (1 + p + p * c)) + A * (1 + p + p * c2)) * W2 =
          M2 * S * W2 + 2 * M1 * (A * ((1 + p + p * c) * W2)) +
            A * ((1 + p + p * c2) * W2) := by
        ring
      have tri : |deriv (deriv (markCut ζ L (a i))) (x + a i) * F (x + a i) +
            2 * (deriv (markCut ζ L (a i)) (x + a i) * deriv F (x + a i)) +
            markCut ζ L (a i) (x + a i) * deriv (deriv F) (x + a i)| ≤
          |deriv (deriv (markCut ζ L (a i))) (x + a i) * F (x + a i) +
            2 * (deriv (markCut ζ L (a i)) (x + a i) * deriv F (x + a i))| +
          |markCut ζ L (a i) (x + a i) * deriv (deriv F) (x + a i)| := abs_add_le _ _
      have tri2 : |deriv (deriv (markCut ζ L (a i))) (x + a i) * F (x + a i) +
            2 * (deriv (markCut ζ L (a i)) (x + a i) * deriv F (x + a i))| ≤
          |deriv (deriv (markCut ζ L (a i))) (x + a i) * F (x + a i)| +
            |2 * (deriv (markCut ζ L (a i)) (x + a i) * deriv F (x + a i))| := abs_add_le _ _
      linarith [tri, tri2, e1, e2, e3, hfin1, hfin2, hM, hsplit]

/-! ## The remainder piece -/

/-- The remainder `(1 - ∑ χ_i) F` has bounded first and second derivatives everywhere, with
constants depending only on the cutoff, the number of marks, the separation and the envelope
data. -/
theorem remainder_envelope {ζ : ℝ → ℝ} {r δ : ℝ} (hζ : ContDiff ℝ ∞ ζ)
    (hζ0 : ∀ s, 2 * r ≤ |s| → ζ s = 0) (hζ1 : ∀ s, |s| ≤ r → ζ s = 1)
    (hζ01 : ∀ s, 0 ≤ ζ s ∧ ζ s ≤ 1) {M1 M2 : ℝ}
    (hM1 : ∀ s, |deriv ζ s| ≤ M1) (hM2 : ∀ s, |deriv (deriv ζ) s| ≤ M2)
    {L : ℝ} (hL : 1 ≤ L) {p : ℕ} (a : Fin p → ℝ)
    (hsep : ∀ i k, i ≠ k → δ ≤ circDist L (a i - a k))
    (hr : 0 < r) (hr16 : r ≤ 1 / 16) (hδ : 6 * r ≤ δ)
    {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) {S : ℝ} (hS : ∀ x, |F x| ≤ S)
    {A b h : ℝ} (hA : 0 ≤ A) (hb : 0 < b)
    (hD1 : ∀ x, |deriv F x| ≤ A * (1 + ∑ k, max (circDist L (x - a k)) h ^ (-b)))
    (hD2 : ∀ x, |deriv (deriv F) x| ≤ A * (1 + ∑ k, max (circDist L (x - a k)) h ^ (-1 - b)))
    (x : ℝ) :
    |deriv (varAlPiece ζ L a F (Fin.last p)) x| ≤ p * M1 * S + (1 + p) * (A * (1 + p * r ^ (-b))) ∧
      |deriv (deriv (varAlPiece ζ L a F (Fin.last p))) x| ≤
        p * M2 * S + 2 * (p * M1) * (A * (1 + p * r ^ (-b))) +
          (1 + p) * (A * (1 + p * r ^ (-1 - b))) := by
  have hL0 : 0 < L := by linarith
  have hLr : 4 * r < L := by linarith
  have hM1nn : 0 ≤ M1 := (abs_nonneg _).trans (hM1 0)
  have hM2nn : 0 ≤ M2 := (abs_nonneg _).trans (hM2 0)
  have hSnn : 0 ≤ S := (abs_nonneg _).trans (hS 0)
  have hp : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hrb : 0 ≤ r ^ (-b) := Real.rpow_nonneg hr.le _
  have hrb2 : 0 ≤ r ^ (-1 - b) := Real.rpow_nonneg hr.le _
  have hCR1 : 0 ≤ p * M1 * S + (1 + p) * (A * (1 + p * r ^ (-b))) := by
    have h1 : 0 ≤ 1 + (p : ℝ) * r ^ (-b) := by nlinarith
    exact add_nonneg (mul_nonneg (mul_nonneg hp hM1nn) hSnn)
      (mul_nonneg (by linarith) (mul_nonneg hA h1))
  have hCR2 : 0 ≤ p * M2 * S + 2 * (p * M1) * (A * (1 + p * r ^ (-b))) +
      (1 + p) * (A * (1 + p * r ^ (-1 - b))) := by
    have h1 : 0 ≤ 1 + (p : ℝ) * r ^ (-b) := by nlinarith
    have h2 : 0 ≤ 1 + (p : ℝ) * r ^ (-1 - b) := by nlinarith
    have t1 : 0 ≤ p * M2 * S := mul_nonneg (mul_nonneg hp hM2nn) hSnn
    have t2 : 0 ≤ 2 * (p * M1) * (A * (1 + p * r ^ (-b))) :=
      mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg hp hM1nn)) (mul_nonneg hA h1)
    have t3 : 0 ≤ (1 + p) * (A * (1 + p * r ^ (-1 - b))) :=
      mul_nonneg (by linarith) (mul_nonneg hA h2)
    linarith
  have hχC : ∀ j : Fin p, ContDiff ℝ ∞ (markCut ζ L (a j)) := fun j =>
    contDiff_markCut hζ hζ0 hL0 hLr (a j)
  have hgC : ContDiff ℝ ∞ (fun t => 1 - ∑ i, markCut ζ L (a i) t) :=
    contDiff_const.sub (ContDiff.sum fun i _ => hχC i)
  have hg1 : ∀ t, deriv (fun t => 1 - ∑ i, markCut ζ L (a i) t) t =
      -∑ i, deriv (markCut ζ L (a i)) t := fun t =>
    ((hasDerivAt_sum_fun (fun i => hχC i) t).const_sub 1).deriv
  have hgfun : deriv (fun t => 1 - ∑ i, markCut ζ L (a i) t) =
      fun t => -∑ i, deriv (markCut ζ L (a i)) t :=
    funext hg1
  have hg2 : ∀ t, deriv (deriv (fun t => 1 - ∑ i, markCut ζ L (a i) t)) t =
      -∑ i, deriv (deriv (markCut ζ L (a i))) t := fun t => by
    rw [hgfun]
    exact ((hasDerivAt_sum_fun (fun i => contDiff_deriv_of (hχC i)) t).neg).deriv
  rw [varAlPiece_last]
  by_cases hk : ∃ k, circDist L (x - a k) < r
  · -- Some mark is within `r` of `x`: the remainder vanishes near `x`.
    obtain ⟨k, hk⟩ := hk
    have hfar : ∀ i, i ≠ k → 2 * r < circDist L (x - a i) := by
      intro i hik
      have h1 := hsep i k hik
      have h2 := circDist_sub_le hL0 (x - a k) (x - a i)
      have e : x - a k - (x - a i) = a i - a k := by ring
      rw [e] at h2
      linarith
    have hev : ∀ᶠ t in 𝓝 x, (1 - ∑ i, markCut ζ L (a i) t) * F t = 0 := by
      have hall : ∀ᶠ t in 𝓝 x, ∀ i, markCut ζ L (a i) t = if i = k then 1 else 0 := by
        rw [Filter.eventually_all]
        intro i
        by_cases hik : i = k
        · subst hik
          filter_upwards [eventually_markCut_eq_one hL0 hζ1 (a i) x hk] with t ht
          simp [ht]
        · filter_upwards [eventually_markCut_eq_zero hL0 hζ0 (a i) x (hfar i hik)] with t ht
          simp [ht, hik]
      filter_upwards [hall] with t ht
      have hs : ∑ i, markCut ζ L (a i) t = 1 := by simp [ht]
      rw [hs]
      ring
    obtain ⟨h1, h2⟩ := deriv_deriv_eq_zero_of_eventually_const hev
    simp only [h1, h2, abs_zero]
    exact ⟨hCR1, hCR2⟩
  · -- Every mark is at distance at least `r` from `x`: the bounds are uniform.
    have hk' : ∀ k, r ≤ circDist L (x - a k) := fun k => not_lt.mp fun h => hk ⟨k, h⟩
    have hg0 : |1 - ∑ i, markCut ζ L (a i) x| ≤ 1 + p := by
      have h1 := abs_sub (1 : ℝ) (∑ i, markCut ζ L (a i) x)
      have h2 : |∑ i, markCut ζ L (a i) x| ≤ p * 1 :=
        varAlPieces_abs_sum_le_card_mul fun i => abs_markCut_le_one hζ01 L (a i) x
      rw [abs_one] at h1
      linarith
    have hg1b : |-∑ i, deriv (markCut ζ L (a i)) x| ≤ p * M1 := by
      rw [abs_neg]
      exact varAlPieces_abs_sum_le_card_mul fun i => abs_deriv_markCut_le hζ0 hL0 hLr hM1 (a i) x
    have hg2b : |-∑ i, deriv (deriv (markCut ζ L (a i))) x| ≤ p * M2 := by
      rw [abs_neg]
      exact varAlPieces_abs_sum_le_card_mul fun i => abs_deriv_deriv_markCut_le hζ0 hL0 hLr hM2 (a i) x
    have hF1 : |deriv F x| ≤ A * (1 + p * r ^ (-b)) := by
      refine (hD1 x).trans (mul_le_mul_of_nonneg_left ?_ hA)
      have hs : ∑ k, max (circDist L (x - a k)) h ^ (-b) ≤ p * r ^ (-b) :=
        sum_le_card_mul fun k =>
          Real.rpow_le_rpow_of_nonpos hr (le_max_of_le_left (hk' k)) (by linarith)
      linarith
    have hF2 : |deriv (deriv F) x| ≤ A * (1 + p * r ^ (-1 - b)) := by
      refine (hD2 x).trans (mul_le_mul_of_nonneg_left ?_ hA)
      have hs : ∑ k, max (circDist L (x - a k)) h ^ (-1 - b) ≤ p * r ^ (-1 - b) :=
        sum_le_card_mul fun k =>
          Real.rpow_le_rpow_of_nonpos hr (le_max_of_le_left (hk' k)) (by linarith)
      linarith
    constructor
    · rw [deriv_mul_of_contDiff hgC hF x, hg1 x]
      have e1 : |(-∑ i, deriv (markCut ζ L (a i)) x) * F x| ≤ p * M1 * S := by
        rw [abs_mul]
        exact mul_le_mul hg1b (hS x) (abs_nonneg _) (mul_nonneg hp hM1nn)
      have e2 : |(1 - ∑ i, markCut ζ L (a i) x) * deriv F x| ≤
          (1 + p) * (A * (1 + p * r ^ (-b))) := by
        rw [abs_mul]
        exact mul_le_mul hg0 hF1 (abs_nonneg _) (by linarith)
      exact (abs_add_le _ _).trans (add_le_add e1 e2)
    · rw [deriv_deriv_mul_of_contDiff hgC hF x, hg2 x, hg1 x]
      have e1 : |(-∑ i, deriv (deriv (markCut ζ L (a i))) x) * F x| ≤ p * M2 * S := by
        rw [abs_mul]
        exact mul_le_mul hg2b (hS x) (abs_nonneg _) (mul_nonneg hp hM2nn)
      have e2 : |2 * ((-∑ i, deriv (markCut ζ L (a i)) x) * deriv F x)| ≤
          2 * (p * M1) * (A * (1 + p * r ^ (-b))) := by
        rw [abs_mul, abs_two, abs_mul]
        have h := mul_le_mul hg1b hF1 (abs_nonneg _) (mul_nonneg hp hM1nn)
        linarith [h]
      have e3 : |(1 - ∑ i, markCut ζ L (a i) x) * deriv (deriv F) x| ≤
          (1 + p) * (A * (1 + p * r ^ (-1 - b))) := by
        rw [abs_mul]
        exact mul_le_mul hg0 hF2 (abs_nonneg _) (by linarith)
      have tri1 := abs_add_le
        ((-∑ i, deriv (deriv (markCut ζ L (a i))) x) * F x)
        (2 * ((-∑ i, deriv (markCut ζ L (a i)) x) * deriv F x))
      have tri2 := abs_add_le
        ((-∑ i, deriv (deriv (markCut ζ L (a i))) x) * F x +
          2 * ((-∑ i, deriv (markCut ζ L (a i)) x) * deriv F x))
        ((1 - ∑ i, markCut ζ L (a i) x) * deriv (deriv F) x)
      linarith [tri1, tri2, e1, e2, e3]

end Riesz1
