/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.VarAlPiecesFixedCutoffs

/-!
# Fixed cutoffs for the transport derivative

The singular pieces are the products of the transport derivative with
fixed periodic cutoffs. Their complement is regular near every mark.
Its derivative has the compact tail and satisfies the a priori envelope
with singularity exponent zero.
-/

public section

open MeasureTheory Filter Set
open scoped ContDiff Topology

namespace Riesz1.Internal

/-- Near one mark, the other marked powers are uniformly bounded. -/
theorem fixedCutoff_marked_weight {n : ℕ} (a : Fin n → ℝ)
    {L r δ K h e x : ℝ} (hL : 0 < L) (hr : 0 < r) (hr16 : r ≤ 1 / 16)
    (hδ : 6 * r ≤ δ) (hsep : ∀ i k, i ≠ k → δ ≤ circDist L (a i - a k))
    (hK : 1 ≤ K) (hh : K⁻¹ ≤ h) (he : 0 ≤ e)
    (i : Fin n) (hx : circDist L (x - a i) ≤ 2 * r) :
    1 + ∑ k, max (circDist L (x - a k)) h ^ (-e) ≤
      (1 + n + n * (4 * r) ^ (-e)) * max (circDist L (x - a i)) K⁻¹ ^ (-e) := by
  have hpos : 0 < max (circDist L (x - a i)) K⁻¹ :=
    lt_max_of_lt_right (inv_pos.mpr (by linarith : 0 < K))
  have hmax : max (circDist L (x - a i)) K⁻¹ ≤ 1 :=
    max_le (by linarith) (inv_le_one_of_one_le₀ hK)
  have hW : 1 ≤ max (circDist L (x - a i)) K⁻¹ ^ (-e) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hpos hmax (by linarith)
  have hc : 0 ≤ (4 * r) ^ (-e) := Real.rpow_nonneg (by linarith) _
  have hterm (k : Fin n) : max (circDist L (x - a k)) h ^ (-e) ≤
      max (circDist L (x - a i)) K⁻¹ ^ (-e) + (4 * r) ^ (-e) := by
    by_cases hk : k = i
    · subst k
      exact (Real.rpow_le_rpow_of_nonpos hpos (max_le_max le_rfl hh) (by linarith)).trans
        (le_add_of_nonneg_right hc)
    · have hd : 4 * r ≤ circDist L (x - a k) := by
        have h1 := hsep i k (Ne.symm hk)
        have h2 := circDist_sub_le hL (x - a k) (x - a i)
        rw [show x - a k - (x - a i) = a i - a k by ring] at h2
        linarith
      exact (Real.rpow_le_rpow_of_nonpos (by linarith : 0 < 4 * r)
        (le_max_of_le_left hd) (by linarith)).trans
        (le_add_of_nonneg_left (by linarith))
  have hsum := sum_le_card_mul hterm
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith [mul_nonneg (mul_nonneg hn hc) (sub_nonneg.mpr hW)]

/-- The first derivative of the regular remainder is uniformly bounded. -/
theorem fixedCutoff_derivative_remainder {n : ℕ} (a : Fin n → ℝ)
    {L r δ M A b h : ℝ} (hL : 1 ≤ L) (hr : 0 < r) (hr16 : r ≤ 1 / 16)
    (hδ : 6 * r ≤ δ) (hsep : ∀ i k, i ≠ k → δ ≤ circDist L (a i - a k))
    (hM : ∀ x, |deriv (cutoffBump r) x| ≤ M) (hA : 0 ≤ A) (hb : 0 ≤ b)
    {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q)
    (hv : ∀ x, |q x| ≤ A * (1 + ∑ k, max (circDist L (x - a k)) h ^ (-b)))
    (hd : ∀ x, |deriv q x| ≤ A * (1 + ∑ k,
      max (circDist L (x - a k)) h ^ (-1 - b))) (x : ℝ) :
    |deriv (varAlPiece (cutoffBump r) L a q (Fin.last n)) x| ≤
      A * (n * M * (1 + n * r ^ (-b)) + (1 + n) * (1 + n * r ^ (-1 - b))) := by
  classical
  have hL0 : 0 < L := by linarith
  have hLr : 4 * r < L := by linarith
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hζ := contDiff_cutoffBump r
  have hζ0 : ∀ y, 2 * r ≤ |y| → cutoffBump r y = 0 :=
    fun y hy => cutoffBump_eq_zero hr hy
  have hχ (i : Fin n) : ContDiff ℝ ∞ (markCut (cutoffBump r) L (a i)) :=
    contDiff_markCut hζ hζ0 hL0 hLr (a i)
  rw [varAlPiece_last]
  by_cases hk : ∃ k, circDist L (x - a k) < r
  · obtain ⟨k, hk⟩ := hk
    have hfar (i : Fin n) (hik : i ≠ k) : 2 * r < circDist L (x - a i) := by
      have h1 := hsep i k hik
      have h2 := circDist_sub_le hL0 (x - a k) (x - a i)
      rw [show x - a k - (x - a i) = a i - a k by ring] at h2
      linarith
    have hev : (fun y => (1 - ∑ i, markCut (cutoffBump r) L (a i) y) * q y) =ᶠ[𝓝 x]
        fun _ => 0 := by
      have hall : ∀ᶠ y in 𝓝 x, ∀ i, markCut (cutoffBump r) L (a i) y =
          if i = k then 1 else 0 := by
        rw [Filter.eventually_all]
        intro i
        by_cases hik : i = k
        · subst i
          filter_upwards [eventually_markCut_eq_one hL0
            (fun y hy => cutoffBump_eq_one hy) (a k) x hk] with y hy
          simp [hy]
        · filter_upwards [eventually_markCut_eq_zero hL0 hζ0 (a i) x (hfar i hik)] with y hy
          simp [hy, hik]
      filter_upwards [hall] with y hy
      simp [hy]
    rw [hev.deriv_eq, deriv_const, abs_zero]
    positivity
  · have hk' (k : Fin n) : r ≤ circDist L (x - a k) := not_lt.mp fun h => hk ⟨k, h⟩
    have hq0 : |q x| ≤ A * (1 + n * r ^ (-b)) := by
      apply (hv x).trans (mul_le_mul_of_nonneg_left _ hA)
      have hs : ∑ k, max (circDist L (x - a k)) h ^ (-b) ≤ n * r ^ (-b) :=
        sum_le_card_mul fun k => Real.rpow_le_rpow_of_nonpos hr
          (le_max_of_le_left (hk' k)) (by linarith)
      linarith
    have hq1 : |deriv q x| ≤ A * (1 + n * r ^ (-1 - b)) := by
      apply (hd x).trans (mul_le_mul_of_nonneg_left _ hA)
      have hs : ∑ k, max (circDist L (x - a k)) h ^ (-1 - b) ≤ n * r ^ (-1 - b) :=
        sum_le_card_mul fun k => Real.rpow_le_rpow_of_nonpos hr
          (le_max_of_le_left (hk' k)) (by linarith)
      linarith
    have hg : ContDiff ℝ ∞ (fun y => 1 - ∑ i, markCut (cutoffBump r) L (a i) y) :=
      contDiff_const.sub (ContDiff.sum fun i _ => hχ i)
    have hg0 : |1 - ∑ i, markCut (cutoffBump r) L (a i) x| ≤ 1 + n := by
      have h1 := abs_sub (1 : ℝ) (∑ i, markCut (cutoffBump r) L (a i) x)
      have h2 := varAlPieces_abs_sum_le_card_mul fun i =>
        abs_markCut_le_one (fun y => cutoffBump_mem_Icc r y) L (a i) x
      rw [abs_one] at h1
      linarith
    have hg1 : |deriv (fun y => 1 - ∑ i, markCut (cutoffBump r) L (a i) y) x| ≤ n * M := by
      rw [((hasDerivAt_sum_fun hχ x).const_sub 1).deriv, abs_neg]
      exact varAlPieces_abs_sum_le_card_mul fun i =>
        abs_deriv_markCut_le hζ0 hL0 hLr hM (a i) x
    rw [deriv_mul_of_contDiff hg hq x]
    calc
      _ ≤ |deriv (fun y => 1 - ∑ i, markCut (cutoffBump r) L (a i) y) x * q x| +
          |(1 - ∑ i, markCut (cutoffBump r) L (a i) x) * deriv q x| := abs_add_le _ _
      _ = |deriv (fun y => 1 - ∑ i, markCut (cutoffBump r) L (a i) y) x| * |q x| +
          |1 - ∑ i, markCut (cutoffBump r) L (a i) x| * |deriv q x| := by
        rw [abs_mul, abs_mul]
      _ ≤ (n * M) * (A * (1 + n * r ^ (-b))) +
          (1 + n) * (A * (1 + n * r ^ (-1 - b))) :=
        add_le_add (mul_le_mul hg1 hq0 (abs_nonneg _) (by positivity))
          (mul_le_mul hg0 hq1 (abs_nonneg _) (by positivity))
      _ = _ := by ring

/-- A cutoff near one mark satisfies the singular derivative envelope. -/
theorem fixedCutoff_derivative_singular {n : ℕ} (a : Fin n → ℝ)
    {L r δ M A b K h : ℝ} (hL : 1 ≤ L) (hr : 0 < r) (hr16 : r ≤ 1 / 16)
    (hδ : 6 * r ≤ δ) (hsep : ∀ i k, i ≠ k → δ ≤ circDist L (a i - a k))
    (hM : ∀ x, |deriv (cutoffBump r) x| ≤ M) (hA : 0 ≤ A) (hb : 0 ≤ b)
    (hK : 1 ≤ K) (hh : K⁻¹ ≤ h) {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q)
    (hv : ∀ x, |q x| ≤ A * (1 + ∑ k, max (circDist L (x - a k)) h ^ (-b)))
    (hd : ∀ x, |deriv q x| ≤ A * (1 + ∑ k,
      max (circDist L (x - a k)) h ^ (-1 - b))) (i : Fin n) (x : ℝ) :
    |deriv (varAlPiece (cutoffBump r) L a q (Fin.castSucc i)) x| ≤
      A * (M * (1 + n + n * (4 * r) ^ (-b)) + (1 + n + n * (4 * r) ^ (-1 - b))) *
        (if circDist L (x - a i) < 1 then
          max (circDist L (x - a i)) K⁻¹ ^ (-1 - b) else 0) := by
  have hL0 : 0 < L := by linarith
  have hLr : 4 * r < L := by linarith
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hζ0 : ∀ y, 2 * r ≤ |y| → cutoffBump r y = 0 :=
    fun y hy => cutoffBump_eq_zero hr hy
  have hχ : ContDiff ℝ ∞ (markCut (cutoffBump r) L (a i)) :=
    contDiff_markCut (contDiff_cutoffBump r) hζ0 hL0 hLr (a i)
  by_cases hx : 2 * r < circDist L (x - a i)
  · have hev : varAlPiece (cutoffBump r) L a q (Fin.castSucc i) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [eventually_markCut_eq_zero hL0 hζ0 (a i) x hx] with y hy
      simp only [varAlPiece_castSucc, hy, zero_mul]
    rw [hev.deriv_eq, deriv_const, abs_zero]
    apply mul_nonneg
    · positivity
    · split_ifs
      · exact Real.rpow_nonneg (le_max_of_le_right (inv_nonneg.mpr (by linarith))) _
      · exact le_rfl
  · have hx' : circDist L (x - a i) ≤ 2 * r := not_lt.mp hx
    have hx1 : circDist L (x - a i) < 1 := by linarith
    simp only [hx1, ↓reduceIte]
    rw [varAlPiece_castSucc, deriv_mul_of_contDiff hχ hq x]
    have hq0 := (hv x).trans (mul_le_mul_of_nonneg_left
      (fixedCutoff_marked_weight a hL0 hr hr16 hδ hsep hK hh hb i hx') hA)
    have hmarked := fixedCutoff_marked_weight a hL0 hr hr16 hδ hsep hK hh
      (by linarith : 0 ≤ 1 + b) i hx'
    rw [show -(1 + b) = -1 - b by ring] at hmarked
    have hq1 := (hd x).trans (mul_le_mul_of_nonneg_left hmarked hA)
    have hW : max (circDist L (x - a i)) K⁻¹ ^ (-b) ≤
        max (circDist L (x - a i)) K⁻¹ ^ (-1 - b) :=
      Real.rpow_le_rpow_of_exponent_ge
        (lt_max_of_lt_right (inv_pos.mpr (by linarith : 0 < K)))
        (max_le hx1.le (inv_le_one_of_one_le₀ hK)) (by linarith)
    rw [← mul_assoc] at hq0 hq1
    have hc : 0 ≤ A * (1 + n + n * (4 * r) ^ (-b)) := by positivity
    have hq0' := hq0.trans (mul_le_mul_of_nonneg_left hW hc)
    calc
      _ ≤ |deriv (markCut (cutoffBump r) L (a i)) x * q x| +
          |markCut (cutoffBump r) L (a i) x * deriv q x| := abs_add_le _ _
      _ = |deriv (markCut (cutoffBump r) L (a i)) x| * |q x| +
          |markCut (cutoffBump r) L (a i) x| * |deriv q x| := by
        rw [abs_mul, abs_mul]
      _ ≤ M * (A * (1 + n + n * (4 * r) ^ (-b)) *
          max (circDist L (x - a i)) K⁻¹ ^ (-1 - b)) +
          1 * (A * (1 + n + n * (4 * r) ^ (-1 - b)) *
          max (circDist L (x - a i)) K⁻¹ ^ (-1 - b)) :=
        add_le_add (mul_le_mul (abs_deriv_markCut_le hζ0 hL0 hLr hM (a i) x)
          hq0' (abs_nonneg _) hM0)
          (mul_le_mul (abs_markCut_le_one (fun y => cutoffBump_mem_Icc r y) L (a i) x)
            hq1 (abs_nonneg _) zero_le_one)
      _ = _ := by ring

/-- Localize a smooth transport derivative by fixed disjoint cutoffs.
The regular remainder has exponent zero in the a priori derivative envelope. -/
theorem varAlPieces_derivative_cutoffs (n : ℕ) (a : Fin n → ℝ)
    {s b δ : ℝ} (hs : s < 3) (hb : 0 ≤ b) (hδ : 0 < δ) :
    ∃ D : ℝ, 0 < D ∧ ∀ (L K h A : ℝ), 1 ≤ L →
      (∀ i k, i ≠ k → δ ≤ circDist L (a i - a k)) →
      1 ≤ K → K⁻¹ ≤ h → 0 ≤ A → ∀ q : ℝ → ℝ,
      ContDiff ℝ ∞ q → Function.Periodic q L →
      (∀ x, |q x| ≤ A * (1 + ∑ k, max (circDist L (x - a k)) h ^ (-b))) →
      (∀ x, |deriv q x| ≤ A * (1 + ∑ k,
        max (circDist L (x - a k)) h ^ (-1 - b))) →
      (∀ x, 4 ≤ circDist L x → |deriv q x| ≤ A * circDist L x ^ (s - 3)) →
      ∃ φ : Fin (n + 1) → ℝ → ℝ,
        (∀ j, ContDiff ℝ ∞ (φ j) ∧ Function.Periodic (φ j) L) ∧
        (∀ x, ∑ j, φ j x = q x) ∧
        (∀ j x, |deriv (φ j) x| ≤ D * A * gradWeightTwo s
          (Fin.lastCases 0 (fun _ : Fin n => b) j) K L (x - Fin.lastCases 0 a j)) := by
  classical
  let r := min (δ / 6) (1 / 16)
  have hr : 0 < r := lt_min (by linarith) (by norm_num)
  have hr16 : r ≤ 1 / 16 := min_le_right _ _
  have hδr : 6 * r ≤ δ := by linarith [min_le_left (δ / 6) (1 / 16)]
  have hζ0 : ∀ x, 2 * r ≤ |x| → cutoffBump r x = 0 :=
    fun x hx => cutoffBump_eq_zero hr hx
  obtain ⟨M, _, hM, _⟩ := exists_bounds_deriv_bump (contDiff_cutoffBump r) hζ0
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  let R := 4 + ∑ i, |a i|
  have hR4 : 4 ≤ R := le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  have hRa (i : Fin n) : |a i| ≤ R - 4 := by
    dsimp [R]
    simpa only [add_sub_cancel_left] using
      Finset.single_le_sum (f := fun i => |a i|) (fun i _ => abs_nonneg _) (Finset.mem_univ i)
  let S₀ := M * (1 + n + n * (4 * r) ^ (-b)) + (1 + n + n * (4 * r) ^ (-1 - b))
  let R₀ := n * M * (1 + n * r ^ (-b)) + (1 + n) * (1 + n * r ^ (-1 - b))
  have hS₀ : 0 ≤ S₀ := by dsimp [S₀]; positivity
  have hR₀ : 0 ≤ R₀ := by dsimp [R₀]; positivity
  have hRp : 0 ≤ R ^ (3 - s) := Real.rpow_nonneg (by linarith) _
  let D := 1 + S₀ + R₀ * (1 + R ^ (3 - s))
  have hD : 0 < D := by dsimp [D]; positivity
  have hDS : S₀ ≤ D := by dsimp [D]; nlinarith
  have hDR : R₀ ≤ D := by dsimp [D]; nlinarith
  have hDRp : R₀ * R ^ (3 - s) ≤ D := by dsimp [D]; nlinarith
  have hD1 : 1 ≤ D := by dsimp [D]; nlinarith
  refine ⟨D, hD, fun L K h A hL hsep hK hh hA q hq hp hv hd ht => ?_⟩
  have hL0 : 0 < L := by linarith
  have hLr : 4 * r < L := by linarith
  have hfar (x : ℝ) (hx : R ≤ circDist L x) (i : Fin n) :
      2 * r < circDist L (x - a i) := by
    have h1 := circDist_add_le hL0 (x - a i) (a i)
    rw [sub_add_cancel] at h1
    have h2 := circDist_le_abs' hL0 (a i)
    linarith [hRa i]
  refine ⟨varAlPiece (cutoffBump r) L a q,
    fun j => ⟨contDiff_varAlPiece (contDiff_cutoffBump r) hζ0 hL0 hLr a hq j,
      periodic_varAlPiece hL0 a hp j⟩, sum_varAlPiece (cutoffBump r) L a q, fun j => ?_⟩
  refine Fin.lastCases ?_ (fun i => ?_) j
  · intro x
    simp only [Fin.lastCases_last, sub_zero]
    unfold gradWeightTwo
    rw [add_zero]
    have hg : |deriv (varAlPiece (cutoffBump r) L a q (Fin.last n)) x| ≤ A * R₀ :=
      fixedCutoff_derivative_remainder a hL hr hr16 hδr hsep hM hA hb hq hv hd x
    exact weighted_remainder_bound (k := 3) (s := s) (A0 := A * R₀) (Ct := A) (R := R)
      (K := D * A) (circDist_nonneg _ _) (by linarith) hs
      (fun hx => one_le_weight_of_lt hx hK (by norm_num)) hg
      (fun hx => by
        rw [(remainder_eq_near hL0 hζ0 a q (hfar x hx)).1]
        exact ht x (hR4.trans hx))
      (by nlinarith [mul_le_mul_of_nonneg_left hDRp hA])
      (by nlinarith [mul_le_mul_of_nonneg_left hDR hA])
      (by nlinarith [mul_le_mul_of_nonneg_right hD1 hA]) (mul_nonneg hD.le hA)
  · intro x
    simp only [Fin.lastCases_castSucc]
    have hg := fixedCutoff_derivative_singular a hL hr hr16 hδr hsep hM hA hb hK hh hq hv hd i x
    change |deriv (varAlPiece (cutoffBump r) L a q (Fin.castSucc i)) x| ≤ A * S₀ * _ at hg
    unfold gradWeightTwo
    rw [show -(1 + b) = -1 - b by ring]
    split_ifs at hg ⊢ with hx
    · exact hg.trans (mul_le_mul_of_nonneg_right
        (by nlinarith [mul_le_mul_of_nonneg_left hDS hA] : A * S₀ ≤ D * A)
        (Real.rpow_nonneg (le_max_of_le_left (circDist_nonneg _ _)) _))
    · rw [mul_zero] at hg
      exact hg.trans (mul_nonneg (mul_nonneg hD.le hA)
        (Real.rpow_nonneg (circDist_nonneg _ _) _))

end Riesz1.Internal
