/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.GradientSplittingWindowKernel

/-!
# Truncated integration by parts for the kernel `g'`

Let `g = hurwitzKernel s` and `G = deriv g`. For a coefficient `Φ` of class `C¹` the integrand
`Φ G` is not integrable at the integers, but its integrals over the allowed set
`A_δ = {v : |v - m| ≥ δ for every m ∈ ℤ}` are well defined. This file proves the truncated formula

`∫_{A_δ ∩ [c,d]} Φ K = Φ(d) A(d) - Φ(c) A(c) + ∑_{k ∈ (⌊c⌋, ⌊d⌋]} (Φ(k-δ)A(k-δ) - Φ(k+δ)A(k+δ))
  - ∫_{A_δ ∩ [c,d]} Φ' A`

for an antiderivative `A` of `K` on `A_δ` (the free pieces are integrated by parts, the cells around
the integers contribute nothing). The principal value of `Φ G` over `[a, b]` is the limit of these
truncated integrals as `δ ↓ 0` (`tendsto_truncated_by_parts`), see `GradientSplittingWindowPV`.

The allowed set, the truncated integrals and the cell lemmas are stated for real `δ`. The integers
enter through `Int.floor`.
-/

@[expose] public section

open Set MeasureTheory Filter Topology intervalIntegral
open scoped ContDiff

namespace Riesz1

noncomputable section

/-- The allowed set `A_δ`: points at distance at least `δ` from every integer. The truncated
integrals of the principal values keep exactly these points. -/
def gradAllowed (δ : ℝ) : Set ℝ := {v : ℝ | ∀ m : ℤ, δ ≤ |v - m|}

lemma gradAllowed_isClosed (δ : ℝ) : IsClosed (gradAllowed δ) := by
  have h : gradAllowed δ = ⋂ m : ℤ, {v : ℝ | δ ≤ |v - m|} := by
    ext v
    simp [gradAllowed]
  rw [h]
  exact isClosed_iInter fun m => isClosed_le continuous_const (by fun_prop)

/-- Two allowed points with no integer strictly between them span an allowed interval. -/
lemma gradAllowed_of_between {δ c d v : ℝ} (hc : c ∈ gradAllowed δ) (hd : d ∈ gradAllowed δ)
    (hno : ∀ m : ℤ, ¬ (c < m ∧ (m : ℝ) < d)) (hv : v ∈ Icc c d) : v ∈ gradAllowed δ := by
  intro m
  rcases le_or_gt (m : ℝ) c with h | h
  · have h1 : |v - m| = v - m := abs_of_nonneg (by linarith [hv.1])
    have h2 : |c - m| = c - m := abs_of_nonneg (by linarith)
    have h3 := hc m
    rw [h2] at h3
    rw [h1]
    linarith [hv.1]
  · rcases le_or_gt d (m : ℝ) with h' | h'
    · have h1 : |v - m| = -(v - m) := abs_of_nonpos (by linarith [hv.2])
      have h2 : |d - m| = -(d - m) := abs_of_nonpos (by linarith)
      have h3 := hd m
      rw [h2] at h3
      rw [h1]
      linarith [hv.2]
    · exact absurd ⟨h, h'⟩ (hno m)

/-- The points `m ± δ` are allowed when `0 < δ < 1/2`. -/
lemma gradAllowed_cell_endpoints {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1 / 2) (m : ℤ) :
    (m : ℝ) - δ ∈ gradAllowed δ ∧ (m : ℝ) + δ ∈ gradAllowed δ := by
  have key : ∀ k : ℤ, k ≠ m → (1 : ℝ) ≤ |(m : ℝ) - k| := by
    intro k hk
    have hz : (1 : ℤ) ≤ |m - k| := Int.one_le_abs (sub_ne_zero.mpr (Ne.symm hk))
    have : ((|m - k| : ℤ) : ℝ) = |(m : ℝ) - k| := by push_cast; rfl
    rw [← this]
    exact_mod_cast hz
  constructor
  · intro k
    by_cases hk : k = m
    · subst hk
      simp [abs_of_pos hδ0]
    · have h1 := key k hk
      have h3 : |(m : ℝ) - δ - k| = |((m : ℝ) - k) - δ| := by ring_nf
      rw [h3]
      have := abs_sub_abs_le_abs_sub ((m : ℝ) - k) δ
      rw [abs_of_pos hδ0] at this
      linarith
  · intro k
    by_cases hk : k = m
    · subst hk
      simp [abs_of_pos hδ0]
    · have h1 := key k hk
      have h3 : |(m : ℝ) + δ - k| = |((m : ℝ) - k) - (-δ)| := by ring_nf
      rw [h3]
      have := abs_sub_abs_le_abs_sub ((m : ℝ) - k) (-δ)
      rw [abs_neg, abs_of_pos hδ0] at this
      linarith

/-- An allowed point is not an integer, and it is not in the open `δ`-neighbourhood of an integer. -/
lemma not_mem_gradAllowed_of_abs_lt {δ v : ℝ} {m : ℤ} (h : |v - m| < δ) :
    v ∉ gradAllowed δ := fun hv => absurd (hv m) (not_le.mpr h)

/-- An indicator of a closed set, of a function continuous on that set, is interval integrable. -/
lemma intervalIntegrable_indicator_of_continuousOn {S : Set ℝ} (hS : IsClosed S) {F : ℝ → ℝ}
    (hF : ContinuousOn F S) (c d : ℝ) : IntervalIntegrable (S.indicator F) volume c d := by
  have hcpt : IsCompact (uIcc c d ∩ S) := isCompact_uIcc.inter_right hS
  obtain ⟨M, hM⟩ := hcpt.exists_bound_of_continuousOn (hF.mono inter_subset_right)
  rw [intervalIntegrable_iff]
  refine Measure.integrableOn_of_bounded (M := max M 0) ?_ ?_ ?_
  · exact ((measure_mono Set.uIoc_subset_uIcc).trans_lt isCompact_uIcc.measure_lt_top).ne
  · exact (aestronglyMeasurable_indicator_iff hS.measurableSet).2
      (hF.aestronglyMeasurable hS.measurableSet)
  · refine (ae_restrict_mem measurableSet_uIoc).mono fun x hx => ?_
    have hxI : x ∈ uIcc c d := Set.uIoc_subset_uIcc hx
    by_cases hxS : x ∈ S
    · rw [indicator_of_mem hxS]
      exact (hM x ⟨hxI, hxS⟩).trans (le_max_left _ _)
    · rw [indicator_of_notMem hxS]
      simp

/-- Integration by parts on a free piece: if `A' = K` on `[c, d]`, then
`∫ Φ K = Φ(d) A(d) - Φ(c) A(c) - ∫ Φ' A`. -/
lemma integral_mul_kernel_free {Φ K A : ℝ → ℝ} (hΦ : ContDiff ℝ 1 Φ) {c d : ℝ}
    (hA : ∀ v ∈ uIcc c d, HasDerivAt A (K v) v) (hK : ContinuousOn K (uIcc c d)) :
    ∫ v in c..d, Φ v * K v = Φ d * A d - Φ c * A c - ∫ v in c..d, deriv Φ v * A v := by
  have hu : ∀ x ∈ uIcc c d, HasDerivAt Φ (deriv Φ x) x := fun x _ =>
    ((hΦ.differentiable (by simp)) x).hasDerivAt
  have hdΦ : Continuous (deriv Φ) := hΦ.continuous_deriv (by simp)
  exact intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hA (hdΦ.intervalIntegrable _ _)
    (hK.intervalIntegrable)

/-- The integral over a cell `[m - δ, m + δ]` of the truncated integrand vanishes: every point of
the open cell is excluded, and the endpoint `m + δ` is a null set. -/
lemma integral_indicator_cell_eq_zero {δ : ℝ} (hδ0 : 0 < δ) (F : ℝ → ℝ) (m : ℤ) :
    ∫ v in ((m : ℝ) - δ)..((m : ℝ) + δ), (gradAllowed δ).indicator F v = 0 := by
  have hle : (m : ℝ) - δ ≤ (m : ℝ) + δ := by linarith
  rw [intervalIntegral.integral_congr_ae (g := fun _ => (0 : ℝ))]
  · simp
  · have hnull : ∀ᵐ v ∂(volume : Measure ℝ), v ∉ ({(m : ℝ) + δ} : Set ℝ) :=
      (Set.countable_singleton _).ae_notMem _
    refine hnull.mono fun v hv hvI => ?_
    rw [uIoc_of_le hle] at hvI
    have hvne : v ≠ (m : ℝ) + δ := fun h => hv (by simp [h])
    have hlt : |v - m| < δ := by
      rw [abs_lt]
      constructor
      · linarith [hvI.1]
      · exact lt_of_le_of_ne hvI.2 hvne |>.trans_le' le_rfl |> fun h => by linarith
    exact indicator_of_notMem (not_mem_gradAllowed_of_abs_lt hlt) _


/-- Splitting off the first integer of a discrete interval: `(a, b] = {a+1} ∪ (a+1, b]`. -/
lemma sum_Ioc_split_left (f : ℤ → ℝ) {a b : ℤ} (h : a < b) :
    ∑ k ∈ Finset.Ioc a b, f k = f (a + 1) + ∑ k ∈ Finset.Ioc (a + 1) b, f k := by
  have hset : Finset.Ioc a b = insert (a + 1) (Finset.Ioc (a + 1) b) := by
    ext k
    simp only [Finset.mem_Ioc, Finset.mem_insert]
    omega
  rw [hset, Finset.sum_insert (by simp)]

/-- On a set of points that is an interval of allowed points, the indicator is the function. -/
lemma integral_indicator_eq_of_uIcc_mem {S : Set ℝ} {c d : ℝ} (h : ∀ v ∈ uIcc c d, v ∈ S)
    (F : ℝ → ℝ) : ∫ v in c..d, S.indicator F v = ∫ v in c..d, F v := by
  apply intervalIntegral.integral_congr
  intro v hv
  exact indicator_of_mem (h v hv) F

/-- Truncated integration by parts (identity part of Lemma 5.7, the principal
value of `Φ g'`). Induction on `⌊d⌋ - ⌊c⌋`: the first integer above `c` is split off, its cell
contributes nothing, and the rest is handled by the induction hypothesis. -/
theorem gradTrunc_formula {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1 / 2) {Φ K A : ℝ → ℝ}
    (hΦ : ContDiff ℝ 1 Φ) (hA : ∀ v ∈ gradAllowed δ, HasDerivAt A (K v) v)
    (hK : ContinuousOn K (gradAllowed δ)) (hA' : ContinuousOn A (gradAllowed δ)) :
    ∀ n : ℕ, ∀ c d : ℝ, c ≤ d → c ∈ gradAllowed δ → d ∈ gradAllowed δ →
      ⌊d⌋ - ⌊c⌋ = (n : ℤ) →
      ∫ v in c..d, (gradAllowed δ).indicator (fun v => Φ v * K v) v
        = Φ d * A d - Φ c * A c
          + ∑ k ∈ Finset.Ioc ⌊c⌋ ⌊d⌋,
              (Φ ((k : ℝ) - δ) * A ((k : ℝ) - δ) - Φ ((k : ℝ) + δ) * A ((k : ℝ) + δ))
          - ∫ v in c..d, (gradAllowed δ).indicator (fun v => deriv Φ v * A v) v := by
  have hSc := gradAllowed_isClosed δ
  have hFK : ContinuousOn (fun v => Φ v * K v) (gradAllowed δ) :=
    hΦ.continuous.continuousOn.mul hK
  have hFA : ContinuousOn (fun v => deriv Φ v * A v) (gradAllowed δ) :=
    (hΦ.continuous_deriv (by simp)).continuousOn.mul hA'
  have intFK : ∀ c d : ℝ, IntervalIntegrable ((gradAllowed δ).indicator (fun v => Φ v * K v))
      volume c d := fun c d => intervalIntegrable_indicator_of_continuousOn hSc hFK c d
  have intFA : ∀ c d : ℝ, IntervalIntegrable ((gradAllowed δ).indicator (fun v => deriv Φ v * A v))
      volume c d := fun c d => intervalIntegrable_indicator_of_continuousOn hSc hFA c d
  intro n
  induction n with
  | zero =>
    intro c d hcd hc hd hn
    rw [Nat.cast_zero, sub_eq_zero] at hn
    have hnoint : ∀ m : ℤ, ¬ (c < m ∧ (m : ℝ) < d) := by
      rintro m ⟨h1, h2⟩
      have a1 : ⌊c⌋ < m := Int.floor_lt.2 h1
      have a2 : m ≤ ⌊d⌋ := Int.le_floor.2 h2.le
      omega
    have hfree : ∀ v ∈ uIcc c d, v ∈ gradAllowed δ := fun v hv =>
      gradAllowed_of_between hc hd hnoint (by rw [uIcc_of_le hcd] at hv; exact hv)
    rw [integral_indicator_eq_of_uIcc_mem hfree, integral_indicator_eq_of_uIcc_mem hfree]
    have hsum : ∑ k ∈ Finset.Ioc ⌊c⌋ ⌊d⌋,
        (Φ ((k : ℝ) - δ) * A ((k : ℝ) - δ) - Φ ((k : ℝ) + δ) * A ((k : ℝ) + δ)) = 0 := by
      rw [hn, Finset.Ioc_self, Finset.sum_empty]
    have key := integral_mul_kernel_free hΦ (fun v hv => hA v (hfree v hv))
      (hK.mono (fun v hv => hfree v hv))
    rw [hsum, key]
    ring
  | succ n ih =>
    intro c d hcd hc hd hn
    push_cast at hn
    set m : ℤ := ⌊c⌋ + 1 with hm
    have hcm : c < m := by
      have := Int.lt_floor_add_one c
      rw [hm]
      exact_mod_cast this
    have hmd' : (m : ℝ) ≤ d := by
      have h1 : m ≤ ⌊d⌋ := by omega
      exact (show (m : ℝ) ≤ (⌊d⌋ : ℝ) by exact_mod_cast h1).trans (Int.floor_le d)
    have hmd : (m : ℝ) < d := by
      refine lt_of_le_of_ne hmd' fun h => ?_
      have := hd m
      rw [← h, sub_self, abs_zero] at this
      linarith
    obtain ⟨hme, hpe⟩ := gradAllowed_cell_endpoints hδ0 hδ1 m
    have hcl : c ≤ (m : ℝ) - δ := by
      have h := hc m
      rw [abs_of_neg (by linarith : c - m < 0)] at h
      linarith
    have hcr : (m : ℝ) + δ ≤ d := by
      have h := hd m
      rw [abs_of_pos (by linarith : (0 : ℝ) < d - m)] at h
      linarith
    -- the first piece `[c, m - δ]` is free
    have hfree1 : ∀ v ∈ uIcc c ((m : ℝ) - δ), v ∈ gradAllowed δ := by
      intro v hv
      refine gradAllowed_of_between hc hme (fun k hk => ?_) (by rw [uIcc_of_le hcl] at hv; exact hv)
      have a1 : ⌊c⌋ < k := Int.floor_lt.2 hk.1
      have a2 : m ≤ k := by omega
      have a3 : (m : ℝ) ≤ k := by exact_mod_cast a2
      linarith [hk.2]
    -- the last piece `[m + δ, d]` is handled by induction
    have hfloor : ⌊(m : ℝ) + δ⌋ = m := Int.floor_eq_iff.2 ⟨by linarith, by linarith⟩
    have hn' : ⌊d⌋ - ⌊(m : ℝ) + δ⌋ = (n : ℤ) := by rw [hfloor]; omega
    have IH := ih ((m : ℝ) + δ) d hcr hpe hd hn'
    rw [hfloor] at IH
    -- splitting of both integrals at the cell `[m - δ, m + δ]`
    have hsplitK : ∫ v in c..d, (gradAllowed δ).indicator (fun v => Φ v * K v) v
        = (∫ v in c..((m : ℝ) - δ), (gradAllowed δ).indicator (fun v => Φ v * K v) v)
          + (∫ v in ((m : ℝ) + δ)..d, (gradAllowed δ).indicator (fun v => Φ v * K v) v) := by
      rw [← intervalIntegral.integral_add_adjacent_intervals (intFK c ((m : ℝ) - δ))
          (intFK ((m : ℝ) - δ) d),
        ← intervalIntegral.integral_add_adjacent_intervals
          (intFK ((m : ℝ) - δ) ((m : ℝ) + δ)) (intFK ((m : ℝ) + δ) d),
        integral_indicator_cell_eq_zero hδ0 _ m, zero_add]
    have hsplitA : ∫ v in c..d, (gradAllowed δ).indicator (fun v => deriv Φ v * A v) v
        = (∫ v in c..((m : ℝ) - δ), (gradAllowed δ).indicator (fun v => deriv Φ v * A v) v)
          + (∫ v in ((m : ℝ) + δ)..d, (gradAllowed δ).indicator (fun v => deriv Φ v * A v) v) := by
      rw [← intervalIntegral.integral_add_adjacent_intervals (intFA c ((m : ℝ) - δ))
          (intFA ((m : ℝ) - δ) d),
        ← intervalIntegral.integral_add_adjacent_intervals
          (intFA ((m : ℝ) - δ) ((m : ℝ) + δ)) (intFA ((m : ℝ) + δ) d),
        integral_indicator_cell_eq_zero hδ0 _ m, zero_add]
    -- the first piece is free
    have hI1 : ∫ v in c..((m : ℝ) - δ), (gradAllowed δ).indicator (fun v => Φ v * K v) v
        = Φ ((m : ℝ) - δ) * A ((m : ℝ) - δ) - Φ c * A c
          - ∫ v in c..((m : ℝ) - δ), (gradAllowed δ).indicator (fun v => deriv Φ v * A v) v := by
      rw [integral_indicator_eq_of_uIcc_mem hfree1, integral_indicator_eq_of_uIcc_mem hfree1]
      exact integral_mul_kernel_free hΦ (fun v hv => hA v (hfree1 v hv))
        (hK.mono (fun v hv => hfree1 v hv))
    -- the sums over the integers in `(⌊c⌋, ⌊d⌋]`
    have hlt : ⌊c⌋ < ⌊d⌋ := by omega
    have hsumsplit : ∑ k ∈ Finset.Ioc ⌊c⌋ ⌊d⌋,
        (Φ ((k : ℝ) - δ) * A ((k : ℝ) - δ) - Φ ((k : ℝ) + δ) * A ((k : ℝ) + δ))
        = (Φ ((m : ℝ) - δ) * A ((m : ℝ) - δ) - Φ ((m : ℝ) + δ) * A ((m : ℝ) + δ))
          + ∑ k ∈ Finset.Ioc m ⌊d⌋,
              (Φ ((k : ℝ) - δ) * A ((k : ℝ) - δ) - Φ ((k : ℝ) + δ) * A ((k : ℝ) + δ)) :=
      sum_Ioc_split_left (fun k : ℤ => Φ ((k : ℝ) - δ) * A ((k : ℝ) - δ)
        - Φ ((k : ℝ) + δ) * A ((k : ℝ) + δ)) hlt
    rw [hsplitK, hsplitA, hI1, IH, hsumsplit]
    -- the first-piece integral of `Φ' A` is the restriction of the indicator
    have hI1A : ∫ v in c..((m : ℝ) - δ), (gradAllowed δ).indicator (fun v => deriv Φ v * A v) v
        = ∫ v in c..((m : ℝ) - δ), deriv Φ v * A v :=
      integral_indicator_eq_of_uIcc_mem hfree1 _
    rw [hI1A]
    ring

end

end Riesz1
