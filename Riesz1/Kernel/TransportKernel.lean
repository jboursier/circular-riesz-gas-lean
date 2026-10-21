/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Kernel.TransportSums

/-!
# The transport kernel `K_{s,L}` on circles of arbitrary length

For `0 < s < 1`, the kernel `K_s` is the limit of the symmetric sums
`∑_{k=-M}^{M} sgn(t - k)|t - k|^{s-1}`. Away from the integers, the terms with `k ≠ 0, t` are
smooth and paired: `φ(t-k) + φ(t+k)` with `φ = signPow s` is `O(k^{s-2})` uniformly on
`|t| ≤ 1/2`. This file uses the pairing to prove, for the unit kernel, that

* the symmetric partial sums converge to `K_s` pointwise off `ℤ`, and in `L¹(-1/2, 1/2)`.

and then transports these facts to `K_{s,L}(r) = L^{s-1} K_s(r/L)` on `[-L/2, L/2]`.

The pairing bound is the mean value inequality for `φ` on `[c, ∞)`, where
`|φ'(w)| = (1-s)|w|^{s-2} ≤ (1-s)c^{s-2}`.
-/

public section

open MeasureTheory Set intervalIntegral Filter Topology
open scoped ContDiff Real

namespace Riesz1

/-- The mean value inequality for the signed power on `[c, ∞)`, `c > 0`. -/
lemma abs_signPow_sub_le_of_le {s c a b : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hc : 0 < c)
    (ha : c ≤ a) (hb : c ≤ b) :
    |signPow s b - signPow s a| ≤ (1 - s) * c ^ (s - 2) * |b - a| := by
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (𝕜 := ℝ)
    (f := fun w : ℝ => signPow s w) (f' := fun w : ℝ => (s - 1) * |w| ^ (s - 2))
    (s := Ici c) (C := (1 - s) * c ^ (s - 2))
    (fun w hw => (hasDerivAt_signPow (s := s) (u := w) (by
      have : c ≤ w := hw
      linarith)).hasDerivWithinAt)
    (fun w hw => by
      have hw' : c ≤ w := hw
      have hw0 : 0 < w := lt_of_lt_of_le hc hw'
      have e : |(s - 1) * |w| ^ (s - 2)| = (1 - s) * w ^ (s - 2) := by
        rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg w) _),
          abs_of_neg (by linarith : s - 1 < 0), abs_of_pos hw0]
        ring
      rw [Real.norm_eq_abs, e]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (by linarith) hw'
        (by linarith)) (by linarith))
    (convex_Ici c) (show a ∈ Ici c from ha) (show b ∈ Ici c from hb)
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hmvt
  exact hmvt

/-- The signed power is odd. -/
lemma signPow_neg' (s u : ℝ) : signPow s (-u) = -signPow s u := by
  unfold signPow
  rw [Real.sign_neg, abs_neg]
  ring

/-- The paired kernel terms `φ(t-u) + φ(t+u)` for `u ≥ 1` and `|t| ≤ 1/2`: they are bounded by
`(1-s)(u - 1/2)^{s-2}`, which is summable over `u` in the integers. -/
lemma abs_signPow_pair_le {s t u : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (ht : |t| ≤ 1 / 2)
    (hu : 1 ≤ u) :
    |signPow s (t - u) + signPow s (t + u)| ≤ (1 - s) * (u - 1 / 2) ^ (s - 2) := by
  have hc : 0 < u - 1 / 2 := by linarith
  have ht' := abs_le.1 ht
  have hodd : signPow s (t - u) = -signPow s (u - t) := by
    rw [← signPow_neg', neg_sub]
  rw [hodd, neg_add_eq_sub]
  have h := abs_signPow_sub_le_of_le (s := s) (c := u - 1 / 2) (a := u - t) (b := t + u) hs0 hs1
    hc (by linarith) (by linarith)
  calc |signPow s (t + u) - signPow s (u - t)|
      ≤ (1 - s) * (u - 1 / 2) ^ (s - 2) * |t + u - (u - t)| := h
    _ ≤ (1 - s) * (u - 1 / 2) ^ (s - 2) * 1 := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by linarith) (Real.rpow_nonneg hc.le _))
        rw [show t + u - (u - t) = 2 * t by ring, abs_mul, abs_two]
        linarith
    _ = (1 - s) * (u - 1 / 2) ^ (s - 2) := mul_one _

/-- The symmetric sum over `[-M, M]` is the central term plus the paired terms. -/
lemma sum_Icc_symm_eq (φ : ℝ → ℝ) (t : ℝ) (M : ℕ) :
    ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), φ (t - k) =
      φ t + ∑ k ∈ Finset.range M, (φ (t - ((k : ℤ) + 1 : ℤ)) + φ (t + ((k : ℤ) + 1 : ℤ))) := by
  induction M with
  | zero => simp
  | succ M ih =>
    have hIcc : Finset.Icc (-((M + 1 : ℕ) : ℤ)) ((M + 1 : ℕ) : ℤ) =
        insert (-((M : ℤ) + 1)) (insert ((M : ℤ) + 1) (Finset.Icc (-(M : ℤ)) (M : ℤ))) := by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_insert]
      push_cast
      omega
    have hnot1 : -((M : ℤ) + 1) ∉ insert ((M : ℤ) + 1) (Finset.Icc (-(M : ℤ)) (M : ℤ)) := by
      simp only [Finset.mem_insert, Finset.mem_Icc, not_or, not_and, not_le]
      constructor
      · omega
      · intro _; omega
    have hnot2 : (M : ℤ) + 1 ∉ Finset.Icc (-(M : ℤ)) (M : ℤ) := by
      simp only [Finset.mem_Icc, not_and, not_le]
      intro _; omega
    rw [hIcc, Finset.sum_insert hnot1, Finset.sum_insert hnot2, ih, Finset.sum_range_succ]
    push_cast
    ring_nf

/-- The `(k+1)`-th pair `φ(t-(k+1)) + φ(t+(k+1))` with the exponent cast. -/
lemma abs_signPow_pair_nat_le {s t : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (ht : |t| ≤ 1 / 2)
    (k : ℕ) :
    |signPow s (t - ((k : ℤ) + 1 : ℤ)) + signPow s (t + ((k : ℤ) + 1 : ℤ))| ≤
      (1 - s) * ((k : ℝ) + 1 / 2) ^ (s - 2) := by
  have hu : (1 : ℝ) ≤ (k : ℝ) + 1 := by
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  have h := abs_signPow_pair_le hs0 hs1 ht hu
  push_cast at h ⊢
  have e : (k : ℝ) + 1 - 1 / 2 = (k : ℝ) + 1 / 2 := by ring
  rw [e] at h
  exact h

/-- The summability of the pair bounds `(k + 1/2)^{s-2}` over `k ∈ ℕ`. -/
lemma summable_pair_bound {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    Summable fun k : ℕ => (1 - s) * ((k : ℝ) + 1 / 2) ^ (s - 2) := by
  have h : Summable fun n : ℕ => (n : ℝ) ^ (s - 2) := Real.summable_nat_rpow.2 (by linarith)
  have hsh : Summable fun k : ℕ => ((k : ℝ) + 1) ^ (s - 2) := by
    have := (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ (s - 2)) 1).2 h
    simpa using this
  suffices hbd : Summable fun k : ℕ => ((k : ℝ) + 1 / 2) ^ (s - 2) from hbd.mul_left (1 - s)
  refine Summable.of_nonneg_of_le (fun k => Real.rpow_nonneg (by positivity) _) (fun k => ?_)
    (hsh.mul_left (2 ^ (2 - s)))
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hpos : 0 < (k : ℝ) + 1 / 2 := by linarith
  have hle : ((k : ℝ) + 1) / 2 ≤ (k : ℝ) + 1 / 2 := by linarith
  have h1 : ((k : ℝ) + 1 / 2) ^ (s - 2) ≤ (((k : ℝ) + 1) / 2) ^ (s - 2) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) hle (by linarith)
  rw [Real.div_rpow (by linarith) (by norm_num), show (2 : ℝ) ^ (s - 2) = (2 ^ (2 - s))⁻¹ by
    rw [← Real.rpow_neg (by norm_num), neg_sub]] at h1
  have h2 : (((k : ℝ) + 1) ^ (s - 2)) / (2 ^ (2 - s))⁻¹ = (2 ^ (2 - s)) * ((k : ℝ) + 1) ^ (s - 2) := by
    rw [div_inv_eq_mul]
    ring
  rw [h2] at h1
  exact h1

/-- The signed power is measurable in its argument `t - k`. -/
lemma measurable_signPow_shift (s : ℝ) (k : ℤ) : Measurable fun t : ℝ => signPow s (t - k) := by
  unfold signPow
  exact (measurable_realSign.comp (by fun_prop)).mul (by fun_prop)

/-- The symmetric partial sums of the signed power converge to `K_s` off the integers. -/
lemma tendsto_symmetric_signPow {s t : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (ht : ∀ k : ℤ, t ≠ k) :
    Tendsto (fun M : ℕ => ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), signPow s (t - k)) atTop
      (𝓝 (periodicKernel s t)) := by
  have h := tendsto_symmetricPartialSum hs0 hs1 ht
  simpa only [signPow] using h

/-- The paired bound on the symmetric partial sums on `|t| ≤ 1/2`:
`|∑_{|k| ≤ M} φ(t-k)| ≤ |t|^{s-1} + ∑_k (1-s)(k+1/2)^{s-2}`. -/
lemma abs_sum_signPow_le {s t : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (ht : |t| ≤ 1 / 2) (M : ℕ) :
    |∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), signPow s (t - k)| ≤
      |t| ^ (s - 1) + ∑' k : ℕ, (1 - s) * ((k : ℝ) + 1 / 2) ^ (s - 2) := by
  rw [sum_Icc_symm_eq (signPow s) t M]
  have hsum := summable_pair_bound hs0 hs1
  calc |signPow s t + ∑ k ∈ Finset.range M,
        (signPow s (t - ((k : ℤ) + 1 : ℤ)) + signPow s (t + ((k : ℤ) + 1 : ℤ)))|
      ≤ |signPow s t| + |∑ k ∈ Finset.range M,
        (signPow s (t - ((k : ℤ) + 1 : ℤ)) + signPow s (t + ((k : ℤ) + 1 : ℤ)))| := abs_add_le _ _
    _ ≤ |t| ^ (s - 1) + ∑ k ∈ Finset.range M, (1 - s) * ((k : ℝ) + 1 / 2) ^ (s - 2) := by
        gcongr
        · exact (abs_signPow_le s t)
        · exact (Finset.abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum fun k _ => abs_signPow_pair_nat_le hs0 hs1 ht k)
    _ ≤ |t| ^ (s - 1) + ∑' k : ℕ, (1 - s) * ((k : ℝ) + 1 / 2) ^ (s - 2) := by
        gcongr
        exact hsum.sum_le_tsum _ (fun k _ => mul_nonneg (by linarith)
          (Real.rpow_nonneg (by positivity) _))

/-- Almost every real number avoids the integers, for any measure without atoms. -/
lemma ae_ne_int (μ : Measure ℝ) [NullSingletonClass μ] :
    ∀ᵐ t ∂μ, ∀ k : ℤ, t ≠ (k : ℝ) := by
  have hcount : (Set.range (fun k : ℤ => (k : ℝ))).Countable := Set.countable_range _
  filter_upwards [hcount.ae_notMem μ] with t ht k hk
  exact ht ⟨k, hk.symm⟩

/-- Restriction to an interval keeps the almost-everywhere avoidance of the integers. -/
lemma ae_restrict_ne_int (A : Set ℝ) : ∀ᵐ t ∂(volume.restrict A), ∀ k : ℤ, t ≠ (k : ℝ) :=
  ae_restrict_of_ae (ae_ne_int volume)

/-- **The unit kernel: `L¹` convergence of the symmetric partial sums on `[-1/2, 1/2]`.** -/
theorem tendsto_symmetric_signPow_L1 {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    Tendsto (fun M : ℕ => ∫ t in (-(1 / 2 : ℝ))..(1 / 2),
      |∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), signPow s (t - k) - periodicKernel s t|)
      atTop (𝓝 0) := by
  set C : ℝ := ∑' k : ℕ, (1 - s) * ((k : ℝ) + 1 / 2) ^ (s - 2) with hC
  set G : ℝ → ℝ := fun t => |t| ^ (s - 1) + C with hG
  set μ := volume.restrict (Ioc (-(1 / 2 : ℝ)) (1 / 2)) with hμ
  -- off the integers, the sums converge. The set of integers is null
  have hae : ∀ᵐ t ∂μ, ∀ k : ℤ, t ≠ (k : ℝ) := ae_restrict_ne_int _
  have hIoc : ∀ t ∈ Ioc (-(1 / 2 : ℝ)) (1 / 2), |t| ≤ 1 / 2 := fun t ht => by
    rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
  have hK_le : ∀ t : ℝ, |t| ≤ 1 / 2 → (∀ k : ℤ, t ≠ k) → |periodicKernel s t| ≤ G t := by
    intro t ht hint
    have hlim := (tendsto_symmetric_signPow hs0 hs1 hint).abs
    refine le_of_tendsto hlim (Eventually.of_forall fun M => ?_)
    exact (abs_sum_signPow_le hs0 hs1 ht M).trans (le_refl _)
  have hmeas : ∀ M : ℕ, Measurable fun t : ℝ =>
      ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), signPow s (t - k) := fun M =>
    Finset.measurable_sum _ fun k _ => measurable_signPow_shift s k
  have hGint : IntegrableOn G (Ioc (-(1 / 2 : ℝ)) (1 / 2)) := by
    have h1 : IntervalIntegrable (fun t : ℝ => |t| ^ (s - 1)) volume (-(1 / 2 : ℝ)) (1 / 2) :=
      intervalIntegrable_abs_rpow (by linarith) _ _
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)] at h1
    exact h1.add (integrableOn_const (by simp))
  have hKmeas : AEStronglyMeasurable (periodicKernel s) μ := by
    refine aestronglyMeasurable_of_tendsto_ae atTop (fun M => (hmeas M).aestronglyMeasurable) ?_
    filter_upwards [hae] with t ht
    exact tendsto_symmetric_signPow hs0 hs1 ht
  have hlim : ∀ᵐ t ∂μ, Tendsto (fun M : ℕ => |∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
      signPow s (t - k) - periodicKernel s t|) atTop (𝓝 0) := by
    filter_upwards [hae] with t ht
    have h := ((tendsto_symmetric_signPow hs0 hs1 ht).sub_const (periodicKernel s t)).abs
    simpa using h
  have hdom := tendsto_integral_filter_of_dominated_convergence (μ := μ) (l := atTop)
    (F := fun (M : ℕ) (t : ℝ) => |∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
      signPow s (t - k) - periodicKernel s t|)
    (fun t => 2 * G t)
    (Eventually.of_forall fun M => ((hmeas M).aestronglyMeasurable.sub hKmeas).norm)
    (Eventually.of_forall fun M => by
      filter_upwards [hae, ae_restrict_mem measurableSet_Ioc] with t hint ht
      rw [Real.norm_eq_abs, abs_abs]
      have h1 := abs_sum_signPow_le hs0 hs1 (hIoc t ht) M
      have h2 := hK_le t (hIoc t ht) hint
      calc |∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), signPow s (t - k) - periodicKernel s t|
          ≤ |∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), signPow s (t - k)| + |periodicKernel s t| :=
            abs_sub _ _
        _ ≤ 2 * G t := by simp only [hG] at h1 h2 ⊢; linarith)
    (hGint.const_mul 2) hlim
  simp only [intervalIntegral.integral_of_le (show -(1 / 2 : ℝ) ≤ 1 / 2 by norm_num),
    integral_zero] at *
  exact hdom

end Riesz1
