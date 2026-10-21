/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Kernel.TransportKernel

/-!
# `L¹` convergence of the symmetric sums on every unit interval

The symmetric sums `S_M(t) = ∑_{|k| ≤ M} sgn(t-k)|t-k|^{s-1}` satisfy the exact shift identity
`S_M(t+1) = S_M(t) + φ(t+M+1) - φ(t-M)` (with `φ = signPow s`), whose boundary terms are
`O(M^{s-1})` uniformly for `|t| ≤ 1/2`. Hence the `L¹(-1/2, 1/2)` convergence of
`S_M → K_s` (proved in `TransportKernel`) transfers to `L¹(j - 1/2, j + 1/2)` for every `j ∈ ℤ`,
and then to `L¹(a, a + 1)` for every real `a`. This is what makes the transport formula
`ψ(x) = A ∫_0^1 ξ(y) K_s(x - y) dy` hold at every point `x`.
-/

public section

open MeasureTheory Set intervalIntegral Filter Topology
open scoped ContDiff Real

namespace Riesz1

/-- The symmetric sum over `[-M, M]` is shifted by one unit, with two boundary terms. -/
lemma symmetric_sum_shift_succ (s t : ℝ) (M : ℕ) :
    ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), signPow s (t + 1 - k) =
      ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), signPow s (t - k) +
        signPow s (t + ((M : ℤ) + 1 : ℤ)) - signPow s (t - (M : ℤ)) := by
  -- Reindex the left sum by `j = k - 1`, which runs over `[-M-1, M-1]`.
  have hre : ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), signPow s (t + 1 - k) =
      ∑ j ∈ Finset.Icc (-(M : ℤ) - 1) ((M : ℤ) - 1), signPow s (t - j) := by
    refine Finset.sum_nbij' (fun k => k - 1) (fun j => j + 1) ?_ ?_ ?_ ?_ ?_
    · intro k hk
      simp only [Finset.mem_Icc] at hk ⊢
      omega
    · intro j hj
      simp only [Finset.mem_Icc] at hj ⊢
      omega
    · intro k _; simp
    · intro j _; simp
    · intro k _
      congr 1
      push_cast
      ring
  have hsplit1 : Finset.Icc (-(M : ℤ) - 1) ((M : ℤ) - 1) =
      insert (-(M : ℤ) - 1) (Finset.Icc (-(M : ℤ)) ((M : ℤ) - 1)) := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hsplit2 : Finset.Icc (-(M : ℤ)) (M : ℤ) = insert (M : ℤ) (Finset.Icc (-(M : ℤ)) ((M : ℤ) - 1)) := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hn1 : (-(M : ℤ) - 1) ∉ Finset.Icc (-(M : ℤ)) ((M : ℤ) - 1) := by
    simp only [Finset.mem_Icc, not_and, not_le]
    intro _; omega
  have hn2 : (M : ℤ) ∉ Finset.Icc (-(M : ℤ)) ((M : ℤ) - 1) := by
    simp only [Finset.mem_Icc, not_and, not_le]
    intro _; omega
  rw [hre, hsplit1, hsplit2, Finset.sum_insert hn1, Finset.sum_insert hn2]
  have hA : signPow s (t - ((-(M : ℤ) - 1 : ℤ) : ℝ)) = signPow s (t + ((M : ℤ) + 1 : ℤ)) := by
    congr 1; push_cast; ring
  rw [hA]
  ring

/-- The bound of a boundary term: `|φ(v)| ≤ (M/2)^{s-1}` once `|v| ≥ M/2`. -/
lemma abs_signPow_le_of_ge {s v c : ℝ} (_hs0 : 0 < s) (hs1 : s < 1) (hc : 0 < c) (hv : c ≤ |v|) :
    |signPow s v| ≤ c ^ (s - 1) := by
  refine (abs_signPow_le s v).trans ?_
  exact Real.rpow_le_rpow_of_nonpos (by linarith) hv (by linarith)

/-- Forward integer shifts of the symmetric sums: the drift over `n` unit steps is at most
`2n (M/2)^{s-1}` for `|t| ≤ 1/2` and `M ≥ 2n + 2`. -/
lemma abs_symmetric_sum_shift_nat_le {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (n : ℕ) :
    ∀ (t : ℝ) (M : ℕ), |t| ≤ 1 / 2 → 2 * n + 2 ≤ M →
      |∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), signPow s (t + n - k) -
          ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), signPow s (t - k)| ≤
        2 * n * ((M : ℝ) / 2) ^ (s - 1) := by
  induction n with
  | zero => intro t M _ _; simp
  | succ n ih =>
    intro t M ht hM
    have hM' : 2 * n + 2 ≤ M := by omega
    have hih := ih t M ht hM'
    have hstep := symmetric_sum_shift_succ s (t + n) M
    have hcast : t + ((n + 1 : ℕ) : ℝ) = t + n + 1 := by push_cast; ring
    rw [hcast]
    rw [hstep]
    have hMpos : (0 : ℝ) < (M : ℝ) / 2 := by
      have : (2 : ℝ) * n + 2 ≤ M := by exact_mod_cast hM'
      have : (0 : ℝ) < M := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      linarith
    have hMr : (2 : ℝ) * n + 2 ≤ M := by exact_mod_cast hM'
    have hb1 : |signPow s (t + n + ((M : ℤ) + 1 : ℤ))| ≤ ((M : ℝ) / 2) ^ (s - 1) := by
      refine abs_signPow_le_of_ge hs0 hs1 hMpos ?_
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      rw [abs_of_nonneg (by push_cast; linarith [abs_le.1 ht])]
      push_cast
      linarith [abs_le.1 ht]
    have hb2 : |signPow s (t + n - (M : ℤ))| ≤ ((M : ℝ) / 2) ^ (s - 1) := by
      refine abs_signPow_le_of_ge hs0 hs1 hMpos ?_
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      rw [show t + n - ((M : ℤ) : ℝ) = -((M : ℝ) - n - t) by push_cast; ring, abs_neg,
        abs_of_pos (by linarith [abs_le.1 ht])]
      linarith [abs_le.1 ht]
    have hsum : |signPow s (t + n + ((M : ℤ) + 1 : ℤ)) - signPow s (t + n - (M : ℤ))| ≤
        2 * ((M : ℝ) / 2) ^ (s - 1) := by
      have := abs_sub (signPow s (t + n + ((M : ℤ) + 1 : ℤ))) (signPow s (t + n - (M : ℤ)))
      linarith
    have hfin : ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), signPow s (t + n - k) +
        signPow s (t + n + ((M : ℤ) + 1 : ℤ)) - signPow s (t + n - (M : ℤ)) -
        ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), signPow s (t - k) =
        (∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), signPow s (t + n - k) -
          ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), signPow s (t - k)) +
        (signPow s (t + n + ((M : ℤ) + 1 : ℤ)) - signPow s (t + n - (M : ℤ))) := by ring
    rw [hfin]
    calc _ ≤ _ := abs_add_le _ _
      _ ≤ 2 * n * ((M : ℝ) / 2) ^ (s - 1) + 2 * ((M : ℝ) / 2) ^ (s - 1) := add_le_add hih hsum
      _ = 2 * ((n + 1 : ℕ) : ℝ) * ((M : ℝ) / 2) ^ (s - 1) := by push_cast; ring

/-- The symmetric sums are odd. -/
lemma symmetricSum_neg (s t : ℝ) (M : ℕ) :
    ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), signPow s (-t - k) =
      -∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), signPow s (t - k) := by
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_nbij' (fun k => -k) (fun k => -k) ?_ ?_ ?_ ?_ ?_
  · intro k hk; simp only [Finset.mem_Icc] at hk ⊢; omega
  · intro k hk; simp only [Finset.mem_Icc] at hk ⊢; omega
  · intro k _; simp
  · intro k _; simp
  · intro k _
    rw [show -t - (k : ℝ) = -(t - ((-k : ℤ) : ℝ)) by push_cast; ring, signPow_neg']

/-- The periodic kernel is odd. -/
lemma periodicKernel_neg' (s t : ℝ) : periodicKernel s (-t) = -periodicKernel s t := by
  have h1 := periodicKernel_add_int s (1 - t) (-1)
  have h2 := periodicKernel_one_sub s t
  have e : (1 - t) + ((-1 : ℤ) : ℝ) = -t := by push_cast; ring
  rw [e] at h1
  rw [h1, h2]

/-- Interval integrability of `t ↦ sgn(t - k)|t - k|^{s-1}`, for a fixed integer `k`. -/
lemma intervalIntegrable_signPow_shift {s : ℝ} (hs0 : 0 < s) (_hs1 : s < 1) (k : ℤ) (a b : ℝ) :
    IntervalIntegrable (fun t : ℝ => signPow s (t - k)) volume a b := by
  have hpow : IntervalIntegrable (fun t : ℝ => |t - k| ^ (s - 1)) volume a b := by
    have := intervalIntegrable_abs_sub_rpow (r := s - 1) (by linarith) (k : ℝ) a b
    simpa only [abs_sub_comm] using this
  refine IntervalIntegrable.mono_fun' (hpow) ?_ (ae_of_all _ fun t => ?_)
  · exact (measurable_realSign.comp (by fun_prop)).mul (by fun_prop) |>.aestronglyMeasurable
  · exact abs_signPow_le s _

/-- The periodic kernel is integrable on `[-1/2, 1/2]`: it is dominated by the bound
`|t|^{s-1} + C` obtained for the symmetric sums, and it is an almost-everywhere limit of them. -/
lemma intervalIntegrable_periodicKernel_half {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    IntervalIntegrable (periodicKernel s) volume (-(1 / 2 : ℝ)) (1 / 2) := by
  set C : ℝ := ∑' k : ℕ, (1 - s) * ((k : ℝ) + 1 / 2) ^ (s - 2) with hC
  have hmeas : ∀ M : ℕ, Measurable fun t : ℝ =>
      ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), signPow s (t - k) := fun M =>
    Finset.measurable_sum _ fun k _ => measurable_signPow_shift s k
  have hae : ∀ᵐ t ∂(volume.restrict (Ioc (-(1 / 2 : ℝ)) (1 / 2))), ∀ k : ℤ, t ≠ (k : ℝ) :=
    ae_restrict_ne_int _
  have hKm : AEStronglyMeasurable (periodicKernel s) (volume.restrict (Ioc (-(1 / 2 : ℝ)) (1 / 2))) := by
    refine aestronglyMeasurable_of_tendsto_ae atTop (fun M => (hmeas M).aestronglyMeasurable) ?_
    filter_upwards [hae] with t ht
    exact tendsto_symmetric_signPow hs0 hs1 ht
  have hG : IntegrableOn (fun t : ℝ => |t| ^ (s - 1) + C) (Ioc (-(1 / 2 : ℝ)) (1 / 2)) := by
    have h1 : IntervalIntegrable (fun t : ℝ => |t| ^ (s - 1)) volume (-(1 / 2 : ℝ)) (1 / 2) :=
      intervalIntegrable_abs_rpow (by linarith) _ _
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)] at h1
    exact h1.add (integrableOn_const (by simp))
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
  refine Integrable.mono' hG hKm ?_
  filter_upwards [hae, ae_restrict_mem measurableSet_Ioc] with t ht1 ht2
  have ht' : |t| ≤ 1 / 2 := by
    rw [abs_le]; constructor <;> linarith [ht2.1, ht2.2]
  rw [Real.norm_eq_abs]
  have hlim := (tendsto_symmetric_signPow hs0 hs1 ht1).abs
  exact le_of_tendsto hlim (Eventually.of_forall fun M => abs_sum_signPow_le hs0 hs1 ht' M)

/-- The periodic kernel is 1-periodic. -/
lemma periodicKernel_periodic (s : ℝ) : Function.Periodic (periodicKernel s) 1 := by
  intro t
  have h := periodicKernel_add_int s t 1
  simpa using h

/-- The periodic kernel is interval integrable on every interval. -/
lemma intervalIntegrable_periodicKernel_all {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (a b : ℝ) :
    IntervalIntegrable (periodicKernel s) volume a b := by
  have h0 := intervalIntegrable_periodicKernel_half hs0 hs1
  have h1 : IntervalIntegrable (periodicKernel s) volume (-(1 / 2 : ℝ)) (-(1 / 2) + 1) := by
    rw [show -(1 / 2 : ℝ) + 1 = 1 / 2 by ring]
    exact h0
  exact (periodicKernel_periodic s).intervalIntegrable one_ne_zero (t := -(1 / 2 : ℝ)) h1 a b

/-- Interval integrability of the symmetric sums minus the kernel, on every interval. -/
lemma intervalIntegrable_symmetricSum_sub {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (M : ℕ) (a b : ℝ) :
    IntervalIntegrable (fun t : ℝ =>
      ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), signPow s (t - k) - periodicKernel s t) volume a b := by
  refine IntervalIntegrable.sub ?_ (intervalIntegrable_periodicKernel_all hs0 hs1 a b)
  have h := IntervalIntegrable.sum (μ := volume) (a := a) (b := b)
    (Finset.Icc (-(M : ℤ)) (M : ℤ)) (f := fun k : ℤ => fun t : ℝ => signPow s (t - k))
    (fun k _ => intervalIntegrable_signPow_shift hs0 hs1 k a b)
  convert h using 1
  ext t
  simp [Finset.sum_apply]

/-- The `L¹` deviation of the symmetric sums on `[n - 1/2, n + 1/2]` for `n ∈ ℕ` tends to zero. -/
lemma tendsto_L1_nat_center {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (n : ℕ) :
    Tendsto (fun M : ℕ => ∫ t in ((n : ℝ) - 1 / 2)..((n : ℝ) + 1 / 2),
      |∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), signPow s (t - k) - periodicKernel s t|)
      atTop (𝓝 0) := by
  have hL1 := tendsto_symmetric_signPow_L1 hs0 hs1
  have hc : Tendsto (fun M : ℕ => 2 * (n : ℝ) * ((M : ℝ) / 2) ^ (s - 1)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun M : ℕ => ((M : ℝ) / 2)) atTop atTop :=
      (tendsto_natCast_atTop_atTop).atTop_div_const (by norm_num)
    have h2 := (tendsto_rpow_neg_atTop (y := 1 - s) (by linarith)).comp h1
    have h3 := h2.const_mul (2 * (n : ℝ))
    simpa [show ∀ M : ℕ, ((M : ℝ) / 2) ^ (s - 1) = ((M : ℝ) / 2) ^ (-(1 - s)) from
      fun M => by ring_nf] using h3
  have hup : ∀ᶠ M : ℕ in atTop,
      ∫ t in ((n : ℝ) - 1 / 2)..((n : ℝ) + 1 / 2),
        |∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), signPow s (t - k) - periodicKernel s t| ≤
      (∫ t in (-(1 / 2 : ℝ))..(1 / 2),
        |∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), signPow s (t - k) - periodicKernel s t|) +
      2 * (n : ℝ) * ((M : ℝ) / 2) ^ (s - 1) := by
    filter_upwards [eventually_ge_atTop (2 * n + 2)] with M hM
    -- pointwise: shift by `n` costs at most `2n (M/2)^{s-1}`
    have hpt : ∀ t ∈ Set.uIcc ((n : ℝ) - 1 / 2) ((n : ℝ) + 1 / 2),
        |∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), signPow s (t - k) - periodicKernel s t| ≤
        |∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), signPow s ((t - n) - k) -
            periodicKernel s (t - n)| + 2 * (n : ℝ) * ((M : ℝ) / 2) ^ (s - 1) := by
      intro t ht
      rw [uIcc_of_le (by linarith)] at ht
      have hu : |t - n| ≤ 1 / 2 := by
        rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
      have hsh := abs_symmetric_sum_shift_nat_le hs0 hs1 n (t - n) M hu (by omega)
      rw [sub_add_cancel] at hsh
      have hK : periodicKernel s t = periodicKernel s (t - n) := by
        have h := periodicKernel_add_int s (t - n) (n : ℤ)
        push_cast at h
        rw [sub_add_cancel] at h
        exact h
      rw [hK]
      have e : ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), signPow s (t - k) - periodicKernel s (t - n) =
          (∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), signPow s ((t - n) - k) - periodicKernel s (t - n)) +
          (∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), signPow s (t - k) -
            ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), signPow s ((t - n) - k)) := by ring
      rw [e]
      refine (abs_add_le _ _).trans ?_
      have h2 := abs_sub_comm (∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), signPow s (t - k))
        (∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), signPow s ((t - n) - k))
      linarith [abs_sub_comm (∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), signPow s (t - k))
        (∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), signPow s ((t - n) - k))]
    have hint_shift : IntervalIntegrable (fun t : ℝ =>
        |∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), signPow s ((t - n) - k) - periodicKernel s (t - n)|)
        volume ((n : ℝ) - 1 / 2) ((n : ℝ) + 1 / 2) := by
      have h := (intervalIntegrable_symmetricSum_sub hs0 hs1 M (-(1 / 2 : ℝ)) (1 / 2)).abs
      have h' := h.comp_sub_right (n : ℝ)
      rw [show -(1 / 2 : ℝ) + n = (n : ℝ) - 1 / 2 by ring,
        show (1 / 2 : ℝ) + n = (n : ℝ) + 1 / 2 by ring] at h'
      exact h'
    have hint_left : IntervalIntegrable (fun t : ℝ =>
        |∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), signPow s (t - k) - periodicKernel s t|)
        volume ((n : ℝ) - 1 / 2) ((n : ℝ) + 1 / 2) :=
      (intervalIntegrable_symmetricSum_sub hs0 hs1 M _ _).abs
    have hint_const : IntervalIntegrable (fun _ : ℝ => 2 * (n : ℝ) * ((M : ℝ) / 2) ^ (s - 1))
        volume ((n : ℝ) - 1 / 2) ((n : ℝ) + 1 / 2) := intervalIntegrable_const
    have hmono := intervalIntegral.integral_mono_on (by linarith : (n : ℝ) - 1 / 2 ≤ n + 1 / 2)
      hint_left (hint_shift.add hint_const) (fun t ht => hpt t (by
        rw [uIcc_of_le (by linarith)]; exact ht))
    rw [intervalIntegral.integral_add hint_shift hint_const, intervalIntegral.integral_const,
      intervalIntegral.integral_comp_sub_right (fun t : ℝ =>
        |∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), signPow s (t - k) - periodicKernel s t|) (n : ℝ)] at hmono
    rw [show (n : ℝ) - 1 / 2 - n = -(1 / 2 : ℝ) by ring, show (n : ℝ) + 1 / 2 - n = 1 / 2 by ring,
      smul_eq_mul, show (n : ℝ) + 1 / 2 - ((n : ℝ) - 1 / 2) = 1 by ring, one_mul] at hmono
    exact hmono
  have hsum := hL1.add hc
  rw [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum ?_ hup
  filter_upwards with M
  exact intervalIntegral.integral_nonneg (by linarith) (fun t _ => abs_nonneg _)

/-- The `L¹` deviation of the symmetric sums on `[j - 1/2, j + 1/2]` for `j ∈ ℤ` tends to zero. -/
lemma tendsto_L1_center {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (j : ℤ) :
    Tendsto (fun M : ℕ => ∫ t in ((j : ℝ) - 1 / 2)..((j : ℝ) + 1 / 2),
      |∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), signPow s (t - k) - periodicKernel s t|)
      atTop (𝓝 0) := by
  rcases le_or_gt 0 j with hj | hj
  · have hn : ((j.toNat : ℕ) : ℤ) = j := Int.toNat_of_nonneg hj
    have := tendsto_L1_nat_center hs0 hs1 j.toNat
    rwa [show ((j.toNat : ℕ) : ℝ) = (j : ℝ) by exact_mod_cast hn] at this
  · -- for `j < 0`, reflect the interval using the oddness of the symmetric sums and the kernel
    have hn : ((-j).toNat : ℤ) = -j := Int.toNat_of_nonneg (by omega)
    have hnr : (((-j).toNat : ℕ) : ℝ) = -(j : ℝ) := by exact_mod_cast hn
    have := tendsto_L1_nat_center hs0 hs1 (-j).toNat
    rw [hnr] at this
    refine this.congr fun M => ?_
    set n : ℝ := -(j : ℝ) with hn_def
    have hodd : ∀ x : ℝ,
        |∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), signPow s (-x - k) - periodicKernel s (-x)| =
        |∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), signPow s (x - k) - periodicKernel s x| := by
      intro x
      rw [symmetricSum_neg, periodicKernel_neg']
      rw [← abs_neg]
      congr 1
      ring
    have hcomp := intervalIntegral.integral_comp_neg (a := n - 1 / 2) (b := n + 1 / 2)
      (fun t : ℝ => |∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), signPow s (t - k) - periodicKernel s t|)
    simp only [hodd] at hcomp
    rw [show -(n + 1 / 2) = (j : ℝ) - 1 / 2 by rw [hn_def]; ring,
      show -(n - 1 / 2) = (j : ℝ) + 1 / 2 by rw [hn_def]; ring] at hcomp
    exact hcomp

/-- **The `L¹` convergence of the symmetric sums on every unit interval** (the statement used
for the transport identity at every point). -/
theorem tendsto_L1_unit_interval {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (a : ℝ) :
    Tendsto (fun M : ℕ => ∫ t in a..(a + 1),
      |∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), signPow s (t - k) - periodicKernel s t|)
      atTop (𝓝 0) := by
  set n : ℤ := ⌊a + 1 / 2⌋ with hn
  have hn1 : (n : ℝ) ≤ a + 1 / 2 := Int.floor_le _
  have hn2 : a + 1 / 2 < (n : ℝ) + 1 := Int.lt_floor_add_one _
  have hA : (n : ℝ) - 1 / 2 ≤ a := by linarith
  have hB : a + 1 ≤ (n : ℝ) + 3 / 2 := by linarith
  have hB' : (n : ℝ) + 1 / 2 ≤ a + 1 := by linarith
  have hc1 := tendsto_L1_center hs0 hs1 n
  have hc2 := tendsto_L1_center hs0 hs1 (n + 1)
  have e1 : ((n + 1 : ℤ) : ℝ) - 1 / 2 = (n : ℝ) + 1 / 2 := by push_cast; ring
  have e2 : ((n + 1 : ℤ) : ℝ) + 1 / 2 = (n : ℝ) + 3 / 2 := by push_cast; ring
  rw [e1, e2] at hc2
  have hc2' := hc2
  have hsum := hc1.add hc2'
  rw [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum ?_ ?_
  · filter_upwards with M
    exact intervalIntegral.integral_nonneg (by linarith) (fun t _ => abs_nonneg _)
  · filter_upwards with M
    have hint : IntervalIntegrable (fun t : ℝ =>
        |∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), signPow s (t - k) - periodicKernel s t|)
        volume ((n : ℝ) - 1 / 2) ((n : ℝ) + 3 / 2) :=
      (intervalIntegrable_symmetricSum_sub hs0 hs1 M _ _).abs
    have hmono := intervalIntegral.integral_mono_interval hA (by linarith : a ≤ a + 1) hB
      (ae_of_all _ fun t => abs_nonneg _) hint
    have h1 := (intervalIntegrable_symmetricSum_sub hs0 hs1 M ((n : ℝ) - 1 / 2) ((n : ℝ) + 1 / 2)).abs
    have h2 := (intervalIntegrable_symmetricSum_sub hs0 hs1 M ((n : ℝ) + 1 / 2) ((n : ℝ) + 3 / 2)).abs
    rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2] at hmono
    exact hmono

end Riesz1
