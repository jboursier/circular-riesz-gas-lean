/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopArcsSymm
public import Riesz1.Auxiliary.LoopMomentsDiscrepancy

/-!
# Product kernels and arc discrepancies

Preparation for the identification of the arc-crossing pairing with `Λ` (arcs part of
Lemma 5.8). For `t` off the particle positions, the
indicator kernels `(z, u) ↦ 1[fwd(t - z) < y] 1[fwd(u - t) < w]` are product kernels, and their
pairing against `ν ⊗ ν` is the product of two discrepancies of arcs of `N𝕋`:

* `loopArcPairing_mul`: the pairing of a product kernel `F(z) H(u)` is `ν(F) ν(H)`.
* `loopArcPairing_arc_product`: the pairing of the indicator product is
  `loopDiscrepancy (t - y) y X * loopDiscrepancy t w X`.

The arc facts used are the membership of a point in an arc of `N𝕋` (`exists_arc_start_iff`,
`exists_arc_end_iff_fwd`) and the length of an arc (`volume_microArc`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Finset Set

namespace Riesz1

/-- The pairing of a product kernel `F(z) H(u)` against `ν ⊗ ν` is the product of the two
signed measures: `Pair(F ⊗ H) = (∑ᵢ F(zᵢ) - ∫F)(∑ⱼ H(zⱼ) - ∫H)`. No integrability is needed. -/
theorem loopArcPairing_mul (N : ℕ+) (X : Configuration N) (F H : ℝ → ℝ) :
    loopArcPairing N X (fun z u => F z * H u)
      = ((∑ i : Fin (N : ℕ), F (loopArcPos N X i)) - ∫ z in (0 : ℝ)..(N : ℝ), F z)
        * ((∑ j : Fin (N : ℕ), H (loopArcPos N X j)) - ∫ u in (0 : ℝ)..(N : ℝ), H u) := by
  have hA : ∑ i : Fin (N : ℕ), ∑ j : Fin (N : ℕ), F (loopArcPos N X i) * H (loopArcPos N X j)
      = (∑ i : Fin (N : ℕ), F (loopArcPos N X i)) * ∑ j : Fin (N : ℕ), H (loopArcPos N X j) := by
    rw [Finset.sum_mul_sum]
  have hB : ∑ i : Fin (N : ℕ), F (loopArcPos N X i) * ∫ u in (0 : ℝ)..(N : ℝ), H u
      = (∑ i : Fin (N : ℕ), F (loopArcPos N X i)) * ∫ u in (0 : ℝ)..(N : ℝ), H u := by
    rw [Finset.sum_mul]
  have hC : ∑ j : Fin (N : ℕ), (∫ z in (0 : ℝ)..(N : ℝ), F z) * H (loopArcPos N X j)
      = (∫ z in (0 : ℝ)..(N : ℝ), F z) * ∑ j : Fin (N : ℕ), H (loopArcPos N X j) := by
    rw [Finset.mul_sum]
  simp only [loopArcPairing, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_mul_const]
  rw [hA, hB, hC]
  ring

/-- The forward distance is positive when the point is not a multiple of `N`. -/
theorem loopArcFwd_pos_of_ne (N : ℕ+) (x : ℝ) (hx : ∀ k : ℤ, x ≠ k * N) :
    0 < loopArcFwd N x := by
  rcases (loopArcFwd_nonneg N x).lt_or_eq with h | h
  · exact h
  · exfalso
    have hs := loopArcFwd_sub_floor N x
    rw [← h, zero_add] at hs
    exact hx _ hs

/-- **Core arc lemma.** For `0 < r ≤ N`, some integer translate of `w` lies in `(0, r)` if and only
if the forward distance of `w` lies in `(0, r)`. -/
theorem exists_translate_iff_fwd (N : ℕ+) (w r : ℝ) (hrN : r ≤ N) :
    (∃ n : ℤ, 0 < w + n * N ∧ w + n * N < r) ↔ (0 < loopArcFwd N w ∧ loopArcFwd N w < r) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast N.pos
  constructor
  · rintro ⟨n, h1, h2⟩
    have hs := loopArcFwd_sub_floor N w
    have hf0 := loopArcFwd_nonneg N w
    have hfN := loopArcFwd_lt N w
    -- With `m = n + ⌊w / N⌋`, the number `fwd(w) + m N` lies in `(0, r)`.
    have e : w + n * N = loopArcFwd N w + (((n + ⌊w / N⌋ : ℤ)) : ℝ) * N := by
      push_cast
      linarith
    rw [e] at h1 h2
    have hm1 : (((n + ⌊w / N⌋ : ℤ)) : ℝ) < 1 := by
      by_contra hc
      have hc' := le_of_not_gt hc
      nlinarith
    have hm2 : (-1 : ℝ) < (((n + ⌊w / N⌋ : ℤ)) : ℝ) := by
      by_contra hc
      have hc' := le_of_not_gt hc
      nlinarith
    have hm1' : n + ⌊w / N⌋ < 1 := by exact_mod_cast hm1
    have hm2' : -1 < n + ⌊w / N⌋ := by exact_mod_cast hm2
    have hm0 : n + ⌊w / N⌋ = 0 := by omega
    rw [hm0] at h1 h2
    simp only [Int.cast_zero, zero_mul, add_zero] at h1 h2
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨-⌊w / N⌋, ?_, ?_⟩
    · have hs := loopArcFwd_sub_floor N w
      push_cast
      linarith
    · have hs := loopArcFwd_sub_floor N w
      push_cast
      linarith

/-- The arc `{x : c < x < c + r} mod N` contains the point `z` if and only if the forward
distance of `z - c` lies in `(0, r)`. -/
theorem exists_arc_start_iff (N : ℕ+) (z c r : ℝ) (hrN : r ≤ N) :
    (∃ n : ℤ, c < z + n * N ∧ z + n * N < c + r)
      ↔ (0 < loopArcFwd N (z - c) ∧ loopArcFwd N (z - c) < r) := by
  rw [← exists_translate_iff_fwd N (z - c) r hrN]
  refine exists_congr fun n => ?_
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- The arc `{x : c < x < c + r} mod N` contains the point `z` if and only if the forward
distance of `c + r - z` lies in `(0, r)`. -/
theorem exists_arc_end_iff_fwd (N : ℕ+) (z c r : ℝ) (hrN : r ≤ N) :
    (∃ n : ℤ, c < z + n * N ∧ z + n * N < c + r)
      ↔ (0 < loopArcFwd N (c + r - z) ∧ loopArcFwd N (c + r - z) < r) := by
  rw [← exists_translate_iff_fwd N (c + r - z) r hrN]
  constructor
  · rintro ⟨n, h1, h2⟩
    refine ⟨-n, ?_, ?_⟩
    · push_cast
      linarith
    · push_cast
      linarith
  · rintro ⟨n, h1, h2⟩
    refine ⟨-n, ?_, ?_⟩
    · push_cast at h1 ⊢
      linarith
    · push_cast at h2 ⊢
      linarith

/-- The integral of `f(fwd(u - z))` over `z` on one period is the integral of `f` over `[0, N]`. -/
theorem integral_fwd_sub (N : ℕ+) (f : ℝ → ℝ) (u : ℝ) :
    ∫ z in (0 : ℝ)..(N : ℝ), f (loopArcFwd N (u - z)) = ∫ δ in (0 : ℝ)..(N : ℝ), f δ := by
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have hper : Function.Periodic (fun v => f (loopArcFwd N v)) (N : ℝ) := by
    intro v
    simp only
    rw [show v + (N : ℝ) = v + ((1 : ℤ) : ℝ) * N by push_cast; ring, loopArcFwd_add_int_mul]
  have h1 : ∫ z in (0 : ℝ)..(N : ℝ), f (loopArcFwd N (u - z))
      = ∫ v in (u - N)..(u - 0), f (loopArcFwd N v) := by
    rw [← intervalIntegral.integral_comp_sub_left (fun v => f (loopArcFwd N v)) u]
  have h2 : ∫ v in (u - N)..(u - 0), f (loopArcFwd N v) = ∫ v in (0 : ℝ)..(N : ℝ), f (loopArcFwd N v) := by
    have h := hper.intervalIntegral_add_eq (u - N) 0
    rw [sub_add_cancel, zero_add] at h
    rw [sub_zero]
    exact h
  rw [h1, h2]
  refine intervalIntegral.integral_congr_ae ?_
  have hN_ae : ∀ᵐ v ∂(volume : Measure ℝ), v ≠ (N : ℝ) := by
    rw [ae_iff]
    simp
  filter_upwards [hN_ae] with v hv hvI
  rw [uIoc_of_le hN0] at hvI
  rw [loopArcFwd_of_mem hvI.1.le (lt_of_le_of_ne hvI.2 hv)]

/-- The indicator of `(-∞, c)` on `(0, N]` integrates to `c`, for `0 ≤ c ≤ N`. -/
theorem integral_ite_lt_eq (c : ℝ) (N : ℕ+) (hc0 : 0 ≤ c) (hcN : c ≤ N) :
    ∫ v in (0 : ℝ)..(N : ℝ), (if v < c then (1 : ℝ) else 0) = c := by
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have hfun : (fun v : ℝ => if v < c then (1 : ℝ) else 0) = (Iio c).indicator (fun _ => (1 : ℝ)) := by
    funext v
    simp [Set.indicator]
  rw [intervalIntegral.integral_of_le hN0, hfun, setIntegral_indicator measurableSet_Iio,
    setIntegral_const]
  have hset : Ioc (0 : ℝ) N ∩ Iio c = Ioo 0 c := by
    ext v
    simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Iio, Set.mem_Ioo]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩
      exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩
      exact ⟨⟨h1, (h3.trans_le hcN).le⟩, h3⟩
  rw [hset, Real.volume_real_Ioo_of_le hc0]
  simp

/-- The loop count of the arc `(t - y, t)` counts the particles `z` with `fwd(t - z) < y`, when
no particle is at `t` modulo `N`. -/
theorem loopCount_eq_sum_fwd_left (N : ℕ+) (X : Configuration N) (t y : ℝ)
    (hyN : y ≤ N) (ht : ∀ (i : Fin (N : ℕ)) (k : ℤ), t ≠ loopArcPos N X i + k * N) :
    loopCount (t - y) y X
      = ∑ i : Fin (N : ℕ), if loopArcFwd N (t - loopArcPos N X i) < y then (1 : ℝ) else 0 := by
  unfold loopCount
  refine Finset.sum_congr rfl fun i _ => ?_
  have hpos : 0 < loopArcFwd N (t - loopArcPos N X i) :=
    loopArcFwd_pos_of_ne N _ fun k hk => ht i k (by linarith)
  have hmem : loopPos X i ∈ microArc N (t - y) y ↔ loopArcFwd N (t - loopArcPos N X i) < y := by
    have hc : loopPos X i = ((loopArcPos N X i : ℝ) : AddCircle (N : ℝ)) := rfl
    rw [hc, coe_mem_microArc_iff, exists_arc_end_iff_fwd N _ (t - y) y hyN]
    rw [show t - y + y - loopArcPos N X i = t - loopArcPos N X i by ring]
    exact ⟨fun h => h.2, fun h => ⟨hpos, h⟩⟩
  simp only [hmem]

/-- The loop count of the arc `(t, t + w)` counts the particles `z` with `fwd(z - t) < w`, when
no particle is at `t` modulo `N`. -/
theorem loopCount_eq_sum_fwd_right (N : ℕ+) (X : Configuration N) (t w : ℝ)
    (hwN : w ≤ N) (ht : ∀ (i : Fin (N : ℕ)) (k : ℤ), t ≠ loopArcPos N X i + k * N) :
    loopCount t w X
      = ∑ j : Fin (N : ℕ), if loopArcFwd N (loopArcPos N X j - t) < w then (1 : ℝ) else 0 := by
  unfold loopCount
  refine Finset.sum_congr rfl fun j _ => ?_
  have hpos : 0 < loopArcFwd N (loopArcPos N X j - t) :=
    loopArcFwd_pos_of_ne N _ fun k hk => ht j (-k) (by push_cast; linarith)
  have hmem : loopPos X j ∈ microArc N t w ↔ loopArcFwd N (loopArcPos N X j - t) < w := by
    have hc : loopPos X j = ((loopArcPos N X j : ℝ) : AddCircle (N : ℝ)) := rfl
    rw [hc, coe_mem_microArc_iff, exists_arc_start_iff N _ t w hwN]
    exact ⟨fun h => h.2, fun h => ⟨hpos, h⟩⟩
  simp only [hmem]

/-- The discrepancy of the arc `(t - y, t)`: the particle count minus the length `y`. -/
theorem loopDiscrepancy_arc_left (N : ℕ+) (X : Configuration N) (t y : ℝ) (hy0 : 0 < y)
    (hyN : y ≤ N) (ht : ∀ (i : Fin (N : ℕ)) (k : ℤ), t ≠ loopArcPos N X i + k * N) :
    loopDiscrepancy (t - y) y X
      = (∑ i : Fin (N : ℕ), if loopArcFwd N (t - loopArcPos N X i) < y then (1 : ℝ) else 0) - y := by
  unfold loopDiscrepancy
  rw [loopCount_eq_sum_fwd_left N X t y hyN ht, volume_microArc hy0 hyN,
    ENNReal.toReal_ofReal hy0.le]

/-- The discrepancy of the arc `(t, t + w)`: the particle count minus the length `w`. -/
theorem loopDiscrepancy_arc_right (N : ℕ+) (X : Configuration N) (t w : ℝ) (hw0 : 0 < w)
    (hwN : w ≤ N) (ht : ∀ (i : Fin (N : ℕ)) (k : ℤ), t ≠ loopArcPos N X i + k * N) :
    loopDiscrepancy t w X
      = (∑ j : Fin (N : ℕ), if loopArcFwd N (loopArcPos N X j - t) < w then (1 : ℝ) else 0) - w := by
  unfold loopDiscrepancy
  rw [loopCount_eq_sum_fwd_right N X t w hwN ht, volume_microArc hw0 hwN,
    ENNReal.toReal_ofReal hw0.le]

/-- **Product kernels of arc indicators.** For `t` off the particle positions, the pairing of
`(z, u) ↦ 1[fwd(t - z) < y] 1[fwd(u - t) < w]` against `ν ⊗ ν` is the product of the two arc
discrepancies `loopDiscrepancy (t - y) y X` and `loopDiscrepancy t w X`. -/
theorem loopArcPairing_arc_product (N : ℕ+) (X : Configuration N) (t y w : ℝ) (hy0 : 0 < y)
    (hyN : y ≤ N) (hw0 : 0 < w) (hwN : w ≤ N)
    (ht : ∀ (i : Fin (N : ℕ)) (k : ℤ), t ≠ loopArcPos N X i + k * N) :
    loopArcPairing N X (fun z u =>
        (if loopArcFwd N (t - z) < y then (1 : ℝ) else 0)
          * (if loopArcFwd N (u - t) < w then (1 : ℝ) else 0))
      = loopDiscrepancy (t - y) y X * loopDiscrepancy t w X := by
  have hF : ∫ z in (0 : ℝ)..(N : ℝ), (if loopArcFwd N (t - z) < y then (1 : ℝ) else 0) = y := by
    rw [integral_fwd_sub N (fun δ => if δ < y then (1 : ℝ) else 0) t]
    exact integral_ite_lt_eq y N hy0.le hyN
  have hH : ∫ u in (0 : ℝ)..(N : ℝ), (if loopArcFwd N (u - t) < w then (1 : ℝ) else 0) = w := by
    rw [integral_fwd_comp N (fun δ => if δ < w then (1 : ℝ) else 0) t]
    exact integral_ite_lt_eq w N hw0.le hwN
  rw [loopArcPairing_mul, hF, hH, loopDiscrepancy_arc_left N X t y hy0 hyN ht,
    loopDiscrepancy_arc_right N X t w hw0 hwN ht]

/-- The indicator product `1[a < y] 1[b < x - y]` integrates over `y ∈ (0, x)` to `(x - (a + b))_+`,
for `a, b ≥ 0` and `x ≥ 0`. -/
theorem integral_indicator_prod_eq (a b x : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hx : 0 ≤ x) :
    ∫ y in (0 : ℝ)..x, (if a < y then (1 : ℝ) else 0) * (if b < x - y then (1 : ℝ) else 0)
      = max (x - (a + b)) 0 := by
  have hfun : (fun y : ℝ => (if a < y then (1 : ℝ) else 0) * (if b < x - y then (1 : ℝ) else 0))
      = (Ioo a (x - b)).indicator (fun _ => (1 : ℝ)) := by
    funext y
    simp only [Set.indicator, Set.mem_Ioo, show b < x - y ↔ y < x - b from
      ⟨fun h => by linarith, fun h => by linarith⟩]
    by_cases h1 : a < y <;> by_cases h2 : y < x - b <;> simp [h1, h2]
  rw [intervalIntegral.integral_of_le hx, hfun, setIntegral_indicator measurableSet_Ioo,
    setIntegral_const]
  have hset : Ioc (0 : ℝ) x ∩ Ioo a (x - b) = Ioo a (x - b) :=
    Set.inter_eq_right.mpr fun y hy => ⟨by linarith [hy.1], by linarith [hy.2]⟩
  rw [hset, Real.volume_real_Ioo, smul_eq_mul, mul_one]
  congr 1
  ring

/-- **Cutoff as an integral of the third derivative.** For `a, b ≥ 0` with `a + b > 0`, and with
`R = N / 2`,
`Q(a + b) = ∫₀^R (-g'''(x)) (∫₀^x 1[a < y] 1[b < x - y] dy) dx
  + g''(R) (∫₀^R 1[a < y] 1[b < R - y] dy)`.
The inner integrals are the triangle lengths `(x - (a + b))_+`, and the atom `g''(R)` is the jump
of `Q'` at `R`. -/
theorem loopArcQ_eq_integral_indicator (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (N : ℕ+) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 0 < a + b) :
    loopArcQ s N (a + b)
      = (∫ x in (0 : ℝ)..((N : ℝ) / 2), -iteratedDeriv 3 (loopArcG s N) x
            * ∫ y in (0 : ℝ)..x, (if a < y then (1 : ℝ) else 0) * (if b < x - y then (1 : ℝ) else 0))
        + iteratedDeriv 2 (loopArcG s N) ((N : ℝ) / 2)
          * ∫ y in (0 : ℝ)..((N : ℝ) / 2),
              (if a < y then (1 : ℝ) else 0) * (if b < (N : ℝ) / 2 - y then (1 : ℝ) else 0) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hR0 : (0 : ℝ) ≤ (N : ℝ) / 2 := by positivity
  have hinner : (∫ x in (0 : ℝ)..((N : ℝ) / 2), -iteratedDeriv 3 (loopArcG s N) x
        * ∫ y in (0 : ℝ)..x, (if a < y then (1 : ℝ) else 0) * (if b < x - y then (1 : ℝ) else 0))
      = ∫ x in (0 : ℝ)..((N : ℝ) / 2), -iteratedDeriv 3 (loopArcG s N) x * max (x - (a + b)) 0 := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le hR0] at hx
    rw [integral_indicator_prod_eq a b x ha hb hx.1]
  have hatom : ∫ y in (0 : ℝ)..((N : ℝ) / 2),
        (if a < y then (1 : ℝ) else 0) * (if b < (N : ℝ) / 2 - y then (1 : ℝ) else 0)
      = max ((N : ℝ) / 2 - (a + b)) 0 := integral_indicator_prod_eq a b _ ha hb hR0
  rw [hinner, hatom]
  by_cases hd : a + b < (N : ℝ) / 2
  · -- Case `0 < d < R`: the integrand vanishes below `d`, and above `d` it is the derivative term.
    have hQ := loopArcQ_eq_integral s hs0 hs1 N hab hd
    have hcont : ContinuousOn (fun x => -iteratedDeriv 3 (loopArcG s N) x)
        (uIcc (a + b) ((N : ℝ) / 2)) := by
      rw [uIcc_of_le hd.le]
      refine ContinuousOn.neg ((contDiffOn_iteratedDeriv_open isOpen_Ioo
        (contDiffOn_loopArcG s hs0 hs1 N) 3).continuousOn.mono ?_)
      intro x hx
      exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hcontf : ContinuousOn (fun x => -iteratedDeriv 3 (loopArcG s N) x * max (x - (a + b)) 0)
        (uIcc (a + b) ((N : ℝ) / 2)) :=
      hcont.mul (((continuous_id.sub continuous_const).max continuous_const).continuousOn)
    have hI1 : IntervalIntegrable
        (fun x => -iteratedDeriv 3 (loopArcG s N) x * max (x - (a + b)) 0)
        volume (a + b) ((N : ℝ) / 2) := hcontf.intervalIntegrable
    have hI0 : IntervalIntegrable
        (fun x => -iteratedDeriv 3 (loopArcG s N) x * max (x - (a + b)) 0) volume 0 (a + b) := by
      refine (intervalIntegrable_const (c := (0 : ℝ))).congr_uIoo ?_
      intro x hx
      rw [uIoo_of_le hab.le] at hx
      have hx' : max (x - (a + b)) 0 = 0 := max_eq_right (by linarith [hx.2])
      simp [hx']
    have hsplit := intervalIntegral.integral_add_adjacent_intervals hI0 hI1
    have hEq0 : EqOn (fun x => -iteratedDeriv 3 (loopArcG s N) x * max (x - (a + b)) 0)
        (fun _ => (0 : ℝ)) (uIcc 0 (a + b)) := by
      intro x hx
      rw [uIcc_of_le hab.le] at hx
      simp only [max_eq_right (show x - (a + b) ≤ 0 by linarith [hx.2]), mul_zero]
    have hz0 : ∫ x in (0 : ℝ)..(a + b), -iteratedDeriv 3 (loopArcG s N) x * max (x - (a + b)) 0
        = 0 := by
      rw [intervalIntegral.integral_congr hEq0]
      simp
    have hEq1 : EqOn (fun x => -iteratedDeriv 3 (loopArcG s N) x * max (x - (a + b)) 0)
        (fun x => (x - (a + b)) * (-iteratedDeriv 3 (loopArcG s N) x)) (uIcc (a + b) ((N : ℝ) / 2)) := by
      intro x hx
      rw [uIcc_of_le hd.le] at hx
      show -iteratedDeriv 3 (loopArcG s N) x * max (x - (a + b)) 0
        = (x - (a + b)) * (-iteratedDeriv 3 (loopArcG s N) x)
      rw [max_eq_left (show 0 ≤ x - (a + b) by linarith [hx.1])]
      ring
    rw [hQ, ← hsplit, hz0, zero_add, intervalIntegral.integral_congr hEq1,
      max_eq_left (show 0 ≤ (N : ℝ) / 2 - (a + b) by linarith)]
    ring
  · -- Case `d ≥ R`: both sides vanish, since every integrand vanishes on `[0, R]`.
    have hQ : loopArcQ s N (a + b) = 0 := loopArcQ_eq_zero_of_le s N (not_lt.mp hd)
    have hEq : EqOn (fun x => -iteratedDeriv 3 (loopArcG s N) x * max (x - (a + b)) 0)
        (fun _ => (0 : ℝ)) (uIcc 0 ((N : ℝ) / 2)) := by
      intro x hx
      rw [uIcc_of_le hR0] at hx
      simp only [max_eq_right (show x - (a + b) ≤ 0 by linarith [hx.2, not_lt.mp hd]), mul_zero]
    rw [hQ, intervalIntegral.integral_congr hEq, intervalIntegral.integral_zero,
      max_eq_right (show (N : ℝ) / 2 - (a + b) ≤ 0 by linarith [not_lt.mp hd]), mul_zero,
      add_zero]

end Riesz1

end
end
