/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopArcsRepresentation

/-!
# The arc pairing equals the arc function `Λ`

The arcs part of Lemma B.2: for `t` off the particle positions the
arc-crossing pairing of the cutoff kernel equals the function `Λ(t)` of `loopArcLambda`,

`loopArcPairing N X (loopArcPhi s N t) = loopArcLambda s N X t`.

The proof represents `Q(a + b)` through `loopArcQ_eq_triangle` as an integral over the square
`(0, N/2)²` of the triangle kernel times a product of indicators (`loopArcTriKernel`) plus the
atom `g_N''(N/2)` times a one-dimensional integral (`loopArcAtomKernel`). The pairing commutes
with these parameter integrals (`loopArcPairing_integral_param`), and each product kernel pairs to
a product of discrepancies (`loopArcPairing_arc_product`). The square integral is then converted
to the iterated form of `loopArcLambda` by `integral_loopArcTri_square`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Riesz1

/-- The integral of `1[y < c] f(y)` over `(0, R)` is the interval integral over `(0, c)`, for
`0 ≤ c ≤ R`. -/
theorem integral_Ioo_ite_lt {R c : ℝ} (f : ℝ → ℝ) (hc0 : 0 ≤ c) (hcR : c ≤ R) :
    ∫ y in Ioo (0 : ℝ) R, (if y < c then f y else 0) = ∫ y in (0 : ℝ)..c, f y := by
  have hind : (fun y => if y < c then f y else 0) = Set.indicator (Iio c) f := by
    ext y
    simp only [Set.indicator, mem_Iio]
  have hset : Iio c ∩ Ioo (0 : ℝ) R = Ioo 0 c := by
    ext y
    simp only [mem_inter_iff, mem_Iio, mem_Ioo]
    constructor
    · rintro ⟨h1, h2, _⟩
      exact ⟨h2, h1⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h2, h1, by linarith⟩
  rw [hind, integral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio,
    hset, intervalIntegral.integral_of_le hc0, integral_Ioc_eq_integral_Ioo]

/-- The integral of an integrable function over `(0, R)` is the interval integral over `[0, R]`.
-/
theorem integral_Ioo_eq_interval {R : ℝ} (hR : 0 ≤ R) (g : ℝ → ℝ) :
    ∫ x in Ioo (0 : ℝ) R, g x = ∫ x in (0 : ℝ)..R, g x := by
  rw [intervalIntegral.integral_of_le hR, integral_Ioc_eq_integral_Ioo]

/-- **Triangle conversion of the square integral.** For a function `F` of two variables with the
square integrable, the integral of `ψ(q) F(q)` over the square `(0, N/2)²` is the iterated interval
integral over `u ∈ (0, N/2)`, `v ∈ (0, N/2 - u)`, with the kernel `-g_N'''(u + v)`. -/
theorem integral_loopArcTri_square (s : ℝ) (N : ℕ+) (F : ℝ → ℝ → ℝ)
    (hF : Integrable (fun q : ℝ × ℝ => loopArcTri s N q * F q.1 q.2) (loopArcSq N)) :
    ∫ q, loopArcTri s N q * F q.1 q.2 ∂(loopArcSq N)
      = ∫ u in (0 : ℝ)..((N : ℝ) / 2), ∫ v in (0 : ℝ)..((N : ℝ) / 2 - u),
          -iteratedDeriv 3 (loopArcG s N) (u + v) * F u v := by
  have hR : (0 : ℝ) ≤ (N : ℝ) / 2 := by positivity
  unfold loopArcSq at hF ⊢
  rw [integral_prod _ hF]
  rw [← integral_Ioo_eq_interval hR]
  refine setIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
  -- inner integral in `v`: the indicator `v < N/2 - u` restricts the range to `(0, N/2 - u)`
  have hpt : ∀ v : ℝ, loopArcTri s N (u, v) * F u v
      = (if v < (N : ℝ) / 2 - u then -iteratedDeriv 3 (loopArcG s N) (u + v) * F u v else 0) := by
    intro v
    unfold loopArcTri
    simp only
    split_ifs <;> simp
  simp only [hpt]
  rw [integral_Ioo_ite_lt _ (by linarith [hu.2]) (by linarith [hu.1])]

/-- **Pairing of a triangle kernel.** For `0 < q₁, q₂ ≤ N`, the pairing of the parametric kernel
is `ψ(q)` times the product of the two arc discrepancies. -/
theorem loopArcPairing_triKernel (s : ℝ) (N : ℕ+) (t : ℝ) (X : Configuration N)
    (ht : ∀ (i : Fin (N : ℕ)) (k : ℤ), t ≠ loopArcPos N X i + k * N) (q : ℝ × ℝ)
    (hq1 : 0 < q.1) (hq1N : q.1 ≤ (N : ℝ)) (hq2 : 0 < q.2) (hq2N : q.2 ≤ (N : ℝ)) :
    loopArcPairing N X (fun z u => loopArcTriKernel s N t q z u)
      = loopArcTri s N q * (loopDiscrepancy (t - q.1) q.1 X * loopDiscrepancy t q.2 X) := by
  have h := loopArcPairing_arc_product N X t q.1 q.2 hq1 hq1N hq2 hq2N ht
  rw [show (fun z u => loopArcTriKernel s N t q z u)
      = fun z u => loopArcTri s N q * ((if loopArcFwd N (t - z) < q.1 then (1 : ℝ) else 0)
        * (if loopArcFwd N (u - t) < q.2 then (1 : ℝ) else 0)) from rfl,
    loopArcPairing_const_mul, h]

/-- **Pairing of the atom kernel.** For `0 < w < N/2`, the pairing of the atom kernel is the
product of the two arc discrepancies of lengths `w` and `N/2 - w`. -/
theorem loopArcPairing_atomKernel (N : ℕ+) (X : Configuration N) (t w : ℝ)
    (ht : ∀ (i : Fin (N : ℕ)) (k : ℤ), t ≠ loopArcPos N X i + k * N)
    (hw0 : 0 < w) (hwR : w < (N : ℝ) / 2) :
    loopArcPairing N X (fun z u => loopArcAtomKernel N t w z u)
      = loopDiscrepancy (t - w) w X * loopDiscrepancy t ((N : ℝ) / 2 - w) X := by
  have hN : (0 : ℝ) < N := by have := N.pos; exact_mod_cast this
  exact loopArcPairing_arc_product N X t w ((N : ℝ) / 2 - w) hw0 (by linarith) (by linarith)
    (by linarith) ht

/-- The forward distance from `t` to a particle is positive when `t` is off the particles. -/
theorem loopArcFwd_pos_particle (N : ℕ+) (X : Configuration N) (t : ℝ)
    (ht : ∀ (i : Fin (N : ℕ)) (k : ℤ), t ≠ loopArcPos N X i + k * N) (i : Fin (N : ℕ)) :
    0 < loopArcFwd N (t - loopArcPos N X i) := by
  refine loopArcFwd_pos_of_ne N _ (fun k hk => ht i k ?_)
  linarith

/-- The forward distance from a particle to `t` is positive when `t` is off the particles. -/
theorem loopArcFwd_pos_particle' (N : ℕ+) (X : Configuration N) (t : ℝ)
    (ht : ∀ (i : Fin (N : ℕ)) (k : ℤ), t ≠ loopArcPos N X i + k * N) (j : Fin (N : ℕ)) :
    0 < loopArcFwd N (loopArcPos N X j - t) := by
  refine loopArcFwd_pos_of_ne N _ (fun k hk => ht j (-k) ?_)
  push_cast
  linarith

/-- The arc-crossing pairing of the parametric kernel, as an integral in `q` over the square.
This is the parametric Fubini exchange of `loopArcPairing_integral_param`, with the four blocks
supplied by the integrability lemmas of `LoopArcsRepresentation`. -/
theorem loopArcPairing_triKernel_integral (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (N : ℕ+)
    (X : Configuration N) (t : ℝ)
    (ht : ∀ (i : Fin (N : ℕ)) (k : ℤ), t ≠ loopArcPos N X i + k * N) :
    loopArcPairing N X (fun z u => ∫ q, loopArcTriKernel s N t q z u ∂(loopArcSq N))
      = ∫ q, loopArcTri s N q * (loopDiscrepancy (t - q.1) q.1 X * loopDiscrepancy t q.2 X)
          ∂(loopArcSq N) := by
  have hP := loopArcPairing_integral_param (loopArcSq N) N X
    (fun q z u => loopArcTriKernel s N t q z u)
    (fun i j => integrable_triKernel_left s hs0 hs1 N t _ _
      (loopArcFwd_pos_particle N X t ht i))
    (fun i => integrable_triKernel_prod_left s hs0 hs1 N t _
      (loopArcFwd_pos_particle N X t ht i))
    (fun j => integrable_triKernel_prod_right s hs0 hs1 N t _
      (loopArcFwd_pos_particle' N X t ht j))
    (integrable_triKernel_prod_bg s hs0 hs1 N t)
  rw [hP]
  refine integral_congr_ae ?_
  filter_upwards [ae_loopArcSq N] with q hq
  exact loopArcPairing_triKernel s N t X ht q hq.1 (by linarith [hq.2.1]) hq.2.2.1
    (by linarith [hq.2.2.2])

/-- The atom kernel is bounded by one. -/
theorem abs_atomKernel_le_one (N : ℕ+) (t w z u : ℝ) : |loopArcAtomKernel N t w z u| ≤ 1 := by
  unfold loopArcAtomKernel
  have key : |(if loopArcFwd N (t - z) < w then (1 : ℝ) else 0)|
      * |(if loopArcFwd N (u - t) < (N : ℝ) / 2 - w then (1 : ℝ) else 0)| ≤ 1 := by
    split_ifs <;> norm_num
  rw [abs_mul]
  exact key

/-- Measurability of the atom kernel in `(w, z, u)`. -/
theorem measurable_atomKernel_full (N : ℕ+) (t : ℝ) :
    Measurable (fun p : ℝ × (ℝ × ℝ) => loopArcAtomKernel N t p.1 p.2.1 p.2.2) := by
  unfold loopArcAtomKernel
  refine Measurable.mul (Measurable.ite ?_ measurable_const measurable_const)
    (Measurable.ite ?_ measurable_const measurable_const)
  · exact measurableSet_lt ((measurable_loopArcFwd_of N).comp
      (measurable_const.sub (measurable_fst.comp measurable_snd))) measurable_fst
  · exact measurableSet_lt ((measurable_loopArcFwd_of N).comp
      ((measurable_snd.comp measurable_snd).sub measurable_const))
      (measurable_const.sub measurable_fst)

/-- Measurability of the atom kernel in `(w, u)` for a fixed particle `z`. -/
theorem measurable_atomKernel_wu (N : ℕ+) (t z : ℝ) :
    Measurable (fun q : ℝ × ℝ => loopArcAtomKernel N t q.1 z q.2) := by
  unfold loopArcAtomKernel
  refine Measurable.mul (Measurable.ite ?_ measurable_const measurable_const)
    (Measurable.ite ?_ measurable_const measurable_const)
  · exact measurableSet_lt measurable_const measurable_fst
  · exact measurableSet_lt ((measurable_loopArcFwd_of N).comp (measurable_snd.sub measurable_const))
      (measurable_const.sub measurable_fst)

/-- Measurability of the atom kernel in `(w, z)` for a fixed particle `u`. -/
theorem measurable_atomKernel_wz (N : ℕ+) (t u : ℝ) :
    Measurable (fun q : ℝ × ℝ => loopArcAtomKernel N t q.1 q.2 u) := by
  unfold loopArcAtomKernel
  refine Measurable.mul (Measurable.ite ?_ measurable_const measurable_const)
    (Measurable.ite ?_ measurable_const measurable_const)
  · exact measurableSet_lt ((measurable_loopArcFwd_of N).comp
      (measurable_const.sub measurable_snd)) measurable_fst
  · exact measurableSet_lt measurable_const (measurable_const.sub measurable_fst)

/-- Measurability of the atom kernel in `w` for fixed `z`, `u`. -/
theorem measurable_atomKernel_w (N : ℕ+) (t z u : ℝ) :
    Measurable (fun w : ℝ => loopArcAtomKernel N t w z u) := by
  unfold loopArcAtomKernel
  refine Measurable.mul (Measurable.ite ?_ measurable_const measurable_const)
    (Measurable.ite ?_ measurable_const measurable_const)
  · exact measurableSet_lt measurable_const measurable_id
  · exact measurableSet_lt measurable_const (measurable_const.sub measurable_id)

/-- **The atom pairing.** The pairing of the atom integral is the integral of the pairings. -/
theorem loopArcPairing_atom_integral (N : ℕ+) (X : Configuration N) (t : ℝ)
    (ht : ∀ (i : Fin (N : ℕ)) (k : ℤ), t ≠ loopArcPos N X i + k * N) :
    loopArcPairing N X (fun z u => ∫ w, loopArcAtomKernel N t w z u
        ∂(volume.restrict (Ioo (0 : ℝ) ((N : ℝ) / 2))))
      = ∫ w, loopDiscrepancy (t - w) w X * loopDiscrepancy t ((N : ℝ) / 2 - w) X
          ∂(volume.restrict (Ioo (0 : ℝ) ((N : ℝ) / 2))) := by
  have hP := loopArcPairing_integral_param (volume.restrict (Ioo (0 : ℝ) ((N : ℝ) / 2))) N X
    (fun w z u => loopArcAtomKernel N t w z u)
    (fun i j => integrable_of_ae_abs_le (measurable_atomKernel_w N t _ _)
      (ae_of_all _ fun w => abs_atomKernel_le_one N t w _ _))
    (fun i => integrable_of_ae_abs_le (measurable_atomKernel_wu N t _)
      (ae_of_all _ fun q => abs_atomKernel_le_one N t q.1 _ q.2))
    (fun j => integrable_of_ae_abs_le (measurable_atomKernel_wz N t _)
      (ae_of_all _ fun q => abs_atomKernel_le_one N t q.1 q.2 _))
    (integrable_of_ae_abs_le (measurable_atomKernel_full N t)
      (ae_of_all _ fun q => abs_atomKernel_le_one N t q.1 q.2.1 q.2.2))
  rw [hP]
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with w hw
  exact loopArcPairing_atomKernel N X t w ht hw.1 hw.2

/-- The atom integral over `(0, N/2)` is the interval integral of the two indicators. -/
theorem integral_atomKernel_eq (N : ℕ+) (t z u : ℝ) :
    ∫ w, loopArcAtomKernel N t w z u ∂(volume.restrict (Ioo (0 : ℝ) ((N : ℝ) / 2)))
      = ∫ w in (0 : ℝ)..((N : ℝ) / 2), (if loopArcFwd N (t - z) < w then (1 : ℝ) else 0)
          * (if loopArcFwd N (u - t) < (N : ℝ) / 2 - w then (1 : ℝ) else 0) := by
  have hR : (0 : ℝ) ≤ (N : ℝ) / 2 := by positivity
  rw [← integral_Ioo_eq_interval hR]
  rfl

/-- **Pointwise decomposition of the arc cutoff.** For `t` off the particles, and `z` with
`fwd(t - z) > 0`, the cutoff `Q(a + b)` splits as the parametric triangle integral plus the atom
`g_N''(N/2)` times the one-dimensional integral. -/
theorem loopArcPhi_eq_decomp (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (N : ℕ+) (t z u : ℝ)
    (hz : 0 < loopArcFwd N (t - z)) :
    loopArcPhi s N t z u
      = (∫ q, loopArcTriKernel s N t q z u ∂(loopArcSq N))
        + iteratedDeriv 2 (loopArcG s N) ((N : ℝ) / 2)
          * ∫ w, loopArcAtomKernel N t w z u ∂(volume.restrict (Ioo (0 : ℝ) ((N : ℝ) / 2))) := by
  have hb := loopArcFwd_nonneg N (u - t)
  have hK : ∫ q, loopArcTriKernel s N t q z u ∂(loopArcSq N)
      = ∫ x in (0 : ℝ)..((N : ℝ) / 2), ∫ y in (0 : ℝ)..((N : ℝ) / 2 - x),
          -iteratedDeriv 3 (loopArcG s N) (x + y)
            * ((if loopArcFwd N (t - z) < x then (1 : ℝ) else 0)
              * (if loopArcFwd N (u - t) < y then (1 : ℝ) else 0)) := by
    have hF := integrable_triKernel_left s hs0 hs1 N t z u hz
    have := integral_loopArcTri_square s N
      (fun x y => (if loopArcFwd N (t - z) < x then (1 : ℝ) else 0)
        * (if loopArcFwd N (u - t) < y then (1 : ℝ) else 0)) hF
    exact this
  unfold loopArcPhi
  rw [loopArcQ_eq_triangle s hs0 hs1 N hz.le hb (by linarith), hK, integral_atomKernel_eq]

/-- For a.e. background point `z` the forward distance to `t` is positive, since the exceptional
set `{z : fwd(t - z) = 0}` is countable. -/
theorem ae_loopArcFwd_pos (N : ℕ+) (t : ℝ) :
    ∀ᵐ z ∂(volume.restrict (Ioc (0 : ℝ) N)), 0 < loopArcFwd N (t - z) := by
  have hcount : Set.Countable {z : ℝ | ¬ (0 < loopArcFwd N (t - z))} := by
    refine (Set.countable_range (fun k : ℤ => t - (k : ℝ) * N)).mono ?_
    intro z hz
    have h0 : loopArcFwd N (t - z) = 0 := le_antisymm (not_lt.mp hz) (loopArcFwd_nonneg N _)
    have hsub := loopArcFwd_sub_floor N (t - z)
    refine ⟨⌊(t - z) / N⌋, ?_⟩
    rw [h0] at hsub
    simp only
    linarith
  have hz0 : volume {z : ℝ | ¬ (0 < loopArcFwd N (t - z))} = 0 := hcount.measure_zero _
  rw [ae_restrict_iff' measurableSet_Ioc]
  filter_upwards [MeasureTheory.ae_iff.mpr hz0] with z hz _
  exact hz

/-- **Congruence of the arc pairing.** Two kernels agreeing when the first argument is off the
arc's start point pair equally, provided the particles are off `t` and the background is a.e. off
`t`. -/
theorem loopArcPairing_congr_pos (N : ℕ+) (X : Configuration N) (t : ℝ)
    (G1 G2 : ℝ → ℝ → ℝ)
    (hpos : ∀ i : Fin (N : ℕ), 0 < loopArcFwd N (t - loopArcPos N X i))
    (h : ∀ z u : ℝ, 0 < loopArcFwd N (t - z) → G1 z u = G2 z u) :
    loopArcPairing N X G1 = loopArcPairing N X G2 := by
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have hae : ∀ᵐ z ∂volume, z ∈ Ioc (0 : ℝ) N → 0 < loopArcFwd N (t - z) :=
    (ae_restrict_iff' measurableSet_Ioc).mp (ae_loopArcFwd_pos N t)
  unfold loopArcPairing
  have e1 : (∑ i : Fin (N : ℕ), ∑ j : Fin (N : ℕ), G1 (loopArcPos N X i) (loopArcPos N X j))
      = ∑ i : Fin (N : ℕ), ∑ j : Fin (N : ℕ), G2 (loopArcPos N X i) (loopArcPos N X j) :=
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => h _ _ (hpos i)
  have e2 : (∑ i : Fin (N : ℕ), ∫ u in (0 : ℝ)..(N : ℝ), G1 (loopArcPos N X i) u)
      = ∑ i : Fin (N : ℕ), ∫ u in (0 : ℝ)..(N : ℝ), G2 (loopArcPos N X i) u :=
    Finset.sum_congr rfl fun i _ => intervalIntegral.integral_congr fun u _ => h _ _ (hpos i)
  have e3 : (∑ j : Fin (N : ℕ), ∫ z in (0 : ℝ)..(N : ℝ), G1 z (loopArcPos N X j))
      = ∑ j : Fin (N : ℕ), ∫ z in (0 : ℝ)..(N : ℝ), G2 z (loopArcPos N X j) := by
    refine Finset.sum_congr rfl fun j _ => intervalIntegral.integral_congr_ae ?_
    filter_upwards [hae] with z hz hzI
    rw [Set.uIoc_of_le hN0] at hzI
    exact h z _ (hz hzI)
  have e4 : (∫ z in (0 : ℝ)..(N : ℝ), ∫ u in (0 : ℝ)..(N : ℝ), G1 z u)
      = ∫ z in (0 : ℝ)..(N : ℝ), ∫ u in (0 : ℝ)..(N : ℝ), G2 z u := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hae] with z hz hzI
    rw [Set.uIoc_of_le hN0] at hzI
    exact intervalIntegral.integral_congr fun u _ => h z u (hz hzI)
  rw [e1, e2, e3, e4]

/-- **Linearity of the arc pairing** for two kernels whose integrability (as functions on the
background square and on the slices at the particles) is given. -/
theorem loopArcPairing_add_slices (N : ℕ+) (X : Configuration N) (G H : ℝ → ℝ → ℝ)
    (hG : Integrable (fun zu : ℝ × ℝ => G zu.1 zu.2)
      ((volume.restrict (Ioc (0 : ℝ) N)).prod (volume.restrict (Ioc (0 : ℝ) N))))
    (hH : Integrable (fun zu : ℝ × ℝ => H zu.1 zu.2)
      ((volume.restrict (Ioc (0 : ℝ) N)).prod (volume.restrict (Ioc (0 : ℝ) N))))
    (hGl : ∀ i : Fin (N : ℕ), Integrable (fun u => G (loopArcPos N X i) u)
      (volume.restrict (Ioc (0 : ℝ) N)))
    (hGr : ∀ j : Fin (N : ℕ), Integrable (fun z => G z (loopArcPos N X j))
      (volume.restrict (Ioc (0 : ℝ) N)))
    (hHl : ∀ i : Fin (N : ℕ), Integrable (fun u => H (loopArcPos N X i) u)
      (volume.restrict (Ioc (0 : ℝ) N)))
    (hHr : ∀ j : Fin (N : ℕ), Integrable (fun z => H z (loopArcPos N X j))
      (volume.restrict (Ioc (0 : ℝ) N))) :
    loopArcPairing N X (fun z u => G z u + H z u)
      = loopArcPairing N X G + loopArcPairing N X H := by
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have s3 : ∫ z in Ioc (0 : ℝ) N, ∫ u in Ioc (0 : ℝ) N, (G z u + H z u)
      = (∫ z in Ioc (0 : ℝ) N, ∫ u in Ioc (0 : ℝ) N, G z u)
        + ∫ z in Ioc (0 : ℝ) N, ∫ u in Ioc (0 : ℝ) N, H z u := by
    have i1 : Integrable (fun z => ∫ u in Ioc (0 : ℝ) N, G z u)
        (volume.restrict (Ioc (0 : ℝ) N)) := hG.integral_prod_left
    have i2 : Integrable (fun z => ∫ u in Ioc (0 : ℝ) N, H z u)
        (volume.restrict (Ioc (0 : ℝ) N)) := hH.integral_prod_left
    rw [← integral_add i1 i2]
    refine integral_congr_ae ?_
    filter_upwards [hG.prod_right_ae, hH.prod_right_ae] with z h1 h2
    exact integral_add h1 h2
  unfold loopArcPairing
  simp only [intervalIntegral.integral_of_le hN0, Finset.sum_add_distrib]
  have s1 : ∀ i : Fin (N : ℕ), ∫ u in Ioc (0 : ℝ) N, (G (loopArcPos N X i) u + H (loopArcPos N X i) u)
      = (∫ u in Ioc (0 : ℝ) N, G (loopArcPos N X i) u)
        + ∫ u in Ioc (0 : ℝ) N, H (loopArcPos N X i) u :=
    fun i => integral_add (hGl i) (hHl i)
  have s2 : ∀ j : Fin (N : ℕ), ∫ z in Ioc (0 : ℝ) N, (G z (loopArcPos N X j) + H z (loopArcPos N X j))
      = (∫ z in Ioc (0 : ℝ) N, G z (loopArcPos N X j))
        + ∫ z in Ioc (0 : ℝ) N, H z (loopArcPos N X j) :=
    fun j => integral_add (hGr j) (hHr j)
  simp only [s1, s2, Finset.sum_add_distrib, s3]
  ring

/-- Integrability of the triangle kernel times the left indicator and the background coordinate. -/
theorem integrable_triKernel_left_mul (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (N : ℕ+) (a : ℝ)
    (ha : 0 < a) :
    Integrable (fun q : ℝ × ℝ => loopArcTri s N q * ((if a < q.1 then (1 : ℝ) else 0) * q.2))
      (loopArcSq N) := by
  obtain ⟨C, hC, hD⟩ := loopArcTri_left_le s hs0 hs1
  have hmeas : Measurable (fun q : ℝ × ℝ => loopArcTri s N q * ((if a < q.1 then (1 : ℝ) else 0)
      * q.2)) :=
    Measurable.mul (measurable_loopArcTri s N) (Measurable.mul
      (Measurable.ite (measurableSet_lt measurable_const measurable_fst) measurable_const
        measurable_const) measurable_snd)
  have hR : (0 : ℝ) ≤ (N : ℝ) / 2 := by positivity
  refine integrable_of_ae_abs_le (M := C * a ^ (-s - 3) * ((N : ℝ) / 2)) hmeas ?_
  filter_upwards [ae_loopArcSq N] with q hq
  have h1 := hD N a q ha hq.1 hq.2.2.1
  have hi : 0 ≤ (if a < q.1 then (1 : ℝ) else 0) := by split_ifs <;> norm_num
  rw [abs_mul, abs_mul, abs_of_nonneg hi, abs_of_nonneg hq.2.2.1.le]
  have hC' : 0 ≤ C * a ^ (-s - 3) := by positivity
  calc |loopArcTri s N q| * ((if a < q.1 then (1 : ℝ) else 0) * q.2)
      = (|loopArcTri s N q| * (if a < q.1 then (1 : ℝ) else 0)) * q.2 := by ring
    _ ≤ (C * a ^ (-s - 3)) * ((N : ℝ) / 2) :=
        mul_le_mul h1 hq.2.2.2.le hq.2.2.1.le hC'
    _ = C * a ^ (-s - 3) * ((N : ℝ) / 2) := rfl

/-- Integrability of the triangle kernel times the right indicator and the first coordinate. -/
theorem integrable_triKernel_right_mul (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (N : ℕ+) (b : ℝ)
    (hb : 0 < b) :
    Integrable (fun q : ℝ × ℝ => loopArcTri s N q * (q.1 * (if b < q.2 then (1 : ℝ) else 0)))
      (loopArcSq N) := by
  obtain ⟨C, hC, hD⟩ := loopArcTri_right_le s hs0 hs1
  have hmeas : Measurable (fun q : ℝ × ℝ => loopArcTri s N q * (q.1
      * (if b < q.2 then (1 : ℝ) else 0))) :=
    Measurable.mul (measurable_loopArcTri s N) (Measurable.mul measurable_fst
      (Measurable.ite (measurableSet_lt measurable_const measurable_snd) measurable_const
        measurable_const))
  refine integrable_of_ae_abs_le (M := C * b ^ (-s - 3) * ((N : ℝ) / 2)) hmeas ?_
  filter_upwards [ae_loopArcSq N] with q hq
  have h1 := hD N b q hb hq.1 hq.2.2.1
  have hi : 0 ≤ (if b < q.2 then (1 : ℝ) else 0) := by split_ifs <;> norm_num
  rw [abs_mul, abs_mul, abs_of_nonneg hi, abs_of_nonneg hq.1.le]
  have hC' : 0 ≤ C * b ^ (-s - 3) := by positivity
  have hq1 : q.1 ≤ (N : ℝ) / 2 := hq.2.1.le
  calc |loopArcTri s N q| * (q.1 * (if b < q.2 then (1 : ℝ) else 0))
      = q.1 * (|loopArcTri s N q| * (if b < q.2 then (1 : ℝ) else 0)) := by ring
    _ ≤ ((N : ℝ) / 2) * (C * b ^ (-s - 3)) :=
        mul_le_mul hq1 h1 (mul_nonneg (abs_nonneg _) hi) (by positivity)
    _ = C * b ^ (-s - 3) * ((N : ℝ) / 2) := by ring

/-- **Expansion of the discrepancy product.** On the square, the triangle kernel times the product
of the two arc discrepancies is a sum of integrable pieces: the parametric kernels at the particles
and the two indicator-weighted pieces, which are bounded by the single-particle bounds. -/
theorem integrable_triKernel_discrepancy (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (N : ℕ+)
    (X : Configuration N) (t : ℝ)
    (ht : ∀ (i : Fin (N : ℕ)) (k : ℤ), t ≠ loopArcPos N X i + k * N) :
    Integrable (fun q : ℝ × ℝ => loopArcTri s N q
      * (loopDiscrepancy (t - q.1) q.1 X * loopDiscrepancy t q.2 X)) (loopArcSq N) := by
  have hexp : ∀ q : ℝ × ℝ, 0 < q.1 → q.1 ≤ (N : ℝ) → 0 < q.2 → q.2 ≤ (N : ℝ) →
      loopArcTri s N q * (loopDiscrepancy (t - q.1) q.1 X * loopDiscrepancy t q.2 X)
        = (∑ i : Fin (N : ℕ), ∑ j : Fin (N : ℕ),
            loopArcTriKernel s N t q (loopArcPos N X i) (loopArcPos N X j))
          - (∑ i : Fin (N : ℕ), loopArcTri s N q
              * ((if loopArcFwd N (t - loopArcPos N X i) < q.1 then (1 : ℝ) else 0) * q.2))
          - (∑ j : Fin (N : ℕ), loopArcTri s N q
              * (q.1 * (if loopArcFwd N (loopArcPos N X j - t) < q.2 then (1 : ℝ) else 0)))
          + loopArcTri s N q * (q.1 * q.2) := by
    intro q h1 h1N h2 h2N
    rw [loopDiscrepancy_arc_left N X t q.1 h1 h1N ht,
      loopDiscrepancy_arc_right N X t q.2 h2 h2N ht]
    unfold loopArcTriKernel
    have key : (∑ i : Fin (N : ℕ), (if loopArcFwd N (t - loopArcPos N X i) < q.1 then (1 : ℝ) else 0)
          - q.1) * ((∑ j : Fin (N : ℕ), (if loopArcFwd N (loopArcPos N X j - t) < q.2 then (1 : ℝ) else 0))
          - q.2)
        = (∑ i : Fin (N : ℕ), (if loopArcFwd N (t - loopArcPos N X i) < q.1 then (1 : ℝ) else 0))
            * (∑ j : Fin (N : ℕ), (if loopArcFwd N (loopArcPos N X j - t) < q.2 then (1 : ℝ) else 0))
          - (∑ i : Fin (N : ℕ), (if loopArcFwd N (t - loopArcPos N X i) < q.1 then (1 : ℝ) else 0)) * q.2
          - q.1 * (∑ j : Fin (N : ℕ), (if loopArcFwd N (loopArcPos N X j - t) < q.2 then (1 : ℝ) else 0))
          + q.1 * q.2 := by ring
    rw [key]
    simp only [mul_add, mul_sub, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
  have hA : Integrable (fun q : ℝ × ℝ => ∑ i : Fin (N : ℕ), ∑ j : Fin (N : ℕ),
      loopArcTriKernel s N t q (loopArcPos N X i) (loopArcPos N X j)) (loopArcSq N) :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      integrable_triKernel_left s hs0 hs1 N t _ _ (loopArcFwd_pos_particle N X t ht i)
  have hB : Integrable (fun q : ℝ × ℝ => ∑ i : Fin (N : ℕ), loopArcTri s N q
      * ((if loopArcFwd N (t - loopArcPos N X i) < q.1 then (1 : ℝ) else 0) * q.2))
      (loopArcSq N) :=
    integrable_finsetSum _ fun i _ => integrable_triKernel_left_mul s hs0 hs1 N _
      (loopArcFwd_pos_particle N X t ht i)
  have hC : Integrable (fun q : ℝ × ℝ => ∑ j : Fin (N : ℕ), loopArcTri s N q
      * (q.1 * (if loopArcFwd N (loopArcPos N X j - t) < q.2 then (1 : ℝ) else 0)))
      (loopArcSq N) :=
    integrable_finsetSum _ fun j _ => integrable_triKernel_right_mul s hs0 hs1 N _
      (loopArcFwd_pos_particle' N X t ht j)
  have hD : Integrable (fun q : ℝ × ℝ => loopArcTri s N q * (q.1 * q.2)) (loopArcSq N) := by
    refine Integrable.mono' (integrable_loopArcTri_mul s hs0 hs1 N)
      ((measurable_loopArcTri s N).mul (measurable_fst.mul measurable_snd)).aestronglyMeasurable ?_
    filter_upwards [ae_loopArcSq N] with q hq
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mul_pos hq.1 hq.2.2.1).le]
  refine Integrable.congr (((hA.sub hB).sub hC).add hD) ?_
  have hR : (0 : ℝ) ≤ (N : ℝ) / 2 := by positivity
  filter_upwards [ae_loopArcSq N] with q hq
  exact (hexp q hq.1 (by linarith [hq.2.1, hR]) hq.2.2.1 (by linarith [hq.2.2.2, hR])).symm

/-- **Triangle conversion of the discrepancy product.** -/
theorem integral_triKernel_discrepancy_eq (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (N : ℕ+)
    (X : Configuration N) (t : ℝ)
    (ht : ∀ (i : Fin (N : ℕ)) (k : ℤ), t ≠ loopArcPos N X i + k * N) :
    ∫ q, loopArcTri s N q * (loopDiscrepancy (t - q.1) q.1 X * loopDiscrepancy t q.2 X)
        ∂(loopArcSq N)
      = ∫ u in (0 : ℝ)..((N : ℝ) / 2), ∫ v in (0 : ℝ)..((N : ℝ) / 2 - u),
          -iteratedDeriv 3 (loopArcG s N) (u + v)
            * (loopDiscrepancy (t - u) u X * loopDiscrepancy t v X) :=
  integral_loopArcTri_square s N (fun x y => loopDiscrepancy (t - x) x X * loopDiscrepancy t y X)
    (integrable_triKernel_discrepancy s hs0 hs1 N X t ht)

/-- The background-background atom of the arc kernel is integrable against the square. -/
theorem integrable_atom_prod (N : ℕ+) (t : ℝ) (μ : Measure ℝ) [IsFiniteMeasure μ] (ν : Measure ℝ)
    [IsFiniteMeasure ν] :
    Integrable (fun p : ℝ × (ℝ × ℝ) => loopArcAtomKernel N t p.1 p.2.1 p.2.2)
      (μ.prod (ν.prod ν)) :=
  integrable_of_ae_abs_le (measurable_atomKernel_full N t)
    (ae_of_all _ fun p => abs_atomKernel_le_one N t p.1 p.2.1 p.2.2)

/-- **The arc pairing equals the arc function `Λ`.** For `t` off the particle positions,
`loopArcPairing N X (loopArcPhi s N t) = loopArcLambda s N X t`, as in the paper and
the representation step of the arcs part of Lemma B.2. -/
theorem loopArcPairing_phi_eq_lambda (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (N : ℕ+) (t : ℝ)
    (X : Configuration N)
    (ht : ∀ (i : Fin (N : ℕ)) (k : ℤ), t ≠ loopArcPos N X i + k * N) :
    loopArcPairing N X (loopArcPhi s N t) = loopArcLambda s N X t := by
  have hR : (0 : ℝ) ≤ (N : ℝ) / 2 := by positivity
  have hposA := fun i => loopArcFwd_pos_particle N X t ht i
  have hposB := fun j => loopArcFwd_pos_particle' N X t ht j
  -- the pairing is the sum of the square integral and the atom integral
  have hdecomp := loopArcPairing_congr_pos N X t (loopArcPhi s N t)
    (fun z u => (∫ q, loopArcTriKernel s N t q z u ∂(loopArcSq N))
      + iteratedDeriv 2 (loopArcG s N) ((N : ℝ) / 2)
        * ∫ w, loopArcAtomKernel N t w z u ∂(volume.restrict (Ioo (0 : ℝ) ((N : ℝ) / 2)))) hposA
    (fun z u hz => loopArcPhi_eq_decomp s hs0 hs1 N t z u hz)
  rw [hdecomp]
  -- integrability of the two parts against the background square
  have hGint : Integrable (fun zu : ℝ × ℝ => ∫ q, loopArcTriKernel s N t q zu.1 zu.2 ∂(loopArcSq N))
      ((volume.restrict (Ioc (0 : ℝ) N)).prod (volume.restrict (Ioc (0 : ℝ) N))) :=
    (integrable_triKernel_prod_bg s hs0 hs1 N t).integral_prod_right
  have hHint : Integrable (fun zu : ℝ × ℝ =>
      ∫ w, loopArcAtomKernel N t w zu.1 zu.2 ∂(volume.restrict (Ioo (0 : ℝ) ((N : ℝ) / 2))))
      ((volume.restrict (Ioc (0 : ℝ) N)).prod (volume.restrict (Ioc (0 : ℝ) N))) :=
    (integrable_atom_prod N t (volume.restrict (Ioo (0 : ℝ) ((N : ℝ) / 2)))
      (volume.restrict (Ioc (0 : ℝ) N))).integral_prod_right
  have hGl : ∀ i : Fin (N : ℕ), Integrable (fun u => ∫ q, loopArcTriKernel s N t q (loopArcPos N X i) u
      ∂(loopArcSq N)) (volume.restrict (Ioc (0 : ℝ) N)) := fun i =>
    (integrable_triKernel_prod_left s hs0 hs1 N t _ (hposA i)).integral_prod_right
  have hGr : ∀ j : Fin (N : ℕ), Integrable (fun z => ∫ q, loopArcTriKernel s N t q z (loopArcPos N X j)
      ∂(loopArcSq N)) (volume.restrict (Ioc (0 : ℝ) N)) := fun j =>
    (integrable_triKernel_prod_right s hs0 hs1 N t _ (hposB j)).integral_prod_right
  have hHl : ∀ i : Fin (N : ℕ), Integrable (fun u => iteratedDeriv 2 (loopArcG s N) ((N : ℝ) / 2)
      * ∫ w, loopArcAtomKernel N t w (loopArcPos N X i) u
        ∂(volume.restrict (Ioo (0 : ℝ) ((N : ℝ) / 2)))) (volume.restrict (Ioc (0 : ℝ) N)) := fun i => by
    have h : Integrable (fun q : ℝ × ℝ => loopArcAtomKernel N t q.1 (loopArcPos N X i) q.2)
        ((volume.restrict (Ioo (0 : ℝ) ((N : ℝ) / 2))).prod (volume.restrict (Ioc (0 : ℝ) N))) :=
      integrable_of_ae_abs_le (measurable_atomKernel_wu N t _)
        (ae_of_all _ fun q => abs_atomKernel_le_one N t q.1 _ q.2)
    exact (h.integral_prod_right).const_mul _
  have hHr : ∀ j : Fin (N : ℕ), Integrable (fun z => iteratedDeriv 2 (loopArcG s N) ((N : ℝ) / 2)
      * ∫ w, loopArcAtomKernel N t w z (loopArcPos N X j)
        ∂(volume.restrict (Ioo (0 : ℝ) ((N : ℝ) / 2)))) (volume.restrict (Ioc (0 : ℝ) N)) := fun j => by
    have h : Integrable (fun q : ℝ × ℝ => loopArcAtomKernel N t q.1 q.2 (loopArcPos N X j))
        ((volume.restrict (Ioo (0 : ℝ) ((N : ℝ) / 2))).prod (volume.restrict (Ioc (0 : ℝ) N))) :=
      integrable_of_ae_abs_le (measurable_atomKernel_wz N t _)
        (ae_of_all _ fun q => abs_atomKernel_le_one N t q.1 q.2 _)
    exact (h.integral_prod_right).const_mul _
  -- split the pairing and evaluate both parts
  rw [loopArcPairing_add_slices N X (fun z u => ∫ q, loopArcTriKernel s N t q z u ∂(loopArcSq N))
    (fun z u => iteratedDeriv 2 (loopArcG s N) ((N : ℝ) / 2)
      * ∫ w, loopArcAtomKernel N t w z u ∂(volume.restrict (Ioo (0 : ℝ) ((N : ℝ) / 2))))
    hGint (hHint.const_mul _) hGl hGr hHl hHr]
  rw [loopArcPairing_const_mul N X (iteratedDeriv 2 (loopArcG s N) ((N : ℝ) / 2))
    (fun z u => ∫ w, loopArcAtomKernel N t w z u ∂(volume.restrict (Ioo (0 : ℝ) ((N : ℝ) / 2))))]
  rw [loopArcPairing_triKernel_integral s hs0 hs1 N X t ht, loopArcPairing_atom_integral N X t ht,
    integral_triKernel_discrepancy_eq s hs0 hs1 N X t ht, integral_Ioo_eq_interval hR]
  unfold loopArcLambda
  simp only [mul_assoc]


/-- **Integrability of the arc pairing in `t`.** The pairing `t ↦ P_t` of the arc cutoff is
arclength integrable on `(0, N]`, for every configuration. Its four blocks are integrable by the
integrability of `loopArcPhi` on the products. -/
theorem integrable_loopArcPairing_phi (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (N : ℕ+)
    (X : Configuration N) :
    Integrable (fun t => loopArcPairing N X (loopArcPhi s N t))
      (volume.restrict (Ioc (0 : ℝ) N)) := by
  have hN0 : (0 : ℝ) ≤ N := by positivity
  unfold loopArcPairing
  simp only [intervalIntegral.integral_of_le hN0]
  have iA : Integrable (fun t => ∑ i : Fin (N : ℕ), ∑ j : Fin (N : ℕ),
      loopArcPhi s N t (loopArcPos N X i) (loopArcPos N X j)) (volume.restrict (Ioc (0 : ℝ) N)) :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hN0).mp
        (intervalIntegrable_loopArcPhi s N _ _ 0 N)
  have iB : Integrable (fun t => ∑ i : Fin (N : ℕ), ∫ u in Ioc (0 : ℝ) N,
      loopArcPhi s N t (loopArcPos N X i) u) (volume.restrict (Ioc (0 : ℝ) N)) :=
    integrable_finsetSum _ fun i _ =>
      (integrable_loopArcPhi_fixed_left s hs0 hs1 N (loopArcPos N X i)).integral_prod_left
  have iC : Integrable (fun t => ∑ j : Fin (N : ℕ), ∫ z in Ioc (0 : ℝ) N,
      loopArcPhi s N t z (loopArcPos N X j)) (volume.restrict (Ioc (0 : ℝ) N)) :=
    integrable_finsetSum _ fun j _ =>
      (integrable_loopArcPhi_fixed_right s hs0 hs1 N (loopArcPos N X j)).integral_prod_left
  have hT := integrable_loopArcPhi_triple s hs0 hs1 N
  have iD : Integrable (fun t => ∫ z in Ioc (0 : ℝ) N, ∫ u in Ioc (0 : ℝ) N,
      loopArcPhi s N t z u) (volume.restrict (Ioc (0 : ℝ) N)) := by
    refine (hT.integral_prod_right).congr ?_
    filter_upwards [hT.prod_left_ae] with t ht
    exact integral_prod _ ht
  exact ((iA.sub iB).sub iC).add iD

/-- The set of times at which a particle lies, or `t` is a lift of a particle, is countable, so
almost every `t` is off the particles. -/
theorem ae_off_particles (N : ℕ+) (X : Configuration N) :
    ∀ᵐ t ∂(volume : Measure ℝ), ∀ (i : Fin (N : ℕ)) (k : ℤ), t ≠ loopArcPos N X i + k * N := by
  have hc : Set.Countable (Set.range (fun p : Fin (N : ℕ) × ℤ =>
      loopArcPos N X p.1 + (p.2 : ℝ) * N)) := Set.countable_range _
  have hz := hc.measure_zero (volume : Measure ℝ)
  have hsub : {t : ℝ | ¬ ∀ (i : Fin (N : ℕ)) (k : ℤ), t ≠ loopArcPos N X i + k * N}
      ⊆ Set.range (fun p : Fin (N : ℕ) × ℤ => loopArcPos N X p.1 + (p.2 : ℝ) * N) := by
    intro t ht
    simp only [Set.mem_ofPred_eq, not_forall, not_not] at ht
    obtain ⟨i, k, hk⟩ := ht
    exact Set.mem_range.mpr ⟨(i, k), hk.symm⟩
  filter_upwards [MeasureTheory.ae_iff.mpr (measure_mono_null hsub hz)] with t ht
  exact ht

/-- **The loop functional as an integral of `Λ`.** For every configuration, every `C¹` periodic
`b` with period `N`: `L(b) = -2 ∫₀^N b'(t) Λ(t) dt`, the identity of the arcs part of Lemma B.2.
The integral is the interval integral over `(0, N]`. -/
theorem loopArcL_eq_integral_lambda (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (N : ℕ+) (b : ℝ → ℝ)
    (hb : ContDiff ℝ 1 b) (hper : Function.Periodic b (N : ℝ)) (X : Configuration N) :
    loopArcL s N b X
      = -2 * ∫ t in (0 : ℝ)..(N : ℝ), deriv b t * loopArcLambda s N X t := by
  rw [loopArcL_eq_integral_pairing s hs0 hs1 N b hb hper X]
  congr 1
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [ae_off_particles N X] with t ht _
  rw [loopArcPairing_phi_eq_lambda s hs0 hs1 N t X ht]

/-- **Arclength integrability of `Λ`.** For every configuration, `Λ` is integrable on `(0, N]`,
since it agrees with the integrable pairing `t ↦ P_t` off the particles. -/
theorem integrable_loopArcLambda (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (N : ℕ+)
    (X : Configuration N) :
    IntegrableOn (fun t => loopArcLambda s N X t) (Ioc (0 : ℝ) N) := by
  refine (integrable_loopArcPairing_phi s hs0 hs1 N X).congr ?_
  filter_upwards [ae_restrict_of_ae (ae_off_particles N X)] with t ht
  exact loopArcPairing_phi_eq_lambda s hs0 hs1 N t X ht


end Riesz1

end
end
