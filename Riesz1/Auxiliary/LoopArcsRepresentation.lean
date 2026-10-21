/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopArcsTriangle
public import Riesz1.Auxiliary.LoopArcsParam

/-!
# The arc function as a pairing against a parameter measure

The representation step of the arcs part of Lemma 5.8. For `t` off the
particle positions, the arc-crossing pairing `P_t = loopArcPairing N X (loopArcPhi s N t)` equals
the function `Λ(t) = loopArcLambda s N X t`. This file proves that identity in three parts:

* Part A (this section): the triangle kernel `ψ(q) = -g_N'''(q₁ + q₂) 1[q₂ < N/2 - q₁]` on the
  square `(0, N/2)²`, with its pointwise bounds, measurability and integrability against
  `q₁ q₂`. These bounds are the integrability of the parametric pairing kernels.
* Part B: the parametric representation of the cutoff and the exchange of the pairing with the
  parameter integrals (`loopArcPairing_integral_param`).
* Part C: the identity `loopArcPairing N X (loopArcPhi s N t) = loopArcLambda s N X t` for `t` off
  the particles, with the conversion of the square integral to the iterated integral of
  `loopArcLambda`.

No new analytic input beyond the scaled bound `norm_iteratedDeriv_loopArcG_le` is used.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Riesz1

/-- The triangle kernel `ψ(q) = -g_N'''(q₁ + q₂)` when `q₂ < N/2 - q₁`, and `0` otherwise. It is the
density of the `(u, v)`-form of the cutoff in `loopArcQ_eq_triangle`. -/
noncomputable def loopArcTri (s : ℝ) (N : ℕ+) (q : ℝ × ℝ) : ℝ :=
  if q.2 < (N : ℝ) / 2 - q.1 then -iteratedDeriv 3 (loopArcG s N) (q.1 + q.2) else 0

/-- The triangle kernel is measurable. -/
theorem measurable_loopArcTri (s : ℝ) (N : ℕ+) : Measurable (loopArcTri s N) := by
  unfold loopArcTri
  refine Measurable.ite (measurableSet_lt measurable_snd (measurable_const.sub measurable_fst)) ?_
    measurable_const
  exact Measurable.neg ((measurable_iteratedDeriv_succ_real 2 _).comp
    (measurable_fst.add measurable_snd))

/-- The pointwise bound `|ψ(q)| ≤ C (q₁ + q₂)^{-s-3}` on the positive quadrant. -/
theorem loopArcTri_abs_le (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (q : ℝ × ℝ), 0 < q.1 → 0 < q.2 →
      |loopArcTri s N q| ≤ C * (q.1 + q.2) ^ (-s - 3) := by
  obtain ⟨C, hC, hD⟩ := norm_iteratedDeriv_loopArcG_le s hs0 hs1
  refine ⟨C, hC, fun N q h1 h2 => ?_⟩
  unfold loopArcTri
  split_ifs with h
  · have hr : 0 < q.1 + q.2 := by linarith
    have hrR : q.1 + q.2 ≤ (N : ℝ) / 2 := by linarith
    have h3 := hD N 3 (by norm_num) (by norm_num) (q.1 + q.2) hr hrR
    rw [abs_neg]
    simpa using h3
  · rw [abs_zero]
    positivity

/-- **The majorant of the triangle kernel.** With `P = q₁ q₂`, `|ψ(q)| P ≤ C P^{-(1+s)/2}` on the
positive quadrant, by the arithmetic-geometric mean inequality `q₁ + q₂ ≥ 2 √P`. -/
theorem loopArcTri_mul_le (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (q : ℝ × ℝ), 0 < q.1 → 0 < q.2 →
      |loopArcTri s N q| * (q.1 * q.2) ≤ C * (q.1 * q.2) ^ (-(1 + s) / 2) := by
  obtain ⟨C, hC, hD⟩ := loopArcTri_abs_le s hs0 hs1
  refine ⟨C * 2 ^ (-s - 3), by positivity, fun N q h1 h2 => ?_⟩
  have hP0 : 0 < q.1 * q.2 := mul_pos h1 h2
  have hsq : 2 * √(q.1 * q.2) ≤ q.1 + q.2 := by
    nlinarith [sq_nonneg (q.1 - q.2), Real.sq_sqrt hP0.le, Real.sqrt_nonneg (q.1 * q.2)]
  have hpow1 : (q.1 + q.2) ^ (-s - 3) ≤ (2 * √(q.1 * q.2)) ^ (-s - 3) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hsq (by linarith)
  have hpow2 : (2 * √(q.1 * q.2)) ^ (-s - 3)
      = 2 ^ (-s - 3) * (q.1 * q.2) ^ (-(s + 3) / 2) := by
    rw [Real.mul_rpow (by norm_num) (Real.sqrt_nonneg _), Real.sqrt_eq_rpow,
      ← Real.rpow_mul hP0.le]
    congr 2
    ring
  have hfin : (q.1 * q.2) ^ (-(s + 3) / 2) * (q.1 * q.2) = (q.1 * q.2) ^ (-(1 + s) / 2) := by
    rw [show -(1 + s) / 2 = -(s + 3) / 2 + 1 by ring, Real.rpow_add hP0, Real.rpow_one]
  calc |loopArcTri s N q| * (q.1 * q.2)
      ≤ (C * (q.1 + q.2) ^ (-s - 3)) * (q.1 * q.2) :=
        mul_le_mul_of_nonneg_right (hD N q h1 h2) hP0.le
    _ ≤ (C * (2 ^ (-s - 3) * (q.1 * q.2) ^ (-(s + 3) / 2))) * (q.1 * q.2) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hpow1.trans_eq hpow2) hC.le)
          hP0.le
    _ = C * 2 ^ (-s - 3) * (q.1 * q.2) ^ (-(1 + s) / 2) := by rw [← hfin]; ring

/-- **Integrability of the triangle majorant on the square.** The function `|ψ(q)| q₁ q₂` is
integrable against the square measure `(Lebesgue on (0, N/2))²`. -/
theorem integrable_loopArcTri_mul (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (N : ℕ+) :
    Integrable (fun q : ℝ × ℝ => |loopArcTri s N q| * (q.1 * q.2))
      ((volume.restrict (Ioo (0 : ℝ) ((N : ℝ) / 2))).prod
        (volume.restrict (Ioo (0 : ℝ) ((N : ℝ) / 2)))) := by
  obtain ⟨C, hC, hM⟩ := loopArcTri_mul_le s hs0 hs1
  have hR : (0 : ℝ) < (N : ℝ) / 2 := by have := N.pos; positivity
  have h1d : IntegrableOn (fun x : ℝ => x ^ (-(1 + s) / 2)) (Ioo (0 : ℝ) ((N : ℝ) / 2)) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff hR).mpr (by linarith)
  have hmaj : Integrable (fun q : ℝ × ℝ => C * (q.1 ^ (-(1 + s) / 2) * q.2 ^ (-(1 + s) / 2)))
      ((volume.restrict (Ioo (0 : ℝ) ((N : ℝ) / 2))).prod
        (volume.restrict (Ioo (0 : ℝ) ((N : ℝ) / 2)))) :=
    (h1d.mul_prod h1d).const_mul C
  refine Integrable.mono' hmaj ?_ ?_
  · exact ((continuous_abs.measurable.comp (measurable_loopArcTri s N)).mul
      (measurable_fst.mul measurable_snd)).aestronglyMeasurable
  · rw [Measure.prod_restrict, ae_restrict_iff' (measurableSet_Ioo.prod measurableSet_Ioo)]
    refine ae_of_all _ fun q hq => ?_
    have hq1 : 0 < q.1 := hq.1.1
    have hq2 : 0 < q.2 := hq.2.1
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hb := hM N q hq1 hq2
    rw [Real.mul_rpow hq1.le hq2.le] at hb
    exact hb

/-- The square parameter measure `(Lebesgue on (0, N/2))²` of the triangle kernel. -/
noncomputable def loopArcSq (N : ℕ+) : Measure (ℝ × ℝ) :=
  (volume.restrict (Ioo (0 : ℝ) ((N : ℝ) / 2))).prod (volume.restrict (Ioo (0 : ℝ) ((N : ℝ) / 2)))

instance loopArcSq_isFiniteMeasure (N : ℕ+) : IsFiniteMeasure (loopArcSq N) :=
  inferInstanceAs (IsFiniteMeasure ((volume.restrict (Ioo (0 : ℝ) ((N : ℝ) / 2))).prod
    (volume.restrict (Ioo (0 : ℝ) ((N : ℝ) / 2)))))

/-- The parametric pairing kernel `K(q; z, u) = ψ(q) 1[a(z) < q₁] 1[b(u) < q₂]`, where
`a(z) = fwd(t - z)` and `b(u) = fwd(u - t)` are the forward distances to the arc `t`. -/
noncomputable def loopArcTriKernel (s : ℝ) (N : ℕ+) (t : ℝ) (q : ℝ × ℝ) (z u : ℝ) : ℝ :=
  loopArcTri s N q * ((if loopArcFwd N (t - z) < q.1 then (1 : ℝ) else 0)
    * (if loopArcFwd N (u - t) < q.2 then (1 : ℝ) else 0))

/-- The atom kernel `1[a(z) < w] 1[b(u) < N/2 - w]` on `(0, N/2)`. -/
noncomputable def loopArcAtomKernel (N : ℕ+) (t : ℝ) (w z u : ℝ) : ℝ :=
  (if loopArcFwd N (t - z) < w then (1 : ℝ) else 0)
    * (if loopArcFwd N (u - t) < (N : ℝ) / 2 - w then (1 : ℝ) else 0)

/-- Almost every point of the square `loopArcSq N` lies in the open square `(0, N/2)²`. -/
theorem ae_loopArcSq (N : ℕ+) :
    ∀ᵐ q ∂loopArcSq N, 0 < q.1 ∧ q.1 < (N : ℝ) / 2 ∧ 0 < q.2 ∧ q.2 < (N : ℝ) / 2 := by
  unfold loopArcSq
  rw [Measure.prod_restrict]
  filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)] with q hq
  exact ⟨hq.1.1, hq.1.2, hq.2.1, hq.2.2⟩

/-- A bound holding for almost every point of a product measure in its first factor. -/
theorem ae_prod_fst_of_ae {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SigmaFinite ν] {P : α → Prop}
    (hP : ∀ᵐ x ∂μ, P x) (hPm : MeasurableSet {x | P x}) :
    ∀ᵐ p ∂(μ.prod ν), P p.1 := by
  have hm : MeasurableSet {p : α × β | P p.1} := hPm.preimage measurable_fst
  refine (Measure.ae_prod_iff_ae_ae hm).mpr ?_
  filter_upwards [hP] with x hx
  exact ae_of_all _ fun _ => hx

/-- A bound holding for almost every first coordinate, uniformly in the second, lifts to the
product measure. -/
theorem ae_prod_of_ae_forall {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SigmaFinite ν] {P : α → β → Prop}
    (hP : ∀ᵐ x ∂μ, ∀ y, P x y) (hPm : MeasurableSet {p : α × β | P p.1 p.2}) :
    ∀ᵐ p ∂(μ.prod ν), P p.1 p.2 :=
  (Measure.ae_prod_iff_ae_ae hPm).mpr (hP.mono fun _ hx => ae_of_all _ hx)

/-- Integrability of a measurable function that is almost everywhere bounded on a finite measure. -/
theorem integrable_of_ae_abs_le {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {f : α → ℝ} (hf : Measurable f) {M : ℝ} (hM : ∀ᵐ x ∂μ, |f x| ≤ M) : Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable M (hM.mono fun x hx => by rwa [Real.norm_eq_abs])

/-- Measurability of the parametric kernel in `(q, z, u)`. -/
theorem measurable_loopArcTriKernel (s : ℝ) (N : ℕ+) (t : ℝ) :
    Measurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => loopArcTriKernel s N t p.1 p.2.1 p.2.2) := by
  have hz : Measurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => loopArcFwd N (t - p.2.1)) :=
    (measurable_loopArcFwd_of N).comp (measurable_const.sub (measurable_fst.comp measurable_snd))
  have hu : Measurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => loopArcFwd N (p.2.2 - t)) :=
    (measurable_loopArcFwd_of N).comp (measurable_snd.comp measurable_snd |>.sub measurable_const)
  unfold loopArcTriKernel
  refine Measurable.mul ((measurable_loopArcTri s N).comp measurable_fst) (Measurable.mul ?_ ?_)
  · exact Measurable.ite (measurableSet_lt hz (measurable_fst.comp measurable_fst))
      measurable_const measurable_const
  · exact Measurable.ite (measurableSet_lt hu (measurable_snd.comp measurable_fst))
      measurable_const measurable_const

/-- The left bound `|ψ(q)| 1[a < q₁] ≤ C a^{-s-3}` on the positive quadrant, for `a > 0`. -/
theorem loopArcTri_left_le (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (a : ℝ) (q : ℝ × ℝ), 0 < a → 0 < q.1 → 0 < q.2 →
      |loopArcTri s N q| * (if a < q.1 then (1 : ℝ) else 0) ≤ C * a ^ (-s - 3) := by
  obtain ⟨C, hC, hD⟩ := loopArcTri_abs_le s hs0 hs1
  refine ⟨C, hC, fun N a q ha h1 h2 => ?_⟩
  split_ifs with h
  · rw [mul_one]
    have hpow : (q.1 + q.2) ^ (-s - 3) ≤ a ^ (-s - 3) :=
      Real.rpow_le_rpow_of_nonpos ha (by linarith) (by linarith)
    calc |loopArcTri s N q| ≤ C * (q.1 + q.2) ^ (-s - 3) := hD N q h1 h2
      _ ≤ C * a ^ (-s - 3) := mul_le_mul_of_nonneg_left hpow hC.le
  · rw [mul_zero]
    positivity

/-- The right bound `|ψ(q)| 1[b < q₂] ≤ C b^{-s-3}` on the positive quadrant, for `b > 0`. -/
theorem loopArcTri_right_le (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (b : ℝ) (q : ℝ × ℝ), 0 < b → 0 < q.1 → 0 < q.2 →
      |loopArcTri s N q| * (if b < q.2 then (1 : ℝ) else 0) ≤ C * b ^ (-s - 3) := by
  obtain ⟨C, hC, hD⟩ := loopArcTri_abs_le s hs0 hs1
  refine ⟨C, hC, fun N b q hb h1 h2 => ?_⟩
  split_ifs with h
  · rw [mul_one]
    have hpow : (q.1 + q.2) ^ (-s - 3) ≤ b ^ (-s - 3) :=
      Real.rpow_le_rpow_of_nonpos hb (by linarith) (by linarith)
    calc |loopArcTri s N q| ≤ C * (q.1 + q.2) ^ (-s - 3) := hD N q h1 h2
      _ ≤ C * b ^ (-s - 3) := mul_le_mul_of_nonneg_left hpow hC.le
  · rw [mul_zero]
    positivity

/-- The parametric kernel is bounded by the triangle kernel times the left indicator. -/
theorem abs_triKernel_le_left (s : ℝ) (N : ℕ+) (t : ℝ) (q : ℝ × ℝ) (z u : ℝ) :
    |loopArcTriKernel s N t q z u|
      ≤ |loopArcTri s N q| * (if loopArcFwd N (t - z) < q.1 then (1 : ℝ) else 0) := by
  unfold loopArcTriKernel
  rw [abs_mul, abs_mul]
  have key : |(if loopArcFwd N (t - z) < q.1 then (1 : ℝ) else 0)|
      * |(if loopArcFwd N (u - t) < q.2 then (1 : ℝ) else 0)|
      ≤ (if loopArcFwd N (t - z) < q.1 then (1 : ℝ) else 0) := by
    split_ifs <;> norm_num
  exact mul_le_mul_of_nonneg_left key (abs_nonneg _)

/-- The parametric kernel is bounded by the triangle kernel times the right indicator. -/
theorem abs_triKernel_le_right (s : ℝ) (N : ℕ+) (t : ℝ) (q : ℝ × ℝ) (z u : ℝ) :
    |loopArcTriKernel s N t q z u|
      ≤ |loopArcTri s N q| * (if loopArcFwd N (u - t) < q.2 then (1 : ℝ) else 0) := by
  unfold loopArcTriKernel
  rw [abs_mul, abs_mul]
  have key : |(if loopArcFwd N (t - z) < q.1 then (1 : ℝ) else 0)|
      * |(if loopArcFwd N (u - t) < q.2 then (1 : ℝ) else 0)|
      ≤ (if loopArcFwd N (u - t) < q.2 then (1 : ℝ) else 0) := by
    split_ifs <;> norm_num
  exact mul_le_mul_of_nonneg_left key (abs_nonneg _)

/-- The parametric kernel is bounded by `|ψ(q)|` (both indicators at most one). -/
theorem abs_triKernel_le (s : ℝ) (N : ℕ+) (t : ℝ) (q : ℝ × ℝ) (z u : ℝ) :
    |loopArcTriKernel s N t q z u| ≤ |loopArcTri s N q| := by
  unfold loopArcTriKernel
  rw [abs_mul, abs_mul]
  have key : |(if loopArcFwd N (t - z) < q.1 then (1 : ℝ) else 0)|
      * |(if loopArcFwd N (u - t) < q.2 then (1 : ℝ) else 0)| ≤ 1 := by
    split_ifs <;> norm_num
  calc |loopArcTri s N q| * (|(if loopArcFwd N (t - z) < q.1 then (1 : ℝ) else 0)|
          * |(if loopArcFwd N (u - t) < q.2 then (1 : ℝ) else 0)|)
      ≤ |loopArcTri s N q| * 1 := mul_le_mul_of_nonneg_left key (abs_nonneg _)
    _ = |loopArcTri s N q| := mul_one _

/-- **Atomic integrability, left.** For a particle `z` with `a(z) = fwd(t - z) > 0`, the kernel
`q ↦ K(q; z, u)` is integrable on the square, for every `u`. -/
theorem integrable_triKernel_left (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (N : ℕ+) (t z u : ℝ)
    (hz : 0 < loopArcFwd N (t - z)) :
    Integrable (fun q : ℝ × ℝ => loopArcTriKernel s N t q z u) (loopArcSq N) := by
  obtain ⟨C, hC, hD⟩ := loopArcTri_left_le s hs0 hs1
  have hmeas : Measurable (fun q : ℝ × ℝ => loopArcTriKernel s N t q z u) := by
    unfold loopArcTriKernel
    refine Measurable.mul (measurable_loopArcTri s N) (Measurable.mul ?_ ?_)
    · exact Measurable.ite (measurableSet_lt measurable_const measurable_fst) measurable_const
        measurable_const
    · exact Measurable.ite (measurableSet_lt measurable_const measurable_snd) measurable_const
        measurable_const
  refine integrable_of_ae_abs_le (M := C * loopArcFwd N (t - z) ^ (-s - 3)) hmeas ?_
  filter_upwards [ae_loopArcSq N] with q hq
  exact (abs_triKernel_le_left s N t q z u).trans (hD N _ q hz hq.1 hq.2.2.1)

instance loopArcBg_isFiniteMeasure (N : ℕ+) : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) N)) :=
  ⟨by rw [Measure.restrict_apply_univ, Real.volume_Ioc]; exact ENNReal.ofReal_lt_top⟩

/-- **Mixed integrability, left.** For `a(z) > 0`, the kernel is integrable in `(q, u)` against
the square and the background `ν`. -/
theorem integrable_triKernel_prod_left (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (N : ℕ+) (t z : ℝ)
    (hz : 0 < loopArcFwd N (t - z)) :
    Integrable (fun p : (ℝ × ℝ) × ℝ => loopArcTriKernel s N t p.1 z p.2)
      ((loopArcSq N).prod (volume.restrict (Ioc (0 : ℝ) N))) := by
  obtain ⟨C, hC, hD⟩ := loopArcTri_left_le s hs0 hs1
  have hmeas : Measurable (fun p : (ℝ × ℝ) × ℝ => loopArcTriKernel s N t p.1 z p.2) := by
    unfold loopArcTriKernel
    refine Measurable.mul ((measurable_loopArcTri s N).comp measurable_fst)
      (Measurable.mul ?_ ?_)
    · exact Measurable.ite (measurableSet_lt measurable_const (measurable_fst.comp measurable_fst))
        measurable_const measurable_const
    · exact Measurable.ite (measurableSet_lt ((measurable_loopArcFwd_of N).comp
        (measurable_snd.sub measurable_const)) (measurable_snd.comp measurable_fst))
        measurable_const measurable_const
  refine integrable_of_ae_abs_le (M := C * loopArcFwd N (t - z) ^ (-s - 3)) hmeas ?_
  refine ae_prod_of_ae_forall (P := fun q u => |loopArcTriKernel s N t q z u|
      ≤ C * loopArcFwd N (t - z) ^ (-s - 3)) ?_ ?_
  · filter_upwards [ae_loopArcSq N] with q hq
    intro u
    exact (abs_triKernel_le_left s N t q z u).trans (hD N _ q hz hq.1 hq.2.2.1)
  · exact measurableSet_le (continuous_abs.measurable.comp hmeas) measurable_const

/-- **Mixed integrability, right.** For `b(u) > 0`, the kernel is integrable in `(q, z)`. -/
theorem integrable_triKernel_prod_right (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (N : ℕ+) (t u : ℝ)
    (hu : 0 < loopArcFwd N (u - t)) :
    Integrable (fun p : (ℝ × ℝ) × ℝ => loopArcTriKernel s N t p.1 p.2 u)
      ((loopArcSq N).prod (volume.restrict (Ioc (0 : ℝ) N))) := by
  obtain ⟨C, hC, hD⟩ := loopArcTri_right_le s hs0 hs1
  have hfa : Measurable (fun p : (ℝ × ℝ) × ℝ => loopArcFwd N (t - p.2)) :=
    (measurable_loopArcFwd_of N).comp (measurable_const.sub measurable_snd)
  have hmeas : Measurable (fun p : (ℝ × ℝ) × ℝ => loopArcTriKernel s N t p.1 p.2 u) := by
    unfold loopArcTriKernel
    refine Measurable.mul ((measurable_loopArcTri s N).comp measurable_fst)
      (Measurable.mul ?_ ?_)
    · exact Measurable.ite (measurableSet_lt hfa (measurable_fst.comp measurable_fst))
        measurable_const measurable_const
    · exact Measurable.ite (measurableSet_lt measurable_const (measurable_snd.comp measurable_fst))
        measurable_const measurable_const
  refine integrable_of_ae_abs_le (M := C * loopArcFwd N (u - t) ^ (-s - 3)) hmeas ?_
  refine ae_prod_of_ae_forall (P := fun q z => |loopArcTriKernel s N t q z u|
      ≤ C * loopArcFwd N (u - t) ^ (-s - 3)) ?_ ?_
  · filter_upwards [ae_loopArcSq N] with q hq
    intro z
    exact (abs_triKernel_le_right s N t q z u).trans (hD N _ q hu hq.1 hq.2.2.1)
  · exact measurableSet_le (continuous_abs.measurable.comp hmeas) measurable_const

/-- The background integral of the left indicator `1[fwd(t - z) < c]` is `c`, for `0 ≤ c ≤ N`. -/
theorem integral_fwd_indicator_left (N : ℕ+) (t c : ℝ) (hc0 : 0 ≤ c) (hcN : c ≤ (N : ℝ)) :
    ∫ z, (if loopArcFwd N (t - z) < c then (1 : ℝ) else 0)
      ∂(volume.restrict (Ioc (0 : ℝ) N)) = c := by
  rw [← intervalIntegral.integral_of_le (by positivity)]
  have h := integral_fwd_sub N (fun δ => if δ < c then (1 : ℝ) else 0) t
  rw [h, integral_ite_lt_eq c N hc0 hcN]

/-- The background integral of the right indicator `1[fwd(u - t) < c]` is `c`, for `0 ≤ c ≤ N`. -/
theorem integral_fwd_indicator_right (N : ℕ+) (t c : ℝ) (hc0 : 0 ≤ c) (hcN : c ≤ (N : ℝ)) :
    ∫ u, (if loopArcFwd N (u - t) < c then (1 : ℝ) else 0)
      ∂(volume.restrict (Ioc (0 : ℝ) N)) = c := by
  rw [← intervalIntegral.integral_of_le (by positivity)]
  have h := integral_fwd_comp N (fun δ => if δ < c then (1 : ℝ) else 0) t
  rw [h, integral_ite_lt_eq c N hc0 hcN]

/-- **Integrability of the full parametric kernel.** The map `(q, (z, u)) ↦ K(q; z, u)` is
integrable against the square and the background square, by the decomposition
`integrable_prod_iff`: each slice is bounded by `|ψ(q)|`, and the background integral of the
absolute value is `|ψ(q)| q₁ q₂`. -/
theorem integrable_triKernel_prod_bg (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (N : ℕ+) (t : ℝ) :
    Integrable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => loopArcTriKernel s N t p.1 p.2.1 p.2.2)
      ((loopArcSq N).prod
        ((volume.restrict (Ioc (0 : ℝ) N)).prod (volume.restrict (Ioc (0 : ℝ) N)))) := by
  have hmeas : Measurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => loopArcTriKernel s N t p.1 p.2.1 p.2.2) :=
    measurable_loopArcTriKernel s N t
  rw [integrable_prod_iff hmeas.aestronglyMeasurable]
  refine ⟨ae_of_all _ fun q => ?_, ?_⟩
  · have hfa : Measurable (fun zu : ℝ × ℝ => loopArcFwd N (t - zu.1)) :=
      (measurable_loopArcFwd_of N).comp (measurable_const.sub measurable_fst)
    have hfb : Measurable (fun zu : ℝ × ℝ => loopArcFwd N (zu.2 - t)) :=
      (measurable_loopArcFwd_of N).comp (measurable_snd.sub measurable_const)
    have hm : Measurable (fun zu : ℝ × ℝ => loopArcTriKernel s N t q zu.1 zu.2) := by
      unfold loopArcTriKernel
      refine Measurable.mul measurable_const (Measurable.mul ?_ ?_)
      · exact Measurable.ite (measurableSet_lt hfa measurable_const) measurable_const
          measurable_const
      · exact Measurable.ite (measurableSet_lt hfb measurable_const) measurable_const
          measurable_const
    exact integrable_of_ae_abs_le (M := |loopArcTri s N q|) hm
      (ae_of_all _ fun zu => abs_triKernel_le s N t q zu.1 zu.2)
  · refine Integrable.congr (integrable_loopArcTri_mul s hs0 hs1 N) ?_
    filter_upwards [ae_loopArcSq N] with q hq
    have hpt : ∀ zu : ℝ × ℝ, ‖loopArcTriKernel s N t q zu.1 zu.2‖
        = |loopArcTri s N q| * ((if loopArcFwd N (t - zu.1) < q.1 then (1 : ℝ) else 0)
          * (if loopArcFwd N (zu.2 - t) < q.2 then (1 : ℝ) else 0)) := by
      intro zu
      unfold loopArcTriKernel
      have hnn : 0 ≤ (if loopArcFwd N (t - zu.1) < q.1 then (1 : ℝ) else 0)
          * (if loopArcFwd N (zu.2 - t) < q.2 then (1 : ℝ) else 0) := by
        split_ifs <;> norm_num
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hnn]
    simp only [hpt]
    rw [integral_const_mul,
      integral_prod_mul (fun z : ℝ => if loopArcFwd N (t - z) < q.1 then (1 : ℝ) else 0)
        (fun u : ℝ => if loopArcFwd N (u - t) < q.2 then (1 : ℝ) else 0),
      integral_fwd_indicator_left N t q.1 hq.1.le (by
        have : (0 : ℝ) ≤ (N : ℝ) := by positivity
        linarith [hq.2.1]),
      integral_fwd_indicator_right N t q.2 hq.2.2.1.le (by
        have : (0 : ℝ) ≤ (N : ℝ) := by positivity
        linarith [hq.2.2.2])]

end Riesz1

end
end
