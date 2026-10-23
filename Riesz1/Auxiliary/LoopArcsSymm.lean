/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopArcsPair
public import Riesz1.Auxiliary.LoopArcsBounds

/-!
# Symmetry of the pairing and integrability of the arc kernel

Preparation for the arcs part of Lemma B.2. This file proves
the facts that let the arc kernel `Φ_t` be integrated against `ν ⊗ ν`:

* `loopArcPairing_swap`: the pairing is invariant under exchanging the two arguments of the kernel.
* `integral_fwd_comp`: the integral of `f(fwd(u - z))` over one period does not depend on `z`.
* `integral_norm_loopArcPhi`: `∫₀^N |Φ_t(z, u)| dt = |Q(δ)| δ` with `δ = fwd(u - z)`.
* `intervalIntegrable_loopArcQ_mul`: `δ ↦ |Q(δ)| δ` is interval integrable on `[0, N]`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Finset Set
open scoped ContDiff

namespace Riesz1

/-- Exchanging the two arguments of a pair kernel does not change its pairing against `ν ⊗ ν`, as
long as the kernel is integrable on the background square `(0, N]²`. The empirical sum is
symmetric, and the two particle-background blocks exchange with each other. -/
theorem loopArcPairing_swap (N : ℕ+) (X : Configuration N) (G : ℝ → ℝ → ℝ)
    (hG : Integrable (fun p : ℝ × ℝ => G p.1 p.2)
      ((volume.restrict (Ioc (0 : ℝ) N)).prod (volume.restrict (Ioc (0 : ℝ) N)))) :
    loopArcPairing N X (fun z u => G u z) = loopArcPairing N X G := by
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have hswap : Integrable (fun p : ℝ × ℝ => G p.2 p.1)
      ((volume.restrict (Ioc (0 : ℝ) N)).prod (volume.restrict (Ioc (0 : ℝ) N))) := hG.swap
  have hBB : ∫ z in (0 : ℝ)..(N : ℝ), ∫ u in (0 : ℝ)..(N : ℝ), G u z
      = ∫ z in (0 : ℝ)..(N : ℝ), ∫ u in (0 : ℝ)..(N : ℝ), G z u := by
    simp only [intervalIntegral.integral_of_le hN0]
    exact integral_integral_swap (f := fun z u => G u z) hswap
  have hEmp : ∑ i : Fin (N : ℕ), ∑ j : Fin (N : ℕ), G (loopArcPos N X j) (loopArcPos N X i)
      = ∑ i : Fin (N : ℕ), ∑ j : Fin (N : ℕ), G (loopArcPos N X i) (loopArcPos N X j) :=
    Finset.sum_comm
  simp only [loopArcPairing]
  rw [hEmp, hBB]
  ring

/-- The integral of `f` composed with the forward distance `fwd(u - z)` over one period equals
the integral of `f` over `[0, N]`, for every shift `z`. -/
theorem integral_fwd_comp (N : ℕ+) (f : ℝ → ℝ) (z : ℝ) :
    ∫ u in (0 : ℝ)..(N : ℝ), f (loopArcFwd N (u - z)) = ∫ δ in (0 : ℝ)..(N : ℝ), f δ := by
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have hper : Function.Periodic (fun v => f (loopArcFwd N v)) (N : ℝ) := by
    intro v
    simp only
    rw [show v + (N : ℝ) = v + ((1 : ℤ) : ℝ) * N by push_cast; ring, loopArcFwd_add_int_mul]
  have h1 : ∫ u in (0 : ℝ)..(N : ℝ), f (loopArcFwd N (u - z))
      = ∫ v in (0 : ℝ)..(N : ℝ), f (loopArcFwd N v) := by
    rw [intervalIntegral.integral_comp_sub_right (fun v => f (loopArcFwd N v)) z]
    have h := hper.intervalIntegral_add_eq (-z) 0
    simp only [zero_add] at h
    rw [zero_sub, show (N : ℝ) - z = -z + N by ring]
    exact h
  rw [h1]
  refine intervalIntegral.integral_congr_ae ?_
  have hN_ae : ∀ᵐ v ∂(volume : Measure ℝ), v ≠ (N : ℝ) := by
    rw [ae_iff]
    simp
  filter_upwards [hN_ae] with v hv hvI
  rw [uIoc_of_le hN0] at hvI
  rw [loopArcFwd_of_mem hvI.1.le (lt_of_le_of_ne hvI.2 hv)]

/-- Composing an interval integrable function with the forward distance gives an interval
integrable function on one period. -/
theorem intervalIntegrable_comp_fwd (N : ℕ+) {g : ℝ → ℝ} (hg : IntervalIntegrable g volume 0 N) :
    IntervalIntegrable (fun v => g (loopArcFwd N v)) volume 0 N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast N.pos
  refine hg.congr_uIoo ?_
  intro v hv
  rw [uIoo_of_le hN0.le] at hv
  dsimp only
  rw [loopArcFwd_of_mem hv.1.le hv.2]

/-- The shifted forward distance of an interval integrable function is interval integrable over
one period. -/
theorem intervalIntegrable_fwd_comp (N : ℕ+) {g : ℝ → ℝ} (hg : IntervalIntegrable g volume 0 N)
    (z : ℝ) : IntervalIntegrable (fun u => g (loopArcFwd N (u - z))) volume 0 N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hz : IntervalIntegrable (fun u => g (loopArcFwd N (u - z))) volume z (z + N) := by
    have h := (intervalIntegrable_comp_fwd N hg).comp_add_right (-z)
    simp only [sub_neg_eq_add, ← sub_eq_add_neg, zero_add] at h
    rw [add_comm (N : ℝ) z] at h
    exact h
  have hper : Function.Periodic (fun u => g (loopArcFwd N (u - z))) (N : ℝ) := by
    intro u
    simp only
    rw [show u + (N : ℝ) - z = (u - z) + ((1 : ℤ) : ℝ) * N by push_cast; ring,
      loopArcFwd_add_int_mul]
  exact hper.intervalIntegrable (by exact_mod_cast N.ne_zero) hz 0 N

/-- The reflected version: `z ↦ g(fwd(u - z))` is interval integrable over one period. -/
theorem intervalIntegrable_fwd_sub (N : ℕ+) {g : ℝ → ℝ} (hg : IntervalIntegrable g volume 0 N)
    (u : ℝ) : IntervalIntegrable (fun z => g (loopArcFwd N (u - z))) volume 0 N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast N.pos
  have h := (intervalIntegrable_comp_fwd N hg).comp_sub_left u
  have hper : Function.Periodic (fun z => g (loopArcFwd N (u - z))) (N : ℝ) := by
    intro z
    simp only
    rw [show u - (z + N) = (u - z) + ((-1 : ℤ) : ℝ) * N by push_cast; ring,
      loopArcFwd_add_int_mul]
  have h2 : IntervalIntegrable (fun z => g (loopArcFwd N (u - z))) volume (u - N) (u - N + N) := by
    rw [sub_add_cancel]
    simpa only [sub_zero] using h.symm
  exact hper.intervalIntegrable (by exact_mod_cast N.ne_zero) h2 0 N

/-- The indicator of `[0, δ]` on `(0, N]` integrates to `c δ`, for `0 ≤ δ ≤ N`. -/
theorem integral_ite_le_eq (c δ : ℝ) (N : ℕ+) (hδ0 : 0 ≤ δ) (hδN : δ ≤ N) :
    ∫ v in (0 : ℝ)..(N : ℝ), (if v ≤ δ then c else 0) = c * δ := by
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have hfun : (fun v : ℝ => if v ≤ δ then c else 0) = (Iic δ).indicator (fun _ => c) := by
    funext v
    simp [Set.indicator]
  rw [intervalIntegral.integral_of_le hN0, hfun, setIntegral_indicator measurableSet_Iic,
    setIntegral_const]
  have hset : Ioc (0 : ℝ) N ∩ Iic δ = Ioc 0 δ := by
    ext v
    simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Iic]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩
      exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩
      exact ⟨⟨h1, h3.trans hδN⟩, h3⟩
  rw [hset, Real.volume_real_Ioc_of_le hδ0]
  simp [smul_eq_mul, mul_comm]

/-- The integral of `‖Φ_t(z, u)‖` over one period in `t` is `|Q(δ)| δ`, where `δ = fwd(u - z)`:
the arc kernel is `Q(δ)` on the set of `t` with `fwd(t - z) ≤ δ`, a set of length `δ`. -/
theorem integral_norm_loopArcPhi (s : ℝ) (N : ℕ+) (z u : ℝ) :
    ∫ t in (0 : ℝ)..(N : ℝ), ‖loopArcPhi s N t z u‖
      = |loopArcQ s N (loopArcFwd N (u - z))| * loopArcFwd N (u - z) := by
  have hδ0 : 0 ≤ loopArcFwd N (u - z) := loopArcFwd_nonneg N _
  have hδN : loopArcFwd N (u - z) ≤ N := (loopArcFwd_lt N _).le
  have hfun : (fun t => ‖loopArcPhi s N t z u‖)
      = fun t => if loopArcFwd N (t - z) ≤ loopArcFwd N (u - z)
          then |loopArcQ s N (loopArcFwd N (u - z))| else 0 := by
    funext t
    simp only [loopArcPhi_eq_ite]
    split_ifs <;> simp
  rw [hfun, integral_fwd_comp N (fun v => if v ≤ loopArcFwd N (u - z)
    then |loopArcQ s N (loopArcFwd N (u - z))| else 0) z, integral_ite_le_eq _ _ N hδ0 hδN]

/-- A bound for the cutoff: `|Q(δ)| δ ≤ C δ^{-s}` for every `δ > 0`, with `C` depending on `s`
and `N`. -/
theorem norm_loopArcQ_mul_le (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (N : ℕ+) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → |loopArcQ s N δ| * δ ≤ C * δ ^ (-s) := by
  obtain ⟨C, hC, h⟩ := norm_deriv_loopArcG_le s hs0 hs1 N
  refine ⟨C, hC, fun δ hδ => ?_⟩
  by_cases hlt : δ < (N : ℝ) / 2
  · have hQ : |loopArcQ s N δ| = |deriv (loopArcG s N) δ| := by
      simp only [loopArcQ, hlt, ↓reduceIte, abs_neg]
    rw [hQ]
    have hb := h δ hδ hlt.le
    have hpow : δ ^ (-s - 1) * δ = δ ^ (-s) := by
      rw [Real.rpow_sub_one hδ.ne']
      field_simp
    calc |deriv (loopArcG s N) δ| * δ ≤ C * δ ^ (-s - 1) * δ :=
          mul_le_mul_of_nonneg_right hb hδ.le
      _ = C * δ ^ (-s) := by rw [mul_assoc, hpow]
  · have hQ : loopArcQ s N δ = 0 := loopArcQ_eq_zero_of_le s N (not_lt.mp hlt)
    rw [hQ, abs_zero, zero_mul]
    exact mul_nonneg hC.le (Real.rpow_nonneg hδ.le _)

/-- The measurability of the cutoff `Q`. -/
theorem measurable_loopArcQ (s : ℝ) (N : ℕ+) : Measurable (loopArcQ s N) := by
  unfold loopArcQ
  exact Measurable.ite measurableSet_Iio (measurable_deriv _).neg measurable_const

/-- The function `δ ↦ |Q(δ)| δ` is interval integrable on `[0, N]`. -/
theorem intervalIntegrable_loopArcQ_mul (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (N : ℕ+) :
    IntervalIntegrable (fun δ => |loopArcQ s N δ| * δ) volume 0 N := by
  obtain ⟨C, hC, h⟩ := norm_loopArcQ_mul_le s hs0 hs1 N
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have hint : IntervalIntegrable (fun δ : ℝ => C * δ ^ (-s)) volume 0 N :=
    (intervalIntegral.intervalIntegrable_rpow' (by linarith)).const_mul C
  refine hint.mono_fun' ?_ ?_
  · exact ((continuous_abs.measurable.comp (measurable_loopArcQ s N)).mul
      measurable_id).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_uIoc] with δ hδ
    rw [uIoc_of_le hN0] at hδ
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) hδ.1.le)]
    exact h δ hδ.1

/-- A continuous periodic function is bounded on the whole line. -/
theorem loopArc_bound_of_periodic (N : ℕ+) {f : ℝ → ℝ} (hf : Continuous f)
    (hper : Function.Periodic f (N : ℝ)) : ∃ M : ℝ, ∀ t : ℝ, ‖f t‖ ≤ M := by
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := N)).exists_bound_of_continuousOn
    hf.continuousOn
  refine ⟨M, fun t => ?_⟩
  obtain ⟨y, hy, hfy⟩ := hper.exists_mem_Ico₀ hN t
  rw [hfy]
  exact hM y ⟨hy.1, hy.2.le⟩

/-- The forward distance is a measurable function of the point. -/
theorem measurable_loopArcFwd_of (N : ℕ+) : Measurable (loopArcFwd N) := by
  unfold loopArcFwd
  exact (measurable_fract.comp (measurable_id.div_const _)).const_mul _

/-- The arc kernel is jointly measurable in its three arguments. -/
theorem measurable_loopArcPhi_of (s : ℝ) (N : ℕ+) {α : Type*} [MeasurableSpace α]
    {T Z U : α → ℝ} (hT : Measurable T) (hZ : Measurable Z) (hU : Measurable U) :
    Measurable (fun a => loopArcPhi s N (T a) (Z a) (U a)) := by
  have hF1 : Measurable (fun a => loopArcFwd N (T a - Z a)) :=
    (measurable_loopArcFwd_of N).comp (hT.sub hZ)
  have hF2 : Measurable (fun a => loopArcFwd N (U a - Z a)) :=
    (measurable_loopArcFwd_of N).comp (hU.sub hZ)
  simp only [loopArcPhi_eq_ite]
  exact Measurable.ite (measurableSet_le hF1 hF2) ((measurable_loopArcQ s N).comp hF2)
    measurable_const

/-- The function `δ ↦ |Q(δ)| δ` is measurable. -/
theorem measurable_loopArcQ_mul (s : ℝ) (N : ℕ+) :
    Measurable (fun δ : ℝ => |loopArcQ s N δ| * δ) :=
  (continuous_abs.measurable.comp (measurable_loopArcQ s N)).mul measurable_id

/-- For fixed `z`, the arc kernel is integrable on the background square in `(t, u)`. -/
theorem integrable_loopArcPhi_fixed_left (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (N : ℕ+) (z : ℝ) :
    Integrable (fun p : ℝ × ℝ => loopArcPhi s N p.1 z p.2)
      ((volume.restrict (Ioc (0 : ℝ) N)).prod (volume.restrict (Ioc (0 : ℝ) N))) := by
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have hmeas : Measurable (fun p : ℝ × ℝ => loopArcPhi s N p.1 z p.2) :=
    measurable_loopArcPhi_of s N measurable_fst measurable_const measurable_snd
  rw [integrable_prod_iff' hmeas.aestronglyMeasurable]
  refine ⟨Filter.Eventually.of_forall fun u => (intervalIntegrable_loopArcPhi s N z u 0 N).1, ?_⟩
  have h : (fun u : ℝ => ∫ t, ‖loopArcPhi s N t z u‖ ∂(volume.restrict (Ioc (0 : ℝ) N)))
      = fun u => (fun δ => |loopArcQ s N δ| * δ) (loopArcFwd N (u - z)) := by
    funext u
    rw [← intervalIntegral.integral_of_le hN0, integral_norm_loopArcPhi]
  rw [h]
  exact (intervalIntegrable_fwd_comp N (intervalIntegrable_loopArcQ_mul s hs0 hs1 N) z).1

/-- For fixed `u`, the arc kernel is integrable on the background square in `(t, z)`. -/
theorem integrable_loopArcPhi_fixed_right (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (N : ℕ+) (u : ℝ) :
    Integrable (fun p : ℝ × ℝ => loopArcPhi s N p.1 p.2 u)
      ((volume.restrict (Ioc (0 : ℝ) N)).prod (volume.restrict (Ioc (0 : ℝ) N))) := by
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have hmeas : Measurable (fun p : ℝ × ℝ => loopArcPhi s N p.1 p.2 u) :=
    measurable_loopArcPhi_of s N measurable_fst measurable_snd measurable_const
  rw [integrable_prod_iff' hmeas.aestronglyMeasurable]
  refine ⟨Filter.Eventually.of_forall fun z => (intervalIntegrable_loopArcPhi s N z u 0 N).1, ?_⟩
  have h : (fun z : ℝ => ∫ t, ‖loopArcPhi s N t z u‖ ∂(volume.restrict (Ioc (0 : ℝ) N)))
      = fun z => (fun δ => |loopArcQ s N δ| * δ) (loopArcFwd N (u - z)) := by
    funext z
    rw [← intervalIntegral.integral_of_le hN0, integral_norm_loopArcPhi]
  rw [h]
  exact (intervalIntegrable_fwd_sub N (intervalIntegrable_loopArcQ_mul s hs0 hs1 N) u).1

/-- The integrability of `g(fwd(u - z))` against `ν ⊗ ν` in `(z, u)`, for a measurable `g` that
is interval integrable on `[0, N]`. -/
theorem integrable_fwd_square (N : ℕ+) {g : ℝ → ℝ} (hgm : Measurable g)
    (hg : IntervalIntegrable g volume 0 N) :
    Integrable (fun p : ℝ × ℝ => g (loopArcFwd N (p.2 - p.1)))
      ((volume.restrict (Ioc (0 : ℝ) N)).prod (volume.restrict (Ioc (0 : ℝ) N))) := by
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have hmeas : Measurable (fun p : ℝ × ℝ => g (loopArcFwd N (p.2 - p.1))) :=
    hgm.comp ((measurable_loopArcFwd_of N).comp (measurable_snd.sub measurable_fst))
  rw [integrable_prod_iff hmeas.aestronglyMeasurable]
  refine ⟨Filter.Eventually.of_forall fun z => (intervalIntegrable_fwd_comp N hg z).1, ?_⟩
  have h : (fun z : ℝ => ∫ u, ‖g (loopArcFwd N (u - z))‖ ∂(volume.restrict (Ioc (0 : ℝ) N)))
      = fun _ => ∫ δ in (0 : ℝ)..(N : ℝ), ‖g δ‖ := by
    funext z
    rw [← intervalIntegral.integral_of_le hN0, integral_fwd_comp N (fun δ => ‖g δ‖) z]
  rw [h]
  exact integrable_const _

/-- The arc kernel is integrable on the triple product, in `((z, u), t)`. -/
theorem integrable_loopArcPhi_triple (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (N : ℕ+) :
    Integrable (fun p : (ℝ × ℝ) × ℝ => loopArcPhi s N p.2 p.1.1 p.1.2)
      (((volume.restrict (Ioc (0 : ℝ) N)).prod (volume.restrict (Ioc (0 : ℝ) N))).prod
        (volume.restrict (Ioc (0 : ℝ) N))) := by
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have hmeas : Measurable (fun p : (ℝ × ℝ) × ℝ => loopArcPhi s N p.2 p.1.1 p.1.2) :=
    measurable_loopArcPhi_of s N measurable_snd measurable_fst.fst measurable_fst.snd
  rw [integrable_prod_iff hmeas.aestronglyMeasurable]
  refine ⟨Filter.Eventually.of_forall fun x => (intervalIntegrable_loopArcPhi s N x.1 x.2 0 N).1,
    ?_⟩
  have h : (fun x : ℝ × ℝ => ∫ t, ‖loopArcPhi s N t x.1 x.2‖ ∂(volume.restrict (Ioc (0 : ℝ) N)))
      = fun x => (fun δ => |loopArcQ s N δ| * δ) (loopArcFwd N (x.2 - x.1)) := by
    funext x
    rw [← intervalIntegral.integral_of_le hN0, integral_norm_loopArcPhi]
  rw [h]
  exact integrable_fwd_square N (measurable_loopArcQ_mul s N)
    (intervalIntegrable_loopArcQ_mul s hs0 hs1 N)

/-- The `t`-integrated arc kernel is bounded by the integral of its absolute value: for a bound
`M` on `b'`, `|∫ b'(t) Φ_t(z, u) dt| ≤ M |Q(δ)| δ` with `δ = fwd(u - z)`. -/
theorem norm_integral_deriv_mul_loopArcPhi_le (s : ℝ) (N : ℕ+) {b : ℝ → ℝ}
    (hb : ContDiff ℝ 1 b) {M : ℝ} (hM : ∀ t, ‖deriv b t‖ ≤ M) (z u : ℝ) :
    ‖∫ t in (0 : ℝ)..(N : ℝ), deriv b t * loopArcPhi s N t z u‖
      ≤ M * (|loopArcQ s N (loopArcFwd N (u - z))| * loopArcFwd N (u - z)) := by
  have hN0 : (0 : ℝ) ≤ N := by positivity
  calc ‖∫ t in (0 : ℝ)..(N : ℝ), deriv b t * loopArcPhi s N t z u‖
      ≤ ∫ t in (0 : ℝ)..(N : ℝ), ‖deriv b t * loopArcPhi s N t z u‖ :=
        intervalIntegral.norm_integral_le_integral_norm hN0
    _ ≤ ∫ t in (0 : ℝ)..(N : ℝ), M * ‖loopArcPhi s N t z u‖ := by
        refine intervalIntegral.integral_mono_on hN0
          (intervalIntegrable_deriv_mul_loopArcPhi s N b hb z u 0 N).norm
          ((intervalIntegrable_loopArcPhi s N z u 0 N).norm.const_mul M) ?_
        intro t _
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hM t) (norm_nonneg _)
    _ = M * ∫ t in (0 : ℝ)..(N : ℝ), ‖loopArcPhi s N t z u‖ :=
        intervalIntegral.integral_const_mul _ _
    _ = M * (|loopArcQ s N (loopArcFwd N (u - z))| * loopArcFwd N (u - z)) := by
        rw [integral_norm_loopArcPhi]

/-- The `t`-integrated arc kernel `∫₀^N b'(t) Φ_t(z, u) dt` is interval integrable in `u`. -/
theorem intervalIntegrable_arc_left (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (N : ℕ+) {b : ℝ → ℝ}
    (hb : ContDiff ℝ 1 b) (hper : Function.Periodic b (N : ℝ)) (z : ℝ) :
    IntervalIntegrable (fun u => ∫ t in (0 : ℝ)..(N : ℝ), deriv b t * loopArcPhi s N t z u)
      volume 0 N := by
  obtain ⟨M, hM⟩ := loopArc_bound_of_periodic N (hb.continuous_deriv le_rfl)
    (deriv_periodic_of hper)
  have hbound := (intervalIntegrable_fwd_comp N
    (intervalIntegrable_loopArcQ_mul s hs0 hs1 N) z).const_mul M
  refine hbound.mono_fun' ?_ ?_
  · have hfun : (fun u => ∫ t in (0 : ℝ)..(N : ℝ), deriv b t * loopArcPhi s N t z u)
        = fun u => loopArcQ s N (loopArcFwd N (u - z)) * (b u - b z) := by
      funext u
      exact integral_deriv_mul_phi s N b hb hper z u
    rw [hfun]
    exact (((measurable_loopArcQ s N).comp
      ((measurable_loopArcFwd_of N).comp (measurable_id.sub_const z))).mul
      (hb.continuous.measurable.sub_const _)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun u => norm_integral_deriv_mul_loopArcPhi_le s N hb
      (fun t => hM t) z u

/-- The `t`-integrated arc kernel is interval integrable in `z`. -/
theorem intervalIntegrable_arc_right (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (N : ℕ+) {b : ℝ → ℝ}
    (hb : ContDiff ℝ 1 b) (hper : Function.Periodic b (N : ℝ)) (u : ℝ) :
    IntervalIntegrable (fun z => ∫ t in (0 : ℝ)..(N : ℝ), deriv b t * loopArcPhi s N t z u)
      volume 0 N := by
  obtain ⟨M, hM⟩ := loopArc_bound_of_periodic N (hb.continuous_deriv le_rfl)
    (deriv_periodic_of hper)
  have hbound := (intervalIntegrable_fwd_sub N
    (intervalIntegrable_loopArcQ_mul s hs0 hs1 N) u).const_mul M
  refine hbound.mono_fun' ?_ ?_
  · have hfun : (fun z => ∫ t in (0 : ℝ)..(N : ℝ), deriv b t * loopArcPhi s N t z u)
        = fun z => loopArcQ s N (loopArcFwd N (u - z)) * (b u - b z) := by
      funext z
      exact integral_deriv_mul_phi s N b hb hper z u
    have hm : Measurable (fun z : ℝ => loopArcFwd N (u - z)) :=
      (measurable_loopArcFwd_of N).comp (measurable_const.sub measurable_id)
    have hm' : Measurable (fun z : ℝ => b u - b z) :=
      measurable_const.sub (hb.continuous.measurable)
    rw [hfun]
    exact (((measurable_loopArcQ s N).comp hm).mul hm').aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun z => norm_integral_deriv_mul_loopArcPhi_le s N hb
      (fun t => hM t) z u

/-- The `t`-integrated arc kernel `F(z, u) = ∫₀^N b'(t) Φ_t(z, u) dt` is integrable on the
background square. -/
theorem integrable_arc_square (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (N : ℕ+) {b : ℝ → ℝ}
    (hb : ContDiff ℝ 1 b) (hper : Function.Periodic b (N : ℝ)) :
    Integrable (fun p : ℝ × ℝ => ∫ t in (0 : ℝ)..(N : ℝ), deriv b t * loopArcPhi s N t p.1 p.2)
      ((volume.restrict (Ioc (0 : ℝ) N)).prod (volume.restrict (Ioc (0 : ℝ) N))) := by
  obtain ⟨M, hM⟩ := loopArc_bound_of_periodic N (hb.continuous_deriv le_rfl)
    (deriv_periodic_of hper)
  have hgI := integrable_fwd_square N (measurable_loopArcQ_mul s N)
    (intervalIntegrable_loopArcQ_mul s hs0 hs1 N)
  refine Integrable.mono' (hgI.const_mul M) ?_ ?_
  · have hfun : (fun p : ℝ × ℝ => ∫ t in (0 : ℝ)..(N : ℝ), deriv b t * loopArcPhi s N t p.1 p.2)
        = fun p => loopArcQ s N (loopArcFwd N (p.2 - p.1)) * (b p.2 - b p.1) := by
      funext p
      exact integral_deriv_mul_phi s N b hb hper p.1 p.2
    have hm : Measurable (fun p : ℝ × ℝ => loopArcFwd N (p.2 - p.1)) :=
      (measurable_loopArcFwd_of N).comp (measurable_snd.sub measurable_fst)
    rw [hfun]
    exact (((measurable_loopArcQ s N).comp hm).mul
      ((hb.continuous.measurable.comp measurable_snd).sub
        (hb.continuous.measurable.comp measurable_fst))).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun p => norm_integral_deriv_mul_loopArcPhi_le s N hb hM
      p.1 p.2

/-- The pairing is additive in the kernel. The hypotheses are the integrability of each kernel on
the background square and on each slice, which the background integrals need. -/
theorem loopArcPairing_add (N : ℕ+) (X : Configuration N) (G H : ℝ → ℝ → ℝ)
    (hG : Integrable (fun p : ℝ × ℝ => G p.1 p.2)
      ((volume.restrict (Ioc (0 : ℝ) N)).prod (volume.restrict (Ioc (0 : ℝ) N))))
    (hH : Integrable (fun p : ℝ × ℝ => H p.1 p.2)
      ((volume.restrict (Ioc (0 : ℝ) N)).prod (volume.restrict (Ioc (0 : ℝ) N))))
    (hGl : ∀ z : ℝ, IntervalIntegrable (fun u => G z u) volume 0 N)
    (hGr : ∀ u : ℝ, IntervalIntegrable (fun z => G z u) volume 0 N)
    (hHl : ∀ z : ℝ, IntervalIntegrable (fun u => H z u) volume 0 N)
    (hHr : ∀ u : ℝ, IntervalIntegrable (fun z => H z u) volume 0 N) :
    loopArcPairing N X (fun z u => G z u + H z u)
      = loopArcPairing N X G + loopArcPairing N X H := by
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have hGi : IntervalIntegrable (fun z => ∫ u in (0 : ℝ)..(N : ℝ), G z u) volume 0 N := by
    refine (intervalIntegrable_iff_integrableOn_Ioc_of_le hN0).2 ?_
    simp only [intervalIntegral.integral_of_le hN0]
    exact hG.integral_prod_left
  have hHi : IntervalIntegrable (fun z => ∫ u in (0 : ℝ)..(N : ℝ), H z u) volume 0 N := by
    refine (intervalIntegrable_iff_integrableOn_Ioc_of_le hN0).2 ?_
    simp only [intervalIntegral.integral_of_le hN0]
    exact hH.integral_prod_left
  have hsplit : ∀ z : ℝ, ∫ u in (0 : ℝ)..(N : ℝ), (G z u + H z u)
      = (∫ u in (0 : ℝ)..(N : ℝ), G z u) + ∫ u in (0 : ℝ)..(N : ℝ), H z u :=
    fun z => intervalIntegral.integral_add (hGl z) (hHl z)
  simp only [loopArcPairing]
  have e1 : ∑ i : Fin (N : ℕ), ∑ j : Fin (N : ℕ), (G (loopArcPos N X i) (loopArcPos N X j)
      + H (loopArcPos N X i) (loopArcPos N X j))
      = (∑ i : Fin (N : ℕ), ∑ j : Fin (N : ℕ), G (loopArcPos N X i) (loopArcPos N X j))
        + ∑ i : Fin (N : ℕ), ∑ j : Fin (N : ℕ), H (loopArcPos N X i) (loopArcPos N X j) := by
    simp only [Finset.sum_add_distrib]
  have e2 : ∑ i : Fin (N : ℕ), ∫ u in (0 : ℝ)..(N : ℝ), (G (loopArcPos N X i) u
      + H (loopArcPos N X i) u)
      = (∑ i : Fin (N : ℕ), ∫ u in (0 : ℝ)..(N : ℝ), G (loopArcPos N X i) u)
        + ∑ i : Fin (N : ℕ), ∫ u in (0 : ℝ)..(N : ℝ), H (loopArcPos N X i) u := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => intervalIntegral.integral_add (hGl _) (hHl _)
  have e3 : ∑ j : Fin (N : ℕ), ∫ z in (0 : ℝ)..(N : ℝ), (G z (loopArcPos N X j)
      + H z (loopArcPos N X j))
      = (∑ j : Fin (N : ℕ), ∫ z in (0 : ℝ)..(N : ℝ), G z (loopArcPos N X j))
        + ∑ j : Fin (N : ℕ), ∫ z in (0 : ℝ)..(N : ℝ), H z (loopArcPos N X j) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => intervalIntegral.integral_add (hGr _) (hHr _)
  have e4 : ∫ z in (0 : ℝ)..(N : ℝ), ∫ u in (0 : ℝ)..(N : ℝ), (G z u + H z u)
      = (∫ z in (0 : ℝ)..(N : ℝ), ∫ u in (0 : ℝ)..(N : ℝ), G z u)
        + ∫ z in (0 : ℝ)..(N : ℝ), ∫ u in (0 : ℝ)..(N : ℝ), H z u := by
    simp only [hsplit]
    exact intervalIntegral.integral_add hGi hHi
  rw [e1, e2, e3, e4]
  ring

/-- The pairing is linear under negation. No integrability is needed. -/
theorem loopArcPairing_neg (N : ℕ+) (X : Configuration N) (G : ℝ → ℝ → ℝ) :
    loopArcPairing N X (fun z u => -G z u) = -loopArcPairing N X G := by
  simp only [loopArcPairing, Finset.sum_neg_distrib, intervalIntegral.integral_neg]
  ring

/-- The pairing commutes with multiplication by a constant. No integrability is needed. -/
theorem loopArcPairing_const_mul (N : ℕ+) (X : Configuration N) (c : ℝ) (G : ℝ → ℝ → ℝ) :
    loopArcPairing N X (fun z u => c * G z u) = c * loopArcPairing N X G := by
  simp only [loopArcPairing, ← Finset.mul_sum, intervalIntegral.integral_const_mul]
  ring

/-- **Kernel as a sum of two arc terms.** For a `C¹` periodic `b`, the pair kernel is
`(b(z) - b(u)) g_N'(z - u) = -(F(z, u) + F(u, z))` with `F(z, u) = ∫₀^N b'(t) Φ_t(z, u) dt`. -/
theorem loopArcKernel_eq_integral_add (s : ℝ) (N : ℕ+) (b : ℝ → ℝ) (hb : ContDiff ℝ 1 b)
    (hper : Function.Periodic b (N : ℝ)) (z u : ℝ) :
    loopArcKernel s N b z u
      = -((∫ t in (0 : ℝ)..(N : ℝ), deriv b t * loopArcPhi s N t z u)
        + ∫ t in (0 : ℝ)..(N : ℝ), deriv b t * loopArcPhi s N t u z) := by
  rw [loopArcKernel_eq_integral s N b hb hper z u,
    ← intervalIntegral.integral_add
      (intervalIntegrable_deriv_mul_loopArcPhi s N b hb z u 0 N)
      (intervalIntegrable_deriv_mul_loopArcPhi s N b hb u z 0 N)]
  simp only [mul_add]

/-- **The loop functional as an arc integral.** For a `C¹` `N`-periodic `b`, and every
configuration `X`, the loop functional is `L(b) = -2 ∫₀^N b'(t) P_t dt`, where
`P_t = loopArcPairing N X (Φ_t)` is the pairing of the arc kernel `Φ_t` against `ν ⊗ ν`. This is
the first step of the arcs part of Lemma B.2. The identification of `P_t` with `Λ(t)`
is the next step. -/
theorem loopArcL_eq_integral_pairing (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (N : ℕ+) (b : ℝ → ℝ)
    (hb : ContDiff ℝ 1 b) (hper : Function.Periodic b (N : ℝ)) (X : Configuration N) :
    loopArcL s N b X
      = -2 * ∫ t in (0 : ℝ)..(N : ℝ), deriv b t * loopArcPairing N X (loopArcPhi s N t) := by
  have hb' : Continuous (deriv b) := hb.continuous_deriv le_rfl
  obtain ⟨M, hM⟩ := loopArc_bound_of_periodic N hb' (deriv_periodic_of hper)
  have hsq := integrable_arc_square s hs0 hs1 N hb hper
  have hsq' : Integrable (fun p : ℝ × ℝ =>
      ∫ t in (0 : ℝ)..(N : ℝ), deriv b t * loopArcPhi s N t p.2 p.1)
      ((volume.restrict (Ioc (0 : ℝ) N)).prod (volume.restrict (Ioc (0 : ℝ) N))) := hsq.swap
  -- Step 1: the kernel is `-(F + Fᵀ)`, so `L(b) = -(Pair F + Pair Fᵀ)`.
  have hpair : loopArcPairing N X (fun z u =>
      (∫ t in (0 : ℝ)..(N : ℝ), deriv b t * loopArcPhi s N t z u)
        + ∫ t in (0 : ℝ)..(N : ℝ), deriv b t * loopArcPhi s N t u z)
      = loopArcPairing N X (fun z u => ∫ t in (0 : ℝ)..(N : ℝ), deriv b t * loopArcPhi s N t z u)
        + loopArcPairing N X (fun z u => ∫ t in (0 : ℝ)..(N : ℝ), deriv b t * loopArcPhi s N t u z) :=
    loopArcPairing_add N X _ _ hsq hsq'
      (fun z => intervalIntegrable_arc_left s hs0 hs1 N hb hper z)
      (fun u => intervalIntegrable_arc_right s hs0 hs1 N hb hper u)
      (fun z => intervalIntegrable_arc_right s hs0 hs1 N hb hper z)
      (fun u => intervalIntegrable_arc_left s hs0 hs1 N hb hper u)
  have hL : loopArcL s N b X = -(loopArcPairing N X
      (fun z u => ∫ t in (0 : ℝ)..(N : ℝ), deriv b t * loopArcPhi s N t z u)
        + loopArcPairing N X (fun z u => ∫ t in (0 : ℝ)..(N : ℝ), deriv b t * loopArcPhi s N t u z)) := by
    have hfun : loopArcKernel s N b = fun z u => -((∫ t in (0 : ℝ)..(N : ℝ),
        deriv b t * loopArcPhi s N t z u) + ∫ t in (0 : ℝ)..(N : ℝ),
          deriv b t * loopArcPhi s N t u z) :=
      funext fun z => funext fun u => loopArcKernel_eq_integral_add s N b hb hper z u
    rw [loopArcL_eq_pairing, hfun]
    rw [loopArcPairing_neg N X (fun z u => (∫ t in (0 : ℝ)..(N : ℝ), deriv b t * loopArcPhi s N t z u)
        + ∫ t in (0 : ℝ)..(N : ℝ), deriv b t * loopArcPhi s N t u z), hpair]
  -- Step 2: the pairing of `Fᵀ` is that of `F`, by symmetry.
  have hswap : loopArcPairing N X (fun z u => ∫ t in (0 : ℝ)..(N : ℝ), deriv b t * loopArcPhi s N t u z)
      = loopArcPairing N X (fun z u => ∫ t in (0 : ℝ)..(N : ℝ), deriv b t * loopArcPhi s N t z u) :=
    loopArcPairing_swap N X _ hsq
  -- Step 3: Fubini in `t`, using the four integrability blocks.
  have h1 : ∀ i j : Fin (N : ℕ), Integrable
      (fun t => deriv b t * loopArcPhi s N t (loopArcPos N X i) (loopArcPos N X j))
      (volume.restrict (Ioc (0 : ℝ) N)) :=
    fun i j => (intervalIntegrable_deriv_mul_loopArcPhi s N b hb _ _ 0 N).1
  have h2 : ∀ i : Fin (N : ℕ), Integrable
      (fun p : ℝ × ℝ => deriv b p.1 * loopArcPhi s N p.1 (loopArcPos N X i) p.2)
      ((volume.restrict (Ioc (0 : ℝ) N)).prod (volume.restrict (Ioc (0 : ℝ) N))) :=
    fun i => Integrable.bdd_mul (integrable_loopArcPhi_fixed_left s hs0 hs1 N _)
      (hb'.measurable.comp measurable_fst).aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => hM p.1)
  have h3 : ∀ j : Fin (N : ℕ), Integrable
      (fun p : ℝ × ℝ => deriv b p.1 * loopArcPhi s N p.1 p.2 (loopArcPos N X j))
      ((volume.restrict (Ioc (0 : ℝ) N)).prod (volume.restrict (Ioc (0 : ℝ) N))) :=
    fun j => Integrable.bdd_mul (integrable_loopArcPhi_fixed_right s hs0 hs1 N _)
      (hb'.measurable.comp measurable_fst).aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => hM p.1)
  have h4 : Integrable (fun p : (ℝ × ℝ) × ℝ => deriv b p.2 * loopArcPhi s N p.2 p.1.1 p.1.2)
      (((volume.restrict (Ioc (0 : ℝ) N)).prod (volume.restrict (Ioc (0 : ℝ) N))).prod
        (volume.restrict (Ioc (0 : ℝ) N))) :=
    Integrable.bdd_mul (integrable_loopArcPhi_triple s hs0 hs1 N)
      (hb'.measurable.comp measurable_snd).aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => hM p.2)
  have hfub : loopArcPairing N X
      (fun z u => ∫ t in (0 : ℝ)..(N : ℝ), deriv b t * loopArcPhi s N t z u)
      = ∫ t in (0 : ℝ)..(N : ℝ), loopArcPairing N X
          (fun z u => deriv b t * loopArcPhi s N t z u) :=
    loopArcPairing_integral_comm N X (fun t z u => deriv b t * loopArcPhi s N t z u) h1 h2 h3 h4
  have hpt : ∫ t in (0 : ℝ)..(N : ℝ), loopArcPairing N X
      (fun z u => deriv b t * loopArcPhi s N t z u)
      = ∫ t in (0 : ℝ)..(N : ℝ), deriv b t * loopArcPairing N X (loopArcPhi s N t) :=
    intervalIntegral.integral_congr fun t _ => loopArcPairing_const_mul N X _ _
  rw [hL, hswap, hfub, hpt]
  ring

end Riesz1

end
end
