/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopArcsKernel
public import Mathlib.MeasureTheory.Function.Floor

/-!
# Forward distances and the arc kernel `Φ_t`

For the arc-crossing representation of Lemma 5.8, every pair `(z, u)` of
points of the microscopic circle is written through the forward distance `loopArcFwd N x ∈ [0, N)`
of `x` modulo `N`, and the kernel

`Φ_t(z, u) = Q(fwd(t - z) + fwd(u - t))`

records the arc of `N𝕋` from `z` to `u` through `t`. This file proves the two facts the
representation rests on:

* the `t`-slice identity `∫₀^N b'(t) Φ_t(z, u) dt = Q(fwd(u - z)) (b(u) - b(z))` for every
  smooth `N`-periodic `b` (a change of variables, no arc bookkeeping).
* `Q` vanishes at distances `≥ N/2`, so the forward sum `fwd(t - z) + fwd(u - t)` contributes
  only when it is below `N/2`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace Riesz1

/-- The forward distance `fwd N x = N · fract(x / N) ∈ [0, N)` of a real `x` modulo `N`. -/
noncomputable def loopArcFwd (N : ℕ+) (x : ℝ) : ℝ := (N : ℝ) * Int.fract (x / N)

theorem loopArcFwd_nonneg (N : ℕ+) (x : ℝ) : 0 ≤ loopArcFwd N x :=
  mul_nonneg (Nat.cast_nonneg _) (Int.fract_nonneg _)

theorem loopArcFwd_lt (N : ℕ+) (x : ℝ) : loopArcFwd N x < N := by
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  exact mul_lt_of_lt_one_right hN (Int.fract_lt_one _)

/-- The forward distance is invariant under integer translates by `N`. -/
theorem loopArcFwd_add_int_mul (N : ℕ+) (x : ℝ) (k : ℤ) :
    loopArcFwd N (x + k * N) = loopArcFwd N x := by
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast N.ne_zero
  unfold loopArcFwd
  rw [show (x + (k : ℝ) * N) / N = x / N + k by field_simp, Int.fract_add_intCast]

/-- The forward distance of a point in `[0, N)` is the point itself. -/
theorem loopArcFwd_of_mem {N : ℕ+} {x : ℝ} (h0 : 0 ≤ x) (h1 : x < N) :
    loopArcFwd N x = x := by
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast N.ne_zero
  have hN' : (0 : ℝ) < N := by exact_mod_cast N.pos
  unfold loopArcFwd
  rw [Int.fract_eq_self.mpr ⟨div_nonneg h0 hN'.le, (div_lt_one hN').mpr h1⟩]
  field_simp

/-- A point in `(-N, 0)` has forward distance `x + N`. -/
theorem loopArcFwd_of_neg {N : ℕ+} {x : ℝ} (h0 : -(N : ℝ) < x) (h1 : x < 0) :
    loopArcFwd N x = x + N := by
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast N.ne_zero
  have hN' : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hfr : Int.fract (x / N) = x / N + 1 := by
    rw [← Int.fract_add_one (x / N)]
    refine Int.fract_eq_self.mpr ⟨?_, ?_⟩
    · have : -1 < x / N := by rw [lt_div_iff₀ hN']; linarith
      linarith
    · have : x / N < 0 := div_neg_of_neg_of_pos h1 hN'
      linarith
  unfold loopArcFwd
  rw [hfr]
  field_simp

/-- Every real is a forward distance plus an integer multiple of `N`. -/
theorem loopArcFwd_sub_floor (N : ℕ+) (x : ℝ) :
    x = loopArcFwd N x + (⌊x / N⌋ : ℝ) * N := by
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast N.ne_zero
  unfold loopArcFwd
  rw [← Int.self_sub_floor]
  field_simp
  ring

/-- The arc kernel `Φ_t(z, u) = Q(fwd(t - z) + fwd(u - t))`: the cutoff evaluated at the length of
the arc from `z` to `u` through `t`. -/
noncomputable def loopArcPhi (s : ℝ) (N : ℕ+) (t z u : ℝ) : ℝ :=
  loopArcQ s N (loopArcFwd N (t - z) + loopArcFwd N (u - t))

/-- A `Q`-value at a length of at least `N / 2` vanishes. -/
theorem loopArcQ_eq_zero_of_le (s : ℝ) (N : ℕ+) {r : ℝ} (h : (N : ℝ) / 2 ≤ r) :
    loopArcQ s N r = 0 := by
  have h' : ¬ r < (N : ℝ) / 2 := not_lt.mpr h
  simp only [loopArcQ, h', ↓reduceIte]

/-- **The `t`-slice identity.** For a `C¹` function `b` with period `N`, and for `z, u ∈ ℝ`,
`∫₀^N b'(t) Φ_t(z, u) dt = Q(fwd(u - z)) (b(u) - b(z))`. The integrand is
`N`-periodic in `t`. Shifting the window to `[z, z + N]` and splitting at `fwd(u - z)` leaves
only the piece where the arc from `z` to `u` lies in `[z, z + fwd(u - z)]`. -/
theorem integral_deriv_mul_phi (s : ℝ) (N : ℕ+) (b : ℝ → ℝ) (hb : ContDiff ℝ 1 b)
    (hper : Function.Periodic b (N : ℝ)) (z u : ℝ) :
    ∫ t in (0 : ℝ)..(N : ℝ), deriv b t * loopArcPhi s N t z u
      = loopArcQ s N (loopArcFwd N (u - z)) * (b u - b z) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hdper : Function.Periodic (deriv b) (N : ℝ) := deriv_periodic_of hper
  have hFper : Function.Periodic (fun t => deriv b t * loopArcPhi s N t z u) (N : ℝ) := by
    intro t
    simp only [loopArcPhi]
    rw [hdper t, show t + N - z = (t - z) + ((1 : ℤ) : ℝ) * N by push_cast; ring,
      show u - (t + N) = (u - t) + ((-1 : ℤ) : ℝ) * N by push_cast; ring,
      loopArcFwd_add_int_mul, loopArcFwd_add_int_mul]
  -- Shift the window from `[0, N]` to `[z, z + N]`, then to `[0, N]` again around `z`.
  have h1 : ∫ t in (0 : ℝ)..(N : ℝ), deriv b t * loopArcPhi s N t z u
      = ∫ t in z..z + N, deriv b t * loopArcPhi s N t z u := by
    have := hFper.intervalIntegral_add_eq 0 z
    simpa using this
  have h2 : ∫ τ in (0 : ℝ)..(N : ℝ), deriv b (z + τ) * loopArcPhi s N (z + τ) z u
      = ∫ t in z..z + N, deriv b t * loopArcPhi s N t z u := by
    have h := intervalIntegral.integral_comp_add_left (a := 0) (b := (N : ℝ)) (d := z)
      (fun t => deriv b t * loopArcPhi s N t z u)
    simpa only [add_zero] using h
  -- Notation: the forward distance `δ = fwd(u - z)` and the integer `k` with `u - z = δ + k N`.
  set δ := loopArcFwd N (u - z) with hδ_def
  set k : ℤ := ⌊(u - z) / N⌋ with hk_def
  have hδ0 : 0 ≤ δ := loopArcFwd_nonneg N _
  have hδN : δ < N := loopArcFwd_lt N _
  have hk : u - z = δ + (k : ℝ) * N := loopArcFwd_sub_floor N (u - z)
  -- On `[0, δ]` the arc kernel is the constant `Q(δ)`.
  have hpre : ∀ τ ∈ Icc (0 : ℝ) δ, deriv b (z + τ) * loopArcPhi s N (z + τ) z u
      = deriv b (z + τ) * loopArcQ s N δ := by
    intro τ hτ
    have hτ0 : 0 ≤ τ := hτ.1
    have hτN : τ < N := lt_of_le_of_lt hτ.2 hδN
    have hA : loopArcFwd N ((z + τ) - z) = τ := by
      rw [show (z + τ) - z = τ by ring]
      exact loopArcFwd_of_mem hτ0 hτN
    have hB : loopArcFwd N (u - (z + τ)) = δ - τ := by
      have hcongr : u - (z + τ) = (δ - τ) + (k : ℝ) * N := by linear_combination hk
      rw [hcongr, loopArcFwd_add_int_mul]
      exact loopArcFwd_of_mem (by linarith [hτ.2]) (by linarith [hτ.1, hδN])
    simp only [loopArcPhi]
    rw [hA, hB, show τ + (δ - τ) = δ by ring]
  -- On `(δ, N)` the arc kernel vanishes, since the total length is at least `N`.
  have hpost : ∀ τ ∈ Ioo δ (N : ℝ), deriv b (z + τ) * loopArcPhi s N (z + τ) z u = 0 := by
    intro τ hτ
    have hτ0 : 0 ≤ τ := by linarith [hτ.1, hδ0]
    have hτN : τ < N := hτ.2
    have hA : loopArcFwd N ((z + τ) - z) = τ := by
      rw [show (z + τ) - z = τ by ring]
      exact loopArcFwd_of_mem hτ0 hτN
    have hB : loopArcFwd N (u - (z + τ)) = δ - τ + N := by
      have hcongr : u - (z + τ) = (δ - τ + N) + ((k - 1 : ℤ) : ℝ) * N := by
        push_cast
        linear_combination hk
      rw [hcongr, loopArcFwd_add_int_mul]
      exact loopArcFwd_of_mem (by linarith [hτ.2, hδ0]) (by linarith [hτ.1])
    have hNpos : (0 : ℝ) < N := by exact_mod_cast N.pos
    have hQ : loopArcQ s N (τ + (δ - τ + N)) = 0 :=
      loopArcQ_eq_zero_of_le s N (by linarith [hδ0])
    simp only [loopArcPhi]
    rw [hA, hB, hQ, mul_zero]
  -- Integrability of the integrand on the two pieces, from the explicit values there.
  have hcontG : Continuous (fun τ : ℝ => deriv b (z + τ)) :=
    (hb.continuous_deriv le_rfl).comp (continuous_const_add z)
  have hIpre : IntervalIntegrable (fun τ => deriv b (z + τ) * loopArcPhi s N (z + τ) z u)
      volume 0 δ := by
    have hc : IntervalIntegrable (fun τ => deriv b (z + τ) * loopArcQ s N δ) volume 0 δ :=
      (hcontG.mul continuous_const).intervalIntegrable 0 δ
    refine hc.congr_uIoo ?_
    intro τ hτ
    have hτ' : τ ∈ Icc (0 : ℝ) δ := by
      rw [uIoo_of_le hδ0] at hτ
      exact ⟨hτ.1.le, hτ.2.le⟩
    exact (hpre τ hτ').symm
  have hIpost : IntervalIntegrable (fun τ => deriv b (z + τ) * loopArcPhi s N (z + τ) z u)
      volume δ N := by
    refine (intervalIntegrable_const (c := (0 : ℝ))).congr_uIoo ?_
    intro τ hτ
    rw [uIoo_of_le hδN.le] at hτ
    exact (hpost τ hτ).symm
  -- On `[0, δ]` the integral is `Q(δ)` times the increment of `b` over `[z, z + δ]`.
  have hFTC : ∫ τ in (0 : ℝ)..δ, deriv b (z + τ) = b (z + δ) - b z := by
    rw [intervalIntegral.integral_comp_add_left (f := deriv b) (a := 0) (b := δ) (d := z),
      add_zero]
    exact intervalIntegral.integral_deriv_eq_sub (fun x _ => (hb.differentiable (by norm_num)) x)
      ((hb.continuous_deriv le_rfl).intervalIntegrable _ _)
  have hpre_int : ∫ τ in (0 : ℝ)..δ, deriv b (z + τ) * loopArcPhi s N (z + τ) z u
      = loopArcQ s N δ * (b (z + δ) - b z) := by
    rw [intervalIntegral.integral_congr (g := fun τ => deriv b (z + τ) * loopArcQ s N δ)
      (fun τ hτ => hpre τ (by rwa [uIcc_of_le hδ0] at hτ)),
      intervalIntegral.integral_mul_const, hFTC, mul_comm]
  -- On `(δ, N)` the integrand vanishes, except possibly at the endpoint `N`.
  have hN_ae : ∀ᵐ τ ∂(volume : Measure ℝ), τ ≠ (N : ℝ) := by
    rw [ae_iff]
    simp
  have hpost_int : ∫ τ in δ..(N : ℝ), deriv b (z + τ) * loopArcPhi s N (z + τ) z u = 0 := by
    rw [intervalIntegral.integral_congr_ae (g := fun _ => (0 : ℝ))]
    · simp
    · filter_upwards [hN_ae] with τ hτN hτ
      rw [uIoc_of_le hδN.le] at hτ
      exact hpost τ ⟨hτ.1, lt_of_le_of_ne hτ.2 hτN⟩
  -- The periodicity of `b` identifies `b (z + δ)` with `b u`, since `u = z + δ + k N`.
  have hbu : b u = b (z + δ) := by
    have h := (hper.int_mul k) (z + δ)
    rw [show z + δ + (k : ℝ) * N = u by linear_combination -hk] at h
    exact h
  have hmain : ∫ τ in (0 : ℝ)..(N : ℝ), deriv b (z + τ) * loopArcPhi s N (z + τ) z u
      = loopArcQ s N δ * (b u - b z) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hIpre hIpost, hpre_int, hpost_int,
      add_zero, hbu]
  rw [h1, ← h2, hmain]

/-- **Closed form of the arc kernel.** With `δ = fwd(u - z)`, the kernel `Φ_t(z, u)` equals `Q(δ)`
when `fwd(t - z) ≤ δ` (the point `t` lies on the arc from `z` to `u`) and vanishes otherwise. -/
theorem loopArcPhi_eq_ite (s : ℝ) (N : ℕ+) (t z u : ℝ) :
    loopArcPhi s N t z u = if loopArcFwd N (t - z) ≤ loopArcFwd N (u - z)
      then loopArcQ s N (loopArcFwd N (u - z)) else 0 := by
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  set δ := loopArcFwd N (u - z) with hδ_def
  set k : ℤ := ⌊(u - z) / N⌋ with hk_def
  have hδ0 : 0 ≤ δ := loopArcFwd_nonneg N _
  have hδN : δ < N := loopArcFwd_lt N _
  have hk : u - z = δ + (k : ℝ) * N := loopArcFwd_sub_floor N (u - z)
  set τ := loopArcFwd N (t - z) with hτ_def
  set m : ℤ := ⌊(t - z) / N⌋ with hm_def
  have hτ0 : 0 ≤ τ := loopArcFwd_nonneg N _
  have hτN : τ < N := loopArcFwd_lt N _
  have hm : t - z = τ + (m : ℝ) * N := loopArcFwd_sub_floor N (t - z)
  have hcongr : u - t = (δ - τ) + ((k - m : ℤ) : ℝ) * N := by
    push_cast
    linear_combination hk - hm
  unfold loopArcPhi
  rw [← hτ_def, show u - t = (δ - τ) + ((k - m : ℤ) : ℝ) * N from hcongr,
    loopArcFwd_add_int_mul]
  by_cases hle : τ ≤ δ
  · have h1 : loopArcFwd N (δ - τ) = δ - τ := loopArcFwd_of_mem (by linarith) (by linarith)
    simp only [hle, ↓reduceIte, h1, show τ + (δ - τ) = δ by ring]
  · have h1 : loopArcFwd N (δ - τ) = δ - τ + N := loopArcFwd_of_neg (by linarith) (by linarith)
    have hQ : loopArcQ s N (τ + (δ - τ + N)) = 0 :=
      loopArcQ_eq_zero_of_le s N (by linarith [hδ0])
    simp only [hle, ↓reduceIte, h1, hQ]

/-- The forward distance is measurable. -/
theorem measurable_loopArcFwd (N : ℕ+) (z : ℝ) :
    Measurable (fun t : ℝ => loopArcFwd N (t - z)) := by
  unfold loopArcFwd
  exact (measurable_fract.comp ((measurable_id.sub_const z).div_const _)).const_mul _

/-- As a function of `t`, the arc kernel is measurable. -/
theorem measurable_loopArcPhi (s : ℝ) (N : ℕ+) (z u : ℝ) :
    Measurable (fun t => loopArcPhi s N t z u) := by
  simp only [loopArcPhi_eq_ite]
  exact Measurable.ite (measurableSet_le (measurable_loopArcFwd N z) measurable_const)
    measurable_const measurable_const

/-- The arc kernel is bounded in `t`, by `|Q(δ)|`. -/
theorem norm_loopArcPhi_le (s : ℝ) (N : ℕ+) (t z u : ℝ) :
    ‖loopArcPhi s N t z u‖ ≤ |loopArcQ s N (loopArcFwd N (u - z))| := by
  rw [loopArcPhi_eq_ite]
  split_ifs
  · rfl
  · simp

/-- The arc kernel is integrable in `t` on every compact interval, being bounded and measurable. -/
theorem integrableOn_loopArcPhi (s : ℝ) (N : ℕ+) (z u a c : ℝ) :
    IntegrableOn (fun t => loopArcPhi s N t z u) (Set.uIcc a c) volume :=
  IntegrableOn.of_bound measure_Icc_lt_top
    (measurable_loopArcPhi s N z u).aestronglyMeasurable
    |loopArcQ s N (loopArcFwd N (u - z))| (Filter.Eventually.of_forall fun t =>
      norm_loopArcPhi_le s N t z u)

/-- The arc kernel is interval integrable in `t` over every interval. -/
theorem intervalIntegrable_loopArcPhi (s : ℝ) (N : ℕ+) (z u a c : ℝ) :
    IntervalIntegrable (fun t => loopArcPhi s N t z u) volume a c :=
  (integrableOn_loopArcPhi s N z u a c).intervalIntegrable

/-- The product of `b'` with the arc kernel is interval integrable, since `b'` is continuous. -/
theorem intervalIntegrable_deriv_mul_loopArcPhi (s : ℝ) (N : ℕ+) (b : ℝ → ℝ)
    (hb : ContDiff ℝ 1 b) (z u a c : ℝ) :
    IntervalIntegrable (fun t => deriv b t * loopArcPhi s N t z u) volume a c := by
  have hcont : Continuous (deriv b) := hb.continuous_deriv le_rfl
  have hΦ : IntegrableOn (fun t => loopArcPhi s N t z u) (Set.uIcc a c) volume :=
    integrableOn_loopArcPhi s N z u a c
  have h2 : IntegrableOn (fun t => loopArcPhi s N t z u * deriv b t) (Set.uIcc a c) volume :=
    hΦ.mul_continuousOn hcont.continuousOn isCompact_uIcc
  exact IntegrableOn.intervalIntegrable (h2.congr_fun (fun t _ => mul_comm _ _) measurableSet_uIcc)


/-- The derivative of the microscopic kernel is `N`-periodic. -/
theorem deriv_loopArcG_periodic (s : ℝ) (N : ℕ+) :
    Function.Periodic (deriv (loopArcG s N)) (N : ℝ) :=
  deriv_periodic_of (loopArcG_periodic s N)

/-- **Kernel representation.** For a `C¹` function `b` with period `N`, every `z, u ∈ ℝ` satisfy
`(b(z) - b(u)) g_N'(z - u) = -∫₀^N b'(t) (Φ_t(z, u) + Φ_t(u, z)) dt`. The two arc terms are the
two orientations of the arc between `z` and `u`. The identity needs no restriction on `z - u`. -/
theorem loopArcKernel_eq_integral (s : ℝ) (N : ℕ+) (b : ℝ → ℝ) (hb : ContDiff ℝ 1 b)
    (hper : Function.Periodic b (N : ℝ)) (z u : ℝ) :
    loopArcKernel s N b z u
      = -∫ t in (0 : ℝ)..(N : ℝ), deriv b t * (loopArcPhi s N t z u + loopArcPhi s N t u z) := by
  have hsum : ∫ t in (0 : ℝ)..(N : ℝ), deriv b t * (loopArcPhi s N t z u + loopArcPhi s N t u z)
      = (∫ t in (0 : ℝ)..(N : ℝ), deriv b t * loopArcPhi s N t z u)
        + ∫ t in (0 : ℝ)..(N : ℝ), deriv b t * loopArcPhi s N t u z := by
    simp only [mul_add]
    exact intervalIntegral.integral_add
      (intervalIntegrable_deriv_mul_loopArcPhi s N b hb z u 0 N)
      (intervalIntegrable_deriv_mul_loopArcPhi s N b hb u z 0 N)
  rw [hsum, integral_deriv_mul_phi s N b hb hper z u, integral_deriv_mul_phi s N b hb hper u z]
  unfold loopArcKernel
  set δ := loopArcFwd N (u - z) with hδ_def
  set k : ℤ := ⌊(u - z) / N⌋ with hk_def
  have hδ0 : 0 ≤ δ := loopArcFwd_nonneg N _
  have hδN : δ < N := loopArcFwd_lt N _
  have hk : u - z = δ + (k : ℝ) * N := loopArcFwd_sub_floor N (u - z)
  rcases eq_or_lt_of_le hδ0 with hδz | hδpos
  · -- If `δ = 0` then `u = z + k N`, so `b u = b z` and both sides vanish.
    have hbz : b u = b z := by
      have h := (hper.int_mul k) z
      rw [show z + (k : ℝ) * N = u by linear_combination -hk + hδz] at h
      exact h
    rw [hbz]
    simp
  · -- Here `0 < δ < N`, and `fwd(z - u) = N - δ`.
    have hδ'eq : loopArcFwd N (z - u) = N - δ := by
      have hcongr : z - u = (N - δ) + ((-k - 1 : ℤ) : ℝ) * N := by
        push_cast
        linear_combination -hk
      rw [hcongr, loopArcFwd_add_int_mul]
      exact loopArcFwd_of_mem (by linarith) (by linarith)
    -- The derivative at `z - u` is the derivative at `-δ`, which is odd.
    have hdz : deriv (loopArcG s N) (z - u) = -deriv (loopArcG s N) δ := by
      have hcongr' : z - u = (-δ) + ((-k : ℤ) : ℝ) * N := by
        push_cast
        linear_combination -hk
      rw [hcongr']
      exact ((deriv_loopArcG_periodic s N).int_mul (-k) (-δ)).trans (deriv_loopArcG_neg s N δ)
    -- The cutoff identity `Q(δ) - Q(N - δ) = -g_N'(δ)`, by the three positions of `δ`.
    have hQ : loopArcQ s N δ - loopArcQ s N (N - δ) = -deriv (loopArcG s N) δ := by
      have hsymm : deriv (loopArcG s N) (N - δ) = -deriv (loopArcG s N) δ := by
        rw [show (N : ℝ) - δ = -δ + N by ring, deriv_loopArcG_periodic s N (-δ),
          deriv_loopArcG_neg s N δ]
      rcases lt_trichotomy δ ((N : ℝ) / 2) with h | h | h
      · have h1 : loopArcQ s N δ = -deriv (loopArcG s N) δ := by
          simp only [loopArcQ, h, ↓reduceIte]
        have h2 : loopArcQ s N (N - δ) = 0 := loopArcQ_eq_zero_of_le s N (by linarith)
        rw [h1, h2, sub_zero]
      · have h1 : loopArcQ s N δ = 0 := loopArcQ_eq_zero_of_le s N h.symm.le
        have h2 : loopArcQ s N (N - δ) = 0 := loopArcQ_eq_zero_of_le s N (by linarith)
        have hd : deriv (loopArcG s N) δ = 0 := by
          rw [h]
          exact deriv_loopArcG_half s N
        rw [h1, h2, hd, sub_zero, neg_zero]
      · have h1 : loopArcQ s N δ = 0 := loopArcQ_eq_zero_of_le s N h.le
        have hlt : N - δ < (N : ℝ) / 2 := by linarith
        have h2 : loopArcQ s N (N - δ) = -deriv (loopArcG s N) (N - δ) := by
          simp only [loopArcQ, hlt, ↓reduceIte]
        rw [h1, h2, hsymm]
        ring
    have hG : deriv (loopArcG s N) (z - u) = loopArcQ s N δ - loopArcQ s N (N - δ) :=
      hdz.trans hQ.symm
    rw [hδ'eq]
    linear_combination (b z - b u) * hG

end Riesz1

end
end
