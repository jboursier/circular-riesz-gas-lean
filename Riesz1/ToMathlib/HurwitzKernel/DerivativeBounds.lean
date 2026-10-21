/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.HurwitzKernel.Derivatives

/-!
# Derivative bounds for the Hurwitz kernel

For `0 < s < 1` and every `m : ℕ` there is a number `C` with
`|g^{(m)}(x)| ≤ C * dist (x : UnitAddCircle) 0 ^ (-s - m)` for every non-integer `x`, where
`g = hurwitzKernel s` and `dist (x : UnitAddCircle) 0` is the distance from `x` to the nearest
integer (`UnitAddCircle.norm_eq`).

On `(0,1)` the kernel is `x ^ (-s) + (1 - x) ^ (-s) + Re Q(x) + Re Q(1 - x) - 2 / (1 - s)`, where
`Q` is the Euler remainder series. Each piece has explicit iterated derivatives: powers of
affine maps, and real parts of the complex series `∑ₙ (n + 1 + w) ^ (-a)`. Periodicity and
evenness move every non-integer point into `(0, 1/2]`.

Lemma 2.1, derivative bounds.
-/

public section

open Filter Topology MeasureTheory Set Complex
open scoped ContDiff
namespace Riesz1

lemma summable_nat_add_one_rpow_sub (s : ℝ) (hs : 0 < s) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-s - 1)) := by
  have h := (summable_nat_add_iff 1).mpr
    (Real.summable_nat_rpow.mpr (show -s - 1 < -1 by linarith))
  simpa only [Nat.cast_add, Nat.cast_one] using h

/-- A uniform bound on the shifted series `shiftPowSum a` on the half-plane `-1/2 < re w`. -/
lemma norm_shiftPowSum_le (a : ℝ) (ha : 1 < a) (w : ℂ) (hw : -(1 / 2 : ℝ) < w.re) :
    ‖shiftPowSum a w‖ ≤ ∑' n : ℕ, (2 : ℝ) ^ a * ((n : ℝ) + 1) ^ (-a) := by
  unfold shiftPowSum
  exact tsum_of_norm_bounded ((summable_nat_add_one_rpow a ha).mul_left _).hasSum
    (fun n => norm_shift_cpow_le a (by linarith) n w hw)

/-- The Euler remainder series is bounded on the unit disc intersected with `-1/2 < re w`. -/
lemma norm_eulerSum_le (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (w : ℂ) (hw : -(1 / 2 : ℝ) < w.re)
    (hwR : ‖w‖ ≤ 1) :
    ‖∑' n : ℕ, eulerTermC s w n‖ ≤
      ∑' n : ℕ, (s + s * 2 ^ (s + 1) * 1) * ((n : ℝ) + 1) ^ (-s - 1) :=
  tsum_of_norm_bounded
    ((summable_nat_add_one_rpow_sub s hs0).mul_left _).hasSum
    (fun n => norm_eulerTermC_le s hs0 hs1 1 zero_le_one w hw hwR n)

lemma isOpen_affine_pos (α β : ℝ) : IsOpen {z : ℝ | 0 < α + β * z} :=
  isOpen_lt continuous_const (by fun_prop)

/-- Iterated derivatives of a power of an affine map, on the region where the base is positive. -/
lemma iteratedDeriv_affine_rpow (p α β : ℝ) (k : ℕ) :
    ∃ c : ℝ, ∀ x : ℝ, 0 < α + β * x →
      iteratedDeriv k (fun x : ℝ => (α + β * x) ^ p) x = c * (α + β * x) ^ (p - k) := by
  induction k with
  | zero => exact ⟨1, fun x _ => by simp⟩
  | succ k ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨c * (β * (p - k)), fun x hx => ?_⟩
    have hopen := isOpen_affine_pos α β
    have hev : iteratedDeriv k (fun x : ℝ => (α + β * x) ^ p) =ᶠ[𝓝 x]
        fun z => c * (α + β * z) ^ (p - k) := by
      filter_upwards [hopen.mem_nhds hx] with z hz using hc z hz
    rw [iteratedDeriv_succ, hev.deriv_eq]
    have h1 : HasDerivAt (fun z : ℝ => α + β * z) β x := by
      simpa using ((hasDerivAt_id x).const_mul β).const_add α
    have h2 := (h1.rpow_const (p := p - k) (Or.inl hx.ne')).const_mul c
    rw [h2.deriv, show p - ((k + 1 : ℕ) : ℝ) = p - k - 1 by push_cast; ring]
    ring

/-- The real part of a complex-differentiable function along an affine real map. -/
lemma hasDerivAt_re_affine (α β : ℝ) (Φ : ℂ → ℂ) (Φ' : ℂ) (x : ℝ)
    (hΦ : HasDerivAt Φ Φ' ((α + β * x : ℝ) : ℂ)) :
    HasDerivAt (fun y : ℝ => (Φ ((α + β * y : ℝ) : ℂ)).re) (β * Φ'.re) x := by
  have hl : HasDerivAt (fun v : ℂ => (α : ℂ) + (β : ℂ) * v) (β : ℂ) (x : ℂ) := by
    simpa using ((hasDerivAt_id' (x : ℂ)).const_mul (β : ℂ)).const_add (α : ℂ)
  have hΦ' : HasDerivAt Φ Φ' ((α : ℂ) + (β : ℂ) * (x : ℂ)) := by
    convert hΦ using 1
    push_cast
    rfl
  have h := ((hΦ'.comp (x : ℂ) hl).real_of_complex)
  convert h using 1
  · funext y
    congr 2
    push_cast
    rfl
  · simp [Complex.mul_re]
    ring

/-- Iterated derivatives of the real part of the Euler series along an affine map. -/
lemma iteratedDeriv_re_affine_euler (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (α β : ℝ) (k : ℕ) :
    ∃ c : ℝ, ∀ x : ℝ, 0 < α + β * x →
      iteratedDeriv (k + 1) (fun x : ℝ => (∑' n, eulerTermC s ((α + β * x : ℝ) : ℂ) n).re) x =
        c * (shiftPowSum (s + 1 + k) ((α + β * x : ℝ) : ℂ)).re := by
  induction k with
  | zero =>
    refine ⟨-s * β, fun x hx => ?_⟩
    have hw : -(1 / 2 : ℝ) < ((α + β * x : ℝ) : ℂ).re := by simp; linarith
    have h := hasDerivAt_re_affine α β (fun v : ℂ => ∑' n : ℕ, eulerTermC s v n)
      (-(s : ℂ) * shiftPowSum (s + 1) ((α + β * x : ℝ) : ℂ)) x
      (hasDerivAt_euler_sum s hs0 hs1 _ hw)
    rw [zero_add, iteratedDeriv_one, h.deriv]
    simp [Complex.mul_re]
    ring
  | succ k ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨c * (-(s + 1 + k) * β), fun x hx => ?_⟩
    have hopen := isOpen_affine_pos α β
    have hev : iteratedDeriv (k + 1) (fun x : ℝ => (∑' n, eulerTermC s ((α + β * x : ℝ) : ℂ) n).re)
        =ᶠ[𝓝 x] fun z => c * (shiftPowSum (s + 1 + k) ((α + β * z : ℝ) : ℂ)).re := by
      filter_upwards [hopen.mem_nhds hx] with z hz using hc z hz
    rw [iteratedDeriv_succ, hev.deriv_eq]
    have hw : -(1 / 2 : ℝ) < ((α + β * x : ℝ) : ℂ).re := by simp; linarith
    have hP := hasDerivAt_shiftPowSum (s + 1 + k) (by linarith [Nat.cast_nonneg (α := ℝ) k])
      ((α + β * x : ℝ) : ℂ) hw
    have h := (hasDerivAt_re_affine α β (shiftPowSum (s + 1 + k))
      (-((s + 1 + k : ℝ) : ℂ) * shiftPowSum (s + 1 + k + 1) ((α + β * x : ℝ) : ℂ)) x hP).const_mul c
    rw [h.deriv, show s + 1 + ((k + 1 : ℕ) : ℝ) = s + 1 + k + 1 by push_cast; ring]
    simp [Complex.mul_re]
    ring

lemma contDiffAt_kernel_pieces (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (n : ℕ) (y : ℝ) (hy0 : 0 < y)
    (hy1 : y < 1) :
    ContDiffAt ℝ n (fun x : ℝ => x ^ (-s)) y ∧
      ContDiffAt ℝ n (fun x : ℝ => (1 - x) ^ (-s)) y ∧
      ContDiffAt ℝ n (fun x : ℝ => (∑' k, eulerTermC s (x : ℂ) k).re) y ∧
      ContDiffAt ℝ n (fun x : ℝ => (∑' k, eulerTermC s ((1 - x : ℝ) : ℂ) k).re) y := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (Real.contDiffAt_rpow_const_of_ne hy0.ne').of_le (by exact_mod_cast le_top)
  · exact ((Real.contDiffAt_rpow_const_of_ne (sub_pos.mpr hy1).ne').comp y
      (contDiffAt_const.sub contDiffAt_id)).of_le (by exact_mod_cast le_top)
  · exact (contDiffAt_euler_remainder s hs0 hs1 y (by linarith)).of_le (by exact_mod_cast le_top)
  · exact ((contDiffAt_euler_remainder s hs0 hs1 (1 - y) (by linarith)).comp y
      (contDiffAt_const.sub contDiffAt_id)).of_le (by exact_mod_cast le_top)

/-- Sum of four smooth pieces: the iterated derivative splits termwise. -/
lemma iteratedDeriv_four (n : ℕ) (f₁ f₂ f₃ f₄ : ℝ → ℝ) (y : ℝ) (h₁ : ContDiffAt ℝ n f₁ y)
    (h₂ : ContDiffAt ℝ n f₂ y) (h₃ : ContDiffAt ℝ n f₃ y) (h₄ : ContDiffAt ℝ n f₄ y) :
    iteratedDeriv n (fun x => f₁ x + f₂ x + f₃ x + f₄ x) y =
      iteratedDeriv n f₁ y + iteratedDeriv n f₂ y + iteratedDeriv n f₃ y +
        iteratedDeriv n f₄ y := by
  have h12 : ContDiffAt ℝ n (fun x => f₁ x + f₂ x) y := h₁.add h₂
  have h123 : ContDiffAt ℝ n (fun x => f₁ x + f₂ x + f₃ x) y := h12.add h₃
  rw [iteratedDeriv_fun_add h123 h₄, iteratedDeriv_fun_add h12 h₃,
    iteratedDeriv_fun_add h₁ h₂]

lemma rpow_half_neg_eq (a : ℝ) : (1 / 2 : ℝ) ^ (-a) = 2 ^ a := by
  rw [one_div, Real.inv_rpow (by norm_num), Real.rpow_neg (by norm_num), inv_inv]

/-- The zeroth derivative on `(0,1/2]`: the kernel is bounded by a multiple of `y ^ (-s)`. -/
lemma bound_unit_zero (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, 0 < y → y ≤ 1 / 2 → |hurwitzKernel s y| ≤ C * y ^ (-s) := by
  set K₀ : ℝ := ∑' n : ℕ, (s + s * 2 ^ (s + 1) * 1) * ((n : ℝ) + 1) ^ (-s - 1) with hK₀
  set c : ℝ := 2 / (1 - s) with hc
  set B : ℝ := 2 ^ s + 2 * K₀ + |c| with hB
  have hcpos : 0 < c := div_pos (by norm_num) (by linarith)
  have hK₀nn : 0 ≤ K₀ := by
    refine tsum_nonneg fun n => ?_
    have : (0 : ℝ) < s + s * 2 ^ (s + 1) * 1 := by positivity
    exact mul_nonneg this.le (Real.rpow_nonneg (by positivity) _)
  have hB0 : 0 ≤ B := by
    have : (0 : ℝ) ≤ 2 ^ s := by positivity
    have := abs_nonneg c
    linarith
  refine ⟨1 + B, by linarith, fun y hy0 hy1 => ?_⟩
  have hy1' : y < 1 := by linarith
  have hK := hurwitzKernel_eq_euler s hs0 hs1 y hy0 hy1'
  have hA : 1 ≤ y ^ (-s) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hy0 hy1'.le (by linarith)
  have hA0 : 0 ≤ y ^ (-s) := Real.rpow_nonneg hy0.le _
  have hB' : (1 - y) ^ (-s) ≤ 2 ^ s := by
    rw [← rpow_half_neg_eq s]
    exact Real.rpow_le_rpow_of_nonpos (by norm_num) (by linarith) (by linarith)
  have hBnn : 0 ≤ (1 - y) ^ (-s) := Real.rpow_nonneg (by linarith) _
  have hw1 : -(1 / 2 : ℝ) < (y : ℂ).re := by simp; linarith
  have hw2 : -(1 / 2 : ℝ) < ((1 - y : ℝ) : ℂ).re := by simp; linarith
  have hR1 : ‖(y : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg hy0.le]; linarith
  have hR2 : ‖((1 - y : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]; linarith
  have hQ1 : |(∑' n, eulerTermC s (y : ℂ) n).re| ≤ K₀ :=
    (Complex.abs_re_le_norm _).trans (norm_eulerSum_le s hs0 hs1 _ hw1 hR1)
  have hQ2 : |(∑' n, eulerTermC s ((1 - y : ℝ) : ℂ) n).re| ≤ K₀ :=
    (Complex.abs_re_le_norm _).trans (norm_eulerSum_le s hs0 hs1 _ hw2 hR2)
  have hq1 := abs_le.mp hQ1
  have hq2 := abs_le.mp hQ2
  have hcabs1 : c ≤ |c| := le_abs_self c
  have hcabs2 : -c ≤ |c| := neg_le_abs c
  have hpow : (0 : ℝ) ≤ 2 ^ s := by positivity
  have hKle : |hurwitzKernel s y| ≤ y ^ (-s) + B := by
    rw [abs_le, hK]
    constructor <;> linarith [hq1.1, hq1.2, hq2.1, hq2.2]
  have hmul : B ≤ B * y ^ (-s) := le_mul_of_one_le_right hB0 hA
  calc |hurwitzKernel s y| ≤ y ^ (-s) + B := hKle
    _ ≤ (1 + B) * y ^ (-s) := by nlinarith

/-- Iterated derivatives of the kernel on `(0,1/2]` for `m ≥ 1`. -/
lemma bound_unit_succ (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, 0 < y → y ≤ 1 / 2 →
      |iteratedDeriv (k + 1) (hurwitzKernel s) y| ≤ C * y ^ (-s - ((k + 1 : ℕ) : ℝ)) := by
  obtain ⟨c₁, hc₁⟩ := iteratedDeriv_affine_rpow (-s) 0 1 (k + 1)
  obtain ⟨c₂, hc₂⟩ := iteratedDeriv_affine_rpow (-s) 1 (-1) (k + 1)
  obtain ⟨c₃, hc₃⟩ := iteratedDeriv_re_affine_euler s hs0 hs1 0 1 k
  obtain ⟨c₄, hc₄⟩ := iteratedDeriv_re_affine_euler s hs0 hs1 1 (-1) k
  simp only [zero_add, one_mul] at hc₁ hc₃
  simp only [neg_mul, one_mul, ← sub_eq_add_neg] at hc₂ hc₄
  set M : ℝ := ∑' n : ℕ, (2 : ℝ) ^ (s + 1 + k) * ((n : ℝ) + 1) ^ (-(s + 1 + k)) with hM
  have hS : ∀ w : ℂ, -(1 / 2 : ℝ) < w.re → |(shiftPowSum (s + 1 + k) w).re| ≤ |M| := by
    intro w hw
    have ha : 1 < s + 1 + k := by linarith [Nat.cast_nonneg (α := ℝ) k]
    exact ((Complex.abs_re_le_norm _).trans (norm_shiftPowSum_le _ ha w hw)).trans (le_abs_self M)
  set Cc : ℝ := |c₁| + |c₂| * 2 ^ (s + ((k + 1 : ℕ) : ℝ)) + (|c₃| + |c₄|) * |M| + 1 with hCc
  refine ⟨Cc, by positivity, fun y hy0 hy1 => ?_⟩
  have hy1' : y < 1 := by linarith
  have hK_ev : hurwitzKernel s =ᶠ[𝓝 y] fun x : ℝ => (x ^ (-s) + (1 - x) ^ (-s) +
      (∑' n, eulerTermC s (x : ℂ) n).re + (∑' n, eulerTermC s ((1 - x : ℝ) : ℂ) n).re) -
        2 / (1 - s) :=
    Filter.eventually_of_mem (Ioo_mem_nhds hy0 hy1') fun x hx => hurwitzKernel_eq_euler s hs0 hs1 x hx.1 hx.2
  have hN : iteratedDeriv (k + 1) (fun x : ℝ => (x ^ (-s) + (1 - x) ^ (-s) +
      (∑' n, eulerTermC s (x : ℂ) n).re + (∑' n, eulerTermC s ((1 - x : ℝ) : ℂ) n).re) -
        2 / (1 - s)) y =
      iteratedDeriv (k + 1) (fun x : ℝ => x ^ (-s)) y +
        iteratedDeriv (k + 1) (fun x : ℝ => (1 - x) ^ (-s)) y +
        iteratedDeriv (k + 1) (fun x : ℝ => (∑' n, eulerTermC s (x : ℂ) n).re) y +
        iteratedDeriv (k + 1) (fun x : ℝ => (∑' n, eulerTermC s ((1 - x : ℝ) : ℂ) n).re) y := by
    obtain ⟨p1, p2, p3, p4⟩ := contDiffAt_kernel_pieces s hs0 hs1 (k + 1) y hy0 hy1'
    have hconst : ContDiffAt ℝ (k + 1) (fun _ : ℝ => 2 / (1 - s)) y := contDiffAt_const
    rw [iteratedDeriv_fun_sub ((p1.add p2).add p3 |>.add p4) hconst, iteratedDeriv_const]
    simp only [Nat.succ_ne_zero, ite_false, sub_zero]
    exact iteratedDeriv_four (k + 1) _ _ _ _ y p1 p2 p3 p4
  have hKeq : iteratedDeriv (k + 1) (hurwitzKernel s) y =
      iteratedDeriv (k + 1) (fun x : ℝ => (x ^ (-s) + (1 - x) ^ (-s) +
        (∑' n, eulerTermC s (x : ℂ) n).re + (∑' n, eulerTermC s ((1 - x : ℝ) : ℂ) n).re) -
          2 / (1 - s)) y :=
    (hK_ev.iteratedDeriv (k + 1)).self_of_nhds
  have hw1 : -(1 / 2 : ℝ) < (y : ℂ).re := by simp; linarith
  have hw2 : -(1 / 2 : ℝ) < ((1 - y : ℝ) : ℂ).re := by simp; linarith
  have hexp : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hY1 : 1 ≤ y ^ (-s - ((k + 1 : ℕ) : ℝ)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hy0 hy1'.le (by linarith)
  have hY0 : 0 ≤ y ^ (-s - ((k + 1 : ℕ) : ℝ)) := Real.rpow_nonneg hy0.le _
  have hZ : (1 - y) ^ (-s - ((k + 1 : ℕ) : ℝ)) ≤ 2 ^ (s + ((k + 1 : ℕ) : ℝ)) := by
    rw [← rpow_half_neg_eq, show -(s + ((k + 1 : ℕ) : ℝ)) = -s - ((k + 1 : ℕ) : ℝ) by ring]
    exact Real.rpow_le_rpow_of_nonpos (by norm_num) (by linarith) (by linarith)
  have hZ0 : 0 ≤ (1 - y) ^ (-s - ((k + 1 : ℕ) : ℝ)) := Real.rpow_nonneg (by linarith) _
  have hS3 := hS (y : ℂ) hw1
  have hS4 := hS ((1 - y : ℝ) : ℂ) hw2
  have e1 := hc₁ y hy0
  have e2 := hc₂ y (by linarith)
  have e3 := hc₃ y hy0
  have e4 := hc₄ y (by linarith)
  rw [hKeq, hN, e1, e2, e3, e4]
  set Y := y ^ (-s - ((k + 1 : ℕ) : ℝ)) with hYdef
  set Z := (1 - y) ^ (-s - ((k + 1 : ℕ) : ℝ)) with hZdef
  set T := |c₂| * 2 ^ (s + ((k + 1 : ℕ) : ℝ)) with hTdef
  set Mm := (|c₃| + |c₄|) * |M| with hMmdef
  have hTnn : 0 ≤ T := by positivity
  have hMmnn : 0 ≤ Mm := by positivity
  have b1 : |c₁ * Y| ≤ |c₁| * Y := by rw [abs_mul, abs_of_nonneg hY0]
  have b2 : |c₂ * Z| ≤ T := by
    rw [abs_mul, abs_of_nonneg hZ0, hTdef]
    exact mul_le_mul_of_nonneg_left hZ (abs_nonneg _)
  have b3 : |c₃ * (shiftPowSum (s + 1 + k) (y : ℂ)).re| ≤ |c₃| * |M| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hS3 (abs_nonneg _)
  have b4 : |c₄ * (shiftPowSum (s + 1 + k) ((1 - y : ℝ) : ℂ)).re| ≤ |c₄| * |M| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hS4 (abs_nonneg _)
  have hT : T ≤ T * Y := le_mul_of_one_le_right hTnn hY1
  have hMm : Mm ≤ Mm * Y := le_mul_of_one_le_right hMmnn hY1
  have hsplit : |c₁| * Y + T + Mm ≤ (|c₁| + T + Mm + 1) * Y := by
    nlinarith
  have hsum : |c₁ * Y + c₂ * Z + c₃ * (shiftPowSum (s + 1 + k) (y : ℂ)).re +
      c₄ * (shiftPowSum (s + 1 + k) ((1 - y : ℝ) : ℂ)).re| ≤ |c₁| * Y + T + Mm := by
    have hb3 : |c₃| * |M| + |c₄| * |M| = Mm := by rw [hMmdef]; ring
    have u1 := abs_le.mp b1
    have u2 := abs_le.mp b2
    have u3 := abs_le.mp b3
    have u4 := abs_le.mp b4
    rw [abs_le]
    constructor <;> linarith [u1.1, u1.2, u2.1, u2.2, u3.1, u3.2, u4.1, u4.2]
  calc _ ≤ |c₁| * Y + T + Mm := hsum
    _ ≤ (|c₁| + T + Mm + 1) * Y := hsplit
    _ = _ := by rw [hCc]

/-- Uniform bound on `(0,1/2]` for every derivative order. -/
lemma bound_unit (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, 0 < y → y ≤ 1 / 2 →
      |iteratedDeriv m (hurwitzKernel s) y| ≤ C * y ^ (-s - (m : ℝ)) := by
  cases m with
  | zero =>
    obtain ⟨C, hC, h⟩ := bound_unit_zero s hs0 hs1
    exact ⟨C, hC, fun y hy0 hy1 => by simpa using h y hy0 hy1⟩
  | succ k => exact bound_unit_succ s hs0 hs1 k

/-- The reflection `x ↦ -x` leaves the modulus of every derivative of the kernel unchanged. -/
lemma abs_iteratedDeriv_neg (s : ℝ) (m : ℕ) (a : ℝ) :
    |iteratedDeriv m (hurwitzKernel s) a| = |iteratedDeriv m (hurwitzKernel s) (-a)| := by
  have hfe : (fun z : ℝ => hurwitzKernel s (-z)) = hurwitzKernel s := by
    funext z
    unfold hurwitzKernel
    congr 1
    exact hurwitzZetaEven_re_even (s : ℂ) z
  have h := iteratedDeriv_comp_neg m (hurwitzKernel s) a
  rw [hfe] at h
  rw [h, smul_eq_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]

/-- Derivative bounds for the kernel (Lemma 2.1): for every `m : ℕ`
there is `C > 0`, chosen before `x`, with `|g^{(m)}(x)| ≤ C * dist (x : UnitAddCircle) 0 ^ (-s - m)`
for every `x` that is not an integer. Here `dist (x : UnitAddCircle) 0` equals `|x - round x|`,
the distance from `x` to the nearest integer (`UnitAddCircle.norm_eq`). -/
theorem iteratedDeriv_hurwitzKernel_bound (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, (x : UnitAddCircle) ≠ 0 →
      |iteratedDeriv m (hurwitzKernel s) x| ≤ C * dist (x : UnitAddCircle) 0 ^ (-s - (m : ℝ)) := by
  obtain ⟨C, hC, hbound⟩ := bound_unit s hs0 hs1 m
  refine ⟨C, hC, fun x hx => ?_⟩
  set t : ℝ := x - (round x : ℝ) with ht
  have hdist : dist (x : UnitAddCircle) 0 = |t| := by
    rw [dist_zero_right, UnitAddCircle.norm_eq]
  have ht_ne : t ≠ 0 := by
    intro h0
    apply hx
    have hxn : x = (round x : ℝ) := by linarith
    rw [hxn]
    exact (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨round x, by simp⟩
  have ht_le : |t| ≤ 1 / 2 := abs_sub_round x
  have hpos : 0 < |t| := abs_pos.mpr ht_ne
  -- Periodicity moves `x` to `t`.
  have hper : iteratedDeriv m (hurwitzKernel s) x = iteratedDeriv m (hurwitzKernel s) t := by
    have hfun : (fun z : ℝ => hurwitzKernel s (z + -(round x : ℝ))) = hurwitzKernel s := by
      funext z
      rw [← sub_eq_add_neg]
      exact hurwitzKernel_sub_int s (round x) z
    have h := iteratedDeriv_comp_add_const (n := m) (f := hurwitzKernel s) (s := -(round x : ℝ))
    rw [hfun] at h
    have h1 := congrFun h x
    rw [← sub_eq_add_neg] at h1
    exact h1
  -- Evenness moves the representative `t` to its modulus `|t|` in `(0, 1/2]`.
  have hmod : |iteratedDeriv m (hurwitzKernel s) t| =
      |iteratedDeriv m (hurwitzKernel s) (|t|)| := by
    rcases le_or_gt 0 t with h0 | h0
    · rw [abs_of_nonneg h0]
    · rw [abs_of_neg h0]
      exact abs_iteratedDeriv_neg s m t
  rw [hdist, hper, hmod]
  exact hbound |t| hpos ht_le

end Riesz1
