/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Kernel.PeriodicZetaIdentity
public import Riesz1.Frozen.PeriodicZeta
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Basic.Real.Sign

/-!
# The periodic zeta combination `V_s`: regularity, asymptotics and concavity

For `0 < s < 1`, `periodicZeta s` is the function `V_s`.
On `(0, 1)` it equals `Re ζ(-s, t) + Re ζ(-s, 1 - t) - 2 Re ζ(-s, 1)`, where `ζ` is the Hurwitz
zeta function of `PeriodicZetaIdentity`. This file proves: continuity, evenness, periodicity
and smoothness on `(0, 1)`, the expansion `|V_s(t) - t^s| ≤ C t²` near zero, and strict
positivity and strict concavity on `(0, 1)`.

It also proves the properties of the periodic kernel `K_s`: `V_s' = s K_s` off the
integers, integrability over a period with mean zero, and convergence of the symmetric partial
sums `∑_{k=-M}^{M} sign(t - k)|t - k|^(s-1)` to `K_s(t)` off the integers.
-/

public section

open Complex Set Filter Topology MeasureTheory
open scoped ContDiff
namespace Riesz1

/-- The point `1` of the circle is the origin. -/
lemma coe_one_real_eq_zero : ((1 : ℝ) : UnitAddCircle) = 0 :=
  AddCircle.coe_period 1

/-- The reflected point: `-t` and `1 - t` have the same image on the unit circle. -/
lemma coe_one_sub_real (t : ℝ) : ((1 - t : ℝ) : UnitAddCircle) = -(t : UnitAddCircle) := by
  rw [show (1 - t : ℝ) = -t + 1 by ring, AddCircle.coe_add, coe_one_real_eq_zero, add_zero,
    AddCircle.coe_neg]

/-- The periodic zeta combination in terms of the real parts of the Hurwitz zeta function at the
points `t`, `1 - t` and `1`. -/
theorem periodicZeta_eq_re (s : RieszExponent) (t : ℝ) :
    periodicZeta s (t : UnitAddCircle) =
      (hurwitzAt t (-(s.val : ℂ))).re + (hurwitzAt (1 - t) (-(s.val : ℂ))).re -
        2 * (hurwitzAt 1 (-(s.val : ℂ))).re := by
  unfold periodicZeta hurwitzAt
  rw [HurwitzZeta.hurwitzZetaEven_eq, HurwitzZeta.hurwitzZetaEven_eq, neg_zero,
    coe_one_sub_real, coe_one_real_eq_zero]
  simp only [Complex.div_ofNat_re, Complex.add_re]
  ring

/-- The value at the origin vanishes. -/
theorem periodicZeta_zero_point (s : RieszExponent) : periodicZeta s 0 = 0 := by
  unfold periodicZeta
  simp

/-- The periodic zeta combination is even. -/
theorem periodicZeta_neg (s : RieszExponent) (t : ℝ) :
    periodicZeta s ((-t : ℝ) : UnitAddCircle) = periodicZeta s (t : UnitAddCircle) := by
  unfold periodicZeta
  rw [AddCircle.coe_neg, HurwitzZeta.hurwitzZetaEven_neg]

/-- The periodic zeta combination is invariant under integer translations. -/
theorem periodicZeta_add_int (s : RieszExponent) (t : ℝ) (k : ℤ) :
    periodicZeta s ((t + k : ℝ) : UnitAddCircle) = periodicZeta s (t : UnitAddCircle) := by
  have hk : ((k : ℝ) : UnitAddCircle) = 0 :=
    (AddCircle.coe_eq_zero_iff _).mpr ⟨k, by simp⟩
  rw [AddCircle.coe_add, hk, add_zero]

/-- The real-valued combination `Re ζ(-σ, v) + Re ζ(-σ, 1 - v) - 2 Re ζ(-σ, 1)`, which equals
`periodicZeta` at `v` by `periodicZeta_eq_re`. -/
@[expose] noncomputable def periodicZetaRe (σ : ℝ) (v : ℝ) : ℝ :=
  (hurwitzAt v (-(σ : ℂ))).re + (hurwitzAt (1 - v) (-(σ : ℂ))).re -
    2 * (hurwitzAt 1 (-(σ : ℂ))).re

/-- The combination `periodicZetaRe` is the periodic zeta combination. -/
lemma periodicZeta_eq_periodicZetaRe (s : RieszExponent) (v : ℝ) :
    periodicZeta s (v : UnitAddCircle) = periodicZetaRe s.val v :=
  periodicZeta_eq_re s v

/-- The real part of a function with a complex derivative has the real part of the derivative. -/
lemma hasDerivAt_re_of_hasDerivAt {f : ℝ → ℂ} {f' : ℂ} {t : ℝ} (h : HasDerivAt f f' t) :
    HasDerivAt (fun v => (f v).re) f'.re t :=
  Complex.reCLM.hasFDerivAt.comp_hasDerivAt t h

/-- Chain rule for the reflection `v ↦ 1 - v` in the Hurwitz point. -/
lemma hasDerivAt_hurwitzAt_one_sub {w d : ℂ} {t : ℝ}
    (h : HasDerivAt (fun u : ℝ => hurwitzAt u w) d (1 - t)) :
    HasDerivAt (fun v : ℝ => hurwitzAt (1 - v) w) (-d) t := by
  have hc : HasDerivAt (fun v : ℝ => 1 - v) (-1) t := (hasDerivAt_id t).const_sub 1
  have h2 : HasDerivAt (fun v : ℝ => hurwitzAt (1 - v) w) ((-1 : ℝ) • d) t := h.scomp t hc
  rwa [neg_one_smul] at h2

/-- The derivative of `v ↦ ζ(-σ, v)` on `(0, 1)`: `∂_v ζ(-σ, v) = σ ζ(1 - σ, v)`. -/
lemma hasDerivAt_hurwitzAt_neg {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) {t : ℝ} (ht0 : 0 < t)
    (ht1 : t < 1) :
    HasDerivAt (fun v : ℝ => hurwitzAt v (-(σ : ℂ))) ((σ : ℂ) * hurwitzAt t (1 - σ)) t := by
  have hw0 : -(σ : ℂ) ≠ 0 := neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr hσ0.ne')
  have h := hasDerivAt_hurwitzAt_of_re_gt ht0 ht1 (w := -(σ : ℂ))
    (by simp only [neg_re, ofReal_re]; linarith) (by simp only [neg_re, ofReal_re]; linarith) hw0
  have e1 : -(-(σ : ℂ)) = (σ : ℂ) := by ring
  have e2 : -(σ : ℂ) + 1 = 1 - σ := by ring
  rw [e1, e2] at h
  exact h

/-- The derivative of `periodicZetaRe σ` on `(0, 1)`: `σ (Re ζ(1-σ, t) - Re ζ(1-σ, 1 - t))`. -/
lemma hasDerivAt_periodicZetaRe {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) {t : ℝ} (ht0 : 0 < t)
    (ht1 : t < 1) :
    HasDerivAt (periodicZetaRe σ)
      (σ * (hurwitzAt t (1 - σ)).re - σ * (hurwitzAt (1 - t) (1 - σ)).re) t := by
  have hA := hasDerivAt_re_of_hasDerivAt (hasDerivAt_hurwitzAt_neg hσ0 hσ1 ht0 ht1)
  have hB := hasDerivAt_re_of_hasDerivAt
    (hasDerivAt_hurwitzAt_one_sub (hasDerivAt_hurwitzAt_neg hσ0 hσ1 (t := 1 - t)
      (by linarith) (by linarith)))
  have hC := (hA.add hB).sub_const (2 * (hurwitzAt 1 (-(σ : ℂ))).re)
  have hfun : periodicZetaRe σ = fun v : ℝ =>
      (hurwitzAt v (-(σ : ℂ))).re + (hurwitzAt (1 - v) (-(σ : ℂ))).re -
        2 * (hurwitzAt 1 (-(σ : ℂ))).re := rfl
  rw [hfun]
  convert hC using 1
  simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero]
  ring

/-- The Hurwitz zeta function at a real exponent `r > 1` and a point `u ∈ (0, 1]` has positive real
part: it is a series of positive real terms. -/
lemma re_hurwitzAt_pos {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1) {r : ℝ} (hr : 1 < r) :
    0 < (hurwitzAt u (r : ℂ)).re := by
  have hre : 1 < ((r : ℂ)).re := by simpa using hr
  have hS := Complex.hasSum_re (hasSum_hurwitzAt hu0.le hu1 hre)
  have hterm : ∀ n : ℕ, (((n : ℂ) + u) ^ (-(r : ℂ))).re = ((n : ℝ) + u) ^ (-r) := by
    intro n
    have hbase : ((n : ℂ) + u) = (((n : ℝ) + u : ℝ) : ℂ) := by push_cast; ring
    rw [hbase, show -(r : ℂ) = ((-r : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow (by positivity)]
    simp
  have hpos : ∀ n : ℕ, 0 < (((n : ℂ) + u) ^ (-(r : ℂ))).re := fun n => by
    rw [hterm n]
    exact Real.rpow_pos_of_pos (by positivity) _
  have hsum : Summable (fun n : ℕ => (((n : ℂ) + u) ^ (-(r : ℂ))).re) := hS.summable
  have htsum : ∑' n : ℕ, (((n : ℂ) + u) ^ (-(r : ℂ))).re = (hurwitzAt u (r : ℂ)).re :=
    hS.tsum_eq
  rw [← htsum]
  exact hsum.tsum_pos (fun n => (hpos n).le) 0 (hpos 0)

/-- The second derivative of `periodicZetaRe σ` on `(0, 1)`:
`-σ(1 - σ) (Re ζ(2 - σ, t) + Re ζ(2 - σ, 1 - t))`. -/
lemma hasDerivAt_deriv_periodicZetaRe {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) {t : ℝ} (ht0 : 0 < t)
    (ht1 : t < 1) :
    HasDerivAt (deriv (periodicZetaRe σ))
      (-(σ * (1 - σ)) * ((hurwitzAt t (2 - σ)).re + (hurwitzAt (1 - t) (2 - σ)).re)) t := by
  have hev : deriv (periodicZetaRe σ) =ᶠ[𝓝 t] fun v : ℝ =>
      σ * (hurwitzAt v (1 - σ)).re - σ * (hurwitzAt (1 - v) (1 - σ)).re := by
    filter_upwards [Ioo_mem_nhds ht0 ht1] with v hv
    exact (hasDerivAt_periodicZetaRe hσ0 hσ1 hv.1 hv.2).deriv
  have hw0 : (1 - (σ : ℂ)) ≠ 0 := by
    intro h
    have : (σ : ℂ) = 1 := by linear_combination -h
    have h1 : σ = 1 := by exact_mod_cast this
    linarith
  have hre1 : -1 < ((1 : ℂ) - σ).re := by simp; linarith
  have hre2 : ((1 : ℂ) - σ).re < 1 := by simp; linarith
  have hZ : ∀ u : ℝ, 0 < u → u < 1 → HasDerivAt (fun v : ℝ => hurwitzAt v (1 - σ))
      (-(1 - (σ : ℂ)) * hurwitzAt u (2 - σ)) u := by
    intro u hu0 hu1
    have h := hasDerivAt_hurwitzAt_of_re_gt hu0 hu1 hre1 hre2 hw0
    have e : (1 - (σ : ℂ)) + 1 = 2 - σ := by ring
    rw [e] at h
    exact h
  have hA := hasDerivAt_re_of_hasDerivAt (hZ t ht0 ht1)
  have hB := hasDerivAt_re_of_hasDerivAt (hasDerivAt_hurwitzAt_one_sub
    (hZ (1 - t) (by linarith) (by linarith)))
  have hC := (hA.const_mul σ).sub (hB.const_mul σ)
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  convert hC using 1
  simp only [Complex.mul_re, Complex.neg_re, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, neg_mul, Complex.neg_re, mul_neg, sub_neg_eq_add]
  ring

/-- The Euler sum `∑ₙ eulerTerm x v n` at the point `x`. -/
@[expose] noncomputable def eulerSum (x : ℝ) (v : ℂ) : ℂ :=
  ∑' n : ℕ, eulerTerm x v n

/-- Each Euler term is Lipschitz on `[0, 1]`, with the factor given by its derivative bound. -/
lemma eulerTerm_sub_le (v : ℂ) (hv : 0 < v.re) (n : ℕ) {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
    (hy : y ∈ Icc (0 : ℝ) 1) :
    ‖eulerTerm y v n - eulerTerm x v n‖ ≤ (‖v‖ * ((n : ℝ) + 1) ^ (-v.re - 1)) * |y - x| := by
  have hder : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivWithinAt (fun u : ℝ => eulerTerm u v n)
      (-v * ((n : ℂ) + 1 + (u : ℂ)) ^ (-v - 1)) (Icc (0 : ℝ) 1) u := fun u hu =>
    (hasDerivAt_eulerTerm_real v n (by linarith [hu.1, Nat.cast_nonneg (α := ℝ) n])).hasDerivWithinAt
  have hb : ∀ u ∈ Icc (0 : ℝ) 1, ‖-v * ((n : ℂ) + 1 + (u : ℂ)) ^ (-v - 1)‖ ≤
      ‖v‖ * ((n : ℝ) + 1) ^ (-v.re - 1) := fun u hu => norm_eulerTerm_deriv_le v hv n hu.1
  have key := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hder hb (convex_Icc 0 1) hx hy
  rw [Real.norm_eq_abs] at key
  simpa [mul_comm] using key

/-- The Euler sum is Lipschitz on `[0, 1]`. -/
lemma eulerSum_sub_le {v : ℂ} (hv : 0 < v.re) (hv1 : v ≠ 1) {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
    (hy : y ∈ Icc (0 : ℝ) 1) :
    ‖eulerSum y v - eulerSum x v‖ ≤
      (∑' n : ℕ, ‖v‖ * ((n : ℝ) + 1) ^ (-v.re - 1)) * |y - x| := by
  have hsum : Summable (fun n : ℕ => ‖v‖ * ((n : ℝ) + 1) ^ (-v.re - 1)) :=
    Summable.mul_left _ ((summable_rpow_shift (a := v.re + 1) (by linarith)).congr
      (fun n => by congr 1; ring))
  have hs : Summable (fun n : ℕ => eulerTerm y v n - eulerTerm x v n) :=
    (summable_eulerTerm y hy.1 hy.2 v hv hv1).sub (summable_eulerTerm x hx.1 hx.2 v hv hv1)
  have hbound : ∀ n : ℕ, ‖eulerTerm y v n - eulerTerm x v n‖ ≤
      (‖v‖ * ((n : ℝ) + 1) ^ (-v.re - 1)) * |y - x| := fun n => eulerTerm_sub_le v hv n hx hy
  have hnorm : Summable (fun n : ℕ => ‖eulerTerm y v n - eulerTerm x v n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hbound (hsum.mul_right _)
  unfold eulerSum
  rw [← (summable_eulerTerm y hy.1 hy.2 v hv hv1).tsum_sub
    (summable_eulerTerm x hx.1 hx.2 v hv hv1)]
  calc ‖∑' n : ℕ, (eulerTerm y v n - eulerTerm x v n)‖
      ≤ ∑' n : ℕ, ‖eulerTerm y v n - eulerTerm x v n‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' n : ℕ, (‖v‖ * ((n : ℝ) + 1) ^ (-v.re - 1)) * |y - x| :=
        hnorm.tsum_le_tsum hbound (hsum.mul_right _)
    _ = (∑' n : ℕ, ‖v‖ * ((n : ℝ) + 1) ^ (-v.re - 1)) * |y - x| := tsum_mul_right

/-- The telescoping identity `eulerSum 0 v - eulerSum 1 v = 1` for `Re v > 0`. -/
lemma eulerSum_zero_sub_one {v : ℂ} (hv : 0 < v.re) (hv1 : v ≠ 1) :
    eulerSum 0 v - eulerSum 1 v = 1 := by
  have hterm : ∀ n : ℕ, eulerTerm 0 v n - eulerTerm 1 v n =
      -(((n : ℂ) + 2) ^ (-v) - ((n : ℂ) + 1) ^ (-v)) := by
    intro n
    simp only [eulerTerm, Complex.ofReal_zero, Complex.ofReal_one, add_zero]
    ring_nf
  have hfun : (fun n : ℕ => eulerTerm 0 v n - eulerTerm 1 v n) =
      fun n : ℕ => -(((n : ℂ) + 2) ^ (-v) - ((n : ℂ) + 1) ^ (-v)) := funext hterm
  unfold eulerSum
  rw [← (summable_eulerTerm 0 le_rfl zero_le_one v hv hv1).tsum_sub
    (summable_eulerTerm 1 zero_le_one le_rfl v hv hv1), hfun, tsum_neg,
    (hasSum_telescope_cpow hv).tsum_eq]
  norm_num

/-- The power `u ↦ u^(σ - 1)` is close to `1` near `u = 1`: for `t ∈ [0, 1/2]`,
`|(1 - t)^(σ - 1) - 1| ≤ (1 - σ) (1/2)^(σ - 2) t`. -/
lemma abs_rpow_one_sub_sub_one_le {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1 / 2) :
    |(1 - t) ^ (σ - 1) - 1| ≤ (1 - σ) * (1 / 2 : ℝ) ^ (σ - 2) * t := by
  have hder : ∀ u ∈ Icc (1 / 2 : ℝ) 1, HasDerivWithinAt (fun u : ℝ => u ^ (σ - 1))
      ((σ - 1) * u ^ (σ - 1 - 1)) (Icc (1 / 2 : ℝ) 1) u := by
    intro u hu
    exact (Real.hasDerivAt_rpow_const (Or.inl (by linarith [hu.1]))).hasDerivWithinAt
  have hb : ∀ u ∈ Icc (1 / 2 : ℝ) 1, ‖(σ - 1) * u ^ (σ - 1 - 1)‖ ≤ (1 - σ) * (1 / 2 : ℝ) ^ (σ - 2) := by
    intro u hu
    have hu0 : 0 < u := by linarith [hu.1]
    have hpow : u ^ (σ - 1 - 1) ≤ (1 / 2 : ℝ) ^ (σ - 1 - 1) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) hu.1 (by linarith)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hu0.le _),
      abs_of_neg (by linarith : σ - 1 < 0)]
    have e : σ - 1 - 1 = σ - 2 := by ring
    rw [e] at hpow ⊢
    nlinarith [Real.rpow_nonneg hu0.le (σ - 2)]
  have key := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hder hb (convex_Icc _ _)
    (show (1 - t) ∈ Icc (1 / 2 : ℝ) 1 by constructor <;> linarith)
    (show (1 : ℝ) ∈ Icc (1 / 2 : ℝ) 1 by norm_num)
  simp only [Real.one_rpow] at key
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - (1 - t)),
    show (1 - (1 - t) : ℝ) = t by ring] at key
  have hpos : 0 ≤ (1 - σ) * (1 / 2 : ℝ) ^ (σ - 2) := by
    have := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) (σ - 2)
    nlinarith
  rw [abs_sub_comm] at key
  calc |(1 - t) ^ (σ - 1) - 1| ≤ (1 - σ) * (1 / 2 : ℝ) ^ (σ - 2) * t := by
        convert key using 1

/-- The series `∑ₙ hurwitzDiffTerm t (-σ) n` at the exponent `-σ`. -/
@[expose] noncomputable def hurwitzDiffSum (σ t : ℝ) : ℂ :=
  ∑' n : ℕ, hurwitzDiffTerm t (-(σ : ℂ)) n

/-- The real remainder `ψ(t) = (1 - t)^σ - 1 + Re(T(t) + T(1 - t) - 2 T(1))`, where
`T = hurwitzDiffSum σ`. On `(0, 1)`, `periodicZetaRe σ t = t^σ + ψ(t)`. -/
@[expose] noncomputable def psiFun (σ t : ℝ) : ℝ :=
  (1 - t) ^ σ - 1 + (hurwitzDiffSum σ t + hurwitzDiffSum σ (1 - t) - 2 * hurwitzDiffSum σ 1).re

/-- The norm bound on the terms of `hurwitzDiffTerm`, summable for `-1 < Re w`. -/
lemma summable_hurwitzDiff_bound {w : ℂ} (hw : -1 < w.re) :
    Summable (fun n : ℕ => ‖w‖ * (‖w + 1‖ * ((n : ℝ) + 1) ^ (-w.re - 2))) := by
  have h := summable_rpow_shift (a := w.re + 2) (by linarith)
  refine Summable.mul_left _ (Summable.mul_left _ (h.congr (fun n => ?_)))
  congr 1
  ring

/-- The two points `0` and `1` give the same shifted term. -/
lemma hurwitzDiffTerm_zero_eq_one (w : ℂ) (n : ℕ) :
    hurwitzDiffTerm 0 w n = hurwitzDiffTerm 1 w n := by
  unfold hurwitzDiffTerm
  simp only [Complex.ofReal_zero, Complex.ofReal_one, add_zero]
  ring_nf

/-- The shifted series takes the same value at `0` and `1`. -/
lemma hurwitzDiffSum_zero_eq_one (σ : ℝ) : hurwitzDiffSum σ 0 = hurwitzDiffSum σ 1 := by
  unfold hurwitzDiffSum
  congr 1
  funext n
  exact hurwitzDiffTerm_zero_eq_one _ n

/-- The shifted series is continuous on `[0, 1]`, by uniform convergence of the terms. -/
lemma continuousOn_hurwitzDiffSum {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    ContinuousOn (fun t : ℝ => hurwitzDiffSum σ t) (Icc 0 1) := by
  have hw : -1 < (-(σ : ℂ)).re := by simp only [neg_re, ofReal_re]; linarith
  have hw0 : -(σ : ℂ) ≠ 0 := neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr hσ0.ne')
  unfold hurwitzDiffSum
  refine continuousOn_tsum (fun n => ?_) (summable_hurwitzDiff_bound hw) (fun n t ht => ?_)
  · intro t ht
    exact (hasDerivAt_hurwitzDiffTerm hw0 n ht.1).continuousAt.continuousWithinAt
  · refine (norm_hurwitzDiffTerm_le hw ht.1 ht.2 n).trans ?_
    refine mul_le_of_le_one_left (by positivity) ?_
    rw [abs_le]
    constructor <;> linarith [ht.1, ht.2]

/-- For `t ∈ (0, 1)`, the Hurwitz values at `t`, `1 - t` and `1` give `periodicZetaRe`. -/
lemma periodicZetaRe_eq_rpow_add_psiFun {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) {t : ℝ} (ht0 : 0 < t)
    (ht1 : t < 1) : periodicZetaRe σ t = t ^ σ + psiFun σ t := by
  have hw : -1 < (-(σ : ℂ)).re := by simp only [neg_re, ofReal_re]; linarith
  have hw' : (-(σ : ℂ)).re < 1 := by simp only [neg_re, ofReal_re]; linarith
  have h1 := hurwitzAt_sub_eq_hurwitzDiff ht0 ht1.le hw hw' (t := t)
  have h2 := hurwitzAt_sub_eq_hurwitzDiff (show (0 : ℝ) < 1 - t by linarith)
    (show 1 - t ≤ 1 by linarith) hw hw'
  have h3 := hurwitzAt_sub_eq_hurwitzDiff (show (0 : ℝ) < 1 by norm_num) le_rfl hw hw'
  unfold hurwitzDiff at h1 h2 h3
  simp only [Complex.ofReal_one, Complex.one_cpow] at h3
  have hpow1 : (t : ℂ) ^ (-(-(σ : ℂ))) = ((t ^ σ : ℝ) : ℂ) := by
    rw [neg_neg, Complex.ofReal_cpow ht0.le]
  have hpow2 : ((1 - t : ℝ) : ℂ) ^ (-(-(σ : ℂ))) = (((1 - t) ^ σ : ℝ) : ℂ) := by
    rw [neg_neg, Complex.ofReal_cpow (by linarith)]
  have hc : hurwitzAt t (-(σ : ℂ)) + hurwitzAt (1 - t) (-(σ : ℂ)) - 2 * hurwitzAt 1 (-(σ : ℂ)) =
      ((t ^ σ : ℝ) : ℂ) + (((1 - t) ^ σ : ℝ) : ℂ) - 1 + hurwitzDiffSum σ t +
        hurwitzDiffSum σ (1 - t) - 2 * hurwitzDiffSum σ 1 := by
    have hcast : ((1 - t : ℝ) : ℂ) = 1 - (t : ℂ) := by push_cast; ring
    unfold hurwitzDiffSum
    rw [← hpow1, ← hpow2]
    linear_combination h1 + h2 - 2 * h3 - hcast
  have hre := congrArg Complex.re hc
  unfold periodicZetaRe psiFun
  unfold hurwitzDiffSum at *
  simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.one_re,
    Complex.re_ofNat, Complex.im_ofNat] at hre
  simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.re_ofNat,
    Complex.im_ofNat]
  linarith

/-- The derivative of the shifted series: `∂_t T(t) = σ S₁(t)`, where `S₁ = eulerSum · (1 - σ)`. -/
lemma hasDerivAt_hurwitzDiffSum {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) {t : ℝ} (ht0 : 0 < t)
    (ht1 : t < 1) :
    HasDerivAt (fun v : ℝ => hurwitzDiffSum σ v) ((σ : ℂ) * eulerSum t (1 - σ)) t := by
  have hw0 : -(σ : ℂ) ≠ 0 := neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr hσ0.ne')
  have hw : -1 < (-(σ : ℂ)).re := by simp only [neg_re, ofReal_re]; linarith
  have hD := hasDerivAt_hurwitzDiff ht0 ht1 hw hw0
  have hPow : HasDerivAt (fun v : ℝ => (v : ℂ) ^ (-(-(σ : ℂ))))
      (-(-(σ : ℂ)) * (t : ℂ) ^ (-(-(σ : ℂ)) - 1)) t :=
    hasDerivAt_ofReal_cpow_const ht0.ne' (neg_ne_zero.mpr hw0)
  have hLin : HasDerivAt (fun v : ℝ => (v : ℂ) - ((1 / 2 : ℝ) : ℂ)) 1 t := by
    have h := ((hasDerivAt_id' t).ofReal_comp).sub_const (((1 / 2 : ℝ) : ℂ))
    simpa only [Complex.ofReal_one] using h
  have hC := hD.sub (((hPow.sub_const (((1 / 2 : ℝ) : ℂ) ^ (-(-(σ : ℂ))))).sub hLin))
  have hfun : (fun v : ℝ => hurwitzDiffSum σ v) = fun v : ℝ =>
      hurwitzDiff v (-(σ : ℂ)) - ((v : ℂ) ^ (-(-(σ : ℂ))) -
        ((1 / 2 : ℝ) : ℂ) ^ (-(-(σ : ℂ))) - ((v : ℂ) - ((1 / 2 : ℝ) : ℂ))) := by
    funext v
    unfold hurwitzDiff hurwitzDiffSum
    ring
  rw [hfun]
  refine HasDerivAt.congr_deriv hC ?_
  have hre : 0 < (-(σ : ℂ) + 1).re := by simp only [add_re, neg_re, ofReal_re, one_re]; linarith
  have hne : -(σ : ℂ) + 1 ≠ 1 := fun h => hw0 (by linear_combination h)
  have hA : hurwitzAt t (-(σ : ℂ) + 1) = (t : ℂ) ^ (-(-(σ : ℂ) + 1)) +
      ∑' n : ℕ, eulerTerm t (-(σ : ℂ) + 1) n - 1 / (1 - (-(σ : ℂ) + 1)) :=
    (euler_eq_hurwitzZeta t ht0 ht1.le _ hre hne).symm
  have e1 : -(-(σ : ℂ) + 1) = -(-(σ : ℂ)) - 1 := by ring
  have e2 : (1 : ℂ) - (-(σ : ℂ) + 1) = σ := by ring
  have e3 : (1 : ℂ) - (σ : ℂ) = -(σ : ℂ) + 1 := by ring
  have hσc : (σ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hσ0.ne'
  rw [e3, hA, e1, e2]
  unfold eulerSum
  field_simp
  ring

/-- Chain rule for the reflection `v ↦ 1 - v` at a general complex-valued function. -/
lemma hasDerivAt_comp_one_sub_general {g : ℝ → ℂ} {d : ℂ} {t : ℝ}
    (h : HasDerivAt g d (1 - t)) : HasDerivAt (fun v : ℝ => g (1 - v)) (-d) t := by
  have hc : HasDerivAt (fun v : ℝ => 1 - v) (-1) t := (hasDerivAt_id' t).const_sub 1
  have h2 : HasDerivAt (fun v : ℝ => g (1 - v)) ((-1 : ℝ) • d) t := h.scomp t hc
  rwa [neg_one_smul] at h2

/-- The derivative of `ψ` on `(0, 1)`: the power `(1 - t)^σ` and the real parts of the shifted
series `T(t)` and `T(1 - t)`. -/
lemma hasDerivAt_psiFun {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) {t : ℝ} (ht0 : 0 < t)
    (ht1 : t < 1) :
    HasDerivAt (psiFun σ) (-σ * (1 - t) ^ (σ - 1) + σ * (eulerSum t (1 - σ)).re -
      σ * (eulerSum (1 - t) (1 - σ)).re) t := by
  have hne : (1 : ℝ) - t ≠ 0 := (by linarith : (0 : ℝ) < 1 - t).ne'
  have hA : HasDerivAt (fun v : ℝ => (1 - v) ^ σ) ((-1) * σ * (1 - t) ^ (σ - 1)) t := by
    have h := ((hasDerivAt_id' t).const_sub 1).rpow_const (p := σ) (Or.inl hne)
    simpa using h
  have hD1 : HasDerivAt (fun v : ℝ => hurwitzDiffSum σ v) ((σ : ℂ) * eulerSum t (1 - σ)) t :=
    hasDerivAt_hurwitzDiffSum hσ0 hσ1 ht0 ht1
  have hD2 : HasDerivAt (fun v : ℝ => hurwitzDiffSum σ (1 - v))
      (-((σ : ℂ) * eulerSum (1 - t) (1 - σ))) t :=
    hasDerivAt_comp_one_sub_general (hasDerivAt_hurwitzDiffSum hσ0 hσ1 (t := 1 - t)
      (by linarith) (by linarith))
  have hcomp := (hD1.add hD2).sub_const (2 * hurwitzDiffSum σ 1)
  have hre := hasDerivAt_re_of_hasDerivAt hcomp
  have hsum := (hA.sub_const 1).add hre
  have hfun : psiFun σ = fun v : ℝ => ((1 - v) ^ σ - 1) +
      (hurwitzDiffSum σ v + hurwitzDiffSum σ (1 - v) - 2 * hurwitzDiffSum σ 1).re := rfl
  rw [hfun]
  refine hsum.congr_deriv ?_
  simp only [Complex.add_re, Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  ring

/-- The key bound on the derivative of `ψ`: for `0 < t ≤ 1/2`, `|ψ'(t)| ≤ C t`, with
`C = σ (2 L + (1 - σ)(1/2)^(σ-2))` and `L` a Lipschitz bound for `eulerSum · (1 - σ)`. -/
lemma abs_deriv_psiFun_le {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) {t : ℝ} (ht0 : 0 < t)
    (ht1 : t ≤ 1 / 2) :
    |-σ * (1 - t) ^ (σ - 1) + σ * (eulerSum t (1 - σ)).re - σ * (eulerSum (1 - t) (1 - σ)).re| ≤
      σ * (2 * (∑' n : ℕ, ‖(1 - (σ : ℂ))‖ * ((n : ℝ) + 1) ^ (-(1 - (σ : ℂ)).re - 1)) +
        (1 - σ) * (1 / 2 : ℝ) ^ (σ - 2)) * t := by
  have hv0 : 0 < (1 - (σ : ℂ)).re := by simp only [sub_re, one_re, ofReal_re]; linarith
  have hv1 : (1 - (σ : ℂ)) ≠ 1 := by
    intro h
    have h' := congrArg Complex.re h
    simp only [sub_re, one_re, ofReal_re] at h'
    linarith
  have hS0 := eulerSum_zero_sub_one hv0 hv1
  have hA := eulerSum_sub_le hv0 hv1 (x := 0) (y := t) ⟨le_rfl, zero_le_one⟩
    ⟨ht0.le, by linarith⟩
  have hB := eulerSum_sub_le hv0 hv1 (x := 1) (y := 1 - t) ⟨zero_le_one, le_rfl⟩
    ⟨by linarith, by linarith⟩
  have hC := abs_rpow_one_sub_sub_one_le hσ0 hσ1 ht0.le ht1
  have hr : (eulerSum 0 (1 - (σ : ℂ))).re - (eulerSum 1 (1 - (σ : ℂ))).re = 1 := by
    have := congrArg Complex.re hS0
    simpa only [Complex.sub_re, Complex.one_re] using this
  rw [sub_zero, abs_of_pos ht0] at hA
  rw [show (1 - t - 1 : ℝ) = -t by ring, abs_neg, abs_of_pos ht0] at hB
  set L := ∑' n : ℕ, ‖(1 - (σ : ℂ))‖ * ((n : ℝ) + 1) ^ (-(1 - (σ : ℂ)).re - 1) with hLdef
  set Cp := (1 - σ) * (1 / 2 : ℝ) ^ (σ - 2) with hCp
  have hX : -σ * (1 - t) ^ (σ - 1) + σ * (eulerSum t (1 - σ)).re - σ * (eulerSum (1 - t) (1 - σ)).re =
      σ * (((eulerSum t (1 - σ) - eulerSum 0 (1 - σ)).re - (eulerSum (1 - t) (1 - σ) -
        eulerSum 1 (1 - σ)).re) - ((1 - t) ^ (σ - 1) - 1)) := by
    simp only [Complex.sub_re]
    linear_combination σ * hr
  rw [hX, abs_mul, abs_of_pos hσ0]
  have hre1 : |(eulerSum t (1 - σ) - eulerSum 0 (1 - σ)).re| ≤ L * t :=
    (Complex.abs_re_le_norm _).trans hA
  have hre2 : |(eulerSum (1 - t) (1 - σ) - eulerSum 1 (1 - σ)).re| ≤ L * t :=
    (Complex.abs_re_le_norm _).trans hB
  have hsub := abs_sub ((eulerSum t (1 - σ) - eulerSum 0 (1 - σ)).re -
    (eulerSum (1 - t) (1 - σ) - eulerSum 1 (1 - σ)).re) ((1 - t) ^ (σ - 1) - 1)
  have htri := abs_sub ((eulerSum t (1 - σ) - eulerSum 0 (1 - σ)).re)
    ((eulerSum (1 - t) (1 - σ) - eulerSum 1 (1 - σ)).re)
  have key : |((eulerSum t (1 - σ) - eulerSum 0 (1 - σ)).re - (eulerSum (1 - t) (1 - σ) -
      eulerSum 1 (1 - σ)).re) - ((1 - t) ^ (σ - 1) - 1)| ≤ (2 * L + Cp) * t := by
    have h1 := abs_sub ((eulerSum t (1 - σ) - eulerSum 0 (1 - σ)).re -
      (eulerSum (1 - t) (1 - σ) - eulerSum 1 (1 - σ)).re) ((1 - t) ^ (σ - 1) - 1)
    have h2 := abs_sub ((eulerSum t (1 - σ) - eulerSum 0 (1 - σ)).re)
      ((eulerSum (1 - t) (1 - σ) - eulerSum 1 (1 - σ)).re)
    linarith
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left key hσ0.le

/-- The function `ψ` is continuous on `[0, 1]`. -/
lemma psiFun_continuousOn {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    ContinuousOn (psiFun σ) (Icc 0 1) := by
  have h1 : ContinuousOn (fun t : ℝ => (1 - t) ^ σ) (Icc 0 1) :=
    ((continuous_const.sub continuous_id).rpow_const (fun _ => Or.inr hσ0.le)).continuousOn
  have h2 : ContinuousOn (fun t : ℝ => hurwitzDiffSum σ t) (Icc 0 1) :=
    continuousOn_hurwitzDiffSum hσ0 hσ1
  have h3 : ContinuousOn (fun t : ℝ => hurwitzDiffSum σ (1 - t)) (Icc 0 1) := by
    refine ContinuousOn.comp (continuousOn_hurwitzDiffSum hσ0 hσ1)
      (continuous_const.sub continuous_id).continuousOn ?_
    intro t ht
    exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have h4 : ContinuousOn (fun t : ℝ =>
      (hurwitzDiffSum σ t + hurwitzDiffSum σ (1 - t) - 2 * hurwitzDiffSum σ 1).re) (Icc 0 1) :=
    Complex.continuous_re.comp_continuousOn ((h2.add h3).sub continuousOn_const)
  unfold psiFun
  exact (h1.sub continuousOn_const).add h4

/-- The function `ψ` vanishes at the origin. -/
lemma psiFun_zero (σ : ℝ) : psiFun σ 0 = 0 := by
  unfold psiFun
  rw [sub_zero, Real.one_rpow, hurwitzDiffSum_zero_eq_one]
  rw [show hurwitzDiffSum σ 1 + hurwitzDiffSum σ 1 - 2 * hurwitzDiffSum σ 1 = 0 by ring]
  simp

/-- The remainder `ψ` is quadratic at the origin: `|ψ(t)| ≤ C t²` for `0 < t ≤ 1/2`. -/
lemma exists_abs_psiFun_le_sq {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → t ≤ 1 / 2 → |psiFun σ t| ≤ C * t ^ 2 := by
  set K : ℝ := σ * (2 * (∑' n : ℕ, ‖(1 - (σ : ℂ))‖ * ((n : ℝ) + 1) ^ (-(1 - (σ : ℂ)).re - 1)) +
    (1 - σ) * (1 / 2 : ℝ) ^ (σ - 2)) with hK
  have hKnn : 0 ≤ K := by
    have hsum : 0 ≤ ∑' n : ℕ, ‖(1 - (σ : ℂ))‖ * ((n : ℝ) + 1) ^ (-(1 - (σ : ℂ)).re - 1) :=
      tsum_nonneg (fun n => by positivity)
    have hp : 0 ≤ (1 - σ) * (1 / 2 : ℝ) ^ (σ - 2) :=
      mul_nonneg (by linarith) (Real.rpow_nonneg (by norm_num) _)
    rw [hK]
    exact mul_nonneg hσ0.le (by linarith)
  refine ⟨K, hKnn, fun t ht0 ht1 => ?_⟩
  have hcont := psiFun_continuousOn hσ0 hσ1
  have hbound : ∀ ε ∈ Ioo 0 t, |psiFun σ t - psiFun σ ε| ≤ K * t * t := by
    intro ε hε
    have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := psiFun σ)
      (f' := fun u : ℝ => -σ * (1 - u) ^ (σ - 1) + σ * (eulerSum u (1 - σ)).re -
        σ * (eulerSum (1 - u) (1 - σ)).re)
      (s := Icc ε t) (C := K * t)
      (fun u hu => (hasDerivAt_psiFun hσ0 hσ1 (by linarith [hε.1, hu.1])
        (by linarith [hu.2, ht1])).hasDerivWithinAt)
      (fun u hu => by
        rw [Real.norm_eq_abs]
        have hb := abs_deriv_psiFun_le hσ0 hσ1 (t := u) (by linarith [hε.1, hu.1])
          (by linarith [hu.2, ht1])
        rw [← hK] at hb
        exact hb.trans (mul_le_mul_of_nonneg_left hu.2 hKnn))
      (convex_Icc ε t) (left_mem_Icc.mpr hε.2.le) (right_mem_Icc.mpr hε.2.le)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by linarith [hε.2] : 0 < t - ε)] at hmvt
    have hb1 : (t - ε) ≤ t := by linarith [hε.1]
    have hKt : 0 ≤ K * t := mul_nonneg hKnn ht0.le
    calc |psiFun σ t - psiFun σ ε| ≤ K * t * (t - ε) := hmvt
      _ ≤ K * t * t := mul_le_mul_of_nonneg_left hb1 hKt
  have hpsi : Tendsto (psiFun σ) (𝓝[>] (0 : ℝ)) (𝓝 (psiFun σ 0)) :=
    ((hcont 0 ⟨le_rfl, zero_le_one⟩).tendsto.mono_left
      ((nhdsWithin_le_of_mem (Ioo_mem_nhdsGT zero_lt_one)).trans
        (nhdsWithin_mono 0 Ioo_subset_Icc_self)))
  have hlim : Tendsto (fun ε => |psiFun σ t - psiFun σ ε|) (𝓝[>] (0 : ℝ))
      (𝓝 |psiFun σ t - psiFun σ 0|) :=
    (tendsto_const_nhds.sub hpsi).abs
  have hle : |psiFun σ t - psiFun σ 0| ≤ K * t * t :=
    le_of_tendsto hlim (Filter.eventually_of_mem (Ioo_mem_nhdsGT ht0)
      (fun ε hε => hbound ε hε))
  rw [psiFun_zero, sub_zero] at hle
  calc |psiFun σ t| ≤ K * t * t := hle
    _ = K * t ^ 2 := by ring

/-- The Hurwitz zeta function at the point `1` of the circle equals its value at `0`. -/
lemma hurwitzAt_one_eq_zero_point (w : ℂ) : hurwitzAt 1 w = hurwitzAt 0 w := by
  unfold hurwitzAt
  rw [coe_one_real_eq_zero]
  simp

/-- The combination `periodicZetaRe σ` vanishes at `1`. -/
lemma periodicZetaRe_one (σ : ℝ) : periodicZetaRe σ 1 = 0 := by
  unfold periodicZetaRe
  rw [sub_self, hurwitzAt_one_eq_zero_point]
  ring

/-- The periodic zeta combination equals `periodicZetaRe` on `UnitAddCircle`. -/
lemma periodicZeta_eq_periodicZetaRe' (s : RieszExponent) :
    (fun x : ℝ => periodicZeta s (x : UnitAddCircle)) = periodicZetaRe s.val :=
  funext (periodicZeta_eq_periodicZetaRe s)

/-- The periodic zeta combination is continuous at the origin, from the right. -/
lemma continuousWithinAt_periodicZetaRe_Icc {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    ContinuousWithinAt (periodicZetaRe σ) (Icc 0 1) 0 := by
  have hpow : ContinuousWithinAt (fun t : ℝ => t ^ σ) (Icc 0 1) 0 :=
    (Real.continuousAt_rpow_const 0 σ (Or.inr hσ0.le)).continuousWithinAt
  have hsum : ContinuousWithinAt (fun t : ℝ => t ^ σ + psiFun σ t) (Icc 0 1) 0 :=
    hpow.add ((psiFun_continuousOn hσ0 hσ1) 0 ⟨le_rfl, zero_le_one⟩)
  have hz : periodicZetaRe σ 0 = 0 := by
    unfold periodicZetaRe
    rw [sub_zero, hurwitzAt_one_eq_zero_point]
    ring
  refine hsum.congr ?_ ?_
  · intro t ht
    rcases eq_or_lt_of_le ht.1 with h0 | hpos
    · subst h0
      rw [hz, psiFun_zero, Real.zero_rpow hσ0.ne']
      ring
    · rcases eq_or_lt_of_le ht.2 with h1 | hlt
      · subst h1
        rw [periodicZetaRe_one]
        have hpsi : psiFun σ 1 = -1 := by
          unfold psiFun
          rw [sub_self, Real.zero_rpow hσ0.ne', hurwitzDiffSum_zero_eq_one]
          rw [show hurwitzDiffSum σ 1 + hurwitzDiffSum σ 1 - 2 * hurwitzDiffSum σ 1 = 0 by ring]
          simp
        rw [hpsi, Real.one_rpow]
        ring
      · exact periodicZetaRe_eq_rpow_add_psiFun hσ0 hσ1 hpos hlt
  · rw [hz, psiFun_zero, Real.zero_rpow hσ0.ne']
    ring

/-- The combination `periodicZetaRe σ` vanishes at the origin. -/
lemma periodicZetaRe_zero_point (σ : ℝ) : periodicZetaRe σ 0 = 0 := by
  unfold periodicZetaRe
  rw [sub_zero, hurwitzAt_one_eq_zero_point]
  ring

/-- The combination `periodicZetaRe σ` is even. -/
lemma periodicZetaRe_neg {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (x : ℝ) :
    periodicZetaRe σ (-x) = periodicZetaRe σ x := by
  have hs : (⟨σ, hσ0, hσ1⟩ : RieszExponent).val = σ := rfl
  rw [← periodicZeta_eq_periodicZetaRe ⟨σ, hσ0, hσ1⟩ (-x), ← periodicZeta_eq_periodicZetaRe
    ⟨σ, hσ0, hσ1⟩ x, periodicZeta_neg]

/-- The combination `periodicZetaRe σ` is continuous at the origin. -/
lemma continuousAt_periodicZetaRe_zero {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    ContinuousAt (periodicZetaRe σ) 0 := by
  have hR := continuousWithinAt_periodicZetaRe_Icc hσ0 hσ1
  have hR' : ContinuousWithinAt (periodicZetaRe σ) (Icc 0 1) (-0) := by
    rw [neg_zero]
    exact hR
  have hL0 := hR'.comp continuous_neg.continuousWithinAt
    (fun x (hx : x ∈ Icc (-1 : ℝ) 0) => (⟨by linarith [hx.2], by linarith [hx.1]⟩ : -x ∈ Icc (0 : ℝ) 1))
  have hL : ContinuousWithinAt (periodicZetaRe σ) (Icc (-1) 0) 0 := by
    refine hL0.congr (fun x _ => ?_) ?_
    · simp only [Function.comp_apply]
      exact (periodicZetaRe_neg hσ0 hσ1 x).symm
    · simp only [Function.comp_apply, neg_zero]
  have hU := hL.union hR
  rw [Icc_union_Icc_eq_Icc (by norm_num) zero_le_one] at hU
  exact hU.continuousAt (Icc_mem_nhds (by norm_num) (by norm_num))

/-- The combination `periodicZetaRe σ` is continuous on `ℝ`. -/
lemma continuous_periodicZetaRe {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    Continuous (periodicZetaRe σ) := by
  refine continuous_iff_continuousAt.2 (fun x₀ => ?_)
  set k : ℤ := ⌊x₀⌋ with hk
  have hperiod : periodicZetaRe σ = fun x => periodicZetaRe σ (x - k) := by
    funext x
    have hs : (⟨σ, hσ0, hσ1⟩ : RieszExponent).val = σ := rfl
    rw [← periodicZeta_eq_periodicZetaRe ⟨σ, hσ0, hσ1⟩ x,
      ← periodicZeta_eq_periodicZetaRe ⟨σ, hσ0, hσ1⟩ (x - k)]
    have h := periodicZeta_add_int ⟨σ, hσ0, hσ1⟩ (x - k) k
    rw [show x - (k : ℝ) + (k : ℝ) = x by ring] at h
    exact h
  have hy0 : 0 ≤ x₀ - k := by
    rw [hk]
    exact sub_nonneg.mpr (Int.floor_le x₀)
  have hy1 : x₀ - k < 1 := by
    rw [hk]
    have := Int.lt_floor_add_one x₀
    linarith
  have hcont : ContinuousAt (periodicZetaRe σ) (x₀ - k) := by
    rcases eq_or_lt_of_le hy0 with h | hpos
    · rw [← h]
      exact continuousAt_periodicZetaRe_zero hσ0 hσ1
    · exact (hasDerivAt_periodicZetaRe hσ0 hσ1 hpos hy1).continuousAt
  rw [hperiod]
  have hcomp := hcont.comp (f := fun x : ℝ => x - k) ((continuous_id.sub continuous_const).continuousAt
    (x := x₀))
  exact hcomp

/-- The combination `periodicZetaRe σ` is `C^∞` on `(0, 1)`. -/
theorem contDiffOn_periodicZetaRe {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    ContDiffOn ℝ ∞ (periodicZetaRe σ) (Ioo 0 1) := by
  have hdiff : DifferentiableOn ℝ (periodicZetaRe σ) (Ioo 0 1) := fun t ht =>
    (hasDerivAt_periodicZetaRe hσ0 hσ1 ht.1 ht.2).differentiableAt.differentiableWithinAt
  refine (contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioo).mpr ⟨hdiff, ?_⟩
  have hderiv : EqOn (deriv (periodicZetaRe σ))
      (fun t : ℝ => σ * (hurwitzAt t (1 - σ)).re - σ * (hurwitzAt (1 - t) (1 - σ)).re) (Ioo 0 1) :=
    fun t ht => (hasDerivAt_periodicZetaRe hσ0 hσ1 ht.1 ht.2).deriv
  refine ContDiffOn.congr ?_ hderiv
  have hre : 0 < (1 - (σ : ℂ)).re := by simp only [sub_re, one_re, ofReal_re]; linarith
  have hne : (1 - (σ : ℂ)) ≠ 1 := by
    intro h
    have h' := congrArg Complex.re h
    simp only [sub_re, one_re, ofReal_re] at h'
    linarith
  have hA : ContDiffOn ℝ ∞ (fun t : ℝ => (hurwitzAt t (1 - σ)).re) (Ioo 0 1) :=
    Complex.reCLM.contDiff.comp_contDiffOn (contDiffOn_infty_hurwitzAt_of_re_pos hre hne)
  have hB0 : ContDiffOn ℝ ∞ (fun t : ℝ => hurwitzAt (1 - t) (1 - σ)) (Ioo 0 1) :=
    (contDiffOn_infty_hurwitzAt_of_re_pos hre hne).comp
      (contDiffOn_const.sub contDiffOn_id) (fun t ht => ⟨by linarith [ht.2], by linarith [ht.1]⟩)
  have hB : ContDiffOn ℝ ∞ (fun t : ℝ => (hurwitzAt (1 - t) (1 - σ)).re) (Ioo 0 1) :=
    Complex.reCLM.contDiff.comp_contDiffOn hB0
  exact (contDiffOn_const.mul hA).sub (contDiffOn_const.mul hB)

/-- The second derivative of `periodicZetaRe σ`, its derivative, is negative on `(0, 1)`. -/
lemma deriv_deriv_periodicZetaRe_neg {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) {x : ℝ} (hx0 : 0 < x)
    (hx1 : x < 1) : deriv (deriv (periodicZetaRe σ)) x < 0 := by
  have hd := (hasDerivAt_deriv_periodicZetaRe hσ0 hσ1 hx0 hx1).deriv
  rw [hd]
  have h2 : (2 : ℂ) - (σ : ℂ) = ((2 - σ : ℝ) : ℂ) := by push_cast; ring
  have hp1 : 0 < (hurwitzAt x (2 - σ)).re := by
    rw [h2]
    exact re_hurwitzAt_pos hx0 hx1.le (by linarith)
  have hp2 : 0 < (hurwitzAt (1 - x) (2 - σ)).re := by
    rw [h2]
    exact re_hurwitzAt_pos (by linarith) (by linarith) (by linarith)
  have hpos : 0 < σ * (1 - σ) := mul_pos hσ0 (by linarith)
  have := mul_pos hpos (add_pos hp1 hp2)
  linarith

/-- The combination `periodicZetaRe σ` is strictly concave on `[0, 1]`. -/
theorem strictConcaveOn_periodicZetaRe {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    StrictConcaveOn ℝ (Icc 0 1) (periodicZetaRe σ) := by
  refine strictConcaveOn_of_deriv2_neg (convex_Icc 0 1)
    (continuous_periodicZetaRe hσ0 hσ1).continuousOn ?_
  intro x hx
  rw [interior_Icc] at hx
  exact deriv_deriv_periodicZetaRe_neg hσ0 hσ1 hx.1 hx.2

/-- The combination `periodicZetaRe σ` is strictly positive on `(0, 1)`. -/
theorem periodicZetaRe_pos {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) {x : ℝ} (hx0 : 0 < x)
    (hx1 : x < 1) : 0 < periodicZetaRe σ x := by
  have hc := (strictConcaveOn_periodicZetaRe hσ0 hσ1).2
  have := hc (x := 0) (by simp) (y := 1) (by simp) (by norm_num) (a := 1 - x) (b := x)
    (by linarith) hx0 (by ring)
  simp only [smul_eq_mul, periodicZetaRe_zero_point, periodicZetaRe_one, mul_zero, zero_add,
    mul_one, add_zero] at this
  simpa [sub_mul, mul_zero, zero_add, one_mul] using this

/-! ## The periodic zeta combination `V_s = periodicZeta s` -/

/-- Item 1: the periodic zeta combination is continuous on `ℝ`. -/
theorem periodicZeta_continuous (s : RieszExponent) :
    Continuous (fun t : ℝ => periodicZeta s (t : UnitAddCircle)) := by
  rw [periodicZeta_eq_periodicZetaRe']
  exact continuous_periodicZetaRe s.2.1 s.2.2

/-- Item 1: the periodic zeta combination is even. -/
theorem periodicZeta_even (s : RieszExponent) (t : ℝ) :
    periodicZeta s ((-t : ℝ) : UnitAddCircle) = periodicZeta s (t : UnitAddCircle) :=
  periodicZeta_neg s t

/-- Item 1: the periodic zeta combination is `1`-periodic. -/
theorem periodicZeta_periodic (s : RieszExponent) (t : ℝ) :
    periodicZeta s ((t + 1 : ℝ) : UnitAddCircle) = periodicZeta s (t : UnitAddCircle) := by
  simp

/-- Item 1: the periodic zeta combination vanishes at the origin. -/
theorem periodicZeta_zero (s : RieszExponent) : periodicZeta s 0 = 0 :=
  periodicZeta_zero_point s

/-- Item 1: the periodic zeta combination is `C^∞` on `(0, 1)`. -/
theorem periodicZeta_contDiffOn (s : RieszExponent) :
    ContDiffOn ℝ ∞ (fun t : ℝ => periodicZeta s (t : UnitAddCircle)) (Ioo 0 1) := by
  rw [periodicZeta_eq_periodicZetaRe']
  exact contDiffOn_periodicZetaRe s.2.1 s.2.2

/-- Item 1: the periodic zeta combination is strictly positive on `(0, 1)`. -/
theorem periodicZeta_pos (s : RieszExponent) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    0 < periodicZeta s (t : UnitAddCircle) := by
  rw [periodicZeta_eq_periodicZetaRe]
  exact periodicZetaRe_pos s.2.1 s.2.2 ht0 ht1

/-- Item 2: the expansion `|V_s(t) - t^s| ≤ C t²` for `0 < t ≤ t₀`, with `t₀ = 1/2`. -/
theorem periodicZeta_asymptotic (s : RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t : ℝ, 0 < t → t ≤ t₀ →
      |periodicZeta s (t : UnitAddCircle) - t ^ s.val| ≤ C * t ^ 2 := by
  obtain ⟨C₀, hC₀, hbound⟩ := exists_abs_psiFun_le_sq s.2.1 s.2.2
  refine ⟨C₀ + 1, by linarith, 1 / 2, by norm_num, fun t ht0 ht1 => ?_⟩
  have ht1' : t < 1 := by linarith
  rw [periodicZeta_eq_periodicZetaRe, periodicZetaRe_eq_rpow_add_psiFun s.2.1 s.2.2 ht0 ht1']
  rw [add_sub_cancel_left]
  have h := hbound t ht0 ht1
  have hsq : 0 ≤ t ^ 2 := sq_nonneg t
  nlinarith

/-- Item 3: the second derivative of the periodic zeta combination on `(0, 1)`:
`V_s''(t) = -s(1 - s)(ζ(2 - s, t) + ζ(2 - s, 1 - t))`, where `ζ` is the Hurwitz zeta function
(its real parts, as the values are real). -/
theorem periodicZeta_hasDerivAt_deriv (s : RieszExponent) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    HasDerivAt (deriv fun τ : ℝ => periodicZeta s (τ : UnitAddCircle))
      (-(s.val * (1 - s.val)) * ((hurwitzAt t (2 - s.val)).re +
        (hurwitzAt (1 - t) (2 - s.val)).re)) t := by
  rw [periodicZeta_eq_periodicZetaRe']
  exact hasDerivAt_deriv_periodicZetaRe s.2.1 s.2.2 ht0 ht1

/-- Item 3: the periodic zeta combination is strictly concave on `(0, 1)`. -/
theorem periodicZeta_strictConcaveOn (s : RieszExponent) :
    StrictConcaveOn ℝ (Ioo 0 1) (fun t : ℝ => periodicZeta s (t : UnitAddCircle)) := by
  rw [periodicZeta_eq_periodicZetaRe']
  exact (strictConcaveOn_periodicZetaRe s.2.1 s.2.2).subset Ioo_subset_Icc_self (convex_Ioo 0 1)

/-! ## The periodic kernel `K_s` -/

/-- The periodic kernel `K_s`: for `t ∉ ℤ`,
`K_s(t) = Re ζ(1 - s, {t}) - Re ζ(1 - s, 1 - {t})`, where `{t} = Int.fract t` lies in `(0, 1)`.
The real parts are the values, since the Hurwitz values at real points are real. -/
@[expose] noncomputable def periodicKernel (s : ℝ) (t : ℝ) : ℝ :=
  (hurwitzAt (Int.fract t) (1 - (s : ℂ))).re - (hurwitzAt (1 - Int.fract t) (1 - (s : ℂ))).re

/-- The kernel is `1`-periodic under integer shifts. -/
lemma periodicKernel_add_int (s t : ℝ) (n : ℤ) : periodicKernel s (t + n) = periodicKernel s t := by
  unfold periodicKernel
  rw [Int.fract_add_intCast]

/-- The periodic zeta combination is invariant under integer shifts of the real variable. -/
lemma periodicZetaRe_sub_int {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (t : ℝ) (n : ℤ) :
    periodicZetaRe σ (t - n) = periodicZetaRe σ t := by
  have h := periodicZeta_add_int ⟨σ, hσ0, hσ1⟩ (t - n) n
  rw [show t - n + n = t by ring] at h
  rw [← periodicZeta_eq_periodicZetaRe ⟨σ, hσ0, hσ1⟩ t, ← periodicZeta_eq_periodicZetaRe
    ⟨σ, hσ0, hσ1⟩ (t - n), h]

/-- The fractional part of a non-integer lies in `(0, 1)`. -/
lemma fract_mem_Ioo_of_not_int {t : ℝ} (ht : ∀ k : ℤ, t ≠ k) : Int.fract t ∈ Ioo (0 : ℝ) 1 := by
  refine ⟨?_, Int.fract_lt_one t⟩
  rcases (Int.fract_nonneg t).lt_or_eq with h | h
  · exact h
  · exfalso
    apply ht ⌊t⌋
    have := Int.fract_add_floor t
    rw [← h] at this
    linarith

/-- For `t ∉ ℤ`, the periodic zeta combination has derivative `s K_s(t)`: this is `V_s' = s K_s`
off the integers, as in Lemma 2.3. -/
theorem hasDerivAt_periodicZeta_of_not_int (s : RieszExponent) {t : ℝ} (ht : ∀ k : ℤ, t ≠ k) :
    HasDerivAt (fun τ : ℝ => periodicZeta s (τ : UnitAddCircle)) (s.val * periodicKernel s.val t) t := by
  rw [periodicZeta_eq_periodicZetaRe']
  have hx := fract_mem_Ioo_of_not_int ht
  have hsub : t - (⌊t⌋ : ℝ) = Int.fract t := rfl
  have h : HasDerivAt (periodicZetaRe s.val) (s.val * (hurwitzAt (Int.fract t) (1 - s.val)).re -
      s.val * (hurwitzAt (1 - Int.fract t) (1 - s.val)).re) (t - ⌊t⌋) := by
    rw [hsub]
    exact hasDerivAt_periodicZetaRe s.2.1 s.2.2 hx.1 hx.2
  have h2 := h.comp_sub_const t ⌊t⌋
  have hfun : (fun τ : ℝ => periodicZetaRe s.val (τ - ⌊t⌋)) = periodicZetaRe s.val :=
    funext fun τ => periodicZetaRe_sub_int s.2.1 s.2.2 τ ⌊t⌋
  rw [hfun] at h2
  convert h2 using 1
  unfold periodicKernel
  ring

/-- The summable majorant of the Euler terms, for `Re v > 0`. -/
lemma summable_eulerBound (v : ℂ) (hv : 0 < v.re) :
    Summable (fun n : ℕ => ‖v‖ * ((n : ℝ) + 1) ^ (-v.re - 1)) :=
  Summable.mul_left _ ((summable_rpow_shift (a := v.re + 1) (by linarith)).congr
    (fun n => by congr 1; ring))

/-- The Euler sum at exponent `1 - s` is continuous on `[0, 1]`, by uniform convergence. -/
lemma continuousOn_eulerSum_Icc {v : ℂ} (hv : 0 < v.re) (hv1 : v ≠ 1) :
    ContinuousOn (fun u : ℝ => eulerSum u v) (Icc 0 1) := by
  unfold eulerSum
  refine continuousOn_tsum (fun n => ?_) (summable_eulerBound v hv)
    (fun n u hu => norm_eulerTerm_le u hu.1 hu.2 v hv hv1 n)
  intro u hu
  exact (hasDerivAt_eulerTerm_real v n
    (by linarith [hu.1, Nat.cast_nonneg (α := ℝ) n])).continuousAt.continuousWithinAt

/-- The Euler representation of the real part of `ζ(1 - s, u)` for `u ∈ (0, 1]`:
`Re ζ(1 - s, u) = u^(s - 1) + Re eulerSum u (1 - s) - 1/s`. -/
lemma re_hurwitzAt_one_sub_eq {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {u : ℝ} (hu0 : 0 < u)
    (hu1 : u ≤ 1) :
    (hurwitzAt u (1 - (s : ℂ))).re = u ^ (s - 1) + (eulerSum u (1 - s)).re - 1 / s := by
  have hre : 0 < (1 - (s : ℂ)).re := by simp only [sub_re, one_re, ofReal_re]; linarith
  have hne : (1 - (s : ℂ)) ≠ 1 := by
    intro h
    have h' := congrArg Complex.re h
    simp only [sub_re, one_re, ofReal_re] at h'
    linarith
  have hE := euler_eq_hurwitzZeta u hu0 hu1 (1 - (s : ℂ)) hre hne
  have hpow : (u : ℂ) ^ (-(1 - (s : ℂ))) = ((u ^ (s - 1) : ℝ) : ℂ) := by
    rw [show -(1 - (s : ℂ)) = ((s - 1 : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_cpow hu0.le]
  have h1 : (1 : ℂ) - (1 - (s : ℂ)) = ((s : ℝ) : ℂ) := by ring
  have hdiv : (1 : ℂ) / ((s : ℝ) : ℂ) = ((1 / s : ℝ) : ℂ) := by push_cast; ring
  unfold hurwitzAt
  rw [← hE]
  unfold eulerSum
  rw [hpow, h1, hdiv]
  simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re]

/-- On `(0, 1)` the kernel is `x^(s-1) - (1-x)^(s-1) + Re(S(x) - S(1-x))`, with the Euler sum
`S = eulerSum · (1 - s)`. -/
lemma periodicKernel_eq_on_Ioo {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    EqOn (periodicKernel s) (fun x : ℝ => x ^ (s - 1) - (1 - x) ^ (s - 1) +
      ((eulerSum x (1 - s)).re - (eulerSum (1 - x) (1 - s)).re)) (Ioo 0 1) := by
  intro x hx
  unfold periodicKernel
  have hfx : Int.fract x = x := Int.fract_eq_self.mpr ⟨hx.1.le, hx.2⟩
  rw [hfx]
  rw [re_hurwitzAt_one_sub_eq hs0 hs1 hx.1 hx.2.le,
    re_hurwitzAt_one_sub_eq hs0 hs1 (by linarith [hx.2]) (by linarith [hx.1])]
  dsimp only
  ring

/-- The periodic kernel is integrable over a period. -/
theorem intervalIntegrable_periodicKernel {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    IntervalIntegrable (periodicKernel s) volume 0 1 := by
  have hv : 0 < (1 - (s : ℂ)).re := by simp only [sub_re, one_re, ofReal_re]; linarith
  have hv1 : (1 - (s : ℂ)) ≠ 1 := by
    intro h
    have h' := congrArg Complex.re h
    simp only [sub_re, one_re, ofReal_re] at h'
    linarith
  have hcont1 : ContinuousOn (fun x : ℝ => (eulerSum x (1 - s)).re) (uIcc 0 1) := by
    rw [uIcc_of_le zero_le_one]
    exact Complex.continuous_re.comp_continuousOn (continuousOn_eulerSum_Icc hv hv1)
  have hcont2 : ContinuousOn (fun x : ℝ => (eulerSum (1 - x) (1 - s)).re) (uIcc 0 1) := by
    rw [uIcc_of_le zero_le_one]
    refine Complex.continuous_re.comp_continuousOn (ContinuousOn.comp
      (continuousOn_eulerSum_Icc hv hv1) (continuous_const.sub continuous_id).continuousOn ?_)
    intro x hx
    exact ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hpow1 : IntervalIntegrable (fun x : ℝ => x ^ (s - 1)) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (r := s - 1) (by linarith)
  have hpow2 : IntervalIntegrable (fun x : ℝ => (1 - x) ^ (s - 1)) volume 0 1 := by
    have h := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1)
      (show (-1 : ℝ) < s - 1 by linarith)).comp_sub_left 1
    simp only [sub_zero, sub_self] at h
    exact h.symm
  have hg : IntervalIntegrable (fun x : ℝ => x ^ (s - 1) - (1 - x) ^ (s - 1) +
      ((eulerSum x (1 - s)).re - (eulerSum (1 - x) (1 - s)).re)) volume 0 1 :=
    ((hpow1.sub hpow2).add ((hcont1.intervalIntegrable).sub hcont2.intervalIntegrable))
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one] at hg ⊢
  exact hg.congr_fun (periodicKernel_eq_on_Ioo hs0 hs1).symm measurableSet_Ioo

/-- The kernel is antisymmetric about `1/2`: `K_s(1 - t) = -K_s(t)` for every real `t`. -/
lemma periodicKernel_one_sub (s t : ℝ) : periodicKernel s (1 - t) = -periodicKernel s t := by
  unfold periodicKernel
  by_cases hf : Int.fract t = 0
  · have hx : Int.fract (1 - t) = 0 := by
      have h1 : (1 - t) = ((1 - ⌊t⌋ : ℤ) : ℝ) := by
        have := Int.fract_add_floor t
        push_cast
        linarith
      rw [h1, Int.fract_intCast]
    rw [hf, hx, sub_zero, hurwitzAt_one_eq_zero_point]
    simp
  · have h1 : Int.fract (1 - t) = 1 - Int.fract t := by
      rw [show (1 - t) = -t + 1 by ring, Int.fract_add_one, Int.fract_neg hf]
    rw [h1, show (1 : ℝ) - (1 - Int.fract t) = Int.fract t by ring]
    ring

/-- The periodic kernel has mean zero over a period. -/
theorem integral_periodicKernel (s : ℝ) : ∫ t in (0 : ℝ)..1, periodicKernel s t = 0 := by
  have h := intervalIntegral.integral_comp_sub_left (periodicKernel s) (1 : ℝ) (a := 0) (b := 1)
  simp only [sub_self, sub_zero] at h
  have hneg : ∫ t in (0 : ℝ)..1, periodicKernel s (1 - t) =
      -∫ t in (0 : ℝ)..1, periodicKernel s t := by
    rw [← intervalIntegral.integral_neg]
    congr 1
    funext t
    exact periodicKernel_one_sub s t
  linarith

/-! ## The symmetric partial sums of `sign(t - k) |t - k|^(s-1)` -/

/-- The signed power `sign(u) |u|^(s-1)`, the summand of the symmetric partial sums. -/
@[expose] noncomputable def signPow (s u : ℝ) : ℝ := Real.sign u * |u| ^ (s - 1)

lemma signPow_of_pos {s u : ℝ} (hu : 0 < u) : signPow s u = u ^ (s - 1) := by
  unfold signPow
  rw [Real.sign_of_pos hu, abs_of_pos hu, one_mul]

lemma signPow_of_neg {s u : ℝ} (hu : u < 0) : signPow s u = -((-u) ^ (s - 1)) := by
  unfold signPow
  rw [Real.sign_of_neg hu, abs_of_neg hu, neg_one_mul]

/-- Splitting off the two endpoints of the symmetric range `[-(M+1), M+1]`. -/
lemma sum_Icc_succ_symm (h : ℤ → ℝ) (M : ℕ) :
    ∑ k ∈ Finset.Icc (-((M : ℤ) + 1)) ((M : ℤ) + 1), h k =
      ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), h k + h (-((M : ℤ) + 1)) + h ((M : ℤ) + 1) := by
  have hset : Finset.Icc (-((M : ℤ) + 1)) ((M : ℤ) + 1) =
      insert (-((M : ℤ) + 1)) (insert ((M : ℤ) + 1) (Finset.Icc (-(M : ℤ)) (M : ℤ))) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_insert]
    constructor <;> intro hk <;> omega
  have hn1 : ((M : ℤ) + 1) ∉ Finset.Icc (-(M : ℤ)) (M : ℤ) := by
    simp only [Finset.mem_Icc, not_and, not_le]
    omega
  have hn2 : (-((M : ℤ) + 1)) ∉ insert ((M : ℤ) + 1) (Finset.Icc (-(M : ℤ)) (M : ℤ)) := by
    simp only [Finset.mem_insert, Finset.mem_Icc, not_or, not_and, not_le]
    omega
  rw [hset, Finset.sum_insert hn2, Finset.sum_insert hn1]
  ring

/-- The shift identity: the symmetric partial sums at `t` and `t + 1` differ by the two endpoint
terms `signPow (t - M) - signPow (t + M + 1)`. -/
lemma symmetricSum_sub_shift (s t : ℝ) (M : ℕ) :
    ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), signPow s (t - k) -
      ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), signPow s (t + 1 - k) =
      signPow s (t - M) - signPow s (t + M + 1) := by
  induction M with
  | zero => simp
  | succ M ih =>
    have h1 := sum_Icc_succ_symm (fun k : ℤ => signPow s (t - k)) M
    have h2 := sum_Icc_succ_symm (fun k : ℤ => signPow s (t + 1 - k)) M
    have ea : signPow s (t - (((-((M : ℤ) + 1)) : ℤ) : ℝ)) = signPow s (t + (M : ℝ) + 1) := by
      congr 1; push_cast; ring
    have eb : signPow s (t - (((M : ℤ) + 1 : ℤ) : ℝ)) = signPow s (t - ((M : ℝ) + 1)) := by
      congr 1; push_cast; ring
    have ec : signPow s (t + 1 - (((-((M : ℤ) + 1)) : ℤ) : ℝ)) =
        signPow s (t + ((M : ℝ) + 1) + 1) := by
      congr 1; push_cast; ring
    have ed : signPow s (t + 1 - (((M : ℤ) + 1 : ℤ) : ℝ)) = signPow s (t - (M : ℝ)) := by
      congr 1; push_cast; ring
    push_cast
    rw [h1, h2, ea, eb, ec, ed]
    linarith [ih]

/-- Closed form of the symmetric partial sums on `(0, 1)`: the terms `±k` are paired, and the
pairs telescope into the Euler partial sum at `x` and `1 - x`. -/
lemma symmetricSum_formula {s x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) (M : ℕ) :
    ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), signPow s (x - k) =
      x ^ (s - 1) - (1 - x) ^ (s - 1) +
        (∑ n ∈ Finset.range M, (((n : ℝ) + 1 + x) ^ (s - 1) - ((n : ℝ) + 2 - x) ^ (s - 1))) +
        ((M : ℝ) + 1 - x) ^ (s - 1) := by
  induction M with
  | zero =>
    simp [signPow_of_pos hx0]
  | succ M ih =>
    have h1 := sum_Icc_succ_symm (fun k : ℤ => signPow s (x - k)) M
    have ea : signPow s (x - (((-((M : ℤ) + 1)) : ℤ) : ℝ)) = ((M : ℝ) + 1 + x) ^ (s - 1) := by
      rw [show x - (((-((M : ℤ) + 1)) : ℤ) : ℝ) = (M : ℝ) + 1 + x by push_cast; ring]
      exact signPow_of_pos (by positivity)
    have eb : signPow s (x - (((M : ℤ) + 1 : ℤ) : ℝ)) = -(((M : ℝ) + 1 - x) ^ (s - 1)) := by
      rw [show x - (((M : ℤ) + 1 : ℤ) : ℝ) = -((M : ℝ) + 1 - x) by push_cast; ring,
        signPow_of_neg (by linarith [(by positivity : (0 : ℝ) ≤ (M : ℝ))]), neg_neg]
    push_cast
    rw [h1, ea, eb, Finset.sum_range_succ, show (M : ℝ) + 1 + 1 - x = (M : ℝ) + 2 - x by ring]
    linarith [ih]

/-- The real part of the difference of the Euler terms at `x` and `1 - x` is the difference of the
powers `(n + 1 + x)^(s - 1) - (n + 2 - x)^(s - 1)`, since the corrections cancel. -/
lemma re_eulerTerm_sub_eq (s x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) (n : ℕ) :
    (eulerTerm x (1 - (s : ℂ)) n - eulerTerm (1 - x) (1 - (s : ℂ)) n).re =
      ((n : ℝ) + 1 + x) ^ (s - 1) - ((n : ℝ) + 2 - x) ^ (s - 1) := by
  have hA : ((n : ℂ) + 1 + (x : ℂ)) ^ (-(1 - (s : ℂ))) =
      ((((n : ℝ) + 1 + x) ^ (s - 1) : ℝ) : ℂ) := by
    rw [show ((n : ℂ) + 1 + (x : ℂ)) = (((n : ℝ) + 1 + x : ℝ) : ℂ) by push_cast; ring,
      show -(1 - (s : ℂ)) = ((s - 1 : ℝ) : ℂ) by push_cast; ring,
      Complex.ofReal_cpow (by positivity)]
  have hB : ((n : ℂ) + 1 + ((1 - x : ℝ) : ℂ)) ^ (-(1 - (s : ℂ))) =
      ((((n : ℝ) + 2 - x) ^ (s - 1) : ℝ) : ℂ) := by
    rw [show ((n : ℂ) + 1 + ((1 - x : ℝ) : ℂ)) = ((((n : ℝ) + 2 - x) : ℝ) : ℂ) by push_cast; ring,
      show -(1 - (s : ℂ)) = ((s - 1 : ℝ) : ℂ) by push_cast; ring,
      Complex.ofReal_cpow (by linarith [(by positivity : (0 : ℝ) ≤ (n : ℝ))])]
  unfold eulerTerm
  rw [hA, hB]
  simp only [Complex.sub_re, Complex.ofReal_re]
  ring_nf

/-- The symmetric partial sums converge to `K_s(x)` for `x ∈ (0, 1)`: the closed form of
`symmetricSum_formula` converges, term by term, to the Euler representation of the kernel. -/
theorem tendsto_symmetricSum_of_mem {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {x : ℝ} (hx0 : 0 < x)
    (hx1 : x < 1) :
    Tendsto (fun M : ℕ => ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), signPow s (x - k)) atTop
      (𝓝 (periodicKernel s x)) := by
  have hv : 0 < (1 - (s : ℂ)).re := by simp only [sub_re, one_re, ofReal_re]; linarith
  have hv1 : (1 - (s : ℂ)) ≠ 1 := by
    intro h
    have h' := congrArg Complex.re h
    simp only [sub_re, one_re, ofReal_re] at h'
    linarith
  have hS1 := (summable_eulerTerm x hx0.le hx1.le (1 - (s : ℂ)) hv hv1).hasSum
  have hS2 := (summable_eulerTerm (1 - x) (by linarith) (by linarith) (1 - (s : ℂ)) hv hv1).hasSum
  have hD := (hS1.sub hS2).tendsto_sum_nat
  have hRe := (Complex.continuous_re.tendsto _).comp hD
  have hReP : ∀ M : ℕ, (∑ n ∈ Finset.range M,
      (eulerTerm x (1 - (s : ℂ)) n - eulerTerm (1 - x) (1 - (s : ℂ)) n)).re =
        ∑ n ∈ Finset.range M, (((n : ℝ) + 1 + x) ^ (s - 1) - ((n : ℝ) + 2 - x) ^ (s - 1)) := by
    intro M
    rw [Complex.re_sum]
    exact Finset.sum_congr rfl (fun n _ => re_eulerTerm_sub_eq s x hx0 hx1 n)
  have hRealP : Tendsto (fun M : ℕ => ∑ n ∈ Finset.range M,
      (((n : ℝ) + 1 + x) ^ (s - 1) - ((n : ℝ) + 2 - x) ^ (s - 1))) atTop
      (𝓝 (eulerSum x (1 - (s : ℂ)) - eulerSum (1 - x) (1 - (s : ℂ))).re) := by
    have h := hRe
    simp only [Function.comp_def] at h
    refine h.congr (fun M => ?_)
    rw [hReP M]
  have hlast : Tendsto (fun M : ℕ => ((M : ℝ) + 1 - x) ^ (s - 1)) atTop (𝓝 0) := by
    have hb : Tendsto (fun M : ℕ => (M : ℝ) + (1 - x)) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    have h := (tendsto_rpow_neg_atTop (by linarith : (0 : ℝ) < 1 - s)).comp hb
    have e : -(1 - s) = s - 1 := by ring
    simp only [Function.comp_def, e] at h
    refine h.congr (fun M => ?_)
    rw [add_sub_assoc]
  have hcomb := ((tendsto_const_nhds (x := x ^ (s - 1) - (1 - x) ^ (s - 1))).add hRealP).add hlast
  have hfun : (fun M : ℕ => ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), signPow s (x - k)) = fun M : ℕ =>
      x ^ (s - 1) - (1 - x) ^ (s - 1) +
        (∑ n ∈ Finset.range M, (((n : ℝ) + 1 + x) ^ (s - 1) - ((n : ℝ) + 2 - x) ^ (s - 1))) +
        ((M : ℝ) + 1 - x) ^ (s - 1) :=
    funext (fun M => symmetricSum_formula hx0 hx1 M)
  have hlimit : x ^ (s - 1) - (1 - x) ^ (s - 1) +
      (eulerSum x (1 - (s : ℂ)) - eulerSum (1 - x) (1 - (s : ℂ))).re + 0 =
        periodicKernel s x := by
    rw [periodicKernel_eq_on_Ioo hs0 hs1 ⟨hx0, hx1⟩]
    simp only [Complex.sub_re, eulerSum]
    ring
  rw [hfun]
  rw [hlimit] at hcomb
  exact hcomb

/-- The signed power tends to zero along a sequence whose absolute value tends to infinity. -/
lemma tendsto_signPow_zero {s : ℝ} (_hs0 : 0 < s) (hs1 : s < 1) (u : ℕ → ℝ)
    (hu : Tendsto (fun M => |u M|) atTop atTop) :
    Tendsto (fun M => signPow s (u M)) atTop (𝓝 0) := by
  have hpow : Tendsto (fun M => |u M| ^ (s - 1)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (by linarith : (0 : ℝ) < 1 - s)).comp hu
    have e : -(1 - s) = s - 1 := by ring
    simpa only [Function.comp_def, e] using h
  refine squeeze_zero_norm' ?_ hpow
  filter_upwards with M
  rw [Real.norm_eq_abs, signPow, abs_mul, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
  have hsign : |Real.sign (u M)| ≤ 1 := by
    unfold Real.sign
    split_ifs <;> simp
  exact mul_le_of_le_one_left (Real.rpow_nonneg (abs_nonneg _) _) hsign

/-- The shift `t ↦ t + 1` does not change whether the symmetric partial sums converge, nor their
limit: the two sums differ by the endpoint terms, which tend to zero. -/
lemma tendsto_symmetricSum_shift_iff {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (t L : ℝ) :
    Tendsto (fun M : ℕ => ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), signPow s (t + 1 - k)) atTop
        (𝓝 L) ↔
      Tendsto (fun M : ℕ => ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), signPow s (t - k)) atTop
        (𝓝 L) := by
  have hA : Tendsto (fun M : ℕ => |t - M|) atTop atTop := by
    refine tendsto_atTop_mono (fun M : ℕ => ?_)
      (tendsto_atTop_add_const_right _ (-|t|) tendsto_natCast_atTop_atTop)
    have := abs_sub_abs_le_abs_sub (M : ℝ) t
    rw [abs_of_nonneg (Nat.cast_nonneg M)] at this
    linarith [abs_sub_comm (M : ℝ) t]
  have hA' : Tendsto (fun M : ℕ => |t + M + 1|) atTop atTop := by
    refine tendsto_atTop_mono (fun M : ℕ => ?_)
      (tendsto_atTop_add_const_right _ (t + 1) tendsto_natCast_atTop_atTop)
    have := le_abs_self (t + M + 1)
    linarith
  have hB : Tendsto (fun M : ℕ => signPow s (t - M) - signPow s (t + M + 1)) atTop (𝓝 0) := by
    have h1 := tendsto_signPow_zero hs0 hs1 (fun M : ℕ => t - M) hA
    have h2 := tendsto_signPow_zero hs0 hs1 (fun M : ℕ => t + M + 1) hA'
    simpa using h1.sub h2
  have hdiff : ∀ M : ℕ, ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), signPow s (t - k) =
      ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), signPow s (t + 1 - k) +
        (signPow s (t - M) - signPow s (t + M + 1)) := fun M => by
    linarith [symmetricSum_sub_shift s t M]
  constructor
  · intro h
    have h' := h.add hB
    rw [add_zero] at h'
    exact h'.congr (fun M => (hdiff M).symm)
  · intro h
    have h' := h.sub hB
    rw [sub_zero] at h'
    exact h'.congr (fun M => by linarith [hdiff M])

/-- Item 4: for every `t ∉ ℤ`, the symmetric partial sums `∑_{k=-M}^{M} sign(t - k)|t - k|^(s-1)`
converge to the periodic kernel `K_s(t)`. -/
theorem tendsto_symmetricPartialSum {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {t : ℝ}
    (ht : ∀ k : ℤ, t ≠ k) :
    Tendsto (fun M : ℕ => ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), Real.sign (t - k) * |t - k| ^ (s - 1))
      atTop (𝓝 (periodicKernel s t)) := by
  have hx := fract_mem_Ioo_of_not_int ht
  have hK : periodicKernel s t = periodicKernel s (Int.fract t) := by
    have := periodicKernel_add_int s (Int.fract t) ⌊t⌋
    rw [Int.fract_add_floor] at this
    exact this
  have key : ∀ m : ℤ, Tendsto (fun M : ℕ => ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
      signPow s (Int.fract t + m - k)) atTop (𝓝 (periodicKernel s (Int.fract t))) := by
    intro m
    induction m using Int.induction_on with
    | zero =>
      simpa using tendsto_symmetricSum_of_mem hs0 hs1 hx.1 hx.2
    | succ i ih =>
      have h := (tendsto_symmetricSum_shift_iff hs0 hs1 (Int.fract t + (i : ℝ))
        (periodicKernel s (Int.fract t))).mpr ih
      refine h.congr (fun M => ?_)
      refine Finset.sum_congr rfl (fun k _ => ?_)
      congr 1
      push_cast
      ring
    | pred i ih =>
      have hcongr : (fun M : ℕ => ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
          signPow s (Int.fract t + ((-(i : ℤ) - 1 : ℤ) : ℝ) + 1 - k)) =
          (fun M : ℕ => ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
            signPow s (Int.fract t + ((-(i : ℤ)) : ℤ) - k)) := by
        funext M
        refine Finset.sum_congr rfl (fun k _ => ?_)
        congr 1
        push_cast
        ring
      have h := (tendsto_symmetricSum_shift_iff hs0 hs1 (Int.fract t + ((-(i : ℤ) - 1 : ℤ) : ℝ))
        (periodicKernel s (Int.fract t))).mp (by rw [hcongr]; exact ih)
      exact h
  have h := key ⌊t⌋
  simp only [Int.fract_add_floor] at h
  rw [hK]
  refine h.congr (fun M => Finset.sum_congr rfl (fun k _ => ?_))
  rfl

/-- The Hurwitz zeta values at `x` and `1 - x` sum to twice Mathlib's `hurwitzZetaEven x z`
(the even part), for `x ∈ (0, 1)`. -/
lemma hurwitzAt_add_one_sub_eq (x : ℝ) (z : ℂ) :
    hurwitzAt x z + hurwitzAt (1 - x) z = 2 * HurwitzZeta.hurwitzZetaEven (x : UnitAddCircle) z := by
  unfold hurwitzAt
  rw [HurwitzZeta.hurwitzZetaEven_eq, coe_one_sub_real]
  ring

/-- Item 3 in Mathlib's even Hurwitz zeta: for `0 < t < 1`, the second derivative of the periodic
zeta combination is `-2 s (1 - s) Re hurwitzZetaEven(t, 2 - s)`, since
`ζ(2 - s, t) + ζ(2 - s, 1 - t) = 2 hurwitzZetaEven t (2 - s)`. -/
theorem periodicZeta_hasDerivAt_deriv_even (s : RieszExponent) {t : ℝ} (ht0 : 0 < t)
    (ht1 : t < 1) :
    HasDerivAt (deriv fun τ : ℝ => periodicZeta s (τ : UnitAddCircle))
      (-(2 * s.val * (1 - s.val)) * (HurwitzZeta.hurwitzZetaEven (t : UnitAddCircle)
        (2 - (s.val : ℂ))).re) t := by
  have h := periodicZeta_hasDerivAt_deriv s ht0 ht1
  have e := hurwitzAt_add_one_sub_eq t (2 - (s.val : ℂ))
  have hre := congrArg Complex.re e
  simp only [Complex.add_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul,
    sub_zero] at hre
  convert h using 1
  rw [show (hurwitzAt t (2 - s.val)).re + (hurwitzAt (1 - t) (2 - s.val)).re =
    2 * (HurwitzZeta.hurwitzZetaEven (t : UnitAddCircle) (2 - (s.val : ℂ))).re by linarith]
  ring

/-- Item 4: `K_s = V_s' / s` off the integers, where `V_s = periodicZeta s`. -/
theorem periodicKernel_eq_deriv_div (s : RieszExponent) {t : ℝ} (ht : ∀ k : ℤ, t ≠ k) :
    periodicKernel s.val t =
      deriv (fun τ : ℝ => periodicZeta s (τ : UnitAddCircle)) t / s.val := by
  rw [(hasDerivAt_periodicZeta_of_not_int s ht).deriv]
  have : s.val ≠ 0 := s.2.1.ne'
  field_simp

end Riesz1

end
