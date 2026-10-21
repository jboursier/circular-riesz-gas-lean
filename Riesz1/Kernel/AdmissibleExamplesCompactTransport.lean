/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Kernel.TransportScaledMain

/-!
# Transport of an interval indicator on enlarged circles

Let `K = K_{s,L}` be the scaled kernel, and let `ζ` be the indicator of an open interval
`(u, v)` with `-1/2 < u < v < 1/2`, on a circle of length `L ≥ 1`. Its transport `Ψ = transportConv
β s L ζ` has the closed form `Ψ(x) = A_s (F(x - u) - F(x - v))`,
where `F` is the antiderivative of `K` vanishing at the origin. This closed form gives smoothness
of `Ψ` off the marks `u, v` (modulo `L`), and the endpoint and far-field bounds on `Ψ''` with
constants independent of `L`.
-/

public section

open MeasureTheory Set intervalIntegral Filter Topology
open scoped ContDiff Real

namespace Riesz1

/-- The distance to the lattice `L ℤ` is nonnegative. -/
lemma latticeDist_nonneg_transport (L r : ℝ) : 0 ≤ latticeDist L r := abs_nonneg _

/-- The antiderivative `F(r) = ∫_0^r K_{s,L}` of the scaled kernel, vanishing at the origin. -/
@[expose] noncomputable def kernelPrimitive (s L r : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..r, scaledKernel s L t

/-- The antiderivative has derivative `K_{s,L}` at every point off the lattice `L ℤ`. -/
lemma hasDerivAt_kernelPrimitive {s L r : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hL : 0 < L)
    (hr : ∀ k : ℤ, r ≠ k * L) : HasDerivAt (kernelPrimitive s L) (scaledKernel s L r) r :=
  intervalIntegral.integral_hasDerivAt_right (intervalIntegrable_scaledKernel hs0 hs1 hL 0 r)
    ((scaledKernel_contDiffOn hs0 hs1 hL).continuousOn.stronglyMeasurableAtFilter
      (isOpen_lattice_compl hL) r hr)
    (scaledKernel_contDiffAt hs0 hs1 hL hr).continuousAt

/-- The antiderivative is smooth off the lattice `L ℤ`. -/
lemma contDiffOn_kernelPrimitive {s L : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hL : 0 < L) :
    ContDiffOn ℝ ∞ (kernelPrimitive s L) {r : ℝ | ∀ k : ℤ, r ≠ k * L} := by
  let G : ℕ → ℝ → ℝ := fun m => match m with
    | 0 => kernelPrimitive s L
    | m + 1 => iteratedDeriv m (scaledKernel s L)
  have hG : ∀ m : ℕ, ∀ x ∈ {r : ℝ | ∀ k : ℤ, r ≠ k * L}, HasDerivAt (G m) (G (m + 1) x) x := by
    intro m x hx
    cases m with
    | zero => simpa [G] using hasDerivAt_kernelPrimitive hs0 hs1 hL hx
    | succ m => simpa [G] using hasDerivAt_iteratedDeriv_scaledKernel hs0 hs1 hL hx m
  exact contDiffOn_of_hasDerivAt_family (isOpen_lattice_compl hL) G hG 0

/-- Closed form of the transport of an interval indicator on a circle of length `L ≥ 1`:
`Ψ(x) = A_s (F(x - u) - F(x - v))`. -/
lemma transportConv_indicator {β s L u v : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hL : 1 ≤ L)
    (hu : -(1 / 2) < u) (huv : u < v) (hv : v < 1 / 2) (x : ℝ) :
    transportConv β s L ((Ioo u v).indicator (fun _ => (1 : ℝ))) x =
      transportConst β s * (kernelPrimitive s L (x - u) - kernelPrimitive s L (x - v)) := by
  have hL0 : 0 < L := by linarith
  have hsub : Ioo u v ⊆ Ioc (-(L / 2)) (L / 2) := fun y hy =>
    ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hind : ∀ y : ℝ, (Ioo u v).indicator (fun _ => (1 : ℝ)) y * scaledKernel s L (x - y) =
      (Ioo u v).indicator (fun y => scaledKernel s L (x - y)) y := by
    intro y
    by_cases hy : y ∈ Ioo u v <;> simp [hy]
  unfold transportConv
  congr 1
  simp_rw [hind]
  rw [setIntegral_indicator measurableSet_Ioo, Set.inter_eq_right.mpr hsub,
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le huv.le,
    intervalIntegral.integral_comp_sub_left (scaledKernel s L) x]
  unfold kernelPrimitive
  rw [intervalIntegral.integral_interval_sub_left
    (intervalIntegrable_scaledKernel hs0 hs1 hL0 0 (x - u))
    (intervalIntegrable_scaledKernel hs0 hs1 hL0 0 (x - v))]

/-- The transport of the interval indicator is differentiable off the marks, with derivative
`A_s (K(y - u) - K(y - v))`. -/
lemma hasDerivAt_transportConv_indicator {β s L u v : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hL : 1 ≤ L) (hu : -(1 / 2) < u) (huv : u < v) (hv : v < 1 / 2) {y : ℝ}
    (hyu : ∀ k : ℤ, y - u ≠ k * L) (hyv : ∀ k : ℤ, y - v ≠ k * L) :
    HasDerivAt (transportConv β s L ((Ioo u v).indicator (fun _ => (1 : ℝ))))
      (transportConst β s * (scaledKernel s L (y - u) - scaledKernel s L (y - v))) y := by
  have hL0 : 0 < L := by linarith
  have hfun : transportConv β s L ((Ioo u v).indicator (fun _ => (1 : ℝ))) =
      fun z => transportConst β s * (kernelPrimitive s L (z - u) - kernelPrimitive s L (z - v)) :=
    funext (transportConv_indicator hs0 hs1 hL hu huv hv)
  rw [hfun]
  have h1 := HasDerivAt.comp_sub_const y u (hasDerivAt_kernelPrimitive hs0 hs1 hL0 hyu)
  have h2 := HasDerivAt.comp_sub_const y v (hasDerivAt_kernelPrimitive hs0 hs1 hL0 hyv)
  exact (h1.sub h2).const_mul (transportConst β s)

/-- The transport of the interval indicator is `C²` off the marks. -/
lemma contDiffAt_transportConv_indicator {β s L u v : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hL : 1 ≤ L) (hu : -(1 / 2) < u) (huv : u < v) (hv : v < 1 / 2) {y : ℝ}
    (hyu : ∀ k : ℤ, y - u ≠ k * L) (hyv : ∀ k : ℤ, y - v ≠ k * L) :
    ContDiffAt ℝ 2 (transportConv β s L ((Ioo u v).indicator (fun _ => (1 : ℝ)))) y := by
  have hL0 : 0 < L := by linarith
  have hF : ∀ w : ℝ, (∀ k : ℤ, w ≠ k * L) → ContDiffAt ℝ 2 (kernelPrimitive s L) w := by
    intro w hw
    exact ((contDiffOn_kernelPrimitive hs0 hs1 hL0).contDiffAt
      ((isOpen_lattice_compl hL0).mem_nhds hw)).of_le (by simp)
  have hfun : transportConv β s L ((Ioo u v).indicator (fun _ => (1 : ℝ))) =
      fun z => transportConst β s * (kernelPrimitive s L (z - u) - kernelPrimitive s L (z - v)) :=
    funext (transportConv_indicator hs0 hs1 hL hu huv hv)
  rw [hfun]
  have hsu : ContDiffAt ℝ 2 (fun z : ℝ => kernelPrimitive s L (z - u)) y :=
    (hF (y - u) hyu).comp y (contDiffAt_id.sub contDiffAt_const)
  have hsv : ContDiffAt ℝ 2 (fun z : ℝ => kernelPrimitive s L (z - v)) y :=
    (hF (y - v) hyv).comp y (contDiffAt_id.sub contDiffAt_const)
  exact contDiffAt_const.mul (hsu.sub hsv)

/-- The second derivative of the transport of the interval indicator, off the marks. -/
lemma deriv_deriv_transportConv_indicator {β s L u v : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hL : 1 ≤ L) (hu : -(1 / 2) < u) (huv : u < v) (hv : v < 1 / 2) {y : ℝ}
    (hyu : ∀ k : ℤ, y - u ≠ k * L) (hyv : ∀ k : ℤ, y - v ≠ k * L) :
    deriv (deriv (transportConv β s L ((Ioo u v).indicator (fun _ => (1 : ℝ))))) y =
      transportConst β s * (deriv (scaledKernel s L) (y - u) - deriv (scaledKernel s L) (y - v)) := by
  have hL0 : 0 < L := by linarith
  have ho : IsOpen {z : ℝ | (∀ k : ℤ, z - u ≠ k * L) ∧ (∀ k : ℤ, z - v ≠ k * L)} :=
    ((isOpen_lattice_compl hL0).preimage (continuous_id.sub continuous_const)).inter
      ((isOpen_lattice_compl hL0).preimage (continuous_id.sub continuous_const))
  have hev : ∀ᶠ z in 𝓝 y, deriv (transportConv β s L ((Ioo u v).indicator (fun _ => (1 : ℝ)))) z =
      transportConst β s * (scaledKernel s L (z - u) - scaledKernel s L (z - v)) := by
    filter_upwards [ho.mem_nhds ⟨hyu, hyv⟩] with z hz
    exact (hasDerivAt_transportConv_indicator hs0 hs1 hL hu huv hv hz.1 hz.2).deriv
  rw [Filter.EventuallyEq.deriv_eq hev]
  have hKu : HasDerivAt (fun z : ℝ => scaledKernel s L (z - u)) (deriv (scaledKernel s L) (y - u)) y :=
    HasDerivAt.comp_sub_const y u
      ((scaledKernel_contDiffAt hs0 hs1 hL0 hyu).differentiableAt (by simp)).hasDerivAt
  have hKv : HasDerivAt (fun z : ℝ => scaledKernel s L (z - v)) (deriv (scaledKernel s L) (y - v)) y :=
    HasDerivAt.comp_sub_const y v
      ((scaledKernel_contDiffAt hs0 hs1 hL0 hyv).differentiableAt (by simp)).hasDerivAt
  exact ((hKu.sub hKv).const_mul (transportConst β s)).deriv

/-- The first derivative of the scaled kernel is bounded by `C |r|_L^{s-2}`, with `C` independent
of `L`. -/
lemma exists_norm_deriv_scaledKernel_le {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ L r : ℝ, 0 < L → (∀ k : ℤ, r ≠ k * L) →
      ‖deriv (scaledKernel s L) r‖ ≤ C * latticeDist L r ^ (s - 2) := by
  obtain ⟨C, hC, hb⟩ := norm_iteratedDeriv_scaledKernel_le hs0 hs1 (m := 1) le_rfl
  refine ⟨C, hC, fun L r hL hr => ?_⟩
  have h := hb L r hL hr
  rw [iteratedDeriv_one] at h
  have e : s - 1 - ((1 : ℕ) : ℝ) = s - 2 := by push_cast; ring
  rwa [e] at h

/-- The second derivative of the scaled kernel is bounded by `C |r|_L^{s-3}`, with `C` independent
of `L`. -/
lemma exists_norm_iteratedDeriv_two_scaledKernel_le {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ L r : ℝ, 0 < L → (∀ k : ℤ, r ≠ k * L) →
      ‖iteratedDeriv 2 (scaledKernel s L) r‖ ≤ C * latticeDist L r ^ (s - 3) := by
  obtain ⟨C, hC, hb⟩ := norm_iteratedDeriv_scaledKernel_le hs0 hs1 (m := 2) (by norm_num)
  refine ⟨C, hC, fun L r hL hr => ?_⟩
  have e : s - 1 - ((2 : ℕ) : ℝ) = s - 3 := by push_cast; ring
  rw [← e]
  exact hb L r hL hr

/-- Mean value estimate for the derivative of the scaled kernel across the two marks `u` and `v`,
at a point `y` whose distance to the lattice is at least one. The segment between `y - u` and
`y - v` stays at distance at least `latticeDist L y / 2` from the lattice. -/
lemma norm_deriv_scaledKernel_sub_le {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {C2 : ℝ} (hC2 : 0 < C2)
    (hb2 : ∀ L r : ℝ, 0 < L → (∀ k : ℤ, r ≠ k * L) →
      ‖iteratedDeriv 2 (scaledKernel s L) r‖ ≤ C2 * latticeDist L r ^ (s - 3))
    {L u v y : ℝ} (hL : 1 ≤ L) (hu : -(1 / 2) < u) (huv : u < v) (hv : v < 1 / 2)
    (hy : 1 ≤ latticeDist L y) :
    ‖deriv (scaledKernel s L) (y - u) - deriv (scaledKernel s L) (y - v)‖ ≤
      C2 * (latticeDist L y / 2) ^ (s - 3) * (v - u) := by
  have hL0 : 0 < L := by linarith
  have hseg : ∀ t ∈ uIcc (y - u) (y - v), |t - y| ≤ 1 / 2 := by
    intro t ht
    rw [Set.mem_uIcc] at ht
    rw [abs_le]
    rcases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> constructor <;> linarith
  have hd_seg : ∀ t ∈ uIcc (y - u) (y - v), latticeDist L y / 2 ≤ latticeDist L t := by
    intro t ht
    have h1 := latticeDist_lipschitz L t y hL0
    have h2 := hseg t ht
    linarith
  have hoff : ∀ t ∈ uIcc (y - u) (y - v), ∀ k : ℤ, t ≠ k * L := by
    intro t ht k hk
    have h0 : latticeDist L t = 0 := by
      rw [hk]
      simp only [latticeDist, mul_div_cancel_right₀ _ hL0.ne', round_intCast]
      rw [show (k : ℝ) * L - L * k = 0 by ring]
      simp
    have := hd_seg t ht
    linarith
  have hdiff : ∀ t ∈ uIcc (y - u) (y - v),
      HasDerivAt (iteratedDeriv 1 (scaledKernel s L)) (iteratedDeriv 2 (scaledKernel s L) t) t := by
    intro t ht
    simpa using hasDerivAt_iteratedDeriv_scaledKernel hs0 hs1 hL0 (hoff t ht) 1
  have hbound : ∀ t ∈ uIcc (y - u) (y - v),
      ‖deriv (iteratedDeriv 1 (scaledKernel s L)) t‖ ≤ C2 * (latticeDist L y / 2) ^ (s - 3) := by
    intro t ht
    rw [(hdiff t ht).deriv]
    refine le_trans (hb2 L t hL0 (hoff t ht)) ?_
    apply mul_le_mul_of_nonneg_left _ hC2.le
    exact Real.rpow_le_rpow_of_nonpos (by linarith [hy]) (hd_seg t ht) (by linarith)
  have hMVT := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun t ht => (hdiff t ht).differentiableAt) hbound (convex_uIcc _ _)
    (right_mem_uIcc (a := y - u) (b := y - v)) (left_mem_uIcc (a := y - u) (b := y - v))
  have hlen : ‖(y - u) - (y - v)‖ = v - u := by
    rw [show (y - u) - (y - v) = v - u by ring, Real.norm_eq_abs, abs_of_pos (by linarith)]
  rw [hlen, iteratedDeriv_one] at hMVT
  exact hMVT

/-- Uniform bounds on the second derivative of the transport of an interval indicator, with one
constant for every circle of length `L ≥ 1`. Near the marks, `|Ψ''(y)|` is bounded by a sum of
powers `|y - u|_L^{s-2}` and `|y - v|_L^{s-2}`, where `|·|_L` is the distance to `L ℤ`. At distance
at least one from the origin, `|Ψ''(y)| ≤ C |y|_L^{s-3}`. -/
theorem transportConv_indicator_second_deriv_bound {β s : ℝ} (hβ : 0 < β) (hs0 : 0 < s)
    (hs1 : s < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L u v : ℝ), 1 ≤ L → -(1 / 2) < u → u < v → v < 1 / 2 →
      ∀ y : ℝ, (∀ k : ℤ, y - u ≠ k * L) → (∀ k : ℤ, y - v ≠ k * L) →
        |deriv (deriv (transportConv β s L ((Ioo u v).indicator (fun _ => (1 : ℝ))))) y| ≤
            C * (latticeDist L (y - u) ^ (s - 2) + latticeDist L (y - v) ^ (s - 2)) ∧
          (1 ≤ latticeDist L y →
            |deriv (deriv (transportConv β s L ((Ioo u v).indicator (fun _ => (1 : ℝ))))) y| ≤
              C * latticeDist L y ^ (s - 3)) := by
  obtain ⟨C1, hC1, hb1⟩ := exists_norm_deriv_scaledKernel_le hs0 hs1
  obtain ⟨C2, hC2, hb2⟩ := exists_norm_iteratedDeriv_two_scaledKernel_le hs0 hs1
  have hA : 0 < |transportConst β s| := abs_pos.2 (transportConst_ne_zero hβ hs0 hs1)
  have hpow : 0 < (1 / 2 : ℝ) ^ (s - 3) := by positivity
  refine ⟨|transportConst β s| * (C1 + C2 * (1 / 2) ^ (s - 3)), by positivity, ?_⟩
  intro L u v hL hu huv hv y hyu hyv
  have hL0 : 0 < L := by linarith
  have hA' : (deriv (deriv (transportConv β s L ((Ioo u v).indicator (fun _ => (1 : ℝ))))) y) =
      transportConst β s * (deriv (scaledKernel s L) (y - u) - deriv (scaledKernel s L) (y - v)) :=
    deriv_deriv_transportConv_indicator hs0 hs1 hL hu huv hv hyu hyv
  rw [hA', abs_mul]
  have hnear : |deriv (scaledKernel s L) (y - u) - deriv (scaledKernel s L) (y - v)| ≤
      C1 * (latticeDist L (y - u) ^ (s - 2) + latticeDist L (y - v) ^ (s - 2)) := by
    have h1 := hb1 L (y - u) hL0 hyu
    have h2 := hb1 L (y - v) hL0 hyv
    rw [← Real.norm_eq_abs]
    calc ‖deriv (scaledKernel s L) (y - u) - deriv (scaledKernel s L) (y - v)‖
        ≤ ‖deriv (scaledKernel s L) (y - u)‖ + ‖deriv (scaledKernel s L) (y - v)‖ := norm_sub_le _ _
      _ ≤ C1 * latticeDist L (y - u) ^ (s - 2) + C1 * latticeDist L (y - v) ^ (s - 2) :=
          add_le_add h1 h2
      _ = C1 * (latticeDist L (y - u) ^ (s - 2) + latticeDist L (y - v) ^ (s - 2)) := by ring
  constructor
  · have hsum : 0 ≤ latticeDist L (y - u) ^ (s - 2) + latticeDist L (y - v) ^ (s - 2) :=
      add_nonneg (Real.rpow_nonneg (latticeDist_nonneg_transport _ _) _)
        (Real.rpow_nonneg (latticeDist_nonneg_transport _ _) _)
    calc |transportConst β s| * |deriv (scaledKernel s L) (y - u) - deriv (scaledKernel s L) (y - v)|
        ≤ |transportConst β s| * (C1 * (latticeDist L (y - u) ^ (s - 2) +
            latticeDist L (y - v) ^ (s - 2))) := mul_le_mul_of_nonneg_left hnear hA.le
      _ ≤ |transportConst β s| * (C1 + C2 * (1 / 2) ^ (s - 3)) *
            (latticeDist L (y - u) ^ (s - 2) + latticeDist L (y - v) ^ (s - 2)) := by
          have : 0 ≤ |transportConst β s| * (C2 * (1 / 2) ^ (s - 3)) *
              (latticeDist L (y - u) ^ (s - 2) + latticeDist L (y - v) ^ (s - 2)) :=
            mul_nonneg (mul_nonneg hA.le (mul_nonneg hC2.le hpow.le)) hsum
          nlinarith
  · intro hy
    have hd0 : 0 ≤ latticeDist L y := by linarith
    have hfar := norm_deriv_scaledKernel_sub_le hs0 hs1 hC2 hb2 hL hu huv hv hy
    have hsplit : (latticeDist L y / 2) ^ (s - 3) = (1 / 2) ^ (s - 3) * latticeDist L y ^ (s - 3) := by
      rw [← Real.mul_rpow (by norm_num) hd0]
      congr 1
      ring
    have hvu : v - u ≤ 1 := by linarith
    have hnorm : ‖deriv (scaledKernel s L) (y - u) - deriv (scaledKernel s L) (y - v)‖ ≤
        C2 * (1 / 2) ^ (s - 3) * latticeDist L y ^ (s - 3) := by
      refine le_trans hfar ?_
      rw [hsplit]
      have hdpow : 0 ≤ latticeDist L y ^ (s - 3) :=
        Real.rpow_nonneg (latticeDist_nonneg_transport _ _) _
      calc C2 * ((1 / 2) ^ (s - 3) * latticeDist L y ^ (s - 3)) * (v - u)
          ≤ C2 * ((1 / 2) ^ (s - 3) * latticeDist L y ^ (s - 3)) * 1 :=
            mul_le_mul_of_nonneg_left hvu (mul_nonneg hC2.le (mul_nonneg hpow.le hdpow))
        _ = C2 * (1 / 2) ^ (s - 3) * latticeDist L y ^ (s - 3) := by ring
    calc |transportConst β s| * |deriv (scaledKernel s L) (y - u) - deriv (scaledKernel s L) (y - v)|
        ≤ |transportConst β s| * (C2 * (1 / 2) ^ (s - 3) * latticeDist L y ^ (s - 3)) := by
          rw [← Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left hnorm hA.le
      _ ≤ |transportConst β s| * (C1 + C2 * (1 / 2) ^ (s - 3)) * latticeDist L y ^ (s - 3) := by
          have hdpow : 0 ≤ latticeDist L y ^ (s - 3) :=
            Real.rpow_nonneg (latticeDist_nonneg_transport _ _) _
          have hC1pos : 0 ≤ |transportConst β s| * C1 * latticeDist L y ^ (s - 3) :=
            mul_nonneg (mul_nonneg hA.le hC1.le) hdpow
          nlinarith

end Riesz1

end
