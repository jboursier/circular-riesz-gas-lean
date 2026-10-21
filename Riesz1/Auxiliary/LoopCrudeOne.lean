/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopArcsLambda
public import Riesz1.Auxiliary.LoopArcsDerivs
public import Riesz1.Auxiliary.LoopArcsBounds
public import Riesz1.Auxiliary.LoopArcsIdentity

/-!
# The crude microscopic loop bound for one particle

The crude part of Lemma 5.8, case `N = 1`: for one particle the loop functional is a
deterministic quantity bounded by a constant times the sup of `|b'|` over the period. The
arc decomposition needs `N ≥ 2`, so this case is proved directly from the singular kernel.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Finset

namespace Riesz1

/-- **Kernel derivative on the circle.** For `0 < s < 1` there is `C > 0` such that for every
real `x` that is not an integer, `|g_1'(x)| ≤ C d^{-s-1}`, where `d` is the fractional part of `x`
if it is at most `1/2` and one minus it otherwise. -/
theorem loopCrudeOne_deriv_fract {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 0 < Int.fract x →
      (Int.fract x ≤ 1 / 2 → |deriv (loopArcG s 1) x| ≤ C * (Int.fract x) ^ (-s - 1)) ∧
      (1 / 2 < Int.fract x → |deriv (loopArcG s 1) x| ≤ C * (1 - Int.fract x) ^ (-s - 1)) := by
  obtain ⟨C, hC, hb⟩ := norm_deriv_loopArcG_le s hs0 hs1 1
  have hper : Function.Periodic (deriv (loopArcG s 1)) 1 := by
    simpa using deriv_periodic_of (loopArcG_periodic s 1)
  have hfr : ∀ x : ℝ, deriv (loopArcG s 1) x = deriv (loopArcG s 1) (Int.fract x) := by
    intro x
    have h := hper.sub_int_mul_eq (x := x) ⌊x⌋
    rw [mul_one] at h
    rw [← h]
    rfl
  have hhalf : ((1 : ℕ+) : ℝ) / 2 = 1 / 2 := by simp
  refine ⟨C, hC, fun x hx0 => ⟨fun hle => ?_, fun hgt => ?_⟩⟩
  · rw [hfr x]
    exact hb _ hx0 (by rw [hhalf]; exact hle)
  · have hlt := Int.fract_lt_one x
    have h2 : deriv (loopArcG s 1) (Int.fract x) = deriv (loopArcG s 1) (-(1 - Int.fract x)) := by
      have h := hper (-(1 - Int.fract x))
      rw [show -(1 - Int.fract x) + 1 = Int.fract x by ring] at h
      exact h
    rw [hfr x, h2, deriv_loopArcG_neg, abs_neg]
    exact hb _ (by linarith) (by rw [hhalf]; linarith)

/-- A `1`-periodic function whose derivative is bounded by `M` on `[0,1]` has derivative bounded
by `M` on the whole real line. -/
theorem loopCrudeOne_deriv_le {b : ℝ → ℝ} {M : ℝ} (hper : Function.Periodic b 1)
    (hM : ∀ z ∈ Icc (0 : ℝ) 1, |deriv b z| ≤ M) (x : ℝ) : |deriv b x| ≤ M := by
  have hd : Function.Periodic (deriv b) 1 := deriv_periodic_of hper
  have h := hd.sub_int_mul_eq (x := x) ⌊x⌋
  rw [mul_one] at h
  have h2 : deriv b x = deriv b (Int.fract x) := by
    rw [← h]
    rfl
  rw [h2]
  exact hM _ ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩

/-- A differentiable function with derivative bounded by `M` everywhere is `M`-Lipschitz. -/
theorem loopCrudeOne_lip {b : ℝ → ℝ} {M : ℝ} (hb : ContDiff ℝ 1 b)
    (hM : ∀ x, |deriv b x| ≤ M) (x y : ℝ) : |b y - b x| ≤ M * |y - x| := by
  have hdiff : ∀ x, DifferentiableAt ℝ b x := fun x => hb.differentiable one_ne_zero x
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (s := Set.univ) (f := b)
    (fun x _ => hdiff x) (fun x _ => by simpa using hM x) convex_univ (Set.mem_univ x)
    (Set.mem_univ y)
  simpa using h

/-- Two increments of a `1`-periodic Lipschitz function: for `0 ≤ y ≤ 1`, the increment
`b (v + y) - b v` is at most `M y` and at most `M (1 - y)`, the latter by periodicity. -/
theorem loopCrudeOne_step {b : ℝ → ℝ} {M : ℝ} (hb : ContDiff ℝ 1 b)
    (hper : Function.Periodic b 1) (hM : ∀ x, |deriv b x| ≤ M) (v y : ℝ) (hy0 : 0 ≤ y)
    (hy1 : y ≤ 1) : |b (v + y) - b v| ≤ M * y ∧ |b (v + y) - b v| ≤ M * (1 - y) := by
  constructor
  · have h := loopCrudeOne_lip hb hM v (v + y)
    rwa [add_sub_cancel_left, abs_of_nonneg hy0] at h
  · have h := loopCrudeOne_lip hb hM (v + 1) (v + y)
    have h1 : b (v + 1) = b v := hper v
    have h2 : v + y - (v + 1) = -(1 - y) := by ring
    rwa [h1, h2, abs_neg, abs_of_nonneg (show (0 : ℝ) ≤ 1 - y by linarith)] at h

/-- Periodic Lipschitz bound: for all real `z, u`, `|b z - b u|` is at most `M` times the
fractional part of `z - u` and at most `M` times one minus that fractional part. -/
theorem loopCrudeOne_sub_le {b : ℝ → ℝ} {M : ℝ} (hb : ContDiff ℝ 1 b)
    (hper : Function.Periodic b 1) (hM : ∀ x, |deriv b x| ≤ M) (z u : ℝ) :
    |b z - b u| ≤ M * Int.fract (z - u) ∧ |b z - b u| ≤ M * (1 - Int.fract (z - u)) := by
  have hy0 := Int.fract_nonneg (z - u)
  have hy1 := Int.fract_lt_one (z - u)
  have hbv : b (u + (⌊z - u⌋ : ℤ)) = b u := by
    simpa using hper.int_mul ⌊z - u⌋ u
  have hz : z = (u + (⌊z - u⌋ : ℤ)) + Int.fract (z - u) := by
    have h := Int.floor_add_fract (z - u)
    linarith
  have key := loopCrudeOne_step hb hper hM (u + (⌊z - u⌋ : ℤ)) (Int.fract (z - u)) hy0 hy1.le
  rw [hbv] at key
  have e : u + (⌊z - u⌋ : ℤ) + Int.fract (z - u) = z := hz.symm
  rw [e] at key
  exact key

/-- For `t > 0`, `t * t^{-s-1} = t^{-s}`. -/
theorem loopCrudeOne_mul_rpow {s t : ℝ} (ht : 0 < t) : t * t ^ (-s - 1) = t ^ (-s) := by
  have h := Real.rpow_add_one ht.ne' (-s - 1)
  rw [show -s - 1 + 1 = -s by ring] at h
  rw [h]
  ring

/-- **Pointwise kernel bound for one particle.** There is `C > 0` such that for every
`1`-periodic `C^1` function `b` with `|b'| ≤ M` and every `z, u` with `z - u` not an integer,
`|(b z - b u) g_1'(z - u)| ≤ C M (y^{-s} + (1 - y)^{-s})`, where `y` is the fractional part of
`z - u`. -/
theorem loopCrudeOne_kernel_le {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (b : ℝ → ℝ) (M : ℝ), ContDiff ℝ 1 b → Function.Periodic b 1 →
      (∀ x, |deriv b x| ≤ M) → ∀ z u : ℝ, 0 < Int.fract (z - u) →
        |loopArcKernel s 1 b z u| ≤
          C * M * (Int.fract (z - u) ^ (-s) + (1 - Int.fract (z - u)) ^ (-s)) := by
  obtain ⟨C, hC, hd⟩ := loopCrudeOne_deriv_fract hs0 hs1
  refine ⟨C, hC, fun b M hb hper hM z u hy => ?_⟩
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  have hy1 := Int.fract_lt_one (z - u)
  obtain ⟨hD1, hD2⟩ := loopCrudeOne_sub_le hb hper hM z u
  obtain ⟨hG1, hG2⟩ := hd (z - u) hy
  have hpos1 : 0 ≤ (Int.fract (z - u)) ^ (-s) := Real.rpow_nonneg hy.le _
  have hpos2 : 0 ≤ (1 - Int.fract (z - u)) ^ (-s) := Real.rpow_nonneg (by linarith) _
  have hCM : 0 ≤ C * M := mul_nonneg hC.le hM0
  unfold loopArcKernel
  rw [abs_mul]
  by_cases hcase : Int.fract (z - u) ≤ 1 / 2
  · have hG := hG1 hcase
    have h1 : |b z - b u| * |deriv (loopArcG s 1) (z - u)| ≤
        (M * Int.fract (z - u)) * (C * Int.fract (z - u) ^ (-s - 1)) :=
      mul_le_mul hD1 hG (abs_nonneg _) (mul_nonneg hM0 hy.le)
    have h2 : (M * Int.fract (z - u)) * (C * Int.fract (z - u) ^ (-s - 1)) =
        C * M * Int.fract (z - u) ^ (-s) := by
      rw [← loopCrudeOne_mul_rpow (s := s) hy]
      ring
    rw [h2] at h1
    nlinarith
  · have hgt : 1 / 2 < Int.fract (z - u) := lt_of_not_ge hcase
    have hG := hG2 hgt
    have hy2 : 0 < 1 - Int.fract (z - u) := by linarith
    have h1 : |b z - b u| * |deriv (loopArcG s 1) (z - u)| ≤
        (M * (1 - Int.fract (z - u))) * (C * (1 - Int.fract (z - u)) ^ (-s - 1)) :=
      mul_le_mul hD2 hG (abs_nonneg _) (mul_nonneg hM0 hy2.le)
    have h2 : (M * (1 - Int.fract (z - u))) * (C * (1 - Int.fract (z - u)) ^ (-s - 1)) =
        C * M * (1 - Int.fract (z - u)) ^ (-s) := by
      rw [← loopCrudeOne_mul_rpow (s := s) hy2]
      ring
    rw [h2] at h1
    nlinarith

/-- The majorant `y ↦ y^{-s} + (1 - y)^{-s}` of the fractional part is `1`-periodic. -/
theorem loopCrudeOne_maj_periodic (s : ℝ) :
    Function.Periodic (fun x : ℝ => Int.fract x ^ (-s) + (1 - Int.fract x) ^ (-s)) 1 := by
  intro x
  simp only [Int.fract_add_one]

/-- For `s < 1` the periodic majorant is integrable on every bounded interval. -/
theorem loopCrudeOne_maj_integrable {s : ℝ} (hs1 : s < 1) (a b : ℝ) :
    IntervalIntegrable (fun x : ℝ => Int.fract x ^ (-s) + (1 - Int.fract x) ^ (-s))
      MeasureTheory.volume a b := by
  have h1 : IntervalIntegrable (fun x : ℝ => x ^ (-s)) MeasureTheory.volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have h2 : IntervalIntegrable (fun x : ℝ => (1 - x) ^ (-s)) MeasureTheory.volume 0 1 := by
    have := (intervalIntegral.intervalIntegrable_rpow' (a := 1) (b := 0) (r := -s)
      (by linarith)).comp_sub_left 1
    simpa using this
  have h3 := h1.add h2
  have h4 : IntervalIntegrable (fun x : ℝ => Int.fract x ^ (-s) + (1 - Int.fract x) ^ (-s))
      MeasureTheory.volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one]
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one] at h3
    refine h3.congr_fun (fun x hx => ?_) measurableSet_Ioo
    have : Int.fract x = x := Int.fract_eq_self.mpr ⟨hx.1.le, hx.2⟩
    simp [this]
  exact (loopCrudeOne_maj_periodic s).intervalIntegrable one_ne_zero (t := 0)
    (by simpa using h4) a b

/-- If `|F z u|` is bounded by `A` times the periodic majorant of `z - u` whenever `z - u` is not
an integer, then the integral of `F z` over `u ∈ [0,1]` is bounded by `A` times the integral of the
majorant over one period, uniformly in `z`. -/
theorem loopCrudeOne_integral_u {s : ℝ} (hs1 : s < 1) {A : ℝ} {F : ℝ → ℝ → ℝ}
    (hF : ∀ z u : ℝ, 0 < Int.fract (z - u) →
      |F z u| ≤ A * (Int.fract (z - u) ^ (-s) + (1 - Int.fract (z - u)) ^ (-s))) (z : ℝ) :
    |∫ u in (0 : ℝ)..1, F z u| ≤
      A * ∫ x in (0 : ℝ)..1, (Int.fract x ^ (-s) + (1 - Int.fract x) ^ (-s)) := by
  have hint : IntervalIntegrable
      (fun u : ℝ => A * (Int.fract (z - u) ^ (-s) + (1 - Int.fract (z - u)) ^ (-s)))
      MeasureTheory.volume 0 1 := by
    have := (loopCrudeOne_maj_integrable hs1 z (z - 1)).comp_sub_left z
    have h2 := this.const_mul A
    simpa using h2
  have hae : ∀ᵐ u : ℝ, u ∈ Ioc (0 : ℝ) 1 →
      ‖F z u‖ ≤ A * (Int.fract (z - u) ^ (-s) + (1 - Int.fract (z - u)) ^ (-s)) := by
    have hcount : {u : ℝ | Int.fract (z - u) = 0}.Countable := by
      refine (Set.countable_range (fun n : ℤ => z - (n : ℝ))).mono ?_
      intro u hu
      obtain ⟨n, hn⟩ := Int.fract_eq_zero_iff.mp hu
      exact ⟨n, by simp only; linarith⟩
    filter_upwards [hcount.ae_notMem MeasureTheory.volume] with u hu _
    have hpos : 0 < Int.fract (z - u) :=
      lt_of_le_of_ne (Int.fract_nonneg _) (fun h => hu h.symm)
    simpa [Real.norm_eq_abs] using hF z u hpos
  have h1 := intervalIntegral.norm_integral_le_of_norm_le zero_le_one hae hint
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_sub_left
    (fun x : ℝ => Int.fract x ^ (-s) + (1 - Int.fract x) ^ (-s)) z] at h1
  have h2 := (loopCrudeOne_maj_periodic s).intervalIntegral_add_eq (z - 1) 0
  rw [show z - 1 + 1 = z - 0 by ring, zero_add] at h2
  rw [Real.norm_eq_abs] at h1
  rw [h2] at h1
  exact h1

/-- The same bound as for the `u`-integral, for the integral of `F · u` over `z ∈ [0,1]`,
uniformly in `u`. -/
theorem loopCrudeOne_integral_z {s : ℝ} (hs1 : s < 1) {A : ℝ} {F : ℝ → ℝ → ℝ}
    (hF : ∀ z u : ℝ, 0 < Int.fract (z - u) →
      |F z u| ≤ A * (Int.fract (z - u) ^ (-s) + (1 - Int.fract (z - u)) ^ (-s))) (u : ℝ) :
    |∫ z in (0 : ℝ)..1, F z u| ≤
      A * ∫ x in (0 : ℝ)..1, (Int.fract x ^ (-s) + (1 - Int.fract x) ^ (-s)) := by
  have hint : IntervalIntegrable
      (fun z : ℝ => A * (Int.fract (z - u) ^ (-s) + (1 - Int.fract (z - u)) ^ (-s)))
      MeasureTheory.volume 0 1 := by
    have := (loopCrudeOne_maj_integrable hs1 (-u) (1 - u)).comp_sub_right u
    have h2 := this.const_mul A
    simpa using h2
  have hae : ∀ᵐ z : ℝ, z ∈ Ioc (0 : ℝ) 1 →
      ‖F z u‖ ≤ A * (Int.fract (z - u) ^ (-s) + (1 - Int.fract (z - u)) ^ (-s)) := by
    have hcount : {z : ℝ | Int.fract (z - u) = 0}.Countable := by
      refine (Set.countable_range (fun n : ℤ => u + (n : ℝ))).mono ?_
      intro z hz
      obtain ⟨n, hn⟩ := Int.fract_eq_zero_iff.mp hz
      exact ⟨n, by simp only; linarith⟩
    filter_upwards [hcount.ae_notMem MeasureTheory.volume] with z hz _
    have hpos : 0 < Int.fract (z - u) :=
      lt_of_le_of_ne (Int.fract_nonneg _) (fun h => hz h.symm)
    simpa [Real.norm_eq_abs] using hF z u hpos
  have h1 := intervalIntegral.norm_integral_le_of_norm_le zero_le_one hae hint
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_sub_right
    (fun x : ℝ => Int.fract x ^ (-s) + (1 - Int.fract x) ^ (-s)) u] at h1
  have h2 := (loopCrudeOne_maj_periodic s).intervalIntegral_add_eq (0 - u) 0
  rw [show 0 - u + 1 = 1 - u by ring, zero_add] at h2
  rw [Real.norm_eq_abs, h2] at h1
  exact h1

/-- A sum over the single index of `Fin 1` of terms bounded by `B` is bounded by `B`. -/
theorem loopCrudeOne_sum_le {f : Fin ((1 : ℕ+) : ℕ) → ℝ} {B : ℝ} (hf : ∀ i, |f i| ≤ B) :
    |∑ i, f i| ≤ B := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ B (fun i _ => hf i)).trans ?_
  rw [Finset.card_univ, Fintype.card_fin, PNat.one_coe, one_smul]

/-- **Crude bound for one particle.** For `0 < s < 1` there is `C ≥ 0` such that for every
smooth real `1`-periodic `b`, every `M` bounding `|b'|` on `[0,1]`, and every configuration,
`|L(b)| ≤ C M`. -/
theorem loopArcL_one_abs_le {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (b : ℝ → ℝ) (M : ℝ), ContDiff ℝ 1 b → Function.Periodic b 1 →
      (∀ z ∈ Icc (0 : ℝ) 1, |deriv b z| ≤ M) → ∀ X : Configuration 1,
        |loopArcL s 1 b X| ≤ C * M := by
  obtain ⟨C₁, hC₁, hK⟩ := loopCrudeOne_kernel_le hs0 hs1
  have hI0 : 0 ≤ ∫ x in (0 : ℝ)..1, (Int.fract x ^ (-s) + (1 - Int.fract x) ^ (-s)) :=
    intervalIntegral.integral_nonneg zero_le_one (fun x _ =>
      add_nonneg (Real.rpow_nonneg (Int.fract_nonneg x) _)
        (Real.rpow_nonneg (by linarith [Int.fract_lt_one x]) _))
  refine ⟨3 * C₁ * ∫ x in (0 : ℝ)..1, (Int.fract x ^ (-s) + (1 - Int.fract x) ^ (-s)),
    by positivity, fun b M hb hper hM X => ?_⟩
  have hM' := loopCrudeOne_deriv_le hper hM
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0 ⟨le_rfl, zero_le_one⟩)
  have hF : ∀ z u : ℝ, 0 < Int.fract (z - u) →
      |loopArcKernel s 1 b z u| ≤ (C₁ * M) *
        (Int.fract (z - u) ^ (-s) + (1 - Int.fract (z - u)) ^ (-s)) := by
    intro z u hy
    have := hK b M hb hper hM' z u hy
    linarith
  set I := ∫ x in (0 : ℝ)..1, (Int.fract x ^ (-s) + (1 - Int.fract x) ^ (-s)) with hI
  have hu : ∀ z : ℝ, |∫ u in (0 : ℝ)..1, loopArcKernel s 1 b z u| ≤ (C₁ * M) * I :=
    fun z => loopCrudeOne_integral_u hs1 hF z
  have hz : ∀ u : ℝ, |∫ z in (0 : ℝ)..1, loopArcKernel s 1 b z u| ≤ (C₁ * M) * I :=
    fun u => loopCrudeOne_integral_z hs1 hF u
  have hcast : (((1 : ℕ+) : ℕ) : ℝ) = 1 := by simp
  have hsub : Subsingleton (Fin ((1 : ℕ+) : ℕ)) := inferInstanceAs (Subsingleton (Fin 1))
  unfold loopArcL
  simp only [hcast]
  have h0 : (∑ i : Fin ((1 : ℕ+) : ℕ), ∑ j : Fin ((1 : ℕ+) : ℕ),
      if j = i then 0 else loopArcKernel s 1 b (loopArcPos 1 X i) (loopArcPos 1 X j)) = 0 := by
    refine Finset.sum_eq_zero (fun i _ => Finset.sum_eq_zero (fun j _ => ?_))
    obtain rfl : j = i := Subsingleton.elim j i
    exact ite_eq_left_iff.mpr fun h => (h rfl).elim
  have h1 : |∑ i : Fin ((1 : ℕ+) : ℕ), ∫ u in (0 : ℝ)..1,
      loopArcKernel s 1 b (loopArcPos 1 X i) u| ≤ (C₁ * M) * I :=
    loopCrudeOne_sum_le (fun i => hu _)
  have h2 : |∑ i : Fin ((1 : ℕ+) : ℕ), ∫ z in (0 : ℝ)..1,
      loopArcKernel s 1 b z (loopArcPos 1 X i)| ≤ (C₁ * M) * I :=
    loopCrudeOne_sum_le (fun i => hz _)
  have h3 : |∫ z in (0 : ℝ)..1, ∫ u in (0 : ℝ)..1, loopArcKernel s 1 b z u| ≤ (C₁ * M) * I := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
      (f := fun z : ℝ => ∫ u in (0 : ℝ)..1, loopArcKernel s 1 b z u) (C := (C₁ * M) * I)
      (fun z _ => by simpa [Real.norm_eq_abs] using hu z)
    simpa using this
  rw [h0, zero_sub]
  have a1 := abs_le.mp h1
  have a2 := abs_le.mp h2
  have a3 := abs_le.mp h3
  rw [abs_le]
  constructor <;> nlinarith

end Riesz1

end
end
