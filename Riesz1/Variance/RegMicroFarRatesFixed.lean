/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.RegMicroFarRatesMoving

/-!
# Fixed marked cutoffs preserve the microscopic far rate

The fixed transition in Lemma 5.3. The input `g` can
be the actual moving-cutoff error. This internal calculus lemma consumes
its derivative envelope and its fixed-region value estimate. It does
not assume a variance estimate.
-/

public section

open Set

namespace Riesz1.Internal

/-- The marked fixed cutoff converts the nearest-mark envelope into
the envelope centered at the selected mark. Constants are uniform in
the microscopic radius and the circle. -/
theorem regMicro_fixed_deriv_bound (n : ℕ+) :
    ∃ D : ℝ, 0 < D ∧ ∀ (L r₀ h : ℝ), 0 < L → 0 < r₀ → 4*r₀ < L →
      2*r₀ ≤ 1 → 0 < h → h ≤ r₀ → h ≤ 1 →
      ∀ (a : Fin (n : ℕ) → ℝ),
        (∀ i j, i ≠ j → 4*r₀ ≤ dist (a i : AddCircle L) (a j : AddCircle L)) →
      ∀ (s q A B : ℝ), 0 ≤ s → 0 ≤ q → 0 ≤ A → 0 ≤ B →
      ∀ (g : AddCircle L → ℝ) (x : ℝ),
        DifferentiableAt ℝ (fun t : ℝ => g (t : AddCircle L)) x →
        (|deriv (fun t : ℝ => g (t : AddCircle L)) x| ≤
          A*h^(1-s)*(max (cappedMarkDistance (fun j => (a j : AddCircle L))
            (x : AddCircle L)) h)^(-q)) →
        (r₀ ≤ cappedMarkDistance (fun j => (a j : AddCircle L)) (x : AddCircle L) →
          |g (x : AddCircle L)| ≤ B*h) →
      ∀ j, |deriv (fun t : ℝ =>
          microCutoffSum L r₀ (fun _ : Unit => a j) (t : AddCircle L)*g (t : AddCircle L)) x| ≤
        (A+D/r₀*B*(2*r₀)^q)*h^(1-s)*
          (max (dist (x : AddCircle L) (a j : AddCircle L)) h)^(-q) := by
  obtain ⟨D, hD, hb⟩ := microCutoffSum_deriv_bound (ι := Unit)
  refine ⟨D, hD, fun L r₀ h hL hr₀ hrL hr1 hh hhr hh1 a hsep s q A B hs hq hA hB g x hg hder hval j => ?_⟩
  let χ := fun t : ℝ => microCutoffSum L r₀ (fun _ : Unit => a j) (t : AddCircle L)
  let d := dist (x : AddCircle L) (a j : AddCircle L)
  let z := max d h
  have hz : 0 < z := lt_of_lt_of_le hh (le_max_right _ _)
  have hχsep : ∀ i k : Unit, i ≠ k →
      4*r₀ ≤ dist ((fun _ : Unit => a j) i : AddCircle L)
        ((fun _ : Unit => a j) k : AddCircle L) := fun i k hik => (hik (Subsingleton.elim i k)).elim
  have hc := microCutoffSum_mem_Icc hr₀ (fun _ : Unit => a j) hχsep (x : AddCircle L)
  have hdχ : DifferentiableAt ℝ χ x :=
    (microCutoffSum_contDiff hL hr₀ hrL (fun _ : Unit => a j)).differentiable (by simp) x
  rw [deriv_fun_mul hdχ hg]
  by_cases hd : 2*r₀ ≤ d
  · have hzero : χ x = 0 := microCutoffSum_eq_zero hr₀ (fun _ : Unit => a j) (fun _ => hd)
    have hdzero := microCutoffSum_deriv_eq_zero_of_zero hr₀ (fun _ : Unit => a j) hχsep hzero
    change deriv χ x = 0 at hdzero
    rw [hzero, hdzero]
    simp only [zero_mul, zero_add, abs_zero]
    positivity
  · have hdist : d ≤ 2*r₀ := (lt_of_not_ge hd).le
    have hradius : cappedMarkDistance (fun j => (a j : AddCircle L)) (x : AddCircle L) = d :=
      cappedMarkDistance_eq_dist_of_near (fun j => (a j : AddCircle L)) hsep hr1 j hdist
    have hsecond : |χ x| * |deriv (fun t : ℝ => g (t : AddCircle L)) x| ≤
        A*h^(1-s)*z^(-q) := by
      have hc1 : |χ x| ≤ 1 := by rw [abs_of_nonneg hc.1]; exact hc.2
      exact (mul_le_of_le_one_left (abs_nonneg _) hc1).trans (by simpa only [hradius] using hder)
    have hfirst : |deriv χ x| * |g (x : AddCircle L)| ≤
        (D/r₀*B*(2*r₀)^q)*h^(1-s)*z^(-q) := by
      by_cases hzero : deriv χ x = 0
      · rw [hzero, abs_zero, zero_mul]
        positivity
      · obtain ⟨hin, _hout⟩ := microCutoffSum_transition_of_deriv_ne_zero hr₀
          (fun _ : Unit => a j) hχsep hzero
        have hv : |g (x : AddCircle L)| ≤ B*h :=
          hval (by rw [hradius]; exact (hin ()).le)
        have hzc : z ≤ 2*r₀ := max_le hdist (by linarith)
        have hp : 1 ≤ (2*r₀)^q*z^(-q) := by
          have hp := mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hz.le hzc hq)
            (Real.rpow_nonneg hz.le (-q))
          rw [← Real.rpow_add hz, add_neg_cancel, Real.rpow_zero] at hp
          exact hp
        calc
          _ ≤ (D/r₀)*(B*h) := mul_le_mul
            (by simpa only [Fintype.card_unit, Nat.cast_one, one_mul] using
              (hb L r₀ hL hr₀ hrL (fun _ : Unit => a j) x)) hv (abs_nonneg _) (by positivity)
          _ ≤ (D/r₀)*(B*h^(1-s)) := mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (regMicro_fixed_value_power hh hh1 hs) hB) (by positivity)
          _ ≤ (D/r₀)*(B*h^(1-s))*((2*r₀)^q*z^(-q)) :=
            le_mul_of_one_le_right (by positivity) hp
          _ = _ := by ring
    calc
      _ ≤ |deriv χ x| * |g (x : AddCircle L)|+
          |χ x| * |deriv (fun t : ℝ => g (t : AddCircle L)) x| := by
        simpa only [abs_mul] using abs_add_le
          (deriv χ x*g (x : AddCircle L)) (χ x*deriv (fun t : ℝ => g (t : AddCircle L)) x)
      _ ≤ (D/r₀*B*(2*r₀)^q)*h^(1-s)*z^(-q)+A*h^(1-s)*z^(-q) :=
        add_le_add hfirst hsecond
      _ = _ := by ring

/-- The fixed smooth remainder has a bounded derivative of order
`h^(1-s)`. This estimates its actual cutoff product on the whole circle. -/
theorem regMicro_remainder_deriv_bound (n : ℕ+) :
    ∃ D : ℝ, 0 < D ∧ ∀ (L r₀ h : ℝ), 0 < L → 0 < r₀ → 4*r₀ < L →
      r₀ ≤ 1 → 0 < h → h ≤ 1 →
      ∀ (a : Fin (n : ℕ) → ℝ),
        (∀ i j, i ≠ j → 4*r₀ ≤ dist (a i : AddCircle L) (a j : AddCircle L)) →
      ∀ (s q A B : ℝ), 0 ≤ s → 0 ≤ q → 0 ≤ A → 0 ≤ B →
      ∀ (g : AddCircle L → ℝ) (x : ℝ),
        DifferentiableAt ℝ (fun t : ℝ => g (t : AddCircle L)) x →
        (|deriv (fun t : ℝ => g (t : AddCircle L)) x| ≤
          A*h^(1-s)*(max (cappedMarkDistance (fun j => (a j : AddCircle L))
            (x : AddCircle L)) h)^(-q)) →
        (r₀ ≤ cappedMarkDistance (fun j => (a j : AddCircle L)) (x : AddCircle L) →
          |g (x : AddCircle L)| ≤ B*h) →
        |deriv (fun t : ℝ =>
          (1-microCutoffSum L r₀ a (t : AddCircle L))*g (t : AddCircle L)) x| ≤
        (A*r₀^(-q)+(n : ℝ)*D/r₀*B)*h^(1-s) := by
  obtain ⟨D, hD, hb⟩ := microCutoffSum_deriv_bound (ι := Fin (n : ℕ))
  refine ⟨D, hD, fun L r₀ h hL hr₀ hrL hr1 hh hh1 a hsep s q A B hs hq hA hB g x hg hder hval => ?_⟩
  let χ := fun t : ℝ => microCutoffSum L r₀ a (t : AddCircle L)
  have hc := microCutoffSum_mem_Icc hr₀ a hsep (x : AddCircle L)
  have hdχ : DifferentiableAt ℝ χ x :=
    (microCutoffSum_contDiff hL hr₀ hrL a).differentiable (by simp) x
  rw [deriv_fun_mul (hdχ.hasDerivAt.const_sub (1 : ℝ)).differentiableAt hg, deriv_const_sub]
  by_cases hone : χ x = 1
  · have hd0 := microCutoffSum_deriv_eq_zero_of_one hr₀ a hsep hone
    change deriv χ x = 0 at hd0
    rw [hone, hd0]
    simp only [neg_zero, zero_mul, sub_self, zero_add, abs_zero]
    positivity
  · have hradius : r₀ ≤ cappedMarkDistance (fun j => (a j : AddCircle L)) (x : AddCircle L) := by
      apply le_cappedMarkDistance_of_forall_dist _ _ hr1
      intro j
      by_contra hj
      exact hone (microCutoffSum_eq_one hr₀ a hsep j (le_of_not_ge hj))
    have hp : (max (cappedMarkDistance (fun j => (a j : AddCircle L))
        (x : AddCircle L)) h)^(-q) ≤ r₀^(-q) :=
      Real.rpow_le_rpow_of_nonpos hr₀ (hradius.trans (le_max_left _ _)) (neg_nonpos.mpr hq)
    have hfirst : |deriv χ x| * |g (x : AddCircle L)| ≤
        ((n : ℝ)*D/r₀*B)*h^(1-s) := by
      calc
        _ ≤ ((n : ℝ)*D/r₀)*(B*h) := mul_le_mul
          (by simpa only [Fintype.card_fin] using hb L r₀ hL hr₀ hrL a x)
          (hval hradius) (abs_nonneg _) (by positivity)
        _ ≤ ((n : ℝ)*D/r₀)*(B*h^(1-s)) := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (regMicro_fixed_value_power hh hh1 hs) hB) (by positivity)
        _ = _ := by ring
    have hsecond : |1-χ x| * |deriv (fun t : ℝ => g (t : AddCircle L)) x| ≤
        A*r₀^(-q)*h^(1-s) := by
      have hc1 : |1-χ x| ≤ 1 := by rw [abs_of_nonneg (sub_nonneg.mpr hc.2)]; linarith [hc.1]
      calc
        _ ≤ |deriv (fun t : ℝ => g (t : AddCircle L)) x| :=
          mul_le_of_le_one_left (abs_nonneg _) hc1
        _ ≤ A*h^(1-s)*(max (cappedMarkDistance (fun j => (a j : AddCircle L))
            (x : AddCircle L)) h)^(-q) := hder
        _ ≤ A*h^(1-s)*r₀^(-q) := mul_le_mul_of_nonneg_left hp (by positivity)
        _ = _ := by ring
    calc
      _ ≤ |deriv χ x| * |g (x : AddCircle L)|+
          |1-χ x| * |deriv (fun t : ℝ => g (t : AddCircle L)) x| := by
        simpa only [abs_mul, abs_neg] using abs_add_le
          (-deriv χ x*g (x : AddCircle L)) ((1-χ x)*deriv (fun t : ℝ => g (t : AddCircle L)) x)
      _ ≤ ((n : ℝ)*D/r₀*B)*h^(1-s)+A*r₀^(-q)*h^(1-s) := add_le_add hfirst hsecond
      _ = _ := by ring

end Riesz1.Internal
