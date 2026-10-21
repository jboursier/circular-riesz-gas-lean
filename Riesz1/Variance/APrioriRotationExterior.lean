/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.APrioriRotationKernel
public import Riesz1.Variance.APrioriRotationMoments
public import Riesz1.Variance.Window
public import Riesz1.ToMathlib.Calculus.DiscreteTailSum

/-!
# Exterior tail of the moved origin

First claim of the rotation estimate in Lemma 5.2: the exterior sum
`E_γ(X) = ∑_{i ∉ I_γ} f((x_i - x_1)/ℓ)` has `L^p(dGi)` norm bounded by a constant `C_ε`, for `γ`
large depending on `s, λ, p`. The proof is pointwise: each exterior term is bounded by inverse
powers of the two arc lengths `F = S_{0,i}` and `G = S_{i,N-i}` (`abs_le_blocks`). The moments of
these arc lengths are summed over the exterior labels with `sum_natCast_rpow_neg_le_of_subset`.

Exponents: `A = (λ+ε+γ)/(γ-1) + 2` for the inverse powers of the blocks and `2-s` for the
nearest-neighbour powers. The threshold is `γ₀ = (2-s)/(1-s)`, which depends on `s` only.
-/

@[expose] public section

open MeasureTheory Finset Set

namespace Riesz1

/-- The exterior sum `E_γ(X) = ∑_{i ∉ I_γ} f((x_i - x_1)/ℓ)` of Lemma 5.2,
with labels counted from zero (`x_i = cyclicLift X i`) and `K = Nℓ`. -/
noncomputable def exteriorSum (N : ℕ+) (ℓ γ : ℝ) (f : ℝ → ℝ) (X : Configuration N) : ℝ :=
  ∑ i ∈ (window N (((N : ℕ) : ℝ) * ℓ) γ)ᶜ, f ((cyclicLift X (i : ℕ) - cyclicLift X 0) / ℓ)

/-- A label outside the window is farther than `K^γ` from the origin label. -/
theorem labelDist_gt_of_not_mem_window {N : ℕ+} {K γ : ℝ} {i : Fin (N : ℕ)}
    (hi : i ∉ window N K γ) : K ^ γ < (labelDistToOne N i : ℝ) := by
  by_cases h : K ^ γ < ((N : ℕ) : ℝ) / 8
  · unfold window windowLabels at hi
    rw [windowTime_of_lt h] at hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hi
    have hN : ((N : ℕ) : ℝ) ≠ 0 := by exact_mod_cast N.ne_zero
    have h1 : ((N : ℕ) : ℝ) * (K ^ γ / ((N : ℕ) : ℝ)) = K ^ γ := by field_simp
    linarith
  · exact (hi (by rw [window_full h]; exact Finset.mem_univ i)).elim

/-- A sum of `(φ i)^{-a}` over labels `i` with `φ` injective on the set, all values in `(J, N]`,
is at most `J^{1-a}/(a-1)`. -/
theorem sum_rpow_neg_le_of_injOn {N : ℕ} {a : ℝ} (ha : 1 < a) {J : ℕ} (hJ : 1 ≤ J)
    (E : Finset (Fin N)) (φ : Fin N → ℕ) (hinj : Set.InjOn φ E)
    (hE : ∀ i ∈ E, J < φ i ∧ φ i ≤ N) :
    ∑ i ∈ E, ((φ i : ℕ) : ℝ) ^ (-a) ≤ (J : ℝ) ^ (1 - a) / (a - 1) := by
  calc ∑ i ∈ E, ((φ i : ℕ) : ℝ) ^ (-a)
      = ∑ m ∈ E.image φ, (m : ℝ) ^ (-a) :=
        (Finset.sum_image (f := fun m : ℕ => (m : ℝ) ^ (-a)) hinj).symm
    _ ≤ (J : ℝ) ^ (1 - a) / (a - 1) := by
        refine sum_natCast_rpow_neg_le_of_subset (N := N) ha hJ _ (fun m hm => ?_)
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hm
        exact hE i hi

/-- **Tail constant, inverse block powers.** If `1 < A`, `λ+ε+γ ≤ A(γ-1)` and `K^γ/2 ≤ J`, then
`K^{λ+ε} (2K)^A J^{1-A} ≤ 2^{2A-1}` for `K ≥ 1`. -/
theorem tail_const_A {K γ lam ε A : ℝ} {J : ℕ} (hK : 1 ≤ K) (hγ : 1 < γ)
    (_hlam : 0 ≤ lam) (hA : 1 < A) (hexp : lam + ε + γ ≤ A * (γ - 1)) (hJ : K ^ γ / 2 ≤ J) :
    K ^ (lam + ε) * (2 * K) ^ A * (J : ℝ) ^ (1 - A) ≤ 2 ^ (2 * A - 1) := by
  have hK0 : 0 < K := by linarith
  have hKγ1 : 1 ≤ K ^ γ := Real.one_le_rpow hK (by linarith)
  have hKγ0 : 0 < K ^ γ / 2 := div_pos (by linarith) two_pos
  have h1 : (J : ℝ) ^ (1 - A) ≤ (K ^ γ / 2) ^ (1 - A) :=
    Real.rpow_le_rpow_of_nonpos hKγ0 hJ (by linarith)
  have h2 : (K ^ γ / 2) ^ (1 - A) = K ^ (γ * (1 - A)) * 2 ^ (A - 1) := by
    rw [Real.div_rpow (Real.rpow_nonneg hK0.le _) two_pos.le, ← Real.rpow_mul hK0.le,
      show (1 : ℝ) - A = -(A - 1) by ring, Real.rpow_neg two_pos.le, div_inv_eq_mul]
  have h3 : K ^ (lam + ε) * (2 * K) ^ A * (K ^ (γ * (1 - A)) * 2 ^ (A - 1)) =
      2 ^ (2 * A - 1) * K ^ (lam + ε + A + γ * (1 - A)) := by
    rw [Real.mul_rpow two_pos.le hK0.le, show (2 : ℝ) * A - 1 = A + (A - 1) by ring,
      Real.rpow_add hK0 (lam + ε + A) (γ * (1 - A)), Real.rpow_add hK0 (lam + ε) A,
      Real.rpow_add two_pos A (A - 1)]
    ring
  have hexp' : lam + ε + A + γ * (1 - A) ≤ 0 := by linarith
  have hKle : K ^ (lam + ε + A + γ * (1 - A)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hK hexp'
  calc K ^ (lam + ε) * (2 * K) ^ A * (J : ℝ) ^ (1 - A)
      ≤ K ^ (lam + ε) * (2 * K) ^ A * (K ^ γ / 2) ^ (1 - A) :=
        mul_le_mul_of_nonneg_left h1
          (mul_nonneg (Real.rpow_nonneg hK0.le _) (Real.rpow_nonneg (by linarith) _))
    _ = K ^ (lam + ε) * (2 * K) ^ A * (K ^ (γ * (1 - A)) * 2 ^ (A - 1)) := by rw [h2]
    _ = 2 ^ (2 * A - 1) * K ^ (lam + ε + A + γ * (1 - A)) := h3
    _ ≤ 2 ^ (2 * A - 1) * 1 := mul_le_mul_of_nonneg_left hKle (by positivity)
    _ = 2 ^ (2 * A - 1) := mul_one _

/-- **Tail constant, nearest-neighbour powers.** If `2 - s ≤ γ(1-s)` and `K^γ/2 ≤ J`, then
`K^{2-s} J^{s-1} ≤ 2^{1-s}` for `K ≥ 1`. -/
theorem tail_const_B {K γ s : ℝ} {J : ℕ} (hK : 1 ≤ K) (hγ : 0 ≤ γ) (hs1 : s < 1)
    (hexp : 2 - s ≤ γ * (1 - s)) (hJ : K ^ γ / 2 ≤ J) :
    K ^ (2 - s) * (J : ℝ) ^ (s - 1) ≤ 2 ^ (1 - s) := by
  have hK0 : 0 < K := by linarith
  have hKγ1 : 1 ≤ K ^ γ := Real.one_le_rpow hK hγ
  have hKγ0 : 0 < K ^ γ / 2 := div_pos (by linarith) two_pos
  have h1 : (J : ℝ) ^ (s - 1) ≤ (K ^ γ / 2) ^ (s - 1) :=
    Real.rpow_le_rpow_of_nonpos hKγ0 hJ (by linarith)
  have h2 : (K ^ γ / 2) ^ (s - 1) = K ^ (γ * (s - 1)) * 2 ^ (1 - s) := by
    rw [Real.div_rpow (Real.rpow_nonneg hK0.le _) two_pos.le, ← Real.rpow_mul hK0.le,
      show s - 1 = -(1 - s) by ring, Real.rpow_neg two_pos.le, div_inv_eq_mul]
  have h3 : K ^ (2 - s) * (K ^ (γ * (s - 1)) * 2 ^ (1 - s)) =
      2 ^ (1 - s) * K ^ (2 - s + γ * (s - 1)) := by
    rw [Real.rpow_add hK0 (2 - s) (γ * (s - 1))]
    ring
  have hexp' : 2 - s + γ * (s - 1) ≤ 0 := by linarith
  have hKle : K ^ (2 - s + γ * (s - 1)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hK hexp'
  calc K ^ (2 - s) * (J : ℝ) ^ (s - 1)
      ≤ K ^ (2 - s) * (K ^ γ / 2) ^ (s - 1) :=
        mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hK0.le _)
    _ = K ^ (2 - s) * (K ^ (γ * (s - 1)) * 2 ^ (1 - s)) := by rw [h2]
    _ = 2 ^ (1 - s) * K ^ (2 - s + γ * (s - 1)) := h3
    _ ≤ 2 ^ (1 - s) * 1 := mul_le_mul_of_nonneg_left hKle (by positivity)
    _ = 2 ^ (1 - s) := mul_one _

/-- **`L^p` norm of a four-term sum over a finite index set.** If `|E X| ≤ ∑_i (h₁ i X + h₂ i X +
h₃ i X + h₄ i X)` pointwise, then the `L^p` seminorm of `E` is at most the sum of the seminorms of
the four families. -/
theorem eLpNorm_le_sum_four {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {p : ENNReal}
    (hp : 1 ≤ p) (s : Finset ι) {E : Ω → ℝ} (hE : Measurable E) (h₁ h₂ h₃ h₄ : ι → Ω → ℝ)
    (hpt : ∀ X, |E X| ≤ ∑ i ∈ s, (h₁ i X + h₂ i X + h₃ i X + h₄ i X)) :
    eLpNorm E p μ ≤ ∑ i ∈ s, (eLpNorm (h₁ i) p μ + eLpNorm (h₂ i) p μ +
      eLpNorm (h₃ i) p μ + eLpNorm (h₄ i) p μ) := by
  calc eLpNorm E p μ
      ≤ eLpNorm (fun X => ∑ i ∈ s, (h₁ i X + h₂ i X + h₃ i X + h₄ i X)) p μ :=
        eLpNorm_mono_real hE.aestronglyMeasurable fun X => by
          rw [Real.norm_eq_abs]
          exact hpt X
    _ = eLpNorm (∑ i ∈ s, (h₁ i + h₂ i + h₃ i + h₄ i)) p μ := by
        congr 1
        funext X
        simp [Finset.sum_apply]
    _ ≤ ∑ i ∈ s, eLpNorm (h₁ i + h₂ i + h₃ i + h₄ i) p μ := eLpNorm_sum_le hp
    _ ≤ ∑ i ∈ s, (eLpNorm (h₁ i) p μ + eLpNorm (h₂ i) p μ + eLpNorm (h₃ i) p μ +
          eLpNorm (h₄ i) p μ) := by
        refine Finset.sum_le_sum fun i _ => ?_
        calc eLpNorm (h₁ i + h₂ i + h₃ i + h₄ i) p μ
            ≤ eLpNorm (h₁ i + h₂ i + h₃ i) p μ + eLpNorm (h₄ i) p μ := eLpNorm_add_le hp
          _ ≤ (eLpNorm (h₁ i + h₂ i) p μ + eLpNorm (h₃ i) p μ) + eLpNorm (h₄ i) p μ := by
              gcongr
              exact eLpNorm_add_le hp
          _ ≤ ((eLpNorm (h₁ i) p μ + eLpNorm (h₂ i) p μ) + eLpNorm (h₃ i) p μ) +
                eLpNorm (h₄ i) p μ := by
              gcongr
              exact eLpNorm_add_le hp
          _ = _ := by ring

end Riesz1

end
