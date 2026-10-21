/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.ConvexificationHessian

/-!
# The anchored inverse-energy bound

Lemma 5.2, fourth claim. Let `v` and `(a_i)` be anchored vector fields with
`v · U = ∑_{i,i+1 ∈ I_γ} a_i N (u_{i+1} - u_i)` for every anchored `U`, almost everywhere. The claim
bounds the inverse energy of `v` by `C K^{(s+2)ε}` times the mean of `∑ a_i²`.

The proof has two steps, which this file formalizes in their variational form.

* **Pointwise.** For a point `y` of the anchored domain, the variational supremum
  `sup_U { 2 v·U - U·∇²V(y) U }` is at most `(∑ a_i²) / λ`, where `λ` is the constant of the Hessian
  lower bound `anchoredPotential_hessian_lower`. This is the inequality `2ab - λb² ≤ a²/λ` summed over
  the window edges, with `b = N (u_{i+1} - u_i)`.
* **Integration.** The pointwise bound integrates against every measure `ν` on the anchored domain, with
  no integrability hypothesis, since the bound holds in `ENNReal`.

Here `anchoredInverseSup V y v` is the variational supremum of the Hessian form, which is the
Brascamp–Lieb expression for the inverse energy. It bounds the inverse energy `∫ v · A_1^{-1} v`
from above. That bound, the vector Brascamp–Lieb inequality (part of Lemma 3.5), is not
formalized in this file.
-/

@[expose] public section

open MeasureTheory Set Finset

namespace Riesz1

/-- The pairing `v · U = ∑_k v_k U_k` of two anchored vectors. -/
def dotProd {n : ℕ} (v U : Fin n → ℝ) : ℝ :=
  ∑ k, v k * U k

/-- The variational supremum `sup_U { 2 v · U - ∇²V(y)[U, U] }` of the Hessian of `V` at `y`. -/
noncomputable def anchoredInverseSup {n : ℕ} (V : (Fin n → ℝ) → ℝ) (y v : Fin n → ℝ) : ℝ :=
  sSup (Set.range fun U : Fin n → ℝ => 2 * dotProd v U - fderiv ℝ (fderiv ℝ V) y U U)

/-- The scalar inequality `2 a t - λ t² ≤ a² / λ` for `λ > 0`, from `(a - λ t)² ≥ 0`. -/
lemma two_mul_sub_sq_le {a t lam : ℝ} (hlam : 0 < lam) :
    2 * a * t - lam * t ^ 2 ≤ a ^ 2 / lam := by
  rw [le_div_iff₀ hlam]
  nlinarith [sq_nonneg (a - lam * t)]

/-- A quadratic lower bound on a Hessian form turns the variational supremum into a sum. If the
pairing `v · U` is `∑_{e ∈ E} a_e t_e(U)` and `λ ∑_{e ∈ E} t_e(U)² ≤ Hess(U, U)` for every `U`, then
the variational supremum is at most `(∑_{e ∈ E} a_e²) / λ`. -/
lemma anchoredInverseSup_le_of_quadratic_bound {n : ℕ} {ι : Type*} (V : (Fin n → ℝ) → ℝ)
    (y v : Fin n → ℝ) (E : Finset ι) (a : ι → ℝ) (t : ι → (Fin n → ℝ) → ℝ) {lam : ℝ}
    (hlam : 0 < lam) (hrep : ∀ U, dotProd v U = ∑ e ∈ E, a e * t e U)
    (hess : ∀ U, lam * ∑ e ∈ E, t e U ^ 2 ≤ fderiv ℝ (fderiv ℝ V) y U U) :
    anchoredInverseSup V y v ≤ (∑ e ∈ E, a e ^ 2) / lam := by
  unfold anchoredInverseSup
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨U, rfl⟩
  have h1 : 2 * dotProd v U = ∑ e ∈ E, 2 * a e * t e U := by
    rw [hrep U, Finset.mul_sum]
    exact Finset.sum_congr rfl fun e _ => by ring
  have h2 : ∑ e ∈ E, (2 * a e * t e U - lam * t e U ^ 2) ≤ ∑ e ∈ E, a e ^ 2 / lam :=
    Finset.sum_le_sum fun e _ => two_mul_sub_sq_le hlam
  have h3 : ∑ e ∈ E, (2 * a e * t e U - lam * t e U ^ 2) =
      (∑ e ∈ E, 2 * a e * t e U) - lam * ∑ e ∈ E, t e U ^ 2 := by
    rw [Finset.sum_sub_distrib, Finset.mul_sum]
  have h4 : (∑ e ∈ E, a e ^ 2) / lam = ∑ e ∈ E, a e ^ 2 / lam := Finset.sum_div _ _ _
  show 2 * dotProd v U - fderiv ℝ (fderiv ℝ V) y U U ≤ (∑ e ∈ E, a e ^ 2) / lam
  rw [h4]
  linarith [h1, h2, h3, hess U]

/-- **Pointwise inverse-energy bound.** At a point `y` of the anchored domain, if the representation
`v · U = ∑_{e} a_e N (u_{e+1} - u_e)` holds for every `U`, then the variational supremum of the
Hessian form of `β (H_N^* + F^*)` is at most `c⁻¹ K^{(s+2)ε} ∑_e a_e²`. The constant `c` is the one of
`anchoredPotential_hessian_lower`, passed as the hypothesis `hH`. -/
theorem anchoredInverseSup_le (β : ℝ) (hβ : 0 < β) (s : RieszExponent) {c : ℝ} (hc : 0 < c)
    (hH : ∀ (θ : ℝ → ℝ), IsForcingCutoff θ → ∀ (n : ℕ), 1 ≤ n → ∀ (K γ ε : ℝ), 1 ≤ K → 0 ≤ ε →
      ∀ y ∈ anchoredDomain n, ∀ U : Fin n → ℝ,
        c * K ^ (-((s.val + 2) * ε)) *
            ∑ i ∈ nearestPairs n.succPNat (window n.succPNat K γ),
              (((n : ℝ) + 1) ^ 2 * (edgeForm n i U) ^ 2) ≤
          fderiv ℝ (fderiv ℝ (anchoredPotential β hβ s θ n K γ ε)) y U U)
    (θ : ℝ → ℝ) (hθ : IsForcingCutoff θ) (n : ℕ) (hn : 1 ≤ n) (K γ ε : ℝ) (hK : 1 ≤ K)
    (hε : 0 ≤ ε) {y : Fin n → ℝ} (hy : y ∈ anchoredDomain n) (v : Fin n → ℝ)
    (a : Fin (n.succPNat : ℕ) → ℝ)
    (hrep : ∀ U : Fin n → ℝ, dotProd v U =
      ∑ e ∈ nearestPairs n.succPNat (window n.succPNat K γ), a e * (((n : ℝ) + 1) * edgeForm n e U)) :
    anchoredInverseSup (anchoredPotential β hβ s θ n K γ ε) y v ≤
      1 / c * K ^ ((s.val + 2) * ε) *
        ∑ e ∈ nearestPairs n.succPNat (window n.succPNat K γ), a e ^ 2 := by
  have hK0 : 0 < K := by linarith
  set E := nearestPairs n.succPNat (window n.succPNat K γ) with hE
  set lam := c * K ^ (-((s.val + 2) * ε)) with hlam
  have hlam0 : 0 < lam := mul_pos hc (Real.rpow_pos_of_pos hK0 _)
  have hess : ∀ U : Fin n → ℝ, lam * ∑ e ∈ E, (((n : ℝ) + 1) * edgeForm n e U) ^ 2 ≤
      fderiv ℝ (fderiv ℝ (anchoredPotential β hβ s θ n K γ ε)) y U U := by
    intro U
    have h := hH θ hθ n hn K γ ε hK hε y hy U
    have hsum : ∑ e ∈ E, (((n : ℝ) + 1) * edgeForm n e U) ^ 2 =
        ∑ e ∈ E, ((n : ℝ) + 1) ^ 2 * (edgeForm n e U) ^ 2 :=
      Finset.sum_congr rfl fun e _ => by ring
    rw [hsum, hlam]
    exact h
  have key := anchoredInverseSup_le_of_quadratic_bound (anchoredPotential β hβ s θ n K γ ε) y v E a
    (fun e U => ((n : ℝ) + 1) * edgeForm n e U) hlam0 hrep hess
  have hinv : (∑ e ∈ E, a e ^ 2) / lam =
      1 / c * K ^ ((s.val + 2) * ε) * ∑ e ∈ E, a e ^ 2 := by
    rw [hlam, Real.rpow_neg hK0.le, div_eq_mul_inv, mul_inv, inv_inv]
    ring
  rw [hinv] at key
  exact key

/-- **Lemma 5.2, fourth claim (variational form).** Let `0 < ε` and `γ`
be fixed, and let `c > 0` be the constant of the Hessian lower bound, which depends only on `s` and
`β`. For every cutoff `θ`, every `n ≥ 1`, every `K ≥ 1`, and every probability measure `ν` on the
anchored domain, let `v` and `a_e` be vector fields with `v · U = ∑_{e} a_e N (u_{e+1} - u_e)` for
every `U`, `ν`-almost everywhere. Then the integral of the variational supremum of the Hessian form
of `β (H_N^* + F^*)` against `ν` is at most `c⁻¹ K^{(s+2)ε}` times the integral of `∑_e a_e²`.

The bound holds in `ENNReal` without any integrability hypothesis. In particular, it holds whenever
the right side is finite. -/
theorem anchoredInverse_lintegral_le (β : ℝ) (hβ : 0 < β) (s : RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ (θ : ℝ → ℝ), IsForcingCutoff θ → ∀ (n : ℕ), 1 ≤ n →
      ∀ (K γ ε : ℝ), 1 ≤ K → 0 ≤ ε → ∀ (ν : Measure (Fin n → ℝ)) (v : (Fin n → ℝ) → (Fin n → ℝ))
        (a : (Fin n → ℝ) → Fin (n.succPNat : ℕ) → ℝ),
        (∀ᵐ y ∂ν, y ∈ anchoredDomain n) →
        (∀ᵐ y ∂ν, ∀ U : Fin n → ℝ, dotProd (v y) U =
          ∑ e ∈ nearestPairs n.succPNat (window n.succPNat K γ),
            a y e * (((n : ℝ) + 1) * edgeForm n e U)) →
        ∫⁻ y, ENNReal.ofReal (anchoredInverseSup (anchoredPotential β hβ s θ n K γ ε) y (v y)) ∂ν ≤
          ENNReal.ofReal (C * K ^ ((s.val + 2) * ε)) *
            ∫⁻ y, ENNReal.ofReal (∑ e ∈ nearestPairs n.succPNat (window n.succPNat K γ),
              a y e ^ 2) ∂ν := by
  obtain ⟨c, hc, hH⟩ := anchoredPotential_hessian_lower β hβ s
  refine ⟨1 / c, one_div_pos.mpr hc, fun θ hθ n hn K γ ε hK hε ν v a hν hrep => ?_⟩
  have hnn : 0 ≤ 1 / c * K ^ ((s.val + 2) * ε) := by
    have : (0 : ℝ) < K := by linarith
    exact mul_nonneg (one_div_pos.mpr hc).le (Real.rpow_nonneg this.le _)
  calc ∫⁻ y, ENNReal.ofReal (anchoredInverseSup (anchoredPotential β hβ s θ n K γ ε) y (v y)) ∂ν
      ≤ ∫⁻ y, ENNReal.ofReal (1 / c * K ^ ((s.val + 2) * ε) *
          ∑ e ∈ nearestPairs n.succPNat (window n.succPNat K γ), a y e ^ 2) ∂ν := by
        apply lintegral_mono_ae
        filter_upwards [hν, hrep] with y hy hry
        exact ENNReal.ofReal_le_ofReal
          (anchoredInverseSup_le β hβ s hc hH θ hθ n hn K γ ε hK hε hy (v y) (a y) hry)
    _ = ENNReal.ofReal (1 / c * K ^ ((s.val + 2) * ε)) *
          ∫⁻ y, ENNReal.ofReal (∑ e ∈ nearestPairs n.succPNat (window n.succPNat K γ),
            a y e ^ 2) ∂ν := by
        simp_rw [ENNReal.ofReal_mul hnn]
        exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

end Riesz1

end
