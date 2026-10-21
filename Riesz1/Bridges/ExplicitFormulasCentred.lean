/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Bridges.IndicatorArc
public import Riesz1.Kernel.ExplicitFormulasIndicator

/-!
# Bridge: the explicit formulas of the indicator about any centre

The theorem `explicit_formulas_indicator` is centred at `0`. Lemma 2.3 needs the same conclusions
for the arc `arcIndicator c a` of radius `a` about any centre `c`.

The proof is a translation. Translating a function by `c` multiplies its Fourier coefficient
by a unimodular factor, so the seminorm and the transport coefficients are unchanged up to that
factor, and the transport formula is translated by `c`.

Main result: `explicit_formulas_indicator_centered`.
-/

public section

open MeasureTheory Set Filter Topology
open scoped Real Interval

namespace Riesz1

/-- Every Fourier mode on the unit circle has modulus one. -/
lemma norm_fourier_unitAddCircle_eq_one (n : ℤ) (x : UnitAddCircle) : ‖fourier n x‖ = 1 := by
  rw [fourier_apply, Circle.norm_coe]

/-- The Fourier coefficient of the translate `t ↦ f (t - c)` equals `e_{-k}(c)` times the
Fourier coefficient of `f`. The substitution `t ↦ t + c` uses the translation invariance of the
Haar measure on the circle. -/
lemma fourierCoeff_sub_centre (f : UnitAddCircle → ℂ) (c : UnitAddCircle) (k : ℤ) :
    fourierCoeff (fun t => f (t - c)) k = fourier (-k) c * fourierCoeff f k := by
  have hshift := integral_sub_right_eq_self (μ := AddCircle.haarAddCircle)
    (fun u : UnitAddCircle => fourier (-k) (u + c) • f u) c
  simp only [sub_add_cancel] at hshift
  have hmul : ∀ u : UnitAddCircle, fourier (-k) (u + c) • f u =
      fourier (-k) c • (fourier (-k) u • f u) := by
    intro u
    rw [fourier_add_point, mul_smul, smul_comm]
  calc fourierCoeff (fun t => f (t - c)) k
      = ∫ t, fourier (-k) t • f (t - c) ∂AddCircle.haarAddCircle := rfl
    _ = ∫ u, fourier (-k) (u + c) • f u ∂AddCircle.haarAddCircle := hshift
    _ = ∫ u, fourier (-k) c • (fourier (-k) u • f u) ∂AddCircle.haarAddCircle :=
        integral_congr_ae (ae_of_all _ hmul)
    _ = fourier (-k) c • ∫ u, fourier (-k) u • f u ∂AddCircle.haarAddCircle :=
        integral_smul _ _
    _ = fourier (-k) c * fourierCoeff f k := by
        rw [smul_eq_mul]
        rfl

/-- The Fourier coefficient of the translate `t ↦ f (t + c)` equals `e_{-k}(-c)` times the
Fourier coefficient of `f`. -/
lemma fourierCoeff_add_centre (f : UnitAddCircle → ℂ) (c : UnitAddCircle) (k : ℤ) :
    fourierCoeff (fun t => f (t + c)) k = fourier (-k) (-c) * fourierCoeff f k := by
  have hshift := integral_add_right_eq_self (μ := AddCircle.haarAddCircle)
    (fun u : UnitAddCircle => fourier (-k) (u - c) • f u) c
  simp only [add_sub_cancel_right] at hshift
  have hmul : ∀ u : UnitAddCircle, fourier (-k) (u - c) • f u =
      fourier (-k) (-c) • (fourier (-k) u • f u) := by
    intro u
    rw [sub_eq_add_neg, fourier_add_point, mul_smul, smul_comm]
  calc fourierCoeff (fun t => f (t + c)) k
      = ∫ t, fourier (-k) t • f (t + c) ∂AddCircle.haarAddCircle := rfl
    _ = ∫ u, fourier (-k) (u - c) • f u ∂AddCircle.haarAddCircle := hshift
    _ = ∫ u, fourier (-k) (-c) • (fourier (-k) u • f u) ∂AddCircle.haarAddCircle :=
        integral_congr_ae (ae_of_all _ hmul)
    _ = fourier (-k) (-c) • ∫ u, fourier (-k) u • f u ∂AddCircle.haarAddCircle :=
        integral_smul _ _
    _ = fourier (-k) (-c) * fourierCoeff f k := by
        rw [smul_eq_mul]
        rfl

/-- Every Fourier mode is one at the origin of the circle. -/
lemma fourier_at_zero (n : ℤ) : fourier n (0 : UnitAddCircle) = 1 := by
  simp [fourier_apply]

/-- The two unimodular factors of the translations by `c` and `-c` cancel. -/
lemma fourier_neg_mul_fourier_eq_one (k : ℤ) (c : UnitAddCircle) :
    fourier (-k) (-c) * fourier (-k) c = 1 := by
  rw [← fourier_add_point, neg_add_cancel, fourier_at_zero]

/-- The Fourier coefficients of the arc indicator about `c` are those of the arc about `0`,
multiplied by `e_{-k}(c)`. -/
lemma fourierCoeff_arcIndicator_centre {a : ℝ} (ha1 : a < 1 / 2) (c : UnitAddCircle) (k : ℤ) :
    fourierCoeff (fun t => (arcIndicator c a t : ℂ)) k =
      fourier (-k) c * fourierCoeff (fun t => (indicatorArc a t : ℂ)) k := by
  have e : (fun t : UnitAddCircle => (arcIndicator c a t : ℂ)) =
      fun t => (indicatorArc a (t - c) : ℂ) := by
    funext t
    rw [arcIndicator_eq_indicatorArc_sub ha1]
  rw [e]
  exact fourierCoeff_sub_centre (fun u => (indicatorArc a u : ℂ)) c k

/-- The Fourier coefficients of the centred arc `arcIndicator c a - 2a` are those of the centred
arc about `0`, multiplied by `e_{-k}(c)`. -/
lemma fourierCoeff_centredArc_centre {a : ℝ} (ha1 : a < 1 / 2) (c : UnitAddCircle) (k : ℤ) :
    fourierCoeff (fun t => ((arcIndicator c a t - 2 * a : ℝ) : ℂ)) k =
      fourier (-k) c * fourierCoeff (fun t => (centeredIndicatorArc a t : ℂ)) k := by
  have e : (fun t : UnitAddCircle => ((arcIndicator c a t - 2 * a : ℝ) : ℂ)) =
      fun t => ((centeredIndicatorArc a (t - c) : ℝ) : ℂ) := by
    funext t
    rw [centeredIndicatorArc, arcIndicator_eq_indicatorArc_sub ha1]
  rw [e]
  exact fourierCoeff_sub_centre (fun u => ((centeredIndicatorArc a u : ℝ) : ℂ)) c k

/-- The seminorm of the centred arc about `c` equals that of the centred arc about `0`. -/
lemma circleSobolevSq_centredArc_centre {a : ℝ} (ha1 : a < 1 / 2) (c : UnitAddCircle) (r : ℝ) :
    circleSobolevSq r ⟨fun t => ((arcIndicator c a t - 2 * a : ℝ) : ℂ), memLp_centredArc c a⟩ =
      circleSobolevSq r ⟨fun t => ((centeredIndicatorArc a t : ℝ) : ℂ),
        memLp_centeredIndicatorArc a⟩ := by
  unfold circleSobolevSq
  refine tsum_congr fun k => ?_
  by_cases hk : k = 0
  · simp [hk]
  · dsimp only
    simp only [hk, ↓reduceIte]
    rw [fourierCoeff_centredArc_centre ha1 c k, norm_mul, norm_fourier_unitAddCircle_eq_one,
      one_mul]

/-- The seminorm of the arc indicator about `c` equals that of the centred arc about `c`:
they have the same nonzero Fourier coefficients, since the constant `2a` has none. -/
lemma circleSobolevSq_arcIndicator_centre {a : ℝ} (ha1 : a < 1 / 2) (c : UnitAddCircle) (r : ℝ) :
    circleSobolevSq r ⟨fun t => (arcIndicator c a t : ℂ), memLp_arcIndicator c a⟩ =
      circleSobolevSq r ⟨fun t => ((arcIndicator c a t - 2 * a : ℝ) : ℂ),
        memLp_centredArc c a⟩ := by
  unfold circleSobolevSq
  refine tsum_congr fun k => ?_
  by_cases hk : k = 0
  · simp [hk]
  · dsimp only
    simp only [hk, ↓reduceIte]
    rw [fourierCoeff_arcIndicator_centre ha1 c k, fourierCoeff_centredArc_centre ha1 c k,
      fourierCoeff_indicatorArc_eq_centered hk]

/-- Translating a square integrable real function on the circle by `c` keeps it square
integrable. -/
lemma memLp_sub_centre {g : UnitAddCircle → ℝ} (hg : MemLp (fun t => (g t : ℂ)) 2 volume)
    (c : UnitAddCircle) : MemLp (fun t => ((g (t - c) : ℝ) : ℂ)) 2 volume :=
  hg.comp_measurePreserving (measurePreserving_sub_right volume c)

/-- Equal functions have equal transport coefficients, whatever their proofs of square
integrability. -/
lemma transportCoeffs_congr_fun (P : Parameters) {f g : UnitAddCircle → ℝ}
    (hf : MemLp (fun t => (f t : ℂ)) 2 volume) (hg : MemLp (fun t => (g t : ℂ)) 2 volume)
    (h : f = g) (k : ℤ) :
    transportCoeffs P ⟨1, one_pos⟩ ⟨f, hf⟩ k = transportCoeffs P ⟨1, one_pos⟩ ⟨g, hg⟩ k := by
  subst h
  rfl

/-- The transport coefficients of a translate: the mean-zero transport coefficient at `k` is
multiplied by `e_{-k}(c)`. -/
lemma transportCoeffs_sub_centre (P : Parameters) {g : UnitAddCircle → ℝ}
    (hg : MemLp (fun t => (g t : ℂ)) 2 volume) (c : UnitAddCircle) (k : ℤ) :
    transportCoeffs P ⟨1, one_pos⟩ ⟨fun t => g (t - c), memLp_sub_centre hg c⟩ k =
      fourier (-k) c * transportCoeffs P ⟨1, one_pos⟩ ⟨g, hg⟩ k := by
  unfold transportCoeffs
  by_cases hk : k = 0
  · simp [hk]
  · simp only [hk, ↓reduceIte]
    unfold coeff
    dsimp only
    rw [fourierCoeff_sub_centre (fun t => (g t : ℂ)) c k]
    ring

/-- The transport coefficients of the arc indicator about `c` are those of the arc about
`0`, multiplied by `e_{-k}(c)`. -/
lemma transportCoeffs_arcIndicator_centre (P : Parameters) {a : ℝ} (ha1 : a < 1 / 2)
    (c : UnitAddCircle) (k : ℤ) :
    transportCoeffs P ⟨1, one_pos⟩ ⟨fun t => arcIndicator c a t, memLp_arcIndicator c a⟩ k =
      fourier (-k) c * transportCoeffs P ⟨1, one_pos⟩ ⟨indicatorArc a, memLp_indicatorArc a⟩ k :=
  (transportCoeffs_congr_fun P (memLp_arcIndicator c a)
    (memLp_sub_centre (memLp_indicatorArc a) c)
    (funext fun t => arcIndicator_eq_indicatorArc_sub ha1 c t) k).trans
    (transportCoeffs_sub_centre P (memLp_indicatorArc a) c k)

/-- The transport coefficients of the centred arc about `c` are those of the centred arc
about `0`, multiplied by `e_{-k}(c)`. -/
lemma transportCoeffs_centredArc_centre (P : Parameters) {a : ℝ} (ha1 : a < 1 / 2)
    (c : UnitAddCircle) (k : ℤ) :
    transportCoeffs P ⟨1, one_pos⟩ ⟨fun t => arcIndicator c a t - 2 * a, memLp_centredArc c a⟩ k =
      fourier (-k) c * transportCoeffs P ⟨1, one_pos⟩
        ⟨centeredIndicatorArc a, memLp_centeredIndicatorArc a⟩ k :=
  (transportCoeffs_congr_fun P (memLp_centredArc c a)
    (memLp_sub_centre (memLp_centeredIndicatorArc a) c)
    (funext fun t => by rw [centeredIndicatorArc, arcIndicator_eq_indicatorArc_sub ha1]) k).trans
    (transportCoeffs_sub_centre P (memLp_centeredIndicatorArc a) c k)

/-- Lemma 2.3 for the indicator about an arbitrary centre. For
`0 < s < 1`, `β > 0`, `0 < a < 1/2` and a centre `c` on the unit circle, with the arc
`arcIndicator c a` and its centred version `arcIndicator c a - 2a`:

* the transport `V_s(x - c + a) - V_s(x - c - a)` form, translated by `c`, is continuous, and every
  `L²` function with the transport coefficients of the centred arc about `c` equals the
  translated transport almost everywhere.
* the energy identity `(2π)^{1-s}/(2β c_s) ‖ξ_c‖² = cot(πs/2) V_s(2a)/(2πβs)` holds for the
  centred arc `ξ_c` about `c`, and `‖ξ_c‖²` is finite.
* the uncentred arc about `c` has the same transport coefficients and seminorm as the centred one. -/
theorem explicit_formulas_indicator_centered (s : RieszExponent) (β : ℝ) (hβ : 0 < β)
    (c : UnitAddCircle) (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1 / 2) :
    Continuous (fun t : UnitAddCircle => transportFormula s β a (t - c)) ∧
    (∀ ψ : {g : Circle ⟨1, one_pos⟩ → ℝ // MemLp (fun x => (g x : ℂ)) 2
          (arclength ⟨1, one_pos⟩)},
      (∀ k : ℤ, coeff ⟨1, one_pos⟩
          ⟨fun x => (ψ.val x : ℂ), complexL2Integrable ⟨1, one_pos⟩ _ ψ.property⟩ k =
        transportCoeffs ⟨(β, s.val), hβ, s.2.1, s.2.2⟩ ⟨1, one_pos⟩
          ⟨fun t => arcIndicator c a t - 2 * a, memLp_centredArc c a⟩ k) →
      ∀ᵐ x ∂(arclength ⟨1, one_pos⟩), ψ.val x = transportFormula s β a (x - c)) ∧
    (circleSobolevSq ((1 - s.val) / 2)
        ⟨fun t : UnitAddCircle => ((arcIndicator c a t - 2 * a : ℝ) : ℂ),
          memLp_centredArc c a⟩ ≠ ⊤ ∧
      (2 * Real.pi) ^ (1 - s.val) / (2 * β * rieszConstant s) *
          (circleSobolevSq ((1 - s.val) / 2)
            ⟨fun t : UnitAddCircle => ((arcIndicator c a t - 2 * a : ℝ) : ℂ),
              memLp_centredArc c a⟩).toReal =
        Real.cos (Real.pi * s.val / 2) / Real.sin (Real.pi * s.val / 2) /
            (2 * Real.pi * β * s.val) * periodicZeta s ((2 * a : ℝ) : UnitAddCircle)) ∧
    (∀ k : ℤ, transportCoeffs ⟨(β, s.val), hβ, s.2.1, s.2.2⟩ ⟨1, one_pos⟩
          ⟨fun t => arcIndicator c a t, memLp_arcIndicator c a⟩ k =
        transportCoeffs ⟨(β, s.val), hβ, s.2.1, s.2.2⟩ ⟨1, one_pos⟩
          ⟨fun t => arcIndicator c a t - 2 * a, memLp_centredArc c a⟩ k) ∧
    circleSobolevSq ((1 - s.val) / 2)
        ⟨fun t : UnitAddCircle => (arcIndicator c a t : ℂ), memLp_arcIndicator c a⟩ =
      circleSobolevSq ((1 - s.val) / 2)
        ⟨fun t : UnitAddCircle => ((arcIndicator c a t - 2 * a : ℝ) : ℂ),
          memLp_centredArc c a⟩ := by
  obtain ⟨_, hunique, henergy, htr, _⟩ := explicit_formulas_indicator s β hβ a ha0 ha1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (continuous_transportFormula_real (s := s) β a).comp (continuous_id.sub continuous_const)
  · intro ψ hψ
    -- The translate `x ↦ ψ(x + c)` has the transport coefficients of the arc about `0`.
    have hψmem : MemLp (fun x : UnitAddCircle => (ψ.val (x + c) : ℂ)) 2 volume :=
      ψ.property.comp_measurePreserving (measurePreserving_add_right volume c)
    have hcoeff : ∀ k : ℤ, fourierCoeff (fun x : UnitAddCircle => (ψ.val x : ℂ)) k =
        fourier (-k) c * transportCoeffs ⟨(β, s.val), hβ, s.2.1, s.2.2⟩ ⟨1, one_pos⟩
          ⟨centeredIndicatorArc a, memLp_centeredIndicatorArc a⟩ k := fun k =>
      (hψ k).trans (transportCoeffs_centredArc_centre ⟨(β, s.val), hβ, s.2.1, s.2.2⟩ ha1 c k)
    have hφ : ∀ k : ℤ, coeff ⟨1, one_pos⟩
        ⟨fun x => ((ψ.val (x + c)) : ℂ), complexL2Integrable ⟨1, one_pos⟩ _ hψmem⟩ k =
        transportCoeffs ⟨(β, s.val), hβ, s.2.1, s.2.2⟩ ⟨1, one_pos⟩
          ⟨centeredIndicatorArc a, memLp_centeredIndicatorArc a⟩ k := by
      intro k
      show fourierCoeff (fun x : UnitAddCircle => ((ψ.val (x + c)) : ℂ)) k = _
      rw [fourierCoeff_add_centre (fun x : UnitAddCircle => (ψ.val x : ℂ)) c k, hcoeff k,
        ← mul_assoc, fourier_neg_mul_fourier_eq_one, one_mul]
    have hae : ∀ᵐ x ∂(arclength ⟨1, one_pos⟩), ψ.val (x + c) = transportFormula s β a x :=
      hunique ⟨fun x => ψ.val (x + c), hψmem⟩ hφ
    have hback := (measurePreserving_sub_right volume c).quasiMeasurePreserving.ae hae
    filter_upwards [hback] with x hx
    rw [sub_add_cancel] at hx
    exact hx
  · refine ⟨?_, ?_⟩
    · rw [circleSobolevSq_centredArc_centre ha1 c ((1 - s.val) / 2)]
      exact henergy.1
    · rw [circleSobolevSq_centredArc_centre ha1 c ((1 - s.val) / 2)]
      exact henergy.2
  · intro k
    rw [transportCoeffs_arcIndicator_centre _ ha1 c k, transportCoeffs_centredArc_centre _ ha1 c k,
      htr k]
  · exact circleSobolevSq_arcIndicator_centre ha1 c ((1 - s.val) / 2)

end Riesz1

end
