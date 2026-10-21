/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.VarAlPiecesEnvelopeCore
public import Riesz1.Variance.RegUniformFirstTransport
public import Riesz1.Variance.RegUniformSecondTransport
public import Riesz1.Variance.RegUniformTransport
public import Riesz1.ToMathlib.CircleCoeffUniqueness
public import Riesz1.ToMathlib.CircleMollifyBounds
public import Riesz1.ToMathlib.MollifierPointwise.Derivative

/-!
# Decomposition and envelopes of the regularized transport, macroscopic circle

Proposition 5.9, macroscopic case. On the unit circle the regularized transport
`ψ_h` is the sum of `n + 1` smooth periodic pieces: the cutoff pieces `χ_j ψ_h` around the marks and
the remainder `(1 - ∑ χ_j) ψ_h`. After translating a singular piece to its mark, both derivatives
are bounded by the envelopes of `gradWeightOne` and `gradWeightTwo` with `K = N`, with a constant
independent of `N`, `h` and the transport.

The weights are written out as the defining `if` expressions of `gradWeightOne` and
`gradWeightTwo` (`Riesz1/Auxiliary/GradientSplittingZWeights.lean`). That file and
`MollifierPointwise/Circle.lean` both declare `Riesz1.circDist`, so they cannot be imported
together. The expressions agree with the library definitions by unfolding.
-/

public section

open MeasureTheory Filter Set
open scoped ContDiff Topology

namespace Riesz1

/-- The constant of the envelopes of the pieces, from the derivative bounds of the bump, the
sup bound `S` of the smoothed transport, the envelope amplitude `A`, the number `p` of marks,
the radius `r` of the cutoffs, and the exponent `b`. -/
noncomputable def varAlConst (M1 M2 S A r : ℝ) (p : ℕ) (b : ℝ) : ℝ :=
  1 + ((M1 * S + A * (1 + p + p * (4 * r) ^ (-b))) +
    (M2 * S + 2 * M1 * (A * (1 + p + p * (4 * r) ^ (-b))) +
      A * (1 + p + p * (4 * r) ^ (-1 - b))) +
    (p * M1 * S + (1 + p) * (A * (1 + p * r ^ (-b)))) +
    (p * M2 * S + 2 * (p * M1) * (A * (1 + p * r ^ (-b))) +
      (1 + p) * (A * (1 + p * r ^ (-1 - b)))))

/-- The four constants of the envelopes are nonnegative, so each is at most `varAlConst`. -/
lemma varAlConst_bounds {M1 M2 S A r : ℝ} {p : ℕ} (hM1 : 0 ≤ M1) (hM2 : 0 ≤ M2)
    (hS : 0 ≤ S) (hA : 0 ≤ A) (hr : 0 < r) (b : ℝ) :
    (M1 * S + A * (1 + p + p * (4 * r) ^ (-b))) ≤ varAlConst M1 M2 S A r p b ∧
    (M2 * S + 2 * M1 * (A * (1 + p + p * (4 * r) ^ (-b))) +
      A * (1 + p + p * (4 * r) ^ (-1 - b))) ≤ varAlConst M1 M2 S A r p b ∧
    (p * M1 * S + (1 + p) * (A * (1 + p * r ^ (-b)))) ≤ varAlConst M1 M2 S A r p b ∧
    (p * M2 * S + 2 * (p * M1) * (A * (1 + p * r ^ (-b))) +
      (1 + p) * (A * (1 + p * r ^ (-1 - b)))) ≤ varAlConst M1 M2 S A r p b ∧
    1 ≤ varAlConst M1 M2 S A r p b := by
  have hp : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hc : 0 ≤ (4 * r) ^ (-b) := Real.rpow_nonneg (by linarith) _
  have hc2 : 0 ≤ (4 * r) ^ (-1 - b) := Real.rpow_nonneg (by linarith) _
  have hd : 0 ≤ r ^ (-b) := Real.rpow_nonneg hr.le _
  have hd2 : 0 ≤ r ^ (-1 - b) := Real.rpow_nonneg hr.le _
  have h1 : 0 ≤ 1 + (p : ℝ) + p * (4 * r) ^ (-b) := by
    have := mul_nonneg hp hc
    linarith
  have h2 : 0 ≤ 1 + (p : ℝ) + p * (4 * r) ^ (-1 - b) := by
    have := mul_nonneg hp hc2
    linarith
  have h3 : 0 ≤ 1 + (p : ℝ) * r ^ (-b) := by
    have := mul_nonneg hp hd
    linarith
  have h4 : 0 ≤ 1 + (p : ℝ) * r ^ (-1 - b) := by
    have := mul_nonneg hp hd2
    linarith
  have t1 : 0 ≤ M1 * S := mul_nonneg hM1 hS
  have t2 : 0 ≤ M2 * S := mul_nonneg hM2 hS
  have t3 : 0 ≤ A * (1 + p + p * (4 * r) ^ (-b)) := mul_nonneg hA h1
  have t4 : 0 ≤ A * (1 + p + p * (4 * r) ^ (-1 - b)) := mul_nonneg hA h2
  have t5 : 0 ≤ A * (1 + p * r ^ (-b)) := mul_nonneg hA h3
  have t6 : 0 ≤ A * (1 + p * r ^ (-1 - b)) := mul_nonneg hA h4
  have t7 : 0 ≤ 2 * M1 * (A * (1 + p + p * (4 * r) ^ (-b))) :=
    mul_nonneg (mul_nonneg (by norm_num) hM1) t3
  have t8 : 0 ≤ p * M1 * S := mul_nonneg (mul_nonneg hp hM1) hS
  have t9 : 0 ≤ p * M2 * S := mul_nonneg (mul_nonneg hp hM2) hS
  have t10 : 0 ≤ 2 * (p * M1) * (A * (1 + p * r ^ (-b))) :=
    mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg hp hM1)) t5
  have t11 : 0 ≤ (1 + p) * (A * (1 + p * r ^ (-b))) := mul_nonneg (by linarith) t5
  have t12 : 0 ≤ (1 + p) * (A * (1 + p * r ^ (-1 - b))) := mul_nonneg (by linarith) t6
  have hsum : 0 ≤ (M1 * S + A * (1 + p + p * (4 * r) ^ (-b))) +
      (M2 * S + 2 * M1 * (A * (1 + p + p * (4 * r) ^ (-b))) +
        A * (1 + p + p * (4 * r) ^ (-1 - b))) +
      (p * M1 * S + (1 + p) * (A * (1 + p * r ^ (-b)))) +
      (p * M2 * S + 2 * (p * M1) * (A * (1 + p * r ^ (-b))) +
        (1 + p) * (A * (1 + p * r ^ (-1 - b)))) := by
    linarith
  have hC : varAlConst M1 M2 S A r p b = 1 + ((M1 * S + A * (1 + p + p * (4 * r) ^ (-b))) +
      (M2 * S + 2 * M1 * (A * (1 + p + p * (4 * r) ^ (-b))) +
        A * (1 + p + p * (4 * r) ^ (-1 - b))) +
      (p * M1 * S + (1 + p) * (A * (1 + p * r ^ (-b)))) +
      (p * M2 * S + 2 * (p * M1) * (A * (1 + p * r ^ (-b))) +
        (1 + p) * (A * (1 + p * r ^ (-1 - b))))) := rfl
  have hE1 : 0 ≤ M1 * S + A * (1 + p + p * (4 * r) ^ (-b)) := by linarith
  have hE2 : 0 ≤ M2 * S + 2 * M1 * (A * (1 + p + p * (4 * r) ^ (-b))) +
      A * (1 + p + p * (4 * r) ^ (-1 - b)) := by linarith
  have hE3 : 0 ≤ p * M1 * S + (1 + p) * (A * (1 + p * r ^ (-b))) := by linarith
  have hE4 : 0 ≤ p * M2 * S + 2 * (p * M1) * (A * (1 + p * r ^ (-b))) +
      (1 + p) * (A * (1 + p * r ^ (-1 - b))) := by linarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rw [hC] <;> linarith

/-- The distance to `0` of a point of the unit circle is less than one. -/
lemma circDist_unit_lt_one (x : ℝ) : circDist unitLength.val x < 1 := by
  have h := abs_cutRep_le_half (L := unitLength.val) (by norm_num [unitLength]) x
  have e : circDist unitLength.val x = |cutRep unitLength.val x| := rfl
  have hu : unitLength.val / 2 = (1 : ℝ) / 2 := by norm_num [unitLength]
  rw [e]
  rw [hu] at h
  linarith

/-- On the unit circle the weight branch of the envelopes is the first one. -/
lemma ite_unit_eq {A B : ℝ} (x : ℝ) :
    (if circDist unitLength.val x < 1 then A else B) = A := by
  simp [circDist_unit_lt_one x]

/-- The unit-scale weight is at least one at every point of the unit circle. -/
lemma one_le_unit_weight {K : ℝ} (hK : 1 ≤ K) {e : ℝ} (he : e ≤ 0) (x : ℝ) :
    1 ≤ max (circDist unitLength.val x) K⁻¹ ^ e := by
  have hKinv : K⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hK
  have hpos : 0 < max (circDist unitLength.val x) K⁻¹ :=
    lt_max_of_lt_right (inv_pos.mpr (by linarith))
  have hle : max (circDist unitLength.val x) K⁻¹ ≤ 1 :=
    max_le (circDist_unit_lt_one x).le hKinv
  exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hpos hle he

/-- The pieces of a smooth periodic function on the unit circle, with envelopes of the singular
pieces and of the remainder. Only the cutoff data, the separation of the marks and the envelope
data of the function enter. -/
theorem pieces_envelope_of_data {r δ M1 M2 S A b K h₀ : ℝ} {p : ℕ}
    (hr : 0 < r) (hr16 : r ≤ 1 / 16) (hδr : 6 * r ≤ δ)
    (hM1 : ∀ s, |deriv (cutoffBump r) s| ≤ M1)
    (hM2 : ∀ s, |deriv (deriv (cutoffBump r)) s| ≤ M2)
    (marks : Fin p → ℝ)
    (hsep : ∀ i k, i ≠ k → δ ≤ circDist unitLength.val (marks i - marks k))
    {F : ℝ → ℝ} (hFC : ContDiff ℝ ∞ F) (hFP : Function.Periodic F unitLength.val)
    (hFS : ∀ x, |F x| ≤ S) (hA : 0 ≤ A) (hb : 0 < b) (hK : 1 ≤ K) (hh : K⁻¹ ≤ h₀)
    (hD1 : ∀ x, |deriv F x| ≤ A * (1 + ∑ k, max (circDist unitLength.val (x - marks k)) h₀ ^ (-b)))
    (hD2 : ∀ x, |deriv (deriv F) x| ≤
      A * (1 + ∑ k, max (circDist unitLength.val (x - marks k)) h₀ ^ (-1 - b))) :
    ∃ φ : Fin (p + 1) → ℝ → ℝ,
      (∀ j, ContDiff ℝ ∞ (φ j) ∧ Function.Periodic (φ j) unitLength.val ∧
          ∃ C' : NNReal, LipschitzWith C' (φ j)) ∧
      (∀ x : ℝ, F x = ∑ j, φ j x) ∧
      (∀ j, ∃ a : ℝ,
          (∀ x : ℝ, |deriv (fun t => φ j (t + a)) x| ≤
              varAlConst M1 M2 S A r p b *
                (if circDist unitLength.val x < 1 then
                  max (circDist unitLength.val x) K⁻¹ ^ (-b) else 0)) ∧
          (∀ x : ℝ, |deriv (deriv (fun t => φ j (t + a))) x| ≤
              varAlConst M1 M2 S A r p b *
                (if circDist unitLength.val x < 1 then
                  max (circDist unitLength.val x) K⁻¹ ^ (-1 - b) else 0))) := by
  have hL0 : (0 : ℝ) < unitLength.val := by norm_num [unitLength]
  have hL1 : (1 : ℝ) ≤ unitLength.val := by norm_num [unitLength]
  have hLr : 4 * r < unitLength.val := by
    have : (4 : ℝ) * r < 1 := by linarith
    linarith [hL1]
  have hS : 0 ≤ S := (abs_nonneg _).trans (hFS 0)
  have hM1nn : 0 ≤ M1 := (abs_nonneg _).trans (hM1 0)
  have hM2nn : 0 ≤ M2 := (abs_nonneg _).trans (hM2 0)
  obtain ⟨c1, c2, c3, c4, hC1⟩ := varAlConst_bounds (p := p) hM1nn hM2nn hS hA hr b
  have hCnn : 0 ≤ varAlConst M1 M2 S A r p b := le_trans zero_le_one hC1
  have hζ := contDiff_cutoffBump r
  have hζ0 : ∀ s, 2 * r ≤ |s| → cutoffBump r s = 0 := fun s hs => cutoffBump_eq_zero hr hs
  refine ⟨varAlPiece (cutoffBump r) unitLength.val marks F, ?_, ?_, ?_⟩
  · intro j
    have hsm := contDiff_varAlPiece (ζ := cutoffBump r) hζ hζ0 hL0 hLr marks hFC j
    have hper := periodic_varAlPiece (ζ := cutoffBump r) hL0 marks hFP j
    exact ⟨hsm, hper, lipschitz_of_periodic_contDiff hL0 hsm hper⟩
  · intro x
    exact (sum_varAlPiece (cutoffBump r) unitLength.val marks F x).symm
  · intro j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · -- The remainder piece, translated by `0`.
      refine ⟨0, fun x => ?_, fun x => ?_⟩
      · simp only [add_zero]
        have hrem := (remainder_envelope hζ hζ0 (fun s hs => cutoffBump_eq_one hs)
          (fun s => cutoffBump_mem_Icc r s) hM1 hM2 hL1 marks hsep hr hr16 hδr hFC hFS hA hb
          hD1 hD2 x).1
        have hw := one_le_unit_weight hK (e := -b) (by linarith) x
        rw [ite_unit_eq x]
        exact hrem.trans (c3.trans (le_mul_of_one_le_right hCnn hw))
      · simp only [add_zero]
        have hrem := (remainder_envelope hζ hζ0 (fun s hs => cutoffBump_eq_one hs)
          (fun s => cutoffBump_mem_Icc r s) hM1 hM2 hL1 marks hsep hr hr16 hδr hFC hFS hA hb
          hD1 hD2 x).2
        have hw := one_le_unit_weight hK (e := -1 - b) (by linarith) x
        rw [ite_unit_eq x]
        exact hrem.trans (c4.trans (le_mul_of_one_le_right hCnn hw))
    · -- A singular piece, translated to its mark.
      refine ⟨marks i, fun x => ?_, fun x => ?_⟩
      · rw [deriv_comp_add_const]
        have hs := (sing_envelope hζ hζ0 (fun s => cutoffBump_mem_Icc r s) hM1 hM2
          hL1 marks hsep hr hr16 hδr hFC hFS hA hb hK hh hD1 hD2 i x).1
        rw [ite_unit_eq x] at hs ⊢
        have hW : 0 ≤ max (circDist unitLength.val x) K⁻¹ ^ (-b) :=
          Real.rpow_nonneg (le_max_of_le_right (inv_nonneg.mpr (by linarith))) _
        exact hs.trans (mul_le_mul_of_nonneg_right c1 hW)
      · have hfun : deriv (fun t => varAlPiece (cutoffBump r) unitLength.val marks F
            (Fin.castSucc i) (t + marks i)) =
            fun t => deriv (varAlPiece (cutoffBump r) unitLength.val marks F
              (Fin.castSucc i)) (t + marks i) :=
          funext fun t => deriv_comp_add_const _ _ _
        rw [hfun, deriv_comp_add_const]
        have hs := (sing_envelope hζ hζ0 (fun s => cutoffBump_mem_Icc r s) hM1 hM2
          hL1 marks hsep hr hr16 hδr hFC hFS hA hb hK hh hD1 hD2 i x).2
        rw [ite_unit_eq x] at hs ⊢
        have hW : 0 ≤ max (circDist unitLength.val x) K⁻¹ ^ (-1 - b) :=
          Real.rpow_nonneg (le_max_of_le_right (inv_nonneg.mpr (by linarith))) _
        exact hs.trans (mul_le_mul_of_nonneg_right c2 hW)

/-- The macroscopic decomposition, with envelopes of the singular pieces and of the remainder. The
transport of a test profile is identified with the transports of the regularization
theorems by Fourier uniqueness. -/
theorem varAl_envelope_macro (P : Parameters) (p : Profile) (η B C₀ : ℝ) (n : ℕ+)
    (marks : Fin (n : ℕ) → ℝ) (α : ℝ) (hη : 0 < η) (hB : 0 < B) (hC₀ : 0 < C₀)
    (hα0 : P.val.2 - 1 < α) (hα1 : α < P.val.2 / 2)
    (hprim : PrimitiveRegularity unitLength η P.val.2 B ⟨p.val, p.property⟩)
    (hreg : TransportRegularity P unitLength ⟨p.val, p.property⟩ n marks α C₀)
    (ρ : ℝ → ℝ) (hρ : IsMollifier ρ) :
    ∃ (m : ℕ) (C : ℝ), 0 < C ∧ ∀ (N : ℕ+) (h : ℝ), 1 ≤ (N : ℝ) → ((N : ℝ))⁻¹ ≤ h → h ≤ 1 →
      ∀ ψ : {g : Circle unitLength → ℝ // MemLp (fun x => (g x : ℂ)) 2 (arclength unitLength)},
        (∀ k : ℤ, coeff unitLength ⟨(fun x => (ψ.val x : ℂ)), complexL2Integrable _ _ ψ.property⟩ k
            = transportCoeffs P unitLength ⟨p.val, p.property⟩ k) →
        Continuous ψ.val →
        ∃ φ : Fin m → ℝ → ℝ,
          (∀ j, ContDiff ℝ ∞ (φ j) ∧ Function.Periodic (φ j) unitLength.val ∧
              ∃ C' : NNReal, LipschitzWith C' (φ j)) ∧
          (∀ x : ℝ, circleMollify ρ unitLength.val h
              (fun t : ℝ => ψ.val (t : Circle unitLength)) x = ∑ j, φ j x) ∧
          (∀ j, ∃ a : ℝ,
              (∀ x : ℝ, |deriv (fun t => φ j (t + a)) x| ≤
                  C * (if circDist unitLength.val x < 1 then
                    max (circDist unitLength.val x) (N : ℝ)⁻¹ ^ (-(1 - P.val.2 + α))
                    else circDist unitLength.val x ^ (P.val.2 - 2))) ∧
              (∀ x : ℝ, |deriv (deriv (fun t => φ j (t + a))) x| ≤
                  C * (if circDist unitLength.val x < 1 then
                    max (circDist unitLength.val x) (N : ℝ)⁻¹ ^ (-(1 + (1 - P.val.2 + α)))
                    else circDist unitLength.val x ^ (P.val.2 - 3)))) := by
  classical
  have hL0 : (0 : ℝ) < unitLength.val := by norm_num [unitLength]
  -- Separation of the marks and the cutoff radius.
  have hinj : Function.Injective (fun j : Fin (n : ℕ) => ((marks j : ℝ) : Circle unitLength)) :=
    hreg.1
  obtain ⟨δ, hδ0, hδsep⟩ := exists_pos_le_dist_of_injective hinj
  have hsep : ∀ i k : Fin (n : ℕ), i ≠ k → δ ≤ circDist unitLength.val (marks i - marks k) := by
    intro i k hik
    have h1 := hδsep i k hik
    rwa [dist_coe_eq_circDist_sub hL0] at h1
  obtain ⟨r, hr_def⟩ : ∃ r : ℝ, r = min (δ / 6) (1 / 16) := ⟨_, rfl⟩
  have hr : 0 < r := by
    rw [hr_def]
    exact lt_min (by linarith) (by norm_num)
  have hr16 : r ≤ 1 / 16 := by
    rw [hr_def]
    exact min_le_right _ _
  have hδr : 6 * r ≤ δ := by
    have h1 := min_le_left (δ / 6) (1 / 16)
    rw [← hr_def] at h1
    linarith
  obtain ⟨M1, M2, hM1, hM2⟩ := exists_bounds_deriv_bump (contDiff_cutoffBump r)
    (fun s hs => cutoffBump_eq_zero hr hs)
  -- The transports from the regularization theorems.
  have hα0' : P.val.2 - 1 ≤ α := hα0.le
  obtain ⟨C₁, hC₁, ψ₁, hψ₁c, hψ₁m, hψ₁coeff, hD1raw⟩ :=
    regUniform_firstTransport_macroscopic P p η B n marks α α C₀ hη hB.le hC₀.le hα0' hα1
      le_rfl hα0 hα1 hprim hreg ρ hρ
  obtain ⟨C₂, hC₂, ψ₂, hψ₂c, hψ₂m, hψ₂coeff, hD2raw⟩ :=
    regUniform_secondTransport_macroscopic P p η B n marks α α C₀ hη hB.le hC₀.le hα0' hα1
      le_rfl hα0 hα1 hprim hreg ρ hρ
  obtain ⟨Cs, hCs, hsup⟩ := regUniform_transport_sup P η B hη hB.le
  obtain ⟨ψs, hψsc, hψsm, hψscoeff, -, hψsmoll⟩ :=
    hsup unitLength ⟨p.val, p.property⟩ hprim
  have hb : 0 < 1 - P.val.2 + α := by linarith
  have hA : 0 ≤ max C₁ C₂ := le_trans hC₁.le (le_max_left _ _)
  have hM1nn : 0 ≤ M1 := (abs_nonneg _).trans (hM1 0)
  have hM2nn : 0 ≤ M2 := (abs_nonneg _).trans (hM2 0)
  have hCsnn : 0 ≤ Cs := hCs.le
  have hconst : 1 ≤ varAlConst M1 M2 Cs (max C₁ C₂) r (n : ℕ) (1 - P.val.2 + α) :=
    (varAlConst_bounds (p := (n : ℕ)) hM1nn hM2nn hCsnn hA hr _).2.2.2.2
  refine ⟨(n : ℕ) + 1, varAlConst M1 M2 Cs (max C₁ C₂) r (n : ℕ) (1 - P.val.2 + α),
    lt_of_lt_of_le one_pos hconst, ?_⟩
  intro N h hN hNh hh1 ψ hψcoeff hψcont
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le one_pos hN
  have hh0 : 0 < h := lt_of_lt_of_le (inv_pos.mpr hNpos) hNh
  -- Identify the transports of `ψ` with the ones from the regularization theorems.
  have hψ1 : ψ.val = ψ₁ :=
    continuous_eq_of_coeff_eq hψcont hψ₁c ψ.property hψ₁m
      (fun k => (hψcoeff k).trans (hψ₁coeff k).symm)
  have hψ2 : ψ.val = ψ₂ :=
    continuous_eq_of_coeff_eq hψcont hψ₂c ψ.property hψ₂m
      (fun k => (hψcoeff k).trans (hψ₂coeff k).symm)
  have hψs : ψ.val = ψs :=
    continuous_eq_of_coeff_eq hψcont hψsc ψ.property hψsm
      (fun k => (hψcoeff k).trans (hψscoeff k).symm)
  have hlocI : LocallyIntegrable (fun t : ℝ => ψ.val (t : Circle unitLength)) volume :=
    (hψcont.comp (AddCircle.continuous_mk' unitLength.val)).locallyIntegrable
  have hperψ : Function.Periodic (fun t : ℝ => ψ.val (t : Circle unitLength))
      unitLength.val := by
    intro t
    simp only [AddCircle.coe_add_period]
  have hFC : ContDiff ℝ ∞
      (circleMollify ρ unitLength.val h (fun t : ℝ => ψ.val (t : Circle unitLength))) :=
    contDiff_circleMollify hρ hL0 hh0 hlocI hperψ
  have hFP : Function.Periodic
      (circleMollify ρ unitLength.val h (fun t : ℝ => ψ.val (t : Circle unitLength)))
      unitLength.val :=
    Riesz1.Internal.circleMollify_periodic hρ hL0 hh0 hlocI hperψ
  have hFS : ∀ x, |circleMollify ρ unitLength.val h
      (fun t : ℝ => ψ.val (t : Circle unitLength)) x| ≤ Cs := by
    intro x
    have h1 := hψsmoll ρ hρ h hh0 x
    rw [← hψs] at h1
    exact h1
  have hD1 : ∀ x, |deriv (circleMollify ρ unitLength.val h
      (fun t : ℝ => ψ.val (t : Circle unitLength))) x| ≤
      max C₁ C₂ * (1 + ∑ k, max (circDist unitLength.val (x - marks k)) h ^
        (-(1 - P.val.2 + α))) := by
    intro x
    have h1 := hD1raw h hh0 hh1 x
    rw [← hψ1] at h1
    simp only [dist_coe_eq_circDist_sub hL0] at h1
    have e : -1 + P.val.2 - α = -(1 - P.val.2 + α) := by ring
    rw [e] at h1
    have hsum0 : 0 ≤ ∑ k, max (circDist unitLength.val (x - marks k)) h ^
        (-(1 - P.val.2 + α)) :=
      Finset.sum_nonneg fun k _ => Real.rpow_nonneg (le_max_of_le_right hh0.le) _
    calc _ ≤ C₁ * (1 + ∑ k, max (circDist unitLength.val (x - marks k)) h ^
          (-(1 - P.val.2 + α))) := h1
      _ ≤ max C₁ C₂ * (1 + ∑ k, max (circDist unitLength.val (x - marks k)) h ^
          (-(1 - P.val.2 + α))) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)
  have hD2 : ∀ x, |deriv (deriv (circleMollify ρ unitLength.val h
      (fun t : ℝ => ψ.val (t : Circle unitLength)))) x| ≤
      max C₁ C₂ * (1 + ∑ k, max (circDist unitLength.val (x - marks k)) h ^
        (-1 - (1 - P.val.2 + α))) := by
    intro x
    have h1 := hD2raw h hh0 hh1 x
    rw [← hψ2] at h1
    simp only [dist_coe_eq_circDist_sub hL0] at h1
    have e : -2 + P.val.2 - α = -1 - (1 - P.val.2 + α) := by ring
    rw [e] at h1
    have hsum0 : 0 ≤ ∑ k, max (circDist unitLength.val (x - marks k)) h ^
        (-1 - (1 - P.val.2 + α)) :=
      Finset.sum_nonneg fun k _ => Real.rpow_nonneg (le_max_of_le_right hh0.le) _
    calc _ ≤ C₂ * (1 + ∑ k, max (circDist unitLength.val (x - marks k)) h ^
          (-1 - (1 - P.val.2 + α))) := h1
      _ ≤ max C₁ C₂ * (1 + ∑ k, max (circDist unitLength.val (x - marks k)) h ^
          (-1 - (1 - P.val.2 + α))) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith)
  obtain ⟨φ, hφ1, hφsum, hφb⟩ :=
    pieces_envelope_of_data (b := 1 - P.val.2 + α) (K := (N : ℝ)) hr hr16 hδr hM1 hM2 marks
      hsep hFC hFP hFS hA hb hN hNh hD1 hD2
  refine ⟨φ, hφ1, fun x => hφsum x, fun j => ?_⟩
  obtain ⟨a, ha1, ha2⟩ := hφb j
  refine ⟨a, fun x => ?_, fun x => ?_⟩
  · have h1 := ha1 x
    rw [ite_unit_eq x] at h1 ⊢
    exact h1
  · have h1 := ha2 x
    rw [show (-(1 + (1 - P.val.2 + α))) = -1 - (1 - P.val.2 + α) by ring]
    rw [ite_unit_eq x] at h1 ⊢
    exact h1

end Riesz1

end
