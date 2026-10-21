/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.VarAlGapCutoffBridge
public import Riesz1.Variance.APrioriCutoffComplete

/-!
# Negligible inverse energy of the loop cutoff error

The second assertion of Proposition 5.9, taking `External.BakryEmery` and
`External.PrekopaLeindler` as hypotheses, with the actual larger-window
anchored inverse.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace Riesz1

theorem varAlGap_transport_support {χ ψ : ℝ → ℝ}
    (hχs : tsupport χ ⊆ Ioo (-(1 / 4)) (1 / 4))
    {N : ℕ+} {ℓ γ : ℝ} (hℓ : 0 < ℓ) (hP : GradPartial N ℓ γ)
    (y : ℝ) (hy : ∀ m : ℤ, gradT N ℓ γ / 4 ≤ |y - m|) :
    loopTransport χ N ℓ γ ψ (y / ℓ) = 0 := by
  have ht : 0 < gradT N ℓ γ := by
    unfold gradT
    rw [ite_eq_left hP]
    exact div_pos (Real.rpow_pos_of_pos (mul_pos (by positivity) hℓ) γ) (by positivity)
  have hn := hy ⌊y + 1 / 2⌋
  have heq : ℓ * loopCircleRep ℓ (y / ℓ) = y - (⌊y + 1 / 2⌋ : ℤ) := by
    unfold loopCircleRep
    field_simp
  have hfar : 1 / 4 ≤ |ℓ * loopCircleRep ℓ (y / ℓ) / gradT N ℓ γ| := by
    rw [heq, abs_div, abs_of_pos ht, le_div_iff₀ ht]
    linarith
  have hnot : ℓ * loopCircleRep ℓ (y / ℓ) / gradT N ℓ γ ∉ tsupport χ := by
    intro h
    have := abs_lt.mpr (hχs h)
    linarith
  simp only [loopTransport, hP, ↓reduceIte]
  rw [image_eq_zero_of_notMem_tsupport hnot, zero_mul]

/-- Proposition 5.9, cutoff-error assertion. In fact every
prescribed power `b > 0` is available. All constants precede the particle
number, forcing cutoff, scale and transport. -/
theorem varAl_gap_cutoff_energy (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (P : Parameters) {α γ ε C₀ b : ℝ}
    (hα : P.val.2 - 1 ≤ α) (hα2 : α < P.val.2 / 2) (hγ : 1 < γ)
    (hε : 0 < ε) (hεs : ε ≤ 1 - P.val.2 / 2) (hC₀ : 0 < C₀) (hb : 0 < b)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hχs : tsupport χ ⊆ Ioo (-(1 / 4)) (1 / 4))
    (hχ1 : ∀ x : ℝ, |x| ≤ 1 / 8 → χ x = 1) (hχ01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 1 ≤ n →
      ∀ (θ : ℝ → ℝ) (hθ : IsForcingCutoff θ) (ℓ : ℝ),
        0 < ℓ → ℓ ≤ 1 → ∀ (hK : 1 ≤ (n.succPNat : ℝ) * ℓ),
        ∀ (ψ : ℝ → ℝ), ContDiff ℝ ∞ ψ → Function.Periodic ψ ℓ⁻¹ →
          (∀ t, |deriv ψ t| ≤ C₀ * gradWeightOne P.val.2 (1 - P.val.2 + α)
            ((n.succPNat : ℝ) * ℓ) ℓ⁻¹ t) →
          (∀ t, |deriv (deriv ψ) t| ≤ C₀ * gradWeightTwo P.val.2 (1 - P.val.2 + α)
            ((n.succPNat : ℝ) * ℓ) ℓ⁻¹ t) →
          let K := (n.succPNat : ℝ) * ℓ
          let Q := nearestTiltedPairs P n.succPNat hθ K (2 * γ) ε (by linarith)
          let v := fun y : AnchoredEuclidean n => WithLp.toLp 2 fun i : Fin n =>
            gradLoop P.val.2 (loopTransport χ n.succPNat ℓ γ ψ) n.succPNat ℓ γ
              (anchorVector (WithLp.ofLp y)) *
            fderiv ℝ (fun z => loopCutoff P.val.2 γ ε n.succPNat ℓ (anchorVector z))
              (WithLp.ofLp y) (Pi.single i (1 : ℝ))
          ∃ hv : MemLp v 2 (anchoredMeasureE Q),
            anchoredInverseEnergy Q
              (hsRieszPairPotentials_curvature_pos n.succPNat P.2.1 (parametersExponent P))
              (hv.toLp v) ≤ C * K ^ (-b) := by
  classical
  obtain ⟨Cl, hCl, hl⟩ := varAl_loop_good_bound P.2.2.1 P.2.2.2 hα hα2 hγ hε hεs
    hχ hχc hχs hχ1 hχ01
  let D := (1 - P.val.2 + α) + 2 * γ + ε * (P.val.2 + 1)
  let M := (Cl + 1) * C₀
  have hD : 0 < D := by
    dsimp [D]
    have : 0 ≤ 1 - P.val.2 + α := by linarith
    have : 0 < P.val.2 + 1 := by linarith [P.2.2.1]
    positivity
  have hM : 0 < M := by dsimp [M]; positivity
  obtain ⟨C, hC, hc⟩ := anchoredCutoff_energy hBE hPL P (2 * γ) ε (by linarith) hε
    D M b hD hM hb
  refine ⟨C, hC, ?_⟩
  intro n hn θ hθ ℓ hℓ hℓ1 hK ψ hψ hp h1 h2
  let N := n.succPNat
  let K := (N : ℝ) * ℓ
  let Q := nearestTiltedPairs P N hθ K (2 * γ) ε (by linarith : 0 < K)
  let μ := anchoredMeasureE Q
  let L := fun y : Fin n → ℝ =>
    gradLoop P.val.2 (loopTransport χ N ℓ γ ψ) N ℓ γ (anchorVector y)
  let T := (anchoredDomain n).piecewise L (fun _ => 0)
  have hav : Continuous (anchorVector : (Fin n → ℝ) → Fin (N : ℕ) → ℝ) :=
    continuous_pi fun k => continuous_anchorVector_apply k
  have hLc : ContinuousOn L (anchoredDomain n) :=
    ((gradient_splitting_identity (contDiff_loopTransport hχ hψ hχs N hℓ γ) hℓ
      (by simpa only [one_div] using loopTransport_periodic (N := N) (γ := γ) hℓ χ hp)
      P.2.2.1 P.2.2.2 (fun hP y hy => varAlGap_transport_support hχs hℓ hP y hy)).1.continuousOn).comp
      hav.continuousOn (fun _ hy => varAl_anchorVector_mem hy)
  have hTm : Measurable T := hLc.measurable_piecewise continuousOn_const (measurableSet_anchoredDomain n)
  have hT : ∀ y : Fin n → ℝ, fderiv ℝ (anchoredCutoff N P.val.2 K (2 * γ) ε) y ≠ 0 →
      |T y| ≤ M * K ^ D := by
    intro y hy
    by_cases hyd : y ∈ anchoredDomain n
    · rw [show T y = L y from piecewise_eq_of_mem _ _ _ hyd]
      have hder := varAlGap_fderiv_cutoff (γ := γ) hn hK P.val.2 ε hyd
      have hpos : 0 < loopCutoff P.val.2 γ ε N ℓ (anchorVector y) := by
        have hn0 := (loopCutoff_mem_Icc (N := N) P.val.2 γ ε ℓ (anchorVector y)).1
        apply lt_of_le_of_ne hn0
        intro heq
        apply hy
        rw [← hder]
        apply IsLocalMin.fderiv_eq_zero
        exact Filter.Eventually.of_forall fun z => by
          change loopCutoff P.val.2 γ ε N ℓ (anchorVector y) ≤
            loopCutoff P.val.2 γ ε N ℓ (anchorVector z)
          rw [← heq]
          exact (loopCutoff_mem_Icc P.val.2 γ ε ℓ (anchorVector z)).1
      have hgood := gradEvent_of_loopCutoff_pos hℓ
        (⟨anchorVector y, varAl_anchorVector_mem hyd⟩ : Configuration N) hpos
      exact (hl C₀ N ℓ ψ hC₀.le hℓ hK hψ hp h1 h2 _ hgood (anchorVector_zero y)).trans
        (mul_le_mul_of_nonneg_right (by dsimp [M]; nlinarith) (by positivity))
    · rw [show T y = 0 from piecewise_eq_of_notMem _ _ _ hyd, abs_zero]
      positivity
  have hKN : K ≤ (n : ℝ) + 1 := by
    dsimp [K, N]
    simpa only [Nat.succPNat_coe, Nat.cast_succ] using
      mul_le_of_le_one_right (show 0 ≤ (n.succPNat : ℝ) by positivity) hℓ1
  obtain ⟨hw, hwE⟩ := hc n hn θ hθ K hK hKN T hTm hT
  let v := fun y : AnchoredEuclidean n => WithLp.toLp 2 fun i : Fin n =>
    L (WithLp.ofLp y) * fderiv ℝ
      (fun z => loopCutoff P.val.2 γ ε N ℓ (anchorVector z)) (WithLp.ofLp y)
        (Pi.single i (1 : ℝ))
  have hvw : v =ᵐ[μ] anchoredCutoffField n P.val.2 K (2 * γ) ε T := by
    filter_upwards [ae_mem_anchoredSimplex Q] with y hy
    have hder := varAlGap_fderiv_cutoff (γ := γ) hn hK P.val.2 ε hy
    change WithLp.toLp 2 (fun i => _) = WithLp.toLp 2 (fun i => _)
    congr 1
    funext i
    rw [hder, show T (WithLp.ofLp y) = L (WithLp.ofLp y) from piecewise_eq_of_mem _ _ _ hy]
    rfl
  have hv : MemLp v 2 μ := hw.ae_eq hvw.symm
  refine ⟨hv, ?_⟩
  have heq : hv.toLp v = hw.toLp (anchoredCutoffField n P.val.2 K (2 * γ) ε T) := by
    apply Lp.ext
    exact hv.coeFn_toLp.trans (hvw.trans hw.coeFn_toLp.symm)
  rw [heq]
  exact hwE

end Riesz1

end
