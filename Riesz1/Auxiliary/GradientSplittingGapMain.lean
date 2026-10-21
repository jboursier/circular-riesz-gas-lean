/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.GradientSplittingGapBound
public import Riesz1.Auxiliary.GradientSplittingGapIdentity
public import Riesz1.Auxiliary.GradientSplittingDisplacement
public import Riesz1.Auxiliary.GradientSplittingConvolutionParticle

/-!
# The gap representative: the squared bound and the lemma

The gap part of Lemma 5.7, complete. The statement collects the
identity `W·U = -∑_i W^gap_i N(u_{i+1} - u_i)` and `∑_i W_i = 0` (proved in
`GradientSplittingGapIdentity.lean`), the pointwise bound `|W^gap_i| ≤ C C_0 K^{κε} ∑_j w_1(x_j/ℓ)
(1 + d(i,j))^{-(1+s/2)}` (`GradientSplittingGapBound.lean`), and the squared bound
`∑_i |W^gap_i|² ≤ C C_0² K^{κε} (K + K^{2a})`, proved here by the Schur test on the decay kernel and
the particle sum of the convolution part of Lemma 5.7.

The statement drops two hypotheses of the paper that the gap estimate does not use: the second
envelope `|ψ''| ≤ C_0 w_2` and the vanishing of `ψ` in a partial window. Both are weakenings of
the hypotheses, so the statement is a generalization.
-/

@[expose] public section

open Finset
open scoped ContDiff
open scoped Classical

namespace Riesz1

noncomputable section

/-! ## The Schur test -/

/-- The weighted Schur test: a nonnegative kernel `p` with row and column sums at most `D` gives
`∑_i (∑_j p_{ij} w_j)^2 ≤ D^2 ∑_j w_j^2`. -/
lemma gapSchur {ι : Type*} [DecidableEq ι] (T : Finset ι) (p : ι → ι → ℝ) (w : ι → ℝ) {D : ℝ}
    (hD : 0 ≤ D) (hp : ∀ i ∈ T, ∀ j ∈ T, 0 ≤ p i j) (hrow : ∀ i ∈ T, ∑ j ∈ T, p i j ≤ D)
    (hcol : ∀ j ∈ T, ∑ i ∈ T, p i j ≤ D) :
    ∑ i ∈ T, (∑ j ∈ T, p i j * w j) ^ 2 ≤ D ^ 2 * ∑ j ∈ T, (w j) ^ 2 := by
  have h1 : ∀ i ∈ T, (∑ j ∈ T, p i j * w j) ^ 2 ≤ D * ∑ j ∈ T, p i j * (w j) ^ 2 := by
    intro i hi
    have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul T
      (r := fun j => p i j * w j) (f := fun j => p i j) (g := fun j => p i j * (w j) ^ 2)
      (fun j hj => hp i hi j hj) (fun j hj => mul_nonneg (hp i hi j hj) (sq_nonneg _))
      (fun j _ => (show (p i j * w j) ^ 2 = p i j * (p i j * (w j) ^ 2) by ring).le)
    have hnn : 0 ≤ ∑ j ∈ T, p i j * (w j) ^ 2 :=
      Finset.sum_nonneg fun j hj => mul_nonneg (hp i hi j hj) (sq_nonneg _)
    calc (∑ j ∈ T, p i j * w j) ^ 2 ≤ (∑ j ∈ T, p i j) * ∑ j ∈ T, p i j * (w j) ^ 2 := hcs
      _ ≤ D * ∑ j ∈ T, p i j * (w j) ^ 2 := mul_le_mul_of_nonneg_right (hrow i hi) hnn
  have h2 : ∑ i ∈ T, ∑ j ∈ T, p i j * (w j) ^ 2 ≤ D * ∑ j ∈ T, (w j) ^ 2 := by
    rw [Finset.sum_comm]
    calc ∑ j ∈ T, ∑ i ∈ T, p i j * (w j) ^ 2 = ∑ j ∈ T, (∑ i ∈ T, p i j) * (w j) ^ 2 := by
          simp only [Finset.sum_mul]
      _ ≤ ∑ j ∈ T, D * (w j) ^ 2 :=
          Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_right (hcol j hj) (sq_nonneg _)
      _ = D * ∑ j ∈ T, (w j) ^ 2 := by rw [Finset.mul_sum]
  calc ∑ i ∈ T, (∑ j ∈ T, p i j * w j) ^ 2 ≤ ∑ i ∈ T, D * ∑ j ∈ T, p i j * (w j) ^ 2 :=
        Finset.sum_le_sum h1
    _ = D * ∑ i ∈ T, ∑ j ∈ T, p i j * (w j) ^ 2 := by rw [Finset.mul_sum]
    _ ≤ D * (D * ∑ j ∈ T, (w j) ^ 2) := mul_le_mul_of_nonneg_left h2 hD
    _ = D ^ 2 * ∑ j ∈ T, (w j) ^ 2 := by ring

/-! ## The microscopic weight in the variable `x / ℓ` -/

/-- The microscopic weight `W_1(N x) = w_1(x/ℓ)`, in the form of `gradWeightOne` used by the
statement. -/
lemma gapW1_eq_micro (s a : ℝ) (N : ℕ+) {ℓ : ℝ} (hℓ : 0 < ℓ) (x : ℝ) :
    gradW1 s a N ℓ (((N : ℕ) : ℝ) * x) = gradWeightOne s a (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ (x / ℓ) := by
  have hN : (0 : ℝ) < ((N : ℕ) : ℝ) := by exact_mod_cast N.pos
  unfold gradW1
  rw [show ((N : ℕ) : ℝ) / (((N : ℕ) : ℝ) * ℓ) = ℓ⁻¹ by field_simp,
    show ((N : ℕ) : ℝ) * x / (((N : ℕ) : ℝ) * ℓ) = x / ℓ by field_simp]

/-- The logarithmic factor is absorbed into a power: for `K ≥ 1` and `ε > 0`,
`1 + log K ≤ (1 + 1/ε) K^ε`. -/
lemma gapLog_le_rpow {K ε : ℝ} (hK : 1 ≤ K) (hε : 0 < ε) :
    1 + Real.log K ≤ (1 + 1 / ε) * K ^ ε := by
  have h1 := Real.log_le_rpow_div (by linarith : (0 : ℝ) ≤ K) hε
  have h2 : 1 ≤ K ^ ε := Real.one_le_rpow hK hε.le
  have h3 : K ^ ε / ε = 1 / ε * K ^ ε := by ring
  rw [add_mul, one_mul]
  linarith

/-! ## The residues of the window -/

/-- The residue map `e ↦ e mod N` is injective on the window. -/
lemma gapRes_injOn {ℓ γ : ℝ} {N : ℕ+} :
    Set.InjOn (fun e : ℤ => e % ((N : ℕ) : ℤ)) (gradLabels N ℓ γ : Set ℤ) := by
  intro e he e' he' h
  have h1 : (e - 0) % ((N : ℕ) : ℤ) = (e' - 0) % ((N : ℕ) : ℤ) := by simpa using h
  exact emod_inj_of_abs_sub_lt h1 (by
    have := gradLabels_abs_sub_lt he he'
    rwa [abs_sub_comm] at this)

/-- A residue not met by any edge of the window carries no gap representative: every positive path
between labels of the window uses only edges of the window. -/
lemma gradWgap_eq_zero_of_not_mem {s γ ℓ : ℝ} {N : ℕ+} (ψ : ℝ → ℝ) (X : Fin (N : ℕ) → ℝ)
    {r : ℤ} (hr : ∀ e ∈ gradLabels N ℓ γ, e % ((N : ℕ) : ℤ) ≠ r) :
    gradWgap s ψ N ℓ γ X r = 0 := by
  unfold gradWgap
  refine mul_eq_zero.mpr (Or.inr (Finset.sum_eq_zero fun l hl => Finset.sum_eq_zero fun m hm => ?_))
  obtain ⟨_, hmI⟩ := Finset.mem_erase.mp hm
  split_ifs with hcond
  swap
  · rfl
  obtain ⟨hk, t, htk, ht⟩ := hcond
  exfalso
  by_cases hP : GradPartial N ℓ γ
  · -- partial window: the edge `l + t` lies in the window
    have hk' : gradPathIncr N ℓ γ l m = m - l := by
      unfold gradPathIncr
      simp only [hP, ↓reduceIte]
    rw [hk'] at htk
    rw [mem_gradLabels_partial hP] at hl hmI
    apply hr (l + t) ((mem_gradLabels_partial hP _).2 ⟨by omega, by omega⟩)
    exact ht
  · -- full window: the reduced edge lies in `[0, N)`
    have hN : (0 : ℤ) < ((N : ℕ) : ℤ) := by exact_mod_cast N.pos
    apply hr ((l + t) % ((N : ℕ) : ℤ)) ((mem_gradLabels_full hP _).2
      ⟨Int.emod_nonneg _ hN.ne', Int.emod_lt_of_pos _ hN⟩)
    rw [Int.emod_emod]
    exact ht

/-! ## The squared bound -/

/-- The squared bound on the window, before the particle sum is evaluated: with the pointwise bound
of `gapWgap_abs_le`, the Schur test on the decay kernel `(1 + d(i,j))^{-(1+s/2)}` gives
`∑_{e ∈ I} |W^gap_{e mod N}|² ≤ (4 C_G C_0 C_d K^{(s+3)ε} C_q)² C_dec² R`, where `R` bounds the
squared weights `∑_{j ∈ I} w_1(x_j/ℓ)²`. -/
lemma gapSquare_le {s a γ ε ℓ C0 Cd Cdec Rp : ℝ} {N : ℕ+} {X : Fin (N : ℕ) → ℝ} {ψ : ℝ → ℝ}
    (hs0 : 0 < s) (hs1 : s < 1) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1) (hK : 1 ≤ ((N : ℕ) : ℝ) * ℓ) (hε : 0 < ε)
    (hεs : ε < (1 - s / 2) / 8) (hC0 : 0 ≤ C0) (hCd : 0 ≤ Cd) (hCdec : 0 ≤ Cdec)
    (hkd : ∀ u : ℝ, 0 < u → u ≤ 3 / 4 → |iteratedDeriv 2 (gradKernelH s) u| ≤ Cd * u ^ (-s - 2))
    (hψ : ContDiff ℝ ∞ ψ) (hper : Function.Periodic ψ ℓ⁻¹)
    (hbd : ∀ t, |deriv ψ t| ≤ C0 * gradWeightOne s a (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ t)
    (hX : gradEvent s γ ε N ℓ X)
    (hdec : ∀ i ∈ gradLabels N ℓ γ,
      ∑ j ∈ gradLabels N ℓ γ, (1 + (gradLabelDist N i j : ℝ)) ^ (-(1 + s / 2)) ≤ Cdec)
    (hRp : ∑ j ∈ gradLabels N ℓ γ,
      (gradWeightOne s a (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ (gradLift N X j / ℓ)) ^ 2 ≤ Rp) :
    ∑ e ∈ gradLabels N ℓ γ, (gradWgap s ψ N ℓ γ X (e % ((N : ℕ) : ℤ))) ^ 2
      ≤ (4 * (gradZConst a s * C0 * Cd * (((N : ℕ) : ℝ) * ℓ) ^ ((s + 3) * ε)
          * (2 ^ (1 + s / 2) * (1 + 1 / (1 + s / 2))))) ^ 2 * Cdec ^ 2 * Rp := by
  set I := gradLabels N ℓ γ with hI
  set w : ℤ → ℝ := fun j => gradWeightOne s a (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ (gradLift N X j / ℓ)
    with hw
  set A : ℝ := 4 * (gradZConst a s * C0 * Cd * (((N : ℕ) : ℝ) * ℓ) ^ ((s + 3) * ε)
          * (2 ^ (1 + s / 2) * (1 + 1 / (1 + s / 2)))) with hA
  set p : ℤ → ℤ → ℝ := fun i j => (1 + (gradLabelDist N i j : ℝ)) ^ (-(1 + s / 2)) with hp
  -- the pointwise bound in the Schur form `∑_j p_{ej} w_j`
  have hSe : ∀ e ∈ I, ∑ j ∈ I, w j / (1 + (gradLabelDist N e j : ℝ)) ^ (1 + s / 2)
      = ∑ j ∈ I, p e j * w j := by
    intro e he
    refine Finset.sum_congr rfl fun j hj => ?_
    have hd0 := gapLabelDist_nonneg he hj
    show w j / (1 + (gradLabelDist N e j : ℝ)) ^ (1 + s / 2)
      = (1 + (gradLabelDist N e j : ℝ)) ^ (-(1 + s / 2)) * w j
    rw [Real.rpow_neg (by linarith), div_eq_mul_inv, mul_comm]
  have hW : ∀ e ∈ I, (gradWgap s ψ N ℓ γ X (e % ((N : ℕ) : ℤ))) ^ 2 ≤ (A * ∑ j ∈ I, p e j * w j) ^ 2 := by
    intro e he
    have h := gapWgap_abs_le hs0 hs1 ha0 ha1 hℓ hℓ1 hK hε hεs hC0 hCd hkd hψ hper hbd hX he
    have h' : |gradWgap s ψ N ℓ γ X (e % ((N : ℕ) : ℤ))| ≤ A * ∑ j ∈ I, p e j * w j := by
      rw [← hSe e he]
      exact h
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h' 2
  have hpnn : ∀ i ∈ I, ∀ j ∈ I, 0 ≤ p i j := by
    intro i hi j hj
    have := gapLabelDist_nonneg hi hj
    show 0 ≤ (1 + (gradLabelDist N i j : ℝ)) ^ (-(1 + s / 2))
    exact Real.rpow_nonneg (by linarith) _
  have hcol : ∀ j ∈ I, ∑ i ∈ I, p i j ≤ Cdec := by
    intro j hj
    have hsymm : ∑ i ∈ I, p i j = ∑ i ∈ I, (1 + (gradLabelDist N j i : ℝ)) ^ (-(1 + s / 2)) :=
      Finset.sum_congr rfl fun i _ => by
        show (1 + (gradLabelDist N i j : ℝ)) ^ (-(1 + s / 2)) = _
        rw [gradLabelDist_comm N i j]
    rw [hsymm]
    exact hdec j hj
  have hSchur := gapSchur I p w hCdec hpnn (fun i hi => hdec i hi) hcol
  calc ∑ e ∈ I, (gradWgap s ψ N ℓ γ X (e % ((N : ℕ) : ℤ))) ^ 2
      ≤ ∑ e ∈ I, (A * ∑ j ∈ I, p e j * w j) ^ 2 := Finset.sum_le_sum hW
    _ = A ^ 2 * ∑ e ∈ I, (∑ j ∈ I, p e j * w j) ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun e _ => ?_
        ring
    _ ≤ A ^ 2 * (Cdec ^ 2 * ∑ j ∈ I, (w j) ^ 2) :=
        mul_le_mul_of_nonneg_left hSchur (sq_nonneg _)
    _ ≤ A ^ 2 * (Cdec ^ 2 * Rp) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hRp (sq_nonneg _)) (sq_nonneg _)
    _ = (4 * (gradZConst a s * C0 * Cd * (((N : ℕ) : ℝ) * ℓ) ^ ((s + 3) * ε)
          * (2 ^ (1 + s / 2) * (1 + 1 / (1 + s / 2))))) ^ 2 * Cdec ^ 2 * Rp := by
        rw [hA]
        ring


/-- The squared sum over the residues `Ico 0 N` equals the sum over the window labels, since the
gap representative vanishes on the residues that no edge of the window reaches. -/
lemma gapSum_Ico_eq {s γ ℓ : ℝ} {N : ℕ+} (ψ : ℝ → ℝ) (X : Fin (N : ℕ) → ℝ) :
    ∑ e ∈ Finset.Ico (0 : ℤ) N, (gradWgap s ψ N ℓ γ X e) ^ 2
      = ∑ e ∈ gradLabels N ℓ γ, (gradWgap s ψ N ℓ γ X (e % ((N : ℕ) : ℤ))) ^ 2 := by
  have hN : (0 : ℤ) < ((N : ℕ) : ℤ) := by exact_mod_cast N.pos
  have hsub : (gradLabels N ℓ γ).image (fun e : ℤ => e % ((N : ℕ) : ℤ)) ⊆ Finset.Ico (0 : ℤ) N := by
    intro r hr
    obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hr
    exact Finset.mem_Ico.mpr ⟨Int.emod_nonneg _ hN.ne', Int.emod_lt_of_pos _ hN⟩
  rw [← Finset.sum_image (f := fun r : ℤ => (gradWgap s ψ N ℓ γ X r) ^ 2) gapRes_injOn]
  refine (Finset.sum_subset hsub fun r _ hr => ?_).symm
  rw [gradWgap_eq_zero_of_not_mem ψ X (fun e he h => hr (Finset.mem_image.mpr ⟨e, he, h⟩))]
  ring

/-! ## The lemma -/

/-- The gap part of Lemma 5.7, complete. The identity `W·U = -∑_i W^gap_i N(u_{i+1} - u_i)`
and `∑_i W_i = 0` hold on the configuration space. On the event `𝒜_{ε,γ}` the representative
satisfies the pointwise bound and the squared bound, with `κ = κ(s, α)` and `C = C(s, α, ε)`.

The statement generalizes the paper in two ways: the parameter `γ` ranges over `γ > 1`, and the
hypotheses `|ψ''| ≤ C_0 w_2` and the partial-window vanishing of `ψ` are dropped, since the gap
estimate uses only the first derivative envelope. -/
theorem gradient_splitting_gap {s α γ : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hα0 : s - 1 ≤ α)
    (hα1 : α < s / 2) (hγ : 1 < γ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ ε : ℝ, 0 < ε → ε < min (1 / 8) ((1 - s / 2) / 8) →
      ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (ℓ C₀ : ℝ) (ψ : ℝ → ℝ) (X : Fin (N : ℕ) → ℝ),
        2 ≤ (N : ℕ) → 0 < ℓ → ℓ ≤ 1 → 1 ≤ ((N : ℕ) : ℝ) * ℓ → 0 ≤ C₀ →
        ContDiff ℝ ∞ ψ → Function.Periodic ψ ℓ⁻¹ →
        (∀ t : ℝ, |deriv ψ t| ≤ C₀ * gradWeightOne s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ t) →
        X ∈ orderedDomain N → gradEvent s γ ε N ℓ X →
        (∀ U : Fin (N : ℕ) → ℝ,
          ∑ k : Fin (N : ℕ), gradWfield s ψ N ℓ γ X k * U k
            = -∑ e ∈ Finset.Ico (0 : ℤ) N, gradWgap s ψ N ℓ γ X e * (N : ℝ) * gradEdgeDiff N U e) ∧
        ∑ k : Fin (N : ℕ), gradWfield s ψ N ℓ γ X k = 0 ∧
        (∀ i ∈ gradLabels N ℓ γ, |gradWgap s ψ N ℓ γ X (i % ((N : ℕ) : ℤ))| ≤
          C * C₀ * (((N : ℕ) : ℝ) * ℓ) ^ (κ * ε) * ∑ j ∈ gradLabels N ℓ γ,
            gradWeightOne s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ (gradLift N X j / ℓ)
              / (1 + (gradLabelDist N i j : ℝ)) ^ (1 + s / 2)) ∧
        ∑ e ∈ Finset.Ico (0 : ℤ) N, (gradWgap s ψ N ℓ γ X e) ^ 2
          ≤ C * C₀ ^ 2 * (((N : ℕ) : ℝ) * ℓ) ^ (κ * ε)
            * ((((N : ℕ) : ℝ) * ℓ) + (((N : ℕ) : ℝ) * ℓ) ^ (2 * (1 - s + α))) := by
  have ha0 : 0 ≤ 1 - s + α := by linarith
  have ha1 : 1 - s + α < 1 := by linarith
  have ha : 1 - s + α < 1 - s / 2 := by linarith
  obtain ⟨κp, hκp, hpart⟩ :=
    gradient_splitting_particle_sum_sq (s := s) (a := 1 - s + α) hs0 hs1 ha0 ha
  obtain ⟨Cdec, hCdec, hdec⟩ := sum_labels_decay_le (s := s) hs0
  obtain ⟨Cd, hCd, hkd⟩ := gapKernel_second_le hs0 hs1
  refine ⟨2 * (s + 3) + κp + 1, by linarith, fun ε hε hεs => ?_⟩
  have hεs' : ε < (1 - s / 2) / 8 := lt_of_lt_of_le hεs (min_le_right _ _)
  obtain ⟨Cp, hCp, hpart'⟩ := hpart ε hε hεs'
  have hG0 : 0 ≤ gradZConst (1 - s + α) s := gradZConst_nonneg ha1 hs1
  have h2 : 0 < 1 + s / 2 := by linarith
  have hCq0 : 0 ≤ 2 ^ (1 + s / 2) * (1 + 1 / (1 + s / 2)) :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) (add_nonneg zero_le_one (by positivity))
  have hε1 : 0 ≤ 1 + 1 / ε := add_nonneg zero_le_one (div_nonneg zero_le_one hε.le)
  obtain ⟨G, hG⟩ : ∃ G : ℝ, gradZConst (1 - s + α) s = G := ⟨_, rfl⟩
  obtain ⟨Cq, hCq⟩ : ∃ Cq : ℝ, 2 ^ (1 + s / 2) * (1 + 1 / (1 + s / 2)) = Cq := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ, 4 * (G * Cd * Cq) = B := ⟨_, rfl⟩
  obtain ⟨Csq, hCsq⟩ : ∃ Csq : ℝ, B ^ 2 * Cdec ^ 2 * Cp * (1 + 1 / ε) = Csq := ⟨_, rfl⟩
  have hG0' : 0 ≤ G := hG ▸ hG0
  have hCq0' : 0 ≤ Cq := hCq ▸ hCq0
  have hB0 : 0 ≤ B := hB ▸ mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg hG0' hCd) hCq0')
  have hCsq0 : 0 ≤ Csq := hCsq ▸ mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    hCp.le) hε1
  refine ⟨B + Csq + 1, by linarith, ?_⟩
  intro N ℓ C₀ ψ X hN2 hℓ hℓ1 hK hC0 hψ hper hbd hXD hEv
  have hK0 : 0 < ((N : ℕ) : ℝ) * ℓ := by linarith
  have hκ_ge : (s + 3) * ε ≤ (2 * (s + 3) + κp + 1) * ε :=
    mul_le_mul_of_nonneg_right (by linarith) hε.le
  refine ⟨gradient_splitting_gap_identity (γ := γ) hs0 hs1 hper hXD,
    gradWfield_sum_eq_zero (γ := γ) hs0 hs1 hper hXD, ?_, ?_⟩
  · -- the pointwise bound
    intro i hi
    have hS0 : 0 ≤ ∑ j ∈ gradLabels N ℓ γ,
        gradWeightOne s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ (gradLift N X j / ℓ)
          / (1 + (gradLabelDist N i j : ℝ)) ^ (1 + s / 2) :=
      Finset.sum_nonneg fun j hj => div_nonneg (gradWeightOne_nonneg hK)
        (Real.rpow_nonneg (by linarith [gapLabelDist_nonneg hi hj]) _)
    have h := gapWgap_abs_le hs0 hs1 ha0 ha1 hℓ hℓ1 hK hε hεs' hC0 hCd hkd hψ hper hbd hEv hi
    rw [hG, hCq] at h
    have hKle : (((N : ℕ) : ℝ) * ℓ) ^ ((s + 3) * ε)
        ≤ (((N : ℕ) : ℝ) * ℓ) ^ ((2 * (s + 3) + κp + 1) * ε) :=
      Real.rpow_le_rpow_of_exponent_le hK hκ_ge
    refine h.trans ?_
    calc 4 * (G * C₀ * Cd * (((N : ℕ) : ℝ) * ℓ) ^ ((s + 3) * ε) * Cq)
          * ∑ j ∈ gradLabels N ℓ γ,
            gradWeightOne s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ (gradLift N X j / ℓ)
              / (1 + (gradLabelDist N i j : ℝ)) ^ (1 + s / 2)
        = B * C₀ * (((N : ℕ) : ℝ) * ℓ) ^ ((s + 3) * ε)
          * ∑ j ∈ gradLabels N ℓ γ,
            gradWeightOne s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ (gradLift N X j / ℓ)
              / (1 + (gradLabelDist N i j : ℝ)) ^ (1 + s / 2) := by
          rw [← hB]
          ring
      _ ≤ (B + Csq + 1) * C₀ * (((N : ℕ) : ℝ) * ℓ) ^ ((2 * (s + 3) + κp + 1) * ε)
          * ∑ j ∈ gradLabels N ℓ γ,
            gradWeightOne s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ (gradLift N X j / ℓ)
              / (1 + (gradLabelDist N i j : ℝ)) ^ (1 + s / 2) := by
          apply mul_le_mul_of_nonneg_right _ hS0
          apply mul_le_mul (mul_le_mul_of_nonneg_right (by linarith) hC0) hKle
            (Real.rpow_nonneg hK0.le _) (mul_nonneg (by linarith) hC0)
  · -- the squared bound
    have hRp := hpart' γ N ℓ X hγ hN2 hℓ hℓ1 hK hEv
    simp only [gapW1_eq_micro s (1 - s + α) N hℓ] at hRp
    have hsq := gapSquare_le (ℓ := ℓ) (γ := γ) hs0 hs1 ha0 ha1 hℓ hℓ1 hK hε hεs' hC0 hCd hCdec.le
      hkd hψ hper hbd hEv (fun i hi => hdec N ℓ γ i hN2 hi) hRp
    rw [hG, hCq] at hsq
    rw [gapSum_Ico_eq ψ X]
    have hlog := gapLog_le_rpow hK hε
    have hK1 : 0 ≤ ((N : ℕ) : ℝ) * ℓ := hK0.le
    have hrp : ((((N : ℕ) : ℝ) * ℓ) ^ ((s + 3) * ε)) ^ 2 * (((N : ℕ) : ℝ) * ℓ) ^ (κp * ε)
        * (((N : ℕ) : ℝ) * ℓ) ^ ε = (((N : ℕ) : ℝ) * ℓ) ^ ((2 * (s + 3) + κp + 1) * ε) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hK0.le, ← Real.rpow_add hK0,
        ← Real.rpow_add hK0]
      congr 1
      push_cast
      ring
    have hKpos : 0 ≤ (((N : ℕ) : ℝ) * ℓ) ^ (κp * ε) := Real.rpow_nonneg hK1 _
    have hKa : 0 ≤ ((N : ℕ) : ℝ) * ℓ + (((N : ℕ) : ℝ) * ℓ) ^ (2 * (1 - s + α)) :=
      add_nonneg hK1 (Real.rpow_nonneg hK1 _)
    calc ∑ e ∈ gradLabels N ℓ γ, (gradWgap s ψ N ℓ γ X (e % ((N : ℕ) : ℤ))) ^ 2
        ≤ (4 * (G * C₀ * Cd * (((N : ℕ) : ℝ) * ℓ) ^ ((s + 3) * ε) * Cq)) ^ 2 * Cdec ^ 2
          * (Cp * (((N : ℕ) : ℝ) * ℓ) ^ (κp * ε)
              * ((((N : ℕ) : ℝ) * ℓ) + (((N : ℕ) : ℝ) * ℓ) ^ (2 * (1 - s + α)))
              * ((1 + 1 / ε) * (((N : ℕ) : ℝ) * ℓ) ^ ε)) := by
          refine hsq.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
          exact mul_le_mul_of_nonneg_left hlog (mul_nonneg (mul_nonneg hCp.le hKpos) hKa)
      _ = Csq * C₀ ^ 2 * ((((N : ℕ) : ℝ) * ℓ) ^ ((s + 3) * ε)) ^ 2
            * (((N : ℕ) : ℝ) * ℓ) ^ (κp * ε) * (((N : ℕ) : ℝ) * ℓ) ^ ε
            * ((((N : ℕ) : ℝ) * ℓ) + (((N : ℕ) : ℝ) * ℓ) ^ (2 * (1 - s + α))) := by
          rw [← hCsq, ← hB]
          ring
      _ = Csq * C₀ ^ 2 * (((N : ℕ) : ℝ) * ℓ) ^ ((2 * (s + 3) + κp + 1) * ε)
            * ((((N : ℕ) : ℝ) * ℓ) + (((N : ℕ) : ℝ) * ℓ) ^ (2 * (1 - s + α))) := by
          rw [← hrp]
          ring
      _ ≤ (B + Csq + 1) * C₀ ^ 2 * (((N : ℕ) : ℝ) * ℓ) ^ ((2 * (s + 3) + κp + 1) * ε)
            * ((((N : ℕ) : ℝ) * ℓ) + (((N : ℕ) : ℝ) * ℓ) ^ (2 * (1 - s + α))) := by
          apply mul_le_mul_of_nonneg_right _ hKa
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hK1 _)
          apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
          linarith

end

end Riesz1
