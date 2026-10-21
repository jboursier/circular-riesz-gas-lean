/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.GradientSplittingIdentityPair

/-!
# Lattice facts for the localized loop

The window labels are integers, the lifts `x_j = gradLift N X j` satisfy `x_{j+Nc} = x_j + c`, and the path
increment `k_ij` satisfies `i + k_ij ≡ j (mod N)`. Hence each pair term of `H_γ` is the kernel
`P(x_i, x_j)`, and for `X` in the ordered domain the points of distinct labels never differ by an integer.
-/

@[expose] public section

open Set MeasureTheory Filter Topology intervalIntegral
open scoped ContDiff

namespace Riesz1

noncomputable section

/-- Shifting a label by a multiple of `N` shifts the lift by the same integer. -/
lemma gradLift_add_mul (N : ℕ+) (X : Fin (N : ℕ) → ℝ) (j c : ℤ) :
    gradLift N X (j + (N : ℤ) * c) = gradLift N X j + c := by
  unfold gradLift
  have hidx : gradIndex N (j + (N : ℤ) * c) = gradIndex N j := by
    unfold gradIndex
    simp only [Int.add_mul_emod_self_left]
  rw [hidx]
  have hdiv : (j + (N : ℤ) * c) / (N : ℤ) = j / (N : ℤ) + c := by
    rw [Int.add_mul_ediv_left j c (by exact_mod_cast N.ne_zero)]
  rw [hdiv]
  push_cast
  ring

/-- The path increment of a pair of labels reaches the label `j` modulo `N`. -/
lemma gradPathIncr_modEq (N : ℕ+) (ℓ γ : ℝ) (i j : ℤ) :
    ∃ c : ℤ, i + gradPathIncr N ℓ γ i j = j + (N : ℤ) * c := by
  have hNpos : (0 : ℤ) < (N : ℤ) := by exact_mod_cast N.pos
  by_cases hP : GradPartial N ℓ γ
  · refine ⟨0, ?_⟩
    unfold gradPathIncr
    rw [ite_eq_left hP]
    ring
  · unfold gradPathIncr
    rw [ite_eq_right hP]
    have hdq := Int.emod_add_mul_ediv (j - i) (N : ℤ)
    set d := (j - i) % (N : ℤ) with hd
    set q := (j - i) / (N : ℤ) with hq
    by_cases h1 : 2 * d < (N : ℤ)
    · rw [ite_eq_left h1]
      exact ⟨-q, by linarith⟩
    · rw [ite_eq_right h1]
      by_cases h2 : (N : ℤ) < 2 * d
      · rw [ite_eq_left h2]
        exact ⟨-q - 1, by linarith⟩
      · rw [ite_eq_right h2]
        have hN : 2 * d = (N : ℤ) := by omega
        have hN2 : (N : ℤ) / 2 = d := by omega
        by_cases h3 : i % (N : ℤ) < j % (N : ℤ)
        · rw [ite_eq_left h3, hN2]
          exact ⟨-q, by linarith⟩
        · rw [ite_eq_right h3]
          exact ⟨-q - 1, by linarith⟩

/-- The pair term of `H_γ` is the pair kernel at the two lifts: `Z(x_i, x_i + r_ij) h(r_ij) = P(x_i, x_j)`. -/
lemma gradZ_pair_eq {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) {ℓ : ℝ} (hℓ : ℓ ≠ 0)
    (hp : Function.Periodic ψ (1 / ℓ)) (s : ℝ) (N : ℕ+) (γ : ℝ) (X : Fin (N : ℕ) → ℝ) (i j : ℤ) :
    gradZ ψ ℓ (gradLift N X i) (gradLift N X i + gradSep N ℓ γ X i j)
        * gradKernelH s (gradSep N ℓ γ X i j)
      = gradPairKernel s ψ ℓ (gradLift N X i) (gradLift N X j) := by
  obtain ⟨c, hc⟩ := gradPathIncr_modEq N ℓ γ i j
  have h1 := gradZ_mul_kernelH hψ hℓ s (gradLift N X i)
    (gradLift N X i + gradSep N ℓ γ X i j)
  rw [add_sub_cancel_left] at h1
  have hlift : gradLift N X i + gradSep N ℓ γ X i j = gradLift N X j + c := by
    unfold gradSep
    rw [show gradLift N X (i + gradPathIncr N ℓ γ i j) = gradLift N X j + c by
      rw [hc, gradLift_add_mul]]
    ring
  have hsep : gradSep N ℓ γ X i j = gradLift N X j + c - gradLift N X i := by linarith
  rw [h1, hsep, ← gradPairKernel_add_int_right hp s (gradLift N X i) (gradLift N X j) c]
  rw [show gradLift N X i + (gradLift N X j + (c : ℝ) - gradLift N X i) = gradLift N X j + c by ring]
  rfl

/-- The residues of two distinct labels of the window are distinct. -/
lemma gradIndex_ne_of_mem_labels {N : ℕ+} {ℓ γ : ℝ} (hℓ : 0 ≤ ℓ) {i j : ℤ} (hi : i ∈ gradLabels N ℓ γ)
    (hj : j ∈ gradLabels N ℓ γ) (hij : i ≠ j) : gradIndex N i ≠ gradIndex N j := by
  intro heq
  have hmod : i % (N : ℤ) = j % (N : ℤ) := by
    have h := congrArg Fin.val heq
    unfold gradIndex at h
    simp only at h
    have h1 : 0 ≤ i % (N : ℤ) := Int.emod_nonneg _ (by exact_mod_cast N.ne_zero)
    have h2 : 0 ≤ j % (N : ℤ) := Int.emod_nonneg _ (by exact_mod_cast N.ne_zero)
    omega
  have hdvd : (N : ℤ) ∣ i - j := Int.ModEq.dvd (show j ≡ i [ZMOD (N : ℤ)] from hmod.symm)
  unfold gradLabels at hi hj
  have hNpos : (0 : ℤ) < (N : ℤ) := by exact_mod_cast N.pos
  split_ifs at hi hj with hP
  · rw [Finset.mem_Icc] at hi hj
    have hM : 0 ≤ gradM N ℓ γ := by
      unfold gradM
      exact Real.rpow_nonneg (mul_nonneg (by positivity) hℓ) _
    have hn8 : (⌊gradM N ℓ γ⌋ : ℝ) < (N : ℝ) / 8 := by
      have h1 : (⌊gradM N ℓ γ⌋ : ℝ) ≤ gradM N ℓ γ := Int.floor_le _
      linarith [hP]
    have hn8' : (⌊gradM N ℓ γ⌋ : ℤ) * 8 < (N : ℤ) := by
      have : ((⌊gradM N ℓ γ⌋ * 8 : ℤ) : ℝ) < ((N : ℤ) : ℝ) := by
        push_cast
        linarith
      exact_mod_cast this
    have hdiff : |i - j| < (N : ℤ) := by
      rw [abs_lt]
      constructor <;> omega
    obtain ⟨m, hm⟩ := hdvd
    have hm0 : m = 0 := by
      rcases (lt_trichotomy m 0) with h | h | h
      · have : (N : ℤ) * m ≤ -(N : ℤ) := by nlinarith
        rw [abs_lt] at hdiff
        omega
      · exact h
      · have : (N : ℤ) * m ≥ (N : ℤ) := by nlinarith
        rw [abs_lt] at hdiff
        omega
    rw [hm0, mul_zero] at hm
    exact hij (by omega)
  · rw [Finset.mem_Ico] at hi hj
    have hi' : i % (N : ℤ) = i := Int.emod_eq_of_lt hi.1 hi.2
    have hj' : j % (N : ℤ) = j := Int.emod_eq_of_lt hj.1 hj.2
    exact hij (by omega)

/-- On the ordered domain, two lifts of distinct labels of the window never differ by an integer. -/
lemma gradLift_sub_not_int {N : ℕ+} {ℓ γ : ℝ} (hℓ : 0 ≤ ℓ) {X : Fin (N : ℕ) → ℝ}
    (hX : X ∈ orderedDomain N) {i j : ℤ} (hi : i ∈ gradLabels N ℓ γ) (hj : j ∈ gradLabels N ℓ γ)
    (hij : i ≠ j) (n : ℤ) : gradLift N X j - gradLift N X i ≠ n := by
  intro h
  unfold gradLift at h
  have hne : gradIndex N j ≠ gradIndex N i :=
    fun h' => gradIndex_ne_of_mem_labels hℓ hi hj hij h'.symm
  obtain ⟨hmono, h0, h1, hall⟩ := hX
  have hbound : ∀ p q : Fin (N : ℕ), |X p - X q| < 1 := by
    intro p q
    have hlo : ∀ r : Fin (N : ℕ), X ⟨0, N.pos⟩ ≤ X r := fun r =>
      hmono.monotone (Fin.mk_le_of_le_val (Nat.zero_le _))
    rw [abs_lt]
    have := hlo p
    have := hlo q
    have := hall p
    have := hall q
    constructor <;> linarith
  have hm : X (gradIndex N j) - X (gradIndex N i) = ((n - (j / (N : ℤ) - i / (N : ℤ)) : ℤ) : ℝ) := by
    push_cast
    linarith
  have hb := hbound (gradIndex N j) (gradIndex N i)
  rw [hm] at hb
  have hz : n - (j / (N : ℤ) - i / (N : ℤ)) = 0 := by
    have hlt : |((n - (j / (N : ℤ) - i / (N : ℤ)) : ℤ) : ℝ)| < 1 := hb
    rw [← Int.cast_abs] at hlt
    have : |n - (j / (N : ℤ) - i / (N : ℤ))| < 1 := by exact_mod_cast hlt
    have hz' : |n - (j / (N : ℤ) - i / (N : ℤ))| = 0 := by
      have : |n - (j / (N : ℤ) - i / (N : ℤ))| ≤ 0 := by
        rw [abs_lt] at this
        rw [abs_le]
        constructor <;> omega
      exact le_antisymm this (abs_nonneg _)
    exact abs_eq_zero.1 hz'
  have hXeq : X (gradIndex N j) = X (gradIndex N i) := by
    have : X (gradIndex N j) - X (gradIndex N i) = 0 := by
      rw [hm, hz]
      simp
    linarith
  exact hne (hmono.injective hXeq)

/-- The lift along a coordinate direction: `x_i(X + t e_k) = x_i(X) + t` if `i` lies over `k`. -/
lemma gradLift_add_smul_single (N : ℕ+) (X : Fin (N : ℕ) → ℝ) (k : Fin (N : ℕ)) (t : ℝ) (i : ℤ) :
    gradLift N (X + t • Pi.single k 1) i
      = gradLift N X i + t * (if gradIndex N i = k then 1 else 0) := by
  unfold gradLift
  simp only [Pi.add_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  split_ifs <;> ring

/-- The particle-particle part and the background part of `H_γ` in the lifts. -/
lemma gradLoop_eq_pairs_background {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) {ℓ : ℝ} (hℓ : ℓ ≠ 0)
    (hp : Function.Periodic ψ (1 / ℓ)) (s : ℝ) (N : ℕ+) (γ : ℝ) (X : Fin (N : ℕ) → ℝ) :
    gradLoop s ψ N ℓ γ X
      = (N : ℝ) ^ (-s) * ∑ i ∈ gradLabels N ℓ γ, ∑ j ∈ (gradLabels N ℓ γ).erase i,
          gradPairKernel s ψ ℓ (gradLift N X i) (gradLift N X j)
        - 2 * (N : ℝ) ^ (1 - s) * ∑ i ∈ gradLabels N ℓ γ,
          gradBackground s ψ N ℓ γ (gradLift N X i) := by
  unfold gradLoop
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact gradZ_pair_eq hψ hℓ hp s N γ X i j

/-- In a partial window `0 < t = M/N ≤ 1/2`. -/
lemma gradT_partial_bounds {N : ℕ+} {ℓ γ : ℝ} (hℓ : 0 < ℓ) (hpart : GradPartial N ℓ γ) :
    0 < gradT N ℓ γ ∧ gradT N ℓ γ ≤ 1 / 2 := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast N.pos
  have hM : 0 < gradM N ℓ γ := by
    unfold gradM
    exact Real.rpow_pos_of_pos (mul_pos hNpos hℓ) _
  have hlt : gradM N ℓ γ / (N : ℝ) < 1 / 8 := by
    rw [div_lt_iff₀ hNpos]
    linarith [hpart]
  rw [gradT, ite_eq_left hpart]
  exact ⟨div_pos hM hNpos, by linarith⟩

/-- The background integral in the partial window: `J(x) = BT(x) - Φ(x)`. -/
lemma gradBackground_partial_eq {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) {ℓ γ : ℝ} (hℓ0 : 0 < ℓ)
    (hp : Function.Periodic ψ (1 / ℓ)) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {N : ℕ+}
    (hpart : GradPartial N ℓ γ)
    (hsupp : ∀ y : ℝ, (∀ m : ℤ, gradT N ℓ γ / 4 ≤ |y - m|) → ψ (y / ℓ) = 0) (x : ℝ) :
    gradBackground s ψ N ℓ γ x
      = gradBTpart s ψ ℓ (gradT N ℓ γ) x - gradPhi s ψ ℓ x := by
  obtain ⟨ht, ht2⟩ := gradT_partial_bounds hℓ0 hpart
  have hlo : gradBLo N ℓ γ x = -gradT N ℓ γ := by
    unfold gradBLo
    rw [ite_eq_left hpart]
  have hhi : gradBHi N ℓ γ x = gradT N ℓ γ := by
    unfold gradBHi
    rw [ite_eq_left hpart]
  rw [gradBackground_eq_vframe s hψ N hℓ0.ne' x, hlo, hhi]
  exact gradBackground_partial_closed hψ hℓ0 hp hs0 hs1 ht ht2 hsupp x

/-- The background integral in the full window: `J(x) = -Φ(x)`. -/
lemma gradBackground_full_eq {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) {ℓ γ : ℝ} (hℓ0 : 0 < ℓ)
    (hp : Function.Periodic ψ (1 / ℓ)) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {N : ℕ+}
    (hfull : ¬ GradPartial N ℓ γ) (x : ℝ) :
    gradBackground s ψ N ℓ γ x = - gradPhi s ψ ℓ x := by
  have hlo : gradBLo N ℓ γ x - x = -1 / 2 := by
    unfold gradBLo
    rw [ite_eq_right hfull]
    ring
  have hhi : gradBHi N ℓ γ x - x = 1 / 2 := by
    unfold gradBHi
    rw [ite_eq_right hfull]
    ring
  rw [gradBackground_eq_vframe s hψ N hℓ0.ne' x, hlo, hhi]
  exact gradBackground_full_closed hψ hℓ0 hp hs0 hs1 x

/-- The derivative of the background integral `J(x)` in the lift `x`, in the form of the identity of
the two principal values of `V`. -/
noncomputable def gradJderiv (s : ℝ) (ψ : ℝ → ℝ) (N : ℕ+) (ℓ γ x : ℝ) : ℝ :=
  if GradPartial N ℓ γ then
    gradBTpartDeriv s ψ ℓ (gradT N ℓ γ) x - deriv (fun y => gradPhi s ψ ℓ y) x
  else -deriv (fun y => gradPhi s ψ ℓ y) x

/-- `Φ` is smooth and differentiable everywhere. -/
lemma gradPhi_contDiff {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) {ℓ : ℝ} (hℓ : ℓ ≠ 0) {s : ℝ}
    (hs0 : 0 < s) (hs1 : s < 1) : ContDiff ℝ ∞ (fun y => gradPhi s ψ ℓ y) :=
  contDiff_gradPhiFam hℓ hs0 hs1 ((contDiff_infty_iff_deriv.1 hψ).2)

/-- The background integral is smooth in the lift `x`, and its derivative is `gradJderiv`. -/
lemma gradBackground_hasDerivAt {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) {ℓ γ : ℝ} (hℓ0 : 0 < ℓ)
    (hp : Function.Periodic ψ (1 / ℓ)) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {N : ℕ+}
    (hsupp : GradPartial N ℓ γ → ∀ y : ℝ, (∀ m : ℤ, gradT N ℓ γ / 4 ≤ |y - m|) → ψ (y / ℓ) = 0)
    (x : ℝ) :
    HasDerivAt (fun y => gradBackground s ψ N ℓ γ y) (gradJderiv s ψ N ℓ γ x) x := by
  have hΦ : HasDerivAt (fun y => gradPhi s ψ ℓ y) (deriv (fun y => gradPhi s ψ ℓ y) x) x :=
    ((gradPhi_contDiff hψ hℓ0.ne' hs0 hs1).differentiable (by simp)) x |>.hasDerivAt
  by_cases hpart : GradPartial N ℓ γ
  · obtain ⟨ht, ht2⟩ := gradT_partial_bounds hℓ0 hpart
    have hfun : (fun y => gradBackground s ψ N ℓ γ y)
        = fun y => gradBTpart s ψ ℓ (gradT N ℓ γ) y - gradPhi s ψ ℓ y :=
      funext fun y => gradBackground_partial_eq hψ hℓ0 hp hs0 hs1 hpart (hsupp hpart) y
    rw [hfun]
    unfold gradJderiv
    rw [ite_eq_left hpart]
    exact (hasDerivAt_gradBTpart hψ hℓ0.ne' ht ht2 (hsupp hpart) hs0 hs1 x).sub hΦ
  · have hfun : (fun y => gradBackground s ψ N ℓ γ y) = fun y => -gradPhi s ψ ℓ y :=
      funext fun y => gradBackground_full_eq hψ hℓ0 hp hs0 hs1 hpart y
    rw [hfun]
    unfold gradJderiv
    rw [ite_eq_right hpart]
    exact hΦ.neg

/-- The background integral is smooth in the lift. -/
lemma gradBackground_contDiff {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) {ℓ γ : ℝ} (hℓ0 : 0 < ℓ)
    (hp : Function.Periodic ψ (1 / ℓ)) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {N : ℕ+}
    (hsupp : GradPartial N ℓ γ → ∀ y : ℝ, (∀ m : ℤ, gradT N ℓ γ / 4 ≤ |y - m|) → ψ (y / ℓ) = 0) :
    ContDiff ℝ ∞ (fun y => gradBackground s ψ N ℓ γ y) := by
  by_cases hpart : GradPartial N ℓ γ
  · obtain ⟨ht, ht2⟩ := gradT_partial_bounds hℓ0 hpart
    have hfun : (fun y => gradBackground s ψ N ℓ γ y)
        = fun y => gradBTpart s ψ ℓ (gradT N ℓ γ) y - gradPhi s ψ ℓ y :=
      funext fun y => gradBackground_partial_eq hψ hℓ0 hp hs0 hs1 hpart (hsupp hpart) y
    rw [hfun]
    exact (contDiff_iff_contDiffAt.2 fun x =>
      contDiffAt_gradBTpart hψ ht ht2 (hsupp hpart) hs0 hs1 x).sub (gradPhi_contDiff hψ hℓ0.ne' hs0 hs1)
  · have hfun : (fun y => gradBackground s ψ N ℓ γ y) = fun y => -gradPhi s ψ ℓ y :=
      funext fun y => gradBackground_full_eq hψ hℓ0 hp hs0 hs1 hpart y
    rw [hfun]
    exact (gradPhi_contDiff hψ hℓ0.ne' hs0 hs1).neg

/-- The two principal values of `V` in the `v`-frame have the difference `J'(x)`. -/
lemma gradPV_sub_eq_gradJderiv {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) {ℓ γ : ℝ} (hℓ0 : 0 < ℓ)
    (hp : Function.Periodic ψ (1 / ℓ)) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {N : ℕ+}
    (hsupp : GradPartial N ℓ γ → ∀ y : ℝ, (∀ m : ℤ, gradT N ℓ γ / 4 ≤ |y - m|) → ψ (y / ℓ) = 0)
    (x : ℝ) :
    gradPV N ℓ γ x (fun y => gradZx ψ ℓ x y * gradKernelH s (y - x))
      - gradPV N ℓ γ x (fun y => gradZ ψ ℓ x y * deriv (gradKernelH s) (y - x))
      = gradJderiv s ψ N ℓ γ x := by
  by_cases hpart : GradPartial N ℓ γ
  · obtain ⟨ht, ht2⟩ := gradT_partial_bounds hℓ0 hpart
    obtain ⟨LA, LB, hA, hB, hid⟩ :=
      gradV_identity_partial hψ hℓ0 hp hs0 hs1 ht ht2 (hsupp hpart) x
    have hlo : gradBLo N ℓ γ x - x = -gradT N ℓ γ - x := by
      unfold gradBLo
      rw [ite_eq_left hpart]
    have hhi : gradBHi N ℓ γ x - x = gradT N ℓ γ - x := by
      unfold gradBHi
      rw [ite_eq_left hpart]
    have hA' : Tendsto (fun δ : ℝ => ∫ v in (gradBLo N ℓ γ x - x)..(gradBHi N ℓ γ x - x),
        (gradAllowed δ).indicator (fun v => (fun y => gradZx ψ ℓ x y * gradKernelH s (y - x)) (x + v)) v)
        (𝓝[>] 0) (𝓝 LA) := by
      rw [hlo, hhi]
      simpa only [add_sub_cancel_left] using hA
    have hB' : Tendsto (fun δ : ℝ => ∫ v in (gradBLo N ℓ γ x - x)..(gradBHi N ℓ γ x - x),
        (gradAllowed δ).indicator
          (fun v => (fun y => gradZ ψ ℓ x y * deriv (gradKernelH s) (y - x)) (x + v)) v)
        (𝓝[>] 0) (𝓝 LB) := by
      rw [hlo, hhi]
      simpa only [add_sub_cancel_left] using hB
    have hJ : gradJderiv s ψ N ℓ γ x
        = gradBTpartDeriv s ψ ℓ (gradT N ℓ γ) x - deriv (fun y => gradPhi s ψ ℓ y) x := by
      unfold gradJderiv
      rw [ite_eq_left hpart]
    have eA : gradPV N ℓ γ x (fun y => gradZx ψ ℓ x y * gradKernelH s (y - x)) = LA :=
      gradPV_eq_of_tendsto (f := fun y => gradZx ψ ℓ x y * gradKernelH s (y - x)) N ℓ γ x hA'
    have eB : gradPV N ℓ γ x (fun y => gradZ ψ ℓ x y * deriv (gradKernelH s) (y - x)) = LB :=
      gradPV_eq_of_tendsto (f := fun y => gradZ ψ ℓ x y * deriv (gradKernelH s) (y - x)) N ℓ γ x hB'
    have h1 : gradPV N ℓ γ x (fun y => gradZx ψ ℓ x y * gradKernelH s (y - x))
          - gradPV N ℓ γ x (fun y => gradZ ψ ℓ x y * deriv (gradKernelH s) (y - x)) = LA - LB := by
      rw [eA, eB]
    exact h1.trans (hid.trans hJ.symm)
  · have hlo : gradBLo N ℓ γ x - x = -1 / 2 := by
      unfold gradBLo
      rw [ite_eq_right hpart]
      ring
    have hhi : gradBHi N ℓ γ x - x = 1 / 2 := by
      unfold gradBHi
      rw [ite_eq_right hpart]
      ring
    obtain ⟨LA, LB, hA, hB, hid⟩ := gradV_identity_full hψ hℓ0 hp hs0 hs1 x
    have hA' : Tendsto (fun δ : ℝ => ∫ v in (gradBLo N ℓ γ x - x)..(gradBHi N ℓ γ x - x),
        (gradAllowed δ).indicator (fun v => (fun y => gradZx ψ ℓ x y * gradKernelH s (y - x)) (x + v)) v)
        (𝓝[>] 0) (𝓝 LA) := by
      rw [hlo, hhi]
      simpa only [add_sub_cancel_left] using hA
    have hB' : Tendsto (fun δ : ℝ => ∫ v in (gradBLo N ℓ γ x - x)..(gradBHi N ℓ γ x - x),
        (gradAllowed δ).indicator
          (fun v => (fun y => gradZ ψ ℓ x y * deriv (gradKernelH s) (y - x)) (x + v)) v)
        (𝓝[>] 0) (𝓝 LB) := by
      rw [hlo, hhi]
      simpa only [add_sub_cancel_left] using hB
    have hJ : gradJderiv s ψ N ℓ γ x = -deriv (fun y => gradPhi s ψ ℓ y) x := by
      unfold gradJderiv
      rw [ite_eq_right hpart]
    have eA : gradPV N ℓ γ x (fun y => gradZx ψ ℓ x y * gradKernelH s (y - x)) = LA :=
      gradPV_eq_of_tendsto (f := fun y => gradZx ψ ℓ x y * gradKernelH s (y - x)) N ℓ γ x hA'
    have eB : gradPV N ℓ γ x (fun y => gradZ ψ ℓ x y * deriv (gradKernelH s) (y - x)) = LB :=
      gradPV_eq_of_tendsto (f := fun y => gradZ ψ ℓ x y * deriv (gradKernelH s) (y - x)) N ℓ γ x hB'
    have h1 : gradPV N ℓ γ x (fun y => gradZx ψ ℓ x y * gradKernelH s (y - x))
          - gradPV N ℓ γ x (fun y => gradZ ψ ℓ x y * deriv (gradKernelH s) (y - x)) = LA - LB := by
      rw [eA, eB]
    exact h1.trans (hid.trans hJ.symm)

/-- Swapping the two summation indices of a sum over ordered pairs of distinct labels. -/
lemma sum_erase_swap (S : Finset ℤ) (f : ℤ → ℤ → ℝ) :
    ∑ i ∈ S, ∑ j ∈ S.erase i, f j i = ∑ i ∈ S, ∑ j ∈ S.erase i, f i j := by
  have key : ∀ x y : ℤ, (x ∈ S ∧ y ∈ S.erase x) ↔ (x ∈ S.erase y ∧ y ∈ S) := by
    intro x y
    constructor
    · rintro ⟨hx, hy⟩
      have hxy : y ≠ x := (Finset.mem_erase.1 hy).1
      exact ⟨Finset.mem_erase.2 ⟨fun h => hxy h.symm |>.elim, hx⟩ |> fun _ =>
        Finset.mem_erase.2 ⟨fun h => hxy h.symm, hx⟩, (Finset.mem_erase.1 hy).2⟩
    · rintro ⟨hx, hy⟩
      have hxy : x ≠ y := (Finset.mem_erase.1 hx).1
      exact ⟨(Finset.mem_erase.1 hx).2, Finset.mem_erase.2 ⟨fun h => hxy h.symm, hy⟩⟩
  exact Finset.sum_comm' key

/-- The pair increment of two distinct labels is not an integer on the ordered domain. -/
lemma gradSep_add_not_int {N : ℕ+} {ℓ γ : ℝ} (hℓ : 0 ≤ ℓ) {X : Fin (N : ℕ) → ℝ}
    (hX : X ∈ orderedDomain N) {i j : ℤ} (hi : i ∈ gradLabels N ℓ γ) (hj : j ∈ gradLabels N ℓ γ)
    (hij : i ≠ j) (c : ℤ) (hc : gradLift N X i + gradSep N ℓ γ X i j = gradLift N X j + c) :
    ((gradLift N X i + gradSep N ℓ γ X i j - gradLift N X i : ℝ) : UnitAddCircle) ≠ 0 := by
  apply coe_ne_zero_of_forall_ne_int
  intro m hm
  apply gradLift_sub_not_int hℓ hX hi hj hij (m - c)
  push_cast
  linarith

/-- The `V`-and-`W` pieces of one label, in closed form: `V_i + W_i = 2N^{-s} ∑_j P1(x_i, x_j) - 2N^{1-s} J'(x_i)`. -/
lemma gradVlab_add_gradWlab_eq {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) {ℓ γ : ℝ} (hℓ0 : 0 < ℓ)
    (hp : Function.Periodic ψ (1 / ℓ)) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {N : ℕ+}
    (hsupp : GradPartial N ℓ γ → ∀ y : ℝ, (∀ m : ℤ, gradT N ℓ γ / 4 ≤ |y - m|) → ψ (y / ℓ) = 0)
    {X : Fin (N : ℕ) → ℝ} (hX : X ∈ orderedDomain N) {i : ℤ} (hi : i ∈ gradLabels N ℓ γ) :
    gradVlab s ψ N ℓ γ X i + gradWlab s ψ N ℓ γ X i
      = 2 * (N : ℝ) ^ (-s) * ∑ j ∈ (gradLabels N ℓ γ).erase i,
          gradPairP1 s ψ ℓ (gradLift N X i) (gradLift N X j)
        - 2 * (N : ℝ) ^ (1 - s) * gradJderiv s ψ N ℓ γ (gradLift N X i) := by
  have hPV := gradPV_sub_eq_gradJderiv hψ hℓ0 hp hs0 hs1 hsupp (gradLift N X i)
  have hterm : ∀ j ∈ (gradLabels N ℓ γ).erase i,
      gradZx ψ ℓ (gradLift N X i) (gradLift N X i + gradSep N ℓ γ X i j)
          * gradKernelH s (gradSep N ℓ γ X i j)
        - gradZ ψ ℓ (gradLift N X i) (gradLift N X i + gradSep N ℓ γ X i j)
          * deriv (gradKernelH s) (gradSep N ℓ γ X i j)
        = gradPairP1 s ψ ℓ (gradLift N X i) (gradLift N X j) := by
    intro j hj
    have hij : i ≠ j := fun h => (Finset.mem_erase.1 hj).1 h.symm
    have hjl : j ∈ gradLabels N ℓ γ := Finset.mem_of_mem_erase hj
    obtain ⟨c, hc⟩ := gradPathIncr_modEq N ℓ γ i j
    have hlift : gradLift N X i + gradSep N ℓ γ X i j = gradLift N X j + c := by
      unfold gradSep
      rw [show gradLift N X (i + gradPathIncr N ℓ γ i j) = gradLift N X j + c by
        rw [hc, gradLift_add_mul]]
      ring
    have hnint := gradSep_add_not_int hℓ0.le hX hi hjl hij c hlift
    have e := gradPairP1_eq hψ hℓ0.ne' hs0 hs1 (gradLift N X i)
      (gradLift N X i + gradSep N ℓ γ X i j) hnint
    rw [add_sub_cancel_left] at e
    have hP := gradPairP1_add_int_right hp s (gradLift N X i) (gradLift N X j) c
    rw [← hP, ← hlift, e]
  have hW : ∑ j ∈ (gradLabels N ℓ γ).erase i,
      gradZ ψ ℓ (gradLift N X i) (gradLift N X i + gradSep N ℓ γ X i j)
        * (deriv (gradKernelH s) (gradSep N ℓ γ X i j)
          - deriv (gradKernelH s) ((gradPathIncr N ℓ γ i j : ℝ) / N))
      = ∑ j ∈ (gradLabels N ℓ γ).erase i,
          gradZ ψ ℓ (gradLift N X i) (gradLift N X i + gradSep N ℓ γ X i j)
            * deriv (gradKernelH s) (gradSep N ℓ γ X i j)
        - ∑ j ∈ (gradLabels N ℓ γ).erase i,
          gradZ ψ ℓ (gradLift N X i) (gradLift N X i + gradSep N ℓ γ X i j)
            * deriv (gradKernelH s) ((gradPathIncr N ℓ γ i j : ℝ) / N) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hS : ∑ j ∈ (gradLabels N ℓ γ).erase i,
      gradZx ψ ℓ (gradLift N X i) (gradLift N X i + gradSep N ℓ γ X i j)
          * gradKernelH s (gradSep N ℓ γ X i j)
        - ∑ j ∈ (gradLabels N ℓ γ).erase i,
          gradZ ψ ℓ (gradLift N X i) (gradLift N X i + gradSep N ℓ γ X i j)
            * deriv (gradKernelH s) (gradSep N ℓ γ X i j)
      = ∑ j ∈ (gradLabels N ℓ γ).erase i,
          gradPairP1 s ψ ℓ (gradLift N X i) (gradLift N X j) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl hterm
  unfold gradVlab gradWlab
  rw [hW]
  linear_combination (2 * (N : ℝ) ^ (-s)) * hS - (2 * (N : ℝ) ^ (1 - s)) * hPV

/-- The two pair contributions of a coordinate direction combine into twice the first one. -/
lemma sum_pair_alpha_eq (S : Finset ℤ) (P1 P2 : ℤ → ℤ → ℝ) (α : ℤ → ℝ)
    (hP2 : ∀ i j, P2 i j = P1 j i) :
    ∑ i ∈ S, ∑ j ∈ S.erase i, (α i * P1 i j + α j * P2 i j)
      = 2 * ∑ i ∈ S, ∑ j ∈ S.erase i, α i * P1 i j := by
  simp only [Finset.sum_add_distrib]
  have h := sum_erase_swap S (fun i j => α i * P1 i j)
  have h2 : ∑ i ∈ S, ∑ j ∈ S.erase i, α j * P2 i j = ∑ i ∈ S, ∑ j ∈ S.erase i, α i * P1 i j := by
    simp only [hP2]
    exact h
  rw [h2]
  ring

/-- The directional derivative of `H_γ` along the coordinate direction `e_k`, at any configuration
where the lifts of distinct labels avoid integer differences. -/
lemma hasDerivAt_gradLoop_single {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) {ℓ γ : ℝ} (hℓ0 : 0 < ℓ)
    (hp : Function.Periodic ψ (1 / ℓ)) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {N : ℕ+}
    (hsupp : GradPartial N ℓ γ → ∀ y : ℝ, (∀ m : ℤ, gradT N ℓ γ / 4 ≤ |y - m|) → ψ (y / ℓ) = 0)
    {X : Fin (N : ℕ) → ℝ} (hX : X ∈ orderedDomain N) (k : Fin (N : ℕ)) :
    HasDerivAt (fun t : ℝ => gradLoop s ψ N ℓ γ (X + t • Pi.single k 1))
      (∑ i ∈ gradLabels N ℓ γ, (if gradIndex N i = k then (1 : ℝ) else 0) *
        (2 * (N : ℝ) ^ (-s) * ∑ j ∈ (gradLabels N ℓ γ).erase i,
          gradPairP1 s ψ ℓ (gradLift N X i) (gradLift N X j)
          - 2 * (N : ℝ) ^ (1 - s) * gradJderiv s ψ N ℓ γ (gradLift N X i))) 0 := by
  set α : ℤ → ℝ := fun i => if gradIndex N i = k then (1 : ℝ) else 0 with hα
  set I := gradLabels N ℓ γ with hI
  -- the decomposition of `H_γ` along the line
  have hdec : (fun t : ℝ => gradLoop s ψ N ℓ γ (X + t • Pi.single k 1))
      = fun t : ℝ => (N : ℝ) ^ (-s) * ∑ i ∈ I, ∑ j ∈ I.erase i,
          gradPairKernel s ψ ℓ (gradLift N (X + t • Pi.single k 1) i)
            (gradLift N (X + t • Pi.single k 1) j)
        - 2 * (N : ℝ) ^ (1 - s) * ∑ i ∈ I,
          gradBackground s ψ N ℓ γ (gradLift N (X + t • Pi.single k 1) i) := by
    funext t
    exact gradLoop_eq_pairs_background hψ hℓ0.ne' hp s N γ _
  rw [hdec]
  -- the lifts along the line
  have hlin : ∀ m : ℤ, gradLift N (X + (0 : ℝ) • Pi.single k 1) m = gradLift N X m := by
    intro m; simp
  have hline : ∀ m : ℤ, ∀ t : ℝ, gradLift N (X + t • Pi.single k 1) m = gradLift N X m + t * α m := by
    intro m t
    exact gradLift_add_smul_single N X k t m
  -- the pair derivative
  have hpair : ∀ i ∈ I, ∀ j ∈ I.erase i,
      HasDerivAt (fun t : ℝ => gradPairKernel s ψ ℓ (gradLift N (X + t • Pi.single k 1) i)
          (gradLift N (X + t • Pi.single k 1) j))
        (α i * gradPairP1 s ψ ℓ (gradLift N X i) (gradLift N X j)
          + α j * gradPairP2 s ψ ℓ (gradLift N X i) (gradLift N X j)) 0 := by
    intro i hi j hj
    have hij : i ≠ j := fun h => (Finset.mem_erase.1 hj).1 h.symm
    have hjI : j ∈ I := Finset.mem_of_mem_erase hj
    have hab : ((gradLift N X j - gradLift N X i : ℝ) : UnitAddCircle) ≠ 0 :=
      coe_ne_zero_of_forall_ne_int fun n h => gradLift_sub_not_int hℓ0.le hX hi hjI hij n (by linarith)
    have h := hasDerivAt_gradPairKernel_line hψ hℓ0.ne' hs0 hs1 (gradLift N X i) (gradLift N X j)
      (α i) (α j) hab
    simp only [hline]
    exact h
  have hbg : ∀ i ∈ I, HasDerivAt (fun t : ℝ => gradBackground s ψ N ℓ γ (gradLift N (X + t • Pi.single k 1) i))
      (gradJderiv s ψ N ℓ γ (gradLift N X i) * α i) 0 := by
    intro i _
    have hJ := gradBackground_hasDerivAt hψ hℓ0 hp hs0 hs1 hsupp (gradLift N X i)
    have hl : HasDerivAt (fun t : ℝ => gradLift N X i + t * α i) (α i) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (α i)).const_add (gradLift N X i)
    have hJ' : HasDerivAt (fun y => gradBackground s ψ N ℓ γ y) (gradJderiv s ψ N ℓ γ (gradLift N X i))
        (gradLift N X i + (0 : ℝ) * α i) := by
      rw [zero_mul, add_zero]
      exact hJ
    have h := hJ'.comp (0 : ℝ) hl
    have hfun : (fun t : ℝ => gradBackground s ψ N ℓ γ (gradLift N (X + t • Pi.single k 1) i))
        = (fun y => gradBackground s ψ N ℓ γ y) ∘ (fun t : ℝ => gradLift N X i + t * α i) := by
      funext t
      simp only [Function.comp, hline]
    rw [hfun]
    simpa using h
  -- assemble the two sums
  have hsumP : HasDerivAt (fun t : ℝ => ∑ i ∈ I, ∑ j ∈ I.erase i,
        gradPairKernel s ψ ℓ (gradLift N (X + t • Pi.single k 1) i)
          (gradLift N (X + t • Pi.single k 1) j))
      (∑ i ∈ I, ∑ j ∈ I.erase i, (α i * gradPairP1 s ψ ℓ (gradLift N X i) (gradLift N X j)
          + α j * gradPairP2 s ψ ℓ (gradLift N X i) (gradLift N X j))) 0 := by
    apply HasDerivAt.fun_sum
    intro i hi
    apply HasDerivAt.fun_sum
    intro j hj
    exact hpair i hi j hj
  have hsumB : HasDerivAt (fun t : ℝ => ∑ i ∈ I,
        gradBackground s ψ N ℓ γ (gradLift N (X + t • Pi.single k 1) i))
      (∑ i ∈ I, gradJderiv s ψ N ℓ γ (gradLift N X i) * α i) 0 := by
    apply HasDerivAt.fun_sum
    intro i hi
    exact hbg i hi
  have hcomb := (hsumP.const_mul ((N : ℝ) ^ (-s))).sub (hsumB.const_mul (2 * (N : ℝ) ^ (1 - s)))
  refine hcomb.congr_deriv ?_
  -- the derivative is the claimed sum, by the symmetry of the pair sum
  have hP2 : ∀ i j, gradPairP2 s ψ ℓ (gradLift N X i) (gradLift N X j)
      = gradPairP1 s ψ ℓ (gradLift N X j) (gradLift N X i) := fun i j => gradPairP2_eq_swap s _ _
  have hsym := sum_pair_alpha_eq I
    (fun i j => gradPairP1 s ψ ℓ (gradLift N X i) (gradLift N X j))
    (fun i j => gradPairP2 s ψ ℓ (gradLift N X i) (gradLift N X j))
    α (fun i j => hP2 i j)
  have hsym' : ∑ i ∈ I, ∑ j ∈ I.erase i, (α i * gradPairP1 s ψ ℓ (gradLift N X i) (gradLift N X j)
          + α j * gradPairP2 s ψ ℓ (gradLift N X i) (gradLift N X j))
      = 2 * ∑ i ∈ I, ∑ j ∈ I.erase i, α i * gradPairP1 s ψ ℓ (gradLift N X i) (gradLift N X j) :=
    hsym
  rw [hsym']
  simp only [Finset.mul_sum, mul_sub, Finset.sum_sub_distrib, hα]
  congr 1
  · apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro i _
    ring
  · apply Finset.sum_congr rfl
    intro i _
    ring

/-- The lift is a smooth function of the configuration. -/
lemma contDiff_gradLift (N : ℕ+) (j : ℤ) :
    ContDiff ℝ ∞ (fun X : Fin (N : ℕ) → ℝ => gradLift N X j) := by
  unfold gradLift
  exact (contDiff_apply ℝ (fun _ : Fin (N : ℕ) => ℝ) (gradIndex N j)).add contDiff_const

/-- `H_γ` is smooth at every configuration of the ordered domain. -/
lemma contDiffAt_gradLoop {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) {ℓ γ : ℝ} (hℓ0 : 0 < ℓ)
    (hp : Function.Periodic ψ (1 / ℓ)) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {N : ℕ+}
    (hsupp : GradPartial N ℓ γ → ∀ y : ℝ, (∀ m : ℤ, gradT N ℓ γ / 4 ≤ |y - m|) → ψ (y / ℓ) = 0)
    {X : Fin (N : ℕ) → ℝ}
    (hX : ∀ i ∈ gradLabels N ℓ γ, ∀ j ∈ gradLabels N ℓ γ, i ≠ j →
      ((gradLift N X j - gradLift N X i : ℝ) : UnitAddCircle) ≠ 0) :
    ContDiffAt ℝ ∞ (gradLoop s ψ N ℓ γ) X := by
  have hfun : gradLoop s ψ N ℓ γ = fun Y : Fin (N : ℕ) → ℝ =>
      (N : ℝ) ^ (-s) * ∑ i ∈ gradLabels N ℓ γ, ∑ j ∈ (gradLabels N ℓ γ).erase i,
          gradPairKernel s ψ ℓ (gradLift N Y i) (gradLift N Y j)
        - 2 * (N : ℝ) ^ (1 - s) * ∑ i ∈ gradLabels N ℓ γ, gradBackground s ψ N ℓ γ (gradLift N Y i) := by
    funext Y
    exact gradLoop_eq_pairs_background hψ hℓ0.ne' hp s N γ Y
  rw [hfun]
  apply ContDiffAt.sub
  · apply ContDiffAt.mul contDiffAt_const
    apply ContDiffAt.sum
    intro i hi
    apply ContDiffAt.sum
    intro j hj
    have hij : i ≠ j := fun h => (Finset.mem_erase.1 hj).1 h.symm
    have hjI : j ∈ gradLabels N ℓ γ := Finset.mem_of_mem_erase hj
    have hab : ((gradLift N X j - gradLift N X i : ℝ) : UnitAddCircle) ≠ 0 := hX i hi j hjI hij
    have hk := contDiffAt_gradPairKernel hs0 hs1 hψ (ℓ := ℓ) (gradLift N X i) (gradLift N X j) hab
    have hc : ContDiffAt ℝ ∞ (fun Y : Fin (N : ℕ) → ℝ => (gradLift N Y i, gradLift N Y j)) X :=
      (contDiff_gradLift N i).contDiffAt.prodMk (contDiff_gradLift N j).contDiffAt
    exact hk.comp X hc
  · apply ContDiffAt.mul contDiffAt_const
    apply ContDiffAt.sum
    intro i _
    exact (contDiff_iff_contDiffAt.1 (gradBackground_contDiff hψ hℓ0 hp hs0 hs1 hsupp)
      (gradLift N X i)).comp X (contDiff_gradLift N i).contDiffAt

/-- The directional derivatives of `H_γ` in the coordinate directions are the components of `V + W`
(identity part of Lemma 5.7, `∇H_γ = V + W`). -/
lemma fderiv_gradLoop_single {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) {ℓ γ : ℝ} (hℓ0 : 0 < ℓ)
    (hp : Function.Periodic ψ (1 / ℓ)) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {N : ℕ+}
    (hsupp : GradPartial N ℓ γ → ∀ y : ℝ, (∀ m : ℤ, gradT N ℓ γ / 4 ≤ |y - m|) → ψ (y / ℓ) = 0)
    {X : Fin (N : ℕ) → ℝ} (hX : X ∈ orderedDomain N) (k : Fin (N : ℕ)) :
    fderiv ℝ (gradLoop s ψ N ℓ γ) X (Pi.single k 1)
      = gradVfield s ψ N ℓ γ X k + gradWfield s ψ N ℓ γ X k := by
  have hH := (contDiffAt_gradLoop hψ hℓ0 hp hs0 hs1 hsupp (X := X)
    (fun i hi j hj hij => coe_ne_zero_of_forall_ne_int (gradLift_sub_not_int hℓ0.le hX hi hj hij)))
    |>.differentiableAt (by simp)
  have hline : HasDerivAt (fun t : ℝ => X + t • Pi.single (k : Fin (N : ℕ)) (1 : ℝ))
      (Pi.single k 1) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single (k : Fin (N : ℕ)) (1 : ℝ))).const_add X
  have hH0 : HasFDerivAt (gradLoop s ψ N ℓ γ) (fderiv ℝ (gradLoop s ψ N ℓ γ) X)
      (X + (0 : ℝ) • Pi.single (k : Fin (N : ℕ)) (1 : ℝ)) := by
    rw [zero_smul, add_zero]
    exact hH.hasFDerivAt
  have hcomp := hH0.comp_hasDerivAt (0 : ℝ) hline
  have hder := hasDerivAt_gradLoop_single hψ hℓ0 hp hs0 hs1 hsupp hX k
  have hval : fderiv ℝ (gradLoop s ψ N ℓ γ) X (Pi.single k 1)
      = ∑ i ∈ gradLabels N ℓ γ, (if gradIndex N i = k then (1 : ℝ) else 0) *
        (2 * (N : ℝ) ^ (-s) * ∑ j ∈ (gradLabels N ℓ γ).erase i,
          gradPairP1 s ψ ℓ (gradLift N X i) (gradLift N X j)
          - 2 * (N : ℝ) ^ (1 - s) * gradJderiv s ψ N ℓ γ (gradLift N X i)) :=
    hcomp.unique hder
  rw [hval]
  simp only [gradVfield, gradWfield]
  rw [← Finset.sum_add_distrib, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  rw [gradVlab_add_gradWlab_eq hψ hℓ0 hp hs0 hs1 hsupp hX hi]
  split_ifs <;> ring

end

end Riesz1
