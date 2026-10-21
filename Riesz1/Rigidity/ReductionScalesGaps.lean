/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Rigidity.ReductionScalesWeights
public import Riesz1.Rigidity.ForcingPotential

/-!
# Gap coordinates of the multiscale increments and their reversal

This is part of Lemma 4.4. For a block `I = [i0, i0 + L] ∩ ℤ` with gaps
`g_u = gap X (i0 + u)`, `0 ≤ u < L`, this file writes

* the forcing potential as `forcingFun θ L R (u ↦ g_u)`, a function of the gaps alone
  (`forcingPotential_eq_forcingFun`), and proves that it is invariant under reversal of the block
  gap sequence (`forcingFun_reflect`).
* a linear coefficient vector `gapCoefOf N c L` with `∑_{r ≤ L} c_r x_{i0 + r} = ∑_{u ≤ L} a_u g_u`
  (`sum_coef_cyclicLift_eq_gap`).
* antisymmetry `a_{L - 1 - u} = - a_u` of these gap coefficients when the coefficients are
  palindromic with zero sum (`gapCoefOf_reflect`), which holds for the increment `G_m` when its
  block is symmetric about `i` (`scaleCoef_reflect`).

The reversal of the gap family as a law is in `Riesz1.ReductionScalesReflection`.
-/

@[expose] public section

open MeasureTheory Finset

namespace Riesz1

variable {N : ℕ+}

/-! ### Reindexing integer intervals by offsets -/

/-- A sum over `(a + p, a + n]` is a sum over the offsets `(p, n]`. -/
theorem sum_Ioc_int_eq_range {M : Type*} [AddCommMonoid M] (f : ℤ → M) (a : ℤ) (p n : ℕ) :
    ∑ q ∈ Finset.Ioc (a + p) (a + n), f q = ∑ q ∈ Finset.Ioc p n, f (a + q) := by
  refine Finset.sum_nbij' (fun j => (j - a).toNat) (fun r : ℕ => a + (r : ℤ)) ?_ ?_ ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_Ioc] at hj ⊢
    omega
  · intro r hr
    simp only [Finset.mem_Ioc] at hr ⊢
    omega
  · intro j hj
    simp only [Finset.mem_Ioc] at hj
    omega
  · intro r _
    omega
  · intro j hj
    simp only [Finset.mem_Ioc] at hj
    congr 1
    omega

/-- A sum over `[a + p, a + q)` is a sum over the offsets `[p, q)`. -/
theorem sum_Ico_int_eq_range {M : Type*} [AddCommMonoid M] (f : ℤ → M) (a : ℤ) (p q : ℕ) :
    ∑ u ∈ Finset.Ico (a + p) (a + q), f u = ∑ u ∈ Finset.Ico p q, f (a + u) := by
  refine Finset.sum_nbij' (fun j => (j - a).toNat) (fun r : ℕ => a + (r : ℤ)) ?_ ?_ ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_Ico] at hj ⊢
    omega
  · intro r hr
    simp only [Finset.mem_Ico] at hr ⊢
    omega
  · intro j hj
    simp only [Finset.mem_Ico] at hj
    omega
  · intro r _
    omega
  · intro j hj
    simp only [Finset.mem_Ico] at hj
    congr 1
    omega

/-- A block gap sum is a difference of lifts: `N (x_{i0 + q} - x_{i0 + p}) = ∑_{p ≤ u < q} gap`. -/
theorem N_mul_sub_eq_sum_Ico (X : Configuration N) (i0 : ℤ) {p q : ℕ} (hpq : p ≤ q) :
    ((N : ℕ) : ℝ) * (cyclicLift X (i0 + q) - cyclicLift X (i0 + p)) =
      ∑ u ∈ Finset.Ico p q, gap X (i0 + u) := by
  rw [Finset.sum_Ico_eq_sum_range]
  have h := blockLength_eq_sum X (i0 + (p : ℤ)) (q - p)
  unfold blockLength at h
  have hq : i0 + (p : ℤ) + ((q - p : ℕ) : ℤ) = i0 + q := by omega
  rw [hq] at h
  rw [h]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  push_cast
  ring

/-! ### The forcing potential in gap coordinates -/

/-- The forcing potential of a block of `L` gaps, written in the gap sequence `g : ℕ → ℝ`:
`2 ∑_{0 ≤ p ≤ L} ∑_{p < q ≤ L} θ((∑_{p ≤ u < q} g_u) / R)`. -/
noncomputable def forcingFun (θ : ℝ → ℝ) (L : ℕ) (R : ℝ) (g : ℕ → ℝ) : ℝ :=
  2 * ∑ p ∈ range (L + 1), ∑ q ∈ Finset.Ioc p L, θ ((∑ u ∈ Finset.Ico p q, g u) / R)

/-- The forcing potential `F_{I,R}` is the gap-coordinate forcing potential
evaluated at the gaps `g_u = gap X (i0 + u)` of its block. -/
theorem forcingPotential_eq_forcingFun (θ : ℝ → ℝ) (i0 : ℤ) (L : ℕ) (R : ℝ)
    (X : Configuration N) :
    forcingPotential θ i0 L R X = forcingFun θ L R (fun u => gap X (i0 + u)) := by
  unfold forcingPotential forcingFun
  congr 1
  rw [sum_Icc_eq_sum_range_int (fun p => ∑ q ∈ Finset.Ioc p (i0 + L),
    θ (((N : ℕ) : ℝ) * (cyclicLift X q - cyclicLift X p) / R)) i0 L]
  refine Finset.sum_congr rfl fun p' _ => ?_
  rw [sum_Ioc_int_eq_range (fun q => θ (((N : ℕ) : ℝ) * (cyclicLift X q - cyclicLift X (i0 + p')) / R))
    i0 p' L]
  refine Finset.sum_congr rfl fun q' hq' => ?_
  have hpq : p' ≤ q' := (Finset.mem_Ioc.1 hq').1.le
  rw [N_mul_sub_eq_sum_Ico X i0 hpq]

/-- The gap-coordinate forcing potential is invariant under reversal of the block gap sequence. -/
theorem forcingFun_reflect (θ : ℝ → ℝ) (L : ℕ) (R : ℝ) (g : ℕ → ℝ) :
    forcingFun θ L R (fun u => g (L - 1 - u)) = forcingFun θ L R g := by
  rcases Nat.eq_zero_or_pos L with rfl | hL
  · simp [forcingFun]
  unfold forcingFun
  congr 1
  -- reflect each inner interval `[p, q)` to `[L - q, L - p)`
  have hinner : ∀ p ∈ range (L + 1), ∀ q ∈ Finset.Ioc p L,
      (∑ u ∈ Finset.Ico p q, g (L - 1 - u)) = ∑ u ∈ Finset.Ico (L - q) (L - p), g u := by
    intro p _ q hq
    have hq' := Finset.mem_Ioc.1 hq
    rw [Finset.sum_Ico_reflect (fun u => g u) p (by omega : q ≤ L - 1 + 1)]
    rw [show L - 1 + 1 - q = L - q by omega, show L - 1 + 1 - p = L - p by omega]
  rw [Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl fun q hq => by
    rw [hinner p hp q hq]]
  -- reindex the pairs `(p, q) ↦ (L - q, L - p)`
  rw [Finset.sum_sigma' (range (L + 1)) (fun p => Finset.Ioc p L),
    Finset.sum_sigma' (range (L + 1)) (fun a => Finset.Ioc a L)]
  refine Finset.sum_nbij' (fun x => ⟨L - x.2, L - x.1⟩) (fun x => ⟨L - x.2, L - x.1⟩)
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨p, q⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_Ioc] at hx ⊢
    omega
  · rintro ⟨a, b⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_Ioc] at hx ⊢
    omega
  · rintro ⟨p, q⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_Ioc] at hx
    have h1 : L - (L - p) = p := by omega
    have h2 : L - (L - q) = q := by omega
    simp only [h1, h2]
  · rintro ⟨a, b⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_Ioc] at hx
    have h1 : L - (L - b) = b := by omega
    have h2 : L - (L - a) = a := by omega
    simp only [h1, h2]
  · rintro ⟨p, q⟩ hx
    rfl

/-- The forcing potential depends only on the gaps below `L`. -/
theorem forcingFun_congr_lt (θ : ℝ → ℝ) (L : ℕ) (R : ℝ) {g g' : ℕ → ℝ}
    (h : ∀ u < L, g u = g' u) : forcingFun θ L R g = forcingFun θ L R g' := by
  unfold forcingFun
  congr 1
  refine Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl fun q hq => ?_
  have hp' := Finset.mem_range.1 hp
  have hq' := Finset.mem_Ioc.1 hq
  congr 2
  exact Finset.sum_congr rfl fun u hu => h u (by
    have := Finset.mem_Ico.1 hu
    omega)

/-! ### Gap coefficients of a linear form in the block lifts -/

/-- The coefficient of the gap `g_u` in `∑_{r ≤ L} c_r x_{i0 + r}`, when `∑_{r} c_r = 0`:
`a_u = N^{-1} ∑_{u < r ≤ L} c_r`. -/
noncomputable def gapCoefOf (N : ℝ) (c : ℕ → ℝ) (L u : ℕ) : ℝ :=
  N⁻¹ * ∑ r ∈ range (L + 1), if u < r then c r else 0

/-- Exchange of the order of summation between the lifts and the gaps. -/
theorem sum_mul_sum_Ico_eq (c g : ℕ → ℝ) (L : ℕ) :
    ∑ r ∈ range (L + 1), c r * ∑ u ∈ range r, g u =
      ∑ u ∈ range (L + 1), g u * ∑ r ∈ range (L + 1), if u < r then c r else 0 := by
  have key : ∀ r ∈ range (L + 1), ∑ u ∈ range r, g u =
      ∑ u ∈ range (L + 1), if u < r then g u else 0 := by
    intro r hr
    have hr' := Finset.mem_range.1 hr
    rw [← Finset.sum_filter]
    congr 1
    ext u
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [Finset.sum_congr rfl fun r hr => by rw [key r hr]]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun r _ => ?_
  split_ifs <;> ring

/-- The lifted linear form in the block coordinates has gap representation: if `∑_{r ≤ L} c_r = 0`
then `∑_{r ≤ L} c_r x_{i0 + r} = ∑_{u ≤ L} a_u g_u` with `g_u = gap X (i0 + u)`. -/
theorem sum_coef_cyclicLift_eq_gap (X : Configuration N) (i0 : ℤ) (c : ℕ → ℝ) (L : ℕ)
    (hsum : ∑ r ∈ range (L + 1), c r = 0) :
    ∑ r ∈ range (L + 1), c r * cyclicLift X (i0 + r) =
      ∑ u ∈ range (L + 1), gapCoefOf ((N : ℕ) : ℝ) c L u * gap X (i0 + u) := by
  have hN : ((N : ℕ) : ℝ) ≠ 0 := by exact_mod_cast N.ne_zero
  have hr : ∀ r : ℕ, cyclicLift X (i0 + r) =
      cyclicLift X i0 + ((N : ℕ) : ℝ)⁻¹ * ∑ u ∈ range r, gap X (i0 + u) := by
    intro r
    have h := blockLength_eq_sum X i0 r
    unfold blockLength at h
    have h' : cyclicLift X (i0 + r) - cyclicLift X i0 = ((N : ℕ) : ℝ)⁻¹ *
        ∑ u ∈ range r, gap X (i0 + u) := by
      rw [← h, inv_mul_cancel_left₀ hN]
    linarith
  simp only [hr, mul_add, Finset.sum_add_distrib]
  have h0 : ∑ r ∈ range (L + 1), c r * cyclicLift X i0 = 0 := by
    rw [← Finset.sum_mul, hsum, zero_mul]
  rw [h0, zero_add]
  rw [show ∑ r ∈ range (L + 1), c r * (((N : ℕ) : ℝ)⁻¹ * ∑ u ∈ range r, gap X (i0 + u)) =
      ((N : ℕ) : ℝ)⁻¹ * ∑ r ∈ range (L + 1), c r * ∑ u ∈ range r, gap X (i0 + u) by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    ring]
  rw [sum_mul_sum_Ico_eq c (fun u => gap X (i0 + u)) L]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  unfold gapCoefOf
  ring

/-- The gap coefficients are antisymmetric under reversal of the block when the lifted coefficients are
palindromic with zero sum. -/
theorem gapCoefOf_reflect (N : ℝ) (c : ℕ → ℝ) (L : ℕ) (hpal : ∀ r ≤ L, c (L - r) = c r)
    (hsum : ∑ r ∈ range (L + 1), c r = 0) {u : ℕ} (hu : u < L) :
    gapCoefOf N c L (L - 1 - u) = -gapCoefOf N c L u := by
  unfold gapCoefOf
  have hB : ∑ r ∈ range (L + 1), (if L - 1 - u < r then c r else 0) =
      ∑ r ∈ range (L + 1), (if r < u + 1 then c r else 0) := by
    have hrefl := Finset.sum_range_reflect (fun r => if L - 1 - u < r then c r else 0) (L + 1)
    simp only [Nat.add_sub_cancel] at hrefl
    rw [← hrefl]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j < L + 1 := Finset.mem_range.1 hj
    rw [hpal j (by omega)]
    by_cases h1 : L - 1 - u < L - j
    · have h2 : j < u + 1 := by omega
      simp [h1, h2]
    · have h2 : ¬ j < u + 1 := by omega
      simp [h1, h2]
  have hsplit : ∑ r ∈ range (L + 1), (if u < r then c r else 0) +
      ∑ r ∈ range (L + 1), (if r < u + 1 then c r else 0) = ∑ r ∈ range (L + 1), c r := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    by_cases h1 : u < r
    · have h2 : ¬ r < u + 1 := by omega
      simp [h1, h2]
    · have h2 : r < u + 1 := by omega
      simp [h1, h2]
  rw [hsum] at hsplit
  rw [hB]
  linear_combination (N⁻¹) * hsplit

/-! ### Palindromic coefficients of symmetric blocks -/

/-- The coefficient of `G_m` is palindromic on a block symmetric about `i`: when `2K < N`, the block
`J_K(i)` and every lower representative set `J_{k'}(i)`, `k' ≤ K`, are symmetric about `i`, and
`i0 + L = 2i - i0`. -/
theorem scaleCoef_reflect (i : ℤ) {k q m : ℕ} (hk : 1 ≤ k) (_hkN : 2 * k ≤ (N : ℕ))
    (hm : m < q) (hsym : 2 * scaleIndex k q (m + 1) < (N : ℕ)) {r : ℕ}
    (hr : r ≤ cyclicRepSpan N (scaleIndex k q (m + 1))) :
    scaleCoef N i k q m (cyclicRepSpan N (scaleIndex k q (m + 1)) - r) = scaleCoef N i k q m r := by
  set K := scaleIndex k q (m + 1) with hKdef
  have hK : 1 ≤ K := one_le_scaleIndex hk
  have hKk : K ≤ k := (scaleIndex_mem hk (by omega) (by omega)).2
  have hlow : lowScale k q m ≤ K := lowScale_le hk
  have hspan : cyclicRepSpan N K = 2 * K := by
    unfold cyclicRepSpan
    rw [ite_eq_left hsym]
  have hstart : cyclicRepStart N K i = i - K := by
    unfold cyclicRepStart
    rw [ite_eq_left hsym]
  have hlowN : 2 * lowScale k q m < (N : ℕ) := by omega
  rw [hspan] at hr ⊢
  -- the lower weights: `i - K + (2K - r)` and `i - K + r` lie in the same symmetric set
  have hlowEq : blockWeight (cyclicRep N (lowScale k q m) i) (i - K + ((2 * K - r : ℕ) : ℤ)) =
      blockWeight (cyclicRep N (lowScale k q m) i) (i - K + (r : ℤ)) := by
    unfold blockWeight
    simp only [mem_cyclicRep_of_two_mul_lt hlowN]
    by_cases h1 : i - ((lowScale k q m : ℕ) : ℤ) ≤ i - K + (r : ℤ) ∧
        i - K + (r : ℤ) ≤ i + ((lowScale k q m : ℕ) : ℤ)
    · have h2 : i - ((lowScale k q m : ℕ) : ℤ) ≤ i - K + ((2 * K - r : ℕ) : ℤ) ∧
          i - K + ((2 * K - r : ℕ) : ℤ) ≤ i + ((lowScale k q m : ℕ) : ℤ) := by
        constructor <;> omega
      rw [ite_eq_left h1, ite_eq_left h2]
    · have h2 : ¬ (i - ((lowScale k q m : ℕ) : ℤ) ≤ i - K + ((2 * K - r : ℕ) : ℤ) ∧
          i - K + ((2 * K - r : ℕ) : ℤ) ≤ i + ((lowScale k q m : ℕ) : ℤ)) := by
        omega
      rw [ite_eq_right h1, ite_eq_right h2]
  -- the block weights are constant on the block itself
  have hKEq : blockWeight (cyclicRep N K i) (i - K + ((2 * K - r : ℕ) : ℤ)) =
      blockWeight (cyclicRep N K i) (i - K + (r : ℤ)) := by
    unfold blockWeight
    simp only [mem_cyclicRep_of_two_mul_lt hsym]
    have h1 : i - (K : ℤ) ≤ i - K + (r : ℤ) ∧ i - K + (r : ℤ) ≤ i + K := by
      constructor <;> omega
    have h2 : i - (K : ℤ) ≤ i - K + ((2 * K - r : ℕ) : ℤ) ∧
        i - K + ((2 * K - r : ℕ) : ℤ) ≤ i + K := by
      constructor <;> omega
    rw [ite_eq_left h1, ite_eq_left h2]
  unfold scaleCoef
  rw [hstart, hlowEq, hKEq]

end Riesz1

end
