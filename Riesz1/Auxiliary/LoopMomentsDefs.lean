/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Rigidity.Gaps
public import Mathlib.Analysis.Normed.Group.AddCircle
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Microscopic counts, discrepancies and rooted energies

On the microscopic circle
`N𝕋 = AddCircle (N : ℝ)` the particles sit at `z_i = N x_i`. This file defines

* the open arc `microArc N a r` of length `r` starting at `a`,
* the count `loopCount N a r X` of particles in the arc,
* the discrepancy `loopDiscrepancy N a r X` (count minus arclength),
* the rooted inverse energy `rootedEnergy s X i` of particle `i`,

and proves the bridge lemmas between them and the gap and block lengths of
`Riesz1.Rigidity.Gaps`: the arc membership criterion, the circular norm of a block,
and the identity `dist (z_i) (z_{i+k}) = |S_{i,k}|` on the circle.
-/

@[expose] public section

noncomputable section

open MeasureTheory Finset Set

attribute [local instance] Classical.propDecidable

namespace Riesz1

/-- The circle `AddCircle (N : ℝ)` has period `N > 0`. -/
instance factPNatPos (N : ℕ+) : Fact (0 < (N : ℝ)) := ⟨by exact_mod_cast N.pos⟩

/-- The microscopic position `z_i = N x_i` of the particle with index `i`, on `N𝕋`. -/
def loopPos {N : ℕ+} (X : Configuration N) (i : Fin (N : ℕ)) : AddCircle (N : ℝ) :=
  (((N : ℝ) * X.val i : ℝ) : AddCircle (N : ℝ))

/-- The open arc of `N𝕋` of arclength `r`, starting at the real point `a`. -/
def microArc (N : ℕ+) (a r : ℝ) : Set (AddCircle (N : ℝ)) :=
  (fun t : ℝ => (t : AddCircle (N : ℝ))) '' Ioo a (a + r)

/-- The count `M_J = ∑_i 1_J(z_i)` of microscopic particles in the arc `microArc N a r`. -/
def loopCount {N : ℕ+} (a r : ℝ) (X : Configuration N) : ℝ :=
  ∑ i : Fin (N : ℕ), if loopPos X i ∈ microArc N a r then 1 else 0

/-- The discrepancy `ν(J) = M_J - |J|` of the arc `microArc N a r`, where `|J|` is the
arclength, the Haar measure of `J` in `N𝕋`. -/
def loopDiscrepancy {N : ℕ+} (a r : ℝ) (X : Configuration N) : ℝ :=
  loopCount a r X - (volume (microArc N a r)).toReal

/-- The rooted local inverse energy `E_i = ∑_{j ≠ i, dist(z_i, z_j) ≤ 3} dist(z_i, z_j)^{-s}`
of the particle `i`, with the circular distance of `N𝕋`. -/
def rootedEnergy (s : ℝ) {N : ℕ+} (X : Configuration N) (i : Fin (N : ℕ)) : ℝ :=
  ∑ j ∈ univ.filter (fun j => j ≠ i ∧ dist (loopPos X i) (loopPos X j) ≤ 3),
    dist (loopPos X i) (loopPos X j) ^ (-s)

/-! ### Arcs and coincidences in `N𝕋` -/

/-- Two real points have the same image in `N𝕋` exactly when they differ by an integer
multiple of `N`. -/
theorem coe_eq_coe_iff_int {N : ℕ+} (s t : ℝ) :
    ((s : AddCircle (N : ℝ)) = (t : AddCircle (N : ℝ))) ↔ ∃ n : ℤ, s = t + n * N := by
  rw [← sub_eq_zero, ← QuotientAddGroup.mk_sub]
  constructor
  · intro h
    obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (N : ℝ)).mp h
    exact ⟨n, by rw [zsmul_eq_mul] at hn; linarith⟩
  · rintro ⟨n, hn⟩
    exact (AddCircle.coe_eq_zero_iff (N : ℝ)).mpr ⟨n, by rw [zsmul_eq_mul, hn]; ring⟩

/-- Membership in the arc, described on real lifts: `t` lies in `microArc N a r` exactly when
some integer translate of `t` lies in the interval `(a, a + r)`. -/
theorem coe_mem_microArc_iff {N : ℕ+} (a r t : ℝ) :
    (t : AddCircle (N : ℝ)) ∈ microArc N a r ↔
      ∃ n : ℤ, a < t + n * N ∧ t + n * N < a + r := by
  constructor
  · rintro ⟨s, hs, hst⟩
    obtain ⟨n, hn⟩ := (coe_eq_coe_iff_int s t).mp hst
    exact ⟨n, by rw [← hn]; exact hs.1, by rw [← hn]; exact hs.2⟩
  · rintro ⟨n, h1, h2⟩
    refine ⟨t + n * N, ⟨h1, h2⟩, ?_⟩
    exact (coe_eq_coe_iff_int _ _).mpr ⟨n, rfl⟩

/-! ### Circular norms of blocks -/

/-- The circular norm of a block length `0 < S < N` in `N𝕋` is the smaller of `S` and `N - S`. -/
theorem norm_coe_block {N : ℕ+} {S : ℝ} (h0 : 0 < S) (h1 : S < N) :
    ‖(S : AddCircle (N : ℝ))‖ = min S ((N : ℝ) - S) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hfrac : S / N < 1 := by rw [div_lt_one hN]; exact h1
  rcases lt_or_ge (S / N) (1 / 2) with hlt | hge
  · have hr : round (S / N) = 0 := by
      rw [round_eq, Int.floor_eq_iff]
      constructor <;> push_cast <;> linarith [div_pos h0 hN]
    have hle : S ≤ (N : ℝ) - S := by
      rw [div_lt_iff₀ hN] at hlt
      linarith
    rw [AddCircle.norm_eq, inv_mul_eq_div, hr, Int.cast_zero, zero_mul, sub_zero,
      abs_of_pos h0, min_eq_left hle]
  · have hr : round (S / N) = 1 := by
      rw [round_eq, Int.floor_eq_iff]
      constructor <;> push_cast <;> linarith [div_pos h0 hN]
    have hle : (N : ℝ) - S ≤ S := by
      rw [le_div_iff₀ hN] at hge
      linarith
    rw [AddCircle.norm_eq, inv_mul_eq_div, hr, Int.cast_one, one_mul,
      abs_of_nonpos (by linarith), min_eq_right hle]
    ring

/-- The circular distance between the particles at `z_i` and `z_{i+k}` is the norm of the block
`S_{i,k} = N (x_{i+k} - x_i)`. The index `i + k` is reduced modulo `N` to name the particle. -/
theorem dist_loopPos_eq_block {N : ℕ+} (X : Configuration N) (i : Fin (N : ℕ)) (k : ℕ) :
    dist (loopPos X i) (loopPos X ⟨(i + k) % (N : ℕ), Nat.mod_lt _ N.pos⟩) =
      ‖((blockLength X (i : ℕ) k : ℝ) : AddCircle (N : ℝ))‖ := by
  set j : ℕ := (i + k) % (N : ℕ) with hj
  set q : ℕ := (i + k) / (N : ℕ) with hq
  have hjN : j < (N : ℕ) := Nat.mod_lt _ N.pos
  have hsum : ((i : ℤ) + (k : ℤ)) = (j : ℤ) + ((N : ℕ) : ℤ) * (q : ℤ) := by
    have h := Nat.mod_add_div (i + k) (N : ℕ)
    rw [← hj, ← hq] at h
    exact_mod_cast h.symm
  have hcl : cyclicLift X ((i : ℤ) + (k : ℤ)) = X.val ⟨j, hjN⟩ + (q : ℤ) := by
    rw [hsum]
    exact cyclicLift_add_mul X hjN q
  have hcli : cyclicLift X ((i : ℕ) : ℤ) = X.val i := cyclicLift_natCast X i
  have hblock : blockLength X (i : ℕ) k = (N : ℝ) * (X.val ⟨j, hjN⟩ + (q : ℝ) - X.val i) := by
    unfold blockLength
    rw [hcl, hcli]
    push_cast
    ring
  rw [dist_eq_norm, ← norm_neg, hblock]
  congr 1
  unfold loopPos
  rw [neg_sub]
  change ((((N : ℝ) * X.val ⟨j, hjN⟩ : ℝ) : AddCircle (N : ℝ)) -
      (((N : ℝ) * X.val i : ℝ) : AddCircle (N : ℝ))) = _
  rw [← QuotientAddGroup.mk_sub]
  exact (coe_eq_coe_iff_int _ _).mpr ⟨-(q : ℤ), by push_cast; ring⟩

end Riesz1

end
end
