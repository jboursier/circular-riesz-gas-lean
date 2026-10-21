/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.SignedPowerRemainder

/-!
# Smooth cancellation of transport kernels

The comparison needed to remove exterior marks
requires two derivatives, including through the diagonal. Here the paired
series is differentiated on every window strictly inside `(-1,1)`.
-/

public section

open MeasureTheory Set Filter
open scoped Topology ContDiff

namespace Riesz1.Internal

/-- The paired transport series has summable bounds for every derivative
on an arbitrary strict subwindow of the puncture-free interval. -/
theorem regMicro_pairTerm_bounds {s θ : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    ∀ m : ℕ, ∃ V : ℕ → ℝ, Summable V ∧ ∀ k : ℕ, ∀ x ∈ Ioo (-θ) θ,
      ‖iteratedDeriv m (fun z => pairTerm s z k) x‖ ≤ V k := by
  let δ := 1-θ
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hδ1 : δ ≤ 1 := by dsimp [δ]; linarith
  have hsep (k : ℕ) (x : ℝ) (hx : x ∈ Ioo (-θ) θ) :
      δ*((k : ℝ)+1) ≤ ((k : ℝ)+1)-x ∧
      δ*((k : ℝ)+1) ≤ ((k : ℝ)+1)+x := by
    have hk := Nat.cast_nonneg (α := ℝ) k
    have hh : δ*((k : ℝ)+1) ≤ (k : ℝ)+δ := by nlinarith
    constructor <;> dsimp [δ] at * <;> linarith [hx.1, hx.2]
  intro m
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · refine ⟨fun k => 2*δ^(s-2)*((k : ℝ)+1)^(s-2), ?_, ?_⟩
    · have hh := (summable_nat_add_iff 1).2
        (Real.summable_nat_rpow.mpr (by linarith : s-2 < -1))
      simpa only [Nat.cast_add, Nat.cast_one] using hh.mul_left (2*δ^(s-2))
    · intro k x hx
      have hc : 0 < δ*((k : ℝ)+1) := by positivity
      have hd := abs_signPow_sub_le_of_le hs0 hs1 hc (hsep k x hx).1 (hsep k x hx).2
      have heq : pairTerm s x k =
          signPow s (((k : ℝ)+1)+x)-signPow s (((k : ℝ)+1)-x) := by
        unfold pairTerm
        rw [show x-((k : ℝ)+1) = -(((k : ℝ)+1)-x) by ring, signPow_neg']
        rw [add_comm x ((k : ℝ)+1)]
        ring
      have hsmall : (1-s)*(2*|x|) ≤ 2 := by
        have hxa : |x| < 1 := (abs_lt.mpr hx).trans hθ1
        nlinarith [abs_nonneg x, mul_nonneg hs0.le (abs_nonneg x)]
      rw [iteratedDeriv_zero, Real.norm_eq_abs, heq]
      calc
        _ ≤ (1-s)*(δ*((k : ℝ)+1))^(s-2)*|((k : ℝ)+1)+x-(((k : ℝ)+1)-x)| := hd
        _ = ((1-s)*(2*|x|))*(δ*((k : ℝ)+1))^(s-2) := by
          rw [show ((k : ℝ)+1)+x-(((k : ℝ)+1)-x) = 2*x by ring, abs_mul, abs_two]
          ring
        _ ≤ 2*(δ*((k : ℝ)+1))^(s-2) :=
          mul_le_mul_of_nonneg_right hsmall (by positivity)
        _ = _ := by rw [Real.mul_rpow hδ.le (by positivity)]; ring
  · have hm1 : 1 ≤ m := hm
    have hmr : (1 : ℝ) ≤ m := by exact_mod_cast hm1
    let e := s-1-(m : ℝ)
    refine ⟨fun k => 2*derivCoeff s m*δ^e*((k : ℝ)+1)^e, ?_, ?_⟩
    · have hh := (summable_nat_add_iff 1).2
        (Real.summable_nat_rpow.mpr (by dsimp [e]; linarith : e < -1))
      simpa only [Nat.cast_add, Nat.cast_one] using hh.mul_left (2*derivCoeff s m*δ^e)
    · intro k x hx
      have hc : 0 < δ*((k : ℝ)+1) := by positivity
      have ha : x-((k : ℝ)+1) ≠ 0 := by
        have hk := Nat.cast_nonneg (α := ℝ) k
        linarith [hx.2]
      have hb : x+((k : ℝ)+1) ≠ 0 := by
        have hk := Nat.cast_nonneg (α := ℝ) k
        linarith [hx.1]
      have heq : iteratedDeriv m (fun z => pairTerm s z k) x =
          iteratedDeriv m (signPow s) (x-((k : ℝ)+1)) +
          iteratedDeriv m (signPow s) (x+((k : ℝ)+1)) := by
        unfold pairTerm
        rw [iteratedDeriv_fun_add (contDiffAt_signPow_sub (n := (m : WithTop ℕ∞)) ha)
          (contDiffAt_signPow_add (n := (m : WithTop ℕ∞)) hb),
          iteratedDeriv_comp_sub_const, iteratedDeriv_comp_add_const]
      have hpow (v : ℝ) (hv : v ≠ 0) (hd : δ*((k : ℝ)+1) ≤ |v|) :
          |iteratedDeriv m (signPow s) v| ≤
            derivCoeff s m*δ^e*((k : ℝ)+1)^e := by
        rw [abs_iteratedDeriv_signPow s m hv]
        have hh := Real.rpow_le_rpow_of_nonpos hc hd (by dsimp [e]; linarith : e ≤ 0)
        rw [Real.mul_rpow hδ.le (by positivity)] at hh
        exact (mul_le_mul_of_nonneg_left hh (derivCoeff_nonneg s m)).trans_eq (by ring)
      have hda : δ*((k : ℝ)+1) ≤ |x-((k : ℝ)+1)| :=
        (hsep k x hx).1.trans (by rw [abs_sub_comm]; exact le_abs_self _)
      have hdb : δ*((k : ℝ)+1) ≤ |x+((k : ℝ)+1)| :=
        (hsep k x hx).2.trans (by rw [add_comm]; exact le_abs_self _)
      rw [heq, Real.norm_eq_abs]
      exact (abs_add_le _ _).trans (by linarith [hpow _ ha hda, hpow _ hb hdb])

/-- Smoothness of the paired series through zero on the entire interval
between the two neighboring lattice singularities. -/
theorem regMicro_pairSum_smooth {s θ : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    ContDiffOn ℝ ∞ (fun z => ∑' k : ℕ, pairTerm s z k) (Ioo (-θ) θ) := by
  apply contDiffOn_tsum_window isOpen_Ioo (convex_Ioo _ _).isPreconnected
    (hbd := regMicro_pairTerm_bounds hs0 hs1 hθ0 hθ1)
  intro k x hx
  have hk := Nat.cast_nonneg (α := ℝ) k
  exact ((contDiffAt_signPow_sub (n := ∞) (by linarith [hx.2] : x-((k : ℝ)+1) ≠ 0)).add
    (contDiffAt_signPow_add (n := ∞) (by linarith [hx.1] : x+((k : ℝ)+1) ≠ 0))).contDiffWithinAt

/-- Subtracting the central signed power removes the singularity to
every order. All derivative bounds precede the circumference. -/
theorem regMicro_scaledKernel_smooth_remainder {s θ : ℝ}
    (hs0 : 0 < s) (hs1 : s < 1) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    ∃ C : ℕ → ℝ, (∀ m, 0 < C m) ∧ ∀ L : ℝ, 1 ≤ L → ∃ H : ℝ → ℝ,
      ContDiffOn ℝ ∞ H (Ioo (-θ) θ) ∧
      (∀ m x, |x| < θ → ‖iteratedDeriv m H x‖ ≤ C m) ∧
      ∀ x, |x| < θ → x ≠ 0 → scaledKernel s L x = signPow s x + H x := by
  classical
  let S := fun z => ∑' k : ℕ, pairTerm s z k
  have hS := regMicro_pairSum_smooth hs0 hs1 hθ0 hθ1
  choose V hV hb using regMicro_pairTerm_bounds hs0 hs1 hθ0 hθ1
  let C := fun m => (∑' k, V m k)+1
  have hC (m : ℕ) : 0 < C m := by
    have hn (k : ℕ) : 0 ≤ V m k := (norm_nonneg _).trans (hb m k 0 ⟨by linarith, hθ0⟩)
    dsimp [C]
    linarith [show 0 ≤ (∑' k : ℕ, V m k) from tsum_nonneg hn]
  have hbound (m : ℕ) (x : ℝ) (hx : |x| < θ) : ‖iteratedDeriv m S x‖ ≤ C m := by
    rw [iteratedDeriv_tsum_window isOpen_Ioo (convex_Ioo _ _).isPreconnected
      (hsm := fun k y hy => by
        have hk := Nat.cast_nonneg (α := ℝ) k
        exact ((contDiffAt_signPow_sub (n := ∞) (by linarith [hy.2] : y-((k : ℝ)+1) ≠ 0)).add
          (contDiffAt_signPow_add (n := ∞) (by linarith [hy.1] : y+((k : ℝ)+1) ≠ 0))).contDiffWithinAt)
      (regMicro_pairTerm_bounds hs0 hs1 hθ0 hθ1) m x (abs_lt.mp hx)]
    exact (tsum_of_norm_bounded (hV m).hasSum (fun k => hb m k x (abs_lt.mp hx))).trans
      (by dsimp [C]; linarith)
  refine ⟨C, hC, fun L hL => ?_⟩
  have hLp : 0 < L := by linarith
  let H := fun x => L^(s-1)*S (L⁻¹*x)
  have hwin (x : ℝ) (hx : |x| < θ) : |L⁻¹*x| < θ := by
    rw [mul_comm, ← div_eq_mul_inv, abs_div, abs_of_pos hLp]
    exact (div_le_self (abs_nonneg x) hL).trans_lt hx
  have hsm : ContDiffOn ℝ ∞ (fun x => S (L⁻¹*x)) (Ioo (-θ) θ) := by
    apply hS.comp (contDiff_const.mul contDiff_id).contDiffOn
    intro x hx
    exact abs_lt.mp (hwin x (abs_lt.mpr hx))
  refine ⟨H, contDiffOn_const.mul hsm, fun m x hx => ?_, fun x hx hx0 => ?_⟩
  · have hh : ContDiffAt ℝ (m : WithTop ℕ∞) (fun x => S (L⁻¹*x)) x :=
      (hsm.contDiffAt (isOpen_Ioo.mem_nhds (abs_lt.mp hx))).of_le (by simp)
    change ‖iteratedDeriv m (L^(s-1) • (fun x => S (L⁻¹*x))) x‖ ≤ C m
    rw [iteratedDeriv_const_smul hh, smul_eq_mul,
      iteratedDeriv_comp_mul_of_contDiffOn isOpen_Ioo L⁻¹ m S hS x
        (abs_lt.mp (hwin x hx)), norm_mul, norm_mul, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hLp.le _), Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg (inv_pos.mpr hLp).le m)]
    have hscale : L^(s-1)*(L⁻¹)^m = L^(s-1-(m : ℝ)) := by
      rw [inv_pow, ← Real.rpow_natCast, ← Real.rpow_neg hLp.le, ← Real.rpow_add hLp]
      congr 1
    rw [← mul_assoc, hscale]
    have hscl := Real.rpow_le_one_of_one_le_of_nonpos hL
      (by linarith [Nat.cast_nonneg (α := ℝ) m] : s-1-(m : ℝ) ≤ 0)
    exact (mul_le_mul_of_nonneg_left (hbound m _ (hwin x hx)) (by positivity)).trans
      (mul_le_of_le_one_left (hC m).le hscl)
  · have heq : H x = L^(s-1)*(∑' k : ℕ, pairTerm s (x/L) k) := by
      dsimp [H, S]
      rw [mul_comm L⁻¹, ← div_eq_mul_inv]
    rw [heq]
    have hn : ∀ k : ℤ, x ≠ k*L := by
      intro k he
      by_cases hk : k = 0
      · exact hx0 (by simpa only [hk, Int.cast_zero, zero_mul] using he)
      · have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast Int.one_le_abs hk
        have hh : L ≤ |x| := by rw [he, abs_mul, abs_of_pos hLp]; nlinarith
        linarith
    have hxL : |x/L| < 1 := by
      have hh := hwin x hx
      rw [mul_comm L⁻¹, ← div_eq_mul_inv] at hh
      exact hh.trans hθ1
    rw [scaledKernel_eq_periodic hs0 hs1 hLp hn,
      periodicKernel_eq_add_pairs_unit hs0 hs1 hxL (div_ne_zero hx0 hLp.ne'), mul_add]
    congr 1
    rw [← signPow_mul_pos hLp, mul_div_cancel₀ _ hLp.ne']

/-- The difference of two transport kernels has a smooth extension
through the diagonal, uniformly bounded to every order before both lengths. -/
theorem regMicro_scaledKernel_smooth_difference {s θ : ℝ}
    (hs0 : 0 < s) (hs1 : s < 1) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    ∃ C : ℕ → ℝ, (∀ m, 0 < C m) ∧ ∀ L T : ℝ, 1 ≤ L → 1 ≤ T → ∃ H : ℝ → ℝ,
      ContDiffOn ℝ ∞ H (Ioo (-θ) θ) ∧
      (∀ m x, |x| < θ → ‖iteratedDeriv m H x‖ ≤ C m) ∧
      ∀ x, |x| < θ → x ≠ 0 → scaledKernel s L x-scaledKernel s T x = H x := by
  obtain ⟨C, hC, hr⟩ := regMicro_scaledKernel_smooth_remainder hs0 hs1 hθ0 hθ1
  refine ⟨fun m => 2*C m, fun m => mul_pos (by norm_num) (hC m), fun L T hL hT => ?_⟩
  obtain ⟨F, hF, hbF, heF⟩ := hr L hL
  obtain ⟨G, hG, hbG, heG⟩ := hr T hT
  refine ⟨fun x => F x-G x, hF.sub hG, fun m x hx => ?_, fun x hx hx0 => ?_⟩
  · rw [iteratedDeriv_fun_sub
      ((hF.contDiffAt (isOpen_Ioo.mem_nhds (abs_lt.mp hx))).of_le (by simp))
      ((hG.contDiffAt (isOpen_Ioo.mem_nhds (abs_lt.mp hx))).of_le (by simp))]
    exact (norm_sub_le _ _).trans (by linarith [hbF m x hx, hbG m x hx])
  · rw [heF x hx hx0, heG x hx hx0]
    ring

end Riesz1.Internal
