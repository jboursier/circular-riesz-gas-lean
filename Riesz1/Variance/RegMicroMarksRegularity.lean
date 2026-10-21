/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.RegMicroMarksComparison
public import Riesz1.Variance.RegMicroMarksSelection
public import Riesz1.Variance.RegMicroMarksInner

/-!
# Removing exterior marks from compact transport regularity

A large observation circle detects the fixed real
singularities. Smooth comparison transfers them to every other circle,
even when exterior real marks wrap into the support. Off-support kernel
bounds supply the rest of the derivative envelope.
-/

public section

open MeasureTheory Set Filter
open scoped Topology ContDiff

namespace Riesz1.Internal

/-- Preserve the complete regularity predicate after replacing
the original marks by fixed interior marks that contain every possible
real singularity. No original transport hypothesis is needed on the
additional observation circle, only its primitive regularity. -/
theorem regMicro_remove_exterior_marks
    (P : Parameters) (p : Profile) {r q : ℝ}
    (hr : 0 < r) (hrq : r < q) (hq : q < 1/2)
    (hsupp : ∀ᵐ y : ℝ, r ≤ |y| → zeroExtension p y = 0)
    (η B C₀ α : ℝ) (n : ℕ+) (a : Fin (n : ℕ) → ℝ)
    (hη : 0 < η) (hB : 0 ≤ B) (hC₀ : 0 ≤ C₀)
    (hα : P.val.2-1 ≤ α) (hα2 : α < P.val.2/2)
    (m : ℕ+) (b : Fin (m : ℕ) → ℝ)
    (hb : Function.Injective b) (hbin : ∀ j, |b j| ≤ q)
    (hcover : ∀ i, |a i| ≤ q → ∃ j, b j = a i) :
    ∃ C : ℝ, 0 < C ∧ ∀ ell : Scales,
      Tendsto (fun k : ℕ => (ell ⟨k+1, Nat.succ_pos k⟩).val) atTop (𝓝 0) →
      (∀ N, PrimitiveRegularity (observationLength (ell N)) η P.val.2 B
          ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ ∧
        TransportRegularity P (observationLength (ell N))
          ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩
            n a α C₀) →
      ∀ c : Scale, PrimitiveRegularity (observationLength c) η P.val.2 B
        ⟨periodizedProfile p (observationLength c), periodizedProfileL2 p c⟩ →
        TransportRegularity P (observationLength c)
          ⟨periodizedProfile p (observationLength c), periodizedProfileL2 p c⟩ m b α C := by
  classical
  let σ := (r+q)/2
  have hrσ : r < σ := by dsimp [σ]; linarith
  have hσq : σ < q := by dsimp [σ]; linarith
  have hσ : σ < 1/2 := hσq.trans hq
  have hσ0 : 0 < σ := hr.trans hrσ
  let e := -2+P.val.2-α
  have he : e ≤ 0 := by dsimp [e]; linarith
  obtain ⟨D, hD, hbase⟩ := exists_uniform_transport_sup_secondDeriv P η B n a α α C₀
    hη hB hC₀ hα hα2 le_rfl
  obtain ⟨Q, hQ, hcompare⟩ := regMicro_transport_difference_smooth P p hr hσ hrσ hsupp
  obtain ⟨T, hT, hoff⟩ := uniform_transport_deriv_off_support P 2 (by norm_num)
  obtain ⟨U, hU, htail⟩ := compact_transport_second_off_support P p ⟨r, hr, hrq.trans hq, hsupp⟩
  obtain ⟨δ, hδ, hsep⟩ := exists_uniform_circle_separation_of_inner b hb hq hbin
  let Z := ∫ y : ℝ, |zeroExtension p y|
  let E := T*Z*(σ-r)^(P.val.2-3)
  let A := (2+|b ⟨0, m.pos⟩|)^(-e)
  let J := D*(1+(n : ℝ)*(q-σ)^e)+Q 2
  let C := J*A+D*(n : ℝ)+E*A+U+1
  have hZ : 0 ≤ Z := integral_nonneg fun _ => abs_nonneg _
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  have hJ : 0 < J := by
    dsimp [J]
    have hh : 0 ≤ (n : ℝ)*(q-σ)^e := by positivity
    linarith [mul_pos hD (by linarith : 0 < 1+(n : ℝ)*(q-σ)^e), hQ 2]
  have hC : 0 < C := by dsimp [C]; positivity
  have hJC : J*A+D*(n : ℝ) ≤ C := by dsimp [C]; linarith [mul_nonneg hE hA.le]
  have hEC : E*A ≤ C := by dsimp [C]; linarith [mul_nonneg hJ.le hA.le, mul_nonneg hD.le (by positivity : 0 ≤ (n : ℝ))]
  have hUC : U ≤ C := by dsimp [C]; linarith [mul_nonneg hJ.le hA.le, mul_nonneg hE hA.le, mul_nonneg hD.le (by positivity : 0 ≤ (n : ℝ))]
  let R := 2+∑ i, |a i|
  have hR : 2 ≤ R := by
    dsimp [R]
    linarith [Finset.sum_nonneg (s := Finset.univ) (fun i _ => abs_nonneg (a i))]
  have haR (i : Fin (n : ℕ)) : |a i| ≤ R := by
    have hh := Finset.single_le_sum (s := Finset.univ) (f := fun j => |a j|)
      (fun j _ => abs_nonneg (a j)) (Finset.mem_univ i)
    dsimp [R]
    linarith
  refine ⟨C, hC, fun ell hell hfamily c hprim => ?_⟩
  obtain ⟨k, hk⟩ := (hell.eventually
    (eventually_lt_nhds (inv_pos.mpr (by linarith : 0 < 4*R)))).exists
  let c' := ell ⟨k+1, Nat.succ_pos k⟩
  let L' := observationLength c'
  have : Fact (0 < L'.val) := ⟨L'.property⟩
  have hlarge : 4*R ≤ L'.val := (le_inv_comm₀ (by linarith) c'.property.1).mpr hk.le
  obtain ⟨ψ', hc', hψ', hf', _, _, _, hp'⟩ := hbase L' _
    (hfamily ⟨k+1, Nat.succ_pos k⟩).1 (hfamily ⟨k+1, Nat.succ_pos k⟩).2
  let L := observationLength c
  have : Fact (0 < L.val) := ⟨L.property⟩
  have hL : 1 ≤ L.val := (one_le_inv₀ c.property.1).mpr c.property.2
  obtain ⟨ψ, hc, hψ, hf⟩ := exists_continuous_transport_of_primitiveRegularity P L η B hη hB _ hprim
  obtain ⟨hdiff, hdiffbound⟩ := hcompare c c' ψ ψ' hc hc' hψ hψ' hf hf'
  have hbdist (x : ℝ) (hx : |x| < σ) (i : Fin (n : ℕ)) :
      dist (x : Circle L') (a i : Circle L') = |x-a i| := by
    apply CircleSingularity.dist_coe_eq_abs_sub L'.property
    exact (abs_sub x (a i)).trans ((add_le_add hx.le (haR i)).trans (by linarith))
  have hinner (x : ℝ) (hx : |x| < σ)
      (hxm : ∀ j, (x : Circle L) ≠ (b j : Circle L)) :
      ContDiffAt ℝ 2 (fun t : ℝ => ψ (t : Circle L)) x ∧
      |deriv (deriv (fun t : ℝ => ψ (t : Circle L))) x| ≤
        (J*A+D*(n : ℝ))*(∑ j, dist (x : Circle L) (b j : Circle L)^e) := by
    exact regMicro_marks_inner_comparison L L' n m a b σ q e D (Q 2)
      (by linarith) hσq he hD.le (hQ 2).le hcover hbdist ψ ψ'
      hp' hdiff (hdiffbound 2) x hx hxm
  refine ⟨?_, ⟨ψ, hψ⟩, hf, fun x hxm => ?_⟩
  · intro i j hij
    change (b i : Circle L) = (b j : Circle L) at hij
    by_contra hne
    have hh := hsep L.val hL i j hne
    rw [hij, dist_self] at hh
    linarith
  let y := centralRep L (x : Circle L)
  have hyx : (y : Circle L) = (x : Circle L) := AddCircle.coe_equivIco
  have hym : ∀ j, (y : Circle L) ≠ (b j : Circle L) := by simpa only [hyx] using hxm
  have hyL : |y| ≤ L.val/2 := by
    have hh := centralRep_mem_Ico L (x : Circle L)
    exact abs_le.mpr ⟨hh.1, hh.2.le⟩
  have hdist : dist (x : Circle L) 0 = |y| := by
    rw [← hyx]
    simpa only [AddCircle.coe_zero, sub_zero] using
      CircleSingularity.dist_coe_eq_abs_sub L.property (x := y) (y := 0) (by simpa using hyL)
  have hlocal : ContDiffAt ℝ 2 (fun t : ℝ => ψ (t : Circle L)) y ∧
      |deriv (deriv (fun t : ℝ => ψ (t : Circle L))) y| ≤ C *
        ((if |y| ≤ 1 then ∑ j, dist (y : Circle L) (b j : Circle L)^e else 0)+
         (if 1 ≤ |y| then |y|^(P.val.2-3) else 0)) := by
    by_cases hyσ : |y| < σ
    · obtain ⟨hs, hv⟩ := hinner y hyσ hym
      refine ⟨hs, ?_⟩
      rw [ite_eq_left (by linarith : |y| ≤ 1), ite_eq_right (by linarith : ¬1 ≤ |y|), add_zero]
      exact hv.trans (mul_le_mul_of_nonneg_right hJC (by positivity))
    · have hyσ' : σ ≤ |y| := le_of_not_gt hyσ
      have ho := hoff p c ψ hc hψ hf r (σ-r) y hr (hrq.trans hq)
        (by linarith) hsupp (by linarith) hyL
      have hEbound : |deriv (deriv (fun t : ℝ => ψ (t : Circle L))) y| ≤ E := by
        simpa only [iteratedDeriv_succ, iteratedDeriv_zero, Real.norm_eq_abs, Nat.cast_ofNat,
          show P.val.2-1-2 = P.val.2-3 by ring] using ho.2
      refine ⟨ho.1.of_le (by simp), ?_⟩
      by_cases hy1 : |y| ≤ 1
      · have hone := inner_mark_power_sum L m b he (by rw [hyx, hdist]; exact hy1) hym
        change 1 ≤ A*(∑ j, dist (y : Circle L) (b j : Circle L)^e) at hone
        have hh := mul_le_mul_of_nonneg_left hone hE
        have hmass : 0 ≤ ∑ j, dist (y : Circle L) (b j : Circle L)^e := by positivity
        rw [ite_eq_left hy1]
        split_ifs
        all_goals nlinarith [mul_le_mul_of_nonneg_right hEC hmass,
          mul_nonneg hC.le (Real.rpow_nonneg (abs_nonneg y) (P.val.2-3))]
      · have hy1' : 1 ≤ dist (y : Circle L) 0 := by rw [hyx, hdist]; exact (le_of_not_ge hy1)
        have ht := (htail c ψ hc hψ hf y (by linarith)).2
        rw [hyx, hdist] at ht
        rw [ite_eq_right hy1, ite_eq_left (le_of_not_ge hy1), zero_add]
        exact ht.trans (mul_le_mul_of_nonneg_right hUC (by positivity))
  have hs := contDiffAt_circle_lift_of_coe_eq ψ hyx hlocal.1
  have hv := hlocal.2
  rw [deriv_deriv_circle_lift_eq_of_coe_eq ψ hyx, hyx, ← hdist] at hv
  exact ⟨hs, by simpa only [e, show P.val.2-3 = -3+P.val.2 by ring] using hv⟩

end Riesz1.Internal
