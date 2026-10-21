/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.RegMicroUniformBounded
public import Riesz1.Variance.RegMicroFinalFixed

/-!
# Uniform compact assembly with a separated marked set

This internal assembly of Lemma 5.3 isolates the geometric
mark-removal obligation. Its sole additional hypothesis is uniform separation
of the actual marked set. The coefficient precedes every scale sequence
and particle number. Endpoints and bounded `K` are included.
-/

public section

open MeasureTheory Set Filter
open scoped Topology

namespace Riesz1.Internal

/-- Complete compact assembly once the marked set has uniform
separation. This is an internal helper, not the final theorem for Lemma 5.3.
Discarding the smooth exterior marks remains an independent geometric and
transport-regularity obligation. -/
theorem regMicro_compact_of_uniform_separation
    (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (P : Parameters) (p : Profile) (hp : CompactProfile p)
    (α η B C₀ : ℝ) (n : ℕ+) (a : Fin (n : ℕ) → ℝ)
    (hα0 : P.val.2-1 ≤ α) (hα1 : α < P.val.2/2)
    (hη : 0 < η) (hB : 0 ≤ B) (hC₀ : 0 ≤ C₀)
    (δ : ℝ) (hδ : 0 < δ)
    (hsep : ∀ (b : Scale),
      TransportRegularity P (observationLength b)
        ⟨periodizedProfile p (observationLength b), periodizedProfileL2 p b⟩ n a α C₀ →
      ∀ i j, i ≠ j → δ ≤ dist (a i : Circle (observationLength b))
        (a j : Circle (observationLength b)))
    (ρ : ℝ → ℝ) (hρ : IsMollifier ρ) (ε : ℝ) (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ (ell : Scales),
      Tendsto (fun k : ℕ => (ell ⟨k+1, Nat.succ_pos k⟩).val) atTop (𝓝 0) →
      (∀ N, PrimitiveRegularity (observationLength (ell N)) η P.val.2 B
          ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ ∧
        TransportRegularity P (observationLength (ell N))
          ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩
          n a α C₀) →
      ∀ N : ℕ+, 1 ≤ cltK N (ell N) →
        let f := (⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ :
          {f : Circle (loopMasterLength (ell N)) → ℝ //
            MemLp (fun z => (f z : ℂ)) 2 (arclength (loopMasterLength (ell N)))})
        ∃ hE : MemLp (mixedStat P N (ell N) (subCircleL2 f (mixedReg hρ N (ell N) f))) 2
          (gibbsMeasure P N),
          variance (gibbsMeasure P N) _ (hE.integrable one_le_two) ≤
            ENNReal.ofReal (D*cltK N (ell N)^ε*
              (cltK N (ell N)^(2*α)+cltK N (ell N)^(3*P.val.2-2))) := by
  obtain ⟨α', hα'0, hα'1, hαα', hα'ne, hloss⟩ :=
    regMicro_interior_exponent hα0 hα1 hε
  let C₀' := C₀*(1+∑ j, |a j|)^(α'-α)
  have hC₀' : 0 ≤ C₀' := by dsimp [C₀']; positivity
  obtain ⟨C, H, R, hC, hH, _hR, _hRhalf, _hsupp, hkernel⟩ :=
    regMicroKernel_complete_compact P ρ hρ p hp η B n a α' C₀'
      hη hB hC₀' hα'0 hα'1
  let r₀ := min (δ/8) (1/16)
  have hr₀ : 0 < r₀ := lt_min (by linarith) (by norm_num)
  have hr₀small : r₀ < 1/8 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  obtain ⟨Dsmall, hDsmall, hsmall⟩ := regMicro_small_radius_of_kernel hBE hPL P α' (ε/2)
    hα'0.le hα'1 hα'ne (by linarith) n η B C₀' hη hB hC₀' ρ hρ C H r₀ 2
      hC.le hr₀ hr₀small
  let H' := min H (min (r₀/8) 1)
  have hH' : 0 < H' := lt_min hH (lt_min (by linarith) zero_lt_one)
  let K₀ := max 1 H'⁻¹
  obtain ⟨Db, hDb, hb⟩ := reg_micro_bounded_K P p K₀ α ε (le_max_left _ _) hε.le
  refine ⟨Dsmall+Db, add_pos hDsmall hDb, fun ell hell hfamily N hK => ?_⟩
  let b := ell N
  let L := observationLength b
  let f := (⟨periodizedProfile p L, periodizedProfileL2 p b⟩ :
      {f : Circle L → ℝ // MemLp (fun z => (f z : ℂ)) 2 (arclength L)})
  let K := cltK N b
  have hK0 : 0 < K := cltK_pos N b
  have hfamily' : ∀ M, PrimitiveRegularity (observationLength (ell M)) η P.val.2 B
        ⟨periodizedProfile p (observationLength (ell M)), periodizedProfileL2 p (ell M)⟩ ∧
      TransportRegularity P (observationLength (ell M))
        ⟨periodizedProfile p (observationLength (ell M)), periodizedProfileL2 p (ell M)⟩
        n a α' C₀' := fun M => ⟨(hfamily M).1,
          transportRegularity_increase_exponent P _ _ n a hαα' hC₀ (hfamily M).2⟩
  have hsep' : ∀ i j, i ≠ j → 4*r₀ ≤ dist (a i : Circle L) (a j : Circle L) := by
    intro i j hij
    have hh : r₀ ≤ δ/8 := min_le_left _ _
    exact (by linarith : 4*r₀ ≤ δ).trans (hsep b (hfamily N).2 i j hij)
  have hR : 0 ≤ K^ε*(K^(2*α)+K^(3*P.val.2-2)) := by positivity
  by_cases hh : K⁻¹ ≤ H'
  · have hsupp : ∀ᵐ z ∂arclength L, 2 ≤ dist z 0 →
        f.val z-cltRegCircle hρ L (inv_pos.mpr hK0) f z = 0 := by
      have hs := regMicro_periodized_error_support p b hρ (inv_pos.mpr hK0)
        (inv_le_one_of_one_le₀ hK)
      filter_upwards [hs] with z hz hd
      exact hz (by linarith)
    obtain ⟨hE, hv⟩ := hsmall N b hK a hsep' f (hfamily' N).1 (hfamily' N).2
      (hkernel ell hell hfamily' b (hfamily' N).1 (hfamily' N).2)
      (hh.trans (min_le_left _ _))
      (hh.trans ((min_le_right _ _).trans (min_le_left _ _))) (Or.inr hsupp)
    refine ⟨hE, hv.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    have hp : K^(ε/2)*(K^(2*α')+K^(3*P.val.2-2)) ≤
        K^ε*(K^(2*α)+K^(3*P.val.2-2)) := by
      have ht := regMicro_endpoint_rate (s := P.val.2) (α := α)
        (δ := α'-α) hK hloss hε.le
      simpa only [add_sub_cancel] using ht
    calc
      _ ≤ Dsmall*(K^ε*(K^(2*α)+K^(3*P.val.2-2))) := by
        simpa only [K, cltK, mul_assoc] using mul_le_mul_of_nonneg_left hp hDsmall.le
      _ ≤ (Dsmall+Db)*(K^ε*(K^(2*α)+K^(3*P.val.2-2))) :=
        mul_le_mul_of_nonneg_right (by linarith) hR
      _ = _ := by ring
  · have hKK : K ≤ K₀ := by
      have hinv : H' < K⁻¹ := lt_of_not_ge hh
      have hk : K < H'⁻¹ := (lt_inv_comm₀ hK0 hH').mpr hinv
      exact hk.le.trans (le_max_right _ _)
    obtain ⟨hE, hv⟩ := hb hPL ρ hρ N b hK hKK
    refine ⟨hE, hv.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    nlinarith [mul_nonneg hDsmall.le hR]

end Riesz1.Internal
