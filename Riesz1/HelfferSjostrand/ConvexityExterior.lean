/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.BlockEnergies
public import Riesz1.HelfferSjostrand.ConvexityPolytopeLocal
public import Riesz1.Frozen.External.PrekopaLeindler
public import Riesz1.ToMathlib.LogConcave.ConvexDistributionalHessian

/-!
# Convexity and translation invariance of the block energy (Lemma 3.7)

For a pair Hamiltonian `χ` and a block decomposition `e : Fin m ⊕ Fin n ≃ Fin N` with label `1`
retained, the block energy `H̃` of `BlockEnergies.lean` is convex on the retained chamber, is
invariant under common real translations of the retained lifts, and satisfies `D²H̃ ≥ 0`
distributionally. The only external input is the Prékopa–Leindler inequality `External.PrekopaLeindler`, passed
as an explicit hypothesis `hPL`. The density identity is in `ConvexityExteriorDensity.lean`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter

namespace Riesz1

variable {N : ℕ+} {c : ℝ} {m n : ℕ}

/-- The fibers over the retained chamber have finite and positive exponential integrals. -/
theorem fiber_integrable_pos (hPL : External.PrekopaLeindler) (χ : HsPairPotentials N c)
    (hc : 0 < c) (e : Fin m ⊕ Fin n ≃ Fin (N : ℕ)) (hmono : StrictMono fun a => e (Sum.inl a))
    (hm : 0 < m) (he0 : e (Sum.inl ⟨0, hm⟩) = ⟨0, N.pos⟩) {z : EuclideanSpace ℝ (Fin m)}
    (hz : z ∈ retainedChamber m) :
    IntegrableOn (fun y => Real.exp (-blockExteriorEnergy χ e (z, y)))
        {y | blockLift e (z, y) ∈ hsChamber N} ∧
      0 < ∫ y in {y | blockLift e (z, y) ∈ hsChamber N},
        Real.exp (-blockExteriorEnergy χ e (z, y)) := by
  by_cases hn : n = 0
  · subst hn
    obtain ⟨y0, hy0⟩ := exists_lift_of_mem_retainedChamber e hmono hm he0 hz
    have hsub : ∀ y y' : EuclideanSpace ℝ (Fin 0), y = y' :=
      fun _ _ => PiLp.ext fun i => Fin.elim0 i
    have hfib : {y : EuclideanSpace ℝ (Fin 0) | blockLift e (z, y) ∈ hsChamber N} = univ :=
      Set.eq_univ_of_forall fun y => by
        show blockLift e (z, y) ∈ hsChamber N
        rw [hsub y y0]
        exact hy0
    have hl : ∀ s : Fin m ⊕ Fin 0, s.isLeft = true := by
      rintro (a | b)
      · rfl
      · exact Fin.elim0 b
    have hV : ∀ y : EuclideanSpace ℝ (Fin 0), blockExteriorEnergy χ e (z, y) = 0 := by
      intro y
      have hmix : mixedPairs e = ∅ := by
        rw [mixedPairs, Finset.filter_eq_empty_iff]
        intro ij _ h
        exact h.2 ⟨hl _, hl _⟩
      rw [blockExteriorEnergy_eq_mixed χ e hmono, hmix]
      simp
    rw [hfib]
    simp only [hV, neg_zero, Real.exp_zero]
    refine ⟨integrableOn_const (by simp [volume_univ_fin_zero]), ?_⟩
    rw [setIntegral_const, Measure.real, volume_univ_fin_zero]
    simp
  · have hn' : 0 < n := Nat.pos_of_ne_zero hn
    have h := convexity_exterior_polytope_local hPL hn' (liftChamber e) (isOpen_liftChamber e)
      (convex_liftChamber e) (fun _ _ => exists_nhds_bounded_liftChamber e hm he0)
      (blockExteriorEnergy χ e) (convexOn_exteriorEnergy χ hc e hmono)
    have hz' : z ∈ Prod.fst '' liftChamber e := by
      rw [fst_image_liftChamber e hmono hm he0]
      exact hz
    exact h.1 z hz'

/-- The block energy is convex on the retained chamber (Lemma 3.7). -/
theorem convexOn_blockTilde (hPL : External.PrekopaLeindler) (χ : HsPairPotentials N c)
    (hc : 0 < c) (e : Fin m ⊕ Fin n ≃ Fin (N : ℕ)) (hmono : StrictMono fun a => e (Sum.inl a))
    (hm : 0 < m) (he0 : e (Sum.inl ⟨0, hm⟩) = ⟨0, N.pos⟩) :
    ConvexOn ℝ (retainedChamber m) (blockTilde χ e) := by
  by_cases hn : n = 0
  · exact convexOn_blockTilde_of_isEmpty χ e hmono hm he0 hn
  · have hn' : 0 < n := Nat.pos_of_ne_zero hn
    have h := convexity_exterior_polytope_local hPL hn' (liftChamber e) (isOpen_liftChamber e)
      (convex_liftChamber e) (fun _ _ => exists_nhds_bounded_liftChamber e hm he0)
      (blockExteriorEnergy χ e) (convexOn_exteriorEnergy χ hc e hmono)
    rw [fst_image_liftChamber e hmono hm he0] at h
    exact h.2

/-- For `m = N` the block energy vanishes on the retained chamber. -/
theorem blockTilde_eq_zero_of_eq_card (χ : HsPairPotentials N c)
    (e : Fin m ⊕ Fin n ≃ Fin (N : ℕ)) (hmono : StrictMono fun a => e (Sum.inl a))
    (hm : 0 < m) (he0 : e (Sum.inl ⟨0, hm⟩) = ⟨0, N.pos⟩) (hmN : m = (N : ℕ))
    {z : EuclideanSpace ℝ (Fin m)} (hz : z ∈ retainedChamber m) : blockTilde χ e z = 0 := by
  have hn : n = 0 := by
    have := card_add_of_block e
    omega
  exact blockTilde_eq_zero_of_isEmpty χ e hmono hm he0 hn hz

/-! ### Translation invariance along the diagonal -/

/-- The constant vector with all entries equal to `t`. -/
def constVec (k : ℕ) (t : ℝ) : EuclideanSpace ℝ (Fin k) := WithLp.toLp 2 (fun _ => t)

theorem constVec_apply (k : ℕ) (t : ℝ) (i : Fin k) : constVec k t i = t := rfl

theorem blockLift_translate (e : Fin m ⊕ Fin n ≃ Fin (N : ℕ)) (z : EuclideanSpace ℝ (Fin m))
    (y : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    blockLift e (z + constVec m t, y + constVec n t) = hsTranslate t (blockLift e (z, y)) := by
  ext i
  obtain ⟨s, rfl⟩ := e.surjective i
  rw [blockLift_apply, Equiv.symm_apply_apply, hsTranslate_apply, blockLift_apply,
    Equiv.symm_apply_apply]
  cases s with
  | inl a => simp [constVec_apply]
  | inr b => simp [constVec_apply]

theorem blockExteriorEnergy_translate (χ : HsPairPotentials N c)
    (e : Fin m ⊕ Fin n ≃ Fin (N : ℕ)) (z : EuclideanSpace ℝ (Fin m))
    (y : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    blockExteriorEnergy χ e (z + constVec m t, y + constVec n t) = blockExteriorEnergy χ e (z, y) := by
  have hd : ∀ a b : Fin m, (z + constVec m t) b - (z + constVec m t) a = z b - z a :=
    fun a b => by simp [constVec_apply]
  unfold blockExteriorEnergy
  simp only [blockLift_translate, hsPairExpression_translate, blockRetainedEnergy, hd]

theorem add_constVec_mem_retainedChamber {z : EuclideanSpace ℝ (Fin m)}
    (hz : z ∈ retainedChamber m) (t : ℝ) : z + constVec m t ∈ retainedChamber m := by
  obtain ⟨hs, hb⟩ := hz
  refine ⟨fun a b hab => ?_, fun a b => ?_⟩
  · simp only [PiLp.add_apply, constVec_apply]
    linarith [hs hab]
  · simp only [PiLp.add_apply, constVec_apply]
    linarith [hb a b]

/-- The block energy is invariant under common real translations of the retained lifts. -/
theorem blockTilde_translate (χ : HsPairPotentials N c) (e : Fin m ⊕ Fin n ≃ Fin (N : ℕ))
    (z : EuclideanSpace ℝ (Fin m)) (t : ℝ) :
    blockTilde χ e (z + constVec m t) = blockTilde χ e z := by
  unfold blockTilde
  congr 2
  have hm1 : MeasurableSet {y : EuclideanSpace ℝ (Fin n) |
      blockLift e (z + constVec m t, y) ∈ hsChamber N} :=
    (isOpen_fiber e (z + constVec m t)).measurableSet
  have hm2 : MeasurableSet {y : EuclideanSpace ℝ (Fin n) | blockLift e (z, y) ∈ hsChamber N} :=
    (isOpen_fiber e z).measurableSet
  rw [← integral_indicator hm1, ← integral_indicator hm2]
  rw [← integral_add_right_eq_self
    (fun y => {y | blockLift e (z + constVec m t, y) ∈ hsChamber N}.indicator
      (fun y => Real.exp (-blockExteriorEnergy χ e (z + constVec m t, y))) y) (constVec n t)]
  apply integral_congr_ae
  filter_upwards with y
  by_cases h : blockLift e (z, y) ∈ hsChamber N
  · have hmem : blockLift e (z + constVec m t, y + constVec n t) ∈ hsChamber N := by
      rw [blockLift_translate]
      exact (hsTranslate_mem_chamber_iff t _).2 h
    simp only [Set.indicator, mem_ofPred_eq, hmem, h, ite_true]
    rw [blockExteriorEnergy_translate]
  · have hmem : blockLift e (z + constVec m t, y + constVec n t) ∉ hsChamber N := by
      rw [blockLift_translate]
      exact fun h' => h ((hsTranslate_mem_chamber_iff t _).1 h')
    simp only [Set.indicator, mem_ofPred_eq, hmem, h, ite_false]

/-! ### Distributional Hessian -/

/-- The block energy has a nonnegative distributional Hessian on the retained chamber. -/
theorem blockTilde_distributional_hessian (hPL : External.PrekopaLeindler)
    (χ : HsPairPotentials N c) (hc : 0 < c) (e : Fin m ⊕ Fin n ≃ Fin (N : ℕ))
    (hmono : StrictMono fun a => e (Sum.inl a)) (hm : 0 < m)
    (he0 : e (Sum.inl ⟨0, hm⟩) = ⟨0, N.pos⟩) {φ : EuclideanSpace ℝ (Fin m) → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ retainedChamber m)
    (hφ0 : ∀ z, 0 ≤ φ z) (b : EuclideanSpace ℝ (Fin m)) :
    0 ≤ ∫ z, blockTilde χ e z * fderiv ℝ (fderiv ℝ φ) z b b :=
  convexOn_distributional_hessian_nonneg (isOpen_retainedChamber m) (convex_retainedChamber m)
    (convexOn_blockTilde hPL χ hc e hmono hm he0) hφ hφc hφU hφ0 b

end Riesz1

end
end
