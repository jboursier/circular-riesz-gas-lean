/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.SettingHamiltonian
public import Riesz1.ToMathlib.LogConcave.BlockLiftMeasure

/-!
# Interior and exterior block energies

A block decomposition `e : Fin m ⊕ Fin n ≃ Fin N` splits the `N` labels of a pair Hamiltonian
`χ` into `m` retained labels `e (inl a)` and `n` exterior labels `e (inr b)`. The lift of a pair
`(z, y)` is `blockLift e (z, y)`. The retained labels are listed in increasing order, and label
`1` (index `0`) is retained. This is the normalization `1 ∈ I`.

This file defines the retained energy `H₁`, the exterior energy `H₂ = H - H₁` and the block
energy `H̃`. It proves the basic claims about these energies, and the convexity inputs of
Lemma 3.7. The density and translation claims are in `ConvexityExterior.lean`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Finset
open scoped Topology

namespace Riesz1

variable {N : ℕ+} {c : ℝ} {m n : ℕ}

/-- The chamber of retained lifts `z_{i₁} < ⋯ < z_{i_m} < z_{i₁} + 1`. For `m = 1` it is `ℝ`. -/
def retainedChamber (m : ℕ) : Set (EuclideanSpace ℝ (Fin m)) :=
  {z | StrictMono z ∧ ∀ a b, z b < z a + 1}

/-- The retained energy `H₁(z) = 2 ∑_{a<b} χ_{ab}(z_b - z_a)` over the retained labels. -/
def blockRetainedEnergy (χ : HsPairPotentials N c) (e : Fin m ⊕ Fin n ≃ Fin (N : ℕ))
    (z : EuclideanSpace ℝ (Fin m)) : ℝ :=
  2 * ∑ a : Fin m, ∑ b ∈ univ.filter (a < ·),
    χ.potential (e (Sum.inl a)) (e (Sum.inl b)) (z b - z a)

/-- The exterior energy `H₂ = H - H₁`, evaluated at the lift `(z, y)`. -/
def blockExteriorEnergy (χ : HsPairPotentials N c) (e : Fin m ⊕ Fin n ≃ Fin (N : ℕ))
    (p : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) : ℝ :=
  hsPairExpression χ (blockLift e p) - blockRetainedEnergy χ e p.1

/-- The block energy `H̃(z) = -log ∫ e^{-H₂(z,y)} dy`, where `y` runs over the fiber of the
lifted chamber above `z`. Its carrier is `retainedChamber m`. Off the carrier the fiber is empty,
and the value is Lean's junk value `0`. The claims below concern the carrier only. -/
def blockTilde (χ : HsPairPotentials N c) (e : Fin m ⊕ Fin n ≃ Fin (N : ℕ))
    (z : EuclideanSpace ℝ (Fin m)) : ℝ :=
  -Real.log (∫ y in {y | blockLift e (z, y) ∈ hsChamber N},
    Real.exp (-blockExteriorEnergy χ e (z, y)))

/-! ### Convexity and continuity of the lifted chamber -/

theorem continuous_blockLift {m n N : ℕ} (e : Fin m ⊕ Fin n ≃ Fin N) :
    Continuous (blockLift e) := by
  have key : ∀ s : Fin m ⊕ Fin n, Continuous fun p :
      EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n) =>
        Sum.elim (fun a => p.1 a) (fun b => p.2 b) s := by
    intro s
    cases s with
    | inl a => exact (PiLp.continuous_apply 2 _ a).comp continuous_fst
    | inr b => exact (PiLp.continuous_apply 2 _ b).comp continuous_snd
  unfold blockLift
  exact (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => key (e.symm i))

theorem blockLift_inl {m n N : ℕ} (e : Fin m ⊕ Fin n ≃ Fin N)
    (p : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) (a : Fin m) :
    blockLift e p (e (Sum.inl a)) = p.1 a := by
  rw [blockLift_apply, Equiv.symm_apply_apply, Sum.elim_inl]

theorem blockLift_inr {m n N : ℕ} (e : Fin m ⊕ Fin n ≃ Fin N)
    (p : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) (b : Fin n) :
    blockLift e p (e (Sum.inr b)) = p.2 b := by
  rw [blockLift_apply, Equiv.symm_apply_apply, Sum.elim_inr]

/-! ### The mixed pairs and the splitting of `H` -/

/-- The label pairs `i < j` with at least one exterior label. These index the terms of `H₂`. -/
def mixedPairs (e : Fin m ⊕ Fin n ≃ Fin (N : ℕ)) :
    Finset (Fin (N : ℕ) × Fin (N : ℕ)) :=
  univ.filter fun ij => ij.1 < ij.2 ∧
    ¬((e.symm ij.1).isLeft = true ∧ (e.symm ij.2).isLeft = true)

/-- Reindexing a double sum over labels by the block bijection. -/
theorem sum_sum_eq_block {m n N : ℕ} (e : Fin m ⊕ Fin n ≃ Fin N) (F : Fin N → Fin N → ℝ) :
    ∑ i, ∑ j, F i j = ∑ s : Fin m ⊕ Fin n, ∑ t : Fin m ⊕ Fin n, F (e s) (e t) := by
  calc ∑ i, ∑ j, F i j = ∑ s, ∑ j, F (e s) j := (Equiv.sum_comp e _).symm
    _ = _ := Finset.sum_congr rfl fun s _ => (Equiv.sum_comp e _).symm

/-- The energy `H₂` is the sum over the mixed pairs. -/
theorem blockExteriorEnergy_eq_mixed (χ : HsPairPotentials N c)
    (e : Fin m ⊕ Fin n ≃ Fin (N : ℕ)) (hmono : StrictMono fun a => e (Sum.inl a))
    (p : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) :
    blockExteriorEnergy χ e p =
      2 * ∑ ij ∈ mixedPairs e, χ.potential ij.1 ij.2 (blockLift e p ij.2 - blockLift e p ij.1) := by
  set x := blockLift e p with hx
  set T : Fin (N : ℕ) → Fin (N : ℕ) → ℝ := fun i j => χ.potential i j (x j - x i) with hT
  set Fi : Fin (N : ℕ) → Fin (N : ℕ) → ℝ := fun i j => if i < j then T i j else 0 with hFi
  set Gc : Fin (N : ℕ) → Fin (N : ℕ) → ℝ := fun i j =>
    if (e.symm i).isLeft = true ∧ (e.symm j).isLeft = true ∧ i < j then T i j else 0 with hGc
  have hfull : hsPairExpression χ x = 2 * ∑ i, ∑ j, Fi i j := by
    unfold hsPairExpression
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Finset.sum_filter, hFi]
    rfl
  have hret : blockRetainedEnergy χ e p.1 = 2 * ∑ i, ∑ j, Gc i j := by
    unfold blockRetainedEnergy
    congr 1
    rw [sum_sum_eq_block e Gc]
    simp only [Finset.sum_filter, Fintype.sum_sum_type, hGc, Equiv.symm_apply_apply,
      Sum.isLeft_inl, Sum.isLeft_inr, Bool.false_eq_true, false_and, and_false, ite_false,
      Finset.sum_const_zero, add_zero, true_and]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    by_cases hab : a < b
    · have hlt : e (Sum.inl a) < e (Sum.inl b) := hmono hab
      simp [hT, hx, hab, hlt, blockLift_inl]
    · have hlt : ¬ e (Sum.inl a) < e (Sum.inl b) := fun h => hab (hmono.lt_iff_lt.1 h)
      simp [hab, hlt]
  have hpt : ∀ ij : Fin (N : ℕ) × Fin (N : ℕ),
      Fi ij.1 ij.2 - Gc ij.1 ij.2 = if ij.1 < ij.2 ∧
        ¬((e.symm ij.1).isLeft = true ∧ (e.symm ij.2).isLeft = true) then T ij.1 ij.2 else 0 := by
    rintro ⟨i, j⟩
    by_cases h1 : i < j <;> by_cases h2 : (e.symm i).isLeft = true ∧ (e.symm j).isLeft = true <;>
      simp [hFi, hGc, h1, h2]
  have hsum : ∑ i, ∑ j, Fi i j - ∑ i, ∑ j, Gc i j = ∑ ij ∈ mixedPairs e, T ij.1 ij.2 := by
    rw [← Fintype.sum_prod_type' (fun i j => Fi i j), ← Fintype.sum_prod_type' (fun i j => Gc i j),
      ← Finset.sum_sub_distrib, mixedPairs, Finset.sum_filter]
    exact Finset.sum_congr rfl fun ij _ => hpt ij
  rw [blockExteriorEnergy, hfull, hret, ← mul_sub, hsum]

/-! ### Convexity of the exterior energy on the lifted chamber -/

/-- The lifted chamber, as a subset of the retained-exterior product. -/
def liftChamber (e : Fin m ⊕ Fin n ≃ Fin (N : ℕ)) :
    Set (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) :=
  blockLift e ⁻¹' hsChamber N

theorem isOpen_liftChamber (e : Fin m ⊕ Fin n ≃ Fin (N : ℕ)) : IsOpen (liftChamber e) :=
  (isOpen_hsChamber N).preimage (continuous_blockLift e)

theorem convex_liftChamber (e : Fin m ⊕ Fin n ≃ Fin (N : ℕ)) : Convex ℝ (liftChamber e) := by
  intro p hp q hq a b ha hb hab
  show blockLift e (a • p + b • q) ∈ hsChamber N
  rw [blockLift_add, blockLift_smul, blockLift_smul]
  exact convex_hsChamber N hp hq ha hb hab

/-- A single pair term of `H₂` is convex on the lifted chamber. -/
theorem convexOn_pairTerm (χ : HsPairPotentials N c) (hc : 0 < c)
    (e : Fin m ⊕ Fin n ≃ Fin (N : ℕ)) {i j : Fin (N : ℕ)} (hij : i < j) :
    ConvexOn ℝ (liftChamber e) (fun p => χ.potential i j (blockLift e p j - blockLift e p i)) := by
  refine ⟨convex_liftChamber e, fun p hp q hq a b ha hb hab => ?_⟩
  have hp' := hsChamber_separation_mem hp hij
  have hq' := hsChamber_separation_mem hq hij
  have hcomb : blockLift e (a • p + b • q) j - blockLift e (a • p + b • q) i =
      a * (blockLift e p j - blockLift e p i) + b * (blockLift e q j - blockLift e q i) := by
    rw [blockLift_add, blockLift_smul, blockLift_smul]
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  have hconv := (χ.convex hc i j hij).2 hp' hq' ha hb hab
  dsimp only
  rw [hcomb, smul_eq_mul, smul_eq_mul]
  exact hconv

/-- Finite sums of convex functions are convex. -/
theorem convexOn_finset_sum' {ι E : Type*} [AddCommGroup E] [Module ℝ E] {S : Set E}
    (hS : Convex ℝ S) (s : Finset ι) (f : ι → E → ℝ) (hf : ∀ i ∈ s, ConvexOn ℝ S (f i)) :
    ConvexOn ℝ S (fun p => ∑ i ∈ s, f i p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using convexOn_const (0 : ℝ) hS
  | insert k s hk ih =>
    have h1 := hf k (Finset.mem_insert_self k s)
    have h2 := ih fun i hi => hf i (Finset.mem_insert_of_mem hi)
    simp only [Finset.sum_insert hk]
    exact h1.add h2

/-- The exterior energy `H₂` is convex on the lifted chamber. -/
theorem convexOn_exteriorEnergy (χ : HsPairPotentials N c) (hc : 0 < c)
    (e : Fin m ⊕ Fin n ≃ Fin (N : ℕ)) (hmono : StrictMono fun a => e (Sum.inl a)) :
    ConvexOn ℝ (liftChamber e) (blockExteriorEnergy χ e) := by
  have hfun : blockExteriorEnergy χ e = fun p => 2 * ∑ ij ∈ mixedPairs e,
      χ.potential ij.1 ij.2 (blockLift e p ij.2 - blockLift e p ij.1) :=
    funext fun p => blockExteriorEnergy_eq_mixed χ e hmono p
  rw [hfun]
  have hsum := convexOn_finset_sum' (convex_liftChamber e) (mixedPairs e)
    (fun ij p => χ.potential ij.1 ij.2 (blockLift e p ij.2 - blockLift e p ij.1))
    fun ij hij => convexOn_pairTerm χ hc e (Finset.mem_filter.1 hij).2.1
  have h2 := hsum.smul (c := (2 : ℝ)) (by norm_num)
  simpa only [smul_eq_mul, Finset.mul_sum] using h2

/-! ### The retained chamber and the lift of its points -/

theorem exists_gap_scale (N : ℕ) {m : ℕ} (w : Fin m → ℝ) (top : ℝ)
    (hw : ∀ a b, a < b → w a < w b) (htop : ∀ a, w a < top) :
    ∃ η : ℝ, 0 < η ∧ (∀ a b, a < b → (N : ℝ) * η ≤ w b - w a) ∧
      ∀ a, (N : ℝ) * η ≤ top - w a := by
  have key : ∀ d : ℝ, 0 < d → ∀ᶠ η in 𝓝 (0 : ℝ), (N : ℝ) * η < d := by
    intro d hd
    have ht : Tendsto (fun η : ℝ => (N : ℝ) * η) (𝓝 0) (𝓝 ((N : ℝ) * 0)) :=
      (continuous_const.mul continuous_id).tendsto 0
    rw [mul_zero] at ht
    exact ht.eventually (gt_mem_nhds hd)
  have hall : ∀ᶠ η in 𝓝 (0 : ℝ),
      (∀ a b, a < b → (N : ℝ) * η < w b - w a) ∧ ∀ a, (N : ℝ) * η < top - w a := by
    refine Filter.Eventually.and ?_ ?_
    · refine Filter.eventually_all.2 fun a => Filter.eventually_all.2 fun b => ?_
      by_cases hab : a < b
      · exact ((key _ (sub_pos.2 (hw a b hab))).mono fun η hη _ => hη)
      · exact Filter.Eventually.of_forall fun η h => absurd h hab
    · exact Filter.eventually_all.2 fun a => (key _ (sub_pos.2 (htop a))).mono fun η hη => hη
  obtain ⟨η, hη, hη0⟩ := ((hall.filter_mono nhdsWithin_le_nhds).and
    (eventually_mem_nhdsWithin : ∀ᶠ η in 𝓝[>] (0 : ℝ), η ∈ Set.Ioi 0)).exists
  exact ⟨η, hη0, fun a b hab => (hη.1 a b hab).le, fun a => (hη.2 a).le⟩

/-- Every point of the retained chamber has a lift in the lifted chamber. The exterior
coordinates are read off a piecewise-linear configuration, whose value at label `i` is
`i η` plus the largest retained value `z_a - w_a η` with `w_a ≤ i`, where `η > 0` is small. -/
theorem exists_lift_of_mem_retainedChamber (e : Fin m ⊕ Fin n ≃ Fin (N : ℕ))
    (hmono : StrictMono fun a => e (Sum.inl a)) (hm : 0 < m)
    (he0 : e (Sum.inl ⟨0, hm⟩) = ⟨0, N.pos⟩) {z : EuclideanSpace ℝ (Fin m)}
    (hz : z ∈ retainedChamber m) : ∃ y, (z, y) ∈ liftChamber e := by
  obtain ⟨hzmono, hzlt⟩ := hz
  obtain ⟨w, hw⟩ : ∃ w : Fin m → ℕ, ∀ a, w a = (e (Sum.inl a) : ℕ) := ⟨_, fun _ => rfl⟩
  obtain ⟨η, hη, hgap, hgap'⟩ := exists_gap_scale (N : ℕ) (fun a => z a)
    (z ⟨0, hm⟩ + 1) (fun a b hab => hzmono hab) fun a => hzlt ⟨0, hm⟩ a
  have hMne : ∀ i : Fin (N : ℕ), (Finset.univ.filter fun a : Fin m => w a ≤ (i : ℕ)).Nonempty :=
    fun i => ⟨⟨0, hm⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, by simp [hw, he0]⟩⟩
  obtain ⟨M, hM⟩ : ∃ M : Fin (N : ℕ) → ℝ, ∀ i, M i = (Finset.univ.filter fun a : Fin m =>
      w a ≤ (i : ℕ)).sup' (hMne i) (fun a => z a - (w a : ℝ) * η) := ⟨_, fun _ => rfl⟩
  have hMmono : ∀ i j : Fin (N : ℕ), i ≤ j → M i ≤ M j := by
    intro i j hij
    rw [hM i, hM j]
    refine Finset.sup'_le _ _ fun a ha => Finset.le_sup'_of_le _ ?_ le_rfl
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _,
      (Finset.mem_filter.1 ha).2.trans (Fin.le_iff_val_le_val.1 hij)⟩
  have hMret : ∀ b : Fin m, M (e (Sum.inl b)) = z b - (w b : ℝ) * η := by
    intro b
    rw [hM]
    apply le_antisymm
    · refine Finset.sup'_le _ _ fun a ha => ?_
      have hwab : w a ≤ w b := by
        have := (Finset.mem_filter.1 ha).2
        rwa [← hw b] at this
      have hab' : a ≤ b := hmono.le_iff_le.1 (Fin.le_iff_val_le_val.2 (by rw [← hw a, ← hw b]; exact hwab))
      rcases eq_or_lt_of_le hab' with rfl | hlt
      · exact le_rfl
      · have h1 : (N : ℝ) * η ≤ z b - z a := hgap a b hlt
        have hwN : ((w b : ℕ) : ℝ) ≤ N := by
          rw [hw b]; exact_mod_cast (e (Sum.inl b)).isLt.le
        have hwa : (0 : ℝ) ≤ w a := Nat.cast_nonneg _
        have h2 : ((w b : ℝ) - w a) * η ≤ (N : ℝ) * η :=
          mul_le_mul_of_nonneg_right (by linarith) hη.le
        rw [sub_mul] at h2
        linarith
    · exact Finset.le_sup'_of_le (fun a => z a - (w a : ℝ) * η)
        (Finset.mem_filter.2 ⟨Finset.mem_univ b, (hw b).le⟩) le_rfl
  obtain ⟨Xf, hXf⟩ : ∃ f : Fin (N : ℕ) → ℝ, ∀ i, f i = ((i : ℕ) : ℝ) * η + M i :=
    ⟨_, fun _ => rfl⟩
  have hXfret : ∀ a : Fin m, Xf (e (Sum.inl a)) = z a := by
    intro a
    rw [hXf, hMret, ← hw a]
    ring
  have hXfmono : StrictMono Xf := fun i j hij => by
    rw [hXf, hXf]
    exact add_lt_add_of_lt_of_le
      (mul_lt_mul_of_pos_right (by exact_mod_cast Fin.lt_def.1 hij) hη) (hMmono i j hij.le)
  have hXf0 : Xf ⟨0, N.pos⟩ = z ⟨0, hm⟩ := by
    rw [← he0, hXfret]
  have hXfbd : ∀ i, Xf i < Xf ⟨0, N.pos⟩ + 1 := by
    intro i
    obtain ⟨a, _, hMa⟩ := Finset.exists_mem_eq_sup' (hMne i) (fun a => z a - (w a : ℝ) * η)
    have hMi : M i = z a - (w a : ℝ) * η := by rw [hM]; exact hMa
    have hwa : (0 : ℝ) ≤ w a := Nat.cast_nonneg _
    have hiN : ((i : ℕ) : ℝ) - w a < N := by
      have : ((i : ℕ) : ℝ) < N := by exact_mod_cast i.isLt
      linarith
    have h1 : (((i : ℕ) : ℝ) - w a) * η < (N : ℝ) * η := mul_lt_mul_of_pos_right hiN hη
    have e1 : Xf i = z a + (((i : ℕ) : ℝ) - w a) * η := by
      rw [hXf, hMi]; ring
    have hg : (N : ℝ) * η ≤ z ⟨0, hm⟩ + 1 - z a := hgap' a
    rw [hXf0]
    linarith
  refine ⟨WithLp.toLp 2 (fun b => Xf (e (Sum.inr b))), ?_⟩
  have hlift : blockLift e (z, WithLp.toLp 2 (fun b => Xf (e (Sum.inr b)))) =
      WithLp.toLp 2 Xf := by
    ext i
    obtain ⟨s, rfl⟩ := e.surjective i
    rw [blockLift_apply, Equiv.symm_apply_apply]
    cases s with
    | inl a => rw [Sum.elim_inl]; exact (hXfret a).symm
    | inr b => rw [Sum.elim_inr]
  show blockLift e _ ∈ hsChamber N
  rw [hlift]
  exact ⟨hXfmono, hXfbd⟩

/-- The retained chamber is convex. -/
theorem convex_retainedChamber (m : ℕ) : Convex ℝ (retainedChamber m) := by
  intro x hx y hy a b ha hb hab
  have key : ∀ d₁ d₂ : ℝ, 0 < d₁ → 0 < d₂ → 0 < a * d₁ + b * d₂ := by
    intro d₁ d₂ h₁ h₂
    nlinarith [mul_le_mul_of_nonneg_left (min_le_left d₁ d₂) ha,
      mul_le_mul_of_nonneg_left (min_le_right d₁ d₂) hb, lt_min h₁ h₂]
  refine ⟨fun i j hij => ?_, fun i j => ?_⟩
  · have := key _ _ (sub_pos.2 (hx.1 hij)) (sub_pos.2 (hy.1 hij))
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    nlinarith [this]
  · have := key (x i + 1 - x j) (y i + 1 - y j) (by linarith [hx.2 i j]) (by linarith [hy.2 i j])
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    nlinarith [this]

/-- The retained chamber is open. -/
theorem isOpen_retainedChamber (m : ℕ) : IsOpen (retainedChamber m) := by
  have hpair : ∀ ab : Fin m × Fin m,
      IsOpen {z : EuclideanSpace ℝ (Fin m) | ab.1 < ab.2 → z ab.1 < z ab.2} := fun ab => by
    by_cases h : ab.1 < ab.2
    · simp only [h, true_implies]
      exact isOpen_lt (PiLp.continuous_apply 2 _ ab.1) (PiLp.continuous_apply 2 _ ab.2)
    · simp only [h, false_implies]
      exact isOpen_univ
  have hcond : ∀ ab : Fin m × Fin m, IsOpen {z : EuclideanSpace ℝ (Fin m) | z ab.2 < z ab.1 + 1} :=
    fun ab => isOpen_lt (PiLp.continuous_apply 2 _ ab.2)
      ((PiLp.continuous_apply 2 _ ab.1).add continuous_const)
  have h : retainedChamber m =
      (⋂ ab : Fin m × Fin m, {z : EuclideanSpace ℝ (Fin m) | ab.1 < ab.2 → z ab.1 < z ab.2}) ∩
        ⋂ ab : Fin m × Fin m, {z : EuclideanSpace ℝ (Fin m) | z ab.2 < z ab.1 + 1} := by
    ext z
    simp only [retainedChamber, mem_ofPred_eq, mem_inter_iff, mem_iInter]
    constructor
    · rintro ⟨hs, hb⟩
      exact ⟨fun ab hab => hs hab, fun ab => hb ab.1 ab.2⟩
    · rintro ⟨hs, hb⟩
      exact ⟨fun a b hab => hs (a, b) hab, fun a b => hb (a, b)⟩
  rw [h]
  exact (isOpen_iInter_of_finite hpair).inter (isOpen_iInter_of_finite hcond)

/-- Coordinates of a lift are controlled by its first retained coordinate. -/
theorem abs_coord_le_of_mem (e : Fin m ⊕ Fin n ≃ Fin (N : ℕ))
    (hm : 0 < m) (he0 : e (Sum.inl ⟨0, hm⟩) = ⟨0, N.pos⟩)
    {p : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)} (hp : p ∈ liftChamber e) :
    (∀ a, |p.1 a| ≤ |p.1 ⟨0, hm⟩| + 1) ∧ ∀ b, |p.2 b| ≤ |p.1 ⟨0, hm⟩| + 1 := by
  have hp' : blockLift e p ∈ hsChamber N := hp
  have hX0' : blockLift e p ⟨0, N.pos⟩ = p.1 ⟨0, hm⟩ := by rw [← he0, blockLift_inl]
  have hbd : ∀ j, |blockLift e p j| ≤ |blockLift e p ⟨0, N.pos⟩| + 1 := fun j => by
    have hlow : blockLift e p ⟨0, N.pos⟩ ≤ blockLift e p j :=
      hp'.1.monotone (Fin.le_iff_val_le_val.2 (Nat.zero_le _))
    rw [abs_le]
    constructor
    · linarith [neg_abs_le (blockLift e p ⟨0, N.pos⟩), hp'.2 j]
    · linarith [le_abs_self (blockLift e p ⟨0, N.pos⟩), hp'.2 j]
  refine ⟨fun a => ?_, fun b => ?_⟩
  · have := hbd (e (Sum.inl a))
    rwa [blockLift_inl, hX0'] at this
  · have := hbd (e (Sum.inr b))
    rwa [blockLift_inr, hX0'] at this

/-- Coordinate bound for the Euclidean norm. -/
theorem norm_le_of_coord_le {k : ℕ} (y : EuclideanSpace ℝ (Fin k)) {R : ℝ} (hR : 0 ≤ R)
    (h : ∀ i, |y i| ≤ R) : ‖y‖ ≤ ((k : ℝ) + 1) * R := by
  rw [EuclideanSpace.norm_eq]
  have hsum : ∑ i, ‖y i‖ ^ 2 ≤ (((k : ℝ) + 1) * R) ^ 2 := by
    calc ∑ i, ‖y i‖ ^ 2 ≤ ∑ _i : Fin k, R ^ 2 := Finset.sum_le_sum fun i _ => by
          rw [Real.norm_eq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (h i) 2
      _ = (k : ℝ) * R ^ 2 := by simp
      _ ≤ (((k : ℝ) + 1) * R) ^ 2 := by
          nlinarith [sq_nonneg R, hR, (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  calc √(∑ i, ‖y i‖ ^ 2) ≤ √((((k : ℝ) + 1) * R) ^ 2) := Real.sqrt_le_sqrt hsum
    _ = ((k : ℝ) + 1) * R := Real.sqrt_sq (by positivity)

/-- Every fiber of the lifted chamber is bounded. -/
theorem isBounded_fiber (e : Fin m ⊕ Fin n ≃ Fin (N : ℕ)) (hm : 0 < m)
    (he0 : e (Sum.inl ⟨0, hm⟩) = ⟨0, N.pos⟩) (z : EuclideanSpace ℝ (Fin m)) :
    Bornology.IsBounded {y | (z, y) ∈ liftChamber e} := by
  refine isBounded_iff_forall_norm_le.2 ⟨((n : ℝ) + 1) * (|z ⟨0, hm⟩| + 1), fun y hy => ?_⟩
  exact norm_le_of_coord_le y (by positivity)
    (fun b => (abs_coord_le_of_mem e hm he0 hy).2 b)

/-- The fibers of the lifted chamber are open. -/
theorem isOpen_fiber (e : Fin m ⊕ Fin n ≃ Fin (N : ℕ)) (z : EuclideanSpace ℝ (Fin m)) :
    IsOpen {y | (z, y) ∈ liftChamber e} :=
  (isOpen_liftChamber e).preimage (Continuous.prodMk continuous_const continuous_id)

/-- The projection of the lifted chamber is the retained chamber. -/
theorem fst_image_liftChamber (e : Fin m ⊕ Fin n ≃ Fin (N : ℕ))
    (hmono : StrictMono fun a => e (Sum.inl a)) (hm : 0 < m)
    (he0 : e (Sum.inl ⟨0, hm⟩) = ⟨0, N.pos⟩) :
    Prod.fst '' liftChamber e = retainedChamber m := by
  ext z
  constructor
  · rintro ⟨p, hp, rfl⟩
    have hp' : blockLift e p ∈ hsChamber N := hp
    have hsm : StrictMono p.1 := fun a b hab => by
      have h := hp'.1 (hmono hab)
      rwa [blockLift_inl, blockLift_inl] at h
    refine ⟨hsm, fun a b => ?_⟩
    have h1 := hp'.2 (e (Sum.inl b))
    have h0 : blockLift e p ⟨0, N.pos⟩ = p.1 ⟨0, hm⟩ := by rw [← he0, blockLift_inl]
    rw [blockLift_inl, h0] at h1
    have h2 : p.1 ⟨0, hm⟩ ≤ p.1 a := hsm.monotone (Fin.le_iff_val_le_val.2 (Nat.zero_le _))
    linarith
  · rintro ⟨hsm, hbd⟩
    obtain ⟨y, hy⟩ := exists_lift_of_mem_retainedChamber e hmono hm he0 ⟨hsm, hbd⟩
    exact ⟨(z, y), hy, rfl⟩

/-- The lifted chamber has locally bounded fibers over the retained chamber. -/
theorem exists_nhds_bounded_liftChamber (e : Fin m ⊕ Fin n ≃ Fin (N : ℕ))
    (hm : 0 < m) (he0 : e (Sum.inl ⟨0, hm⟩) = ⟨0, N.pos⟩) {z : EuclideanSpace ℝ (Fin m)} :
    ∃ U ∈ 𝓝 z, Bornology.IsBounded (liftChamber e ∩ (U ×ˢ univ)) := by
  refine ⟨Metric.ball z 1, Metric.ball_mem_nhds z one_pos, ?_⟩
  refine isBounded_iff_forall_norm_le.2
    ⟨max (((m : ℝ) + 1) * (‖z‖ + 1)) (((n : ℝ) + 1) * (‖z‖ + 1 + 1)), fun p hp => ?_⟩
  obtain ⟨hpL, hpU⟩ := hp
  have hp1 : ‖p.1 - z‖ < 1 := by
    have h := hpU.1
    rwa [Metric.mem_ball, dist_eq_norm] at h
  have hcoord1 : ∀ a, |p.1 a| ≤ ‖z‖ + 1 := by
    intro a
    have h1 : |(p.1 - z) a| ≤ ‖p.1 - z‖ := by
      simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (p.1 - z) a
    have h2 : |z a| ≤ ‖z‖ := by
      simpa [Real.norm_eq_abs] using PiLp.norm_apply_le z a
    have h3 : |p.1 a| ≤ |p.1 a - z a| + |z a| := by
      have := abs_add_le (p.1 a - z a) (z a)
      simpa using this
    have h4 : |p.1 a - z a| ≤ 1 := by
      have := h1
      simp only [PiLp.sub_apply] at this
      linarith
    linarith
  have hn1 : ‖p.1‖ ≤ ((m : ℝ) + 1) * (‖z‖ + 1) :=
    norm_le_of_coord_le p.1 (by positivity) hcoord1
  have hcoord2 : ∀ b, |p.2 b| ≤ ‖z‖ + 1 + 1 := fun b => by
    have h := (abs_coord_le_of_mem e hm he0 hpL).2 b
    have h0 := hcoord1 ⟨0, hm⟩
    linarith
  have hn2 : ‖p.2‖ ≤ ((n : ℝ) + 1) * (‖z‖ + 1 + 1) :=
    norm_le_of_coord_le p.2 (by positivity) hcoord2
  rw [Prod.norm_def]
  exact max_le_max hn1 hn2

/-! ### Basic claims about the block energies without the Prékopa–Leindler hypothesis -/

theorem card_add_of_block (e : Fin m ⊕ Fin n ≃ Fin (N : ℕ)) : m + n = (N : ℕ) := by
  simpa using Fintype.card_congr e

/-- For `m = 1` the retained chamber is `ℝ`. -/
theorem retainedChamber_one : retainedChamber 1 = univ := by
  apply Set.eq_univ_of_forall
  intro z
  refine ⟨fun a b hab => absurd hab ?_, fun a b => ?_⟩
  · rw [Subsingleton.elim a b]
    exact lt_irrefl b
  · rw [Subsingleton.elim a b]
    linarith

/-- The volume of the zero-dimensional Euclidean space is one. -/
theorem volume_univ_fin_zero : (volume : Measure (EuclideanSpace ℝ (Fin 0))) univ = 1 := by
  have hpi : (volume : Measure (Fin 0 → ℝ)) univ = 1 := by
    rw [volume_pi, Measure.pi_univ]
    simp
  have h := (PiLp.volume_preserving_ofLp (Fin 0)).measure_preimage
    (MeasurableSet.univ : MeasurableSet (univ : Set (Fin 0 → ℝ))).nullMeasurableSet
  rw [preimage_univ, hpi] at h
  exact h

/-- When `n = 0`, that is `m = N`, the block energy vanishes on the retained chamber. -/
theorem blockTilde_eq_zero_of_isEmpty (χ : HsPairPotentials N c)
    (e : Fin m ⊕ Fin n ≃ Fin (N : ℕ)) (hmono : StrictMono fun a => e (Sum.inl a))
    (hm : 0 < m) (he0 : e (Sum.inl ⟨0, hm⟩) = ⟨0, N.pos⟩) (hn : n = 0)
    {z : EuclideanSpace ℝ (Fin m)} (hz : z ∈ retainedChamber m) : blockTilde χ e z = 0 := by
  subst hn
  obtain ⟨y0, hy0⟩ := exists_lift_of_mem_retainedChamber e hmono hm he0 hz
  have hsub : ∀ y y' : EuclideanSpace ℝ (Fin 0), y = y' := fun _ _ => PiLp.ext fun i => Fin.elim0 i
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
  have hint : ∫ y in (univ : Set (EuclideanSpace ℝ (Fin 0))),
      Real.exp (-blockExteriorEnergy χ e (z, y)) = 1 := by
    simp only [hV, neg_zero, Real.exp_zero, setIntegral_const, smul_eq_mul, mul_one]
    rw [Measure.real, volume_univ_fin_zero]
    simp
  unfold blockTilde
  rw [hfib, hint]
  simp

/-- When `n = 0`, the block energy is convex on the retained chamber. -/
theorem convexOn_blockTilde_of_isEmpty (χ : HsPairPotentials N c)
    (e : Fin m ⊕ Fin n ≃ Fin (N : ℕ)) (hmono : StrictMono fun a => e (Sum.inl a))
    (hm : 0 < m) (he0 : e (Sum.inl ⟨0, hm⟩) = ⟨0, N.pos⟩) (hn : n = 0) :
    ConvexOn ℝ (retainedChamber m) (blockTilde χ e) := by
  refine ⟨convex_retainedChamber m, fun x hx y hy a b ha hb hab => ?_⟩
  rw [blockTilde_eq_zero_of_isEmpty χ e hmono hm he0 hn hx,
    blockTilde_eq_zero_of_isEmpty χ e hmono hm he0 hn hy,
    blockTilde_eq_zero_of_isEmpty χ e hmono hm he0 hn
      (convex_retainedChamber m hx hy ha hb hab)]
  simp

end Riesz1

end
end
