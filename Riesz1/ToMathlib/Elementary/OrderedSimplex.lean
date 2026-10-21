/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
# Volume of the ordered simplex

The set of `x : Fin n → ℝ` with `0 < x_i < 1` for every `i` and `x_0 < ⋯ < x_{n-1}` has volume
`1 / n!`. The proof uses symmetry. For each permutation `σ` of the coordinates, the set of `x` with
`x ∘ σ` strictly increasing is a measure-preserving copy of the simplex. These `n!` sets are
pairwise disjoint, and their union is the set of cube points with distinct entries. That union
has volume one, since the points with a repeated entry form a null set.

The circle version, with `x_0 < x_1 < ⋯ < x_n < x_0 + 1` and `0 ≤ x_0 < 1`, follows by
splitting off the first coordinate.
-/

public section

open MeasureTheory Set Function

namespace Riesz1

/-- The set of strictly increasing tuples is measurable. -/
lemma measurableSet_strictMono (n : ℕ) : MeasurableSet {x : Fin n → ℝ | StrictMono x} := by
  have h : {x : Fin n → ℝ | StrictMono x}
      = ⋂ i : Fin n, ⋂ j : Fin n, {x : Fin n → ℝ | i < j → x i < x j} := by
    ext x
    simp only [mem_ofPred_eq, mem_iInter]
    exact ⟨fun hx i j hij => hx hij, fun hx a b hab => hx a b hab⟩
  rw [h]
  refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_
  by_cases hij : i < j
  · simpa [hij] using measurableSet_lt (measurable_pi_apply i) (measurable_pi_apply j)
  · simp [hij]

/-- The ordered simplex is measurable. -/
lemma measurableSet_ordered_simplex (n : ℕ) :
    MeasurableSet {x : Fin n → ℝ | (∀ i, 0 < x i ∧ x i < 1) ∧ StrictMono x} := by
  have hcube : {x : Fin n → ℝ | ∀ i, 0 < x i ∧ x i < 1}
      = ⋂ i : Fin n, (fun x : Fin n → ℝ => x i) ⁻¹' Ioo 0 1 := by
    ext x
    simp
  have hsplit : {x : Fin n → ℝ | (∀ i, 0 < x i ∧ x i < 1) ∧ StrictMono x}
      = {x : Fin n → ℝ | ∀ i, 0 < x i ∧ x i < 1} ∩ {x : Fin n → ℝ | StrictMono x} := rfl
  rw [hsplit, hcube]
  exact (MeasurableSet.iInter fun i => measurableSet_Ioo.preimage (measurable_pi_apply i)).inter
    (measurableSet_strictMono n)

/-- Tuples with a repeated entry form a null set. -/
lemma volume_not_injective (n : ℕ) :
    volume {x : Fin n → ℝ | ¬ Function.Injective x} = 0 := by
  have hsub : {x : Fin n → ℝ | ¬ Function.Injective x} ⊆
      ⋃ p : {p : Fin n × Fin n // p.1 ≠ p.2}, {x : Fin n → ℝ | x p.1.1 = x p.1.2} := by
    intro x hx
    obtain ⟨a, b, hab, hne⟩ := Function.not_injective_iff.1 hx
    exact mem_iUnion.2 ⟨⟨(a, b), hne⟩, hab⟩
  refine measure_mono_null hsub (measure_iUnion_null fun p => ?_)
  obtain ⟨⟨i, j⟩, hij⟩ := p
  have hij' : i ≠ j := hij
  let f : (Fin n → ℝ) →ₗ[ℝ] ℝ :=
    (LinearMap.proj i : (Fin n → ℝ) →ₗ[ℝ] ℝ) - LinearMap.proj j
  let s : Submodule ℝ (Fin n → ℝ) := LinearMap.ker f
  have hset : {x : Fin n → ℝ | x i = x j} = (s : Set (Fin n → ℝ)) := by
    ext x
    simp [s, f, sub_eq_zero]
  have hne : s ≠ ⊤ := by
    intro htop
    have hmem : (Pi.single i 1 : Fin n → ℝ) ∈ s := by
      rw [htop]
      exact Submodule.mem_top
    simp [s, f, hij'.symm] at hmem
  rw [hset]
  exact Measure.addHaar_submodule volume s hne

/-- The coordinate permutation `x ↦ x ∘ σ` preserves volume on `Fin n → ℝ`. -/
lemma volume_preimage_perm (n : ℕ) (σ : Equiv.Perm (Fin n)) {A : Set (Fin n → ℝ)}
    (hA : MeasurableSet A) :
    volume ((fun x : Fin n → ℝ => x ∘ σ) ⁻¹' A) = volume A := by
  have hmp := volume_measurePreserving_piCongrLeft (fun _ : Fin n => ℝ) σ.symm
  have heq : ⇑(MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) σ.symm)
      = fun x : Fin n → ℝ => x ∘ σ := by
    funext x i
    simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
  rw [heq] at hmp
  exact hmp.measure_preimage hA.nullMeasurableSet

/-- A tuple with distinct entries that becomes strictly increasing after reindexing by `σ` is
sorted by `σ`. -/
lemma perm_eq_sort_of_strictMono {n : ℕ} {x : Fin n → ℝ} (hx : Function.Injective x)
    {σ : Equiv.Perm (Fin n)} (hσ : StrictMono (x ∘ σ)) : σ = Tuple.sort x := by
  refine Tuple.eq_sort_iff.2 ⟨hσ.monotone, fun i j hij heq => ?_⟩
  exact absurd (σ.injective (hx heq)) (ne_of_lt hij)

/-- If `x ∘ σ` is strictly increasing, then `x` is injective. -/
lemma injective_of_strictMono_comp {n : ℕ} {x : Fin n → ℝ} {σ : Equiv.Perm (Fin n)}
    (hσ : StrictMono (x ∘ σ)) : Function.Injective x := by
  intro a b hab
  have h := hσ.injective (show (x ∘ σ) (σ.symm a) = (x ∘ σ) (σ.symm b) by simp [hab])
  exact σ.symm.injective h

/-- The injective points of the cube are the union of the `n!` sets of tuples that are increasing
after a coordinate permutation. -/
lemma injective_cube_eq_iUnion (n : ℕ) :
    {x : Fin n → ℝ | (∀ i, 0 < x i ∧ x i < 1) ∧ Function.Injective x}
      = ⋃ σ : Equiv.Perm (Fin n),
        (fun x : Fin n → ℝ => x ∘ σ) ⁻¹'
          {x : Fin n → ℝ | (∀ i, 0 < x i ∧ x i < 1) ∧ StrictMono x} := by
  ext x
  simp only [mem_ofPred_eq, mem_iUnion, mem_preimage]
  constructor
  · rintro ⟨hcube, hinj⟩
    refine ⟨Tuple.sort x, fun i => hcube _, ?_⟩
    exact (Tuple.monotone_sort x).strictMono_of_injective (hinj.comp (Tuple.sort x).injective)
  · rintro ⟨σ, hcube, hmono⟩
    refine ⟨fun i => ?_, injective_of_strictMono_comp hmono⟩
    simpa using hcube (σ.symm i)

/-- The ordered simplex `{0 < x_0 < ⋯ < x_{n-1} < 1}` in `Fin n → ℝ` has volume `1 / n!`. -/
theorem volume_ordered_simplex (n : ℕ) :
    volume {x : Fin n → ℝ | (∀ i, 0 < x i ∧ x i < 1) ∧ StrictMono x} =
      ENNReal.ofReal (1 / (n.factorial : ℝ)) := by
  have hSm := measurableSet_ordered_simplex n
  -- The `n!` sets `x ∘ σ ∈ S` are pairwise disjoint: a distinct-entry tuple sorts uniquely.
  have hdisj : Pairwise (Disjoint on fun σ : Equiv.Perm (Fin n) =>
      (fun x : Fin n → ℝ => x ∘ σ) ⁻¹'
        {x : Fin n → ℝ | (∀ i, 0 < x i ∧ x i < 1) ∧ StrictMono x}) := by
    intro σ τ hστ
    refine Set.disjoint_left.2 fun x hxσ hxτ => hστ ?_
    have hσ : StrictMono (x ∘ σ) := hxσ.2
    have hτ : StrictMono (x ∘ τ) := hxτ.2
    have hinj := injective_of_strictMono_comp hσ
    exact (perm_eq_sort_of_strictMono hinj hσ).trans (perm_eq_sort_of_strictMono hinj hτ).symm
  have hmeas : ∀ σ : Equiv.Perm (Fin n),
      MeasurableSet ((fun x : Fin n → ℝ => x ∘ σ) ⁻¹'
        {x : Fin n → ℝ | (∀ i, 0 < x i ∧ x i < 1) ∧ StrictMono x}) :=
    fun σ => hSm.preimage (measurable_pi_iff.2 fun i => measurable_pi_apply (σ i))
  have hvol : ∀ σ : Equiv.Perm (Fin n),
      volume ((fun x : Fin n → ℝ => x ∘ σ) ⁻¹'
        {x : Fin n → ℝ | (∀ i, 0 < x i ∧ x i < 1) ∧ StrictMono x})
        = volume {x : Fin n → ℝ | (∀ i, 0 < x i ∧ x i < 1) ∧ StrictMono x} :=
    fun σ => volume_preimage_perm n σ hSm
  -- The injective points of the cube have volume `n!` times the volume of the simplex.
  have hU : volume {x : Fin n → ℝ | (∀ i, 0 < x i ∧ x i < 1) ∧ Function.Injective x}
      = (n.factorial : ENNReal)
        * volume {x : Fin n → ℝ | (∀ i, 0 < x i ∧ x i < 1) ∧ StrictMono x} := by
    rw [injective_cube_eq_iUnion n, measure_iUnion hdisj hmeas]
    simp only [tsum_fintype, hvol, Finset.sum_const, Finset.card_univ, Fintype.card_perm,
      Fintype.card_fin, nsmul_eq_mul]
  -- The injective points of the cube have full volume, since their complement is null.
  have hC : volume (Set.univ.pi fun _ : Fin n => Ioo (0 : ℝ) 1) = 1 := by
    rw [Real.volume_pi_Ioo]
    simp
  have hUC : volume {x : Fin n → ℝ | (∀ i, 0 < x i ∧ x i < 1) ∧ Function.Injective x}
      = volume (Set.univ.pi fun _ : Fin n => Ioo (0 : ℝ) 1) := by
    apply le_antisymm
    · apply measure_mono
      intro x hx
      exact mem_univ_pi.2 fun i => mem_Ioo.2 (hx.1 i)
    · calc volume (Set.univ.pi fun _ : Fin n => Ioo (0 : ℝ) 1)
          ≤ volume ({x : Fin n → ℝ | (∀ i, 0 < x i ∧ x i < 1) ∧ Function.Injective x}
              ∪ {x : Fin n → ℝ | ¬ Function.Injective x}) := by
            apply measure_mono
            intro x hx
            by_cases hinj : Function.Injective x
            · exact Or.inl ⟨fun i => mem_Ioo.1 (mem_univ_pi.1 hx i), hinj⟩
            · exact Or.inr hinj
        _ ≤ volume {x : Fin n → ℝ | (∀ i, 0 < x i ∧ x i < 1) ∧ Function.Injective x}
              + volume {x : Fin n → ℝ | ¬ Function.Injective x} := measure_union_le _ _
        _ = volume {x : Fin n → ℝ | (∀ i, 0 < x i ∧ x i < 1) ∧ Function.Injective x} := by
          rw [volume_not_injective, add_zero]
  have hprod : (n.factorial : ENNReal)
      * volume {x : Fin n → ℝ | (∀ i, 0 < x i ∧ x i < 1) ∧ StrictMono x} = 1 := by
    rw [← hU, hUC, hC]
  rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_one, ENNReal.ofReal_natCast,
    one_div]
  exact ENNReal.eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hprod)

/-- Adding a constant to every entry of a tuple preserves strict monotonicity. -/
lemma strictMono_add_const_iff {n : ℕ} (y : Fin n → ℝ) (c : ℝ) :
    StrictMono (y + fun _ => c) ↔ StrictMono y :=
  ⟨fun h a b hab => by simpa using h hab, fun h a b hab => by simpa using h hab⟩

/-- The circle version: the set of `x : Fin (n + 1) → ℝ` with `0 ≤ x_0 < 1`, `x_0 < x_1 < ⋯ < x_n`
and `x_n < x_0 + 1` has volume `1 / n!`. -/
theorem volume_circle_ordered_simplex (n : ℕ) :
    volume {x : Fin (n + 1) → ℝ | (0 ≤ x 0 ∧ x 0 < 1) ∧ StrictMono x ∧ x (Fin.last n) < x 0 + 1} =
      ENNReal.ofReal (1 / (n.factorial : ℝ)) := by
  set S : Set (Fin n → ℝ) := {x : Fin n → ℝ | (∀ i, 0 < x i ∧ x i < 1) ∧ StrictMono x} with hSdef
  set T' : Set (ℝ × (Fin n → ℝ)) :=
    {p | (0 ≤ p.1 ∧ p.1 < 1) ∧ (∀ j, p.1 < p.2 j) ∧ StrictMono p.2 ∧ ∀ j, p.2 j < p.1 + 1}
    with hT'def
  -- The splitting `x ↦ (x_0, (x_1, …, x_n))` and its measurability.
  have hA : MeasurableSet {p : ℝ × (Fin n → ℝ) | 0 ≤ p.1 ∧ p.1 < 1} :=
    (measurableSet_le measurable_const measurable_fst).inter
      (measurableSet_lt measurable_fst measurable_const)
  have hB : MeasurableSet {p : ℝ × (Fin n → ℝ) | ∀ j, p.1 < p.2 j} := by
    have h : {p : ℝ × (Fin n → ℝ) | ∀ j, p.1 < p.2 j}
        = ⋂ j : Fin n, {p : ℝ × (Fin n → ℝ) | p.1 < p.2 j} := by
      ext p
      simp
    rw [h]
    exact MeasurableSet.iInter fun j =>
      measurableSet_lt measurable_fst ((measurable_pi_apply j).comp measurable_snd)
  have hC : MeasurableSet {p : ℝ × (Fin n → ℝ) | StrictMono p.2} :=
    (measurableSet_strictMono n).preimage measurable_snd
  have hD : MeasurableSet {p : ℝ × (Fin n → ℝ) | ∀ j, p.2 j < p.1 + 1} := by
    have h : {p : ℝ × (Fin n → ℝ) | ∀ j, p.2 j < p.1 + 1}
        = ⋂ j : Fin n, {p : ℝ × (Fin n → ℝ) | p.2 j < p.1 + 1} := by
      ext p
      simp
    rw [h]
    exact MeasurableSet.iInter fun j =>
      measurableSet_lt ((measurable_pi_apply j).comp measurable_snd) (measurable_fst.add_const 1)
  have hT'm : MeasurableSet T' := hA.inter (hB.inter (hC.inter hD))
  -- In coordinates `(x_0, (x_1, …, x_n))`, the circle set is the preimage of `T'`.
  have hT : {x : Fin (n + 1) → ℝ | (0 ≤ x 0 ∧ x 0 < 1) ∧ StrictMono x ∧
      x (Fin.last n) < x 0 + 1}
      = (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0) ⁻¹' T' := by
    ext x
    have he : (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0) x
        = (x 0, fun j => x j.succ) := rfl
    simp only [mem_ofPred_eq, mem_preimage, he, hT'def]
    constructor
    · rintro ⟨⟨h0, h1⟩, hmono, hlast⟩
      exact ⟨⟨h0, h1⟩, fun j => hmono (Fin.succ_pos j),
        fun a b hab => hmono (Fin.succ_lt_succ_iff.2 hab),
        fun j => lt_of_le_of_lt (hmono.monotone (Fin.le_last _)) hlast⟩
    · rintro ⟨⟨h0, h1⟩, hy1, hymono, hy2⟩
      have hmono : StrictMono x := by
        intro a b hab
        induction a using Fin.cases with
        | zero =>
          induction b using Fin.cases with
          | zero => exact absurd hab (lt_irrefl _)
          | succ j => exact hy1 j
        | succ i =>
          induction b using Fin.cases with
          | zero => exact absurd hab (Fin.not_lt_zero _)
          | succ j => exact hymono (Fin.succ_lt_succ_iff.1 hab)
      have hall : ∀ i : Fin (n + 1), x i < x 0 + 1 := by
        intro i
        induction i using Fin.cases with
        | zero => exact lt_add_one _
        | succ j => exact hy2 j
      exact ⟨⟨h0, h1⟩, hmono, hall _⟩
  -- The splitting map preserves volume.
  have hpres := (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).measure_preimage
    hT'm.nullMeasurableSet
  -- Each fiber over `t` is a translate of the simplex when `0 ≤ t < 1`, and empty otherwise.
  have hfib : ∀ t : ℝ,
      volume (Prod.mk t ⁻¹' T') = (Ico (0 : ℝ) 1).indicator (fun _ => volume S) t := by
    intro t
    by_cases ht : t ∈ Ico (0 : ℝ) 1
    · rw [indicator_of_mem ht]
      have hset : Prod.mk t ⁻¹' T' = (fun h : Fin n → ℝ => h + fun _ => -t) ⁻¹' S := by
        ext y
        simp only [mem_preimage, hT'def, hSdef, mem_ofPred_eq, Pi.add_apply]
        rw [strictMono_add_const_iff]
        constructor
        · rintro ⟨-, h1, h2, h3⟩
          exact ⟨fun i => ⟨by linarith [h1 i], by linarith [h3 i]⟩, h2⟩
        · rintro ⟨h1, h2⟩
          exact ⟨⟨ht.1, ht.2⟩, fun j => by linarith [(h1 j).1], h2, fun j => by linarith [(h1 j).2]⟩
      rw [hset, measure_preimage_add_right]
    · rw [indicator_of_notMem ht]
      have hempty : Prod.mk t ⁻¹' T' = ∅ := by
        ext y
        simp only [mem_preimage, hT'def, mem_ofPred_eq, mem_empty_iff_false, iff_false]
        exact fun h => ht ⟨h.1.1, h.1.2⟩
      rw [hempty, measure_empty]
  calc volume {x : Fin (n + 1) → ℝ | (0 ≤ x 0 ∧ x 0 < 1) ∧ StrictMono x ∧ x (Fin.last n) < x 0 + 1}
      = volume T' := by rw [hT, hpres]
    _ = (volume.prod volume) T' := by rw [Measure.volume_eq_prod]
    _ = ∫⁻ t, volume (Prod.mk t ⁻¹' T') := Measure.prod_apply hT'm
    _ = ∫⁻ t, (Ico (0 : ℝ) 1).indicator (fun _ => volume S) t := lintegral_congr hfib
    _ = volume S * volume (Ico (0 : ℝ) 1) := lintegral_indicator_const measurableSet_Ico _
    _ = volume S := by simp
    _ = ENNReal.ofReal (1 / (n.factorial : ℝ)) := volume_ordered_simplex n

end Riesz1
