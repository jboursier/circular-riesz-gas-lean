/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.CLT.SelectionCyclic
public import Riesz1.Rigidity.BoundarySelectionLawWindow
public import Riesz1.Rigidity.GapLawMoments
public import Riesz1.Rigidity.Inversion
public import Riesz1.Variance.APrioriRotationVariance

/-!
# The joint law of the origin offset and the relabelled gaps

Part of Lemma 5.2 (the rotation part), the joint-law claim. Let `J` be the label of the particle
preceding the origin, that is the largest integer `j` with `x_j ≤ 0`. Put `D = -N x_J` and
`y_k = x_{J+k} - x_J` for `0 ≤ k < N`. For every measurable `φ ≥ 0`,
`E φ(D, y) = E_{μ*} ∫_{0<D<w(y)} φ(D, y) dD` with `w(y) = N y_2` and `μ*` the anchored law. This is
`joint_law_rotAnchoredLaw`.

The proof follows `Riesz1.nearest_selection_nonneg`, with the preceding label in place of the
nearest one, and keeps the origin offset as a variable.

1. *Residue classes.* Exactly one residue `i` of `J` modulo `N` holds. On the class `i`, the origin
   offset is `N` times the representative in `[0, 1)` of `-x_i`, and the class is the event that
   this representative is below `gap_i / N` (`originLabel_mod_iff`).
2. *Rotation.* The pair `(x_i mod 1, gapVector)` has the product law
   (`map_cyclicLift_gapVector_gibbsMeasure`). The circle integral of the representative is the
   Lebesgue integral over `[0, 1)` (`lintegral_circle_negRep`).
3. *Dilation.* The factor `1/N` from `D = N r` turns `∫_{[0, gap_i/N)}` into `(1/N) ∫_{(0, gap_i)}`.
4. *Cyclic invariance.* Each class has the expectation of class `0`
   (`lintegral_shiftFin_gapVector`), so the `N` classes with weight `1/N` sum to class `0`.

The statement is checked on `N = 2`: there `w(y) = 2 y_1` with `E_{μ*} w = 1`, and the joint law
has total mass one.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Riesz1

variable {N : ℕ+}

/-! ### The origin label and the relabelled positions -/

/-- The label of the particle preceding the origin: the largest integer `j` with `x_j ≤ 0`. -/
def originLabel (X : Configuration N) : ℤ :=
  sSup {j : ℤ | cyclicLift X j ≤ 0}

/-- The origin offset `D = -N x_J` of the rotation part of Lemma 5.2. -/
def originD (X : Configuration N) : ℝ :=
  -((N : ℕ) : ℝ) * cyclicLift X (originLabel X)

/-- The positions `y_k = x_{J+k} - x_J` of the particles relabelled to start at the preceding
particle. -/
def originPos (X : Configuration N) : Fin (N : ℕ) → ℝ :=
  fun k => cyclicLift X (originLabel X + ((k : ℕ) : ℤ)) - cyclicLift X (originLabel X)

/-- The preceding particle satisfies `x_J ≤ 0 < x_{J+1}`. -/
theorem originLabel_spec (X : Configuration N) :
    cyclicLift X (originLabel X) ≤ 0 ∧ 0 < cyclicLift X (originLabel X + 1) :=
  preceding_spec X (b := 0) le_rfl zero_lt_one

/-- A label `j` with `x_j ≤ 0 < x_{j+1}` is the preceding label. -/
theorem eq_originLabel_of_spec (X : Configuration N) {j : ℤ}
    (hj : cyclicLift X j ≤ 0 ∧ 0 < cyclicLift X (j + 1)) : j = originLabel X := by
  obtain ⟨h1, h2⟩ := hj
  obtain ⟨h3, h4⟩ := originLabel_spec X
  have hmono := (cyclicLift_strictMono X).monotone
  rcases lt_trichotomy j (originLabel X) with h | h | h
  · have := hmono (show j + 1 ≤ originLabel X by omega)
    linarith
  · exact h
  · have := hmono (show originLabel X + 1 ≤ j by omega)
    linarith

/-! ### Gap positions and the telescoping identity -/

/-- The positions of the particles `i, i+1, …` relative to particle `i`, read from a gap vector
`h`: the entry `k` is `(1/N) ∑_{j<k} h_{i+j}`. -/
def gapPositions (h : Fin (N : ℕ) → ℝ) (i : ℤ) : Fin (N : ℕ) → ℝ :=
  fun k => (∑ j ∈ Finset.range (k : ℕ), gapOf h (i + (j : ℤ))) / ((N : ℕ) : ℝ)

/-- A gap of the gap vector, divided by `N`, is the increment of the lifts. -/
theorem gapOf_gapVector_div (X : Configuration N) (j : ℤ) :
    gapOf (gapVector X) j / ((N : ℕ) : ℝ) = cyclicLift X (j + 1) - cyclicLift X j := by
  have hN : ((N : ℕ) : ℝ) ≠ 0 := by exact_mod_cast N.ne_zero
  rw [← gap_eq_gapOf_gapVector]
  unfold gap
  exact mul_div_cancel_left₀ _ hN

/-- The lift of particle `i + k` relative to particle `i` is the gap position of `k`. -/
theorem cyclicLift_sub_eq_gapPositions (X : Configuration N) (i : ℤ) (k : Fin (N : ℕ)) :
    cyclicLift X (i + ((k : ℕ) : ℤ)) - cyclicLift X i = gapPositions (gapVector X) i k := by
  have key : ∀ n : ℕ, cyclicLift X (i + (n : ℤ)) - cyclicLift X i =
      (∑ j ∈ Finset.range n, gapOf (gapVector X) (i + (j : ℤ))) / ((N : ℕ) : ℝ) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, add_div, ← ih, gapOf_gapVector_div, Nat.cast_succ, ← add_assoc]
      ring
  exact key k

/-- Gap positions depend on the label only through its residue modulo `N`. -/
theorem gapPositions_eq_of_mod_eq (h : Fin (N : ℕ) → ℝ) {j i : ℤ}
    (hj : j % ((N : ℕ) : ℤ) = i) : gapPositions h j = gapPositions h i := by
  obtain ⟨q, rfl⟩ : ∃ q : ℤ, j = i + ((N : ℕ) : ℤ) * q :=
    ⟨j / ((N : ℕ) : ℤ), by linarith [Int.emod_def j ((N : ℕ) : ℤ)]⟩
  funext k
  unfold gapPositions
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [show i + ((N : ℕ) : ℤ) * q + (m : ℤ) = (i + (m : ℤ)) + ((N : ℕ) : ℤ) * q by ring]
  exact periodic_add_mul (fun n => gapOf h n) (fun n => gapOf_add_N h n) _ q

/-! ### The representative of `-u` in `[0, 1)` -/

/-- The representative in `[0, 1)` of the point `-u` of the unit circle. -/
def negRep (u : UnitAddCircle) : ℝ :=
  (AddCircle.equivIco (1 : ℝ) 0 (0 - u) : ℝ)

theorem negRep_mem (u : UnitAddCircle) : negRep u ∈ Ico (0 : ℝ) 1 := by
  unfold negRep
  have h := (AddCircle.equivIco (1 : ℝ) 0 (0 - u)).2
  exact ⟨h.1, by simpa using h.2⟩

theorem measurable_negRep : Measurable negRep := by
  have hsub : Measurable (fun u : UnitAddCircle => (0 : UnitAddCircle) - u) := by fun_prop
  unfold negRep
  exact (measurable_subtype_coe.comp (AddCircle.measurableEquivIco (1 : ℝ) 0).measurable).comp
    hsub

theorem coe_negRep (u : UnitAddCircle) : ((negRep u : ℝ) : UnitAddCircle) = -u := by
  unfold negRep
  rw [AddCircle.coe_equivIco, zero_sub]

/-- The representative of `-x` differs from `-x` by an integer. -/
theorem exists_int_negRep (x : ℝ) : ∃ m : ℤ, negRep (x : UnitAddCircle) = -x + m := by
  have h : ((negRep (x : UnitAddCircle) - -x : ℝ) : UnitAddCircle) = 0 := by
    rw [QuotientAddGroup.mk_sub, coe_negRep, QuotientAddGroup.mk_neg]
    simp
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp h
  refine ⟨n, ?_⟩
  rw [zsmul_eq_mul, mul_one] at hn
  linarith

/-- Two points of `[0, 1)` that differ by an integer are equal. -/
theorem eq_of_sub_eq_int_of_mem_Ico {a b : ℝ} (ha : a ∈ Ico (0 : ℝ) 1) (hb : b ∈ Ico (0 : ℝ) 1)
    {m : ℤ} (h : a - b = m) : a = b := by
  obtain ⟨ha0, ha1⟩ := ha
  obtain ⟨hb0, hb1⟩ := hb
  have h1 : (m : ℝ) < 1 := by linarith
  have h2 : (-1 : ℝ) < m := by linarith
  have h1' : m < 1 := by exact_mod_cast h1
  have h2' : -1 < m := by exact_mod_cast h2
  have hm : m = 0 := by omega
  rw [hm, Int.cast_zero, sub_eq_zero] at h
  exact h

/-! ### The residue classes of the origin label -/

/-- On the residue class `i` of the origin label, the representative of `-x_i` is the origin
offset `-x_J`, which lies below `gap_i / N`. -/
theorem negRep_eq_neg_origin (X : Configuration N) {i : ℤ}
    (hJ : originLabel X % ((N : ℕ) : ℤ) = i) :
    negRep (cyclicLift X i : UnitAddCircle) = -cyclicLift X (originLabel X) ∧
      -cyclicLift X (originLabel X) < gapOf (gapVector X) i / ((N : ℕ) : ℝ) := by
  obtain ⟨q, hq⟩ : ∃ q : ℤ, originLabel X = i + ((N : ℕ) : ℤ) * q :=
    ⟨originLabel X / ((N : ℕ) : ℤ), by linarith [Int.emod_def (originLabel X) ((N : ℕ) : ℤ)]⟩
  obtain ⟨h1, h2⟩ := originLabel_spec X
  have hxJ : cyclicLift X (originLabel X) = cyclicLift X i + q := by
    rw [hq]
    exact lift_add_mul_eq (cyclicLift X) (cyclicLift_add_N X) i q
  have hgap : gapOf (gapVector X) (originLabel X) = gapOf (gapVector X) i := by
    rw [hq]
    exact periodic_add_mul (fun n => gapOf (gapVector X) n) (fun n => gapOf_add_N _ n) i q
  have hstep := gapOf_gapVector_div X (originLabel X)
  rw [hgap] at hstep
  have hc1 : gapOf (gapVector X) i / ((N : ℕ) : ℝ) ≤ 1 := by
    have hNpos : (0 : ℝ) < ((N : ℕ) : ℝ) := by exact_mod_cast N.pos
    rw [← gap_eq_gapOf_gapVector]
    exact (div_le_one hNpos).2 (gap_le_N X i)
  have hlt : -cyclicLift X (originLabel X) < gapOf (gapVector X) i / ((N : ℕ) : ℝ) := by
    linarith
  have hb : -cyclicLift X (originLabel X) ∈ Ico (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  obtain ⟨m, hm⟩ := exists_int_negRep (cyclicLift X i)
  refine ⟨?_, hlt⟩
  refine eq_of_sub_eq_int_of_mem_Ico (negRep_mem _) hb (m := m + q) ?_
  rw [hm, hxJ]
  push_cast
  ring

/-- The origin label lies in the residue class `i` exactly when the representative of `-x_i`
lies below `gap_i / N`. -/
theorem originLabel_mod_iff (X : Configuration N) {i : ℤ} (hi0 : 0 ≤ i)
    (hiN : i < ((N : ℕ) : ℤ)) :
    originLabel X % ((N : ℕ) : ℤ) = i ↔
      negRep (cyclicLift X i : UnitAddCircle) < gapOf (gapVector X) i / ((N : ℕ) : ℝ) := by
  constructor
  · intro hJ
    obtain ⟨hneg, hlt⟩ := negRep_eq_neg_origin X hJ
    rw [hneg]
    exact hlt
  · intro hlt
    obtain ⟨m, hm⟩ := exists_int_negRep (cyclicLift X i)
    have hr0 := (negRep_mem (cyclicLift X i : UnitAddCircle)).1
    have hx : cyclicLift X (i + ((N : ℕ) : ℤ) * (-m)) = cyclicLift X i + -(m : ℝ) := by
      have h := lift_add_mul_eq (cyclicLift X) (cyclicLift_add_N X) i (-m)
      push_cast at h
      exact h
    have hgap : gapOf (gapVector X) (i + ((N : ℕ) : ℤ) * (-m)) = gapOf (gapVector X) i :=
      periodic_add_mul (fun n => gapOf (gapVector X) n) (fun n => gapOf_add_N _ n) i (-m)
    have hstep := gapOf_gapVector_div X (i + ((N : ℕ) : ℤ) * (-m))
    rw [hgap] at hstep
    have hspec : cyclicLift X (i + ((N : ℕ) : ℤ) * (-m)) ≤ 0 ∧
        0 < cyclicLift X (i + ((N : ℕ) : ℤ) * (-m) + 1) := by
      constructor
      · linarith
      · linarith
    have hJ := eq_originLabel_of_spec X hspec
    rw [← hJ, Int.add_mul_emod_self_left, Int.emod_eq_of_lt hi0 hiN]

/-! ### The residue integrand and the residue weight -/

/-- The integrand of the residue class `i` of the origin label, as a function of the rotation
`u` (the class of `x_i` modulo one) and of the gap vector `h`. -/
def residueIntegrand (φ : ℝ → (Fin (N : ℕ) → ℝ) → ℝ≥0∞) (i : ℤ) (u : UnitAddCircle)
    (h : Fin (N : ℕ) → ℝ) : ℝ≥0∞ :=
  if negRep u < gapOf h i / ((N : ℕ) : ℝ) then
    φ (((N : ℕ) : ℝ) * negRep u) (gapPositions h i)
  else 0

/-- The residue integrand on the class `i` is the origin term of `φ` on the class, else zero. -/
theorem residueIntegrand_eq_ite (φ : ℝ → (Fin (N : ℕ) → ℝ) → ℝ≥0∞) (X : Configuration N) {i : ℤ}
    (hi0 : 0 ≤ i) (hiN : i < ((N : ℕ) : ℤ)) :
    residueIntegrand φ i (cyclicLift X i : UnitAddCircle) (gapVector X) =
      if originLabel X % ((N : ℕ) : ℤ) = i then φ (originD X) (originPos X) else 0 := by
  by_cases hJ : originLabel X % ((N : ℕ) : ℤ) = i
  · simp only [hJ, ↓reduceIte]
    have hlt := (originLabel_mod_iff X hi0 hiN).1 hJ
    obtain ⟨hneg, -⟩ := negRep_eq_neg_origin X hJ
    have hD : originD X = ((N : ℕ) : ℝ) * negRep (cyclicLift X i : UnitAddCircle) := by
      rw [hneg]
      unfold originD
      ring
    have hP : originPos X = gapPositions (gapVector X) i := by
      rw [← gapPositions_eq_of_mod_eq (gapVector X) hJ]
      funext k
      exact cyclicLift_sub_eq_gapPositions X (originLabel X) k
    unfold residueIntegrand
    simp only [hlt, ↓reduceIte]
    rw [hD, hP]
  · simp only [hJ, ↓reduceIte]
    have hlt : ¬ negRep (cyclicLift X i : UnitAddCircle) <
        gapOf (gapVector X) i / ((N : ℕ) : ℝ) :=
      fun h => hJ ((originLabel_mod_iff X hi0 hiN).2 h)
    unfold residueIntegrand
    simp only [hlt, ↓reduceIte]

/-- Exactly one residue class of the origin label holds, so the origin term is the sum of the
residue integrands. -/
theorem originTerm_eq_sum (φ : ℝ → (Fin (N : ℕ) → ℝ) → ℝ≥0∞) (X : Configuration N) :
    φ (originD X) (originPos X) =
      ∑ i : Fin (N : ℕ), residueIntegrand φ ((i : ℕ) : ℤ)
        (cyclicLift X ((i : ℕ) : ℤ) : UnitAddCircle) (gapVector X) := by
  have hN0 : (0 : ℤ) < ((N : ℕ) : ℤ) := by exact_mod_cast N.pos
  have hmod0 := Int.emod_nonneg (originLabel X) hN0.ne'
  have hmodlt := Int.emod_lt_of_pos (originLabel X) hN0
  have hi0 : (originLabel X % ((N : ℕ) : ℤ)).toNat < (N : ℕ) := by omega
  have hcast : (((originLabel X % ((N : ℕ) : ℤ)).toNat : ℕ) : ℤ) = originLabel X % ((N : ℕ) : ℤ) :=
    Int.toNat_of_nonneg hmod0
  rw [Finset.sum_eq_single ⟨(originLabel X % ((N : ℕ) : ℤ)).toNat, hi0⟩]
  · have hi0' : (0 : ℤ) ≤ (((⟨(originLabel X % ((N : ℕ) : ℤ)).toNat, hi0⟩ : Fin (N : ℕ)) : ℕ) : ℤ) :=
      Nat.cast_nonneg _
    have hiN' : (((⟨(originLabel X % ((N : ℕ) : ℤ)).toNat, hi0⟩ : Fin (N : ℕ)) : ℕ) : ℤ) <
        ((N : ℕ) : ℤ) := by
      exact_mod_cast (show (⟨(originLabel X % ((N : ℕ) : ℤ)).toNat, hi0⟩ : Fin (N : ℕ)).val <
        (N : ℕ) from hi0)
    have hcond : originLabel X % ((N : ℕ) : ℤ) =
        (((⟨(originLabel X % ((N : ℕ) : ℤ)).toNat, hi0⟩ : Fin (N : ℕ)) : ℕ) : ℤ) := hcast.symm
    rw [residueIntegrand_eq_ite φ X hi0' hiN', ite_eq_left_of_eq_true _ _ (eq_true hcond)]
  · intro i _ hne
    have hi0' : (0 : ℤ) ≤ ((i : ℕ) : ℤ) := Nat.cast_nonneg _
    have hiN' : ((i : ℕ) : ℤ) < ((N : ℕ) : ℤ) := by exact_mod_cast i.isLt
    rw [residueIntegrand_eq_ite φ X hi0' hiN']
    have hne' : ¬ originLabel X % ((N : ℕ) : ℤ) = ((i : ℕ) : ℤ) := by
      intro h
      apply hne
      apply Fin.ext
      have hh : (originLabel X % ((N : ℕ) : ℤ)).toNat = (i : ℕ) := by
        rw [h]
        simp
      exact hh.symm
    rw [ite_eq_right_of_eq_false _ _ (eq_false hne')]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The residue weight: the integral of `φ` over the origin offsets `0 < D ≤ gap_i` against the
positions of `h` relabelled at `i`. -/
def residueWeight (φ : ℝ → (Fin (N : ℕ) → ℝ) → ℝ≥0∞) (i : ℤ) (h : Fin (N : ℕ) → ℝ) : ℝ≥0∞ :=
  ∫⁻ D in Ioc (0 : ℝ) (gapOf h i), φ D (gapPositions h i)

/-! ### Measurability -/

theorem measurable_gapOf_div (i : ℤ) :
    Measurable (fun h : Fin (N : ℕ) → ℝ => gapOf h i / ((N : ℕ) : ℝ)) :=
  (measurable_pi_apply (modFin N i)).div_const _

theorem measurable_gapPositions (i : ℤ) :
    Measurable (fun h : Fin (N : ℕ) → ℝ => gapPositions h i) := by
  refine Measurable.of_eval fun k => ?_
  unfold gapPositions
  refine Measurable.div_const (Finset.measurable_sum _ fun j _ => ?_) _
  exact (measurable_pi_apply (modFin N (i + (j : ℤ))) :
    Measurable fun h : Fin (N : ℕ) → ℝ => gapOf h (i + (j : ℤ)))

/-- A parametric integral over `(0, c(b)]` is measurable in the parameter `b`. -/
theorem measurable_lintegral_Ioc_param {β : Type*} [MeasurableSpace β] (c : β → ℝ)
    (hc : Measurable c) (F : β × ℝ → ℝ≥0∞) (hF : Measurable F) :
    Measurable (fun b => ∫⁻ D in Ioc (0 : ℝ) (c b), F (b, D)) := by
  have hS : MeasurableSet {q : β × ℝ | 0 < q.2 ∧ q.2 ≤ c q.1} :=
    (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd (hc.comp measurable_fst))
  have hΦ : Measurable ({q : β × ℝ | 0 < q.2 ∧ q.2 ≤ c q.1}.indicator F) := hF.indicator hS
  have key : ∀ b : β, ∫⁻ D in Ioc (0 : ℝ) (c b), F (b, D) =
      ∫⁻ D, {q : β × ℝ | 0 < q.2 ∧ q.2 ≤ c q.1}.indicator F (b, D) := by
    intro b
    rw [← lintegral_indicator measurableSet_Ioc]
    refine lintegral_congr fun D => ?_
    by_cases hD : D ∈ Ioc (0 : ℝ) (c b)
    · rw [indicator_of_mem hD, indicator_of_mem (show (b, D) ∈
        {q : β × ℝ | 0 < q.2 ∧ q.2 ≤ c q.1} from ⟨hD.1, hD.2⟩)]
    · rw [indicator_of_notMem hD, indicator_of_notMem]
      intro h
      exact hD ⟨h.1, h.2⟩
  simp_rw [key]
  exact hΦ.lintegral_prod_right'

theorem measurable_residueWeight (φ : ℝ → (Fin (N : ℕ) → ℝ) → ℝ≥0∞)
    (hφ : Measurable (fun p : ℝ × (Fin (N : ℕ) → ℝ) => φ p.1 p.2)) (i : ℤ) :
    Measurable (residueWeight φ i) := by
  have hc : Measurable (fun h : Fin (N : ℕ) → ℝ => gapOf h i) :=
    measurable_pi_apply (modFin N i)
  have hF : Measurable (fun q : (Fin (N : ℕ) → ℝ) × ℝ => φ q.2 (gapPositions q.1 i)) :=
    hφ.comp (measurable_snd.prodMk ((measurable_gapPositions i).comp measurable_fst))
  exact measurable_lintegral_Ioc_param (fun h => gapOf h i) hc
    (fun q => φ q.2 (gapPositions q.1 i)) hF

theorem measurable_residueIntegrand (φ : ℝ → (Fin (N : ℕ) → ℝ) → ℝ≥0∞)
    (hφ : Measurable (fun p : ℝ × (Fin (N : ℕ) → ℝ) => φ p.1 p.2)) (i : ℤ) :
    Measurable (fun p : UnitAddCircle × (Fin (N : ℕ) → ℝ) => residueIntegrand φ i p.1 p.2) := by
  unfold residueIntegrand
  refine Measurable.ite ?_ ?_ measurable_const
  · exact measurableSet_lt (measurable_negRep.comp measurable_fst)
      ((measurable_gapOf_div i).comp measurable_snd)
  · exact hφ.comp ((measurable_const.mul (measurable_negRep.comp measurable_fst)).prodMk
      ((measurable_gapPositions i).comp measurable_snd))

/-! ### Circle integrals and dilations -/

/-- Integrating a function of the representative `-u` over the circle gives Lebesgue measure on
`[0, 1)`. -/
theorem lintegral_circle_negRep (H : ℝ → ℝ≥0∞) (hH : Measurable H) :
    ∫⁻ u, H (negRep u) ∂(volume : Measure UnitAddCircle) = ∫⁻ r in Ico (0 : ℝ) 1, H r := by
  have hsub : Measurable (fun u : UnitAddCircle => (0 : UnitAddCircle) - u) := by fun_prop
  have hrep : Measurable (fun u : UnitAddCircle => (AddCircle.equivIco (1 : ℝ) 0 u : ℝ)) :=
    measurable_subtype_coe.comp (AddCircle.measurableEquivIco (1 : ℝ) 0).measurable
  have hmap : (volume : Measure UnitAddCircle).map negRep = volume.restrict (Ico (0 : ℝ) 1) := by
    rw [show negRep = (fun u => (AddCircle.equivIco (1 : ℝ) 0 u : ℝ)) ∘ (fun u => 0 - u) from rfl,
      ← Measure.map_map hrep hsub,
      (volume : Measure UnitAddCircle).measurePreserving_sub_left 0 |>.map_eq,
      map_circle_representative_uniform]
  rw [← lintegral_map hH measurable_negRep, hmap]

/-- The integral over `[0, 1)` of `1_{r < c} g(r)` is the integral of `g` over `[0, c)`, for
`0 ≤ c ≤ 1`. -/
theorem lintegral_Ico_ite_eq (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (g : ℝ → ℝ≥0∞) :
    ∫⁻ r in Ico (0 : ℝ) 1, (if r < c then g r else 0) = ∫⁻ r in Ico (0 : ℝ) c, g r := by
  rw [← Ico_union_Ico_eq_Ico hc0 hc1, lintegral_union measurableSet_Ico Ico_disjoint_Ico_same]
  have h1 : ∫⁻ r in Ico (0 : ℝ) c, (if r < c then g r else 0) = ∫⁻ r in Ico (0 : ℝ) c, g r :=
    setLIntegral_congr_fun measurableSet_Ico fun r hr =>
      ite_eq_left_of_eq_true _ _ (eq_true hr.2)
  have h2 : ∫⁻ r in Ico c 1, (if r < c then g r else 0) = 0 := by
    have hz : ∀ r ∈ Ico c 1, (if r < c then g r else 0) = (0 : ℝ≥0∞) := fun r hr =>
      ite_eq_right_of_eq_false _ _ (eq_false (not_lt.2 hr.1))
    rw [setLIntegral_congr_fun measurableSet_Ico hz, lintegral_zero]
  rw [h1, h2, add_zero]

/-- Substituting `r ↦ a r` in an integral over `(0, c]`, for `a > 0`. -/
theorem lintegral_Ioc_mul (a c : ℝ) (ha : 0 < a) (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ r in Ioc (0 : ℝ) c, g (a * r) = ENNReal.ofReal a⁻¹ * ∫⁻ D in Ioc (0 : ℝ) (a * c), g D := by
  have hset : ∀ r : ℝ, (Ioc (0 : ℝ) c).indicator (fun r => g (a * r)) r =
      (Ioc (0 : ℝ) (a * c)).indicator g (a * r) := by
    intro r
    by_cases hr : r ∈ Ioc (0 : ℝ) c
    · have hr' : a * r ∈ Ioc (0 : ℝ) (a * c) :=
        ⟨mul_pos ha hr.1, mul_le_mul_of_nonneg_left hr.2 ha.le⟩
      rw [indicator_of_mem hr, indicator_of_mem hr']
    · have hr' : a * r ∉ Ioc (0 : ℝ) (a * c) := by
        rintro ⟨h1, h2⟩
        exact hr ⟨pos_of_mul_pos_right h1 ha.le, le_of_mul_le_mul_left h2 ha⟩
      rw [indicator_of_notMem hr, indicator_of_notMem hr']
  have hm : Measurable (fun r : ℝ => a * r) := measurable_const.mul measurable_id
  have hind : Measurable ((Ioc (0 : ℝ) (a * c)).indicator g) := hg.indicator measurableSet_Ioc
  calc ∫⁻ r in Ioc (0 : ℝ) c, g (a * r)
      = ∫⁻ r, (Ioc (0 : ℝ) c).indicator (fun r => g (a * r)) r :=
        (lintegral_indicator measurableSet_Ioc _).symm
    _ = ∫⁻ r, (Ioc (0 : ℝ) (a * c)).indicator g (a * r) := lintegral_congr hset
    _ = ∫⁻ D, (Ioc (0 : ℝ) (a * c)).indicator g D ∂(volume.map (fun r : ℝ => a * r)) :=
        (lintegral_map hind hm).symm
    _ = ∫⁻ D, (Ioc (0 : ℝ) (a * c)).indicator g D ∂(ENNReal.ofReal |a⁻¹| • volume) := by
        rw [Real.map_volume_mul_left ha.ne']
    _ = ENNReal.ofReal |a⁻¹| * ∫⁻ D, (Ioc (0 : ℝ) (a * c)).indicator g D :=
        lintegral_smul_measure _ _
    _ = ENNReal.ofReal a⁻¹ * ∫⁻ D in Ioc (0 : ℝ) (a * c), g D := by
        rw [abs_of_pos (inv_pos.2 ha), lintegral_indicator measurableSet_Ioc]

/-- The integral of the residue integrand over the rotation, for a class whose gap lies in
`[0, N]`. -/
theorem lintegral_residueIntegrand_eq (φ : ℝ → (Fin (N : ℕ) → ℝ) → ℝ≥0∞)
    (hφ : Measurable (fun p : ℝ × (Fin (N : ℕ) → ℝ) => φ p.1 p.2)) (i : ℤ)
    (h : Fin (N : ℕ) → ℝ) (hc0 : 0 ≤ gapOf h i / ((N : ℕ) : ℝ))
    (hc1 : gapOf h i / ((N : ℕ) : ℝ) ≤ 1) :
    ∫⁻ u, residueIntegrand φ i u h ∂(volume : Measure UnitAddCircle) =
      ENNReal.ofReal (((N : ℕ) : ℝ)⁻¹) * residueWeight φ i h := by
  have hNpos : (0 : ℝ) < ((N : ℕ) : ℝ) := by exact_mod_cast N.pos
  have hsec : Measurable (fun D : ℝ => φ D (gapPositions h i)) :=
    hφ.comp (measurable_id.prodMk measurable_const)
  have hNc : ((N : ℕ) : ℝ) * (gapOf h i / ((N : ℕ) : ℝ)) = gapOf h i := by
    field_simp
  have hH : Measurable (fun r : ℝ => if r < gapOf h i / ((N : ℕ) : ℝ) then
      φ (((N : ℕ) : ℝ) * r) (gapPositions h i) else 0) :=
    Measurable.ite (measurableSet_lt measurable_id measurable_const)
      (hsec.comp (measurable_const.mul measurable_id)) measurable_const
  have hfun : ∀ u : UnitAddCircle, residueIntegrand φ i u h =
      (if negRep u < gapOf h i / ((N : ℕ) : ℝ) then
        φ (((N : ℕ) : ℝ) * negRep u) (gapPositions h i) else 0) := fun u => rfl
  simp_rw [hfun]
  rw [lintegral_circle_negRep (fun r : ℝ => if r < gapOf h i / ((N : ℕ) : ℝ) then
      φ (((N : ℕ) : ℝ) * r) (gapPositions h i) else 0) hH]
  rw [lintegral_Ico_ite_eq (gapOf h i / ((N : ℕ) : ℝ)) hc0 hc1
    (fun r => φ (((N : ℕ) : ℝ) * r) (gapPositions h i))]
  rw [Measure.restrict_congr_set Ico_ae_eq_Ioc,
    lintegral_Ioc_mul ((N : ℕ) : ℝ) _ hNpos (fun D => φ D (gapPositions h i)) hsec, hNc]
  rfl

/-! ### The residue classes as a whole -/

/-- The residue-class integral is measurable in the rotation and the gap vector. -/
theorem measurable_residueIntegrand_comp (φ : ℝ → (Fin (N : ℕ) → ℝ) → ℝ≥0∞)
    (hφ : Measurable (fun p : ℝ × (Fin (N : ℕ) → ℝ) => φ p.1 p.2)) (i : ℤ) :
    Measurable (fun X : Configuration N => residueIntegrand φ i (cyclicLift X i : UnitAddCircle)
      (gapVector X)) :=
  (measurable_residueIntegrand φ hφ i).comp
    ((measurable_coe_circle.comp (measurable_cyclicLift i)).prodMk (measurable_gapVector N))

/-- The shift of the gap vector to the class `i` moves the residue weight to class zero. -/
theorem residueWeight_shiftFin (φ : ℝ → (Fin (N : ℕ) → ℝ) → ℝ≥0∞) (i : ℤ)
    (h : Fin (N : ℕ) → ℝ) :
    residueWeight φ 0 (shiftFin N i h) = residueWeight φ i h := by
  unfold residueWeight
  have hg : gapOf (shiftFin N i h) 0 = gapOf h i := by
    rw [gapOf_shiftFin, add_zero]
  have hp : gapPositions (shiftFin N i h) 0 = gapPositions h i := by
    funext k
    unfold gapPositions
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [gapOf_shiftFin, zero_add]
  rw [hg, hp]

/-- The class-`i` integral of the joint law, after the rotation and the dilation. -/
theorem lintegral_residue_eq (P : Parameters) (φ : ℝ → (Fin (N : ℕ) → ℝ) → ℝ≥0∞)
    (hφ : Measurable (fun p : ℝ × (Fin (N : ℕ) → ℝ) => φ p.1 p.2)) (i : ℤ) :
    ∫⁻ X, residueIntegrand φ i (cyclicLift X i : UnitAddCircle) (gapVector X)
        ∂(gibbsMeasure P N) =
      ENNReal.ofReal (((N : ℕ) : ℝ)⁻¹) * ∫⁻ X, residueWeight φ i (gapVector X)
        ∂(gibbsMeasure P N) := by
  have := (modelWellDefined P N).2.2
  have hG := measurable_residueIntegrand φ hφ i
  have hNpos : (0 : ℝ) < ((N : ℕ) : ℝ) := by exact_mod_cast N.pos
  have hmapX : Measurable (fun X : Configuration N =>
      (((cyclicLift X i : ℝ) : UnitAddCircle), gapVector X)) :=
    (measurable_coe_circle.comp (measurable_cyclicLift i)).prodMk (measurable_gapVector N)
  have hsupp : ∀ᵐ h ∂((gibbsMeasure P N).map gapVector),
      0 ≤ gapOf h i / ((N : ℕ) : ℝ) ∧ gapOf h i / ((N : ℕ) : ℝ) ≤ 1 := by
    have hset : MeasurableSet {h : Fin (N : ℕ) → ℝ |
        0 ≤ gapOf h i / ((N : ℕ) : ℝ) ∧ gapOf h i / ((N : ℕ) : ℝ) ≤ 1} :=
      (measurableSet_le measurable_const (measurable_gapOf_div i)).inter
        (measurableSet_le (measurable_gapOf_div i) measurable_const)
    refine (ae_map_iff (measurable_gapVector N).aemeasurable hset).2 (ae_of_all _ fun X => ?_)
    show 0 ≤ gapOf (gapVector X) i / ((N : ℕ) : ℝ) ∧ gapOf (gapVector X) i / ((N : ℕ) : ℝ) ≤ 1
    rw [← gap_eq_gapOf_gapVector]
    exact ⟨div_nonneg (gap_pos X i).le hNpos.le, (div_le_one hNpos).2 (gap_le_N X i)⟩
  calc ∫⁻ X, residueIntegrand φ i (cyclicLift X i : UnitAddCircle) (gapVector X)
        ∂(gibbsMeasure P N)
      = ∫⁻ p, residueIntegrand φ i p.1 p.2 ∂((gibbsMeasure P N).map
          (fun X : Configuration N => (((cyclicLift X i : ℝ) : UnitAddCircle), gapVector X))) :=
        (lintegral_map hG hmapX).symm
    _ = ∫⁻ p, residueIntegrand φ i p.1 p.2 ∂((volume : Measure UnitAddCircle).prod
          ((gibbsMeasure P N).map gapVector)) := by
        rw [map_cyclicLift_gapVector_gibbsMeasure P N i]
    _ = ∫⁻ h, ∫⁻ u, residueIntegrand φ i u h ∂(volume : Measure UnitAddCircle)
          ∂((gibbsMeasure P N).map gapVector) :=
        lintegral_prod_symm _ hG.aemeasurable
    _ = ∫⁻ h, ENNReal.ofReal (((N : ℕ) : ℝ)⁻¹) * residueWeight φ i h
          ∂((gibbsMeasure P N).map gapVector) := by
        refine lintegral_congr_ae ?_
        filter_upwards [hsupp] with h hh
        exact lintegral_residueIntegrand_eq φ hφ i h hh.1 hh.2
    _ = ENNReal.ofReal (((N : ℕ) : ℝ)⁻¹) * ∫⁻ h, residueWeight φ i h
          ∂((gibbsMeasure P N).map gapVector) :=
        lintegral_const_mul _ (measurable_residueWeight φ hφ i)
    _ = ENNReal.ofReal (((N : ℕ) : ℝ)⁻¹) * ∫⁻ X, residueWeight φ i (gapVector X)
          ∂(gibbsMeasure P N) := by
        rw [lintegral_map (measurable_residueWeight φ hφ i) (measurable_gapVector N)]

/-! ### The joint law -/

/-- **Joint law** (the rotation part of Lemma 5.2). Let `J` be the label of the particle
preceding the origin, `D = -N x_J` and `y_k = x_{J+k} - x_J`. For every measurable `φ ≥ 0` on
`ℝ × (Fin N → ℝ)`, `E φ(D, y) = E_{μ*} ∫_{0<D<w(y)} φ(D, y) dD`, where `μ*` is the anchored law
`rotAnchoredLaw P N` and `w(y) = N y_2` is `sizeBiasWeight N hN y`. -/
theorem joint_law_rotAnchoredLaw (P : Parameters) (N : ℕ+) (hN : 2 ≤ (N : ℕ))
    (φ : ℝ → (Fin (N : ℕ) → ℝ) → ℝ≥0∞)
    (hφ : Measurable (fun p : ℝ × (Fin (N : ℕ) → ℝ) => φ p.1 p.2)) :
    ∫⁻ X, φ (originD X) (originPos X) ∂(gibbsMeasure P N) =
      ∫⁻ y, (∫⁻ D in Ioo (0 : ℝ) (sizeBiasWeight N hN y), φ D y) ∂(rotAnchoredLaw P N) := by
  have := (modelWellDefined P N).2.2
  have hNr : (0 : ℝ) < ((N : ℕ) : ℝ) := by exact_mod_cast N.pos
  have hK : ((N : ℕ) : ℝ≥0∞) * ENNReal.ofReal (((N : ℕ) : ℝ)⁻¹) = 1 := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
      mul_inv_cancel₀ hNr.ne', ENNReal.ofReal_one]
  -- the origin term is the sum over the residue classes
  have hLHS : ∫⁻ X, φ (originD X) (originPos X) ∂(gibbsMeasure P N) =
      ∑ i : Fin (N : ℕ), ENNReal.ofReal (((N : ℕ) : ℝ)⁻¹) *
        ∫⁻ X, residueWeight φ ((i : ℕ) : ℤ) (gapVector X) ∂(gibbsMeasure P N) := by
    rw [lintegral_congr (originTerm_eq_sum φ), lintegral_finsetSum]
    · refine Finset.sum_congr rfl fun i _ => ?_
      exact lintegral_residue_eq P φ hφ _
    · intro i _
      exact measurable_residueIntegrand_comp φ hφ _
  -- each class has the expectation of class zero
  have hshift : ∀ i : Fin (N : ℕ), ∫⁻ X, residueWeight φ ((i : ℕ) : ℤ) (gapVector X)
      ∂(gibbsMeasure P N) = ∫⁻ X, residueWeight φ 0 (gapVector X) ∂(gibbsMeasure P N) := by
    intro i
    have h := lintegral_shiftFin_gapVector P hN (residueWeight φ 0)
      (measurable_residueWeight φ hφ 0) (i : ℕ)
    rw [← h]
    refine lintegral_congr fun X => ?_
    rw [residueWeight_shiftFin]
  -- the right-hand side is the class-zero integral over the anchored law
  have hRHS : ∫⁻ y, (∫⁻ D in Ioo (0 : ℝ) (sizeBiasWeight N hN y), φ D y) ∂(rotAnchoredLaw P N) =
      ∫⁻ X, residueWeight φ 0 (gapVector X) ∂(gibbsMeasure P N) := by
    have hIoo : ∀ y : Fin (N : ℕ) → ℝ, ∫⁻ D in Ioo (0 : ℝ) (sizeBiasWeight N hN y), φ D y =
        ∫⁻ D in Ioc (0 : ℝ) (sizeBiasWeight N hN y), φ D y := fun y => by
      rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    rw [lintegral_congr hIoo]
    unfold rotAnchoredLaw
    rw [lintegral_map (measurable_lintegral_Ioc_param (fun y => sizeBiasWeight N hN y)
      (measurable_sizeBiasWeight N hN) (fun q => φ q.2 q.1) (hφ.comp measurable_swap))
      (measurable_rotAnchorVec N)]
    refine lintegral_congr fun X => ?_
    have hw : sizeBiasWeight N hN (rotAnchorVec N X) = gapOf (gapVector X) 0 := by
      rw [sizeBiasWeight_anchorVec, gap_eq_gapOf_gapVector]
    have hv : rotAnchorVec N X = gapPositions (gapVector X) 0 := by
      funext k
      have h := cyclicLift_sub_eq_gapPositions X 0 k
      rw [zero_add] at h
      exact h
    rw [hw, hv]
    rfl
  rw [hLHS, hRHS]
  simp_rw [hshift]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc, hK,
    one_mul]

end Riesz1

end

end
