/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Kernel.AdmissibleExamplesCompactTransport
public import Riesz1.Kernel.AdmissibleExamplesCompactPrimitive
public import Riesz1.Kernel.TransportScaledMain
public import Riesz1.Bridges.IndicatorArc
public import Riesz1.Frozen.Admissible

/-!
# Admissibility of a fixed arc on enlarged circles

Compact branch: an arc indicator `arcIndicator c a` whose closure lies in
`(-1/2, 1/2)` (that is, `|c| + a < 1/2`) satisfies `Admissible` at every shrinking scale
sequence `ℓ_N → 0`, with the exponent `α = 0`. The `TestData` are fixed before the scale
sequence. The primitive and transport data of each enlarged circle are uniform in its length.
-/

public section

open MeasureTheory Set Filter Topology
open scoped ContDiff Real

namespace Riesz1

/-- The distance between the classes of two reals on the circle of length `L` is the distance
from their difference to the lattice `L ℤ`. -/
lemma dist_coe_eq_latticeDist {L : ℝ} (hL : 0 < L) (x y : ℝ) :
    dist (x : AddCircle L) (y : AddCircle L) = latticeDist L (x - y) := by
  have : Fact (0 < L) := ⟨hL⟩
  rw [dist_eq_norm, ← AddCircle.coe_sub, AddCircle.norm_eq]
  unfold latticeDist
  rw [inv_mul_eq_div, mul_comm]

/-- Reals at distance less than one and not equal have distinct classes on a circle of length
`L ≥ 1`. -/
lemma coe_ne_of_abs_sub_lt {L u v : ℝ} (hL : 1 ≤ L) (huv : |u - v| < 1) (hne : u ≠ v) :
    (u : AddCircle L) ≠ (v : AddCircle L) := by
  have : Fact (0 < L) := ⟨by linarith⟩
  intro h
  have h0 : ((u - v : ℝ) : AddCircle L) = 0 := by rw [AddCircle.coe_sub, h, sub_self]
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff L).1 h0
  rw [zsmul_eq_mul] at hn
  have hlt := abs_lt.1 huv
  rcases lt_trichotomy n 0 with hn0 | hn0 | hn0
  · have hn1 : (n : ℝ) ≤ -1 := by exact_mod_cast (show n ≤ -1 by omega)
    nlinarith
  · subst hn0
    simp only [Int.cast_zero, zero_mul] at hn
    exact hne (by linarith)
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    nlinarith

/-- A real offset from a mark class gives a point off every lattice translate of the mark. -/
lemma not_lattice_of_coe_ne (ℓ : Length) {x y : ℝ} (h : (x : Circle ℓ) ≠ (y : Circle ℓ)) :
    ∀ k : ℤ, x - y ≠ k * ℓ.val := by
  intro k hk
  apply h
  have hx : x = y + k * ℓ.val := by linarith
  rw [hx, coe_add_int_mul_eq]

/-- For `1/2 ≤ |y| < 1 - a`, the distance from `y` to the nearest integer is at least `a`. -/
lemma le_abs_sub_round_of_half_le {a y : ℝ} (ha0 : 0 < a)
    (hy1 : 1 / 2 ≤ |y|) (hy2 : |y| < 1 - a) :
    a ≤ |y - round y| := by
  have hlo := (abs_lt.1 hy2).1
  have hhi := (abs_lt.1 hy2).2
  rcases le_or_gt 0 y with hy0 | hy0
  · have hyh : 1 / 2 ≤ y := by rw [abs_of_nonneg hy0] at hy1; exact hy1
    have hr : round y = 1 := by
      rw [round_eq, Int.floor_eq_iff]
      constructor
      · push_cast; linarith
      · push_cast; linarith
    rw [hr, Int.cast_one, abs_of_nonpos (by linarith)]
    linarith
  · rw [abs_of_neg hy0] at hy1
    rcases eq_or_lt_of_le (show 1 / 2 ≤ -y by linarith) with heq | hlt
    · have hyn : y = -(1 / 2) := by linarith
      have hr : round y = 0 := by
        rw [round_eq, Int.floor_eq_iff]
        constructor
        · rw [hyn]; norm_num
        · rw [hyn]; norm_num
      rw [hr, Int.cast_zero, sub_zero, abs_of_neg hy0]
      linarith
    · have hr : round y = -1 := by
        rw [round_eq, Int.floor_eq_iff]
        constructor
        · push_cast; linarith
        · push_cast; linarith
      rw [hr, Int.cast_neg, Int.cast_one, sub_neg_eq_add, abs_of_nonneg (by linarith)]
      linarith

/-- The residue of `y` modulo the lattice is below `a` exactly when `|y| < a`, for `|y| < 1 - a`. -/
lemma abs_sub_round_lt_iff {a y : ℝ} (ha0 : 0 < a) (hy : |y| < 1 - a) :
    |y - round y| < a ↔ |y| < a := by
  rcases lt_or_ge |y| (1 / 2) with h | h
  · have hr : round y = 0 := round_eq_zero_iff.2 ⟨(abs_lt.1 h).1.le, (abs_lt.1 h).2⟩
    rw [hr, Int.cast_zero, sub_zero]
  · constructor
    · intro h'
      exact absurd h' (not_lt.2 (le_abs_sub_round_of_half_le ha0 h hy))
    · intro h'
      exfalso
      linarith

/-- For `|c| + a < 1/2` and `|x| < 1/2`, the arc indicator about `c` is the indicator of
`(c - a, c + a)` at `x`. -/
lemma arcIndicator_real_eq_indicator {c a x : ℝ} (ha0 : 0 < a) (hca : |c| + a < 1 / 2)
    (hx : |x| < 1 / 2) :
    arcIndicator (c : UnitAddCircle) a (x : UnitAddCircle) =
      (Ioo (c - a) (c + a)).indicator (fun _ => (1 : ℝ)) x := by
  have hac : a < 1 / 2 := by linarith [abs_nonneg c]
  have hbound : |x - c| < 1 - a := by linarith [abs_sub x c]
  have hmemIoo : x ∈ Ioo (c - a) (c + a) ↔ |x - c| < a := by
    rw [Set.mem_Ioo, abs_lt]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  have hround := abs_sub_round_lt_iff ha0 hbound
  rw [arcIndicator_eq_indicatorArc_sub hac, ← AddCircle.coe_sub]
  unfold indicatorArc
  by_cases hA : |(x - c) - round (x - c)| < a
  · have hB : |x - c| < a := hround.1 hA
    rw [Set.indicator_of_mem ((mem_arcImage_iff_abs_lt hac (x - c)).2 hA),
      Set.indicator_of_mem (hmemIoo.2 hB)]
  · have hB : ¬ |x - c| < a := fun h => hA (hround.2 h)
    rw [Set.indicator_of_notMem (fun h => hA ((mem_arcImage_iff_abs_lt hac (x - c)).1 h)),
      Set.indicator_of_notMem (fun h => hB (hmemIoo.1 h))]

/-- The zero extension of the arc profile about `c` is the indicator of `(c - a, c + a)` on the
real line. -/
lemma zeroExtension_arcIndicator {c a : ℝ} (ha0 : 0 < a) (hca : |c| + a < 1 / 2) (x : ℝ) :
    zeroExtension ⟨arcIndicator (c : UnitAddCircle) a, memLp_arcIndicator (c : UnitAddCircle) a⟩ x =
      (Ioo (c - a) (c + a)).indicator (fun _ => (1 : ℝ)) x := by
  unfold zeroExtension
  by_cases hx : |x| < 1 / 2
  · simp only [hx, ↓reduceIte]
    exact arcIndicator_real_eq_indicator ha0 hca hx
  · simp only [hx, ↓reduceIte]
    have hout : x ∉ Ioo (c - a) (c + a) := fun hm => hx (by
      rw [abs_lt]
      constructor <;> linarith [hm.1, hm.2, neg_abs_le c, le_abs_self c])
    rw [Set.indicator_of_notMem hout]

/-- A Hölder bound with constant `4`, from a uniform bound by `2` and a `1`-Lipschitz estimate. -/
lemma holder_of_lipschitz_bounded {X : Type*} [MetricSpace X] (f : X → ℝ) {M r : ℝ}
    (hM : ∀ x, |f x| ≤ M) (hM2 : M ≤ 2) (hr0 : 0 < r) (hr1 : r ≤ 1)
    (hL : ∀ x y, |f x - f y| ≤ dist x y) (x y : X) :
    |f x - f y| ≤ 4 * dist x y ^ r := by
  have hd0 : 0 ≤ dist x y := dist_nonneg
  have hpos : 0 ≤ dist x y ^ r := Real.rpow_nonneg hd0 r
  rcases le_total (dist x y) 1 with h | h
  · have h2 : dist x y ≤ dist x y ^ r := by
      rcases eq_or_lt_of_le hd0 with h0 | h0
      · rw [← h0, Real.zero_rpow hr0.ne']
      · calc dist x y = dist x y ^ (1 : ℝ) := (Real.rpow_one _).symm
          _ ≤ dist x y ^ r := Real.rpow_le_rpow_of_exponent_ge h0 h hr1
    linarith [hL x y]
  · have h1 : 1 ≤ dist x y ^ r := Real.one_le_rpow h hr0.le
    have h2 : |f x - f y| ≤ 4 := by
      calc |f x - f y| ≤ |f x| + |f y| := abs_sub _ _
        _ ≤ M + M := add_le_add (hM x) (hM y)
        _ ≤ 4 := by linarith
    linarith

/-- A bounded continuous function on a circle is square integrable. -/
lemma memLp_of_bounded_continuous (ℓ : Length) {G : Circle ℓ → ℝ} (hG : Continuous G) {B : ℝ}
    (hB : ∀ z, |G z| ≤ B) : MemLp (fun z => (G z : ℂ)) 2 (arclength ℓ) := by
  have : Fact (0 < ℓ.val) := ⟨ℓ.property⟩
  refine MemLp.of_bound (Complex.continuous_ofReal.comp hG).aestronglyMeasurable |B| ?_
  refine ae_of_all _ fun z => ?_
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact (hB z).trans (le_abs_self B)

/-- The primitive regularity of the compact arc on the enlarged circle `observationLength ell`:
a Hölder primitive with exponent `1 - s + s/2` and constant `4`, independent of `ell`. -/
lemma compact_primitiveRegularity (P : Parameters) {c a : ℝ} (ha0 : 0 < a)
    (hca : |c| + a < 1 / 2) (ell : Scale) :
    PrimitiveRegularity (observationLength ell) (P.val.2 / 2) P.val.2 4
      ⟨periodizedProfile ⟨arcIndicator (c : UnitAddCircle) a, memLp_arcIndicator (c : UnitAddCircle) a⟩
        (observationLength ell),
        periodizedProfileL2 ⟨arcIndicator (c : UnitAddCircle) a, memLp_arcIndicator (c : UnitAddCircle) a⟩
          ell⟩ := by
  have hℓ : 1 ≤ (observationLength ell).val := (one_le_inv₀ ell.property.1).mpr ell.property.2
  have : Fact (0 < (observationLength ell).val) := ⟨(observationLength ell).property⟩
  have hac : a < 1 / 2 := by linarith [abs_nonneg c]
  have hu : -(1 / 2) < c - a := by linarith [neg_abs_le c]
  have hv : c + a < 1 / 2 := by linarith [le_abs_self c]
  have huv : c - a < c + a := by linarith
  obtain ⟨G, hGc, hGb, hGL, hF⟩ :=
    exists_compact_indicator_primitive (observationLength ell) hℓ hu huv hv
  have hpp : ∀ z : Circle (observationLength ell),
      periodizedProfile ⟨arcIndicator (c : UnitAddCircle) a, memLp_arcIndicator (c : UnitAddCircle) a⟩
        (observationLength ell) z =
        periodicIndicator (observationLength ell) (c - a) (c + a) z := by
    intro z
    rw [periodizedProfile_eq_zeroExtension _ _ hℓ z, zeroExtension_arcIndicator ha0 hca]
    rfl
  have hM : 2 * (c + a - (c - a)) ≤ 2 := by linarith
  have hr0 : 0 < 1 - P.val.2 + P.val.2 / 2 := by linarith [P.property.2.2]
  have hr1 : 1 - P.val.2 + P.val.2 / 2 ≤ 1 := by linarith [P.property.2.1]
  refine ⟨⟨G, memLp_of_bounded_continuous _ hGc (B := 2) fun z => (hGb z).trans hM⟩, ?_, ?_⟩
  · exact ⟨hGc, fun z => (hGb z).trans (by linarith),
      fun z w => holder_of_lipschitz_bounded G hGb hM hr0 hr1 hGL z w⟩
  · intro k hk
    show (2 * Real.pi * Complex.I * (k : ℂ) / ((observationLength ell).val : ℂ)) *
        fourierCoeff (fun z => (G z : ℂ)) k =
        fourierCoeff (fun z => ((periodizedProfile
          ⟨arcIndicator (c : UnitAddCircle) a, memLp_arcIndicator (c : UnitAddCircle) a⟩
          (observationLength ell) z : ℝ) : ℂ)) k
    rw [hF k hk]
    simp only [hpp]

/-- The transport regularity of the compact arc on the enlarged circle `observationLength ell`,
with the uniform constant `C` of the second derivative bound and the two marks `c - a, c + a`. -/
lemma compact_transportRegularity (P : Parameters) {c a : ℝ} (ha0 : 0 < a)
    (hca : |c| + a < 1 / 2) (ell : Scale) {C : ℝ} (hC : 0 < C)
    (hbound : ∀ (L u v : ℝ), 1 ≤ L → -(1 / 2) < u → u < v → v < 1 / 2 → ∀ y : ℝ,
      (∀ k : ℤ, y - u ≠ k * L) → (∀ k : ℤ, y - v ≠ k * L) →
        |deriv (deriv (transportConv P.val.1 P.val.2 L
          ((Ioo u v).indicator (fun _ => (1 : ℝ))))) y| ≤
            C * (latticeDist L (y - u) ^ (P.val.2 - 2) + latticeDist L (y - v) ^ (P.val.2 - 2)) ∧
          (1 ≤ latticeDist L y →
            |deriv (deriv (transportConv P.val.1 P.val.2 L
              ((Ioo u v).indicator (fun _ => (1 : ℝ))))) y| ≤
                C * latticeDist L y ^ (P.val.2 - 3))) :
    TransportRegularity P (observationLength ell)
      ⟨periodizedProfile ⟨arcIndicator (c : UnitAddCircle) a, memLp_arcIndicator (c : UnitAddCircle) a⟩
        (observationLength ell),
        periodizedProfileL2 ⟨arcIndicator (c : UnitAddCircle) a, memLp_arcIndicator (c : UnitAddCircle) a⟩
          ell⟩
      ⟨2, by norm_num⟩ ![c - a, c + a] 0 C := by
  have : Fact (0 < (observationLength ell).val) := ⟨(observationLength ell).property⟩
  have hL : 1 ≤ (observationLength ell).val := (one_le_inv₀ ell.property.1).mpr ell.property.2
  have hL0 : 0 < (observationLength ell).val := by linarith
  have hu : -(1 / 2) < c - a := by linarith [neg_abs_le c]
  have huv : c - a < c + a := by linarith
  have hv : c + a < 1 / 2 := by linarith [le_abs_self c]
  have hs0 : 0 < P.val.2 := P.property.2.1
  have hs1 : P.val.2 < 1 := P.property.2.2
  set p : Profile := ⟨arcIndicator (c : UnitAddCircle) a, memLp_arcIndicator (c : UnitAddCircle) a⟩
    with hp
  have hzero : zeroExtension p = (Ioo (c - a) (c + a)).indicator (fun _ => (1 : ℝ)) :=
    funext (zeroExtension_arcIndicator ha0 hca)
  obtain ⟨hL2, hcoef⟩ := (transport_kernel_scaled P p ell).2.2.1
  have hinj : Function.Injective (fun j : Fin ((⟨2, by norm_num⟩ : ℕ+) : ℕ) =>
      (((![c - a, c + a] : Fin 2 → ℝ) j : ℝ) : Circle (observationLength ell))) := by
    have hcoe := coe_ne_of_abs_sub_lt (L := (observationLength ell).val) hL
      (by rw [abs_lt]; constructor <;> linarith) (ne_of_lt huv)
    intro i j hij
    fin_cases i <;> fin_cases j <;> first | rfl | exact absurd hij hcoe | exact absurd hij.symm hcoe
  refine ⟨hinj, ⟨⟨fun z => transportConv P.val.1 P.val.2 (observationLength ell).val (zeroExtension p)
    (centralRep (observationLength ell) z), hL2⟩, hcoef, ?_⟩⟩
  intro lift x hx
  have hlift : lift = transportConv P.val.1 P.val.2 (observationLength ell).val
      ((Ioo (c - a) (c + a)).indicator (fun _ => (1 : ℝ))) := by
    funext y
    show transportConv P.val.1 P.val.2 (observationLength ell).val (zeroExtension p)
      (centralRep (observationLength ell) (y : Circle (observationLength ell))) = _
    rw [transportConv_centralRep, hzero]
  have hx0 : (x : Circle (observationLength ell)) ≠ ((c - a : ℝ) : Circle (observationLength ell)) :=
    hx (0 : Fin 2)
  have hx1 : (x : Circle (observationLength ell)) ≠ ((c + a : ℝ) : Circle (observationLength ell)) :=
    hx (1 : Fin 2)
  have hyu : ∀ k : ℤ, x - (c - a) ≠ k * (observationLength ell).val :=
    not_lattice_of_coe_ne _ hx0
  have hyv : ∀ k : ℤ, x - (c + a) ≠ k * (observationLength ell).val :=
    not_lattice_of_coe_ne _ hx1
  have hcd : ContDiffAt ℝ 2 (transportConv P.val.1 P.val.2 (observationLength ell).val
      ((Ioo (c - a) (c + a)).indicator (fun _ => (1 : ℝ)))) x :=
    contDiffAt_transportConv_indicator hs0 hs1 hL hu huv hv hyu hyv
  obtain ⟨hnear, hfar⟩ := hbound (observationLength ell).val (c - a) (c + a) hL hu huv hv x hyu hyv
  rw [hlift]
  refine ⟨hcd, ?_⟩
  have hd0 : dist (x : Circle (observationLength ell)) 0 =
      latticeDist (observationLength ell).val x := by
    have h := dist_coe_eq_latticeDist hL0 x 0
    simp only [sub_zero, AddCircle.coe_zero] at h
    exact h
  have hdu : dist (x : Circle (observationLength ell)) ((c - a : ℝ) : Circle (observationLength ell)) =
      latticeDist (observationLength ell).val (x - (c - a)) :=
    dist_coe_eq_latticeDist hL0 x (c - a)
  have hdv : dist (x : Circle (observationLength ell)) ((c + a : ℝ) : Circle (observationLength ell)) =
      latticeDist (observationLength ell).val (x - (c + a)) :=
    dist_coe_eq_latticeDist hL0 x (c + a)
  have e1 : (-2 + P.val.2 - 0 : ℝ) = P.val.2 - 2 := by ring
  have e2 : (-3 + P.val.2 : ℝ) = P.val.2 - 3 := by ring
  simp only [hd0, e1, e2]
  have hdu0 : dist (x : Circle (observationLength ell))
      (((![c - a, c + a] : Fin 2 → ℝ) (0 : Fin 2) : ℝ) : Circle (observationLength ell)) =
      latticeDist (observationLength ell).val (x - (c - a)) := hdu
  have hdv1 : dist (x : Circle (observationLength ell))
      (((![c - a, c + a] : Fin 2 → ℝ) (1 : Fin 2) : ℝ) : Circle (observationLength ell)) =
      latticeDist (observationLength ell).val (x - (c + a)) := hdv
  have hF0 : 0 ≤ latticeDist (observationLength ell).val x ^ (P.val.2 - 3) :=
    Real.rpow_nonneg (latticeDist_nonneg_transport _ _) _
  by_cases h1 : latticeDist (observationLength ell).val x ≤ 1
  · simp only [h1, ↓reduceIte]
    by_cases h2 : 1 ≤ latticeDist (observationLength ell).val x
    · simp only [h2, ↓reduceIte]
      refine le_trans hnear (mul_le_mul_of_nonneg_left ?_ hC.le)
      show _ ≤ (∑ j : Fin 2, dist (x : Circle (observationLength ell))
        (((![c - a, c + a] : Fin 2 → ℝ) j : ℝ) : Circle (observationLength ell)) ^ (P.val.2 - 2)) +
        latticeDist (observationLength ell).val x ^ (P.val.2 - 3)
      rw [Fin.sum_univ_two, hdu0, hdv1]
      linarith [hF0]
    · simp only [h2, ↓reduceIte, add_zero]
      refine le_trans hnear (mul_le_mul_of_nonneg_left ?_ hC.le)
      show _ ≤ ∑ j : Fin 2, dist (x : Circle (observationLength ell))
        (((![c - a, c + a] : Fin 2 → ℝ) j : ℝ) : Circle (observationLength ell)) ^ (P.val.2 - 2)
      rw [Fin.sum_univ_two, hdu0, hdv1]
  · have h2 : 1 ≤ latticeDist (observationLength ell).val x := le_of_lt (not_le.1 h1)
    simp only [h1, h2, ↓reduceIte, zero_add]
    exact hfar h2

/-- **Compact branch.** An arc indicator `arcIndicator c a` with `|c| + a < 1/2`,
so that its support lies in `(-1/2, 1/2)`, is admissible on enlarged circles: there is one
`TestData` for every shrinking scale sequence, with exponent `α = 0`. -/
theorem admissible_compact_arcIndicator (P : Parameters) {c a : ℝ} (ha0 : 0 < a)
    (hca : |c| + a < 1 / 2) :
    ∃ d : TestData, ∀ ell : Scales,
      Tendsto (fun n : ℕ => (ell ⟨n + 1, Nat.succ_pos n⟩).val) atTop (𝓝 0) →
        Admissible P ⟨arcIndicator (c : UnitAddCircle) a, memLp_arcIndicator (c : UnitAddCircle) a⟩
          ell 0 d := by
  obtain ⟨hβ, hs0, hs1⟩ := P.property
  obtain ⟨C, hC, hbound⟩ := transportConv_indicator_second_deriv_bound hβ hs0 hs1
  refine ⟨(P.val.2 / 2, 4, C, ⟨⟨2, by norm_num⟩, ![c - a, c + a]⟩), fun ell hell => ?_⟩
  have hu : -(1 / 2) < c - a := by linarith [neg_abs_le c]
  have huv : c - a < c + a := by linarith
  have hv : c + a < 1 / 2 := by linarith [le_abs_self c]
  refine ⟨by linarith, by linarith, by linarith, by linarith, by norm_num, hC,
    Or.inr ⟨?_, hell, fun N => ⟨compact_primitiveRegularity P ha0 hca (ell N),
      compact_transportRegularity P ha0 hca (ell N) hC hbound⟩⟩⟩
  refine ⟨|c| + a, by linarith [abs_nonneg c], by linarith, Filter.Eventually.of_forall fun x hx => ?_⟩
  rw [zeroExtension_arcIndicator ha0 hca x, Set.indicator_of_notMem]
  intro hm
  have : |x| < |c| + a := by
    rw [abs_lt]
    constructor <;> linarith [hm.1, hm.2, neg_abs_le c, le_abs_self c]
  linarith

end Riesz1

end
