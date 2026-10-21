/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Kernel.TransportKernel
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Smoothness and derivative bounds of the transport kernel off the integers

For `0 < s < 1`, the kernel `K_s = periodicKernel s` is `C^∞` at every point off the integers.
For `m ≥ 1`, its `m`-th derivative satisfies
`|K_s^{(m)}(t)| ≤ C dist(t, ℤ)^(s - 1 - m)` with `C` depending only on `s` and `m`.

The proof uses the decomposition, valid on the window `(-3/4, 3/4)` away from `0`,
`K_s = φ + ∑_{k ≥ 0} (φ(· - (k+1)) + φ(· + (k+1)))` with `φ = signPow s`. The paired terms are
smooth on the window and have the summable bounds `2 c_m (k + 1/4)^(s - 1 - m)` on their `m`-th
derivatives, where `c_m = |∏_{i<m} (s - 1 - i)|`. Hence the series can be differentiated term by
term. The singular part `φ` has explicit derivatives on `ℝ ∖ {0}`. Translation by an integer
and the choice of the nearest integer then give the statements at every non-integer point.
-/

public section

open MeasureTheory Set Filter Topology
open scoped ContDiff Real

namespace Riesz1

/-- The coefficient `|∏_{i<m} (s - 1 - i)|` of the `m`-th derivative of the signed power. -/
@[expose] noncomputable def derivCoeff (s : ℝ) (m : ℕ) : ℝ :=
  |∏ i ∈ Finset.range m, (s - 1 - (i : ℝ))|

lemma derivCoeff_nonneg (s : ℝ) (m : ℕ) : 0 ≤ derivCoeff s m := abs_nonneg _

/-- The paired kernel term `φ(t - (k+1)) + φ(t + (k+1))` for `φ = signPow s`. -/
@[expose] noncomputable def pairTerm (s t : ℝ) (k : ℕ) : ℝ :=
  signPow s (t - ((k : ℝ) + 1)) + signPow s (t + ((k : ℝ) + 1))

/-- The summable bound `∑_k 2 c_m (k + 1/4)^(s - 1 - m)` on the `m`-th derivatives of the paired
series. -/
@[expose] noncomputable def pairBound (s : ℝ) (m : ℕ) : ℝ :=
  ∑' k : ℕ, 2 * derivCoeff s m * ((k : ℝ) + 1 / 4) ^ (s - 1 - (m : ℝ))

lemma pairBound_nonneg (s : ℝ) (m : ℕ) : 0 ≤ pairBound s m :=
  tsum_nonneg fun k => mul_nonneg (mul_nonneg (by norm_num) (derivCoeff_nonneg s m))
    (Real.rpow_nonneg (by positivity) _)

/-- The series `∑_k (k + 1/4)^a` converges for `a < -1`. -/
lemma summable_shift_rpow {a : ℝ} (ha : a < -1) :
    Summable fun k : ℕ => ((k : ℝ) + 1 / 4) ^ a := by
  have h : Summable fun n : ℕ => (n : ℝ) ^ a := Real.summable_nat_rpow.2 ha
  have hsh : Summable fun k : ℕ => ((k : ℝ) + 1) ^ a := by
    have := (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ a) 1).2 h
    simpa using this
  refine Summable.of_nonneg_of_le (fun k => Real.rpow_nonneg (by positivity) _) (fun k => ?_)
    (hsh.mul_left ((1 / 4 : ℝ) ^ a))
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hle : ((k : ℝ) + 1) / 4 ≤ (k : ℝ) + 1 / 4 := by linarith
  have h1 : ((k : ℝ) + 1 / 4) ^ a ≤ (((k : ℝ) + 1) / 4) ^ a :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hle (by linarith)
  rw [show ((k : ℝ) + 1) / 4 = ((k : ℝ) + 1) * (1 / 4) by ring,
    Real.mul_rpow (by positivity) (by norm_num)] at h1
  exact h1.trans_eq (mul_comm _ _)

/-- The `m`-th derivative of `x ↦ x^a` on `(0, ∞)` is `∏_{i<m} (a - i) · x^(a - m)`. -/
lemma iteratedDeriv_rpow_of_pos (a : ℝ) (m : ℕ) :
    ∀ v : ℝ, 0 < v → iteratedDeriv m (fun x : ℝ => x ^ a) v =
      (∏ i ∈ Finset.range m, (a - (i : ℝ))) * v ^ (a - (m : ℝ)) := by
  induction m with
  | zero => intro v _; simp
  | succ m ih =>
    intro v hv
    have heq : iteratedDeriv m (fun x : ℝ => x ^ a) =ᶠ[𝓝 v]
        fun x => (∏ i ∈ Finset.range m, (a - (i : ℝ))) * x ^ (a - (m : ℝ)) := by
      filter_upwards [Ioi_mem_nhds hv] with x hx using ih x hx
    have hd : HasDerivAt (fun x : ℝ => (∏ i ∈ Finset.range m, (a - (i : ℝ))) * x ^ (a - (m : ℝ)))
        ((∏ i ∈ Finset.range m, (a - (i : ℝ))) * ((a - (m : ℝ)) * v ^ (a - (m : ℝ) - 1))) v :=
      (Real.hasDerivAt_rpow_const (Or.inl hv.ne')).const_mul _
    rw [iteratedDeriv_succ, heq.deriv_eq, hd.deriv, Finset.prod_range_succ,
      show a - ((m + 1 : ℕ) : ℝ) = a - (m : ℝ) - 1 by push_cast; ring]
    ring

/-- The `m`-th derivative of the signed power at `v ≠ 0` has modulus
`derivCoeff s m · |v|^(s - 1 - m)`. -/
lemma abs_iteratedDeriv_signPow (s : ℝ) (m : ℕ) {v : ℝ} (hv : v ≠ 0) :
    |iteratedDeriv m (signPow s) v| = derivCoeff s m * |v| ^ (s - 1 - (m : ℝ)) := by
  rcases lt_or_gt_of_ne hv with hneg | hpos
  · have hev : signPow s =ᶠ[𝓝 v] fun x => -((-x) ^ (s - 1)) := by
      filter_upwards [Iio_mem_nhds hneg] with x hx using signPow_of_neg hx
    have hc := iteratedDeriv_comp_neg m (fun y : ℝ => y ^ (s - 1)) v
    rw [hev.iteratedDeriv_eq m, iteratedDeriv_fun_neg, hc, smul_eq_mul,
      iteratedDeriv_rpow_of_pos (s - 1) m (-v) (by linarith), abs_neg]
    simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    rw [abs_of_pos (Real.rpow_pos_of_pos (show (0 : ℝ) < -v by linarith) (s - 1 - (m : ℝ))),
      abs_of_neg hneg, derivCoeff]
  · have hev : signPow s =ᶠ[𝓝 v] fun x => x ^ (s - 1) := by
      filter_upwards [Ioi_mem_nhds hpos] with x hx using signPow_of_pos hx
    rw [hev.iteratedDeriv_eq m, iteratedDeriv_rpow_of_pos (s - 1) m v hpos, abs_mul,
      abs_of_pos (Real.rpow_pos_of_pos hpos (s - 1 - (m : ℝ))), abs_of_pos hpos, derivCoeff]

/-- The signed power is smooth at every point off the origin. -/
lemma contDiffAt_signPow {s v : ℝ} {n : WithTop ℕ∞} (hv : v ≠ 0) :
    ContDiffAt ℝ n (signPow s) v := by
  rcases lt_or_gt_of_ne hv with hneg | hpos
  · have hev : signPow s =ᶠ[𝓝 v] fun x => -((-x) ^ (s - 1)) := by
      filter_upwards [Iio_mem_nhds hneg] with x hx using signPow_of_neg hx
    refine ContDiffAt.congr_of_eventuallyEq ?_ hev
    have h1 : ContDiffAt ℝ n (fun x : ℝ => x ^ (s - 1)) (-v) :=
      Real.contDiffAt_rpow_const_of_ne (neg_ne_zero.2 hv)
    have h2 : ContDiffAt ℝ n (fun x : ℝ => -x) v := contDiffAt_id.neg
    exact (ContDiffAt.comp (f := fun x : ℝ => -x) v h1 h2).neg
  · have hev : signPow s =ᶠ[𝓝 v] fun x => x ^ (s - 1) := by
      filter_upwards [Ioi_mem_nhds hpos] with x hx using signPow_of_pos hx
    exact (Real.contDiffAt_rpow_const_of_ne hv).congr_of_eventuallyEq hev

/-- The shifted signed power `z ↦ φ(z - c)` is smooth at `x` when `x - c ≠ 0`. -/
lemma contDiffAt_signPow_sub {s x c : ℝ} {n : WithTop ℕ∞} (hx : x - c ≠ 0) :
    ContDiffAt ℝ n (fun z : ℝ => signPow s (z - c)) x :=
  ContDiffAt.comp (f := fun z : ℝ => z - c) x (contDiffAt_signPow (s := s) (n := n) hx)
    (contDiffAt_id.sub contDiffAt_const)

/-- The shifted signed power `z ↦ φ(z + c)` is smooth at `x` when `x + c ≠ 0`. -/
lemma contDiffAt_signPow_add {s x c : ℝ} {n : WithTop ℕ∞} (hx : x + c ≠ 0) :
    ContDiffAt ℝ n (fun z : ℝ => signPow s (z + c)) x :=
  ContDiffAt.comp (f := fun z : ℝ => z + c) x (contDiffAt_signPow (s := s) (n := n) hx)
    (contDiffAt_id.add contDiffAt_const)

/-- The `m`-th derivative of the paired term at `x` with `|x| < 3/4` is the sum of the derivatives
of the two shifted signed powers. -/
lemma iteratedDeriv_pairTerm (s : ℝ) (m k : ℕ) {x : ℝ} (hx : |x| < 3 / 4) :
    iteratedDeriv m (fun z => pairTerm s z k) x =
      iteratedDeriv m (signPow s) (x - ((k : ℝ) + 1)) +
        iteratedDeriv m (signPow s) (x + ((k : ℝ) + 1)) := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hab := abs_lt.1 hx
  have h1 : x - ((k : ℝ) + 1) ≠ 0 := fun h => by linarith [hab.2]
  have h2 : x + ((k : ℝ) + 1) ≠ 0 := fun h => by linarith [hab.1]
  have hA : ContDiffAt ℝ (m : WithTop ℕ∞) (fun z => signPow s (z - ((k : ℝ) + 1))) x :=
    contDiffAt_signPow_sub (s := s) h1
  have hB : ContDiffAt ℝ (m : WithTop ℕ∞) (fun z => signPow s (z + ((k : ℝ) + 1))) x :=
    contDiffAt_signPow_add (s := s) h2
  rw [show (fun z => pairTerm s z k) =
      fun z => signPow s (z - ((k : ℝ) + 1)) + signPow s (z + ((k : ℝ) + 1)) from rfl,
    iteratedDeriv_fun_add hA hB, iteratedDeriv_comp_sub_const, iteratedDeriv_comp_add_const]

/-- The value bound of the paired term on the window `(-3/4, 3/4)`:
`|φ(x - (k+1)) + φ(x + (k+1))| ≤ 2 (k + 1/4)^(s - 2)`. -/
lemma abs_pairTerm_le {s x : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hx : |x| < 3 / 4) (k : ℕ) :
    |pairTerm s x k| ≤ 2 * ((k : ℝ) + 1 / 4) ^ (s - 2) := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hc : (0 : ℝ) < (k : ℝ) + 1 / 4 := by linarith
  have hab := abs_lt.1 hx
  have hodd : signPow s (x - ((k : ℝ) + 1)) = -signPow s (((k : ℝ) + 1) - x) := by
    rw [← signPow_neg']
    congr 1
    ring
  have h := abs_signPow_sub_le_of_le (s := s) (c := (k : ℝ) + 1 / 4)
    (a := ((k : ℝ) + 1) - x) (b := ((k : ℝ) + 1) + x) hs0 hs1 hc (by linarith) (by linarith)
  have hpair : pairTerm s x k =
      signPow s (((k : ℝ) + 1) + x) - signPow s (((k : ℝ) + 1) - x) := by
    unfold pairTerm
    rw [hodd, add_comm x ((k : ℝ) + 1)]
    ring
  have hp : 0 ≤ ((k : ℝ) + 1 / 4) ^ (s - 2) := Real.rpow_nonneg hc.le _
  have h3 : (1 - s) * (2 * |x|) ≤ 2 := by
    have : 0 ≤ 1 - s := by linarith
    nlinarith [abs_nonneg x, mul_nonneg hs0.le (abs_nonneg x)]
  rw [hpair]
  calc |signPow s (((k : ℝ) + 1) + x) - signPow s (((k : ℝ) + 1) - x)|
      ≤ (1 - s) * ((k : ℝ) + 1 / 4) ^ (s - 2) * |((k : ℝ) + 1) + x - (((k : ℝ) + 1) - x)| := h
    _ = ((1 - s) * (2 * |x|)) * ((k : ℝ) + 1 / 4) ^ (s - 2) := by
        rw [show ((k : ℝ) + 1) + x - (((k : ℝ) + 1) - x) = 2 * x by ring, abs_mul, abs_two]
        ring
    _ ≤ 2 * ((k : ℝ) + 1 / 4) ^ (s - 2) := mul_le_mul_of_nonneg_right h3 hp

/-- The paired terms are summable on the window. -/
lemma summable_pairTerm {s x : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hx : |x| < 3 / 4) :
    Summable fun k : ℕ => pairTerm s x k :=
  Summable.of_norm_bounded ((summable_shift_rpow (a := s - 2) (by linarith)).mul_left 2)
    (fun k => by rw [Real.norm_eq_abs]; exact abs_pairTerm_le hs0 hs1 hx k)

/-- The `m`-th derivative of the paired term is bounded on the window, for `m ≥ 1`. -/
lemma norm_iteratedDeriv_pairTerm_le {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {m : ℕ} (hm : 1 ≤ m)
    {x : ℝ} (hx : |x| < 3 / 4) (k : ℕ) :
    ‖iteratedDeriv m (fun z => pairTerm s z k) x‖ ≤
      2 * derivCoeff s m * ((k : ℝ) + 1 / 4) ^ (s - 1 - (m : ℝ)) := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hc : (0 : ℝ) < (k : ℝ) + 1 / 4 := by linarith
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hexp : s - 1 - (m : ℝ) ≤ 0 := by linarith
  have hab := abs_lt.1 hx
  have key : ∀ v : ℝ, (k : ℝ) + 1 / 4 ≤ |v| →
      |iteratedDeriv m (signPow s) v| ≤
        derivCoeff s m * ((k : ℝ) + 1 / 4) ^ (s - 1 - (m : ℝ)) := by
    intro v hv
    have hv0 : v ≠ 0 := fun h => by rw [h, abs_zero] at hv; linarith
    rw [abs_iteratedDeriv_signPow s m hv0]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hc hv hexp)
      (derivCoeff_nonneg s m)
  rw [iteratedDeriv_pairTerm s m k hx, Real.norm_eq_abs]
  have hA := key (x - ((k : ℝ) + 1)) (le_abs.2 (Or.inr (by linarith)))
  have hB := key (x + ((k : ℝ) + 1)) (le_abs.2 (Or.inl (by linarith)))
  calc |iteratedDeriv m (signPow s) (x - ((k : ℝ) + 1)) +
        iteratedDeriv m (signPow s) (x + ((k : ℝ) + 1))|
      ≤ |iteratedDeriv m (signPow s) (x - ((k : ℝ) + 1))| +
        |iteratedDeriv m (signPow s) (x + ((k : ℝ) + 1))| := abs_add_le _ _
    _ ≤ derivCoeff s m * ((k : ℝ) + 1 / 4) ^ (s - 1 - (m : ℝ)) +
        derivCoeff s m * ((k : ℝ) + 1 / 4) ^ (s - 1 - (m : ℝ)) := add_le_add hA hB
    _ = 2 * derivCoeff s m * ((k : ℝ) + 1 / 4) ^ (s - 1 - (m : ℝ)) := by ring

/-- The shifted-term smoothness on the window. -/
lemma contDiffOn_pairTerm (s : ℝ) (k : ℕ) :
    ContDiffOn ℝ ∞ (fun z => pairTerm s z k) (Ioo (-(3 / 4 : ℝ)) (3 / 4)) := by
  intro x hx
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have h1 : x - ((k : ℝ) + 1) ≠ 0 := fun h => by linarith [hx.2]
  have h2 : x + ((k : ℝ) + 1) ≠ 0 := fun h => by linarith [hx.1]
  exact ((contDiffAt_signPow_sub (s := s) (n := ∞) h1).add
    (contDiffAt_signPow_add (s := s) (n := ∞) h2)).contDiffWithinAt

/-- The uniform summable bounds on all the derivatives of the paired terms on the window. -/
lemma pairTerm_hbd {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    ∀ m : ℕ, ∃ V : ℕ → ℝ, Summable V ∧ ∀ k : ℕ, ∀ y ∈ Ioo (-(3 / 4 : ℝ)) (3 / 4),
      ‖iteratedDeriv m (fun z => pairTerm s z k) y‖ ≤ V k := by
  intro m
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · refine ⟨fun k => 2 * ((k : ℝ) + 1 / 4) ^ (s - 2),
      (summable_shift_rpow (a := s - 2) (by linarith)).mul_left 2, fun k y hy => ?_⟩
    rw [iteratedDeriv_zero, Real.norm_eq_abs]
    exact abs_pairTerm_le hs0 hs1 (abs_lt.2 ⟨hy.1, hy.2⟩) k
  · have hm' : 1 ≤ m := by omega
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm'
    refine ⟨fun k => 2 * derivCoeff s m * ((k : ℝ) + 1 / 4) ^ (s - 1 - (m : ℝ)),
      (summable_shift_rpow (a := s - 1 - (m : ℝ)) (by linarith)).mul_left _,
      fun k y hy => norm_iteratedDeriv_pairTerm_le hs0 hs1 hm' (abs_lt.2 ⟨hy.1, hy.2⟩) k⟩

/-- Iterated derivatives of a `C^∞` function on an open set are `C^∞` there. -/
lemma contDiffOn_iteratedDeriv_of_isOpen {I : Set ℝ} (hI : IsOpen I) (m : ℕ) :
    ∀ f : ℝ → ℝ, ContDiffOn ℝ ∞ f I → ContDiffOn ℝ ∞ (iteratedDeriv m f) I := by
  induction m with
  | zero => intro f hf; simpa only [iteratedDeriv_zero] using hf
  | succ m ih =>
    intro f hf
    rw [iteratedDeriv_succ']
    exact ih (deriv f) ((contDiffOn_infty_iff_deriv_of_isOpen hI).1 hf).2

/-- Termwise differentiation on an open preconnected set: the derivative of the `m`-th derivative
of a series is the series of the `(m+1)`-st derivatives. -/
lemma hasDerivAt_tsum_iteratedDeriv_window {I : Set ℝ} (hI : IsOpen I) (hconn : IsPreconnected I)
    {g : ℕ → ℝ → ℝ} (hsm : ∀ k, ContDiffOn ℝ ∞ (g k) I)
    (hbd : ∀ m : ℕ, ∃ V : ℕ → ℝ, Summable V ∧ ∀ k, ∀ y ∈ I, ‖iteratedDeriv m (g k) y‖ ≤ V k)
    (m : ℕ) {y : ℝ} (hy : y ∈ I) :
    HasDerivAt (fun z => ∑' k, iteratedDeriv m (g k) z)
      (∑' k, iteratedDeriv (m + 1) (g k) y) y := by
  obtain ⟨V, hV, hVb⟩ := hbd (m + 1)
  obtain ⟨W, hW, hWb⟩ := hbd m
  have hg : ∀ k, ∀ z ∈ I, HasDerivAt (iteratedDeriv m (g k))
      (iteratedDeriv (m + 1) (g k) z) z := by
    intro k z hz
    have hdiff := (contDiffOn_iteratedDeriv_of_isOpen hI m (g k) (hsm k)).differentiableOn
      (by simp)
    rw [iteratedDeriv_succ]
    exact (hdiff.differentiableAt (hI.mem_nhds hz)).hasDerivAt
  exact hasDerivAt_tsum_of_isPreconnected (g := fun k z => iteratedDeriv m (g k) z)
    (g' := fun k z => iteratedDeriv (m + 1) (g k) z) (u := V) (t := I) (y₀ := y) (y := y)
    hV hI hconn (fun k z hz => hg k z hz) (fun k z hz => hVb k z hz) hy
    (Summable.of_norm_bounded hW (fun k => hWb k y hy)) hy

/-- The `m`-th iterated derivative of a series on an open preconnected set is the series of the
`m`-th iterated derivatives. -/
lemma iteratedDeriv_tsum_window {I : Set ℝ} (hI : IsOpen I) (hconn : IsPreconnected I)
    {g : ℕ → ℝ → ℝ} (hsm : ∀ k, ContDiffOn ℝ ∞ (g k) I)
    (hbd : ∀ m : ℕ, ∃ V : ℕ → ℝ, Summable V ∧ ∀ k, ∀ y ∈ I, ‖iteratedDeriv m (g k) y‖ ≤ V k)
    (m : ℕ) : ∀ y ∈ I,
      iteratedDeriv m (fun z => ∑' k, g k z) y = ∑' k, iteratedDeriv m (g k) y := by
  induction m with
  | zero => intro y _; simp only [iteratedDeriv_zero]
  | succ m ih =>
    intro y hy
    have heq : iteratedDeriv m (fun z => ∑' k, g k z) =ᶠ[𝓝 y]
        fun z => ∑' k, iteratedDeriv m (g k) z :=
      Filter.eventually_of_mem (hI.mem_nhds hy) fun z hz => ih z hz
    rw [iteratedDeriv_succ, heq.deriv_eq,
      (hasDerivAt_tsum_iteratedDeriv_window hI hconn hsm hbd m hy).deriv]

/-- A series of `C^∞` functions on an open preconnected set, with summable bounds on all the
derivatives, is `C^∞` on that set. -/
lemma contDiffOn_tsum_window {I : Set ℝ} (hI : IsOpen I) (hconn : IsPreconnected I)
    {g : ℕ → ℝ → ℝ} (hsm : ∀ k, ContDiffOn ℝ ∞ (g k) I)
    (hbd : ∀ m : ℕ, ∃ V : ℕ → ℝ, Summable V ∧ ∀ k, ∀ y ∈ I, ‖iteratedDeriv m (g k) y‖ ≤ V k) :
    ContDiffOn ℝ ∞ (fun z => ∑' k, g k z) I := by
  have hdiff : ∀ m : ℕ, DifferentiableOn ℝ (iteratedDeriv m (fun z => ∑' k, g k z)) I := by
    intro m y hy
    have heq : iteratedDeriv m (fun z => ∑' k, g k z) =ᶠ[𝓝 y]
        fun z => ∑' k, iteratedDeriv m (g k) z :=
      Filter.eventually_of_mem (hI.mem_nhds hy) fun z hz =>
        iteratedDeriv_tsum_window hI hconn hsm hbd m z hz
    exact (((hasDerivAt_tsum_iteratedDeriv_window hI hconn hsm hbd m hy).congr_of_eventuallyEq
      heq).differentiableAt).differentiableWithinAt
  refine (contDiffOn_iff_continuousOn_differentiableOn_deriv hI.uniqueDiffOn).2
    ⟨fun m _ => ?_, fun m _ => ?_⟩
  · exact ((hdiff m).continuousOn).congr (iteratedDerivWithin_of_isOpen hI)
  · exact (hdiff m).congr (iteratedDerivWithin_of_isOpen hI)

/-- The paired series is `C^∞` on the window `(-3/4, 3/4)`. -/
lemma contDiffOn_pairSum {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    ContDiffOn ℝ ∞ (fun z => ∑' k : ℕ, pairTerm s z k) (Ioo (-(3 / 4 : ℝ)) (3 / 4)) :=
  contDiffOn_tsum_window isOpen_Ioo (convex_Ioo _ _).isPreconnected
    (g := fun k z => pairTerm s z k) (fun k => contDiffOn_pairTerm s k) (pairTerm_hbd hs0 hs1)

/-- The decomposition of the symmetric partial sums into the central term and the pairs. -/
lemma symmetric_eq_add_pairs (s x : ℝ) (M : ℕ) :
    ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), signPow s (x - k) =
      signPow s x + ∑ k ∈ Finset.range M, pairTerm s x k := by
  rw [sum_Icc_symm_eq (signPow s) x M]
  congr 1
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp only [pairTerm, Int.cast_add, Int.cast_natCast, Int.cast_one]

/-- Off the integers in the window, the kernel is the signed power plus the paired series. -/
lemma periodicKernel_eq_add_pairs {s x : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hx : |x| < 3 / 4)
    (hint : ∀ k : ℤ, x ≠ k) :
    periodicKernel s x = signPow s x + ∑' k : ℕ, pairTerm s x k := by
  have hlim := tendsto_symmetric_signPow hs0 hs1 hint
  have hfun : (fun M : ℕ => ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), signPow s (x - k)) =
      fun M : ℕ => signPow s x + ∑ k ∈ Finset.range M, pairTerm s x k :=
    funext fun M => symmetric_eq_add_pairs s x M
  rw [hfun] at hlim
  have hlim2 : Tendsto (fun M : ℕ => signPow s x + ∑ k ∈ Finset.range M, pairTerm s x k) atTop
      (𝓝 (signPow s x + ∑' k : ℕ, pairTerm s x k)) :=
    tendsto_const_nhds.add (summable_pairTerm hs0 hs1 hx).hasSum.tendsto_sum_nat
  exact tendsto_nhds_unique hlim hlim2

/-- On the punctured window `(-3/4, 3/4) ∖ {0}`, the kernel is the signed power plus the paired
series. -/
lemma periodicKernel_eqOn {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    EqOn (periodicKernel s) (fun z => signPow s z + ∑' k : ℕ, pairTerm s z k)
      (Ioo (-(3 / 4 : ℝ)) (3 / 4) \ {0}) := by
  intro x hx
  have hx' : |x| < 3 / 4 := abs_lt.2 ⟨hx.1.1, hx.1.2⟩
  have hne : x ≠ 0 := hx.2
  have hint : ∀ k : ℤ, x ≠ k := by
    intro k hk
    have h1 : (k : ℝ) < 1 := by linarith [hx.1.2]
    have h2 : (-1 : ℝ) < k := by linarith [hx.1.1]
    have h1' : k < 1 := by exact_mod_cast h1
    have h2' : -1 < k := by exact_mod_cast h2
    have hk0 : k = 0 := by omega
    exact hne (by simp [hk, hk0])
  exact periodicKernel_eq_add_pairs hs0 hs1 hx' hint

/-- The kernel is `C^∞` on the punctured window. -/
lemma contDiffOn_periodicKernel_punct {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    ContDiffOn ℝ ∞ (periodicKernel s) (Ioo (-(3 / 4 : ℝ)) (3 / 4) \ {0}) := by
  have hφ : ContDiffOn ℝ ∞ (signPow s) (Ioo (-(3 / 4 : ℝ)) (3 / 4) \ {0}) := by
    intro x hx
    have hne : x ≠ 0 := hx.2
    exact (contDiffAt_signPow (s := s) (n := ∞) hne).contDiffWithinAt
  have hR : ContDiffOn ℝ ∞ (fun z => ∑' k : ℕ, pairTerm s z k)
      (Ioo (-(3 / 4 : ℝ)) (3 / 4) \ {0}) :=
    (contDiffOn_pairSum hs0 hs1).mono sdiff_subset
  exact (hφ.add hR).congr (periodicKernel_eqOn hs0 hs1)

/-- The `m`-th derivative of the kernel on the punctured window splits into the derivative of the
signed power and the series of the derivatives of the paired terms. -/
lemma iteratedDeriv_periodicKernel_punct {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (m : ℕ) {x : ℝ}
    (hx : x ∈ Ioo (-(3 / 4 : ℝ)) (3 / 4) \ {0}) :
    iteratedDeriv m (periodicKernel s) x = iteratedDeriv m (signPow s) x +
      ∑' k : ℕ, iteratedDeriv m (fun z => pairTerm s z k) x := by
  have hxI : x ∈ Ioo (-(3 / 4 : ℝ)) (3 / 4) := hx.1
  have hne : x ≠ 0 := hx.2
  have hJ : IsOpen (Ioo (-(3 / 4 : ℝ)) (3 / 4) \ {0}) := isOpen_Ioo.sdiff isClosed_singleton
  have h1 := (periodicKernel_eqOn hs0 hs1).iteratedDeriv_of_isOpen hJ m
  have hA : ContDiffAt ℝ (m : WithTop ℕ∞) (signPow s) x :=
    contDiffAt_signPow (s := s) (n := (m : WithTop ℕ∞)) hne
  have hR : ContDiffAt ℝ (m : WithTop ℕ∞) (fun z => ∑' k : ℕ, pairTerm s z k) x :=
    ((contDiffOn_pairSum hs0 hs1).contDiffAt (isOpen_Ioo.mem_nhds hxI)).of_le
      (WithTop.coe_le_coe.2 le_top)
  rw [h1 hx, iteratedDeriv_fun_add hA hR,
    iteratedDeriv_tsum_window isOpen_Ioo (convex_Ioo _ _).isPreconnected
      (g := fun k z => pairTerm s z k) (fun k => contDiffOn_pairTerm s k)
      (pairTerm_hbd hs0 hs1) m x hxI]

/-- The series of the `m`-th derivatives of the paired terms is bounded by `pairBound s m`, for
`m ≥ 1`, on the window. -/
lemma norm_iteratedDeriv_pairSum_le {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {m : ℕ} (hm : 1 ≤ m)
    {x : ℝ} (hx : |x| < 3 / 4) :
    ‖∑' k : ℕ, iteratedDeriv m (fun z => pairTerm s z k) x‖ ≤ pairBound s m := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hsum : Summable fun k : ℕ => 2 * derivCoeff s m * ((k : ℝ) + 1 / 4) ^ (s - 1 - (m : ℝ)) :=
    (summable_shift_rpow (a := s - 1 - (m : ℝ)) (by linarith)).mul_left _
  exact tsum_of_norm_bounded hsum.hasSum
    (fun k => norm_iteratedDeriv_pairTerm_le hs0 hs1 hm hx k)

/-- The derivative bound on the punctured window, with the factor `derivCoeff s m + pairBound s m
+ 1`, which depends only on `s` and `m`. -/
lemma norm_iteratedDeriv_periodicKernel_punct_le {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {m : ℕ}
    (hm : 1 ≤ m) {x : ℝ} (hx : x ∈ Ioo (-(3 / 4 : ℝ)) (3 / 4) \ {0}) :
    ‖iteratedDeriv m (periodicKernel s) x‖ ≤
      (derivCoeff s m + pairBound s m + 1) * |x| ^ (s - 1 - (m : ℝ)) := by
  have hx' : |x| < 3 / 4 := abs_lt.2 ⟨hx.1.1, hx.1.2⟩
  have hx0 : 0 < |x| := abs_pos.2 hx.2
  have hx1 : |x| ≤ 1 := by linarith
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hP : 1 ≤ |x| ^ (s - 1 - (m : ℝ)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hx0 hx1 (by linarith)
  have hP0 : 0 ≤ |x| ^ (s - 1 - (m : ℝ)) := Real.rpow_nonneg hx0.le _
  have hD0 := pairBound_nonneg s m
  have hA : ‖iteratedDeriv m (signPow s) x‖ = derivCoeff s m * |x| ^ (s - 1 - (m : ℝ)) := by
    rw [Real.norm_eq_abs, abs_iteratedDeriv_signPow s m hx.2]
  have hB := norm_iteratedDeriv_pairSum_le hs0 hs1 hm hx'
  rw [iteratedDeriv_periodicKernel_punct hs0 hs1 m hx]
  have hsum := norm_add_le (iteratedDeriv m (signPow s) x)
    (∑' k : ℕ, iteratedDeriv m (fun z => pairTerm s z k) x)
  have hD1 : pairBound s m ≤ pairBound s m * |x| ^ (s - 1 - (m : ℝ)) :=
    le_mul_of_one_le_right hD0 hP
  have hexp : (derivCoeff s m + pairBound s m + 1) * |x| ^ (s - 1 - (m : ℝ)) =
      derivCoeff s m * |x| ^ (s - 1 - (m : ℝ)) + pairBound s m * |x| ^ (s - 1 - (m : ℝ)) +
        |x| ^ (s - 1 - (m : ℝ)) := by ring
  rw [hexp]
  linarith

/-- Every non-integer `t` differs from an integer `n` by a point of the punctured window, and the
distance `min (fract t) (1 - fract t)` equals `|t - n|`. -/
lemma exists_nearest_int {t : ℝ} (ht : ∀ k : ℤ, t ≠ k) :
    ∃ n : ℤ, t - n ∈ Ioo (-(3 / 4 : ℝ)) (3 / 4) \ {0} ∧
      min (Int.fract t) (1 - Int.fract t) = |t - n| := by
  have hdef : Int.fract t = t - ⌊t⌋ := rfl
  have hf0 : 0 ≤ Int.fract t := Int.fract_nonneg t
  have hf1 : Int.fract t < 1 := Int.fract_lt_one t
  have hne : Int.fract t ≠ 0 := by
    intro h
    exact ht ⌊t⌋ (by linarith)
  have hpos : 0 < Int.fract t := lt_of_le_of_ne hf0 (Ne.symm hne)
  rcases le_total (Int.fract t) (1 / 2) with hhalf | hhalf
  · have e1 : t - (⌊t⌋ : ℝ) = Int.fract t := hdef.symm
    refine ⟨⌊t⌋, ?_, ?_⟩
    · rw [e1]
      exact ⟨⟨by linarith, by linarith⟩, hne⟩
    · rw [e1, abs_of_pos hpos, min_eq_left (by linarith)]
  · have e2 : t - ((⌊t⌋ + 1 : ℤ) : ℝ) = Int.fract t - 1 := by
      rw [hdef]
      push_cast
      ring
    refine ⟨⌊t⌋ + 1, ?_, ?_⟩
    · rw [e2]
      exact ⟨⟨by linarith, by linarith⟩, sub_ne_zero.2 hf1.ne⟩
    · rw [e2, min_eq_right (by linarith), abs_of_neg (by linarith)]
      ring

/-- The kernel is `1`-periodic, as a function of the point. -/
lemma periodicKernel_sub_int_fun (s : ℝ) (n : ℤ) :
    (fun z : ℝ => periodicKernel s (z - n)) = periodicKernel s := by
  funext z
  rw [show z - (n : ℝ) = z + ((-n : ℤ) : ℝ) by push_cast; ring]
  exact periodicKernel_add_int s z (-n)

/-- **Smoothness off the integers.** The kernel `K_s` is `C^∞` at every point off the integers. -/
theorem contDiffAt_periodicKernel_of_not_int {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {t : ℝ}
    (ht : ∀ k : ℤ, t ≠ k) : ContDiffAt ℝ ∞ (periodicKernel s) t := by
  obtain ⟨n, hn, -⟩ := exists_nearest_int ht
  have hK : ContDiffAt ℝ ∞ (periodicKernel s) (t - n) :=
    (contDiffOn_periodicKernel_punct hs0 hs1).contDiffAt
      ((isOpen_Ioo.sdiff isClosed_singleton).mem_nhds hn)
  have h2 : ContDiffAt ℝ ∞ (fun z : ℝ => periodicKernel s (z - n)) t :=
    ContDiffAt.comp (f := fun z : ℝ => z - (n : ℝ)) t hK (contDiffAt_id.sub contDiffAt_const)
  rwa [periodicKernel_sub_int_fun s n] at h2

/-- **Derivative bounds off the integers.** For `m ≥ 1` there is a number `C > 0`, depending only
on `s` and `m`, with `|K_s^{(m)}(t)| ≤ C · dist(t, ℤ)^(s - 1 - m)` at every non-integer `t`, where
`dist(t, ℤ) = min (fract t) (1 - fract t)`. -/
theorem norm_iteratedDeriv_periodicKernel_le {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {m : ℕ}
    (hm : 1 ≤ m) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, (∀ k : ℤ, t ≠ k) →
      ‖iteratedDeriv m (periodicKernel s) t‖ ≤
        C * (min (Int.fract t) (1 - Int.fract t)) ^ (s - 1 - (m : ℝ)) := by
  refine ⟨derivCoeff s m + pairBound s m + 1, ?_, fun t ht => ?_⟩
  · have h1 := derivCoeff_nonneg s m
    have h2 := pairBound_nonneg s m
    linarith
  obtain ⟨n, hn, hmin⟩ := exists_nearest_int ht
  have hper := periodicKernel_sub_int_fun s n
  have htr : iteratedDeriv m (periodicKernel s) t =
      iteratedDeriv m (periodicKernel s) (t - n) := by
    have h := congrFun (iteratedDeriv_comp_sub_const m (periodicKernel s) (n : ℝ)) t
    rw [hper] at h
    exact h
  rw [hmin, htr]
  exact norm_iteratedDeriv_periodicKernel_punct_le hs0 hs1 hm hn

end Riesz1
