/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Tactic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 1997, Problem 1

In the plane the points with integer coordinates are the vertices of unit squares.
The squares are colored alternately black and white as on a chessboard.
For any pair of positive integers m and n, consider a right-angled triangle whose
vertices have integer coordinates and whose legs, of lengths m and n, lie along the
edges of the squares. Let S₁ be the total area of the black part of the triangle,
and S₂ be the total area of the white part. Let f(m, n) = |S₁ − S₂|.

(a) Calculate f(m, n) for all positive integers m and n which are either both even
    or both odd.
(b) Prove that f(m, n) ≤ max(m, n)/2 for all m, n.
(c) Show that there is no constant C such that f(m, n) < C for all m, n.
-/

namespace Imo1997P1

open MeasureTheory intervalIntegral

open scoped BigOperators

/- ### Formalization setup

We fix the triangle `T(m,n)` with vertices `(0,0)`, `(m,0)`, `(0,n)`. This is without
loss of generality: any triangle allowed by the problem is obtained from `T(m,n)` by a
translation with integer coordinates, a reflection across a coordinate axis, or a swap
of the two axes. Translations by an integer vector and reflections only change the sign
of `S₁ − S₂` (the chessboard coloring itself is preserved or globally swapped), and
swapping the axes swaps `m` and `n`; hence `|S₁ − S₂|` is the same for every choice of
triangle, so the function `f` of the problem is well defined.

The chessboard coloring is encoded by the sign function `col x * col y` where
`col x = (-1)^⌊x⌋`: the unit square `[i, i+1) × [j, j+1)` carries the sign
`(-1)^(i+j)`. With `S₁` the total black area and `S₂` the total white area we have
`S₁ − S₂ = ∫∫_T col x * col y`, since the two color classes partition the triangle up
to the grid lines, which have area zero. Writing `A t = ∫ x in 0..t, col x` for the
one-dimensional integral of the sign function, the integral over the triangle
`{0 ≤ x, 0 ≤ y, x/m + y/n ≤ 1}` evaluates the inner integral and gives
`S₁ − S₂ = ∫ x in 0..m, col x * A (n * (1 - x/m))`. -/

/-- The sign of the chessboard column containing `x`: `+1` on the unit intervals
`[i, i+1)` with `i` even ("black") and `-1` for `i` odd ("white"). -/
noncomputable def col (x : ℝ) : ℝ := (-1) ^ ⌊x⌋

/-- The integral of `col` from `0` to `t`; a continuous triangular wave. -/
noncomputable def A (t : ℝ) : ℝ := ∫ x in 0..t, col x

/-- `colorSum m n` is `S₁ − S₂` for the right triangle with vertices
`(0,0)`, `(m,0)`, `(0,n)`. -/
noncomputable def colorSum (m n : ℕ) : ℝ := ∫ x in 0..m, col x * A (n * (1 - x / m))

/-- `f m n = |S₁ − S₂|` as in the problem statement. -/
noncomputable def f (m n : ℕ) : ℝ := |colorSum m n|

snip begin

/-! ### A.e. congruence and integrability infrastructure -/

/-- Functions that agree off a countable set have equal interval integrals. -/
lemma integral_congr_ae_of_countable {f g : ℝ → ℝ} {a b : ℝ} {s : Set ℝ}
    (hs : s.Countable) (h : ∀ x ∈ Set.Ioo (min a b) (max a b), x ∉ s → f x = g x) :
    ∫ x in a..b, f x = ∫ x in a..b, g x := by
  apply intervalIntegral.integral_congr_ae
  rw [MeasureTheory.ae_iff]
  have hsub : {x | ¬(x ∈ Set.uIoc a b → f x = g x)} ⊆ s ∪ {min a b, max a b} := by
    intro x hx
    simp only [Set.mem_setOf_eq, Classical.not_imp] at hx
    obtain ⟨hxI, hne⟩ := hx
    by_cases hxs : x ∈ s
    · exact Set.mem_union_left _ hxs
    · apply Set.mem_union_right
      by_contra hmem
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hmem
      obtain ⟨hxmin, hxmax⟩ := hmem
      have hIoo : x ∈ Set.Ioo (min a b) (max a b) := by
        rw [Set.mem_uIoc] at hxI
        rcases hxI with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · have hle : a ≤ b := le_of_lt (lt_of_lt_of_le h1 h2)
          rw [min_eq_left hle, max_eq_right hle]
          exact ⟨h1, lt_of_le_of_ne h2 (fun hxb => hxmax (hxb.trans (max_eq_right hle).symm))⟩
        · have hle : b ≤ a := le_of_lt (lt_of_lt_of_le h1 h2)
          rw [min_eq_right hle, max_eq_left hle]
          exact ⟨h1, lt_of_le_of_ne h2 (fun hxa => hxmax (hxa.trans (max_eq_left hle).symm))⟩
      exact hne (h x hIoo hxs)
  exact measure_mono_null hsub
    ((hs.union ((Set.countable_singleton _).insert _)).measure_zero _)

/-- Bounded measurable functions are interval integrable for the Lebesgue measure. -/
lemma intervalIntegrable_of_measurable_bounded {f : ℝ → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ x, ‖f x‖ ≤ C) (a b : ℝ) : IntervalIntegrable f volume a b := by
  constructor <;>
    · exact IntegrableOn.of_bound measure_Ioc_lt_top hf.aestronglyMeasurable.restrict C
        (Filter.Eventually.of_forall hC)

/-! ### Basic properties of `col` -/

lemma measurable_col : Measurable col :=
  (measurable_of_countable _).comp Int.measurable_floor

lemma norm_col (x : ℝ) : ‖col x‖ = 1 := by
  simp [col]

lemma abs_col (x : ℝ) : |col x| = 1 := by
  simp [col]

lemma col_int (a b : ℝ) : IntervalIntegrable col volume a b :=
  intervalIntegrable_of_measurable_bounded measurable_col (fun x => (norm_col x).le) a b

/-- On the open unit interval `(k, k+1)` the sign `col` is constantly `(-1)^k`. -/
lemma col_eq_on_Ioo {k : ℕ} {x : ℝ} (hx : x ∈ Set.Ioo (k : ℝ) (k + 1)) :
    col x = (-1) ^ (k : ℤ) := by
  rw [col, Int.floor_eq_on_Ico (k : ℤ) x ⟨hx.1.le, hx.2⟩]

/-- Reflecting in an integer point flips the sign by `(-1)^(m+1)` off the integers. -/
lemma col_int_sub (m : ℕ) {x : ℝ} (hx : x ∉ Set.range Int.cast) :
    col ((m : ℝ) - x) = (-1) ^ ((m : ℤ) + 1) * col x := by
  have hfloor : ⌊(m : ℝ) - x⌋ = (m : ℤ) - ⌊x⌋ - 1 := by
    have h1 : (m : ℝ) - x = -(x - ((m : ℤ) : ℝ)) := by push_cast; ring
    rw [h1, Int.floor_neg, Int.ceil_sub_intCast,
      (Int.ceil_eq_floor_add_one_iff_notMem _).mpr hx]
    ring
  rw [col, col, hfloor]
  have h2 : (-1 : ℝ) ^ (2 * (-⌊x⌋ - 1)) = 1 :=
    Even.neg_one_zpow ⟨-⌊x⌋ - 1, by ring⟩
  calc (-1 : ℝ) ^ ((m : ℤ) - ⌊x⌋ - 1)
      = (-1) ^ (((m : ℤ) + 1 + ⌊x⌋) + 2 * (-⌊x⌋ - 1)) := by congr 1; ring
    _ = (-1) ^ ((m : ℤ) + 1 + ⌊x⌋) * (-1) ^ (2 * (-⌊x⌋ - 1)) := by
        rw [zpow_add₀ (show (-1 : ℝ) ≠ 0 by norm_num)]
    _ = (-1) ^ ((m : ℤ) + 1 + ⌊x⌋) := by rw [h2, mul_one]
    _ = (-1) ^ ((m : ℤ) + 1) * (-1) ^ ⌊x⌋ := by
        rw [zpow_add₀ (show (-1 : ℝ) ≠ 0 by norm_num)]

/-! ### Basic properties of `A` -/

lemma A_cont : Continuous A := intervalIntegral.continuous_primitive col_int 0

lemma A_zero : A 0 = 0 := by simp [A]

lemma A_sub (s t : ℝ) : A t - A s = ∫ x in s..t, col x := by
  have h := integral_add_adjacent_intervals (col_int 0 s) (col_int s t)
  unfold A
  linarith

lemma norm_A_sub_le {l u : ℝ} (h : l ≤ u) : ‖A u - A l‖ ≤ u - l := by
  rw [A_sub]
  calc ‖∫ x in l..u, col x‖ ≤ ∫ x in l..u, ‖col x‖ := norm_integral_le_integral_norm h
    _ = ∫ x in l..u, (1 : ℝ) := intervalIntegral.integral_congr (fun x _ => norm_col x)
    _ = u - l := by rw [intervalIntegral.integral_const]; simp

/-- Product of `col` with `A` composed with a continuous function is integrable. -/
lemma colA_int {u : ℝ → ℝ} (hu : Continuous u) (a b : ℝ) :
    IntervalIntegrable (fun x => col x * A (u x)) volume a b :=
  (col_int a b).mul_continuousOn ((A_cont.comp hu).continuousOn)

/-- `col` composed with a measurable function is integrable. -/
lemma colComp_int {u : ℝ → ℝ} (hu : Measurable u) (a b : ℝ) :
    IntervalIntegrable (fun x => col (u x)) volume a b :=
  intervalIntegrable_of_measurable_bounded (measurable_col.comp hu)
    (fun _ => (norm_col _).le) a b

/-- The value of `A` at a natural number: the alternating sum `1 - 1 + 1 - ...`. -/
lemma A_nat (n : ℕ) : A n = if Even n then 0 else 1 := by
  induction n with
  | zero => simp [A_zero]
  | succ k ih =>
    have hstep : A ((k : ℝ) + 1) = A k + (-1 : ℝ) ^ (k : ℤ) := by
      have h := A_sub (k : ℝ) ((k : ℝ) + 1)
      have hint : (∫ x in (k : ℝ)..(k : ℝ) + 1, col x) = (-1 : ℝ) ^ (k : ℤ) := by
        have hcong : (∫ x in (k : ℝ)..(k : ℝ) + 1, col x) =
            ∫ x in (k : ℝ)..(k : ℝ) + 1, ((-1 : ℝ) ^ (k : ℤ)) := by
          apply integral_congr_ae_of_countable Set.countable_empty
          intro x hx _
          have hmn : min (k : ℝ) ((k : ℝ) + 1) = k := min_eq_left (by linarith)
          have hmx : max (k : ℝ) ((k : ℝ) + 1) = (k : ℝ) + 1 := max_eq_right (by linarith)
          rw [hmn, hmx] at hx
          exact col_eq_on_Ioo hx
        rw [hcong, intervalIntegral.integral_const]
        simp
      linarith
    rw [Nat.cast_succ, hstep, ih]
    rcases Nat.even_or_odd k with he | ho
    · rw [if_pos he, if_neg (Nat.not_even_iff_odd.mpr he.add_one),
        Even.neg_one_zpow ((Int.even_coe_nat _).mpr he)]
      simp
    · rw [if_neg (Nat.not_even_iff_odd.mpr ho), if_pos ho.add_one,
        Odd.neg_one_zpow ((Int.odd_coe_nat _).mpr ho)]
      simp

/-- Closed form of `A` on the unit interval `[k, k+1)`: a triangular wave. -/
lemma A_apply_of_mem_Ico {k : ℕ} {t : ℝ} (hk : t ∈ Set.Ico (k : ℝ) (k + 1)) :
    A t = if Even k then t - k else 1 - (t - k) := by
  induction k with
  | zero =>
    simp only [Nat.cast_zero, zero_add] at hk
    obtain ⟨h0, h1⟩ := hk
    have hAt : A t = ∫ x in (0 : ℝ)..t, (1 : ℝ) := by
      apply integral_congr_ae_of_countable Set.countable_empty
      intro x hx _
      rw [min_eq_left h0, max_eq_right h0] at hx
      have hxI : x ∈ Set.Ioo ((0 : ℕ) : ℝ) ((0 : ℕ) + 1) := by
        simp only [Nat.cast_zero, zero_add]
        exact ⟨hx.1, hx.2.trans_le h1.le⟩
      rw [col_eq_on_Ioo hxI]
      simp
    rw [hAt, intervalIntegral.integral_const]
    simp
  | succ k ih =>
    rw [Nat.cast_succ] at hk
    obtain ⟨h0, h1⟩ := hk
    have hsplit : A t = A ((k : ℝ) + 1) + ∫ x in (k : ℝ) + 1..t, col x := by
      have h := A_sub ((k : ℝ) + 1) t
      linarith
    have hstep : (∫ x in (k : ℝ) + 1..t, col x) = (-1 : ℝ) ^ ((k : ℤ) + 1) * (t - (k + 1)) := by
      have hcong : (∫ x in (k : ℝ) + 1..t, col x) =
          ∫ x in (k : ℝ) + 1..t, ((-1 : ℝ) ^ ((k : ℤ) + 1)) := by
        apply integral_congr_ae_of_countable Set.countable_empty
        intro x hx _
        rw [min_eq_left h0, max_eq_right h0] at hx
        have hxI : x ∈ Set.Ioo ((k + 1 : ℕ) : ℝ) ((k + 1 : ℕ) + 1) := by
          simp only [Nat.cast_succ]
          exact ⟨hx.1, hx.2.trans_le h1.le⟩
        exact col_eq_on_Ioo hxI
      rw [hcong, intervalIntegral.integral_const, smul_eq_mul, mul_comm]
    have hbase : A ((k : ℝ) + 1) = if Even (k + 1) then 0 else 1 := by
      have h := A_nat (k + 1)
      rw [Nat.cast_succ] at h
      exact h
    rw [hsplit, hbase, hstep]
    rcases Nat.even_or_odd (k + 1) with he | ho
    · rw [if_pos he, if_pos he]
      have hE : Even ((k : ℤ) + 1) := by
        have hE' := (Int.even_coe_nat _).mpr he
        rwa [Nat.cast_add, Nat.cast_one] at hE'
      rw [Even.neg_one_zpow hE]
      push_cast
      ring
    · rw [if_neg (Nat.not_even_iff_odd.mpr ho), if_neg (Nat.not_even_iff_odd.mpr ho)]
      have hO : Odd ((k : ℤ) + 1) := by
        have hO' := (Int.odd_coe_nat _).mpr ho
        rwa [Nat.cast_add, Nat.cast_one] at hO'
      rw [Odd.neg_one_zpow hO]
      push_cast
      ring

/-- `A` composed with `x ↦ n - x` is a reflected copy of `A` up to sign and shift. -/
lemma A_int_sub (n : ℕ) (t : ℝ) :
    A ((n : ℝ) - t) = (-1) ^ ((n : ℤ) + 1) * (A n - A t) := by
  have h1 : (∫ y in t..(n : ℝ), col ((n : ℝ) - y)) = A ((n : ℝ) - t) := by
    rw [integral_comp_sub_left]
    simp [A]
  rw [← h1, integral_congr_ae_of_countable (Set.countable_range Int.cast)
    (fun y _ hyI => col_int_sub n hyI), intervalIntegral.integral_const_mul, ← A_sub]

/-! ### The reflection equations for `colorSum` -/

/-- First reflection identity: substituting `x ↦ m - x` in the integral. -/
lemma colorSum_reflection {m n : ℕ} (hm : 0 < m) :
    colorSum m n = (-1) ^ ((m : ℤ) + 1) * ∫ x in (0 : ℝ)..(m : ℝ), col x * A (n * x / m) := by
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hA : ∀ x : ℝ, (n : ℝ) * (1 - ((m : ℝ) - x) / m) = n * x / m := by
    intro x
    field_simp
    ring
  have h1 : (∫ x in (0 : ℝ)..(m : ℝ), col ((m : ℝ) - x) * A (n * (1 - (m - x) / m))) =
      colorSum m n := by
    rw [integral_comp_sub_left (f := fun x => col x * A (n * (1 - x / m))) (d := (m : ℝ))]
    simp [colorSum]
  have hcong : (∫ x in (0 : ℝ)..(m : ℝ), col ((m : ℝ) - x) * A (n * (1 - (m - x) / m))) =
      ∫ x in (0 : ℝ)..(m : ℝ), (-1) ^ ((m : ℤ) + 1) * (col x * A (n * x / m)) := by
    apply integral_congr_ae_of_countable (Set.countable_range Int.cast)
    intro x _ hxI
    rw [col_int_sub m hxI, hA x]
    ring
  rw [← h1, hcong, intervalIntegral.integral_const_mul]

/-- Second reflection identity: using the reflection formula for `A`. -/
lemma colorSum_reflection' {m n : ℕ} (hm : 0 < m) :
    colorSum m n = (-1) ^ ((n : ℤ) + 1) *
      (A n * A m - ∫ x in (0 : ℝ)..(m : ℝ), col x * A (n * x / m)) := by
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hA : ∀ x : ℝ, (n : ℝ) * (1 - x / m) = n - n * x / m := by
    intro x
    field_simp
  have hcong : colorSum m n = ∫ x in (0 : ℝ)..(m : ℝ), col x * A (n - n * x / m) := by
    unfold colorSum
    apply integral_congr_ae_of_countable Set.countable_empty
    intro x _ _
    rw [hA x]
  have hcong2 : (∫ x in (0 : ℝ)..(m : ℝ), col x * A (n - n * x / m)) =
      ∫ x in (0 : ℝ)..(m : ℝ), (-1) ^ ((n : ℤ) + 1) * (col x * A n - col x * A (n * x / m)) := by
    apply integral_congr_ae_of_countable Set.countable_empty
    intro x _ _
    rw [A_int_sub n (n * x / m)]
    ring
  rw [hcong, hcong2, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub (colA_int (by continuity) _ _) (colA_int (by continuity) _ _)]
  have h3 : (∫ x in (0 : ℝ)..(m : ℝ), col x * A (n : ℝ)) = A (n : ℝ) * A (m : ℝ) := by
    have h4 : (∫ x in (0 : ℝ)..(m : ℝ), col x * A (n : ℝ)) =
        ∫ x in (0 : ℝ)..(m : ℝ), A (n : ℝ) * col x := by
      apply integral_congr_ae_of_countable Set.countable_empty
      intro x _ _
      ring
    rw [h4, intervalIntegral.integral_const_mul]
    rfl
  rw [h3]

/-- For `m + n` even, the color sum is explicitly `(-1)^(n+1) * A n * A m / 2`. -/
lemma colorSum_same_parity {m n : ℕ} (hm : 0 < m) (h : Even (m + n)) :
    colorSum m n = (-1) ^ ((n : ℤ) + 1) * A n * A m / 2 := by
  have eq1 := colorSum_reflection (n := n) hm
  have eq2 := colorSum_reflection' (n := n) hm
  have hc : ((-1 : ℝ) ^ ((m : ℤ) + 1)) * ((-1) ^ ((m : ℤ) + 1)) = 1 := by
    rw [← zpow_add₀ (show (-1 : ℝ) ≠ 0 by norm_num)]
    exact Even.neg_one_zpow ⟨(m : ℤ) + 1, by ring⟩
  have hdc : ((-1 : ℝ) ^ ((n : ℤ) + 1)) * ((-1) ^ ((m : ℤ) + 1)) = 1 := by
    have hsum : ((n : ℤ) + 1) + ((m : ℤ) + 1) = ((m + n : ℕ) : ℤ) + 2 := by push_cast; ring
    rw [← zpow_add₀ (show (-1 : ℝ) ≠ 0 by norm_num), hsum]
    exact Even.neg_one_zpow (Even.add ((Int.even_coe_nat _).mpr h) ⟨1, by ring⟩)
  have hJ : ∫ x in (0 : ℝ)..(m : ℝ), col x * A (n * x / m) =
      (-1) ^ ((m : ℤ) + 1) * colorSum m n := by
    have h2 : ((-1 : ℝ) ^ ((m : ℤ) + 1)) * colorSum m n =
        ((-1) ^ ((m : ℤ) + 1)) *
          (((-1) ^ ((m : ℤ) + 1)) * ∫ x in (0 : ℝ)..(m : ℝ), col x * A (n * x / m)) := by
      rw [eq1]
    rw [← mul_assoc, hc, one_mul] at h2
    exact h2.symm
  rw [hJ] at eq2
  have e : (-1 : ℝ) ^ ((n : ℤ) + 1) * (A n * A m - (-1) ^ ((m : ℤ) + 1) * colorSum m n) =
      (-1) ^ ((n : ℤ) + 1) * A n * A m - colorSum m n := by
    rw [mul_sub, ← mul_assoc ((-1 : ℝ) ^ ((n : ℤ) + 1)) ((-1) ^ ((m : ℤ) + 1)) (colorSum m n),
      hdc]
    ring
  rw [e] at eq2
  linarith [eq2]

/-! ### Extension inequalities -/

/-- The interval integral of an affine function. -/
lemma int_affine (c d a b : ℝ) :
    ∫ x in a..b, (c * x + d) = c * (b ^ 2 - a ^ 2) / 2 + d * (b - a) := by
  rw [intervalIntegral.integral_add
      ((by continuity : Continuous fun x : ℝ => c * x).intervalIntegrable a b)
      intervalIntegrable_const,
    intervalIntegral.integral_const_mul, integral_id, intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

/-- Extending the first leg by `1` changes the color sum by at most `n/2`. -/
lemma abs_colorSum_sub_succ_le {m n : ℕ} (hm : 0 < m) :
    |colorSum (m + 1) n - colorSum m n| ≤ n / 2 := by
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hm1n : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  have hm1 : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := Nat.cast_succ m
  have hsplit : (∫ x in (0 : ℝ)..((m : ℝ) + 1), col x * A (n * (1 - x / (m + 1)))) =
      (∫ x in (0 : ℝ)..(m : ℝ), col x * A (n * (1 - x / (m + 1)))) +
        ∫ x in (m : ℝ)..((m : ℝ) + 1), col x * A (n * (1 - x / (m + 1))) :=
    (integral_add_adjacent_intervals
      (colA_int (by continuity) _ _) (colA_int (by continuity) _ _)).symm
  have hD : colorSum (m + 1) n - colorSum m n =
      (∫ x in (0 : ℝ)..(m : ℝ), (col x * A (n * (1 - x / (m + 1))) - col x * A (n * (1 - x / m)))) +
        ∫ x in (m : ℝ)..((m : ℝ) + 1), col x * A (n * (1 - x / (m + 1))) := by
    have hsub : (∫ x in (0 : ℝ)..(m : ℝ),
        (col x * A (n * (1 - x / (m + 1))) - col x * A (n * (1 - x / m)))) =
        (∫ x in (0 : ℝ)..(m : ℝ), col x * A (n * (1 - x / (m + 1)))) -
          ∫ x in (0 : ℝ)..(m : ℝ), col x * A (n * (1 - x / m)) :=
      intervalIntegral.integral_sub
        (colA_int (by continuity) _ _) (colA_int (by continuity) _ _)
    rw [colorSum, colorSum]
    simp only [Nat.cast_succ]
    rw [hsplit, hsub]
    ring
  have hI1 : (∫ x in (0 : ℝ)..(m : ℝ), (n * (x / m - x / (m + 1)))) =
      n * m / (2 * ((m : ℝ) + 1)) := by
    have hcongr : (∫ x in (0 : ℝ)..(m : ℝ), (n * (x / m - x / (m + 1)))) =
        ∫ x in (0 : ℝ)..(m : ℝ), ((n / m - n / (m + 1)) * x + 0) := by
      apply integral_congr_ae_of_countable Set.countable_empty
      intro x _ _
      field_simp
      ring
    rw [hcongr, int_affine]
    field_simp
    ring
  have hI2 : (∫ x in (m : ℝ)..((m : ℝ) + 1), (n * (1 - x / (m + 1)))) =
      n / (2 * ((m : ℝ) + 1)) := by
    have hcongr : (∫ x in (m : ℝ)..((m : ℝ) + 1), (n * (1 - x / (m + 1)))) =
        ∫ x in (m : ℝ)..((m : ℝ) + 1), ((-n / (m + 1)) * x + n) := by
      apply integral_congr_ae_of_countable Set.countable_empty
      intro x _ _
      field_simp
      ring
    rw [hcongr, int_affine]
    field_simp
    ring
  have hb1 : ‖∫ x in (0 : ℝ)..(m : ℝ),
      (col x * A (n * (1 - x / (m + 1))) - col x * A (n * (1 - x / m)))‖ ≤
      ∫ x in (0 : ℝ)..(m : ℝ), (n * (x / m - x / (m + 1))) := by
    refine le_trans (norm_integral_le_integral_norm (Nat.cast_nonneg m)) ?_
    apply intervalIntegral.integral_mono_on (Nat.cast_nonneg m)
      (((colA_int (by continuity) _ _).sub (colA_int (by continuity) _ _)).norm)
      ((by continuity : Continuous fun x : ℝ => (n : ℝ) * (x / m - x / (m + 1))).intervalIntegrable _ _)
    intro x hx
    obtain ⟨hx0, hxm⟩ := hx
    rw [← mul_sub, norm_mul, norm_col, one_mul]
    have h2 : x / ((m : ℝ) + 1) ≤ x / m := by
      rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < (m : ℝ) + 1)
        (by positivity : (0 : ℝ) < m)]
      nlinarith [hx0]
    have hlu : (n : ℝ) * (1 - x / m) ≤ n * (1 - x / (m + 1)) := by
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      nlinarith [h2]
    refine le_trans (norm_A_sub_le hlu) ?_
    apply le_of_eq
    field_simp
    ring
  have hb2 : ‖∫ x in (m : ℝ)..((m : ℝ) + 1), col x * A (n * (1 - x / (m + 1)))‖ ≤
      ∫ x in (m : ℝ)..((m : ℝ) + 1), (n * (1 - x / (m + 1))) := by
    have hle : (m : ℝ) ≤ (m : ℝ) + 1 := by linarith
    refine le_trans (norm_integral_le_integral_norm hle) ?_
    apply intervalIntegral.integral_mono_on hle ((colA_int (by continuity) _ _).norm)
      ((by continuity : Continuous fun x : ℝ => (n : ℝ) * (1 - x / (m + 1))).intervalIntegrable _ _)
    intro x hx
    obtain ⟨hx0, hxm⟩ := hx
    rw [norm_mul, norm_col, one_mul]
    have hu0 : (0 : ℝ) ≤ (n : ℝ) * (1 - x / (m + 1)) := by
      have h1 : (0 : ℝ) ≤ 1 - x / (m + 1) := by
        have hx2 : x / ((m : ℝ) + 1) ≤ 1 := by
          rw [div_le_one (by positivity : (0 : ℝ) < (m : ℝ) + 1)]
          linarith [hxm]
        linarith [hx2]
      exact mul_nonneg (Nat.cast_nonneg n) h1
    have h2 := norm_A_sub_le (l := (0 : ℝ)) (u := (n : ℝ) * (1 - x / (m + 1))) hu0
    rwa [A_zero, sub_zero, sub_zero] at h2
  rw [hD, ← Real.norm_eq_abs]
  calc ‖(∫ x in (0 : ℝ)..(m : ℝ), (col x * A (n * (1 - x / (m + 1))) - col x * A (n * (1 - x / m)))) +
        ∫ x in (m : ℝ)..((m : ℝ) + 1), col x * A (n * (1 - x / (m + 1)))‖
      ≤ ‖∫ x in (0 : ℝ)..(m : ℝ),
          (col x * A (n * (1 - x / (m + 1))) - col x * A (n * (1 - x / m)))‖ +
        ‖∫ x in (m : ℝ)..((m : ℝ) + 1), col x * A (n * (1 - x / (m + 1)))‖ := norm_add_le _ _
    _ ≤ (∫ x in (0 : ℝ)..(m : ℝ), (n * (x / m - x / (m + 1)))) +
        (∫ x in (m : ℝ)..((m : ℝ) + 1), (n * (1 - x / (m + 1)))) := add_le_add hb1 hb2
    _ = n / 2 := by rw [hI1, hI2]; field_simp

/-- Extending the second leg by `1` changes the color sum by at most `m/2`. -/
lemma abs_colorSum_sub_succ_le' {m n : ℕ} (hm : 0 < m) :
    |colorSum m (n + 1) - colorSum m n| ≤ m / 2 := by
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hD : colorSum m (n + 1) - colorSum m n =
      ∫ x in (0 : ℝ)..(m : ℝ),
        (col x * A ((n + 1) * (1 - x / m)) - col x * A (n * (1 - x / m))) := by
    rw [colorSum, colorSum]
    simp only [Nat.cast_succ]
    rw [← intervalIntegral.integral_sub
      (colA_int (by continuity) _ _) (colA_int (by continuity) _ _)]
  have hI : (∫ x in (0 : ℝ)..(m : ℝ),
      (((n : ℝ) + 1) * (1 - x / m) - n * (1 - x / m))) = m / 2 := by
    have hcongr : (∫ x in (0 : ℝ)..(m : ℝ),
        (((n : ℝ) + 1) * (1 - x / m) - n * (1 - x / m))) =
        ∫ x in (0 : ℝ)..(m : ℝ), ((-1 / m) * x + 1) := by
      apply integral_congr_ae_of_countable Set.countable_empty
      intro x _ _
      field_simp
      ring
    rw [hcongr, int_affine]
    field_simp
    ring
  have hb : ‖∫ x in (0 : ℝ)..(m : ℝ),
      (col x * A ((n + 1) * (1 - x / m)) - col x * A (n * (1 - x / m)))‖ ≤
      ∫ x in (0 : ℝ)..(m : ℝ), (((n : ℝ) + 1) * (1 - x / m) - n * (1 - x / m)) := by
    refine le_trans (norm_integral_le_integral_norm (Nat.cast_nonneg m)) ?_
    apply intervalIntegral.integral_mono_on (Nat.cast_nonneg m)
      (((colA_int (by continuity) _ _).sub (colA_int (by continuity) _ _)).norm)
      ((by continuity : Continuous fun x : ℝ =>
        ((n : ℝ) + 1) * (1 - x / m) - n * (1 - x / m)).intervalIntegrable _ _)
    intro x hx
    obtain ⟨hx0, hxm⟩ := hx
    rw [← mul_sub, norm_mul, norm_col, one_mul]
    have h10 : (0 : ℝ) ≤ 1 - x / m := by
      have hx2 : x / (m : ℝ) ≤ 1 := by
        rw [div_le_one (by positivity : (0 : ℝ) < m)]
        exact hxm
      linarith [hx2]
    have hlu : (n : ℝ) * (1 - x / m) ≤ ((n : ℝ) + 1) * (1 - x / m) := by nlinarith [h10]
    refine le_trans (norm_A_sub_le hlu) ?_
    apply le_of_eq
    ring
  rw [hD, ← Real.norm_eq_abs]
  exact hb.trans_eq hI

/-! ### The exact computation for part (c) -/

/-- Splitting an interval integral over `[0, n]` into unit pieces. -/
lemma int_eq_sum_unit {F : ℝ → ℝ} (hF : ∀ a b, IntervalIntegrable F volume a b) (n : ℕ) :
    ∫ y in (0 : ℝ)..(n : ℝ), F y = ∑ k ∈ Finset.range n, ∫ y in (k : ℝ)..((k : ℝ) + 1), F y := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Nat.cast_succ, ← integral_add_adjacent_intervals (hF 0 k) (hF k (k + 1)), ih,
      Finset.sum_range_succ]

/-- On the interval `(k, k + (n-k)/(n+1))` the sign `col ((n+1)/n · y)` equals `(-1)^k`. -/
lemma col_scale_left {n k : ℕ} (hn : 0 < n) {y : ℝ}
    (hyk : (k : ℝ) < y) (hy : y - (k : ℝ) < ((n : ℝ) - (k : ℝ)) / ((n : ℝ) + 1)) :
    col (((n : ℝ) + 1) / n * y) = (-1) ^ (k : ℤ) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by positivity
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hn0' : (n : ℝ) ≠ 0 := hn0.ne'
  set r := y - (k : ℝ) with hr
  have hr0 : 0 < r := by linarith [hyk]
  have h1 : r * ((n : ℝ) + 1) < (n : ℝ) - (k : ℝ) := by
    rw [lt_div_iff₀ hn1] at hy
    exact hy
  have hy0 : (0 : ℝ) < y := by linarith [hyk, Nat.cast_nonneg (α := ℝ) k]
  have hyn : (0 : ℝ) < y / n := div_pos hy0 hn0
  have hs0 : (0 : ℝ) < r + y / n := by linarith [hr0, hyn]
  have hs1 : r + y / n < 1 := by
    have h4 : (r + y / (n : ℝ)) * (n : ℝ) < 1 * n := by
      have heq : (r + y / (n : ℝ)) * (n : ℝ) = r * n + y := by
        field_simp [hn0']
      rw [heq]
      linarith [h1, hr]
    exact lt_of_mul_lt_mul_right h4 hn0.le
  have heq2 : ((n : ℝ) + 1) / n * y = (k : ℝ) + (r + y / n) := by
    rw [hr]
    field_simp [hn0']
    ring
  have hfloor : ⌊((n : ℝ) + 1) / n * y⌋ = (k : ℤ) := by
    rw [heq2, Int.floor_eq_iff]
    push_cast
    exact ⟨by linarith [hs0.le], by linarith [hs1]⟩
  rw [col, hfloor]

/-- On the interval `(k + (n-k)/(n+1), k+1)` the sign `col ((n+1)/n · y)` equals
`(-1)^(k+1)`. -/
lemma col_scale_right {n k : ℕ} (hn : 0 < n) (hk : k < n) {y : ℝ}
    (hy1 : (k : ℝ) + ((n : ℝ) - (k : ℝ)) / ((n : ℝ) + 1) < y) (hy2 : y < (k : ℝ) + 1) :
    col (((n : ℝ) + 1) / n * y) = (-1) ^ ((k : ℤ) + 1) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by positivity
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hn0' : (n : ℝ) ≠ 0 := hn0.ne'
  set r := y - (k : ℝ) with hr
  have h1 : ((n : ℝ) - (k : ℝ)) / ((n : ℝ) + 1) < r := by linarith [hy1, hr]
  have hr1 : (n : ℝ) - (k : ℝ) < r * ((n : ℝ) + 1) := by
    rw [div_lt_iff₀ hn1] at h1
    exact h1
  have hs1 : 1 < r + y / n := by
    have h4 : (1 : ℝ) * n < (r + y / (n : ℝ)) * (n : ℝ) := by
      have heq : (r + y / (n : ℝ)) * (n : ℝ) = r * n + y := by
        field_simp [hn0']
      rw [heq]
      linarith [hr1, hr]
    exact lt_of_mul_lt_mul_right h4 hn0.le
  have hs2 : r + y / n < 2 := by
    have hy3 : y < (n : ℝ) := by
      have h5 : (k : ℝ) + 1 ≤ (n : ℝ) := by
        have h6 : k + 1 ≤ n := hk
        calc (k : ℝ) + 1 = ((k + 1 : ℕ) : ℝ) := by norm_cast
          _ ≤ (n : ℝ) := Nat.cast_le.mpr h6
      linarith [hy2, h5]
    have hyn : y / (n : ℝ) < 1 := by
      rw [div_lt_one hn0]
      exact hy3
    have hr2 : r < 1 := by linarith [hy2, hr]
    linarith [hyn, hr2]
  have heq2 : ((n : ℝ) + 1) / n * y = ((k : ℝ) + 1) + (r + y / n - 1) := by
    rw [hr]
    field_simp [hn0']
    ring
  have hfloor : ⌊((n : ℝ) + 1) / n * y⌋ = (k : ℤ) + 1 := by
    rw [heq2, Int.floor_eq_iff]
    push_cast
    exact ⟨by linarith [hs1], by linarith [hs2]⟩
  rw [col, hfloor]

/-- The contribution of the unit interval `[k, k+1]` to the sum in part (c). -/
noncomputable def termF (n k : ℕ) : ℝ :=
  (-1) ^ (k : ℤ) *
    (if Even k then (((n : ℝ) - (k : ℝ)) / ((n : ℝ) + 1)) ^ 2 - 1 / 2
      else 2 * (((n : ℝ) - (k : ℝ)) / ((n : ℝ) + 1)) -
        (((n : ℝ) - (k : ℝ)) / ((n : ℝ) + 1)) ^ 2 - 1 / 2)

/-- The integral of `col ((n+1)/n · y) * A y` over one unit interval `[k, k+1]` with
`k < n`, split at the crossing point `k + (n-k)/(n+1)` of the scaled diagonal with the
integer grid. -/
lemma unit_int {n k : ℕ} (hn : 0 < n) (hk : k < n) :
    ∫ y in (k : ℝ)..((k : ℝ) + 1), col (((n : ℝ) + 1) / n * y) * A y = termF n k := by
  rw [termF]
  set rk := ((n : ℝ) - (k : ℝ)) / ((n : ℝ) + 1) with hrk
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hrk0 : (0 : ℝ) < rk := by
    have h1 : (0 : ℝ) < (n : ℝ) - (k : ℝ) := by
      simp only [sub_pos]
      exact Nat.cast_lt.mpr hk
    exact div_pos h1 (by positivity)
  have hrk1 : rk < 1 := by
    rw [hrk, div_lt_one (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
    simp only [sub_lt_iff_lt_add]
    nlinarith [hk0]
  have hF : ∀ a b : ℝ,
      IntervalIntegrable (fun y => col (((n : ℝ) + 1) / n * y) * A y) volume a b :=
    fun a b => (colComp_int (by measurability) a b).mul_continuousOn A_cont.continuousOn
  have hsplit : (∫ y in (k : ℝ)..((k : ℝ) + 1), col (((n : ℝ) + 1) / n * y) * A y) =
      (∫ y in (k : ℝ)..((k : ℝ) + rk), col (((n : ℝ) + 1) / n * y) * A y) +
        ∫ y in (k : ℝ) + rk..((k : ℝ) + 1), col (((n : ℝ) + 1) / n * y) * A y :=
    (integral_add_adjacent_intervals (hF _ _) (hF _ _)).symm
  have hA : ∀ y ∈ Set.Ioo (k : ℝ) ((k : ℝ) + 1),
      A y = if Even k then y - (k : ℝ) else 1 - (y - (k : ℝ)) := by
    intro y hy
    exact A_apply_of_mem_Ico ⟨hy.1.le, hy.2⟩
  have hleft : (∫ y in (k : ℝ)..((k : ℝ) + rk), col (((n : ℝ) + 1) / n * y) * A y) =
      (-1) ^ (k : ℤ) *
        ∫ y in (k : ℝ)..((k : ℝ) + rk), (if Even k then y - (k : ℝ) else 1 - (y - (k : ℝ))) := by
    have hcong : (∫ y in (k : ℝ)..((k : ℝ) + rk), col (((n : ℝ) + 1) / n * y) * A y) =
        ∫ y in (k : ℝ)..((k : ℝ) + rk),
          (-1) ^ (k : ℤ) * (if Even k then y - (k : ℝ) else 1 - (y - (k : ℝ))) := by
      apply integral_congr_ae_of_countable Set.countable_empty
      intro y hy _
      have hle : (k : ℝ) ≤ (k : ℝ) + rk := by linarith [hrk0.le]
      rw [min_eq_left hle, max_eq_right hle] at hy
      have h5 : y - (k : ℝ) < rk := by linarith [hy.2, hrk0]
      have hyA : y ∈ Set.Ioo (k : ℝ) ((k : ℝ) + 1) :=
        ⟨hy.1, hy.2.trans_le (by linarith [hrk1] : (k : ℝ) + rk ≤ (k : ℝ) + 1)⟩
      rw [col_scale_left hn hy.1 h5, hA y hyA]
    rw [hcong, intervalIntegral.integral_const_mul]
  have hright : (∫ y in (k : ℝ) + rk..((k : ℝ) + 1), col (((n : ℝ) + 1) / n * y) * A y) =
      (-1) ^ ((k : ℤ) + 1) *
        ∫ y in (k : ℝ) + rk..((k : ℝ) + 1), (if Even k then y - (k : ℝ) else 1 - (y - (k : ℝ))) := by
    have hcong : (∫ y in (k : ℝ) + rk..((k : ℝ) + 1), col (((n : ℝ) + 1) / n * y) * A y) =
        ∫ y in (k : ℝ) + rk..((k : ℝ) + 1),
          (-1) ^ ((k : ℤ) + 1) * (if Even k then y - (k : ℝ) else 1 - (y - (k : ℝ))) := by
      apply integral_congr_ae_of_countable Set.countable_empty
      intro y hy _
      have hle : (k : ℝ) + rk ≤ (k : ℝ) + 1 := by linarith [hrk1.le]
      rw [min_eq_left hle, max_eq_right hle] at hy
      have hyA : y ∈ Set.Ioo (k : ℝ) ((k : ℝ) + 1) :=
        ⟨by linarith [hy.1, hrk0], hy.2⟩
      rw [col_scale_right hn hk hy.1 hy.2, hA y hyA]
    rw [hcong, intervalIntegral.integral_const_mul]
  rw [hsplit, hleft, hright]
  rcases Nat.even_or_odd k with he | ho
  · have hint1 : ∫ y in (k : ℝ)..((k : ℝ) + rk), (if Even k then y - (k : ℝ) else 1 - (y - (k : ℝ))) =
        rk ^ 2 / 2 := by
      simp only [if_pos he]
      have hcongr : (∫ y in (k : ℝ)..((k : ℝ) + rk), (y - (k : ℝ))) =
          ∫ y in (k : ℝ)..((k : ℝ) + rk), (1 * y + (-(k : ℝ))) := by
        apply integral_congr_ae_of_countable Set.countable_empty
        intro y _ _
        ring
      rw [hcongr, int_affine]
      ring
    have hint2 : ∫ y in (k : ℝ) + rk..((k : ℝ) + 1), (if Even k then y - (k : ℝ) else 1 - (y - (k : ℝ))) =
        (1 - rk ^ 2) / 2 := by
      simp only [if_pos he]
      have hcongr : (∫ y in (k : ℝ) + rk..((k : ℝ) + 1), (y - (k : ℝ))) =
          ∫ y in (k : ℝ) + rk..((k : ℝ) + 1), (1 * y + (-(k : ℝ))) := by
        apply integral_congr_ae_of_countable Set.countable_empty
        intro y _ _
        ring
      rw [hcongr, int_affine]
      ring
    have hO : Odd ((k : ℤ) + 1) := by
      have hO' := (Int.odd_coe_nat _).mpr he.add_one
      rwa [Nat.cast_add, Nat.cast_one] at hO'
    rw [hint1, hint2, if_pos he, Even.neg_one_zpow ((Int.even_coe_nat _).mpr he),
      Odd.neg_one_zpow hO]
    ring
  · have hint1 : ∫ y in (k : ℝ)..((k : ℝ) + rk), (if Even k then y - (k : ℝ) else 1 - (y - (k : ℝ))) =
        rk - rk ^ 2 / 2 := by
      simp only [if_neg (Nat.not_even_iff_odd.mpr ho)]
      have hcongr : (∫ y in (k : ℝ)..((k : ℝ) + rk), (1 - (y - (k : ℝ)))) =
          ∫ y in (k : ℝ)..((k : ℝ) + rk), ((-1) * y + (1 + (k : ℝ))) := by
        apply integral_congr_ae_of_countable Set.countable_empty
        intro y _ _
        ring
      rw [hcongr, int_affine]
      ring
    have hint2 : ∫ y in (k : ℝ) + rk..((k : ℝ) + 1), (if Even k then y - (k : ℝ) else 1 - (y - (k : ℝ))) =
        1 / 2 - rk + rk ^ 2 / 2 := by
      simp only [if_neg (Nat.not_even_iff_odd.mpr ho)]
      have hcongr : (∫ y in (k : ℝ) + rk..((k : ℝ) + 1), (1 - (y - (k : ℝ)))) =
          ∫ y in (k : ℝ) + rk..((k : ℝ) + 1), ((-1) * y + (1 + (k : ℝ))) := by
        apply integral_congr_ae_of_countable Set.countable_empty
        intro y _ _
        ring
      rw [hcongr, int_affine]
      ring
    have hE : Even ((k : ℤ) + 1) := by
      have hE' := (Int.even_coe_nat _).mpr ho.add_one
      rwa [Nat.cast_add, Nat.cast_one] at hE'
    rw [hint1, hint2, if_neg (Nat.not_even_iff_odd.mpr ho), Even.neg_one_zpow hE,
      Odd.neg_one_zpow ((Int.odd_coe_nat _).mpr ho)]
    ring

/-- Summing over pairs of consecutive indices. -/
lemma sum_range_pair {g : ℕ → ℝ} (t : ℕ) :
    ∑ k ∈ Finset.range (2 * t), g k = ∑ j ∈ Finset.range t, (g (2 * j) + g (2 * j + 1)) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [show 2 * (t + 1) = 2 * t + 2 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ]
    ring

/-- Reindexing a finite sum: `∑_{j<t} F (t-j) = ∑_{j<t} F (j+1)` for real arguments. -/
lemma sum_range_reindex {F : ℝ → ℝ} {t : ℕ} :
    (∑ j ∈ Finset.range t, F ((t : ℝ) - j)) = ∑ j ∈ Finset.range t, F ((j : ℝ) + 1) := by
  rw [← Finset.sum_range_reflect (fun j => F ((t : ℝ) - j)) t]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  have h4 : ((t - 1 - j : ℕ) : ℝ) + ((j : ℝ) + 1) = (t : ℝ) := by
    have h3 : (t - 1 - j) + (j + 1) = t := by omega
    calc ((t - 1 - j : ℕ) : ℝ) + ((j : ℝ) + 1)
        = (((t - 1 - j) + (j + 1) : ℕ) : ℝ) := by push_cast; ring
      _ = t := by rw [h3]
  have h5 : (t : ℝ) - ((t - 1 - j : ℕ) : ℝ) = (j : ℝ) + 1 := by linarith [h4]
  rw [h5]

/-- `∑_{j<t} (j+1)² = t(t+1)(2t+1)/6`. -/
lemma sum_sq_succ (t : ℕ) :
    ∑ j ∈ Finset.range t, ((j : ℝ) + 1) ^ 2 =
      (t : ℝ) * ((t : ℝ) + 1) * (2 * (t : ℝ) + 1) / 6 := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    field_simp
    ring

/-- `∑_{j<t} (2(j+1) - 1) = t²`. -/
lemma sum_two_succ (t : ℕ) :
    ∑ j ∈ Finset.range t, (2 * ((j : ℝ) + 1) - 1) = (t : ℝ) ^ 2 := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-- `∑_{j<t} (2(j+1) - 1)² = t(2t-1)(2t+1)/3`. -/
lemma sum_two_succ_sq (t : ℕ) :
    ∑ j ∈ Finset.range t, (2 * ((j : ℝ) + 1) - 1) ^ 2 =
      (t : ℝ) * (2 * (t : ℝ) - 1) * (2 * (t : ℝ) + 1) / 3 := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    field_simp
    ring

/-- For positive even `n`, the color sum of the `(n+1, n)` triangle is `-(n-1)/6`. -/
lemma colorSum_succ_self {n : ℕ} (hn : 0 < n) (hn2 : Even n) :
    colorSum (n + 1) n = -((n : ℝ) - 1) / 6 := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by positivity
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hn0' : (n : ℝ) ≠ 0 := hn0.ne'
  have hF : ∀ a b : ℝ,
      IntervalIntegrable (fun y => col (((n : ℝ) + 1) / n * y) * A y) volume a b :=
    fun a b => (colComp_int (by measurability) a b).mul_continuousOn A_cont.continuousOn
  -- steps 1–4: rewrite the color sum as a scaled integral over `[0, n]`
  have step14 : colorSum (n + 1) n =
      ((n : ℝ) + 1) / n * ∫ y in (0 : ℝ)..(n : ℝ), col (((n : ℝ) + 1) / n * y) * A y := by
    have h1 : (∫ x in (0 : ℝ)..((n : ℝ) + 1),
          col (((n : ℝ) + 1) - x) * A (n * (1 - ((n : ℝ) + 1 - x) / ((n : ℝ) + 1)))) =
        colorSum (n + 1) n := by
      rw [integral_comp_sub_left (f := fun x => col x * A (n * (1 - x / ((n : ℝ) + 1))))
        (d := (n : ℝ) + 1)]
      simp [colorSum]
    have hsign : (-1 : ℝ) ^ (((n + 1 : ℕ) : ℤ) + 1) = 1 := by
      apply Even.neg_one_zpow
      have he2 : Even (n + 2) := Even.add hn2 ⟨1, rfl⟩
      have h2 := (Int.even_coe_nat _).mpr he2
      rwa [Nat.cast_add, Nat.cast_two] at h2
    have hsign' : ∀ x : ℝ, x ∉ Set.range Int.cast → col (((n : ℝ) + 1) - x) = col x := by
      intro x hx
      have h3 := col_int_sub (n + 1) hx
      rw [Nat.cast_succ] at h3
      rw [h3, hsign, one_mul]
    have hcong : (∫ x in (0 : ℝ)..((n : ℝ) + 1),
          col (((n : ℝ) + 1) - x) * A (n * (1 - ((n : ℝ) + 1 - x) / ((n : ℝ) + 1)))) =
        ∫ x in (0 : ℝ)..((n : ℝ) + 1), col x * A (n * x / ((n : ℝ) + 1)) := by
      apply integral_congr_ae_of_countable (Set.countable_range Int.cast)
      intro x _ hxI
      rw [hsign' x hxI]
      congr 1
      congr 1
      field_simp [hn1.ne']
      ring
    have hcong2 : (∫ x in (0 : ℝ)..((n : ℝ) + 1), col x * A (n * x / ((n : ℝ) + 1))) =
        ∫ x in (0 : ℝ)..((n : ℝ) + 1),
          col (((n : ℝ) + 1) / n * (x * (n / ((n : ℝ) + 1)))) * A (x * (n / ((n : ℝ) + 1))) := by
      apply integral_congr_ae_of_countable Set.countable_empty
      intro x _ _
      have he1 : ((n : ℝ) + 1) / n * (x * (n / ((n : ℝ) + 1))) = x := by
        field_simp [hn0', hn1.ne']
      have he2 : n * x / ((n : ℝ) + 1) = x * (n / ((n : ℝ) + 1)) := by ring
      rw [he2, congrArg col he1.symm]
    have hcomp : (∫ x in (0 : ℝ)..((n : ℝ) + 1),
          col (((n : ℝ) + 1) / n * (x * (n / ((n : ℝ) + 1)))) * A (x * (n / ((n : ℝ) + 1)))) =
        ((n : ℝ) + 1) / n * ∫ y in (0 : ℝ)..(n : ℝ), col (((n : ℝ) + 1) / n * y) * A y := by
      have hc0 : (n : ℝ) / ((n : ℝ) + 1) ≠ 0 := div_ne_zero hn0' hn1.ne'
      rw [integral_comp_mul_right (f := fun y => col (((n : ℝ) + 1) / n * y) * A y) hc0]
      have hc1 : ((n : ℝ) + 1) * (n / ((n : ℝ) + 1)) = n := by field_simp [hn1.ne']
      have hc2 : ((n : ℝ) / ((n : ℝ) + 1))⁻¹ = ((n : ℝ) + 1) / n := by
        field_simp [hn0', hn1.ne']
      rw [hc1, hc2]
      simp [smul_eq_mul]
    rw [← h1, hcong, hcong2, hcomp]
  -- steps 5–6: split into unit intervals and evaluate each
  have assemble : colorSum (n + 1) n =
      ((n : ℝ) + 1) / n * ∑ k ∈ Finset.range n, termF n k := by
    rw [step14, int_eq_sum_unit hF n]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    exact unit_int hn hk
  -- step 7: evaluate the sum for `n = 2t`
  have key : ∑ k ∈ Finset.range n, termF n k = (n : ℝ) * (1 - n) / (6 * ((n : ℝ) + 1)) := by
    obtain ⟨t, ht⟩ := hn2
    have ht0 : 0 < t := by omega
    have ht0' : (t : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr ht0.ne'
    have h2t1' : (2 * (t : ℝ) + 1) ≠ 0 := by positivity
    rw [ht, show t + t = 2 * t by ring, sum_range_pair]
    -- the pair of consecutive terms
    have hterm : ∀ j : ℕ, termF (2 * t) (2 * j) + termF (2 * t) (2 * j + 1) =
        ((((2 * t : ℕ) : ℝ) - ((2 * j : ℕ) : ℝ)) / (((2 * t : ℕ) : ℝ) + 1)) ^ 2 +
          ((((2 * t : ℕ) : ℝ) - ((2 * j + 1 : ℕ) : ℝ)) / (((2 * t : ℕ) : ℝ) + 1)) ^ 2 -
          2 * ((((2 * t : ℕ) : ℝ) - ((2 * j + 1 : ℕ) : ℝ)) / (((2 * t : ℕ) : ℝ) + 1)) := by
      intro j
      have he : Even (2 * j) := ⟨j, by ring⟩
      have hne : ¬Even (2 * j + 1) := Nat.not_even_iff_odd.mpr he.add_one
      rw [termF, termF, if_pos he, if_neg hne, Even.neg_one_zpow ((Int.even_coe_nat _).mpr he),
        Odd.neg_one_zpow ((Int.odd_coe_nat _).mpr he.add_one)]
      ring
    -- evaluate the numerators
    have hpoint : ∀ j : ℕ,
        ((((2 * t : ℕ) : ℝ) - ((2 * j : ℕ) : ℝ)) / (((2 * t : ℕ) : ℝ) + 1)) ^ 2 +
          ((((2 * t : ℕ) : ℝ) - ((2 * j + 1 : ℕ) : ℝ)) / (((2 * t : ℕ) : ℝ) + 1)) ^ 2 -
          2 * ((((2 * t : ℕ) : ℝ) - ((2 * j + 1 : ℕ) : ℝ)) / (((2 * t : ℕ) : ℝ) + 1)) =
        (1 / (2 * (t : ℝ) + 1) ^ 2) *
          (4 * ((t : ℝ) - j) ^ 2 + (2 * ((t : ℝ) - j) - 1) ^ 2 -
            2 * (2 * (t : ℝ) + 1) * (2 * ((t : ℝ) - j) - 1)) := by
      intro j
      have e1 : (((2 * t : ℕ) : ℝ) - ((2 * j : ℕ) : ℝ)) / (((2 * t : ℕ) : ℝ) + 1) =
          2 * ((t : ℝ) - j) / (2 * (t : ℝ) + 1) := by
        push_cast
        field_simp [h2t1']
      have e2 : (((2 * t : ℕ) : ℝ) - ((2 * j + 1 : ℕ) : ℝ)) / (((2 * t : ℕ) : ℝ) + 1) =
          (2 * ((t : ℝ) - j) - 1) / (2 * (t : ℝ) + 1) := by
        push_cast
        field_simp [h2t1']
        ring
      rw [e1, e2]
      field_simp [h2t1']
      ring
    have hnum : ∑ j ∈ Finset.range t,
          (4 * ((t : ℝ) - j) ^ 2 + (2 * ((t : ℝ) - j) - 1) ^ 2 -
            2 * (2 * (t : ℝ) + 1) * (2 * ((t : ℝ) - j) - 1)) =
        4 * ((t : ℝ) * ((t : ℝ) + 1) * (2 * (t : ℝ) + 1) / 6) +
          (t : ℝ) * (2 * (t : ℝ) - 1) * (2 * (t : ℝ) + 1) / 3 -
          (2 * (2 * (t : ℝ) + 1)) * (t : ℝ) ^ 2 := by
      have hre := sum_range_reindex (t := t) (F := fun u => 4 * u ^ 2 + (2 * u - 1) ^ 2 -
        2 * (2 * (t : ℝ) + 1) * (2 * u - 1))
      rw [hre, Finset.sum_sub_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum, sum_sq_succ, sum_two_succ_sq, sum_two_succ]
    rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_congr rfl (fun j _ => hpoint j),
      ← Finset.mul_sum, hnum]
    push_cast
    field_simp [ht0', h2t1']
    ring
  rw [assemble, key]
  field_simp [hn0', hn1.ne']
  ring

snip end

/-- The answer to part (a): `f(m,n) = 0` when `m,n` are both even and `1/2` when both
are odd. -/
noncomputable determine answer (m n : ℕ) : ℝ := if Even m ∧ Even n then 0 else 1 / 2

problem imo1997_p1_a (m n : ℕ) (hm : 0 < m) (_hn : 0 < n)
    (h : Even m ∧ Even n ∨ Odd m ∧ Odd n) : f m n = answer m n := by
  have hpar : Even (m + n) := by
    rcases h with ⟨⟨hem, hen⟩⟩ | ⟨hom, hon⟩
    · obtain ⟨a, ha⟩ := hem
      obtain ⟨b, hb⟩ := hen
      exact ⟨a + b, by rw [ha, hb]; ring⟩
    · obtain ⟨a, ha⟩ := hom
      obtain ⟨b, hb⟩ := hon
      exact ⟨a + b + 1, by rw [ha, hb]; ring⟩
  have hS := colorSum_same_parity hm hpar
  rcases h with ⟨hem, hen⟩ | ⟨hom, hon⟩
  · have hm0 : A m = 0 := by rw [A_nat m, if_pos hem]
    rw [hm0] at hS
    have hS0 : colorSum m n = 0 := by linear_combination hS
    rw [f, hS0, answer, if_pos ⟨hem, hen⟩, abs_zero]
  · have hm1 : A m = 1 := by rw [A_nat m, if_neg (Nat.not_even_iff_odd.mpr hom)]
    have hn1 : A n = 1 := by rw [A_nat n, if_neg (Nat.not_even_iff_odd.mpr hon)]
    have hsign : (-1 : ℝ) ^ ((n : ℤ) + 1) = 1 := by
      apply Even.neg_one_zpow
      have h2 := (Int.even_coe_nat _).mpr hon.add_one
      rwa [Nat.cast_add, Nat.cast_one] at h2
    rw [hm1, hn1, hsign] at hS
    have hS' : colorSum m n = 1 / 2 := by linear_combination hS
    have hne : ¬(Even m ∧ Even n) := fun hh => Nat.not_even_iff_odd.mpr hom hh.1
    rw [f, hS', answer, if_neg hne, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]

problem imo1997_p1_b (m n : ℕ) (hm : 0 < m) (_hn : 0 < n) :
    f m n ≤ max m n / 2 := by
  have hmax1 : (1 : ℝ) ≤ max (m : ℝ) (n : ℝ) := le_max_of_le_left (Nat.one_le_cast.mpr hm)
  rcases Nat.even_or_odd (m + n) with hpar | hpar
  · -- same parity: `|colorSum| ≤ 1/2 ≤ max/2`
    have hS := colorSum_same_parity hm hpar
    have hbound : |colorSum m n| ≤ 1 / 2 := by
      rw [hS]
      rcases Nat.even_or_odd m with hem | hom
      · rw [A_nat m, if_pos hem]
        norm_num
      · rw [A_nat m, if_neg (Nat.not_even_iff_odd.mpr hom)]
        have hAn : |A (n : ℝ)| ≤ 1 := by
          rw [A_nat n]
          rcases Nat.even_or_odd n with hen | hon
          · rw [if_pos hen]; norm_num
          · rw [if_neg (Nat.not_even_iff_odd.mpr hon)]; norm_num
        have e : |(-1 : ℝ) ^ ((n : ℤ) + 1) * A (n : ℝ) * 1 / 2| = |A (n : ℝ)| / 2 := by
          rw [mul_one, abs_div, abs_mul, show |(-1 : ℝ) ^ ((n : ℤ) + 1)| = 1 by simp,
            show |(2 : ℝ)| = 2 by norm_num, one_mul]
        rw [e]
        linarith [hAn]
    rw [f, Nat.cast_max]
    linarith [hbound, hmax1]
  · -- opposite parity: extend the odd leg by `1` and use part (a)
    have hcases : (Odd m ∧ Even n) ∨ (Even m ∧ Odd n) := by
      rcases Nat.even_or_odd m with hem | hom
      · rcases Nat.even_or_odd n with hen | hon
        · exact absurd (Even.add hem hen) (Nat.not_even_iff_odd.mpr hpar)
        · exact Or.inr ⟨hem, hon⟩
      · rcases Nat.even_or_odd n with hen | hon
        · exact Or.inl ⟨hom, hen⟩
        · exact absurd (hom.add_odd hon) (Nat.not_even_iff_odd.mpr hpar)
    rcases hcases with ⟨hom, hen⟩ | ⟨hem, hon⟩
    · -- `m` odd, `n` even: extend the first leg; the bound is `n/2`
      have h0 : colorSum (m + 1) n = 0 := by
        have hS := colorSum_same_parity (Nat.succ_pos m) (Even.add hom.add_one hen)
        rw [A_nat (m + 1), if_pos hom.add_one] at hS
        linear_combination hS
      have hle := abs_colorSum_sub_succ_le (n := n) hm
      rw [h0, zero_sub, abs_neg] at hle
      have hnmax : (n : ℝ) ≤ max (m : ℝ) (n : ℝ) := le_max_right _ _
      rw [f, Nat.cast_max]
      linarith [hle, hnmax]
    · -- `m` even, `n` odd: extend the second leg; the bound is `m/2`
      have h0 : colorSum m (n + 1) = 0 := by
        have hS := colorSum_same_parity (n := n + 1) hm (Even.add hem hon.add_one)
        rw [A_nat m, if_pos hem] at hS
        linear_combination hS
      have hle := abs_colorSum_sub_succ_le' (n := n) hm
      rw [h0, zero_sub, abs_neg] at hle
      have hmmax : (m : ℝ) ≤ max (m : ℝ) (n : ℝ) := le_max_left _ _
      rw [f, Nat.cast_max]
      linarith [hle, hmmax]

problem imo1997_p1_c : ∀ C : ℝ, ∃ m n : ℕ, 0 < m ∧ 0 < n ∧ C < f m n := by
  intro C
  obtain ⟨t, ht⟩ := exists_nat_gt ((6 * C + 1) / 2)
  -- with `n = 2 * (t + 1)` (even) we have `f (n+1) n = (n-1)/6 > C`
  have hev : Even (2 * (t + 1)) := ⟨t + 1, by ring⟩
  have hval := colorSum_succ_self (n := 2 * (t + 1)) (by positivity) hev
  refine ⟨2 * (t + 1) + 1, 2 * (t + 1), by positivity, by positivity, ?_⟩
  have hpos : (0 : ℝ) ≤ ((2 * (t + 1) : ℕ) : ℝ) - 1 := by
    have h1 : (1 : ℝ) ≤ ((2 * (t + 1) : ℕ) : ℝ) := Nat.one_le_cast.mpr (by omega)
    linarith
  have hcast : ((2 * (t + 1) : ℕ) : ℝ) = 2 * (t : ℝ) + 2 := by push_cast; ring
  rw [f, hval, neg_div, abs_neg, abs_of_nonneg (div_nonneg hpos (by norm_num)), hcast]
  linarith [ht]

end Imo1997P1
