/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.ConditionallyCompleteOrder
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Star
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Ring.Basic
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics] }

/-!
# USA Mathematical Olympiad 2008, Problem 3

Let n be a positive integer. Denote by Sₙ the set of points (x, y)
with integer coordinates such that

  |x| + |y + 1/2| < n.

A path is a sequence of distinct points (x₁, y₁), (x₂, y₂), ..., (x_ℓ, y_ℓ)
in Sₙ such that, for i = 2, ..., ℓ, the distance between (xᵢ, yᵢ) and
(xᵢ₋₁, yᵢ₋₁) is 1. Prove that the points in Sₙ cannot be partitioned into
fewer than n paths.
-/

namespace Usa2008P3

/-- The half-width of the row of `S n` at height `y`: the row consists of the
points `(x, y)` with `|x| ≤ rowK n y`. -/
def rowK (n : ℕ) (y : ℤ) : ℤ := if 0 ≤ y then (n : ℤ) - 1 - y else (n : ℤ) + y

/-- The set `Sₙ` of the problem, namely the integer points `(x, y)` with
`|x| + |y + 1/2| < n`.  Multiplying by two, this is `2|x| + |2y + 1| < 2n`,
and we build the set row by row. -/
noncomputable def S (n : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.Icc (-(n : ℤ)) ((n : ℤ) - 1)).biUnion fun y ↦
    (Finset.Icc (-(rowK n y)) (rowK n y)) ×ˢ {y}

/-- Two lattice points are adjacent when their (Manhattan) distance is 1. -/
def Adj (p q : ℤ × ℤ) : Prop := |p.1 - q.1| + |p.2 - q.2| = 1

snip begin

/-!
### Proof overview

We follow the official "global" solution (see e.g. Evan Chen's *USAMO 2008
Solution Notes*).  Colour the point `(x, y)` **blue** when
`2x + |2y + 1| ≡ 2n - 1 (mod 4)` and **red** otherwise; this is the
checkerboard colouring of each half, reflected across the horizontal symmetry
axis `y = -1/2`.  Then

* there are exactly `2n` more blue points than red points
  (`sum_chi`: the `±1` sum over `S n` equals `2n`);
* two adjacent blue points must form a vertical pair `{(x, 0), (x, -1)}`
  crossing the axis (`blue_adj`); hence every blue-blue adjacency inside a
  path can be charged to a distinct blue point on the axis `y = 0`, and
  there are exactly `n` such points (`card_B0`);
* after cutting every path at its blue-blue adjacencies, each piece
  alternates colours except for possible red-red pairs, so each piece has
  `#blue ≤ #red + 1`; packaged in `path_bound`, every path's colour sum
  exceeds its number of blue axial points by at most one.

If `m` paths partition `Sₙ`, this gives `2n ≤ m + n`, hence `m ≥ n`.
-/

/-- The auxiliary potential: blue points are those with `f p ≡ 2n - 1 (mod 4)`. -/
def f (p : ℤ × ℤ) : ℤ := 2 * p.1 + |2 * p.2 + 1|

/-- The blue predicate. -/
def blue (n : ℕ) (p : ℤ × ℤ) : Prop := f p ≡ 2 * (n : ℤ) - 1 [ZMOD 4]

instance (n : ℕ) : DecidablePred (blue n) :=
  fun p ↦ inferInstanceAs (Decidable (f p ≡ 2 * (n : ℤ) - 1 [ZMOD 4]))

/-- The colour of a point as `±1` (`+1` for blue, `-1` for red). -/
def chi (n : ℕ) (p : ℤ × ℤ) : ℤ := if blue n p then 1 else -1

/-- The sum of colours along a list of points. -/
def sig (n : ℕ) (P : List (ℤ × ℤ)) : ℤ := (P.map (chi n)).sum

/-- The number of blue points on the axis `y = 0` in a list. -/
def b0 (n : ℕ) (P : List (ℤ × ℤ)) : ℤ :=
  ((P.filter (fun p ↦ decide (blue n p ∧ p.2 = 0))).length : ℤ)

/-- The "good head" condition on a list: either the head is red, or it lies in
`B₀` (blue, `y = 0`) and the second point (if any) is red.  For such lists the
colour sum is at most the number of `B₀`-points. -/
def GH (n : ℕ) : List (ℤ × ℤ) → Prop
  | [] => True
  | [p] => ¬ blue n p ∨ p.2 = 0
  | p :: q :: _ => ¬ blue n p ∨ (p.2 = 0 ∧ ¬ blue n q)

lemma chi_of_blue {n : ℕ} {p : ℤ × ℤ} (h : blue n p) : chi n p = 1 := ite_eq_left h

lemma chi_of_not_blue {n : ℕ} {p : ℤ × ℤ} (h : ¬ blue n p) : chi n p = -1 := ite_eq_right h

lemma sig_cons (n : ℕ) (p : ℤ × ℤ) (tl : List (ℤ × ℤ)) :
    sig n (p :: tl) = chi n p + sig n tl := rfl

lemma sig_nil (n : ℕ) : sig n [] = 0 := rfl

lemma b0_cons (n : ℕ) (p : ℤ × ℤ) (tl : List (ℤ × ℤ)) :
    b0 n (p :: tl) = (if blue n p ∧ p.2 = 0 then (1 : ℤ) else 0) + b0 n tl := by
  unfold b0
  by_cases h : blue n p ∧ p.2 = 0
  · rw [ite_eq_left h, List.filter_cons_of_pos (by simp [h]), List.length_cons]
    push_cast
    ring
  · rw [ite_eq_right h, List.filter_cons_of_neg (by simp [h])]
    simp

lemma b0_nil (n : ℕ) : b0 n [] = 0 := rfl

lemma rowK_of_nonneg (n : ℕ) {y : ℤ} (hy : 0 ≤ y) : rowK n y = (n : ℤ) - 1 - y := by
  rw [show rowK n y = if 0 ≤ y then (n : ℤ) - 1 - y else (n : ℤ) + y from rfl, ite_eq_left hy]

lemma rowK_of_neg (n : ℕ) {y : ℤ} (hy : ¬ 0 ≤ y) : rowK n y = (n : ℤ) + y := by
  rw [show rowK n y = if 0 ≤ y then (n : ℤ) - 1 - y else (n : ℤ) + y from rfl, ite_eq_right hy]

/-! ## Geometry: membership of `S n` and the adjacency lemmas -/

lemma mem_S {n : ℕ} {p : ℤ × ℤ} :
    p ∈ S n ↔ 2 * |p.1| + |2 * p.2 + 1| < 2 * (n : ℤ) := by
  simp only [S]
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨y, hy, hp⟩
    rw [Finset.mem_Icc] at hy
    rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_singleton] at hp
    obtain ⟨⟨h1, h2⟩, h3⟩ := hp
    subst h3
    by_cases hy0 : 0 ≤ p.2
    · rw [rowK_of_nonneg n hy0] at h1 h2
      have hp1 : |p.1| ≤ (n : ℤ) - 1 - p.2 := abs_le.mpr ⟨h1, h2⟩
      have hp2 : |2 * p.2 + 1| = 2 * p.2 + 1 := abs_of_nonneg (by omega)
      omega
    · rw [rowK_of_neg n hy0] at h1 h2
      have hp1 : |p.1| ≤ (n : ℤ) + p.2 := abs_le.mpr ⟨h1, h2⟩
      have hp2 : |2 * p.2 + 1| = -(2 * p.2 + 1) := abs_of_neg (by omega)
      omega
  · intro h
    have hk : |p.1| ≤ rowK n p.2 ∧ p.2 ∈ Finset.Icc (-(n : ℤ)) ((n : ℤ) - 1) := by
      rw [Finset.mem_Icc]
      by_cases hy0 : 0 ≤ p.2
      · rw [rowK_of_nonneg n hy0]
        have hp2 : |2 * p.2 + 1| = 2 * p.2 + 1 := abs_of_nonneg (by omega)
        have hb := abs_nonneg (p.1 : ℤ)
        omega
      · rw [rowK_of_neg n hy0]
        have hp2 : |2 * p.2 + 1| = -(2 * p.2 + 1) := abs_of_neg (by omega)
        have hb := abs_nonneg (p.1 : ℤ)
        omega
    obtain ⟨hk1, hk2⟩ := hk
    have hk3 := abs_le.mp hk1
    exact ⟨p.2, hk2, by
      rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_singleton]
      exact ⟨hk3, rfl⟩⟩

lemma rowK_nonneg (n : ℕ) {y : ℤ} (hy : y ∈ Finset.Icc (-(n : ℤ)) ((n : ℤ) - 1)) :
    0 ≤ rowK n y := by
  rw [Finset.mem_Icc] at hy
  show 0 ≤ (if 0 ≤ y then (n : ℤ) - 1 - y else (n : ℤ) + y)
  split_ifs <;> omega

/-- Adjacent points differ by a unit step in exactly one coordinate. -/
lemma adj_cases {p q : ℤ × ℤ} (h : Adj p q) :
    (p.1 = q.1 ∧ (p.2 = q.2 + 1 ∨ p.2 = q.2 - 1)) ∨
      (p.2 = q.2 ∧ (p.1 = q.1 + 1 ∨ p.1 = q.1 - 1)) := by
  unfold Adj at h
  rcases abs_cases (p.1 - q.1) with ⟨h1, h1'⟩ | ⟨h1, h1'⟩ <;>
    rcases abs_cases (p.2 - q.2) with ⟨h2, h2'⟩ | ⟨h2, h2'⟩ <;> omega

/-- Along an edge, `f` changes by `±2`, except for the vertical pairs crossing
the axis `y = -1/2`, where it does not change. -/
lemma f_diff {p q : ℤ × ℤ} (h : Adj p q) :
    |f p - f q| ≤ 2 ∧
      (f p = f q → p.1 = q.1 ∧ ((p.2 = 0 ∧ q.2 = -1) ∨ (p.2 = -1 ∧ q.2 = 0))) := by
  rcases adj_cases h with ⟨hx, hy⟩ | ⟨hy, hx⟩
  · rcases hy with hy | hy
    · -- `p.1 = q.1`, `p.2 = q.2 + 1`
      have hfp : f p = 2 * q.1 + |2 * q.2 + 3| := by
        have e : f p = 2 * p.1 + |2 * p.2 + 1| := rfl
        rw [e, hx, hy]
        congr 1
        congr 1
        ring
      have hfq : f q = 2 * q.1 + |2 * q.2 + 1| := rfl
      refine ⟨?_, fun hfeq ↦ ?_⟩
      · rw [hfp, hfq]
        rcases abs_cases (2 * q.2 + 3) with ⟨h3, h3'⟩ | ⟨h3, h3'⟩ <;>
          rcases abs_cases (2 * q.2 + 1) with ⟨h4, h4'⟩ | ⟨h4, h4'⟩ <;>
          · rw [h3, h4, abs_le]
            omega
      · rw [hfp, hfq] at hfeq
        rcases abs_cases (2 * q.2 + 3) with ⟨h3, h3'⟩ | ⟨h3, h3'⟩ <;>
          rcases abs_cases (2 * q.2 + 1) with ⟨h4, h4'⟩ | ⟨h4, h4'⟩ <;>
          · rw [h3, h4] at hfeq
            rw [hx, hy]
            omega
    · -- `p.1 = q.1`, `p.2 = q.2 - 1`
      have hfp : f p = 2 * q.1 + |2 * q.2 - 1| := by
        have e : f p = 2 * p.1 + |2 * p.2 + 1| := rfl
        rw [e, hx, hy]
        congr 1
        congr 1
        ring
      have hfq : f q = 2 * q.1 + |2 * q.2 + 1| := rfl
      refine ⟨?_, fun hfeq ↦ ?_⟩
      · rw [hfp, hfq]
        rcases abs_cases (2 * q.2 - 1) with ⟨h3, h3'⟩ | ⟨h3, h3'⟩ <;>
          rcases abs_cases (2 * q.2 + 1) with ⟨h4, h4'⟩ | ⟨h4, h4'⟩ <;>
          · rw [h3, h4, abs_le]
            omega
      · rw [hfp, hfq] at hfeq
        rcases abs_cases (2 * q.2 - 1) with ⟨h3, h3'⟩ | ⟨h3, h3'⟩ <;>
          rcases abs_cases (2 * q.2 + 1) with ⟨h4, h4'⟩ | ⟨h4, h4'⟩ <;>
          · rw [h3, h4] at hfeq
            rw [hx, hy]
            omega
  · rcases hx with hx | hx
    · -- `p.2 = q.2`, `p.1 = q.1 + 1`
      have hfp : f p = 2 * q.1 + 2 + |2 * p.2 + 1| := by
        have e : f p = 2 * p.1 + |2 * p.2 + 1| := rfl
        rw [e, hx]
        ring
      have hfq : f q = 2 * q.1 + |2 * q.2 + 1| := rfl
      refine ⟨?_, fun hfeq ↦ ?_⟩
      · rw [hfp, hfq, hy, abs_le]
        omega
      · rw [hfp, hfq, hy] at hfeq
        omega
    · -- `p.2 = q.2`, `p.1 = q.1 - 1`
      have hfp : f p = 2 * q.1 - 2 + |2 * p.2 + 1| := by
        have e : f p = 2 * p.1 + |2 * p.2 + 1| := rfl
        rw [e, hx]
        ring
      have hfq : f q = 2 * q.1 + |2 * q.2 + 1| := rfl
      refine ⟨?_, fun hfeq ↦ ?_⟩
      · rw [hfp, hfq, hy, abs_le]
        omega
      · rw [hfp, hfq, hy] at hfeq
        omega

/-- Two adjacent blue points form a vertical pair crossing the axis. -/
lemma blue_adj {n : ℕ} {p q : ℤ × ℤ} (hadj : Adj p q) (hp : blue n p) (hq : blue n q) :
    p.1 = q.1 ∧ ((p.2 = 0 ∧ q.2 = -1) ∨ (p.2 = -1 ∧ q.2 = 0)) := by
  have hfe : f p = f q := by
    have h1 := (f_diff hadj).1
    have h2 : f p ≡ f q [ZMOD 4] := hp.trans hq.symm
    rw [Int.modEq_iff_dvd] at h2
    rw [abs_le] at h1
    omega
  exact (f_diff hadj).2 hfe

/-! ## Counting: the colour sum over `S n` and the count of blue axial points -/

/-- The symmetric integer interval `[-K, K]` as a map of `range (2K+1)`. -/
lemma Icc_neg_eq_map (K : ℕ) :
    Finset.Icc (-(K : ℤ)) (K : ℤ) =
      (Finset.range (2 * K + 1)).map ⟨fun i : ℕ ↦ (i : ℤ) - (K : ℤ), by
        intro a b h
        dsimp only at h
        omega⟩ := by
  ext x
  simp only [Finset.mem_Icc, Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨h1, h2⟩
    have h0 : (0 : ℤ) ≤ x + (K : ℤ) := by omega
    have h1' := Int.toNat_of_nonneg h0
    exact ⟨(x + (K : ℤ)).toNat, by omega, by omega⟩
  · rintro ⟨i, hi, rfl⟩
    constructor <;> omega

lemma sum_range_neg_one (k : ℕ) : ∑ i ∈ Finset.range (2 * k + 1), (-1 : ℤ) ^ i = 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 2 by ring]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih, pow_succ]
    ring

/-- The `±1` alternating sum over a symmetric interval equals `1` (each row of
`S n` has one more blue point than red points). -/
lemma row_sum (K : ℕ) (c : ℤ) (hc : Even (c - (K : ℤ))) :
    ∑ x ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), (if Even (x + c) then (1 : ℤ) else -1) = 1 := by
  have hpar1 : ∀ i : ℕ, Even ((i : ℤ) - (K : ℤ) + c) ↔ Even (i : ℤ) := by
    intro i
    simp only [even_iff_two_dvd] at hc ⊢
    constructor
    · intro hd
      omega
    · intro hd
      omega
  have hpar2 : ∀ i : ℕ, Even (i : ℤ) ↔ Even i := by
    intro i
    rw [← Int.not_odd_iff_even, Int.odd_coe_nat, Nat.not_odd_iff_even]
  rw [Icc_neg_eq_map, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk]
  rw [Finset.sum_congr rfl (fun i _ ↦ if_congr (hpar1 i |>.trans (hpar2 i)) rfl rfl
    |>.trans (neg_one_pow_eq_ite).symm), sum_range_neg_one]

/-- The colour of `(x, y)` as an explicit parity test. -/
lemma chi_eq (n : ℕ) (x y : ℤ) :
    chi n (x, y) =
      if 0 ≤ y then (if Even (x + y + 1 - (n : ℤ)) then (1 : ℤ) else -1)
        else (if Even (x - y - (n : ℤ)) then (1 : ℤ) else -1) := by
  by_cases hy : 0 ≤ y
  · rw [ite_eq_left hy]
    have hf : f (x, y) = 2 * x + (2 * y + 1) := by
      have e : f (x, y) = 2 * x + |2 * y + 1| := rfl
      rw [e, abs_of_nonneg (by omega : (0 : ℤ) ≤ 2 * y + 1)]
    by_cases hb : blue n (x, y)
    · rw [chi_of_blue hb]
      have hb2 : f (x, y) ≡ 2 * (n : ℤ) - 1 [ZMOD 4] := hb
      rw [hf, Int.modEq_iff_dvd] at hb2
      have hev : Even (x + y + 1 - (n : ℤ)) := by
        rw [even_iff_two_dvd]
        omega
      rw [ite_eq_left hev]
    · rw [chi_of_not_blue hb]
      have hne : ¬ Even (x + y + 1 - (n : ℤ)) := by
        rw [even_iff_two_dvd]
        intro hd
        apply hb
        show f (x, y) ≡ 2 * (n : ℤ) - 1 [ZMOD 4]
        rw [hf, Int.modEq_iff_dvd]
        omega
      rw [ite_eq_right hne]
  · rw [ite_eq_right hy]
    have hf : f (x, y) = 2 * x - (2 * y + 1) := by
      have e : f (x, y) = 2 * x + |2 * y + 1| := rfl
      rw [e, abs_of_neg (by omega : 2 * y + 1 < 0)]
      ring
    by_cases hb : blue n (x, y)
    · rw [chi_of_blue hb]
      have hb2 : f (x, y) ≡ 2 * (n : ℤ) - 1 [ZMOD 4] := hb
      rw [hf, Int.modEq_iff_dvd] at hb2
      have hev : Even (x - y - (n : ℤ)) := by
        rw [even_iff_two_dvd]
        omega
      rw [ite_eq_left hev]
    · rw [chi_of_not_blue hb]
      have hne : ¬ Even (x - y - (n : ℤ)) := by
        rw [even_iff_two_dvd]
        intro hd
        apply hb
        show f (x, y) ≡ 2 * (n : ℤ) - 1 [ZMOD 4]
        rw [hf, Int.modEq_iff_dvd]
        omega
      rw [ite_eq_right hne]

/-- The colour sum over the row at height `y` equals `1`. -/
lemma inner_sum (n : ℕ) (y : ℤ) (hy : y ∈ Finset.Icc (-(n : ℤ)) ((n : ℤ) - 1)) :
    ∑ p ∈ (Finset.Icc (-(rowK n y)) (rowK n y)) ×ˢ {y}, chi n p = 1 := by
  rw [Finset.sum_product]
  simp only [Finset.sum_singleton]
  have hK := rowK_nonneg n hy
  have hKz : ((rowK n y).toNat : ℤ) = rowK n y := Int.toNat_of_nonneg hK
  rw [← hKz]
  by_cases hy0 : 0 ≤ y
  · have hc : Even ((y + 1 - (n : ℤ)) - ((rowK n y).toNat : ℤ)) := by
      rw [hKz, rowK_of_nonneg n hy0]
      exact ⟨y + 1 - (n : ℤ), by ring⟩
    have e : ∀ x ∈ Finset.Icc (-((rowK n y).toNat : ℤ)) ((rowK n y).toNat : ℤ),
        chi n (x, y) = (if Even (x + (y + 1 - (n : ℤ))) then (1 : ℤ) else -1) := by
      intro x hx
      rw [chi_eq, ite_eq_left hy0]
      have he : x + y + 1 - (n : ℤ) = x + (y + 1 - (n : ℤ)) := by ring
      rw [he]
    rw [Finset.sum_congr rfl e]
    exact row_sum _ _ hc
  · have hc : Even ((-y - (n : ℤ)) - ((rowK n y).toNat : ℤ)) := by
      rw [hKz, rowK_of_neg n hy0]
      exact ⟨-y - (n : ℤ), by ring⟩
    have e : ∀ x ∈ Finset.Icc (-((rowK n y).toNat : ℤ)) ((rowK n y).toNat : ℤ),
        chi n (x, y) = (if Even (x + (-y - (n : ℤ))) then (1 : ℤ) else -1) := by
      intro x hx
      rw [chi_eq, ite_eq_right hy0]
      have he : x - y - (n : ℤ) = x + (-y - (n : ℤ)) := by ring
      rw [he]
    rw [Finset.sum_congr rfl e]
    exact row_sum _ _ hc

/-- There are `2n` more blue points than red points in `S n`. -/
lemma sum_chi (n : ℕ) : ∑ p ∈ S n, chi n p = 2 * (n : ℤ) := by
  simp only [S]
  rw [Finset.sum_biUnion (fun y hy z hz hyz ↦ by
    show Disjoint ((Finset.Icc (-(rowK n y)) (rowK n y)) ×ˢ {y})
      ((Finset.Icc (-(rowK n z)) (rowK n z)) ×ˢ {z})
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    simp only [Finset.mem_product, Finset.mem_singleton] at hp1 hp2
    exact hyz (hp1.2.symm.trans hp2.2))]
  rw [Finset.sum_congr rfl (fun y hy ↦ inner_sum n y hy)]
  rw [Finset.sum_const, Int.card_Icc]
  have h1 : ((n : ℤ) - 1 + 1 - (-(n : ℤ))).toNat = 2 * n := by
    rw [show (n : ℤ) - 1 + 1 - (-(n : ℤ)) = ((2 * n : ℕ) : ℤ) by push_cast; ring,
      Int.toNat_natCast]
  rw [h1, nsmul_eq_mul, mul_one]
  norm_cast

/-- Exactly `n` points of `S n` are blue and lie on the axis `y = 0`. -/
lemma card_B0 (n : ℕ) :
    ((S n).filter (fun p ↦ blue n p ∧ p.2 = 0)).card = n := by
  have hf1 : ∀ p : ℤ × ℤ, p.2 = 0 → f p = 2 * p.1 + 1 := by
    intro p hp0
    have e : f p = 2 * p.1 + |2 * p.2 + 1| := rfl
    rw [e, hp0]
    norm_num
  have hset : (S n).filter (fun p ↦ blue n p ∧ p.2 = 0)
      = ((Finset.Icc (-((n : ℤ) - 1)) ((n : ℤ) - 1)).filter
          (fun x ↦ (x + 1 - (n : ℤ)) % 2 = 0)) ×ˢ {0} := by
    ext p
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_singleton, Finset.mem_filter,
      Finset.mem_Icc]
    constructor
    · rintro ⟨hpS, hpb, hp0⟩
      rw [mem_S] at hpS
      have hpa : |2 * p.2 + 1| = 1 := by rw [hp0]; norm_num
      rw [hpa] at hpS
      have hk : |p.1| ≤ (n : ℤ) - 1 := by omega
      have hk' := abs_le.mp hk
      have h2 : f p ≡ 2 * (n : ℤ) - 1 [ZMOD 4] := hpb
      rw [Int.modEq_iff_dvd, hf1 p hp0] at h2
      refine ⟨⟨⟨?_, ?_⟩, ?_⟩, hp0⟩ <;> omega
    · rintro ⟨⟨⟨h1, h2⟩, hmod⟩, hp0⟩
      refine ⟨?_, ?_, hp0⟩
      · rw [mem_S]
        have hpa : |2 * p.2 + 1| = 1 := by rw [hp0]; norm_num
        rw [hpa]
        have hk : |p.1| ≤ (n : ℤ) - 1 := abs_le.mpr ⟨h1, h2⟩
        omega
      · show f p ≡ 2 * (n : ℤ) - 1 [ZMOD 4]
        rw [Int.modEq_iff_dvd, hf1 p hp0]
        omega
  rw [hset, Finset.card_product, Finset.card_singleton, mul_one]
  have hinj : Function.Injective (fun t : ℤ ↦ (n : ℤ) - 1 - 2 * t) := by
    intro a b h
    dsimp only at h
    omega
  have hmap : (Finset.Icc (-((n : ℤ) - 1)) ((n : ℤ) - 1)).filter
        (fun x ↦ (x + 1 - (n : ℤ)) % 2 = 0)
      = (Finset.Icc (0 : ℤ) ((n : ℤ) - 1)).map
          ⟨(fun t : ℤ ↦ (n : ℤ) - 1 - 2 * t), hinj⟩ := by
    ext x
    rw [Finset.mem_filter, Finset.mem_map, Finset.mem_Icc]
    simp only [Function.Embedding.coeFn_mk, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨h1, h2⟩, hmod⟩
      exact ⟨((n : ℤ) - 1 - x) / 2, ⟨by omega, by omega⟩, by omega⟩
    · rintro ⟨t, ⟨ht1, ht2⟩, rfl⟩
      refine ⟨⟨?_, ?_⟩, ?_⟩ <;> omega
  rw [hmap, Finset.card_map, Int.card_Icc]
  rw [show (n : ℤ) - 1 + 1 - 0 = (n : ℤ) by ring, Int.toNat_natCast]

/-! ## The per-path bound -/

/-- Every path's colour sum exceeds its number of blue axial points by at most
one; moreover, if the path has a "good head" (`GH`), the sum is at most the
count itself.  This packages the "cut at blue-blue pairs" argument: each unit
of surplus is charged to a distinct blue point of the axis `y = 0`. -/
lemma path_bound {n : ℕ} (P : List (ℤ × ℤ)) (hchain : P.IsChain Adj) (hnodup : P.Nodup) :
    sig n P ≤ b0 n P + 1 ∧ (GH n P → sig n P ≤ b0 n P) := by
  induction P with
  | nil => exact ⟨by simp [sig_nil, b0_nil], fun _ ↦ by simp [sig_nil, b0_nil]⟩
  | cons p tl ih =>
    rw [List.nodup_cons] at hnodup
    obtain ⟨hpnin, hnodtl⟩ := hnodup
    rw [List.isChain_cons_iff] at hchain
    rcases hchain with htl | ⟨q, rest, hadj, hchaintl, rfl⟩
    · -- `P = [p]`
      subst htl
      clear ih
      by_cases hb : blue n p
      · by_cases h0 : p.2 = 0
        · refine ⟨?_, fun _ ↦ ?_⟩
          · rw [sig_cons, sig_nil, b0_cons, b0_nil, chi_of_blue hb, ite_eq_left ⟨hb, h0⟩]
            norm_num
          · rw [sig_cons, sig_nil, b0_cons, b0_nil, chi_of_blue hb, ite_eq_left ⟨hb, h0⟩]
        · refine ⟨?_, fun hgh ↦ ?_⟩
          · rw [sig_cons, sig_nil, b0_cons, b0_nil, chi_of_blue hb,
              ite_eq_right (fun ⟨_, h'⟩ ↦ h0 h')]
            norm_num
          · simp only [GH] at hgh
            rcases hgh with hcontra | hcontra
            · exact absurd hb hcontra
            · exact absurd hcontra h0
      · refine ⟨?_, fun _ ↦ ?_⟩
        · rw [sig_cons, sig_nil, b0_cons, b0_nil, chi_of_not_blue hb,
            ite_eq_right (fun ⟨h', _⟩ ↦ hb h')]
          norm_num
        · rw [sig_cons, sig_nil, b0_cons, b0_nil, chi_of_not_blue hb,
            ite_eq_right (fun ⟨h', _⟩ ↦ hb h')]
          norm_num
    · -- `P = p :: q :: rest`
      obtain ⟨ihA, ihB⟩ := ih hchaintl hnodtl
      by_cases hb : blue n p
      · by_cases h0 : p.2 = 0
        · -- `p ∈ B₀`
          refine ⟨?_, fun hgh ↦ ?_⟩
          · rw [sig_cons, b0_cons, chi_of_blue hb, ite_eq_left ⟨hb, h0⟩]
            linarith [ihA]
          · have hnq : ¬ blue n q := by
              have h : GH n (p :: q :: rest) := hgh
              simp only [GH] at h
              rcases h with hcontra | ⟨_, h'⟩
              · exact absurd hb hcontra
              · exact h'
            have ghq : GH n (q :: rest) := by
              cases rest with
              | nil => simp only [GH]; exact Or.inl hnq
              | cons r rest2 => simp only [GH]; exact Or.inl hnq
            rw [sig_cons, b0_cons, chi_of_blue hb, ite_eq_left ⟨hb, h0⟩]
            linarith [ihB ghq]
        · -- `p` blue, `p.2 ≠ 0`
          have hnp0 : ¬ (blue n p ∧ p.2 = 0) := fun ⟨_, h'⟩ ↦ h0 h'
          refine ⟨?_, fun hgh ↦ ?_⟩
          · have ghq : GH n (q :: rest) := by
              by_cases hbq : blue n q
              · -- blue-blue pair, must cross the axis
                obtain ⟨hx1, hy⟩ := blue_adj hadj hb hbq
                have hp2 : p.2 = -1 ∧ q.2 = 0 := by
                  rcases hy with ⟨h1, h2⟩ | ⟨h1, h2⟩
                  · exact absurd h1 h0
                  · exact ⟨h1, h2⟩
                cases rest with
                | nil => simp only [GH]; exact Or.inr hp2.2
                | cons r rest2 =>
                  have hnr : ¬ blue n r := by
                    intro hbr
                    obtain ⟨hadjqr, -⟩ := List.isChain_cons_cons.mp hchaintl
                    obtain ⟨hx2, hy2⟩ := blue_adj hadjqr hbq hbr
                    have hr2 : r.2 = -1 := by
                      rcases hy2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
                      · exact h2
                      · omega
                    have hr_eq : r = p :=
                      Prod.ext (hx2.symm.trans hx1.symm) (hr2.trans hp2.1.symm)
                    subst hr_eq
                    exact hpnin (by simp)
                  simp only [GH]
                  exact Or.inr ⟨hp2.2, hnr⟩
              · cases rest with
                | nil => simp only [GH]; exact Or.inl hbq
                | cons r rest2 => simp only [GH]; exact Or.inl hbq
            rw [sig_cons, b0_cons, chi_of_blue hb, ite_eq_right hnp0]
            linarith [ihB ghq]
          · have h : GH n (p :: q :: rest) := hgh
            simp only [GH] at h
            rcases h with hcontra | ⟨h1, -⟩
            · exact absurd hb hcontra
            · exact absurd h1 h0
      · -- `p` red
        have hnb : ¬ (blue n p ∧ p.2 = 0) := fun ⟨h', _⟩ ↦ hb h'
        refine ⟨?_, fun _ ↦ ?_⟩
        · rw [sig_cons, b0_cons, chi_of_not_blue hb, ite_eq_right hnb]
          linarith [ihA]
        · rw [sig_cons, b0_cons, chi_of_not_blue hb, ite_eq_right hnb]
          linarith [ihA]

/-! ## List/Finset bridges -/

lemma sum_map_flatten (L : List (List (ℤ × ℤ))) (g : ℤ × ℤ → ℤ) :
    (L.map (fun P ↦ (P.map g).sum)).sum = (L.flatten.map g).sum := by
  induction L with
  | nil => simp
  | cons Q qs ih =>
    simp only [List.map_cons, List.sum_cons, List.flatten_cons, List.map_append,
      List.sum_append, ih]

lemma sum_b0_flatten (L : List (List (ℤ × ℤ))) (pred : ℤ × ℤ → Bool) :
    (L.map (fun P ↦ ((P.filter pred).length : ℤ))).sum
      = ((L.flatten.filter pred).length : ℤ) := by
  induction L with
  | nil => simp
  | cons Q qs ih =>
    simp only [List.map_cons, List.sum_cons, List.flatten_cons, List.filter_append,
      List.length_append, ih]
    push_cast
    ring

lemma map_sum_add_one (l : List (List (ℤ × ℤ))) (g : List (ℤ × ℤ) → ℤ) :
    (l.map (fun P ↦ g P + 1)).sum = (l.map g).sum + (l.length : ℤ) := by
  induction l with
  | nil => simp
  | cons Q qs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
    push_cast
    ring

snip end

/-- USAMO 2008, Problem 3: any partition of `Sₙ` into paths uses at least
`n` paths.  We model a partition as a list of lists of points: each list is a
path (its points are distinct, lie in `S n`, and consecutive points are
adjacent), the lists are pairwise disjoint, and together they cover `S n`. -/
problem usa2008_p3 (n : ℕ) (_hn : 0 < n) (paths : List (List (ℤ × ℤ)))
    (hmem : ∀ P ∈ paths, ∀ p ∈ P, p ∈ S n)
    (hnodup : ∀ P ∈ paths, P.Nodup)
    (hchain : ∀ P ∈ paths, P.IsChain Adj)
    (hdisj : paths.Pairwise List.Disjoint)
    (hcover : ∀ p ∈ S n, ∃ P ∈ paths, p ∈ P) :
    n ≤ paths.length := by
  have hjoinN : paths.flatten.Nodup := List.nodup_flatten.mpr ⟨hnodup, hdisj⟩
  have hjoin : paths.flatten.toFinset = S n := by
    ext p
    simp only [List.mem_toFinset, List.mem_flatten]
    exact ⟨fun ⟨P, hP, hp⟩ ↦ hmem P hP p hp, fun hp ↦ hcover p hp⟩
  -- the total colour sum over all paths equals `2n`
  have hsig : (paths.map (sig n)).sum = 2 * (n : ℤ) := by
    have h1 : (paths.map (sig n)).sum = (paths.flatten.map (chi n)).sum := by
      show (paths.map (fun P ↦ (P.map (chi n)).sum)).sum = _
      exact sum_map_flatten paths (chi n)
    rw [h1, ← List.sum_toFinset (chi n) hjoinN, hjoin, sum_chi]
  -- the total number of blue axial points over all paths equals `n`
  have hb0 : (paths.map (b0 n)).sum = (((S n).filter (fun p ↦ blue n p ∧ p.2 = 0)).card : ℤ) := by
    have hN1 : (paths.flatten.filter (fun p ↦ decide (blue n p ∧ p.2 = 0))).Nodup :=
      List.Nodup.filter _ hjoinN
    have htf : (paths.flatten.filter (fun p ↦ decide (blue n p ∧ p.2 = 0))).toFinset
        = (S n).filter (fun p ↦ blue n p ∧ p.2 = 0) := by
      rw [List.toFinset_filter, hjoin]
      ext p
      simp [decide_eq_true_eq]
    have h1 : (paths.map (b0 n)).sum
        = ((paths.flatten.filter (fun p ↦ decide (blue n p ∧ p.2 = 0))).length : ℤ) := by
      show (paths.map (fun P ↦ ((P.filter (fun p ↦ decide (blue n p ∧ p.2 = 0))).length : ℤ))).sum = _
      exact sum_b0_flatten paths _
    rw [h1, show (paths.flatten.filter (fun p ↦ decide (blue n p ∧ p.2 = 0))).length
        = (paths.flatten.filter (fun p ↦ decide (blue n p ∧ p.2 = 0))).toFinset.card from
      (List.toFinset_card_of_nodup hN1).symm, htf]
  -- the per-path bound, summed
  have hle : (paths.map (sig n)).sum ≤ (paths.map (fun P ↦ b0 n P + 1)).sum :=
    List.sum_le_sum (fun P hP ↦ (path_bound P (hchain P hP) (hnodup P hP)).1)
  rw [hsig, map_sum_add_one paths (b0 n), hb0, card_B0] at hle
  -- `2n ≤ n + m`, hence `n ≤ m`
  have hfin : (n : ℤ) ≤ (paths.length : ℤ) := by linarith
  exact_mod_cast hfin

end Usa2008P3
