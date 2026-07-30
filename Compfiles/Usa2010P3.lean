/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Star.Real
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Algebra] }

/-!
# USA Mathematical Olympiad 2010, Problem 3

The 2010 positive real numbers $a_1, a_2, \ldots, a_{2010}$ satisfy the inequality
$a_i a_j \le i + j$ for all $1 \le i < j \le 2010$. Determine, with proof, the largest
possible value of the product $a_1 a_2 \cdots a_{2010}$.
-/

namespace Usa2010P3

snip begin

/-!
We follow the proof sketched in Evan Chen's *USAMO 2010 Solution Notes*
(https://web.evanchen.cc/exams/USAMO-2010-notes.pdf).

*Upper bound*: pairing the factors as $(a_1 a_2)(a_3 a_4)\cdots(a_{2009} a_{2010})$
and applying $a_i a_j \le i + j$ to each pair gives
$a_1 a_2 \cdots a_{2010} \le 3 \cdot 7 \cdot 11 \cdots 4019$.

*Construction* (zero-based indexing): take $a_{2k} = \dfrac{4k+3}{2\sqrt{k+1}}$ and
$a_{2k+1} = 2\sqrt{k+1}$. Then $a_{2k} a_{2k+1} = 4k+3$, so the product attains the
bound. The inequality $a_i a_j \le (i+1) + (j+1)$ is verified by a case analysis on
the parities of $i$ and $j$; each case reduces, after squaring, to an elementary
polynomial inequality (`key₁`, `key₂`, `key₃`, `key₄` below).
-/

/-- Split a product over `Finset.range (2 * n)` into a product of consecutive pairs. -/
lemma prod_range_pair (f : ℕ → ℝ) (n : ℕ) :
    ∏ i ∈ Finset.range (2 * n), f i = ∏ k ∈ Finset.range n, f (2 * k) * f (2 * k + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : 2 * (n + 1) = 2 * n + 1 + 1 := by ring
    rw [e, Finset.prod_range_succ, Finset.prod_range_succ, ih, Finset.prod_range_succ,
      mul_assoc]

/-- For `0 ≤ C` and `0 ≤ Z`: `C * √Z = √(C² * Z)`. -/
lemma mul_sqrt_eq_sqrt_mul {C Z : ℝ} (hC : 0 ≤ C) (_hZ : 0 ≤ Z) :
    C * Real.sqrt Z = Real.sqrt (C ^ 2 * Z) := by
  conv_lhs => rw [← Real.sqrt_sq hC]
  rw [← Real.sqrt_mul (sq_nonneg C)]

/-- Key inequality for the "even index, odd index" case: the difference factors as
`(q - p) * (4 * (p + 1) * (q + 1) - (2 * p + 1) ^ 2)`, which is nonnegative for
`0 ≤ p ≤ q`. -/
lemma key₁ {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) :
    (4 * p + 3) ^ 2 * (q + 1) ≤ (2 * p + 2 * q + 3) ^ 2 * (p + 1) := by
  have h1 : (2 * p + 2 * q + 3) ^ 2 * (p + 1) - (4 * p + 3) ^ 2 * (q + 1)
      = (q - p) * (4 * (p + 1) * (q + 1) - (2 * p + 1) ^ 2) := by ring
  have h2 : 0 ≤ 4 * (p + 1) * (q + 1) - (2 * p + 1) ^ 2 := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ p + 1) (by linarith : (0:ℝ) ≤ q - p), hp]
  have h3 : 0 ≤ (q - p) * (4 * (p + 1) * (q + 1) - (2 * p + 1) ^ 2) :=
    mul_nonneg (by linarith) h2
  linarith [h1, h3]

/-- Key inequality for the "odd index, even index" case: the difference factors as
`(p - q) * (4 * (p + 1) * (q + 1) - (2 * q + 1) ^ 2)`, a product of two nonpositive
factors for `0 ≤ p` and `p + 1 ≤ q`. -/
lemma key₂ {p q : ℝ} (hp : 0 ≤ p) (hpq : p + 1 ≤ q) :
    (4 * q + 3) ^ 2 * (p + 1) ≤ (2 * p + 2 * q + 3) ^ 2 * (q + 1) := by
  have h1 : (2 * p + 2 * q + 3) ^ 2 * (q + 1) - (4 * q + 3) ^ 2 * (p + 1)
      = (p - q) * (4 * (p + 1) * (q + 1) - (2 * q + 1) ^ 2) := by ring
  have h2 : 4 * (p + 1) * (q + 1) - (2 * q + 1) ^ 2 ≤ -1 := by
    nlinarith [mul_le_mul_of_nonneg_left hpq (by linarith : (0:ℝ) ≤ q + 1)]
  have h3 : 0 ≤ (p - q) * (4 * (p + 1) * (q + 1) - (2 * q + 1) ^ 2) :=
    mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
  linarith [h1, h3]

/-- Key inequality for the "even index, even index" case. Writing `q = p + 1 + t`
with `0 ≤ t`, the difference expands to a polynomial in `p` and `t` all of whose
coefficients are positive. -/
lemma key₃ {p q : ℝ} (hp : 0 ≤ p) (hpq : p + 1 ≤ q) :
    (4 * p + 3) ^ 2 * (4 * q + 3) ^ 2
      ≤ 64 * (p + q + 1) ^ 2 * (p + 1) * (q + 1) := by
  obtain ⟨t, ht, rfl⟩ : ∃ t : ℝ, 0 ≤ t ∧ q = p + 1 + t := ⟨q - p - 1, by linarith, by ring⟩
  have key : 64 * (p + (p + 1 + t) + 1) ^ 2 * (p + 1) * ((p + 1 + t) + 1)
      - (4 * p + 3) ^ 2 * (4 * (p + 1 + t) + 3) ^ 2
      = (64 * p + 64) * t ^ 3 + (64 * p ^ 2 + 320 * p + 240) * t ^ 2
        + (128 * p ^ 2 + 416 * p + 264) * t + (32 * p ^ 2 + 112 * p + 71) := by ring
  have h : 0 ≤ 64 * (p + (p + 1 + t) + 1) ^ 2 * (p + 1) * ((p + 1 + t) + 1)
      - (4 * p + 3) ^ 2 * (4 * (p + 1 + t) + 3) ^ 2 := by
    rw [key]; positivity
  linarith [h]

/-- Key inequality for the "odd index, odd index" case (AM–GM). -/
lemma key₄ {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (2 * Real.sqrt x) * (2 * Real.sqrt y) ≤ 2 * x + 2 * y := by
  nlinarith [sq_nonneg (Real.sqrt x - Real.sqrt y), Real.sq_sqrt hx, Real.sq_sqrt hy,
    mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)]

/-- The extremal sequence (zero-based): at index `2k` the value is
`(4k+3) / (2 * √(k+1))`, and at index `2k+1` it is `2 * √(k+1)`. -/
noncomputable def constr (i : ℕ) : ℝ :=
  if Even i then (4 * ((i / 2 : ℕ) : ℝ) + 3) / (2 * Real.sqrt (((i / 2 : ℕ) : ℝ) + 1))
  else 2 * Real.sqrt (((i / 2 : ℕ) : ℝ) + 1)

lemma constr_even (k : ℕ) :
    constr (2 * k) = (4 * (k : ℝ) + 3) / (2 * Real.sqrt ((k : ℝ) + 1)) := by
  have h1 : Even (2 * k) := ⟨k, two_mul k⟩
  have h2 : (2 * k) / 2 = k := by omega
  simp only [constr, if_pos h1, h2]

lemma constr_odd (k : ℕ) :
    constr (2 * k + 1) = 2 * Real.sqrt ((k : ℝ) + 1) := by
  have h1 : ¬ Even (2 * k + 1) := Nat.not_even_iff_odd.mpr ⟨k, rfl⟩
  have h2 : (2 * k + 1) / 2 = k := by omega
  simp only [constr, if_neg h1, h2]

lemma constr_pos (i : ℕ) : 0 < constr i := by
  by_cases h : Even i
  · simp only [constr, if_pos h]
    positivity
  · simp only [constr, if_neg h]
    positivity

/-- The product of two consecutive terms is exactly `4k + 3`. -/
lemma constr_pair (k : ℕ) : constr (2 * k) * constr (2 * k + 1) = 4 * (k : ℝ) + 3 := by
  rw [constr_even, constr_odd,
    div_mul_cancel₀ _ (ne_of_gt (by positivity : (0:ℝ) < 2 * Real.sqrt ((k : ℝ) + 1)))]

/-- Validity of the construction: case both indices even. -/
lemma ineq_ee {p q : ℝ} (hp : 0 ≤ p) (hpq : p + 1 ≤ q) :
    (4 * p + 3) / (2 * Real.sqrt (p + 1)) * ((4 * q + 3) / (2 * Real.sqrt (q + 1)))
      ≤ (2 * p + 1) + (2 * q + 1) := by
  have hq : 0 ≤ q := by linarith
  have hd : (0:ℝ) < 2 * Real.sqrt (p + 1) * (2 * Real.sqrt (q + 1)) := by positivity
  have e1 : (2 * Real.sqrt (p + 1)) * (2 * Real.sqrt (q + 1))
      = 4 * Real.sqrt ((p + 1) * (q + 1)) := by
    rw [Real.sqrt_mul (by positivity : (0:ℝ) ≤ p + 1)]; ring
  have e2 := mul_sqrt_eq_sqrt_mul (C := ((2 * p + 1) + (2 * q + 1)) * 4)
    (Z := (p + 1) * (q + 1)) (by positivity) (by positivity)
  rw [div_mul_div_comm, div_le_iff₀ hd, e1, ← mul_assoc, e2]
  refine (Real.le_sqrt (by positivity) (by positivity)).mpr ?_
  nlinarith [key₃ hp hpq]

/-- Validity of the construction: case even index, odd index. -/
lemma ineq_eo {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) :
    (4 * p + 3) / (2 * Real.sqrt (p + 1)) * (2 * Real.sqrt (q + 1))
      ≤ (2 * p + 1) + (2 * q + 2) := by
  have hq : 0 ≤ q := by linarith
  have hd : (0:ℝ) < 2 * Real.sqrt (p + 1) := by positivity
  have e1 : (4 * p + 3) * (2 * Real.sqrt (q + 1))
      = ((4 * p + 3) * 2) * Real.sqrt (q + 1) := by ring
  have e2 := mul_sqrt_eq_sqrt_mul (C := (4 * p + 3) * 2) (Z := q + 1)
    (by positivity) (by positivity)
  have e3 : (2 * p + 1 + (2 * q + 2)) * (2 * Real.sqrt (p + 1))
      = ((2 * p + 1 + (2 * q + 2)) * 2) * Real.sqrt (p + 1) := by ring
  have e4 := mul_sqrt_eq_sqrt_mul (C := (2 * p + 1 + (2 * q + 2)) * 2) (Z := p + 1)
    (by positivity) (by positivity)
  rw [div_mul_eq_mul_div, div_le_iff₀ hd, e1, e2, e3, e4]
  refine (Real.sqrt_le_sqrt_iff (by positivity)).mpr ?_
  nlinarith [key₁ hp hpq]

/-- Validity of the construction: case odd index, even index. -/
lemma ineq_oe {p q : ℝ} (hp : 0 ≤ p) (hpq : p + 1 ≤ q) :
    (2 * Real.sqrt (p + 1)) * ((4 * q + 3) / (2 * Real.sqrt (q + 1)))
      ≤ (2 * p + 2) + (2 * q + 1) := by
  have hq : 0 ≤ q := by linarith
  have hd : (0:ℝ) < 2 * Real.sqrt (q + 1) := by positivity
  have e1 : (2 * Real.sqrt (p + 1)) * (4 * q + 3)
      = ((4 * q + 3) * 2) * Real.sqrt (p + 1) := by ring
  have e2 := mul_sqrt_eq_sqrt_mul (C := (4 * q + 3) * 2) (Z := p + 1)
    (by positivity) (by positivity)
  have e3 : (2 * p + 2 + (2 * q + 1)) * (2 * Real.sqrt (q + 1))
      = ((2 * p + 2 + (2 * q + 1)) * 2) * Real.sqrt (q + 1) := by ring
  have e4 := mul_sqrt_eq_sqrt_mul (C := (2 * p + 2 + (2 * q + 1)) * 2) (Z := q + 1)
    (by positivity) (by positivity)
  rw [mul_div_assoc', div_le_iff₀ hd, e1, e2, e3, e4]
  refine (Real.sqrt_le_sqrt_iff (by positivity)).mpr ?_
  nlinarith [key₂ hp hpq]

/-- Validity of the construction: case both indices odd. -/
lemma ineq_oo {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    (2 * Real.sqrt (p + 1)) * (2 * Real.sqrt (q + 1)) ≤ (2 * p + 2) + (2 * q + 2) := by
  have h := key₄ (show (0:ℝ) ≤ p + 1 by positivity) (show (0:ℝ) ≤ q + 1 by positivity)
  linarith [h]

/-- The construction satisfies `aᵢaⱼ ≤ (i+1) + (j+1)` for all `i < j`. -/
lemma constr_ineq {i j : ℕ} (hij : i < j) :
    constr i * constr j ≤ (i : ℝ) + 1 + ((j : ℝ) + 1) := by
  obtain ⟨p, rfl | rfl⟩ : ∃ p, i = 2 * p ∨ i = 2 * p + 1 := ⟨i / 2, by omega⟩
  · obtain ⟨q, rfl | rfl⟩ : ∃ q, j = 2 * q ∨ j = 2 * q + 1 := ⟨j / 2, by omega⟩
    · have hpq : p + 1 ≤ q := by omega
      rw [constr_even, constr_even]
      push_cast
      have h := ineq_ee (p := (p : ℝ)) (q := (q : ℝ)) (Nat.cast_nonneg p)
        (by exact_mod_cast hpq)
      linarith [h]
    · have hpq : p ≤ q := by omega
      rw [constr_even, constr_odd]
      push_cast
      have h := ineq_eo (p := (p : ℝ)) (q := (q : ℝ)) (Nat.cast_nonneg p)
        (by exact_mod_cast hpq)
      linarith [h]
  · obtain ⟨q, rfl | rfl⟩ : ∃ q, j = 2 * q ∨ j = 2 * q + 1 := ⟨j / 2, by omega⟩
    · have hpq : p + 1 ≤ q := by omega
      rw [constr_odd, constr_even]
      push_cast
      have h := ineq_oe (p := (p : ℝ)) (q := (q : ℝ)) (Nat.cast_nonneg p)
        (by exact_mod_cast hpq)
      linarith [h]
    · rw [constr_odd, constr_odd]
      push_cast
      have h := ineq_oo (Nat.cast_nonneg p) (Nat.cast_nonneg q)
      linarith [h]

snip end

/-- The answer: `3 * 7 * 11 * ⋯ * 4019`. -/
determine answer : ℝ := ∏ k ∈ Finset.range 1005, (4 * k + 3)

problem usa2010_p3 :
    IsGreatest {x : ℝ | ∃ a : ℕ → ℝ,
      (∀ i, i < 2010 → 0 < a i) ∧
      (∀ i j : ℕ, i < j → j < 2010 → a i * a j ≤ (i : ℝ) + 1 + ((j : ℝ) + 1)) ∧
      x = ∏ i ∈ Finset.range 2010, a i} answer := by
  constructor
  · refine ⟨constr, fun i _ ↦ constr_pos i, fun i j hij _ ↦ constr_ineq hij, ?_⟩
    rw [show (2010 : ℕ) = 2 * 1005 from by norm_num, prod_range_pair constr 1005]
    show (∏ k ∈ Finset.range 1005, (4 * (k : ℝ) + 3))
      = ∏ k ∈ Finset.range 1005, constr (2 * k) * constr (2 * k + 1)
    exact Finset.prod_congr rfl fun k _ ↦ (constr_pair k).symm
  · intro y hy
    obtain ⟨a, hpos, hineq, heq⟩ := hy
    rw [heq]
    rw [show (2010 : ℕ) = 2 * 1005 from by norm_num, prod_range_pair a 1005]
    show (∏ k ∈ Finset.range 1005, a (2 * k) * a (2 * k + 1))
      ≤ ∏ k ∈ Finset.range 1005, (4 * (k : ℝ) + 3)
    refine Finset.prod_le_prod (fun k hk ↦ ?_) (fun k hk ↦ ?_)
    · have hk' := Finset.mem_range.mp hk
      exact mul_nonneg (hpos _ (by omega)).le (hpos _ (by omega)).le
    · have hk' := Finset.mem_range.mp hk
      have h := hineq (2 * k) (2 * k + 1) (by omega) (by omega)
      push_cast at h
      linarith [h]

end Usa2010P3
