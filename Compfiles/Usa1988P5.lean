/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.Data.Rat.Star
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Algebra] }

/-!
# USA Mathematical Olympiad 1988, Problem 5

Let p(x) be the polynomial (1 - x)ᵃ (1 - x²)ᵇ (1 - x³)ᶜ ... (1 - x³²)ᵏ,
where a, b, ..., k are integers. When expanded in powers of x, the coefficient
of x¹ is -2 and the coefficients of x², x³, ... , x³² are all zero. Find k.
-/

namespace Usa1988P5

open Polynomial

/-- The polynomial `p(x) = ∏_{i = 1}^{32} (1 - X^i) ^ (a i)`. The exponent
`a 32` of the last factor is the `k` of the problem. (We take the exponents
to be natural numbers; the coefficient conditions force every exponent to be
positive anyway.) -/
noncomputable def prodForm (a : ℕ → ℕ) : ℚ[X] := ∏ i ∈ Finset.Icc 1 32, (1 - X ^ i) ^ a i

snip begin

/-- The effect of one doubling step `p(x) ↦ p(x) p(-x)` on the exponents:
if `p = ∏ (1 - X^i) ^ (a i)` then `p(x) p(-x) = q(x²)` where
`q = ∏ (1 - X^i) ^ (nextA a i)`. -/
def nextA (a : ℕ → ℕ) (j : ℕ) : ℕ := (if Odd j then a j else 0) + 2 * a (2 * j)

/-- `Good p c m` expresses `p = 1 + c * X + O(X^(m+1))`. -/
def Good (p : ℚ[X]) (c : ℚ) (m : ℕ) : Prop :=
  p.coeff 0 = 1 ∧ p.coeff 1 = c ∧ ∀ k, 2 ≤ k → k ≤ m → p.coeff k = 0

lemma coeff_comp_neg_X (p : ℚ[X]) (n : ℕ) :
    (p.comp (-X)).coeff n = (-1) ^ n * p.coeff n := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [add_comp, coeff_add, coeff_add, hp, hq, mul_add]
  | monomial k a =>
      rw [← C_mul_X_pow_eq_monomial, mul_comp, C_comp, pow_comp, X_comp]
      have e : ((-X : ℚ[X]) ^ k) = C ((-1 : ℚ) ^ k) * X ^ k := by
        rw [show (-X : ℚ[X]) = -1 * X by simp, mul_pow]
        congr 1
        simp
      rw [e, ← mul_assoc, ← map_mul, coeff_C_mul_X_pow, coeff_C_mul_X_pow]
      by_cases h : k = n
      · subst h
        rw [if_pos rfl, if_pos rfl, mul_comm]
      · rw [if_neg (fun e => h e.symm), if_neg (fun e => h e.symm), mul_zero]

lemma coeff_comp_X_sq (q : ℚ[X]) (j : ℕ) :
    (q.comp (X ^ 2)).coeff (2 * j) = q.coeff j := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => rw [add_comp, coeff_add, coeff_add, hp, hq]
  | monomial k a =>
      rw [← C_mul_X_pow_eq_monomial, mul_comp, C_comp, pow_comp, X_comp, ← pow_mul,
        coeff_C_mul_X_pow, coeff_C_mul_X_pow]
      by_cases h : k = j
      · subst h
        rw [if_pos rfl, if_pos rfl]
      · have h2 : ¬ 2 * k = 2 * j := by omega
        rw [if_neg (fun e => h2 e.symm), if_neg (fun e => h e.symm)]

/-- Binomial expansion of the coefficients of `(1 - X^n)^a`. -/
lemma coeff_one_sub_pow (n a k : ℕ) :
    ((1 - X ^ n) ^ a : ℚ[X]).coeff k =
      ∑ j ∈ Finset.range (a + 1),
        if j * n = k then (-1 : ℚ) ^ j * (a.choose j : ℚ) else 0 := by
  rw [sub_eq_add_neg, add_comm (1 : ℚ[X]) (-(X ^ n)), add_pow, finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro j _
  have e2 : (-(X ^ n) : ℚ[X]) ^ j = C ((-1 : ℚ) ^ j) * X ^ (j * n) := by
    rw [show (-(X ^ n) : ℚ[X]) = -1 * X ^ n by simp, mul_pow, ← pow_mul,
      mul_comm n j]
    congr 1
    simp
  rw [one_pow, mul_one, mul_comm _ ((a.choose j : ℚ[X])), e2, ← mul_assoc,
    show ((a.choose j : ℚ[X])) = C ((a.choose j : ℚ)) by simp, ← map_mul,
    coeff_C_mul_X_pow]
  by_cases h : k = j * n
  · rw [if_pos h, if_pos h.symm, mul_comm]
  · rw [if_neg h, if_neg (fun e => h e.symm)]

lemma coeff_zero_factor {n a : ℕ} (hn : 1 ≤ n) :
    ((1 - X ^ n) ^ a : ℚ[X]).coeff 0 = 1 := by
  rw [coeff_zero_eq_eval_zero, eval_pow, eval_sub, eval_one, eval_pow, eval_X,
    zero_pow (by omega : n ≠ 0)]
  simp

lemma coeff_one_factor {n a : ℕ} (hn : 2 ≤ n) :
    ((1 - X ^ n) ^ a : ℚ[X]).coeff 1 = 0 := by
  rw [coeff_one_sub_pow]
  apply Finset.sum_eq_zero
  intro j _
  by_cases h : j * n = 1
  · exfalso
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp at h
    · have := Nat.mul_le_mul hj hn
      omega
  · rw [if_neg h]

lemma coeff_two_factor {n a : ℕ} (hn : 3 ≤ n) :
    ((1 - X ^ n) ^ a : ℚ[X]).coeff 2 = 0 := by
  rw [coeff_one_sub_pow]
  apply Finset.sum_eq_zero
  intro j _
  by_cases h : j * n = 2
  · exfalso
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp at h
    · have := Nat.mul_le_mul hj hn
      omega
  · rw [if_neg h]

lemma coeff_zero_one_sub_X (a : ℕ) : ((1 - X) ^ a : ℚ[X]).coeff 0 = 1 := by
  rw [show (1 - X : ℚ[X]) = 1 - X ^ (1:ℕ) by simp]
  exact coeff_zero_factor (le_refl 1)

lemma coeff_one_one_sub_X (a : ℕ) : ((1 - X) ^ a : ℚ[X]).coeff 1 = -(a : ℚ) := by
  rw [show (1 - X : ℚ[X]) = 1 - X ^ (1:ℕ) by simp, coeff_one_sub_pow 1 a 1]
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp
  · rw [Finset.sum_eq_single 1]
    · rw [if_pos rfl, pow_one, Nat.choose_one_right, neg_one_mul]
    · intro j _ hj1
      rw [if_neg (by rw [mul_one]; exact hj1)]
    · intro h
      rw [Finset.mem_range] at h
      omega

lemma coeff_two_one_sub_X (a : ℕ) :
    ((1 - X) ^ a : ℚ[X]).coeff 2 = (a.choose 2 : ℚ) := by
  rw [show (1 - X : ℚ[X]) = 1 - X ^ (1:ℕ) by simp, coeff_one_sub_pow 1 a 2]
  by_cases ha : 2 ≤ a
  · rw [Finset.sum_eq_single 2]
    · rw [if_pos rfl, Even.neg_one_pow even_two, one_mul]
    · intro j _ hj2
      rw [if_neg (by rw [mul_one]; exact hj2)]
    · intro h
      rw [Finset.mem_range] at h
      omega
  · rw [Nat.choose_eq_zero_of_lt (show a < 2 by omega), Nat.cast_zero]
    apply Finset.sum_eq_zero
    intro j hj
    rw [Finset.mem_range] at hj
    rw [if_neg (by rw [mul_one]; omega)]

lemma coeff_two_one_sub_X_sq (a : ℕ) :
    ((1 - X ^ 2) ^ a : ℚ[X]).coeff 2 = -(a : ℚ) := by
  rw [coeff_one_sub_pow 2 a 2]
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp
  · rw [Finset.sum_eq_single 1]
    · rw [if_pos rfl, pow_one, Nat.choose_one_right, neg_one_mul]
    · intro j _ hj1
      rw [if_neg (by omega : ¬ j * 2 = 2)]
    · intro h
      rw [Finset.mem_range] at h
      omega

lemma coeff_mul_zero (f g : ℚ[X]) :
    (f * g).coeff 0 = f.coeff 0 * g.coeff 0 := by
  rw [coeff_mul]
  have e : Finset.HasAntidiagonal.antidiagonal 0 = {(0, 0)} := by decide
  rw [e, Finset.sum_singleton]

lemma coeff_mul_one (f g : ℚ[X]) :
    (f * g).coeff 1 = f.coeff 0 * g.coeff 1 + f.coeff 1 * g.coeff 0 := by
  rw [coeff_mul]
  have e : Finset.HasAntidiagonal.antidiagonal 1 = {(0, 1), (1, 0)} := by decide
  rw [e, Finset.sum_insert (by decide), Finset.sum_singleton]

lemma coeff_mul_two (f g : ℚ[X]) :
    (f * g).coeff 2 =
      f.coeff 0 * g.coeff 2 + f.coeff 1 * g.coeff 1 + f.coeff 2 * g.coeff 0 := by
  rw [coeff_mul]
  have e : Finset.HasAntidiagonal.antidiagonal 2 = {(0, 2), (1, 1), (2, 0)} := by decide
  rw [e, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  rw [add_assoc]

lemma coeff_zero_prod (s : Finset ℕ) (f : ℕ → ℚ[X])
    (h : ∀ i ∈ s, (f i).coeff 0 = 1) :
    (∏ i ∈ s, f i).coeff 0 = 1 := by
  rw [coeff_zero_eq_eval_zero, eval_prod]
  apply Finset.prod_eq_one
  intro i hi
  rw [← coeff_zero_eq_eval_zero]
  exact h i hi

lemma coeff_one_prod (s : Finset ℕ) (f : ℕ → ℚ[X])
    (h0 : ∀ i ∈ s, (f i).coeff 0 = 1) (h1 : ∀ i ∈ s, (f i).coeff 1 = 0) :
    (∏ i ∈ s, f i).coeff 1 = 0 := by
  revert h0 h1
  induction s using Finset.induction with
  | empty =>
      intro _ _
      simp [Polynomial.coeff_one]
  | insert a s ha ih =>
      intro h0 h1
      have h0' : ∀ i ∈ s, (f i).coeff 0 = 1 :=
        fun i hi => h0 i (Finset.mem_insert_of_mem hi)
      have h1' : ∀ i ∈ s, (f i).coeff 1 = 0 :=
        fun i hi => h1 i (Finset.mem_insert_of_mem hi)
      rw [Finset.prod_insert ha, coeff_mul_one, ih h0' h1', coeff_zero_prod s f h0',
        h0 a (Finset.mem_insert_self a s), h1 a (Finset.mem_insert_self a s)]
      simp

lemma coeff_two_prod (s : Finset ℕ) (f : ℕ → ℚ[X])
    (h0 : ∀ i ∈ s, (f i).coeff 0 = 1) (h1 : ∀ i ∈ s, (f i).coeff 1 = 0)
    (h2 : ∀ i ∈ s, (f i).coeff 2 = 0) :
    (∏ i ∈ s, f i).coeff 2 = 0 := by
  revert h0 h1 h2
  induction s using Finset.induction with
  | empty =>
      intro _ _ _
      simp [Polynomial.coeff_one]
  | insert a s ha ih =>
      intro h0 h1 h2
      have h0' : ∀ i ∈ s, (f i).coeff 0 = 1 :=
        fun i hi => h0 i (Finset.mem_insert_of_mem hi)
      have h1' : ∀ i ∈ s, (f i).coeff 1 = 0 :=
        fun i hi => h1 i (Finset.mem_insert_of_mem hi)
      have h2' : ∀ i ∈ s, (f i).coeff 2 = 0 :=
        fun i hi => h2 i (Finset.mem_insert_of_mem hi)
      rw [Finset.prod_insert ha, coeff_mul_two, ih h0' h1' h2',
        coeff_zero_prod s f h0', coeff_one_prod s f h0' h1',
        h0 a (Finset.mem_insert_self a s), h1 a (Finset.mem_insert_self a s),
        h2 a (Finset.mem_insert_self a s)]
      simp

lemma nextA_support {a : ℕ → ℕ} (ha : ∀ i, 32 < i → a i = 0) {i : ℕ}
    (hi : 32 < i) : nextA a i = 0 := by
  have h1 : a i = 0 := ha i hi
  have h2 : a (2 * i) = 0 := ha (2 * i) (by omega)
  simp [nextA, h1, h2]

lemma nextA_even (a : ℕ → ℕ) {j : ℕ} (hj : ¬ Odd j) :
    nextA a j = 2 * a (2 * j) := by
  simp [nextA, hj]

/-- The doubling step, at the level of the product representation:
`(∏ (1 - X^i)^(a i)) · (∏ (1 - X^i)^(a i)).comp (-X)`
equals `(∏ (1 - X^i)^(nextA a i)).comp (X^2)`. -/
lemma prod_double {a : ℕ → ℕ} (ha : ∀ i, 32 < i → a i = 0) :
    prodForm a * (prodForm a).comp (-X) = (prodForm (nextA a)).comp (X ^ 2) := by
  have hL : prodForm a * (prodForm a).comp (-X)
      = ∏ i ∈ Finset.Icc 1 32, ((1 - X ^ i : ℚ[X]) * (1 - (-X) ^ i)) ^ a i := by
    rw [prodForm, Polynomial.prod_comp, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    rw [Polynomial.pow_comp, Polynomial.sub_comp, Polynomial.one_comp,
      Polynomial.pow_comp, Polynomial.X_comp, ← mul_pow]
  have hR : (prodForm (nextA a)).comp (X ^ 2)
      = ∏ j ∈ Finset.Icc 1 32, (1 - ((X : ℚ[X]) ^ 2) ^ j) ^ nextA a j := by
    rw [prodForm, Polynomial.prod_comp]
    apply Finset.prod_congr rfl
    intro j _
    rw [Polynomial.pow_comp, Polynomial.sub_comp, Polynomial.one_comp,
      Polynomial.pow_comp, Polynomial.X_comp]
  rw [hL, hR]
  have hodd : ∀ i : ℕ, Odd i → ((1 - X ^ i : ℚ[X]) * (1 - (-X) ^ i)) ^ a i
      = (1 - ((X : ℚ[X]) ^ 2) ^ i) ^ a i := by
    intro i hi
    have e : ((X : ℚ[X]) ^ 2) ^ i = (X ^ i) ^ 2 := by
      rw [← pow_mul X 2 i, ← pow_mul X i 2, mul_comm 2 i]
    rw [hi.neg_pow, e]
    congr 1
    ring
  have heven : ∀ i : ℕ, ¬ Odd i → ((1 - X ^ i : ℚ[X]) * (1 - (-X) ^ i)) ^ a i
      = (1 - X ^ i) ^ (2 * a i) := by
    intro i hi
    rw [(Nat.not_odd_iff_even.mp hi).neg_pow, ← pow_two, ← pow_mul', mul_comm (a i) 2]
  have hL2 : (∏ i ∈ (Finset.Icc 1 32).filter (fun i => Odd i),
        ((1 - X ^ i : ℚ[X]) * (1 - (-X) ^ i)) ^ a i)
      = ∏ i ∈ (Finset.Icc 1 32).filter (fun i => Odd i),
        (1 - ((X : ℚ[X]) ^ 2) ^ i) ^ a i :=
    Finset.prod_congr rfl fun i hi => hodd i (Finset.mem_filter.mp hi).2
  have hL3 : (∏ i ∈ (Finset.Icc 1 32).filter (fun i => ¬ Odd i),
        ((1 - X ^ i : ℚ[X]) * (1 - (-X) ^ i)) ^ a i)
      = ∏ i ∈ (Finset.Icc 1 32).filter (fun i => ¬ Odd i), (1 - X ^ i) ^ (2 * a i) :=
    Finset.prod_congr rfl fun i hi => heven i (Finset.mem_filter.mp hi).2
  have hre : (∏ j ∈ Finset.Icc 1 16, (1 - ((X : ℚ[X]) ^ 2) ^ j) ^ (2 * a (2 * j)))
      = ∏ i ∈ (Finset.Icc 1 32).filter (fun i => ¬ Odd i),
        (1 - X ^ i) ^ (2 * a i) := by
    apply Finset.prod_bij (fun j _ => 2 * j)
    · intro j hj
      rw [Finset.mem_Icc] at hj
      rw [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨by omega, by omega⟩, Nat.not_odd_iff_even.mpr ⟨j, two_mul j⟩⟩
    · intro j1 _ j2 _ h
      omega
    · intro i hi
      rw [Finset.mem_filter, Finset.mem_Icc] at hi
      obtain ⟨⟨h1, h32⟩, hev⟩ := hi
      rw [Nat.not_odd_iff_even] at hev
      obtain ⟨r, hr⟩ := hev
      exact ⟨r, by rw [Finset.mem_Icc]; omega, by omega⟩
    · intro j _
      rw [← pow_mul X 2 j]
  rw [← Finset.prod_filter_mul_prod_filter_not (Finset.Icc 1 32) (fun i => Odd i)
      (fun i => ((1 - X ^ i : ℚ[X]) * (1 - (-X) ^ i)) ^ a i), hL2, hL3, ← hre]
  have hRo : (∏ j ∈ (Finset.Icc 1 32).filter (fun j => Odd j),
        (1 - ((X : ℚ[X]) ^ 2) ^ j) ^ nextA a j)
      = (∏ j ∈ (Finset.Icc 1 32).filter (fun j => Odd j), (1 - ((X : ℚ[X]) ^ 2) ^ j) ^ a j)
        * ∏ j ∈ (Finset.Icc 1 32).filter (fun j => Odd j),
          (1 - ((X : ℚ[X]) ^ 2) ^ j) ^ (2 * a (2 * j)) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro j hj
    rw [Finset.mem_filter] at hj
    rw [nextA, if_pos hj.2, pow_add]
  have hRe : (∏ j ∈ (Finset.Icc 1 32).filter (fun j => ¬ Odd j),
        (1 - ((X : ℚ[X]) ^ 2) ^ j) ^ nextA a j)
      = ∏ j ∈ (Finset.Icc 1 32).filter (fun j => ¬ Odd j),
        (1 - ((X : ℚ[X]) ^ 2) ^ j) ^ (2 * a (2 * j)) := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [Finset.mem_filter] at hj
    rw [nextA, if_neg hj.2, zero_add]
  have hRest : (∏ j ∈ Finset.Icc 1 16, (1 - ((X : ℚ[X]) ^ 2) ^ j) ^ (2 * a (2 * j)))
      = ∏ j ∈ Finset.Icc 1 32, (1 - ((X : ℚ[X]) ^ 2) ^ j) ^ (2 * a (2 * j)) := by
    apply Finset.prod_subset
    · intro j hj
      rw [Finset.mem_Icc] at hj ⊢
      omega
    · intro j hj32 hj16
      rw [Finset.mem_Icc] at hj32 hj16
      have hz : a (2 * j) = 0 := ha (2 * j) (by omega)
      rw [hz, mul_zero, pow_zero]
  rw [← Finset.prod_filter_mul_prod_filter_not (Finset.Icc 1 32) (fun j => Odd j)
      (fun j => (1 - ((X : ℚ[X]) ^ 2) ^ j) ^ nextA a j), hRo, hRe, hRest,
    ← Finset.prod_filter_mul_prod_filter_not (Finset.Icc 1 32) (fun j => Odd j)
      (fun j => (1 - ((X : ℚ[X]) ^ 2) ^ j) ^ (2 * a (2 * j))), mul_assoc]

/-- The doubling step preserves the `1 + c * X + O(X^(m+1))` shape,
squaring the linear coefficient and halving the range of vanishing. -/
lemma good_transport {p q : ℚ[X]} {c : ℚ} {m : ℕ} (hm : 2 ≤ m)
    (hp : Good p c m) (h : p * p.comp (-X) = q.comp (X ^ 2)) :
    Good q (-c ^ 2) (m / 2) := by
  obtain ⟨h0, h1, hz⟩ := hp
  have hpc : ∀ n, (p.comp (-X)).coeff n = (-1) ^ n * p.coeff n :=
    fun n => coeff_comp_neg_X p n
  refine ⟨?_, ?_, ?_⟩
  · have e := coeff_comp_X_sq q 0
    rw [mul_zero] at e
    rw [← e, ← h, coeff_mul_zero, hpc 0, h0]
    simp
  · have e : q.coeff 1 = (q.comp (X ^ 2)).coeff 2 := by
      have h2 := coeff_comp_X_sq q 1
      rw [mul_one] at h2
      exact h2.symm
    rw [e, ← h, coeff_mul_two, hpc 0, hpc 1, hpc 2, h0, h1,
      hz 2 (le_refl 2) hm]
    ring
  · intro j hj2 hjm
    have e : q.coeff j = (q.comp (X ^ 2)).coeff (2 * j) := (coeff_comp_X_sq q j).symm
    rw [e, ← h, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    apply Finset.sum_eq_zero
    intro i hi
    dsimp only
    rw [Finset.mem_range] at hi
    rw [hpc (2 * j - i)]
    rcases eq_or_ne i 0 with rfl | hi0
    · simp only [Nat.sub_zero]
      rw [hz (2 * j) (by omega) (by omega)]
      simp
    · rcases eq_or_ne i 1 with rfl | hi1
      · rw [hz (2 * j - 1) (by omega) (by omega)]
        simp
      · rw [hz i (by omega) (by omega)]
        simp

/-- Reading off the two lowest coefficients of a product `∏ (1 - X^i)^(b i)`:
the exponent of `1 - X` is `65536` and the exponent of `1 - X^2` is its
binomial coefficient. -/
lemma extract {b : ℕ → ℕ} (h1 : (prodForm b).coeff 1 = -65536)
    (h2 : (prodForm b).coeff 2 = 0) :
    b 1 = 65536 ∧ b 2 = (65536).choose 2 := by
  unfold prodForm at h1 h2
  have hs1 : (1 : ℕ) ∈ Finset.Icc 1 32 := by rw [Finset.mem_Icc]; omega
  rw [← Finset.mul_prod_erase (Finset.Icc 1 32) (fun i => (1 - X ^ i : ℚ[X]) ^ b i)
    hs1] at h1 h2
  rw [pow_one] at h1 h2
  set R1 := ∏ x ∈ (Finset.Icc 1 32).erase 1, (1 - X ^ x : ℚ[X]) ^ b x with hR1def
  have hR10 : R1.coeff 0 = 1 := by
    apply coeff_zero_prod
    intro i hi
    apply coeff_zero_factor
    rw [Finset.mem_erase, Finset.mem_Icc] at hi
    omega
  have hR11 : R1.coeff 1 = 0 := by
    apply coeff_one_prod
    · intro i hi
      apply coeff_zero_factor
      rw [Finset.mem_erase, Finset.mem_Icc] at hi
      omega
    · intro i hi
      apply coeff_one_factor
      rw [Finset.mem_erase, Finset.mem_Icc] at hi
      omega
  rw [coeff_mul_one, hR10, hR11, coeff_one_one_sub_X, coeff_zero_one_sub_X] at h1
  have hb1 : b 1 = 65536 := by
    simp only [mul_zero, mul_one, zero_add, neg_inj] at h1
    exact_mod_cast h1
  have hs2 : (2 : ℕ) ∈ (Finset.Icc 1 32).erase 1 := by
    rw [Finset.mem_erase, Finset.mem_Icc]
    omega
  have hR1eq : R1 = (1 - X ^ (2:ℕ) : ℚ[X]) ^ b 2
      * ∏ x ∈ ((Finset.Icc 1 32).erase 1).erase 2, (1 - X ^ x) ^ b x := by
    rw [hR1def, ← Finset.mul_prod_erase _ (fun x => (1 - X ^ x : ℚ[X]) ^ b x) hs2]
  set R2 := ∏ x ∈ ((Finset.Icc 1 32).erase 1).erase 2, (1 - X ^ x : ℚ[X]) ^ b x
    with hR2def
  have hR20 : R2.coeff 0 = 1 := by
    apply coeff_zero_prod
    intro i hi
    apply coeff_zero_factor
    rw [Finset.mem_erase, Finset.mem_erase, Finset.mem_Icc] at hi
    omega
  have hR21 : R2.coeff 1 = 0 := by
    apply coeff_one_prod
    · intro i hi
      apply coeff_zero_factor
      rw [Finset.mem_erase, Finset.mem_erase, Finset.mem_Icc] at hi
      omega
    · intro i hi
      apply coeff_one_factor
      rw [Finset.mem_erase, Finset.mem_erase, Finset.mem_Icc] at hi
      omega
  have hR22 : R2.coeff 2 = 0 := by
    apply coeff_two_prod
    · intro i hi
      apply coeff_zero_factor
      rw [Finset.mem_erase, Finset.mem_erase, Finset.mem_Icc] at hi
      omega
    · intro i hi
      apply coeff_one_factor
      rw [Finset.mem_erase, Finset.mem_erase, Finset.mem_Icc] at hi
      omega
    · intro i hi
      apply coeff_two_factor
      rw [Finset.mem_erase, Finset.mem_erase, Finset.mem_Icc] at hi
      omega
  have hR12 : R1.coeff 2 = -(b 2 : ℚ) := by
    rw [hR1eq, coeff_mul_two, hR20, hR21, hR22, coeff_two_one_sub_X_sq,
      coeff_zero_factor (show (1:ℕ) ≤ 2 by omega),
      coeff_one_factor (show (2:ℕ) ≤ 2 by omega)]
    simp
  rw [coeff_mul_two, hR11, hR10, coeff_two_one_sub_X, coeff_zero_one_sub_X,
    coeff_one_one_sub_X] at h2
  rw [hR12] at h2
  have hb2 : b 2 = (b 1).choose 2 := by
    simp only [one_mul, mul_zero, add_zero, mul_one] at h2
    have h : (b 2 : ℚ) = ((b 1).choose 2 : ℚ) := by linarith [h2]
    exact_mod_cast h
  rw [hb1] at hb2
  exact ⟨hb1, hb2⟩

snip end

determine answer : ℕ := 2 ^ 27 - 2 ^ 11

problem usa1988_p5 (a : ℕ → ℕ)
    (h1 : (prodForm a).coeff 1 = -2)
    (hz : ∀ k, 2 ≤ k → k ≤ 32 → (prodForm a).coeff k = 0) :
    a 32 = answer := by
  -- The product only sees `a` on `[1, 32]`, so we may assume the exponents
  -- vanish outside that range.
  let b : ℕ → ℕ := fun i => if i ∈ Finset.Icc 1 32 then a i else 0
  have hprod : prodForm b = prodForm a := by
    apply Finset.prod_congr rfl
    intro i hi
    rw [show b i = a i from if_pos hi]
  have ha : ∀ i, 32 < i → b i = 0 := by
    intro i hi
    have hni : i ∉ Finset.Icc 1 32 := by rw [Finset.mem_Icc]; omega
    exact if_neg hni
  have hb32 : b 32 = a 32 := if_pos (by rw [Finset.mem_Icc]; omega)
  rw [← hprod] at h1 hz
  have h0 : (prodForm b).coeff 0 = 1 := by
    apply coeff_zero_prod
    intro i hi
    apply coeff_zero_factor
    rw [Finset.mem_Icc] at hi
    omega
  have g0 : Good (prodForm b) (-2) 32 := ⟨h0, h1, hz⟩
  -- Four doubling steps: `p(x) p(-x)`, each time squaring the linear
  -- coefficient and halving the number of vanishing coefficients.
  have hs1 : ∀ i, 32 < i → nextA b i = 0 := fun i hi => nextA_support ha hi
  have hs2 : ∀ i, 32 < i → nextA (nextA b) i = 0 := fun i hi => nextA_support hs1 hi
  have hs3 : ∀ i, 32 < i → nextA (nextA (nextA b)) i = 0 :=
    fun i hi => nextA_support hs2 hi
  have g1 : Good (prodForm (nextA b)) (-4) 16 :=
    good_transport (by norm_num) g0 (prod_double ha)
  have g2 : Good (prodForm (nextA (nextA b))) (-16) 8 :=
    good_transport (by norm_num) g1 (prod_double hs1)
  have g3 : Good (prodForm (nextA (nextA (nextA b)))) (-256) 4 :=
    good_transport (by norm_num) g2 (prod_double hs2)
  have g4 : Good (prodForm (nextA (nextA (nextA (nextA b))))) (-65536) 2 :=
    good_transport (by norm_num) g3 (prod_double hs3)
  obtain ⟨-, g41, g4z⟩ := g4
  obtain ⟨hb1, hb2⟩ := extract g41 (g4z 2 (le_refl 2) (le_refl 2))
  -- Unfolding the exponent bookkeeping: the exponent of `1 - X^2` after four
  -- steps is `16 * b 32`.
  have chain : nextA (nextA (nextA (nextA b))) 2 = 16 * b 32 := by
    rw [nextA_even _ (by decide : ¬ Odd 2), nextA_even _ (by decide : ¬ Odd (2 * 2)),
      nextA_even _ (by decide : ¬ Odd (2 * (2 * 2))),
      nextA_even _ (by decide : ¬ Odd (2 * (2 * (2 * 2))))]
    ring
  have hfin : 16 * b 32 = (65536).choose 2 := by
    rw [← chain]
    exact hb2
  rw [Nat.choose_two_right] at hfin
  have hanswer : b 32 = 2 ^ 27 - 2 ^ 11 := by omega
  rw [hb32] at hanswer
  exact hanswer

end Usa1988P5
