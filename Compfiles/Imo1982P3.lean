/-
Copyright (c) 2024 Alex Brodbelt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Brodbelt
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file {
  tags := [.Algebra]
  importedFrom :=
    "https://github.com/leanprover-community/mathlib4/pull/16190"
}

/-!
# International Mathematical Olympiad 1982, Problem 3

Consider infinite sequences $\{x_n \}$ of positive reals such that $x_0 = 0$ and
$x_0 \geq x_1 \geq x_2 \geq ...$

a) Prove that for every such sequence there is an $n \geq 1$ such that:

$\frac{x_0^2}{x_1} + \ldots + \frac{x_{n-1}^2}{x_n} \geq 3.999$

b) Find such a sequence such that for all n:

$\frac{x_0^2}{x_1} + \ldots + \frac{x_{n-1}^2}{x_n} < 4$
-/

namespace Imo1982Q3

snip begin

/-
The solution is based on the one at the
[Art of Problem Solving](https://artofproblemsolving.com/wiki/index.php/1982_IMO_Problems/Problem_3)
website.
-/

lemma sum_Fin_eq_sum_Ico {x : ℕ → ℝ} {N : ℕ} : ∑ n : Fin N, x n = ∑ n ∈ Finset.Ico 0 N, x n := by
  rw [Fin.sum_univ_eq_sum_range, Nat.Ico_zero_eq_range]

/-
Specialization of Cauchy-Schwarz inequality with the sequences x n / √(y n) and √(y n)
-/
theorem Sedrakyan's_lemma {ι : Type*} {s : Finset ι} {x y : ι → ℝ}
    (hN : 0 < Finset.card s) (_xi_pos : ∀ i ∈ s, 0 < x i) (yi_pos : ∀ i ∈ s, 0 < y i) :
    (∑ n ∈ s, x n) ^ 2 / (∑ n ∈ s, y n) ≤ ∑ n ∈ s, (x n) ^ 2 / y n := by
  have : 0 < ∑ n ∈ s, y n := Finset.sum_pos yi_pos <| Finset.card_pos.mp hN
  apply le_of_le_of_eq (b := ((∑ n ∈ s, x n ^ 2 / y n) * ∑ n ∈ s, y n) / ∑ n ∈ s, y n)
  · gcongr
    convert Finset.sum_mul_sq_le_sq_mul_sq s (fun n ↦ x n / √ (y n)) (fun n ↦ √ (y n)) with n hn n hn n hn
    all_goals specialize _xi_pos n hn
    all_goals specialize yi_pos n hn
    · field_simp
    · field_simp
    · rw [Real.sq_sqrt]
      positivity
  · field_simp

lemma ineq₁ {x : ℕ → ℝ} {N : ℕ} (hN : 1 < N) (hx : ∀ i , x (i + 1) ≤ x i) :
    x N ≤ (∑ n : Fin (N - 1), x (n + 1)) / (N - 1) := by
  have h : ∀ m n : ℕ, n ≤ m → x m ≤ x n := by
    intro m n mlen
    induction' m, mlen using Nat.le_induction with k _nlek xk_le_xn
    · exact le_refl (x n)
    · calc
      x (k + 1) ≤ x k := hx k
      _         ≤ x n := xk_le_xn
  rw [le_div_iff₀ (by aesop)]
  calc
  x N * (↑N - 1) = ((N - 1) : ℕ) * x N := by
    rw [mul_comm, Nat.cast_sub, Nat.cast_one]; linarith
  _ = ↑(Finset.range (N - 1)).card * x N := by rw [Finset.card_range]
  _ = ∑ _ ∈ Finset.range (N - 1), x N := by
    simp only [Finset.univ_eq_attach, Finset.sum_const, Finset.card_attach, Nat.card_Ioc, nsmul_eq_mul]
  _ ≤ ∑ n ∈ Finset.range (N - 1), x (n + 1) := by
    apply Finset.sum_le_sum
    intro i hi
    rw [Finset.mem_range, Nat.lt_sub_iff_add_lt (a := i) (b := 1) (c := N)] at hi
    apply h
    apply le_of_lt hi
  _ = ∑ n : Fin (N - 1), x (↑n + 1) := by rw [Finset.sum_range]

lemma ineq₂ {x : ℕ → ℝ} {N : ℕ}
    (hN : 1 < N) (hx : ∀ i , x (i + 1) ≤ x i) (x_pos : ∀ i, x i > (0 : ℝ)) :
  (N - 1) / N * (1 / ∑ n : Fin (N - 1), x (n + 1)) ≤ 1 / (∑ n : Fin N, x (n + 1)) := by
  have ne_zero : N - 1 ≠ 0 := Nat.sub_ne_zero_iff_lt.mpr hN
  have ne_zero' : (N : ℝ) - 1 ≠ 0 :=  by
    rw [ne_eq]; intro h
    rw [sub_eq_iff_eq_add, zero_add] at h
    rw [@Nat.cast_eq_one] at h
    rw [h] at hN; apply lt_irrefl _ hN
  have sum_range_pos : 0 < ∑ i ∈ Finset.range (N - 1), x (i + 1) := by
    apply Finset.sum_pos
    · intro i _hi
      apply x_pos _
    simp [ne_zero]
  have mul_sum_pos : 0 < ∑ i ∈ Finset.range (N - 1), x (i + 1) * ↑N / (↑N - 1) := by
    apply Finset.sum_pos
    · intro i _hi
      apply div_pos
      · apply mul_pos
        · apply x_pos
        simp only [Nat.cast_pos]
        linarith
      rw [lt_sub_iff_add_lt, zero_add, Nat.one_lt_cast]
      apply hN
    rw [Finset.nonempty_range_iff]
    exact ne_zero
  have sum_fin_pos : 0 < ∑ n : Fin N, x (↑n + 1) := by
    apply Finset.sum_pos; intro i _hi
    · apply x_pos (i +1)
    rw [Finset.univ_nonempty_iff, ← Fin.pos_iff_nonempty]
    linarith
  convert_to
    (N - 1) / N * (1 / ∑ n ∈ Finset.range (N - 1), x (n + 1)) ≤ 1 / (∑ n : Fin N, x (n + 1)) using 3
  · rw [Finset.sum_range]
  convert_to 1 / (N * (∑ n ∈ Finset.range (N - 1), x (n + 1)) / (N - 1)) ≤ 1 / (∑ n : Fin N, x (n + 1))
  · field_simp
  convert_to 1 / ∑ i ∈ Finset.range (N - 1), x (i + 1) * ↑N / (↑N - 1) ≤ 1 / (∑ n : Fin N, x (n + 1))
  · rw [mul_comm, Finset.sum_mul, Finset.sum_div]
  rw [div_le_div_iff₀ (mul_sum_pos) (sum_fin_pos), one_mul, one_mul, ]
  calc ∑ n : Fin N, x (↑n + 1) = ∑ n ∈ Finset.range N, x (n + 1) := by rw [Finset.sum_range]
  _ = ∑ n ∈ Finset.range (N - 1 + 1), x (n + 1) := by
    rw [Nat.sub_one_add_one_eq_of_pos (by linarith [hN])]
  _ = ∑ n ∈ Finset.range (N - 1), x (n + 1) + x N := by
    rw [Finset.sum_range_succ, Nat.sub_one_add_one_eq_of_pos (by linarith [hN])]
  _ ≤ ∑ n ∈ Finset.range (N - 1), x (n + 1) + (∑ n ∈ Finset.range (N - 1), x (n + 1)) / (↑N - 1) := by
    apply add_le_add_left; rw [Finset.sum_range]; apply ineq₁ hN hx;
  _ = ∑ n ∈ Finset.range (N - 1), x (n + 1) + (∑ n ∈ Finset.range (N - 1), x (n + 1) / (↑N - 1)) :=  by
    rw [Finset.sum_div]
  _ = ∑ n ∈ Finset.range (N - 1), (x (n + 1) + x (n + 1) / (↑N - 1)) := by rw [Finset.sum_add_distrib]
  _ = ∑ n ∈ Finset.range (N - 1),  N * x (n + 1) / (↑N - 1) := by
    apply Finset.sum_congr (by rfl)
    intro n _hn
    nth_rewrite 1 [
      ← one_mul (x (n + 1)),
      ← div_self (a := (N - 1 : ℝ)) (ne_zero'),
      mul_comm,
      mul_div,
      div_add_div_same
      ]
    nth_rewrite 2 [← mul_one (x (n + 1))]
    rw [← mul_add, mul_comm]
    simp only [sub_add_cancel]
  _ = ∑ i ∈ Finset.range (N - 1), x (i + 1) * ↑N / (↑N - 1) := by
    apply Finset.sum_congr (by rfl); intro n _hn; rw [mul_comm]

lemma ineq₃ {x : ℕ → ℝ} {N : ℕ } (hN : 1 < N) (x_pos : ∀ i, x i > (0 : ℝ)) :
    2 * (∑ n : Fin N, x (n + 1)) ≤ 1 + (∑ n : Fin N, x (n + 1))^2 := by
  have sum_fin_pos : 0 < ∑ n : Fin N, x (↑n + 1) := by
    apply Finset.sum_pos
    · intro i _hi
      apply x_pos (i +1)
    rw [Finset.univ_nonempty_iff, ←Fin.pos_iff_nonempty]
    linarith
  calc
  2 * (∑ n : Fin N, x (n + 1)) = 2 * (1^(1/2 : ℝ) * ((∑ n : Fin N, x (n  + 1))^2)^(1/2 : ℝ)) := by
    rw [Real.one_rpow, one_mul, ← Real.sqrt_eq_rpow, Real.sqrt_sq _]
    apply le_of_lt sum_fin_pos
  _ ≤ 2 * ((1/2 : ℝ) * 1 + (1/2 : ℝ) * (∑ n : Fin N, x (n  + 1))^2) := by
    rw [mul_le_mul_left (by norm_num)]
    apply Real.geom_mean_le_arith_mean2_weighted
      (by norm_num) (by norm_num) (by norm_num) (sq_nonneg _) (by norm_num)
  _ ≤ 1 + (∑ n : Fin N, x (n  + 1))^2 := by field_simp

lemma Ico_sdiff_zero_eq_Ico {N : ℕ} : Finset.Ico 0 N \ {0} = Finset.Ico 1 N := by
  rw [Finset.sdiff_singleton_eq_erase, Finset.Ico_erase_left, Nat.Ico_succ_left]

lemma eq₀ {x : ℕ → ℝ} {N : ℕ} (hN : 1 < N) (hx₀ : x 0 = (1 : ℝ)) :
    (∑ n : Fin N, (x n))^2
    = 1 + 2 * (∑ n : Fin (N - 1), x (n + 1)) + (∑ n : Fin (N - 1), x (n + 1))^2 := by
  have zero_lt_N : 0  < N := by linarith
  have two_le_N : 2 ≤ N := by linarith
  have : ∀ N, 2 ≤ N → ∑ n : Fin (N - 1), x (↑n + 1) = (∑ n ∈ Finset.Ico 1 N, x n) := by
    intro N hN
    let f : ℕ → ℝ := (fun n => x (n + 1))
    induction' N, hN using Nat.le_induction with d two_le_d hd
    case base => simp
    case succ =>
      have one_le_d : 1 ≤ d := by exact Nat.one_le_of_lt two_le_d
      rw [
        ← Finset.sum_range (n := d + 1 - 1) (f := f),
        Nat.sub_add_comm (one_le_d),
        Finset.sum_range_succ, Finset.sum_range, hd, Finset.sum_Ico_succ_top one_le_d]
      simp only [add_right_inj, f]
      rw [Nat.sub_add_cancel one_le_d]
  rw [
    sum_Fin_eq_sum_Ico, Finset.sum_eq_sum_diff_singleton_add (i := 0) (by simp [zero_lt_N]),
    Ico_sdiff_zero_eq_Ico, pow_two, hx₀
    ]
  ring_nf
  rw [this _ two_le_N]; ring

snip end

problem iom1982_p3a {x : ℕ → ℝ} (x_pos : ∀ i, x i > (0 : ℝ))
    (hx₀ : x 0 = (1 : ℝ))
    (hx : ∀ i , x (i + 1) ≤ x i) :
    ∃ N : ℕ, 3.999 ≤ ∑ n : Fin N, (x n)^2 / x (n + 1) := by
  have div_prev_pos : ∀ N > 1, 0 < (↑N - 1) / (N : ℝ) := by
    intro N hN
    exact div_pos (by linarith) (by linarith)
  have sum_xi_pos : ∀ N > 0, 0 < (∑ n : Fin N, x n) := by
    intro N hN
    apply Finset.sum_pos
    · intro i _hi
      apply x_pos i
    rw [← Finset.card_pos, Finset.card_fin]
    apply hN
  have sum_xi_pos' : ∀ N > 1, 0 < (∑ n : Fin (N - 1), x (n + 1)) := by
    intro N hN
    apply Finset.sum_pos
    · intro i _hi
      apply x_pos _
    rw [← Finset.card_pos, Finset.card_fin, Nat.lt_sub_iff_add_lt, zero_add]
    apply hN
  have sedrakayan's_lemma :
    ∀ N > 0,
    ((∑ n : Fin N, (x n))^2 / (∑ n : Fin N, x (n + 1))) ≤ (∑ n : Fin N, (x n)^2 / x (n + 1)) :=
    fun N hN => Sedrakyan's_lemma (by simpa) (fun i _ => x_pos i) (fun i _ => x_pos (i + 1))
  have :
    ∃ (N : ℕ), 0 < N ∧ 1 < N ∧ 2 < N ∧  (3.999 : ℝ) ≤ 4 * ((N - 1) / N) :=  by use 4000; norm_num
  obtain ⟨N, zero_lt_N, one_lt_N, two_lt_N, ineq₀⟩ := this
  use N
  calc (3.999 : ℝ) ≤ 4 * ((N - 1) / N) := ineq₀
  _ = (2 + 2) * ((N - 1) / N) := by norm_num
  _ = ((2 * (∑ n : Fin (N - 1), x (n + 1))
    + 2 * (∑ n : Fin (N - 1), x (n + 1))) / (∑ n : Fin (N - 1), x (n + 1))) * ((N - 1) / (N)) := by
    rw [← div_add_div_same, ← mul_div, div_self, mul_one]
    symm
    apply (lt_iff_le_and_ne.mp (sum_xi_pos' _ one_lt_N)).right
  _ ≤ (1 + (∑ n : Fin (N - 1), x (n + 1))^2
    + 2 * (∑ n : Fin (N - 1), x (n + 1))) / (∑ n : Fin (N - 1), x (n + 1)) * ((N - 1) / (N)) := by
    rw [mul_le_mul_right (by apply div_prev_pos N; simp [one_lt_N])]
    apply div_le_div₀
    · apply add_nonneg
      · apply add_nonneg (by norm_num) (sq_nonneg _)
      apply mul_nonneg (by norm_num)
      apply (lt_iff_le_and_ne.mp (sum_xi_pos' _ one_lt_N)).left
    · apply add_le_add_right
      apply ineq₃ _ x_pos
      rw [Nat.lt_sub_iff_add_lt, one_add_one_eq_two]
      apply two_lt_N
    · apply sum_xi_pos' _ one_lt_N
    apply le_refl
  _ = ((∑ n : Fin N, (x n))^2 / (∑ n : Fin (N - 1), x (n + 1))) * ((N - 1) / (N)) := by
    rw [
      eq₀ one_lt_N hx₀,
      add_assoc,
      add_comm ((∑ n : Fin (N - 1), x (↑n + 1)) ^ 2),
      ← add_assoc
      ]
  _ = ((∑ n : Fin N, (x n))^2) * ((N - 1) / (N)) * (1 / (∑ n : Fin (N - 1), x (n + 1))) := by
    rw [← mul_one (((∑ n : Fin N, x ↑n) ^ 2)), mul_div]
    ring
  _ ≤ ((∑ n : Fin N, (x n))^2 / (∑ n : Fin N, x (n + 1))) := by
    nth_rewrite 2 [← mul_one (((∑ n : Fin N, x ↑n) ^ 2))]
    rw [← mul_div _ 1, mul_assoc, mul_le_mul_left]
    apply ineq₂ one_lt_N hx x_pos
    apply sq_pos_of_pos (sum_xi_pos _ zero_lt_N)
  _ ≤ ∑ n : Fin N, (x ↑n) ^ 2 / x (↑n + 1) := by
    apply sedrakayan's_lemma
    apply zero_lt_N

noncomputable determine sol : ℕ → ℝ := fun n => (1/2)^n

problem imo1982_p3b :
    (∀ i, sol i > 0) ∧ (∀ i, sol (i + 1) ≤ sol i) ∧ (sol 0 = 1)
      ∧ ∀ N, ∑ n ∈ Finset.range (N + 1), (sol n ^2 / (sol (n + 1))) < 4 := by
  constructor
  · intro i
    apply pow_pos (by norm_num) i
  constructor
  · intro i
    apply pow_le_pow_of_le_one (by norm_num)
    · rw [one_div_le (by norm_num) (by norm_num), div_one]; norm_num
    · apply Nat.le_succ
  constructor
  · rfl
  intro N
  dsimp [sol]
  rw [
    Finset.sum_eq_sum_diff_singleton_add
      (s := Finset.range (N + 1)) (i := 0) (Finset.mem_range.mpr (by linarith)),
    pow_zero, zero_add, one_pow, pow_one, one_div_one_div, add_comm
    ]
  convert_to (2 + ∑ n ∈ Finset.range N, (1/2) ^ n : ℝ) < 4 using 2
  induction' N with k hk
  case zero =>
    simp only [
      zero_add, Finset.range_one, sdiff_self, Finset.bot_eq_empty, one_div, inv_pow, div_inv_eq_mul,
      Finset.sum_empty, Finset.range_zero
      ]
  case succ =>
    rw [
      Finset.sum_range_succ, ← hk, Finset.range_add_one
      ]
    simp only [
      one_div, inv_pow, div_inv_eq_mul, Finset.singleton_subset_iff, Finset.mem_insert,
      self_eq_add_left, AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false,
      Finset.mem_range, lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true,
      Finset.sum_sdiff_eq_sub, lt_self_iff_false, not_false_eq_true, Finset.sum_insert,
      Finset.sum_singleton, pow_zero, one_pow, inv_one, zero_add, pow_one, one_mul
      ]
    rw [
      ← pow_mul, mul_comm, ← inv_pow
      ]
    nth_rewrite 1 [← inv_inv 2]
    rw [
      mul_comm, inv_pow 2⁻¹, ← pow_sub₀ (a := 2⁻¹) (ha := by norm_num) (h := by linarith), add_mul,
      one_mul, add_assoc, one_add_one_eq_two, mul_comm k 2, two_mul, add_assoc,
      Nat.add_sub_assoc (by linarith), Nat.sub_self, add_zero, inv_pow, add_sub_assoc, add_comm
    ]
  rw [
    geom_sum_eq (by norm_num), half_sub, div_neg, div_eq_inv_mul, one_div, inv_inv,
    mul_comm, ← neg_mul, neg_sub
    ]
  have h₁: (0 < (2 : ℝ)⁻¹ ^ N) := by positivity
  linarith [h₁]

end Imo1982Q3
