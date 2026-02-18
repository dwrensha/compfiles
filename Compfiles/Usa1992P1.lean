/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Tactic

import ProblemExtraction

set_option backward.isDefEq.respectTransparency false

problem_file { tags := [.Algebra] }

/-!
# USA Mathematical Olympiad 1992, Problem 1

Find, as a function of n, the sum of the digits of

     9 × 99 × 9999 × ... × (10^2ⁿ - 1),

where each factor has twice as many digits as the last one.
-/

namespace Usa1992P1

snip begin

-- TODO add a generalization of this mathlib?
lemma digits_pow (m : ℕ) : (Nat.digits 10 (10^m)).length = m + 1 := by
  induction' m with m ih
  · simp
  rw [pow_succ, Nat.digits_def' (by norm_num) (by positivity)]
  rw [mul_div_cancel_right₀ _ (by norm_num), List.length_cons]
  rw [ih]

lemma lemma2 {m y: ℕ} (hy : y < 10^m) : (Nat.digits 10 y).length < m + 1 := by
  induction m generalizing y with
  | zero => simp [show y = 0 by lia]
  | succ m ih =>
    obtain rfl | hyp := Nat.eq_zero_or_pos y
    · simp
    rw [Nat.digits_def' (by norm_num) hyp]
    rw [List.length_cons, add_lt_add_iff_right]
    have h2 : y / 10 < 10 ^ m := by lia
    exact ih h2

lemma digits_sum_mul_pow {m x : ℕ} :
    (Nat.digits 10 (x * 10 ^ m)).sum = (Nat.digits 10 x).sum := by
  cases x with
  | zero => simp
  | succ x =>
    rw [mul_comm, Nat.digits_base_pow_mul (by lia) (by lia)]
    simp

lemma digits_sum (m x y : ℕ)
    (h1 : y < 10^m) :
    (Nat.digits 10 (x * 10^m + y)).sum =
    (Nat.digits 10 (x * 10^m)).sum + (Nat.digits 10 y).sum := by
  cases x with | zero => simp | succ x =>
  -- choose k such that (digits 10 y).length + k = m
  have h3 : (Nat.digits 10 y).length ≤ m := by
    have h4 := lemma2 h1
    exact Nat.le_of_lt_succ h4
  have ⟨k, hk⟩ : ∃ k, (Nat.digits 10 y).length + k = m := Nat.le.dest h3
  nth_rewrite 1 [add_comm, mul_comm]
  nth_rewrite 1 [←hk]
  have one_lt_ten : 1 < 10 := by norm_num
  rw [←Nat.digits_append_zeroes_append_digits one_lt_ten (Nat.zero_lt_succ x)]
  simp only [List.sum_append, List.sum_replicate, smul_eq_mul, mul_zero, add_zero]
  rw [digits_sum_mul_pow]
  ring

lemma Finset.prod_odd {α : Type} [DecidableEq α] {f : α → ℕ} {s : Finset α}
    (hs : ∀ i ∈ s, Odd (f i)) : Odd (∏ i ∈ s, f i) := by
  revert hs
  induction s using Finset.induction
  case empty => simp
  case insert a s' ha ih =>
    intro hs'
    rw [Finset.prod_insert ha, Nat.odd_mul]
    simp only [Finset.mem_insert, forall_eq_or_imp] at hs'
    specialize ih hs'.2
    exact ⟨hs'.1, ih⟩

lemma lemma3 {m : ℕ} (hm : (m % 10) + 1 < 10) :
    (Nat.digits 10 (m + 1)).sum = (Nat.digits 10 m).sum + 1 := by
  rw [Nat.digits_eq_cons_digits_div (by norm_num) (by lia)]
  by_cases h : m = 0
  · simp [h]
  nth_rw 2 [Nat.digits_eq_cons_digits_div (by norm_num) (by exact h)]
  simp only [List.sum_cons]
  lia

theorem lemma6 {b : ℕ} {l1 l2 : List ℕ} (hg : List.Forall₂ (· ≥ ·) l1 l2) :
    Nat.ofDigits b l1 ≥ Nat.ofDigits b l2 := by
  induction l1 generalizing l2 with
  | nil => simp_all [Nat.ofDigits]
  | cons hd₁ tl₁ ih₁ =>
    induction l2 generalizing tl₁ with
    | nil => simp_all
    | cons hd₂ tl₂ _ =>
      simp only [Nat.ofDigits_cons]
      have htl : List.Forall₂ (fun x1 x2 ↦ x1 ≥ x2) tl₁ tl₂ := by
        simp_all only [ge_iff_le, List.forall₂_cons]
      specialize ih₁ htl
      have h1 : hd₁ ≥ hd₂ := by simp_all only [ge_iff_le, List.forall₂_cons, and_true]
      gcongr

/-- The subtraction of ofDigits of two lists is equal to ofDigits of digit-wise subtraction of them -/
theorem ofDigits_sub_ofDigits_eq_ofDigits_zipWith {b : ℕ} {l1 l2 : List ℕ}
    (hg : List.Forall₂ (· ≥ ·) l1 l2) :
    Nat.ofDigits b l1 - Nat.ofDigits b l2 =
    Nat.ofDigits b (l1.zipWith (· - ·) l2) := by
  induction l1 generalizing l2 with
  | nil => simp_all [Nat.ofDigits]
  | cons hd₁ tl₁ ih₁ =>
    induction l2 generalizing tl₁ with
    | nil => simp_all
    | cons hd₂ tl₂ ih₂ =>
      simp_all only [Nat.ofDigits_cons, List.zipWith_cons_cons]
      have htl : List.Forall₂ (fun x1 x2 ↦ x1 ≥ x2) tl₁ tl₂ := by
        simp_all only [ge_iff_le, List.forall₂_cons]
      specialize ih₁ htl
      rw [← ih₁, Nat.mul_sub]
      have h1 : hd₁ ≥ hd₂ := by simp_all only [ge_iff_le, List.forall₂_cons, and_true]
      have h2 : b * Nat.ofDigits b tl₁ ≥ b * Nat.ofDigits b tl₂ := by
        have : Nat.ofDigits b tl₁ ≥ Nat.ofDigits b tl₂ := lemma6 htl
        gcongr
      lia

lemma lemma8 {n : ℕ} : 10 ^ n - 1 = Nat.ofDigits 10 (List.replicate n 9) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, Nat.ofDigits_cons]
    replace ih : 10 ^ n = Nat.ofDigits 10 (List.replicate n 9) + 1 := by
      have : 1 ≤ 10 ^ n := Nat.one_le_pow' n 9
      lia
    rw [pow_succ, ih]
    lia

lemma lemma9 {m n : ℕ} (hm : m < 10^n) : (Nat.digits 10 m).length ≤ n := by
  exact (Nat.digits_length_le_iff (by norm_num) m).mpr hm

def padList (l : List ℕ) (n : ℕ) : List ℕ := l ++ List.replicate (n - l.length) 0

lemma padList_cons {hd n : ℕ} {tl : List ℕ} : padList (hd::tl) (n + 1) = hd :: padList tl n := by
  simp [padList]

def digitsPadded (b m n : ℕ) : List ℕ := padList (Nat.digits b m) n

theorem digitsPadded_lt_base {b m n d : ℕ} (hb : 1 < b)
    (hd : d ∈ digitsPadded b m n) :
    d < b := by
  unfold digitsPadded padList at hd
  simp only [List.mem_append, List.mem_replicate, ne_eq] at hd
  obtain hd | hd := hd
  · exact Nat.digits_lt_base hb hd
  · lia

theorem digitsPaddedLength (b m n : ℕ) (hm : (Nat.digits b m).length ≤ n) :
     (digitsPadded b m n).length = n := by
  unfold digitsPadded padList
  simp only [List.length_append, List.length_replicate]
  exact Nat.add_sub_of_le hm

theorem exists_prefix (L : List ℕ) :
    ∃ l1 : List ℕ, (∀ hl1 : l1 ≠ [], l1.getLast hl1 ≠ 0) ∧
      ∃ m : ℕ, L = l1 ++ List.replicate m 0 := by
  induction L with
  | nil => simp
  | cons hd tl ih =>
    obtain ⟨l2, hl20, m, hm⟩ := ih
    by_cases hnil : l2 ≠ []
    · specialize hl20 hnil
      subst hm
      use hd :: l2
      have h5 : ∀ (hl1 : hd :: l2 ≠ []), (hd :: l2).getLast hl1 ≠ 0 := by simp_all
      refine ⟨h5, m, ?_⟩
      simp
    · simp only [ne_eq, Decidable.not_not] at hnil
      subst hnil
      simp only [List.nil_append] at hm
      subst hm
      cases hd with
      | zero =>
        use []
        constructor
        · simp
        · use m + 1
          rw [List.replicate_succ, List.nil_append]
      | succ hd =>
        use [hd + 1]
        constructor
        · simp
        · use m
          simp

theorem digitsPadded_ofDigits (b n : ℕ) (h : 1 < b) (L : List ℕ) (w₁ : ∀ l ∈ L, l < b)
    (hn : L.length ≤ n) :
    digitsPadded b (Nat.ofDigits b L) n = padList L n := by
  have ⟨l1, hl1, m, hm⟩ := exists_prefix L
  subst hm
  rw [Nat.ofDigits_append_replicate_zero]
  unfold digitsPadded
  have hl : ∀ l ∈ l1, l < b := by simp_all
  have hl3 : ∀ (h : l1 ≠ []), l1.getLast h ≠ 0 := by simp_all
  rw [Nat.digits_ofDigits b h _ hl hl3]
  simp only [padList, List.length_append, List.length_replicate, List.append_assoc,
             List.replicate_append_replicate, List.append_cancel_left_eq, List.replicate_inj,
             or_true, and_true]
  simp only [List.length_append, List.length_replicate] at hn
  lia

theorem digitsPadded_sum (b m n : ℕ) :
    (digitsPadded b m n).sum = (Nat.digits b m).sum := by
  simp [digitsPadded, padList]

lemma List.map_eq_zip (x : ℕ) (l : List ℕ) (f : ℕ → ℕ → ℕ)
    : (List.map (f x) l) = List.zipWith f (List.replicate l.length x) l := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.map_cons, List.length_cons, ih]
    rfl

lemma lemma5 {m n : ℕ} (hm : m < 10^n) :
    digitsPadded 10 (10^n - 1 - m) n =
    (digitsPadded 10 m n).map (fun d ↦ 9 - d) := by
  let m_digits := Nat.digits 10 m
  let padding := List.replicate (n - m_digits.length) 0
  let m_digits_padded := m_digits ++ padding
  let complement_digits := m_digits_padded.map (λ d ↦ 9 - d)
  have h_length : m_digits_padded.length = n := by
    rw [List.length_append, List.length_replicate]
    have : m_digits.length ≤ n := lemma9 hm
    lia

  have h_sub2 : m = Nat.ofDigits 10 m_digits_padded := by
    unfold m_digits_padded padding m_digits
    rw [Nat.ofDigits_append, Nat.ofDigits_digits, Nat.ofDigits_replicate_zero,
        mul_zero, add_zero]

  have h_length2 : (List.replicate n 9).length = m_digits_padded.length := by
    rw [h_length]
    exact List.length_replicate

  have ha : List.Forall₂ (fun x1 x2 ↦ x1 ≥ x2) (List.replicate n 9) m_digits_padded := by
    unfold m_digits_padded padding
    rw [List.forall₂_iff_get]
    refine ⟨h_length2, ?_⟩
    intro i h1 h2
    simp only [List.get_eq_getElem, List.getElem_replicate, ge_iff_le]
    obtain hl | hr := Nat.lt_or_ge i m_digits.length
    · rw [List.getElem_append_left hl]
      unfold m_digits
      have h3 : (Nat.digits 10 m)[i] ∈ Nat.digits 10 m := List.getElem_mem hl
      have : (Nat.digits 10 m)[i] < 10 := Nat.digits_lt_base' h3
      exact Nat.le_of_lt_succ this
    · rw [List.getElem_append_right hr]
      simp

  have h_sub : 10^n - 1 - m = Nat.ofDigits 10 complement_digits := by
    have h1 := ofDigits_sub_ofDigits_eq_ofDigits_zipWith (b := 10) ha
    have h2 : List.zipWith (fun x1 x2 ↦ x1 - x2) (List.replicate n 9) m_digits_padded =
           List.map (fun d ↦ 9 - d) m_digits_padded := by
      have h5 := List.map_eq_zip 9 m_digits_padded (fun x y ↦ x - y)
      rw [h5]
      rw [h_length]
    rw [h2] at h1
    unfold complement_digits
    rw [←h1, ←lemma8, h_sub2]
  rw [h_sub]
  have h12 : ∀ l ∈ complement_digits, l < 10 := by
    intro x hx
    simp only [List.map_append, List.mem_append, List.mem_map, complement_digits, m_digits_padded,
               padding, m_digits] at hx
    lia
  have h14 : complement_digits.length ≤ n := by
    simp only [List.map_append, List.length_append, List.length_map, complement_digits,
               m_digits_padded, padding, List.length_replicate, m_digits]
    have : (Nat.digits 10 m).length ≤ n := lemma9 hm
    simp_all
  have h13 := digitsPadded_ofDigits 10 n (by norm_num) complement_digits h12 h14
  rw [h13]

  have h16 : (Nat.digits 10 m).length ≤ n := lemma9 hm
  simp [digitsPadded, padList, List.map_append, List.map_replicate, tsub_zero, complement_digits,
        m_digits_padded, padding, m_digits, h16]

lemma List.sum_map_sub_aux (l1 l2 : List ℕ) (h2 : List.Forall₂ (· ≥ ·) l1 l2) :
    (List.zipWith (fun x1 x2 ↦ x1 - x2) l1 l2).sum = l1.sum - l2.sum ∧ l1.sum ≥ l2.sum := by
match l1, l2 with
| [], [] => simp
| [], h :: tl => simp_all
| h :: tl, [] => simp_all
| hd1 :: tl1, hd2 :: tl2 =>
  have hp : List.Forall₂ (fun x1 x2 ↦ x1 ≥ x2) tl1 tl2 := by simp_all only [List.forall₂_cons]
  have ih := List.sum_map_sub_aux tl1 tl2 hp
  simp only [List.zipWith_cons_cons, List.sum_cons]
  rw [ih.1]
  have h3 : hd1 ≥ hd2 := (List.forall₂_cons.mp h2).1
  lia

lemma List.sum_map_sub (l1 l2 : List ℕ) (h2 : List.Forall₂ (· ≥ ·) l1 l2) :
    (List.zipWith (fun x1 x2 ↦ x1 - x2) l1 l2).sum = l1.sum - l2.sum :=
  (List.sum_map_sub_aux l1 l2 h2).1

lemma lemma4 {m n : ℕ} (hm : m < 10^n) :
    (Nat.digits 10 (10^n - 1 - m)).sum = 9 * n - (Nat.digits 10 m).sum := by
  rw [←digitsPadded_sum, lemma5 hm]
  have h2 := List.map_eq_zip 9 (digitsPadded 10 m n) (fun x y ↦ x - y)
  rw [h2]
  have h5 : List.Forall₂ (· ≥ ·)
              (List.replicate (digitsPadded 10 m n).length 9) (digitsPadded 10 m n) := by
     rw [List.forall₂_iff_get]
     refine ⟨List.length_replicate, ?_⟩
     intro x1 hx1 hx2
     simp only [List.get_eq_getElem, List.getElem_replicate, ge_iff_le]
     have h7 := digitsPadded_lt_base (show 1 < 10 by norm_num) (List.getElem_mem hx2)
     lia
  have h4 := List.sum_map_sub _ _ h5
  simp only [List.sum_replicate, smul_eq_mul] at h4
  rw [mul_comm]
  have h6 := digitsPaddedLength _ _ _ (lemma9 hm)
  rw [h6] at h4 ⊢
  rw [digitsPadded_sum] at h4
  exact h4

snip end

determine solution : ℕ → ℕ := fun n ↦ 9 * 2 ^ n

problem usa1992_p1 (n : ℕ) :
    (Nat.digits 10
     (∏ i ∈ Finset.range (n + 1), (10^(2^i) - 1))).sum = solution n := by
  -- We follow the informal proof from
  -- https://prase.cz/kalva/usa/usoln/usol921.html

  induction' n with n ih
  · simp

  let a i := 10^(2^i) - 1

  -- Obviously, for all i, a i < 10^(2^i).
  have h1 : ∀ i, a i < 10 ^ (2 ^ i) := fun i ↦ by
    dsimp [a]
    have h2 : 0 < 10 ^ 2 ^ i := by positivity
    lia

  have ha1 : ∀ i, 1 ≤ a i := fun i ↦ by
    dsimp [a]
    have h3 : 1 ≤ 2 ^ i := Nat.one_le_two_pow
    have h4 : 10 ^ 1 ≤ 10 ^ (2 ^ i) :=
      Nat.pow_le_pow_right (by norm_num) h3
    lia

  let b : ℕ → ℕ := fun m ↦ ∏ i ∈ Finset.range (m + 1), a i
  change (Nat.digits 10 (b (n +1))).sum = solution (n + 1)

  -- So, for all m, `b m < 10^(1 + 2 + 2^2 + ... + 2^m)`.
  have h2 : ∀ m, b m < 10^(∑ i ∈ Finset.range (m + 1), 2^i) := fun m ↦ by
    dsimp [b]
    rw [←Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_lt_prod_of_nonempty ?_ ?_ Finset.nonempty_range_add_one
    · intro i hi
      exact ha1 i
    · intro i hi
      exact h1 i

  -- ... < 10^(2^m).
  have h3 : ∀ m, 10^(∑ i ∈ Finset.range m, 2^i) < 10^(2^m) := fun m ↦ by
    have h4 : ∑ i ∈ Finset.range m, 2 ^ i < 2 ^ m :=
      Nat.geomSum_lt (le_refl _) fun _ hk ↦ Finset.mem_range.mp hk
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).mpr h4

  have bn_ge_nine : 9 ≤ b n := by
    clear ih
    dsimp [b, a]
    induction n
    case zero => simp
    case succ n ih2 =>
      rw [Finset.prod_range_succ]
      exact le_mul_of_le_of_one_le ih2 (ha1 (n + 1))

  -- Now b (n + 1) = (b n) * 10^N - b n, where N = 2^(n + 1).
  have h4 : b (n + 1) = b n * 10^(2^(n+1)) - b n := by
    nth_rewrite 2 [←mul_one (b n)]
    rw [←Nat.mul_sub_left_distrib]
    dsimp [b]
    rw [Finset.prod_range_succ]

  -- But b n < 10^N,
  have h5 : b n < 10 ^ 2 ^ (n + 1) := by
    calc _ < 10 ^ ∑ i ∈ Finset.range (n + 1), 2 ^ i := h2 _
         _ < 10 ^ 2 ^ (n + 1) := h3 (n + 1)

  have h7 : 1 ≤ b n := by
    dsimp [b]
    exact Finset.one_le_prod' fun i a ↦ ha1 i

  -- ... so b (n + 1) = (b n - 1)10^N + (10^N - b n)
  have h6 : b (n + 1) = (b n - 1) * 10 ^(2^(n+1)) + (10 ^(2^(n+1)) - b n) := by
    rw [h4]
    -- TODO: simpler version via zify
    have h5' := h5.le
    have h8 : 10 ^ 2 ^ (n + 1) ≤ b n * 10 ^ 2 ^ (n + 1) :=
      Nat.le_mul_of_pos_left (10 ^ 2 ^ (n + 1)) h7
    rw [←Nat.add_sub_assoc h5']
    nth_rewrite 2 [add_comm]
    rw [Nat.mul_sub_right_distrib, one_mul, Nat.add_sub_of_le h8]

  -- ... and the digit sum of b (n + 1) is just
  -- the digit sum of (b n - 1)·10^N plus the digit sum of (10^N - b n).
  have h8 : (Nat.digits 10 (b (n + 1))).sum =
            (Nat.digits 10 ((b n - 1) * 10 ^ 2 ^ (n+1))).sum +
            (Nat.digits 10 (10^2^(n+1) - b n)).sum := by
   have h9 : 0 < b n := h7
   have h10 := digits_sum (2^(n+1)) (b n - 1) (10^2^(n+1) - b n)
             (Nat.sub_lt_self h9 h5.le) -- ..
   rw [←h10, h4]
   congr 2
   lia

  -- b n is odd
  have h9 : ∀ n, Odd (b n) := by
    intro n
    unfold b a
    suffices H : ∀ i ∈ Finset.range (n + 1), Odd (a i) from Finset.prod_odd H
    intro i hi
    rw [Nat.odd_iff]
    have h32 : (10 ^ 2 ^ i) % 2 = 0 := by
      rw [show 10 = 5 * 2 by rfl]
      rw [mul_pow, Nat.mul_mod, Nat.pow_mod]
      simp
    rw [←Nat.even_iff] at h32
    rw [←Nat.odd_iff]
    have h33 : Odd 1 := Nat.odd_iff.mpr rfl
    have h34 : 1 ≤ 10 ^ 2 ^ i := Nat.one_le_pow' (2 ^ i) 9
    exact Nat.Even.sub_odd h34 h32 h33

  -- ... so its last digit is non-zero,
  have h10 : (Nat.digits 10 (b n)).head! ≠ 0 := by
    rw [Nat.head!_digits (by norm_num)]
    intro h11
    have h13 : 2 ∣ b n := by lia
    have h14 : ¬ 2 ∣ b n := Odd.not_two_dvd_nat (h9 _)
    contradiction

  have one_lt_ten : 1 < 10 := by norm_num

  -- ... so the digit sum of `b n - 1` is one less than the digit sum of `b n`,
  have h11 : (Nat.digits 10 (b n - 1)).sum = (Nat.digits 10 (b n)).sum - 1 := by
    rw [Nat.digits_def' one_lt_ten (by lia)]
    nth_rewrite 2 [Nat.digits_def' one_lt_ten (by lia)]
    rw [List.sum_cons, List.sum_cons]
    have h13 : b n % 10 ≠ 0 := by
      intro h11
      have h13 : 2 ∣ b n := by lia
      have h14 : ¬ 2 ∣ b n := Odd.not_two_dvd_nat (h9 _)
      contradiction

    have h12 : (b n - 1) / 10 = b n / 10 := by lia
    rw [h12]
    suffices H : (b n - 1) % 10 + 1 = b n % 10 by lia
    lia

  -- ... and hence is 9·2^n - 1.
  rw [ih, solution] at h11

  -- Multiplying by 10^N does not change the digit sum.
  rw [digits_sum_mul_pow, h11] at h8
  clear h11

  -- (10^N - 1) - b n has 2^(n+1) digits,
  -- each 9 minus the corresponding digit of b n,
  -- so its digit sum is 9·2^(n+1) - 9·2^n.
  have h12 : (Nat.digits 10 (10 ^ 2 ^ (n + 1) - 1 - b n)).sum = 9 * 2^(n + 1) - 9 * 2^n := by
    change (Nat.digits 10 (b n)).sum = 9 * 2^n at ih
    rw [lemma4 h5, ih]

  -- b n is odd, so its last digit is not 0,
  -- and hence the last digit of (10^N - 1) - b n is not 9.
  -- So the digit sum of 10^N - b n is 9·2^(n + 1) - 9·2^n + 1.
  have h13 : (Nat.digits 10 (10 ^ 2 ^ (n + 1) - b n)).sum = 9 * 2^(n + 1) - 9 * 2^n + 1 := by
    have h15 : ((10 ^ 2 ^ (n + 1) - 1 - b n) % 10) + 1 < 10 := by
      by_contra! H
      replace H : 9 % 10 = (10 ^ 2 ^ (n + 1) - 1 - b n) % 10 := by lia
      change _ ≡ _ [MOD 10] at H
      rw [show 10 = 2 * 5 by rfl] at H
      have h40 : Nat.Coprime 2 5 := by norm_num
      rw [←Nat.modEq_and_modEq_iff_modEq_mul h40] at H
      obtain ⟨H1, -⟩ := H
      change _ % _ = _ % _ at H1
      simp only [Nat.reduceMod, Nat.reduceMul] at H1
      symm at H1
      rw [←Nat.odd_iff] at H1
      have h42 : (10 ^ 2 ^ (n+1)) % 2 = 0 := by
        rw [show 10 = 5 * 2 by rfl]
        rw [mul_pow, Nat.mul_mod, Nat.pow_mod]
        simp
      rw [←Nat.even_iff] at h42
      have h43 : Odd 1 := Nat.odd_iff.mpr rfl
      have h44 : 1 ≤ 10 ^ 2 ^ (n+1) := Nat.one_le_pow' _ _
      have h45 : Odd (10 ^ 2 ^ (n + 1) - 1) := Nat.Even.sub_odd h44 h42 h43
      have h47 : Even (10 ^ 2 ^ (n + 1) - 1 - b n) := Nat.Odd.sub_odd h45 (h9 n)
      rw [Nat.even_iff] at h47
      rw [Nat.odd_iff] at H1
      simp [H1] at h47
    apply_fun (· + 1) at h12
    rw [←lemma3 h15] at h12
    have h17 : 10 ^ 2 ^ (n + 1) - 1 - b n + 1 = 10 ^ 2 ^ (n + 1) - b n := by lia
    rw [←h17]
    exact h12

  rw [h13] at h8
  rw [h8, solution]

  -- Hence b n has digit sum (9·2^n - 1) + (9·2^(n+1) - 9·2^n + 1) = 9·2^(n+1).
  have h14 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  lia

end Usa1992P1
