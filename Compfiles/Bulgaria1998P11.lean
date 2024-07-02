/-
Copyright (c) 2023 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw, Adam Kurkiewicz
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
Bulgarian Mathematical Olympiad 1998, Problem 11

Let m,n be natural numbers such that

   A = ((m + 3)ⁿ + 1) / (3m)

is an integer. Prove that A is odd.
-/

namespace Bulgaria1998P11

snip begin

lemma even_of_add {a b : ℕ} : Even a → Even (b + a) → Even (b) := by
  intro even_a even_b_add_a
  contrapose! even_b_add_a
  rw [←Nat.odd_iff_not_even] at *
  exact Even.odd_add even_a even_b_add_a

lemma mod_3_add_3_under_exponent (m n : ℕ) : ((m + 3) ^ n) ≡ (m ^ n) [MOD 3] := by
  change (m + 3)^n % 3 = m ^ n % 3
  simp [Nat.pow_mod, Nat.add_mod]

lemma zero_pow_mod_3 {m n : ℕ} (h1 : n > 0) (h2 : m ≡ 0 [MOD 3]) : m ^ n ≡ 0 [MOD 3]:= by
  change _ % 3 = 0 at h2 ⊢
  rw [←Nat.dvd_iff_mod_eq_zero] at h2 ⊢
  exact Dvd.dvd.pow h2 (Nat.not_eq_zero_of_lt h1)

lemma zero_pow_mod_2 {m n : ℕ} (h1 : n > 0) (h2 : m ≡ 0 [MOD 2]) : m ^ n ≡ 0 [MOD 2]:= by
  change _ % 2 = 0 at h2 ⊢
  rw [←Nat.dvd_iff_mod_eq_zero] at h2 ⊢
  exact Dvd.dvd.pow h2 (Nat.not_eq_zero_of_lt h1)

lemma one_pow_mod_3 {m n : ℕ} (h2 : m ≡ 1 [MOD 3]) : m ^ n ≡ 1 [MOD 3]:= by
  change _ % _ = 1 at h2 ⊢
  simp [Nat.pow_mod, h2]

lemma one_pow_mod_4 {m n : ℕ} (h2 : m ≡ 1 [MOD 4]) : m ^ n ≡ 1 [MOD 4]:= by
  change _ % _ = 1 at h2 ⊢
  simp [Nat.pow_mod, h2]

lemma one_pow_mod_8 {m n : ℕ} (h2 : m ≡ 1 [MOD 8]) : m ^ n ≡ 1 [MOD 8]:= by
  change _ % _ = 1 at h2 ⊢
  simp [Nat.pow_mod, h2]

lemma two_even_pow_mod_3 {m n : ℕ} (h1 : Even n) (h2 : m ≡ 2 [MOD 3]) : m ^ n ≡ 1 [MOD 3] := by
  change _ % _ = _ at h2 ⊢
  obtain ⟨k, hk⟩ := h1
  simp_arith [Nat.pow_mod, h2, hk, pow_mul]

theorem n_odd_and_m_eq_2_mod_3 (m n A : ℕ) (h : 3 * m * A = (m + 3)^n + 1) : Odd n ∧ m ≡ 2 [MOD 3] := by
  by_cases n_gt_zero : n > 0
  · have h_mod_3 : 0 ≡ (m ^ n + 1) [MOD 3] := by
      calc 0 ≡ 3 * (m * A) [MOD 3] := (Nat.mul_mod_right 3 (m * A)).symm
      _ ≡ (3 * m * A) [MOD 3] := by rw[show 3 * (m * A) = (3 * m * A) by ring]
      _ ≡ ((m + 3) ^ n + 1) [MOD 3] := by rw[h]
      _ ≡ (m ^ n + 1) [MOD 3] := Nat.ModEq.add (mod_3_add_3_under_exponent m n) rfl
    mod_cases mod_case : m % 3
    · have towards_contradiction : 0 ≡ 1 [MOD 3] := by
        calc 0 ≡ m ^ n + 1 [MOD 3] := h_mod_3
        _ ≡ 0 + 1 [MOD 3] := Nat.ModEq.add (zero_pow_mod_3 n_gt_zero mod_case) rfl
        _ ≡ 1 [MOD 3] := by rfl
      contradiction
    · have towards_contradiction : 0 ≡ 2 [MOD 3] := by
        rw[show 2 = 1 + 1 by ring]
        calc 0 ≡ m ^ n + 1 [MOD 3] := h_mod_3
        _ ≡ 1 + 1 [MOD 3] := Nat.ModEq.add (one_pow_mod_3 mod_case) rfl
      contradiction
    · by_cases n_even : Even n
      · have towards_contradiction : 0 ≡ 2 [MOD 3] := by
          calc 0 ≡ m ^ n + 1 [MOD 3] := h_mod_3
          _ ≡ 1 + 1 [MOD 3] := Nat.ModEq.add (two_even_pow_mod_3 n_even mod_case) rfl
          _ ≡ 2 [MOD 3] := by rfl
        contradiction
      · constructor
        · apply (@Nat.odd_iff_not_even n).mpr
          exact n_even
        · exact mod_case
  · rw [Nat.eq_zero_of_not_pos n_gt_zero] at h
    simp at h
    have towards_contradiction : 3 ∣ 2 := by
      use m * A
      rw[← h]
      ring
    contradiction

lemma mul_right {a b : ℕ} (c : ℕ) (H : a = b) : (a * c = b * c) := by
  rw[H]

lemma not_one_le_k {k : ℕ} (h : ¬1 ≤ k) : k = 0 := by
  simp_all only [not_le, Nat.lt_one_iff]

lemma two_le_pow_two (l : ℕ) : 2 ≤ 2 ^ (l + 1) := by
  rw [pow_succ]
  suffices 1 ≤ 2 ^ l from Nat.le_mul_of_pos_left 2 this
  exact Nat.one_le_two_pow

lemma two_n_and_rest_factorisation (m : ℕ) (even_m : Even m) (h: 0 < m) : ∃ (l : ℕ) (m₁ : ℕ), 1 ≤ l ∧ Odd m₁ ∧ m = 2 ^ l * m₁ := by
  match m with
  | 0 =>
    contradiction
  | 1 =>
    contradiction
  | m + 2 =>
    have even_m2 := even_m
    obtain ⟨m', m'H⟩ := even_m
    have m_m'_relationship : m = 2 * m' - 2 := by
      rw[show 2 * m' = m' + m' by ring]
      rw[← m'H]
      rw[Nat.add_sub_self_right m 2]
    have one_le_m' : 1 ≤ m' := by
      subst m_m'_relationship
      simp_all only [pos_add_self_iff, even_add_self]
      exact h
    have m'_m_relationship : m' = m /2 + 1 := by
      rw[m_m'_relationship]
      rw[← Nat.mul_sub_left_distrib 2 m' 1]
      field_simp
    have zero_lt_m': 0 < m' := by omega
    by_cases m'_even : Even m'
    · have IH := two_n_and_rest_factorisation m' m'_even zero_lt_m'
      obtain ⟨l, k, lower_level⟩ := IH
      rw[m'_m_relationship] at lower_level
      use (l + 1)
      use k
      constructor
      · exact le_add_left (Nat.le_refl 1)
      · constructor
        · exact lower_level.right.left
        · obtain ⟨_, ⟨k_odd: Odd k, lower_level_statement : m / 2 + 1 = 2 ^ l * k ⟩⟩ := lower_level
          have two_le_k : 2 ≤ 2 ^ (l + 1) * k := by
            have one_le_k : 1 ≤ k := by
              by_contra k_zero
              have k_zero : k = 0 := not_one_le_k k_zero
              have even_k : Even 0 := even_zero
              rw[← k_zero] at even_k
              exact (Nat.even_iff_not_odd.mp even_k) k_odd
            have two_le_expr : 2 ≤ 2 ^ (l + 1) := two_le_pow_two l
            exact Nat.mul_le_mul two_le_expr one_le_k
          have lower_level_statement_2 : (m / 2 + 1) * 2 = (2 ^ l * k) * 2 := mul_right 2 lower_level_statement
          calc  m + 2 = (2 * m' - 2) + 2 := by rw[m_m'_relationship]
                _ = (m' * 2 - 2) + 2 := by ring_nf
                _ = ((m / 2 + 1) * 2 - 2) + 2 := by rw[m'_m_relationship]
                _ = ((2 ^ l * k) * 2 - 2) + 2 := by rw[lower_level_statement_2]
                _ = (2 ^ (l + 1) * k - 2) + 2 := by ring_nf
                _ = 2 ^ (l + 1) * k := @Nat.sub_add_cancel (2 ^ (l + 1) * k) 2 two_le_k
    · use 1
      use m'
      constructor
      · exact Nat.le.refl
      · constructor
        · exact Nat.odd_iff_not_even.mpr m'_even
        · rw[m'H]
          ring

lemma m_mod_2_contradiction (m n A : ℕ)
                            (even_m : Even m)
                            (even_A : Even A)
                            (m_eq_2_mod_4 : m ≡ 2 [MOD 4])
                            (h : 3 * m * A = (m + 3)^n + 1) : False := by
  obtain ⟨a, Ha⟩ := even_A
  obtain ⟨m', Hm'⟩ := even_m
  have towards_contradiction : 0 ≡ 2 [MOD 4] :=
    calc  0 ≡ 3 * m * A [MOD 4] := by
              rw[Ha]
              rw[show a + a = 2 * a by ring]
              rw[Hm']
              rw[show m' + m' = 2 * m' by ring]
              rw[show 3 * (2 * m') * (2 * a) = 4 * (3 * m' * a) by ring]
              rw[show 0 = 0 * (3 * m' * a) by ring]
              apply Nat.ModEq.mul
              rfl
              rfl
          _ ≡ (m + 3)^n + 1 [MOD 4] := by rw[h]
          _ ≡ 2 [MOD 4] := by
              have : m + 3 ≡ 1 [MOD 4] := by
                calc  m + 3 ≡ 2 + 3 [MOD 4] := by
                        apply Nat.ModEq.add
                        exact m_eq_2_mod_4
                        rfl
                      _ ≡ 1 [MOD 4] := by rfl
              have : (m + 3)^n ≡ 1 [MOD 4] := one_pow_mod_4 this
              rw [show 2 = 1 + 1 by rfl]
              apply Nat.ModEq.add
              exact this
              rfl
  contradiction

lemma m_add_3_pow_n_mod_m (n m : ℕ) : (m + 3)^n ≡ 3^n [MOD m] := by
  simp [Nat.ModEq, Nat.pow_mod, Nat.add_mod]

lemma too_good_to_be_true (n l : ℕ)
                          (three_le_l : 3 ≤ l)
                          (two_pow_l_divides_expresion : 2^l ∣ (3^n + 1))
                          (expression_eq_4_mod_8 : 3^n + 1 ≡ 4 [MOD 8]) : False := by
  have : 8 ∣ 3 ^ n + 1 := by
    obtain ⟨a, Ha⟩ := two_pow_l_divides_expresion
    obtain ⟨b, Hb⟩ := Nat.exists_eq_add_of_le' three_le_l
    rw[Hb] at Ha
    dsimp [Dvd.dvd]
    use 2 ^ b * a
    rw[Ha]
    ring
  obtain ⟨a, Ha⟩ := this
  rw [Ha] at expression_eq_4_mod_8
  dsimp[Nat.ModEq] at expression_eq_4_mod_8
  simp at expression_eq_4_mod_8

lemma Thue's_lemma (a m : ℤ) : ∃ (x y : ℤ),  a * x + y ≡ 0 [ZMOD m] ∧ 0 < x ^ 2 ∧ x ^ 2 < m ∧ y ^ 2 ≤ m :=
  sorry

lemma mod_z_of_mod_n {a b m : ℕ} (h : a ≡ b [MOD m]) : a ≡ b [ZMOD m] := by
  dsimp [Int.ModEq]
  rw[show a % m = @Nat.cast ℤ _ (a % m) by norm_num]
  rw[h]
  norm_num


lemma square_contra_mod_3 {y : ℤ} (h: y ^ 2 ≡ 2 [ZMOD 3]) : False := by
  rw [show y ^ 2 = y * y by ring] at h
  mod_cases y_mod_3 : y % 3
  · have : y * y ≡ 0 * 0 [ZMOD 3]:= by
      apply Int.ModEq.mul
      exact y_mod_3
      exact y_mod_3
    rw[show (0 : ℤ) * 0 = 0 by norm_num] at this
    have := Int.ModEq.trans h.symm this
    contradiction
  · have : y * y ≡ 1 * 1 [ZMOD 3]:= by
      apply Int.ModEq.mul
      exact y_mod_3
      exact y_mod_3
    rw[show (1 : ℤ) * 1 = 1 by norm_num] at this
    have := Int.ModEq.trans h.symm this
    contradiction
  · have : y * y ≡ 2 * 2 [ZMOD 3]:= by
      apply Int.ModEq.mul
      exact y_mod_3
      exact y_mod_3
    have := Int.ModEq.trans h.symm this
    contradiction

lemma square_mod_4 {x : ℤ} : x ^ 2 ≡ 1 [ZMOD 4] ∨ x ^ 2 ≡ 0 [ZMOD 4] := by
  rw[show x ^ 2 = x * x by ring]
  mod_cases x_mod_4 : x % 4
  · right
    rw[show (0 : ℤ) = 0 * 0 by rfl]
    apply Int.ModEq.mul
    exact x_mod_4
    exact x_mod_4
  · left
    rw[show (1 : ℤ) = 1 * 1 by rfl]
    apply Int.ModEq.mul
    exact x_mod_4
    exact x_mod_4
  · right
    calc  x * x ≡ 2 * 2 [ZMOD 4] := by
                  apply Int.ModEq.mul
                  exact x_mod_4
                  exact x_mod_4
          _ ≡ 0 [ZMOD 4]:= by rfl
  · left
    calc  x * x ≡ 3 * 3 [ZMOD 4] := by
                  apply Int.ModEq.mul
                  exact x_mod_4
                  exact x_mod_4
          _ ≡ 1 [ZMOD 4]:= by rfl

lemma square_mod_4_zmod (x : ZMod 4) : x ^ 2 = 1 ∨ x ^ 2 = 0 := by
  fin_cases x <;> simp_arith

lemma square_mod_3_zmod_0 : ∀ {x : ZMod 3} (_ : x ^ 2 = 0), x = 0 := by
  decide

lemma leaf_contradiction {x y m₁ : ℤ} (h: 3 * x ^ 2 + y ^ 2 = m₁) (h2 : m₁ - 5 ≡ 0 [ZMOD 6]) : False := by
  have := Int.modEq_zero_iff_dvd.mp h2
  dsimp[Dvd.dvd] at this
  obtain ⟨c, this⟩ := this
  have expr_m₁_mod_6 : ↑m₁ = 6 * c + 5 := by linarith
  rw[expr_m₁_mod_6] at h
  ring_nf at h
  have := calc y ^ 2 ≡ x ^ 2 * 3 + y ^ 2 [ZMOD 3] := by
                      nth_rw 1 [show y ^ 2 = 0 + y ^ 2 by ring]
                      apply Int.ModEq.add
                      dsimp[Int.ModEq]
                      simp
                      rfl
        _ ≡ (5 + c * 6) [ZMOD 3] := by rw[h]
        _ ≡ 2 [ZMOD 3] := by
          have zmod : 5 + (c : ZMod 3) * 6 = 2 := by
            reduce_mod_char
          have : (3 : ℤ) = (3 : ℕ) := by rw [Nat.cast_ofNat]
          rw[this]
          rw[← ZMod.intCast_eq_intCast_iff]
          rw[Int.cast_ofNat]
          rw[← zmod]
          norm_cast
  exact square_contra_mod_3 this

snip end

problem bulgaria1998_p11
    (m n A : ℕ)
    (h : 3 * m * A = (m + 3)^n + 1) : Odd A := by
  have ⟨odd_n, m_eq_2_mod_3⟩ : Odd n ∧ m ≡ 2 [MOD 3] := n_odd_and_m_eq_2_mod_3 m n A h
  by_contra even_A
  have even_A := (@Nat.even_iff_not_odd A).mpr even_A
  have zero_lt_m : 0 < m := by
    by_contra m_eq_0
    have m_eq_0 : m = 0 := by
      simp_all only [not_lt, nonpos_iff_eq_zero]
    rw[m_eq_0] at h
    ring_nf at h
    have : 1 + 3 ^ n > 0 := by positivity
    rw[← h] at this
    contradiction
  have zero_lt_n : 0 < n := by
    by_contra zero_eq_n
    have zero_eq_n : 0 = n := by simp_all only [Nat.odd_iff_not_even, not_lt, nonpos_iff_eq_zero]
    rw[← zero_eq_n] at h
    ring_nf at h
    have : 0 ≡ 2 [MOD 3] := by
      calc 0 ≡ m * A * 3 [MOD 3] := by
                rw[show 0 = 0 * (m * A) by ring]
                rw[show m * A * 3 = 3 * (m * A) by ring]
                apply Nat.ModEq.mul
                rfl
                rfl
            _ ≡ 2 [MOD 3] := by rw[h]
    contradiction
  have even_m : Even m := by
    by_contra odd_m
    have odd_m := Nat.odd_iff_not_even.mpr odd_m
    obtain ⟨a, Ha⟩ := odd_m
    have : m ≡ 1 [MOD 2] := by
      rw[Ha]
      nth_rw 2 [show 1 = 0 * a + 1 by ring]
      apply Nat.ModEq.add
      apply Nat.ModEq.mul
      rfl
      rfl
      rfl
    have towards_contradiction : 0 ≡ 1 [MOD 2] := by
      calc  0 ≡ 3 * m * A [MOD 2] := by
                obtain ⟨a, Ha⟩ := even_A
                rw[Ha]
                rw[show a + a = 2 * a by ring]
                rw[show 3 * m * (2 * a) = 2 * (3 * m * a) by ring]
                rw[show 0 = 0 * (3 * m * a) by ring]
                apply Nat.ModEq.mul
                rfl
                rfl
            _ ≡ (m + 3)^n + 1 [MOD 2] := by rw[h]
            _ ≡ 1 [MOD 2] := by
                nth_rw 2 [show 1 = 0 + 1 by rfl]
                apply Nat.ModEq.add
                have : m + 3 ≡ 0 [MOD 2] := by
                  calc  m + 3 ≡ 1 + 1 [MOD 2] := by
                                apply Nat.ModEq.add
                                exact this
                                rfl
                        _ ≡ 0 [MOD 2] := by
                                ring_nf
                                rfl
                exact zero_pow_mod_2 zero_lt_n this
                rfl
    contradiction

  obtain ⟨l, m₁, ⟨one_le_l, odd_m₁, m_factorisation⟩⟩ := two_n_and_rest_factorisation m even_m zero_lt_m
  by_cases l_eq_one : (l = 1)
  · rw [l_eq_one] at m_factorisation
    ring_nf at m_factorisation
    have : m₁ ≡ 1 [MOD 4] ∨ m₁ ≡ 3 [MOD 4] := by
      obtain ⟨a, aH⟩ := odd_m₁
      obtain even_a | odd_a := Nat.even_or_odd a
      · obtain ⟨b, bH⟩ := even_a
        left
        rw[aH]
        rw[bH]
        dsimp [Nat.ModEq]
        ring_nf
        simp
      · obtain ⟨b, bH⟩ := odd_a
        right
        rw[aH]
        rw[bH]
        dsimp [Nat.ModEq]
        ring_nf
        simp
    have m_eq_2_mod_4 : m ≡ 2 [MOD 4] := by
      obtain left | right := this
      · rw[m_factorisation]
        rw[show 2 = 1 * 2 by rfl]
        apply Nat.ModEq.mul
        exact left
        ring_nf
        rfl
      · rw[m_factorisation]
        calc m₁ * 2 ≡ 3 * 2 [MOD 4] := Nat.ModEq.mul right rfl
          _ ≡ 2 [MOD 4] := rfl
    exact m_mod_2_contradiction m n A even_m even_A m_eq_2_mod_4 h
  · have two_le_l : 2 ≤ l := by
      obtain left | right := LE.le.lt_or_eq one_le_l
      exact left
      exfalso
      apply l_eq_one
      exact right.symm
    have eq_2 : 0 ≡ 3^n + 1 [MOD m] := by
      calc  0 ≡ m * (3 * A) [MOD m] := by
                rw[show 0 = 0 * (3 * A) by ring]
                apply Nat.ModEq.mul
                dsimp [Nat.ModEq]
                simp
                rfl
            _ ≡ 3 * m * A [MOD m] := by rw[show m * (3 * A) = 3 * m * A by ring]
            _ ≡ (m + 3)^n + 1 [MOD m] := by rw[h]
            _ ≡ 3^n + 1 [MOD m] := by
                apply Nat.ModEq.add
                exact m_add_3_pow_n_mod_m n m
                rfl
    have l_eq_2 : l = 2 := by
      obtain left | right := lt_or_eq_of_le two_le_l
      · have two_pow_l_divides_expresion : 2 ^ l ∣ (3^n + 1) := by
          have m_divides_expression : m ∣ (3 ^ n) + 1 := by
            exact (@Nat.modEq_zero_iff_dvd m (3^n + 1)).mp eq_2.symm
          dsimp[Dvd.dvd]
          obtain ⟨a, Ha⟩ := m_divides_expression
          use m₁ * a
          rw[show 2 ^ l * (m₁ * a) = (2 ^ l * m₁) * a by ring]
          rw[← m_factorisation]
          exact Ha
        have expression_eq_4_mod_8 : 3^n + 1 ≡ 4 [MOD 8] := by
          obtain ⟨k, Hk⟩ := odd_n
          rw[Hk]
          rw[show 3 ^ (2 * k + 1) = 3^(2 * k) * 3 by ring]
          rw[show 3 ^ (2 * k) = (3 ^ 2) ^ k by exact pow_mul 3 2 k]
          rw[show (3 ^ 2) = 9 by ring]
          have : 9 ^ k ≡ 1 [MOD 8] := by
            have : 9 ≡ 1 [MOD 8] := by
              dsimp[Nat.ModEq]
            exact one_pow_mod_8 this
          rw[show 4 = 3 + 1 by rfl]
          apply Nat.ModEq.add
          rw[show 3 = 1 * 3 by rfl]
          rw[show 9 ^ k * (1 * 3) = 9 ^ k * 3 by rfl]
          apply Nat.ModEq.mul
          exact this
          rfl
          rfl
        exfalso
        exact too_good_to_be_true n l (show 3 ≤ l by exact left) two_pow_l_divides_expresion expression_eq_4_mod_8
      · exact right.symm

    have m_eq_4_m₁ : m = 4 * m₁ := by
      rw[l_eq_2] at m_factorisation
      ring_nf at m_factorisation
      ring_nf
      exact m_factorisation

    have m₁_divides_expresion : m₁ ∣ (3^n + 1) := by
      have m_divides_expression : m ∣ (3 ^ n) + 1 := by
        exact (@Nat.modEq_zero_iff_dvd m (3^n + 1)).mp eq_2.symm
      dsimp[Dvd.dvd]
      obtain ⟨a, Ha⟩ := m_divides_expression
      use 2 ^ l * a
      rw[show m₁ * (2 ^ l * a) = (2 ^ l * m₁) * a by ring]
      rw[← m_factorisation]
      exact Ha

    have m₁_eq_2_mod_3 : m₁ ≡ 2 [MOD 3] := by
      have step_1 : 4 * m₁ ≡ 2 [MOD 3] := by
        rw[m_eq_4_m₁] at m_eq_2_mod_3
        exact m_eq_2_mod_3
      have step_2 : 4 * m₁ ≡ m₁ [MOD 3] := by
        nth_rw 2 [show m₁ = 1 * m₁ by ring]
        apply Nat.ModEq.mul
        rfl
        rfl
      calc  m₁ ≡ 4 * m₁ [MOD 3] := step_2.symm
            _ ≡ 2 [MOD 3] := step_1
    have m₁_eq_5_mod_6 : m₁ ≡ 5 [MOD 6] := by
      mod_cases m_mod_six : m₁ % 6
      · have step_1: m₁ * 2 ≡ 0 * 2 [MOD 6]:= Nat.ModEq.mul_right 2 m_mod_six
        have step_2: m₁ * 2 ≡ 2 * 2 [MOD 3 * 2] := Nat.ModEq.mul_right' 2 m₁_eq_2_mod_3
        simp at step_1
        simp at step_2
        exfalso
        have := Nat.ModEq.trans step_2.symm step_1
        contradiction
      · have step_1: m₁ * 2 ≡ 1 * 2 [MOD 6]:= Nat.ModEq.mul_right 2 m_mod_six
        have step_2: m₁ * 2 ≡ 2 * 2 [MOD 3 * 2] := Nat.ModEq.mul_right' 2 m₁_eq_2_mod_3
        simp at step_1
        simp at step_2
        exfalso
        have := Nat.ModEq.trans step_2.symm step_1
        contradiction
      · have : m₁ ≡ 1 [MOD 2] := by
          obtain ⟨a, Ha⟩ := odd_m₁
          rw[show 1 = 0 + 1 by norm_num]
          rw[Ha]
          apply Nat.ModEq.add
          dsimp[Nat.ModEq]
          simp
          rfl
        have step_1: m₁ * 2 ≡ 2 * 2 [MOD 3 * 2] := Nat.ModEq.mul_right' 2 m₁_eq_2_mod_3
        have step_2: m₁ * 3 ≡ 1 * 3 [MOD 2 * 3] := Nat.ModEq.mul_right' 3 this
        simp at step_1
        simp at step_2
        have step_3 : m₁ * 3 + 2 * (m₁ * 2) ≡ 3 + 2 * 4 [MOD 6]:= by
          apply Nat.ModEq.add
          nth_rw 2 [show 3 = 1 * 3 by norm_num]
          exact step_2
          apply Nat.ModEq.mul
          rfl
          exact step_1
        ring_nf at step_3
        have : 11 ≡ 5 * 7 [MOD 6] := rfl
        have step_4 : m₁ * 7 ≡ 5 * 7 [MOD 6] := Nat.ModEq.trans step_3 this
        calc  m₁ ≡ m₁ * 7 [MOD 6] := by
                  nth_rw 1 [show m₁ = m₁ * 1 by ring]
                  apply Nat.ModEq.mul
                  rfl
                  rfl
              _ ≡ 5 * 7 [MOD 6] := step_4
              _ ≡ 5 [MOD 6] := by
                  nth_rw 2 [show 5 = 5 * 1 by ring]
                  apply Nat.ModEq.mul
                  rfl
                  rfl
      · have step_1: m₁ * 2 ≡ 3 * 2 [MOD 6]:= Nat.ModEq.mul_right 2 m_mod_six
        have step_2: m₁ * 2 ≡ 2 * 2 [MOD 3 * 2] := Nat.ModEq.mul_right' 2 m₁_eq_2_mod_3
        simp at step_1
        simp at step_2
        exfalso
        have := Nat.ModEq.trans step_2.symm step_1
        contradiction
      · have step_1: m₁ * 2 ≡ 4 * 2 [MOD 6]:= Nat.ModEq.mul_right 2 m_mod_six
        have step_2: m₁ * 2 ≡ 2 * 2 [MOD 3 * 2] := Nat.ModEq.mul_right' 2 m₁_eq_2_mod_3
        simp at step_1
        simp at step_2
        exfalso
        have := Nat.ModEq.trans step_2.symm step_1
        contradiction
      · exact m_mod_six

    obtain ⟨k, Hk⟩ := odd_n
    have exists_a : ∃ (a : ℕ ), a = 3 ^ (k + 1) := by
      use 3 ^ (k + 1)
    obtain ⟨a, Ha⟩ := exists_a
    have m₁_divides_for_thues_lemma : m₁ ∣ a^2 + 3 := by
      apply Nat.modEq_zero_iff_dvd.mp
      have step_1:= Nat.modEq_zero_iff_dvd.mpr m₁_divides_expresion
      rw[Hk] at step_1
      have step_2: 3 * (3 ^ (2 * k + 1) + 1) ≡ 3 * 0 [MOD m₁] := Nat.ModEq.mul_left 3 step_1
      ring_nf at step_2
      rw[show 3 ^ (k * 2) * 9 = 3 ^ ((k + 1) * 2 ) by ring] at step_2
      have step_3 : 3 ^ ((k + 1) * 2) = (3 ^ (k + 1)) ^ (2) :=
        pow_mul 3 (k + 1) 2
      rw[step_3] at step_2
      rw[← Ha] at step_2
      ring_nf
      exact step_2

    obtain ⟨x, y, x_y_props⟩ := Thue's_lemma a m₁
    obtain ⟨mod_expression, x_lower, x_higher, y_higher⟩ := x_y_props

    have lifted_m₁_result := mod_z_of_mod_n (Nat.modEq_zero_iff_dvd.mpr m₁_divides_for_thues_lemma)
    norm_num at lifted_m₁_result

    have step_1 : a ^ 2 ≡ -3 [ZMOD m₁] := by
      rw[show -3 = 0 - 3 by ring]
      rw[show (@Nat.cast ℤ _ a) ^ 2 = ↑a ^ 2 + 3 - 3 by ring]
      apply Int.ModEq.sub
      exact lifted_m₁_result
      rfl

    have step_2 : a * x ≡ -y [ZMOD m₁] := by
      rw[show -y = 0 - y by ring]
      rw[show a * x = a * x + y - y by ring]
      apply Int.ModEq.sub
      exact mod_expression
      rfl

    have step_3 : a ^ 2 * x ^ 2 ≡ y ^ 2 [ZMOD m₁] := by
      rw[show a ^ 2 * x ^ 2 = (a * x) * (a * x) by ring]
      rw[show y ^ 2 = (-y) * (-y) by ring]
      apply Int.ModEq.mul
      exact step_2
      exact step_2

    have step_4: (-3) * x ^ 2 ≡ y ^ 2 [ZMOD m₁] := by
      trans a ^ 2 * x ^ 2
      · exact? says exact Int.ModEq.mul (id (Int.ModEq.symm step_1)) rfl
      · exact? says exact step_3

    have expression : 3 * x ^ 2 + y ^ 2 ≡ 0 [ZMOD m₁] := by
      have : ((-3) * x ^ 2) + (3 * x ^ 2)  ≡ (y ^ 2) + (3 * x ^ 2) [ZMOD m₁] := by
        apply Int.ModEq.add
        exact step_4
        rfl
      rw[show (-3) * x ^ 2 + (3 * x ^ 2) = 0 by ring] at this
      rw[show y ^ 2 + 3 * x ^ 2 = 3 * x ^ 2 + y ^ 2 by ring] at this
      exact this.symm

    have := Int.modEq_zero_iff_dvd.mp expression
    obtain ⟨s, Hs⟩ := this

    have upper_bound_expression: 3 * x ^ 2 + y ^ 2 ≤ 4 * m₁ := by
      linarith
    rw[Hs] at upper_bound_expression
    rw[show m₁ * s = s * m₁ by ring] at upper_bound_expression
    have zero_le_m₁ : 0 ≤ (m₁ : ℤ) := by positivity
    rw[m_eq_4_m₁] at zero_lt_m
    have zero_lt_m₁ : 0 < @Nat.cast ℤ _ m₁ := by linarith

    have upper_bound_s : s ≤ 4 := by
      exact le_of_mul_le_mul_right upper_bound_expression zero_lt_m₁

    have lower_bound_expression : 0 < 3 * x ^ 2 + y ^ 2 := by
      have : 0 < 3 * x ^ 2 := by
        linarith
      have : 0 ≤ y ^ 2 := by positivity
      linarith
    rw[Hs] at lower_bound_expression

    rw[show (0 : ℤ) = m₁ * 0 by ring] at lower_bound_expression
    have lower_bound_s : 0 < s := by
      exact lt_of_mul_lt_mul_of_nonneg_left lower_bound_expression zero_le_m₁

    have := mod_z_of_mod_n m₁_eq_5_mod_6
    have m₁_sub_5_mod_6 : ↑m₁ - 5 ≡ 0 [ZMOD 6] := by
      rw[show (0 : ℤ) = (5 : ℤ) - 5 by ring]
      apply Int.ModEq.sub
      exact this
      rfl

    have := mod_z_of_mod_n m₁_eq_2_mod_3
    have m₁_sub_2_mod_3 : ↑m₁ - 2 ≡ 0 [ZMOD 3] := by
      rw[show (0 : ℤ) = (2 : ℤ) - 2 by ring]
      apply Int.ModEq.sub
      exact this
      rfl

    obtain (left : ((1 : ℤ) = s)) | (right : 1 < s) := LE.le.eq_or_lt (Order.succ_le_of_lt lower_bound_s)
    rw[left.symm] at Hs
    rw[show (m₁ : ℤ) * 1 = m₁ by ring] at Hs
    exact leaf_contradiction Hs m₁_sub_5_mod_6

    obtain (left : ((2 : ℤ) = s)) | (right : 2 < s) := LE.le.eq_or_lt (Order.succ_le_of_lt right)
    rw[left.symm] at Hs
    have := Int.modEq_zero_iff_dvd.mp m₁_sub_5_mod_6
    dsimp[Dvd.dvd] at this
    obtain ⟨c, this⟩ := this
    have expr_m₁_mod_6 : ↑m₁ = 6 * c + 5 := by linarith
    rw[expr_m₁_mod_6] at Hs
    ring_nf at Hs
    have expression_mod_4 : ((x : (ZMod 4)) ^ 2 * 3 + y ^ 2) = ((10 + c * 12) : (ZMod 4)) := by
      norm_cast
      rw[Hs]
    reduce_mod_char at expression_mod_4
    obtain left_x | right_x := square_mod_4_zmod x
    rw[left_x] at expression_mod_4
    obtain left_y | right_y := square_mod_4_zmod y
    rw[left_y] at expression_mod_4
    ring_nf at expression_mod_4
    contradiction
    rw[right_y] at expression_mod_4
    ring_nf at expression_mod_4
    contradiction
    rw[right_x] at expression_mod_4
    obtain left_y | right_y := square_mod_4_zmod y
    rw[left_y] at expression_mod_4
    ring_nf at expression_mod_4
    contradiction
    rw[right_y] at expression_mod_4
    ring_nf at expression_mod_4
    contradiction
    obtain (left : ((3 : ℤ) = s)) | (right : 3 < s) := LE.le.eq_or_lt (Order.succ_le_of_lt right)
    rw[left.symm] at Hs
    have := Int.modEq_zero_iff_dvd.mp m₁_sub_5_mod_6
    dsimp[Dvd.dvd] at this
    obtain ⟨c, this⟩ := this
    have expr_m₁_mod_6 : ↑m₁ = 6 * c + 5 := by linarith
    rw[expr_m₁_mod_6] at Hs
    ring_nf at Hs
    have expression_mod_3 : ((x : (ZMod 3)) ^ 2 * 3 + y ^ 2) = ((15 + c * 18) : (ZMod 3)) := by
      norm_cast
      rw[Hs]
    reduce_mod_char at expression_mod_3
    have : (y : ZMod 3) = 0 := square_mod_3_zmod_0 expression_mod_3
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd y 3).mp this
    dsimp[Dvd.dvd] at this
    obtain⟨y', Hy'⟩ := this
    rw[Hy'] at Hs
    ring_nf at Hs
    rw[show x ^ 2 * 3 + y' ^ 2 * 9 = 3 * (x ^ 2 + 3 * y' ^ 2) by ring] at Hs
    rw[show 15 + c * 18 = 3 * (5 + 6 * c) by ring] at Hs
    have reduced_expression : (x ^ 2 + 3 * y' ^ 2) = (5 + 6 * c) := by
      omega

    rw[show 5 + 6 * c = 6 * c + 5 by ring] at reduced_expression
    rw[← expr_m₁_mod_6] at reduced_expression
    rw[show x ^ 2 + 3 * y' ^ 2 = 3 * y' ^ 2 + x ^ 2 by ring] at reduced_expression
    exact leaf_contradiction reduced_expression m₁_sub_5_mod_6

    obtain (left : ((4 : ℤ) = s)) | (right : 4 < s) := LE.le.eq_or_lt (Order.succ_le_of_lt right)
    rw[left.symm] at Hs
    linarith
    linarith
