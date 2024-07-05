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
  have ⟨a, ha⟩ := Nat.maxPowDiv.pow_dvd 2 m
  refine ⟨Nat.maxPowDiv 2 m, a, ?_⟩
  obtain ⟨k, hk⟩ := even_iff_two_dvd.mp even_m
  have hk0 : 0 < k := by omega
  refine ⟨?_, ?_, ha⟩
  · rw [hk]
    rw [show 2 * k = 2^1 * k from rfl]
    rw [Nat.maxPowDiv.base_pow_mul one_lt_two hk0]
    exact Nat.le_add_left 1 (Nat.maxPowDiv 2 k)
  · by_contra! Ha
    rw [←Nat.even_iff_not_odd] at Ha
    obtain ⟨b, hb⟩ := Ha
    have h3 : 2 ^ (Nat.maxPowDiv 2 m  + 1) ∣ m := by
      use b
      rw [hb] at ha
      rw [pow_succ]
      linarith only [ha]
    have h4 := Nat.maxPowDiv.le_of_dvd one_lt_two h h3
    exact (lt_self_iff_false _).mp (Nat.succ_le_iff.mp h4)

lemma m_mod_2_contradiction (m n A : ℕ)
                            (even_m : Even m)
                            (even_A : Even A)
                            (m_eq_2_mod_4 : m ≡ 2 [MOD 4])
                            (h : 3 * m * A = (m + 3)^n + 1) : False := by
  obtain ⟨a, Ha⟩ := even_A
  obtain ⟨m', Hm'⟩ := even_m
  have towards_contradiction : 0 ≡ 2 [MOD 4] :=
    calc  0 ≡ 3 * m * A [MOD 4] := by
              rw [Ha, Hm', ←Nat.two_mul, ←Nat.two_mul]
              rw [show 3 * (2 * m') * (2 * a) = 4 * (3 * m' * a) by ring]
              change 0 = _ % _
              exact (Nat.mul_mod_right 4 (3 * m' * a)).symm
          _ ≡ (m + 3)^n + 1 [MOD 4] := by rw[h]
          _ ≡ 2 [MOD 4] := by
              have : m + 3 ≡ 1 [MOD 4] := by
                calc  m + 3 ≡ 2 + 3 [MOD 4] :=
                                 Nat.ModEq.add_right 3 m_eq_2_mod_4
                      _ ≡ 1 [MOD 4] := by rfl
              have : (m + 3)^n ≡ 1 [MOD 4] := one_pow_mod_4 this
              rw [show 2 = 1 + 1 by rfl]
              exact Nat.ModEq.add_right 1 this
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

lemma thue
    (a n : ℕ) (hn : 1 < n) :
    ∃ (x y : ℤ), (a : ZMod n) * x + y = 0 ∧ 0 < |x| ∧ x ^ 2 ≤ n ∧ y ^ 2 ≤ n := by
  -- https://services.artofproblemsolving.com/download.php?id=YXR0YWNobWVudHMvMy8yL2QzYjEzOGM0ODE3YzYwZGU4NGFmOTEwZDc0ZGNhODRjOGMyMzZlLnBkZg==&rn=dGh1ZS12NC5wZGY=

  -- let r = ⌊√n⌋, i.e. r is the unique integer for which
  -- r² ≤ n < (r + 1)².
  let r := Nat.sqrt n

  -- The number of pairs (x,y) so that 0 ≤ x,y ≤ r is (r + 1)² which
  -- is greater than n.

  --
  -- Therefore there must be two different pairs (x₁, y₁) and (x₂, y₂)
  -- such that
  --     ax₁ + y₁ = ax₂ + ay₂ (mod n)
  --     i.e.
  --     a(x₁ - x₂) = y₂ - y₁ (mod n)
  --

  let D := Fin (r + 1) × Fin (r + 1)
  let f : D → ZMod n := fun ⟨x,y⟩ ↦ a * (x.val : ZMod n) + (y.val : ZMod n)
  have cardD : Fintype.card D = (r + 1)^2 := by
    unfold_let D
    rw [sq, Fintype.card_prod, Fintype.card_fin]

  have : NeZero n := NeZero.of_gt hn
  have cardZ : Fintype.card (ZMod n) = n := ZMod.card n

  have hDZ : Fintype.card (ZMod n) < Fintype.card D := by
    rw [cardD, cardZ]
    exact Nat.lt_succ_sqrt' n

  obtain ⟨⟨x₁, y₁⟩, ⟨x₂, y₂⟩, hxyn, hxy⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt f hDZ
  dsimp [f] at hxy
  replace hxy : (a : ZMod n) * (↑↑x₁ - ↑↑x₂) + (↑↑y₁ - ↑↑y₂) = 0 :=
    by linear_combination hxy
  use (x₁ : ℤ) - (x₂ : ℤ)
  use (y₁ : ℤ) - (y₂ : ℤ)

  have hx1 : ((x₁ : ℕ): ZMod n) = (((x₁ : ℕ): ℤ) : ZMod n)  := by
      norm_cast
  have hx2 : ((x₂ : ℕ): ZMod n) = (((x₂ : ℕ): ℤ) : ZMod n)  := by
      norm_cast

  have hx3 : (((x₁ : ℕ): ℤ) : ZMod n) - (((x₂ : ℕ): ℤ) : ZMod n) =
            (((((x₁ : ℕ): ℤ) -((x₂ : ℕ): ℤ)) : ℤ) : ZMod n) := by
    norm_cast

  have hy1 : ((y₁ : ℕ): ZMod n) = (((y₁ : ℕ): ℤ) : ZMod n)  := by
      norm_cast
  have hy2 : ((y₂ : ℕ): ZMod n) = (((y₂ : ℕ): ℤ) : ZMod n)  := by
      norm_cast
  have hy3 : (((y₁ : ℕ): ℤ) : ZMod n) - (((y₂ : ℕ): ℤ) : ZMod n) =
            (((((y₁ : ℕ): ℤ) -((y₂ : ℕ): ℤ)) : ℤ) : ZMod n) := by
    norm_cast

  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hx1, hx2, hx3, hy1, hy2, hy3] at hxy
    rw [hxy]

  · by_contra! H
    replace H : |((x₁:ℕ):ℤ) - ↑↑x₂| = 0 := by
      have : (0 : ℤ) ≤ |((x₁:ℕ):ℤ) - ↑↑x₂| := abs_nonneg (↑↑x₁ - ↑↑x₂)
      exact (Int.le_antisymm this H).symm
    rw [abs_eq_zero] at H
    replace H : ((x₁:ℕ):ℤ) = ↑↑x₂ := Int.eq_of_sub_eq_zero H
    replace H : x₁.val = x₂.val := Int.ofNat_inj.mp H
    replace H : x₁ = x₂ := Fin.eq_of_val_eq H
    rw [H, sub_self, mul_zero, zero_add] at hxy
    have h4 : ((y₁:ℕ): ZMod n) = ↑↑y₂ := by linear_combination hxy
    rw [ZMod.natCast_eq_natCast_iff'] at h4
    have p1 := y₁.prop
    have p2 := y₂.prop
    have : r + 1 ≤ n := by
      have h31 := Nat.sqrt_lt_self hn
      omega
    have h10 : y₁.val < n := by omega
    have h11 : y₂.val < n := by omega
    rw [Nat.mod_eq_of_lt h10, Nat.mod_eq_of_lt h11] at h4
    have h12 : y₁ = y₂ := Fin.eq_of_val_eq h4
    rw [H,h12] at hxyn
    simp at hxyn
  · have hx₁ : x₁.val < r + 1 := x₁.prop
    have hx₂ : x₂.val < r + 1 := x₂.prop
    have hr1 : r^2 ≤ n := Nat.sqrt_le' n
    nlinarith only [hx₁, hx₂, hr1]
  · have hy₁ : y₁.val < r + 1 := y₁.prop
    have hy₂ : y₂.val < r + 1 := y₂.prop
    have hr1 : r^2 ≤ n := Nat.sqrt_le' n
    nlinarith only [hy₁, hy₂, hr1]

/--
In this version of Thue's lemma, we get an `x` that is nonzero and
a `y` that might be zero. If we wanted to guarantee that `y` is nonzero,
we would need an extra hypothesis `Nat.Coprime a n`.
-/
lemma Thue's_lemma
    (a n : ℕ)
    (hn : 1 < n) :
    ∃ (x y : ℤ),
      a * x + y ≡ 0 [ZMOD n] ∧
      0 < |x| ∧
      x ^ 2 ≤ n ∧
      y ^ 2 ≤ n := by
  obtain ⟨x, y, hxay, hx, hx1, hy1⟩ := thue a n hn
  refine ⟨x, y, ?_, hx, hx1, hy1⟩
  have h1 : (a : ZMod n) * (x : ZMod n) + (y : ZMod n) =
            ((((a : ℤ) * x + y):ℤ) : ZMod n) := by norm_cast
  have h2 : ((0:ℤ):ZMod n) = 0 := by norm_cast
  rw [h1, ←h2] at hxay
  exact (ZMod.intCast_eq_intCast_iff (a * x + y) 0 n).mp hxay

example (a b n : ℕ) (ha : a < n + 1) (hb : b < n + 1) : ((a : ℤ) - (b : ℤ))^2 ≤ n^2 := by
  nlinarith

lemma mod_z_of_mod_n {a b m : ℕ} (h : a ≡ b [MOD m]) : a ≡ b [ZMOD m] := by
  dsimp [Int.ModEq]
  rw[show a % m = @Nat.cast ℤ _ (a % m) by norm_num]
  rw[h]
  norm_num

lemma square_contra_mod_3 {y : ℤ} (h: y ^ 2 ≡ 2 [ZMOD 3]) : False := by
  rw [show 3 = ((3:ℕ):ℤ) by rfl] at h
  rw [← ZMod.intCast_eq_intCast_iff] at h
  rw [show (((y^2):ℤ): ZMod 3) = (y : ZMod 3)^2 by norm_cast] at h
  obtain ⟨z, hz⟩ : ∃ z : ZMod 3, z = y := exists_eq
  fin_cases z <;> rw [← hz] at h <;> simp_arith at h

lemma square_mod_4_zmod (x : ZMod 4) : x ^ 2 = 1 ∨ x ^ 2 = 0 := by
  fin_cases x <;> simp_arith

lemma square_mod_3_zmod_0 : ∀ {x : ZMod 3} (_ : x ^ 2 = 0), x = 0 := by
  decide

lemma leaf_contradiction {x y m₁ : ℤ} (h: 3 * x ^ 2 + y ^ 2 = m₁) (h2 : m₁ - 5 ≡ 0 [ZMOD 6]) : False := by
  obtain ⟨c, hc⟩ := Int.modEq_zero_iff_dvd.mp h2
  have expr_m₁_mod_6 : ↑m₁ = 6 * c + 5 := by omega
  rw [expr_m₁_mod_6] at h
  ring_nf at h
  have := calc y ^ 2 ≡ x ^ 2 * 3 + y ^ 2 [ZMOD 3] := by
                      nth_rw 1 [show y ^ 2 = 0 + y ^ 2 by ring]
                      refine Int.ModEq.add_right _ ?_
                      simp [Int.ModEq]
        _ ≡ (5 + c * 6) [ZMOD 3] := by rw[h]
        _ ≡ 2 [ZMOD 3] := by
          have zmod : 5 + (c : ZMod 3) * 6 = 2 := by
            reduce_mod_char
          have : (3 : ℤ) = (3 : ℕ) := by rw [Nat.cast_ofNat]
          rw [this]
          rw [← ZMod.intCast_eq_intCast_iff]
          rw [Int.cast_ofNat]
          rw [← zmod]
          norm_cast
  exact square_contra_mod_3 this

snip end

problem bulgaria1998_p11
    (m n A : ℕ)
    (h : 3 * m * A = (m + 3)^n + 1) : Odd A := by
  -- Follows the second solution in _Mathematical Olympiads 1998-1999_
  -- (edited by Titu Andreescu and Zuming Feng)

  have ⟨⟨k, Hk⟩, m_eq_2_mod_3⟩ : Odd n ∧ m ≡ 2 [MOD 3] := n_odd_and_m_eq_2_mod_3 m n A h
  by_contra even_A
  rw [←Nat.even_iff_not_odd] at even_A
  have zero_lt_m : 0 < m := by
    by_contra m_eq_0
    replace m_eq_0 := not_one_le_k m_eq_0
    rw [m_eq_0] at h
    ring_nf at h
    have : 1 + 3 ^ n > 0 := by positivity
    rw [← h] at this
    contradiction
  have zero_lt_n : 0 < n := by omega
  have even_m : Even m := by
    by_contra odd_m
    have odd_m := Nat.odd_iff_not_even.mpr odd_m
    obtain ⟨a, Ha⟩ := odd_m
    have : m % 2 = 1 % 2 := by
      simp only [Ha, Nat.add_mod, Nat.mul_mod_right, Nat.mod_succ, zero_add]

    have towards_contradiction : 0 ≡ 1 [MOD 2] := by
      calc  0 ≡ 3 * m * A [MOD 2] := by
                change _ % _ = _ % _
                obtain ⟨a, Ha⟩ := even_A
                rw [Ha, ←Nat.two_mul]
                simp [Nat.mul_mod]
            _ ≡ (m + 3)^n + 1 [MOD 2] := by rw[h]
            _ ≡ 1 [MOD 2] := by
                nth_rw 2 [show 1 = 0 + 1 by rfl]
                refine Nat.ModEq.add ?_ rfl
                have : m + 3 ≡ 0 [MOD 2] := by
                  calc  m + 3 ≡ 1 + 1 [MOD 2] := by
                                exact Nat.ModEq.add this rfl
                        _ ≡ 0 [MOD 2] := by rfl
                exact zero_pow_mod_2 zero_lt_n this
    contradiction

  obtain ⟨l, m₁, ⟨one_le_l, odd_m₁, m_factorisation⟩⟩ := two_n_and_rest_factorisation m even_m zero_lt_m
  by_cases l_eq_one : (l = 1)
  · rw [l_eq_one] at m_factorisation
    ring_nf at m_factorisation
    have : m₁ ≡ 1 [MOD 4] ∨ m₁ ≡ 3 [MOD 4] := by
      obtain ⟨a, rfl⟩ := odd_m₁
      obtain ⟨b, rfl⟩ | ⟨b, rfl⟩ := Nat.even_or_odd a
      · left
        dsimp [Nat.ModEq]
        ring_nf
        simp
      · right
        dsimp [Nat.ModEq]
        ring_nf
        simp
    have m_eq_2_mod_4 : m ≡ 2 [MOD 4] := by
      rw [m_factorisation]
      obtain left | right := this
      · nth_rw 2 [show 2 = 1 * 2 by rfl]
        exact Nat.ModEq.mul_right _ left
      · calc m₁ * 2 ≡ 3 * 2 [MOD 4] := Nat.ModEq.mul right rfl
          _ ≡ 2 [MOD 4] := rfl
    exact m_mod_2_contradiction m n A even_m even_A m_eq_2_mod_4 h
  · have eq_2 : 0 ≡ 3^n + 1 [MOD m] := by
      calc  0 ≡ m * (3 * A) [MOD m] := by
                rw[show 0 = 0 * (3 * A) by ring]
                refine Nat.ModEq.mul_right _ ?_
                simp [Nat.ModEq]
            _ ≡ 3 * m * A [MOD m] := by rw[show m * (3 * A) = 3 * m * A by ring]
            _ ≡ (m + 3)^n + 1 [MOD m] := by rw[h]
            _ ≡ 3^n + 1 [MOD m] := by
                refine Nat.ModEq.add_right _ ?_
                exact m_add_3_pow_n_mod_m n m

    have l_eq_2 : l = 2 := by
      have two_le_l : 2 ≤ l := by omega
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
          rw[Hk]
          rw[show 3 ^ (2 * k + 1) = 3^(2 * k) * 3 by ring]
          rw[show 3 ^ (2 * k) = (3 ^ 2) ^ k by exact pow_mul 3 2 k]
          rw[show (3 ^ 2) = 9 by ring]
          have : 9 ^ k ≡ 1 [MOD 8] := by
            have : 9 ≡ 1 [MOD 8] := by
              dsimp[Nat.ModEq]
            exact one_pow_mod_8 this
          rw[show 4 = 3 + 1 by rfl]
          refine Nat.ModEq.add_right _ ?_
          rw[show 3 = 1 * 3 by rfl]
          rw[show 9 ^ k * (1 * 3) = 9 ^ k * 3 by rfl]
          exact Nat.ModEq.mul_right _ this
        exfalso
        exact too_good_to_be_true n l (show 3 ≤ l by exact left) two_pow_l_divides_expresion expression_eq_4_mod_8
      · exact right.symm
    have m_eq_4_m₁ : m = 4 * m₁ := by
      rw[l_eq_2] at m_factorisation
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
        exact Nat.ModEq.mul rfl rfl
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
          refine Nat.ModEq.add_right _ ?_
          simp[Nat.ModEq]
        have step_1: m₁ * 2 ≡ 2 * 2 [MOD 3 * 2] := Nat.ModEq.mul_right' 2 m₁_eq_2_mod_3
        have step_2: m₁ * 3 ≡ 1 * 3 [MOD 2 * 3] := Nat.ModEq.mul_right' 3 this
        change m₁ * 2 + m₁ ≡ 2 * 2 + 5 [MOD 2 * 3] at step_2
        exact Nat.ModEq.add_left_cancel step_1 step_2
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

    have hn1 : 1 < m₁ := by
      change _ % _ = _ % _ at m₁_eq_2_mod_3
      have h40 := Nat.div_add_mod m₁ 3
      rw [m₁_eq_2_mod_3] at h40
      omega
    obtain ⟨x, y, x_y_props⟩ := Thue's_lemma a m₁ hn1
    clear hn1
    obtain ⟨mod_expression, x_lower, x_higher, y_higher⟩ := x_y_props

    have lifted_m₁_result := mod_z_of_mod_n (Nat.modEq_zero_iff_dvd.mpr m₁_divides_for_thues_lemma)
    norm_num at lifted_m₁_result

    have step_2 : a * x ≡ -y [ZMOD m₁] := by
      rw [show -y = 0 - y by ring]
      rw [show a * x = a * x + y - y by ring]
      exact Int.ModEq.sub_right _ mod_expression

    have step_3 : a ^ 2 * x ^ 2 ≡ y ^ 2 [ZMOD m₁] := by
      rw [show a ^ 2 * x ^ 2 = (a * x) * (a * x) by ring]
      rw [show y ^ 2 = (-y) * (-y) by ring]
      exact Int.ModEq.mul step_2 step_2

    have step_4: (-3) * x ^ 2 ≡ y ^ 2 [ZMOD m₁] := by
      have step_1 : a ^ 2 ≡ -3 [ZMOD m₁] :=
        Int.ModEq.add_right_cancel' 3 lifted_m₁_result
      trans a ^ 2 * x ^ 2
      · exact Int.ModEq.mul (step_1.symm) rfl
      · exact step_3

    have expression : 3 * x ^ 2 + y ^ 2 ≡ 0 [ZMOD m₁] := by
      have : ((-3) * x ^ 2) + (3 * x ^ 2)  ≡ (y ^ 2) + (3 * x ^ 2) [ZMOD m₁] :=
        Int.ModEq.add_right _ step_4
      rw [show (-3) * x ^ 2 + (3 * x ^ 2) = 0 by ring] at this
      rw [show y ^ 2 + 3 * x ^ 2 = 3 * x ^ 2 + y ^ 2 by ring] at this
      exact this.symm

    obtain ⟨s, Hs⟩ := Int.modEq_zero_iff_dvd.mp expression
    rw [m_eq_4_m₁] at zero_lt_m
    have zero_lt_m₁ : 0 < @Nat.cast ℤ _ m₁ := by omega

    have upper_bound_s : s ≤ 4 := by
      have upper_bound_expression: 3 * x ^ 2 + y ^ 2 ≤ 4 * m₁ := by omega
      rw [Hs] at upper_bound_expression
      rw [show m₁ * s = s * m₁ by ring] at upper_bound_expression
      exact le_of_mul_le_mul_right upper_bound_expression zero_lt_m₁

    have lower_bound_expression : 0 < 3 * x ^ 2 + y ^ 2 := by
      have h1 : 0 < 3 * x ^ 2 := by rw [←sq_abs]; positivity
      exact Int.add_pos_of_pos_of_nonneg h1 (sq_nonneg y)
    rw[Hs] at lower_bound_expression

    rw[show (0 : ℤ) = m₁ * 0 by ring] at lower_bound_expression
    have lower_bound_s : 0 < s := by
      exact lt_of_mul_lt_mul_of_nonneg_left lower_bound_expression zero_lt_m₁.le

    have m₁_sub_5_mod_6 : ↑m₁ - 5 ≡ 0 [ZMOD 6] := by
      exact Int.ModEq.sub (mod_z_of_mod_n m₁_eq_5_mod_6) rfl

    interval_cases s
    · -- s = 1
      rw[show (m₁ : ℤ) * 1 = m₁ by ring] at Hs
      exact leaf_contradiction Hs m₁_sub_5_mod_6

    · -- s = 2
      have := Int.modEq_zero_iff_dvd.mp m₁_sub_5_mod_6
      dsimp[Dvd.dvd] at this
      obtain ⟨c, this⟩ := this
      have expr_m₁_mod_6 : ↑m₁ = 6 * c + 5 := sub_eq_iff_eq_add.mp this
      rw[expr_m₁_mod_6] at Hs
      ring_nf at Hs
      have expression_mod_4 : ((x : (ZMod 4)) ^ 2 * 3 + y ^ 2) = ((10 + c * 12) : (ZMod 4)) := by
        norm_cast
        rw[Hs]
      reduce_mod_char at expression_mod_4
      obtain left_x | right_x := square_mod_4_zmod x
      · rw[left_x] at expression_mod_4
        obtain left_y | right_y := square_mod_4_zmod y
        · rw[left_y] at expression_mod_4
          simp_arith[left_y] at expression_mod_4
        · rw[right_y] at expression_mod_4
          simp_arith at expression_mod_4
      · rw[right_x] at expression_mod_4
        obtain left_y | right_y := square_mod_4_zmod y
        · rw[left_y] at expression_mod_4
          simp_arith at expression_mod_4
        · rw[right_y] at expression_mod_4
          simp_arith at expression_mod_4
    · -- s = 3
      have := Int.modEq_zero_iff_dvd.mp m₁_sub_5_mod_6
      dsimp[Dvd.dvd] at this
      obtain ⟨c, this⟩ := this
      have expr_m₁_mod_6 : ↑m₁ = 6 * c + 5 := by linarith
      rw[expr_m₁_mod_6] at Hs
      ring_nf at Hs
      have expression_mod_3 :
          ((x : (ZMod 3)) ^ 2 * 3 + y ^ 2) = ((15 + c * 18) : (ZMod 3)) := by
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

    · -- s = 4
      have : y^2 < m₁ := by
        by_contra! H
        have h1 : y^2 = m₁ := (Int.le_antisymm H y_higher).symm
        rw [←sq_abs, Int.abs_eq_natAbs] at h1
        norm_cast at h1
        obtain ⟨yy, hyy⟩ : ∃ yy, yy = y.natAbs := exists_eq
        rw [←hyy] at h1
        rw [←h1] at m₁_eq_2_mod_3
        mod_cases Hyy : yy % 3 <;>
           change _ % _ = _ % _ at Hyy m₁_eq_2_mod_3 <;>
           simp [Nat.pow_mod, Hyy] at m₁_eq_2_mod_3
      omega
