/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.Star
public import Mathlib.Data.Nat.Prime.Factorial
public import Mathlib.NumberTheory.Bertrand
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.NumberTheory] }

/-!
# USA Mathematical Olympiad 2024, Problem 1

Find all integers $n \geq 3$ such that the following property holds:
if we list the divisors of $n!$ in increasing order as
$1 = d_1 < d_2 < \cdots < d_k = n!$, then we have
$d_2 - d_1 \leq d_3 - d_2 \leq \cdots \leq d_k - d_{k-1}$.
-/

namespace Usa2024P1

/-- The property required of `n`: writing the divisors of `n !` in increasing
order as `1 = d₁ < d₂ < ⋯ < dₖ = n !`, the consecutive gaps are non-decreasing.
We phrase this using consecutive triples: whenever `a < b < c` are divisors of
`n !` such that no divisor of `n !` lies strictly between `a` and `b`, or strictly
between `b` and `c`, we have `b - a ≤ c - b`.
(Note: we write `Nat.factorial n` instead of `n !` since the `!` notation clashes
with `PiLp.vecNotation` under a full `Mathlib` import.) -/
def Good (n : ℕ) : Prop :=
  ∀ a ∈ (Nat.factorial n).divisors, ∀ b ∈ (Nat.factorial n).divisors,
    ∀ c ∈ (Nat.factorial n).divisors,
    a < b → b < c →
    (∀ d ∈ (Nat.factorial n).divisors, d ≤ a ∨ b ≤ d) →
    (∀ d ∈ (Nat.factorial n).divisors, d ≤ b ∨ c ≤ d) →
    b - a ≤ c - b

determine solution_set : Set ℕ := {3, 4}

snip begin

/-!
## Solution outline

The answer is `n ∈ {3, 4}`, following Evan Chen's write-up
(<https://web.evanchen.cc/exams/USAMO-2024-notes.pdf>).

* `n = 3` has divisors `1, 2, 3, 6` and `n = 4` has divisors
  `1, 2, 3, 4, 6, 8, 12, 24`; both are checked directly.
* `n = 5` fails with the consecutive triple `(15, 20, 24)` of divisors of `5 !`;
  `n = 6` fails with `(90, 120, 144)`.
* Every `n` with `7 ≤ n ≤ 12` fails with the consecutive triple `(12, 14, 15)`
  (there is no divisor of `n !` strictly between `12` and `14` since `13 ∤ n !`).
* For `n ≥ 13`, put `m = ⌊n / 2⌋ ≥ 6`. Both `m² - 1 = (m - 1)(m + 1)` and `m²`
  divide `n !` (each is a product of two distinct positive integers `≤ n`),
  so they are consecutive divisors of `n !` with gap `1`. If the gaps were
  non-decreasing, every gap before them would also have to be `1`, so every
  integer in `[1, m²]` would divide `n !`. But Bertrand's postulate gives a
  prime `p` with `n < p ≤ 2n ≤ m²`, and such a prime cannot divide `n !`.
-/

/-- If `a` and `b` are distinct positive integers with `a, b ≤ n`, then
`a * b ∣ Nat.factorial n`: both occur as distinct factors in
`n ! = ∏ i ∈ Finset.range n, (i + 1)`. -/
lemma mul_dvd_factorial_of_ne {a b n : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b)
    (han : a ≤ n) (hbn : b ≤ n) : a * b ∣ Nat.factorial n := by
  have ha' : a - 1 ∈ Finset.range n := Finset.mem_range.mpr (by omega)
  have hb' : b - 1 ∈ (Finset.range n).erase (a - 1) :=
    Finset.mem_erase.mpr ⟨by omega, Finset.mem_range.mpr (by omega)⟩
  have e1 := Finset.mul_prod_erase _ (fun x => x + 1) ha'
  have e2 := Finset.mul_prod_erase _ (fun x => x + 1) hb'
  rw [Nat.sub_add_cancel ha] at e1
  rw [Nat.sub_add_cancel hb] at e2
  rw [← Finset.prod_range_add_one_eq_factorial, ← e1, ← e2]
  exact ⟨∏ x ∈ ((Finset.range n).erase (a - 1)).erase (b - 1), (x + 1), by ring⟩

/-- The divisors of `3 ! = 6` are `1, 2, 3, 6`, with gaps `1, 1, 3`. -/
lemma good_three : Good 3 := by
  unfold Good
  decide

/-- The divisors of `4 ! = 24` are `1, 2, 3, 4, 6, 8, 12, 24`,
with gaps `1, 1, 1, 2, 2, 4, 12`. -/
lemma good_four : Good 4 := by
  unfold Good
  decide

/-- `n = 5` fails: `15, 20, 24` are consecutive divisors of `5 ! = 120`,
but `20 - 15 = 5 > 4 = 24 - 20`. -/
lemma not_good_five : ¬ Good 5 := by
  intro h
  unfold Good at h
  have key := h 15 (by decide) 20 (by decide) 24 (by decide) (by norm_num) (by norm_num)
    (by decide) (by decide)
  norm_num at key

set_option maxRecDepth 10000 in
/-- `n = 6` fails: `90, 120, 144` are consecutive divisors of `6 ! = 720`,
but `120 - 90 = 30 > 24 = 144 - 120`. -/
lemma not_good_six : ¬ Good 6 := by
  intro h
  unfold Good at h
  have key := h 90 (by decide) 120 (by decide) 144 (by decide) (by norm_num) (by norm_num)
    (by decide) (by decide)
  norm_num at key

/-- Every `n` with `7 ≤ n ≤ 12` fails: `12, 14, 15` are consecutive divisors
of `n !` (there is no divisor strictly between `12` and `14` since `13 ∤ n !`),
but `14 - 12 = 2 > 1 = 15 - 14`. -/
lemma not_good_of_seven_le {n : ℕ} (h7 : 7 ≤ n) (hn12 : n ≤ 12) : ¬ Good n := by
  intro h
  unfold Good at h
  have hfact7 : Nat.factorial 7 ∣ Nat.factorial n := Nat.factorial_dvd_factorial h7
  have hd12 : 12 ∣ Nat.factorial n := (by decide : 12 ∣ Nat.factorial 7).trans hfact7
  have hd14 : 14 ∣ Nat.factorial n := (by decide : 14 ∣ Nat.factorial 7).trans hfact7
  have hd15 : 15 ∣ Nat.factorial n := (by decide : 15 ∣ Nat.factorial 7).trans hfact7
  have hd13 : ¬ 13 ∣ Nat.factorial n := by
    rw [Nat.Prime.dvd_factorial (by norm_num : Nat.Prime 13)]
    omega
  have hmem : ∀ {d : ℕ}, d ∣ Nat.factorial n → d ∈ (Nat.factorial n).divisors :=
    fun hd => Nat.mem_divisors.mpr ⟨hd, Nat.factorial_ne_zero n⟩
  have hsucc1 : ∀ d ∈ (Nat.factorial n).divisors, d ≤ 12 ∨ 14 ≤ d := by
    intro d hd
    rcases le_or_gt d 12 with hle | hgt
    · exact Or.inl hle
    · rcases le_or_gt 14 d with hle2 | hlt2
      · exact Or.inr hle2
      · have hd13' : d = 13 := by omega
        subst hd13'
        exact absurd (Nat.mem_divisors.mp hd).1 hd13
  have hsucc2 : ∀ d ∈ (Nat.factorial n).divisors, d ≤ 14 ∨ 15 ≤ d := fun d _ => by omega
  have key := h 12 (hmem hd12) 14 (hmem hd14) 15 (hmem hd15) (by norm_num) (by norm_num)
    hsucc1 hsucc2
  norm_num at key

/-- Every `n ≥ 13` fails. With `m = ⌊n / 2⌋ ≥ 6`, both `m² - 1` and `m²` divide
`n !`, hence are consecutive divisors of `n !` with gap `1`. A downward induction
using `Good n` then shows that every integer in `[1, m²]` divides `n !`, which
contradicts Bertrand's postulate: there is a prime `p` with `n < p ≤ 2n ≤ m²`. -/
lemma not_good_of_thirteen_le {n : ℕ} (hn : 13 ≤ n) : ¬ Good n := by
  intro hGood
  unfold Good at hGood
  obtain ⟨m, hm2, hm1⟩ : ∃ m, 2 * m ≤ n ∧ n ≤ 2 * m + 1 := ⟨n / 2, by omega⟩
  have hm6 : 6 ≤ m := by omega
  have hmsq : 4 * m + 4 ≤ m ^ 2 := by
    obtain ⟨t, rfl⟩ : ∃ t, m = 6 + t := ⟨m - 6, by omega⟩
    nlinarith [sq_nonneg t]
  have hmem : ∀ {d : ℕ}, d ∣ Nat.factorial n → d ∈ (Nat.factorial n).divisors :=
    fun hd => Nat.mem_divisors.mpr ⟨hd, Nat.factorial_ne_zero n⟩
  -- `m² ∣ n !`, as `m` and `2m` are distinct factors of `n !`.
  have hA : m ^ 2 ∣ Nat.factorial n := by
    have h := mul_dvd_factorial_of_ne (show 0 < m by omega) (show 0 < 2 * m by omega)
      (show m ≠ 2 * m by omega) (show m ≤ n by omega) (show 2 * m ≤ n by omega)
    have e : m * (2 * m) = m ^ 2 * 2 := by ring
    exact (dvd_mul_right (m ^ 2) 2).trans (e ▸ h)
  -- `m² - 1 ∣ n !`, as `m - 1` and `m + 1` are distinct factors of `n !`.
  have hB : m ^ 2 - 1 ∣ Nat.factorial n := by
    have h := mul_dvd_factorial_of_ne (show 0 < m - 1 by omega) (show 0 < m + 1 by omega)
      (show m - 1 ≠ m + 1 by omega) (show m - 1 ≤ n by omega) (show m + 1 ≤ n by omega)
    have e : m ^ 2 - 1 = (m - 1) * (m + 1) := by
      have h2 : m ^ 2 = (m - 1) * (m + 1) + 1 := by
        zify [show (1 : ℕ) ≤ m by omega]
        ring
      omega
    rwa [e]
  -- Bertrand's postulate: a prime `p` with `n < p ≤ 2n ≤ m² - 2`.
  obtain ⟨p, hpprime, hpn, hp2n⟩ := Nat.exists_prime_lt_and_le_two_mul n (by omega)
  have hpp : 0 < p := hpprime.pos
  -- Downward induction: every integer in `[m² - 1 - k, m²]` divides `n !`.
  have key : ∀ k : ℕ, k ≤ m ^ 2 - 2 → ∀ j : ℕ, m ^ 2 - 1 - k ≤ j → j ≤ m ^ 2 →
      j ∣ Nat.factorial n := by
    intro k
    induction k with
    | zero =>
        intro _ j hj1 hj2
        have hcases : j = m ^ 2 - 1 ∨ j = m ^ 2 := by omega
        rcases hcases with rfl | rfl
        · exact hB
        · exact hA
    | succ k ih =>
        intro hk j hj1 hj2
        have ht2 : 2 ≤ m ^ 2 - 1 - k := by omega
        have htD : m ^ 2 - 1 - k ∣ Nat.factorial n := ih (by omega) _ le_rfl (by omega)
        have ht1D : m ^ 2 - 1 - k + 1 ∣ Nat.factorial n :=
          ih (by omega) _ (by omega) (by omega)
        have h1mem : (1 : ℕ) ∈ (Nat.factorial n).divisors := hmem (one_dvd _)
        have hSne : ((Nat.factorial n).divisors.filter (· ≤ m ^ 2 - 1 - k - 1)).Nonempty :=
          ⟨1, Finset.mem_filter.mpr ⟨h1mem, by omega⟩⟩
        set q := ((Nat.factorial n).divisors.filter (· ≤ m ^ 2 - 1 - k - 1)).max' hSne
        have hqmem' : q ∈ (Nat.factorial n).divisors.filter (· ≤ m ^ 2 - 1 - k - 1) :=
          Finset.max'_mem _ hSne
        rw [Finset.mem_filter] at hqmem'
        obtain ⟨hqmem, hqle⟩ := hqmem'
        -- `q` and `m² - 1 - k` are consecutive divisors of `n !`.
        have hsuccq : ∀ d ∈ (Nat.factorial n).divisors, d ≤ q ∨ m ^ 2 - 1 - k ≤ d := by
          intro d hd
          rcases le_or_gt d (m ^ 2 - 1 - k - 1) with hle | hgt
          · exact Or.inl (Finset.le_max' _ d (Finset.mem_filter.mpr ⟨hd, hle⟩))
          · exact Or.inr (by omega)
        have hssuct : ∀ d ∈ (Nat.factorial n).divisors,
            d ≤ m ^ 2 - 1 - k ∨ m ^ 2 - 1 - k + 1 ≤ d := fun d _ => by omega
        have hqt : q < m ^ 2 - 1 - k := by omega
        have hgap : m ^ 2 - 1 - k - q ≤ m ^ 2 - 1 - k + 1 - (m ^ 2 - 1 - k) :=
          hGood q hqmem _ (hmem htD) _ (hmem ht1D) hqt (by omega) hsuccq hssuct
        have hqeq : q = m ^ 2 - 1 - k - 1 := by omega
        have hm1D : m ^ 2 - 1 - k - 1 ∣ Nat.factorial n :=
          hqeq ▸ (Nat.mem_divisors.mp hqmem).1
        have hcases : j = m ^ 2 - 1 - k - 1 ∨ m ^ 2 - 1 - k ≤ j := by omega
        rcases hcases with rfl | hge
        · exact hm1D
        · exact ih (by omega) j hge hj2
  have hpD : p ∣ Nat.factorial n := key (m ^ 2 - 2) le_rfl p (by omega) (by omega)
  have hple := (Nat.Prime.dvd_factorial hpprime).mp hpD
  omega

snip end

problem usa2024_p1 (n : ℕ) (hn : 3 ≤ n) : n ∈ solution_set ↔ Good n := by
  constructor
  · intro h
    have h' : n = 3 ∨ n = 4 := by
      simp only [solution_set, Set.mem_insert_iff, Set.mem_singleton_iff] at h
      exact h
    rcases h' with rfl | rfl
    · exact good_three
    · exact good_four
  · intro hGood
    simp only [solution_set, Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases (by omega : n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ (7 ≤ n ∧ n ≤ 12) ∨ 13 ≤ n) with
      rfl | rfl | rfl | rfl | ⟨h7, h12⟩ | h13
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact absurd hGood not_good_five
    · exact absurd hGood not_good_six
    · exact absurd hGood (not_good_of_seven_le h7 h12)
    · exact absurd hGood (not_good_of_thirteen_le h13)

end Usa2024P1
