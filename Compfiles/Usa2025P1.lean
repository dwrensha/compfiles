/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Data.List.GetD
public import Mathlib.Data.Nat.Digits.Lemmas
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.NumberTheory] }

/-!
# USA Mathematical Olympiad 2025, Problem 1

Fix positive integers k and d. Prove that for all sufficiently large odd
positive integers n, the digits of the base-2n representation of n ^ k are
all greater than d.
-/

namespace Usa2025P1

snip begin

/-- For odd `n` and `1 ≤ ℓ ≤ k`, the residue of `n ^ k` modulo `(2 * n) ^ ℓ`
has the form `c * n ^ ℓ` for an odd `c` (so in particular `1 ≤ c`).
In other words, the `ℓ` rightmost base-`(2 * n)` digits of `n ^ k` are the
base-`(2 * n)` digits of `c * n ^ ℓ`. -/
lemma residue_mod {n k ℓ : ℕ} (hodd : Odd n) (hℓ1 : 1 ≤ ℓ) (hℓk : ℓ ≤ k) :
    ∃ c : ℕ, Odd c ∧ 1 ≤ c ∧ n ^ k % (2 * n) ^ ℓ = c * n ^ ℓ := by
  have hn0 : 0 < n := hodd.pos
  have hc_odd : Odd (n ^ (k - ℓ) % 2 ^ ℓ) := by
    rw [Nat.odd_iff, Nat.mod_mod_of_dvd _ (dvd_pow_self 2 (by omega : ℓ ≠ 0))]
    exact Nat.odd_iff.mp hodd.pow
  refine ⟨n ^ (k - ℓ) % 2 ^ ℓ, hc_odd, hc_odd.pos, ?_⟩
  have hdvd : (2 * n) ^ ℓ ∣ n ^ k - (n ^ (k - ℓ) % 2 ^ ℓ) * n ^ ℓ := by
    rw [mul_pow]
    have h1 : 2 ^ ℓ * n ^ ℓ ∣ (n ^ (k - ℓ) - n ^ (k - ℓ) % 2 ^ ℓ) * n ^ ℓ :=
      mul_dvd_mul_right (Nat.dvd_sub_mod _) _
    have h2 : (n ^ (k - ℓ) - n ^ (k - ℓ) % 2 ^ ℓ) * n ^ ℓ
        = n ^ k - (n ^ (k - ℓ) % 2 ^ ℓ) * n ^ ℓ := by
      rw [Nat.sub_mul, ← pow_add, Nat.sub_add_cancel hℓk]
    rwa [h2] at h1
  obtain ⟨q, hq⟩ := hdvd
  have hle : (n ^ (k - ℓ) % 2 ^ ℓ) * n ^ ℓ ≤ n ^ k := by
    calc (n ^ (k - ℓ) % 2 ^ ℓ) * n ^ ℓ ≤ n ^ (k - ℓ) * n ^ ℓ :=
        Nat.mul_le_mul (Nat.mod_le _ _) le_rfl
      _ = n ^ k := by rw [← pow_add, Nat.sub_add_cancel hℓk]
  have hlt : (n ^ (k - ℓ) % 2 ^ ℓ) * n ^ ℓ < (2 * n) ^ ℓ := by
    rw [mul_pow]
    exact mul_lt_mul_of_pos_right
      (Nat.mod_lt _ (Nat.pow_pos (by omega : (0 : ℕ) < 2))) (Nat.pow_pos hn0)
  have hnk : n ^ k = (n ^ (k - ℓ) % 2 ^ ℓ) * n ^ ℓ + (2 * n) ^ ℓ * q := by
    rw [← hq]
    exact (Nat.add_sub_cancel' hle).symm
  rw [hnk, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

/-- The `i`-th base-`b` digit of `m` (counting from the right, starting at `0`)
equals `E / b ^ i`, where `E = m % b ^ (i + 1)` is the residue of `m` modulo
the next power of `b`. -/
lemma digit_of_mod {m b E i : ℕ} (hb : 1 < b) (hm : m % b ^ (i + 1) = E) :
    m / b ^ i % b = E / b ^ i := by
  have hb0 : 0 < b := by omega
  have hE : E < b ^ (i + 1) := by
    rw [← hm]
    exact Nat.mod_lt _ (Nat.pow_pos hb0)
  have hbl : b ^ (i + 1) = b ^ i * b := pow_succ b i
  have hE' : E < b ^ i * b := by rwa [hbl] at hE
  have h := Nat.div_add_mod m (b ^ (i + 1))
  rw [hm] at h
  set q := m / b ^ (i + 1) with hq_def
  -- h : b ^ (i + 1) * q + E = m
  have hm' : m = E + b ^ i * (b * q) := by
    rw [← h, hbl]
    ring
  have hdiv : m / b ^ i = E / b ^ i + b * q := by
    rw [hm']
    exact Nat.add_mul_div_left _ _ (Nat.pow_pos hb0)
  rw [hdiv, Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt (Nat.div_lt_of_lt_mul hE')

snip end

problem usa2025_p1 (k d : ℕ) (hk : 0 < k) (_hd : 0 < d) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Odd n → ∀ a ∈ Nat.digits (2 * n) (n ^ k), d < a := by
  -- The threshold `N = (d + 1) * 2 ^ (k - 1)` works.
  refine ⟨(d + 1) * 2 ^ (k - 1), fun n hn hodd a ha ↦ ?_⟩
  have hn0 : 0 < n := hodd.pos
  -- Locate the position `i` of the digit `a`.
  obtain ⟨i, hi_lt, hi_eq⟩ := List.mem_iff_getElem.mp ha
  -- `n ^ k < (2 * n) ^ k`, so `n ^ k` has at most `k` base-`(2 * n)` digits and `i < k`.
  have hik : i < k := by
    have hlen : (Nat.digits (2 * n) (n ^ k)).length ≤ k := by
      rw [Nat.digits_length_le_iff (by omega : 1 < 2 * n)]
      exact Nat.pow_lt_pow_left (by omega : n < 2 * n) (by omega : k ≠ 0)
    omega
  -- The digit value: `a = n ^ k / (2 * n) ^ i % (2 * n)`.
  have ha_eq : a = n ^ k / (2 * n) ^ i % (2 * n) := by
    have h1 : (Nat.digits (2 * n) (n ^ k)).getD i 0 = n ^ k / (2 * n) ^ i % (2 * n) :=
      Nat.getD_digits _ _ (by omega : 2 ≤ 2 * n)
    rw [List.getD_eq_getElem _ _ hi_lt] at h1
    exact hi_eq.symm.trans h1
  -- The residue computation: `n ^ k % (2 * n) ^ (i + 1) = c * n ^ (i + 1)` with `1 ≤ c`.
  obtain ⟨c, -, hc1, hres⟩ := residue_mod (n := n) (k := k) (ℓ := i + 1) hodd
    (by omega) (by omega)
  -- Hence `a = c * n ^ (i + 1) / (2 * n) ^ i = c * n / 2 ^ i`.
  have hdig : n ^ k / (2 * n) ^ i % (2 * n) = c * n ^ (i + 1) / (2 * n) ^ i :=
    digit_of_mod (by omega : 1 < 2 * n) hres
  have hsimp : c * n ^ (i + 1) / (2 * n) ^ i = c * n / 2 ^ i := by
    rw [mul_pow, pow_succ]
    have h : c * (n ^ i * n) = (c * n) * n ^ i := by ring
    rw [h, Nat.mul_div_mul_right _ _ (Nat.pow_pos hn0)]
  -- The lower bound: `d + 1 ≤ c * n / 2 ^ i`, because `c ≥ 1` and
  -- `n ≥ (d + 1) * 2 ^ (k - 1)` with `2 ^ i ∣ 2 ^ (k - 1)`.
  have hbound : d + 1 ≤ c * n / 2 ^ i := by
    have hge : (d + 1) * 2 ^ (k - 1) ≤ c * n := by
      calc (d + 1) * 2 ^ (k - 1) ≤ n := hn
        _ ≤ c * n := Nat.le_mul_of_pos_left n hc1
    have hsplit : 2 ^ (k - 1) = 2 ^ (k - 1 - i) * 2 ^ i := by
      rw [← pow_add]
      congr 1
      omega
    rw [hsplit] at hge
    have h1 : (d + 1) * 2 ^ (k - 1 - i) ≤ c * n / 2 ^ i := by
      have h3 : (d + 1) * (2 ^ (k - 1 - i) * 2 ^ i)
          = 2 ^ i * ((d + 1) * 2 ^ (k - 1 - i)) := by ring
      rw [h3] at hge
      have h4 : 2 ^ i * ((d + 1) * 2 ^ (k - 1 - i)) / 2 ^ i ≤ c * n / 2 ^ i :=
        Nat.div_le_div_right hge
      rwa [Nat.mul_div_right _ (Nat.pow_pos (by omega : (0 : ℕ) < 2))] at h4
    exact (Nat.le_mul_of_pos_right (d + 1)
      (Nat.pow_pos (by omega : (0 : ℕ) < 2))).trans h1
  rw [ha_eq, hdig, hsimp]
  exact hbound

end Usa2025P1
