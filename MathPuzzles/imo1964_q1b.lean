import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LibrarySearch

/-!
# International Mathematical Olympiad 1964, Problem 1b

Prove that there is no positive integer n for which 2ⁿ + 1 is divisible by 7.
-/

/-
Informal proof (credit to twitch.tv viewer int_fast64_t):
  let 2^n = 2^{3k + j},j < 3
  (i.e. write n as 3k + j)
  =>
    2^n mod 7 = (2^3 mod 7)^k * 2^j mod 7 = 1 mod 7 * 2^j mod 7,
  but 2^j < 5
-/
theorem imo_1964_q1b (n : ℕ) : ¬ 7 ∣ (2^n + 1) := by
  intro h
  replace h := Nat.mod_eq_zero_of_dvd h
  have h1 := Nat.div_add_mod n 3
  rw[←h1] at h; clear h1

  have h3 : (2 ^ 3) % 7 = 1 := by rfl
  have h4 : 1 % 7 = 1 := by rfl

  have h := calc
     0 = (2 ^ (3 * (n / 3) + n % 3) + 1) % 7       := h.symm
     _ = ((2 ^ 3)^ (n / 3) * 2 ^ (n % 3) + 1) % 7  := by rw[pow_add, pow_mul]
     _ = ((2 ^ 3 % 7) ^ (n / 3) % 7 * (2 ^ (n % 3) % 7) % 7 + 1 % 7) % 7 :=
                      by rw[Nat.add_mod, Nat.mul_mod, Nat.pow_mod]
     _ = (1 ^ (n / 3) % 7 * (2 ^ (n % 3) % 7) % 7 + 1 % 7) % 7 := by rw[h3]
     _ = (1 % 7 * (2 ^ (n % 3) % 7) % 7 + 1 % 7) % 7 := by rw[one_pow]
     _ = (2 ^ (n % 3) % 7 + 1) % 7 := by rw[h4, one_mul, Nat.mod_mod]

  have hn : ∃ n', n' = n % 3 := ⟨n%3, rfl⟩
  obtain ⟨n', hn'⟩ := hn
  cases n' with
  | zero => rw[← hn'] at h; norm_num at h
  | succ n' =>
    cases n' with
    | zero => rw[← hn'] at h; norm_num at h
    | succ n' =>
      cases n' with
      | zero => rw[← hn'] at h; norm_num at h
      | succ n' => have h5 : 3 > 0 := by norm_num
                   have h6 := Nat.mod_lt n h5
                   rw[←hn'] at h6
                   linarith
