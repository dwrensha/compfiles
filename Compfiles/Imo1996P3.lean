/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Olympiad 1996, Problem 3

Let S denote the set of nonnegative integers. Find
all functions f from S to itself such that

 f(m + f(n)) = f(f(m)) + f(n)

for all m,n in S.
-/

namespace Imo1996P3

determine SolutionSet : Set (ℕ → ℕ) :=
   { f | ∃ k : ℕ, ∃ n : ℕ → ℕ, n 0 = 0 ∧
          f = fun x ↦ (x / k) * k + (n (x % k)) * k }

problem imo1996_p3 (f : ℕ → ℕ) :
    f ∈ SolutionSet ↔ ∀ m n, f (m + f n) = f (f m) + f n := by
  -- we follow the informal solution from
  -- https://prase.cz/kalva/imo/isoln/isoln963.html
  constructor
  · intro hf m n
    simp only [Set.mem_setOf_eq] at hf
    obtain ⟨k, n1, hn1, hf1⟩ := hf

    obtain hk0 | hkp := Nat.eq_zero_or_pos k
    · rw [hf1, hk0]; simp

    -- Let m = ak + r, n = bk + s, with 0 ≤ r, s < k.
    let a := m / k
    let r := m % k
    let b := n / k
    let s := n % k

    have h2 : ∀ x, k ∣ x → f x = x := fun x hx ↦ by
      rw [hf1]
      dsimp only
      rw [Nat.div_mul_cancel hx, Nat.dvd_iff_mod_eq_zero.mp hx, hn1]
      simp

    have h3 : ∀ x, k ∣ f x := fun x ↦ by
      rw [hf1]
      dsimp only
      rw [←Nat.add_mul]
      exact Nat.dvd_mul_left _ _

    -- Then f(f(m)) = f(m)
    have h1 : ∀ x, f (f x) = f x := by grind

    -- f(m) = ak + (n r) k
    have h4 : f m = a * k + (n1 r) * k := by subst f; rfl

    -- and f(n) = bk + (n s) k
    have h5 : f n = b * k + (n1 s) * k := by subst f; rfl

    -- so f(m + f(n)) = ak + bk + nrk + nsk,
    have h6 : f (m + f n) = a * k + b * k + (n1 r) * k + (n1 s) * k := by
      -- todo: cleaner version that uses the above lemmas?
      rw [h5]
      rw [hf1]
      dsimp only
      rw [Nat.add_mod, Nat.add_mod (b * k)]
      simp only [Nat.mul_mod_left, add_zero, Nat.zero_mod,
                 dvd_refl, Nat.mod_mod_of_dvd]
      have h7 : k ∣ b * k + n1 s * k := by apply Nat.dvd_add <;> simp
      rw [Nat.add_div_of_dvd_left h7]
      rw [←Nat.add_mul b]
      rw [Nat.mul_div_left (b + n1 s) hkp, Nat.add_mul]
      ring

    -- and f(f(m)) + f(n) = ak + bk + nrk + nsk.
    have h8 : f (f m) + f n = a * k + b * k + (n1 r) * k + (n1 s) * k := by
      grind

    grind
  intro hf
  simp only [Set.mem_setOf_eq]

  /- Setting m = n = 0, the given relation becomes:
     f(f(0)) = f(f(0)) + f(0).
     Hence f(0) = 0. Hence also f(f(0)) = 0.
     Setting m = 0, now gives f(f(n)) = f(n),
    so we may write the original relation as f(m + f(n)) = f(m) + f(n).
  -/
  have h0 := hf 0 0
  rw [zero_add] at h0
  have hf0 : f 0 = 0 := by omega
  have hf00 : f (f 0) = 0 := by grind
  have hm := hf 0
  rw [hf00] at hm
  simp only [zero_add] at hm

  replace hf : ∀ m n, f (m + f n) = f m + f n := by grind

  -- So for all n, f(n) is a fixed point.

  -- Let k be the smallest non-zero fixed point.
  -- If k does not exist, then f(n) is zero for all n,
  -- which is a possible solution.

  obtain hfp | hfp := Classical.em (∃ x, 0 < x ∧ f x = x)
  swap
  · have h2 : ∀ y, f y = 0 := by grind
    use 0, 0
    aesop

  let k := Nat.find hfp
  obtain ⟨hk0, hfk⟩ : 0 < k ∧ f k = k := Nat.find_spec hfp

  -- If k does exist, then an easy induction shows that f(qk) = qk
  --  for all non-negative integers q.
  have h3 : ∀ q, f (q * k) = q * k := fun q ↦ by
    induction q with
    | zero => simp only [hf0, zero_mul]
    | succ q ih =>
      rw [Nat.add_mul, one_mul]
      nth_rw 2 [←hfk]
      rw [hf, ih, hfk]

  have h4 : ∀ n, f n = n → k ∣ n := fun n hn ↦ by
    -- Now if n is another fixed point, write n = kq + r, with 0 ≤ r < k.
    let q := n / k
    let r := n % k
    have hnd : n = k * q + r := (Nat.div_add_mod n k).symm

    have h5 := calc
      f n = f (r + f (k * q)) := by
              rw [mul_comm, h3, add_comm, mul_comm]
              exact congrArg f hnd
        _ = f r + f (k * q) := by grind
        _ = k * q + f r :=  by rw [mul_comm, h3]; ring

    -- Hence f(r) = r
    have h6 : f r = r := by
      rw [hn, hnd] at h5
      exact Nat.add_left_cancel h5.symm

    -- so r must be zero.
    have h7 : r = 0 := by
      have hr : r < k := Nat.mod_lt n hk0
      have h8 := Nat.find_min hfp hr
      rw [not_and'] at h8
      exact Nat.eq_zero_of_not_pos (h8 h6)

    exact Nat.dvd_of_mod_eq_zero h7

  -- so f(n) is a multiple of k for any n.
  have h10 : ∀ n, k ∣ f n := fun n ↦ h4 (f n) (hm n)

  use k
  use fun x ↦ f x / k
  constructor
  · simp[hf0]
  ext x
  nth_rw 1 [←Nat.div_add_mod x k]
  have h11 := h3 (x / k)
  nth_rw 2 [mul_comm] at h11
  rw [←h11, add_comm _ (x % k), hf, h3]
  have h12 : f (x % k) / k * k = f (x % k) := Nat.div_mul_cancel (h10 (x % k))
  rw [h12]
  ring

end Imo1996P3
