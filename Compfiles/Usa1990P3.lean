/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.Ring
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.NumberTheory] }

/-!
# USA Mathematical Olympiad 1990, Problem 3

Show that for any odd positive integer n, we can always divide the set
{n, n+1, n+2, ... , n+32} into two parts, one with 14 numbers and one with 19,
so that the numbers in each part can be arranged in a circle, with each number
relatively prime to its two neighbours.
-/

namespace Usa1990P3

/-- A circular arrangement `a : Fin k → ℕ` of `k` numbers is *valid* if every entry is
relatively prime to its cyclically-next neighbour (and hence also to its cyclically
previous neighbour, since `Nat.Coprime` is symmetric). -/
def ValidCircle {k : ℕ} [NeZero k] (a : Fin k → ℕ) : Prop :=
  ∀ i : Fin k, Nat.Coprime (a i) (a (i + 1))

snip begin

/- Solution outline (following John Scholes' write-up at
   https://prase.cz/kalva/usa/usoln/usol903.html):

   We split on whether `13 ∣ n`, and then on `n % 17`.

   * If `13 ∤ n`, the first circle is `n, n+1, …, n+13`: consecutive integers are
     coprime, and `gcd(n, n+13) ∣ 13`.  The second circle is the remaining 19 numbers
     `n+14, …, n+32` arranged as `n+15, n+14, n+16, n+17, …, n+32` when
     `n ≢ 2 [MOD 17]` (the wrap-around pair `n+32, n+15` differs by 17), and as
     `n+14, n+15, …, n+30, n+32, n+31` when `n ≡ 2 [MOD 17]`.

   * If `13 ∣ n`, the first circle is `n+19, n+20, …, n+32` (the wrap-around pair
     `n+32, n+19` differs by 13, which divides neither of them).  The second circle is
     `n, …, n+18` arranged as `n+1, n, n+2, …, n+18` when `n ≢ 16 [MOD 17]`, and as
     `n, n+1, …, n+16, n+18, n+17` when `n ≡ 16 [MOD 17]`.

   Every "special" seam joins two numbers whose difference is `1`, `2`, `13` or `17`;
   for the difference `2` seams we use that `n` is odd. -/

section Helpers

/-- Consecutive integers are coprime. -/
lemma coprime_succ_self' (m : ℕ) : Nat.Coprime m (m + 1) := by
  rw [Nat.coprime_self_add_right]
  exact Nat.coprime_one_right m

/-- `n + c` is coprime to its successor. -/
lemma coprime_succ_gen (n c : ℕ) : Nat.Coprime (n + c) (n + (c + 1)) := by
  have e : n + (c + 1) = (n + c) + 1 := by ring
  rw [e]
  exact coprime_succ_self' _

/-- If `p` is prime and does not divide `n + c`, then `n + c` and `n + c + p` are
coprime (any common divisor divides their difference `p`). -/
lemma coprime_add_prime_right {p : ℕ} (hp : p.Prime) {n c : ℕ} (h : ¬ p ∣ n + c) :
    Nat.Coprime (n + c) (n + (c + p)) := by
  have e : n + (c + p) = (n + c) + p := by ring
  rw [e, Nat.coprime_self_add_right, Nat.coprime_comm, hp.coprime_iff_not_dvd]
  exact h

/-- The symmetric version of `coprime_add_prime_right`. -/
lemma coprime_add_prime_left {p : ℕ} (hp : p.Prime) {n c : ℕ} (h : ¬ p ∣ n + c) :
    Nat.Coprime (n + (c + p)) (n + c) :=
  Nat.coprime_comm.mpr (coprime_add_prime_right hp h)

/-- Two odd numbers at distance `2` are coprime. -/
lemma coprime_add_two {n c : ℕ} (h : ¬ 2 ∣ n + c) : Nat.Coprime (n + c) (n + (c + 2)) :=
  coprime_add_prime_right Nat.prime_two h

end Helpers

section Constructions

/-- Offsets of the first circle when `13 ∤ n`: `[n, n+1, …, n+13]`. -/
def offA1 (i : Fin 14) : ℕ := i.val

/-- Offsets of the second circle when `13 ∤ n` and `n ≢ 2 [MOD 17]`:
`[n+15, n+14, n+16, n+17, …, n+32]`. -/
def offB1a (i : Fin 19) : ℕ :=
  if i.val = 0 then 15 else if i.val = 1 then 14 else i.val + 14

/-- Offsets of the second circle when `13 ∤ n` and `n ≡ 2 [MOD 17]`:
`[n+14, n+15, …, n+30, n+32, n+31]`. -/
def offB1b (i : Fin 19) : ℕ :=
  if i.val = 17 then 32 else if i.val = 18 then 31 else i.val + 14

/-- Offsets of the first circle when `13 ∣ n`: `[n+19, n+20, …, n+32]`. -/
def offA2 (i : Fin 14) : ℕ := i.val + 19

/-- Offsets of the second circle when `13 ∣ n` and `n ≢ 16 [MOD 17]`:
`[n+1, n, n+2, n+3, …, n+18]`. -/
def offB2a (i : Fin 19) : ℕ :=
  if i.val = 0 then 1 else if i.val = 1 then 0 else i.val

/-- Offsets of the second circle when `13 ∣ n` and `n ≡ 16 [MOD 17]`:
`[n, n+1, …, n+16, n+18, n+17]`. -/
def offB2b (i : Fin 19) : ℕ :=
  if i.val = 17 then 18 else if i.val = 18 then 17 else i.val

/-- First circle when `13 ∤ n`. -/
def a1 (n : ℕ) (i : Fin 14) : ℕ := n + offA1 i

/-- Second circle when `13 ∤ n` and `n ≢ 2 [MOD 17]`. -/
def b1a (n : ℕ) (i : Fin 19) : ℕ := n + offB1a i

/-- Second circle when `13 ∤ n` and `n ≡ 2 [MOD 17]`. -/
def b1b (n : ℕ) (i : Fin 19) : ℕ := n + offB1b i

/-- First circle when `13 ∣ n`. -/
def a2 (n : ℕ) (i : Fin 14) : ℕ := n + offA2 i

/-- Second circle when `13 ∣ n` and `n ≢ 16 [MOD 17]`. -/
def b2a (n : ℕ) (i : Fin 19) : ℕ := n + offB2a i

/-- Second circle when `13 ∣ n` and `n ≡ 16 [MOD 17]`. -/
def b2b (n : ℕ) (i : Fin 19) : ℕ := n + offB2b i

end Constructions

section InjectivityBounds

lemma offA1_injective : Function.Injective offA1 := fun _i _j h ↦ Fin.ext h

lemma offA2_injective : Function.Injective offA2 :=
  fun _i _j h ↦ Fin.ext (Nat.add_right_cancel h)

lemma offB1a_injective : Function.Injective offB1a := by
  intro i j h
  simp only [offB1a] at h
  apply Fin.ext
  (repeat' split at h) <;> lia

lemma offB1b_injective : Function.Injective offB1b := by
  intro i j h
  simp only [offB1b] at h
  apply Fin.ext
  (repeat' split at h) <;> lia

lemma offB2a_injective : Function.Injective offB2a := by
  intro i j h
  simp only [offB2a] at h
  apply Fin.ext
  (repeat' split at h) <;> lia

lemma offB2b_injective : Function.Injective offB2b := by
  intro i j h
  simp only [offB2b] at h
  apply Fin.ext
  (repeat' split at h) <;> lia

/-- Adding the same constant preserves injectivity. -/
lemma injective_n_add {k : ℕ} {off : Fin k → ℕ} (h : Function.Injective off) (n : ℕ) :
    Function.Injective (fun i ↦ n + off i) :=
  fun _i _j h' ↦ h (Nat.add_left_cancel h')

lemma offA1_le (i : Fin 14) : offA1 i ≤ 13 := by
  have := i.isLt
  simp only [offA1]
  lia

lemma offA1_le32 (i : Fin 14) : offA1 i ≤ 32 := (offA1_le i).trans (by norm_num)

lemma offA2_ge (i : Fin 14) : 19 ≤ offA2 i := by
  simp only [offA2]
  lia

lemma offA2_le32 (i : Fin 14) : offA2 i ≤ 32 := by
  have := i.isLt
  simp only [offA2]
  lia

lemma offB1a_ge (i : Fin 19) : 14 ≤ offB1a i := by
  simp only [offB1a]
  (repeat' split) <;> lia

lemma offB1a_le32 (i : Fin 19) : offB1a i ≤ 32 := by
  have := i.isLt
  simp only [offB1a]
  (repeat' split) <;> lia

lemma offB1b_ge (i : Fin 19) : 14 ≤ offB1b i := by
  simp only [offB1b]
  (repeat' split) <;> lia

lemma offB1b_le32 (i : Fin 19) : offB1b i ≤ 32 := by
  have := i.isLt
  simp only [offB1b]
  (repeat' split) <;> lia

lemma offB2a_le18 (i : Fin 19) : offB2a i ≤ 18 := by
  have := i.isLt
  simp only [offB2a]
  (repeat' split) <;> lia

lemma offB2a_le32 (i : Fin 19) : offB2a i ≤ 32 := (offB2a_le18 i).trans (by norm_num)

lemma offB2b_le18 (i : Fin 19) : offB2b i ≤ 18 := by
  have := i.isLt
  simp only [offB2b]
  (repeat' split) <;> lia

lemma offB2b_le32 (i : Fin 19) : offB2b i ≤ 32 := (offB2b_le18 i).trans (by norm_num)

end InjectivityBounds

section Partition

/-- If all offsets are at most `32`, the image of `fun i ↦ n + off i` lies in
`Finset.Icc n (n + 32)`. -/
lemma image_add_off_subset_Icc {k : ℕ} (off : Fin k → ℕ) (h : ∀ i, off i ≤ 32) (n : ℕ) :
    Finset.univ.image (fun i ↦ n + off i) ⊆ Finset.Icc n (n + 32) := by
  intro x hx
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
  obtain ⟨i, rfl⟩ := hx
  simp only [Finset.mem_Icc]
  refine ⟨Nat.le_add_right _ _, ?_⟩
  have := h i
  lia

/-- If the offsets of two families are separated by a constant `c`, their images
(after shifting by `n`) are disjoint. -/
lemma disjoint_add_off {k l : ℕ} {off₁ : Fin k → ℕ} {off₂ : Fin l → ℕ} {c : ℕ}
    (h₁ : ∀ i, off₁ i ≤ c) (h₂ : ∀ j, c < off₂ j) (n : ℕ) :
    Disjoint (Finset.univ.image (fun i ↦ n + off₁ i))
      (Finset.univ.image (fun j ↦ n + off₂ j)) := by
  rw [Finset.disjoint_left]
  intro x hx hx2
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx hx2
  obtain ⟨i, rfl⟩ := hx
  obtain ⟨j, hj⟩ := hx2
  have h3 := h₁ i
  have h4 := h₂ j
  have h5 : off₂ j = off₁ i := Nat.add_left_cancel hj
  lia

/-- Two disjoint injective families of `14` and `19` elements inside the `33`-element
set `Finset.Icc n (n + 32)` must cover it. -/
lemma image_union_eq_Icc {n : ℕ} {a : Fin 14 → ℕ} {b : Fin 19 → ℕ}
    (ha : Function.Injective a) (hb : Function.Injective b)
    (hsub₁ : Finset.univ.image a ⊆ Finset.Icc n (n + 32))
    (hsub₂ : Finset.univ.image b ⊆ Finset.Icc n (n + 32))
    (hdisj : Disjoint (Finset.univ.image a) (Finset.univ.image b)) :
    Finset.univ.image a ∪ Finset.univ.image b = Finset.Icc n (n + 32) := by
  apply Finset.eq_of_subset_of_card_le (Finset.union_subset hsub₁ hsub₂)
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ ha,
    Finset.card_image_of_injective _ hb, Finset.card_univ, Finset.card_univ,
    Fintype.card_fin, Fintype.card_fin, Nat.card_Icc]
  lia

end Partition

section ValidCircles

lemma validCircle_a1 (n : ℕ) (h13 : ¬ 13 ∣ n) : ValidCircle (a1 n) := by
  unfold ValidCircle
  intro i
  rcases eq_or_lt_of_le (Fin.le_last i) with hlast | hlt
  · -- wrap-around seam: `n + 13` next to `n`; their difference is `13`
    subst hlast
    show Nat.Coprime (n + 13) (n + 0)
    exact coprime_add_prime_left (p := 13) (by norm_num) (c := 0) (by lia)
  · have hv : ((i + 1 : Fin 14) : ℕ) = i.val + 1 := Fin.val_add_one_of_lt hlt
    show Nat.Coprime (n + i.val) (n + ((i + 1 : Fin 14)).val)
    rw [hv]
    exact coprime_succ_gen n i.val

lemma validCircle_b1a (n : ℕ) (hn : Odd n) (h17 : n % 17 ≠ 2) :
    ValidCircle (b1a n) := by
  unfold ValidCircle
  intro i
  rcases eq_or_lt_of_le (Fin.le_last i) with hlast | hlt
  · -- wrap-around seam: `n + 32` next to `n + 15`; their difference is `17`
    subst hlast
    show Nat.Coprime (n + 32) (n + 15)
    exact coprime_add_prime_left (p := 17) (by norm_num) (c := 15) (by lia)
  · have hv : ((i + 1 : Fin 19) : ℕ) = i.val + 1 := Fin.val_add_one_of_lt hlt
    show Nat.Coprime (n + offB1a i) (n + offB1a (i + 1))
    simp only [offB1a, hv]
    by_cases hi0 : i.val = 0
    · -- seam: `n + 15` next to `n + 14`
      rw [ite_eq_left hi0, ite_eq_right (by lia : ¬ i.val + 1 = 0),
        ite_eq_left (by lia : i.val + 1 = 1)]
      exact (coprime_succ_gen n 14).symm
    · by_cases hi1 : i.val = 1
      · -- seam: `n + 14` next to `n + 16`; both odd since `n` is odd
        rw [ite_eq_right hi0, ite_eq_left hi1, ite_eq_right (by lia : ¬ i.val + 1 = 0),
          ite_eq_right (by lia : ¬ i.val + 1 = 1), hi1]
        obtain ⟨k, hk⟩ := hn
        exact coprime_add_two (c := 14) (by lia)
      · -- generic seam: consecutive integers
        have h2 : 2 ≤ i.val := by lia
        rw [ite_eq_right hi0, ite_eq_right hi1, ite_eq_right (by lia : ¬ i.val + 1 = 0),
          ite_eq_right (by lia : ¬ i.val + 1 = 1)]
        exact coprime_succ_gen n (i.val + 14)

lemma validCircle_b1b (n : ℕ) (hn : Odd n) (h17 : n % 17 = 2) :
    ValidCircle (b1b n) := by
  unfold ValidCircle
  intro i
  rcases eq_or_lt_of_le (Fin.le_last i) with hlast | hlt
  · -- wrap-around seam: `n + 31` next to `n + 14`; their difference is `17`
    subst hlast
    show Nat.Coprime (n + 31) (n + 14)
    exact coprime_add_prime_left (p := 17) (by norm_num) (c := 14) (by lia)
  · have hv : ((i + 1 : Fin 19) : ℕ) = i.val + 1 := Fin.val_add_one_of_lt hlt
    show Nat.Coprime (n + offB1b i) (n + offB1b (i + 1))
    simp only [offB1b, hv]
    rcases Nat.lt_trichotomy i.val 16 with h | h | h
    · -- generic seam: consecutive integers
      rw [ite_eq_right (by lia : ¬ i.val = 17), ite_eq_right (by lia : ¬ i.val = 18),
        ite_eq_right (by lia : ¬ i.val + 1 = 17), ite_eq_right (by lia : ¬ i.val + 1 = 18)]
      exact coprime_succ_gen n (i.val + 14)
    · -- seam: `n + 30` next to `n + 32`; both odd
      rw [ite_eq_right (by lia : ¬ i.val = 17), ite_eq_right (by lia : ¬ i.val = 18),
        ite_eq_left (by lia : i.val + 1 = 17), h]
      obtain ⟨k, hk⟩ := hn
      exact coprime_add_two (c := 30) (by lia)
    · -- seam: `n + 32` next to `n + 31`
      have h17' : i.val = 17 := by lia
      rw [ite_eq_left h17', ite_eq_right (by lia : ¬ i.val + 1 = 17),
        ite_eq_left (by lia : i.val + 1 = 18)]
      exact (coprime_succ_gen n 31).symm

lemma validCircle_a2 (n : ℕ) (h13 : 13 ∣ n) : ValidCircle (a2 n) := by
  unfold ValidCircle
  intro i
  rcases eq_or_lt_of_le (Fin.le_last i) with hlast | hlt
  · -- wrap-around seam: `n + 32` next to `n + 19`; their difference is `13`
    subst hlast
    show Nat.Coprime (n + 32) (n + 19)
    exact coprime_add_prime_left (p := 13) (by norm_num) (c := 19) (by lia)
  · have hv : ((i + 1 : Fin 14) : ℕ) = i.val + 1 := Fin.val_add_one_of_lt hlt
    show Nat.Coprime (n + (i.val + 19)) (n + (((i + 1 : Fin 14)).val + 19))
    rw [hv]
    exact coprime_succ_gen n (i.val + 19)

lemma validCircle_b2a (n : ℕ) (hn : Odd n) (h17 : n % 17 ≠ 16) :
    ValidCircle (b2a n) := by
  unfold ValidCircle
  intro i
  rcases eq_or_lt_of_le (Fin.le_last i) with hlast | hlt
  · -- wrap-around seam: `n + 18` next to `n + 1`; their difference is `17`
    subst hlast
    show Nat.Coprime (n + 18) (n + 1)
    exact coprime_add_prime_left (p := 17) (by norm_num) (c := 1) (by lia)
  · have hv : ((i + 1 : Fin 19) : ℕ) = i.val + 1 := Fin.val_add_one_of_lt hlt
    show Nat.Coprime (n + offB2a i) (n + offB2a (i + 1))
    simp only [offB2a, hv]
    by_cases hi0 : i.val = 0
    · -- seam: `n + 1` next to `n`
      rw [ite_eq_left hi0, ite_eq_right (by lia : ¬ i.val + 1 = 0),
        ite_eq_left (by lia : i.val + 1 = 1)]
      show Nat.Coprime (n + 1) n
      exact (coprime_succ_gen n 0).symm
    · by_cases hi1 : i.val = 1
      · -- seam: `n` next to `n + 2`; both odd
        rw [ite_eq_right hi0, ite_eq_left hi1, ite_eq_right (by lia : ¬ i.val + 1 = 0),
          ite_eq_right (by lia : ¬ i.val + 1 = 1), hi1]
        obtain ⟨k, hk⟩ := hn
        exact coprime_add_two (c := 0) (by lia)
      · -- generic seam: consecutive integers
        have h2 : 2 ≤ i.val := by lia
        rw [ite_eq_right hi0, ite_eq_right hi1, ite_eq_right (by lia : ¬ i.val + 1 = 0),
          ite_eq_right (by lia : ¬ i.val + 1 = 1)]
        exact coprime_succ_gen n i.val

lemma validCircle_b2b (n : ℕ) (hn : Odd n) (h17 : n % 17 = 16) :
    ValidCircle (b2b n) := by
  unfold ValidCircle
  intro i
  rcases eq_or_lt_of_le (Fin.le_last i) with hlast | hlt
  · -- wrap-around seam: `n + 17` next to `n`; their difference is `17`
    subst hlast
    show Nat.Coprime (n + 17) (n + 0)
    rw [Nat.coprime_comm]
    exact coprime_add_prime_right (p := 17) (by norm_num) (c := 0) (by lia)
  · have hv : ((i + 1 : Fin 19) : ℕ) = i.val + 1 := Fin.val_add_one_of_lt hlt
    show Nat.Coprime (n + offB2b i) (n + offB2b (i + 1))
    simp only [offB2b, hv]
    rcases Nat.lt_trichotomy i.val 16 with h | h | h
    · -- generic seam: consecutive integers
      rw [ite_eq_right (by lia : ¬ i.val = 17), ite_eq_right (by lia : ¬ i.val = 18),
        ite_eq_right (by lia : ¬ i.val + 1 = 17), ite_eq_right (by lia : ¬ i.val + 1 = 18)]
      exact coprime_succ_gen n i.val
    · -- seam: `n + 16` next to `n + 18`; both odd
      rw [ite_eq_right (by lia : ¬ i.val = 17), ite_eq_right (by lia : ¬ i.val = 18),
        ite_eq_left (by lia : i.val + 1 = 17), h]
      obtain ⟨k, hk⟩ := hn
      exact coprime_add_two (c := 16) (by lia)
    · -- seam: `n + 18` next to `n + 17`
      have h17' : i.val = 17 := by lia
      rw [ite_eq_left h17', ite_eq_right (by lia : ¬ i.val + 1 = 17),
        ite_eq_left (by lia : i.val + 1 = 18)]
      exact (coprime_succ_gen n 17).symm

end ValidCircles

section Cases

/-- Case `13 ∤ n`, `n ≢ 2 [MOD 17]`. -/
lemma case1a (n : ℕ) (hn : Odd n) (h13 : ¬ 13 ∣ n) (h17 : n % 17 ≠ 2) :
    ∃ a : Fin 14 → ℕ, ∃ b : Fin 19 → ℕ,
      Function.Injective a ∧ Function.Injective b ∧
      Disjoint (Finset.univ.image a) (Finset.univ.image b) ∧
      Finset.univ.image a ∪ Finset.univ.image b = Finset.Icc n (n + 32) ∧
      ValidCircle a ∧ ValidCircle b := by
  have hinj₁ := injective_n_add offA1_injective n
  have hinj₂ := injective_n_add offB1a_injective n
  have hsub₁ := image_add_off_subset_Icc offA1 offA1_le32 n
  have hsub₂ := image_add_off_subset_Icc offB1a offB1a_le32 n
  have hdisj : Disjoint (Finset.univ.image (a1 n)) (Finset.univ.image (b1a n)) :=
    disjoint_add_off offA1_le offB1a_ge n
  exact ⟨a1 n, b1a n, hinj₁, hinj₂, hdisj,
    image_union_eq_Icc hinj₁ hinj₂ hsub₁ hsub₂ hdisj,
    validCircle_a1 n h13, validCircle_b1a n hn h17⟩

/-- Case `13 ∤ n`, `n ≡ 2 [MOD 17]`. -/
lemma case1b (n : ℕ) (hn : Odd n) (h13 : ¬ 13 ∣ n) (h17 : n % 17 = 2) :
    ∃ a : Fin 14 → ℕ, ∃ b : Fin 19 → ℕ,
      Function.Injective a ∧ Function.Injective b ∧
      Disjoint (Finset.univ.image a) (Finset.univ.image b) ∧
      Finset.univ.image a ∪ Finset.univ.image b = Finset.Icc n (n + 32) ∧
      ValidCircle a ∧ ValidCircle b := by
  have hinj₁ := injective_n_add offA1_injective n
  have hinj₂ := injective_n_add offB1b_injective n
  have hsub₁ := image_add_off_subset_Icc offA1 offA1_le32 n
  have hsub₂ := image_add_off_subset_Icc offB1b offB1b_le32 n
  have hdisj : Disjoint (Finset.univ.image (a1 n)) (Finset.univ.image (b1b n)) :=
    disjoint_add_off offA1_le offB1b_ge n
  exact ⟨a1 n, b1b n, hinj₁, hinj₂, hdisj,
    image_union_eq_Icc hinj₁ hinj₂ hsub₁ hsub₂ hdisj,
    validCircle_a1 n h13, validCircle_b1b n hn h17⟩

/-- Case `13 ∣ n`, `n ≢ 16 [MOD 17]`. -/
lemma case2a (n : ℕ) (hn : Odd n) (h13 : 13 ∣ n) (h17 : n % 17 ≠ 16) :
    ∃ a : Fin 14 → ℕ, ∃ b : Fin 19 → ℕ,
      Function.Injective a ∧ Function.Injective b ∧
      Disjoint (Finset.univ.image a) (Finset.univ.image b) ∧
      Finset.univ.image a ∪ Finset.univ.image b = Finset.Icc n (n + 32) ∧
      ValidCircle a ∧ ValidCircle b := by
  have hinj₁ := injective_n_add offA2_injective n
  have hinj₂ := injective_n_add offB2a_injective n
  have hsub₁ := image_add_off_subset_Icc offA2 offA2_le32 n
  have hsub₂ := image_add_off_subset_Icc offB2a offB2a_le32 n
  have hdisj : Disjoint (Finset.univ.image (a2 n)) (Finset.univ.image (b2a n)) :=
    (disjoint_add_off offB2a_le18 offA2_ge n).symm
  exact ⟨a2 n, b2a n, hinj₁, hinj₂, hdisj,
    image_union_eq_Icc hinj₁ hinj₂ hsub₁ hsub₂ hdisj,
    validCircle_a2 n h13, validCircle_b2a n hn h17⟩

/-- Case `13 ∣ n`, `n ≡ 16 [MOD 17]`. -/
lemma case2b (n : ℕ) (hn : Odd n) (h13 : 13 ∣ n) (h17 : n % 17 = 16) :
    ∃ a : Fin 14 → ℕ, ∃ b : Fin 19 → ℕ,
      Function.Injective a ∧ Function.Injective b ∧
      Disjoint (Finset.univ.image a) (Finset.univ.image b) ∧
      Finset.univ.image a ∪ Finset.univ.image b = Finset.Icc n (n + 32) ∧
      ValidCircle a ∧ ValidCircle b := by
  have hinj₁ := injective_n_add offA2_injective n
  have hinj₂ := injective_n_add offB2b_injective n
  have hsub₁ := image_add_off_subset_Icc offA2 offA2_le32 n
  have hsub₂ := image_add_off_subset_Icc offB2b offB2b_le32 n
  have hdisj : Disjoint (Finset.univ.image (a2 n)) (Finset.univ.image (b2b n)) :=
    (disjoint_add_off offB2b_le18 offA2_ge n).symm
  exact ⟨a2 n, b2b n, hinj₁, hinj₂, hdisj,
    image_union_eq_Icc hinj₁ hinj₂ hsub₁ hsub₂ hdisj,
    validCircle_a2 n h13, validCircle_b2b n hn h17⟩

end Cases

snip end

problem usa1990_p3 (n : ℕ) (hn : Odd n) (_hn0 : 0 < n) :
    ∃ a : Fin 14 → ℕ, ∃ b : Fin 19 → ℕ,
      Function.Injective a ∧ Function.Injective b ∧
      Disjoint (Finset.univ.image a) (Finset.univ.image b) ∧
      Finset.univ.image a ∪ Finset.univ.image b = Finset.Icc n (n + 32) ∧
      ValidCircle a ∧ ValidCircle b := by
  by_cases h13 : 13 ∣ n
  · by_cases h17 : n % 17 = 16
    · exact case2b n hn h13 h17
    · exact case2a n hn h13 h17
  · by_cases h17 : n % 17 = 2
    · exact case1b n hn h13 h17
    · exact case1a n hn h13 h17

end Usa1990P3
