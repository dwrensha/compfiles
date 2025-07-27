/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InternLM-MATH LEAN Formalizer v0.1
          Shahar Blumentzvaig
-/

import Mathlib.Tactic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Finset.Basic
/-!
# International Mathematical Olympiad 1975, Problem 2

Let a1 < a2 < a3 < ... be positive integers.
Prove that for every i >= 1,
there are infinitely many a_n that can be written in the form a_n = ra_i + sa_j,
with r, s positive integers and j > i.
-/

namespace Imo1975P2


lemma monotone (a : ℕ → ℤ) (ha : ∀ i : ℕ, a i < a (i + 1)) : (∀ m k : ℕ , (m>k) → (a m>a k)) := by
  intro m
  intro k
  intro h
  induction m with
  | zero => 
    exfalso
    exact Nat.not_lt_zero k h
  | succ d hd =>
    by_cases h2 : d=k
    rw [h2]
    exact ha k
    have h3 : d>k := by
      have g1 : d+1>=k +1 := Nat.lt_iff_add_one_le.mp h
      have g2 : d>=k := Nat.le_of_add_le_add_right g1
      push_neg at h2
      exact lt_of_le_of_ne g2 h2.symm
    have h4 : a (d+1) > a d := ha d
    have h5 := hd h3
    exact lt_trans h5 h4

theorem imo1975_p2 (a : ℕ → ℤ)
  (apos : ∀ i : ℕ, 0 < a i)
  (ha : ∀ i : ℕ, a i < a (i + 1)) :
    ( ∀ i n0 : ℕ ,
      ∃ n, n0 ≤ n ∧
      ∃ r s : ℕ,
      ∃ j : ℕ,
        a n = r * a i + s * a j ∧
        i < j ∧
        0 < r ∧
        0 < s ):= by
  let b : ℕ → ℕ := fun n => (a n).natAbs
  intro i
  have hn0 : ∀j:ℕ , a j ≠ (0 : ℤ) := by
    intro j
    have hn0' := apos j
    exact Ne.symm (Int.ne_of_lt hn0') 
  intro n0
  have h1 : ∃t:ℕ , ∀ n1:ℕ , ∃ n:ℕ , n>n1 ∧ a i ∣ (a n-t) := by
    by_contra h2
    push_neg at h2

    choose f hf using h2
    let m := Nat.succ (Finset.sup ((List.range (b i)).toFinset) f)
    have h3 : ∀ n>m , ∀ t:ℕ , t < b i → ¬ (a i ∣ a n - t) := by
      intro n1
      intro g
      intro t1
      intro r
      have h4 :m > f t1 := by
        have h4' : (Finset.sup (List.range (b i)).toFinset f) >= f t1 := by
          apply Finset.le_sup
          rw[List.mem_toFinset]
          exact List.mem_range.2 r
        unfold m
        apply Nat.lt_of_le_of_lt h4' (Nat.lt_succ_self ((List.range (b i)).toFinset.sup f))
      have h6 : n1 > f t1 := by exact Nat.lt_trans h4 g
      apply hf t1 n1 h6
    have h4 := h3 (m+1) (Nat.lt_add_one m)
    let t_int := a (m+1) - (a i)*((a (m+1))/(a i))
    let t := t_int.natAbs
    have g : (a i)∣ a (m+1) - (a (m+1) - (a i)*((a (m+1))/(a i))) := by
      simp
    have h5 := h4 t
    have h6 : (a i ∣ a (m + 1) - ↑t) → (t ≥ b i) := by
      contrapose
      intro r
      apply lt_of_not_ge at r
      exact h5 r
    dsimp [t] at h6
    dsimp [t_int] at h6
    have g : (a (m + 1) - a i * (a (m + 1) / a i))≥0 := by
        have r : (a i)*(a (m + 1) / a i) ≤ a (m+1) := by
          nth_rewrite 2 [← Int.ediv_add_emod (a (m+1)) (a i)]
          simp
          exact Int.emod_nonneg (a (m+1)) (hn0 (i))
        linarith
    have h7 : ↑(a (m + 1) - a i * (a (m + 1) / a i)).natAbs = (a (m + 1) - a i * (a (m + 1) / a i)) := Int.natAbs_of_nonneg g
    rw [h7] at h6
    simp at h6
    unfold b at h6
    have h8 : a (m + 1) - a i * (a (m + 1) / a i) < (a i):= by
      have h8' : a i * (a (m + 1) / a i) + (a i) > a (m + 1) :=  Int.lt_mul_ediv_self_add (apos i)
      linarith
    rw [← Int.natAbs_of_nonneg g] at h8
    nth_rewrite 3 [← Int.natAbs_of_nonneg (le_of_lt (apos i))] at h8
    simp at h8
    linarith
  obtain ⟨t,ht⟩ := h1
  have g := ht (n0+i)
  obtain ⟨k,hk⟩ := g
  rcases hk.right with ⟨x, hx⟩
  have g' := ht k
  obtain ⟨m,hm⟩ := g'
  rcases hm.right with ⟨y, hy⟩
  have g : a m = (y-x)*(a i) + (a k) := by
    calc
          a m   = (a m - t) - (a k - t)+(a k) := by ring
          _   = a i * y - a i * x +(a k)     := by rw [hy, hx]
          _   = (y - x) * a i +(a k)        := by ring
  have rm : n0 ≤ m ∧ ∃ r s j : ℕ, a m = ↑r * a i + ↑s * a j ∧ i < j ∧ 0 < r ∧ 0 < s := by
    have r1 : m ≥ n0 := by
      have r1' : m > n0+i := Nat.lt_trans hk.left hm.left
      have r1'' : m≥ n0+i := le_of_lt r1'
      have r2 : n0+i>=n0 := Nat.le_add_right n0 i
      exact le_trans r2 r1''
    have r2 : ∃ r s j : ℕ, a m = r * a i + s * a j ∧ i < j ∧ 0 < r ∧ 0 < s := by
      have s3 : 0<y-x := by
        have t1 : a m > a k := monotone a ha m k hm.left
        have t2 : a m - t > a k - t :=  add_lt_add_right t1 (-t)
        rw [hy] at t2
        rw [hx] at t2
        have t3 := (mul_lt_mul_left (apos i)).mp t2
        exact sub_pos.mpr t3
      have s : a m = (y-x) * a i + 1 * a k ∧ i < k ∧ 0 < (y - x).natAbs ∧ (0 : ℕ)<(1 : ℕ) := by
        have s1 : a m = (y-x) * a i + 1 * a k := by
          rw [g]
          ring
        have s2 : i<k := by
          have s2' : n0+i≥i := by exact Nat.le_add_left i n0
          exact lt_of_le_of_lt s2' hk.left
        
        have s4 : (0 : ℕ)<(1 : ℕ) := Nat.zero_lt_one
        have s3' : (y-x)≠0 := by
          symm
          exact ne_of_lt s3
        have s3'' := Int.natAbs_pos.mpr s3'
        exact And.intro s1 (And.intro s2 (And.intro s3'' s4))
      use (y-x).natAbs
      use 1
      use k
      have abs_eq : ↑((y - x).natAbs) = y - x := by
        rw [Int.natAbs_of_nonneg (Int.le_of_lt s3)]
      rw [abs_eq]
      exact s
    exact And.intro r1 r2
  use m
end Imo1975P2
