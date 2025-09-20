/-
Copyright (c) 2025 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lynn Van Hauwe
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!

# International Mathematical Olympiad 1974, Problem 1

Three players $A, B$ and $C$ play the following game:

* On each of three cards an integer is written.
* These three numbers $p, q, r$ satisfy $0 < p < q < r$.
* The three cards are shuffled and one is dealt to each player.
* Each then receives the number of counters indicated by the card he holds.
* Then the cards are shuffled again; the counters remain with the players.

This process (shuffling, dealing, giving out counters) takes place
for at least two rounds. After the last round, $A$ has 20 counters in all,
$B$ has 10 and $C$ has 9. At the last round $B$ received $r$ counters.

Who received $q$ counters on the first round?
-/

snip begin

/-
Translation of [this proof](https://artofproblemsolving.com/wiki/index.php/1974_IMO_Problems/Problem_1).

We'll model the `game` as a function ℕ → (Fin 3 ≃ Fin 3), mapping round
numbers to bijections between player-indices and card-indices.

Then, for example, `![p,q,r] (game k 2)` is the number of counters won by
player `2` in round `k`.
-/

snip end

namespace Imo1974P1

abbrev Player := Fin 3

determine solution : Player := 2  -- player C

problem imo1974_p1
  (p q r : ℕ)
  (hpqr : 0 < p ∧ p < q ∧ q < r)
  (n : ℕ)
  (hn : 1 < n)
  (game : ℕ → (Player ≃ Fin 3))
  (hA : ∑ k ∈ Finset.range n, ![p,q,r] (game k 0) = 20)
  (hB : ∑ k ∈ Finset.range n, ![p,q,r] (game k 1) = 10)
  (hC : ∑ k ∈ Finset.range n, ![p,q,r] (game k 2) = 9)
  (hl : ![p,q,r] (game (n-1) 1) = r)
  : game 0 solution = 1 := by

  obtain ⟨h0p, hpq, hqr⟩ := hpqr

  -- Counters won by player j in round i.
  let C i j := ![p,q,r] (game i j)

  -- Any score is at least p.
  have p_le : ∀i, p ≤ ![p,q,r] i := by
    intro i; fin_cases i <;> simp <;> omega

  -- Any score is at most r.
  have le_r : ∀i, ![p,q,r] i ≤ r := by
    intro i; fin_cases i <;> simp <;> omega

  -- Because 1 ≤ p and 2 ≤ q and 3 ≤ r, we have 6 ≤ p+q+r.
  have hs : 6 ≤ p+q+r := by omega

  -- Each round, the players win p+q+r counters in total.
  have h_total i : C i 0 + C i 1 + C i 2 = p + q + r := by
    rw [←Fin.sum_univ_three]
    unfold C
    rw [←Fintype.sum_equiv (game i)⁻¹ _ _ (fun _ ↦ rfl)]
    simp [Fin.sum_univ_three]

  -- The total score, 39, equals n(p+q+r).
  have h1 : n*(p+q+r) = 39 := calc
    _ = ∑ k ∈ Finset.range n, (p+q+r) := by simp
    _ = ∑ k ∈ Finset.range n, (C k 0 + C k 1 + C k 2) := by congr; ext i; rw [←h_total]
    _ = ∑ k ∈ Finset.range n, (C k 0)
      + ∑ k ∈ Finset.range n, (C k 1)
      + ∑ k ∈ Finset.range n, (C k 2) := by repeat rw [Finset.sum_add_distrib]
    _ = 20 + 10 + 9                   := by rw [hA, hB, hC]

  -- Thus n ∈ {1,3,13,39}.
  have h2 : n ∣ 39 := by
    rw [←h1]; apply Nat.dvd_mul_right
  have h3 : n ∈ Nat.divisors 39 := by
    apply Nat.mem_divisors.mpr; exact ⟨h2, by decide⟩

  -- In fact, n = 3, and p+q+r = 13.
  fin_cases h3 <;> try omega
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Nat.one_lt_ofNat,
    Fin.isValue, Nat.add_one_sub_one, Nat.reduceDvd] at *
  clear h2 hn
  have h4 : p+q+r = 13 := by omega

  -- Simplify the score sums.
  rw [Finset.sum] at hA hB hC
  simp only [Finset.range_val, Multiset.range_succ, Multiset.range_zero, Multiset.cons_zero,
    Fin.isValue, Multiset.map_cons, Multiset.map_singleton, Multiset.sum_cons,
    Multiset.sum_singleton] at hA hB hC
  rw [←Nat.add_assoc] at hA hB hC

  -- Show 2+r ≤ 10, and thus r ≤ 8:
  have h5 : 2+r ≤ 10 := calc
    2+r ≤ r     + p     + p     := by omega
    _   ≤ r     + C 1 1 + C 0 1 := by gcongr <;> apply p_le
    _   = C 2 1 + C 1 1 + C 0 1 := by unfold C; rw [hl]
    _   = 10                    := hB

  have h6 : r ≤ 8 := by omega

  -- Show 20 ≤ r+r+r, and thus r > 6:
  have h7 : 20 ≤ r+r+r := calc
    20 = C 2 0 + C 1 0 + C 0 0 := by unfold C; omega
    _  ≤ r+r+r                 := by gcongr <;> apply le_r

  have h8 : r > 6 := by omega

  -- Proof idea:
  -- hB claims: r + (p|q|r) + (p|q|r) = 10.
  -- But neither can be r, because r+r+... > 10.
  -- And they can't be (p,q) or (q,p) because we know 13 = r+p+q ≠ 10.
  -- So the only options are r+p+p and r+q+q.
  have h9 : r+p+p = 10 ∨ r+q+q = 10 := by sorry

  -- r = 7 leads to a contradiction. Thus r = 8:
  have hr : r = 8 := by omega

  -- Then p and q are also determined.
  have hp : p = 1 := by omega
  have hq : q = 4 := by omega

  -- Clean up now that we know (p,q,r).
  rw [hl] at hB
  rw [hp, hq, hr] at hA hB hC p_le le_r
  clear h0p hpq hqr hs h1 h4 h5 h6 h7 h8 h9 hl hp hq hr

  -- Looking at hB : 8 + G 1 1 + G 0 1 = 10
  -- we can deduce that this must be 8 + 1 + 1 = 10
  -- and so (game 1) 1 = 0 and (game 0) 1 = 0.
  have hg01 : game 0 1 = 0 := by
    generalize hg01 : game 0 1 = g01 at hB
    generalize hg11 : game 1 1 = g11 at hB
    fin_cases g01 <;> fin_cases g11 <;> simp at hB ⊢

  -- So (game 0) 2 ≠ 0 (bijective).
  have hg020 : game 0 2 ≠ 0 := by
    intro h; rw [←h] at hg01
    have := Equiv.injective (game 0) hg01
    simp only [Fin.isValue, Fin.reduceEq] at this

  -- But (game 0) 2 = 2 would make the sum in hC too big.
  have hg022 : game 0 2 ≠ 2 := by
    intro h; rw [h] at hC
    simp only [Fin.isValue, Matrix.cons_val, Nat.reduceEqDiff] at hC; grind

  -- So there is only one option left: (game 0) 2 = 1.
  unfold solution; omega

end Imo1974P1
