/- Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: spertuzz -/

-- Imports
module

public import Mathlib.Tactic
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Algebra, .NumberTheory] }

namespace Ibero2026P4

-- Proof written by spertuzz

/- This problem is from the

2026 Olimpiada Iberoamericana de Matemáticas (Iberoamerican Mathematical Olympiad) in Buenos Aires

For some background information, this olympiad takes place every year inviting contestants across South
and Central America (plus Spain and Portugal) to compete in a 6-problem test over 2 days.

Specifically, this is Problem 4; the easiest on Day 2. -/

/-! PROBLEM STATEMENT

A sequence a 1, a 2, a 3, ... of positive integers is porteña if it satisfies these conditions:

(i) a 1 < a 2 < a 3 < ...
(ii) 2 * a n - n is a perfect square for all n ≥ 1
(iii) a (n - 1) + a n ≤ n ^ 2 for all n ≥ 2

Determine all porteña sequences.

(Note that, in the code, the sequence has been reindexed to start at 0. This was done in order to avoid
possible issues with using subtraction in ℕ.) -/

-- Conditions for a valid sequence
def porteña_seq (a : ℕ → ℕ) : Prop :=
  1 ≤ a 0 ∧
  StrictMono a ∧  -- Sequence is increasing
  (∀ n : ℕ, ∃ k : ℕ, 2 * a n = (n + 1) + k ^ 2) ∧
  (∀ n : ℕ, a n + a (n + 1) ≤ (n + 2) ^ 2)

snip begin

-- Product of two consecutive integers is even
lemma succ_mul_even (n : ℕ) : 2 ∣ n * (n + 1) := by
  -- Split between even and odd n
  by_cases h : 2 ∣ n
  case pos =>  -- Even n
    apply dvd_mul_of_dvd_left h (n + 1)  -- Multiply by (n + 1) and it's exact
  case neg =>  -- Odd n
    -- Derive (n + 1) % 2 = 0
    have h1 : (n + 1) % 2 = 0 := by omega
    have h2 : 2 ∣ (n + 1) := by omega
    apply dvd_mul_of_dvd_right h2 n  -- Multiply by n to finish

-- Useful lemma to simplify later parts: converts certain sequence equalities into a ℕ-friendly format
lemma convert_to_double (a n : ℕ) (h : a = (n + 1) * (n + 2) / 2) : 2 * a = (n + 1) * (n + 2) := by
  have ht := succ_mul_even (n + 1)  -- Gather known divisibility info for cancellation
  -- Rewrite in the desired form
  rw [add_assoc] at ht
  norm_num at ht
  replace ht : (n + 1) * (n + 2) % 2 = 0 := by omega
  omega

-- Lemma used to convert the standard, repeated hypotheses into a more useful, ℕ-friendly format
lemma instant_convert (a : ℕ → ℕ) (ha : ∀ n : ℕ, a n = (n + 1) * (n + 2) / 2) (n : ℕ) :
  2 * a n = (n + 1) * (n + 2) := by
  have hn := ha n
  replace hn := convert_to_double (a n) n hn
  trivial

-- Forwards statement (porteña → a n = (n + 1) * (n + 2) / 2)
theorem p4_forward (a : ℕ → ℕ) (ha : porteña_seq a) : ∀ n : ℕ, a n = (n + 1) * (n + 2) / 2 := by
  -- Extract relevant conditions
  obtain ⟨h_one, h_mono, h_sq, h_lim⟩ := ha
  intro n
  -- Perform induction over all n
  induction n with
  | zero =>  -- Case for n = 0 (n = 1 in the original statement)
    -- Gather conditions for base case and modify
    norm_num
    have h1 := h_sq 0
    have h2 := h_lim 0
    norm_num at h1
    norm_num at h2
    -- Convert all variables to a 0
    have h_size : a 0 < a 1 := h_mono (Nat.lt_succ_self 0)
    rw [← Nat.add_one_le_iff] at h_size
    have h3 : 2 * a 0 + 1 ≤ 4 := by linarith
    -- Split between a 0 = 1 and a 0 ≥ 2
    by_cases h : a 0 ≤ 1
    case pos =>
      -- Trivial
      linarith
    case neg =>
      -- Rewrite inequality to be impossible
      rw [not_le, ← Nat.add_one_le_iff] at h
      have h4 : 5 ≤ 4 := by linarith
      omega
  | succ n hn =>  -- n ≥ 1 (or n ≥ 2 in the original statement)
    -- Gather conditions for base case and alter
    have h1 := h_sq (n + 1)
    rcases h1 with ⟨k, hk⟩
    have h2 := h_lim n
    rw [hn] at h2
    -- Rewrite inequality at h2 to obtain an upper bound in terms of only n
    replace h2 : (n + 1) * (n + 2) + 2 * a (n + 1) ≤ 2 * (n + 2) ^ 2 := by  -- Cancel 2 using divisibility
      have h_temp := convert_to_double (a n) n hn
      omega
    replace h2 : 2 * a (n + 1) ≤ (n + 2) * (n + 3) := by linarith  -- Convenient rewrite
    -- Split into a range of cases (I didn't know about case intervals ☺)
    by_cases h_end : k ≤ n + 1  -- Split across n + 1
    case pos =>  -- Case for the square being at most (n + 1) ^ 2 (no solution)
      -- Rewrite into a convenient inequality with a lower bound for 2 * a (n + 1)
      replace hk : 2 * a (n + 1) ≤ n + 2 + (n + 1) ^ 2 := by nlinarith
      have h_done : (n + 1) * (n + 2) + 2 ≤ 2 * a (n + 1) := by
        have h_temp : a n < a (n + 1) := h_mono (Nat.lt_succ_self n)
        rw [← Nat.add_one_le_iff, hn] at h_temp
        have h_div := succ_mul_even (n + 1)
        replace h_div : (n + 1) * (n + 1 + 1) % 2 = 0 := by omega
        rw [add_assoc] at h_div
        norm_num at h_div
        omega
      -- Use transitivity to mix upper and lower bounds into an impossible inequality
      have h_trans : (n + 1) * (n + 2) + 2 ≤ n + 2 + (n + 1) ^ 2 := by linarith
      nlinarith
    case neg =>  -- Case for the square being at least (n + 2) ^ 2
      -- Convenient rewrites
      rw [not_le, ← Nat.add_one_le_iff] at h_end
      replace h_end : n + 2 ≤ k := by linarith
      -- Split the current interval again across n + 2 to separate all relevant cases
      by_cases h_t : k ≤ n + 2
      case pos =>  -- Case for the square being (n + 2) ^ 2 (solution)
        have h_t1 : k = n + 2 := by omega  -- Show the inequalities simplify to this equality (trivial)
        -- Rewrite and finish
        rw [h_t1] at hk
        replace h_t1 : 2 * a (n + 1) = (n + 2) * (n + 3) := by linarith
        repeat rw [add_assoc]
        norm_num
        omega
      case neg =>  -- Case for the square being at least (n + 3) ^ 2 (no solution)
        -- Obtain convenient lower bound for 2 * a (n + 1)
        rw [not_le, ← Nat.add_one_le_iff] at h_t
        replace h_t : n + 3 ≤ k := by linarith
        have h_final : n + 2 + (n + 3) ^ 2 ≤ 2 * a (n + 1) := by nlinarith
        -- Mix lower bound with upper bound to obtian an impossible inequality
        replace h_final : n + 2 + (n + 3) ^ 2 ≤ (n + 2) * (n + 3) := by linarith
        replace h_final : n + 3 ≤ n + 2 := by linarith
        omega
  -- All cases are solved so the proof is over and the only candidates are proven to be a n = (n + 1) * (n + 2) / 2

-- Backwards statement (a n = (n + 1) * (n + 2) / 2 → porteña)
theorem p4_backward (a : ℕ → ℕ) (ha : ∀ n : ℕ, a n = (n + 1) * (n + 2) / 2) : porteña_seq a := by
  refine ⟨?_, ?_, ?_, ?_⟩  -- Retrieve individual goals
  -- Goal 1: 1 ≤ a 0
  · have h0 := ha 0
    norm_num at h0
    omega  -- Trivial
  -- Goal 2: m < n → a m < a n (strictly increasing)
  · intro m n h_size  -- Gather variables with size constraint
    -- Obtain relevant hypotheses by substituting variables
    have hm := instant_convert a ha m
    have hn := instant_convert a ha n
    rw [← Nat.mul_lt_mul_left (a := 2) (by positivity), hm, hn]
    nlinarith  -- Trivial
  -- Goal 3: ∃ k, 2 * a n = n + 1 + k ^ 2
  · intro n
    use n + 1  -- Substitute the correct value for k (so the square is (n + 1) ^ 2)
    have hn := instant_convert a ha n
    rw [hn]
    nlinarith  -- Trivial from here
  -- Goal 4: a n + a (n + 1) ≤ (n + 2) ^ 2
  · intro n
    -- Reorder into an ℕ-friendly format
    rw [← mul_le_mul_iff_right₀ (by positivity : 0 < 2), Nat.mul_add]
    have hn := instant_convert a ha n
    have hn1 := instant_convert a ha (n + 1)
    rw [hn, hn1]
    nlinarith  -- Trivial

snip end

-- Solution set (a n = (n + 1) * (n + 2) / 2)
determine sols : Set (ℕ → ℕ) := { fun n => (n + 1) * (n + 2) / 2 }

problem ibero_2026_p4 (a : ℕ → ℕ) : porteña_seq a ↔ a ∈ sols := by
  simp only [sols, Set.mem_singleton_iff, funext_iff]
  constructor  -- Split into both directions and end with the proofs
  · apply p4_forward
  · apply p4_backward
  -- The proofs for these cases were already written and thus this problem is solved. ■

end Ibero2026P4
