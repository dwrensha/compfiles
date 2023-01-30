import Mathlib.Data.PNat.Basic
import Mathlib.Data.Nat.Parity
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# IMO 2013 Q1

Prove that for any pair of positive integers k and n, there exist k positive integers
m₁, m₂, ..., mₖ (not necessarily different) such that

  1 + (2ᵏ - 1)/ n = (1 + 1/m₁) * (1 + 1/m₂) * ... * (1 + 1/mₖ).

# Solution

Adaptation of the solution found in https://www.imo-official.org/problems/IMO2013SL.pdf

We prove a slightly more general version where k does not need to be strictly positive.
-/

open BigOperators

lemma prod_lemma (m : ℕ → ℕ+) (k : ℕ) (nm : ℕ+):
      ∏ i in Finset.range k, ((1 : ℚ) + 1 / ((if i < k then m i else nm)):ℚ) =
      ∏ i in Finset.range k, (1 + 1 / ((m i):ℕ)) := by
  have : ∀ i, i ∈ Finset.range k →
      (1 : ℚ) + 1 / ↑(if i < k then m i else nm) = 1 + 1 / m i := by
    intros i hi
    simp [Finset.mem_range.mp hi]
  sorry
  --exact Finset.prod_congr rfl this

theorem imo2013_q1 (n : ℕ+) (k : ℕ) :
    (∃ m : ℕ → ℕ+, (1 : ℚ) + (2^k - 1) / (n:ℚ) =
    (∏ i in Finset.range k, (1 + 1 / ((m i):ℕ)))) := by
  revert n
  induction k with
  | zero => intro n; use (fun _ ↦ 1); simp -- For the base case, any m works.
  | succ pk hpk =>
    intro n
    obtain ⟨t, ht : ↑n = t + t⟩ | ⟨t, ht : ↑n = 2 * t + 1⟩ := (n : ℕ).even_or_odd
    · -- even case
      rw [←two_mul] at ht
      cases t with -- Eliminate the zero case to simplify later calculations.
      | zero => exfalso; rw [Nat.mul_zero] at ht; exact PNat.ne_zero n ht
      | succ t =>
        -- Now we have ht : ↑n = 2 * (t + 1).
        let t_succ : ℕ+ := ⟨t + 1, t.succ_pos⟩
        obtain ⟨pm, hpm⟩ := hpk t_succ
        let m := λi => if i < pk then pm i else ⟨2 * t + 2^pk.succ, by positivity⟩
        use m
        have hmpk : (m pk : ℚ) = 2 * t + 2^pk.succ := by
          have : m pk = ⟨2 * t + 2^pk.succ, _⟩ := if_neg (irrefl pk)
          rw [this]
          norm_cast

        have denom_ne_zero : (2 * (t:ℚ) + 2^pk.succ) ≠ 0 := sorry --by positivity

--        have := calc (1 : ℚ) + (2 ^ pk.succ - 1) / ↑↑n
--            = 1 + (2 * 2 ^ pk - 1) / (2 * (t + 1) : ℕ) := by rw [ht, pow_succ]; sorry
--         _  = (1 + 1 / (2 * t + 2 * 2^pk)) *
--           (1 + (2 ^ pk - 1) / (↑t + 1))              := by sorry
/-

{ field_simp [t.cast_add_one_ne_zero],
                                                             ring }

    ... = (1 + 1 / (2 * t + 2^pk.succ)) *
          (1 + (2 ^ pk - 1) / t_succ)                 : by norm_cast
    ... = (1 + 1 / ↑(m pk)) *
          ∏ (i : ℕ) in finset.range pk, (1 + 1 / m i) : by rw [hpm, prod_lemma, ←hmpk]
    ... = ∏ (i : ℕ) in finset.range pk.succ,
                                        (1 + 1 / m i) : (finset.prod_range_succ_comm _ pk).symm
-/
        sorry
    · sorry
/-


 },
  { -- odd case
    let t_succ : ℕ+ := ⟨t + 1, t.succ_pos⟩,
    obtain ⟨pm, hpm⟩ := hpk t_succ,
    let m := λi, if i < pk then pm i else ⟨2 * t + 1, nat.succ_pos _⟩,
    use m,

    have hmpk : (m pk : ℚ) = 2 * t + 1,
    { have : m pk = ⟨2 * t + 1, _⟩ := if_neg (irrefl pk), simp [this] },

    have denom_ne_zero : (2 * (t : ℚ) + 1) ≠ 0 := by positivity,

    calc (1 : ℚ) + (2 ^ pk.succ - 1) / ↑n
        = 1 + (2 * 2^pk - 1) / (2 * t + 1 : ℕ)        : by rw [coe_coe n, ht, pow_succ]
    ... = (1 + 1 / (2 * t + 1)) *
          (1 + (2^pk - 1) / (t + 1))                  : by { field_simp [t.cast_add_one_ne_zero],
                                                             ring }
    ... = (1 + 1 / (2 * t + 1)) *
          (1 + (2^pk - 1) / t_succ)                   : by norm_cast
    ... = (1 + 1 / ↑(m pk)) *
          ∏ (i : ℕ) in finset.range pk, (1 + 1 / m i) : by rw [hpm, prod_lemma, ←hmpk]
    ... = ∏ (i : ℕ) in finset.range pk.succ,
                                        (1 + 1 / m i) : (finset.prod_range_succ_comm _ pk).symm }
end
-/
