import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.BigOperators.Order
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-
Canadian Mathematical Olympiad 1998, Problem 3

Let n be a natural number such that n ≥ 2. Show that

  (1/(n + 1))(1 + 1/3 + ... + 1/(2n - 1)) > (1/n)(1/2 + 1/4 + ... + 1/2n).
-/

open BigOperators

private theorem lemma1 {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : a * c > b * d) : (1 / b) * c > (1/a) * d := by
  have ha' : a ≠ 0 := (ne_of_lt ha).symm
  have hb' : b ≠ 0 := (ne_of_lt hb).symm
  have h1 : a * c / a > b * d / a := div_lt_div_of_lt ha h
  have h2 : a * c / a / b > b * d / a / b := div_lt_div_of_lt hb h1
  have h3 : a * c / a = c := mul_div_cancel_left c ha'
  rw[h3] at h2; clear h3
  ring_nf at h2
  have h4 : b * b⁻¹ = 1 := CommGroupWithZero.mul_inv_cancel b hb'
  rw[h4] at h2; clear h4
  ring_nf
  rw[one_mul] at h2
  linarith

private theorem lemma2 (f g : ℕ → ℝ) (n : ℕ) (hn : n ≠ 0)
   (h : ∀ i ∈ Finset.range n, f i < g i) :
   ∑ i in Finset.range n, f i < ∑ i in Finset.range n, g i := sorry

private theorem lemma3 (a b c d : ℝ) (h1 : b < a) (h2 : a + c = d) :
    b + c < d := by linarith

theorem canada1998_q3 (n : ℕ) (hn : 2 ≤ n) :
    (1/((n:ℝ) + 1)) * ∑ i in Finset.range n, (1/(2 * (i:ℝ) + 1)) >
    (1/(n:ℝ)) * ∑ i in Finset.range n, (1/(2 * (i:ℝ) + 2)) := by
  cases' n with n; norm_num at hn
  cases' n with n; norm_num at hn

  revert hn
  intro h2; clear h2

  -- We prove
  -- n(1 + 1/3 + ... + 1/(2n - 1)) > (n + 1)(1/2 + 1/4 + ... + 1/2n)
  -- by induction.
  suffices
   (n.succ.succ:ℝ) * ∑ i in Finset.range n.succ.succ, (1/(2 * (i:ℝ) + 1)) >
    ((n.succ.succ:ℝ) + 1) * ∑ i in Finset.range n.succ.succ, (1/(2 * (i:ℝ) + 2))
      by have h3 : 0 < (n.succ.succ:ℝ) := by norm_cast; exact Nat.zero_lt_succ _
         have h4 : 0 < (n.succ.succ:ℝ) + 1 :=
           by norm_cast; exact Nat.zero_lt_succ _
         apply lemma1 h3 h4 this

  induction n with
  | zero =>
     -- Base case: when n = 2, we have 8/3 > 9/4.
     field_simp[Finset.sum_range_succ]
     norm_num
  | succ m ih =>
    let k := m.succ.succ

    -- Inductive case: suppose claim is true for k ≥ 2. Then we have
    -- k (1 + 1/3 + ... 1/(2k - 1)) > (k + 1)(1/2 + 1/4 + ... + 1/2k).
    -- Note that
    --  (1 + 1/3 + ... + 1/(2k-1)) + (k+1)/(2k+1)
    --    = (1/2 + 1/3 + ... + 1/(2k-1)) + 1/2 + (k+1)/(2k+1)
    --    > (1/2 + 1/4 + ... + 1/2k) + 1/2 + (k+1)/(2k+1)
    --    > (1/2 + 1/4 + ... + 1/2k) + (k + 1)/(2k + 2) + 1/(2k+1)
    --    > (1/2 + 1/4 + ... + 1/2k) + (k + 2)/(2k + 2).

    have h1 : (1:ℝ) / (2 * ↑(0:ℕ) + 1) = 1 := by norm_num

    have h2 : ∀ k' ∈ Finset.range (m + 1), (1:ℝ) / (2 * ↑(k' + 1) + 1) >
                          (1:ℝ) / (2 * ↑(k' + 1) + 1 + 1) := by
      intros k' _
      apply div_lt_div_of_lt_left zero_lt_one
      · positivity
      · exact lt_add_one _

    have h3 : (∑i in Finset.range k, 1 / (2 * (i:ℝ) + 1)) + (k+1)/(2 * k + 1)
            = _ := rfl

    nth_rewrite 1 [Finset.sum_range_succ'] at h3
    rw[h1, add_assoc] at h3

    have h4 : Finset.Nonempty (Finset.range (m + 1)) :=
      Finset.nonempty_range_succ
    have h5 := Finset.sum_lt_sum_of_nonempty h4 h2

    have :=
      calc (∑i in Finset.range k, 1 / (2 * (i:ℝ) + 1)) + (k+1)/(2 * k + 1)
         = (∑i in Finset.range (m+1), 1 / (2 * ((i + 1):ℝ) + 1))
               + (1 + (k+1)/(2 * k + 1)) := by rw[←h3]; norm_cast
                                        -- TODO shouldn't need casting?
       _ > (∑i in Finset.range (m+1), 1 / (2 * ((i + 1):ℝ) + 1 + 1))
              + (1 + (k+1)/(2 * k + 1)) := sorry

    sorry

  --
  -- Then we are done because
  -- (k + 1)(1 + 1/3 + ... + 1/(2k - 1) + 1/(2k + 1))
  --  = k (1 + 1/3 + ... + 1/(2k - 1))
  --     + (1 + 1/3 + ... + 1/(2k - 1)) + (k + 1)/(2k + 1)
  --  > k(1 + 1/3 + ... + 1/(2k - 1))
  --     + (1 + 1/2 + ... + 1/2k)) + (k + 2)/(2k + 1)
  --  > (k + 2)(1/2 + 1/4 + ... + 1/(2k + 2)).

