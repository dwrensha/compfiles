--import algebra.big_operators.intervals
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Data.Nat.Prime
import Mathlib.Algebra.Associated
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Ring

/-
Hungarian Mathematical Olympiad 1998, Problem 6

Let x, y, z be integers with z > 1. Show that

 (x + 1)² + (x + 2)² + ... + (x + 99)² ≠ yᶻ.
-/

lemma sum_range_square_mul_six (n : ℕ) :
    (∑i in Finset.range n, (i+1)^2) * 6 = n * (n + 1) * (2*n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h : n.succ = n + 1 := rfl
    rw[Finset.sum_range_succ, add_mul, ih, h]
    ring_nf

lemma sum_range_square (n : ℕ) :
    (∑i in Finset.range n, (i+1)^2) = n * (n + 1) * (2*n + 1)/6 :=
  by rw [← sum_range_square_mul_six n, Nat.mul_div_cancel]
     norm_num

lemma cast_sum_square (n : ℕ) :
  (∑i in Finset.range n, ((i:ℤ)+1)^2) =
   (((∑i in Finset.range n, (i+1)^2):ℕ) :ℤ) := by norm_cast

theorem hungary1998_q6 (x y : ℤ) (z : ℕ) (hz : 1 < z) :
    (∑ i in Finset.range 99, (x + i + 1)^2) ≠ y^z := by
  -- Suppose (x + 1)² + (x + 2)² + ... + (x + 99)² = yᶻ.

  intro he

  -- We notice that
  -- y^z = (x + 1)² + (x + 2)² + ... + (x + 99)²
  --     = 99x² + 2(1 + 2 + ... + 99)x + (1² + 2² + ... + 99²)
  --     = 99x² + 2[(99 ⬝ 100)/2]x + (99 ⬝ 100 ⬝ 199)/6
  --     = 33(3x² + 300x + 50 ⬝ 199).

  have h2 : (∑ i in Finset.range 99, (x^2)) = 99 * x^2 := by norm_num

  have h3 : (∑ i in Finset.range 99, (2 * x * ((i:ℤ) + 1))) =
         2 * x * ∑ i in Finset.range 99, ((i:ℤ) + 1) := Finset.mul_sum.symm

  have h4 : (∑ i in Finset.range 99, ((i:ℤ) + 1)) =
          ∑ i in Finset.range 100, (i:ℤ) := by
    rw[@Finset.sum_range_succ' _ _ _ 99]
    rfl

  sorry
/-
  have h5 : ∑(i : ℕ) in finset.range 100, (i:ℤ) = 99 * 100 / 2,
  { rw[← nat.cast_sum, finset.sum_range_id], norm_num},

  have h6 : ∑(i : ℕ) in finset.range 99, ((i:ℤ) + 1)^2 = (99 * 100 * 199)/6,
  { rw[cast_sum_square, sum_range_square], norm_num },

  have h7 := calc y^z
      = ∑(i : ℕ) in finset.range 99, ((x + i) + 1)^2 : he.symm
  ... = ∑(i : ℕ) in finset.range 99,
          (x^2 + 2 * x * (i + 1) + (i + 1)^2) : by {congr, funext, ring}
  ... = ∑(i : ℕ) in finset.range 99, (x^2 + 2 * x * (i + 1)) +
         ∑(i : ℕ) in finset.range 99, ((i + 1)^2) : finset.sum_add_distrib
  ... = ∑(i : ℕ) in finset.range 99, (x^2) +
          ∑(i : ℕ) in finset.range 99, (2 * x * (i + 1)) +
         ∑(i : ℕ) in finset.range 99, ((i + 1)^2) : by rw[finset.sum_add_distrib]
  ... = 99 * x^2 + 2 * x * (99 * 100 / 2) +  (99 * 100 * 199)/6
        : by rw[h2, h3, h4, h5, h6]
  ... = 3 * (11 * (3 * x^2 + 300 * x + 50 * 199)) : by {norm_num, ring},

  -- which implies that 3∣y.
  have h8 : 3 ∣ y^z := dvd.intro _ (eq.symm h7),
  have h9 : 3 ∣ y := prime.dvd_of_dvd_pow int.prime_three h8,

  obtain ⟨k,hk⟩ := h9,
  rw[hk] at h7,
  cases z, { exact nat.not_lt_zero 1 hz },
  cases z, { exact nat.lt_asymm hz hz },
  rw[pow_succ,pow_succ] at h7,

  -- Since z ≥ 2, 3²∣yᶻ, but 3² does not divide
  -- 33(3x² + 300x + 50 ⬝ 199), contradiction.

  have h10 : 3 * k * (3 * k * (3 * k) ^ z) = 3 * (k * (3 * k * (3 * k) ^ z))
       := by ring,
  rw[h10] at h7,

  have h11 : (3:ℤ) ≠ 0 := by norm_num,

  have h12 : k * (3 * k * (3 * k) ^ z) = (11 * (3 * x ^ 2 + 300 * x + 50 * 199)),
  { exact (mul_right_inj' h11).mp h7 },

  have h14 : (k * (3 * k * (3 * k) ^ z)) = (3 * (k * k * (3 * k) ^ z)) :=
    by ring,
  have h16 : 11 * (3 * x ^ 2 + 300 * x + 50 * 199) =
    3 * (11 * (x ^ 2 + 100 * x + 3316) + 7) + 1 := by ring,

  rw[h14,h16] at h12,

  have h18 : (3 * (k * k * (3 * k) ^ z)) % 3 =
    (3 * (11 * (x ^ 2 + 100 * x + 3316) + 7) + 1) % 3 :=
    congr_fun (congr_arg has_mod.mod h12) 3,

  have h19 : (3 * (11 * (x ^ 2 + 100 * x + 3316) + 7) + 1) % 3 =
   (((3 * (11 * (x ^ 2 + 100 * x + 3316) + 7))% 3) + (1%3)) % 3 :=
   int.add_mod _ _ _,
  rw[h19] at h18,
  norm_num at h18

-/
