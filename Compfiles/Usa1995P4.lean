/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.ConditionallyCompleteOrder
public import Mathlib.Data.Int.Star
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.Ring.Compare
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Algebra, .NumberTheory] }

/-!
# USA Mathematical Olympiad 1995, Problem 4

a₀, a₁, a₂, ... is an infinite sequence of integers such that aₙ - aₘ is
divisible by n - m for all (unequal) n and m. For some polynomial p(x) we have
p(n) > |aₙ| for all n. Show that there is a polynomial q(x) such that
q(n) = aₙ for all n.
-/

namespace Usa1995P4

open Polynomial

snip begin

/-- `gcd (lcm over s) x` divides the product of the individual gcds. -/
lemma gcd_lcm_dvd_prod_gcd (t : ℕ → ℕ) (x : ℕ) (s : Finset ℕ) :
    (∀ i ∈ s, 0 < t i) → Nat.gcd (s.lcm t) x ∣ ∏ i ∈ s, Nat.gcd (t i) x := by
  induction s using Finset.induction_on with
  | empty =>
    intro _
    rw [Finset.lcm_empty, Nat.gcd_one_left, Finset.prod_empty]
  | insert a s ha ih =>
    intro hpos
    rw [Finset.lcm_insert, Finset.prod_insert ha]
    have h1 : Nat.gcd (lcm (t a) (s.lcm t)) x ∣ Nat.gcd (t a * s.lcm t) x :=
      Nat.dvd_gcd ((Nat.gcd_dvd_left _ _).trans (lcm_dvd_mul _ _)) (Nat.gcd_dvd_right _ _)
    have h2 : Nat.gcd (t a * s.lcm t) x ∣ Nat.gcd (t a) x * Nat.gcd (s.lcm t) x :=
      Nat.gcd_mul_left_dvd_mul_gcd x (t a) (s.lcm t)
    have h3 : Nat.gcd (s.lcm t) x ∣ ∏ i ∈ s, Nat.gcd (t i) x :=
      ih (fun i hi => hpos i (Finset.mem_insert_of_mem hi))
    exact h1.trans (h2.trans (Nat.mul_dvd_mul_left _ h3))

/-- Exact factorization: a product of naturals equals their lcm times the product of
the gcds of the successive partial lcms with the next factor. -/
lemma prod_eq_lcm_mul_gcd_prod (t : ℕ → ℕ) (k : ℕ) :
    ∏ i ∈ Finset.range (k + 1), t i =
      (Finset.range (k + 1)).lcm t *
        ∏ j ∈ Finset.range k, Nat.gcd ((Finset.range (j + 1)).lcm t) (t (j + 1)) := by
  induction k with
  | zero =>
    rw [Finset.prod_range_succ t 0, Finset.prod_range_zero, Finset.prod_range_zero,
      one_mul, mul_one,
      show Finset.range (0 + 1) = insert 0 (Finset.range 0) from Finset.range_add_one,
      Finset.lcm_insert, Finset.range_zero, Finset.lcm_empty, lcm_eq_nat_lcm,
      Nat.lcm_one_right]
  | succ k ih =>
    rw [Finset.prod_range_succ t (k + 1), ih,
      Finset.prod_range_succ (fun j => Nat.gcd ((Finset.range (j + 1)).lcm t) (t (j + 1))) k,
      show Finset.range (k + 1 + 1) = insert (k + 1) (Finset.range (k + 1)) from
        Finset.range_add_one,
      Finset.lcm_insert, lcm_eq_nat_lcm]
    have h2 : t (k + 1) * (Finset.range (k + 1)).lcm t =
        Nat.gcd ((Finset.range (k + 1)).lcm t) (t (k + 1)) *
          Nat.lcm (t (k + 1)) ((Finset.range (k + 1)).lcm t) := by
      have h := Nat.gcd_mul_lcm (t (k + 1)) ((Finset.range (k + 1)).lcm t)
      rw [Nat.gcd_comm] at h
      exact h.symm
    rw [show ((Finset.range (k + 1)).lcm t *
            ∏ j ∈ Finset.range k, Nat.gcd ((Finset.range (j + 1)).lcm t) (t (j + 1))) *
          t (k + 1) =
        (t (k + 1) * (Finset.range (k + 1)).lcm t) *
          ∏ j ∈ Finset.range k, Nat.gcd ((Finset.range (j + 1)).lcm t) (t (j + 1)) from
        by ring, h2]
    ring

/-- Each step gcd is at most `N ^ (j + 1)`, since `gcd (m - i) (m - (j+1))` divides
`(j + 1) - i ≤ N` for every `i < j + 1`. -/
lemma gcd_lcm_le_pow (m N j : ℕ) (hm : N < m) (hj : j ∈ Finset.range N) :
    Nat.gcd ((Finset.range (j + 1)).lcm (fun i => m - i)) (m - (j + 1)) ≤ N ^ (j + 1) := by
  have _hjN : j + 1 ≤ N := Finset.mem_range.mp hj
  have hpos : ∀ i ∈ Finset.range (j + 1), 0 < m - i := by
    intro i hi
    have _hi' : i < j + 1 := Finset.mem_range.mp hi
    lia
  have hdvd := gcd_lcm_dvd_prod_gcd (fun i => m - i) (m - (j + 1)) (Finset.range (j + 1)) hpos
  have hprod_pos : 0 < ∏ i ∈ Finset.range (j + 1), Nat.gcd (m - i) (m - (j + 1)) :=
    Finset.prod_pos (fun i hi => Nat.gcd_pos_of_pos_left _ (hpos i hi))
  have hbound : ∀ i ∈ Finset.range (j + 1), Nat.gcd (m - i) (m - (j + 1)) ≤ N := by
    intro i hi
    have _hi' : i < j + 1 := Finset.mem_range.mp hi
    have hsub : (m - i) - (m - (j + 1)) = (j + 1) - i := by lia
    have hd : Nat.gcd (m - i) (m - (j + 1)) ∣ (j + 1) - i := by
      rw [← hsub]
      exact Nat.dvd_sub (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _)
    exact (Nat.le_of_dvd (by lia) hd).trans (by lia)
  calc Nat.gcd ((Finset.range (j + 1)).lcm (fun i => m - i)) (m - (j + 1))
      ≤ ∏ i ∈ Finset.range (j + 1), Nat.gcd (m - i) (m - (j + 1)) :=
        Nat.le_of_dvd hprod_pos hdvd
    _ ≤ N ^ (Finset.range (j + 1)).card := Finset.prod_le_pow_card _ _ _ hbound
    _ = N ^ (j + 1) := by rw [Finset.card_range]

/-- A lower bound for the lcm of the `N + 1` consecutive integers
`m, m - 1, ..., m - N`: their product is at most `N ^ (N * (N + 1))` times
their lcm. -/
lemma prod_le_lcm_mul_pow (N m : ℕ) (hm : N < m) :
    ∏ i ∈ Finset.range (N + 1), (m - i) ≤
      ((Finset.range (N + 1)).lcm fun i => m - i) * N ^ (N * (N + 1)) := by
  rcases Nat.eq_zero_or_pos N with rfl | _hN
  · rw [Finset.prod_range_succ _ 0, Finset.prod_range_zero, one_mul,
      show Finset.range (0 + 1) = insert 0 (Finset.range 0) from Finset.range_add_one,
      Finset.lcm_insert, Finset.range_zero, Finset.lcm_empty, lcm_eq_nat_lcm,
      Nat.lcm_one_right]
    simp
  · have hid := prod_eq_lcm_mul_gcd_prod (fun i => m - i) N
    have hG : ∏ j ∈ Finset.range N,
          Nat.gcd ((Finset.range (j + 1)).lcm (fun i => m - i)) (m - (j + 1)) ≤
        ∏ j ∈ Finset.range N, N ^ (j + 1) :=
      Finset.prod_le_prod (fun i _ => Nat.zero_le _) (fun j hj => gcd_lcm_le_pow m N j hm hj)
    rw [Finset.prod_pow_eq_pow_sum] at hG
    have hexp : (∑ j ∈ Finset.range N, (j + 1)) ≤ N * (N + 1) :=
      calc (∑ j ∈ Finset.range N, (j + 1)) ≤ (Finset.range N).card • N :=
            Finset.sum_le_card_nsmul _ _ _ (fun j hj => Finset.mem_range.mp hj)
        _ = N * N := by rw [Finset.card_range, smul_eq_mul]
        _ ≤ N * (N + 1) := Nat.mul_le_mul_left N (Nat.le_succ N)
    calc ∏ i ∈ Finset.range (N + 1), (m - i)
        = (Finset.range (N + 1)).lcm (fun i => m - i) *
            ∏ j ∈ Finset.range N,
              Nat.gcd ((Finset.range (j + 1)).lcm (fun i => m - i)) (m - (j + 1)) := hid
      _ ≤ (Finset.range (N + 1)).lcm (fun i => m - i) * N ^ (N * (N + 1)) :=
            Nat.mul_le_mul_left _ (hG.trans (pow_le_pow_right' (by lia) hexp))


/-- Lagrange interpolation (over ℚ): the first `N + 1` values of an integer
sequence are interpolated by a rational polynomial of degree at most `N`. -/
lemma interpolate_exists (a : ℕ → ℤ) (N : ℕ) :
    ∃ q : ℚ[X], q.natDegree ≤ N ∧ ∀ i : ℕ, i ≤ N → q.eval (i : ℚ) = (a i : ℚ) := by
  have hinj : Set.InjOn (fun i : ℕ => (i : ℚ)) (↑(Finset.range (N + 1))) :=
    fun i _ j _ h => by
      have h' : (i : ℚ) = (j : ℚ) := h
      exact_mod_cast h'
  refine ⟨Lagrange.interpolate (Finset.range (N + 1)) (fun i : ℕ => (i : ℚ))
      (fun i : ℕ => (a i : ℚ)), ?_, ?_⟩
  · have hdeg := Lagrange.degree_interpolate_lt (r := fun i : ℕ => (a i : ℚ)) hinj
    rw [Finset.card_range] at hdeg
    by_cases hq0 : Lagrange.interpolate (Finset.range (N + 1)) (fun i : ℕ => (i : ℚ))
        (fun i : ℕ => (a i : ℚ)) = 0
    · simp [hq0]
    · have h2 := (Polynomial.natDegree_lt_iff_degree_lt hq0).mpr hdeg
      exact Nat.lt_succ_iff.mp h2
  · intro i hi
    rw [Lagrange.eval_interpolate_at_node (r := fun i : ℕ => (a i : ℚ)) hinj
      (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hi))]

/-- The product of the denominators of the coefficients of `q` of degree at
most `N`. Scaling `q` by this natural number clears the denominators. -/
def denomProd (q : ℚ[X]) (N : ℕ) : ℕ := ∏ i ∈ Finset.range (N + 1), (q.coeff i).den

/-- The (integer) coefficients of `denomProd q N • q`. -/
def clearCoeff (q : ℚ[X]) (N : ℕ) (i : ℕ) : ℤ :=
  ((denomProd q N : ℚ) * q.coeff i).num

/-- The integer polynomial obtained from `q : ℚ[X]` by clearing denominators:
its coefficients are `clearCoeff q N`, so it agrees with `denomProd q N • q`
on all evaluations. -/
noncomputable def clearPoly (q : ℚ[X]) (N : ℕ) : ℤ[X] :=
  ∑ i ∈ Finset.range (N + 1), Polynomial.monomial i (clearCoeff q N i)

lemma denomProd_pos (q : ℚ[X]) (N : ℕ) : 0 < denomProd q N :=
  Finset.prod_pos fun _ _ => Rat.den_pos _

/-- The defining property of `clearCoeff`: as rationals, `clearCoeff q N i`
equals `denomProd q N * q.coeff i` (for `i ≤ N`). -/
lemma clearCoeff_spec (q : ℚ[X]) (N : ℕ) {i : ℕ} (hi : i ∈ Finset.range (N + 1)) :
    ((clearCoeff q N i : ℤ) : ℚ) = (denomProd q N : ℚ) * q.coeff i := by
  obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem (fun j => (q.coeff j).den) hi
  have h3 : (denomProd q N : ℚ) = ((q.coeff i).den : ℚ) * (k : ℚ) := by exact_mod_cast hk
  have h1 : ((denomProd q N : ℚ) * q.coeff i) = (((k : ℤ) * (q.coeff i).num : ℤ) : ℚ) := by
    rw [h3]
    calc ((q.coeff i).den : ℚ) * (k : ℚ) * q.coeff i
        = (k : ℚ) * (q.coeff i * ((q.coeff i).den : ℚ)) := by ring
      _ = (k : ℚ) * ((q.coeff i).num : ℚ) := by rw [Rat.mul_den_eq_num]
      _ = (((k : ℤ) * (q.coeff i).num : ℤ) : ℚ) := by push_cast; ring
  have h4 : clearCoeff q N i = k * (q.coeff i).num := by
    show ((denomProd q N : ℚ) * q.coeff i).num = _
    rw [h1]
    exact Rat.num_intCast _
  rw [h4]
  exact h1.symm

lemma clearPoly_eval (q : ℚ[X]) (N : ℕ) (x : ℤ) :
    (clearPoly q N).eval x = ∑ i ∈ Finset.range (N + 1), clearCoeff q N i * x ^ i := by
  rw [clearPoly, Polynomial.eval_finsetSum]
  exact Finset.sum_congr rfl fun i _ => by rw [Polynomial.eval_monomial]

/-- Evaluating the cleared polynomial gives `denomProd q N` times the
evaluation of `q` (as rational numbers). -/
lemma clearPoly_eval_cast (q : ℚ[X]) {N : ℕ} (hqN : q.natDegree ≤ N) (m : ℕ) :
    (((clearPoly q N).eval (m : ℤ) : ℤ) : ℚ) = (denomProd q N : ℚ) * q.eval (m : ℚ) := by
  rw [clearPoly_eval, Int.cast_sum]
  rw [Finset.sum_congr rfl (fun i hi => by
    rw [Int.cast_mul, Int.cast_pow, Int.cast_natCast, clearCoeff_spec q N hi, mul_assoc])]
  rw [← Finset.mul_sum,
    ← Polynomial.eval_eq_sum_range' (Nat.lt_succ_iff.mpr hqN) (m : ℚ)]

/-- At the interpolation nodes `i ≤ N`, the cleared polynomial takes the value
`denomProd q N * a i`. -/
lemma clearPoly_node (a : ℕ → ℤ) {q : ℚ[X]} {N : ℕ} (hqN : q.natDegree ≤ N)
    (hqval : ∀ i : ℕ, i ≤ N → q.eval (i : ℚ) = (a i : ℚ)) {i : ℕ} (hi : i ≤ N) :
    (clearPoly q N).eval (i : ℤ) = (denomProd q N : ℤ) * a i := by
  have h := clearPoly_eval_cast q hqN i
  rw [hqval i hi] at h
  have h2 : ((denomProd q N : ℚ) * ((a i : ℤ) : ℚ)) =
      (((denomProd q N : ℤ) * a i : ℤ) : ℚ) := by push_cast; ring
  rw [h2] at h
  exact_mod_cast h

/-- The difference `clearPoly q N ⬝ m - denomProd q N * a m` is divisible by
`m - i` for every `i ≤ N`. -/
lemma clearPoly_dvd (a : ℕ → ℤ) (hdiv : ∀ n m : ℕ, ((n : ℤ) - (m : ℤ)) ∣ a n - a m)
    {q : ℚ[X]} {N : ℕ} (hqN : q.natDegree ≤ N)
    (hqval : ∀ i : ℕ, i ≤ N → q.eval (i : ℚ) = (a i : ℚ)) (m : ℕ) {i : ℕ}
    (hi : i ∈ Finset.range (N + 1)) :
    ((m : ℤ) - (i : ℤ)) ∣ (clearPoly q N).eval (m : ℤ) - (denomProd q N : ℤ) * a m := by
  have h1 : ((m : ℤ) - (i : ℤ)) ∣
      (clearPoly q N).eval (m : ℤ) - (clearPoly q N).eval (i : ℤ) :=
    Polynomial.sub_dvd_eval_sub _ _ _
  have h2 : (clearPoly q N).eval (i : ℤ) = (denomProd q N : ℤ) * a i :=
    clearPoly_node a hqN hqval (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
  have h3 : ((m : ℤ) - (i : ℤ)) ∣ a m - a i := hdiv m i
  have h4 : ((m : ℤ) - (i : ℤ)) ∣
      ((clearPoly q N).eval (m : ℤ) - (clearPoly q N).eval (i : ℤ)) -
        (denomProd q N : ℤ) * (a m - a i) :=
    dvd_sub h1 (dvd_mul_of_dvd_right h3 _)
  have h5 : (clearPoly q N).eval (m : ℤ) - (denomProd q N : ℤ) * a m =
      ((clearPoly q N).eval (m : ℤ) - (clearPoly q N).eval (i : ℤ)) -
        (denomProd q N : ℤ) * (a m - a i) := by
    rw [h2]; ring
  rwa [h5]

/-- A sum of the form `∑ c i * m ^ i` with `m ≥ 1` grows at most like
`m ^ N`. -/
lemma sum_pow_abs_le (c : ℕ → ℤ) (N : ℕ) (m : ℕ) (hm : 1 ≤ m) :
    |∑ i ∈ Finset.range (N + 1), c i * (m : ℤ) ^ i| ≤
      ((∑ i ∈ Finset.range (N + 1), (c i).natAbs : ℕ) : ℤ) * (m : ℤ) ^ N := by
  have hm0 : (0 : ℤ) ≤ (m : ℤ) := by positivity
  calc |∑ i ∈ Finset.range (N + 1), c i * (m : ℤ) ^ i|
      ≤ ∑ i ∈ Finset.range (N + 1), |c i * (m : ℤ) ^ i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ Finset.range (N + 1), |c i| * (m : ℤ) ^ i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [abs_mul, abs_pow, abs_of_nonneg hm0]
    _ ≤ ∑ i ∈ Finset.range (N + 1), |c i| * (m : ℤ) ^ N := by
        refine Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        have h : m ^ i ≤ m ^ N :=
          pow_le_pow_right' (by lia) (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
        exact_mod_cast h
    _ = ((∑ i ∈ Finset.range (N + 1), (c i).natAbs : ℕ) : ℤ) * (m : ℤ) ^ N := by
        simp only [Int.abs_eq_natAbs]
        rw [← Finset.sum_mul, ← Nat.cast_sum]

/-- The evaluation of an integer polynomial at `m ≥ 1` is bounded by a
constant times `m ^ natDegree`. -/
lemma abs_eval_le (p : ℤ[X]) (m : ℕ) (hm : 1 ≤ m) :
    |p.eval (m : ℤ)| ≤
      ((∑ i ∈ Finset.range (p.natDegree + 1), (p.coeff i).natAbs : ℕ) : ℤ) *
        (m : ℤ) ^ p.natDegree := by
  rw [Polynomial.eval_eq_sum_range]
  exact sum_pow_abs_le p.coeff p.natDegree m hm

/-- Key step: for large `m`, the cleared polynomial agrees with
`denomProd q N * a m`. The difference is divisible by the lcm of
`m, m - 1, ..., m - N`, which (being larger than the product of the growth
bounds) forces the difference to vanish. -/
lemma clearPoly_eq_of_large (a : ℕ → ℤ)
    (hdiv : ∀ n m : ℕ, ((n : ℤ) - (m : ℤ)) ∣ a n - a m)
    {q : ℚ[X]} {N : ℕ} (hqN : q.natDegree ≤ N)
    (hqval : ∀ i : ℕ, i ≤ N → q.eval (i : ℚ) = (a i : ℚ))
    {C C₁ : ℕ}
    (hC : ∀ m : ℕ, 1 ≤ m → |(clearPoly q N).eval (m : ℤ)| ≤ (C : ℤ) * (m : ℤ) ^ N)
    (hC₁ : ∀ m : ℕ, 1 ≤ m → |a m| ≤ (C₁ : ℤ) * (m : ℤ) ^ N)
    (m : ℕ) (hm : 2 * N < m)
    (hmB : 2 ^ (N + 1) * N ^ (N * (N + 1)) * (C + denomProd q N * C₁) < m) :
    (clearPoly q N).eval (m : ℤ) = (denomProd q N : ℤ) * a m := by
  have hmN : N < m := by lia
  have hm1 : 1 ≤ m := by lia
  set Z : ℤ := (clearPoly q N).eval (m : ℤ) - (denomProd q N : ℤ) * a m with hZ
  by_contra hne
  have hZne : Z ≠ 0 := by rw [hZ]; exact sub_ne_zero.mpr hne
  -- The lcm of `m, m - 1, ..., m - N` divides `Z`.
  have hpoint : ∀ i ∈ Finset.range (N + 1), (m - i) ∣ Z.natAbs := by
    intro i hi
    have h1 := clearPoly_dvd a hdiv hqN hqval m hi
    have h2 : ((m - i : ℕ) : ℤ) = (m : ℤ) - (i : ℤ) :=
      Nat.cast_sub (by have hi' : i < N + 1 := Finset.mem_range.mp hi; lia)
    rw [← h2] at h1
    have h3 := (Int.natAbs_dvd_natAbs).mpr h1
    rwa [Int.natAbs_natCast] at h3
  have hLlcm : (Finset.range (N + 1)).lcm (fun i => m - i) ∣ Z.natAbs :=
    Finset.lcm_dvd hpoint
  have hLle : (Finset.range (N + 1)).lcm (fun i => m - i) ≤ Z.natAbs :=
    Nat.le_of_dvd (Int.natAbs_pos.mpr hZne) hLlcm
  -- The lcm is large: at least `(m - N) ^ (N + 1) / N ^ (N * (N + 1))`.
  have hprod := prod_le_lcm_mul_pow N m hmN
  have hconsec : (m - N) ^ (N + 1) ≤ ∏ i ∈ Finset.range (N + 1), (m - i) := by
    have h1 : (m - N) ^ (N + 1) = ∏ i ∈ Finset.range (N + 1), (m - N) := by
      rw [Finset.prod_const, Finset.card_range]
    rw [h1]
    refine Finset.prod_le_prod (fun i _ => Nat.zero_le _) (fun i hi => ?_)
    have hi' : i < N + 1 := Finset.mem_range.mp hi
    exact Nat.sub_le_sub_left (by lia) m
  have hkey : m ^ (N + 1) ≤ 2 ^ (N + 1) * (m - N) ^ (N + 1) := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (Nat.zero_le _) (by lia) (N + 1)
  have hcomb : m ^ (N + 1) ≤
      2 ^ (N + 1) * (((Finset.range (N + 1)).lcm fun i => m - i) * N ^ (N * (N + 1))) :=
    le_trans hkey (le_trans (mul_le_mul_right hconsec _) (mul_le_mul_right hprod _))
  -- But `Z.natAbs` is small: at most `(C + Q * C₁) * m ^ N`.
  have hZle : (((Finset.range (N + 1)).lcm fun i => m - i : ℕ) : ℤ) ≤ |Z| := by
    rw [Int.abs_eq_natAbs]
    exact_mod_cast hLle
  have hZup : |Z| ≤ ((C + denomProd q N * C₁ : ℕ) : ℤ) * (m : ℤ) ^ N := by
    rw [hZ]
    have hsub : |(clearPoly q N).eval (m : ℤ) - (denomProd q N : ℤ) * a m| ≤
        |(clearPoly q N).eval (m : ℤ)| + |(denomProd q N : ℤ) * a m| := by
      have h := abs_add_le ((clearPoly q N).eval (m : ℤ)) (-((denomProd q N : ℤ) * a m))
      rwa [abs_neg, ← sub_eq_add_neg] at h
    refine hsub.trans ?_
    calc |(clearPoly q N).eval (m : ℤ)| + |(denomProd q N : ℤ) * a m|
        ≤ (C : ℤ) * (m : ℤ) ^ N + (denomProd q N : ℤ) * ((C₁ : ℤ) * (m : ℤ) ^ N) := by
          have h2 : |(denomProd q N : ℤ) * a m| ≤
              (denomProd q N : ℤ) * ((C₁ : ℤ) * (m : ℤ) ^ N) := by
            rw [abs_mul, abs_of_nonneg (by exact_mod_cast Nat.zero_le (denomProd q N))]
            exact mul_le_mul_of_nonneg_left (hC₁ m hm1) (by exact_mod_cast Nat.zero_le _)
          exact add_le_add (hC m hm1) h2
      _ = ((C + denomProd q N * C₁ : ℕ) : ℤ) * (m : ℤ) ^ N := by push_cast; ring
  -- Combining the bounds gives `m ^ (N + 1) ≤ B * m ^ N`, hence `m ≤ B`:
  -- contradiction.
  have hcombZ0 : ((m ^ (N + 1) : ℕ) : ℤ) ≤
      ((2 ^ (N + 1) *
        (((Finset.range (N + 1)).lcm fun i => m - i) * N ^ (N * (N + 1))) : ℕ) : ℤ) := by
    exact_mod_cast hcomb
  have hcombZ : (m : ℤ) ^ (N + 1) ≤
      (2 : ℤ) ^ (N + 1) * ((((Finset.range (N + 1)).lcm fun i => m - i : ℕ) : ℤ) *
        (N : ℤ) ^ (N * (N + 1))) := by
    push_cast at hcombZ0
    linear_combination hcombZ0
  have hle2 : (2 : ℤ) ^ (N + 1) * ((((Finset.range (N + 1)).lcm fun i => m - i : ℕ) : ℤ) *
        (N : ℤ) ^ (N * (N + 1))) ≤
      (2 : ℤ) ^ (N + 1) * (|Z| * (N : ℤ) ^ (N * (N + 1))) := by
    gcongr
  have hle3 : (2 : ℤ) ^ (N + 1) * (|Z| * (N : ℤ) ^ (N * (N + 1))) ≤
      (2 : ℤ) ^ (N + 1) * ((((C + denomProd q N * C₁ : ℕ) : ℤ) * (m : ℤ) ^ N) *
        (N : ℤ) ^ (N * (N + 1))) := by
    gcongr
  have hfinal : (m : ℤ) ^ (N + 1) ≤
      ((2 ^ (N + 1) * N ^ (N * (N + 1)) * (C + denomProd q N * C₁) : ℕ) : ℤ) *
        (m : ℤ) ^ N := by
    have h := le_trans (le_trans hcombZ hle2) hle3
    have h' : (2 : ℤ) ^ (N + 1) * ((((C + denomProd q N * C₁ : ℕ) : ℤ) * (m : ℤ) ^ N) *
          (N : ℤ) ^ (N * (N + 1))) =
        ((2 ^ (N + 1) * N ^ (N * (N + 1)) * (C + denomProd q N * C₁) : ℕ) : ℤ) *
          (m : ℤ) ^ N := by
      push_cast; ring
    rwa [h'] at h
  rw [pow_succ (m : ℤ) N, mul_comm (((2 ^ (N + 1) * N ^ (N * (N + 1)) *
      (C + denomProd q N * C₁) : ℕ) : ℤ)) ((m : ℤ) ^ N)] at hfinal
  have hmpos : (0 : ℤ) < (m : ℤ) ^ N := pow_pos (by exact_mod_cast (by lia : 0 < m)) N
  have hmle : (m : ℤ) ≤
      ((2 ^ (N + 1) * N ^ (N * (N + 1)) * (C + denomProd q N * C₁) : ℕ) : ℤ) :=
    (mul_le_mul_iff_right₀ hmpos).mp hfinal
  have hBlt : ((2 ^ (N + 1) * N ^ (N * (N + 1)) * (C + denomProd q N * C₁) : ℕ) : ℤ) <
      (m : ℤ) := by exact_mod_cast hmB
  linarith

/-- Tail argument: the cleared polynomial agrees with `denomProd q N * a n`
for every `n` (for large arguments use `clearPoly_eq_of_large`; divisibility
by `M - n` for a large `M` then forces equality at `n`). -/
lemma clearPoly_eq_all (a : ℕ → ℤ)
    (hdiv : ∀ n m : ℕ, ((n : ℤ) - (m : ℤ)) ∣ a n - a m)
    {q : ℚ[X]} {N : ℕ} (hqN : q.natDegree ≤ N)
    (hqval : ∀ i : ℕ, i ≤ N → q.eval (i : ℚ) = (a i : ℚ))
    {C C₁ : ℕ}
    (hC : ∀ m : ℕ, 1 ≤ m → |(clearPoly q N).eval (m : ℤ)| ≤ (C : ℤ) * (m : ℤ) ^ N)
    (hC₁ : ∀ m : ℕ, 1 ≤ m → |a m| ≤ (C₁ : ℤ) * (m : ℤ) ^ N)
    (n : ℕ) :
    (clearPoly q N).eval (n : ℤ) = (denomProd q N : ℤ) * a n := by
  set Zn : ℤ := (clearPoly q N).eval (n : ℤ) - (denomProd q N : ℤ) * a n with hZn
  set z : ℕ := Zn.natAbs with hz
  have hM : ∃ M : ℕ, 2 * N < M ∧
      2 ^ (N + 1) * N ^ (N * (N + 1)) * (C + denomProd q N * C₁) < M ∧ z < M - n :=
    ⟨n + z + 2 ^ (N + 1) * N ^ (N * (N + 1)) * (C + denomProd q N * C₁) + 2 * N + 1,
      by lia⟩
  obtain ⟨M, hM2N, hMB, hMlt⟩ := hM
  have hMeq := clearPoly_eq_of_large a hdiv hqN hqval hC hC₁ M hM2N hMB
  have h1 : ((M : ℤ) - (n : ℤ)) ∣
      (clearPoly q N).eval (M : ℤ) - (clearPoly q N).eval (n : ℤ) :=
    Polynomial.sub_dvd_eval_sub _ _ _
  have h2 : ((M : ℤ) - (n : ℤ)) ∣ a M - a n := hdiv M n
  have h3 : ((M : ℤ) - (n : ℤ)) ∣
      ((clearPoly q N).eval (M : ℤ) - (clearPoly q N).eval (n : ℤ)) -
        (denomProd q N : ℤ) * (a M - a n) :=
    dvd_sub h1 (dvd_mul_of_dvd_right h2 _)
  have heq : ((clearPoly q N).eval (M : ℤ) - (clearPoly q N).eval (n : ℤ)) -
      (denomProd q N : ℤ) * (a M - a n) = -Zn := by
    rw [hMeq, hZn]; ring
  rw [heq] at h3
  have h5 : ((M : ℤ) - (n : ℤ)) ∣ Zn := dvd_neg.mp h3
  have hMn : ((M - n : ℕ) : ℤ) = (M : ℤ) - (n : ℤ) := Nat.cast_sub (by lia : n ≤ M)
  rw [← hMn] at h5
  have h6 : (M - n) ∣ z := by
    have h := (Int.natAbs_dvd_natAbs).mpr h5
    rwa [Int.natAbs_natCast, ← hz] at h
  have h7 : z = 0 := Nat.eq_zero_of_dvd_of_lt h6 hMlt
  have h8 : Zn.natAbs = 0 := by rw [← hz]; exact h7
  have h9 : Zn = 0 := Int.natAbs_eq_zero.mp h8
  rw [hZn] at h9
  exact sub_eq_zero.mp h9

snip end

problem usa1995_p4 (a : ℕ → ℤ)
    (hdiv : ∀ n m : ℕ, ((n : ℤ) - (m : ℤ)) ∣ a n - a m)
    (hp : ∃ p : ℤ[X], ∀ n : ℕ, p.eval (n : ℤ) > |a n|) :
    ∃ q : ℚ[X], ∀ n : ℕ, q.eval (n : ℚ) = (a n : ℚ) := by
  obtain ⟨p, hp⟩ := hp
  obtain ⟨q, hqN, hqval⟩ := interpolate_exists a p.natDegree
  have hC : ∃ C : ℕ, ∀ m : ℕ, 1 ≤ m →
      |(clearPoly q p.natDegree).eval (m : ℤ)| ≤ (C : ℤ) * (m : ℤ) ^ p.natDegree := by
    exact ⟨_, fun m hm => by rw [clearPoly_eval]; exact sum_pow_abs_le _ _ m hm⟩
  obtain ⟨C, hC⟩ := hC
  have hC₁ : ∀ m : ℕ, 1 ≤ m →
      |a m| ≤ ((∑ i ∈ Finset.range (p.natDegree + 1), (p.coeff i).natAbs : ℕ) : ℤ) *
        (m : ℤ) ^ p.natDegree := by
    intro m hm
    exact le_of_lt ((hp m).trans_le ((le_abs_self _).trans (abs_eval_le p m hm)))
  refine ⟨q, fun n => ?_⟩
  have hn := clearPoly_eq_all a hdiv hqN hqval hC hC₁ n
  have hcast := clearPoly_eval_cast q hqN n
  rw [hn] at hcast
  have hQne : ((denomProd q p.natDegree : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (denomProd_pos q p.natDegree).ne'
  have hcast2 : ((denomProd q p.natDegree : ℚ) * ((a n : ℤ) : ℚ)) =
      (denomProd q p.natDegree : ℚ) * q.eval (n : ℚ) := by
    have h3 : (((denomProd q p.natDegree : ℤ) * a n : ℤ) : ℚ) =
        (denomProd q p.natDegree : ℚ) * ((a n : ℤ) : ℚ) := by push_cast; ring
    rw [← h3]; exact hcast
  exact (mul_left_cancel₀ hQne hcast2).symm

end Usa1995P4
