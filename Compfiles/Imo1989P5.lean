import Mathlib.Algebra.IsPrimePow
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime
import Mathlib.Tactic.Common
import Std.Data.List.Lemmas

import ProblemExtraction

problem_file

/-!
# International Mathematical Olympiad 1989, Problem 5

Prove that for each positive integer n there exist n consecutive positive
integers, none of which is an integral power of a prime number.
-/

namespace Imo1989P5

snip begin

lemma coprime_of_product (n : ℕ) (lst : List ℕ) (h : ∀ y ∈ lst, n.Coprime y) :
    n.Coprime lst.prod := by
  induction lst with
  | nil => simp only [List.prod_nil, Nat.coprime_one_right_eq_true]
  | cons x xs ih =>
    have hy : ∀ (y : ℕ), y ∈ xs → Nat.Coprime n y :=
      fun y hy ↦ h y (List.mem_cons.mpr (Or.inr hy))
    have h1 := h x (by simp)
    rw [List.prod_cons]
    exact Nat.Coprime.mul_right h1 (ih hy)

lemma modulus_of_product {a b : ℕ} {xs : List ℕ}
    (h : a ≡ b [MOD xs.prod])
    (x : ℕ)
    (hx : x ∈ xs)
    : a ≡ b [MOD x] := by
  induction xs with
  | nil => aesop
  | cons y ys ih =>
    rw [List.prod_cons] at h
    cases hx with
    | head => exact Nat.ModEq.of_mul_right _ h
    | tail w hw =>
      exact ih (Nat.ModEq.of_mul_left _ h) hw

structure ChinesePair where
  modulus : ℕ
  remainder : ℕ

lemma general_chinese_remainder (xs : List ChinesePair)
    (x_coprime : xs.Pairwise (fun x y ↦ Nat.Coprime x.modulus y.modulus)) :
    ∃ m : ℕ, ∀ x ∈ xs, m ≡ x.remainder [MOD x.modulus] := by
  induction xs with
  | nil => use 0; decide
  | cons x xs ih =>
    obtain ⟨b, hb⟩ := ih x_coprime.tail
    clear ih
    -- then we use Nat.chineseRemainder on x and ⟨List.prod(xs.map modulus), b⟩
    rw [List.pairwise_cons] at x_coprime
    -- need that `Nat.Coprime x.modulus y`
    have h1 := coprime_of_product x.modulus (xs.map (·.modulus))
      (by intro z hz; aesop)
    obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder h1 x.remainder b
    use k
    intro z hz
    cases hz with
    | head => exact hk1
    | tail w hw =>
      have h2 := hb z hw
      have h4 := modulus_of_product hk2 _ (List.mem_map_of_mem ChinesePair.modulus hw)
      exact Nat.ModEq.trans h4 h2

lemma list_upper_bound (l : List ℕ) : ∃ m : ℕ, ∀ x ∈ l, x ≤ m := by
  match h : l.maximum with
  | none => use 0; intro x a; rw [List.maximum_eq_none] at h
            rw [h] at a; exact (List.not_mem_nil _ a).elim
  | some mx => use mx; intro x hx; exact List.le_maximum_of_mem hx h

theorem get_primes (n m : ℕ) :
    ∃ lst : List ℕ, lst.length = n ∧ lst.Nodup ∧
               ∀ x ∈ lst, x.Prime ∧ m ≤ x := by
  induction n with
  | zero => use ∅; simp
  | succ n ih =>
    obtain ⟨l', hl', hlnd, hlp⟩ := ih
    obtain ⟨mx, hmx⟩ := list_upper_bound l'
    obtain ⟨p, hpm, hp⟩ := Nat.exists_infinite_primes (max m (mx + 1))
    use p :: l'
    constructor
    · exact Iff.mpr Nat.succ_inj' hl'
    · constructor
      · rw [List.nodup_cons]
        constructor
        · intro hpl
          exact Iff.mpr Nat.not_le (le_of_max_le_right hpm) (hmx p hpl)
        · exact hlnd
      · aesop

lemma not_prime_power_of_two_factors
     {n p q : ℕ}
     (hp : Nat.Prime p) (hq : Nat.Prime q)
     (hpq : p ≠ q)
     (hpn : p ∣ n) (hqn : q ∣ n) : ¬IsPrimePow n := by
   intro hpp
   have h0 : n ≠ 0 := by
     have h : ¬IsPrimePow 0 := not_isPrimePow_zero
     intro hn
     rw [←hn] at h
     exact h hpp
   obtain ⟨r, k, hr, hk, hrk⟩ := hpp
   rw [← Nat.prime_iff] at hr
   rw [← hrk] at hqn hpn h0; clear hrk
   have h1 := (Nat.mem_factors h0).mpr ⟨hp, hpn⟩
   rw [Nat.Prime.factors_pow hr] at h1
   have h3 := (List.mem_replicate.mp h1).2
   have h2 := (Nat.mem_factors h0).mpr ⟨hq, hqn⟩
   rw [Nat.Prime.factors_pow hr] at h2
   have h4 := (List.mem_replicate.mp h2).2
   rw [h3, h4] at hpq
   exact hpq rfl

lemma lemma1 {p1 p2 q : ℕ}
    (hp1 : Nat.Prime p1)
    (hp2 : Nat.Prime p2)
    (hq : Nat.Prime q)
    (hp1q : p1 ≠ q)
    (hp2q : p2 ≠ q) :
    Nat.Coprime (p1 * p2) q := by
  have h1 : Nat.Coprime p1 q := Iff.mpr (Nat.coprime_primes hp1 hq) hp1q
  have h2 : Nat.Coprime p2 q := Iff.mpr (Nat.coprime_primes hp2 hq) hp2q
  exact Nat.Coprime.mul h1 h2

lemma lemma2 {p1 q1 p2 q2 : ℕ}
    (hp1 : Nat.Prime p1)
    (hq1 : Nat.Prime q1)
    (hp2 : Nat.Prime p2)
    (hq2 : Nat.Prime q2)
    (hp1q1 : p1 ≠ q1)
    (hp1q2 : p1 ≠ q2)
    (hp2q1 : p2 ≠ q1)
    (hp2q2 : p2 ≠ q2) :
    Nat.Coprime (p1 * p2) (q1 * q2) := by
  have h1 := lemma1 hp1 hp2 hq1 hp1q1 hp2q1
  have h2 := lemma1 hp1 hp2 hq2 hp1q2 hp2q2
  exact Nat.Coprime.mul_right h1 h2

lemma lemma3 {α : Type} (l : List α)
    (hl : List.Nodup l)
    {i j : Fin l.length}
    (hij : i ≠ j)
    : l.get i ≠ l.get j := by
  intro hij'
  --TODO why do neither aesop nor library_search succeed here?
  exact hij (List.nodup_iff_injective_get.mp hl hij')

lemma lemma4 {a b : ℕ} (h : a ≡ b [MOD b]) : a ≡ 0 [MOD b] := by
  have h1 : a % b = b % b := h
  have h2 : b % b = 0 := Nat.mod_self b
  rw [h2] at h1
  exact h1

snip end

problem imo1989_p5 (n : ℕ) : ∃ m, ∀ j < n, ¬IsPrimePow (m + j) := by
  -- (informal solution from https://artofproblemsolving.com)
  -- Let p₁,p₂,...pₙ,q₁,q₂,...,qₙ be distinct primes.
  obtain ⟨l, hll, hld, hl⟩ := get_primes (2 * n) n
  let ci : List ChinesePair :=
    List.ofFn (fun x : Fin n ↦ have hx0: ↑x < List.length l := by
                                 rw [hll, Nat.two_mul]
                                 exact Nat.lt_add_right _ n n x.2
                               have hx1: ↑x + n < List.length l := by
                                 rw [hll, Nat.two_mul]
                                 exact Nat.add_lt_add_right x.2 n
                               let p := l.get ⟨x.1, hx0⟩
                               let q := l.get ⟨x.1 + n, hx1⟩
                               ⟨p * q, p * q - x.1⟩)

  have lcp : ci.Pairwise (fun x y => Nat.Coprime x.modulus y.modulus) := by
     simp only [ge_iff_le, List.pairwise_ofFn]
     intro i j hij
     apply lemma2
           (hl _ (List.get_mem _ _ _)).1
           (hl _ (List.get_mem _ _ _)).1
           (hl _ (List.get_mem _ _ _)).1
           (hl _ (List.get_mem _ _ _)).1
     · exact lemma3 l hld (LT.lt.ne hij)
     · have hijn : i < j + n := Nat.lt_add_right _ _ n hij
       exact lemma3 l hld (Fin.ne_of_vne (LT.lt.ne hijn))
     · have hijn' := calc j < n := j.prop
                          _ ≤ i + n := Nat.le_add_left _ _
       have hijn : i + n ≠ j := Nat.ne_of_gt hijn'
       exact lemma3 l hld (Fin.ne_of_vne hijn)
     · have hijn : i + n < j + n := Nat.add_lt_add_right hij n
       exact lemma3 l hld (Fin.ne_of_vne (LT.lt.ne hijn))

  -- By the Chinese Remainder theorem, there exists x such that
  --   x ≡ 0 mod p₁q₁
  --   x ≡ -1 mod p₂q₂
  --   ...
  --   x ≡ -(n - 1) mod pₙqₙ

  obtain ⟨m, hm⟩ := general_chinese_remainder ci lcp

  -- The n consecutive numbers x, x, ..., x+n-1 each have at least
  -- two prime factors, so none of them can be expressed as an integral
  -- power of a prime.
  use m
  intro j hj
  have hcil : ci.length = n := by aesop
  have hj1 : j < ci.length := by rwa [hcil]
  have hj2 : j < l.length := by rw [hll, Nat.two_mul]
                                exact Nat.lt_add_right j n n hj
  have hj3 : j + n < l.length := by rw [hll, Nat.two_mul]
                                    exact Nat.add_lt_add_right hj n
  have h1 := hm (ci.get ⟨j, hj1⟩) (List.get_mem _ _ _)
  obtain ⟨h2, h3⟩ := hl (l.get ⟨j, hj2⟩) (List.get_mem _ _ _)
  obtain ⟨h4, _⟩ := hl (l.get ⟨j + n, hj3⟩) (List.get_mem _ _ _)
  simp only [List.get_ofFn, ge_iff_le, Fin.cast_mk] at h1
  have h6 := Nat.ModEq.add_right j h1
  have h7 : j ≤ l.get ⟨j, hj2⟩ * l.get ⟨j + n, hj3⟩ := by
      apply Nat.le_of_lt
      calc
        j < n := hj
        _ ≤ l.get ⟨j, hj2⟩ := h3
        _ ≤ l.get ⟨j, hj2⟩ * l.get ⟨j + n, hj3⟩ := Nat.le_mul_of_pos_right (Nat.Prime.pos h4)

  rw [Nat.sub_add_cancel h7] at h6
  clear h1 h7
  have h8 := lemma4 h6
  replace h8 := Nat.dvd_of_mod_eq_zero h8
  have h9 := dvd_of_mul_right_dvd h8
  have h10 := dvd_of_mul_left_dvd h8
  have h11 : l.get ⟨j, hj2⟩ ≠ l.get ⟨j + n, hj3⟩ := by
    intro h12
    have h13 := (List.Nodup.get_inj_iff hld).mp h12
    simp only [Fin.mk.injEq, self_eq_add_right] at h13
    simp only [h13, not_lt_zero'] at hj
  exact not_prime_power_of_two_factors h2 h4 h11 h9 h10
