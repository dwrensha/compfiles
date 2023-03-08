import Aesop
import Mathlib.Algebra.IsPrimePow
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime
import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.Ring

/-!
# International Mathematical Olympiad 1989, Problem 5

Prove that for each positive integer n there exist n consecutive positive
integers, none of which is an integral power of a prime number.
-/

namespace Imo1989Q5

lemma coprime_of_product (n : ℕ) (lst : List ℕ) (h : ∀ y ∈ lst, n.coprime y) :
    n.coprime lst.prod := by
  induction lst with
  | nil => simp
  | cons x xs ih =>
    have hy : ∀ (y : ℕ), y ∈ xs → Nat.coprime n y := by
      intro y hy
      aesop
    have h1 := h x (by simp)
    rw[List.prod_cons]
    exact Nat.coprime.mul_right h1 (ih hy)

lemma modulus_of_product {a b : ℕ} {xs : List ℕ}
    (h : a ≡ b [MOD xs.prod])
    (x : ℕ)
    (hx : x ∈ xs)
    : a ≡ b [MOD x] := by
  induction xs with
  | nil => aesop
  | cons y ys ih =>
    rw[ List.prod_cons] at h
    cases hx with
    | head => exact Nat.ModEq.of_mul_right _ h
    | tail w hw =>
      exact ih (Nat.ModEq.of_mul_left _ h) hw

structure ChinesePair where
  modulus : ℕ
  remainder : ℕ

lemma general_chinese_remainder (xs : List ChinesePair)
    (x_coprime : xs.Pairwise (fun x y ↦ Nat.coprime x.modulus y.modulus)) :
    ∃ m : ℕ, ∀ x ∈ xs, m ≡ x.remainder [MOD x.modulus] := by
  induction xs with
  | nil => use 0; simp only
  | cons x xs ih =>
    obtain ⟨b, hb⟩ := ih x_coprime.tail
    clear ih
    -- then we use Nat.chineseRemainder on x and ⟨List.prod(xs.map modulus), b⟩
    rw[List.pairwise_cons] at x_coprime
    -- need that `Nat.Coprime x.modulus y`
    have h1 := coprime_of_product x.modulus (xs.map (·.modulus))
      (by intros z hz; aesop)
    obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder h1 x.remainder b
    use k
    intros z hz
    cases hz with
    | head => exact hk1
    | tail w hw =>
      have h2 := hb z hw
      have h3 : z.modulus ∈ (List.map (fun x => x.modulus) xs) := by aesop
      have h4 := modulus_of_product hk2 _ h3
      exact Nat.ModEq.trans h4 h2

#check Nat.exists_infinite_primes
#check List.maximum
#check WithBot

theorem get_primes (n : ℕ) :
    ∃ lst : List ℕ, lst.length = n ∧ lst.Nodup ∧ ∀ x ∈ lst, x.Prime := by
  induction n with
  | zero => use ∅; simp
  | succ n ih =>
    obtain ⟨l', hl', hlnd, hlp⟩ := ih
    have := l'.maximum
--    use (l'.maximum + 1)::l'
    sorry

theorem imo1989_q5 (n : ℕ) : ∃ m > 0, ∀ j < n, ¬IsPrimePow (m + j) := by
  -- (informal solution from https://artofproblemsolving.com)
  -- Let p₁,p₂,...pₙ,q₁,q₂,...,qₙ be distinct primes.
  -- By the Chinese Remainder theorem, there exists x such that
  --   x ≡ -1 mod p₁q₁
  --   x ≡ -2 mod p₂q₂
  --   ...
  --   x ≡ -n mod pₙqₙ
  -- The n consecutive numbers x+1, x+2, ..., x+n each have at least
  -- two prime factors, so none of them can be expressed as an integral
  -- power of a prime.
  sorry
