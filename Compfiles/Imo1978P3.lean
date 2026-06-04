/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Olympiad 1978, Problem 3

The set of all positive integers is the union of two disjoint subsets
{f(1), f(2), ..., f(n), ...} and {g(1), g(2), ..., g(n), ...}, where

  f(1) < f(2) < ... < f(n) < ...,
  g(1) < g(2) < ... < g(n) < ...,

and g(n) = f(f(n)) + 1 for all n ≥ 1.

Determine f(240).
-/

namespace Imo1978P3

determine solution : ℕ := 388

snip begin

/-
We follow the solution by John Scholes,
https://prase.cz/kalva/imo/isoln/isoln783.html

A counting argument shows that `g n = f n + n`, hence `f (f n) = f n + n - 1`. It
follows that `f` is the lower Wythoff sequence `f n = ⌊n·φ⌋` (with `φ` the golden
ratio), whose values together with `f n + n = ⌊n·φ²⌋` partition the positive integers
by Rayleigh's (Beatty's) theorem. Uniqueness of such an `f` is proved by strong
induction, and finally `f 240 = ⌊240·φ⌋ = 388`.
-/

open scoped goldenRatio
open Real

/-- The lower Wythoff sequence `⌊n·φ⌋`, which is the function `f` in the problem. -/
noncomputable def a (n : ℕ) : ℕ := (⌊(n : ℝ) * φ⌋).toNat

lemma a_eq (n : ℕ) : (a n : ℤ) = ⌊(n : ℝ) * φ⌋ := by
  unfold a
  rw [Int.toNat_of_nonneg]
  exact Int.floor_nonneg.mpr (by positivity)

/-- `a n + n = ⌊n·φ²⌋`, using `φ² = φ + 1`. -/
lemma a_add_eq (n : ℕ) : ((a n : ℤ) + n) = ⌊(n : ℝ) * φ ^ 2⌋ := by
  rw [a_eq]
  rw [show (n : ℝ) * φ ^ 2 = (n : ℝ) * φ + n by rw [goldenRatio_sq]; ring]
  rw [Int.floor_add_natCast]

lemma beattySeq_a (n : ℕ) : beattySeq φ (n : ℤ) = (a n : ℤ) := by
  rw [a_eq, beattySeq]; push_cast; rfl

lemma beattySeq_a_add (n : ℕ) : beattySeq (φ ^ 2) (n : ℤ) = ((a n : ℤ) + n) := by
  rw [a_add_eq, beattySeq]; push_cast; rfl

lemma holderConj : (φ).HolderConjugate (φ ^ 2) := by
  refine ⟨?_, goldenRatio_pos, by positivity⟩
  rw [inv_one, ← inv_pow, inv_goldenRatio, neg_sq, goldenConj_sq]
  ring

lemma a_pos {k : ℕ} (hk : 0 < k) : 0 < a k := by
  have h1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have : (1 : ℝ) < (k : ℝ) * φ := by
    calc (1 : ℝ) < φ := one_lt_goldenRatio
    _ = 1 * φ := (one_mul _).symm
    _ ≤ (k : ℝ) * φ := by gcongr
  have hfloor : (1 : ℤ) ≤ ⌊(k : ℝ) * φ⌋ := by
    rw [Int.le_floor]; push_cast; linarith
  have := a_eq k
  lia

lemma a_strictMono : StrictMono a := by
  apply strictMono_nat_of_lt_succ
  intro n
  have key : (a n : ℤ) + 1 ≤ a (n + 1) := by
    rw [a_eq, a_eq]
    have h1 : ((n : ℝ) * φ) + 1 ≤ ((n : ℝ) + 1) * φ := by
      have := one_lt_goldenRatio; nlinarith
    have hmono : ⌊(n : ℝ) * φ⌋ + 1 ≤ ⌊((n : ℝ) + 1) * φ⌋ := by
      calc ⌊(n : ℝ) * φ⌋ + 1 = ⌊(n : ℝ) * φ + 1⌋ := by rw [Int.floor_add_one]
        _ ≤ ⌊((n : ℝ) + 1) * φ⌋ := Int.floor_le_floor h1
    have hcast : ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [hcast] at hmono
    exact hmono
  lia

lemma a_mono {i j : ℕ} (hij : i ≤ j) : a i ≤ a j := a_strictMono.monotone hij

/-- Every positive integer is `a k` or `a k + k` for some `k ≥ 1`. -/
lemma ha_cover (m : ℕ) (hm : 0 < m) :
    (∃ k, 0 < k ∧ a k = m) ∨ (∃ k, 0 < k ∧ a k + k = m) := by
  have hj : (0 : ℤ) < (m : ℤ) := by exact_mod_cast hm
  have ref := Irrational.beattySeq_symmDiff_beattySeq_pos holderConj goldenRatio_irrational
  have hmem : (m : ℤ) ∈ {n : ℤ | 0 < n} := hj
  rw [← ref] at hmem
  have hor := Set.mem_symmDiff.mp hmem
  rcases hor with ⟨hA, _⟩ | ⟨hB, _⟩
  · obtain ⟨K, hK, hKeq⟩ := hA
    left
    refine ⟨K.toNat, by lia, ?_⟩
    have hcast : ((K.toNat : ℤ)) = K := Int.toNat_of_nonneg (by lia)
    have h2 : beattySeq φ (K.toNat : ℤ) = (m : ℤ) := by rw [hcast]; exact hKeq
    rw [beattySeq_a] at h2
    exact_mod_cast h2
  · obtain ⟨K, hK, hKeq⟩ := hB
    right
    refine ⟨K.toNat, by lia, ?_⟩
    have hcast : ((K.toNat : ℤ)) = K := Int.toNat_of_nonneg (by lia)
    have h2 : beattySeq (φ ^ 2) (K.toNat : ℤ) = (m : ℤ) := by rw [hcast]; exact hKeq
    rw [beattySeq_a_add] at h2
    exact_mod_cast h2

/-- The two sequences `a k` and `a k + k` are disjoint. -/
lemma ha_disj (j k : ℕ) (hj : 0 < j) (hk : 0 < k) : a j ≠ a k + k := by
  intro heq
  have hvpos : (0 : ℤ) < (a j : ℤ) := by have := a_pos hj; exact_mod_cast this
  have heqz : (a j : ℤ) = ((a k : ℤ) + k) := by rw [heq]; push_cast; ring
  have ref := Irrational.beattySeq_symmDiff_beattySeq_pos holderConj goldenRatio_irrational
  have hmem : (a j : ℤ) ∈ {n : ℤ | 0 < n} := hvpos
  rw [← ref] at hmem
  rcases Set.mem_symmDiff.mp hmem with ⟨_, hnotB⟩ | ⟨_, hnotA⟩
  · exact hnotB ⟨(k : ℤ), by exact_mod_cast hk, by rw [beattySeq_a_add, heqz]⟩
  · exact hnotA ⟨(j : ℤ), by exact_mod_cast hj, by rw [beattySeq_a]⟩

lemma a_240 : a 240 = 388 := by
  have hs2 : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hsn : (0 : ℝ) ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  have hφ : (φ : ℝ) = (1 + Real.sqrt 5) / 2 := rfl
  have hval : (240 : ℝ) * φ = 120 + 120 * Real.sqrt 5 := by rw [hφ]; ring
  have hfloor : ⌊(240 : ℝ) * φ⌋ = 388 := by
    rw [Int.floor_eq_iff]
    refine ⟨?_, ?_⟩
    · push_cast; rw [hval]; nlinarith [hs2, hsn]
    · push_cast; rw [hval]; nlinarith [hs2, hsn]
  have h := a_eq 240
  rw [show ((240 : ℕ) : ℝ) = (240 : ℝ) by norm_num, hfloor] at h
  exact_mod_cast h

/-- A strictly increasing positive sequence `F` is uniquely determined by the property
that `{F k}` and `{F k + k}` partition the positive integers. We state this as: any two
such sequences `F` and `A` agree. The key fact is that `F n` is the least positive integer
not among `{F k, F k + k : k < n}`. -/
lemma wythoff_unique (F A : ℕ → ℕ)
    (hFmono : ∀ p q, 0 < p → p < q → F p < F q)
    (hAmono : ∀ p q, 0 < p → p < q → A p < A q)
    (hFpos : ∀ k, 0 < k → 0 < F k)
    (hApos : ∀ k, 0 < k → 0 < A k)
    (coverF : ∀ m, 0 < m → (∃ k, 0 < k ∧ F k = m) ∨ (∃ k, 0 < k ∧ F k + k = m))
    (coverA : ∀ m, 0 < m → (∃ k, 0 < k ∧ A k = m) ∨ (∃ k, 0 < k ∧ A k + k = m))
    (disjF : ∀ p q, 0 < p → 0 < q → F p ≠ F q + q)
    (disjA : ∀ p q, 0 < p → 0 < q → A p ≠ A q + q) :
    ∀ n, 0 < n → F n = A n := by
  -- One symmetric direction: given `P k = Q k` for `k < n`, conclude `P n ≤ Q n`.
  have step : ∀ (P Q : ℕ → ℕ),
      (∀ p q, 0 < p → p < q → P p < P q) → (∀ p q, 0 < p → p < q → Q p < Q q) →
      (∀ k, 0 < k → 0 < Q k) →
      (∀ m, 0 < m → (∃ k, 0 < k ∧ P k = m) ∨ (∃ k, 0 < k ∧ P k + k = m)) →
      (∀ p q, 0 < p → 0 < q → Q p ≠ Q q + q) →
      ∀ n, 0 < n → (∀ k, k < n → 0 < k → P k = Q k) → P n ≤ Q n := by
    intro P Q hPmono hQmono hQpos coverP disjQ n hn IH
    have hPcancel : ∀ p q, 0 < q → P p < P q → p < q := by
      intro p q hq h
      by_contra hcon
      rw [not_lt] at hcon
      rcases eq_or_lt_of_le hcon with h2 | h2
      · rw [h2] at h; exact lt_irrefl _ h
      · exact absurd (hPmono q p hq h2) (by lia)
    -- every positive `m < P n` is hit by `P k` or `P k + k` with `k < n`
    have lowP : ∀ m, 0 < m → m < P n →
        (∃ k, 0 < k ∧ k < n ∧ P k = m) ∨ (∃ k, 0 < k ∧ k < n ∧ P k + k = m) := by
      intro m hm hmlt
      rcases coverP m hm with ⟨k, hk, hkeq⟩ | ⟨k, hk, hkeq⟩
      · exact Or.inl ⟨k, hk, hPcancel k n hn (by rw [hkeq]; exact hmlt), hkeq⟩
      · exact Or.inr ⟨k, hk, hPcancel k n hn (by lia), hkeq⟩
    -- but `Q n` is hit by neither, using the induction hypothesis
    have hQnot : ¬ ((∃ k, 0 < k ∧ k < n ∧ P k = Q n) ∨
                    (∃ k, 0 < k ∧ k < n ∧ P k + k = Q n)) := by
      rintro (⟨k, hk, hkn, hkeq⟩ | ⟨k, hk, hkn, hkeq⟩)
      · rw [IH k hkn hk] at hkeq
        exact absurd hkeq (ne_of_lt (hQmono k n hk hkn))
      · rw [IH k hkn hk] at hkeq
        exact disjQ n k hn hk hkeq.symm
    by_contra hcon
    rw [not_le] at hcon
    exact hQnot (lowP (Q n) (hQpos n hn) hcon)
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro hn
  have h1 := step F A hFmono hAmono hApos coverF disjA n hn (fun k hkn hk => IH k hkn hk)
  have h2 := step A F hAmono hFmono hFpos coverA disjF n hn (fun k hkn hk => (IH k hkn hk).symm)
  lia

snip end

problem imo1978_p3
    (f g : ℕ → ℕ)
    (hfpos : ∀ n, 0 < n → 0 < f n)
    (hgpos : ∀ n, 0 < n → 0 < g n)
    (hfmono : ∀ n m, 0 < n → n < m → f n < f m)
    (hgmono : ∀ n m, 0 < n → n < m → g n < g m)
    (hdisjoint : ∀ n m, 0 < n → 0 < m → f n ≠ g m)
    (hcover : ∀ k, 0 < k → (∃ n, 0 < n ∧ f n = k) ∨ (∃ n, 0 < n ∧ g n = k))
    (hgf : ∀ n, 0 < n → g n = f (f n) + 1) :
    f 240 = solution := by
  classical
  -- A sequence strictly increasing on the positives is injective and monotone there.
  have injOn_of : ∀ (h : ℕ → ℕ) (b : ℕ), (∀ p q, 0 < p → p < q → h p < h q) →
      Set.InjOn h ↑(Finset.Icc 1 b) := by
    intro h b hmono x hx y hy hxy
    simp only [Finset.coe_Icc, Set.mem_Icc] at hx hy
    rcases lt_trichotomy x y with hlt | he | hlt
    · exact absurd hxy (ne_of_lt (hmono x y (by lia) hlt))
    · exact he
    · exact absurd hxy.symm (ne_of_lt (hmono y x (by lia) hlt))
  have le_of : ∀ (h : ℕ → ℕ), (∀ p q, 0 < p → p < q → h p < h q) →
      ∀ p q, 0 < p → p ≤ q → h p ≤ h q := by
    intro h hmono p q hp hpq
    rcases eq_or_lt_of_le hpq with he | hlt
    · rw [he]
    · exact le_of_lt (hmono p q hp hlt)
  have hg_le_cancel : ∀ p q, 0 < q → g p ≤ g q → p ≤ q := by
    intro p q hq h
    by_contra hcon
    rw [not_le] at hcon
    exact absurd (hgmono q p hq hcon) (by lia)
  -- Part (I): `g n = f n + n`, via counting the integers in `[1, g n]`.
  have hg_eq : ∀ n, 0 < n → g n = f n + n := by
    intro n hn
    set G := g n with hG
    have hffn : 0 < f n := hfpos n hn
    have hgfn : G = f (f n) + 1 := hgf n hn
    have hinjf : Set.InjOn f ↑(Finset.Icc 1 (f n)) := injOn_of f (f n) hfmono
    have hinjg : Set.InjOn g ↑(Finset.Icc 1 n) := injOn_of g n hgmono
    have key : (Finset.image f (Finset.Icc 1 (f n))) ∪ (Finset.image g (Finset.Icc 1 n))
                = Finset.Icc 1 G := by
      apply Finset.Subset.antisymm
      · intro x hx
        rw [Finset.mem_union] at hx
        rw [Finset.mem_Icc]
        rcases hx with hx | hx
        · rw [Finset.mem_image] at hx
          obtain ⟨k, hkmem, hkeq⟩ := hx
          rw [Finset.mem_Icc] at hkmem
          subst hkeq
          refine ⟨hfpos k (by lia), ?_⟩
          have : f k ≤ f (f n) := le_of f hfmono k (f n) (by lia) hkmem.2
          lia
        · rw [Finset.mem_image] at hx
          obtain ⟨k, hkmem, hkeq⟩ := hx
          rw [Finset.mem_Icc] at hkmem
          subst hkeq
          refine ⟨hgpos k (by lia), ?_⟩
          have : g k ≤ g n := le_of g hgmono k n (by lia) hkmem.2
          lia
      · intro m hm
        rw [Finset.mem_Icc] at hm
        have hm0 : 0 < m := hm.1
        rw [Finset.mem_union, Finset.mem_image, Finset.mem_image]
        rcases hcover m hm0 with ⟨k, hk, hkeq⟩ | ⟨k, hk, hkeq⟩
        · left
          refine ⟨k, ?_, hkeq⟩
          rw [Finset.mem_Icc]
          refine ⟨hk, ?_⟩
          by_contra hcon
          rw [not_le] at hcon
          have h1 : f (f n) < f k := hfmono (f n) k hffn hcon
          have h2 : f k ≤ G := by rw [hkeq]; exact hm.2
          have h3 : f k = G := by lia
          have hfg : f k = g n := by rw [h3]
          exact hdisjoint k n hk hn hfg
        · right
          refine ⟨k, ?_, hkeq⟩
          rw [Finset.mem_Icc]
          refine ⟨hk, ?_⟩
          have h2 : g k ≤ G := by rw [hkeq]; exact hm.2
          rw [hG] at h2
          exact hg_le_cancel k n hn h2
    have hdisj : Disjoint (Finset.image f (Finset.Icc 1 (f n)))
                          (Finset.image g (Finset.Icc 1 n)) := by
      rw [Finset.disjoint_left]
      intro x hxf hxg
      rw [Finset.mem_image] at hxf hxg
      obtain ⟨k1, hk1, hk1eq⟩ := hxf
      obtain ⟨k2, hk2, hk2eq⟩ := hxg
      rw [Finset.mem_Icc] at hk1 hk2
      exact hdisjoint k1 k2 (by lia) (by lia) (by rw [hk1eq, hk2eq])
    have hcardf : (Finset.image f (Finset.Icc 1 (f n))).card = f n := by
      rw [Finset.card_image_of_injOn hinjf, Nat.card_Icc]; lia
    have hcardg : (Finset.image g (Finset.Icc 1 n)).card = n := by
      rw [Finset.card_image_of_injOn hinjg, Nat.card_Icc]; lia
    have hcard := Finset.card_union_of_disjoint hdisj
    rw [key, hcardf, hcardg, Nat.card_Icc] at hcard
    lia
  -- `f`'s values and `f k + k` partition the positive integers.
  have cover_f : ∀ m, 0 < m → (∃ k, 0 < k ∧ f k = m) ∨ (∃ k, 0 < k ∧ f k + k = m) := by
    intro m hm
    rcases hcover m hm with ⟨k, hk, hkeq⟩ | ⟨k, hk, hkeq⟩
    · exact Or.inl ⟨k, hk, hkeq⟩
    · exact Or.inr ⟨k, hk, by rw [← hg_eq k hk]; exact hkeq⟩
  have disj_f : ∀ p q, 0 < p → 0 < q → f p ≠ f q + q := by
    intro p q hp hq
    rw [← hg_eq q hq]
    exact hdisjoint p q hp hq
  -- Part (II): `f` is the lower Wythoff sequence `a`, by the uniqueness lemma.
  have huniq := wythoff_unique f a hfmono (fun _ _ _ h => a_strictMono h)
    hfpos (fun k hk => a_pos hk) cover_f ha_cover disj_f ha_disj
  -- Final computation: `f 240 = a 240 = 388`.
  show f 240 = 388
  rw [huniq 240 (by norm_num), a_240]

end Imo1978P3
