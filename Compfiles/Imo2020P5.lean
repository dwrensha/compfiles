/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Olympiad 2020, Problem 5

A deck of n > 1 cards is given. A positive integer is written on
each card. The deck has the property that the arithmetic mean of
the numbers on each pair of cards is also the geometric mean of
the numbers on some collection of one or more cards.

For which n does it follow that the numbers on the cards are all equal?
-/

namespace Imo2020P5

determine SolutionSet : Set ℕ := {n | 1 < n}

noncomputable def geometric_mean {α : Type} (f : α → ℕ+) (s : Finset α) : ℝ :=
  (∏ i ∈ s, (f i : ℝ))^((1:ℝ)/s.card)

snip begin
/- The answer is "all n > 1": for every n > 1 the property forces all numbers
   to be equal. The proof follows the standard official-solution strategy:
   divide all numbers by their gcd (the property is invariant under scaling),
   so we may assume the numbers are coprime. If the maximal value M were at
   least 2, pick a prime P ∣ M and a card value b not divisible by P which is
   maximal among such values. The arithmetic mean (M + b)/2 equals the
   geometric mean of some collection; since it exceeds b, the collection
   contains a value larger than b, which must be divisible by P. Hence P
   divides the product of the collection, i.e. P ∣ 2^k * N = (M + b)^k, so
   P ∣ M + b and therefore P ∣ b, a contradiction. Thus M = 1 and all
   numbers coincide. -/

lemma rpow_inv_eq_iff {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) {k : ℕ} (hk : k ≠ 0) :
    x ^ ((1:ℝ)/k) = y ↔ x = y ^ k := by
  rw [one_div]
  constructor
  · intro h
    have hx2 : x = (x ^ ((k:ℝ)⁻¹)) ^ k := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx, inv_mul_cancel₀ (by exact_mod_cast hk),
        Real.rpow_one]
    rw [hx2, h]
  · intro h
    rw [h, ← Real.rpow_natCast, ← Real.rpow_mul hy, mul_inv_cancel₀ (by exact_mod_cast hk),
      Real.rpow_one]

lemma all_equal {α : Type} [Fintype α] [Nonempty α] (f : α → ℕ+)
    (h : Pairwise fun a b ↦ ∃ s : Finset α, s.Nonempty ∧
      geometric_mean f s = ((f a : ℝ) + f b) / 2) :
    ∃ y, ∀ a, f a = y := by
  classical
  -- Step 1: divide out the overall gcd; the property is preserved.
  set d := Finset.univ.gcd (fun i => (f i : ℕ)) with hd
  have hd_dvd : ∀ i, d ∣ (f i : ℕ) := fun i => Finset.gcd_dvd (Finset.mem_univ i)
  obtain ⟨i0⟩ := ‹Nonempty α›
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos (hd_dvd i0) (f i0).pos
  set g : α → ℕ+ := fun i => ⟨(f i : ℕ)/d,
    Nat.div_pos (Nat.le_of_dvd (f i).pos (hd_dvd i)) hdpos⟩ with hg
  have hfg : ∀ i, (f i : ℕ) = d * (g i : ℕ) := by
    intro i
    rw [hg]
    exact (Nat.mul_div_cancel' (hd_dvd i)).symm
  have hprop : Pairwise fun a b ↦ ∃ s : Finset α, s.Nonempty ∧
      geometric_mean g s = ((g a : ℝ) + g b) / 2 := by
    intro a b hab
    obtain ⟨s, hs, hGM⟩ := h hab
    refine ⟨s, hs, ?_⟩
    have hk : s.card ≠ 0 := Nat.ne_of_gt hs.card_pos
    unfold geometric_mean at hGM ⊢
    have hx : 0 ≤ ∏ i ∈ s, (f i : ℝ) := Finset.prod_nonneg fun i _ => by positivity
    have hy : 0 ≤ ((f a : ℝ) + f b)/2 := by positivity
    rw [rpow_inv_eq_iff hx hy hk] at hGM
    have hx2 : 0 ≤ ∏ i ∈ s, (g i : ℝ) := Finset.prod_nonneg fun i _ => by positivity
    have hy2 : 0 ≤ ((g a : ℝ) + g b)/2 := by positivity
    rw [rpow_inv_eq_iff hx2 hy2 hk]
    have hfgR : ∀ i, ((f i : ℕ+) : ℝ) = (d:ℝ) * ((g i : ℕ+) : ℝ) := by
      intro i
      have h2 := hfg i
      rw [show ((f i : ℕ+) : ℝ) = ((f i : ℕ) : ℝ) from rfl,
        show ((g i : ℕ+) : ℝ) = ((g i : ℕ) : ℝ) from rfl, ← Nat.cast_mul, h2]
    have hprod : ∏ i ∈ s, (f i : ℝ) = (d:ℝ)^s.card * ∏ i ∈ s, (g i : ℝ) := by
      rw [Finset.prod_congr rfl (fun i _ => hfgR i), Finset.prod_mul_distrib,
        Finset.prod_const]
    have hAM : ((f a : ℝ) + f b)/2 = (d:ℝ) * (((g a : ℝ) + g b)/2) := by
      rw [hfgR a, hfgR b]; ring
    rw [hprod, hAM, mul_pow] at hGM
    exact mul_left_cancel₀ (pow_ne_zero s.card (by exact_mod_cast hdpos.ne')) hGM
  -- Step 2: the values of g are coprime.
  have hgcd : Finset.univ.gcd (fun i => (g i : ℕ)) = 1 := by
    have h2 : d * Finset.univ.gcd (fun j => (g j : ℕ)) ∣
        Finset.univ.gcd (fun i => (f i : ℕ)) := by
      apply Finset.dvd_gcd
      intro i _
      rw [hfg i]
      exact mul_dvd_mul_left d (Finset.gcd_dvd (Finset.mem_univ i))
    rw [← hd] at h2
    have h3 := Nat.le_of_dvd hdpos h2
    nth_rw 2 [← mul_one d] at h3
    have h4 := le_of_mul_le_mul_left h3 hdpos
    have h5 : 0 < Finset.univ.gcd (fun j => (g j : ℕ)) :=
      Nat.pos_of_dvd_of_pos (Finset.gcd_dvd (Finset.mem_univ i0)) (g i0).pos
    exact le_antisymm h4 h5
  -- Step 3: let i1 be an index where g attains its maximum.
  have huniv : (Finset.univ : Finset α).Nonempty := Finset.univ_nonempty
  obtain ⟨i1, -, hmax⟩ := Finset.exists_max_image Finset.univ (fun i => (g i : ℕ)) huniv
  have hmax' : ∀ i, (g i : ℕ) ≤ (g i1 : ℕ) := fun i => hmax i (Finset.mem_univ i)
  by_cases hM : (g i1 : ℕ) ≤ 1
  · -- If the maximum is 1, every value is 1, hence every f-value equals d.
    refine ⟨⟨d, hdpos⟩, fun a => ?_⟩
    have hga : (g a : ℕ) = 1 := le_antisymm ((hmax' a).trans hM) (g a).pos
    apply Subtype.ext
    show (f a : ℕ) = d
    rw [hfg a, hga, mul_one]
  · -- Otherwise derive a contradiction.
    push Not at hM
    set P := Nat.minFac (g i1 : ℕ) with hP
    have hPprime : Nat.Prime P := Nat.minFac_prime (ne_of_gt hM)
    have hPdvd : P ∣ (g i1 : ℕ) := Nat.minFac_dvd _
    have hex : ∃ i, ¬ P ∣ (g i : ℕ) := by
      by_contra hall
      push Not at hall
      have h1 : P ∣ Finset.univ.gcd (fun i => (g i : ℕ)) :=
        Finset.dvd_gcd fun i _ => hall i
      rw [hgcd] at h1
      exact hPprime.not_dvd_one h1
    obtain ⟨m0, hm0mem, hm0max⟩ := Finset.exists_max_image
      (Finset.univ.filter fun i => ¬ P ∣ (g i : ℕ)) (fun i => (g i : ℕ))
      (Finset.filter_nonempty_iff.mpr (by
        obtain ⟨i, hi⟩ := hex
        exact ⟨i, Finset.mem_univ i, hi⟩))
    rw [Finset.mem_filter] at hm0mem
    -- every value larger than g m0 is divisible by P
    have hgt : ∀ i, (g m0 : ℕ) < (g i : ℕ) → P ∣ (g i : ℕ) := by
      intro i hi
      by_contra hndiv
      have himem : i ∈ Finset.univ.filter (fun j => ¬ P ∣ (g j : ℕ)) := by
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ i, hndiv⟩
      have hle : (g i : ℕ) ≤ (g m0 : ℕ) := hm0max i himem
      omega
    have hne : i1 ≠ m0 := by
      intro heq
      rw [heq] at hPdvd
      exact hm0mem.2 hPdvd
    -- apply the property to the pair (i1, m0)
    obtain ⟨s, hs, hGM⟩ := hprop hne
    have hk : s.card ≠ 0 := Nat.ne_of_gt hs.card_pos
    unfold geometric_mean at hGM
    have hx2 : 0 ≤ ∏ i ∈ s, (g i : ℝ) := Finset.prod_nonneg fun i _ => by positivity
    have hy2 : 0 ≤ ((g i1 : ℝ) + g m0)/2 := by positivity
    rw [rpow_inv_eq_iff hx2 hy2 hk] at hGM
    -- restate with natural-number casts for convenience
    have hGM' : (∏ i ∈ s, ((g i : ℕ) : ℝ)) =
        ((((g i1 : ℕ) : ℝ) + ((g m0 : ℕ) : ℝ))/2) ^ s.card := hGM
    have hnat : ((g i1 : ℕ) + (g m0 : ℕ)) ^ s.card =
        2 ^ s.card * ∏ i ∈ s, (g i : ℕ) := by
      have hr : (((g i1 : ℕ):ℝ) + ((g m0 : ℕ):ℝ)) ^ s.card =
          (2:ℝ) ^ s.card * (∏ i ∈ s, ((g i : ℕ) : ℝ)) := by
        rw [hGM', ← mul_pow]
        congr 1
        ring
      exact_mod_cast hr
    -- g m0 < g i1
    have h1lt : (g m0 : ℕ) < (g i1 : ℕ) := by
      have hle1 := hmax' m0
      have hneq : (g m0 : ℕ) ≠ (g i1 : ℕ) := fun heq => hm0mem.2 (heq ▸ hPdvd)
      omega
    -- the collection contains a value larger than g m0
    have hgt2 : ∃ i ∈ s, (g m0 : ℕ) < (g i : ℕ) := by
      by_contra hall
      push Not at hall
      have hle : ∏ i ∈ s, (g i : ℕ) ≤ (g m0 : ℕ) ^ s.card :=
        Finset.prod_le_pow_card s (fun i => (g i : ℕ)) (g m0 : ℕ) hall
      have hlt : (((g m0 : ℕ) ^ s.card : ℕ) : ℝ) < (∏ i ∈ s, ((g i : ℕ) : ℝ)) := by
        rw [hGM', Nat.cast_pow]
        have hr : ((g m0 : ℕ) : ℝ) < ((g i1 : ℕ) : ℝ) := by exact_mod_cast h1lt
        have hbase : ((g m0 : ℕ) : ℝ) < (((g i1 : ℕ) : ℝ) + (g m0 : ℕ))/2 := by linarith
        exact pow_lt_pow_left₀ hbase (Nat.cast_nonneg _) hk
      have hle2 : ((∏ i ∈ s, ((g i : ℕ) : ℝ))) ≤ (((g m0 : ℕ) ^ s.card : ℕ) : ℝ) := by
        exact_mod_cast hle
      exact absurd (lt_of_lt_of_le hlt hle2) (lt_irrefl _)
    obtain ⟨i', hi'mem, hi'⟩ := hgt2
    -- conclude P ∣ g m0, a contradiction
    have hPdN : P ∣ ∏ i ∈ s, (g i : ℕ) :=
      (hgt i' hi').trans (Finset.dvd_prod_of_mem _ hi'mem)
    have hPdsum : P ∣ (g i1 : ℕ) + (g m0 : ℕ) := by
      have h2 : P ∣ ((g i1 : ℕ) + (g m0 : ℕ)) ^ s.card := by
        rw [hnat]
        exact dvd_mul_of_dvd_right hPdN _
      exact hPprime.dvd_of_dvd_pow h2
    have hfin : P ∣ (g m0 : ℕ) := by
      exact (Nat.dvd_add_iff_right hPdvd).mpr hPdsum
    exact absurd hfin hm0mem.2
snip end

problem imo2020_p5 (n : ℕ) :
    n ∈ SolutionSet ↔
    (1 < n ∧
     (∀ f : Fin n → ℕ+,
        (Pairwise fun a b ↦ ∃ s : Finset (Fin n),
          s.Nonempty ∧ geometric_mean f s = (((f a):ℝ) + f b) / 2)
        → ∃ y, ∀ a, f a = y )) := by
  constructor
  · intro hn
    have h1 : 1 < n := hn
    refine ⟨h1, ?_⟩
    intro f hf
    exact @all_equal (Fin n) _ ⟨1, h1⟩ f hf
  · rintro ⟨h1, -⟩
    exact h1

end Imo2020P5
