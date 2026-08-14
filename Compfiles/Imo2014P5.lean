/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Rat.Star
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FieldSimp.Lemmas
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Preprocessing
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Ring.Basic
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Olympiad 2014, Problem 5

For every positive integer n, the Bank of Cape Town issues coins of
denomination 1/n. Given a finite collection of such coins (of not
necessarily different denominations) with total value at most 99 + 1/2,
prove that it is possible to split this collection into 100 or fewer
groups, such that each group has total value at most 1.
-/

namespace Imo2014P5

snip begin

/-- The total value of a collection of coins, where a coin of denomination `n`
is worth `(n : ℚ)⁻¹`. -/
def value (c : Multiset ℕ) : ℚ := (c.map fun n : ℕ ↦ (n : ℚ)⁻¹).sum

lemma value_zero : value 0 = 0 := by simp [value]

lemma value_add (c d : Multiset ℕ) : value (c + d) = value c + value d := by
  simp [value]

lemma value_cons (n : ℕ) (c : Multiset ℕ) :
    value (n ::ₘ c) = (n : ℚ)⁻¹ + value c := by
  simp [value]

lemma value_singleton (n : ℕ) : value {n} = (n : ℚ)⁻¹ := by simp [value]

lemma value_replicate (t n : ℕ) :
    value (Multiset.replicate t n) = (t : ℚ) * (n : ℚ)⁻¹ := by
  rw [value, Multiset.map_replicate, Multiset.sum_replicate, nsmul_eq_mul]

lemma value_nonneg (c : Multiset ℕ) : 0 ≤ value c := by
  apply Multiset.sum_nonneg
  intro x hx
  simp only [Multiset.mem_map] at hx
  obtain ⟨n, -, rfl⟩ := hx
  exact inv_nonneg.mpr (Nat.cast_nonneg _)

lemma value_sum {ι : Type*} (s : Finset ι) (f : ι → Multiset ℕ) :
    value (∑ m ∈ s, f m) = ∑ m ∈ s, value (f m) := by
  classical
  induction s using Finset.induction with
  | empty => simp [value]
  | insert a s ha IH => rw [Finset.sum_insert ha, value_add, IH, Finset.sum_insert ha]

/-- The capacity bound: any collection of total value at most `cap k` can be
split into `k` or fewer groups each of value at most `1`. -/
def cap (k : ℕ) : ℚ := k - k / (2 * k + 1)

lemma cap_eq' (k : ℕ) : cap k = (k : ℚ) * (1 - (2 * (k : ℚ) + 1)⁻¹) := by
  rw [cap, div_eq_mul_inv]; ring

lemma cap_sub_one_le (k : ℕ) : cap k - 1 ≤ cap (k - 1) := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; norm_num [cap]
  · have h1 : ((k - 1 : ℕ) : ℚ) = (k : ℚ) - 1 := Nat.cast_sub hk
    rw [cap, cap, h1]
    have h1q : (1 : ℚ) ≤ (k : ℚ) := by exact_mod_cast hk
    have h2k1 : (0 : ℚ) < 2 * ((k : ℚ) - 1) + 1 := by linarith
    have h2kp1 : (0 : ℚ) < 2 * (k : ℚ) + 1 := by linarith
    have key : ((k : ℚ) - 1) / (2 * ((k : ℚ) - 1) + 1) ≤ (k : ℚ) / (2 * (k : ℚ) + 1) := by
      rw [div_le_div_iff₀ h2k1 h2kp1]
      nlinarith
    linarith

lemma exists_mem_of_mem_sum {s : Multiset (Multiset ℕ)} {a : ℕ} (h : a ∈ s.sum) :
    ∃ t ∈ s, a ∈ t := by
  induction s using Multiset.induction_on with
  | empty => simp at h
  | cons x s IH =>
    rw [Multiset.sum_cons, Multiset.mem_add] at h
    rcases h with h | h
    · exact ⟨x, Multiset.mem_cons_self x s, h⟩
    · obtain ⟨t, ht, ha⟩ := IH h
      exact ⟨t, Multiset.mem_cons_of_mem ht, ha⟩

lemma count_sum_filter_boxes (k : ℕ) (c : Multiset ℕ) (n : ℕ) :
    Multiset.count n (∑ m ∈ Finset.range k, c.filter (fun p ↦ p = 2 * m + 1 ∨ p = 2 * m + 2))
      = ∑ m ∈ Finset.range k,
        (if (n = 2 * m + 1 ∨ n = 2 * m + 2) then Multiset.count n c else 0) := by
  rw [show (∑ m ∈ Finset.range k, c.filter (fun p ↦ p = 2 * m + 1 ∨ p = 2 * m + 2))
        = ((Finset.range k).1.map
          fun m ↦ c.filter fun p ↦ p = 2 * m + 1 ∨ p = 2 * m + 2).sum from rfl,
    Multiset.count_sum]
  simp only [Multiset.count_filter]
  rfl

lemma filter_boxes_add_pile (k : ℕ) (c : Multiset ℕ) (hpos : ∀ n ∈ c, 0 < n) :
    (∑ m ∈ Finset.range k, c.filter (fun p ↦ p = 2 * m + 1 ∨ p = 2 * m + 2))
      + c.filter (fun p ↦ 2 * k + 1 ≤ p) = c := by
  ext n
  rw [Multiset.count_add, count_sum_filter_boxes, Multiset.count_filter]
  by_cases hn0 : n = 0
  · subst hn0
    have hcount0 : Multiset.count 0 c = 0 :=
      Multiset.count_eq_zero.mpr (fun h ↦ absurd (hpos 0 h) (by lia))
    rw [Finset.sum_eq_zero (fun m _ ↦ ite_eq_right (by lia)), ite_eq_right (by lia), hcount0]
  · have hn1 : 1 ≤ n := Nat.pos_of_ne_zero hn0
    by_cases hn2k : n ≤ 2 * k
    · have hm0k : (n - 1) / 2 < k := by lia
      have hPm0 : n = 2 * ((n - 1) / 2) + 1 ∨ n = 2 * ((n - 1) / 2) + 2 := by lia
      rw [Finset.sum_eq_single_of_mem ((n - 1) / 2) (Finset.mem_range.mpr hm0k)
        (f := fun m ↦ if (n = 2 * m + 1 ∨ n = 2 * m + 2) then Multiset.count n c else 0)]
      · rw [ite_eq_left hPm0, ite_eq_right (by lia), add_zero]
      · intro b hb hbne
        rw [Finset.mem_range] at hb
        exact ite_eq_right (by rintro (h | h) <;> lia)
    · have hn2k' : 2 * k + 1 ≤ n := by lia
      rw [Finset.sum_eq_zero (fun m hm ↦ ite_eq_right (by
          have hm' := Finset.mem_range.mp hm
          rintro (h | h) <;> lia)), ite_eq_left hn2k', zero_add]

lemma value_filter_box_le (c : Multiset ℕ)
    (heven : ∀ m, 1 ≤ m → c.count (2 * m) ≤ 1)
    (hodd : ∀ m, c.count (2 * m + 1) ≤ 2 * m) (m : ℕ) :
    value (c.filter (fun p ↦ p = 2 * m + 1 ∨ p = 2 * m + 2))
      ≤ (2 * m : ℚ) * ((2 * m + 1 : ℕ) : ℚ)⁻¹ + ((2 * m + 2 : ℕ) : ℚ)⁻¹ := by
  have hPQ : c.filter (fun p ↦ p = 2 * m + 1 ∨ p = 2 * m + 2)
      = c.filter (· = 2 * m + 1) + c.filter (· = 2 * m + 2) := by
    ext n
    rw [Multiset.count_add, Multiset.count_filter, Multiset.count_filter, Multiset.count_filter]
    by_cases h1 : n = 2 * m + 1
    · rw [ite_eq_left (Or.inl h1), ite_eq_left h1, ite_eq_right (by lia), add_zero]
    · by_cases h2 : n = 2 * m + 2
      · rw [ite_eq_left (Or.inr h2), ite_eq_right h1, ite_eq_left h2, zero_add]
      · rw [ite_eq_right (not_or.mpr ⟨h1, h2⟩), ite_eq_right h1, ite_eq_right h2, add_zero]
  rw [hPQ, Multiset.filter_eq', Multiset.filter_eq', value_add, value_replicate, value_replicate]
  have h1 : (c.count (2 * m + 1) : ℚ) ≤ (2 * m : ℚ) := by exact_mod_cast hodd m
  have h2 : (c.count (2 * m + 2) : ℚ) ≤ (1 : ℚ) := by
    exact_mod_cast heven (m + 1) (Nat.succ_pos m)
  have h3 : (0 : ℚ) ≤ ((2 * m + 1 : ℕ) : ℚ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  have h4 : (0 : ℚ) ≤ ((2 * m + 2 : ℕ) : ℚ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  have h := add_le_add (mul_le_mul_of_nonneg_right h1 h3) (mul_le_mul_of_nonneg_right h2 h4)
  rwa [one_mul] at h

lemma box_capacity_lt_one (m : ℕ) :
    (2 * m : ℚ) * ((2 * m + 1 : ℕ) : ℚ)⁻¹ + ((2 * m + 2 : ℕ) : ℚ)⁻¹ < 1 := by
  have h1 : (2 * m : ℚ) * ((2 * m + 1 : ℕ) : ℚ)⁻¹ = 1 - ((2 * m + 1 : ℕ) : ℚ)⁻¹ := by
    have hx : ((2 * m + 1 : ℕ) : ℚ) = 2 * (m : ℚ) + 1 := by push_cast; ring
    rw [hx]
    have hne : (2 * (m : ℚ) + 1) ≠ 0 := by positivity
    field_simp
    ring
  have h2 : ((2 * m + 2 : ℕ) : ℚ)⁻¹ < ((2 * m + 1 : ℕ) : ℚ)⁻¹ := by
    have hpos : (0 : ℚ) < ((2 * m + 1 : ℕ) : ℚ) := by exact_mod_cast Nat.succ_pos (2 * m)
    have hlt : ((2 * m + 1 : ℕ) : ℚ) < ((2 * m + 2 : ℕ) : ℚ) := by
      exact_mod_cast Nat.lt_succ_self (2 * m + 1)
    have := one_div_lt_one_div_of_lt hpos hlt
    rwa [inv_eq_one_div, inv_eq_one_div]
  linarith

/-- Greedy distribution of the "light" coins (of denomination at least `2k+1`)
into the `k` boxes: as long as a coin remains, some box still has room for it,
for otherwise the total value would exceed `cap k`. -/
lemma greedy (k : ℕ) (pile : Multiset ℕ) :
    (∀ n ∈ pile, 2 * k + 1 ≤ n) → ∀ w : Fin k → ℚ, (∀ m, w m ≤ 1) →
    value pile + ∑ m, w m ≤ cap k →
    ∃ parts : Fin k → Multiset ℕ,
      (∑ m, parts m) = pile ∧ ∀ m, w m + value (parts m) ≤ 1 := by
  induction pile using Multiset.induction_on with
  | empty =>
    intro _ w hw _
    exact ⟨fun _ ↦ 0, Finset.sum_const_zero, fun m ↦ by simpa [value] using hw m⟩
  | cons n rest IH =>
    intro hpile w hw htot
    have hn : 2 * k + 1 ≤ n := hpile n (Multiset.mem_cons_self n rest)
    have hrest : ∀ m ∈ rest, 2 * k + 1 ≤ m :=
      fun m hm ↦ hpile m (Multiset.mem_cons_of_mem hm)
    have hnpos : (0 : ℚ) < (n : ℚ)⁻¹ :=
      inv_pos.mpr (by exact_mod_cast (by lia : 0 < n))
    have hrest_nonneg : 0 ≤ value rest := value_nonneg rest
    obtain ⟨m0, hm0⟩ : ∃ m0 : Fin k, w m0 + (n : ℚ)⁻¹ ≤ 1 := by
      by_contra hcon
      push Not at hcon
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk
        have hsum0 : (∑ m : Fin 0, w m) = 0 :=
          Finset.sum_eq_zero (fun m _ ↦ absurd m.2 (Nat.not_lt_zero _))
        rw [value_cons, hsum0] at htot
        have hcap0 : cap 0 = 0 := by norm_num [cap]
        rw [hcap0] at htot
        linarith
      · have hne : (Finset.univ : Finset (Fin k)).Nonempty :=
          Finset.univ_nonempty_iff.mpr ⟨⟨0, hk⟩⟩
        have hlt : (∑ m : Fin k, (1 - (n : ℚ)⁻¹)) < ∑ m : Fin k, w m :=
          Finset.sum_lt_sum_of_nonempty hne (fun m _ ↦ by have h := hcon m; linarith)
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hlt
        have hcaple : cap k ≤ (k : ℚ) * (1 - (n : ℚ)⁻¹) := by
          rw [cap_eq']
          have hinv : (n : ℚ)⁻¹ ≤ (2 * (k : ℚ) + 1)⁻¹ := by
            rw [inv_eq_one_div, inv_eq_one_div]
            exact one_div_le_one_div_of_le
              (by positivity) (by exact_mod_cast hn)
          have hnonneg : (0 : ℚ) ≤ 1 - (2 * (k : ℚ) + 1)⁻¹ := by
            have hle1 : (1 : ℚ) ≤ 2 * (k : ℚ) + 1 := by
              have h0 := Nat.cast_nonneg (α := ℚ) k
              linarith
            have h1 := inv_le_one_of_one_le₀ hle1
            linarith
          exact mul_le_mul le_rfl (by linarith) hnonneg (Nat.cast_nonneg k)
        rw [value_cons] at htot
        linarith
    -- Place the coin in box `m0` and continue with the remaining pile.
    have hsum : (∑ m, Function.update w m0 (w m0 + (n : ℚ)⁻¹) m)
        = (∑ m, w m) + (n : ℚ)⁻¹ := by
      rw [Finset.sum_update_of_mem (Finset.mem_univ m0)]
      have h2 := Finset.sum_eq_sum_sdiff_singleton_add (Finset.mem_univ m0) (f := w)
      linarith
    have htot' : value rest + ∑ m, Function.update w m0 (w m0 + (n : ℚ)⁻¹) m ≤ cap k := by
      rw [hsum, value_cons] at *
      linarith
    have hw' : ∀ m, Function.update w m0 (w m0 + (n : ℚ)⁻¹) m ≤ 1 := by
      intro m
      by_cases h : m = m0
      · subst h; rwa [Function.update_self]
      · rw [Function.update_of_ne h]; exact hw m
    obtain ⟨parts', hp'sum, hp'val⟩ := IH hrest _ hw' htot'
    refine ⟨Function.update parts' m0 (n ::ₘ parts' m0), ?_, ?_⟩
    · have e1 := Finset.sum_update_of_mem (Finset.mem_univ m0) parts' (n ::ₘ parts' m0)
      have e2 := Finset.sum_eq_sum_sdiff_singleton_add (Finset.mem_univ m0) (f := parts')
      rw [e1]
      have heq : (n ::ₘ parts' m0) + ∑ m ∈ Finset.univ \ {m0}, parts' m
          = {n} + ((∑ m ∈ Finset.univ \ {m0}, parts' m) + parts' m0) := by
        rw [← Multiset.singleton_add, add_assoc,
          add_comm (parts' m0) (∑ m ∈ Finset.univ \ {m0}, parts' m)]
      rw [heq, ← e2, hp'sum, Multiset.singleton_add]
    · intro m
      by_cases h : m = m0
      · rw [h, Function.update_self, value_cons]
        have h1 := hp'val m0
        rw [Function.update_self] at h1
        linarith
      · rw [Function.update_of_ne h]
        have h1 := hp'val m
        rw [Function.update_of_ne h] at h1
        exact h1

/-- The main claim, proved by strong induction on the number of coins:
a collection of total value at most `cap k` admits a partition into at most
`k` groups each of value at most `1`. -/
theorem exists_partition_aux : ∀ (N k : ℕ) (c : Multiset ℕ), c.card = N →
    (∀ n ∈ c, 0 < n) → value c ≤ cap k →
    ∃ gs : Multiset (Multiset ℕ), gs.sum = c ∧ gs.card ≤ k ∧ ∀ g ∈ gs, value g ≤ 1 := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N IH =>
    rintro k c rfl hpos hcap
    by_cases heven : ∃ m, 1 ≤ m ∧ 2 ≤ c.count (2 * m)
    · -- Merge two coins of denomination `2m` into one coin of denomination `m`.
      obtain ⟨m, hm1, hm2⟩ := heven
      have hle : ({2 * m, 2 * m} : Multiset ℕ) ≤ c := by
        rw [Multiset.le_iff_count]
        intro n
        by_cases h : n = 2 * m
        · subst h
          rw [show ({2 * m, 2 * m} : Multiset ℕ) = 2 * m ::ₘ {2 * m} from rfl,
            Multiset.count_cons_self, Multiset.count_singleton_self]
          exact hm2
        · rw [show ({2 * m, 2 * m} : Multiset ℕ) = 2 * m ::ₘ {2 * m} from rfl,
            Multiset.count_cons_of_ne h, Multiset.count_singleton, ite_eq_right h]
          exact Nat.zero_le _
      obtain ⟨rest, rfl⟩ := Multiset.le_iff_exists_add.mp hle
      have hpair : value ({2 * m, 2 * m} : Multiset ℕ) = (m : ℚ)⁻¹ := by
        have h : ((2 * m : ℕ) : ℚ) = 2 * (m : ℚ) := by push_cast; ring
        rw [show ({2 * m, 2 * m} : Multiset ℕ) = 2 * m ::ₘ {2 * m} from rfl,
          value_cons, value_singleton, h, mul_inv]
        ring
      have hpos' : ∀ n ∈ m ::ₘ rest, 0 < n := by
        intro n hn
        rw [Multiset.mem_cons] at hn
        rcases hn with rfl | hn
        · exact hm1
        · exact hpos n (Multiset.mem_add.mpr (Or.inr hn))
      have hval' : value (m ::ₘ rest) ≤ cap k := by
        have h1 : value ({2 * m, 2 * m} + rest) = value (m ::ₘ rest) := by
          rw [value_add, hpair, value_cons]
        rwa [← h1]
      have hcardlt : (m ::ₘ rest).card < ({2 * m, 2 * m} + rest).card := by
        rw [Multiset.card_cons, Multiset.card_add]
        have hc2 : Multiset.card ({2 * m, 2 * m} : Multiset ℕ) = 2 := rfl
        lia
      obtain ⟨gs', hsum', hcard', hval''⟩ := IH _ hcardlt k (m ::ₘ rest) rfl hpos' hval'
      have hmgs : m ∈ gs'.sum := hsum' ▸ Multiset.mem_cons_self m rest
      obtain ⟨g', hg'mem, hmg'⟩ := exists_mem_of_mem_sum hmgs
      refine ⟨({2 * m, 2 * m} + g'.erase m) ::ₘ gs'.erase g', ?_, ?_, ?_⟩
      · have hg'sum : g' + (gs'.erase g').sum = gs'.sum := by
          rw [← Multiset.sum_cons, Multiset.cons_erase hg'mem]
        have hg'e : g' = m ::ₘ g'.erase m := (Multiset.cons_erase hmg').symm
        have hcancel : g'.erase m + (gs'.erase g').sum = rest := by
          have h1 : (m ::ₘ g'.erase m) + (gs'.erase g').sum = m ::ₘ rest := by
            rw [← hg'e, hg'sum, hsum']
          rw [← Multiset.singleton_add, ← Multiset.singleton_add, add_assoc] at h1
          exact add_left_cancel h1
        rw [Multiset.sum_cons]
        have hassoc : ({2 * m, 2 * m} + g'.erase m) + (gs'.erase g').sum
            = {2 * m, 2 * m} + (g'.erase m + (gs'.erase g').sum) := add_assoc _ _ _
        rw [hassoc, hcancel]
      · rw [Multiset.card_cons, Multiset.card_erase_add_one hg'mem]
        exact hcard'
      · intro g hg
        rw [Multiset.mem_cons] at hg
        rcases hg with rfl | hg
        · have h2 : value ({2 * m, 2 * m} + g'.erase m) = value g' := by
            rw [value_add, hpair, ← value_cons, Multiset.cons_erase hmg']
          rw [h2]; exact hval'' g' hg'mem
        · exact hval'' g (Multiset.mem_of_mem_erase hg)
    · by_cases hodd : ∃ m, 2 * m + 1 ≤ c.count (2 * m + 1)
      · -- Pull out `2m+1` coins of denomination `2m+1` as a group of value `1`.
        obtain ⟨m, hm⟩ := hodd
        have hle : Multiset.replicate (2 * m + 1) (2 * m + 1) ≤ c := by
          exact Multiset.le_count_iff_replicate_le.mp hm
        obtain ⟨rest, rfl⟩ := Multiset.le_iff_exists_add.mp hle
        have hvrep : value (Multiset.replicate (2 * m + 1) (2 * m + 1)) = 1 := by
          rw [value_replicate]
          exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _))
        have hval : value (Multiset.replicate (2 * m + 1) (2 * m + 1) + rest)
            = 1 + value rest := by rw [value_add, hvrep]
        have hpos' : ∀ n ∈ rest, 0 < n :=
          fun n hn ↦ hpos n (Multiset.mem_add.mpr (Or.inr hn))
        have hk1 : 1 ≤ k := by
          by_contra hk
          push Not at hk
          interval_cases k
          rw [hval] at hcap
          norm_num [cap] at hcap
          have := value_nonneg rest
          linarith
        have hval' : value rest ≤ cap (k - 1) := by
          have hstep := cap_sub_one_le k
          rw [hval] at hcap
          linarith
        have hcardlt : rest.card < (Multiset.replicate (2 * m + 1) (2 * m + 1) + rest).card := by
          rw [Multiset.card_add, Multiset.card_replicate]
          lia
        obtain ⟨gs', hsum', hcard', hval''⟩ := IH _ hcardlt (k - 1) rest rfl hpos' hval'
        refine ⟨Multiset.replicate (2 * m + 1) (2 * m + 1) ::ₘ gs', ?_, ?_, ?_⟩
        · rw [Multiset.sum_cons, hsum']
        · rw [Multiset.card_cons]
          lia
        · intro g hg
          rw [Multiset.mem_cons] at hg
          rcases hg with rfl | hg
          · rw [hvrep]
          · exact hval'' g hg
      · -- Normalized case: distribute the coins into boxes `B₀, …, B_{k-1}`,
        -- then greedily toss the remaining light coins into the boxes.
        push Not at heven hodd
        have heven' : ∀ m, 1 ≤ m → c.count (2 * m) ≤ 1 :=
          fun m hm ↦ Nat.le_of_lt_succ (heven m hm)
        have hodd' : ∀ m, c.count (2 * m + 1) ≤ 2 * m :=
          fun m ↦ Nat.le_of_lt_succ (hodd m)
        have hdecomp := filter_boxes_add_pile k c hpos
        have hdecomp' : c.filter (fun p ↦ 2 * k + 1 ≤ p)
            + (∑ m ∈ Finset.range k, c.filter (fun p ↦ p = 2 * m + 1 ∨ p = 2 * m + 2))
            = c := by
          rw [add_comm]; exact hdecomp
        have htotal : value (c.filter (fun p ↦ 2 * k + 1 ≤ p))
            + ∑ m : Fin k, value (c.filter (fun p ↦ p = 2 * (m : ℕ) + 1 ∨ p = 2 * (m : ℕ) + 2))
            ≤ cap k := by
          have h : value (c.filter (fun p ↦ 2 * k + 1 ≤ p))
              + ∑ m : Fin k, value (c.filter (fun p ↦ p = 2 * (m : ℕ) + 1 ∨ p = 2 * (m : ℕ) + 2))
              = value c := by
            rw [Fin.sum_univ_eq_sum_range
                (fun m ↦ value (c.filter (fun p ↦ p = 2 * m + 1 ∨ p = 2 * m + 2))) k,
              ← value_sum, ← value_add, hdecomp']
          rw [h]
          exact hcap
        have hw : ∀ m : Fin k,
            value (c.filter (fun p ↦ p = 2 * (m : ℕ) + 1 ∨ p = 2 * (m : ℕ) + 2)) ≤ 1 :=
          fun m ↦ le_of_lt (lt_of_le_of_lt (value_filter_box_le c heven' hodd' m)
            (box_capacity_lt_one m))
        obtain ⟨parts, hparts_sum, hparts_val⟩ := greedy k (c.filter fun p ↦ 2 * k + 1 ≤ p)
          (fun n hn ↦ (Multiset.mem_filter.mp hn).2)
          (fun m ↦ value (c.filter (fun p ↦ p = 2 * (m : ℕ) + 1 ∨ p = 2 * (m : ℕ) + 2)))
          hw htotal
        refine ⟨((Finset.univ : Finset (Fin k)).1.map fun m : Fin k ↦
          c.filter (fun p ↦ p = 2 * (m : ℕ) + 1 ∨ p = 2 * (m : ℕ) + 2) + parts m), ?_, ?_, ?_⟩
        · have hgsum : Multiset.sum ((Finset.univ : Finset (Fin k)).1.map fun m : Fin k ↦
              c.filter (fun p ↦ p = 2 * (m : ℕ) + 1 ∨ p = 2 * (m : ℕ) + 2) + parts m)
              = ∑ m : Fin k,
                (c.filter (fun p ↦ p = 2 * (m : ℕ) + 1 ∨ p = 2 * (m : ℕ) + 2) + parts m) := rfl
          rw [hgsum, Finset.sum_add_distrib, Fin.sum_univ_eq_sum_range
            (fun m ↦ c.filter (fun p ↦ p = 2 * m + 1 ∨ p = 2 * m + 2)) k, hparts_sum]
          exact hdecomp
        · rw [Multiset.card_map]
          have hcard : (Finset.univ : Finset (Fin k)).card = k := by
            rw [Finset.card_univ, Fintype.card_fin]
          exact hcard.le
        · intro g hg
          rw [Multiset.mem_map] at hg
          obtain ⟨m, -, rfl⟩ := hg
          rw [value_add]
          exact hparts_val m

theorem exists_partition (k : ℕ) (c : Multiset ℕ) (hpos : ∀ n ∈ c, 0 < n)
    (hcap : value c ≤ cap k) :
    ∃ gs : Multiset (Multiset ℕ), gs.sum = c ∧ gs.card ≤ k ∧ ∀ g ∈ gs, value g ≤ 1 :=
  exists_partition_aux c.card k c rfl hpos hcap

snip end

problem imo2014_p5 (c : Multiset ℕ) (hpos : ∀ n ∈ c, 0 < n)
    (hval : value c ≤ 99 + 1 / 2) :
    ∃ gs : Multiset (Multiset ℕ), gs.sum = c ∧ gs.card ≤ 100 ∧
      ∀ g ∈ gs, value g ≤ 1 := by
  have hcap : (99 + 1 / 2 : ℚ) ≤ cap 100 := by norm_num [cap]
  exact exists_partition 100 c hpos (le_trans hval hcap)

end Imo2014P5
