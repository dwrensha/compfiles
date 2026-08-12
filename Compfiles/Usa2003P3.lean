/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Tactic.NormNum.Ineq
public import ProblemExtraction

@[expose] public section

problem_file {
  tags := [.Combinatorics]
}

/-!
# USA Mathematical Olympiad 2003, Problem 3

Let n be a positive integer. For every sequence of integers
A = (a₀, a₁, a₂, . . . , aₙ) satisfying 0 ≤ aᵢ ≤ i, for i = 0, . . . , n,
we define another sequence t(A) = (t(a₀), t(a₁), t(a₂), . . . , t(aₙ))
by setting t(aᵢ) to be the number of terms in the sequence A that precede
the term aᵢ and are different from aᵢ. Show that, starting from any
sequence A as above, fewer than n applications of the transformation t
lead to a sequence B such that t(B) = B.
-/

namespace Usa2003P3

/-- The transformation `t`: `t a i` is the number of terms of `a` that precede
the `i`-th term and are different from it.

We model the sequence `A = (a₀, a₁, …, aₙ)` as a function `ℕ → ℕ` where only the
values at `0, 1, …, n` are constrained.  The problem prescribes integer values,
but the constraint `0 ≤ aᵢ` allows us to work with natural numbers throughout. -/
def t (a : ℕ → ℕ) : ℕ → ℕ :=
  fun i => ((Finset.range i).filter (fun j => a j ≠ a i)).card

snip begin

-- The proof follows Evan Chen's solution
-- (https://web.evanchen.cc/exams/USAMO-2003-notes.pdf): strong induction on `n`.
--
-- * If `a₁ = 1`, then `1 ≤ t(aᵢ)` for all `i ≥ 1`, and the shifted sequence
--   `bⱼ = t(a_{j+1}) - 1` is again admissible; one checks `t^[m] b j + 1 = t^[m+1] a (j+1)`,
--   so the induction hypothesis applied to `b` gives stability of `a` after `n-1` steps.
-- * Otherwise `a₁ = 0`.  If some `aₖ ≠ 0` with `k` minimal (so `k ≥ 2`), then
--   `k ≤ t^[2] a i` for all `i ≥ k`, and the shifted sequence
--   `cⱼ = t^[2] a (j+k) - k` is again admissible; one checks
--   `t^[m] c j + k = t^[m+2] a (j+k)`, so the induction hypothesis applied to `c`
--   gives stability of the terms `i ≥ k` after `n-k+1 ≤ n-1` steps, while the terms
--   `i < k` are identically zero after one step.

lemma t_def (a : ℕ → ℕ) (i : ℕ) :
    t a i = ((Finset.range i).filter (fun j => a j ≠ a i)).card := rfl

lemma t_zero (a : ℕ → ℕ) : t a 0 = 0 := by
  rw [t_def, Finset.range_zero, Finset.filter_empty, Finset.card_empty]

lemma t_le (a : ℕ → ℕ) (i : ℕ) : t a i ≤ i := by
  rw [t_def]
  exact le_trans (Finset.card_filter_le _ _) (Finset.card_range i).le

lemma t_eq_zero_of {b : ℕ → ℕ} {i : ℕ} (h : ∀ j < i, b j = b i) : t b i = 0 := by
  have he : (Finset.range i).filter (fun j => b j ≠ b i) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro j hj
    rw [Finset.mem_range] at hj
    simp [h j hj]
  rw [t_def, he, Finset.card_empty]

lemma one_le_t_of {b : ℕ → ℕ} {i j : ℕ} (hji : j < i) (h : b j ≠ b i) : 1 ≤ t b i := by
  rw [t_def]
  apply Finset.card_pos.mpr
  rw [Finset.filter_nonempty_iff]
  exact ⟨j, Finset.mem_range.mpr hji, h⟩

/-- If `a` is admissible at position `i`, then `a i ≤ t a i`. -/
lemma le_t (a : ℕ → ℕ) (i : ℕ) (h : ∀ j ≤ i, a j ≤ j) : a i ≤ t a i := by
  rw [t_def]
  by_cases hi : a i = 0
  · rw [hi]
    exact Nat.zero_le _
  · have sub : Finset.range (a i) ⊆ (Finset.range i).filter (fun j => a j ≠ a i) := by
      intro j hj
      rw [Finset.mem_range] at hj
      rw [Finset.mem_filter, Finset.mem_range]
      refine ⟨lt_of_lt_of_le hj (h i le_rfl), ?_⟩
      have h2 : a j ≤ j := h j (le_of_lt (lt_of_lt_of_le hj (h i le_rfl)))
      omega
    calc a i = (Finset.range (a i)).card := (Finset.card_range _).symm
      _ ≤ ((Finset.range i).filter (fun j => a j ≠ a i)).card := Finset.card_le_card sub

lemma iter_succ (m : ℕ) (b : ℕ → ℕ) : t^[m+1] b = t (t^[m] b) :=
  Function.iterate_succ_apply' t m b

lemma iter_t_zero (a : ℕ → ℕ) (m : ℕ) : t^[m+1] a 0 = 0 := by
  rw [iter_succ m a]
  exact t_zero _

lemma iter_t_le (a : ℕ → ℕ) (m : ℕ) (i : ℕ) : t^[m+1] a i ≤ i := by
  rw [iter_succ m a]
  exact t_le _ _

lemma iter_mono_succ (a : ℕ → ℕ) (i : ℕ) (m : ℕ) (hm : 1 ≤ m) :
    t^[m] a i ≤ t^[m+1] a i := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  rw [iter_succ (m+1) a]
  exact le_t (t^[m+1] a) i (fun j _ => iter_t_le _ _ _)

lemma iter_ge_of_le {a : ℕ → ℕ} {i p : ℕ} (h : p ≤ t^[1] a i) (m : ℕ) (hm : 1 ≤ m) :
    p ≤ t^[m] a i :=
  Nat.le_induction h (fun k hk IH => le_trans IH (iter_mono_succ a i k hk)) m hm

lemma iter_ge_two_of_le {a : ℕ → ℕ} {i p : ℕ} (h : p ≤ t^[2] a i) (m : ℕ) (hm : 2 ≤ m) :
    p ≤ t^[m] a i :=
  Nat.le_induction h (fun k hk IH => le_trans IH (iter_mono_succ a i k (by omega))) m hm

/-- The values `t^[m] a j` for `j ≤ i` only depend on the values `a j` for `j ≤ i`. -/
lemma iter_congr {a b : ℕ → ℕ} {i : ℕ} (h : ∀ j ≤ i, a j = b j) :
    ∀ m, ∀ j ≤ i, t^[m] a j = t^[m] b j := by
  intro m
  induction m with
  | zero => exact fun j hj => h j hj
  | succ m IH =>
    intro j hj
    rw [iter_succ m a, iter_succ m b, t_def, t_def]
    congr 1
    apply Finset.filter_congr
    intro l hl
    rw [Finset.mem_range] at hl
    have h1 := IH l (le_trans (le_of_lt hl) hj)
    have h2 := IH j hj
    rw [h1, h2]

/-- Once a whole initial segment is stable, it stays stable. -/
lemma iter_stable_add (a : ℕ → ℕ) {N p : ℕ}
    (h : ∀ i ≤ N, t^[p] a i = t^[p+1] a i) :
    ∀ q, ∀ i ≤ N, t^[p+q] a i = t^[p+q+1] a i := by
  intro q
  induction q with
  | zero => exact fun i hi => h i hi
  | succ q IH =>
    intro i hi
    rw [← add_assoc, iter_succ (p+q) a,
      iter_succ ((p+q)+1) a, t_def, t_def]
    congr 1
    apply Finset.filter_congr
    intro l hl
    rw [Finset.mem_range] at hl
    have h1 := IH l (le_trans (le_of_lt hl) hi)
    have h2 := IH i hi
    rw [h1, h2]

/-- If the first `k` terms of `a` are all zero, they stay zero forever. -/
lemma iter_eq_zero {a : ℕ → ℕ} {k : ℕ} (hz : ∀ i < k, a i = 0) :
    ∀ m, ∀ i < k, t^[m+1] a i = 0 := by
  intro m
  induction m with
  | zero =>
    intro i hi
    show t a i = 0
    apply t_eq_zero_of
    intro j hj
    rw [hz j (lt_trans hj hi), hz i hi]
  | succ m IH =>
    intro i hi
    rw [iter_succ (m+1) a]
    apply t_eq_zero_of
    intro j hj
    rw [IH j (lt_trans hj hi), IH i hi]

/-- Counting elements `m < j + k` with `p m`, when `p` holds on all of `[0, k)`. -/
lemma range_add_filter_card (p : ℕ → Prop) [DecidablePred p] (j k : ℕ)
    (hk : ∀ m < k, p m) :
    ((Finset.range (j+k)).filter p).card
      = k + ((Finset.range j).filter (fun l => p (l + k))).card := by
  have hdis : Disjoint (Finset.range k)
      (((Finset.range j).filter (fun l => p (l + k))).map
        (⟨(· + k), add_left_injective k⟩ : ℕ ↪ ℕ)) := by
    rw [Finset.disjoint_left]
    intro m hm hmem
    rw [Finset.mem_range] at hm
    rw [Finset.mem_map] at hmem
    obtain ⟨l, -, hl⟩ := hmem
    have hlm : l + k = m := hl
    omega
  have hset : (Finset.range (j+k)).filter p
      = Finset.range k ∪ (((Finset.range j).filter (fun l => p (l + k))).map
          (⟨(· + k), add_left_injective k⟩ : ℕ ↪ ℕ)) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union, Finset.mem_map,
      Function.Embedding.coeFn_mk]
    constructor
    · intro h
      obtain ⟨hm, hd⟩ := h
      by_cases hmk : m < k
      · exact Or.inl hmk
      · refine Or.inr ⟨m - k, ⟨by omega, ?_⟩, ?_⟩
        · rwa [Nat.sub_add_cancel (by omega : k ≤ m)]
        · show m - k + k = m
          omega
    · intro h
      rcases h with hmk | ⟨l, ⟨hl, hd⟩, rfl⟩
      · exact ⟨by omega, hk m hmk⟩
      · refine ⟨?_, hd⟩
        show l + k < j + k
        omega
  rw [hset, Finset.card_union_of_disjoint hdis, Finset.card_map, Finset.card_range]

/-- The key commutation relation for the case `a₁ = 1`: with `bⱼ = t a (j+1) - 1`,
iterating `t` on `b` simulates iterating `t` on `a`, shifted by one index. -/
lemma comm1 {a : ℕ → ℕ} {n : ℕ}
    (hP1 : ∀ i, 1 ≤ i → i ≤ n → ∀ m, 1 ≤ m → 1 ≤ t^[m] a i) :
    ∀ m, ∀ j, j + 1 ≤ n →
      t^[m] (fun j => t a (j+1) - 1) j + 1 = t^[m+1] a (j+1) := by
  intro m
  induction m with
  | zero =>
    intro j hj
    show (t a (j+1) - 1) + 1 = t a (j+1)
    have h : 1 ≤ t a (j+1) := hP1 (j+1) (by omega) hj 1 le_rfl
    omega
  | succ m IH =>
    intro j hj
    rw [iter_succ m (fun j => t a (j+1) - 1), t_def]
    have hfilter : (Finset.range j).filter
          (fun l => t^[m] (fun j => t a (j+1) - 1) l ≠ t^[m] (fun j => t a (j+1) - 1) j)
        = (Finset.range j).filter (fun l => t^[m+1] a (l+1) ≠ t^[m+1] a (j+1)) := by
      apply Finset.filter_congr
      intro l hl
      rw [Finset.mem_range] at hl
      have h1 := IH l (by omega)
      have h2 := IH j hj
      have hp1 := hP1 (l+1) (by omega) (by omega) (m+1) (by omega)
      have hp2 := hP1 (j+1) (by omega) hj (m+1) (by omega)
      constructor <;> intro h3 <;> omega
    rw [hfilter, iter_succ (m+1) a, t_def]
    have h0 : t^[m+1] a 0 ≠ t^[m+1] a (j+1) := by
      rw [iter_t_zero a m]
      have hp2 := hP1 (j+1) (by omega) hj (m+1) (by omega)
      omega
    have hcount : ((Finset.range (j+1)).filter (fun m' => t^[m+1] a m' ≠ t^[m+1] a (j+1))).card
        = 1 + ((Finset.range j).filter (fun l => t^[m+1] a (l+1) ≠ t^[m+1] a (j+1))).card :=
      range_add_filter_card _ j 1 (fun m' hm' => by
        rw [Nat.lt_one_iff.mp hm']
        exact h0)
    omega

/-- The key commutation relation for the case `a₀ = a₁ = ⋯ = aₖ₋₁ = 0 < aₖ`:
with `cⱼ = t^[2] a (j+k) - k`, iterating `t` on `c` simulates iterating `t` on `a`,
shifted by `k` indices. -/
lemma comm2 {a : ℕ → ℕ} {n k : ℕ} (hk1 : 1 ≤ k)
    (hz : ∀ m, ∀ i < k, t^[m+1] a i = 0)
    (hge : ∀ i, k ≤ i → i ≤ n → ∀ m, k ≤ t^[m+2] a i) :
    ∀ m, ∀ j, j + k ≤ n →
      t^[m] (fun j => t^[2] a (j+k) - k) j + k = t^[m+2] a (j+k) := by
  intro m
  induction m with
  | zero =>
    intro j hj
    show (t^[2] a (j+k) - k) + k = t^[2] a (j+k)
    have h : k ≤ t^[2] a (j+k) := hge (j+k) (by omega) hj 0
    omega
  | succ m IH =>
    intro j hj
    rw [iter_succ m (fun j => t^[2] a (j+k) - k), t_def]
    have hfilter : (Finset.range j).filter
          (fun l => t^[m] (fun j => t^[2] a (j+k) - k) l ≠ t^[m] (fun j => t^[2] a (j+k) - k) j)
        = (Finset.range j).filter (fun l => t^[m+2] a (l+k) ≠ t^[m+2] a (j+k)) := by
      apply Finset.filter_congr
      intro l hl
      rw [Finset.mem_range] at hl
      have h1 := IH l (by omega)
      have h2 := IH j hj
      have hp1 := hge (l+k) (by omega) (by omega) m
      have hp2 := hge (j+k) (by omega) hj m
      constructor <;> intro h3 <;> omega
    rw [hfilter, add_right_comm, iter_succ (m+2) a, t_def]
    have h0 : ∀ m' < k, t^[m+2] a m' ≠ t^[m+2] a (j+k) := by
      intro m' hm'
      have e1 : t^[m+2] a m' = 0 := hz (m+1) m' hm'
      have hp2 := hge (j+k) (by omega) hj m
      omega
    have hcount : ((Finset.range (j+k)).filter (fun m' => t^[m+2] a m' ≠ t^[m+2] a (j+k))).card
        = k + ((Finset.range j).filter (fun l => t^[m+2] a (l+k) ≠ t^[m+2] a (j+k))).card :=
      range_add_filter_card _ j k h0
    omega

/-- The main induction: after `n-1` applications of `t`, the sequence is stable. -/
theorem main_aux (n : ℕ) : 1 ≤ n → ∀ a : ℕ → ℕ, (∀ i ≤ n, a i ≤ i) →
    ∀ i ≤ n, t^[n-1] a i = t^[n] a i := by
  induction n using Nat.strongRecOn with
  | _ n IH =>
    intro hn a ha i hi
    by_cases hn1 : n = 1
    · -- Base case `n = 1`: `a = (0, a₁)` with `a₁ ≤ 1`, and `t a = a` on `{0, 1}`.
      subst hn1
      have h0 : a 0 = 0 := by have h := ha 0 (by norm_num); omega
      have hi01 : i = 0 ∨ i = 1 := by omega
      rcases hi01 with rfl | rfl
      · show t^[0] a 0 = t^[1] a 0
        show a 0 = t a 0
        rw [h0, t_zero a]
      · show a 1 = t a 1
        by_cases h1 : a 1 = 0
        · rw [h1]
          symm
          apply t_eq_zero_of
          intro j hj
          rw [Nat.lt_one_iff.mp hj, h0, h1]
        · have h1v : a 1 = 1 := by have hle := ha 1 le_rfl; omega
          have hge : a 1 ≤ t a 1 := le_t a 1 (fun j hj => ha j (by omega))
          have hle2 : t a 1 ≤ 1 := t_le a 1
          omega
    · -- Inductive step, `n ≥ 2`.
      have hn2 : 2 ≤ n := by omega
      have hn3 : n - 1 = n - 2 + 1 := by omega
      have ha1 : a 1 ≤ 1 := ha 1 (by omega)
      by_cases hcase : a 1 = 1
      · -- Case 1: `a₁ = 1`.  Then `t^[m] a i ≥ 1` for all `m ≥ 1`, `1 ≤ i ≤ n`.
        have hP1 : ∀ i, 1 ≤ i → i ≤ n → ∀ m, 1 ≤ m → 1 ≤ t^[m] a i := by
          intro i' hi1 hin m hm
          apply iter_ge_of_le (m := m) (hm := hm)
          show 1 ≤ t a i'
          by_cases hai : a i' = 0
          · have hi2 : 1 < i' := by
              rcases (by omega : i' = 1 ∨ 1 < i') with rfl | h'
              · exact absurd hai (by rw [hcase]; exact one_ne_zero)
              · exact h'
            exact one_le_t_of hi2 (by rw [hcase, hai]; exact one_ne_zero)
          · have h0 : a 0 = 0 := by have h := ha 0 (by omega); omega
            exact one_le_t_of (j := 0) (by omega) (by rw [h0]; omega)
        have hcomm : ∀ m, ∀ j, j + 1 ≤ n →
            t^[m] (fun j => t a (j+1) - 1) j + 1 = t^[m+1] a (j+1) := comm1 hP1
        have hbvalid : ∀ j ≤ n - 1, (fun j => t a (j+1) - 1) j ≤ j := by
          intro j hj
          show t a (j+1) - 1 ≤ j
          have h := t_le a (j+1)
          omega
        have IHb : ∀ j ≤ n - 1, t^[n-1-1] (fun j => t a (j+1) - 1) j
            = t^[n-1] (fun j => t a (j+1) - 1) j := IH (n-1) (by omega) (by omega) _ hbvalid
        rcases (by omega : i = 0 ∨ 1 ≤ i) with rfl | hi1
        · rw [hn3, iter_t_zero a (n-2), ← Nat.sub_one_add_one_eq_of_pos hn, iter_t_zero a (n-1)]
        · have h1 : t^[n-2] (fun j => t a (j+1) - 1) (i-1) + 1 = t^[n-1] a i := by
            have e := hcomm (n-2) (i-1) (by omega)
            rwa [← hn3, Nat.sub_one_add_one_eq_of_pos hi1] at e
          have h2 : t^[n-1] (fun j => t a (j+1) - 1) (i-1) + 1 = t^[n] a i := by
            have e := hcomm (n-1) (i-1) (by omega)
            rwa [Nat.sub_one_add_one_eq_of_pos hn, Nat.sub_one_add_one_eq_of_pos hi1] at e
          have h3 : t^[n-2] (fun j => t a (j+1) - 1) (i-1)
              = t^[n-1] (fun j => t a (j+1) - 1) (i-1) := by
            have e := IHb (i-1) (by omega)
            rwa [Nat.sub_succ'] at e
          omega
      · -- Case 2: `a₁ = 0`.
        have ha10 : a 1 = 0 := by omega
        by_cases hall : ∀ i ≤ n, a i = 0
        · -- All terms are zero; the sequence is already stable after one step.
          have hz : ∀ i' < n + 1, a i' = 0 := (hall · <| Nat.le_of_succ_le_succ ·)
          have hz' := iter_eq_zero hz
          rw [hn3, hz' (n-2) i (by omega), ← Nat.sub_one_add_one_eq_of_pos hn, hz' (n-1) i (by omega)]
        · push Not at hall
          obtain ⟨k0, hk0n, hk0⟩ := hall
          -- Let `k` be the first index with `aₖ ≠ 0`; then `2 ≤ k`.
          obtain ⟨k, hkn, hknz, hkmin⟩ :
              ∃ k, k ≤ n ∧ a k ≠ 0 ∧ ∀ m < k, m ≤ n → a m = 0 := by
            have hex : ∃ i', i' ≤ n ∧ a i' ≠ 0 := ⟨k0, hk0n, hk0⟩
            refine ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2,
              fun m hm hmn => ?_⟩
            by_contra hne
            exact Nat.find_min hex hm ⟨hmn, hne⟩
          have h0 : a 0 = 0 := by have h := ha 0 (by omega); omega
          have hk2 : 2 ≤ k := by
            rcases (by omega : k = 0 ∨ k = 1 ∨ 2 ≤ k) with rfl | rfl | h'
            · exact absurd h0 hknz
            · exact absurd ha10 hknz
            · exact h'
          have hz : ∀ i' < k, a i' = 0 := fun i' hi' => hkmin i' hi' (by omega)
          have hz' : ∀ m, ∀ i' < k, t^[m+1] a i' = 0 := iter_eq_zero hz
          -- `t a i ≥ 1` for all `i ≥ k`.
          have hP2b : ∀ i', k ≤ i' → i' ≤ n → 1 ≤ t a i' := by
            intro i' hik hin
            by_cases hai : a i' = 0
            · have hki : k < i' := by
                by_contra hc
                push Not at hc
                have hkk : i' = k := by omega
                rw [hkk] at hai
                exact absurd hai hknz
              exact one_le_t_of hki (by rw [hai]; exact hknz)
            · exact one_le_t_of (j := 0) (by omega) (by rw [h0]; omega)
          -- `t^[m+2] a i ≥ k` for all `i ≥ k`.
          have hP2c : ∀ i', k ≤ i' → i' ≤ n → ∀ m, k ≤ t^[m+2] a i' := by
            intro i' hik hin m
            apply iter_ge_two_of_le (m := m+2) (hm := by omega)
            show k ≤ t (t a) i'
            rw [t_def]
            have sub : Finset.range k ⊆ (Finset.range i').filter (fun j => t a j ≠ t a i') := by
              intro j hj
              rw [Finset.mem_range] at hj
              rw [Finset.mem_filter, Finset.mem_range]
              refine ⟨lt_of_lt_of_le hj hik, ?_⟩
              have e1 : t a j = 0 := hz' 0 j hj
              have e2 : 1 ≤ t a i' := hP2b i' hik hin
              rw [e1]
              omega
            rw [← Finset.card_range k]
            exact Finset.card_le_card sub
          by_cases hkeq : n = k
          · -- Sub-case `k = n`: only `aₙ ≠ 0`; then `t a = t^[2] a` on `{0, …, n}`.
            subst hkeq
            have hstep : ∀ i' ≤ n, t a i' = t^[2] a i' := by
              intro i' hi'
              rcases hi'.eq_or_lt with rfl | hi2
              · have e1 : t a i' = i' := by
                  rw [t_def]
                  have hf : (Finset.range i').filter (fun j => a j ≠ a i') = Finset.range i' := by
                    apply Finset.filter_true_of_mem
                    intro j hj
                    rw [Finset.mem_range] at hj
                    have e3 : a j = 0 := hz j hj
                    rw [e3]
                    exact fun hh => hknz hh.symm
                  rw [hf, Finset.card_range]
                have e2 : t^[2] a i' = i' := by
                  show t (t a) i' = i'
                  rw [t_def]
                  have hf : (Finset.range i').filter (fun j => t a j ≠ t a i')
                      = Finset.range i' := by
                    apply Finset.filter_true_of_mem
                    intro j hj
                    rw [Finset.mem_range] at hj
                    have e3 : t a j = 0 := hz' 0 j hj
                    rw [e3, e1]
                    omega
                  rw [hf, Finset.card_range]
                rw [e1, e2]
              · have e1 : t a i' = 0 := hz' 0 i' hi2
                have e2 : t^[2] a i' = 0 := hz' 1 i' hi2
                rw [e1, e2]
            have e1 : t^[n-1] a i = t^[n-2] (t a) i := by
              rw [hn3, Function.iterate_add_apply, Function.iterate_one]
            rw [e1, ← Nat.sub_add_cancel hn2, Function.iterate_add_apply]
            exact iter_congr (hstep · <| ·.trans hi) (n-2) i le_rfl
          · -- Sub-case `k < n`: shift by `k` and apply the induction hypothesis.
            have hklt : k < n := by omega
            have hcomm : ∀ m, ∀ j, j + k ≤ n →
                t^[m] (fun j => t^[2] a (j+k) - k) j + k = t^[m+2] a (j+k) :=
              comm2 (by omega) hz' hP2c
            have hcvalid : ∀ j ≤ n - k, (fun j => t^[2] a (j+k) - k) j ≤ j := by
              intro j hj
              show t^[2] a (j+k) - k ≤ j
              have h : t^[2] a (j+k) ≤ j + k := iter_t_le a 1 (j+k)
              omega
            have IHc : ∀ j ≤ n - k, t^[n-k-1] (fun j => t^[2] a (j+k) - k) j
                = t^[n-k] (fun j => t^[2] a (j+k) - k) j :=
              IH (n-k) (by omega) (by omega) _ hcvalid
            -- The whole sequence is stable after `n - k + 1 ≤ n - 1` steps.
            have hstab : ∀ i' ≤ n, t^[n-k+1] a i' = t^[n-k+1+1] a i' := by
              intro i' hi'
              by_cases hik : i' < k
              · rw [hz' (n-k) i' hik, hz' (n-k+1) i' hik]
              · have hik2 : k ≤ i' := by omega
                have h1 : t^[n-k-1] (fun j => t^[2] a (j+k) - k) (i'-k) + k
                    = t^[n-k+1] a i' := by
                  have e := hcomm (n-k-1) (i'-k) (by rwa [Nat.sub_add_cancel hik2])
                  rwa [← Nat.sub_add_comm (by omega), Nat.add_succ_sub_one, Nat.sub_add_cancel hik2] at e
                have h2 : t^[n-k] (fun j => t^[2] a (j+k) - k) (i'-k) + k
                    = t^[n-k+1+1] a i' := by
                  have e := hcomm (n-k) (i'-k) (by omega)
                  rwa [Nat.add_succ, Nat.sub_add_cancel hik2] at e
                have h3 : t^[n-k-1] (fun j => t^[2] a (j+k) - k) (i'-k)
                    = t^[n-k] (fun j => t^[2] a (j+k) - k) (i'-k) := IHc (i'-k) (by omega)
                omega
            have hpers : t^[n-k+1+(k-2)] a i = t^[n-k+1+(k-2)+1] a i :=
              iter_stable_add a hstab (k-2) i hi
            rwa [Nat.add_right_comm, Nat.sub_add_sub_cancel hkn hk2, ← hn3, Nat.sub_one_add_one_eq_of_pos hn] at hpers

snip end

/-- ## USA Mathematical Olympiad 2003, Problem 3 -/
problem usa2003_p3 (n : ℕ) (hn : 0 < n) (a : ℕ → ℕ) (ha : ∀ i ≤ n, a i ≤ i) :
    ∃ k, k < n ∧ ∀ i ≤ n, t^[k] a i = t^[k+1] a i := by
  refine ⟨n - 1, by omega, fun i hi => ?_⟩
  rw [Nat.sub_one_add_one_eq_of_pos hn]
  exact main_aux n hn a ha i hi

end Usa2003P3
