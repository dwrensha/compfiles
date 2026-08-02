/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.Data.Set.Card
public import Mathlib.Order.CompletePartialOrder
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics] }

/-!
# USA Mathematical Olympiad 1990, Problem 4

How many positive integers can be written in base n so that
(1) the integer has no two digits the same, and
(2) each digit after the first differs by one from an earlier digit?
For example, in base 3, the possible numbers are 1, 2, 10, 12, 21, 102, 120, 210.
-/

namespace Usa1990P4

/-- Condition (2) of the problem, phrased for the list of base-`n` digits of a
number as produced by `Nat.digits` (least significant digit first, so the
"first" digit of the number is the last entry of the list): every digit except
the most significant one differs by one from some more significant digit. -/
def DiffByOne (l : List ℕ) : Prop :=
  ∀ i, ∀ (_ : i + 1 < l.length), ∃ j, i < j ∧ j < l.length ∧ ∀ (_ : j < l.length),
    (l[i] + 1 = l[j] ∨ l[j] + 1 = l[i])

snip begin

/-- `IV a b l` holds when `l` is a list of natural numbers whose set of entries
is exactly the interval `[a, b]`, built by starting from a single digit and
repeatedly prepending a new minimum or a new maximum. These are essentially the
valid digit lists of the problem (up to the leading-digit condition). -/
inductive IV : ℕ → ℕ → List ℕ → Prop
  | single (d : ℕ) : IV d d [d]
  | consLo {a b : ℕ} {l : List ℕ} (h : IV (a + 1) b l) : IV a b (a :: l)
  | consHi {a b : ℕ} {l : List ℕ} (h : IV a (b - 1) l) (hhi : 0 < b) :
      IV a b (b :: l)

namespace IV

theorem ne_nil {a b : ℕ} {l : List ℕ} (h : IV a b l) : l ≠ [] := by
  cases h <;> exact List.cons_ne_nil _ _

theorem lo_le_hi {a b : ℕ} {l : List ℕ} (h : IV a b l) : a ≤ b := by
  induction h with
  | single d => exact Nat.le_refl d
  | consLo h ih => omega
  | consHi h hhi ih => omega

theorem mem_iff {a b : ℕ} {l : List ℕ} (h : IV a b l) (d : ℕ) :
    d ∈ l ↔ a ≤ d ∧ d ≤ b := by
  induction h with
  | single d₀ =>
      rw [List.mem_singleton]
      constructor
      · intro h; subst h; exact ⟨Nat.le_refl _, Nat.le_refl _⟩
      · rintro ⟨h1, h2⟩; exact Nat.le_antisymm h2 h1
  | consLo h ih =>
      have h1 := lo_le_hi h
      rw [List.mem_cons, ih]; omega
  | consHi h hhi ih =>
      have h1 := lo_le_hi h
      rw [List.mem_cons, ih]; omega

theorem mem_lo {a b : ℕ} {l : List ℕ} (h : IV a b l) : a ∈ l :=
  (mem_iff h a).mpr ⟨Nat.le_refl a, lo_le_hi h⟩

theorem mem_hi {a b : ℕ} {l : List ℕ} (h : IV a b l) : b ∈ l :=
  (mem_iff h b).mpr ⟨lo_le_hi h, Nat.le_refl b⟩

theorem nodup {a b : ℕ} {l : List ℕ} (h : IV a b l) : l.Nodup := by
  induction h with
  | single d => simp
  | consLo h ih =>
      refine List.nodup_cons.mpr ⟨?_, ih⟩
      intro hmem
      have h1 := (mem_iff h _).mp hmem
      omega
  | consHi h hhi ih =>
      refine List.nodup_cons.mpr ⟨?_, ih⟩
      intro hmem
      have h1 := (mem_iff h _).mp hmem
      omega

theorem length_eq {a b : ℕ} {l : List ℕ} (h : IV a b l) :
    l.length = b + 1 - a := by
  induction h with
  | single d => show (1 : ℕ) = d + 1 - d; omega
  | consLo h ih =>
      have h1 := lo_le_hi h
      rw [List.length_cons, ih]; omega
  | consHi h hhi ih =>
      have h1 := lo_le_hi h
      rw [List.length_cons, ih]; omega

/-- Inversion principle for `IV` on a cons list. -/
theorem cons_iff {a b d : ℕ} {l : List ℕ} :
    IV a b (d :: l) ↔
      (d = a ∧ IV (a + 1) b l) ∨ (d = b ∧ 0 < b ∧ IV a (b - 1) l) ∨
        (a = d ∧ b = d ∧ l = []) := by
  constructor
  · intro h
    cases h with
    | single d₀ => exact Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)
    | consLo h => exact Or.inl ⟨rfl, h⟩
    | consHi h hhi => exact Or.inr (Or.inl ⟨rfl, hhi, h⟩)
  · intro h
    rcases h with ⟨rfl, h⟩ | ⟨rfl, hhi, h⟩ | ⟨rfl, rfl, rfl⟩
    · exact consLo h
    · exact consHi h hhi
    · exact single _

/-- `IV` lists satisfy condition (2) of the problem. -/
theorem diffByOne {a b : ℕ} {l : List ℕ} (h : IV a b l) : DiffByOne l := by
  induction h with
  | single d =>
      intro i b
      have h1 : ([d]).length = 1 := rfl
      omega
  | consLo h ih =>
      rename_i a' b' l'
      intro i b
      rcases i with _ | i'
      · obtain ⟨j', hj'1, hj'2⟩ := List.mem_iff_getElem.mp (mem_lo h)
        refine ⟨j' + 1, Nat.zero_lt_succ j', by rw [List.length_cons]; omega, fun _ ↦ ?_⟩
        left
        rw [List.getElem_cons_zero, List.getElem_cons_succ]
        exact hj'2.symm
      · have b' : i' + 1 < l'.length := by
          rw [List.length_cons] at b; omega
        obtain ⟨j', hjj, hj'b, hclose⟩ := ih i' b'
        refine ⟨j' + 1, by omega, by rw [List.length_cons]; omega, fun _ ↦ ?_⟩
        rw [List.getElem_cons_succ, List.getElem_cons_succ]
        exact hclose hj'b
  | consHi h hhi ih =>
      rename_i a' b' l'
      intro i b
      rcases i with _ | i'
      · obtain ⟨j', hj'1, hj'2⟩ := List.mem_iff_getElem.mp (mem_hi h)
        refine ⟨j' + 1, Nat.zero_lt_succ j', by rw [List.length_cons]; omega, fun _ ↦ ?_⟩
        right
        rw [List.getElem_cons_zero, List.getElem_cons_succ, hj'2]
        omega
      · have b' : i' + 1 < l'.length := by
          rw [List.length_cons] at b; omega
        obtain ⟨j', hjj, hj'b, hclose⟩ := ih i' b'
        refine ⟨j' + 1, by omega, by rw [List.length_cons]; omega, fun _ ↦ ?_⟩
        rw [List.getElem_cons_succ, List.getElem_cons_succ]
        exact hclose hj'b

/-- Lists with distinct entries satisfying condition (2) are exactly the
`IV` lists. -/
theorem of_diffByOne {l : List ℕ} (hne : l ≠ []) (hn : l.Nodup) (hd : DiffByOne l) :
    ∃ a b, IV a b l := by
  induction l with
  | nil => exact absurd rfl hne
  | cons d l' ih =>
      rcases l' with _ | ⟨d₂, l''⟩
      · exact ⟨d, d, single d⟩
      · have hn' : (d₂ :: l'').Nodup := (List.nodup_cons.mp hn).2
        have hd' : DiffByOne (d₂ :: l'') := by
          intro i b
          obtain ⟨j, hj1, hj2, hclose⟩ := hd (i + 1) (by rw [List.length_cons]; omega)
          obtain ⟨j'', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
          rw [Nat.succ_eq_add_one] at hj1 hj2 hclose
          rw [List.length_cons] at hj2
          refine ⟨j'', by omega, by omega, fun _ ↦ ?_⟩
          have hc := hclose (by rw [List.length_cons]; omega : j'' + 1 < (d :: d₂ :: l'').length)
          rwa [List.getElem_cons_succ, List.getElem_cons_succ] at hc
        obtain ⟨a, b, hIV⟩ := ih (List.cons_ne_nil d₂ l'') hn' hd'
        obtain ⟨j, hj1, hj2, hclose⟩ := hd 0 (by simp only [List.length_cons]; omega)
        obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
        rw [Nat.succ_eq_add_one] at hj1 hj2 hclose
        have hc := hclose hj2
        rw [List.getElem_cons_zero, List.getElem_cons_succ] at hc
        rw [List.length_cons] at hj2
        have hcmem : (d₂ :: l'')[j'] ∈ (d₂ :: l'') :=
          List.getElem_mem (by omega : j' < (d₂ :: l'').length)
        have hcb := (mem_iff hIV _).mp hcmem
        have hdn : d ∉ (d₂ :: l'') := (List.nodup_cons.mp hn).1
        have hdnot : ¬ (a ≤ d ∧ d ≤ b) := fun hbad ↦ hdn ((mem_iff hIV d).mpr hbad)
        rcases hc with h | h
        · refine ⟨d, b, ?_⟩
          have h1 : d + 1 = a := by omega
          exact consLo (h1.symm ▸ hIV)
        · refine ⟨a, d, ?_⟩
          have h2 : d - 1 = b := by omega
          have h3 : 0 < d := by omega
          exact consHi (h2.symm ▸ hIV) h3

/-- The interval endpoints of an `IV` list are uniquely determined. -/
theorem unique_indices {a b a' b' : ℕ} {l : List ℕ} (h : IV a b l)
    (h' : IV a' b' l) : a = a' ∧ b = b' := by
  have a1 := (mem_iff h' a).mp (mem_lo h)
  have a2 := (mem_iff h' b).mp (mem_hi h)
  have a3 := (mem_iff h a').mp (mem_lo h')
  have a4 := (mem_iff h b').mp (mem_hi h')
  omega

end IV

/-- Digit lists satisfying the conditions of the problem in base `n`:
distinct digits, condition (2), all digits less than `n`, and a nonzero
leading digit (the last entry of the list, since digits are stored
least-significant first). -/
def ValidLists (n : ℕ) : Set (List ℕ) :=
  {l | l.Nodup ∧ DiffByOne l ∧ (∀ d ∈ l, d < n) ∧ l ≠ [] ∧
    ∀ h : l ≠ [], l.getLast h ≠ 0}

/-- Valid digit lists whose digits form exactly the interval `[a, b]`. -/
def W (a b : ℕ) : Set (List ℕ) := {l | IV a b l ∧ ∀ h : l ≠ [], l.getLast h ≠ 0}

/-- Lists whose digits form exactly the interval `[a, b]`. -/
def IVSet (a b : ℕ) : Set (List ℕ) := {l | IV a b l}

/-- The decreasing list `b, b-1, ..., 1, 0`. -/
def descend : ℕ → List ℕ
  | 0 => [0]
  | b + 1 => (b + 1) :: descend b

theorem descend_ne_nil : ∀ b, descend b ≠ [] := by
  intro b
  rcases b with _ | k
  · exact List.cons_ne_nil 0 []
  · exact List.cons_ne_nil (k + 1) (descend k)

theorem descend_eq (b : ℕ) (h : 0 < b) : descend b = b :: descend (b - 1) := by
  rcases b with _ | k
  · omega
  · rfl

theorem IV_descend : ∀ b, IV 0 b (descend b) := by
  intro b
  induction b with
  | zero => exact IV.single 0
  | succ k ih => exact IV.consHi ih (Nat.zero_lt_succ k)

theorem getLast?_descend : ∀ b, (descend b).getLast? = some 0 := by
  intro b
  induction b with
  | zero => rfl
  | succ k ih =>
      show ((k + 1) :: descend k).getLast? = some 0
      rw [List.getLast?_cons_of_ne_nil (descend_ne_nil k)]
      exact ih

theorem getLast_descend (b : ℕ) (h : descend b ≠ []) : (descend b).getLast h = 0 := by
  have h2 := getLast?_descend b
  rw [List.getLast?_eq_some_getLast h] at h2
  exact Option.some.inj h2

/-- Among `IV 0 b` lists, only the decreasing list ends in `0`. -/
theorem eq_descend {a b : ℕ} {l : List ℕ} (h : IV a b l)
    (hgl : ∀ hh : l ≠ [], l.getLast hh = 0) : a = 0 ∧ l = descend b := by
  induction h with
  | single d =>
      have h1 : d = 0 := by
        have h2 := hgl (List.cons_ne_nil d [])
        rwa [List.getLast_singleton] at h2
      subst h1
      exact ⟨rfl, rfl⟩
  | consLo h ih =>
      rename_i a' b' l'
      have hgl' : ∀ hh : l' ≠ [], l'.getLast hh = 0 := fun hh ↦ by
        have h2 := hgl (List.cons_ne_nil a' l')
        rwa [List.getLast_cons hh] at h2
      obtain ⟨h1, -⟩ := ih hgl'
      exact absurd h1 (Nat.succ_ne_zero a')
  | consHi h hhi ih =>
      rename_i a' b' l'
      have hgl' : ∀ hh : l' ≠ [], l'.getLast hh = 0 := fun hh ↦ by
        have h2 := hgl (List.cons_ne_nil b' l')
        rwa [List.getLast_cons hh] at h2
      obtain ⟨h1, h2⟩ := ih hgl'
      refine ⟨h1, ?_⟩
      rw [h2, descend_eq b' hhi]

/-- The number of `IV` lists over the interval `[a, a + k]` is `2 ^ k`. -/
theorem finite_and_ncard_IVSet : ∀ (k a : ℕ),
    (IVSet a (a + k)).Finite ∧ (IVSet a (a + k)).ncard = 2 ^ k := by
  intro k
  induction k with
  | zero =>
      intro a
      have hset : IVSet a (a + 0) = {[a]} := by
        ext l
        simp only [IVSet, Set.mem_setOf_eq, Set.mem_singleton_iff]
        constructor
        · intro hl
          have h1 := IV.lo_le_hi hl
          have h2 := IV.length_eq hl
          have h3 : l.length = 1 := by omega
          obtain ⟨d, rfl⟩ := List.length_eq_one_iff.mp h3
          rcases IV.cons_iff.mp hl with ⟨h4, h5⟩ | ⟨h4, h6, h5⟩ | ⟨h4, -, -⟩
          · exact (IV.ne_nil h5 rfl).elim
          · exact (IV.ne_nil h5 rfl).elim
          · rw [← h4]
        · intro h
          rw [h]
          exact IV.single a
      rw [hset]
      exact ⟨Set.finite_singleton _, Set.ncard_singleton _⟩
  | succ k ih =>
      intro a
      obtain ⟨fin1, card1⟩ := ih (a + 1)
      obtain ⟨fin2, card2⟩ := ih a
      have hset : IVSet a (a + (k + 1)) =
          (fun l ↦ a :: l) '' IVSet (a + 1) (a + 1 + k) ∪
          (fun l ↦ (a + (k + 1)) :: l) '' IVSet a (a + k) := by
        ext l
        simp only [IVSet, Set.mem_setOf_eq, Set.mem_union, Set.mem_image]
        constructor
        · intro hl
          rcases l with _ | ⟨d, l'⟩
          · exact absurd (IV.ne_nil hl rfl) (by simp)
          · rcases IV.cons_iff.mp hl with ⟨h1, h2⟩ | ⟨h1, h6, h2⟩ | ⟨h3, h4, -⟩
            · subst h1
              rw [show d + (k + 1) = d + 1 + k by omega] at h2
              exact Or.inl ⟨l', h2, rfl⟩
            · subst h1
              exact Or.inr ⟨l', h2, rfl⟩
            · omega
        · rintro (⟨l', h1, rfl⟩ | ⟨l', h1, rfl⟩)
          · rw [show a + 1 + k = a + (k + 1) by omega] at h1
            exact IV.consLo h1
          · exact IV.consHi h1 (by omega)
      rw [hset]
      refine ⟨Set.Finite.union (fin1.image _) (fin2.image _), ?_⟩
      rw [Set.ncard_union_eq _ (fin1.image _) (fin2.image _),
        Set.ncard_image_of_injective _ List.cons_injective,
        Set.ncard_image_of_injective _ List.cons_injective, card1, card2]
      · rw [pow_succ]; ring
      · rw [Set.disjoint_left]
        rintro _ ⟨l₁, -, rfl⟩ ⟨l₂, -, h₂⟩
        have h3 : a + (k + 1) = a := (List.cons.inj h₂).1
        omega

/-- Geometric series with ratio `2`. -/
theorem geom2 : ∀ m, ∑ k ∈ Finset.range m, 2 ^ k = 2 ^ m - 1 := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      have h4 : 0 < 2 ^ m := by positivity
      omega

theorem two_pow_ge : ∀ n, 2 * n + 2 ≤ 2 ^ (n + 1) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ]
      omega

theorem outer_sum : ∀ n, ∑ b ∈ Finset.range n, (2 ^ (b + 1) - 2) =
    2 ^ (n + 1) - 2 * n - 2 := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      have h2 : 2 * n + 2 ≤ 2 ^ (n + 1) := two_pow_ge n
      rw [show 2 ^ (n + 1 + 1) = 2 * 2 ^ (n + 1) by rw [pow_succ]; ring]
      omega

/-- Finite disjoint unions of sets of lists have the sum of the cardinalities. -/
theorem ncard_biUnion {α : Type*} (s : Finset ℕ) (f : ℕ → Set α)
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (f i) (f j))
    (hf : ∀ i ∈ s, (f i).Finite) :
    (⋃ i ∈ s, f i).ncard = ∑ i ∈ s, (f i).ncard := by
  induction s using Finset.induction with
  | empty =>
      have hunion : (⋃ i ∈ (∅ : Finset ℕ), f i) = ∅ := by
        ext x
        simp
      rw [hunion, Finset.sum_empty]
      exact Set.ncard_empty _
  | @insert i s his ih =>
      have hmem : i ∈ insert i s := Finset.mem_insert_self i s
      have hfin : (⋃ x ∈ s, f x).Finite :=
        Set.Finite.biUnion (Finset.finite_toSet s)
          (fun j hj ↦ hf j (Finset.mem_insert_of_mem hj))
      have hunion : (⋃ x ∈ insert i s, f x) = f i ∪ ⋃ x ∈ s, f x := by
        ext x
        constructor
        · intro hx
          rw [Set.mem_iUnion₂] at hx
          obtain ⟨j, hj, hx⟩ := hx
          rw [Finset.mem_insert] at hj
          rcases hj with rfl | hj
          · exact Or.inl hx
          · exact Or.inr (Set.mem_iUnion₂.mpr ⟨j, hj, hx⟩)
        · intro hx
          rcases hx with hx | hx
          · exact Set.mem_iUnion₂.mpr ⟨i, hmem, hx⟩
          · rw [Set.mem_iUnion₂] at hx
            obtain ⟨j, hj, hx⟩ := hx
            exact Set.mem_iUnion₂.mpr ⟨j, Finset.mem_insert_of_mem hj, hx⟩
      rw [Finset.sum_insert his, hunion,
        Set.ncard_union_eq _ (hf i hmem) hfin]
      · rw [ih (fun j hj j' hj' ↦ hd j (Finset.mem_insert_of_mem hj) j'
            (Finset.mem_insert_of_mem hj'))
          (fun j hj ↦ hf j (Finset.mem_insert_of_mem hj))]
      · rw [Set.disjoint_left]
        intro x hxi hx
        rw [Set.mem_iUnion₂] at hx
        obtain ⟨j, hj, hxj⟩ := hx
        exact Set.disjoint_left.mp
          (hd i hmem j (Finset.mem_insert_of_mem hj) (fun h ↦ his (h.symm ▸ hj))) hxi hxj

theorem W_finite (a b : ℕ) : (W a b).Finite := by
  by_cases h : a ≤ b
  · obtain ⟨fin, -⟩ := finite_and_ncard_IVSet (b - a) a
    rw [show a + (b - a) = b by omega] at fin
    exact fin.subset (fun l hl ↦ hl.1)
  · have hset : W a b = ∅ := by
      ext l
      simp only [W, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨hIV, -⟩
      have h1 := IV.lo_le_hi hIV
      omega
    rw [hset]
    exact Set.finite_empty

theorem disjoint_W {a b a' b' : ℕ} (hne : (a, b) ≠ (a', b')) :
    Disjoint (W a b) (W a' b') := by
  rw [Set.disjoint_left]
  rintro l ⟨h1, -⟩ ⟨h2, -⟩
  obtain ⟨rfl, rfl⟩ := IV.unique_indices h1 h2
  exact hne rfl

/-- The number of valid digit lists with digit interval `[a, b]`. -/
theorem ncard_W {a b : ℕ} (hle : a ≤ b) :
    (W a b).ncard = 2 ^ (b - a) - (if a = 0 then 1 else 0) := by
  obtain ⟨fin, card⟩ := finite_and_ncard_IVSet (b - a) a
  rw [show a + (b - a) = b by omega] at fin card
  by_cases h0 : a = 0
  · subst h0
    have hset : W 0 b = IVSet 0 b \ {descend b} := by
      ext l
      simp only [W, IVSet, Set.mem_setOf_eq, Set.mem_sdiff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨hIV, hgl⟩
        refine ⟨hIV, fun hle ↦ ?_⟩
        subst hle
        exact hgl (descend_ne_nil b) (getLast_descend b _)
      · rintro ⟨hIV, hne⟩
        exact ⟨hIV, fun _ hgl ↦ hne (eq_descend hIV (fun _ ↦ hgl)).2⟩
    rw [hset, Set.ncard_sdiff_singleton_of_mem (s := IVSet 0 b) (IV_descend b), card]
    simp
  · have hset : W a b = IVSet a b := by
      ext l
      simp only [W, IVSet, Set.mem_setOf_eq]
      constructor
      · exact fun hl ↦ hl.1
      · intro hIV
        refine ⟨hIV, fun hh ↦ ?_⟩
        have hmem := List.getLast_mem hh
        have hb := (IV.mem_iff hIV _).mp hmem
        omega
    rw [hset, card]
    simp [h0]

/-- The valid digit lists are the disjoint union of the `W a b` over
`0 ≤ a ≤ b < n`. -/
theorem validLists_eq_biUnion (n : ℕ) :
    ValidLists n = ⋃ b ∈ Finset.range n, ⋃ a ∈ Finset.range (b + 1), W a b := by
  ext l
  constructor
  · rintro ⟨hn1, hn2, hlt, hne, hgl⟩
    obtain ⟨a, b, hIV⟩ := IV.of_diffByOne hne hn1 hn2
    have hhi : b < n := hlt b (IV.mem_hi hIV)
    have hlo : a < b + 1 := Nat.lt_succ_of_le (IV.lo_le_hi hIV)
    exact Set.mem_iUnion₂.mpr ⟨b, Finset.mem_range.mpr hhi,
      Set.mem_iUnion₂.mpr ⟨a, Finset.mem_range.mpr hlo, ⟨hIV, hgl⟩⟩⟩
  · intro hl
    rw [Set.mem_iUnion₂] at hl
    obtain ⟨b, hhi, hl⟩ := hl
    rw [Set.mem_iUnion₂] at hl
    obtain ⟨a, hlo, hIV, hgl⟩ := hl
    rw [Finset.mem_range] at hhi
    refine ⟨IV.nodup hIV, IV.diffByOne hIV, fun d hd ↦ ?_, IV.ne_nil hIV, hgl⟩
    have hd' := (IV.mem_iff hIV d).mp hd
    omega

theorem disjoint_inner {i j : ℕ} (hij : i ≠ j) :
    Disjoint (⋃ a ∈ Finset.range (i + 1), W a i)
      (⋃ a ∈ Finset.range (j + 1), W a j) := by
  rw [Set.disjoint_left]
  rintro l hli hlj
  rw [Set.mem_iUnion₂] at hli hlj
  obtain ⟨a₁, -, h1⟩ := hli
  obtain ⟨a₂, -, h2⟩ := hlj
  obtain ⟨-, hii⟩ := IV.unique_indices h1.1 h2.1
  exact hij hii

theorem inner_finite (b : ℕ) : (⋃ a ∈ Finset.range (b + 1), W a b).Finite :=
  Set.Finite.biUnion (Finset.finite_toSet (Finset.range (b + 1)))
    (fun a _ ↦ W_finite a b)

/-- The number of valid digit lists whose largest digit is exactly `b`. -/
theorem ncard_inner (b : ℕ) :
    (⋃ a ∈ Finset.range (b + 1), W a b).ncard = 2 ^ (b + 1) - 2 := by
  rw [ncard_biUnion (Finset.range (b + 1)) (fun a ↦ W a b)
    (fun a₁ _ a₂ _ hne ↦ disjoint_W (by simpa using hne))
    (fun a _ ↦ W_finite a b)]
  rw [Finset.sum_range_succ']
  have h0 : (W 0 b).ncard = 2 ^ b - 1 := by
    rw [ncard_W (Nat.zero_le b)]
    simp
  have hs : ∑ a ∈ Finset.range b, (W (a + 1) b).ncard = 2 ^ b - 1 := by
    have h3 : ∀ a ∈ Finset.range b, (W (a + 1) b).ncard = 2 ^ (b - 1 - a) := by
      intro a hlo
      rw [Finset.mem_range] at hlo
      rw [ncard_W (show a + 1 ≤ b by omega), if_neg (by simp), tsub_zero]
      congr 1
      omega
    rw [Finset.sum_congr rfl h3]
    exact (Finset.sum_range_reflect (fun k ↦ 2 ^ k) b).trans (geom2 b)
  rw [h0, hs]
  have h4 : 0 < 2 ^ b := by positivity
  rw [pow_succ]
  omega

/-- The total number of valid digit lists in base `n`. -/
theorem ncard_validLists (n : ℕ) :
    (ValidLists n).ncard = 2 ^ (n + 1) - 2 * n - 2 := by
  rw [validLists_eq_biUnion n,
    ncard_biUnion (Finset.range n) _
      (fun i _ j _ hij ↦ disjoint_inner hij) (fun i _ ↦ inner_finite i)]
  exact (Finset.sum_congr rfl (fun b _ ↦ ncard_inner b)).trans (outer_sum n)

/-- Positive integers satisfying the conditions of the problem correspond to
valid digit lists via `Nat.digits`. -/
theorem ncard_numbers_eq (n : ℕ) (hn : 1 < n) :
    Set.ncard {m : ℕ | 0 < m ∧ (Nat.digits n m).Nodup ∧ DiffByOne (Nat.digits n m)} =
      (ValidLists n).ncard := by
  refine Set.ncard_congr (fun m _ ↦ Nat.digits n m) ?_ ?_ ?_
  · intro m hm
    obtain ⟨hm0, hn1, hn2⟩ := hm
    have hm0' : m ≠ 0 := by omega
    have hne : Nat.digits n m ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hm0'
    exact ⟨hn1, hn2, fun d hd ↦ Nat.digits_lt_base hn hd, hne,
      fun _ ↦ Nat.getLast_digit_ne_zero n hm0'⟩
  · intro m₁ m₂ _ _ h
    exact Nat.digits.injective n h
  · intro l hl
    obtain ⟨hn1, hn2, hlt, hne, hgl⟩ := hl
    have hdig : Nat.digits n (Nat.ofDigits n l) = l := Nat.digits_ofDigits n hn l hlt hgl
    have hpos : 0 < Nat.ofDigits n l := by
      rcases Nat.eq_zero_or_pos (Nat.ofDigits n l) with h | h
      · rw [h, Nat.digits_eq_nil_iff_eq_zero.mpr rfl] at hdig
        exact absurd hdig.symm hne
      · exact h
    exact ⟨Nat.ofDigits n l, ⟨hpos, hdig.symm ▸ hn1, hdig.symm ▸ hn2⟩, hdig⟩

snip end

determine answer (n : ℕ) : ℕ := 2 ^ (n + 1) - 2 * n - 2

problem usa1990_p4 (n : ℕ) (hn : 2 ≤ n) :
    Set.ncard {m : ℕ | 0 < m ∧ (Nat.digits n m).Nodup ∧ DiffByOne (Nat.digits n m)} =
      answer n := by
  rw [ncard_numbers_eq n (by omega), ncard_validLists n]

end Usa1990P4
