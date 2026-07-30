/-
Copyright (c) 2026 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw, Kimi K3
-/

module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.Data.Set.Card
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics] }

open scoped Nat

/-!
# USA Mathematical Olympiad 2019, Problem 4

Let n be a nonnegative integer. Determine the number of ways to choose
sets Sᵢⱼ ⊆ {1, 2, ..., 2n}, for all 0 ≤ i ≤ n and 0 ≤ j ≤ n (not
necessarily distinct), such that

  • |Sᵢⱼ| = i + j, and
  • Sᵢⱼ ⊆ Sₖₗ if 0 ≤ i ≤ k ≤ n and 0 ≤ j ≤ l ≤ n.
-/

namespace Usa2019P4

snip begin

/-- The grid cells indexing the sets `Sᵢⱼ`. -/
abbrev Cell (n : ℕ) := Fin (n + 1) × Fin (n + 1)

/-- The cardinality required at cell `(i, j)`. -/
def target {n : ℕ} (c : Cell n) : ℕ := c.1.val + c.2.val

/-- Partial configurations on a set `D` of cells: the cardinality and
monotonicity conditions hold on `D`, and the value is `∅` off `D`
(the latter condition keeps the ambient function type finite). -/
def Fillings (n : ℕ) (D : Set (Cell n)) : Set (Cell n → Finset (Fin (2 * n))) :=
  {S | (∀ c ∈ D, (S c).card = target c) ∧
       (∀ a ∈ D, ∀ b ∈ D, a ≤ b → S a ⊆ S b) ∧
       (∀ c ∉ D, S c = ∅)}

/-- The cells of column `0` in rows `≤ j`. -/
def colZero (n j : ℕ) : Set (Cell n) := {c | c.1.val = 0 ∧ c.2.val ≤ j}

/-- The cells of row `n` in columns `1..i`. -/
def topRow (n i : ℕ) : Set (Cell n) := {c | 1 ≤ c.1.val ∧ c.1.val ≤ i ∧ c.2.val = n}

/-- The interior cells (rows `< n`) in columns `1..i`. -/
def intCols (n i : ℕ) : Set (Cell n) := {c | 1 ≤ c.1.val ∧ c.1.val ≤ i ∧ c.2.val < n}

/-- The interior cells of column `k` in rows `n - r .. n - 1`. -/
def colPart (n k r : ℕ) : Set (Cell n) := {c | c.1.val = k ∧ n - r ≤ c.2.val ∧ c.2.val < n}

/-- Cell equality in terms of coordinate values. -/
lemma cell_ext {n : ℕ} {c : Cell n} {a b : ℕ} {ha : a < n + 1} {hb : b < n + 1} :
    c = (⟨a, ha⟩, ⟨b, hb⟩) ↔ c.1.val = a ∧ c.2.val = b :=
  ⟨fun h ↦ by rw [h]; exact ⟨rfl, rfl⟩,
   fun ⟨h1, h2⟩ ↦ Prod.ext_iff.mpr ⟨Fin.ext_iff.mpr h1, Fin.ext_iff.mpr h2⟩⟩

/-- The only filling of the empty set of cells. -/
lemma fillings_empty (n : ℕ) : Fillings n (∅ : Set (Cell n)) = {fun _ ↦ ∅} := by
  ext S
  simp [Fillings, funext_iff]

/-- Restricting a filling of `insert s D` to a filling of `D`
by resetting the value at `s` to `∅`. -/
lemma restrict_mem {n : ℕ} {D : Set (Cell n)} {s : Cell n} (hs : s ∉ D)
    {S : Cell n → Finset (Fin (2 * n))} (hS : S ∈ Fillings n (insert s D)) :
    Function.update S s ∅ ∈ Fillings n D := by
  obtain ⟨hcard, hmono, hjunk⟩ := hS
  refine ⟨?_, ?_, ?_⟩
  · intro c hc
    rw [Function.update_of_ne (ne_of_mem_of_not_mem hc hs)]
    exact hcard c (Set.mem_insert_of_mem s hc)
  · intro a ha b hb hab
    rw [Function.update_of_ne (ne_of_mem_of_not_mem ha hs),
      Function.update_of_ne (ne_of_mem_of_not_mem hb hs)]
    exact hmono a (Set.mem_insert_of_mem s ha) b (Set.mem_insert_of_mem s hb) hab
  · intro c hc
    by_cases hcs : c = s
    · rw [hcs]; exact Function.update_self s ∅ S
    · rw [Function.update_of_ne hcs]
      exact hjunk c fun h ↦ hc (Set.mem_of_mem_insert_of_ne h hcs)

/-- Extending a filling of `D` by an admissible value `X` at `s`. -/
lemma extend_mem {n : ℕ} {D : Set (Cell n)} {s : Cell n} (hs : s ∉ D)
    {A C : (Cell n → Finset (Fin (2 * n))) → Finset (Fin (2 * n))}
    (hlo : ∀ f ∈ Fillings n D, ∀ d ∈ D, d ≤ s → f d ⊆ A f)
    (hhi : ∀ f ∈ Fillings n D, ∀ d ∈ D, s ≤ d → C f ⊆ f d)
    {f : Cell n → Finset (Fin (2 * n))} (hf : f ∈ Fillings n D)
    {X : Finset (Fin (2 * n))} (hXA : A f ⊆ X) (hXC : X ⊆ C f)
    (hXt : X.card = target s) :
    Function.update f s X ∈ Fillings n (insert s D) := by
  refine ⟨?_, ?_, ?_⟩
  · intro c hc
    rcases Set.mem_insert_iff.mp hc with rfl | hcD
    · rw [Function.update_self]; exact hXt
    · rw [Function.update_of_ne (ne_of_mem_of_not_mem hcD hs)]; exact hf.1 c hcD
  · intro a ha b hb hab
    rcases Set.mem_insert_iff.mp ha with rfl | haD <;>
    rcases Set.mem_insert_iff.mp hb with rfl | hbD
    · exact Finset.Subset.refl _
    · rw [Function.update_self, Function.update_of_ne (ne_of_mem_of_not_mem hbD hs)]
      exact Finset.Subset.trans hXC (hhi f hf b hbD hab)
    · rw [Function.update_self, Function.update_of_ne (ne_of_mem_of_not_mem haD hs)]
      exact Finset.Subset.trans (hlo f hf a haD hab) hXA
    · rw [Function.update_of_ne (ne_of_mem_of_not_mem haD hs),
        Function.update_of_ne (ne_of_mem_of_not_mem hbD hs)]
      exact hf.2.1 a haD b hbD hab
  · intro c hc
    have hcs : c ≠ s := by
      intro h
      rw [h] at hc
      exact hc (Set.mem_insert s D)
    rw [Function.update_of_ne hcs]
    exact hf.2.2 c fun hD ↦ hc (Set.mem_insert_of_mem s hD)

/-- The sets between `A` and `C` with cardinality `t` are counted
by a binomial coefficient. -/
lemma card_between {α : Type*} [DecidableEq α] {A C : Finset α} (hAC : A ⊆ C)
    {t : ℕ} (hAt : A.card ≤ t) :
    Nat.card {X : Finset α // A ⊆ X ∧ X ⊆ C ∧ X.card = t} =
      (C.card - A.card).choose (t - A.card) := by
  have e : {X : Finset α // A ⊆ X ∧ X ⊆ C ∧ X.card = t} ≃
      ↥(Finset.powersetCard (t - A.card) (C \ A)) :=
    ⟨fun X ↦ ⟨X.1 \ A, Finset.mem_powersetCard.mpr
        ⟨Finset.sdiff_subset_sdiff X.2.2.1 (Finset.Subset.refl A), by
          rw [Finset.card_sdiff_of_subset X.2.1, X.2.2.2]⟩⟩,
     fun Y ↦ ⟨Y.1 ∪ A, by
       have hY := Finset.mem_powersetCard.mp Y.2
       refine ⟨Finset.subset_union_right, ?_, ?_⟩
       · exact Finset.union_subset (Finset.Subset.trans hY.1 Finset.sdiff_subset) hAC
       · rw [Finset.card_union_of_disjoint
           (Finset.disjoint_of_subset_left hY.1 Finset.sdiff_disjoint), hY.2,
           Nat.sub_add_cancel hAt]⟩,
     fun X ↦ Subtype.ext (Finset.sdiff_union_of_subset X.2.1),
     fun Y ↦ Subtype.ext (Finset.union_sdiff_cancel_right
       (Finset.disjoint_of_subset_left
         (Finset.mem_powersetCard.mp Y.2).1 Finset.sdiff_disjoint))⟩
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe,
    Finset.card_powersetCard, Finset.card_sdiff_of_subset hAC]

/-- The possible values of a filling at a fresh cell `s`,
given the values `A f` and `C f` forced by the neighbors of `s`. -/
abbrev Fiber {n : ℕ} {D : Set (Cell n)}
    (A C : (Cell n → Finset (Fin (2 * n))) → Finset (Fin (2 * n))) (s : Cell n)
    (f : ↥(Fillings n D)) : Type :=
  {X : Finset (Fin (2 * n)) // A f.1 ⊆ X ∧ X ⊆ C f.1 ∧ X.card = target s}

/-- Adding one cell to the domain multiplies the number of fillings
by a binomial coefficient. -/
lemma ncard_fillings_insert {n : ℕ} {D : Set (Cell n)} {s : Cell n} (hs : s ∉ D)
    {A C : (Cell n → Finset (Fin (2 * n))) → Finset (Fin (2 * n))}
    (hlo : ∀ f ∈ Fillings n D, ∀ d ∈ D, d ≤ s → f d ⊆ A f)
    (hhi : ∀ f ∈ Fillings n D, ∀ d ∈ D, s ≤ d → C f ⊆ f d)
    (hAs : ∀ g ∈ Fillings n (insert s D), A (Function.update g s ∅) ⊆ g s)
    (hsC : ∀ g ∈ Fillings n (insert s D), g s ⊆ C (Function.update g s ∅))
    (hAC : ∀ f ∈ Fillings n D, A f ⊆ C f)
    {a₀ c₀ : ℕ}
    (hAcard : ∀ f ∈ Fillings n D, (A f).card = a₀)
    (hCcard : ∀ f ∈ Fillings n D, (C f).card = c₀)
    (hAt : ∀ f ∈ Fillings n D, (A f).card ≤ target s) :
    (Fillings n (insert s D)).ncard =
      (c₀ - a₀).choose (target s - a₀) * (Fillings n D).ncard := by
  classical
  have hfib : ∀ f : ↥(Fillings n D),
      Nat.card (Fiber A C s f) = (c₀ - a₀).choose (target s - a₀) := by
    intro f
    have h1 := card_between (hAC f.1 f.2) (hAt f.1 f.2)
    rw [hAcard f.1 f.2, hCcard f.1 f.2] at h1
    exact h1
  let toSigma : ↥(Fillings n (insert s D)) → (Σ f : ↥(Fillings n D), Fiber A C s f) :=
    fun g ↦ ⟨⟨Function.update g.1 s ∅, restrict_mem hs g.2⟩,
      g.1 s, hAs g.1 g.2, hsC g.1 g.2, g.2.1 s (Set.mem_insert s D)⟩
  let fromSigma : (Σ f : ↥(Fillings n D), Fiber A C s f) → ↥(Fillings n (insert s D)) :=
    fun p ↦ ⟨Function.update p.1.1 s p.2.1,
      extend_mem hs hlo hhi p.1.2 p.2.2.1 p.2.2.2.1 p.2.2.2.2⟩
  have inj : Function.Injective toSigma := by
    intro g₁ g₂ heq
    have h1 : Function.update g₁.1 s ∅ = Function.update g₂.1 s ∅ :=
      congrArg (fun p : (Σ f : ↥(Fillings n D), Fiber A C s f) ↦ p.1.1) heq
    have h2 : g₁.1 s = g₂.1 s :=
      congrArg (fun p : (Σ f : ↥(Fillings n D), Fiber A C s f) ↦ p.2.1) heq
    apply Subtype.ext
    funext c
    by_cases hcs : c = s
    · rw [hcs]; exact h2
    · have e1 := congrFun h1 c
      rw [Function.update_of_ne hcs, Function.update_of_ne hcs] at e1
      exact e1
  have hgen : ∀ (g : Cell n → Finset (Fin (2 * n))) (Y : Finset (Fin (2 * n))),
      Function.update (Function.update g s Y) s ∅ = Function.update g s ∅ := by
    intro g Y
    funext c
    by_cases hcs : c = s
    · rw [hcs, Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hcs, Function.update_of_ne hcs, Function.update_of_ne hcs]
  have inj2 : Function.Injective fromSigma := by
    intro p₁ p₂ heq
    obtain ⟨⟨f₁, hf₁⟩, X₁, hXA₁, hXC₁, hXt₁⟩ := p₁
    obtain ⟨⟨f₂, hf₂⟩, X₂, hXA₂, hXC₂, hXt₂⟩ := p₂
    have eX : X₁ = X₂ := by
      have e := congrArg (fun g : ↥(Fillings n (insert s D)) ↦ g.1 s) heq
      change Function.update f₁ s X₁ s = Function.update f₂ s X₂ s at e
      rw [Function.update_self, Function.update_self] at e
      exact e
    have ef : f₁ = f₂ := by
      have e := congrArg (fun g : ↥(Fillings n (insert s D)) ↦ Function.update g.1 s ∅) heq
      change Function.update (Function.update f₁ s X₁) s ∅ =
        Function.update (Function.update f₂ s X₂) s ∅ at e
      rw [hgen, hgen] at e
      funext c
      by_cases hcs : c = s
      · rw [hcs, hf₁.2.2 s hs, hf₂.2.2 s hs]
      · have ec := congrFun e c
        rw [Function.update_of_ne hcs, Function.update_of_ne hcs] at ec
        exact ec
    subst ef
    subst eX
    rfl
  have hcard : Nat.card ↥(Fillings n (insert s D)) =
      Nat.card (Σ f : ↥(Fillings n D), Fiber A C s f) := by
    apply le_antisymm
    · rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
      exact Fintype.card_le_of_injective toSigma inj
    · rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
      exact Fintype.card_le_of_injective fromSigma inj2
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
  calc Nat.card ↥(Fillings n (insert s D))
      = Nat.card (Σ f : ↥(Fillings n D), Fiber A C s f) := hcard
    _ = ∑ f : ↥(Fillings n D), Nat.card (Fiber A C s f) := by
        rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
        exact Finset.sum_congr rfl fun f _ ↦ (Nat.card_eq_fintype_card).symm
    _ = ∑ f : ↥(Fillings n D), (c₀ - a₀).choose (target s - a₀) :=
        Finset.sum_congr rfl fun f _ ↦ hfib f
    _ = (Fillings n D).ncard * (c₀ - a₀).choose (target s - a₀) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id,
          ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
    _ = (c₀ - a₀).choose (target s - a₀) * (Fillings n D).ncard := mul_comm _ _

/-- Counting the fillings of the leftmost column: after `j` steps there are
`∏ i ∈ range j, (2 * n - i)` fillings. -/
lemma stageA (n : ℕ) : ∀ j, j ≤ n →
    (Fillings n (colZero n j)).ncard = ∏ i ∈ Finset.range j, (2 * n - i) := by
  intro j
  induction j with
  | zero =>
    intro _
    have h0n : (0 : ℕ) < n + 1 := Nat.zero_lt_succ n
    have h0 : colZero n 0 = insert (⟨0, h0n⟩, ⟨0, h0n⟩) (∅ : Set (Cell n)) := by
      ext c
      simp only [colZero, Set.mem_insert_iff, Set.mem_empty_iff_false, Set.mem_setOf_eq,
        cell_ext, or_false]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, Nat.eq_zero_of_le_zero h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, Nat.le_of_eq h2⟩
    rw [h0, ncard_fillings_insert (A := fun _ ↦ ∅) (C := fun _ ↦ Finset.univ)
      (Set.notMem_empty _)
      (by intro f hf d hd hds; exact (Set.notMem_empty d hd).elim)
      (by intro f hf d hd hds; exact (Set.notMem_empty d hd).elim)
      (by intro g hg; exact Finset.empty_subset _)
      (by intro g hg; exact Finset.subset_univ _)
      (by intro f hf; exact Finset.empty_subset _)
      (by intro f hf; rw [Finset.card_empty])
      (by intro f hf; rw [Finset.card_univ, Fintype.card_fin])
      (by intro f hf; rw [Finset.card_empty]; exact Nat.zero_le _),
      fillings_empty, Set.ncard_singleton, Finset.prod_range_zero]
    simp [target]
  | succ j ih =>
    intro hj
    have hj' : j ≤ n := Nat.le_of_succ_le hj
    have hjn : j < n + 1 := by omega
    have hjn1 : j + 1 < n + 1 := by omega
    have h0n : (0 : ℕ) < n + 1 := Nat.zero_lt_succ n
    have hid : colZero n (j + 1) =
        insert (⟨0, h0n⟩, ⟨j + 1, hjn1⟩) (colZero n j) := by
      ext c
      simp only [colZero, Set.mem_insert_iff, Set.mem_setOf_eq, cell_ext]
      constructor <;> intro h <;> omega
    have hs : (⟨0, h0n⟩, ⟨j + 1, hjn1⟩) ∉ colZero n j := by
      simp only [colZero, Set.mem_setOf_eq]
      omega
    have ha₀ : (⟨0, h0n⟩, ⟨j, hjn⟩) ∈ colZero n j := ⟨rfl, le_refl _⟩
    have hcount : (2 * n - target (⟨0, h0n⟩, ⟨j, hjn⟩)).choose
        (target (⟨0, h0n⟩, ⟨j + 1, hjn1⟩) - target (⟨0, h0n⟩, ⟨j, hjn⟩)) = 2 * n - j := by
      have h1 : target (⟨0, h0n⟩, ⟨j, hjn⟩) = j := Nat.zero_add j
      have h2 : target (⟨0, h0n⟩, ⟨j + 1, hjn1⟩) - target (⟨0, h0n⟩, ⟨j, hjn⟩) = 1 := by
        show 0 + (j + 1) - (0 + j) = 1
        omega
      rw [h1] at h2
      rw [h1, h2, Nat.choose_one_right]
    rw [hid, ncard_fillings_insert hs
      (A := fun f ↦ f (⟨0, h0n⟩, ⟨j, hjn⟩)) (C := fun _ ↦ Finset.univ)
      (by
        intro f hf d hd _
        apply hf.2.1 d hd _ ha₀
        simp only [colZero, Set.mem_setOf_eq] at hd
        simp only [Prod.le_def, Fin.le_def]
        exact ⟨by omega, by omega⟩)
      (by
        intro f hf d hd hds
        simp only [colZero, Set.mem_setOf_eq] at hd
        simp only [Prod.le_def, Fin.le_def] at hds
        omega)
      (by
        intro g hg
        rw [Function.update_of_ne (by
          intro hcon
          simp only [cell_ext] at hcon
          omega)]
        exact hg.2.1 _ (Set.mem_insert_of_mem _ ha₀) _ (Set.mem_insert _ _)
          (by simp only [Prod.le_def, Fin.le_def]; omega))
      (by intro g hg; exact Finset.subset_univ _)
      (by intro f hf; exact Finset.subset_univ _)
      (by intro f hf; exact hf.1 _ ha₀)
      (by intro f hf; rw [Finset.card_univ, Fintype.card_fin])
      (by
        intro f hf
        rw [hf.1 _ ha₀]
        show 0 + j ≤ 0 + (j + 1)
        omega),
      hcount, ih hj', Finset.prod_range_succ]
    ring

/-- Counting the fillings of the left column together with the top row. -/
lemma stageB (n : ℕ) : ∀ i, i ≤ n →
    (Fillings n (colZero n n ∪ topRow n i)).ncard =
      (∏ j ∈ Finset.range i, (n - j)) * ∏ j ∈ Finset.range n, (2 * n - j) := by
  intro i
  induction i with
  | zero =>
    intro _
    have h0 : topRow n 0 = (∅ : Set (Cell n)) := by
      ext c
      simp only [topRow, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      omega
    rw [h0, Set.union_empty, Finset.prod_range_zero, one_mul, stageA n n (le_refl n)]
  | succ i ih =>
    intro hi
    have hi' : i ≤ n := Nat.le_of_succ_le hi
    have hin : i < n + 1 := by omega
    have hin1 : i + 1 < n + 1 := by omega
    have hnn : n < n + 1 := Nat.lt_succ_self n
    have hid : colZero n n ∪ topRow n (i + 1) =
        insert (⟨i + 1, hin1⟩, ⟨n, hnn⟩) (colZero n n ∪ topRow n i) := by
      ext c
      simp only [colZero, topRow, Set.mem_insert_iff, Set.mem_union, Set.mem_setOf_eq,
        cell_ext]
      constructor <;> intro h <;> omega
    have hs : (⟨i + 1, hin1⟩, ⟨n, hnn⟩) ∉ colZero n n ∪ topRow n i := by
      simp only [colZero, topRow, Set.mem_union, Set.mem_setOf_eq]
      omega
    have ha₀ : (⟨i, hin⟩, ⟨n, hnn⟩) ∈ colZero n n ∪ topRow n i := by
      by_cases hi0 : i = 0
      · subst hi0; exact Or.inl ⟨rfl, le_refl _⟩
      · exact Or.inr ⟨by show (1 : ℕ) ≤ i; omega, le_refl i, rfl⟩
    have hcount : (2 * n - target (⟨i, hin⟩, ⟨n, hnn⟩)).choose
        (target (⟨i + 1, hin1⟩, ⟨n, hnn⟩) - target (⟨i, hin⟩, ⟨n, hnn⟩)) = n - i := by
      have h1 : 2 * n - target (⟨i, hin⟩, ⟨n, hnn⟩) = n - i := by
        show 2 * n - (i + n) = n - i
        omega
      have h2 : target (⟨i + 1, hin1⟩, ⟨n, hnn⟩) - target (⟨i, hin⟩, ⟨n, hnn⟩) = 1 := by
        show i + 1 + n - (i + n) = 1
        omega
      rw [h1, h2, Nat.choose_one_right]
    rw [hid, ncard_fillings_insert hs
      (A := fun f ↦ f (⟨i, hin⟩, ⟨n, hnn⟩)) (C := fun _ ↦ Finset.univ)
      (by
        intro f hf d hd _
        apply hf.2.1 d hd _ ha₀
        simp only [colZero, topRow, Set.mem_union, Set.mem_setOf_eq] at hd
        simp only [Prod.le_def, Fin.le_def]
        show d.1.val ≤ i ∧ d.2.val ≤ n
        omega)
      (by
        intro f hf d hd hds
        simp only [colZero, topRow, Set.mem_union, Set.mem_setOf_eq] at hd
        simp only [Prod.le_def, Fin.le_def] at hds
        omega)
      (by
        intro g hg
        rw [Function.update_of_ne (by
          intro hcon
          simp only [cell_ext] at hcon
          omega)]
        exact hg.2.1 _ (Set.mem_insert_of_mem _ ha₀) _ (Set.mem_insert _ _)
          (by simp only [Prod.le_def, Fin.le_def]; omega))
      (by intro g hg; exact Finset.subset_univ _)
      (by intro f hf; exact Finset.subset_univ _)
      (by intro f hf; exact hf.1 _ ha₀)
      (by intro f hf; rw [Finset.card_univ, Fintype.card_fin])
      (by
        intro f hf
        rw [hf.1 _ ha₀]
        show i + n ≤ i + 1 + n
        omega),
      hcount, ih hi', Finset.prod_range_succ]
    ring

/-- Filling the interior column `k + 1` from the top down: each of the
`n` cells doubles the number of fillings. -/
lemma stageC_inner (n : ℕ) : ∀ r, r ≤ n → ∀ k, k < n →
    (Fillings n (colZero n n ∪ topRow n n ∪ intCols n k ∪ colPart n (k + 1) r)).ncard =
      2 ^ r * (Fillings n (colZero n n ∪ topRow n n ∪ intCols n k)).ncard := by
  intro r
  induction r with
  | zero =>
    intro _ k hk
    have h0 : colPart n (k + 1) 0 = (∅ : Set (Cell n)) := by
      ext c
      simp only [colPart, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      omega
    rw [h0, Set.union_empty, pow_zero, one_mul]
  | succ r ih =>
    intro hr k hk
    have hr' : r ≤ n := Nat.le_of_succ_le hr
    have hkn : k < n + 1 := by omega
    have hkn1 : k + 1 < n + 1 := by omega
    have hnr : n - r < n + 1 := by omega
    have hnr1 : n - r - 1 < n + 1 := by omega
    have hid : colZero n n ∪ topRow n n ∪ intCols n k ∪ colPart n (k + 1) (r + 1) =
        insert (⟨k + 1, hkn1⟩, ⟨n - r - 1, hnr1⟩)
          (colZero n n ∪ topRow n n ∪ intCols n k ∪ colPart n (k + 1) r) := by
      ext c
      simp only [colZero, topRow, intCols, colPart, Set.mem_insert_iff, Set.mem_union,
        Set.mem_setOf_eq, cell_ext]
      constructor <;> intro h <;> omega
    have hs : (⟨k + 1, hkn1⟩, ⟨n - r - 1, hnr1⟩) ∉
        colZero n n ∪ topRow n n ∪ intCols n k ∪ colPart n (k + 1) r := by
      simp only [colZero, topRow, intCols, colPart, Set.mem_union, Set.mem_setOf_eq]
      omega
    have ha₀ : (⟨k, hkn⟩, ⟨n - r - 1, hnr1⟩) ∈
        colZero n n ∪ topRow n n ∪ intCols n k ∪ colPart n (k + 1) r := by
      by_cases hk0 : k = 0
      · subst hk0
        exact Or.inl (Or.inl (Or.inl ⟨rfl, by show n - r - 1 ≤ n; omega⟩))
      · exact Or.inl (Or.inr ⟨by show (1 : ℕ) ≤ k; omega, le_refl k,
          by show n - r - 1 < n; omega⟩)
    have hc₀ : (⟨k + 1, hkn1⟩, ⟨n - r, hnr⟩) ∈
        colZero n n ∪ topRow n n ∪ intCols n k ∪ colPart n (k + 1) r := by
      by_cases hr0 : r = 0
      · subst hr0
        exact Or.inl (Or.inl (Or.inr ⟨by show (1 : ℕ) ≤ k + 1; omega,
          by show k + 1 ≤ n; omega, by show n - 0 = n; omega⟩))
      · exact Or.inr ⟨rfl, le_refl _, by show n - r < n; omega⟩
    have hcount : (target (⟨k + 1, hkn1⟩, ⟨n - r, hnr⟩) -
        target (⟨k, hkn⟩, ⟨n - r - 1, hnr1⟩)).choose
        (target (⟨k + 1, hkn1⟩, ⟨n - r - 1, hnr1⟩) -
          target (⟨k, hkn⟩, ⟨n - r - 1, hnr1⟩)) = 2 := by
      have h1 : target (⟨k + 1, hkn1⟩, ⟨n - r, hnr⟩) -
          target (⟨k, hkn⟩, ⟨n - r - 1, hnr1⟩) = 2 := by
        show k + 1 + (n - r) - (k + (n - r - 1)) = 2
        omega
      have h2 : target (⟨k + 1, hkn1⟩, ⟨n - r - 1, hnr1⟩) -
          target (⟨k, hkn⟩, ⟨n - r - 1, hnr1⟩) = 1 := by
        show k + 1 + (n - r - 1) - (k + (n - r - 1)) = 1
        omega
      rw [h1, h2, Nat.choose_one_right]
    rw [hid, ncard_fillings_insert hs
      (A := fun f ↦ f (⟨k, hkn⟩, ⟨n - r - 1, hnr1⟩))
      (C := fun f ↦ f (⟨k + 1, hkn1⟩, ⟨n - r, hnr⟩))
      (by
        intro f hf d hd hds
        apply hf.2.1 d hd _ ha₀
        simp only [colZero, topRow, intCols, colPart, Set.mem_union, Set.mem_setOf_eq] at hd
        simp only [Prod.le_def, Fin.le_def] at hds ⊢
        omega)
      (by
        intro f hf d hd hds
        apply hf.2.1 _ hc₀ d hd
        simp only [colZero, topRow, intCols, colPart, Set.mem_union, Set.mem_setOf_eq] at hd
        simp only [Prod.le_def, Fin.le_def] at hds ⊢
        omega)
      (by
        intro g hg
        rw [Function.update_of_ne (by
          intro hcon
          simp only [cell_ext] at hcon
          omega)]
        exact hg.2.1 _ (Set.mem_insert_of_mem _ ha₀) _ (Set.mem_insert _ _)
          (by simp only [Prod.le_def, Fin.le_def]; omega))
      (by
        intro g hg
        rw [Function.update_of_ne (by
          intro hcon
          simp only [cell_ext] at hcon
          omega)]
        exact hg.2.1 _ (Set.mem_insert _ _) _ (Set.mem_insert_of_mem _ hc₀)
          (by simp only [Prod.le_def, Fin.le_def]; omega))
      (by
        intro f hf
        exact hf.2.1 _ ha₀ _ hc₀ (by simp only [Prod.le_def, Fin.le_def]; omega))
      (by intro f hf; exact hf.1 _ ha₀)
      (by intro f hf; exact hf.1 _ hc₀)
      (by
        intro f hf
        rw [hf.1 _ ha₀]
        show k + (n - r - 1) ≤ k + 1 + (n - r - 1)
        omega),
      hcount, ih hr' k hk, pow_succ]
    ring

/-- Counting the fillings of everything except the right column
of the grid. -/
lemma stageC (n : ℕ) : ∀ k, k ≤ n →
    (Fillings n (colZero n n ∪ topRow n n ∪ intCols n k)).ncard =
      2 ^ (n * k) * ((∏ i ∈ Finset.range n, (n - i)) * ∏ j ∈ Finset.range n, (2 * n - j)) := by
  intro k
  induction k with
  | zero =>
    intro _
    have h0 : intCols n 0 = (∅ : Set (Cell n)) := by
      ext c
      simp only [intCols, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      omega
    rw [h0, Set.union_empty, stageB n n (le_refl n)]
    simp
  | succ k ih =>
    intro hk
    have hk' : k < n := by omega
    have hid : colZero n n ∪ topRow n n ∪ intCols n (k + 1) =
        colZero n n ∪ topRow n n ∪ intCols n k ∪ colPart n (k + 1) n := by
      ext c
      simp only [colZero, topRow, intCols, colPart, Set.mem_union, Set.mem_setOf_eq]
      constructor <;> intro h <;> omega
    rw [hid, stageC_inner n n (le_refl n) k hk', ih (Nat.le_of_succ_le hk),
      show n * (k + 1) = n * k + n from by ring, pow_add]
    ring

theorem prod_range_self_sub (n : ℕ) :
    ∏ i ∈ Finset.range n, (n - i) = n ! := by
  rw [← Finset.prod_range_add_one_eq_factorial,
    ← Finset.prod_range_reflect (fun j => j + 1) n]
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  omega

theorem prod_range_two_mul_sub_mul (n : ℕ) :
    (∏ j ∈ Finset.range n, (2 * n - j)) * (∏ i ∈ Finset.range n, (n - i)) = (2 * n) ! := by
  have h2 : ∏ j ∈ Finset.range n, (2 * n - j) = ∏ x ∈ Finset.range n, (n + x + 1) := by
    rw [← Finset.prod_range_reflect (fun j => 2 * n - j) n]
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    omega
  have h3 : (∏ x ∈ Finset.range n, (n + x + 1)) * (∏ x ∈ Finset.range n, (x + 1))
      = (2 * n)! := by
    have h := Finset.prod_range_add (fun i => i + 1) n n
    rw [← Nat.two_mul n, Finset.prod_range_add_one_eq_factorial] at h
    rw [h]
    exact Nat.mul_comm _ _
  rw [prod_range_self_sub n, h2, ← Finset.prod_range_add_one_eq_factorial n, h3]

/-- The full count: the number of valid configurations is
`(2 * n)! * 2 ^ (n ^ 2)`. -/
lemma main_count (n : ℕ) : (Fillings n Set.univ).ncard = (2 * n)! * 2 ^ (n ^ 2) := by
  have huniv : (Set.univ : Set (Cell n)) = colZero n n ∪ topRow n n ∪ intCols n n := by
    ext c
    simp only [Set.mem_univ, colZero, topRow, intCols, Set.mem_union, Set.mem_setOf_eq,
      true_iff]
    have h1 := c.1.isLt
    have h2 := c.2.isLt
    omega
  rw [huniv, stageC n n (le_refl n),
    mul_comm (∏ i ∈ Finset.range n, (n - i)) (∏ j ∈ Finset.range n, (2 * n - j)),
    prod_range_two_mul_sub_mul, show n * n = n ^ 2 from (pow_two n).symm, mul_comm]

snip end

determine answer (n : ℕ) : ℕ := (2 * n)! * 2 ^ (n ^ 2)

problem usa2019_p4 (n : ℕ) :
    Nat.card {S : Fin (n + 1) → Fin (n + 1) → Finset (Fin (2 * n)) //
      (∀ i j, (S i j).card = i.val + j.val) ∧
      (∀ i k j l, i ≤ k → j ≤ l → S i j ⊆ S k l)} = answer n := by
  classical
  have e : {S : Fin (n + 1) → Fin (n + 1) → Finset (Fin (2 * n)) //
      (∀ i j, (S i j).card = i.val + j.val) ∧
      (∀ i k j l, i ≤ k → j ≤ l → S i j ⊆ S k l)} ≃ ↥(Fillings n Set.univ) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact fun S ↦ ⟨fun c ↦ S.1 c.1 c.2, by
        refine ⟨?_, ?_, ?_⟩
        · intro c _
          exact S.2.1 c.1 c.2
        · intro a _ b _ hab
          exact S.2.2 a.1 b.1 a.2 b.2 (Prod.le_def.mp hab).1 (Prod.le_def.mp hab).2
        · intro c hc
          exact absurd (Set.mem_univ c) hc⟩
    · exact fun S ↦ ⟨fun i j ↦ S.1 (i, j), by
        refine ⟨?_, ?_⟩
        · intro i j
          exact S.2.1 (i, j) (Set.mem_univ _)
        · intro i k j l hik hjl
          exact S.2.2.1 (i, j) (Set.mem_univ _) (k, l) (Set.mem_univ _)
            (Prod.le_def.mpr ⟨hik, hjl⟩)⟩
    · intro S
      apply Subtype.ext
      rfl
    · intro S
      apply Subtype.ext
      funext c
      change S.1 (c.1, c.2) = S.1 c
      rw [Prod.mk.eta]
  rw [Nat.card_congr e, Nat.card_coe_set_eq, main_count]

end Usa2019P4
