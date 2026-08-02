/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Tactic
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics] }

/-!
# USA Mathematical Olympiad 1981, Problem 2

What is the largest number of towns that can meet the following criteria?
Each pair is directly linked by just one of air, bus or train.
At least one pair is linked by air, at least one pair by bus and at least
one pair by train. No town has an air link, a bus link and a train link.
No three towns, A, B, C are such that the links between AB, AC and BC are
all air, all bus or all train.
-/

namespace Usa1981P2

/-- The three possible link types between two towns. -/
inductive Link | air | bus | train
  deriving DecidableEq, Fintype

/-- The set of link types that town `v` has to other towns. -/
abbrev colorsAt {n : ℕ} (f : Fin n → Fin n → Link) (v : Fin n) : Finset Link :=
  (Finset.univ.filter (· ≠ v)).image (f v ·)

/-- A link assignment on `n` towns satisfying all the criteria of the problem:
it is symmetric, all three link types are used, no town has all three link
types, and no three towns are pairwise linked by the same type. -/
abbrev Valid {n : ℕ} (f : Fin n → Fin n → Link) : Prop :=
  (∀ i j, f i j = f j i) ∧
  (∃ i j, i ≠ j ∧ f i j = .air) ∧
  (∃ i j, i ≠ j ∧ f i j = .bus) ∧
  (∃ i j, i ≠ j ∧ f i j = .train) ∧
  (∀ v, (colorsAt f v).card ≤ 2) ∧
  (∀ a b c, a ≠ b → b ≠ c → a ≠ c → ¬ (f a b = f a c ∧ f a b = f b c))

determine answer : ℕ := 4

snip begin

/-- If a town `u` is linked to three other towns by three pairwise distinct
link types, then `u` has at least three link types. -/
theorem three_le_card_colorsAt {n : ℕ} {f : Fin n → Fin n → Link} {u : Fin n}
    {p q r : Fin n} (hp : p ≠ u) (hq : q ≠ u) (hr : r ≠ u)
    {c₁ c₂ c₃ : Link} (h1 : f u p = c₁) (h2 : f u q = c₂) (h3 : f u r = c₃)
    (d12 : c₁ ≠ c₂) (d13 : c₁ ≠ c₃) (d23 : c₂ ≠ c₃) :
    3 ≤ (colorsAt f u).card := by
  have hsub : ({c₁, c₂, c₃} : Finset Link) ⊆ colorsAt f u := by
    intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl
    · exact Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ p, hp⟩, h1⟩
    · exact Finset.mem_image.mpr ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_univ q, hq⟩, h2⟩
    · exact Finset.mem_image.mpr ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ r, hr⟩, h3⟩
  have hcard : ({c₁, c₂, c₃} : Finset Link).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [d12, d13]),
      Finset.card_insert_of_notMem (by simp [d23]), Finset.card_singleton]
  exact hcard ▸ Finset.card_le_card hsub

/-- Key local fact: no town is linked to three other towns by the same link
type. (Among any three such towns, the links would have to avoid that type,
and then either one of the three towns has all three link types, or the
remaining links form a monochromatic triangle.) -/
theorem fiber_card_le_two {n : ℕ} {f : Fin n → Fin n → Link} (hf : Valid f)
    (v : Fin n) (c : Link) :
    (Finset.univ.filter fun w ↦ w ≠ v ∧ f v w = c).card ≤ 2 := by
  obtain ⟨hsymm, -, -, -, hmax, hmono⟩ := hf
  by_contra h
  rw [not_le] at h
  obtain ⟨w₁, w₂, w₃, hw₁, hw₂, hw₃, d12, d13, d23⟩ := Finset.two_lt_card_iff.mp h
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw₁ hw₂ hw₃
  -- The links among `w₁, w₂, w₃` cannot have type `c`, otherwise the link
  -- together with `v` would form a monochromatic triangle.
  have e12 : f w₁ w₂ ≠ c := fun e ↦
    hmono v w₁ w₂ (Ne.symm hw₁.1) d12 (Ne.symm hw₂.1)
      ⟨hw₁.2.trans hw₂.2.symm, hw₁.2.trans e.symm⟩
  have e13 : f w₁ w₃ ≠ c := fun e ↦
    hmono v w₁ w₃ (Ne.symm hw₁.1) d13 (Ne.symm hw₃.1)
      ⟨hw₁.2.trans hw₃.2.symm, hw₁.2.trans e.symm⟩
  have e23 : f w₂ w₃ ≠ c := fun e ↦
    hmono v w₂ w₃ (Ne.symm hw₂.1) d23 (Ne.symm hw₃.1)
      ⟨hw₂.2.trans hw₃.2.symm, hw₂.2.trans e.symm⟩
  by_cases hxy : f w₁ w₂ = f w₁ w₃
  · -- Then `f w₂ w₃` differs from both, so `w₂` has all three link types.
    have e23' : f w₂ w₃ ≠ f w₁ w₂ := fun e ↦
      hmono w₁ w₂ w₃ d12 d23 d13 ⟨hxy, e.symm⟩
    have hle := three_le_card_colorsAt (Ne.symm hw₂.1) d12 (Ne.symm d23)
      ((hsymm w₂ v).trans hw₂.2) (hsymm w₂ w₁) rfl
      (Ne.symm e12) (Ne.symm e23) (Ne.symm e23')
    have := hmax w₂
    omega
  · -- Then `w₁` has all three link types.
    have hle := three_le_card_colorsAt (Ne.symm hw₁.1) (Ne.symm d12) (Ne.symm d13)
      ((hsymm w₁ v).trans hw₁.2) rfl rfl
      (Ne.symm e12) (Ne.symm e13) hxy
    have := hmax w₁
    omega

/-- Every town is directly linked to at most four other towns:
at most two link types, at most two links of each type. -/
theorem card_neighbors_le_four {n : ℕ} {f : Fin n → Fin n → Link} (hf : Valid f)
    (v : Fin n) :
    (Finset.univ.filter (· ≠ v)).card ≤ 4 := by
  rw [Finset.card_eq_sum_card_image (f v ·) (Finset.univ.filter (· ≠ v))]
  have hfib : ∀ d ∈ (Finset.univ.filter (· ≠ v)).image (f v ·),
      ((Finset.univ.filter (· ≠ v)).filter fun w ↦ f v w = d).card ≤ 2 := by
    intro d _
    refine le_trans (Finset.card_le_card ?_) (fiber_card_le_two hf v d)
    intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    exact hw
  calc ∑ d ∈ (Finset.univ.filter (· ≠ v)).image (f v ·),
          ((Finset.univ.filter (· ≠ v)).filter fun w ↦ f v w = d).card
      ≤ ∑ _d ∈ (Finset.univ.filter (· ≠ v)).image (f v ·), 2 := Finset.sum_le_sum hfib
    _ = 2 * ((Finset.univ.filter (· ≠ v)).image (f v ·)).card := by
        rw [Finset.sum_const, smul_eq_mul, mul_comm]
    _ ≤ 2 * 2 := by
        gcongr
        exact hf.2.2.2.2.1 v
    _ = 4 := rfl

theorem card_filter_ne {n : ℕ} (v : Fin n) :
    (Finset.univ.filter (· ≠ v)).card = n - 1 := by
  rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ v),
    Finset.card_univ, Fintype.card_fin]

/-- The ten unordered pairs of towns of `Fin 5`, in a fixed order. -/
def pair : Fin 10 → Fin 5 × Fin 5 := fun k ↦
  match k.val with
  | 0 => (0, 1)
  | 1 => (0, 2)
  | 2 => (0, 3)
  | 3 => (0, 4)
  | 4 => (1, 2)
  | 5 => (1, 3)
  | 6 => (1, 4)
  | 7 => (2, 3)
  | 8 => (2, 4)
  | 9 => (3, 4)
  | _ => (0, 1)

/-- The position of the unordered pair `{i, j}` in the list `pair`. -/
def edgeIdx (i j : Fin 5) : Fin 10 :=
  ⟨(match i.val, j.val with
    | 0, 1 | 1, 0 => 0
    | 0, 2 | 2, 0 => 1
    | 0, 3 | 3, 0 => 2
    | 0, 4 | 4, 0 => 3
    | 1, 2 | 2, 1 => 4
    | 1, 3 | 3, 1 => 5
    | 1, 4 | 4, 1 => 6
    | 2, 3 | 3, 2 => 7
    | 2, 4 | 4, 2 => 8
    | 3, 4 | 4, 3 => 9
    | _, _ => 0) % 10, Nat.mod_lt _ (by decide)⟩

/-- A symmetric link assignment on five towns, reconstructed from its
restriction to the ten unordered pairs. -/
def mkColor (u : Fin 10 → Link) : Fin 5 → Fin 5 → Link :=
  fun i j ↦ if i = j then .air else u (edgeIdx i j)

theorem pair_edgeIdx :
    ∀ i j : Fin 5, i ≠ j → pair (edgeIdx i j) = (i, j) ∨ pair (edgeIdx i j) = (j, i) := by
  decide

theorem mkColor_eq {f : Fin 5 → Fin 5 → Link} (hsymm : ∀ i j, f i j = f j i)
    {i j : Fin 5} (hij : i ≠ j) :
    mkColor (fun k ↦ f (pair k).1 (pair k).2) i j = f i j := by
  simp only [mkColor, if_neg hij]
  rcases pair_edgeIdx i j hij with e | e
  · rw [e]
  · rw [e]
    exact hsymm j i

/-- Any valid assignment on five towns restricts to a valid assignment
reconstructed from the ten unordered pairs. -/
theorem valid_mkColor {f : Fin 5 → Fin 5 → Link} (hf : Valid f) :
    Valid (mkColor fun k ↦ f (pair k).1 (pair k).2) := by
  obtain ⟨hsymm, hair, hbus, htrain, hmax, hmono⟩ := hf
  have mc : ∀ {i j : Fin 5}, i ≠ j →
      mkColor (fun k ↦ f (pair k).1 (pair k).2) i j = f i j :=
    fun h ↦ mkColor_eq hsymm h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    by_cases hij : i = j
    · rw [hij]
    · rw [mc hij, mc (Ne.symm hij)]
      exact hsymm i j
  · obtain ⟨i, j, hij, h⟩ := hair
    exact ⟨i, j, hij, by rw [mc hij]; exact h⟩
  · obtain ⟨i, j, hij, h⟩ := hbus
    exact ⟨i, j, hij, by rw [mc hij]; exact h⟩
  · obtain ⟨i, j, hij, h⟩ := htrain
    exact ⟨i, j, hij, by rw [mc hij]; exact h⟩
  · intro v
    have heq : colorsAt (mkColor fun k ↦ f (pair k).1 (pair k).2) v = colorsAt f v :=
      Finset.image_congr fun w hw ↦ mc (Ne.symm (Finset.mem_filter.mp hw).2)
    rw [heq]
    exact hmax v
  · intro a b c hab hbc hac ⟨e1, e2⟩
    rw [mc hab, mc hac] at e1
    rw [mc hab, mc hbc] at e2
    exact hmono a b c hab hbc hac ⟨e1, e2⟩

/-- Boolean check: does a town whose four links have these types see all
three link types? (The `||` and `&&` chains are explicitly right-nested so
that `simp` normal forms match anonymous-constructor patterns.) -/
def seesAll3 (a b c d : Link) : Bool :=
  (a == .air || (b == .air || (c == .air || d == .air))) &&
    ((a == .bus || (b == .bus || (c == .bus || d == .bus))) &&
      (a == .train || (b == .train || (c == .train || d == .train))))

/-- Boolean check: is the triangle with these three link types
monochromatic? -/
def monoE (x y z : Link) : Bool := x == y && x == z

/-- Boolean check: is link type `x` used by the assignment `u`? -/
def usesC (u : Fin 10 → Link) (x : Link) : Bool :=
  u 0 == x || (u 1 == x || (u 2 == x || (u 3 == x || (u 4 == x ||
    (u 5 == x || (u 6 == x || (u 7 == x || (u 8 == x || u 9 == x))))))))

/-- A kernel-efficient Boolean version of `Valid (mkColor u)`. The ten
unordered pairs of `Fin 5` are hard-coded by their positions in `pair`: the
links at town `0` are `u 0, u 1, u 2, u 3`, at town `1` are `u 0, u 4, u 5,
u 6`, at town `2` are `u 1, u 4, u 7, u 8`, at town `3` are `u 2, u 5, u 7,
u 9`, and at town `4` are `u 3, u 6, u 8, u 9`; the ten triangles are listed
similarly. -/
def validB (u : Fin 10 → Link) : Bool :=
  !seesAll3 (u 0) (u 1) (u 2) (u 3) && (!seesAll3 (u 0) (u 4) (u 5) (u 6) &&
    (!seesAll3 (u 1) (u 4) (u 7) (u 8) && (!seesAll3 (u 2) (u 5) (u 7) (u 9) &&
    (!seesAll3 (u 3) (u 6) (u 8) (u 9) && (!monoE (u 0) (u 1) (u 4) &&
    (!monoE (u 0) (u 2) (u 5) && (!monoE (u 0) (u 3) (u 6) && (!monoE (u 1) (u 2) (u 7) &&
    (!monoE (u 1) (u 3) (u 8) && (!monoE (u 2) (u 3) (u 9) && (!monoE (u 4) (u 5) (u 7) &&
    (!monoE (u 4) (u 6) (u 8) && (!monoE (u 5) (u 6) (u 9) && (!monoE (u 7) (u 8) (u 9) &&
    (usesC u .air && (usesC u .bus && usesC u .train))))))))))))))))

/-- Bundle ten link types into a function `Fin 10 → Link`. -/
def mkU (c₀ c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ : Link) : Fin 10 → Link := fun k ↦
  match k.val with
  | 0 => c₀
  | 1 => c₁
  | 2 => c₂
  | 3 => c₃
  | 4 => c₄
  | 5 => c₅
  | 6 => c₆
  | 7 => c₇
  | 8 => c₈
  | 9 => c₉
  | _ => c₀

theorem edgeIdx_symm : ∀ i j : Fin 5, edgeIdx i j = edgeIdx j i := by
  decide

theorem mkColor_apply (u : Fin 10 → Link) {i j : Fin 5} (hij : i ≠ j) :
    mkColor u i j = u (edgeIdx i j) :=
  if_neg hij

theorem mkColor_symm (u : Fin 10 → Link) (i j : Fin 5) :
    mkColor u i j = mkColor u j i := by
  by_cases hij : i = j
  · rw [hij]
  · rw [mkColor_apply u hij, mkColor_apply u (Ne.symm hij), edgeIdx_symm i j]

/-- A town has at most two link types unless it has all three of them. -/
theorem card_le_two_iff {n : ℕ} {f : Fin n → Fin n → Link} {v : Fin n} :
    (colorsAt f v).card ≤ 2 ↔
      ¬((∃ w, w ≠ v ∧ f v w = .air) ∧ (∃ w, w ≠ v ∧ f v w = .bus) ∧
        (∃ w, w ≠ v ∧ f v w = .train)) := by
  have mem_iff : ∀ c : Link, c ∈ colorsAt f v ↔ ∃ w, w ≠ v ∧ f v w = c := by
    intro c
    constructor
    · intro h
      obtain ⟨w, hw, hwe⟩ := Finset.mem_image.mp h
      exact ⟨w, (Finset.mem_filter.mp hw).2, hwe⟩
    · intro ⟨w, hwv, hwe⟩
      exact Finset.mem_image.mpr ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ w, hwv⟩, hwe⟩
  constructor
  · intro hcard ⟨ha, hb, ht⟩
    obtain ⟨wa, hwa, ea⟩ := ha
    obtain ⟨wb, hwb, eb⟩ := hb
    obtain ⟨wt, hwt, et⟩ := ht
    have h3 := three_le_card_colorsAt hwa hwb hwt ea eb et
      (by decide) (by decide) (by decide)
    omega
  · intro h
    by_contra hc
    rw [not_le] at hc
    have hle : (colorsAt f v).card ≤ 3 := by
      calc (colorsAt f v).card ≤ Finset.univ.card :=
            Finset.card_le_card (Finset.subset_univ _)
        _ = 3 := by decide
    have heq3 : (colorsAt f v).card = 3 := by omega
    have huniv : colorsAt f v = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [heq3]
      decide
    have hmem : ∀ c : Link, c ∈ colorsAt f v := by
      intro c
      rw [huniv]
      exact Finset.mem_univ c
    exact h ⟨(mem_iff .air).mp (hmem .air), (mem_iff .bus).mp (hmem .bus),
      (mem_iff .train).mp (hmem .train)⟩

/-- The six orderings of the monochromatic-triangle condition on three link
types, derived from the canonical one. -/
theorem tri6 {x y z : Link} (h : ¬(x = y ∧ x = z)) :
    ¬(x = y ∧ x = z) ∧ ¬(x = z ∧ x = y) ∧ ¬(y = x ∧ y = z) ∧
      ¬(y = z ∧ y = x) ∧ ¬(z = x ∧ z = y) ∧ ¬(z = y ∧ z = x) :=
  ⟨h, fun ⟨e1, e2⟩ ↦ h ⟨e2, e1⟩,
    fun ⟨e1, e2⟩ ↦ h ⟨e1.symm, e1.symm.trans e2⟩,
    fun ⟨e1, e2⟩ ↦ h ⟨e2.symm, e2.symm.trans e1⟩,
    fun ⟨e1, e2⟩ ↦ h ⟨e1.symm.trans e2, e1.symm⟩,
    fun ⟨e1, e2⟩ ↦ h ⟨e2.symm.trans e1, e2.symm⟩⟩

/-- The Boolean check `validB` decides validity of the reconstructed
assignment. -/
theorem validB_iff (u : Fin 10 → Link) : validB u = true ↔ Valid (mkColor u) := by
  -- For each town, express "sees link type `c`" through the ten pairs.
  have ex0 : ∀ c : Link, (∃ w, w ≠ 0 ∧ mkColor u 0 w = c) ↔
      (u 0 = c ∨ u 1 = c ∨ u 2 = c ∨ u 3 = c) := by
    intro c
    constructor
    · rintro ⟨w, hw, e⟩
      fin_cases w
      · exact absurd rfl hw
      · exact Or.inl e
      · exact Or.inr (Or.inl e)
      · exact Or.inr (Or.inr (Or.inl e))
      · exact Or.inr (Or.inr (Or.inr e))
    · rintro (e | e | e | e)
      · exact ⟨1, by decide, e⟩
      · exact ⟨2, by decide, e⟩
      · exact ⟨3, by decide, e⟩
      · exact ⟨4, by decide, e⟩
  have ex1 : ∀ c : Link, (∃ w, w ≠ 1 ∧ mkColor u 1 w = c) ↔
      (u 0 = c ∨ u 4 = c ∨ u 5 = c ∨ u 6 = c) := by
    intro c
    constructor
    · rintro ⟨w, hw, e⟩
      fin_cases w
      · exact Or.inl e
      · exact absurd rfl hw
      · exact Or.inr (Or.inl e)
      · exact Or.inr (Or.inr (Or.inl e))
      · exact Or.inr (Or.inr (Or.inr e))
    · rintro (e | e | e | e)
      · exact ⟨0, by decide, e⟩
      · exact ⟨2, by decide, e⟩
      · exact ⟨3, by decide, e⟩
      · exact ⟨4, by decide, e⟩
  have ex2 : ∀ c : Link, (∃ w, w ≠ 2 ∧ mkColor u 2 w = c) ↔
      (u 1 = c ∨ u 4 = c ∨ u 7 = c ∨ u 8 = c) := by
    intro c
    constructor
    · rintro ⟨w, hw, e⟩
      fin_cases w
      · exact Or.inl e
      · exact Or.inr (Or.inl e)
      · exact absurd rfl hw
      · exact Or.inr (Or.inr (Or.inl e))
      · exact Or.inr (Or.inr (Or.inr e))
    · rintro (e | e | e | e)
      · exact ⟨0, by decide, e⟩
      · exact ⟨1, by decide, e⟩
      · exact ⟨3, by decide, e⟩
      · exact ⟨4, by decide, e⟩
  have ex3 : ∀ c : Link, (∃ w, w ≠ 3 ∧ mkColor u 3 w = c) ↔
      (u 2 = c ∨ u 5 = c ∨ u 7 = c ∨ u 9 = c) := by
    intro c
    constructor
    · rintro ⟨w, hw, e⟩
      fin_cases w
      · exact Or.inl e
      · exact Or.inr (Or.inl e)
      · exact Or.inr (Or.inr (Or.inl e))
      · exact absurd rfl hw
      · exact Or.inr (Or.inr (Or.inr e))
    · rintro (e | e | e | e)
      · exact ⟨0, by decide, e⟩
      · exact ⟨1, by decide, e⟩
      · exact ⟨2, by decide, e⟩
      · exact ⟨4, by decide, e⟩
  have ex4 : ∀ c : Link, (∃ w, w ≠ 4 ∧ mkColor u 4 w = c) ↔
      (u 3 = c ∨ u 6 = c ∨ u 8 = c ∨ u 9 = c) := by
    intro c
    constructor
    · rintro ⟨w, hw, e⟩
      fin_cases w
      · exact Or.inl e
      · exact Or.inr (Or.inl e)
      · exact Or.inr (Or.inr (Or.inl e))
      · exact Or.inr (Or.inr (Or.inr e))
      · exact absurd rfl hw
    · rintro (e | e | e | e)
      · exact ⟨0, by decide, e⟩
      · exact ⟨1, by decide, e⟩
      · exact ⟨2, by decide, e⟩
      · exact ⟨3, by decide, e⟩
  -- A link type used somewhere is used on one of the ten pairs.
  have or10 : ∀ {P : Fin 10 → Prop}, (∃ k, P k) →
      (P 0 ∨ P 1 ∨ P 2 ∨ P 3 ∨ P 4 ∨ P 5 ∨ P 6 ∨ P 7 ∨ P 8 ∨ P 9) := by
    intro P h
    obtain ⟨k, h⟩ := h
    fin_cases k
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl h))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr h))))))))
  simp only [validB, seesAll3, monoE, usesC, Bool.and_eq_true, Bool.or_eq_true,
    Bool.not_eq_true', ← Bool.not_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨t0, t1, t2, t3, t4, m012, m013, m014, m023, m024, m034, m123, m124,
      m134, m234, ua, ub, ut⟩
    refine ⟨mkColor_symm u, ?_, ?_, ?_, ?_, ?_⟩
    · rcases ua with h | h | h | h | h | h | h | h | h | h
      · exact ⟨0, 1, by decide, h⟩
      · exact ⟨0, 2, by decide, h⟩
      · exact ⟨0, 3, by decide, h⟩
      · exact ⟨0, 4, by decide, h⟩
      · exact ⟨1, 2, by decide, h⟩
      · exact ⟨1, 3, by decide, h⟩
      · exact ⟨1, 4, by decide, h⟩
      · exact ⟨2, 3, by decide, h⟩
      · exact ⟨2, 4, by decide, h⟩
      · exact ⟨3, 4, by decide, h⟩
    · rcases ub with h | h | h | h | h | h | h | h | h | h
      · exact ⟨0, 1, by decide, h⟩
      · exact ⟨0, 2, by decide, h⟩
      · exact ⟨0, 3, by decide, h⟩
      · exact ⟨0, 4, by decide, h⟩
      · exact ⟨1, 2, by decide, h⟩
      · exact ⟨1, 3, by decide, h⟩
      · exact ⟨1, 4, by decide, h⟩
      · exact ⟨2, 3, by decide, h⟩
      · exact ⟨2, 4, by decide, h⟩
      · exact ⟨3, 4, by decide, h⟩
    · rcases ut with h | h | h | h | h | h | h | h | h | h
      · exact ⟨0, 1, by decide, h⟩
      · exact ⟨0, 2, by decide, h⟩
      · exact ⟨0, 3, by decide, h⟩
      · exact ⟨0, 4, by decide, h⟩
      · exact ⟨1, 2, by decide, h⟩
      · exact ⟨1, 3, by decide, h⟩
      · exact ⟨1, 4, by decide, h⟩
      · exact ⟨2, 3, by decide, h⟩
      · exact ⟨2, 4, by decide, h⟩
      · exact ⟨3, 4, by decide, h⟩
    · intro v
      rw [card_le_two_iff]
      fin_cases v <;> rintro ⟨ha, hb, ht⟩
      · exact t0 ⟨(ex0 .air).mp ha, (ex0 .bus).mp hb, (ex0 .train).mp ht⟩
      · exact t1 ⟨(ex1 .air).mp ha, (ex1 .bus).mp hb, (ex1 .train).mp ht⟩
      · exact t2 ⟨(ex2 .air).mp ha, (ex2 .bus).mp hb, (ex2 .train).mp ht⟩
      · exact t3 ⟨(ex3 .air).mp ha, (ex3 .bus).mp hb, (ex3 .train).mp ht⟩
      · exact t4 ⟨(ex4 .air).mp ha, (ex4 .bus).mp hb, (ex4 .train).mp ht⟩
    · obtain ⟨h012a, h012b, h012c, h012d, h012e, h012f⟩ := tri6 m012
      obtain ⟨h013a, h013b, h013c, h013d, h013e, h013f⟩ := tri6 m013
      obtain ⟨h014a, h014b, h014c, h014d, h014e, h014f⟩ := tri6 m014
      obtain ⟨h023a, h023b, h023c, h023d, h023e, h023f⟩ := tri6 m023
      obtain ⟨h024a, h024b, h024c, h024d, h024e, h024f⟩ := tri6 m024
      obtain ⟨h034a, h034b, h034c, h034d, h034e, h034f⟩ := tri6 m034
      obtain ⟨h123a, h123b, h123c, h123d, h123e, h123f⟩ := tri6 m123
      obtain ⟨h124a, h124b, h124c, h124d, h124e, h124f⟩ := tri6 m124
      obtain ⟨h134a, h134b, h134c, h134d, h134e, h134f⟩ := tri6 m134
      obtain ⟨h234a, h234b, h234c, h234d, h234e, h234f⟩ := tri6 m234
      intro a b c hab hbc hac
      fin_cases a <;> fin_cases b <;> fin_cases c
        <;> first
          | exact absurd rfl hab
          | exact absurd rfl hbc
          | exact absurd rfl hac
          | assumption
  · rintro ⟨hsymm, hair, hbus, htrain, hmax, hmono⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rintro ⟨da, db, dt⟩
      exact (card_le_two_iff.mp (hmax 0)) ⟨(ex0 .air).mpr da, (ex0 .bus).mpr db,
        (ex0 .train).mpr dt⟩
    · rintro ⟨da, db, dt⟩
      exact (card_le_two_iff.mp (hmax 1)) ⟨(ex1 .air).mpr da, (ex1 .bus).mpr db,
        (ex1 .train).mpr dt⟩
    · rintro ⟨da, db, dt⟩
      exact (card_le_two_iff.mp (hmax 2)) ⟨(ex2 .air).mpr da, (ex2 .bus).mpr db,
        (ex2 .train).mpr dt⟩
    · rintro ⟨da, db, dt⟩
      exact (card_le_two_iff.mp (hmax 3)) ⟨(ex3 .air).mpr da, (ex3 .bus).mpr db,
        (ex3 .train).mpr dt⟩
    · rintro ⟨da, db, dt⟩
      exact (card_le_two_iff.mp (hmax 4)) ⟨(ex4 .air).mpr da, (ex4 .bus).mpr db,
        (ex4 .train).mpr dt⟩
    · rintro ⟨e1, e2⟩
      exact hmono 0 1 2 (by decide) (by decide) (by decide) ⟨e1, e2⟩
    · rintro ⟨e1, e2⟩
      exact hmono 0 1 3 (by decide) (by decide) (by decide) ⟨e1, e2⟩
    · rintro ⟨e1, e2⟩
      exact hmono 0 1 4 (by decide) (by decide) (by decide) ⟨e1, e2⟩
    · rintro ⟨e1, e2⟩
      exact hmono 0 2 3 (by decide) (by decide) (by decide) ⟨e1, e2⟩
    · rintro ⟨e1, e2⟩
      exact hmono 0 2 4 (by decide) (by decide) (by decide) ⟨e1, e2⟩
    · rintro ⟨e1, e2⟩
      exact hmono 0 3 4 (by decide) (by decide) (by decide) ⟨e1, e2⟩
    · rintro ⟨e1, e2⟩
      exact hmono 1 2 3 (by decide) (by decide) (by decide) ⟨e1, e2⟩
    · rintro ⟨e1, e2⟩
      exact hmono 1 2 4 (by decide) (by decide) (by decide) ⟨e1, e2⟩
    · rintro ⟨e1, e2⟩
      exact hmono 1 3 4 (by decide) (by decide) (by decide) ⟨e1, e2⟩
    · rintro ⟨e1, e2⟩
      exact hmono 2 3 4 (by decide) (by decide) (by decide) ⟨e1, e2⟩
    · obtain ⟨i, j, hij, e⟩ := hair
      exact or10 (P := fun k ↦ u k = .air) ⟨edgeIdx i j, by rwa [mkColor_apply u hij] at e⟩
    · obtain ⟨i, j, hij, e⟩ := hbus
      exact or10 (P := fun k ↦ u k = .bus) ⟨edgeIdx i j, by rwa [mkColor_apply u hij] at e⟩
    · obtain ⟨i, j, hij, e⟩ := htrain
      exact or10 (P := fun k ↦ u k = .train) ⟨edgeIdx i j, by rwa [mkColor_apply u hij] at e⟩

set_option maxHeartbeats 0 in
/-- The finite check over all `3^10` assignments, evaluated by kernel
reduction. The enumeration is stated as ten nested quantifiers over `Link` —
three choices each — so that the reduction stays shallow. The first four
variables are case-split before the kernel reduction, so that the kernel only
ever enumerates `3^6 = 729` assignments at a time; this keeps the peak
elaboration memory low. -/
theorem check5B : ∀ c₀ c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ : Link,
    validB (mkU c₀ c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉) = false := by
  intro c₀ c₁ c₂ c₃
  cases c₀ <;> cases c₁ <;> cases c₂ <;> cases c₃ <;> decide +kernel

/-- A brute-force check: no link assignment on five towns satisfies all the
criteria. (The conditions only involve the ten unordered pairs, so there are
only `3^10` symmetric assignments to check, see `check5B`.) -/
theorem check5 : ∀ u : Fin 10 → Link, ¬ Valid (mkColor u) := by
  intro u hu
  rw [← validB_iff u] at hu
  have hu' : mkU (u 0) (u 1) (u 2) (u 3) (u 4) (u 5) (u 6) (u 7) (u 8) (u 9) = u := by
    funext k
    fin_cases k <;> rfl
  rw [← hu'] at hu
  rw [check5B (u 0) (u 1) (u 2) (u 3) (u 4) (u 5) (u 6) (u 7) (u 8) (u 9)] at hu
  exact Bool.noConfusion hu

theorem not_valid_five {f : Fin 5 → Fin 5 → Link} (hf : Valid f) : False :=
  check5 _ (valid_mkColor hf)

snip end

problem usa1981_p2 :
    IsGreatest {n : ℕ | ∃ f : Fin n → Fin n → Link, Valid f} answer := by
  refine ⟨⟨fun i j ↦
      if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) then .bus
      else if (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) then .train
      else .air, by decide⟩, fun n hn ↦ ?_⟩
  -- Four towns are achievable: link towns `0` and `1` by bus, towns `2` and
  -- `3` by train, and all other pairs by air.
  obtain ⟨f, hf⟩ := hn
  by_contra h
  rw [not_le, show answer = 4 from rfl] at h
  -- `4 < n`; we derive a contradiction.
  rcases (show n = 5 ∨ 6 ≤ n by omega) with h5 | h6
  · subst h5
    exact not_valid_five hf
  · have v : Fin n := ⟨0, by omega⟩
    have h4 := card_neighbors_le_four hf v
    rw [card_filter_ne v] at h4
    omega

end Usa1981P2

