/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Powerset
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics] }

/-!
# USA Mathematical Olympiad 2015, Problem 3

Let S = {1, 2, ..., n}, where n ≥ 1. Each of the 2ⁿ subsets of S is to be colored red or
blue. (The subset itself is assigned a color and not its individual elements.) For any set
T ⊆ S, we then write f(T) for the number of subsets of T that are blue. Determine the number
of colorings that satisfy the following condition: for any subsets T₁ and T₂ of S,

  f(T₁) f(T₂) = f(T₁ ∪ T₂) f(T₁ ∩ T₂).
-/

namespace Usa2015P3

/-- A coloring of the subsets of `Fin n`; `true` means blue, `false` means red. -/
abbrev Coloring (n : ℕ) : Type := Finset (Fin n) → Bool

/-- `blueCard c T` is the number of subsets of `T` that are colored blue by `c`;
this is the function `f` of the problem statement. -/
def blueCard {n : ℕ} (c : Coloring n) (T : Finset (Fin n)) : ℕ :=
  (T.powerset.filter fun W => c W = true).card

/-- A coloring is *valid* if it satisfies the multiplicative condition of the problem. -/
def IsValid {n : ℕ} (c : Coloring n) : Prop :=
  ∀ T₁ T₂ : Finset (Fin n),
    blueCard c T₁ * blueCard c T₂ = blueCard c (T₁ ∪ T₂) * blueCard c (T₁ ∩ T₂)

/-- The colorings that the problem asks to count. -/
def ValidColorings (n : ℕ) : Type := {c : Coloring n // IsValid c}

instance (n : ℕ) : DecidablePred (@IsValid n) := fun _ => Fintype.decidableForallFintype

instance (n : ℕ) : Fintype (ValidColorings n) := Subtype.fintype _

snip begin

/-- The intersection of all blue sets of a coloring. We show that for a nontrivial valid
coloring the blue sets are exactly the sets `T` with `X c ⊆ T ⊆ X c ∪ B c`. -/
def X {n : ℕ} (c : Coloring n) : Finset (Fin n) :=
  Finset.univ.filter fun i => ∀ T, c T = true → i ∈ T

/-- The elements `i` outside `X c` such that `X c ∪ {i}` is blue. -/
def B {n : ℕ} (c : Coloring n) : Finset (Fin n) :=
  Finset.univ.filter fun i => i ∉ X c ∧ c (X c ∪ {i}) = true

lemma mem_X {n : ℕ} {c : Coloring n} {i : Fin n} :
    i ∈ X c ↔ ∀ T, c T = true → i ∈ T := by
  simp [X]

lemma mem_B {n : ℕ} {c : Coloring n} {i : Fin n} :
    i ∈ B c ↔ i ∉ X c ∧ c (X c ∪ {i}) = true := by
  simp [B]

lemma blueCard_ne_zero_iff {n : ℕ} {c : Coloring n} {T : Finset (Fin n)} :
    blueCard c T ≠ 0 ↔ ∃ W ⊆ T, c W = true := by
  rw [blueCard, ← pos_iff_ne_zero, Finset.card_pos, Finset.filter_nonempty_iff]
  simp only [Finset.mem_powerset]

lemma blueCard_ne_zero_of_mem {n : ℕ} {c : Coloring n} {T : Finset (Fin n)}
    (h : c T = true) : blueCard c T ≠ 0 :=
  blueCard_ne_zero_iff.mpr ⟨T, Finset.Subset.refl _, h⟩

section Classification

variable {n : ℕ} {c : Coloring n} (hv : IsValid c)

include hv

/-- If two sets contain a blue subset each, so does their intersection. -/
lemma blueCard_ne_zero_inter {T₁ T₂ : Finset (Fin n)}
    (h₁ : blueCard c T₁ ≠ 0) (h₂ : blueCard c T₂ ≠ 0) : blueCard c (T₁ ∩ T₂) ≠ 0 := by
  intro h
  have h3 := hv T₁ T₂
  rw [h, mul_zero] at h3
  exact mul_ne_zero h₁ h₂ h3

/-- The intersection of a nonempty family of sets each containing a blue subset
itself contains a blue subset. -/
lemma blueCard_ne_zero_inter_all (F : Finset (Finset (Fin n))) :
    F.Nonempty → (∀ T ∈ F, blueCard c T ≠ 0) →
    blueCard c (Finset.univ.filter fun i => ∀ T ∈ F, i ∈ T) ≠ 0 := by
  intro hs
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a =>
      intro hF
      have h1 : (Finset.univ.filter fun i => ∀ T ∈ ({a} : Finset (Finset (Fin n))), i ∈ T)
          = a := by
        ext i
        simp
      rw [h1]
      exact hF a (Finset.mem_singleton_self a)
  | cons a s ha hs ih =>
      intro hF
      have h1 : blueCard c a ≠ 0 := hF a (Finset.mem_cons.mpr (Or.inl rfl))
      have h2 := ih (fun T hT => hF T (Finset.mem_cons.mpr (Or.inr hT)))
      have h3 : (Finset.univ.filter fun i => ∀ T ∈ Finset.cons a s ha, i ∈ T) =
          a ∩ (Finset.univ.filter fun i => ∀ T ∈ s, i ∈ T) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_inter,
          Finset.mem_cons]
        constructor
        · intro h
          exact ⟨h a (Or.inl rfl), fun T hT => h T (Or.inr hT)⟩
        · rintro ⟨ha', hs'⟩ T (rfl | hT)
          · exact ha'
          · exact hs' T hT
      rw [h3]
      exact blueCard_ne_zero_inter hv h1 h2

/-- The intersection `X c` of all blue sets contains a blue subset. -/
lemma blueCard_ne_zero_X (hne : ∃ T, c T = true) : blueCard c (X c) ≠ 0 := by
  obtain ⟨T₀, hT₀⟩ := hne
  have hXF : X c = Finset.univ.filter
      (fun i => ∀ T ∈ Finset.univ.filter (fun T => c T = true), i ∈ T) := by
    ext i
    simp only [X, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hXF]
  apply blueCard_ne_zero_inter_all hv _
    ⟨T₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hT₀⟩⟩
  intro T hT
  exact blueCard_ne_zero_of_mem ((Finset.mem_filter.mp hT).2)

/-- The intersection `X c` of all blue sets is itself blue. -/
lemma X_blue (hne : ∃ T, c T = true) : c (X c) = true := by
  obtain ⟨W, hWX, hW⟩ := blueCard_ne_zero_iff.mp (blueCard_ne_zero_X hv hne)
  have hXW : X c ⊆ W := fun i hi => mem_X.mp hi W hW
  have hWeq : W = X c := Finset.Subset.antisymm hWX hXW
  rwa [hWeq] at hW

/-- `X c` is the only blue subset of itself. -/
lemma blueCard_X (hne : ∃ T, c T = true) : blueCard c (X c) = 1 := by
  have h1 : (X c).powerset.filter (fun W => c W = true) = {X c} := by
    ext W
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_singleton]
    constructor
    · rintro ⟨hWX, hW⟩
      exact Finset.Subset.antisymm hWX (fun i hi => mem_X.mp hi W hW)
    · intro hW
      rw [hW]
      exact ⟨Finset.Subset.refl _, X_blue hv hne⟩
  rw [blueCard, h1, Finset.card_singleton]

/-- Multiplicativity of `blueCard` over pairs of sets whose intersection is `X c`. -/
lemma blueCard_union {T₁ T₂ : Finset (Fin n)} (h1 : X c ⊆ T₁) (h2 : X c ⊆ T₂)
    (h3 : T₁ ∩ T₂ ⊆ X c) (hne : ∃ T, c T = true) :
    blueCard c (T₁ ∪ T₂) = blueCard c T₁ * blueCard c T₂ := by
  have h4 : T₁ ∩ T₂ = X c := Finset.Subset.antisymm h3 (Finset.subset_inter h1 h2)
  have h5 := hv T₁ T₂
  rw [h4, blueCard_X hv hne, mul_one] at h5
  exact h5.symm

/-- `X c ∪ {i}` has one blue subset if it is red (`X c` itself) and two if it is blue. -/
lemma blueCard_singleton (i : Fin n) (hi : i ∉ X c) (hne : ∃ T, c T = true) :
    blueCard c (X c ∪ {i}) = if c (X c ∪ {i}) then 2 else 1 := by
  have hfilter : ∀ W : Finset (Fin n), W ⊆ X c ∪ {i} → c W = true →
      W = X c ∨ W = X c ∪ {i} := by
    intro W hW hcW
    have hXW : X c ⊆ W := fun j hj => mem_X.mp hj W hcW
    have h2 : W \ X c ⊆ {i} := by
      intro x hx
      obtain ⟨hxW, hxX⟩ := Finset.mem_sdiff.mp hx
      have h3 := hW hxW
      simp only [Finset.mem_union, Finset.mem_singleton] at h3
      rcases h3 with h3 | h3
      · exact absurd h3 hxX
      · exact Finset.mem_singleton.mpr h3
    rcases Finset.subset_singleton_iff.mp h2 with h3 | h3
    · left
      rw [Finset.sdiff_eq_empty_iff_subset] at h3
      exact Finset.Subset.antisymm h3 hXW
    · right
      rw [← Finset.union_sdiff_of_subset hXW, h3]
  by_cases hb : c (X c ∪ {i}) = true
  · have h1 : (X c ∪ {i}).powerset.filter (fun W => c W = true) = {X c, X c ∪ {i}} := by
      ext W
      simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · rintro ⟨hW, hcW⟩
        exact hfilter W hW hcW
      · rintro (rfl | rfl)
        · exact ⟨Finset.subset_union_left, X_blue hv hne⟩
        · exact ⟨Finset.Subset.refl _, hb⟩
    have h2 : X c ∉ ({X c ∪ {i}} : Finset (Finset (Fin n))) := by
      simp only [Finset.mem_singleton]
      intro h
      have h3 : i ∈ X c := by
        have h4 : i ∈ X c ∪ {i} :=
          Finset.mem_union.mpr (Or.inr (Finset.mem_singleton_self i))
        rwa [← h] at h4
      exact hi h3
    rw [if_pos hb, blueCard, h1, Finset.card_insert_of_notMem h2, Finset.card_singleton]
  · have h1 : (X c ∪ {i}).powerset.filter (fun W => c W = true) = {X c} := by
      ext W
      simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_singleton]
      constructor
      · rintro ⟨hW, hcW⟩
        rcases hfilter W hW hcW with h | h
        · exact h
        · rw [h] at hcW
          exact absurd hcW hb
      · intro hW
        rw [hW]
        exact ⟨Finset.subset_union_left, X_blue hv hne⟩
    rw [if_neg hb, blueCard, h1, Finset.card_singleton]

/-- `blueCard` is multiplicative over the elements of a set disjoint from `X c`. -/
lemma blueCard_prod (U : Finset (Fin n)) (hne : ∃ T, c T = true) :
    Disjoint (X c) U → blueCard c (X c ∪ U) = ∏ i ∈ U, blueCard c (X c ∪ {i}) := by
  induction U using Finset.induction with
  | empty =>
      intro hU
      simp [Finset.union_empty, blueCard_X hv hne]
  | insert i U hi ih =>
      intro hU
      have hU' : Disjoint (X c) U := hU.mono_right (Finset.subset_insert i U)
      have hiX : i ∉ X c := by
        intro h
        exact (Finset.disjoint_left.mp hU h) (Finset.mem_insert_self i U)
      have hcap : (X c ∪ {i}) ∩ (X c ∪ U) ⊆ X c := by
        intro x hx
        simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_singleton] at hx
        obtain ⟨hx1 | rfl, hx2 | hx3⟩ := hx
        · exact hx1
        · exact hx1
        · exact hx2
        · exact absurd hx3 hi
      rw [Finset.prod_insert hi, ← ih hU']
      have hU1 : X c ∪ insert i U = (X c ∪ {i}) ∪ (X c ∪ U) := by
        ext x
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
        tauto
      rw [hU1]
      exact blueCard_union hv Finset.subset_union_left Finset.subset_union_left hcap hne

/-- For `U` disjoint from `X c`, the number of blue subsets of `X c ∪ U` is a power of two
determined by which of the `X c ∪ {i}` are blue. -/
lemma blueCard_pow (U : Finset (Fin n)) (hU : Disjoint (X c) U) (hne : ∃ T, c T = true) :
    blueCard c (X c ∪ U) = 2 ^ (U.filter fun i => c (X c ∪ {i})).card := by
  have h1 : ∀ i ∈ U, blueCard c (X c ∪ {i}) = if c (X c ∪ {i}) then 2 else 1 := by
    intro i hi
    exact blueCard_singleton hv i (Finset.disjoint_right.mp hU hi) hne
  rw [blueCard_prod hv U hne hU, Finset.prod_congr rfl h1, Finset.prod_ite]
  simp [Finset.prod_const]

/-- Every set in the interval `[X c, X c ∪ B c]` is blue. -/
lemma blue_of_mem_interval (hne : ∃ T, c T = true) {T : Finset (Fin n)}
    (hXT : X c ⊆ T) (hTB : T ⊆ X c ∪ B c) : c T = true := by
  have hT : T = X c ∪ (T \ X c) := (Finset.union_sdiff_of_subset hXT).symm
  have hUB : T \ X c ⊆ B c := by
    intro i hi
    obtain ⟨hiT, hiX⟩ := Finset.mem_sdiff.mp hi
    have hiXB := hTB hiT
    rw [mem_B]
    refine ⟨hiX, ?_⟩
    simp only [Finset.mem_union] at hiXB
    rcases hiXB with h | h
    · exact absurd h hiX
    · exact (mem_B.mp h).2
  have hfil : (T \ X c).filter (fun i => c (X c ∪ {i})) = T \ X c := by
    apply Finset.filter_true_of_mem
    intro i hi
    exact (mem_B.mp (hUB hi)).2
  have hf : blueCard c T = 2 ^ (T \ X c).card := by
    conv_lhs => rw [hT, blueCard_pow hv (T \ X c) Finset.disjoint_sdiff hne, hfil]
  have himg_sub : (T.powerset.filter (fun W => c W = true)).image (fun W => W \ X c) ⊆
      (T \ X c).powerset := by
    intro V hV
    obtain ⟨W, hW, rfl⟩ := Finset.mem_image.mp hV
    rw [Finset.mem_filter, Finset.mem_powerset] at hW
    rw [Finset.mem_powerset]
    exact Finset.sdiff_subset_sdiff hW.1 (Finset.Subset.refl _)
  have hinj : Set.InjOn (fun W => W \ X c) ↑(T.powerset.filter (fun W => c W = true)) := by
    intro W₁ hW₁ W₂ hW₂ h
    change W₁ \ X c = W₂ \ X c at h
    rw [Finset.mem_coe, Finset.mem_filter] at hW₁ hW₂
    have h1 : X c ⊆ W₁ := fun j hj => mem_X.mp hj W₁ hW₁.2
    have h2 : X c ⊆ W₂ := fun j hj => mem_X.mp hj W₂ hW₂.2
    have e1 := Finset.union_sdiff_of_subset h1
    have e2 := Finset.union_sdiff_of_subset h2
    rw [← e1, h, e2]
  have hcard : ((T.powerset.filter (fun W => c W = true)).image fun W => W \ X c).card =
      (T \ X c).powerset.card := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_powerset, ← hf, blueCard]
  have heq : (T.powerset.filter (fun W => c W = true)).image (fun W => W \ X c) =
      (T \ X c).powerset :=
    Finset.eq_of_subset_of_card_le himg_sub (le_of_eq hcard.symm)
  have hmem : T \ X c ∈ (T \ X c).powerset := Finset.mem_powerset.mpr (Finset.Subset.refl _)
  rw [← heq] at hmem
  obtain ⟨W, hW, hWX⟩ := Finset.mem_image.mp hmem
  rw [Finset.mem_filter] at hW
  have hXW : X c ⊆ W := fun j hj => mem_X.mp hj W hW.2
  have hWeq : W = T := by
    have e := Finset.union_sdiff_of_subset hXW
    rw [hWX, ← hT] at e
    exact e.symm
  rw [hWeq] at hW
  exact hW.2

/-- Every blue set lies in the interval `[X c, X c ∪ B c]`. -/
lemma interval_of_blue (hne : ∃ T, c T = true) {T : Finset (Fin n)} (hcT : c T = true) :
    X c ⊆ T ∧ T ⊆ X c ∪ B c := by
  have hXT : X c ⊆ T := fun i hi => mem_X.mp hi T hcT
  refine ⟨hXT, ?_⟩
  intro i hiT
  by_contra hiXB
  have hiX : i ∉ X c := fun h => hiXB (Finset.mem_union.mpr (Or.inl h))
  have hiB : i ∉ B c := fun h => hiXB (Finset.mem_union.mpr (Or.inr h))
  have hci : c (X c ∪ {i}) = false := by
    by_contra h
    exact hiB (mem_B.mpr ⟨hiX, Bool.eq_true_of_not_eq_false h⟩)
  have hT : T = X c ∪ (T \ X c) := (Finset.union_sdiff_of_subset hXT).symm
  have hfT : blueCard c T = 2 ^ ((T \ X c).filter fun j => c (X c ∪ {j})).card := by
    conv_lhs => rw [hT, blueCard_pow hv (T \ X c) Finset.disjoint_sdiff hne]
  have hTnotin : T ∉ (((T \ X c).filter fun j => c (X c ∪ {j})).powerset.image
      fun V => X c ∪ V) := by
    intro h
    obtain ⟨V, hV, hTV⟩ := Finset.mem_image.mp h
    rw [← hTV] at hiT
    rw [Finset.mem_union] at hiT
    rcases hiT with hiT | hiT
    · exact hiX hiT
    · have hif : i ∈ (T \ X c).filter fun j => c (X c ∪ {j}) := by
        rw [Finset.mem_powerset] at hV
        exact hV hiT
      rw [Finset.mem_filter] at hif
      rw [hci] at hif
      exact Bool.false_ne_true hif.2
  have hinj : Set.InjOn (fun V => X c ∪ V)
      ↑(((T \ X c).filter fun j => c (X c ∪ {j})).powerset) := by
    intro V₁ hV₁ V₂ hV₂ h
    rw [Finset.mem_coe, Finset.mem_powerset] at hV₁ hV₂
    have e : ∀ V : Finset (Fin n), V ⊆ T \ X c → (X c ∪ V) \ X c = V := fun V hV =>
      Finset.union_sdiff_cancel_left (Disjoint.mono_right hV Finset.disjoint_sdiff)
    have e1 := e V₁ (Finset.Subset.trans hV₁ (Finset.filter_subset _ (T \ X c)))
    have e2 := e V₂ (Finset.Subset.trans hV₂ (Finset.filter_subset _ (T \ X c)))
    change X c ∪ V₁ = X c ∪ V₂ at h
    rw [h] at e1
    rw [e2] at e1
    exact e1.symm
  have hsub : insert T (((T \ X c).filter fun j => c (X c ∪ {j})).powerset.image
      fun V => X c ∪ V) ⊆ T.powerset.filter (fun W => c W = true) := by
    intro W hW
    simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_powerset] at hW
    rw [Finset.mem_filter, Finset.mem_powerset]
    rcases hW with rfl | ⟨V, hV, rfl⟩
    · exact ⟨Finset.Subset.refl _, hcT⟩
    · have hVB : V ⊆ B c := by
        intro j hj
        have hjf := hV hj
        rw [Finset.mem_filter] at hjf
        obtain ⟨hjU, hcj⟩ := hjf
        obtain ⟨hjT, hjX⟩ := Finset.mem_sdiff.mp hjU
        exact mem_B.mpr ⟨hjX, hcj⟩
      have hVTX : V ⊆ T \ X c := Finset.Subset.trans hV (Finset.filter_subset _ _)
      refine ⟨?_, ?_⟩
      · rw [hT]
        exact Finset.union_subset_union (Finset.Subset.refl _) hVTX
      · exact blue_of_mem_interval hv hne Finset.subset_union_left
          (Finset.union_subset_union (Finset.Subset.refl _) hVB)
  have hcard : (insert T (((T \ X c).filter fun j => c (X c ∪ {j})).powerset.image
      fun V => X c ∪ V)).card =
      2 ^ ((T \ X c).filter fun j => c (X c ∪ {j})).card + 1 := by
    rw [Finset.card_insert_of_notMem hTnotin, Finset.card_image_of_injOn hinj,
      Finset.card_powerset]
  have hle : 2 ^ ((T \ X c).filter fun j => c (X c ∪ {j})).card + 1 ≤ blueCard c T := by
    have h1 := Finset.card_le_card hsub
    rw [hcard] at h1
    exact h1
  rw [hfT] at hle
  exact Nat.not_succ_le_self _ hle

/-- A nontrivial valid coloring is exactly the interval `[X c, X c ∪ B c]`. -/
lemma blue_iff (hne : ∃ T, c T = true) (T : Finset (Fin n)) :
    c T = true ↔ X c ⊆ T ∧ T ⊆ X c ∪ B c := by
  exact ⟨interval_of_blue hv hne, fun ⟨h1, h2⟩ => blue_of_mem_interval hv hne h1 h2⟩

end Classification

section Existence

variable {n : ℕ}

/-- The coloring whose blue sets are exactly the sets `T` with `X₀ ⊆ T ⊆ X₀ ∪ B₀`. -/
def colorOf (X₀ B₀ : Finset (Fin n)) : Coloring n := fun T => decide (X₀ ⊆ T ∧ T ⊆ X₀ ∪ B₀)

lemma blueCard_colorOf {X₀ B₀ : Finset (Fin n)} (h : Disjoint X₀ B₀) (T : Finset (Fin n)) :
    blueCard (colorOf X₀ B₀) T = if X₀ ⊆ T then 2 ^ (T ∩ B₀).card else 0 := by
  by_cases hT : X₀ ⊆ T
  · rw [if_pos hT]
    have hbij : T.powerset.filter (fun W => colorOf X₀ B₀ W = true) =
        (T ∩ B₀).powerset.image (X₀ ∪ ·) := by
      ext W
      simp only [Finset.mem_filter, Finset.mem_powerset, colorOf, decide_eq_true_eq,
        Finset.mem_image]
      constructor
      · rintro ⟨hWT, hXW, hWXB⟩
        refine ⟨W ∩ B₀, Finset.inter_subset_inter hWT (Finset.Subset.refl _), ?_⟩
        ext j
        simp only [Finset.mem_union, Finset.mem_inter]
        constructor
        · rintro (hj | ⟨hjW, -⟩)
          · exact hXW hj
          · exact hjW
        · intro hjW
          have h1 := hWXB hjW
          rw [Finset.mem_union] at h1
          rcases h1 with h1 | h1
          · exact Or.inl h1
          · exact Or.inr ⟨hjW, h1⟩
      · rintro ⟨V, hV, rfl⟩
        have hVT : V ⊆ T := Finset.Subset.trans hV Finset.inter_subset_left
        have hVB : V ⊆ B₀ := Finset.Subset.trans hV Finset.inter_subset_right
        refine ⟨Finset.union_subset hT hVT, Finset.subset_union_left,
          Finset.union_subset_union (Finset.Subset.refl _) hVB⟩
    rw [blueCard, hbij, Finset.card_image_of_injOn, Finset.card_powerset]
    intro V₁ hV₁ V₂ hV₂ heq
    change X₀ ∪ V₁ = X₀ ∪ V₂ at heq
    rw [Finset.mem_coe, Finset.mem_powerset] at hV₁ hV₂
    have hVB1 : V₁ ⊆ B₀ := Finset.Subset.trans hV₁ Finset.inter_subset_right
    have hVB2 : V₂ ⊆ B₀ := Finset.Subset.trans hV₂ Finset.inter_subset_right
    have e : ∀ V : Finset (Fin n), V ⊆ B₀ → (X₀ ∪ V) ∩ B₀ = V := by
      intro V hV
      ext j
      simp only [Finset.mem_inter, Finset.mem_union]
      constructor
      · rintro ⟨hjX | hjV, hjB⟩
        · exact absurd hjB (Finset.disjoint_left.mp h hjX)
        · exact hjV
      · intro hjV
        exact ⟨Or.inr hjV, hV hjV⟩
    have e1 := e V₁ hVB1
    have e2 := e V₂ hVB2
    rw [← e1, heq, e2]
  · rw [if_neg hT]
    have h1 : T.powerset.filter (fun W => colorOf X₀ B₀ W = true) = ∅ := by
      apply Finset.filter_false_of_mem
      intro W hW
      rw [Finset.mem_powerset] at hW
      simp only [colorOf, decide_eq_true_eq, not_and]
      intro hXW hWXB
      exact hT (Finset.Subset.trans hXW hW)
    rw [blueCard, h1, Finset.card_empty]

lemma isValid_colorOf {X₀ B₀ : Finset (Fin n)} (h : Disjoint X₀ B₀) :
    IsValid (colorOf X₀ B₀) := by
  intro T₁ T₂
  rw [blueCard_colorOf h, blueCard_colorOf h, blueCard_colorOf h, blueCard_colorOf h]
  by_cases h1 : X₀ ⊆ T₁ <;> by_cases h2 : X₀ ⊆ T₂
  · rw [if_pos h1, if_pos h2, if_pos (Finset.Subset.trans h1 Finset.subset_union_left),
      if_pos (Finset.subset_inter h1 h2), ← pow_add, ← pow_add]
    congr 1
    have e1 : (T₁ ∪ T₂) ∩ B₀ = (T₁ ∩ B₀) ∪ (T₂ ∩ B₀) :=
      Finset.union_inter_distrib_right _ _ _
    have e2 : (T₁ ∩ T₂) ∩ B₀ = (T₁ ∩ B₀) ∩ (T₂ ∩ B₀) :=
      Finset.inter_inter_distrib_right _ _ _
    rw [e1, e2]
    exact (Finset.card_union_add_card_inter _ _).symm
  · rw [if_pos h1, if_neg h2, if_neg
      (fun h => h2 (Finset.Subset.trans h Finset.inter_subset_right)), mul_zero, mul_zero]
  · rw [if_neg h1, if_pos h2, if_neg
      (fun h => h1 (Finset.Subset.trans h Finset.inter_subset_left)), zero_mul, mul_zero]
  · rw [if_neg h1, if_neg h2, if_neg
      (fun h => h1 (Finset.Subset.trans h Finset.inter_subset_left)), zero_mul, mul_zero]

lemma isValid_all_red {n : ℕ} : IsValid (fun _ => false : Coloring n) := by
  intro T₁ T₂
  have h0 : ∀ T : Finset (Fin n), blueCard (fun _ => false : Coloring n) T = 0 := by
    intro T
    rw [blueCard]
    simp
  simp [h0]

end Existence

/-- The type of disjoint pairs `(X₀, B₀)` of finsets of `Fin n`; these parametrize the
nontrivial valid colorings. -/
def DisjointPairs (n : ℕ) : Type :=
  {p : Finset (Fin n) × Finset (Fin n) // Disjoint p.1 p.2}

instance (n : ℕ) : Fintype (DisjointPairs n) := Subtype.fintype _

/-- The blue interval `[X₀, X₀ ∪ B₀]` of a disjoint pair determines a valid coloring,
and conversely every nontrivial valid coloring arises this way. -/
lemma X_colorOf {n : ℕ} {X₀ B₀ : Finset (Fin n)} :
    X (colorOf X₀ B₀) = X₀ := by
  ext i
  simp only [mem_X, colorOf, decide_eq_true_eq]
  constructor
  · intro h'
    exact h' X₀ ⟨Finset.Subset.refl _, Finset.subset_union_left⟩
  · intro hi T hT'
    exact hT'.1 hi

lemma B_colorOf {n : ℕ} {X₀ B₀ : Finset (Fin n)} (h : Disjoint X₀ B₀) :
    B (colorOf X₀ B₀) = B₀ := by
  ext i
  rw [mem_B, X_colorOf]
  simp only [colorOf, decide_eq_true_eq]
  constructor
  · rintro ⟨hiX, -, hsub⟩
    have h1 : i ∈ X₀ ∪ B₀ :=
      hsub (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton_self i)))
    rw [Finset.mem_union] at h1
    rcases h1 with h1 | h1
    · exact absurd h1 hiX
    · exact h1
  · intro hi
    have hiX : i ∉ X₀ := Finset.disjoint_right.mp h hi
    exact ⟨hiX, Finset.subset_union_left, Finset.union_subset Finset.subset_union_left
      (Finset.singleton_subset_iff.mpr (Finset.mem_union.mpr (Or.inr hi)))⟩

/-- The map from a valid coloring to its parametrizing data: `none` for the all-red
coloring, and the disjoint pair `(X c, B c)` otherwise. -/
def fromColoring {n : ℕ} (c : Coloring n) (_hv : IsValid c) : Option (DisjointPairs n) :=
  if _h : ∃ T, c T = true then
    some ⟨⟨X c, B c⟩, by
      rw [Finset.disjoint_left]
      intro i hiX hiB
      exact (mem_B.mp hiB).1 hiX⟩
  else none

/-- The valid coloring associated to a parameter: the all-red coloring for `none`, and
the interval coloring `colorOf X₀ B₀` for a disjoint pair `(X₀, B₀)`. -/
def toColoring {n : ℕ} : Option (DisjointPairs n) → ValidColorings n
  | none => ⟨fun _ => false, isValid_all_red⟩
  | some ⟨(X₀, B₀), h⟩ => ⟨colorOf X₀ B₀, isValid_colorOf h⟩

/-- The valid colorings are in bijection with the parameters. -/
def mainEquiv (n : ℕ) : ValidColorings n ≃ Option (DisjointPairs n) where
  toFun := fun vc => fromColoring vc.1 vc.2
  invFun := toColoring
  left_inv := fun ⟨c, hv⟩ => by
    by_cases h : ∃ T, c T = true
    · show toColoring (fromColoring c hv) = ⟨c, hv⟩
      unfold fromColoring
      rw [dif_pos h]
      simp only [toColoring]
      apply Subtype.ext
      funext T
      show decide (X c ⊆ T ∧ T ⊆ X c ∪ B c) = c T
      rw [Bool.eq_iff_iff, decide_eq_true_eq]
      exact (blue_iff hv h T).symm
    · show toColoring (fromColoring c hv) = ⟨c, hv⟩
      unfold fromColoring
      rw [dif_neg h]
      simp only [toColoring]
      apply Subtype.ext
      funext T
      show (false : Bool) = c T
      cases e : c T
      · rfl
      · exact absurd ⟨T, e⟩ h
  right_inv := fun opt => by
    rcases opt with _ | ⟨⟨X₀, B₀⟩, hd⟩
    · simp only [toColoring]
      show fromColoring (fun _ => false : Coloring n) isValid_all_red = none
      unfold fromColoring
      rw [dif_neg]
      intro h
      obtain ⟨T, hT⟩ := h
      exact Bool.false_ne_true hT
    · simp only [toColoring]
      show fromColoring (colorOf X₀ B₀) (isValid_colorOf hd) = some ⟨⟨X₀, B₀⟩, hd⟩
      unfold fromColoring
      rw [dif_pos (⟨X₀, by simp [colorOf]⟩ : ∃ T, colorOf X₀ B₀ T = true)]
      congr 1
      apply Subtype.ext
      apply Prod.ext
      · exact X_colorOf
      · exact B_colorOf hd

/-- Disjoint pairs of finsets of `Fin n` correspond to ternary functions: each element
is in `X₀`, in `B₀`, or in neither. -/
def disjointPairEquiv (n : ℕ) : DisjointPairs n ≃ (Fin n → Fin 3) where
  toFun := fun p i => if i ∈ p.1.1 then 0 else if i ∈ p.1.2 then 1 else 2
  invFun := fun g => ⟨(Finset.univ.filter fun i => g i = 0,
      Finset.univ.filter fun i => g i = 1), by
    rw [Finset.disjoint_left]
    intro i hi0 hi1
    have h0 := (Finset.mem_filter.mp hi0).2
    have h1 := (Finset.mem_filter.mp hi1).2
    rw [h0] at h1
    exact absurd h1 (by decide)⟩
  left_inv := fun ⟨⟨X₀, B₀⟩, hd⟩ => by
    apply Subtype.ext
    apply Prod.ext
    · ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h
        by_contra hi
        rw [if_neg hi] at h
        by_cases hi2 : i ∈ B₀
        · rw [if_pos hi2] at h
          exact absurd h (by decide)
        · rw [if_neg hi2] at h
          exact absurd h (by decide)
      · intro h
        rw [if_pos h]
    · ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h
        by_cases hi1 : i ∈ X₀
        · rw [if_pos hi1] at h
          exact absurd h (by decide)
        · rw [if_neg hi1] at h
          by_cases hi2 : i ∈ B₀
          · exact hi2
          · rw [if_neg hi2] at h
            exact absurd h (by decide)
      · intro h
        have hi1 : i ∉ X₀ := Finset.disjoint_right.mp hd h
        rw [if_neg hi1, if_pos h]
  right_inv := fun g => by
    funext i
    show (if i ∈ Finset.univ.filter (fun j => g j = 0) then (0 : Fin 3)
        else if i ∈ Finset.univ.filter (fun j => g j = 1) then 1 else 2) = g i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hlt := (g i).isLt
    have h3 : (g i).val = 0 ∨ (g i).val = 1 ∨ (g i).val = 2 := by omega
    rcases h3 with h | h | h
    · have e : g i = 0 := Fin.ext h
      rw [if_pos e]
      exact e.symm
    · have e : g i = 1 := Fin.ext h
      rw [if_neg (by rw [e]; decide), if_pos e]
      exact e.symm
    · have e : g i = 2 := Fin.ext h
      rw [if_neg (by rw [e]; decide), if_neg (by rw [e]; decide)]
      exact e.symm

lemma card_disjointPairs (n : ℕ) : Fintype.card (DisjointPairs n) = 3 ^ n := by
  rw [Fintype.card_congr (disjointPairEquiv n), Fintype.card_fun]
  simp

lemma card_validColorings (n : ℕ) : Fintype.card (ValidColorings n) = 3 ^ n + 1 := by
  rw [Fintype.card_congr (mainEquiv n), Fintype.card_option, card_disjointPairs]

snip end

determine NumberOfColorings (n : ℕ) : ℕ := 3 ^ n + 1

problem usa2015_p3 (n : ℕ) :
    Fintype.card (ValidColorings n) = NumberOfColorings n := by
  exact card_validColorings n

end Usa2015P3
