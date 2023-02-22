import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Interval
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.NAry
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.Linarith

/-!
# International Mathematical Olympiad 1987, Problem 4

Prove that there is no function f : ℕ → ℕ such that f(f(n)) = n + 1987
for every n.
-/

-- Should we be using Finset.card instead of Fintype.card?


#check Set.toFinset

theorem foo (f : ℕ → ℕ) (A : Finset ℕ) (hi : f.Injective) :
    Fintype.card A = Fintype.card (f '' A) := by
  sorry

#check Finset.disjUnion
#check Finset.card_disjUnion

theorem baz' (A B : Finset ℕ) (hd : Disjoint A B) :
    Finset.card (A ∪ B) = A.card + B.card := by
  rw[←Finset.disjUnion_eq_union A B hd]
  exact Finset.card_disjUnion A B hd

theorem bar0' (A B : Set ℕ) (ha : Fintype A) (hb : Fintype B) (hd : A ⊆ B) :
    A.toFinset ⊆ B.toFinset := Set.toFinset_mono hd

theorem bar0'' (A : Set ℕ) (B : Finset ℕ) (ha : Fintype A)
    (hd : B ⊆ A.toFinset) : B.toSet ⊆ A := by
  intros x hx
  rw[Finset.mem_coe] at hx
  have := hd hx
  rw [Set.mem_toFinset] at this
  exact this

theorem bar0 {A B : Set ℕ} (ha : Fintype A) (hb : Fintype B) (hd : Disjoint A B) :
    Disjoint A.toFinset B.toFinset := by
  intros C hCa hCb
  have hCa' : C.toSet ≤ A := bar0'' A C _ hCa
  have hCb' : C.toSet ≤ B := bar0'' B C _ hCb
  intros c hc
  exact (hd hCa' hCb' hc).elim

#check Set.card_image_of_inj_on
#check Set.card_image_of_injective

theorem bar (f : ℕ → ℕ) (A : Set ℕ) (h : Fintype A) (hi : f.Injective) :
    Fintype.card (f '' A) = Fintype.card A := by
  exact Set.card_image_of_injective A hi

-- ab_finite : Fintype ↑(A ∪ B)
-- Set.toFinset (A ∪ B) : Finset ℕ

-- Set.toFinset (A ∪ B) = Set.toFinset A ∪ Set.toFinset B
#check Set.toFinset_union


theorem bar1 (A B : Set ℕ) (ha : Fintype A) (hb : Fintype B)
    (hab : Fintype ↑(A ∪ B)):
    @Set.toFinset _ (A ∪ B) hab = @Set.toFinset _ A ha ∪ @Set.toFinset _ B hb :=
  Set.toFinset_union A B

#check (· ⊆ ·)

theorem bar2 (A B : Set ℕ) (hab : Fintype ↑(A ∪ B)) : Fintype A := by
  sorry

#check Fintype
#check Finite
#check Set.Finite
#check Set.Finite.subset

theorem bar3 (A B : Set ℕ) (h : A ⊆ B) (hab : B.Finite) : A.Finite := by
  exact Set.Finite.subset hab h

theorem bar4 (A B : Set ℕ) (h : A ⊆ B) (hab : Finite ↑B) : Finite ↑A := by
  rw[Set.finite_coe_iff]
  rw[Set.finite_coe_iff] at hab
  exact Set.Finite.subset hab h

#check Fintype.ofFinite
#check Finite.of_fintype

theorem bar5 (A B : Set ℕ) (h : A ⊆ B) (hab : Fintype ↑B) : Fintype ↑A := by
  suffices Finite ↑A by exact Fintype.ofFinite A
  apply bar4 A B h
  -- library_search -- TODO: namedPattern brokenness!
  exact (Finite.of_fintype ↑B)

theorem bar6 (A B : Set ℕ) (hab : Fintype ↑(A ∪ B)) : Fintype ↑A := by
  have h : A ⊆ A ∪ B := Set.subset_union_left A B
  exact bar5 A (A ∪ B) h hab

theorem bar7 (A B : Set ℕ) (hab : Fintype ↑(A ∪ B)) : Fintype ↑B := by
  have h : B ⊆ A ∪ B := Set.subset_union_right A B
  exact bar5 B (A ∪ B) h hab

theorem bar8 (A : Set ℕ) (h: Fintype ↑A) :
    Fintype.card ↑(A) = (Set.toFinset A).card := (Set.toFinset_card A).symm

theorem baz (A B : Set ℕ) (hA : Fintype A) (hB : Fintype ↑B)
    (hd : Disjoint A B) :
    Fintype.card ↑(A ∪ B) = Fintype.card A + Fintype.card B := by
  sorry

theorem imo1987_q4_generalized (m : ℕ) :
    (¬∃ f : ℕ → ℕ, ∀ n, f (f n) = n + (2 * m + 1)) := by
  -- Informal solution by Sawa Pavlov, listed at
  -- https://artofproblemsolving.com/wiki/index.php/1987_IMO_Problems/Problem_4

  intro hf
  obtain ⟨f, hf⟩ := hf

  -- Note that f is injective, because if f(n) = f(m),
  -- then f(f(n)) = f(f(m)), so m = n.
  have f_injective : f.Injective := by
    intros n m hnm
    have hff : f (f n) = f (f m) := congrArg _ hnm
    have hfn := hf n
    have hfm := hf m
    rw[hff] at hfn
    rw[hfn, add_left_inj] at hfm
    exact hfm

  -- Let A := ℕ - f(ℕ) and B := f(A).
  let NN : Set ℕ := {_x | True}
  let A : Set ℕ := NN \ (f '' NN)
  let B : Set ℕ := f '' A

  -- We claim that B = f(ℕ) - f(f(ℕ)).
  have B_eq : B = f '' NN \ (f '' (f '' NN)) := by
    apply Set.eq_of_subset_of_subset
    · -- Obviously B is a subset of f(ℕ) and if k belongs to B,
      -- then it does not belong to f(f(ℕ)) since f is injective.
      intros b hb
      simp
      constructor
      · obtain ⟨b',hb1', hb2'⟩ := hb
        use b'
        exact hb2'
      · intro x hx
        obtain ⟨b',hb1', hb2'⟩ := hb
        obtain ⟨c, hc⟩ := hb1'
        rw[←hx] at hb2'
        have hfi := f_injective hb2'
        simp at hc
        exact (hc x hfi.symm).elim
    · -- Similarly, a member of f(f(ℕ)) cannot belong to B.
      intros x hx
      simp at hx
      obtain ⟨⟨y, hy⟩, hx2⟩ := hx
      use y
      constructor
      · simp
        intros z hz
        rw[← hz] at hy
        exact (hx2 z hy).elim
      · assumption

  -- A and B are disjoint and have union ℕ - f(f(ℕ)).
  have ab_disjoint : Disjoint A B := sorry

  have ab_union : A ∪ B = NN \ (f '' (f '' NN)) := by
    apply Set.eq_of_subset_of_subset
    · intros x hx
      cases hx with
      | inl hxa =>
        obtain ⟨y, hy⟩ := hxa
        simp
        intros x1 hx1
        simp at hy
        exact (hy (f x1) hx1).elim
      | inr hxb =>
        simp
        intros y hy
        simp at hxb
        obtain ⟨z, hz1, hz2⟩ := hxb
        rw[←hz2] at hy
        have hz3 := f_injective hy
        exact (hz1 y hz3).elim
    · intros x hx
      obtain ⟨hx, hx'⟩ := hx
      cases Classical.em (x ∈ A) with
      | inl hxa => exact Set.mem_union_left B hxa
      | inr hxna =>
        simp
        right
        simp at hxna
        obtain ⟨y, hy⟩ := hxna
        use y
        constructor
        · intros z hz
          rw[←hz] at hy
          simp at hx'
          exact (hx' z hy).elim
        · exact hy

  -- ... which is {0, 1, ... , 2 * m}.
  have ab_range : A ∪ B = {n | n < 2*m + 1} := by
    apply Set.eq_of_subset_of_subset
    · rw[ab_union]
      intros x hx
      simp at hx
      simp
      by_contra H
      push_neg at H
      have hz: ∃ z, x = (2 * m + 1) + z := exists_add_of_le H
      obtain ⟨z, hz⟩ := hz
      rw[hz] at hx
      have hzz := hx z
      rw[hf z] at hzz
      rw[add_comm] at hzz
      exact (hzz rfl).elim
    · rw[ab_union]
      intros x hx
      simp at hx
      simp
      intros y hy
      have hfy := hf y
      rw[hy] at hfy
      rw[hfy] at hx
      norm_num at hx

  -- But since f is injective they have the
  -- same number of elements, which is impossible since {0, 1, ... , 2 * m}
  -- has an odd number of elements.

  have ab_finite : Fintype ↑(A ∪ B) := by
    rw[ab_range]
    exact inferInstance--exact Set.fintypeIio _

  have h2 : Fintype.card ↑(A ∪ B) = 2 * m + 1 := by
    have hc := @Fintype.card_congr' ↑(A ∪ B)
                  {x | x < 2 * m + 1} _ _ (by rw[ab_range])
    rw[hc]
    simp only [Fintype.card_ofFinset, Finset.card_range]

  have a_finite := bar6 A B ab_finite
  have b_finite := bar7 A B ab_finite
  have h3 := bar1 A B a_finite b_finite ab_finite
  have ab_finite' := ab_finite
  have h4 := bar8 (A ∪ B) ab_finite
  rw[h4] at h2; clear h4
  rw[h3] at h2; clear h3
  have ab_disjoint' := bar0 a_finite b_finite ab_disjoint
  rw[baz' A.toFinset B.toFinset ab_disjoint'] at h2
  sorry

theorem imo1987_q4 : (¬∃ f : ℕ → ℕ, ∀ n, f (f n) = n + 1987) := by
  rw[show 1987 = (2 * 993 + 1) by norm_num]
  exact imo1987_q4_generalized 993
