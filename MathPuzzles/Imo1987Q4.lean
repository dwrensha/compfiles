import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Interval
import Mathlib.Init.Set
import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.Linarith

/-!
# International Mathematical Olympiad 1987, Problem 4

Prove that there is no function f : ℕ → ℕ such that f(f(n)) = n + 1987
for every n.
-/

theorem imo1987_q4 : (¬∃ f : ℕ → ℕ, ∀ n, f (f n) = n + 1987) := by
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
    rw[hfn] at hfm
    simp at hfm
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

  -- ... which is {0, 1, 2, ... , 1986}.
  have ab_range : A ∪ B = {n | n < 1987} := by
    apply Set.eq_of_subset_of_subset
    · rw[ab_union]
      intros x hx
      simp at hx
      simp
      by_contra H
      push_neg at H
      have hz: ∃ z, x = 1987 + z := exists_add_of_le H
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
  -- same number of elements, which is impossible since {0, 1, ... , 1986}
  -- has an odd number of elements.

  have : @Fintype.card {x | x < 1987} (Set.fintypeIio _) = 1987 :=
    Nat.card_fintypeIio 1987

  sorry


  -- TODO: Set.univ does not seem to work as expected.
  --let A': Set ℕ := {x: ℕ | True}
  --let A'': Set ℕ := univ x -- sorryAx (Set ℕ) true
