import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Interval
import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.Ring

/-!
# International Mathematical Olympiad 1987, Problem 4

Prove that there is no function f : ℕ → ℕ such that f(f(n)) = n + 1987
for every n.
-/

namespace Imo1987Q4

theorem baz' (A B : Finset ℕ) (hd : Disjoint A B) :
    Finset.card (A ∪ B) = A.card + B.card := by
  rw[←Finset.disjUnion_eq_union A B hd]
  exact Finset.card_disjUnion A B hd

theorem bar0'' (A : Set ℕ) (B : Finset ℕ) (ha : Fintype A)
    (hd : B ⊆ A.toFinset) : B.toSet ⊆ A := by
  intros x hx
  rw[Finset.mem_coe] at hx
  exact Set.mem_toFinset.mp (hd hx)

theorem bar0 {A B : Set ℕ} (ha : Fintype A) (hb : Fintype B) (hd : Disjoint A B) :
    Disjoint A.toFinset B.toFinset := by
  intros C hCa hCb
  have hCa' : C.toSet ≤ A := bar0'' A C _ hCa
  have hCb' : C.toSet ≤ B := bar0'' B C _ hCb
  intros c hc
  exact (hd hCa' hCb' hc).elim

theorem subset_finite {A B : Set ℕ} (h : A ⊆ B) (hab : Finite ↑B) : Finite ↑A := by
  rw[Set.finite_coe_iff]
  rw[Set.finite_coe_iff] at hab
  exact Set.Finite.subset hab h

theorem bar5 {A B : Set ℕ} (h : A ⊆ B) (hab : Fintype ↑B) : Fintype ↑A := by
  exact @Fintype.ofFinite A (subset_finite h (Finite.of_fintype ↑B))

/--
More general version of the problem.
-/
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
  let NN : Set ℕ := Set.univ
  let A : Set ℕ := NN \ (f '' NN)
  let B : Set ℕ := f '' A

  have hid := Set.image_diff f_injective NN (f '' NN)
  rw[show f '' (NN \ f '' NN) = B by rfl] at hid

  -- A and B are disjoint and have union ℕ - f(f(ℕ)).
  have ab_disjoint : Disjoint A B := by
    intros _C hca hcb c hc
    have hcca := hca hc
    have hccb := hcb hc
    rw[Set.mem_diff] at hcca
    obtain ⟨_, hcaa⟩ := hcca
    rw[hid] at hccb
    exact (hcaa (Set.mem_of_mem_diff hccb)).elim

  have ab_union : A ∪ B = NN \ (f '' (f '' NN)) := by
    rw[hid]
    apply Set.eq_of_subset_of_subset
    · intros x hx
      cases hx with
      | inl hxa =>
        obtain ⟨_y, hy⟩ := hxa
        simp
        intros x1 hx1
        simp at hy
        exact (hy (f x1) hx1).elim
      | inr hxb =>
        simp
        intros y hy
        simp at hxb
        obtain ⟨_, hz2⟩ := hxb
        cases hz2 y hy
    · intros x hx
      obtain ⟨_hx, hx'⟩ := hx
      cases Classical.em (x ∈ A) with
      | inl hxa => exact Set.mem_union_left _ hxa
      | inr hxna =>
        simp
        right
        simp at hxna
        constructor
        · exact hxna
        · intros z hz
          simp at hx'
          exact (hx' z hz).elim

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
    rw[ab_range]; exact inferInstance

  have h2 : Fintype.card ↑(A ∪ B) = 2 * m + 1 := by
    have hc := @Fintype.card_congr' ↑(A ∪ B)
                  {x | x < 2 * m + 1} _ _ (by rw[ab_range])
    simp only [hc, Fintype.card_ofFinset, Finset.card_range]

  have a_finite := bar5 (Set.subset_union_left A B) ab_finite
  have b_finite := bar5 (Set.subset_union_right A B) ab_finite
  have h3 := @Set.toFinset_union ℕ A B _ a_finite b_finite ab_finite
  rw[←@Set.toFinset_card _ (A ∪ B) ab_finite] at h2
  rw[h3] at h2; clear h3
  have ab_disjoint' := bar0 a_finite b_finite ab_disjoint
  rw[baz' A.toFinset B.toFinset ab_disjoint'] at h2
  rw[Set.toFinset_card, Set.toFinset_card] at h2
  rw[Set.card_image_of_injective A f_injective] at h2
  ring_nf at h2
  have h4 := congrFun (congrArg HMod.hMod (f_injective (congrArg f h2))) 2
  norm_num at h4

theorem imo1987_q4 : (¬∃ f : ℕ → ℕ, ∀ n, f (f n) = n + 1987) := by
  rw[show 1987 = (2 * 993 + 1) by norm_num]
  exact imo1987_q4_generalized 993
