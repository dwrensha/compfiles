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
# International Mathematical Olympiad 1979, Problem 2

A prism with pentagons $A_1A_2A_3A_4A_5$ and $B_1B_2B_3B_4B_5$ as the top and
bottom faces is given. Each side of the two pentagons and each of the 25
segments $A_iB_j$ is colored red or green. Every triangle whose vertices are
vertices of the prism and whose sides have all been colored has two sides of
a different color. Prove that all 10 sides of the top and bottom faces have
the same color.
-/

namespace Imo1979P2

snip begin

/-- In a two-element palette, any two elements that both differ from a third
element are equal. -/
lemma eq_of_ne_of_ne : ∀ x y z : Bool, x ≠ z → y ≠ z → x = y := by decide

/-- In a two-element palette, any element equals one of two distinct elements. -/
lemma eq_or_eq_of_ne : ∀ x y z : Bool, x ≠ y → z = x ∨ z = y := by decide

/-- Among five booleans, some three (at pairwise distinct positions) coincide. -/
lemma three_eq_of_five :
    ∀ f : Fin 5 → Bool, ∃ i j k : Fin 5,
      i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ f i = f j ∧ f j = f k := by
  decide

/-- Any three pairwise distinct elements of `Fin 5` contain two that are
cyclically adjacent, i.e. of the form `m, m + 1`. -/
lemma adjacent_of_three :
    ∀ i j k : Fin 5, i ≠ j → i ≠ k → j ≠ k →
      ∃ m : Fin 5, (m = i ∨ m = j ∨ m = k) ∧ (m + 1 = i ∨ m + 1 = j ∨ m + 1 = k) := by
  decide

/-- Two three-element subsets of the five-element set intersect. -/
lemma inter_of_three :
    ∀ i j k i' j' k' : Fin 5,
      (i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ i' ≠ j' ∧ i' ≠ k' ∧ j' ≠ k') →
      ∃ q : Fin 5, (q = i ∨ q = j ∨ q = k) ∧ (q = i' ∨ q = j' ∨ q = k') := by
  decide

/-- If all cyclically adjacent values of a `Fin 5 → Bool` are equal,
then all its values are equal. -/
lemma all_eq_of_cycle :
    ∀ f : Fin 5 → Bool, (∀ i, f i = f (i + 1)) → ∀ i, f i = f 0 := by
  decide

/-- Key lemma. Consider two pentagons `P` and `Q` with edge colors `e` and `g`
(`e p` being the color of the side `P_pP_{p+1}`, indices taken modulo 5) and
cross edges `d` (`d p q` the color of the segment `P_pQ_q`), such that no
triangle with all sides colored is monochromatic. Then all sides of `P` have
the same color. -/
lemma one_color (e g : Fin 5 → Bool) (d : Fin 5 → Fin 5 → Bool)
    (he : ∀ p q : Fin 5, ¬ (e p = d p q ∧ d p q = d (p + 1) q))
    (hg : ∀ q p : Fin 5, ¬ (g q = d p q ∧ d p q = d p (q + 1))) :
    ∀ p : Fin 5, e p = e 0 := by
  by_contra hne
  obtain ⟨p, hp⟩ : ∃ p, e p ≠ e (p + 1) := by
    by_contra hcon
    exact hne (all_eq_of_cycle e fun p ↦ not_ne_iff.mp (not_exists.mp hcon p))
  -- `P_{p+1}` is a vertex incident to two differently colored sides.
  obtain ⟨i, j, k, hij, hik, hjk, h1, h2⟩ := three_eq_of_five (d (p + 1))
  have hv : ∀ t : Fin 5, (t = i ∨ t = j ∨ t = k) → d (p + 1) t = d (p + 1) i := by
    intro t ht
    rcases ht with rfl | rfl | rfl
    · rfl
    · exact h1.symm
    · exact h2.symm.trans h1.symm
  -- Given a vertex `Q_w` whose edges to `Q_i`, `Q_j`, `Q_k` all differ from
  -- the common color `d (p+1) i`, we reach a contradiction.
  have finish : ∀ w : Fin 5,
      (∀ t : Fin 5, (t = i ∨ t = j ∨ t = k) → d w t ≠ d (p + 1) i) → False := by
    intro w hw
    obtain ⟨m, hm, hm1⟩ := adjacent_of_three i j k hij hik hjk
    have hvm := hv m hm
    have hvm1 := hv (m + 1) hm1
    have hgm : g m ≠ d (p + 1) i :=
      fun hgm' ↦ hg m (p + 1) ⟨hgm'.trans hvm.symm, hvm.trans hvm1.symm⟩
    have hwm := hw m hm
    have hwm1 := hw (m + 1) hm1
    exact hg m w ⟨eq_of_ne_of_ne _ _ _ hgm hwm, eq_of_ne_of_ne _ _ _ hwm hwm1⟩
  -- The common color `d (p+1) i` equals one of the two differently colored
  -- sides `e p`, `e (p+1)` at `P_{p+1}`.
  rcases eq_or_eq_of_ne _ _ _ hp with hγ | hγ
  · -- Case `d (p+1) i = e p`: take `w = p`.
    exact finish p fun t ht htγ ↦
      he p t ⟨hγ.symm.trans htγ.symm, htγ.trans (hv t ht).symm⟩
  · -- Case `d (p+1) i = e (p+1)`: take `w = p + 2`.
    exact finish (p + 1 + 1) fun t ht htγ ↦
      he (p + 1) t ⟨hγ.symm.trans (hv t ht).symm, (hv t ht).trans htγ.symm⟩

snip end

problem imo1979_p2 (a b : Fin 5 → Bool) (c : Fin 5 → Fin 5 → Bool)
    (ha : ∀ i j : Fin 5, ¬ (a i = c i j ∧ c i j = c (i + 1) j))
    (hb : ∀ i j : Fin 5, ¬ (b j = c i j ∧ c i j = c i (j + 1))) :
    ∃ col : Bool, (∀ i : Fin 5, a i = col) ∧ (∀ i : Fin 5, b i = col) := by
  -- All sides of the top pentagon have the same color, and similarly
  -- for the bottom pentagon.
  have ha_all : ∀ i : Fin 5, a i = a 0 := one_color a b c ha fun q p ↦ hb p q
  have hb_all : ∀ i : Fin 5, b i = b 0 :=
    one_color b a (fun p q ↦ c q p) (fun p q ↦ hb q p) ha
  -- It remains to show that the two common colors coincide.
  have hab : a 0 = b 0 := by
    by_contra hne
    obtain ⟨i, j, k, hij, hik, hjk, h1, h2⟩ := three_eq_of_five (c 0)
    have hv0 : ∀ t : Fin 5, (t = i ∨ t = j ∨ t = k) → c 0 t = c 0 i := by
      intro t ht
      rcases ht with rfl | rfl | rfl
      · rfl
      · exact h1.symm
      · exact h2.symm.trans h1.symm
    -- The common color of the three edges `c 0 i, c 0 j, c 0 k` cannot be `b 0`:
    -- two of `B_i, B_j, B_k` are adjacent, giving a monochromatic triangle.
    have hγ0 : c 0 i ≠ b 0 := by
      intro hγb
      obtain ⟨m, hm, hm1⟩ := adjacent_of_three i j k hij hik hjk
      exact hb 0 m ⟨(hb_all m).trans (hγb.symm.trans (hv0 m hm).symm),
        (hv0 m hm).trans (hv0 (m + 1) hm1).symm⟩
    have hγa : c 0 i = a 0 := eq_of_ne_of_ne _ _ _ hγ0 hne
    obtain ⟨i', j', k', hij', hik', hjk', h1', h2'⟩ := three_eq_of_five (c 1)
    have hv1 : ∀ t : Fin 5, (t = i' ∨ t = j' ∨ t = k') → c 1 t = c 1 i' := by
      intro t ht
      rcases ht with rfl | rfl | rfl
      · rfl
      · exact h1'.symm
      · exact h2'.symm.trans h1'.symm
    have hγ0' : c 1 i' ≠ b 0 := by
      intro hγb
      obtain ⟨m, hm, hm1⟩ := adjacent_of_three i' j' k' hij' hik' hjk'
      exact hb 1 m ⟨(hb_all m).trans (hγb.symm.trans (hv1 m hm).symm),
        (hv1 m hm).trans (hv1 (m + 1) hm1).symm⟩
    have hγa' : c 1 i' = a 0 := eq_of_ne_of_ne _ _ _ hγ0' hne
    -- The two three-element sets of indices intersect in some `q`, and then
    -- the triangle `A_0A_1B_q` is monochromatic: a contradiction.
    obtain ⟨q, hq, hq'⟩ :=
      inter_of_three i j k i' j' k' ⟨hij, hik, hjk, hij', hik', hjk'⟩
    have hc0q : c 0 q = a 0 := (hv0 q hq).trans hγa
    have hc1q : c 1 q = a 0 := (hv1 q hq').trans hγa'
    exact ha 0 q ⟨hc0q.symm, hc0q.trans hc1q.symm⟩
  exact ⟨a 0, ha_all, fun i ↦ (hb_all i).trans hab.symm⟩

end Imo1979P2
