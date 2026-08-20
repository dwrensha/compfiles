/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics] }

/-!
# USA Mathematical Olympiad 2008, Problem 5

Three nonnegative real numbers r₁, r₂, r₃ are written on a blackboard.
These numbers have the property that there exist integers a₁, a₂, a₃,
not all zero, satisfying a₁r₁ + a₂r₂ + a₃r₃ = 0. We are permitted to
perform the following operation: find two numbers x, y on the
blackboard with x ≤ y, then erase y and write y − x in its place.
Prove that after a finite number of such operations, we can end up
with at least one 0 on the blackboard.
-/

namespace Usa2008P5

/-- One legal operation of the game: choose two distinct positions `i` and `j`
with `r j ≤ r i`, erase the number `r i` and write `r i - r j` in its place. -/
abbrev Step (r r' : Fin 3 → ℝ) : Prop :=
  ∃ i j : Fin 3, i ≠ j ∧ r j ≤ r i ∧ r' = Function.update r i (r i - r j)

snip begin

-- This follows the solution in
-- https://web.evanchen.cc/exams/USAMO-2008-notes.pdf
--
-- The strategy has two phases. While no coefficient aᵢ is zero, one can always
-- make a legal move after which |a₁| + |a₂| + |a₃| strictly decreases
-- (`phase1_core`), so after finitely many moves some coefficient is zero,
-- say a₃ = 0. Then a₁r₁ + a₂r₂ = 0 with a₁, a₂ ≠ 0, so r₁ and r₂ have a
-- rational ratio, and the subtractive Euclidean algorithm on that pair
-- (`euclid`, `phase2`) produces a zero.

/-- The weight of a coefficient vector: the sum of the absolute values. -/
abbrev weight (a : Fin 3 → ℤ) : ℕ := ∑ l, (a l).natAbs

lemma insert_eq_univ {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ({i, j, k} : Finset (Fin 3)) = Finset.univ := by
  apply Finset.eq_univ_of_card
  rw [Finset.card_insert_of_notMem (by simp [hij, hik]),
    Finset.card_pair hjk, Fintype.card_fin]

lemma sum3 {α : Type*} [AddCommMonoid α] {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (f : Fin 3 → α) :
    ∑ l, f l = f i + f j + f k := by
  rw [← insert_eq_univ hij hik hjk,
    Finset.sum_insert (by simp [hij, hik]), Finset.sum_pair hjk, add_assoc]

lemma weight_eq_three {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (a : Fin 3 → ℤ) :
    weight a = (a i).natAbs + (a j).natAbs + (a k).natAbs :=
  sum3 hij hik hjk _

/-- One step of the first phase of the strategy: if `r k ≤ r i`, we may erase
`r i` writing `r i - r k`, and update the coefficients accordingly. The new
coefficients still give a zero-sum relation, are not all zero, and their weight
strictly decreases, provided that `(a k + a i).natAbs < (a k).natAbs`. -/
lemma move_lemma {r : Fin 3 → ℝ} {a : Fin 3 → ℤ} {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hnn : ∀ l, 0 ≤ r l) (hle : r k ≤ r i)
    (hsum : (a i : ℝ) * r i + (a j : ℝ) * r j + (a k : ℝ) * r k = 0)
    (hane : a i ≠ 0) (hdec : (a k + a i).natAbs < (a k).natAbs) :
    ∃ r' : Fin 3 → ℝ, Step r r' ∧ (∀ l, 0 ≤ r' l) ∧
      ∃ a' : Fin 3 → ℤ, a' ≠ 0 ∧
        (a' i : ℝ) * r' i + (a' j : ℝ) * r' j + (a' k : ℝ) * r' k = 0 ∧
        (a' i).natAbs + (a' j).natAbs + (a' k).natAbs <
          (a i).natAbs + (a j).natAbs + (a k).natAbs := by
  have e1 : Function.update a k (a k + a i) i = a i := Function.update_of_ne hik _ _
  have e2 : Function.update a k (a k + a i) j = a j := Function.update_of_ne hjk _ _
  have e3 : Function.update a k (a k + a i) k = a k + a i := Function.update_self _ _ _
  have f1 : Function.update r i (r i - r k) i = r i - r k := Function.update_self _ _ _
  have f2 : Function.update r i (r i - r k) j = r j := Function.update_of_ne hij.symm _ _
  have f3 : Function.update r i (r i - r k) k = r k := Function.update_of_ne hik.symm _ _
  refine ⟨Function.update r i (r i - r k), ⟨i, k, hik, hle, rfl⟩, ?_,
    Function.update a k (a k + a i), ?_, ?_, ?_⟩
  · intro l
    by_cases h : l = i
    · subst h
      rw [Function.update_self]
      exact sub_nonneg.mpr hle
    · rw [Function.update_of_ne h]
      exact hnn l
  · rw [Function.ne_iff]
    exact ⟨i, by simp only [e1, Pi.zero_apply]; exact hane⟩
  · rw [e1, e2, e3, f1, f2, f3]
    push_cast
    linarith [hsum]
  · rw [e1, e2, e3]
    exact add_lt_add_right hdec _

/-- The first phase of the strategy, under the normalization `0 < a i` where
`i` is the position of the largest number: there is always a legal move after
which the weight of the coefficients strictly decreases. -/
lemma phase1_pos {r : Fin 3 → ℝ} {a : Fin 3 → ℤ} {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hrj : r j < r i) (hrk : r k < r j) (hpos : ∀ l, 0 < r l)
    (hai : 0 < a i) (haj : a j ≠ 0) (hak : a k ≠ 0)
    (hsum : (a i : ℝ) * r i + (a j : ℝ) * r j + (a k : ℝ) * r k = 0) :
    ∃ r' : Fin 3 → ℝ, Step r r' ∧ (∀ l, 0 ≤ r' l) ∧
      ∃ a' : Fin 3 → ℤ, a' ≠ 0 ∧ (∑ l, (a' l : ℝ) * r' l = 0) ∧ weight a' < weight a := by
  rcases lt_or_gt_of_ne haj with hajl | hajr
  · -- Case `a j < 0`.
    rcases lt_or_gt_of_ne hak with hakl | hakr
    · -- Case `a k < 0`: one of the two moves must decrease the weight.
      rcases lt_or_ge |a i + a j| |a j| with hc | hc
      · -- The move erasing `r i` using `r j` decreases the weight.
        have hdec : (a j + a i).natAbs < (a j).natAbs := by
          rw [← Int.ofNat_lt, Int.natCast_natAbs, Int.natCast_natAbs, add_comm (a j) (a i)]
          exact hc
        obtain ⟨r', hs, hn, a', hane, hrel, hdec3⟩ :=
          move_lemma hik hij hjk.symm (fun l => (hpos l).le) (le_of_lt hrj)
            (by linarith [hsum]) (ne_of_gt hai) hdec
        refine ⟨r', hs, hn, a', hane, ?_, ?_⟩
        · rw [sum3 hik hij hjk.symm]
          exact hrel
        · rw [weight_eq_three hik hij hjk.symm a', weight_eq_three hik hij hjk.symm a]
          exact hdec3
      · rcases lt_or_ge |a i + a k| |a k| with hc2 | hc2
        · -- The move erasing `r i` using `r k` decreases the weight.
          have hdec : (a k + a i).natAbs < (a k).natAbs := by
            rw [← Int.ofNat_lt, Int.natCast_natAbs, Int.natCast_natAbs, add_comm (a k) (a i)]
            exact hc2
          obtain ⟨r', hs, hn, a', hane, hrel, hdec3⟩ :=
            move_lemma hij hik hjk (fun l => (hpos l).le) (le_of_lt (lt_trans hrk hrj))
              hsum (ne_of_gt hai) hdec
          refine ⟨r', hs, hn, a', hane, ?_, ?_⟩
          · rw [sum3 hij hik hjk]
            exact hrel
          · rw [weight_eq_three hij hik hjk a', weight_eq_three hij hik hjk a]
            exact hdec3
        · -- Neither move decreases the weight: contradiction.
          exfalso
          have hpos1 : 0 < a i + a j := by
            rcases lt_trichotomy (a i + a j) 0 with h0 | h0 | h0
            · exfalso
              rw [abs_of_neg h0, abs_of_neg hajl] at hc
              lia
            · exfalso
              rw [h0, abs_zero] at hc
              have e2 : |a j| = -(a j) := abs_of_neg hajl
              lia
            · exact h0
          have hpos2 : 0 < a i + a k := by
            rcases lt_trichotomy (a i + a k) 0 with h0 | h0 | h0
            · exfalso
              rw [abs_of_neg h0, abs_of_neg hakl] at hc2
              lia
            · exfalso
              rw [h0, abs_zero] at hc2
              have e2 : |a k| = -(a k) := abs_of_neg hakl
              lia
            · exact h0
          have h3 : a i + 2 * a j ≥ 0 := by
            rw [abs_of_pos hpos1, abs_of_neg hajl] at hc
            lia
          have h4 : a i + 2 * a k ≥ 0 := by
            rw [abs_of_pos hpos2, abs_of_neg hakl] at hc2
            lia
          have h5 : 0 ≤ a i + a j + a k := by lia
          have h6 : ((a i : ℝ) + (a j : ℝ) + (a k : ℝ)) * r j < 0 := by
            have haiR : (0:ℝ) < a i := by exact_mod_cast hai
            have hakR : (a k : ℝ) < 0 := by exact_mod_cast hakl
            have e1 : (a i : ℝ) * r j < (a i : ℝ) * r i := mul_lt_mul_of_pos_left hrj haiR
            have e2 : (a k : ℝ) * r j < (a k : ℝ) * r k := mul_lt_mul_of_neg_left hrk hakR
            rw [add_mul, add_mul]
            linarith [hsum, e1, e2]
          have h7 : (a i : ℝ) + (a j : ℝ) + (a k : ℝ) < 0 :=
            neg_of_mul_neg_left h6 (hpos j).le
          have h5R : (0:ℝ) ≤ (a i : ℝ) + (a j : ℝ) + (a k : ℝ) := by exact_mod_cast h5
          linarith [h7, h5R]
    · -- Case `0 < a k`: the move erasing `r i` using `r j` decreases the weight.
      have hkey : a i + a j < 0 := by
        have haiR : (0:ℝ) < a i := by exact_mod_cast hai
        have e1 : (a i : ℝ) * r j < (a i : ℝ) * r i := mul_lt_mul_of_pos_left hrj haiR
        have e2 : (0:ℝ) < (a k : ℝ) * r k := mul_pos (by exact_mod_cast hakr) (hpos k)
        have e3 : ((a i : ℝ) + (a j : ℝ)) * r j < 0 := by
          rw [add_mul]
          linarith [hsum, e1, e2]
        have e4 := neg_of_mul_neg_left e3 (hpos j).le
        exact_mod_cast e4
      have hdec : (a j + a i).natAbs < (a j).natAbs := by
        rw [← Int.ofNat_lt, Int.natCast_natAbs, Int.natCast_natAbs,
          abs_of_neg (show a j + a i < 0 by lia), abs_of_neg hajl]
        lia
      obtain ⟨r', hs, hn, a', hane, hrel, hdec3⟩ :=
        move_lemma hik hij hjk.symm (fun l => (hpos l).le) (le_of_lt hrj)
          (by linarith [hsum]) (ne_of_gt hai) hdec
      refine ⟨r', hs, hn, a', hane, ?_, ?_⟩
      · rw [sum3 hik hij hjk.symm]
        exact hrel
      · rw [weight_eq_three hik hij hjk.symm a', weight_eq_three hik hij hjk.symm a]
        exact hdec3
  · -- Case `0 < a j`: then `a k < 0` and erasing `r i` using `r k` decreases the weight.
    have hakl : a k < 0 := by
      rcases lt_or_gt_of_ne hak with h | h
      · exact h
      · exfalso
        have e1 : (0:ℝ) < (a i : ℝ) * r i := mul_pos (by exact_mod_cast hai) (hpos i)
        have e2 : (0:ℝ) < (a j : ℝ) * r j := mul_pos (by exact_mod_cast hajr) (hpos j)
        have e3 : (0:ℝ) < (a k : ℝ) * r k := mul_pos (by exact_mod_cast h) (hpos k)
        linarith [hsum]
    have hkey : a i + a k < 0 := by
      have haiR : (0:ℝ) < a i := by exact_mod_cast hai
      have e1 : (a i : ℝ) * r k < (a i : ℝ) * r i :=
        mul_lt_mul_of_pos_left (lt_trans hrk hrj) haiR
      have e2 : (0:ℝ) < (a j : ℝ) * r j := mul_pos (by exact_mod_cast hajr) (hpos j)
      have e3 : ((a i : ℝ) + (a k : ℝ)) * r k < 0 := by
        rw [add_mul]
        linarith [hsum, e1, e2]
      have e4 := neg_of_mul_neg_left e3 (hpos k).le
      exact_mod_cast e4
    have hdec : (a k + a i).natAbs < (a k).natAbs := by
      rw [← Int.ofNat_lt, Int.natCast_natAbs, Int.natCast_natAbs,
        abs_of_neg (show a k + a i < 0 by lia), abs_of_neg hakl]
      lia
    obtain ⟨r', hs, hn, a', hane, hrel, hdec3⟩ :=
      move_lemma hij hik hjk (fun l => (hpos l).le) (le_of_lt (lt_trans hrk hrj))
        hsum (ne_of_gt hai) hdec
    refine ⟨r', hs, hn, a', hane, ?_, ?_⟩
    · rw [sum3 hij hik hjk]
      exact hrel
    · rw [weight_eq_three hij hik hjk a', weight_eq_three hij hik hjk a]
      exact hdec3

/-- The first phase of the strategy: as long as no coefficient is zero, there
is a legal move after which the weight of the coefficients strictly decreases. -/
lemma phase1_core {r : Fin 3 → ℝ} {a : Fin 3 → ℤ} {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hrj : r j < r i) (hrk : r k < r j) (hpos : ∀ l, 0 < r l)
    (hai : a i ≠ 0) (haj : a j ≠ 0) (hak : a k ≠ 0)
    (hsum : (a i : ℝ) * r i + (a j : ℝ) * r j + (a k : ℝ) * r k = 0) :
    ∃ r' : Fin 3 → ℝ, Step r r' ∧ (∀ l, 0 ≤ r' l) ∧
      ∃ a' : Fin 3 → ℤ, a' ≠ 0 ∧ (∑ l, (a' l : ℝ) * r' l = 0) ∧ weight a' < weight a := by
  rcases lt_or_gt_of_ne hai with h | h
  · -- If `a i < 0`, apply the normalized version to `-a`.
    have hsum' : ((-a) i : ℝ) * r i + ((-a) j : ℝ) * r j + ((-a) k : ℝ) * r k = 0 := by
      simp only [Pi.neg_apply, Int.cast_neg]
      linarith [hsum]
    obtain ⟨r', hs, hn, a', hane, hrel, hdec⟩ :=
      phase1_pos hij hik hjk hrj hrk hpos (neg_pos.mpr h)
        (neg_ne_zero.mpr haj) (neg_ne_zero.mpr hak) hsum'
    have hSa : weight (-a) = weight a := by
      apply Finset.sum_congr rfl
      intro l _
      simp only [Pi.neg_apply, Int.natAbs_neg]
    have hdec' : weight a' < weight a := by rwa [hSa] at hdec
    exact ⟨r', hs, hn, a', hane, hrel, hdec'⟩
  · exact phase1_pos hij hik hjk hrj hrk hpos h haj hak hsum

/-- The subtractive Euclidean algorithm on one pair of positions. If the values
at positions `i` and `j` are positive integer multiples `p * t` and `q * t` of a
common positive real `t`, then by repeatedly erasing the larger of the two we
can reach a board containing `0`. -/
lemma euclid : ∀ n : ℕ, ∀ (r : Fin 3 → ℝ) (t : ℝ) (i j : Fin 3) (p q : ℕ),
    p + q = n → (∀ l, 0 ≤ r l) → 0 < t → i ≠ j → 0 < p → 0 < q →
    r i = (p : ℝ) * t → r j = (q : ℝ) * t →
    ∃ r' : Fin 3 → ℝ, Relation.ReflTransGen Step r r' ∧ ∃ l, r' l = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro r t i j p q hpq hnn ht hij hp hq hi hj
    rcases lt_trichotomy p q with h | h | h
    · -- `p < q`: erase `r j = q * t` using `r i = p * t`, recurse on `(p, q - p)`.
      have hle : r i ≤ r j := by
        rw [hi, hj]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast h.le : (p:ℝ) ≤ (q:ℝ)) ht.le
      set r' := Function.update r j (r j - r i) with hr'
      have hstep : Step r r' := ⟨j, i, hij.symm, hle, rfl⟩
      have hnn' : ∀ l, 0 ≤ r' l := by
        intro l
        by_cases hjl : l = j
        · subst hjl
          rw [hr', Function.update_self]
          exact sub_nonneg.mpr hle
        · rw [hr', Function.update_of_ne hjl]
          exact hnn l
      have hqj : 0 < q - p := Nat.sub_pos_of_lt h
      have hrj' : r' j = ((q - p : ℕ) : ℝ) * t := by
        rw [hr', Function.update_self, hj, hi, Nat.cast_sub h.le]
        ring
      have hri' : r' i = (p : ℝ) * t := by
        rw [hr', Function.update_of_ne hij]
        exact hi
      obtain ⟨r'', hreach, l, hl⟩ :=
        IH q (hpq ▸ Nat.lt_add_of_pos_left hp) r' t i j p (q - p) (Nat.add_sub_of_le h.le)
          hnn' ht hij hp hqj hri' hrj'
      exact ⟨r'', Relation.ReflTransGen.trans (Relation.ReflTransGen.single hstep) hreach, l, hl⟩
    · -- `p = q`: the two values are equal, so one move produces `0`.
      refine ⟨Function.update r i (r i - r j),
        Relation.ReflTransGen.single ⟨i, j, hij, le_of_eq (by rw [hi, hj, h]), rfl⟩, i, ?_⟩
      rw [Function.update_self, hi, hj, h, sub_self]
    · -- `q < p`: erase `r i = p * t` using `r j = q * t`, recurse on `(p - q, q)`.
      have hle : r j ≤ r i := by
        rw [hi, hj]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast h.le : (q:ℝ) ≤ (p:ℝ)) ht.le
      set r' := Function.update r i (r i - r j) with hr'
      have hstep : Step r r' := ⟨i, j, hij, hle, rfl⟩
      have hnn' : ∀ l, 0 ≤ r' l := by
        intro l
        by_cases hil : l = i
        · subst hil
          rw [hr', Function.update_self]
          exact sub_nonneg.mpr hle
        · rw [hr', Function.update_of_ne hil]
          exact hnn l
      have hpi : 0 < p - q := Nat.sub_pos_of_lt h
      have hri' : r' i = ((p - q : ℕ) : ℝ) * t := by
        rw [hr', Function.update_self, hi, hj, Nat.cast_sub h.le]
        ring
      have hrj' : r' j = (q : ℝ) * t := by
        rw [hr', Function.update_of_ne hij.symm]
        exact hj
      obtain ⟨r'', hreach, l, hl⟩ :=
        IH p (hpq ▸ Nat.lt_add_of_pos_right hq) r' t i j (p - q) q (Nat.sub_add_cancel h.le)
          hnn' ht hij hpi hq hri' hrj'
      exact ⟨r'', Relation.ReflTransGen.trans (Relation.ReflTransGen.single hstep) hreach, l, hl⟩

/-- The second phase of the strategy: if some coefficient is zero, then the
other two coefficients are nonzero and the corresponding numbers have a
rational ratio, so the Euclidean algorithm finishes the game. -/
lemma phase2 {r : Fin 3 → ℝ} {a : Fin 3 → ℤ} {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hpos : ∀ l, 0 < r l) (ha : a ≠ 0) (hak : a k = 0)
    (hsum : (a i : ℝ) * r i + (a j : ℝ) * r j + (a k : ℝ) * r k = 0) :
    ∃ r' : Fin 3 → ℝ, Relation.ReflTransGen Step r r' ∧ ∃ l, r' l = 0 := by
  rw [hak, Int.cast_zero, zero_mul, add_zero] at hsum
  have hcov : ∀ l : Fin 3, l = i ∨ l = j ∨ l = k := by
    intro l
    have hmem : l ∈ ({i, j, k} : Finset (Fin 3)) := by
      rw [insert_eq_univ hij hik hjk]
      exact Finset.mem_univ l
    simpa using hmem
  have hai : a i ≠ 0 := by
    intro hi0
    rw [hi0, Int.cast_zero, zero_mul, zero_add] at hsum
    rcases mul_eq_zero.mp hsum with h1 | h1
    · apply ha
      ext l
      rcases hcov l with rfl | rfl | rfl
      · exact hi0
      · exact Int.cast_eq_zero.mp h1
      · exact hak
    · exact absurd h1 (ne_of_gt (hpos j))
  have haj : a j ≠ 0 := by
    intro hj0
    rw [hj0, Int.cast_zero, zero_mul, add_zero] at hsum
    rcases mul_eq_zero.mp hsum with h1 | h1
    · apply ha
      ext l
      rcases hcov l with rfl | rfl | rfl
      · exact Int.cast_eq_zero.mp h1
      · exact hj0
      · exact hak
    · exact absurd h1 (ne_of_gt (hpos i))
  -- Set `p = |a i|` and `q = |a j|`; then `p * r i = q * r j`.
  set p := (a i).natAbs with hp
  set q := (a j).natAbs with hq
  have hp0 : 0 < p := Int.natAbs_pos.mpr hai
  have hq0 : 0 < q := Int.natAbs_pos.mpr haj
  have hpq : (p : ℝ) * r i = (q : ℝ) * r j := by
    rcases lt_or_gt_of_ne hai with h | h
    · -- `a i < 0`, hence `0 < a j`.
      have haj' : 0 < a j := by
        have h1 : (0:ℝ) < (a j : ℝ) * r j := by
          have h2 : (a i : ℝ) * r i < 0 := mul_neg_of_neg_of_pos (by exact_mod_cast h) (hpos i)
          linarith [hsum]
        rcases mul_pos_iff.mp h1 with h2 | h2
        · exact_mod_cast h2.1
        · exact absurd h2.2 (not_lt_of_ge (hpos j).le)
      have hpR : (p : ℝ) = -(a i : ℝ) := by
        rw [hp, ← Int.cast_natCast, Int.natCast_natAbs, abs_of_neg h, Int.cast_neg]
      have hqR : (q : ℝ) = (a j : ℝ) := by
        rw [hq, ← Int.cast_natCast, Int.natCast_natAbs, abs_of_pos haj']
      rw [hpR, hqR]
      linarith [hsum]
    · -- `0 < a i`, hence `a j < 0`.
      have haj' : a j < 0 := by
        have h1 : (a j : ℝ) * r j < 0 := by
          have h2 : (0:ℝ) < (a i : ℝ) * r i := mul_pos (by exact_mod_cast h) (hpos i)
          linarith [hsum]
        rcases mul_neg_iff.mp h1 with h2 | h2
        · exact absurd h2.2 (not_lt_of_ge (hpos j).le)
        · exact_mod_cast h2.1
      have hpR : (p : ℝ) = (a i : ℝ) := by
        rw [hp, ← Int.cast_natCast, Int.natCast_natAbs, abs_of_pos h]
      have hqR : (q : ℝ) = -(a j : ℝ) := by
        rw [hq, ← Int.cast_natCast, Int.natCast_natAbs, abs_of_neg haj', Int.cast_neg]
      rw [hpR, hqR]
      linarith [hsum]
  -- With `t = r j / p` we have `r i = q * t` and `r j = p * t`.
  set t := r j / (p : ℝ) with ht
  have htp : 0 < t := div_pos (hpos j) (by exact_mod_cast hp0)
  have hpne : (p : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hp0)
  have hpt : (p : ℝ) * t = r j := by
    rw [ht]
    exact mul_div_cancel₀ _ hpne
  have hri_eq : r i = (q : ℝ) * t := by
    apply mul_left_cancel₀ hpne
    calc (p : ℝ) * r i = (q : ℝ) * r j := hpq
    _ = (q : ℝ) * ((p : ℝ) * t) := by rw [← hpt]
    _ = (p : ℝ) * ((q : ℝ) * t) := by ring
  exact euclid (q + p) r t i j q p rfl (fun l => (hpos l).le) htp hij hq0 hp0 hri_eq hpt.symm

/-- The key lemma, proved by strong induction on the weight of the coefficient
vector: one can always reach a board containing `0`. -/
lemma key : ∀ n : ℕ, ∀ (r : Fin 3 → ℝ) (a : Fin 3 → ℤ),
    weight a = n → (∀ l, 0 ≤ r l) → a ≠ 0 → (∑ l, (a l : ℝ) * r l) = 0 →
    ∃ r' : Fin 3 → ℝ, Relation.ReflTransGen Step r r' ∧ ∃ l, r' l = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro r a hSn hnn ha hsum
    by_cases hz : ∃ l, r l = 0
    · -- A zero is already on the board.
      obtain ⟨l, hl⟩ := hz
      exact ⟨r, Relation.ReflTransGen.refl, l, hl⟩
    · by_cases heq : ∃ i j, i ≠ j ∧ r i = r j
      · -- Two equal numbers produce a zero in one move.
        obtain ⟨u, v, huv, huv2⟩ := heq
        refine ⟨Function.update r u (r u - r v),
          Relation.ReflTransGen.single ⟨u, v, huv, le_of_eq huv2.symm, rfl⟩, u, ?_⟩
        rw [Function.update_self, huv2, sub_self]
      · push Not at hz
        push Not at heq
        have hpos : ∀ l, 0 < r l := fun l => lt_of_le_of_ne' (hnn l) (hz l)
        by_cases haz : ∃ l, a l = 0
        · -- Some coefficient is zero: the Euclidean algorithm finishes.
          obtain ⟨k, hk⟩ := haz
          fin_cases k
          · have hsum3 : (a 1 : ℝ) * r 1 + (a 2 : ℝ) * r 2 + (a 0 : ℝ) * r 0 = 0 := by
              rw [sum3 (show (1 : Fin 3) ≠ 2 by decide) (show (1 : Fin 3) ≠ 0 by decide)
                (show (2 : Fin 3) ≠ 0 by decide)] at hsum
              exact hsum
            exact phase2 (show (1 : Fin 3) ≠ 2 by decide) (show (1 : Fin 3) ≠ 0 by decide)
              (show (2 : Fin 3) ≠ 0 by decide) hpos ha hk hsum3
          · have hsum3 : (a 0 : ℝ) * r 0 + (a 2 : ℝ) * r 2 + (a 1 : ℝ) * r 1 = 0 := by
              rw [sum3 (show (0 : Fin 3) ≠ 2 by decide) (show (0 : Fin 3) ≠ 1 by decide)
                (show (2 : Fin 3) ≠ 1 by decide)] at hsum
              exact hsum
            exact phase2 (show (0 : Fin 3) ≠ 2 by decide) (show (0 : Fin 3) ≠ 1 by decide)
              (show (2 : Fin 3) ≠ 1 by decide) hpos ha hk hsum3
          · have hsum3 : (a 0 : ℝ) * r 0 + (a 1 : ℝ) * r 1 + (a 2 : ℝ) * r 2 = 0 := by
              rw [sum3 (show (0 : Fin 3) ≠ 1 by decide) (show (0 : Fin 3) ≠ 2 by decide)
                (show (1 : Fin 3) ≠ 2 by decide)] at hsum
              exact hsum
            exact phase2 (show (0 : Fin 3) ≠ 1 by decide) (show (0 : Fin 3) ≠ 2 by decide)
              (show (1 : Fin 3) ≠ 2 by decide) hpos ha hk hsum3
        · -- No coefficient is zero: decrease the weight and apply the induction hypothesis.
          push Not at haz
          have finish : ∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k → r j < r i → r k < r j →
              ∃ r' : Fin 3 → ℝ, Relation.ReflTransGen Step r r' ∧ ∃ l, r' l = 0 := by
            intro i j k hij hik hjk hrj hrk
            have hsum3 : (a i : ℝ) * r i + (a j : ℝ) * r j + (a k : ℝ) * r k = 0 := by
              rw [sum3 hij hik hjk] at hsum
              exact hsum
            obtain ⟨r', hstep, hnn', a', ha', hsum', hdec⟩ :=
              phase1_core hij hik hjk hrj hrk hpos (haz i) (haz j) (haz k) hsum3
            have hSn' : weight a' < n := by
              rw [← hSn]
              exact hdec
            obtain ⟨r'', hreach, l, hl⟩ := IH (weight a') hSn' r' a' rfl hnn' ha' hsum'
            exact ⟨r'', Relation.ReflTransGen.trans
              (Relation.ReflTransGen.single hstep) hreach, l, hl⟩
          have d01 : r 0 ≠ r 1 := heq 0 1 (by decide)
          have d02 : r 0 ≠ r 2 := heq 0 2 (by decide)
          have d12 : r 1 ≠ r 2 := heq 1 2 (by decide)
          rcases lt_or_gt_of_ne d01 with h01 | h01
          · rcases lt_or_gt_of_ne d12 with h12 | h12
            · -- `r 0 < r 1 < r 2`
              exact finish 2 1 0 (by decide) (by decide) (by decide) h12 h01
            · rcases lt_or_gt_of_ne d02 with h02 | h02
              · -- `r 0 < r 2 < r 1`
                exact finish 1 2 0 (by decide) (by decide) (by decide) h12 h02
              · -- `r 2 < r 0 < r 1`
                exact finish 1 0 2 (by decide) (by decide) (by decide) h01 h02
          · rcases lt_or_gt_of_ne d12 with h12 | h12
            · rcases lt_or_gt_of_ne d02 with h02 | h02
              · -- `r 1 < r 0 < r 2`
                exact finish 2 0 1 (by decide) (by decide) (by decide) h02 h01
              · -- `r 1 < r 2 < r 0`
                exact finish 0 2 1 (by decide) (by decide) (by decide) h02 h12
            · -- `r 2 < r 1 < r 0`
              exact finish 0 1 2 (by decide) (by decide) (by decide) h01 h12

snip end

problem usa2008_p5 (r : Fin 3 → ℝ) (hr : ∀ i, 0 ≤ r i)
    (a : Fin 3 → ℤ) (ha : a ≠ 0) (hsum : ∑ i, (a i : ℝ) * r i = 0) :
    ∃ r' : Fin 3 → ℝ, Relation.ReflTransGen Step r r' ∧ ∃ i, r' i = 0 :=
  key (weight a) r a rfl hr ha hsum

end Usa2008P5
