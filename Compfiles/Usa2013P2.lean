/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.Ring
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics] }

/-!
# USA Mathematical Olympiad 2013, Problem 2

For a positive integer $n \ge 3$ plot $n$ equally spaced points around a circle.
Label one of them $A$, and place a marker at $A$. One may move the marker forward
in a clockwise direction to either the next point or the point after that. Hence
there are a total of $2n$ distinct moves available; two from each point. Let $a_n$
count the number of ways to advance around the circle exactly twice, beginning and
ending at $A$, without repeating a move. Prove that $a_{n-1} + a_n = 2^n$ for all
$n \ge 4$.
-/

namespace Usa2013P2

/-!
## Setting up the count

We unroll the two trips around the circle into the integer interval
`{0, 1, …, 2n}`: a path becomes a walk from `0` to `2n` in steps of size `1` or
`2`, and a *move* is a pair (starting point mod `n`, step length). Recording, for
each `i ∈ {0, …, 2n}`, whether the walk visits `i` yields a `2 × (n+1)` zero-one
matrix

```
[ p₀   p₁   …  p_{n-1}  p_n   ]
[ p_n  p_{n+1} … p_{2n-1} p_{2n} ]
```

with `p₀ = p_{2n} = 1`. The conditions of the problem translate as follows:
* steps have size at most `2` iff no two horizontally adjacent entries are both `0`;
* no repeated move of length `2` iff no column is `(0,0)` (points `i` and `i+n`
  are both skipped exactly when the same length-2 move is used twice);
* no repeated move of length `1` iff no two adjacent columns are both `(1,1)`
  (points `i, i+1, i+n, i+n+1` are all visited exactly when the same length-1
  move is used twice).

Conversely every such matrix determines a unique valid path, so `a_n` counts
these matrices. Each column is one of `u = (1,0)`, `v = (0,1)`, `w = (1,1)`
(encoded as `0, 1, 2 : Fin 3`), and the conditions say exactly that adjacent
columns are distinct, the first column is `u` or `w`, the last column is `v` or
`w`, and the first column is `w` iff the last one is. Sequences starting with
`u` must end in `v`, and sequences starting with `w` must end in `w`, giving
`a_n = x_n + y_n` below. We then follow the first solution in Evan Chen's
*USAMO 2013 Solution Notes*: by symmetry (`Fin 3` column relabeling) and the
"delete the last column" bijection one gets `x_{n+1} = x_n + y_n`,
`y_{n+1} = 2 * x_n` and `2 * x_n + y_n = 2^n`, hence
`a_{n+1} + a_n = 2 ^ (n+1)`.
-/

/-- A sequence of `n+1` columns, each column one of the three symbols of `Fin 3`
(`0 = u`, `1 = v`, `2 = w`). -/
abbrev ColSeq (n : ℕ) := Fin (n + 1) → Fin 3

/-- Adjacent columns are distinct. -/
abbrev AdjDistinct {n : ℕ} (c : ColSeq n) : Prop := ∀ i : Fin n, c i.castSucc ≠ c i.succ

/-- The number of column sequences of length `n+1` with distinct adjacent columns
starting with `s` and ending with `t`. -/
noncomputable def countCol (n : ℕ) (s t : Fin 3) : ℕ :=
  Nat.card {c : ColSeq n // AdjDistinct c ∧ c 0 = s ∧ c (Fin.last n) = t}

/-- The number of ways to advance around the circle exactly twice without
repeating a move: sequences starting with `u = 0` end in `v = 1`, and sequences
starting with `w = 2` end in `w = 2`. -/
noncomputable def a (n : ℕ) : ℕ := countCol n 0 1 + countCol n 2 2

snip begin

/-- Relabeling columns by a permutation of `Fin 3` does not change the counts. -/
def permEquiv {n : ℕ} (σ : Equiv.Perm (Fin 3)) (s t : Fin 3) :
    {c : ColSeq n // AdjDistinct c ∧ c 0 = s ∧ c (Fin.last n) = t} ≃
    {c : ColSeq n // AdjDistinct c ∧ c 0 = σ s ∧ c (Fin.last n) = σ t} where
  toFun c := ⟨σ ∘ c,
    fun i h => c.2.1 i (σ.injective h),
    by simp [Function.comp_apply, c.2.2.1],
    by simp [Function.comp_apply, c.2.2.2]⟩
  invFun c := ⟨σ.symm ∘ c,
    fun i h => c.2.1 i (σ.symm.injective h),
    by simp [Function.comp_apply, c.2.2.1],
    by simp [Function.comp_apply, c.2.2.2]⟩
  left_inv c := by
    ext i
    simp [Function.comp_apply]
  right_inv c := by
    ext i
    simp [Function.comp_apply]

/-- Swapping two column symbols does not change the counts. -/
theorem card_eq_swap {n : ℕ} (s t s' t' p q : Fin 3)
    (hs : Equiv.swap p q s = s') (ht : Equiv.swap p q t = t') :
    countCol n s t = countCol n s' t' := by
  unfold countCol
  rw [← hs, ← ht]
  exact Nat.card_congr (permEquiv (Equiv.swap p q) s t)

/-- Deleting the last column: sequences of length `n+2` ending in `t` correspond
to sequences of length `n+1` ending in some `r ≠ t`. -/
def dropLastEquiv {n : ℕ} (s t : Fin 3) :
    {c : ColSeq (n + 1) // AdjDistinct c ∧ c 0 = s ∧ c (Fin.last (n + 1)) = t} ≃
    Σ r : Fin 3,
      {c : ColSeq n // AdjDistinct c ∧ c 0 = s ∧ c (Fin.last n) = r ∧ r ≠ t} where
  toFun c :=
    ⟨c.1 (Fin.castSucc (Fin.last n)), Fin.init c.1,
      fun i => by
        have h := c.2.1 (Fin.castSucc i)
        have h2 : Fin.castSucc i.succ = (Fin.castSucc i).succ := Fin.ext rfl
        show c.1 (Fin.castSucc (Fin.castSucc i)) ≠ c.1 (Fin.castSucc i.succ)
        rw [h2]; exact h,
      by
        have hcs : Fin.castSucc (0 : Fin (n + 1)) = 0 := Fin.ext rfl
        show c.1 (Fin.castSucc 0) = s
        rw [hcs]; exact c.2.2.1,
      rfl,
      by
        have h1 := c.2.1 (Fin.last n)
        have h2 : Fin.succ (Fin.last n) = Fin.last (n + 1) := Fin.ext rfl
        rw [h2, c.2.2.2] at h1
        exact h1⟩
  invFun x :=
    ⟨Fin.snoc x.2.1 t,
      fun i => by
        rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
        · have h2 : Fin.succ (Fin.castSucc j) = Fin.castSucc (Fin.succ j) := Fin.ext rfl
          rw [Fin.snoc_castSucc, h2, Fin.snoc_castSucc]
          exact x.2.2.1 j
        · have h2 : Fin.succ (Fin.last n) = Fin.last (n + 1) := Fin.ext rfl
          rw [Fin.snoc_castSucc, h2, Fin.snoc_last, x.2.2.2.2.1]
          exact x.2.2.2.2.2,
      by
        have hcs : Fin.castSucc (0 : Fin (n + 1)) = 0 := Fin.ext rfl
        rw [← hcs, Fin.snoc_castSucc]
        exact x.2.2.2.1,
      Fin.snoc_last _ _⟩
  left_inv c := by
    refine Subtype.ext (funext fun i => ?_)
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · show Fin.snoc (Fin.init c.1) t (Fin.castSucc j) = c.1 (Fin.castSucc j)
      rw [Fin.snoc_castSucc]
      rfl
    · show Fin.snoc (Fin.init c.1) t (Fin.last (n + 1)) = c.1 (Fin.last (n + 1))
      rw [Fin.snoc_last]
      exact c.2.2.2.symm
  right_inv x := by
    obtain ⟨r, c', hadj, h0, hlast, hrt⟩ := x
    have h1 : (Fin.snoc c' t : Fin (n + 2) → Fin 3) (Fin.castSucc (Fin.last n)) = r := by
      rw [Fin.snoc_castSucc, hlast]
    have h2 : Fin.init (Fin.snoc c' t : Fin (n + 2) → Fin 3) = c' := Fin.init_snoc _ _
    refine Sigma.ext h1 ?_
    subst h1
    exact heq_of_eq (Subtype.ext h2)

/-- The count recurrence obtained from `dropLastEquiv`. -/
theorem countCol_succ {n : ℕ} (s t : Fin 3) :
    countCol (n + 1) s t =
      ∑ r : Fin 3, Nat.card
        {c : ColSeq n // AdjDistinct c ∧ c 0 = s ∧ c (Fin.last n) = r ∧ r ≠ t} := by
  unfold countCol
  rw [Nat.card_congr (dropLastEquiv s t), Nat.card_sigma]

/-- Dropping a decidable side condition from a column count. -/
theorem card_drop_ne {n : ℕ} (s r t : Fin 3) (h : r ≠ t) :
    Nat.card {c : ColSeq n // AdjDistinct c ∧ c 0 = s ∧ c (Fin.last n) = r ∧ r ≠ t} =
      countCol n s r :=
  Nat.card_congr (Equiv.subtypeEquivRight
    (fun _ => ⟨fun h' => ⟨h'.1, h'.2.1, h'.2.2.1⟩, fun h' => ⟨h'.1, h'.2.1, h'.2.2, h⟩⟩))

/-- A column count with contradictory side conditions is zero. -/
theorem card_eq_zero_of_ne {n : ℕ} (s r t : Fin 3) (h : r = t) :
    Nat.card {c : ColSeq n // AdjDistinct c ∧ c 0 = s ∧ c (Fin.last n) = r ∧ r ≠ t} = 0 := by
  subst h
  rw [Nat.card_eq_fintype_card, Fintype.card_eq_zero_iff]
  exact ⟨fun c => c.2.2.2.2 rfl⟩

/-- First recursion: `x_{n+1} = y_n + x_n`. -/
theorem x_succ (n : ℕ) : countCol (n + 1) 0 1 = countCol n 2 2 + countCol n 0 1 := by
  simp only [countCol_succ, Fin.sum_univ_three,
    card_drop_ne 0 0 1 (by decide), card_eq_zero_of_ne 0 1 1 rfl,
    card_drop_ne 0 2 1 (by decide),
    card_eq_swap 0 0 2 2 0 2 (by decide) (by decide),
    card_eq_swap 0 2 0 1 1 2 (by decide) (by decide)]
  ring

/-- Second recursion: `y_{n+1} = 2 * x_n`. -/
theorem y_succ (n : ℕ) : countCol (n + 1) 2 2 = 2 * countCol n 0 1 := by
  simp only [countCol_succ, Fin.sum_univ_three,
    card_drop_ne 2 0 2 (by decide), card_drop_ne 2 1 2 (by decide),
    card_eq_zero_of_ne 2 2 2 rfl,
    card_eq_swap 2 0 0 2 0 2 (by decide) (by decide),
    card_eq_swap 0 2 0 1 1 2 (by decide) (by decide),
    card_eq_swap 2 1 0 1 0 2 (by decide) (by decide)]
  ring

/-- Base value: there is no sequence starting with `u` and ending with `v` when
`n = 0`. -/
theorem x_zero : countCol 0 0 1 = 0 := by
  unfold countCol
  rw [Nat.card_eq_fintype_card, Fintype.card_eq_zero_iff]
  exact ⟨fun c => by
    have h1 := c.2.2.1
    have h2 := c.2.2.2
    exact absurd (h1 ▸ (show c.1 0 = 1 from h2)) (by decide)⟩

/-- Base value: exactly one sequence starts and ends with `w` when `n = 0`. -/
theorem y_zero : countCol 0 2 2 = 1 := by
  have : Unique {c : ColSeq 0 // AdjDistinct c ∧ c 0 = 2 ∧ c (Fin.last 0) = 2} :=
    { default := ⟨fun _ => 2, fun i => i.elim0, rfl, rfl⟩
      uniq := fun c => by
        apply Subtype.ext
        funext i
        rw [Fin.eq_zero i]
        exact c.2.2.1 }
  unfold countCol
  rw [Nat.card_eq_fintype_card, Fintype.card_unique]

/-- The total number of sequences with fixed first column: `2 * x_n + y_n = 2^n`. -/
theorem two_x_add_y (n : ℕ) : 2 * countCol n 0 1 + countCol n 2 2 = 2 ^ n := by
  induction n with
  | zero => rw [x_zero, y_zero]; rfl
  | succ n ih =>
    rw [x_succ, y_succ, pow_succ]
    omega

/-- The key identity: `a_{n+1} + a_n = 2 ^ (n+1)`. -/
theorem key (n : ℕ) : a (n + 1) + a n = 2 ^ (n + 1) := by
  have h := two_x_add_y n
  unfold a
  rw [x_succ, y_succ, pow_succ]
  omega

snip end

problem usa2013_p2 (n : ℕ) (hn : 4 ≤ n) : a (n - 1) + a n = 2 ^ n := by
  have h := key (n - 1)
  have e : n - 1 + 1 = n := by omega
  rw [e] at h
  omega

end Usa2013P2
