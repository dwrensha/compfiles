/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics] }

/-!
# USA Mathematical Olympiad 1996, Problem 4

An n-term sequence (x₁, x₂, …, xₙ) in which each term is either 0 or 1 is called a
binary sequence of length n. Let aₙ be the number of binary sequences of length n
containing no three consecutive terms equal to 0, 1, 0 in that order. Let bₙ be the
number of binary sequences of length n that contain no four consecutive terms equal
to 0, 0, 1, 1 or 1, 1, 0, 0 in that order. Prove that bₙ₊₁ = 2aₙ for all positive
integers n.
-/

namespace Usa1996P4

/-- The `i`-th term of a binary sequence `x : Fin n → Bool`, or `false` if `i`
is out of range. -/
def sget {n : ℕ} (x : Fin n → Bool) (i : ℕ) : Bool :=
  if h : i < n then x ⟨i, h⟩ else false

/-- A binary sequence of length `n` (encoded as `x : Fin n → Bool`, with `false`
standing for `0` and `true` for `1`) is `A`-good if it contains no three consecutive
terms equal to `0, 1, 0` in that order. -/
abbrev GoodA {n : ℕ} (x : Fin n → Bool) : Prop :=
  ∀ i : Fin n, (i : ℕ) + 2 < n →
    ¬(sget x (i : ℕ) = false ∧ sget x ((i : ℕ) + 1) = true ∧ sget x ((i : ℕ) + 2) = false)

/-- A binary sequence of length `n` is `B`-good if it contains no four consecutive
terms equal to `0, 0, 1, 1` or `1, 1, 0, 0` in that order. -/
abbrev GoodB {n : ℕ} (y : Fin n → Bool) : Prop :=
  ∀ i : Fin n, (i : ℕ) + 3 < n →
    ¬((sget y (i : ℕ) = false ∧ sget y ((i : ℕ) + 1) = false ∧ sget y ((i : ℕ) + 2) = true ∧
        sget y ((i : ℕ) + 3) = true) ∨
      (sget y (i : ℕ) = true ∧ sget y ((i : ℕ) + 1) = true ∧ sget y ((i : ℕ) + 2) = false ∧
        sget y ((i : ℕ) + 3) = false))

snip begin

theorem sget_lt {n : ℕ} (x : Fin n → Bool) {i : ℕ} (h : i < n) :
    sget x i = x ⟨i, h⟩ :=
  dite_eq_left h

/-- The sequence of successive differences (XORs) of `y`. -/
def diff {n : ℕ} (y : Fin (n + 1) → Bool) : Fin n → Bool :=
  fun i ↦ xor (sget y i.val) (sget y (i.val + 1))

/-- Auxiliary for `build`: the `k`-th term of the sequence with first term `c`
and successive differences given by `x`. -/
def buildAux {n : ℕ} (x : Fin n → Bool) (c : Bool) : ℕ → Bool
  | 0 => c
  | k + 1 => xor (buildAux x c k) (sget x k)

/-- The sequence of length `n + 1` with first term `c` whose successive
differences are given by `x`. -/
def build {n : ℕ} (x : Fin n → Bool) (c : Bool) : Fin (n + 1) → Bool :=
  fun i ↦ buildAux x c i.val

theorem build_zero {n : ℕ} (x : Fin n → Bool) (c : Bool) :
    build x c 0 = c := by
  show buildAux x c 0 = c
  simp only [buildAux]

theorem buildAux_succ {n : ℕ} (x : Fin n → Bool) (c : Bool) (k : ℕ) :
    buildAux x c (k + 1) = xor (buildAux x c k) (sget x k) := by
  simp only [buildAux]

theorem sget_build {n : ℕ} (x : Fin n → Bool) (c : Bool) {i : ℕ} (h : i < n + 1) :
    sget (build x c) i = buildAux x c i :=
  dite_eq_left h

theorem sget_diff_build {n : ℕ} (x : Fin n → Bool) (c : Bool) :
    ∀ i : ℕ, i < n →
      xor (sget (build x c) i) (sget (build x c) (i + 1)) = sget x i := by
  intro i hi
  have hi' : i < n + 1 := by lia
  have hi1 : i + 1 < n + 1 := by lia
  rw [sget_build x c hi', sget_build x c hi1, buildAux_succ]
  generalize buildAux x c i = u
  generalize sget x i = v
  revert u v
  decide

theorem sget_diff {n : ℕ} (y : Fin (n + 1) → Bool) :
    ∀ i : ℕ, i < n → xor (sget y i) (sget y (i + 1)) = sget (diff y) i := by
  intro i hi
  rw [sget_lt (diff y) hi]
  rfl

/-- A block `0,0,1,1` or `1,1,0,0` in `y` at position `i` corresponds exactly to
a block `0,1,0` in the difference sequence of `y` at position `i`. -/
theorem pattern_transfer {n : ℕ} {y : Fin (n + 1) → Bool} {x : Fin n → Bool}
    (hxe : ∀ j : ℕ, j < n → xor (sget y j) (sget y (j + 1)) = sget x j)
    {i : ℕ} (hi : i + 3 < n + 1) :
    ((sget y i = false ∧ sget y (i + 1) = false ∧ sget y (i + 2) = true ∧
        sget y (i + 3) = true) ∨
      (sget y i = true ∧ sget y (i + 1) = true ∧ sget y (i + 2) = false ∧
        sget y (i + 3) = false)) ↔
    (sget x i = false ∧ sget x (i + 1) = true ∧ sget x (i + 2) = false) := by
  have e0 : xor (sget y i) (sget y (i + 1)) = sget x i := hxe i (by lia)
  have e1 : xor (sget y (i + 1)) (sget y (i + 2)) = sget x (i + 1) := hxe (i + 1) (by lia)
  have e2 : xor (sget y (i + 2)) (sget y (i + 3)) = sget x (i + 2) := hxe (i + 2) (by lia)
  revert e0 e1 e2
  generalize sget y i = a
  generalize sget y (i + 1) = b
  generalize sget y (i + 2) = d
  generalize sget y (i + 3) = e
  generalize sget x i = a'
  generalize sget x (i + 1) = b'
  generalize sget x (i + 2) = d'
  revert a b d e a' b' d'
  decide

theorem goodB_build {n : ℕ} {x : Fin n → Bool} {c : Bool} (hx : GoodA x) :
    GoodB (build x c) := by
  intro i hi hpat
  have hi' : (i : ℕ) + 3 < n + 1 := hi
  have key : sget x (i : ℕ) = false ∧ sget x ((i : ℕ) + 1) = true ∧
      sget x ((i : ℕ) + 2) = false :=
    (pattern_transfer (sget_diff_build x c) (i := (i : ℕ)) hi').mp hpat
  have hn : (i : ℕ) < n := by lia
  exact hx ⟨(i : ℕ), hn⟩ (by show (i : ℕ) + 2 < n; lia) key

theorem goodA_diff {n : ℕ} {y : Fin (n + 1) → Bool} (hy : GoodB y) :
    GoodA (diff y) := by
  intro i hi hpat
  have hi' : (i : ℕ) + 3 < n + 1 := by lia
  have key : (sget y (i : ℕ) = false ∧ sget y ((i : ℕ) + 1) = false ∧
      sget y ((i : ℕ) + 2) = true ∧ sget y ((i : ℕ) + 3) = true) ∨
    (sget y (i : ℕ) = true ∧ sget y ((i : ℕ) + 1) = true ∧
      sget y ((i : ℕ) + 2) = false ∧ sget y ((i : ℕ) + 3) = false) :=
    (pattern_transfer (sget_diff y) (i := (i : ℕ)) hi').mpr hpat
  have hn : (i : ℕ) < n + 1 := by lia
  exact hy ⟨(i : ℕ), hn⟩ (by show (i : ℕ) + 3 < n + 1; lia) key

theorem diff_build {n : ℕ} (x : Fin n → Bool) (c : Bool) :
    diff (build x c) = x := by
  funext i
  show xor (sget (build x c) i.val) (sget (build x c) (i.val + 1)) = x i
  rw [sget_diff_build x c i.val i.isLt, sget_lt x i.isLt]

theorem build_diff {n : ℕ} (y : Fin (n + 1) → Bool) :
    build (diff y) (y 0) = y := by
  funext i
  obtain ⟨k, hk⟩ := i
  revert hk
  show ∀ hk : k < n + 1, buildAux (diff y) (y 0) k = y ⟨k, hk⟩
  induction k with
  | zero =>
    intro hk
    have h0 : buildAux (diff y) (y 0) 0 = y 0 := by simp only [buildAux]
    rw [h0, Fin.zero_eta]
  | succ k ih =>
    intro hk
    have hkn : k < n + 1 := by lia
    have hkn' : k < n := by lia
    rw [buildAux_succ, ← sget_diff y k hkn', ih hkn, sget_lt y hkn, sget_lt y hk]
    generalize y ⟨k, hkn⟩ = u
    generalize y ⟨k + 1, hk⟩ = v
    revert u v
    decide

/-- The 2-to-1 correspondence: a `B`-good sequence of length `n + 1` is
determined by its first term (two choices) and its difference sequence, which
is an `A`-good sequence of length `n`. -/
def seqEquiv (n : ℕ) :
    {x : Fin n → Bool // GoodA x} × Bool ≃ {y : Fin (n + 1) → Bool // GoodB y} where
  toFun := fun ⟨x, c⟩ ↦ ⟨build x.1 c, goodB_build x.2⟩
  invFun := fun y ↦ ⟨⟨diff y.1, goodA_diff y.2⟩, y.1 0⟩
  left_inv := by
    rintro ⟨x, c⟩
    refine Prod.ext ?_ ?_
    · exact Subtype.ext (diff_build x.1 c)
    · exact build_zero x.1 c
  right_inv := by
    intro y
    exact Subtype.ext (build_diff y.1)

snip end

problem usa1996_p4 (n : ℕ) :
    Fintype.card {y : Fin (n + 1) → Bool // GoodB y} =
      2 * Fintype.card {x : Fin n → Bool // GoodA x} := by
  have h := Fintype.card_congr (seqEquiv n)
  rw [Fintype.card_prod, Fintype.card_bool] at h
  lia

end Usa1996P4
