/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Tactic
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 1973, Problem 2

Can we find a finite set of non-coplanar points in space, such that given any
two points, `A` and `B`, there are two others, `C` and `D`, with the lines `AB`
and `CD` parallel and distinct?

(Problem and answer source: https://prase.cz/kalva/imo/isoln/isoln732.html)
-/

namespace Imo1973P2

/-- Three-dimensional Euclidean space, coordinatized as `ℝ³`. -/
abbrev Point := Fin 3 → ℝ

/-- The line through two points `A B : ℝ³`, parametrized as `A + t • (B - A)`. -/
def lineThrough (A B : Point) : Set Point := {P | ∃ t : ℝ, P = A + t • (B - A)}

/-- The lines `AB` and `CD` are parallel (their direction vectors are
proportional with a nonzero factor) and distinct (as sets of points). -/
def ParallelDistinct (A B C D : Point) : Prop :=
  (∃ k : ℝ, k ≠ 0 ∧ B - A = k • (D - C)) ∧ lineThrough A B ≠ lineThrough C D

/-- A set of points in `ℝ³` is coplanar if it is contained in some plane,
i.e. there is a nonzero normal vector `n` and a constant `d` such that every
point `P` of the set satisfies `n • P = d`. -/
def Coplanar (s : Set Point) : Prop :=
  ∃ n : Point, n ≠ 0 ∧ ∃ d : ℝ, ∀ P ∈ s, P 0 * n 0 + P 1 * n 1 + P 2 * n 2 = d

/-- The property required of the point set: given any two points `A B` of the
set there are two others `C D` with the lines `AB` and `CD` parallel and
distinct, and the points of the set are not all coplanar. -/
def IsGood (M : Finset Point) : Prop :=
  (∀ A ∈ M, ∀ B ∈ M, A ≠ B →
    ∃ C ∈ M, ∃ D ∈ M, C ≠ A ∧ C ≠ B ∧ D ≠ A ∧ D ≠ B ∧ C ≠ D ∧
      ParallelDistinct A B C D) ∧
  ¬ Coplanar (M : Set Point)

snip begin

/-- The witness: the twelve vertices of a cuboctahedron, all permutations of
`(±1, ±1, 0)`. -/
noncomputable def cuboct : Finset Point :=
  {![1,1,0], ![1,-1,0], ![-1,1,0], ![-1,-1,0],
   ![1,0,1], ![1,0,-1], ![-1,0,1], ![-1,0,-1],
   ![0,1,1], ![0,1,-1], ![0,-1,1], ![0,-1,-1]}

/-- Extensionality for points of `ℝ³` via the three coordinates. -/
lemma vec_ext {v w : Point} (h0 : v 0 = w 0) (h1 : v 1 = w 1) (h2 : v 2 = w 2) :
    v = w := by
  funext i; fin_cases i <;> assumption

/-- Two points are different if some coordinate differs. -/
lemma ne_of_apply_ne {i : Fin 3} {v w : Point} (h : v i ≠ w i) : v ≠ w :=
  fun he => h (congrFun he i)

/-- Componentwise verification of inequalities between explicit points. -/
macro "coord_ne" : tactic =>
  `(tactic| norm_num [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
      Pi.neg_apply])

/-- Componentwise verification of identities between explicit points. -/
macro "vec_norm" : tactic =>
  `(tactic| ext i <;> fin_cases i <;>
    norm_num [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
      Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul])

/-- Every point of `cuboct` has squared norm `2`. -/
lemma sqnorm {A : Point} (hA : A ∈ cuboct) : A 0 ^ 2 + A 1 ^ 2 + A 2 ^ 2 = 2 := by
  simp only [cuboct, Finset.mem_insert, Finset.mem_singleton] at hA
  rcases hA with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    norm_num [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]

/-- `cuboct` is centrally symmetric: it is closed under `P ↦ -P`. -/
lemma neg_mem {A : Point} (hA : A ∈ cuboct) : -A ∈ cuboct := by
  have n1 : (-![1,1,0] : Point) = ![-1,-1,0] := by vec_norm
  have n2 : (-![1,-1,0] : Point) = ![-1,1,0] := by vec_norm
  have n3 : (-![-1,1,0] : Point) = ![1,-1,0] := by vec_norm
  have n4 : (-![-1,-1,0] : Point) = ![1,1,0] := by vec_norm
  have n5 : (-![1,0,1] : Point) = ![-1,0,-1] := by vec_norm
  have n6 : (-![1,0,-1] : Point) = ![-1,0,1] := by vec_norm
  have n7 : (-![-1,0,1] : Point) = ![1,0,-1] := by vec_norm
  have n8 : (-![-1,0,-1] : Point) = ![1,0,1] := by vec_norm
  have n9 : (-![0,1,1] : Point) = ![0,-1,-1] := by vec_norm
  have n10 : (-![0,1,-1] : Point) = ![0,-1,1] := by vec_norm
  have n11 : (-![0,-1,1] : Point) = ![0,1,-1] := by vec_norm
  have n12 : (-![0,-1,-1] : Point) = ![0,1,1] := by vec_norm
  simp only [cuboct, Finset.mem_insert, Finset.mem_singleton] at hA
  rcases hA with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp [cuboct, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12]

/-- No point of `cuboct` is fixed by `P ↦ -P` (as none of them is zero). -/
lemma neg_ne_self {A : Point} (hA : A ∈ cuboct) : -A ≠ A := by
  intro h
  have hs := sqnorm hA
  have hz : A = 0 := by
    funext i
    have hi := congrFun h i
    simp only [Pi.neg_apply] at hi
    simp only [Pi.zero_apply]
    linarith [hi]
  rw [hz] at hs
  norm_num [Pi.zero_apply] at hs

/-- The line through `A` and `B` is the same as the line through `B` and `A`. -/
lemma lineThrough_comm (A B : Point) : lineThrough A B = lineThrough B A := by
  ext P
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨1 - t, by module⟩
  · rintro ⟨t, rfl⟩
    exact ⟨1 - t, by module⟩

/-- The generic case `B ≠ -A`: take the antipodes `C = -A`, `D = -B`. -/
lemma generic {A B : Point} (hA : A ∈ cuboct) (hB : B ∈ cuboct) (hAB : A ≠ B)
    (hBA : B ≠ -A) :
    ∃ C ∈ cuboct, ∃ D ∈ cuboct, C ≠ A ∧ C ≠ B ∧ D ≠ A ∧ D ≠ B ∧ C ≠ D ∧
      ParallelDistinct A B C D := by
  refine ⟨-A, neg_mem hA, -B, neg_mem hB, neg_ne_self hA,
    fun h => hBA h.symm, fun h => hBA ?_, neg_ne_self hB,
    fun h => hAB (neg_inj.mp h), ⟨⟨-1, by norm_num, by module⟩, ?_⟩⟩
  · calc B = -(-B) := (neg_neg B).symm
      _ = -A := by rw [h]
  · -- The line through `-A`, `-B` (the reflection of the line `AB` in the
    -- origin) is distinct from the line `AB`: if `-A` lay on the line `AB`,
    -- then `A` and `B` would be linearly dependent, forcing `B = ±A` since
    -- both have squared norm `2`; both possibilities are excluded.
    intro hL
    have hmem : -A ∈ lineThrough (-A) (-B) := ⟨0, by simp⟩
    rw [← hL] at hmem
    obtain ⟨t, ht⟩ := hmem
    have hsA := sqnorm hA
    have hsB := sqnorm hB
    have e0 := congrFun ht 0
    have e1 := congrFun ht 1
    have e2 := congrFun ht 2
    simp only [Pi.neg_apply, Pi.add_apply, Pi.smul_apply, Pi.sub_apply,
      smul_eq_mul] at e0 e1 e2
    have k0 : t * B 0 = (t - 2) * A 0 := by linarith [e0]
    have k1 : t * B 1 = (t - 2) * A 1 := by linarith [e1]
    have k2 : t * B 2 = (t - 2) * A 2 := by linarith [e2]
    have hl : (t * B 0)^2 + (t * B 1)^2 + (t * B 2)^2 =
        t^2 * (B 0^2 + B 1^2 + B 2^2) := by ring
    have hr : ((t-2)*A 0)^2 + ((t-2)*A 1)^2 + ((t-2)*A 2)^2 =
        (t-2)^2 * (A 0^2 + A 1^2 + A 2^2) := by ring
    have hsq : (t * B 0)^2 + (t * B 1)^2 + (t * B 2)^2 =
        ((t-2)*A 0)^2 + ((t-2)*A 1)^2 + ((t-2)*A 2)^2 := by rw [k0, k1, k2]
    rw [hl, hr, hsA, hsB] at hsq
    have ht2 : t^2 = (t-2)^2 := by linarith [hsq]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp ht2 with h | h
    · linarith
    · have ht1 : t = 1 := by linarith [h]
      apply hBA
      apply vec_ext
      · have := k0; rw [ht1] at this; simp only [Pi.neg_apply]; linarith [this]
      · have := k1; rw [ht1] at this; simp only [Pi.neg_apply]; linarith [this]
      · have := k2; rw [ht1] at this; simp only [Pi.neg_apply]; linarith [this]

/-- The antipodal case: given explicit data satisfying the requirements for
the pair `(A, -A)`, conclude. Here `C, D` will be an edge of the cuboctahedron
parallel to the diameter through `A`. -/
lemma anti {A C D : Point} (_hA : A ∈ cuboct) (hC : C ∈ cuboct) (hD : D ∈ cuboct)
    (hcA : C ≠ A) (hcB : C ≠ -A) (hdA : D ≠ A) (hdB : D ≠ -A) (hcd : C ≠ D)
    (hpar : -A - A = (-2:ℝ) • (D - C)) (hline : ∀ t : ℝ, C ≠ A + t • (-A - A)) :
    ∃ C' ∈ cuboct, ∃ D' ∈ cuboct, C' ≠ A ∧ C' ≠ -A ∧ D' ≠ A ∧ D' ≠ -A ∧ C' ≠ D' ∧
      ParallelDistinct A (-A) C' D' :=
  ⟨C, hC, D, hD, hcA, hcB, hdA, hdB, hcd, ⟨⟨-2, by norm_num, hpar⟩,
    fun hL => by
      have hmem : C ∈ lineThrough C D := ⟨0, by simp⟩
      rw [← hL] at hmem
      obtain ⟨t, ht⟩ := hmem
      exact hline t ht⟩⟩

/-- The parallel-and-distinct property holds for `cuboct`. -/
lemma cuboct_parallel :
    ∀ A ∈ cuboct, ∀ B ∈ cuboct, A ≠ B →
      ∃ C ∈ cuboct, ∃ D ∈ cuboct, C ≠ A ∧ C ≠ B ∧ D ≠ A ∧ D ≠ B ∧ C ≠ D ∧
        ParallelDistinct A B C D := by
  intro A hA B hB hAB
  by_cases hBA : B = -A
  · -- Antipodal pairs: an explicit parallel edge in each of the 12 cases.
    subst hBA
    simp only [cuboct, Finset.mem_insert, Finset.mem_singleton] at hA
    rcases hA with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    -- `A = (1, 1, 0)`, edge `![0,-1,1] ![1,0,1]`
    · exact anti (C := ![0,-1,1]) (D := ![1,0,1])
        (by simp [cuboct]) (by simp [cuboct]) (by simp [cuboct])
        (ne_of_apply_ne (i := 0) (by coord_ne)) (ne_of_apply_ne (i := 0) (by coord_ne))
        (ne_of_apply_ne (i := 1) (by coord_ne)) (ne_of_apply_ne (i := 1) (by coord_ne))
        (ne_of_apply_ne (i := 0) (by coord_ne)) (by vec_norm)
        (fun t ht => by
          have h2 := congrFun ht 2
          simp at h2)
    -- `A = (1, -1, 0)`, edge `![0,1,1] ![1,0,1]`
    · exact anti (C := ![0,1,1]) (D := ![1,0,1])
        (by simp [cuboct]) (by simp [cuboct]) (by simp [cuboct])
        (ne_of_apply_ne (i := 0) (by coord_ne)) (ne_of_apply_ne (i := 0) (by coord_ne))
        (ne_of_apply_ne (i := 1) (by coord_ne)) (ne_of_apply_ne (i := 1) (by coord_ne))
        (ne_of_apply_ne (i := 0) (by coord_ne)) (by vec_norm)
        (fun t ht => by
          have h2 := congrFun ht 2
          simp at h2)
    -- `A = (-1, 1, 0)`, edge `![1,0,1] ![0,1,1]`
    · exact anti (C := ![1,0,1]) (D := ![0,1,1])
        (by simp [cuboct]) (by simp [cuboct]) (by simp [cuboct])
        (ne_of_apply_ne (i := 0) (by coord_ne)) (ne_of_apply_ne (i := 1) (by coord_ne))
        (ne_of_apply_ne (i := 0) (by coord_ne)) (ne_of_apply_ne (i := 0) (by coord_ne))
        (ne_of_apply_ne (i := 0) (by coord_ne)) (by vec_norm)
        (fun t ht => by
          have h2 := congrFun ht 2
          simp at h2)
    -- `A = (-1, -1, 0)`, edge `![1,0,1] ![0,-1,1]`
    · exact anti (C := ![1,0,1]) (D := ![0,-1,1])
        (by simp [cuboct]) (by simp [cuboct]) (by simp [cuboct])
        (ne_of_apply_ne (i := 0) (by coord_ne)) (ne_of_apply_ne (i := 1) (by coord_ne))
        (ne_of_apply_ne (i := 0) (by coord_ne)) (ne_of_apply_ne (i := 0) (by coord_ne))
        (ne_of_apply_ne (i := 0) (by coord_ne)) (by vec_norm)
        (fun t ht => by
          have h2 := congrFun ht 2
          simp at h2)
    -- `A = (1, 0, 1)`, edge `![0,1,-1] ![1,1,0]`
    · exact anti (C := ![0,1,-1]) (D := ![1,1,0])
        (by simp [cuboct]) (by simp [cuboct]) (by simp [cuboct])
        (ne_of_apply_ne (i := 0) (by coord_ne)) (ne_of_apply_ne (i := 0) (by coord_ne))
        (ne_of_apply_ne (i := 2) (by coord_ne)) (ne_of_apply_ne (i := 2) (by coord_ne))
        (ne_of_apply_ne (i := 0) (by coord_ne)) (by vec_norm)
        (fun t ht => by
          have h1 := congrFun ht 1
          simp at h1)
    -- `A = (1, 0, -1)`, edge `![0,1,1] ![1,1,0]`
    · exact anti (C := ![0,1,1]) (D := ![1,1,0])
        (by simp [cuboct]) (by simp [cuboct]) (by simp [cuboct])
        (ne_of_apply_ne (i := 0) (by coord_ne)) (ne_of_apply_ne (i := 0) (by coord_ne))
        (ne_of_apply_ne (i := 2) (by coord_ne)) (ne_of_apply_ne (i := 2) (by coord_ne))
        (ne_of_apply_ne (i := 0) (by coord_ne)) (by vec_norm)
        (fun t ht => by
          have h1 := congrFun ht 1
          simp at h1)
    -- `A = (-1, 0, 1)`, edge `![1,1,0] ![0,1,1]`
    · exact anti (C := ![1,1,0]) (D := ![0,1,1])
        (by simp [cuboct]) (by simp [cuboct]) (by simp [cuboct])
        (ne_of_apply_ne (i := 0) (by coord_ne)) (ne_of_apply_ne (i := 2) (by coord_ne))
        (ne_of_apply_ne (i := 0) (by coord_ne)) (ne_of_apply_ne (i := 0) (by coord_ne))
        (ne_of_apply_ne (i := 0) (by coord_ne)) (by vec_norm)
        (fun t ht => by
          have h1 := congrFun ht 1
          simp at h1)
    -- `A = (-1, 0, -1)`, edge `![1,1,0] ![0,1,-1]`
    · exact anti (C := ![1,1,0]) (D := ![0,1,-1])
        (by simp [cuboct]) (by simp [cuboct]) (by simp [cuboct])
        (ne_of_apply_ne (i := 0) (by coord_ne)) (ne_of_apply_ne (i := 2) (by coord_ne))
        (ne_of_apply_ne (i := 0) (by coord_ne)) (ne_of_apply_ne (i := 0) (by coord_ne))
        (ne_of_apply_ne (i := 0) (by coord_ne)) (by vec_norm)
        (fun t ht => by
          have h1 := congrFun ht 1
          simp at h1)
    -- `A = (0, 1, 1)`, edge `![1,0,-1] ![1,1,0]`
    · exact anti (C := ![1,0,-1]) (D := ![1,1,0])
        (by simp [cuboct]) (by simp [cuboct]) (by simp [cuboct])
        (ne_of_apply_ne (i := 1) (by coord_ne)) (ne_of_apply_ne (i := 1) (by coord_ne))
        (ne_of_apply_ne (i := 0) (by coord_ne)) (ne_of_apply_ne (i := 0) (by coord_ne))
        (ne_of_apply_ne (i := 1) (by coord_ne)) (by vec_norm)
        (fun t ht => by
          have h0 := congrFun ht 0
          simp at h0)
    -- `A = (0, 1, -1)`, edge `![1,0,1] ![1,1,0]`
    · exact anti (C := ![1,0,1]) (D := ![1,1,0])
        (by simp [cuboct]) (by simp [cuboct]) (by simp [cuboct])
        (ne_of_apply_ne (i := 1) (by coord_ne)) (ne_of_apply_ne (i := 1) (by coord_ne))
        (ne_of_apply_ne (i := 0) (by coord_ne)) (ne_of_apply_ne (i := 0) (by coord_ne))
        (ne_of_apply_ne (i := 1) (by coord_ne)) (by vec_norm)
        (fun t ht => by
          have h0 := congrFun ht 0
          simp at h0)
    -- `A = (0, -1, 1)`, edge `![1,1,0] ![1,0,1]`
    · exact anti (C := ![1,1,0]) (D := ![1,0,1])
        (by simp [cuboct]) (by simp [cuboct]) (by simp [cuboct])
        (ne_of_apply_ne (i := 1) (by coord_ne)) (ne_of_apply_ne (i := 2) (by coord_ne))
        (ne_of_apply_ne (i := 1) (by coord_ne)) (ne_of_apply_ne (i := 2) (by coord_ne))
        (ne_of_apply_ne (i := 1) (by coord_ne)) (by vec_norm)
        (fun t ht => by
          have h0 := congrFun ht 0
          simp at h0)
    -- `A = (0, -1, -1)`, edge `![1,1,0] ![1,0,-1]`
    · exact anti (C := ![1,1,0]) (D := ![1,0,-1])
        (by simp [cuboct]) (by simp [cuboct]) (by simp [cuboct])
        (ne_of_apply_ne (i := 1) (by coord_ne)) (ne_of_apply_ne (i := 2) (by coord_ne))
        (ne_of_apply_ne (i := 1) (by coord_ne)) (ne_of_apply_ne (i := 2) (by coord_ne))
        (ne_of_apply_ne (i := 1) (by coord_ne)) (by vec_norm)
        (fun t ht => by
          have h0 := congrFun ht 0
          simp at h0)
  · exact generic hA hB hAB hBA

/-- The vertices of the cuboctahedron are not coplanar: the four points
`(1,1,0)`, `(1,-1,0)`, `(1,0,1)`, `(0,1,1)` are affinely independent. -/
lemma not_coplanar : ¬ Coplanar (cuboct : Set Point) := by
  rintro ⟨n, hn, d, hd⟩
  have e1 := hd ![1,1,0] (by simp [cuboct])
  have e2 := hd ![1,-1,0] (by simp [cuboct])
  have e3 := hd ![1,0,1] (by simp [cuboct])
  have e4 := hd ![0,1,1] (by simp [cuboct])
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons] at e1 e2 e3 e4
  apply hn
  apply vec_ext
  · simp only [Pi.zero_apply]; linarith
  · simp only [Pi.zero_apply]; linarith
  · simp only [Pi.zero_apply]; linarith

snip end

determine does_exist : Bool := true

problem imo1973_p2 :
    if does_exist then ∃ M : Finset Point, IsGood M
    else ¬ ∃ M : Finset Point, IsGood M := by
  simp only [ite_true]
  exact ⟨cuboct, cuboct_parallel, not_coplanar⟩

end Imo1973P2
