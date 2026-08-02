/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.RingTheory.SimpleRing.Principal
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics, .Geometry] }

/-!
# USA Mathematical Olympiad 2022, Problem 2

Let b ≥ 2 and w ≥ 2 be fixed integers, and n = b + w. Given are 2b identical
black rods and 2w identical white rods, each of side length 1.

We assemble a regular 2n-gon using these rods so that parallel sides are the
same color. Then, a convex 2b-gon B is formed by translating the black rods,
and a convex 2w-gon W is formed by translating the white rods. An example of
one way of doing the assembly when b = 3 and w = 2 is shown below, as well as
the resulting polygons B and W.

Prove that the difference of the areas of B and W depends only on the numbers
b and w, and not on how the 2n-gon was assembled.
-/

namespace Usa2022P2

open Complex Finset

noncomputable section

/-!
## Setup

We identify the Euclidean plane with `ℂ`.  A regular `2n`-gon is determined
(up to translation) by the directions of its sides; traversing the boundary
counterclockwise, the `j`-th side is a unit complex number, and consecutive
sides differ by the exterior angle `π / n`.  We model the side directions as
`u j = ζ * ω ^ j`, where `ζ` is a unit complex number (the direction of the
first side) and `ω` satisfies `ω ^ n = -1` (so `ω = exp (I * π / n)`, up to
winding).  Note that `u (j + n) = - u j`: sides `j` and `j + n` are parallel,
as required.  The parameters `n`, `ω`, `ζ` are bundled in `GonParams`.

An *assembly* is thus a coloring `c : Fin n → Bool` of the first `n` sides
(one side per pair of parallel sides), extended by `c (j + n) = c j`.

For `a b : ℂ` we write `wedge a b = (star a * b).im = a.re * b.im - a.im * b.re`
for the signed area of the parallelogram spanned by the corresponding vectors.

If `e 0, …, e (m - 1)` are the edge vectors of a convex polygon traversed
counterclockwise, its signed area equals `½ * ∑_{i < j} wedge (e i) (e j)`
(shoelace formula).  The black polygon `B` has edge vectors
`u i₁, …, u i_b, - u i₁, …, - u i_b` in circular order, where `i₁ < … < i_b`
are the black indices.  Since the black edge vectors sum to zero, the shoelace
formula simplifies to `∑_{r < s} wedge (u i_r) (u i_s)`, which is the
definition we use below for `blackArea` (and likewise for `whiteArea`).
-/

/-- Parameters describing the regular `2n`-gon: the half side count `n`,
and complex numbers `ζ` (direction of the first side) and `ω` (rotation by
the exterior angle `π / n`); the relevant hypotheses are `ω ^ n = -1` and
`‖ζ‖ = 1`. -/
structure GonParams where
  n : ℕ
  ω : ℂ
  ζ : ℂ

variable (P : GonParams)
variable {n : ℕ}

/-- The wedge (cross) product of two plane vectors represented as complex
numbers: the signed area of the parallelogram they span. -/
def wedge (a b : ℂ) : ℝ := (star a * b).im

/-- The direction of the `j`-th side of the regular `2n`-gon, as a unit complex
number.  Here `ω ^ n = -1`, so `u (j + n) = - u j`: sides `j` and `j + n` are
parallel. -/
def u (j : ℕ) : ℂ := P.ζ * P.ω ^ j

/-- An assembly of the `2n`-gon: the colors of the first `n` sides (one side
per pair of parallel sides), `true` for black and `false` for white. -/
abbrev Assembly (n : ℕ) := Fin n → Bool

/-- The number of black pairs of parallel sides; the assembly uses
`2 * blackCount c` black rods in total. -/
def blackCount (c : Assembly n) : ℕ := (univ.filter fun i ↦ c i).card

/-- The sign associated to a color: `+1` for black, `-1` for white. -/
def sgn (b : Bool) : ℝ := if b then 1 else -1

/-- The area of the convex polygon `B` formed by the black rods (see the setup
note for the derivation of this formula). -/
def blackArea (c : Assembly P.n) : ℝ :=
  ∑ i : Fin P.n, ∑ j : Fin P.n, if i < j ∧ c i ∧ c j then wedge (u P i.1) (u P j.1) else 0

/-- The area of the convex polygon `W` formed by the white rods. -/
def whiteArea (c : Assembly P.n) : ℝ :=
  ∑ i : Fin P.n, ∑ j : Fin P.n, if i < j ∧ ¬ c i ∧ ¬ c j then wedge (u P i.1) (u P j.1) else 0

snip begin

variable {ι : Type*}

/-!
### Basic properties of the wedge product
-/

lemma wedge_self (a : ℂ) : wedge a a = 0 := by
  simp [wedge, ← Complex.normSq_eq_conj_mul_self]

lemma wedge_add_left (a b c : ℂ) : wedge (a + b) c = wedge a c + wedge b c := by
  simp [wedge, add_mul]

lemma wedge_add_right (a b c : ℂ) : wedge a (b + c) = wedge a b + wedge a c := by
  simp [wedge, mul_add]

lemma wedge_sub_left (a b c : ℂ) : wedge (a - b) c = wedge a c - wedge b c := by
  simp [wedge, sub_mul]

lemma wedge_sub_right (a b c : ℂ) : wedge a (b - c) = wedge a b - wedge a c := by
  simp [wedge, mul_sub]

lemma wedge_antisymm (a b : ℂ) : wedge a b + wedge b a = 0 := by
  have e : star b * a = star (star a * b) := by rw [star_mul, star_star, mul_comm]
  have e2 : (star (star a * b)).im = - (star a * b).im := Complex.conj_im _
  simp only [wedge, e, e2, add_neg_cancel]

lemma wedge_neg (a b : ℂ) : wedge a b = - wedge b a := by
  linarith [wedge_antisymm a b]

lemma wedge_zero_left (a : ℂ) : wedge 0 a = 0 := by simp [wedge]

lemma wedge_zero_right (a : ℂ) : wedge a 0 = 0 := by simp [wedge]

lemma wedge_sum_left [DecidableEq ι] (s : Finset ι) (f : ι → ℂ) (b : ℂ) :
    wedge (∑ i ∈ s, f i) b = ∑ i ∈ s, wedge (f i) b := by
  induction s using Finset.induction with
  | empty => simp [wedge_zero_left]
  | insert x s h ih => simp [Finset.sum_insert h, wedge_add_left, ih]

lemma wedge_sum_right [DecidableEq ι] (s : Finset ι) (f : ι → ℂ) (a : ℂ) :
    wedge a (∑ i ∈ s, f i) = ∑ i ∈ s, wedge a (f i) := by
  induction s using Finset.induction with
  | empty => simp [wedge_zero_right]
  | insert x s h ih => simp [Finset.sum_insert h, wedge_add_right, ih]

/-!
### The side directions `u P j = ζ * ω ^ j`
-/

lemma one_le_n (hω : P.ω ^ P.n = -1) : 1 ≤ P.n := by
  rcases Nat.eq_zero_or_pos P.n with h | h
  · exfalso
    rw [h, pow_zero] at hω
    exact absurd hω (by norm_num)
  · exact h

lemma omega_ne_zero (hω : P.ω ^ P.n = -1) : P.ω ≠ 0 := by
  have hn := one_le_n P hω
  intro h
  rw [h, zero_pow (by omega : P.n ≠ 0)] at hω
  exact absurd hω (by norm_num)

lemma normSq_omega (hω : P.ω ^ P.n = -1) : normSq P.ω = 1 := by
  have hn := one_le_n P hω
  have h1 : (normSq P.ω) ^ P.n = 1 := by
    have h2 : normSq (P.ω ^ P.n) = normSq (-1 : ℂ) := by rw [hω]
    rw [map_pow] at h2
    simpa using h2
  exact (pow_eq_one_iff_of_nonneg (normSq_nonneg P.ω) (by omega)).mp h1

lemma star_omega (hω : P.ω ^ P.n = -1) : star P.ω = P.ω⁻¹ := by
  have e : star P.ω * P.ω = 1 := by
    rw [show star P.ω * P.ω = (starRingEnd ℂ) P.ω * P.ω from rfl,
      ← Complex.normSq_eq_conj_mul_self, normSq_omega P hω]
    simp
  exact eq_inv_of_mul_eq_one_left e

lemma star_zeta_mul (hζ : ‖P.ζ‖ = 1) : star P.ζ * P.ζ = 1 := by
  rw [show star P.ζ * P.ζ = (starRingEnd ℂ) P.ζ * P.ζ from rfl,
    ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hζ]
  simp

/-- The sum of the first `i` side vectors `u 0, …, u (i-1)`. -/
def Usum (i : ℕ) : ℂ := ∑ j ∈ range i, u P j

/-- The sum of the side vectors `u i, …, u (n-1)` (an empty sum when `n ≤ i`). -/
def UsumFrom (i : ℕ) : ℂ := ∑ j ∈ range (P.n - i), u P (i + j)

lemma Usum_succ (i : ℕ) : Usum P (i + 1) = Usum P i + u P i :=
  Finset.sum_range_succ (fun j ↦ u P j) i

lemma UsumFrom_succ {i : ℕ} (h : i + 1 ≤ P.n) : UsumFrom P i = u P i + UsumFrom P (i + 1) := by
  have e : P.n - i = P.n - (i + 1) + 1 := by omega
  unfold UsumFrom
  rw [e, Finset.sum_range_succ']
  have e2 : (∑ k ∈ range (P.n - (i + 1)), u P (i + (k + 1)))
      = ∑ j ∈ range (P.n - (i + 1)), u P (i + 1 + j) := by
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    omega
  rw [e2]
  simp only [add_zero]
  exact add_comm _ _

/-!
### The key geometric fact

We introduce, for each side index `i`, the quantity
`g i = wedge (u i) (UsumFrom (i + 1) - Usum i)`.  The heart of the problem is
the following fact: swapping two adjacent sides of different colors does not
change the difference of the areas.  Algebraically this reduces to the identity
`wedge (u k - u (k + 1)) (UsumFrom (k + 2) - Usum k) = 0`, which says that
`u k - u (k + 1)` is parallel to the sum of the remaining side vectors of the
semicircle (both are perpendicular to `u k + u (k + 1)`; compare the classical
solution using the inscribed angle theorem).  We prove it by direct computation
with geometric series.
-/

/-- The wedge of the `i`-th side vector with the difference of the sums of the
side vectors after and before it.  We will show that `g` is constant. -/
def g (i : ℕ) : ℝ := wedge (u P i) (UsumFrom P (i + 1) - Usum P i)

lemma key (hω : P.ω ^ P.n = -1) (hζ : ‖P.ζ‖ = 1) {k : ℕ} (hk : k + 2 ≤ P.n) :
    wedge (u P k - u P (k + 1)) (UsumFrom P (k + 2) - Usum P k) = 0 := by
  have hω0 := omega_ne_zero P hω
  have hζ1 := star_zeta_mul P hζ
  have hωconj := star_omega P hω
  -- Closed forms from the geometric series.
  have hgeomS : (P.ω - 1) * UsumFrom P (k + 2) = P.ζ * (P.ω ^ P.n - P.ω ^ (k + 2)) := by
    have e1 : UsumFrom P (k + 2) = P.ζ * P.ω ^ (k + 2) * ∑ j ∈ range (P.n - (k + 2)), P.ω ^ j := by
      unfold UsumFrom
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      simp only [u, pow_add]
      ring
    rw [e1]
    have e2 : (P.ω - 1) * (P.ζ * P.ω ^ (k + 2) * ∑ j ∈ range (P.n - (k + 2)), P.ω ^ j)
        = P.ζ * P.ω ^ (k + 2) * ((P.ω - 1) * ∑ j ∈ range (P.n - (k + 2)), P.ω ^ j) := by ring
    rw [e2, mul_geom_sum]
    have e3 : P.ω ^ (k + 2) * (P.ω ^ (P.n - (k + 2)) - 1) = P.ω ^ P.n - P.ω ^ (k + 2) := by
      rw [mul_sub, ← pow_add, Nat.add_sub_cancel' hk, mul_one]
    rw [show P.ζ * P.ω ^ (k + 2) * (P.ω ^ (P.n - (k + 2)) - 1)
        = P.ζ * (P.ω ^ (k + 2) * (P.ω ^ (P.n - (k + 2)) - 1)) from by ring, e3]
  have hgeomP : (P.ω - 1) * Usum P k = P.ζ * (P.ω ^ k - 1) := by
    have e1 : Usum P k = P.ζ * ∑ j ∈ range k, P.ω ^ j := by
      unfold Usum
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rfl
    rw [e1]
    have e2 : (P.ω - 1) * (P.ζ * ∑ j ∈ range k, P.ω ^ j)
        = P.ζ * ((P.ω - 1) * ∑ j ∈ range k, P.ω ^ j) := by ring
    rw [e2, mul_geom_sum]
  -- The complex number whose imaginary part is the wedge we care about.
  set z := star (u P k - u P (k + 1)) * (UsumFrom P (k + 2) - Usum P k) with hz_def
  have h3 : P.ω ^ (k + 1) * star (u P k - u P (k + 1)) = star P.ζ * (P.ω - 1) := by
    have e1 : star (u P k - u P (k + 1)) = star P.ζ * (P.ω⁻¹) ^ k * (1 - P.ω⁻¹) := by
      simp only [u, star_sub, star_mul, star_pow, hωconj, pow_succ]
      ring
    rw [e1]
    have e3 : (1 : ℂ) - P.ω⁻¹ = (P.ω - 1) * P.ω⁻¹ := by
      field_simp [hω0]
    have e4 : P.ω ^ (k + 1) * (star P.ζ * (P.ω⁻¹) ^ k * ((P.ω - 1) * P.ω⁻¹))
        = (P.ω ^ (k + 1) * (P.ω⁻¹) ^ (k + 1)) * (star P.ζ * (P.ω - 1)) := by
      rw [pow_succ P.ω⁻¹ k]
      ring
    rw [e3, e4, ← mul_pow, mul_inv_cancel₀ hω0, one_pow, one_mul]
  have h4 : P.ω ^ (k + 1) * z = -P.ω ^ k * (P.ω ^ 2 + 1) := by
    have e1 : P.ω ^ (k + 1) * z
        = (P.ω ^ (k + 1) * star (u P k - u P (k + 1))) * (UsumFrom P (k + 2) - Usum P k) := by
      rw [hz_def]
      ring
    rw [e1, h3]
    have e2 : (star P.ζ * (P.ω - 1)) * (UsumFrom P (k + 2) - Usum P k)
        = star P.ζ * ((P.ω - 1) * UsumFrom P (k + 2) - (P.ω - 1) * Usum P k) := by ring
    rw [e2, hgeomS, hgeomP]
    have e3 : star P.ζ * (P.ζ * (P.ω ^ P.n - P.ω ^ (k + 2)) - P.ζ * (P.ω ^ k - 1))
        = (star P.ζ * P.ζ) * (P.ω ^ P.n - P.ω ^ (k + 2) - (P.ω ^ k - 1)) := by ring
    rw [e3, hζ1, one_mul, hω, pow_add]
    ring
  have h5 : P.ω * z = -(P.ω ^ 2 + 1) := by
    have e : P.ω ^ (k + 1) * z = P.ω ^ k * (P.ω * z) := by rw [pow_succ]; ring
    rw [e] at h4
    have h4' : P.ω ^ k * (P.ω * z) = P.ω ^ k * (-(P.ω ^ 2 + 1)) := by rw [h4]; ring
    exact mul_left_cancel₀ (pow_ne_zero k hω0) h4'
  have hz : z = -(P.ω ^ 2 + 1) / P.ω := by
    rw [eq_div_iff hω0, mul_comm]
    exact h5
  have hcz : star z = z := by
    rw [hz]
    simp only [star_neg, star_div₀, star_add, star_pow, star_one, hωconj, inv_pow]
    field_simp [hω0, pow_ne_zero _ hω0]
    ring
  have him : z.im = 0 := Complex.conj_eq_iff_im.mp hcz
  show (star (u P k - u P (k + 1)) * (UsumFrom P (k + 2) - Usum P k)).im = 0
  rw [← hz_def]
  exact him

lemma g_step (hω : P.ω ^ P.n = -1) (hζ : ‖P.ζ‖ = 1) {k : ℕ} (hk : k + 2 ≤ P.n) :
    g P k = g P (k + 1) := by
  have hA : UsumFrom P (k + 1) = u P (k + 1) + UsumFrom P (k + 2) := UsumFrom_succ P (by omega)
  have hB : Usum P (k + 1) = Usum P k + u P k := Usum_succ P k
  have hk0 := key P hω hζ hk
  have hs := wedge_antisymm (u P k) (u P (k + 1))
  simp only [g]
  rw [show (k + 1 + 1 : ℕ) = k + 2 by omega]
  rw [hA, hB, ← sub_eq_zero]
  simp only [wedge_add_right, wedge_sub_right, wedge_sub_left] at hk0 ⊢
  linarith

lemma g_const (hω : P.ω ^ P.n = -1) (hζ : ‖P.ζ‖ = 1) : ∀ k : ℕ, k + 1 ≤ P.n → g P k = g P 0 := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ m ih =>
    intro h
    rw [← ih (by omega)]
    exact (g_step P hω hζ (by omega)).symm

/-!
### The difference of the areas as a weighted sum
-/

lemma areaDiff_range (c : ℕ → Bool) :
    (∑ i ∈ range P.n, ∑ j ∈ range P.n, (if i < j ∧ c i ∧ c j then wedge (u P i) (u P j) else 0)) -
    (∑ i ∈ range P.n, ∑ j ∈ range P.n, (if i < j ∧ ¬ c i ∧ ¬ c j then wedge (u P i) (u P j) else 0)) =
    (1 / 2) * ∑ i ∈ range P.n, sgn (c i) * g P i := by
  have step1 : ∀ i j : ℕ,
      (if i < j ∧ c i ∧ c j then wedge (u P i) (u P j) else 0) -
      (if i < j ∧ ¬ c i ∧ ¬ c j then wedge (u P i) (u P j) else 0) =
      if i < j then (sgn (c i) + sgn (c j)) / 2 * wedge (u P i) (u P j) else 0 := by
    intro i j
    by_cases hij : i < j
    · cases h1 : c i <;> cases h2 : c j <;> simp [hij, sgn]
    · simp [hij]
  have step2 : ∀ i j : ℕ,
      (if i < j then (sgn (c i) + sgn (c j)) / 2 * wedge (u P i) (u P j) else 0) =
      (1 / 2 * sgn (c i)) * (if i < j then wedge (u P i) (u P j) else 0) +
      (1 / 2 * sgn (c j)) * (if i < j then wedge (u P i) (u P j) else 0) := by
    intro i j
    by_cases hij : i < j <;> simp [hij]
    ring
  have hT1 : ∀ i : ℕ,
      (∑ j ∈ range P.n, if i < j then wedge (u P i) (u P j) else 0) =
        wedge (u P i) (UsumFrom P (i + 1)) := by
    intro i
    have e : (∑ j ∈ range P.n, if i < j then wedge (u P i) (u P j) else 0)
        = ∑ j ∈ range P.n, wedge (u P i) (if i < j then u P j else 0) := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases h : i < j <;> simp [h, wedge_zero_right]
    rw [e, ← wedge_sum_right]
    congr 1
    rw [← Finset.sum_filter]
    have e2 : (range P.n).filter (fun x ↦ i < x) = Ico (i + 1) P.n := by
      rw [Finset.range_eq_Ico]
      show {x ∈ Ico 0 P.n | i + 1 ≤ x} = Ico (i + 1) P.n
      rw [Finset.Ico_filter_le]
      simp
    rw [e2, Finset.sum_Ico_eq_sum_range]
    rfl
  have hT2 : ∀ j : ℕ, j ≤ P.n →
      (∑ i ∈ range P.n, if i < j then wedge (u P i) (u P j) else 0) = wedge (Usum P j) (u P j) := by
    intro j hj
    have e : (∑ i ∈ range P.n, if i < j then wedge (u P i) (u P j) else 0)
        = ∑ i ∈ range P.n, wedge (if i < j then u P i else 0) (u P j) := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases h : i < j <;> simp [h, wedge_zero_left]
    rw [e, ← wedge_sum_left]
    congr 1
    rw [← Finset.sum_filter]
    have e2 : (range P.n).filter (fun x ↦ x < j) = range j := by
      rw [Finset.range_eq_Ico, Finset.Ico_filter_lt, min_eq_right hj, ← Finset.range_eq_Ico]
    rw [e2]
    rfl
  calc (∑ i ∈ range P.n, ∑ j ∈ range P.n, (if i < j ∧ c i ∧ c j then wedge (u P i) (u P j) else 0)) -
        (∑ i ∈ range P.n, ∑ j ∈ range P.n, (if i < j ∧ ¬ c i ∧ ¬ c j then wedge (u P i) (u P j) else 0))
      = ∑ i ∈ range P.n, ∑ j ∈ range P.n,
          (if i < j then (sgn (c i) + sgn (c j)) / 2 * wedge (u P i) (u P j) else 0) := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro j _
        exact step1 i j
    _ = ∑ i ∈ range P.n, ∑ j ∈ range P.n,
          ((1 / 2 * sgn (c i)) * (if i < j then wedge (u P i) (u P j) else 0) +
           (1 / 2 * sgn (c j)) * (if i < j then wedge (u P i) (u P j) else 0)) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        exact step2 i j
    _ = (∑ i ∈ range P.n, ∑ j ∈ range P.n,
          (1 / 2 * sgn (c i)) * (if i < j then wedge (u P i) (u P j) else 0)) +
        (∑ i ∈ range P.n, ∑ j ∈ range P.n,
          (1 / 2 * sgn (c j)) * (if i < j then wedge (u P i) (u P j) else 0)) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_add_distrib]
    _ = (∑ i ∈ range P.n, (1 / 2 * sgn (c i)) *
          ∑ j ∈ range P.n, (if i < j then wedge (u P i) (u P j) else 0)) +
        (∑ j ∈ range P.n, (1 / 2 * sgn (c j)) *
          ∑ i ∈ range P.n, (if i < j then wedge (u P i) (u P j) else 0)) := by
        congr 1
        · apply Finset.sum_congr rfl
          intro i _
          rw [← Finset.mul_sum]
        · rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro j _
          rw [← Finset.mul_sum]
    _ = (∑ i ∈ range P.n, (1 / 2 * sgn (c i)) * wedge (u P i) (UsumFrom P (i + 1))) +
        (∑ j ∈ range P.n, (1 / 2 * sgn (c j)) * wedge (Usum P j) (u P j)) := by
        congr 1
        · apply Finset.sum_congr rfl
          intro i _
          rw [hT1 i]
        · apply Finset.sum_congr rfl
          intro j hj
          rw [hT2 j (by rw [Finset.mem_range] at hj; omega)]
    _ = (∑ i ∈ range P.n, (1 / 2 * sgn (c i)) * wedge (u P i) (UsumFrom P (i + 1))) -
        (∑ j ∈ range P.n, (1 / 2 * sgn (c j)) * wedge (u P j) (Usum P j)) := by
        have this : (∑ j ∈ range P.n, (1 / 2 * sgn (c j)) * wedge (Usum P j) (u P j))
            = - ∑ j ∈ range P.n, (1 / 2 * sgn (c j)) * wedge (u P j) (Usum P j) := by
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro j _
          rw [wedge_neg]
          ring
        rw [this, sub_eq_add_neg]
    _ = ∑ i ∈ range P.n, ((1 / 2 * sgn (c i)) * wedge (u P i) (UsumFrom P (i + 1)) -
        (1 / 2 * sgn (c i)) * wedge (u P i) (Usum P i)) := by
        rw [← Finset.sum_sub_distrib]
    _ = ∑ i ∈ range P.n, (1 / 2 * sgn (c i)) * g P i := by
        apply Finset.sum_congr rfl
        intro i _
        rw [← mul_sub, ← wedge_sub_right]
        rfl
    _ = (1 / 2) * ∑ i ∈ range P.n, sgn (c i) * g P i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring

/-!
### Conversion between `Fin n` and `ℕ`-indexed sums
-/

/-- Lift an assembly to a function on `ℕ` (junk values outside `range n`). -/
def liftA (c : Assembly n) : ℕ → Bool := fun i ↦ if h : i < n then c ⟨i, h⟩ else false

lemma liftA_apply (c : Assembly n) (i : Fin n) : liftA c i.1 = c i := by
  obtain ⟨i, hi⟩ := i
  simp [liftA, hi]

lemma blackArea_range (c : Assembly P.n) :
    blackArea P c = ∑ i ∈ range P.n, ∑ j ∈ range P.n,
      (if i < j ∧ liftA c i ∧ liftA c j then wedge (u P i) (u P j) else 0) := by
  have hF : ∀ i : Fin P.n, (∑ j : Fin P.n, if i < j ∧ c i ∧ c j then wedge (u P i.1) (u P j.1) else 0)
      = ∑ j ∈ range P.n, (if i.1 < j ∧ liftA c i.1 ∧ liftA c j then wedge (u P i.1) (u P j) else 0) := by
    intro i
    have e : (∑ j : Fin P.n, if i < j ∧ c i ∧ c j then wedge (u P i.1) (u P j.1) else 0)
        = ∑ j : Fin P.n, (if i.1 < j.1 ∧ liftA c i.1 ∧ liftA c j.1 then wedge (u P i.1) (u P j.1)
          else 0) := by
      apply Finset.sum_congr rfl
      intro j _
      simp only [Fin.lt_def, liftA_apply]
    rw [e]
    exact Fin.sum_univ_eq_sum_range
      (fun j ↦ if i.1 < j ∧ liftA c i.1 ∧ liftA c j then wedge (u P i.1) (u P j) else 0) P.n
  calc blackArea P c
      = ∑ i : Fin P.n, ∑ j : Fin P.n, if i < j ∧ c i ∧ c j then wedge (u P i.1) (u P j.1) else 0 := rfl
    _ = ∑ i : Fin P.n, ∑ j ∈ range P.n,
          if i.1 < j ∧ liftA c i.1 ∧ liftA c j then wedge (u P i.1) (u P j) else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        exact hF i
    _ = ∑ i ∈ range P.n, ∑ j ∈ range P.n,
          if i < j ∧ liftA c i ∧ liftA c j then wedge (u P i) (u P j) else 0 :=
        Fin.sum_univ_eq_sum_range
          (fun i ↦ ∑ j ∈ range P.n, if i < j ∧ liftA c i ∧ liftA c j then wedge (u P i) (u P j)
            else 0) P.n

lemma whiteArea_range (c : Assembly P.n) :
    whiteArea P c = ∑ i ∈ range P.n, ∑ j ∈ range P.n,
      (if i < j ∧ ¬ liftA c i ∧ ¬ liftA c j then wedge (u P i) (u P j) else 0) := by
  have hF : ∀ i : Fin P.n, (∑ j : Fin P.n, if i < j ∧ ¬ c i ∧ ¬ c j then wedge (u P i.1) (u P j.1) else 0)
      = ∑ j ∈ range P.n, (if i.1 < j ∧ ¬ liftA c i.1 ∧ ¬ liftA c j then wedge (u P i.1) (u P j) else 0) := by
    intro i
    have e : (∑ j : Fin P.n, if i < j ∧ ¬ c i ∧ ¬ c j then wedge (u P i.1) (u P j.1) else 0)
        = ∑ j : Fin P.n, (if i.1 < j.1 ∧ ¬ liftA c i.1 ∧ ¬ liftA c j.1 then wedge (u P i.1) (u P j.1)
          else 0) := by
      apply Finset.sum_congr rfl
      intro j _
      simp only [Fin.lt_def, liftA_apply]
    rw [e]
    exact Fin.sum_univ_eq_sum_range
      (fun j ↦ if i.1 < j ∧ ¬ liftA c i.1 ∧ ¬ liftA c j then wedge (u P i.1) (u P j) else 0) P.n
  calc whiteArea P c
      = ∑ i : Fin P.n, ∑ j : Fin P.n, if i < j ∧ ¬ c i ∧ ¬ c j then wedge (u P i.1) (u P j.1) else 0 := rfl
    _ = ∑ i : Fin P.n, ∑ j ∈ range P.n,
          if i.1 < j ∧ ¬ liftA c i.1 ∧ ¬ liftA c j then wedge (u P i.1) (u P j) else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        exact hF i
    _ = ∑ i ∈ range P.n, ∑ j ∈ range P.n,
          if i < j ∧ ¬ liftA c i ∧ ¬ liftA c j then wedge (u P i) (u P j) else 0 :=
        Fin.sum_univ_eq_sum_range
          (fun i ↦ ∑ j ∈ range P.n, if i < j ∧ ¬ liftA c i ∧ ¬ liftA c j then wedge (u P i) (u P j)
            else 0) P.n

lemma areaDiff_fin (c : Assembly P.n) :
    blackArea P c - whiteArea P c = (1 / 2) * ∑ i : Fin P.n, sgn (c i) * g P i.1 := by
  rw [blackArea_range P c, whiteArea_range P c, areaDiff_range P (liftA c)]
  congr 1
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  rw [liftA_apply]

/-!
### The total sign of an assembly
-/

lemma sgn_sum {b : ℕ} (c : Assembly n) (hc : blackCount c = b) :
    ∑ i : Fin n, sgn (c i) = 2 * (b : ℝ) - n := by
  have hc' : (univ.filter fun i ↦ c i).card = b := hc
  have h1 : ∀ i ∈ univ.filter (fun i ↦ c i), sgn (c i) = (1 : ℝ) := by
    intro i hi
    rw [Finset.mem_filter] at hi
    have h : c i = true := hi.2
    simp [sgn, h]
  have h2 : ∀ i ∈ univ.filter (fun i ↦ ¬ c i), sgn (c i) = (-1 : ℝ) := by
    intro i hi
    rw [Finset.mem_filter] at hi
    have h3 : c i = false := by simpa using hi.2
    simp [sgn, h3]
  have e : ∑ i : Fin n, sgn (c i)
      = (∑ i ∈ univ.filter (fun i ↦ c i), (1 : ℝ)) +
        (∑ i ∈ univ.filter (fun i ↦ ¬ c i), (-1 : ℝ)) := by
    rw [← Finset.sum_filter_add_sum_filter_not univ (fun i ↦ c i) (fun i ↦ sgn (c i))]
    rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2]
  rw [e]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  have hcard : (univ.filter fun i ↦ ¬ c i).card = n - b := by
    have h := Finset.card_filter_add_card_filter_not (fun i ↦ c i) (s := univ)
    rw [hc', Finset.card_univ, Fintype.card_fin] at h
    omega
  rw [hcard, hc']
  have hbn : b ≤ n := by
    rw [← hc']
    calc (univ.filter fun i ↦ c i).card ≤ univ.card := Finset.card_filter_le _ _
    _ = n := by simp
  rw [Nat.cast_sub hbn]
  ring

/-!
### Evaluation of the difference of the areas
-/

lemma areaDiff_eval {b w : ℕ} (hPn : P.n = b + w) (hω : P.ω ^ P.n = -1) (hζ : ‖P.ζ‖ = 1)
    (c : Assembly P.n) (hc : blackCount c = b) :
    blackArea P c - whiteArea P c = ((b : ℝ) - w) / 2 * g P 0 := by
  rw [areaDiff_fin P c]
  have hg : ∀ i : Fin P.n, g P i.1 = g P 0 :=
    fun i ↦ g_const P hω hζ i.1 (by have hi := i.2; omega)
  have e : ∑ i : Fin P.n, sgn (c i) * g P i.1 = g P 0 * ∑ i : Fin P.n, sgn (c i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hg i]
    ring
  rw [e, sgn_sum c hc, hPn]
  push_cast
  ring

snip end

/-- **USAMO 2022, Problem 2.**  The difference of the areas of the black
polygon `B` and the white polygon `W` does not depend on the assembly:
any two assemblies with the same numbers of rods give the same difference. -/
problem usa2022_p2 {b w : ℕ} (_hb : 2 ≤ b) (_hw : 2 ≤ w) (hPn : P.n = b + w)
    (hω : P.ω ^ P.n = -1) (hζ : ‖P.ζ‖ = 1) (c c' : Assembly P.n)
    (hc : blackCount c = b) (hc' : blackCount c' = b) :
    blackArea P c - whiteArea P c = blackArea P c' - whiteArea P c' := by
  rw [areaDiff_eval P hPn hω hζ c hc, areaDiff_eval P hPn hω hζ c' hc']

end

end Usa2022P2
