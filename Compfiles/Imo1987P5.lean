/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Tactic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.NumberTheory.Real.Irrational
public import ProblemExtraction

@[expose] public section

problem_file {
  tags := [.Combinatorics, .Geometry]
}

/-!
# International Mathematical Olympiad 1987, Problem 5

Let n be an integer greater than or equal to 3. Prove that there is a set
of n points in the plane such that the distance between any two points is
irrational and each set of 3 points determines a non-degenerate triangle
with rational area.
-/

namespace Imo1987P5

/-- The Euclidean plane. -/
abbrev Pt := EuclideanSpace ℝ (Fin 2)

/-- The area of the triangle with vertices `p`, `q`, `r`,
given by the shoelace formula. -/
noncomputable def area (p q r : Pt) : ℝ :=
  |(q 0 - p 0) * (r 1 - p 1) - (q 1 - p 1) * (r 0 - p 0)| / 2

snip begin

/-- The point `(k, k²)` on the parabola `y = x²`. -/
def parPt (k : ℕ) : Pt := !₂[(k : ℝ), (k : ℝ)^2]

/-- The coordinates of `parPt k`. -/
lemma parPt_apply (k : ℕ) : parPt k 0 = (k : ℝ) ∧ parPt k 1 = (k : ℝ)^2 := by
  simp [parPt, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- `parPt` is injective: the first coordinate recovers `k`. -/
lemma parPt_inj : Function.Injective parPt := by
  intro a b hab
  have h0 : (parPt a) 0 = (parPt b) 0 := by rw [hab]
  rw [(parPt_apply a).1, (parPt_apply b).1] at h0
  exact Nat.cast_injective h0

/-- For `0 < m`, the natural number `1 + m²` lies strictly between `m²` and
`(m+1)²`, so it is not a perfect square. -/
lemma not_isSquare_one_add_sq {m : ℕ} (hm : 0 < m) : ¬ IsSquare (1 + m^2) := by
  rintro ⟨r, hr⟩
  rw [pow_two] at hr
  have h1 : m * m < r * r := by
    rw [← hr]; omega
  have h2 : r * r < (m + 1) * (m + 1) := by
    rw [← hr]
    have e : (m + 1) * (m + 1) = m * m + 2 * m + 1 := by ring
    rw [e]; omega
  have h3 : m < r := Nat.mul_self_lt_mul_self_iff.mp h1
  have h4 : r < m + 1 := Nat.mul_self_lt_mul_self_iff.mp h2
  omega

/-- The square root of `1 + m²` is irrational for `0 < m`. -/
lemma irrational_sqrt_one_add_sq {m : ℕ} (hm : 0 < m) :
    Irrational (√((1 + m^2 : ℕ) : ℝ)) :=
  irrational_sqrt_natCast_iff.mpr (not_isSquare_one_add_sq hm)

/-- The distance between the points `(a, a²)` and `(b, b²)` equals
`|a - b| * √(1 + (a+b)²)`. -/
lemma dist_parPt (a b : ℕ) :
    dist (parPt a) (parPt b) = |(a : ℝ) - b| * √(1 + ((a : ℝ) + b)^2) := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two]
  rw [(parPt_apply a).1, (parPt_apply a).2, (parPt_apply b).1, (parPt_apply b).2]
  rw [Real.dist_eq, Real.dist_eq, sq_abs, sq_abs]
  rw [show ((a : ℝ) - b)^2 + ((a : ℝ)^2 - (b : ℝ)^2)^2 =
      ((a : ℝ) - b)^2 * (1 + ((a : ℝ) + b)^2) from by ring]
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

/-- The distance between two distinct points `(a, a²)`, `(b, b²)` with
`0 < a` is irrational. -/
lemma irrational_dist_parPt {a b : ℕ} (ha : 0 < a) (hab : a ≠ b) :
    Irrational (dist (parPt a) (parPt b)) := by
  have hd' : |(a : ℝ) - b| = ((Int.natAbs ((a : ℤ) - b) : ℕ) : ℝ) := by
    have h1 : (a : ℝ) - b = (((a : ℤ) - b : ℤ) : ℝ) := by push_cast; ring
    rw [h1, ← Int.cast_abs (R := ℝ), ← Int.natCast_natAbs, Int.cast_natCast]
  have hm' : (1 : ℝ) + ((a : ℝ) + b)^2 = ((1 + (a + b)^2 : ℕ) : ℝ) := by
    push_cast; ring
  have hdm : Int.natAbs ((a : ℤ) - b) ≠ 0 := by
    have hz : ((a : ℤ) - b) ≠ 0 := by
      rw [sub_ne_zero]
      exact_mod_cast hab
    exact mt Int.natAbs_eq_zero.mp hz
  rw [dist_parPt, hd', hm']
  exact (irrational_sqrt_one_add_sq (Nat.add_pos_left ha b)).natCast_mul hdm

/-- The shoelace expression of three parabola points equals the integer
`(b - a)(c - a)(c - b)`. -/
lemma shoelace_parPt (a b c : ℕ) :
    (parPt b 0 - parPt a 0) * (parPt c 1 - parPt a 1) -
      (parPt b 1 - parPt a 1) * (parPt c 0 - parPt a 0) =
      (↑(((b : ℤ) - a) * ((c : ℤ) - a) * ((c : ℤ) - b)) : ℝ) := by
  rw [(parPt_apply a).1, (parPt_apply a).2, (parPt_apply b).1, (parPt_apply b).2,
    (parPt_apply c).1, (parPt_apply c).2]
  push_cast
  ring

/-- The shoelace expression of three distinct parabola points is nonzero. -/
lemma shoelace_parPt_ne_zero {a b c : ℕ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (parPt b 0 - parPt a 0) * (parPt c 1 - parPt a 1) -
      (parPt b 1 - parPt a 1) * (parPt c 0 - parPt a 0) ≠ 0 := by
  rw [shoelace_parPt]
  have h1 : ((b : ℤ) - a) ≠ 0 := by
    rw [sub_ne_zero]
    exact_mod_cast hab.symm
  have h2 : ((c : ℤ) - a) ≠ 0 := by
    rw [sub_ne_zero]
    exact_mod_cast hac.symm
  have h3 : ((c : ℤ) - b) ≠ 0 := by
    rw [sub_ne_zero]
    exact_mod_cast hbc.symm
  simp only [Int.cast_ne_zero]
  exact mul_ne_zero (mul_ne_zero h1 h2) h3

/-- Three distinct parabola points are not collinear. -/
lemma not_collinear_parPt {a b c : ℕ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ¬ Collinear ℝ {parPt a, parPt b, parPt c} := by
  intro hcol
  rw [collinear_iff_of_mem (Set.mem_insert (parPt a) {parPt b, parPt c})] at hcol
  obtain ⟨v, hv⟩ := hcol
  obtain ⟨t₁, ht₁⟩ := hv (parPt b)
    (Set.mem_insert_of_mem _ (Set.mem_insert (parPt b) {parPt c}))
  obtain ⟨t₂, ht₂⟩ := hv (parPt c)
    (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton (parPt c))))
  rw [vadd_eq_add] at ht₁ ht₂
  have hsub₁ : parPt b - parPt a = t₁ • v := sub_eq_iff_eq_add.mpr ht₁
  have hsub₂ : parPt c - parPt a = t₂ • v := sub_eq_iff_eq_add.mpr ht₂
  have hz := shoelace_parPt_ne_zero hab hac hbc
  apply hz
  simp only [← PiLp.sub_apply]
  rw [hsub₁, hsub₂]
  simp only [PiLp.smul_apply, smul_eq_mul]
  ring

/-- The area of the triangle determined by three parabola points is rational. -/
lemma rational_area_parPt (a b c : ℕ) :
    ∃ q : ℚ, area (parPt a) (parPt b) (parPt c) = q := by
  refine ⟨(|↑(((b : ℤ) - a) * ((c : ℤ) - a) * ((c : ℤ) - b))|) / 2, ?_⟩
  unfold area
  rw [shoelace_parPt, ← Int.cast_abs (R := ℝ), ← Int.cast_abs (R := ℚ)]
  push_cast
  ring

snip end

problem imo1987_p5 (n : ℕ) (hn : 3 ≤ n) :
    ∃ s : Finset Pt, s.card = n ∧
      (∀ p ∈ s, ∀ q ∈ s, p ≠ q → Irrational (dist p q)) ∧
      ∀ p ∈ s, ∀ q ∈ s, ∀ r ∈ s, p ≠ q → p ≠ r → q ≠ r →
        ¬ Collinear ℝ {p, q, r} ∧ ∃ a : ℚ, area p q r = a := by
  refine ⟨(Finset.Icc 1 n).image parPt, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ parPt_inj, Nat.card_Icc]
    omega
  · intro p hp q hq hpq
    rw [Finset.mem_image] at hp hq
    obtain ⟨a, ha, rfl⟩ := hp
    obtain ⟨b, hb, rfl⟩ := hq
    rw [Finset.mem_Icc] at ha hb
    have hab : a ≠ b := fun h => hpq (by rw [h])
    exact irrational_dist_parPt ha.1 hab
  · intro p hp q hq r hr hpq hpr hqr
    rw [Finset.mem_image] at hp hq hr
    obtain ⟨a, ha, rfl⟩ := hp
    obtain ⟨b, hb, rfl⟩ := hq
    obtain ⟨c, hc, rfl⟩ := hr
    have hab : a ≠ b := fun h => hpq (by rw [h])
    have hac : a ≠ c := fun h => hpr (by rw [h])
    have hbc : b ≠ c := fun h => hqr (by rw [h])
    exact ⟨not_collinear_parPt hab hac hbc, rational_area_parPt a b c⟩

end Imo1987P5
