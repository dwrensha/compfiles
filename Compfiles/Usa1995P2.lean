/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Algebra] }

/-!
# USA Mathematical Olympiad 1995, Problem 2

A trigonometric map is any one of sin, cos, tan, arcsin, arccos and arctan.
Show that given any positive rational number x, one can find a finite
sequence of trigonometric maps which take 0 to x. [So we need to show that
we can always find a sequence of trigonometric maps tᵢ so that:
x₁ = t₀(0), x₂ = t₁(x₁), ..., xₙ = tₙ₋₁(xₙ₋₁), x = tₙ(xₙ).]
-/

namespace Usa1995P2

/-- The six trigonometric maps allowed by the problem. -/
inductive TrigMap where
  | sin | cos | tan | arcsin | arccos | arctan

/-- Evaluate a trigonometric map at a real number. -/
noncomputable def TrigMap.apply : TrigMap → ℝ → ℝ
  | .sin => Real.sin
  | .cos => Real.cos
  | .tan => Real.tan
  | .arcsin => Real.arcsin
  | .arccos => Real.arccos
  | .arctan => Real.arctan

/-- Apply a finite sequence of trigonometric maps to a starting value. -/
noncomputable def run (l : List TrigMap) (x : ℝ) : ℝ := l.foldl (fun a f => f.apply a) x

snip begin

lemma run_append (l₁ l₂ : List TrigMap) (x : ℝ) :
    run (l₁ ++ l₂) x = run l₂ (run l₁ x) := by
  simp only [run, List.foldl_append]

/-- The chain `arctan, sin, arccos, tan` of trigonometric maps.
We show in `run_chainInv` that it sends any positive `x` to `1 / x`. -/
def chainInv : List TrigMap := [.arctan, .sin, .arccos, .tan]

/-- The chain `arctan, cos, arctan, sin, arccos, tan` of trigonometric maps.
We show in `run_chainSqrt` that it sends any real `x` to `√(1 + x²)`. -/
def chainSqrt : List TrigMap := [.arctan, .cos, .arctan, .sin, .arccos, .tan]

/-- The chain `arctan, sin, arccos, tan` sends `x` to `1 / x`: with
`t = arctan x` we have `sin t = x / √(1 + x²)`, and if `u = arccos (sin t)`
then `tan u = sin u / cos u = √(1 - x²/(1+x²)) / (x/√(1+x²)) = 1 / x`. -/
lemma run_chainInv (x : ℝ) (hx : 0 < x) : run chainInv x = 1 / x := by
  have hc : (0 : ℝ) < √(1 + x ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hxc : x < √(1 + x ^ 2) := by
    rw [Real.lt_sqrt hx.le]
    linarith [sq_nonneg x]
  have hs1 : x / √(1 + x ^ 2) ≤ 1 := (div_le_one hc).2 hxc.le
  have hs0 : (-1 : ℝ) ≤ x / √(1 + x ^ 2) := by
    have h := div_nonneg hx.le (Real.sqrt_nonneg (1 + x ^ 2))
    linarith
  have h1 : (1 : ℝ) - (x / √(1 + x ^ 2)) ^ 2 = (1 / √(1 + x ^ 2)) ^ 2 := by
    have hsq : (√(1 + x ^ 2)) ^ 2 = 1 + x ^ 2 := Real.sq_sqrt (by positivity)
    rw [div_pow, div_pow, one_pow, hsq, sub_eq_iff_eq_add, ← add_div,
      div_self (by positivity : (1 : ℝ) + x ^ 2 ≠ 0)]
  show Real.tan (Real.arccos (Real.sin (Real.arctan x))) = 1 / x
  rw [Real.tan_eq_sin_div_cos, Real.sin_arctan, Real.sin_arccos, Real.cos_arccos hs0 hs1,
    h1, Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 1 / √(1 + x ^ 2))]
  have hne : √(1 + x ^ 2) ≠ 0 := hc.ne'
  have hx' : x ≠ 0 := ne_of_gt hx
  field_simp

/-- The chain `arctan, cos, arctan, sin, arccos, tan` sends `x` to `√(1 + x²)`:
it is the previous chain applied to `cos (arctan x) = 1 / √(1 + x²)`. -/
lemma run_chainSqrt (x : ℝ) : run chainSqrt x = √(1 + x ^ 2) := by
  have h : run chainSqrt x = run chainInv (Real.cos (Real.arctan x)) := rfl
  rw [h, run_chainInv _ (Real.cos_arctan_pos x), Real.cos_arctan, one_div_one_div]

/-- Every number of the form `√(m / n)` with `m, n` positive naturals can be
reached from `0` by a finite sequence of trigonometric maps.
Proof by well-founded induction on `m + n` (Euclidean algorithm):
- if `m = n` then `√(m/n) = 1 = cos 0`;
- if `m > n` then `√(m/n) = √(1 + (√((m-n)/n))²)` and `(m-n) + n < m + n`;
- if `m < n` then `√(m/n) = 1 / √(n/m)` and `√(n/m) = √(1 + (√((n-m)/m))²)`
  with `(n-m) + m < m + n`. -/
lemma reachable_sqrt_div (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    ∃ l : List TrigMap, run l 0 = √((m : ℝ) / n) := by
  rcases lt_trichotomy m n with hlt | heq | hgt
  · -- case `m < n`: reach `√((n-m)/m)`, apply `chainSqrt`, then `chainInv`
    obtain ⟨l, hl⟩ := reachable_sqrt_div (n - m) m (Nat.sub_pos_of_lt hlt) hm
    have hcast : ((n - m : ℕ) : ℝ) = (n : ℝ) - m := Nat.cast_sub hlt.le
    have hpos : (0 : ℝ) < √(1 + ((n - m : ℕ) : ℝ) / m) := Real.sqrt_pos.2 (by positivity)
    refine ⟨l ++ chainSqrt ++ chainInv, ?_⟩
    rw [run_append, run_append, hl, run_chainSqrt,
      Real.sq_sqrt (show (0 : ℝ) ≤ ((n - m : ℕ) : ℝ) / m by positivity),
      run_chainInv _ hpos, hcast]
    have h2 : (1 : ℝ) + ((n : ℝ) - m) / m = (n : ℝ) / m := by
      have hm' : (m : ℝ) ≠ 0 := by positivity
      field_simp
      ring
    rw [h2, Real.sqrt_div' (n : ℝ) (Nat.cast_nonneg m),
      Real.sqrt_div' (m : ℝ) (Nat.cast_nonneg n), one_div_div]
  · -- case `m = n`: `√(m/n) = 1 = cos 0`
    subst heq
    refine ⟨[.cos], ?_⟩
    have hm' : (m : ℝ) ≠ 0 := by positivity
    rw [div_self hm', Real.sqrt_one]
    exact Real.cos_zero
  · -- case `m > n`: reach `√((m-n)/n)` and apply `chainSqrt`
    obtain ⟨l, hl⟩ := reachable_sqrt_div (m - n) n (Nat.sub_pos_of_lt hgt) hn
    have hcast : ((m - n : ℕ) : ℝ) = (m : ℝ) - n := Nat.cast_sub hgt.le
    refine ⟨l ++ chainSqrt, ?_⟩
    rw [run_append, hl, run_chainSqrt,
      Real.sq_sqrt (show (0 : ℝ) ≤ ((m - n : ℕ) : ℝ) / n by positivity), hcast]
    have h2 : (1 : ℝ) + ((m : ℝ) - n) / n = (m : ℝ) / n := by
      have hn' : (n : ℝ) ≠ 0 := by positivity
      field_simp
      ring
    rw [h2]
termination_by m + n
decreasing_by
  · lia
  · lia

snip end

problem usa1995_p2 (x : ℚ) (hx : 0 < x) :
    ∃ l : List TrigMap, run l 0 = (x : ℝ) := by
  have hnum : 0 < x.num := Rat.num_pos.2 hx
  have hm2 : 0 < x.num.toNat ^ 2 := pow_pos (by lia) 2
  obtain ⟨l, hl⟩ := reachable_sqrt_div (x.num.toNat ^ 2) (x.den ^ 2) hm2 (pow_pos x.den_pos 2)
  refine ⟨l, ?_⟩
  rw [hl]
  have hmn : ((x.num.toNat : ℝ) / (x.den : ℝ)) = (x : ℝ) := by
    have hcast : ((x.num.toNat : ℝ)) = (x.num : ℝ) := by
      norm_cast
      exact Int.toNat_of_nonneg hnum.le
    rw [hcast]
    conv_rhs => rw [← Rat.num_div_den x]
    norm_cast
  have h2 : (((x.num.toNat ^ 2 : ℕ) : ℝ) / ((x.den ^ 2 : ℕ) : ℝ)) = (x : ℝ) ^ 2 := by
    push_cast
    rw [← div_pow, hmn]
  rw [h2, Real.sqrt_sq (Rat.cast_nonneg.2 hx.le)]

end Usa1995P2
