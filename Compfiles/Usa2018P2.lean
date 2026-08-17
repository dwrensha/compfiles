/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.EuclideanDomain.Basic
public import Mathlib.Algebra.EuclideanDomain.Field
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Tactic.IntervalCases
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Algebra] }

/-!
# United States of America Mathematical Olympiad 2018, Problem 2

Find all functions $f : (0, \infty) \to (0, \infty)$ such that
$$f\left(x + \frac{1}{y}\right) + f\left(y + \frac{1}{z}\right) +
  f\left(z + \frac{1}{x}\right) = 1$$
for all $x, y, z > 0$ with $xyz = 1$.
-/

namespace Usa2018P2

snip begin

/-- If `h` satisfies Jensen's functional equation on `[0, 1]`, vanishes at the
endpoints and is bounded there, then `h` is identically zero on `[0, 1]`. -/
theorem jensen_bounded_eq_zero {h : ℝ → ℝ}
    (hJ : ∀ s t : ℝ, 0 ≤ s → s ≤ 1 → 0 ≤ t → t ≤ 1 → h ((s + t) / 2) = (h s + h t) / 2)
    (h0 : h 0 = 0) (h1 : h 1 = 0)
    (hb : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → |h t| ≤ 1) :
    ∀ t : ℝ, 0 ≤ t → t ≤ 1 → h t = 0 := by
  -- Step 1: `h` vanishes at dyadic rationals `k / 2 ^ n` in `[0, 1]`.
  have hdy : ∀ n : ℕ, ∀ k : ℕ, k ≤ 2 ^ n → h ((k : ℝ) / 2 ^ n) = 0 := by
    intro n
    induction n with
    | zero =>
      intro k hk
      rw [pow_zero] at hk
      interval_cases k
      · simpa using h0
      · simpa using h1
    | succ n ih =>
      intro k hk
      rcases Nat.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
      · have hjj : (((j + j : ℕ) : ℝ)) / 2 ^ (n + 1) = (j : ℝ) / 2 ^ n := by
          push_cast
          rw [pow_succ, div_eq_div_iff (by positivity : (2 : ℝ) ^ n * 2 ≠ 0)
            (by positivity : (2 : ℝ) ^ n ≠ 0)]
          ring
        rw [hjj]
        apply ih
        rw [pow_succ] at hk
        lia
      · have hjj : (((2 * j + 1 : ℕ) : ℝ)) / 2 ^ (n + 1)
            = (((j : ℝ) / 2 ^ n) + (((j + 1 : ℕ) : ℝ) / 2 ^ n)) / 2 := by
          push_cast
          rw [pow_succ, ← add_div, div_div]
          ring
        rw [hjj]
        have hj1 : j + 1 ≤ 2 ^ n := by
          rw [pow_succ] at hk
          lia
        have hj : j ≤ 2 ^ n := le_trans (Nat.le_succ j) hj1
        have h2n : (0 : ℝ) < 2 ^ n := by positivity
        have hja : (0 : ℝ) ≤ (j : ℝ) / 2 ^ n := by positivity
        have hjb : (j : ℝ) / 2 ^ n ≤ 1 := by
          rw [div_le_one h2n]
          exact_mod_cast hj
        have hka : (0 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) / 2 ^ n := by positivity
        have hkb : ((j + 1 : ℕ) : ℝ) / 2 ^ n ≤ 1 := by
          rw [div_le_one h2n]
          exact_mod_cast hj1
        rw [hJ _ _ hja hjb hka hkb, ih j hj, ih (j + 1) hj1]
        norm_num
  -- Step 2: shifting by `1 / 2 ^ n` does not change the value of `h`.
  have hshift1 : ∀ (t : ℝ) (n : ℕ), 0 ≤ t → t + 1 / 2 ^ n ≤ 1 →
      h (t + 1 / 2 ^ n) = h t := by
    intro t n ht0 ht1
    have h2n : (0 : ℝ) < 2 ^ n := by positivity
    have h1le : (1 : ℕ) ≤ 2 ^ n := Nat.one_le_pow n 2 (by norm_num)
    have hd : h (1 / 2 ^ n) = 0 := by
      have hh := hdy n 1 h1le
      rwa [Nat.cast_one] at hh
    have ha : (0 : ℝ) ≤ 1 / 2 ^ n := by positivity
    have hb1 : (1 : ℝ) / 2 ^ n ≤ 1 := by
      rw [div_le_one h2n]
      exact_mod_cast h1le
    have ht1' : t ≤ 1 := by linarith
    have e1 := hJ t (1 / 2 ^ n) ht0 ht1' ha hb1
    have e2 := hJ (t + 1 / 2 ^ n) 0 (add_nonneg ht0 ha) ht1 le_rfl zero_le_one
    rw [add_zero] at e2
    rw [hd] at e1
    rw [h0] at e2
    linarith
  -- Step 3: shifting by `j / 2 ^ n` does not change the value of `h`.
  have hshift : ∀ (n j : ℕ) (t : ℝ), 0 ≤ t → t + (j : ℝ) / 2 ^ n ≤ 1 →
      h (t + (j : ℝ) / 2 ^ n) = h t := by
    intro n j
    induction j with
    | zero =>
      intro t _ _
      simp
    | succ j ih =>
      intro t ht0 ht1
      have hdecomp : t + ((j + 1 : ℕ) : ℝ) / 2 ^ n
          = (t + (j : ℝ) / 2 ^ n) + 1 / 2 ^ n := by
        push_cast
        rw [add_div]
        ring
      have ha : (0 : ℝ) ≤ 1 / 2 ^ n := by positivity
      have hj0 : (0 : ℝ) ≤ (j : ℝ) / 2 ^ n := by positivity
      have ht1a : (t + (j : ℝ) / 2 ^ n) + 1 / 2 ^ n ≤ 1 := by
        rw [← hdecomp]
        exact ht1
      have ht1b : t + (j : ℝ) / 2 ^ n ≤ 1 := by linarith
      rw [hdecomp]
      rw [hshift1 (t + (j : ℝ) / 2 ^ n) n (add_nonneg ht0 hj0) ht1a]
      exact ih t ht0 ht1b
  -- Step 4: doubling.
  have hdouble : ∀ t : ℝ, 0 ≤ t → 2 * t ≤ 1 → h (2 * t) = 2 * h t := by
    intro t ht0 ht1
    have ht0' : (0:ℝ) ≤ 2 * t := by linarith
    have e := hJ (2 * t) 0 ht0' ht1 le_rfl zero_le_one
    rw [add_zero] at e
    rw [h0] at e
    have h2t : 2 * t / 2 = t := mul_div_cancel_left₀ t (by norm_num : (2 : ℝ) ≠ 0)
    rw [h2t] at e
    linarith
  -- Step 5: iterated doubling.
  have hpow : ∀ (m : ℕ) (u : ℝ), 0 ≤ u → 2 ^ m * u ≤ 1 →
      h (2 ^ m * u) = 2 ^ m * h u := by
    intro m
    induction m with
    | zero =>
      intro u _ _
      simp
    | succ m ih =>
      intro u hu0 hu1
      have h2m0 : (0 : ℝ) ≤ 2 ^ m := by positivity
      have h2mu : (0 : ℝ) ≤ 2 ^ m * u := mul_nonneg h2m0 hu0
      have hdecomp : (2 : ℝ) ^ (m + 1) * u = 2 * (2 ^ m * u) := by
        rw [pow_succ]
        ring
      rw [hdecomp] at hu1 ⊢
      have hle : 2 ^ m * u ≤ 1 := by linarith
      rw [hdouble (2 ^ m * u) h2mu hu1, ih u hu0 hle, pow_succ]
      ring
  -- Step 6: conclusion by contradiction.
  intro t ht0 ht1
  by_contra hc
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (1 / |h t|) (by norm_num : (1 : ℝ) < 2)
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  have h2n0 : (0 : ℝ) ≤ 2 ^ n := le_of_lt h2n
  have hKle : (⌊2 ^ n * t⌋₊ : ℝ) ≤ 2 ^ n * t := Nat.floor_le (mul_nonneg h2n0 ht0)
  have hKlt : 2 ^ n * t < (⌊2 ^ n * t⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  set u := t - (⌊2 ^ n * t⌋₊ : ℝ) / 2 ^ n with hu
  have hu0 : 0 ≤ u := by
    rw [hu, sub_nonneg, div_le_iff₀ h2n]
    linarith
  have hu1' : u * 2 ^ n < 1 := by
    rw [hu, sub_mul, div_mul_cancel₀ _ (ne_of_gt h2n)]
    linarith
  have hu1 : u < 1 / 2 ^ n := by
    rw [lt_div_iff₀ h2n]
    exact hu1'
  have htu : h t = h u := by
    have hteq : t = u + (⌊2 ^ n * t⌋₊ : ℝ) / 2 ^ n := by
      rw [hu]
      ring
    rw [hteq]
    exact hshift n ⌊2 ^ n * t⌋₊ u hu0 (by linarith)
  have hune : u ≠ 0 := fun hu0' ↦ hc (by rw [htu, hu0', h0])
  have hupos : 0 < u := lt_of_le_of_ne hu0 (Ne.symm hune)
  have h2nu : 2 ^ n * u ≤ 1 := by linarith
  have hfinal := hpow n u (le_of_lt hupos) h2nu
  rw [← htu] at hfinal
  have hb2 := hb (2 ^ n * u) (mul_nonneg h2n0 (le_of_lt hupos)) h2nu
  rw [hfinal] at hb2
  rw [abs_mul, abs_of_pos h2n] at hb2
  have hapos : (0 : ℝ) < |h t| := abs_pos.mpr hc
  rw [div_lt_iff₀ hapos] at hn
  linarith

/-- The normalized function $g(s) = f(1/s - 1)$, mapping $(0, 1)$ to $(0, 1)$. -/
noncomputable def g (f : ℝ → ℝ) : ℝ → ℝ := fun s ↦ f (1 / s - 1)

/-- The discrepancy between `g` and its linear interpolant on `[1/8, 3/8]`,
rescaled to parameters in `[0, 1]`. -/
noncomputable def hfn (f : ℝ → ℝ) : ℝ → ℝ := fun t ↦
  g f ((2 * t + 1) / 8) - (1 - t) * g f (1 / 8) - t * g f (3 / 8)

variable {f : ℝ → ℝ}
variable (fpos : ∀ x : ℝ, 0 < x → 0 < f x)
variable (fe : ∀ x y z : ℝ, 0 < x → 0 < y → 0 < z → x * y * z = 1 →
  f (x + 1 / y) + f (y + 1 / z) + f (z + 1 / x) = 1)

include fpos fe in
/-- Every value `f t` with `t > 0` is less than `1`
(plug `(x, y, z) = (t / 2, 2 / t, 1)` into the equation). -/
theorem f_lt_one {t : ℝ} (ht : 0 < t) : f t < 1 := by
  have ht0 : t ≠ 0 := ne_of_gt ht
  have hxyz : t / 2 * (2 / t) * 1 = 1 := by field_simp
  have h := fe (t / 2) (2 / t) 1 (by positivity) (by positivity) one_pos hxyz
  rw [show t / 2 + 1 / (2 / t) = t by rw [one_div_div]; ring] at h
  have e1 := fpos (2 / t + 1 / (1 : ℝ)) (by positivity)
  have e2 := fpos (1 + 1 / (t / 2)) (by positivity)
  linarith

/-- For `s ∈ (0, 1)` the argument `1 / s - 1` of `f` in `g` is positive. -/
theorem arg_pos {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) : 0 < 1 / s - 1 := by
  have h : (1:ℝ) < 1 / s := by rwa [one_lt_div hs0]
  linarith

include fpos in
theorem g_pos {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) : 0 < g f s := by
  exact fpos _ (arg_pos hs0 hs1)

include fpos fe in
theorem g_lt_one {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) : g f s < 1 := by
  exact f_lt_one fpos fe (arg_pos hs0 hs1)

include fe in
/-- The functional equation rewritten in terms of `g` via the substitution
`(x, y, z) = (b / c, c / a, a / b)`. -/
theorem g_eq {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    g f (a / (a + b + c)) + g f (b / (a + b + c)) + g f (c / (a + b + c)) = 1 := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hb0 : b ≠ 0 := ne_of_gt hb
  have hc0 : c ≠ 0 := ne_of_gt hc
  have habc0 : a + b + c ≠ 0 := ne_of_gt (by positivity)
  have hxyz : b / c * (c / a) * (a / b) = 1 := by field_simp
  have h := fe (b / c) (c / a) (a / b) (by positivity) (by positivity) (by positivity) hxyz
  have e1 : g f (c / (a + b + c)) = f (b / c + 1 / (c / a)) := by
    show f (1 / (c / (a + b + c)) - 1) = f (b / c + 1 / (c / a))
    congr 1
    field_simp
    ring
  have e2 : g f (a / (a + b + c)) = f (c / a + 1 / (a / b)) := by
    show f (1 / (a / (a + b + c)) - 1) = f (c / a + 1 / (a / b))
    congr 1
    field_simp
    ring
  have e3 : g f (b / (a + b + c)) = f (a / b + 1 / (b / c)) := by
    show f (1 / (b / (a + b + c)) - 1) = f (a / b + 1 / (b / c))
    congr 1
    field_simp
    ring
  rw [e1, e2, e3]
  linarith [h]

include fe in
/-- For `a + b + c = 1` this reads `g a + g b + g c = 1`. -/
theorem g_eq_one {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hsum : a + b + c = 1) : g f a + g f b + g f c = 1 := by
  have h := g_eq fe ha hb hc
  rwa [hsum, div_one, div_one, div_one] at h

include fe in
/-- Jensen's functional equation for `g` on pairs summing to less than `1`. -/
theorem g_jensen {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a + b < 1) :
    g f a + g f b = 2 * g f ((a + b) / 2) := by
  have hc : (0:ℝ) < 1 - a - b := by linarith
  have h1 := g_eq_one fe ha hb hc (by ring)
  have h2 := g_eq_one fe (by positivity : (0:ℝ) < (a + b) / 2) (by positivity : (0:ℝ) < (a + b) / 2) hc (by ring)
  linarith

theorem hfn_zero : hfn f 0 = 0 := by
  have e : (2 * (0:ℝ) + 1) / 8 = 1 / 8 := by norm_num
  show g f ((2 * (0:ℝ) + 1) / 8) - (1 - 0) * g f (1 / 8) - 0 * g f (3 / 8) = 0
  rw [e]
  ring

theorem hfn_one : hfn f 1 = 0 := by
  have e : (2 * (1:ℝ) + 1) / 8 = 3 / 8 := by norm_num
  show g f ((2 * (1:ℝ) + 1) / 8) - (1 - 1) * g f (1 / 8) - 1 * g f (3 / 8) = 0
  rw [e]
  ring

include fe in
theorem hfn_jensen {s t : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    hfn f ((s + t) / 2) = (hfn f s + hfn f t) / 2 := by
  have hs : (0:ℝ) < (2 * s + 1) / 8 := by
    have h2s : (0:ℝ) < 2 * s + 1 := by linarith
    positivity
  have ht : (0:ℝ) < (2 * t + 1) / 8 := by
    have h2t : (0:ℝ) < 2 * t + 1 := by linarith
    positivity
  have hst : (2 * s + 1) / 8 + (2 * t + 1) / 8 < 1 := by linarith
  have key := g_jensen fe hs ht hst
  have e : ((2 * s + 1) / 8 + (2 * t + 1) / 8) / 2 = (2 * ((s + t) / 2) + 1) / 8 := by ring
  rw [e] at key
  simp only [hfn]
  linarith [key]

include fpos fe in
theorem hfn_bdd {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : |hfn f t| ≤ 1 := by
  have hu0 : (0:ℝ) < (2 * t + 1) / 8 := by
    have h2t : (0:ℝ) < 2 * t + 1 := by linarith
    positivity
  have hu1 : (2 * t + 1) / 8 < 1 := by linarith
  have gu0 := g_pos fpos hu0 hu1
  have gu1 := g_lt_one fpos fe hu0 hu1
  have gA0 := g_pos fpos (by norm_num : (0:ℝ) < 1 / 8) (by norm_num : (1:ℝ) / 8 < 1)
  have gA1 := g_lt_one fpos fe (by norm_num : (0:ℝ) < 1 / 8) (by norm_num : (1:ℝ) / 8 < 1)
  have gB0 := g_pos fpos (by norm_num : (0:ℝ) < 3 / 8) (by norm_num : (3:ℝ) / 8 < 1)
  have gB1 := g_lt_one fpos fe (by norm_num : (0:ℝ) < 3 / 8) (by norm_num : (3:ℝ) / 8 < 1)
  have mA : (1 - t) * g f (1 / 8) ≤ 1 - t := by
    have hm := mul_le_mul_of_nonneg_left gA1.le (by linarith : (0:ℝ) ≤ 1 - t)
    rwa [mul_one] at hm
  have mB : t * g f (3 / 8) ≤ t := by
    have hm := mul_le_mul_of_nonneg_left gB1.le ht0
    rwa [mul_one] at hm
  have pA : (0:ℝ) ≤ (1 - t) * g f (1 / 8) := mul_nonneg (by linarith) gA0.le
  have pB : (0:ℝ) ≤ t * g f (3 / 8) := mul_nonneg ht0 gB0.le
  simp only [hfn]
  rw [abs_le]
  refine ⟨?_, ?_⟩ <;> linarith

include fpos fe in
theorem hfn_eq_zero {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : hfn f t = 0 :=
  jensen_bounded_eq_zero (fun _ _ hs0 hs1 ht0 ht1 ↦ hfn_jensen fe hs0 hs1 ht0 ht1)
    hfn_zero hfn_one (fun _ ht0 ht1 ↦ hfn_bdd fpos fe ht0 ht1) t ht0 ht1

include fpos fe in
/-- `g` agrees with a linear function on `[1/8, 3/8]`. -/
theorem g_linear_mid_exp {x : ℝ} (hx0 : 1 / 8 ≤ x) (hx1 : x ≤ 3 / 8) :
    g f x = 4 * (g f (3 / 8) - g f (1 / 8)) * x + (3 * g f (1 / 8) - g f (3 / 8)) / 2 := by
  have ht0 : (0:ℝ) ≤ 4 * x - 1 / 2 := by linarith
  have ht1 : 4 * x - 1 / 2 ≤ 1 := by linarith
  have hz := hfn_eq_zero fpos fe ht0 ht1
  simp only [hfn] at hz
  have e : (2 * (4 * x - 1 / 2) + 1) / 8 = x := by ring
  rw [e] at hz
  linarith [hz]

include fe in
/-- With `3 g (1/3) = 1` and `1/3 ∈ [1/8, 3/8]`, the coefficients satisfy
`k + 3 l = 1`. -/
theorem kl_sum {k l : ℝ}
    (hmid : ∀ x : ℝ, 1 / 8 ≤ x → x ≤ 3 / 8 → g f x = k * x + l) : k + 3 * l = 1 := by
  have h1 := g_eq_one fe (by norm_num : (0:ℝ) < 1 / 3) (by norm_num : (0:ℝ) < 1 / 3)
    (by norm_num : (0:ℝ) < 1 / 3) (by norm_num : (1:ℝ) / 3 + 1 / 3 + 1 / 3 = 1)
  have m := hmid (1 / 3) (by norm_num) (by norm_num)
  linarith

include fe in
/-- Linearity extends from `[1/8, 3/8]` down to `(0, 1/8)` using Jensen. -/
theorem g_linear_ext_low {k l : ℝ}
    (hmid : ∀ x : ℝ, 1 / 8 ≤ x → x ≤ 3 / 8 → g f x = k * x + l)
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1 / 8) : g f x = k * x + l := by
  have h1 := g_jensen fe hx0 (by linarith : (0:ℝ) < 3 / 10 - x)
    (by linarith : x + (3 / 10 - x) < 1)
  have e : (x + (3 / 10 - x)) / 2 = 3 / 20 := by ring
  rw [e] at h1
  have m1 := hmid (3 / 20) (by norm_num) (by norm_num)
  have m2 := hmid (3 / 10 - x) (by linarith) (by linarith)
  linarith

include fe in
/-- `g` is linear on all of `(0, 3/8]`. -/
theorem g_linear_low {k l : ℝ}
    (hmid : ∀ x : ℝ, 1 / 8 ≤ x → x ≤ 3 / 8 → g f x = k * x + l)
    {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 3 / 8) : g f x = k * x + l := by
  rcases le_or_gt (1 / 8 : ℝ) x with h | h
  · exact hmid x h hx1
  · exact g_linear_ext_low fe hmid hx0 h

include fe in
/-- Linearity extends from `(0, 3/8]` up to `(0, 1)` using the equation with
`(x, (1 - x) / 2, (1 - x) / 2)`. -/
theorem g_linear_ext_high {k l : ℝ} (hsum : k + 3 * l = 1)
    (hmid : ∀ x : ℝ, 1 / 8 ≤ x → x ≤ 3 / 8 → g f x = k * x + l)
    {x : ℝ} (hx0 : 3 / 8 ≤ x) (hx1 : x < 1) : g f x = k * x + l := by
  have hw0 : (0:ℝ) < (1 - x) / 2 := by linarith
  have h1 := g_eq_one fe (by linarith : (0:ℝ) < x) hw0 hw0 (by ring)
  have mw := g_linear_low fe hmid hw0 (by linarith : (1 - x) / 2 ≤ 3 / 8)
  linarith

include fe in
/-- `g` is linear on all of `(0, 1)`. -/
theorem g_linear {k l : ℝ} (hsum : k + 3 * l = 1)
    (hmid : ∀ x : ℝ, 1 / 8 ≤ x → x ≤ 3 / 8 → g f x = k * x + l)
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) : g f x = k * x + l := by
  rcases le_or_gt x (3 / 8 : ℝ) with h | h
  · rcases le_or_gt (1 / 8 : ℝ) x with h2 | h2
    · exact hmid x h2 h
    · exact g_linear_ext_low fe hmid hx0 h2
  · exact g_linear_ext_high fe hsum hmid (le_of_lt h) hx1

include fpos in
/-- Since `g` is positive, the constant term of the linear function is
nonnegative. -/
theorem l_nonneg {k l : ℝ}
    (hg : ∀ x : ℝ, 0 < x → x < 1 → g f x = k * x + l) : 0 ≤ l := by
  by_contra hl
  push Not at hl
  rcases le_or_gt k 0 with hk | hk
  · have h3 := hg (1 / 2) (by norm_num) (by norm_num)
    have gpos := g_pos fpos (by norm_num : (0:ℝ) < 1 / 2) (by norm_num : (1:ℝ) / 2 < 1)
    rw [h3] at gpos
    linarith
  · obtain ⟨n, hn⟩ := exists_nat_gt (k / (-l))
    have hnl : (0:ℝ) < -l := by linarith
    have hnp : (0:ℝ) < (n : ℝ) := by
      have hkr : (0:ℝ) < k / (-l) := by positivity
      exact lt_trans hkr hn
    have hkey : k < ((n : ℝ) + 1) * (-l) := by
      rw [div_lt_iff₀ hnl] at hn
      linarith [hn, hnl]
    have hkn : k / ((n : ℝ) + 1) < -l := by
      rw [div_lt_iff₀ (by linarith : (0:ℝ) < (n : ℝ) + 1)]
      linarith [hkey]
    have hx0 : (0:ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hx1 : 1 / ((n : ℝ) + 1) < 1 := by
      rw [div_lt_one (by linarith : (0:ℝ) < (n : ℝ) + 1)]
      linarith
    have h3 := hg (1 / ((n : ℝ) + 1)) hx0 hx1
    have gpos := g_pos fpos hx0 hx1
    rw [h3, mul_one_div] at gpos
    linarith [hkn]

include fpos in
/-- Since `g` is positive, the value of the linear function at `1` is
nonnegative. -/
theorem kl_nonneg {k l : ℝ}
    (hg : ∀ x : ℝ, 0 < x → x < 1 → g f x = k * x + l) : 0 ≤ k + l := by
  by_contra hkl
  push Not at hkl
  rcases le_or_gt 0 k with hk | hk
  · have h3 := hg (1 / 2) (by norm_num) (by norm_num)
    have gpos := g_pos fpos (by norm_num : (0:ℝ) < 1 / 2) (by norm_num : (1:ℝ) / 2 < 1)
    rw [h3] at gpos
    linarith
  · obtain ⟨n, hn⟩ := exists_nat_gt (k / (k + l))
    have hnn : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hN : (0:ℝ) < (n : ℝ) + 2 := by positivity
    have hNgt : k / (k + l) < (n : ℝ) + 2 := by linarith
    have h1 : ((n : ℝ) + 2) * (k + l) < k := by
      rwa [div_lt_iff_of_neg hkl] at hNgt
    have h2 : k + l < k / ((n : ℝ) + 2) := by
      rw [lt_div_iff₀ hN]
      linarith [h1]
    have h3 : k * (1 - 1 / ((n : ℝ) + 2)) + l < 0 := by
      have e : k * (1 - 1 / ((n : ℝ) + 2)) + l = (k + l) - k / ((n : ℝ) + 2) := by
        field_simp
        ring
      rw [e]
      linarith [h2]
    have hle : 1 / ((n : ℝ) + 2) ≤ 1 / 2 :=
      one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 2) (by linarith)
    have hx0 : (0:ℝ) < 1 - 1 / ((n : ℝ) + 2) := by linarith
    have hx1 : 1 - 1 / ((n : ℝ) + 2) < 1 := by
      have h4 : (0:ℝ) < 1 / ((n : ℝ) + 2) := by positivity
      linarith
    have h4 := hg (1 - 1 / ((n : ℝ) + 2)) hx0 hx1
    have gpos := g_pos fpos hx0 hx1
    rw [h4] at gpos
    linarith [h3]

include fpos in
/-- The slope of the linear function lies in `[-1/2, 1]`. -/
theorem k_mem {k l : ℝ} (hsum : k + 3 * l = 1)
    (hg : ∀ x : ℝ, 0 < x → x < 1 → g f x = k * x + l) : k ∈ Set.Icc (-1 / 2) 1 := by
  have hl := l_nonneg fpos hg
  have hkl := kl_nonneg fpos hg
  rw [Set.mem_Icc]
  constructor <;> linarith

/-- Transfer the linear formula for `g` back to `f`. -/
theorem f_formula {k l : ℝ} (hsum : k + 3 * l = 1)
    (hg : ∀ x : ℝ, 0 < x → x < 1 → g f x = k * x + l)
    {t : ℝ} (ht : 0 < t) : f t = k / (t + 1) + (1 - k) / 3 := by
  have ht1 : (0:ℝ) < t + 1 := by linarith
  have hs0 : (0:ℝ) < 1 / (t + 1) := by positivity
  have hs1 : 1 / (t + 1) < 1 := by
    rw [div_lt_one ht1]
    linarith
  have h1 := hg (1 / (t + 1)) hs0 hs1
  have e : 1 / (1 / (t + 1)) - 1 = t := by rw [one_div_div]; ring
  unfold g at h1
  rw [e, mul_one_div] at h1
  have hl : l = (1 - k) / 3 := by linarith
  rw [hl] at h1
  exact h1

include fpos fe in
/-- Forward direction: every solution belongs to the one-parameter family. -/
theorem forward :
    ∃ k : ℝ, k ∈ Set.Icc (-1 / 2) 1 ∧ ∀ t : ℝ, 0 < t → f t = k / (t + 1) + (1 - k) / 3 := by
  have hmid : ∀ x : ℝ, 1 / 8 ≤ x → x ≤ 3 / 8 →
      g f x = 4 * (g f (3 / 8) - g f (1 / 8)) * x + (3 * g f (1 / 8) - g f (3 / 8)) / 2 :=
    fun x hx0 hx1 ↦ g_linear_mid_exp fpos fe hx0 hx1
  have hsum := kl_sum fe hmid
  have hg : ∀ x : ℝ, 0 < x → x < 1 →
      g f x = 4 * (g f (3 / 8) - g f (1 / 8)) * x + (3 * g f (1 / 8) - g f (3 / 8)) / 2 :=
    fun x hx0 hx1 ↦ g_linear fe hsum hmid hx0 hx1
  exact ⟨_, k_mem fpos hsum hg, fun t ht ↦ f_formula hsum hg ht⟩

/-- Backward direction: every function of the one-parameter family solves the
problem. -/
theorem backward {f : ℝ → ℝ} {k : ℝ} (hk : k ∈ Set.Icc (-1 / 2) 1)
    (hf : ∀ t : ℝ, 0 < t → f t = k / (t + 1) + (1 - k) / 3) :
    (∀ x : ℝ, 0 < x → 0 < f x) ∧
    (∀ x y z : ℝ, 0 < x → 0 < y → 0 < z → x * y * z = 1 →
      f (x + 1 / y) + f (y + 1 / z) + f (z + 1 / x) = 1) := by
  rw [Set.mem_Icc] at hk
  obtain ⟨hk0, hk1⟩ := hk
  constructor
  · intro x hx
    rw [hf x hx]
    have hx1 : (0:ℝ) < x + 1 := by linarith
    rcases le_or_gt 0 k with h | h
    · have e1 : (0:ℝ) ≤ k / (x + 1) := by positivity
      have e2 : (0:ℝ) ≤ (1 - k) / 3 := by linarith
      rcases eq_or_lt_of_le h with h0 | h0
      · have e3 : (0:ℝ) < (1 - k) / 3 := by linarith
        linarith
      · have e4 : (0:ℝ) < k / (x + 1) := by positivity
        linarith
    · have h11 : (1:ℝ) / (x + 1) < 1 := by
        rw [div_lt_one hx1]
        linarith
      have e : k < k / (x + 1) := by
        have hm := mul_lt_mul_of_neg_left h11 h
        rwa [mul_one, mul_one_div] at hm
      linarith
  · intro x y z hx hy hz hxyz
    have hxp : (0:ℝ) < x + 1 / y := by positivity
    have hyp : (0:ℝ) < y + 1 / z := by positivity
    have hzp : (0:ℝ) < z + 1 / x := by positivity
    have hD : (0:ℝ) < x * y + y + 1 := by positivity
    have hD0 : x * y + y + 1 ≠ 0 := ne_of_gt hD
    have hy0 : y ≠ 0 := ne_of_gt hy
    have hza : z = (x * y)⁻¹ := eq_inv_of_mul_eq_one_right hxyz
    have s1 : 1 / (x + 1 / y + 1) = y / (x * y + y + 1) := by
      have hA : x + 1 / y + 1 ≠ 0 := ne_of_gt (by positivity)
      field_simp
      ring
    have s2 : 1 / (y + 1 / z + 1) = 1 / (x * y + y + 1) := by
      rw [hza]
      congr 1
      rw [one_div, inv_inv]
      ring
    have s3 : 1 / (z + 1 / x + 1) = x * y / (x * y + y + 1) := by
      rw [hza]
      have hx0 : x ≠ 0 := ne_of_gt hx
      have hxy0 : x * y ≠ 0 := mul_ne_zero hx0 hy0
      have hC : (x * y)⁻¹ + 1 / x + 1 ≠ 0 := ne_of_gt (by positivity)
      field_simp
      ring
    have key : 1 / (x + 1 / y + 1) + 1 / (y + 1 / z + 1) + 1 / (z + 1 / x + 1) = 1 := by
      rw [s1, s2, s3]
      field_simp
      ring
    rw [hf _ hxp, hf _ hyp, hf _ hzp]
    have hsum : k / (x + 1 / y + 1) + k / (y + 1 / z + 1) + k / (z + 1 / x + 1) = k := by
      have e : k * (1 / (x + 1 / y + 1) + 1 / (y + 1 / z + 1) + 1 / (z + 1 / x + 1)) =
          k / (x + 1 / y + 1) + k / (y + 1 / z + 1) + k / (z + 1 / x + 1) := by
        rw [mul_add, mul_add, mul_one_div, mul_one_div, mul_one_div]
      rw [← e, key, mul_one]
    linarith [hsum]

snip end

determine solution_set : Set (ℝ → ℝ) :=
  { f | ∃ k : ℝ, k ∈ Set.Icc (-1 / 2) 1 ∧ ∀ t : ℝ, 0 < t → f t = k / (t + 1) + (1 - k) / 3 }

problem usa2018_p2 (f : ℝ → ℝ) :
    f ∈ solution_set ↔
      (∀ x : ℝ, 0 < x → 0 < f x) ∧
        (∀ x y z : ℝ, 0 < x → 0 < y → 0 < z → x * y * z = 1 →
          f (x + 1 / y) + f (y + 1 / z) + f (z + 1 / x) = 1) := by
  constructor
  · intro hf
    obtain ⟨k, hk, hfk⟩ := hf
    exact backward hk hfk
  · intro h
    obtain ⟨fpos, fe⟩ := h
    exact forward fpos fe

end Usa2018P2
