/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Normed.Field.Basic
public import ProblemExtraction

@[expose] public section

problem_file {
  tags := [.Algebra, .Inequality]
  problemImportedFrom :=
    "https://github.com/humanfia/imo2026"
}

/-!
# International Mathematical Olympiad 2026, Problem 5

Let ℝ_{>0} be the set of positive real numbers. Determine all functions
f : ℝ_{>0} → ℝ_{>0} such that

    √((x² + f(y)²)/2) ≥ (f(x) + y)/2 ≥ √(x·f(y))

for every x, y ∈ ℝ_{>0}.

Statement formalization adapted from AxiomMath/IMO2026; proof adapted from
Humanfia's Kimi-K3 solutions (https://github.com/humanfia/imo2026).
-/

namespace Imo2026P5

/-- The subtype of positive real numbers, representing `\mathbb{R}_{>0}`. -/
abbrev PositiveReal : Type := {x : ℝ // 0 < x}

/-- The two-sided inequality defining admissible functions on positive real numbers. -/
def IsAdmissible (f : PositiveReal → PositiveReal) : Prop :=
  ∀ x y : PositiveReal,
    ((f x : ℝ) + (y : ℝ)) / 2 ≤ Real.sqrt (((x : ℝ) ^ 2 + (f y : ℝ) ^ 2) / 2) ∧
      Real.sqrt ((x : ℝ) * (f y : ℝ)) ≤ ((f x : ℝ) + (y : ℝ)) / 2

snip begin

/-- The defect `f x - x` of a function on the positive reals. -/
def fdef (f : PositiveReal → PositiveReal) (x : PositiveReal) : ℝ := (f x : ℝ) - (x : ℝ)

lemma fdef_eq (f : PositiveReal → PositiveReal) (x : PositiveReal) :
    fdef f x = (f x : ℝ) - (x : ℝ) := rfl

lemma pval (v : ℝ) (hv : 0 < v) : ((⟨v, hv⟩ : PositiveReal) : ℝ) = v := rfl

/-- Squared form of the right inequality: `4 x f(y) ≤ (f(x) + y)^2`. -/
lemma hB (f : PositiveReal → PositiveReal) (h : IsAdmissible f) (x y : PositiveReal) :
    4 * (x : ℝ) * (f y : ℝ) ≤ ((f x : ℝ) + (y : ℝ)) ^ 2 := by
  have hx : (0 : ℝ) ≤ (x : ℝ) := le_of_lt x.2
  have hfy : (0 : ℝ) ≤ (f y : ℝ) := le_of_lt (f y).2
  have h1 : Real.sqrt ((x : ℝ) * (f y : ℝ)) ≤ ((f x : ℝ) + (y : ℝ)) / 2 := (h x y).2
  have h2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
  rw [Real.sq_sqrt (mul_nonneg hx hfy)] at h2
  nlinarith [h2]

/-- Squared form of the left inequality: `(f(x) + y)^2 ≤ 2 (x^2 + f(y)^2)`. -/
lemma hA (f : PositiveReal → PositiveReal) (h : IsAdmissible f) (x y : PositiveReal) :
    ((f x : ℝ) + (y : ℝ)) ^ 2 ≤ 2 * ((x : ℝ) ^ 2 + (f y : ℝ) ^ 2) := by
  have hfx : (0 : ℝ) ≤ (f x : ℝ) := le_of_lt (f x).2
  have hy : (0 : ℝ) ≤ (y : ℝ) := le_of_lt y.2
  have h1 : ((f x : ℝ) + (y : ℝ)) / 2 ≤ Real.sqrt (((x : ℝ) ^ 2 + (f y : ℝ) ^ 2) / 2) :=
    (h x y).1
  have hpos : (0 : ℝ) ≤ ((f x : ℝ) + (y : ℝ)) / 2 := by linarith
  have h2 := pow_le_pow_left₀ hpos h1 2
  have hnn : (0 : ℝ) ≤ ((x : ℝ) ^ 2 + (f y : ℝ) ^ 2) / 2 := by positivity
  rw [Real.sq_sqrt hnn] at h2
  nlinarith [h2]

/-- Iterating `f` twice shifts by the defect: `f(f(y)) = 2 f(y) - y`. -/
lemma fcomp (f : PositiveReal → PositiveReal) (h : IsAdmissible f) (y : PositiveReal) :
    (f (f y) : ℝ) = 2 * (f y : ℝ) - (y : ℝ) := by
  have hv := (f y).2
  have hw := (f (f y)).2
  have ht := y.2
  have h1 := hB f h (f y) y
  have h2 := hA f h (f y) y
  have h3 : ((f (f y) : ℝ) + (y : ℝ)) ^ 2 = (2 * (f y : ℝ)) ^ 2 := by
    nlinarith [h1, h2]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h3 with h4 | h4
  · linarith [h4]
  · nlinarith [h4, hw, ht, hv]

/-- The orbit of `f` is an arithmetic progression with difference `fdef f y`. -/
lemma orbit (f : PositiveReal → PositiveReal) (h : IsAdmissible f) (y : PositiveReal)
    (n : ℕ) :
    (f^[n] y : ℝ) = (y : ℝ) + (n : ℝ) * ((f y : ℝ) - (y : ℝ)) := by
  have key : ∀ k : ℕ,
      (f^[k] y : ℝ) = (y : ℝ) + (k : ℝ) * ((f y : ℝ) - (y : ℝ)) ∧
        (f^[k + 1] y : ℝ) = (y : ℝ) + ((k + 1 : ℕ) : ℝ) * ((f y : ℝ) - (y : ℝ)) := by
    intro k
    induction k with
    | zero =>
      constructor
      · rw [Function.iterate_zero_apply]
        simp
      · rw [Function.iterate_one]
        push_cast
        ring
    | succ k ih =>
      obtain ⟨ih1, ih2⟩ := ih
      refine ⟨ih2, ?_⟩
      have e1 : f^[k + 1 + 1] y = f (f (f^[k] y)) := by
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      have e2 := fcomp f h (f^[k] y)
      have e3 : f (f^[k] y) = f^[k + 1] y := (Function.iterate_succ_apply' f k y).symm
      rw [e1, e2, e3, ih1, ih2]
      push_cast
      ring
  exact (key n).1

/-- The defect is nonnegative: `f y ≥ y`. -/
lemma g_nonneg (f : PositiveReal → PositiveReal) (h : IsAdmissible f) (y : PositiveReal) :
    (0 : ℝ) ≤ (f y : ℝ) - (y : ℝ) := by
  by_contra hlt
  push Not at hlt
  set g := (f y : ℝ) - (y : ℝ) with hg
  have hgneg : g < 0 := hlt
  have hpg : (0 : ℝ) < -g := by linarith
  obtain ⟨n, hn⟩ := exists_nat_gt ((y : ℝ) / (-g))
  have hng : (y : ℝ) < (n : ℝ) * (-g) := (div_lt_iff₀ hpg).mp hn
  have h2 := orbit f h y n
  have h3 := (f^[n] y).2
  nlinarith [h2, h3, hng]

/-- Cross inequality on orbit points, with `p = fdef f b`, `q = fdef f a`. -/
lemma cross (f : PositiveReal → PositiveReal) (h : IsAdmissible f) (a b : PositiveReal)
    (m n : ℕ) :
    4 * (f^[m] b : ℝ) * (((f a : ℝ) - (a : ℝ)) - ((f b : ℝ) - (b : ℝ))) ≤
      ((f^[m] b : ℝ) - (f^[n] a : ℝ) - ((f b : ℝ) - (b : ℝ))) ^ 2 := by
  have h1 := hB f h (f^[m] b) (f^[n] a)
  have e1 : f (f^[m] b) = f^[m + 1] b := (Function.iterate_succ_apply' f m b).symm
  have e2 : f (f^[n] a) = f^[n + 1] a := (Function.iterate_succ_apply' f n a).symm
  have o1 := orbit f h b m
  have o2 := orbit f h b (m + 1)
  have o3 := orbit f h a n
  have o4 := orbit f h a (n + 1)
  rw [e1, e2, o2, o4, o1, o3] at h1
  rw [o1, o3]
  have hid :
      ((b : ℝ) + (m : ℝ) * ((f b : ℝ) - (b : ℝ)) - ((a : ℝ) + (n : ℝ) * ((f a : ℝ) - (a : ℝ))) -
          ((f b : ℝ) - (b : ℝ))) ^ 2 -
        4 * ((b : ℝ) + (m : ℝ) * ((f b : ℝ) - (b : ℝ))) *
          (((f a : ℝ) - (a : ℝ)) - ((f b : ℝ) - (b : ℝ))) =
      ((b : ℝ) + ((m + 1 : ℕ) : ℝ) * ((f b : ℝ) - (b : ℝ)) +
          ((a : ℝ) + (n : ℝ) * ((f a : ℝ) - (a : ℝ)))) ^ 2 -
        4 * ((b : ℝ) + (m : ℝ) * ((f b : ℝ) - (b : ℝ))) *
          ((a : ℝ) + ((n + 1 : ℕ) : ℝ) * ((f a : ℝ) - (a : ℝ))) := by
    push_cast
    ring
  linarith [h1, hid]

/-- Two positive defect values cannot be strictly ordered. -/
lemma absurd_lt (f : PositiveReal → PositiveReal) (h : IsAdmissible f) (a b : PositiveReal)
    (ha : (0 : ℝ) < (f a : ℝ) - (a : ℝ)) (hb : (0 : ℝ) < (f b : ℝ) - (b : ℝ))
    (hlt : (f b : ℝ) - (b : ℝ) < (f a : ℝ) - (a : ℝ)) : False := by
  set p := (f b : ℝ) - (b : ℝ) with hp
  set q := (f a : ℝ) - (a : ℝ) with hq
  have hqp : (0 : ℝ) < q - p := by linarith
  set K := |(b : ℝ) - (a : ℝ) - p| + p / 2 with hK
  have hKpos : (0 : ℝ) ≤ K := by
    rw [hK]
    have h1 := abs_nonneg ((b : ℝ) - (a : ℝ) - p)
    linarith [h1, hb]
  obtain ⟨n, hn⟩ := exists_nat_gt ((K ^ 2 / (4 * (q - p)) - (b : ℝ) + p / 2) / q)
  have hnq : K ^ 2 / (4 * (q - p)) - (b : ℝ) + p / 2 < (n : ℝ) * q := (div_lt_iff₀ ha).mp hn
  set m := ⌊((n : ℝ) * q) / p + 1 / 2⌋₊ with hm
  have hnqp : (0 : ℝ) ≤ ((n : ℝ) * q) / p :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg _) (le_of_lt ha)) (le_of_lt hb)
  have hm1 : (m : ℝ) ≤ ((n : ℝ) * q) / p + 1 / 2 := Nat.floor_le (by linarith [hnqp])
  have hm2 : ((n : ℝ) * q) / p + 1 / 2 < (m : ℝ) + 1 := Nat.lt_floor_add_one _
  have hmp_ge : (n : ℝ) * q - p / 2 ≤ (m : ℝ) * p := by
    have h2 := mul_lt_mul_of_pos_right hm2 hb
    rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hb)] at h2
    linarith [h2]
  have hmp_le : (m : ℝ) * p ≤ (n : ℝ) * q + p / 2 := by
    have h2 := mul_le_mul_of_nonneg_right hm1 (le_of_lt hb)
    rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hb)] at h2
    linarith [h2]
  have hc := cross f h a b m n
  rw [orbit f h b m, orbit f h a n] at hc
  have hsq : ((b : ℝ) + (m : ℝ) * p - ((a : ℝ) + (n : ℝ) * q) - p) ^ 2 ≤ K ^ 2 := by
    have habs : |(b : ℝ) + (m : ℝ) * p - ((a : ℝ) + (n : ℝ) * q) - p| ≤ K := by
      have e : (b : ℝ) + (m : ℝ) * p - ((a : ℝ) + (n : ℝ) * q) - p =
          ((b : ℝ) - (a : ℝ) - p) + ((m : ℝ) * p - (n : ℝ) * q) := by ring
      rw [e]
      have h1 : |(m : ℝ) * p - (n : ℝ) * q| ≤ p / 2 := by
        rw [abs_le]
        constructor <;> linarith [hmp_ge, hmp_le]
      have h2 := abs_add_le ((b : ℝ) - (a : ℝ) - p) ((m : ℝ) * p - (n : ℝ) * q)
      linarith [h1, h2, hK, hKpos]
    have h3 := pow_le_pow_left₀ (abs_nonneg _) habs 2
    rwa [sq_abs] at h3
  have hX : (b : ℝ) + (n : ℝ) * q - p / 2 ≤ (b : ℝ) + (m : ℝ) * p := by linarith [hmp_ge]
  have h4 : 4 * ((b : ℝ) + (n : ℝ) * q - p / 2) * (q - p) ≤
      4 * ((b : ℝ) + (m : ℝ) * p) * (q - p) := by
    have h5 := mul_le_mul_of_nonneg_right hX (le_of_lt hqp)
    linarith only [h5]
  have h6 : K ^ 2 < 4 * ((b : ℝ) + (n : ℝ) * q - p / 2) * (q - p) := by
    have h7 : K ^ 2 / (4 * (q - p)) < (b : ℝ) + (n : ℝ) * q - p / 2 := by linarith [hnq]
    have h8 := mul_lt_mul_of_pos_right h7 (by linarith [hqp] : (0 : ℝ) < 4 * (q - p))
    rw [div_mul_cancel₀ _ (ne_of_gt (by linarith [hqp] : (0 : ℝ) < 4 * (q - p)))] at h8
    linarith only [h8]
  linarith only [hc, hsq, h4, h6]

/-- All positive values of the defect coincide. -/
lemma eq_of_pos (f : PositiveReal → PositiveReal) (h : IsAdmissible f) (a b : PositiveReal)
    (ha : (0 : ℝ) < (f a : ℝ) - (a : ℝ)) (hb : (0 : ℝ) < (f b : ℝ) - (b : ℝ)) :
    (f a : ℝ) - (a : ℝ) = (f b : ℝ) - (b : ℝ) := by
  rcases lt_trichotomy ((f a : ℝ) - (a : ℝ)) ((f b : ℝ) - (b : ℝ)) with h1 | h1 | h1
  · exact (absurd_lt f h b a hb ha h1).elim
  · exact h1
  · exact (absurd_lt f h a b ha hb h1).elim

/-- Near a zero of the defect, the defect vanishes. -/
lemma ball (f : PositiveReal → PositiveReal) (h : IsAdmissible f) (a : PositiveReal)
    (ha : (0 : ℝ) < fdef f a)
    (hdval : ∀ x : PositiveReal, fdef f x = 0 ∨ fdef f x = fdef f a)
    (t x : PositiveReal) (ht : fdef f t = 0)
    (hclose : |(x : ℝ) - (t : ℝ)| < Real.sqrt (2 * fdef f a * (t : ℝ))) :
    fdef f x = 0 := by
  have hd : (0 : ℝ) < fdef f a := ha
  have hx2 := g_nonneg f h x
  have hft : (f t : ℝ) = (t : ℝ) := by
    rw [fdef_eq] at ht
    linarith
  have h1 := hA f h x t
  rw [hft] at h1
  have he : (f x : ℝ) = (x : ℝ) + fdef f x := by rw [fdef_eq]; ring
  rw [he] at h1
  have hgx : (0 : ℝ) ≤ fdef f x := by rw [fdef_eq]; linarith [hx2]
  have h2 : 2 * fdef f x * ((x : ℝ) + (t : ℝ)) ≤ ((x : ℝ) - (t : ℝ)) ^ 2 := by
    nlinarith [h1, sq_nonneg (fdef f x)]
  have h3 : ((x : ℝ) - (t : ℝ)) ^ 2 < 2 * fdef f a * ((x : ℝ) + (t : ℝ)) := by
    have h4 : ((x : ℝ) - (t : ℝ)) ^ 2 = |(x : ℝ) - (t : ℝ)| ^ 2 := (sq_abs _).symm
    have h5 : |(x : ℝ) - (t : ℝ)| ^ 2 < (Real.sqrt (2 * fdef f a * (t : ℝ))) ^ 2 :=
      pow_lt_pow_left₀ hclose (abs_nonneg _) two_ne_zero
    have hnn : (0 : ℝ) ≤ 2 * fdef f a * (t : ℝ) :=
      mul_nonneg (mul_nonneg (le_of_lt (by norm_num : (0 : ℝ) < 2)) (le_of_lt hd))
        (le_of_lt t.2)
    rw [Real.sq_sqrt hnn] at h5
    rw [h4]
    have hxp := x.2
    nlinarith [h5, mul_nonneg (le_of_lt hd) (le_of_lt hxp)]
  have hpos : (0 : ℝ) < (x : ℝ) + (t : ℝ) := add_pos x.2 t.2
  have h6 : fdef f x < fdef f a := by
    have h7 : 2 * fdef f x * ((x : ℝ) + (t : ℝ)) < 2 * fdef f a * ((x : ℝ) + (t : ℝ)) :=
      lt_of_le_of_lt h2 h3
    have h8 := lt_of_mul_lt_mul_right h7 (le_of_lt hpos)
    nlinarith [h8]
  rcases hdval x with h0 | hd'
  · exact h0
  · linarith [h6, hd']

/-- Everything strictly above a zero of the defect is a zero. -/
lemma ascend (f : PositiveReal → PositiveReal) (h : IsAdmissible f) (a : PositiveReal)
    (ha : (0 : ℝ) < fdef f a)
    (hdval : ∀ x : PositiveReal, fdef f x = 0 ∨ fdef f x = fdef f a)
    (t : PositiveReal) (ht : fdef f t = 0) (x : PositiveReal) (htx : (t : ℝ) < (x : ℝ)) :
    fdef f x = 0 := by
  set d := fdef f a with hd_def
  have hd : (0 : ℝ) < d := ha
  have htpos : (0 : ℝ) < (t : ℝ) := t.2
  have h2dt : (0 : ℝ) < 2 * d * (t : ℝ) := mul_pos (mul_pos two_pos hd) htpos
  set δ := Real.sqrt (2 * d * (t : ℝ)) / 2 with hδ_def
  have hδ : (0 : ℝ) < δ := by
    have hs := Real.sqrt_pos_of_pos h2dt
    linarith [hδ_def, hs]
  set i := ⌊((x : ℝ) - (t : ℝ)) / δ⌋₊ with hi_def
  have hxt : (0 : ℝ) ≤ (x : ℝ) - (t : ℝ) := sub_nonneg.mpr (le_of_lt htx)
  have hi_le : (i : ℝ) ≤ ((x : ℝ) - (t : ℝ)) / δ :=
    Nat.floor_le (div_nonneg hxt (le_of_lt hδ))
  have hi_lt : ((x : ℝ) - (t : ℝ)) / δ < (i : ℝ) + 1 := Nat.lt_floor_add_one _
  have htipos : (0 : ℝ) < (t : ℝ) + (i : ℝ) * δ :=
    add_pos_of_pos_of_nonneg htpos (mul_nonneg (Nat.cast_nonneg _) (le_of_lt hδ))
  set ti : PositiveReal := ⟨(t : ℝ) + (i : ℝ) * δ, htipos⟩ with hti_def
  have hgti : fdef f ti = 0 := by
    have step : ∀ j : ℕ, ∀ hj : (0 : ℝ) < (t : ℝ) + (j : ℝ) * δ,
        fdef f ⟨(t : ℝ) + (j : ℝ) * δ, hj⟩ = 0 := by
      intro j
      induction j with
      | zero =>
        intro hj
        have e : (⟨(t : ℝ) + ((0 : ℕ) : ℝ) * δ, hj⟩ : PositiveReal) = t := by
          apply Subtype.ext
          simp
        rw [e]
        exact ht
      | succ j ih =>
        intro hj
        have hjpos : (0 : ℝ) < (t : ℝ) + (j : ℝ) * δ :=
          add_pos_of_pos_of_nonneg htpos (mul_nonneg (Nat.cast_nonneg _) (le_of_lt hδ))
        have ih' := ih hjpos
        have hclose : |(t : ℝ) + ((j + 1 : ℕ) : ℝ) * δ - ((t : ℝ) + (j : ℝ) * δ)| <
            Real.sqrt (2 * d * ((t : ℝ) + (j : ℝ) * δ)) := by
          have e : (t : ℝ) + ((j + 1 : ℕ) : ℝ) * δ - ((t : ℝ) + (j : ℝ) * δ) = δ := by
            push_cast
            ring
          rw [e, abs_of_nonneg (le_of_lt hδ)]
          have hj0 : (0 : ℝ) ≤ (j : ℝ) * δ := mul_nonneg (Nat.cast_nonneg _) (le_of_lt hδ)
          have hsqrt : Real.sqrt (2 * d * (t : ℝ)) ≤
              Real.sqrt (2 * d * ((t : ℝ) + (j : ℝ) * δ)) :=
            Real.sqrt_le_sqrt (by nlinarith [mul_nonneg (le_of_lt hd) hj0])
          have hs : (0 : ℝ) < Real.sqrt (2 * d * (t : ℝ)) := Real.sqrt_pos_of_pos h2dt
          have h2 : δ < Real.sqrt (2 * d * (t : ℝ)) := by linarith [hδ_def, hs]
          exact lt_of_lt_of_le h2 hsqrt
        exact ball f h a ha hdval ⟨(t : ℝ) + (j : ℝ) * δ, hjpos⟩
          ⟨(t : ℝ) + ((j + 1 : ℕ) : ℝ) * δ, hj⟩ ih' hclose
    exact step i htipos
  have hclose2 : |(x : ℝ) - (ti : ℝ)| < Real.sqrt (2 * d * (ti : ℝ)) := by
    have e : (ti : ℝ) = (t : ℝ) + (i : ℝ) * δ := rfl
    rw [e]
    have hx1 : (0 : ℝ) ≤ (x : ℝ) - (t : ℝ) - (i : ℝ) * δ := by
      have hmul := mul_le_mul_of_nonneg_right hi_le (le_of_lt hδ)
      rw [div_mul_cancel₀ _ (ne_of_gt hδ)] at hmul
      nlinarith [hmul]
    have hx2 : (x : ℝ) - (t : ℝ) - (i : ℝ) * δ < δ := by
      have hmul := mul_lt_mul_of_pos_right hi_lt hδ
      rw [div_mul_cancel₀ _ (ne_of_gt hδ)] at hmul
      nlinarith [hmul]
    have ex : (x : ℝ) - ((t : ℝ) + (i : ℝ) * δ) = (x : ℝ) - (t : ℝ) - (i : ℝ) * δ := by
      ring
    rw [ex, abs_of_nonneg hx1]
    have hsqrt : Real.sqrt (2 * d * (t : ℝ)) ≤
        Real.sqrt (2 * d * ((t : ℝ) + (i : ℝ) * δ)) := by
      apply Real.sqrt_le_sqrt
      have hi0 : (0 : ℝ) ≤ (i : ℝ) * δ := mul_nonneg (Nat.cast_nonneg _) (le_of_lt hδ)
      nlinarith [mul_nonneg (le_of_lt hd) hi0]
    have hs : (0 : ℝ) < Real.sqrt (2 * d * (t : ℝ)) := Real.sqrt_pos_of_pos h2dt
    have h2 : δ < Real.sqrt (2 * d * (t : ℝ)) := by linarith [hδ_def, hs]
    linarith [hx2, h2, hsqrt]
  exact ball f h a ha hdval ti x hgti hclose2

/-- A zero of the defect cannot coexist with a positive value. -/
lemma zero_contra (f : PositiveReal → PositiveReal) (h : IsAdmissible f) (a : PositiveReal)
    (ha : (0 : ℝ) < fdef f a)
    (hdval : ∀ x : PositiveReal, fdef f x = 0 ∨ fdef f x = fdef f a)
    (b : PositiveReal) (hb : fdef f b = 0) : False := by
  set d := fdef f a with hd_def
  have hd : (0 : ℝ) < d := ha
  have hbpos : (0 : ℝ) < (b : ℝ) := b.2
  obtain ⟨t0, ht0g, ht0le⟩ : ∃ t0 : PositiveReal, fdef f t0 = 0 ∧ (t0 : ℝ) ≤ 2 * d := by
    by_cases hb2 : (b : ℝ) ≤ 2 * d
    · exact ⟨b, hb, hb2⟩
    · push Not at hb2
      set k := ⌊((b : ℝ) - 2 * d) / d⌋₊ + 1 with hk_def
      have hu : (0 : ℝ) ≤ ((b : ℝ) - 2 * d) / d :=
        div_nonneg (sub_nonneg.mpr (le_of_lt hb2)) (le_of_lt hd)
      have hk1 : ((b : ℝ) - 2 * d) / d < (k : ℝ) := by
        have h1 := Nat.lt_floor_add_one (((b : ℝ) - 2 * d) / d)
        rw [hk_def]
        push_cast
        linarith [h1]
      have hk2 : (k : ℝ) ≤ ((b : ℝ) - 2 * d) / d + 1 := by
        have h1 := Nat.floor_le hu
        rw [hk_def]
        push_cast
        linarith [h1]
      have ht0pos : (0 : ℝ) < (b : ℝ) - (k : ℝ) * d := by
        have hmul := mul_le_mul_of_nonneg_right hk2 (le_of_lt hd)
        rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hd)] at hmul
        nlinarith [hmul]
      have ht0le : (b : ℝ) - (k : ℝ) * d ≤ 2 * d := by
        have hmul := mul_lt_mul_of_pos_right hk1 hd
        rw [div_mul_cancel₀ _ (ne_of_gt hd)] at hmul
        nlinarith [hmul]
      have ht0g : fdef f ⟨(b : ℝ) - (k : ℝ) * d, ht0pos⟩ = 0 := by
        have step : ∀ j : ℕ, j ≤ k → ∀ hj : (0 : ℝ) < (b : ℝ) - (j : ℝ) * d,
            fdef f ⟨(b : ℝ) - (j : ℝ) * d, hj⟩ = 0 := by
          intro j
          induction j with
          | zero =>
            intro _ hj
            have e : (⟨(b : ℝ) - ((0 : ℕ) : ℝ) * d, hj⟩ : PositiveReal) = b := by
              apply Subtype.ext
              simp
            rw [e]
            exact hb
          | succ j ih =>
            intro hjk hj
            have hjk' : j ≤ k := Nat.le_of_succ_le hjk
            have hjfloor : j ≤ ⌊((b : ℝ) - 2 * d) / d⌋₊ := by omega
            have h1 : (j : ℝ) ≤ ((b : ℝ) - 2 * d) / d := by
              have h2 := Nat.floor_le hu
              have h3 : (j : ℝ) ≤ (⌊((b : ℝ) - 2 * d) / d⌋₊ : ℝ) :=
                Nat.cast_le.mpr hjfloor
              linarith [h2, h3]
            have hbd : (2 : ℝ) * d ≤ (b : ℝ) - (j : ℝ) * d := by
              have hmul := mul_le_mul_of_nonneg_right h1 (le_of_lt hd)
              rw [div_mul_cancel₀ _ (ne_of_gt hd)] at hmul
              nlinarith [hmul]
            have hjpos : (0 : ℝ) < (b : ℝ) - (j : ℝ) * d := by nlinarith [hbd, hd]
            have ih' := ih hjk' hjpos
            have hclose : |(b : ℝ) - ((j + 1 : ℕ) : ℝ) * d - ((b : ℝ) - (j : ℝ) * d)| <
                Real.sqrt (2 * d * ((b : ℝ) - (j : ℝ) * d)) := by
              have e : (b : ℝ) - ((j + 1 : ℕ) : ℝ) * d - ((b : ℝ) - (j : ℝ) * d) = -d := by
                push_cast
                ring
              rw [e, abs_neg, abs_of_nonneg (le_of_lt hd)]
              rw [Real.lt_sqrt (le_of_lt hd)]
              nlinarith [hbd, hd, mul_pos hd hd]
            exact ball f h a ha hdval ⟨(b : ℝ) - (j : ℝ) * d, hjpos⟩
              ⟨(b : ℝ) - ((j + 1 : ℕ) : ℝ) * d, hj⟩ ih' hclose
        exact step k (le_refl k) ht0pos
      exact ⟨⟨(b : ℝ) - (k : ℝ) * d, ht0pos⟩, ht0g, ht0le⟩
  have hall : ∀ x : PositiveReal, fdef f x = 0 := by
    intro x
    rcases lt_or_ge (x : ℝ) (t0 : ℝ) with hx | hx
    · have hclose : |(x : ℝ) - (t0 : ℝ)| < Real.sqrt (2 * d * (t0 : ℝ)) := by
        have h1 : (t0 : ℝ) ^ 2 ≤ 2 * d * (t0 : ℝ) := by
          have hmul := mul_le_mul_of_nonneg_right ht0le (le_of_lt t0.2)
          nlinarith [hmul]
        have h2 : (t0 : ℝ) ≤ Real.sqrt (2 * d * (t0 : ℝ)) := by
          rw [Real.le_sqrt (le_of_lt t0.2) (mul_nonneg (mul_nonneg (le_of_lt two_pos) (le_of_lt hd)) (le_of_lt t0.2))]
          exact h1
        rw [abs_of_nonpos (by linarith : (x : ℝ) - (t0 : ℝ) ≤ 0)]
        have hxp := x.2
        linarith [h2, hxp]
      exact ball f h a ha hdval t0 x ht0g hclose
    · rcases eq_or_lt_of_le hx with he | hlt
      · have heq : x = t0 := Subtype.ext he.symm
        rw [heq]
        exact ht0g
      · exact ascend f h a ha hdval t0 ht0g x hlt
  have hfa : d = 0 := hall a
  linarith [hd, hfa]

snip end

determine answer : Set (PositiveReal → PositiveReal) :=
  {f : PositiveReal → PositiveReal |
    ∃ c : ℝ, 0 ≤ c ∧ ∀ x : PositiveReal, (f x : ℝ) = (x : ℝ) + c}

/-- The admissible functions are exactly the translations `f(x) = x + c` with a
nonnegative constant `c`. -/
problem imo2026_p5 (f : PositiveReal → PositiveReal) :
    IsAdmissible f ↔ f ∈ answer := by
  change IsAdmissible f ↔
      ∃ c : ℝ, 0 ≤ c ∧ ∀ x : PositiveReal, (f x : ℝ) = (x : ℝ) + c
  constructor
  · intro h
    by_cases hz : ∃ b : PositiveReal, fdef f b = 0
    · by_cases hp : ∃ a : PositiveReal, (0 : ℝ) < fdef f a
      · obtain ⟨a, ha⟩ := hp
        obtain ⟨b, hb⟩ := hz
        have hdval : ∀ x : PositiveReal, fdef f x = 0 ∨ fdef f x = fdef f a := by
          intro x
          have hgx := g_nonneg f h x
          rw [fdef_eq]
          rcases eq_or_lt_of_le hgx with h0 | hpos
          · exact Or.inl h0.symm
          · exact Or.inr (eq_of_pos f h x a hpos ha)
        exact (zero_contra f h a ha hdval b hb).elim
      · push Not at hp
        refine ⟨0, le_refl 0, fun x => ?_⟩
        have hgx := g_nonneg f h x
        have h0 : fdef f x = 0 := by
          have hp' := hp x
          rw [fdef_eq] at hp' ⊢
          linarith [hgx]
        rw [fdef_eq] at h0
        linarith [h0]
    · push Not at hz
      have ha₀ : (0 : ℝ) < fdef f ⟨1, one_pos⟩ := by
        have hg := g_nonneg f h ⟨1, one_pos⟩
        have hne := hz ⟨1, one_pos⟩
        rcases eq_or_lt_of_le hg with h0 | hpos
        · exact absurd h0.symm hne
        · exact hpos
      have hdval : ∀ x : PositiveReal, fdef f x = fdef f ⟨1, one_pos⟩ := by
        intro x
        have hx : (0 : ℝ) < fdef f x := by
          have hg := g_nonneg f h x
          have hne := hz x
          rcases eq_or_lt_of_le hg with h0 | hpos
          · exact absurd h0.symm hne
          · exact hpos
        exact eq_of_pos f h x ⟨1, one_pos⟩ hx ha₀
      refine ⟨fdef f ⟨1, one_pos⟩, le_of_lt ha₀, fun x => ?_⟩
      have h1 := hdval x
      rw [fdef_eq] at h1
      linarith [h1]
  · rintro ⟨c, hc, hfc⟩
    intro x y
    have hx : (0 : ℝ) < (x : ℝ) := x.2
    have hy : (0 : ℝ) < (y : ℝ) := y.2
    rw [hfc x, hfc y]
    constructor
    · have hpos : (0 : ℝ) ≤ ((x : ℝ) + c + (y : ℝ)) / 2 := by linarith [hx, hy, hc]
      rw [Real.le_sqrt hpos (by positivity)]
      nlinarith [sq_nonneg ((x : ℝ) - ((y : ℝ) + c))]
    · have hpos : (0 : ℝ) ≤ ((x : ℝ) + c + (y : ℝ)) / 2 := by linarith [hx, hy, hc]
      rw [Real.sqrt_le_iff]
      refine ⟨hpos, ?_⟩
      nlinarith [sq_nonneg ((x : ℝ) - ((y : ℝ) + c))]

end Imo2026P5
