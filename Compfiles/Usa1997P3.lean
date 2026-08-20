/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.EuclideanDomain.Basic
public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Data.Int.Star
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Algebra] }

/-!
# USA Mathematical Olympiad 1997, Problem 3

Prove that for any integer n, there exists a unique polynomial Q with
coefficients in {0, 1, ..., 9} such that Q(-2) = Q(-5) = n.
-/

namespace Usa1997P3

open Polynomial

snip begin

/-!
### The coefficient extraction algorithm

If `Q(x) = a₀ + a₁x + ⋯` has integer coefficients and satisfies `Q(-2) = u`
and `Q(-5) = v`, then `a₀ ≡ u (mod 2)` and `a₀ ≡ v (mod 5)`, which determines
`a₀` uniquely inside `{0, …, 9}`, and the shifted polynomial
`(Q(x) - a₀)/x` represents the pair `((a₀ - u)/2, (a₀ - v)/5)` at `-2` and `-5`.
Iterating this procedure extracts the coefficients one at a time.
-/

/-- The unique digit in `{0, …, 9}` congruent to `u` modulo 2 and to `v`
modulo 5 (which exist and are unique by the Chinese remainder theorem). -/
def digit (u v : ℤ) : ℤ := (6 * v - 5 * u) % 10

lemma digit_props (u v : ℤ) :
    0 ≤ digit u v ∧ digit u v ≤ 9 ∧ digit u v % 2 = u % 2 ∧ digit u v % 5 = v % 5 := by
  unfold digit
  refine ⟨by lia, by lia, by lia, by lia⟩

/-- One step of the extraction: the successor pair
`((digit u v - u)/2, (digit u v - v)/5)` keeps the invariant `u ≡ v (mod 3)`,
and its components are strictly smaller than those of `(u, v)` as soon as
`|v| > 2` (for the second component) or `|u| > 9` (for the first one). -/
lemma step_props (u v : ℤ) (h3 : (u - v) % 3 = 0) :
    0 ≤ digit u v ∧ digit u v ≤ 9 ∧
    2 * ((digit u v - u) / 2) = digit u v - u ∧
    5 * ((digit u v - v) / 5) = digit u v - v ∧
    ((digit u v - u) / 2 - (digit u v - v) / 5) % 3 = 0 ∧
    (2 < v.natAbs → ((digit u v - v) / 5).natAbs < v.natAbs) ∧
    (v.natAbs ≤ 2 → 9 < u.natAbs → ((digit u v - u) / 2).natAbs < u.natAbs) ∧
    (v.natAbs ≤ 2 → ((digit u v - v) / 5).natAbs ≤ 2) := by
  obtain ⟨hd0, hd9, hd2, hd5⟩ := digit_props u v
  have h2 : 2 ∣ digit u v - u := by lia
  have h5 : 5 ∣ digit u v - v := by lia
  have h2' : 2 * ((digit u v - u) / 2) = digit u v - u := by
    obtain ⟨k, hk⟩ := h2
    rw [hk, Int.mul_ediv_cancel_left k (by norm_num)]
  have h5' : 5 * ((digit u v - v) / 5) = digit u v - v := by
    obtain ⟨k, hk⟩ := h5
    rw [hk, Int.mul_ediv_cancel_left k (by norm_num)]
  exact ⟨hd0, hd9, h2', h5', by lia, by lia, by lia, by lia⟩

/-- The polynomial whose coefficients are the given list of digits,
in little-endian order. -/
noncomputable def polyOfDigits : List ℤ → ℤ[X]
  | [] => 0
  | d :: ds => C d + X * polyOfDigits ds

lemma eval_polyOfDigits_cons (d : ℤ) (ds : List ℤ) (x : ℤ) :
    (polyOfDigits (d :: ds)).eval x = d + x * (polyOfDigits ds).eval x := by
  simp [polyOfDigits]

lemma coeff_polyOfDigits_cons (d : ℤ) (ds : List ℤ) (i : ℕ) :
    (polyOfDigits (d :: ds)).coeff i = if i = 0 then d else (polyOfDigits ds).coeff (i - 1) := by
  cases i with
  | zero =>
    rw [ite_eq_left rfl]
    simp only [polyOfDigits, coeff_add, coeff_C_zero, mul_coeff_zero, coeff_X_zero,
      zero_mul, add_zero]
  | succ j =>
    have hj : j + 1 ≠ 0 := by lia
    rw [ite_eq_right hj, Nat.add_sub_cancel]
    simp only [polyOfDigits, coeff_add, coeff_C_succ, coeff_X_mul, zero_add]

lemma coeff_polyOfDigits (ds : List ℤ) (h : ∀ d ∈ ds, 0 ≤ d ∧ d ≤ 9) (i : ℕ) :
    0 ≤ (polyOfDigits ds).coeff i ∧ (polyOfDigits ds).coeff i ≤ 9 := by
  induction ds generalizing i with
  | nil => simp [polyOfDigits]
  | cons d ds ih =>
    have hd : 0 ≤ d ∧ d ≤ 9 := h d (by simp)
    have hds : ∀ e ∈ ds, 0 ≤ e ∧ e ≤ 9 := fun e he ↦ h e (List.mem_cons_of_mem d he)
    rw [coeff_polyOfDigits_cons]
    cases i with
    | zero => simpa using hd
    | succ j => simpa using ih hds j

/-- Runs the extraction algorithm for at most `fuel` steps, returning the
list of extracted digits if the pair `(0, 0)` is reached in time. -/
def build : ℕ → ℤ → ℤ → Option (List ℤ)
  | 0, u, v => if u = 0 ∧ v = 0 then some [] else none
  | fuel + 1, u, v =>
    if u = 0 ∧ v = 0 then some []
    else
      match build fuel ((digit u v - u) / 2) ((digit u v - v) / 5) with
      | some ds => some (digit u v :: ds)
      | none => none

/-- Any digit list produced by `build` from a pair `(u, v)` with
`u ≡ v (mod 3)` indeed represents `(u, v)`. -/
lemma build_correct (fuel : ℕ) (u v : ℤ) (ds : List ℤ) (h : build fuel u v = some ds)
    (h3 : (u - v) % 3 = 0) :
    (polyOfDigits ds).eval (-2) = u ∧ (polyOfDigits ds).eval (-5) = v ∧
      ∀ d ∈ ds, 0 ≤ d ∧ d ≤ 9 := by
  induction fuel generalizing u v ds with
  | zero =>
    simp only [build] at h
    by_cases huv : u = 0 ∧ v = 0
    · rw [ite_eq_left huv] at h
      obtain ⟨rfl, rfl⟩ := huv
      obtain rfl := Option.some.inj h
      exact ⟨by simp [polyOfDigits], by simp [polyOfDigits], fun d hd ↦ by simp at hd⟩
    · rw [ite_eq_right huv] at h
      simp at h
  | succ fuel ih =>
    simp only [build] at h
    by_cases huv : u = 0 ∧ v = 0
    · rw [ite_eq_left huv] at h
      obtain ⟨rfl, rfl⟩ := huv
      obtain rfl := Option.some.inj h
      exact ⟨by simp [polyOfDigits], by simp [polyOfDigits], fun d hd ↦ by simp at hd⟩
    · rw [ite_eq_right huv] at h
      obtain ⟨hd0, hd9, h2, h5, h3', -, -, -⟩ := step_props u v h3
      cases hb : build fuel ((digit u v - u) / 2) ((digit u v - v) / 5) with
      | none => rw [hb] at h; simp at h
      | some ds' =>
        rw [hb] at h
        obtain rfl := Option.some.inj h
        obtain ⟨e2, e5, hdig⟩ := ih _ _ _ hb h3'
        refine ⟨?_, ?_, fun d hd ↦ ?_⟩
        · rw [eval_polyOfDigits_cons, e2]; lia
        · rw [eval_polyOfDigits_cons, e5]; lia
        · rcases List.mem_cons.mp hd with rfl | hd'
          · exact ⟨hd0, hd9⟩
          · exact hdig _ hd'

/-- On the finite region `|u| ≤ 9`, `|v| ≤ 2` the algorithm always terminates
in at most 8 steps (checked here by exhaustive computation over the 95 pairs
with `u ≡ v (mod 3)`). -/
lemma build_region_all :
    ∀ a ∈ Finset.range 19, ∀ b ∈ Finset.range 5,
      ((a : ℤ) - 9 - ((b : ℤ) - 2)) % 3 = 0 →
      (build 8 ((a : ℤ) - 9) ((b : ℤ) - 2)).isSome := by
  decide

lemma build_region_some (u v : ℤ) (hu : -9 ≤ u ∧ u ≤ 9) (hv : -2 ≤ v ∧ v ≤ 2)
    (h3 : (u - v) % 3 = 0) : ∃ ds, build 8 u v = some ds := by
  have ha : ∃ a ∈ Finset.range 19, (a : ℤ) - 9 = u := by
    refine ⟨(u + 9).toNat, Finset.mem_range.mpr ?_, by lia⟩
    lia
  have hb : ∃ b ∈ Finset.range 5, (b : ℤ) - 2 = v := by
    refine ⟨(v + 2).toNat, Finset.mem_range.mpr ?_, by lia⟩
    lia
  obtain ⟨a, ham, hae⟩ := ha
  obtain ⟨b, hbm, hbe⟩ := hb
  rw [← hae, ← hbe] at h3 ⊢
  exact Option.isSome_iff_exists.mp (build_region_all a ham b hbm h3)

/-- The specification of the problem: `Q` has coefficients in `{0, …, 9}` and
takes the values `u` at `-2` and `v` at `-5`. -/
def Good (u v : ℤ) (Q : ℤ[X]) : Prop :=
  (∀ i, 0 ≤ Q.coeff i ∧ Q.coeff i ≤ 9) ∧ Q.eval (-2) = u ∧ Q.eval (-5) = v

/-- If the successor pair of `(u, v)` is representable, so is `(u, v)`:
prepend the extracted digit as the new constant coefficient. -/
lemma good_of_good_step (u v : ℤ) (h3 : (u - v) % 3 = 0)
    (h : ∃ Q, Good ((digit u v - u) / 2) ((digit u v - v) / 5) Q) :
    ∃ Q, Good u v Q := by
  obtain ⟨hd0, hd9, h2, h5, -, -, -, -⟩ := step_props u v h3
  obtain ⟨Q, hc, e2, e5⟩ := h
  refine ⟨C (digit u v) + X * Q, fun i ↦ ?_, ?_, ?_⟩
  · cases i with
    | zero =>
      have hz : (C (digit u v) + X * Q).coeff 0 = digit u v := by
        simp only [coeff_add, coeff_C_zero, mul_coeff_zero, coeff_X_zero, zero_mul,
          add_zero]
      rw [hz]
      exact ⟨hd0, hd9⟩
    | succ j =>
      have hs : (C (digit u v) + X * Q).coeff (j + 1) = Q.coeff j := by
        simp only [coeff_add, coeff_C_succ, coeff_X_mul, zero_add]
      rw [hs]
      exact hc j
  · simp [e2]; lia
  · simp [e5]; lia

/-- Existence for all pairs in the region `|v| ≤ 2`, by strong descent on
`|u|`: either `|u| ≤ 9` and we are in the finite region checked by
`build_region_all`, or one extraction step strictly decreases `|u|`. -/
theorem exists_good_region (u v : ℤ) (hv2 : v.natAbs ≤ 2) (h3 : (u - v) % 3 = 0) :
    ∃ Q, Good u v Q := by
  induction hM : u.natAbs using Nat.strong_induction_on generalizing u v with | _ M ih
  by_cases hsmall : u.natAbs ≤ 9
  · obtain ⟨ds, hds⟩ := build_region_some u v (by lia) (by lia) h3
    obtain ⟨e2, e5, hdig⟩ := build_correct _ _ _ _ hds h3
    exact ⟨polyOfDigits ds, coeff_polyOfDigits ds hdig, e2, e5⟩
  · obtain ⟨hd0, hd9, h2, h5, h3', hvdec, hudec, hvin⟩ := step_props u v h3
    obtain ⟨Q, hQ⟩ := ih (((digit u v - u) / 2).natAbs)
      (by have hlt := hudec hv2 (by lia); lia) _ _ (hvin hv2) h3' rfl
    exact good_of_good_step u v h3 ⟨Q, hQ⟩

/-- Existence for all pairs `(u, v)` with `u ≡ v (mod 3)`, by strong descent
on `|v|`: either `|v| ≤ 2` and `exists_good_region` applies, or one
extraction step strictly decreases `|v|`. -/
theorem exists_good (u v : ℤ) (h3 : (u - v) % 3 = 0) : ∃ Q, Good u v Q := by
  induction hM : v.natAbs using Nat.strong_induction_on generalizing u v with | _ M ih
  by_cases hsmall : v.natAbs ≤ 2
  · exact exists_good_region u v hsmall h3
  · obtain ⟨hd0, hd9, h2, h5, h3', hvdec, -, -⟩ := step_props u v h3
    obtain ⟨Q, hQ⟩ := ih (((digit u v - v) / 5).natAbs)
      (by have hlt := hvdec (by lia); lia) _ _ h3' rfl
    exact good_of_good_step u v h3 ⟨Q, hQ⟩

/-- Uniqueness: the difference `D` of two good polynomials has coefficients in
`{-9, …, 9}` and vanishes at `-2` and `-5`. Its trailing coefficient is then
divisible by both 2 and 5, hence by 10, hence it is zero — a contradiction
unless `D = 0`. -/
theorem good_unique (Q₁ Q₂ : ℤ[X]) (n : ℤ) (h₁ : Good n n Q₁) (h₂ : Good n n Q₂) :
    Q₁ = Q₂ := by
  by_contra hne
  obtain ⟨hc1, e21, e51⟩ := h₁
  obtain ⟨hc2, e22, e52⟩ := h₂
  set D := Q₁ - Q₂ with hD
  have hDne : D ≠ 0 := sub_ne_zero.mpr hne
  have hDe2 : D.eval (-2) = 0 := by simp [hD, e21, e22]
  have hDe5 : D.eval (-5) = 0 := by simp [hD, e51, e52]
  have htc : D.trailingCoeff ≠ 0 := trailingCoeff_nonzero_iff_nonzero.mpr hDne
  obtain ⟨F, hF⟩ : (X ^ D.natTrailingDegree : ℤ[X]) ∣ D :=
    X_pow_dvd_iff.mpr fun i hi ↦ coeff_eq_zero_of_lt_natTrailingDegree hi
  have hFe2 : F.eval (-2) = 0 := by
    have h := hDe2
    rw [hF] at h
    simp only [eval_mul, eval_pow, eval_X] at h
    rcases mul_eq_zero.mp h with hpow | hF0
    · exact absurd hpow (pow_ne_zero _ (by norm_num))
    · exact hF0
  have hFe5 : F.eval (-5) = 0 := by
    have h := hDe5
    rw [hF] at h
    simp only [eval_mul, eval_pow, eval_X] at h
    rcases mul_eq_zero.mp h with hpow | hF0
    · exact absurd hpow (pow_ne_zero _ (by norm_num))
    · exact hF0
  have h2dvd : (2 : ℤ) ∣ F.eval 0 := by
    simpa [hFe2] using sub_dvd_eval_sub 0 (-2) F
  have h5dvd : (5 : ℤ) ∣ F.eval 0 := by
    simpa [hFe5] using sub_dvd_eval_sub 0 (-5) F
  have hFc : F.coeff 0 = D.trailingCoeff := by
    have h1 : (X ^ D.natTrailingDegree * F).coeff D.natTrailingDegree = F.coeff 0 := by
      have h2 := coeff_X_pow_mul F D.natTrailingDegree 0
      rwa [zero_add] at h2
    calc F.coeff 0 = (X ^ D.natTrailingDegree * F).coeff D.natTrailingDegree := h1.symm
    _ = D.coeff D.natTrailingDegree := by rw [← hF]
    _ = D.trailingCoeff := rfl
  have h10 : (10 : ℤ) ∣ D.trailingCoeff := by
    have h : (10 : ℤ) ∣ F.eval 0 := by lia
    rwa [← coeff_zero_eq_eval_zero, hFc] at h
  have hb : -9 ≤ D.trailingCoeff ∧ D.trailingCoeff ≤ 9 := by
    have ha := hc1 D.natTrailingDegree
    have hb2 := hc2 D.natTrailingDegree
    have hDk : D.coeff D.natTrailingDegree =
        Q₁.coeff D.natTrailingDegree - Q₂.coeff D.natTrailingDegree := by
      rw [hD]; exact coeff_sub _ _ _
    show -9 ≤ D.coeff D.natTrailingDegree ∧ D.coeff D.natTrailingDegree ≤ 9
    rw [hDk]; lia
  exact htc (by lia)

snip end

problem usa1997_p3 (n : ℤ) :
    ∃! Q : ℤ[X], (∀ i, 0 ≤ Q.coeff i ∧ Q.coeff i ≤ 9) ∧
      Q.eval (-2) = n ∧ Q.eval (-5) = n := by
  obtain ⟨Q, hQ⟩ := exists_good n n (by simp)
  exact ⟨Q, hQ, fun Q' hQ' ↦ good_unique Q' Q n hQ' hQ⟩

end Usa1997P3
