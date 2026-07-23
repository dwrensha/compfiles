/-
Copyright (c) 2024 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# USA Mathematical Olympiad 2017, Problem 5

Determine the set of positive real numbers c such that there exists
a labeling of the lattice points in ℤ² with positive integers for which:

  1. only finitely many distinct labels occur, and
  2. for each label i, the distance between any two points labeled i
     is at least cⁱ.
-/

namespace Usa2017P5

determine solution_set : Set ℝ := Set.Ioo 0 (Real.sqrt 2)

noncomputable def dist : ℤ × ℤ → ℤ × ℤ → ℝ
| ⟨x1, y1⟩, ⟨x2, y2⟩ => Real.sqrt ((x2 - x1)^2 + (y2 - y1)^2)

snip begin
-- Solution adapted from Evan Chen's presentation of Calvin Deng's solution: https://web.evanchen.cc/exams/USAMO-2017-notes.pdf
open Real
set_option linter.flexible true

abbrev off (v : ℤ × ℤ) (p : ℕ × ℕ) : ℤ × ℤ :=
  (v + ((p.1 : ℤ), (p.2 : ℤ)))

example (a b : ℕ) (h1 : a < b) (h2 : b < a + 2) : b = a + 1 := by
  sorry

-- points close to a point p cannot be the labelled the same as p itself
lemma exclusion {l : ℤ × ℤ → ℕ} (l_dist: ∀ {p1 p2}, p1 ≠ p2 → (l p1 = l p2) → √2 ^ (l p1) ≤ dist p1 p2)
  {n: ℕ} {p : ℤ × ℤ} (hp : 2 * n + 1 ≤ l p)
  -- a can be weakened to only the positive part
  (a : (Finset.Icc (-2 ^ n : ℤ) (2 ^ n : ℤ) × Finset.Icc (-2 ^ n : ℤ) (2 ^ n : ℤ)))
  (ha₁: a ≠ (⟨0, by simp⟩, ⟨0, by simp⟩)) (ha₂ : |a.1.val| < 2 ^ n ∨ |a.2.val| < 2 ^ n)
    : l (p + (a.1.val, a.2.val)) ≠ l p := by
  -- otherwise, they violate the distance property of l
  contrapose! l_dist
  use p
  use p + (a.1.val, a.2.val)
  and_intros
  · contrapose! ha₁
    obtain ⟨_, _⟩ := a
    simp only [left_eq_add, Prod.mk_eq_zero] at ha₁
    congr!
    · exact ha₁.1
    · exact ha₁.2
  · exact l_dist.symm
  · rw [dist]
    suffices h: √(a.1 ^ 2 + a.2 ^ 2) < √2 ^ l p by simpa using h
    calc √(a.1 ^ 2 + a.2 ^ 2)
      _ = √(|a.1.val| ^ 2 + |a.2.val| ^ 2) := by simp [@sq_abs]
      _ < √((2 ^ n) ^ 2 + (2 ^ n) ^ 2) := by
        rw [Real.sqrt_lt_sqrt_iff_of_pos (by simp)]
        obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := a
        replace hx := abs_le.mpr $ Finset.mem_Icc.mp hx
        replace hy := abs_le.mpr $ Finset.mem_Icc.mp hy
        rw [add_lt_add_iff_of_le_of_le (sq_le_sq.mpr (by simp; norm_cast)) (sq_le_sq.mpr (by simp; norm_cast))]
        simp_rw [Int.cast_abs] at ha₂ ⊢
        rcases ha₂ with _ | _
        · left; refine (sq_lt_sq₀ (abs_nonneg _) (by simp)).mpr (by norm_cast)
        · right; refine (sq_lt_sq₀ (abs_nonneg _) (by simp)).mpr (by norm_cast)
      _ = √(2 ^ (2 * n + 1)) := by rw [← mul_two, ← pow_mul', ← pow_succ]
      _ = √2 ^ (2 * n + 1) := by simp [Real.sqrt_eq_rpow, ← Real.rpow_pow_comm]
      _ ≤ √2 ^ l p := (pow_le_pow_iff_right₀ Real.one_lt_sqrt_two).mpr hp

lemma square_squeeze (n : ℕ) (l : ℤ × ℤ → ℕ) (_l_fin: (Set.range l).Finite) (_l_pos: ∀ p, 0 < l p)
  (l_dist: ∀ {p1 p2}, p1 ≠ p2 → (l p1 = l p2) → √2 ^ (l p1) ≤ dist p1 p2)
  : ∀ v : ℤ × ℤ, ∃ p : Finset.range (2 ^ (n + 1)) × Finset.range (2 ^ (n + 1)), 2 * (n + 1) < l (off v (p.1, p.2)) := by
  intro v
  induction n generalizing v with
  | zero =>
    contrapose! l_dist
    by_cases h : l (0, 0) = l (0, 1)

    refine ⟨(0, 0), (0, 1), by simp, ?_, ?_⟩


    sorry
    simp [dist]
    all_goals sorry
  | succ n ih =>
    -- assume a quadrant has no label > 2 * (n + 2)
    wlog! quadrant : ∀ (p : Finset.range (2 ^ (n + 1)) × Finset.range (2 ^ (n + 1))), l (off v (p.1, p.2)) ≤ 2 * (n + 1 + 1)
    · obtain ⟨⟨⟨x, hx⟩, ⟨y, hy⟩⟩, hp⟩ := quadrant
      -- for some reason grind doens't work on the latter hole
      use ⟨⟨x, by grind⟩, ⟨y, ?_⟩⟩
      simp only [Finset.mem_range] at hy ⊢
      apply hy.trans_le
      grind
    -- then the quadrant must have a label > 2 * n
    have ⟨⟨x₁, y₁⟩, h₁⟩ := ih v
    let p₁ := off v (x₁, y₁)
    have p₁_lb : 2 * (n + 1) + 1 ≤ l p₁  := by
      rwa [Nat.lt_iff_add_one_le] at h₁
    have p₁_ub := quadrant (x₁, y₁)
    -- construct A, then it must also contain a label > 2 * (n + 1), and is distinct from the first point
    let v₂ := ((1 + x₁ : ℤ), (0 : ℤ))
    have ⟨(x₂, y₂), h₂⟩ := ih (v + v₂)
    let p₂ := off (v + v₂) (x₂, y₂)
    have p₂_lb : 2 * (n + 1) + 1 ≤ l p₂ := by
      rwa [Nat.lt_iff_add_one_le] at h₂
    wlog! p₂_ub : l p₂ ≤ 2 * (n + 2)
    · use ⟨⟨1 + x₁ + x₂, by grind⟩, ⟨y₂, by grind⟩⟩
      simpa [p₂, v₂, off, add_assoc] using p₂_ub
    have p₁_ne_p₂ : l p₁ ≠ l p₂ := by
      obtain ⟨x₁, hx₁⟩ := x₁
      obtain ⟨x₂, hx₂⟩ := x₂
      obtain ⟨y₁, hy₁⟩ := y₁
      obtain ⟨y₂, hy₂⟩ := y₂
      rw [Finset.mem_range] at hx₁ hx₂ hy₁ hy₂
      have := exclusion l_dist p₁_lb
        (⟨x₂ + 1, ?_⟩, ⟨y₂ - y₁, ?_⟩) (not_eq_of_beq_eq_false rfl) ?_
      · obtain ⟨_, _⟩ := v
        symm at this
        simpa [off, v₂, p₁, p₂, add_assoc, add_rotate'] using this
      · simp [Finset.mem_Icc]; constructor <;> lia
      · simp [Finset.mem_Icc]; constructor <;> lia
      -- prove that p₂ is close enough to p₁
      · right
        refine abs_sub_lt_of_nonneg_of_lt ?_ ?_ ?_ ?_
        <;> first | exact Int.natCast_nonneg _ | norm_cast
    -- plumbing: if the label > 2 * (n + 1) and cannot be the same as p₁ and p₂, it must by > 2 * (n + 2)
    have pigeonhole (p: ℤ × ℤ) (hp : 2 * (n + 1) < l p) (h_ne₁ : l p ≠ l p₁) (h_ne₂ : l p ≠ l p₂) : 2 * (n + 2) < l p := by
      by_cases! hp₁ : l p₁ = 2 * (n + 1) + 1
      · have hp₂ : l p₂ = 2 * (n + 2) := by
          rw [hp₁] at p₁_ne_p₂
          rw [le_iff_exists_add] at p₂_lb
          obtain ⟨c, hc⟩ := p₂_lb
          rcases c with rfl | rfl | c <;> lia
        rcases lt_iff_exists_add.mp hp with rfl | rfl | rfl | c <;> lia
      · replace ⟨hp₂, hp₁⟩ : l p₂ = 2 * (n + 1) + 1 ∧ l p₁ = 2 * (n + 2) := by
          rw [le_iff_exists_add] at p₁_lb
          obtain ⟨c, hc⟩ := p₁_lb
          rcases c with rfl | rfl | c <;> try lia
        rcases lt_iff_exists_add.mp hp with rfl | rfl | rfl | c <;> lia
    -- construct B, which touches both p₁ and p₂
    by_cases h : y₁ ≤ y₂
    · let v₃ := ((v₂.1 + x₂ - 2 ^ (n + 1) : ℤ), (y₁ + 1: ℤ))
      have ⟨(x₃, y₃), h₂⟩ := ih (v + v₃)
      let p₃ := off (v + v₃) (x₃, y₃)
      have p₃_ne_p₁ : l p₃ ≠ l p₁ := sorry
      have p₃_ne_p₂ : l p₃ ≠ l p₂ := sorry
      use (⟨1 + x₁ + x₂ - 2 ^ (n + 1) + x₃, ?_⟩, ⟨y₁ + 1 + y₃, ?_⟩)
      have := pigeonhole p₃ sorry p₃_ne_p₁ p₃_ne_p₂
      simp [p₃, off, v₃, v₂, add_assoc] at this ⊢
      convert this
      sorry
      obtain ⟨x₂, hx₂⟩ := x₂
      obtain ⟨x₃, hx₃⟩ := x₃

      rw [Finset.mem_range]
      suffices h : ↑x₂ - 2 ^ (n + 1) < (2 ^ (n + 1)) by
        sorry

      all_goals sorry
    · have v₃ := (v₂.1, (y₂ + 1: ℤ))

      all_goals sorry

snip end

-- def d (n : ℕ) : ℕ := by
--   cases Nat.even_or_odd n with
--   | odd => exact 1
--   | even => exact 1

problem usa2017_p5 (c : ℝ) :
  c ∈ solution_set ↔
  (0 < c ∧
    ∃ l : ℤ × ℤ → ℕ,
      (Set.range l).Finite ∧
      (∀ p, 0 < l p) ∧
      ∀ {p1 p2}, p1 ≠ p2 → (l p1 = l p2) →
          c ^ (l p1) ≤ dist p1 p2) := by
  rw [solution_set, Set.mem_Ioo, and_congr_right_iff]
  intro c_pos
  constructor
  · intro c_lt
    -- calculate an upper bound
    have ⟨n, hn⟩ : ∃ n : ℕ, n > (Real.log √2) / (Real.log √2 - Real.log c) := exists_nat_gt _
    have : c ^ n < √2 ^ ((n: ℤ) - 1) := by
      rw [zpow_natCast_sub_one₀ (by simp), Real.pow_lt_iff_lt_log c_pos (by simp)]
      rw [log_div (by simp) (by simp), log_pow, lt_sub_comm, ← mul_sub, ← div_lt_iff₀ ?_]
      · norm_cast
      · rw [← log_div (by simp) (by linarith)]
        apply log_pos
        field_simp
        exact c_lt
    -- the construction here is basically a truncation of an infinite one,
    -- use Nat.findGreatest?

    sorry
  · contrapose
    -- Any counterexample we have for c = √2 works for c > √2 as well
    wlog hc : √2 = c with rest
    · push Not at rest ⊢
      exact fun h => (have ⟨p1, p2, h1, h2, h3⟩ := rest √2 (by simp) (by simp) (by simp) · · ·
        ⟨p1, p2, h1, h2, h3.trans_le <| pow_le_pow_left₀ (by simp) h _⟩)
    subst hc
    rintro - ⟨l, l_fin, l_pos, l_dist⟩
    -- Get an upper bound for the labelling
    have h := l_fin
    simp_rw [Set.finite_iff_bddAbove, bddAbove_def] at h
    obtain ⟨n, hn⟩ := h
    -- Construct a large enough square to force a label exceeding the bound
    have ⟨p, hp⟩ := square_squeeze n l l_fin l_pos l_dist (0, 0)
    specialize hn (l (off (0,0) (p.1, p.2))) (Set.mem_range_self _)
    linarith


end Usa2017P5
