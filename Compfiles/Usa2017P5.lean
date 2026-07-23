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
-- When the two labels are not in the same row, we can make B touch both labels, implying that it must contain a larger label.
-- However, if they are in the same row, we place B touching the smaller label, and B must at least share a corner with the larger one.
-- This is just close enough to the larger label to ensure all of B doesn't contain the same label.
open Real
set_option linter.flexible true

def labelling (c: ℝ) :=  ∃ l : ℤ × ℤ → ℕ,
  (Set.range l).Finite ∧
  (∀ p, 0 < l p) ∧
  ∀ {p1 p2}, p1 ≠ p2 → (l p1 = l p2) →
      c ^ (l p1) ≤ dist p1 p2

abbrev transpose (x y : ℤ) {c : ℝ} (l: labelling c) : labelling c := by
  have ⟨l, fin, pos, hdist⟩ := l
  let f (p : ℤ × ℤ) := (p.1 + x, p.2 + y)
  use l ∘ f
  and_intros
  sorry
  · intros; simpa using pos _
  · intro p1 p2 ne lbl
    apply_fun f at ne using (by intro _ _; grind : Function.Injective f)
    simpa [dist, f] using hdist ne lbl

abbrev flip (n : ℕ) {c : ℝ} (l: labelling c) : labelling c := by
  have ⟨l, fin, pos, hdist⟩ := l
  let f (p: ℤ × ℤ) := (2 ^ n - 1 - p.1, p.2)
  use l ∘ f
  and_intros
  · rw [Set.finite_iff_bddAbove, bddAbove_def] at fin ⊢
    aesop
  · intros; simpa using pos _
  · intro p1 p2 ne lbl
    apply_fun f at ne using (by intro _ _; grind : Function.Injective f)
    simpa [dist, f, sub_sq_comm] using hdist ne lbl

abbrev off (v : ℤ × ℤ) (p : ℕ × ℕ) : ℤ × ℤ :=
  (v + ((p.1 : ℤ), (p.2 : ℤ)))


-- points close to a point p cannot be the labelled the same as p itself
lemma exclusion {l : ℤ × ℤ → ℕ} (l_dist: ∀ {p1 p2}, p1 ≠ p2 → (l p1 = l p2) → √2 ^ (l p1) ≤ dist p1 p2)
  {n: ℕ} {p : ℤ × ℤ} (hp : 2 * n < l p)
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

-- spcialized for 2 * (n + 1)
lemma exclusion' {l : ℤ × ℤ → ℕ} (l_dist: ∀ {p1 p2}, p1 ≠ p2 → (l p1 = l p2) → √2 ^ (l p1) ≤ dist p1 p2)
  {n: ℕ} {p : ℤ × ℤ} (hp : 2 * (n + 1) = l p)
  (a : (Finset.Icc (-2 ^ n : ℤ) (2 ^ n : ℤ) × Finset.Icc (-2 ^ n : ℤ) (2 ^ n : ℤ)))
  (ha₁: a ≠ (⟨0, by simp⟩, ⟨0, by simp⟩))
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
  --a good refactor would be to retrieve the dist argument out of exclusion
  · rw [dist]
    suffices h: √(a.1 ^ 2 + a.2 ^ 2) < √2 ^ l p by simpa using h
    calc √(a.1 ^ 2 + a.2 ^ 2)
      _ = √(|a.1.val| ^ 2 + |a.2.val| ^ 2) := by simp [@sq_abs]
      _ ≤ √((2 ^ n) ^ 2 + (2 ^ n) ^ 2) := by
        rw [Real.sqrt_le_sqrt_iff (by simp)]
        obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := a
        replace hx := abs_le.mpr $ Finset.mem_Icc.mp hx
        replace hy := abs_le.mpr $ Finset.mem_Icc.mp hy
        refine add_le_add (sq_le_sq.mpr (by simp; norm_cast)) (sq_le_sq.mpr (by simp; norm_cast))
      _ = √(2 ^ (2 * n + 1)) := by rw [← mul_two, ← pow_mul', ← pow_succ]
      _ = √2 ^ (2 * n + 1) := by simp [Real.sqrt_eq_rpow, ← Real.rpow_pow_comm]
      _ < √2 ^ l p := pow_lt_pow_right₀ one_lt_sqrt_two (by linarith)

lemma square_squeeze' (n : ℕ) (l : ℤ × ℤ → ℕ) (_l_fin: (Set.range l).Finite) (l_pos: ∀ p, 0 < l p)
  (l_dist: ∀ {p1 p2}, p1 ≠ p2 → (l p1 = l p2) → √2 ^ (l p1) ≤ dist p1 p2)
  : ∀ v : ℤ × ℤ, ∃ p : Finset.range (2 ^ n) × Finset.range (2 ^ n), 2 * n < l (off v (p.1, p.2)) := by
  induction n with
  | zero => exact fun v =>
    -- by positivity we must have a label > 0
    -- this elides the need to check the n = 1 case
    ⟨(⟨0, by simp⟩, ⟨0, by simp⟩), by simpa using l_pos (off v (0, 0))⟩
  | succ n ih =>
    intro v
    -- we prove the setup of the two large labels here
    wlog quadrant : ∃ p₁ p₂ : Finset.range (2 ^ n) × Finset.range (2 ^ n), l (off v (p₁.1, p₁.2)) = 2 * n + 1
      ∧ p₂.1 ≤ p₁.1 ∧ l (off v (2 ^ n + p₂.1, p₂.2)) = 2 * (n + 1) generalizing l ih v with H
    · push +distrib Not at quadrant
      obtain ⟨vx, vy⟩ := v
      -- In both cases, we can flip the labelling and continue
      let l'_bundle := flip (n+1) ⟨l, _l_fin, l_pos, l_dist⟩
      let l' := l'_bundle.1 -- maintain provenence of flip
      specialize H l' l'_bundle.2.1 l'_bundle.2.2.1 l'_bundle.2.2.2 (fun v => by
        have ⟨⟨⟨x, hx⟩, y⟩, hp⟩ := ih (2^n-v.1, v.2)
        have h1 : x ≤ 2 ^ n - 1 := by
          rw [Finset.mem_range] at hx
          rw [Nat.le_sub_one_iff_lt (by lia)]
          grind
        have h2 : 2 ^ n - 1 - x < 2 ^ n := by
          zify
          rw [Int.ofNat_sub h1, Int.ofNat_sub <| Nat.one_le_two_pow]
          push_cast
          omega
        refine ⟨⟨⟨2^n - 1 - x, by simpa using h2⟩, y⟩ , ?_⟩
        simp only [Prod.mk_add_mk, Function.comp_apply, Prod.fst_add, Prod.snd_add, l',
          l'_bundle] at hp ⊢
        rw [Int.ofNat_sub h1, Int.ofNat_sub <| Nat.one_le_two_pow]
        · push_cast
          ring_nf at hp ⊢
          exact hp) (2^n-vx, vy)

      rcases quadrant with quadrant | quadrant
      -- say the quadrant indeed has a label 2 * (n + 1)
      · have ⟨⟨x₁, y₁⟩, p₁_lb⟩ := ih (vx, vy)
        let p₁ := off (vx, vy) (x₁, y₁)
        wlog! p₁_ub : l p₁ ≤ 2 * (n + 1)
        · use ⟨⟨x₁, by grind⟩, ⟨y₁, by grind⟩⟩
        have := quadrant ⟨x₁, y₁⟩
        have p₁_eq : l p₁ = 2 * (n + 1) := by lia
        -- then we can force a label of 2 * n + 1 using A
        let v₂ := ((1 + x₁ : ℕ), 0)
        have ⟨(x₂, y₂), p₂_lb⟩ := ih ((vx, vy) + (↑v₂.1, ↑v₂.2))
        let p₂ := off ((vx, vy) + ((v₂.1 : ℤ), (v₂.2 : ℤ))) (x₂, y₂)
        wlog! p₂_ub : l p₂ ≤ 2 * (n + 1)
        · use ⟨⟨1 + x₁ + x₂, by grind⟩, ⟨y₂, by grind⟩⟩
          simpa [v₂, p₂, add_assoc, off] using p₂_ub
        have p₂_ne : l p₂ ≠ 2 * (n + 1) := by
          -- A touches p₁, so p₂ cannot use the label of p₂
          have := exclusion' l_dist p₁_eq.symm
            (⟨x₂ + 1, by simp; norm_cast; grind⟩, ⟨y₂ - y₁, by simp; norm_cast; grind⟩) (not_eq_of_beq_eq_false rfl)
          simpa [off, v₂, p₁, p₂, add_assoc, add_rotate', ← p₁_eq] using this
        have p₂_eq : l p₂ = 2 * n + 1 := by lia
        let ⟨⟨⟨x₃, hx₃⟩, y₃⟩, p₃_lb⟩ := H ⟨⟨?_, ?_⟩ , ⟨?_, ?_⟩⟩
        · let p₃ := (x₃, y₃)
          use ⟨⟨2 ^ n - 1 - p₃.1, by grind⟩, p₃.2⟩
          dsimp [l', l'_bundle, off] at p₃_lb ⊢
          rw [Int.ofNat_sub (by simp [p₃] at hx₃ ⊢; grind), Int.ofNat_sub (by grind)]
          push_cast at p₃_lb ⊢
          ring_nf at p₃_lb ⊢
          exact p₃_lb
        -- put in our flipped p₁ and p₂
        · refine ⟨⟨2 ^ n - 1 - (v₂.1 + x₂ : ℕ), by simp; zify; sorry⟩, y₂⟩
        · dsimp [l', l'_bundle]
          rw [← p₂_eq]
          rw [Int.ofNat_sub ?_]
          simp [p₂, off, v₂]
          ring_nf

          all_goals sorry
        · refine ⟨⟨2 ^ n - 1 - (x₁ : ℕ), by simp; sorry⟩, y₁⟩
        · dsimp [l', l'_bundle]
          rw [← p₁_eq, Int.ofNat_sub <| Nat.le_sub_one_iff_lt (Nat.two_pow_pos n) |>.mpr (by grind)]
          simp [p₁]
          ring_nf
      · all_goals sorry
    have pigeonhole (p: ℤ × ℤ) (hp : 2 * n < l p) (h_ne₁ : l p ≠ 2 * n + 1) (h_ne₂ : l p ≠ 2 * (n + 1)) : 2 * (n + 1) < l p := by lia
    -- assume a quadrant has no label > 2 * (n + 2)
    -- construct B, which touches both p₁ and p₂
    -- we can then use pigeonhole to show B contains a large enough label
    obtain ⟨⟨⟨x₁, y₁⟩, h₁⟩, ⟨⟨x₂, y₂⟩, h₂⟩⟩ := quadrant

    by_cases h : y₁ ≤ y₂
    -- p₁ is at least as high as p₂, B is bounded north by p₁ and bounded east by p₂
    · let v₃ := ((x₂ : ℕ), (y₁ + 1 : ℕ))
      have ⟨(x₃, y₃), h₃⟩ := ih (v + ((v₃.1 : ℤ), (v₃.2 : ℤ)))
      let p₃ := off v (v₃ + ((x₃ : ℕ), (y₃ : ℕ)))
      have p₃_ne_p₁ : l p₃ ≠ 2 * n + 1 := by
        -- rw [← h₁]
        obtain ⟨y₃, hy₃⟩ := y₃
        have h1 : (x₂.val + x₃.val - x₁.val : ℤ) ∈ Finset.Icc (-2 ^ n) (2 ^ n) := by
          simp
          sorry
        have := exclusion l_dist h₁.symm.le
          ⟨⟨x₂ + x₃ - x₁, h1⟩, ⟨1 + y₃, by simp at hy₃ ⊢; constructor <;> linarith⟩⟩ (by grind) (by simp; sorry)
        simpa [← h₁, off, v₃, p₃, add_assoc] using this
      have p₃_ne_p₂ : l p₃ ≠ 2 * (n + 1) := by
        obtain ⟨x₃, hx₃⟩ := x₃
        have := exclusion' l_dist h₂.symm
          ⟨⟨x₃ - 2 ^ n, by simp at hx₃ ⊢; linarith⟩, ⟨1 + y₁ + y₃ - y₂, ?_⟩⟩ (by rw [Finset.mem_range] at hx₃; zify at hx₃; lia)
        simp [← h₂, off, v₃, p₃, add_assoc] at this ⊢
        ring_nf at this ⊢
        exact this
        calc
          1 + (y₁: ℤ) + y₃ - y₂
          _ = 1 + y₃ + y₁ - y₂ := by ring
          _ ≤ 1 + y₃ := by sorry

        sorry
      replace h₃ : 2 * n < l p₃ := by simpa [p₃, off, v₃, add_assoc] using h₃
      have p₃_label : 2 * (n + 1) < l p₃ := by lia
      use ⟨⟨v₃.1 + x₃, by grind⟩, ⟨v₃.2 + y₃, by grind⟩⟩
      simp [p₃, off, v₃, add_assoc] at p₃_ne_p₁ p₃_ne_p₂ ⊢
      simpa [p₃, off, add_assoc, v₃] using p₃_label
    -- p₂ is higher, B is bounded north by p₂ and bounded west by p₁
    ·
      all_goals sorry


        all_goals sorry
      use (⟨1 + x₁ + x₃, by grind⟩, ⟨y₂ + 1 + y₃, by grind⟩)
      simpa [p₃, off, v₃, v₂, add_assoc] using pigeonhole p₃ h₃ p₃_ne_p₁ p₃_ne_p₂

snip end

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
