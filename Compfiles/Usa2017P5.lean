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

def labelling (c: ℝ) := { l : ℤ × ℤ → ℕ //
  (Set.range l).Finite ∧
  (∀ p, 0 < l p) ∧
  ∀ {p1 p2}, p1 ≠ p2 → (l p1 = l p2) →
      c ^ (l p1) ≤ dist p1 p2}

@[ext]
theorem labelling.ext {c : ℝ} (l₁ l₂ : labelling c) : l₁.1 = l₂.1 → l₁ = l₂ := by
  intro h
  obtain ⟨l₁, _⟩ := l₁
  obtain ⟨l₂, _⟩ := l₂
  simp at h
  simp [h]

-- this doesn't work yet, simp still needs to reduce the funlike to its underlying function
instance (c: ℝ) : FunLike (labelling c) (ℤ × ℤ) ℕ := by
  refine ⟨(·.1), fun ⟨l, hl⟩ ⟨l', hl'⟩ => ?_⟩
  rintro rfl
  simp

abbrev transpose (p : ℤ × ℤ) {c : ℝ} (l: labelling c) : {l': labelling c // l'.1 = l.1 ∘ (fun (q : ℤ × ℤ) => (p.1 + q.1, p.2 + q.2)) } := by
  have ⟨l, fin, pos, hdist⟩ := l
  let f (q : ℤ × ℤ) := (p.1 + q.1, p.2 + q.2)
  constructor
  case val =>
    use l ∘ f
    and_intros
    · rw [Set.finite_iff_bddAbove, bddAbove_def] at fin ⊢
      aesop
    · intros; simpa using pos _
    · intro p1 p2 ne lbl
      apply_fun f at ne using (by intro _ _; grind : Function.Injective f)
      simpa [dist, f] using hdist ne lbl
  rfl

abbrev flip (n : ℕ) {c : ℝ} (l: labelling c) : labelling c := by
  let f (p: ℤ × ℤ) := (2 ^ n - 1 - p.1, p.2)
  use l ∘ f
  obtain ⟨l, fin, pos, hdist⟩ := l
  and_intros
  · rw [Set.finite_iff_bddAbove, bddAbove_def] at fin ⊢
    aesop
  · intros;
    simpa [DFunLike.coe] using pos _
  · intro p1 p2 ne lbl
    apply_fun f at ne using (by intro _ _; grind : Function.Injective f)
    simpa [DFunLike.coe, dist, f, sub_sq_comm] using hdist ne lbl

example (c : ℝ) (n : ℕ) (p : ℤ × ℤ) (l: labelling c) : flip n l p = l (2 ^ n - 1 - p.1, p.2) := by
  simp [DFunLike.coe]

abbrev off (v : ℤ × ℤ) (p : ℕ × ℕ) : ℤ × ℤ :=
  (v + ((p.1 : ℤ), (p.2 : ℤ)))

lemma dist_lt {p : ℤ × ℤ} {l : ℤ × ℤ → ℕ} {n : ℕ} (hp : 2 * n + 1 ≤ l p) (a : (Finset.Icc (-2 ^ n : ℤ) (2 ^ n : ℤ) × Finset.Icc (-2 ^ n : ℤ) (2 ^ n : ℤ)))
  (ha₁: a ≠ (⟨0, by simp⟩, ⟨0, by simp⟩)) (ha₂ : |a.1.val| < 2 ^ n ∨ |a.2.val| < 2 ^ n)
  : dist p (p + ((a.1 : ℤ), (a.2 : ℤ))) < √2 ^ l p := by
  rw [dist]
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
      _ ≤ √2 ^ l p := (pow_le_pow_iff_right₀ one_lt_sqrt_two).mpr hp

lemma dist_lt'  {p : ℤ × ℤ} {l : ℤ × ℤ → ℕ} {n : ℕ} (hp : l p = 2 * (n + 1)) (a : (Finset.Icc (-2 ^ n : ℤ) (2 ^ n : ℤ) × Finset.Icc (-2 ^ n : ℤ) (2 ^ n : ℤ)))
  (ha₁: a ≠ (⟨0, by simp⟩, ⟨0, by simp⟩)) : dist p (p + ((a.1 : ℤ), (a.2 : ℤ))) < √2 ^ l p := by
  rw [dist]
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
  · exact dist_lt hp a ha₁ ha₂

-- spcialized for 2 * (n + 1)
lemma exclusion' {l : ℤ × ℤ → ℕ} (l_dist: ∀ {p1 p2}, p1 ≠ p2 → (l p1 = l p2) → √2 ^ (l p1) ≤ dist p1 p2)
  {n: ℕ} {p : ℤ × ℤ} (hp : l p = 2 * (n + 1))
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
  · exact dist_lt' hp a ha₁

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
          exact hp)

      -- then the quadrant must have a label > 2 * n
      have ⟨p₀, h₀⟩ := ih ⟨vx, vy⟩
      -- we also need to assume it is the rightmost label to force the large label in A to not be in the current quadrant
      let s : Finset _ := {p : Finset.range (2 ^ n) × Finset.range (2 ^ n) | 2 * n < l (off (vx, vy) (p.1, p.2)) }
      have ⟨⟨⟨x₁, hx₁⟩, ⟨y₁, hy₁⟩⟩, p₁_lb, h₁⟩ := Finset.exists_mem_eq_sup s ⟨p₀, Finset.mem_filter_univ _ |>.mpr h₀⟩ (fun p => p.1.val)
      have rightmost (p: Finset.range (2 ^ n) × Finset.range (2 ^ n)) (h : 2 * n < l (off (vx, vy) (p.1, p.2))) : p.1 ≤ x₁ := by
        dsimp at h₁
        rw [← h₁]
        exact @Finset.le_sup _ _ _ _ s (fun p ↦ p.1.val) _ (by simpa [s] using h)
      let p₁ := off (vx, vy) (x₁, y₁)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, s] at p₁_lb
      wlog! p₁_ub : l p₁ ≤ 2 * (n + 1)
      · use ⟨⟨x₁, by grind⟩, ⟨y₁, by grind⟩⟩
      -- construct A, then it must also contain a label > 2 * (n + 1), and is distinct from the first point
      let v₂ := (vx, vy) + ((1 + x₁ : ℤ), (0 : ℤ))
      have ⟨(⟨x₂, hx₂⟩, ⟨y₂, hy₂⟩), p₂_lb⟩ := ih v₂
      let p₂ := off (vx, vy) (1 + x₁ + x₂, y₂)
      wlog! p₂_ub : l (off (vx, vy) (1 + x₁ + x₂, y₂)) ≤ 2 * (n + 1)
      · clear this -- help out grind
        use ⟨⟨1 + x₁ + x₂, by grind⟩, ⟨y₂, by grind⟩⟩
      -- A touches p₁, so A cannot use the label of p₂
      have p₁_ne_p₂ : l p₁ ≠ l p₂ := by
        simp only [Finset.mem_range] at hx₂ hy₁ hy₂
        have := exclusion l_dist p₁_lb
          (⟨x₂ + 1, by simp; norm_cast; omega⟩, ⟨y₂ - y₁, by simp; constructor <;> linarith⟩) (not_eq_of_beq_eq_false rfl) (?_)
        · symm at this
          simpa [off, v₂, p₁, p₂, add_assoc, add_rotate'] using this
        · right; simp [abs_sub_lt_iff]; constructor <;> linarith
      -- we need to show that p₂ is not in the quadrant
      have p₂x_large : 2 ^ n ≤ (1 + (x₁ + x₂): ℕ) := by
        contrapose! rightmost with p₂x_small
        refine ⟨⟨⟨1 + (x₁ + x₂), Finset.mem_range.mpr p₂x_small⟩, ⟨y₂, hy₂⟩⟩,
          by simpa [off, v₂, add_assoc] using p₂_lb, by lia⟩
      -- change x-coordinate of p₂ to start at the next quadrant
      have ⟨x₂', hx₂'⟩ : ∃ x, (1 + (x₁ + x₂) : ℕ) = 2 ^ n + x := by
        rwa [le_iff_exists_add] at p₂x_large
      -- by the bounds of A, we have that p₂.1 is not too far from p₁.1
      have : x₂' ≤ x₁ := by
        -- TODO: grind is kind of slow here
        rw [← add_le_add_iff_left (2^n), ← hx₂']
        simp at hx₂
        omega
      -- by our assumption, the labels of p₁ and p₂ are forced
      specialize quadrant (⟨x₁, hx₁⟩, ⟨y₁, hy₁⟩) (⟨x₂', by grind⟩, ⟨y₂, hy₂⟩)
      have ⟨p₁_eq, p₂_eq⟩ : l p₁ = 2 * (n + 1) ∧ l p₂ = 2 * n + 1 := by
        dsimp at quadrant
        rcases quadrant with quadrant | quadrant | quadrant
        · have p₁_eq : l p₁ = 2 * (n + 1) := by
            simp [p₁, off] at p₁_lb p₁_ub ⊢
            lia
          have p₂_eq : l p₂ = 2 * n + 1 := by
            simp [p₁_eq, p₂, v₂, off] at p₂_lb p₂_ub p₁_ne_p₂ ⊢
            lia
          exact ⟨p₁_eq, p₂_eq⟩
        · simp at quadrant; lia
        · have p₂_eq : l p₂ = 2 * n + 1 := by
            zify at hx₂'
            simp [p₂, v₂, off, ← hx₂'] at p₂_lb p₂_ub p₁_ne_p₂ quadrant ⊢
            lia
          have p₁_eq : l p₁ = 2 * (n + 1) := by
            simp [p₂_eq, p₁, off] at p₁_lb p₁_ub p₁_ne_p₂ ⊢
            lia
          exact ⟨p₁_eq, p₂_eq⟩
      -- we can now use our hypothesis, flipping the labelling
      clear p₁_lb p₁_ub p₂_lb p₂_ub rightmost quadrant
      simp [Finset.mem_range] at hx₁
      have h2 : x₂' ≤ 2^n - 1 := by
        rw [Nat.le_iff_lt_add_one, Nat.sub_add_cancel Nat.one_le_two_pow]
        lia
      have h3 : ((2 ^ n - 1 - x₂' : ℕ) : ℤ) = (2 ^ n - 1 - x₂' : ℤ) := by
        rw [Int.ofNat_sub h2, Int.ofNat_sub <| Nat.one_le_two_pow]
        push_cast
        rfl
      have h4 : x₁ ≤ 2^n - 1 := by rwa [Nat.le_sub_one_iff_lt <| Nat.two_pow_pos _]
      specialize H (-vx, vy) ⟨(⟨2^n - 1 - x₂', by rw [Finset.mem_range]; zify [h3]; lia⟩, ⟨y₂, by grind⟩), (⟨2 ^ n - 1 - x₁, by rw [Finset.mem_range]; zify [h4]; lia⟩, ⟨y₁, by grind⟩), ?_, ?_, ?_⟩
      · zify at hx₂'
        simp [DFunLike.coe, add_assoc, p₂, l', l'_bundle, hx₂', h3] at p₂_eq ⊢
        convert p₂_eq
        lia
      · simp
        zify [h3] at p₂x_large ⊢
        lia
      · simp [DFunLike.coe, l', l'_bundle, p₂, ← p₁_eq, p₁, h4] at p₂_eq ⊢
        ring_nf
      simp [l', l'_bundle] at H
      obtain ⟨x, hx, y, hy, h⟩ := H
      have h5 : ((2 ^ (n + 1) - 1 - x : ℕ) : ℤ) = (2 ^ (n + 1) - 1 - x : ℤ) := by
        rw [Int.ofNat_sub <| Nat.le_sub_one_iff_lt Nat.one_le_two_pow |>.mpr hx, Int.ofNat_sub Nat.one_le_two_pow]
        simp
      use ⟨⟨2 ^ (n+1) - 1 - x, ?_⟩, ⟨y, Finset.mem_range.mpr hy⟩⟩
      · simp [DFunLike.coe, h5] at h ⊢
        push_cast
        ring_nf at h ⊢
        exact h
      · rw [Finset.mem_range]
        zify [h5]
        lia
    obtain ⟨⟨⟨x₁, hx₁⟩, ⟨y₁, hy₁⟩⟩, ⟨⟨x₂, hx₂⟩, ⟨y₂, hy₂⟩⟩, h₁, le, h₂⟩ := quadrant

    by_cases h : y₁ ≤ y₂
    -- p₁ is at least as high as p₂, B is bounded north by p₁ and bounded east by p₂
    · let v₃ := ((x₂ : ℕ), (y₁ + 1 : ℕ))
      have ⟨(⟨x₃, hx₃⟩, ⟨y₃, hy₃⟩), h₃⟩ := ih (v + ((v₃.1 : ℤ), (v₃.2 : ℤ)))
      let p₃ := off v (v₃ + ((x₃ : ℕ), (y₃ : ℕ)))
      simp only [Subtype.mk_le_mk, Finset.mem_range] at le hx₁ hx₂ hx₃ hy₁ hy₂ hy₃
      have p₃_ne_p₁ : l p₃ ≠ 2 * n + 1 := by
        have := exclusion l_dist h₁.symm.le
          ⟨⟨x₂ + x₃ - x₁, ?_⟩, ⟨1 + y₃, by simp at hy₃ ⊢; lia⟩⟩ (by grind) ?_
        · simpa [← h₁, off, v₃, p₃, add_assoc] using this
        · simp
          norm_cast
          lia
        · left
          simp [abs_lt]
          norm_cast
          lia
      have p₃_ne_p₂ : l p₃ ≠ 2 * (n + 1) := by
        have := exclusion' l_dist h₂
          ⟨⟨x₃ - 2 ^ n, by simp; lia⟩, ⟨1 + y₁ + y₃ - y₂, ?_⟩⟩ (by norm_cast; lia)
        · simp [← h₂, off, v₃, p₃, add_assoc] at this ⊢
          ring_nf at this ⊢
          exact this
        · rw [Finset.mem_Icc]
          norm_cast
          lia
      replace h₃ : 2 * n < l p₃ := by simpa [p₃, off, v₃, add_assoc] using h₃
      have p₃_label : 2 * (n + 1) < l p₃ := by lia
      use ⟨⟨v₃.1 + x₃, by grind⟩, ⟨v₃.2 + y₃, by grind⟩⟩
      convert p₃_label <;> rfl
    -- p₂ is higher, B is bounded north by p₂ and bounded west by p₁
    · let v₃ := ((x₁ + 1 : ℕ), (y₂ + 1 : ℕ))
      have ⟨(⟨x₃, hx₃⟩, ⟨y₃, hy₃⟩), h₃⟩ := ih (v + ((v₃.1 : ℤ), (v₃.2 : ℤ)))
      simp only [Subtype.mk_le_mk, Finset.mem_range] at le hx₁ hx₂ hx₃ hy₁ hy₂ hy₃
      let p₃ := off v (v₃ + ((x₃ : ℕ), (y₃ : ℕ)))
      have p₃_ne_p₁ : l p₃ ≠ 2 * n + 1 := by
        have := exclusion l_dist h₁.symm.le
          ⟨⟨1 + x₃, by grind⟩, ⟨1 + y₃ + y₂ - y₁, by simp; norm_cast; lia⟩⟩ (by grind) (by grind)
        simp [← h₁, off, v₃, p₃, add_assoc] at this ⊢
        ring_nf at this ⊢
        exact this
      have p₃_ne_p₂ : l p₃ ≠ 2 * (n + 1) := by
        have := exclusion' l_dist h₂
          ⟨⟨1 + x₁ + x₃ - x₂ - 2 ^ n, ?_⟩, ⟨1 + y₃, ?_⟩⟩ (by norm_cast; lia)
        · simp [← h₂, off, v₃, p₃, add_assoc] at this ⊢
          ring_nf at this ⊢
          exact this
        · simp; norm_cast; lia
        · simp; norm_cast; lia
      replace h₃ : 2 * n < l p₃ := by simpa [p₃, off, v₃, add_assoc] using h₃
      have p₃_label : 2 * (n + 1) < l p₃ := by lia
      use ⟨⟨v₃.1 + x₃, by grind⟩, ⟨v₃.2 + y₃, by grind⟩⟩
      convert p₃_label <;> rfl


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
    have ⟨p, hp⟩ := square_squeeze' n l l_fin l_pos l_dist (0, 0)
    specialize hn (l (off (0,0) (p.1, p.2))) (Set.mem_range_self _)
    linarith


end Usa2017P5
