/-
Copyright (c) 2024 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw, hillosanation
-/

module

public import Mathlib.Tactic

public import ProblemExtraction

@[expose] public section

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
-- Note that this version starts the induction for √2 ≤ c at n = 0 to avoid case-bashing.
open Real

def labelling (c : ℝ) := { l : ℤ × ℤ → ℕ //
  (Set.range l).Finite ∧
  (∀ p, 0 < l p) ∧
  ∀ {p1 p2}, p1 ≠ p2 → (l p1 = l p2) →
      c ^ (l p1) ≤ dist p1 p2 }

instance (c : ℝ) : FunLike (labelling c) (ℤ × ℤ) ℕ :=
  ⟨(·.1), fun _ _ => Subtype.ext⟩

attribute [local simp] DFunLike.coe

instance (n : ℕ) : CoeOut (Finset.range (2 ^ n) × Finset.range (2 ^ n)) (ℤ × ℤ) := ⟨fun ⟨x, y⟩ => ⟨x, y⟩⟩

instance : Coe (ℕ × ℕ) (ℤ × ℤ) := ⟨fun ⟨x, y⟩ => ⟨x, y⟩⟩

abbrev transpose (p : ℤ × ℤ) {c : ℝ} (l : labelling c) : labelling c := by
  let f (q : ℤ × ℤ) := p + q
  use l ∘ f
  obtain ⟨l, fin, pos, hdist⟩ := l
  and_intros
  · rw [Set.finite_iff_bddAbove, bddAbove_def] at fin ⊢
    aesop
  · intros; simpa using pos _
  · intro p1 p2 ne lbl
    apply_fun f at ne using (by intro _ _; grind : Function.Injective f)
    simpa [dist, f] using hdist ne lbl

abbrev flip (n : ℕ) {c : ℝ} (l : labelling c) : labelling c := by
  let f (p : ℤ × ℤ) := (2 ^ n - 1 - p.1, p.2)
  use l ∘ f
  obtain ⟨l, fin, pos, hdist⟩ := l
  and_intros
  · rw [Set.finite_iff_bddAbove, bddAbove_def] at fin ⊢
    aesop
  · intros;
    simpa using pos _
  · intro p1 p2 ne lbl
    apply_fun f at ne using (by intro _ _; grind : Function.Injective f)
    simpa [dist, f, sub_sq_comm] using hdist ne lbl

lemma dist_lt {p : ℤ × ℤ} {l : ℤ × ℤ → ℕ} {n : ℕ} (hp : 2 * n + 1 ≤ l p) (a : (Finset.Icc (-2 ^ n : ℤ) (2 ^ n : ℤ) × Finset.Icc (-2 ^ n : ℤ) (2 ^ n : ℤ)))
  (ha : |a.1.val| < 2 ^ n ∨ |a.2.val| < 2 ^ n)
  : dist p (p + ((a.1 : ℤ), (a.2 : ℤ))) < √2 ^ l p := by
  rw [dist]
  suffices h : √(a.1 ^ 2 + a.2 ^ 2) < √2 ^ l p by simpa using h
  calc √(a.1 ^ 2 + a.2 ^ 2)
    _ = √(|a.1.val| ^ 2 + |a.2.val| ^ 2) := by simp [@sq_abs]
    _ < √((2 ^ n) ^ 2 + (2 ^ n) ^ 2) := by
      rw [Real.sqrt_lt_sqrt_iff_of_pos (by simp)]
      obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := a
      rw [Finset.mem_Icc, ← abs_le] at hx hy
      rw [add_lt_add_iff_of_le_of_le (sq_le_sq.mpr (by simp; norm_cast)) (sq_le_sq.mpr (by simp; norm_cast))]
      simp_rw [Int.cast_abs] at ha ⊢
      rcases ha with _ | _
      · left; exact (sq_lt_sq₀ (abs_nonneg _) (by simp)).mpr (by norm_cast)
      · right; exact (sq_lt_sq₀ (abs_nonneg _) (by simp)).mpr (by norm_cast)
    _ = √2 ^ (2 * n + 1) := by simp [← mul_two, ← pow_mul', ← pow_succ, Real.sqrt_eq_rpow, ← Real.rpow_pow_comm]
    _ ≤ √2 ^ l p := (pow_le_pow_iff_right₀ one_lt_sqrt_two).mpr hp

lemma dist_lt' {p : ℤ × ℤ} {l : ℤ × ℤ → ℕ} {n : ℕ} (hp : l p = 2 * (n + 1)) (a : (Finset.Icc (-2 ^ n : ℤ) (2 ^ n : ℤ) × Finset.Icc (-2 ^ n : ℤ) (2 ^ n : ℤ)))
  : dist p (p + ((a.1 : ℤ), (a.2 : ℤ))) < √2 ^ l p := by
  rw [dist]
  suffices h : √(a.1 ^ 2 + a.2 ^ 2) < √2 ^ l p by simpa using h
  calc √(a.1 ^ 2 + a.2 ^ 2)
    _ = √(|a.1.val| ^ 2 + |a.2.val| ^ 2) := by simp [@sq_abs]
    _ ≤ √((2 ^ n) ^ 2 + (2 ^ n) ^ 2) := by
      rw [Real.sqrt_le_sqrt_iff (by simp)]
      obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := a
      rw [Finset.mem_Icc, ← abs_le] at hx hy
      exact add_le_add (sq_le_sq.mpr (by simp; norm_cast)) (sq_le_sq.mpr (by simp; norm_cast))
    _ = √2 ^ (2 * n + 1) := by simp [← mul_two, ← pow_mul', ← pow_succ, Real.sqrt_eq_rpow, ← Real.rpow_pow_comm]
    _ < √2 ^ l p := pow_lt_pow_right₀ one_lt_sqrt_two (by linarith)

lemma dist_ne {p₁ p₂ : ℤ × ℤ} (h : p₁ ≠ p₂) : 1 ≤ dist p₁ p₂ := by
  obtain ⟨x₁, y₁⟩ := p₁
  obtain ⟨x₂, y₂⟩ := p₂
  rw [dist]
  refine one_le_sqrt.mpr ?_
  norm_cast
  simp at h
  by_cases h2 : x₁ = x₂
  · simp [h2]
    grind
  · rw [← sq_abs]
    have : 1 ≤ |x₂ - x₁| ^ 2 := by refine one_le_pow₀ (by grind)
    nlinarith

lemma dist_scale {a b c d : ℤ} : dist (a * 2, b * 2) (c * 2, d * 2) = dist (a, b) (c, d) * 2 := by
  simp_rw [dist]
  norm_cast
  simp_rw [← sub_mul, mul_pow, ← add_mul, Int.cast_mul]
  push_cast
  rw [sqrt_mul (by nlinarith)]
  ring

lemma exclusion {l : ℤ × ℤ → ℕ} (l_dist : ∀ {p1 p2}, p1 ≠ p2 → (l p1 = l p2) → √2 ^ (l p1) ≤ dist p1 p2)
  {n : ℕ} {a : (Finset.Icc (-2 ^ n : ℤ) (2 ^ n : ℤ) × Finset.Icc (-2 ^ n : ℤ) (2 ^ n : ℤ))} {p : ℤ × ℤ}
  (ha₂ : dist p (p + ((a.1 : ℤ), (a.2 : ℤ))) < √2 ^ l p) (ha₁ : a ≠ (⟨0, by simp⟩, ⟨0, by simp⟩))
  : l (p + (a.1.val, a.2.val)) ≠ l p := by
  -- points close to a point p cannot be the labelled the same as p itself
  -- otherwise, they violate the distance property of l
  contrapose! l_dist
  refine ⟨p, p + (a.1.val, a.2.val), ?_, l_dist.symm, ha₂⟩
  contrapose! ha₁
  simp only [left_eq_add, Prod.mk_eq_zero] at ha₁
  congr!
  · exact ha₁.1
  · exact ha₁.2

lemma square_squeeze' (n : ℕ) (l : labelling √2)
  : ∃ p : Finset.range (2 ^ n) × Finset.range (2 ^ n), 2 * n < l p := by
  induction n generalizing l with
  -- by positivity we must have a label > 0
  -- this elides the need to check the n = 1 case
  | zero => exact ⟨(⟨0, by simp⟩, ⟨0, by simp⟩), by simpa using l.2.2.1 (0, 0)⟩
  | succ n ih =>
    -- we prove the setup of the two large labels here
    wlog setup : ∃ p₁ p₂ : Finset.range (2 ^ n) × Finset.range (2 ^ n), l p₁ = 2 * n + 1
      ∧ p₂.1 ≤ p₁.1 ∧ l (2 ^ n + p₂.1, p₂.2) = 2 * (n + 1) generalizing l with H
    · push +distrib Not at setup
      have l_dist := @l.2.2.2
      -- In both cases, we can flip the labelling and continue
      let l' := flip (n+1) l
      specialize H l'
      -- then the quadrant must have a label > 2 * n
      have ⟨p₀, h₀⟩ := ih l
      -- we also need to assume it is the rightmost label to force the large label in A to not be in the current quadrant
      let s : Finset _ := {p : Finset.range (2 ^ n) × Finset.range (2 ^ n) | 2 * n < l p }
      have ⟨⟨⟨x₁, hx₁⟩, ⟨y₁, hy₁⟩⟩, p₁_lb, h₁⟩ := Finset.exists_mem_eq_sup s ⟨p₀, Finset.mem_filter_univ _ |>.mpr h₀⟩ (·.1.val)
      have rightmost (p: Finset.range (2 ^ n) × Finset.range (2 ^ n)) (h : 2 * n < l p) : p.1 ≤ x₁ := by
        dsimp at h₁
        rw [← h₁]
        exact @Finset.le_sup _ _ _ _ s (fun p ↦ p.1.val) _ (by simpa [s] using h)
      let p₁ := (x₁, y₁)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, s] at p₁_lb
      wlog! p₁_ub : l p₁ ≤ 2 * (n + 1)
      · use ⟨⟨x₁, by grind⟩, ⟨y₁, by grind⟩⟩
      -- construct A, then it must also contain a label > 2 * (n + 1), and is distinct from the first point
      let v₂ := ((1 + x₁ : ℤ), (0 : ℤ))
      have ⟨(⟨x₂, hx₂⟩, ⟨y₂, hy₂⟩), p₂_lb⟩ := ih (transpose v₂ l)
      let p₂ := (1 + x₁ + x₂, y₂)
      wlog! p₂_ub : l ((1 + x₁ + x₂, y₂)) ≤ 2 * (n + 1)
      · clear this -- help out grind
        exact ⟨⟨⟨1 + x₁ + x₂, by grind⟩, ⟨y₂, by grind⟩⟩, p₂_ub⟩
      -- A touches p₁, so A annot use the label of p₂
      have p₁_ne_p₂ : l p₁ ≠ l p₂ := by
        simp only [Finset.mem_range] at hx₂ hy₁ hy₂
        have dist_lt := dist_lt p₁_lb (⟨x₂ + 1, by simp; norm_cast; omega⟩, ⟨y₂ - y₁, by simp; constructor <;> linarith⟩) ?_
        · have := exclusion l_dist dist_lt (not_eq_of_beq_eq_false rfl)
          simpa [p₁, p₂, add_assoc, add_rotate'] using this.symm
        · right; simp [abs_sub_lt_iff]; constructor <;> linarith
      -- we need to show that p₂ is not in the quadrant
      have p₂x_large : 2 ^ n ≤ (1 + (x₁ + x₂): ℕ) := by
        contrapose! rightmost with p₂x_small
        exact ⟨⟨⟨1 + (x₁ + x₂), Finset.mem_range.mpr p₂x_small⟩, ⟨y₂, hy₂⟩⟩,
          by simpa [v₂, add_assoc, transpose] using p₂_lb, by lia⟩
      -- change x-coordinate of p₂ to start at the next quadrant
      have ⟨x₂', hx₂'⟩ : ∃ x, (1 + (x₁ + x₂) : ℕ) = 2 ^ n + x := by
        rwa [le_iff_exists_add] at p₂x_large
      -- by the bounds of A, we have that p₂.1 is not too far from p₁.1
      have : x₂' ≤ x₁ := by grind
      -- by our assumption, the labels of p₁ and p₂ are forced
      specialize setup (⟨x₁, hx₁⟩, ⟨y₁, hy₁⟩) (⟨x₂', by grind⟩, ⟨y₂, hy₂⟩)
      have ⟨p₁_eq, p₂_eq⟩ : l p₁ = 2 * (n + 1) ∧ l p₂ = 2 * n + 1 := by
        dsimp at setup
        rcases setup with setup | setup | setup
        · have p₁_eq : l p₁ = 2 * (n + 1) := by
            simp [p₁] at p₁_lb p₁_ub ⊢
            lia
          have p₂_eq : l p₂ = 2 * n + 1 := by
            simp [↓p₁_eq, p₂, v₂] at p₂_lb p₂_ub p₁_ne_p₂ ⊢
            lia
          exact ⟨p₁_eq, p₂_eq⟩
        · simp at setup; lia
        · have p₂_eq : l p₂ = 2 * n + 1 := by
            zify at hx₂'
            simp [p₂, v₂, ← hx₂'] at p₂_lb p₂_ub p₁_ne_p₂ setup ⊢
            lia
          have p₁_eq : l p₁ = 2 * (n + 1) := by
            simp [↓p₂_eq, p₁] at p₁_lb p₁_ub p₁_ne_p₂ ⊢
            lia
          exact ⟨p₁_eq, p₂_eq⟩
      -- we can now use our hypothesis, flipping the labelling
      clear p₁_lb p₁_ub p₂_lb p₂_ub rightmost setup
      simp [Finset.mem_range] at hx₁
      have h2 : x₂' ≤ 2^n - 1 := by
        rw [Nat.le_iff_lt_add_one, Nat.sub_add_cancel Nat.one_le_two_pow]
        lia
      have h3 : ((2 ^ n - 1 - x₂' : ℕ) : ℤ) = 2 ^ n - 1 - x₂' := by
        rw [Int.ofNat_sub h2, Int.ofNat_sub <| Nat.one_le_two_pow]
        push_cast
        rfl
      have h4 : x₁ ≤ 2^n - 1 := by rwa [Nat.le_sub_one_iff_lt <| Nat.two_pow_pos _]
      zify at hx₂' p₂x_large
      specialize H ⟨(⟨2^n - 1 - x₂', by rw [Finset.mem_range]; lia⟩, ⟨y₂, by lia⟩), (⟨2 ^ n - 1 - x₁, by rw [Finset.mem_range]; lia⟩, ⟨y₁, by lia⟩), ?_, ?_, ?_⟩
      · simp [add_assoc, p₂, l', hx₂'] at p₂_eq ⊢
        grind
      · simp only [Subtype.mk_le_mk]
        lia
      · simp [l', p₂, ← p₁_eq, p₁, h4] at p₂_eq ⊢
        ring_nf
      obtain ⟨⟨⟨x, hx⟩, ⟨y, hy⟩⟩, h⟩ := H
      simp only [l', Finset.mem_range] at h hx hy
      have h5 : ((2 ^ (n + 1) - 1 - x : ℕ) : ℤ) = 2 ^ (n + 1) - 1 - x := by
        rw [Int.ofNat_sub <| Nat.le_sub_one_iff_lt Nat.one_le_two_pow |>.mpr hx, Int.ofNat_sub Nat.one_le_two_pow]
        simp
      use ⟨⟨2 ^ (n+1) - 1 - x, ?_⟩, ⟨y, Finset.mem_range.mpr hy⟩⟩
      · simp [h5] at h ⊢
        lia
      · rw [Finset.mem_range]
        lia
    have exclusion := @exclusion _ l.2.2.2
    obtain ⟨⟨⟨x₁, hx₁⟩, ⟨y₁, hy₁⟩⟩, ⟨⟨x₂, hx₂⟩, ⟨y₂, hy₂⟩⟩, h₁, le, h₂⟩ := setup
    -- we follow the split of cases in the solution
    by_cases h : y₁ ≤ y₂
    -- p₁ is at least as high as p₂, B is bounded north by p₁ and bounded east by p₂
    · let v₃ := ((x₂ : ℕ), (y₁ + 1 : ℕ))
      have ⟨(⟨x₃, hx₃⟩, ⟨y₃, hy₃⟩), h₃⟩ := ih (transpose v₃ l)
      simp only [Subtype.mk_le_mk, Finset.mem_range] at le hx₁ hx₂ hx₃ hy₁ hy₂ hy₃
      let p₃ := v₃ + (x₃, y₃)
      have p₃_ne_p₁ : l p₃ ≠ 2 * n + 1 := by
        have dist_lt := dist_lt h₁.symm.le ⟨⟨x₂ + x₃ - x₁, by simp; lia⟩, ⟨1 + y₃, by simp; lia⟩⟩ (by simp [abs_lt]; lia)
        have := exclusion dist_lt (by lia)
        simpa [← h₁, v₃, p₃, add_assoc] using this
      have p₃_ne_p₂ : l p₃ ≠ 2 * (n + 1) := by
        have dist_lt := dist_lt' h₂ ⟨⟨x₃ - 2 ^ n, by simp; lia⟩, ⟨1 + y₁ + y₃ - y₂, by simp; lia⟩⟩
        have := exclusion dist_lt (by lia)
        simp [← h₂, v₃, p₃, add_assoc] at this ⊢
        grind
      replace h₃ : 2 * n < l p₃ := by simpa [p₃, v₃, add_assoc] using h₃
      have p₃_label : 2 * (n + 1) < l p₃ := by lia
      use ⟨⟨v₃.1 + x₃, by grind⟩, ⟨v₃.2 + y₃, by grind⟩⟩
    -- p₂ is higher, B is bounded north by p₂ and bounded west by p₁
    · let v₃ := ((x₁ + 1 : ℕ), (y₂ + 1 : ℕ))
      have ⟨(⟨x₃, hx₃⟩, ⟨y₃, hy₃⟩), h₃⟩ := ih (transpose v₃ l)
      simp only [Subtype.mk_le_mk, Finset.mem_range] at le hx₁ hx₂ hx₃ hy₁ hy₂ hy₃
      let p₃ := v₃ + (x₃, y₃)
      have p₃_ne_p₁ : l p₃ ≠ 2 * n + 1 := by
        have dist_lt := dist_lt h₁.symm.le ⟨⟨1 + x₃, by grind⟩, ⟨1 + y₃ + y₂ - y₁, by simp; lia⟩⟩ (by simp [abs_lt]; lia)
        have := exclusion dist_lt (by grind)
        simp [← h₁, v₃, p₃, add_assoc] at this ⊢
        grind
      have p₃_ne_p₂ : l p₃ ≠ 2 * (n + 1) := by
        have dist_lt := dist_lt' h₂ ⟨⟨1 + x₁ + x₃ - x₂ - 2 ^ n, by simp; lia⟩, ⟨1 + y₃, by simp; lia⟩⟩
        have := exclusion dist_lt
        simp [← h₂, v₃, p₃, add_assoc] at this ⊢
        grind
      replace h₃ : 2 * n < l p₃ := by simpa [p₃, v₃, add_assoc] using h₃
      have p₃_label : 2 * (n + 1) < l p₃ := by lia
      use ⟨⟨v₃.1 + x₃, by grind⟩, ⟨v₃.2 + y₃, by grind⟩⟩

-- We take care of 3/4 of the space in one iteration, removing the need to fiddle with the parity of being aligned with the grid
-- this does mean that we need an N twice as large
variable (limit : ℕ) (p : ℤ × ℤ)
def label : ℕ → ℤ × ℤ → ℕ
| 0, _ => 1
| limit + 1, (a, b) =>
  if Odd (a + b) then 1
  else if Odd a ∧ Odd b then 2
  else 2 + label limit (a / 2, b / 2)

lemma label_max : label limit p ≤ 2 * limit + 1 := by
  induction limit generalizing p with
  | zero => simp [label]
  | succ limit ih =>
    rw [label]
    grind

lemma label_finite : (Set.range <| label limit).Finite := by
  simp_rw [Set.finite_iff_bddAbove, bddAbove_def, Set.mem_range]
  use 2 * limit + 1
  rintro _ ⟨p, rfl⟩
  exact label_max _ _

lemma label_pos : 0 < label limit p := by
  induction limit
  · simp [label]
  · rw [label]
    lia

lemma label_cases : label (limit + 1) p = 1 ∨ label (limit + 1) p = 2 ∨ label (limit + 1) p = 2 + label limit (p.1 / 2, p.2 / 2) := by
  obtain ⟨a, b⟩ := p
  if h : Odd (a + b) then simp [h, label]
  else if h' : Odd a ∧ Odd b then grind [label]
  else simp [h, h', label]

lemma label_one_iff : label (limit + 1) p = 1 ↔ Odd (p.1 + p.2) := by
  grind [label]

lemma label_two_iff : label (limit + 1) p = 2 ↔ Odd p.1 ∧ Odd p.2 := by
  grind [label, label_pos]

lemma label_more_iff : label (limit + 1) p = 2 + label limit (p.1 / 2, p.2 / 2) ↔ Even p.1 ∧ Even p.2 := by
  grind [label, label_pos]

lemma label_max_exists_eq (h : label limit p = 2 * limit + 1) : ∃ a b : ℤ, p = (a * 2 ^ limit, b * 2 ^ limit) := by
  induction limit generalizing p with
  | zero => exact ⟨p.1, p.2, by simp⟩
  | succ limit ih =>
    have ⟨a, b, hab⟩ := ih (p.1 / 2, p.2 / 2) (by simp [label] at h; lia)
    refine ⟨a, b, by grind [label]⟩

lemma label_congr {limit : ℕ} {p₁ p₂ : ℤ × ℤ} (h : label (limit + 1) p₁ = label (limit + 1) p₂)
  : (Odd (p₁.1 + p₁.2) ∧ Odd (p₂.1 + p₂.2))
    ∨ (Odd p₁.1 ∧ Odd p₁.2 ∧ Odd p₂.1 ∧ Odd p₂.2)
    ∨ (Even p₁.1 ∧ Even p₁.2 ∧ Even p₂.1 ∧ Even p₂.2) := by
  grind [label, label_pos]

-- For the normal case, following the bound of √2 ^ i < dist p₁ p₂
lemma label_dist {p₁ p₂ : ℤ × ℤ} (h_ne : p₁ ≠ p₂) {limit : ℕ}
  (hp : label limit p₁ = label limit p₂)
  (hv : label limit p₁ ≠ 2 * limit + 1) : √2 ^ (label limit p₁) ≤ dist p₁ p₂ := by
  induction limit generalizing p₁ p₂ with
  | zero => grind [label]
  | succ limit ih =>
    rcases label_congr <| hp with ⟨h₁, h₂⟩ | ⟨h₁, h₂, h₃, h₄⟩ | ⟨h₁, h₂, h₃, h₄⟩
    -- v = 1, checkerboard has dist ≥ √2
    · rw [label_one_iff _ _ |>.mpr h₁]
      rw [pow_one, dist, sqrt_le_iff]
      refine ⟨sqrt_nonneg _, ?_⟩
      rw [sq_sqrt (by nlinarith)]
      norm_cast
      by_cases h : p₁.1 ≠ p₂.1 ∧ p₁.2 ≠ p₂.2
      · have : 1 ≤ (p₂.1 - p₁.1) ^ 2 := by
          rw [← sq_abs]
          exact one_le_pow₀ (by grind)
        have : 1 ≤ (p₂.2 - p₁.2) ^ 2 := by
          rw [← sq_abs]
          exact one_le_pow₀ (by grind)
        linarith
      · push +distrib Not at h
        rcases h with h | h
        · have : 2 ≤ |p₂.2 - p₁.2| := by grind
          nth_rw 2 [← sq_abs]
          nlinarith
        · have : 2 ≤ |p₂.1 - p₁.1| := by grind
          rw [← sq_abs]
          nlinarith
    -- v = 2, 1/4 spaced board has dist ≥ 2
    · rw [label_two_iff _ _ |>.mpr ⟨h₁, h₂⟩, dist]
      simp only [Nat.ofNat_nonneg, sq_sqrt]
      rw [le_sqrt' zero_lt_two]
      norm_cast
      simp only [Nat.reducePow, Nat.cast_ofNat]
      by_cases! h : p₁.1 ≠ p₂.1
      · have : 2 ≤ |p₂.1 - p₁.1| := by grind
        rw [← sq_abs]
        nlinarith
      · have : 2 ≤ |p₂.2 - p₁.2| := by grind
        nth_rw 2 [← sq_abs]
        nlinarith
    -- induction, points are 1/4 more sparse than the previous grid
    · rw [label_more_iff _ _ |>.mpr ⟨h₁, h₂⟩]
      have hp1 := label_more_iff limit p₁ |>.mpr ⟨h₁, h₂⟩
      have hp2 := label_more_iff limit p₂ |>.mpr ⟨h₃, h₄⟩
      specialize @ih (p₁.1 / 2, p₁.2 / 2) (p₂.1 / 2, p₂.2 / 2) (by grind) (by lia) (by lia)
      ring_nf
      rw [sq_sqrt zero_le_two]
      rw [dist] at ih
      push_cast [
        Int.cast_div_charZero <| even_iff_two_dvd.mp h₁,
        Int.cast_div_charZero <| even_iff_two_dvd.mp h₂,
        Int.cast_div_charZero <| even_iff_two_dvd.mp h₃,
        Int.cast_div_charZero <| even_iff_two_dvd.mp h₄] at ih
      simp_rw [div_sub_div_same, div_pow, ← add_div] at ih
      rw [sqrt_div (by nlinarith), sqrt_sq (by linarith)] at ih
      grind [dist]

-- For the last case, where all of the rest of the unfilled squares are marked with the same label
lemma label_dist_max {p₁ p₂ : ℤ × ℤ} (h : p₁ ≠ p₂) {limit : ℕ}
  (hp₁ : label limit p₁ = 2 * limit + 1) (hp₂ : label limit p₂ = 2 * limit + 1)
  : √2 ^ (2 * limit) ≤ dist p₁ p₂ := by
  induction limit generalizing p₁ p₂ with
  | zero => simp [dist_ne h]
  | succ limit ih =>
    obtain ⟨a1, b1, rfl⟩ := label_max_exists_eq (limit + 1) p₁ hp₁
    obtain ⟨a2, b2, rfl⟩ := label_max_exists_eq (limit + 1) p₂ hp₂
    simp_rw [pow_succ, ← mul_assoc]
    rw [dist_scale, Nat.mul_add_one, pow_add, sq_sqrt zero_le_two, mul_le_mul_iff_left₀ zero_lt_two]
    apply ih (by grind)
    · rw [label] at hp₁
      repeat (split at hp₁; lia)
      simp_rw [pow_succ, ← mul_assoc, Int.mul_ediv_cancel _ (by decide : (2 : ℤ) ≠ 0)] at hp₁
      lia
    · rw [label] at hp₂
      repeat (split at hp₂; lia)
      simp_rw [pow_succ, ← mul_assoc, Int.mul_ediv_cancel _ (by decide : (2 : ℤ) ≠ 0)] at hp₂
      lia

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
    -- this is weaker than the one given in the solution, as it makes calculating the explicit bounds for our construction easier
    have ⟨n, hn⟩ : ∃ m : ℕ, Real.log c / (2 * (Real.log √2 - Real.log c)) < m := exists_nat_gt _
    have c_bound : c ^ (2 * n + 1) < √2 ^ (2 * n) := by
      rw [Real.pow_lt_iff_lt_log c_pos (by simp), log_pow]
      push_cast
      rw [add_one_mul, ← lt_tsub_iff_left, ← mul_sub, ← mul_rotate, ← div_lt_iff₀' ?_]
      · simpa [mul_comm] using hn
      · refine (mul_pos_iff_of_pos_left ?_).mpr zero_lt_two
        rwa [sub_pos, log_lt_log_iff c_pos (c_pos.trans c_lt)]
    refine ⟨label n, label_finite _, label_pos _, fun {p₁ p₂} h_ne h_label => ?_⟩
    rcases (label_max n p₁).eq_or_lt with eq | lt
    · rw [eq]
      exact c_bound.trans_le (label_dist_max h_ne eq (h_label.symm.trans eq)) |>.le
    · calc
        c ^ label n p₁
        _ ≤ √2 ^ label n p₁ := pow_le_pow_iff_left₀ c_pos.le (sqrt_nonneg _) (label_pos _ _ |>.ne.symm) |>.mpr c_lt.le
        _ ≤ dist p₁ p₂ := label_dist h_ne h_label lt.ne
  · contrapose
    -- Any counterexample we have for c = √2 works for c > √2 as well
    wlog hc : c = √2 with rest
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
    have ⟨p, hp⟩ := square_squeeze' n ⟨l, l_fin, l_pos, l_dist⟩
    specialize hn (l p) (Set.mem_range_self _)
    simp only [DFunLike.coe] at hp
    linarith


end Usa2017P5
