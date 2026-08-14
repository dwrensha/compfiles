/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.Int.ConditionallyCompleteOrder
public import Mathlib.Data.Nat.Dist
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Ring.Basic
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics] }

/-!
# USA Mathematical Olympiad 2003, Problem 6

At the vertices of a regular hexagon are written six nonnegative integers
whose sum is 2003^2003. Bert is allowed to make moves of the following form:
he may pick a vertex and replace the number written there by the absolute
value of the difference between the numbers written at the two neighboring
vertices. Prove that Bert can make a sequence of moves, after which the
number 0 appears at all six vertices.
-/

namespace Usa2003P6

snip begin

/-- A configuration of six integers at the vertices of a hexagon. -/
abbrev Conf := ZMod 6 → ℤ

/-- One move at vertex `j`: replace the number at `j` by the absolute value
of the difference of the numbers at the two neighboring vertices. -/
def step (f : Conf) (j : ZMod 6) : Conf := Function.update f j |f (j - 1) - f (j + 1)|

/-- `Moves f g` means that configuration `g` can be reached from `f` by a
sequence of moves. -/
def Moves (f g : Conf) : Prop := ∃ l : List (ZMod 6), l.foldl step f = g

lemma Moves.refl (f : Conf) : Moves f f := ⟨[], rfl⟩

lemma Moves.trans {f g h : Conf} (h1 : Moves f g) (h2 : Moves g h) : Moves f h := by
  obtain ⟨l1, rfl⟩ := h1
  obtain ⟨l2, rfl⟩ := h2
  exact ⟨l1 ++ l2, by rw [List.foldl_append]⟩

/-- The maximum entry of a configuration. -/
noncomputable def cmax (f : Conf) : ℤ :=
  (Finset.univ.image f).max' (Finset.univ_nonempty.image f)

lemma le_cmax (f : Conf) (i : ZMod 6) : f i ≤ cmax f :=
  Finset.le_max' _ _ (Finset.mem_image_of_mem f (Finset.mem_univ i))

lemma cmax_le (f : Conf) (C : ℤ) (h : ∀ i, f i ≤ C) : cmax f ≤ C := by
  apply Finset.max'_le
  intro x hx
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
  exact h i

lemma cmax_attained (f : Conf) : ∃ i, f i = cmax f := by
  have h := Finset.max'_mem _ (Finset.univ_nonempty.image (f := f))
  obtain ⟨i, -, hi⟩ := Finset.mem_image.mp h
  exact ⟨i, hi⟩

/-! ### Parity machinery -/

lemma cast_abs2 (n : ℤ) : ((|n| : ℤ) : ZMod 2) = (n : ZMod 2) := by
  rcases abs_choice n with h | h
  · rw [h]
  · rw [h, Int.cast_neg]
    have h2 : ∀ x : ZMod 2, -x = x := by decide
    rw [h2]

lemma odd_iff_cast (n : ℤ) : Odd n ↔ (n : ZMod 2) = 1 := by
  have h1 : (1 : ZMod 2) = ((1 : ℤ) : ZMod 2) := by norm_num
  rw [h1, ZMod.intCast_eq_intCast_iff, Int.odd_iff]
  exact ⟨id, id⟩

lemma even_iff_cast (n : ℤ) : Even n ↔ (n : ZMod 2) = 0 := by
  have h1 : (0 : ZMod 2) = ((0 : ℤ) : ZMod 2) := by norm_num
  rw [h1, ZMod.intCast_eq_intCast_iff, Int.even_iff]
  exact ⟨id, id⟩

lemma odd_sum_iff (f : Conf) : Odd (∑ i, f i) ↔ (∑ i, (f i : ZMod 2)) = 1 := by
  rw [← Int.cast_sum]
  exact odd_iff_cast _

lemma one_le_of_odd {n : ℤ} (h0 : 0 ≤ n) (ho : Odd n) : 1 ≤ n := by
  rcases ho with ⟨k, rfl⟩
  omega

lemma two_le_of_even_pos {n : ℤ} (h0 : 0 < n) (he : Even n) : 2 ≤ n := by
  rcases he with ⟨k, rfl⟩
  omega

/-- The move on parity vectors: in `ZMod 2` the absolute difference becomes a sum. -/
def step2 (v : ZMod 6 → ZMod 2) (j : ZMod 6) : ZMod 6 → ZMod 2 :=
  Function.update v j (v (j - 1) + v (j + 1))

lemma par_step (f : Conf) (j : ZMod 6) :
    (fun i => ((step f j) i : ZMod 2)) = step2 (fun i => (f i : ZMod 2)) j := by
  funext i
  by_cases hij : i = j
  · subst hij
    simp only [step, step2, Function.update_self]
    rw [cast_abs2, Int.cast_sub, sub_eq_add_neg]
    have h2 : ∀ x : ZMod 2, -x = x := by decide
    rw [h2]
  · simp only [step, step2, Function.update_of_ne hij]

lemma par_foldl (f : Conf) (l : List (ZMod 6)) :
    (fun i => ((l.foldl step f) i : ZMod 2)) = l.foldl step2 (fun i => (f i : ZMod 2)) := by
  induction l generalizing f with
  | nil => rfl
  | cons a l ih =>
    simp only [List.foldl_cons]
    rw [← par_step]
    exact ih _

/-! ### Nonnegativity and the maximum under moves -/

lemma step_nonneg (f : Conf) (hnn : ∀ i, 0 ≤ f i) (j : ZMod 6) : ∀ i, 0 ≤ step f j i := by
  intro i
  by_cases hij : i = j
  · subst hij
    rw [step, Function.update_self]
    exact abs_nonneg _
  · rw [step, Function.update_of_ne hij]
    exact hnn i

lemma foldl_nonneg (f : Conf) (hnn : ∀ i, 0 ≤ f i) : ∀ l : List (ZMod 6), ∀ i, 0 ≤ (l.foldl step f) i := by
  intro l
  induction l generalizing f hnn with
  | nil => exact hnn
  | cons a l ih =>
    intro i
    simp only [List.foldl_cons]
    exact ih (step f a) (step_nonneg f hnn a) i

lemma abs_sub_le_of {x y B : ℤ} (hx0 : 0 ≤ x) (hy0 : 0 ≤ y) (hxB : x ≤ B) (hyB : y ≤ B) :
    |x - y| ≤ B :=
  abs_le.mpr ⟨by omega, by omega⟩

lemma cmax_step_le (f : Conf) (hnn : ∀ i, 0 ≤ f i) (j : ZMod 6) : cmax (step f j) ≤ cmax f := by
  apply cmax_le
  intro i
  by_cases hij : i = j
  · rw [step, hij, Function.update_self]
    exact le_trans (abs_sub_le_of (hnn (j - 1)) (hnn (j + 1))
      (le_max_left _ _) (le_max_right _ _)) (max_le (le_cmax f (j - 1)) (le_cmax f (j + 1)))
  · rw [step, Function.update_of_ne hij]
    exact le_cmax f i

lemma cmax_foldl_le (f : Conf) (hnn : ∀ i, 0 ≤ f i) : ∀ l : List (ZMod 6), cmax (l.foldl step f) ≤ cmax f := by
  intro l
  induction l generalizing f hnn with
  | nil => exact le_refl _
  | cons a l ih =>
    simp only [List.foldl_cons]
    exact le_trans (ih (step f a) (step_nonneg f hnn a)) (cmax_step_le f hnn a)

/-! ### Phase 1: from odd sum to a single odd entry -/

/-- The candidate move sequences used to reach a configuration with exactly
one odd entry. Which one applies depends on the parity pattern of the
starting configuration. -/
def cands : List (List (ZMod 6)) :=
  [[1, 5, 0, 5, 3], [3, 1, 2, 1, 5], [5, 3, 4, 3, 1], [1, 5, 3, 4, 2],
   [2, 0, 1, 0, 4], [4, 2, 3, 2, 0], [0, 4, 5, 4, 2], [2, 0, 4, 5, 3]]

/-- Machine-checked parity verification: from every parity vector with odd
sum, one of the candidate sequences leads to a parity vector with exactly
one odd entry. -/
lemma phase1_decide : ∀ v : ZMod 6 → ZMod 2, (∑ i, v i) = 1 →
    ∃ l ∈ cands, ∃ p, ∀ i, (l.foldl step2 v) i = (if i = p then 1 else 0) := by
  decide

lemma phase1 (f : Conf) (hnn : ∀ i, 0 ≤ f i) (hodd : Odd (∑ i, f i)) :
    ∃ l : List (ZMod 6), ∃ g : Conf, l.foldl step f = g ∧ (∀ i, 0 ≤ g i) ∧
      cmax g ≤ cmax f ∧ ∃ p : ZMod 6, (g p : ZMod 2) = 1 ∧ ∀ i, i ≠ p → (g i : ZMod 2) = 0 := by
  rw [odd_sum_iff] at hodd
  obtain ⟨l, -, p, hp⟩ := phase1_decide _ hodd
  refine ⟨l, l.foldl step f, rfl, foldl_nonneg f hnn l, cmax_foldl_le f hnn l, p, ?_, ?_⟩
  · have hf2 : ((l.foldl step f) p : ZMod 2) = (l.foldl step2 (fun i => (f i : ZMod 2))) p :=
      congr_fun (par_foldl f l) p
    rw [hf2]
    have hpp := hp p
    rw [ite_eq_left rfl] at hpp
    exact hpp
  · intro i hi
    have hf2 : ((l.foldl step f) i : ZMod 2) = (l.foldl step2 (fun i => (f i : ZMod 2))) i :=
      congr_fun (par_foldl f l) i
    rw [hf2]
    have hpi := hp i
    rw [ite_eq_right hi] at hpi
    exact hpi

/-! ### Rotation symmetry -/

lemma step_comp_add (f : Conf) (c j : ZMod 6) :
    step (f ∘ (· + c)) j = (step f (j + c)) ∘ (· + c) := by
  funext i
  simp only [step, Function.comp_apply]
  by_cases hij : i = j
  · subst hij
    rw [Function.update_self, Function.update_self]
    congr 2
    · congr 1
      ring
    · congr 1
      ring
  · have hij2 : i + c ≠ j + c := fun h => hij (add_right_cancel h)
    rw [Function.update_of_ne hij, Function.update_of_ne hij2]
    rfl

lemma foldl_comp_add (f : Conf) (c : ZMod 6) (l : List (ZMod 6)) :
    l.foldl step (f ∘ (· + c)) = ((l.map (· + c)).foldl step f) ∘ (· + c) := by
  induction l generalizing f with
  | nil => rfl
  | cons a l ih =>
    simp only [List.foldl_cons, List.map_cons]
    rw [step_comp_add]
    exact ih _

lemma moves_comp_add (f g : Conf) (c : ZMod 6) (h : Moves f g) :
    Moves (f ∘ (· + c)) (g ∘ (· + c)) := by
  obtain ⟨l, hl⟩ := h
  refine ⟨l.map (· - c), ?_⟩
  rw [foldl_comp_add, List.map_map]
  have hid : ((· + c) ∘ (· - c) : ZMod 6 → ZMod 6) = id := by
    funext x
    simp only [Function.comp_apply, id_eq]
    ring
  rw [hid, List.map_id, hl]

/-! ### Concrete move computations -/

lemma step0 (f : Conf) : step f 0 = Function.update f 0 (abs (f 5 - f 1)) := by
  simp only [step, show (0 : ZMod 6) - 1 = 5 by decide, show (0 : ZMod 6) + 1 = 1 by decide]
lemma step1 (f : Conf) : step f 1 = Function.update f 1 (abs (f 0 - f 2)) := by
  simp only [step, show (1 : ZMod 6) - 1 = 0 by decide, show (1 : ZMod 6) + 1 = 2 by decide]
lemma step2' (f : Conf) : step f 2 = Function.update f 2 (abs (f 1 - f 3)) := by
  simp only [step, show (2 : ZMod 6) - 1 = 1 by decide, show (2 : ZMod 6) + 1 = 3 by decide]
lemma step3 (f : Conf) : step f 3 = Function.update f 3 (abs (f 2 - f 4)) := by
  simp only [step, show (3 : ZMod 6) - 1 = 2 by decide, show (3 : ZMod 6) + 1 = 4 by decide]
lemma step4 (f : Conf) : step f 4 = Function.update f 4 (abs (f 3 - f 5)) := by
  simp only [step, show (4 : ZMod 6) - 1 = 3 by decide, show (4 : ZMod 6) + 1 = 5 by decide]
lemma step5 (f : Conf) : step f 5 = Function.update f 5 (abs (f 4 - f 0)) := by
  simp only [step, show (5 : ZMod 6) - 1 = 4 by decide, show (5 : ZMod 6) + 1 = 0 by decide]

/-- Evaluate a concrete sequence of moves at a concrete vertex. -/
macro "eval_step" : tactic =>
  `(tactic| (simp only [List.foldl_cons, List.foldl_nil, step0, step1, step2', step3, step4, step5];
             repeat (first | rw [Function.update_self] | rw [Function.update_of_ne (by decide)])))

lemma abs_sub_le_mk1 {x y M : ℤ} (hx1 : 1 ≤ x) (hxM : x ≤ M - 1) (hy0 : 0 ≤ y) (hyM : y ≤ M) :
    |x - y| ≤ M - 1 :=
  abs_le.mpr ⟨by omega, by omega⟩

lemma abs_sub_le_mk2 {x y M : ℤ} (hx0 : 0 ≤ x) (hxM : x ≤ M - 1) (hy0 : 0 ≤ y) (hyM : y ≤ M - 1) :
    |x - y| ≤ M - 1 :=
  abs_le.mpr ⟨by omega, by omega⟩

/-! ### Phase 2: reducing the maximum from a single odd entry -/

lemma phase2 (g : Conf) (hnn : ∀ i, 0 ≤ g i) (h0 : (g 0 : ZMod 2) = 1)
    (hk : ∀ i, i ≠ 0 → (g i : ZMod 2) = 0) :
    ∃ h : Conf, Moves g h ∧ (h = 0 ∨ (Odd (∑ i, h i) ∧ cmax h < cmax g)) := by
  have g0ge : 1 ≤ g 0 := one_le_of_odd (hnn 0) ((odd_iff_cast _).mpr h0)
  have hM1 : 1 ≤ cmax g := le_trans g0ge (le_cmax g 0)
  obtain ⟨q, hq⟩ := cmax_attained g
  have hparinit : (fun i => (g i : ZMod 2)) = (fun i => if i = 0 then 1 else 0) := by
    funext i
    by_cases hi : i = 0
    · subst hi
      rw [ite_eq_left rfl]
      exact h0
    · rw [ite_eq_right hi]
      exact hk i hi
  by_cases hq0 : q = 0
  · -- The maximum is odd, hence attained exactly at vertex 0.
    subst hq0
    have Mpar : (cmax g : ZMod 2) = 1 := by
      rw [← hq]
      exact h0
    have glt : ∀ i, i ≠ 0 → g i ≤ cmax g - 1 := by
      intro i hi
      have h1 := le_cmax g i
      have h2 : g i ≠ cmax g := by
        intro heq
        have t1 := hk i hi
        rw [heq, Mpar] at t1
        exact (by decide : (1 : ZMod 2) ≠ 0) t1
      omega
    by_cases h2 : g 2 = 0
    · by_cases h4 : g 4 = 0
      · -- Vertices 2 and 4 both zero: six moves finish the job.
        have A1 : |g 0 - g 2| = cmax g := by
          rw [h2, sub_zero, ← hq]
          exact abs_of_nonneg (hnn 0)
        have A2 : |g 4 - g 0| = cmax g := by
          rw [h4, zero_sub, ← hq, abs_neg]
          exact abs_of_nonneg (by have := le_cmax g 0; omega)
        have e0 : ([1, 5, 3, 0, 5, 1].foldl step g) 0 =
            abs (abs (g 4 - g 0) - abs (g 0 - g 2)) := by eval_step
        have e1 : ([1, 5, 3, 0, 5, 1].foldl step g) 1 =
            abs (abs (abs (g 4 - g 0) - abs (g 0 - g 2)) - g 2) := by eval_step
        have e2 : ([1, 5, 3, 0, 5, 1].foldl step g) 2 = g 2 := by eval_step
        have e3 : ([1, 5, 3, 0, 5, 1].foldl step g) 3 = abs (g 2 - g 4) := by eval_step
        have e4 : ([1, 5, 3, 0, 5, 1].foldl step g) 4 = g 4 := by eval_step
        have e5 : ([1, 5, 3, 0, 5, 1].foldl step g) 5 =
            abs (g 4 - abs (abs (g 4 - g 0) - abs (g 0 - g 2))) := by eval_step
        have z0 : ([1, 5, 3, 0, 5, 1].foldl step g) 0 = 0 := by
          rw [e0, A1, A2, sub_self, abs_zero]
        have z1 : ([1, 5, 3, 0, 5, 1].foldl step g) 1 = 0 := by
          rw [e1, A1, A2, h2, sub_self, abs_zero, sub_zero, abs_zero]
        have z2 : ([1, 5, 3, 0, 5, 1].foldl step g) 2 = 0 := by
          rw [e2, h2]
        have z3 : ([1, 5, 3, 0, 5, 1].foldl step g) 3 = 0 := by
          rw [e3, h2, h4, sub_self, abs_zero]
        have z4 : ([1, 5, 3, 0, 5, 1].foldl step g) 4 = 0 := by
          rw [e4, h4]
        have z5 : ([1, 5, 3, 0, 5, 1].foldl step g) 5 = 0 := by
          rw [e5, A1, A2, h4, sub_self, abs_zero, sub_zero, abs_zero]
        refine ⟨[1, 5, 3, 0, 5, 1].foldl step g, ⟨[1, 5, 3, 0, 5, 1], rfl⟩, Or.inl ?_⟩
        funext i
        fin_cases i <;> simp only <;> assumption
      · -- Vertex 2 zero, vertex 4 positive.
        have g4ge : 2 ≤ g 4 :=
          two_le_of_even_pos (lt_of_le_of_ne' (hnn 4) h4) ((even_iff_cast _).mpr (hk 4 (by decide)))
        have A1 : |g 0 - g 2| = cmax g := by
          rw [h2, sub_zero, ← hq]
          exact abs_of_nonneg (hnn 0)
        have A2 : |g 4 - g 0| = cmax g - g 4 := by
          rw [abs_of_nonpos (by have := le_cmax g 4; omega), ← hq]
          ring
        have e0 : ([5, 1, 0, 1].foldl step g) 0 =
            abs (abs (g 4 - g 0) - abs (g 0 - g 2)) := by eval_step
        have e1 : ([5, 1, 0, 1].foldl step g) 1 =
            abs (abs (abs (g 4 - g 0) - abs (g 0 - g 2)) - g 2) := by eval_step
        have e2 : ([5, 1, 0, 1].foldl step g) 2 = g 2 := by eval_step
        have e3 : ([5, 1, 0, 1].foldl step g) 3 = g 3 := by eval_step
        have e4 : ([5, 1, 0, 1].foldl step g) 4 = g 4 := by eval_step
        have e5 : ([5, 1, 0, 1].foldl step g) 5 = abs (g 4 - g 0) := by eval_step
        have b0 : abs (abs (g 4 - g 0) - abs (g 0 - g 2)) ≤ cmax g - 1 := by
          rw [A1, A2, show cmax g - g 4 - cmax g = -g 4 by ring, abs_neg, abs_of_nonneg (hnn 4)]
          exact glt 4 (by decide)
        have b1 : abs (abs (abs (g 4 - g 0) - abs (g 0 - g 2)) - g 2) ≤ cmax g - 1 := by
          rw [A1, A2, h2, sub_zero, show cmax g - g 4 - cmax g = -g 4 by ring, abs_neg,
            abs_of_nonneg (hnn 4), abs_of_nonneg (hnn 4)]
          exact glt 4 (by decide)
        have b2 : g 2 ≤ cmax g - 1 := by omega
        have b3 : g 3 ≤ cmax g - 1 := glt 3 (by decide)
        have b4 : g 4 ≤ cmax g - 1 := glt 4 (by decide)
        have b5 : abs (g 4 - g 0) ≤ cmax g - 1 := by
          rw [A2]
          omega
        have hcm : cmax ([5, 1, 0, 1].foldl step g) < cmax g := by
          have hle : cmax ([5, 1, 0, 1].foldl step g) ≤ cmax g - 1 := by
            apply cmax_le
            intro i
            fin_cases i
            · exact b0
            · exact b1
            · exact b2
            · exact b3
            · exact b4
            · exact b5
          exact lt_of_le_of_lt hle (by omega)
        have pc : ∀ i, (([5, 1, 0, 1].foldl step g) i : ZMod 2) = (if i = 5 then 1 else 0) := by
          intro i
          have hf2 : (([5, 1, 0, 1].foldl step g) i : ZMod 2) =
              ([5, 1, 0, 1].foldl step2 (fun i => (g i : ZMod 2))) i :=
            congr_fun (par_foldl g [5, 1, 0, 1]) i
          rw [hf2, hparinit]
          fin_cases i <;> decide
        have osum : Odd (∑ i, ([5, 1, 0, 1].foldl step g) i) := by
          rw [odd_sum_iff]
          simp only [pc]
          decide
        exact ⟨[5, 1, 0, 1].foldl step g, ⟨[5, 1, 0, 1], rfl⟩, Or.inr ⟨osum, hcm⟩⟩
    · -- Vertex 2 positive.
      have g2ge : 2 ≤ g 2 :=
        two_le_of_even_pos (lt_of_le_of_ne' (hnn 2) h2) ((even_iff_cast _).mpr (hk 2 (by decide)))
      have A1 : |g 0 - g 2| = cmax g - g 2 := by
        rw [← hq]
        exact abs_of_nonneg (by have := le_cmax g 2; omega)
      have A2 : |g 4 - g 0| = cmax g - g 4 := by
        rw [abs_of_nonpos (by have := le_cmax g 4; omega), ← hq]
        ring
      have e0 : ([1, 5, 0, 5].foldl step g) 0 =
          abs (abs (g 4 - g 0) - abs (g 0 - g 2)) := by eval_step
      have e1 : ([1, 5, 0, 5].foldl step g) 1 = abs (g 0 - g 2) := by eval_step
      have e2 : ([1, 5, 0, 5].foldl step g) 2 = g 2 := by eval_step
      have e3 : ([1, 5, 0, 5].foldl step g) 3 = g 3 := by eval_step
      have e4 : ([1, 5, 0, 5].foldl step g) 4 = g 4 := by eval_step
      have e5 : ([1, 5, 0, 5].foldl step g) 5 =
          abs (g 4 - abs (abs (g 4 - g 0) - abs (g 0 - g 2))) := by eval_step
      have b0 : abs (abs (g 4 - g 0) - abs (g 0 - g 2)) ≤ cmax g - 1 := by
        rw [A1, A2, show cmax g - g 4 - (cmax g - g 2) = g 2 - g 4 by ring]
        exact abs_sub_le_of (hnn 2) (hnn 4) (glt 2 (by decide)) (glt 4 (by decide))
      have b1 : abs (g 0 - g 2) ≤ cmax g - 1 := by
        rw [A1]
        omega
      have b2 : g 2 ≤ cmax g - 1 := glt 2 (by decide)
      have b3 : g 3 ≤ cmax g - 1 := glt 3 (by decide)
      have b4 : g 4 ≤ cmax g - 1 := glt 4 (by decide)
      have b5 : abs (g 4 - abs (abs (g 4 - g 0) - abs (g 0 - g 2))) ≤ cmax g - 1 := by
        rw [A1, A2, show cmax g - g 4 - (cmax g - g 2) = g 2 - g 4 by ring]
        have inner : abs (g 2 - g 4) ≤ cmax g - 1 :=
          abs_sub_le_of (hnn 2) (hnn 4) (glt 2 (by decide)) (glt 4 (by decide))
        exact abs_sub_le_of (hnn 4) (abs_nonneg _) (glt 4 (by decide)) inner
      have hcm : cmax ([1, 5, 0, 5].foldl step g) < cmax g := by
        have hle : cmax ([1, 5, 0, 5].foldl step g) ≤ cmax g - 1 := by
          apply cmax_le
          intro i
          fin_cases i
          · exact b0
          · exact b1
          · exact b2
          · exact b3
          · exact b4
          · exact b5
        exact lt_of_le_of_lt hle (by omega)
      have pc : ∀ i, (([1, 5, 0, 5].foldl step g) i : ZMod 2) = (if i = 1 then 1 else 0) := by
        intro i
        have hf2 : (([1, 5, 0, 5].foldl step g) i : ZMod 2) =
            ([1, 5, 0, 5].foldl step2 (fun i => (g i : ZMod 2))) i :=
          congr_fun (par_foldl g [1, 5, 0, 5]) i
        rw [hf2, hparinit]
        fin_cases i <;> decide
      have osum : Odd (∑ i, ([1, 5, 0, 5].foldl step g) i) := by
        rw [odd_sum_iff]
        simp only [pc]
        decide
      exact ⟨[1, 5, 0, 5].foldl step g, ⟨[1, 5, 0, 5], rfl⟩, Or.inr ⟨osum, hcm⟩⟩
  · -- The maximum is even, hence larger than the unique odd entry at vertex 0.
    have Mpar : (cmax g : ZMod 2) = 0 := by
      have t1 := hk q hq0
      rw [hq] at t1
      exact t1
    have g0lt : g 0 < cmax g := by
      have h1 := le_cmax g 0
      have h2 : g 0 ≠ cmax g := by
        intro heq
        rw [heq, Mpar] at h0
        exact (by decide : (0 : ZMod 2) ≠ 1) h0
      omega
    have e0 : ([1, 2, 3, 4, 5].foldl step g) 0 = g 0 := by eval_step
    have e1 : ([1, 2, 3, 4, 5].foldl step g) 1 = abs (g 0 - g 2) := by eval_step
    have e2 : ([1, 2, 3, 4, 5].foldl step g) 2 = abs (abs (g 0 - g 2) - g 3) := by eval_step
    have e3 : ([1, 2, 3, 4, 5].foldl step g) 3 =
        abs (abs (abs (g 0 - g 2) - g 3) - g 4) := by eval_step
    have e4 : ([1, 2, 3, 4, 5].foldl step g) 4 =
        abs (abs (abs (abs (g 0 - g 2) - g 3) - g 4) - g 5) := by eval_step
    have e5 : ([1, 2, 3, 4, 5].foldl step g) 5 =
        abs (abs (abs (abs (abs (g 0 - g 2) - g 3) - g 4) - g 5) - g 0) := by eval_step
    have pc : ∀ i, (([1, 2, 3, 4, 5].foldl step g) i : ZMod 2) = (if i = 5 then 0 else 1) := by
      intro i
      have hf2 : (([1, 2, 3, 4, 5].foldl step g) i : ZMod 2) =
          ([1, 2, 3, 4, 5].foldl step2 (fun i => (g i : ZMod 2))) i :=
        congr_fun (par_foldl g [1, 2, 3, 4, 5]) i
      rw [hf2, hparinit]
      fin_cases i <;> decide
    have b0 : g 0 ≤ cmax g - 1 := by omega
    have u1odd : Odd |g 0 - g 2| := by
      rw [odd_iff_cast, ← e1]
      have t := pc 1
      rwa [ite_eq_right (by decide : ¬((1 : ZMod 6) = 5))] at t
    have u1ge : 1 ≤ |g 0 - g 2| := one_le_of_odd (abs_nonneg _) u1odd
    have b1 : abs (g 0 - g 2) ≤ cmax g - 1 :=
      abs_sub_le_mk1 g0ge b0 (hnn 2) (le_cmax g 2)
    have u2odd : Odd (abs (abs (g 0 - g 2) - g 3)) := by
      rw [odd_iff_cast, ← e2]
      have t := pc 2
      rwa [ite_eq_right (by decide : ¬((2 : ZMod 6) = 5))] at t
    have u2ge : 1 ≤ abs (abs (g 0 - g 2) - g 3) := one_le_of_odd (abs_nonneg _) u2odd
    have b2 : abs (abs (g 0 - g 2) - g 3) ≤ cmax g - 1 :=
      abs_sub_le_mk1 u1ge b1 (hnn 3) (le_cmax g 3)
    have u3odd : Odd (abs (abs (abs (g 0 - g 2) - g 3) - g 4)) := by
      rw [odd_iff_cast, ← e3]
      have t := pc 3
      rwa [ite_eq_right (by decide : ¬((3 : ZMod 6) = 5))] at t
    have u3ge : 1 ≤ abs (abs (abs (g 0 - g 2) - g 3) - g 4) := one_le_of_odd (abs_nonneg _) u3odd
    have b3 : abs (abs (abs (g 0 - g 2) - g 3) - g 4) ≤ cmax g - 1 :=
      abs_sub_le_mk1 u2ge b2 (hnn 4) (le_cmax g 4)
    have b4 : abs (abs (abs (abs (g 0 - g 2) - g 3) - g 4) - g 5) ≤ cmax g - 1 :=
      abs_sub_le_mk1 u3ge b3 (hnn 5) (le_cmax g 5)
    have b5 : abs (abs (abs (abs (abs (g 0 - g 2) - g 3) - g 4) - g 5) - g 0) ≤ cmax g - 1 :=
      abs_sub_le_mk2 (abs_nonneg _) b4 (hnn 0) b0
    have hcm : cmax ([1, 2, 3, 4, 5].foldl step g) < cmax g := by
      have hle : cmax ([1, 2, 3, 4, 5].foldl step g) ≤ cmax g - 1 := by
        apply cmax_le
        intro i
        fin_cases i
        · exact b0
        · exact b1
        · exact b2
        · exact b3
        · exact b4
        · exact b5
      exact lt_of_le_of_lt hle (by omega)
    have osum : Odd (∑ i, ([1, 2, 3, 4, 5].foldl step g) i) := by
      rw [odd_sum_iff]
      simp only [pc]
      decide
    exact ⟨[1, 2, 3, 4, 5].foldl step g, ⟨[1, 2, 3, 4, 5], rfl⟩, Or.inr ⟨osum, hcm⟩⟩

/-! ### The main induction -/

lemma winnable_aux (f : Conf) (hnn : ∀ i, 0 ≤ f i) (hodd : Odd (∑ i, f i)) : Moves f 0 := by
  suffices H : ∀ m : ℕ, ∀ f : Conf, (∀ i, 0 ≤ f i) → Odd (∑ i, f i) →
      (cmax f).toNat = m → Moves f 0 from H _ f hnn hodd rfl
  intro m
  induction m using Nat.strongRecOn with
  | ind m ihm =>
    intro f hnn hodd hm
    obtain ⟨l1, g, hfl, gnn, gcmax, p, gp1, gpk⟩ := phase1 f hnn hodd
    -- Rotate the configuration so that the unique odd entry sits at vertex 0.
    set g' := g ∘ (· + p) with hg'
    have g'nn : ∀ i, 0 ≤ g' i := fun i => gnn (i + p)
    have g'0 : (g' 0 : ZMod 2) = 1 := by
      show (g (0 + p) : ZMod 2) = 1
      rw [zero_add]
      exact gp1
    have g'k : ∀ i, i ≠ 0 → (g' i : ZMod 2) = 0 := by
      intro i hi
      show (g (i + p) : ZMod 2) = 0
      apply gpk
      intro hip
      apply hi
      have h2 : i + p = 0 + p := by rw [hip, zero_add]
      exact add_right_cancel h2
    have g'cmax : cmax g' = cmax g := by
      apply le_antisymm
      · apply cmax_le
        intro i
        exact le_cmax g (i + p)
      · apply cmax_le
        intro i
        have h2 : g' (i + -p) = g i := by
          show g (i + -p + p) = g i
          congr 1
          ring
        rw [← h2]
        exact le_cmax g' (i + -p)
    obtain ⟨h, ⟨l2, hl2⟩, hcase⟩ := phase2 g' g'nn g'0 g'k
    have back : Moves g' 0 → Moves g 0 := by
      intro hw
      have ht := moves_comp_add g' 0 (-p) hw
      have e1 : g' ∘ (· + -p) = g := by
        funext i
        show g (i + -p + p) = g i
        congr 1
        ring
      have e2 : (0 : Conf) ∘ (· + -p) = 0 := rfl
      rw [e1, e2] at ht
      exact ht
    rcases hcase with h0' | ⟨hodd', hlt⟩
    · subst h0'
      exact Moves.trans ⟨l1, hfl⟩ (back ⟨l2, hl2⟩)
    · have hnn' : ∀ i, 0 ≤ h i := by
        rw [← hl2]
        exact foldl_nonneg g' g'nn l2
      have h1c : 1 ≤ cmax g := by
        have gpge : 1 ≤ g p := one_le_of_odd (gnn p) ((odd_iff_cast _).mpr gp1)
        exact le_trans gpge (le_cmax g p)
      have hlt' : (cmax h).toNat < m := by
        rw [← hm]
        have h1 : cmax h < cmax f := lt_of_lt_of_le (by rwa [g'cmax] at hlt) gcmax
        have h2 : 0 < cmax f := lt_of_lt_of_le (by omega : (0 : ℤ) < 1) (le_trans h1c gcmax)
        omega
      exact Moves.trans ⟨l1, hfl⟩
        (back (Moves.trans ⟨l2, hl2⟩ (ihm (cmax h).toNat hlt' h hnn' hodd' rfl)))

/-! ### From natural to integer configurations -/

/-- One move at vertex `j`, phrased on natural numbers. -/
def stepN (f : ZMod 6 → ℕ) (j : ZMod 6) : ZMod 6 → ℕ :=
  Function.update f j (Nat.dist (f (j - 1)) (f (j + 1)))

lemma dist_cast (x y : ℕ) : ((Nat.dist x y : ℤ)) = |(x : ℤ) - (y : ℤ)| := by
  unfold Nat.dist
  rcases le_total x y with h | h
  · rw [Nat.sub_eq_zero_of_le h, zero_add, Nat.cast_sub h,
      abs_of_nonpos (by omega : (x : ℤ) - (y : ℤ) ≤ 0)]
    ring
  · rw [Nat.sub_eq_zero_of_le h, add_zero, Nat.cast_sub h,
      abs_of_nonneg (by omega : (0 : ℤ) ≤ (x : ℤ) - (y : ℤ))]

lemma stepN_cast (f : ZMod 6 → ℕ) (j : ZMod 6) :
    (fun i => ((stepN f j) i : ℤ)) = step (fun i => ((f i : ℤ))) j := by
  funext i
  by_cases hij : i = j
  · subst hij
    rw [stepN, Function.update_self, step, Function.update_self]
    exact dist_cast _ _
  · rw [stepN, Function.update_of_ne hij, step, Function.update_of_ne hij]

lemma foldl_bridge (f : ZMod 6 → ℕ) (l : List (ZMod 6)) :
    (fun i => ((l.foldl stepN f) i : ℤ)) = l.foldl step (fun i => ((f i : ℤ))) := by
  induction l generalizing f with
  | nil => rfl
  | cons a l ih =>
    simp only [List.foldl_cons]
    rw [← stepN_cast]
    exact ih _

snip end

problem usa2003_p6 (f : ZMod 6 → ℕ) (hsum : ∑ i, f i = 2003 ^ 2003) :
    ∃ l : List (ZMod 6),
      l.foldl (fun g j => Function.update g j (Nat.dist (g (j - 1)) (g (j + 1)))) f = 0 := by
  have hnn : ∀ i, 0 ≤ (fun i => ((f i : ℤ))) i := fun i => Int.natCast_nonneg _
  have hodd : Odd (∑ i, ((f i : ℤ))) := by
    rw [← Nat.cast_sum, hsum, Nat.cast_pow]
    exact Odd.pow ⟨1001, rfl⟩
  obtain ⟨l, hl⟩ := winnable_aux (fun i => ((f i : ℤ))) hnn hodd
  refine ⟨l, ?_⟩
  have hb := foldl_bridge f l
  rw [hl] at hb
  show l.foldl stepN f = 0
  funext i
  have hbi := congr_fun hb i
  simp only [Pi.zero_apply] at hbi
  exact_mod_cast hbi

end Usa2003P6
