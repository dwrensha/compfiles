/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Data.Finset.Card
import Mathlib.Order.Bounds.Basic
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# USA Mathematical Olympiad 2001, Problem 1

Each of eight boxes contains six balls.
Each ball has been colored with one of n colors, such that no two balls
in the same box are the same color, and no two colors occur together in
more than one box. Determine, with justification, the smallest integer n
for which this is possible.
-/

namespace Usa2001P1

def possible_num_colors : Set ℕ :=
{ n : ℕ | ∃ f : Fin 8 → Finset (Fin n),
    (∀ i, (f i).card = 6) ∧
    (∀ x y : Fin n, ∀ i j : Fin 8,
      i ≠ j → x ∈ f i → y ∈ f i → x ≠ y →
        (¬ (x ∈ f j ∧ y ∈ f j))) }

determine min_colors : ℕ := 23

lemma l {α} (s : Finset α) (sz : s.card = 6) (gen : α -> ℕ) (gt : ∀ i ∈ s, gen i ≥ 1) (sum : (∑ i ∈ s, gen i) ≤ 13) : (36:ℝ)/(13:ℝ) ≤ (∑ i ∈ s, 1 / (gen i:ℝ)) := by
  let f := λ (i : α) ↦ Real.sqrt (gen i : ℝ)
  let g := λ (i : α) ↦ (1 : ℝ) / Real.sqrt (gen i : ℝ)
  have h := Finset.sum_mul_sq_le_sq_mul_sq s f g
  unfold f g at h
  have : (∑ x ∈ s, √(gen x : ℝ) * (1 / √(gen x : ℝ))) = ∑ x ∈ s, 1 := by
    apply Finset.sum_congr rfl; intro x hx; have := gt x hx; field_simp
  rw [this] at h; simp [sz] at h;
  have : (∑ x ∈ s, (gen x:ℝ)⁻¹) = (∑ x ∈ s, 1 / (gen x : ℝ)) := by
    apply Finset.sum_congr rfl; intro x hx; have := gt x hx; field_simp
  rw [this] at h;
  set aa := (∑ x ∈ s, (gen x : ℝ)) with haa
  set bb := (∑ x ∈ s, (1 / (gen x : ℝ))) with hbb
  rify at sum; rw [←haa] at sum; norm_num at h; 
  have : aa ≥ 0 := by rw [haa]; apply Finset.sum_nonneg; intro i hi; simp
  have : bb ≥ 0 := by rw [hbb]; apply Finset.sum_nonneg; intro i hi; simp
  field_simp; trans aa*bb;
  · exact h
  · nlinarith

lemma ll {m n : ℕ} (f : Fin m → Finset (Fin n)) (p : Fin n → Bool) (i : Fin m) : (∑ x ∈ f i, if p x then 1 else 0) > 1 → ∃ a b, a ∈ f i ∧ b ∈ f i ∧ a ≠ b ∧ p a ∧ p b := by
  intro h
  rw [<-Finset.sum_filter] at h
  simp at h
  rw [Finset.one_lt_card] at h
  obtain ⟨a, ⟨ha, ⟨b, ⟨hb, hab⟩⟩⟩⟩ := h
  rw [Finset.mem_filter] at ha
  rw [Finset.mem_filter] at hb
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  use a, b

set_option maxHeartbeats 1234567 in
problem usa2001_p1 : IsLeast possible_num_colors min_colors := by
  -- Informal solution from
  -- https://artofproblemsolving.com/wiki/index.php/2001_USAMO_Problems/Problem_1
  constructor
  · rw [possible_num_colors]
    let f : Fin 8 → Finset (Fin 23)
        | 0 => {1, 2, 3, 4, 5, 6}
        | 1 => {1, 7, 8, 9, 10, 11}
        | 2 => {1, 12, 13, 14, 15, 16}
        | 3 => {2, 7, 12, 17, 18, 19}
        | 4 => {3, 8, 13, 17, 20, 21}
        | 5 => {4, 9, 14, 17, 22, 23}
        | 6 => {5, 10, 15, 18, 20, 22}
        | 7 => {6, 11, 16, 19, 21, 23}
    use f
    constructor
    · intro i
      fin_cases i <;> simp (config := {decide := true}) [f]
    · intro x y i j hij hx hy hxy
      unfold min_colors at x y
      fin_cases i <;> fin_cases j <;> dsimp [f] at hx <;> dsimp [f] at hy <;> dsimp at hij <;> dsimp [f]
      all_goals clear f ; try contradiction
      all_goals fin_cases hx <;> fin_cases hy
      all_goals (first | decide | contradiction)


  · dsimp only [lowerBounds, Set.mem_setOf_eq]
    by_contra
    push_neg at this
    obtain ⟨n, ha_mem, ha_lt⟩ := this
    suffices n ≥ min_colors by omega
    clear ha_lt
    suffices n > 22 by { unfold min_colors; omega }
    dsimp [possible_num_colors] at ha_mem
    obtain ⟨f, ⟨h1, h2⟩⟩ := ha_mem
    let count color i := if decide (color ∈ f i) = true then 1 else 0
    let count_k : Fin n → ℕ := λ color ↦ ∑ i : Fin 8, count color i
    suffices (n: ℝ) > 22 by
    { revert this; simp }
    have nsum : n = ∑ k : Fin n, 1 := by simp
    rw [nsum]
    apply lt_of_lt_of_le ((by linarith) : (22 < 8 * ((36:ℝ) / (13:ℝ))))
    trans ∑ (k : Fin n), ∑ i : Fin 8, ((count k i):ℝ) / ((count_k k):ℝ)
    pick_goal 2;
    · rify; gcongr with k i; rw [<-Finset.sum_div]; unfold count_k; rify;
      set x := (∑ i:Fin 8, (count k i):ℝ) with hx; by_cases h:x=0;
      · rw [h]; simp;
      · rw [div_self]; exact h
    rw [Finset.sum_comm]
    have : 8 * ((36:ℝ) / (13:ℝ)) = ∑ i:Fin 8, ((36:ℝ) / (13:ℝ)) := by simp
    rw [this]
    gcongr with i a
    have : ∑ (x : Fin n), ((count x i):ℝ) / ((count_k x):ℝ) = ∑ (k ∈ f i), ((count k i):ℝ) / ((count_k k):ℝ) := by
      have : f i ⊆ (Finset.univ : (Finset (Fin n))) := by simp
      have : ∑ (x : Fin n), ((count x i):ℝ) / ((count_k x):ℝ) = ∑ (x ∈ f i), ((count x i):ℝ) / ((count_k x):ℝ) := by
        symm; apply Finset.sum_subset this; intro x hx hne; unfold count; simp; left; exact hne
      rw [this]
    rw [this]
    have : ∑ (k ∈ f i), ((count k i):ℝ) / ((count_k k):ℝ) = ∑ (k ∈ f i), 1 / ((count_k k):ℝ) := by
      apply Finset.sum_congr; rfl; intro x hx; congr; unfold count; simp [hx]
    rw [this]
    apply l; exact h1 i; intro ii hii; unfold count_k; unfold count; simp; use i; simp; exact hii
    unfold count_k
    rw [Finset.sum_comm]
    -- have := Finset.sum_erase_add
    let xx := Fin.fintype 8
    have : (∑ y, ∑ x ∈ f i, count x y) = ∑ y ∈ ((Fin.fintype 8).elems), (λ y ↦ ∑ x ∈ f i, count x y) y := by
      simp; rfl
    rw [this]
    have : ∀ (i : Fin 8) (f : Fin 8 → ℕ), (∑ y ∈ (Fin.fintype 8).elems, f y) = (∑ y ∈ ((Fin.fintype 8).elems.erase i), f y) + f i := by
      intro i f; rw [Finset.sum_erase_add]; apply Finset.mem_univ
    rw [this]
    pick_goal 2; exact i
    have : (∑ x ∈ f i, count x i) = 6 := by
      unfold count; simp [*]
    rw [this]
    simp
    by_contra
    simp at this
    have : ∃ z ∈ Fintype.elems.erase i, ∑ x ∈ f i, count x z > 1 := by
      by_contra
      push_neg at this
      have : ∑ z ∈ Fintype.elems.erase i, ∑ x ∈ f i, count x z ≤ 7 := by
        trans ∑ z ∈ Fintype.elems.erase i, 1
        · gcongr with xx yy; simp [*]
        · simp; apply le_of_eq; rw [Finset.card_erase_eq_ite];
          have : i ∈ (Fin.fintype 8).elems := by apply Finset.mem_univ
          simp [this]; rfl
      omega
    obtain ⟨z, ⟨hz1, hz2⟩⟩ := this
    have : z ≠ i := by
      intro h; rw [h] at hz1; apply Finset.notMem_erase i; exact hz1
    unfold count at hz2
    have : ∃ (x y : Fin n), (x ∈ f i) ∧ (x ∈ f z) ∧ (y ∈ f i) ∧ (y ∈ f z) ∧ (x ≠ y) := by
      have := ll (m := 8) (n := n) f (p := λ finn ↦ finn ∈ f z) i hz2
      obtain ⟨x, y, q1, q2, q3, q4, q5⟩ := this
      simp at q4
      simp at q5
      use x, y
    obtain ⟨ex, ey, p1, p2, p3, p4, p5⟩ := this
    apply h2 ex ey i z ?_ p1 p3 p5 ⟨p2,p4⟩
    · intro h; apply this; rw [h]


end Usa2001P1
