/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: short_c1rcuit
-/
import Mathlib.Data.Set.Card
import Mathlib.Logic.Equiv.Defs
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# British Mathematical Olympiad 2024, Round 1, Problem 1

An unreliable typist can guarantee that when they try to type a word with
different letters, every letter of the word will appear exactly once in what
they type, and each letter will occur at most one letter late (though it may
occur more than one letter early). Thus, when trying to type MATHS, the
typist may type MATHS, MTAHS or TMASH, but not ATMSH.

Determine, with proof, the number of possible spellings of OLYMPIADS
that might be typed.
-/

namespace UK2024R1P1

snip begin
/-
The basic idea of this proof is that the first letter can only go in the first
or second position. In both cases the spellings of the other letters is
equivalent to a valid spelling of an eight letter word. So the number of valid
spellings for nine letters is two times that for eight letters. Similar logic
gets the same relation for eight and seven letter words. This recurses down
until we reach one letter, which only has one spelling. Thus, OLYMPIADS has
2*2*2*2*2*2*2*2*1 = 2^8 = 256 valid spellings.

Most of this proof is defining the mapping between spellings of k + 2 letters
where the first letter goes to position m and spellings of k + 1 letters. This
is done by removing that first letter and shifting the letters after it over
to fill in the gap. Then we show that if m is one of the first two positions,
the spellings the mapping creates are valid and the mapping itself is
bijective. Thus the two sets of spellings have the same size.
-/

variable {k : ℕ} {m : Fin (k + 2)}

def S (k : ℕ) := {f : Equiv.Perm (Fin k) | ∀ n, (f n).castSucc ≤ n.succ}
def S' (k : ℕ) (m : Fin (k + 2)) := {f | f ∈ S (k + 2) ∧ f 0 = m}

lemma g_nonzero_ne_m {g : Equiv.Perm (Fin (k + 2))}
    (hg : g ∈ (S' k m)) (n : Fin (k + 2)) (hn : n ≠ 0) : g n ≠ m := by
  contrapose! hn
  rwa [←Equiv.apply_eq_iff_eq g, hg.2]

def f_toFun (g : Equiv.Perm (Fin (k + 2))) (hg : g ∈ (S' k m)) (n : Fin (k + 1)) : Fin (k + 1) :=
  if hg' : g n.succ ≤ m then
    (g n.succ).castPred (by
      replace hg' := lt_iff_le_and_ne.2 ⟨hg', g_nonzero_ne_m hg n.succ (Fin.succ_ne_zero n)⟩
      exact Fin.ne_last_of_lt hg'
    )
  else
    (g n.succ).pred (by
      push_neg at hg'
      exact Fin.ne_zero_of_lt hg'
    )

def f_invFun (g : Equiv.Perm (Fin (k + 2))) (hg : g ∈ (S' k m)) (n : Fin (k + 1)) : Fin (k + 1) :=
  if hg' : n.castSucc < m then
    (g.symm n.castSucc).pred (by
      contrapose! hg'
      rw [le_iff_lt_or_eq]
      right
      rw [←hg.2, ←hg', Equiv.apply_symm_apply]
    )
  else
    (g.symm n.succ).pred (by
      contrapose! hg'
      rw [Equiv.symm_apply_eq, hg.2] at hg'
      simp only [←hg', Fin.castSucc_lt_succ_iff, le_refl]
    )

lemma f_left_inv (g : Equiv.Perm (Fin (k + 2))) (hg : g ∈ (S' k m)) :
    Function.LeftInverse (f_invFun g hg) (f_toFun g hg) := by
  intro n
  simp [f_invFun, f_toFun]
  obtain hg' | hg' := em (g n.succ ≤ m)
  · simp only [hg']
    replace hg' := lt_iff_le_and_ne.2 ⟨hg', g_nonzero_ne_m hg n.succ (Fin.succ_ne_zero n)⟩
    simp [hg']
  · simp only [hg', reduceDIte, Fin.succ_pred, Equiv.symm_apply_apply, Fin.pred_succ]
    apply dif_neg
    intro hg''
    apply hg'
    push_neg at hg'
    rwa [←Fin.lt_castPred_iff (Fin.ne_last_of_lt hg'), Fin.pred_lt_castPred_iff] at hg''

lemma f_right_inv (g : Equiv.Perm (Fin (k + 2))) (hg : g ∈ (S' k m)) :
    Function.RightInverse (f_invFun g hg) (f_toFun g hg) := by
  intro n
  simp [f_invFun, f_toFun]
  obtain hg' | hg' := em (n.castSucc < m)
  · simp only [hg']
    replace hg' := le_of_lt hg'
    simp [hg']
  · simp only [hg', reduceDIte, Fin.succ_pred, Equiv.apply_symm_apply, Fin.pred_succ]
    apply dif_neg
    intro hg''
    apply hg'
    exact hg''

def f (g : Equiv.Perm (Fin (k + 2))) (hg : g ∈ (S' k m)) :=
  Equiv.mk (f_toFun g hg) (f_invFun g hg) (f_left_inv g hg) (f_right_inv g hg)

def f'_toFun (g : Equiv.Perm (Fin (k + 1))) (m : Fin (k + 2)) (n : Fin (k + 2)) : Fin (k + 2) :=
  if hn : n = 0 then
    m
  else
    if (g (n.pred hn)).castSucc < m then
      (g (n.pred hn)).castSucc
    else
      (g (n.pred hn)).succ

def f'_invFun (g : Equiv.Perm (Fin (k + 1))) (m : Fin (k + 2)) (n : Fin (k + 2)) : Fin (k + 2) :=
  if hn : n = m then
    0
  else
    if hn' : n < m then
      (g.symm (n.castPred (Fin.ne_last_of_lt hn'))).succ
    else
      (g.symm (n.pred (Fin.ne_zero_of_lt (lt_iff_le_and_ne.2 ⟨le_of_not_gt hn', Ne.symm hn⟩)))).succ

lemma f'_left_inv (g : Equiv.Perm (Fin (k + 1))) :
    Function.LeftInverse (f'_invFun g m) (f'_toFun g m) := by
  intro n
  simp only [f'_invFun, f'_toFun]
  obtain hn | hn := em (n = 0) <;> simp [hn]
  obtain hg | hg := em ((g (n.pred hn)).castSucc < m)
  · simp only [hg, reduceIte, ne_of_lt, reduceDIte, Fin.castPred_castSucc,
               Equiv.symm_apply_apply, Fin.succ_pred]
  · simp [hg]
    push_neg at hg
    simp only [hg, Fin.le_castSucc_iff.mp, ne_of_gt, reduceIte, not_lt_of_gt, reduceDIte]

lemma f'_right_inv (g : Equiv.Perm (Fin (k + 1))) :
    Function.RightInverse (f'_invFun g m) (f'_toFun g m) := by
  intro n
  simp only [f'_invFun, f'_toFun]
  obtain hn | hn := em (n = m) <;> simp [hn]
  obtain hg | hg := em (n < m)
  · simp only [hg, reduceDIte, Fin.pred_succ, Equiv.apply_symm_apply, Fin.castSucc_castPred,
               Fin.succ_ne_zero, reduceIte]
  · simp_rw [hg, reduceDIte, Fin.succ_ne_zero, reduceDIte, Fin.pred_succ,
             Equiv.apply_symm_apply, Fin.succ_pred]
    apply dif_neg
    push_neg at *
    rw [Fin.le_castSucc_pred_iff]
    exact lt_iff_le_and_ne.2 ⟨hg, Ne.symm hn⟩

def f' (m : Fin (k + 2)) (g : Equiv.Perm (Fin (k + 1))) :=
  Equiv.mk (f'_toFun g m) (f'_invFun g m) (f'_left_inv g) (f'_right_inv g)

lemma f'_in_S'_k (hm : m ≤ 1) {g : Equiv.Perm (Fin (k + 1))} (hg : g ∈ S (k + 1)) :
    f' m g ∈ S' k m := by
  constructor
  · intro n
    simp [f', f'_toFun]
    obtain hn | hn := em (n = 0) <;> simp [hn]
    · exact hm
    · obtain hn' | hn' := em ((g (n.pred hn)).castSucc < m) <;>
        simp only [hn', ↓reduceIte ]
      · apply le_trans (Fin.castSucc_le_castSucc_iff.2 (hg (n.pred hn)))
        rw [Fin.succ_pred]
        exact le_of_lt (Fin.castSucc_lt_succ n)
      · rw [←Fin.succ_castSucc]
        apply le_trans (Fin.succ_le_succ_iff.2 (hg (n.pred hn)))
        rw [Fin.succ_pred]
  · simp [f', f'_toFun]

  lemma f_f'_left_inv {g : Equiv.Perm (Fin (k + 2))} (hg : g ∈ S' k m) : f' m (f g hg) = g := by
    apply Equiv.ext
    intro x
    simp [f', f'_toFun, f, f_toFun]
    obtain hx | hx := em (x = 0) <;> simp [hx, hg.2]
    obtain hx' | hx' := em (g x ≤ m)
    · simp only [hx', reduceDIte, Fin.castSucc_castPred]
      exact dif_pos (lt_iff_le_and_ne.2 ⟨hx', g_nonzero_ne_m hg x hx⟩)
    · simp only [hx', reduceDIte, Fin.succ_pred]
      apply dif_neg
      push_neg at *
      rwa [Fin.le_castSucc_pred_iff]

lemma f_f'_right_inv (hm : m ≤ 1) {g : Equiv.Perm (Fin (k + 1))} (hg : g ∈ S (k + 1)) :
    f (f' m g) (f'_in_S'_k hm hg) = g := by
  apply Equiv.ext
  intro x
  simp [f, f_toFun, f', f'_toFun, Fin.succ_ne_zero]
  obtain hx | hx := em ((g x).castSucc < m)
  · simp only [hx, reduceIte, Fin.castPred_castSucc]
    exact dif_pos (le_of_lt hx)
  · simp_rw [hx, reduceIte, Fin.pred_succ]
    apply dif_neg
    contrapose! hx
    rwa [Fin.castSucc_lt_iff_succ_le]

lemma S'_k_card_eq_S_succ_k_card (hm : m ≤ 1) : (S' k m).ncard = (S (k + 1)).ncard := by
    apply Set.ncard_congr f
    · intro a ha
      simp [S, f, f_toFun]
      intro n
      obtain h | h := em (a n.succ ≤ m)
      · simp only [h, reduceDIte, Fin.castSucc_castPred]
        exact le_trans (le_trans h hm) (Fin.succ_pos n)
      · simp [h]
        replace ha := ha.1 n.succ
        rw [Fin.castSucc_pred_eq_pred_castSucc]
        apply le_trans (Fin.pred_le_pred_iff.2 ha)
        rw [Fin.pred_succ]
        exact n.succ.succ_ne_zero
    · intro a b ha hb hab
      rw [←f_f'_left_inv ha, ←f_f'_left_inv hb, hab]
    · intro b hb
      exact ⟨f' m b, ⟨f'_in_S'_k hm hb, f_f'_right_inv hm hb⟩⟩

lemma S_succ_succ_k_card_eq_two_mul_S_succ_k_card : (S (k + 2)).ncard = (S (k + 1)).ncard * 2 := by
    let S₁ := S' k 0
    let S₂ := S' k 1
    have h1 : S₁.ncard = (S (k + 1)).ncard := by exact S'_k_card_eq_S_succ_k_card (by norm_num)
    have h2 : S₂.ncard = (S (k + 1)).ncard := by exact S'_k_card_eq_S_succ_k_card (by norm_num)
    have h3 : Disjoint S₁ S₂ := by {
      rw [Set.disjoint_left]
      rintro f ⟨_, hf⟩
      simp [S₂, S', Set.mem_setOf]
      intro
      rw [hf]
      aesop
    }
    have h4 : S (k + 2) = S₁ ∪ S₂ := by
      apply Set.ext
      intro x
      constructor <;> intro hx
      · have hx' : (x 0) ≤ 1 := by
          rw [←Fin.val_fin_le, Fin.val_one]
          exact hx 0
        obtain hx' | hx' := le_iff_lt_or_eq.mp hx'
        · left
          replace hx' : x 0 = 0 := by
            rw [←Fin.val_eq_val, Fin.val_zero, ←Nat.lt_one_iff]
            rwa [Fin.lt_iff_val_lt_val, Fin.val_one] at hx'
          exact ⟨hx, hx'⟩
        · right
          exact ⟨hx, hx'⟩
      · obtain hx | hx := hx <;> exact hx.1
    rw [h4, Set.ncard_union_eq h3, h1, h2, mul_two]

lemma S_succ_k_card_eq_two_pow_k {k : ℕ} :
    (S (k + 1)).ncard = 2 ^ k := by
  induction k with
  | zero =>
      simp
      let f : Equiv.Perm (Fin 1) := Equiv.mk id id (by decide) (by decide)
      use f
      apply Set.ext
      intro g
      constructor <;> simp [S]
      · rw [Equiv.ext_iff]
        omega
      · intro h n
        simp [h, f, Fin.eq_zero]
  | succ n hn =>
      rw [Nat.pow_succ, ←hn, S_succ_succ_k_card_eq_two_mul_S_succ_k_card]
snip end

determine solution_value : ℕ := 256

/-
Since OLYMPIADS has no duplicate letters, then the set of spellings is just a
subset of the permutations of 9 elements.
-/
problem uk2024_r1_p1 :
  {f : Equiv.Perm (Fin 9) | ∀ k, (f k : ℕ) ≤ k + 1}.ncard = solution_value := by
    change (S 9).ncard = solution_value
    rw [S_succ_k_card_eq_two_pow_k]
    norm_num


end UK2024R1P1
