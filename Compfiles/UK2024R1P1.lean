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
  def S (k : ℕ) := {f : Equiv.Perm (Fin k) | ∀ k, (f k : ℕ) ≤ k + 1}

  lemma S_succ_k_card_eq_two_mul_S_k_card {k : ℕ} (hk : k ≥ 1) :
    (S (k + 1)).ncard = 2 * (S k).ncard := by
    let S₁ := {f | f ∈ S (k + 1) ∧ f 0 = 0}
    let S₂ := {f | f ∈ S (k + 1) ∧ f 0 = 1}
    have h1 : (1 : Fin (k + 1)).val = 1 := by {
        simp
        linarith
    }
    have h2 {n : Fin (k + 1)} (hn : n ≠ 0) : 1 ≤ n := by {
      rw [←Fin.pos_iff_ne_zero] at hn
      omega
    }
    have h3 : S₁.ncard = (S k).ncard := by {
      have h3_1 (g : Equiv.Perm (Fin (k + 1))) (hg : g ∈ S₁) (n : Fin k) : 1 ≤ g n.succ := by {
        rw [←Fin.zero_add 1]
        apply Fin.add_one_le_of_lt
        rw [Fin.pos_iff_ne_zero]
        simp
        rw [←hg.2, Equiv.apply_eq_iff_eq]
        exact Fin.succ_ne_zero n
      }
      have h3_2 (g : Equiv.Perm (Fin (k + 1))) (hg : g ∈ S₁) (n : Fin k) : 1 ≤ (Equiv.symm g) n.succ := by {
        rw [←Fin.zero_add 1]
        apply Fin.add_one_le_of_lt
        rw [Fin.pos_iff_ne_zero]
        simp
        rw [←Equiv.apply_eq_iff_eq g, Equiv.apply_symm_apply, hg.2]
        exact Fin.succ_ne_zero n
      }

      let toFun (g : Equiv.Perm (Fin (k + 1))) (hg : g ∈ S₁) (n : Fin k) : Fin k :=
        Fin.castLT (g (n + 1) - 1) (by {
          simp
          rw [Fin.coe_sub_iff_le.2 (h3_1 g hg n), Nat.sub_lt_iff_lt_add (Fin.val_fin_le.2 (h3_1 g hg n)), h1, Nat.add_comm 1 k]
          exact (g n.succ).isLt
        })

      let invFun (g : Equiv.Perm (Fin (k + 1))) (hg : g ∈ S₁) (n : Fin k) : Fin k :=
        Fin.castLT (g.invFun (n + 1) - 1) (by {
          simp
          rw [Fin.coe_sub_iff_le.2 (h3_2 g hg n), Nat.sub_lt_iff_lt_add (Fin.val_fin_le.2 (h3_2 g hg n)), h1, Nat.add_comm 1 k]
          exact ((Equiv.symm g) n.succ).isLt
        })

      have h3_3 (g : Equiv.Perm (Fin (k + 1))) (hg : g ∈ S₁) : Function.LeftInverse (invFun g hg) (toFun g hg) := by {
        intro n
        simp [invFun, toFun, Fin.castLT]
        conv in ↑(g n.succ - 1) + 1 =>
          rw [Fin.coe_sub_iff_le.2 (h3_1 g hg n), ←(Nat.sub_add_comm (Fin.val_fin_le.2 (h3_1 g hg n))), h1, Nat.add_sub_cancel_right]
        simp
        conv =>
          left
          left
          rw [Fin.coe_sub, h1]
        simp [Nat.add_comm _ 1, ←Nat.add_assoc]
        congr
        apply Nat.mod_eq_of_lt
        apply lt_trans n.isLt
        linarith
      }

      have h3_4 (g : Equiv.Perm (Fin (k + 1))) (hg : g ∈ S₁) : Function.RightInverse (invFun g hg) (toFun g hg) := by {
        intro n
        simp [invFun, toFun, Fin.castLT]
        conv in ↑((Equiv.symm g) n.succ - 1) + 1 =>
          rw [Fin.coe_sub_iff_le.2 (h3_2 g hg n), ←(Nat.sub_add_comm (Fin.val_fin_le.2 (h3_2 g hg n))), h1, Nat.add_sub_cancel_right]
        simp
        conv =>
          left
          left
          rw [Fin.coe_sub, h1]
        simp [Nat.add_comm _ 1, ←Nat.add_assoc]
        congr
        apply Nat.mod_eq_of_lt
        apply lt_trans n.isLt
        linarith
      }

      let f (g : Equiv.Perm (Fin (k + 1))) (hg : g ∈ S₁) := Equiv.mk (toFun g hg) (invFun g hg) (h3_3 g hg) (h3_4 g hg)
      apply Set.ncard_congr f
      {
        intro a ha
        simp [S, f, toFun]
        intro n
        rw [Fin.coe_sub_iff_le.2 (h3_1 a ha n), Nat.sub_le_iff_le_add]
        convert ha.1 n.succ
      }
      {
        intro a b ha hb hab
        rw [Equiv.ext_iff] at hab
        rw [Equiv.ext_iff]
        intro x
        rcases Fin.eq_or_lt_of_le (Fin.zero_le x) with hx | hx
        rw [←hx, ha.2, hb.2]
        {
          have hx' : 1 ≤ x := by omega
          have hab' := hab (Fin.castLT (x - 1) (by {
            rw [Fin.coe_sub_iff_le.2 hx', Nat.sub_lt_iff_lt_add hx', h1, Nat.add_comm 1 k]
            exact x.isLt
          }))
          simp [f, toFun, Fin.castLT] at hab'
          conv at hab' =>
            pattern (occs := *) ↑(x - 1) + 1
            rw [Fin.coe_sub_iff_le.2 hx', h1, Nat.sub_add_cancel (by omega)]
          simp [Fin.val_inj] at hab'
          exact hab'
        }
      }
      {
        intro b hb

        let a_toFun (n : Fin (k + 1)) : Fin (k + 1) :=
        if hn : n = 0 then 0 else (b (Fin.castLT (n - 1) (by {
          have hn' : 1 ≤ n := h2 hn
          rw [Fin.coe_sub_iff_le.2 hn', Nat.sub_lt_iff_lt_add hn', h1, Nat.add_comm 1 k]
          exact n.isLt
        })) + 1)

        let a_invFun (n : Fin (k + 1)) : Fin (k + 1) :=
        if hn : n = 0 then 0 else (b.invFun (Fin.castLT (n - 1) (by {
          have hn' : 1 ≤ n := h2 hn
          rw [Fin.coe_sub_iff_le.2 hn', Nat.sub_lt_iff_lt_add hn', h1, Nat.add_comm 1 k]
          exact n.isLt
        })) + 1)

        have h3_5 : Function.LeftInverse a_invFun a_toFun := by {
          intro n
          simp [a_invFun, a_toFun, Fin.castLT]
          rcases eq_or_ne n 0 with hn | hn
          simp [hn]
          simp [hn, Fin.succ_ne_zero]
          simp [←Fin.coeSucc_eq_succ]
        }
        have h3_6 : Function.RightInverse a_invFun a_toFun := by {
          intro n
          simp [a_invFun, a_toFun, Fin.castLT]
          rcases eq_or_ne n 0 with hn | hn
          simp [hn]
          simp [hn, Fin.succ_ne_zero]
          simp [←Fin.coeSucc_eq_succ]
        }

        let a := Equiv.mk a_toFun a_invFun h3_5 h3_6
        have ha : a ∈ S₁ := by {
          constructor
          {
            intro n
            simp [a, a_toFun]
            rcases eq_or_ne n 0 with hn | hn
            simp [hn]
            simp [hn]
            apply Nat.le_trans (hb _)
            have hn' : 1 ≤ n := h2 hn
            simp [Fin.castLT]
            rw [Fin.coe_sub_iff_le.2 hn', h1, Nat.sub_add_cancel (by omega)]
          }
          {
            simp [a, a_toFun]
          }
        }
        use a, ha
        rw [Equiv.ext_iff]
        intro n
        simp [f, a, toFun, a_toFun, Fin.succ_ne_zero]
        simp [←Fin.coeSucc_eq_succ]
      }
    }
    have h4 : S₂.ncard = (S k).ncard := by {
      let toFun (g : Equiv.Perm (Fin (k + 1))) (hg : g ∈ S₂) (n : Fin k) : Fin k :=
        if hg' : g (n + 1) = 0 then
        Fin.castLT (g (n + 1)) (by {
          rw [hg', Fin.val_zero]
          linarith
        })
        else Fin.castLT (g (n + 1) - 1) (by {
          have hg'' := h2 hg'
          rw [Fin.coe_sub_iff_le.2 hg'', Nat.sub_lt_iff_lt_add hg'', h1, Nat.add_comm 1]
          apply Fin.isLt
        })

      let invFun (g : Equiv.Perm (Fin (k + 1))) (hg : g ∈ S₂) (n : Fin k) : Fin k :=
        if hg' : n = (0 : Fin (k + 1)) then
        Fin.castLT ((g.invFun n) - 1) (by {
          have hg'' : 1 ≤ g.invFun n := by {
            apply h2
            contrapose! hg'
            rw [Equiv.invFun_as_coe, Equiv.symm_apply_eq, hg.2] at hg'
            rw [hg']
            simp
            linarith
          }
          rw [Fin.coe_sub_iff_le.2 hg'', Nat.sub_lt_iff_lt_add hg'', h1, Nat.add_comm 1]
          apply Fin.isLt
        })
        else Fin.castLT (g.invFun (n + 1) - 1) (by {
          have hg'' : 1 ≤ g.invFun (n + 1) := by {
            apply h2
            contrapose! hg'
            rw [Equiv.invFun_as_coe, Equiv.symm_apply_eq, hg.2] at hg'
            exact self_eq_add_left.1 (id (Eq.symm hg'))
          }
          rw [Fin.coe_sub_iff_le.2 hg'', Nat.sub_lt_iff_lt_add hg'', h1, Nat.add_comm 1]
          apply Fin.isLt
        })

      have h4_1 (g : Equiv.Perm (Fin (k + 1))) (hg : g ∈ S₂) : Function.LeftInverse (invFun g hg) (toFun g hg) := by {
        intro n
        simp [invFun, toFun]
        rcases eq_or_ne (g n.succ) 0 with hg' | hg'
        {
          simp [hg']
          rw [←Equiv.eq_symm_apply] at hg'
          simp [←hg', ←Fin.coeSucc_eq_succ]
        }
        {
          have hg'' : g n.succ - 1 ≠ 0 := by {
            have hn := Fin.succ_ne_zero n
            contrapose! hn
            rw [sub_eq_zero, ←hg.2, Equiv.apply_eq_iff_eq] at hn
            exact hn
          }
          simp [hg', hg'', Fin.castLT]
          conv in ↑(g n.succ - 1) + 1 =>
            rw [Fin.coe_sub_iff_le.2 (h2 hg'), ←(Nat.sub_add_comm (Fin.val_fin_le.2 (h2 hg'))), h1, Nat.add_sub_cancel_right]
          simp [←Fin.coeSucc_eq_succ]
        }
      }

      have h4_2 (g : Equiv.Perm (Fin (k + 1))) (hg : g ∈ S₂) : Function.RightInverse (invFun g hg) (toFun g hg) := by {
        intro n
        simp only [toFun, invFun, Fin.castLT]
        rcases eq_or_ne n.castSucc 0 with hn | hn
        {
          simp [hn]
          rw [←Fin.castSucc_inj]
          simp [hn]
        }
        {
          simp [hn, Fin.succ_ne_zero]
          simp [←Fin.coeSucc_eq_succ]
        }
      }

      let f (g : Equiv.Perm (Fin (k + 1))) (hg : g ∈ S₂) := Equiv.mk (toFun g hg) (invFun g hg) (h4_1 g hg) (h4_2 g hg)
      apply Set.ncard_congr f
      {
        intro a ha
        simp [S, f]
        intro n
        simp only [toFun]
        rcases eq_or_ne (a n.succ) 0 with hn | hn
        simp [hn]
        {
          simp [hn]
          rw [Fin.coe_sub_iff_le.2 (h2 hn), Nat.sub_le_iff_le_add, h1]
          apply le_trans (ha.1 n.succ)
          apply le_of_eq
          simp
        }
      }
      {
        intro a b ha hb hab

        sorry
      }
      {
        sorry
      }
    }
    have h5 : Disjoint S₁ S₂ := by {
      rw [Set.disjoint_left]
      rintro f ⟨hf, hf'⟩
      rw [Set.mem_setOf]
      push_neg
      intro
      rw [hf', ←Fin.val_ne_iff, Fin.val_zero]
      rw [h1]
      norm_num
    }
    have h6 : S (k + 1) = S₁ ∪ S₂ := by sorry
    rw [h6, Set.ncard_union_eq h5, h3, h4, two_mul]

  lemma S_card_eq_two_pow_k_sub_one {k : ℕ} (hk : k ≥ 1) :
    (S k).ncard = 2 ^ (k - 1) := by
    induction k, hk using Nat.le_induction with
    | base => {
      simp
      let f : Equiv.Perm (Fin 1) := Equiv.mk id id (by decide) (by decide)
      use f
      apply Set.ext
      intro g
      constructor
      {
        unfold S
        simp
        rw [Equiv.ext_iff]
        omega
      }
      {
        unfold S
        simp
      }
    }
    | succ n hn hn'=> {
      simp [S_succ_k_card_eq_two_mul_S_k_card hn, hn', ←Nat.pow_add_one', Nat.sub_add_cancel hn]
    }
snip end

determine solution_value : ℕ := 256

/-
Since OLYMPIADS has no duplicate letters, then the set of spellings is just a
subset of the permutations of 9 elements.
-/
problem uk2024_r1_p1 :
  {f : Equiv.Perm (Fin 9) | ∀ k, (f k : ℕ) ≤ k + 1}.ncard = solution_value := by
    have h1 : {f : Equiv.Perm (Fin 9) | ∀ k, (f k : ℕ) ≤ k + 1} = S 9 := rfl
    rw [h1, S_card_eq_two_pow_k_sub_one (by norm_num)]
    norm_num
