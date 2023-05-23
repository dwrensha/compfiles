import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Int.Basic

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.LibrarySearch

/-
Polish Mathematical Olympiad 1998, Problem 4

Prove that the sequence {a_n} defined by a_1 = 1 and

     a_n = a_{n - 1} + a_{⌊n/2⌋}        n = 2,3,4,...

contains infinitely many integers divisible by 7.

-/

namespace Poland1998Q4

def a : ℕ → ℕ
| 0 => 1 -- unused dummy value
| 1 => 1
| Nat.succ n =>
    have _ : (n.succ / 2) < n.succ := Nat.div_lt_self' n 0
    a n + a (n.succ / 2)

lemma a_recurrence (n : ℕ) (hn : 2 ≤ n) : a n = a (n - 1) + a (n / 2) := by
  cases' n with n
  · exact (Nat.not_succ_le_zero _ hn).elim
  · cases' n
    · exact (Nat.not_succ_le_self _ hn).elim
    · simp only [a, Nat.succ_sub_succ_eq_sub, tsub_zero]

lemma lemma1 (n : ℕ) (npos : 0 < n) : 2 * (n - 1) + 1 = 2 * n - 1 := by
  cases' n with n
  · exact (lt_asymm npos npos).elim
  · rfl

lemma lemma2 (n : ℕ) : (2 * n + 1) / 2 = n := by
  have h1 : ¬ 2 ∣ 2 * n + 1 := by
    intro h
    have h1 : 2 ∣ 2 * n := Dvd.intro n rfl
    have : 2 ∣ 1 := (Nat.dvd_add_right h1).mp h
    rw [Nat.dvd_one] at this
    exact Nat.succ_succ_ne_one 0 this
  rw [Nat.succ_div_of_not_dvd h1]
  exact Nat.mul_div_right n zero_lt_two

def a' : ℕ → ZMod 7
| n => ⟨(a n) % 7, Nat.mod_lt _ (by norm_num)⟩

lemma a'_5_is_0 : a' 5 = 0 := by
  simp [a',a, Nat.succ_eq_one_add,
        show 1 + 1 / 2 = 1 by norm_num,
        show (1 + 3) / 2 = 2 by norm_num,
        show (1 + 4) / 2 = 2 by norm_num ]

lemma zmod_ext (a b : ZMod 7) (hz : ZMod.val a = ZMod.val b) : a = b := by
  have : ((ZMod.val a) : ZMod 7)  = ((ZMod.val b) : ZMod 7) := congrArg Nat.cast hz
  simp only [ZMod.nat_cast_val, ZMod.cast_id', id_eq] at this
  exact this

lemma a'_recurrence (n : ℕ) (hn : 2 ≤ n) : a' n = a' (n - 1) + a' (n / 2) := by
  have : (a' n).val = (a' (n - 1) + a' (n / 2)).val := by
    rw [ZMod.val_add]
    simp_rw [a', a_recurrence n hn]
    rw [ZMod.val]
    simp
  exact zmod_ext _ _ this

lemma lemma3
    (N0 : ℕ)
    (k : ZMod 7)
    (hk : k ≠ 0)
    (hN : ∀ i : ℕ, i < 7 → a' (N0 + i) = a' N0 + k * i) :
    (∃ i : ℕ, i < 7 ∧ a' (N0 + i) = 0) := by
  have hp : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  let ii := - (a' N0) / k
  use ii.val
  constructor
  · exact ZMod.val_lt ii
  · have := hN ii.val (ZMod.val_lt ii)
    rw [this, ZMod.nat_cast_val, ZMod.cast_id', id.def, mul_div_cancel' _ hk]
    exact add_neg_self (a' N0)

lemma lemma6 (n : ℕ) : (4 * (n - 1) + 1 + 3) / 2 = (2 * (n - 1) + 1 + 1) := by
  have : (4 * (n - 1) + 1 + 3) = 2 * (2 * (n - 1) + 1 + 1) := by ring
  rw [this, Nat.mul_div_right]
  exact two_pos


lemma lemma6' (n : ℕ) : (4 * (n - 1) + 1 + 4) / 2 = (2 * (n - 1) + 1 + 1) := by
  have h1 : (4 * (n - 1) + 1 + 4) = 2 * (2 * (n - 1) + 1 + 1) + 1 := by linarith
  rw [h1]
  exact lemma2 (2 * (n - 1) + 1 + 1)

lemma lemma7 (n : ℕ) : (4 * (n - 1) + 1 + 5) / 2 = (2 * (n - 1) + 1 + 2) := by
  have h1 : (4 * (n - 1) + 1 + 5) = 2 * (2 * (n - 1) + 1 + 2) := by ring
  have h2 : (4 * (n - 1) + 1 + 5) / 2 = (2 * (2 * (n - 1) + 1 + 2)) / 2 :=
    congrFun (congrArg HDiv.hDiv h1) 2
  rwa[Nat.mul_div_right _ (show 0 < 2 by norm_num)] at h2

lemma lemma7' (n : ℕ) : (4 * (n - 1) + 1 + 6) / 2 = (2 * (n - 1) + 1 + 2) := by
  have h1 : (4 * (n - 1) + 1 + 6) = 2 * (2 * (n - 1) + 1 + 2) + 1 := by ring
  rw [h1]
  exact lemma2 (2 * (n - 1) + 1 + 2)

lemma can_get_a_later_one_zmod :
    (∀ N : ℕ, a' N = 0 → (∃ M : ℕ, N < M ∧ a' M = 0)) := by
  intros n hn

  obtain (hlt : n < 2) | (hlte : 2 ≤ n) := lt_or_ge n 2
  · use 5
    constructor
    · calc n < 2 := hlt
           _ < 5 := by norm_num
    · exact a'_5_is_0

  let n1 : ℕ := 2 * (n - 1) + 1

  -- a' (2 * n - 1), a' (2 * n), and a' (2 * n + 1) are all equal

  have npos := calc 0 < 2 := by norm_num
                    _ ≤ n := hlte
  have hn1v : n1 = 2 * n - 1 := lemma1 n npos
  have hn2: 2 ≤ n1 + 1 := by
    have : 1 ≤ n1 := le_add_self
    exact Nat.succ_le_succ this

  have hn3: 2 ≤ n1 + 2 := le_add_self

  let an1 := a' n1

  have hn1 : (n1 + 1) = 2 * n := by
    have hrw : (n1 + 1) = 2 * (n - 1) + 1 + 1 := rfl
    rw [hrw]
    cases' n
    · exfalso; exact lt_asymm npos npos
    · rfl

  have ha1 : a' (n1 + 1) = an1 + a' n := by
    have haa : a' (n1 + 1) = a' n1 + a' (n1.succ / 2) := a'_recurrence (n1 + 1) hn2
    have h2n1 : 2 * n / 2 = n := by norm_num
    have h2n1' : (n1 + 1) / 2 = n := by rw [hn1, h2n1]
    rw [haa, h2n1']

  have hn1' : n1 + 2 = 2 * n + 1 := by
    have hrw : (n1 + 2) = 2 * (n - 1) + 1 + 1 + 1 := rfl
    rw [hrw]
    cases' n
    · exfalso; exact lt_asymm npos npos
    · rfl

  have ha2 : a' (n1 + 2) = a' (n1 + 1) +  a' n := by
    have haa : a' (n1 + 2) = a' (n1 + 1) + a' (n1.succ.succ / 2) :=
      a'_recurrence (n1 + 2) hn3
    have h1 : (2 * n + 1) / 2 = n := lemma2 n
    have hn1v' : 2 * n = n1 + 1 := by
      have hrw : n1 + 1 = 2 * (n - 1) + 1 + 1 := rfl
      rw [hrw]
      cases' n
      · exfalso; exact lt_asymm npos npos
      · rfl
    rw [haa]
    congr
    have : n1.succ.succ = (n1 + 1 + 1) := rfl
    rw [this, ←hn1v', h1]

  have ha1' : a' (n1 + 1) = a' n1 := by
    rw [hn] at ha1
    simp at ha1
    exact ha1

  have ha2' : a' (n1 + 2) = a' n1 := by
    rw [hn, ha1'] at ha2
    simp at ha2
    exact ha2

  clear ha1 ha2

  have : ∀ i, i ≤ 2 → a' (n1 + i) = a' n1 := by
    intros i hi
    interval_cases i
    · rfl
    · exact ha1'
    · exact ha2'

  -- then the seven elements beginning with a (4 * n - 3) will all have different
  -- residues mod 7.

/-

  let n4 := 4 * n - 3,
  -- a (n4 + 1) = a n4 + a n1
  -- a (n4 + 2) = a (n4 + 1) + a n1
  -- a (n4 + 3) = a (n4 + 2) + a (n1 + 1)
  -- a (n4 + 4) = a (n4 + 3) + a (n1 + 1)
  -- a (n4 + 5) = a (n4 + 4) + a (n1 + 2)
  -- a (n4 + 6) = a (n4 + 5) + a (n1 + 2)

-/

  -- n2 = 4 * n - 3
  --   = 4 * (n - 1) + 1
  let n2: ℕ := 4 * (n - 1) + 1

  have hii : ∀ i, i < 6 → a' (n2 + i + 1) = a' (n2 + i) + a' n1 := by
    intros i hi
    have hn2ge2 : 2 ≤ n2 + i + 1 := by linarith
    have hr := a'_recurrence (n2 + i + 1) hn2ge2
    interval_cases i
    · suffices (n2 + 1) / 2 = n1 by rwa [this] at hr
      have : (4 * (n - 1) + 1 + 1) = 2 * (2 * (n - 1) + 1) := by ring
      simp only [this, Nat.succ_pos', Nat.mul_div_right]
    · suffices hn1 : (n2 + 2) / 2 = n1 by rwa [hn1] at hr
      have h1 : (4 * (n - 1) + 1 + 2) = 2 * (2 * (n - 1) + 1) + 1 := by ring
      rw [h1]
      exact lemma2 (2 * (n - 1) + 1)
    · have hn1 : (n2 + 3) / 2 = n1 + 1 := lemma6 n
      rw [hn1, ha1'] at hr
      exact hr
    · have hn1 : (n2 + 4) / 2 = n1 + 1 := lemma6' n
      rw [hn1, ha1'] at hr
      exact hr
    · have hn1 : (n2 + 5) / 2 = n1 + 2 := lemma7 n
      rw [hn1, ha2'] at hr
      exact hr
    · have hn1 : (n2 + 6) / 2 = n1 + 2 := lemma7' n
      rw [hn1, ha2'] at hr
      exact hr

  have hik : ∀ i, i < 7 → a' (n2 + i) = a' n2 + a' n1 * i := by
    intros i
    induction' i with p hp
    · intro; simp
    · intro hpi7
      have hpi6 : p < 6 := Nat.succ_lt_succ_iff.mp hpi7
      have hinc := hii p hpi6
      have hadd : n2 + p + 1 = n2 + p.succ := rfl
      have hi6 : p < 7 := Nat.lt.step hpi6
      have hpp := hp hi6
      have hp1: (p.succ : ZMod 7) = (p : ZMod 7) + 1 := by norm_cast
      rw [←hadd, hinc, hpp, hp1]
      ring

  obtain (haez : a' n1 = 0) | (hanez : ¬ a' n1 = 0) := em (a' n1 = 0)
  · use n1
    constructor
    · linarith
    · exact haez

  · have := lemma3 n2 (a' n1) hanez hik
    obtain ⟨ii, _, hia'⟩ := this
    use (n2 + ii)
    constructor
    · linarith
    · assumption

lemma can_get_a_later_one : (∀ N : ℕ, 7 ∣ a N → (∃ M : ℕ, N < M ∧ 7 ∣ a M)) := by
  intros n hn
  have ha' : a' n = 0 := by
    have : a' n = ⟨a n % 7, Nat.mod_lt _ (by norm_num)⟩ := by simp[a']
    rw [this]
    have := Nat.mod_eq_zero_of_dvd hn
    aesop
  obtain ⟨m, hmgt, hm7⟩ := can_get_a_later_one_zmod n ha'
  use m
  use hmgt
  have : a m % 7 = 0 := by injections
  exact Nat.dvd_of_mod_eq_zero this

lemma strengthen
    {P : ℕ → Prop}
    (h : ∀ N : ℕ, P N → (∃ M : ℕ, N < M ∧ P M))
    (he : ∃ N : ℕ, P N) :
    (∀ N : ℕ, ∃ M : ℕ, N < M ∧ P M) := by
  obtain ⟨N0, hn0⟩ := he
  intro N
  refine' Nat.recOn N _ _
  · obtain (hlt : 0 < N0) | (hlte : N0 ≤ 0) := lt_or_ge 0 N0
    · exact ⟨N0, hlt, hn0⟩
    · have heq : N0 = 0 := eq_bot_iff.mpr hlte
      rw [heq] at hn0
      exact h 0 hn0
  . intros pn hpn
    obtain ⟨m, hm, hmp⟩ := hpn
    obtain (hlt : pn + 1 < m) |  (hlte : m ≤ pn + 1) := lt_or_ge (pn + 1) m
    · exact ⟨m, hlt, hmp⟩
    · have heq : m = pn + 1 := le_antisymm hlte hm
      rw [heq] at hmp
      exact h (pn.succ) hmp

theorem poland1998_q4 : (∀ N : ℕ, ∃ M : ℕ, N < M ∧ 7 ∣ a M) := by
  have he: 7 ∣ a 5 := by rw [show a 5 = 7 by rfl]
  exact strengthen can_get_a_later_one ⟨5, he⟩
