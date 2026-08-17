/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Liao
-/

module

public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.Data.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics, .NumberTheory] }

/-!
# USA Mathematical Olympiad 2026, Problem 4

A positive integer n is called solitary if, for any non-negative integers a and b such
that a + b = n, either a or b contains the digit "1".
Determine, with proof, the number of solitary integers less than 10^2026.
-/

namespace Usa2026P4

open Classical

determine solution : ℕ := 2^2026 - 1

def has_digit_one (n : ℕ) : Prop :=
  1 ∈ Nat.digits 10 n

def is_solitary (n : ℕ) : Prop :=
  0 < n ∧ ∀ a b : ℕ, a + b = n → has_digit_one a ∨ has_digit_one b

snip begin
-- We follow Solution 1 by sillybone and Hpenguin from Art of Problem Solving.

-- lemma not_solitary_zero : ¬ is_solitary 0 := by simp [is_solitary]

lemma not_solitary_two_zeros {k : ℕ} : ¬ is_solitary (2 * 10 ^ k) := by
  rw [is_solitary]
  push Not
  intro _
  use (2 * 10 ^ k), 0
  and_intros
  · rfl
  · induction k with
    | zero => simp [has_digit_one]
    | succ k ih =>
      specialize ih (by omega)
      simp [has_digit_one, Nat.mul_mod, Nat.pow_mod]
      rw [Nat.pow_add_one 10 k]
      rw [Nat.mul_div_assoc 2 (Nat.dvd_mul_left _ _)]
      rw [Nat.mul_div_left (10 ^ k) (by decide)]
      rwa [has_digit_one] at ih
  · simp [has_digit_one]

lemma digit_squeeze {m k : ℕ} (hm : m ∈ Set.Ico (10 ^ k) (2 * 10 ^ k)) : 1 ∈ Nat.digits 10 m := by
  induction k generalizing m with
  | zero =>
    have ⟨_, _⟩ := hm
    interval_cases m
    rw [Nat.digits_of_lt 10 1 Nat.one_ne_zero (by decide)]
    exact List.mem_singleton_self _
  | succ k ih =>
    rw [Set.mem_Ico] at hm
    rw [Nat.digits_def' (by decide) (by omega)]
    exact List.mem_cons_of_mem _ <| @ih (m/10) (by grind)

lemma digits_last_mem {m k : ℕ} (h1 : 0 < m) (h2 : 10 ^ k ≤ m) (h3 : m / 10 ^ k < 10) : m / (10 ^ k) ∈ Nat.digits 10 m := by
  induction k generalizing m with
  | zero =>
    simp only [pow_zero, Nat.div_one]
    rw [Nat.digits_def' (by decide) h1]
    rw [Nat.mod_eq_of_lt (by omega)]
    exact List.mem_cons_self
  | succ k ih =>
    rw [Nat.digits_def' (by decide) h1]
    refine List.mem_cons_of_mem _ ?_
    rw [pow_succ', ← Nat.div_div_eq_div_mul]
    exact @ih (m / 10) (by grind) (by omega)
      (by rwa [Nat.div_div_eq_div_mul, ← pow_succ'])

-- lemma digits_last_mem₃ {a k : ℕ} : Nat.digits 10 (a % 10 ^ k) ++ [a / 10 ^ k % 10] = Nat.digits 10 (a % 10 ^ (k + 1)) := by
--   induction k with
--   | zero =>
--     wlog! w : a % 10 ≠ 0
--     simp
--     simp [Nat.mod_one]
--     rw [Nat.digits_of_lt 10 (a % 10) ?_ (show a % 10 < 10 by omega)]
--     sorry
--   | succ => sorry

-- lemma digits_div_subset' (a k : ℕ) : Nat.digits 10 (a % 10 ^ (k + 1)) <+: Nat.digits 10 a := by
--   wlog! h : a % 10 ^ (k + 1) ≠ 0
--   · simp [h]
--   induction k with
--   | zero =>
--     rw [Nat.digits_def']
--     simp [Nat.mod_one]
--   | succ k ih =>
--     rw [ih]

--     nth_rw 2 [Nat.digits_def' (by decide)]
--     rw [List.append_cons]
--     rw [Nat.div_div_eq_div_mul, ← pow_succ]
--     rw [List.append_left_inj]
--     sorry

lemma digits_div_subset (a k : ℕ) : Nat.digits 10 (a % 10 ^ (k + 1)) ⊆ Nat.digits 10 a := by
  wlog! h : a % 10 ^ (k + 1) ≠ 0
  · simp [h]
  induction k with
  | zero =>
    rw [Nat.digits_def' (by decide) (by omega)]
    simp
    rw [Nat.digits_def' (by decide) (by omega)]
    exact List.mem_cons_self
  | succ k ih =>
    specialize ih sorry
    rw [Nat.digits_def' (by decide)]
    refine List.cons_subset.mpr ⟨?_, ?_⟩
    rw [Nat.mod_mod_of_dvd]

    rw [Nat.digits_def' (by decide)]
    · exact List.mem_cons_self
    · rw [Nat.ne_zero_iff_zero_lt] at h
      cases a
      · simp at h
      · simp
    · exact dvd_of_mul_left_eq _ rfl

    nth_rw 2 [Nat.digits_def' (by decide)]
    refine List.subset_cons_of_subset (a % 10) ?_

    convert ih
    rw [@Nat.mod_pow_succ]
    rw [Nat.digits_def' (by decide)] at ih
    all_goals sorry

lemma solitary_form (k : ℕ) : is_solitary (2 * 10 ^ k - 1) := by
  refine ⟨by grind, fun a b h => ?_⟩
  wlog! w : b ≤ a
  · exact this k b a (by rwa [add_comm]) w.le |>.symm
  have : a ≤ 2 * 10 ^ k - 1 := by omega
  exact Or.inl <| digit_squeeze ⟨by omega, (Nat.le_sub_one_iff_lt <| Nat.pos_of_neZero _).mp (this)⟩

lemma solitary_one : is_solitary 1 := solitary_form 0

lemma solitary_extend (n k : ℕ) (hn1 : 0 < n) (hn2 : n < 10 ^ k) : is_solitary n ↔ is_solitary (2 * 10 ^ k + n) := by
  contrapose!
  constructor
  · intro hn hm
    unfold is_solitary at hn
    push Not at hn
    rcases hn hn1 with ⟨a, b, rfl, ha, hb⟩
    have ha' : ¬ has_digit_one (a + 2 * 10 ^ k) := by
      have h : (Nat.digits 10 a).length ≤ k := (Nat.digits_length_le_iff (by decide) a).mpr (by omega)
      rcases Nat.exists_eq_add_of_le h with ⟨l, hl⟩
      rw [mul_comm, has_digit_one, hl, ← Nat.digits_append_zeroes_append_digits (by decide) zero_lt_two]
      simpa [has_digit_one] using ha
    have := hm.2 (a + 2 * 10 ^ k) b (by omega)
    lia
  · intro hm hn
    unfold is_solitary at hm
    push Not at hm
    rcases hm <| Nat.add_pos_right _ hn1 with ⟨a, b, h, ha, hb⟩
    clear hm
    let a' := a % (10 ^ (k+1))
    let b' := b % (10 ^ (k+1))
    set x := a / (10 ^ k) with hxdef
    set y := b / (10 ^ k) with hydef
    -- In this step, AoPS claims a, b ≠ 1, but we actually want x, y ≠ 1.
    wlog! w : x ≤ y generalizing a b
    · apply this b a (by rwa [add_comm]) hb ha hydef hxdef w.le
    have : a ≤ 2 * 10 ^ k + n := by omega
    have : x ≤ 2 := calc
      _ ≤ a / 10 ^ k + b / 10 ^ k := Nat.le_add_right _ _
      _ ≤ (a + b) / 10 ^ k := Nat.div_add_div_le_add_div
      _ = (2 * 10 ^ k + n) / 10 ^ k := by rw [h]
      _ = _ := by simp [Nat.add_div, Nat.div_eq_of_lt, Nat.mod_eq_of_lt, hn2]
    have : x + y = 2 := calc a / 10 ^ k + b / 10 ^ k
      _ = (a + b) / 10 ^ k := by
        refine Eq.symm (Nat.add_div_eq_of_add_mod_lt ?_)
        sorry
      _ = (2 * 10 ^ k + n) / 10 ^ k := by rw [h]
      _ = _ := by simp [Nat.add_div, Nat.div_eq_of_lt, Nat.mod_eq_of_lt, hn2]

    interval_cases hx : x
    · have hy : y = 2 := by omega
      have := calc a' + b'
        _ = 2 * 10 ^ k + n - x * (10 ^ k) - y * (10 ^ k) := by
          simp [hx, hy]
          sorry
        _ = n := by simp [hx, hy]
      have hab := hn.2 a' b' this
      clear * - ha hb hab
      wlog ha' : has_digit_one a' generalizing a b
      · exact this b a hb ha hab.symm <| hab.resolve_left ha'
      clear * - ha' ha
      exact ha <| digits_div_subset a k ha'
    · clear hx
      absurd ha
      unfold has_digit_one
      rw [hxdef]
      refine @digits_last_mem a k ?_ ?_ (by rw [← hxdef]; decide)
      · rw [Nat.div_eq_sub_mod_div, Nat.eq_div_iff_mul_eq_left (Nat.ne_zero_of_lt hn2) (Nat.dvd_sub_mod a)] at hxdef
        omega
      · rw [← Nat.one_le_div_iff (Nat.zero_lt_of_lt hn2), hxdef]
    · omega

-- lemma nines (k a : ℕ) : a ∈ Nat.digits 10 ((10 ^ (k + 1)) - 1) ↔ a = 9 := by
--   induction k with
--   | zero => simp
--   | succ k ih =>
--     rw [Nat.digits_def' (by decide) (by grind)]
--     have (n : ℕ) : 9 = (10 ^ (n + 1 + 1) - 1) % 10 := by
--       rw [← Nat.add_mod_right, ← Nat.sub_add_comm <| Nat.one_le_pow' _ _]
--       simp [Nat.add_mod, Nat.pow_mod]
--     constructor
--     · rw [List.mem_cons]
--       rintro (h | h)
--       · rwa [this]
--       · have (n : ℕ) : (10 ^ (n + 1 + 1) - 1) / 10 = 10 ^ (n + 1) - 1 := by omega
--         rw [this] at h
--         exact ih.mp h
--     · rintro rfl
--       refine List.mem_cons.mpr <| Or.inl <| this _

lemma nines' (k : ℕ) : 10 ^ k - 1 = Nat.ofDigits 10 (List.replicate k 9) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.add_comm k 1, List.replicate_add, List.replicate_one, Nat.ofDigits_append]
    simp [← ih]
    grind

lemma chop_off_leading (m k : ℕ) (hm : m ∈ Finset.Ico (10 ^ k) (10 ^ (k + 1)))
    : m = Nat.ofDigits 10 ((Nat.digits 10 m).dropLast ++ [m / 10 ^ k]) := by
  rw [Finset.mem_Ico] at hm
  induction k generalizing m with
  | zero =>
    rw [Nat.digits_of_lt 10 m (by omega) (by omega)]
    simp
  | succ k ih =>
    rw [Nat.digits_def' (by decide) (by omega)]
    rw [List.dropLast_cons_of_ne_nil ?_]
    on_goal 2 =>
      refine Nat.digits_ne_nil_iff_ne_zero.mpr ?_
      omega
    rw [List.cons_append]
    rw [Nat.ofDigits_cons]
    specialize ih (m / 10) (by omega)
    rw [Nat.div_div_eq_div_mul, ← Nat.pow_add_one'] at ih
    rw [← ih]
    omega

abbrev correction (m k : ℕ) :=
  Nat.digits 10 (m - (10 ^ k - 1)) |>.take k |>.map (if · = 1 then 1 else 0) |> Nat.ofDigits 10

lemma correction_le {m k : ℕ} (hm : m ∈ Finset.Ico (10 ^ k) (10 ^ (k + 1))) : correction m k ≤ 10 ^ k - 1 := by
  cases k with
  | zero =>
    rw [Finset.mem_Ico] at hm
    rw [correction, Nat.digits_of_lt]
    · simp
    · omega
    · omega
  | succ k =>
    rw [Nat.le_sub_one_iff_lt <| Nat.pos_of_neZero _]
    calc correction m (k + 1)
      _ < 10 ^ _ :=
        Nat.ofDigits_lt_base_pow_length (by decide) (by grind)
      _ ≤ 10 ^ (k + 1) := by
        rw [Nat.pow_le_pow_iff_right (by decide), List.length_map]
        apply List.length_take_le

lemma nines_sub_correction (m k : ℕ) : Nat.ofDigits 10 (List.replicate k 9) - correction m k =
    (Nat.digits 10 (m - (10 ^ k - 1)) |>.take k |>.map (if · = 1 then 8 else 9) |> Nat.ofDigits 10) := by
  sorry

lemma nines_sub_correction_not_has_digit_one (m k : ℕ) : ¬has_digit_one (10 ^ k - 1 - correction m k) := by
  cases k with
  | zero => simp [has_digit_one]
  | succ k =>
    rw [nines', nines_sub_correction]
    simp [has_digit_one]
    rw [Nat.digits_ofDigits _ (by decide)]
    · suffices 1 ∉ List.map (fun x ↦ if x = 1 then 8 else 9) (Nat.digits 10 (m - (10 ^ (k + 1) - 1))) by
        contrapose this
        exact List.mem_of_mem_take this
      simp [List.mem_map, ite_eq_iff]
    · grind
    intro h
    rw [List.getLast_take h]
    simp [ite_eq_iff]

lemma add_correction_not_has_digit_one (m k : ℕ) : ¬has_digit_one (m - (10 ^ k - 1) + correction m k) := by
  sorry

lemma solitary_iff {m k : ℕ} (hm : m ∈ Finset.Ico (10 ^ k) (10 ^ (k + 1))) :
    is_solitary m ↔ m = 2 * 10 ^ k - 1 ∨ (∃ n ∈ Finset.Ico 1 (10 ^ k), is_solitary n ∧ m = 2 * 10 ^ k + n) := by
  constructor
  · contrapose!
    rintro ⟨hm1, hm2⟩
    rw [Finset.mem_Ico] at hm
    zify at hm1 hm2
    push_cast [Int.natCast_pred_of_pos, Nat.pos_of_neZero] at hm1
    -- by lemma 2, we know that 2 is not the leading digit of m
    intro solitary
    have m_ne : (m : ℤ) ≠ 2 * 10 ^ k := by
      norm_cast
      contrapose solitary with h
      rw [h]
      exact not_solitary_two_zeros
    have : m < 2 * 10 ^ k ∨ (3 * 10 ^ k) ≤ m := by
      contrapose! hm2
      have h2 : 1 ≤ 2 * 10 ^ k := by omega
      use m - 2 * 10 ^ k
      rw [@solitary_extend _ k, Finset.mem_Ico]
      · zify [h2] at hm2
        zify [hm2.left, h2]
        rw [Nat.add_sub_of_le (by exact_mod_cast hm2.left)]
        simp [solitary]
        omega
      · rw [@Nat.sub_pos_iff_lt]
        zify at hm2 ⊢
        exact hm2.left.lt_of_ne m_ne.symm
      · zify [hm2.left] at hm2 ⊢; omega
    -- move inequalities to b
    replace : m - (10 ^ k - 1) < 10 ^ k ∨ 2 * 10 ^ k < m - (10 ^ k - 1) := by
      contrapose! this
      constructor
      · have h1 : 10 ^ k - 1 ≤ m := by omega
        have h2 : 1 ≤ 10 ^ k := by omega
        zify [h1, h2] at this ⊢
        omega
      · omega
    -- nudge all ones in b by taking from a
    set corr := correction m k with hc
    absurd solitary
    unfold is_solitary
    push Not
    intro _
    use 10 ^ k - 1 - corr, m - (10 ^ k - 1) + corr
    and_intros
    · rw [Nat.add_left_comm, Nat.sub_add_cancel ?_, Nat.sub_add_cancel (by omega)]
      rw [← Finset.mem_Ico] at hm
      exact correction_le hm
    · exact nines_sub_correction_not_has_digit_one m k
    · exact add_correction_not_has_digit_one m k
  · simp only [Finset.mem_Ico]
    rintro (rfl | ⟨n, ⟨npos, hnk⟩, hn, rfl⟩)
    · exact solitary_form k
    · exact solitary_extend n k npos hnk |>.mp hn

lemma solitary_count (k : ℕ) : Finset.card { x ∈ (Finset.Ico 1 (10^k)) | is_solitary x } = 2 ^ k - 1 := by
  -- #count_heartbeats! 1 in -- 10333
  induction k with
  | zero => simp
  | succ k ih =>
    -- this should really be a calc block...
    have : { x ∈ (Finset.Ico 1 (10^(k + 1))) | is_solitary x }
        = { x ∈ (Finset.Ico 1 (10^k)) | is_solitary x } ∪ { x ∈ (Finset.Ico (10^k) (10^(k+1))) | is_solitary x } := by
      rw [← Finset.filter_union, Finset.Ico_union_Ico_eq_Ico]
      · grind
      · exact Nat.pow_le_pow_right (by decide) (Nat.le_succ _)
    rw [this, Finset.card_union_of_disjoint <| Finset.disjoint_filter_filter <| Finset.Ico_disjoint_Ico_consecutive _ _ _]
    have : {x ∈ Finset.Ico (10 ^ k) (10 ^ (k + 1)) | is_solitary x} =
        {2 * 10 ^ k - 1} ∪ { m ∈ Finset.Ico (10 ^ k) (10 ^ (k + 1)) | ∃ n ∈ Finset.Ico 1 (10 ^ k), is_solitary n ∧ m = 2 * 10 ^ k + n }
          := by
      ext m
      simp only [Finset.mem_filter, Finset.singleton_union, Finset.mem_insert]
      constructor
      · rintro ⟨hm, hm2⟩
        rw [solitary_iff hm] at hm2
        simpa [hm] using hm2
      · rintro (rfl | ⟨hm, hm2⟩)
        · grind [solitary_form]
        · simp [solitary_iff hm, ↓hm2, hm]
    rw [this, Finset.card_union_of_disjoint (by simp; omega)]
    have : { x ∈ (Finset.Ico 1 (10^k)) | is_solitary x }.card
        = {m ∈ Finset.Ico (10 ^ k) (10 ^ (k + 1)) | ∃ n ∈ Finset.Ico 1 (10 ^ k), is_solitary n ∧ m = 2 * 10 ^ k + n}.card := by
      refine Finset.card_nbij (2 * 10 ^ k + ·) (by intro n; grind) (by simp) (by intro a; simp; grind)
    rw [← this, ih, Finset.card_singleton]
    grind

snip end

problem usa2026_p4 :
    (Finset.filter is_solitary (Finset.Ico 1 (10^2026))).card = solution := by
  apply solitary_count

end Usa2026P4
