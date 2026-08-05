/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.Ring
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics] }

/-!
# USA Mathematical Olympiad 2024, Problem 4

Let m and n be positive integers. A circular necklace contains mn beads, each
either red or blue. It turned out that no matter how the necklace was cut into
m blocks of n consecutive beads, each block had a distinct number of red beads.
Determine, with proof, all possible values of the ordered pair (m, n).
-/

namespace Usa2024P4

/-- A circular necklace with `m * n` beads, each red (`true`) or blue (`false`).
The beads are indexed by their position on the circle, i.e. by `ZMod (m * n)`. -/
abbrev Necklace (m n : ℕ) := ZMod (m * n) → Bool

/-- The number of red beads in the block of `n` consecutive beads starting at
position `s + i * n` (positions are taken modulo `m * n`). -/
def blockCount {m n : ℕ} (c : Necklace m n) (s : ZMod (m * n)) (i : ℕ) : ℕ :=
  ∑ j ∈ Finset.range n, if c (s + ((i * n + j : ℕ) : ZMod (m * n))) then 1 else 0

/-- The property from the problem statement: no matter how the necklace is cut
into `m` blocks of `n` consecutive beads (the cut is determined by the starting
position `s` of the first block), the numbers of red beads in the `m` blocks
are pairwise distinct. -/
def AllCutsDistinct {m n : ℕ} (c : Necklace m n) : Prop :=
  ∀ s : ZMod (m * n), Function.Injective (fun i : Fin m ↦ blockCount c s i.val)

snip begin

/-- Each block contains `n` beads, so its red bead count is at most `n`. -/
lemma blockCount_le {m n : ℕ} (c : Necklace m n) (s : ZMod (m * n)) (i : ℕ) :
    blockCount c s i ≤ n := by
  unfold blockCount
  calc (∑ j ∈ Finset.range n, if c (s + ((i * n + j : ℕ) : ZMod (m * n))) then 1 else 0)
      ≤ ∑ j ∈ Finset.range n, 1 := by
        apply Finset.sum_le_sum
        intro j _
        split <;> simp
    _ = n := by simp

/-- Necessity: the `m` distinct block counts all lie in `{0, 1, ..., n}`,
which has only `n + 1` elements. -/
lemma le_of_allCutsDistinct {m n : ℕ} {c : Necklace m n} (hc : AllCutsDistinct c) :
    m ≤ n + 1 := by
  have hinj := hc 0
  have hsub : Finset.univ.image (fun i : Fin m ↦ blockCount c 0 i.val) ⊆
      Finset.range (n + 1) := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨i, -, rfl⟩ := hx
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (blockCount_le c 0 i.val)
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin,
    Finset.card_range] at hcard
  exact hcard

/-- The red indicator of the unfolded construction: writing `p = q * n + j`
with `j < n` (so `q` is the row and `j` the column of bead `p`), the bead is
red iff `n + 1 - m ≤ j < n - q`. -/
def rowRed (m n : ℕ) (p : ℕ) : ℕ :=
  if n + 1 - m ≤ p % n ∧ p % n + p / n < n then 1 else 0

/-- Evaluating `rowRed` on the bead `t * n + a` in row `t`, column `a`. -/
lemma rowRed_eq {m n : ℕ} (hn : 0 < n) (t a : ℕ) (ha : a < n) :
    rowRed m n (t * n + a) = if n + 1 - m ≤ a ∧ a + t < n then 1 else 0 := by
  unfold rowRed
  have h1 : (t * n + a) % n = a := by
    rw [show t * n + a = a + n * t by ring, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt ha]
  have h2 : (t * n + a) / n = t := by
    rw [show t * n + a = a + n * t by ring, Nat.add_mul_div_left _ _ hn,
      Nat.div_eq_of_lt ha, Nat.zero_add]
  rw [h1, h2]

/-- Evaluating `rowRed` on a bead in row `0`. -/
lemma rowRed_self {m n j : ℕ} (hj : j < n) :
    rowRed m n j = if n + 1 - m ≤ j then 1 else 0 := by
  unfold rowRed
  rw [Nat.mod_eq_of_lt hj, Nat.div_eq_of_lt hj]
  simp only [Nat.add_zero, hj, and_true]

/-- The necklace constructed for the `m ≤ n + 1` direction: writing
`p = q * n + j` with `j < n`, bead `p` is red iff `n + 1 - m ≤ j < n - q`. -/
def constr (m n : ℕ) : Necklace m n :=
  fun p ↦ decide (n + 1 - m ≤ p.val % n ∧ p.val % n + p.val / n < n)

/-- Bridging lemma: the block count of the constructed necklace can be computed
with natural number arithmetic; the modulo `m * n` on the indices keeps track
of the wrap-around of the circle. -/
lemma blockCount_constr_eq {m n : ℕ} (s' t : ℕ) :
    blockCount (constr m n) ((s' : ℕ) : ZMod (m * n)) t =
      ∑ j ∈ Finset.range n, rowRed m n ((s' + t * n + j) % (m * n)) := by
  unfold blockCount
  apply Finset.sum_congr rfl
  intro j _
  rw [show ((s' : ℕ) : ZMod (m * n)) + ((t * n + j : ℕ) : ZMod (m * n)) =
      ((s' + t * n + j : ℕ) : ZMod (m * n)) by push_cast; ring]
  simp only [constr, rowRed, ZMod.val_natCast, decide_eq_true_eq]

/-- The key counting lemma: for a cut starting at `s' < n`, the number of red
beads in block `t` (interpreted without wrap-around) is
`m - 1 - t` if `s' + t < n` and `m - 2 - t` otherwise. -/
lemma sum_rowRed {m n : ℕ} (hn : 0 < n) (hmn : m ≤ n + 1) {s' t : ℕ}
    (hs : s' < n) :
    (∑ j ∈ Finset.range n, rowRed m n (s' + t * n + j)) =
      if s' + t < n then m - 1 - t else m - 2 - t := by
  have e := Finset.sum_range_add (fun j ↦ rowRed m n (s' + t * n + j)) (n - s') s'
  rw [Nat.sub_add_cancel (Nat.le_of_lt hs)] at e
  rw [e]
  -- the first `n - s'` beads lie in row `t`, columns `s'` to `n - 1`
  have h1 : (∑ j ∈ Finset.range (n - s'), rowRed m n (s' + t * n + j)) =
      n - t - max s' (n + 1 - m) := by
    have step : (∑ j ∈ Finset.range (n - s'), rowRed m n (s' + t * n + j)) =
        ∑ j ∈ Finset.range (n - s'),
          (if n + 1 - m ≤ s' + j ∧ s' + j + t < n then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_range] at hj
      rw [show s' + t * n + j = t * n + (s' + j) by ring,
        rowRed_eq hn t (s' + j) (by omega)]
    rw [step]
    have hico := Finset.sum_Ico_eq_sum_range
      (f := fun u ↦ if n + 1 - m ≤ u ∧ u + t < n then 1 else 0) s' n
    rw [← hico, ← Finset.card_filter]
    have hfilter : (Finset.Ico s' n).filter (fun u ↦ n + 1 - m ≤ u ∧ u + t < n) =
        Finset.Ico (max s' (n + 1 - m)) (n - t) := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_Ico]
      omega
    rw [hfilter, Nat.card_Ico]
  -- the last `s'` beads lie in row `t + 1`, columns `0` to `s' - 1`
  have h2 : (∑ j ∈ Finset.range s', rowRed m n (s' + t * n + (n - s' + j))) =
      min s' (n - t - 1) - (n + 1 - m) := by
    have step : (∑ j ∈ Finset.range s', rowRed m n (s' + t * n + (n - s' + j))) =
        ∑ j ∈ Finset.range s',
          (if n + 1 - m ≤ j ∧ j + (t + 1) < n then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_range] at hj
      rw [show s' + t * n + (n - s' + j) = (t + 1) * n + j by
        rw [add_mul, one_mul]; omega, rowRed_eq hn (t + 1) j (by omega)]
    rw [step, ← Finset.card_filter]
    have hfilter : (Finset.range s').filter (fun j ↦ n + 1 - m ≤ j ∧ j + (t + 1) < n) =
        Finset.Ico (n + 1 - m) (min s' (n - t - 1)) := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      omega
    rw [hfilter, Nat.card_Ico]
  rw [h1, h2]
  split_ifs with h <;> omega

/-- The last block (which wraps around the end of the necklace) contains
exactly `s' - (n + 1 - m)` red beads: its first `n - s'` beads lie in row
`m - 1` (which is entirely blue) and its last `s'` beads lie in row `0`. -/
lemma sum_rowRed_last {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : m ≤ n + 1) {s' : ℕ}
    (hs : s' < n) :
    (∑ j ∈ Finset.range n, rowRed m n ((s' + (m - 1) * n + j) % (m * n))) =
      s' - (n + 1 - m) := by
  have hmn' : (m - 1) * n + n = m * n := by
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    rw [Nat.add_sub_cancel, Nat.succ_mul]
  have e := Finset.sum_range_add
    (fun j ↦ rowRed m n ((s' + (m - 1) * n + j) % (m * n))) (n - s') s'
  rw [Nat.sub_add_cancel (Nat.le_of_lt hs)] at e
  rw [e]
  -- the first `n - s'` beads lie in row `m - 1`, which has no red beads
  have h1 : (∑ j ∈ Finset.range (n - s'),
      rowRed m n ((s' + (m - 1) * n + j) % (m * n))) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [Finset.mem_range] at hj
    have hlt : s' + (m - 1) * n + j < m * n := by
      have hsj : s' + j < n := by omega
      have h' := add_lt_add_left hsj ((m - 1) * n)
      omega
    rw [Nat.mod_eq_of_lt hlt, show s' + (m - 1) * n + j = (m - 1) * n + (s' + j) by ring,
      rowRed_eq hn (m - 1) (s' + j) (by omega), if_neg (by omega)]
  -- the last `s'` beads wrap around into row `0`, columns `0` to `s' - 1`
  have h2 : (∑ j ∈ Finset.range s',
      rowRed m n ((s' + (m - 1) * n + (n - s' + j)) % (m * n))) = s' - (n + 1 - m) := by
    have step : ∀ j ∈ Finset.range s',
        rowRed m n ((s' + (m - 1) * n + (n - s' + j)) % (m * n)) =
          if n + 1 - m ≤ j then 1 else 0 := by
      intro j hj
      rw [Finset.mem_range] at hj
      have e1 : s' + (m - 1) * n + (n - s' + j) = m * n + j := by
        have hle : s' ≤ n := Nat.le_of_lt hs
        calc s' + (m - 1) * n + (n - s' + j) = (m - 1) * n + n + j := by omega
          _ = m * n + j := by rw [hmn']
      rw [e1, Nat.add_comm (m * n) j, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by
          have hle : n ≤ m * n := Nat.le_mul_of_pos_left n hm
          omega),
        rowRed_self (by omega : j < n)]
    rw [Finset.sum_congr rfl step, ← Finset.card_filter]
    have hfilter : (Finset.range s').filter (fun j ↦ n + 1 - m ≤ j) =
        Finset.Ico (n + 1 - m) s' := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      omega
    rw [hfilter, Nat.card_Ico]
  rw [h1, h2, Nat.zero_add]

/-- The complete formula for the block counts of the constructed necklace
when the cut starts at `s' < n`. -/
lemma blockCount_constr {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : m ≤ n + 1) {s' t : ℕ}
    (hs : s' < n) (ht : t < m) :
    blockCount (constr m n) ((s' : ℕ) : ZMod (m * n)) t =
      if t = m - 1 then s' - (n + 1 - m)
      else if s' + t < n then m - 1 - t else m - 2 - t := by
  rw [blockCount_constr_eq s' t]
  by_cases hlast : t = m - 1
  · subst hlast
    rw [if_pos rfl]
    exact sum_rowRed_last hm hn hmn hs
  · rw [if_neg hlast]
    have hlt : ∀ j ∈ Finset.range n, s' + t * n + j < m * n := by
      intro j hj
      rw [Finset.mem_range] at hj
      have hle : (t + 2) * n ≤ m * n := by
        have h : t + 2 ≤ m := by omega
        exact mul_le_mul_of_nonneg_right h (Nat.zero_le n)
      calc s' + t * n + j < t * n + 2 * n := by omega
        _ = (t + 2) * n := by rw [add_mul]
        _ ≤ m * n := hle
    have step : (∑ j ∈ Finset.range n, rowRed m n ((s' + t * n + j) % (m * n))) =
        ∑ j ∈ Finset.range n, rowRed m n (s' + t * n + j) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Nat.mod_eq_of_lt (hlt j hj)]
    rw [step]
    exact sum_rowRed hn hmn hs

/-- The block count is periodic in the block index with period `m`. -/
lemma blockCount_add_period {m n : ℕ} (c : Necklace m n) (s : ZMod (m * n)) (i : ℕ) :
    blockCount c s (i + m) = blockCount c s i := by
  unfold blockCount
  apply Finset.sum_congr rfl
  intro j _
  have e : (((i + m) * n + j : ℕ) : ZMod (m * n)) = ((i * n + j : ℕ) : ZMod (m * n)) := by
    have h : (i + m) * n + j = i * n + j + m * n := by ring
    rw [h, Nat.cast_add, ZMod.natCast_self, add_zero]
  rw [e]

/-- Iterated version of `blockCount_add_period`. -/
lemma blockCount_add_mul {m n : ℕ} (c : Necklace m n) (s : ZMod (m * n)) (i q : ℕ) :
    blockCount c s (i + m * q) = blockCount c s i := by
  induction q with
  | zero => simp
  | succ q ih =>
    have h : i + m * (q + 1) = (i + m * q) + m := by ring
    rw [h, blockCount_add_period c s (i + m * q), ih]

/-- The block count only depends on the block index modulo `m`. -/
lemma blockCount_mod {m n : ℕ} (c : Necklace m n) (s : ZMod (m * n)) (x : ℕ) :
    blockCount c s x = blockCount c s (x % m) := by
  conv_lhs => rw [← Nat.mod_add_div x m]
  exact blockCount_add_mul c s (x % m) (x / m)

/-- Shifting the starting position of the cut by `n` beads shifts the blocks
by one. This reduces a general cut `s` to a cut starting at `s.val % n < n`. -/
lemma blockCount_shift {m n : ℕ} [NeZero (m * n)] (c : Necklace m n)
    (s : ZMod (m * n)) (i : ℕ) :
    blockCount c s i =
      blockCount c ((s.val % n : ℕ) : ZMod (m * n)) (s.val / n + i) := by
  unfold blockCount
  apply Finset.sum_congr rfl
  intro j _
  have e : s + ((i * n + j : ℕ) : ZMod (m * n)) =
      ((s.val % n : ℕ) : ZMod (m * n)) + (((s.val / n + i) * n + j : ℕ) : ZMod (m * n)) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val s, ← Nat.cast_add]
    rw [← Nat.cast_add]
    congr 1
    conv_lhs => rw [← Nat.mod_add_div s.val n]
    ring
  rw [e]

/-- The constructed necklace satisfies the property of the problem. -/
lemma allCutsDistinct_constr {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : m ≤ n + 1) :
    AllCutsDistinct (constr m n) := by
  have : NeZero (m * n) := ⟨(Nat.mul_pos hm hn).ne'⟩
  intro s i₁ i₂ hij
  have hij' : blockCount (constr m n) s i₁.val =
      blockCount (constr m n) s i₂.val := hij
  rw [blockCount_shift _ s i₁.val, blockCount_shift _ s i₂.val,
    blockCount_mod _ _ (s.val / n + i₁.val),
    blockCount_mod _ _ (s.val / n + i₂.val)] at hij'
  have hs' : s.val % n < n := Nat.mod_lt s.val hn
  have hr1 : (s.val / n + i₁.val) % m < m := Nat.mod_lt _ hm
  have hr2 : (s.val / n + i₂.val) % m < m := Nat.mod_lt _ hm
  rw [blockCount_constr hm hn hmn hs' hr1, blockCount_constr hm hn hmn hs' hr2] at hij'
  -- the explicit formula now forces the two shifted block indices to coincide
  have hval : (s.val / n + i₁.val) % m = (s.val / n + i₂.val) % m := by
    split_ifs at hij' <;> omega
  have hz : ((s.val / n + i₁.val : ℕ) : ZMod m) = ((s.val / n + i₂.val : ℕ) : ZMod m) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mpr hval
  push_cast at hz
  have h3 : (i₁.val : ZMod m) = (i₂.val : ZMod m) := add_left_cancel hz
  have h4 : i₁.val ≡ i₂.val [MOD m] := (ZMod.natCast_eq_natCast_iff _ _ _).mp h3
  have h5 : i₁.val % m = i₂.val % m := h4
  rw [Nat.mod_eq_of_lt i₁.isLt, Nat.mod_eq_of_lt i₂.isLt] at h5
  exact Fin.ext h5

snip end

/-- The answer: the required necklaces exist exactly for the pairs `(m, n)`
with `m ≤ n + 1`. -/
determine solution : ℕ → ℕ → Prop := fun m n ↦ m ≤ n + 1

problem usa2024_p4 (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    (∃ c : Necklace m n, AllCutsDistinct c) ↔ solution m n := by
  constructor
  · rintro ⟨c, hc⟩
    exact le_of_allCutsDistinct hc
  · intro h
    exact ⟨constr m n, allCutsDistinct_constr hm hn h⟩

end Usa2024P4
