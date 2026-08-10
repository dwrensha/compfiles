/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Tactic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Combinatorics.Hall.Basic
public import Mathlib.Data.Int.ConditionallyCompleteOrder
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.Ring.Basic
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics] }

/-!
# USA Mathematical Olympiad 2025, Problem 6

Let `m` and `n` be positive integers with `m ≥ n`. There are `m` cupcakes of different
flavors arranged around a circle and `n` people who like cupcakes. Each person assigns
a nonnegative real number score to each cupcake, depending on how much they like the
cupcake. Suppose that for each person `P`, it is possible to partition the circle of
`m` cupcakes into `n` groups of consecutive cupcakes so that the sum of `P`'s scores
of the cupcakes in each group is at least 1. Prove that it is possible to distribute
the `m` cupcakes to the `n` people so that each person `P` receives cupcakes of total
score at least 1 with respect to `P`.
-/

namespace Usa2025P6

/-!
## Circular partitions

The circle of `m` cupcakes is modeled by `ZMod m`; arcs are intervals of consecutive
cupcakes and a `CirclePartition` is a partition of the circle into such arcs.
-/

/-- An arc of length `l` starting at `c` on the circle `ZMod m`. -/
def arcSet {m : ℕ} (c : ZMod m) (l : ℕ) : Finset (ZMod m) :=
  (Finset.range l).image (fun t : ℕ => c + (t : ZMod m))


/-- A partition of the circle `ZMod m` into `k` consecutive nonempty arcs,
described by a basepoint and the list of arc lengths. -/
structure CirclePartition (m k : ℕ) where
  base : ZMod m
  len : Fin k → ℕ
  len_pos : ∀ i, 1 ≤ len i
  len_sum : ∑ i, len i = m


namespace CirclePartition

variable {m k : ℕ} (P : CirclePartition m k)

/-- The offset of arc `i`: total length of the preceding arcs. -/
def off (i : Fin k) : ℕ := ∑ j ∈ Finset.univ.filter (· < i), P.len j

/-- The starting point of arc `i`. -/
def start (i : Fin k) : ZMod m := P.base + (P.off i : ZMod m)

/-- The `i`-th arc as a finset. -/
def arcOf (i : Fin k) : Finset (ZMod m) := arcSet (P.start i) (P.len i)


end CirclePartition

snip begin

namespace CirclePartition

variable {m k : ℕ} (P : CirclePartition m k)

lemma mem_arcSet {m : ℕ} {c : ZMod m} {l : ℕ} {x : ZMod m} :
    x ∈ arcSet c l ↔ ∃ t : ℕ, t < l ∧ c + (t : ZMod m) = x := by
  simp [arcSet]

lemma natCast_injective_of_lt {m : ℕ} [NeZero m] {t₁ t₂ : ℕ} (h₁ : t₁ < m) (h₂ : t₂ < m)
    (h : (t₁ : ZMod m) = (t₂ : ZMod m)) : t₁ = t₂ := by
  rw [ZMod.natCast_eq_natCast_iff] at h
  rwa [Nat.ModEq, Nat.mod_eq_of_lt h₁, Nat.mod_eq_of_lt h₂] at h

lemma arcSet_card {m : ℕ} [NeZero m] {c : ZMod m} {l : ℕ} (hl : l ≤ m) :
    (arcSet c l).card = l := by
  rw [arcSet, Finset.card_image_of_injOn, Finset.card_range]
  intro t₁ ht₁ t₂ ht₂ h
  rw [Finset.mem_coe, Finset.mem_range] at ht₁ ht₂
  simp only [add_left_cancel_iff] at h
  exact natCast_injective_of_lt (by omega) (by omega) h

lemma sum_arcSet {m : ℕ} [NeZero m] {c : ZMod m} {l : ℕ} (hl : l ≤ m) (w : ZMod m → ℝ) :
    ∑ x ∈ arcSet c l, w x = ∑ t ∈ Finset.range l, w (c + (t : ZMod m)) := by
  rw [arcSet, Finset.sum_image]
  intro t₁ ht₁ t₂ ht₂ h
  rw [Finset.mem_coe, Finset.mem_range] at ht₁ ht₂
  simp only [add_left_cancel_iff] at h
  exact natCast_injective_of_lt (by omega) (by omega) h

lemma arcSet_univ {m : ℕ} [NeZero m] {c : ZMod m} :
    arcSet c m = Finset.univ := by
  apply Finset.eq_univ_of_card
  rw [arcSet_card le_rfl, ZMod.card]

lemma k_pos (P : CirclePartition m k) (hm : 0 < m) : 0 < k := by
  by_contra h
  push Not at h
  replace h : k = 0 := Nat.eq_zero_of_le_zero h
  have e : (Finset.univ : Finset (Fin k)) = ∅ := by
    rw [h]
    exact Finset.univ_eq_empty
  have hsum := P.len_sum
  rw [e, Finset.sum_empty] at hsum
  omega

/-- Periodic extension of the offsets: the total length of the first `a` arcs
(going around the circle repeatedly). -/
def offExt (hk : 0 < k) (a : ℕ) : ℕ :=
  ∑ i ∈ Finset.range a, P.len ⟨i % k, Nat.mod_lt i hk⟩


/-- Helper: evaluating the periodic length at an explicitly given index. -/
lemma len_congr (hk : 0 < k) {a : ℕ} {j : Fin k} (h : a % k = j.val) :
    P.len ⟨a % k, Nat.mod_lt a hk⟩ = P.len j :=
  congr_arg P.len (Fin.ext h)

lemma offExt_zero (hk : 0 < k) : P.offExt hk 0 = 0 := by simp [offExt]

lemma offExt_succ (hk : 0 < k) (a : ℕ) :
    P.offExt hk (a + 1) = P.offExt hk a + P.len ⟨a % k, Nat.mod_lt a hk⟩ := by
  simp [offExt, Finset.sum_range_succ]

lemma off_eq_offExt (hk : 0 < k) (i : Fin k) : P.off i = P.offExt hk i.val := by
  rw [off, offExt]
  apply Finset.sum_bij (fun a _ => a.val)
  · intro a ha
    rw [Finset.mem_filter] at ha
    rw [Finset.mem_range]
    exact ha.2
  · intro a₁ _ a₂ _ h
    exact Fin.ext h
  · intro b hb
    rw [Finset.mem_range] at hb
    refine ⟨⟨b, by omega⟩, ?_, rfl⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by rw [Fin.lt_def]; exact hb⟩
  · intro a ha
    rw [Finset.mem_filter] at ha
    have hlt : a.val < k := by
      have := i.isLt
      rw [Fin.lt_def] at ha
      omega
    exact (len_congr P hk (Nat.mod_eq_of_lt hlt)).symm

lemma offExt_k (hk : 0 < k) : P.offExt hk k = m := by
  have h : ∑ i ∈ Finset.range k, P.len ⟨i % k, Nat.mod_lt i hk⟩ = ∑ i : Fin k, P.len i := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => P.len ⟨i % k, Nat.mod_lt i hk⟩) k]
    apply Finset.sum_congr rfl
    intro i _
    exact len_congr P hk (Nat.mod_eq_of_lt i.isLt)
  rw [offExt, h, P.len_sum]

lemma offExt_add_period (hk : 0 < k) (a : ℕ) :
    P.offExt hk (a + k) = P.offExt hk a + m := by
  induction a with
  | zero => simp [offExt_zero, offExt_k]
  | succ a ih =>
    have e : P.len ⟨(a + k) % k, Nat.mod_lt (a + k) hk⟩ = P.len ⟨a % k, Nat.mod_lt a hk⟩ :=
      len_congr P hk (Nat.add_mod_right a k)
    rw [show a + 1 + k = (a + k) + 1 by omega, offExt_succ, e, ih, offExt_succ]
    ring

lemma offExt_mono (hk : 0 < k) {a b : ℕ} (h : a ≤ b) : P.offExt hk a ≤ P.offExt hk b := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le h
  induction c with
  | zero => simp
  | succ c ih =>
    rw [Nat.add_succ, offExt_succ]
    have hpos := P.len_pos ⟨(a + c) % k, Nat.mod_lt (a + c) hk⟩
    omega

lemma offExt_lt_succ (hk : 0 < k) (a : ℕ) : P.offExt hk a < P.offExt hk (a + 1) := by
  rw [offExt_succ]
  have := P.len_pos ⟨a % k, Nat.mod_lt a hk⟩
  omega

/-- The periodic weight function on `ℕ` associated to a score function. -/
def perW (w : ZMod m → ℝ) (t : ℕ) : ℝ := w (P.base + (t : ZMod m))

lemma perW_periodic (w : ZMod m → ℝ) (t : ℕ) : P.perW w (t + m) = P.perW w t := by
  rw [perW, perW, Nat.cast_add, ZMod.natCast_self, add_zero]

lemma offExt_succ_fin (hk : 0 < k) (i : Fin k) :
    P.offExt hk (i.val + 1) = P.off i + P.len i := by
  rw [offExt_succ, off_eq_offExt P hk]
  congr 1
  exact len_congr P hk (Nat.mod_eq_of_lt i.isLt)

lemma off_add_len_le (hk : 0 < k) (i : Fin k) : P.off i + P.len i ≤ m := by
  rw [← offExt_succ_fin P hk]
  have h := P.offExt_mono hk i.isLt
  rwa [offExt_k] at h

lemma len_le (hk : 0 < k) (i : Fin k) : P.len i ≤ m :=
  le_trans (Nat.le_add_left _ _) (P.off_add_len_le hk i)

lemma offExt_strictMono (hk : 0 < k) : StrictMono (P.offExt hk) := by
  intro a b h
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_lt h
  clear h
  have step : ∀ d, P.offExt hk (a + d) < P.offExt hk (a + d + 1) := fun d => by
    rw [offExt_succ]
    have hpos := P.len_pos ⟨(a + d) % k, Nat.mod_lt (a + d) hk⟩
    omega
  induction c with
  | zero => simpa using step 0
  | succ c ih =>
    have h2 := step (c + 1)
    rw [show a + (c + 1) = a + c + 1 by omega] at h2 ⊢
    omega

lemma off_le_off (hk : 0 < k) {i j : Fin k} (h : i ≤ j) : P.off i ≤ P.off j := by
  rw [off_eq_offExt, off_eq_offExt]
  exact P.offExt_mono hk (by rw [Fin.le_def] at h; exact h)

lemma off_add_len_le_off (hk : 0 < k) {i j : Fin k} (h : i ≤ j) :
    P.off i + P.len i ≤ P.off j + P.len j := by
  rw [← offExt_succ_fin, ← offExt_succ_fin]
  exact P.offExt_mono hk (by rw [Fin.le_def] at h; omega)

/-- Every position in `[0, m)` lies in a unique arc interval; existence part. -/
lemma exists_Ico_of_mono {off : ℕ → ℕ} {K p : ℕ} (h0 : off 0 ≤ p) (hp : p < off K) :
    ∃ j < K, off j ≤ p ∧ p < off (j + 1) := by
  induction K with
  | zero => omega
  | succ K ih =>
    by_cases h : p < off K
    · obtain ⟨j, hj, hj1, hj2⟩ := ih h
      exact ⟨j, Nat.lt_succ_of_lt hj, hj1, hj2⟩
    · exact ⟨K, Nat.lt_succ_self _, by omega, by omega⟩

/-- The position of a point relative to the basepoint. -/
def pos (x : ZMod m) : ℕ := (x - P.base).val

lemma base_add_pos [NeZero m] (x : ZMod m) :
    P.base + (P.pos x : ZMod m) = x := by
  rw [pos, ZMod.natCast_val, ZMod.cast_id]
  abel

lemma pos_start_add (hk : 0 < k) [NeZero m] (i : Fin k) {t : ℕ} (ht : t < P.len i) :
    P.pos (P.start i + (t : ZMod m)) = P.off i + t := by
  have h1 : P.start i + (t : ZMod m) - P.base = ((P.off i + t : ℕ) : ZMod m) := by
    rw [start, Nat.cast_add]
    abel
  rw [pos, h1, ZMod.val_natCast, Nat.mod_eq_of_lt (by
    have := P.off_add_len_le hk i
    omega)]

lemma arcOf_cover (hk : 0 < k) [NeZero m] (x : ZMod m) :
    ∃ i : Fin k, x ∈ P.arcOf i := by
  obtain ⟨j, hjk, hj1, hj2⟩ := exists_Ico_of_mono (off := P.offExt hk) (K := k) (p := P.pos x)
    (by rw [offExt_zero]; exact Nat.zero_le _)
    (by rw [offExt_k]; exact ZMod.val_lt (x - P.base))
  have hj1' : P.off ⟨j, hjk⟩ ≤ P.pos x := by
    rw [off_eq_offExt P hk ⟨j, hjk⟩]
    exact hj1
  have hj2' : P.pos x < P.off ⟨j, hjk⟩ + P.len ⟨j, hjk⟩ := by
    rw [← offExt_succ_fin P hk ⟨j, hjk⟩]
    exact hj2
  refine ⟨⟨j, hjk⟩, ?_⟩
  rw [arcOf, mem_arcSet]
  refine ⟨P.pos x - P.off ⟨j, hjk⟩, by omega, ?_⟩
  have e : (P.off ⟨j, hjk⟩ : ZMod m) + ((P.pos x - P.off ⟨j, hjk⟩ : ℕ) : ZMod m)
      = (P.pos x : ZMod m) := by
    rw [← Nat.cast_add, Nat.add_sub_cancel' hj1']
  rw [start, add_assoc, e, base_add_pos]

lemma arcOf_disjoint (hk : 0 < k) [NeZero m] {i j : Fin k} (h : i ≠ j) :
    Disjoint (P.arcOf i) (P.arcOf j) := by
  rw [Finset.disjoint_left]
  intro x hx hxj
  rw [arcOf, mem_arcSet] at hx hxj
  obtain ⟨ti, hti, rfl⟩ := hx
  obtain ⟨tj, htj, h'⟩ := hxj
  have h1 := P.pos_start_add hk i hti
  have h2 := P.pos_start_add hk j htj
  rw [← h', h2] at h1
  have hij : i.val ≠ j.val := Fin.val_ne_of_ne h
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · have hle : P.off i + P.len i ≤ P.off j := by
      rw [← offExt_succ_fin P hk, off_eq_offExt P hk]
      exact P.offExt_mono hk (by omega)
    omega
  · have hle : P.off j + P.len j ≤ P.off i := by
      rw [← offExt_succ_fin P hk, off_eq_offExt P hk]
      exact P.offExt_mono hk (by omega)
    omega


lemma perW_sum_shift (w : ZMod m → ℝ) (a s : ℕ) :
    ∑ t ∈ Finset.Ico (a + m) (a + m + s), P.perW w t = ∑ t ∈ Finset.Ico a (a + s), P.perW w t := by
  apply Finset.sum_bij (fun t _ => t - m)
  · intro t ht
    simp only [Finset.mem_Ico] at ht ⊢
    omega
  · intro t₁ ht₁ t₂ ht₂ h
    simp only [Finset.mem_Ico] at ht₁ ht₂
    omega
  · intro b hb
    simp only [Finset.mem_Ico] at hb
    refine ⟨b + m, by simp only [Finset.mem_Ico]; omega, by omega⟩
  · intro t ht
    simp only [Finset.mem_Ico] at ht
    have e : t - m + m = t := by omega
    conv_lhs => rw [← e, perW_periodic]

lemma perW_sum_period (w : ZMod m → ℝ) (q a s : ℕ) :
    ∑ t ∈ Finset.Ico (a + q * m) (a + q * m + s), P.perW w t
      = ∑ t ∈ Finset.Ico a (a + s), P.perW w t := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [show a + (q + 1) * m = a + q * m + m by ring, perW_sum_shift]
    exact ih

lemma offExt_add_mul_period (hk : 0 < k) (a q : ℕ) :
    P.offExt hk (a + q * k) = P.offExt hk a + q * m := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [show a + (q + 1) * k = (a + q * k) + k by ring, offExt_add_period, ih]
    ring

lemma offExt_eq_off_add_div (hk : 0 < k) (a : ℕ) {j : Fin k} (hj : a % k = j.val) :
    P.offExt hk a = P.off j + (a / k) * m := by
  conv_lhs => rw [← Nat.mod_add_div a k, Nat.mul_comm k (a / k)]
  rw [offExt_add_mul_period, off_eq_offExt P hk j]
  congr 1
  exact congr_arg (P.offExt hk) hj

lemma sum_arcOf (hk : 0 < k) [NeZero m] (i : Fin k) (w : ZMod m → ℝ) :
    ∑ x ∈ P.arcOf i, w x = ∑ t ∈ Finset.Ico (P.off i) (P.off i + P.len i), P.perW w t := by
  rw [arcOf, sum_arcSet (P.len_le hk i) w, Finset.sum_Ico_eq_sum_range,
    Nat.add_sub_cancel_left]
  apply Finset.sum_congr rfl
  intro t _
  rw [perW, start, Nat.cast_add, ← add_assoc]

lemma sum_arcOf_ext (hk : 0 < k) [NeZero m] (a : ℕ) {j : Fin k} (hj : a % k = j.val)
    (w : ZMod m → ℝ) :
    ∑ t ∈ Finset.Ico (P.offExt hk a) (P.offExt hk a + P.len j), P.perW w t
      = ∑ x ∈ P.arcOf j, w x := by
  rw [offExt_eq_off_add_div P hk a hj, perW_sum_period, sum_arcOf P hk]

lemma perW_sum_nonneg (w : ZMod m → ℝ) (hnn : ∀ x, 0 ≤ w x) (a b : ℕ) :
    0 ≤ ∑ t ∈ Finset.Ico a b, P.perW w t := by
  apply Finset.sum_nonneg
  intro x _
  exact hnn _

lemma perW_sum_mono (w : ZMod m → ℝ) (hnn : ∀ x, 0 ≤ w x) {a b c d : ℕ}
    (h1 : c ≤ a) (h2 : b ≤ d) :
    ∑ t ∈ Finset.Ico a b, P.perW w t ≤ ∑ t ∈ Finset.Ico c d, P.perW w t := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · rw [Finset.subset_iff]
    intro x hx
    simp only [Finset.mem_Ico] at hx ⊢
    omega
  · intro x _ _
    exact hnn _



/-!
## Gaps: `nextD` (successor skipping a deleted set) and circular embeddings
-/

section NextD

variable {m : ℕ} [NeZero m]

lemma exists_gap (D : Finset (ZMod m)) (hD : D ≠ Finset.univ) (x : ZMod m) :
    ∃ t : ℕ, 1 ≤ t ∧ t ≤ m ∧ x + (t : ZMod m) ∉ D := by
  obtain ⟨y, _, hy⟩ := Finset.exists_of_ssubset (Finset.ssubset_univ_iff.mpr hD)
  by_cases hyx : y = x
  · refine ⟨m, Nat.pos_of_ne_zero (NeZero.ne m), le_rfl, ?_⟩
    rw [← hyx, ZMod.natCast_self, add_zero]
    exact hy
  · refine ⟨(y - x).val, ?_, ?_, ?_⟩
    · have : (y - x).val ≠ 0 := by
        intro h
        rw [ZMod.val_eq_zero] at h
        exact hyx (by rwa [sub_eq_zero] at h)
      omega
    · exact le_trans (ZMod.val_le _) (by omega)
    · rw [ZMod.natCast_val, ZMod.cast_id, add_comm, sub_add_cancel]
      exact hy

/-- The distance to the next point outside `D` (a positive number of steps). -/
noncomputable def gapSize (D : Finset (ZMod m)) (hD : D ≠ Finset.univ) (x : ZMod m) : ℕ :=
  Nat.find (exists_gap D hD x)

lemma gapSize_spec (D : Finset (ZMod m)) (hD : D ≠ Finset.univ) (x : ZMod m) :
    1 ≤ gapSize D hD x ∧ gapSize D hD x ≤ m ∧ x + (gapSize D hD x : ZMod m) ∉ D :=
  Nat.find_spec (exists_gap D hD x)

lemma gapSize_mem (D : Finset (ZMod m)) (hD : D ≠ Finset.univ) (x : ZMod m) {s : ℕ}
    (h1 : 1 ≤ s) (h2 : s < gapSize D hD x) : x + (s : ZMod m) ∈ D := by
  have h := Nat.find_min (exists_gap D hD x) h2
  have h3 := gapSize_spec D hD x
  by_contra hnot
  exact h ⟨h1, by omega, hnot⟩

/-- The successor of `x` in the circle with `D` deleted. -/
noncomputable def nextD (D : Finset (ZMod m)) (hD : D ≠ Finset.univ) (x : ZMod m) : ZMod m :=
  x + (gapSize D hD x : ZMod m)

lemma nextD_notMem (D : Finset (ZMod m)) (hD : D ≠ Finset.univ) (x : ZMod m) :
    nextD D hD x ∉ D :=
  (gapSize_spec D hD x).2.2

lemma nextD_ne_univ (D : Finset (ZMod m)) (hD : D ≠ Finset.univ) (x : ZMod m) :
    nextD D hD x = x + (gapSize D hD x : ZMod m) := rfl

end NextD

/-- A circular embedding: an enumeration of the complement of `D` that respects
the successor structure of the circle. -/
structure CircleEmb {m : ℕ} [NeZero m] {m' : ℕ} [NeZero m']
    (D : Finset (ZMod m)) (hD : D ≠ Finset.univ) (φ : ZMod m' → ZMod m) : Prop where
  inj : Function.Injective φ
  next : ∀ i, φ (i + 1) = nextD D hD (φ i)
  notMem : ∀ i, φ i ∉ D
  cover : ∀ y, y ∉ D → ∃ i, φ i = y

lemma CircleEmb.congr_D {m : ℕ} [NeZero m] {m' : ℕ} [NeZero m']
    {D₁ D₂ : Finset (ZMod m)} {hD₁ : D₁ ≠ Finset.univ} {hD₂ : D₂ ≠ Finset.univ}
    {φ : ZMod m' → ZMod m} (h : D₁ = D₂) (he : CircleEmb D₁ hD₁ φ) :
    CircleEmb D₂ hD₂ φ := by
  subst h
  exact he

/-- The enumeration of the complement of an arc, starting right after the arc. -/
def skipMap {m : ℕ} (a₀ : ZMod m) (l : ℕ) (i : ZMod (m - l)) : ZMod m :=
  a₀ + (l : ZMod m) + (i.val : ZMod m)

section SkipMap

variable {m : ℕ} [NeZero m] {a₀ : ZMod m} {l : ℕ}

lemma skipMap_injective [NeZero (m - l)] (hl : l ≤ m) :
    Function.Injective (skipMap a₀ l) := by
  intro i₁ i₂ h
  rw [skipMap, skipMap, add_left_cancel_iff] at h
  have hv := natCast_injective_of_lt (m := m) (t₁ := i₁.val) (t₂ := i₂.val)
    (by have := ZMod.val_lt i₁; omega) (by have := ZMod.val_lt i₂; omega) h
  exact ZMod.val_injective _ hv

lemma skipMap_notMem [NeZero (m - l)] (hl : l ≤ m) (i : ZMod (m - l)) :
    skipMap a₀ l i ∉ arcSet a₀ l := by
  rw [mem_arcSet]
  rintro ⟨t, htl, h⟩
  rw [skipMap, add_assoc, add_left_cancel_iff] at h
  have h2 : (t : ZMod m) = ((l + i.val : ℕ) : ZMod m) := by
    rw [Nat.cast_add]
    exact h
  have h3 := natCast_injective_of_lt (m := m) (t₁ := t) (t₂ := l + i.val)
    (by have := ZMod.val_lt i; omega) (by have := ZMod.val_lt i; omega) h2
  omega

lemma skipMap_cover [NeZero (m - l)] (hl : l ≤ m) (y : ZMod m) (hy : y ∉ arcSet a₀ l) :
    ∃ i, skipMap a₀ l i = y := by
  have huy : a₀ + ((y - a₀).val : ZMod m) = y := by
    rw [ZMod.natCast_val, ZMod.cast_id, add_comm, sub_add_cancel]
  by_cases hu : l ≤ (y - a₀).val
  · set u := (y - a₀).val with hu_def
    have hum : u < m := ZMod.val_lt (y - a₀)
    refine ⟨((u - l : ℕ) : ZMod (m - l)), ?_⟩
    have hival : (((u - l : ℕ) : ZMod (m - l)).val) = u - l := by
      rw [ZMod.val_natCast]
      exact Nat.mod_eq_of_lt (by omega)
    rw [skipMap, hival]
    have e : (l : ZMod m) + ((u - l : ℕ) : ZMod m) = (u : ZMod m) := by
      rw [← Nat.cast_add, Nat.add_sub_cancel' hu]
    rw [add_assoc, e]
    exact huy
  · exfalso
    apply hy
    rw [mem_arcSet]
    exact ⟨(y - a₀).val, by have := ZMod.val_lt (y - a₀); omega, huy⟩


omit [NeZero m] in
lemma skipMap_add (i : ZMod (m - l)) (s : ℕ) :
    skipMap a₀ l i + (s : ZMod m) = a₀ + ((l + i.val + s : ℕ) : ZMod m) := by
  rw [skipMap, Nat.cast_add, Nat.cast_add]
  abel

omit [NeZero m] in
lemma skipMap_eq (j : ZMod (m - l)) :
    skipMap a₀ l j = a₀ + ((l + j.val : ℕ) : ZMod m) := by
  rw [skipMap, Nat.cast_add, add_assoc]

omit [NeZero m] in
lemma mem_arcSet_iff (hl : l ≤ m) (u s : ℕ) :
    (a₀ + ((l + u + s : ℕ) : ZMod m)) ∈ arcSet a₀ l ↔ (l + u + s) % m < l := by
  rw [mem_arcSet]
  constructor
  · rintro ⟨t, htl, h⟩
    rw [add_left_cancel_iff, ZMod.natCast_eq_natCast_iff] at h
    have h' : t % m = (l + u + s) % m := h
    rw [Nat.mod_eq_of_lt (by omega : t < m)] at h'
    rw [← h']
    exact htl
  · intro h
    refine ⟨(l + u + s) % m, h, ?_⟩
    rw [add_left_cancel_iff, ZMod.natCast_eq_natCast_iff]
    exact Nat.mod_modEq _ _

lemma skipMap_next [NeZero (m - l)] (hl : l ≤ m) (hlD : arcSet a₀ l ≠ Finset.univ)
    (i : ZMod (m - l)) :
    skipMap a₀ l (i + 1) = nextD (arcSet a₀ l) hlD (skipMap a₀ l i) := by
  have hlm : l < m := by
    by_contra h
    push Not at h
    rw [Nat.le_antisymm hl h] at hlD
    exact hlD arcSet_univ
  have hum : i.val < m - l := ZMod.val_lt i
  have hone : (1 : ZMod (m - l)) = ((1 : ℕ) : ZMod (m - l)) := by simp
  by_cases hcase : i.val + 1 < m - l
  · have hnot : skipMap a₀ l i + ((1 : ℕ) : ZMod m) ∉ arcSet a₀ l := by
      rw [skipMap_add, mem_arcSet_iff hl, Nat.mod_eq_of_lt (by omega : l + i.val + 1 < m)]
      omega
    have hgap : gapSize (arcSet a₀ l) hlD (skipMap a₀ l i) = 1 := by
      apply le_antisymm
      · exact Nat.find_min' (exists_gap (arcSet a₀ l) hlD (skipMap a₀ l i))
          ⟨le_refl 1, Nat.pos_of_ne_zero (NeZero.ne m), hnot⟩
      · exact (gapSize_spec _ _ _).1
    have hival : (i + 1).val = i.val + 1 := by
      rw [hone, ZMod.val_add, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega : 1 < m - l)]
      exact Nat.mod_eq_of_lt (by omega)
    have h1 : nextD (arcSet a₀ l) hlD (skipMap a₀ l i)
        = skipMap a₀ l i + ((1 : ℕ) : ZMod m) := by
      rw [nextD, hgap]
    rw [h1, skipMap_add, skipMap_eq, hival, add_left_cancel_iff, ZMod.natCast_eq_natCast_iff]
    have e : l + (i.val + 1) = l + i.val + 1 := by omega
    rw [e]
  · have hu : i.val = m - l - 1 := by omega
    have hnot : skipMap a₀ l i + ((l + 1 : ℕ) : ZMod m) ∉ arcSet a₀ l := by
      rw [skipMap_add, mem_arcSet_iff hl]
      have e1 : l + i.val + (l + 1) = m + l := by omega
      rw [e1, Nat.add_mod_left, Nat.mod_eq_of_lt hlm]
      exact Nat.lt_irrefl l
    have hmem : ∀ s : ℕ, 1 ≤ s → s ≤ l → skipMap a₀ l i + (s : ZMod m) ∈ arcSet a₀ l := by
      intro s hs1 hs2
      rw [skipMap_add, mem_arcSet_iff hl]
      have e1 : l + i.val + s = m + (s - 1) := by omega
      rw [e1, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega : s - 1 < m)]
      omega
    have hgap : gapSize (arcSet a₀ l) hlD (skipMap a₀ l i) = l + 1 := by
      apply le_antisymm
      · exact Nat.find_min' (exists_gap (arcSet a₀ l) hlD (skipMap a₀ l i))
          ⟨by omega, by omega, hnot⟩
      · by_contra hlt
        push Not at hlt
        have hspec := gapSize_spec (arcSet a₀ l) hlD (skipMap a₀ l i)
        exact hspec.2.2 (hmem _ hspec.1 (by omega))
    have hival : (i + 1).val = 0 := by
      by_cases hml : m - l = 1
      · have h1 : (i + 1).val < m - l := ZMod.val_lt (i + 1)
        omega
      · rw [hone, ZMod.val_add, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega : 1 < m - l),
          hu, show m - l - 1 + 1 = m - l by omega, Nat.mod_self]
    have h1 : nextD (arcSet a₀ l) hlD (skipMap a₀ l i)
        = skipMap a₀ l i + ((l + 1 : ℕ) : ZMod m) := by
      rw [nextD, hgap]
    rw [h1, skipMap_add, skipMap_eq, hival, add_left_cancel_iff, ZMod.natCast_eq_natCast_iff]
    have e1 : l + 0 = l := by omega
    have e2 : l + i.val + (l + 1) = m + l := by omega
    rw [e1, e2, Nat.ModEq, Nat.add_mod_left]

/-- The circular embedding given by skipping a single arc. -/
lemma circleEmb_skipMap [NeZero (m - l)] (hl : l ≤ m) (hlD : arcSet a₀ l ≠ Finset.univ) :
    CircleEmb (arcSet a₀ l) hlD (skipMap a₀ l) where
  inj := skipMap_injective hl
  next := fun i => skipMap_next hl hlD i
  notMem := fun i => skipMap_notMem hl i
  cover := fun y hy => skipMap_cover hl y hy


lemma mem_image_skipMap (D₂ : Finset (ZMod (m - l))) [NeZero (m - l)] (hl : l ≤ m)
    (z : ZMod (m - l)) :
    skipMap a₀ l z ∈ D₂.image (skipMap a₀ l) ↔ z ∈ D₂ := by
  rw [Finset.mem_image]
  constructor
  · rintro ⟨d, hd, h⟩
    rw [← skipMap_injective hl h]
    exact hd
  · intro h
    exact ⟨z, h, rfl⟩

/-- The intertwining lemma: skipping an arc commutes with the deleted successor. -/
lemma skipMap_nextD [NeZero (m - l)] (hl : l ≤ m)
    (D₂ : Finset (ZMod (m - l))) (hD₂ : D₂ ≠ Finset.univ)
    (hD : arcSet a₀ l ∪ D₂.image (skipMap a₀ l) ≠ Finset.univ)
    (x : ZMod (m - l)) :
    skipMap a₀ l (nextD D₂ hD₂ x) =
      nextD (arcSet a₀ l ∪ D₂.image (skipMap a₀ l)) hD (skipMap a₀ l x) := by
  have hu : x.val < m - l := ZMod.val_lt x
  have hg := gapSize_spec D₂ hD₂ x
  set g := gapSize D₂ hD₂ x with hg_def
  have hLHS_notMem : skipMap a₀ l (nextD D₂ hD₂ x)
      ∉ arcSet a₀ l ∪ D₂.image (skipMap a₀ l) := by
    rw [Finset.mem_union]
    push Not
    refine ⟨skipMap_notMem hl _, ?_⟩
    rw [mem_image_skipMap D₂ hl]
    exact nextD_notMem D₂ hD₂ x
  set G := (if l + x.val + g < m then g else g + l) with hG_def
  have hGL : skipMap a₀ l x + (G : ZMod m) = skipMap a₀ l (nextD D₂ hD₂ x) := by
    by_cases hc : l + x.val + g < m
    · rw [hG_def, if_pos hc]
      have h1 : (x + ((g : ℕ) : ZMod (m - l))).val = x.val + g := by
        rw [ZMod.val_add, ZMod.val_natCast, Nat.add_mod_mod,
          Nat.mod_eq_of_lt (by omega)]
      rw [skipMap_add, nextD, ← hg_def, skipMap_eq, h1, add_left_cancel_iff,
        ZMod.natCast_eq_natCast_iff, show l + x.val + g = l + (x.val + g) by omega]
    · rw [hG_def, if_neg hc]
      have h1 : (x + ((g : ℕ) : ZMod (m - l))).val = x.val + g - (m - l) := by
        rw [ZMod.val_add, ZMod.val_natCast, Nat.add_mod_mod,
          Nat.mod_eq_sub_mod (by omega : m - l ≤ x.val + g),
          Nat.mod_eq_of_lt (by omega : x.val + g - (m - l) < m - l)]
      rw [skipMap_add, nextD, ← hg_def, skipMap_eq, h1, add_left_cancel_iff,
        ZMod.natCast_eq_natCast_iff]
      have e : l + x.val + (g + l) = (l + (x.val + g - (m - l))) + m := by omega
      rw [e, Nat.ModEq, Nat.add_mod_right]
  have hG1 : 1 ≤ G := by
    by_cases hc : l + x.val + g < m
    · rw [hG_def, if_pos hc]; omega
    · rw [hG_def, if_neg hc]; omega
  have hGm : G ≤ m := by
    by_cases hc : l + x.val + g < m
    · rw [hG_def, if_pos hc]; omega
    · rw [hG_def, if_neg hc]; omega
  have hmem_walk : ∀ s : ℕ, 1 ≤ s → s < G →
      skipMap a₀ l x + (s : ZMod m) ∈ arcSet a₀ l ∪ D₂.image (skipMap a₀ l) := by
    intro s hs1 hsG
    by_cases hc : l + x.val + g < m
    · rw [hG_def, if_pos hc] at hsG
      have h1 : skipMap a₀ l x + (s : ZMod m) = skipMap a₀ l (x + (s : ZMod (m - l))) := by
        rw [skipMap_add, skipMap, ZMod.val_add, ZMod.val_natCast, Nat.add_mod_mod,
          Nat.mod_eq_of_lt (by omega : x.val + s < m - l),
          add_assoc a₀ (l : ZMod m) (↑(x.val + s)), ← Nat.cast_add,
          show l + x.val + s = l + (x.val + s) by omega]
      rw [h1, Finset.mem_union]
      right
      rw [mem_image_skipMap D₂ hl]
      exact gapSize_mem D₂ hD₂ x hs1 hsG
    · rw [hG_def, if_neg hc] at hsG
      set s₀ := m - l - x.val with hs₀_def
      by_cases hs2 : s < s₀
      · have h1 : skipMap a₀ l x + (s : ZMod m) = skipMap a₀ l (x + (s : ZMod (m - l))) := by
          rw [skipMap_add, skipMap, ZMod.val_add, ZMod.val_natCast, Nat.add_mod_mod,
            Nat.mod_eq_of_lt (by omega : x.val + s < m - l),
            add_assoc a₀ (l : ZMod m) (↑(x.val + s)), ← Nat.cast_add,
            show l + x.val + s = l + (x.val + s) by omega]
        rw [h1, Finset.mem_union]
        right
        rw [mem_image_skipMap D₂ hl]
        exact gapSize_mem D₂ hD₂ x hs1 (by omega)
      · by_cases hs3 : s < s₀ + l
        · rw [Finset.mem_union]
          left
          rw [skipMap_add, mem_arcSet_iff hl,
            Nat.mod_eq_sub_mod (by omega : m ≤ l + x.val + s),
            Nat.mod_eq_of_lt (by omega : l + x.val + s - m < m)]
          omega
        · have h2 : (x + ((s - l : ℕ) : ZMod (m - l))).val = x.val + (s - l) - (m - l) := by
            rw [ZMod.val_add, ZMod.val_natCast, Nat.add_mod_mod,
              Nat.mod_eq_sub_mod (by omega : m - l ≤ x.val + (s - l)),
              Nat.mod_eq_of_lt (by omega : x.val + (s - l) - (m - l) < m - l)]
          have h1 : skipMap a₀ l x + (s : ZMod m)
              = skipMap a₀ l (x + ((s - l : ℕ) : ZMod (m - l))) := by
            rw [skipMap_add, skipMap, h2,
              add_assoc a₀ (l : ZMod m) (↑(x.val + (s - l) - (m - l))), ← Nat.cast_add,
              add_left_cancel_iff, ZMod.natCast_eq_natCast_iff]
            have e : l + x.val + s = (l + (x.val + (s - l) - (m - l))) + m := by omega
            rw [e, Nat.ModEq, Nat.add_mod_right]
          rw [h1, Finset.mem_union]
          right
          rw [mem_image_skipMap D₂ hl]
          exact gapSize_mem D₂ hD₂ x (by omega) (by omega)
  have hgap : gapSize (arcSet a₀ l ∪ D₂.image (skipMap a₀ l)) hD (skipMap a₀ l x) = G := by
    apply le_antisymm
    · exact Nat.find_min' (exists_gap _ hD _) ⟨hG1, hGm, by rw [hGL]; exact hLHS_notMem⟩
    · by_contra hlt
      push Not at hlt
      have hspec := gapSize_spec _ hD (skipMap a₀ l x)
      exact hspec.2.2 (hmem_walk _ hspec.1 (by omega))
  conv_rhs => rw [nextD, hgap]
  exact hGL.symm

/-- Composition of a circular embedding with `skipMap`. -/
lemma circleEmb_comp_skipMap {m : ℕ} [NeZero m] {a₀ : ZMod m} {l : ℕ} [NeZero (m - l)]
    (hl : l ≤ m) {m₂ : ℕ} [NeZero m₂] (D₂ : Finset (ZMod (m - l))) (hD₂ : D₂ ≠ Finset.univ)
    (ψ : ZMod m₂ → ZMod (m - l)) (hψ : CircleEmb D₂ hD₂ ψ)
    (hD : arcSet a₀ l ∪ D₂.image (skipMap a₀ l) ≠ Finset.univ) :
    CircleEmb (arcSet a₀ l ∪ D₂.image (skipMap a₀ l)) hD ((skipMap a₀ l) ∘ ψ) where
  inj := (skipMap_injective hl).comp hψ.inj
  next := fun i => by
    rw [Function.comp_apply, Function.comp_apply, hψ.next]
    exact skipMap_nextD hl D₂ hD₂ hD (ψ i)
  notMem := fun i => by
    rw [Function.comp_apply, Finset.mem_union]
    push Not
    refine ⟨skipMap_notMem hl _, ?_⟩
    rw [mem_image_skipMap D₂ hl]
    exact hψ.notMem i
  cover := fun y hy => by
    rw [Finset.mem_union] at hy
    push Not at hy
    obtain ⟨x, hx⟩ := skipMap_cover hl y hy.1
    have hx2 : x ∉ D₂ := by
      intro h
      exact hy.2 (Finset.mem_image.mpr ⟨x, h, hx⟩)
    obtain ⟨i, hi⟩ := hψ.cover x hx2
    exact ⟨i, by rw [Function.comp_apply, hi, hx]⟩


/-- Factorization of a circular embedding through `skipMap`. -/
lemma circleEmb_factor {m : ℕ} [NeZero m] {m' : ℕ} [NeZero m'] {a₀ : ZMod m} {l : ℕ}
    [NeZero (m - l)] (hl : l ≤ m)
    (D₂ : Finset (ZMod (m - l))) (hD₂ : D₂ ≠ Finset.univ)
    (D : Finset (ZMod m)) (hD : D ≠ Finset.univ)
    (hDeq : D = arcSet a₀ l ∪ D₂.image (skipMap a₀ l))
    (φ : ZMod m' → ZMod m) (hφ : CircleEmb D hD φ) :
    ∃ φ' : ZMod m' → ZMod (m - l), (skipMap a₀ l ∘ φ') = φ ∧ CircleEmb D₂ hD₂ φ' := by
  have hD' : arcSet a₀ l ∪ D₂.image (skipMap a₀ l) ≠ Finset.univ := hDeq ▸ hD
  have hmem : ∀ i, φ i ∈ Set.range (skipMap a₀ l) := by
    intro i
    have h1 := hφ.notMem i
    rw [hDeq, Finset.mem_union] at h1
    push Not at h1
    exact skipMap_cover hl (φ i) h1.1
  choose φ' hφ' using fun i => hmem i
  have hinj : Function.Injective φ' := by
    intro i₁ i₂ h
    apply hφ.inj
    rw [← hφ' i₁, ← hφ' i₂, h]
  refine ⟨φ', funext hφ', hinj, ?_, ?_, ?_⟩
  · intro i
    apply skipMap_injective hl
    rw [hφ' (i + 1), hφ.next i, ← hφ' i]
    subst hDeq
    exact (skipMap_nextD hl D₂ hD₂ hD (φ' i)).symm
  · intro i
    have h1 := hφ.notMem i
    rw [hDeq, Finset.mem_union] at h1
    push Not at h1
    rw [← hφ' i] at h1
    rw [mem_image_skipMap D₂ hl] at h1
    exact h1.2
  · intro y hy
    have hys : skipMap a₀ l y ∉ D := by
      rw [hDeq, Finset.mem_union]
      push Not
      refine ⟨skipMap_notMem hl _, ?_⟩
      rw [mem_image_skipMap D₂ hl]
      exact hy
    obtain ⟨i, hi⟩ := hφ.cover (skipMap a₀ l y) hys
    refine ⟨i, ?_⟩
    apply skipMap_injective hl
    rw [hφ' i, hi]

end SkipMap

/-- Transport of an arc disjoint from the skipped arc into the smaller circle. -/
lemma transport_arc {m : ℕ} [NeZero m] {a₀ : ZMod m} {l : ℕ} [NeZero (m - l)]
    (hl1 : 1 ≤ l) (hl : l ≤ m) {c : ZMod m} {l₁ : ℕ} (hl₁ : 1 ≤ l₁)
    (hdisj : Disjoint (arcSet a₀ l) (arcSet c l₁)) :
    ∃ v : ZMod (m - l), l₁ ≤ m - l ∧
      (arcSet v l₁).image (skipMap a₀ l) = arcSet c l₁ ∧
      (∀ w : ZMod m → ℝ, ∑ x ∈ arcSet c l₁, w x = ∑ y ∈ arcSet v l₁, w (skipMap a₀ l y)) := by
  have hu : (c - a₀).val < m := ZMod.val_lt (c - a₀)
  have hcuy : a₀ + ((c - a₀).val : ZMod m) = c := by
    rw [ZMod.natCast_val, ZMod.cast_id, add_comm, sub_add_cancel]
  have hnot : ¬ (c - a₀).val < l := by
    intro hlt
    have hmem : c ∈ arcSet a₀ l := by
      rw [mem_arcSet]
      exact ⟨(c - a₀).val, hlt, hcuy⟩
    have hmem2 : c ∈ arcSet c l₁ := by
      rw [mem_arcSet]
      exact ⟨0, hl₁, by simp⟩
    exact Finset.disjoint_left.mp hdisj hmem hmem2
  set v₀ := (c - a₀).val - l with hv₀_def
  have hv₀ : v₀ < m - l := by omega
  have hcv : c = a₀ + (l : ZMod m) + (v₀ : ZMod m) := by
    rw [← hcuy]
    have e : ((c - a₀).val : ZMod m) = (l : ZMod m) + (v₀ : ZMod m) := by
      rw [← Nat.cast_add, Nat.add_sub_cancel' (by omega : l ≤ (c - a₀).val)]
    rw [e]
    abel
  have hle : v₀ + l₁ ≤ m - l := by
    by_contra h
    push Not at h
    set t := m - l - v₀ with ht_def
    have ht1 : t < l₁ := by omega
    have ht2 : a₀ ∈ arcSet c l₁ := by
      rw [mem_arcSet]
      refine ⟨t, ht1, ?_⟩
      have e2 : l + v₀ + t = m := by omega
      have e3 : (l : ZMod m) + (v₀ : ZMod m) + (t : ZMod m) = ((l + v₀ + t : ℕ) : ZMod m) := by
        rw [Nat.cast_add, Nat.cast_add]
      rw [hcv, show (a₀ + ↑l + ↑v₀) + ↑t = a₀ + (↑l + ↑v₀ + ↑t) by abel, e3, e2,
        ZMod.natCast_self, add_zero]
    have ht3 : a₀ ∈ arcSet a₀ l := by
      rw [mem_arcSet]
      exact ⟨0, hl1, by simp⟩
    exact Finset.disjoint_left.mp hdisj ht3 ht2
  refine ⟨((v₀ : ℕ) : ZMod (m - l)), by omega, ?_, ?_⟩
  · apply Finset.eq_of_subset_of_card_le
    · intro y hy
      rw [Finset.mem_image] at hy
      obtain ⟨z, hz, hzy⟩ := hy
      rw [mem_arcSet] at hz ⊢
      obtain ⟨s, hs1, hs2⟩ := hz
      refine ⟨s, hs1, ?_⟩
      have e : (((v₀ : ℕ) : ZMod (m - l)) + (s : ZMod (m - l))).val = v₀ + s := by
        rw [← Nat.cast_add, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega : v₀ + s < m - l)]
      rw [← hzy, ← hs2, skipMap, e, hcv, Nat.cast_add]
      abel
    · rw [Finset.card_image_of_injective _ (skipMap_injective hl), arcSet_card (by omega),
        arcSet_card (by omega)]
  · intro w
    rw [sum_arcSet (by omega : l₁ ≤ m), sum_arcSet (by omega : l₁ ≤ m - l)]
    apply Finset.sum_congr rfl
    intro s hs
    rw [Finset.mem_range] at hs
    have e : (((v₀ : ℕ) : ZMod (m - l)) + (s : ZMod (m - l))).val = v₀ + s := by
      rw [← Nat.cast_add, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega : v₀ + s < m - l)]
    have e2 : c + (s : ZMod m) = a₀ + (l : ZMod m) + ((v₀ + s : ℕ) : ZMod m) := by
      rw [hcv, Nat.cast_add]
      abel
    rw [e2, skipMap, e]


/-- Surgery: deleting a family of disjoint arcs yields a circular embedding of
the complement, built by composing `skipMap`s. -/
lemma surgeryMany {t : ℕ} :
    ∀ {m : ℕ} [NeZero m] (ca : Fin t → ZMod m) (la : Fin t → ℕ)
    (_hla1 : ∀ s, 1 ≤ la s) (_hlam : ∀ s, la s ≤ m)
    (_hdij : ∀ s₁ s₂, s₁ ≠ s₂ → Disjoint (arcSet (ca s₁) (la s₁)) (arcSet (ca s₂) (la s₂)))
    (hD : (Finset.univ.biUnion fun s => arcSet (ca s) (la s)) ≠ Finset.univ),
    ∃ (m' : ℕ) (_ : NeZero m') (φ : ZMod m' → ZMod m),
      CircleEmb (Finset.univ.biUnion fun s => arcSet (ca s) (la s)) hD φ ∧
      m' = m - ∑ s, la s := by
  induction t with
  | zero =>
    intro m _ ca la _ _ _ hD
    have hD0 : (Finset.univ.biUnion fun s : Fin 0 => arcSet (ca s) (la s)) = ∅ := by
      simp [Finset.univ_eq_empty]
    have hempty : (∅ : Finset (ZMod m)) ≠ Finset.univ := Finset.univ_nonempty.ne_empty.symm
    have hnext : ∀ i : ZMod m, (id i) + 1 = nextD ∅ hempty i := by
      intro i
      have hg : gapSize ∅ hempty i = 1 := by
        apply le_antisymm
        · exact Nat.find_min' (exists_gap ∅ hempty i)
            ⟨le_refl 1, Nat.pos_of_ne_zero (NeZero.ne m), by simp⟩
        · exact (gapSize_spec ∅ hempty i).1
      rw [nextD, hg, Nat.cast_one, id_eq]
    have hid : CircleEmb ∅ hempty (id : ZMod m → ZMod m) := {
      inj := Function.injective_id
      next := fun i => hnext i
      notMem := fun i => by simp
      cover := fun y hy => ⟨y, rfl⟩
    }
    refine ⟨m, inferInstance, id, CircleEmb.congr_D hD0 hid, by simp⟩
  | succ t ih =>
    intro m hm ca la hla1 hlam hdij hD
    have hl0 : la 0 < m := by
      have h1 := hlam 0
      rcases Nat.eq_or_lt_of_le h1 with h2 | h2
      · exfalso
        apply hD
        apply Finset.eq_univ_of_forall
        intro x
        rw [Finset.mem_biUnion]
        exact ⟨0, Finset.mem_univ _, by rw [h2, arcSet_univ]; exact Finset.mem_univ x⟩
      · exact h2
    have : NeZero (m - la 0) := ⟨by omega⟩
    have htr : ∀ s : Fin t, ∃ v : ZMod (m - la 0), la s.succ ≤ m - la 0 ∧
      (arcSet v (la s.succ)).image (skipMap (ca 0) (la 0)) = arcSet (ca s.succ) (la s.succ) ∧
      (∀ w : ZMod m → ℝ, ∑ x ∈ arcSet (ca s.succ) (la s.succ), w x
        = ∑ y ∈ arcSet v (la s.succ), w (skipMap (ca 0) (la 0) y)) := by
      intro s
      exact transport_arc (hla1 0) (hlam 0) (hla1 s.succ)
        (hdij 0 s.succ (Fin.succ_ne_zero s).symm)
    choose v hvle himg hsum using htr
    have hdij' : ∀ s₁ s₂ : Fin t, s₁ ≠ s₂ →
        Disjoint (arcSet (v s₁) (la s₁.succ)) (arcSet (v s₂) (la s₂.succ)) := by
      intro s₁ s₂ h
      rw [Finset.disjoint_left]
      intro x hx₁ hx₂
      have h1 : skipMap (ca 0) (la 0) x ∈ arcSet (ca s₁.succ) (la s₁.succ) := by
        rw [← himg s₁]
        exact Finset.mem_image_of_mem _ hx₁
      have h2 : skipMap (ca 0) (la 0) x ∈ arcSet (ca s₂.succ) (la s₂.succ) := by
        rw [← himg s₂]
        exact Finset.mem_image_of_mem _ hx₂
      exact Finset.disjoint_left.mp
        (hdij s₁.succ s₂.succ (fun hh => h (Fin.succ_inj.mp hh))) h1 h2
    have hdecomp : arcSet (ca 0) (la 0) ∪ (Finset.univ.biUnion fun s : Fin t =>
        arcSet (v s) (la s.succ)).image (skipMap (ca 0) (la 0))
        = Finset.univ.biUnion fun s : Fin (t + 1) => arcSet (ca s) (la s) := by
      have hb : ((Finset.univ.biUnion fun s : Fin t => arcSet (v s) (la s.succ)).image
          (skipMap (ca 0) (la 0)))
          = Finset.univ.biUnion fun s : Fin t =>
            (arcSet (v s) (la s.succ)).image (skipMap (ca 0) (la 0)) := by
        ext x
        simp only [Finset.mem_image, Finset.mem_biUnion]
        tauto
      rw [hb]
      ext x
      rw [Finset.mem_union, Finset.mem_biUnion, Finset.mem_biUnion]
      constructor
      · rintro (h | ⟨s, _, hs⟩)
        · exact ⟨0, Finset.mem_univ _, h⟩
        · rw [himg s] at hs
          exact ⟨s.succ, Finset.mem_univ _, hs⟩
      · rintro ⟨s, _, hs⟩
        rcases Fin.eq_zero_or_eq_succ s with rfl | ⟨s', rfl⟩
        · exact Or.inl hs
        · exact Or.inr ⟨s', Finset.mem_univ _, by rw [himg s']; exact hs⟩
    have hD' : (Finset.univ.biUnion fun s : Fin t => arcSet (v s) (la s.succ))
        ≠ Finset.univ := by
      intro huniv
      apply hD
      rw [← hdecomp]
      apply Finset.eq_univ_of_forall
      intro x
      rw [Finset.mem_union]
      by_cases hx : x ∈ arcSet (ca 0) (la 0)
      · exact Or.inl hx
      · right
        obtain ⟨i, hi⟩ := skipMap_cover (Nat.le_of_lt hl0) x hx
        have hxi : i ∈ (Finset.univ.biUnion fun s : Fin t => arcSet (v s) (la s.succ)) := by
          rw [huniv]
          exact Finset.mem_univ i
        rw [← hi]
        exact Finset.mem_image_of_mem _ hxi
    obtain ⟨m', hm', ψ, hψ, hm'eq⟩ := ih v (fun s => la s.succ)
      (fun s => hla1 s.succ) (fun s => hvle s) hdij' hD'
    refine ⟨m', hm', skipMap (ca 0) (la 0) ∘ ψ, ?_, ?_⟩
    · rw [← hdecomp] at hD
      exact CircleEmb.congr_D hdecomp
        (circleEmb_comp_skipMap (Nat.le_of_lt hl0) _ hD' ψ hψ hD)
    · rw [Fin.sum_univ_succ]
      omega


lemma off_zero (hk : 0 < k) : P.off ⟨0, hk⟩ = 0 := by
  rw [off, Finset.filter_eq_empty_iff.mpr (fun j _ => by
    simp only [Fin.lt_def]
    omega), Finset.sum_empty]

lemma off_succ (i : Fin k) (h : i.val + 1 < k) : P.off ⟨i.val + 1, h⟩ = P.off i + P.len i := by
  rw [off, off]
  have e : (Finset.univ.filter (· < ⟨i.val + 1, h⟩)) = (Finset.univ.filter (· < i)) ∪ {i} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      Finset.mem_singleton, Fin.lt_def]
    constructor
    · intro h1
      by_cases h2 : x.val < i.val
      · exact Or.inl h2
      · exact Or.inr (Fin.ext (by omega))
    · rintro (h1 | h1)
      · omega
      · rw [h1]; omega
  rw [e, Finset.sum_union (by
    rw [Finset.disjoint_left]
    intro x hx hx2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
      Fin.lt_def] at hx hx2
    rw [hx2] at hx
    omega)]
  simp

/-- The single-arc merge lemma: deleting an arc of value `< 1` from the circle
yields a smaller circle with a partition into `k - 1` arcs of value `≥ 1`. -/
lemma mergeOne {m k : ℕ} [NeZero m] (P : CirclePartition m k) (hk : 0 < k) (hk2 : 2 ≤ k)
    (w : ZMod m → ℝ) (hnn : ∀ x, 0 ≤ w x)
    (hval : ∀ i, 1 ≤ ∑ x ∈ P.arcOf i, w x)
    {a₀ : ZMod m} {l : ℕ} (hl1 : 1 ≤ l) (hlm : l ≤ m)
    (hA : ∑ x ∈ arcSet a₀ l, w x < 1) :
    ∃ (P' : CirclePartition (m - l) (k - 1)),
      (∀ i, 1 ≤ ∑ x ∈ P'.arcOf i, (w ∘ skipMap a₀ l) x) := by
  have hlm' : l < m := by
    by_contra h
    push Not at h
    rw [Nat.le_antisymm hlm h, arcSet_univ] at hA
    have hge : 1 ≤ ∑ x : ZMod m, w x := by
      have h1 := hval ⟨0, hk⟩
      exact le_trans h1 (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun x _ _ => hnn x))
    linarith
  have : NeZero (m - l) := ⟨by omega⟩
  obtain ⟨j, hj⟩ := P.arcOf_cover hk a₀
  rw [arcOf, mem_arcSet] at hj
  obtain ⟨tj, htj, htj2⟩ := hj
  set p := P.pos a₀ with hp_def
  have hp1 : P.base + (p : ZMod m) = a₀ := P.base_add_pos a₀
  have hp2 : p < m := ZMod.val_lt _
  have hp3 : p = P.off j + tj := by
    rw [hp_def, ← htj2]
    exact P.pos_start_add hk j htj
  have hAIco : ∑ x ∈ arcSet a₀ l, w x = ∑ t ∈ Finset.Ico p (p + l), P.perW w t := by
    rw [sum_arcSet hlm w, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
    apply Finset.sum_congr rfl
    intro t _
    rw [perW, ← hp1]
    congr 1
    rw [Nat.cast_add]
    abel
  have hpl : p + l ≤ P.offExt hk (j.val + 2) := by
    by_contra h
    push Not at h
    have hsub : ∑ t ∈ Finset.Ico (P.offExt hk (j.val + 1)) (P.offExt hk (j.val + 2)),
        P.perW w t ≤ ∑ t ∈ Finset.Ico p (p + l), P.perW w t := by
      apply P.perW_sum_mono w hnn
      · rw [offExt_succ_fin P hk]
        omega
      · omega
    have hge : 1 ≤ ∑ t ∈ Finset.Ico (P.offExt hk (j.val + 1)) (P.offExt hk (j.val + 2)),
        P.perW w t := by
      have h1 := hval ⟨(j.val + 1) % k, Nat.mod_lt _ hk⟩
      rw [← sum_arcOf_ext P hk (j.val + 1) (j := ⟨(j.val + 1) % k, Nat.mod_lt _ hk⟩) rfl w] at h1
      have e : P.offExt hk (j.val + 2)
          = P.offExt hk (j.val + 1) + P.len ⟨(j.val + 1) % k, Nat.mod_lt _ hk⟩ := by
        rw [show j.val + 2 = (j.val + 1) + 1 by omega, offExt_succ]
      rw [e]
      exact h1
    have hA2 : ∑ t ∈ Finset.Ico p (p + l), P.perW w t < 1 := hAIco ▸ hA
    linarith
  set H := p - P.off j with hH_def
  set T := P.offExt hk (j.val + 2) - p - l with hT_def
  have hoff2 : P.offExt hk (j.val + 2)
      = P.off j + P.len j + P.len ⟨(j.val + 1) % k, Nat.mod_lt _ hk⟩ := by
    rw [show j.val + 2 = (j.val + 1) + 1 by omega, offExt_succ, offExt_succ_fin P hk]
  have hHT : H + T = P.len j + P.len ⟨(j.val + 1) % k, Nat.mod_lt _ hk⟩ - l := by
    rw [hH_def, hT_def, hoff2]
    omega
  have hHT1 : 1 ≤ H + T := by
    rw [hHT]
    by_cases hp0 : p = P.off j
    · have hl' : l < P.len j := by
        by_contra hl''
        push Not at hl''
        have hsub : ∑ t ∈ Finset.Ico (P.off j) (P.off j + P.len j), P.perW w t
            ≤ ∑ t ∈ Finset.Ico p (p + l), P.perW w t := by
          apply P.perW_sum_mono w hnn <;> omega
        have hge : 1 ≤ ∑ t ∈ Finset.Ico (P.off j) (P.off j + P.len j), P.perW w t := by
          have h1 := hval j
          rw [sum_arcOf P hk] at h1
          exact h1
        have hA2 : ∑ t ∈ Finset.Ico p (p + l), P.perW w t < 1 := hAIco ▸ hA
        linarith
      have hlen1 := P.len_pos ⟨(j.val + 1) % k, Nat.mod_lt _ hk⟩
      omega
    · omega
  have hdisj : (j.val + 1) % k ≠ j.val := by
    intro h
    have h1 : (j.val + 1) % k = j.val := h
    have h2 : ∃ q, j.val + 1 = j.val + k * q := by
      refine ⟨(j.val + 1) / k, ?_⟩
      conv_lhs => rw [← Nat.mod_add_div (j.val + 1) k, h1]
    obtain ⟨q, hq⟩ := h2
    have h3 : k ≤ 1 := Nat.le_of_dvd (by omega : 0 < 1) ⟨q, by omega⟩
    omega
  have hHTm : H + T ≤ m - l := by
    have hle : P.len j + P.len ⟨(j.val + 1) % k, Nat.mod_lt _ hk⟩ ≤ m := by
      have hsum : ∑ i ∈ ({j, ⟨(j.val + 1) % k, Nat.mod_lt _ hk⟩} : Finset (Fin k)), P.len i
          ≤ ∑ i, P.len i := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        intro x _ _
        have := P.len_pos x
        omega
      rw [P.len_sum, Finset.sum_insert (by
        rw [Finset.mem_singleton]
        intro h
        exact hdisj (congr_arg Fin.val h).symm), Finset.sum_singleton] at hsum
      exact hsum
    omega
  set base' := ((m - l - H : ℕ) : ZMod (m - l)) with hbase'_def
  set len' : Fin (k - 1) → ℕ := fun i =>
    if i.val = 0 then H + T else P.len ⟨(j.val + 1 + i.val) % k, Nat.mod_lt _ hk⟩ with hlen'_def
  have hlen'_pos : ∀ i : Fin (k - 1), 1 ≤ len' i := by
    intro i
    by_cases hi : i.val = 0
    · simp only [hlen'_def, hi, if_true]
      exact hHT1
    · simp only [hlen'_def, hi, if_false]
      exact P.len_pos _
  have hk' : 0 < k - 1 := Nat.sub_pos_of_lt hk2
  have hofj : P.off j = P.offExt hk j.val := off_eq_offExt P hk j
  have hlen'_sum : ∑ i, len' i = m - l := by
    have hz : (Finset.univ.filter (fun i : Fin (k - 1) => i.val = 0))
        = {⟨0, hk'⟩} := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro h
        exact Fin.ext h
      · intro h
        rw [h]
    have e2 : ∑ i ∈ Finset.univ.filter (fun i : Fin (k - 1) => i.val ≠ 0), len' i
        = m - P.len j - P.len ⟨(j.val + 1) % k, Nat.mod_lt _ hk⟩ := by
      have e3 : ∑ i ∈ Finset.univ.filter (fun i : Fin (k - 1) => i.val ≠ 0), len' i
          = ∑ i ∈ Finset.univ.filter (fun i : Fin (k - 1) => i.val ≠ 0),
            P.len ⟨(j.val + 1 + i.val) % k, Nat.mod_lt _ hk⟩ := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        simp only [hlen'_def, hi, if_false]
      rw [e3]
      rw [show (∑ i ∈ Finset.univ.filter (fun i : Fin (k - 1) => i.val ≠ 0),
          P.len ⟨(j.val + 1 + i.val) % k, Nat.mod_lt _ hk⟩)
          = ∑ s ∈ Finset.Ico (j.val + 2) (j.val + k), P.len ⟨s % k, Nat.mod_lt s hk⟩ from ?_]
      · have e4 : (∑ i ∈ Finset.range (j.val + k), P.len ⟨i % k, Nat.mod_lt i hk⟩)
            = P.offExt hk (j.val + k) := by rw [offExt]
        have e5 : (∑ i ∈ Finset.range (j.val + 2), P.len ⟨i % k, Nat.mod_lt i hk⟩)
            = P.offExt hk (j.val + 2) := by rw [offExt]
        have e6 : (∑ i ∈ Finset.range (j.val + 2), P.len ⟨i % k, Nat.mod_lt i hk⟩)
            + ∑ s ∈ Finset.Ico (j.val + 2) (j.val + k), P.len ⟨s % k, Nat.mod_lt s hk⟩
            = ∑ i ∈ Finset.range (j.val + k), P.len ⟨i % k, Nat.mod_lt i hk⟩ :=
          Finset.sum_range_add_sum_Ico _ (by omega)
        rw [e4, e5, offExt_add_period, hoff2, hofj] at e6
        omega
      · apply Finset.sum_bij (fun i _ => j.val + 1 + i.val)
        · intro i hi
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
          simp only [Finset.mem_Ico]
          omega
        · intro i₁ _ i₂ _ h
          exact Fin.ext (by omega)
        · intro b hb
          simp only [Finset.mem_Ico] at hb
          refine ⟨⟨b - j.val - 1, by omega⟩, ?_, ?_⟩
          · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            omega
          · show j.val + 1 + (b - j.val - 1) = b
            omega
        · intro i _
          rfl
    have e1 : ∑ i, len' i = (H + T) + ∑ i ∈ Finset.univ.filter (fun i : Fin (k - 1) => i.val ≠ 0),
        len' i := by
      rw [← Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset (Fin (k - 1))))
        (p := fun i => i.val = 0) (f := len')]
      congr 1
      rw [hz, Finset.sum_singleton]
      simp only [hlen'_def, if_pos rfl]
    rw [e1, e2, hHT]
    omega
  set P' : CirclePartition (m - l) (k - 1) :=
    { base := base', len := len', len_pos := hlen'_pos, len_sum := hlen'_sum } with hP'_def
  have hP'base : P'.base = base' := rfl
  have hP'len : P'.len = len' := rfl
  have hperW' : ∀ t : ℕ, P'.perW (w ∘ skipMap a₀ l) t
      = P.perW w (p + l + (base'.val + t) % (m - l)) := by
    intro t
    rw [perW, Function.comp_apply, skipMap]
    have e1 : (P'.base + (t : ZMod (m - l))).val = (base'.val + t) % (m - l) := by
      have e2 : ((t : ZMod (m - l)).val) = t % (m - l) := ZMod.val_natCast (m - l) t
      rw [ZMod.val_add, e2, Nat.add_mod_mod, hP'base]
    rw [e1, perW, ← hp1]
    congr 1
    rw [Nat.cast_add, Nat.cast_add]
    abel
  have off'_eq : ∀ n (hn : 1 ≤ n) (hn2 : n < k - 1),
      P'.off ⟨n, hn2⟩ = P.offExt hk (j.val + 1 + n) - P.off j - l := by
    intro n hn
    induction n with
    | zero => omega
    | succ n ih =>
      intro hn2
      by_cases hn0 : n = 0
      · subst hn0
        have h1 : P'.off ⟨0 + 1, hn2⟩ = P'.off ⟨0, hk'⟩ + P'.len ⟨0, hk'⟩ :=
          off_succ P' ⟨0, hk'⟩ hn2
        rw [h1, off_zero P' hk', hP'len]
        simp only [hlen'_def, if_pos rfl, zero_add]
        rw [hHT, hoff2, hofj]
        omega
      · have ih' := ih (by omega) (by omega)
        have h1 : P'.off ⟨n + 1, hn2⟩ = P'.off ⟨n, by omega⟩ + P'.len ⟨n, by omega⟩ :=
          off_succ P' ⟨n, by omega⟩ hn2
        have hge : P.off j + l ≤ P.offExt hk (j.val + 1 + n) := by
          have h2 : P.offExt hk (j.val + 2) ≤ P.offExt hk (j.val + 1 + n) := by
            apply P.offExt_mono hk
            omega
          rw [hoff2, hofj] at h2
          omega
        rw [h1, ih', hP'len]
        simp only [hlen'_def, hn0, if_false]
        rw [show j.val + 1 + (n + 1) = j.val + 1 + n + 1 by omega, offExt_succ]
        omega
  refine ⟨P', ?_⟩
  intro i
  by_cases hi0 : i.val = 0
  · have hlen0 : P'.len i = H + T := by
      rw [hP'len]
      simp only [hlen'_def, hi0, if_true]
    have hoff0 : P'.off i = 0 := by
      rw [show i = ⟨0, hk'⟩ from Fin.ext hi0]
      exact off_zero P' hk'
    rw [sum_arcOf P' hk' i (w ∘ skipMap a₀ l), hoff0, hlen0, zero_add]
    have hsplit : ∑ t ∈ Finset.Ico 0 (H + T), P'.perW (w ∘ skipMap a₀ l) t
        = (∑ t ∈ Finset.Ico 0 H, P'.perW (w ∘ skipMap a₀ l) t)
          + ∑ t ∈ Finset.Ico H (H + T), P'.perW (w ∘ skipMap a₀ l) t := by
      rw [Finset.sum_Ico_consecutive _ (by omega : 0 ≤ H) (by omega : H ≤ H + T)]
    rw [hsplit]
    have hpart1 : ∑ t ∈ Finset.Ico 0 H, P'.perW (w ∘ skipMap a₀ l) t
        = ∑ t ∈ Finset.Ico (P.off j) p, P.perW w t := by
      rw [Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
      apply Finset.sum_congr rfl
      intro t ht
      rw [Finset.mem_range] at ht
      by_cases hH0 : H = 0
      · rw [hH0] at ht
        omega
      · have hbv : base'.val = m - l - H := by
          rw [hbase'_def, ZMod.val_natCast (m - l) (m - l - H),
            Nat.mod_eq_of_lt (by omega)]
        rw [hperW' (0 + t), hbv, show m - l - H + (0 + t) = m - l - H + t by omega,
          Nat.mod_eq_of_lt (by omega : m - l - H + t < m - l)]
        have e : p + l + (m - l - H + t) = (p - H + t) + m := by omega
        rw [e, perW_periodic]
        have e2 : p - H + t = P.off j + t := by omega
        rw [e2]
    have hpart2 : ∑ t ∈ Finset.Ico H (H + T), P'.perW (w ∘ skipMap a₀ l) t
        = ∑ t ∈ Finset.Ico (p + l) (P.offExt hk (j.val + 2)), P.perW w t := by
      rw [show P.offExt hk (j.val + 2) = p + l + T by omega]
      rw [Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
      simp only [Nat.add_sub_cancel_left]
      apply Finset.sum_congr rfl
      intro t ht
      rw [Finset.mem_range] at ht
      by_cases hH0 : H = 0
      · have hbv : base'.val = 0 := by
          rw [hbase'_def, hH0, Nat.sub_zero, ZMod.val_natCast (m - l) (m - l), Nat.mod_self]
        rw [hperW' (H + t), hH0, hbv]
        simp only [zero_add]
        rw [Nat.mod_eq_of_lt (by omega : t < m - l)]
      · have hbv : base'.val = m - l - H := by
          rw [hbase'_def, ZMod.val_natCast (m - l) (m - l - H),
            Nat.mod_eq_of_lt (by omega)]
        rw [hperW' (H + t), hbv]
        have e1 : m - l - H + (H + t) = (m - l) + t := by omega
        rw [e1, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega : t < m - l)]
    have hvj : ∑ x ∈ P.arcOf j, w x
        = ∑ t ∈ Finset.Ico (P.off j) (P.off j + P.len j), P.perW w t :=
      sum_arcOf P hk j w
    have hvj1 : ∑ x ∈ P.arcOf ⟨(j.val + 1) % k, Nat.mod_lt _ hk⟩, w x
        = ∑ t ∈ Finset.Ico (P.offExt hk (j.val + 1))
          (P.offExt hk (j.val + 1) + P.len ⟨(j.val + 1) % k, Nat.mod_lt _ hk⟩), P.perW w t :=
      (sum_arcOf_ext P hk (j.val + 1) (j := ⟨(j.val + 1) % k, Nat.mod_lt _ hk⟩) rfl w).symm
    have h1 := hval j
    have h2 := hval ⟨(j.val + 1) % k, Nat.mod_lt _ hk⟩
    have hA2 : ∑ t ∈ Finset.Ico p (p + l), P.perW w t < 1 := hAIco ▸ hA
    have hV : ∑ t ∈ Finset.Ico (P.off j) (P.off j + P.len j), P.perW w t
        + ∑ t ∈ Finset.Ico (P.offExt hk (j.val + 1))
          (P.offExt hk (j.val + 1) + P.len ⟨(j.val + 1) % k, Nat.mod_lt _ hk⟩), P.perW w t
        = ∑ t ∈ Finset.Ico (P.off j) (P.offExt hk (j.val + 2)), P.perW w t := by
      rw [← offExt_succ_fin P hk j,
        show P.offExt hk (j.val + 1) + P.len ⟨(j.val + 1) % k, Nat.mod_lt _ hk⟩
          = P.offExt hk (j.val + 2) by
          rw [show j.val + 2 = (j.val + 1) + 1 by omega, offExt_succ P hk (j.val + 1)]]
      exact Finset.sum_Ico_consecutive _
        (by rw [hofj]; exact P.offExt_mono hk (by omega))
        (P.offExt_mono hk (by omega))
    have hVsplit : ∑ t ∈ Finset.Ico (P.off j) (P.offExt hk (j.val + 2)), P.perW w t
        = ∑ t ∈ Finset.Ico (P.off j) p, P.perW w t
          + ∑ t ∈ Finset.Ico p (p + l), P.perW w t
          + ∑ t ∈ Finset.Ico (p + l) (P.offExt hk (j.val + 2)), P.perW w t := by
      rw [← Finset.sum_Ico_consecutive _ (by omega : P.off j ≤ p + l) hpl,
        ← Finset.sum_Ico_consecutive _ (by omega : P.off j ≤ p) (by omega : p ≤ p + l)]
    rw [hpart1, hpart2]
    linarith
  · have hleni : P'.len i = P.len ⟨(j.val + 1 + i.val) % k, Nat.mod_lt _ hk⟩ := by
      rw [hP'len]
      simp only [hlen'_def, hi0, if_false]
    have hoffi : P'.off i = P.offExt hk (j.val + 1 + i.val) - P.off j - l := by
      have h3 := off'_eq i.val (by omega) i.isLt
      rw [show i = ⟨i.val, i.isLt⟩ from Fin.eta i _]
      exact h3
    have hbound : P.offExt hk (j.val + 1 + i.val) - P.off j - l + P.len ⟨(j.val + 1 + i.val) % k,
        Nat.mod_lt _ hk⟩ ≤ m - l := by
      have h1 : P.offExt hk (j.val + 2 + i.val) ≤ P.offExt hk (j.val + k) := by
        apply P.offExt_mono hk
        omega
      rw [show j.val + 2 + i.val = (j.val + 1 + i.val) + 1 by omega, offExt_succ,
        offExt_add_period] at h1
      have h2 : P.offExt hk (j.val + 2) ≤ P.offExt hk (j.val + 1 + i.val) := by
        apply P.offExt_mono hk
        omega
      rw [hoff2, hofj] at h2
      omega
    rw [sum_arcOf P' hk' i (w ∘ skipMap a₀ l), hoffi, hleni, Finset.sum_Ico_eq_sum_range,
      Nat.add_sub_cancel_left]
    have hoffH : H ≤ P.offExt hk (j.val + 1 + i.val) - P.off j - l := by
      have h1 : P.offExt hk (j.val + 2) ≤ P.offExt hk (j.val + 1 + i.val) := by
        apply P.offExt_mono hk
        omega
      rw [hoff2, hofj] at h1
      omega
    have hge2 : P.off j + l ≤ P.offExt hk (j.val + 1 + i.val) := by
      have h1 : P.offExt hk (j.val + 2) ≤ P.offExt hk (j.val + 1 + i.val) := by
        apply P.offExt_mono hk
        omega
      omega
    have hpt : ∀ t : ℕ, t < P.len ⟨(j.val + 1 + i.val) % k, Nat.mod_lt _ hk⟩ →
        P'.perW (w ∘ skipMap a₀ l) (P.offExt hk (j.val + 1 + i.val) - P.off j - l + t)
        = P.perW w (P.offExt hk (j.val + 1 + i.val) + t) := by
      intro t ht
      rw [hperW']
      have hX2 : P.offExt hk (j.val + 1 + i.val) - P.off j - l + t < m - l := by
        have hb := hbound
        omega
      by_cases hH0 : H = 0
      · have hbv : base'.val = 0 := by
          rw [hbase'_def, hH0, Nat.sub_zero, ZMod.val_natCast (m - l) (m - l), Nat.mod_self]
        rw [hbv, zero_add, Nat.mod_eq_of_lt hX2]
        have e2 : p + l + (P.offExt hk (j.val + 1 + i.val) - P.off j - l + t)
            = P.offExt hk (j.val + 1 + i.val) + t := by
          omega
        rw [e2]
      · have hbv : base'.val = m - l - H := by
          rw [hbase'_def, ZMod.val_natCast (m - l) (m - l - H),
            Nat.mod_eq_of_lt (by omega)]
        rw [hbv]
        have hX1 : H ≤ P.offExt hk (j.val + 1 + i.val) - P.off j - l + t :=
          le_trans hoffH (by omega)
        have e1 : (m - l - H + (P.offExt hk (j.val + 1 + i.val) - P.off j - l + t)) % (m - l)
            = (m - l - H + (P.offExt hk (j.val + 1 + i.val) - P.off j - l + t)) - (m - l) := by
          rw [Nat.mod_eq_sub_mod (by omega : m - l ≤ m - l - H +
              (P.offExt hk (j.val + 1 + i.val) - P.off j - l + t)),
            Nat.mod_eq_of_lt (by omega : (m - l - H +
              (P.offExt hk (j.val + 1 + i.val) - P.off j - l + t)) - (m - l) < m - l)]
        rw [e1]
        have e2 : p + l + ((m - l - H + (P.offExt hk (j.val + 1 + i.val) - P.off j - l + t))
            - (m - l)) = P.offExt hk (j.val + 1 + i.val) + t := by
          omega
        rw [e2]
    rw [show ∑ t ∈ Finset.range (P.len ⟨(j.val + 1 + i.val) % k, Nat.mod_lt _ hk⟩),
        P'.perW (w ∘ skipMap a₀ l) (P.offExt hk (j.val + 1 + i.val) - P.off j - l + t)
        = ∑ t ∈ Finset.range (P.len ⟨(j.val + 1 + i.val) % k, Nat.mod_lt _ hk⟩),
          P.perW w (P.offExt hk (j.val + 1 + i.val) + t) from
        Finset.sum_congr rfl (fun t ht => hpt t (Finset.mem_range.mp ht))]
    have hfin : ∑ t ∈ Finset.range (P.len ⟨(j.val + 1 + i.val) % k, Nat.mod_lt _ hk⟩),
        P.perW w (P.offExt hk (j.val + 1 + i.val) + t)
        = ∑ t ∈ Finset.Ico (P.offExt hk (j.val + 1 + i.val))
          (P.offExt hk (j.val + 1 + i.val) + P.len ⟨(j.val + 1 + i.val) % k, Nat.mod_lt _ hk⟩),
          P.perW w t := by
      rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
    rw [hfin, sum_arcOf_ext P hk (j.val + 1 + i.val) (j := ⟨(j.val + 1 + i.val) % k, Nat.mod_lt _ hk⟩) rfl w]
    exact hval _


/-- Reindexing a circular partition along an equality of the number of arcs. -/
def cast {m a b : ℕ} (h : a = b) (P : CirclePartition m a) :
    CirclePartition m b where
  base := P.base
  len := fun i => P.len (Fin.cast h.symm i)
  len_pos := fun i => P.len_pos _
  len_sum := by
    subst h
    simp only [Fin.cast_refl, id_eq]
    exact P.len_sum

lemma circlePartition_cast_len {m a b : ℕ} (h : a = b) (P : CirclePartition m a) (i : Fin b) :
    (CirclePartition.cast h P).len i = P.len (Fin.cast h.symm i) := rfl

lemma circlePartition_cast_off {m a b : ℕ} (h : a = b) (P : CirclePartition m a) (i : Fin b) :
    (CirclePartition.cast h P).off i = P.off (Fin.cast h.symm i) := by
  subst h
  simp only [Fin.cast_refl, id_eq]
  rw [off, off]
  apply Finset.sum_congr rfl
  intro j _
  rfl

lemma circlePartition_cast_arcOf {m a b : ℕ} (h : a = b) (P : CirclePartition m a) (i : Fin b) :
    (CirclePartition.cast h P).arcOf i = P.arcOf (Fin.cast h.symm i) := by
  have e1 : (CirclePartition.cast h P).start i = P.start (Fin.cast h.symm i) := by
    rw [start, start, circlePartition_cast_off h P i]
    rfl
  rw [arcOf, arcOf, e1, circlePartition_cast_len h P i]

/-- The multi-arc merge lemma: deleting `t` disjoint arcs, each of value `< 1`,
yields a smaller circle with a partition into `k - t` arcs of value `≥ 1`. -/
lemma mergeValues {t : ℕ} :
    ∀ {m k : ℕ} [NeZero m] (P : CirclePartition m k) (_hk : 0 < k)
    (ca : Fin t → ZMod m) (la : Fin t → ℕ) (w : ZMod m → ℝ)
    (_hnn : ∀ x, 0 ≤ w x) (_hval : ∀ i, 1 ≤ ∑ x ∈ P.arcOf i, w x)
    (_hla1 : ∀ s, 1 ≤ la s) (_hlam : ∀ s, la s ≤ m)
    (_hdij : ∀ s₁ s₂, s₁ ≠ s₂ → Disjoint (arcSet (ca s₁) (la s₁)) (arcSet (ca s₂) (la s₂)))
    (_harcval : ∀ s, ∑ x ∈ arcSet (ca s) (la s), w x < 1)
    (_htk : t < k)
    {m' : ℕ} [NeZero m'] (φ : ZMod m' → ZMod m)
    {hD : (Finset.univ.biUnion fun s => arcSet (ca s) (la s)) ≠ Finset.univ}
    (_hφ : CircleEmb _ hD φ),
    ∃ P' : CirclePartition m' (k - t), ∀ i, 1 ≤ ∑ x ∈ P'.arcOf i, (w ∘ φ) x := by
  induction t with
  | zero =>
    intro m k hm P hk ca la w hnn hval _ _ _ _ _ m' hm' φ hD hφ
    have hk0 : k - 0 = k := Nat.sub_zero k
    have hD0 : (Finset.univ.biUnion fun s : Fin 0 => arcSet (ca s) (la s)) = ∅ := by
      simp [Finset.univ_eq_empty]
    have hφ0 : CircleEmb ∅ Finset.univ_nonempty.ne_empty.symm φ := CircleEmb.congr_D hD0 hφ
    -- φ is a rotation
    have hnext : ∀ i : ZMod m', φ (i + 1) = φ i + 1 := by
      intro i
      have h1 := hφ0.next i
      have h2 : nextD ∅ Finset.univ_nonempty.ne_empty.symm (φ i) = φ i + 1 := by
        have hg : gapSize ∅ Finset.univ_nonempty.ne_empty.symm (φ i) = 1 := by
          apply le_antisymm
          · exact Nat.find_min' (exists_gap ∅ Finset.univ_nonempty.ne_empty.symm (φ i))
              ⟨le_refl 1, Nat.pos_of_ne_zero (NeZero.ne m), by simp⟩
          · exact (gapSize_spec ∅ _ (φ i)).1
        rw [nextD, hg, Nat.cast_one]
      rw [h2] at h1
      exact h1
    have hiter : ∀ n : ℕ, ∀ i : ZMod m', φ (i + (n : ZMod m')) = φ i + (n : ZMod m) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        intro i
        have e1 : (i + ((n + 1 : ℕ) : ZMod m')) = (i + ((n : ℕ) : ZMod m')) + 1 := by
          rw [Nat.cast_add, Nat.cast_one]
          abel
        rw [e1, hnext, ih]
        rw [Nat.cast_add, Nat.cast_one]
        abel
    have hm'm : m' = m := by
      have hcard : m' ≤ m := by
        have h := Fintype.card_le_of_injective φ hφ.inj
        rwa [ZMod.card, ZMod.card] at h
      have hdvd : m ∣ m' := by
        have h2 := hiter m' 0
        rw [zero_add, ZMod.natCast_self] at h2
        have h3 : φ 0 = φ 0 + ((m' : ℕ) : ZMod m) := h2
        have h4 : φ 0 + 0 = φ 0 + ((m' : ℕ) : ZMod m) := by
          rw [add_zero]
          exact h3
        have h5 : ((m' : ℕ) : ZMod m) = 0 := (add_left_cancel h4).symm
        exact (ZMod.natCast_eq_zero_iff m' m).mp h5
      exact Nat.le_antisymm hcard (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne m')) hdvd)
    have hm'm2 : m = m' := hm'm.symm
    subst hm'm2
    have hrot : ∀ y : ZMod m, φ y = φ 0 + (y.val : ZMod m) := by
      intro y
      have h1 := hiter y.val 0
      rw [zero_add] at h1
      have h3 : φ ((y.val : ZMod m)) = φ y := by
        rw [ZMod.natCast_val, ZMod.cast_id]
      rw [h3] at h1
      exact h1
    refine ⟨⟨P.base - φ 0, P.len, P.len_pos, P.len_sum⟩, ?_⟩
    intro i
    have hval_i : ∑ x ∈ (⟨P.base - φ 0, P.len, P.len_pos, P.len_sum⟩ : CirclePartition m k).arcOf i,
        (w ∘ φ) x = ∑ x ∈ P.arcOf i, w x := by
      rw [arcOf, arcOf, sum_arcSet (P.len_le hk i) w, sum_arcSet (P.len_le hk i) (w ∘ φ)]
      apply Finset.sum_congr rfl
      intro t _
      rw [Function.comp_apply]
      have e1 : (⟨P.base - φ 0, P.len, P.len_pos, P.len_sum⟩ : CirclePartition m k).start i
          = (P.base - φ 0) + (P.off i : ZMod m) := rfl
      rw [e1, hrot]
      have e4 : (((P.base - φ 0) + (P.off i : ZMod m) + (t : ZMod m)).val : ZMod m)
          = (P.base - φ 0) + (P.off i : ZMod m) + (t : ZMod m) := by
        rw [ZMod.natCast_val, ZMod.cast_id]
      rw [e4, start]
      abel_nf
    rw [hval_i]
    exact hval i
  | succ t ih =>
    intro m k hm P hk ca la w hnn hval hla1 hlam hdij harcval htk m' hm' φ hD hφ
    have hk2 : 2 ≤ k := by omega
    have hk' : 0 < k - 1 := by omega
    obtain ⟨P₁, hP₁⟩ := mergeOne P hk hk2 w hnn hval (hla1 0) (hlam 0) (harcval 0)
    have hl0 : la 0 < m := by
      have h1 := hlam 0
      rcases Nat.eq_or_lt_of_le h1 with h2 | h2
      · exfalso
        have huniv : arcSet (ca 0) (la 0) = Finset.univ := by rw [h2, arcSet_univ]
        have hge : 1 ≤ ∑ x : ZMod m, w x := by
          have h1 := hval ⟨0, hk⟩
          exact le_trans h1 (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun x _ _ => hnn x))
        have h1 := harcval 0
        rw [huniv] at h1
        linarith
      · exact h2
    have : NeZero (m - la 0) := ⟨by omega⟩
    have htr : ∀ s : Fin t, ∃ v : ZMod (m - la 0), la s.succ ≤ m - la 0 ∧
      (arcSet v (la s.succ)).image (skipMap (ca 0) (la 0)) = arcSet (ca s.succ) (la s.succ) ∧
      (∀ w : ZMod m → ℝ, ∑ x ∈ arcSet (ca s.succ) (la s.succ), w x
        = ∑ y ∈ arcSet v (la s.succ), w (skipMap (ca 0) (la 0) y)) := by
      intro s
      exact transport_arc (hla1 0) (hlam 0) (hla1 s.succ)
        (hdij 0 s.succ (Fin.succ_ne_zero s).symm)
    choose v hvle himg hsum using htr
    have hdij' : ∀ s₁ s₂ : Fin t, s₁ ≠ s₂ →
        Disjoint (arcSet (v s₁) (la s₁.succ)) (arcSet (v s₂) (la s₂.succ)) := by
      intro s₁ s₂ h
      rw [Finset.disjoint_left]
      intro x hx₁ hx₂
      have h1 : skipMap (ca 0) (la 0) x ∈ arcSet (ca s₁.succ) (la s₁.succ) := by
        rw [← himg s₁]
        exact Finset.mem_image_of_mem _ hx₁
      have h2 : skipMap (ca 0) (la 0) x ∈ arcSet (ca s₂.succ) (la s₂.succ) := by
        rw [← himg s₂]
        exact Finset.mem_image_of_mem _ hx₂
      exact Finset.disjoint_left.mp
        (hdij s₁.succ s₂.succ (fun hh => h (Fin.succ_inj.mp hh))) h1 h2
    have harcval' : ∀ s : Fin t, ∑ y ∈ arcSet (v s) (la s.succ), (w ∘ skipMap (ca 0) (la 0)) y
        < 1 := by
      intro s
      have h1 := harcval s.succ
      rw [hsum s w] at h1
      exact h1
    have hdecomp : arcSet (ca 0) (la 0) ∪ (Finset.univ.biUnion fun s : Fin t =>
        arcSet (v s) (la s.succ)).image (skipMap (ca 0) (la 0))
        = Finset.univ.biUnion fun s : Fin (t + 1) => arcSet (ca s) (la s) := by
      have hb : ((Finset.univ.biUnion fun s : Fin t => arcSet (v s) (la s.succ)).image
          (skipMap (ca 0) (la 0)))
          = Finset.univ.biUnion fun s : Fin t =>
            (arcSet (v s) (la s.succ)).image (skipMap (ca 0) (la 0)) := by
        ext x
        simp only [Finset.mem_image, Finset.mem_biUnion]
        tauto
      rw [hb]
      ext x
      rw [Finset.mem_union, Finset.mem_biUnion, Finset.mem_biUnion]
      constructor
      · rintro (h | ⟨s, _, hs⟩)
        · exact ⟨0, Finset.mem_univ _, h⟩
        · rw [himg s] at hs
          exact ⟨s.succ, Finset.mem_univ _, hs⟩
      · rintro ⟨s, _, hs⟩
        rcases Fin.eq_zero_or_eq_succ s with rfl | ⟨s', rfl⟩
        · exact Or.inl hs
        · exact Or.inr ⟨s', Finset.mem_univ _, by rw [himg s']; exact hs⟩
    have hD' : (Finset.univ.biUnion fun s : Fin t => arcSet (v s) (la s.succ))
        ≠ Finset.univ := by
      intro huniv
      apply hD
      rw [← hdecomp]
      apply Finset.eq_univ_of_forall
      intro x
      rw [Finset.mem_union]
      by_cases hx : x ∈ arcSet (ca 0) (la 0)
      · exact Or.inl hx
      · right
        obtain ⟨i, hi⟩ := skipMap_cover (Nat.le_of_lt hl0) x hx
        have hxi : i ∈ (Finset.univ.biUnion fun s : Fin t => arcSet (v s) (la s.succ)) := by
          rw [huniv]
          exact Finset.mem_univ i
        rw [← hi]
        exact Finset.mem_image_of_mem _ hxi
    obtain ⟨φ', hφ'comp, hφ'⟩ := circleEmb_factor (Nat.le_of_lt hl0) _ hD' _ hD hdecomp.symm φ hφ
    have htk' : t < k - 1 := by omega
    obtain ⟨P', hP'⟩ := ih P₁ hk' v (fun s => la s.succ) (w ∘ skipMap (ca 0) (la 0))
      (fun x => hnn _) hP₁ (fun s => hla1 s.succ) hvle hdij' harcval' htk' φ' hφ'
    have hcast : (k - 1) - t = k - (t + 1) := by omega
    refine ⟨CirclePartition.cast hcast P', ?_⟩
    intro i
    rw [circlePartition_cast_arcOf hcast P' i]
    have h1 := hP' (Fin.cast hcast.symm i)
    rwa [show (w ∘ skipMap (ca 0) (la 0)) ∘ φ' = w ∘ φ from funext fun x => by
      rw [Function.comp_apply, Function.comp_apply, Function.comp_apply,
        show skipMap (ca 0) (la 0) (φ' x) = φ x from congr_fun hφ'comp x]] at h1


theorem hall_deficiency {n : ℕ} [NeZero n] (r : Fin n → Fin n → Prop) [DecidableRel r]
    (pip : Fin n) (hpip : ∀ j, r pip j) :
    ∃ (M T : Finset (Fin n)) (f : Fin n → Fin n),
      pip ∈ M ∧
      T.card = M.card ∧
      (∀ p ∈ M, f p ∈ T ∧ r p (f p)) ∧
      (∀ p₁ ∈ M, ∀ p₂ ∈ M, f p₁ = f p₂ → p₁ = p₂) ∧
      (∀ p, p ∉ M → ∀ j ∈ T, ¬ r p j) := by
  classical
  -- neighborhood of a person: the set of jobs they are compatible with
  set N : Fin n → Finset (Fin n) := fun p => Finset.univ.filter (r p) with hN
  -- the deficiency of a set of people
  set d : Finset (Fin n) → ℤ := fun B => (B.card : ℤ) - (B.biUnion N).card with hd
  have hd_apply : ∀ B : Finset (Fin n), d B = (B.card : ℤ) - ((B.biUnion N).card : ℤ) :=
    fun B => rfl
  -- pick a set B of maximal deficiency
  obtain ⟨B, -, hBmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (Finset (Fin n))) d ⟨∅, Finset.mem_univ _⟩
  rcases le_or_gt (d B) 0 with hdB | hdB
  · -- Case 1: maximal deficiency ≤ 0, so Hall's condition holds; match everybody
    have hHall : ∀ s : Finset (Fin n), s.card ≤ (s.biUnion N).card := by
      intro s
      have hs := hBmax s (Finset.mem_univ s)
      rw [hd_apply s] at hs
      have hle : (s.card : ℤ) ≤ ((s.biUnion N).card : ℤ) := by omega
      exact_mod_cast hle
    obtain ⟨f, hinj, hf⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective N).mp hHall
    refine ⟨Finset.univ, Finset.univ, f, Finset.mem_univ _, rfl, ?_, ?_, ?_⟩
    · intro p _
      have hfp : f p ∈ Finset.univ.filter (r p) := hf p
      exact ⟨Finset.mem_univ _, (Finset.mem_filter.mp hfp).2⟩
    · intro p₁ _ p₂ _ h
      exact hinj h
    · intro p hp
      exact absurd (Finset.mem_univ p) hp
  · -- Case 2: maximal deficiency ≥ 1
    -- pip cannot lie in B, since N pip = univ would force the deficiency of B to be ≤ 0
    have hpipB : pip ∉ B := by
      intro hmem
      have hNp : N pip = Finset.univ := by
        apply Finset.eq_univ_of_forall
        intro j
        have hj : j ∈ Finset.univ.filter (r pip) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ j, hpip j⟩
        exact hj
      have hsub : (Finset.univ : Finset (Fin n)) ⊆ B.biUnion N := by
        rw [← hNp]
        exact Finset.subset_biUnion_of_mem N hmem
      have hZ : B.biUnion N = Finset.univ := le_antisymm (Finset.subset_univ _) hsub
      have hZcard : (B.biUnion N).card = n := by rw [hZ, Finset.card_univ, Fintype.card_fin]
      have hBcard : (B.card : ℤ) ≤ (n : ℤ) := by
        have h := Finset.card_le_univ B
        rw [Fintype.card_fin] at h
        exact_mod_cast h
      have hdBexp := hd_apply B
      omega
    set M : Finset (Fin n) := Finset.univ \ B with hM
    set Y : Finset (Fin n) := Finset.univ \ B.biUnion N with hY
    have hpipM : pip ∈ M := Finset.mem_sdiff.mpr ⟨Finset.mem_univ pip, hpipB⟩
    -- restricted Hall condition on M, from maximality of B
    have hRestr : ∀ s : Finset (Fin n), s ⊆ M → s.card ≤ ((s.biUnion N) ∩ Y).card := by
      intro s hsM
      have hdisj : Disjoint B s := by
        rw [Finset.disjoint_left]
        intro a haB has
        have haM : a ∈ M := hsM has
        rw [hM, Finset.mem_sdiff] at haM
        exact haM.2 haB
      have hcard_union : (B ∪ s).card = B.card + s.card := Finset.card_union_of_disjoint hdisj
      have hbiU : (B ∪ s).biUnion N = (B.biUnion N) ∪ (s.biUnion N) := Finset.union_biUnion
      have hunion : (B.biUnion N) ∪ (s.biUnion N) = (B.biUnion N) ∪ ((s.biUnion N) ∩ Y) := by
        ext j
        simp only [Finset.mem_union, Finset.mem_inter, hY, Finset.mem_sdiff, Finset.mem_univ,
          true_and]
        tauto
      have hdisj2 : Disjoint (B.biUnion N) ((s.biUnion N) ∩ Y) := by
        rw [Finset.disjoint_left]
        intro j hjZ hjW
        have hjY : j ∈ Y := (Finset.mem_inter.mp hjW).2
        rw [hY, Finset.mem_sdiff] at hjY
        exact hjY.2 hjZ
      have hcard2 : ((B.biUnion N) ∪ ((s.biUnion N) ∩ Y)).card =
          (B.biUnion N).card + ((s.biUnion N) ∩ Y).card :=
        Finset.card_union_of_disjoint hdisj2
      have hmax := hBmax (B ∪ s) (Finset.mem_univ _)
      rw [hd_apply (B ∪ s), hd_apply B, hcard_union, hbiU, hunion, hcard2] at hmax
      omega
    -- Hall's theorem applied to the subtype of M
    have hHallSub : ∀ s : Finset {x // x ∈ M},
        s.card ≤ (s.biUnion (fun p => N p.val ∩ Y)).card := by
      intro s
      set s' : Finset (Fin n) := s.image Subtype.val with hs'
      have hs'card : s'.card = s.card := by
        rw [hs']
        exact Finset.card_image_of_injective s Subtype.val_injective
      have hs'M : s' ⊆ M := by
        intro x hx
        rw [hs', Finset.mem_image] at hx
        obtain ⟨p, _, rfl⟩ := hx
        exact p.property
      have hEq : s.biUnion (fun p => N p.val ∩ Y) = (s'.biUnion N) ∩ Y := by
        apply le_antisymm
        · intro j hj
          rw [Finset.mem_biUnion] at hj
          obtain ⟨p, hp, hjp⟩ := hj
          have hjp' := Finset.mem_inter.mp hjp
          rw [Finset.mem_inter, Finset.mem_biUnion]
          exact ⟨⟨p.val, Finset.mem_image_of_mem _ hp, hjp'.1⟩, hjp'.2⟩
        · intro j hj
          rw [Finset.mem_inter, Finset.mem_biUnion] at hj
          obtain ⟨⟨x, hx, hjx⟩, hjY⟩ := hj
          rw [hs', Finset.mem_image] at hx
          obtain ⟨p, hp, rfl⟩ := hx
          rw [Finset.mem_biUnion]
          exact ⟨p, hp, Finset.mem_inter.mpr ⟨hjx, hjY⟩⟩
      rw [hEq, ← hs'card]
      exact hRestr s' hs'M
    obtain ⟨f', hinj', hf'⟩ :=
      (Finset.all_card_le_biUnion_card_iff_exists_injective
        (fun p : {x // x ∈ M} => N p.val ∩ Y)).mp hHallSub
    -- extend f' to all of Fin n by the identity outside M
    set f : Fin n → Fin n := fun p => if h : p ∈ M then f' ⟨p, h⟩ else p with hf
    have hfM : ∀ (p : Fin n) (hp : p ∈ M), f p = f' ⟨p, hp⟩ := fun p hp => dif_pos hp
    set T : Finset (Fin n) := M.image f with hT
    have hinjM : Set.InjOn f M := by
      intro p₁ hp₁ p₂ hp₂ h
      rw [hfM p₁ hp₁, hfM p₂ hp₂] at h
      exact congrArg Subtype.val (hinj' h)
    have hTcard : T.card = M.card := by
      rw [hT]
      exact Finset.card_image_of_injOn hinjM
    refine ⟨M, T, f, hpipM, hTcard, ?_, ?_, ?_⟩
    · intro p hpM
      refine ⟨Finset.mem_image_of_mem f hpM, ?_⟩
      have h1 : f p ∈ N p ∩ Y := by
        rw [hfM p hpM]
        exact hf' ⟨p, hpM⟩
      have h2 : f p ∈ Finset.univ.filter (r p) := (Finset.mem_inter.mp h1).1
      exact (Finset.mem_filter.mp h2).2
    · intro p₁ hp₁ p₂ hp₂ h
      exact hinjM hp₁ hp₂ h
    · intro p hpM j hjT hrpj
      have hpB : p ∈ B := by
        by_contra hpB
        exact hpM (Finset.mem_sdiff.mpr ⟨Finset.mem_univ p, hpB⟩)
      rw [hT, Finset.mem_image] at hjT
      obtain ⟨q, hqM, hqf⟩ := hjT
      have hjY : j ∈ Y := by
        have h1 : j ∈ N q ∩ Y := by
          rw [← hqf, hfM q hqM]
          exact hf' ⟨q, hqM⟩
        exact (Finset.mem_inter.mp h1).2
      rw [hY, Finset.mem_sdiff] at hjY
      have hjNp : j ∈ N p := by
        have h2 : j ∈ Finset.univ.filter (r p) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ j, hrpj⟩
        exact h2
      have hsub : N p ⊆ B.biUnion N := Finset.subset_biUnion_of_mem N hpB
      exact hjY.2 (hsub hjNp)

/-- The main theorem: USAMO 2025 Problem 6. -/
theorem usa2025_p6_main (N : ℕ) (hN : 0 < N) : ∀ (m : ℕ) [NeZero m] (_hmn : N ≤ m)
    (like : Fin N → ZMod m → ℝ) (_hnn : ∀ p c, 0 ≤ like p c)
    (_hpart : ∀ p, ∃ P : CirclePartition m N, ∀ i, 1 ≤ ∑ x ∈ P.arcOf i, like p x),
    ∃ a : ZMod m → Fin N, ∀ p, 1 ≤ ∑ c ∈ Finset.univ.filter (a · = p), like p c := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro m hm' hmn like hnn hpart
    rcases Nat.eq_or_lt_of_le hN with rfl | hN2
    · obtain ⟨P, hP⟩ := hpart ⟨0, hN⟩
      have h1 := hP ⟨0, by omega⟩
      have hlen : P.len ⟨0, by omega⟩ = m := by
        have hsum := P.len_sum
        rw [Fin.sum_univ_one] at hsum
        exact hsum
      have huniv : P.arcOf ⟨0, by omega⟩ = Finset.univ := by
        rw [arcOf, hlen, arcSet_univ]
      rw [huniv] at h1
      refine ⟨fun _ => (⟨0, hN⟩ : Fin 1), fun p => ?_⟩
      have hp0 : p = ⟨0, hN⟩ := Subsingleton.elim _ _
      rw [hp0]
      have hfilter : ((Finset.univ : Finset (ZMod m)).filter ((fun x => (⟨0, hN⟩ : Fin 1))
          · = ⟨0, hN⟩)) = Finset.univ := by
        apply Finset.filter_true_of_mem
        intro x _
        rfl
      rw [hfilter]
      exact h1
    · obtain ⟨Pπ, hPπ⟩ := hpart ⟨0, hN⟩
      classical
      have : NeZero N := ⟨(Nat.ne_of_lt hN).symm⟩
      have hk : 0 < N := hN
      have hk2 : 2 ≤ N := hN2
      obtain ⟨M, T, f, pipM, cardMT, fprop, finj, hate⟩ :=
        hall_deficiency (fun p i => 1 ≤ ∑ x ∈ Pπ.arcOf i, like p x) ⟨0, hN⟩ hPπ
      set B := Finset.univ \ M with hB_def
      set t := M.card with ht_def
      have ht1 : 1 ≤ t := Finset.card_pos.mpr ⟨⟨0, hN⟩, pipM⟩
      have hMT : M.image f = T := by
        apply Finset.eq_of_subset_of_card_le
        · intro y hy
          rw [Finset.mem_image] at hy
          obtain ⟨q, hq, rfl⟩ := hy
          exact (fprop q hq).1
        · rw [Finset.card_image_of_injOn finj, cardMT]
      by_cases hB : B = ∅
      · have hM : M = Finset.univ := by
          rw [hB_def] at hB
          rw [Finset.sdiff_eq_empty_iff_subset] at hB
          exact le_antisymm (Finset.subset_univ M) hB
        have hT : T = Finset.univ := by
          apply Finset.eq_univ_of_card
          rw [cardMT, ht_def, hM, Finset.card_univ]
        have hex : ∀ x : ZMod m, ∃ q ∈ M, x ∈ Pπ.arcOf (f q) := by
          intro x
          obtain ⟨j, hj⟩ := Pπ.arcOf_cover hk x
          have hjT : j ∈ T := by rw [hT]; exact Finset.mem_univ j
          rw [← hMT, Finset.mem_image] at hjT
          obtain ⟨q, hq, rfl⟩ := hjT
          exact ⟨q, hq, hj⟩
        refine ⟨fun x => Classical.choose (hex x), fun q => ?_⟩
        have hspec : ∀ x, Classical.choose (hex x) ∈ M ∧ x ∈ Pπ.arcOf (f (Classical.choose (hex x))) :=
          fun x => Classical.choose_spec (hex x)
        by_cases hqM : q ∈ M
        · have hqset : (Finset.univ.filter (fun x => Classical.choose (hex x) = q))
              = Pπ.arcOf (f q) := by
            ext x
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            constructor
            · intro hxq
              have h1 := (hspec x).2
              rw [hxq] at h1
              exact h1
            · intro hx
              by_cases hff : f (Classical.choose (hex x)) = f q
              · exact finj _ (hspec x).1 _ hqM hff
              · exact absurd (Finset.disjoint_left.mp (Pπ.arcOf_disjoint hk hff) (hspec x).2 hx)
                  (by simp)
          rw [hqset]
          exact (fprop q hqM).2
        · rw [hM] at hqM
          exact absurd (Finset.mem_univ q) hqM
      · have hBne : B.Nonempty := Finset.nonempty_iff_ne_empty.mpr hB
        have hBcard : B.card = N - t := by
          rw [hB_def, Finset.card_sdiff, Finset.card_univ, Fintype.card_fin,
            Finset.inter_univ, ht_def]
        have htN : t < N := by
          have h2 : 1 ≤ B.card := Finset.card_pos.mpr hBne
          omega
        set e := M.orderEmbOfFin rfl with he_def
        have heM : ∀ s : Fin t, e s ∈ M := fun s => M.orderEmbOfFin_mem rfl s
        have himageM : Finset.univ.image e = M := by
          apply Finset.eq_of_subset_of_card_le
          · intro y hy
            rw [Finset.mem_image] at hy
            obtain ⟨s, _, rfl⟩ := hy
            exact heM s
          · rw [Finset.card_image_of_injective _ e.injective]
            simp
        have hesurj : ∀ q ∈ M, ∃ s : Fin t, e s = q := by
          intro q hq
          rw [← himageM, Finset.mem_image] at hq
          obtain ⟨s, _, hs⟩ := hq
          exact ⟨s, hs⟩
        set ca : Fin t → ZMod m := fun s => Pπ.start (f (e s)) with hca_def
        set la : Fin t → ℕ := fun s => Pπ.len (f (e s)) with hla_def
        have hca_la : ∀ s, arcSet (ca s) (la s) = Pπ.arcOf (f (e s)) := fun s => rfl
        have hla1 : ∀ s, 1 ≤ la s := fun s => Pπ.len_pos _
        have hlam : ∀ s, la s ≤ m := fun s => Pπ.len_le hk _
        have hdij : ∀ s₁ s₂ : Fin t, s₁ ≠ s₂ →
            Disjoint (arcSet (ca s₁) (la s₁)) (arcSet (ca s₂) (la s₂)) := by
          intro s₁ s₂ h
          rw [hca_la, hca_la]
          apply Pπ.arcOf_disjoint hk
          intro hff
          apply h
          apply e.injective
          apply finj _ (heM s₁) _ (heM s₂) hff
        set D := Finset.univ.biUnion (fun s : Fin t => arcSet (ca s) (la s)) with hD_def
        have hD : D ≠ Finset.univ := by
          intro huniv
          have hNT : (Finset.univ \ T).Nonempty := by
            apply Finset.nonempty_iff_ne_empty.mpr
            intro hempty
            rw [Finset.sdiff_eq_empty_iff_subset] at hempty
            have h2 : T.card = N := by
              rw [le_antisymm (Finset.subset_univ T) hempty, Finset.card_univ, Fintype.card_fin]
            omega
          obtain ⟨j, hj⟩ := hNT
          simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hj
          obtain ⟨x, hx⟩ : (Pπ.arcOf j).Nonempty := by
            refine ⟨Pπ.start j, ?_⟩
            rw [arcOf, mem_arcSet]
            exact ⟨0, Pπ.len_pos j, by simp⟩
          have hxD : x ∈ D := by rw [huniv]; exact Finset.mem_univ x
          rw [hD_def, Finset.mem_biUnion] at hxD
          obtain ⟨s, _, hsx⟩ := hxD
          rw [hca_la] at hsx
          have hjeq : j = f (e s) := by
            by_contra hne
            exact (Finset.disjoint_left.mp (Pπ.arcOf_disjoint hk hne) hx hsx).elim
          have hsT : f (e s) ∈ T := (fprop _ (heM s)).1
          rw [← hjeq] at hsT
          exact hj hsT
        obtain ⟨m', hm', φ, hφ, hm'eq⟩ := surgeryMany ca la hla1 hlam hdij hD
        have hm'ge : B.card ≤ m' := by
          have hsum1 : ∑ s : Fin t, la s = ∑ q ∈ M, Pπ.len (f q) := by
            rw [← himageM, Finset.sum_image (fun a _ b _ h => e.injective h)]
          have hsum2 : ∑ q ∈ M, Pπ.len (f q) = ∑ q ∈ T, Pπ.len q := by
            rw [← hMT, Finset.sum_image (fun a ha b hb h => finj a ha b hb h)]
          have htotal : ∑ q ∈ T, Pπ.len q + ∑ q ∈ Finset.univ \ T, Pπ.len q = m := by
            have hdis : Disjoint T (Finset.univ \ T) := by
              rw [Finset.disjoint_left]
              intro x hx hx2
              rw [Finset.mem_sdiff] at hx2
              exact hx2.2 hx
            rw [← Finset.sum_union hdis, Finset.union_sdiff_of_subset (Finset.subset_univ T),
              Pπ.len_sum]
          have hNT_card : (Finset.univ \ T).card = N - t := by
            rw [Finset.card_sdiff, Finset.card_univ, Fintype.card_fin, Finset.inter_univ,
              cardMT]
          have hge2 : N - t ≤ ∑ q ∈ Finset.univ \ T, Pπ.len q := by
            rw [← hNT_card]
            have h1 : ∑ q ∈ Finset.univ \ T, 1 ≤ ∑ q ∈ Finset.univ \ T, Pπ.len q := by
              apply Finset.sum_le_sum
              intro q _
              exact Pπ.len_pos q
            rw [Finset.sum_const, nsmul_eq_mul, mul_one] at h1
            exact h1
          rw [hm'eq, hBcard, hsum1, hsum2]
          omega
        set g := B.orderEmbOfFin rfl with hg_def
        have hgM : ∀ p : Fin B.card, g p ∈ B := fun p => B.orderEmbOfFin_mem rfl p
        have hgMin : ∀ p : Fin B.card, g p ∉ M := by
          intro p
          have h1 := hgM p
          have h2 : g p ∈ Finset.univ \ M := hB_def ▸ h1
          rw [Finset.mem_sdiff] at h2
          exact h2.2
        have hgimage : Finset.univ.image g = B := by
          apply Finset.eq_of_subset_of_card_le
          · intro y hy
            rw [Finset.mem_image] at hy
            obtain ⟨s, _, rfl⟩ := hy
            exact hgM s
          · rw [Finset.card_image_of_injective _ g.injective]
            simp
        have gsurj : ∀ q ∈ B, ∃ p : Fin B.card, g p = q := by
          intro q hq
          rw [← hgimage, Finset.mem_image] at hq
          obtain ⟨p, _, hp⟩ := hq
          exact ⟨p, hp⟩
        have hpart' : ∀ p : Fin B.card, ∃ P' : CirclePartition m' B.card,
            ∀ i, 1 ≤ ∑ x ∈ P'.arcOf i, like (g p) (φ x) := by
          intro p
          obtain ⟨Qp, hQp⟩ := hpart (g p)
          have harcval' : ∀ s : Fin t, ∑ x ∈ arcSet (ca s) (la s), like (g p) x < 1 := by
            intro s
            rw [hca_la]
            have h1 : f (e s) ∈ T := (fprop _ (heM s)).1
            have h2 := hate (g p) (hgMin p) (f (e s)) h1
            rw [not_le] at h2
            exact h2
          obtain ⟨Pp, hPp⟩ := mergeValues Qp hk ca la (like (g p)) (fun x => hnn _ x) hQp
            hla1 hlam hdij harcval' htN φ hφ
          have hcast : N - t = B.card := hBcard.symm
          exact ⟨CirclePartition.cast hcast Pp, fun i => by
            rw [circlePartition_cast_arcOf hcast Pp i]
            exact hPp (Fin.cast hcast.symm i)⟩
        have hBcard0 : 0 < B.card := by omega
        obtain ⟨a', ha'⟩ := ih B.card (by omega) hBcard0 m' hm'ge
          (fun p y => like (g p) (φ y)) (fun p y => hnn _ _) hpart'
        -- the final assignment
        have hDM : ∀ x ∈ D, ∃ q ∈ M, x ∈ Pπ.arcOf (f q) := by
          intro x hx
          rw [hD_def, Finset.mem_biUnion] at hx
          obtain ⟨s, _, hsx⟩ := hx
          rw [hca_la] at hsx
          exact ⟨e s, heM s, hsx⟩
        refine ⟨fun x => if hx : x ∈ D then Classical.choose (hDM x hx)
          else g (a' (Classical.choose (hφ.cover x hx))), fun q => ?_⟩
        by_cases hqM : q ∈ M
        · have hqset : (Finset.univ.filter (fun x =>
              (if hx : x ∈ D then Classical.choose (hDM x hx)
                else g (a' (Classical.choose (hφ.cover x hx)))) = q))
              = Pπ.arcOf (f q) := by
            ext x
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            constructor
            · intro hxq
              by_cases hx : x ∈ D
              · rw [dif_pos hx] at hxq
                rw [← hxq]
                exact (Classical.choose_spec (hDM x hx)).2
              · rw [dif_neg hx] at hxq
                exfalso
                have h2 : g (a' (Classical.choose (hφ.cover x hx))) ∈ B := hgM _
                have h3 : g (a' (Classical.choose (hφ.cover x hx))) ∈ Finset.univ \ M :=
                  hB_def ▸ h2
                rw [Finset.mem_sdiff] at h3
                exact h3.2 (hxq ▸ hqM)
            · intro hx
              by_cases hxD : x ∈ D
              · rw [dif_pos hxD]
                have h1 := (Classical.choose_spec (hDM x hxD)).2
                by_cases hff : f (Classical.choose (hDM x hxD)) = f q
                · exact finj _ (Classical.choose_spec (hDM x hxD)).1 _ hqM hff
                · exact absurd (Finset.disjoint_left.mp (Pπ.arcOf_disjoint hk hff) h1 hx)
                    (by simp)
              · exfalso
                have h1 : x ∈ D := by
                  obtain ⟨s, hs⟩ := hesurj q hqM
                  rw [hD_def, Finset.mem_biUnion]
                  refine ⟨s, Finset.mem_univ _, ?_⟩
                  rw [hca_la, hs]
                  exact hx
                exact hxD h1
          rw [hqset]
          exact (fprop q hqM).2
        · have hqB : q ∈ B := by
            rw [hB_def, Finset.mem_sdiff]
            exact ⟨Finset.mem_univ q, hqM⟩
          obtain ⟨p, hp⟩ := gsurj q hqB
          have hqset : (Finset.univ.filter (fun x =>
              (if hx : x ∈ D then Classical.choose (hDM x hx)
                else g (a' (Classical.choose (hφ.cover x hx)))) = q))
              = (Finset.univ.filter (a' · = p)).image φ := by
            ext x
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
            constructor
            · intro hxq
              by_cases hx : x ∈ D
              · rw [dif_pos hx] at hxq
                exfalso
                have h1 := (Classical.choose_spec (hDM x hx)).1
                have h2 : q ∈ Finset.univ \ M := hB_def ▸ hqB
                rw [Finset.mem_sdiff] at h2
                exact h2.2 (hxq ▸ h1)
              · rw [dif_neg hx] at hxq
                refine ⟨Classical.choose (hφ.cover x hx), ?_, ?_⟩
                · apply g.injective
                  rw [hxq, hp]
                · exact Classical.choose_spec (hφ.cover x hx)
            · rintro ⟨y, hy, rfl⟩
              have hynot : φ y ∉ D := hφ.notMem y
              rw [dif_neg hynot]
              have hy2 : Classical.choose (hφ.cover (φ y) hynot) = y := by
                have h1 := Classical.choose_spec (hφ.cover (φ y) hynot)
                exact hφ.inj h1
              rw [hy2, hy, hp]
          rw [hqset, Finset.sum_image (fun a _ b _ h => hφ.inj h), ← hp]
          exact ha' p


end CirclePartition

snip end

/-- The USAMO 2025 Problem 6: distributing cupcakes to people so that everybody
gets total score at least one in their own ranking. -/
problem usa2025_p6 {m n : ℕ} [NeZero m] (_hm : 0 < m) (hn : 0 < n) (hmn : n ≤ m)
    (like : Fin n → ZMod m → ℝ) (hnn : ∀ p c, 0 ≤ like p c)
    (hpart : ∀ p, ∃ P : CirclePartition m n, ∀ i, 1 ≤ ∑ x ∈ P.arcOf i, like p x) :
    ∃ a : ZMod m → Fin n, ∀ p, 1 ≤ ∑ c ∈ Finset.univ.filter (a · = p), like p c := by
  exact CirclePartition.usa2025_p6_main n hn m hmn like hnn hpart

end Usa2025P6
