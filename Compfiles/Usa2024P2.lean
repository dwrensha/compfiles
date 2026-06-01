/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Mathlib.Data.Set.Card
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.Ring.RingNF

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# USA Mathematical Olympiad 2024, Problem 2

Let S₁, S₂, ..., S₁₀₀ be finite sets of integers whose intersection
is not empty. For each non-empty T ⊆ {S₁, S₂, ..., S₁₀₀}, the size of
the intersection of the sets in T is a multiple of the number of
sets in T. What is the least possible number of elements that are in
at least 50 sets?
-/

namespace Usa2024P2

determine solution : ℕ := 50 * Nat.choose 100 50

structure Good (S : Fin 100 → Set ℤ) : Prop where
  finite : ∀ i, (S i).Finite
  nonempty_inter : ⋂ i, S i ≠ ∅
  card : ∀ T : Finset (Fin 100), T.Nonempty →
                 ∃ k : ℕ, (⋂ i ∈ T, S i).ncard = k * T.card

-- z is in at least k of the sets S.
abbrev InAtLeastKSubsets (S : Fin 100 → Set ℤ) (k : ℕ) (z : ℤ) : Prop :=
  k ≤ {i : Fin 100 | z ∈ S i }.ncard

snip begin

abbrev Signature := Finset (Fin 100)

def topSignature : Signature := Finset.univ

/-- The membership signature of an integer with respect to the family `S`. -/
noncomputable def signatureOf (S : Fin 100 → Set ℤ) (z : ℤ) : Signature := by
  classical
  exact Finset.univ.filter (fun i ↦ z ∈ S i)

lemma ncard_preimage_eq_sum_fibers
    {α β : Type} [Fintype β]
    (g : α → β) (p : β → Prop) [DecidablePred p]
    (hfin : {a : α | p (g a)}.Finite) :
    {a : α | p (g a)}.ncard =
      ∑ b : β, if p b then {a : α | g a = b}.ncard else 0 := by
  classical
  let e : ↑({a : α | p (g a)}) ≃
      Sigma (fun b : ↑({b : β | p b}) => ↑({a : α | g a = b.1})) :=
    { toFun := fun a => ⟨⟨g a.1, a.2⟩, ⟨a.1, rfl⟩⟩
      invFun := fun x => ⟨x.2.1, by
        change p (g x.2.1)
        rw [x.2.2]
        exact x.1.2⟩
      left_inv := by
        intro a
        ext
        rfl
      right_inv := by
        intro x
        cases x with
        | mk b a =>
          ext
          · exact a.2
          · rfl }
  have hfiber_fin : ∀ b : ↑({b : β | p b}), ({a : α | g a = b.1}).Finite := by
    intro b
    exact hfin.subset (by
      intro a ha
      change p (g a)
      rw [ha]
      exact b.2)
  letI := hfin.fintype
  letI : Fintype ↑({b : β | p b}) := inferInstance
  letI (b : ↑({b : β | p b})) : Fintype ↑({a : α | g a = b.1}) :=
    (hfiber_fin b).fintype
  letI : Fintype
      (Sigma (fun b : ↑({b : β | p b}) => ↑({a : α | g a = b.1}))) :=
    inferInstance
  have hAcard :
      {a : α | p (g a)}.ncard = Fintype.card ↑({a : α | p (g a)}) := by
    rw [Set.ncard_eq_toFinset_card ({a : α | p (g a)}) hfin]
    exact hfin.card_toFinset
  have hsigma :
      Fintype.card
        (Sigma (fun b : ↑({b : β | p b}) => ↑({a : α | g a = b.1})))
        = ∑ b : ↑({b : β | p b}), ({a : α | g a = b.1}).ncard := by
    calc
      Fintype.card
          (Sigma (fun b : ↑({b : β | p b}) => ↑({a : α | g a = b.1})))
          = ∑ b : ↑({b : β | p b}), Fintype.card ↑({a : α | g a = b.1}) := by
            exact Fintype.card_sigma
      _ = ∑ b : ↑({b : β | p b}), ({a : α | g a = b.1}).ncard := by
        refine Finset.sum_congr rfl ?_
        intro b _
        exact Set.fintypeCard_eq_ncard {a | g a = ↑b}
  calc
    {a : α | p (g a)}.ncard = Fintype.card ↑({a : α | p (g a)}) := hAcard
    _ =
        Fintype.card
          (Sigma (fun b : ↑({b : β | p b}) => ↑({a : α | g a = b.1}))) := by
          exact Fintype.card_congr e
    _ = ∑ b : ↑({b : β | p b}), ({a : α | g a = b.1}).ncard := hsigma
    _ = ∑ b : β, if p b then {a : α | g a = b}.ncard else 0 := by
      rw [← Finset.sum_filter]
      rw [Finset.sum_subtype ((Finset.univ : Finset β).filter p) ?_
        (fun b => ({a : α | g a = b}).ncard)]
      intro b
      simp

/-- Counts elements whose signature contains `u`. -/
noncomputable def SignatureIntersectionCount (f : Signature → ℕ) (u : Signature) : ℕ :=
  ∑ v : Signature, if u ⊆ v then f v else 0

/-- Divisibility condition in signature-count form. -/
def SignatureCountCondition (f : Signature → ℕ) : Prop :=
  ∀ u : Signature, u.Nonempty → u.card ∣ SignatureIntersectionCount f u

/-- Number of realized points lying in at least `50` sets. -/
noncomputable def SignatureObjective (f : Signature → ℕ) : ℕ :=
  ∑ v : Signature, if 50 ≤ v.card then f v else 0

/-- Canonical high-rank counts used by the construction. -/
def canonicalHighCount (v : Signature) : ℕ :=
  if 50 ≤ v.card then 2 * v.card - 100 else 0

/-- Count supersignatures of `u` with exactly `j` new indices. -/
lemma superset_layer_card (u : Signature) (j : ℕ) :
    ((Finset.univ : Finset Signature).filter
        (fun v : Signature => u ⊆ v ∧ v.card = u.card + j)).card =
      (100 - u.card).choose j := by
  classical
  have hsubset_top : u ⊆ topSignature := by
    intro a _
    simp [topSignature]
  have hfilter :
      ((Finset.univ : Finset Signature).filter
          (fun v : Signature => u ⊆ v ∧ v.card = u.card + j)) =
        (topSignature.powersetCard (u.card + j)).filter (fun v : Signature => u ⊆ v) := by
    ext v
    constructor
    · intro hv
      rw [Finset.mem_filter] at hv ⊢
      exact ⟨Finset.mem_powersetCard.mpr ⟨by intro a _; simp [topSignature], hv.2.2⟩,
        hv.2.1⟩
    · intro hv
      rw [Finset.mem_filter] at hv ⊢
      exact ⟨Finset.mem_univ v, hv.2, (Finset.mem_powersetCard.mp hv.1).2⟩
  rw [hfilter]
  rw [Finset.card_filter_powersetCard_subset u topSignature (u.card + j) hsubset_top (by omega)]
  have hcard_top : topSignature.card = 100 := by
    simp [topSignature]
  rw [hcard_top]
  congr 1
  omega

def supersetLayer (u : Signature) (j : ℕ) : Finset Signature :=
  (Finset.univ : Finset Signature).filter
    (fun v : Signature => u ⊆ v ∧ v.card = u.card + j)

lemma mem_supersetLayer {u v : Signature} {j : ℕ} :
    v ∈ supersetLayer u j ↔ u ⊆ v ∧ v.card = u.card + j := by
  simp [supersetLayer]

lemma supersetLayer_card (u : Signature) (j : ℕ) :
    (supersetLayer u j).card = (100 - u.card).choose j := by
  simpa [supersetLayer] using superset_layer_card u j

lemma canonicalHighCount_of_superset_high
    {u v : Signature} (hu : 50 ≤ u.card) (huv : u ⊆ v) :
    canonicalHighCount v = 2 * v.card - 100 := by
  have huv_card : u.card ≤ v.card := Finset.card_le_card huv
  simp [canonicalHighCount, le_trans hu huv_card]

lemma canonicalHighCount_grouped_summand
    {a m j : ℕ} (ham : a + m = 100) (_ha : 50 ≤ a) (_hj : j ≤ m) :
    2 * (a + j) - 100 = (a - m) + 2 * j := by
  omega

lemma sum_supersets_by_rank
    (u : Signature) (F : ℕ → ℕ) :
    (∑ v : Signature, if u ⊆ v then F v.card else 0) =
      ∑ j ∈ Finset.range (100 - u.card + 1),
        F (u.card + j) * (100 - u.card).choose j := by
  classical
  calc
    (∑ v : Signature, if u ⊆ v then F v.card else 0)
        = ∑ v ∈ (Finset.univ : Finset Signature).filter (fun v : Signature => u ⊆ v),
            F v.card := by
          rw [← Finset.sum_filter]
    _ = ∑ v ∈ (Finset.univ : Finset Signature).filter (fun v : Signature => u ⊆ v),
          ∑ j ∈ Finset.range (100 - u.card + 1),
            if v.card = u.card + j then F v.card else 0 := by
          refine Finset.sum_congr rfl ?_
          intro v hv
          rw [Finset.mem_filter] at hv
          have huv : u ⊆ v := hv.2
          have hcard_le : u.card ≤ v.card := Finset.card_le_card huv
          have hv_le_100 : v.card ≤ 100 := by
            have h := Finset.card_le_univ v
            simpa using h
          have hjmem : v.card - u.card ∈ Finset.range (100 - u.card + 1) := by
            simp
            omega
          calc
            F v.card =
                (if v.card = u.card + (v.card - u.card) then F v.card else 0) := by
                  rw [Nat.add_sub_of_le hcard_le]
                  simp
            _ = ∑ j ∈ Finset.range (100 - u.card + 1),
                  if v.card = u.card + j then F v.card else 0 := by
                  symm
                  refine Finset.sum_eq_single (v.card - u.card) ?_ ?_
                  · intro j hj hjne
                    have hneq : v.card ≠ u.card + j := by
                      intro h
                      have : j = v.card - u.card := by omega
                      exact hjne this
                    simp [hneq]
                  · intro hnot
                    exact (hnot hjmem).elim
    _ = ∑ j ∈ Finset.range (100 - u.card + 1),
          ∑ v ∈ (Finset.univ : Finset Signature).filter (fun v : Signature => u ⊆ v),
            if v.card = u.card + j then F v.card else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ j ∈ Finset.range (100 - u.card + 1),
          F (u.card + j) * (100 - u.card).choose j := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          calc
            (∑ v ∈ (Finset.univ : Finset Signature).filter (fun v : Signature => u ⊆ v),
                if v.card = u.card + j then F v.card else 0)
                =
              ∑ v ∈ ((Finset.univ : Finset Signature).filter
                  (fun v : Signature => u ⊆ v)).filter
                  (fun v : Signature => v.card = u.card + j),
                F v.card := by
                rw [← Finset.sum_filter]
            _ = ∑ v ∈ supersetLayer u j, F v.card := by
                have hfilter :
                    ((Finset.univ : Finset Signature).filter
                      (fun v : Signature => u ⊆ v)).filter
                      (fun v : Signature => v.card = u.card + j) =
                    supersetLayer u j := by
                  ext v
                  simp [supersetLayer]
                rw [hfilter]
            _ = ∑ v ∈ supersetLayer u j, F (u.card + j) := by
                refine Finset.sum_congr rfl ?_
                intro v hv
                rw [(mem_supersetLayer.mp hv).2]
            _ = F (u.card + j) * (100 - u.card).choose j := by
                simp [Finset.sum_const, supersetLayer_card, Nat.mul_comm]

/-- Group the high-count intersection sum by rank difference. -/
lemma SignatureIntersectionCount_canonicalHighCount_grouped
    (u : Signature) (hu : 50 ≤ u.card) :
    SignatureIntersectionCount canonicalHighCount u =
      ∑ j ∈ Finset.range (100 - u.card + 1),
        (2 * (u.card + j) - 100) * (100 - u.card).choose j := by
  rw [SignatureIntersectionCount]
  calc
    (∑ v : Signature, if u ⊆ v then canonicalHighCount v else 0)
        = ∑ v : Signature, if u ⊆ v then 2 * v.card - 100 else 0 := by
          refine Finset.sum_congr rfl ?_
          intro v _
          by_cases huv : u ⊆ v
          · rw [if_pos huv, if_pos huv, canonicalHighCount_of_superset_high hu huv]
          · simp [huv]
    _ = ∑ j ∈ Finset.range (100 - u.card + 1),
          (2 * (u.card + j) - 100) * (100 - u.card).choose j := by
          exact sum_supersets_by_rank u (fun r => 2 * r - 100)

/-- The binomial identity after grouping by rank. -/
lemma canonicalHighCount_grouped_sum_eq {a m : ℕ}
    (ham : a + m = 100) (ha : 50 ≤ a) :
    (∑ j ∈ Finset.range (m + 1),
        (2 * (a + j) - 100) * m.choose j) =
      a * 2 ^ m := by
  have hm_le_a : m ≤ a := by omega
  have hchoose := Nat.sum_range_choose m
  have hmulchoose := Nat.sum_range_mul_choose m
  calc
    (∑ j ∈ Finset.range (m + 1), (2 * (a + j) - 100) * m.choose j)
        = ∑ j ∈ Finset.range (m + 1), ((a - m) + 2 * j) * m.choose j := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          have hjle : j ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
          rw [canonicalHighCount_grouped_summand ham ha hjle]
    _ = (∑ j ∈ Finset.range (m + 1),
          ((a - m) * m.choose j + (2 * j) * m.choose j)) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          ring
    _ = (a - m) * (∑ j ∈ Finset.range (m + 1), m.choose j) +
          ∑ j ∈ Finset.range (m + 1), (2 * j) * m.choose j := by
          rw [Finset.sum_add_distrib]
          congr 1
          rw [Finset.mul_sum]
    _ = (a - m) * (∑ j ∈ Finset.range (m + 1), m.choose j) +
          2 * (∑ j ∈ Finset.range (m + 1), j * m.choose j) := by
          congr 1
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro j hj
          ring
    _ = (a - m) * 2 ^ m + 2 * (m * 2 ^ (m - 1)) := by
          rw [hchoose, hmulchoose]
    _ = a * 2 ^ m := by
          by_cases hm : m = 0
          · subst hm
            simp
          · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
            rw [← mul_pow_sub_one hm 2]
            have hsubadd : a - m + m = a := Nat.sub_add_cancel hm_le_a
            calc
              (a - m) * (2 * 2 ^ (m - 1)) + 2 * (m * 2 ^ (m - 1))
                  = ((a - m) + m) * (2 * 2 ^ (m - 1)) := by ring
              _ = a * (2 * 2 ^ (m - 1)) := by rw [hsubadd]

/-- Closed form for canonical high-rank intersections. -/
lemma SignatureIntersectionCount_canonicalHighCount_closed_form
    (u : Signature) (hu : 50 ≤ u.card) :
    SignatureIntersectionCount canonicalHighCount u =
      u.card * 2 ^ (100 - u.card) := by
  rw [SignatureIntersectionCount_canonicalHighCount_grouped u hu]
  have hcard_le : u.card ≤ 100 := by
    have h := Finset.card_le_univ u
    simpa using h
  exact canonicalHighCount_grouped_sum_eq (by omega) hu

/-- Move one full block from `v` to its immediate sub-signatures. -/
def pushDown (f : Signature → ℕ) (v : Signature) : Signature → ℕ :=
  fun w ↦
    if w = v then f w - v.card
    else if w ⊆ v ∧ w.card + 1 = v.card then f w + 1
    else f w

lemma immediate_supersets_count {u v : Signature} (huv : u ⊆ v) :
    (∑ w ∈ (Finset.univ : Finset Signature).erase v,
        if u ⊆ w ∧ w ⊆ v ∧ w.card + 1 = v.card then 1 else 0) =
      v.card - u.card := by
  classical
  rw [← Finset.card_filter
    (fun w : Signature => u ⊆ w ∧ w ⊆ v ∧ w.card + 1 = v.card)
    ((Finset.univ : Finset Signature).erase v)]
  by_cases huv_eq : u = v
  · subst huv_eq
    rw [tsub_self]
    have hfilter :
        ((Finset.univ : Finset Signature).erase u).filter
            (fun w : Signature => u ⊆ w ∧ w ⊆ u ∧ w.card + 1 = u.card) = ∅ := by
      ext w
      constructor
      · intro hw
        exfalso
        rw [Finset.mem_filter] at hw
        have hwu : w = u := Finset.Subset.antisymm hw.2.2.1 hw.2.1
        exact (Finset.mem_erase.mp hw.1).1 hwu
      · intro hw
        simp at hw
    rw [hfilter, Finset.card_empty]
  · have hcard_lt : u.card < v.card :=
      Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨huv, huv_eq⟩)
    have hfilter :
        ((Finset.univ : Finset Signature).erase v).filter
            (fun w : Signature => u ⊆ w ∧ w ⊆ v ∧ w.card + 1 = v.card) =
          (v.powersetCard (v.card - 1)).filter (fun w : Signature => u ⊆ w) := by
      ext w
      constructor
      · intro hw
        rw [Finset.mem_filter] at hw ⊢
        exact ⟨Finset.mem_powersetCard.mpr ⟨hw.2.2.1, by omega⟩, hw.2.1⟩
      · intro hw
        rw [Finset.mem_filter] at hw ⊢
        have hw' := Finset.mem_powersetCard.mp hw.1
        refine ⟨?_, hw.2, hw'.1, by omega⟩
        refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ w⟩
        intro hwv
        have : w.card = v.card := by rw [hwv]
        omega
    rw [hfilter]
    rw [Finset.card_filter_powersetCard_subset u v (v.card - 1) huv (by omega)]
    have hidx : v.card - 1 - u.card = v.card - u.card - 1 := by omega
    rw [hidx]
    cases hdiff : v.card - u.card with
    | zero => omega
    | succ n => simp [Nat.choose_succ_self_right]

lemma canonicalHighCount_valid_on_high :
    ∀ u : Signature, 50 ≤ u.card →
      u.card ∣ SignatureIntersectionCount canonicalHighCount u := by
  intro u hu
  rw [SignatureIntersectionCount_canonicalHighCount_closed_form u hu]
  exact dvd_mul_right u.card (2 ^ (100 - u.card))

lemma sum_signatures_by_card (F : ℕ → ℕ) :
    (∑ v : Signature, F v.card) =
      ∑ r ∈ Finset.range 101, F r * Nat.choose 100 r := by
  simpa using (sum_supersets_by_rank (∅ : Signature) F)

lemma high_rank_objective_sum_eq_tail :
    (∑ r ∈ Finset.range 101,
        (if 50 ≤ r then 2 * r - 100 else 0) * Nat.choose 100 r) =
      ∑ j ∈ Finset.range 51,
        (2 * (50 + j) - 100) * Nat.choose 100 (50 + j) := by
  let F : ℕ → ℕ := fun r =>
    (if 50 ≤ r then 2 * r - 100 else 0) * Nat.choose 100 r
  have hsplit := Finset.sum_range_add F 50 51
  norm_num at hsplit
  rw [hsplit]
  have hzero : (∑ x ∈ Finset.range 50, F x) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    have hxlt : x < 50 := Finset.mem_range.mp hx
    simp [F, not_le_of_gt hxlt]
  rw [hzero, zero_add]
  refine Finset.sum_congr rfl ?_
  intro j _hj
  simp [F]

lemma high_rank_objective_summand_int {r : ℕ}
    (hr50 : 50 ≤ r) (hr100 : r ≤ 100) :
    (((2 * r - 100) * Nat.choose 100 r : ℕ) : ℤ) =
      100 * ((Nat.choose 99 (r - 1) : ℤ) - Nat.choose 99 r) := by
  have hrpos : 0 < r := by omega
  have hmul_left_nat : 100 * Nat.choose 99 (r - 1) = r * Nat.choose 100 r := by
    have h := Nat.add_one_mul_choose_eq 99 (r - 1)
    have hr : r - 1 + 1 = r := Nat.sub_add_cancel hrpos
    simpa [hr, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h
  have hmul_right_nat : 100 * Nat.choose 99 r = (100 - r) * Nat.choose 100 r := by
    have h := Nat.choose_mul_succ_eq 99 r
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h
  have hmul_left : (100 : ℤ) * Nat.choose 99 (r - 1) = r * Nat.choose 100 r := by
    exact_mod_cast hmul_left_nat
  have hmul_right :
      (100 : ℤ) * Nat.choose 99 r = (100 - r : ℕ) * Nat.choose 100 r := by
    exact_mod_cast hmul_right_nat
  calc
    (((2 * r - 100) * Nat.choose 100 r : ℕ) : ℤ)
        = ((2 * r - 100 : ℕ) : ℤ) * Nat.choose 100 r := by simp
    _ = (((r : ℤ) - (100 - r : ℕ)) * Nat.choose 100 r) := by
          have hcoef : ((2 * r - 100 : ℕ) : ℤ) = (r : ℤ) - (100 - r : ℕ) := by
            omega
          rw [hcoef]
    _ = (r * Nat.choose 100 r : ℤ) - ((100 - r : ℕ) * Nat.choose 100 r : ℤ) := by
          ring
    _ = 100 * ((Nat.choose 99 (r - 1) : ℤ) - Nat.choose 99 r) := by
          rw [← hmul_left, ← hmul_right]
          ring

lemma high_rank_choose_telescope_int (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1),
        (100 : ℤ) * ((Nat.choose 99 (49 + j) : ℤ) - Nat.choose 99 (50 + j))) =
      100 * ((Nat.choose 99 49 : ℤ) - Nat.choose 99 (50 + n)) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      rw [ih]
      ring_nf

lemma high_rank_weighted_choose_sum :
    (∑ j ∈ Finset.range 51,
        (2 * (50 + j) - 100) * Nat.choose 100 (50 + j)) =
      50 * Nat.choose 100 50 := by
  have hcast :
      ((∑ j ∈ Finset.range 51,
          (2 * (50 + j) - 100) * Nat.choose 100 (50 + j) : ℕ) : ℤ) =
        ((50 * Nat.choose 100 50 : ℕ) : ℤ) := by
    calc
      ((∑ j ∈ Finset.range 51,
          (2 * (50 + j) - 100) * Nat.choose 100 (50 + j) : ℕ) : ℤ)
          = ∑ j ∈ Finset.range 51,
              (((2 * (50 + j) - 100) * Nat.choose 100 (50 + j) : ℕ) : ℤ) := by
              rw [Nat.cast_sum]
      _ = ∑ j ∈ Finset.range 51,
              (100 : ℤ) * ((Nat.choose 99 (49 + j) : ℤ) - Nat.choose 99 (50 + j)) := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              have hjlt : j < 51 := Finset.mem_range.mp hj
              have h49 : 50 + j - 1 = 49 + j := by omega
              rw [high_rank_objective_summand_int
                (by omega : 50 ≤ 50 + j) (by omega : 50 + j ≤ 100), h49]
      _ = 100 * ((Nat.choose 99 49 : ℤ) - Nat.choose 99 (50 + 50)) := by
              simpa using high_rank_choose_telescope_int 50
      _ = ((50 * Nat.choose 100 50 : ℕ) : ℤ) := by
              have hboundary : 100 * Nat.choose 99 49 = Nat.choose 100 50 * 50 :=
                Nat.add_one_mul_choose_eq 99 49
              have hzero : Nat.choose 99 (50 + 50) = 0 := by
                exact Nat.choose_eq_zero_of_lt (by norm_num)
              rw [hzero]
              norm_num
              exact_mod_cast hboundary.trans (Nat.mul_comm (Nat.choose 100 50) 50)
  exact Nat.cast_inj.mp hcast

lemma canonicalHighCount_objective_rank_sum :
    (∑ r ∈ Finset.range 101,
        (if 50 ≤ r then 2 * r - 100 else 0) * Nat.choose 100 r) =
      solution := by
  rw [high_rank_objective_sum_eq_tail, solution]
  exact high_rank_weighted_choose_sum

lemma canonicalHighCount_objective :
    SignatureObjective canonicalHighCount = solution := by
  rw [SignatureObjective]
  calc
    (∑ v : Signature, if 50 ≤ v.card then canonicalHighCount v else 0)
        = ∑ v : Signature, if 50 ≤ v.card then 2 * v.card - 100 else 0 := by
          refine Finset.sum_congr rfl ?_
          intro v _
          by_cases hv : 50 ≤ v.card
          · simp [canonicalHighCount, hv]
          · simp [hv]
    _ = ∑ r ∈ Finset.range 101,
          (if 50 ≤ r then 2 * r - 100 else 0) * Nat.choose 100 r := by
          exact sum_signatures_by_card (fun r => if 50 ≤ r then 2 * r - 100 else 0)
    _ = solution := canonicalHighCount_objective_rank_sum

lemma pushDown_preserves_condition {f : Signature → ℕ} {v : Signature}
    (hfv : v.card ≤ f v) (hf : SignatureCountCondition f) :
    SignatureCountCondition (pushDown f v) := by
  -- Only intersections below `v` change.
  classical
  intro u hu
  by_cases huv : u ⊆ v
  · have hucard_le_vcard : u.card ≤ v.card := Finset.card_le_card huv
    have hchange :
        SignatureIntersectionCount (pushDown f v) u + u.card =
          SignatureIntersectionCount f u := by
      rw [SignatureIntersectionCount, SignatureIntersectionCount]
      rw [← Finset.sum_erase_add (Finset.univ : Finset Signature)
        (fun w => if u ⊆ w then pushDown f v w else 0) (Finset.mem_univ v)]
      rw [← Finset.sum_erase_add (Finset.univ : Finset Signature)
        (fun w => if u ⊆ w then f w else 0) (Finset.mem_univ v)]
      have herase :
          (∑ w ∈ (Finset.univ : Finset Signature).erase v,
              if u ⊆ w then pushDown f v w else 0)
            =
          (∑ w ∈ (Finset.univ : Finset Signature).erase v,
              if u ⊆ w then f w else 0) + (v.card - u.card) := by
        calc
          (∑ w ∈ (Finset.univ : Finset Signature).erase v,
              if u ⊆ w then pushDown f v w else 0)
              =
            (∑ w ∈ (Finset.univ : Finset Signature).erase v,
              ((if u ⊆ w then f w else 0)
                + (if u ⊆ w ∧ w ⊆ v ∧ w.card + 1 = v.card then 1 else 0))) := by
              refine Finset.sum_congr rfl ?_
              intro w hw
              have hwne : w ≠ v := (Finset.mem_erase.mp hw).1
              by_cases huw : u ⊆ w
              · by_cases himm : w ⊆ v ∧ w.card + 1 = v.card
                · simp [pushDown, hwne, huw, himm]
                · simp [pushDown, hwne, huw, himm]
              · have hnot : ¬(u ⊆ w ∧ w ⊆ v ∧ w.card + 1 = v.card) := by
                  exact fun h => huw h.1
                simp [huw]
          _ =
            (∑ w ∈ (Finset.univ : Finset Signature).erase v,
              if u ⊆ w then f w else 0) +
            (∑ w ∈ (Finset.univ : Finset Signature).erase v,
              if u ⊆ w ∧ w ⊆ v ∧ w.card + 1 = v.card then 1 else 0) := by
              rw [Finset.sum_add_distrib]
          _ =
            (∑ w ∈ (Finset.univ : Finset Signature).erase v,
              if u ⊆ w then f w else 0) + (v.card - u.card) := by
              rw [immediate_supersets_count huv]
      have hpush_v : pushDown f v v = f v - v.card := by simp [pushDown]
      rw [if_pos huv, if_pos huv, hpush_v]
      rw [herase]
      omega
    have hold : u.card ∣ SignatureIntersectionCount f u := hf u hu
    rw [← hchange] at hold
    exact (Nat.dvd_add_self_right).mp hold
  · have hchange :
        SignatureIntersectionCount (pushDown f v) u = SignatureIntersectionCount f u := by
      rw [SignatureIntersectionCount, SignatureIntersectionCount]
      refine Finset.sum_congr rfl ?_
      intro w _
      by_cases huw : u ⊆ w
      · have hwne : w ≠ v := by
          intro hwv
          exact huv (by simpa [hwv] using huw)
        have hnot : ¬(w ⊆ v ∧ w.card + 1 = v.card) := by
          intro h
          exact huv (fun i hi => h.1 (huw hi))
        simp [pushDown, huw, hwne, hnot]
      · simp [huw]
    rw [hchange]
    exact hf u hu

lemma pushDown_preserves_objective_of_large {f : Signature → ℕ} {v : Signature}
    (hv : 50 < v.card) (hfv : v.card ≤ f v) :
    SignatureObjective (pushDown f v) = SignatureObjective f := by
  -- Above rank `50`, push-down preserves the objective.
  classical
  have hv_le : 50 ≤ v.card := by omega
  have hpush_v : pushDown f v v = f v - v.card := by
    simp [pushDown]
  have hterm_v_new :
      (if 50 ≤ v.card then pushDown f v v else 0) = f v - v.card := by
    simp [hv_le, hpush_v]
  have hterm_v_old :
      (if 50 ≤ v.card then f v else 0) = f v := by
    simp [hv_le]
  have hchoose_pred : v.card.choose (v.card - 1) = v.card := by
    cases hcard : v.card with
    | zero => omega
    | succ n =>
        simp [Nat.choose_succ_self_right]
  have himmediate_sum :
      (∑ w ∈ (Finset.univ : Finset Signature).erase v,
          if w ⊆ v ∧ w.card + 1 = v.card then 1 else 0) = v.card := by
    rw [← Finset.card_filter
      (fun w : Signature ↦ w ⊆ v ∧ w.card + 1 = v.card)
      ((Finset.univ : Finset Signature).erase v)]
    have hfilter :
        ((Finset.univ : Finset Signature).erase v).filter
            (fun w : Signature ↦ w ⊆ v ∧ w.card + 1 = v.card)
          = Finset.powersetCard (v.card - 1) v := by
      ext w
      constructor
      · intro h
        have h' := Finset.mem_filter.mp h
        exact Finset.mem_powersetCard.mpr ⟨h'.2.1, by omega⟩
      · intro h
        have h' := Finset.mem_powersetCard.mp h
        refine Finset.mem_filter.mpr ⟨?_, h'.1, by omega⟩
        refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ w⟩
        intro hwv
        have hwcard : w.card = v.card := by rw [hwv]
        omega
    rw [hfilter, Finset.card_powersetCard, hchoose_pred]
  have hsum_erase :
      (∑ w ∈ (Finset.univ : Finset Signature).erase v,
          if 50 ≤ w.card then pushDown f v w else 0)
        =
      (∑ w ∈ (Finset.univ : Finset Signature).erase v,
          if 50 ≤ w.card then f w else 0) + v.card := by
    calc
      (∑ w ∈ (Finset.univ : Finset Signature).erase v,
          if 50 ≤ w.card then pushDown f v w else 0)
          =
        (∑ w ∈ (Finset.univ : Finset Signature).erase v,
          ((if 50 ≤ w.card then f w else 0)
            + (if w ⊆ v ∧ w.card + 1 = v.card then 1 else 0))) := by
            refine Finset.sum_congr rfl ?_
            intro w hw
            have hwne : w ≠ v := (Finset.mem_erase.mp hw).1
            by_cases himmediate : w ⊆ v ∧ w.card + 1 = v.card
            · have hwcard : 50 ≤ w.card := by omega
              simp [pushDown, hwne, himmediate, hwcard]
            · by_cases hwcard : 50 ≤ w.card
              · simp [pushDown, hwne, himmediate, hwcard]
              · simp [himmediate, hwcard]
      _ =
        (∑ w ∈ (Finset.univ : Finset Signature).erase v,
          if 50 ≤ w.card then f w else 0)
          +
        (∑ w ∈ (Finset.univ : Finset Signature).erase v,
          if w ⊆ v ∧ w.card + 1 = v.card then 1 else 0) := by
            rw [Finset.sum_add_distrib]
      _ =
        (∑ w ∈ (Finset.univ : Finset Signature).erase v,
          if 50 ≤ w.card then f w else 0) + v.card := by
            rw [himmediate_sum]
  calc
    SignatureObjective (pushDown f v)
        = (∑ w ∈ (Finset.univ : Finset Signature).erase v,
              if 50 ≤ w.card then pushDown f v w else 0)
            + (if 50 ≤ v.card then pushDown f v v else 0) := by
          rw [SignatureObjective]
          exact (Finset.sum_erase_add (Finset.univ : Finset Signature)
            (fun w ↦ if 50 ≤ w.card then pushDown f v w else 0)
            (Finset.mem_univ v)).symm
    _ = ((∑ w ∈ (Finset.univ : Finset Signature).erase v,
              if 50 ≤ w.card then f w else 0) + v.card) + (f v - v.card) := by
          rw [hsum_erase, hterm_v_new]
    _ = (∑ w ∈ (Finset.univ : Finset Signature).erase v,
              if 50 ≤ w.card then f w else 0) + f v := by
          omega
    _ = (∑ w ∈ (Finset.univ : Finset Signature).erase v,
              if 50 ≤ w.card then f w else 0)
          + (if 50 ≤ v.card then f v else 0) := by
          rw [hterm_v_old]
    _ = SignatureObjective f := by
          rw [SignatureObjective]
          exact Finset.sum_erase_add (Finset.univ : Finset Signature)
            (fun w ↦ if 50 ≤ w.card then f w else 0)
            (Finset.mem_univ v)

lemma pushDown_decreases_objective_at_middle {f : Signature → ℕ} {v : Signature}
    (hv : v.card = 50) (hfv : v.card ≤ f v) :
    SignatureObjective (pushDown f v) + 50 = SignatureObjective f := by
  classical
  have hv_le : 50 ≤ v.card := by omega
  have hfv50 : 50 ≤ f v := by omega
  have hpush_v : pushDown f v v = f v - 50 := by
    simp [pushDown, hv]
  have hterm_v_new :
      (if 50 ≤ v.card then pushDown f v v else 0) = f v - 50 := by
    simp [hv_le, hpush_v]
  have hterm_v_old :
      (if 50 ≤ v.card then f v else 0) = f v := by
    simp [hv_le]
  have hother :
      (∑ w ∈ (Finset.univ : Finset Signature).erase v,
          if 50 ≤ w.card then pushDown f v w else 0)
        =
      (∑ w ∈ (Finset.univ : Finset Signature).erase v,
          if 50 ≤ w.card then f w else 0) := by
    refine Finset.sum_congr rfl ?_
    intro w hw
    have hwne : w ≠ v := (Finset.mem_erase.mp hw).1
    by_cases hwcard : 50 ≤ w.card
    · have hnot_immediate : ¬(w ⊆ v ∧ w.card + 1 = v.card) := by
        intro h
        omega
      simp [hwcard, pushDown, hwne, hnot_immediate]
    · simp [hwcard]
  calc
    SignatureObjective (pushDown f v) + 50
        = ((∑ w ∈ (Finset.univ : Finset Signature).erase v,
              if 50 ≤ w.card then pushDown f v w else 0)
            + (if 50 ≤ v.card then pushDown f v v else 0)) + 50 := by
          rw [SignatureObjective]
          rw [← Finset.sum_erase_add (Finset.univ : Finset Signature)
            (fun w ↦ if 50 ≤ w.card then pushDown f v w else 0)
            (Finset.mem_univ v)]
    _ = ((∑ w ∈ (Finset.univ : Finset Signature).erase v,
              if 50 ≤ w.card then f w else 0) + (f v - 50)) + 50 := by
          rw [hother, hterm_v_new]
    _ = (∑ w ∈ (Finset.univ : Finset Signature).erase v,
              if 50 ≤ w.card then f w else 0) + f v := by
          omega
    _ = (∑ w ∈ (Finset.univ : Finset Signature).erase v,
              if 50 ≤ w.card then f w else 0)
          + (if 50 ≤ v.card then f v else 0) := by
          rw [hterm_v_old]
    _ = SignatureObjective f := by
          rw [SignatureObjective]
          exact Finset.sum_erase_add (Finset.univ : Finset Signature)
            (fun w ↦ if 50 ≤ w.card then f w else 0)
            (Finset.mem_univ v)

/-- Strict-superset part of an intersection count. -/
noncomputable def strictSupersetContribution (f : Signature → ℕ) (u : Signature) : ℕ :=
  ∑ w : Signature, if u ⊂ w then f w else 0

/-- Fill one rank with the least residue making divisibility hold. -/
noncomputable def fillRank (k : ℕ) (f : Signature → ℕ) : Signature → ℕ :=
  fun v ↦
    if v.card = k then
      let s := strictSupersetContribution f v
      (v.card - s % v.card) % v.card
    else f v

/-- The chosen residue makes `residue + s` divisible by `d`. -/
lemma dvd_complement_mod_add {d s : ℕ} (hd : 0 < d) :
    d ∣ ((d - s % d) % d) + s := by
  let r := s % d
  have hrlt : r < d := by simpa [r] using Nat.mod_lt s hd
  by_cases hr0 : r = 0
  · have hsmod : s % d = 0 := by simpa [r] using hr0
    rw [Nat.dvd_iff_mod_eq_zero]
    simp [hsmod]
  · have hres : (d - r) % d = d - r := Nat.mod_eq_of_lt (by omega)
    refine ⟨s / d + 1, ?_⟩
    calc
      ((d - s % d) % d) + s = (d - r) + s := by simp [r, hres]
      _ = (d - r) + (d * (s / d) + r) := by rw [Nat.div_add_mod s d]
      _ = d * (s / d + 1) := by
        rw [show (d - r) + (d * (s / d) + r) =
            ((d - r) + r) + d * (s / d) by omega]
        rw [Nat.sub_add_cancel (le_of_lt hrlt)]
        ring

lemma fillRank_eq_of_card {k : ℕ} {f : Signature → ℕ} {v : Signature}
    (hv : v.card = k) :
    fillRank k f v =
      let s := strictSupersetContribution f v
      (v.card - s % v.card) % v.card := by
  simp [fillRank, hv]

lemma fillRank_eq_self_of_card_ne {k : ℕ} {f : Signature → ℕ} {v : Signature}
    (hv : v.card ≠ k) : fillRank k f v = f v := by
  simp [fillRank, hv]

lemma fillRank_eq_self_of_card_gt {k : ℕ} {f : Signature → ℕ} {v : Signature}
    (hv : k < v.card) : fillRank k f v = f v := by
  exact fillRank_eq_self_of_card_ne (by omega)

lemma fillRank_eq_self_of_card_lt {k : ℕ} {f : Signature → ℕ} {v : Signature}
    (hv : v.card < k) : fillRank k f v = f v := by
  exact fillRank_eq_self_of_card_ne (by omega)

lemma fillRank_eq_self_of_high {k : ℕ} {f : Signature → ℕ} {v : Signature}
    (hk : k < 50) (hv : 50 ≤ v.card) : fillRank k f v = f v := by
  exact fillRank_eq_self_of_card_gt (by omega)

lemma fillRank_eq_self_on_supersets_of_card_lt {k : ℕ} {f : Signature → ℕ}
    {u w : Signature} (hu : k < u.card) (huw : u ⊆ w) :
    fillRank k f w = f w := by
  apply fillRank_eq_self_of_card_gt
  exact lt_of_lt_of_le hu (Finset.card_le_card huw)

lemma strictSupersetContribution_congr {f g : Signature → ℕ} {u : Signature}
    (h : ∀ w : Signature, u ⊂ w → f w = g w) :
    strictSupersetContribution f u = strictSupersetContribution g u := by
  unfold strictSupersetContribution
  refine Finset.sum_congr rfl ?_
  intro w _
  by_cases huw : u ⊂ w
  · simp [huw, h w huw]
  · simp [huw]

/-- Canonical strict supersets give the canonical strict contribution. -/
lemma strictSupersetContribution_eq_canonical_of_strict
    {f : Signature → ℕ} {u : Signature}
    (hstrict : ∀ w : Signature, u ⊂ w → f w = canonicalHighCount w) :
    strictSupersetContribution f u =
      strictSupersetContribution canonicalHighCount u := by
  exact strictSupersetContribution_congr hstrict

/-- Split an intersection count into exact and strict-superset terms. -/
lemma SignatureIntersectionCount_eq_self_add_strict
    (f : Signature → ℕ) (u : Signature) :
    SignatureIntersectionCount f u = f u + strictSupersetContribution f u := by
  classical
  let A : Signature → ℕ := fun w ↦ if u ⊆ w then f w else 0
  let B : Signature → ℕ := fun w ↦ if u ⊂ w then f w else 0
  have hsum_erase :
      (∑ w ∈ (Finset.univ : Finset Signature).erase u, A w) =
        ∑ w ∈ (Finset.univ : Finset Signature).erase u, B w := by
    refine Finset.sum_congr rfl ?_
    intro w hw
    have hne : w ≠ u := (Finset.mem_erase.mp hw).1
    by_cases huw : u ⊆ w
    · have hss : u ⊂ w := Finset.ssubset_iff_subset_ne.mpr ⟨huw, hne.symm⟩
      simp [A, B, huw, hss]
    · have hnss : ¬ u ⊂ w := fun h => huw h.1
      simp [A, B, huw, hnss]
  have hstrict_erase :
      strictSupersetContribution f u =
        ∑ w ∈ (Finset.univ : Finset Signature).erase u, B w := by
    rw [strictSupersetContribution]
    rw [← Finset.sum_erase_add (Finset.univ : Finset Signature) B (Finset.mem_univ u)]
    have hnss : ¬ u ⊂ u := by exact irrefl u
    simp [B, hnss]
  calc
    SignatureIntersectionCount f u =
        (∑ w ∈ (Finset.univ : Finset Signature).erase u, A w) + A u := by
          rw [SignatureIntersectionCount]
          exact (Finset.sum_erase_add (Finset.univ : Finset Signature) A
            (Finset.mem_univ u)).symm
    _ = (∑ w ∈ (Finset.univ : Finset Signature).erase u, A w) + f u := by
          simp [A]
    _ = f u + (∑ w ∈ (Finset.univ : Finset Signature).erase u, B w) := by
          rw [hsum_erase, Nat.add_comm]
    _ = f u + strictSupersetContribution f u := by
          rw [hstrict_erase]

/-- Divisibility after adding the same tail gives a congruence. -/
lemma modEq_self_of_split_divisibilities {d a b T : ℕ}
    (ha : d ∣ a + T) (hb : d ∣ b + T) :
    a ≡ b [MOD d] := by
  have ha0 : a + T ≡ 0 [MOD d] := Nat.modEq_zero_iff_dvd.mpr ha
  have hb0 : b + T ≡ 0 [MOD d] := Nat.modEq_zero_iff_dvd.mpr hb
  exact Nat.ModEq.add_right_cancel' T (ha0.trans hb0.symm)

/-- A small representative is a lower bound for congruent naturals. -/
lemma le_of_modEq_of_lt_modulus {d a b : ℕ}
    (hb : b < d) (hmod : a ≡ b [MOD d]) :
    b ≤ a := by
  have hbmod : b % d = b := Nat.mod_eq_of_lt hb
  have hamod : a % d = b := by
    simpa [Nat.ModEq, hbmod] using hmod
  calc
    b = a % d := hamod.symm
    _ ≤ a := Nat.mod_le a d

lemma SignatureIntersectionCount_fillRank_of_card_gt {k : ℕ} {f : Signature → ℕ}
    {u : Signature} (hu : k < u.card) :
    SignatureIntersectionCount (fillRank k f) u = SignatureIntersectionCount f u := by
  classical
  rw [SignatureIntersectionCount, SignatureIntersectionCount]
  refine Finset.sum_congr rfl ?_
  intro w _
  by_cases huw : u ⊆ w
  · rw [if_pos huw, if_pos huw, fillRank_eq_self_on_supersets_of_card_lt hu huw]
  · simp [huw]

lemma fillRank_self_add_strictSupersetContribution_dvd {k : ℕ} {f : Signature → ℕ}
    {u : Signature} (hu : u.card = k) (hupos : 0 < u.card) :
    u.card ∣ fillRank k f u + strictSupersetContribution f u := by
  rw [fillRank_eq_of_card hu]
  exact dvd_complement_mod_add hupos

/-- Filling rank `k` makes rank `k` valid. -/
lemma fillRank_satisfies_rank {k : ℕ} {f : Signature → ℕ} {u : Signature}
    (hu : u.card = k) (hupos : 0 < u.card) :
    u.card ∣ SignatureIntersectionCount (fillRank k f) u := by
  rw [SignatureIntersectionCount_eq_self_add_strict]
  have hcongr :
      strictSupersetContribution (fillRank k f) u =
        strictSupersetContribution f u := by
    apply strictSupersetContribution_congr
    intro w huw
    exact fillRank_eq_self_of_card_gt (by
      have hcard := Finset.card_lt_card huw
      omega)
  rw [hcongr]
  exact fillRank_self_add_strictSupersetContribution_dvd hu hupos

/-- Filling rank `k` preserves completed higher ranks. -/
lemma fillRank_preserves_completed_ranks {k : ℕ} {f : Signature → ℕ}
    (hf : ∀ u : Signature, u.Nonempty → k < u.card →
      u.card ∣ SignatureIntersectionCount f u) :
    ∀ u : Signature, u.Nonempty → k < u.card →
      u.card ∣ SignatureIntersectionCount (fillRank k f) u := by
  intro u hu hku
  rw [SignatureIntersectionCount_fillRank_of_card_gt hku]
  exact hf u hu hku

/-- After filling rank `k`, all ranks at least `k` are valid. -/
lemma fillRank_extends_completed_ranks {k : ℕ} {f : Signature → ℕ}
    (hf : ∀ u : Signature, u.Nonempty → k < u.card →
      u.card ∣ SignatureIntersectionCount f u) :
    ∀ u : Signature, u.Nonempty → k ≤ u.card →
      u.card ∣ SignatureIntersectionCount (fillRank k f) u := by
  intro u hu hku
  by_cases huk : u.card = k
  · exact fillRank_satisfies_rank huk (Finset.card_pos.mpr hu)
  · apply fillRank_preserves_completed_ranks hf
    · exact hu
    · omega

/-- Low-rank filling does not change the high-rank objective. -/
lemma SignatureObjective_fillRank_of_low {k : ℕ} {f : Signature → ℕ}
    (hk : k < 50) :
    SignatureObjective (fillRank k f) = SignatureObjective f := by
  rw [SignatureObjective, SignatureObjective]
  refine Finset.sum_congr rfl ?_
  intro v _
  by_cases hv : 50 ≤ v.card
  · rw [fillRank_eq_self_of_high hk hv]
  · simp [hv]

noncomputable def lowerFill : ℕ → Signature → ℕ
  | 0 => canonicalHighCount
  | n + 1 => fillRank (49 - n) (lowerFill n)

lemma lowerFill_valid
    (n : ℕ) (hn : n ≤ 49) :
    ∀ u : Signature, u.Nonempty → 50 - n ≤ u.card →
      u.card ∣ SignatureIntersectionCount (lowerFill n) u := by
  induction n with
  | zero =>
      intro u _hu hcard
      exact canonicalHighCount_valid_on_high u (by simpa using hcard)
  | succ n ih =>
      intro u hu hcard
      change u.card ∣
        SignatureIntersectionCount (fillRank (49 - n) (lowerFill n)) u
      apply fillRank_extends_completed_ranks
      · intro w hw hkw
        apply ih
        · omega
        · exact hw
        · omega
      · exact hu
      · omega

lemma lowerFill_preserves_high
    (n : ℕ) :
    ∀ v : Signature, 50 ≤ v.card →
      lowerFill n v = canonicalHighCount v := by
  induction n with
  | zero =>
      intro v _hv
      rfl
  | succ n ih =>
      intro v hv
      change fillRank (49 - n) (lowerFill n) v = canonicalHighCount v
      rw [fillRank_eq_self_of_high (by omega) hv, ih v hv]

lemma lowerFill_objective
    (n : ℕ) :
    SignatureObjective (lowerFill n) =
      SignatureObjective canonicalHighCount := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      change SignatureObjective (fillRank (49 - n) (lowerFill n)) =
        SignatureObjective canonicalHighCount
      rw [SignatureObjective_fillRank_of_low (by omega), ih]

/-- Fill ranks `49, ..., 1`. -/
lemma lower_rank_filling_exists :
    ∃ f : Signature → ℕ,
      (∀ u : Signature, u.Nonempty →
        u.card ∣ SignatureIntersectionCount f u) ∧
      (∀ v : Signature, 50 ≤ v.card → f v = canonicalHighCount v) ∧
      SignatureObjective f = SignatureObjective canonicalHighCount := by
  refine ⟨lowerFill 49, ?_, ?_, ?_⟩
  · intro u hu
    apply lowerFill_valid 49 (by norm_num) u hu
    have hpos : 0 < u.card := Finset.card_pos.mpr hu
    omega
  · exact lowerFill_preserves_high 49
  · exact lowerFill_objective 49

/-- Construct a valid signature count model extending the canonical high ranks. -/
lemma extend_canonical_high_counts :
    ∃ f : Signature → ℕ,
      SignatureCountCondition f ∧
      0 < f topSignature ∧
      (∀ v : Signature, 50 ≤ v.card → f v = canonicalHighCount v) ∧
      SignatureObjective f = solution := by
  rcases lower_rank_filling_exists with ⟨f, hf, hhigh, hobj⟩
  refine ⟨f, hf, ?_, hhigh, ?_⟩
  · rw [hhigh topSignature (by simp [topSignature])]
    simp [canonicalHighCount, topSignature]
  · rw [hobj, canonicalHighCount_objective]

abbrev RealizedPoint (f : Signature → ℕ) :=
  Sigma fun v : Signature => Fin (f v)

noncomputable def encodePoint (f : Signature → ℕ) :
    RealizedPoint f ↪ ℤ := by
  classical
  let e := Fintype.equivFin (RealizedPoint f)
  refine
    { toFun := fun x => ((e x).1 : ℤ)
      inj' := ?_ }
  intro x y hxy
  apply e.injective
  apply Fin.ext
  exact Int.ofNat.inj hxy

noncomputable def realizedFamily (f : Signature → ℕ)
    (i : Fin 100) : Set ℤ :=
  Set.range fun x : {x : RealizedPoint f // i ∈ x.fst} =>
    encodePoint f x.1

lemma realizedFamily_finite (f : Signature → ℕ) (i : Fin 100) :
    (realizedFamily f i).Finite := by
  classical
  exact Set.finite_range fun x : {x : RealizedPoint f // i ∈ x.fst} =>
    encodePoint f x.1

lemma mem_realizedFamily_iff
    {f : Signature → ℕ} {i : Fin 100} {x : RealizedPoint f} :
    encodePoint f x ∈ realizedFamily f i ↔ i ∈ x.fst := by
  constructor
  · intro hx
    rcases hx with ⟨y, hy⟩
    have hxy : y.1 = x := (encodePoint f).injective hy
    simpa [hxy] using y.2
  · intro hi
    exact ⟨⟨x, hi⟩, rfl⟩

lemma realizedPoint_subtype_card
    (f : Signature → ℕ) (p : Signature → Prop) [DecidablePred p] :
    Nat.card {x : RealizedPoint f // p x.fst} =
      ∑ v : Signature, if p v then f v else 0 := by
  classical
  let e :
      {x : RealizedPoint f // p x.fst} ≃
        Sigma (fun v : {v : Signature // p v} => Fin (f v.1)) :=
    Equiv.subtypeSigmaEquiv (fun v : Signature => Fin (f v)) p
  calc
    Nat.card {x : RealizedPoint f // p x.fst}
        = Fintype.card {x : RealizedPoint f // p x.fst} := Nat.card_eq_fintype_card
    _ = Fintype.card (Sigma (fun v : {v : Signature // p v} => Fin (f v.1))) :=
          Fintype.card_congr e
    _ = ∑ v : {v : Signature // p v}, f v.1 := by
          rw [Fintype.card_sigma]
          simp
    _ = ∑ v : Signature, if p v then f v else 0 := by
          rw [← Finset.sum_filter]
          rw [Finset.sum_subtype ((Finset.univ : Finset Signature).filter p) ?_
            (fun v => f v)]
          intro v
          simp

lemma realized_intersection_eq
    {f : Signature → ℕ} (u : Signature) (hu : u.Nonempty) :
    (⋂ i ∈ u, realizedFamily f i) =
      Set.range fun x : {x : RealizedPoint f // u ⊆ x.fst} =>
        encodePoint f x.1 := by
  classical
  ext z
  constructor
  · intro hz
    rcases hu with ⟨i0, hi0⟩
    have hzi0 : z ∈ realizedFamily f i0 := Set.mem_iInter₂.mp hz i0 hi0
    rcases hzi0 with ⟨x, hx⟩
    have hsub : u ⊆ x.1.fst := by
      intro i hi
      have hzi : z ∈ realizedFamily f i := Set.mem_iInter₂.mp hz i hi
      have henc : encodePoint f x.1 ∈ realizedFamily f i := by
        simpa [hx] using hzi
      exact (mem_realizedFamily_iff (x := x.1)).mp henc
    exact ⟨⟨x.1, hsub⟩, hx⟩
  · intro hz
    rcases hz with ⟨x, hx⟩
    rw [← hx]
    exact Set.mem_iInter₂.mpr fun i hi =>
      (mem_realizedFamily_iff (x := x.1)).mpr (x.2 hi)

lemma realized_intersection_ncard
    {f : Signature → ℕ} (u : Signature) (hu : u.Nonempty) :
    (⋂ i ∈ u, realizedFamily f i).ncard =
      SignatureIntersectionCount f u := by
  classical
  rw [realized_intersection_eq u hu]
  rw [Set.ncard_range_of_injective]
  · rw [realizedPoint_subtype_card, SignatureIntersectionCount]
  · intro x y hxy
    exact Subtype.ext ((encodePoint f).injective hxy)

lemma realized_membership_ncard
    {f : Signature → ℕ} (x : RealizedPoint f) :
    {i : Fin 100 | encodePoint f x ∈ realizedFamily f i}.ncard = x.fst.card := by
  classical
  have hfin : {i : Fin 100 | encodePoint f x ∈ realizedFamily f i}.Finite :=
    Set.finite_univ.subset (by intro i _; simp)
  rw [Set.ncard_eq_toFinset_card _ hfin]
  have htoFinset :
      hfin.toFinset = x.1 := by
    ext i
    simp [mem_realizedFamily_iff]
  rw [htoFinset]

lemma realized_objective_ncard
    {f : Signature → ℕ} :
    {z : ℤ | InAtLeastKSubsets (realizedFamily f) 50 z}.ncard =
      SignatureObjective f := by
  classical
  have hobj_eq :
      {z : ℤ | InAtLeastKSubsets (realizedFamily f) 50 z} =
        Set.range fun x : {x : RealizedPoint f // 50 ≤ x.fst.card} =>
          encodePoint f x.1 := by
    ext z
    constructor
    · intro hz
      have hfin : {i : Fin 100 | z ∈ realizedFamily f i}.Finite :=
        Set.finite_univ.subset (by intro i _; simp)
      have hpos : 0 < {i : Fin 100 | z ∈ realizedFamily f i}.ncard :=
        lt_of_lt_of_le (by norm_num) hz
      rcases (Set.ncard_pos hfin).mp hpos with ⟨i, hi⟩
      rcases hi with ⟨x, hx⟩
      have hhigh : 50 ≤ x.1.fst.card := by
        rw [← realized_membership_ncard x.1]
        simpa [hx] using hz
      exact ⟨⟨x.1, hhigh⟩, hx⟩
    · intro hz
      rcases hz with ⟨x, hx⟩
      rw [← hx]
      change 50 ≤ {i : Fin 100 | encodePoint f x.1 ∈ realizedFamily f i}.ncard
      rw [realized_membership_ncard x.1]
      exact x.2
  rw [hobj_eq]
  rw [Set.ncard_range_of_injective]
  · change Nat.card {x : RealizedPoint f // (fun v : Signature => 50 ≤ v.card) x.fst} =
      SignatureObjective f
    rw [SignatureObjective]
    exact realizedPoint_subtype_card f (fun v : Signature => 50 ≤ v.card)
  · intro x y hxy
    exact Subtype.ext ((encodePoint f).injective hxy)

/-- Realize finite signature counts by finite integer sets. -/
lemma realize_signature_counts
    {f : Signature → ℕ}
    (hf : SignatureCountCondition f) (htop : 0 < f topSignature) :
    ∃ S : Fin 100 → Set ℤ,
      Good S ∧
      {z : ℤ | InAtLeastKSubsets S 50 z }.ncard = SignatureObjective f := by
  classical
  refine ⟨realizedFamily f, ?_, realized_objective_ncard⟩
  refine ⟨realizedFamily_finite f, ?_, ?_⟩
  · let x : RealizedPoint f := ⟨topSignature, ⟨0, htop⟩⟩
    apply Set.nonempty_iff_ne_empty.mp
    refine ⟨encodePoint f x, ?_⟩
    exact Set.mem_iInter.mpr fun i =>
      (mem_realizedFamily_iff (x := x)).mpr (by
        change i ∈ topSignature
        simp [topSignature])
  · intro T hT
    rcases hf T hT with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [realized_intersection_ncard T hT, hk, Nat.mul_comm]

/-- Exact signature counts extracted from an actual family. -/
noncomputable def signatureCount (S : Fin 100 → Set ℤ) (v : Signature) : ℕ := by
  classical
  exact if v.Nonempty then {z : ℤ | signatureOf S z = v}.ncard else 0

lemma signatureCount_condition_of_good (S : Fin 100 → Set ℤ) (hS : Good S) :
    SignatureCountCondition (signatureCount S) := by
  -- Partition the intersection by exact signatures.
  classical
  intro u hu
  rcases hS.card u hu with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  rw [mul_comm k u.card] at hk
  rw [← hk]
  symm
  have hinter_eq :
      (⋂ i ∈ u, S i) = {z : ℤ | u ⊆ signatureOf S z} := by
    ext z
    constructor
    · intro hz i hi
      have hzi : z ∈ S i := Set.mem_iInter₂.mp hz i hi
      simp [signatureOf, hzi]
    · intro hz
      exact Set.mem_iInter₂.mpr (fun i hi => by
        have hsig : i ∈ signatureOf S z := hz hi
        simpa [signatureOf] using hsig)
  have hinter_finite : (⋂ i ∈ u, S i).Finite := by
    rcases hu with ⟨i, hi⟩
    exact (hS.finite i).subset (by
      intro z hz
      exact Set.mem_iInter₂.mp hz i hi)
  calc
    (⋂ i ∈ u, S i).ncard
        = {z : ℤ | u ⊆ signatureOf S z}.ncard := by rw [hinter_eq]
    _ = ∑ v : Signature, if u ⊆ v then {z : ℤ | signatureOf S z = v}.ncard else 0 := by
          exact ncard_preimage_eq_sum_fibers (signatureOf S) (fun v : Signature => u ⊆ v)
            (by simpa [← hinter_eq] using hinter_finite)
    _ = SignatureIntersectionCount (signatureCount S) u := by
          rw [SignatureIntersectionCount]
          refine Finset.sum_congr rfl ?_
          intro v _
          by_cases huv : u ⊆ v
          · have hvnonempty : v.Nonempty := by
              rcases hu with ⟨i, hi⟩
              exact ⟨i, huv hi⟩
            simp [huv, signatureCount, hvnonempty]
          · simp [huv]

lemma signatureCount_top_pos_of_good (S : Fin 100 → Set ℤ) (hS : Good S) :
    0 < signatureCount S topSignature := by
  classical
  have htop : topSignature.Nonempty := by
    exact ⟨0, by simp [topSignature]⟩
  have hnonempty : (⋂ i, S i).Nonempty := by
    exact Set.nonempty_iff_ne_empty.mpr hS.nonempty_inter
  rcases hnonempty with ⟨z, hz⟩
  have hzsig : signatureOf S z = topSignature := by
    ext i
    have hzi : z ∈ S i := Set.mem_iInter.mp hz i
    simp [signatureOf, topSignature, hzi]
  have hfiber_nonempty :
      {z : ℤ | signatureOf S z = topSignature}.Nonempty := ⟨z, hzsig⟩
  have hfiber_finite :
      {z : ℤ | signatureOf S z = topSignature}.Finite := by
    have hsubset : {z : ℤ | signatureOf S z = topSignature} ⊆ S 0 := by
      intro y hy
      have hmem : (0 : Fin 100) ∈ signatureOf S y := by
        rw [hy]
        simp [topSignature]
      simpa [signatureOf] using hmem
    exact (hS.finite 0).subset hsubset
  have hpos : 0 < {z : ℤ | signatureOf S z = topSignature}.ncard := by
    exact (Set.ncard_pos hfiber_finite).mpr hfiber_nonempty
  simpa [signatureCount, htop] using hpos

lemma signatureObjective_eq_original_objective
    (S : Fin 100 → Set ℤ) (hS : Good S) :
    SignatureObjective (signatureCount S) =
      {z : ℤ | InAtLeastKSubsets S 50 z }.ncard := by
  -- Partition high-membership elements by exact signature.
  classical
  have hsig_card :
      ∀ z : ℤ, {i : Fin 100 | z ∈ S i}.ncard = (signatureOf S z).card := by
    intro z
    have hfin : {i : Fin 100 | z ∈ S i}.Finite :=
      Set.finite_univ.subset (by intro i _; simp)
    rw [Set.ncard_eq_toFinset_card _ hfin]
    simp [signatureOf]
  have hobj_set :
      {z : ℤ | InAtLeastKSubsets S 50 z}
        = {z : ℤ | 50 ≤ (signatureOf S z).card} := by
    ext z
    simp [InAtLeastKSubsets, hsig_card z]
  have hunion_finite : (⋃ i, S i).Finite := Set.finite_iUnion hS.finite
  have hobj_finite : {z : ℤ | 50 ≤ (signatureOf S z).card}.Finite := by
    refine hunion_finite.subset ?_
    intro z hz
    have hpos : 0 < {i : Fin 100 | z ∈ S i}.ncard := by
      have hsigpos : 0 < (signatureOf S z).card := lt_of_lt_of_le (by norm_num) hz
      rw [hsig_card z]
      exact hsigpos
    have hnonempty : {i : Fin 100 | z ∈ S i}.Nonempty := by
      exact (Set.ncard_pos (Set.finite_univ.subset (by intro i _; simp))).mp hpos
    rcases hnonempty with ⟨i, hi⟩
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  calc
    SignatureObjective (signatureCount S)
        = ∑ v : Signature, if 50 ≤ v.card then {z : ℤ | signatureOf S z = v}.ncard else 0 := by
          rw [SignatureObjective]
          refine Finset.sum_congr rfl ?_
          intro v _
          by_cases hv : 50 ≤ v.card
          · have hvnonempty : v.Nonempty := by
              cases v.eq_empty_or_nonempty with
              | inl hempty =>
                  exfalso
                  simp [hempty] at hv
              | inr h => exact h
            simp [hv, signatureCount, hvnonempty]
          · simp [hv]
    _ = {z : ℤ | 50 ≤ (signatureOf S z).card}.ncard := by
          exact (ncard_preimage_eq_sum_fibers (signatureOf S)
            (fun v : Signature => 50 ≤ v.card) hobj_finite).symm
    _ = {z : ℤ | InAtLeastKSubsets S 50 z}.ncard := by rw [hobj_set]

lemma topSignature_card : topSignature.card = 100 := by
  simp [topSignature]

lemma topSignature_nonempty : topSignature.Nonempty := by
  exact ⟨0, by simp [topSignature]⟩

lemma eq_topSignature_of_card_eq_100 {v : Signature} (hv : v.card = 100) :
    v = topSignature := by
  apply Finset.eq_univ_of_card
  simp [hv]

lemma card_lt_100_of_ne_topSignature {v : Signature} (hvt : v ≠ topSignature) :
    v.card < 100 := by
  have hle : v.card ≤ 100 := by
    have h := Finset.card_le_univ v
    simpa using h
  by_contra hnot
  have hv : v.card = 100 := by omega
  exact hvt (eq_topSignature_of_card_eq_100 hv)

lemma canonicalHighCount_top : canonicalHighCount topSignature = 100 := by
  simp [canonicalHighCount, topSignature]

lemma canonicalHighCount_lt_card_of_high_ne_top {v : Signature}
    (hv : 50 ≤ v.card) (hvt : v ≠ topSignature) :
    canonicalHighCount v < v.card := by
  have hlt : v.card < 100 := card_lt_100_of_ne_topSignature hvt
  simp [canonicalHighCount, hv]
  omega

lemma canonicalHighCount_le_card_of_high {v : Signature} (hv : 50 ≤ v.card) :
    canonicalHighCount v ≤ v.card := by
  by_cases htop : v = topSignature
  · subst htop
    simp [canonicalHighCount, topSignature]
  · exact le_of_lt (canonicalHighCount_lt_card_of_high_ne_top hv htop)

lemma iterate_pushDown_self (f : Signature → ℕ) (v : Signature) (n : ℕ) :
    (Nat.iterate (fun g : Signature → ℕ => pushDown g v) n f) v =
      f v - n * v.card := by
  induction n with
  | zero => simp [Nat.iterate]
  | succ n ih =>
      rw [Function.iterate_succ']
      simp only [Function.comp_apply]
      rw [show pushDown ((fun g : Signature → ℕ => pushDown g v)^[n] f) v v =
          ((fun g : Signature → ℕ => pushDown g v)^[n] f) v - v.card by
        simp [pushDown], ih, Nat.sub_sub]
      congr 1
      ring

lemma iterate_pushDown_condition {f : Signature → ℕ} {v : Signature} (n : ℕ)
    (hsteps : n * v.card ≤ f v) (hf : SignatureCountCondition f) :
    SignatureCountCondition
      (Nat.iterate (fun g : Signature → ℕ => pushDown g v) n f) := by
  induction n with
  | zero => simpa [Nat.iterate]
  | succ n ih =>
      rw [Function.iterate_succ']
      change SignatureCountCondition
        (pushDown ((Nat.iterate (fun g : Signature → ℕ => pushDown g v) n f)) v)
      apply pushDown_preserves_condition
      · rw [iterate_pushDown_self]
        have hn : (n + 1) * v.card = n * v.card + v.card := by ring
        omega
      · apply ih
        have : n * v.card ≤ (n + 1) * v.card :=
          Nat.mul_le_mul_right v.card (Nat.le_succ n)
        omega

lemma iterate_pushDown_objective_le {f : Signature → ℕ} {v : Signature} (n : ℕ)
    (hv : 50 ≤ v.card) (hsteps : n * v.card ≤ f v) :
    SignatureObjective
        (Nat.iterate (fun g : Signature → ℕ => pushDown g v) n f) ≤
      SignatureObjective f := by
  induction n with
  | zero => simp [Nat.iterate]
  | succ n ih =>
      rw [Function.iterate_succ']
      change SignatureObjective
          (pushDown ((Nat.iterate (fun g : Signature → ℕ => pushDown g v) n f)) v) ≤
        SignatureObjective f
      have hprev : n * v.card ≤ f v := by
        have : n * v.card ≤ (n + 1) * v.card :=
          Nat.mul_le_mul_right v.card (Nat.le_succ n)
        omega
      have henough : v.card ≤
          (Nat.iterate (fun g : Signature → ℕ => pushDown g v) n f) v := by
        rw [iterate_pushDown_self]
        have hn : (n + 1) * v.card = n * v.card + v.card := by ring
        omega
      by_cases hlarge : 50 < v.card
      · rw [pushDown_preserves_objective_of_large hlarge henough]
        exact ih hprev
      · have hmid : v.card = 50 := by omega
        have hdrop := pushDown_decreases_objective_at_middle hmid henough
        have hle_step : SignatureObjective (pushDown
            (Nat.iterate (fun g : Signature → ℕ => pushDown g v) n f) v) ≤
            SignatureObjective
              (Nat.iterate (fun g : Signature → ℕ => pushDown g v) n f) := by
          omega
        exact le_trans hle_step (ih hprev)

lemma pushDown_to_canonical_count {f : Signature → ℕ} {v : Signature}
    (hf : SignatureCountCondition f) (hv : 50 ≤ v.card)
    (hcan_le : canonicalHighCount v ≤ f v)
    (hdiv : v.card ∣ f v - canonicalHighCount v) :
    let n := (f v - canonicalHighCount v) / v.card
    let g := Nat.iterate (fun h : Signature → ℕ => pushDown h v) n f
    SignatureCountCondition g ∧ SignatureObjective g ≤ SignatureObjective f ∧
      g v = canonicalHighCount v := by
  dsimp
  let n := (f v - canonicalHighCount v) / v.card
  have hmul : n * v.card = f v - canonicalHighCount v := by
    dsimp [n]
    exact Nat.div_mul_cancel hdiv
  have hsteps : n * v.card ≤ f v := by omega
  refine ⟨iterate_pushDown_condition n hsteps hf, iterate_pushDown_objective_le n hv hsteps, ?_⟩
  rw [iterate_pushDown_self, hmul]
  omega

/-- Signatures of rank `k`. -/
def rankSignatures (k : ℕ) : Finset Signature :=
  (Finset.univ : Finset Signature).filter fun v : Signature => v.card = k

lemma mem_rankSignatures {k : ℕ} {v : Signature} :
    v ∈ rankSignatures k ↔ v.card = k := by
  simp [rankSignatures]

lemma pushDown_eq_self_of_not_affected {f : Signature → ℕ} {v w : Signature}
    (hneq : w ≠ v)
    (hnot : ¬ (w ⊆ v ∧ w.card + 1 = v.card)) :
    pushDown f v w = f w := by
  simp [pushDown, hneq, hnot]

lemma pushDown_eq_self_of_card_ge_ne {f : Signature → ℕ} {v w : Signature}
    (hcard : v.card ≤ w.card) (hneq : w ≠ v) :
    pushDown f v w = f w := by
  apply pushDown_eq_self_of_not_affected hneq
  intro h
  omega

lemma pushDown_eq_self_of_card_gt {f : Signature → ℕ} {v w : Signature}
    (hcard : v.card < w.card) :
    pushDown f v w = f w := by
  apply pushDown_eq_self_of_card_ge_ne (le_of_lt hcard)
  intro h
  subst h
  omega

lemma iterate_pushDown_eq_self_of_not_affected
    (f : Signature → ℕ) (v w : Signature) (n : ℕ)
    (hneq : w ≠ v)
    (hnot : ¬ (w ⊆ v ∧ w.card + 1 = v.card)) :
    (Nat.iterate (fun g : Signature → ℕ => pushDown g v) n f) w = f w := by
  induction n with
  | zero =>
      simp [Nat.iterate]
  | succ n ih =>
      rw [Function.iterate_succ']
      change pushDown (Nat.iterate (fun g : Signature → ℕ => pushDown g v) n f) v w = f w
      rw [pushDown_eq_self_of_not_affected hneq hnot, ih]

lemma iterate_pushDown_eq_self_of_card_ge_ne
    (f : Signature → ℕ) (v w : Signature) (n : ℕ)
    (hcard : v.card ≤ w.card) (hneq : w ≠ v) :
    (Nat.iterate (fun g : Signature → ℕ => pushDown g v) n f) w = f w := by
  apply iterate_pushDown_eq_self_of_not_affected f v w n hneq
  intro h
  omega

lemma iterate_pushDown_eq_self_of_card_gt
    (f : Signature → ℕ) (v w : Signature) (n : ℕ)
    (hcard : v.card < w.card) :
    (Nat.iterate (fun g : Signature → ℕ => pushDown g v) n f) w = f w := by
  apply iterate_pushDown_eq_self_of_card_ge_ne f v w n (le_of_lt hcard)
  intro h
  subst h
  omega

lemma iterate_pushDown_preserves_canonical_of_card_gt
    {f : Signature → ℕ} {v w : Signature} {n : ℕ}
    (hcard : v.card < w.card)
    (hw : f w = canonicalHighCount w) :
    (Nat.iterate (fun g : Signature → ℕ => pushDown g v) n f) w =
      canonicalHighCount w := by
  rw [iterate_pushDown_eq_self_of_card_gt f v w n hcard, hw]

lemma iterate_pushDown_preserves_canonical_of_same_rank_ne
    {f : Signature → ℕ} {v w : Signature} {n : ℕ}
    (hcard : v.card = w.card) (hneq : w ≠ v)
    (hw : f w = canonicalHighCount w) :
    (Nat.iterate (fun g : Signature → ℕ => pushDown g v) n f) w =
      canonicalHighCount w := by
  rw [iterate_pushDown_eq_self_of_card_ge_ne f v w n (by omega) hneq, hw]

/-- Push `v` down to its canonical high-rank residue. -/
def normalizeSignature (f : Signature → ℕ) (v : Signature) : Signature → ℕ :=
  let n := (f v - canonicalHighCount v) / v.card
  Nat.iterate (fun g : Signature → ℕ => pushDown g v) n f

lemma normalizeSignature_eq_self_of_card_gt
    (f : Signature → ℕ) {v w : Signature} (hcard : v.card < w.card) :
    normalizeSignature f v w = f w := by
  unfold normalizeSignature
  exact iterate_pushDown_eq_self_of_card_gt f v w
    ((f v - canonicalHighCount v) / v.card) hcard

lemma normalizeSignature_preserves_canonical_of_card_gt
    {f : Signature → ℕ} {v w : Signature}
    (hcard : v.card < w.card)
    (hw : f w = canonicalHighCount w) :
    normalizeSignature f v w = canonicalHighCount w := by
  rw [normalizeSignature_eq_self_of_card_gt f hcard, hw]

lemma normalizeSignature_preserves_canonical_of_same_rank_ne
    {f : Signature → ℕ} {v w : Signature}
    (hcard : v.card = w.card) (hneq : w ≠ v)
    (hw : f w = canonicalHighCount w) :
    normalizeSignature f v w = canonicalHighCount w := by
  unfold normalizeSignature
  exact iterate_pushDown_preserves_canonical_of_same_rank_ne hcard hneq hw

lemma high_signature_count_forced_after_supersets_normalized
    {f : Signature → ℕ} {v : Signature}
    (hf : SignatureCountCondition f) (htop : 0 < f topSignature)
    (hv : 50 ≤ v.card)
    (hstrict : ∀ w : Signature, v ⊂ w → f w = canonicalHighCount w) :
    canonicalHighCount v ≤ f v ∧ v.card ∣ f v - canonicalHighCount v := by
  -- Normalized strict supersets force the residue at `v`.
  have hvpos : 0 < v.card := by omega
  have hvnonempty : v.Nonempty := Finset.card_pos.mp hvpos
  have htail :
      strictSupersetContribution f v =
        strictSupersetContribution canonicalHighCount v :=
    strictSupersetContribution_eq_canonical_of_strict hstrict
  have hf_split :
      v.card ∣ f v + strictSupersetContribution f v := by
    have h := hf v hvnonempty
    rwa [SignatureIntersectionCount_eq_self_add_strict] at h
  have hf_common :
      v.card ∣ f v + strictSupersetContribution canonicalHighCount v := by
    simpa [htail] using hf_split
  have hcanon_split :
      v.card ∣
        canonicalHighCount v + strictSupersetContribution canonicalHighCount v := by
    have h := canonicalHighCount_valid_on_high v hv
    rwa [SignatureIntersectionCount_eq_self_add_strict] at h
  have hmod : f v ≡ canonicalHighCount v [MOD v.card] :=
    modEq_self_of_split_divisibilities hf_common hcanon_split
  have hcan_le : canonicalHighCount v ≤ f v := by
    by_cases htop_v : v = topSignature
    · subst htop_v
      have hmod0 : f topSignature ≡ 0 [MOD topSignature.card] := by
        simpa [canonicalHighCount_top, topSignature_card, Nat.ModEq] using hmod
      have hdvd_top : topSignature.card ∣ f topSignature :=
        Nat.modEq_zero_iff_dvd.mp hmod0
      rcases hdvd_top with ⟨m, hm⟩
      have hmpos : 0 < m := by
        by_contra hnot
        have hmzero : m = 0 := Nat.eq_zero_of_not_pos hnot
        subst hmzero
        simp at hm
        omega
      have hle_top : topSignature.card ≤ f topSignature := by
        calc
          topSignature.card = topSignature.card * 1 := by rw [mul_one]
          _ ≤ topSignature.card * m :=
            Nat.mul_le_mul_left topSignature.card (Nat.succ_le_of_lt hmpos)
          _ = f topSignature := hm.symm
      simpa [canonicalHighCount_top, topSignature_card] using hle_top
    · exact le_of_modEq_of_lt_modulus
        (canonicalHighCount_lt_card_of_high_ne_top hv htop_v) hmod
  refine ⟨hcan_le, ?_⟩
  exact (Nat.modEq_iff_dvd' hcan_le).mp hmod.symm

lemma normalizeSignature_spec
    {f : Signature → ℕ} {v : Signature}
    (hf : SignatureCountCondition f) (htop : 0 < f topSignature)
    (hv : 50 ≤ v.card)
    (hstrict : ∀ w : Signature, v ⊂ w → f w = canonicalHighCount w) :
    SignatureCountCondition (normalizeSignature f v) ∧
      SignatureObjective (normalizeSignature f v) ≤ SignatureObjective f ∧
      normalizeSignature f v v = canonicalHighCount v := by
  rcases high_signature_count_forced_after_supersets_normalized hf htop hv hstrict with
    ⟨hcan_le, hdiv⟩
  simpa [normalizeSignature] using pushDown_to_canonical_count hf hv hcan_le hdiv

lemma normalizeSignature_top_pos
    {f : Signature → ℕ} {v : Signature}
    (htop : 0 < f topSignature)
    (hcanon : normalizeSignature f v v = canonicalHighCount v) :
    0 < normalizeSignature f v topSignature := by
  by_cases hvt : v = topSignature
  · subst hvt
    rw [hcanon, canonicalHighCount_top]
    norm_num
  · have hcard : v.card < topSignature.card := card_lt_100_of_ne_topSignature hvt
    rw [normalizeSignature_eq_self_of_card_gt f hcard]
    exact htop

/-- Normalize a finite subset of one rank. -/
lemma normalize_rank_subset
    (k : ℕ) (A : Finset Signature) (f : Signature → ℕ)
    (hk : 50 ≤ k)
    (hA : ∀ v : Signature, v ∈ A → v.card = k)
    (hf : SignatureCountCondition f)
    (htop : 0 < f topSignature)
    (hgt : ∀ w : Signature, k < w.card → f w = canonicalHighCount w) :
    ∃ g : Signature → ℕ,
      SignatureCountCondition g ∧
      SignatureObjective g ≤ SignatureObjective f ∧
      0 < g topSignature ∧
      (∀ w : Signature, k < w.card → g w = canonicalHighCount w) ∧
      (∀ v : Signature, v ∈ A → g v = canonicalHighCount v) := by
  classical
  revert hA f
  refine Finset.induction_on A ?base ?step
  · intro f _hA hf htop hgt
    refine ⟨f, hf, le_rfl, htop, hgt, ?_⟩
    intro v hv
    simp at hv
  · intro v A hv_not_mem ih f hA hf htop hgt
    have hA0 : ∀ w : Signature, w ∈ A → w.card = k := by
      intro w hw
      exact hA w (by simp [hw])
    have hv_card : v.card = k := hA v (by simp [hv_not_mem])
    rcases ih f hA0 hf htop hgt with
      ⟨g0, hg0, hobj0, htop0, hgt0, hA0canon⟩
    have hv_high : 50 ≤ v.card := by omega
    have hstrict : ∀ w : Signature, v ⊂ w →
        g0 w = canonicalHighCount w := by
      intro w hvw
      apply hgt0
      have hcard := Finset.card_lt_card hvw
      omega
    rcases normalizeSignature_spec hg0 htop0 hv_high hstrict with
      ⟨hg1, hobj1, hcanonv⟩
    refine ⟨normalizeSignature g0 v, hg1, le_trans hobj1 hobj0,
      normalizeSignature_top_pos htop0 hcanonv, ?_, ?_⟩
    · intro w hkw
      apply normalizeSignature_preserves_canonical_of_card_gt
      · omega
      · exact hgt0 w hkw
    · intro w hw
      rw [Finset.mem_insert] at hw
      rcases hw with rfl | hwA
      · exact hcanonv
      · apply normalizeSignature_preserves_canonical_of_same_rank_ne
        · rw [hv_card, hA0 w hwA]
        · intro hwv
          subst hwv
          exact hv_not_mem hwA
        · exact hA0canon w hwA

/-- Normalize all signatures of one rank. -/
lemma normalize_rank
    (k : ℕ) (f : Signature → ℕ)
    (hk : 50 ≤ k)
    (hf : SignatureCountCondition f)
    (htop : 0 < f topSignature)
    (hgt : ∀ w : Signature, k < w.card → f w = canonicalHighCount w) :
    ∃ g : Signature → ℕ,
      SignatureCountCondition g ∧
      SignatureObjective g ≤ SignatureObjective f ∧
      0 < g topSignature ∧
      (∀ w : Signature, k ≤ w.card → g w = canonicalHighCount w) := by
  rcases normalize_rank_subset k (rankSignatures k) f hk
      (by intro v hv; exact mem_rankSignatures.mp hv) hf htop hgt with
    ⟨g, hg, hobj, htopg, hgtg, hrank⟩
  refine ⟨g, hg, hobj, htopg, ?_⟩
  intro w hkw
  by_cases hgtw : k < w.card
  · exact hgtg w hgtw
  · have hw : w.card = k := by omega
    exact hrank w (mem_rankSignatures.mpr hw)

lemma smooth_high_signatures_from_rank
    (k : ℕ) (hk49 : 49 ≤ k) (hk100 : k ≤ 100)
    (f : Signature → ℕ)
    (hf : SignatureCountCondition f) (htop : 0 < f topSignature)
    (hgt : ∀ w : Signature, k < w.card → f w = canonicalHighCount w) :
    ∃ g : Signature → ℕ,
      SignatureCountCondition g ∧
      SignatureObjective g ≤ SignatureObjective f ∧
      0 < g topSignature ∧
      (∀ w : Signature, 50 ≤ w.card → g w = canonicalHighCount w) := by
  classical
  revert hk100 f
  refine Nat.le_induction ?base ?step k hk49
  · intro _hk100 f hf htop hgt
    refine ⟨f, hf, le_rfl, htop, ?_⟩
    intro w hw
    exact hgt w (by omega)
  · intro k hk49 ih hk_succ_100 f hf htop hgt
    rcases normalize_rank (k + 1) f (by omega) hf htop hgt with
      ⟨g1, hg1, hobj1, htop1, hge1⟩
    have hgt1 : ∀ w : Signature, k < w.card → g1 w = canonicalHighCount w := by
      intro w hw
      exact hge1 w (by omega)
    rcases ih (by omega) g1 hg1 htop1 hgt1 with
      ⟨g, hg, hobj, htopg, hcanon⟩
    exact ⟨g, hg, le_trans hobj hobj1, htopg, hcanon⟩

/-- Normalize high ranks from `100` down to `50`. -/
lemma smooth_high_signatures_by_ranks
    (f : Signature → ℕ)
    (hf : SignatureCountCondition f) (htop : 0 < f topSignature) :
    ∃ g : Signature → ℕ,
      SignatureCountCondition g ∧
      SignatureObjective g ≤ SignatureObjective f ∧
      0 < g topSignature ∧
      (∀ v : Signature, 50 ≤ v.card → g v = canonicalHighCount v) := by
  have hgt0 : ∀ w : Signature, 100 < w.card → f w = canonicalHighCount w := by
    intro w hw
    have hle : w.card ≤ 100 := by
      have h := Finset.card_le_univ w
      simpa using h
    omega
  exact smooth_high_signatures_from_rank 100 (by norm_num) (by norm_num) f hf htop hgt0

lemma smooth_high_signatures_to_canonical
    (f : Signature → ℕ)
    (hf : SignatureCountCondition f) (htop : 0 < f topSignature) :
    ∃ g : Signature → ℕ,
      SignatureCountCondition g ∧
      SignatureObjective g ≤ SignatureObjective f ∧
      (∀ v : Signature, 50 ≤ v.card → g v = canonicalHighCount v) := by
  rcases smooth_high_signatures_by_ranks f hf htop with
    ⟨g, hg, hobj, _htopg, hcanonical⟩
  exact ⟨g, hg, hobj, hcanonical⟩

/-- Smoothing gives the signature-model lower bound. -/
lemma signature_model_lower_bound
    (f : Signature → ℕ)
    (hf : SignatureCountCondition f) (htop : 0 < f topSignature) :
    solution ≤ SignatureObjective f := by
  classical
  rcases smooth_high_signatures_to_canonical f hf htop with
    ⟨g, _hg, hobj_le, hcanonical⟩
  have hgobj : SignatureObjective g = SignatureObjective canonicalHighCount := by
    rw [SignatureObjective, SignatureObjective]
    refine Finset.sum_congr rfl ?_
    intro v _
    by_cases hv : 50 ≤ v.card
    · simp [hv, hcanonical v hv]
    · simp [hv]
  calc
    solution = SignatureObjective canonicalHighCount := canonicalHighCount_objective.symm
    _ = SignatureObjective g := hgobj.symm
    _ ≤ SignatureObjective f := hobj_le

/-- The signature construction realizes the claimed value. -/
lemma construction_attains_solution :
    ∃ S, Good S ∧
      solution = {z : ℤ | InAtLeastKSubsets S 50 z }.ncard := by
  rcases extend_canonical_high_counts with ⟨f, hf, htop, _hhigh, hobj⟩
  rcases realize_signature_counts hf htop with ⟨S, hS, hSobj⟩
  refine ⟨S, hS, ?_⟩
  rw [hSobj, hobj]

/-- Lower bound for any good family. -/
lemma at_least_solution_elements (S : Fin 100 → Set ℤ) (hS : Good S) :
    solution ≤ {z : ℤ | InAtLeastKSubsets S 50 z }.ncard := by
  rw [← signatureObjective_eq_original_objective S hS]
  exact signature_model_lower_bound
    (signatureCount S)
    (signatureCount_condition_of_good S hS)
    (signatureCount_top_pos_of_good S hS)

snip end

problem usa2024_p2 :
    IsLeast
      { k | ∃ S, Good S ∧
             k = {z : ℤ | InAtLeastKSubsets S 50 z }.ncard } solution :=
  by
    constructor
    · exact construction_attains_solution
    · intro k hk
      rcases hk with ⟨S, hS, hk⟩
      rw [hk]
      exact at_least_solution_elements S hS


end Usa2024P2
