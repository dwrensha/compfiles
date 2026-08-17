/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Int.ConditionallyCompleteOrder
public import Mathlib.Data.Int.Star
public import Mathlib.Data.Rat.Star
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.Ring.Basic
public import ProblemExtraction

@[expose] public section

problem_file {
  tags := [.Combinatorics]
}

/-!
# USA Mathematical Olympiad 2010, Problem 6

There are 68 ordered pairs (not necessarily distinct) of nonzero integers
on a blackboard. It's known that for no integer k does both (k, k) and
(−k, −k) appear. A student erases some of the 136 integers such that no two
erased integers have sum zero, and scores one point for each ordered pair
with at least one erased integer. What is the maximum possible score the
student can guarantee?
-/

namespace Usa2010P6

/-- A choice of integers to erase is valid if no two erased integers sum to zero.
(If a value `x` is erased at some position, erasing every occurrence of `x` is never
worse, so the optimal strategies correspond exactly to sets of values `T` with
`x ∈ T → -x ∉ T`.) -/
def ValidErase (T : Finset ℤ) : Prop := ∀ x ∈ T, -x ∉ T

/-- The score obtained by erasing the set `T` from the board `L`:
one point for each ordered pair with at least one erased entry. -/
def score (L : List (ℤ × ℤ)) (T : Finset ℤ) : ℕ :=
  (L.filter (fun p => decide (p.1 ∈ T ∨ p.2 ∈ T))).length

/-- A valid board: 68 ordered pairs of nonzero integers such that for no `k`
do both `(k, k)` and `(-k, -k)` appear. -/
structure ValidBoard (L : List (ℤ × ℤ)) : Prop where
  length_eq : L.length = 68
  nonzero : ∀ p ∈ L, p.1 ≠ 0 ∧ p.2 ≠ 0
  no_both_loops : ∀ k : ℤ, (k, k) ∈ L → (-k, -k) ∉ L

/-- The maximum score the student can guarantee. -/
determine N : ℕ := 43

snip begin

/-- The probability weight: rational `309/500` approximating `(√5-1)/2`,
satisfying `q² + q ≤ 1` and `68 * q > 42`. -/
def qProb : ℚ := 309 / 500

/-- weight of a strategy `t` (the set of vertices where we pick the "a" side) -/
noncomputable def w (n : ℕ) (q : ℚ) (t : Finset (Fin n)) : ℚ :=
  q ^ t.card * (1 - q) ^ (n - t.card)

/-- Conditional marginal: total weight of strategies containing all of `S₀` and
disjoint from `S₁`, when `S₀ ∩ S₁ = ∅`. -/
lemma cond_weight (n : ℕ) (q : ℚ) (S₀ S₁ : Finset (Fin n)) (hd : Disjoint S₀ S₁) :
    ∑ t : Finset (Fin n), (if S₀ ⊆ t ∧ Disjoint t S₁ then w n q t else 0)
      = q ^ S₀.card * (1 - q) ^ S₁.card := by
  set f : Fin n → ℚ := fun i => if i ∈ S₁ then 0 else q
  set g : Fin n → ℚ := fun i => if i ∈ S₀ then 0 else 1 - q
  have key := Finset.prod_add f g (Finset.univ : Finset (Fin n))
  have hLHS : ∏ i ∈ (Finset.univ : Finset (Fin n)), (f i + g i)
      = q ^ S₀.card * (1 - q) ^ S₁.card := by
    have hfg : ∀ i : Fin n, f i + g i = if i ∈ S₀ then q else (if i ∈ S₁ then 1 - q else 1) := by
      intro i
      simp only [f, g]
      by_cases h0 : i ∈ S₀
      · have h1 : i ∉ S₁ := Finset.disjoint_left.mp hd h0
        simp [h0, h1]
      · by_cases h1 : i ∈ S₁
        · simp [h0, h1]
        · simp [h0, h1]
    rw [Finset.prod_congr rfl (fun i _ => hfg i), Finset.prod_ite, Finset.prod_ite_mem, Finset.prod_const, Finset.prod_const
      , Finset.inter_comm, Finset.filter_univ_mem, Finset.filter_notMem_eq_sdiff
      , ← Finset.inter_sdiff_assoc, Finset.inter_univ, Finset.sdiff_eq_self_of_disjoint hd.symm]
  have hterm : ∀ t : Finset (Fin n),
      (∏ i ∈ t, f i) * (∏ i ∈ (Finset.univ : Finset (Fin n)) \ t, g i)
        = if S₀ ⊆ t ∧ Disjoint t S₁ then w n q t else 0 := by
    intro t
    have h1 : ∏ i ∈ t, f i = if Disjoint t S₁ then q ^ t.card else 0 := by
      by_cases hd1 : Disjoint t S₁
      · rw [ite_eq_left hd1, ← Finset.prod_const]
        apply Finset.prod_congr rfl
        intro i hi
        simp [f, Finset.disjoint_left.mp hd1 hi]
      · rw [ite_eq_right hd1]
        rw [Finset.not_disjoint_iff] at hd1
        obtain ⟨i, hi, hi1⟩ := hd1
        exact Finset.prod_eq_zero hi (by simp [f, hi1])
    have h2 : ∏ i ∈ (Finset.univ : Finset (Fin n)) \ t, g i
        = if S₀ ⊆ t then (1 - q) ^ (n - t.card) else 0 := by
      by_cases hsub : S₀ ⊆ t
      · rw [ite_eq_left hsub]
        have hcard : ((Finset.univ : Finset (Fin n)) \ t).card = n - t.card := by
          rw [Finset.card_sdiff, Finset.card_univ, Fintype.card_fin, Finset.inter_univ]
        rw [← hcard, ← Finset.prod_const]
        apply Finset.prod_congr rfl
        intro i hi
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hi
        have hi0 : i ∉ S₀ := fun h0 => hi (hsub h0)
        simp only [g, ite_eq_right hi0]
      · rw [ite_eq_right hsub]
        rw [Finset.not_subset] at hsub
        obtain ⟨i, hi0, hit⟩ := hsub
        exact Finset.prod_eq_zero (Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hit⟩) (by simp [g, hi0])
    rw [h1, h2]
    by_cases hc : S₀ ⊆ t ∧ Disjoint t S₁
    · rw [ite_eq_left hc, ite_eq_left hc.2, ite_eq_left hc.1]
      rfl
    · rw [ite_eq_right hc]
      rcases not_and_or.mp hc with h | h
      · rw [ite_eq_right h, mul_zero]
      · rw [ite_eq_right h, zero_mul]
  rw [Finset.powerset_univ] at key
  rw [hLHS] at key
  rw [key]
  exact Finset.sum_congr rfl (fun t _ => (hterm t).symm)

/-- total weight = 1 -/
lemma total_weight (n : ℕ) (q : ℚ) : ∑ t : Finset (Fin n), w n q t = 1 := by
  have h := cond_weight n q ∅ ∅ (by simp)
  simpa using h

lemma w_pos (n : ℕ) (q : ℚ) (hq0 : 0 < q) (hq1 : q < 1) (t : Finset (Fin n)) :
    0 < w n q t := by
  apply mul_pos (pow_pos hq0 _)
  exact pow_pos (by linarith) _

/-! ### Board setup -/

/-- The set of absolute values appearing on the board. -/
def V (L : List (ℤ × ℤ)) : Finset ℕ :=
  (L.flatMap (fun p => [p.1.natAbs, p.2.natAbs])).toFinset

lemma natAbs_mem_V {L : List (ℤ × ℤ)} {p : ℤ × ℤ} (hp : p ∈ L) :
    p.1.natAbs ∈ V L ∧ p.2.natAbs ∈ V L := by
  constructor <;>
    · apply List.mem_toFinset.mpr
      apply List.mem_flatMap.mpr
      exact ⟨p, hp, by simp⟩

lemma V_ne_zero {L : List (ℤ × ℤ)} (hL : ValidBoard L) : ∀ v ∈ V L, v ≠ 0 := by
  intro v hv
  rw [V, List.mem_toFinset, List.mem_flatMap] at hv
  obtain ⟨p, hp, hvp⟩ := hv
  have hpz := hL.nonzero p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hvp
  rcases hvp with h | h
  · rw [h]; exact Int.natAbs_ne_zero.mpr hpz.1
  · rw [h]; exact Int.natAbs_ne_zero.mpr hpz.2

/-- number of distinct absolute values -/
noncomputable def nV (L : List (ℤ × ℤ)) : ℕ := (V L).card

/-- enumeration of the absolute values -/
noncomputable def kE (L : List (ℤ × ℤ)) : Fin (nV L) → ℕ :=
  fun i => ((V L).orderIsoOfFin rfl i).val

lemma kE_inj (L : List (ℤ × ℤ)) : Function.Injective (kE L) := by
  intro a b hab
  apply ((V L).orderIsoOfFin rfl).injective
  exact Subtype.ext hab

lemma kE_ne_zero {L : List (ℤ × ℤ)} (hL : ValidBoard L) (i : Fin (nV L)) : kE L i ≠ 0 := by
  have h : ((V L).orderIsoOfFin rfl i).val ∈ V L := ((V L).orderIsoOfFin rfl i).property
  exact V_ne_zero hL _ h

lemma kE_cov (L : List (ℤ × ℤ)) (v : ℕ) (hv : v ∈ V L) : ∃ i : Fin (nV L), kE L i = v := by
  refine ⟨((V L).orderIsoOfFin rfl).symm ⟨v, hv⟩, ?_⟩
  simp only [kE, OrderIso.apply_symm_apply]

/-- the "a" side representative: if the negative loop `(-k,-k)` appears, we take
`-k` as the representative (making all loops "positive"); otherwise `k`. -/
noncomputable def aE (L : List (ℤ × ℤ)) : Fin (nV L) → ℤ :=
  fun i => if (-(kE L i : ℤ), -(kE L i : ℤ)) ∈ L then -(kE L i : ℤ) else (kE L i : ℤ)

lemma aE_natAbs (L : List (ℤ × ℤ)) (i : Fin (nV L)) : (aE L i).natAbs = kE L i := by
  by_cases h : (-(kE L i : ℤ), -(kE L i : ℤ)) ∈ L <;>
    simp [aE, h, Int.natAbs_neg, Int.natAbs_natCast]

lemma aE_ne_zero {L : List (ℤ × ℤ)} (hL : ValidBoard L) (i : Fin (nV L)) : aE L i ≠ 0 := by
  have h1 := aE_natAbs L i
  have h2 := kE_ne_zero hL i
  intro hzero
  rw [hzero, Int.natAbs_zero] at h1
  exact h2 h1.symm

lemma loop_excl {L : List (ℤ × ℤ)} (hL : ValidBoard L) (i : Fin (nV L)) :
    (-aE L i, -aE L i) ∉ L := by
  by_cases h : (-(kE L i : ℤ), -(kE L i : ℤ)) ∈ L
  · have hai : aE L i = -(kE L i : ℤ) := by simp [aE, h]
    rw [hai]
    simp only [neg_neg]
    have := hL.no_both_loops (-(kE L i : ℤ)) h
    rwa [neg_neg] at this
  · have hai : aE L i = (kE L i : ℤ) := by simp [aE, h]
    rw [hai]
    exact h

/-- the erased set for strategy `t` -/
noncomputable def Tof (L : List (ℤ × ℤ)) (t : Finset (Fin (nV L))) : Finset ℤ :=
  t.biUnion (fun i => {aE L i}) ∪ ((Finset.univ \ t).biUnion (fun i => {-aE L i}))

lemma mem_Tof {L : List (ℤ × ℤ)} {t : Finset (Fin (nV L))} {x : ℤ} :
    x ∈ Tof L t ↔ (∃ i ∈ t, x = aE L i) ∨ (∃ i ∈ (Finset.univ \ t), x = -aE L i) := by
  simp only [Tof, Finset.mem_union, Finset.mem_biUnion, Finset.mem_singleton]

lemma validErase_Tof {L : List (ℤ × ℤ)} (hL : ValidBoard L) (t : Finset (Fin (nV L))) :
    ValidErase (Tof L t) := by
  intro x hx hnx
  rw [mem_Tof] at hx hnx
  have key : ∀ i j : Fin (nV L), x = aE L i ∨ x = -aE L i →
      (-x = aE L j ∨ -x = -aE L j) → i = j := by
    intro i j hi hj
    have h1 : (x).natAbs = kE L i := by
      rcases hi with h | h <;> rw [h] <;> simp [aE_natAbs, Int.natAbs_neg]
    have h2 : (x).natAbs = kE L j := by
      have hnxabs : (x).natAbs = (-x).natAbs := (Int.natAbs_neg x).symm
      rw [hnxabs]
      rcases hj with h | h <;> rw [h] <;> simp [aE_natAbs, Int.natAbs_neg]
    exact kE_inj L (h1.symm.trans h2)
  rcases hx with ⟨i, hit, hxi⟩ | ⟨i, hit, hxi⟩
  · rcases hnx with ⟨j, hjt, hxj⟩ | ⟨j, hjt, hxj⟩
    · have hij := key i j (Or.inl hxi) (Or.inl hxj)
      subst hij
      have hz : aE L i = 0 := by linarith [hxi, hxj]
      exact aE_ne_zero hL i hz
    · have hij := key i j (Or.inl hxi) (Or.inr hxj)
      subst hij
      rw [Finset.mem_sdiff] at hjt
      exact hjt.2 hit
  · rcases hnx with ⟨j, hjt, hxj⟩ | ⟨j, hjt, hxj⟩
    · have hij := key i j (Or.inr hxi) (Or.inl hxj)
      subst hij
      rw [Finset.mem_sdiff] at hit
      exact hit.2 hjt
    · have hij := key i j (Or.inr hxi) (Or.inr hxj)
      subst hij
      have hz : aE L i = 0 := by linarith [hxi, hxj]
      exact aE_ne_zero hL i hz

/-! ### List sum helpers -/

lemma list_filter_length {α : Type*} (l : List α) (p : α → Bool) :
    (l.filter p).length = (l.map (fun a => if p a then (1:ℕ) else 0)).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    by_cases h : p x
    · rw [List.filter_cons_of_pos h, List.map_cons, List.sum_cons, List.length_cons, ih]
      simp [h]
      lia
    · rw [List.filter_cons_of_neg h, List.map_cons, List.sum_cons, ih]
      simp [h]

lemma list_const_mul_sum {α : Type*} (c : ℚ) (l : List α) (f : α → ℚ) :
    c * (l.map f).sum = (l.map (fun a => c * f a)).sum := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [List.map_cons, List.sum_cons, mul_add, ih]

lemma sum_finset_list_map {α β : Type*} (s : Finset α) (l : List β) (F : α → β → ℚ) :
    ∑ a ∈ s, (l.map (F a)).sum = (l.map (fun b => ∑ a ∈ s, F a b)).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [Finset.sum_add_distrib, ih]

/-! ### Expectation identity -/

lemma score_cast (L : List (ℤ × ℤ)) (T : Finset ℤ) :
    (score L T : ℚ) = (L.map (fun p => (if p.1 ∈ T ∨ p.2 ∈ T then (1:ℚ) else 0))).sum := by
  have key : ∀ l : List (ℤ × ℤ),
      ((l.map (fun a => if decide (a.1 ∈ T ∨ a.2 ∈ T) then (1:ℕ) else 0)).sum : ℚ)
        = (l.map (fun a => if a.1 ∈ T ∨ a.2 ∈ T then (1:ℚ) else 0)).sum := by
    intro l
    induction l with
    | nil => simp
    | cons x xs ihr =>
      simp only [List.map_cons, List.sum_cons, Nat.cast_add, ihr]
      by_cases h : x.1 ∈ T ∨ x.2 ∈ T <;> simp [h]
  rw [score, list_filter_length]
  exact key L

lemma expected_score (L : List (ℤ × ℤ)) :
    ∑ t : Finset (Fin (nV L)), w (nV L) qProb t * (score L (Tof L t) : ℚ)
      = (L.map (fun p => ∑ t : Finset (Fin (nV L)),
          (if p.1 ∈ Tof L t ∨ p.2 ∈ Tof L t then w (nV L) qProb t else 0))).sum := by
  calc ∑ t : Finset (Fin (nV L)), w (nV L) qProb t * (score L (Tof L t) : ℚ)
      = ∑ t : Finset (Fin (nV L)), w (nV L) qProb t *
          (L.map (fun p => (if p.1 ∈ Tof L t ∨ p.2 ∈ Tof L t then (1:ℚ) else 0))).sum :=
        Finset.sum_congr rfl (fun t _ => by rw [score_cast])
    _ = ∑ t : Finset (Fin (nV L)),
          (L.map (fun p => w (nV L) qProb t *
            (if p.1 ∈ Tof L t ∨ p.2 ∈ Tof L t then (1:ℚ) else 0))).sum :=
        Finset.sum_congr rfl (fun t _ => list_const_mul_sum _ _ _)
    _ = (L.map (fun p => ∑ t : Finset (Fin (nV L)), w (nV L) qProb t *
          (if p.1 ∈ Tof L t ∨ p.2 ∈ Tof L t then (1:ℚ) else 0))).sum :=
        sum_finset_list_map Finset.univ L _
    _ = (L.map (fun p => ∑ t : Finset (Fin (nV L)),
          (if p.1 ∈ Tof L t ∨ p.2 ∈ Tof L t then w (nV L) qProb t else 0))).sum := by
        congr 1
        apply List.map_congr_left
        intro p _
        apply Finset.sum_congr rfl
        intro t _
        by_cases h : p.1 ∈ Tof L t ∨ p.2 ∈ Tof L t <;> simp [h]

/-! ### Edge case analysis -/

lemma W_ge {L : List (ℤ × ℤ)} (hL : ValidBoard L) {p : ℤ × ℤ} (hp : p ∈ L) :
    qProb ≤ ∑ t : Finset (Fin (nV L)),
      (if p.1 ∈ Tof L t ∨ p.2 ∈ Tof L t then w (nV L) qProb t else 0) := by
  have hpz := hL.nonzero p hp
  obtain ⟨hpV1, hpV2⟩ := natAbs_mem_V hp
  obtain ⟨i, hi⟩ := kE_cov L p.1.natAbs hpV1
  obtain ⟨j, hj⟩ := kE_cov L p.2.natAbs hpV2
  have hp1 : p.1 = aE L i ∨ p.1 = -aE L i := by
    have habs : (p.1).natAbs = (aE L i).natAbs := by
      rw [aE_natAbs]; exact hi.symm
    rw [Int.natAbs_eq_natAbs_iff] at habs
    rcases habs with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hp2 : p.2 = aE L j ∨ p.2 = -aE L j := by
    have habs : (p.2).natAbs = (aE L j).natAbs := by
      rw [aE_natAbs]; exact hj.symm
    rw [Int.natAbs_eq_natAbs_iff] at habs
    rcases habs with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hmem1 : ∀ t : Finset (Fin (nV L)),
      p.1 ∈ Tof L t ↔ (p.1 = aE L i ∧ i ∈ t) ∨ (p.1 = -aE L i ∧ i ∉ t) := by
    intro t
    rw [mem_Tof]
    constructor
    · rintro (⟨i', hi't, hxi'⟩ | ⟨i', hi't, hxi'⟩)
      · have habs : kE L i' = kE L i := by
          have h2 : (p.1).natAbs = kE L i' := by rw [hxi']; exact aE_natAbs L i'
          exact h2.symm.trans hi.symm
        have hii : i' = i := kE_inj L habs
        subst hii
        exact Or.inl ⟨hxi', hi't⟩
      · have habs : kE L i' = kE L i := by
          have h2 : (p.1).natAbs = kE L i' := by
            rw [hxi', Int.natAbs_neg]; exact aE_natAbs L i'
          exact h2.symm.trans hi.symm
        have hii : i' = i := kE_inj L habs
        subst hii
        rw [Finset.mem_sdiff] at hi't
        exact Or.inr ⟨hxi', hi't.2⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact Or.inl ⟨i, h2, h1⟩
      · exact Or.inr ⟨i, Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, h2⟩, h1⟩
  have hmem2 : ∀ t : Finset (Fin (nV L)),
      p.2 ∈ Tof L t ↔ (p.2 = aE L j ∧ j ∈ t) ∨ (p.2 = -aE L j ∧ j ∉ t) := by
    intro t
    rw [mem_Tof]
    constructor
    · rintro (⟨j', hj't, hyj'⟩ | ⟨j', hj't, hyj'⟩)
      · have habs : kE L j' = kE L j := by
          have h2 : (p.2).natAbs = kE L j' := by rw [hyj']; exact aE_natAbs L j'
          exact h2.symm.trans hj.symm
        have hjj : j' = j := kE_inj L habs
        subst hjj
        exact Or.inl ⟨hyj', hj't⟩
      · have habs : kE L j' = kE L j := by
          have h2 : (p.2).natAbs = kE L j' := by
            rw [hyj', Int.natAbs_neg]; exact aE_natAbs L j'
          exact h2.symm.trans hj.symm
        have hjj : j' = j := kE_inj L habs
        subst hjj
        rw [Finset.mem_sdiff] at hj't
        exact Or.inr ⟨hyj', hj't.2⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact Or.inl ⟨j, h2, h1⟩
      · exact Or.inr ⟨j, Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, h2⟩, h1⟩
  have aE_ne_ne : ∀ i : Fin (nV L), aE L i ≠ -aE L i := by
    intro i' h
    have hz : aE L i' = 0 := by linarith [h]
    exact aE_ne_zero hL i' hz
  have hnot : ∀ t : Finset (Fin (nV L)), ¬(p.1 ∈ Tof L t ∨ p.2 ∈ Tof L t) ↔
      ¬((p.1 = aE L i ∧ i ∈ t) ∨ (p.1 = -aE L i ∧ i ∉ t)) ∧
      ¬((p.2 = aE L j ∧ j ∈ t) ∨ (p.2 = -aE L j ∧ j ∉ t)) := by
    intro t
    rw [not_or]
    exact and_congr (not_congr (hmem1 t)) (not_congr (hmem2 t))
  have hsplit : ∑ t : Finset (Fin (nV L)),
        (if p.1 ∈ Tof L t ∨ p.2 ∈ Tof L t then w (nV L) qProb t else (0:ℚ))
      = 1 - ∑ t : Finset (Fin (nV L)),
        (if ¬(p.1 ∈ Tof L t ∨ p.2 ∈ Tof L t) then w (nV L) qProb t else (0:ℚ)) := by
    have h := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Finset (Fin (nV L))))
      (fun t => p.1 ∈ Tof L t ∨ p.2 ∈ Tof L t) (w (nV L) qProb)
    rw [Finset.sum_filter, Finset.sum_filter, total_weight] at h
    linarith
  rw [hsplit]
  -- case analysis
  by_cases hij : i = j
  · subst hij
    rcases hp1 with h1 | h1 <;> rcases hp2 with h2 | h2
    · -- loop (a i, a i): bad weight = 1 - q
      have hsum : ∑ t : Finset (Fin (nV L)),
          (if ¬(p.1 ∈ Tof L t ∨ p.2 ∈ Tof L t) then w (nV L) qProb t else (0:ℚ))
          = 1 - qProb := by
        have hcond : ∀ t : Finset (Fin (nV L)),
            (if ¬(p.1 ∈ Tof L t ∨ p.2 ∈ Tof L t) then w (nV L) qProb t else (0:ℚ))
            = (if (∅ : Finset (Fin (nV L))) ⊆ t ∧ Disjoint t {i} then w (nV L) qProb t else 0) := by
          intro t
          apply if_congr _ rfl rfl
          rw [hnot t]
          simp [h1, h2, aE_ne_ne i, Finset.disjoint_singleton_right]
        rw [Finset.sum_congr rfl (fun t _ => hcond t)]
        rw [cond_weight (nV L) qProb ∅ {i} (by simp)]
        simp
      rw [hsum]
      linarith
    · -- (a i, -a i): bad weight = 0
      have hsum : ∑ t : Finset (Fin (nV L)),
          (if ¬(p.1 ∈ Tof L t ∨ p.2 ∈ Tof L t) then w (nV L) qProb t else (0:ℚ)) = 0 := by
        apply Finset.sum_eq_zero
        intro t _
        apply ite_eq_right
        rw [hnot t]
        simp [h1, h2, aE_ne_ne i, (aE_ne_ne i).symm]
      rw [hsum]
      norm_num [qProb]
    · -- (-a i, a i): bad weight = 0
      have hsum : ∑ t : Finset (Fin (nV L)),
          (if ¬(p.1 ∈ Tof L t ∨ p.2 ∈ Tof L t) then w (nV L) qProb t else (0:ℚ)) = 0 := by
        apply Finset.sum_eq_zero
        intro t _
        apply ite_eq_right
        rw [hnot t]
        simp [h1, h2, aE_ne_ne i, (aE_ne_ne i).symm]
      rw [hsum]
      norm_num [qProb]
    · -- (-a i, -a i): excluded by the board condition
      exfalso
      have hpp : p = (-aE L i, -aE L i) := Prod.ext_iff.mpr ⟨h1, h2⟩
      rw [hpp] at hp
      exact loop_excl hL i hp
  · rcases hp1 with h1 | h1 <;> rcases hp2 with h2 | h2
    · -- (a i, a j), i ≠ j: bad weight = (1-q)²
      have hsum : ∑ t : Finset (Fin (nV L)),
          (if ¬(p.1 ∈ Tof L t ∨ p.2 ∈ Tof L t) then w (nV L) qProb t else (0:ℚ))
          = (1 - qProb)^2 := by
        have hcond : ∀ t : Finset (Fin (nV L)),
            (if ¬(p.1 ∈ Tof L t ∨ p.2 ∈ Tof L t) then w (nV L) qProb t else (0:ℚ))
            = (if (∅ : Finset (Fin (nV L))) ⊆ t ∧ Disjoint t {i, j} then w (nV L) qProb t else 0) := by
          intro t
          apply if_congr _ rfl rfl
          rw [hnot t]
          simp [h1, h2, aE_ne_ne i, aE_ne_ne j, Finset.disjoint_insert_right,
            Finset.disjoint_singleton_right]
        rw [Finset.sum_congr rfl (fun t _ => hcond t)]
        rw [cond_weight (nV L) qProb ∅ {i, j} (by simp)]
        simp [Finset.card_pair hij]
      rw [hsum]
      norm_num [qProb]
    · -- (a i, -a j): bad weight = q(1-q)
      have hsum : ∑ t : Finset (Fin (nV L)),
          (if ¬(p.1 ∈ Tof L t ∨ p.2 ∈ Tof L t) then w (nV L) qProb t else (0:ℚ))
          = qProb * (1 - qProb) := by
        have hcond : ∀ t : Finset (Fin (nV L)),
            (if ¬(p.1 ∈ Tof L t ∨ p.2 ∈ Tof L t) then w (nV L) qProb t else (0:ℚ))
            = (if ({j} : Finset (Fin (nV L))) ⊆ t ∧ Disjoint t {i} then w (nV L) qProb t else 0) := by
          intro t
          apply if_congr _ rfl rfl
          rw [hnot t]
          simp [h1, h2, aE_ne_ne i, (aE_ne_ne j).symm, Finset.singleton_subset_iff,
            Finset.disjoint_singleton_right, and_comm]
        rw [Finset.sum_congr rfl (fun t _ => hcond t)]
        rw [cond_weight (nV L) qProb {j} {i} (Finset.disjoint_singleton.mpr (Ne.symm hij))]
        simp
      rw [hsum]
      norm_num [qProb]
    · -- (-a i, a j): bad weight = q(1-q)
      have hsum : ∑ t : Finset (Fin (nV L)),
          (if ¬(p.1 ∈ Tof L t ∨ p.2 ∈ Tof L t) then w (nV L) qProb t else (0:ℚ))
          = qProb * (1 - qProb) := by
        have hcond : ∀ t : Finset (Fin (nV L)),
            (if ¬(p.1 ∈ Tof L t ∨ p.2 ∈ Tof L t) then w (nV L) qProb t else (0:ℚ))
            = (if ({i} : Finset (Fin (nV L))) ⊆ t ∧ Disjoint t {j} then w (nV L) qProb t else 0) := by
          intro t
          apply if_congr _ rfl rfl
          rw [hnot t]
          simp [h1, h2, (aE_ne_ne i).symm, aE_ne_ne j, Finset.singleton_subset_iff,
            Finset.disjoint_singleton_right]
        rw [Finset.sum_congr rfl (fun t _ => hcond t)]
        rw [cond_weight (nV L) qProb {i} {j} (Finset.disjoint_singleton.mpr hij)]
        simp
      rw [hsum]
      norm_num [qProb]
    · -- (-a i, -a j): bad weight = q²
      have hsum : ∑ t : Finset (Fin (nV L)),
          (if ¬(p.1 ∈ Tof L t ∨ p.2 ∈ Tof L t) then w (nV L) qProb t else (0:ℚ))
          = qProb^2 := by
        have hcond : ∀ t : Finset (Fin (nV L)),
            (if ¬(p.1 ∈ Tof L t ∨ p.2 ∈ Tof L t) then w (nV L) qProb t else (0:ℚ))
            = (if ({i, j} : Finset (Fin (nV L))) ⊆ t ∧ Disjoint t (∅ : Finset (Fin (nV L)))
              then w (nV L) qProb t else 0) := by
          intro t
          apply if_congr _ rfl rfl
          rw [hnot t]
          simp [h1, h2, (aE_ne_ne i).symm, (aE_ne_ne j).symm, Finset.insert_subset_iff,
            Finset.singleton_subset_iff]
        rw [Finset.sum_congr rfl (fun t _ => hcond t)]
        rw [cond_weight (nV L) qProb {i, j} ∅ (Finset.disjoint_empty_right _)]
        simp [Finset.card_pair hij]
      rw [hsum]
      norm_num [qProb]

/-! ### Assembling the lower bound -/

lemma lower_bound (L : List (ℤ × ℤ)) (hL : ValidBoard L) :
    ∃ T : Finset ℤ, ValidErase T ∧ 43 ≤ score L T := by
  have hsum : (L.map (fun _ => qProb)).sum ≤ (L.map (fun p => ∑ t : Finset (Fin (nV L)),
      (if p.1 ∈ Tof L t ∨ p.2 ∈ Tof L t then w (nV L) qProb t else 0))).sum :=
    List.sum_le_sum (fun p hp => W_ge hL hp)
  have hL68 : (L.map (fun _ => qProb)).sum = 68 * qProb := by
    rw [List.map_const', List.sum_replicate, hL.length_eq, nsmul_eq_mul]
    norm_num
  rw [← expected_score L] at hsum
  rw [hL68] at hsum
  have h42 : (42 : ℚ) < 68 * qProb := by norm_num [qProb]
  have hlt : ∑ t : Finset (Fin (nV L)), w (nV L) qProb t * (42:ℚ)
      < ∑ t : Finset (Fin (nV L)), w (nV L) qProb t * (score L (Tof L t) : ℚ) := by
    rw [← Finset.sum_mul, total_weight, one_mul]
    linarith [hsum, h42]
  obtain ⟨t, -, ht⟩ := Finset.exists_lt_of_sum_lt hlt
  have hwq : 0 < w (nV L) qProb t :=
    w_pos (nV L) qProb (by norm_num [qProb]) (by norm_num [qProb]) t
  have hsc : (42 : ℚ) < (score L (Tof L t) : ℚ) := (Rat.mul_lt_mul_left hwq).mp ht
  have hsc43 : 43 ≤ score L (Tof L t) := by
    have h' : 42 < score L (Tof L t) := by exact_mod_cast hsc
    lia
  exact ⟨Tof L t, validErase_Tof hL t, hsc43⟩

/-! ### The extremal construction (upper bound) -/

/-- The extremal board: five loops `(i,i)` for each `i ∈ {1,…,8}` and one negative
edge `(-i,-j)` for each `1 ≤ j < i ≤ 8` (a `K₈` on the negative side). -/
def L0 : List (ℤ × ℤ) :=
  (List.range 8).flatMap (fun i => List.replicate 5 ((i+1 : ℤ), (i+1 : ℤ))) ++
  (List.range 8).flatMap (fun i => (List.range i).map (fun j => (-(i+1 : ℤ), -(j+1 : ℤ))))

/-- The loop part of `L0`: five loops (i,i) for each i ∈ {1,…,8}. -/
def upperLoopList : List (ℤ × ℤ) :=
  (List.range 8).flatMap (fun (i : ℕ) => List.replicate 5 ((i : ℤ) + 1, (i : ℤ) + 1))

/-- The negative part of `L0`: one edge (-i,-j) for each 1 ≤ j < i ≤ 8. -/
def upperNegList : List (ℤ × ℤ) :=
  (List.range 8).flatMap (fun (i : ℕ) =>
    (List.range i).map (fun (j : ℕ) => (-((i : ℤ) + 1), -((j : ℤ) + 1))))

lemma upperLoopList_def :
    upperLoopList
      = (List.range 8).flatMap (fun (i : ℕ) => List.replicate 5 ((i : ℤ) + 1, (i : ℤ) + 1)) :=
  rfl

lemma upperNegList_def :
    upperNegList = (List.range 8).flatMap (fun (i : ℕ) =>
      (List.range i).map (fun (j : ℕ) => (-((i : ℤ) + 1), -((j : ℤ) + 1)))) :=
  rfl

lemma upper_L0_eq : L0 = upperLoopList ++ upperNegList := rfl

/-- Bridge between `List.sum` over `List.range` and `Finset.sum` over `Finset.range`. -/
lemma upper_sum_map_range (g : ℕ → ℕ) (n : ℕ) :
    ((List.range n).map g).sum = ∑ i ∈ Finset.range n, g i := by
  induction n with
  | zero => simp
  | succ k ih =>
      simp [List.range_succ, List.map_append, List.sum_append, Finset.sum_range_succ, ih]

/-- For a list without duplicates, the length of a filtered list equals the
cardinality of the corresponding filtered finset. -/
lemma upper_filter_length_eq_card (l : List ℕ) (hl : l.Nodup) (p : ℕ → Bool) :
    (l.filter p).length = (l.toFinset.filter (fun a => p a = true)).card := by
  rw [← List.toFinset_filter, List.toFinset_card_of_nodup (hl.filter p)]

/-- Elements of the loop part of `L0` are diagonal pairs (i+1, i+1) with i < 8. -/
lemma upper_mem_loopList {p : ℤ × ℤ} (h : p ∈ upperLoopList) :
    ∃ i : ℕ, i < 8 ∧ p = ((i : ℤ) + 1, (i : ℤ) + 1) := by
  simp only [upperLoopList_def, List.mem_flatMap, List.mem_range, List.mem_replicate] at h
  obtain ⟨i, hi, -, hp⟩ := h
  exact ⟨i, hi, hp⟩

/-- No diagonal pair (k,k) occurs in the negative part of `L0`:
its entries (-(i+1), -(j+1)) always have j < i, hence distinct components. -/
lemma upper_not_mem_negList_diag (k : ℤ) : (k, k) ∉ upperNegList := by
  intro h
  simp only [upperNegList_def, List.mem_flatMap, List.mem_range, List.mem_map] at h
  obtain ⟨i, -, j, hji, heq⟩ := h
  simp only [Prod.mk.injEq] at heq
  have : i = j := by lia
  lia

/-- The combinatorial heart of the upper bound: for any `A : Finset ℕ`,
`a choose 2 ≤ ∑ i ∈ A, #(A ∩ range i)`, proved by enumerating `A` in
increasing order via `Finset.orderEmbOfFin`. -/
lemma upper_card_choose_le (A : Finset ℕ) :
    A.card * (A.card - 1) / 2 ≤ ∑ i ∈ A, (A ∩ Finset.range i).card := by
  have hre : ∑ i ∈ A, (A ∩ Finset.range i).card
      = ∑ t : Fin A.card, (A ∩ Finset.range (A.orderEmbOfFin rfl t)).card := by
    have h2 := Finset.sum_image (s := (Finset.univ : Finset (Fin A.card)))
      (f := fun i => (A ∩ Finset.range i).card) (g := A.orderEmbOfFin rfl)
      (Set.InjOn.mono (Set.subset_univ _) (RelEmbedding.injective _).injOn)
    rw [Finset.image_orderEmbOfFin_univ] at h2
    exact h2
  have hkey : ∀ t : Fin A.card, t.val ≤ (A ∩ Finset.range (A.orderEmbOfFin rfl t)).card := by
    intro t
    have hinj : Function.Injective
        (fun s : Fin t.val => A.orderEmbOfFin rfl ⟨s.val, s.isLt.trans t.isLt⟩) := by
      intro a b hab
      have h2 : (⟨a.val, a.isLt.trans t.isLt⟩ : Fin A.card) = ⟨b.val, b.isLt.trans t.isLt⟩ :=
        RelEmbedding.injective (A.orderEmbOfFin rfl) hab
      exact Fin.ext_iff.mpr (congrArg (fun x : Fin A.card => x.val) h2)
    have hsub : Finset.image
        (fun s : Fin t.val => A.orderEmbOfFin rfl ⟨s.val, s.isLt.trans t.isLt⟩) Finset.univ
        ⊆ A ∩ Finset.range (A.orderEmbOfFin rfl t) := by
      intro x hx
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
      obtain ⟨s, rfl⟩ := hx
      simp only [Finset.mem_inter, Finset.mem_range]
      exact ⟨Finset.orderEmbOfFin_mem A rfl _,
        (A.orderEmbOfFin rfl).strictMono
          (show (⟨s.val, s.isLt.trans t.isLt⟩ : Fin A.card) < t from s.isLt)⟩
    have hcard : (Finset.image
        (fun s : Fin t.val => A.orderEmbOfFin rfl ⟨s.val, s.isLt.trans t.isLt⟩) Finset.univ).card
        = t.val := by
      rw [Finset.card_image_of_injective Finset.univ hinj, Finset.card_univ, Fintype.card_fin]
    rw [← hcard]
    exact Finset.card_le_card hsub
  calc A.card * (A.card - 1) / 2
      = ∑ i ∈ Finset.range A.card, i := (Finset.sum_range_id A.card).symm
    _ = ∑ t : Fin A.card, t.val := (Fin.sum_univ_eq_sum_range (fun i => i) A.card).symm
    _ ≤ ∑ t : Fin A.card, (A ∩ Finset.range (A.orderEmbOfFin rfl t)).card :=
        Finset.sum_le_sum fun t _ => hkey t
    _ = ∑ i ∈ A, (A ∩ Finset.range i).card := hre.symm

lemma validBoard_L0 : ValidBoard L0 := by
  refine ⟨?_, ?_, ?_⟩
  · decide
  · decide
  · intro k hk hneg
    rw [upper_L0_eq] at hk hneg
    have hkpos : 0 < k := by
      rcases List.mem_append.mp hk with h | h
      · obtain ⟨i, -, heq⟩ := upper_mem_loopList h
        simp only [Prod.mk.injEq] at heq
        lia
      · exact absurd h (upper_not_mem_negList_diag k)
    rcases List.mem_append.mp hneg with h | h
    · obtain ⟨i, -, heq⟩ := upper_mem_loopList h
      simp only [Prod.mk.injEq] at heq
      lia
    · exact upper_not_mem_negList_diag (-k) h

/-- The loop part contributes exactly `5 * a`, where `a` counts the indices
i ∈ {1,…,8} with i ∈ T. -/
lemma upper_loopScore (T : Finset ℤ) :
    (upperLoopList.filter (fun p => decide (p.1 ∈ T ∨ p.2 ∈ T))).length
      = 5 * ((Finset.range 8).filter (fun (i : ℕ) => (i : ℤ) + 1 ∈ T)).card := by
  have hRHS : 5 * ((Finset.range 8).filter (fun (i : ℕ) => (i : ℤ) + 1 ∈ T)).card
      = ∑ i ∈ Finset.range 8, if (i : ℤ) + 1 ∈ T then 5 else 0 := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    simp [Nat.mul_comm]
  rw [upperLoopList_def, List.filter_flatMap, List.length_flatMap, upper_sum_map_range, hRHS]
  apply Finset.sum_congr rfl
  intro i _
  show (List.filter (fun p => decide (p.1 ∈ T ∨ p.2 ∈ T))
      (List.replicate 5 ((i : ℤ) + 1, (i : ℤ) + 1))).length
    = if (i : ℤ) + 1 ∈ T then 5 else 0
  rw [List.filter_replicate]
  by_cases h : (i : ℤ) + 1 ∈ T <;> simp [h]

/-- The number of unscored negative edges is at least `a choose 2`:
for each i ∈ A, all edges (-(i+1), -(j+1)) with j ∈ A, j < i are unscored. -/
lemma upper_negUnscored (T : Finset ℤ) (hT : ValidErase T) :
    ((Finset.range 8).filter (fun (i : ℕ) => (i : ℤ) + 1 ∈ T)).card
        * (((Finset.range 8).filter (fun (i : ℕ) => (i : ℤ) + 1 ∈ T)).card - 1) / 2
      ≤ (upperNegList.filter (fun p => decide (p.1 ∉ T ∧ p.2 ∉ T))).length := by
  set A := (Finset.range 8).filter (fun (i : ℕ) => (i : ℤ) + 1 ∈ T) with hA
  have hsub : A ⊆ Finset.range 8 := by rw [hA]; exact Finset.filter_subset _ _
  refine le_trans (upper_card_choose_le A) ?_
  have hAsum : ∑ i ∈ A, (A ∩ Finset.range i).card
      = ∑ i ∈ Finset.range 8, if i ∈ A then (A ∩ Finset.range i).card else 0 := by
    rw [← Finset.sum_filter]
    congr 1
    rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hsub]
  rw [hAsum, upperNegList_def, List.filter_flatMap, List.length_flatMap, upper_sum_map_range]
  apply Finset.sum_le_sum
  intro i _
  by_cases hiA : i ∈ A
  · rw [ite_eq_left hiA]
    have hiT : (i : ℤ) + 1 ∈ T := by
      have h2 := hiA
      rw [hA] at h2
      exact (Finset.mem_filter.mp h2).2
    have hnegT : -((i : ℤ) + 1) ∉ T := hT _ hiT
    show (A ∩ Finset.range i).card ≤ (List.filter (fun p => decide (p.1 ∉ T ∧ p.2 ∉ T))
      ((List.range i).map fun (j : ℕ) => (-((i : ℤ) + 1), -((j : ℤ) + 1)))).length
    rw [List.filter_map, List.length_map]
    have hpred : (fun p => decide (p.1 ∉ T ∧ p.2 ∉ T))
          ∘ (fun (j : ℕ) => (-((i : ℤ) + 1), -((j : ℤ) + 1)))
        = fun (j : ℕ) => decide (-((j : ℤ) + 1) ∉ T) := by
      funext j
      show decide (-((i : ℤ) + 1) ∉ T ∧ -((j : ℤ) + 1) ∉ T) = decide (-((j : ℤ) + 1) ∉ T)
      rw [decide_eq_decide]
      exact ⟨fun h => h.2, fun h => ⟨hnegT, h⟩⟩
    rw [hpred, upper_filter_length_eq_card _ List.nodup_range, List.toFinset_range]
    apply Finset.card_le_card
    intro j hj
    simp only [Finset.mem_inter, Finset.mem_range] at hj
    simp only [Finset.mem_filter, Finset.mem_range, decide_eq_true_eq]
    refine ⟨hj.2, ?_⟩
    have hjT : (j : ℤ) + 1 ∈ T := by
      have h2 := hj.1
      rw [hA] at h2
      exact (Finset.mem_filter.mp h2).2
    exact hT _ hjT
  · rw [ite_eq_right hiA]
    exact Nat.zero_le _

/-- Case check: for a ≤ 8, `5a + 28 - a(a-1)/2 ≤ 43`. -/
lemma upper_arith (a : ℕ) (ha : a ≤ 8) : 5 * a + (28 - a * (a - 1) / 2) ≤ 43 := by
  interval_cases a <;> decide

lemma upper_score (T : Finset ℤ) (hT : ValidErase T) : score L0 T ≤ 43 := by
  have hlen : upperNegList.length = 28 := by decide
  have hloop : (upperLoopList.filter (fun p => decide (p.1 ∈ T ∨ p.2 ∈ T))).length
      = 5 * ((Finset.range 8).filter (fun (i : ℕ) => (i : ℤ) + 1 ∈ T)).card :=
    upper_loopScore T
  have hLB := upper_negUnscored T hT
  have hcard8 : ((Finset.range 8).filter (fun (i : ℕ) => (i : ℤ) + 1 ∈ T)).card ≤ 8 :=
    calc ((Finset.range 8).filter (fun (i : ℕ) => (i : ℤ) + 1 ∈ T)).card
        ≤ (Finset.range 8).card := Finset.card_le_card (Finset.filter_subset _ _)
      _ = 8 := Finset.card_range 8
  have hfinal := upper_arith _ hcard8
  have hsplit : (upperNegList.filter (fun p => decide (p.1 ∈ T ∨ p.2 ∈ T))).length
      + (upperNegList.filter (fun p => decide (p.1 ∉ T ∧ p.2 ∉ T))).length = 28 := by
    have h0 := List.length_eq_length_filter_add (l := upperNegList)
      (f := fun p => decide (p.1 ∈ T ∨ p.2 ∈ T))
    rw [hlen] at h0
    rw [h0]
    congr 1
    congr 1
    apply List.filter_congr
    intro x _
    simp only [← decide_not, not_or]
  rw [upper_L0_eq]
  show ((upperLoopList ++ upperNegList).filter (fun p => decide (p.1 ∈ T ∨ p.2 ∈ T))).length ≤ 43
  rw [List.filter_append, List.length_append]
  lia


snip end

problem usa2010_p6 :
    IsGreatest {m : ℕ | ∀ L : List (ℤ × ℤ), ValidBoard L →
      ∃ T : Finset ℤ, ValidErase T ∧ m ≤ score L T} N := by
  constructor
  · intro L hL
    obtain ⟨T, hT, hscore⟩ := lower_bound L hL
    exact ⟨T, hT, hscore⟩
  · intro m hm
    obtain ⟨T, hT, hscore⟩ := hm L0 validBoard_L0
    exact le_trans hscore (upper_score T hT)

end Usa2010P6
