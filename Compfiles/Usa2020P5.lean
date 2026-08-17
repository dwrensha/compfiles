/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Polynomial.Roots
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics] }

/-!
# USA Mathematical Olympiad 2020, Problem 5

A finite set S of points in the coordinate plane is called overdetermined if |S| ≥ 2
and there exists a nonzero polynomial P(t), with real coefficients and of degree at
most |S| − 2, satisfying P(x) = y for every point (x, y) ∈ S.

For each integer n ≥ 2, find the largest integer k (in terms of n) such that there
exists a set of n distinct points that is not overdetermined, but has k
overdetermined subsets.
-/

open Classical Polynomial

namespace Usa2020P5

/-- A finite set of points in the coordinate plane is *overdetermined* if it has at
least two elements and some nonzero real polynomial of degree at most `|S| - 2`
passes through every point of `S`. -/
def Overdetermined (S : Finset (ℝ × ℝ)) : Prop :=
  2 ≤ S.card ∧ ∃ P : ℝ[X], P ≠ 0 ∧ P.natDegree ≤ S.card - 2 ∧ ∀ p ∈ S, P.eval p.1 = p.2

determine solution (n : ℕ) : ℕ := 2 ^ (n - 1) - n

snip begin

/- The proof follows the official solution (also presented in Evan Chen's
*USAMO 2020 Solution Notes*). Call a set of points *flooded* if it is not
overdetermined. If a flooded set has `m ≥ 3` elements, then at most one of its
`(m-1)`-subsets is overdetermined: two different overdetermined deletion sets would
give interpolating polynomials of degree at most `m - 3` agreeing on `m - 2` points,
hence equal, which would witness that the whole set is overdetermined. A
double-counting argument on the incidence relation between flooded `m`-sets and
flooded `(m+1)`-sets then shows that an `n`-element flooded set has at least
`(n-1).choose (m-1)` flooded `m`-subsets for every `2 ≤ m ≤ n`, so at most
`2^(n-1) - n` of its subsets are overdetermined. This bound is attained by the set
`{(1, 1), (2, 2), (3, 2), ..., (n, 2)}`. -/

/-- `k + 1 ≤ 2 ^ k` for every natural number `k`. -/
lemma two_pow_ge_succ (k : ℕ) : k + 1 ≤ 2 ^ k := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [pow_succ]
    lia

/-- A nonzero polynomial that vanishes on every element of a finite set of reals has
degree at least the cardinality of that set. -/
lemma roots_card_bound {P : ℝ[X]} (hP : P ≠ 0) {X : Finset ℝ}
    (hX : ∀ x ∈ X, P.eval x = 0) : X.card ≤ P.natDegree := by
  have hsub : X ⊆ P.roots.toFinset := by
    intro x hx
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hP, Polynomial.IsRoot.def]
    exact hX x hx
  exact (Finset.card_le_card hsub).trans
    ((Multiset.toFinset_card_le _).trans (Polynomial.card_roots' P))

/-- Uniqueness of low-degree interpolating polynomials: two real polynomials of degree
at most `|T| - 1` that both pass through every point of a nonempty finite set `T` of
points in the plane are equal. -/
lemma poly_unique {T : Finset (ℝ × ℝ)} (hT : T.Nonempty) {f g : ℝ[X]}
    (hf : f.natDegree ≤ T.card - 1) (hg : g.natDegree ≤ T.card - 1)
    (hfT : ∀ p ∈ T, f.eval p.1 = p.2) (hgT : ∀ p ∈ T, g.eval p.1 = p.2) :
    f = g := by
  by_contra hne
  have hfg : f - g ≠ 0 := sub_ne_zero.mpr hne
  have hX : ∀ x ∈ T.image Prod.fst, (f - g).eval x = 0 := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨p, hpT, rfl⟩
    rw [Polynomial.eval_sub, hfT p hpT, hgT p hpT, sub_self]
  have hle := roots_card_bound hfg hX
  have hdeg : (f - g).natDegree ≤ T.card - 1 :=
    (Polynomial.natDegree_sub_le f g).trans (max_le hf hg)
  have hpos : 0 < T.card := Finset.card_pos.mpr hT
  have hlt : (T.image Prod.fst).card < T.card := by lia
  rcases Finset.exists_ne_map_eq_of_card_image_lt hlt with ⟨p, hpT, q, hqT, hpq, h1⟩
  apply hpq
  have h2 : p.2 = q.2 := by rw [← hfT p hpT, ← hfT q hqT, h1]
  exact Prod.ext h1 h2

/-- A flooded (i.e. not overdetermined) set of `m + 2` points has at most one
overdetermined subset of size `m + 1`. -/
lemma eq_of_overdetermined_of_flooded {S : Finset (ℝ × ℝ)} (hS : ¬ Overdetermined S)
    {m : ℕ} (hcard : S.card = m + 2) {U₁ U₂ : Finset (ℝ × ℝ)}
    (hU₁ : U₁ ⊆ S) (hU₁c : U₁.card = m + 1) (hU₁o : Overdetermined U₁)
    (hU₂ : U₂ ⊆ S) (hU₂c : U₂.card = m + 1) (hU₂o : Overdetermined U₂) :
    U₁ = U₂ := by
  obtain ⟨hU₁o2, f, hf0, hfd, hfU⟩ := hU₁o
  obtain ⟨hU₂o2, g, hg0, hgd, hgU⟩ := hU₂o
  -- each `Uᵢ` is `S` with a single point `pᵢ` removed
  have hsd1 : (S \ U₁).card = 1 := by
    have h := Finset.card_sdiff_of_subset hU₁
    lia
  obtain ⟨p₁, hp₁⟩ := Finset.card_eq_one.mp hsd1
  have hsd2 : (S \ U₂).card = 1 := by
    have h := Finset.card_sdiff_of_subset hU₂
    lia
  obtain ⟨p₂, hp₂⟩ := Finset.card_eq_one.mp hsd2
  have hmem1 : p₁ ∈ S := by
    have h : p₁ ∈ S \ U₁ := by rw [hp₁]; exact Finset.mem_singleton_self p₁
    exact (Finset.mem_sdiff.mp h).1
  have hmem2 : p₂ ∈ S := by
    have h : p₂ ∈ S \ U₂ := by rw [hp₂]; exact Finset.mem_singleton_self p₂
    exact (Finset.mem_sdiff.mp h).1
  have hU₁eq : U₁ = S \ {p₁} := by
    exact (sdiff_eq_symm hU₁ hp₁).symm
  have hU₂eq : U₂ = S \ {p₂} := by
    exact (sdiff_eq_symm hU₂ hp₂).symm
  by_cases hpp : p₁ = p₂
  · rw [hU₁eq, hU₂eq, hpp]
  · exfalso
    -- the two deletion sets intersect in `m` points, on which `f` and `g` agree
    have hsub12 : {p₁, p₂} ⊆ S := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hmem1
      · exact hmem2
    have hT : U₁ ∩ U₂ = S \ {p₁, p₂} := by
      rw [hU₁eq, hU₂eq]
      ext x
      simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_singleton, Finset.mem_insert]
      constructor
      · rintro ⟨⟨hxS, hx1⟩, -, hx2⟩
        refine ⟨hxS, fun h => ?_⟩
        rcases h with rfl | rfl
        · exact hx1 rfl
        · exact hx2 rfl
      · rintro ⟨hxS, hxn⟩
        exact ⟨⟨hxS, fun h => hxn (Or.inl h)⟩, hxS, fun h => hxn (Or.inr h)⟩
    have hTcard : (U₁ ∩ U₂).card = m := by
      have h1 := Finset.card_sdiff_of_subset hsub12
      have h2 : ({p₁, p₂} : Finset (ℝ × ℝ)).card = 2 := Finset.card_pair_eq_two_iff.mpr hpp
      rw [hT]
      lia
    have hTn : (U₁ ∩ U₂).Nonempty := by
      rw [← Finset.card_pos]
      lia
    have hfd' : f.natDegree ≤ (U₁ ∩ U₂).card - 1 := by lia
    have hgd' : g.natDegree ≤ (U₁ ∩ U₂).card - 1 := by lia
    have hfg : f = g := poly_unique hTn hfd' hgd'
      (fun p hp => hfU p (Finset.mem_inter.mp hp).1)
      (fun p hp => hgU p (Finset.mem_inter.mp hp).2)
    -- so `f` passes through every point of `S`
    have hfS : ∀ p ∈ S, f.eval p.1 = p.2 := by
      intro p hp
      by_cases hp1 : p = p₁
      · have hpU₂ : p ∈ U₂ := by
          rw [hU₂eq, Finset.mem_sdiff, Finset.mem_singleton]
          exact ⟨hp, fun h => hpp (hp1.symm.trans h)⟩
        rw [hfg]
        exact hgU p hpU₂
      · have hpU₁ : p ∈ U₁ := by
          rw [hU₁eq, Finset.mem_sdiff, Finset.mem_singleton]
          exact ⟨hp, hp1⟩
        exact hfU p hpU₁
    exact hS ⟨by lia, f, hf0, by lia, hfS⟩

/-- A flooded set of `t ≥ 3` points has at least `t - 1` flooded subsets of size
`t - 1`. -/
lemma card_flooded_subsets {S : Finset (ℝ × ℝ)} {t : ℕ} (ht : 3 ≤ t)
    (hScard : S.card = t) (hS : ¬ Overdetermined S) :
    t - 1 ≤ ((S.powersetCard (t - 1)).filter (fun a => ¬ Overdetermined a)).card := by
  have hover : ((S.powersetCard (t - 1)).filter Overdetermined).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro U₁ hU₁ U₂ hU₂
    simp only [Finset.mem_filter, Finset.mem_powersetCard] at hU₁ hU₂
    obtain ⟨⟨hU₁S, hU₁c⟩, hU₁o⟩ := hU₁
    obtain ⟨⟨hU₂S, hU₂c⟩, hU₂o⟩ := hU₂
    exact eq_of_overdetermined_of_flooded hS (m := t - 2) (by lia)
      hU₁S (by lia) hU₁o hU₂S (by lia) hU₂o
  have htotal : (S.powersetCard (t - 1)).card = t := by
    rw [Finset.card_powersetCard, hScard, ← Nat.choose_symm (show t - 1 ≤ t by lia),
      show t - (t - 1) = 1 by lia, Nat.choose_one_right]
  have hsplit := Finset.card_filter_add_card_filter_not (s := S.powersetCard (t - 1)) Overdetermined
  rw [htotal] at hsplit
  lia

/-- A set `U` of `m` points of `A` is contained in at most `A.card - m` subsets of `A`
of size `m + 1`. -/
lemma card_supersets {A U : Finset (ℝ × ℝ)} (hU : U ⊆ A) {m : ℕ} (hUm : U.card = m) :
    ((A.powersetCard (m + 1)).filter (fun T => U ⊆ T)).card ≤ A.card - m := by
  have hinj : Set.InjOn (· \ U) (((A.powersetCard (m + 1)).filter (fun T => U ⊆ T)) : Set _) := by
    intro T₁ hT₁ T₂ hT₂ hsd
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_powersetCard] at hT₁ hT₂
    calc T₁ = U ∪ (T₁ \ U) := (Finset.union_sdiff_of_subset hT₁.2).symm
    _ = U ∪ (T₂ \ U) := by rw [show T₁ \ U = T₂ \ U from hsd]
    _ = T₂ := Finset.union_sdiff_of_subset hT₂.2
  have him : ((A.powersetCard (m + 1)).filter (fun T => U ⊆ T)).image (· \ U) ⊆
      (A \ U).powersetCard 1 := by
    intro V hV
    rcases Finset.mem_image.mp hV with ⟨T, hT, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_powersetCard] at hT
    have hc : (T \ U).card = 1 := by
      have h := Finset.card_sdiff_of_subset hT.2
      lia
    simp only [Finset.mem_powersetCard]
    exact ⟨Finset.sdiff_subset_sdiff hT.1.1 (Finset.Subset.refl U), hc⟩
  calc ((A.powersetCard (m + 1)).filter (fun T => U ⊆ T)).card
      = (((A.powersetCard (m + 1)).filter (fun T => U ⊆ T)).image (· \ U)).card :=
        (Finset.card_image_of_injOn hinj).symm
    _ ≤ ((A \ U).powersetCard 1).card := Finset.card_le_card him
    _ = (A \ U).card := by rw [Finset.card_powersetCard, Nat.choose_one_right]
    _ = A.card - m := by rw [Finset.card_sdiff_of_subset hU, hUm]

/-- Double counting of the incidence relation between flooded `m`-subsets and flooded
`(m+1)`-subsets of `A`. -/
lemma double_count {A : Finset (ℝ × ℝ)} {m : ℕ} (hm : 2 ≤ m) (_hmn : m < A.card) :
    m * ((A.powersetCard (m + 1)).filter (fun a => ¬ Overdetermined a)).card ≤
    (A.card - m) * ((A.powersetCard m).filter (fun a => ¬ Overdetermined a)).card := by
  set Fsucc := (A.powersetCard (m + 1)).filter (fun a => ¬ Overdetermined a) with hFsucc
  set Fm := (A.powersetCard m).filter (fun a => ¬ Overdetermined a) with hFm
  have key : ∀ T ∈ Fsucc, m ≤ (Fm.filter (fun U => U ⊆ T)).card := by
    intro T hT
    simp only [hFsucc, Finset.mem_filter, Finset.mem_powersetCard] at hT
    obtain ⟨⟨hTA, hTcard⟩, hTf⟩ := hT
    have hsub : (T.powersetCard m).filter (fun a => ¬ Overdetermined a) ⊆
        Fm.filter (fun U => U ⊆ T) := by
      intro U hU
      simp only [Finset.mem_filter, Finset.mem_powersetCard] at hU
      rw [hFm, Finset.mem_filter, Finset.mem_filter, Finset.mem_powersetCard]
      exact ⟨⟨⟨hU.1.1.trans hTA, hU.1.2⟩, hU.2⟩, hU.1.1⟩
    have h := card_flooded_subsets (S := T) (t := m + 1) (by lia) hTcard hTf
    rw [show m + 1 - 1 = m by lia] at h
    exact h.trans (Finset.card_le_card hsub)
  have upper : ∀ U ∈ Fm, (Fsucc.filter (fun T => U ⊆ T)).card ≤ A.card - m := by
    intro U hU
    simp only [hFm, Finset.mem_filter, Finset.mem_powersetCard] at hU
    obtain ⟨⟨hUA, hUcard⟩, -⟩ := hU
    have hsub : Fsucc.filter (fun T => U ⊆ T) ⊆
        (A.powersetCard (m + 1)).filter (fun T => U ⊆ T) := by
      intro T hT
      simp only [hFsucc, Finset.mem_filter] at hT
      simp only [Finset.mem_filter]
      exact ⟨hT.1.1, hT.2⟩
    exact (Finset.card_le_card hsub).trans (card_supersets hUA hUcard)
  have hsum : ∑ T ∈ Fsucc, (Fm.filter (fun U => U ⊆ T)).card =
      ∑ U ∈ Fm, (Fsucc.filter (fun T => U ⊆ T)).card := by
    have e : ∀ (s : Finset (Finset (ℝ × ℝ))) (p : Finset (ℝ × ℝ) → Prop) [DecidablePred p],
        (s.filter p).card = ∑ x ∈ s, (if p x then 1 else 0) := by
      intro s p _
      simp [Finset.sum_boole]
    conv_lhs => arg 2; ext T; rw [e Fm (fun U => U ⊆ T)]
    conv_rhs => arg 2; ext U; rw [e Fsucc (fun T => U ⊆ T)]
    exact Finset.sum_comm
  calc m * Fsucc.card = ∑ T ∈ Fsucc, m := by simp [Finset.sum_const, Nat.mul_comm]
    _ ≤ ∑ T ∈ Fsucc, (Fm.filter (fun U => U ⊆ T)).card := Finset.sum_le_sum key
    _ = ∑ U ∈ Fm, (Fsucc.filter (fun T => U ⊆ T)).card := hsum
    _ ≤ ∑ U ∈ Fm, (A.card - m) := Finset.sum_le_sum upper
    _ = (A.card - m) * Fm.card := by simp [Finset.sum_const, Nat.mul_comm]

/-- A flooded set `A` has at least `(A.card - 1).choose (m - 1)` flooded subsets of
size `m`, for every `2 ≤ m ≤ A.card`. -/
lemma flooded_count {A : Finset (ℝ × ℝ)} (hA : ¬ Overdetermined A) :
    ∀ m, 2 ≤ m → m ≤ A.card → Nat.choose (A.card - 1) (m - 1) ≤
      ((A.powersetCard m).filter (fun a => ¬ Overdetermined a)).card := by
  intro m h2m hmn
  revert h2m
  induction hmn using Nat.decreasingInduction with
  | self =>
    intro _
    have hF : (A.powersetCard A.card).filter (fun a => ¬ Overdetermined a) = {A} := by
      ext T
      simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨hTA, hTc⟩, -⟩
        exact Finset.eq_of_subset_of_card_le hTA (by lia)
      · rintro rfl
        exact ⟨⟨Finset.Subset.refl _, rfl⟩, hA⟩
    have h1 : ((A.powersetCard A.card).filter (fun a => ¬ Overdetermined a)).card = 1 := by
      rw [hF, Finset.card_singleton]
    have h2 : Nat.choose (A.card - 1) (A.card - 1) = 1 := Nat.choose_self _
    lia
  | @of_succ k hkn ih =>
    intro h2k
    have ih' := ih (by lia : 2 ≤ k + 1)
    simp only [Nat.add_sub_cancel] at ih'
    have hdc := double_count (A := A) (m := k) h2k hkn
    have hid : k * Nat.choose (A.card - 1) k =
        (A.card - k) * Nat.choose (A.card - 1) (k - 1) := by
      have h := Nat.choose_succ_right_eq (A.card - 1) (k - 1)
      rw [show k - 1 + 1 = k by lia, show A.card - 1 - (k - 1) = A.card - k by lia] at h
      rw [mul_comm k, mul_comm (A.card - k)]
      exact h
    have hpos : 0 < A.card - k := by lia
    have hle : (A.card - k) * Nat.choose (A.card - 1) (k - 1) ≤
        (A.card - k) * ((A.powersetCard k).filter (fun a => ¬ Overdetermined a)).card := by
      calc (A.card - k) * Nat.choose (A.card - 1) (k - 1)
          = k * Nat.choose (A.card - 1) k := hid.symm
        _ ≤ k * ((A.powersetCard (k + 1)).filter (fun a => ¬ Overdetermined a)).card :=
            Nat.mul_le_mul (le_refl k) ih'
        _ ≤ (A.card - k) * ((A.powersetCard k).filter (fun a => ¬ Overdetermined a)).card :=
            hdc
    exact Nat.le_of_mul_le_mul_left hle hpos

/-- The sum of `(n - 1).choose m` over `m ∈ Icc 2 n` equals `2 ^ (n - 1) - n`. -/
lemma sum_choose_Icc {n : ℕ} (hn : 2 ≤ n) :
    ∑ m ∈ Finset.Icc 2 n, Nat.choose (n - 1) m = 2 ^ (n - 1) - n := by
  have hge : n ≤ 2 ^ (n - 1) := by
    have h := two_pow_ge_succ (n - 1)
    lia
  have h1 : ∑ m ∈ Finset.range n, Nat.choose (n - 1) m = 2 ^ (n - 1) := by
    have h := Nat.sum_range_choose (n - 1)
    rwa [Nat.sub_add_cancel (by lia : 1 ≤ n)] at h
  have hIcc : Finset.Icc 2 n = (Finset.range (n - 1)).image (· + 2) := by
    ext m
    simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨h2m, hmn⟩
      exact ⟨m - 2, by lia, by lia⟩
    · rintro ⟨i, hi, rfl⟩
      lia
  have hr : Finset.range (n + 1) =
      insert 0 (insert 1 ((Finset.range (n - 1)).image (· + 2))) := by
    ext m
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_image]
    constructor
    · intro hm
      by_cases h0 : m = 0
      · exact Or.inl h0
      · by_cases h1' : m = 1
        · exact Or.inr (Or.inl h1')
        · exact Or.inr (Or.inr ⟨m - 2, by lia, by lia⟩)
    · rintro (rfl | rfl | ⟨i, hi, rfl⟩) <;> lia
  have h2 : Nat.choose (n - 1) 0 + (Nat.choose (n - 1) 1 +
      ∑ i ∈ Finset.range (n - 1), Nat.choose (n - 1) (i + 2)) = 2 ^ (n - 1) := by
    have h2' : ∑ m ∈ Finset.range (n + 1), Nat.choose (n - 1) m = 2 ^ (n - 1) := by
      rw [Finset.sum_range_succ, h1, Nat.choose_eq_zero_of_lt (by lia : n - 1 < n), add_zero]
    rw [hr, Finset.sum_insert (by
        simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_range]
        rintro (h | ⟨i, -, h⟩) <;> lia),
      Finset.sum_insert (by
        simp only [Finset.mem_image, Finset.mem_range]
        rintro ⟨i, -, h⟩; lia),
      Finset.sum_image (fun i _ j _ h => by lia)] at h2'
    exact h2'
  have h3 : ∑ i ∈ Finset.range (n - 1), Nat.choose (n - 1) (i + 2) = 2 ^ (n - 1) - n := by
    rw [Nat.choose_zero_right, Nat.choose_one_right] at h2
    lia
  rw [hIcc, Finset.sum_image (fun i _ j _ h => by lia)]
  exact h3

/-- An `n`-element flooded set of points has at most `2 ^ (n - 1) - n` overdetermined
subsets. -/
lemma overdetermined_bound {A : Finset (ℝ × ℝ)} (h2 : 2 ≤ A.card) (hA : ¬ Overdetermined A) :
    (A.powerset.filter Overdetermined).card ≤ 2 ^ (A.card - 1) - A.card := by
  have heq : A.powerset.filter Overdetermined =
      (Finset.Icc 2 A.card).biUnion (fun m => (A.powersetCard m).filter Overdetermined) := by
    ext T
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_biUnion, Finset.mem_Icc,
      Finset.mem_powersetCard]
    constructor
    · rintro ⟨hTA, hTo⟩
      exact ⟨T.card, ⟨hTo.1, Finset.card_le_card hTA⟩, ⟨⟨hTA, rfl⟩, hTo⟩⟩
    · rintro ⟨m, -, ⟨⟨hTA, -⟩, hTo⟩⟩
      exact ⟨hTA, hTo⟩
  have hdisj : (↑(Finset.Icc 2 A.card) : Set ℕ).PairwiseDisjoint
      (fun m => (A.powersetCard m).filter Overdetermined) := by
    intro m₁ _ m₂ _ hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro T hT₁ hT₂
    simp only [Finset.mem_filter, Finset.mem_powersetCard] at hT₁ hT₂
    exact hne (hT₁.1.2.symm.trans hT₂.1.2)
  rw [heq, Finset.card_biUnion hdisj]
  calc ∑ m ∈ Finset.Icc 2 A.card, ((A.powersetCard m).filter Overdetermined).card
      ≤ ∑ m ∈ Finset.Icc 2 A.card, Nat.choose (A.card - 1) m := by
        apply Finset.sum_le_sum
        intro m hm
        simp only [Finset.mem_Icc] at hm
        have hsplit := Finset.card_filter_add_card_filter_not (s := A.powersetCard m) Overdetermined
        rw [Finset.card_powersetCard] at hsplit
        have hflooded := flooded_count hA m hm.1 hm.2
        have hpascal : Nat.choose A.card m =
            Nat.choose (A.card - 1) m + Nat.choose (A.card - 1) (m - 1) := by
          have h := Nat.choose_succ_succ' (A.card - 1) (m - 1)
          rw [Nat.sub_add_cancel (show 1 ≤ A.card by lia),
            Nat.sub_add_cancel (show 1 ≤ m by lia)] at h
          lia
        lia
    _ = 2 ^ (A.card - 1) - A.card := sum_choose_Icc h2

/-- A finite set `s` has exactly `2 ^ s.card - s.card - 1` subsets of cardinality at
least two. -/
lemma card_powerset_filter_two_le {α : Type*} [DecidableEq α] (s : Finset α) :
    (s.powerset.filter (fun T => 2 ≤ T.card)).card = 2 ^ s.card - s.card - 1 := by
  have hge : s.card + 1 ≤ 2 ^ s.card := two_pow_ge_succ s.card
  have hsplit := Finset.card_filter_add_card_filter_not (s := s.powerset) (fun T => 2 ≤ T.card)
  rw [Finset.card_powerset] at hsplit
  have hsplit' : (s.powerset.filter (fun T => 2 ≤ T.card)).card +
      (s.powerset.filter (fun T => ¬ 2 ≤ T.card)).card = 2 ^ s.card := by
    simpa using hsplit
  have hcompl : (s.powerset.filter (fun T => ¬ 2 ≤ T.card)).card = s.card + 1 := by
    have heq : s.powerset.filter (fun T => ¬ 2 ≤ T.card) =
        s.powersetCard 0 ∪ s.powersetCard 1 := by
      ext T
      simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_union,
        Finset.mem_powersetCard]
      constructor
      · rintro ⟨hT, hc⟩
        by_cases h0 : T.card = 0
        · exact Or.inl ⟨hT, h0⟩
        · exact Or.inr ⟨hT, by lia⟩
      · rintro (⟨hT, h0⟩ | ⟨hT, h1⟩)
        · exact ⟨hT, by lia⟩
        · exact ⟨hT, by lia⟩
    rw [heq, Finset.card_union_of_disjoint (by
      rw [Finset.disjoint_left]
      intro T hT0 hT1
      simp only [Finset.mem_powersetCard] at hT0 hT1
      lia), Finset.card_powersetCard, Finset.card_powersetCard, Nat.choose_zero_right,
      Nat.choose_one_right, Nat.add_comm]
  lia

/-- The "tail" of the extremal construction: the points `(i, 2)` for `2 ≤ i ≤ n`. -/
noncomputable def tail (n : ℕ) : Finset (ℝ × ℝ) :=
  (Finset.Icc 2 n).image fun i : ℕ => ((i : ℝ), 2)

/-- The extremal construction: the points `(1, 1)` and `(i, 2)` for `2 ≤ i ≤ n`. -/
noncomputable def constrSet (n : ℕ) : Finset (ℝ × ℝ) :=
  insert ((1 : ℝ), (1 : ℝ)) (tail n)

lemma card_tail (n : ℕ) : (tail n).card = n - 1 := by
  have hinj : Set.InjOn (fun i : ℕ => ((i : ℝ), (2 : ℝ))) (Finset.Icc 2 n) := by
    intro i _ j _ h
    have h1 : (i : ℝ) = (j : ℝ) := congrArg Prod.fst h
    exact Nat.cast_injective h1
  rw [tail, Finset.card_image_of_injOn hinj, Nat.card_Icc]
  lia

lemma one_one_not_mem_tail {n : ℕ} : ((1 : ℝ), (1 : ℝ)) ∉ tail n := by
  simp only [tail, Finset.mem_image, Finset.mem_Icc]
  rintro ⟨i, -, h⟩
  have h1 : (2 : ℝ) = 1 := congrArg Prod.snd h
  norm_num at h1

lemma card_constrSet {n : ℕ} (hn : 2 ≤ n) : (constrSet n).card = n := by
  rw [constrSet, Finset.card_insert_of_notMem one_one_not_mem_tail, card_tail]
  lia

lemma not_overdetermined_constrSet {n : ℕ} (hn : 2 ≤ n) : ¬ Overdetermined (constrSet n) := by
  rintro ⟨-, P, hP0, hPd, hPS⟩
  rw [card_constrSet hn] at hPd
  have hX : ∀ x ∈ (Finset.Icc 2 n).image (fun i : ℕ => (i : ℝ)), (P - Polynomial.C 2).eval x = 0 := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
    rw [Polynomial.eval_sub, Polynomial.eval_C]
    have hmem : ((i : ℝ), 2) ∈ constrSet n :=
      Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
    have h2 : P.eval (i : ℝ) = 2 := hPS ((i : ℝ), 2) hmem
    rw [h2]
    exact sub_self 2
  have hXcard : ((Finset.Icc 2 n).image (fun i : ℕ => (i : ℝ))).card = n - 1 := by
    rw [Finset.card_image_of_injOn (fun i _ j _ h => Nat.cast_injective h), Nat.card_Icc]
    lia
  by_cases hPC : P - Polynomial.C 2 = 0
  · have hP2 : P = Polynomial.C 2 := sub_eq_zero.mp hPC
    have hmem : ((1 : ℝ), (1 : ℝ)) ∈ constrSet n := Finset.mem_insert_self _ _
    have h1 : P.eval 1 = 1 := hPS ((1 : ℝ), (1 : ℝ)) hmem
    rw [hP2, Polynomial.eval_C] at h1
    norm_num at h1
  · have hle := roots_card_bound hPC hX
    have hdeg : (P - Polynomial.C 2).natDegree ≤ n - 2 :=
      calc (P - Polynomial.C 2).natDegree ≤ max P.natDegree (Polynomial.C (2 : ℝ)).natDegree :=
          Polynomial.natDegree_sub_le P (Polynomial.C 2)
      _ = P.natDegree := by rw [Polynomial.natDegree_C, max_eq_left (Nat.zero_le _)]
      _ ≤ n - 2 := hPd
    lia

/-- The overdetermined subsets of the extremal construction are exactly the subsets of
its tail with at least two elements. -/
lemma overdetermined_subset_constrSet_iff {n : ℕ} {T : Finset (ℝ × ℝ)}
    (hT : T ⊆ constrSet n) : Overdetermined T ↔ T ⊆ tail n ∧ 2 ≤ T.card := by
  constructor
  · rintro ⟨h2T, P, hP0, hPd, hPS⟩
    have hnotmem : ((1 : ℝ), (1 : ℝ)) ∉ T := by
      intro hmem
      have hT'sub : T \ {((1 : ℝ), (1 : ℝ))} ⊆ tail n := by
        intro p hp
        rw [Finset.mem_sdiff, Finset.mem_singleton] at hp
        have hp3 := hT hp.1
        rw [constrSet, Finset.mem_insert] at hp3
        rcases hp3 with h1 | h2
        · exact absurd h1 hp.2
        · exact h2
      have hT'card : (T \ {((1 : ℝ), (1 : ℝ))}).card = T.card - 1 := by
        have h := Finset.card_sdiff_of_subset (Finset.singleton_subset_iff.mpr hmem)
        rwa [Finset.card_singleton] at h
      have hinj : Set.InjOn Prod.fst (tail n : Set (ℝ × ℝ)) := by
        intro a ha b hb hab
        rw [tail, Finset.mem_coe, Finset.mem_image] at ha hb
        rcases ha with ⟨i, -, rfl⟩
        rcases hb with ⟨j, -, rfl⟩
        have hij : (i : ℝ) = (j : ℝ) := hab
        rw [Nat.cast_injective hij]
      have hX : ∀ x ∈ (T \ {((1 : ℝ), (1 : ℝ))}).image Prod.fst,
          (P - Polynomial.C 2).eval x = 0 := by
        intro x hx
        rcases Finset.mem_image.mp hx with ⟨p, hpT', rfl⟩
        rw [Polynomial.eval_sub, Polynomial.eval_C]
        have hp2 : p.2 = 2 := by
          have hp := hT'sub hpT'
          rw [tail, Finset.mem_image] at hp
          rcases hp with ⟨i, -, rfl⟩
          rfl
        have hpT : p ∈ T := (Finset.mem_sdiff.mp hpT').1
        rw [hPS p hpT, hp2, sub_self]
      by_cases hPC : P - Polynomial.C 2 = 0
      · have hP2 : P = Polynomial.C 2 := sub_eq_zero.mp hPC
        have h1 : P.eval 1 = 1 := hPS ((1 : ℝ), (1 : ℝ)) hmem
        rw [hP2, Polynomial.eval_C] at h1
        norm_num at h1
      · have hle := roots_card_bound hPC hX
        have himg : ((T \ {((1 : ℝ), (1 : ℝ))}).image Prod.fst).card = T.card - 1 := by
          rw [Finset.card_image_of_injOn (hinj.mono (Finset.coe_subset.mpr hT'sub))]
          exact hT'card
        have hdeg : (P - Polynomial.C 2).natDegree ≤ T.card - 2 :=
          calc (P - Polynomial.C 2).natDegree ≤ max P.natDegree (Polynomial.C (2 : ℝ)).natDegree :=
              Polynomial.natDegree_sub_le P (Polynomial.C 2)
          _ = P.natDegree := by rw [Polynomial.natDegree_C, max_eq_left (Nat.zero_le _)]
          _ ≤ T.card - 2 := hPd
        lia
    have hTtail : T ⊆ tail n := by
      intro p hp
      have hp1 := hT hp
      rw [constrSet, Finset.mem_insert] at hp1
      rcases hp1 with h1 | h2
      · rw [h1] at hp
        exact absurd hp hnotmem
      · exact h2
    exact ⟨hTtail, h2T⟩
  · rintro ⟨hTtail, h2T⟩
    refine ⟨h2T, Polynomial.C 2, Polynomial.C_ne_zero.mpr (by norm_num), by
      rw [Polynomial.natDegree_C]; exact Nat.zero_le _, ?_⟩
    intro p hp
    have hpmem := hTtail hp
    rw [tail, Finset.mem_image] at hpmem
    rcases hpmem with ⟨i, -, rfl⟩
    rw [Polynomial.eval_C]

/-- The extremal construction has exactly `2 ^ (n - 1) - n` overdetermined subsets. -/
lemma count_constrSet {n : ℕ} (hn : 2 ≤ n) :
    ((constrSet n).powerset.filter Overdetermined).card = 2 ^ (n - 1) - n := by
  have heq : (constrSet n).powerset.filter Overdetermined =
      (tail n).powerset.filter (fun T => 2 ≤ T.card) := by
    ext T
    simp only [Finset.mem_filter, Finset.mem_powerset]
    constructor
    · rintro ⟨hT, hTo⟩
      exact (overdetermined_subset_constrSet_iff hT).mp hTo
    · rintro ⟨hTtail, h2T⟩
      have hT : T ⊆ constrSet n := fun p hp => Finset.mem_insert_of_mem (hTtail hp)
      exact ⟨hT, (overdetermined_subset_constrSet_iff hT).mpr ⟨hTtail, h2T⟩⟩
  have hge : n ≤ 2 ^ (n - 1) := by
    have h := two_pow_ge_succ (n - 1)
    lia
  rw [heq, card_powerset_filter_two_le, card_tail]
  lia

snip end

problem usa2020_p5 (n : ℕ) (hn : 2 ≤ n) :
    IsGreatest {k : ℕ | ∃ S : Finset (ℝ × ℝ), S.card = n ∧ ¬ Overdetermined S ∧
      (S.powerset.filter Overdetermined).card = k} (solution n) := by
  constructor
  · exact ⟨constrSet n, card_constrSet hn, not_overdetermined_constrSet hn,
      count_constrSet hn⟩
  · intro k hk
    obtain ⟨S, hScard, hS, hk⟩ := hk
    rw [← hk]
    have hb := overdetermined_bound (A := S) (by lia) hS
    rw [hScard] at hb
    exact hb

end Usa2020P5
