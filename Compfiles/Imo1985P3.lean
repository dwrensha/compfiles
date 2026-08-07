/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.Tactic.NormNum
public import ProblemExtraction

@[expose] public section

problem_file {
  tags := [.Algebra]
}

/-!
# International Mathematical Olympiad 1985, Problem 3

For any polynomial $P(x) = a_0 + a_1x + \dots + a_kx^k$ with integer coefficients, the
number of odd coefficients is denoted by $o(P)$. For $i = 0, 1, 2, \dots$ let
$Q_i(x) = (1 + x)^i$. Prove that if $i_1, i_2, \dots, i_n$ are integers satisfying
$0 \le i_1 < i_2 < \dots < i_n$, then
$$o(Q_{i_1} + Q_{i_2} + \dots + Q_{i_n}) \ge o(Q_{i_1}).$$
-/

namespace Imo1985P3

open Polynomial

/-- The number of odd coefficients of a polynomial with integer coefficients. -/
noncomputable def oddCount (P : ℤ[X]) : ℕ :=
  (P.support.filter fun n => Odd (P.coeff n)).card

snip begin

/-!
# Solution

We count odd coefficients modulo $2$: the number of odd coefficients of `P : ℤ[X]` equals
the number `o P` of nonzero coefficients of its image in `(ZMod 2)[X]`. If `m` is a power
of two then $(1 + X)^m = 1 + X^m$ in characteristic $2$ (the freshman's dream), and for
polynomials `p q` of degree less than `m` the supports of `p` and `X ^ m * q` are disjoint,
so `o (p + X ^ m * q) = o p + o q`. We also have `o p ≤ o (p + q) + o q` for all `p`, `q`.

The main claim is then proved by strong induction on the largest index $i_n$. Let $m$ be
the largest power of two with $m \le i_n$, so $i_n < 2m$. If every index is at least $m$,
every term factors through $(1 + X)^m$, and the claim follows from the induction hypothesis
applied to the set of indices shifted down by $m$. Otherwise the sum splits into a "low"
part (indices below $m$) and a "high" part; the high part factors through $(1 + X)^m$, and
the claim follows from the induction hypothesis applied to the low part together with the
inequality `o p ≤ o (p + q) + o q`.
-/

/-- `o P` is the number of nonzero coefficients of a polynomial `P` over `ZMod 2`. -/
noncomputable def o (P : (ZMod 2)[X]) : ℕ := P.support.card

/-- The support of `X ^ m * p` is the support of `p` shifted by `m`. -/
lemma support_X_pow_mul (m : ℕ) (p : (ZMod 2)[X]) :
    (X ^ m * p).support = p.support.image (· + m) := by
  ext j
  simp only [mem_support_iff, coeff_X_pow_mul', ne_eq, Finset.mem_image]
  by_cases hjm : m ≤ j
  · rw [if_pos hjm]
    constructor
    · intro h
      exact ⟨j - m, h, Nat.sub_add_cancel hjm⟩
    · rintro ⟨a, ha, rfl⟩
      rw [Nat.add_sub_cancel]
      exact ha
  · rw [if_neg hjm]
    constructor
    · intro h
      exact absurd rfl h
    · rintro ⟨a, ha, rfl⟩
      exact absurd (Nat.le_add_left m a) hjm

/-- If `p` has degree less than `m`, the supports of `p` and `X ^ m * q` are
disjoint, hence `o (p + X ^ m * q) = o p + o q`. -/
lemma o_add_X_pow_mul {m : ℕ} {p q : (ZMod 2)[X]} (hp : p.natDegree < m) :
    o (p + X ^ m * q) = o p + o q := by
  have hsupp : (p + X ^ m * q).support = p.support ∪ (X ^ m * q).support := by
    apply Finset.Subset.antisymm support_add
    intro j hj
    rw [mem_support_iff]
    rcases Finset.mem_union.mp hj with hj | hj
    · have hjm : j < m := lt_of_le_of_lt (le_natDegree_of_mem_supp j hj) hp
      rw [mem_support_iff] at hj
      rwa [coeff_add, coeff_X_pow_mul', if_neg (show ¬ m ≤ j by omega), add_zero]
    · rw [support_X_pow_mul] at hj
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
      rw [mem_support_iff] at hk
      have hpk : p.coeff (k + m) = 0 :=
        coeff_eq_zero_of_natDegree_lt (show p.natDegree < k + m by omega)
      rwa [coeff_add, hpk, zero_add, coeff_X_pow_mul', if_pos (show m ≤ k + m by omega),
        Nat.add_sub_cancel]
  have hdisj : Disjoint p.support (X ^ m * q).support := by
    rw [Finset.disjoint_left]
    intro j hj hj2
    have hjm : j < m := lt_of_le_of_lt (le_natDegree_of_mem_supp j hj) hp
    rw [support_X_pow_mul] at hj2
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj2
    omega
  unfold o
  rw [hsupp, Finset.card_union_of_disjoint hdisj, support_X_pow_mul,
    Finset.card_image_of_injective _ (fun _ _ h ↦ Nat.add_right_cancel h)]

/-- Subadditivity of `o`. -/
lemma o_add_le (p q : (ZMod 2)[X]) : o (p + q) ≤ o p + o q :=
  le_trans (Finset.card_le_card support_add) (Finset.card_union_le _ _)

/-- A convenient rearrangement of subadditivity. -/
lemma o_le_o_add_add (p q : (ZMod 2)[X]) : o p ≤ o (p + q) + o q := by
  have hn : o (-q) = o q := congrArg Finset.card support_neg
  calc o p = o ((p + q) + (-q)) := by rw [add_neg_cancel_right]
    _ ≤ o (p + q) + o (-q) := o_add_le _ _
    _ = o (p + q) + o q := by rw [hn]

/-- The degree of `(1 + X) ^ i` over `ZMod 2`. -/
lemma natDegree_one_add_X_pow (i : ℕ) : ((1 + X : (ZMod 2)[X]) ^ i).natDegree = i := by
  have h : (1 + X : (ZMod 2)[X]) = X + C 1 := by rw [C_1]; exact add_comm _ _
  rw [h, Monic.natDegree_pow (monic_X_add_C (1 : ZMod 2)) i, natDegree_X_add_C, mul_one]

/-- The freshman's dream in characteristic $2$: `(1 + X) ^ (2 ^ k) = 1 + X ^ (2 ^ k)`. -/
lemma one_add_X_pow_two_pow (k : ℕ) :
    (1 + X : (ZMod 2)[X]) ^ 2 ^ k = 1 + X ^ 2 ^ k := by
  rw [add_pow_expChar_pow, one_pow]

/-- The number of odd coefficients of `P : ℤ[X]` equals `o` of its image in
`(ZMod 2)[X]`. -/
lemma oddCount_eq_o (P : ℤ[X]) :
    oddCount P = o (P.map (Int.castRingHom (ZMod 2))) := by
  unfold oddCount o
  congr 1
  ext j
  simp only [Finset.mem_filter, mem_support_iff, coeff_map, Int.coe_castRingHom]
  constructor
  · rintro ⟨-, hodd⟩
    simp only [ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd]
    intro hdvd
    exact (Int.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr (by exact_mod_cast hdvd))
  · intro hj
    simp only [ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd] at hj
    have hodd : Odd (P.coeff j) :=
      Int.not_even_iff_odd.mp fun he ↦ hj (by exact_mod_cast even_iff_two_dvd.mp he)
    refine ⟨?_, hodd⟩
    intro hz
    rw [hz] at hodd
    obtain ⟨k, hk⟩ := hodd
    omega

/-- The image of a single power of `1 + X` in `(ZMod 2)[X]`. -/
lemma map_one_add_X_pow (i : ℕ) :
    ((1 + X : ℤ[X]) ^ i).map (Int.castRingHom (ZMod 2)) = (1 + X : (ZMod 2)[X]) ^ i := by
  rw [Polynomial.map_pow, Polynomial.map_add, Polynomial.map_one, Polynomial.map_X]

/-- The image of a sum of powers of `1 + X` in `(ZMod 2)[X]`. -/
lemma map_sum_one_add_X_pow (S : Finset ℕ) :
    (∑ i ∈ S, (1 + X : ℤ[X]) ^ i).map (Int.castRingHom (ZMod 2)) =
      ∑ i ∈ S, (1 + X : (ZMod 2)[X]) ^ i := by
  rw [Polynomial.map_sum]
  exact Finset.sum_congr rfl fun i _ ↦ by
    rw [Polynomial.map_pow, Polynomial.map_add, Polynomial.map_one, Polynomial.map_X]

/-- The main inequality over `ZMod 2`, proved by strong induction on the largest
index `N`. -/
lemma key : ∀ N : ℕ, ∀ (S : Finset ℕ) (hS : S.Nonempty), S.max' hS = N →
    o ((1 + X : (ZMod 2)[X]) ^ S.min' hS) ≤
      o (∑ i ∈ S, (1 + X : (ZMod 2)[X]) ^ i) :=
  fun N ↦ Nat.strong_induction_on N fun N IH S hS hN ↦ by
    by_cases hN0 : N = 0
    · subst hN0
      have hS0 : S = {0} := by
        apply Finset.eq_singleton_iff_nonempty_unique_mem.mpr
        exact ⟨hS, fun x hx ↦ by
          have hx0 := le_trans (Finset.le_max' S x hx) (le_of_eq hN)
          omega⟩
      subst hS0
      rw [Finset.min'_singleton, Finset.sum_singleton]
    · obtain ⟨k, hkN, hNk⟩ : ∃ k, 2 ^ k ≤ N ∧ N < 2 ^ (k + 1) :=
        ⟨Nat.log 2 N, Nat.pow_log_le_self 2 hN0, Nat.lt_pow_succ_log_self (by norm_num) N⟩
      have hfrob : (1 + X : (ZMod 2)[X]) ^ (2 ^ k) = 1 + X ^ (2 ^ k) :=
        one_add_X_pow_two_pow k
      set m := 2 ^ k with hmdef
      have hm1 : 1 ≤ m := by rw [hmdef]; exact pow_pos (show (0 : ℕ) < 2 by norm_num) k
      have hmN : m ≤ N := hkN
      have hNm : N < 2 * m := by
        rw [hmdef]
        rw [pow_succ'] at hNk
        exact hNk
      by_cases hcase : S.min' hS < m
      · -- The smallest index is below `m`: split the sum into a low part and a high part.
        set A := S.filter (· < m)
        set B := S.filter fun i ↦ ¬ i < m
        have hAne : A.Nonempty :=
          ⟨S.min' hS, Finset.mem_filter.mpr ⟨Finset.min'_mem S hS, hcase⟩⟩
        have hBne : B.Nonempty :=
          ⟨S.max' hS, Finset.mem_filter.mpr
            ⟨Finset.max'_mem S hS, not_lt.mpr (le_trans hmN (le_of_eq hN.symm))⟩⟩
        have hAB : Disjoint A B := Finset.disjoint_filter_filter_not S S (· < m)
        have hunion : A ∪ B = S := Finset.filter_union_filter_not_eq (p := (· < m)) S
        have hmaxA : A.max' hAne < m := (Finset.mem_filter.mp (Finset.max'_mem A hAne)).2
        have hRdeg : (∑ i ∈ A, (1 + X : (ZMod 2)[X]) ^ i).natDegree < m := by
          refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le A _ fun i hi ↦ ?_) hmaxA
          rw [natDegree_one_add_X_pow]
          exact Finset.le_max' A i hi
        have hTdeg : (∑ i ∈ B, (1 + X : (ZMod 2)[X]) ^ (i - m)).natDegree < m := by
          refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le B _ fun i hi ↦ ?_)
            (show N - m < m by omega)
          rw [natDegree_one_add_X_pow]
          have hiS : i ∈ S := Finset.mem_of_mem_filter i hi
          have hiN : i ≤ N := le_trans (Finset.le_max' S i hiS) (le_of_eq hN)
          omega
        have hBsum : ∑ i ∈ B, (1 + X : (ZMod 2)[X]) ^ i =
            (1 + X ^ m) * ∑ i ∈ B, (1 + X : (ZMod 2)[X]) ^ (i - m) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i hi ↦ ?_
          have him : m ≤ i := not_lt.mp (Finset.mem_filter.mp hi).2
          rw [← hfrob, ← pow_add, show m + (i - m) = i by omega]
        have hdecomp : ∑ i ∈ S, (1 + X : (ZMod 2)[X]) ^ i =
            (∑ i ∈ A, (1 + X : (ZMod 2)[X]) ^ i +
              ∑ i ∈ B, (1 + X : (ZMod 2)[X]) ^ (i - m)) +
              X ^ m * ∑ i ∈ B, (1 + X : (ZMod 2)[X]) ^ (i - m) := by
          have hsum : ∑ i ∈ S, (1 + X : (ZMod 2)[X]) ^ i =
              (∑ i ∈ A, (1 + X : (ZMod 2)[X]) ^ i) +
                ∑ i ∈ B, (1 + X : (ZMod 2)[X]) ^ i := by
            rw [← hunion, Finset.sum_union hAB]
          rw [hsum, hBsum, add_mul, one_mul, ← add_assoc]
        have hRTdeg : (∑ i ∈ A, (1 + X : (ZMod 2)[X]) ^ i +
            ∑ i ∈ B, (1 + X : (ZMod 2)[X]) ^ (i - m)).natDegree < m :=
          lt_of_le_of_lt (natDegree_add_le _ _) (by omega)
        rw [hdecomp, o_add_X_pow_mul hRTdeg]
        have hminA : A.min' hAne = S.min' hS := by
          apply le_antisymm
          · exact Finset.min'_le A (S.min' hS)
              (Finset.mem_filter.mpr ⟨Finset.min'_mem S hS, hcase⟩)
          · exact Finset.min'_le S (A.min' hAne)
              (Finset.mem_of_mem_filter _ (Finset.min'_mem A hAne))
        have ihA := IH (A.max' hAne) (by omega) A hAne rfl
        rw [hminA] at ihA
        exact le_trans ihA (o_le_o_add_add _ _)
      · -- Every index is at least `m`: everything factors through `(1 + X) ^ m`.
        push Not at hcase
        have hmi : ∀ i ∈ S, m ≤ i := fun i hi ↦ le_trans hcase (Finset.min'_le S i hi)
        have hsplit : ∑ i ∈ S, (1 + X : (ZMod 2)[X]) ^ i =
            (1 + X ^ m) * ∑ i ∈ S, (1 + X : (ZMod 2)[X]) ^ (i - m) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i hi ↦ ?_
          have him : m ≤ i := hmi i hi
          rw [← hfrob, ← pow_add, show m + (i - m) = i by omega]
        have hTdeg : (∑ i ∈ S, (1 + X : (ZMod 2)[X]) ^ (i - m)).natDegree < m := by
          refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le S _ fun i hi ↦ ?_)
            (show N - m < m by omega)
          rw [natDegree_one_add_X_pow]
          have hiN : i ≤ N := le_trans (Finset.le_max' S i hi) (le_of_eq hN)
          omega
        have hS'ne : (S.image (· - m)).Nonempty := hS.image _
        have hsub_inj : ∀ x ∈ S, ∀ y ∈ S, x - m = y - m → x = y := by
          intro x hx y hy hxy
          have h1 := hmi x hx
          have h2 := hmi y hy
          omega
        have hT' : (∑ i ∈ S, (1 + X : (ZMod 2)[X]) ^ (i - m)) =
            ∑ j ∈ S.image (· - m), (1 + X : (ZMod 2)[X]) ^ j :=
          (Finset.sum_image hsub_inj).symm
        have hmaxS' : (S.image (· - m)).max' hS'ne = N - m := by
          rw [Finset.max'_image (fun _ _ hab ↦ by omega) S hS'ne]
          exact congrArg (· - m) hN
        have hminS' : (S.image (· - m)).min' hS'ne = S.min' hS - m := by
          rw [Finset.min'_image (fun _ _ hab ↦ by omega) S hS'ne]
        have ihS' := IH (N - m) (by omega) (S.image (· - m)) hS'ne hmaxS'
        rw [hminS', ← hT'] at ihS'
        have hmindeg : ((1 + X : (ZMod 2)[X]) ^ (S.min' hS - m)).natDegree < m := by
          rw [natDegree_one_add_X_pow]
          have hle : S.min' hS ≤ N :=
            le_trans (Finset.min'_le S _ (Finset.max'_mem S hS)) (le_of_eq hN)
          omega
        have hmin : (1 + X : (ZMod 2)[X]) ^ S.min' hS =
            (1 + X ^ m) * (1 + X : (ZMod 2)[X]) ^ (S.min' hS - m) := by
          rw [← hfrob, ← pow_add, show m + (S.min' hS - m) = S.min' hS by omega]
        rw [hsplit, add_mul, one_mul, o_add_X_pow_mul hTdeg, hmin, add_mul, one_mul,
          o_add_X_pow_mul hmindeg]
        omega

snip end

problem imo1985_p3 (S : Finset ℕ) (hS : S.Nonempty) :
    oddCount ((1 + X : ℤ[X]) ^ S.min' hS) ≤
      oddCount (∑ i ∈ S, (1 + X : ℤ[X]) ^ i) := by
  rw [oddCount_eq_o, map_one_add_X_pow, oddCount_eq_o, map_sum_one_add_X_pow]
  exact key _ S hS rfl

end Imo1985P3
