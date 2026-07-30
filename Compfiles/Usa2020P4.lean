/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Data.Int.Star
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.LinearCombination.Lemmas
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics] }

/-!
# USA Mathematical Olympiad 2020, Problem 4

Suppose that (a₁, b₁), (a₂, b₂), ..., (a₁₀₀, b₁₀₀) are distinct ordered pairs
of nonnegative integers. Let N denote the number of pairs of integers (i, j)
satisfying 1 ≤ i < j ≤ 100 and |aᵢbⱼ − aⱼbᵢ| = 1. Determine the largest
possible value of N over all possible choices of the 100 ordered pairs.
-/

namespace Usa2020P4

/-- The determinant `aᵢ bⱼ − aⱼ bᵢ` of two ordered pairs of nonnegative
integers, viewed as an integer. -/
def det (P Q : ℕ × ℕ) : ℤ := (P.1 : ℤ) * (Q.2 : ℤ) - (Q.1 : ℤ) * (P.2 : ℤ)

determine answer : ℕ := 197

snip begin

/-!
## Solution

The answer is `197 = 2 * 100 - 3`; more generally the maximum for `n ≥ 2`
points is `2n - 3`.

*Construction*: take `(1, 0)` together with `(k, 1)` for `1 ≤ k ≤ 99`. The
good pairs are `{(1, 0), (k, 1)}` for `1 ≤ k ≤ 99` (99 pairs) and
`{(k, 1), (k + 1, 1)}` for `1 ≤ k ≤ 98` (98 pairs), totalling `197`.

*Upper bound*: induction on `n`. Given `n ≥ 3` points, let `P` be a point with
maximal distance from the origin. Then `P` belongs to at most two good pairs:
if `P = (0, 0)` or `gcd P.1 P.2 > 1` it belongs to none, since `gcd P.1 P.2`
divides every determinant `det P Q`; and if `P = (a, b)` is primitive, the good
partners `Q` of `P` lie on one of the two lines `det P Q = ±1`. On each line
the lattice points are spaced exactly by the vector `(a, b)`, so at most one of
them (other than the origin, which is never a good partner) can lie in the
closed disk of radius `|P|` around the origin that contains all the given
points. Removing `P` therefore destroys at most two good pairs, and
`2 * (n - 1) - 3 + 2 = 2 * n - 3` by induction.
-/

/-- The good two-element subsets of a set of points: those `{P, Q}` with
`|det P Q| = 1`. -/
private def goodSets (S : Finset (ℕ × ℕ)) : Finset (Finset (ℕ × ℕ)) :=
  (S.powersetCard 2).filter fun s => ∀ P ∈ s, ∀ Q ∈ s, P ≠ Q → |det P Q| = 1

/-- The good index pairs of a choice `v` of 100 points. -/
private def goodPairs (v : Fin 100 → ℕ × ℕ) : Finset (Fin 100 × Fin 100) :=
  Finset.univ.filter fun p => p.1 < p.2 ∧ |det (v p.1) (v p.2)| = 1

private lemma det_swap (P Q : ℕ × ℕ) : det Q P = -det P Q := by unfold det; ring

/-- If `(u, v) = (u', v') + t • (a, b)` with `t ≥ 1`, all of `u' v' a b`
nonnegative, and `u² + v² ≤ a² + b²`, then `(u', v') = (0, 0)`. -/
private lemma eq_zero_of_eq_add_mul {u v u' v' a b t : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hu' : 0 ≤ u') (hv' : 0 ≤ v') (ht : 1 ≤ t)
    (huu : u = u' + t * a) (hvv : v = v' + t * b)
    (hn : u ^ 2 + v ^ 2 ≤ a ^ 2 + b ^ 2) : u' = 0 ∧ v' = 0 := by
  have h1 : a ≤ u := by
    calc a = 1 * a := (one_mul a).symm
    _ ≤ t * a := mul_le_mul_of_nonneg_right ht ha
    _ ≤ u' + t * a := le_add_of_nonneg_left hu'
    _ = u := huu.symm
  have h2 : b ≤ v := by
    calc b = 1 * b := (one_mul b).symm
    _ ≤ t * b := mul_le_mul_of_nonneg_right ht hb
    _ ≤ v' + t * b := le_add_of_nonneg_left hv'
    _ = v := hvv.symm
  have h3 : a ^ 2 ≤ u ^ 2 := pow_le_pow_left₀ ha h1 2
  have h4 : b ^ 2 ≤ v ^ 2 := pow_le_pow_left₀ hb h2 2
  have h5 : a ^ 2 = u ^ 2 ∧ b ^ 2 = v ^ 2 := by constructor <;> linarith
  have hu_eq : u = a := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp h5.1.symm with h | h
    · exact h
    · linarith
  have hv_eq : v = b := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp h5.2.symm with h | h
    · exact h
    · linarith
  have hu'e : u' = (1 - t) * a := by linear_combination hu_eq - huu
  have hv'e : v' = (1 - t) * b := by linear_combination hv_eq - hvv
  have h1t : (1 : ℤ) - t ≤ 0 := by linarith
  exact ⟨le_antisymm (by rw [hu'e]; exact mul_nonpos_of_nonpos_of_nonneg h1t ha) hu',
    le_antisymm (by rw [hv'e]; exact mul_nonpos_of_nonpos_of_nonneg h1t hb) hv'⟩

/-- Two points of the first quadrant having the same determinant of absolute
value `1` with a primitive point `P`, and both at most as far from the origin
as `P`, must coincide. -/
private lemma eq_of_det_eq_of_le {P Q₁ Q₂ : ℕ × ℕ} (hP : Nat.Coprime P.1 P.2)
    (hdet : det P Q₁ = det P Q₂) (habs : |det P Q₁| = 1)
    (hn₁ : Q₁.1 ^ 2 + Q₁.2 ^ 2 ≤ P.1 ^ 2 + P.2 ^ 2)
    (hn₂ : Q₂.1 ^ 2 + Q₂.2 ^ 2 ≤ P.1 ^ 2 + P.2 ^ 2) : Q₁ = Q₂ := by
  obtain ⟨a, b⟩ := P
  obtain ⟨u₁, v₁⟩ := Q₁
  obtain ⟨u₂, v₂⟩ := Q₂
  simp only [det] at hdet habs
  dsimp only at hP hn₁ hn₂ hdet habs
  have hn₁' : (u₁ : ℤ) ^ 2 + (v₁ : ℤ) ^ 2 ≤ (a : ℤ) ^ 2 + (b : ℤ) ^ 2 := by
    exact_mod_cast hn₁
  have hn₂' : (u₂ : ℤ) ^ 2 + (v₂ : ℤ) ^ 2 ≤ (a : ℤ) ^ 2 + (b : ℤ) ^ 2 := by
    exact_mod_cast hn₂
  have h1 : (a : ℤ) * ((v₁ : ℤ) - (v₂ : ℤ)) = ((u₁ : ℤ) - (u₂ : ℤ)) * (b : ℤ) := by
    linear_combination hdet
  have hcop : IsCoprime (a : ℤ) (b : ℤ) := Int.isCoprime_iff_gcd_eq_one.mpr (by
    rw [Int.gcd_natCast_natCast]; exact hP)
  have hdvd : (a : ℤ) ∣ (u₁ : ℤ) - u₂ :=
    hcop.dvd_of_dvd_mul_right ⟨(v₁ : ℤ) - v₂, h1.symm⟩
  obtain ⟨t, hta, htb⟩ :
      ∃ t : ℤ, (u₁ : ℤ) - u₂ = t * a ∧ (v₁ : ℤ) - v₂ = t * b := by
    obtain ⟨t, ht⟩ := hdvd
    by_cases ha0 : (a : ℤ) = 0
    · have ha0' : a = 0 := by exact_mod_cast ha0
      have hb1 : (b : ℤ) = 1 := by
        have hP1 : Nat.gcd a b = 1 := hP
        rw [ha0', Nat.gcd_zero_left] at hP1
        exact_mod_cast hP1
      exact ⟨(v₁ : ℤ) - v₂, by rw [ht, ha0, zero_mul, mul_zero], by rw [hb1, mul_one]⟩
    · refine ⟨t, by rw [ht, mul_comm], ?_⟩
      have h2 : (a : ℤ) * ((v₁ : ℤ) - v₂) = (a : ℤ) * (t * (b : ℤ)) := by
        rw [h1, ht]; ring
      exact mul_left_cancel₀ ha0 h2
  have hta' : (u₁ : ℤ) = u₂ + t * a := by linear_combination hta
  have htb' : (v₁ : ℤ) = v₂ + t * b := by linear_combination htb
  rcases lt_or_ge t 1 with htl | htg
  · by_cases ht0 : t = 0
    · subst ht0
      rw [zero_mul, add_zero] at hta'
      rw [zero_mul, add_zero] at htb'
      exact Prod.ext_iff.mpr ⟨Nat.cast_inj.mp hta', Nat.cast_inj.mp htb'⟩
    · have htn : 1 ≤ -t := by omega
      have huu : (u₂ : ℤ) = u₁ + (-t) * a := by linear_combination -hta'
      have hvv : (v₂ : ℤ) = v₁ + (-t) * b := by linear_combination -htb'
      obtain ⟨hu1, hv1⟩ := eq_zero_of_eq_add_mul (Int.natCast_nonneg _)
        (Int.natCast_nonneg _) (Int.natCast_nonneg _) (Int.natCast_nonneg _)
        htn huu hvv hn₂'
      rw [hu1, hv1] at habs
      simp at habs
  · obtain ⟨hu2, hv2⟩ := eq_zero_of_eq_add_mul (Int.natCast_nonneg _)
      (Int.natCast_nonneg _) (Int.natCast_nonneg _) (Int.natCast_nonneg _)
      htg hta' htb' hn₁'
    rw [hdet, hu2, hv2] at habs
    simp at habs

/-- The gcd of the coordinates of `P` divides every determinant `det P Q`. -/
private lemma gcd_dvd_det (P Q : ℕ × ℕ) : (Nat.gcd P.1 P.2 : ℤ) ∣ det P Q := by
  obtain ⟨a, b⟩ := P
  obtain ⟨u, v⟩ := Q
  exact dvd_sub (dvd_mul_of_dvd_left (by exact_mod_cast Nat.gcd_dvd_left a b) _)
    (dvd_mul_of_dvd_right (by exact_mod_cast Nat.gcd_dvd_right a b) _)

/-- A farthest point `P` of `S` forms good pairs with at most two points
of `S`. -/
private lemma card_partners_le_two {S : Finset (ℕ × ℕ)} {P : ℕ × ℕ}
    (hmax : ∀ Q ∈ S, Q.1 ^ 2 + Q.2 ^ 2 ≤ P.1 ^ 2 + P.2 ^ 2) :
    ((S.erase P).filter fun Q => |det P Q| = 1).card ≤ 2 := by
  by_cases hP : Nat.Coprime P.1 P.2
  · have hmaps : Set.MapsTo (det P) ((S.erase P).filter fun Q => |det P Q| = 1)
        ({1, -1} : Finset ℤ) := by
      intro Q hQ
      rw [Finset.mem_coe, Finset.mem_filter] at hQ
      rcases eq_or_eq_neg_of_abs_eq hQ.2 with h | h
      · rw [Finset.mem_coe, h]; exact Finset.mem_insert_self 1 {-1}
      · rw [Finset.mem_coe, h]
        exact Finset.mem_insert_of_mem (Finset.mem_singleton_self (-1))
    have hinj : Set.InjOn (det P) ((S.erase P).filter fun Q => |det P Q| = 1) := by
      intro Q₁ hQ₁ Q₂ hQ₂ hd
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_erase] at hQ₁ hQ₂
      exact eq_of_det_eq_of_le hP hd hQ₁.2 (hmax Q₁ hQ₁.1.2) (hmax Q₂ hQ₂.1.2)
    have h2card : (({1, -1} : Finset ℤ)).card = 2 :=
      Finset.card_pair_eq_two_iff.mpr (by norm_num)
    exact (Finset.card_le_card_of_injOn (det P) hmaps hinj).trans_eq h2card
  · suffices h : ((S.erase P).filter fun Q => |det P Q| = 1) = ∅ by
      rw [h, Finset.card_empty]; exact Nat.zero_le 2
    rw [Finset.filter_eq_empty_iff]
    intro Q hQ habs
    obtain ⟨a, b⟩ := P
    have hdvd := gcd_dvd_det (a, b) Q
    have hdvd1 : ((Nat.gcd (a, b).1 (a, b).2 : ℕ) : ℤ) ∣ 1 := by
      rcases eq_or_eq_neg_of_abs_eq habs with h | h
      · rwa [h] at hdvd
      · rw [h] at hdvd; exact dvd_neg.mp hdvd
    have h1 : ((Nat.gcd (a, b).1 (a, b).2 : ℕ) : ℤ) = 1 := by
      rcases Int.isUnit_iff.mp (isUnit_of_dvd_one hdvd1) with h | h
      · exact h
      · have hnonneg : (0 : ℤ) ≤ ((Nat.gcd (a, b).1 (a, b).2 : ℕ) : ℤ) :=
          Int.natCast_nonneg _
        linarith
    exact hP (by exact_mod_cast h1)

/-- A set of `n ≥ 2` points determines at most `2 * n - 3` good pairs. -/
private lemma card_goodSets_le : ∀ n : ℕ, 2 ≤ n → ∀ S : Finset (ℕ × ℕ),
    S.card = n → (goodSets S).card ≤ 2 * n - 3 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro hn S hcard
    rcases Nat.lt_or_ge n 3 with hlt | hge
    · have hn2 : n = 2 := by omega
      subst hn2
      calc (goodSets S).card ≤ (S.powersetCard 2).card := Finset.card_filter_le _ _
        _ = 1 := by rw [Finset.card_powersetCard, hcard]; decide
    · have hne : S.Nonempty := Finset.card_pos.mp (by rw [hcard]; omega)
      obtain ⟨P, hPS, hmax⟩ :=
        Finset.exists_max_image S (fun Q : ℕ × ℕ => Q.1 ^ 2 + Q.2 ^ 2) hne
      have hcard' : (S.erase P).card = n - 1 := by
        rw [Finset.card_erase_of_mem hPS, hcard]
      have hIH : (goodSets (S.erase P)).card ≤ 2 * (n - 1) - 3 :=
        IH (n - 1) (by omega) (by omega) (S.erase P) hcard'
      have hpart : ((S.erase P).filter fun Q => |det P Q| = 1).card ≤ 2 :=
        card_partners_le_two hmax
      have hcover : goodSets S ⊆ goodSets (S.erase P) ∪
          ((S.erase P).filter fun Q => |det P Q| = 1).image (fun Q => {P, Q}) := by
        intro s hs
        rw [goodSets, Finset.mem_filter, Finset.mem_powersetCard] at hs
        obtain ⟨⟨hsS, hscard⟩, hsgood⟩ := hs
        by_cases hPs : P ∈ s
        · obtain ⟨Q, hQe⟩ := Finset.card_eq_one.mp (by
            rw [Finset.card_erase_of_mem hPs, hscard])
          have hQse : Q ∈ s.erase P := by rw [hQe]; exact Finset.mem_singleton_self Q
          have hQs : Q ∈ s := Finset.mem_of_mem_erase hQse
          have hQP : P ≠ Q := fun h => (Finset.mem_erase.mp (h ▸ hQse)).1 rfl
          have hs_eq : s = {P, Q} := by rw [← Finset.insert_erase hPs, hQe]
          have hQS : Q ∈ S.erase P := by
            have hsub : s.erase P ⊆ S.erase P := Finset.erase_subset_erase P hsS
            rw [hQe] at hsub
            exact Finset.singleton_subset_iff.mp hsub
          have hQgood : |det P Q| = 1 := hsgood P hPs Q hQs hQP
          exact Finset.mem_union_right _ (Finset.mem_image.mpr
            ⟨Q, Finset.mem_filter.mpr ⟨hQS, hQgood⟩, hs_eq.symm⟩)
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr
            ⟨Finset.mem_powersetCard.mpr
              ⟨Finset.subset_erase.mpr ⟨hsS, hPs⟩, hscard⟩, hsgood⟩)
      have h1 : (goodSets S).card ≤ (goodSets (S.erase P) ∪
          ((S.erase P).filter fun Q => |det P Q| = 1).image
            (fun Q => ({P, Q} : Finset (ℕ × ℕ)))).card :=
        Finset.card_le_card hcover
      have h2 : (goodSets (S.erase P) ∪
          ((S.erase P).filter fun Q => |det P Q| = 1).image
            (fun Q => ({P, Q} : Finset (ℕ × ℕ)))).card ≤
          (goodSets (S.erase P)).card +
          (((S.erase P).filter fun Q => |det P Q| = 1).image
            (fun Q => ({P, Q} : Finset (ℕ × ℕ)))).card :=
        Finset.card_union_le _ _
      have h3 : (goodSets (S.erase P)).card +
          (((S.erase P).filter fun Q => |det P Q| = 1).image
            (fun Q => ({P, Q} : Finset (ℕ × ℕ)))).card ≤
          (2 * (n - 1) - 3) + 2 :=
        add_le_add hIH (le_trans Finset.card_image_le hpart)
      have h4 : (2 * (n - 1) - 3) + 2 = 2 * n - 3 := by omega
      exact h1.trans ((h2.trans h3).trans_eq h4)

set_option maxRecDepth 4096 in
/-- For an injective choice `v` of points, the good index pairs and the good
two-element subsets of the image are equinumerous. -/
private lemma card_goodPairs_eq {v : Fin 100 → ℕ × ℕ} (hv : Function.Injective v) :
    (goodPairs v).card = (goodSets (Finset.univ.image v)).card := by
  apply Finset.card_bij (fun p _ => ({v p.1, v p.2} : Finset (ℕ × ℕ)))
  · intro p hp
    simp only [goodPairs, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    obtain ⟨hlt, hgood⟩ := hp
    have hne : v p.1 ≠ v p.2 := fun h => hlt.ne (hv h)
    rw [goodSets, Finset.mem_filter, Finset.mem_powersetCard]
    refine ⟨⟨?_, Finset.card_pair_eq_two_iff.mpr hne⟩, ?_⟩
    · intro x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> exact Finset.mem_image_of_mem v (Finset.mem_univ _)
    · intro P hP Q hQ hPQ
      rw [Finset.mem_insert, Finset.mem_singleton] at hP hQ
      rcases hP with rfl | rfl
      · rcases hQ with rfl | rfl
        · exact absurd rfl hPQ
        · exact hgood
      · rcases hQ with rfl | rfl
        · rw [det_swap, abs_neg]; exact hgood
        · exact absurd rfl hPQ
  · intro p hp q hq h
    simp only [goodPairs, Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
    have h1 : v p.1 ∈ ({v q.1, v q.2} : Finset (ℕ × ℕ)) := by
      rw [← h]; exact Finset.mem_insert_self _ _
    have h2 : v p.2 ∈ ({v q.1, v q.2} : Finset (ℕ × ℕ)) := by
      rw [← h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    rw [Finset.mem_insert, Finset.mem_singleton] at h1 h2
    rcases h1 with h1 | h1
    · rcases h2 with h2 | h2
      · exact absurd ((hv (h2.trans h1.symm)).symm) hp.1.ne
      · exact Prod.ext_iff.mpr ⟨hv h1, hv h2⟩
    · rcases h2 with h2 | h2
      · have e1 : p.1 = q.2 := hv h1
        have e2 : p.2 = q.1 := hv h2
        exfalso; omega
      · exact absurd (hv (h1.trans h2.symm)) hp.1.ne
  · intro s hs
    rw [goodSets, Finset.mem_filter, Finset.mem_powersetCard] at hs
    obtain ⟨⟨hsS, hscard⟩, hsgood⟩ := hs
    obtain ⟨P, Q, hPQ, hsPQ⟩ := Finset.card_eq_two.mp hscard
    subst hsPQ
    have hPS : P ∈ Finset.univ.image v := hsS (Finset.mem_insert_self P {Q})
    have hQS : Q ∈ Finset.univ.image v :=
      hsS (Finset.mem_insert_of_mem (Finset.mem_singleton_self Q))
    rw [Finset.mem_image] at hPS hQS
    obtain ⟨i, -, hi⟩ := hPS
    obtain ⟨j, -, hj⟩ := hQS
    have hgood : |det P Q| = 1 := hsgood P (Finset.mem_insert_self P {Q}) Q
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self Q)) hPQ
    have hij : i ≠ j := fun h => hPQ (hi.symm.trans (h ▸ hj))
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · refine ⟨(i, j), ?_, ?_⟩
      · simp only [goodPairs, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨hlt, ?_⟩
        show |det (v i) (v j)| = 1
        rw [hi, hj]; exact hgood
      · show ({v i, v j} : Finset (ℕ × ℕ)) = {P, Q}
        rw [hi, hj]
    · refine ⟨(j, i), ?_, ?_⟩
      · simp only [goodPairs, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨hgt, ?_⟩
        show |det (v j) (v i)| = 1
        rw [hj, hi, det_swap, abs_neg]; exact hgood
      · show ({v j, v i} : Finset (ℕ × ℕ)) = {P, Q}
        rw [hj, hi, Finset.pair_comm]

snip end

/-- USA Mathematical Olympiad 2020, Problem 4 -/
problem usamo2020_p4 :
    IsGreatest {N : ℕ | ∃ v : Fin 100 → ℕ × ℕ, Function.Injective v ∧
      N = (Finset.univ.filter fun p : Fin 100 × Fin 100 =>
        p.1 < p.2 ∧ |det (v p.1) (v p.2)| = 1).card} answer := by
  constructor
  · refine ⟨fun i => if i = 0 then (1, 0) else (i.val, 1), ?_, ?_⟩
    · decide
    · set_option maxRecDepth 10000 in decide
  · intro N hN
    obtain ⟨v, hv, hN'⟩ := hN
    rw [hN']
    change (goodPairs v).card ≤ answer
    rw [card_goodPairs_eq hv]
    have h100 : (Finset.univ.image v).card = 100 := by
      rw [Finset.card_image_of_injective _ hv, Finset.card_univ, Fintype.card_fin]
    exact (card_goodSets_le 100 (by norm_num) _ h100).trans_eq (by norm_num [answer])

end Usa2020P4
