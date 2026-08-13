/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Data.Int.ConditionallyCompleteOrder
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.Ring
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Algebra, .NumberTheory] }

/-!
# USA Mathematical Olympiad 2004, Problem 2

Suppose a₁, a₂, …, aₙ are integers whose greatest common divisor is 1.
Let S be a set of integers with the following properties:

(a) For i = 1, 2, …, n, aᵢ ∈ S.

(b) For i, j = 1, 2, …, n (not necessarily distinct), aᵢ − aⱼ ∈ S.

(c) For any integers x, y ∈ S, if x + y ∈ S, then x − y ∈ S.

Prove that S must equal the set of all integers.
-/

namespace Usa2004P2

snip begin

-- The proof follows the solution in Evan Chen's USAMO 2004 solution notes
-- (https://web.evanchen.cc/exams/USAMO-2004-notes.pdf): one shows that every
-- integer linear combination of the aᵢ lies in S, and then Bézout's lemma
-- (using that the gcd of the aᵢ is 1) shows that every integer is in S.

variable {n : ℕ} {a : Fin n → ℤ} {S : Set ℤ}

/-- Bézout's identity for finitely many integers: the gcd of the values of `a`
on a finset `T` is an integer linear combination of them. -/
lemma bezout (T : Finset (Fin n)) :
    ∃ c : Fin n → ℤ, ∑ i ∈ T, c i * a i = T.gcd a := by
  induction T using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert b T hbT ih =>
    obtain ⟨c, hc⟩ := ih
    rw [Finset.gcd_insert]
    refine ⟨Function.update (fun i => c i * Int.gcdB (a b) (T.gcd a)) b
      (Int.gcdA (a b) (T.gcd a)), ?_⟩
    rw [Finset.sum_insert hbT, Function.update_self]
    have hsum : ∑ i ∈ T, (Function.update (fun i => c i * Int.gcdB (a b) (T.gcd a)) b
          (Int.gcdA (a b) (T.gcd a))) i * a i
        = ∑ i ∈ T, (c i * Int.gcdB (a b) (T.gcd a)) * a i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Function.update_of_ne (ne_of_mem_of_not_mem hi hbT)]
    have hterm : ∀ i ∈ T, (c i * Int.gcdB (a b) (T.gcd a)) * a i
        = Int.gcdB (a b) (T.gcd a) * (c i * a i) := fun i _ => by ring
    rw [hsum, Finset.sum_congr rfl hterm, ← Finset.mul_sum, hc, ← Int.coe_gcd,
      Int.gcd_eq_gcd_ab]
    ring

/-- From (b) with `i = j` we get `0 ∈ S`, and then (c) with `x = 0` shows that
`S` is closed under negation. -/
lemma neg_mem (h0 : (0 : ℤ) ∈ S)
    (hcond : ∀ x y : ℤ, x ∈ S → y ∈ S → x + y ∈ S → x - y ∈ S)
    {s : ℤ} (hs : s ∈ S) : -s ∈ S := by
  have h := hcond 0 s h0 hs (by simpa using hs)
  simpa using h

/-- The key reformulation of condition (c): for `x, y ∈ S`, the membership of
`x + y` and of `x - y` in `S` are equivalent. -/
lemma add_mem_iff_sub_mem (h0 : (0 : ℤ) ∈ S)
    (hcond : ∀ x y : ℤ, x ∈ S → y ∈ S → x + y ∈ S → x - y ∈ S)
    {x y : ℤ} (hx : x ∈ S) (hy : y ∈ S) : x + y ∈ S ↔ x - y ∈ S := by
  refine ⟨hcond x y hx hy, fun h => ?_⟩
  have h1 : x + -y ∈ S := by rwa [sub_eq_add_neg] at h
  have h2 := hcond x (-y) hx (neg_mem h0 hcond hy) h1
  rwa [sub_neg_eq_add] at h2

/-- Any natural multiple of a generator lies in `S`. -/
lemma nat_mul_mem (h0 : (0 : ℤ) ∈ S) (ha : ∀ i, a i ∈ S)
    (hcond : ∀ x y : ℤ, x ∈ S → y ∈ S → x + y ∈ S → x - y ∈ S)
    (k : Fin n) (c : ℕ) : (c : ℤ) * a k ∈ S := by
  have aux : ∀ c : ℕ, ((c : ℤ) * a k ∈ S) ∧ (((c + 1 : ℕ) : ℤ) * a k ∈ S) := by
    intro c
    induction c with
    | zero => exact ⟨by simpa using h0, by simpa using ha k⟩
    | succ c ih =>
      refine ⟨ih.2, ?_⟩
      have e : (((c + 1 + 1 : ℕ) : ℤ)) * a k = ((c + 1 : ℕ) : ℤ) * a k + a k := by
        push_cast; ring
      rw [e]
      refine (add_mem_iff_sub_mem h0 hcond ih.2 (ha k)).mpr ?_
      have e2 : ((c + 1 : ℕ) : ℤ) * a k - a k = (c : ℤ) * a k := by push_cast; ring
      rw [e2]
      exact ih.1
  exact (aux c).1

/-- Any number of the form `c * a i - a j` with `c : ℕ` lies in `S`. -/
lemma sub_one_mem (h0 : (0 : ℤ) ∈ S) (ha : ∀ i, a i ∈ S)
    (hdiff : ∀ i j, a i - a j ∈ S)
    (hcond : ∀ x y : ℤ, x ∈ S → y ∈ S → x + y ∈ S → x - y ∈ S)
    (i j : Fin n) (c : ℕ) : (c : ℤ) * a i - a j ∈ S := by
  have aux : ∀ c : ℕ, ((c : ℤ) * a i - a j ∈ S) ∧ (((c + 1 : ℕ) : ℤ) * a i - a j ∈ S) := by
    intro c
    induction c with
    | zero => exact ⟨by simpa using neg_mem h0 hcond (ha j), by simpa using hdiff i j⟩
    | succ c ih =>
      refine ⟨ih.2, ?_⟩
      have e : (((c + 1 + 1 : ℕ) : ℤ)) * a i - a j
          = (((c + 1 : ℕ) : ℤ) * a i - a j) + a i := by push_cast; ring
      rw [e]
      refine (add_mem_iff_sub_mem h0 hcond ih.2 (ha i)).mpr ?_
      have e2 : ((c + 1 : ℕ) : ℤ) * a i - a j - a i = (c : ℤ) * a i - a j := by
        push_cast; ring
      rw [e2]
      exact ih.1
  exact (aux c).1

/-- Any combination `c * a i + d * a j` with `c d : ℕ` lies in `S`. -/
lemma nat_add_mem (h0 : (0 : ℤ) ∈ S) (ha : ∀ i, a i ∈ S)
    (hdiff : ∀ i j, a i - a j ∈ S)
    (hcond : ∀ x y : ℤ, x ∈ S → y ∈ S → x + y ∈ S → x - y ∈ S)
    (i j : Fin n) (c d : ℕ) : (c : ℤ) * a i + (d : ℤ) * a j ∈ S := by
  have aux : ∀ d : ℕ, ((c : ℤ) * a i + (d : ℤ) * a j ∈ S)
      ∧ ((c : ℤ) * a i + ((d + 1 : ℕ) : ℤ) * a j ∈ S) := by
    intro d
    induction d with
    | zero =>
      refine ⟨by simpa using nat_mul_mem h0 ha hcond i c, ?_⟩
      have e : (c : ℤ) * a i + ((0 + 1 : ℕ) : ℤ) * a j = (c : ℤ) * a i + a j := by simp
      rw [e]
      exact (add_mem_iff_sub_mem h0 hcond (nat_mul_mem h0 ha hcond i c) (ha j)).mpr
        (sub_one_mem h0 ha hdiff hcond i j c)
    | succ d ih =>
      refine ⟨ih.2, ?_⟩
      have e : (c : ℤ) * a i + (((d + 1 + 1 : ℕ) : ℤ)) * a j
          = ((c : ℤ) * a i + ((d + 1 : ℕ) : ℤ) * a j) + a j := by push_cast; ring
      rw [e]
      refine (add_mem_iff_sub_mem h0 hcond ih.2 (ha j)).mpr ?_
      have e2 : (c : ℤ) * a i + ((d + 1 : ℕ) : ℤ) * a j - a j
          = (c : ℤ) * a i + (d : ℤ) * a j := by push_cast; ring
      rw [e2]
      exact ih.1
  exact (aux d).1

/-- Any combination `c * a i - d * a j` with `c d : ℕ` lies in `S`. -/
lemma nat_sub_mem (h0 : (0 : ℤ) ∈ S) (ha : ∀ i, a i ∈ S)
    (hdiff : ∀ i j, a i - a j ∈ S)
    (hcond : ∀ x y : ℤ, x ∈ S → y ∈ S → x + y ∈ S → x - y ∈ S)
    (i j : Fin n) (c d : ℕ) : (c : ℤ) * a i - (d : ℤ) * a j ∈ S := by
  have aux : ∀ d : ℕ, ((c : ℤ) * a i - (d : ℤ) * a j ∈ S)
      ∧ ((c : ℤ) * a i - ((d + 1 : ℕ) : ℤ) * a j ∈ S) := by
    intro d
    induction d with
    | zero =>
      refine ⟨by simpa using nat_mul_mem h0 ha hcond i c, ?_⟩
      have e : (c : ℤ) * a i - ((0 + 1 : ℕ) : ℤ) * a j = (c : ℤ) * a i - a j := by simp
      rw [e]
      exact sub_one_mem h0 ha hdiff hcond i j c
    | succ d ih =>
      refine ⟨ih.2, ?_⟩
      have e : (c : ℤ) * a i - (((d + 1 + 1 : ℕ) : ℤ)) * a j
          = ((c : ℤ) * a i - ((d + 1 : ℕ) : ℤ) * a j) - a j := by push_cast; ring
      rw [e]
      have e2 : (c : ℤ) * a i - ((d + 1 : ℕ) : ℤ) * a j + a j
          = (c : ℤ) * a i - (d : ℤ) * a j := by push_cast; ring
      have h3 : (c : ℤ) * a i - ((d + 1 : ℕ) : ℤ) * a j + a j ∈ S := by
        rw [e2]; exact ih.1
      exact (add_mem_iff_sub_mem h0 hcond ih.2 (ha j)).mp h3
  exact (aux d).1

/-- First lemma of the informal proof: any two-term integer linear combination
`c * a i + d * a j` lies in `S`. -/
lemma two_term_mem (h0 : (0 : ℤ) ∈ S) (ha : ∀ i, a i ∈ S)
    (hdiff : ∀ i j, a i - a j ∈ S)
    (hcond : ∀ x y : ℤ, x ∈ S → y ∈ S → x + y ∈ S → x - y ∈ S)
    (i j : Fin n) (c d : ℤ) : c * a i + d * a j ∈ S := by
  by_cases hc0 : 0 ≤ c <;> by_cases hd0 : 0 ≤ d
  · lift c to ℕ using hc0
    lift d to ℕ using hd0
    exact nat_add_mem h0 ha hdiff hcond i j c d
  · lift c to ℕ using hc0
    obtain ⟨d₀, rfl⟩ : ∃ d₀ : ℕ, d = -(d₀ : ℤ) :=
      ⟨(-d).toNat, by rw [Int.toNat_of_nonneg (neg_nonneg.mpr (not_le.mp hd0).le)]; ring⟩
    convert nat_sub_mem h0 ha hdiff hcond i j c d₀ using 1
    ring
  · obtain ⟨c₀, rfl⟩ : ∃ c₀ : ℕ, c = -(c₀ : ℤ) :=
      ⟨(-c).toNat, by rw [Int.toNat_of_nonneg (neg_nonneg.mpr (not_le.mp hc0).le)]; ring⟩
    lift d to ℕ using hd0
    convert neg_mem h0 hcond (nat_sub_mem h0 ha hdiff hcond i j c₀ d) using 1
    ring
  · obtain ⟨c₀, rfl⟩ : ∃ c₀ : ℕ, c = -(c₀ : ℤ) :=
      ⟨(-c).toNat, by rw [Int.toNat_of_nonneg (neg_nonneg.mpr (not_le.mp hc0).le)]; ring⟩
    obtain ⟨d₀, rfl⟩ : ∃ d₀ : ℕ, d = -(d₀ : ℤ) :=
      ⟨(-d).toNat, by rw [Int.toNat_of_nonneg (neg_nonneg.mpr (not_le.mp hd0).le)]; ring⟩
    convert neg_mem h0 hcond (nat_add_mem h0 ha hdiff hcond i j c₀ d₀) using 1
    ring

/-- Splitting step of the second lemma of the informal proof: if some
coefficient `c p` is even, then `∑ i ∈ T, c i * a i` can be written as
`x - y` with `x, y, x + y ∈ S`, where membership of `x` and `x + y` comes
from the induction hypothesis on strictly smaller finsets. -/
lemma even_split (h0 : (0 : ℤ) ∈ S) (ha : ∀ i, a i ∈ S)
    (hdiff : ∀ i j, a i - a j ∈ S)
    (hcond : ∀ x y : ℤ, x ∈ S → y ∈ S → x + y ∈ S → x - y ∈ S)
    {T : Finset (Fin n)}
    (IH : ∀ U : Finset (Fin n), U ⊂ T → ∀ c : Fin n → ℤ, ∑ i ∈ U, c i * a i ∈ S)
    {c : Fin n → ℤ} {p q : Fin n} (hp : p ∈ T) (hq : q ∈ T) (hpq : p ≠ q)
    (hpe : Even (c p)) : ∑ i ∈ T, c i * a i ∈ S := by
  obtain ⟨k, hk⟩ := hpe
  have hpT' : p ∈ T.erase q := Finset.mem_erase.mpr ⟨hpq, hp⟩
  have hqT' : q ∈ T.erase p := Finset.mem_erase.mpr ⟨hpq.symm, hq⟩
  set R := (T.erase p).erase q with hR
  set c₁ := Function.update c p k with hc₁
  have hx : ∑ i ∈ T.erase q, c₁ i * a i ∈ S := IH _ (Finset.erase_ssubset hq) c₁
  have hx' : ∑ i ∈ T.erase q, c₁ i * a i = k * a p + ∑ i ∈ R, c i * a i := by
    rw [← Finset.add_sum_erase _ _ hpT']
    have hperase : (T.erase q).erase p = R := by
      rw [hR]; ext i; simp only [Finset.mem_erase]; tauto
    rw [hperase]
    congr 1
    · simp [hc₁]
    · apply Finset.sum_congr rfl
      intro i hi
      have hne : i ≠ p := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
      simp [hc₁, Function.update_of_ne hne]
  have hy : (-k) * a p + (-(c q)) * a q ∈ S := two_term_mem h0 ha hdiff hcond p q (-k) (-(c q))
  set c₂ := Function.update c q (-(c q)) with hc₂
  have hxy : ∑ i ∈ T.erase p, c₂ i * a i ∈ S := IH _ (Finset.erase_ssubset hp) c₂
  have hxy' : ∑ i ∈ T.erase p, c₂ i * a i = -(c q) * a q + ∑ i ∈ R, c i * a i := by
    rw [← Finset.add_sum_erase _ _ hqT']
    congr 1
    · simp [hc₂]
    · apply Finset.sum_congr rfl
      intro i hi
      have hne : i ≠ q := (Finset.mem_erase.mp hi).1
      simp [hc₂, Function.update_of_ne hne]
  have hxy2 : (∑ i ∈ T.erase q, c₁ i * a i) + ((-k) * a p + (-(c q)) * a q)
      = ∑ i ∈ T.erase p, c₂ i * a i := by
    rw [hx', hxy']; ring
  rw [← hxy2] at hxy
  have hfin := hcond _ _ hx hy hxy
  have hgoal : (∑ i ∈ T.erase q, c₁ i * a i) - ((-k) * a p + (-(c q)) * a q)
      = ∑ i ∈ T, c i * a i := by
    rw [hx']
    have hT : ∑ i ∈ T, c i * a i = c p * a p + (c q * a q + ∑ i ∈ R, c i * a i) := by
      rw [← Finset.add_sum_erase T _ hp, ← Finset.add_sum_erase (T.erase p) _ hqT']
    rw [hT, hk]; ring
  rwa [hgoal] at hfin

/-- Second lemma of the informal proof: every integer linear combination of
the generators lies in `S`. Proved by strong induction on the finset `T`:
vanishing coefficients are simply removed, an even coefficient allows the
`even_split` step, and if all coefficients are odd one first perturbs two of
them using `u * a q = v * a p` (where `u = a p / gcd a p a q`,
`v = a q / gcd a p a q`) to manufacture an even coefficient. -/
lemma all_linear_comb (h0 : (0 : ℤ) ∈ S) (ha : ∀ i, a i ∈ S)
    (hdiff : ∀ i j, a i - a j ∈ S)
    (hcond : ∀ x y : ℤ, x ∈ S → y ∈ S → x + y ∈ S → x - y ∈ S)
    (T : Finset (Fin n)) (c : Fin n → ℤ) : ∑ i ∈ T, c i * a i ∈ S := by
  induction T using Finset.strongInduction generalizing c with
  | H T IH =>
    by_cases hz : ∃ p ∈ T, c p = 0
    · obtain ⟨p, hpT, hp0⟩ := hz
      have e : ∑ i ∈ T, c i * a i = ∑ i ∈ T.erase p, c i * a i := by
        rw [← Finset.add_sum_erase T _ hpT, hp0, zero_mul, zero_add]
      rw [e]
      exact IH _ (Finset.erase_ssubset hpT) c
    · push Not at hz
      by_cases hT : T.card ≤ 1
      · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hT with h1 | h1
        · rw [Finset.card_eq_zero.mp h1]
          simpa using h0
        · obtain ⟨p, rfl⟩ := Finset.card_eq_one.mp h1
          rw [Finset.sum_singleton]
          simpa using two_term_mem h0 ha hdiff hcond p p (c p) 0
      · push Not at hT
        obtain ⟨p, hpT⟩ := Finset.card_pos.mp (by omega : 0 < T.card)
        obtain ⟨q, hqT'⟩ := Finset.card_pos.mp (by
          rw [Finset.card_erase_of_mem hpT]; omega : 0 < (T.erase p).card)
        have hqT : q ∈ T := (Finset.mem_erase.mp hqT').2
        have hqp : q ≠ p := (Finset.mem_erase.mp hqT').1
        by_cases he : ∃ r ∈ T, Even (c r)
        · obtain ⟨r, hrT, hre⟩ := he
          obtain ⟨r', hr'T'⟩ := Finset.card_pos.mp (by
            rw [Finset.card_erase_of_mem hrT]; omega : 0 < (T.erase r).card)
          exact even_split h0 ha hdiff hcond IH hrT (Finset.mem_erase.mp hr'T').2
            (fun h => (Finset.mem_erase.mp hr'T').1 h.symm) hre
        · push Not at he
          by_cases hap : a p = 0
          · have e : ∑ i ∈ T, c i * a i = ∑ i ∈ T.erase p, c i * a i := by
              rw [← Finset.add_sum_erase T _ hpT, hap, mul_zero, zero_add]
            rw [e]
            exact IH _ (Finset.erase_ssubset hpT) c
          · have hg0 : 0 < Int.gcd (a p) (a q) := Int.gcd_pos_of_ne_zero_left _ hap
            obtain ⟨u, v, huv, hap_eq, haq_eq⟩ := Int.exists_gcd_one hg0
            set g : ℤ := ((a p).gcd (a q) : ℤ) with hg
            set c' := Function.update (Function.update c p (c p + v)) q (c q - u) with hc'
            have hcp : c' p = c p + v := by
              rw [hc', Function.update_of_ne hqp.symm, Function.update_self]
            have hcq : c' q = c q - u := by rw [hc', Function.update_self]
            have hcr : ∀ i ∈ (T.erase p).erase q, c' i = c i := by
              intro i hi
              have hiq : i ≠ q := (Finset.mem_erase.mp hi).1
              have hip : i ≠ p := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
              rw [hc', Function.update_of_ne hiq, Function.update_of_ne hip]
            have sum_eq : ∑ i ∈ T, c' i * a i = ∑ i ∈ T, c i * a i := by
              rw [← Finset.add_sum_erase T (fun i => c' i * a i) hpT,
                ← Finset.add_sum_erase T (fun i => c i * a i) hpT,
                ← Finset.add_sum_erase (T.erase p) (fun i => c' i * a i) hqT',
                ← Finset.add_sum_erase (T.erase p) (fun i => c i * a i) hqT',
                hcp, hcq, Finset.sum_congr rfl (fun i hi => by rw [hcr i hi]), hap_eq, haq_eq]
              ring
            by_cases hz2 : c' p = 0 ∨ c' q = 0
            · rcases hz2 with hz2 | hz2
              · have e : ∑ i ∈ T, c' i * a i = ∑ i ∈ T.erase p, c' i * a i := by
                  rw [← Finset.add_sum_erase T _ hpT, hz2, zero_mul, zero_add]
                rw [← sum_eq, e]
                exact IH _ (Finset.erase_ssubset hpT) c'
              · have e : ∑ i ∈ T, c' i * a i = ∑ i ∈ T.erase q, c' i * a i := by
                  rw [← Finset.add_sum_erase T _ hqT, hz2, zero_mul, zero_add]
                rw [← sum_eq, e]
                exact IH _ (Finset.erase_ssubset hqT) c'
            · push Not at hz2
              obtain ⟨hzp, hzq⟩ := hz2
              have huv2 : ¬(Even u ∧ Even v) := by
                rintro ⟨hu2, hv2⟩
                have h2dvd : (2 : ℤ) ∣ (Int.gcd u v : ℤ) :=
                  Int.dvd_coe_gcd (Even.two_dvd hu2) (Even.two_dvd hv2)
                rw [huv] at h2dvd
                norm_num at h2dvd
              have hodp : Odd (c p) := Int.not_even_iff_odd.mp (he p hpT)
              have hodq : Odd (c q) := Int.not_even_iff_odd.mp (he q hqT)
              by_cases hve : Even v
              · have hou : Odd u := Int.not_even_iff_odd.mp (fun hu2 => huv2 ⟨hu2, hve⟩)
                have heven : Even (c' q) := by rw [hcq]; exact hodq.sub_odd hou
                rw [← sum_eq]
                exact even_split h0 ha hdiff hcond IH hqT hpT hqp heven
              · have hov : Odd v := Int.not_even_iff_odd.mp hve
                have heven : Even (c' p) := by rw [hcp]; exact hodp.add_odd hov
                rw [← sum_eq]
                exact even_split h0 ha hdiff hcond IH hpT hqT hqp.symm heven

snip end

problem usa2004_p2 {n : ℕ} (a : Fin n → ℤ) (S : Set ℤ)
    (hgcd : Finset.univ.gcd a = 1)
    (ha : ∀ i, a i ∈ S)
    (hdiff : ∀ i j, a i - a j ∈ S)
    (hcond : ∀ x y : ℤ, x ∈ S → y ∈ S → x + y ∈ S → x - y ∈ S) :
    S = Set.univ := by
  obtain ⟨c₀, hc₀⟩ := bezout (Finset.univ : Finset (Fin n))
  rw [hgcd] at hc₀
  obtain ⟨i0, _⟩ : (Finset.univ : Finset (Fin n)).Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne, Finset.gcd_empty] at hgcd
    exact zero_ne_one hgcd
  have h0 : (0 : ℤ) ∈ S := by
    have h := hdiff i0 i0
    rwa [sub_self] at h
  have key : ∀ t : ℤ, t ∈ S := by
    intro t
    have h := all_linear_comb h0 ha hdiff hcond Finset.univ (fun i => t * c₀ i)
    have e : ∑ i ∈ Finset.univ, (t * c₀ i) * a i = t * ∑ i ∈ Finset.univ, c₀ i * a i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [e, hc₀, mul_one] at h
    exact h
  exact Set.eq_univ_of_forall key

end Usa2004P2
