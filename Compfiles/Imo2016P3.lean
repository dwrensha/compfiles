/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Data.Int.Star
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.Data.Rat.Star
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Order.CompletePartialOrder
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry, .NumberTheory] }

/-!
# International Mathematical Olympiad 2016, Problem 3

Let P = A₁A₂ ... Aₖ be a convex polygon in the plane. The vertices A₁, A₂, ...,
Aₖ have integral coordinates and lie on a circle. Let S be the area of P. An odd
positive integer n is given such that the squares of the side lengths of P are
integers divisible by n. Prove that 2S is an integer divisible by n.

## Formalization notes

* Twice the (signed) area of a lattice polygon is computed by the shoelace sum
  `shoelace A = ∑ i, cdet (A i) (A (finRotate k i))`; for a convex polygon this
  equals `±2S`, so divisibility of the shoelace sum by `n` is equivalent to
  divisibility of `2S`.
* We prove the stronger statement without any convexity hypothesis: for any
  injective family of integer points lying on a circle *with rational center*
  (no restriction in the interesting case `k ≥ 3`: the center of a circle through
  three non-collinear rational points is rational), if the odd integer `n`
  divides all squared side lengths then `n` divides the shoelace sum.
* The proof follows Jeck Lim's solution (see Evan Chen's IMO 2016 notes):
  induction on the number of vertices; Heron's formula for `k = 3`; for `k ≥ 4`
  one shows that some diagonal has square divisible by `n`, using an inversion
  ("generalized Ptolemy") relation together with linear independence of square
  roots of squarefree integers over `ℚ` (Besicovitch's theorem), and then cuts
  the polygon along that diagonal.
-/

namespace Imo2016P3

snip begin

/-!
### Basic definitions: squared distance, determinant, shoelace sum
-/

/-- Squared distance between two integer points in the plane. -/
def distSq (P Q : ℤ × ℤ) : ℤ := (P.1 - Q.1) ^ 2 + (P.2 - Q.2) ^ 2

/-- The determinant `P.1 * Q.2 - Q.1 * P.2` (twice a signed area). -/
def cdet (P Q : ℤ × ℤ) : ℤ := P.1 * Q.2 - Q.1 * P.2

/-- Twice the signed area of the cyclic polygon on the vertices `A`
(shoelace formula). -/
def shoelace {k : ℕ} (A : Fin k → ℤ × ℤ) : ℤ := ∑ i, cdet (A i) (A (finRotate k i))

lemma cdet_self (P : ℤ × ℤ) : cdet P P = 0 := by simp [cdet]

lemma cdet_comm (P Q : ℤ × ℤ) : cdet Q P = -cdet P Q := by simp only [cdet]; ring

lemma distSq_comm (P Q : ℤ × ℤ) : distSq P Q = distSq Q P := by
  simp only [distSq]; ring

lemma distSq_ne_zero {P Q : ℤ × ℤ} (h : P ≠ Q) : distSq P Q ≠ 0 := by
  intro hz
  apply h
  simp only [distSq] at hz
  have h1 : (P.1 - Q.1) ^ 2 = 0 := by
    nlinarith [sq_nonneg (P.1 - Q.1 : ℤ), sq_nonneg (P.2 - Q.2 : ℤ)]
  have h2 : (P.2 - Q.2) ^ 2 = 0 := by
    nlinarith [sq_nonneg (P.1 - Q.1 : ℤ), sq_nonneg (P.2 - Q.2 : ℤ)]
  have g1 : P.1 = Q.1 := by rwa [sq_eq_zero_iff, sub_eq_zero] at h1
  have g2 : P.2 = Q.2 := by rwa [sq_eq_zero_iff, sub_eq_zero] at h2
  exact Prod.ext g1 g2

lemma shoelace_of_le_two {k : ℕ} (hk : k ≤ 2) (A : Fin k → ℤ × ℤ) : shoelace A = 0 := by
  interval_cases k
  · simp [shoelace]
  · simp only [shoelace, Fin.sum_univ_one]
    rw [finRotate_apply, show (0 : Fin 1) + 1 = 0 by decide, cdet_self]
  · simp only [shoelace, Fin.sum_univ_two, finRotate_apply]
    have h1 : (0 : Fin 2) + 1 = 1 := by decide
    have h2 : (1 : Fin 2) + 1 = 0 := by decide
    rw [h1, h2, cdet_comm (A 1) (A 0)]
    simp

/-!
### Besicovitch: linear independence of square roots of squarefree integers
-/

noncomputable section

/-- The intermediate field of `ℝ` generated over `ℚ` by the square roots of the
elements of a finset `P`. -/
noncomputable def K (P : Finset ℕ) : IntermediateField ℚ ℝ :=
  IntermediateField.adjoin ℚ ((fun p : ℕ => Real.sqrt (p : ℝ)) '' (P : Set ℕ))

theorem sqrt_nat_mem_K {P : Finset ℕ} {r : ℕ} (hr : r ∈ P) :
    Real.sqrt (r : ℝ) ∈ K P :=
  IntermediateField.subset_adjoin _ _ ⟨r, Finset.mem_coe.mpr hr, rfl⟩

theorem intField_coe_eq_zero {L : IntermediateField ℚ ℝ} {x : L} (h : (x : ℝ) = 0) :
    x = 0 := by
  have h' : (x : ℝ) = ((0 : L) : ℝ) := by rw [h]; simp
  exact SetLike.coe_eq_coe.mp h'

/-- If `√q ∉ K P`, then `1, √q` are linearly independent over `K P`. -/
theorem eq_zero_and_eq_zero_of_add_mul_sqrt {P : Finset ℕ} {q : ℕ}
    (hsq_notmem : Real.sqrt (q : ℝ) ∉ K P)
    {a b : ℝ} (ha : a ∈ K P) (hb : b ∈ K P) (h : a + b * Real.sqrt (q : ℝ) = 0) :
    a = 0 ∧ b = 0 := by
  by_cases hb0 : b = 0
  · subst hb0
    simpa using h
  · exfalso
    have e : Real.sqrt (q : ℝ) = -a / b := by
      have e1 : b * Real.sqrt (q : ℝ) = -a := by linarith [h]
      rw [← e1]
      exact (mul_div_cancel_left₀ _ hb0).symm
    exact hsq_notmem (e.symm ▸ div_mem (neg_mem ha) hb)

/-- `√b ∈ K P` whenever all prime factors of `b` lie in `P`. -/
theorem sqrt_mem_K_of_factors {P : Finset ℕ} :
    ∀ b : ℕ, 0 < b → (∀ r : ℕ, r.Prime → r ∣ b → r ∈ P) → Real.sqrt (b : ℝ) ∈ K P := by
  intro b
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    intro hb hfactors
    by_cases hb1 : b = 1
    · rw [hb1, Nat.cast_one, Real.sqrt_one]
      exact one_mem _
    · obtain ⟨r, hrp, hrdvd⟩ := Nat.exists_prime_and_dvd hb1
      have hrpos : 0 < r := hrp.pos
      have hdvd' : b / r ∣ b := ⟨r, by rw [mul_comm]; exact (Nat.mul_div_cancel' hrdvd).symm⟩
      have hfactors' : ∀ r' : ℕ, r'.Prime → r' ∣ b / r → r' ∈ P :=
        fun r' hr'p hr'dvd => hfactors r' hr'p (dvd_trans hr'dvd hdvd')
      have hpos' : 0 < b / r := Nat.div_pos (Nat.le_of_dvd hb hrdvd) hrpos
      have hlt : b / r < b := Nat.div_lt_self hb hrp.one_lt
      have hcast : (b : ℝ) = (r : ℝ) * ((b / r : ℕ) : ℝ) := by
        rw [← Nat.cast_mul, Nat.mul_div_cancel' hrdvd]
      rw [hcast, Real.sqrt_mul (Nat.cast_nonneg r)]
      exact mul_mem (sqrt_nat_mem_K (hfactors r hrp hrdvd)) (ih (b / r) hlt hpos' hfactors')

/-- Every element of `K (insert q P)` has the form `a + b√q` with `a, b ∈ K P`. -/
theorem exists_add_mul_sqrt_of_mem_insert {P : Finset ℕ} (_hP : ∀ p ∈ P, p.Prime)
    {q : ℕ} (_hq : q.Prime) (hqmem : (q : ℝ) ∈ K P)
    (hsq_notmem : Real.sqrt (q : ℝ) ∉ K P)
    {x : ℝ} (hx : x ∈ K (insert q P)) :
    ∃ a b : K P, x = (a : ℝ) + (b : ℝ) * Real.sqrt (q : ℝ) := by
  have e : K (insert q P) = IntermediateField.adjoin ℚ
      (insert (Real.sqrt (q : ℝ)) ((fun p : ℕ => Real.sqrt (p : ℝ)) '' (P : Set ℕ))) := by
    simp only [K, Finset.coe_insert, Set.image_insert_eq]
  rw [e] at hx
  induction hx using IntermediateField.adjoin_induction with
  | mem y hy =>
    rw [Set.mem_insert_iff] at hy
    rcases hy with rfl | hy
    · exact ⟨0, 1, by simp⟩
    · obtain ⟨p, hpP, rfl⟩ := hy
      exact ⟨⟨Real.sqrt (p : ℝ),
        IntermediateField.subset_adjoin _ _ ⟨p, Finset.mem_coe.mpr hpP, rfl⟩⟩, 0, by simp⟩
  | algebraMap y =>
    exact ⟨⟨algebraMap ℚ ℝ y, IntermediateField.algebraMap_mem _ _⟩, 0, by simp⟩
  | add y z _ _ ihy ihz =>
    obtain ⟨a₁, b₁, h₁⟩ := ihy
    obtain ⟨a₂, b₂, h₂⟩ := ihz
    refine ⟨a₁ + a₂, b₁ + b₂, ?_⟩
    rw [h₁, h₂]
    simp only [IntermediateField.coe_add]
    ring
  | mul y z _ _ ihy ihz =>
    obtain ⟨a₁, b₁, h₁⟩ := ihy
    obtain ⟨a₂, b₂, h₂⟩ := ihz
    refine ⟨a₁ * a₂ + ⟨(q : ℝ), hqmem⟩ * (b₁ * b₂), a₁ * b₂ + a₂ * b₁, ?_⟩
    rw [h₁, h₂]
    have hsq2 : Real.sqrt (q : ℝ) * Real.sqrt (q : ℝ) = (q : ℝ) :=
      Real.mul_self_sqrt (Nat.cast_nonneg q)
    have hqq : ((⟨(q : ℝ), hqmem⟩ : K P) : ℝ) = (q : ℝ) := rfl
    simp only [IntermediateField.coe_add, IntermediateField.coe_mul]
    linear_combination (↑b₁ * ↑b₂ : ℝ) * hsq2
  | inv y _ ihy =>
    obtain ⟨a₁, b₁, h₁⟩ := ihy
    by_cases hb : b₁ = 0
    · subst hb
      refine ⟨a₁⁻¹, 0, ?_⟩
      rw [h₁]
      simp
    · have hb1ne : (b₁ : ℝ) ≠ 0 := fun e => hb (intField_coe_eq_zero e)
      have hne : (a₁ : ℝ) ^ 2 - (q : ℝ) * (b₁ : ℝ) ^ 2 ≠ 0 := by
        intro hz
        have hsq2pow : (Real.sqrt (q : ℝ)) ^ 2 = (q : ℝ) := Real.sq_sqrt (Nat.cast_nonneg q)
        have h1 : (a₁ : ℝ) ^ 2 = ((b₁ : ℝ) * Real.sqrt (q : ℝ)) ^ 2 := by
          have e := sub_eq_zero.mp hz
          rw [e, mul_pow, hsq2pow]
          ring
        rcases sq_eq_sq_iff_eq_or_eq_neg.mp h1 with h2 | h2
        · have e : Real.sqrt (q : ℝ) = ((a₁ / b₁ : K P) : ℝ) := by
            rw [IntermediateField.coe_div, h2]
            exact (mul_div_cancel_left₀ _ hb1ne).symm
          exact hsq_notmem (e.symm ▸ (a₁ / b₁ : K P).2)
        · have e : Real.sqrt (q : ℝ) = ((-a₁ / b₁ : K P) : ℝ) := by
            rw [IntermediateField.coe_div, IntermediateField.coe_neg, h2, neg_neg]
            exact (mul_div_cancel_left₀ _ hb1ne).symm
          exact hsq_notmem (e.symm ▸ (-a₁ / b₁ : K P).2)
      have hDmem : (a₁ : ℝ) ^ 2 - (q : ℝ) * (b₁ : ℝ) ^ 2 ∈ K P :=
        sub_mem (pow_mem a₁.2 2) (mul_mem hqmem (pow_mem b₁.2 2))
      have hmul : ((a₁ : ℝ) + (b₁ : ℝ) * Real.sqrt (q : ℝ)) *
          ((a₁ : ℝ) / ((a₁ : ℝ) ^ 2 - (q : ℝ) * (b₁ : ℝ) ^ 2) +
            (-(b₁ : ℝ)) / ((a₁ : ℝ) ^ 2 - (q : ℝ) * (b₁ : ℝ) ^ 2) * Real.sqrt (q : ℝ)) = 1 := by
        have hsq2pow : (Real.sqrt (q : ℝ)) ^ 2 = (q : ℝ) := Real.sq_sqrt (Nat.cast_nonneg q)
        have hD' : ((a₁ : ℝ) + (b₁ : ℝ) * Real.sqrt (q : ℝ)) *
            ((a₁ : ℝ) - (b₁ : ℝ) * Real.sqrt (q : ℝ)) =
            (a₁ : ℝ) ^ 2 - (q : ℝ) * (b₁ : ℝ) ^ 2 := by
          linear_combination -(↑b₁ ^ 2 : ℝ) * hsq2pow
        have e : (a₁ : ℝ) / ((a₁ : ℝ) ^ 2 - (q : ℝ) * (b₁ : ℝ) ^ 2) +
            (-(b₁ : ℝ)) / ((a₁ : ℝ) ^ 2 - (q : ℝ) * (b₁ : ℝ) ^ 2) * Real.sqrt (q : ℝ) =
            ((a₁ : ℝ) - (b₁ : ℝ) * Real.sqrt (q : ℝ)) /
              ((a₁ : ℝ) ^ 2 - (q : ℝ) * (b₁ : ℝ) ^ 2) := by
          rw [div_mul_eq_mul_div, ← add_div]
          congr 1
          ring
        rw [e, ← mul_div_assoc, div_eq_one_iff_eq hne]
        exact hD'
      refine ⟨a₁ / ⟨(a₁ : ℝ) ^ 2 - (q : ℝ) * (b₁ : ℝ) ^ 2, hDmem⟩,
        (-b₁) / ⟨(a₁ : ℝ) ^ 2 - (q : ℝ) * (b₁ : ℝ) ^ 2, hDmem⟩, ?_⟩
      rw [h₁]
      simp only [IntermediateField.coe_div, IntermediateField.coe_neg]
      have hinv := eq_inv_of_mul_eq_one_left hmul
      rw [hinv, inv_inv]

/-- Besicovitch's property Q: if `d` is squarefree and `√d ∈ K P`, then all prime
factors of `d` lie in `P`. -/
theorem Q_of (P : Finset ℕ) :
    (∀ p ∈ P, p.Prime) →
    ∀ d : ℕ, Squarefree d → 0 < d → Real.sqrt (d : ℝ) ∈ K P →
      ∀ q : ℕ, q.Prime → q ∣ d → q ∈ P := by
  induction P using Finset.induction with
  | empty =>
    intro _ d hdsq hdpos hdmem q hq hqd
    have hK : K ∅ = ⊥ := by
      simp only [K, Finset.coe_empty, Set.image_empty, IntermediateField.adjoin_empty]
    rw [hK, IntermediateField.mem_bot] at hdmem
    obtain ⟨c, hc⟩ := hdmem
    have hc' : (c : ℝ) = Real.sqrt (d : ℝ) := by
      rw [← hc]; exact (eq_ratCast _ _).symm
    have hirr : ¬ Irrational (Real.sqrt (d : ℝ)) := fun h => h ⟨c, hc'⟩
    rw [irrational_sqrt_natCast_iff, not_not] at hirr
    obtain ⟨m, hm⟩ := hirr
    have hunit : IsUnit m := hdsq m ⟨1, by rw [mul_one]; exact hm⟩
    have hm1 : m = 1 := Nat.isUnit_iff.mp hunit
    have hd1 : d = 1 := by rw [hm, hm1, mul_one]
    rw [hd1] at hqd
    exact absurd (Nat.dvd_one.mp hqd) hq.ne_one
  | insert q P' hqP' ih =>
    intro hP d hdsq hdpos hdmem r hr hdr
    have hq : q.Prime := hP q (Finset.mem_insert_self q P')
    have hP' : ∀ p ∈ P', p.Prime := fun p hp => hP p (Finset.mem_insert_of_mem hp)
    have ih' := ih hP'
    have hqpos : 0 < q := hq.pos
    have hsqq : Squarefree q := (Nat.prime_iff.mp hq).squarefree
    have hsq_notmem : Real.sqrt (q : ℝ) ∉ K P' := fun h =>
      hqP' (ih' q hsqq hqpos h q hq (dvd_refl q))
    have hqmem : (q : ℝ) ∈ K P' := by
      have h1 := IntermediateField.algebraMap_mem (K P') (q : ℚ)
      rwa [eq_ratCast, Rat.cast_natCast] at h1
    obtain ⟨a, b, hab⟩ := exists_add_mul_sqrt_of_mem_insert hP' hq hqmem hsq_notmem hdmem
    have hkey : ((a : ℝ) + (b : ℝ) * Real.sqrt (q : ℝ)) *
        ((a : ℝ) + (b : ℝ) * Real.sqrt (q : ℝ)) = (d : ℝ) := by
      rw [← hab]
      exact Real.mul_self_sqrt (Nat.cast_nonneg d)
    have hsq2pow : (Real.sqrt (q : ℝ)) ^ 2 = (q : ℝ) := Real.sq_sqrt (Nat.cast_nonneg q)
    have hexp : ((a : ℝ) ^ 2 + (q : ℝ) * (b : ℝ) ^ 2 - (d : ℝ)) +
        ((2 : ℝ) * (a : ℝ) * (b : ℝ)) * Real.sqrt (q : ℝ) = 0 := by
      linear_combination hkey - (↑b ^ 2 : ℝ) * hsq2pow
    have hdmem' : (d : ℝ) ∈ K P' := by
      have h := IntermediateField.algebraMap_mem (K P') (d : ℚ)
      rwa [eq_ratCast, Rat.cast_natCast] at h
    have h2mem : (2 : ℝ) ∈ K P' := by
      have h := IntermediateField.algebraMap_mem (K P') (2 : ℚ)
      rwa [eq_ratCast, Rat.cast_ofNat] at h
    obtain ⟨_, h2ab⟩ := eq_zero_and_eq_zero_of_add_mul_sqrt hsq_notmem
      (sub_mem (add_mem (pow_mem a.2 2) (mul_mem hqmem (pow_mem b.2 2))) hdmem')
      (mul_mem (mul_mem h2mem a.2) b.2) hexp
    have h2ab' : (a : ℝ) * (b : ℝ) = 0 := by
      have e : (2 : ℝ) * ((a : ℝ) * (b : ℝ)) = (2 : ℝ) * 0 := by
        rw [mul_zero]; linear_combination h2ab
      exact mul_left_cancel₀ (by norm_num : (2 : ℝ) ≠ 0) e
    rcases mul_eq_zero.mp h2ab' with ha0 | hb0
    · -- case `a = 0`: then `d = q * b²`
      have hdq : (d : ℝ) = (q : ℝ) * (b : ℝ) ^ 2 := by
        rw [ha0, zero_add] at hkey
        linear_combination -hkey + (↑b ^ 2 : ℝ) * hsq2pow
      by_cases hqdiv : q ∣ d
      · -- `d = q * d'`; then `√d' ∈ K P'`
        obtain ⟨d', hd'⟩ := hqdiv
        have hd'pos : 0 < d' := by
          by_contra hc0
          rw [Nat.eq_zero_of_not_pos hc0, mul_zero] at hd'
          omega
        have hd'sq : Squarefree d' :=
          Squarefree.squarefree_of_dvd ⟨q, by rw [mul_comm]; exact hd'⟩ hdsq
        have hcast : (d : ℝ) = (q : ℝ) * ((d' : ℕ) : ℝ) := by rw [hd']; norm_cast
        have hbd : (b : ℝ) ^ 2 = ((d' : ℕ) : ℝ) :=
          mul_left_cancel₀ (show (q : ℝ) ≠ 0 from Nat.cast_ne_zero.mpr hqpos.ne')
            (by rw [← hdq, ← hcast])
        have hbsq : (b : ℝ) = Real.sqrt ((d' : ℕ) : ℝ) ∨
            (b : ℝ) = -Real.sqrt ((d' : ℕ) : ℝ) := by
          have h2 : (b : ℝ) ^ 2 = (Real.sqrt ((d' : ℕ) : ℝ)) ^ 2 := by
            rw [hbd, Real.sq_sqrt (Nat.cast_nonneg d')]
          exact sq_eq_sq_iff_eq_or_eq_neg.mp h2
        have hd'mem : Real.sqrt ((d' : ℕ) : ℝ) ∈ K P' := by
          rcases hbsq with h | h
          · rw [← h]; exact b.2
          · have e : Real.sqrt ((d' : ℕ) : ℝ) = ((-b : K P') : ℝ) := by
              rw [IntermediateField.coe_neg, h, neg_neg]
            rw [e]; exact (-b).2
        have hfact := ih' d' hd'sq hd'pos hd'mem
        rw [hd'] at hdr
        rcases hr.dvd_mul.mp hdr with hrdq | hrdd'
        · have hrq : r = q :=
            (prime_dvd_prime_iff_eq (Nat.prime_iff.mp hr) (Nat.prime_iff.mp hq)).mp hrdq
          rw [hrq]
          exact Finset.mem_insert_self q P'
        · exact Finset.mem_insert_of_mem (hfact r hr hrdd')
      · -- `q ∤ d`: then `d * q` is squarefree and `√(d*q) ∈ K P'`, contradiction
        have hcop : Nat.Coprime d q := ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqdiv).symm
        have hdqsq : Squarefree (d * q) := (Nat.squarefree_mul hcop).mpr ⟨hdsq, hsqq⟩
        have hdqpos : 0 < d * q := Nat.mul_pos hdpos hqpos
        have hmem2 : Real.sqrt ((d * q : ℕ) : ℝ) ∈ K P' := by
          have h3 : (Real.sqrt ((d * q : ℕ) : ℝ)) ^ 2 = ((b : ℝ) * (q : ℝ)) ^ 2 := by
            rw [Real.sq_sqrt (Nat.cast_nonneg _), Nat.cast_mul]
            linear_combination (q : ℝ) * hdq
          rcases sq_eq_sq_iff_eq_or_eq_neg.mp h3 with h | h
          · have e : Real.sqrt ((d * q : ℕ) : ℝ) = ((b * ⟨(q : ℝ), hqmem⟩ : K P') : ℝ) := by
              rw [IntermediateField.coe_mul]
              exact h
            rw [e]; exact (b * _).2
          · have e : Real.sqrt ((d * q : ℕ) : ℝ) = ((-(b * ⟨(q : ℝ), hqmem⟩) : K P') : ℝ) := by
              rw [IntermediateField.coe_neg, IntermediateField.coe_mul]
              exact h
            rw [e]; exact (-(b * _)).2
        exact absurd (ih' (d * q) hdqsq hdqpos hmem2 q hq (dvd_mul_left q d)) hqP'
    · -- case `b = 0`: then `√d = a ∈ K P'`
      have hdmem2 : Real.sqrt (d : ℝ) ∈ K P' := by
        have e : Real.sqrt (d : ℝ) = (a : ℝ) := by rw [hab, hb0, zero_mul, add_zero]
        rw [e]; exact a.2
      exact Finset.mem_insert_of_mem (ih' d hdsq hdpos hdmem2 r hr hdr)

/-- Besicovitch linear independence over a fixed finset of primes. -/
theorem LI_of (P : Finset ℕ) :
    (∀ p ∈ P, p.Prime) →
    ∀ B : Finset ℕ, (∀ b ∈ B, Squarefree b ∧ 0 < b) →
      (∀ b ∈ B, ∀ r : ℕ, r.Prime → r ∣ b → r ∈ P) →
      ∀ C : ℕ → ℚ, ∑ b ∈ B, (C b : ℝ) * Real.sqrt (b : ℝ) = 0 → ∀ b ∈ B, C b = 0 := by
  induction P using Finset.induction with
  | empty =>
    intro _ B hB hfactors C hsum
    have hB1 : ∀ b ∈ B, b = 1 := by
      intro b hb
      obtain ⟨hsqb, hbpos⟩ := hB b hb
      by_contra hb1
      obtain ⟨r, hrp, hrdvd⟩ := Nat.exists_prime_and_dvd hb1
      exact absurd (hfactors b hb r hrp hrdvd) (by simp)
    have hsub : B ⊆ {1} := fun b hb => Finset.mem_singleton.mpr (hB1 b hb)
    rw [Finset.subset_singleton_iff] at hsub
    rcases hsub with rfl | rfl
    · intro b hb; simp at hb
    · intro b hb
      have hb1 : b = 1 := Finset.mem_singleton.mp hb
      subst hb1
      have h0 : (C 1 : ℝ) = 0 := by simpa using hsum
      exact_mod_cast h0
  | insert q P' hqP' ih =>
    intro hP B hB hfactors C hsum
    have hq : q.Prime := hP q (Finset.mem_insert_self q P')
    have hP' : ∀ p ∈ P', p.Prime := fun p hp => hP p (Finset.mem_insert_of_mem hp)
    have hqpos : 0 < q := hq.pos
    have hsqq : Squarefree q := (Nat.prime_iff.mp hq).squarefree
    have hsq_notmem : Real.sqrt (q : ℝ) ∉ K P' := fun h =>
      hqP' (Q_of P' hP' q hsqq hqpos h q hq (dvd_refl q))
    set B₀ := B.filter (fun b => ¬ q ∣ b) with hB₀
    set B₁ := B.filter (fun b => q ∣ b) with hB₁
    have hB₀' : ∀ b ∈ B₀, Squarefree b ∧ 0 < b := by
      intro b hb
      rw [hB₀] at hb
      exact hB b ((Finset.mem_filter.mp hb).1)
    have hfac₀ : ∀ b ∈ B₀, ∀ r : ℕ, r.Prime → r ∣ b → r ∈ P' := by
      intro b hb r hr hrdvd
      rw [hB₀] at hb
      have hbB : b ∈ B := (Finset.mem_filter.mp hb).1
      have hrP := hfactors b hbB r hr hrdvd
      have hrne : r ≠ q := by
        intro hrq
        rw [hrq] at hrdvd
        exact (Finset.mem_filter.mp hb).2 hrdvd
      exact Finset.mem_of_mem_insert_of_ne hrP hrne
    have hdivdvd : ∀ b ∈ B₁, b / q ∣ b := by
      intro b hb
      rw [hB₁] at hb
      exact ⟨q, by rw [mul_comm]; exact (Nat.mul_div_cancel' (Finset.mem_filter.mp hb).2).symm⟩
    have hfac₁ : ∀ b ∈ B₁, ∀ r : ℕ, r.Prime → r ∣ b / q → r ∈ P' := by
      intro b hb r hr hrdvd
      have hb' := hdivdvd b hb
      rw [hB₁] at hb
      have hbB : b ∈ B := (Finset.mem_filter.mp hb).1
      have hbq : q ∣ b := (Finset.mem_filter.mp hb).2
      have hrP := hfactors b hbB r hr (dvd_trans hrdvd hb')
      have hrne : r ≠ q := by
        intro hrq
        rw [hrq] at hrdvd
        obtain ⟨hsqb, _⟩ := hB b hbB
        have hqq : q * q ∣ b := by
          obtain ⟨c, hc⟩ := hrdvd
          exact ⟨c, by rw [← Nat.mul_div_cancel' hbq, hc]; ring⟩
        have hu : IsUnit q := hsqb q hqq
        exact hq.ne_one (Nat.isUnit_iff.mp hu)
      exact Finset.mem_of_mem_insert_of_ne hrP hrne
    have hpos₁ : ∀ b ∈ B₁, 0 < b / q := by
      intro b hb
      rw [hB₁] at hb
      have hbB : b ∈ B := (Finset.mem_filter.mp hb).1
      exact Nat.div_pos (Nat.le_of_dvd (hB b hbB).2 (Finset.mem_filter.mp hb).2) hqpos
    have hCmem : ∀ b : ℕ, (C b : ℝ) ∈ K P' := fun b => by
      have h := IntermediateField.algebraMap_mem (K P') (C b)
      rwa [eq_ratCast] at h
    have hterm : ∀ b ∈ B₁, (C b : ℝ) * Real.sqrt (b : ℝ) =
        Real.sqrt (q : ℝ) * ((C b : ℝ) * Real.sqrt ((b / q : ℕ) : ℝ)) := by
      intro b hb
      rw [hB₁] at hb
      have hbq : q ∣ b := (Finset.mem_filter.mp hb).2
      have hcast : (b : ℝ) = (q : ℝ) * ((b / q : ℕ) : ℝ) := by
        rw [← Nat.cast_mul, Nat.mul_div_cancel' hbq]
      rw [hcast, Real.sqrt_mul (Nat.cast_nonneg q)]
      ring
    have h1 : (∑ b ∈ B, (C b : ℝ) * Real.sqrt (b : ℝ)) =
        (∑ b ∈ B₁, (C b : ℝ) * Real.sqrt (b : ℝ)) +
          (∑ b ∈ B₀, (C b : ℝ) * Real.sqrt (b : ℝ)) := by
      rw [hB₀, hB₁]
      exact (Finset.sum_filter_add_sum_filter_not B (fun b => q ∣ b) _).symm
    have h2 : (∑ b ∈ B₁, (C b : ℝ) * Real.sqrt (b : ℝ)) =
        Real.sqrt (q : ℝ) * (∑ b ∈ B₁, (C b : ℝ) * Real.sqrt ((b / q : ℕ) : ℝ)) := by
      rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    have hsplit : (∑ b ∈ B₀, (C b : ℝ) * Real.sqrt (b : ℝ)) +
        Real.sqrt (q : ℝ) * (∑ b ∈ B₁, (C b : ℝ) * Real.sqrt ((b / q : ℕ) : ℝ)) = 0 := by
      rw [h1, h2] at hsum
      rw [add_comm] at hsum
      exact hsum
    have hS₀ : (∑ b ∈ B₀, (C b : ℝ) * Real.sqrt (b : ℝ)) ∈ K P' := by
      apply sum_mem
      intro b hb
      have hb0 := hb
      rw [hB₀] at hb
      exact mul_mem (hCmem b)
        (sqrt_mem_K_of_factors b (hB₀' b hb0).2 (hfac₀ b hb0))
    have hS₁ : (∑ b ∈ B₁, (C b : ℝ) * Real.sqrt ((b / q : ℕ) : ℝ)) ∈ K P' := by
      apply sum_mem
      intro b hb
      have hb0 := hb
      rw [hB₁] at hb
      exact mul_mem (hCmem b)
        (sqrt_mem_K_of_factors (b / q) (hpos₁ b hb0) (hfac₁ b hb0))
    obtain ⟨hS₀z, hS₁z⟩ := eq_zero_and_eq_zero_of_add_mul_sqrt hsq_notmem hS₀ hS₁
      (by rw [mul_comm]; exact hsplit)
    have hC₀ : ∀ b ∈ B₀, C b = 0 := ih hP' B₀ hB₀' hfac₀ C hS₀z
    set B₁' := B₁.image (· / q) with hB₁''
    have hinj : ∀ x ∈ B₁, ∀ y ∈ B₁, x / q = y / q → x = y := by
      intro x hx y hy hxy
      rw [hB₁] at hx hy
      have hxq : q ∣ x := (Finset.mem_filter.mp hx).2
      have hyq : q ∣ y := (Finset.mem_filter.mp hy).2
      rw [← Nat.mul_div_cancel' hxq, ← Nat.mul_div_cancel' hyq, hxy]
    have hB₁' : ∀ b ∈ B₁', Squarefree b ∧ 0 < b := by
      intro b hb
      rw [hB₁''] at hb
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hb
      have hxB : x ∈ B := (Finset.mem_filter.mp hx).1
      exact ⟨Squarefree.squarefree_of_dvd (hdivdvd x hx) (hB x hxB).1, hpos₁ x hx⟩
    have hfac₁' : ∀ b ∈ B₁', ∀ r : ℕ, r.Prime → r ∣ b → r ∈ P' := by
      intro b hb r hr hrdvd
      rw [hB₁''] at hb
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hb
      exact hfac₁ x hx r hr hrdvd
    have hsum' : ∑ b ∈ B₁', (C (q * b) : ℝ) * Real.sqrt (b : ℝ) = 0 := by
      rw [hB₁'', Finset.sum_image hinj]
      have e : ∀ x ∈ B₁, (C (q * (x / q)) : ℝ) * Real.sqrt ((x / q : ℕ) : ℝ) =
          (C x : ℝ) * Real.sqrt ((x / q : ℕ) : ℝ) := by
        intro x hx
        rw [Nat.mul_div_cancel' (Finset.mem_filter.mp hx).2]
      rw [Finset.sum_congr rfl e]
      exact hS₁z
    have hC₁ : ∀ b ∈ B₁', C (q * b) = 0 := ih hP' B₁' hB₁' hfac₁' _ hsum'
    intro b hb
    by_cases hqdiv : q ∣ b
    · have hb1 : b ∈ B₁ := Finset.mem_filter.mpr ⟨hb, hqdiv⟩
      have h1 : b / q ∈ B₁' := by rw [hB₁'']; exact Finset.mem_image_of_mem (· / q) hb1
      have h2 := hC₁ (b / q) h1
      rwa [Nat.mul_div_cancel' hqdiv] at h2
    · exact hC₀ b (Finset.mem_filter.mpr ⟨hb, hqdiv⟩)

theorem linearIndependent_real_sqrt {ι : Type*} [Fintype ι] {b : ι → ℕ}
    (hb : Function.Injective b) (hsq : ∀ i, Squarefree (b i)) (hpos : ∀ i, 0 < b i) :
    LinearIndependent ℚ (fun i => Real.sqrt (b i) : ι → ℝ) := by
  classical
  rw [linearIndependent_iff']
  intro s g hsum
  set P : Finset ℕ := s.biUnion (fun i => (b i).primeFactors) with hP
  have hPprime : ∀ p ∈ P, p.Prime := by
    intro p hp
    rw [hP, Finset.mem_biUnion] at hp
    obtain ⟨i, _, hpi⟩ := hp
    exact (Nat.mem_primeFactors.mp hpi).1
  set B : Finset ℕ := s.image b with hB
  have hBsq : ∀ x ∈ B, Squarefree x ∧ 0 < x := by
    intro x hx
    rw [hB] at hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨hsq i, hpos i⟩
  have hfactors : ∀ x ∈ B, ∀ r : ℕ, r.Prime → r ∣ x → r ∈ P := by
    intro x hx r hr hrdvd
    rw [hB] at hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    rw [hP, Finset.mem_biUnion]
    exact ⟨i, hi, hr.mem_primeFactors hrdvd (Nat.pos_iff_ne_zero.mp (hpos i))⟩
  set C : ℕ → ℚ := fun x => if h : ∃ i ∈ s, b i = x then g (Classical.choose h) else 0 with hC
  have hCb : ∀ i ∈ s, C (b i) = g i := by
    intro i hi
    have h1 : ∃ j ∈ s, b j = b i := ⟨i, hi, rfl⟩
    simp only [hC, dif_pos h1]
    have h2 := (Classical.choose_spec h1).2
    have h3 : Classical.choose h1 = i := hb h2
    rw [h3]
  have hsum3 : ∑ x ∈ B, (C x : ℝ) * Real.sqrt (x : ℝ) = 0 := by
    rw [hB, Finset.sum_image (fun i _ j _ h => hb h)]
    have e : ∀ i ∈ s, (C (b i) : ℝ) * Real.sqrt ((b i : ℕ) : ℝ) =
        g i • Real.sqrt ((b i : ℕ) : ℝ) := by
      intro i hi
      rw [hCb i hi, Algebra.smul_def, eq_ratCast]
    rw [Finset.sum_congr rfl e]
    exact hsum
  have hvanish : ∀ x ∈ B, C x = 0 := LI_of P hPprime B hBsq hfactors C hsum3
  intro i hi
  have h1 : b i ∈ B := by rw [hB]; exact Finset.mem_image_of_mem b hi
  have h2 := hvanish (b i) h1
  rwa [hCb i hi] at h2

/-- Every positive natural number is a square times a squarefree number. -/
theorem exists_sq_mul_squarefree :
    ∀ w : ℕ, 0 < w → ∃ c k : ℕ, 0 < c ∧ 0 < k ∧ Squarefree k ∧ w = c ^ 2 * k := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hsq : Squarefree w
    · exact ⟨1, w, one_pos, hw, hsq, by rw [one_pow, one_mul]⟩
    · have hsq' : ∃ x, x * x ∣ w ∧ ¬ IsUnit x := by
        by_contra hcon
        apply hsq
        intro x hx
        by_contra hunit
        exact hcon ⟨x, hx, hunit⟩
      obtain ⟨x, hxx, hx⟩ := hsq'
      have hx0 : x ≠ 0 := by
        rintro rfl
        rw [zero_mul, zero_dvd_iff] at hxx
        omega
      have hx1 : x ≠ 1 := by
        rintro rfl
        exact hx isUnit_one
      have hx2 : 2 ≤ x := by omega
      have hx2dvd : x ^ 2 ∣ w := by rw [pow_two]; exact hxx
      have hpos' : 0 < w / x ^ 2 :=
        Nat.div_pos (Nat.le_of_dvd hw hx2dvd) (pow_pos (by omega : 0 < x) 2)
      have hlt : w / x ^ 2 < w := Nat.div_lt_self hw (by nlinarith [hx2])
      obtain ⟨c, k, hc, hk, hksq, hck⟩ := ih (w / x ^ 2) hlt hpos'
      refine ⟨x * c, k, Nat.mul_pos (by omega) hc, hk, hksq, ?_⟩
      have e : w = x ^ 2 * (w / x ^ 2) := (Nat.mul_div_cancel' hx2dvd).symm
      rw [e, hck]
      ring

/-- A sum of rationals each of positive `p`-adic valuation has positive valuation. -/
theorem one_le_padicValRat_sum {p : ℕ} (hp : p.Prime) {ι : Type*} {s : Finset ι} {f : ι → ℚ}
    (hsum : ∑ i ∈ s, f i ≠ 0) (hf : ∀ i ∈ s, 1 ≤ padicValRat p (f i)) :
    1 ≤ padicValRat p (∑ i ∈ s, f i) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  induction s using Finset.induction with
  | empty => exact absurd rfl hsum
  | insert a s has ih =>
    rw [Finset.sum_insert has] at hsum ⊢
    by_cases hs : ∑ i ∈ s, f i = 0
    · rw [hs, add_zero]
      exact hf a (Finset.mem_insert_self a s)
    · have h1 := hf a (Finset.mem_insert_self a s)
      have h2 := ih hs (fun i hi => hf i (Finset.mem_insert_of_mem hi))
      have h3 := padicValRat.min_le_padicValRat_add (p := p) hsum
      exact le_trans (le_min h1 h2) h3

theorem sum_signed_sqrt_ne_one_of_padicValRat {p : ℕ} (hp : p.Prime) {t : ℕ}
    {r : Fin t → ℚ} (hr : ∀ i, 0 < r i) (hval : ∀ i, 1 ≤ padicValRat p (r i))
    {ε : Fin t → ℤ} (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) :
    (∑ i, (ε i : ℝ) * Real.sqrt (r i : ℝ)) ≠ (σ : ℝ) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  intro hsum
  have hexists : ∀ i : Fin t, ∃ c k : ℕ, 0 < c ∧ 0 < k ∧ Squarefree k ∧
      ((r i).num.natAbs * (r i).den = c ^ 2 * k) ∧
      Real.sqrt (r i : ℝ) = (c : ℝ) / ((r i).den : ℝ) * Real.sqrt (k : ℝ) := by
    intro i
    have hvpos : 0 < (r i).den := (r i).den_pos
    have hunpos : 0 < (r i).num.natAbs := by
      rw [Int.natAbs_pos]
      exact ne_of_gt (Rat.num_pos.mpr (hr i))
    obtain ⟨c, k, hcpos, hkpos, hksq, hw⟩ :=
      exists_sq_mul_squarefree ((r i).num.natAbs * (r i).den) (Nat.mul_pos hunpos hvpos)
    refine ⟨c, k, hcpos, hkpos, hksq, hw, ?_⟩
    have hnum : (((r i).num.natAbs : ℕ) : ℝ) = ((r i).num : ℝ) := by
      have e : ((r i).num.natAbs : ℤ) = (r i).num :=
        Int.natAbs_of_nonneg (le_of_lt (Rat.num_pos.mpr (hr i)))
      have e2 : (((r i).num.natAbs : ℕ) : ℝ) = (((r i).num.natAbs : ℤ) : ℝ) :=
        (Int.cast_natCast _).symm
      rw [e2, e]
    have hri : (r i : ℝ) = (((r i).num.natAbs : ℕ) : ℝ) / ((r i).den : ℝ) := by
      rw [Rat.cast_def, ← hnum]
    have hvne : ((r i).den : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hvpos)
    have e1 : (((r i).num.natAbs : ℕ) : ℝ) / ((r i).den : ℝ) =
        (((r i).num.natAbs * (r i).den : ℕ) : ℝ) / (((r i).den : ℝ) * ((r i).den : ℝ)) := by
      rw [Nat.cast_mul]
      exact (mul_div_mul_right _ _ hvne).symm
    have e2 : (((r i).num.natAbs * (r i).den : ℕ) : ℝ) = (c : ℝ) ^ 2 * (k : ℝ) := by
      norm_cast
    rw [hri, e1, e2,
      Real.sqrt_div (mul_nonneg (sq_nonneg (c : ℝ)) (Nat.cast_nonneg k)),
      Real.sqrt_mul (sq_nonneg (c : ℝ)), Real.sqrt_sq (Nat.cast_nonneg c),
      Real.sqrt_mul_self (Nat.cast_nonneg (r i).den)]
    ring
  choose c k hcpos hkpos hksq hw hsqrtid using hexists
  set f : Fin t → ℚ := fun i => (ε i : ℚ) * ((c i : ℚ) / ((r i).den : ℚ)) with hf
  set A : ℕ → ℚ := fun j => ∑ i ∈ Finset.univ.filter (fun i => k i = j), f i with hA
  set B : Finset ℕ := Finset.univ.image k with hB
  have hσeq : (σ : ℝ) = ∑ j ∈ B, (A j : ℝ) * Real.sqrt (j : ℝ) := by
    rw [← hsum]
    have step1 : (∑ i, (ε i : ℝ) * Real.sqrt (r i : ℝ)) =
        ∑ i, ((f i : ℚ) : ℝ) * Real.sqrt ((k i : ℕ) : ℝ) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hsqrtid i]
      simp only [hf, Rat.cast_mul, Rat.cast_intCast, Rat.cast_div, Rat.cast_natCast]
      ring
    rw [step1]
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := B)
      (fun i _ => by rw [hB]; exact Finset.mem_image_of_mem k (Finset.mem_univ i))
      (fun i => ((f i : ℚ) : ℝ) * Real.sqrt ((k i : ℕ) : ℝ))]
    apply Finset.sum_congr rfl
    intro j _
    have e1 : (∑ i ∈ Finset.univ.filter (fun i => k i = j), ((f i : ℚ) : ℝ) *
        Real.sqrt ((k i : ℕ) : ℝ)) =
        (∑ i ∈ Finset.univ.filter (fun i => k i = j), ((f i : ℚ) : ℝ)) *
          Real.sqrt (j : ℝ) := by
      have e' : ∀ i ∈ Finset.univ.filter (fun i => k i = j),
          ((f i : ℚ) : ℝ) * Real.sqrt ((k i : ℕ) : ℝ) =
            ((f i : ℚ) : ℝ) * Real.sqrt (j : ℝ) := by
        intro i hi
        rw [(Finset.mem_filter.mp hi).2]
      rw [Finset.sum_congr rfl e', ← Finset.sum_mul]
    have e2 : (∑ i ∈ Finset.univ.filter (fun i => k i = j), ((f i : ℚ) : ℝ)) =
        ((A j : ℚ) : ℝ) := by
      simp only [hA]
      push_cast
      rfl
    rw [e1, e2]
  have hAout : ∀ j : ℕ, j ∉ B → A j = 0 := by
    intro j hj
    have he : Finset.univ.filter (fun i => k i = j) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro i _ hki
      apply hj
      rw [hB]
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hki⟩
    simp only [hA, he, Finset.sum_empty]
  set D : ℕ → ℚ := fun j => A j - (if j = 1 then (σ : ℚ) else 0) with hD
  have hvan : ∑ j ∈ insert 1 B, (D j : ℝ) * Real.sqrt (j : ℝ) = 0 := by
    have esplit : ∀ j : ℕ, j ∈ insert 1 B → ((D j : ℚ) : ℝ) * Real.sqrt (j : ℝ) =
        (A j : ℝ) * Real.sqrt (j : ℝ) -
          ((if j = 1 then (σ : ℚ) else 0 : ℚ) : ℝ) * Real.sqrt (j : ℝ) := by
      intro j _
      simp only [hD]
      push_cast
      ring
    rw [Finset.sum_congr rfl esplit, Finset.sum_sub_distrib]
    have e2 : ∑ j ∈ insert 1 B,
        ((if j = 1 then (σ : ℚ) else 0 : ℚ) : ℝ) * Real.sqrt (j : ℝ) = (σ : ℝ) := by
      have e2' : ∀ j : ℕ, j ∈ insert 1 B →
          ((if j = 1 then (σ : ℚ) else 0 : ℚ) : ℝ) * Real.sqrt (j : ℝ) =
          if j = 1 then (σ : ℝ) * Real.sqrt (j : ℝ) else 0 := by
        intro j _
        split <;> simp
      rw [Finset.sum_congr rfl e2', Finset.sum_ite_eq', if_pos (Finset.mem_insert_self 1 B),
        Nat.cast_one, Real.sqrt_one, mul_one]
    rw [e2]
    have e3 : ∑ j ∈ B, (A j : ℝ) * Real.sqrt (j : ℝ) =
        ∑ j ∈ insert 1 B, (A j : ℝ) * Real.sqrt (j : ℝ) := by
      apply Finset.sum_subset (Finset.subset_insert 1 B)
      intro j hj1 hj2
      have hj : j = 1 := by
        rcases Finset.mem_insert.mp hj1 with rfl | h
        · rfl
        · exact absurd h hj2
      have hj2' : 1 ∉ B := hj ▸ hj2
      rw [hj, hAout 1 hj2', Rat.cast_zero, zero_mul]
    rw [← e3, ← hσeq]
    exact sub_self (σ : ℝ)
  set P : Finset ℕ := (insert 1 B).biUnion Nat.primeFactors with hP
  have hPprime : ∀ q ∈ P, q.Prime := by
    intro q hq
    rw [hP, Finset.mem_biUnion] at hq
    obtain ⟨j, _, hqj⟩ := hq
    exact (Nat.mem_primeFactors.mp hqj).1
  have hB1sq : ∀ j ∈ insert 1 B, Squarefree j ∧ 0 < j := by
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact ⟨squarefree_one, one_pos⟩
    · rw [hB] at hj
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hj
      exact ⟨hksq i, hkpos i⟩
  have hfactors : ∀ j ∈ insert 1 B, ∀ q : ℕ, q.Prime → q ∣ j → q ∈ P := by
    intro j hj q hq hqj
    rw [hP, Finset.mem_biUnion]
    exact ⟨j, hj, hq.mem_primeFactors hqj (Nat.pos_iff_ne_zero.mp (hB1sq j hj).2)⟩
  have hDv : ∀ j ∈ insert 1 B, D j = 0 := LI_of P hPprime (insert 1 B) hB1sq hfactors D hvan
  have hA1 : A 1 = (σ : ℚ) := by
    have h := hDv 1 (Finset.mem_insert_self 1 B)
    simp only [hD] at h
    simp at h
    linarith [h]
  have hσq : (σ : ℚ) ≠ 0 := by
    rcases hσ with rfl | rfl <;> norm_num
  have hA1ne : A 1 ≠ 0 := by rw [hA1]; exact hσq
  have hvalA : padicValRat p (A 1) = 0 := by
    rw [hA1]
    rcases hσ with rfl | rfl
    · rw [Int.cast_one, padicValRat.one]
    · rw [Int.cast_neg, Int.cast_one, padicValRat.neg, padicValRat.one]
  have hge : 1 ≤ padicValRat p (A 1) := by
    have hA1' : A 1 = ∑ i ∈ Finset.univ.filter (fun i => k i = 1), f i := by
      simp only [hA]
    rw [hA1']
    refine one_le_padicValRat_sum hp (by rwa [hA1'] at hA1ne) (fun i hi => ?_)
    have hki : k i = 1 := (Finset.mem_filter.mp hi).2
    have hr_sq : r i = ((c i : ℚ) / ((r i).den : ℚ)) ^ 2 := by
      have h1 : (r i : ℚ) = ((r i).num : ℚ) / ((r i).den : ℚ) := (Rat.num_div_den (r i)).symm
      have h2 : ((r i).num : ℚ) = (((r i).num.natAbs : ℕ) : ℚ) := by
        have e : ((r i).num.natAbs : ℤ) = (r i).num :=
          Int.natAbs_of_nonneg (le_of_lt (Rat.num_pos.mpr (hr i)))
        have e2 : (((r i).num.natAbs : ℕ) : ℚ) = (((r i).num.natAbs : ℤ) : ℚ) :=
          (Int.cast_natCast _).symm
        rw [e2, e]
      have h3 : (r i).num.natAbs * (r i).den = (c i) ^ 2 := by
        have h := hw i
        rw [hki, mul_one] at h
        exact h
      have hd : ((r i).den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt (r i).den_pos)
      have h5 : (((r i).num.natAbs : ℕ) : ℚ) = (c i : ℚ) ^ 2 / ((r i).den : ℚ) := by
        have h7 : (((r i).num.natAbs : ℕ) : ℚ) * ((r i).den : ℚ) = (c i : ℚ) ^ 2 := by
          have h8 : (((r i).num.natAbs * (r i).den : ℕ) : ℚ) = ((c i ^ 2 : ℕ) : ℚ) := by rw [h3]
          push_cast at h8
          linarith [h8]
        exact (eq_div_iff hd).mpr h7
      have h6 : ((r i).num : ℚ) / ((r i).den : ℚ) = ((c i : ℚ) / ((r i).den : ℚ)) ^ 2 := by
        rw [h2, h5, div_div, div_pow, pow_two ((r i).den : ℚ)]
      exact h1.trans h6
    have hv2 : padicValRat p (r i) = 2 * padicValRat p ((c i : ℚ) / ((r i).den : ℚ)) := by
      have e := congrArg (padicValRat p) hr_sq
      rw [e, padicValRat.pow]
      norm_num
    have hterm : padicValRat p (f i) = padicValRat p ((c i : ℚ) / ((r i).den : ℚ)) := by
      simp only [hf]
      rcases hε i with h1 | h1
      · rw [h1, Int.cast_one, one_mul]
      · rw [h1, Int.cast_neg, Int.cast_one, neg_one_mul, padicValRat.neg]
    rw [hterm]
    have hvi := hval i
    rw [hv2] at hvi
    omega
  omega

/-!
### p-adic valuation helpers
-/

theorem le_padicValInt_of_dvd {p : ℕ} (hp : p.Prime) {e : ℕ} {s : ℤ} (hs : s ≠ 0)
    (h : (p : ℤ) ^ e ∣ s) : e ≤ padicValInt p s := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [padicValInt_dvd_iff] at h
  rcases h with (rfl | h)
  · exact absurd rfl hs
  · exact h

theorem padicValInt_lt_of_not_dvd {p : ℕ} (hp : p.Prime) {e : ℕ} {s : ℤ} (_hs : s ≠ 0)
    (h : ¬ (p : ℤ) ^ e ∣ s) : padicValInt p s < e := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra hge
  exact h ((padicValInt_dvd_iff e s).mpr (Or.inr (le_of_not_gt hge)))

/-- The number-theoretic heart of Heron's formula: if an odd prime power `p^(2e)`
divides `4 * m^2`, then `p^e ∣ m`. -/
theorem pow_dvd_of_pow_two_dvd_four_mul_sq {p : ℕ} (hp : p.Prime) (hpo : Odd p)
    (e : ℕ) {m : ℤ} (h : (p : ℤ) ^ (2 * e) ∣ 4 * m ^ 2) : (p : ℤ) ^ e ∣ m := by
  rcases eq_or_ne m 0 with (rfl | hm)
  · exact dvd_zero _
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact absurd hpo (by decide)
  have h4 : padicValInt p (4 : ℤ) = 0 := by
    apply padicValInt.eq_zero_of_not_dvd
    intro hdvd
    have hdvd' : p ∣ 4 := by exact_mod_cast hdvd
    have hdvd2 : p ∣ 2 ^ 2 := by simpa using hdvd'
    rcases (Nat.dvd_prime Nat.prime_two).mp (Nat.Prime.dvd_of_dvd_pow hp hdvd2) with h1 | h1
    · exact absurd h1 hp.ne_one
    · exact hp2 h1
  have hm2 : padicValInt p (m ^ 2) = 2 * padicValInt p m := by
    rw [pow_two, padicValInt.mul hm hm]
    ring
  have hval2 : padicValInt p (4 * m ^ 2) = 2 * padicValInt p m := by
    rw [padicValInt.mul (by norm_num) (pow_ne_zero 2 hm), h4, hm2, zero_add]
  rw [padicValInt_dvd_iff] at h ⊢
  rcases h with (h0 | hval)
  · exact absurd h0 (mul_ne_zero (by norm_num) (pow_ne_zero 2 hm))
  · exact Or.inr (by rw [hval2] at hval; exact Nat.le_of_mul_le_mul_left hval (by norm_num))

/-!
### Heron's formula: the triangle case `k = 3`
-/

theorem heron_case {p : ℕ} (hp : p.Prime) (hpo : Odd p) (e : ℕ) (A : Fin 3 → ℤ × ℤ)
    (hsides : ∀ i : Fin 3, (p : ℤ) ^ e ∣ distSq (A i) (A (finRotate 3 i))) :
    (p : ℤ) ^ e ∣ shoelace A := by
  simp only [finRotate_apply] at hsides
  have h1 : (0 : Fin 3) + 1 = 1 := by decide
  have h2 : (1 : Fin 3) + 1 = 2 := by decide
  have h3 : (2 : Fin 3) + 1 = 0 := by decide
  have hshoelace : shoelace A = cdet (A 0) (A 1) + cdet (A 1) (A 2) + cdet (A 2) (A 0) := by
    simp only [shoelace, Fin.sum_univ_three, finRotate_apply]
    rw [h1, h2, h3]
  rw [hshoelace]
  apply pow_dvd_of_pow_two_dvd_four_mul_sq hp hpo e
  have hH : 4 * (cdet (A 0) (A 1) + cdet (A 1) (A 2) + cdet (A 2) (A 0)) ^ 2 =
      2 * (distSq (A 0) (A 1) * distSq (A 1) (A 2) + distSq (A 1) (A 2) * distSq (A 2) (A 0) +
        distSq (A 2) (A 0) * distSq (A 0) (A 1)) -
      (distSq (A 0) (A 1) ^ 2 + distSq (A 1) (A 2) ^ 2 + distSq (A 2) (A 0) ^ 2) := by
    simp only [cdet, distSq]
    ring
  have hpow : (p : ℤ) ^ (2 * e) = ((p : ℤ) ^ e) ^ 2 := by rw [mul_comm, pow_mul]
  rw [hH, hpow]
  have hd01 : (p : ℤ) ^ e ∣ distSq (A 0) (A 1) := by rw [← h1]; exact hsides 0
  have hd12 : (p : ℤ) ^ e ∣ distSq (A 1) (A 2) := by rw [← h2]; exact hsides 1
  have hd20 : (p : ℤ) ^ e ∣ distSq (A 2) (A 0) := by rw [← h3]; exact hsides 2
  apply dvd_sub
  · apply Dvd.dvd.mul_left
    apply dvd_add
    · apply dvd_add
      · rw [pow_two]; exact mul_dvd_mul hd01 hd12
      · rw [pow_two]; exact mul_dvd_mul hd12 hd20
    · rw [pow_two]; exact mul_dvd_mul hd20 hd01
  · apply dvd_add
    · exact dvd_add (pow_dvd_pow_of_dvd hd01 2) (pow_dvd_pow_of_dvd hd12 2)
    · exact pow_dvd_pow_of_dvd hd20 2

/-!
### Rotation invariance of the shoelace sum
-/

theorem shoelace_rotate {k : ℕ} (A : Fin (k + 1) → ℤ × ℤ) (a : Fin (k + 1)) :
    shoelace (fun i => A (i + a)) = shoelace A := by
  simp only [shoelace]
  rw [← Equiv.sum_comp (finCycle a) (fun j => cdet (A j) (A (finRotate (k + 1) j)))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [finCycle_apply, finRotate_apply, finRotate_apply,
    show i + 1 + a = i + a + 1 by
      rw [add_assoc, add_comm (1 : Fin (k + 1)) a, ← add_assoc]]

/-!
### Splitting the shoelace sum along a diagonal
-/

lemma shoelace_eq_sum_range {m : ℕ} (hm : 0 < m) (B : Fin m → ℤ × ℤ) :
    shoelace B =
      ∑ i ∈ Finset.range m, cdet (B ⟨i % m, Nat.mod_lt i hm⟩)
        (B ⟨(i + 1) % m, Nat.mod_lt _ hm⟩) := by
  rw [shoelace,
    ← Fin.sum_univ_eq_sum_range
      (fun i => cdet (B ⟨i % m, Nat.mod_lt i hm⟩) (B ⟨(i + 1) % m, Nat.mod_lt _ hm⟩)) m]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : (⟨(i : ℕ) % m, Nat.mod_lt (i : ℕ) hm⟩ : Fin m) = i := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt i.isLt
  rw [h1]
  have h2 : finRotate m i = ⟨(↑i + 1) % m, Nat.mod_lt _ hm⟩ := by
    rw [finRotate_apply]
    apply Fin.ext
    simp only [Fin.val_add, Fin.val_one', Nat.mod_mod]
    exact Nat.add_mod_mod _ _ _
  rw [h2]

theorem shoelace_split {m : ℕ} (A : Fin m → ℤ × ℤ) {t : ℕ} (ht : 2 ≤ t)
    (htm : t ≤ m - 2) :
    shoelace A =
      shoelace (fun i : Fin (t + 1) => A ⟨i.1, by have := i.isLt; omega⟩) +
      shoelace (fun i : Fin (m - t + 1) =>
        A ⟨(t + i.1) % m, Nat.mod_lt _ (by omega)⟩) := by
  have hm : 0 < m := by omega
  set Bf : ℕ → ℤ × ℤ := fun i => A ⟨i % m, Nat.mod_lt i hm⟩ with hBf
  have hsA : shoelace A = ∑ i ∈ Finset.range m, cdet (Bf i) (Bf (i + 1)) :=
    shoelace_eq_sum_range hm A
  have htm1 : 0 < t + 1 := by omega
  have hpart1 : shoelace (fun i : Fin (t + 1) => A ⟨i.1, by have := i.isLt; omega⟩) =
      (∑ i ∈ Finset.range t, cdet (Bf i) (Bf (i + 1))) + cdet (Bf t) (Bf 0) := by
    rw [shoelace_eq_sum_range htm1 (fun i : Fin (t + 1) => A ⟨i.1, by have := i.isLt; omega⟩),
      Finset.sum_range_succ]
    have hstep : ∀ i : ℕ, i < t →
        cdet ((fun j : Fin (t + 1) => A ⟨j.1, by have := j.isLt; omega⟩)
            ⟨i % (t + 1), Nat.mod_lt i htm1⟩)
          ((fun j : Fin (t + 1) => A ⟨j.1, by have := j.isLt; omega⟩)
            ⟨(i + 1) % (t + 1), Nat.mod_lt _ htm1⟩) =
          cdet (Bf i) (Bf (i + 1)) := by
      intro i hi
      have e1 : (⟨i % (t + 1), Nat.mod_lt i htm1⟩ : Fin (t + 1)) = ⟨i, by omega⟩ := by
        apply Fin.ext
        exact Nat.mod_eq_of_lt (by omega)
      have e2 : (⟨(i + 1) % (t + 1), Nat.mod_lt _ htm1⟩ : Fin (t + 1)) = ⟨i + 1, by omega⟩ := by
        apply Fin.ext
        exact Nat.mod_eq_of_lt (by omega)
      rw [e1, e2]
      have f1 : (⟨i % m, Nat.mod_lt i hm⟩ : Fin m) = ⟨i, by omega⟩ := by
        apply Fin.ext
        exact Nat.mod_eq_of_lt (by omega)
      have f2 : (⟨(i + 1) % m, Nat.mod_lt _ hm⟩ : Fin m) = ⟨i + 1, by omega⟩ := by
        apply Fin.ext
        exact Nat.mod_eq_of_lt (by omega)
      simp only [hBf]
      rw [f1, f2]
    rw [Finset.sum_congr rfl (fun i hi => hstep i (Finset.mem_range.mp hi))]
    congr 1
    have e1 : (⟨t % (t + 1), Nat.mod_lt t htm1⟩ : Fin (t + 1)) = ⟨t, by omega⟩ := by
      apply Fin.ext
      exact Nat.mod_eq_of_lt (by omega)
    have e2 : (⟨(t + 1) % (t + 1), Nat.mod_lt _ htm1⟩ : Fin (t + 1)) = ⟨0, by omega⟩ := by
      apply Fin.ext
      exact Nat.mod_self (t + 1)
    rw [e1, e2]
    have f1 : (⟨t % m, Nat.mod_lt t hm⟩ : Fin m) = ⟨t, by omega⟩ := by
      apply Fin.ext
      exact Nat.mod_eq_of_lt (by omega)
    have f2 : (⟨0 % m, Nat.mod_lt 0 hm⟩ : Fin m) = ⟨0, by omega⟩ := by
      apply Fin.ext
      exact Nat.zero_mod m
    simp only [hBf]
    rw [f1, f2]
  have htm2 : 0 < m - t + 1 := by omega
  have hpart2 : shoelace (fun i : Fin (m - t + 1) =>
        A ⟨(t + i.1) % m, Nat.mod_lt _ (by omega)⟩) =
      (∑ i ∈ Finset.range (m - t), cdet (Bf (t + i)) (Bf (t + i + 1))) + cdet (Bf 0) (Bf t) := by
    rw [shoelace_eq_sum_range htm2 (fun i : Fin (m - t + 1) =>
        A ⟨(t + i.1) % m, Nat.mod_lt _ (by omega)⟩), Finset.sum_range_succ]
    have hstep : ∀ i : ℕ, i < m - t →
        cdet ((fun j : Fin (m - t + 1) => A ⟨(t + j.1) % m, Nat.mod_lt _ (by omega)⟩)
            ⟨i % (m - t + 1), Nat.mod_lt i htm2⟩)
          ((fun j : Fin (m - t + 1) => A ⟨(t + j.1) % m, Nat.mod_lt _ (by omega)⟩)
            ⟨(i + 1) % (m - t + 1), Nat.mod_lt _ htm2⟩) =
          cdet (Bf (t + i)) (Bf (t + i + 1)) := by
      intro i hi
      have e1 : (⟨i % (m - t + 1), Nat.mod_lt i htm2⟩ : Fin (m - t + 1)) = ⟨i, by omega⟩ := by
        apply Fin.ext
        exact Nat.mod_eq_of_lt (by omega)
      have e2 : (⟨(i + 1) % (m - t + 1), Nat.mod_lt _ htm2⟩ : Fin (m - t + 1)) =
          ⟨i + 1, by omega⟩ := by
        apply Fin.ext
        exact Nat.mod_eq_of_lt (by omega)
      rw [e1, e2]
      simp only [hBf]
      rw [show t + (i + 1) = t + i + 1 from by omega]
    rw [Finset.sum_congr rfl (fun i hi => hstep i (Finset.mem_range.mp hi))]
    congr 1
    have e1 : (⟨(m - t) % (m - t + 1), Nat.mod_lt _ htm2⟩ : Fin (m - t + 1)) =
        ⟨m - t, by omega⟩ := by
      apply Fin.ext
      exact Nat.mod_eq_of_lt (by omega)
    have e2 : (⟨(m - t + 1) % (m - t + 1), Nat.mod_lt _ htm2⟩ : Fin (m - t + 1)) =
        ⟨0, by omega⟩ := by
      apply Fin.ext
      exact Nat.mod_self (m - t + 1)
    rw [e1, e2]
    have f1 : (⟨(t + (m - t)) % m, Nat.mod_lt _ hm⟩ : Fin m) = ⟨0, hm⟩ := by
      apply Fin.ext
      show (t + (m - t)) % m = 0
      rw [Nat.add_sub_cancel' (by omega : t ≤ m)]
      exact Nat.mod_self m
    have f2 : (⟨(t + 0) % m, Nat.mod_lt _ hm⟩ : Fin m) = ⟨t % m, Nat.mod_lt t hm⟩ := by
      apply Fin.ext
      show (t + 0) % m = t % m
      rw [Nat.add_zero]
    rw [f1, f2]
    simp only [hBf]
    have g1 : (⟨0 % m, Nat.mod_lt 0 hm⟩ : Fin m) = ⟨0, hm⟩ := by
      apply Fin.ext
      exact Nat.zero_mod m
    rw [g1]
  rw [hsA, hpart1, hpart2,
    ← Finset.sum_range_add_sum_Ico (f := fun i => cdet (Bf i) (Bf (i + 1))) (by omega : t ≤ m),
    Finset.sum_Ico_eq_sum_range,
    cdet_comm (Bf 0) (Bf t)]
  ring

/-!
### The geometry: inversion and the generalized Ptolemy relation

We work with points in `ℚ × ℚ`. `normSqQ` is the squared norm, `dotQ` the dot
product, `subQ` subtraction, `smulQ` scalar multiplication.
-/

/-- Embedding of integer points into rational points. -/
def toQ (P : ℤ × ℤ) : ℚ × ℚ := ((P.1 : ℚ), (P.2 : ℚ))

/-- Squared norm of a rational point. -/
def normSqQ (P : ℚ × ℚ) : ℚ := P.1 ^ 2 + P.2 ^ 2

/-- Dot product of two rational points. -/
def dotQ (P Q : ℚ × ℚ) : ℚ := P.1 * Q.1 + P.2 * Q.2

/-- Subtraction of rational points. -/
def subQ (P Q : ℚ × ℚ) : ℚ × ℚ := (P.1 - Q.1, P.2 - Q.2)

/-- Scalar multiplication of a rational point. -/
def smulQ (t : ℚ) (P : ℚ × ℚ) : ℚ × ℚ := (t * P.1, t * P.2)

lemma toQ_injective : Function.Injective toQ := by
  intro P Q h
  simp only [toQ, Prod.mk.injEq, Rat.intCast_inj] at h
  exact Prod.ext h.1 h.2

lemma normSqQ_subQ_toQ (X Y : ℤ × ℤ) :
    normSqQ (subQ (toQ X) (toQ Y)) = (distSq X Y : ℚ) := by
  simp only [normSqQ, subQ, toQ, distSq]
  push_cast
  ring

lemma normSqQ_eq_zero {P : ℚ × ℚ} (h : normSqQ P = 0) : P = (0, 0) := by
  simp only [normSqQ] at h
  have h1 : P.1 ^ 2 = 0 := by nlinarith [sq_nonneg P.1, sq_nonneg P.2]
  have h2 : P.2 ^ 2 = 0 := by nlinarith [sq_nonneg P.1, sq_nonneg P.2]
  rw [sq_eq_zero_iff] at h1 h2
  exact Prod.ext h1 h2

lemma normSqQ_pos_of_ne_zero {P : ℚ × ℚ} (h : P ≠ (0, 0)) : 0 < normSqQ P := by
  simp only [normSqQ]
  by_cases h1 : P.1 = 0
  · have h2 : P.2 ≠ 0 := by
      intro h2
      exact h (Prod.ext h1 h2)
    exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero h2)
  · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero h1) (sq_nonneg _)

lemma normSqQ_smulQ (t : ℚ) (P : ℚ × ℚ) : normSqQ (smulQ t P) = t ^ 2 * normSqQ P := by
  simp only [normSqQ, smulQ]
  ring

lemma dotQ_smulQ (t : ℚ) (P Q : ℚ × ℚ) : dotQ P (smulQ t Q) = t * dotQ P Q := by
  simp only [dotQ, smulQ]
  ring

lemma dotQ_subQ (P Q R : ℚ × ℚ) : dotQ P (subQ Q R) = dotQ P Q - dotQ P R := by
  simp only [dotQ, subQ]
  ring

lemma dotQ_subQ_left (P Q R : ℚ × ℚ) : dotQ (subQ Q R) P = dotQ Q P - dotQ R P := by
  simp only [dotQ, subQ]
  ring

lemma subQ_subQ_right (P Q R : ℚ × ℚ) : subQ (subQ P R) (subQ Q R) = subQ P Q := by
  simp only [subQ, Prod.mk.injEq]
  constructor <;> ring

lemma normSqQ_perpd (c' : ℚ × ℚ) : normSqQ (-c'.2, c'.1) = normSqQ c' := by
  simp only [normSqQ]
  ring

/-- A vector perpendicular to `c'` is a scalar multiple of `(-c'.2, c'.1)`. -/
lemma perp_eq_smul (c' w : ℚ × ℚ) (h : dotQ c' w = 0) (hne : normSqQ c' ≠ 0) :
    w = smulQ (dotQ w (-c'.2, c'.1) / normSqQ c') (-c'.2, c'.1) := by
  simp only [dotQ] at h
  have hne' : c'.1 ^ 2 + c'.2 ^ 2 ≠ 0 := by simpa only [normSqQ] using hne
  simp only [dotQ, smulQ, normSqQ]
  refine Prod.ext ?_ ?_
  · field_simp [hne']
    linear_combination c'.1 * h
  · field_simp [hne']
    linear_combination c'.2 * h

/-- The inversion distance formula: `|P/|P|² - Q/|Q|²|² = |P - Q|²/(|P|²|Q|²)`. -/
lemma inv_dist (P Q : ℚ × ℚ) (hP : normSqQ P ≠ 0) (hQ : normSqQ Q ≠ 0) :
    normSqQ (subQ (smulQ (normSqQ P)⁻¹ P) (smulQ (normSqQ Q)⁻¹ Q)) =
      normSqQ (subQ P Q) / (normSqQ P * normSqQ Q) := by
  have hP' : P.1 ^ 2 + P.2 ^ 2 ≠ 0 := by simpa only [normSqQ] using hP
  have hQ' : Q.1 ^ 2 + Q.2 ^ 2 ≠ 0 := by simpa only [normSqQ] using hQ
  simp only [normSqQ, subQ, smulQ]
  field_simp [hP', hQ']
  ring

lemma sqrt_normSqQ_smul (t : ℚ) (P : ℚ × ℚ) :
    Real.sqrt (normSqQ (smulQ t P) : ℝ) = |t| * Real.sqrt (normSqQ P : ℝ) := by
  rw [normSqQ_smulQ]
  simp only [Rat.cast_mul, Rat.cast_pow]
  rw [Real.sqrt_mul (sq_nonneg (t : ℝ)), Real.sqrt_sq_eq_abs, ← Rat.cast_abs]

theorem no_good_diag_absurd {k : ℕ} (hk : 3 ≤ k) (A : Fin (k + 1) → ℤ × ℤ)
    (hA : Function.Injective A) (c : ℚ × ℚ) (ρ : ℚ)
    (hcircle : ∀ i, (((A i).1 : ℚ) - c.1) ^ 2 + (((A i).2 : ℚ) - c.2) ^ 2 = ρ)
    {p : ℕ} (hp : p.Prime) {e : ℕ} (he : 1 ≤ e)
    (hsides : ∀ i : Fin (k + 1), (p : ℤ) ^ e ∣ distSq (A i) (A (finRotate (k + 1) i)))
    (hdiag : ∀ a b : Fin (k + 1), a ≠ b → b ≠ a + 1 → a ≠ b + 1 →
      ¬ (p : ℤ) ^ e ∣ distSq (A a) (A b)) :
    False := by
  haveI : Fact p.Prime := ⟨hp⟩
  set O : ℤ × ℤ := A ⟨k, Nat.lt_succ_self k⟩ with hO
  set Aext : ℕ → ℤ × ℤ := fun i => A ⟨i % (k + 1), Nat.mod_lt i (Nat.succ_pos k)⟩ with hAext
  have hAext_eq : ∀ (i : ℕ) (hi : i < k + 1), Aext i = A ⟨i, hi⟩ := by
    intro i hi
    simp only [hAext, Nat.mod_eq_of_lt hi]
  have hinj : ∀ i j : ℕ, i < k + 1 → j < k + 1 → Aext i = Aext j → i = j := by
    intro i j hi hj h
    rw [hAext_eq i hi, hAext_eq j hj] at h
    have h' := hA h
    simp only [Fin.mk.injEq] at h'
    exact h'
  have hOk : O = Aext k := by
    simp only [hO, hAext, Nat.mod_eq_of_lt (Nat.lt_succ_self k)]
  set c' : ℚ × ℚ := (c.1 - (O.1 : ℚ), c.2 - (O.2 : ℚ)) with hc'
  set Pj : ℕ → ℚ × ℚ := fun j => subQ (toQ (Aext j)) (toQ O) with hPj
  -- the circle equation, centered at O
  have key : ∀ j : ℕ, normSqQ (Pj j) = 2 * dotQ c' (Pj j) := by
    intro j
    have h1 := hcircle ⟨j % (k + 1), Nat.mod_lt j (Nat.succ_pos k)⟩
    have h2 := hcircle ⟨k, Nat.lt_succ_self k⟩
    simp only [hPj, normSqQ, dotQ, subQ, toQ, hc', hO, hAext]
    linear_combination h1 - h2
  -- Pj j ≠ 0 unless j ≡ k
  have hPne : ∀ j : ℕ, j % (k + 1) ≠ k → Pj j ≠ (0, 0) := by
    intro j hj h
    apply hj
    simp only [hPj] at h
    have h1 : toQ (Aext j) = toQ O := by
      simp only [subQ, Prod.mk.injEq, sub_eq_zero] at h
      exact Prod.ext h.1 h.2
    have h2 : Aext j = O := toQ_injective h1
    simp only [hO, hAext] at h2
    have h3 := hA h2
    simp only [Fin.mk.injEq] at h3
    exact h3
  have hNne : ∀ j : ℕ, j % (k + 1) ≠ k → normSqQ (Pj j) ≠ 0 := by
    intro j hj h
    exact hPne j hj (normSqQ_eq_zero h)
  have hc'ne : c' ≠ (0, 0) := by
    intro h
    have h1 := key 0
    rw [h] at h1
    have h2 : dotQ (0, 0) (Pj 0) = 0 := by simp [dotQ]
    rw [h2, mul_zero] at h1
    have h0 : (0 : ℕ) % (k + 1) ≠ k := by simp only [Nat.zero_mod]; omega
    exact hPne 0 h0 (normSqQ_eq_zero h1)
  -- inversion about O
  set B : ℕ → ℚ × ℚ := fun j => smulQ (normSqQ (Pj j))⁻¹ (Pj j) with hB
  have hBline : ∀ j : ℕ, j % (k + 1) ≠ k → 2 * dotQ c' (B j) = 1 := by
    intro j hj
    have h1 : 2 * dotQ c' (B j) = (normSqQ (Pj j))⁻¹ * (2 * dotQ c' (Pj j)) := by
      simp only [hB, dotQ_smulQ]
      ring
    rw [h1, ← key j, inv_mul_cancel₀ (hNne j hj)]
  set ed : ℚ × ℚ := (-c'.2, c'.1) with hed
  have hedne : normSqQ ed ≠ 0 := by
    rw [hed, normSqQ_perpd]
    exact fun h => hc'ne (normSqQ_eq_zero h)
  have hedpos : (0 : ℝ) < Real.sqrt (normSqQ ed : ℝ) := by
    apply Real.sqrt_pos.mpr
    have h : (0 : ℚ) < normSqQ ed := by
      apply normSqQ_pos_of_ne_zero
      intro h
      exact hedne (by rw [h]; simp [normSqQ])
    exact_mod_cast h
  set τ : ℕ → ℚ := fun j => dotQ (subQ (B j) (B 0)) ed / normSqQ ed with hτ
  have hne_k : ∀ j : ℕ, j ≤ k - 1 → j % (k + 1) ≠ k := by
    intro j hj
    rw [Nat.mod_eq_of_lt (by omega : j < k + 1)]
    omega
  -- the images B j are collinear, with coordinate τ
  have hBsub : ∀ i j : ℕ, i % (k + 1) ≠ k → j % (k + 1) ≠ k →
      subQ (B i) (B j) = smulQ (τ i - τ j) ed := by
    intro i j hi hj
    have hdi : dotQ c' (subQ (B i) (B j)) = 0 := by
      rw [dotQ_subQ]
      have e1 := hBline i hi
      have e2 := hBline j hj
      linarith
    have h1 := perp_eq_smul c' (subQ (B i) (B j)) hdi (fun h => hc'ne (normSqQ_eq_zero h))
    have h2 : dotQ (subQ (B i) (B j)) ed = (τ i - τ j) * normSqQ ed := by
      have h21 : dotQ (subQ (B i) (B j)) ed =
          dotQ (subQ (B i) (B 0)) ed - dotQ (subQ (B j) (B 0)) ed := by
        have hsub : subQ (B i) (B j) = subQ (subQ (B i) (B 0)) (subQ (B j) (B 0)) := by
          simp only [subQ, Prod.mk.injEq]
          constructor <;> ring
        rw [hsub, dotQ_subQ_left]
      rw [h21]
      simp only [hτ]
      field_simp [hedne]
    have h3 : normSqQ c' = normSqQ ed := by rw [hed, normSqQ_perpd]
    rw [h1, ← hed]
    congr 1
    rw [h2, h3]
    field_simp [hedne]
  -- B is injective on the relevant range
  have hPB : ∀ i j : ℕ, i % (k + 1) ≠ k → j % (k + 1) ≠ k → B i = B j → Pj i = Pj j := by
    intro i j hi hj h
    have hNi : normSqQ (Pj i) ≠ 0 := hNne i hi
    have hNj : normSqQ (Pj j) ≠ 0 := hNne j hj
    have h1 : Pj i = smulQ (normSqQ (Pj i)) (B i) := by
      simp only [hB, smulQ]
      apply Prod.ext <;> field_simp [hNi] <;> ring
    have h2 : Pj j = smulQ (normSqQ (Pj j)) (B j) := by
      simp only [hB, smulQ]
      apply Prod.ext <;> field_simp [hNj] <;> ring
    have h3 : normSqQ (B i) = (normSqQ (Pj i))⁻¹ := by
      simp only [hB, normSqQ_smulQ]
      field_simp [hNi]
    have h4 : normSqQ (B j) = (normSqQ (Pj j))⁻¹ := by
      simp only [hB, normSqQ_smulQ]
      field_simp [hNj]
    have h5 : normSqQ (Pj i) = normSqQ (Pj j) := by
      have h6 := congrArg normSqQ h
      rw [h3, h4] at h6
      exact inv_inj.mp h6
    rw [h1, h2, h, ← h5]
  have hBinj : ∀ i j : ℕ, i ≤ k - 1 → j ≤ k - 1 → B i = B j → i = j := by
    intro i j hi hj h
    have h1 := hPB i j (hne_k i hi) (hne_k j hj) h
    have h2 : toQ (Aext i) = toQ (Aext j) := by
      simp only [hPj, subQ, Prod.mk.injEq] at h1
      exact Prod.ext (by linarith [h1.1]) (by linarith [h1.2])
    exact hinj i j (by omega) (by omega) (toQ_injective h2)
  have hτeq : ∀ i j : ℕ, i ≤ k - 1 → j ≤ k - 1 → τ i = τ j → i = j := by
    intro i j hi hj h
    apply hBinj i j hi hj
    have h1 := hBsub i j (hne_k i (by omega)) (hne_k j (by omega))
    rw [h, sub_self] at h1
    have h2 : subQ (B i) (B j) = (0, 0) := by
      rw [h1]
      simp [smulQ]
    simp only [subQ, Prod.mk.injEq, sub_eq_zero] at h2
    exact Prod.ext h2.1 h2.2
  -- the rational quantities q_j and their square roots
  set qq : ℕ → ℚ := fun j =>
    normSqQ (subQ (Pj j) (Pj (j + 1))) / (normSqQ (Pj j) * normSqQ (Pj (j + 1))) with hqq
  set qe : ℚ := normSqQ (subQ (Pj 0) (Pj (k - 1))) /
    (normSqQ (Pj 0) * normSqQ (Pj (k - 1))) with hqe
  have hqqpos : ∀ j ∈ Finset.range (k - 1), 0 < qq j := by
    intro j hj
    rw [Finset.mem_range] at hj
    have h1 : 0 < normSqQ (subQ (Pj j) (Pj (j + 1))) := by
      apply normSqQ_pos_of_ne_zero
      intro h
      have hP : Pj j = Pj (j + 1) := by
        simp only [subQ, Prod.mk.injEq, sub_eq_zero] at h
        exact Prod.ext h.1 h.2
      have h2 : toQ (Aext j) = toQ (Aext (j + 1)) := by
        simp only [hPj, subQ, Prod.mk.injEq] at hP
        exact Prod.ext (by linarith [hP.1]) (by linarith [hP.2])
      have h3 : Aext j = Aext (j + 1) := toQ_injective h2
      have h4 := hinj j (j + 1) (by omega) (by omega) h3
      omega
    have h2 : 0 < normSqQ (Pj j) * normSqQ (Pj (j + 1)) := by
      apply mul_pos
      · exact normSqQ_pos_of_ne_zero (hPne j (hne_k j (by omega)))
      · exact normSqQ_pos_of_ne_zero (hPne (j + 1) (hne_k (j + 1) (by omega)))
    simp only [hqq]
    exact div_pos h1 h2
  have hqepos : 0 < qe := by
    have h1 : 0 < normSqQ (subQ (Pj 0) (Pj (k - 1))) := by
      apply normSqQ_pos_of_ne_zero
      intro h
      have hP : Pj 0 = Pj (k - 1) := by
        simp only [subQ, Prod.mk.injEq, sub_eq_zero] at h
        exact Prod.ext h.1 h.2
      have h2 : toQ (Aext 0) = toQ (Aext (k - 1)) := by
        simp only [hPj, subQ, Prod.mk.injEq] at hP
        exact Prod.ext (by linarith [hP.1]) (by linarith [hP.2])
      have h3 : Aext 0 = Aext (k - 1) := toQ_injective h2
      have h4 := hinj 0 (k - 1) (by omega) (by omega) h3
      omega
    have h2 : 0 < normSqQ (Pj 0) * normSqQ (Pj (k - 1)) := by
      apply mul_pos
      · exact normSqQ_pos_of_ne_zero (hPne 0 (hne_k 0 (by omega)))
      · exact normSqQ_pos_of_ne_zero (hPne (k - 1) (hne_k (k - 1) (by omega)))
    simp only [hqe]
    exact div_pos h1 h2
  have hsqrt : ∀ j : ℕ, j ≤ k - 2 →
      Real.sqrt (qq j : ℝ) = |τ (j + 1) - τ j| * Real.sqrt (normSqQ ed : ℝ) := by
    intro j hj
    have h1 : qq j = normSqQ (subQ (B j) (B (j + 1))) := by
      simp only [hqq]
      rw [inv_dist (Pj j) (Pj (j + 1)) (hNne j (hne_k j (by omega)))
        (hNne (j + 1) (hne_k (j + 1) (by omega)))]
    rw [h1, hBsub j (j + 1) (hne_k j (by omega)) (hne_k (j + 1) (by omega)),
      sqrt_normSqQ_smul, abs_sub_comm]
  have hsqrt_end : Real.sqrt (qe : ℝ) = |τ (k - 1) - τ 0| * Real.sqrt (normSqQ ed : ℝ) := by
    have h1 : qe = normSqQ (subQ (B 0) (B (k - 1))) := by
      simp only [hqe]
      rw [inv_dist (Pj 0) (Pj (k - 1)) (hNne 0 (hne_k 0 (by omega)))
        (hNne (k - 1) (hne_k (k - 1) (by omega)))]
    rw [h1, hBsub 0 (k - 1) (hne_k 0 (by omega)) (hne_k (k - 1) (by omega)),
      sqrt_normSqQ_smul, abs_sub_comm]
  -- telescoping
  have htel : ∑ j ∈ Finset.range (k - 1), (τ (j + 1) - τ j) = τ (k - 1) - τ 0 :=
    Finset.sum_range_sub (fun j => τ j) (k - 1)
  set ε : ℕ → ℤ := fun j => if τ j < τ (j + 1) then 1 else -1 with hε
  have hεsign : ∀ j : ℕ, j ≤ k - 2 → (ε j : ℚ) * |τ (j + 1) - τ j| = τ (j + 1) - τ j := by
    intro j hj
    have hne : τ j ≠ τ (j + 1) := fun h => by
      have habs := hτeq j (j + 1) (by omega) (by omega) h
      omega
    simp only [hε]
    by_cases hcase : τ j < τ (j + 1)
    · rw [if_pos hcase]
      simp only [Int.cast_one, one_mul]
      exact abs_of_pos (sub_pos.mpr hcase)
    · rw [if_neg hcase]
      have hlt : τ (j + 1) - τ j < 0 := by
        have hle : τ (j + 1) ≤ τ j := le_of_not_gt hcase
        have hne2 : τ (j + 1) ≠ τ j := fun h => hne h.symm
        exact sub_neg.mpr (lt_of_le_of_ne hle hne2)
      rw [abs_of_neg hlt]
      simp
  set σ : ℤ := if τ 0 < τ (k - 1) then 1 else -1 with hσ
  have hσsign : (σ : ℚ) * |τ (k - 1) - τ 0| = τ (k - 1) - τ 0 := by
    have hne : τ 0 ≠ τ (k - 1) := fun h => by
      have habs := hτeq 0 (k - 1) (by omega) (by omega) h
      omega
    simp only [hσ]
    by_cases hcase : τ 0 < τ (k - 1)
    · rw [if_pos hcase]
      simp only [Int.cast_one, one_mul]
      exact abs_of_pos (sub_pos.mpr hcase)
    · rw [if_neg hcase]
      have hlt : τ (k - 1) - τ 0 < 0 := by
        have hle : τ (k - 1) ≤ τ 0 := le_of_not_gt hcase
        have hne2 : τ (k - 1) ≠ τ 0 := fun h => hne h.symm
        exact sub_neg.mpr (lt_of_le_of_ne hle hne2)
      rw [abs_of_neg hlt]
      simp
  -- the signed "generalized Ptolemy" relation
  have hsum : ∑ j ∈ Finset.range (k - 1), (ε j : ℝ) * Real.sqrt (qq j : ℝ) =
      (σ : ℝ) * Real.sqrt (qe : ℝ) := by
    have h1 : ∀ j ∈ Finset.range (k - 1), (ε j : ℝ) * Real.sqrt (qq j : ℝ) =
        (((ε j : ℚ) * |τ (j + 1) - τ j| : ℚ) : ℝ) * Real.sqrt (normSqQ ed : ℝ) := by
      intro j hj
      rw [Finset.mem_range] at hj
      rw [hsqrt j (by omega)]
      push_cast [Rat.cast_intCast]
      ring
    have h2 : (∑ j ∈ Finset.range (k - 1), (ε j : ℝ) * Real.sqrt (qq j : ℝ)) =
        (∑ j ∈ Finset.range (k - 1), (((ε j : ℚ) * |τ (j + 1) - τ j| : ℚ) : ℝ)) *
          Real.sqrt (normSqQ ed : ℝ) := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl h1
    have h3 : (∑ j ∈ Finset.range (k - 1), (((ε j : ℚ) * |τ (j + 1) - τ j| : ℚ) : ℝ)) =
        ((τ (k - 1) - τ 0 : ℚ) : ℝ) := by
      have h31 : ∀ j ∈ Finset.range (k - 1), (ε j : ℚ) * |τ (j + 1) - τ j| =
          τ (j + 1) - τ j := by
        intro j hj
        rw [Finset.mem_range] at hj
        exact hεsign j (by omega)
      rw [← Rat.cast_sum, Finset.sum_congr rfl h31, htel]
    have h4 : ((τ (k - 1) - τ 0 : ℚ) : ℝ) = (σ : ℝ) * (↑|τ (k - 1) - τ 0| : ℝ) := by
      have h41 : ((τ (k - 1) - τ 0 : ℚ) : ℝ) = (((σ : ℚ) * |τ (k - 1) - τ 0| : ℚ) : ℝ) := by
        rw [hσsign]
      rw [h41, Rat.cast_mul, Rat.cast_intCast]
    rw [h2, h3, hsqrt_end, h4]
    ring
  -- pass to the ratios r_j = q_j / q_e
  set rr : ℕ → ℚ := fun j => qq j / qe with hrr
  have hrpos : ∀ j ∈ Finset.range (k - 1), 0 < rr j := by
    intro j hj
    simp only [hrr]
    exact div_pos (hqqpos j hj) hqepos
  have hrsqrt : ∀ j ∈ Finset.range (k - 1),
      Real.sqrt (qq j : ℝ) = Real.sqrt (rr j : ℝ) * Real.sqrt (qe : ℝ) := by
    intro j hj
    have h11 : qq j = rr j * qe := by
      simp only [hrr]
      rw [div_mul_cancel₀ (qq j) hqepos.ne']
    rw [h11, Rat.cast_mul]
    exact Real.sqrt_mul (by exact_mod_cast (hrpos j hj).le) (qe : ℝ)
  have hrel : (∑ j ∈ Finset.range (k - 1), (ε j : ℝ) * Real.sqrt (rr j : ℝ)) = (σ : ℝ) := by
    have h1 : (∑ j ∈ Finset.range (k - 1), (ε j : ℝ) * Real.sqrt (rr j : ℝ)) *
        Real.sqrt (qe : ℝ) = (σ : ℝ) * Real.sqrt (qe : ℝ) := by
      rw [← hsum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [hrsqrt j hj]
      ring
    exact mul_right_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr (by exact_mod_cast hqepos))) h1
  have hrelFin : (∑ i : Fin (k - 1), (ε i.1 : ℝ) * Real.sqrt (rr i.1 : ℝ)) = (σ : ℝ) := by
    rw [← hrel]
    exact Fin.sum_univ_eq_sum_range (fun j => (ε j : ℝ) * Real.sqrt (rr j : ℝ)) (k - 1)
  -- valuations
  set sd : ℕ → ℤ := fun j => distSq (Aext j) (Aext (j + 1)) with hsd
  set ud : ℕ → ℤ := fun j => distSq (Aext j) O with hud
  set dd : ℤ := distSq (Aext 0) (Aext (k - 1)) with hdd
  have hcastP : ∀ j : ℕ, normSqQ (Pj j) = (ud j : ℚ) := by
    intro j
    simp only [hPj, hud]
    exact normSqQ_subQ_toQ (Aext j) O
  have hcastS : ∀ i j : ℕ, normSqQ (subQ (Pj i) (Pj j)) = (distSq (Aext i) (Aext j) : ℚ) := by
    intro i j
    have hsub : subQ (Pj i) (Pj j) = subQ (toQ (Aext i)) (toQ (Aext j)) := by
      simp only [hPj]
      rw [subQ_subQ_right]
    rw [hsub]
    exact normSqQ_subQ_toQ (Aext i) (Aext j)
  have hcast_qq : ∀ j : ℕ, qq j = (sd j : ℚ) / ((ud j : ℚ) * (ud (j + 1) : ℚ)) := by
    intro j
    simp only [hqq, hsd]
    rw [hcastS j (j + 1), hcastP j, hcastP (j + 1)]
  have hcast_qe : qe = (dd : ℚ) / ((ud 0 : ℚ) * (ud (k - 1) : ℚ)) := by
    simp only [hqe, hdd]
    rw [hcastS 0 (k - 1), hcastP 0, hcastP (k - 1)]
  have hsdne : ∀ j : ℕ, j ≤ k - 2 → sd j ≠ 0 := by
    intro j hj
    simp only [hsd]
    apply distSq_ne_zero
    intro h
    have h' := hinj j (j + 1) (by omega) (by omega) h
    omega
  have hudne : ∀ j : ℕ, j ≤ k - 1 → ud j ≠ 0 := by
    intro j hj
    simp only [hud]
    apply distSq_ne_zero
    intro h
    rw [hOk] at h
    have h' := hinj j k (by omega) (by omega) h
    omega
  have hddne : dd ≠ 0 := by
    simp only [hdd]
    apply distSq_ne_zero
    intro h
    have h' := hinj 0 (k - 1) (by omega) (by omega) h
    omega
  have hfinrot : ∀ (j : ℕ) (hj : j < k + 1),
      finRotate (k + 1) ⟨j, hj⟩ = ⟨(j + 1) % (k + 1), Nat.mod_lt _ (by omega)⟩ := by
    intro j hj
    rw [finRotate_apply]
    apply Fin.ext
    simp only [Fin.val_add, Fin.val_one', Nat.mod_mod]
    exact Nat.add_mod_mod _ _ _
  have hfinrot_of_lt : ∀ (j : ℕ) (hj : j + 1 < k + 1),
      finRotate (k + 1) ⟨j, by omega⟩ = ⟨j + 1, hj⟩ := by
    intro j hj
    rw [hfinrot j (by omega)]
    apply Fin.ext
    exact Nat.mod_eq_of_lt hj
  have hfinrot_last : finRotate (k + 1) ⟨k, by omega⟩ = ⟨0, by omega⟩ := by
    rw [hfinrot k (by omega)]
    apply Fin.ext
    exact Nat.mod_self (k + 1)
  have hfinrot_pred : finRotate (k + 1) ⟨k - 1, by omega⟩ = ⟨k, by omega⟩ := by
    rw [hfinrot (k - 1) (by omega)]
    apply Fin.ext
    rw [show k - 1 + 1 = k by omega]
    exact Nat.mod_eq_of_lt (Nat.lt_succ_self k)
  have hside_eq : ∀ (j : ℕ) (hj : j ≤ k - 2) (hj' : j < k + 1),
      distSq (Aext j) (Aext (j + 1)) =
        distSq (A ⟨j, hj'⟩) (A (finRotate (k + 1) ⟨j, hj'⟩)) := by
    intro j hj hj'
    rw [hAext_eq j hj', hAext_eq (j + 1) (by omega), hfinrot_of_lt j (by omega)]
  have hside_val : ∀ j : ℕ, j ≤ k - 2 → e ≤ padicValInt p (sd j) := by
    intro j hj
    apply le_padicValInt_of_dvd hp (hsdne j hj)
    simp only [hsd]
    rw [hside_eq j hj (by omega)]
    exact hsides ⟨j, by omega⟩
  have hud0_eq : distSq (Aext 0) O =
      distSq (A ⟨k, by omega⟩) (A (finRotate (k + 1) ⟨k, by omega⟩)) := by
    rw [hAext_eq 0 (by omega), hOk, hAext_eq k (by omega),
      distSq_comm (A ⟨0, by omega⟩) (A ⟨k, by omega⟩), hfinrot_last]
  have hudk_eq : distSq (Aext (k - 1)) O =
      distSq (A ⟨k - 1, by omega⟩) (A (finRotate (k + 1) ⟨k - 1, by omega⟩)) := by
    rw [hAext_eq (k - 1) (by omega), hOk, hAext_eq k (by omega), hfinrot_pred]
  have hud0_val : e ≤ padicValInt p (ud 0) := by
    apply le_padicValInt_of_dvd hp (hudne 0 (by omega))
    simp only [hud]
    rw [hud0_eq]
    exact hsides ⟨k, by omega⟩
  have hudk_val : e ≤ padicValInt p (ud (k - 1)) := by
    apply le_padicValInt_of_dvd hp (hudne (k - 1) (by omega))
    simp only [hud]
    rw [hudk_eq]
    exact hsides ⟨k - 1, by omega⟩
  have hval_add_one : ∀ (j : ℕ) (hj : j < k + 1),
      ((⟨j, hj⟩ : Fin (k + 1)) + 1).val = (j + 1) % (k + 1) := by
    intro j hj
    simp only [Fin.val_add, Fin.val_one', Nat.mod_mod]
    exact Nat.add_mod_mod _ _ _
  have hdiag' : ∀ (i j : ℕ) (hi : i < k + 1) (hj : j < k + 1),
      i ≠ j → j ≠ (i + 1) % (k + 1) → i ≠ (j + 1) % (k + 1) →
      ¬ (p : ℤ) ^ e ∣ distSq (A ⟨i, hi⟩) (A ⟨j, hj⟩) := by
    intro i j hi hj h0 h1 h2
    apply hdiag
    · intro h
      exact h0 (Fin.ext_iff.mp h)
    · intro h
      have h3 := congrArg Fin.val h
      rw [hval_add_one i hi] at h3
      exact h1 h3
    · intro h
      have h3 := congrArg Fin.val h
      rw [hval_add_one j hj] at h3
      exact h2 h3
  have hmid_val : ∀ j : ℕ, 1 ≤ j → j ≤ k - 2 → padicValInt p (ud j) < e := by
    intro j hj1 hj2
    apply padicValInt_lt_of_not_dvd hp (hudne j (by omega))
    simp only [hud]
    rw [hAext_eq j (by omega), hOk, hAext_eq k (by omega)]
    apply hdiag' j k (by omega) (by omega) (by omega)
    · rw [Nat.mod_eq_of_lt (by omega : j + 1 < k + 1)]
      omega
    · rw [Nat.mod_self]
      omega
  have hdd_val : padicValInt p dd < e := by
    apply padicValInt_lt_of_not_dvd hp hddne
    simp only [hdd]
    rw [hAext_eq 0 (by omega), hAext_eq (k - 1) (by omega)]
    apply hdiag' 0 (k - 1) (by omega) (by omega) (by omega)
    · rw [Nat.mod_eq_of_lt (by omega : 1 < k + 1)]
      omega
    · rw [show (k - 1 + 1) % (k + 1) = k from by
        rw [show k - 1 + 1 = k by omega]
        exact Nat.mod_eq_of_lt (Nat.lt_succ_self k)]
      omega
  have hval_qq : ∀ j : ℕ, j ≤ k - 2 → padicValRat p (qq j) =
      (padicValInt p (sd j) : ℤ) -
        ((padicValInt p (ud j) : ℤ) + (padicValInt p (ud (j + 1)) : ℤ)) := by
    intro j hj
    rw [hcast_qq j,
      padicValRat.div (by exact_mod_cast hsdne j hj) (by
        exact mul_ne_zero (by exact_mod_cast hudne j (by omega))
          (by exact_mod_cast hudne (j + 1) (by omega))),
      padicValRat.mul (by exact_mod_cast hudne j (by omega))
        (by exact_mod_cast hudne (j + 1) (by omega))]
    simp only [padicValRat.of_int]
  have hval_qe : padicValRat p qe = (padicValInt p dd : ℤ) -
      ((padicValInt p (ud 0) : ℤ) + (padicValInt p (ud (k - 1)) : ℤ)) := by
    rw [hcast_qe,
      padicValRat.div (by exact_mod_cast hddne) (by
        exact mul_ne_zero (by exact_mod_cast hudne 0 (by omega))
          (by exact_mod_cast hudne (k - 1) (by omega))),
      padicValRat.mul (by exact_mod_cast hudne 0 (by omega))
        (by exact_mod_cast hudne (k - 1) (by omega))]
    simp only [padicValRat.of_int]
  have hval_final : ∀ j : ℕ, j ≤ k - 2 → 1 ≤ padicValRat p (rr j) := by
    intro j hj
    have h1 : padicValRat p (rr j) = padicValRat p (qq j) - padicValRat p qe := by
      simp only [hrr]
      exact padicValRat.div (ne_of_gt (hqqpos j (Finset.mem_range.mpr (by omega))))
        (ne_of_gt hqepos)
    rw [h1, hval_qq j hj, hval_qe]
    have cast_le : ∀ x : ℕ, e ≤ x → (e : ℤ) ≤ (x : ℤ) := fun x h => Nat.cast_le.mpr h
    have cast_lt : ∀ x : ℕ, x < e → (x : ℤ) ≤ (e : ℤ) - 1 := by
      intro x h
      have h2 : x ≤ e - 1 := Nat.le_pred_of_lt h
      have h3 : (x : ℤ) ≤ ((e - 1 : ℕ) : ℤ) := Nat.cast_le.mpr h2
      have h4 : ((e - 1 : ℕ) : ℤ) = (e : ℤ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ e)]
        simp
      rwa [h4] at h3
    by_cases hj0 : j = 0
    · subst hj0
      have b1 := cast_le _ (hside_val 0 (by omega))
      have b2 := cast_lt _ (hmid_val 1 (by omega) (by omega))
      have b3 := cast_lt _ hdd_val
      have b4 := cast_le _ hudk_val
      linarith
    · by_cases hje : j = k - 2
      · subst hje
        have hmk : k - 2 + 1 = k - 1 := by omega
        rw [hmk]
        have b1 := cast_le _ (hside_val (k - 2) (by omega))
        have b2 := cast_lt _ (hmid_val (k - 2) (by omega) (by omega))
        have b3 := cast_lt _ hdd_val
        have b4 := cast_le _ hud0_val
        have b5 := cast_le _ hudk_val
        linarith
      · have hj1 : 1 ≤ j := by omega
        have hj3 : j ≤ k - 3 := by omega
        have b1 := cast_le _ (hside_val j hj)
        have b2 := cast_lt _ (hmid_val j hj1 (by omega))
        have b3 := cast_lt _ (hmid_val (j + 1) (by omega) (by omega))
        have b4 := cast_lt _ hdd_val
        have b5 := cast_le _ hud0_val
        have b6 := cast_le _ hudk_val
        linarith
  have hval : ∀ i : Fin (k - 1), 1 ≤ padicValRat p (rr i.1) := by
    intro i
    exact hval_final i.1 (by have := i.isLt; omega)
  have hrposFin : ∀ i : Fin (k - 1), 0 < rr i.1 := by
    intro i
    exact hrpos i.1 (Finset.mem_range.mpr i.isLt)
  have hεi : ∀ i : Fin (k - 1), ε i.1 = 1 ∨ ε i.1 = -1 := by
    intro i
    simp only [hε]
    split_ifs <;> simp
  have hσi : σ = 1 ∨ σ = -1 := by
    simp only [hσ]
    split_ifs <;> simp
  exact sum_signed_sqrt_ne_one_of_padicValRat hp hrposFin hval hεi hσi hrelFin

theorem exists_good_diag {k : ℕ} (hk : 3 ≤ k) (A : Fin (k + 1) → ℤ × ℤ)
    (hA : Function.Injective A) (c : ℚ × ℚ) (ρ : ℚ)
    (hcircle : ∀ i, (((A i).1 : ℚ) - c.1) ^ 2 + (((A i).2 : ℚ) - c.2) ^ 2 = ρ)
    {p : ℕ} (hp : p.Prime) {e : ℕ} (he : 1 ≤ e)
    (hsides : ∀ i : Fin (k + 1), (p : ℤ) ^ e ∣ distSq (A i) (A (finRotate (k + 1) i))) :
    ∃ a b : Fin (k + 1), a ≠ b ∧ b ≠ a + 1 ∧ a ≠ b + 1 ∧
      (p : ℤ) ^ e ∣ distSq (A a) (A b) := by
  by_contra h
  push Not at h
  exact no_good_diag_absurd hk A hA c ρ hcircle hp he hsides h

/-!
### The main induction: prime powers
-/

theorem prime_power_case {p : ℕ} (hp : p.Prime) (hpo : Odd p) {e : ℕ} (he : 1 ≤ e)
    {k : ℕ} (hk : 1 ≤ k) (A : Fin k → ℤ × ℤ) (c : ℚ × ℚ) (ρ : ℚ)
    (hA : Function.Injective A)
    (hcircle : ∀ i, (((A i).1 : ℚ) - c.1) ^ 2 + (((A i).2 : ℚ) - c.2) ^ 2 = ρ)
    (hsides : ∀ i : Fin k, (p : ℤ) ^ e ∣ distSq (A i) (A (finRotate k i))) :
    (p : ℤ) ^ e ∣ shoelace A := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  clear hk
  revert hsides hcircle hA ρ c A
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro c ρ A hA hcircle hsides
    rcases (by omega : k ≤ 2 ∨ 3 ≤ k) with hk | hk
    · interval_cases k
      · rw [shoelace_of_le_two (by omega : 1 ≤ 2) A]
        exact dvd_zero _
      · rw [shoelace_of_le_two (by omega : 2 ≤ 2) A]
        exact dvd_zero _
      · exact heron_case hp hpo e A hsides
    · obtain ⟨a, b, hab, hb1, hb2, hgood⟩ :=
        exists_good_diag hk A hA c ρ hcircle hp he hsides
      have hrot_ne_self : ∀ x : Fin (k + 1), finRotate (k + 1) x ≠ x := by
        intro x hx
        have h1 := congrArg Fin.val hx
        rw [finRotate_apply] at h1
        simp only [Fin.val_add, Fin.val_one', Nat.mod_mod] at h1
        rw [Nat.add_mod_mod] at h1
        by_cases h2 : x.val < k
        · rw [Nat.mod_eq_of_lt (by omega : x.val + 1 < k + 1)] at h1
          omega
        · have h3 : x.val = k := by omega
          rw [h3, Nat.mod_self] at h1
          omega
      set t : Fin (k + 1) := b - a with ht
      have htlt : t.val < k + 1 := t.isLt
      have ht0 : t ≠ 0 := by
        intro h
        rw [ht] at h
        exact hab (sub_eq_zero.mp h).symm
      have ht1 : t ≠ 1 := by
        intro h
        rw [ht] at h
        apply hb1
        have h2 : b = 1 + a := sub_eq_iff_eq_add.mp h
        rw [add_comm (1 : Fin (k + 1)) a] at h2
        exact h2
      have htl : t ≠ -1 := by
        intro h
        rw [ht] at h
        apply hb2
        have h2 : a - b = 1 := by
          have h3 : b - a = -1 := h
          have h4 : -(b - a) = 1 := by rw [h3, neg_neg]
          rw [neg_sub] at h4
          exact h4
        have h3 : a = 1 + b := sub_eq_iff_eq_add.mp h2
        rw [add_comm (1 : Fin (k + 1)) b] at h3
        exact h3
      have htval0 : t.val ≠ 0 := by
        intro h
        exact ht0 (Fin.ext h)
      have htval1 : t.val ≠ 1 := by
        intro h
        apply ht1
        apply Fin.ext
        simp only [h, Fin.val_one']
        exact (Nat.mod_eq_of_lt (by omega : 1 < k + 1)).symm
      have hneg1 : (-1 : Fin (k + 1)).val = k := by
        have h1 : Fin.last k + 1 = (0 : Fin (k + 1)) := by
          rw [← finRotate_apply]
          exact finRotate_last
        have h2 : (-1 : Fin (k + 1)) = Fin.last k := (eq_neg_of_add_eq_zero_left h1).symm
        rw [h2]
        exact Fin.val_last k
      have htvalk : t.val ≠ k := by
        intro h
        apply htl
        apply Fin.ext
        rw [h, hneg1]
      have htval : 2 ≤ t.val ∧ t.val ≤ k - 1 := by
        have := t.isLt
        omega
      set A' : Fin (k + 1) → ℤ × ℤ := fun i => A (i + a) with hA'
      have hA'inj : Function.Injective A' := by
        rw [hA', show (fun i => A (i + a)) = A ∘ finCycle a from
          funext fun i => by simp only [Function.comp_apply, finCycle_apply]]
        exact hA.comp (finCycle a).injective
      have hcircle' : ∀ i, (((A' i).1 : ℚ) - c.1) ^ 2 + (((A' i).2 : ℚ) - c.2) ^ 2 = ρ :=
        fun i => hcircle (i + a)
      have hsides' : ∀ i : Fin (k + 1), (p : ℤ) ^ e ∣ distSq (A' i) (A' (finRotate (k + 1) i)) := by
        intro i
        have h1 : A' (finRotate (k + 1) i) = A (finRotate (k + 1) (i + a)) := by
          simp only [hA', finRotate_apply]
          congr 1
          rw [add_assoc, add_comm (1 : Fin (k + 1)) a, ← add_assoc]
        rw [h1]
        exact hsides (i + a)
      have hshoelace : shoelace A' = shoelace A := shoelace_rotate A a
      have hgood' : (p : ℤ) ^ e ∣ distSq (A' 0) (A' t) := by
        have e1 : A' 0 = A a := by simp only [hA', zero_add]
        have e2 : A' t = A b := by
          simp only [hA', ht]
          congr 1
          exact sub_add_cancel b a
        rw [e1, e2]
        exact hgood
      have hsplit := shoelace_split A' htval.1 (by omega : t.val ≤ (k + 1) - 2)
      rw [hshoelace] at hsplit
      rw [hsplit]
      apply dvd_add
      · refine ih t.val (by omega) c ρ _ ?_ ?_ ?_
        · apply Function.Injective.comp hA'inj
          intro i j h
          have h2 := congrArg Fin.val h
          exact Fin.ext h2
        · intro i
          exact hcircle' ⟨i.1, by have := i.isLt; omega⟩
        · intro i
          by_cases hi : i.val < t.val
          · have e2 : finRotate (t.val + 1) i = ⟨i.val + 1, by omega⟩ := by
              rw [finRotate_apply]
              apply Fin.ext
              exact Fin.val_add_one_of_lt' (by omega)
            have idx2 : (⟨↑((finRotate (↑t + 1)) i),
                  by have := (finRotate (↑t + 1) i).isLt; have := htlt; omega⟩ : Fin (k + 1)) =
                finRotate (k + 1) ⟨↑i, by omega⟩ := by
              apply Fin.ext
              show (↑((finRotate (↑t + 1)) i) : ℕ) = ↑(finRotate (k + 1) ⟨↑i, by omega⟩)
              have e2v : ↑(finRotate (↑t + 1) i) = i.val + 1 := congrArg Fin.val e2
              rw [e2v, finRotate_apply]
              simp only [Fin.val_add, Fin.val_one', Nat.mod_mod]
              rw [Nat.add_mod_mod]
              exact (Nat.mod_eq_of_lt (by omega : i.val + 1 < k + 1)).symm
            rw [idx2]
            exact hsides' ⟨i.val, by omega⟩
          · have hi2 : i.val = t.val := by
              have := i.isLt
              omega
            have ei : i = Fin.last t.val := by
              apply Fin.ext
              rw [hi2, Fin.val_last]
            have e2 : finRotate (t.val + 1) i = 0 := by
              rw [ei, finRotate_last]
            have idx1 : (⟨↑i, by omega⟩ : Fin (k + 1)) = t := by
              apply Fin.ext
              exact hi2
            have idx2 : (⟨↑((finRotate (↑t + 1)) i),
                  by have := (finRotate (↑t + 1) i).isLt; have := htlt; omega⟩ : Fin (k + 1)) =
                ⟨0, by omega⟩ := by
              apply Fin.ext
              show (↑((finRotate (↑t + 1)) i) : ℕ) = ((0 : Fin (k + 1)) : ℕ)
              exact congrArg Fin.val e2
            rw [idx1, idx2, distSq_comm]
            exact hgood'
      · refine ih ((k + 1) - t.val) (by omega) c ρ _ ?_ ?_ ?_
        · apply Function.Injective.comp hA'inj
          intro i j h
          have h2 := congrArg Fin.val h
          change (t.val + i.1) % (k + 1) = (t.val + j.1) % (k + 1) at h2
          have hi := i.isLt
          have hj := j.isLt
          by_cases hi3 : i.1 < (k + 1) - t.val
          · by_cases hj3 : j.1 < (k + 1) - t.val
            · rw [Nat.mod_eq_of_lt (by omega : t.val + i.1 < k + 1),
                Nat.mod_eq_of_lt (by omega : t.val + j.1 < k + 1)] at h2
              exact Fin.ext (by omega)
            · have hj4 : j.1 = (k + 1) - t.val := by omega
              rw [hj4, show t.val + ((k + 1) - t.val) = k + 1 by omega, Nat.mod_self,
                Nat.mod_eq_of_lt (by omega : t.val + i.1 < k + 1)] at h2
              omega
          · have hi4 : i.1 = (k + 1) - t.val := by omega
            by_cases hj3 : j.1 < (k + 1) - t.val
            · rw [hi4, show t.val + ((k + 1) - t.val) = k + 1 by omega, Nat.mod_self,
                Nat.mod_eq_of_lt (by omega : t.val + j.1 < k + 1)] at h2
              omega
            · exact Fin.ext (by omega)
        · intro i
          exact hcircle' ⟨(t.val + i.1) % (k + 1), Nat.mod_lt _ (by omega)⟩
        · intro i
          by_cases hi : i.1 < (k + 1) - t.val
          · have e2 : finRotate ((k + 1) - t.val + 1) i = ⟨i.1 + 1, by omega⟩ := by
              rw [finRotate_apply]
              apply Fin.ext
              exact Fin.val_add_one_of_lt' (by omega)
            by_cases hi2 : i.1 < k - t.val
            · have idx1 : (⟨(t.val + i.1) % (k + 1), Nat.mod_lt _ (by omega)⟩ : Fin (k + 1)) =
                  ⟨t.val + i.1, by omega⟩ := by
                apply Fin.ext
                exact Nat.mod_eq_of_lt (by omega)
              have idx2 : (⟨(t.val + ↑((finRotate ((k + 1) - t.val).succ) i)) % (k + 1),
                    Nat.mod_lt _ (by omega)⟩ : Fin (k + 1)) =
                  finRotate (k + 1) ⟨t.val + i.1, by omega⟩ := by
                apply Fin.ext
                show (t.val + ↑((finRotate ((k + 1) - t.val).succ) i)) % (k + 1) =
                  ↑(finRotate (k + 1) ⟨t.val + i.1, by omega⟩)
                have e2v : ↑((finRotate ((k + 1) - t.val).succ) i) = i.1 + 1 :=
                  congrArg Fin.val e2
                rw [e2v, finRotate_apply]
                simp only [Fin.val_add, Fin.val_one', Nat.mod_mod]
                rw [Nat.add_mod_mod, show t.val + (i.1 + 1) = t.val + i.1 + 1 by omega]
              rw [idx1, idx2]
              exact hsides' ⟨t.val + i.1, by omega⟩
            · have hi3 : i.1 = k - t.val := by omega
              have idx1 : (⟨(t.val + i.1) % (k + 1), Nat.mod_lt _ (by omega)⟩ : Fin (k + 1)) =
                  ⟨k, by omega⟩ := by
                apply Fin.ext
                rw [hi3, show t.val + (k - t.val) = k by omega]
                exact Nat.mod_eq_of_lt (Nat.lt_succ_self k)
              have idx2 : (⟨(t.val + ↑((finRotate ((k + 1) - t.val).succ) i)) % (k + 1),
                    Nat.mod_lt _ (by omega)⟩ : Fin (k + 1)) =
                  finRotate (k + 1) ⟨k, by omega⟩ := by
                apply Fin.ext
                show (t.val + ↑((finRotate ((k + 1) - t.val).succ) i)) % (k + 1) =
                  ↑(finRotate (k + 1) ⟨k, by omega⟩)
                have e2v : ↑((finRotate ((k + 1) - t.val).succ) i) = i.1 + 1 :=
                  congrArg Fin.val e2
                rw [e2v, finRotate_apply]
                simp only [Fin.val_add, Fin.val_one', Nat.mod_mod]
                rw [Nat.add_mod_mod, hi3, show t.val + (k - t.val + 1) = k + 1 by omega,
                  Nat.mod_self]
              rw [idx1, idx2]
              exact hsides' ⟨k, by omega⟩
          · have hi2 : i.1 = (k + 1) - t.val := by
              have := i.isLt
              omega
            have ei : i = Fin.last ((k + 1) - t.val) := by
              apply Fin.ext
              rw [hi2, Fin.val_last]
            have e2v : (↑((finRotate ((k + 1) - t.val + 1)) i) : ℕ) = 0 := by
              rw [show (finRotate ((k + 1) - t.val + 1)) i =
                  finRotate ((k + 1) - t.val + 1) (Fin.last ((k + 1) - t.val)) from by
                rw [ei]]
              exact congrArg Fin.val (finRotate_last (n := (k + 1) - t.val))
            have idx1 : (⟨(t.val + i.1) % (k + 1), Nat.mod_lt _ (by omega)⟩ : Fin (k + 1)) =
                ⟨0, by omega⟩ := by
              apply Fin.ext
              show (t.val + i.1) % (k + 1) = (0 : ℕ)
              rw [hi2, show t.val + ((k + 1) - t.val) = k + 1 by omega, Nat.mod_self]
            have idx2 : (⟨(t.val + ↑((finRotate ((k + 1) - t.val).succ) i)) % (k + 1),
                  Nat.mod_lt _ (by omega)⟩ : Fin (k + 1)) = t := by
              apply Fin.ext
              show (t.val + (↑((finRotate ((k + 1) - t.val + 1)) i) : ℕ)) % (k + 1) = t.val
              rw [e2v]
              exact Nat.mod_eq_of_lt htlt
            rw [idx1, idx2]
            exact hgood'

/-!
### Reduction from odd `n` to prime powers
-/

theorem odd_case {n : ℕ} (hn : Odd n) (hn1 : 1 ≤ n) {k : ℕ} (A : Fin k → ℤ × ℤ)
    (hA : Function.Injective A) (c : ℚ × ℚ) (ρ : ℚ)
    (hcircle : ∀ i, (((A i).1 : ℚ) - c.1) ^ 2 + (((A i).2 : ℚ) - c.2) ^ 2 = ρ)
    (hsides : ∀ i : Fin k, (n : ℤ) ∣ distSq (A i) (A (finRotate k i))) :
    (n : ℤ) ∣ shoelace A := by
  by_cases hk0 : k = 0
  · subst hk0
    rw [shoelace_of_le_two (by omega : 0 ≤ 2) A]
    exact dvd_zero _
  · have hk1 : 1 ≤ k := by omega
    have hgoal : n ∣ (shoelace A).natAbs := by
      by_cases hs0 : (shoelace A).natAbs = 0
      · rw [hs0]
        exact dvd_zero _
      · rw [← Nat.factorization_le_iff_dvd (by omega : n ≠ 0) hs0, Finsupp.le_def]
        intro q
        by_cases hq : q ∈ n.primeFactors
        · rw [Nat.mem_primeFactors] at hq
          obtain ⟨hqp, hqdiv, hn0⟩ := hq
          have hodd : Odd q := by
            rcases Nat.Prime.eq_two_or_odd hqp with (rfl | h)
            · exfalso
              have h2 : ¬ 2 ∣ n := by
                rcases hn with ⟨m, hm⟩
                omega
              exact h2 hqdiv
            · exact Nat.odd_iff.mpr h
          have he : 1 ≤ n.factorization q := Nat.Prime.factorization_pos_of_dvd hqp hn0 hqdiv
          rw [← Nat.Prime.pow_dvd_iff_le_factorization hqp hs0]
          have hsides' : ∀ i : Fin k, (q : ℤ) ^ n.factorization q ∣
              distSq (A i) (A (finRotate k i)) := by
            intro i
            exact dvd_trans (by exact_mod_cast Nat.ordProj_dvd n q) (hsides i)
          have hdvd := prime_power_case hqp hodd he hk1 A c ρ hA hcircle hsides'
          have hdvd2 : q ^ n.factorization q ∣ (shoelace A).natAbs := by
            have h1 := Int.natAbs_dvd_natAbs.mpr hdvd
            rw [Int.natAbs_pow, Int.natAbs_natCast] at h1
            exact_mod_cast h1
          exact hdvd2
        · rw [Nat.mem_primeFactors] at hq
          push Not at hq
          have hf : n.factorization q = 0 := by
            by_cases hq2 : q.Prime
            · have hq3 : ¬ q ∣ n := by
                intro hd
                exact absurd (hq hq2 hd) (by omega)
              exact Nat.factorization_eq_zero_of_not_dvd hq3
            · exact Nat.factorization_eq_zero_of_not_prime n hq2
          rw [hf]
          exact Nat.zero_le _
    exact Int.dvd_natAbs.mp (by exact_mod_cast hgoal)

end

snip end

problem imo2016_p3 {k : ℕ} (A : Fin k → ℤ × ℤ) (hA : Function.Injective A)
    {n : ℕ} (hn : Odd n) (hn1 : 1 ≤ n)
    (hcircle : ∃ c : ℚ × ℚ, ∃ ρ : ℚ, ∀ i,
      (((A i).1 : ℚ) - c.1) ^ 2 + (((A i).2 : ℚ) - c.2) ^ 2 = ρ)
    (hsides : ∀ i : Fin k, (n : ℤ) ∣ distSq (A i) (A (finRotate k i))) :
    (n : ℤ) ∣ shoelace A := by
  obtain ⟨c, ρ, hc⟩ := hcircle
  exact odd_case hn hn1 A hA c ρ hc hsides

end Imo2016P3
