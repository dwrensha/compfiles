/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Data.Int.Star
public import Mathlib.Data.Rat.Star
public import Mathlib.RingTheory.Int.Basic
public import Mathlib.RingTheory.Polynomial.GaussLemma
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.NumberTheory] }

/-!
# USA Mathematical Olympiad 2006, Problem 3

For integral m, let p(m) be the greatest prime divisor of m. By convention,
we set p(±1) = 1 and p(0) = ∞. Find all polynomials f with integer
coefficients such that the sequence

    {p(f(n²)) − 2n},  n = 0, 1, 2, ...

is bounded above. (In particular, this requires f(n²) ≠ 0 for n ≥ 0.)
-/

namespace Usa2006P3

open Polynomial

snip begin

/-- The greatest prime divisor of an integer `m`, with the convention
`gpd (±1) = 1`. (The value at `0` is irrelevant for the problem, which
requires `f(n²) ≠ 0` anyway.) -/
noncomputable def gpd (m : ℤ) : ℕ := (m.natAbs.primeFactors.max).unbotD 1

/-- The condition that the sequence `p(f(n²)) − 2n` is bounded above
(and defined for every `n`). -/
def BddCond (f : ℤ[X]) : Prop :=
  ∃ B : ℤ, ∀ n : ℕ, f.eval ((n : ℤ) ^ 2) ≠ 0 ∧
    ((gpd (f.eval ((n : ℤ) ^ 2)) : ℤ) - 2 * n ≤ B)

/-- The classification: `f` is a nonzero constant times a (possibly empty)
product of factors `4X − a²` with `a` an odd integer. -/
def Classification (f : ℤ[X]) : Prop :=
  ∃ (c : ℤ) (L : List ℤ), c ≠ 0 ∧ (∀ a ∈ L, Odd a) ∧
    f = C c * (L.map fun a ↦ C 4 * X - C (a ^ 2)).prod

/-- An auxiliary formulation of boundedness: every prime divisor of
`f(n²)` is at most `2n + B`. -/
def Pbound (f : ℤ[X]) (B : ℕ) : Prop :=
  ∀ n : ℕ, f.eval ((n : ℤ) ^ 2) ≠ 0 ∧
    ∀ q : ℕ, q.Prime → (q : ℤ) ∣ f.eval ((n : ℤ) ^ 2) → q ≤ 2 * n + B

lemma gpd_eq_max' {m : ℤ} (h : m.natAbs.primeFactors.Nonempty) :
    gpd m = m.natAbs.primeFactors.max' h := by
  rw [gpd, ← Finset.coe_max', WithBot.unbotD_coe]

lemma gpd_eq_one_of_not_nonempty {m : ℤ} (h : ¬ m.natAbs.primeFactors.Nonempty) :
    gpd m = 1 := by
  rw [Finset.not_nonempty_iff_eq_empty] at h
  rw [gpd, h, Finset.max_empty, WithBot.unbotD_bot]

/-- The two formulations of the boundedness condition agree. -/
lemma bddCond_iff (f : ℤ[X]) : BddCond f ↔ ∃ B, Pbound f B := by
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨B.toNat, fun n ↦ ⟨(hB n).1, fun q hq hdvd ↦ ?_⟩⟩
    have hne := (hB n).1
    have hqmem : q ∈ (f.eval ((n : ℤ) ^ 2)).natAbs.primeFactors := by
      rw [Nat.mem_primeFactors]
      refine ⟨hq, ?_, Int.natAbs_ne_zero.mpr hne⟩
      have h1 : (q : ℤ).natAbs ∣ (f.eval ((n : ℤ) ^ 2)).natAbs :=
        Int.natAbs_dvd_natAbs.mpr hdvd
      rwa [Int.natAbs_natCast] at h1
    have hnonempty : (f.eval ((n : ℤ) ^ 2)).natAbs.primeFactors.Nonempty := ⟨q, hqmem⟩
    have hqle : q ≤ gpd (f.eval ((n : ℤ) ^ 2)) := by
      rw [gpd_eq_max' hnonempty]
      exact Finset.le_max' _ _ hqmem
    have h2 := (hB n).2
    have h3 : (q : ℤ) ≤ 2 * n + B := by
      have hg : ((gpd (f.eval ((n : ℤ) ^ 2)) : ℕ) : ℤ) ≤ 2 * n + B := by linarith
      exact le_trans (by exact_mod_cast hqle) hg
    have h4 : (q : ℤ) ≤ ((2 * n + B.toNat : ℕ) : ℤ) := by
      push_cast
      by_cases hB0 : 0 ≤ B
      · rw [Int.toNat_of_nonneg hB0]
        linarith
      · rw [Int.toNat_of_nonpos (not_le.mp hB0).le]
        push_cast
        linarith
    exact_mod_cast h4
  · rintro ⟨B, hB⟩
    refine ⟨max (B : ℤ) 1, fun n ↦ ⟨(hB n).1, ?_⟩⟩
    by_cases he : (f.eval ((n : ℤ) ^ 2)).natAbs.primeFactors.Nonempty
    · have hgpd : gpd (f.eval ((n : ℤ) ^ 2)) =
          (f.eval ((n : ℤ) ^ 2)).natAbs.primeFactors.max' he := gpd_eq_max' he
      have hqmem : (f.eval ((n : ℤ) ^ 2)).natAbs.primeFactors.max' he ∈
          (f.eval ((n : ℤ) ^ 2)).natAbs.primeFactors := Finset.max'_mem _ _
      rw [Nat.mem_primeFactors] at hqmem
      obtain ⟨hqp, hqd, _⟩ := hqmem
      have h1 : ((f.eval ((n : ℤ) ^ 2)).natAbs.primeFactors.max' he : ℤ) ∣
          f.eval ((n : ℤ) ^ 2) := by
        have h2 : (((f.eval ((n : ℤ) ^ 2)).natAbs.primeFactors.max' he : ℤ)).natAbs ∣
            (f.eval ((n : ℤ) ^ 2)).natAbs := by
          rw [Int.natAbs_natCast]
          exact hqd
        exact Int.natAbs_dvd_natAbs.mp h2
      have hqle := (hB n).2 _ hqp h1
      have h3 : ((gpd (f.eval ((n : ℤ) ^ 2)) : ℕ) : ℤ) =
          ((f.eval ((n : ℤ) ^ 2)).natAbs.primeFactors.max' he : ℕ) := by
        exact_mod_cast hgpd
      have h4 : (((f.eval ((n : ℤ) ^ 2)).natAbs.primeFactors.max' he : ℕ) : ℤ) ≤
          2 * n + (B : ℤ) := by exact_mod_cast hqle
      linarith [le_max_left (B : ℤ) 1]
    · have hgpd : gpd (f.eval ((n : ℤ) ^ 2)) = 1 := gpd_eq_one_of_not_nonempty he
      have h3 : ((gpd (f.eval ((n : ℤ) ^ 2)) : ℕ) : ℤ) = 1 := by exact_mod_cast hgpd
      linarith [le_max_right (B : ℤ) 1]

lemma natAbs_list_prod (L : List ℤ) :
    (L.prod).natAbs = (L.map Int.natAbs).prod := by
  induction L with
  | nil => simp
  | cons a l ih => simp [List.prod_cons, Int.natAbs_mul, ih]

lemma prime_dvd_list_prod {q : ℕ} (hq : q.Prime) (L : List ℕ)
    (h : q ∣ L.prod) : ∃ a ∈ L, q ∣ a := by
  induction L with
  | nil =>
    simp only [List.prod_nil] at h
    exact absurd (Nat.dvd_one.mp h) hq.ne_one
  | cons b l ih =>
    rw [List.prod_cons] at h
    rcases (Nat.Prime.dvd_mul hq).mp h with h | h
    · exact ⟨b, List.mem_cons_self, h⟩
    · obtain ⟨a, ha, hd⟩ := ih h
      exact ⟨a, List.mem_cons_of_mem b ha, hd⟩

lemma eval_factor (a x : ℤ) :
    (C 4 * X - C (a ^ 2)).eval x = 4 * x - a ^ 2 := by
  simp [eval_sub, eval_mul]

lemma eval_prod_factors (L : List ℤ) (x : ℤ) :
    ((L.map fun a ↦ C 4 * X - C (a ^ 2)).prod).eval x =
      (L.map fun a ↦ 4 * x - a ^ 2).prod := by
  induction L with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons, eval_mul, ih,
      eval_factor]

lemma factor_eq (a n : ℤ) : 4 * n ^ 2 - a ^ 2 = (2 * n - a) * (2 * n + a) := by ring

lemma odd_ne_even {a : ℤ} (ho : Odd a) (he : Even a) : False := by
  obtain ⟨k, hk⟩ := ho
  obtain ⟨m, hm⟩ := he
  omega

lemma odd_sq_sub_four_mul_ne_zero {a : ℤ} (ha : Odd a) (n : ℤ) :
    4 * n ^ 2 - a ^ 2 ≠ 0 := by
  intro hzero
  have hsq : a ^ 2 = (2 * n) ^ 2 := by linarith
  rw [sq_eq_sq_iff_eq_or_eq_neg] at hsq
  rcases hsq with h | h
  · exact odd_ne_even ha ⟨n, by linarith⟩
  · exact odd_ne_even ha ⟨-n, by linarith⟩

/-- The easy direction: every polynomial of the classified form satisfies
the boundedness condition. -/
lemma pbound_of_classification (f : ℤ[X]) (h : Classification f) :
    ∃ B, Pbound f B := by
  obtain ⟨c, L, hc, ho, rfl⟩ := h
  refine ⟨c.natAbs + ∑ a ∈ L.toFinset, a.natAbs, fun n ↦ ⟨?_, ?_⟩⟩
  · rw [eval_mul, eval_C, eval_prod_factors]
    apply mul_ne_zero hc
    apply List.prod_ne_zero
    intro hx
    rw [List.mem_map] at hx
    obtain ⟨a, ha, h0⟩ := hx
    exact odd_sq_sub_four_mul_ne_zero (ho a ha) _ h0
  · intro q hq hdvd
    rw [eval_mul, eval_C, eval_prod_factors] at hdvd
    have h1 : q ∣ c.natAbs * ((L.map fun a ↦ 4 * (n : ℤ) ^ 2 - a ^ 2).map
        Int.natAbs).prod := by
      have h2 : (q : ℤ).natAbs ∣ _ := Int.natAbs_dvd_natAbs.mpr hdvd
      rwa [Int.natAbs_natCast, Int.natAbs_mul, natAbs_list_prod] at h2
    rcases (Nat.Prime.dvd_mul hq).mp h1 with hcase | hcase
    · have hle : q ≤ c.natAbs := Nat.le_of_dvd (Int.natAbs_pos.mpr hc) hcase
      omega
    · rw [List.map_map] at hcase
      obtain ⟨b, hb, hqb⟩ := prime_dvd_list_prod hq _ hcase
      rw [List.mem_map] at hb
      obtain ⟨a, ha, rfl⟩ := hb
      have hle3 : a.natAbs ≤ ∑ x ∈ L.toFinset, x.natAbs :=
        Finset.single_le_sum (fun x _ ↦ Nat.zero_le _) (by simpa using ha)
      simp only [Function.comp_apply] at hqb
      rw [factor_eq, Int.natAbs_mul] at hqb
      have hnat : (2 * (n : ℤ)).natAbs = 2 * n := by
        rw [show (2 * (n : ℤ)) = ((2 * n : ℕ) : ℤ) by push_cast; ring]
        exact Int.natAbs_natCast _
      rcases (Nat.Prime.dvd_mul hq).mp hqb with h | h
      · have hne : (2 * (n : ℤ) - a) ≠ 0 := by
          intro hz
          exact odd_ne_even (ho a ha) ⟨n, by linarith⟩
        have hle : q ≤ (2 * (n : ℤ) - a).natAbs :=
          Nat.le_of_dvd (Int.natAbs_pos.mpr hne) h
        have hle2 : (2 * (n : ℤ) - a).natAbs ≤ 2 * n + a.natAbs := by
          have h3 : (2 * (n : ℤ) - a).natAbs ≤ (2 * (n : ℤ)).natAbs + (-a).natAbs := by
            have h4 : (2 * (n : ℤ) - a) = (2 * (n : ℤ)) + (-a) := by ring
            rw [h4]
            exact Int.natAbs_add_le _ _
          rwa [Int.natAbs_neg, hnat] at h3
        omega
      · have hne : (2 * (n : ℤ) + a) ≠ 0 := by
          intro hz
          exact odd_ne_even (ho a ha) ⟨-n, by linarith⟩
        have hle : q ≤ (2 * (n : ℤ) + a).natAbs :=
          Nat.le_of_dvd (Int.natAbs_pos.mpr hne) h
        have hle2 : (2 * (n : ℤ) + a).natAbs ≤ 2 * n + a.natAbs := by
          have h3 := Int.natAbs_add_le (2 * (n : ℤ)) a
          rwa [hnat] at h3
        omega

/-- **Schur's theorem**: a nonconstant polynomial with integer coefficients
takes some value divisible by a prime outside any given finite set of primes. -/
lemma schur (h : ℤ[X]) (hd : h.natDegree ≠ 0) (s : Finset ℕ) (hs : ∀ q ∈ s, q.Prime) :
    ∃ q : ℕ, q.Prime ∧ q ∉ s ∧ ∃ m : ℕ, (q : ℤ) ∣ h.eval (m : ℤ) := by
  classical
  by_cases hc0 : h.eval 0 = 0
  · -- If `h(0) = 0` then `X ∣ h`, so every prime `q` divides `h(q)`.
    have hcoeff : h.coeff 0 = 0 := by rw [coeff_zero_eq_eval_zero]; exact hc0
    obtain ⟨g, hg⟩ := X_dvd_iff.mpr hcoeff
    obtain ⟨q, hqge, hq⟩ := Nat.exists_infinite_primes (s.sup id + 1)
    refine ⟨q, hq, ?_, q, ?_⟩
    · intro hmem
      have hle : q ≤ s.sup id := Finset.le_sup (f := id) hmem
      omega
    · have hev : h.eval (q : ℤ) = (q : ℤ) * g.eval (q : ℤ) := by
        rw [hg]
        simp [eval_mul, eval_X]
      rw [hev]
      exact dvd_mul_right _ _
  · -- The interesting case: `c := h(0) ≠ 0`.
    set c := h.eval 0 with hc
    have hcc : (h - C c).eval 0 = 0 := by simp [hc]
    have hcc2 : (h - C c).coeff 0 = 0 := by rw [coeff_zero_eq_eval_zero]; exact hcc
    obtain ⟨g, hg⟩ := X_dvd_iff.mpr hcc2
    -- `P`, the product of the forbidden primes.
    set P : ℤ := ∏ q₀ ∈ s, (q₀ : ℤ) with hP
    have hP0 : P ≠ 0 := by
      rw [hP, Finset.prod_ne_zero_iff]
      intro q₀ hq₀
      exact_mod_cast (hs q₀ hq₀).ne_zero
    have hPnn : 0 ≤ P := by
      rw [hP]
      exact Finset.prod_nonneg fun q₀ _ ↦ by positivity
    have hcP : c * P ≠ 0 := mul_ne_zero hc0 hP0
    -- The relevant polynomials are nonzero, so their root sets are finite.
    have hsub : (h - C c) ≠ 0 := by
      intro hh
      have hh2 : h = C c := sub_eq_zero.mp hh
      rw [hh2, natDegree_C] at hd
      exact hd rfl
    have hadd : (h + C c) ≠ 0 := by
      intro hh
      have hh2 : h = -C c := add_eq_zero_iff_eq_neg.mp hh
      rw [hh2, natDegree_neg, natDegree_C] at hd
      exact hd rfl
    have h0 : h ≠ 0 := by
      intro hh
      rw [hh, natDegree_zero] at hd
      exact hd rfl
    have hinj : Function.Injective fun t : ℤ ↦ c * P * t := fun a b hab ↦
      mul_left_cancel₀ hcP hab
    have hpre : ∀ (p : ℤ[X]) (hp : p ≠ 0),
        ((fun t : ℤ ↦ c * P * t) ⁻¹' {x : ℤ | p.eval x = 0}).Finite :=
      fun p hp ↦ Set.Finite.preimage hinj.injOn (finite_setOf_isRoot hp)
    -- The set of "bad" translations is finite.
    have e1 : {t : ℤ | h.eval (c * P * t) = c} =
        (fun t : ℤ ↦ c * P * t) ⁻¹' {x : ℤ | (h - C c).eval x = 0} := by
      ext t
      simp only [Set.mem_setOf_eq, Set.mem_preimage, eval_sub, eval_C, sub_eq_zero]
    have e2 : {t : ℤ | h.eval (c * P * t) = -c} =
        (fun t : ℤ ↦ c * P * t) ⁻¹' {x : ℤ | (h + C c).eval x = 0} := by
      ext t
      simp only [Set.mem_setOf_eq, Set.mem_preimage, eval_add, eval_C,
        eq_neg_iff_add_eq_zero]
    have hbfin : {t : ℤ | h.eval (c * P * t) = c ∨ h.eval (c * P * t) = -c ∨
        h.eval (c * P * t) = 0}.Finite := by
      have hunion : {t : ℤ | h.eval (c * P * t) = c ∨ h.eval (c * P * t) = -c ∨
          h.eval (c * P * t) = 0} = {t : ℤ | h.eval (c * P * t) = c} ∪
          ({t : ℤ | h.eval (c * P * t) = -c} ∪ {t : ℤ | h.eval (c * P * t) = 0}) := by
        ext t
        simp only [Set.mem_setOf_eq, Set.mem_union]
      rw [hunion, e1, e2]
      exact (hpre _ hsub).union ((hpre _ hadd).union (hpre _ h0))
    -- Hence we can pick a large positive translation that is not bad.
    obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ t : ℤ, h.eval (c * P * t) = c ∨ h.eval (c * P * t) = -c ∨
        h.eval (c * P * t) = 0 → t.natAbs ≤ N := by
      refine ⟨hbfin.toFinset.sup Int.natAbs, fun t ht ↦ ?_⟩
      exact Finset.le_sup (f := Int.natAbs) (hbfin.mem_toFinset.mpr ht)
    set t₀ : ℤ := (N : ℤ) + 1 with ht₀
    have ht₀pos : 0 < t₀ := by omega
    have ht₀abs : t₀.natAbs = N + 1 := by
      rw [ht₀, show ((N : ℤ) + 1) = ((N + 1 : ℕ) : ℤ) by push_cast; ring]
      exact Int.natAbs_natCast _
    have ht₀nb : ¬ (h.eval (c * P * t₀) = c ∨ h.eval (c * P * t₀) = -c ∨
        h.eval (c * P * t₀) = 0) := by
      intro ht
      have := hN t₀ ht
      omega
    have hneg_nb : ¬ (h.eval (c * P * (-t₀)) = c ∨ h.eval (c * P * (-t₀)) = -c ∨
        h.eval (c * P * (-t₀)) = 0) := by
      intro ht
      have := hN (-t₀) ht
      rw [Int.natAbs_neg, ht₀abs] at this
      omega
    -- Choose the sign so that the argument of `h` becomes nonnegative.
    have hpos₀ : 0 ≤ c.natAbs * P * t₀ :=
      mul_nonneg (mul_nonneg (Int.natCast_nonneg c.natAbs) hPnn) ht₀pos.le
    obtain ⟨t₁, hne1, hne2, hne3, hxge⟩ : ∃ t₁ : ℤ, h.eval (c * P * t₁) ≠ c ∧
        h.eval (c * P * t₁) ≠ -c ∧ h.eval (c * P * t₁) ≠ 0 ∧ 0 ≤ c * P * t₁ := by
      by_cases hcc0 : 0 ≤ c
      · refine ⟨t₀, fun hh ↦ ht₀nb (Or.inl hh), fun hh ↦ ht₀nb (Or.inr (Or.inl hh)),
          fun hh ↦ ht₀nb (Or.inr (Or.inr hh)), ?_⟩
        rw [show c * P * t₀ = c.natAbs * P * t₀ by rw [Int.natAbs_of_nonneg hcc0]]
        exact hpos₀
      · refine ⟨-t₀, fun hh ↦ hneg_nb (Or.inl hh), fun hh ↦ hneg_nb (Or.inr (Or.inl hh)),
          fun hh ↦ hneg_nb (Or.inr (Or.inr hh)), ?_⟩
        rw [show c * P * (-t₀) = c.natAbs * P * t₀ by
          rw [Int.ofNat_natAbs_of_nonpos (not_le.mp hcc0).le]; ring]
        exact hpos₀
    set x := c * P * t₁ with hx
    -- `h(x) = c · w` with `w = 1 + P·u` and `w ∉ {-1, 0, 1}`.
    have hev : h.eval x = c * (1 + P * (t₁ * g.eval x)) := by
      have h2 : h.eval x = c + x * g.eval x := by
        have h3 := congrArg (fun p : ℤ[X] ↦ p.eval x) hg
        simp only [eval_sub, eval_C, eval_mul, eval_X] at h3
        linarith
      rw [h2, hx]
      ring
    set w := 1 + P * (t₁ * g.eval x) with hw
    have hw0 : w ≠ 0 := fun h1 ↦ hne3 (by rw [hev, h1, mul_zero])
    have hw1 : w ≠ 1 := fun h1 ↦ hne1 (by rw [hev, h1, mul_one])
    have hw_1 : w ≠ -1 := fun h1 ↦ hne2 (by rw [hev, h1, mul_neg, mul_one])
    have hwabs : w.natAbs ≠ 1 := by
      intro h1
      rw [Int.natAbs_eq_iff] at h1
      rcases h1 with h1 | h1
      · exact hw1 (by exact_mod_cast h1)
      · exact hw_1 (by exact_mod_cast h1)
    -- Any prime divisor `q` of `w` is new and divides `h(x)`.
    obtain ⟨p, hpp, hpd⟩ := Int.exists_prime_and_dvd hwabs
    set q := p.natAbs with hq
    have hqp : q.Prime := Int.prime_iff_natAbs_prime.mp hpp
    have hqdw : (q : ℤ) ∣ w := by
      have h1 : p.natAbs ∣ w.natAbs := Int.natAbs_dvd_natAbs.mpr hpd
      have h2 : ((p.natAbs : ℕ) : ℤ) ∣ (w.natAbs : ℤ) := Int.ofNat_dvd.mpr h1
      exact dvd_trans h2 Int.natAbs_dvd_self
    have hqs : q ∉ s := by
      intro hmem
      have hqP : (q : ℤ) ∣ P := by
        rw [hP]
        exact Finset.dvd_prod_of_mem (fun q₀ : ℕ ↦ (q₀ : ℤ)) hmem
      have h1 : (q : ℤ) ∣ P * (t₁ * g.eval x) := dvd_mul_of_dvd_left hqP _
      have h2 : (q : ℤ) ∣ 1 := by
        have h3 := dvd_sub hqdw h1
        rwa [show w - P * (t₁ * g.eval x) = 1 by rw [hw]; abel] at h3
      have h4 : q ∣ 1 := by exact_mod_cast h2
      exact hqp.ne_one (Nat.dvd_one.mp h4)
    refine ⟨q, hqp, hqs, x.natAbs, ?_⟩
    have hx2 : ((x.natAbs : ℕ) : ℤ) = x := Int.natAbs_of_nonneg hxge
    rw [hx2, hev]
    exact dvd_mul_of_dvd_right hqdw c

/-- The integer-valued function `Fs f t = 4^d · f(t²/4)`, where
`d = f.natDegree`; the powers of `4` clear the denominators. -/
def Fs (f : ℤ[X]) (t : ℤ) : ℤ :=
  ∑ i ∈ Finset.range (f.natDegree + 1), 4 ^ (f.natDegree - i) * f.coeff i * t ^ (2 * i)

lemma Fs_two_mul (f : ℤ[X]) (t : ℤ) :
    Fs f (2 * t) = 4 ^ f.natDegree * f.eval (t ^ 2) := by
  rw [Fs, eval_eq_sum_range, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  have hi' : i ≤ f.natDegree := Nat.le_of_lt_succ hi
  have e1 : (2 * t) ^ (2 * i) = 4 ^ i * t ^ (2 * i) := by
    rw [mul_pow, pow_mul]
    norm_num
  have e2 : (4 : ℤ) ^ (f.natDegree - i) * 4 ^ i = 4 ^ f.natDegree := by
    rw [← pow_add, Nat.sub_add_cancel hi']
  rw [e1, ← pow_mul]
  calc 4 ^ (f.natDegree - i) * f.coeff i * (4 ^ i * t ^ (2 * i))
      = (4 ^ (f.natDegree - i) * 4 ^ i) * (f.coeff i * t ^ (2 * i)) := by ring
    _ = 4 ^ f.natDegree * (f.coeff i * t ^ (2 * i)) := by rw [e2]

lemma Fs_neg (f : ℤ[X]) (t : ℤ) : Fs f (-t) = Fs f t := by
  unfold Fs
  apply Finset.sum_congr rfl
  intro i _
  rw [Even.neg_pow ⟨i, two_mul i⟩ t]

lemma intModEq_sum {ι : Type*} [DecidableEq ι] (s : Finset ι) {g₁ g₂ : ι → ℤ} {n : ℤ}
    (h : ∀ i ∈ s, g₁ i ≡ g₂ i [ZMOD n]) :
    (∑ i ∈ s, g₁ i) ≡ (∑ i ∈ s, g₂ i) [ZMOD n] := by
  induction s using Finset.induction with
  | empty => exact Int.ModEq.refl _
  | insert a s has ih =>
    rw [Finset.sum_insert has, Finset.sum_insert has]
    exact Int.ModEq.add (h a (Finset.mem_insert_self a s))
      (ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi))

lemma Fs_modEq (f : ℤ[X]) {q : ℤ} {a b : ℤ} (h : a ≡ b [ZMOD q]) :
    Fs f a ≡ Fs f b [ZMOD q] :=
  intModEq_sum _ fun _ _ ↦ Int.ModEq.mul (Int.ModEq.refl _) (Int.ModEq.pow _ h)

lemma Fs_cast (f : ℤ[X]) (a : ℤ) :
    (4 : ℚ) ^ f.natDegree * (f.map (Int.castRingHom ℚ)).eval ((a : ℚ) ^ 2 / 4) =
      ((Fs f a : ℤ) : ℚ) := by
  rw [eval_eq_sum_range' (lt_of_le_of_lt natDegree_map_le (Nat.lt_succ_self _)),
    Finset.mul_sum, Fs, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  have hi' : i ≤ f.natDegree := Nat.le_of_lt_succ hi
  rw [coeff_map]
  have e : (4 : ℚ) ^ f.natDegree * ((f.coeff i : ℚ) * ((a : ℚ) ^ 2 / 4) ^ i) =
      (4 : ℚ) ^ (f.natDegree - i) * (f.coeff i : ℚ) * (a : ℚ) ^ (2 * i) := by
    have e2 : (4 : ℚ) ^ f.natDegree = 4 ^ (f.natDegree - i) * 4 ^ i := by
      rw [← pow_add, Nat.sub_add_cancel hi']
    rw [e2, div_pow, ← pow_mul]
    field_simp
  have e' : (Int.castRingHom ℚ) (f.coeff i) = (f.coeff i : ℚ) := by simp
  rw [e', e]
  push_cast
  ring

lemma eval_modEq (f : ℤ[X]) {q : ℤ} {a b : ℤ} (h : a ≡ b [ZMOD q]) :
    f.eval a ≡ f.eval b [ZMOD q] := by
  induction f using Polynomial.induction_on with
  | C r => simp only [eval_C]; exact Int.ModEq.refl _
  | add p₁ p₂ ihp ihq => simp only [eval_add]; exact Int.ModEq.add ihp ihq
  | monomial n r ih =>
    simp only [eval_mul, eval_C, eval_pow, eval_X] at ih ⊢
    simp only [pow_succ, ← mul_assoc]
    exact Int.ModEq.mul ih h

/-- If `f` is nonconstant and satisfies the prime bound, then `f` has a
root of the form `(2k+1)²/4` over `ℚ`. This is the heart of the proof:
a large prime `q` dividing `f(n²)` forces `q = 2n + 2k + 1` with `k ≤ B`,
and then `q` divides `Fs f (2k+1)`; since there are infinitely many such
primes but only finitely many possible `k`, some `Fs f (2k+1)` vanishes. -/
lemma exists_root_of_pbound (f : ℤ[X]) (hd : f.natDegree ≠ 0) (B : ℕ) (hB : Pbound f B) :
    ∃ k : ℕ, (f.map (Int.castRingHom ℚ)).eval (((2 * k + 1 : ℕ) : ℚ) ^ 2 / 4) = 0 := by
  by_contra hcon
  push Not at hcon
  -- Each integer `Fs f (2k+1)` is nonzero.
  have hFs : ∀ k : ℕ, Fs f ((2 * k + 1 : ℕ) : ℤ) ≠ 0 := by
    intro k hk
    have h1 := Fs_cast f (((2 * k + 1 : ℕ) : ℤ))
    rw [hk, Int.cast_zero, mul_eq_zero] at h1
    rcases h1 with h1 | h1
    · exact absurd h1 (pow_ne_zero _ (by norm_num : (4 : ℚ) ≠ 0))
    · rw [Int.cast_natCast] at h1
      exact hcon k h1
  -- A nonzero integer that would be divisible by every large Schur prime.
  set M : ℤ := ∏ k ∈ Finset.range (B + 1), Fs f ((2 * k + 1 : ℕ) : ℤ) with hM
  have hM0 : M ≠ 0 := by
    rw [hM, Finset.prod_ne_zero_iff]
    intro k _
    exact hFs k
  -- Schur's theorem applied to `f ∘ X²`.
  have hcomp : (f.comp (X ^ 2)).natDegree ≠ 0 := by
    rw [natDegree_comp, natDegree_X_pow]
    exact Nat.mul_ne_zero hd (by norm_num)
  obtain ⟨q, hq, hqs, m, hqm⟩ := schur (f.comp (X ^ 2)) hcomp
    (insert 2 M.natAbs.primeFactors) (by
      intro q₀ hq₀
      rw [Finset.mem_insert] at hq₀
      rcases hq₀ with rfl | hq₀
      · exact Nat.prime_two
      · exact Nat.prime_of_mem_primeFactors hq₀)
  have hqev : (q : ℤ) ∣ f.eval ((m : ℤ) ^ 2) := by
    have h1 : (f.comp (X ^ 2)).eval (m : ℤ) = f.eval ((m : ℤ) ^ 2) := by
      simp [eval_comp, eval_pow, eval_X]
    rwa [h1] at hqm
  have hq2 : q ≠ 2 := by
    intro h2
    apply hqs
    rw [h2]
    exact Finset.mem_insert_self 2 _
  have hqodd : Odd q := hq.odd_of_ne_two hq2
  -- Reduce `m` modulo `q` to a representative `n` with `2n + 1 ≤ q`.
  have hn₀lt : m % q < q := Nat.mod_lt m hq.pos
  have hmod₀ : ((m % q : ℕ) : ℤ) ≡ (m : ℤ) [ZMOD (q : ℤ)] := by
    rw [Int.modEq_iff_dvd]
    have e : (m : ℤ) = (q : ℤ) * (m / q : ℕ) + ((m % q : ℕ) : ℤ) := by
      have h1 := Nat.div_add_mod m q
      push_cast at h1 ⊢
      linarith
    rw [e, add_sub_cancel_right]
    exact dvd_mul_right _ _
  have hqn₀ : (q : ℤ) ∣ f.eval (((m % q : ℕ) : ℤ) ^ 2) := by
    have h1 := eval_modEq f (Int.ModEq.pow 2 hmod₀)
    rw [Int.modEq_iff_dvd] at h1
    have h2 := dvd_sub hqev h1
    rwa [sub_sub_self] at h2
  obtain ⟨n, hnq, hqn⟩ : ∃ n : ℕ, 2 * n + 1 ≤ q ∧ (q : ℤ) ∣ f.eval ((n : ℤ) ^ 2) := by
    by_cases hcase : 2 * (m % q) < q
    · exact ⟨m % q, hcase, hqn₀⟩
    · push Not at hcase
      refine ⟨q - m % q, ?_, ?_⟩
      · have h1 : 2 * (q - m % q) ≤ q := by omega
        have h2 : 2 * (q - m % q) ≠ q := by
          intro h3
          rcases hqodd with ⟨k, hk⟩
          omega
        omega
      · have hmod : ((q - m % q : ℕ) : ℤ) ≡ -((m % q : ℕ) : ℤ) [ZMOD (q : ℤ)] := by
          rw [Int.modEq_iff_dvd]
          have e : ((q - m % q : ℕ) : ℤ) = (q : ℤ) - ((m % q : ℕ) : ℤ) :=
            Nat.cast_sub (le_of_lt hn₀lt)
          rw [e]
          have e2 : -((m % q : ℕ) : ℤ) - ((q : ℤ) - ((m % q : ℕ) : ℤ)) = -(q : ℤ) := by
            ring
          rw [e2]
          exact dvd_neg.mpr (dvd_refl _)
        have hsq : (((q - m % q : ℕ) : ℤ) ^ 2) ≡ (((m % q : ℕ) : ℤ) ^ 2) [ZMOD (q : ℤ)] := by
          have h1 := Int.ModEq.pow 2 hmod
          rwa [neg_sq] at h1
        have h2 := eval_modEq f hsq
        rw [Int.modEq_iff_dvd] at h2
        have h3 := dvd_sub hqn₀ h2
        rwa [sub_sub_self] at h3
  -- Apply the bound: `q ≤ 2n + B`, so `q = 2n + 2k + 1` for some `k ≤ B`.
  have hqB := (hB n).2 q hq hqn
  obtain ⟨j, hj1, hjB, hjodd⟩ : ∃ j : ℕ, q = 2 * n + j ∧ j ≤ B ∧ Odd j := by
    refine ⟨q - 2 * n, by omega, by omega, ?_⟩
    rcases hqodd with ⟨k, hk⟩
    exact ⟨k - n, by omega⟩
  obtain ⟨k, hk⟩ := hjodd
  subst hk
  have hkB : k ≤ B := by omega
  -- Then `q` divides `Fs f (2k+1)`.
  have hqFs : (q : ℤ) ∣ Fs f ((2 * k + 1 : ℕ) : ℤ) := by
    have h1 : ((2 * k + 1 : ℕ) : ℤ) ≡ -((2 * n : ℕ) : ℤ) [ZMOD (q : ℤ)] := by
      rw [Int.modEq_iff_dvd]
      have e : (q : ℤ) = 2 * (n : ℤ) + (2 * (k : ℤ) + 1) := by exact_mod_cast hj1
      have e2 : -((2 * n : ℕ) : ℤ) - ((2 * k + 1 : ℕ) : ℤ) = -(q : ℤ) := by
        push_cast
        linarith [e]
      rw [e2]
      exact dvd_neg.mpr (dvd_refl _)
    have h2 := Fs_modEq f h1
    rw [Fs_neg] at h2
    have h3 : Fs f (2 * (n : ℤ)) = 4 ^ f.natDegree * f.eval ((n : ℤ) ^ 2) :=
      Fs_two_mul f _
    have h4 : ((2 * n : ℕ) : ℤ) = 2 * (n : ℤ) := by push_cast; ring
    rw [h4, h3] at h2
    have h5 : (4 ^ f.natDegree * f.eval ((n : ℤ) ^ 2)) ≡ 0 [ZMOD (q : ℤ)] :=
      Int.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_right hqn _)
    exact Int.modEq_zero_iff_dvd.mp (Int.ModEq.trans h2 h5)
  -- Hence `q` divides `M`, so `q` is one of the excluded primes: contradiction.
  have hqM : (q : ℤ) ∣ M := by
    rw [hM]
    exact dvd_trans hqFs
      (Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr (by omega)))
  have hqmem : q ∈ M.natAbs.primeFactors := by
    rw [Nat.mem_primeFactors]
    refine ⟨hq, ?_, Int.natAbs_ne_zero.mpr hM0⟩
    have h1 : (q : ℤ).natAbs ∣ M.natAbs := Int.natAbs_dvd_natAbs.mpr hqM
    rwa [Int.natAbs_natCast] at h1
  exact hqs (Finset.mem_insert_of_mem hqmem)

lemma odd_nat_coprime_two {m : ℕ} (h : Odd m) : Nat.Coprime 2 m := by
  rw [Nat.prime_two.coprime_iff_not_dvd]
  rintro ⟨l, hl⟩
  obtain ⟨k, hk⟩ := h
  omega

lemma coeff_factor_one (a : ℤ) : (C 4 * X - C (a ^ 2) : ℤ[X]).coeff 1 = 4 := by
  rw [coeff_sub, coeff_C_mul, coeff_X_one, coeff_C_succ, mul_one, sub_zero]

lemma coeff_factor_zero (a : ℤ) : (C 4 * X - C (a ^ 2) : ℤ[X]).coeff 0 = -a ^ 2 := by
  rw [coeff_sub, coeff_C_mul, coeff_X_zero, coeff_C_zero, mul_zero, zero_sub]

/-- `4X − a²` with `a` odd is a primitive polynomial over `ℤ`. -/
lemma isPrimitive_factor {a : ℤ} (ha : Odd a) : (C 4 * X - C (a ^ 2)).IsPrimitive := by
  rw [isPrimitive_iff_isUnit_of_C_dvd]
  intro r hr
  rw [C_dvd_iff_dvd_coeff] at hr
  have h1 : r ∣ 4 := by
    have h := hr 1
    rwa [coeff_factor_one] at h
  have h0 : r ∣ -a ^ 2 := by
    have h := hr 0
    rwa [coeff_factor_zero] at h
  have hn4 : r.natAbs ∣ 4 := by
    have h := Int.natAbs_dvd_natAbs.mpr h1
    rwa [show (4 : ℤ).natAbs = 4 by decide] at h
  have hnA : r.natAbs ∣ a.natAbs ^ 2 := by
    have h := Int.natAbs_dvd_natAbs.mpr h0
    rwa [Int.natAbs_neg, Int.natAbs_pow] at h
  have hcop : Nat.Coprime 4 (a.natAbs ^ 2) :=
    ((odd_nat_coprime_two (Odd.natAbs ha)).pow_left 2).pow_right 2
  have h1' : r.natAbs ∣ 1 := by
    rw [← hcop.gcd_eq_one]
    exact Nat.dvd_gcd hn4 hnA
  have h2' : r.natAbs = 1 := Nat.dvd_one.mp h1'
  rw [Int.isUnit_iff]
  rw [Int.natAbs_eq_iff] at h2'
  rcases h2' with h | h
  · left
    exact_mod_cast h
  · right
    exact_mod_cast h

/-- If `f` has the root `(2k+1)²/4` over `ℚ`, then `4X − (2k+1)²`
divides `f` over `ℤ` (Gauss's lemma). -/
lemma factor_dvd_of_root (f : ℤ[X]) {k : ℕ}
    (hroot : (f.map (Int.castRingHom ℚ)).eval (((2 * k + 1 : ℕ) : ℚ) ^ 2 / 4) = 0) :
    (C 4 * X - C (((2 * k + 1 : ℕ) : ℤ) ^ 2)) ∣ f := by
  set a : ℤ := ((2 * k + 1 : ℕ) : ℤ) with ha
  have haodd : Odd a := ⟨(k : ℤ), by rw [ha]; push_cast; ring⟩
  have hprim : (C 4 * X - C (a ^ 2)).IsPrimitive := isPrimitive_factor haodd
  -- Over `ℚ`, `4X − a² = 4 · (X − a²/4)`, and `X − a²/4` divides `f`.
  have hroot' : (f.map (Int.castRingHom ℚ)).IsRoot ((a : ℚ) ^ 2 / 4) := by
    rw [IsRoot.def, ha, Int.cast_natCast]
    exact hroot
  have hdvd : (X - C ((a : ℚ) ^ 2 / 4)) ∣ f.map (Int.castRingHom ℚ) :=
    dvd_iff_isRoot.mpr hroot'
  have hmap : (C 4 * X - C (a ^ 2)).map (Int.castRingHom ℚ) =
      C 4 * X - C (4 * ((a : ℚ) ^ 2 / 4)) := by
    have e1 : (Int.castRingHom ℚ) (a ^ 2) = (4 : ℚ) * ((a : ℚ) ^ 2 / 4) := by
      simp
      field_simp
    rw [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
      Polynomial.map_C, e1]
    congr 1
  have hfac : (C 4 * X - C (4 * ((a : ℚ) ^ 2 / 4)) : ℚ[X]) =
      C 4 * (X - C ((a : ℚ) ^ 2 / 4)) := by
    rw [mul_sub, ← C_mul]
  have hdvdQ : (C 4 * X - C (a ^ 2)).map (algebraMap ℤ ℚ) ∣
      f.map (algebraMap ℤ ℚ) := by
    rw [algebraMap_int_eq, hmap, hfac,
      (isUnit_C.mpr (by rw [isUnit_iff_ne_zero]; norm_num : IsUnit (4 : ℚ))).mul_left_dvd]
    exact hdvd
  exact hprim.dvd_of_fraction_map_dvd_fraction_map hdvdQ

/-- The cofactor of a `4X − a²` factor still satisfies the prime bound. -/
lemma pbound_of_mul_factor {f f₁ : ℤ[X]} {a : ℤ} (B : ℕ)
    (hf : f = (C 4 * X - C (a ^ 2)) * f₁) (hB : Pbound f B) : Pbound f₁ B := by
  intro n
  have h1 := (hB n).1
  rw [hf, eval_mul] at h1
  exact ⟨right_ne_zero_of_mul h1, fun q hq hqdv ↦ (hB n).2 q hq (by
    rw [hf, eval_mul]
    exact dvd_trans hqdv (dvd_mul_left _ _))⟩

/-- The classification theorem, proved by strong induction on the degree:
a nonconstant `f` satisfying the bound has a root `(2k+1)²/4`, hence a
factor `4X − (2k+1)²`, and the cofactor has smaller degree. -/
lemma classification_of_pbound : ∀ d : ℕ, ∀ f : ℤ[X], f.natDegree = d →
    (∃ B, Pbound f B) → Classification f := by
  intro d
  refine Nat.strong_induction_on d ?_
  intro d IH f hd ⟨B, hB⟩
  by_cases hd0 : d = 0
  · -- The constant case: `f = C c` with `c ≠ 0`.
    have hf : f = C (f.coeff 0) := eq_C_of_natDegree_eq_zero (hd.trans hd0)
    have hc : f.coeff 0 ≠ 0 := by
      have h1 := (hB 0).1
      rw [hf] at h1
      simpa using h1
    exact ⟨f.coeff 0, [], hc, by simp, by rw [hf]; simp⟩
  · -- The nonconstant case.
    have hd' : f.natDegree ≠ 0 := by rwa [hd]
    obtain ⟨k, hroot⟩ := exists_root_of_pbound f hd' B hB
    obtain ⟨f₁, hf₁⟩ := factor_dvd_of_root f hroot
    set a : ℤ := ((2 * k + 1 : ℕ) : ℤ) with ha
    have haodd : Odd a := ⟨(k : ℤ), by rw [ha]; push_cast; ring⟩
    have hf0 : f ≠ 0 := by
      intro h0
      have h1 := (hB 0).1
      rw [h0] at h1
      simp at h1
    have hfac0 : (C 4 * X - C (a ^ 2) : ℤ[X]) ≠ 0 := by
      intro h0
      have h2 : (C 4 * X - C (a ^ 2) : ℤ[X]).coeff 1 = 0 := by rw [h0]; simp
      rw [coeff_factor_one] at h2
      norm_num at h2
    have hf₁0 : f₁ ≠ 0 := fun h0 ↦ hf0 (by rw [hf₁, h0]; simp)
    have hfacdeg : (C 4 * X - C (a ^ 2) : ℤ[X]).natDegree = 1 := by
      rw [natDegree_sub_eq_left_of_natDegree_lt (by
        rw [natDegree_C_mul_X 4 (by norm_num), natDegree_C]
        exact Nat.zero_lt_one)]
      exact natDegree_C_mul_X 4 (by norm_num)
    have hdeg : f.natDegree = (C 4 * X - C (a ^ 2)).natDegree + f₁.natDegree := by
      conv_lhs => rw [hf₁]
      exact natDegree_mul hfac0 hf₁0
    have hdf₁ : f₁.natDegree < d := by omega
    have hPf₁ : Pbound f₁ B := pbound_of_mul_factor B hf₁ hB
    obtain ⟨c, L, hc, ho, hL⟩ := IH f₁.natDegree hdf₁ f₁ rfl ⟨B, hPf₁⟩
    refine ⟨c, a :: L, hc, ?_, ?_⟩
    · intro b hb
      rw [List.mem_cons] at hb
      rcases hb with rfl | hb
      · exact haodd
      · exact ho b hb
    · rw [hL] at hf₁
      rw [hf₁, List.map_cons, List.prod_cons]
      ring

/-- The full classification, in the prime-bound formulation. -/
lemma classification_iff_pbound (f : ℤ[X]) :
    (∃ B, Pbound f B) ↔ Classification f :=
  ⟨fun h ↦ classification_of_pbound f.natDegree f rfl h, pbound_of_classification f⟩

snip end

problem usa2006_p3 (f : ℤ[X]) : BddCond f ↔ Classification f := by
  rw [bddCond_iff]
  exact classification_iff_pbound f

end Usa2006P3
