/-
Copyright (c) 2023 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clayton Knittel
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# International Mathematical Olympiad 2023, Problem 1

Determine all composite integers n>1 that satisfy the following property:
if d₁,d₂,...,dₖ are all the positive divisors of n with
1 = d₁ < d₂ < ... < dₖ = n, then dᵢ divides dᵢ₊₁ + dᵢ₊₂ for every
1 ≤ i ≤ k - 2.
-/

namespace Imo2023P1

abbrev ConsecutiveFactors (n a b : ℕ) :=
  a ∣ n ∧ b ∣ n ∧ a < b ∧ ¬∃ c, (c ∣ n ∧ a < c ∧ c < b)

abbrev Dividable (n : ℕ) :=
  ∀ {a b c : ℕ},
    ConsecutiveFactors n a b ∧ ConsecutiveFactors n b c
    → a ∣ b + c

snip begin

/-- Powers of distinct primes are never equal. -/
lemma PrimePow_ne {a b p q : ℕ} (p_prime : p.Prime) (q_prime : q.Prime) (p_ne_q : p ≠ q)
    (ha : ∃ k > 0, p ^ k = a) (hb : ∃ k > 0, q ^ k = b)
    : a ≠ b := by
  by_contra a_eq_b
  obtain ⟨_, k_ne_0, ha⟩ := ha
  obtain ⟨_, _, hb⟩ := hb
  let h := congrArg (Nat.factorization · p) (hb ▸ a_eq_b ▸ ha)
  dsimp at h
  rw [Nat.Prime.factorization_pow p_prime,
      Nat.Prime.factorization_pow q_prime,
      Finsupp.single_eq_same,
      Finsupp.single_eq_of_ne p_ne_q] at h
  exact k_ne_0.ne.symm h

/-- If a number divides some non-zero number, it is also nonzero. -/
lemma dvd_ne_zero {a b : ℕ} (hb : b ≠ 0) (h : a ∣ b) : 0 < a :=
  Nat.zero_lt_of_ne_zero (fun ha => hb (zero_dvd_iff.mp (ha ▸ h)))

/-- If a prime `p` divides `n`, then `n.factorization p ≠ 0`. -/
lemma dvd_n_fact_ne_zero {n p : ℕ} (n_ne_0 : n ≠ 0) (p_prime : p.Prime) (p_dvd_n : p ∣ n)
    : n.factorization p ≠ 0 := by
  by_contra h
  have := (Nat.factorization_eq_zero_iff n p).mp h
  apply not_or_intro ?_ (not_or_intro ?_ n_ne_0) this
  · exact not_not_intro p_prime
  · exact not_not_intro p_dvd_n

/-- Complementary factors are inversely ordered. -/
lemma mul_cmp_compl {a b x y : ℕ} (hab : a < b) (hy : 0 < y)
    (h : a * x = b * y) : y < x :=
  Nat.lt_of_mul_lt_mul_left
    (h ▸ Nat.mul_lt_mul_of_pos_right hab hy)

/-- Given prime `p`, the factorization of `p + 1` is `0` at `p`. -/
theorem p_succ_fact_zero {p : ℕ} (hp : p.Prime)
    : (p + 1).factorization p = 0 := by
  apply Nat.factorization_eq_zero_of_not_dvd
  exact hp.not_dvd_one ∘ Nat.dvd_add_self_left.mp

/-- If `p ^ e < c < p ^ (e + 1)`, then `∃ q` prime that divides `c`. -/
theorem not_pow_cons_factors_other_prime {p e c : ℕ} (hp : p.Prime)
    (c_gt_e : c > p ^ e) (c_lt_p_e_succ : c < p ^ (e + 1))
    : ∃ q ≠ p, q.Prime ∧ q ∣ c := by
  by_contra h
  have : ∃ c_e, c.factorization = Finsupp.single p c_e := by
    exists c.factorization p
    ext q
    by_cases hq : q = p
    · rw [hq, Finsupp.single_eq_same]
    · rw [Finsupp.single_eq_of_ne hq]
      have {q : ℕ} (q_ne_p : q ≠ p) : c.factorization q = 0 := by
        refine (em q.Prime).elim (fun q_prime => ?_) (Nat.factorization_eq_zero_of_non_prime c)
        by_contra h₂
        exact h ⟨q, q_ne_p, q_prime, Nat.dvd_of_factorization_pos h₂⟩
      exact this hq

  obtain ⟨c_e, hf⟩ := this

  let c_is_pow_p :=
    Nat.eq_of_factorization_eq
      (Nat.ne_zero_of_lt c_gt_e)
      (pow_ne_zero c_e hp.ne_zero)
      fun p => (congrArg (· p) (Nat.Prime.factorization_pow hp ▸ hf))

  have gt_e : c_e ≥ e + 1 :=
    (Nat.pow_lt_pow_iff_right hp.one_lt).mp (c_is_pow_p ▸ c_gt_e)
  have lt_e_succ : c_e < e + 1 :=
    (Nat.pow_lt_pow_iff_right hp.one_lt).mp (c_is_pow_p ▸ c_lt_p_e_succ)
  exact Nat.le_lt_asymm gt_e lt_e_succ

/-- The inverse factors of consecutive factors of `n` are themselves
 consecutive factors of `n`. -/
theorem inv_cons_factors {n a b x y : ℕ} (hn : 0 < n) (ha : n = a * x)
    (hb : n = b * y) (h : ConsecutiveFactors n a b)
    : ConsecutiveFactors n y x := by
  have div_n_ne_0 {a b : ℕ} (h : n = a * b) : 0 < b :=
    Nat.zero_lt_of_ne_zero ((Nat.mul_ne_zero_iff).mp (h ▸ hn.ne).symm).right

  obtain ⟨_, _, a_lt_b, no_c⟩ := h
  have y_lt_x := mul_cmp_compl a_lt_b (div_n_ne_0 hb) (ha ▸ hb)

  rw [Nat.mul_comm] at ha
  rw [Nat.mul_comm] at hb
  refine ⟨⟨b, hb⟩, ⟨a, ha⟩, y_lt_x, ?_⟩

  by_contra hc
  let ⟨c, ⟨z, hc⟩, y_lt_c, c_lt_x⟩ := hc
  apply no_c

  exists z
  exact ⟨
    ⟨c, Nat.mul_comm _ _ ▸ hc⟩,
    mul_cmp_compl c_lt_x (div_n_ne_0 ha) (hc ▸ ha),
    mul_cmp_compl y_lt_c (div_n_ne_0 hc) (hc ▸ hb.symm)
  ⟩

/-- If `n.factorization p ≠ 0`, then `p` is prime. -/
theorem factorization_prime {n p : ℕ} (h : n.factorization p ≠ 0) : p.Prime := by
  by_cases hp : p.Prime
  · exact hp
  · exact False.elim (h (Nat.factorization_eq_zero_of_non_prime n hp))

/-- If `n` is not a prime power, then its `ordCompl[p]` with respect to any `p`
 is `> 1`. -/
theorem ordCompl_of_non_prime_pow {n p : ℕ} (hn : 1 < n) (hp : ¬IsPrimePow n)
    : ordCompl[p] n > 1 := by
  -- Show by contradiction that if `ordCompl[p] n = 1`, then `n` is a prime
  -- power.
  have n_ne_0 := Nat.ne_zero_of_lt hn
  let c := ordCompl[p] n
  by_contra hc
  apply hp

  have c_eq_1 :=
    let hc := Nat.le_of_not_lt hc
    have c_ne_0 := (dvd_ne_zero n_ne_0 (Nat.ordCompl_dvd n p)).ne.symm
    (Nat.le_one_iff_eq_zero_or_eq_one.mp hc).resolve_left c_ne_0
  have c_fact_eq_0 (q : ℕ): c.factorization q = 0 := by
    dsimp [c]
    rw [c_eq_1, Nat.factorization_one]
    rfl

  -- We can take `p` prime and `p ∣ n`, since for non-prime p which does not
  -- divide `n`, `ordCompl[p] n = n` is trivially `> 1`.
  have p_prime :=
    Classical.byContradiction
      (hn.ne ∘ (c_eq_1 ▸ Nat.ordCompl_of_not_prime n p))
  have p_dvd_n : p ∣ n := by
    by_contra h
    have : c = n := by
      rw [← Nat.div_one n, ← Nat.pow_zero p, ← Nat.factorization_eq_zero_of_not_dvd h]
    exact (this ▸ hn).ne c_eq_1.symm

  have n_fact_p_ne_0 : n.factorization p ≠ 0 := dvd_n_fact_ne_zero n_ne_0 p_prime p_dvd_n

  -- Since `c = 1`, `n.factorization q` for `q ≠ p` is `= 0`.
  have (q : ℕ): n.factorization q = Finsupp.single p (n.factorization p) q := by
    if h : q = p then
      rw [h, Finsupp.single_eq_same]
    else
      let c_fact_q := congrArg (· q) (Nat.factorization_ordCompl n p)
      dsimp at c_fact_q
      rw [Finsupp.erase_ne h] at c_fact_q
      rw [← c_fact_q, Finsupp.single_eq_of_ne h]
      exact c_fact_eq_0 q
  -- So `n` is a prime power.
  have n_eq_p_pow :=
    Nat.eq_of_factorization_eq
      n_ne_0
      (pow_ne_zero _ p_prime.ne_zero)
      (Nat.Prime.factorization_pow p_prime ▸ this)

  exact ⟨p, _, p_prime.prime, Nat.zero_lt_of_ne_zero n_fact_p_ne_0, n_eq_p_pow.symm⟩

/-- If `n` is not a prime power, and `p` is its minimum factor, then the second
 smallest prime factor `q` is consecutive to `p` to some power `> 0`.

 This theorem is key to solving the `Dividable → PrimePower` direction of the
 problem. -/
theorem minFac_cons_factor {n : ℕ} (hn : 1 < n) (h : ¬IsPrimePow n)
    : ∃ q e,
      q.Prime ∧ q ≠ n.minFac ∧
      ConsecutiveFactors n (n.minFac ^ e) (n.minFac ^ (e + 1)) ∧
      ConsecutiveFactors n (n.minFac ^ (e + 1)) q := by
  have n_ne_0 := Nat.ne_zero_of_lt hn

  let p := n.minFac
  have p_prime : p.Prime := n.minFac_prime (Nat.ne_of_lt hn).symm

  let c := ordCompl[p] n
  have c_fact_def := fun r => congrArg (· r) (Nat.factorization_ordCompl n p)
  have c_dvd_n := Nat.ordCompl_dvd n p
  have c_gt_one : 1 < c := ordCompl_of_non_prime_pow hn h

  -- Take `q` to be the second smallest prime factor of `n`.
  let q := c.minFac
  have q_prime : q.Prime := c.minFac_prime (Nat.ne_of_lt c_gt_one).symm

  -- Since `q` is the second smallest prime factor of `n`, the only prime
  -- factor `< q` is `p`.
  have p_unique {r : ℕ} (r_lt_q : r < q) (r_ne_p : r ≠ p) : n.factorization r = 0 := by
    have c_fact_r := c_fact_def r
    rw [Finsupp.erase_ne r_ne_p] at c_fact_r
    rw [← c_fact_r]
    by_contra h
    refine Nat.le_lt_asymm (Nat.minFac_le_of_dvd ?_ ?_) r_lt_q
    · exact (factorization_prime h).one_lt
    · exact Nat.dvd_of_factorization_pos h

  have p_lt_q : p < q := by
    have q_dvd_c : q ∣ c := Nat.minFac_dvd c
    have q_dvd_n : q ∣ n := Nat.dvd_trans q_dvd_c c_dvd_n
    have c_fact_q_ne_0 :=
      dvd_n_fact_ne_zero (Nat.ne_zero_of_lt c_gt_one) q_prime q_dvd_c

    refine Nat.lt_of_le_of_ne ?_ ?_
    · exact Nat.minFac_le_of_dvd q_prime.one_lt q_dvd_n
    · by_contra h
      apply c_fact_q_ne_0
      rw [c_fact_def, h, Finsupp.erase_same]

  -- Find the largest power we can raise `p` to without exceeding `q` nor `p`'s
  -- multiplicity.
  let e_succ := min (n.factorization p) (p.log q)
  have e_succ_ne_0 : 0 < e_succ := by
    refine lt_min ?_ ?_
    · exact p_prime.factorization_pos_of_dvd n_ne_0 (Nat.minFac_dvd n)
    · simp [p_lt_q.le, p_prime.one_lt]
  -- Label its predecessor `e`.
  let ⟨e, he⟩ := Nat.exists_add_one_eq.mpr e_succ_ne_0

  exists q, e
  -- We have already shown `q` is prime, and `p ≠ q`.
  refine ⟨q_prime, (Nat.ne_of_lt p_lt_q).symm, ?_⟩

  -- Show that both `p ^ e` and `p ^ (e + 1)` divide `n`.
  have {e : ℕ} : e ≤ n.factorization p → p ^ e ∣ n :=
    Nat.multiplicity_eq_factorization p_prime n_ne_0
      ▸ pow_dvd_of_le_multiplicity
  have p_e_dvd_n : p ^ e ∣ n :=
    (he ▸ this ∘ Nat.le_of_add_right_le) (Nat.min_le_left _ _)
  have p_e_succ_dvd_n : p ^ (e + 1) ∣ n :=
    he ▸ this (Nat.min_le_left _ _)

  have p_e_succ_lt_q : p ^ (e + 1) < q := by
    rw [he]
    refine Nat.lt_of_le_of_ne ?_ ?_
    · exact Nat.pow_le_of_le_log q_prime.ne_zero (min_le_right _ _)
    · exact PrimePow_ne p_prime q_prime p_lt_q.ne
        ⟨e_succ, e_succ_ne_0, rfl⟩
        ⟨1, Nat.zero_lt_one, q.pow_one⟩

  have : ConsecutiveFactors n (p ^ e) (p ^ (e + 1)) := by
    -- Show these are consecutive factors by showing that any number between
    -- them must have a prime factor different from `p` and `< q`, which we
    -- know does not exist.
    refine ⟨p_e_dvd_n, p_e_succ_dvd_n, Nat.pow_lt_pow_succ p_prime.one_lt, ?_⟩
    by_contra hd
    obtain ⟨d, d_dvd_n, d_gt_p_e, d_lt_p_e_succ⟩ := hd
    obtain ⟨r, r_ne_p, r_prime, r_dvd_d⟩ :=
      not_pow_cons_factors_other_prime p_prime d_gt_p_e d_lt_p_e_succ

    apply dvd_n_fact_ne_zero n_ne_0 r_prime (r_dvd_d.trans d_dvd_n)
    refine p_unique ?_ r_ne_p
    exact Nat.lt_of_le_of_lt
      (Nat.le_of_dvd (dvd_ne_zero n_ne_0 d_dvd_n) r_dvd_d)
      (d_lt_p_e_succ.trans p_e_succ_lt_q)
  refine ⟨this, ?_⟩

  -- Show ConsecutiveFactors n (p ^ (e + 1)) q
  refine ⟨p_e_succ_dvd_n, c.minFac_dvd.trans c_dvd_n, p_e_succ_lt_q, ?_⟩
  -- By contradiction, assume `∃ d` between these two factors.
  by_contra h
  obtain ⟨d, d_dvd_n, d_gt_p_e_succ, d_lt_q⟩ := h

  have d_ne_0 := (Nat.ne_of_lt (dvd_ne_zero n_ne_0 d_dvd_n)).symm
  have d_fact_lt_n : d.factorization ≤ n.factorization :=
    (Nat.factorization_le_iff_dvd
      (dvd_ne_zero n_ne_0 d_dvd_n).ne.symm
      n_ne_0).mpr d_dvd_n

  -- d's factorization must only contain `p`, since `d < q`.
  have : ∃ d_e, d.factorization = Finsupp.single p d_e := by
    exists d.factorization p
    ext r
    if hr : r = p then
      rw [hr, Finsupp.single_eq_same]
    else
      rw [Finsupp.single_eq_of_ne hr]
      exact if r_ge_q : r ≥ q then
        Nat.factorization_eq_zero_of_lt (Nat.lt_of_lt_of_le d_lt_q r_ge_q)
      else
        Nat.le_zero.mp (p_unique (Nat.lt_of_not_ge r_ge_q) hr ▸ d_fact_lt_n r)
  obtain ⟨d_e, hd_e⟩ := this

  -- Therefore `d` is a power of `p`.
  have d_eq_p_e :=
    Nat.eq_of_factorization_eq
      d_ne_0
      (Nat.pow_pos (Nat.minFac_pos n)).ne.symm
      fun r => congrArg (· r) (Nat.Prime.factorization_pow p_prime ▸ hd_e)
  -- And its power is `> e + 1`.
  have d_e_gt_e_succ : d_e > e_succ := by
    apply (Nat.pow_lt_pow_iff_right p_prime.one_lt).mp
    rw [← d_eq_p_e, ← he]
    exact d_gt_p_e_succ

  -- Show that in both cases, `d` is too large, either having too high a
  -- multiplicity of `p`, or being larger than `q`.
  by_cases he_min : n.factorization p < p.log q
  · -- Show d_e > n.factorization p
    refine Nat.le_lt_asymm (?_ : d_e ≤ n.factorization p) ?_
    · rw [← (Finsupp.single_eq_same : _ = d_e), ← hd_e]
      exact d_fact_lt_n p
    · rw [← min_eq_left he_min.le]
      exact d_e_gt_e_succ
  · -- Show d = p ^ d_e > q
    have : q ≤ p ^ (Nat.log p q + 1) :=
      (Nat.lt_pow_succ_log_self p_prime.one_lt q).le
    apply Nat.lt_le_asymm d_lt_q ∘ this.trans
    rw [d_eq_p_e, ← min_eq_right (Nat.ge_of_not_lt he_min)]
    apply (Nat.pow_le_pow_iff_right p_prime.one_lt).mpr
    exact d_e_gt_e_succ

/-- The consecutive factors of prime powers of `p` are a factor `p` apart. -/
lemma PrimePow_cons_are_p_apart {x y p n : ℕ} (p_prime : p.Prime)
    (hn : ∃ k, 0 < k ∧ p ^ k = n) (h : ConsecutiveFactors n x y)
    : x * p = y := by
  obtain ⟨e, ⟨e_gt_0, n_eq_p_exp⟩⟩ := hn
  obtain ⟨hx, ⟨hy, ⟨x_lt_y, h⟩⟩⟩ := h
  let ⟨x_exp, ⟨_, x_eq_p_exp⟩⟩ :=
    (Nat.dvd_prime_pow p_prime).mp (n_eq_p_exp ▸ hx)
  let ⟨y_exp, ⟨_, y_eq_p_exp⟩⟩ :=
    (Nat.dvd_prime_pow p_prime).mp (n_eq_p_exp ▸ hy)

  have exp_lt : x_exp < y_exp := by
    apply (Nat.pow_lt_pow_iff_right p_prime.one_lt).mp
    rw [← x_eq_p_exp, ← y_eq_p_exp]
    exact x_lt_y

  have exp_eq : x_exp + 1 = y_exp := by
    by_contra ne
    apply h
    have lt := Nat.lt_of_le_of_ne exp_lt ne

    exists p ^ (x_exp + 1)
    refine And.intro ?_ ⟨
        x_eq_p_exp ▸ Nat.pow_lt_pow_succ p_prime.one_lt,
        y_eq_p_exp ▸ Nat.pow_lt_pow_of_lt p_prime.one_lt lt
      ⟩

    let ⟨b, n_eq⟩ := hy
    let ⟨k, y_eq⟩ := Nat.exists_eq_add_of_lt lt
    exists b * p ^ (k + 1)
    rw [n_eq, y_eq_p_exp, y_eq, add_assoc, Nat.pow_add, mul_assoc,
        mul_comm _ b]

  rw [x_eq_p_exp, y_eq_p_exp, ← exp_eq]
  exact rfl

/-- Proof that all prime powers are `Dividable`. -/
lemma PrimePow_is_dividable {n : ℕ} : IsPrimePow n → 1 < n ∧ Dividable n := by
  intro h
  refine ⟨h.one_lt, ?_⟩

  obtain ⟨p, e, hp, hpp⟩ := h
  intro _ _ _ ⟨xy_cons, yz_cons⟩
  let y_subs := PrimePow_cons_are_p_apart hp.nat_prime ⟨e, hpp⟩ xy_cons
  let z_subs := PrimePow_cons_are_p_apart hp.nat_prime ⟨e, hpp⟩ yz_cons
  rw [← z_subs, ← y_subs]
  exists p + p ^ 2
  linarith

/-- Proof that all `Dividable` numbers `> 1` are prime powers. -/
lemma dividable_is_PrimePow {n : ℕ} (h : 1 < n ∧ Dividable n)
    : IsPrimePow n := by
  obtain ⟨n_gt_1, hd⟩ := h
  let p := n.minFac
  let p_prime := (n.minFac_prime (Nat.ne_of_lt n_gt_1).symm)

  by_contra hn
  let ⟨q, e, q_prime, q_ne_p, cxy, cyz⟩ := minFac_cons_factor n_gt_1 hn
  let ⟨x_div_n, y_div_n, _⟩ := cxy
  let ⟨_, z_div_n, _⟩ := cyz
  obtain ⟨x, hx⟩ := x_div_n
  obtain ⟨y, hy⟩ := y_div_n
  obtain ⟨z, hz⟩ := z_div_n

  have h : p ^ (e + 1) ∣ q * (p + 1) := by
    let ⟨c, h⟩ :=
      have n_gt_0 := Nat.zero_lt_of_lt n_gt_1
      hd ⟨
        inv_cons_factors n_gt_0 hy hz cyz,
        inv_cons_factors n_gt_0 hx hy cxy
      ⟩
    let h := congrArg (p ^ (e + 1) * q * ·) h
    exists c

    have : Function.Injective (· * n) :=
      fun _ _ h => Nat.mul_right_cancel (Nat.zero_lt_of_lt n_gt_1) h
    apply_fun (· * n)
    dsimp

    rw [add_comm, mul_add, add_mul, mul_one]
    nth_rw 1 [hy]
    nth_rw 2 [hx]
    nth_rw 3 [hz]

    rw [mul_assoc, ← Nat.mul_add q, ← mul_assoc, ← Nat.pow_add_one',
        ← Nat.mul_add, ← mul_assoc, mul_comm q, mul_assoc _ c, mul_rotate' c,
        ← mul_assoc]
    exact h

  have : 0 < (p ^ (e + 1)).factorization p := by
    rw [p_prime.factorization_pow, Finsupp.single_eq_same]
    exact Nat.zero_lt_succ _
  apply Nat.not_le_of_gt this

  -- Show that `q * (p + 1)` is not divisible by `p`.
  have : (q * (p + 1)).factorization p = 0 := by
    rw [Nat.factorization_mul q_prime.ne_zero p.succ_ne_zero]
    dsimp
    rw [q_prime.factorization, Finsupp.single_eq_of_ne q_ne_p.symm,
        p_succ_fact_zero p_prime]
  refine this ▸ (Nat.factorization_le_iff_dvd ?_ ?_).mpr h p
  · exact (pow_ne_zero (e + 1) p_prime.ne_zero)
  · exact (Nat.mul_ne_zero q_prime.ne_zero p.succ_ne_zero)

snip end

determine solution_set : Set ℕ := { n | ¬n.Prime ∧ IsPrimePow n }

problem imo2023_p1 : solution_set = { n | 1 < n ∧ ¬n.Prime ∧ Dividable n } := by
  ext x
  refine ⟨fun ⟨hx₁, hx₂⟩ ↦ ?_, fun ⟨hx₁, hx₂, hx₃⟩ ↦ ?_⟩
  · have ⟨hx₃, hx₄⟩ := PrimePow_is_dividable hx₂
    refine ⟨hx₃, hx₁, hx₄⟩
  · exact ⟨hx₂, dividable_is_PrimePow ⟨hx₁, hx₃⟩⟩

end Imo2023P1
