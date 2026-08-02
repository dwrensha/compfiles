/-
Copyright (c) 2023 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Tactic
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Olympiad 2010, Problem 3

Determine all functions g : ℤ>0 → ℤ>0 such that

               (g(m) + n)(g(n) + m)

is always a perfect square.
-/

namespace Imo2010P3

abbrev PosInt : Type := { x : ℤ // 0 < x }

notation "ℤ>0" => PosInt

snip begin

/-- The values of `g`, reindexed as a function `ℕ → ℕ`
(the natural `n` stands for the positive integer `n + 1`). -/
def gF (g : ℤ>0 → ℤ>0) (n : ℕ) : ℕ := (g ⟨↑n + 1, by omega⟩).1.natAbs

/-- If `A * B` is a square and the prime `p` occurs in `A` to an odd power,
then `p` divides `B`. -/
lemma kf {p A B s : ℕ} (hp : p.Prime) (hA : A ≠ 0) (hB : B ≠ 0)
    (hs : A * B = s * s) (hodd : Odd ((Nat.factorization A) p)) : p ∣ B := by
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hs
    rcases Nat.mul_eq_zero.mp hs with h | h
    · exact hA h
    · exact hB h
  have e2 : (Nat.factorization (A * B)) p
      = (Nat.factorization A) p + (Nat.factorization B) p := by
    rw [Nat.factorization_mul hA hB, Finsupp.add_apply]
  rw [hs] at e2
  have e3 : (Nat.factorization (s * s)) p = 2 * (Nat.factorization s) p := by
    rw [Nat.factorization_mul hs0 hs0, Finsupp.add_apply, two_mul]
  rw [e3] at e2
  obtain ⟨k, hk⟩ := hodd
  have h1 : 1 ≤ (Nat.factorization B) p := by omega
  have h2 := (hp.pow_dvd_iff_le_factorization hB).mpr h1
  rwa [pow_one] at h2

/-- A product of two positive integers differing by `1` or `2` is never a square. -/
lemma not_sq_between {W s d : ℕ} (hW : 1 ≤ W) (hd : d = 1 ∨ d = 2)
    (h : W * (W + d) = s * s) : False := by
  have h1 : W * W < s * s := by
    have hlt : W * W < W * (W + d) := mul_lt_mul_of_pos_left (by omega) (by omega)
    rwa [h] at hlt
  have h2 : s * s < (W + 1) * (W + 1) := by
    rw [← h]
    rcases hd with rfl | rfl <;> nlinarith [hW]
  have hWs : W < s := by
    by_contra hle
    push Not at hle
    have := Nat.mul_le_mul hle hle
    omega
  have hsW : s < W + 1 := by
    by_contra hle
    push Not at hle
    have := Nat.mul_le_mul hle hle
    omega
  omega

/-- `F` cannot take the same value at two indices at distance `1` or `2`. -/
lemma F_ne {F : ℕ → ℕ}
    (hsq : ∀ a b : ℕ, ∃ s : ℕ, (F a + (b + 1)) * (F b + (a + 1)) = s * s)
    (a : ℕ) {d : ℕ} (hd : d = 1 ∨ d = 2) : F a ≠ F (a + d) := by
  intro h
  obtain ⟨s, hs⟩ := hsq a (a + d)
  rw [← h] at hs
  have e : (F a + (a + d + 1)) * (F a + (a + 1))
      = (F a + (a + 1)) * ((F a + (a + 1)) + d) := by ring
  rw [e] at hs
  exact not_sq_between (by omega) hd hs

/-- Given `F a ≡ F b [MOD p]`, one can find a positive `x` such that both `F a + x`
and `F b + x` contain the prime `p` to an odd power. -/
lemma choose_x {F : ℕ → ℕ} {p : ℕ} (hp : p.Prime) {a b : ℕ}
    (h : F a ≡ F b [MOD p]) :
    ∃ x : ℕ, 1 ≤ x ∧ Odd ((Nat.factorization (F a + x)) p)
      ∧ Odd ((Nat.factorization (F b + x)) p) := by
  have hp2 : 2 ≤ p := hp.two_le
  have hM : 0 < p ^ 2 := pow_pos hp.pos 2
  have hM4 : 0 < p ^ 4 := pow_pos hp.pos 4
  -- first choice of `x`: it satisfies `F a + x = p + p^2 * (F a + 1)`
  set x := p + p ^ 2 * (F a + 1) - F a with hxdef
  have hA : F a + 1 ≤ p ^ 2 * (F a + 1) := by
    have h1 : 1 * (F a + 1) ≤ p ^ 2 * (F a + 1) :=
      mul_le_mul_left (one_le_pow₀ (by omega : (1 : ℕ) ≤ p)) (F a + 1)
    rwa [one_mul] at h1
  have hx1 : 1 ≤ x := by omega
  have hxFa : F a + x = p + p ^ 2 * (F a + 1) := by omega
  have hdiv1 : p ∣ F a + x := by
    rw [hxFa]
    exact ⟨1 + p * (F a + 1), by ring⟩
  have hndiv1 : ¬ p ^ 2 ∣ F a + x := by
    rw [hxFa]
    rintro ⟨u, hu⟩
    have e1 : p * (1 + p * (F a + 1)) = p * (p * u) := by linear_combination hu
    have e2 : 1 + p * (F a + 1) = p * u := mul_left_cancel₀ hp.pos.ne' e1
    have hd1 : p ∣ 1 := ⟨u - (F a + 1), by rw [Nat.mul_sub]; omega⟩
    exact hp.not_dvd_one hd1
  have hfa : (Nat.factorization (F a + x)) p = 1 := by
    have hn0 : F a + x ≠ 0 := by omega
    have h1 : 1 ≤ (Nat.factorization (F a + x)) p :=
      (hp.pow_dvd_iff_le_factorization hn0).mp (by rwa [pow_one])
    have h2 : ¬ 2 ≤ (Nat.factorization (F a + x)) p :=
      fun h2 => hndiv1 ((hp.pow_dvd_iff_le_factorization hn0).mpr h2)
    omega
  have hdiv2 : p ∣ F b + x := by
    have m1 : F a + x ≡ F b + x [MOD p] := h.add (Nat.ModEq.refl x)
    have m2 : F a + x ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.mpr hdiv1
    have m3 : F b + x ≡ 0 [MOD p] := m1.symm.trans m2
    exact Nat.modEq_zero_iff_dvd.mp m3
  by_cases hcase : p ^ 2 ∣ F b + x
  · -- the first choice fails for `F b`; take `x'` with `F a + x' = p^3 + p^4 * (F a + 1)`
    obtain ⟨U, hU⟩ := hcase
    set x' := p ^ 3 + p ^ 4 * (F a + 1) - F a with hx'def
    have hA' : F a + 1 ≤ p ^ 4 * (F a + 1) := by
      have h1 : 1 * (F a + 1) ≤ p ^ 4 * (F a + 1) :=
        mul_le_mul_left (one_le_pow₀ (by omega : (1 : ℕ) ≤ p)) (F a + 1)
      rwa [one_mul] at h1
    have hx'1 : 1 ≤ x' := by omega
    have hx'Fa : F a + x' = p ^ 3 + p ^ 4 * (F a + 1) := by omega
    have hdiv1' : p ^ 3 ∣ F a + x' := by
      rw [hx'Fa]
      exact ⟨1 + p * (F a + 1), by ring⟩
    have hndiv1' : ¬ p ^ 4 ∣ F a + x' := by
      rw [hx'Fa]
      rintro ⟨u, hu⟩
      have e1 : p ^ 3 * (1 + p * (F a + 1)) = p ^ 3 * (p * u) := by linear_combination hu
      have e2 : 1 + p * (F a + 1) = p * u :=
        mul_left_cancel₀ (by positivity : p ^ 3 ≠ 0) e1
      have hd1 : p ∣ 1 := ⟨u - (F a + 1), by rw [Nat.mul_sub]; omega⟩
      exact hp.not_dvd_one hd1
    have hfa' : (Nat.factorization (F a + x')) p = 3 := by
      have hn0 : F a + x' ≠ 0 := by omega
      have h1 : 3 ≤ (Nat.factorization (F a + x')) p :=
        (hp.pow_dvd_iff_le_factorization hn0).mp hdiv1'
      have h2 : ¬ 4 ≤ (Nat.factorization (F a + x')) p :=
        fun h2 => hndiv1' ((hp.pow_dvd_iff_le_factorization hn0).mpr h2)
      omega
    have hdiv2' : p ∣ F b + x' := by
      have m1 : F a + x' ≡ F b + x' [MOD p] := h.add (Nat.ModEq.refl x')
      have hp3 : p ∣ p ^ 3 := ⟨p ^ 2, by ring⟩
      have m2 : F a + x' ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.mpr (dvd_trans hp3 hdiv1')
      have m3 : F b + x' ≡ 0 [MOD p] := m1.symm.trans m2
      exact Nat.modEq_zero_iff_dvd.mp m3
    have hndiv2' : ¬ p ^ 2 ∣ F b + x' := by
      rintro ⟨V, hV⟩
      have e : p + p ^ 2 * (V + (F a + 1)) = p ^ 2 * (p + p ^ 2 * (F a + 1) + U) := by
        have ee : (F b + x') + (F a + x) = (F a + x') + (F b + x) := by ring
        rw [hxFa, hx'Fa, hU, hV] at ee
        linear_combination ee
      have hX : p ^ 2 * (V + (F a + 1)) ≤ p ^ 2 * (p + p ^ 2 * (F a + 1) + U) := by omega
      have hle : V + (F a + 1) ≤ p + p ^ 2 * (F a + 1) + U :=
        le_of_mul_le_mul_left hX hM
      have e2 : p = p ^ 2 * ((p + p ^ 2 * (F a + 1) + U) - (V + (F a + 1))) := by
        rw [Nat.mul_sub]
        omega
      have hdvd : p ^ 2 ∣ p := ⟨_, e2⟩
      have hpp : p ^ 2 ≤ p := Nat.le_of_dvd (by omega) hdvd
      have hpp2 : p * p ≤ p * 1 := by
        rw [pow_two] at hpp
        rwa [mul_one]
      have hp1 : p ≤ 1 := le_of_mul_le_mul_left hpp2 (by omega)
      exact (not_le_of_gt hp.one_lt) hp1
    have hfb' : (Nat.factorization (F b + x')) p = 1 := by
      have hn0 : F b + x' ≠ 0 := by omega
      have h1 : 1 ≤ (Nat.factorization (F b + x')) p :=
        (hp.pow_dvd_iff_le_factorization hn0).mp (by rwa [pow_one])
      have h2 : ¬ 2 ≤ (Nat.factorization (F b + x')) p :=
        fun h2 => hndiv2' ((hp.pow_dvd_iff_le_factorization hn0).mpr h2)
      omega
    exact ⟨x', hx'1, by rw [hfa']; exact ⟨1, rfl⟩, by rw [hfb']; exact odd_one⟩
  · refine ⟨x, hx1, by rw [hfa]; exact odd_one, ?_⟩
    have hfb : (Nat.factorization (F b + x)) p = 1 := by
      have hn0 : F b + x ≠ 0 := by omega
      have h1 : 1 ≤ (Nat.factorization (F b + x)) p :=
        (hp.pow_dvd_iff_le_factorization hn0).mp (by rwa [pow_one])
      have h2 : ¬ 2 ≤ (Nat.factorization (F b + x)) p :=
        fun h2 => hcase ((hp.pow_dvd_iff_le_factorization hn0).mpr h2)
      omega
    rw [hfb]; exact odd_one

/-- The key claim: any prime dividing `F a - F b` also divides `a - b`;
equivalently, `F a ≡ F b [MOD p]` implies `a ≡ b [MOD p]`. -/
lemma key {F : ℕ → ℕ}
    (hsq : ∀ a b : ℕ, ∃ s : ℕ, (F a + (b + 1)) * (F b + (a + 1)) = s * s)
    {p : ℕ} (hp : p.Prime) {a b : ℕ} (h : F a ≡ F b [MOD p]) :
    a ≡ b [MOD p] := by
  obtain ⟨x, hx1, hoddA, hoddB⟩ := choose_x hp h
  obtain ⟨s1, hs1⟩ := hsq a (x - 1)
  obtain ⟨s2, hs2⟩ := hsq b (x - 1)
  rw [Nat.sub_add_cancel hx1] at hs1 hs2
  have hd1 : p ∣ F (x - 1) + (a + 1) := kf hp (by omega) (by omega) hs1 hoddA
  have hd2 : p ∣ F (x - 1) + (b + 1) := kf hp (by omega) (by omega) hs2 hoddB
  rw [Nat.modEq_iff_dvd]
  have h1z : (p : ℤ) ∣ (F (x - 1) : ℤ) + ((a : ℤ) + 1) := by exact_mod_cast hd1
  have h2z : (p : ℤ) ∣ (F (x - 1) : ℤ) + ((b : ℤ) + 1) := by exact_mod_cast hd2
  have hsub := dvd_sub h2z h1z
  have e : (F (x - 1) : ℤ) + ((b : ℤ) + 1) - ((F (x - 1) : ℤ) + ((a : ℤ) + 1))
      = (b : ℤ) - (a : ℤ) := by ring
  rw [e] at hsub
  exact hsub

/-- Consecutive values of `F` differ by exactly `1`. -/
lemma step2 {F : ℕ → ℕ}
    (hsq : ∀ a b : ℕ, ∃ s : ℕ, (F a + (b + 1)) * (F b + (a + 1)) = s * s)
    (n : ℕ) : F (n + 1) = F n + 1 ∨ F n = F (n + 1) + 1 := by
  have hne : F n ≠ F (n + 1) := F_ne hsq n (Or.inl rfl)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · left
    by_cases hd1 : F (n + 1) - F n = 1
    · omega
    · exfalso
      obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hd1
      have hm : F n ≡ F (n + 1) [MOD p] := (Nat.modEq_iff_dvd' (le_of_lt hlt)).mpr hpd
      have hm2 : n ≡ n + 1 [MOD p] := key hsq hp hm
      have hdvd : p ∣ (n + 1) - n := (Nat.modEq_iff_dvd' (Nat.le_succ n)).mp hm2
      have e : (n + 1) - n = 1 := by omega
      rw [e] at hdvd
      exact hp.not_dvd_one hdvd
  · right
    by_cases hd1 : F n - F (n + 1) = 1
    · omega
    · exfalso
      obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hd1
      have hm : F (n + 1) ≡ F n [MOD p] := (Nat.modEq_iff_dvd' (le_of_lt hgt)).mpr hpd
      have hm2 : n + 1 ≡ n [MOD p] := key hsq hp hm
      have hdvd : p ∣ (n + 1) - n := (Nat.modEq_iff_dvd' (Nat.le_succ n)).mp hm2.symm
      have e : (n + 1) - n = 1 := by omega
      rw [e] at hdvd
      exact hp.not_dvd_one hdvd

/-- The consecutive difference is always `+1` (a constant `-1` would eventually
make `F` nonpositive, and a change of direction would force `F n = F (n + 2)`). -/
lemma all_up {F : ℕ → ℕ}
    (hsq : ∀ a b : ℕ, ∃ s : ℕ, (F a + (b + 1)) * (F b + (a + 1)) = s * s)
    (hFpos : ∀ n, 1 ≤ F n) : ∀ n, F (n + 1) = F n + 1 := by
  have h2 : ∀ n, F n ≠ F (n + 2) := fun n => F_ne hsq n (Or.inr rfl)
  have hstep : ∀ n, F (n + 1) = F n + 1 → F (n + 2) = F (n + 1) + 1 := by
    intro n hn
    rcases step2 hsq (n + 1) with h | h
    · exact h
    · exfalso
      have heq : F (n + 1 + 1) = F n := by omega
      exact h2 n heq.symm
  by_cases h1 : F 1 = F 0 + 1
  · intro n
    induction n with
    | zero => exact h1
    | succ k ih => exact hstep k ih
  · exfalso
    have h1' : F 0 = F 1 + 1 := by
      rcases step2 hsq 0 with h | h
      · exact absurd h h1
      · exact h
    have hstep' : ∀ n, F n = F (n + 1) + 1 → F (n + 1) = F (n + 2) + 1 := by
      intro n hn
      rcases step2 hsq (n + 1) with h | h
      · exfalso
        have heq : F (n + 1 + 1) = F n := by omega
        exact h2 n heq.symm
      · exact h
    have hall : ∀ n, F n = F (n + 1) + 1 := by
      intro n
      induction n with
      | zero => exact h1'
      | succ k ih => exact hstep' k ih
    have hsum : ∀ n, F n + n = F 0 := by
      intro n
      induction n with
      | zero => simp
      | succ k ih =>
          have hk := hall k
          omega
    have h0 := hsum (F 0)
    have hpos0 := hFpos (F 0)
    omega

/-- The values of `g` are completely determined: `F n = n + F 0`. -/
lemma F_eq {F : ℕ → ℕ}
    (hsq : ∀ a b : ℕ, ∃ s : ℕ, (F a + (b + 1)) * (F b + (a + 1)) = s * s)
    (hFpos : ∀ n, 1 ≤ F n) : ∀ n, F n = n + F 0 := by
  have hup : ∀ n, F (n + 1) = F n + 1 := all_up hsq hFpos
  intro n
  induction n with
  | zero => simp
  | succ k ih =>
      rw [hup k, ih]
      omega

snip end

determine SolutionSet : Set (ℤ>0 → ℤ>0) := { f | f = id ∨ ∃ c, ∀ x, f x = x + c }

problem imo2010_p3 (g : ℤ>0 → ℤ>0) :
    g ∈ SolutionSet ↔ ∀ m n, IsSquare ((g m + n) * (g n + m)) := by
  constructor
  · rintro (rfl | ⟨c, hc⟩) m n
    · use m + n; rw [id, id, add_comm m n]
    · use m + n + c; rw [hc m, hc n]; simp only [add_comm, add_left_comm]
  · intro h
    have hFpos : ∀ n, 1 ≤ gF g n := by
      intro n
      have hg := (g ⟨↑n + 1, by omega⟩).2
      have h2 : 0 < (g ⟨↑n + 1, by omega⟩).1.natAbs := Int.natAbs_pos.mpr (ne_of_gt hg)
      exact h2
    have hsq : ∀ a b : ℕ, ∃ s : ℕ, (gF g a + (b + 1)) * (gF g b + (a + 1)) = s * s := by
      intro a b
      obtain ⟨r, hr⟩ := h ⟨↑a + 1, by omega⟩ ⟨↑b + 1, by omega⟩
      refine ⟨r.1.natAbs, ?_⟩
      have hz := congrArg Subtype.val hr
      simp only [Positive.val_mul, Positive.coe_add] at hz
      have hsq2 : ((gF g a + (b + 1)) * (gF g b + (a + 1)) : ℕ)
          = r.1.natAbs * r.1.natAbs := by
        apply Nat.cast_injective (R := ℤ)
        push_cast
        simp only [gF]
        rw [Int.natAbs_of_nonneg (le_of_lt (g _).2),
          Int.natAbs_of_nonneg (le_of_lt (g _).2),
          abs_of_nonneg (le_of_lt r.2)]
        exact hz
      exact hsq2
    have hform : ∀ n, gF g n = n + gF g 0 := F_eq hsq hFpos
    have hF0 : 1 ≤ gF g 0 := hFpos 0
    by_cases h0 : gF g 0 = 1
    · show g = id ∨ ∃ c, ∀ x, g x = x + c
      left
      funext x
      apply Subtype.ext
      show (g x).1 = x.1
      set n := x.1.natAbs - 1 with hn
      have hpos : 0 < x.1.natAbs := Int.natAbs_pos.mpr (ne_of_gt x.2)
      have e2 : ((x.1.natAbs : ℤ)) = x.1 := Int.natAbs_of_nonneg (by omega)
      have hxn : x = ⟨↑n + 1, by omega⟩ := by
        apply Subtype.ext
        show x.1 = ↑n + 1
        omega
      have e4 : (g x).1 = ↑(gF g n) := by
        rw [hxn]
        show (g ⟨↑n + 1, by omega⟩).1 = ↑((g ⟨↑n + 1, by omega⟩).1.natAbs)
        exact (Int.natAbs_of_nonneg (le_of_lt (g _).2)).symm
      have e5 : (↑(gF g n) : ℤ) = ↑n + ↑(gF g 0) := by rw [hform n, Nat.cast_add]
      rw [e4, e5, h0, Nat.cast_one]
      omega
    · show g = id ∨ ∃ c, ∀ x, g x = x + c
      right
      have h2 : (2 : ℤ) ≤ gF g 0 := by
        have h2' : 2 ≤ gF g 0 := by omega
        exact_mod_cast h2'
      refine ⟨⟨(gF g 0 : ℤ) - 1, by omega⟩, ?_⟩
      intro x
      apply Subtype.ext
      simp only [Positive.coe_add]
      show (g x).1 = x.1 + ((gF g 0 : ℤ) - 1)
      set n := x.1.natAbs - 1 with hn
      have hpos : 0 < x.1.natAbs := Int.natAbs_pos.mpr (ne_of_gt x.2)
      have e2 : ((x.1.natAbs : ℤ)) = x.1 := Int.natAbs_of_nonneg (by omega)
      have hxn : x = ⟨↑n + 1, by omega⟩ := by
        apply Subtype.ext
        show x.1 = ↑n + 1
        omega
      have e4 : (g x).1 = ↑(gF g n) := by
        rw [hxn]
        show (g ⟨↑n + 1, by omega⟩).1 = ↑((g ⟨↑n + 1, by omega⟩).1.natAbs)
        exact (Int.natAbs_of_nonneg (le_of_lt (g _).2)).symm
      have e5 : (↑(gF g n) : ℤ) = ↑n + ↑(gF g 0) := by rw [hform n, Nat.cast_add]
      rw [e4, e5]
      omega

end Imo2010P3
