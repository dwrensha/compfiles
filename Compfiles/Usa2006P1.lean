/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Rat.Star
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.NumberTheory] }

/-!
# USA Mathematical Olympiad 2006, Problem 1

Let p be a prime number and let s be an integer with 0 < s < p.
Prove that there exist integers m and n with 0 < m < n < p and

  {sm/p} < {sn/p} < s/p,

where {x} = x − ⌊x⌋ denotes the fractional part of x, if and only if
s is not a divisor of p − 1.
-/

namespace Usa2006P1

snip begin

/-
### Solution sketch

Following Evan Chen's *USAMO 2006 Solution Notes*
(https://web.evanchen.cc/exams/USAMO-2006-notes.pdf).

Since `{x/p} = (x mod p)/p` for natural `x`, the fractional part inequalities
amount to `(s*m) % p < (s*n) % p < s`.  Write `g k` for the residue of
`1 + k * t` mod `p`, where `t` represents `-s⁻¹` in `ZMod p`.  Then
`s * g k ≡ s - k (mod p)`, so `g` parametrizes the indices whose residue
`s * g k % p = s - k` lies in `{1, …, s - 1}`.  Hence suitable `m, n` exist
iff `g` has an "inversion" `g l < g k` with `1 ≤ k < l ≤ s - 1`.

* If `s ∣ p - 1`, say `p - 1 = s * t`, then `1 + j * t ≤ p - t < p` for
  `j ≤ s - 1`, so `g j = 1 + j * t` is strictly increasing and no inversion
  exists.
* Conversely, if no inversion exists then `g` is nondecreasing on
  `[1, s - 1]`.  Since consecutive values differ by `t` modulo `p`, the
  sequence can never wrap around, so `g j = 1 + j * t` there, giving
  `1 + (s - 1) * t ≤ p - 1`.  As `p ∣ 1 + s * t` and
  `0 < 1 + s * t < 2 * p`, we get `1 + s * t = p`, i.e. `s ∣ p - 1`.
-/

/-- If `p` is prime and `0 < s, k < p`, then `s * k ≢ 0 (mod p)`. -/
lemma residue_ne_zero {p s : ℕ} (hp : p.Prime) (hs0 : 0 < s) (hs1 : s < p)
    {k : ℕ} (hk0 : 0 < k) (hk1 : k < p) : (s * k) % p ≠ 0 := by
  intro h
  have hdvd : p ∣ s * k := Nat.dvd_of_mod_eq_zero h
  rcases hp.dvd_mul.mp hdvd with hps | hpk
  · exact absurd (Nat.le_of_dvd hs0 hps) (not_le_of_gt hs1)
  · exact absurd (Nat.le_of_dvd hk0 hpk) (not_le_of_gt hk1)

/-- The residue of `1 + k * t` modulo `p`. -/
def g (p t k : ℕ) : ℕ := (1 + k * t) % p

/-- The fractional part inequalities are equivalent to inequalities of residues. -/
lemma fract_iff_mod (p s : ℕ) (hp : p.Prime) :
    (∃ m n : ℕ, 0 < m ∧ m < n ∧ n < p ∧
      Int.fract ((s : ℚ) * m / p) < Int.fract ((s : ℚ) * n / p) ∧
      Int.fract ((s : ℚ) * n / p) < (s : ℚ) / p) ↔
    ∃ m n : ℕ, 0 < m ∧ m < n ∧ n < p ∧ (s * m) % p < (s * n) % p ∧ (s * n) % p < s := by
  have hp0 : (0 : ℚ) < p := by exact_mod_cast hp.pos
  have key : ∀ m n : ℕ,
      (Int.fract ((s : ℚ) * m / p) < Int.fract ((s : ℚ) * n / p) ∧
        Int.fract ((s : ℚ) * n / p) < (s : ℚ) / p) ↔
      ((s * m) % p < (s * n) % p ∧ (s * n) % p < s) := by
    intro m n
    rw [← Nat.cast_mul, ← Nat.cast_mul, Int.fract_div_natCast_eq_div_natCast_mod,
      Int.fract_div_natCast_eq_div_natCast_mod, div_lt_div_iff_of_pos_right hp0,
      div_lt_div_iff_of_pos_right hp0, Nat.cast_lt, Nat.cast_lt]
  constructor
  · rintro ⟨m, n, hm, hmn, hn, h1, h2⟩
    exact ⟨m, n, hm, hmn, hn, (key m n).mp ⟨h1, h2⟩⟩
  · rintro ⟨m, n, hm, hmn, hn, h1, h2⟩
    exact ⟨m, n, hm, hmn, hn, (key m n).mpr ⟨h1, h2⟩⟩

/-- Core statement: suitable residues exist iff `s` does not divide `p - 1`. -/
lemma mod_iff_not_dvd {p s : ℕ} (hp : p.Prime) (hs0 : 0 < s) (hs1 : s < p) :
    (∃ m n : ℕ, 0 < m ∧ m < n ∧ n < p ∧ (s * m) % p < (s * n) % p ∧ (s * n) % p < s) ↔
    ¬ s ∣ p - 1 := by
  have hp0 : 0 < p := hp.pos
  have hp2 : 2 ≤ p := hp.two_le
  have : NeZero p := ⟨hp0.ne'⟩
  have : Fact p.Prime := ⟨hp⟩
  -- Since `p` is prime, `s` is a unit in `ZMod p`; let `t` be the residue of `-s⁻¹`.
  have hsne : (s : ZMod p) ≠ 0 := by
    intro h
    have h2 := congrArg ZMod.val h
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hs1, ZMod.val_zero] at h2
    omega
  obtain ⟨t, htz, ht1⟩ : ∃ t : ℕ, (t : ZMod p) = -(s : ZMod p)⁻¹ ∧ t < p :=
    ⟨_, ZMod.natCast_zmod_val _, ZMod.val_lt _⟩
  -- Then `s * t ≡ -1 (mod p)`.
  have hst : (s : ZMod p) * (t : ZMod p) = -1 := by
    rw [htz, mul_neg, mul_inv_cancel₀ hsne]
  have ht0 : 0 < t := by
    rcases Nat.eq_zero_or_pos t with h | h
    · rw [h, Nat.cast_zero, mul_zero] at hst
      exact absurd hst.symm (neg_ne_zero.mpr one_ne_zero)
    · exact h
  -- For `k ≤ s` we have `s * g k ≡ s - k (mod p)`; in fact the residues agree.
  have hcong : ∀ k : ℕ, k ≤ s → (s * g p t k) % p = s - k := by
    intro k hk
    have h1 : ((s * g p t k : ℕ) : ZMod p) = ((s - k : ℕ) : ZMod p) := by
      have e1 : ((g p t k : ℕ) : ZMod p) = 1 + (k : ZMod p) * (t : ZMod p) := by
        show (((1 + k * t) % p : ℕ) : ZMod p) = _
        rw [ZMod.natCast_mod, Nat.cast_add, Nat.cast_one, Nat.cast_mul]
      have e2 : (s : ZMod p) * (1 + (k : ZMod p) * (t : ZMod p)) =
          (s : ZMod p) - (k : ZMod p) := by
        calc (s : ZMod p) * (1 + (k : ZMod p) * (t : ZMod p))
            = (s : ZMod p) + (k : ZMod p) * ((s : ZMod p) * (t : ZMod p)) := by ring
          _ = (s : ZMod p) - (k : ZMod p) := by rw [hst]; ring
      rw [Nat.cast_mul, e1, e2, Nat.cast_sub hk]
    have h2 : (s * g p t k) % p = (s - k) % p := (ZMod.natCast_eq_natCast_iff' _ _ _).mp h1
    rwa [Nat.mod_eq_of_lt (by omega : s - k < p)] at h2
  -- `g k` lies in `[1, p)` for `1 ≤ k ≤ s - 1`.
  have hgpos : ∀ k : ℕ, 1 ≤ k → k ≤ s - 1 → 0 < g p t k := by
    intro k hk1 hks
    rcases Nat.eq_zero_or_pos (g p t k) with h | h
    · have h2 := hcong k (le_trans hks (Nat.sub_le s 1))
      rw [h, mul_zero, Nat.zero_mod] at h2
      omega
    · exact h
  have hglt : ∀ k : ℕ, g p t k < p := fun k => Nat.mod_lt _ hp0
  -- Suitable `m, n` exist iff `g` has an inversion `g l < g k` with `k < l`.
  have key : (∃ m n : ℕ, 0 < m ∧ m < n ∧ n < p ∧ (s * m) % p < (s * n) % p ∧
      (s * n) % p < s) ↔
      ∃ k l : ℕ, 1 ≤ k ∧ k < l ∧ l ≤ s - 1 ∧ g p t l < g p t k := by
    constructor
    · rintro ⟨m, n, hm0, hmn, hnp, hrm, hrn⟩
      have hmp : m < p := lt_trans hmn hnp
      have hrm0 : (s * m) % p ≠ 0 := residue_ne_zero hp hs0 hs1 hm0 hmp
      have hrn0 : (s * n) % p ≠ 0 := residue_ne_zero hp hs0 hs1 (by omega) hnp
      have hmeq : m = g p t (s - (s * m) % p) := by
        have hc : (s * g p t (s - (s * m) % p)) % p = (s * m) % p := by
          have h1 := hcong (s - (s * m) % p) (by omega)
          rwa [Nat.sub_sub_self (by omega : (s * m) % p ≤ s)] at h1
        have h2 : ((s * g p t (s - (s * m) % p) : ℕ) : ZMod p) = ((s * m : ℕ) : ZMod p) :=
          (ZMod.natCast_eq_natCast_iff' _ _ _).mpr hc
        rw [Nat.cast_mul, Nat.cast_mul] at h2
        have h3 := mul_left_cancel₀ hsne h2
        have h4 := congrArg ZMod.val h3
        rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hmp,
          Nat.mod_eq_of_lt (hglt _)] at h4
        exact h4.symm
      have hneq : n = g p t (s - (s * n) % p) := by
        have hc : (s * g p t (s - (s * n) % p)) % p = (s * n) % p := by
          have h1 := hcong (s - (s * n) % p) (by omega)
          rwa [Nat.sub_sub_self (by omega : (s * n) % p ≤ s)] at h1
        have h2 : ((s * g p t (s - (s * n) % p) : ℕ) : ZMod p) = ((s * n : ℕ) : ZMod p) :=
          (ZMod.natCast_eq_natCast_iff' _ _ _).mpr hc
        rw [Nat.cast_mul, Nat.cast_mul] at h2
        have h3 := mul_left_cancel₀ hsne h2
        have h4 := congrArg ZMod.val h3
        rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hnp,
          Nat.mod_eq_of_lt (hglt _)] at h4
        exact h4.symm
      exact ⟨s - (s * n) % p, s - (s * m) % p, by omega, by omega, by omega,
        hmeq ▸ hneq ▸ hmn⟩
    · rintro ⟨k, l, hk1, hkl, hls, hglk⟩
      refine ⟨g p t l, g p t k, hgpos l (by omega) hls, hglk, hglt _, ?_, ?_⟩
      · rw [hcong l (by omega), hcong k (by omega)]
        omega
      · rw [hcong k (by omega)]
        omega
  rw [key]
  constructor
  · -- If an inversion exists then `s ∤ p - 1`: otherwise `g` is strictly increasing.
    rintro ⟨k, l, hk1, hkl, hls, hglk⟩ ⟨t', ht'⟩
    have ht'0 : 0 < t' := by
      rcases Nat.eq_zero_or_pos t' with h | h
      · rw [h, mul_zero] at ht'
        omega
      · exact h
    have ht'1 : t' < p := by
      have h2 : t' ≤ s * t' := Nat.le_mul_of_pos_left t' hs0
      omega
    -- `t` and `t'` coincide, as both are residues of `-s⁻¹` modulo `p`.
    have htt' : t = t' := by
      have e1 : ((s * t' : ℕ) : ZMod p) = -1 := by
        rw [← ht', Nat.cast_sub (show 1 ≤ p by omega), Nat.cast_one, ZMod.natCast_self,
          zero_sub]
      have e2 : ((s * t : ℕ) : ZMod p) = -1 := by
        rw [Nat.cast_mul]; exact hst
      have h2e : ((s * t' : ℕ) : ZMod p) = ((s * t : ℕ) : ZMod p) := e1.trans e2.symm
      rw [Nat.cast_mul, Nat.cast_mul] at h2e
      have h2 := mul_left_cancel₀ hsne h2e
      have h3 := congrArg ZMod.val h2
      rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt ht'1,
        Nat.mod_eq_of_lt ht1] at h3
      exact h3.symm
    have hstt : s * t = p - 1 := by rw [htt']; omega
    -- Then `1 + j * t < p` for `j ≤ s - 1`, so `g j = 1 + j * t` is strictly increasing.
    have hval : ∀ j : ℕ, 1 ≤ j → j ≤ s - 1 → g p t j = 1 + j * t := by
      intro j hj1 hj2
      have hub : 1 + j * t < p := by
        have h1 : j * t ≤ (s - 1) * t := Nat.mul_le_mul_right t hj2
        have e : 1 + (s - 1) * t = p - t := by
          have e2 : (s - 1) * t = s * t - t := by rw [Nat.sub_mul, one_mul]
          omega
        omega
      exact Nat.mod_eq_of_lt hub
    have ek : g p t k = 1 + k * t := hval k hk1 (by omega)
    have el : g p t l = 1 + l * t := hval l (by omega) hls
    have hlt : g p t k < g p t l := by
      rw [ek, el]
      have h2 : k * t < l * t := mul_lt_mul_of_pos_right hkl ht0
      omega
    omega
  · -- Conversely, if there is no inversion then `g` is nondecreasing, which
    -- forces `1 + s * t = p`, i.e. `s ∣ p - 1`.
    intro hndvd
    by_contra hnex
    have hmono : ∀ k l : ℕ, 1 ≤ k → k < l → l ≤ s - 1 → g p t k ≤ g p t l := by
      intro k l hk1 hkl hls
      by_contra h
      exact hnex ⟨k, l, hk1, hkl, hls, Nat.lt_of_not_le h⟩
    by_cases hs1' : s = 1
    · subst hs1'
      exact hndvd (one_dvd _)
    · have hs2 : 2 ≤ s := by omega
      -- `t ≠ p - 1` because `s ≥ 2`.
      have ht2 : t ≤ p - 2 := by
        by_contra h
        have htp : t = p - 1 := by omega
        have e : (s : ZMod p) = ((1 : ℕ) : ZMod p) := by
          have ett : (t : ZMod p) = -1 := by
            rw [htp, Nat.cast_sub (show 1 ≤ p by omega), Nat.cast_one, ZMod.natCast_self,
              zero_sub]
          rw [ett, mul_neg, mul_one] at hst
          rw [Nat.cast_one]
          exact neg_inj.mp hst
        have hsmod : s % p = 1 % p := (ZMod.natCast_eq_natCast_iff' _ _ _).mp e
        rw [Nat.mod_eq_of_lt hs1, Nat.mod_eq_of_lt (show 1 < p by omega)] at hsmod
        omega
      -- No wrap-around: `g j = 1 + j * t` for all `1 ≤ j ≤ s - 1`.
      have hval : ∀ j : ℕ, 1 ≤ j → j ≤ s - 1 → g p t j = 1 + j * t := by
        intro j hj1
        induction j, hj1 using Nat.le_induction with
        | base =>
            intro _
            exact Nat.mod_eq_of_lt (by omega)
        | succ j hj1 ih =>
            intro hj2
            have ihj : g p t j = 1 + j * t := ih (by omega)
            have hle : g p t j ≤ g p t (j + 1) := hmono j (j + 1) hj1 (Nat.lt_succ_self j) hj2
            have heq : g p t (j + 1) = (g p t j + t) % p := by
              show (1 + (j + 1) * t) % p = ((1 + j * t) % p + t) % p
              rw [show 1 + (j + 1) * t = (1 + j * t) + t by ring, Nat.add_mod,
                Nat.mod_eq_of_lt ht1]
            by_cases hbig : g p t j + t < p
            · rw [heq, Nat.mod_eq_of_lt hbig, ihj]
              ring
            · exfalso
              have hge : p ≤ g p t j + t := Nat.le_of_not_lt hbig
              have hsub : (g p t j + t) % p = g p t j + t - p := by
                rw [Nat.mod_eq_sub_mod hge,
                  Nat.mod_eq_of_lt (by have h1 := hglt j; omega)]
              omega
      -- In particular `1 + (s - 1) * t ≤ p - 1`.
      have hfin : g p t (s - 1) = 1 + (s - 1) * t := hval (s - 1) (by omega) (le_refl _)
      have hbound : 1 + (s - 1) * t ≤ p - 1 := by
        have h2 := hglt (s - 1)
        omega
      -- But `p ∣ 1 + s * t` and `0 < 1 + s * t < 2 * p`, so `1 + s * t = p`.
      have hdvd : p ∣ 1 + s * t := by
        have e : ((1 + s * t : ℕ) : ZMod p) = 0 := by
          rw [Nat.cast_add, Nat.cast_one, Nat.cast_mul, hst, add_neg_cancel]
        have h2 := congrArg ZMod.val e
        rw [ZMod.val_natCast, ZMod.val_zero] at h2
        exact Nat.dvd_of_mod_eq_zero h2
      have h1st : 1 + s * t = p := by
        obtain ⟨c, hc⟩ := hdvd
        have hub : 1 + s * t < 2 * p := by
          have es : s * t = (s - 1) * t + t := by
            conv_lhs => rw [← Nat.sub_add_cancel (show 1 ≤ s by omega)]
            rw [add_mul, one_mul]
          omega
        have hc0 : 0 < c := by
          rcases Nat.eq_zero_or_pos c with h | h
          · rw [h, mul_zero] at hc
            omega
          · exact h
        have hc2 : c = 1 := by
          have h3 : p * c < p * 2 := by omega
          have h4 := Nat.lt_of_mul_lt_mul_left h3
          omega
        rw [hc2, mul_one] at hc
        exact hc
      exact hndvd ⟨t, by omega⟩

snip end

problem usa2006_p1 (p s : ℕ) (hp : p.Prime) (hs0 : 0 < s) (hs1 : s < p) :
    (∃ m n : ℕ, 0 < m ∧ m < n ∧ n < p ∧
      Int.fract ((s : ℚ) * m / p) < Int.fract ((s : ℚ) * n / p) ∧
      Int.fract ((s : ℚ) * n / p) < (s : ℚ) / p) ↔
    ¬ s ∣ p - 1 := by
  rw [fract_iff_mod p s hp]
  exact mod_iff_not_dvd hp hs0 hs1

end Usa2006P1
