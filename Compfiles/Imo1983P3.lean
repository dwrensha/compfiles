/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Tactic
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.NumberTheory] }

/-!
# International Mathematical Olympiad 1983, Problem 3

Let a, b, c be positive integers, no two of which have a common divisor
greater than 1. Show that 2abc − ab − bc − ca is the largest integer
which cannot be expressed in the form xbc + yca + zab, where x, y, z
are non-negative integers.
-/

namespace Imo1983P3

snip begin

/-- Two-variable Chicken McNugget over `ℤ`: for coprime positive `b c`, every
integer `M > b*c - b - c` is a nonnegative combination of `c` and `b`. -/
lemma two_var {b c : ℕ} (hb : 0 < b) (hc : 0 < c) (hbc : Nat.Coprime b c)
    (M : ℤ) (hM : M > (b : ℤ) * c - b - c) :
    ∃ y z : ℕ, M = y * (c : ℤ) + z * (b : ℤ) := by
  have hbz : (0 : ℤ) < b := by exact_mod_cast hb
  have hcz : (0 : ℤ) < c := by exact_mod_cast hc
  -- Bézout: `b * s + c * t = 1` for some integers `s, t`.
  obtain ⟨s, t, hst⟩ : ∃ s t : ℤ, (b : ℤ) * s + (c : ℤ) * t = 1 := by
    refine ⟨Nat.gcdA b c, Nat.gcdB b c, ?_⟩
    have h1 := Nat.gcd_eq_gcd_ab b c
    rw [show Nat.gcd b c = 1 from hbc] at h1
    push_cast at h1 ⊢
    linarith [h1]
  -- Euclidean division: `M * t = b * q + y` with `0 ≤ y < b`.
  obtain ⟨q, y, hdiv, hy0, hyb⟩ :
      ∃ q y : ℤ, M * t = (b : ℤ) * q + y ∧ 0 ≤ y ∧ y < (b : ℤ) :=
    ⟨(M * t) / (b : ℤ), (M * t) % (b : ℤ), (Int.mul_ediv_add_emod _ _).symm,
     Int.emod_nonneg _ hbz.ne', Int.emod_lt_of_pos _ hbz⟩
  -- Then `M = y * c + z * b` with `z = M * s + q * c`.
  have hMz : M = y * (c : ℤ) + (M * s + q * (c : ℤ)) * (b : ℤ) := by
    have e1 : M = M * s * (b : ℤ) + M * t * (c : ℤ) := by
      calc M = M * ((b : ℤ) * s + (c : ℤ) * t) := by rw [hst]; ring
        _ = M * s * b + M * t * c := by ring
    calc M = M * s * (b : ℤ) + M * t * (c : ℤ) := e1
      _ = M * s * b + ((b : ℤ) * q + y) * c := by rw [hdiv]
      _ = y * c + (M * s + q * (c : ℤ)) * b := by ring
  -- The bound `M > b*c - b - c` forces `z ≥ 0`.
  have hz0 : 0 ≤ M * s + q * (c : ℤ) := by
    have e2 : (M * s + q * (c : ℤ)) * (b : ℤ) = M - y * (c : ℤ) := by linarith [hMz]
    have hyc : y * (c : ℤ) ≤ ((b : ℤ) - 1) * c :=
      mul_le_mul_of_nonneg_right (by lia) (le_of_lt hcz)
    have e3 : M - y * (c : ℤ) > -(b : ℤ) := by linarith [hM, hyc]
    by_contra hneg
    push Not at hneg
    have hzle : M * s + q * (c : ℤ) ≤ -1 := by lia
    have hle : (M * s + q * (c : ℤ)) * (b : ℤ) ≤ -1 * (b : ℤ) :=
      mul_le_mul_of_nonneg_right hzle (le_of_lt hbz)
    linarith [e2, e3, hle]
  refine ⟨y.toNat, (M * s + q * (c : ℤ)).toNat, ?_⟩
  rw [Int.toNat_of_nonneg hy0, Int.toNat_of_nonneg hz0]
  exact hMz

/-- Every integer `n > 2*a*b*c - a*b - b*c - c*a` is expressible as
`x * (b*c) + y * (c*a) + z * (a*b)` with nonnegative `x y z`. -/
lemma rep {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b) (hbc : Nat.Coprime b c) (hca : Nat.Coprime c a)
    (n : ℤ) (hn : n > 2 * (a : ℤ) * b * c - a * b - b * c - c * a) :
    ∃ x y z : ℕ, n = x * ((b : ℤ) * c) + y * ((c : ℤ) * a) + z * ((a : ℤ) * b) := by
  have haz : (0 : ℤ) < a := by exact_mod_cast ha
  have habc : Nat.Coprime a (b * c) := hab.mul_right hca.symm
  -- Bézout: `a * s + (b*c) * t = 1` for some integers `s, t`.
  obtain ⟨s, t, hst⟩ : ∃ s t : ℤ, (a : ℤ) * s + (b : ℤ) * c * t = 1 := by
    refine ⟨Nat.gcdA a (b * c), Nat.gcdB a (b * c), ?_⟩
    have h1 := Nat.gcd_eq_gcd_ab a (b * c)
    rw [show Nat.gcd a (b * c) = 1 from habc] at h1
    push_cast at h1 ⊢
    linarith [h1]
  -- Euclidean division: `n * t = a * q + x` with `0 ≤ x < a`.
  obtain ⟨q, x, hdiv, hx0, hxa⟩ :
      ∃ q x : ℤ, n * t = (a : ℤ) * q + x ∧ 0 ≤ x ∧ x < (a : ℤ) :=
    ⟨(n * t) / (a : ℤ), (n * t) % (a : ℤ), (Int.mul_ediv_add_emod _ _).symm,
     Int.emod_nonneg _ haz.ne', Int.emod_lt_of_pos _ haz⟩
  -- Then `n = x * (b*c) + a * M` with `M = n * s + q * (b*c)`.
  have hn_eq : n = x * ((b : ℤ) * c) + (a : ℤ) * (n * s + q * ((b : ℤ) * c)) := by
    have e1 : n = n * s * (a : ℤ) + n * t * ((b : ℤ) * c) := by
      calc n = n * ((a : ℤ) * s + (b : ℤ) * c * t) := by rw [hst]; ring
        _ = n * s * a + n * t * (b * c) := by ring
    calc n = n * s * (a : ℤ) + n * t * ((b : ℤ) * c) := e1
      _ = n * s * a + ((a : ℤ) * q + x) * (b * c) := by rw [hdiv]
      _ = x * (b * c) + (a : ℤ) * (n * s + q * (b * c)) := by ring
  -- The bound on `n` yields `M > b*c - b - c`.
  have hMgt : n * s + q * ((b : ℤ) * c) > (b : ℤ) * c - b - c := by
    have hxbc : x * ((b : ℤ) * c) ≤ ((a : ℤ) - 1) * (b * c) :=
      mul_le_mul_of_nonneg_right (by lia) (by positivity)
    have e2 : (a : ℤ) * (n * s + q * ((b : ℤ) * c)) = n - x * ((b : ℤ) * c) := by
      linarith [hn_eq]
    have e3 : (a : ℤ) * (n * s + q * ((b : ℤ) * c)) >
        (a : ℤ) * ((b : ℤ) * c - b - c) := by
      rw [e2]
      linarith [hn, hxbc]
    exact lt_of_mul_lt_mul_left e3 (le_of_lt haz)
  -- Apply the two-variable lemma to `M`.
  obtain ⟨y, z, hyz⟩ := two_var hb hc hbc _ hMgt
  refine ⟨x.toNat, y, z, ?_⟩
  rw [Int.toNat_of_nonneg hx0]
  rw [hyz] at hn_eq
  rw [hn_eq]
  ring

snip end

problem imo1983_p3 (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b) (hbc : Nat.Coprime b c) (hca : Nat.Coprime c a) :
    IsGreatest
      {n : ℤ | ¬∃ x y z : ℕ, n = x * (b * c) + y * (c * a) + z * (a * b)}
      (2 * a * b * c - a * b - b * c - c * a) := by
  constructor
  · -- `2abc - ab - bc - ca` is not representable.
    rintro ⟨x, y, z, h⟩
    have h2 : 2 * (a * b * c) = b * c * (x + 1) + c * a * (y + 1) + a * b * (z + 1) := by
      have h2z : ((2 * (a * b * c) : ℕ) : ℤ) =
          ((b * c * (x + 1) + c * a * (y + 1) + a * b * (z + 1) : ℕ) : ℤ) := by
        push_cast
        linarith [h]
      exact_mod_cast h2z
    -- Divisibility arguments: `a ∣ x + 1`, `b ∣ y + 1`, `c ∣ z + 1`.
    have hd1 : a ∣ c * a * (y + 1) := dvd_mul_of_dvd_left (dvd_mul_left a c) (y + 1)
    have hd2 : a ∣ a * b * (z + 1) := dvd_mul_of_dvd_left (dvd_mul_right a b) (z + 1)
    have hd3 : a ∣ b * c * (x + 1) := by
      have hsum : a ∣ 2 * (a * b * c) := ⟨2 * (b * c), by ring⟩
      rw [h2] at hsum
      have h4 : a ∣ b * c * (x + 1) + c * a * (y + 1) := (Nat.dvd_add_iff_left hd2).mpr hsum
      exact (Nat.dvd_add_iff_left hd1).mpr h4
    have hdx : a ∣ x + 1 := (hab.mul_right hca.symm).dvd_of_dvd_mul_left hd3
    have hx1 : a ≤ x + 1 := Nat.le_of_dvd (by lia) hdx
    have hd1' : b ∣ b * c * (x + 1) := dvd_mul_of_dvd_left (dvd_mul_right b c) (x + 1)
    have hd2' : b ∣ a * b * (z + 1) := dvd_mul_of_dvd_left (dvd_mul_left b a) (z + 1)
    have hdy : b ∣ y + 1 := by
      have hsum : b ∣ 2 * (a * b * c) := ⟨2 * (a * c), by ring⟩
      rw [h2] at hsum
      have h4 : b ∣ b * c * (x + 1) + c * a * (y + 1) := (Nat.dvd_add_iff_left hd2').mpr hsum
      exact (hbc.mul_right hab.symm).dvd_of_dvd_mul_left ((Nat.dvd_add_iff_right hd1').mpr h4)
    have hy1 : b ≤ y + 1 := Nat.le_of_dvd (by lia) hdy
    have hd1'' : c ∣ b * c * (x + 1) := dvd_mul_of_dvd_left (dvd_mul_left c b) (x + 1)
    have hd2'' : c ∣ c * a * (y + 1) := dvd_mul_of_dvd_left (dvd_mul_right c a) (y + 1)
    have hdz : c ∣ z + 1 := by
      have hsum : c ∣ 2 * (a * b * c) := ⟨2 * (a * b), by ring⟩
      rw [h2] at hsum
      exact (hca.mul_right hbc.symm).dvd_of_dvd_mul_left
        ((Nat.dvd_add_iff_right (dvd_add hd1'' hd2'')).mpr hsum)
    have hz1 : c ≤ z + 1 := Nat.le_of_dvd (by lia) hdz
    -- Now `2abc ≥ 3abc`, contradiction.
    have hpos : 0 < a * b * c := by positivity
    have g1 : a * b * c ≤ b * c * (x + 1) := by
      calc a * b * c = b * c * a := by ring
        _ ≤ b * c * (x + 1) := mul_le_mul_of_nonneg_left hx1 (Nat.zero_le _)
    have g2 : a * b * c ≤ c * a * (y + 1) := by
      calc a * b * c = c * a * b := by ring
        _ ≤ c * a * (y + 1) := mul_le_mul_of_nonneg_left hy1 (Nat.zero_le _)
    have g3 : a * b * c ≤ a * b * (z + 1) := mul_le_mul_of_nonneg_left hz1 (Nat.zero_le _)
    lia
  · -- Every larger integer is representable.
    intro n hn
    by_contra hle
    push Not at hle
    have hle' : n > 2 * (a : ℤ) * b * c - a * b - b * c - c * a := by
      linarith [hle]
    obtain ⟨x, y, z, hxyz⟩ := rep ha hb hc hab hbc hca n hle'
    apply hn
    refine ⟨x, y, z, ?_⟩
    linarith [hxyz]

end Imo1983P3
