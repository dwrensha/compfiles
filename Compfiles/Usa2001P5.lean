/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.RingTheory.Int.Basic
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.NumberTheory] }

/-!
# USA Mathematical Olympiad 2001, Problem 5

Let S be a set of integers (not necessarily positive) such that

(a) there exist a, b ∈ S with gcd(a, b) = gcd(a − 2, b − 2) = 1;
(b) if x and y are elements of S (possibly equal), then x² − y also belongs to S.

Prove that S is the set of all integers.
-/

namespace Usa2001P5

snip begin

/-- An integer `d` is *shifty* for a set `S` if shifting by `d` does not change
membership in `S`. The shifty integers form a subgroup of `ℤ`, and the proof below
shows that `1` is shifty, which forces `S = ℤ`. -/
def Shifty (S : Set ℤ) (d : ℤ) : Prop := ∀ x : ℤ, x ∈ S ↔ x + d ∈ S

lemma shifty_zero (S : Set ℤ) : Shifty S 0 := fun x ↦ by simp

lemma shifty_neg {S : Set ℤ} {d : ℤ} (h : Shifty S d) : Shifty S (-d) := by
  intro x
  have h' := h (x + -d)
  have e : x + -d + d = x := by ring
  rw [e] at h'
  exact h'.symm

lemma shifty_add {S : Set ℤ} {d e : ℤ} (hd : Shifty S d) (he : Shifty S e) :
    Shifty S (d + e) := by
  intro x
  have h_eq : x + (d + e) = x + d + e := by ring
  rw [h_eq]
  exact (hd x).trans (he (x + d))

lemma shifty_nsmul {S : Set ℤ} {d : ℤ} (hd : Shifty S d) (n : ℕ) :
    Shifty S (n • d) := by
  induction n with
  | zero => simpa using shifty_zero S
  | succ k ih =>
      rw [succ_nsmul]
      exact shifty_add ih hd

lemma shifty_zsmul {S : Set ℤ} {d : ℤ} (hd : Shifty S d) (n : ℤ) :
    Shifty S (n • d) := by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · simpa using shifty_nsmul hd m
  · simpa using shifty_neg (shifty_nsmul hd m)

/-- If `u` and `v` belong to `S`, then `v^2 - u^2` is shifty for `S`. -/
lemma shifty_sq_sub_sq {S : Set ℤ} (hS : ∀ x ∈ S, ∀ y ∈ S, x^2 - y ∈ S)
    {u v : ℤ} (hu : u ∈ S) (hv : v ∈ S) : Shifty S (v^2 - u^2) := by
  intro x
  constructor
  · intro hx
    have h1 : u^2 - x ∈ S := hS u hu x hx
    have h2 : v^2 - (u^2 - x) ∈ S := hS v hv _ h1
    have e : x + (v^2 - u^2) = v^2 - (u^2 - x) := by ring
    rwa [e]
  · intro hx
    have h1 : v^2 - (x + (v^2 - u^2)) ∈ S := hS v hv _ hx
    have h2 : u^2 - (v^2 - (x + (v^2 - u^2))) ∈ S := hS u hu _ h1
    have e : u^2 - (v^2 - (x + (v^2 - u^2))) = x := by ring
    rwa [e] at h2

/-- The number-theoretic core: no prime divides all three of
`a^2 - b^2`, `a^3 * (a - 2)` and `b^3 * (b - 2)`. -/
lemma not_prime_dvd_three {a b : ℤ} (h1 : Int.gcd a b = 1)
    (h2 : Int.gcd (a - 2) (b - 2) = 1) {p : ℤ} (hp : Prime p) :
    ¬ (p ∣ a^2 - b^2 ∧ p ∣ a^3 * (a - 2) ∧ p ∣ b^3 * (b - 2)) := by
  rintro ⟨hA, hB, hC⟩
  have ha_or : p ∣ a ∨ p ∣ a - 2 := by
    rcases hp.dvd_or_dvd hB with h | h
    · exact Or.inl (hp.dvd_of_dvd_pow h)
    · exact Or.inr h
  have hb_or : p ∣ b ∨ p ∣ b - 2 := by
    rcases hp.dvd_or_dvd hC with h | h
    · exact Or.inl (hp.dvd_of_dvd_pow h)
    · exact Or.inr h
  have hab_or : p ∣ a - b ∨ p ∣ a + b := by
    have hAB : p ∣ (a + b) * (a - b) := by
      have e : (a + b) * (a - b) = a^2 - b^2 := by ring
      rwa [e]
    rcases hp.dvd_or_dvd hAB with h | h
    · exact Or.inr h
    · exact Or.inl h
  have dvd_gcd_ab : p ∣ a → p ∣ b → False := by
    intro hpa hpb
    have hgc : p ∣ (Int.gcd a b : ℤ) := by
      rw [Int.gcd_eq_gcd_ab]
      exact dvd_add (dvd_mul_of_dvd_left hpa _) (dvd_mul_of_dvd_left hpb _)
    have hp1 : p ∣ (1 : ℤ) := by simpa [h1] using hgc
    exact hp.not_dvd_one hp1
  rcases ha_or with hpa | hpa2
  · rcases hb_or with hpb | hpb2
    · exact dvd_gcd_ab hpa hpb
    · rcases hab_or with h | h
      · exact dvd_gcd_ab hpa (by
          have h' := dvd_sub hpa h
          rwa [show a - (a - b) = b by ring] at h')
      · exact dvd_gcd_ab hpa (by
          have h' := dvd_sub h hpa
          rwa [show a + b - a = b by ring] at h')
  · rcases hb_or with hpb | hpb2
    · rcases hab_or with h | h
      · exact dvd_gcd_ab (by
          have h' := dvd_add h hpb
          rwa [show a - b + b = a by ring] at h') hpb
      · exact dvd_gcd_ab (by
          have h' := dvd_sub h hpb
          rwa [show a + b - b = a by ring] at h') hpb
    · have hgc : p ∣ (Int.gcd (a - 2) (b - 2) : ℤ) := by
        rw [Int.gcd_eq_gcd_ab]
        exact dvd_add (dvd_mul_of_dvd_left hpa2 _) (dvd_mul_of_dvd_left hpb2 _)
      have hp1 : p ∣ (1 : ℤ) := by simpa [h2] using hgc
      exact hp.not_dvd_one hp1

/-- The gcd of the three shifty integers `a^2 - b^2`, `a^3 * (a - 2)`,
`b^3 * (b - 2)` is `1`. -/
lemma gcd_gcd_eq_one {a b : ℤ} (h1 : Int.gcd a b = 1)
    (h2 : Int.gcd (a - 2) (b - 2) = 1) :
    Int.gcd (↑(Int.gcd (a^2 - b^2) (a^3 * (a - 2)))) (b^3 * (b - 2)) = 1 := by
  by_contra hne
  obtain ⟨p, hp, hpd⟩ := Int.exists_prime_and_dvd
    (n := ↑(Int.gcd (↑(Int.gcd (a^2 - b^2) (a^3 * (a - 2)))) (b^3 * (b - 2))))
    (by simpa using hne)
  have hpA : p ∣ a^2 - b^2 :=
    dvd_trans hpd (dvd_trans (Int.gcd_dvd_left _ _) (Int.gcd_dvd_left _ _))
  have hpB : p ∣ a^3 * (a - 2) :=
    dvd_trans hpd (dvd_trans (Int.gcd_dvd_left _ _) (Int.gcd_dvd_right _ _))
  have hpC : p ∣ b^3 * (b - 2) := dvd_trans hpd (Int.gcd_dvd_right _ _)
  exact not_prime_dvd_three h1 h2 hp ⟨hpA, hpB, hpC⟩

/-- Bézout's identity for three integers whose gcd is `1`. -/
lemma bezout_three {A B C : ℤ} (h : Int.gcd (↑(Int.gcd A B)) C = 1) :
    ∃ m n r : ℤ, m * A + n * B + r * C = 1 := by
  set s := Int.gcdA A B with hs
  set t := Int.gcdB A B with ht
  set G : ℤ := ↑(Int.gcd A B) with hG
  set u := Int.gcdA G C with hu
  set v := Int.gcdB G C with hv
  have e1 : G = A * s + B * t := Int.gcd_eq_gcd_ab A B
  have e2 : (1 : ℤ) = G * u + C * v := by
    have hbez := Int.gcd_eq_gcd_ab G C
    rw [← hu, ← hv, h] at hbez
    norm_cast at hbez
  exact ⟨s * u, t * u, v, by rw [e2, e1]; ring⟩

snip end

problem usa2001_p5 (S : Set ℤ) (hS : ∀ x ∈ S, ∀ y ∈ S, x^2 - y ∈ S)
    (a b : ℤ) (ha : a ∈ S) (hb : b ∈ S)
    (h1 : Int.gcd a b = 1) (h2 : Int.gcd (a - 2) (b - 2) = 1) :
    S = Set.univ := by
  -- The three integers `a^2 - b^2`, `a^3 * (a - 2)`, `b^3 * (b - 2)` are shifty.
  have hA : Shifty S (a^2 - b^2) := shifty_sq_sub_sq hS hb ha
  have ha' : a^2 - a ∈ S := hS a ha a ha
  have hb' : b^2 - b ∈ S := hS b hb b hb
  have hB : Shifty S (a^3 * (a - 2)) := by
    have h := shifty_sq_sub_sq hS ha ha'
    have e : (a^2 - a)^2 - a^2 = a^3 * (a - 2) := by ring
    rwa [e] at h
  have hC : Shifty S (b^3 * (b - 2)) := by
    have h := shifty_sq_sub_sq hS hb hb'
    have e : (b^2 - b)^2 - b^2 = b^3 * (b - 2) := by ring
    rwa [e] at h
  -- Their gcd is `1`, so Bézout makes `1` itself shifty.
  obtain ⟨m, n, r, hmnr⟩ := bezout_three (gcd_gcd_eq_one h1 h2)
  have hone : Shifty S 1 := by
    have h := shifty_add (shifty_add (shifty_zsmul hA m) (shifty_zsmul hB n))
      (shifty_zsmul hC r)
    simp only [Int.zsmul_eq_mul, hmnr] at h
    exact h
  -- Hence every integer is in `S`, being a shift of `a`.
  apply Set.eq_univ_of_forall
  intro x
  have hx : Shifty S (x - a) := by
    have h := shifty_zsmul hone (x - a)
    simp only [Int.zsmul_eq_mul, mul_one] at h
    exact h
  have hmem := (hx a).mp ha
  have e : a + (x - a) = x := by ring
  rwa [e] at hmem
