/-
Copyright (c) 2026 lean-tom. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Liao
-/
import Mathlib
import ProblemExtraction

problem_file {
  tags := [.Algebra]
}

/-!
# International Mathematical Olympiad 1998, Problem 6

Determine the least possible value of `f(1998)`, where `f : ℕ+ → ℕ+` satisfies
`f(n^2 * f(m)) = m * f(n)^2` for all `m, n ∈ ℕ+`.
-/

namespace Imo1998P6

snip begin

set_option maxHeartbeats 1600000

section AlgebraicLemmas

variable (f : ℕ+ → ℕ+) (hf : ∀ m n : ℕ+, f (n ^ 2 * f m) = m * f n ^ 2)
include hf

lemma f_f_eq (n : ℕ+) : f (f n) = n * (f 1) ^ 2 := by
  have h := hf n 1
  simpa using h

lemma f_injective : Function.Injective f := by
  intro a b hab
  have ha := f_f_eq f hf a
  have hb := f_f_eq f hf b
  rw [hab] at ha
  have : (a : ℕ) * ((f 1 : ℕ+) : ℕ) ^ 2 = (b : ℕ) * ((f 1 : ℕ+) : ℕ) ^ 2 := by
    exact_mod_cast ha.symm.trans hb
  exact PNat.eq (by nlinarith [(show (0 : ℕ) < ((f 1 : ℕ+) : ℕ) ^ 2 from by positivity)])

lemma f_sq_d (n : ℕ+) : f (n ^ 2 * f 1) = (f n) ^ 2 := by
  have h := hf 1 n
  simpa using h

lemma f_prod_eq (a b : ℕ+) : f a * f b = f (f 1 * a * b) := by
  have h_eq : f a ^ 2 * f b ^ 2 = f ((a * b * f 1) ^ 2 * f 1) := by
    convert hf ( f ( a ^ 2 * f 1 ) ) b |> Eq.symm using 1
    · simp +decide [ hf ]
    · simp_all +decide [ mul_pow, mul_assoc, mul_comm, mul_left_comm, f_f_eq ]
  simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ]
  rw [ ← PNat.coe_inj ] at * ; simp_all +decide [ ← mul_pow ]

lemma f_d_mul (n : ℕ+) : f 1 * f n = f (f 1 * n) := by
  have h := f_prod_eq f hf 1 n
  simpa using h

lemma f_mul_rel (a b : ℕ+) : f a * f b = f 1 * f (a * b) := by
  rw [f_prod_eq f hf a b, f_d_mul f hf (a * b), mul_assoc]

lemma f1_dvd (n : ℕ+) : (f 1 : ℕ) ∣ (f n : ℕ) := by
  have h_pow : ∀ k : ℕ, k > 0 → f (n ^ k) * (f 1) ^ (k - 1) = f n ^ k := by
    intro k hk_positive
    induction hk_positive <;> simp_all +decide [pow_succ, mul_comm, mul_left_comm]
    rename_i k hk ih
    rw [ ← ih ]
    rw [ ← mul_assoc, mul_comm ]
    rw [ f_mul_rel ]
    · rw [ show f 1 ^ k = f 1 * f 1 ^ ( k - 1 ) by rw [ ← pow_succ', Nat.sub_add_cancel hk ] ]
      ring
    · exact fun m n => by simpa only [ sq, mul_assoc ] using hf m n
  by_contra h_not_div
  obtain ⟨p, hp⟩ : ∃ p : ℕ, Nat.Prime p ∧ (Nat.factorization (f 1)) p > (Nat.factorization (f n)) p := by
    contrapose! h_not_div
    exact Nat.factorization_le_iff_dvd ( by positivity ) ( by positivity ) |>.1 fun p => by by_cases hp : Nat.Prime p <;> aesop
  obtain ⟨k, hk⟩ : ∃ k : ℕ, k > 0 ∧ (k - 1) * Nat.factorization (f 1) p > k * Nat.factorization (f n) p := by
    exact ⟨ ( f 1 |> PNat.val |> Nat.factorization ) p + 1, Nat.succ_pos _, by norm_num; nlinarith ⟩
  replace h_pow := congr_arg ( fun x : ℕ+ => x.val.factorization p ) ( h_pow k hk.1 )
  simp_all +decide [ Nat.factorization_mul ]
  lia

end AlgebraicLemmas

section LowerBound

variable (f : ℕ+ → ℕ+) (hf : ∀ m n : ℕ+, f (n ^ 2 * f m) = m * f n ^ 2)
include hf

noncomputable def gf (n : ℕ+) : ℕ := (f n : ℕ) / (f 1 : ℕ)

lemma gf_spec (n : ℕ+) : (f n : ℕ) = (f 1 : ℕ) * gf f n := by
  rw [gf, Nat.mul_div_cancel' (f1_dvd f hf n)]

lemma gf_pos (n : ℕ+) : 0 < gf f n := by
  rw [gf]
  exact Nat.div_pos (Nat.le_of_dvd (by positivity) (f1_dvd f hf n)) (by positivity)

omit hf in
lemma gf_one : gf f 1 = 1 := by
  rw [gf, Nat.div_self (by positivity)]

lemma gf_mul (a b : ℕ+) : gf f (a * b) = gf f a * gf f b := by
  unfold gf
  rw [ Nat.div_mul_div_comm ]
  · rw [ show ( f a : ℕ ) * f b = f 1 * f ( a * b ) by exact congr_arg PNat.val ( f_mul_rel f hf a b ) ]
    norm_num [ Nat.mul_div_mul_left ]
  · exact f1_dvd f hf a
  · exact f1_dvd f hf b

lemma gf_invol (n : ℕ+) : gf f ⟨gf f n, gf_pos f hf n⟩ = n := by
  have h_fg : f ⟨gf f n, gf_pos f hf n⟩ = n * f 1 := by
    have h_fg : f (f 1 * ⟨gf f n, gf_pos f hf n⟩) = n * f 1 * f 1 := by
      convert hf n 1 using 1
      · simp +decide [mul_comm]
        congr! 1
        exact PNat.eq ( by simp +decide [ gf_spec f hf n ] )
      · ring
    have := f_d_mul f hf ⟨gf f n, gf_pos f hf n⟩
    ( rw [ ← PNat.coe_inj ] at *; simp_all +decide [mul_comm, mul_left_comm] )
    nlinarith [ PNat.pos ( f 1 ) ]
  exact Nat.div_eq_of_eq_mul_left ( PNat.pos _ ) ( by erw [ h_fg ] ; norm_cast )

lemma gf_prime (p : ℕ+) (hp : Nat.Prime (p : ℕ)) : Nat.Prime (gf f p) := by
  refine Nat.prime_def_lt'.mpr ?_
  refine' ⟨ _, fun m hm₁ hm₂ h => _ ⟩
  · by_contra h_contra
    interval_cases _ : gf f p <;> have := gf_invol f hf p <;> simp_all +decide
    · exact absurd ‹gf f p = 0› ( ne_of_gt ( gf_pos f hf p ) )
    · exact absurd this ( by erw [ gf_one f ] ; exact ne_of_lt hp.one_lt )
  · have h_gmn : gf f ⟨m, by linarith⟩ * gf f ⟨gf f p / m, by
      exact Nat.div_pos ( Nat.le_of_dvd ( pos_of_gt hm₂ ) h ) ( pos_of_gt hm₁ )⟩ = p := by
      all_goals generalize_proofs at *
      convert gf_invol f hf p using 1
      convert gf_mul f hf ⟨ m, by linarith ⟩ ⟨ gf f p / m, by linarith ⟩ |> Eq.symm using 1
      exact congr_arg _ ( PNat.eq ( Eq.symm ( Nat.mul_div_cancel' h ) ) )
    generalize_proofs at *
    have h_g_one : gf f ⟨m, by linarith⟩ = 1 ∨ gf f ⟨gf f p / m, by positivity⟩ = 1 := by
      have := hp.isUnit_or_isUnit h_gmn.symm
      aesop
    generalize_proofs at *
    cases h_g_one <;> have := gf_invol f hf ⟨ m, by linarith ⟩ <;> simp_all +decide
    · linarith [ show gf f 1 = 1 from gf_one f ]
    · linarith!

lemma f_1998_eq : (f 1998 : ℕ) = (f 1 : ℕ) * gf f 2 * gf f 3 ^ 3 * gf f 37 := by
  rw [gf_spec f hf 1998]
  have h1998 : (1998 : ℕ+) = 2 * 3 * 3 * 3 * 37 := by rfl
  rw [h1998]
  simp [gf_mul f hf]
  ring

theorem f_1998_ge : (120 : ℕ) ≤ (f 1998 : ℕ) := by
  have h_min : ∀ p q r : ℕ, Nat.Prime p → Nat.Prime q → Nat.Prime r → p ≠ q ∧ q ≠ r ∧ p ≠ r → p * q^3 * r ≥ 120 := by
    intros p q r hp hq hr h_distinct
    by_cases hq2 : q = 2
    · rcases p with ( _ | _ | _ | _ | _ | p ) <;> rcases r with ( _ | _ | _ | _ | _ | r ) <;> simp_all +arith +decide
      grind
    · by_cases hq3 : q = 3
      · rcases p with ( _ | _ | _ | _ | p ) <;> rcases r with ( _ | _ | _ | _ | r ) <;> simp_all +arith +decide
        nlinarith
      · have hq_ge_5 : 5 ≤ q := by exact le_of_not_gt fun h => by interval_cases q <;> trivial
        have hq3_ge_125 : 125 ≤ q^3 := by exact Nat.pow_le_pow_left hq_ge_5 3
        nlinarith [ hp.two_le, hr.two_le, mul_pos hp.pos hr.pos ]
  have h_final : (gf f 2 : ℕ) * (gf f 3 : ℕ) ^ 3 * (gf f 37 : ℕ) ≥ 120 := by
    apply h_min
    · exact gf_prime f hf 2 (by decide)
    · exact gf_prime f hf 3 (by decide)
    · exact gf_prime f hf 37 (by decide)
    · refine' ⟨ _, _, _ ⟩ <;> intro h <;> have := gf_invol f hf 2 <;> have := gf_invol f hf 3 <;> have := gf_invol f hf 37 <;> simp_all +decide
  exact le_trans h_final ( by nlinarith [ f_1998_eq f hf, PNat.pos ( f 1 ) ] )

end LowerBound

section Construction

def primeSwap : ℕ → ℕ
  | 2 => 3 | 3 => 2 | 5 => 37 | 37 => 5 | n => n

def g (n : ℕ) : ℕ := (n.primeFactorsList.map primeSwap).prod

lemma primeSwap_invol (n : ℕ) : primeSwap (primeSwap n) = n := by
  by_cases h2 : n = 2 <;> by_cases h3 : n = 3 <;> by_cases h5 : n = 5 <;> by_cases h37 : n = 37
  all_goals (try subst_vars; try rfl)
  all_goals simp only [primeSwap, *]

lemma primeSwap_prime {p : ℕ} (hp : Nat.Prime p) : Nat.Prime (primeSwap p) := by
  by_cases h2 : p = 2 <;> by_cases h3 : p = 3 <;> by_cases h5 : p = 5 <;> by_cases h37 : p = 37
  all_goals (try subst_vars; try decide)
  all_goals rw [show primeSwap p = p from by simp only [primeSwap, *]]
  exact hp

lemma g_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) : g (a * b) = g a * g b := by
  simp only [g]
  have h := (Nat.perm_primeFactorsList_mul ha hb).map primeSwap
  rw [List.map_append] at h
  rw [h.prod_eq, List.prod_append]

lemma g_prime {p : ℕ} (hp : Nat.Prime p) : g p = primeSwap p := by
  simp [g, Nat.primeFactorsList_prime hp]

lemma g_ne_zero (n : ℕ) : g n ≠ 0 := by
  simp only [g]
  apply List.prod_ne_zero; rw [List.mem_map]; push Not
  intro p hp; exact (primeSwap_prime (Nat.prime_of_mem_primeFactorsList hp)).ne_zero

lemma g_pos (n : ℕ) : 0 < g n := Nat.pos_of_ne_zero (g_ne_zero n)

lemma g_invol {n : ℕ} (hn : n ≠ 0) : g (g n) = n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases hn1 : n = 1
    · subst hn1
      simp [g]
    obtain ⟨p, hp, m, rfl⟩ := Nat.exists_prime_and_dvd hn1
    have hm : m ≠ 0 := right_ne_zero_of_mul hn
    rw [g_mul hp.ne_zero hm,
        g_mul (g_ne_zero p) (g_ne_zero m),
        g_prime hp, g_prime (primeSwap_prime hp), primeSwap_invol]
    congr 1
    exact ih m (by nlinarith [hp.one_lt, Nat.pos_of_ne_zero hm]) hm

lemma g_func_eq {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) : g (n ^ 2 * g m) = m * g n ^ 2 := by
  rw [g_mul (pow_ne_zero 2 hn) (g_ne_zero m),
      show g (n ^ 2) = g n ^ 2 from by rw [sq, g_mul hn hn, sq],
      g_invol hm, mul_comm]

lemma g_1998 : g 1998 = 120 := by native_decide

def gPNat (n : ℕ+) : ℕ+ := ⟨g n.val, g_pos n.val⟩

lemma gPNat_func_eq (m n : ℕ+) : gPNat (n ^ 2 * gPNat m) = m * gPNat n ^ 2 := by
  apply PNat.eq
  show g ((n ^ 2 * gPNat m).val) = (m * gPNat n ^ 2).val
  rw [PNat.mul_coe, PNat.pow_coe, PNat.mul_coe, PNat.pow_coe]
  show g (n.val ^ 2 * (gPNat m).val) = m.val * (gPNat n).val ^ 2
  simp only [gPNat]
  exact g_func_eq m.ne_zero n.ne_zero

lemma gPNat_1998 : gPNat 1998 = 120 := by
  apply PNat.eq
  simp [gPNat, g_1998]

end Construction

theorem imo1998_p6_mem :
    (120 : ℕ+) ∈ {k : ℕ+ | ∃ f : ℕ+ → ℕ+, (∀ m n : ℕ+, f (n ^ 2 * f m) = m * f n ^ 2) ∧ f 1998 = k} :=
  ⟨gPNat, gPNat_func_eq, gPNat_1998⟩

theorem imo1998_p6_lb :
    ∀ k ∈ {k : ℕ+ | ∃ f : ℕ+ → ℕ+, (∀ m n : ℕ+, f (n ^ 2 * f m) = m * f n ^ 2) ∧ f 1998 = k}, (120 : ℕ+) ≤ k := by
  intro k ⟨f, hf_eq, hf_1998⟩
  rw [← hf_1998]
  show (120 : ℕ) ≤ (f 1998 : ℕ)
  exact f_1998_ge f hf_eq

snip end

determine answer : ℕ+ := 120

problem imo1998_p6 :
    IsLeast
      {k : ℕ+ | ∃ f : ℕ+ → ℕ+, (∀ m n : ℕ+, f (n ^ 2 * f m) = m * f n ^ 2) ∧ f 1998 = k}
      answer :=
  ⟨imo1998_p6_mem, imo1998_p6_lb⟩

end Imo1998P6
