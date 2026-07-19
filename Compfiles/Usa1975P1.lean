/-
Copyright (c) 2026 pacmanboss256. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pacmanboss256, hillosanation
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file {
  tags := [.Algebra]
}

/-!
# USA Mathematical Olympiad 1975, Problem 1
a) Prove that
$[5x]+[5y]\ge [3x+y]+[3y+x]$,

where $x,y\ge 0$ and $[u]$ denotes the greatest integer $\le u$ (e.g., $[\sqrt{2}]=1$).

(b) Using (a) or otherwise, prove that
$\frac{(5m)!(5n)!}{m!n!(3m+n)!(3n+m)!}$

is integral for all positive integral $m$ and $n$.
-/

snip begin

-- from https://leanprover.zulipchat.com/#narrow/channel/217875-Is-there-code-for-X.3F/topic/Sylvester-Schur.3A.20.20p-adic.20valuation/near/525085669
lemma Nat.Prime.multiplicity_factorial {p : ℕ} (hp : Prime p) {n b : ℕ} (h : log p n < b) :
  multiplicity p n.factorial = ∑ i ∈ Finset.Ico 1 b, n / p ^ i := by
  have := Nat.Prime.emultiplicity_factorial hp h
  rw [FiniteMultiplicity.emultiplicity_eq_multiplicity <| finiteMultiplicity_of_emultiplicity_eq_natCast this] at this
  exact_mod_cast this

lemma Int.intCast_add_floor (x : ℝ) (a: ℤ) : ⌊a + x⌋ = ⌊x⌋ + a := by
  simp [add_comm]

lemma Int.div_eq_floor {a b : ℕ} : (a / b: ℕ) = ⌊(a : ℝ) / b⌋ := by
  rw [Int.floor_div_natCast, Int.floor_natCast]
  norm_cast

@[reducible]
noncomputable def trunCeil (x : ℝ) := ⌈x⌉ - 1

notation "[[" x "]]" => trunCeil x

lemma floor_le_trunCeil {a b : ℝ} (h : a < b) : ⌊a⌋ ≤ [[b]] := by
  simpa using Int.floor_lt_ceil_of_lt h

lemma cases (a b : Fin 5) : [[(3 * ↑↑a + ↑↑b + 4) / 5]] + [[(3 * ↑↑b + ↑↑a + 4) / 5]] ≤ ↑↑a + ↑↑b := by
  fin_cases a <;> fin_cases b <;> simp [trunCeil] <;> ring_nf <;> linarith

lemma specialized (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) : ⌊3*x + y⌋ + ⌊3*y + x⌋ ≤ ⌊5*x⌋ + ⌊5*y⌋ := by

  sorry

lemma h (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) : ⌊x⌋ + ⌊y⌋ + ⌊3*x + y⌋ + ⌊3*y + x⌋ ≤ ⌊5*x⌋ + ⌊5*y⌋ := by
  wlog h : ⌊x⌋ = 0 ∧ ⌊y⌋ = 0
  · have := this (Int.fract x) (Int.fract y) (by simp) (by simp) ⟨Int.floor_fract _, Int.floor_fract _⟩
    rw [← Int.floor_add_fract x, ← Int.floor_add_fract y]
    ring_nf
    conv => enter [1, 2, 1]; rw [add_add_add_comm', add_assoc]
    conv => enter [1, 1, 2, 1]; rw [add_add_add_comm', add_assoc]
    norm_cast
    simp [↓Int.intCast_add_floor]
    ring_nf at this ⊢
    simp_rw [add_le_add_iff_right]
    simpa using this
  · simp_rw [h.1, h.2, zero_add]
    have hx₁ : x < 1 := by simp_all
    have hy₁ : y < 1 := by simp_all
    let a : Fin 5 := ⟨⌊5*x⌋₊, by rw [← mul_one 5, Nat.floor_lt]; all_goals push_cast; linarith⟩
    let b : Fin 5 := ⟨⌊5*y⌋₊, by rw [← mul_one 5, Nat.floor_lt]; all_goals push_cast; linarith⟩
    have ha : (a : ℝ) = ⌊5*x⌋ := by
      norm_cast
      rw [Int.natCast_floor_eq_floor]
      linarith
    have hb : (b : ℝ) = ⌊5*y⌋ := by
      norm_cast
      rw [Int.natCast_floor_eq_floor]
      linarith
    have hx₂ : x < (a + 1) / 5 := by
      rw [lt_div_iff₀ (by linarith), mul_comm, ha]
      exact Int.lt_floor_add_one _
    have hy₂ : y < (b + 1) / 5 := by
      rw [lt_div_iff₀ (by linarith), mul_comm, hb]
      exact Int.lt_floor_add_one _
    calc
      ⌊3*x+y⌋ + ⌊3*y+x⌋
      _ ≤ [[(3*a+b+4)/5]] + _ := by
        rw [@Int.add_le_add_iff_right]
        exact floor_le_trunCeil (by linarith)
      _ ≤ _ + [[(3*b+a+4)/5]] := by
        rw [@Int.add_le_add_iff_left]
        exact floor_le_trunCeil (by linarith)
      _ ≤ a + b := cases a b
      _ ≤ _ := by norm_cast at ha hb; rw [ha, hb]

snip end

namespace Usa1975P1

problem usa1975_p1a (x y: ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) : ⌊3*x + y⌋ + ⌊3*y + x⌋ ≤ ⌊5*x⌋ + ⌊5*y⌋ := by
  apply le_trans ?_ <| h x y hx hy
  simp
  exact Int.add_nonneg (Int.floor_nonneg.mpr hx) (Int.floor_nonneg.mpr hy)

open scoped Nat

problem usa1975_p1b (m n : ℕ) : (m ! * n ! * (3*m+n) ! * (3*n+m) !) ∣ ((5*m)! * (5*n)!) := by
  rw [Nat.dvd_iff_prime_pow_dvd_dvd]
  intro p k hp h_dvd
  have h_p_ne_one := Nat.Prime.ne_one hp
  have h_p_prime : Prime p := Nat.prime_iff.mp hp
  rw [Nat.pow_dvd_iff_le_padicValNat h_p_ne_one <| by simp [Nat.factorial_ne_zero] ] at h_dvd ⊢

  refine h_dvd.trans ?_
  repeat' rw [padicValNat_def' h_p_ne_one (by simp [Nat.factorial_ne_zero])]
  have multiplicity_mul' {a b : ℕ} (h: a * b ≠ 0) := multiplicity_mul h_p_prime (FiniteMultiplicity.of_prime_left h_p_prime h)
  repeat' rw [multiplicity_mul' <| by simp [Nat.factorial_ne_zero] ] at ⊢

  let b := Finset.sup' {5 * n, 5 * m, 3 * n + m, 3 * m + n, n, m} (by simp) (Nat.log p ·) + 1
  repeat' rw [@Nat.Prime.multiplicity_factorial _ hp _ b <| Nat.lt_add_one_iff.mpr <| Finset.le_sup' _ (by simp)] at ⊢

  apply @Nat.cast_le ℤ _ _ _ _ _ _ _ |>.mp
  simp only [Nat.cast_add, Nat.cast_sum, ↓Int.div_eq_floor]

  simp_rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i hi => ?_
  have := h (m / p ^ i) (n / p ^ i) (div_nonneg ?_ ?_) (div_nonneg ?_ ?_) <;> simp
  field_simp at this ⊢
  convert this

end Usa1975P1
