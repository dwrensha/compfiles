/-
Copyright (c) 2023 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jia-Jun Ma
-/
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Order.Floor
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith.Frontend

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# International Mathematical Olympiad 1987, Problem 6
Let $n$ be an integer greater than or equal to 2. Prove that if $k^2 + k + n$ is prime for all integers $k$ such that $0 <= k <= \sqrt{n/3}$, then $k^2 + k + n$ is prime for all integers $k$ such that $0 <= k <= n - 2$.
-/

namespace Imo1987P6
open Nat

snip begin
lemma minFac_le_sq {n: ℕ} (hnezero : n≠ 0) (hn : minFac n ≠ n)
: (minFac n)^2 ≤  n := by
  match n with
  | 0 => contradiction
  | 1 => simp
  | n+2 =>
    obtain ⟨r,hr⟩ := Nat.minFac_dvd (n+2)
    match r with
    | 0 => omega
    | 1 => nth_rw 2 [hr] at hn; simp at hn
    | r+2 =>
      have hh : (r+2) ∣  (n+2) := ⟨minFac (n+2), (by nth_rw 1 [hr,mul_comm])⟩
      have hr' : minFac (n+2) ≤ (r+2) := Nat.minFac_le_of_dvd (by omega) hh
      calc
      _ =  (minFac (n+2)) * minFac (n+2) := by ring_nf
      _ ≤ minFac (n+2) * (r+2) := Nat.mul_le_mul_left _ hr'
      _ = _ := hr.symm

lemma prime_of_coprime' (n : ℕ) (h1 : 1 < n)
  (h2: ∀ m:ℕ, m^2  ≤  n →  m ≠ 0 → n.Coprime m) : Nat.Prime n :=  by
  rw [Nat.prime_def_minFac]
  by_contra H; push_neg at H
  replace H := H (by omega)
  let m := minFac n
  have nneone : n ≠ 1 := by omega
  have mpos := Nat.minFac_pos n
  replace h2 := h2 (m) (minFac_le_sq (by omega) H) (by omega)
  apply Nat.Prime.not_coprime_iff_dvd.2 ?_ h2
  use (minFac n)
  simp [Nat.minFac_prime nneone,Nat.minFac_dvd,m]


lemma dyadic {k b : ℕ} (h1 : 1 ≤ k) (h2 : k ≤ b) : ∃ i, b < 2^i * k ∧ 2^i *k ≤ 2* b := by
  have hbk :  b/k ≠ 0 := by
    apply (Nat.div_ne_zero_iff (a:=b) (b:=k)).2
    omega
  use Nat.log2 (b/k) + 1
  constructor
  · have h2bk: (b/k).log2 < (b/k).log2 + 1 := Nat.lt_succ_self _
    replace h2bk := (Nat.log2_lt hbk).1 h2bk
    replace h2bk := succ_le_of_lt h2bk
    calc
    _ < b/k * k + k := lt_div_mul_add (by linarith)
    _ = (b/k+1) *k := by ring
    _ ≤  2 ^((b/k).log2 +1) * k := Nat.mul_le_mul_right k h2bk
  · have h2 : 2 ^((b/k).log2 +1)  = 2 * 2^( (b/k).log2 ):=
      by rw [pow_succ _ _,mul_comm]
    rw [h2]
    have h3 : 2^((b/k).log2) ≤ b/k := Nat.log2_self_le hbk
    rw [mul_assoc]
    apply Nat.mul_le_mul_left 2
    calc
    _ ≤  (b/k) * k := Nat.mul_le_mul_right k h3
    _ ≤ b := by rw [mul_comm]; apply mul_div_le


lemma key_lemma  {m b: ℕ }
  (h: ∀ k, b < k → k ≤ 2*b → Coprime m k) :
   ∀ k, 1 < k →  k ≤ 2 * b → Coprime m k  := by
   intro k hk1 hk2
   by_cases hk0 : b < k
   · exact h k hk0 hk2
   · push_neg at hk0
     obtain ⟨i, hi1, hi2⟩  :=  dyadic (le_of_lt hk1) hk0
     have hc := h (2^i *k) hi1 hi2
     exact Nat.coprime_mul_iff_right.1 hc |>.2

lemma key_lemma'  {m b: ℕ } (h1 : 1 < m)
  (h: ∀ k,  b < k → k ≤ 2*b → Coprime m k) (h2 : m < (2*b+1)^2):
   Nat.Prime m   := by
    replace h := key_lemma h
    apply prime_of_coprime' m h1
    intro k hk1 hk2
    by_cases hk0 : k=1
    · simp [hk0]
    push_neg at hk0
    refine h k ?_ ?_
    · match k with
      | 0 => exfalso; exact hk2 rfl
      | 1 => exfalso; exact hk0 rfl
      | n+2 => linarith
    · replace h2 := lt_of_le_of_lt hk1 h2
      rw [pow_two,pow_two] at h2
      replace h2 := Nat.mul_self_lt_mul_self_iff.1 h2
      linarith


lemma dvd_lemma (a b c : ℕ ) (h : c≠ 0):
  a ≤ b → b ∣ c → c < 2*a → b =c := by
  intro h1 h2 h3
  obtain ⟨k,hk⟩ := h2
  match k with
  | 0 => simp at hk; exfalso; exact h hk
  | 1 => simp [hk]
  | k+2 =>
    have hh : 2 * a ≤  c  := by
      calc
      2 * a ≤ 2 * b := by linarith
      _ ≤ 2*b + k * b := by simp
      _ = b *(k+2) := by ring_nf
      _ = c := hk.symm
    linarith

lemma zero_of_le_sub_pos {a b:ℕ}  : b≠ 0 → a ≤ a-b → a = 0 := by
  intro h1 h2
  match a with
  | 0 => rfl
  | a +1 =>
    have : a+1-b < a+1 := by
      calc
      _ =  a - (b-1) := by
        rw [<-Nat.succ_pred h1,Nat.succ_eq_add_one,add_comm b.pred,Nat.sub_add_eq]
        norm_num
      _ ≤ a := by simp
      _ < _  := by linarith
    linarith

lemma sub_le_lemma {a b:ℕ} : b ≤ a → b≠0 → a-b < a := by
  intro h1 h2
  obtain ⟨c,hc⟩ := le_iff_exists_add.1 h1
  rw [hc,add_comm]; simp [Nat.zero_lt_of_ne_zero h2]


lemma Real.coe_lt_coe {a b :ℕ } : (a :ℝ ) < (b: ℝ) ↔ a < b := by
  simp [WithZero.coe_lt_coe]

lemma pos_sub_of_lt {a b : ℕ} : a < b → 0 < b-a := by
  intro h
  exact Nat.pos_iff_ne_zero.2 <| Nat.sub_ne_zero_of_lt h

snip end

problem imo_1987_p6
  (p : ℕ)
  (f : ℕ → ℕ)
  (h₀ : ∀ x, f x = x^2 + x + p)
  (h₁ : ∀ k : ℕ, k ≤ Nat.floor (Real.sqrt (p / 3)) → Nat.Prime (f k)) :
  ∀ i ≤ p - 2, Nat.Prime (f i) := by
  let r := Nat.floor (Real.sqrt (p/3))
  intro k
  apply Nat.case_strong_induction_on k
  · intro; exact h₁ 0 (Nat.zero_le _)
  intro k IH hk
  by_cases h : k+1 ≤ r
  · exact h₁ (k+1) h
  · push_neg at h
    let kk := k+1
    let s := kk - r
    let N := f kk
    have hksr : kk =  s + r := Nat.eq_add_of_sub_eq (le_of_lt h) (by rfl)

    /- Show that N < ... -/
    have hs : 1 ≤ s := by
      simp_rw [s,kk]
      exact pos_sub_of_lt h
    have ieq1 : s+2 < 4*s+1 := by linarith
    have ieq2 : s^2 ≤ s^2 *4 := by nlinarith
    have ieq3 : 3*r ≤ 6*r*s  := by nlinarith
    have ieq4 : p ≤ 3*r^2 + 6*r + 2 := by
      have ieq5: √ (p/3) < r+1 := Nat.lt_floor_add_one _
      replace ieq5 := Real.lt_sq_of_sqrt_lt ieq5 |> (div_lt_iff₀ (by linarith)).1
      replace ieq5: (p) < (3*r^2 + 6*r +3) := Real.coe_lt_coe.1 <| by
        have casteq: ((r:ℝ)+1)^2 * 3 = ((3*r^2+6*r+3:ℕ):ℝ) := by simp;ring_nf
        rw [<-casteq]
        exact ieq5
      linarith
    /-
    have hieqs1 : s ≤ p-r-2 := by
      calc
      _ = kk - r := rfl
      _ ≤ p - 2 - r := Nat.sub_le_sub_right () _
      _ = _ := Nat.sub_right_comm _ _ _
    -/
    have hN0 : N =  kk^2+kk+p := h₀ kk
    have hN1 : N < (2 * (s + r) +1)^2  := by
      calc
      _ = _:= hN0
      _ ≤  3*r^2 + 6*r + 2 + (r+s)*(r+s+1) := by
        nlinarith
      _ = 4*r^2 + 2* r*s + s^2 + 7*r+s+2 := by ring_nf
      _ < 4*r^2 +4*s^2 +8*r*s+4*r+4*s+1 := by nlinarith
      _ = _ := by ring
    rw [<-hksr] at hN1

    have hP : ∀ i , kk < i → i ≤ 2*(kk) → Coprime N i := by
      by_contra H
      push_neg at H
      obtain ⟨j, hj1,hj2,hj3⟩ := H
      have hj1' : s+r +1 ≤ j := by rw [<-hksr]; apply succ_le_of_lt hj1
      let  ss :=  j-(s+r+1)
      have hss0 : j =  ss + (s+r+1) := Nat.eq_add_of_sub_eq hj1' (by rfl)


      have hp: 2 ≤ p :=  Nat.lt_of_sub_ne_zero (by linarith: p-2 ≠ 0) |> le_of_lt

      have hss1 : ss ≤ k := by
        apply Nat.le_of_add_le_add_right (b :=s+r+1)
        rw [<-hss0,<-hksr]
        calc
        _ ≤ _ := hj2
        _ = _ := by omega
      replace hss1 : Nat.Prime (f ss) := IH ss hss1 (by linarith)
      have hfss: N = f ss + (2*kk - j+1) *j := by
        rw [hN0,h₀ ss]
        zify
        rw [Int.natCast_sub hj2,hss0,<-hksr]
        push_cast
        ring_nf
      rw [hfss,Nat.coprime_add_mul_right_left] at hj3
      have hss2 : f ss ∣  j:= Nat.Prime.dvd_iff_not_coprime hss1 |>.2 hj3
      have hfss1: p ≤ f ss := by rw [h₀ ss];linarith [sq_nonneg ss]
      have hp1 : p-2 < p := sub_le_lemma hp (by linarith)
      have hfss2: j < 2*p := by
        calc
        _ ≤ 2*kk := hj2
        _ ≤ 2*(p-2):= by omega
        _ < 2*p := by linarith [hp1]
      have hj : j≠ 0 := by linarith
      have hfss3:  f ss = j := by
        refine dvd_lemma _ _ _ hj hfss1 hss2  hfss2
      rw [h₀ ss,hss0,add_comm _ ss,add_assoc] at hfss3
      replace hfss3 := add_left_cancel hfss3
      have hc1 : p ≤ k + 2 := by
        calc
          p ≤ ss^2 + p := by linarith [pow_two_nonneg ss]
          _ = _ := hfss3
          _ = _ := by rw [<-hksr]
      have hc2: p ≤ p-1 := by
        calc
        _ ≤ _ := hc1
        _ = (k+1) + 1 := by ring_nf
        _ ≤ (p-2)+1 := by linarith
        _ = p-1 := by
          obtain ⟨cc,hcc⟩ := le_iff_exists_add.1 hp
          rw [hcc,add_comm 2 cc];norm_num
      have : p = 0 := zero_of_le_sub_pos (by simp) hc2
      linarith
    have hfk : 1 < f kk := by
      rw [h₀,hksr]
      calc
      _ < 1 + 1 := by decide
      _ ≤ s^2 + s  := by nlinarith [hs]
      _ ≤ s^2 + 2 * r *s + r^2 + s + r + p := by nlinarith
      _ = _ := by ring
    exact key_lemma' (hfk) hP hN1

end Imo1987P6
