/-
Copyright (c) 2026 pacmanboss256. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pacmanboss256, Kimi K3
-/

module

public import Mathlib.Tactic
public import ProblemExtraction

@[expose] public section

problem_file {
  tags := [.Algebra]
}

/-!
# USA Mathematical Olympiad 2010, Problem 5
Let $q = \dfrac{3p-5}{2}$ where $p$ is an odd prime, and let

\[S_q = \frac{1}{2\cdot 3 \cdot 4} + \frac{1}{5\cdot 6 \cdot 7} + \cdots + \frac{1}{q\cdot (q+1) \cdot (q+2)}.\]

Prove that if $\dfrac{1}{p}-2S_q = \dfrac{m}{n}$ for integers $m$ and $n$, then $m-n$ is divisible by $p$.

-/

namespace Usa2010P5

open Finset

snip begin

/-- Summation of three consecutive terms in blocks of three:
the sum of `f (3i+2) + f (3i+3) + f (3i+4)` over `i ∈ range t`
equals the sum of `f j` over `j ∈ Icc 2 (3t+1)`. -/
lemma sum_range_triple (f : ℕ → ℚ) (t : ℕ) :
    ∑ i ∈ Finset.range t, (f (3*i+2) + f (3*i+3) + f (3*i+4)) =
    ∑ j ∈ Finset.Icc 2 (3*t+1), f j := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Finset.sum_range_succ, ih]
    simp_rw [← add_assoc]
    repeat rw [← sum_Icc_succ_top ?_ f]
    · congr 2
    all_goals lia

/-- A sum of reciprocals as a single fraction with the product
of all denominators as denominator. -/
lemma sum_one_div_eq_div_prod {s : Finset ℕ} {c : ℕ → ℚ} (hc : ∀ i ∈ s, c i ≠ 0) :
    ∑ i ∈ s, 1 / c i = (∑ i ∈ s, ∏ j ∈ s.erase i, c j) / ∏ i ∈ s, c i := by
  have h : (∏ j ∈ s, c j) * ∑ i ∈ s, 1 / c i = ∑ i ∈ s, ∏ j ∈ s.erase i, c j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [← Finset.mul_prod_erase s c hi, mul_right_comm, mul_one_div_cancel (hc i hi),
      one_mul]
  have hprod : ∏ i ∈ s, c i ≠ 0 := Finset.prod_ne_zero_iff.2 hc
  rw [eq_div_iff hprod, mul_comm (∑ i ∈ s, 1 / c i) (∏ i ∈ s, c i)]
  exact h

snip end

problem usa2010_p5 (p q : ℕ) (hpp : Nat.Prime p) (hpo : Odd p) (hq : q = (3*p-5)/2) :
    ∀ (m n : ℤ), n ≠ 0 →
      (1 : ℚ)/p - 2 * (∑ k ∈ (Finset.Icc 2 q).filter (fun k ↦ k % 3 = 2),
        (1 : ℚ)/(k*(k+1)*(k+2))) = (m : ℚ)/(n : ℚ) →
      (p : ℤ) ∣ (m - n) := by
  obtain ⟨t, ht⟩ := hpo
  subst ht
  have ht1 : 1 ≤ t := by
    have h2 := hpp.two_le
    lia
  have hq1 : q + 1 = 3 * t := by lia
  -- The indices `2, 5, 8, …, q` are exactly `3i+2` for `i ∈ range t`.
  have hgrid : (Finset.Icc 2 q).filter (fun k ↦ k % 3 = 2) =
      (Finset.range t).image (fun i ↦ 3 * i + 2) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨⟨h2k, hkq⟩, hkm⟩
      exact ⟨(k - 2) / 3, by lia, by lia⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨by lia, by lia⟩, by lia⟩
  have hinj : Set.InjOn (fun i ↦ 3 * i + 2) (Finset.range t) := by
    intro a _ b _ h
    have h' : 3 * a + 2 = 3 * b + 2 := h
    lia
  -- Partial fractions: `2/(k(k+1)(k+2)) = 1/k - 2/(k+1) + 1/(k+2)`,
  -- rewritten as `(1/k + 1/(k+1) + 1/(k+2)) - 1/(i+1)` for `k = 3i+2`.
  have key : ∀ i : ℕ, 2 * ((1:ℚ)/((3*i+2 : ℕ)*((3*i+2 : ℕ)+1)*((3*i+2 : ℕ)+2))) =
      ((1:ℚ)/((3*i+2 : ℕ)) + (1:ℚ)/((3*i+3 : ℕ)) + (1:ℚ)/((3*i+4 : ℕ))) -
        (1:ℚ)/((1+i : ℕ)) := by
    intro i
    have d1 : (3*(i:ℚ)+2) ≠ 0 := by positivity
    have d2 : (3*(i:ℚ)+2+1) ≠ 0 := by positivity
    have d3 : (3*(i:ℚ)+2+2) ≠ 0 := by positivity
    have d4 : (3*(i:ℚ)+3) ≠ 0 := by positivity
    have d5 : (3*(i:ℚ)+4) ≠ 0 := by positivity
    have d6 : ((i:ℚ)+1) ≠ 0 := by positivity
    push_cast
    field_simp
    ring
  have h2 : 2 * (∑ k ∈ (Finset.Icc 2 q).filter (fun k ↦ k % 3 = 2),
        (1 : ℚ)/(k*(k+1)*(k+2))) =
      (∑ i ∈ Finset.range t, ((1:ℚ)/((3*i+2 : ℕ)) + (1:ℚ)/((3*i+3 : ℕ)) +
        (1:ℚ)/((3*i+4 : ℕ)))) - ∑ i ∈ Finset.range t, (1:ℚ)/((1+i : ℕ)) := by
    rw [hgrid, Finset.sum_image hinj, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ ↦ key i)
  have h3 : (∑ i ∈ Finset.range t, ((1:ℚ)/((3*i+2 : ℕ)) + (1:ℚ)/((3*i+3 : ℕ)) +
        (1:ℚ)/((3*i+4 : ℕ)))) = ∑ j ∈ Finset.Icc 2 (3*t+1), (1:ℚ)/(j:ℚ) :=
    sum_range_triple (fun j ↦ (1:ℚ)/(j:ℚ)) t
  -- `H = 1 + B`: peel off the `j = 1` term of the harmonic sum.
  have h5 : (∑ j ∈ Finset.Icc 1 (3*t+1), (1:ℚ)/(j:ℚ)) =
      1 + ∑ j ∈ Finset.Icc 2 (3*t+1), (1:ℚ)/(j:ℚ) := by
    rw [← Finset.Ico_add_one_right_eq_Icc (a := 1) (b := 3*t+1),
      ← Finset.Ico_add_one_right_eq_Icc (a := 2) (b := 3*t+1),
      ← Finset.sum_Ico_consecutive _ (show (1:ℕ) ≤ 2 by lia)
        (show 2 ≤ 3*t+1+1 by lia),
      Nat.Ico_succ_singleton, Finset.sum_singleton]
    norm_num
  -- `H = R + M`: split the harmonic sum at `t`.
  have h6 : (∑ j ∈ Finset.Icc 1 (3*t+1), (1:ℚ)/(j:ℚ)) =
      (∑ i ∈ Finset.range t, (1:ℚ)/((1+i : ℕ))) +
        ∑ j ∈ Finset.Icc (t+1) (3*t+1), (1:ℚ)/(j:ℚ) := by
    rw [← Finset.Ico_add_one_right_eq_Icc (a := 1) (b := 3*t+1),
      ← Finset.Ico_add_one_right_eq_Icc (a := t+1) (b := 3*t+1),
      ← Finset.sum_Ico_consecutive _ (show (1:ℕ) ≤ t+1 by lia)
        (show t+1 ≤ 3*t+1+1 by lia)]
    congr 1
    rw [Finset.sum_Ico_eq_sum_range (fun j ↦ (1:ℚ)/(j:ℚ)) 1 (t+1),
      show t+1-1 = t by lia]
  -- Pairing: the middle harmonic sum, symmetrically around `2t+1`.
  have h7 : (∑ j ∈ Finset.Icc (t+1) (3*t+1), (1:ℚ)/(j:ℚ)) =
      (1:ℚ)/((2*t+1 : ℕ)) + ∑ i ∈ Finset.range t, ((1:ℚ)/((2*t+1 : ℕ)-(1+i)) +
        (1:ℚ)/((2*t+1 : ℕ)+(1+i))) := by
    rw [← Finset.Ico_add_one_right_eq_Icc (a := t+1) (b := 3*t+1),
      ← Finset.sum_Ico_consecutive _ (show t+1 ≤ 2*t+1 by lia)
        (show 2*t+1 ≤ 3*t+1+1 by lia),
      ← Finset.sum_Ico_consecutive _ (show 2*t+1 ≤ 2*t+1+1 by lia)
        (show 2*t+1+1 ≤ 3*t+1+1 by lia),
      Nat.Ico_succ_singleton, Finset.sum_singleton]
    rw [Finset.sum_Ico_eq_sum_range (fun j ↦ (1:ℚ)/(j:ℚ)) (t+1) (2*t+1),
      Finset.sum_Ico_eq_sum_range (fun j ↦ (1:ℚ)/(j:ℚ)) (2*t+1+1) (3*t+1+1),
      show 2*t+1-(t+1) = t by lia, show 3*t+1+1-(2*t+1+1) = t by lia]
    have hrefl : (∑ i ∈ Finset.range t, (1:ℚ)/((t+1+i : ℕ))) =
        ∑ i ∈ Finset.range t, (1:ℚ)/((2*t - i : ℕ)) := by
      have h1 : (∑ i ∈ Finset.range t, (1:ℚ)/((2*t - i : ℕ))) =
          ∑ i ∈ Finset.range t, (1:ℚ)/((t+1+(t-1-i) : ℕ)) := by
        refine Finset.sum_congr rfl (fun i hi ↦ ?_)
        rw [Finset.mem_range] at hi
        rw [show (2*t - i : ℕ) = t+1+(t-1-i) by lia]
      rw [h1]
      exact (Finset.sum_range_reflect (fun i ↦ (1:ℚ)/((t+1+i : ℕ))) t).symm
    have hpair : (∑ i ∈ Finset.range t, ((1:ℚ)/((2*t+1 : ℕ)-(1+i)) +
          (1:ℚ)/((2*t+1 : ℕ)+(1+i)))) =
        ∑ i ∈ Finset.range t, ((1:ℚ)/((2*t - i : ℕ)) + (1:ℚ)/((2*t+1+1+i : ℕ))) := by
      refine Finset.sum_congr rfl (fun i hi ↦ ?_)
      rw [Finset.mem_range] at hi
      have e1 : ((2*t - i : ℕ):ℚ) = ((2*t+1 : ℕ):ℚ) - ((1:ℚ) + (i:ℚ)) := by
        have h : (2*t - i : ℕ) = 2*t+1-(1+i) := by lia
        rw [h, Nat.cast_sub (show 1+i ≤ 2*t+1 by lia)]
        push_cast
        ring
      have e2 : ((2*t+1+1+i : ℕ):ℚ) = ((2*t+1 : ℕ):ℚ) + ((1:ℚ) + (i:ℚ)) := by
        push_cast
        ring
      rw [← e1, ← e2]
    rw [hrefl, hpair, Finset.sum_add_distrib]
    ring
  -- Each pair: `1/(p-i) + 1/(p+i) = 2p/(p²-i²)`.
  have h8 : ∀ i ∈ Finset.range t, (1:ℚ)/((2*t+1 : ℕ)-(1+i)) + (1:ℚ)/((2*t+1 : ℕ)+(1+i)) =
      (2 : ℚ) * ((2*t+1 : ℕ):ℚ) / (((2*t+1 : ℕ):ℚ)^2 - ((1+i : ℕ):ℚ)^2) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have h1 : ((1+i : ℕ):ℚ) < ((2*t+1 : ℕ):ℚ) := by
      exact_mod_cast (show (1:ℕ)+i < 2*t+1 by lia)
    have h2' : ((1+i : ℕ):ℚ) = (1:ℚ) + (i:ℚ) := by push_cast; ring
    rw [h2'] at h1
    have hnz1 : ((2*t+1 : ℕ):ℚ) - ((1:ℚ) + (i:ℚ)) ≠ 0 := ne_of_gt (sub_pos.mpr h1)
    have hnz2 : ((2*t+1 : ℕ):ℚ) + ((1:ℚ) + (i:ℚ)) ≠ 0 := ne_of_gt (by positivity)
    rw [div_add_div _ _ hnz1 hnz2]
    push_cast
    ring
  have h9 : (∑ i ∈ Finset.range t, ((1:ℚ)/((2*t+1 : ℕ)-(1+i)) +
        (1:ℚ)/((2*t+1 : ℕ)+(1+i)))) =
      2 * ((2*t+1 : ℕ):ℚ) * ∑ i ∈ Finset.range t,
        (1:ℚ)/(((2*t+1 : ℕ):ℚ)^2 - ((1+i : ℕ):ℚ)^2) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i hi ↦ ?_)
    rw [h8 i hi, mul_one_div]
  -- The main identity: `1/p - 2S_q = 1 - 2p · Σ 1/(p²-i²)`.
  have hr : (1:ℚ)/((2*t+1 : ℕ)) - 2 * (∑ k ∈ (Finset.Icc 2 q).filter (fun k ↦ k % 3 = 2),
        (1 : ℚ)/(k*(k+1)*(k+2))) =
      1 - 2 * ((2*t+1 : ℕ):ℚ) * ∑ i ∈ Finset.range t,
        (1:ℚ)/(((2*t+1 : ℕ):ℚ)^2 - ((1+i : ℕ):ℚ)^2) := by
    rw [h2, h3]
    have hB : (∑ j ∈ Finset.Icc 2 (3*t+1), (1:ℚ)/(j:ℚ)) =
        (∑ i ∈ Finset.range t, (1:ℚ)/((1+i : ℕ))) +
          (∑ j ∈ Finset.Icc (t+1) (3*t+1), (1:ℚ)/(j:ℚ)) - 1 := by
      linarith [h5, h6]
    rw [hB, h7, h9]
    ring
  -- Nonvanishing of each factor `p² - (1+i)²` in `ℚ`.
  have hcQ : ∀ i ∈ Finset.range t, ((2*t+1 : ℕ):ℚ)^2 - ((1+i : ℕ):ℚ)^2 ≠ 0 := by
    intro i hi
    rw [Finset.mem_range] at hi
    have h1i : (0:ℚ) < ((1+i : ℕ):ℚ) := by positivity
    have hpi : ((1+i : ℕ):ℚ) < ((2*t+1 : ℕ):ℚ) := by
      exact_mod_cast (show (1:ℕ)+i < 2*t+1 by lia)
    have hp0 : (0:ℚ) < ((2*t+1 : ℕ):ℚ) := by positivity
    have m1 := mul_lt_mul_of_pos_left hpi h1i
    have m2 := mul_lt_mul_of_pos_right hpi hp0
    have hsq : ((1+i : ℕ):ℚ)^2 < ((2*t+1 : ℕ):ℚ)^2 := by
      simp only [pow_two]
      exact lt_trans m1 m2
    exact ne_of_gt (sub_pos.mpr hsq)
  have hSigma0 := sum_one_div_eq_div_prod (s := Finset.range t)
    (c := fun i ↦ ((2*t+1 : ℕ):ℚ)^2 - ((1+i : ℕ):ℚ)^2) hcQ
  set V : ℤ := ∏ i ∈ Finset.range t, (((2*t+1 : ℕ):ℤ)^2 - ((1+i : ℕ):ℤ)^2) with hV_def
  set U : ℤ := ∑ i ∈ Finset.range t, ∏ j ∈ (Finset.range t).erase i,
    (((2*t+1 : ℕ):ℤ)^2 - ((1+j : ℕ):ℤ)^2) with hU_def
  have hSigma : ∑ i ∈ Finset.range t, (1:ℚ)/(((2*t+1 : ℕ):ℚ)^2 - ((1+i : ℕ):ℚ)^2) =
      (U : ℚ)/(V : ℚ) := by
    have h1 : ((U : ℤ) : ℚ) = ∑ i ∈ Finset.range t, ∏ j ∈ (Finset.range t).erase i,
        (((2*t+1 : ℕ):ℚ)^2 - ((1+j : ℕ):ℚ)^2) := by
      rw [hU_def]
      push_cast
      ring_nf
    have h2' : ((V : ℤ) : ℚ) = ∏ i ∈ Finset.range t,
        (((2*t+1 : ℕ):ℚ)^2 - ((1+i : ℕ):ℚ)^2) := by
      rw [hV_def]
      push_cast
      ring_nf
    rw [h1, h2']
    exact hSigma0
  -- Each factor is a positive integer, so `V > 0`.
  have hcpos : ∀ i ∈ Finset.range t, (0:ℤ) < ((2*t+1 : ℕ):ℤ)^2 - ((1+i : ℕ):ℤ)^2 := by
    intro i hi
    rw [Finset.mem_range] at hi
    have h1i : (0:ℤ) < ((1+i : ℕ):ℤ) := by exact_mod_cast (show 0 < 1+i by lia)
    have hpi : ((1+i : ℕ):ℤ) < ((2*t+1 : ℕ):ℤ) := by
      exact_mod_cast (show (1:ℕ)+i < 2*t+1 by lia)
    have hp0 : (0:ℤ) < ((2*t+1 : ℕ):ℤ) := by exact_mod_cast (show 0 < 2*t+1 by lia)
    have m1 := mul_lt_mul_of_pos_left hpi h1i
    have m2 := mul_lt_mul_of_pos_right hpi hp0
    have hsq : ((1+i : ℕ):ℤ)^2 < ((2*t+1 : ℕ):ℤ)^2 := by
      simp only [pow_two]
      exact lt_trans m1 m2
    exact sub_pos.mpr hsq
  have hVpos : 0 < V := by
    rw [hV_def]
    exact Finset.prod_pos hcpos
  have hV0Q : ((V : ℤ) : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hVpos)
  -- Hence `1/p - 2S_q = (V - 2pU)/V` with `V - 2pU ≡ V (mod p)`.
  have haform : (1:ℚ)/((2*t+1 : ℕ)) - 2 * (∑ k ∈ (Finset.Icc 2 q).filter (fun k ↦ k % 3 = 2),
        (1 : ℚ)/(k*(k+1)*(k+2))) =
      (((V - 2*((2*t+1 : ℕ):ℤ)*U : ℤ)) : ℚ)/((V : ℤ):ℚ) := by
    rw [hr, hSigma, eq_div_iff hV0Q]
    push_cast
    field_simp
  have hpZ : Prime ((2*t+1 : ℕ):ℤ) := Nat.prime_iff_prime_int.mp hpp
  -- `p ∤ V`: no factor `p² - (1+i)²` is divisible by `p`.
  have hpV : ¬ ((2*t+1 : ℕ):ℤ) ∣ V := by
    rw [hV_def]
    apply hpZ.not_dvd_finsetProd
    intro i hi hdiv
    rw [Finset.mem_range] at hi
    have hP2 : ((2*t+1 : ℕ):ℤ) ∣ ((2*t+1 : ℕ):ℤ)^2 := ⟨_, by ring⟩
    have hi2 : ((2*t+1 : ℕ):ℤ) ∣ ((1+i : ℕ):ℤ)^2 := by
      have hsub := dvd_sub hP2 hdiv
      rwa [Int.sub_sub_self] at hsub
    have hiP : ((2*t+1 : ℕ):ℤ) ∣ ((1+i : ℕ):ℤ) := hpZ.dvd_of_dvd_pow hi2
    have hPdvdN : (2*t+1) ∣ (1+i) := by exact_mod_cast hiP
    have hle : (2*t+1) ≤ (1+i) := Nat.le_of_dvd (by lia) hPdvdN
    lia
  -- Transfer to an arbitrary representation `m/n`.
  intro m n hn hmn
  rw [haform] at hmn
  have hn0 : (n:ℚ) ≠ 0 := by exact_mod_cast hn
  rw [div_eq_div_iff hV0Q hn0] at hmn
  have hmnZ : (V - 2*((2*t+1 : ℕ):ℤ)*U) * n = m * V := by exact_mod_cast hmn
  have hpaV : ((2*t+1 : ℕ):ℤ) ∣ (V - 2*((2*t+1 : ℕ):ℤ)*U) - V := ⟨-2*U, by ring⟩
  have key2 : n * ((V - 2*((2*t+1 : ℕ):ℤ)*U) - V) = (m - n) * V := by
    linear_combination hmnZ
  have hdvd : ((2*t+1 : ℕ):ℤ) ∣ (m - n) * V := by
    rw [← key2]
    exact dvd_mul_of_dvd_right hpaV n
  rcases hpZ.dvd_mul.mp hdvd with h | h
  · exact h
  · exact absurd h hpV

end Usa2010P5
