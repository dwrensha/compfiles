/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Liao
-/

import Mathlib
import ProblemExtraction

problem_file { tags := [.NumberTheory] }

set_option maxHeartbeats 1000000

/-!
# USA Mathematical Olympiad 2025, Problem 5

Find all positive integers `k` such that for every positive integer `n`, the sum
`∑_{i=0}^{n} C(n, i)^k` is divisible by `n + 1`.

-/

namespace Usamo2025P5

determine solution_set : Set ℕ := {k | Even k}

snip begin

lemma p5_necessity (k : ℕ)
    (h : ∀ n : ℕ, 0 < n → (n + 1) ∣ ∑ i ∈ Finset.range (n + 1), (n.choose i) ^ k) :
    Even k := by
  by_contra h_odd;
  have h_mod3 : 2 ^ k % 3 = 2 := by
    rw [ ← Nat.mod_add_div k 2 ] ; norm_num [ Nat.pow_add, Nat.pow_mul, Nat.odd_iff.mp ( by simpa using h_odd ), Nat.mul_mod, Nat.pow_mod ] ;
  exact absurd ( h 2 ( by decide ) ) ( by norm_num [ Finset.sum_range_succ, Nat.choose ] ; omega )

lemma binom_pow_congr (k p e n n' i : ℕ) (hk : Even k) (hp : p.Prime) (he : 0 < e)
    (hdvd : p ^ e ∣ n + 1) (hn' : n + 1 = p * (n' + 1)) (hi : i ≤ n) :
    ((n.choose i : ZMod (p ^ e)) ^ k) = ((n'.choose (i / p) : ZMod (p ^ e)) ^ k) := by
  have h_lucas : ((Nat.choose n i) : ℤ) ≡ ((Nat.choose n' (i / p)) : ℤ) * (-1) ^ (i - i / p) [ZMOD p ^ e] := by
    have h_binom : (Nat.choose n i : ℤ) * (∏ j ∈ Finset.Icc 1 i, if p ∣ j then 1 else (j : ℤ)) ≡ (Nat.choose n' (i / p) : ℤ) * (∏ j ∈ Finset.Icc 1 i, if p ∣ j then 1 else (-j : ℤ)) [ZMOD p ^ e] := by
      have h_binom : (Nat.choose n i : ℤ) * (∏ j ∈ Finset.Icc 1 i, if p ∣ j then 1 else (j : ℤ)) = (∏ j ∈ Finset.Icc 1 i, if p ∣ j then 1 else (n + 1 - j : ℤ)) * (Nat.choose n' (i / p) : ℤ) := by
        have h_binom : (Nat.choose n i : ℤ) * (∏ j ∈ Finset.Icc 1 i, (j : ℤ)) = (∏ j ∈ Finset.Icc 1 i, (n + 1 - j : ℤ)) := by
          have h_binom : (Nat.choose n i : ℤ) * (Nat.factorial i : ℤ) = (∏ j ∈ Finset.range i, (n - j : ℤ)) := by
            rw_mod_cast [ mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose ];
            rw [ Nat.descFactorial_eq_prod_range ];
            rw [ Nat.cast_prod, Finset.prod_congr rfl fun x hx => Int.subNatNat_of_le ( by linarith [ Finset.mem_range.mp hx ] ) ];
          convert h_binom using 1;
          · erw [ ← Nat.cast_prod, Finset.prod_Ico_id_eq_factorial ];
          · erw [ Finset.prod_Ico_eq_prod_range ] ; norm_num [ add_comm, add_left_comm, sub_eq_add_neg ];
        have h_binom : (Nat.choose n' (i / p) : ℤ) * (∏ j ∈ Finset.Icc 1 (i / p), (p * j : ℤ)) = (∏ j ∈ Finset.Icc 1 i, if p ∣ j then (n + 1 - j : ℤ) else 1) := by
          have h_binom : (∏ j ∈ Finset.Icc 1 i, if p ∣ j then (n + 1 - j : ℤ) else 1) = (∏ j ∈ Finset.Icc 1 (i / p), (p * (n' + 1 - j) : ℤ)) := by
            have h_binom : Finset.filter (fun j => p ∣ j) (Finset.Icc 1 i) = Finset.image (fun j => p * j) (Finset.Icc 1 (i / p)) := by
              ext j; simp [Finset.mem_image];
              exact ⟨ fun h => ⟨ j / p, ⟨ Nat.div_pos ( Nat.le_of_dvd h.1.1 h.2 ) hp.pos, Nat.div_le_div_right h.1.2 ⟩, Nat.mul_div_cancel' h.2 ⟩, by rintro ⟨ a, ⟨ ha₁, ha₂ ⟩, rfl ⟩ ; exact ⟨ ⟨ by nlinarith [ hp.two_le ], by nlinarith [ Nat.div_mul_le_self i p ] ⟩, by simp +decide ⟩ ⟩;
            rw [ ← Finset.prod_filter, h_binom, Finset.prod_image ] <;> norm_num [ hp.ne_zero ];
            exact Finset.prod_congr rfl fun x hx => by linarith;
          have h_binom : (Nat.choose n' (i / p) : ℤ) * (∏ j ∈ Finset.Icc 1 (i / p), (j : ℤ)) = (∏ j ∈ Finset.Icc 1 (i / p), (n' + 1 - j : ℤ)) := by
            have h_binom : (Nat.choose n' (i / p) : ℤ) * (Nat.factorial (i / p) : ℤ) = (∏ j ∈ Finset.range (i / p), (n' - j : ℤ)) := by
              rw_mod_cast [ mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose ];
              rw [ Nat.descFactorial_eq_prod_range ];
              rw [ Nat.cast_prod, Finset.prod_congr rfl fun x hx => Int.subNatNat_of_le <| show x ≤ n' from _ ];
              exact fun x hx => by nlinarith [ Finset.mem_range.mp hx, Nat.div_mul_le_self i p ] ;
            convert h_binom using 1;
            · erw [ ← Nat.cast_prod, Finset.prod_Ico_id_eq_factorial ];
            · erw [ Finset.prod_Ico_eq_prod_range ] ; norm_num [ add_comm, sub_sub ];
          simp_all +decide [ Finset.prod_mul_distrib ];
          rw [ ← h_binom, mul_left_comm ];
        simp_all +decide [ Finset.prod_ite, Finset.filter_not ];
        simp_all +decide [ Finset.prod_mul_distrib, (Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc) ];
        simp_all +decide [ ← mul_assoc, ← Finset.prod_sdiff <| Finset.filter_subset ( fun x => p ∣ x ) <| Finset.Ioc 0 i ];
        have h_prod_filter : (∏ x ∈ Finset.Ioc 0 i with p ∣ x, (x : ℤ)) = (p ^ (i / p) * (∏ x ∈ Finset.Ioc 0 (i / p), (x : ℤ))) := by
          have h_prod_filter : Finset.filter (fun x => p ∣ x) (Finset.Ioc 0 i) = Finset.image (fun x => p * x) (Finset.Ioc 0 (i / p)) := by
            ext; simp [Finset.mem_image];
            exact ⟨ fun h => ⟨ ‹_› / p, ⟨ Nat.div_pos ( Nat.le_of_dvd h.1.1 h.2 ) hp.pos, Nat.div_le_div_right h.1.2 ⟩, Nat.mul_div_cancel' h.2 ⟩, by rintro ⟨ a, ⟨ ha₁, ha₂ ⟩, rfl ⟩ ; exact ⟨ ⟨ Nat.mul_pos hp.pos ha₁, by nlinarith [ Nat.div_mul_le_self i p ] ⟩, dvd_mul_right _ _ ⟩ ⟩;
          rw [ h_prod_filter, Finset.prod_image ] <;> norm_num [ Finset.prod_mul_distrib, hp.ne_zero ];
        simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ];
        exact mul_left_cancel₀ ( show ( p : ℤ ) ^ ( i / p ) * ( ∏ x ∈ Finset.Ioc 0 ( i / p ), ( x : ℤ ) ) ≠ 0 from mul_ne_zero ( pow_ne_zero _ ( Nat.cast_ne_zero.mpr hp.ne_zero ) ) ( Finset.prod_ne_zero_iff.mpr fun x hx => Nat.cast_ne_zero.mpr <| by linarith [ Finset.mem_Ioc.mp hx ] ) ) <| by linear_combination' ‹ ( p : ℤ ) ^ ( i / p ) * ( n.choose i * ( ( ∏ x ∈ Finset.Ioc 0 ( i / p ), ( x : ℤ ) ) * ∏ x ∈ Finset.Ioc 0 i \ Finset.filter ( Dvd.dvd p ) ( Finset.Ioc 0 i ), ( x : ℤ ) ) ) = ( ∏ x ∈ Finset.Ioc 0 i with p ∣ x, ( n + 1 - x : ℤ ) ) * ∏ x ∈ Finset.Ioc 0 i \ Finset.filter ( Dvd.dvd p ) ( Finset.Ioc 0 i ), ( n + 1 - x : ℤ ) › - h_binom * ∏ x ∈ Finset.Ioc 0 i \ Finset.filter ( Dvd.dvd p ) ( Finset.Ioc 0 i ), ( n + 1 - x : ℤ ) ;
      rw [ h_binom, mul_comm ];
      refine' Int.ModEq.mul_left _ _;
      exact Int.ModEq.prod fun x hx => by split_ifs <;> [ rfl; exact Int.modEq_iff_dvd.mpr ⟨ - ( ( n + 1 ) / p ^ e ), by linarith [ Int.ediv_mul_cancel ( show ( p ^ e : ℤ ) ∣ n + 1 from mod_cast hdvd ) ] ⟩ ] ;
    have h_coprime : Int.gcd ((∏ j ∈ Finset.Icc 1 i, if p ∣ j then 1 else (j : ℤ))) (p ^ e) = 1 := by
      refine' mod_cast Nat.Coprime.prod_left _;
      intro j hj; split_ifs <;> simp_all +decide [ Nat.Coprime, Nat.Coprime.pow_right ] ;
      exact Nat.Coprime.symm ( hp.coprime_iff_not_dvd.mpr ‹_› );
    have h_cancel : (Nat.choose n i : ℤ) ≡ (Nat.choose n' (i / p) : ℤ) * (-1) ^ (i - i / p) [ZMOD p ^ e] := by
      have h_prod : (∏ j ∈ Finset.Icc 1 i, if p ∣ j then 1 else (-j : ℤ)) = (-1) ^ (i - i / p) * (∏ j ∈ Finset.Icc 1 i, if p ∣ j then 1 else (j : ℤ)) := by
        rw [ Finset.prod_ite, Finset.prod_ite ];
        rw [ Finset.prod_congr rfl fun x hx => neg_eq_neg_one_mul _, Finset.prod_mul_distrib ] ; norm_num;
        rw [ show Finset.filter ( fun x => ¬p ∣ x ) ( Finset.Icc 1 i ) = Finset.Icc 1 i \ Finset.image ( fun x => p * x ) ( Finset.Icc 1 ( i / p ) ) from ?_, Finset.card_sdiff ] <;> norm_num;
        · rw [ show Finset.image ( fun x => p * x ) ( Finset.Icc 1 ( i / p ) ) ∩ Finset.Icc 1 i = Finset.image ( fun x => p * x ) ( Finset.Icc 1 ( i / p ) ) from ?_, Finset.card_image_of_injective _ fun x y hxy => mul_left_cancel₀ hp.ne_zero hxy ]
          · norm_num
          · exact Finset.inter_eq_left.mpr fun x hx => by obtain ⟨ y, hy, rfl ⟩ := Finset.mem_image.mp hx; exact Finset.mem_Icc.mpr ⟨ by nlinarith [ Finset.mem_Icc.mp hy, hp.two_le ], by nlinarith [ Finset.mem_Icc.mp hy, Nat.div_mul_le_self i p ] ⟩
        · ext; simp [Finset.mem_sdiff, Finset.mem_image];
          exact fun _ _ => ⟨ fun h x hx₁ hx₂ hx₃ => h <| hx₃ ▸ dvd_mul_right _ _, fun h => fun hx => h ( ‹_› / p ) ( Nat.div_pos ( Nat.le_of_dvd ( by linarith ) hx ) hp.pos ) ( Nat.div_le_div_right <| by linarith ) <| Nat.mul_div_cancel' hx ⟩
      rw [ Int.modEq_iff_dvd ] at *
      refine' Int.dvd_of_dvd_mul_left_of_gcd_one _ _
      · use ∏ j ∈ Finset.Icc 1 i, if p ∣ j then 1 else ( j : ℤ )
      · convert h_binom using 1 ; rw [ h_prod ] ; ring
      · exact Nat.Coprime.symm h_coprime
    convert h_cancel using 1;
  have h_lucas_k : ((Nat.choose n i) : ℤ) ^ k ≡ ((Nat.choose n' (i / p)) : ℤ) ^ k * (-1) ^ (k * (i - i / p)) [ZMOD p ^ e] := by
    convert h_lucas.pow k using 1 ; ring;
  simp_all +decide [ Int.ModEq, pow_mul ];
  erw [ ← ZMod.intCast_eq_intCast_iff' ] at * ; aesop

lemma p5_block_step (k p e n n' : ℕ) (hk : Even k) (hp : p.Prime) (he : 0 < e)
    (hdvd : p ^ e ∣ n + 1) (hn' : n + 1 = p * (n' + 1)) :
    (∑ i ∈ Finset.range (n + 1), (n.choose i) ^ k : ZMod (p ^ e))
      = (p : ZMod (p ^ e)) * ∑ i ∈ Finset.range (n' + 1), (n'.choose i) ^ k := by
  have h_sum_reindex : ∑ i ∈ Finset.range (p * (n' + 1)), ((n.choose i : ZMod (p ^ e)) ^ k) = ∑ i' ∈ Finset.range (n' + 1), ∑ r ∈ Finset.range p, ((n.choose (p * i' + r) : ZMod (p ^ e)) ^ k) := by
    induction' n' + 1 with n' ih <;> simp_all +decide [ Nat.mul_succ, Finset.sum_range_add ];
  have h_cong : ∀ i' ∈ Finset.range (n' + 1), ∀ r ∈ Finset.range p, ((n.choose (p * i' + r) : ZMod (p ^ e)) ^ k) = ((n'.choose i' : ZMod (p ^ e)) ^ k) := by
    intros i' hi' r hr
    have := binom_pow_congr k p e n n' (p * i' + r) hk hp he hdvd hn' (by
    nlinarith [ Finset.mem_range.mp hi', Finset.mem_range.mp hr ]);
    simp_all +decide [ Nat.add_div, hp.pos ];
    rw [ Nat.div_eq_of_lt hr, if_neg ( Nat.not_le_of_gt ( Nat.mod_lt _ hp.pos ) ) ] ; norm_num;
  simp_all +decide;
  rw [ Finset.mul_sum _ _ _ ]

lemma p5_prime_pow (k : ℕ) (hk : Even k) :
    ∀ m : ℕ, 0 < m → ∀ p e : ℕ, p.Prime → p ^ e ∣ m → ¬ p ^ (e + 1) ∣ m →
      p ^ e ∣ ∑ i ∈ Finset.range m, ((m - 1).choose i) ^ k := by
  intro m hm p e hp hpe hpe'; induction' m using Nat.strong_induction_on with m ih generalizing p e; rcases e with ( _ | e ) <;> simp_all +decide [ Nat.pow_succ' ] ;
  obtain ⟨m₁, rfl⟩ : ∃ m₁, m = p * m₁ := dvd_of_mul_right_dvd hpe;
  have h_block_step : (∑ i ∈ Finset.range (p * m₁), (Nat.choose (p * m₁ - 1) i) ^ k : ℤ) ≡ p * (∑ i ∈ Finset.range m₁, (Nat.choose (m₁ - 1) i) ^ k : ℤ) [ZMOD p ^ (e + 1)] := by
    have h_block_step : (∑ i ∈ Finset.range (p * m₁), (Nat.choose (p * m₁ - 1) i) ^ k : ZMod (p ^ (e + 1))) = (p : ZMod (p ^ (e + 1))) * (∑ i ∈ Finset.range m₁, (Nat.choose (m₁ - 1) i) ^ k : ZMod (p ^ (e + 1))) := by
      convert p5_block_step k p ( e + 1 ) ( p * m₁ - 1 ) ( m₁ - 1 ) hk hp ( Nat.succ_pos _ ) _ _ using 1 <;> norm_num [ Nat.sub_add_cancel ( show 1 ≤ p * m₁ from hm ), Nat.sub_add_cancel ( show 1 ≤ m₁ from Nat.pos_of_ne_zero ( by aesop_cat ) ) ];
      simpa only [ pow_succ' ] using hpe;
    erw [ ← ZMod.intCast_eq_intCast_iff ] ; aesop;
  have h_ind : p ^ e ∣ ∑ i ∈ Finset.range m₁, (Nat.choose (m₁ - 1) i) ^ k := by
    rcases p with ( _ | _ | p ) <;> simp_all +decide [ pow_succ', mul_dvd_mul_iff_left ];
  rw [ ← Int.natCast_dvd_natCast ] at *; simp_all +decide [ pow_succ' ] ;
  exact Int.dvd_of_emod_eq_zero ( h_block_step.symm ▸ Int.emod_eq_zero_of_dvd ( mul_dvd_mul_left _ h_ind ) )

lemma p5_sufficiency (k : ℕ) (hk : Even k) :
    ∀ n : ℕ, 0 < n → (n + 1) ∣ ∑ i ∈ Finset.range (n + 1), (n.choose i) ^ k := by
  intro n hn;
  suffices h_factorization : ∀ p : ℕ, Nat.Prime p → (Nat.factorization (n + 1)) p ≤ (Nat.factorization (∑ i ∈ Finset.range (n + 1), (n.choose i) ^ k)) p by
    exact Nat.factorization_le_iff_dvd ( by positivity ) ( by exact ne_of_gt <| Finset.sum_pos ( fun _ _ => pow_pos ( Nat.choose_pos <| by linarith [ Finset.mem_range.mp ‹_› ] ) _ ) <| by norm_num ) |>.1 fun p => by by_cases hp : Nat.Prime p <;> aesop;
  intro p hp
  have h_div : p ^ (Nat.factorization (n + 1) p) ∣ (∑ i ∈ Finset.range (n + 1), (n.choose i) ^ k) := by
    convert p5_prime_pow k hk ( n + 1 ) ( Nat.succ_pos _ ) p ( Nat.factorization ( n + 1 ) p ) hp ( Nat.ordProj_dvd _ _ ) ( Nat.pow_succ_factorization_not_dvd ( by positivity ) hp ) using 1
    rw [Nat.add_sub_cancel]
  rw [ ← Nat.factorization_le_iff_dvd ] at h_div <;> simp_all +decide [ Nat.factorization_eq_zero_iff ];
  exact ⟨ 0, Nat.zero_le _, by aesop ⟩

snip end

problem usamo2025_p5 (k : ℕ) (_hk : 0 < k) :
    (∀ n : ℕ, 0 < n → (n + 1) ∣ ∑ i ∈ Finset.range (n + 1), (n.choose i) ^ k)
      ↔ k ∈ solution_set := by
  constructor
  · intro h
    exact p5_necessity k h
  · intro h
    exact p5_sufficiency k h

end Usamo2025P5
