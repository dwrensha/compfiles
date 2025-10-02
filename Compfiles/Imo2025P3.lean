/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reuven Peleg (Problem statement) , Shahar Blumentzvaig
-/

import Mathlib.Tactic
import Mathlib.Data.ENat.Basic
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.Multiplicity
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Bounds.Basic
import ProblemExtraction

problem_file {
  tags := [.NumberTheory]
}

/-!
# International Mathematical Olympiad 2025, Problem 3

Let N denote the set of positive integers.

A function f : N → N is said to be bonza if f(a) divides b ^ a − f(b) ^ f(a) for all positive integers a and b.

Determine the smallest real constant c such that f(n) ⩽ cn for all bonza functions f and all positive integers n.
-/
open Int

--sinp begin

lemma fermat_little_theorem: ∀p:ℕ+, (Nat.Prime (p:ℕ)) → (∀a:ℕ, (a^(p:ℕ)≡a [MOD p])) := by
  intro p hp a
  by_cases h1:(p:ℕ)∣a
  · rw [←Nat.modEq_zero_iff_dvd] at h1
    have h2: a ^ (p:ℕ) ≡ 0 ^ (p:ℕ) [MOD p] := by
      exact Nat.ModEq.pow (p:ℕ) h1
    simp at h2
    apply Nat.ModEq.symm at h1
    exact Nat.ModEq.trans h2 h1
  · 
    have h2 : (p:ℕ).Coprime a := by
      by_contra g
      rw [←Nat.Prime.dvd_iff_not_coprime hp] at g
      exact h1 g
    apply Nat.Coprime.symm at h2
    have h3 := Nat.ModEq.pow_totient h2
    rw [Nat.totient_prime hp] at h3
    have h4 : a≡a [MOD p] := Nat.ModEq.rfl
    have h5 := Nat.ModEq.mul h3 h4
    simp at h5
    exact h5

lemma fermat_little_theorem2: ∀p:ℕ+, (Nat.Prime (p:ℕ)) → (∀a:ℕ, ∀k:ℕ, (a^((p:ℕ)^k)≡a [MOD p])) := by
  intro p hp a k
  induction k with
  | zero => 
    simp
    rfl
  | succ d hd => 
    rw [Nat.pow_add,Nat.mul_comm,Nat.pow_mul]
    simp
    have g1 := fermat_little_theorem p hp a
    have g2 := Nat.ModEq.pow ((p:ℕ) ^ d) g1
    exact Nat.ModEq.trans g2 hd

lemma int_dvd_to_nat_dvd : ∀a:ℕ+, ∀ b:ℕ , (a:ℤ)∣(b:ℤ) → (a:ℕ)∣b := by
  intro a b h1
  obtain ⟨x,hx⟩ := h1
  use x.toNat
  have g : x = (x.toNat : ℤ) := by
    simp
    have g2 : ↑a * x ≥ 0 := by
      rw [←hx]
      simp
    simp at g2
    exact g2
  rw [g] at hx
  rw [←Nat.cast_mul] at hx
  rw [Nat.cast_inj] at hx
  exact hx

--sinp end

def Bonza (f : ℕ+ → ℕ+) : Prop :=
  ∀ a b : ℕ+,
    (f a : Int) ∣ ((b : Int) ^ (a: ℕ) - (f b : Int) ^ ((f a): ℕ))

def is_valid_c (c : ℝ) : Prop :=
  ∀ (f : ℕ+ → ℕ+), Bonza f → ∀ n, (f n : ℝ) ≤ c * (n : ℝ)

determine answer : ℝ := 4

problem imo2025_p3 :
  IsLeast {c: ℝ | is_valid_c c} answer := by
    unfold answer
    unfold IsLeast
    constructor
    · simp
      unfold is_valid_c
      intro f hf
      unfold Bonza at hf
      intro n

      have h1 : ∀ a:ℕ+, (f a : Int) ∣ (a^(a :ℕ)) := by
        intro a
        specialize hf a a
        have g1 : (f a : Int) ∣ (f a : Int) ^ (f a : ℕ) := by
          simp
        have g2 := dvd_add hf g1
        simp at g2
        exact g2

      by_cases h2 : ∀b:ℕ+, f b <= b
      · specialize h2 n
        have g2 : (f n : ℝ) ≤ (n : ℝ) := by
          simp
          exact h2
        have g3 : (n : ℝ) ≤ 4*(n : ℝ) := by
          simp
        exact le_trans g2 g3
      · 
        have h3 : ∀p:ℕ+, (Nat.Prime (p:ℕ)) → (∃ k ≤ ↑p, (f p) = p ^ (k:ℕ)) := by
          intro p hp
          specialize h1 p
          have g1 : (f p : ℕ) ∣ (p : ℕ)^(p:ℕ) := by
            have r1 := int_dvd_to_nat_dvd (f p) ((p:ℕ)^(p:ℕ))
            simp at r1
            apply r1 at h1
            exact h1
          rw[Nat.dvd_prime_pow hp] at g1
          obtain ⟨k,hk⟩ := g1
          use k
          constructor
          · exact hk.1
          · exact PNat.coe_inj.mp hk.2

        have h4 : ∀p:ℕ+, (Nat.Prime (p:ℕ)) → (f p = 1 ∨ p ∣ f p) := by
          intro p hp
          specialize h3 p hp
          obtain ⟨i,hi⟩ := h3
          induction i with
          | zero => 
            simp at hi
            exact Or.inl hi
          | succ d hd =>
            have hi2 := hi.2
            apply Or.inr
            rw [hi2]
            simp

        have h5 : ∃N:ℕ+, ∀p:ℕ+, (p>N ∧ Nat.Prime (p : ℕ)) → (f p = 1) := by
          push_neg at h2
          obtain ⟨b,hb⟩ := h2
          use (f b - b)
          intro p hp
          obtain ⟨hp1,hp2⟩ := hp
          specialize hf p b
          by_contra hnp
          specialize h4 p hp2
          rcases h4 with r1|r1
          · exact hnp r1
          · 
            have r2 : (p:ℤ) ∣ (f p : ℤ) := by
              obtain ⟨x,hx⟩ := r1
              use x
              rw [hx]
              simp
            
            have r3 := dvd_trans r2 hf

            have r4 := r3
            rw [←Nat.cast_pow,←Nat.cast_pow] at r4
            rw [←Nat.modEq_iff_dvd] at r4

            have r5 := fermat_little_theorem p hp2 (b:ℕ)

            have r6 := Nat.ModEq.trans r4 r5

            specialize h3 p hp2
            obtain ⟨k,hk⟩ := h3
            obtain ⟨hk1,hk2⟩ := hk
            rw [hk2] at r6
            simp at r6

            have r7 : (f b :ℕ) ^ (p:ℕ) ^ k ≡ (f b) [MOD ↑p] := by
              exact fermat_little_theorem2 p hp2 (↑(f b)) k
            rw [Nat.ModEq.comm] at r7
            have r8 := Nat.ModEq.trans r7 r6
            rw [Nat.modEq_iff_dvd] at r8
            have r9 : (p:ℤ) ∣ (f b : ℤ) - (b:ℤ) := by
              obtain ⟨x,hx⟩ := r8
              use -x
              simp
              rw [←hx]
              simp
            have g1 : (f b : ℤ) - (b:ℤ)≥0 := by
              simp
              exact Nat.le_of_lt hb
            have g2: (f b : ℤ) - (b:ℤ) < (p:ℤ) := by
              simp at hp1
              rw [←PNat.coe_lt_coe] at hp1
              have t : (b:ℕ) ≤ (f b :ℕ) := by
                linarith
              rw [←Nat.cast_sub t]
              simp
              have g2' := PNat.sub_coe (f b) b
              rw [if_pos hb] at g2'
              rw [g2'] at hp1
              exact hp1
            have g3 := Int.eq_zero_of_dvd_of_nonneg_of_lt g1 g2 r9
            have g4 : (f b : ℤ) = (b : ℤ) := by
              linarith
            simp at g4
            rw [g4] at hb
            simp at hb

        have h6 : ∀p:ℕ+, (Nat.Prime p) ∧ (p≠2) → f p = 1 := by
          intro p hp
          obtain ⟨hp1,hp2⟩ := hp

          have r1 : IsUnit ((2:ℕ) : ZMod p) := by
            rw [ZMod.isUnit_iff_coprime 2 (p:ℕ)]
            simp
            have hp3 : (p:ℕ)≠2 := by
              by_contra y1
              have y2 : 2=((2:ℕ+):ℕ) := by
                simp
              rw [y2] at y1
              rw [PNat.coe_inj] at y1
              exact hp2 y1
            exact Nat.Prime.odd_of_ne_two hp1 hp3
          
          have r2 := Nat.setOf_prime_and_eq_mod_infinite (a := (2 : ZMod p)) r1
          obtain ⟨x,hx⟩ := h5
          have r3 := Set.Infinite.exists_gt r2 x
          obtain ⟨q2,htq⟩ := r3
          obtain ⟨htq1,htq2⟩ := htq
          simp at htq1
          obtain ⟨htq1,htq3⟩ := htq1
          have r4 : 0<q2 := by
            exact Nat.zero_lt_of_lt htq2
          let q :ℕ+ := ⟨q2,r4⟩
          have hq1 : Nat.Prime q := by
            unfold q
            simp
            exact htq1
          have hq2 : x < q := by
            unfold q
            exact htq2
          have hq3 : (q:ZMod p)=2 := by
            unfold q
            simp
            exact htq3
          clear htq1 htq2 htq3 r1 r2

          specialize hx q

          have r5 : (q > x ∧ Nat.Prime (q:ℕ)) := by
            exact And.intro hq2 hq1
          apply hx at r5
          
          specialize hf p q
          specialize h4 p hp1
          rcases h4 with h4|h4
          · exact h4
          · exfalso
            have r6 : (p:ℤ) ∣ (f p : ℤ) := by
              apply Nat.cast_dvd_cast
              obtain ⟨x,hx⟩ := h4
              rw [hx]
              simp
            have r7 := Int.dvd_trans r6 hf
            rw [←Nat.cast_pow,←Nat.cast_pow] at r7
            rw [←Nat.modEq_iff_dvd] at r7
            rw [r5] at r7
            simp at r7
            have r8 := fermat_little_theorem p hp1 (q:ℕ)
            have r9 := Nat.ModEq.trans r7 r8
            have r10 : 2 ≡ ↑q [MOD ↑p] := by
              exact (ZMod.natCast_eq_natCast_iff 2 ↑q ↑p).mp (id (Eq.symm hq3))
            rw [Nat.ModEq.comm] at r10
            have r11 := Nat.ModEq.trans r9 r10
            rw [Nat.modEq_iff_dvd] at r11
            simp at r11
            apply int_dvd_to_nat_dvd p 1 at r11
            apply Nat.Prime.not_dvd_one hp1 at r11
            exact r11

        have h7 : ∀a:ℕ+, ∀p:ℕ+, (Nat.Prime p) ∧ (p∣f a) → p=2 := by
          intro a p hp
          obtain ⟨hp1,hp2⟩ := hp
          by_contra r1
          push_neg at r1
          specialize h6 p (And.intro hp1 r1)
          specialize hf a p
          rw [h6] at hf
          simp at hf
          have r2 : (p:ℤ) ∣ (f a :ℤ) := by
            apply Nat.cast_dvd_cast
            rw [PNat.dvd_iff] at hp2
            exact hp2
          have r3 := Int.dvd_trans r2 hf
          have r4 : (p:ℤ) ∣ (p:ℤ) ^ (a:ℕ) := by
            simp
          have r5 := Int.dvd_sub r4 r3
          simp at r5
          apply int_dvd_to_nat_dvd p 1 at r5
          exact Nat.Prime.not_dvd_one hp1 r5

        have h8 : ∀a:ℕ+, ∃k:ℕ, (f a:ℕ) = 2^k := by
          intro a
          specialize h7 a
          have s := Nat.factorization (f a)
          use (f a:ℕ).factorization 2

          have r1 : ∀ (p : ℕ), Nat.Prime p ∧ p ∣ (f a :ℕ) → p = 2 := by
            intro p hp
            obtain ⟨hp1,hp2⟩ := hp
            have hppos : p>0 := by
              exact Nat.zero_lt_of_ne_zero (Nat.Prime.ne_zero hp1)
            let q :ℕ+ := ⟨p,hppos⟩
            have hq1 : Nat.Prime (q:ℕ) := by
              unfold q
              simp
              exact hp1
            have hq2 : q ∣ f a := by
              unfold q
              exact PNat.dvd_iff.mpr hp2
            clear hp1 hp2
            specialize h7 q (And.intro hq1 hq2)
            unfold q at h7
            rw [←PNat.coe_inj] at h7
            simp at h7
            exact h7
          have r2 : (f a : ℕ).factorization.support ⊆ {2} := by
            intro q hq
            simp at hq
            specialize r1 q hq
            simp
            exact r1
          have r3 := Nat.factorization_prod_pow_eq_self (Nat.ne_zero_iff_zero_lt.2 (f a).2)
          symm at r3
          have r4 := Finsupp.prod_of_support_subset ((f a :ℕ).factorization) r2 (fun x1 x2 => x1 ^ x2) 
          simp at r4
          exact r4

        have h9 : f 3 = 1 := by
          specialize h4 3 (by decide)
          rcases h4 with h4|h4
          · exact h4
          · 
            specialize h7 3 3 (And.intro (by decide) h4)
            exfalso
            simp at h7

        have h10 : ∀a:ℕ+, (Even (a:ℕ)) → ((f a :ℕ).factorization 2 ≤ (a:ℕ).factorization 2 + 2) := by
          intro a ha
          specialize hf a 3
          rw [h9] at hf
          simp at hf
          have g1 : (f a:ℕ) ≠ 0 := by
            simp
          have g2 : (a:ℕ) ≠ 0 := by
            simp
          rw [←Nat.multiplicity_eq_factorization (by decide) g1]
          rw [←Nat.multiplicity_eq_factorization (by decide) g2]
          clear g1 g2
          have r1 : emultiplicity 2 (f a:ℕ) = multiplicity 2 (f a:ℕ) := by
            apply FiniteMultiplicity.emultiplicity_eq_multiplicity
            apply Nat.finiteMultiplicity_iff.mpr
            simp
          have r2 : emultiplicity 2 (a:ℕ) = multiplicity 2 (a:ℕ) := by
            apply FiniteMultiplicity.emultiplicity_eq_multiplicity
            apply Nat.finiteMultiplicity_iff.mpr
            simp
          have r3 : emultiplicity 2 (f a:ℕ) ≤ emultiplicity 2 (a:ℕ) + 2 := by
            have g1 : emultiplicity 2 (f a :ℕ) ≤ emultiplicity 2 (3 ^ (a:ℕ) - 1) := by
              have y1 : (f a :ℕ) ∣ 3 ^ (a:ℕ) - 1 := by
                have t : (f a : ℤ) ∣ ((3 ^ (a:ℕ) - 1 : ℕ):ℤ) := by
                  simp
                  exact hf
                exact int_dvd_to_nat_dvd (f a) (3 ^ (a:ℕ) - 1) t
              exact emultiplicity_le_emultiplicity_of_dvd_right y1
            
            have y1 : 2∣3-1 := by decide
            have y2 : ¬2∣3 := by decide
            have g2 := Nat.two_pow_sub_pow y1 y2 ha
            
            simp at g2
            clear y1 y2

            have g3 : emultiplicity 2 2 = 1 := by
              apply FiniteMultiplicity.emultiplicity_self
              rw [Nat.finiteMultiplicity_iff]
              simp
            have g4 : emultiplicity 2 4 = 2 := by
              have y1 : 4=2^2 := by decide
              rw [y1]
              rw [Nat.Prime.emultiplicity_pow_self (by decide)]
              simp
            rw [g3,g4] at g2
            have g5 : emultiplicity 2 (3 ^ (a:ℕ) - 1) = emultiplicity 2 (a:ℕ) + 2 := by
              have y1 : FiniteMultiplicity 2 (3 ^ (a:ℕ) - 1) := by
                apply Nat.finiteMultiplicity_iff.mpr
                simp
              have y2 : FiniteMultiplicity 2 (a:ℕ) := by
                apply Nat.finiteMultiplicity_iff.mpr
                simp
              rw [FiniteMultiplicity.emultiplicity_eq_multiplicity y1,FiniteMultiplicity.emultiplicity_eq_multiplicity y2] at g2
              rw [FiniteMultiplicity.emultiplicity_eq_multiplicity y1,FiniteMultiplicity.emultiplicity_eq_multiplicity y2]
              have y3 : 1 = ((1:ℕ):ENat) := by
                simp
              have y4 : 2 = ((2:ℕ):ENat) := by
                simp
              rw [y3,y4] at g2
              rw [←ENat.coe_add,←ENat.coe_add,←ENat.coe_add] at g2
              rw [ENat.coe_inj] at g2
              rw [y4]
              rw [←ENat.coe_add]
              rw [ENat.coe_inj]
              grind
            rw [g5] at g1
            exact g1
          rw [r1,r2] at r3
          exact ENat.coe_le_coe.mp r3
          

        have h11 : ∀ (a : ℕ+), Even (a:ℕ) → (f a:ℤ) ≤ 4*(a:ℤ) := by
          intro a ha
          specialize h10 a ha
          specialize h8 a
          obtain ⟨k,hk⟩ := h8
          rw [hk] at h10
          simp at h10
          rw [Nat.Prime.factorization_self (by decide)] at h10
          simp at h10
          rw [hk]
          simp
          have r1 : 2^k ≤ 2^((a:ℕ).factorization 2 + 2) := by
            have g1 : 2>0 := by decide
            apply Nat.pow_le_pow_right g1 at h10
            exact h10
          have r2 : 2 ^ (Nat.factorization (a:ℕ) 2) ∣ (a:ℕ) := Nat.ordProj_dvd (a:ℕ) 2
          have g2 : (a:ℕ)>0 := by
            simp
          have r3 := Nat.le_of_dvd g2 r2
          rw [Nat.pow_add] at r1
          simp at r1
          have r4 : (2 ^ (a:ℕ).factorization 2)*4 ≤ (a:ℕ)*4 := by
            simp
            exact r3
          have r5 := Nat.le_trans r1 r4
          grind

        have h12 : ∀ (a : ℕ+), Odd (a:ℕ) → f a = 1 := by
          intro a ha
          specialize h1 a
          specialize h8 a
          obtain ⟨k,hk⟩ := h8
          rw [hk] at h1
          by_contra y1
          push_neg at y1
          have g1 : k≠0 := by
            by_contra y2
            rw [y2] at hk
            simp at hk
            exact y1 hk
          have g2 : 2 ∣ (((2:ℕ)^k):ℤ) := Dvd.dvd.pow (by decide) g1
          simp at h1
          have g3 := Int.dvd_trans g2 h1
          have g4 : 2 ∣ (a:ℕ) ^ (a:ℕ) := by
            obtain ⟨x,hx⟩ := g3
            use x.toNat
            have y2 : x = ((x.toNat):ℤ) :=by
              grind
            have y3 : 2 = ((2:ℕ):ℤ) :=by
              simp
            rw [y2,y3] at hx
            rw [←Nat.cast_mul] at hx
            grind
          apply Nat.Prime.dvd_of_dvd_pow (by decide) at g4
          rw [←Nat.not_even_iff_odd] at ha
          rw [←even_iff_two_dvd] at g4
          exact ha g4

        have h13 : ∀ (a : ℕ+), Odd (a:ℕ) → (f a:ℝ) ≤4*(a:ℝ) := by
          intro a ha
          specialize h12 a ha
          rw [h12]
          simp
          have r1 : a≥1 := by
            simp
          have r2 : 4≤4*(a:ℝ) := by
            simp
            exact r1
          have r3 : (1:ℝ)≤(4:ℝ) := by
            simp
          exact le_trans r3 r2

        by_cases r : Even (n:ℕ)
        · 
          specialize h11 n r
          have g1 : ((f n : ℤ):ℝ)≤((4*n:ℤ):ℝ) := by
            rw [Int.cast_le]
            exact h11
          simp at g1
          exact g1
        · 
          rw [Nat.not_even_iff_odd] at r
          specialize h13 n r
          exact h13

    · 
      unfold lowerBounds
      simp
      intro c hc
      unfold is_valid_c at hc
      let f (n : ℕ+) : ℕ+ :=
        if n = 4 then 16
        else if Odd (n:ℕ) then 1
        else 2
      specialize hc f
      have h : Bonza f := by
        unfold Bonza
        intro a b
        by_cases r1: a = 4
        · 
          have g1 : f a = 16 := by
            grind
          by_cases t1: b = 4
          · 
            have g2 : f b = 16 := by
              grind
            rw [g1,g2,r1,t1]
            decide
          · by_cases t2: Odd (b:ℕ)
            · 
              have g2 : f b = 1 := by
                grind
              rw [g1,g2,r1]
              simp
              have y1 : Odd (b:ℤ) := by
                simp
                exact t2
              have y2 := Int.eight_dvd_sq_sub_one_of_odd y1
              have y3 : Even ((b:ℕ)^2+1) := by
                apply Odd.add_one
                apply Odd.pow
                exact t2
              obtain ⟨x,hx⟩ := y2
              obtain ⟨y,hy⟩ := y3
              use x*y
              symm
              calc
                16*((x:ℤ)*y) = (8*(x:ℤ))*(y+y) := by ring
                _ = ((b:ℤ)^2-1)*(y+y) := by rw [hx]
                _ = ((b:ℤ)^2-1)*((y:ℕ)+y:ℕ) := by grind
                _ = ((b:ℤ)^2-1)*((b:ℤ)^2+1) := by
                  rw [←hy]
                  simp
                _ = ((b:ℤ)^4-1) := by ring
            · 
              have g2 : f b = 2 := by
                grind
              rw [g1,g2,r1]
              simp
              rw [Nat.not_odd_iff_even] at t2
              obtain ⟨x,hx⟩ := t2
              have y1 : x+x=2*x := by
                exact Eq.symm (Nat.two_mul x)
              rw [y1] at hx
              rw [hx]
              simp
              have y2 : (2*(x:ℤ))^4 = 2^4*(x:ℤ)^4 := by
                grind
              rw [y2]
              grind
        · by_cases r2: Odd (a:ℕ)
          · 
            have g1 : f a = 1 := by
              grind
            rw [g1]
            simp
          · 
            have g1 : f a = 2 := by
              grind
            by_cases t1: b = 4
            · 
              have g2 : f b = 16 := by
                grind
              rw [g1,g2,t1]
              simp
              have y1 : (2:ℤ) ∣ 4^(a:ℕ) := by
                apply Dvd.dvd.pow
                · decide
                · simp
              have y2 : (2:ℤ)∣ 256 := by
                decide
              exact Int.dvd_sub y1 y2
            · by_cases t2: Odd (b:ℕ)
              · 
                have g2 : f b = 1 := by
                  grind
                rw [g1,g2]
                simp
                have y1 : Odd (b:ℤ) := by
                  simp
                  exact t2
                have y2 : Odd ((b:ℤ)^(a:ℕ)) := by
                  exact Odd.pow y1
                have y4 : Even ((b:ℤ)^(a:ℕ)-1) := by
                  apply even_sub_one.mpr
                  rw [not_even_iff_odd]
                  exact y2
                rw [even_iff_two_dvd] at y4
                exact y4

              · 
                have g2 : f b = 2 := by
                  grind
                rw [g1,g2]
                simp
                rw [Nat.not_odd_iff_even] at t2
                
                obtain ⟨x,hx⟩ := t2
                have y1 : x+x=2*x := by
                  exact Eq.symm (Nat.two_mul x)
                rw [y1] at hx
                rw [hx]
                simp
                have y2 : 2∣(2*(x:ℤ))^(a:ℕ) := by
                  apply Dvd.dvd.pow
                  · simp
                  · simp
                have y3 : (2:ℤ)∣4 := by
                  decide
                exact Int.dvd_sub y2 y3
      apply hc at h
      specialize h 4
      unfold f at h
      simp at h
      have y : (16:ℝ)=4*4 := by
        grind
      rw [y] at h
      simp at h
      exact h
