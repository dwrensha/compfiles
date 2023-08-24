/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.MeanInequalities

/-!
# USA Mathematical Olympiad 1998, Problem 3

Let a₀,a₁,...,aₙ be real numbers from the interval (0,π/2) such that

  tan(a₀ - π/4) + tan(a₁ - π/4) + ... + tan(aₙ - π/4) ≥ n - 1.

Prove that

  tan(a₀)tan(a₁)...tan(aₙ) ≥ nⁿ⁺¹.

-/

namespace Usa1998Q3
open BigOperators


lemma lemma0 : Set.Icc (-Real.pi / 4) (Real.pi / 4) ⊆
               Set.Ioo (-(Real.pi / 2)) (Real.pi/2) := by
   intros a ha; exact ⟨by linarith[ha.1, Real.pi_pos],
                       by linarith[ha.2, Real.pi_pos]⟩

lemma lemma1 (x : ℝ) (hx : x ∈ Set.Ioo 0 (Real.pi / 2)) :
    Real.tan (x - Real.pi / 4) < 1 := by
  let y' x := Real.tan (x - Real.pi / 4)
  have h4 : Real.tan (Real.pi / 4) = y' (Real.pi / 2) := by
    dsimp
    have h5 : Real.pi / 2 - Real.pi / 4 = Real.pi / 4 := by field_simp; ring
    rw[h5]
  rw[← Real.tan_pi_div_four]
  rw[h4]
  let y1 x := x - Real.pi / 4
  have h5 : StrictMonoOn y1 (Set.Icc 0 (Real.pi / 2)) := by
    intros a _ b _ hab
    exact sub_lt_sub_right hab _

  have h6 : StrictMonoOn y' (Set.Icc 0 (Real.pi / 2)) := by
    apply StrictMonoOn.comp (g := Real.tan) (f := y1)
         (t := (Set.Icc (-Real.pi / 4) (Real.pi / 4)))
         (StrictMonoOn.mono Real.strictMonoOn_tan lemma0)
         h5
    · intro a ha
      obtain ⟨ha1, ha2⟩ := ha
      constructor
      · dsimp; linarith
      · dsimp; linarith

  apply h6
  · exact ⟨le_of_lt hx.1, le_of_lt hx.2⟩
  · constructor
    . exact le_of_lt Real.pi_div_two_pos
    . exact Eq.le rfl
  · exact hx.2

lemma lemma2' (n : ℕ) : Finset.erase (Finset.range (n + 1)) n = Finset.range n :=
by rw[←Nat.succ_eq_add_one, Finset.range_succ]; simp

lemma lemma2 (f : ℕ → ℝ) :
    ∏ i in Finset.range (n + 1), ∏ j in Finset.erase (Finset.range (n + 1)) i, f j =
    ∏ i in Finset.range (n + 1), (f i)^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : ∏ i in Finset.range (Nat.succ n + 1), f i ^ ↑(Nat.succ n) =
            (∏ i in Finset.range (n + 1), f i ^ ↑(Nat.succ n)) * f (n + 1) ^ ↑(Nat.succ n) :=
     by rw[Finset.prod_range_succ]
    rw[h1]; clear h1
    have h2 : ∏ i in Finset.range (n + 1), f i ^ ↑(Nat.succ n) =
              ∏ i in Finset.range (n + 1), (f i ^ ↑n * f i) := by
       congr; funext x
       norm_cast
       exact pow_succ' (f x) _
    rw[h2]; clear h2
    rw[Finset.prod_mul_distrib]

    rw[Finset.prod_range_succ]
    rw[lemma2']

    have h3 :
       (∏ x in Finset.range (n + 1),
          ∏ j in Finset.erase (Finset.range (Nat.succ n + 1)) x, f j) =
        ∏ x in Finset.range (n + 1),
          ((∏ j in Finset.erase (Finset.range (n + 1)) x, f j) * f (n + 1)) := by
      apply Finset.prod_congr rfl
      intros x hx
      have h7' : (n + 1) ∉ (Finset.erase (Finset.range (n + 1)) x) := by simp_all
      have h7 : Finset.erase (Finset.range (Nat.succ n + 1)) x =
          Finset.cons (n + 1) (Finset.erase (Finset.range (n + 1)) x) h7' := by
        ext y
        constructor
        · intro hy
          simp at hy
          simp
          obtain ⟨hy1, hy2⟩ := hy
          by_contra' H
          obtain ⟨H0, H1⟩ := H
          have HH := H1 hy1
          have H0' := H0.symm
          have HH' : n + 2 ≤ y := Nat.lt_of_le_of_ne HH H0'
          linarith
        · intro hy
          simp_all
          cases' hy with hy hy
          · rw[hy]
            constructor
            · exact Nat.ne_of_gt hx
            · exact Nat.lt.base (n + 1)
          · obtain ⟨hy1, hy2⟩ := hy
            use hy1
            exact Nat.lt_add_right y (Nat.succ n) 1 hy2
      rw[h7, Finset.prod_cons]
      ring
    rw[h3]

    have h4 :
        ∏ x in Finset.range (n + 1),
          ((∏ j in Finset.erase (Finset.range (n + 1)) x, f j) * f (n + 1)) =
         (∏ x in Finset.range (n + 1),
            ∏ j in Finset.erase (Finset.range (n + 1)) x, f j) * f (n + 1) ^ (n+1) := by
      rw[Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
      norm_cast
    rw[h4]

    rw[ih]
    have h6 : ((Nat.succ n):ℝ) = (↑n + 1) := by norm_cast
    rw[h6]
    ring

lemma lemma3 (y : ℝ) (f : ℕ → ℝ) :
  ∏ x in Finset.range (n + 1), (f x * y) =
   (∏ x in Finset.range (n + 1), f x) * (∏ _x in Finset.range (n + 1), y) := by
 induction n with
 | zero => simp
 | succ n ih =>
   rw[Finset.prod_range_succ, ih]
   have h1 :
      ((∏ x in Finset.range (n + 1), f x) * ∏ _x in Finset.range (n + 1), y) * (f (n + 1) * y) =
       (∏ x in Finset.range (n + 1), f x) * f (n + 1) * ((∏ _x in Finset.range (n + 1), y) * y) :=
     by ring
   rw [h1]
   rw[←Finset.prod_range_succ, ←Finset.prod_range_succ]

lemma lemma4 (f : ℕ → ℝ) (g : ℕ → ℝ) :
    ∏ x in Finset.range (n + 1), (f x / g x) =
     (∏ x in Finset.range (n + 1), f x) / (∏ x in Finset.range (n + 1), g x) := by
 induction n with
 | zero => simp
 | succ n ih =>
    rw[Finset.prod_range_succ, ih]
    clear ih
    have h1 : ((∏ x in Finset.range (n + 1), f x) / ∏ x in Finset.range (n + 1), g x) * (f (n + 1) / g (n + 1)) =
       ((∏ x in Finset.range (n + 1), f x) * f (n + 1)) / ((∏ x in Finset.range (n + 1), g x) * g (n + 1)) :=
      by ring
    rw[h1]
    rw[←Finset.prod_range_succ, ←Finset.prod_range_succ]

lemma lemma5 {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (h : a ≤ c / b) : b ≤ c / a := by
  have h1 : a * b ≤ c := Iff.mp (le_div_iff hb) h
  exact Iff.mpr (le_div_iff' ha) h1

theorem usa1998_q3
    (n : ℕ)
    (a : ℕ → ℝ)
    (ha : ∀ i ∈ Finset.range (n + 1), a i ∈ Set.Ioo 0 (Real.pi / 2))
    (hs : n - 1 ≤ ∑ i in Finset.range (n + 1), Real.tan (a i - (Real.pi / 4)))
    : Real.rpow n (n + 1) ≤ ∏ i in Finset.range (n + 1), Real.tan (a i) := by

  obtain h0 | h0 := eq_or_ne n 0
  · simp_all[h0]
    exact Real.tan_nonneg_of_nonneg_of_le_pi_div_two
            (le_of_lt ha.1)
            (le_of_lt ha.2)

  -- informal solution from artofproblemsolving.com
  --
  -- Let yᵢ = tan(aᵢ - π/4), where 0 ≤ i ≤ n.
  let y : ℕ → ℝ := λ i ↦ Real.tan (a i - Real.pi / 4)
  -- Then we have
  --  y₀ + y₁ + ... + yₙ ≥ n - 1
  have h1 : n - 1 ≤ ∑ i in Finset.range (n + 1), y i := hs

  --  1 + yᵢ ≥ ∑_{j ≠ i} (1 - yⱼ)
  have h2 : ∀ i ∈ Finset.range (n + 1),
      ∑ j in (Finset.range (n + 1)).erase i, (1 - y j) ≤ 1 + y i := by
    intros i hi
    rw[Finset.sum_erase_eq_sub hi]
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
               nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    linarith

  --  (1 + yᵢ)/n ≥ (1/n) ∑_{j ≠ i} (1 - yⱼ)
  have h3 : ∀ i ∈ Finset.range (n + 1),
      (1/(n:ℝ)) * ∑ j in (Finset.range (n + 1)).erase i, (1 - y j)
          ≤ (1 + y i)/n := by
    intros i hi
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    rw[div_mul_eq_mul_div, one_mul]
    exact div_le_div_of_le hn (h2 i hi)

  --
  -- Then, by AM-GM,
  -- (1/n) ∑_{j ≠ i} (1 - yⱼ) ≥ ∏_{j ≠ i} (1 - yⱼ)^{1/n}
  have h4 : ∀ i ∈ Finset.range (n + 1),
     ∏ j in (Finset.range (n + 1)).erase i, (1 - y j)^(1 / (n : ℝ)) ≤
     (1/(n:ℝ)) * ∑ j in (Finset.range (n + 1)).erase i, (1 - y j) := by
    intros i hi
    let w : ℕ → ℝ := fun i ↦ 1 / (n:ℝ)
    have hn : (n:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr h0
    have hw' : ∑ _j in (Finset.range (n + 1)).erase i, w i = 1 := by
       simp[Finset.card_erase_of_mem hi]; field_simp
    have hw : ∀ j ∈ (Finset.range (n + 1)).erase i, 0 ≤ w j := by
      intros j _hj
      simp only [one_div, inv_nonneg, Nat.cast_nonneg]
    have hz : ∀ j ∈ (Finset.range (n + 1)).erase i, 0 ≤ 1 - y j := by
      intros j hj
      rw[Finset.mem_erase] at hj
      exact sub_nonneg.mpr (le_of_lt (lemma1 (a j) (ha j hj.2)))

    have h5 := Real.geom_mean_le_arith_mean_weighted
              ((Finset.range (n + 1)).erase i)
              w (λ j ↦ 1 - y j)
              hw hw' hz
    rw[Finset.mul_sum]
    exact h5

  -- (1 + yᵢ)/n ≥ ∏_{j ≠ i} (1 - yⱼ)^{1/n}
  have h5 : ∀ i ∈ Finset.range (n + 1),
      ∏ j in Finset.erase (Finset.range (n + 1)) i, (1 - y j) ^ (1 / ↑n) ≤
      (1 + y i) / ↑n := fun i hi ↦ (h4 i hi).trans (h3 i hi)

  -- ∏ᵢ(1 + yᵢ)/n ≥ ∏ᵢ∏_{j ≠ i} (1 - yⱼ)^{1/n}
  -- ∏ᵢ(1 + yᵢ)/n ≥ ∏ᵢ(1 - yᵢ)
  -- ∏ᵢ(1 + yᵢ)/(1 - yᵢ) ≥ ∏ᵢn
  -- ∏ᵢ(1 + yᵢ)/(1-yᵢ) ≥ nⁿ⁺¹
  have h6 : (n:ℝ) ^ ((n:ℝ) + 1) ≤ ∏ j in Finset.range (n + 1), (1 + y j) / (1 - y j) := by
    have h20 : ∀ i ∈ Finset.range (n + 1),
        0 ≤ ∏ j in Finset.erase (Finset.range (n + 1)) i, (1 - y j) ^ (1 / ↑n) := by
      intros i _hi
      apply Finset.prod_nonneg
      intros ii hii
      rw[Finset.mem_erase] at hii
      have := sub_nonneg.mpr (le_of_lt (lemma1 (a ii) (ha ii hii.2)))
      have := Real.rpow_nonneg_of_nonneg this (1 / ↑n)
      exact this -- if I try to collapse this to the previous line, i get timeouts.
    have h21 := Finset.prod_le_prod h20 h5
    have h23 : ∏ i in Finset.range (n + 1),
                ∏ j in Finset.erase (Finset.range (n + 1)) i, (1 - y j) ^ (1 / ↑n)
                = ∏ i in Finset.range (n + 1), (1 - y i) := by
      rw[lemma2]
      apply Finset.prod_congr rfl
      intros x hx
      have h30 : 0 ≤ 1 - y x := sub_nonneg.mpr (le_of_lt (lemma1 (a x) (ha x hx)))
      rw[←Real.rpow_mul h30]
      have h31 : (1:ℝ) / n * n = n / n := by field_simp
      rw[h31]
      have h32' : (n:ℝ) ≠ 0 := by norm_cast
      have h32 : (n:ℝ) / n = 1 := by field_simp
      rw[h32, Real.rpow_one]
    rw[h23] at h21; clear h23
    have h24 : ∏ i in Finset.range (n + 1), (1 + y i) / ↑n =
                 (∏ i in Finset.range (n + 1), (1 + y i)) / (↑n)^(↑n + 1) := by
      have h41 : ∏ i in Finset.range (n + 1), (1 + y i) / ↑n =
                   ∏ i in Finset.range (n + 1), (1 + y i) * (1 / ↑n) := by
        apply Finset.prod_congr rfl
        intros x _hx
        field_simp
      rw[h41]; clear h41
      rw[lemma3]
      rw[Finset.prod_const, Finset.card_range]
      have h43 : HPow.hPow ((1:ℝ) / (n:ℝ)) (n + 1) = (1:ℝ) / (↑n ^ (n + 1)) := by
        rw[div_pow, one_pow]
        norm_cast
      rw[h43]; clear h43
      field_simp
    rw[h24] at h21; clear h24
    rw[lemma4]
    have h25 : 0 < (n:ℝ) ^ (↑n + 1) := by
      norm_cast
      exact Nat.pos_pow_of_pos (n + 1) (Nat.pos_of_ne_zero h0)
    have h26 : 0 < ∏ x in Finset.range (n + 1), (1 - y x) := by
      apply Finset.prod_pos
      intros x hx
      exact sub_pos.mpr (lemma1 (a x) (ha x hx))
    exact lemma5 h26 h25 h21

  -- by the addition formula for tangents,
  -- tan(aᵢ) = tan((aᵢ - π/4) + π/4) = (1 + tan(aᵢ - π/4))/(1 - tan(aᵢ-π/4))
  --     ... = (1 + yᵢ)/(1 - yᵢ)
  have h7 : ∀ i ∈ Finset.range (n + 1), Real.tan (a i) = (1 + y i) / (1 - y i) := by
    intros i hi
    have h8 : a i = a i - Real.pi / 4 + Real.pi / 4 := eq_add_of_sub_eq rfl
    rw[h8]
    have h10 : (∀ (k : ℤ), a i - Real.pi / 4 ≠ (2 * ↑k + 1) * Real.pi / 2) ∧
                ∀ (l : ℤ), Real.pi / 4 ≠ (2 * ↑l + 1) * Real.pi / 2 := by
      have ⟨ha1, ha2⟩ := ha i hi
      constructor
      · intros k hk
        field_simp at hk
        have hkk : ∃ kk : ℝ, ↑k = kk := ⟨↑k, rfl⟩
        have ⟨kk, hkk'⟩ := hkk
        rw[hkk'] at hk
        cases' lt_or_le k 0 with hk' hk'
        · have hk2 : k ≤ -1 := Iff.mp Int.lt_add_one_iff hk'
          have : kk ≤ -1 := by rw[← hkk']; norm_cast
          nlinarith[Real.pi_pos]
        · have : 0 ≤ kk := by rw[← hkk']; norm_cast
          nlinarith[Real.pi_pos]
      · intros k hk
        field_simp at hk
        have hkk : ∃ kk : ℝ, ↑k = kk := ⟨↑k, rfl⟩
        have ⟨kk, hkk'⟩ := hkk
        rw[hkk'] at hk
        obtain hk' | hk' | hk' := lt_trichotomy k 0
        · have hk2 : k ≤ -1 := Iff.mp Int.lt_add_one_iff hk'
          have : kk ≤ -1 := by rw[← hkk']; norm_cast
          nlinarith[Real.pi_pos]
        · have hk0 : kk = 0 := by rw[←hkk']; norm_cast
          rw[hk0] at hk
          norm_num at hk
          exact Real.pi_ne_zero hk
        · have hk2 : 1 ≤ k := hk'
          have : 1 ≤ kk := by rw[← hkk']; norm_cast
          nlinarith[Real.pi_pos]
    have h11 := Real.tan_add' h10
    have h12 : Real.tan (a i - Real.pi / 4) + 1 =
                 1 + Real.tan (a i - Real.pi / 4) := add_comm _ _

    rw[Real.tan_pi_div_four, mul_one, h12] at h11
    rw[h11]

  -- so ∏ᵢ(1 + yᵢ)/(1-yᵢ) = ∏ᵢtan(aᵢ) ≥ nⁿ⁺¹, as desired
  have h8 : ∏ i in Finset.range (n + 1), Real.tan (a i) =
              ∏ j in Finset.range (n + 1), (1 + y j) / (1 - y j) :=
     Finset.prod_congr rfl (fun x hx ↦ h7 x hx)

  rw[h8]
  exact h6
