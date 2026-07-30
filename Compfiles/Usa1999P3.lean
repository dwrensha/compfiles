/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.RingTheory.SimpleRing.Principal
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.NumberTheory] }

/-!
# USA Mathematical Olympiad 1999, Problem 3

Let p > 2 be a prime and let a, b, c, d be integers not divisible by p, such that

    {ra/p} + {rb/p} + {rc/p} + {rd/p} = 2

for any integer r not divisible by p. (Here, {t} = t − ⌊t⌋ is the fractional part.)
Prove that at least two of the numbers a + b, a + c, a + d, b + c, b + d, c + d
are divisible by p.
-/

namespace Usa1999P3

open Finset

snip begin

/-!
## Proof sketch

We follow the classical root-of-unity filter solution (Michael J. Doré's write-up
on Kalva).

Let `ζ = exp (2πi / p)` and let `χ : ZMod p → ℂ` be the additive character
`χ j = ζ ^ j.val`. The hypothesis says that for every nonzero `n : ZMod p` the
residues `(n * a).val + (n * b).val + (n * c).val + (n * d).val` sum to `2p`.
Weighting by `χ (-(m * n))` and summing over all `n` gives, for every nonzero
`m`, the identity `∑_{x ∈ {a,b,c,d}} Sw (-(m * x⁻¹)) = -2p`, where
`Sw j = ∑ k, k.val * χ (j * k)` satisfies `(χ j - 1) * Sw j = p`. Hence
`∑ 1 / (χ (-(m * x⁻¹)) - 1) = -2`. Clearing denominators yields the symmetric
relation `2 + e₃ = e₁ + 2 e₄` in the four numbers `χ (-(m * xᵢ⁻¹))`; summing it
over `m : ZMod p` forces `a⁻¹ + b⁻¹ + c⁻¹ + d⁻¹ = 0` in `ZMod p`. The relation
then reads `∑ χ (m * xᵢ⁻¹) = ∑ χ (-(m * xᵢ⁻¹))`; multiplying by `χ (-(m * a⁻¹))`
and summing over `m` shows that one of `a⁻¹ + b⁻¹`, `a⁻¹ + c⁻¹`, `a⁻¹ + d⁻¹`
vanishes, and the complementary pair vanishes too because the total sum is zero.
Taking inverses once more yields the two required divisibilities.
-/

noncomputable section

/-- The primitive `p`-th root of unity used throughout the proof. -/
def rt (p : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / p)

/-- The additive character `ZMod p → ℂ` given by `j ↦ ζ ^ j.val`. -/
def chi (p : ℕ) (j : ZMod p) : ℂ := rt p ^ j.val

/-- The weighted character sum `∑ k, k.val * χ (j * k)`. -/
def Sw (p : ℕ) [NeZero p] (j : ZMod p) : ℂ := ∑ k : ZMod p, (k.val : ℂ) * chi p (j * k)

lemma isPrimitiveRoot_rt {p : ℕ} (hp : p.Prime) : IsPrimitiveRoot (rt p) p := by
  unfold rt
  exact Complex.isPrimitiveRoot_exp p hp.pos.ne'

lemma chi_zero (p : ℕ) : chi p (0 : ZMod p) = 1 := by
  simp [chi, ZMod.val_zero]

lemma chi_add {p : ℕ} (hp : p.Prime) (j k : ZMod p) :
    chi p (j + k) = chi p j * chi p k := by
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  have hpow : rt p ^ p = 1 := (isPrimitiveRoot_rt hp).pow_eq_one
  have hlt : j.val + k.val < 2 * p := by
    have h1 := j.val_lt
    have h2 := k.val_lt
    omega
  show rt p ^ (j + k).val = rt p ^ j.val * rt p ^ k.val
  rw [ZMod.val_add]
  rcases lt_or_ge (j.val + k.val) p with h | h
  · rw [Nat.mod_eq_of_lt h, pow_add]
  · have hmod : (j.val + k.val) % p = j.val + k.val - p := by
      have h1 : j.val + k.val = j.val + k.val - p + p := by omega
      conv_lhs => rw [h1]
      rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : j.val + k.val - p < p)]
    rw [hmod]
    have h2 : rt p ^ (j.val + k.val - p) * rt p ^ p = rt p ^ j.val * rt p ^ k.val := by
      rw [← pow_add, Nat.sub_add_cancel h, pow_add]
    rw [hpow, mul_one] at h2
    exact h2

lemma chi_eq_one_iff {p : ℕ} (hp : p.Prime) (j : ZMod p) : chi p j = 1 ↔ j = 0 := by
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  have hζ := isPrimitiveRoot_rt hp
  constructor
  · intro h
    have hdvd : p ∣ j.val := (hζ.pow_eq_one_iff_dvd j.val).mp h
    have hz : j.val = 0 := Nat.eq_zero_of_dvd_of_lt hdvd j.val_lt
    have hj0 : (j.val : ZMod p) = 0 := by rw [hz, Nat.cast_zero]
    rwa [ZMod.natCast_zmod_val] at hj0
  · rintro rfl
    exact chi_zero p

/-- Sums over `ZMod p` of a function of the residue can be written as sums over
`Finset.range p`. -/
lemma sum_zmod_val {p : ℕ} [NeZero p] (f : ℕ → ℂ) :
    ∑ j : ZMod p, f (j.val) = ∑ i ∈ Finset.range p, f i := by
  apply Finset.sum_bij (i := fun j _ => j.val)
  · intro j _
    exact Finset.mem_range.mpr j.val_lt
  · intro j _ j' _ hjj'
    have h1 : (j.val : ZMod p) = j := ZMod.natCast_zmod_val j
    have h2 : (j'.val : ZMod p) = j' := ZMod.natCast_zmod_val j'
    rw [← h1, ← h2, hjj']
  · intro k hk
    have hk2 : k < p := Finset.mem_range.mp hk
    exact ⟨(k : ZMod p), Finset.mem_univ _, ZMod.val_natCast_of_lt hk2⟩
  · intro j _
    rfl

lemma sum_chi_self {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : 2 < p) :
    ∑ j : ZMod p, chi p j = 0 := by
  have hζ := isPrimitiveRoot_rt hp
  show ∑ j : ZMod p, (fun k : ℕ => rt p ^ k) j.val = 0
  rw [sum_zmod_val]
  exact hζ.geom_sum_eq_zero (by omega)

lemma sum_chi {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : 2 < p) (c : ZMod p) :
    ∑ m : ZMod p, chi p (c * m) = if c = 0 then (p : ℂ) else 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_cases hc : c = 0
  · subst hc
    rw [if_pos rfl]
    have h1 : (∑ m : ZMod p, chi p ((0 : ZMod p) * m)) = ∑ _m : ZMod p, (1 : ℂ) := by
      apply Finset.sum_congr rfl
      intro m _
      rw [zero_mul]
      exact chi_zero p
    rw [h1, Finset.sum_const, Finset.card_univ, ZMod.card p, nsmul_eq_mul, mul_one]
  · rw [if_neg hc]
    have h2 : (∑ m : ZMod p, chi p (c * m)) = ∑ m : ZMod p, chi p m := by
      have e := Equiv.sum_comp (Units.mulLeft (Units.mk0 c hc)) (chi p)
      rw [← e]
      apply Finset.sum_congr rfl
      intro m _
      rfl
    rw [h2]
    exact sum_chi_self hp hp2

/-- The key identity `(χ j - 1) * Sw j = p` for nonzero `j`, obtained by
reindexing the sum defining `Sw` along `k ↦ k + 1`. -/
lemma Sw_mul_sub_one {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : 2 < p) {j : ZMod p} (hj : j ≠ 0) :
    (chi p j - 1) * Sw p j = (p : ℂ) := by
  have h1 : chi p j * Sw p j = ∑ k : ZMod p, ((k - 1).val : ℂ) * chi p (j * k) := by
    unfold Sw
    rw [Finset.mul_sum]
    have hstep : (∑ k : ZMod p, chi p j * ((k.val : ℂ) * chi p (j * k)))
        = ∑ k : ZMod p, (k.val : ℂ) * chi p (j * (k + 1)) := by
      apply Finset.sum_congr rfl
      intro k _
      calc chi p j * ((k.val : ℂ) * chi p (j * k))
          = (k.val : ℂ) * (chi p j * chi p (j * k)) := by ring
        _ = (k.val : ℂ) * chi p (j * (k + 1)) := by
          rw [← chi_add hp]
          congr 2
          ring
    rw [hstep]
    have e := Equiv.sum_comp (Equiv.addRight (1 : ZMod p))
      (fun k : ZMod p => ((k - 1).val : ℂ) * chi p (j * k))
    rw [← e]
    apply Finset.sum_congr rfl
    intro k _
    have hk1 : (Equiv.addRight (1 : ZMod p)) k = k + 1 := rfl
    rw [hk1, add_sub_cancel_right]
  have h4 : (chi p j - 1) * Sw p j
      = ∑ k : ZMod p, (((k - 1).val : ℂ) - (k.val : ℂ)) * chi p (j * k) := by
    rw [sub_mul, h1, one_mul]
    unfold Sw
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [h4]
  have hw : ∀ k : ZMod p, (((k - 1).val : ℂ) - (k.val : ℂ)) * chi p (j * k)
      = (-1 : ℂ) * chi p (j * k) + (if k = 0 then (p : ℂ) else 0) * chi p (j * k) := by
    intro k
    by_cases hk : k = 0
    · subst hk
      rw [if_pos rfl]
      have hval : ((0 : ZMod p) - 1).val = p - 1 := by
        have h1 : (0 : ZMod p) - 1 = -1 := zero_sub 1
        rw [h1]
        have h2 := ZMod.val_neg_one (p - 1)
        rw [show (p - 1).succ = p from
          (Nat.succ_eq_add_one (p - 1)).trans (Nat.sub_add_cancel (by omega : 1 ≤ p))] at h2
        exact h2
      have hcast : (((p - 1 : ℕ) : ℂ)) = (p : ℂ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one]
      rw [hval, ZMod.val_zero, Nat.cast_zero, hcast]
      ring
    · rw [if_neg hk]
      have hkval : k.val ≠ 0 := by
        intro h0
        apply hk
        have h1 : (k.val : ZMod p) = k := ZMod.natCast_zmod_val k
        rw [h0, Nat.cast_zero] at h1
        exact h1.symm
      have hval : (k - 1).val = k.val - 1 := by
        have h4 : ((k.val - 1 + 1 : ℕ) : ZMod p) = (k.val : ZMod p) := by
          rw [Nat.sub_add_cancel (by omega : 1 ≤ k.val)]
        rw [Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val] at h4
        have h2 : ((k.val - 1 : ℕ) : ZMod p) = k - 1 := by
          rw [eq_sub_iff_add_eq]
          exact h4
        rw [← h2, ZMod.val_natCast_of_lt (by have := k.val_lt; omega : k.val - 1 < p)]
      rw [hval, Nat.cast_sub (by omega : 1 ≤ k.val), Nat.cast_one]
      ring
  have h6 : (∑ k : ZMod p, (((k - 1).val : ℂ) - (k.val : ℂ)) * chi p (j * k))
      = (∑ k : ZMod p, (-1 : ℂ) * chi p (j * k))
        + ∑ k : ZMod p, (if k = 0 then (p : ℂ) else 0) * chi p (j * k) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [hw k]
  rw [h6]
  have h7 : (∑ k : ZMod p, (-1 : ℂ) * chi p (j * k)) = 0 := by
    rw [← Finset.mul_sum]
    have h8 : (∑ k : ZMod p, chi p (j * k)) = 0 := by
      rw [sum_chi hp hp2 j, if_neg hj]
    rw [h8, mul_zero]
  rw [h7, zero_add]
  have h9 : (∑ k : ZMod p, (if k = 0 then (p : ℂ) else 0) * chi p (j * k))
      = (p : ℂ) := by
    have h10 : (∑ k : ZMod p, (if k = 0 then (p : ℂ) else 0) * chi p (j * k))
        = ∑ k : ZMod p, (if k = 0 then (p : ℂ) * chi p (j * k) else 0) := by
      apply Finset.sum_congr rfl
      intro k _
      by_cases hk : k = 0
      · rw [if_pos hk, if_pos hk]
      · rw [if_neg hk, if_neg hk, zero_mul]
    rw [h10, Finset.sum_ite_eq']
    simp [chi_zero]
  exact h9

/-- The symmetric-polynomial identity obtained by clearing denominators in
`∑ 1 / (xᵢ - 1) = -2`. -/
lemma alg_symm {x₁ x₂ x₃ x₄ : ℂ} (h₁ : x₁ ≠ 1) (h₂ : x₂ ≠ 1) (h₃ : x₃ ≠ 1) (h₄ : x₄ ≠ 1)
    (h : 1 / (x₁ - 1) + 1 / (x₂ - 1) + 1 / (x₃ - 1) + 1 / (x₄ - 1) = -2) :
    2 + (x₁ * x₂ * x₃ + x₁ * x₂ * x₄ + x₁ * x₃ * x₄ + x₂ * x₃ * x₄)
      = x₁ + x₂ + x₃ + x₄ + 2 * (x₁ * x₂ * x₃ * x₄) := by
  have d₁ : x₁ - 1 ≠ 0 := sub_ne_zero.mpr h₁
  have d₂ : x₂ - 1 ≠ 0 := sub_ne_zero.mpr h₂
  have d₃ : x₃ - 1 ≠ 0 := sub_ne_zero.mpr h₃
  have d₄ : x₄ - 1 ≠ 0 := sub_ne_zero.mpr h₄
  field_simp at h
  linear_combination -h

end

snip end

problem usa1999_p3 (p : ℕ) (hp : p.Prime) (hp2 : 2 < p) (a b c d : ℤ)
    (ha : ¬ (p : ℤ) ∣ a) (hb : ¬ (p : ℤ) ∣ b) (hc : ¬ (p : ℤ) ∣ c) (hd : ¬ (p : ℤ) ∣ d)
    (h : ∀ n : ℤ, ¬ (p : ℤ) ∣ n →
      Int.fract (((n * a : ℤ) : ℝ) / (p : ℝ)) + Int.fract (((n * b : ℤ) : ℝ) / (p : ℝ)) +
      Int.fract (((n * c : ℤ) : ℝ) / (p : ℝ)) + Int.fract (((n * d : ℤ) : ℝ) / (p : ℝ)) = 2) :
    (p : ℤ) ∣ a + b ∧ (p : ℤ) ∣ c + d ∨
      (p : ℤ) ∣ a + c ∧ (p : ℤ) ∣ b + d ∨
        (p : ℤ) ∣ a + d ∧ (p : ℤ) ∣ b + c := by
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  haveI : Fact p.Prime := ⟨hp⟩
  -- abbreviations for the residue classes of `a, b, c, d` in `ZMod p`
  set A : ZMod p := (a : ZMod p) with hA
  set B : ZMod p := (b : ZMod p) with hB
  set C : ZMod p := (c : ZMod p) with hC
  set D : ZMod p := (d : ZMod p) with hD
  have hA0 : A ≠ 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd a p).not.mpr ha
  have hB0 : B ≠ 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd b p).not.mpr hb
  have hC0 : C ≠ 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd c p).not.mpr hc
  have hD0 : D ≠ 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd d p).not.mpr hd
  -- the hypothesis, recast as a statement about residues in `ZMod p`
  have hyp : ∀ n : ZMod p, n ≠ 0 →
      (n * A).val + (n * B).val + (n * C).val + (n * D).val = 2 * p := by
    intro n hn
    have hcast : ((n.val : ℤ) : ZMod p) = n := by
      rw [Int.cast_natCast]
      exact ZMod.natCast_zmod_val n
    have hn0 : ¬ (p : ℤ) ∣ (n.val : ℤ) := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, hcast]
      exact hn
    have h2 := h (n.val : ℤ) hn0
    rw [Int.fract_div_intCast_eq_div_intCast_mod,
      Int.fract_div_intCast_eq_div_intCast_mod,
      Int.fract_div_intCast_eq_div_intCast_mod,
      Int.fract_div_intCast_eq_div_intCast_mod] at h2
    have e1 : ((n.val : ℤ) * a) % (p : ℤ) = ((n * A).val : ℤ) := by
      rw [← ZMod.val_intCast, Int.cast_mul, hcast, ← hA]
    have e2 : ((n.val : ℤ) * b) % (p : ℤ) = ((n * B).val : ℤ) := by
      rw [← ZMod.val_intCast, Int.cast_mul, hcast, ← hB]
    have e3 : ((n.val : ℤ) * c) % (p : ℤ) = ((n * C).val : ℤ) := by
      rw [← ZMod.val_intCast, Int.cast_mul, hcast, ← hC]
    have e4 : ((n.val : ℤ) * d) % (p : ℤ) = ((n * D).val : ℤ) := by
      rw [← ZMod.val_intCast, Int.cast_mul, hcast, ← hD]
    rw [e1, e2, e3, e4] at h2
    have h3 : (((n * A).val + (n * B).val + (n * C).val + (n * D).val : ℕ) : ℝ)
        = 2 * (p : ℝ) := by
      have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.pos.ne'
      have h4 := congrArg (· * (p : ℝ)) h2
      rw [add_mul, add_mul, add_mul] at h4
      rw [div_mul_cancel₀ _ hpR, div_mul_cancel₀ _ hpR, div_mul_cancel₀ _ hpR,
        div_mul_cancel₀ _ hpR] at h4
      push_cast at h4 ⊢
      linear_combination h4
    exact_mod_cast h3
  -- inverses in `ZMod p`
  set A' : ZMod p := A⁻¹ with hA'
  set B' : ZMod p := B⁻¹ with hB'
  set C' : ZMod p := C⁻¹ with hC'
  set D' : ZMod p := D⁻¹ with hD'
  have hA'0 : A' ≠ 0 := inv_eq_zero.not.mpr hA0
  have hB'0 : B' ≠ 0 := inv_eq_zero.not.mpr hB0
  have hC'0 : C' ≠ 0 := inv_eq_zero.not.mpr hC0
  have hD'0 : D' ≠ 0 := inv_eq_zero.not.mpr hD0
  -- reindexing identity: summing the weighted residues over all `n` gives `Sw`
  have reidx : ∀ X : ZMod p, X ≠ 0 → ∀ m : ZMod p,
      (∑ n : ZMod p, ((n * X).val : ℂ) * chi p (-(m * n))) = Sw p (-(m * X⁻¹)) := by
    intro X hX m
    have hu : X⁻¹ ≠ 0 := inv_eq_zero.not.mpr hX
    have hXX : X⁻¹ * X = 1 := inv_mul_cancel₀ hX
    have e := Equiv.sum_comp (Units.mulLeft (Units.mk0 X⁻¹ hu))
      (fun n : ZMod p => ((n * X).val : ℂ) * chi p (-(m * n)))
    rw [← e]
    unfold Sw
    apply Finset.sum_congr rfl
    intro i _
    have hei : (Units.mulLeft (Units.mk0 X⁻¹ hu)) i = X⁻¹ * i := by
      simp [Units.mulLeft_apply]
    rw [hei]
    have hval : X⁻¹ * i * X = i := by
      calc X⁻¹ * i * X = X⁻¹ * X * i := by ring
        _ = 1 * i := by rw [hXX]
        _ = i := one_mul i
    have harg : -(m * (X⁻¹ * i)) = -(m * X⁻¹) * i := by ring
    rw [hval, harg]
  -- the character-weighted form of the hypothesis, summed over `n`
  have keyEq : ∀ m : ZMod p, m ≠ 0 →
      Sw p (-(m * A')) + Sw p (-(m * B')) + Sw p (-(m * C')) + Sw p (-(m * D'))
        = -2 * (p : ℂ) := by
    intro m hm
    have per_n : ∀ n : ZMod p,
        ((n * A).val : ℂ) * chi p (-(m * n)) + ((n * B).val : ℂ) * chi p (-(m * n)) +
        ((n * C).val : ℂ) * chi p (-(m * n)) + ((n * D).val : ℂ) * chi p (-(m * n))
        = 2 * (p : ℂ) * (chi p (-(m * n)) - if n = 0 then (1 : ℂ) else 0) := by
      intro n
      by_cases hn : n = 0
      · subst hn
        simp [chi_zero, ZMod.val_zero]
      · have h1 := hyp n hn
        have h2 : ((n * A).val : ℂ) + ((n * B).val : ℂ) + ((n * C).val : ℂ) +
            ((n * D).val : ℂ) = 2 * (p : ℂ) := by exact_mod_cast h1
        have h3 := congrArg (· * chi p (-(m * n))) h2
        rw [if_neg hn, sub_zero]
        linear_combination h3
    have summed : (∑ n : ZMod p, (((n * A).val : ℂ) * chi p (-(m * n)) +
        ((n * B).val : ℂ) * chi p (-(m * n)) + ((n * C).val : ℂ) * chi p (-(m * n)) +
        ((n * D).val : ℂ) * chi p (-(m * n))))
        = ∑ n : ZMod p, 2 * (p : ℂ) * (chi p (-(m * n)) - if n = 0 then (1 : ℂ) else 0) :=
      Finset.sum_congr rfl (fun n _ => per_n n)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib] at summed
    rw [reidx A hA0 m, reidx B hB0 m, reidx C hC0 m, reidx D hD0 m] at summed
    have hRHS : (∑ n : ZMod p, 2 * (p : ℂ) * (chi p (-(m * n)) -
        if n = 0 then (1 : ℂ) else 0)) = -2 * (p : ℂ) := by
      rw [← Finset.mul_sum]
      have h1 : (∑ n : ZMod p, (chi p (-(m * n)) - if n = 0 then (1 : ℂ) else 0))
          = -1 := by
        rw [Finset.sum_sub_distrib]
        have h2 : (∑ n : ZMod p, chi p (-(m * n))) = 0 := by
          have h2' : (∑ n : ZMod p, chi p (-(m * n))) = ∑ n : ZMod p, chi p ((-m) * n) :=
            Finset.sum_congr rfl (fun n _ => by congr 1; ring)
          rw [h2', sum_chi hp hp2 (-m), if_neg (neg_ne_zero.mpr hm)]
        have h3 : (∑ n : ZMod p, (if n = 0 then (1 : ℂ) else 0)) = 1 := by
          rw [Finset.sum_ite_eq']
          simp
        rw [h2, h3]
        ring
      rw [h1]
      ring
    rw [hRHS] at summed
    exact summed
  -- dividing by `p`, we get the reciprocal equation
  have recipEq : ∀ m : ZMod p, m ≠ 0 →
      1 / (chi p (-(m * A')) - 1) + 1 / (chi p (-(m * B')) - 1) +
      1 / (chi p (-(m * C')) - 1) + 1 / (chi p (-(m * D')) - 1) = -2 := by
    intro m hm
    have hneA : chi p (-(m * A')) ≠ 1 :=
      (chi_eq_one_iff hp (-(m * A'))).not.mpr (neg_ne_zero.mpr (mul_ne_zero hm hA'0))
    have hneB : chi p (-(m * B')) ≠ 1 :=
      (chi_eq_one_iff hp (-(m * B'))).not.mpr (neg_ne_zero.mpr (mul_ne_zero hm hB'0))
    have hneC : chi p (-(m * C')) ≠ 1 :=
      (chi_eq_one_iff hp (-(m * C'))).not.mpr (neg_ne_zero.mpr (mul_ne_zero hm hC'0))
    have hneD : chi p (-(m * D')) ≠ 1 :=
      (chi_eq_one_iff hp (-(m * D'))).not.mpr (neg_ne_zero.mpr (mul_ne_zero hm hD'0))
    have hSA : Sw p (-(m * A')) = (p : ℂ) / (chi p (-(m * A')) - 1) := by
      have h1 := Sw_mul_sub_one hp hp2 (neg_ne_zero.mpr (mul_ne_zero hm hA'0))
      rw [eq_div_iff (sub_ne_zero.mpr hneA), mul_comm]
      exact h1
    have hSB : Sw p (-(m * B')) = (p : ℂ) / (chi p (-(m * B')) - 1) := by
      have h1 := Sw_mul_sub_one hp hp2 (neg_ne_zero.mpr (mul_ne_zero hm hB'0))
      rw [eq_div_iff (sub_ne_zero.mpr hneB), mul_comm]
      exact h1
    have hSC : Sw p (-(m * C')) = (p : ℂ) / (chi p (-(m * C')) - 1) := by
      have h1 := Sw_mul_sub_one hp hp2 (neg_ne_zero.mpr (mul_ne_zero hm hC'0))
      rw [eq_div_iff (sub_ne_zero.mpr hneC), mul_comm]
      exact h1
    have hSD : Sw p (-(m * D')) = (p : ℂ) / (chi p (-(m * D')) - 1) := by
      have h1 := Sw_mul_sub_one hp hp2 (neg_ne_zero.mpr (mul_ne_zero hm hD'0))
      rw [eq_div_iff (sub_ne_zero.mpr hneD), mul_comm]
      exact h1
    have h2 := keyEq m hm
    rw [hSA, hSB, hSC, hSD] at h2
    have e : ∀ x : ℂ, (p : ℂ) / x = (p : ℂ) * (1 / x) := fun x => (mul_one_div (p : ℂ) x).symm
    rw [e, e, e, e] at h2
    have h3 : (p : ℂ) * (1 / (chi p (-(m * A')) - 1) + 1 / (chi p (-(m * B')) - 1) +
        1 / (chi p (-(m * C')) - 1) + 1 / (chi p (-(m * D')) - 1)) = (p : ℂ) * (-2) := by
      rw [mul_add, mul_add, mul_add, h2]
      ring
    exact mul_left_cancel₀ (by exact_mod_cast hp.pos.ne' : (p : ℂ) ≠ 0) h3
  -- clearing denominators: the symmetric relation, valid for every `m`
  have symEq : ∀ m : ZMod p,
      2 + (chi p ((-(A' + B' + C')) * m) + chi p ((-(A' + B' + D')) * m) +
          chi p ((-(A' + C' + D')) * m) + chi p ((-(B' + C' + D')) * m))
      = (chi p ((-A') * m) + chi p ((-B') * m) + chi p ((-C') * m) + chi p ((-D') * m)) +
        2 * chi p ((-(A' + B' + C' + D')) * m) := by
    intro m
    by_cases hm : m = 0
    · subst hm
      norm_num [chi_zero]
    · have hr := recipEq m hm
      have h1 := alg_symm (x₁ := chi p (-(m * A'))) (x₂ := chi p (-(m * B')))
        (x₃ := chi p (-(m * C'))) (x₄ := chi p (-(m * D')))
        ((chi_eq_one_iff hp (-(m * A'))).not.mpr (neg_ne_zero.mpr (mul_ne_zero hm hA'0)))
        ((chi_eq_one_iff hp (-(m * B'))).not.mpr (neg_ne_zero.mpr (mul_ne_zero hm hB'0)))
        ((chi_eq_one_iff hp (-(m * C'))).not.mpr (neg_ne_zero.mpr (mul_ne_zero hm hC'0)))
        ((chi_eq_one_iff hp (-(m * D'))).not.mpr (neg_ne_zero.mpr (mul_ne_zero hm hD'0)))
        hr
      -- turn products of `chi` into `chi` of sums
      have ht : ∀ u v w : ZMod p,
          chi p (-(m * u)) * chi p (-(m * v)) * chi p (-(m * w))
          = chi p (-(m * (u + v + w))) := by
        intro u v w
        rw [← chi_add hp, ← chi_add hp]
        congr 1
        ring
      have he4 : chi p (-(m * A')) * chi p (-(m * B')) * chi p (-(m * C')) * chi p (-(m * D'))
          = chi p (-(m * (A' + B' + C' + D'))) := by
        rw [← chi_add hp, ← chi_add hp, ← chi_add hp]
        congr 1
        ring
      rw [he4, ht A' B' C', ht A' B' D', ht A' C' D', ht B' C' D'] at h1
      -- normalize `-(m * T)` to `(-T) * m`
      have cn : ∀ T : ZMod p, chi p (-(m * T)) = chi p ((-T) * m) := by
        intro T; congr 1; ring
      simp only [cn] at h1
      exact h1
  -- sum the symmetric relation over all `m : ZMod p`
  have bigSum : (∑ m : ZMod p, ((2 : ℂ) + (chi p ((-(A' + B' + C')) * m) +
      chi p ((-(A' + B' + D')) * m) + chi p ((-(A' + C' + D')) * m) +
      chi p ((-(B' + C' + D')) * m))))
      = ∑ m : ZMod p, ((chi p ((-A') * m) + chi p ((-B') * m) + chi p ((-C') * m) +
        chi p ((-D') * m)) + 2 * chi p ((-(A' + B' + C' + D')) * m)) :=
    Finset.sum_congr rfl (fun m _ => symEq m)
  have evalL : (∑ m : ZMod p, ((2 : ℂ) + (chi p ((-(A' + B' + C')) * m) +
      chi p ((-(A' + B' + D')) * m) + chi p ((-(A' + C' + D')) * m) +
      chi p ((-(B' + C' + D')) * m))))
      = 2 * (p : ℂ) + ((if A' + B' + C' = 0 then (p : ℂ) else 0) +
        (if A' + B' + D' = 0 then (p : ℂ) else 0) + (if A' + C' + D' = 0 then (p : ℂ) else 0) +
        (if B' + C' + D' = 0 then (p : ℂ) else 0)) := by
    rw [Finset.sum_add_distrib]
    have h1 : (∑ m : ZMod p, (2 : ℂ)) = 2 * (p : ℂ) := by
      rw [Finset.sum_const, Finset.card_univ, ZMod.card p, nsmul_eq_mul, mul_comm]
    rw [h1, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
    have e1 : (∑ m : ZMod p, chi p ((-(A' + B' + C')) * m))
        = if A' + B' + C' = 0 then (p : ℂ) else 0 := by
      rw [sum_chi hp hp2 (-(A' + B' + C'))]
      by_cases h : A' + B' + C' = 0
      · rw [if_pos h, if_pos (by rw [h, neg_zero])]
      · rw [if_neg h, if_neg (neg_eq_zero.not.mpr h)]
    have e2 : (∑ m : ZMod p, chi p ((-(A' + B' + D')) * m))
        = if A' + B' + D' = 0 then (p : ℂ) else 0 := by
      rw [sum_chi hp hp2 (-(A' + B' + D'))]
      by_cases h : A' + B' + D' = 0
      · rw [if_pos h, if_pos (by rw [h, neg_zero])]
      · rw [if_neg h, if_neg (neg_eq_zero.not.mpr h)]
    have e3 : (∑ m : ZMod p, chi p ((-(A' + C' + D')) * m))
        = if A' + C' + D' = 0 then (p : ℂ) else 0 := by
      rw [sum_chi hp hp2 (-(A' + C' + D'))]
      by_cases h : A' + C' + D' = 0
      · rw [if_pos h, if_pos (by rw [h, neg_zero])]
      · rw [if_neg h, if_neg (neg_eq_zero.not.mpr h)]
    have e4 : (∑ m : ZMod p, chi p ((-(B' + C' + D')) * m))
        = if B' + C' + D' = 0 then (p : ℂ) else 0 := by
      rw [sum_chi hp hp2 (-(B' + C' + D'))]
      by_cases h : B' + C' + D' = 0
      · rw [if_pos h, if_pos (by rw [h, neg_zero])]
      · rw [if_neg h, if_neg (neg_eq_zero.not.mpr h)]
    rw [e1, e2, e3, e4]
  have evalR : (∑ m : ZMod p, ((chi p ((-A') * m) + chi p ((-B') * m) + chi p ((-C') * m) +
      chi p ((-D') * m)) + 2 * chi p ((-(A' + B' + C' + D')) * m)))
      = 2 * (if A' + B' + C' + D' = 0 then (p : ℂ) else 0) := by
    rw [Finset.sum_add_distrib]
    have hs : (∑ m : ZMod p, (chi p ((-A') * m) + chi p ((-B') * m) + chi p ((-C') * m) +
        chi p ((-D') * m))) = 0 := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
      have s1 : (∑ m : ZMod p, chi p ((-A') * m)) = 0 := by
        rw [sum_chi hp hp2 (-A'), if_neg (neg_ne_zero.mpr hA'0)]
      have s2 : (∑ m : ZMod p, chi p ((-B') * m)) = 0 := by
        rw [sum_chi hp hp2 (-B'), if_neg (neg_ne_zero.mpr hB'0)]
      have s3 : (∑ m : ZMod p, chi p ((-C') * m)) = 0 := by
        rw [sum_chi hp hp2 (-C'), if_neg (neg_ne_zero.mpr hC'0)]
      have s4 : (∑ m : ZMod p, chi p ((-D') * m)) = 0 := by
        rw [sum_chi hp hp2 (-D'), if_neg (neg_ne_zero.mpr hD'0)]
      rw [s1, s2, s3, s4]
      ring
    rw [hs, zero_add]
    have htot : (∑ m : ZMod p, 2 * chi p ((-(A' + B' + C' + D')) * m))
        = 2 * (if A' + B' + C' + D' = 0 then (p : ℂ) else 0) := by
      rw [← Finset.mul_sum, sum_chi hp hp2 (-(A' + B' + C' + D'))]
      by_cases h : A' + B' + C' + D' = 0
      · rw [if_pos h, if_pos (by rw [h, neg_zero])]
      · rw [if_neg h, if_neg (neg_eq_zero.not.mpr h)]
    rw [htot]
  rw [evalL, evalR] at bigSum
  -- counting: the total sum of the inverses must vanish
  have hTot : A' + B' + C' + D' = 0 := by
    have bit : ∀ c : ZMod p, (if c = 0 then (p : ℂ) else 0)
        = (p : ℂ) * (if c = 0 then (1 : ℂ) else 0) := by
      intro c
      by_cases hc : c = 0
      · rw [if_pos hc, if_pos hc, mul_one]
      · rw [if_neg hc, if_neg hc, mul_zero]
    rw [bit (A' + B' + C'), bit (A' + B' + D'), bit (A' + C' + D'), bit (B' + C' + D'),
      bit (A' + B' + C' + D')] at bigSum
    have h5 : (2 : ℂ) + ((if A' + B' + C' = 0 then (1 : ℂ) else 0) +
        (if A' + B' + D' = 0 then (1 : ℂ) else 0) + (if A' + C' + D' = 0 then (1 : ℂ) else 0) +
        (if B' + C' + D' = 0 then (1 : ℂ) else 0))
        = 2 * (if A' + B' + C' + D' = 0 then (1 : ℂ) else 0) := by
      have h6 : (p : ℂ) * ((2 : ℂ) + ((if A' + B' + C' = 0 then (1 : ℂ) else 0) +
          (if A' + B' + D' = 0 then (1 : ℂ) else 0) + (if A' + C' + D' = 0 then (1 : ℂ) else 0) +
          (if B' + C' + D' = 0 then (1 : ℂ) else 0)))
          = (p : ℂ) * (2 * (if A' + B' + C' + D' = 0 then (1 : ℂ) else 0)) := by
        linear_combination bigSum
      exact mul_left_cancel₀ (by exact_mod_cast hp.pos.ne' : (p : ℂ) ≠ 0) h6
    by_cases hT : A' + B' + C' + D' = 0
    · exact hT
    · rw [if_neg hT, mul_zero] at h5
      split_ifs at h5 <;> norm_num at h5
  -- the relation now reads: the character sum is "odd"
  have oddEq : ∀ m : ZMod p,
      chi p (m * A') + chi p (m * B') + chi p (m * C') + chi p (m * D')
      = chi p (-(m * A')) + chi p (-(m * B')) + chi p (-(m * C')) + chi p (-(m * D')) := by
    intro m
    have h1 := symEq m
    have hT1 : B' + C' + D' = -A' := by linear_combination hTot
    have hT2 : A' + C' + D' = -B' := by linear_combination hTot
    have hT3 : A' + B' + D' = -C' := by linear_combination hTot
    have hT4 : A' + B' + C' = -D' := by linear_combination hTot
    have e1 : (-(A' + B' + C')) * m = m * D' := by rw [hT4]; ring
    have e2 : (-(A' + B' + D')) * m = m * C' := by rw [hT3]; ring
    have e3 : (-(A' + C' + D')) * m = m * B' := by rw [hT2]; ring
    have e4 : (-(B' + C' + D')) * m = m * A' := by rw [hT1]; ring
    have e5 : (-(A' + B' + C' + D')) * m = 0 := by rw [hTot]; ring
    have f1 : (-A') * m = -(m * A') := by ring
    have f2 : (-B') * m = -(m * B') := by ring
    have f3 : (-C') * m = -(m * C') := by ring
    have f4 : (-D') * m = -(m * D') := by ring
    rw [e1, e2, e3, e4, e5, f1, f2, f3, f4, chi_zero] at h1
    linear_combination h1
  -- multiply by `χ ((-A') * m)` and sum over `m`
  have finF : (∑ m : ZMod p, chi p ((-A') * m) * (chi p (m * A') + chi p (m * B') +
      chi p (m * C') + chi p (m * D')))
      = (if A' - A' = 0 then (p : ℂ) else 0) + (if B' - A' = 0 then (p : ℂ) else 0) +
        (if C' - A' = 0 then (p : ℂ) else 0) + (if D' - A' = 0 then (p : ℂ) else 0) := by
    have per : ∀ X : ZMod p, (∑ m : ZMod p, chi p ((-A') * m) * chi p (m * X))
        = if X - A' = 0 then (p : ℂ) else 0 := by
      intro X
      have h1 : (∑ m : ZMod p, chi p ((-A') * m) * chi p (m * X))
          = ∑ m : ZMod p, chi p ((X - A') * m) := by
        apply Finset.sum_congr rfl
        intro m _
        rw [← chi_add hp]
        congr 1
        ring
      rw [h1, sum_chi hp hp2 (X - A')]
    have h0 : (∑ m : ZMod p, chi p ((-A') * m) * (chi p (m * A') + chi p (m * B') +
        chi p (m * C') + chi p (m * D')))
        = ∑ m : ZMod p, (chi p ((-A') * m) * chi p (m * A') + chi p ((-A') * m) * chi p (m * B') +
          chi p ((-A') * m) * chi p (m * C') + chi p ((-A') * m) * chi p (m * D')) := by
      apply Finset.sum_congr rfl
      intro m _
      ring
    rw [h0, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
      per A', per B', per C', per D']
  have finG : (∑ m : ZMod p, chi p ((-A') * m) * (chi p (-(m * A')) + chi p (-(m * B')) +
      chi p (-(m * C')) + chi p (-(m * D'))))
      = (if A' + A' = 0 then (p : ℂ) else 0) + (if A' + B' = 0 then (p : ℂ) else 0) +
        (if A' + C' = 0 then (p : ℂ) else 0) + (if A' + D' = 0 then (p : ℂ) else 0) := by
    have per2 : ∀ X : ZMod p, (∑ m : ZMod p, chi p ((-A') * m) * chi p (-(m * X)))
        = if A' + X = 0 then (p : ℂ) else 0 := by
      intro X
      have h1 : (∑ m : ZMod p, chi p ((-A') * m) * chi p (-(m * X)))
          = ∑ m : ZMod p, chi p ((-(A' + X)) * m) := by
        apply Finset.sum_congr rfl
        intro m _
        rw [← chi_add hp]
        congr 1
        ring
      rw [h1, sum_chi hp hp2 (-(A' + X))]
      by_cases h : A' + X = 0
      · rw [if_pos h, if_pos (by rw [h, neg_zero])]
      · rw [if_neg h, if_neg (neg_eq_zero.not.mpr h)]
    have h0 : (∑ m : ZMod p, chi p ((-A') * m) * (chi p (-(m * A')) + chi p (-(m * B')) +
        chi p (-(m * C')) + chi p (-(m * D'))))
        = ∑ m : ZMod p, (chi p ((-A') * m) * chi p (-(m * A')) + chi p ((-A') * m) * chi p (-(m * B')) +
          chi p ((-A') * m) * chi p (-(m * C')) + chi p ((-A') * m) * chi p (-(m * D'))) := by
      apply Finset.sum_congr rfl
      intro m _
      ring
    rw [h0, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
      per2 A', per2 B', per2 C', per2 D']
  have hFinal : (if A' - A' = 0 then (p : ℂ) else 0) + (if B' - A' = 0 then (p : ℂ) else 0) +
      (if C' - A' = 0 then (p : ℂ) else 0) + (if D' - A' = 0 then (p : ℂ) else 0)
      = (if A' + A' = 0 then (p : ℂ) else 0) + (if A' + B' = 0 then (p : ℂ) else 0) +
        (if A' + C' = 0 then (p : ℂ) else 0) + (if A' + D' = 0 then (p : ℂ) else 0) := by
    have hFG : (∑ m : ZMod p, chi p ((-A') * m) * (chi p (m * A') + chi p (m * B') +
        chi p (m * C') + chi p (m * D')))
        = ∑ m : ZMod p, chi p ((-A') * m) * (chi p (-(m * A')) + chi p (-(m * B')) +
          chi p (-(m * C')) + chi p (-(m * D'))) := by
      apply Finset.sum_congr rfl
      intro m _
      rw [oddEq m]
    rw [← finF, ← finG]
    exact hFG
  have h2A : A' + A' ≠ 0 := by
    have hv : ((2 : ℕ) : ZMod p).val = 2 := ZMod.val_natCast_of_lt hp2
    have h2 : (2 : ZMod p) ≠ 0 := by
      have hz : ((2 : ℕ) : ZMod p) ≠ 0 := by
        intro h0
        rw [h0, ZMod.val_zero] at hv
        omega
      exact_mod_cast hz
    have h3 : A' + A' = 2 * A' := by ring
    rw [h3]
    exact mul_ne_zero h2 hA'0
  -- at least one of `A' + B'`, `A' + C'`, `A' + D'` vanishes
  have hone : A' + B' = 0 ∨ A' + C' = 0 ∨ A' + D' = 0 := by
    rw [if_pos (sub_self A'), if_neg h2A] at hFinal
    by_contra hcon
    push Not at hcon
    rw [if_neg hcon.1, if_neg hcon.2.1, if_neg hcon.2.2] at hFinal
    have bit : ∀ c : ZMod p, (if c = 0 then (p : ℂ) else 0)
        = (p : ℂ) * (if c = 0 then (1 : ℂ) else 0) := by
      intro c
      by_cases hc : c = 0
      · rw [if_pos hc, if_pos hc, mul_one]
      · rw [if_neg hc, if_neg hc, mul_zero]
    rw [bit (B' - A'), bit (C' - A'), bit (D' - A')] at hFinal
    have h5 : (1 : ℂ) + ((if B' - A' = 0 then (1 : ℂ) else 0) +
        ((if C' - A' = 0 then (1 : ℂ) else 0) + (if D' - A' = 0 then (1 : ℂ) else 0))) = 0 := by
      have h6 : (p : ℂ) * (1 + ((if B' - A' = 0 then (1 : ℂ) else 0) +
          ((if C' - A' = 0 then (1 : ℂ) else 0) + (if D' - A' = 0 then (1 : ℂ) else 0)))) = 0 := by
        linear_combination hFinal
      exact mul_left_cancel₀ (by exact_mod_cast hp.pos.ne' : (p : ℂ) ≠ 0)
        (h6.trans (mul_zero (p : ℂ)).symm)
    split_ifs at h5 <;> norm_num at h5
  -- turn a vanishing pair of inverses into a vanishing pair
  have pair_zero : ∀ {X Y X' Y' : ZMod p}, X' = X⁻¹ → Y' = Y⁻¹ → X' + Y' = 0 → X + Y = 0 := by
    intro X Y X' Y' hX' hY' hsum
    have h1 : X' = -Y' := eq_neg_of_add_eq_zero_left hsum
    have h2 : X = X'⁻¹ := by rw [hX', inv_inv]
    have h3 : Y = Y'⁻¹ := by rw [hY', inv_inv]
    rw [h2, h3, h1, inv_neg, neg_add_cancel]
  -- conversion back to divisibility of integers
  have dvd_of_zmod : ∀ {x y : ℤ}, (x : ZMod p) + (y : ZMod p) = 0 → (p : ℤ) ∣ x + y := by
    intro x y hxy
    have h1 : ((x + y : ℤ) : ZMod p) = 0 := by
      rw [Int.cast_add]
      exact hxy
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd (x + y) p).mp h1
  rcases hone with h1 | h1 | h1
  · have h2 : C' + D' = 0 := by linear_combination hTot - h1
    have hAB : (a : ZMod p) + (b : ZMod p) = 0 := pair_zero hA' hB' h1
    have hCD : (c : ZMod p) + (d : ZMod p) = 0 := pair_zero hC' hD' h2
    left
    exact ⟨dvd_of_zmod hAB, dvd_of_zmod hCD⟩
  · have h2 : B' + D' = 0 := by linear_combination hTot - h1
    have hAC : (a : ZMod p) + (c : ZMod p) = 0 := pair_zero hA' hC' h1
    have hBD : (b : ZMod p) + (d : ZMod p) = 0 := pair_zero hB' hD' h2
    right; left
    exact ⟨dvd_of_zmod hAC, dvd_of_zmod hBD⟩
  · have h2 : B' + C' = 0 := by linear_combination hTot - h1
    have hAD : (a : ZMod p) + (d : ZMod p) = 0 := pair_zero hA' hD' h1
    have hBC : (b : ZMod p) + (c : ZMod p) = 0 := pair_zero hB' hC' h2
    right; right
    exact ⟨dvd_of_zmod hAD, dvd_of_zmod hBC⟩

end Usa1999P3
