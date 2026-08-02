/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Tactic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.Complex.Trigonometric
public import ProblemExtraction

@[expose] public section

problem_file {
  tags := [.Geometry, .Algebra]
}

/-!
# International Mathematical Olympiad 1990, Problem 6

Prove that there exists a convex 1990-gon such that all its angles are
equal and the lengths of the sides are the numbers 1², 2², ..., 1990²
in some order.

## Formalization

We describe the polygon in the complex plane by its side vectors.
Let `w = exp (2πi / 1990)`, a primitive 1990th root of unity, and let `p`
be a permutation of `Fin 1990`. Consider the side vectors
`sₖ = (pₖ + 1)² * wᵏ` for `k = 0, …, 1989`. We prove that `p` can be chosen
so that

* `‖sₖ‖ = (pₖ + 1)²`, so the lengths of the sides are the numbers
  `1², 2², …, 1990²` in some order;
* `∑ₖ sₖ = 0`, so the polygon closes up;
* `sₖ₊₁` is a positive real multiple of `w * sₖ`, i.e. the direction of each
  side is obtained from the previous one by a rotation through the constant
  angle `2π / 1990`. Hence all exterior angles of the polygon (and therefore
  all interior angles) are equal, and the polygon always turns in the same
  direction; together with the closing condition this means the polygon is
  convex.
-/

namespace Imo1990P6

/-- The primitive 1990th root of unity `exp (2πi / 1990)`; side `k` of the
polygon points in direction `w ^ k`. -/
noncomputable def w : ℂ := Complex.exp (2 * Real.pi * Complex.I / 1990)

snip begin

-- We follow the solution from https://prase.cz/kalva/imo/isoln/isoln906.html :
-- `1990 = 2 · 5 · 199`, and writing the exponent `k` of `w ^ k` via the Chinese
-- remainder theorem as `k ≡ 995 i + 398 j + 10 l (mod 1990)`, the assignment
-- `p(k) = 995 i + 199 j + l` makes the vector sum of the sides telescope to zero.

theorem hw1990 : w ^ 1990 = 1 := by
  have e : (1990 : ℕ) * (2 * (Real.pi : ℂ) * Complex.I / 1990)
      = 2 * (Real.pi : ℂ) * Complex.I := by
    field
  unfold w
  rw [← Complex.exp_nat_mul, e, Complex.exp_two_pi_mul_I]

theorem hw995 : w ^ 995 = -1 := by
  have e : (995 : ℕ) * (2 * (Real.pi : ℂ) * Complex.I / 1990)
      = (Real.pi : ℂ) * Complex.I := by
    field
  unfold w
  rw [← Complex.exp_nat_mul, e, Complex.exp_pi_mul_I]

/-- If `1990 = m * q` with `1 < q`, then `w ^ m ≠ 1`. -/
theorem w_pow_ne_one {m q : ℕ} (hm0 : m ≠ 0) (hq : 1 < q) (hm : 1990 = m * q) :
    w ^ m ≠ 1 := by
  intro h
  unfold w at h
  rw [← Complex.exp_nat_mul] at h
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (by omega : 0 < q))
  have hm0' : (m : ℂ) ≠ 0 := by exact_mod_cast hm0
  have h2pi : (2 : ℂ) * (Real.pi : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero))
      Complex.I_ne_zero
  have hcast : (1990 : ℂ) = (m : ℂ) * (q : ℂ) := by
    have hm' := congrArg (fun x : ℕ => (x : ℂ)) hm
    push_cast at hm'
    exact hm'
  have e : (m : ℕ) * (2 * (Real.pi : ℂ) * Complex.I / 1990)
      = (2 * (Real.pi : ℂ) * Complex.I) / (q : ℂ) := by
    rw [hcast]
    field_simp [hm0', hq0]
  rw [e] at h
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h
  rw [div_eq_iff hq0] at hn
  have h2 : ((q : ℂ) * (n : ℂ)) * (2 * (Real.pi : ℂ) * Complex.I)
      = 1 * (2 * (Real.pi : ℂ) * Complex.I) := by
    rw [one_mul, show ((q : ℂ) * (n : ℂ)) * (2 * (Real.pi : ℂ) * Complex.I)
        = (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) * (q : ℂ) by ring, ← hn]
  have h3 : (q : ℂ) * (n : ℂ) = 1 := mul_right_cancel₀ h2pi h2
  have h4 : (q : ℤ) * n = 1 := by exact_mod_cast h3
  have h5 : (q : ℤ) ≤ 1 := Int.le_of_dvd (by norm_num) ⟨n, h4.symm⟩
  have h6 : (2 : ℤ) ≤ (q : ℤ) := by exact_mod_cast hq
  omega

theorem hw398 : w ^ 398 ≠ 1 :=
  w_pow_ne_one (m := 398) (q := 5) (by norm_num) (by norm_num) rfl

theorem hw10 : w ^ 10 ≠ 1 :=
  w_pow_ne_one (m := 10) (q := 199) (by norm_num) (by norm_num) rfl

/-- Powers of `w` only depend on the exponent modulo `1990`. -/
theorem pow_mod_of_pow_eq (m : ℕ) : w ^ (m % 1990) = w ^ m := by
  have h : m = 1990 * (m / 1990) + m % 1990 := (Nat.div_add_mod m 1990).symm
  conv_rhs => rw [h]
  rw [pow_add, pow_mul, hw1990, one_pow, one_mul]

theorem hα5 : (w ^ 398) ^ 5 = 1 := by
  rw [← pow_mul, show 398 * 5 = 1990 from rfl, hw1990]

theorem hβ199 : (w ^ 10) ^ 199 = 1 := by
  rw [← pow_mul, show 10 * 199 = 1990 from rfl, hw1990]

/-- `w ^ 398` is a primitive 5th root of unity, so its powers sum to zero. -/
theorem hαsum : ∑ j : Fin 5, (w ^ 398) ^ j.val = 0 := by
  rw [Fin.sum_univ_eq_sum_range, geom_sum_eq hw398 5, hα5, sub_self, zero_div]

/-- `w ^ 10` is a primitive 199th root of unity, so its powers sum to zero. -/
theorem hβsum : ∑ l : Fin 199, (w ^ 10) ^ l.val = 0 := by
  rw [Fin.sum_univ_eq_sum_range, geom_sum_eq hw10 199, hβ199, sub_self, zero_div]

/-- The Chinese remainder bijection: `(i, j, l) ↦ 995 i + 398 j + 10 l (mod 1990)`. -/
def posFn : Fin 2 × Fin 5 × Fin 199 → Fin 1990 := fun ⟨i, j, l⟩ =>
  ⟨(995 * i.val + 398 * j.val + 10 * l.val) % 1990, by omega⟩

/-- The side-length assignment: `(i, j, l) ↦ 995 i + 199 j + l`. -/
def valFn : Fin 2 × Fin 5 × Fin 199 → Fin 1990 := fun ⟨i, j, l⟩ =>
  ⟨995 * i.val + 199 * j.val + l.val, by
    have hi := i.isLt
    have hj := j.isLt
    have hl := l.isLt
    omega⟩

theorem valFn_inj : Function.Injective valFn := by
  rintro ⟨i, j, l⟩ ⟨i', j', l'⟩ h
  have hv : 995 * i.val + 199 * j.val + l.val = 995 * i'.val + 199 * j'.val + l'.val :=
    congrArg Fin.val h
  have hb1 := i.isLt; have hb1' := i'.isLt
  have hb2 := j.isLt; have hb2' := j'.isLt
  have hb3 := l.isLt; have hb3' := l'.isLt
  have hi : i = i' := Fin.ext (by omega)
  have hj : j = j' := Fin.ext (by omega)
  have hl : l = l' := Fin.ext (by omega)
  simp only [Prod.mk.injEq]
  exact ⟨hi, hj, hl⟩

theorem posFn_inj : Function.Injective posFn := by
  rintro ⟨i, j, l⟩ ⟨i', j', l'⟩ h
  have hv : (995 * i.val + 398 * j.val + 10 * l.val) % 1990
      = (995 * i'.val + 398 * j'.val + 10 * l'.val) % 1990 := congrArg Fin.val h
  have hb1 := i.isLt; have hb1' := i'.isLt
  have hb2 := j.isLt; have hb2' := j'.isLt
  have hb3 := l.isLt; have hb3' := l'.isLt
  have hi : i = i' := Fin.ext (by omega)
  have hj : j = j' := Fin.ext (by omega)
  have hl : l = l' := Fin.ext (by omega)
  simp only [Prod.mk.injEq]
  exact ⟨hi, hj, hl⟩

theorem posFn_bij : Function.Bijective posFn :=
  (Fintype.bijective_iff_injective_and_card posFn).mpr ⟨posFn_inj, by
    simp [Fintype.card_prod, Fintype.card_fin]⟩

theorem valFn_bij : Function.Bijective valFn :=
  (Fintype.bijective_iff_injective_and_card valFn).mpr ⟨valFn_inj, by
    simp [Fintype.card_prod, Fintype.card_fin]⟩

/-- The Chinese remainder equivalence `Fin 2 × Fin 5 × Fin 199 ≃ Fin 1990`. -/
noncomputable def crtEquiv : Fin 2 × Fin 5 × Fin 199 ≃ Fin 1990 :=
  Equiv.ofBijective posFn posFn_bij

/-- The side-length equivalence `Fin 2 × Fin 5 × Fin 199 ≃ Fin 1990`. -/
noncomputable def valEquiv : Fin 2 × Fin 5 × Fin 199 ≃ Fin 1990 :=
  Equiv.ofBijective valFn valFn_bij

/-- The permutation of `Fin 1990` giving the side lengths of the polygon. -/
noncomputable def sidePerm : Equiv.Perm (Fin 1990) := crtEquiv.symm.trans valEquiv

/-- The `⟨i, j, l⟩`-th side vector, rewritten in terms of the roots of unity
`-1 = w ^ 995`, `w ^ 398` and `w ^ 10`. -/
theorem term_eq (i : Fin 2) (j : Fin 5) (l : Fin 199) :
    ((sidePerm (crtEquiv ⟨i, j, l⟩)).val + 1 : ℂ) ^ 2 * w ^ (crtEquiv ⟨i, j, l⟩).val
    = (995 * (i.val : ℂ) + 199 * (j.val : ℂ) + (l.val : ℂ) + 1) ^ 2
      * ((-1 : ℂ) ^ i.val * ((w ^ 398) ^ j.val * (w ^ 10) ^ l.val)) := by
  have e1 : (sidePerm (crtEquiv ⟨i, j, l⟩)).val = 995 * i.val + 199 * j.val + l.val :=
    congrArg Fin.val (show sidePerm (crtEquiv ⟨i, j, l⟩) = valEquiv ⟨i, j, l⟩ by
      simp [sidePerm])
  have e2 : (crtEquiv ⟨i, j, l⟩).val = (995 * i.val + 398 * j.val + 10 * l.val) % 1990 := rfl
  rw [e1, e2, pow_mod_of_pow_eq, pow_add, pow_add, pow_mul, pow_mul, pow_mul, hw995]
  push_cast
  ring

/-- Evaluation of the triple sum: after summing over `i : Fin 2`, the remaining
double sum splits into products of vanishing geometric sums. -/
theorem big_sum_zero :
    (∑ i : Fin 2, ∑ j : Fin 5, ∑ l : Fin 199,
      (995 * (i.val : ℂ) + 199 * (j.val : ℂ) + (l.val : ℂ) + 1) ^ 2
        * ((-1 : ℂ) ^ i.val * ((w ^ 398) ^ j.val * (w ^ 10) ^ l.val))) = 0 := by
  have step1 : ∀ (j : Fin 5) (l : Fin 199),
      (∑ i : Fin 2,
        (995 * (i.val : ℂ) + 199 * (j.val : ℂ) + (l.val : ℂ) + 1) ^ 2
          * ((-1 : ℂ) ^ i.val * ((w ^ 398) ^ j.val * (w ^ 10) ^ l.val)))
      = (w ^ 398) ^ j.val * (w ^ 10) ^ l.val
          * ((199 * (j.val : ℂ) + (l.val : ℂ) + 1) ^ 2
            - (199 * (j.val : ℂ) + (l.val : ℂ) + 1 + 995) ^ 2) := by
    intro j l
    rw [Fin.sum_univ_two, Fin.val_zero, Fin.val_one]
    ring
  have reorder : (∑ i : Fin 2, ∑ j : Fin 5, ∑ l : Fin 199,
        (995 * (i.val : ℂ) + 199 * (j.val : ℂ) + (l.val : ℂ) + 1) ^ 2
          * ((-1 : ℂ) ^ i.val * ((w ^ 398) ^ j.val * (w ^ 10) ^ l.val)))
      = ∑ j : Fin 5, ∑ l : Fin 199, ∑ i : Fin 2,
        (995 * (i.val : ℂ) + 199 * (j.val : ℂ) + (l.val : ℂ) + 1) ^ 2
          * ((-1 : ℂ) ^ i.val * ((w ^ 398) ^ j.val * (w ^ 10) ^ l.val)) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun j _ => Finset.sum_comm)
  have step3 : ∀ (j : Fin 5) (l : Fin 199),
      (w ^ 398) ^ j.val * (w ^ 10) ^ l.val
        * ((199 * (j.val : ℂ) + (l.val : ℂ) + 1) ^ 2
          - (199 * (j.val : ℂ) + (l.val : ℂ) + 1 + 995) ^ 2)
      = (-1990 * 199) * (((j.val : ℂ) * (w ^ 398) ^ j.val) * (w ^ 10) ^ l.val)
        + (-1990) * ((w ^ 398) ^ j.val * (((l.val : ℂ) + 1) * (w ^ 10) ^ l.val))
        + (-995 ^ 2) * ((w ^ 398) ^ j.val * (w ^ 10) ^ l.val) := by
    intro j l
    ring
  rw [reorder]
  rw [show (∑ j : Fin 5, ∑ l : Fin 199, ∑ i : Fin 2,
        (995 * (i.val : ℂ) + 199 * (j.val : ℂ) + (l.val : ℂ) + 1) ^ 2
          * ((-1 : ℂ) ^ i.val * ((w ^ 398) ^ j.val * (w ^ 10) ^ l.val)))
      = ∑ j : Fin 5, ∑ l : Fin 199,
        (w ^ 398) ^ j.val * (w ^ 10) ^ l.val
          * ((199 * (j.val : ℂ) + (l.val : ℂ) + 1) ^ 2
            - (199 * (j.val : ℂ) + (l.val : ℂ) + 1 + 995) ^ 2)
      from Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun l _ => step1 j l))]
  rw [show (∑ j : Fin 5, ∑ l : Fin 199,
        (w ^ 398) ^ j.val * (w ^ 10) ^ l.val
          * ((199 * (j.val : ℂ) + (l.val : ℂ) + 1) ^ 2
            - (199 * (j.val : ℂ) + (l.val : ℂ) + 1 + 995) ^ 2))
      = ∑ j : Fin 5, ∑ l : Fin 199,
        ((-1990 * 199) * (((j.val : ℂ) * (w ^ 398) ^ j.val) * (w ^ 10) ^ l.val)
        + (-1990) * ((w ^ 398) ^ j.val * (((l.val : ℂ) + 1) * (w ^ 10) ^ l.val))
        + (-995 ^ 2) * ((w ^ 398) ^ j.val * (w ^ 10) ^ l.val))
      from Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun l _ => step3 j l))]
  have step4 : (∑ j : Fin 5, ∑ l : Fin 199,
        ((-1990 * 199) * (((j.val : ℂ) * (w ^ 398) ^ j.val) * (w ^ 10) ^ l.val)
        + (-1990) * ((w ^ 398) ^ j.val * (((l.val : ℂ) + 1) * (w ^ 10) ^ l.val))
        + (-995 ^ 2) * ((w ^ 398) ^ j.val * (w ^ 10) ^ l.val)))
      = (-1990 * 199) * (∑ j : Fin 5, ∑ l : Fin 199,
          ((j.val : ℂ) * (w ^ 398) ^ j.val) * (w ^ 10) ^ l.val)
        + (-1990) * (∑ j : Fin 5, ∑ l : Fin 199,
          (w ^ 398) ^ j.val * (((l.val : ℂ) + 1) * (w ^ 10) ^ l.val))
        + (-995 ^ 2) * (∑ j : Fin 5, ∑ l : Fin 199,
          (w ^ 398) ^ j.val * (w ^ 10) ^ l.val) := by
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  have step5a : (∑ j : Fin 5, ∑ l : Fin 199,
        ((j.val : ℂ) * (w ^ 398) ^ j.val) * (w ^ 10) ^ l.val)
      = (∑ j : Fin 5, (j.val : ℂ) * (w ^ 398) ^ j.val)
        * (∑ l : Fin 199, (w ^ 10) ^ l.val) :=
    (Finset.sum_mul_sum Finset.univ Finset.univ _ _).symm
  have step5b : (∑ j : Fin 5, ∑ l : Fin 199,
        (w ^ 398) ^ j.val * (((l.val : ℂ) + 1) * (w ^ 10) ^ l.val))
      = (∑ j : Fin 5, (w ^ 398) ^ j.val)
        * (∑ l : Fin 199, ((l.val : ℂ) + 1) * (w ^ 10) ^ l.val) :=
    (Finset.sum_mul_sum Finset.univ Finset.univ _ _).symm
  have step5c : (∑ j : Fin 5, ∑ l : Fin 199, (w ^ 398) ^ j.val * (w ^ 10) ^ l.val)
      = (∑ j : Fin 5, (w ^ 398) ^ j.val) * (∑ l : Fin 199, (w ^ 10) ^ l.val) :=
    (Finset.sum_mul_sum Finset.univ Finset.univ _ _).symm
  rw [step4, step5a, step5b, step5c, hαsum, hβsum]
  ring

/-- The polygon closes up: the side vectors sum to zero. -/
theorem sides_sum : ∑ n : Fin 1990, ((sidePerm n).val + 1 : ℂ) ^ 2 * w ^ n.val = 0 := by
  rw [← Equiv.sum_comp crtEquiv
    (fun n : Fin 1990 => ((sidePerm n).val + 1 : ℂ) ^ 2 * w ^ n.val)]
  simp only [Fintype.sum_prod_type, term_eq]
  exact big_sum_zero

theorem hnormw : ‖w‖ = 1 := by
  have hre : (2 * (Real.pi : ℂ) * Complex.I / 1990).re = 0 := by
    have e : (2 * (Real.pi : ℂ) * Complex.I / 1990)
        = (((2 * Real.pi / 1990 : ℝ)) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [e, Complex.mul_I_re, Complex.ofReal_im, neg_zero]
  unfold w
  rw [Complex.norm_exp, hre, Real.exp_zero]

/-- The side lengths are the squares `1², …, 1990²` in some order. -/
theorem sides_len (k : Fin 1990) :
    ‖(((sidePerm k).val + 1 : ℂ) ^ 2 * w ^ k.val)‖ = ((sidePerm k).val + 1 : ℝ) ^ 2 := by
  rw [norm_mul, norm_pow, norm_pow, hnormw, one_pow, mul_one,
    show ((sidePerm k).val + 1 : ℂ) = (((sidePerm k).val + 1 : ℕ) : ℂ) by norm_cast,
    RCLike.norm_natCast]
  norm_cast

/-- At every vertex the direction rotates by the constant angle `2π / 1990`:
the next side vector is a positive real multiple of `w` times the previous one. -/
theorem sides_turn (k : Fin 1990) :
    ∃ c : ℝ, 0 < c ∧
      ((sidePerm (k + 1)).val + 1 : ℂ) ^ 2 * w ^ (k + 1).val
        = (c : ℂ) * w * (((sidePerm k).val + 1 : ℂ) ^ 2 * w ^ k.val) := by
  have ha0 : ((sidePerm k).val + 1 : ℂ) ≠ 0 := by
    rw [show ((sidePerm k).val + 1 : ℂ) = (((sidePerm k).val + 1 : ℝ) : ℂ) by norm_cast]
    exact Complex.ofReal_ne_zero.mpr (by positivity)
  have hadd : (k + 1 : Fin 1990).val = (k.val + 1) % 1990 := by
    have hk := k.isLt
    omega
  refine ⟨(((sidePerm (k + 1)).val + 1 : ℝ) ^ 2) / (((sidePerm k).val + 1 : ℝ) ^ 2),
    by positivity, ?_⟩
  rw [hadd, pow_mod_of_pow_eq, pow_succ w k.val]
  push_cast
  field_simp [ha0]

snip end

problem imo1990_p6 :
    ∃ p : Equiv.Perm (Fin 1990),
      (∀ k : Fin 1990,
        ‖(((p k).val + 1 : ℂ) ^ 2 * w ^ k.val)‖ = ((p k).val + 1 : ℝ) ^ 2) ∧
      (∑ k : Fin 1990, ((p k).val + 1 : ℂ) ^ 2 * w ^ k.val) = 0 ∧
      ∀ k : Fin 1990, ∃ c : ℝ, 0 < c ∧
        ((p (k + 1)).val + 1 : ℂ) ^ 2 * w ^ (k + 1).val
          = (c : ℂ) * w * (((p k).val + 1 : ℂ) ^ 2 * w ^ k.val) :=
  ⟨sidePerm, sides_len, sides_sum, sides_turn⟩

end Imo1990P6
