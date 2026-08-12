/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Algebra] }

/-!
# USA Mathematical Olympiad 2019, Problem 6

Find all polynomials P with real coefficients such that

    P(x)/yz + P(y)/zx + P(z)/xy = P(x − y) + P(y − z) + P(z − x)

for all nonzero real numbers x, y, z obeying 2xyz = x + y + z.
-/

namespace Usa2019P6

open Polynomial

determine SolutionSet : Set (Polynomial ℝ) := {P | ∃ c : ℝ, P = C c * (X ^ 2 + 3)}

snip begin

/-- The polynomial equation, multiplied through by `xyz`. This is the form of the
hypothesis that we use below: it says that `Q(x, y, z)` vanishes, where
`Q(x, y, z) = xP(x) + yP(y) + zP(z) − xyz (P(x−y) + P(y−z) + P(z−x))`. -/
def Qfun {K : Type*} [Field K] (P : Polynomial K) (x y z : K) : K :=
  x * P.eval x + y * P.eval y + z * P.eval z -
    x * y * z * (P.eval (x - y) + P.eval (y - z) + P.eval (z - x))

/-- The "cleared denominator" polynomial: for `n = P.natDegree`, the rational function
`(x, y) ↦ (2xy−1)^(n+1) * Qfun P x y ((x+y)/(2xy−1))` is actually a polynomial function,
and this is the corresponding polynomial, written as a polynomial in `y` whose
coefficients are polynomials in `x`. -/
noncomputable def PhiPoly {R : Type*} [CommRing R] (P : Polynomial R) :
    Polynomial (Polynomial R) :=
  ∑ k ∈ Finset.range (P.natDegree + 1),
    C (C (P.coeff k)) *
      ((C (C 2 * X) * X - 1) ^ (P.natDegree + 1) * (C (X ^ (k + 1)) + X ^ (k + 1)) +
       (C X + X) ^ (k + 1) * (C (C 2 * X) * X - 1) ^ (P.natDegree - k) -
       C X * X * (C X + X) *
         ((C X - X) ^ k * (C (C 2 * X) * X - 1) ^ P.natDegree +
          ((C (C 2 * X) * X ^ 2 - C 2 * X - C X) ^ k +
           (C (C 2 * X) + X - C (C 2 * X ^ 2) * X) ^ k) *
            (C (C 2 * X) * X - 1) ^ (P.natDegree - k)))

/-- `Qfun` expanded as a sum over the coefficients of `P`. -/
lemma qfun_eq_sum {K : Type*} [Field K] (P : Polynomial K) (x y z : K) :
    Qfun P x y z = ∑ k ∈ Finset.range (P.natDegree + 1), P.coeff k *
      (x * x ^ k + y * y ^ k + z * z ^ k -
        x * y * z * ((x - y) ^ k + (y - z) ^ k + (z - x) ^ k)) := by
  rw [Qfun]
  simp only [eval_eq_sum_range, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Evaluating `PhiPoly` at a pair `(x, y)` with `2xy ≠ 1` gives the cleared
value of `Qfun` at the surface point `(x, y, (x+y)/(2xy−1))`. -/
lemma phiPoly_eval {K : Type*} [Field K] (P : Polynomial K) (x y : K)
    (hxy : 2 * x * y ≠ 1) :
    ((PhiPoly P).map (evalRingHom x)).eval y =
      (2 * x * y - 1) ^ (P.natDegree + 1) *
        Qfun P x y ((x + y) / (2 * x * y - 1)) := by
  have hw : 2 * x * y - 1 ≠ 0 := sub_ne_zero.mpr hxy
  rw [Polynomial.eval_map, PhiPoly, Polynomial.eval₂_finsetSum]
  rw [qfun_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  replace hk : k ≤ P.natDegree := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hz1 :
      (x + y) / (2 * x * y - 1) * ((x + y) / (2 * x * y - 1)) ^ k *
          (2 * x * y - 1) ^ (P.natDegree + 1) =
        (x + y) ^ (k + 1) * (2 * x * y - 1) ^ (P.natDegree - k) := by
    rw [← pow_succ', div_pow, div_mul_eq_mul_div, div_eq_iff (pow_ne_zero _ hw),
      mul_assoc (_ ^ _), ← pow_add (2 * x * y - 1), ← Nat.add_assoc, Nat.sub_add_cancel hk]
  have hz2 :
      ((x + y) / (2 * x * y - 1)) * (x - y) ^ k * (2 * x * y - 1) ^ (P.natDegree + 1) =
        (x + y) * (x - y) ^ k * (2 * x * y - 1) ^ P.natDegree := by
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_eq_iff hw,
      pow_succ]
    ring
  have hyz : y - (x + y) / (2 * x * y - 1) = (2 * x * y ^ 2 - x - 2 * y) / (2 * x * y - 1) := by
    rw [eq_div_iff hw, sub_mul, div_mul_cancel₀ _ hw]
    ring
  have hzx : (x + y) / (2 * x * y - 1) - x = (2 * x + y - 2 * x ^ 2 * y) / (2 * x * y - 1) := by
    rw [eq_div_iff hw, sub_mul, div_mul_cancel₀ _ hw]
    ring
  have hz3 :
      ((x + y) / (2 * x * y - 1)) * (y - (x + y) / (2 * x * y - 1)) ^ k *
          (2 * x * y - 1) ^ (P.natDegree + 1) =
        (x + y) * (2 * x * y ^ 2 - x - 2 * y) ^ k * (2 * x * y - 1) ^ (P.natDegree - k) := by
    rw [hyz, div_pow, mul_div_assoc', div_mul_eq_mul_div, div_eq_iff (pow_ne_zero _ hw),
      div_mul_eq_mul_div, div_mul_eq_mul_div, div_eq_iff hw,
      mul_assoc (_ * _ ^ _), ← pow_succ, mul_assoc (_ * _ ^ _), ← pow_add, ← Nat.add_assoc, Nat.sub_add_cancel hk]
  have hz4 :
       ((x + y) / (2 * x * y - 1)) * ((x + y) / (2 * x * y - 1) - x) ^ k *
          (2 * x * y - 1) ^ (P.natDegree + 1) =
         (x + y) * (2 * x + y - 2 * x ^ 2 * y) ^ k * (2 * x * y - 1) ^ (P.natDegree - k) := by
    rw [hzx, div_pow, mul_div_assoc', div_mul_eq_mul_div, div_eq_iff (pow_ne_zero _ hw),
      div_mul_eq_mul_div, div_mul_eq_mul_div, div_eq_iff hw,
      mul_assoc (_ * _ ^ _), ← pow_succ, mul_assoc (_ * _ ^ _), ← pow_add, ← Nat.add_assoc, Nat.sub_add_cancel hk]
  simp only [eval₂_mul, eval₂_add, eval₂_sub, eval₂_pow, eval₂_C, eval₂_X, eval₂_one,
    coe_evalRingHom, eval_C, eval_X, eval_mul, eval_pow, eval_ofNat]
  linear_combination
    (P.coeff k) * (x * y * (hz2 + hz3 + hz4) - hz1)

/-- If `Qfun P` vanishes at every nonzero real triple on the surface `2xyz = x+y+z`,
then `PhiPoly P` is the zero polynomial. This is the "real dimension two" argument:
a bivariate polynomial vanishing on a cofinite union of points is zero. -/
lemma phiPoly_eq_zero (P : Polynomial ℝ)
    (hQ : ∀ x y z : ℝ, x ≠ 0 → y ≠ 0 → z ≠ 0 → 2 * x * y * z = x + y + z →
      Qfun P x y z = 0) :
    PhiPoly P = 0 := by
  have h1 : ∀ x : ℝ, x ≠ 0 → (PhiPoly P).map (evalRingHom x) = 0 := by
    intro x hx
    apply eq_zero_of_infinite_isRoot
    have hsub : (({(0 : ℝ), -x, (2 * x)⁻¹} : Finset ℝ) : Set ℝ)ᶜ ⊆
        {y | ((PhiPoly P).map (evalRingHom x)).IsRoot y} := by
      intro y hy
      have hy0 : y ≠ 0 := fun h => hy (by simp [h])
      have hyx : y ≠ -x := fun h => hy (by simp [h])
      have hxy : 2 * x * y ≠ 1 := by
        intro h
        apply hy
        have : y = (2 * x)⁻¹ := by
          field_simp
          linarith
        simp [this]
      have hw : 2 * x * y - 1 ≠ 0 := sub_ne_zero.mpr hxy
      rw [Set.mem_ofPred_eq, IsRoot.def, phiPoly_eval P x y hxy]
      have hz0 : (x + y) / (2 * x * y - 1) ≠ 0 := by
        apply div_ne_zero _ hw
        intro h
        apply hyx
        linarith
      have hcon : 2 * x * y * ((x + y) / (2 * x * y - 1)) =
          x + y + (x + y) / (2 * x * y - 1) := by
        rw [mul_div_assoc', div_eq_iff hw, add_mul, div_mul_cancel₀ _ hw]
        ring
      rw [hQ x y ((x + y) / (2 * x * y - 1)) hx hy0 hz0 hcon]
      ring
    exact Set.Infinite.mono hsub
      (Set.Finite.infinite_compl (Finset.finite_toSet _))
  apply ext
  intro k
  have h2 : (PhiPoly P).coeff k = 0 := by
    apply eq_zero_of_infinite_isRoot
    have hsub : (({(0 : ℝ)} : Finset ℝ) : Set ℝ)ᶜ ⊆
        {x | ((PhiPoly P).coeff k).IsRoot x} := by
      intro x hx
      have hx0 : x ≠ 0 := fun h => hx (by simp [h])
      rw [Set.mem_ofPred_eq, IsRoot.def]
      have h3 := h1 x hx0
      have h4 : ((PhiPoly P).map (evalRingHom x)).coeff k = 0 := by
        rw [h3]
        simp
      rw [Polynomial.coeff_map] at h4
      simpa [Polynomial.coe_evalRingHom] using h4
    exact Set.Infinite.mono hsub
      (Set.Finite.infinite_compl (Finset.finite_toSet _))
  rw [h2]
  simp

/-- `P` is even: from `PhiPoly P = 0` we get `Qfun P t 0 (-t) = 0` for all real `t`,
hence `t * (P(t) − P(−t)) = 0` for all `t`, so `P.comp (-X) = P`. -/
lemma comp_neg_X_of_phiPoly_eq_zero (P : Polynomial ℝ) (hPhi : PhiPoly P = 0) :
    P.comp (-X) = P := by
  have hG : ∀ t : ℝ, (X * (P.comp (-X) - P)).eval t = 0 := by
    intro t
    have h1 : ((PhiPoly P).map (evalRingHom t)).eval (0 : ℝ) = 0 := by
      rw [hPhi]
      simp
    rw [phiPoly_eval P t 0 (by norm_num : 2 * t * (0 : ℝ) ≠ 1)] at h1
    have h2 : Qfun P t 0 (-t) = 0 := by
      have hw : (2 : ℝ) * t * 0 - 1 = -1 := by ring
      have hz : (t + 0) / (-1 : ℝ) = -t := by ring
      rw [hw, hz] at h1
      exact (mul_eq_zero.mp h1).resolve_left
        (pow_ne_zero _ (by norm_num : (-1 : ℝ) ≠ 0))
    rw [Qfun] at h2
    simp only [eval_mul, eval_X, eval_sub, eval_comp, eval_neg]
    simp only [zero_mul, mul_zero, sub_zero, add_zero] at h2
    linarith [h2]
  have hG0 : X * (P.comp (-X) - P) = 0 := by
    apply eq_zero_of_infinite_isRoot
    exact Set.Infinite.mono (fun t _ => IsRoot.def.mpr (hG t)) Set.infinite_univ
  rcases mul_eq_zero.mp hG0 with hX | hP
  · exact absurd hX X_ne_zero
  · exact eq_of_sub_eq_zero hP

/-- The second finite difference `(X+h)^k + (X−h)^k − 2X^k` has degree at most `k−2`
(in natural subtraction). Expanded via the binomial theorem: the top two terms cancel. -/
lemma Fk_natDegree_le (h : ℂ) (k : ℕ) :
    ((X + C h) ^ k + (X - C h) ^ k - 2 * X ^ k : Polynomial ℂ).natDegree ≤ k - 2 := by
  rcases k with _ | m
  · have e : (X + C h : Polynomial ℂ) ^ 0 + (X - C h) ^ 0 - 2 * X ^ 0 = 0 := by ring
    rw [e]
    simp
  · have key : (X + C h) ^ (m + 1) + (X - C h) ^ (m + 1) - 2 * X ^ (m + 1)
        = ∑ i ∈ Finset.range m,
          C ((h ^ (m + 1 - i) + (-h) ^ (m + 1 - i)) * ((m + 1).choose i : ℂ)) * X ^ i := by
      have e1 := (Polynomial.commute_X (C h)).add_pow (m + 1)
      have e2 : (X - C h : Polynomial ℂ) ^ (m + 1)
          = ∑ i ∈ Finset.range (m + 1 + 1),
            X ^ i * (C (-h)) ^ (m + 1 - i) * ((m + 1).choose i : Polynomial ℂ) := by
        rw [sub_eq_add_neg, ← map_neg]
        exact (Polynomial.commute_X _).add_pow (m + 1)
      rw [e1, e2, ← Finset.sum_add_distrib]
      have g : ∀ i : ℕ, X ^ i * (C h) ^ (m + 1 - i) * ((m + 1).choose i : Polynomial ℂ)
            + X ^ i * (C (-h)) ^ (m + 1 - i) * ((m + 1).choose i : Polynomial ℂ)
          = C ((h ^ (m + 1 - i) + (-h) ^ (m + 1 - i)) * ((m + 1).choose i : ℂ)) * X ^ i := by
        intro i
        rw [← C_pow, ← C_pow, ← map_natCast C, mul_assoc, mul_assoc, ← map_mul, ← map_mul,
          ← mul_add, ← map_add, ← add_mul, (Polynomial.commute_X_pow _ _).eq]
      simp_rw [g]
      simp only [Finset.sum_range_succ]
      have hm : C ((h ^ (m + 1 - m) + (-h) ^ (m + 1 - m)) * ((m + 1).choose m : ℂ)) * X ^ m
          = 0 := by
        have e : m + 1 - m = 1 := by omega
        rw [e, pow_one, pow_one, add_neg_cancel, zero_mul, map_zero, zero_mul]
      have hm1 : C ((h ^ (m + 1 - (m + 1)) + (-h) ^ (m + 1 - (m + 1)))
            * ((m + 1).choose (m + 1) : ℂ)) * X ^ (m + 1)
          = 2 * X ^ (m + 1) := by
        have e : m + 1 - (m + 1) = 0 := tsub_self _
        rw [e, pow_zero, pow_zero, Nat.choose_self, Nat.cast_one, mul_one, one_add_one_eq_two,
          C_ofNat]
      rw [hm, hm1]
      simp only [add_zero, add_sub_cancel_right]
    rw [key]
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro i hi
    have h2 : i < m := Finset.mem_range.mp hi
    exact le_trans (Polynomial.natDegree_C_mul_X_pow_le _ _) (by omega)

/-- The leading coefficient of the second finite difference `(X+h)^k + (X−h)^k − 2X^k`
at degree `k−2` is `k * (k−1) * h²`. -/
lemma Fk_coeff (h : ℂ) (k : ℕ) :
    ((X + C h) ^ k + (X - C h) ^ k - 2 * X ^ k : Polynomial ℂ).coeff (k - 2) =
      (k : ℂ) * ((k : ℂ) - 1) * h ^ 2 := by
  rcases k with _ | m
  · have e : (X + C h : Polynomial ℂ) ^ 0 + (X - C h) ^ 0 - 2 * X ^ 0 = 0 := by ring
    rw [e]
    simp
  · have key : (X + C h) ^ (m + 1) + (X - C h) ^ (m + 1) - 2 * X ^ (m + 1)
        = ∑ i ∈ Finset.range m,
          C ((h ^ (m + 1 - i) + (-h) ^ (m + 1 - i)) * ((m + 1).choose i : ℂ)) * X ^ i := by
      have e1 := (Polynomial.commute_X (C h)).add_pow (m + 1)
      have e2 : (X - C h : Polynomial ℂ) ^ (m + 1)
          = ∑ i ∈ Finset.range (m + 1 + 1),
            X ^ i * (C (-h)) ^ (m + 1 - i) * ((m + 1).choose i : Polynomial ℂ) := by
        rw [sub_eq_add_neg, ← map_neg]
        exact (Polynomial.commute_X _).add_pow (m + 1)
      rw [e1, e2, ← Finset.sum_add_distrib]
      have g : ∀ i : ℕ, X ^ i * (C h) ^ (m + 1 - i) * ((m + 1).choose i : Polynomial ℂ)
            + X ^ i * (C (-h)) ^ (m + 1 - i) * ((m + 1).choose i : Polynomial ℂ)
          = C ((h ^ (m + 1 - i) + (-h) ^ (m + 1 - i)) * ((m + 1).choose i : ℂ)) * X ^ i := by
        intro i
        rw [← C_pow, ← C_pow, ← map_natCast C, mul_assoc, mul_assoc, ← map_mul, ← map_mul,
          ← mul_add, ← map_add, ← add_mul, (Polynomial.commute_X_pow _ _).eq]
      simp_rw [g]
      simp only [Finset.sum_range_succ]
      have hm : C ((h ^ (m + 1 - m) + (-h) ^ (m + 1 - m)) * ((m + 1).choose m : ℂ)) * X ^ m
          = 0 := by
        have e : m + 1 - m = 1 := by omega
        rw [e, pow_one, pow_one, add_neg_cancel, zero_mul, map_zero, zero_mul]
      have hm1 : C ((h ^ (m + 1 - (m + 1)) + (-h) ^ (m + 1 - (m + 1)))
            * ((m + 1).choose (m + 1) : ℂ)) * X ^ (m + 1)
          = 2 * X ^ (m + 1) := by
        have e : m + 1 - (m + 1) = 0 := tsub_self _
        rw [e, pow_zero, pow_zero, Nat.choose_self, Nat.cast_one, mul_one, one_add_one_eq_two,
          C_ofNat]
      rw [hm, hm1]
      simp only [add_zero, add_sub_cancel_right]
    rw [key]
    simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, Finset.sum_ite_eq]
    by_cases hm : m = 0
    · subst hm
      simp
    · have hmem : m + 1 - 2 ∈ Finset.range m := by
        rw [Finset.mem_range]
        omega
      rw [if_pos hmem]
      have hexp : m + 1 - (m + 1 - 2) = 2 := by omega
      rw [hexp]
      have hch : (m + 1).choose (m + 1 - 2) = (m + 1).choose 2 := Nat.choose_symm (by omega)
      rw [hch]
      have hchoose : ((m + 1).choose 2 : ℂ) = ((m + 1 : ℕ) : ℂ) * ((m : ℕ) : ℂ) / 2 := by
        rw [Nat.choose_two_right,
          Nat.cast_div_charZero (Nat.even_mul_pred_self _).two_dvd,
          Nat.cast_mul, Nat.cast_sub (Nat.le_add_left 1 m), Nat.cast_one, Nat.cast_add,
          Nat.cast_one]
        ring
      rw [hchoose, neg_sq]
      simp only [Nat.cast_add, Nat.cast_one]
      ring

/-- `PhiPoly` commutes with mapping the reals into the complexes. -/
lemma phiPoly_map_ofReal (P : Polynomial ℝ) :
    (PhiPoly P).map (mapRingHom Complex.ofRealHom) =
      PhiPoly (P.map Complex.ofRealHom) := by
  have hinj := Complex.ofReal_injective
  rw [PhiPoly, PhiPoly, natDegree_map_eq_of_injective hinj, ← coe_mapRingHom, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp [coe_mapRingHom, Polynomial.map_C, Polynomial.map_X, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_one,
    Polynomial.map_ofNat, Polynomial.coeff_map]

/-- The degree bound: if `PhiPoly P = 0` and `P` is even, then `P.natDegree ≤ 2`.
The proof passes to complex polynomials and evaluates `Qfun` at the surface point
`(x, h, -h)` with `h² = −1/2`, obtaining that the second finite difference of `P` at
`h` is constant; comparing leading coefficients then forces `deg P ≤ 2`. -/
lemma natDegree_le_two (P : Polynomial ℝ) (hP0 : P ≠ 0) (hPhi : PhiPoly P = 0)
    (hEven : P.comp (-X) = P) :
    P.natDegree ≤ 2 := by
  classical
  obtain ⟨h, hh⟩ : ∃ h : ℂ, h ^ 2 = -1 / 2 := by
    refine ⟨Complex.I * (Real.sqrt 2 / 2 : ℝ), ?_⟩
    rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, div_pow,
      Real.sq_sqrt zero_le_two]
    push_cast
    norm_num
  have hne : h ≠ 0 := fun h0 => by rw [h0] at hh; norm_num at hh
  set Pc : Polynomial ℂ := P.map Complex.ofRealHom with hPc
  have hEvenC : Pc.comp (-X) = Pc := by
    have h1 : (P.comp (-X)).map Complex.ofRealHom = Pc := by rw [hEven, hPc]
    rw [Polynomial.map_comp] at h1
    simpa [Polynomial.map_neg, Polynomial.map_X] using h1
  have hPhiC : PhiPoly Pc = 0 := by
    rw [← phiPoly_map_ofReal, hPhi]
    simp
  have hD : ∀ x : ℂ, x ≠ -h → Qfun Pc x h (-h) = 0 := by
    intro x hx
    have hxy : 2 * x * h ≠ 1 := by
      contrapose! hx with hbad
      have h2 : x * (2 * h) = 1 := by linear_combination hbad
      have h3 : (-h) * (2 * h) = 1 := by linear_combination -2 * hh
      rw [eq_inv_of_mul_eq_one_left h2]
      exact (eq_inv_of_mul_eq_one_left h3).symm
    have h1 := phiPoly_eval Pc x h hxy
    rw [hPhiC, Polynomial.map_zero, eval_zero] at h1
    have hz : (x + h) / (2 * x * h - 1) = -h := by
      rw [div_eq_iff (sub_ne_zero.mpr hxy)]
      linear_combination 2 * x * hh
    rw [hz] at h1
    exact (mul_eq_zero.mp h1.symm).resolve_left (pow_ne_zero _ (sub_ne_zero.mpr hxy))
  set D : Polynomial ℂ := X * Pc + C (h * Pc.eval h) + C ((-h) * Pc.eval (-h)) -
    X * C (h * (-h)) * (Pc.comp (X - C h) + C (Pc.eval (h - (-h))) +
      Pc.comp (C (-h) - X)) with hDdef
  have hDeval : ∀ x : ℂ, D.eval x = Qfun Pc x h (-h) := by
    intro x
    simp only [hDdef, Qfun, eval_mul, eval_add, eval_sub, eval_C, eval_X, eval_comp]
    ring
  have hD0 : D = 0 := by
    apply eq_zero_of_infinite_isRoot
    have hsub : ((({-h} : Finset ℂ) : Set ℂ)ᶜ) ⊆ {x | D.IsRoot x} := by
      intro x hx
      have hx' : x ≠ -h := fun hb => hx (by simp [hb])
      rw [Set.mem_ofPred_eq, IsRoot.def, hDeval]
      exact hD x hx'
    exact Set.Infinite.mono hsub (Set.Finite.infinite_compl (Finset.finite_toSet _))
  rw [hDdef] at hD0
  have hev : Pc.eval (-h) = Pc.eval h := by
    have h1 : (Pc.comp (-X)).eval h = Pc.eval h := by rw [hEvenC]
    simpa [eval_comp] using h1
  have hcomp : Pc.comp (C (-h) - X) = Pc.comp (X + C h) := by
    have h2 : (-X : Polynomial ℂ).comp (X + C h) = -(X + C h) := by
      rw [neg_comp, X_comp]
    rw [Polynomial.C_neg, neg_sub_left, ← h2, ← comp_assoc, hEvenC]
  have hconst : C (h * Pc.eval h) + C ((-h) * Pc.eval h) = (0 : Polynomial ℂ) := by
    rw [← Polynomial.C_add]
    simp
  have hhalf : h * (-h) = 1 / 2 := by linear_combination -hh
  rw [sub_neg_eq_add, ← two_mul, hev, hcomp, hhalf] at hD0
  -- hD0 : X * Pc + C (h*eh) + C ((-h)*eh) - X * C (1/2) * (comp(X−Ch) + C (eval (2h)) + comp(X+Ch)) = 0
  have hD1 : X * Pc = X * C (1 / 2 : ℂ) *
      (Pc.comp (X - C h) + C (Pc.eval (2 * h)) + Pc.comp (X + C h)) := by
    linear_combination hD0 - hconst
  have hD2 : Pc = C (1 / 2 : ℂ) *
      (Pc.comp (X - C h) + C (Pc.eval (2 * h)) + Pc.comp (X + C h)) := by
    have hX : X * (Pc - C (1 / 2 : ℂ) *
        (Pc.comp (X - C h) + C (Pc.eval (2 * h)) + Pc.comp (X + C h))) = 0 := by
      linear_combination hD1
    rcases mul_eq_zero.mp hX with hX0 | hP'
    · exact absurd hX0 X_ne_zero
    · exact eq_of_sub_eq_zero hP'
  have hD3 : 2 * Pc =
      Pc.comp (X - C h) + C (Pc.eval (2 * h)) + Pc.comp (X + C h) := by
    have twoC : (2 : Polynomial ℂ) * C (1 / 2 : ℂ) = 1 := by
      rw [← Polynomial.C_ofNat, ← map_mul]
      norm_num
    have h4 : (2 : Polynomial ℂ) * Pc = (2 : Polynomial ℂ) * (C (1 / 2 : ℂ) *
        (Pc.comp (X - C h) + C (Pc.eval (2 * h)) + Pc.comp (X + C h))) := by
      conv_lhs => rw [hD2]
    rw [← mul_assoc, twoC, one_mul] at h4
    exact h4
  have hE : Pc.comp (X + C h) + Pc.comp (X - C h) - 2 * Pc = C (-Pc.eval (2 * h)) := by
    rw [Polynomial.C_neg]
    linear_combination -hD3
  -- coefficient comparison
  by_contra hlt
  have hlt : 2 < P.natDegree := lt_of_not_ge hlt
  set n := P.natDegree with hn
  have hnPc : Pc.natDegree = n := by
    rw [hPc, hn, natDegree_map_eq_of_injective Complex.ofReal_injective]
  have hcoeff0 : (Pc.comp (X + C h) + Pc.comp (X - C h) - 2 * Pc).coeff (n - 2) = 0 := by
    rw [hE]
    simp [Polynomial.coeff_C, Nat.sub_ne_zero_iff_lt.mpr hlt]
  have hterm : ∀ k : ℕ,
      (C (Pc.coeff k) * (X + C h) ^ k + C (Pc.coeff k) * (X - C h) ^ k -
        (2 : Polynomial ℂ) * (C (Pc.coeff k) * X ^ k)).coeff (n - 2) =
      Pc.coeff k * ((X + C h) ^ k + (X - C h) ^ k - 2 * X ^ k).coeff (n - 2) := by
    intro k
    rw [← Polynomial.C_ofNat]
    simp only [coeff_add, coeff_sub, coeff_C_mul]
    ring
  have hcoeff : (Pc.comp (X + C h) + Pc.comp (X - C h) - 2 * Pc).coeff (n - 2) =
      (P.leadingCoeff : ℂ) * (n : ℂ) * ((n : ℂ) - 1) * h ^ 2 := by
    rw [Pc.as_sum_support_C_mul_X_pow]
    simp only [Polynomial.sum_comp, Polynomial.mul_comp, Polynomial.pow_comp,
      Polynomial.X_comp, Polynomial.C_comp, Finset.mul_sum]
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, Polynomial.finsetSum_coeff]
    have hnmem : n ∈ Pc.support := by
      rw [Polynomial.mem_support_iff]
      have h1 : Pc ≠ 0 := by
        rw [hPc]
        exact (Polynomial.map_ne_zero_iff Complex.ofReal_injective).mpr hP0
      rw [← hnPc]
      exact Polynomial.leadingCoeff_ne_zero.mpr h1
    rw [Finset.sum_eq_single_of_mem n hnmem]
    · rw [hterm, hPc, Polynomial.coeff_map, Fk_coeff h n]
      simp only [Complex.ofRealHom_eq_coe]
      rw [show (P.leadingCoeff : ℂ) = (P.coeff n : ℂ) from rfl]
      ring
    · intro k hk hkn
      have hkle : k ≤ n := by
        rw [Polynomial.mem_support_iff] at hk
        have h2 := Polynomial.le_natDegree_of_ne_zero hk
        rw [hnPc] at h2
        exact h2
      rw [hterm]
      have hF0 : ((X + C h) ^ k + (X - C h) ^ k - 2 * X ^ k : Polynomial ℂ).coeff (n - 2) = 0 := by
        apply Polynomial.coeff_eq_zero_of_natDegree_lt
        have h1 := Fk_natDegree_le h k
        have h2 : k ≤ n - 1 := by omega
        omega
      rw [hF0]
      ring
  rw [hcoeff] at hcoeff0
  have hcn : (P.leadingCoeff : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Polynomial.leadingCoeff_ne_zero.mpr hP0)
  have hn0 : (n : ℂ) ≠ 0 := by
    norm_cast
    omega
  have hn1 : (n : ℂ) - 1 ≠ 0 := by
    apply sub_ne_zero.mpr
    norm_cast
    omega
  have hh0 : h ^ 2 ≠ 0 := by
    rw [hh]
    norm_num
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero hcn hn0) hn1) hh0) hcoeff0

snip end

problem usa2019_p6 (P : Polynomial ℝ) :
    P ∈ SolutionSet ↔
    ∀ x y z : ℝ, x ≠ 0 → y ≠ 0 → z ≠ 0 → 2 * x * y * z = x + y + z →
      P.eval x / (y * z) + P.eval y / (z * x) + P.eval z / (x * y) =
        P.eval (x - y) + P.eval (y - z) + P.eval (z - x) := by
  constructor
  · -- Easy direction: every `P = c • (X² + 3)` works.
    rintro ⟨c, rfl⟩ x y z hx hy hz h
    simp only [eval_mul, eval_add, eval_pow, eval_X, eval_C, eval_ofNat]
    field_simp
    linear_combination
      h * (3 * c - c * ((x - y) ^ 2 + 3 + ((y - z) ^ 2 + 3) + ((z - x) ^ 2 + 3))) / 2
  · -- Hard direction.
    intro h
    by_cases hP0 : P = 0
    · subst hP0
      exact ⟨0, by simp⟩
    have hQ : ∀ x y z : ℝ, x ≠ 0 → y ≠ 0 → z ≠ 0 → 2 * x * y * z = x + y + z →
        Qfun P x y z = 0 := by
      intro x y z hx hy hz hc
      have h1 := h x y z hx hy hz hc
      rw [Qfun]
      field_simp [hx, hy, hz] at h1
      linarith [h1]
    have hPhi : PhiPoly P = 0 := phiPoly_eq_zero P hQ
    have hEven : P.comp (-X) = P := comp_neg_X_of_phiPoly_eq_zero P hPhi
    have hdeg : P.natDegree ≤ 2 := natDegree_le_two P hP0 hPhi hEven
    -- `P` has degree at most 2, so write it out explicitly.
    have hsum : ∀ m : ℕ, P.natDegree ≤ m →
        P = ∑ i ∈ Finset.range (m + 1), C (P.coeff i) * X ^ i := by
      intro m hm
      conv_lhs => rw [P.as_sum_range_C_mul_X_pow]
      apply Finset.sum_subset
      · exact Finset.range_subset_range.mpr (Nat.add_le_add_right hm 1)
      · intro i hi1 hi2
        have h4 : ¬ i < P.natDegree + 1 := fun hb => hi2 (Finset.mem_range.mpr hb)
        have h3 : P.natDegree < i := Nat.lt_of_succ_le (Nat.le_of_not_lt h4)
        simp [Polynomial.coeff_eq_zero_of_natDegree_lt h3]
    have hP2 := hsum 2 hdeg
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero] at hP2
    -- evenness forces the linear coefficient to vanish
    have hc1 : P.coeff 1 = 0 := by
      have h1 := congrArg (fun q => q.coeff 1) hEven
      rw [hP2] at h1
      simp only [add_comp, mul_comp, pow_comp, X_comp, coeff_add] at h1
      norm_num at h1
      linarith [h1]
    -- evaluate the functional equation at `(1, 1, 2)`
    have h112 := h 1 1 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    rw [hP2, hc1] at h112
    simp only [eval_add, eval_mul, eval_pow, eval_X, eval_C] at h112
    norm_num at h112
    have hc0 : P.coeff 0 = 3 * P.coeff 2 := by linarith [h112]
    refine ⟨P.coeff 2, ?_⟩
    rw [hP2, hc1, hc0]
    rw [mul_add, ← Polynomial.C_ofNat, ← map_mul]
    norm_num
    ring

end Usa2019P6
