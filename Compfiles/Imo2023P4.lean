/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Olympiad 2023, Problem 4

Let x₁, x₂, ... x₂₀₂₃ be distinct positive real numbers.
Define

   aₙ := √((x₁ + x₂ + ... + xₙ)(1/x₁ + 1/x₂ + ... + 1/xₙ)).

Suppose that aₙ is an integer for all n ∈ {1,...,2023}.
Prove that 3034 ≤ a₂₀₂₃.
-/

namespace Imo2023P4

noncomputable def a (x : Finset.Icc 1 2023 → ℝ) (n : Finset.Icc 1 2023) : ℝ :=
  √((∑ i ∈ Finset.univ.filter (· ≤ n), x i) *
    (∑ i ∈ Finset.univ.filter (· ≤ n), (1 / x i)))

snip begin

noncomputable def aa (m : ℕ)
    (x : Finset.Icc 1 (2 * m + 1) → ℝ) (n : Finset.Icc 1 (2 * m + 1)) : ℝ :=
  √((∑ i ∈ Finset.univ.filter (· ≤ n), x i) *
    (∑ i ∈ Finset.univ.filter (· ≤ n), (1 / x i)))

lemma cauchy_schwarz {x1 x2 x3 y1 y2 y3 : ℝ}
    (hx1 : 0 ≤ x1) (hx2 : 0 ≤ x2) (hx3 : 0 ≤ x3)
    (hy1 : 0 ≤ y1) (hy2 : 0 ≤ y2) (hy3 : 0 ≤ y3) :
    (√(x1 * y1) + √(x2 * y2) + √(x3 * y3))^2 ≤
      (x1 + x2 + x3) * (y1 + y2 + y3) := by
  let f : Fin 3 → ℝ
      | 0 => √x1
      | 1 => √x2
      | 2 => √x3

  let g : Fin 3 → ℝ
      | 0 => √y1
      | 1 => √y2
      | 2 => √y3

  have h1 := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ f g
  simp only [f, g, Fin.sum_univ_three] at h1
  have h2 : 0 ≤ √(x1 *y1) + √(x2 * y2) + √(x3 * y3) := by positivity
  rw [Real.sq_sqrt hx1] at h1
  rw [Real.sq_sqrt hx2] at h1
  rw [Real.sq_sqrt hx3] at h1
  rw [Real.sq_sqrt hy1] at h1
  rw [Real.sq_sqrt hy2] at h1
  rw [Real.sq_sqrt hy3] at h1
  rw [←Real.sqrt_mul (show 0 ≤ x1 + x2 + x3 by positivity)] at h1
  rw [←Real.sqrt_mul hx1] at h1
  rw [←Real.sqrt_mul hx2] at h1
  rw [←Real.sqrt_mul hx3] at h1
  have h4 : (√((x1 + x2 + x3) * (y1 + y2 + y3)))^2 = (x1 + x2 + x3) * (y1 + y2 + y3) := by
    refine Real.sq_sqrt ?_
    positivity
  rw [←h4]
  exact pow_le_pow_left₀ h2 h1 2

lemma lemma1 (u : ℝ) (hu : u ≠ 1) (hp : 0 < u) : 2 < u + 1/u := by
  suffices H : 2 * u < (u + 1 / u) * u from
    (mul_lt_mul_iff_of_pos_right hp).mp H
  field_simp
  have h1 : u - 1 ≠ 0 := sub_ne_zero_of_ne hu
  have h2 : 0 < (u - 1)^2 := pow_two_pos_of_ne_zero h1
  linear_combination h2

theorem imo2023_p4_generalized
    (m : ℕ)
    (x : Finset.Icc 1 (2 * m + 1) → ℝ)
    (hxp : ∀ i, 0 < x i)
    (hxi : x.Injective)
    (hxa : ∀ i : Finset.Icc 1 (2 * m + 1), ∃ k : ℤ, aa m x i = k)
    : 3 * m + 1 ≤ aa m x ⟨2 * m + 1, by simp⟩ := by
  -- We follow the "induct-by-two" solution from
  -- https://web.evanchen.cc/exams/IMO-2023-notes.pdf
  induction m with
  | zero =>
    simp only [CharP.cast_eq_zero, mul_zero, zero_add, aa, Nat.mul_zero, Nat.reduceAdd,
               one_div, Real.one_le_sqrt]
    have h1 : Finset.filter (fun x ↦ x ≤ ⟨1, by simp⟩)
                            (Finset.univ (α := {x //x ∈ Finset.Icc 1 1}))
           = Finset.univ (α := {x // x ∈ Finset.Icc 1 1}) := by
      refine Finset.filter_true_of_mem ?h
      intro x hx
      obtain ⟨x, hx1⟩ := x
      rw [Finset.mem_Icc] at hx1
      obtain ⟨hx2, hx3⟩ := hx1
      exact Subtype.mk_le_mk.mpr hx3
    rw [h1]
    have h2 : Finset.univ (α := { x // x ∈ Finset.Icc 1 1 }) = { ⟨1, by simp⟩ } := by decide
    simp only [h2, Finset.sum_singleton, ge_iff_le]
    simp only [Nat.mul_zero, Nat.reduceAdd, Subtype.forall, Finset.Icc_self,
               Finset.mem_singleton] at hxp
    specialize hxp 1 (by simp)
    field_simp
  | succ m ih =>
    let n := 2 * m + 1
    have hn1 : n + 1 ∈ Finset.Icc 1 (2 * (m + 1) + 1) := by
      simp only [Finset.mem_Icc, le_add_iff_nonneg_left, zero_le,
                 add_le_add_iff_right, true_and, n]
      omega
    have hn2 : n + 2 ∈ Finset.Icc 1 (2 * (m + 1) + 1) := by
      simp only [Finset.mem_Icc, le_add_iff_nonneg_left, zero_le,
                 add_le_add_iff_right, true_and, n]
      omega

    let u := √(x ⟨n + 1, hn1⟩ / x ⟨n + 2, hn2⟩)
    have hu : u ≠ 1 := by
      unfold u n
      intro hu
      rw [Real.sqrt_eq_one] at hu
      rw [(div_eq_one_iff_eq (ne_of_lt (hxp _)).symm)] at hu
      replace hu := hxi hu
      simp at hu
    have h1 : (aa (m + 1) x ⟨n + 2, hn2⟩)^2 =
       (√((∑ i ∈ Finset.univ.filter (· ≤ ⟨n + 2, hn2⟩), x i) *
        (∑ i ∈ Finset.univ.filter (· ≤ ⟨n + 2, hn2⟩), (1 / x i))))^2 := by
      unfold aa; rfl
    have h2 : 0 ≤ (∑ i ∈ Finset.univ.filter (· ≤ ⟨n + 2, hn2⟩), x i) *
        (∑ i ∈ Finset.univ.filter (· ≤ ⟨n + 2, hn2⟩), (1 / x i)) := by
      have h3 :
          0 ≤ ∑ i ∈ Finset.filter
                     (fun x ↦ x ≤ ⟨n + 2, hn2⟩) Finset.univ, x i := by
        refine Finset.sum_nonneg ?_
        intro i hi
        specialize hxp i
        exact le_of_lt hxp
      have h4 :
          0 ≤ ∑ i ∈ Finset.filter
                     (fun x ↦ x ≤ ⟨n + 2, hn2⟩) Finset.univ, 1 / x i := by
        refine Finset.sum_nonneg ?_
        intro i hi
        specialize hxp i
        positivity
      exact Left.mul_nonneg h3 h4
    rw [Real.sq_sqrt h2] at h1; clear h2
    have h5 : ⟨n + 2, hn2⟩ ∉
         Finset.filter (fun x ↦ x ≤ ⟨n + 1, hn1⟩)
            Finset.univ (α := Finset.Icc 1 (n + 2)) := by
      intro H
      simp_all only [Subtype.forall, Finset.mem_Icc, ne_eq, Real.sqrt_eq_one,
                     Finset.univ_eq_attach, one_div, Finset.mem_filter,
                     Finset.mem_attach, Subtype.mk_le_mk, add_le_add_iff_left,
                     Nat.not_ofNat_le_one, and_false, u, n]
    have h6 : Finset.filter (fun x ↦ x ≤ ⟨n + 2, hn2⟩)
                Finset.univ (α := Finset.Icc 1 (2 * (m + 1) + 1)) =
              Finset.cons _ (Finset.filter (fun x ↦ x ≤ ⟨n + 1, hn1⟩)
                 Finset.univ (α := Finset.Icc 1 (2 * (m + 1) + 1))) h5 := by
      clear ih
      ext y
      constructor
      · intro hy
        simp only [Finset.univ_eq_attach, Finset.mem_filter,
                   Finset.mem_attach, true_and] at hy
        simp only [Finset.univ_eq_attach, Finset.cons_eq_insert,
                   Finset.mem_insert, Finset.mem_filter,
                   Finset.mem_attach, true_and]
        obtain ⟨y, hy'⟩ := y
        simp only [Subtype.mk_le_mk] at hy
        simp only [Subtype.mk.injEq, Subtype.mk_le_mk]
        omega
      · intro hy
        simp only [Finset.univ_eq_attach, Finset.cons_eq_insert,
                   Finset.mem_insert, Finset.mem_filter,
                   Finset.mem_attach, true_and] at hy
        obtain ⟨y, hy'⟩ := y
        simp only [Subtype.mk.injEq, Subtype.mk_le_mk] at hy
        simp only [Finset.univ_eq_attach, Finset.mem_filter, Finset.mem_attach,
                   Subtype.mk_le_mk, true_and]
        omega
    simp only [h6] at h1
    simp only [Finset.cons_eq_insert, Finset.mem_filter,
               Finset.mem_attach, Subtype.mk_le_mk, add_le_add_iff_left,
               Nat.not_ofNat_le_one, and_false, not_false_eq_true,
               Finset.sum_insert, one_div] at h1

    have h7 : ⟨n + 1, hn1⟩ ∉
         Finset.filter (fun x ↦ x ≤ ⟨n, by simp [n]⟩)
            Finset.univ (α := Finset.Icc 1 (n + 2)) := by
      intro H
      simp_all only [Subtype.forall, Finset.mem_Icc, ne_eq, Real.sqrt_eq_one,
                     Finset.univ_eq_attach, Finset.cons_eq_insert,
                     Finset.mem_filter, Finset.mem_attach, Subtype.mk_le_mk,
                     add_le_iff_nonpos_right, nonpos_iff_eq_zero, one_ne_zero,
                     and_false, u, n]

    have h8 : Finset.filter (fun x ↦ x ≤ ⟨n + 1, hn1⟩)
                Finset.univ (α := Finset.Icc 1 (2 * (m + 1) + 1)) =
              Finset.cons _ (Finset.filter (fun x ↦ x ≤ ⟨n, by simp[n]⟩)
                 Finset.univ (α := Finset.Icc 1 (2 * (m + 1) + 1))) h7 := by
      clear ih
      ext y
      constructor
      · intro hy
        simp only [Finset.univ_eq_attach, Finset.mem_filter,
                   Finset.mem_attach, true_and] at hy
        simp only [Finset.univ_eq_attach, Finset.cons_eq_insert,
                   Finset.mem_insert, Finset.mem_filter,
                   Finset.mem_attach, true_and]
        obtain ⟨y, hy'⟩ := y
        simp only [Subtype.mk_le_mk] at hy
        simp only [Subtype.mk.injEq, Subtype.mk_le_mk]
        omega
      · intro hy
        simp only [Finset.univ_eq_attach, Finset.cons_eq_insert,
                   Finset.mem_insert, Finset.mem_filter,
                   Finset.mem_attach, true_and] at hy
        obtain ⟨y, hy'⟩ := y
        simp only [Subtype.mk.injEq, Subtype.mk_le_mk] at hy
        simp only [Finset.univ_eq_attach, Finset.mem_filter, Finset.mem_attach,
                   Subtype.mk_le_mk, true_and]
        omega

    simp only [h8] at h1
    clear h6 h8
    simp only [Finset.cons_eq_insert, Finset.mem_filter,
               Finset.mem_attach, Subtype.mk_le_mk, add_le_iff_nonpos_right,
               nonpos_iff_eq_zero, one_ne_zero, and_false, not_false_eq_true,
               Finset.sum_insert] at h1
    rw [←add_assoc, add_comm (x ⟨n + 2, hn2⟩)] at h1
    rw [←add_assoc] at h1
    have hx1 : 0 ≤ x ⟨n + 1, hn1⟩ := le_of_lt (hxp ⟨n + 1, hn1⟩)
    have hx2 : 0 ≤ x ⟨n + 2, hn2⟩ := le_of_lt (hxp ⟨n + 2, hn2⟩)
    have hx3 : 0 ≤ ∑ x_1 ∈ Finset.filter
                    (fun x ↦ x ≤ ⟨n, by simp[n]⟩)
                    Finset.univ, x x_1 := by
      refine Finset.sum_nonneg ?_
      rintro y -
      exact le_of_lt (hxp y)
    have hy1 : 0 ≤ (x ⟨n + 2, hn2⟩)⁻¹ := inv_nonneg_of_nonneg hx2
    have hy2 : 0 ≤ (x ⟨n + 1, hn1⟩)⁻¹ := inv_nonneg_of_nonneg hx1
    have hy3 : 0 ≤ ∑ x_1 ∈ Finset.filter (fun x ↦ x ≤ ⟨n, by simp[n]⟩) Finset.univ, (x x_1)⁻¹ := by
      refine Finset.sum_nonneg ?_
      rintro y hy
      simp only [Finset.mem_filter, Finset.mem_attach, true_and] at hy
      specialize hxp y
      positivity

    have h9 := cauchy_schwarz hx1 hx2 hx3 hy1 hy2 hy3
    clear hx1 hx2 hx3 hy1 hy2 hy3
    rw [←h1] at h9; clear h1
    let x' : { a // a ∈ Finset.Icc 1 (2 * m + 1) } → ℝ :=
      fun ⟨z, hz⟩ ↦ x ⟨z, by simp only [Finset.mem_Icc] at hz ⊢; omega⟩
    let e : { x // x ∈ Finset.Icc 1 (2 * m + 1) } →
            { x // x ∈ Finset.Icc 1 (2 * (m + 1) + 1) }
      | ⟨y, hy⟩ => ⟨y, by simp only [Finset.mem_Icc] at hy ⊢; omega⟩
    have hei : Function.Injective e := by
      intro a b hab
      simp only [e, Subtype.mk.injEq] at hab
      exact Subtype.eq hab
    have h20 {y : ℕ} (hy : y ∈ Finset.Icc 1 (2 * m + 1)) :
        Finset.map ⟨e, hei⟩ (Finset.filter (fun x ↦ x ≤ ⟨y, hy⟩) Finset.univ) =
          Finset.filter
           (fun x ↦ x ≤ ⟨y, by simp only [Finset.mem_Icc] at hy ⊢; omega⟩)
             Finset.univ := by
      ext a
      constructor
      · intro ha
        simp only [Finset.univ_eq_attach, Finset.mem_map, Finset.mem_filter,
                   Finset.mem_attach, true_and, Function.Embedding.coeFn_mk,
                   Subtype.exists, Subtype.mk_le_mk, Finset.mem_Icc,
                   exists_and_left] at ha
        simp only [Finset.univ_eq_attach, Finset.mem_filter, Finset.mem_attach,
                   true_and]
        obtain ⟨aa, haa, haa2, haa3⟩ := ha
        simp only [e] at haa3
        rw [← haa3, Subtype.mk_le_mk]
        exact haa
      · intro ha
        simp only [Finset.univ_eq_attach, Finset.mem_filter, Finset.mem_attach,
                   true_and] at ha
        simp only [Finset.univ_eq_attach, Finset.mem_map, Finset.mem_filter,
                   Finset.mem_attach, true_and, Function.Embedding.coeFn_mk,
                   Subtype.exists, Subtype.mk_le_mk, Finset.mem_Icc,
                   exists_and_left]
        use a
        obtain ⟨a, haa⟩ := a
        simp only [Finset.mem_Icc] at haa hy
        simp only [Subtype.mk_le_mk] at ha
        simp only [exists_prop, and_true]
        omega

    have h10 : √((∑ x_1 ∈ Finset.filter
                  (fun x ↦ x ≤ ⟨n, by simp [n]⟩) Finset.univ, x x_1) *
            ∑ x_1 ∈ Finset.filter (fun x ↦ x ≤ ⟨n, by simp[n]⟩) Finset.univ, (x x_1)⁻¹) = aa m x' ⟨n, by simp[n]⟩ := by
      clear h9 h5 h7
      have hn : n ∈ Finset.Icc 1 (2 * m + 1) := by
        simp only [Finset.mem_Icc, le_refl, and_true, n]
        exact Nat.le_add_left 1 (2 * m)
      unfold aa
      congr 2
      · rw [←h20 hn, Finset.sum_map]
        rfl
      · rw [←h20 hn, Finset.sum_map]
        apply Finset.sum_congr rfl
        intro ii hii
        simp
    rw [h10] at h9; clear h10
    have hxp' : ∀ (i : { x // x ∈ Finset.Icc 1 (2 * m + 1) }), 0 < x' i := by
      rintro ⟨y, hy⟩
      simp only [x']
      have hy' : y ∈ Finset.Icc 1 (2 * (m + 1) + 1) := by
        simp only [Finset.mem_Icc] at hy ⊢
        omega
      exact hxp ⟨y, hy'⟩
    have hxi' : Function.Injective x' := by
      intro a b hab
      simp only [x'] at hab
      specialize hxi hab
      simp only [Subtype.mk.injEq] at hxi
      exact Subtype.eq hxi
    have hxa' : ∀ (i : { x // x ∈ Finset.Icc 1 (2 * m + 1) }),
                    ∃ k : ℤ, aa m x' i = ↑k := by
      rintro ⟨y, hy⟩
      have hy' : y ∈ Finset.Icc 1 (2 * (m + 1) + 1) := by
        simp only [Finset.mem_Icc] at hy ⊢
        omega
      specialize hxa ⟨y, hy'⟩
      obtain ⟨k, hk⟩ := hxa
      use k
      rw [←hk]
      clear h5 h7 h9
      unfold aa
      congr 2
      · rw [←h20 hy, Finset.sum_map]
        rfl
      · rw [←h20 hy, Finset.sum_map]
        rfl
    specialize ih x' hxp' hxi' hxa'
    have hup : 0 < u := by
      unfold u
      simp only [Real.sqrt_pos]
      exact div_pos (hxp ⟨n + 1, hn1⟩) (hxp ⟨n + 2, hn2⟩)
    have huu : 2 < u + 1/u := lemma1 u hu hup
    have h11 : √(x ⟨n + 1, hn1⟩ * (x ⟨n + 2, hn2⟩)⁻¹) +
               √(x ⟨n + 2, hn2⟩ * (x ⟨n + 1, hn1⟩)⁻¹) = u + 1 / u := by
      congr 1
      suffices H: √(x ⟨n + 2, hn2⟩ * (x ⟨n + 1, hn1⟩)⁻¹)  * u = 1 from
        eq_one_div_of_mul_eq_one_left H
      unfold u
      have hp1 : 0 < x ⟨n + 1, hn1⟩ := hxp ⟨n + 1, hn1⟩
      have hp2 : 0 < x ⟨n + 2, hn2⟩ := hxp ⟨n + 2, hn2⟩
      rw [←Real.sqrt_mul (by positivity)]
      field_simp
    rw [h11] at h9; clear h11
    replace h9 : aa m x' ⟨n, by simp[n]⟩ + 2 < aa (m + 1) x ⟨n + 2, hn2⟩ := by
      have h9' : u + 1/u + aa m x' ⟨n, by simp[n]⟩ ≤
          aa (m + 1) x ⟨n + 2, hn2⟩ := by
        have h12 : 0 ≤ aa (m + 1) x ⟨n + 2, hn2⟩ := by
          unfold aa
          exact Real.sqrt_nonneg _
        exact le_of_sq_le_sq h9 h12
      linarith
    simp_rw [show 2 * m + 1 = n from rfl] at ih
    replace h9 : 3 * ↑m + 3 < aa (m + 1) x ⟨n+ 2, hn2⟩ := by linarith
    simp_rw [show n + 2 = 2 * (m + 1) + 1 from rfl] at h9
    specialize hxa ⟨2 * (m + 1) + 1, hn2⟩
    obtain ⟨k, hk⟩ := hxa
    rw [hk] at h9 ⊢
    norm_cast at h9 ⊢

snip end

problem imo2023_p4
    (x : Finset.Icc 1 2023 → ℝ)
    (hxp : ∀ i, 0 < x i)
    (hxi : x.Injective)
    (hxa : ∀ i : Finset.Icc 1 2023, ∃ k : ℤ, a x i = k)
    : 3034 ≤ a x ⟨2023, by simp⟩ := by
  have := imo2023_p4_generalized 1011 x hxp hxi hxa
  convert this
  norm_num

end Imo2023P4
