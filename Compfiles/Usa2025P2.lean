/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Tactic
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Algebra] }

/-!
# USA Mathematical Olympiad 2025, Problem 2

Let `n > k ≥ 1` be integers. Let `P(x) ∈ ℝ[x]` be a polynomial of degree `n` with no
repeated roots and `P(0) ≠ 0`. Suppose that for any real numbers `a₀, a₁, ..., aₖ` such
that the polynomial `aₖxᵏ + ··· + a₁x + a₀` divides `P(x)`, the product `a₀a₁···aₖ` is
zero. Prove that `P(x)` has a nonreal root.
-/

namespace Usa2025P2

open Polynomial Finset

snip begin

/-- The coefficients of an iterated formal derivative are the shifted coefficients of
the original polynomial, up to a natural-number factor. -/
lemma coeff_iterate_derivative_factor (F : ℝ[X]) (j m : ℕ) :
    ∃ N : ℕ, (derivative^[j] F).coeff m = F.coeff (m + j) * N := by
  induction j generalizing m with
  | zero => exact ⟨1, by simp [Function.iterate_zero_apply]⟩
  | succ j ih =>
    rw [Function.iterate_succ_apply', coeff_derivative]
    obtain ⟨N, hN⟩ := ih (m + 1)
    refine ⟨N * (m + 1), ?_⟩
    rw [hN, Nat.cast_mul, show m + (j + 1) = m + 1 + j by omega]
    push_cast
    ring

/-- Over the reals (characteristic zero), differentiation lowers the degree of a
nonconstant polynomial by exactly one. -/
lemma natDegree_derivative_sub_one (F : ℝ[X]) (hF : F.natDegree ≠ 0) :
    F.derivative.natDegree = F.natDegree - 1 := by
  refine le_antisymm (natDegree_derivative_le F) (le_natDegree_of_ne_zero ?_)
  have hF0 : F ≠ 0 := by rintro rfl; simp at hF
  rw [coeff_derivative, show F.natDegree - 1 + 1 = F.natDegree by omega]
  have e2 : (↑(F.natDegree - 1) : ℝ) + 1 = F.natDegree := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]; ring
  rw [e2]
  exact mul_ne_zero (by rw [coeff_natDegree]; exact leadingCoeff_ne_zero.mpr hF0)
    (Nat.cast_ne_zero.mpr hF)

/-- The degree of an iterated formal derivative, as long as it is nonzero. -/
lemma natDegree_iterate_derivative_eq (F : ℝ[X]) (j : ℕ) (hj : j ≤ F.natDegree) :
    (derivative^[j] F).natDegree = F.natDegree - j := by
  induction j with
  | zero => simp [Function.iterate_zero_apply]
  | succ j ih =>
    have hjj : j ≤ F.natDegree := by omega
    rw [Function.iterate_succ_apply',
      natDegree_derivative_sub_one _ (by rw [ih hjj]; omega), ih hjj]
    omega

/-- **Rolle's theorem**: if a real polynomial has all of its roots real and distinct,
then so does its derivative. -/
lemma good_derivative {F : ℝ[X]}
    (h : F.roots.Nodup ∧ Multiset.card F.roots = F.natDegree) :
    F.derivative.roots.Nodup ∧ Multiset.card F.derivative.roots = F.derivative.natDegree := by
  obtain ⟨hnd, hcard⟩ := h
  by_cases hm : F.natDegree ≤ 1
  · -- `F'` is (at most) a nonzero constant or zero; either way it has no roots.
    have hdeg : F.derivative.natDegree = 0 :=
      Nat.le_zero.mp ((natDegree_derivative_le F).trans (Nat.sub_le_sub_right hm 1))
    have hc0 : Multiset.card F.derivative.roots = 0 :=
      Nat.le_zero.mp ((card_roots' _).trans_eq hdeg)
    rw [Multiset.card_eq_zero.mp hc0]
    exact ⟨Multiset.nodup_zero, by rw [Multiset.card_zero]; exact hdeg.symm⟩
  · push Not at hm
    have hF0 : F ≠ 0 := by rintro rfl; simp at hm
    have hdeg : F.derivative.natDegree = F.natDegree - 1 :=
      natDegree_derivative_sub_one F (by omega)
    have hF'0 : F.derivative ≠ 0 := by
      intro hz; rw [hz, natDegree_zero] at hdeg; omega
    set l := F.roots.sort (· ≤ ·) with hl
    have hlen : l.length = F.natDegree := by rw [hl, Multiset.length_sort, hcard]
    have hpair : l.Pairwise (· ≤ ·) := Multiset.pairwise_sort _ _
    have hlnd : l.Nodup := Multiset.coe_nodup.mp (by rw [hl, Multiset.sort_eq]; exact hnd)
    -- Between two consecutive roots of `F`, Rolle's theorem gives a root of `F'`.
    have hrolle : ∀ i : Fin (F.natDegree - 1), ∃ c,
        c ∈ Set.Ioo (l.get ⟨i, by omega⟩) (l.get ⟨i + 1, by omega⟩) ∧
          F.derivative.eval c = 0 := by
      intro i
      have hlt : (⟨i.val, by omega⟩ : Fin l.length) < ⟨i.val + 1, by omega⟩ := by
        rw [Fin.lt_def]; simp
      have hne : l.get ⟨i.val, by omega⟩ ≠ l.get ⟨i.val + 1, by omega⟩ := by
        intro hget
        have hij := hlnd.get_inj_iff.mp hget
        exact absurd hij (by rw [Fin.ext_iff]; omega)
      have hab : l.get ⟨i.val, by omega⟩ < l.get ⟨i.val + 1, by omega⟩ :=
        lt_of_le_of_ne (hpair.rel_get_of_lt hlt) hne
      have heval : ∀ x ∈ l, F.eval x = 0 := fun x hx =>
        IsRoot.def.mp ((mem_roots hF0).mp ((Multiset.mem_sort _).mp hx))
      obtain ⟨c, hc, hderiv⟩ := exists_hasDerivAt_eq_zero hab F.continuous.continuousOn
        (by show F.eval _ = F.eval _
            rw [heval _ (List.get_mem _ _), heval _ (List.get_mem _ _)])
        (fun x _ => F.hasDerivAt x)
      exact ⟨c, hc, hderiv⟩
    choose c hc using hrolle
    -- The Rolle points are pairwise distinct, since they lie in disjoint intervals.
    have hcinj : Function.Injective c := by
      refine StrictMono.injective (fun i j hij => ?_)
      have h1 : c i < l.get ⟨i.val + 1, by omega⟩ := (hc i).1.2
      have h2 : l.get ⟨j.val, by omega⟩ < c j := (hc j).1.1
      have h3 : l.get ⟨i.val + 1, by omega⟩ ≤ l.get ⟨j.val, by omega⟩ := by
        have hij' : i.val + 1 ≤ j.val := by rw [Fin.lt_def] at hij; omega
        rcases Nat.eq_or_lt_of_le hij' with he | hlt
        · have hfin : (⟨i.val + 1, by omega⟩ : Fin l.length) = ⟨j.val, by omega⟩ :=
            Fin.ext he
          exact le_of_eq (congrArg l.get hfin)
        · exact hpair.rel_get_of_lt (by rw [Fin.lt_def]; omega)
      linarith
    have hsub : (Finset.univ.image c) ⊆ F.derivative.roots.toFinset := by
      intro x hx
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
      rw [Multiset.mem_toFinset, mem_roots hF'0, IsRoot.def]
      exact (hc i).2
    have hcard_img : (Finset.univ.image c).card = F.natDegree - 1 := by
      rw [Finset.card_image_of_injective _ hcinj, Finset.card_univ, Fintype.card_fin]
    have hle1 : F.natDegree - 1 ≤ Multiset.card F.derivative.roots := by
      rw [← hcard_img]
      exact (Finset.card_le_card hsub).trans (Multiset.card_le_card (Multiset.dedup_le _))
    have hle2 : Multiset.card F.derivative.roots ≤ F.natDegree - 1 :=
      hdeg ▸ card_roots' _
    have hcard' : Multiset.card F.derivative.roots = F.natDegree - 1 :=
      le_antisymm hle2 hle1
    refine ⟨?_, by rw [hcard', hdeg]⟩
    have h1 : F.derivative.roots.toFinset.card = F.natDegree - 1 :=
      le_antisymm ((Multiset.card_le_card (Multiset.dedup_le _)).trans hcard'.le)
        (hcard_img ▸ Finset.card_le_card hsub)
    have h2 : Multiset.dedup F.derivative.roots = F.derivative.roots := by
      apply Multiset.eq_of_le_of_card_le (Multiset.dedup_le _)
      have h3 : Multiset.card F.derivative.roots =
          Multiset.card (Multiset.dedup F.derivative.roots) := by
        rw [show Multiset.card (Multiset.dedup F.derivative.roots) =
          F.derivative.roots.toFinset.card from rfl, hcard', h1]
      exact h3.le
    exact Multiset.dedup_eq_self.mp h2

/-- Iterated derivatives of a polynomial with distinct real roots still have distinct
real roots. -/
lemma good_iterate (F : ℝ[X]) (j : ℕ)
    (h : F.roots.Nodup ∧ Multiset.card F.roots = F.natDegree) :
    (derivative^[j] F).roots.Nodup ∧
      Multiset.card (derivative^[j] F).roots = (derivative^[j] F).natDegree := by
  induction j with
  | zero => exact h
  | succ j ih => rw [Function.iterate_succ_apply']; exact good_derivative ih

/-- If the coefficients of `x^(t-1)` and `x^t` of `R` both vanish, then `X^2` divides
the `(t-1)`-st derivative of `R`. -/
lemma dvd_X_pow_two_iterate_derivative (R : ℝ[X]) {t : ℕ} (ht : 1 ≤ t)
    (h0 : R.coeff (t - 1) = 0) (h1 : R.coeff t = 0) :
    (X : ℝ[X]) ^ 2 ∣ derivative^[t - 1] R := by
  rw [X_pow_dvd_iff]
  intro d hd
  obtain ⟨N, hN⟩ := coeff_iterate_derivative_factor R (t - 1) d
  interval_cases d
  · rw [hN, show 0 + (t - 1) = t - 1 by omega, h0, zero_mul]
  · rw [hN, show 1 + (t - 1) = t by omega, h1, zero_mul]

/-- A nonzero polynomial divisible by `X^2` has `0` as a multiple root, so its root
multiset is duplicate-free nowhere. -/
lemma not_nodup_roots_of_X_pow_two_dvd {F : ℝ[X]} (hF : F ≠ 0)
    (h : (X : ℝ[X]) ^ 2 ∣ F) : ¬ F.roots.Nodup := by
  intro hnd
  have h2 : 2 ≤ F.rootMultiplicity 0 := by
    rw [le_rootMultiplicity_iff hF]
    simpa using h
  rw [Multiset.nodup_iff_count_le_one] at hnd
  have hcnt := hnd 0
  rw [count_roots] at hcnt
  omega

/-- The combinatorial heart of the problem. Let `s` be a set of `k + 1` real numbers
(with `k ≥ 1`). Then it is impossible that for every `i ∈ s`, the polynomial
`∏_{r ∈ s \ {i}} (X - r)` has a zero coefficient among the positions `1, ..., k - 1`.
Indeed, two such polynomials would share the position `t` of a zero coefficient
(pigeonhole), forcing the common sub-product `∏_{r ∈ s \ {i₁, i₂}} (X - r)` to have two
consecutive zero coefficients, contradicting Rolle's theorem. -/
lemma core_pigeonhole {k : ℕ} (hk : 1 ≤ k) {s : Finset ℝ} (hscard : s.card = k + 1)
    (H : ∀ i ∈ s, ∃ t ∈ Finset.Icc 1 (k - 1),
      (∏ r ∈ s.erase i, (X - C r)).coeff t = 0) :
    False := by
  have H' : ∀ i : s, ∃ t : ℕ, t ∈ Finset.Icc 1 (k - 1) ∧
      (∏ r ∈ s.erase (i : ℝ), (X - C r)).coeff t = 0 := fun i => H i i.2
  choose f hf using H'
  set g : ℝ → ℕ := fun i => if h : i ∈ s then f ⟨i, h⟩ else 0 with hg
  have hgc : (Finset.Icc 1 (k - 1)).card < s.card := by
    rw [Nat.card_Icc, hscard]; omega
  obtain ⟨i1, hi1, i2, hi2, hne, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hgc (f := g) fun i hi => by
      rw [show g i = f ⟨i, hi⟩ from dif_pos hi]; exact (hf ⟨i, hi⟩).1
  have hg1 : g i1 = f ⟨i1, hi1⟩ := dif_pos hi1
  have hg2 : g i2 = f ⟨i2, hi2⟩ := dif_pos hi2
  have hft : f ⟨i1, hi1⟩ = f ⟨i2, hi2⟩ := by rw [← hg1, ← hg2]; exact heq
  set t := f ⟨i1, hi1⟩ with ht_def
  have ht : t ∈ Finset.Icc 1 (k - 1) := (hf ⟨i1, hi1⟩).1
  have hc1 : (∏ r ∈ s.erase i1, (X - C r)).coeff t = 0 := (hf ⟨i1, hi1⟩).2
  have hc2 : (∏ r ∈ s.erase i2, (X - C r)).coeff t = 0 := by
    have hft2 : f ⟨i1, hi1⟩ = f ⟨i2, hi2⟩ := by rw [← ht_def]; exact hft
    rw [ht_def, hft2]; exact (hf ⟨i2, hi2⟩).2
  rw [Finset.mem_Icc] at ht
  -- The common sub-product over `s ∖ {i₁, i₂}`.
  set u := (s.erase i1).erase i2 with hu
  set R := ∏ r ∈ u, (X - C r) with hR
  have hucard : u.card = k - 1 := by
    rw [hu, Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hne.symm, hi2⟩),
      Finset.card_erase_of_mem hi1, hscard]
    omega
  have hRdeg : R.natDegree = k - 1 := by
    rw [hR, natDegree_prod_of_monic _ (fun r => X - C r) fun r _ => monic_X_sub_C r]
    simp [hucard]
  have hRgood : R.roots.Nodup ∧ Multiset.card R.roots = R.natDegree := by
    have e1 : R.roots = u.val := by rw [hR, roots_prod_X_sub_C]
    rw [e1]
    exact ⟨u.nodup, by rw [← Finset.card_def, hucard, hRdeg]⟩
  -- Factorizations of the two "omit one root" products.
  have hi2u : i2 ∉ u := by rw [hu]; exact Finset.notMem_erase i2 _
  have hi1u : i1 ∉ u := by
    rw [hu, Finset.mem_erase]
    push Not
    exact fun _ => Finset.notMem_erase i1 _
  have hfac1 : (∏ r ∈ s.erase i1, (X - C r)) = (X - C i2) * R := by
    have h : s.erase i1 = insert i2 u := by
      rw [hu]
      exact (Finset.insert_erase (Finset.mem_erase.mpr ⟨hne.symm, hi2⟩)).symm
    rw [h, hR, Finset.prod_insert hi2u]
  have hfac2 : (∏ r ∈ s.erase i2, (X - C r)) = (X - C i1) * R := by
    have h1 : s.erase i2 = insert i1 ((s.erase i2).erase i1) :=
      (Finset.insert_erase (Finset.mem_erase.mpr ⟨hne, hi1⟩)).symm
    have h2 : (s.erase i2).erase i1 = u := by
      rw [hu]
      ext x
      simp only [Finset.mem_erase]
      tauto
    rw [h1, h2, hR, Finset.prod_insert hi1u]
  -- The vanishing-coefficient equations: `coeff t` of `(X - c) * R` is
  -- `R.coeff (t - 1) - c * R.coeff t`.
  have hcoeff : ∀ c : ℝ, ∀ m : ℕ, 1 ≤ m →
      ((X - C c) * R).coeff m = R.coeff (m - 1) - c * R.coeff m := by
    intro c m hm
    simp [sub_mul, ← coeff_X_mul R (m-1), ← (Nat.sub_eq_iff_eq_add hm).mp rfl]
  have he1 : R.coeff (t - 1) = i2 * R.coeff t := by
    have h := hc1
    rw [hfac1, hcoeff i2 t ht.1] at h
    linarith
  have he2 : R.coeff (t - 1) = i1 * R.coeff t := by
    have h := hc2
    rw [hfac2, hcoeff i1 t ht.1] at h
    linarith
  -- Since `i₁ ≠ i₂`, both `R.coeff t` and `R.coeff (t - 1)` vanish.
  have hRt : R.coeff t = 0 := by
    have hsub : (i2 - i1) * R.coeff t = 0 := by
      have h : i2 * R.coeff t = i1 * R.coeff t := by rw [← he1, ← he2]
      rw [sub_mul, sub_eq_zero]
      exact h
    rcases mul_eq_zero.mp hsub with h | h
    · exact absurd (sub_eq_zero.mp h) (Ne.symm hne)
    · exact h
  have hRt1 : R.coeff (t - 1) = 0 := by rw [hRt] at he1; simpa using he1
  -- So `X^2` divides the `(t-1)`-st derivative of `R`, contradicting Rolle's theorem.
  have hX2 : (X : ℝ[X]) ^ 2 ∣ derivative^[t - 1] R :=
    dvd_X_pow_two_iterate_derivative R ht.1 hRt1 hRt
  have hGood := good_iterate R (t - 1) hRgood
  have hG0 : derivative^[t - 1] R ≠ 0 := by
    have hd := natDegree_iterate_derivative_eq R (t - 1) (by rw [hRdeg]; omega)
    intro hz
    rw [hz, natDegree_zero, hRdeg] at hd
    omega
  exact not_nodup_roots_of_X_pow_two_dvd hG0 hX2 hGood.1

/-- If every complex root of a squarefree real polynomial `P` is real, then the real
roots of `P` are distinct and there are `deg P` many of them (i.e. `P` splits over
`ℝ`). -/
lemma roots_real_aux {P : ℝ[X]} (hP : P ≠ 0) (hsq : Squarefree P)
    (h : ∀ z : ℂ, aeval z P = 0 → z.im = 0) :
    P.roots.Nodup ∧ Multiset.card P.roots = P.natDegree := by
  have hsep : P.Separable := PerfectField.separable_iff_squarefree.mpr hsq
  have hnodup : P.roots.Nodup := nodup_roots hsep
  refine ⟨hnodup, ?_⟩
  set P' := P.map (algebraMap ℝ ℂ) with hP'
  have hinj : Function.Injective (algebraMap ℝ ℂ) := RingHom.injective _
  have hP'0 : P' ≠ 0 := map_ne_zero hP
  have hnodup' : P'.roots.Nodup := nodup_roots hsep.map
  have him : ∀ z ∈ P'.roots, z.im = 0 := by
    intro z hz
    apply h z
    rw [mem_roots hP'0, IsRoot.def] at hz
    rw [aeval_def, ← eval_map]
    exact hz
  have hroots : P.roots = P'.roots.map Complex.re := by
    refine (Multiset.Nodup.ext hnodup (hnodup'.map_on fun x hx y hy hxy =>
      Complex.ext hxy (by rw [him x hx, him y hy]))).mpr fun r => ?_
    rw [mem_roots hP, IsRoot.def, Multiset.mem_map]
    constructor
    · intro hr
      refine ⟨algebraMap ℝ ℂ r, ?_, ?_⟩
      · rw [mem_roots hP'0, IsRoot.def]
        show (P.map (algebraMap ℝ ℂ)).eval (algebraMap ℝ ℂ r) = 0
        rw [eval_map, ← aeval_def, aeval_algebraMap_apply,
          show aeval r P = P.eval r by rw [aeval_def, Algebra.algebraMap_self, eval₂_id],
          hr, map_zero]
      · simp [Complex.coe_algebraMap]
    · rintro ⟨z, hz, rfl⟩
      have hze : P'.eval z = 0 := IsRoot.def.mp ((mem_roots hP'0).mp hz)
      have hzr : z = algebraMap ℝ ℂ z.re := by
        refine Complex.ext ?_ ?_ <;> simp [Complex.coe_algebraMap, him z hz]
      rw [hzr] at hze
      have hze' : (P.map (algebraMap ℝ ℂ)).eval (algebraMap ℝ ℂ z.re) = 0 := hze
      rw [eval_map, ← aeval_def, aeval_algebraMap_apply] at hze'
      have hz0 : aeval z.re P = 0 := hinj (by rw [map_zero]; exact hze')
      rwa [show aeval z.re P = P.eval z.re by
        rw [aeval_def, Algebra.algebraMap_self, eval₂_id]] at hz0
  calc Multiset.card P.roots = Multiset.card (P'.roots.map Complex.re) := by rw [hroots]
    _ = Multiset.card P'.roots := Multiset.card_map _ _
    _ = P'.natDegree := splits_iff_card_roots.mp (IsAlgClosed.splits P')
    _ = P.natDegree := natDegree_map_eq_of_injective hinj P

snip end

problem usa2025_p2 (n k : ℕ) (hn : k < n) (hk : 1 ≤ k) (P : ℝ[X])
    (hdeg : P.natDegree = n) (hsq : Squarefree P) (h0 : P.eval 0 ≠ 0)
    (H : ∀ a : Fin (k + 1) → ℝ, (∑ i, C (a i) * X ^ (i : ℕ)) ∣ P → ∏ i, a i = 0) :
    ∃ z : ℂ, aeval z P = 0 ∧ z.im ≠ 0 := by
  have hP : P ≠ 0 := by rintro rfl; simp at hdeg; omega
  -- Suppose for contradiction that `P` has no nonreal root.
  by_contra hcon
  push Not at hcon
  obtain ⟨hnodup, hcard⟩ := roots_real_aux hP hsq hcon
  rw [hdeg] at hcard
  -- The finset of real roots of `P` has `n` elements, none of which is `0`.
  set f := P.roots.toFinset with hf
  have hfcard : f.card = n := by
    rw [hf, Multiset.toFinset_card_of_nodup hnodup, hcard]
  have hf0 : 0 ∉ f := by
    rw [hf, Multiset.mem_toFinset, mem_roots hP, IsRoot.def]
    exact h0
  -- Pick any `k + 1` of the roots (the reduction to `n = k + 1`).
  obtain ⟨s, hs, hscard⟩ :=
    Finset.exists_subset_card_eq (show k + 1 ≤ f.card by omega)
  have hs0 : 0 ∉ s := fun h => hf0 (hs h)
  -- The product over these `k + 1` roots divides `P`.
  have hQdvd : (∏ r ∈ s, (X - C r)) ∣ P := by
    have hsv : s.val ≤ P.roots := by
      have h1 : s.val ≤ f.val := Finset.val_le_iff.mpr hs
      rwa [show f.val = P.roots from hnodup.dedup] at h1
    have h1 : (s.val.map fun r => X - C r).prod ∣ (P.roots.map fun r => X - C r).prod :=
      Multiset.prod_dvd_prod_of_le (Multiset.map_le_map hsv)
    have h2 : (P.roots.map fun r => X - C r).prod ∣ P := by
      refine ⟨C P.leadingCoeff, ?_⟩
      rw [mul_comm]
      exact (C_leadingCoeff_mul_prod_multiset_X_sub_C (by rw [hcard, hdeg])).symm
    rw [Finset.prod_eq_multiset_prod]
    exact h1.trans h2
  -- For every root `i ∈ s`, the product over `s ∖ {i}` has degree `k` and divides
  -- `P`, so the hypothesis gives it a zero coefficient, necessarily at a position
  -- in `{1, ..., k - 1}` (the constant and leading coefficients are nonzero).
  apply core_pigeonhole hk hscard
  intro i hi
  set Qi := ∏ r ∈ s.erase i, (X - C r) with hQi
  have hQidvd : Qi ∣ P :=
    (Finset.prod_dvd_prod_of_subset _ _ _ (Finset.erase_subset i s)).trans hQdvd
  have hQimonic : Qi.Monic := monic_prod_of_monic _ (fun r => X - C r) fun r _ => monic_X_sub_C r
  have hQideg : Qi.natDegree = k := by
    rw [hQi, natDegree_prod_of_monic _ (fun r => X - C r) fun r _ => monic_X_sub_C r]
    simp [Finset.card_erase_of_mem hi, hscard]
  have hQisum : (∑ j : Fin (k + 1), C (Qi.coeff j) * X ^ (j : ℕ)) = Qi := by
    rw [← hQideg]
    exact (Fin.sum_univ_eq_sum_range (fun m => C (Qi.coeff m) * X ^ m) _).trans
      (as_sum_range_C_mul_X_pow Qi).symm
  have hprod := H (fun j => Qi.coeff j) (by rwa [hQisum])
  obtain ⟨j, -, hj⟩ := Finset.prod_eq_zero_iff.mp hprod
  refine ⟨j.val, ?_, hj⟩
  rw [Finset.mem_Icc]
  have hc0 : Qi.coeff 0 ≠ 0 := by
    rw [coeff_zero_eq_eval_zero, hQi, eval_prod, Finset.prod_ne_zero_iff]
    intro r hr
    rw [Finset.mem_erase] at hr
    simp only [eval_sub, eval_X, eval_C]
    exact sub_ne_zero.mpr (ne_of_mem_of_not_mem hr.2 hs0).symm
  have hck : Qi.coeff k ≠ 0 := by
    rw [← hQideg, hQimonic.coeff_natDegree]
    exact one_ne_zero
  have hj0 : j.val ≠ 0 := by
    intro hjv
    rw [show j = ⟨0, by omega⟩ from Fin.ext hjv] at hj
    exact hc0 hj
  have hjk : j.val ≠ k := by
    intro hjv
    rw [show j = ⟨k, by omega⟩ from Fin.ext hjv] at hj
    exact hck hj
  exact ⟨by omega, by have hlt := j.isLt; omega⟩

end Usa2025P2
