/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity.Basic
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Olympiad 1989, Problem 3

Let $n$ and $k$ be positive integers and let $S$ be a set of $n$ points in
the plane such that
  (i) no three points of $S$ are collinear, and
  (ii) for each point $P$ of $S$ there are at least $k$ points of $S$
       equidistant from $P$.
Prove that $k < \frac{1}{2} + \sqrt{2n}$.
-/

namespace Imo1989P3

abbrev Pt := EuclideanSpace ℝ (Fin 2)

snip begin

open scoped InnerProductSpace

/-- If `P` and `Q` are both equidistant from `A` and `B`, then `P - Q` is
orthogonal to `B - A`. -/
lemma inner_sub_eq_zero_of_dist_eq {A B P Q : Pt} (hP : dist P A = dist P B)
    (hQ : dist Q A = dist Q B) : ⟪P - Q, B - A⟫_ℝ = 0 := by
  have hsq : ∀ X : Pt, dist X A = dist X B →
      ‖X‖ ^ 2 - 2 * ⟪X, A⟫_ℝ + ‖A‖ ^ 2 = ‖X‖ ^ 2 - 2 * ⟪X, B⟫_ℝ + ‖B‖ ^ 2 := by
    intro X hX
    rw [dist_eq_norm, dist_eq_norm] at hX
    have hsqx : ‖X - A‖ ^ 2 = ‖X - B‖ ^ 2 := by rw [hX]
    rwa [norm_sub_sq_real, norm_sub_sq_real] at hsqx
  have h1 := hsq P hP
  have h2 := hsq Q hQ
  simp only [inner_sub_left, inner_sub_right]
  linear_combination (h1 - h2) / 2

/-- Three points that are all equidistant from two distinct points `A`, `B`
are collinear (they lie on the perpendicular bisector of `A` and `B`,
which is a line). -/
lemma collinear_of_dist_eq {A B : Pt} (hAB : A ≠ B) {p₁ p₂ p₃ : Pt} (h₁₂ : p₁ ≠ p₂)
    (h1 : dist p₁ A = dist p₁ B) (h2 : dist p₂ A = dist p₂ B)
    (h3 : dist p₃ A = dist p₃ B) :
    Collinear ℝ ({p₁, p₂, p₃} : Set Pt) := by
  have hv : B - A ≠ 0 := sub_ne_zero.mpr hAB.symm
  have hu20 : p₂ - p₁ ≠ 0 := sub_ne_zero.mpr h₁₂.symm
  have hu2mem : p₂ - p₁ ∈ (ℝ ∙ (B - A))ᗮ :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
      (inner_eq_zero_symm.mp (inner_sub_eq_zero_of_dist_eq h2 h1))
  have hu3mem : p₃ - p₁ ∈ (ℝ ∙ (B - A))ᗮ :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
      (inner_eq_zero_symm.mp (inner_sub_eq_zero_of_dist_eq h3 h1))
  haveI : Fact (Module.finrank ℝ Pt = 1 + 1) := ⟨by rw [finrank_euclideanSpace_fin]⟩
  have hfin : Module.finrank ℝ (ℝ ∙ (B - A))ᗮ = 1 :=
    Submodule.finrank_orthogonal_span_singleton hv
  have heq : (ℝ ∙ (B - A))ᗮ = ℝ ∙ (p₂ - p₁) :=
    eq_span_singleton_of_mem_of_finrank_eq_one hfin hu2mem hu20
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp (heq ▸ hu3mem)
  rw [collinear_iff_of_mem (Set.mem_insert p₁ _)]
  refine ⟨p₂ -ᵥ p₁, fun p hp => ?_⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl
  · exact ⟨0, by simp⟩
  · exact ⟨1, by simp⟩
  · refine ⟨r, ?_⟩
    rw [vsub_eq_sub, vadd_eq_add, hr, sub_add_cancel]

snip end

problem imo1989_p3 (n k : ℕ) (hn : 0 < n) (hk : 0 < k)
    (S : Finset Pt)
    (hcard : S.card = n)
    (hcol : ∀ p₁ ∈ S, ∀ p₂ ∈ S, ∀ p₃ ∈ S,
              p₁ ≠ p₂ → p₁ ≠ p₃ → p₂ ≠ p₃ → ¬ Collinear ℝ {p₁, p₂, p₃})
    (hequi : ∀ P ∈ S, ∃ (r : ℝ) (T : Finset Pt),
               T ⊆ S ∧ k ≤ T.card ∧ ∀ Q ∈ T, dist P Q = r) :
    (k : ℝ) < 1 / 2 + Real.sqrt (2 * n) := by
  classical
  set P2 := S.powersetCard 2 with hP2
  set R := (S ×ˢ P2).filter (fun p => ∃ r, ∀ Q ∈ p.2, dist p.1 Q = r) with hR
  -- Geometric key fact: at most two points of `S` are equidistant from two
  -- distinct points `A`, `B`, since such points lie on the perpendicular
  -- bisector of `A` and `B` and no three points of `S` are collinear.
  have card_eqi_le_two : ∀ {A B : Pt}, A ≠ B →
      (S.filter (fun P => dist P A = dist P B)).card ≤ 2 := by
    intro A B hAB
    by_contra hcon
    push Not at hcon
    have h1lt : 1 < (S.filter (fun P => dist P A = dist P B)).card := by omega
    obtain ⟨p₁, p₂, hp₁, hp₂, h₁₂⟩ := Finset.one_lt_card_iff.mp h1lt
    have hp₂e : p₂ ∈ (S.filter (fun P => dist P A = dist P B)).erase p₁ :=
      Finset.mem_erase.mpr ⟨h₁₂.symm, hp₂⟩
    have hpos :
        0 < (((S.filter (fun P => dist P A = dist P B)).erase p₁).erase p₂).card := by
      rw [Finset.card_erase_of_mem hp₂e, Finset.card_erase_of_mem hp₁]
      omega
    obtain ⟨p₃, hp₃⟩ := Finset.card_pos.mp hpos
    simp only [Finset.mem_erase] at hp₃
    obtain ⟨h₃₂, h₃₁, hp₃F⟩ := hp₃
    obtain ⟨hp₁S, h1⟩ := Finset.mem_filter.mp hp₁
    obtain ⟨hp₂S, h2⟩ := Finset.mem_filter.mp hp₂
    obtain ⟨hp₃S, h3⟩ := Finset.mem_filter.mp hp₃F
    exact hcol p₁ hp₁S p₂ hp₂S p₃ hp₃S h₁₂ h₃₁.symm h₃₂.symm
      (collinear_of_dist_eq hAB h₁₂ h1 h2 h3)
  -- Lower bound: `n * k.choose 2 ≤ R.card` by counting, for each `P ∈ S`,
  -- the pairs of points equidistant from `P`.
  have hlow : n * k.choose 2 ≤ R.card := by
    have key : ∀ P ∈ S, k.choose 2 ≤ (R.filter (fun q => q.1 = P)).card := by
      intro P hP
      obtain ⟨r, T, hTS, hkT, hT⟩ := hequi P hP
      have hsub : ((T.powersetCard 2).image (Prod.mk P)) ⊆ R.filter (fun q => q.1 = P) := by
        intro q hq
        obtain ⟨U, hU, rfl⟩ := Finset.mem_image.mp hq
        rw [Finset.mem_powersetCard] at hU
        rw [Finset.mem_filter, hR, Finset.mem_filter, Finset.mem_product]
        refine ⟨⟨⟨hP, ?_⟩, ⟨r, ?_⟩⟩, rfl⟩
        · exact Finset.mem_powersetCard.mpr ⟨hU.1.trans hTS, hU.2⟩
        · intro Q hQ
          exact hT Q (hU.1 hQ)
      calc k.choose 2 ≤ T.card.choose 2 := Nat.choose_le_choose 2 hkT
        _ = (T.powersetCard 2).card := (Finset.card_powersetCard 2 T).symm
        _ = ((T.powersetCard 2).image (Prod.mk P)).card :=
            (Finset.card_image_of_injOn (fun U _ V _ h => (Prod.mk_inj.mp h).2)).symm
        _ ≤ (R.filter (fun q => q.1 = P)).card := Finset.card_le_card hsub
    have hfib : R.card = ∑ P ∈ S, (R.filter (fun q => q.1 = P)).card :=
      Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (fun q hq => by
        rw [Finset.mem_coe, hR, Finset.mem_filter, Finset.mem_product] at hq
        exact Finset.mem_coe.mpr hq.1.1)
    have hsum : ∑ P ∈ S, k.choose 2 = n * k.choose 2 := by
      rw [Finset.sum_const, hcard, smul_eq_mul]
    rw [hfib, ← hsum]
    exact Finset.sum_le_sum (fun P hP => key P hP)
  -- Upper bound: `R.card ≤ 2 * n.choose 2` by counting, for each pair of
  -- points of `S`, the points of `S` equidistant from them (at most two).
  have hup : R.card ≤ 2 * n.choose 2 := by
    have key2 : ∀ U ∈ P2, (R.filter (fun q => q.2 = U)).card ≤ 2 := by
      intro U hU
      rw [hP2, Finset.mem_powersetCard] at hU
      obtain ⟨_hUS, hU2⟩ := hU
      obtain ⟨A, B, hAB, rfl⟩ := Finset.card_eq_two.mp hU2
      have hsub : ((R.filter (fun q => q.2 = {A, B})).image Prod.fst) ⊆
          S.filter (fun P => dist P A = dist P B) := by
        intro P hP
        obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hP
        rw [Finset.mem_filter] at hq ⊢
        obtain ⟨hqR, hq2⟩ := hq
        rw [hR, Finset.mem_filter, Finset.mem_product] at hqR
        obtain ⟨⟨hqS, -⟩, r, hr⟩ := hqR
        refine ⟨hqS, ?_⟩
        have hA : A ∈ q.2 := by rw [hq2]; exact Finset.mem_insert_self A {B}
        have hB : B ∈ q.2 := by
          rw [hq2]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self B)
        rw [hr A hA, hr B hB]
      calc (R.filter (fun q => q.2 = {A, B})).card
          = ((R.filter (fun q => q.2 = {A, B})).image Prod.fst).card :=
            (Finset.card_image_of_injOn (fun q hq q' hq' hqq' => by
              simp only [Finset.mem_coe, Finset.mem_filter] at hq hq'
              exact Prod.ext_iff.mpr ⟨hqq', hq.2.trans hq'.2.symm⟩)).symm
        _ ≤ (S.filter (fun P => dist P A = dist P B)).card := Finset.card_le_card hsub
        _ ≤ 2 := card_eqi_le_two hAB
    have hfib2 : R.card = ∑ U ∈ P2, (R.filter (fun q => q.2 = U)).card :=
      Finset.card_eq_sum_card_fiberwise (f := Prod.snd) (fun q hq => by
        rw [Finset.mem_coe, hR, Finset.mem_filter, Finset.mem_product] at hq
        exact Finset.mem_coe.mpr hq.1.2)
    rw [hfib2]
    calc ∑ U ∈ P2, (R.filter (fun q => q.2 = U)).card ≤ ∑ _U ∈ P2, 2 :=
          Finset.sum_le_sum (fun U hU => key2 U hU)
      _ = 2 * n.choose 2 := by
          rw [Finset.sum_const, hP2, Finset.card_powersetCard, hcard, smul_eq_mul]
          ring
  have hmain : n * k.choose 2 ≤ 2 * n.choose 2 := le_trans hlow hup
  -- Turn the combinatorial inequality into `k * (k - 1) ≤ 2 * (n - 1)` over ℝ.
  have hchoose2 : ∀ m : ℕ, 1 ≤ m → (2 : ℝ) * (m.choose 2 : ℝ) = m * (m - 1) := by
    intro m hm
    have h : 2 * m.choose 2 = m * (m - 1) := by
      have h2 := Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self m)
      rw [Nat.choose_two_right]
      omega
    calc (2 : ℝ) * (m.choose 2 : ℝ) = ((2 * m.choose 2 : ℕ) : ℝ) := by norm_cast
      _ = ((m * (m - 1) : ℕ) : ℝ) := by rw [h]
      _ = m * (m - 1) := by rw [Nat.cast_mul, Nat.cast_sub hm, Nat.cast_one]
  have hmain' : (n : ℝ) * (k.choose 2 : ℝ) ≤ 2 * (n.choose 2 : ℝ) := by
    exact_mod_cast hmain
  have hk2 : (k : ℝ) * (k - 1) ≤ 2 * (n - 1) := by
    have h1 := hchoose2 k hk
    have h2 := hchoose2 n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have h3 : (n : ℝ) * (k * (k - 1)) ≤ n * (2 * (n - 1)) := by
      calc (n : ℝ) * (k * (k - 1)) = n * (2 * (k.choose 2 : ℝ)) := by rw [h1]
        _ = 2 * (n * (k.choose 2 : ℝ)) := by ring
        _ ≤ 2 * (2 * (n.choose 2 : ℝ)) := mul_le_mul_of_nonneg_left hmain' (by norm_num)
        _ = n * (2 * (n - 1)) := by rw [h2]; ring
    exact le_of_mul_le_mul_left h3 hnpos
  -- If `k ≥ 1/2 + √(2n)`, then `k * (k - 1) ≥ 2n - 1/4`, a contradiction.
  by_contra hnot
  push Not at hnot
  have hs : (0 : ℝ) ≤ Real.sqrt (2 * n) := Real.sqrt_nonneg _
  have h1 : Real.sqrt (2 * n) ≤ (k : ℝ) - 1 / 2 := by linarith
  have h2 : (Real.sqrt (2 * n)) ^ 2 ≤ ((k : ℝ) - 1 / 2) ^ 2 := pow_le_pow_left₀ hs h1 2
  rw [Real.sq_sqrt (by positivity)] at h2
  nlinarith [hk2, h2]

end Imo1989P3
