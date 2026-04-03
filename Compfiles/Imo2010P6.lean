/-
Copyright (c) 2023 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Rydh
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Olympiad 2010, Problem 6

Let a₁, a₂, a₃, ... be a sequence of positive real numbers. Suppose that for some
positive integer s, we have
    aₙ = max{aₖ + aₙ₋ₖ | 1 ≤ k ≤ n − 1}
for all n > s. Prove that there exist positive integers l and N, with l ≤ s and
such that aₙ = aₗ + aₙ₋ₗ for all n ≥ N.
-/

namespace Imo2010P6

noncomputable def rec_max {n : ℕ+} (f : ℕ+ → ℝ) (h : 1 < n) := Finset.max' ((Finset.Icc 1 (n - 1)).image (fun k ↦ f k + f (n - k)))
    (Finset.image_nonempty.mpr (Finset.nonempty_Icc.mpr (PNat.le_sub_one_of_lt h)))

def Rec (s : ℕ+) (f : ℕ+ → ℝ) := ∀ n (h : n > s), f n = rec_max f (PNat.one_lt_of_lt h)

snip begin

variable {a f : ℕ+ → ℝ}
variable {l s n N : ℕ+}

lemma exists_max_ratio (a : ℕ+ → ℝ) (s : ℕ+) :
    ∃ l ∈ Finset.Icc 1 s, ∀ i ∈ Finset.Icc 1 s, a i / (i : ℝ) ≤ a l / (l : ℝ) := by
  have hsne : (Finset.Icc 1 s).Nonempty := ⟨1, by simp [PNat.one_le s]⟩
  simpa using Finset.exists_max_image (Finset.Icc 1 s) (fun i : ℕ+ ↦ a i / (i : ℝ)) hsne

lemma finset_nonempty (n : ℕ+) : (Finset.Icc 1 n).Nonempty := Finset.nonempty_Icc.mpr (PNat.one_le n)

noncomputable def res (a : ℕ+ → ℝ) (l n : ℕ+) : ℝ := a n - (n : ℝ) * (a l / (l : ℝ))

lemma ne_zero_coe (k : ℕ+) : (k : ℝ) ≠ 0 := by positivity

lemma res_nonpos (h : ∀ i ∈ Finset.Icc 1 s, a i / (i : ℝ) ≤ a l / (l : ℝ)) :
    ∀ k ∈ Finset.Icc 1 s, res a l k ≤ 0 := by
  intro k hk
  replace h := h k hk
  set u := a l / (l : ℝ)
  calc
    res a l k = a k - k * u := rfl
    _ = k * (a k / k) - k * u := by nth_rw 1 [← mul_div_cancel₀ (a k) (ne_zero_coe k)]
    _ ≤ k * (a l / l) - k * u := by simpa
    _ = 0 := sub_self (↑↑k * (a l / ↑↑l))

lemma max_of_image {α : Type} {S : Finset α} {f : α → ℝ} {x : ℝ} (h : S.Nonempty) :
    x = (S.image f).max' (Finset.image_nonempty.mpr h) → ∃ i ∈ S, x = f i := by
  intro hx
  rcases Finset.mem_image.mp (Finset.max'_mem (S.image f) (Finset.image_nonempty.mpr h)) with ⟨i, hi, hfi⟩
  exact ⟨i, hi, hx.trans hfi.symm⟩

lemma sum_multiset {α : Finset ℕ+} (S₁ S₂ : Multiset α) (f : ℕ+ → ℝ) :
  ∃ S₃ : Multiset α, (S₁.map f).sum + (S₂.map f).sum = (S₃.map f).sum := by
  use S₁ + S₂
  norm_num

lemma res_expansion (n : ℕ+) (h_res_rec : Rec s (res a l)) :
    ∃ S : Multiset (Finset.Icc 1 s), res a l n = (S.map (res a l)).sum := by
  by_cases hns : n ≤ s
  · use {⟨n, Finset.mem_Icc.mpr ⟨PNat.one_le n, hns⟩⟩}
    simp [res]
  obtain ⟨k, hk, hrec⟩ := max_of_image (finset_nonempty (n-1)) (h_res_rec n (lt_of_not_ge hns))
  have hk_lt_n : k < n := lt_of_le_of_lt (Finset.mem_Icc.mp hk).2 <| by
    rw [← PNat.sub_add_of_lt (PNat.one_lt_of_lt (lt_of_not_ge hns))]
    exact PNat.lt_add_right (n - 1) 1
  have hkn_lt_n : n - k < n := by simpa [PNat.add_sub_of_lt hk_lt_n] using PNat.lt_add_left (n - k) k
  obtain ⟨S₁, hS₁⟩ := res_expansion k (h_res_rec)
  obtain ⟨S₂, hS₂⟩ := res_expansion (n - k) (h_res_rec)
  obtain ⟨S, hS⟩ := sum_multiset S₁ S₂ (res a l)
  use S
  rw [hrec, hS₁, hS₂, hS]
termination_by n

lemma Multiset.sum_nonpos.{u_2} {α : Type u_2} [AddCommGroup α] [Preorder α] {s : Multiset α} [AddLeftMono α] [AddRightMono α] :
    (∀ x ∈ s, x ≤ 0) → s.sum ≤ 0 := by
  intro h
  have hneg : ∀ x ∈ Multiset.map Neg.neg s, 0 ≤ x := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := Multiset.mem_map.mp hx
    rw [← hyx]
    exact neg_nonneg.2 (h y hy)
  have hsum : 0 ≤ -s.sum := by simpa [Multiset.sum_map_neg'] using (Multiset.sum_nonneg hneg)
  exact neg_nonneg.1 hsum

lemma res_bounded_above
    (h_nonpos : ∀ k ∈ Finset.Icc 1 s, res a l k ≤ 0)
    (h_res_rec : Rec s (res a l)) :
    ∀ n, res a l n ≤ 0 := by
  intro n
  obtain ⟨S, hS⟩ := res_expansion n h_res_rec
  rw [hS]
  exact Multiset.sum_nonpos <| by
    intro x hx
    rcases Multiset.mem_map.mp hx with ⟨k, hk, rfl⟩
    simp at hk
    exact h_nonpos k (by grind only)

lemma sub_lt {a b : ℕ+} (h : a < b) : b - a < b := by grind only [PNat.add_sub_of_lt, PNat.lt_add_left]

lemma bounded_below_aux (n : ℕ+) (h_l_le_s : l ≤ s) (h_step_monotone : ∀ k (_ : k + l > s), f k ≤ f (k + l)) :
  ∃ t ∈ (Finset.Icc 1 s), f t ≤ f n := by
  refine PNat.strongInductionOn (p := fun n => ∃ t ∈ (Finset.Icc 1 s), f t ≤ f n) n ?_
  intro m ih
  by_cases hms : m ≤ s
  · exact ⟨m, Finset.mem_Icc.mpr ⟨m.2, hms⟩, Std.IsPreorder.le_refl (f m)⟩
  · simp at hms
    have h'' : l < m := Std.lt_of_le_of_lt h_l_le_s hms
    obtain ⟨t, ht, htf⟩ := ih (m - l) (sub_lt h'')
    grind [PNat.sub_add_of_lt h'']

lemma res_bounded_below (h_l_le_s : l ≤ s) (h_step_monotone : ∀ n (_ : n + l > s), res a l n ≤ res a l (n + l)) :
    ∃ M, ∀ n, -M ≤ res a l n := by
  use ((Finset.Icc 1 s).image (|res a l|)).max' (Finset.image_nonempty.mpr (finset_nonempty s))
  intro n
  obtain ⟨t, ht, htn⟩ := bounded_below_aux n h_l_le_s h_step_monotone
  have := Finset.le_max' ((Finset.Icc 1 s).image |res a l|) |res a l t| (Finset.mem_image_of_mem |res a l| ht)
  linarith [neg_abs_le (res a l t), htn]

lemma finite_bounded_card_multisets {α : Type} {R : Finset α} {N : ℝ} : {S : Multiset R | S.card ≤ N}.Finite := by
  refine ((List.finite_length_le (α := R) (n := Nat.ceil N)).image (fun l : List R => (l : Multiset R))).subset ?_
  intro S hS
  rcases Quotient.exists_rep S with ⟨l, rfl⟩
  refine ⟨l, ?_, rfl⟩
  exact Nat.cast_le.mp (le_trans (by simpa using hS) (Nat.le_ceil N))

lemma sum_filter_eq_zero {α : Type} [DecidableEq α] [AddCommMonoid α] {S : Multiset α} :
    (Multiset.filter (fun x ↦ x = 0) S).sum = 0 := by
  rw [Multiset.filter_eq' S 0]
  simp

lemma pos_of_min_of_abs_ne_zero {α : Type} {R : Finset α} {f : α → ℝ}
    (h : (R.filter (fun i ↦ f i ≠ 0)).Nonempty) :
    0 < ((R.filter (fun i ↦ f i ≠ 0)).image |f|).min' (Finset.image_nonempty.mpr h) := by
  have hmem := Finset.min'_mem ((R.filter (fun i ↦ f i ≠ 0)).image |f|) (Finset.image_nonempty.mpr h)
  obtain ⟨i, hi, hfi⟩ := Finset.mem_image.mp hmem
  rw [← hfi]
  exact abs_pos.mpr (Finset.mem_filter.mp hi).2

lemma map_sum_le_sup_mul_card {α : Type} {S : Multiset α} {f : α → ℝ} {c : ℝ} (h : ∀ s ∈ S, f s ≤ c)
    : (S.map f).sum ≤ c * S.card := by
  have h₁ : ∀ s ∈ S.map f, s ≤ c := by grind only [Multiset.mem_map]
  have h₂ : S.card = (S.map f).card := by simp
  rw [h₂]
  have := Multiset.sum_le_card_nsmul (S.map f) c h₁
  grind

lemma res_expansion_bounded {M : ℝ} {ε : ℝ} (hε : 0 < ε)
    (h_res_rec : Rec s (res a l))
    (hbounded_above : ∀ k ∈ Finset.Icc 1 s, res a l k ≠ 0 → res a l k ≤ -ε)
    (hbounded_below : ∀ k, -M ≤ res a l k) :
    ∃ S : Multiset (Finset.Icc 1 s), res a l n = (S.map (res a l)).sum ∧ S.card ≤ M / ε := by
  obtain ⟨S, hS⟩ := res_expansion n h_res_rec
  let S' : Multiset (Finset.Icc 1 s) := S.filter (fun k ↦ res a l k ≠ 0)
  have hbound : ∀ k ∈ S', res a l k ≤ -ε := fun k hk ↦ hbounded_above k k.2 (Multiset.mem_filter.mp hk).2
  have hsum_eq : (S.map (res a l)).sum = (S'.map (res a l)).sum := by
    rw [← Multiset.sum_filter_add_sum_filter_not (fun x ↦ x = 0)]
    simp [sum_filter_eq_zero]
    rw [Multiset.filter_map]
    rfl
  use S'
  constructor
  · rwa [← hsum_eq]
  have : -M ≤ -ε * S'.card := by
    calc
      -M ≤ res a l n := hbounded_below n
      _ = (S.map (res a l)).sum := hS
      _ = (S'.map (res a l)).sum := hsum_eq
      _ ≤ -ε * S'.card := by
        have := map_sum_le_sup_mul_card hbound (c := -ε)
        simpa
  replace : ε * S'.card ≤ M := by linarith
  exact (le_div_iff₀' hε).mpr this

lemma res_range_finite
    (hbounded_above : ∀ n, res a l n ≤ 0)
    (hbounded_below : ∃ M, ∀ n, -M ≤ res a l n)
    (h_res_rec : Rec s (res a l)) :
    ∃ R : Finset ℝ, ∀ n, res a l n ∈ R := by
  by_cases h_res_zero : ∀ n ∈ (Finset.Icc 1 s), res a l n = 0
  · use {0}
    intro n
    obtain ⟨S, hS⟩ := res_expansion n h_res_rec
    rw [hS]
    simp
    apply Multiset.sum_eq_zero
    intro x hx
    rcases Multiset.mem_map.mp hx with ⟨k, hk, rfl⟩
    exact h_res_zero k k.2
  let S := (Finset.Icc 1 s).filter (fun k ↦ res a l k ≠ 0)
  have hS : S.Nonempty := by
    by_contra hS
    apply h_res_zero
    intro k hk
    by_contra hk0
    exact hS ⟨k, Finset.mem_filter.mpr ⟨hk, hk0⟩⟩
  let ε := (S.image (|res a l|)).min' (Finset.image_nonempty.mpr hS)
  have h_ε_pos : 0 < ε := pos_of_min_of_abs_ne_zero hS
  obtain ⟨M, hM⟩ := hbounded_below
  let R : Finset ℝ := ((finite_bounded_card_multisets (R := Finset.Icc 1 s) (N := M / ε)).image
      (fun S : Multiset (Finset.Icc 1 s) ↦ (S.map (res a l)).sum)).toFinset
  use R
  intro n
  have h_upper : ∀ k ∈ Finset.Icc 1 s, res a l k ≠ 0 → res a l k ≤ -ε := by
    intro k hk h_ne_zero
    have hkS : k ∈ S := Finset.mem_filter.mpr ⟨hk, h_ne_zero⟩
    calc
      res a l k = -|res a l k| := by rw [abs_of_nonpos (hbounded_above k), neg_neg]
      _ ≤ -ε := by
        have : |res a l k| ∈ Finset.image |res a l| S := Finset.mem_image_of_mem |res a l| hkS
        rw [neg_le_neg_iff]
        exact Finset.min'_le (Finset.image |res a l| S) |res a l k| this
  obtain ⟨S', hS'⟩ := res_expansion_bounded h_ε_pos h_res_rec h_upper hM
  rw [hS'.1]
  rw [Set.Finite.mem_toFinset]
  exact ⟨S', hS'.2, rfl⟩

lemma coe_mul_sub {u : ℝ} {n l : ℕ+} (h : l < n) : ↑↑(n - l) * u = n * u - l * u := by
  have hsub_add : ((n - l : ℕ+) : ℝ) + l = n := by exact_mod_cast (PNat.sub_add_of_lt h)
  grind

lemma max_of_image_sub {S : Finset ℕ+} {f : ℕ+ → ℝ} {a : ℝ} (h : S.Nonempty) :
    Finset.max' (Finset.image (fun k ↦ f k - a) S) (Finset.image_nonempty.mpr h) = Finset.max' (Finset.image f S) (Finset.image_nonempty.mpr h) - a := by
  simpa [Finset.image_image, Function.comp, Finset.image_nonempty]
    using (Finset.max'_image (s := Finset.image f S) (f := fun x : ℝ => x - a)
      (hf := by intro x y hxy; linarith) (h := by simp_all only [Finset.image_nonempty]))

lemma res_rec (l : ℕ+) (hrec : Rec s a) : Rec s (res a l) := by
  intro n hn
  have h_one_lt_n : 1 < n := PNat.one_lt_of_lt hn
  set u := a l / (l : ℝ)
  have : rec_max (res a l) h_one_lt_n =
      Finset.max' ((Finset.Icc 1 (n - 1)).image (fun k ↦ a k + a (n - k) - u * n)) (Finset.image_nonempty.mpr (finset_nonempty (n - 1))) := by
    unfold rec_max
    congr 1
    apply Finset.image_congr
    intro k hk
    have hk_lt_n : k < n := lt_of_le_of_lt (Finset.mem_Icc.mp hk).2 <| by
      rw [← PNat.sub_add_of_lt h_one_lt_n]
      exact PNat.lt_add_right (n - 1) 1
    grind only [res, coe_mul_sub]
  rw [this, res, hrec n hn, max_of_image_sub (finset_nonempty (n - 1)), rec_max, mul_comm]

lemma res_l_zero : res a l l = 0 := by
  have hl_pos : (l : ℝ) > 0 := by positivity
  have hlmul : (l : ℝ) * (a l / (l : ℝ)) = a l := by field_simp [hl_pos.ne']
  exact sub_eq_zero_of_eq hlmul.symm

lemma res_step_monotone (hres_rec : Rec s (res a l)) :
    ∀ n (_ : n + l > s), res a l n ≤ res a l (n + l) := by
  intro n hn
  have h_one_lt : 1 < n + l := PNat.one_lt_of_lt hn
  calc
    res a l n = res a l l + res a l n := (add_eq_right.mpr res_l_zero).symm
    _ = res a l l + res a l (n + l - l) := by rw [PNat.add_sub]
    _ ≤ rec_max (res a l) (h_one_lt) := by
      apply Finset.le_max'
      simp
      use l
      constructor
      · grind only [PNat.le_sub_one_of_lt, PNat.lt_add_left]
      · simp
    _ = res a l (n + l) := (hres_rec (n + l) hn).symm

lemma eventually_eq_succ_of_mem_finset_of_monotone {S : Finset ℝ} {K : ℕ+} (h₁ : ∀ k, f k ∈ S) (h₂ : ∀ a b, K < a → a < b → f a ≤ f b)
  : ∃ N, ∀ k > N, f k = f (k + 1) := by
  have hmax : ∃ m > K, ∀ k > K, f k ≤ f m := by
    let g : Set.Ioi K → ℝ := fun k ↦ f k
    have hfinite : (Set.range g).Finite := (Finset.finite_toSet S).subset <| by
      rintro _ ⟨k, rfl⟩
      simpa [g] using h₁ k
    let T := hfinite.toFinset
    have hT_nonempty : T.Nonempty := by
      rw [Set.Finite.toFinset_nonempty]
      exact Set.range_nonempty g
    have hT_mem : ∀ k : Set.Ioi K, g k ∈ T := by
      intro k
      rw [Set.Finite.mem_toFinset hfinite]
      exact Set.mem_range_self k
    have hmax_mem : T.max' hT_nonempty ∈ T := Finset.max'_mem T hT_nonempty
    rw [Set.Finite.mem_toFinset hfinite] at hmax_mem
    obtain ⟨m, hm⟩ := hmax_mem
    refine ⟨m, Set.mem_Ioi.mp m.2, ?_⟩
    intro k hk
    simpa [g, hm] using Finset.le_max' T (g ⟨k, hk⟩) (hT_mem ⟨k, hk⟩)
  obtain ⟨m, hmK, hm⟩ := hmax
  use m
  have heq : ∀ n > m, f n = f m := by
    intro n hm_lt_n
    have hfn_lt_fm : f n ≤ f m := hm n (gt_trans hm_lt_n hmK)
    have hfm_lt_fn : f m ≤ f n := h₂ m n hmK (gt_iff_lt.mp hm_lt_n)
    exact eq_of_le_of_ge hfn_lt_fm hfm_lt_fn
  intro k hk
  have : k + 1 > m := by
    calc
      k + 1 > k := PNat.lt_add_right k 1
      _ > m := hk
  rw [heq k hk, heq (k+1) this]

lemma mono_of_mono_succ_rec (h : ∀ x, s < x → f x ≤ f (x + 1)) (z : ℕ+): ∀ x, s < x → f x ≤ f (x + z) := by
  intro x h_s_lt_x
  by_cases hz : z = 1
  · rw [hz]
    exact h x h_s_lt_x
  · have hz_pred_ne_zero : z.natPred ≠ 0 := by
      intro hz_pred_eq_zero
      apply hz
      simpa [hz_pred_eq_zero] using (PNat.natPred_add_one z).symm
    have hz_pred_pos := Nat.pos_of_ne_zero hz_pred_ne_zero
    let zpred : ℕ+ := ⟨z.natPred, Nat.zero_lt_of_lt hz_pred_pos⟩
    have hs : s < x + zpred := lt_trans h_s_lt_x (PNat.lt_add_right x zpred)
    calc
      f x ≤ f (x + zpred) := mono_of_mono_succ_rec h zpred x h_s_lt_x
      _ ≤ f (x + zpred + 1) := h (x + zpred) hs
      _ = f (x + z) := by
        have hzpred_succ : zpred + 1 = z := by
          apply PNat.coe_injective
          simp [zpred, PNat.natPred_add_one z]
        rw [add_assoc, hzpred_succ]

lemma mono_of_mono_succ (h : ∀ x, s < x → f x ≤ f (x + 1)) : ∀ x y, s < x → x < y → f x ≤ f y := by
  intro x y h_s_lt_x h_x_lt_y
  rw [← PNat.add_sub_of_lt h_x_lt_y]
  exact mono_of_mono_succ_rec h (y - x) x h_s_lt_x

lemma res_eventually_t_step_eq
    (h_range_finite : ∃ S : Finset ℝ, ∀ n, res a l n ∈ S)
    (h_step_monotone : ∀ n (_ : n + l > s), res a l n ≤ res a l (n + l)) :
    ∀ t ∈ Finset.Icc 1 l, ∃ N : ℕ+, ∀ k, t + k * l > N → res a l (t + k * l) = res a l (t + k * l + l) := by
  intro t ht
  obtain ⟨S, hS⟩ := h_range_finite
  let f := fun k ↦ res a l (t + k * l)
  have hf_in_S : ∀ k, f k ∈ S := fun k ↦ Finset.mem_def.mpr (hS (t + k * l))
  have hmono_succ : ∀ x, s < x → f x ≤ f (x + 1) := by
    intro x hx
    have : t + x * l + l > s := by
      rw [gt_iff_lt]
      calc
        s < x := hx
        _ ≤ x * l := (le_mul_iff_one_le_right' x).mpr (PNat.one_le l)
        _ < t + x * l := PNat.lt_add_left (x * l) t
        _ < t + x * l + l := PNat.lt_add_right (t + x * l) l
    simpa [f, add_one_mul, add_assoc] using h_step_monotone (t + x * l) this
  have h : ∃ K, ∀ k > K, f k = f (k + 1) := eventually_eq_succ_of_mem_finset_of_monotone hf_in_S (mono_of_mono_succ hmono_succ)
  obtain ⟨K, hK⟩ := h
  use t + K * l
  intro k h₁
  simp at h₁
  have := hK k (gt_iff_lt.mp h₁)
  simpa [f, add_one_mul, add_assoc]

lemma decompose (h : l < n) : ∃ (t k : ℕ+), t ∈ Finset.Icc 1 l ∧ n = t + k * l := by
  use (PNat.mod n l)
  let k' := n.div l
  have hmod_add_div : n = (n.mod l : ℕ) + (l : ℕ) * k' := by rw [(PNat.mod_add_div n l).symm, mul_comm]
  have hk'_pos : 0 < k' := by
    by_contra hk0
    have hnle : n ≤ l := by
      rw [Nat.eq_zero_of_not_pos hk0, Nat.mul_zero, add_zero] at hmod_add_div
      exact_mod_cast hmod_add_div.trans_le (PNat.mod_le n l).2
    exact (not_le_of_gt h hnle)
  use ⟨k', hk'_pos⟩
  constructor
  · exact Finset.mem_Icc.mpr ⟨PNat.one_le (n.mod l), (PNat.mod_le n l).2⟩
  · apply PNat.coe_injective
    simpa [mul_comm] using hmod_add_div

lemma res_eventually_step_eq
    (ht : ∀ t ∈ Finset.Icc 1 l, ∃ N : ℕ+, ∀ k, t + k * l > N → res a l (t + k * l) = res a l (t + k * l + l)) :
    ∃ N : ℕ+, ∀ n ≥ N, res a l n = res a l (n + l) := by
  choose Nt hNt using ht
  let N := (((Finset.Icc 1 l).attach).image (fun t ↦ Nt t.1 t.2)).max'
    (Finset.image_nonempty.mpr (Finset.attach_nonempty_iff.mpr (finset_nonempty l)))
  use N + l
  intro n hn
  obtain ⟨t, k, ht, hn_eq⟩ := decompose (lt_of_lt_of_le (PNat.lt_add_left l N) (ge_iff_le.mp hn))
  have h : t + k * l > Nt t ht := by
    rw [← hn_eq]
    apply gt_iff_lt.mpr
    calc
      Nt t ht ≤ N := Finset.le_max' _ _ (by
        rw [Finset.mem_image]
        exact ⟨⟨t, ht⟩, Finset.mem_attach _ _, rfl⟩)
      _ < N + l := PNat.lt_add_right N l
      _ ≤ n := ge_iff_le.mpr hn
  have := hNt t (Finset.mem_def.mpr ht) k h
  rwa [← hn_eq] at this

lemma step_eq_of_res_step_eq (hlt : l < n) (h : res a l n = res a l (n - l)) : a n = a l + a (n - l) := by
  have hsum : (n : ℝ) = ((n - l : ℕ+) : ℝ) + (l : ℝ) := by
    have hsum' : (n : ℝ) = (l : ℝ) + ((n - l : ℕ+) : ℝ) := by exact_mod_cast (PNat.add_sub_of_lt hlt).symm
    simpa [add_comm] using hsum'
  have hdef' : a n - (((n - l : ℕ+) : ℝ) * (a l / (l : ℝ)) + l * (a l / (l : ℝ))) =
      a (n - l) - ((n - l : ℕ+) : ℝ) * (a l / (l : ℝ)) := by
    simpa [res, hsum, add_mul, add_assoc, add_left_comm, add_comm] using h
  have hlmul : l * (a l / (l : ℝ)) = a l := mul_div_cancel₀ (a l) (by positivity)
  linarith

lemma eventual_step_eq_of_eventual_res_step_eq
    (hstab : ∀ n ≥ N, res a l n = res a l (n + l)) :
    ∃ N' : ℕ+, ∀ n ≥ N', a n = a l + a (n - l) := by
  use (max N (l + 1)) + l
  intro n hn
  have hlt : l < n := by
    calc
      l < l + 1 := PNat.lt_succ_self l
      _ ≤ max N (l + 1) := le_max_right N (l + 1)
      _ ≤ max N (l + 1) + l := le_of_lt (PNat.lt_add_right (max N (l + 1)) l)
      _ ≤ n := hn
  have h₁ : n - l ≥ N := by
    have hNl : (N : ℕ) + (l : ℕ) ≤ (n : ℕ) := by
      exact_mod_cast calc
        N + l ≤ max N (l + 1) + l := by simp [add_comm]
        _ ≤ n := hn
    change (N : ℕ) ≤ ((n - l : ℕ+) : ℕ)
    rw [PNat.sub_coe, if_pos hlt]
    lia
  have h₂ := (hstab (n - l) h₁).symm
  rw [PNat.sub_add_of_lt hlt] at h₂
  exact step_eq_of_res_step_eq hlt h₂

snip end

problem imo2010_p6 {a : ℕ+ → ℝ} {s : ℕ+} : Rec s a → ∃ l N : ℕ+, (l ≤ s ∧ ∀ n ≥ N, a n = a l + a (n - l)) := by
  intro hrec
  obtain ⟨l, hlmem, hmaxl⟩ := exists_max_ratio a s
  have hls := (Finset.mem_Icc.mp hlmem).2
  have h_res_rec := res_rec l hrec
  have h_res_pos := res_nonpos hmaxl
  have h_step_monotone := res_step_monotone h_res_rec
  have h_bounded_above := res_bounded_above h_res_pos h_res_rec
  have h_bounded_below := res_bounded_below hls h_step_monotone
  have h_range_finite := res_range_finite h_bounded_above h_bounded_below h_res_rec
  have ht_step_eq := res_eventually_t_step_eq h_range_finite h_step_monotone
  obtain ⟨N, hN⟩ := res_eventually_step_eq ht_step_eq
  obtain ⟨N', hN'⟩ := eventual_step_eq_of_eventual_res_step_eq hN
  exact ⟨l, N', hls, hN'⟩

end Imo2010P6
