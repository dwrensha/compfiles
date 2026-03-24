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

snip begin

lemma coe_mul_sub {u : ℝ} {n l : ℕ} (h : l < n) : u * ↑(n - l) = u * n - u * l := by rw [Nat.cast_sub] <;> grind only

lemma max_of_image_sub {α : Type} {S : Finset α} {f : α → ℝ} {a : ℝ} (h : S.Nonempty)
  : Finset.max' (Finset.image (fun k ↦ f k - a) S) (Finset.image_nonempty.mpr h) = Finset.max' (Finset.image f S) (Finset.image_nonempty.mpr h) - a := by
  simpa [Finset.image_image, Function.comp, Finset.image_nonempty]
    using (Finset.max'_image (s := Finset.image f S) (f := fun x : ℝ => x - a)
      (hf := by intro x y hxy; linarith) (h := by simp_all only [Finset.image_nonempty]))

lemma max_of_image {α : Type} {S : Finset α} {f : α → ℝ} {x : ℝ} (h : S.Nonempty) :
    x = (S.image f).max' (Finset.image_nonempty.mpr h) → ∃ i ∈ S, x = f i := by
  intro hx
  obtain ⟨i, hi, hfi⟩ := Finset.mem_image.mp (Finset.max'_mem (S.image f) (Finset.image_nonempty.mpr h))
  use i
  rw [hx]
  exact ⟨hi, hfi.symm⟩

lemma sum_multiset {α : Finset ℕ} (S₁ S₂ : Multiset α) (f : ℕ → ℝ) :
  ∃ S₃ : Multiset α, (S₁.map f).sum + (S₂.map f).sum = (S₃.map f).sum := by
  use S₁ + S₂
  norm_num

lemma aux₂ {n l s : ℕ} (f : ℕ → ℝ) (h₁ : 0 < l) (h₂ : l ≤ s) (h₃ : s < n) (h₄ : ∀ k > s, f (k - l) ≤ f k) :
  ∃ t ∈ (Finset.Icc 1 s), f t ≤ f n := by
  refine Nat.strong_induction_on n ?_ h₃
  intro m ih hm
  by_cases hms : m - l ≤ s
  · exact ⟨m - l, Finset.mem_Icc.mpr ⟨Nat.sub_pos_of_lt (lt_of_le_of_lt h₂ hm), hms⟩, h₄ m hm⟩
  · obtain ⟨t, ht, htf⟩ := ih (m - l) (Nat.sub_lt (Nat.zero_lt_of_lt hm) h₁) (lt_of_not_ge hms)
    exact ⟨t, ht, le_trans htf (h₄ m hm)⟩

lemma finite_bounded_card_multisets {α : Type} {R : Finset α} {N : ℝ} :
    {S : Multiset R | S.card ≤ N}.Finite := by
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
  have hfi_ne : f i ≠ 0 := (Finset.mem_filter.mp hi).2
  rw [← hfi]
  exact abs_pos.mpr hfi_ne

lemma nonempty_of_filter_nonempty {α : Type} {R : Finset α} {f : α → Prop} [DecidablePred f] :
  (R.filter f).Nonempty → R.Nonempty := by
  grind only [= Finset.nonempty_def, = Finset.mem_filter]

lemma max_filter_le_max {α : Type} {R : Finset α} {g : α → ℝ} {f : α → Prop} [DecidablePred f]
    (h : (R.filter f).Nonempty) :
    ((R.filter f).image g).max' (Finset.image_nonempty.mpr h) ≤
      (R.image g).max' (Finset.image_nonempty.mpr (nonempty_of_filter_nonempty h)) := by
  refine Finset.max'_le _ _ _ ?_
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
  exact Finset.le_max' (R.image g) (g i) (Finset.mem_image_of_mem g (Finset.mem_filter.mp hi).1)


lemma eventually_eq_succ_of_mem_finset_of_monotone {S : Finset ℝ} {f : ℕ → ℝ} (h₁ : ∀ k, f k ∈ S) (h₂ : Monotone f)
  : ∃ N > 0, ∀ k > N, f k = f (k + 1) := by
  have hmax : ∃ m, ∀ k, f k ≤ f m := by
    have hrange_finite := (Finset.finite_toSet S).subset (Set.range_subset_iff.mpr h₁)
    let T := hrange_finite.toFinset
    have hfk_mem_T : ∀ k, f k ∈ T := by
      intro k
      rw [Set.Finite.mem_toFinset hrange_finite]
      exact Set.mem_range_self k
    have hT_nonempty : T.Nonempty := by
      use f 0
      exact hfk_mem_T 0
    let x := T.max' hT_nonempty
    have hx_mem : x ∈ T := Finset.max'_mem T hT_nonempty
    rw [Set.Finite.mem_toFinset hrange_finite] at hx_mem
    obtain ⟨m, hm⟩ := hx_mem
    use m
    intro k
    rw [hm]
    exact Finset.le_max' T (f k) (hfk_mem_T k)
  obtain ⟨m, hm⟩ := hmax
  use m + 1
  constructor
  · exact Nat.zero_lt_succ m
  · have heq : ∀ n > m, f n = f m := by
      intro n hm_lt_n
      have hfn_lt_fm : f n ≤ f m := hm n
      have hfm_lt_fn : f m ≤ f n := monotone_iff_forall_lt.mp h₂ hm_lt_n
      exact eq_of_le_of_ge hfn_lt_fm hfm_lt_fn
    intro k hk
    rw [heq k (Nat.lt_of_succ_lt hk), heq (k+1) (Nat.lt_of_succ_lt (Nat.lt_add_right 1 hk))]


lemma aux {a : ℕ → ℝ} {s : ℕ}
  (hs_pos : s > 0) (h : ∀ n > s, a n = Finset.max ((Finset.Icc 1 (n-1)).image (fun k ↦ a k + a (n - k)))) :
  ∃ l N : ℕ, (0 < l ∧ l ≤ s ∧ l < N ∧ ∀ n ≥ N, a n = a l + a (n - l)) := by
  let S := fun (n : ℕ) ↦ Finset.Ico 1 n
  have hS_nonempty : ∀ n > s, (S n).Nonempty := fun n hn ↦ Finset.Aesop.nonempty_Ico_of_lt (by grind only)

  let R := Finset.Icc 1 s

  have h_l : ∃ l ∈ R, ∀ i ∈ R, (a i)/i ≤ (a l)/l := Finset.exists_max_image R (fun x' ↦ a x' / ↑x') (Finset.nonempty_Icc.mpr hs_pos)
  obtain ⟨l, hl₁, hl₂⟩ := h_l
  let u := (a l)/l

  let b := fun n ↦ a n - u * n
  have hb_l : b l = 0 := by
    have : l ≠ 0 := by grind only [= Finset.mem_Icc]
    unfold b u
    field_simp
    simp

  have hb {n : ℕ} (hs_lt_n : s < n) : b n = Finset.max' ((S n).image (fun k ↦ b k + b (n - k))) (Finset.image_nonempty.mpr (hS_nonempty n hs_lt_n)) := by
    have : Finset.max' ((S n).image (fun k ↦ b k + b (n - k))) (Finset.image_nonempty.mpr (hS_nonempty n hs_lt_n)) =
           Finset.max' ((S n).image (fun k ↦ a k + a (n - k) - u * n)) (Finset.image_nonempty.mpr (hS_nonempty n hs_lt_n)) := by
      congr 1
      apply Finset.image_congr
      intro k hk
      simp
      unfold b
      rw [coe_mul_sub (by grind only [= Finset.mem_coe, = Finset.mem_Ico])]
      grind only

    rw [this]
    unfold b
    have han := h n hs_lt_n
    rw [show Finset.Icc 1 (n-1) = S n by grind, ← Finset.coe_max' (Finset.image_nonempty.mpr (hS_nonempty n hs_lt_n)), WithBot.coe_eq_coe] at han
    rw [max_of_image_sub (hS_nonempty n hs_lt_n)]
    simpa


  have h_b_le_zero : ∀ n > 0, b n ≤ 0 := by
    have h_b_le_zero' : ∀ n ∈ R, b n ≤ 0 := by
      intro n hn
      have hn₁ : n ≠ 0 := ne_zero_of_lt (Finset.mem_Icc.mp hn).1
      have hn₂ : 0 < n := Nat.zero_lt_of_ne_zero hn₁
      calc
        b n = a n - u * n := rfl
        _ = (a n / n) * n - u * n := by
          rw [div_mul_cancel₀ (a n) (Nat.cast_ne_zero.mpr hn₁)]
        _ ≤ (a l / l) * n - u * n := by
          simp
          rw [mul_le_mul_iff_left₀ (Nat.cast_pos'.mpr hn₂)]
          exact hl₂ n hn
        _ = 0 := sub_self (a l / ↑l * ↑n)

    have h_b_le_zero'' : ∀ n ≥ s, b n ≤ 0 := by
      intro n hn
      have : ∃ k, n = k + s := Nat.exists_eq_add_of_le' hn
      rcases this with ⟨k, rfl⟩
      refine Nat.strong_induction_on k ?_
      intro n' hm
      by_cases hn' : n' = 0
      · rw [hn', zero_add]
        exact h_b_le_zero' s (Finset.right_mem_Icc.mpr hs_pos)
      · have hn'_pos : 0 < n' := Nat.zero_lt_of_ne_zero hn'
        rw [hb (Nat.lt_add_of_pos_left hn'_pos)]
        apply Finset.max'_le
        intro y hy
        simp at hy
        obtain ⟨a, ha, hya⟩ := hy
        have hba : b a ≤ 0 := by
          by_cases ha' : a < s
          · exact h_b_le_zero' a (Finset.mem_Icc.mpr ⟨(Finset.mem_Ico.mp ha).1, Nat.le_of_lt ha'⟩)
          · simp at ha'
            have ha_lt : a - s < n' := by
              rw [Nat.sub_lt_iff_lt_add ha']
              exact (Finset.mem_Ico.mp ha).2
            have := hm (a - s) ha_lt
            rwa [Nat.sub_add_cancel ha'] at this
        have hba' : b (n' + s - a) ≤ 0 := by
          by_cases ha' : a ≥ n'
          · have hna_pos : 0 < n' + s - a := Nat.sub_pos_of_lt (Finset.mem_Ico.mp ha).2
            have hna_le_s : n' + s - a ≤ s := (Nat.sub_le_iff_le_add).mpr (by
                simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using Nat.add_le_add_right ha' s)
            exact h_b_le_zero' (n' + s - a) (Finset.mem_Icc.mpr ⟨hna_pos, hna_le_s⟩)
          · simp at ha'
            have ha_pos : 0 < a := (Finset.mem_Ico.mp ha).1
            have := hm (n' - a) (Nat.sub_lt hn'_pos ha_pos)
            have has : n' - a + s = n' + s - a := by
              rw [Nat.add_comm, ← Nat.add_sub_assoc (Nat.le_of_lt ha') s, Nat.add_comm s n']
            rwa [has] at this
        rw [← hya]
        exact add_nonpos hba hba'
    intro n hn
    by_cases hn' : n ∈ R
    · exact h_b_le_zero' n hn'
    · have hs_le_n : s ≤ n := by
        by_contra hsn
        exact hn' (Finset.mem_Icc.mpr ⟨Nat.succ_le_of_lt hn, Nat.le_of_lt (Nat.not_le.mp hsn)⟩)
      exact h_b_le_zero'' n hs_le_n

  have h_bn_gt_bnl : ∀ n > s, b (n - l) ≤ b n := by
    intro n hn
    have hn_gt_one : 1 < n := Nat.lt_of_le_of_lt hs_pos hn
    calc
      b (n - l) = b l + b (n - l) := by grind only
      _ ≤ Finset.max' ((S n).image (fun k ↦ b k + b (n - k))) (Finset.image_nonempty.mpr (hS_nonempty n hn)) := by
        have hl_lt_n : l ≤ n - 1 := by
          calc
            l ≤ s := by grind only [= Finset.mem_Icc]
            _ ≤ n - 1 := Nat.le_sub_one_of_lt hn
        have hl_in_S : l ∈ S n := by grind only [= Finset.mem_Icc, = Finset.mem_Ico]
        grind only [Finset.le_max', Finset.le_max_of_eq, = Finset.mem_image, Finset.coe_max']
      _ = b n := by rw [hb hn]

  let rec h_b_eq_sum (k : ℕ) (hk_pos : 0 < k) : ∃ Sᵢ : Multiset R, b k = (Sᵢ.map b).sum := by
    -- Use recursion with the fact that bₖ = bᵢ + bₖ₋ᵢ for some i ∈ 1..(k-1)
    by_cases hind : k ∈ R
    · use {⟨k, hind⟩}
      simp
    · have hs_lt_k : s < k := by grind only [= Finset.mem_Icc]
      have := hb hs_lt_k
      apply max_of_image (hS_nonempty k hs_lt_k) at this
      obtain ⟨i, hi, hbk⟩ := this
      have hdec₁ : i < k := by grind only [= Finset.mem_Ico]
      obtain ⟨S₁, hS₁⟩ := h_b_eq_sum i (by grind only [= Finset.mem_Ico])
      have hdec₂ : k - i < k := by grind only [= Finset.mem_Ico]
      obtain ⟨S₂, hS₂⟩ := h_b_eq_sum (k-i) (by grind only [= Finset.mem_Ico])
      rw [hbk, hS₁, hS₂]
      exact sum_multiset S₁ S₂ b
    termination_by k

  have h_b_eq_sum_nonzero (k : ℕ) (hk_pos : 0 < k) : ∃ Sᵢ : Multiset R, b k = (Sᵢ.map b).sum ∧ 0 ∉ (Sᵢ.map b):= by
    obtain ⟨Sᵢ, hbₖ⟩ := h_b_eq_sum k hk_pos
    use Sᵢ.filter fun i ↦ b i ≠ 0
    rw [hbₖ]
    simp
    rw [← Multiset.sum_filter_add_sum_filter_not (fun x ↦ x = 0)]
    have : ((Sᵢ.map (fun i : ℕ ↦ b i)).filter (fun x ↦ x = 0)).sum = 0 := sum_filter_eq_zero
    simp at this
    rw [this]
    simp
    rw [Multiset.filter_map]
    simp



  -- If all bᵢ are zero for i ∈ R, then the proof is trivial
  by_cases h_b_zero : ∀ k ∈ R, b k = 0
  · have h₁ : ∀ k > 0, b k = 0 := by
      intro k hk
      obtain ⟨Sᵢ, hsi⟩ := h_b_eq_sum k hk
      rw [hsi]
      simp
      apply Multiset.sum_eq_zero
      simp
      intro x i hi _ hbi
      rw [← hbi, h_b_zero i hi]
    have h₂ : ∀ k > 0, a k = u * k := fun k hk ↦ by grind only [h₁ k hk]
    use 1
    use 2
    have : ∀ n ≥ 2, a n = a 1 + a (n - 1) := by
      intro n hn
      rw [h₂ 1 (gt_iff_lt.mpr zero_lt_one), h₂ (n - 1) (Nat.zero_lt_sub_of_lt hn), h₂ n (Nat.zero_lt_of_lt hn), coe_mul_sub (Nat.lt_of_succ_le hn)]
      simp
    exact ⟨zero_lt_one, hs_pos, one_lt_two, this⟩

  -- The set of all bₙ is finite
  have h_finite : ∃ Sb : Finset ℝ, ∀ t ∈ Finset.Icc 1 l, ∀ k : ℕ, b (s + t + k * l) ∈ Sb := by
    have hnonempty : (R.image |b|).Nonempty := Finset.image_nonempty.mpr (Finset.nonempty_Icc.mpr hs_pos)
    let M := (R.image |b|).max' hnonempty
    have h_bₙ_bounded : ∀ n > s, -M ≤ b n := by
      intro n hn
      have hl_le_s : l ≤ s := by grind only [= Finset.mem_Icc]
      obtain ⟨t, ht, hbₜ_le_bₙ⟩ := aux₂ b (Finset.mem_Icc.mp hl₁).1 hl_le_s (Nat.lt_of_succ_le hn) h_bn_gt_bnl
      calc
        -M ≤ -|b t| := by
          unfold M R
          have := Finset.max'_mem ((Finset.Icc 1 s).image |b|) hnonempty
          simp at this
          obtain ⟨a, ha₁, ha₂⟩ := this
          rw [← ha₂]
          exact neg_le_neg_iff.mpr (((Finset.max'_eq_iff (R.image |b|) hnonempty |b a|).mp ha₂.symm).2 |b t| (Finset.mem_image_of_mem |b| ht))
        _ ≤ b t := neg_abs_le (b t)
        _ ≤ b n := hbₜ_le_bₙ

    have hR_not_all_zero : (R.filter (fun i ↦ b i ≠ 0)).Nonempty := by
      simp at h_b_zero
      obtain ⟨x, hx, hbx_ne_zero⟩ := h_b_zero
      use x
      simp
      exact ⟨hx, hbx_ne_zero⟩
    let Rb := (R.filter (fun i ↦ b i ≠ 0)).image |b|
    have hRb_not_empty : Rb.Nonempty := Finset.image_nonempty.mpr hR_not_all_zero
    let ε := Rb.min' hRb_not_empty
    have h_ε_pos : 0 < ε := pos_of_min_of_abs_ne_zero hR_not_all_zero
    have h_ε_le_M : ε ≤ M := by
      calc
        ε ≤ Rb.max' hRb_not_empty := Finset.min'_le_max' Rb hRb_not_empty
        _ ≤ M := max_filter_le_max hR_not_all_zero

    have hS_card_bounded : ∀ k > 0, ∃ Sᵢ : Multiset R, b k = (Sᵢ.map b).sum ∧ Sᵢ.card ≤ M/ε := by
      intro k hk
      by_cases h : k ≤ s
      · use {⟨k, Finset.mem_Icc.mpr ⟨hk, h⟩⟩}
        simp
        exact (one_le_div₀ h_ε_pos).mpr h_ε_le_M
      obtain ⟨Sₖ, hbₖ, hzero_not_mem⟩ := h_b_eq_sum_nonzero k hk
      use Sₖ
      constructor
      · exact hbₖ
      have hbounded : ∀ x ∈ Sₖ.map b, x ≤ (-ε) := by
        intro x hx
        simp at hx
        obtain ⟨a, ⟨ha_mem_R, ha_mem_Sₖ⟩, hba⟩ := hx
        rw [←hba, ← neg_le_neg_iff (b := b a) (a := -ε)]
        simp
        have hba_nonpos : b a ≤ 0 := h_b_le_zero a (Finset.mem_Icc.mp ha_mem_R).1
        calc
          ε ≤ |b a| := by
            unfold ε
            have hba_ne_zero : b a ≠ 0 := by
              have : b a ∈ Sₖ.map b := by
                simp
                use a
                constructor
                · exact Exists.intro ha_mem_R ha_mem_Sₖ
                · rfl
              grind only
            have ha_mem : a ∈ (R.filter (fun i ↦ b i ≠ 0)) := Finset.mem_filter.mpr ⟨ha_mem_R, hba_ne_zero⟩
            have hba_mem : |b a| ∈ (R.filter (fun i ↦ b i ≠ 0)).image |b| := Finset.mem_image_of_mem |b| ha_mem
            exact Finset.min'_le (Finset.image |b| ({i ∈ R | b i ≠ 0})) |b a| hba_mem
          _ = - b a := abs_of_nonpos hba_nonpos
      have : -M ≤ Sₖ.card * (-ε) := by
        calc
          -M ≤ b k := h_bₙ_bounded k (Nat.lt_of_not_le h)
          _ = (Sₖ.map b).sum := hbₖ
          _ ≤ Sₖ.card * (-ε) := by
            have := Multiset.sum_le_card_nsmul (Sₖ.map b) (-ε) hbounded
            simp_all
      simp at this
      exact (le_div_iff₀ h_ε_pos).mpr this

    let Sₛ := {Sᵢ : Multiset R | Sᵢ.card ≤ M/ε}
    have hS_finite : Sₛ.Finite := finite_bounded_card_multisets
    let T := Sₛ.image (fun Sᵢ ↦ (Sᵢ.map b).sum)
    have hT_finite : T.Finite := Set.Finite.image (fun Sᵢ ↦ (Sᵢ.map b).sum) hS_finite
    use hT_finite.toFinset
    intro t ht k
    obtain ⟨Sₓ, hbₓ, hcard⟩ := hS_card_bounded (s + t + k * l) (by lia)
    rw [hbₓ]
    simp
    unfold T
    simp
    have : Sₓ ∈ Sₛ := Set.mem_setOf.mpr hcard
    use Sₓ

  -- bₙ will eventually become l-periodic
  have h_Nt : ∀ t ∈ Finset.Icc 1 l, ∃ Nt : ℕ, Nt > s + l ∧ ∀ k : ℕ, s + t + k * l > Nt → b (s + t + k * l) = b (s + t + k * l + l) := by
    intro t ht
    obtain ⟨Sb, hSb⟩ := h_finite
    replace hSb := hSb t ht
    let f := fun k ↦ b (s + t + k * l)
    have hf_in_Sb : ∀ k, f k ∈ Sb := by
      intro k
      exact hSb k
    have hf_monotone : Monotone f := by
      refine monotone_nat_of_le_succ ?_
      intro k
      unfold f
      have := h_bn_gt_bnl (s + t + (k + 1) * l) (by grind only [= Finset.mem_Icc])
      have h' : s + t + (k + 1) * l - l = s + t + k * l := by lia
      rwa [h'] at this
    have h : ∃ Nk > 0, ∀ k > Nk, f k = f (k + 1) := eventually_eq_succ_of_mem_finset_of_monotone hf_in_Sb hf_monotone
    obtain ⟨Nk, hNk_pos, hNk⟩ := h
    use s + t + Nk * l
    constructor
    · calc
        s + l < s + t + l := Nat.add_lt_add_right (Nat.lt_add_of_pos_right (Finset.mem_Icc.mp ht).1) l
        _ ≤ s + t + Nk * l := Nat.add_le_add_left (Nat.le_mul_of_pos_left l hNk_pos) (s + t)
    · intro k h₁
      simp at h₁
      have := hNk k (Nat.lt_of_mul_lt_mul_right h₁)
      unfold f at this
      rw [this]
      congr 1
      lia

  choose Nt hNt using h_Nt
  have hnon_empty : ∀ f : Finset.Icc 1 l → ℕ, (((Finset.Icc 1 l).attach).image f).Nonempty := by
    intro f
    simp_all only [Finset.mem_Icc, Finset.image_nonempty, Finset.attach_nonempty_iff, Finset.nonempty_Icc, R]
  let N : ℕ := (((Finset.Icc 1 l).attach).image (fun t ↦ Nt t.1 (t.2))).max' (hnon_empty (fun t ↦ Nt t.1 (t.2)))
  have hb_n : ∀ n > N + l, b n = b (n - l) + b l := by
    intro n hn
    rw [hb_l, add_zero]
    let t' := (n - s) % l
    let t := if t' = 0 then l else t'
    have ht_in_range : t ∈ Finset.Icc 1 l := by
      simp
      constructor
      · grind only [= Finset.mem_Icc]
      · have : t' < l := Nat.mod_lt (n-s) (by grind only [= Finset.mem_Icc])
        by_cases h : t' = 0
        · unfold t
          rw [if_pos h]
        · unfold t
          rw [if_neg h]
          exact Nat.le_of_succ_le this
    have := hNt t ht_in_range
    have hNt_le_N : Nt t ht_in_range ≤ N := by
      let S := ((Finset.Icc 1 l).attach).image (fun t ↦ Nt t.1 (t.2))
      have : Nt t ht_in_range ∈ S := by
        rw [Finset.mem_image]
        use ⟨t, ht_in_range⟩
        simp
      exact Finset.le_max' S (Nt t ht_in_range) this
    have h_non_neg : s + t + l < n := by
      calc
        s + t + l ≤ s + l + l := by grind only [= Finset.mem_Icc]
        _ < (Nt t ht_in_range) + l := by simp ; exact this.1
        _ ≤ N + l := Nat.add_le_add_right hNt_le_N l
        _ < n := hn
    let k := (n - s - t - l)/l
    have hn_eq : n = s + t + k * l + l := by
      unfold k
      unfold t
      by_cases h : t' = 0
      · rw [if_pos h]
        have h_dvd : l ∣ n - s - l - l := by
          rw [Nat.dvd_sub_self_right]
          left
          rw [Nat.dvd_sub_self_right]
          left
          exact Nat.dvd_of_mod_eq_zero h
        rw [Nat.div_mul_cancel h_dvd]
        have : n > s + l + l := by lia
        grind only
      · rw [if_neg h]
        have h_dvd : l ∣ n - s - t' - l := Nat.dvd_sub_self_right.mpr (Or.inl (Nat.dvd_sub_mod (n - s)))
        rw [Nat.div_mul_cancel h_dvd]
        have h_t'_le_t : t' ≤ t := by
          by_cases h : t' = 0
          · rw [h]
            simp
          · unfold t
            rwa [if_neg]
        have h_non_neg' : s + t' + l < n := by
          calc
            s + t' + l ≤ s + t + l := by simp ; exact h_t'_le_t
            _ < n := h_non_neg
        rw [Nat.add_comm (s + t'), ←Nat.sub_add_eq, ←Nat.sub_add_eq, Nat.add_assoc, ← Nat.add_assoc s, Nat.sub_add_cancel]
        exact le_of_lt h_non_neg'

    have hn_gt_Nt_add_l : n > (Nt t ht_in_range) + l := add_lt_of_add_lt_right hn hNt_le_N
    replace hn_gt_Nt_add_l : s + t + k * l > (Nt t ht_in_range) := by
      rw [hn_eq] at hn_gt_Nt_add_l
      exact Nat.lt_of_add_lt_add_right hn_gt_Nt_add_l
    have := this.2 k hn_gt_Nt_add_l
    rw [hn_eq]
    simp
    exact this.symm

  use l
  use N + l + 1
  have h1 : 0 < l := (Finset.mem_Icc.mp hl₁).1
  have h2 : l ≤ s := (Finset.mem_Icc.mp hl₁).2
  have h3 : l < N + l + 1 := lt_of_lt_of_le (Nat.lt_succ_self l) (Nat.succ_le_succ (Nat.le_add_left l N))
  have h4 : ∀ n > N + l, a n = a l + a (n - l) := by
    intro n hn
    replace hn : n > N + l := Nat.lt_of_succ_le hn
    have hab : ∀ k, b k + k * u = a k := fun k ↦ by ring
    have h_n_gt_l : l < n := lt_of_le_of_lt (Nat.le_add_left l N) hn
    calc
      a n = b n + n * u := by ring
      _ = (b (n - l) + (n - l) * u) + (b l + l * u) := by
        rw [hb_n n hn]
        have hsplit : n * u = (n - l) * u + l * u := by
          calc
            n * u = u * n := Nat.cast_comm n u
            _ = (n - l) * u + l * u := by ring
        rw [hsplit]
        exact add_add_add_comm (b (n - l)) (b l) ((↑n - ↑l) * u) (↑l * u)
      _ = a (n - l) + a l := by grind only [coe_mul_sub]
      _ = a l + a (n - l) := by ring
  exact ⟨h1, h2, h3, h4⟩
snip end


problem imo2010_p6 {a : ℕ+ → ℝ} {s : ℕ+}
  (h : ∀ n > s, a n = Finset.max ((Finset.Icc 1 (n-1)).image (fun k ↦ a k + a (n - k)))) :
  ∃ l N : ℕ+, (l ≤ s ∧ ∀ n ≥ N, a n = a l + a (n - l)) := by
  -- Solution based on https://www.imo-official.org/problems/IMO2010SL.pdf

  -- Conv to ℕ
  let a' := fun (i : ℕ) ↦ if h : 0 < i then a ⟨i, h⟩ else a 1
  have h_conv_a {i : ℕ} (h : 0 < i) : a' i = a ⟨i, h⟩ := dif_pos h
  have h' {n : ℕ} (hs_lt_n : s < n): a' n = Finset.max ((Finset.Icc 1 (n-1)).image (fun k ↦ a' k + a' (n - k))) := by
    have hn_pos : 0 < n := Nat.zero_lt_of_lt hs_lt_n
    have := h ⟨n, hn_pos⟩ hs_lt_n
    rw [h_conv_a hn_pos, this]
    congr 1
    have h_finset : (Finset.Icc 1 (n-1) : Finset ℕ) = (Finset.Icc 1 (⟨n, hn_pos⟩-1) : Finset ℕ+).image (fun k ↦ k.val) := by
      have h1n : (1 : ℕ+) < ⟨n, hn_pos⟩ := PNat.one_lt_of_lt hs_lt_n
      ext k
      constructor
      · intro hk
        have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
        have hk2 : k ≤ n - 1 := (Finset.mem_Icc.mp hk).2
        have hk_pos : 0 < k := Nat.lt_of_lt_of_le Nat.zero_lt_one hk1
        refine Finset.mem_image.mpr ?_
        refine ⟨⟨k, hk_pos⟩, ?_, rfl⟩
        refine Finset.mem_Icc.mpr ?_
        refine ⟨PNat.one_le ⟨k, hk_pos⟩, ?_⟩
        apply (PNat.coe_le_coe _ _).1
        simpa [PNat.sub_coe, if_pos h1n] using hk2
      · intro hk
        rcases Finset.mem_image.mp hk with ⟨k', hk', rfl⟩
        have hk2' : k' ≤ ⟨n, hn_pos⟩ - 1 := (Finset.mem_Icc.mp hk').2
        have hk2 : (k' : ℕ) ≤ n - 1 := by
          have hk2nat : (k' : ℕ) ≤ ((⟨n, hn_pos⟩ - 1 : ℕ+) : ℕ) := (PNat.coe_le_coe _ _).2 hk2'
          simpa [PNat.sub_coe, if_pos h1n] using hk2nat
        exact Finset.mem_Icc.mpr ⟨Nat.succ_le_of_lt k'.pos, hk2⟩
    rw [h_finset]
    rw [Finset.image_image, Finset.image_congr]
    simp
    have h_fun_eq : (fun k : ℕ+ ↦ a k + a (⟨n, hn_pos⟩ - k)) = ((fun k : ℕ ↦ a' k + a' (n - k)) ∘ fun k : ℕ+ ↦ ↑k) := by
      ext k
      unfold a'
      simp
      split_ifs with hk
      · have hk_lt_n : (k : ℕ) < n := hk
        have hk_pnat_lt_n : k < ⟨n, hn_pos⟩ := (PNat.coe_lt_coe k ⟨n, hn_pos⟩).1 hk_lt_n
        have hsub_val : ((⟨n, hn_pos⟩ - k : ℕ+) : ℕ) = n - k := by
          simp [PNat.sub_coe, if_pos hk_pnat_lt_n]
        have hsub : (⟨n, hn_pos⟩ - k : ℕ+) = ⟨n - k, Nat.sub_pos_of_lt hk_lt_n⟩ := by
          apply Subtype.ext
          simpa using hsub_val
        have hk_cast : (⟨(k : ℕ), k.pos⟩ : ℕ+) = k := by
          apply Subtype.ext
          rfl
        simp [hsub, hk_cast]
      · have hk_nat_ge : n ≤ (k : ℕ) := Nat.not_lt.mp hk
        have hk_pnat_not_lt_n : ¬k < ⟨n, hn_pos⟩ := by
          intro hk_pnat_lt_n
          exact (Nat.not_lt_of_ge hk_nat_ge) ((PNat.coe_lt_coe k ⟨n, hn_pos⟩).2 hk_pnat_lt_n)
        have hsub : (⟨n, hn_pos⟩ - k : ℕ+) = 1 := by
          apply PNat.coe_injective
          simp [PNat.sub_coe, if_neg hk_pnat_not_lt_n]
        have hk_cast : (⟨(k : ℕ), k.pos⟩ : ℕ+) = k := by
          apply Subtype.ext
          rfl
        simp [hsub, hk_cast]
    have h_SetEqOn_univ := (Set.eqOn_univ _ _).mpr h_fun_eq
    solve_by_elim

  -- Solve problem in ℕ
  obtain ⟨l, N, hl_pos, hl_le_s, hl_lt_N, hn⟩ := aux (PNat.pos s) (fun n hn ↦ h' hn)

  -- Conv back to ℕ+
  use ⟨l, hl_pos⟩
  use ⟨N, Nat.zero_lt_of_lt hl_lt_N⟩
  constructor
  · exact_mod_cast hl_le_s
  · intro n hn_gt_N
    have := hn n.val hn_gt_N
    have h1 : a n = a' n := Eq.symm (dif_pos n.property)
    have h2 : a ⟨l, hl_pos⟩ = a' l := Eq.symm (dif_pos hl_pos)
    have h3 : a (n - ⟨l, hl_pos⟩) = a' (n - l) := by
      have hl1 : l < n := Nat.lt_of_lt_of_le hl_lt_N hn_gt_N
      have hl2 : ⟨l, hl_pos⟩ < n := (PNat.coe_lt_coe ⟨l, hl_pos⟩ n).mp hl1
      unfold a'
      split_ifs
      · congr
        exact PNat.natPred_inj.mp rfl
      · grind only
    rwa [h1, h2, h3]

end Imo2010P6
