/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: hillosanation
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Olympiad 1988, Problem 4

Show that the set of real numbers $x$ which satisfy the inequality
$$\sum_{k=1}^{70} \frac{k}{x - k} \ge \frac{5}{4}$$
is a union of disjoint intervals, the sum of whose lengths is $1988$.
-/

namespace Imo1988P4

open scoped BigOperators

snip begin
noncomputable section Solution
-- Solution adapted from Art of Problem Solving

abbrev singularities := Finset.Icc (1: ℕ) 70

abbrev f (x: ℝ) := ∑ k ∈ singularities, (k : ℝ) / (x - k) - 5 / 4

abbrev S := {x : ℝ | (5 : ℝ) / 4 ≤ ∑ k ∈ singularities, (k : ℝ) / (x - k)}

instance : Coe (Fin 70) singularities := ⟨fun x => ⟨x + 1, by simpa using Fin.is_le x⟩⟩

abbrev last : singularities := ⟨70, by simp⟩

instance s_nonempty : singularities.Nonempty := ⟨last, Finset.insert_eq_self.mp rfl⟩

lemma f_aligned : {x | 0 ≤ f x} = S := by simp

-- Extrapolate from a root f x = 0 that the continuous segment to the left has f x > 0 and the continuou segument to the right has f x < 0.
section Antitone

lemma div_lt_div' {a b c : ℝ} (ha : 0 < a) (hb : 0 > b) (hc : 0 > c) : a / b < a / c ↔ c < b := by
  rw [← neg_lt_neg_iff, ← div_neg, ← div_neg, div_lt_div_iff_of_pos_left ha (Left.neg_pos_iff.mpr hc) (Left.neg_pos_iff.mpr hb), neg_lt_neg_iff]

lemma anti_io : StrictAntiOn f (Set.Iio 1) := by
  apply StrictAntiOn.add_const <| fun a amem b bmem h_ne => Finset.sum_lt_sum_of_nonempty s_nonempty (fun k kmem => ?_)
  simp_all only [Set.mem_Iio, Finset.mem_Icc]
  have : (1: ℝ) ≤ k := Nat.one_le_cast.mpr kmem.1
  rw [div_lt_div'] <;> lia

lemma anti_oi: StrictAntiOn f (Set.Ioi 70) := by
  apply StrictAntiOn.add_const <| fun _ _ _ _ _ => Finset.sum_lt_sum_of_nonempty s_nonempty (fun k kmem => ?_)
  simp_all only [Set.mem_Ioi, Finset.mem_Icc]
  have : k ≤ (70: ℝ) := Nat.cast_le_ofNat.mpr kmem.2
  rw [div_lt_div_iff_of_pos_left] <;> (norm_cast; lia)

lemma component_anti_oo (k n: singularities) : StrictAntiOn (fun x => (k: ℝ) / (x - k)) (Set.Ioo n (n+1)) := by
  obtain ⟨k, hk⟩ := k
  obtain ⟨n, hn⟩ := n
  simp only [Finset.mem_Icc] at hn hk
  have hnk : (↑n: ℝ) < ↑k → (↑n + 1: ℝ) ≤ ↑k := by exact_mod_cast Order.add_one_le_iff.mpr
  intro a amem b bmem _
  rw [Set.mem_Ioo] at bmem amem
  by_cases h: k < a
  · rw [div_lt_div_iff_of_pos_left] <;> (simp; linarith)
  · replace h : b < k := bmem.2.trans_le (by push_cast; exact hnk <| amem.1.trans <| (not_lt.mp h).lt_of_ne (by lia))
    rw [div_lt_div']
    all_goals linarith

lemma anti_oo (n: singularities) : StrictAntiOn f (Set.Ioo n (n+1)) :=
  StrictAntiOn.add_const (fun _ amem _ bmem h_ne =>
    Finset.sum_lt_sum_of_nonempty s_nonempty fun k kmem =>
      component_anti_oo ⟨k, kmem⟩ n amem bmem h_ne) _

end Antitone

-- Used for IVT to find all roots
section Continuity

lemma component_continuous (k: singularities) : ContinuousOn (fun x => (k: ℝ) / (x-k)) (Set.Iio k ∪ Set.Ioi k) := by
  obtain ⟨k, hk⟩ := k
  rw [continouousOn_union_iff_of_isOpen isOpen_Iio isOpen_Ioi]
  constructor
  <;> exact ContinuousOn.div₀ continuousOn_const
      (ContinuousOn.sub continuousOn_id continuousOn_const)
      (by grind only [= Set.mem_Iio, = Set.mem_Ioi])

lemma continuous_oi : ContinuousOn f (Set.Ioi 70) :=
  ContinuousOn.add (continuousOn_finset_sum _ (fun n hn => ContinuousOn.mono (component_continuous ⟨n, hn⟩) (by
    simp only [Finset.mem_Icc, Set.Iio_union_Ioi, Set.subset_compl_singleton_iff, Set.mem_Ioi,
      Nat.ofNat_lt_cast, not_lt] at hn ⊢; exact hn.2
  ))) continuousOn_const

lemma continuous_oo (n: singularities) : ContinuousOn f (Set.Ioo n (n+1)) := by
  refine ContinuousOn.add (continuousOn_finset_sum _ ?_) continuousOn_const
  refine fun n hn => ContinuousOn.mono (component_continuous ⟨n, hn⟩) ?_
  simp only [Set.Iio_union_Ioi, Set.subset_compl_singleton_iff, Set.mem_Ioo, not_and, not_lt]
  norm_cast
  exact Order.add_one_le_iff.mpr

end Continuity

section Singularity

open Filter Topology

-- each singularity (at the integers) has the left side approaching bot and right side approaching top
lemma component_atBot (k: singularities) : Tendsto (fun (x: ℝ) => k / (x - k)) (𝓝[<] k) atBot := by
  rw [@Filter.tendsto_atBot]
  intro b
  rw [@Filter.eventually_iff_exists_mem]
  obtain ⟨n, hn⟩ := k
  simp only [singularities, Finset.mem_Icc] at hn

  have n_pos : (0: ℝ) < n := Nat.cast_pos.mpr hn.1
  by_cases! h: b < 1
  · replace h := sub_neg.mpr h
    refine ⟨Set.Ioo (b/(b-1) * n) n, Ioo_mem_nhdsLT ?_, fun y ⟨l, r⟩ => ?_⟩
    · rw [mul_lt_iff_lt_one_left n_pos, div_lt_one_of_neg h]; exact sub_one_lt _
    · rw [div_le_iff_of_neg (sub_neg.mpr r)]
      suffices h : (b - 1) * y ≤ b * n by linarith
      rw [← div_le_iff_of_neg' h, mul_div_right_comm]
      exact l.le
  · refine ⟨Set.Iio n, self_mem_nhdsWithin, fun _ hy => ?_⟩
    rw [div_le_iff_of_neg (sub_neg.mpr hy), ← le_div_iff₀' (by linarith), sub_le_iff_le_add]
    refine hy.le.trans ?_
    rw [le_add_iff_nonneg_left]
    exact div_nonneg n_pos.le (by linarith)

lemma component_atTop (k: singularities) : Tendsto (fun (x: ℝ) => k / (x - k)) (𝓝[>] k) atTop := by
  rw [@Filter.tendsto_atTop]
  intro b
  rw [@Filter.eventually_iff_exists_mem]
  obtain ⟨n, hn⟩ := k
  simp only [singularities, Finset.mem_Icc] at hn
  obtain ⟨hn₁, hn₂⟩ := hn

  by_cases! h: 0 < b
  · refine ⟨Set.Ioo n (n + n / b), Ioo_mem_nhdsGT ?_, fun y ⟨l, r⟩ => ?_⟩
    · rw [lt_add_iff_pos_right, div_pos_iff]
      left; constructor; norm_cast; linarith
    · rw [le_div_iff₀ (sub_pos.mpr l), ← le_div_iff₀' (by linarith), sub_le_iff_le_add, add_comm]
      exact r.le
  · exact ⟨Set.Ioi n, self_mem_nhdsWithin, fun y hy => h.trans <| div_nonneg (Nat.cast_nonneg' _) (sub_pos.mpr hy).le⟩

lemma f_atTop : Tendsto f atTop (nhds (-(5/4): ℝ)) := by
  unfold f
  suffices h: ∀ i ∈ singularities, Tendsto (fun x ↦ (i: ℝ) / (x - ↑i)) atTop (𝓝 0) by
    simpa using Tendsto.sub_const (tendsto_finset_sum singularities h) _
  simp only [Finset.mem_Icc, and_imp, Metric.tendsto_atTop]
  refine fun i hi₁ hi₂ ε hε => ⟨i + i/ε + 1, fun n hn => ?_⟩
  rw [Real.dist_0_eq_abs, abs_div]
  have : (0: ℝ) < i := Nat.cast_pos'.mpr hi₁
  have : i < n := calc
    _ < i + i / ε := lt_add_iff_pos_right _ |>.mpr <| div_pos this hε
    _ < i + i / ε + 1 := lt_add_one _
    _ ≤ n := hn
  rw [abs_of_pos, abs_of_pos, div_lt_comm₀ _ hε, lt_sub_iff_add_lt]
  all_goals lia

lemma f_atBot : Tendsto f atBot (nhds (-(5/4): ℝ)) := by
  unfold f
  suffices h: ∀ i ∈ singularities, Tendsto (fun x ↦ (i: ℝ) / (x - ↑i)) atBot (𝓝 0) by
    simpa using Tendsto.sub_const (tendsto_finset_sum singularities h) _
  simp only [Finset.mem_Icc, and_imp]
  simp_rw [@Metric.tendsto_nhds, Real.dist_0_eq_abs, eventually_atBot]
  refine fun i hi₁ hi₂ ε hε => ⟨i - i/ε - 1, fun n hn => ?_⟩
  rw [abs_div]
  have hi : (0: ℝ) < i := Nat.cast_pos'.mpr hi₁
  have : n < i := calc
    _ ≤ i - i / ε - 1 := hn
    _ < i - i / ε := sub_lt_self_iff _ |>.mpr Real.zero_lt_one
    _ < i := sub_lt_self_iff _ |>.mpr <| div_pos hi hε
  rw [abs_of_pos hi, div_lt_comm₀ (abs_pos.mpr _) hε, abs_of_neg]
  all_goals linarith

lemma erase_continuousOn : ContinuousOn (fun x => ∑ k ∈ (singularities \ {↑n}), (k: ℝ) / (x - ↑k)) (Set.Ioo (n-1) (n+1)) := by
  apply continuousOn_finset_sum
  simp only [Finset.mem_sdiff, Finset.mem_singleton]
  refine fun i ⟨imem, h_ne⟩ => ContinuousOn.mono (component_continuous ⟨i, imem⟩) ?_
  push_neg at h_ne
  rw [Nat.ne_iff_lt_or_gt] at h_ne
  rcases h_ne with (h | h)
  all_goals
    simp only [Set.Iio_union_Ioi, Set.subset_compl_singleton_iff, Set.mem_Ioo, sub_lt_iff_lt_add,
      not_and, not_lt]
    norm_cast; intros; lia

lemma erase_continuousAt : ContinuousAt (fun x => ∑ k ∈ (singularities \ {↑n}), (k: ℝ) / (x - ↑k) - 5 / 4) n :=
  ContinuousAt.add (ContinuousOn.continuousAt erase_continuousOn <| mem_nhds_iff.mpr ⟨Set.Ioo (n-1) (n+1), by rfl, isOpen_Ioo, by simp⟩) continuousAt_const

lemma f_singularities_nhdsLT_atBot (n: singularities) : Tendsto f (𝓝[<] n) atBot := by
  rw [(by simp [← add_sub_assoc] : f = fun x => (n: ℝ) / (x - n) + (∑ k ∈ (singularities \ {↑n}), (k: ℝ) / (x - ↑k) - 5 / 4))]
  apply Tendsto.atBot_add (component_atBot _) <|
    tendsto_iff_forall_eventually_mem.mpr fun _ => (nhdsWithin_le_nhds <| ContinuousAt.tendsto erase_continuousAt ·)

lemma f_singularities_nhdsGT_atTop (n: singularities) : Tendsto f (𝓝[>] n) atTop := by
  rw [(by simp [← add_sub_assoc] : f = fun x => (n: ℝ) / (x - n) + (∑ k ∈ (singularities \ {↑n}), (k: ℝ) / (x - ↑k) - 5 / 4))]
  exact Tendsto.atTop_add (component_atTop _) <|
    tendsto_iff_forall_eventually_mem.mpr fun _ => (nhdsWithin_le_nhds <| ContinuousAt.tendsto erase_continuousAt ·)

end Singularity

-- Roots of f, where f x = 0
section Roots

open Finset Filter Function Topology

variable {n: singularities}

-- we can have a stronger condition by replacing ∃ with ∃! from combining the antitone condition
lemma root_Ioi : ∃ x ∈ Set.Ioi 70, f x = 0 := by
  let I := Set.Ioi (70: ℝ)
  have hl₁ : 𝓝[>] (70: ℝ) ≤ 𝓟 I := by
    simp_rw [le_principal_iff, mem_nhdsGT_iff_exists_Ioo_subset, Set.mem_Ioi]
    exact ⟨70+1, lt_add_one _, by simpa only [I] using Set.Ioo_subset_Ioi_self⟩
  have hl₂ : atTop ≤ 𝓟 I := le_principal_iff.mpr <| Ioi_mem_atTop _
  have := (isPreconnected_Ioi : IsPreconnected I).intermediate_value_Ioi hl₂ hl₁ continuous_oi f_atTop
    (f_singularities_nhdsGT_atTop ⟨70, Finset.insert_eq_self.mp rfl⟩)
    (by simp : 0 ∈ Set.Ioi (-((5: ℝ)/4)))
  rwa [Set.mem_image] at this

lemma root_Ioo (h: (n: ℕ) ≠ 70) : ∃ x ∈ Set.Ioo (n: ℝ) (n+1), f x = 0 := by
  let I := Set.Ioo (n: ℝ) (n+1)
  have hl₁ : 𝓝[>] (n: ℝ) ≤ 𝓟 I := by
    simp_rw [le_principal_iff, mem_nhdsGT_iff_exists_Ioo_subset, Set.mem_Ioi]
    exact ⟨n+1, by simp only [lt_add_iff_pos_right, zero_lt_one], by rfl⟩
  have hl₂ : 𝓝[<] (n + 1: ℝ) ≤ 𝓟 I := by
    simp_rw [le_principal_iff, mem_nhdsLT_iff_exists_Ioo_subset, Set.mem_Iio]
    refine ⟨n, lt_add_one _, by rfl⟩
  obtain ⟨n, hn⟩ := n
  rw [Finset.mem_Icc] at hn
  obtain ⟨_, hn₂⟩ := hn
  have : (n: ℕ) ≤ 69 := Nat.le_of_lt_succ <| hn₂.lt_of_ne h
  rw [← Set.mem_image]
  exact (isPreconnected_Ioo: IsPreconnected I).intermediate_value_Iii hl₂ hl₁ (continuous_oo ⟨n, hn⟩)
    (by simpa using f_singularities_nhdsLT_atBot ⟨n + 1, by simp [singularities]; linarith⟩)
    (by simpa using f_singularities_nhdsGT_atTop ⟨n, hn⟩)
    (Set.mem_univ 0)

def r (n: singularities): NNReal := if h : (n: ℕ) = 70
  then ⟨root_Ioi.choose, Nat.ofNat_pos'.trans (Set.mem_Ioi.mp root_Ioi.choose_spec.1) |>.le⟩
  else ⟨root_Ioo h |>.choose, (Nat.cast_nonneg' _).trans (Set.mem_Ioo.mp (root_Ioo h |>.choose_spec.1) |>.1).le⟩

lemma r_root : f (r n) = 0 := by
  simp only [r]; split <;> rename_i h
  · exact root_Ioi.choose_spec.2
  · exact root_Ioo h |>.choose_spec.2

lemma r_bounds (h: (n: ℕ) ≠ 70) : (r n: ℝ) ∈ Set.Ioo (n: ℝ) (n+1) := by
  simpa [r, h] using root_Ioo h |>.choose_spec.1

lemma r_bounds₁ (h: (n: ℕ) ≠ 70) : r n < (n+1) :=
  Set.mem_Ioo.mp (r_bounds h) |>.2

lemma r_bounds₂ (n: singularities) : n < r n := by
  simp only [r]
  split <;> rename_i h
  · rw [h]; exact Set.mem_Ioi.mp <| root_Ioi.choose_spec.1
  · exact Set.mem_Ioo.mp (root_Ioo h |>.choose_spec.1) |>.1

lemma r_not_singularity (n m : singularities) : n ≠ r m := by
  by_cases! h : n ≤ m
  · have : (n: NNReal) ≤ m := by norm_cast
    have := r_bounds₂ m
    lia
  · have : (m: ℕ) ≠ 70 := by
      obtain ⟨_, _⟩ := m; obtain ⟨_, hn⟩ := n
      simp at hn h; lia
    have h2 := r_bounds₁ this
    have h3 : (m + 1 : NNReal) ≤ n := by norm_cast
    lia

lemma r_le_r_70 : r n ≤ r last := by
  obtain ⟨n, hn⟩ := n
  by_cases h: (n: ℕ) = 70
  subst h; rfl
  apply le_of_lt; calc
    r ⟨n, hn⟩ < (n + 1) := r_bounds₁ h
    _ ≤ 70 := by rw [Finset.mem_Icc] at hn; norm_cast; lia
    _ < r last := r_bounds₂ last

lemma r_inj: Function.Injective r := by
  intro a b h_eq
  contrapose! h_eq
  wlog! h: (a: ℕ) < b; symm at h_eq ⊢; exact this h_eq <| h.lt_of_ne <| by exact_mod_cast h_eq
  have h₁ := r_bounds₂ b
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  have ha' := ha
  have hb' := hb
  rw [Finset.mem_Icc] at ha' hb'
  have h₂ := @r_bounds₁ ⟨a, ha⟩ (by lia)
  apply ne_of_lt <| h₂.trans_le (by norm_cast) |>.trans h₁

abbrev rset : Finset ℝ := Finset.image (NNReal.toReal ∘ r) Finset.univ

lemma rset_card : rset.card = 70 :=
  Finset.card_image_of_injective _ <| Function.Injective.comp NNReal.coe_injective r_inj

lemma singularities_sum : ∑ i: Fin 70, r i = ∑ r ∈ rset, r := by
  rw [rset, sum_image <| Injective.injOn <| Injective.comp NNReal.coe_injective r_inj]
  -- adding simp reduces recursion depth needed for norm_cast
  simp; norm_cast

end Roots

section Interval

-- the endpoints don't matter in the volume, so we don't need to know if they are in the solution or not
def I (n: singularities) := (if 0 ≤ f n then Set.Icc else Set.Ioc) (n: ℝ) (r n)

lemma I_bounds (n: singularities) (h: (n: ℕ) ≠ 70) : I n ⊆ Set.Ico n (n+1) := by
  have := r_bounds₁ h
  simp only [I]; split
  · exact Set.Icc_subset_Ico_right this
  · exact Set.Ioc_subset_Icc_self.trans <| Set.Icc_subset_Ico_right (by exact_mod_cast this)

lemma I_bounds' : I ⟨70, Finset.insert_eq_self.mp rfl⟩ ⊆ Set.Ici 70 := by
  simp only [I]; split
  · exact Set.Icc_subset_Ici_self
  · exact Set.Ioc_subset_Icc_self.trans Set.Icc_subset_Ici_self

lemma I_bounds_lower (h: x ∈ I n) : n ≤ x := by
  rw [I] at h; split at h <;> (simp at h; lia)

lemma I_bounds_upper (h: x ∈ I n) : x ≤ r n := by
  rw [I] at h; split at h <;> (simp at h; lia)

lemma ico_stack : Set.Ico (1: ℝ) 71 = ⋃ i : singularities, Set.Ico (i: ℝ) (i+1) := by
  simp only [Set.ext_iff, Set.mem_Ico, Set.mem_iUnion, Subtype.exists, Finset.mem_Icc, exists_and_left, exists_prop]
  refine fun x => ⟨fun ⟨h₁, h₂⟩ => ⟨⌊x⌋₊, ?_⟩, fun ⟨i, h₁, ⟨h₂, h₃⟩, h₄⟩ => ⟨?_, h₄.trans_le ?_⟩⟩
  have : ⌊x⌋₊ ≤ x := Nat.floor_le (by lia)
  exact ⟨this, ⟨Nat.one_le_floor_iff x |>.mpr h₁,Nat.le_of_lt_succ <| Nat.cast_lt.mp <| this.trans_lt h₂⟩, Nat.lt_floor_add_one x⟩
  exact_mod_cast Nat.cast_le.mpr h₂ |>.trans h₁
  exact_mod_cast Nat.add_le_add_right h₃ 1

lemma I_connected (n: singularities) : (I n).OrdConnected := by
  dsimp [I]; split
  · exact Set.ordConnected_Icc
  · exact Set.ordConnected_Ioc

lemma I_disjoint {i j : singularities} (h_ne: (i: ℕ) ≠ j) : Disjoint (I i) (I j) := by
  wlog! h: (i: ℕ) < j generalizing i j; symm at h_ne ⊢; exact this h_ne (h.lt_iff_ne.mpr h_ne)

  obtain ⟨i, hi⟩ := i
  obtain ⟨j, hj⟩ := j
  have h₁ := I_bounds ⟨i, hi⟩ (by rw [singularities, Finset.mem_Icc] at hi hj; lia)
  have h₂ : max (i: ℝ) j = j := max_eq_right_of_lt (by exact_mod_cast h)
  have h₃ : min (i: ℝ) j = i := min_eq_left_of_lt (by exact_mod_cast h)

  rw [Set.disjoint_iff]
  by_cases hj_70 : (j: ℕ) = 70
  · simp_rw [hj_70] at ⊢
    refine Set.inter_subset_inter h₁ I_bounds' |>.trans ?_
    rw [Set.Ico_inter_Ici, Set.Ico_eq_empty_of_le (by norm_cast; simp; lia)]
  · refine Set.inter_subset_inter h₁ (I_bounds ⟨j, hj⟩ hj_70) |>.trans ?_
    rw [Set.Ico_inter_Ico, min_add_add_right, h₂, h₃, Set.Ico_eq_empty_of_le]
    norm_cast

lemma I_compl : (⋃ i, I i)ᶜ = Set.Iio 1 ∪ (⋃ i: singularities, Set.Ico (i: ℝ) (i+1) \ I i) ∪ Set.Ioi (r last) := by
  ext x; constructor
  · intro hx; by_cases h : x ∈ Set.Ico (1: ℝ) 71
    · left; right
      rw [ico_stack] at h
      simp only [Set.mem_iUnion, Set.compl_iUnion, Set.mem_iInter, Set.mem_compl_iff] at *
      obtain ⟨p, hp⟩ := h
      exact ⟨p, hp, hx p⟩
    · simp only [Set.mem_Ico, not_and_or, not_le, not_lt] at h
      rcases h with (h | h)
      left; left; exact h; right;
      have : x ∉ I last := by
        simp only [Set.mem_compl_iff] at hx
        contrapose! hx
        exact ⟨I last, by simp, hx⟩
      rw [I] at this; split at this <;> (simp only [Nat.cast_ofNat, Set.mem_Icc, Set.mem_Ioc, not_and, not_le] at this; exact this (by lia))
  · simp only [Set.mem_union, Set.mem_Iio, Set.mem_iUnion, Set.mem_diff, Set.mem_Ioi,
    Set.mem_compl_iff, not_exists, Subtype.forall, Finset.mem_Icc, forall_and_index]
    rintro ((h | ⟨i, xmem, xnmem⟩) | h) a ha₁ ha₂
    · intro mem
      have : (1: ℝ) ≤ a := by exact_mod_cast ha₁
      by_cases h: a = 70
      · subst h; linarith [Set.mem_Ici.mp <| I_bounds' mem]
      · linarith [Set.mem_Ico.mp <| (I_bounds ⟨a, by lia⟩ h) mem]
    · obtain ⟨i, hi⟩ := i
      by_cases! h : a = i; subst h; exact xnmem
      rw [Nat.ne_iff_lt_or_gt] at h
      rcases h with (h | h)
      exact (I_bounds ⟨a, by lia⟩ (by rw [Finset.mem_Icc] at hi; lia) ·
        |> Set.mem_Ico.mp |>.2.trans_le (by norm_cast) |> (Set.mem_Ico.mp xmem).1.trans_lt |> (lt_self_iff_false _).mp)
      exact (I_bounds_lower · |> le_trans (by norm_cast) |> (Set.mem_Ico.mp xmem).2.trans_le |> (lt_self_iff_false _).mp)
    · exact (h.not_ge <| I_bounds_upper · |>.trans r_le_r_70)

lemma I_aligned : ⋃ i, I i = S := by
  simp_rw [Set.ext_iff]
  intro x
  constructor
  · rw [Set.mem_iUnion, forall_exists_index]
    rintro i p
    have anti : StrictAntiOn f (Set.Ioc i (r i)) := by
      by_cases h: (i: ℕ) = 70
      · rw [h]; norm_cast; exact StrictAntiOn.mono anti_oi Set.Ioc_subset_Ioi_self
      · norm_cast; exact StrictAntiOn.mono (anti_oo i) (Set.Ioc_subset_Ioo_right (by exact_mod_cast r_bounds₁ (by lia)))
    have h : Set.Ioc (i: ℝ) (r i) ⊆ S := by
      intro y hy
      by_cases h2: y = r i; simpa only [h2, ← f_aligned, Set.mem_setOf] using r_root |>.symm.le
      simpa [← f_aligned, r_root] using anti hy (by simpa using r_bounds₂ i) (hy.2.lt_of_ne h2) |>.le
    -- deal with edge cases
    unfold I at p; split at p <;> rename_i h2
    rcases Set.eq_endpoints_or_mem_Ioo_of_mem_Icc p with (rfl | (rfl | h3))
    · simpa [← f_aligned] using h2
    · exact h <| Set.right_mem_Ioc.mpr <| r_bounds₂ _
    · exact h <| Set.Ioo_subset_Ioc_self h3
    apply h; simpa [h2] using p
  · simp_rw [← f_aligned]
    contrapose!
    -- check the components of the complement
    rw [← Set.mem_compl_iff, I_compl, Set.mem_setOf]
    push_neg

    have hr : (70: ℝ) < r last := r_bounds₂ last
    rintro ((h | h) | h)
    · simp only [sub_neg]
      suffices h: ∀ k ∈ singularities, k / (x - k) ≤ 0 by linarith [Finset.sum_nonpos h]
      intro k kmem
      simp only [Set.mem_Iio, Finset.mem_Icc] at kmem h
      apply div_nonpos_of_nonneg_of_nonpos <;> linarith [(by norm_cast; exact kmem.1 : (1: ℝ) ≤ k)]
    · simp only [Set.mem_iUnion, Set.mem_diff] at h
      obtain ⟨i, xmem, xnmem⟩ := h
      rcases Set.eq_left_or_mem_Ioo_of_mem_Ico xmem with (rfl | h)
      · unfold I at xnmem; split at xnmem
        · absurd xnmem; exact Set.mem_Icc.mpr ⟨by rfl, r_bounds₂ i |>.le⟩
        · linarith
      · have h2 : r i < x := by rw [I] at xnmem; split at xnmem <;> (simp at xnmem h; lia)
        by_cases hi: (i: ℕ) = 70
        · obtain ⟨_, _⟩ := i; subst hi
          simpa only [← @r_root last] using anti_oi (Set.mem_Ioi.mpr hr) (hr.trans h2) h2
        · simpa only [← @r_root i] using anti_oo _ (Set.mem_Ioo.mpr ⟨r_bounds₂ _, r_bounds₁ hi⟩) h h2
    · rw [Set.mem_Ioi] at h
      simpa only [r_root] using anti_oi (Set.mem_Ioi.mpr hr) (Set.mem_Ioi.mpr (hr.trans h)) h

lemma I_volume (n: singularities) : MeasureTheory.volume (I n) = r n - n := by
  unfold I; split
  · rw [Real.volume_Icc]; rfl
  · rw [Real.volume_Ioc]; rfl

end Interval

section Polynomial

open Polynomial Function Finset

abbrev M : Polynomial ℝ := ∏ n : singularities, (X - C (n: ℝ))

abbrev M' (n : singularities) : Polynomial ℝ := ∏ k ∈ singularities \ {(n: ℕ)}, (X - C (k : ℝ))

abbrev p : Polynomial ℝ := M + C (-(4 / 5)) * ∑ n : singularities, C (n: ℝ) * M' n

lemma M_sum : ∑ x ∈ singularities.attach, (x: ℝ) = 2485 := by norm_cast

lemma M_natDegree : M.natDegree = 70 := by simp

lemma M'_natDegree (n: singularities) : (M' n).natDegree = 69 := by simp [sdiff_singleton_eq_erase]

lemma M_principal_term' : (C (-(4 / 5)) * ∑ n : singularities, C (n: ℝ) * M' n).natDegree < M.natDegree := by
  rw [natDegree_C_mul (by linarith), M_natDegree]
  exact Nat.lt_add_one_of_le <| natDegree_sum_le_of_forall_le (Finset.univ : Finset singularities)
    (fun n => C (n: ℝ) * M' n) (fun ⟨n, hn⟩ _ => by rw [natDegree_C_mul (by simp at hn ⊢; lia)]; exact M'_natDegree ⟨n, hn⟩ |>.le)

lemma p_natDegree : p.natDegree = 70 := by
  rw [natDegree_add_eq_left_of_degree_lt <| degree_lt_degree M_principal_term']
  exact M_natDegree

lemma p_ne_zero : p ≠ 0 := zero_le_degree_iff.mp <| natDegree_pos_iff_degree_pos.mp (by rw [p_natDegree]; lia) |>.le

example (a b: ℕ) (q: Polynomial ℝ) (h : q.degree = b) (h2 : b < a) : q.coeff a = 0 := by
  refine notMem_support_iff.mp ?_
  exact notMem_of_max_lt h2 h

lemma p_leadingCoeff : p.leadingCoeff = 1 := by
  rw [leadingCoeff, p_natDegree]
  rw [coeff_add, coeff_C_mul]
  simp_rw [@finset_sum_coeff, coeff_C_mul]
  have (x: singularities) : (M' x).coeff 70 = 0 := by
    have : (M' x).degree = 69 := by
      rw [degree_eq_natDegree, M'_natDegree _];rfl
      rw [ne_eq, prod_eq_zero_iff]; exact fun ⟨_, _, h⟩ => X_sub_C_ne_zero _ h
    rw [← notMem_support_iff]
    apply notMem_of_max_lt (by lia: 69 < 70) this
  simp_rw [this]
  rw [← M_natDegree, ← leadingCoeff]
  simp [leadingCoeff_prod, ↓leadingCoeff_X_sub_C]

lemma p_nextCoeff : p.nextCoeff = -4473 := by
  rw [nextCoeff_of_natDegree_pos (by linarith [p_natDegree]), p_natDegree]
  unfold p
  simp only [coeff_add, coeff_C_mul, finset_sum_coeff]
  have : M.nextCoeff = -2485 := by simpa [prod_X_sub_C_nextCoeff] using M_sum
  replace : M.coeff 69 = -2485 := by simp [← this, nextCoeff]
  rw [this]
  replace (x: singularities) : (M' x).leadingCoeff = 1 := by
    rw [leadingCoeff_prod]; simp [↓leadingCoeff_X_sub_C]
  replace (x: singularities) : (M' x).coeff 69 = 1 := by
    rw [← this x, leadingCoeff, M'_natDegree]
  simp [↓this, M_sum]
  linarith

lemma p_roots_card_le_rset_card : p.roots.card ≤ rset.val.card :=
  card_roots' p |>.trans <| by rw [card_val, rset_card, p_natDegree]

lemma p_root_of_r_root : p.IsRoot (r n) := by
  unfold p
  simp only [← sum_coe_sort_eq_attach, map_neg, univ_eq_attach, map_natCast, neg_mul, IsRoot.def, eval_add, eval_prod,
    eval_sub, eval_X, eval_natCast, eval_neg, eval_mul, eval_C, eval_finset_sum]

  have prod_ne_zero {s: Finset { x // x ∈ singularities }} : ∏ x ∈ s, ((r n: ℝ) - (x: ℝ)) ≠ 0 := by
    refine prod_ne_zero_iff.mpr ?_
    simp_rw [sub_ne_zero]
    exact_mod_cast fun a _ => (r_not_singularity a n |>.symm)

  apply_fun (· / ∏ x ∈ singularities.attach, (↑(r n) - ↑x))
  case inj => refine mul_left_injective₀ <| inv_ne_zero prod_ne_zero

  simp only [↓add_div, div_self prod_ne_zero, neg_div, mul_div_assoc, sum_div, zero_div]
  have {x: singularities} (h: x ∈ singularities.attach) :=
    prod_erase_mul singularities.attach (((r n: ℝ) - ·)) h
  conv => enter [1, 2, 1, 2, 2, n, 2, 2]; rw [← this <| mem_attach _ n]
  simp only [sdiff_singleton_eq_erase, ← prod_erase_attach, div_mul_eq_div_div, div_self prod_ne_zero]

  have := @r_root n
  simp_rw [mul_one_div]
  rw [add_neg_eq_zero, ← inv_mul_eq_iff_eq_mul₀ (by linarith), inv_div, mul_one]
  exact eq_of_sub_eq_zero this |>.symm

lemma rset_le_p_roots : rset.val ≤ p.roots := by
  refine val_le_iff_val_subset.mpr fun _ hx => ?_
  simp only [image_val, univ_eq_attach, attach_val, comp_apply, Multiset.mem_dedup,
    Multiset.mem_map, Subtype.exists] at hx
  rcases hx with ⟨n, hn, -, rfl⟩
  refine mem_roots'.mpr ⟨p_ne_zero, p_root_of_r_root⟩

lemma rset_eq_p_roots : rset.val = p.roots :=
  Multiset.eq_of_le_of_card_le rset_le_p_roots p_roots_card_le_rset_card

lemma p_eq_X_sub_C_rset_prod : p = ∏ r ∈ rset, (X - C r) := by
  have := @C_leadingCoeff_mul_prod_multiset_X_sub_C _ _ _ p ?_
  simpa [p_leadingCoeff, ← rset_eq_p_roots] using this.symm
  rw [←rset_eq_p_roots, card_val, rset_card]; exact p_natDegree.symm

lemma roots_sum : ∑ r ∈ rset, r = 4473 := by
  have : (∏ r ∈ rset, (X - C r)).nextCoeff = -4473 := by rw [← p_eq_X_sub_C_rset_prod]; exact p_nextCoeff
  simpa [prod_X_sub_C_nextCoeff] using this

end Polynomial

end Solution
snip end

problem imo1988_p4 :
    ∃ (n : ℕ) (I : Fin n → Set ℝ),
      (∀ i, (I i).OrdConnected) ∧
      (Pairwise fun i j ↦ Disjoint (I i) (I j)) ∧
      (⋃ i, I i) =
        {x : ℝ | (5 : ℝ) / 4 ≤ ∑ k ∈ Finset.Icc (1 : ℕ) 70, (k : ℝ) / (x - k)} ∧
      ∑ i, MeasureTheory.volume (I i) = 1988 := by
  refine ⟨70, (I ↑·), (I_connected ↑·), fun _ _ => (I_disjoint <| by simpa using Fin.val_ne_of_ne ·), ?_, ?_⟩
  -- solution set
  · simp_rw [← I_aligned]
    refine Function.Surjective.iUnion_comp (fun ⟨y, hy⟩ => ?_) I
    rw [Finset.mem_Icc] at hy
    exact ⟨⟨y - 1, by lia⟩, by simp [hy]⟩
  -- volume
  · conv => enter [1, 2]; intro x; rw [I_volume x]
    norm_cast
    rw [Finset.sum_tsub_distrib Finset.univ (fun x _ => by exact_mod_cast r_bounds₂ x |>.le), ← Nat.cast_sum Finset.univ _]
    suffices h : ∑ i : Fin 70, r _ = 4473 by rw [h]; norm_cast
    rw [@NNReal.eq_iff, NNReal.coe_ofNat, singularities_sum, roots_sum]

end Imo1988P4
