/-
Copyright (c) 2026 Sebastian Willmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Willmann (with assistance from Github Copilot and Aristotle)
-/

import Mathlib

import ProblemExtraction

problem_file

/-!
# International Mathematical Olympiad 1992, Problem 5

Let S be a finite set of points in three-dimensional space.
Let Sx,Sy and Sz be the sets consisting of the orthogonal projections of the points of S onto the yz-plane, zx-plane and xy-plane, respectively.
Prove that |S|²≤|Sx|·|Sy|·|Sz|.
where |A| denotes the number of elements in the finite set |A|.
(Note: The orthogonal projection of a point onto a plane is the foot of the perpendicular from the point to the plane.)
-/

namespace Imo1992P5

snip begin

abbrev point3 := ℝ × ℝ × ℝ

noncomputable instance : DecidableEq point3 := Classical.decEq _

noncomputable def projection (d : Fin 3) (p : point3) : point3 :=
  (if d = 0 then 0 else p.1, if d = 1 then 0 else p.2.1, if d = 2 then 0 else p.2.2)

noncomputable def project_set (d : Fin 3) (S : Finset point3) : Finset point3 :=
  S.image (projection d)

noncomputable def S_x (S : Finset point3) : Finset point3 := project_set 0 S
noncomputable def S_y (S : Finset point3) : Finset point3 := project_set 1 S
noncomputable def S_z (S : Finset point3) : Finset point3 := project_set 2 S

lemma project_set_mem (S : Finset point3) (d : Fin 3) (s_d : point3)
    (hs : s_d ∈ project_set d S) : ∃ p ∈ S, projection d p = s_d := by
  simp only [project_set, Finset.mem_image] at hs; exact hs

lemma project_set_subset (S T : Finset point3) (d : Fin 3) (h : S ⊆ T) :
    project_set d S ⊆ project_set d T :=
  Finset.image_subset_image h

/-- Z_i S r is the set of points in S with z-coordinate equal to r -/
noncomputable def Z_i (S : Finset point3) (r : ℝ) : Finset point3 :=
  S.filter (fun p => p.2.2 = r)

/-- A set is a Z_i set if all its points have the same z-coordinate -/
def is_Z_i_set (Z_i : Finset point3) : Prop := ∃ r : ℝ, ∀ p ∈ Z_i, p.2.2 = r

/-- Z S is the collection of all Z_i sets for S -/
noncomputable def Z (S : Finset point3) : Finset (Finset point3) :=
  S.image (fun p => Z_i S p.2.2)

lemma Z_S_mem_mem_S (S z : Finset point3) (w : point3) (hz : z ∈ Z S) (hw : w ∈ z) : w ∈ S := by
  simp only [Z, Finset.mem_image] at hz
  obtain ⟨_, _, rfl⟩ := hz
  simp only [Z_i, Finset.mem_filter] at hw
  exact hw.1

lemma project_set_Z_i_inj (Z_i : Finset point3) (h_Zi : is_Z_i_set Z_i) :
    ∀ p1 ∈ Z_i, ∀ p2 ∈ Z_i, projection 2 p1 = projection 2 p2 → p1 = p2 := by
  intro p1 hp1 p2 hp2 h
  obtain ⟨r, hr⟩ := h_Zi
  simp only [projection, Fin.isValue, ↓reduceIte] at h
  have hz1 := hr p1 hp1; have hz2 := hr p2 hp2
  ext <;> simp_all

lemma project_set_Z_i_card (Z_i : Finset point3) (hz_i : is_Z_i_set Z_i) :
    (project_set 2 Z_i).card = Z_i.card := by
  apply Finset.card_image_of_injOn
  exact fun _ hx _ hy h => project_set_Z_i_inj Z_i hz_i _ hx _ hy h

lemma Z_i_partition (S : Finset point3) : (Z S).biUnion id = S := by
  unfold Z Z_i
  ext a
  simp only [Finset.mem_biUnion, Finset.mem_image, id_eq, exists_exists_and_eq_and,
    Finset.mem_filter]
  constructor
  · rintro ⟨w, -, ha, -⟩; exact ha
  · intro ha; exact ⟨a, ha, ha, rfl⟩

lemma Z_i_is_Z_i_set (S : Finset point3) (r : ℝ) : is_Z_i_set (Z_i S r) :=
  ⟨r, fun _ hp => (Finset.mem_filter.mp hp).2⟩

lemma Z_are_Z_i_sets (S : Finset point3) : ∀ z_i ∈ Z S, is_Z_i_set z_i := by
  intro z_i hz
  simp only [Z, Finset.mem_image] at hz
  obtain ⟨w, _, rfl⟩ := hz
  exact Z_i_is_Z_i_set S w.2.2

noncomputable def a_i (S : Finset point3) (r : ℝ) : Finset point3 := (Z_i S r).image (projection 0)
noncomputable def b_i (S : Finset point3) (r : ℝ) : Finset point3 := (Z_i S r).image (projection 1)
noncomputable def a_i_from_Z_i (z : Finset point3) : Finset point3 := z.image (projection 0)
noncomputable def b_i_from_Z_i (z : Finset point3) : Finset point3 := z.image (projection 1)

noncomputable def a (S : Finset point3) : Finset (Finset point3) := S.image (fun p => a_i S p.2.2)
noncomputable def b (S : Finset point3) : Finset (Finset point3) := S.image (fun p => b_i S p.2.2)

noncomputable def a_card (S : Finset point3) : Multiset ℕ := (a S).val.map Finset.card
noncomputable def b_card (S : Finset point3) : Multiset ℕ := (b S).val.map Finset.card

lemma a_eq_a_i_from_Z_i (S : Finset point3) : a S = (Z S).image a_i_from_Z_i := by
  unfold a a_i_from_Z_i a_i Z Z_i
  ext; simp only [Finset.mem_image, exists_exists_and_eq_and]

lemma z_i_sets_eq_or_disjoint (S le ri : Finset point3) (hle_Z : ri ∈ Z S) (hri_Z : le ∈ Z S) :
    ri = le ∨ (le ∩ ri) = ∅ := by
  obtain ⟨slice_1, hs1⟩ := Z_are_Z_i_sets S le hri_Z
  obtain ⟨slice_2, hs2⟩ := Z_are_Z_i_sets S ri hle_Z
  by_cases h : slice_1 = slice_2
  · left
    simp_all only [Z, Z_i, Finset.mem_image]
    obtain ⟨p1, _, rfl⟩ := hle_Z
    obtain ⟨p2, _, rfl⟩ := hri_Z
    grind only [= Finset.mem_filter]
  · right
    simp only [Z, Finset.mem_image] at hle_Z hri_Z
    obtain ⟨_, _, rfl⟩ := hle_Z
    obtain ⟨_, _, rfl⟩ := hri_Z
    grind only [= Finset.mem_filter, = Finset.mem_inter, ← Finset.notMem_empty]

lemma z_i_eq_if_proj_eq (S ri le : Finset point3) (hle_Z : ri ∈ Z S) (hri_Z : le ∈ Z S)
    (hslice : ∃ r ∈ ri, ∃ l ∈ le, r.2.2 = l.2.2) : ri = le := by
  obtain ⟨r_point, hr_p_in_ri, l_point, hl_p_in_le, h_r_eq_l⟩ := hslice
  obtain ⟨r_ri, hr_ri⟩ := Z_are_Z_i_sets S ri hle_Z
  obtain ⟨r_le, hr_le⟩ := Z_are_Z_i_sets S le hri_Z
  rcases z_i_sets_eq_or_disjoint S le ri hle_Z hri_Z with h_eq | h_disjoint
  · exact h_eq
  · simp only [Z, Finset.mem_image] at hle_Z hri_Z
    obtain ⟨_, _, rfl⟩ := hle_Z
    obtain ⟨_, _, rfl⟩ := hri_Z
    simp_all only [Z_i, Finset.mem_filter]


lemma a_disjoint_helper (le ri S : Finset point3) (hri_Z : ri ∈ Z S) (hle_Z : le ∈ Z S)
    (hp_nempty : (a_i_from_Z_i le ∩ a_i_from_Z_i ri).Nonempty) (h_disjoint : le ∩ ri = ∅)
    (hneq : ri ≠ le) : False := by
  obtain ⟨r_le, hr_le⟩ := Z_are_Z_i_sets S le hle_Z
  obtain ⟨r_ri, hr_ri⟩ := Z_are_Z_i_sets S ri hri_Z
  obtain ⟨inter_elem, hinter⟩ := hp_nempty
  rw [Finset.mem_inter] at hinter
  simp only [a_i_from_Z_i, Finset.mem_image, projection] at hinter
  obtain ⟨⟨le_p, hle_p, rfl⟩, ri_p, hri_p, heq⟩ := hinter
  simp only [Fin.isValue, ↓reduceIte, Prod.mk.injEq] at heq
  obtain ⟨hy_eq, hz_eq⟩ := heq
  have hz_le := hr_le le_p hle_p
  have hz_ri := hr_ri ri_p hri_p
  by_cases hx : le_p.1 = ri_p.1
  · have : le_p = ri_p := by ext <;> simp_all
    subst this
    exact Finset.ne_empty_of_mem (Finset.mem_inter_of_mem hle_p hri_p) h_disjoint
  · have heq_sets := z_i_eq_if_proj_eq S le ri hle_Z hri_Z
      ⟨le_p, hle_p, ri_p, hri_p, by simp_all⟩
    exact hneq heq_sets.symm

lemma a_disjoint (S : Finset point3) : (SetLike.coe (a S)).PairwiseDisjoint id := by
  rw [Finset.pairwiseDisjoint_iff]
  intro k hk l hl hkl
  rw [a_eq_a_i_from_Z_i S] at hk hl
  simp_all only [Finset.mem_coe, Finset.mem_image]
  obtain ⟨w, hw, rfl⟩ := hk
  obtain ⟨w_1, hw_1, rfl⟩ := hl
  congr 1
  by_cases heq : w = w_1
  · exact heq
  · rcases z_i_sets_eq_or_disjoint S w w_1 hw_1 hw with h | hdisj
    · exact (heq h.symm).elim
    · exact (a_disjoint_helper w w_1 S hw_1 hw hkl hdisj (Ne.symm heq)).elim

lemma is_Z_i_set_subset (z1 z2 : Finset point3) (h_z2 : is_Z_i_set z2) (h_subset : z1 ⊆ z2) :
    is_Z_i_set z1 := by
  obtain ⟨r, hr⟩ := h_z2
  exact ⟨r, fun p hp => hr p (h_subset hp)⟩


/-- First Equation: |Z_i| ≤ |a_i| * |b_i| -/
theorem equation_1 (z : Finset point3) (h : is_Z_i_set z) :
    (z.card : ℝ) ≤ (a_i_from_Z_i z).card * (b_i_from_Z_i z).card := by
  obtain ⟨r, hr⟩ := h
  have h_inj : z.card ≤ (z.image (fun p => (projection 0 p, projection 1 p))).card := by
    rw [Finset.card_image_of_injOn]
    intro p hp q hq heq
    simp only [projection, Fin.isValue, ↓reduceIte, Prod.mk.injEq] at heq
    ext <;> simp_all
  have h_prod : (z.image (fun p => (projection 0 p, projection 1 p))).card ≤
      (a_i_from_Z_i z).card * (b_i_from_Z_i z).card := by
    rw [← Finset.card_product]
    exact Finset.card_le_card (Finset.image_subset_iff.mpr fun x hx =>
      Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hx, Finset.mem_image_of_mem _ hx⟩)
  exact_mod_cast le_trans h_inj h_prod


/-- Second Equation: |S| = sum |Z_i| -/
lemma equation_2_old (S : Finset point3) : S.card = ((Z S).biUnion id).card := by
  rw [Z_i_partition]

theorem equation_2 (S : Finset point3) : S.card = ∑ z_i ∈ Z S, z_i.card := by
  rw [equation_2_old]
  rw [Finset.card_biUnion (fun zi hzi zj hzj hij => ?_)]
  · simp only [id_eq]
  · rcases z_i_sets_eq_or_disjoint S zi zj hzj hzi with heq | hdisj
    · exact (hij heq.symm).elim
    · exact Finset.disjoint_iff_inter_eq_empty.mpr hdisj


/-- Third Equation: |S_x| = sum |a_i| -/
lemma a_i_partitions_S_x (S : Finset point3) : (a S).biUnion id = S_x S := by
  unfold a S_x project_set a_i Z_i projection
  ext x
  simp only [Fin.isValue, Finset.mem_biUnion, Finset.mem_image, id_eq, exists_exists_and_eq_and,
    Finset.mem_filter]
  constructor
  · rintro ⟨w, -, p, ⟨hp, -⟩, rfl⟩; exact ⟨p, hp, rfl⟩
  · rintro ⟨w, hw, rfl⟩; exact ⟨w, hw, w, ⟨hw, rfl⟩, rfl⟩

theorem equation_3 (S : Finset point3) : (S_x S).card = ((a S).biUnion id).card := by
  rw [a_i_partitions_S_x]

theorem equation_3_new (S : Finset point3) : (S_x S).card = (a_card S).sum := by
  rw [equation_3 S]
  simp only [a_card, Finset.sum_map_val]
  symm
  rw [Finset.card_biUnion]
  · simp only [id_eq]
  · intro x hx y hy hxy
    simp only [id_eq, Finset.disjoint_iff_inter_eq_empty]
    by_contra h
    exact hxy (Finset.pairwiseDisjoint_iff.mp (a_disjoint S) hx hy (Finset.nonempty_iff_ne_empty.mpr h))

/-- Equation 4: |S_y| = sum |b_i| -/
lemma b_i_partitions_S_y (S : Finset point3) : (b S).biUnion id = S_y S := by
  unfold b S_y project_set b_i Z_i projection
  ext x
  simp only [Fin.isValue, Finset.mem_biUnion, Finset.mem_image, id_eq, exists_exists_and_eq_and,
    Finset.mem_filter]
  constructor
  · rintro ⟨w, -, p, ⟨hp, -⟩, rfl⟩; exact ⟨p, hp, rfl⟩
  · rintro ⟨w, hw, rfl⟩; exact ⟨w, hw, w, ⟨hw, rfl⟩, rfl⟩

theorem equation_4 (S : Finset point3) : (S_y S).card = ((b S).biUnion id).card := by
  rw [b_i_partitions_S_y]

lemma Z_preserves_mem_project_set (S w : Finset point3) (hw : w ∈ Z S) :
    project_set 2 w ⊆ project_set 2 S :=
  Finset.image_subset_image fun x hx => Z_S_mem_mem_S S w x hw hx

lemma s_z_mem_projected_Z_i (S : Finset point3) (s_z : point3) (hs_z : s_z ∈ S_z S) :
    ∃ z_i ∈ Z S, s_z ∈ project_set 2 z_i := by
  obtain ⟨w, hw, rfl⟩ := project_set_mem S 2 s_z hs_z
  exact ⟨Z_i S w.2.2, Finset.mem_image_of_mem _ hw, Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hw, rfl⟩)⟩

lemma projected_Z_i_partitions_S_Z (S : Finset point3) :
    (Finset.image (fun zi => project_set 2 zi) (Z S)).biUnion id = S_z S := by
  ext s_z
  simp only [Fin.isValue, Finset.mem_biUnion, Finset.mem_image, id_eq, exists_exists_and_eq_and]
  constructor
  · rintro ⟨w, hw, hs⟩
    exact Z_preserves_mem_project_set S w hw hs
  · intro hs_z
    obtain ⟨z_i, hz_i, hs⟩ := s_z_mem_projected_Z_i S s_z hs_z
    exact ⟨z_i, hz_i, hs⟩

theorem equation_5 (S : Finset point3) : ∀ z_i ∈ Z S, (z_i.card : ℝ) ≤ (S_z S).card := by
  intro z_i hz
  simp only [Z, Finset.mem_image] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  have h_card := project_set_Z_i_card (Z_i S w.2.2) (Z_i_is_Z_i_set S w.2.2)
  have h_sub : Z_i S w.2.2 ⊆ S := Finset.filter_subset _ _
  have h := project_set_subset (Z_i S w.2.2) S 2 h_sub
  simp only [Nat.cast_le]
  calc (Z_i S w.2.2).card = (project_set 2 (Z_i S w.2.2)).card := by simp [h_card]
    _ ≤ (project_set 2 S).card := Finset.card_le_card h
    _ = (S_z S).card := rfl

lemma equation_1_and_5 (S z : Finset point3) (hz : is_Z_i_set z) (hz_in : z ∈ Z S) :
    (z.card : ℝ)^2 ≤ (S_z S).card * (a_i_from_Z_i z).card * (b_i_from_Z_i z).card := by
  have eq1 := equation_1 z hz
  have eq5 := equation_5 S z hz_in
  have h := mul_le_mul eq1 eq5 (Nat.cast_nonneg' _) (mul_nonneg (Nat.cast_nonneg' _) (Nat.cast_nonneg' _))
  ring_nf at *; exact h

lemma equation_1_and_5_sqrt (S z : Finset point3) (hz : is_Z_i_set z) (hz_in : z ∈ Z S) :
    (z.card : ℝ) ≤ (((S_z S).card : ℝ) * (a_i_from_Z_i z).card * (b_i_from_Z_i z).card).sqrt :=
  Real.le_sqrt_of_sq_le (equation_1_and_5 S z hz hz_in)

lemma sum_inequality {α : Type*} [DecidableEq α] (f g : α → ℝ) (s : Finset α)
    (h : ∀ x ∈ s, f x ≤ g x) : ∑ x ∈ s, f x ≤ ∑ x ∈ s, g x :=
  Finset.sum_le_sum h

theorem equation_6 (S : Finset point3) :
    ∑ z_i ∈ Z S, (z_i.card : ℝ) ≤ ∑ z_i ∈ Z S, (((S_z S).card : ℝ) * (a_i_from_Z_i z_i).card * (b_i_from_Z_i z_i).card).sqrt :=
  sum_inequality _ _ _ fun x hx => equation_1_and_5_sqrt S x (Z_are_Z_i_sets S x hx) hx

lemma sum_prod {α: Type*} [DecidableEq α] (f: α → ℝ) (s: Finset α) (g: ℝ) :
    (∑ x ∈ s, f x * g) = g * (∑ x ∈ s, f x) := by
  rw [← Finset.sum_mul]; ring

lemma sqrt_mul (a b c: ℝ) (h: a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0) : (a * b).sqrt * c.sqrt = (a * b * c).sqrt := by {
  simp_all only [ge_iff_le, Real.sqrt_mul, Real.sqrt_mul']
}


-- The sixth equation can be rearranged to have the square root of S_z out of the sum.
lemma equation_6_rearr (S: Finset point3) : ∑ z_i ∈ Z S, (z_i.card: ℝ) ≤ ((S_z S).card: ℝ).sqrt * ∑ z_i ∈ Z S, ((((a_i_from_Z_i z_i).card: ℝ) * (b_i_from_Z_i z_i).card)).sqrt := by {
  have h6 := equation_6 S
  -- set s_z_card_sqrt := (S_z S).card.sqrt
  rw [← sum_prod]
  · convert_to ∑ z_i ∈ Z S, (z_i.card: ℝ) ≤ ∑ x ∈ Z S, ((((a_i_from_Z_i x).card: ℝ) * ((b_i_from_Z_i x).card: ℝ)).sqrt * ((S_z S).card: ℝ).sqrt)
    convert_to ∑ z_i ∈ Z S, (z_i.card: ℝ) ≤ ∑ x ∈ Z S, ((((a_i_from_Z_i x).card: ℝ) * ((b_i_from_Z_i x).card: ℝ)) * (S_z S).card).sqrt
    · apply Finset.sum_congr
      · rfl
      intro z_i _
      set a_card := ((a_i_from_Z_i z_i).card: ℝ)
      set b_card := ((b_i_from_Z_i z_i).card: ℝ)
      set s_z_card := ((S_z S).card: ℝ)
      apply sqrt_mul
      simp
      simp_all only [Finset.card, Nat.cast_nonneg, and_self, a_card, b_card, s_z_card]
    convert_to ∑ z_i ∈ Z S, (z_i.card: ℝ) ≤ ∑ z_i ∈ Z S, √(((S_z S).card: ℝ) * (a_i_from_Z_i z_i).card * (b_i_from_Z_i z_i).card)
    · apply Finset.sum_congr
      · rfl
      simp
      exact fun x a ↦
        Eq.symm (mul_rotate √↑(S_z S).card √↑(a_i_from_Z_i x).card √↑(b_i_from_Z_i x).card)

    exact h6
}

-- Now, we substitute equation 2 in equation 6.
lemma subst_2_6 (S: Finset point3): (S.card: ℝ) ≤ ((S_z S).card: ℝ).sqrt * ∑ z_i ∈ Z S, ((((a_i_from_Z_i z_i).card: ℝ) * ((b_i_from_Z_i z_i).card: ℝ))).sqrt := by {
  rw [equation_2 S]

  have := equation_6_rearr S
  simp_all only [Nat.cast_nonneg, Real.sqrt_mul, Nat.cast_sum]
}

-- Helper lemma for squaring two sides of an inequality
lemma square_inequality {a b : ℝ} (h2: a ≥ 0) : a ≤ b → a^2 ≤ b^2 := by {
  intro h
  rw [ge_iff_le] at h2
  apply sq_le_sq'
  · grind
  · assumption
}

-- Now, we square both sides
lemma subst_2_6_sqr (S: Finset point3): (S.card: ℝ) ^ 2 ≤ ((S_z S).card: ℝ) * (∑ z_i ∈ Z S, √(((a_i_from_Z_i z_i).card: ℝ) * ((b_i_from_Z_i z_i).card: ℝ))) ^ 2 := by {
  -- Which theorem states this?

  have h2_6 := subst_2_6 S
  have S_card_nonneg : 0 ≤ (S.card: ℝ) := by {
    exact Nat.cast_nonneg' S.card
  }
  have temp := square_inequality S_card_nonneg h2_6
  -- Rewrite a bit
  convert_to (S.card: ℝ) ^ 2 ≤ (√((S_z S).card: ℝ) * ∑ z_i ∈ Z S, √(((a_i_from_Z_i z_i).card: ℝ) * ((b_i_from_Z_i z_i).card: ℝ ))) ^ 2
  · ring_nf
    rw  [Real.sq_sqrt]
    · ring
    exact Nat.cast_nonneg' (S_z S).card
  exact temp
}


/-- Cauchy-Schwarz: sum of sqrt (a_i b_i) ≤ sqrt (sum a_i) * sqrt (sum b_i) -/
lemma sum_sqrt_le_sqrt_sum (S: Finset point3) :
    ∑ z_i ∈ Z S, √(((a_i_from_Z_i z_i).card: ℝ) * ((b_i_from_Z_i z_i).card: ℝ)) ≤
    √(∑ z_i ∈ Z S, ((a_i_from_Z_i z_i).card: ℝ)) * √(∑ z_i ∈ Z S, ((b_i_from_Z_i z_i).card: ℝ)) := by
  have a_i_nonneg : ∀ z_i ∈ Z S, 0 ≤ ((a_i_from_Z_i z_i).card: ℝ) := fun _ _ => Nat.cast_nonneg' _
  rw [← Real.sqrt_mul (Finset.sum_nonneg a_i_nonneg)]
  refine Real.le_sqrt_of_sq_le ?_
  convert Finset.sum_mul_sq_le_sq_mul_sq (Z S)
    (fun z_i => √((a_i_from_Z_i z_i).card : ℝ))
    (fun z_i => √((b_i_from_Z_i z_i).card : ℝ)) using 3 <;>
  norm_num [Real.sqrt_mul, a_i_nonneg]

lemma le_trans_mul_sqr {a b c d: ℝ} (hcd: 0 ≤ c) (hb: 0 ≤ b) (h1: a ≤ b * c ^2) (h2: c ≤ d) : a ≤ b * d ^ 2 := by {
  apply le_trans h1
  apply mul_le_mul
  · exact Preorder.le_refl b
  · exact square_inequality hcd h2
  · exact sq_nonneg c
  assumption
}

lemma pre_7 (S: Finset point3) :
    (S.card: ℝ)^2 ≤ ((S_z S).card: ℝ) * (√(∑ z_i ∈ Z S, ((a_i_from_Z_i z_i).card: ℝ)) *
      √(∑ z_i ∈ Z S, ((b_i_from_Z_i z_i).card: ℝ)))^2 := by
  set inner := ∑ z_i ∈ Z S, √(((a_i_from_Z_i z_i).card: ℝ) * ((b_i_from_Z_i z_i).card: ℝ))
  have hcd : 0 ≤ inner := Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _
  have hb : 0 ≤ ((S_z S).card: ℝ) := Nat.cast_nonneg' _
  exact le_trans_mul_sqr hcd hb (subst_2_6_sqr S) (sum_sqrt_le_sqrt_sum S)

-- Almost there: Equation 7:
-- |S|^2 ≤ |S_z| * (sum a_i) * (sum b_i)

theorem equation_7 (S: Finset point3) : (S.card: ℝ)^2 ≤ ((S_z S).card: ℝ) * (∑ z_i ∈ Z S, ((a_i_from_Z_i z_i).card: ℝ)) * (∑ z_i ∈ Z S, ((b_i_from_Z_i z_i).card: ℝ)) := by
  set a := ∑ z_i ∈ Z S, ((a_i_from_Z_i z_i).card: ℝ)
  set b := ∑ z_i ∈ Z S, ((b_i_from_Z_i z_i).card: ℝ)
  have a_nonneg : 0 ≤ a := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg' _
  have b_nonneg : 0 ≤ b := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg' _
  convert_to (S.card: ℝ) ^ 2 ≤ ((S_z S).card: ℝ) * (√a * √b) ^ 2
  · ring_nf; rw [Real.sq_sqrt b_nonneg, Real.sq_sqrt a_nonneg]
  exact pre_7 S

lemma e3_e7_translate (S: Finset point3) :
    (∑ z_i ∈ Z S, ((a_i_from_Z_i z_i).card: ℝ)) = (a_card S).sum := by
  have h_a_card_def : a_card S = (Z S).val.map (fun z => (a_i_from_Z_i z).card) := by
    unfold a_card a
    have h_eq : Finset.image (fun p => a_i S p.2.2) S = Finset.image a_i_from_Z_i (Z S) := by
      unfold Z a_i_from_Z_i; ext a : 1
      simp_all only [Fin.isValue, Finset.mem_image, exists_exists_and_eq_and]; rfl
    rw [h_eq, Finset.image_val]
    have h_disjoint : ∀ z1 z2 : Finset point3, z1 ∈ Z S → z2 ∈ Z S → z1 ≠ z2 →
        Disjoint (a_i_from_Z_i z1) (a_i_from_Z_i z2) := by
      intros z1 z2 hz1 hz2 hneq
      apply Finset.disjoint_left.mpr
      intro x hx1 hx2
      obtain ⟨p1, hp1, rfl⟩ := Finset.mem_image.mp hx1
      obtain ⟨p2, hp2, hp2_eq⟩ := Finset.mem_image.mp hx2
      have h_proj_eq : p1.2.1 = p2.2.1 ∧ p1.2.2 = p2.2.2 := by
        unfold projection at hp2_eq; simp_all
      exact hneq (z_i_eq_if_proj_eq S z1 z2 hz1 hz2 ⟨p1, hp1, p2, hp2, h_proj_eq.2⟩)
    have h_dedup : ∀ z1 z2 : Finset point3, z1 ∈ Z S → z2 ∈ Z S →
        a_i_from_Z_i z1 = a_i_from_Z_i z2 → z1 = z2 := by
      intros z1 z2 hz1 hz2 h_eq
      specialize h_disjoint z1 z2 hz1 hz2
      by_cases h : z1 = z2 <;> simp_all [a_i_from_Z_i]
    rw [Multiset.dedup_eq_self.mpr]
    · rw [Multiset.map_map]; rfl
    · exact Multiset.Nodup.map_on (fun z1 hz1 z2 hz2 h => h_dedup z1 z2 hz1 hz2 h) (Finset.nodup _)
  simp_all only [Finset.sum_map_val, Nat.cast_sum]

lemma e4_e7_translate (S: Finset point3) :
    (∑ z_i ∈ (Z S), ((b_i_from_Z_i z_i).card: ℝ)) = ((b S).biUnion id).card := by
  have hb_biUnion : (b S).biUnion id = Finset.biUnion (Z S) b_i_from_Z_i := by
    ext; simp [b]; unfold b_i_from_Z_i b_i Z
    simp_all only [Fin.isValue, Finset.mem_image, Prod.exists, ↓existsAndEq, and_true]
  rw [hb_biUnion, Finset.card_biUnion]
  · simp_all only [Nat.cast_sum]
  intro x hx y hy hxy
  obtain ⟨r, hr⟩ : ∃ r, x = Z_i S r := by
    unfold Z at hx
    simp_all only [Finset.coe_image, Set.mem_image, Finset.mem_coe, ne_eq]
    obtain ⟨w, _, rfl⟩ := hx; exact ⟨w.2.2, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s, y = Z_i S s := by
    unfold Z at hy; subst hr
    simp_all only [Finset.coe_image, Set.mem_image, Finset.mem_coe, ne_eq]
    obtain ⟨w, _, rfl⟩ := hy; exact ⟨w.2.2, rfl⟩
  have hz : r ≠ s := by contrapose! hxy; subst hxy hr hs; rfl
  have h_disjoint : ∀ p ∈ x, ∀ q ∈ y, projection 1 p ≠ projection 1 q := by
    intros p hp q hq h_eq
    unfold projection at h_eq; simp_all
    unfold Z_i at hp hq; subst hr hs
    simp_all only [Finset.mem_filter, and_false]
  exact Finset.disjoint_left.mpr fun p hp hp' => by
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨q', hq', hq''⟩ := Finset.mem_image.mp hp'
    specialize h_disjoint q hq q' hq'; subst hs hr
    simp_all only [ne_eq, Fin.isValue, not_true_eq_false]

snip end

problem imo1992_p5 (S: Finset (ℝ × ℝ × ℝ)) : S.card^2 ≤
    (Finset.image (fun p => ((0: ℝ) , p.2.1, p.2.2)) S).card *
    (Finset.image (fun p => (p.1, ((0: ℝ) , p.2.2))) S).card *
    (Finset.image (fun p => (p.1, p.2.1, (0: ℝ) )) S).card := by
  suffices H : (S.card : ℝ)^2 ≤
      ((Finset.image (fun p => ((0: ℝ) , p.2.1, p.2.2)) S).card :ℝ) *
      (Finset.image (fun p => (p.1, ((0: ℝ) , p.2.2))) S).card *
      (Finset.image (fun p => (p.1, p.2.1, (0: ℝ) )) S).card by
    norm_cast at H

  -- Revert to our own notation for S_x, S_y and S_z
  convert_to (S.card: ℝ)^2 ≤ ((S_x S).card: ℝ) * ((S_y S).card: ℝ) * ((S_z S).card: ℝ)
  have e7 := equation_7 S

  -- We use equations 4 and 3 in 7.
  have e3 := equation_3_new S
  have e4 := equation_4 S

  have trans37 := e3_e7_translate S
  rw [trans37, ← e3] at e7
  have trans47 := e4_e7_translate S
  rw [trans47, ← e4] at e7
  grind only


end Imo1992P5
