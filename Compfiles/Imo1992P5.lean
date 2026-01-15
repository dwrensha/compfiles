/-
Copyright (c) 2026 Sebastian Willmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Willmann (with assistance from Github Copilot and Aristotle)
-/

-- I reduced the imports because my PC is not very fast
-- import Mathlib.Tactic.FinCases
-- import Mathlib.Data.Real.Basic
-- import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Real.Sqrt

import Lean

import ProblemExtraction

problem_file
/-
# International Mathematical Olympiad 1992, Problem 5

Let S be a finite set of points in three-dimensional space.
Let Sx,Sy and Sz be the sets consisting of the orthogonal projections of the points of S onto the yz-plane, zx-plane and xy-plane, respectively.
Prove that |S|²≤|Sx|·|Sy|·|Sz|.
where |A| denotes the number of elements in the finite set |A|.
(Note: The orthogonal projection of a point onto a plane is the foot of the perpendicular from the point to the plane.)
-/

namespace Imo1992P5

-- noncomputable def point3 := Fin 3 → ℝ

abbrev point3 := (ℝ × ℝ × ℝ)

noncomputable def point3_eq (p q: point3) : Decidable (Eq p q) :=
  if h1: p.fst = q.fst then
    if h2: p.snd.fst = q.snd.fst then
      if h3: p.snd.snd = q.snd.snd then
        have h : p = q := by
          {
            grind
          }
        isTrue h
      else
        isFalse (by exact Ne.intro fun a ↦ h3 (congrArg Prod.snd (congrArg Prod.snd a)))
    else
      isFalse (by exact Ne.intro fun a ↦ h2 (congrArg Prod.fst (congrArg Prod.snd a)))
  else
    isFalse (by exact Ne.intro fun a ↦ h1 (congrArg Prod.fst a))

noncomputable instance : DecidableEq point3 := by
  {
    intros p q
    exact point3_eq p q
  }

-- def point_index (d: Fin 3) (p: point3) : ℝ :=
--   match d with
--   | 0 => p.fst
--   | 1 => p.snd.fst
--   | 2 => p.snd.snd

noncomputable def projection (d: Fin 3) (p: point3) : point3 :=
  -- fun i => if i = d then 0 else ((point_index i p))
  (if d = 0 then 0 else p.fst,
    if d = 1 then 0 else p.snd.fst,
    if d = 2 then 0 else p.snd.snd)


snip begin

-- Note: I was not able to remove the projection from the problem definition due to
-- the ad-hoc definition of it not using the some equality definition.
-- I'd be happy to make the problem cleaner if there is a way to do so.



-- I'll start by declaring the induction construction of the projections.

/-- Because we need to argue with the cardinality of sets and also need to take square roots
-- AND because they are not mapping to the reals when applied to naturals,
-- We'll instead express cardinality as a real number.
-- It can be undone by `unfold Finset.rcard; refine Nat.cast_inj.mpr ?_`. --/
-- Note: this was removed to simplify the solution description. I did learn
-- that this is identical to (S.card: R) in-line.
-- noncomputable def Finset.rcard {α : Type*} (S: Finset α) : ℝ :=
--   (S.card: ℝ)

-- Proves that the rcard of a set is ≥0
-- @[simp]
-- lemma rcard_nonneg (S: Finset point3) : 0 ≤ S.rcard := by
--   {
--     unfold Finset.rcard
--     simp
--   }

-- The card_le_card is also used, so well show it here.
-- lemma Finset.rcard_le_rcard {α: Type*} {S T: Finset α} : S ⊆ T → S.rcard ≤ T.rcard := by
--   {
--     intro h
--     unfold Finset.rcard
--     simp_all only [Nat.cast_le]
--     exact Finset.card_le_card h
--   }

-- Helper Constructions: Project a set (S) into the X, y, or z direction
noncomputable def project_set (d: Fin 3) (S: Finset point3) : Finset point3 :=

    -- We cannot use the Finset.map function, because that only allows embeddings,
    -- which our projection isn't, because it isn't injective (it also isn't surjective)
    -- So we'll instead use the Finset.image function, which allows us to create a new set
    -- by applying a function to each element of the original set.
    -- But it does require DecidableEq instances for the types involved.
  Finset.image (projection d) S

noncomputable def S_x (S: Finset point3) : Finset point3 :=
  project_set 0 S

noncomputable def S_y (S: Finset point3) : Finset point3 :=
  project_set 1 S

noncomputable def S_z (S: Finset point3) : Finset point3 :=
  project_set 2 S

-- Helper lemma: each value of some projected set corresponds to some point in the original set.
lemma project_set_mem (S: Finset point3) (d: Fin 3) (s_d: point3) (hs: s_d ∈ project_set d S) : ∃ p ∈ S, projection d p = s_d := by
  {
    unfold project_set at hs
    simp_all only [Finset.mem_image]
  }

-- Helper lemma: if set a is a subset of set b, then after projecting them, this is still the case.
lemma project_set_subset (S T: Finset point3) (d: Fin 3) (h: S ⊆ T) : project_set d S ⊆ project_set d T := by
  {
    unfold project_set projection
    intro p left
    simp_all only [Finset.mem_image]
    obtain ⟨w, h_1⟩ := left
    obtain ⟨left, right⟩ := h_1
    subst right
    apply Exists.intro
    · apply And.intro
      · exact Finset.mem_def.mpr (h left)
      simp
  }

-- Next in the proof, we need to construct the Z_i sets.
-- Given S, the Z_i sets are the sets of points in S with the same Z coordinate.
-- This means that the union on Z_i is S and that each point in S is in exactly one Z_i set.
noncomputable def Z_i (S: Finset point3) (r: ℝ) : Finset point3 :=
  S.filter (fun p => p.snd.snd = r)

-- Something is a Z_i set iff its third component is constant across all points.
-- To handle empty sets better, I'll rewrite it as "cardinality of z coordinated ≤1"
-- This makes the proof harder, so I'll instead move to the old definition, but remove the "only one" requirement.
noncomputable def is_Z_i_set (Z_i: Finset point3) : Prop :=
  ∃ r: ℝ, ∀ p ∈ Z_i, p.snd.snd = r

noncomputable def Z (S: Finset point3) : Finset (Finset point3) :=
  S.image (fun p => Z_i S (p.snd.snd))

-- Helper lemma: Z S contains all elements of S in two layers
lemma Z_S_mem_mem_S (S z: Finset point3) (w: point3) (hz: z ∈ Z S) (hw: w ∈ z) : w ∈ S := by
  {
    unfold Z Z_i at hz
    simp_all only [Finset.mem_image]
    obtain ⟨w_1, h⟩ := hz
    obtain ⟨_, right⟩ := h
    subst right
    simp_all only [Finset.mem_filter]
  }

-- Helper lemma for the helper lemma for the helper lemma below: If two elements of a Z_i set project to the same, they are the same.
lemma project_set_Z_i_inj (Z_i: Finset point3) (h_Zi: is_Z_i_set Z_i) : ∀ p1 ∈ Z_i, ∀ p2 ∈ Z_i, projection 2 p1 = projection 2 p2 → p1 = p2 := by
  {
    intro p1 hp1 p2 hp2 h
    -- unfold projection at h
    unfold is_Z_i_set at h_Zi
    obtain ⟨r, hr⟩ := h_Zi

    unfold projection at h
    simp at h
    obtain ⟨h1, h2⟩ := h
    ext
    · assumption
    · assumption
    · grind
  }

-- Helper lemma for the helper lemma below: projecting a Z_i set constructs a bijection
lemma project_set_bij_Z_i (Z_i: Finset point3) (h_Zi: is_Z_i_set Z_i) : ∀ p1 ∈ (project_set 2 Z_i), ∃! p2 ∈ Z_i, projection 2 p2 = p1 := by
  {
    intro s_z hs_z
    have temp: ∃ p2 ∈ Z_i, projection 2 p2 = s_z := by {
      exact project_set_mem Z_i 2 s_z hs_z
    }
    obtain ⟨p2, temp⟩ := temp
    obtain ⟨p2z_i, hp2⟩ := temp
    use p2
    simp
    constructor
    constructor
    · assumption
    · assumption
    intro z_i h_zi hp
    subst hp2
    exact fun a a_1 ↦ project_set_Z_i_inj Z_i h_Zi (z_i, h_zi, hp) a p2 p2z_i a_1
  }

-- Helper lemma: show that if a Z_i set is projected, its cardinality is preserved.
lemma project_set_Z_i_card (Z_i: Finset point3) (hz_i: is_Z_i_set Z_i) : (project_set 2 Z_i).card = Z_i.card := by
  {
    refine Nat.cast_inj.mpr ?_
    apply Finset.card_image_of_injOn
    unfold Set.InjOn
    intro x hx y hy h2
    simp_all only [Fin.isValue, Finset.mem_coe]
    have temp := project_set_Z_i_inj Z_i hz_i x hx y hy
    simp_all

  }

-- Exercise: show that the Z_i sets partition S
lemma Z_i_partition (S: Finset point3) : (Z S).biUnion id = S := by
  {
    unfold Z Z_i
    ext a : 1
    simp_all only [Finset.mem_biUnion, Finset.mem_image, id_eq, exists_exists_and_eq_and,
      Finset.mem_filter]
    apply Iff.intro
    · intro a_1
      obtain ⟨w, h⟩ := a_1
      obtain ⟨_, right⟩ := h
      obtain ⟨left_1, _⟩ := right
      simp_all only
    · intro a_1
      simp_all only [true_and]
      apply Exists.intro
      · apply And.intro
        on_goal 2 => {rfl
        }
        · simp_all only

  }

-- Exercise: show that if a set comes from Z_i, it is a Z_i set.
lemma Z_i_is_Z_i_set (S: Finset point3) (r: ℝ): is_Z_i_set (Z_i S r) := by
  {
    unfold is_Z_i_set Z_i
    use r
    intro p a
    simp_all only [Finset.mem_filter]
  }

-- Show that all results from the Z call are Z_i sets.
lemma Z_are_Z_i_sets (S: Finset point3) : ∀ z_i ∈ Z S, is_Z_i_set z_i := by
  {
    intro z_i hZ_i
    unfold is_Z_i_set
    unfold Z Z_i at hZ_i
    simp_all only [Finset.mem_image]
    obtain ⟨w, h⟩ := hZ_i
    obtain ⟨_, right⟩ := h
    subst right
    simp_all only [Finset.mem_filter, and_imp]
    apply Exists.intro
    · intro p _ _
      rfl
  }


-- Now we construct a_i and b_i.
-- They are the values in each Z_i, projected into y and z respectively.
noncomputable def a_i (S: Finset point3) (r: ℝ) : Finset point3 :=
  (Z_i S r).image (fun p => projection 0 p)

noncomputable def b_i (S: Finset point3) (r: ℝ) : Finset point3 :=
  (Z_i S r).image (fun p => projection 1 p)

noncomputable def a_i_from_Z_i (Z_i: Finset point3) : Finset point3 :=
  Z_i.image (fun p => projection 0 p)

noncomputable def b_i_from_Z_i (Z_i: Finset point3) : Finset point3 :=
  Z_i.image (fun p => projection 1 p)

-- All a_i sets, given S
noncomputable def a (S: Finset point3) : Finset (Finset point3) :=
  S.image (fun p => a_i S (p.snd.snd))

noncomputable def b (S: Finset point3) : Finset (Finset point3) :=
  S.image (fun p => b_i S (p.snd.snd))

-- The cardinality of all a_i sets, in order, given S.
noncomputable def a_card (S: Finset point3) : Multiset Nat :=
  (a S).val.map (fun p => p.card)

-- The cardinality of all b_i sets, in order, given S.
noncomputable def b_card (S: Finset point3) : Multiset Nat :=
  (b S).val.map (fun p => p.card)


-- Show that obtaining the as using a or a_i_from_Z_i is the same.
lemma a_eq_a_i_from_Z_i (S: Finset point3) : (a S) = (Z S).image (fun z => a_i_from_Z_i z) := by
  {
    unfold a a_i_from_Z_i a_i Z Z_i
    ext a : 1
    simp_all only [Fin.isValue, Finset.mem_image, exists_exists_and_eq_and]
  }

-- Show that when two Z_i sets come from the same S, they are either equal or disjoint.
lemma z_i_sets_eq_or_disjoint (S le ri: Finset point3) (hle_Z : ri ∈ Z S) (hri_Z : le ∈ Z S) : ri = le ∨ (le ∩ ri) = ∅ := by {
  have fwd : is_Z_i_set le := Z_are_Z_i_sets S le hri_Z
  have fwd_1 : is_Z_i_set ri := Z_are_Z_i_sets S ri hle_Z
  unfold is_Z_i_set at fwd fwd_1
  obtain ⟨slice_1, hs1⟩ := fwd
  obtain ⟨slice_2, hs2⟩ := fwd_1


  by_cases h: slice_1 = slice_2
  {
    left -- They must be equal

    simp_all
    -- All third coordintates are the same. Because the come from the same (Z S), they must be the same set.

    unfold Z Z_i at hle_Z hri_Z
    subst h
    simp_all only [Finset.mem_image]
    obtain ⟨slice_point_1, hsp1⟩ := hle_Z
    obtain ⟨slice_point_2, hsp2⟩ := hri_Z
    obtain ⟨hsp1_in_S, ri_def⟩ := hsp1
    obtain ⟨hsp2_in_S, le_def⟩ := hsp2
    subst ri_def le_def
    simp_all only [Finset.mem_filter, and_imp]

    grind only [= Finset.mem_filter]

  }
  {
    right
    -- Both slices are different.
    unfold Z Z_i at hle_Z hri_Z
    simp_all

    obtain ⟨slice_point_1, hsp1⟩ := hle_Z
    obtain ⟨slice_point_2, hsp2⟩ := hri_Z
    obtain ⟨hsp1_in_S, ri_def⟩ := hsp1
    obtain ⟨hsp2_in_S, le_def⟩ := hsp2
    grind only [= Finset.mem_filter, = Finset.mem_inter, ← Finset.notMem_empty]
  }

}

-- Another helper lemma for a_disjoint below.
-- If two elements from Z S have a matching Z-level, they are identical.
lemma z_i_eq_if_proj_eq (S: Finset point3) (ri le: Finset point3) (hle_Z : ri ∈ Z S) (hri_Z : le ∈ Z S) (hslice: ∃ r ∈ ri, ∃ l ∈ le, (r.snd.snd) = (l.snd.snd)) : ri = le := by {
  obtain ⟨r_point, h⟩ := hslice
  obtain ⟨hr_p_in_ri, right⟩ := h
  obtain ⟨l_point, h⟩ := right
  obtain ⟨hl_p_in_le, h_r_eq_l⟩ := h
  have fwd : l_point ∈ S := Z_S_mem_mem_S S le l_point hri_Z hl_p_in_le
  have fwd_1 : r_point ∈ S := Z_S_mem_mem_S S ri r_point hle_Z hr_p_in_ri
  have fwd_2 : is_Z_i_set ri := Z_are_Z_i_sets S ri hle_Z
  have fwd_3 : is_Z_i_set le := Z_are_Z_i_sets S le hri_Z

  -- Use the disjoint or equal lemma
  have h_eq_or_disjoint := z_i_sets_eq_or_disjoint S le ri hle_Z hri_Z
  cases h_eq_or_disjoint with
  | inl h_eq => exact h_eq
  | inr h_disjoint => {
    unfold is_Z_i_set at fwd_2 fwd_3
    obtain ⟨r_ri, hr_ri⟩ := fwd_2
    obtain ⟨r_le, hr_le⟩ := fwd_3
    simp_all

    unfold Z at hle_Z hri_Z
    simp_all

    obtain ⟨slice_point_1, hsp1⟩ := hle_Z
    obtain ⟨slice_point_2, hsp2⟩ := hri_Z
    obtain ⟨hsp1_in_S, ri_def⟩ := hsp1
    obtain ⟨hsp2_in_S, le_def⟩ := hsp2
    -- subst ri_def le_def

    unfold Z_i at ri_def le_def

    -- have h_slice_point_1_in_ri : slice_point_1 ∈ ri := by {
    --   subst ri_def h_r_eq_l le_def
    --   simp_all only [Fin.isValue, Finset.mem_filter, and_self, true_and, and_imp]
    -- }
    -- have h_slice_point_2_in_le : slice_point_2 ∈ le := by {
    --   subst ri_def h_r_eq_l le_def
    --   simp_all only [Fin.isValue, Finset.mem_filter, and_self, true_and, and_imp]
    -- }

    grind only [= Finset.mem_filter]

  }
}


-- I got stuck at a_disjoint and wanted to clean it up, so I'll move the statement I got stuck at here, to have it be cleaner.
lemma a_disjoint_helper (le ri S: Finset point3) (hri_Z : ri ∈ Z S) (hle_Z : le ∈ Z S) (hp_nempty: (a_i_from_Z_i le ∩ a_i_from_Z_i ri).Nonempty) (h_disjoint: le ∩ ri = ∅) (hneq: ri ≠ le) : False := by {


  have test: (a_i_from_Z_i le ∩ a_i_from_Z_i ri).Nonempty → (le ∩ ri).Nonempty := by {
    intro hp_nempty2
    unfold Finset.Nonempty
    simp_all only [ne_eq, Finset.notMem_empty, exists_false]
    have fwd : is_Z_i_set ri := Z_are_Z_i_sets S ri hri_Z
    have fwd_1 : is_Z_i_set le := Z_are_Z_i_sets S le hle_Z

    unfold Finset.Nonempty at hp_nempty2
    obtain ⟨inter_elem, elem_in⟩ := hp_nempty2

    have elem_in_f_le : inter_elem ∈ a_i_from_Z_i le := by {
      exact Finset.mem_of_mem_filter inter_elem elem_in
    }
    have elem_in_f_ri : inter_elem ∈ a_i_from_Z_i ri := by {
      exact Finset.mem_of_mem_inter_right elem_in
    }

    simp_all only [Finset.mem_inter, and_self]

    -- We now declare that we have an element in both a_i sets.
    -- This can't be, because the coordinates after projection cannot match.

    unfold a_i_from_Z_i projection at elem_in_f_le elem_in_f_ri

    simp_all only [Fin.isValue, Finset.mem_image]

    obtain ⟨le_p, hle_p_in_le, helem_le⟩ := elem_in_f_le
    obtain ⟨ri_p, hri_p_in_ri, helem_ri⟩ := elem_in_f_ri

    -- If this were the case, the reference points need to be equal in dimension 2 (which is Z)

    have hle_p_eq_ri_p_2 : le_p.snd.snd = ri_p.snd.snd := by {
      rw [← helem_le] at  helem_ri
      simp at helem_ri
      exact Real.ext_cauchy (congrArg Real.cauchy (congrArg Prod.snd (id (Eq.symm helem_ri))))
    }

    have hle_p_eq_ri_p_1 : le_p.snd.fst = ri_p.snd.fst := by {
      rw [← helem_le] at  helem_ri
      simp at helem_ri
      exact Real.ext_cauchy (congrArg Real.cauchy (congrArg Prod.fst (id (Eq.symm helem_ri))))
    }

    -- Now we can do a by_cases based on the third dimension of those points.
    -- If it's equal, then le and ri have a nonzero intersection, contradicting h_disjoint.
    -- If it's not equal, then two contradictory defintions of inter_elem exist.

    by_cases h: le_p.fst = ri_p.fst
    {
      -- They are equal, so we have a point in the intersection of le and ri.
      have ri_le_eq: le_p = ri_p := by {
        ext
        · exact h
        · exact hle_p_eq_ri_p_1
        · exact hle_p_eq_ri_p_2
      }
      subst ri_le_eq
      simp_all

      have le_p_in_inter: le_p ∈ le ∩ ri := by {
        exact Finset.mem_inter_of_mem hle_p_in_le hri_p_in_ri
      }

      have inter_nonempty : (le ∩ ri) ≠ ∅ := by {
        exact Finset.ne_empty_of_mem le_p_in_inter
      }

      exact inter_nonempty h_disjoint
    }
    {




      unfold is_Z_i_set at fwd fwd_1
      obtain ⟨r_le, hr_le⟩ := fwd_1
      obtain ⟨r_ri, hr_ri⟩ := fwd

      -- Consider the Z coordinates of le_p and ri_p
      specialize hr_le le_p hle_p_in_le
      specialize hr_ri ri_p hri_p_in_ri

      simp_all

      have insert_elem_in_ri: (∃ r ∈ le, ∃ l ∈ ri, r.snd.snd = l.snd.snd) := by {
        use le_p
        use hle_p_in_le
        use ri_p
        use hri_p_in_ri
        rw [hr_le, hr_ri]
      }

      have applied_projection := z_i_eq_if_proj_eq S le ri hle_Z hri_Z insert_elem_in_ri
      rw [applied_projection] at hneq
      simp_all only [not_true_eq_false]
    }

  }

  have hnot_empty : (le ∩ ri) ≠ ∅ := by {
    exact Finset.nonempty_iff_ne_empty.mp (test hp_nempty)
  }

  exact hnot_empty h_disjoint
}

-- Show that the results of (a S) are pairwise disjoint.
lemma a_disjoint (S: Finset point3): (SetLike.coe (a S)).PairwiseDisjoint id := by {
  refine Finset.pairwiseDisjoint_iff.mpr ?_
  intro k hk l hl hkl
  simp_all only [Finset.mem_coe, id_eq]

  rw [a_eq_a_i_from_Z_i S] at hk hl
  simp_all only [Finset.mem_image]
  obtain ⟨w, h⟩ := hk
  obtain ⟨w_1, h_1⟩ := hl
  obtain ⟨left, right⟩ := h
  obtain ⟨left_1, right_1⟩ := h_1
  subst right right_1
  have fwd : is_Z_i_set w := Z_are_Z_i_sets S w left
  have fwd_1 : is_Z_i_set w_1 := Z_are_Z_i_sets S w_1 left_1

  apply congrArg

  -- unfold a_i_from_Z_i projection at hkl
  unfold is_Z_i_set at fwd fwd_1
  obtain ⟨w_2, h⟩ := fwd

  -- They are two Z_i sets, so they are either equal or disjoint.

  have w_w_1_eq_or_disjoint := z_i_sets_eq_or_disjoint S w w_1 left_1 left
  by_cases w_eq: w = w_1
  {
    assumption
  }
  {

    -- Now we have two assumptions that stand in direct contradiction.
    -- The w_w_1_eq_or_disjoint says they are disjoint, but hkl says they their projections intersect.

    simp_all only
    have w_w_1_disjoint : (w ∩ w_1) = ∅ := by {
      cases w_w_1_eq_or_disjoint with
      | inl h_2 =>
        subst h_2
        simp_all only [Finset.inter_self, not_true_eq_false]
      | inr h_3 => simp_all only
    }

    have applied := a_disjoint_helper w w_1 S left_1 left hkl w_w_1_disjoint
    exact applied fun a ↦ w_eq (id (Eq.symm a))

  }
}

-- Helper lemma:
-- Basically, if a set is a Z_i set, then every subset is also a Z_i set.
lemma is_Z_i_set_subset (z1: Finset point3) (z2: Finset point3) (h_z2: is_Z_i_set z2) (h_subset: z1 ⊆ z2) : is_Z_i_set z1 := by
  {
    unfold is_Z_i_set at h_z2
    obtain ⟨r, hr⟩ := h_z2
    use r
    intro p hp
    have fwd : p ∈ z2 := by {
      exact h_subset hp
    }
    exact hr p fwd
  }


---------
-- First Equation:  |Z_i| ≤ |a_i| * |b_i|
-------
theorem equation_1 (z: Finset point3) (h: is_Z_i_set z): (z.card: ℝ) ≤ (a_i_from_Z_i z).card * ((b_i_from_Z_i z).card: ℝ) := by
  {

    -- I'm not sure whether an induction is the right step. So I'm giving aristotle full control.
    -------- Aristotle start --------
     -- Fix a Z_i set, and show that |Z_i| ≤ |a_i| * |b_i|.
    have h_optimal : ∀ z : Finset point3, is_Z_i_set z → z.card ≤ (a_i_from_Z_i z).card * (b_i_from_Z_i z).card := by
      intros z h_z_i_set
      obtain ⟨r, hr⟩ := h_z_i_set;
      -- Since $a_i$ and $b_i$ are projections of $z$, each element in $z$ corresponds to a unique pair $(a_i, b_i)$.
      have h_bij : Finset.card z ≤ Finset.card (Finset.image (fun p => (projection 0 p, projection 1 p)) z) := by
        rw [ Finset.card_image_of_injOn ];
        intros p hp q hq h_eq
        unfold projection at h_eq
        simp_all
        obtain ⟨h_eq0, h_eq1⟩ := h_eq
        ext
        · simp_all only [and_true]
        · simp_all only [and_true]
        · simp_all only
      refine le_trans h_bij ?_;
      exact le_trans ( Finset.card_le_card <| show Finset.image ( fun p => ( projection 0 p, projection 1 p ) ) z ⊆ Finset.image ( fun p => ( projection 0 p, projection 1 p ) ) ( z ) from Finset.Subset.refl _ ) ( by rw [ ← Finset.card_product ] ; exact Finset.card_le_card <| Finset.image_subset_iff.mpr fun x hx => Finset.mem_product.mpr ⟨ Finset.mem_image_of_mem _ hx, Finset.mem_image_of_mem _ hx ⟩ )
    convert h_optimal z h using 1
    norm_cast
    -------- Aristotle end --------
  }


--------
-- Second Equation: |S| = sum |Z_i|
--------
lemma equation_2_old (S: Finset point3) : S.card = ((Z S).biUnion id).card := by
-- The second equation follows from the fact that the Z_i sets partition S.
  {
    have h := Z_i_partition S
    -- We already proved this.
    rw [h]
  }

theorem equation_2 (S: Finset point3) : S.card = ∑ z_i ∈ (Z S), z_i.card := by
  {
    rw [equation_2_old]

    have set_set_eq (Z : Finset (Finset point3)) (h: ∀ zi ∈ Z, ∀ zj ∈ Z, Disjoint zi zj ∨ zi = zj) : ∑ z ∈ Z, z.card = (Z.biUnion id).card := by
      {
        -- apply Finset.card_biUnion
        ------ Aristotle start --------
        rw_mod_cast [ Finset.card_biUnion ];
        · rfl;
        · -- By definition of pairwise disjointness, if for all zi ∈ Z and zj ∈ Z, if zi ≠ zj then zi and zj are disjoint, then the set Z is pairwise disjoint.
          intros zi hzi zj hzj hij; exact (by
          -- Apply the hypothesis h to zi and zj, and since they are not equal, we get that they are disjoint.
          apply (h zi hzi zj hzj).resolve_right hij)
        ------- Aristotle end --------

      }
    rw  [set_set_eq (Z S)]
    intro zi hzi zj hzj

    -- Now I need to prove that two Z_i sets from the same S are either equal or disjoint,
    -- which is equivalent to showing that the Z_i partition S, which I have already done.
    by_cases h : zi = zj
    · right
      exact h
    simp only [h, or_false]
    -- Extract the members from the set_set_eq statement above.
    have h_disjoint := z_i_sets_eq_or_disjoint S zi zj hzj hzi
    cases h_disjoint with
    | inl h_eq =>
      symm at h_eq
      contradiction
    | inr h_disj =>
      exact Finset.disjoint_iff_inter_eq_empty.mpr h_disj
  }


------
-- Third Equation: |S_x| = sum |a_i|
------

-- The third equation is a bit more involved since we need to work with the projections.
-- But it again follows from a partitioning, this time from the fact that S_x is the union of all a_i.
lemma a_i_partitions_S_x (S: Finset point3) : (a S).biUnion id = S_x S := by
  {
    unfold a S_x project_set a_i projection Z_i
    ext a : 1
    simp_all only [Fin.isValue, Finset.mem_biUnion, Finset.mem_image, id_eq, exists_exists_and_eq_and,
      Finset.mem_filter]
    apply Iff.intro
    · intro a_1
      obtain ⟨w, h⟩ := a_1
      obtain ⟨_, right⟩ := h
      obtain ⟨w_1, h⟩ := right
      obtain ⟨left_1, right⟩ := h
      obtain ⟨left_1, _⟩ := left_1
      subst right
      apply Exists.intro
      · apply And.intro
        on_goal 2 => {rfl
        }
        · simp_all only
    · intro a_1
      obtain ⟨w, h⟩ := a_1
      obtain ⟨left, right⟩ := h
      subst right
      apply Exists.intro
      · apply And.intro
        · exact left
        · apply Exists.intro
          · apply And.intro
            on_goal 2 => {rfl
            }
            · simp_all only [and_self]

  }

theorem equation_3 (S: Finset point3) : (S_x S).card = ((a S).biUnion id).card := by
  -- The third equation follows from the fact that the a_i sets partition S_x.
  {
    have h := a_i_partitions_S_x S
    -- We already proved this.
    rw [h]
  }

-- I replaced the definition of a_card to instead use a multiset of cardinalities, which preserves duplicates.
theorem equation_3_new (S: Finset point3) : (S_x S).card = (a_card S).sum := by
  {
    rw [equation_3 S]
    unfold a_card
    set temp := (a S)
    -- unfold Finset.biUnion
    simp_all only [Finset.sum_map_val]

    have card_sum_biunion (ha: DecidableEq point3) (ha2: DecidableEq (Finset point3)) (F: Finset (Finset point3)) (hF: (SetLike.coe F).PairwiseDisjoint id) : ∑ e ∈ F, e.card = (F.biUnion id).card := by {
      induction F using Finset.induction_on with
        | empty => {
          simp
        }
        | insert x xs hxs ih => {
          simp_all only [Finset.coe_insert, not_false_eq_true, Finset.sum_insert]
          -- simp_all only [Finset.coe_insert, not_false_eq_true, Finset.sum_insert, Finset.biUnion_insert, id_eq]


          have helper (xs: Set (Finset point3)) (x: Set (Finset point3)) (hxs: xs.PairwiseDisjoint id) (hxx: x ⊆ xs) : x.PairwiseDisjoint id := by {
            exact Set.PairwiseDisjoint.subset hxs hxx
          }

          have hxs_disjoint : (SetLike.coe xs).PairwiseDisjoint id := by {
            apply helper (insert x (xs))
            · exact hF
            · exact Set.subset_insert x ↑xs
          }

          have h1 := ih hxs_disjoint

          rw [h1]

          have x_xs_disjoint : Disjoint x (xs.biUnion id) := by {
            refine (Finset.disjoint_biUnion_right x xs id).mpr ?_
            intro xs_ hxs_

            unfold Set.PairwiseDisjoint Set.Pairwise at hF
            have temp : x ∈ (insert x (SetLike.coe xs)) := by simp
            have temp2 : xs_ ∈ (insert x (SetLike.coe xs)) := by {
              simp
              exact Or.symm (Or.intro_left (xs_ = x) hxs_)
            }
            have temp3 : x ≠ xs_ := by {
              exact Ne.symm (ne_of_mem_of_not_mem hxs_ hxs)
            }

            exact hF temp temp2 temp3
          }
          simp_all only [imp_self, Finset.biUnion_insert, id_eq, Finset.card_union_of_disjoint]
        }
    }
    symm

    have temp1 : DecidableEq point3 := by {
      exact instDecidableEqOfLawfulBEq
    }
    have temp2 : DecidableEq (Finset point3) := by {
      exact instDecidableEqOfLawfulBEq
    }

    -- We can use the disjointness of a to use the result

    have temp_disjoint : (SetLike.coe temp).PairwiseDisjoint id := by {
      exact a_disjoint S
    }

    -- specialize result temp_disjoint
    exact card_sum_biunion instDecidableEqPoint3 temp2 temp temp_disjoint

  }


------
-- Equation 4: |Z_i| ≤ |a_i| * |b_i|
------

-- Equation 4 is the same as Equation 3, but with b instead of a and S_y instead of S_x.
-- The same logic just works.

lemma b_i_partitions_S_y (S: Finset point3) : (b S).biUnion id = S_y S := by
  {
    unfold b S_y project_set b_i projection Z_i
    ext a : 1
    simp_all only [Fin.isValue, Finset.mem_biUnion, Finset.mem_image, id_eq, exists_exists_and_eq_and,
      Finset.mem_filter]
    apply Iff.intro
    · intro a_1
      obtain ⟨w, h⟩ := a_1
      obtain ⟨_, right⟩ := h
      obtain ⟨w_1, h⟩ := right
      obtain ⟨left_1, right⟩ := h
      obtain ⟨left_1, _⟩ := left_1
      subst right
      apply Exists.intro
      · apply And.intro
        on_goal 2 => {rfl
        }
        · simp_all only
    · intro a_1
      obtain ⟨w, h⟩ := a_1
      obtain ⟨left, right⟩ := h
      subst right
      apply Exists.intro
      · apply And.intro
        · exact left
        · apply Exists.intro
          · apply And.intro
            on_goal 2 => {rfl
            }
            · simp_all only [and_self]

  }

theorem equation_4 (S: Finset point3) : (S_y S).card = ((b S).biUnion id).card := by
  -- The fourth equation follows from the fact that the b_i sets partition S_y.
  {
    have h := b_i_partitions_S_y S
    -- We already proved this.
    rw [h]
  }


-- Another Helper Lemma for equation 5.
lemma Z_preserves_mem_project_set (S w: Finset point3) (hw: w ∈ Z S) : project_set 2 w ⊆ project_set 2 S := by {
  unfold project_set
  intro a ap
  simp_all only [Fin.isValue, Finset.mem_image]
  obtain ⟨w_1, h⟩ := ap
  obtain ⟨left, right⟩ := h
  -- Maybe w_1 can just be used here?
  use w_1
  constructor
  · exact Z_S_mem_mem_S S w w_1 hw left
  · assumption
}

-- Yet another helper lemma for equation 5.
-- The idea is to show that an element of s_z must correspond to some element of Z_i S.
lemma s_z_mem_projected_Z_i (S: Finset point3) (s_z: point3) (hs_z: s_z ∈ S_z S) : ∃ z_i ∈ Z S, s_z ∈ project_set 2 z_i := by
  {
    have temp := project_set_mem S 2 s_z hs_z
    obtain ⟨w, hw, rfl⟩ := temp
    unfold Z Z_i project_set
    simp_all only [Fin.isValue, Finset.mem_image, exists_exists_and_eq_and, Finset.mem_filter]
    apply Exists.intro
    · apply And.intro
      · exact hw
      · apply Exists.intro
        · apply And.intro
          on_goal 2 => { rfl
          }
          · simp_all only [Fin.isValue, and_self]


  }

-- Helper lemma for equation 5: Z_i S (w 2) ⊆ S_z S for all w in S.
-- However, we want project_set ({Z_i S (w 2)}.biUnion id) 2 = S_z S
-- That is, when we project the union of all Z_i S onto the Z coordinate, we get S_z S
lemma projected_Z_i_partitions_S_Z (S: Finset point3): (Finset.image (fun zi => project_set 2 zi) (Z S)).biUnion id = S_z S := by
  {
    have fwd : (Z S).biUnion id = S := Z_i_partition S
    rw [← fwd]
    unfold S_z
    ext s_z

    simp_all only [Fin.isValue, Finset.mem_biUnion, Finset.mem_image, id_eq, exists_exists_and_eq_and]
    apply Iff.intro
    · intro a_1
      obtain ⟨w, h⟩ := a_1
      obtain ⟨left, right⟩ := h
      have fwd_2 : project_set 2 w ⊆ project_set 2 S := Z_preserves_mem_project_set S w left
      apply fwd_2
      simp_all only [Fin.isValue]
    · intro hs_z
      have temp := s_z_mem_projected_Z_i S s_z hs_z
      obtain ⟨z_i, hz_i, hs_z⟩ := temp
      apply Exists.intro
      · apply And.intro
        · exact hz_i
        · simp_all only [Fin.isValue]

  }

-- The fifth equation is a bit more complicated.
-- It says that each Z_i contains less elements than the entirety of S_z.
theorem equation_5 (S: Finset point3) : ∀ z_i ∈ Z S, (z_i.card: ℝ) ≤ ((S_z S).card: ℝ) := by
  {
    unfold Z
    intro z_i a

    simp_all only [ Finset.mem_image]
    obtain ⟨w, h⟩ := a
    obtain ⟨_, right⟩ := h
    subst right

    -- Another approach: project Z_i S (w 2) onto xy and show that that is a subset of S_z S.
    have middle_right: ((project_set 2 (Z_i S (w.snd.snd))).card: ℝ)  ≤ ((S_z S).card: ℝ) := by {
      simp
      refine Finset.card_le_card ?_
      unfold S_z
      have h1 : (Z_i S (w.snd.snd)) ⊆ S := by {
        unfold Z_i
        simp
      }
      have temp := project_set_subset (Z_i S (w.snd.snd)) S 2 h1
      assumption
    }


    -- We know middle_right, now we need left_middle.
    have left_middle: ((Z_i S (w.snd.snd)).card: ℝ) = (project_set 2 (Z_i S (w.snd.snd))).card := by {
      set z_i := (Z_i S (w.snd.snd))
      have z_i_is_zi := Z_i_is_Z_i_set S (w.snd.snd)

      have temp := project_set_Z_i_card z_i z_i_is_zi
      simp_all
    }
    exact le_of_eq_of_le left_middle middle_right


  }

-- Helper theorem for 6: multiply Equation 1 with 5.
lemma equation_1_and_5 (S Z_i: Finset point3) (hz_i: is_Z_i_set Z_i) (hz_i_in: Z_i ∈ Z S): (Z_i.card : ℝ)^2 ≤ ((S_z S).card: ℝ) * ((a_i_from_Z_i Z_i).card: ℝ) * ((b_i_from_Z_i Z_i).card: ℝ) := by
  {
    have eq1 := equation_1 Z_i hz_i
    have eq5 := equation_5 S Z_i hz_i_in
    have eq1_nonneg : 0 ≤ (Z_i.card: ℝ) := Nat.cast_nonneg' Z_i.card
    have a_nonneg : 0 ≤ ((a_i_from_Z_i Z_i).card : ℝ ) := Nat.cast_nonneg' (a_i_from_Z_i Z_i).card
    have b_nonneg : 0 ≤ ((b_i_from_Z_i Z_i).card : ℝ ) := Nat.cast_nonneg' (b_i_from_Z_i Z_i).card
    have a_b_nonneg := mul_nonneg a_nonneg b_nonneg
    have temp := mul_le_mul eq1 eq5 eq1_nonneg a_b_nonneg
    ring_nf at *
    assumption
  }

-- taking the square root of that
lemma equation_1_and_5_sqrt (S Z_i: Finset point3) (hz_i: is_Z_i_set Z_i) (hz_i_in: Z_i ∈ Z S): (Z_i.card: ℝ) ≤ ((((S_z S).card: ℝ) * ((a_i_from_Z_i Z_i).card: ℝ) * (b_i_from_Z_i Z_i).card)).sqrt := by
  {
    have h15 := equation_1_and_5 S Z_i hz_i hz_i_in
    -- exact Nat.le_sqrt'.mpr h15
    exact Real.le_sqrt_of_sq_le h15

  }

-- Helper lemma for equation 6: if for each of the elements of the set, an inequality holds, this extends to the sum.
lemma sum_inequality {α: Type*} {h: DecidableEq α} (f g: α → ℝ) (s: Finset α) (h: ∀ x ∈ s, f x ≤ g x) : (∑ x ∈ s, f x) ≤ (∑ x ∈ s, g x) := by
  {
    induction s using Finset.induction_on with
    | empty =>
      simp
    | insert a s ha ih =>
    {
      simp_all only [Finset.mem_insert, or_true, implies_true, forall_const, forall_eq_or_imp, not_false_eq_true,
        Finset.sum_insert]
      obtain ⟨left, _⟩ := h
      exact add_le_add left ih
    }

  }


-- Equation 6: the sum of the square roots of all Z_i is less than or equal to the sum of square roots of (a_i*a_b*|S_z|)
theorem equation_6 (S: Finset point3) : ∑ z_i ∈ Z S, (z_i.card: ℝ) ≤ ∑ z_i ∈ Z S, ((((S_z S).card: ℝ) * (a_i_from_Z_i z_i).card * (b_i_from_Z_i z_i).card)).sqrt := by
  {
    -- apply? gave the hint:
    -- (expose_names; refine sum_inequality Finset.card (fun x ↦ ((S_z S).card * (a_i_from_Z_i x).card * (b_i_from_Z_i x).card).sqrt) (Z S) ?_)

    -- refine sum_inequality () Finset.card (fun x ↦ (((S_z S).card * (a_i_from_Z_i x).card * (b_i_from_Z_i x).card)).sqrt) ?_ ?_
    apply sum_inequality
    · exact instDecidableEqOfLawfulBEq

    intro x a
    apply equation_1_and_5_sqrt
    · exact Z_are_Z_i_sets S x a
    · assumption
  }

-- Helper lemma for the rearranging: express that the S_Z can be pulled out.
lemma sum_prod {α: Type*} {hα : DecidableEq α} (f: α → ℝ) (s: Finset α) (g: ℝ) : (∑ x ∈ s, f x * g) = g * (∑ x ∈ s, f x):= by {
  induction s using Finset.induction_on with
  | empty =>
    simp
  | insert a s ha ih =>
  {
    simp_all only [not_false_eq_true, Finset.sum_insert]
    grind
  }

}

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

  exact instDecidableEqOfLawfulBEq

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


-- Next lemma on the way to equation 7:
-- sum of sqrt (a_i b_i) ≤ sqrt (sum a_i) * sqrt (sum b_i)

lemma sum_sqrt_le_sqrt_sum (S: Finset point3) : ∑ z_i ∈ Z S, √(((a_i_from_Z_i z_i).card: ℝ) * ((b_i_from_Z_i z_i).card: ℝ)) ≤ √(∑ z_i ∈ Z S, ((a_i_from_Z_i z_i).card: ℝ)) * √(∑ z_i ∈ Z S, ((b_i_from_Z_i z_i).card: ℝ)) := by {


  have a_i_rcard_noneg : ∀ z_i ∈ Z S, 0 ≤ ((a_i_from_Z_i z_i).card: ℝ) := by {
    exact fun z_i a ↦ Nat.cast_nonneg' (a_i_from_Z_i z_i).card
  }

  -- Ok, but why though?
  ------ Aristotle start --------
  -- Apply the Cauchy-Schwarz inequality to the sums.
  have h_cauchy_schwarz : ∀ (u v : Finset point3 → ℝ), (∑ z_i ∈ Z S, u z_i * v z_i) ^ 2 ≤ (∑ z_i ∈ Z S, u z_i ^ 2) * (∑ z_i ∈ Z S, v z_i ^ 2) := by
    exact fun u v ↦ Finset.sum_mul_sq_le_sq_mul_sq (Z S) u v;
  rw [ ← Real.sqrt_mul ];
  · refine Real.le_sqrt_of_sq_le ?_;
    convert h_cauchy_schwarz ( fun z_i => Real.sqrt ( a_i_from_Z_i z_i |> Finset.card : ℝ ) ) ( fun z_i => Real.sqrt ( b_i_from_Z_i z_i |> Finset.card : ℝ ) ) using 3 <;> norm_num [ Real.sqrt_mul, a_i_rcard_noneg ];
  · exact Finset.sum_nonneg a_i_rcard_noneg
  ------- Aristotle end --------




}

-- Helper lemma for setting up le_tran_mul_sqr in last lemma before equation 7:
-- The sum of non-negative reals is non-negative.
lemma sum_nonneg {α: Type*} {h: DecidableEq α} (f: α → ℝ) (s: Finset α) (h_nonneg: ∀ x ∈ s, 0 ≤ f x) : 0 ≤ (∑ x ∈ s, f x) := by {
  induction s using Finset.induction_on with
  | empty =>
    simp
  | insert a s ha ih =>
  {
    simp_all only [not_false_eq_true, Finset.sum_insert]
    simp_all only [Finset.mem_insert, or_true, implies_true, forall_const, forall_eq_or_imp]
    obtain ⟨left, _⟩ := h_nonneg
    exact Left.add_nonneg left ih
  }
}

-- Helper lemma for last lemma before equation 7:
lemma le_trans_mul_sqr {a b c d: ℝ} (hcd: 0 ≤ c) (hb: 0 ≤ b) (h1: a ≤ b * c ^2) (h2: c ≤ d) : a ≤ b * d ^ 2 := by {
  apply le_trans h1
  apply mul_le_mul
  · exact Preorder.le_refl b
  · exact square_inequality hcd h2
  · exact sq_nonneg c
  assumption
}

-- Last lemma before equation 7:
-- |S| ≤ |S_z| (sqrt(sum(a_i))*sqrt(sum(b_i)))^2
-- Which is basically just the previous two lemmas combined by transitivity.

lemma pre_7 (S: Finset point3) : (S.card: ℝ)^2 ≤ ((S_z S).card: ℝ) * (√(∑ z_i ∈ Z S, ((a_i_from_Z_i z_i).card: ℝ)) * √(∑ z_i ∈ Z S, ((b_i_from_Z_i z_i).card: ℝ)))^2 := by {
  have h1 := subst_2_6_sqr S
  have h2 := sum_sqrt_le_sqrt_sum S
  -- apply le_trans h1
  -- apply mul_le_mul
  -- simp
  -- exact?

  set inner := ∑ z_i ∈ Z S, √(((a_i_from_Z_i z_i).card: ℝ) * ((b_i_from_Z_i z_i).card: ℝ))

  -- Setting up the le_trans_mul_sqr
  have hcd : 0 ≤ inner := by {
    simp [inner]
    apply sum_nonneg
    · exact instDecidableEqOfLawfulBEq

    intro x _hx
    have left_nonneg :=  Real.sqrt_nonneg ((a_i_from_Z_i x).card: ℝ)
    have right_nonneg :=  Real.sqrt_nonneg ((b_i_from_Z_i x).card: ℝ)
    exact Left.mul_nonneg left_nonneg right_nonneg
  }

  have hb : 0 ≤ ((S_z S).card: ℝ) := by {
    exact Nat.cast_nonneg' (S_z S).card
  }

  exact le_trans_mul_sqr hcd hb h1 h2
}



-- Almost there: Equation 7:
-- |S|^2 ≤ |S_z| * (sum a_i) * (sum b_i)

theorem equation_7 (S: Finset point3) : (S.card: ℝ)^2 ≤ ((S_z S).card: ℝ) * (∑ z_i ∈ Z S, ((a_i_from_Z_i z_i).card: ℝ)) * (∑ z_i ∈ Z S, ((b_i_from_Z_i z_i).card: ℝ)) := by {
  let p_7 := pre_7 S

  -- abbreviating to get an overview
  set a := ∑ z_i ∈ Z S, ((a_i_from_Z_i z_i).card: ℝ)
  set b := ∑ z_i ∈ Z S, ((b_i_from_Z_i z_i).card: ℝ)

  convert_to (S.card: ℝ) ^ 2 ≤ ((S_z S).card: ℝ) * (√a * √b) ^ 2
  · ring_nf

    have a_nonneg : 0 ≤ a := by {
      simp [a]
      apply sum_nonneg
      · exact instDecidableEqOfLawfulBEq

      intro x _hx
      apply Nat.cast_nonneg'
    }
    have b_nonneg : 0 ≤ b := by {
      simp [b]
      apply sum_nonneg
      · exact instDecidableEqOfLawfulBEq

      intro x _hx
      apply Nat.cast_nonneg'
    }

    rw [Real.sq_sqrt]
    · rwa [Real.sq_sqrt]
    · assumption
  assumption
}

-- Give a way to translate equation 3 in equation 7
lemma e3_e7_translate (S: Finset point3) : (∑ z_i ∈ Z S, ((a_i_from_Z_i z_i).card: ℝ)) = (a_card S).sum := by {
  -- Note: the same translation for equation 4 to 7 was already done below, but there are some subtle differences.
  ------ Aristotle start --------
  -- By definition of `a_card`, we know that it is the sum of the cardinalities of the `a_i_from_Z_i` sets.
  have h_a_card_def : a_card S = (Z S).val.map (fun z => (a_i_from_Z_i z).card) := by
    unfold a_card a;
    -- Since $Z S$ is the image of $S$ under the function that maps each point to its $Z_i$ set, and $a_i S (p 2)$ is the image of $S$ under the function that maps each point to its $a_i$ set, these two images are equal.
    have h_eq : Finset.image (fun p => a_i S (p.snd.snd)) S = Finset.image (fun z => a_i_from_Z_i z) (Z S) := by
      unfold Z a_i_from_Z_i
      ext a : 1
      simp_all only [Fin.isValue, Finset.mem_image, exists_exists_and_eq_and]
      rfl
    rw [ h_eq, Finset.image_val ];
    -- Since the Z_i sets are disjoint, the image of a_i_from_Z_i over Z S is already deduplicated.
    have h_disjoint : ∀ z1 z2 : Finset point3, z1 ∈ Z S → z2 ∈ Z S → z1 ≠ z2 → Disjoint (a_i_from_Z_i z1) (a_i_from_Z_i z2) := by
      intros z1 z2 hz1 hz2 hneq
      apply Finset.disjoint_left.mpr;
      intro x hx1 hx2;
      obtain ⟨ p1, hp1, rfl ⟩ := Finset.mem_image.mp hx1
      obtain ⟨ p2, hp2, hp2_eq ⟩ := Finset.mem_image.mp hx2
      have h_proj_eq : projection 0 p1 = projection 0 p2 := by
        exact hp2_eq.symm;
      have h_proj_eq : p1.snd.fst = p2.snd.fst ∧ p1.snd.snd = p2.snd.snd := by
        -- exact ⟨ by simpa using congr_fun h_proj_eq 1, by simpa using congr_fun h_proj_eq 2 ⟩;
        unfold projection at h_proj_eq
        simp_all
      have h_proj_eq : z1 = z2 := by
        apply z_i_eq_if_proj_eq S z1 z2 hz1 hz2;
        exact ⟨ p1, hp1, p2, hp2, h_proj_eq.2 ⟩;
      contradiction;
    -- Since the Z_i sets are disjoint, the image of a_i_from_Z_i over Z S is already deduplicated. Therefore, the dedup of the image is just the image itself.
    have h_dedup : ∀ z1 z2 : Finset point3, z1 ∈ Z S → z2 ∈ Z S → a_i_from_Z_i z1 = a_i_from_Z_i z2 → z1 = z2 := by
      intros z1 z2 hz1 hz2 h_eq;
      specialize h_disjoint z1 z2 hz1 hz2;
      by_cases h : z1 = z2 <;> simp_all
      unfold a_i_from_Z_i at *
      simp_all only [Fin.isValue, Finset.image_eq_empty, not_true_eq_false]
    rw [ Multiset.dedup_eq_self.mpr ];
    · rw [ Multiset.map_map ];
      rfl;
    · exact Multiset.Nodup.map_on ( fun z1 hz1 z2 hz2 h => h_dedup z1 z2 hz1 hz2 h ) ( Finset.nodup _ );
  simp_all only [Finset.sum_map_val, Nat.cast_sum]
  ------- Aristotle end --------

}

-- Give a way to translate equation 4 in equation 7
lemma e4_e7_translate (S: Finset point3) : (∑ z_i ∈ (Z S), ((b_i_from_Z_i z_i).card: ℝ)) = ((b S).biUnion id).card := by {
  ------ Aristotle start --------
  -- By definition of $b$, we know that $(b S).biUnion id$ is the union of all $b_i$ sets.
  have hb_biUnion : (b S).biUnion id = Finset.biUnion (Z S) (fun z_i => b_i_from_Z_i z_i) := by
    ext
    simp [b]
    unfold b_i_from_Z_i b_i Z
    simp_all only [Fin.isValue, Finset.mem_image, Prod.exists, ↓existsAndEq, and_true]
  rw [ hb_biUnion, Finset.card_biUnion ]
  · simp_all only [Nat.cast_sum]
  intro x hx y hy hxy;
  -- Since $x$ and $y$ are distinct elements of $Z S$, they are Z_i sets with different z-coordinates.
  obtain ⟨r, hr⟩ : ∃ r, x = Z_i S r := by
    unfold Z at hx
    simp_all only [Finset.coe_image, Set.mem_image, Finset.mem_coe, ne_eq]
    obtain ⟨w, h⟩ := hx
    obtain ⟨_, right⟩ := h
    subst right
    simp_all only [exists_apply_eq_apply']
  obtain ⟨s, hs⟩ : ∃ s, y = Z_i S s := by
    unfold Z at hy
    subst hr
    simp_all only [Finset.coe_image, Set.mem_image, Finset.mem_coe, ne_eq]
    obtain ⟨w, h⟩ := hy
    obtain ⟨_, right⟩ := h
    subst right
    simp_all only [exists_apply_eq_apply']
  have hz : r ≠ s := by
    contrapose! hxy
    subst hxy hr hs
    rfl
  -- Since $r \neq s$, the projections of $x$ and $y$ onto the $yz$-plane are disjoint.
  have h_disjoint : ∀ p ∈ x, ∀ q ∈ y, projection 1 p ≠ projection 1 q := by
    -- intros p hp q hq h_eq; have := congr_fun h_eq 2
    -- simp_all +decide [ projection ]
    -- unfold Z_i at hp hq
    -- subst hr hs
    -- simp_all only [Fin.isValue, Finset.mem_filter, and_false]
    intros p hp q hq h_eq
    unfold projection at h_eq
    simp_all
    unfold Z_i at hp hq
    subst hr hs
    simp_all only [Finset.mem_filter, and_false]
  exact (Finset.disjoint_left.mpr fun p hp hp' =>
    by obtain ⟨ q, hq, rfl ⟩ := Finset.mem_image.mp hp; obtain ⟨ q', hq', hq'' ⟩ :=
    Finset.mem_image.mp hp'; specialize h_disjoint q hq q' hq'; subst hs hr; simp_all only [ne_eq, Fin.isValue, not_true_eq_false])

  ------- Aristotle end --------
}

-- Goal: Show that |S|^2 ≤ |S_x| * |S_y| * |S_z|
snip end

problem imo1992_p5 (S: Finset point3) : (S.card: ℝ)^2 ≤
  ((Finset.image (projection 0) S).card: ℝ) *
  ((Finset.image (projection 1) S).card: ℝ) *
  ((Finset.image (projection 2) S).card: ℝ) := by {
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

}

end Imo1992P5
