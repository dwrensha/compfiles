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

noncomputable instance : DecidableEq (ℝ × ℝ × ℝ) := Classical.decEq _

/-- Project onto yz-plane (zero out x) -/
private abbrev px (p : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ := (0, p.2.1, p.2.2)
/-- Project onto xz-plane (zero out y) -/
private abbrev py (p : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ := (p.1, 0, p.2.2)
/-- Project onto xy-plane (zero out z) -/
private abbrev pz (p : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ := (p.1, p.2.1, 0)

/-- The slice of S at z-coordinate r -/
private noncomputable def zslice (S : Finset (ℝ × ℝ × ℝ)) (r : ℝ) :=
  S.filter (·.2.2 = r)

/-- S is the disjoint union of its z-slices -/
private lemma card_sum_slices (S : Finset (ℝ × ℝ × ℝ)) :
    S.card = ∑ r ∈ S.image (·.2.2), (zslice S r).card := by
  have hunion : (S.image (·.2.2)).biUnion (zslice S) = S := by
    ext p; simp only [Finset.mem_biUnion, Finset.mem_image, zslice, Finset.mem_filter]
    exact ⟨fun ⟨_, ⟨_, _, _⟩, hp, _⟩ => hp, fun hp => ⟨_, ⟨_, hp, rfl⟩, hp, rfl⟩⟩
  calc S.card = ((S.image (·.2.2)).biUnion (zslice S)).card := by rw [hunion]
    _ = ∑ r ∈ S.image (·.2.2), (zslice S r).card := Finset.card_biUnion fun _ _ _ _ hr =>
        Finset.disjoint_left.mpr fun p h₁ h₂ => by
          simp only [zslice, Finset.mem_filter] at h₁ h₂
          exact hr (h₁.2.symm.trans h₂.2)

/-- Each z-slice injects into the product of its x- and y-projections -/
private lemma slice_le_prod (S : Finset (ℝ × ℝ × ℝ)) (r : ℝ) :
    (zslice S r).card ≤ ((zslice S r).image px).card * ((zslice S r).image py).card := by
  calc (zslice S r).card
      = ((zslice S r).image (fun p => (px p, py p))).card := by
          rw [Finset.card_image_of_injOn]
          intro a ha b hb hab
          simp only [zslice, Finset.mem_coe, Finset.mem_filter] at ha hb
          simp only [px, py, Prod.mk.injEq] at hab
          ext <;> simp_all
    _ ≤ ((zslice S r).image px ×ˢ (zslice S r).image py).card :=
          Finset.card_le_card (Finset.image_subset_iff.mpr fun p hp =>
            Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hp, Finset.mem_image_of_mem _ hp⟩)
    _ = ((zslice S r).image px).card * ((zslice S r).image py).card :=
          Finset.card_product ..

/-- Each z-slice has size ≤ |S_z| (pz is injective on each slice) -/
private lemma slice_le_sz (S : Finset (ℝ × ℝ × ℝ)) (r : ℝ) :
    (zslice S r).card ≤ (S.image pz).card := by
  calc (zslice S r).card
      = ((zslice S r).image pz).card := by
          rw [Finset.card_image_of_injOn]
          intro a ha b hb hab
          simp only [zslice, Finset.mem_coe, Finset.mem_filter] at ha hb
          simp only [pz, Prod.mk.injEq] at hab
          ext <;> simp_all
    _ ≤ (S.image pz).card :=
          Finset.card_le_card (Finset.image_subset_image (Finset.filter_subset _ _))

/-- px-images of different z-slices are disjoint (px preserves z-coordinate) -/
private lemma px_disjoint (S : Finset (ℝ × ℝ × ℝ)) {r₁ r₂ : ℝ} (hr : r₁ ≠ r₂) :
    Disjoint ((zslice S r₁).image px) ((zslice S r₂).image px) :=
  Finset.disjoint_left.mpr fun _ h₁ h₂ => by
    obtain ⟨p₁, hp₁, rfl⟩ := Finset.mem_image.mp h₁
    obtain ⟨p₂, hp₂, heq⟩ := Finset.mem_image.mp h₂
    simp only [zslice, Finset.mem_filter] at hp₁ hp₂
    simp only [px, Prod.mk.injEq] at heq
    exact absurd (hp₁.2.symm.trans (heq.2.2 ▸ hp₂.2)) hr

/-- py-images of different z-slices are disjoint -/
private lemma py_disjoint (S : Finset (ℝ × ℝ × ℝ)) {r₁ r₂ : ℝ} (hr : r₁ ≠ r₂) :
    Disjoint ((zslice S r₁).image py) ((zslice S r₂).image py) :=
  Finset.disjoint_left.mpr fun _ h₁ h₂ => by
    obtain ⟨p₁, hp₁, rfl⟩ := Finset.mem_image.mp h₁
    obtain ⟨p₂, hp₂, heq⟩ := Finset.mem_image.mp h₂
    simp only [zslice, Finset.mem_filter] at hp₁ hp₂
    simp only [py, Prod.mk.injEq] at heq
    exact absurd (hp₁.2.symm.trans (heq.2.2 ▸ hp₂.2)) hr

/-- Sum of |px-image of slice| ≤ |Sx| -/
private lemma sum_px_le (S : Finset (ℝ × ℝ × ℝ)) :
    ∑ r ∈ S.image (·.2.2), ((zslice S r).image px).card ≤ (S.image px).card := by
  rw [← Finset.card_biUnion fun _ h₁ _ h₂ h => px_disjoint S h]
  exact Finset.card_le_card (Finset.biUnion_subset_iff_forall_subset.mpr fun r _ =>
    Finset.image_subset_image (Finset.filter_subset _ _))

/-- Sum of |py-image of slice| ≤ |Sy| -/
private lemma sum_py_le (S : Finset (ℝ × ℝ × ℝ)) :
    ∑ r ∈ S.image (·.2.2), ((zslice S r).image py).card ≤ (S.image py).card := by
  rw [← Finset.card_biUnion fun _ h₁ _ h₂ h => py_disjoint S h]
  exact Finset.card_le_card (Finset.biUnion_subset_iff_forall_subset.mpr fun r _ =>
    Finset.image_subset_image (Finset.filter_subset _ _))

/-- Main inequality: |S|² ≤ |Sx| · |Sy| · |Sz| -/
private theorem main (S : Finset (ℝ × ℝ × ℝ)) :
    (S.card : ℝ) ^ 2 ≤ (S.image px).card * (S.image py).card * (S.image pz).card := by
  set R := S.image (·.2.2)
  set ar := fun r => (((zslice S r).image px).card : ℝ)
  set br := fun r => (((zslice S r).image py).card : ℝ)
  set sz := ((S.image pz).card : ℝ)
  -- Step 1: For each slice, |slice r|² ≤ |Sz| · ar · br
  have hslice : ∀ r ∈ R, ((zslice S r).card : ℝ) ≤ (sz * ar r * br r).sqrt := by
    intro r _
    apply Real.le_sqrt_of_sq_le
    calc ((zslice S r).card : ℝ) ^ 2
        = (zslice S r).card * (zslice S r).card := by ring
      _ ≤ sz * (ar r * br r) := by
          simp only [sz, ar, br]
          exact_mod_cast Nat.mul_le_mul (slice_le_sz S r) (slice_le_prod S r)
      _ = sz * ar r * br r := by ring
  -- Step 2: |S| ≤ √sz · Σ √(ar · br)
  have hS : (S.card : ℝ) ≤ sz.sqrt * ∑ r ∈ R, (ar r * br r).sqrt := by
    calc (S.card : ℝ) = ∑ r ∈ R, ((zslice S r).card : ℝ) := by
            exact_mod_cast card_sum_slices S
      _ ≤ ∑ r ∈ R, (sz * ar r * br r).sqrt := Finset.sum_le_sum hslice
      _ = ∑ r ∈ R, sz.sqrt * (ar r * br r).sqrt := by
            congr 1; ext r
            rw [show sz * ar r * br r = sz * (ar r * br r) from by ring,
                Real.sqrt_mul (Nat.cast_nonneg _)]
      _ = sz.sqrt * ∑ r ∈ R, (ar r * br r).sqrt := (Finset.mul_sum ..).symm
  -- Step 3: Square both sides: |S|² ≤ sz · (Σ √(ar · br))²
  have hS2 : (S.card : ℝ) ^ 2 ≤ sz * (∑ r ∈ R, (ar r * br r).sqrt) ^ 2 := by
    calc (S.card : ℝ) ^ 2
        ≤ (sz.sqrt * ∑ r ∈ R, (ar r * br r).sqrt) ^ 2 :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) hS 2
      _ = sz * (∑ r ∈ R, (ar r * br r).sqrt) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  -- Step 4: Cauchy-Schwarz: (Σ √(ar · br))² ≤ (Σ ar) · (Σ br)
  have hCS : (∑ r ∈ R, (ar r * br r).sqrt) ^ 2 ≤ (∑ r ∈ R, ar r) * (∑ r ∈ R, br r) := by
    calc (∑ r ∈ R, (ar r * br r).sqrt) ^ 2
        = (∑ r ∈ R, (ar r).sqrt * (br r).sqrt) ^ 2 := by
          congr 1; congr 1; ext r; exact Real.sqrt_mul (Nat.cast_nonneg _) _
      _ ≤ (∑ r ∈ R, (ar r).sqrt ^ 2) * (∑ r ∈ R, (br r).sqrt ^ 2) :=
          Finset.sum_mul_sq_le_sq_mul_sq R _ _
      _ = (∑ r ∈ R, ar r) * (∑ r ∈ R, br r) := by
          congr 1 <;> refine Finset.sum_congr rfl fun r _ => Real.sq_sqrt (Nat.cast_nonneg _)
  -- Step 5: Σ ar ≤ |Sx| and Σ br ≤ |Sy|
  have ha : ∑ r ∈ R, ar r ≤ (S.image px).card := by simp only [R, ar]; exact_mod_cast sum_px_le S
  have hb : ∑ r ∈ R, br r ≤ (S.image py).card := by simp only [R, br]; exact_mod_cast sum_py_le S
  -- Step 6: Combine
  calc (S.card : ℝ) ^ 2
      ≤ sz * (∑ r ∈ R, (ar r * br r).sqrt) ^ 2 := hS2
    _ ≤ sz * ((∑ r ∈ R, ar r) * (∑ r ∈ R, br r)) :=
        mul_le_mul_of_nonneg_left hCS (Nat.cast_nonneg _)
    _ ≤ sz * ((S.image px).card * (S.image py).card) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul ha hb (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _) (Nat.cast_nonneg _))
          (Nat.cast_nonneg _)
    _ = (S.image px).card * (S.image py).card * sz := by ring

snip end

problem imo1992_p5 (S: Finset (ℝ × ℝ × ℝ)) : S.card^2 ≤
    (Finset.image (fun p => ((0: ℝ) , p.2.1, p.2.2)) S).card *
    (Finset.image (fun p => (p.1, ((0: ℝ) , p.2.2))) S).card *
    (Finset.image (fun p => (p.1, p.2.1, (0: ℝ) )) S).card := by
  have h := main S
  exact_mod_cast h

end Imo1992P5
