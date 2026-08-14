/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Tactic
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Olympiad 2004, Problem 3

Define a "hook" to be a figure made up of six unit squares as shown below
in the picture (a 3 × 3 square with the centre square, the middle square
of one side, and a corner square adjacent to that middle square removed),
or any of the figures obtained by applying rotations and reflections to
this figure.

Which m × n rectangles can be tiled by hooks?
-/

namespace Imo2004P3

/-- The cells of an `m × n` rectangle, as a finite subset of `ℤ × ℤ`. -/
def rect (m n : ℕ) : Finset (ℤ × ℤ) :=
  ((Finset.range m) ×ˢ (Finset.range n)).image fun p => ((p.1 : ℤ), (p.2 : ℤ))

/-- The eight orientations of the hook (rotations and reflections of the
figure in the problem statement). Each orientation is a `3 × 3` square with
three cells removed: the centre cell, the middle cell of one side, and a
corner cell adjacent to that middle cell. -/
def hookShapes : Finset (Finset (ℤ × ℤ)) :=
  { {(0, 0), (0, 1), (0, 2), (1, 0), (1, 2), (2, 0)},
    {(0, 0), (0, 1), (0, 2), (1, 0), (1, 2), (2, 2)},
    {(0, 0), (0, 1), (0, 2), (1, 0), (2, 0), (2, 1)},
    {(0, 0), (0, 1), (1, 0), (2, 0), (2, 1), (2, 2)},
    {(0, 0), (1, 0), (1, 2), (2, 0), (2, 1), (2, 2)},
    {(0, 2), (1, 0), (1, 2), (2, 0), (2, 1), (2, 2)},
    {(0, 1), (0, 2), (1, 2), (2, 0), (2, 1), (2, 2)},
    {(0, 0), (0, 1), (0, 2), (1, 2), (2, 1), (2, 2)} }

/-- A hook is a translate of one of the eight orientations. -/
def IsHook (s : Finset (ℤ × ℤ)) : Prop := ∃ σ ∈ hookShapes, ∃ t, s = σ.image (· + t)

/-- The six orientations of the two-hook "tiles" (pairs of interlocking
hooks): the `3 × 4` rectangle, the `4 × 3` rectangle, and the four
orientations of the zigzag shape. -/
def tileShapes : Finset (Finset (ℤ × ℤ)) :=
  { {(0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (1, 1), (1, 2), (1, 3), (2, 0), (2, 1), (2, 2), (2, 3)},
    {(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2), (3, 0), (3, 1), (3, 2)},
    {(0, 1), (0, 2), (0, 3), (1, 1), (1, 2), (1, 3), (2, 0), (2, 1), (2, 2), (3, 0), (3, 1), (3, 2)},
    {(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 1), (2, 2), (2, 3), (3, 1), (3, 2), (3, 3)},
    {(0, 0), (0, 1), (1, 0), (1, 1), (1, 2), (1, 3), (2, 0), (2, 1), (2, 2), (2, 3), (3, 2), (3, 3)},
    {(0, 2), (0, 3), (1, 0), (1, 1), (1, 2), (1, 3), (2, 0), (2, 1), (2, 2), (2, 3), (3, 0), (3, 1)} }

/-- A tile is a translate of one of the six tile shapes. -/
def IsTile (s : Finset (ℤ × ℤ)) : Prop := ∃ τ ∈ tileShapes, ∃ t, s = τ.image (· + t)

/-- `R` can be tiled by hooks: there is a finite family of pairwise
disjoint hooks whose union is `R`. -/
def Tileable (R : Finset (ℤ × ℤ)) : Prop :=
  ∃ 𝒯 : Finset (Finset (ℤ × ℤ)), (∀ H ∈ 𝒯, IsHook H) ∧
    (∀ H₁ ∈ 𝒯, ∀ H₂ ∈ 𝒯, H₁ ≠ H₂ → Disjoint H₁ H₂) ∧ R = 𝒯.biUnion id

snip begin

/-- The lower-left corner of the bounding box of a set of cells. -/
def lo (s : Finset (ℤ × ℤ)) : ℤ × ℤ :=
  (((s.image Prod.fst).min).getD 0, ((s.image Prod.snd).min).getD 0)

/-- The "hole" (notch) of a hook: the centre cell of its bounding box. -/
def hole (s : Finset (ℤ × ℤ)) : ℤ × ℤ := lo s + (1, 1)

lemma mem_rect {m n : ℕ} {c : ℤ × ℤ} :
    c ∈ rect m n ↔ 0 ≤ c.1 ∧ c.1 < m ∧ 0 ≤ c.2 ∧ c.2 < n := by
  constructor
  · rintro h
    simp only [rect, Finset.mem_image, Finset.mem_product, Finset.mem_range] at h
    obtain ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩ := h
    dsimp only at *
    refine ⟨Nat.cast_nonneg _, by exact_mod_cast ha, Nat.cast_nonneg _, by exact_mod_cast hb⟩
  · rintro ⟨h1, h2, h3, h4⟩
    simp only [rect, Finset.mem_image, Finset.mem_product, Finset.mem_range]
    refine ⟨(c.1.toNat, c.2.toNat), ⟨?_, ?_⟩, ?_⟩
    · exact Int.toNat_lt (by omega) |>.mpr (by exact_mod_cast h2)
    · exact Int.toNat_lt (by omega) |>.mpr (by exact_mod_cast h4)
    · ext <;> simp [h1, h3]

lemma card_rect (m n : ℕ) : (rect m n).card = m * n := by
  have hinj : Function.Injective (fun p : ℕ × ℕ => ((p.1 : ℤ), (p.2 : ℤ))) := by
    rintro ⟨a1, b1⟩ ⟨a2, b2⟩ h
    simp only [Prod.mk.injEq, Int.natCast_inj] at h
    exact Prod.ext h.1 h.2
  rw [rect, Finset.card_image_of_injective _ hinj, Finset.card_product,
    Finset.card_range, Finset.card_range]

lemma lo_eq {s : Finset (ℤ × ℤ)} (hs : s.Nonempty) :
    lo s = ((s.image Prod.fst).min' (hs.image _), (s.image Prod.snd).min' (hs.image _)) := by
  have hget : ∀ (t : Finset ℤ) (ht : t.Nonempty), (t.min).getD 0 = t.min' ht := by
    intro t ht; rw [← Finset.coe_min' ht]; rfl
  rw [show lo s = (((s.image Prod.fst).min).getD 0, ((s.image Prod.snd).min).getD 0) from rfl,
    hget _ (hs.image _), hget _ (hs.image _)]

lemma min'_of_eq {A B : Finset ℤ} (hA : A.Nonempty) (hB : B.Nonempty) (h : A = B) :
    A.min' hA = B.min' hB := by
  subst h; rfl

lemma lo_translate {s : Finset (ℤ × ℤ)} (hs : s.Nonempty) (t : ℤ × ℤ) :
    lo (s.image (· + t)) = lo s + t := by
  have h1 : (s.image (· + t)).image Prod.fst = (s.image Prod.fst).image (· + t.1) := by
    rw [Finset.image_image, Finset.image_image]; rfl
  have h2 : (s.image (· + t)).image Prod.snd = (s.image Prod.snd).image (· + t.2) := by
    rw [Finset.image_image, Finset.image_image]; rfl
  have mono1 : Monotone (· + t.1) := monotone_id.add_const t.1
  have mono2 : Monotone (· + t.2) := monotone_id.add_const t.2
  rw [lo_eq (hs.image _), lo_eq hs,
    min'_of_eq _ ((hs.image Prod.fst).image _) h1,
    min'_of_eq _ ((hs.image Prod.snd).image _) h2,
    Finset.min'_image mono1 (s.image Prod.fst) ((hs.image Prod.fst).image _),
    Finset.min'_image mono2 (s.image Prod.snd) ((hs.image Prod.snd).image _)]
  ext <;> rfl

lemma hole_translate {s : Finset (ℤ × ℤ)} (hs : s.Nonempty) (t : ℤ × ℤ) :
    hole (s.image (· + t)) = hole s + t := by
  simp only [hole, lo_translate hs t, add_right_comm]

lemma shape_bounds : ∀ σ ∈ hookShapes, ∀ c ∈ σ,
    0 ≤ c.1 ∧ c.1 ≤ 2 ∧ 0 ≤ c.2 ∧ c.2 ≤ 2 := by
  decide

lemma shape_extremes : ∀ σ ∈ hookShapes,
    (∃ c ∈ σ, c.1 = 0) ∧ (∃ c ∈ σ, c.1 = 2) ∧ (∃ c ∈ σ, c.2 = 0) ∧ (∃ c ∈ σ, c.2 = 2) := by
  decide

lemma hole_shape : ∀ σ ∈ hookShapes, hole σ = (1, 1) := by
  decide

lemma hole_not_mem : ∀ σ ∈ hookShapes, hole σ ∉ σ := by
  decide

lemma card_hook : ∀ σ ∈ hookShapes, σ.card = 6 := by
  decide

/-- Every hook orientation contains cells two apart in some row. -/
lemma hook_row3 : ∀ σ ∈ hookShapes,
    ((σ.filter fun c => c.2 = 0).image Prod.fst ∩
      (σ.filter fun c => c.2 = 2).image Prod.fst).card ≠ 0 := by
  decide

/-- Every hook orientation contains cells two apart in some column. -/
lemma hook_col3 : ∀ σ ∈ hookShapes,
    ((σ.filter fun c => c.1 = 0).image Prod.snd ∩
      (σ.filter fun c => c.1 = 2).image Prod.snd).card ≠ 0 := by
  decide

/-- The key local fact. Suppose two disjoint hooks are such that the hole of
the first one is covered by the second one, and moreover the hole of the
second hook is either covered by the first hook or can be covered by a third
hook disjoint from both (as must happen in any tiling of a rectangle). Then
the hole of the second hook is covered by the first, and the union of the
two hooks is one of the six tiles. (Checked case by case.) -/
lemma pair_check :
    ∀ σ₁ ∈ hookShapes, ∀ σ₂ ∈ hookShapes,
      ∀ t ∈ (σ₂.image fun c => (1, 1) - c),
        Disjoint σ₁ (σ₂.image (· + t)) →
          ((1, 1) + t ∈ σ₁ ∨
            0 < (hookShapes.biUnion fun σ₃ =>
              (σ₃.image fun c => ((1, 1) + t) - c).filter fun t₃ =>
                Disjoint (σ₃.image (· + t₃)) (σ₁ ∪ (σ₂.image (· + t)))).card) →
          ((1, 1) + t ∈ σ₁) ∧
            0 < (tileShapes.filter fun τ =>
              σ₁ ∪ (σ₂.image (· + t)) =
                τ.image (· + (lo (σ₁ ∪ (σ₂.image (· + t))) - lo τ))).card := by
  decide +kernel

lemma tileable_empty : Tileable ∅ := ⟨∅, by simp, by simp, by simp⟩

lemma image_add_image (s : Finset (ℤ × ℤ)) (t u : ℤ × ℤ) :
    (s.image (· + t)).image (· + u) = s.image (· + (t + u)) := by
  rw [Finset.image_image]
  apply Finset.image_congr
  intro x _
  exact add_assoc x t u

lemma image_swap_add (s : Finset (ℤ × ℤ)) (t : ℤ × ℤ) :
    (s.image (· + t)).image Prod.swap = (s.image Prod.swap).image (· + Prod.swap t) := by
  rw [Finset.image_image, Finset.image_image]
  apply Finset.image_congr
  intro x _
  rfl

lemma isHook_translate {s : Finset (ℤ × ℤ)} (h : IsHook s) (u : ℤ × ℤ) :
    IsHook (s.image (· + u)) := by
  obtain ⟨σ, hσ, t, rfl⟩ := h
  exact ⟨σ, hσ, t + u, image_add_image σ t u⟩

/-- The hook orientations are closed under transposition (which is one of
the eight symmetries of the square). -/
lemma hookShapes_swap : ∀ σ ∈ hookShapes,
    0 < (hookShapes.filter fun σ' =>
      σ.image Prod.swap = σ'.image (· + (lo (σ.image Prod.swap) - lo σ'))).card := by
  decide

lemma isHook_swap {s : Finset (ℤ × ℤ)} (h : IsHook s) : IsHook (s.image Prod.swap) := by
  obtain ⟨σ, hσ, t, rfl⟩ := h
  have hc := hookShapes_swap σ hσ
  rw [Finset.card_pos] at hc
  obtain ⟨σ', hσ'⟩ := hc
  rw [Finset.mem_filter] at hσ'
  obtain ⟨hσ'mem, hσ'eq⟩ := hσ'
  refine ⟨σ', hσ'mem, (lo (σ.image Prod.swap) - lo σ') + Prod.swap t, ?_⟩
  calc (σ.image (· + t)).image Prod.swap
      = (σ.image Prod.swap).image (· + Prod.swap t) := image_swap_add σ t
    _ = (σ'.image (· + (lo (σ.image Prod.swap) - lo σ'))).image (· + Prod.swap t) := by
        conv_lhs => rw [hσ'eq]
    _ = σ'.image (· + ((lo (σ.image Prod.swap) - lo σ') + Prod.swap t)) := image_add_image _ _ _

lemma biUnion_image_translate (𝒯 : Finset (Finset (ℤ × ℤ))) (u : ℤ × ℤ) :
    (𝒯.image (fun H => H.image (· + u))).biUnion id = (𝒯.biUnion id).image (· + u) := by
  ext x
  simp only [Finset.mem_biUnion, Finset.mem_image, id]
  constructor
  · rintro ⟨H', hH', hx⟩
    obtain ⟨H, hH, rfl⟩ := hH'
    obtain ⟨x₀, hx₀, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨x₀, ⟨H, hH, hx₀⟩, rfl⟩
  · rintro ⟨x₀, ⟨H, hH, hx₀⟩, rfl⟩
    exact ⟨H.image (· + u), ⟨H, hH, rfl⟩, Finset.mem_image.mpr ⟨x₀, hx₀, rfl⟩⟩

lemma biUnion_image_swap (𝒯 : Finset (Finset (ℤ × ℤ))) :
    (𝒯.image (fun H => H.image Prod.swap)).biUnion id = (𝒯.biUnion id).image Prod.swap := by
  ext x
  simp only [Finset.mem_biUnion, Finset.mem_image, id]
  constructor
  · rintro ⟨H', hH', hx⟩
    obtain ⟨H, hH, rfl⟩ := hH'
    obtain ⟨x₀, hx₀, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨x₀, ⟨H, hH, hx₀⟩, rfl⟩
  · rintro ⟨x₀, ⟨H, hH, hx₀⟩, rfl⟩
    exact ⟨H.image Prod.swap, ⟨H, hH, rfl⟩, Finset.mem_image.mpr ⟨x₀, hx₀, rfl⟩⟩

lemma tileable_translate {R : Finset (ℤ × ℤ)} (hR : Tileable R) (u : ℤ × ℤ) :
    Tileable (R.image (· + u)) := by
  obtain ⟨𝒯, hh, hd, hU⟩ := hR
  refine ⟨𝒯.image (fun H => H.image (· + u)), ?_, ?_, ?_⟩
  · intro H' hH'
    rw [Finset.mem_image] at hH'
    obtain ⟨H, hH, rfl⟩ := hH'
    exact isHook_translate (hh H hH) u
  · intro H₁' hH₁' H₂' hH₂' hne
    rw [Finset.mem_image] at hH₁' hH₂'
    obtain ⟨H₁, hH₁, rfl⟩ := hH₁'
    obtain ⟨H₂, hH₂, rfl⟩ := hH₂'
    have hne12 : H₁ ≠ H₂ := fun heq => hne (by rw [heq])
    have hd12 := hd H₁ hH₁ H₂ hH₂ hne12
    rw [Finset.disjoint_left] at hd12 ⊢
    rintro x hx1 hx2
    simp only [Finset.mem_image] at hx1 hx2
    obtain ⟨a, ha, rfl⟩ := hx1
    obtain ⟨b, hb, hab⟩ := hx2
    have hab' : b = a := add_right_cancel hab
    exact hd12 ha (hab' ▸ hb)
  · rw [biUnion_image_translate, hU]

lemma tileable_union {R₁ R₂ : Finset (ℤ × ℤ)} (hd : Disjoint R₁ R₂)
    (h1 : Tileable R₁) (h2 : Tileable R₂) : Tileable (R₁ ∪ R₂) := by
  obtain ⟨𝒯₁, hh1, hd1, hU1⟩ := h1
  obtain ⟨𝒯₂, hh2, hd2, hU2⟩ := h2
  refine ⟨𝒯₁ ∪ 𝒯₂, ?_, ?_, ?_⟩
  · rintro H hH
    rcases Finset.mem_union.mp hH with hH | hH
    · exact hh1 H hH
    · exact hh2 H hH
  · rintro H₁ hH₁ H₂ hH₂ hne
    rcases Finset.mem_union.mp hH₁ with h1' | h1' <;> rcases Finset.mem_union.mp hH₂ with h2' | h2'
    · exact hd1 H₁ h1' H₂ h2' hne
    · have s1 : H₁ ⊆ R₁ := by rw [hU1]; exact Finset.subset_biUnion_of_mem id h1'
      have s2 : H₂ ⊆ R₂ := by rw [hU2]; exact Finset.subset_biUnion_of_mem id h2'
      exact Disjoint.mono s1 s2 hd
    · have s1 : H₁ ⊆ R₂ := by rw [hU2]; exact Finset.subset_biUnion_of_mem id h1'
      have s2 : H₂ ⊆ R₁ := by rw [hU1]; exact Finset.subset_biUnion_of_mem id h2'
      exact Disjoint.mono s1 s2 hd.symm
    · exact hd2 H₁ h1' H₂ h2' hne
  · rw [Finset.union_biUnion, ← hU1, ← hU2]

lemma rect_zero_left (n : ℕ) : rect 0 n = ∅ := by simp [rect]

lemma rect_zero_right (m : ℕ) : rect m 0 = ∅ := by simp [rect]

lemma rect_add_rows (m₁ m₂ n : ℕ) :
    rect (m₁ + m₂) n = rect m₁ n ∪ (rect m₂ n).image (· + ((m₁ : ℤ), 0)) := by
  ext c
  simp only [mem_rect, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro ⟨h0, h1, h2, h3⟩
    by_cases hc : c.1 < (m₁ : ℤ)
    · exact Or.inl ⟨h0, hc, h2, h3⟩
    · refine Or.inr ⟨(c.1 - m₁, c.2), ⟨by omega, by omega, by omega, by omega⟩, ?_⟩
      ext <;> simp
  · rintro (⟨h0, h1, h2, h3⟩ | ⟨x, hx, rfl⟩)
    · exact ⟨h0, by omega, h2, h3⟩
    · obtain ⟨hx0, hx1, hx2, hx3⟩ := hx
      have g1 : (x + ((m₁ : ℤ), 0)).1 = x.1 + (m₁ : ℤ) := rfl
      have g2 : (x + ((m₁ : ℤ), 0)).2 = x.2 := add_zero _
      rw [g1, g2]
      exact ⟨by omega, by omega, by omega, by omega⟩

lemma rect_add_rows_disjoint (m₁ m₂ n : ℕ) :
    Disjoint (rect m₁ n) ((rect m₂ n).image (· + ((m₁ : ℤ), 0))) := by
  rw [Finset.disjoint_left]
  rintro c hc1 hc2
  rw [mem_rect] at hc1
  simp only [Finset.mem_image] at hc2
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := hc2
  rw [mem_rect] at hab
  have key : a + (m₁ : ℤ) < (m₁ : ℤ) := hc1.2.1
  have ha0 : 0 ≤ a := hab.1
  omega

lemma rect_add_cols (m n₁ n₂ : ℕ) :
    rect m (n₁ + n₂) = rect m n₁ ∪ (rect m n₂).image (· + (0, (n₁ : ℤ))) := by
  ext c
  simp only [mem_rect, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro ⟨h0, h1, h2, h3⟩
    by_cases hc : c.2 < (n₁ : ℤ)
    · exact Or.inl ⟨h0, h1, h2, hc⟩
    · refine Or.inr ⟨(c.1, c.2 - n₁), ⟨by omega, by omega, by omega, by omega⟩, ?_⟩
      ext <;> simp
  · rintro (⟨h0, h1, h2, h3⟩ | ⟨x, hx, rfl⟩)
    · exact ⟨h0, h1, h2, by omega⟩
    · obtain ⟨hx0, hx1, hx2, hx3⟩ := hx
      have g1 : (x + (0, (n₁ : ℤ))).1 = x.1 := add_zero _
      have g2 : (x + (0, (n₁ : ℤ))).2 = x.2 + (n₁ : ℤ) := rfl
      rw [g1, g2]
      exact ⟨by omega, by omega, by omega, by omega⟩

lemma rect_add_cols_disjoint (m n₁ n₂ : ℕ) :
    Disjoint (rect m n₁) ((rect m n₂).image (· + (0, (n₁ : ℤ)))) := by
  rw [Finset.disjoint_left]
  rintro c hc1 hc2
  rw [mem_rect] at hc1
  simp only [Finset.mem_image] at hc2
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := hc2
  rw [mem_rect] at hab
  have key : b + (n₁ : ℤ) < (n₁ : ℤ) := hc1.2.2.2
  have hb0 : 0 ≤ b := hab.2.2.1
  omega

lemma tileable_mul_rows {a n : ℕ} (h : Tileable (rect a n)) : ∀ k, Tileable (rect (k * a) n) := by
  intro k
  induction k with
  | zero => rw [Nat.zero_mul, rect_zero_left]; exact tileable_empty
  | succ k ih =>
      rw [Nat.succ_mul, rect_add_rows]
      exact tileable_union (rect_add_rows_disjoint _ _ _) ih (tileable_translate h _)

lemma tileable_mul_cols {a n : ℕ} (h : Tileable (rect a n)) : ∀ l, Tileable (rect a (l * n)) := by
  intro l
  induction l with
  | zero => rw [Nat.zero_mul, rect_zero_right]; exact tileable_empty
  | succ l ih =>
      rw [Nat.succ_mul, rect_add_cols]
      exact tileable_union (rect_add_cols_disjoint _ _ _) ih (tileable_translate h _)

lemma tileable_mul {a b : ℕ} (h : Tileable (rect a b)) (k l : ℕ) :
    Tileable (rect (k * a) (l * b)) :=
  tileable_mul_cols (tileable_mul_rows h k) l

lemma rect_transpose (m n : ℕ) : (rect m n).image Prod.swap = rect n m := by
  ext c
  simp only [Finset.mem_image, mem_rect]
  constructor
  · rintro ⟨⟨a, b⟩, ⟨h0, h1, h2, h3⟩, rfl⟩
    exact ⟨h2, h3, h0, h1⟩
  · rintro ⟨h0, h1, h2, h3⟩
    exact ⟨(c.2, c.1), ⟨h2, h3, h0, h1⟩, rfl⟩

lemma tileable_swap {R : Finset (ℤ × ℤ)} (hR : Tileable R) : Tileable (R.image Prod.swap) := by
  obtain ⟨𝒯, hh, hd, hU⟩ := hR
  refine ⟨𝒯.image (fun H => H.image Prod.swap), ?_, ?_, ?_⟩
  · intro H' hH'
    rw [Finset.mem_image] at hH'
    obtain ⟨H, hH, rfl⟩ := hH'
    exact isHook_swap (hh H hH)
  · intro H₁' hH₁' H₂' hH₂' hne
    rw [Finset.mem_image] at hH₁' hH₂'
    obtain ⟨H₁, hH₁, rfl⟩ := hH₁'
    obtain ⟨H₂, hH₂, rfl⟩ := hH₂'
    have hne12 : H₁ ≠ H₂ := fun heq => hne (by rw [heq])
    have hd12 := hd H₁ hH₁ H₂ hH₂ hne12
    rw [Finset.disjoint_left] at hd12 ⊢
    rintro x hx1 hx2
    simp only [Finset.mem_image] at hx1 hx2
    obtain ⟨a, ha, rfl⟩ := hx1
    obtain ⟨b, hb, hab⟩ := hx2
    have hab' : b = a := Prod.swap_injective hab
    exact hd12 ha (hab' ▸ hb)
  · rw [biUnion_image_swap, hU]

lemma tileable_transpose {m n : ℕ} (h : Tileable (rect m n)) : Tileable (rect n m) := by
  rw [← rect_transpose]
  exact tileable_swap h

/-- Two hooks tile a `3 × 4` rectangle. -/
lemma tileable_3_4 : Tileable (rect 3 4) := by
  have h1 : IsHook ({(0, 0), (0, 1), (0, 2), (1, 0), (1, 2), (2, 0)} : Finset (ℤ × ℤ)) := by
    refine ⟨{(0, 0), (0, 1), (0, 2), (1, 0), (1, 2), (2, 0)}, by decide, (0, 0), ?_⟩
    decide
  have h2 : IsHook ({(0, 3), (1, 1), (1, 3), (2, 1), (2, 2), (2, 3)} : Finset (ℤ × ℤ)) := by
    refine ⟨{(0, 2), (1, 0), (1, 2), (2, 0), (2, 1), (2, 2)}, by decide, (0, 1), ?_⟩
    decide
  refine ⟨{ {(0, 0), (0, 1), (0, 2), (1, 0), (1, 2), (2, 0)},
            {(0, 3), (1, 1), (1, 3), (2, 1), (2, 2), (2, 3)} }, ?_, ?_, ?_⟩
  · intro H hH
    fin_cases hH <;> assumption
  · intro H₁ hH₁ H₂ hH₂ hne
    fin_cases hH₁ <;> fin_cases hH₂ <;> first | contradiction | decide
  · decide

/-- Every natural number other than `1, 2, 5` is a sum of `3`s and `4`s. -/
lemma nat_3_4 {n : ℕ} (h : n ≠ 1 ∧ n ≠ 2 ∧ n ≠ 5) : ∃ a b, n = 3 * a + 4 * b := by
  have h3 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases h3 with h3 | h3 | h3
  · exact ⟨n / 3, 0, by omega⟩
  · exact ⟨n / 3 - 1, 1, by omega⟩
  · exact ⟨n / 3 - 2, 2, by omega⟩

/-- A `12 × n` rectangle with `n ∉ {1, 2, 5}` is tileable. -/
lemma tileable_12j (j : ℕ) {n : ℕ} (h2 : n ≠ 1 ∧ n ≠ 2 ∧ n ≠ 5) :
    Tileable (rect (12 * j) n) := by
  obtain ⟨a, b, rfl⟩ := nat_3_4 h2
  have h123 : Tileable (rect 12 3) := tileable_transpose (tileable_mul_cols tileable_3_4 3)
  have h124 : Tileable (rect 12 4) :=
    tileable_transpose (tileable_mul_cols (tileable_transpose tileable_3_4) 4)
  rw [rect_add_cols]
  apply tileable_union (rect_add_cols_disjoint _ _ _)
  · have h := tileable_mul h123 j a
    rw [mul_comm j 12, mul_comm a 3] at h
    exact h
  · have h := tileable_mul h124 j b
    rw [mul_comm j 12, mul_comm b 4] at h
    exact tileable_translate h _

/-- Sufficiency: every rectangle satisfying the conditions is tileable. -/
lemma tileable_of_conditions {m n : ℕ}
    (h1 : m ≠ 1 ∧ m ≠ 2 ∧ m ≠ 5) (h2 : n ≠ 1 ∧ n ≠ 2 ∧ n ≠ 5)
    (h3 : 3 ∣ m ∨ 3 ∣ n) (h4 : 4 ∣ m ∨ 4 ∣ n) :
    Tileable (rect m n) := by
  rcases h3 with h3m | h3n
  · rcases h4 with h4m | h4n
    · -- 3 ∣ m and 4 ∣ m
      by_cases h3n' : 3 ∣ n
      · obtain ⟨l, rfl⟩ := h3n'
        obtain ⟨p, hp⟩ := h4m
        rw [hp, mul_comm 4 p, mul_comm 3 l]
        exact tileable_transpose (tileable_mul tileable_3_4 l p)
      · by_cases h4n' : 4 ∣ n
        · obtain ⟨k, rfl⟩ := h3m
          obtain ⟨q, rfl⟩ := h4n'
          rw [mul_comm 3 k, mul_comm 4 q]
          exact tileable_mul tileable_3_4 k q
        · -- 12 ∣ m and n ∉ {1,2,5}
          obtain ⟨k, rfl⟩ := h3m
          obtain ⟨p, hp⟩ := h4m
          have hk4 : 4 ∣ k :=
            Nat.Coprime.dvd_of_dvd_mul_left (by decide : Nat.Coprime 4 3) ⟨p, hp⟩
          obtain ⟨j, rfl⟩ := hk4
          have e : 3 * (4 * j) = 12 * j := by ring
          rw [e]
          exact tileable_12j j h2
    · -- 3 ∣ m and 4 ∣ n
      obtain ⟨k, rfl⟩ := h3m
      obtain ⟨q, rfl⟩ := h4n
      rw [mul_comm 3 k, mul_comm 4 q]
      exact tileable_mul tileable_3_4 k q
  · rcases h4 with h4m | h4n
    · -- 3 ∣ n and 4 ∣ m
      obtain ⟨l, rfl⟩ := h3n
      obtain ⟨p, hp⟩ := h4m
      rw [hp, mul_comm 4 p, mul_comm 3 l]
      exact tileable_transpose (tileable_mul tileable_3_4 l p)
    · -- 3 ∣ n and 4 ∣ n
      by_cases h3m' : 3 ∣ m
      · obtain ⟨k, rfl⟩ := h3m'
        obtain ⟨q, rfl⟩ := h4n
        rw [mul_comm 3 k, mul_comm 4 q]
        exact tileable_mul tileable_3_4 k q
      · by_cases h4m' : 4 ∣ m
        · obtain ⟨l, rfl⟩ := h3n
          obtain ⟨p, hp⟩ := h4m'
          rw [hp, mul_comm 4 p, mul_comm 3 l]
          exact tileable_transpose (tileable_mul tileable_3_4 l p)
        · -- 12 ∣ n and m ∉ {1,2,5}
          obtain ⟨l, rfl⟩ := h3n
          obtain ⟨q, hq⟩ := h4n
          have hl4 : 4 ∣ l :=
            Nat.Coprime.dvd_of_dvd_mul_left (by decide : Nat.Coprime 4 3) ⟨q, hq⟩
          obtain ⟨j, rfl⟩ := hl4
          have e : 3 * (4 * j) = 12 * j := by ring
          rw [e]
          exact tileable_transpose (tileable_12j j h1)

lemma shape_nonempty : ∀ σ ∈ hookShapes, σ.Nonempty := by
  intro σ hσ
  rw [← Finset.card_pos, card_hook σ hσ]
  norm_num

lemma isHook_nonempty {s : Finset (ℤ × ℤ)} (h : IsHook s) : s.Nonempty := by
  obtain ⟨σ, hσ, t, rfl⟩ := h
  exact (shape_nonempty σ hσ).image _

lemma isHook_card {s : Finset (ℤ × ℤ)} (h : IsHook s) : s.card = 6 := by
  obtain ⟨σ, hσ, t, rfl⟩ := h
  rw [Finset.card_image_of_injective _ (fun _ _ hab => add_right_cancel hab)]
  exact card_hook σ hσ

lemma hole_image (σ : Finset (ℤ × ℤ)) (hσ : σ ∈ hookShapes) (t : ℤ × ℤ) :
    hole (σ.image (· + t)) = (1, 1) + t := by
  rw [hole_translate (shape_nonempty σ hσ) t, hole_shape σ hσ]

lemma hole_not_mem_of_hook {s : Finset (ℤ × ℤ)} (h : IsHook s) : hole s ∉ s := by
  obtain ⟨σ, hσ, t, rfl⟩ := h
  rw [hole_image σ hσ t]
  intro hmem
  rw [Finset.mem_image] at hmem
  obtain ⟨c, hc, hct⟩ := hmem
  have hc11 : c = (1, 1) := add_right_cancel hct
  rw [hc11] at hc
  have hnm := hole_not_mem σ hσ
  rw [hole_shape σ hσ] at hnm
  exact hnm hc

lemma hole_mem_rect_of_hook {m n : ℕ} {s : Finset (ℤ × ℤ)} (h : IsHook s)
    (hsub : s ⊆ rect m n) : hole s ∈ rect m n := by
  obtain ⟨σ, hσ, t, rfl⟩ := h
  rw [hole_image σ hσ t, mem_rect]
  obtain ⟨h00, h02, hc0, hc2⟩ := shape_extremes σ hσ
  obtain ⟨c00, hc00, e00⟩ := h00
  obtain ⟨c02, hc02, e02⟩ := h02
  obtain ⟨cc0, hcc0, ec0⟩ := hc0
  obtain ⟨cc2, hcc2, ec2⟩ := hc2
  have m00 := hsub (Finset.mem_image.mpr ⟨c00, hc00, rfl⟩)
  have m02 := hsub (Finset.mem_image.mpr ⟨c02, hc02, rfl⟩)
  have mc0 := hsub (Finset.mem_image.mpr ⟨cc0, hcc0, rfl⟩)
  have mc2 := hsub (Finset.mem_image.mpr ⟨cc2, hcc2, rfl⟩)
  rw [mem_rect] at m00 m02 mc0 mc2
  simp only [Prod.fst_add, Prod.snd_add] at m00 m02 mc0 mc2 ⊢
  refine ⟨by omega, by omega, by omega, by omega⟩

/-- The pairing lemma in its general form: in any tiling, the partner of a
hook (the hook covering its hole) has its hole covered by the first hook,
and the two hooks together form a tile. -/
lemma pair_general {H₁ H₂ : Finset (ℤ × ℤ)} (h1 : IsHook H₁) (h2 : IsHook H₂)
    (hd : Disjoint H₁ H₂) (hh : hole H₁ ∈ H₂)
    (h3 : hole H₂ ∈ H₁ ∨ ∃ H₃ : Finset (ℤ × ℤ), IsHook H₃ ∧ Disjoint H₃ (H₁ ∪ H₂) ∧
      hole H₂ ∈ H₃) :
    hole H₂ ∈ H₁ ∧ IsTile (H₁ ∪ H₂) := by
  obtain ⟨σ₁, hσ₁, t₁, rfl⟩ := h1
  obtain ⟨σ₂, hσ₂, t₂, rfl⟩ := h2
  rw [hole_image σ₁ hσ₁ t₁] at hh
  have ht_mem : t₂ - t₁ ∈ σ₂.image (fun c => (1, 1) - c) := by
    rw [Finset.mem_image] at hh
    obtain ⟨c₂, hc₂, hct⟩ := hh
    refine Finset.mem_image.mpr ⟨c₂, hc₂, ?_⟩
    have e1 : c₂.1 + t₂.1 = 1 + t₁.1 := by have := congrArg Prod.fst hct; simpa using this
    have e2 : c₂.2 + t₂.2 = 1 + t₁.2 := by have := congrArg Prod.snd hct; simpa using this
    ext <;> simp <;> omega
  have hdisj : Disjoint σ₁ (σ₂.image (· + (t₂ - t₁))) := by
    have e : σ₂.image (· + t₂) = (σ₂.image (· + (t₂ - t₁))).image (· + t₁) := by
      rw [image_add_image]
      apply Finset.image_congr
      intro y _
      rw [sub_add_cancel]
    rw [Finset.disjoint_left] at hd ⊢
    intro x hx1 hx2
    exact hd (Finset.mem_image.mpr ⟨x, hx1, rfl⟩)
      (by rw [e]; exact Finset.mem_image.mpr ⟨x, hx2, rfl⟩)
  have h3' : (1, 1) + (t₂ - t₁) ∈ σ₁ ∨
      0 < (hookShapes.biUnion fun σ₃ =>
        (σ₃.image fun c => ((1, 1) + (t₂ - t₁)) - c).filter fun t₃ =>
          Disjoint (σ₃.image (· + t₃)) (σ₁ ∪ σ₂.image (· + (t₂ - t₁)))).card := by
    rcases h3 with h3l | h3r
    · left
      rw [hole_image σ₂ hσ₂ t₂, Finset.mem_image] at h3l
      obtain ⟨c₁, hc₁, hct⟩ := h3l
      have hc₁' : c₁ = (1, 1) + (t₂ - t₁) := by
        have e1 : c₁.1 + t₁.1 = 1 + t₂.1 := by have := congrArg Prod.fst hct; simpa using this
        have e2 : c₁.2 + t₁.2 = 1 + t₂.2 := by have := congrArg Prod.snd hct; simpa using this
        ext <;> simp <;> omega
      rw [hc₁'] at hc₁
      exact hc₁
    · right
      obtain ⟨H₃, hh3, hd3, hhmem⟩ := h3r
      obtain ⟨σ₃, hσ₃, t₃, rfl⟩ := hh3
      rw [hole_image σ₂ hσ₂ t₂, Finset.mem_image] at hhmem
      obtain ⟨c₃, hc₃, hct⟩ := hhmem
      have ht3 : t₃ - t₁ ∈ σ₃.image (fun c => ((1, 1) + (t₂ - t₁)) - c) := by
        refine Finset.mem_image.mpr ⟨c₃, hc₃, ?_⟩
        have e1 : c₃.1 + t₃.1 = 1 + t₂.1 := by have := congrArg Prod.fst hct; simpa using this
        have e2 : c₃.2 + t₃.2 = 1 + t₂.2 := by have := congrArg Prod.snd hct; simpa using this
        ext <;> simp <;> omega
      have hdisj3 : Disjoint (σ₃.image (· + (t₃ - t₁)))
          (σ₁ ∪ σ₂.image (· + (t₂ - t₁))) := by
        have e3 : σ₃.image (· + t₃) = (σ₃.image (· + (t₃ - t₁))).image (· + t₁) := by
          rw [image_add_image]
          apply Finset.image_congr
          intro y _
          rw [sub_add_cancel]
        have eu : (σ₁.image (· + t₁)) ∪ (σ₂.image (· + t₂)) =
            (σ₁ ∪ σ₂.image (· + (t₂ - t₁))).image (· + t₁) := by
          rw [Finset.image_union]
          congr 1
          rw [image_add_image]
          apply Finset.image_congr
          intro y _
          rw [sub_add_cancel]
        rw [Finset.disjoint_left] at hd3 ⊢
        intro x hx1 hx2
        exact hd3 (by rw [e3]; exact Finset.mem_image.mpr ⟨x, hx1, rfl⟩)
          (by rw [eu]; exact Finset.mem_image.mpr ⟨x, hx2, rfl⟩)
      apply Finset.card_pos.mpr
      refine ⟨t₃ - t₁, ?_⟩
      rw [Finset.mem_biUnion]
      exact ⟨σ₃, hσ₃, by rw [Finset.mem_filter]; exact ⟨ht3, hdisj3⟩⟩
  obtain ⟨g1, g2⟩ := pair_check σ₁ hσ₁ σ₂ hσ₂ (t₂ - t₁) ht_mem hdisj h3'
  constructor
  · rw [hole_image σ₂ hσ₂ t₂, Finset.mem_image]
    refine ⟨(1, 1) + (t₂ - t₁), g1, ?_⟩
    show (1, 1) + (t₂ - t₁) + t₁ = (1, 1) + t₂
    ext <;> simp <;> omega
  · rw [Finset.card_pos] at g2
    obtain ⟨τ, hτ⟩ := g2
    rw [Finset.mem_filter] at hτ
    obtain ⟨hτmem, hτeq⟩ := hτ
    refine ⟨τ, hτmem, lo (σ₁ ∪ σ₂.image (· + (t₂ - t₁))) - lo τ + t₁, ?_⟩
    calc (σ₁.image (· + t₁)) ∪ (σ₂.image (· + t₂))
        = (σ₁ ∪ σ₂.image (· + (t₂ - t₁))).image (· + t₁) := by
          rw [Finset.image_union]
          congr 1
          rw [image_add_image]
          apply Finset.image_congr
          intro y _
          rw [sub_add_cancel]
      _ = (τ.image (· + (lo (σ₁ ∪ σ₂.image (· + (t₂ - t₁))) - lo τ))).image (· + t₁) := by
          conv_lhs => rw [hτeq]
      _ = τ.image (· + ((lo (σ₁ ∪ σ₂.image (· + (t₂ - t₁))) - lo τ) + t₁)) :=
          image_add_image _ _ _

/-- The main structural fact: any hook-tiling of a rectangle refines to a
tiling by the six two-hook tiles. -/
lemma tile_decomposition {m n : ℕ} (h : Tileable (rect m n)) :
    ∃ Tiles : Finset (Finset (ℤ × ℤ)),
      (∀ T ∈ Tiles, IsTile T ∧ T.card = 12) ∧
      (∀ T₁ ∈ Tiles, ∀ T₂ ∈ Tiles, T₁ ≠ T₂ → Disjoint T₁ T₂) ∧
      rect m n = Tiles.biUnion id := by
  obtain ⟨𝒯, hh, hd, hU⟩ := h
  have hcov : ∀ x ∈ rect m n, ∃ H ∈ 𝒯, x ∈ H := by
    intro x hx
    rw [hU, Finset.mem_biUnion] at hx
    exact hx
  have huniq : ∀ H₁ ∈ 𝒯, ∀ H₂ ∈ 𝒯, ∀ x, x ∈ H₁ → x ∈ H₂ → H₁ = H₂ := by
    intro H₁ h1 H₂ h2 x hx1 hx2
    by_contra hne
    exact (Finset.disjoint_left.mp (hd H₁ h1 H₂ h2 hne)) hx1 hx2
  have hhole : ∀ H ∈ 𝒯, hole H ∈ rect m n := by
    intro H hH
    exact hole_mem_rect_of_hook (hh H hH) (by rw [hU]; exact Finset.subset_biUnion_of_mem id hH)
  set φ : Finset (ℤ × ℤ) → Finset (ℤ × ℤ) := fun H =>
    if h : ∃ H' ∈ 𝒯, hole H ∈ H' then Classical.choose h else H with hφ
  have hφ1 : ∀ H ∈ 𝒯, φ H ∈ 𝒯 := by
    intro H hH
    have hex : ∃ H' ∈ 𝒯, hole H ∈ H' := hcov (hole H) (hhole H hH)
    rw [hφ]
    simp only [hex, dite_eq_left]
    exact (Classical.choose_spec hex).1
  have hφ2 : ∀ H ∈ 𝒯, hole H ∈ φ H := by
    intro H hH
    have hex : ∃ H' ∈ 𝒯, hole H ∈ H' := hcov (hole H) (hhole H hH)
    rw [hφ]
    simp only [hex, dite_eq_left]
    exact (Classical.choose_spec hex).2
  have hφne : ∀ H ∈ 𝒯, φ H ≠ H := by
    intro H hH hne
    have h2 := hφ2 H hH
    rw [hne] at h2
    exact hole_not_mem_of_hook (hh H hH) h2
  have htile : ∀ H ∈ 𝒯, hole (φ H) ∈ H ∧ IsTile (H ∪ φ H) := by
    intro H hH
    have h1 : φ H ∈ 𝒯 := hφ1 H hH
    have hne : H ≠ φ H := (hφne H hH).symm
    apply pair_general (hh H hH) (hh (φ H) h1) (hd H hH (φ H) h1 hne) (hφ2 H hH)
    have hhm := hhole (φ H) h1
    obtain ⟨K, hK, hKm⟩ := hcov (hole (φ H)) hhm
    by_cases hKH : K = H
    · exact Or.inl (hKH ▸ hKm)
    · right
      have hKφ : K ≠ φ H := by
        intro heq
        rw [heq] at hKm
        exact hole_not_mem_of_hook (hh (φ H) h1) hKm
      refine ⟨K, hh K hK, ?_, hKm⟩
      rw [Finset.disjoint_left]
      intro x hxK hxU
      rw [Finset.mem_union] at hxU
      rcases hxU with hxU | hxU
      · exact (Finset.disjoint_left.mp (hd K hK H hH hKH)) hxK hxU
      · exact (Finset.disjoint_left.mp (hd K hK (φ H) h1 hKφ)) hxK hxU
  have hφinv : ∀ H ∈ 𝒯, φ (φ H) = H := by
    intro H hH
    have hh2 : hole (φ H) ∈ H := (htile H hH).1
    have hmem2 : φ (φ H) ∈ 𝒯 := hφ1 (φ H) (hφ1 H hH)
    have hφ2' : hole (φ H) ∈ φ (φ H) := hφ2 (φ H) (hφ1 H hH)
    exact (huniq H hH (φ (φ H)) hmem2 (hole (φ H)) hh2 hφ2').symm
  refine ⟨𝒯.image (fun H => H ∪ φ H), ?_, ?_, ?_⟩
  · intro T hT
    rw [Finset.mem_image] at hT
    obtain ⟨H, hH, rfl⟩ := hT
    refine ⟨(htile H hH).2, ?_⟩
    rw [Finset.card_union_of_disjoint (hd H hH (φ H) (hφ1 H hH) (hφne H hH).symm),
      isHook_card (hh H hH), isHook_card (hh (φ H) (hφ1 H hH))]
  · intro T₁ hT₁ T₂ hT₂ hne
    rw [Finset.mem_image] at hT₁ hT₂
    obtain ⟨H₁, hH₁, rfl⟩ := hT₁
    obtain ⟨H₂, hH₂, rfl⟩ := hT₂
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    rw [Finset.mem_union] at hx1 hx2
    rcases hx1 with hx1 | hx1 <;> rcases hx2 with hx2 | hx2
    · have e := huniq H₁ hH₁ H₂ hH₂ x hx1 hx2
      subst e
      exact hne rfl
    · have e := huniq H₁ hH₁ (φ H₂) (hφ1 H₂ hH₂) x hx1 hx2
      apply hne
      rw [e, hφinv H₂ hH₂, Finset.union_comm]
    · have e := huniq (φ H₁) (hφ1 H₁ hH₁) H₂ hH₂ x hx1 hx2
      have e2 : H₁ = φ H₂ := by rw [← hφinv H₁ hH₁, e]
      apply hne
      rw [e, e2, Finset.union_comm]
    · have e := huniq (φ H₁) (hφ1 H₁ hH₁) (φ H₂) (hφ1 H₂ hH₂) x hx1 hx2
      have e2 : H₁ = H₂ := by rw [← hφinv H₁ hH₁, ← hφinv H₂ hH₂, e]
      subst e2
      exact hne rfl
  · rw [hU]
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_image, id]
    constructor
    · rintro ⟨H, hH, hx⟩
      exact ⟨H ∪ φ H, ⟨H, hH, rfl⟩, by rw [Finset.mem_union]; exact Or.inl hx⟩
    · rintro ⟨T, ⟨H, hH, rfl⟩, hx⟩
      rw [Finset.mem_union] at hx
      rcases hx with hx | hx
      · exact ⟨H, hH, hx⟩
      · exact ⟨φ H, hφ1 H hH, hx⟩

lemma twelve_dvd_of_tileable {m n : ℕ} (h : Tileable (rect m n)) : 12 ∣ m * n := by
  obtain ⟨Tiles, hT, hd, hU⟩ := tile_decomposition h
  have hc : (rect m n).card = ∑ T ∈ Tiles, T.card := by
    rw [hU]
    exact Finset.card_biUnion hd
  rw [card_rect, Finset.sum_congr rfl (fun T hT' => (hT T hT').2),
    Finset.sum_const, nsmul_eq_mul, Nat.cast_id] at hc
  exact ⟨Tiles.card, by rw [hc]; ring⟩

lemma three_dvd_of_tileable {m n : ℕ} (h : Tileable (rect m n)) : 3 ∣ m ∨ 3 ∣ n := by
  have h3 : 3 ∣ m * n := dvd_trans (by decide : 3 ∣ 12) (twelve_dvd_of_tileable h)
  exact (Nat.Prime.dvd_mul (by decide : Nat.Prime 3)).mp h3

/-- On every tile, exactly one of the two parity counts (cells in columns
divisible by four, cells in rows divisible by four) is odd. -/
lemma tile_parities : ∀ τ ∈ tileShapes, ∀ t : ℤ × ℤ,
    ((τ.image (· + t)).filter fun c => 4 ∣ c.2).card % 2 +
    ((τ.image (· + t)).filter fun c => 4 ∣ c.1).card % 2 = 1 := by
  intro τ hτ t
  have hk2 : t.2 % 4 = 0 ∨ t.2 % 4 = 1 ∨ t.2 % 4 = 2 ∨ t.2 % 4 = 3 := by omega
  have hk1 : t.1 % 4 = 0 ∨ t.1 % 4 = 1 ∨ t.1 % 4 = 2 ∨ t.1 % 4 = 3 := by omega
  have e2 : ((τ.image (· + t)).filter fun c => 4 ∣ c.2) =
      (τ.filter fun c => 4 ∣ c.2 + t.2 % 4).image (· + t) := by
    rw [Finset.filter_image]
    congr 1
    apply Finset.filter_congr
    intro c _
    have hcr : (c + t).2 = c.2 + t.2 := rfl
    rw [hcr]
    constructor <;> intro hdiv <;> omega
  have e1 : ((τ.image (· + t)).filter fun c => 4 ∣ c.1) =
      (τ.filter fun c => 4 ∣ c.1 + t.1 % 4).image (· + t) := by
    rw [Finset.filter_image]
    congr 1
    apply Finset.filter_congr
    intro c _
    have hcr : (c + t).1 = c.1 + t.1 := rfl
    rw [hcr]
    constructor <;> intro hdiv <;> omega
  rw [e2, e1, Finset.card_image_of_injective _ (fun _ _ h => add_right_cancel h),
    Finset.card_image_of_injective _ (fun _ _ h => add_right_cancel h)]
  fin_cases hτ <;>
    rcases hk2 with hk2 | hk2 | hk2 | hk2 <;>
    rcases hk1 with hk1 | hk1 | hk1 | hk1 <;>
    rw [hk2, hk1] <;> decide

lemma rect_filter_snd_card (m n : ℕ) :
    ((rect m n).filter fun c => 4 ∣ c.2).card =
      m * ((Finset.range n).filter fun j : ℕ => 4 ∣ (j : ℤ)).card := by
  have hinj : Function.Injective (fun p : ℕ × ℕ => ((p.1 : ℤ), (p.2 : ℤ))) := by
    rintro ⟨a1, b1⟩ ⟨a2, b2⟩ h
    simp only [Prod.mk.injEq, Int.natCast_inj] at h
    exact Prod.ext h.1 h.2
  have hdec : (rect m n).filter (fun c => 4 ∣ c.2) =
      ((Finset.range m) ×ˢ ((Finset.range n).filter fun j : ℕ => 4 ∣ (j : ℤ))).image
        (fun p => ((p.1 : ℤ), (p.2 : ℤ))) := by
    ext c
    simp only [rect, Finset.mem_filter, Finset.mem_image, Finset.mem_product, Finset.mem_range]
    constructor
    · rintro ⟨⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩, hp⟩
      exact ⟨⟨a, b⟩, ⟨ha, hb, hp⟩, rfl⟩
    · rintro ⟨⟨a, b⟩, ⟨ha, hb, hp⟩, rfl⟩
      exact ⟨⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩, hp⟩
  rw [hdec, Finset.card_image_of_injective _ hinj, Finset.card_product, Finset.card_range]

lemma rect_filter_fst_card (m n : ℕ) :
    ((rect m n).filter fun c => 4 ∣ c.1).card =
      n * ((Finset.range m).filter fun j : ℕ => 4 ∣ (j : ℤ)).card := by
  have hinj : Function.Injective (fun p : ℕ × ℕ => ((p.1 : ℤ), (p.2 : ℤ))) := by
    rintro ⟨a1, b1⟩ ⟨a2, b2⟩ h
    simp only [Prod.mk.injEq, Int.natCast_inj] at h
    exact Prod.ext h.1 h.2
  have hdec : (rect m n).filter (fun c => 4 ∣ c.1) =
      (((Finset.range m).filter fun j : ℕ => 4 ∣ (j : ℤ)) ×ˢ (Finset.range n)).image
        (fun p => ((p.1 : ℤ), (p.2 : ℤ))) := by
    ext c
    simp only [rect, Finset.mem_filter, Finset.mem_image, Finset.mem_product, Finset.mem_range]
    constructor
    · rintro ⟨⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩, hp⟩
      exact ⟨⟨a, b⟩, ⟨⟨ha, hp⟩, hb⟩, rfl⟩
    · rintro ⟨⟨a, b⟩, ⟨⟨ha, hp⟩, hb⟩, rfl⟩
      exact ⟨⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩, hp⟩
  rw [hdec, Finset.card_image_of_injective _ hinj, Finset.card_product, Finset.card_range,
    mul_comm]

/-- If `4 ∣ a * b` but `4 ∤ a` and `4 ∤ b`, then `a ≡ b ≡ 2 (mod 4)`. -/
lemma mod4_eq_two_of {a b : ℕ} (h4ab : 4 ∣ a * b) (h4a : ¬ 4 ∣ a) (h4b : ¬ 4 ∣ b) :
    a % 4 = 2 ∧ b % 4 = 2 := by
  have h2ab : 2 ∣ a * b := dvd_trans (by decide : 2 ∣ 4) h4ab
  have ha : a % 2 = 0 := by
    by_contra hao
    have hao1 : a % 2 = 1 := by omega
    have h2b : 2 ∣ b := by
      rcases (Nat.Prime.dvd_mul (by decide : Nat.Prime 2)).mp h2ab with h2a | h2b
      · exact absurd h2a (by omega)
      · exact h2b
    obtain ⟨b', rfl⟩ := h2b
    have h2ab' : 2 ∣ a * b' := by
      obtain ⟨k, hk⟩ := h4ab
      have hk2 : 2 * (a * b') = 2 * (2 * k) := by
        have e : a * (2 * b') = 2 * (a * b') := by ring
        rw [e] at hk
        rw [hk]
        ring
      exact ⟨k, Nat.mul_left_cancel (by norm_num) hk2⟩
    rcases (Nat.Prime.dvd_mul (by decide : Nat.Prime 2)).mp h2ab' with h2a | h2b'
    · exact absurd h2a (by omega)
    · obtain ⟨q, hq⟩ := h2b'
      apply h4b
      rw [hq]
      exact ⟨q, by ring⟩
  have hb : b % 2 = 0 := by
    by_contra hbo
    have hbo1 : b % 2 = 1 := by omega
    have h2a : 2 ∣ a := by
      rcases (Nat.Prime.dvd_mul (by decide : Nat.Prime 2)).mp h2ab with h2a | h2b
      · exact h2a
      · exact absurd h2b (by omega)
    obtain ⟨a', rfl⟩ := h2a
    have h2ab' : 2 ∣ a' * b := by
      obtain ⟨k, hk⟩ := h4ab
      have hk2 : 2 * (a' * b) = 2 * (2 * k) := by
        have e : (2 * a') * b = 2 * (a' * b) := by ring
        rw [e] at hk
        rw [hk]
        ring
      exact ⟨k, Nat.mul_left_cancel (by norm_num) hk2⟩
    rcases (Nat.Prime.dvd_mul (by decide : Nat.Prime 2)).mp h2ab' with h2a' | h2b
    · obtain ⟨q, hq⟩ := h2a'
      apply h4a
      rw [hq]
      exact ⟨q, by ring⟩
    · exact absurd h2b (by omega)
  obtain ⟨a', rfl⟩ := Nat.dvd_of_mod_eq_zero ha
  obtain ⟨b', rfl⟩ := Nat.dvd_of_mod_eq_zero hb
  have ha' : a' % 2 = 1 := by
    by_contra hc
    have hc0 : a' % 2 = 0 := by omega
    obtain ⟨q, hq⟩ := Nat.dvd_of_mod_eq_zero hc0
    apply h4a
    rw [hq]
    exact ⟨q, by ring⟩
  have hb' : b' % 2 = 1 := by
    by_contra hc
    have hc0 : b' % 2 = 0 := by omega
    obtain ⟨q, hq⟩ := Nat.dvd_of_mod_eq_zero hc0
    apply h4b
    rw [hq]
    exact ⟨q, by ring⟩
  constructor <;> omega

/-- Necessity of the divisibility condition on `4`. -/
lemma card_biUnion' {s : Finset (Finset (ℤ × ℤ))} {t : Finset (ℤ × ℤ) → Finset (ℤ × ℤ)}
    (h : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → Disjoint (t x) (t y)) :
    (s.biUnion t).card = ∑ x ∈ s, (t x).card :=
  Finset.card_biUnion h

lemma four_dvd_of_tileable {m n : ℕ} (h : Tileable (rect m n)) : 4 ∣ m ∨ 4 ∣ n := by
  obtain ⟨Tiles, hT, hd, hU⟩ := tile_decomposition h
  by_contra hcon
  obtain ⟨h4m, h4n⟩ := not_or.mp hcon
  have h4mn : 4 ∣ m * n := dvd_trans (by decide : 4 ∣ 12) (twelve_dvd_of_tileable h)
  obtain ⟨hm4, hn4⟩ := mod4_eq_two_of h4mn h4m h4n
  -- the number of tiles is even, by the two colouring arguments
  have hmn : m * n = 12 * Tiles.card := by
    have hc : (rect m n).card = ∑ T ∈ Tiles, T.card := by
      rw [hU]
      exact Finset.card_biUnion hd
    rw [card_rect, Finset.sum_congr rfl (fun T hT' => (hT T hT').2), Finset.sum_const,
      nsmul_eq_mul, Nat.cast_id] at hc
    exact hc.trans (mul_comm _ _)
  have hpar : ∀ T ∈ Tiles, ((T.filter fun c => 4 ∣ c.2)).card % 2 +
      ((T.filter fun c => 4 ∣ c.1)).card % 2 = 1 := by
    intro T hT'
    obtain ⟨τ, hτ, t, rfl⟩ := (hT T hT').1
    exact tile_parities τ hτ t
  have hsumc : ∑ T ∈ Tiles, ((T.filter fun c => 4 ∣ c.2)).card =
      ((rect m n).filter fun c => 4 ∣ c.2).card := by
    have hdisj : ∀ T₁ ∈ Tiles, ∀ T₂ ∈ Tiles, T₁ ≠ T₂ →
        Disjoint (T₁.filter fun c => 4 ∣ c.2) (T₂.filter fun c => 4 ∣ c.2) :=
      fun T₁ h1 T₂ h2 hne =>
        (hd T₁ h1 T₂ h2 hne).mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    rw [hU, Finset.filter_biUnion]
    have hid : Tiles.biUnion (fun a => (id a).filter fun c => 4 ∣ c.2) =
        Tiles.biUnion (fun T => T.filter fun c => 4 ∣ c.2) :=
      Finset.biUnion_congr rfl fun T _ => rfl
    rw [hid]
    exact (card_biUnion' hdisj).symm
  have hsumr : ∑ T ∈ Tiles, ((T.filter fun c => 4 ∣ c.1)).card =
      ((rect m n).filter fun c => 4 ∣ c.1).card := by
    have hdisj : ∀ T₁ ∈ Tiles, ∀ T₂ ∈ Tiles, T₁ ≠ T₂ →
        Disjoint (T₁.filter fun c => 4 ∣ c.1) (T₂.filter fun c => 4 ∣ c.1) :=
      fun T₁ h1 T₂ h2 hne =>
        (hd T₁ h1 T₂ h2 hne).mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    rw [hU, Finset.filter_biUnion]
    have hid : Tiles.biUnion (fun a => (id a).filter fun c => 4 ∣ c.1) =
        Tiles.biUnion (fun T => T.filter fun c => 4 ∣ c.1) :=
      Finset.biUnion_congr rfl fun T _ => rfl
    rw [hid]
    exact (card_biUnion' hdisj).symm
  have hevencol : Even (∑ T ∈ Tiles, ((T.filter fun c => 4 ∣ c.2)).card) := by
    rw [hsumc, rect_filter_snd_card]
    obtain ⟨q, hq : m = 2 * q⟩ := show ∃ q, m = 2 * q from ⟨m / 2, by omega⟩
    exact ⟨q * ((Finset.range n).filter fun j : ℕ => 4 ∣ (j : ℤ)).card, by rw [hq]; ring⟩
  have hevenrow : Even (∑ T ∈ Tiles, ((T.filter fun c => 4 ∣ c.1)).card) := by
    rw [hsumr, rect_filter_fst_card]
    obtain ⟨q, hq : n = 2 * q⟩ := show ∃ q, n = 2 * q from ⟨n / 2, by omega⟩
    exact ⟨q * ((Finset.range m).filter fun j : ℕ => 4 ∣ (j : ℤ)).card, by rw [hq]; ring⟩
  have hcol2 : Even (∑ T ∈ Tiles, ((T.filter fun c => 4 ∣ c.2)).card % 2) := by
    have decomp : ∀ T ∈ Tiles, ((T.filter fun c => 4 ∣ c.2)).card =
        2 * (((T.filter fun c => 4 ∣ c.2)).card / 2) +
          ((T.filter fun c => 4 ∣ c.2)).card % 2 := fun T _ => by omega
    rw [Finset.sum_congr rfl decomp, Finset.sum_add_distrib, ← Finset.mul_sum] at hevencol
    obtain ⟨q, hq⟩ := hevencol
    exact ⟨q - ∑ T ∈ Tiles, ((T.filter fun c => 4 ∣ c.2)).card / 2, by omega⟩
  have hrow2 : Even (∑ T ∈ Tiles, ((T.filter fun c => 4 ∣ c.1)).card % 2) := by
    have decomp : ∀ T ∈ Tiles, ((T.filter fun c => 4 ∣ c.1)).card =
        2 * (((T.filter fun c => 4 ∣ c.1)).card / 2) +
          ((T.filter fun c => 4 ∣ c.1)).card % 2 := fun T _ => by omega
    rw [Finset.sum_congr rfl decomp, Finset.sum_add_distrib, ← Finset.mul_sum] at hevenrow
    obtain ⟨q, hq⟩ := hevenrow
    exact ⟨q - ∑ T ∈ Tiles, ((T.filter fun c => 4 ∣ c.1)).card / 2, by omega⟩
  have hcard : Even Tiles.card := by
    have hcs : Tiles.card = ∑ T ∈ Tiles, 1 := by
      rw [Finset.sum_const, nsmul_eq_mul, Nat.cast_id, mul_one]
    have decomp : ∀ T ∈ Tiles, (1 : ℕ) = ((T.filter fun c => 4 ∣ c.2)).card % 2 +
        ((T.filter fun c => 4 ∣ c.1)).card % 2 := fun T hT' => (hpar T hT').symm
    rw [hcs, Finset.sum_congr rfl decomp, Finset.sum_add_distrib]
    obtain ⟨q1, hq1⟩ := hcol2
    obtain ⟨q2, hq2⟩ := hrow2
    exact ⟨q1 + q2, by omega⟩
  -- final contradiction modulo 8
  obtain ⟨s, hs⟩ := hcard
  have em : m = 4 * (m / 4) + 2 := by omega
  have en : n = 4 * (n / 4) + 2 := by omega
  have emn : m * n = 24 * s := by rw [hmn, hs]; ring
  have key : (4 * (m / 4) + 2) * (4 * (n / 4) + 2) =
      8 * (2 * (m / 4) * (n / 4) + (m / 4) + (n / 4)) + 4 := by ring
  rw [← em, ← en, emn] at key
  omega

/-- A rectangle with a side of length at most `2` cannot be tiled (a hook
spans three consecutive rows and three consecutive columns). -/
lemma not_tileable_of_n_le_two {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hnle : n ≤ 2) :
    ¬ Tileable (rect m n) := by
  intro h
  obtain ⟨𝒯, hh, hd, hU⟩ := h
  have hne : (rect m n).Nonempty := ⟨(0, 0), by rw [mem_rect]; omega⟩
  by_cases h𝒯 : 𝒯 = ∅
  · rw [h𝒯, Finset.biUnion_empty] at hU
    rw [hU] at hne
    simp at hne
  · obtain ⟨H, hH⟩ := Finset.nonempty_of_ne_empty h𝒯
    obtain ⟨σ, hσ, t, rfl⟩ := hh H hH
    have hsub : σ.image (· + t) ⊆ rect m n := by
      rw [hU]; exact Finset.subset_biUnion_of_mem id hH
    have hcell : ∃ r : ℤ, (r, 0) ∈ σ ∧ (r, 2) ∈ σ := by
      have hrow := hook_row3 σ hσ
      obtain ⟨r, hr⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hrow)
      rw [Finset.mem_inter, Finset.mem_image, Finset.mem_image] at hr
      obtain ⟨⟨c1, hc1, e1⟩, ⟨c2, hc2, e2⟩⟩ := hr
      rw [Finset.mem_filter] at hc1 hc2
      have e1' : (r, 0) = c1 := Prod.ext e1.symm hc1.2.symm
      have e2' : (r, 2) = c2 := Prod.ext e2.symm hc2.2.symm
      exact ⟨r, by rw [e1']; exact hc1.1, by rw [e2']; exact hc2.1⟩
    obtain ⟨r, hc1, hc2⟩ := hcell
    have m1 := hsub (Finset.mem_image.mpr ⟨(r, 0), hc1, rfl⟩)
    have m2 := hsub (Finset.mem_image.mpr ⟨(r, 2), hc2, rfl⟩)
    rw [mem_rect] at m1 m2
    have e1 : ((r, 0) + t).2 = t.2 := zero_add _
    have e2 : ((r, 2) + t).2 = t.2 + 2 := add_comm _ _
    rw [e1] at m1
    rw [e2] at m2
    omega

/-- The second cell used in the corner propagation argument for the `5 × n`
case: it is the cell just next to a tile placed in the corner which cannot
be covered by any other tile. -/
def cornerCell (τ₀ : Finset (ℤ × ℤ)) : ℤ × ℤ :=
  if (3, 0) ∉ τ₀ then (3, 0) else if (4, 0) ∉ τ₀ then (4, 0)
  else if (0, 2) ∉ τ₀ then (0, 2) else (0, 1)

lemma cornerCell_not_mem : ∀ τ₀ ∈ tileShapes, (0, 0) ∈ τ₀ → cornerCell τ₀ ∉ τ₀ := by
  decide

lemma cornerCell_snd : ∀ τ₀ ∈ tileShapes, (cornerCell τ₀).2 ≤ 2 := by
  decide

lemma cornerCell_val : ∀ τ₀ ∈ tileShapes,
    cornerCell τ₀ ∈ ({(3, 0), (4, 0), (0, 2), (0, 1)} : Finset (ℤ × ℤ)) := by
  decide

/-- The corner propagation check: no tile covering `cornerCell τ₀` within
the bounds of a five-row strip is disjoint from the corner tile `τ₀`. -/
lemma corner_check :
    ∀ τ₀ ∈ tileShapes, (0, 0) ∈ τ₀ →
      ∀ τ' ∈ tileShapes, ∀ v ∈ (τ'.image fun c => cornerCell τ₀ - c),
        (∀ cell ∈ τ'.image (· + v), 0 ≤ cell.1 ∧ cell.1 < 5 ∧ 0 ≤ cell.2 ∧ cell.2 < 6) →
        ¬ Disjoint (τ'.image (· + v)) τ₀ := by
  decide +kernel

lemma tile_bounds : ∀ τ ∈ tileShapes, ∀ c ∈ τ,
    0 ≤ c.1 ∧ c.1 ≤ 3 ∧ 0 ≤ c.2 ∧ c.2 ≤ 3 := by
  decide

lemma tile_min : ∀ τ ∈ tileShapes, (∃ c ∈ τ, c.1 = 0) ∧ (∃ c ∈ τ, c.2 = 0) := by
  decide

/-- A `5 × n` rectangle cannot be tiled. -/
lemma not_tileable_5 (n : ℕ) (hn : 0 < n) : ¬ Tileable (rect 5 n) := by
  intro h
  have h12n : 12 ∣ n :=
    Nat.Coprime.dvd_of_dvd_mul_left (by decide : Nat.Coprime 12 5) (twelve_dvd_of_tileable h)
  have hn12 : 12 ≤ n := Nat.le_of_dvd hn h12n
  obtain ⟨Tiles, hT, hd, hU⟩ := tile_decomposition h
  have h00 : (0, 0) ∈ rect 5 n := by rw [mem_rect]; omega
  rw [hU, Finset.mem_biUnion] at h00
  obtain ⟨T, hT', h00T⟩ := h00
  obtain ⟨τ, hτ, t, rfl⟩ := (hT T hT').1
  have hsubT : τ.image (· + t) ⊆ rect 5 n := by
    rw [hU]; exact Finset.subset_biUnion_of_mem id hT'
  -- the corner tile is a canonical tile (its translation is zero)
  have ht0 : t = (0, 0) := by
    obtain ⟨⟨c1, hc1, e1⟩, ⟨c2, hc2, e2⟩⟩ := tile_min τ hτ
    have m1 := hsubT (Finset.mem_image.mpr ⟨c1, hc1, rfl⟩)
    have m2 := hsubT (Finset.mem_image.mpr ⟨c2, hc2, rfl⟩)
    rw [mem_rect] at m1 m2
    have hbt1 := tile_bounds τ hτ c1 hc1
    have hbt2 := tile_bounds τ hτ c2 hc2
    dsimp only [id] at h00T
    rw [Finset.mem_image] at h00T
    obtain ⟨c0, hc0, e0⟩ := h00T
    have hbt0 := tile_bounds τ hτ c0 hc0
    -- (c1 + t).1 = t.1 ≥ 0; (c0 + t) = 0 → t.1 = -c0.1 ≤ 0; similarly .2
    have g1 : (c1 + t).1 = t.1 := by simp only [Prod.fst_add, e1, zero_add]
    have g2 : (c2 + t).2 = t.2 := by simp only [Prod.snd_add, e2, zero_add]
    rw [g1] at m1
    rw [g2] at m2
    have t1 : t.1 = 0 := by
      have e0f := congrArg Prod.fst e0
      simp at e0f
      omega
    have t2 : t.2 = 0 := by
      have e0s := congrArg Prod.snd e0
      simp at e0s
      omega
    exact Prod.ext t1 t2
  rw [ht0] at h00T hsubT hT'
  have hTτ : τ.image (· + (0, 0)) = τ := by
    have e : (fun c : ℤ × ℤ => c + (0, 0)) = id := by
      funext c
      ext <;> simp
    rw [e, Finset.image_id]
  rw [hTτ] at h00T hsubT hT'
  have hxmem : cornerCell τ ∈ rect 5 n := by
    have hx4 := cornerCell_val τ hτ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx4
    rcases hx4 with h | h | h | h <;> rw [h] <;> (rw [mem_rect]; omega)
  rw [hU, Finset.mem_biUnion] at hxmem
  obtain ⟨U, hU', hxU⟩ := hxmem
  obtain ⟨τ', hτ'', v, rfl⟩ := (hT U hU').1
  dsimp only [id] at hxU
  have hne : τ'.image (· + v) ≠ τ := by
    intro heq
    rw [heq] at hxU
    exact cornerCell_not_mem τ hτ h00T hxU
  have hdisj := hd (τ'.image (· + v)) hU' τ hT' hne
  -- the bounds condition for the candidate enumeration
  have hv_mem : v ∈ τ'.image (fun c => cornerCell τ - c) := by
    rw [Finset.mem_image] at hxU
    obtain ⟨c', hc', hcv⟩ := hxU
    refine Finset.mem_image.mpr ⟨c', hc', ?_⟩
    have e1 := congrArg Prod.fst hcv
    have e2 := congrArg Prod.snd hcv
    simp only [Prod.fst_add, Prod.snd_add] at e1 e2
    ext <;> simp <;> omega
  have hbounds : ∀ cell ∈ τ'.image (· + v), 0 ≤ cell.1 ∧ cell.1 < 5 ∧ 0 ≤ cell.2 ∧ cell.2 < 6 := by
    intro cell hcell
    rw [Finset.mem_image] at hcell
    obtain ⟨c, hc, rfl⟩ := hcell
    have hsub : τ'.image (· + v) ⊆ rect 5 n := by
      rw [hU]; exact Finset.subset_biUnion_of_mem id hU'
    have hm := hsub (Finset.mem_image.mpr ⟨c, hc, rfl⟩)
    rw [mem_rect] at hm
    obtain ⟨hb1, hb2, hb3, hb4⟩ := tile_bounds τ' hτ'' c hc
    rw [Finset.mem_image] at hxU
    obtain ⟨c', hc', hcv⟩ := hxU
    obtain ⟨_, _, _, hb4'⟩ := tile_bounds τ' hτ'' c' hc'
    have hv2 : v.2 = (cornerCell τ).2 - c'.2 := by
      have hcv2 := congrArg Prod.snd hcv
      simp only [Prod.snd_add] at hcv2
      omega
    have hx2 : (cornerCell τ).2 ≤ 2 := cornerCell_snd τ hτ
    have e2 : (c + v).2 = c.2 + v.2 := rfl
    exact ⟨hm.1, hm.2.1, hm.2.2.1, by omega⟩
  exact corner_check τ hτ h00T τ' hτ'' v hv_mem hbounds hdisj

snip end

/-- The predicate characterising the rectangles that can be tiled by hooks. -/
def GoodRect (m n : ℕ) : Prop :=
  m ≠ 1 ∧ m ≠ 2 ∧ m ≠ 5 ∧ n ≠ 1 ∧ n ≠ 2 ∧ n ≠ 5 ∧ (3 ∣ m ∨ 3 ∣ n) ∧ (4 ∣ m ∨ 4 ∣ n)

/-- The answer: exactly the rectangles with `{1, 2, 5} ∩ {m, n} = ∅`,
`3 ∣ mn` (i.e. `3 ∣ m` or `3 ∣ n`) and `4 ∣ mn` (i.e. `4 ∣ m` or `4 ∣ n`). -/
determine answer : Set (ℕ × ℕ) :=
  {p | GoodRect p.1 p.2}

problem imo2004_p3 (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    Tileable (rect m n) ↔ (m, n) ∈ answer := by
  constructor
  · intro h
    have h3 := three_dvd_of_tileable h
    have h4 := four_dvd_of_tileable h
    show GoodRect m n
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, h3, h4⟩
    · intro hm1
      rw [hm1] at h
      exact not_tileable_of_n_le_two hn (by norm_num) (by norm_num) (tileable_transpose h)
    · intro hm2
      rw [hm2] at h
      exact not_tileable_of_n_le_two hn (by norm_num) (by norm_num) (tileable_transpose h)
    · intro hm5
      rw [hm5] at h
      exact not_tileable_5 n hn h
    · intro hn1
      rw [hn1] at h
      exact not_tileable_of_n_le_two hm (by norm_num) (by norm_num) h
    · intro hn2
      rw [hn2] at h
      exact not_tileable_of_n_le_two hm (by norm_num) (by norm_num) h
    · intro hn5
      rw [hn5] at h
      exact not_tileable_5 m hm (tileable_transpose h)
  · intro h
    rw [show (m, n) ∈ answer ↔ GoodRect m n from Iff.rfl] at h
    rcases h with ⟨h1, h1', h1'', h2, h2', h2'', h3, h4⟩
    exact tileable_of_conditions ⟨h1, h1', h1''⟩ ⟨h2, h2', h2''⟩ h3 h4

end Imo2004P3
