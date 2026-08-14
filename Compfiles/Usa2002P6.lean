/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Data.Nat.Cast.Order.Field
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics] }

/-!
# USA Mathematical Olympiad 2002, Problem 6

I have an n×n sheet of stamps, from which I've been asked to tear out blocks
of three adjacent stamps in a single row or column. (I can only tear along the
perforations separating adjacent stamps, and each block must come out of the
sheet in one piece.) Let b(n) be the smallest number of blocks I can tear out
and make it impossible to tear out any more blocks. Prove that there are real
constants c and d such that

    (1/7)n² - cn ≤ b(n) ≤ (1/5)n² - dn

for all n > 0.
-/

namespace Usa2002P6

/-- A horizontal block: three adjacent stamps in a single row. -/
def hblock (i j : ℕ) : Finset (ℕ × ℕ) := {(i, j), (i, j + 1), (i, j + 2)}

/-- A vertical block: three adjacent stamps in a single column. -/
def vblock (i j : ℕ) : Finset (ℕ × ℕ) := {(i, j), (i + 1, j), (i + 2, j)}

/-- A block that can be torn out of the n×n sheet. -/
def IsBlock (n : ℕ) (s : Finset (ℕ × ℕ)) : Prop :=
  (∃ i j, i < n ∧ j + 2 < n ∧ s = hblock i j) ∨
    (∃ i j, i + 2 < n ∧ j < n ∧ s = vblock i j)

/-- A tearing-out of pairwise disjoint blocks from the n×n sheet which makes it
impossible to tear out any more blocks. -/
def IsMaximalTearing (n : ℕ) (T : Finset (Finset (ℕ × ℕ))) : Prop :=
  (∀ s ∈ T, IsBlock n s) ∧
    (∀ s ∈ T, ∀ t ∈ T, s ≠ t → Disjoint s t) ∧
      (∀ s, IsBlock n s → ∃ t ∈ T, ¬ Disjoint s t)

/-- A wasteful maximal tearing: fill the sheet with vertical blocks, column by
column, and fill the leftover bottom rows with horizontal blocks. Used to show
that a maximal tearing always exists (and for the upper bound at small `n`). -/
def trivialTearing (n : ℕ) : Finset (Finset (ℕ × ℕ)) :=
  (Finset.range (n / 3) ×ˢ Finset.range n).image (fun p => vblock (3 * p.1) p.2) ∪
    (Finset.range (n % 3) ×ˢ Finset.range (n / 3)).image
      (fun p => hblock (3 * (n / 3) + p.1) (3 * p.2))

/-- The phase of row `i` in the efficient tearing pattern: in row `i`, the torn
blocks start at columns congruent to `phase i` modulo 5. -/
def phase (i : ℕ) : ℕ := i % 5

/-- The blocks torn out of row `i` in the efficient tearing pattern. -/
def patRowTearing (n i : ℕ) : Finset (Finset (ℕ × ℕ)) :=
  ((Finset.range (n / 5 + 1)).filter fun k => phase i + 5 * k + 2 < n).image
      (fun k => hblock i (phase i + 5 * k)) ∪
    (if 3 ≤ phase i then {hblock i 0} else ∅) ∪
    (if 3 ≤ (n + 2 - phase i) % 5 then {hblock i (n - 3)} else ∅)

/-- The efficient maximal tearing, with asymptotic density n²/5. -/
def patTearing (n : ℕ) : Finset (Finset (ℕ × ℕ)) :=
  (Finset.range n).biUnion fun i => patRowTearing n i

/-- `cov n i j` means that cell `(i, j)` is torn out by the efficient pattern. -/
def cov (n i j : ℕ) : Prop :=
  (3 ≤ phase i ∧ j ≤ 2) ∨
    (phase i ≤ j ∧ (j - phase i) % 5 ≤ 2 ∧ j - (j - phase i) % 5 + 2 < n) ∨
      (3 ≤ (n + 2 - phase i) % 5 ∧ n - 3 ≤ j)

snip begin

theorem mem_hblock {i j a b : ℕ} :
    (a, b) ∈ hblock i j ↔ a = i ∧ j ≤ b ∧ b ≤ j + 2 := by
  simp [hblock]; omega

theorem mem_vblock {i j a b : ℕ} :
    (a, b) ∈ vblock i j ↔ i ≤ a ∧ a ≤ i + 2 ∧ b = j := by
  simp [vblock]; omega

theorem trivialTearing_isMaximalTearing (n : ℕ) :
    IsMaximalTearing n (trivialTearing n) := by
  refine ⟨?_, ?_, ?_⟩
  · -- every member is a block
    intro s hs
    simp only [trivialTearing, Finset.mem_union, Finset.mem_image,
      Finset.mem_product, Finset.mem_range] at hs
    rcases hs with (⟨p, ⟨hk, hj⟩, rfl⟩ | ⟨p, ⟨hr, hk⟩, rfl⟩)
    · exact Or.inr ⟨3 * p.1, p.2, by omega, hj, rfl⟩
    · exact Or.inl ⟨3 * (n / 3) + p.1, 3 * p.2, by omega, by omega, rfl⟩
  · -- the blocks are pairwise disjoint
    intro s hs t ht hst
    simp only [trivialTearing, Finset.mem_union, Finset.mem_image,
      Finset.mem_product, Finset.mem_range] at hs ht
    rw [Finset.disjoint_left]
    intro x hxs hxt
    rcases hs with (⟨p, ⟨hk, hj⟩, rfl⟩ | ⟨p, ⟨hr, hk⟩, rfl⟩) <;>
      rcases ht with (⟨q, ⟨hk', hj'⟩, rfl⟩ | ⟨q, ⟨hr', hk'⟩, rfl⟩)
    · -- two vertical blocks
      rw [mem_vblock] at hxs hxt
      have hp2 : p.2 = q.2 := by omega
      have hp1 : p.1 ≠ q.1 := fun h => hst (by rw [h, hp2])
      omega
    · -- vertical block meets horizontal block: impossible, the rows differ
      rw [mem_vblock] at hxs
      rw [mem_hblock] at hxt
      omega
    · -- horizontal block meets vertical block: impossible, the rows differ
      rw [mem_hblock] at hxs
      rw [mem_vblock] at hxt
      omega
    · -- two horizontal blocks
      rw [mem_hblock] at hxs hxt
      have hp1 : p.1 = q.1 := by omega
      have hp2 : p.2 ≠ q.2 := fun h => hst (by rw [hp1, h])
      omega
  · -- no further block can be torn out
    intro s hs
    rcases hs with ⟨i, j, hi, hj, rfl⟩ | ⟨i, j, hi, hj, rfl⟩
    · -- a horizontal block at row `i`, columns `j .. j+2`
      by_cases hi' : i < 3 * (n / 3)
      · -- cell (i, j) belongs to a torn-out vertical block
        refine ⟨vblock (3 * (i / 3)) j, ?_, ?_⟩
        · refine Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr
            ⟨(i / 3, j), ?_, rfl⟩))
          rw [Finset.mem_product]
          exact ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩
        · exact Finset.not_disjoint_iff.mpr
            ⟨(i, j), by simp [hblock], by rw [mem_vblock]; omega⟩
      · -- cell (i, j) belongs to a torn-out horizontal block
        refine ⟨hblock (3 * (n / 3) + (i - 3 * (n / 3))) (3 * (j / 3)), ?_, ?_⟩
        · refine Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr
            ⟨(i - 3 * (n / 3), j / 3), ?_, rfl⟩))
          rw [Finset.mem_product]
          exact ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩
        · exact Finset.not_disjoint_iff.mpr
            ⟨(i, j), by simp [hblock], by rw [mem_hblock]; omega⟩
    · -- a vertical block at column `j`, rows `i .. i+2`
      have hi' : i < 3 * (n / 3) := by omega
      refine ⟨vblock (3 * (i / 3)) j, ?_, ?_⟩
      · refine Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr
          ⟨(i / 3, j), ?_, rfl⟩))
        rw [Finset.mem_product]
        exact ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr hj⟩
      · exact Finset.not_disjoint_iff.mpr
          ⟨(i, j), by simp [vblock], by rw [mem_vblock]; omega⟩

theorem trivialTearing_card_le (n : ℕ) :
    (trivialTearing n).card ≤ (n / 3) * n + (n % 3) * (n / 3) := by
  refine (Finset.card_union_le _ _).trans ?_
  gcongr <;> exact Finset.card_image_le.trans (by simp)

theorem exists_maximalTearing (n : ℕ) :
    ∃ k, ∃ T, IsMaximalTearing n T ∧ T.card = k :=
  ⟨(trivialTearing n).card, trivialTearing n, trivialTearing_isMaximalTearing n, rfl⟩

snip end

/-- `b n`: the smallest number of blocks one can tear out of an n×n sheet of
stamps (tearing out whole blocks of three adjacent stamps in a single row or
column) making it impossible to tear out any more blocks. -/
noncomputable def b (n : ℕ) : ℕ :=
  open Classical in Nat.find (exists_maximalTearing n)

snip begin

theorem b_le {n : ℕ} {T : Finset (Finset (ℕ × ℕ))} (h : IsMaximalTearing n T) :
    b n ≤ T.card := by
  classical
  exact Nat.find_le ⟨T, h, rfl⟩

theorem b_spec (n : ℕ) : ∃ T, IsMaximalTearing n T ∧ T.card = b n := by
  classical
  exact Nat.find_spec (exists_maximalTearing n)

/-- The set of all horizontal `1 × 3` block positions on the `n × n` sheet. -/
def segsH (n : ℕ) : Finset (Finset (ℕ × ℕ)) :=
  (Finset.range n ×ˢ Finset.range (n - 2)).image fun p => hblock p.1 p.2

/-- The set of all vertical `3 × 1` block positions on the `n × n` sheet. -/
def segsV (n : ℕ) : Finset (Finset (ℕ × ℕ)) :=
  (Finset.range (n - 2) ×ˢ Finset.range n).image fun p => vblock p.1 p.2

theorem lower_hblock_inj {i j i' j' : ℕ} (h : hblock i j = hblock i' j') :
    i = i' ∧ j = j' := by
  have key1 : (i, j) ∈ hblock i j := mem_hblock.mpr ⟨rfl, le_rfl, by omega⟩
  have key2 : (i', j') ∈ hblock i' j' := mem_hblock.mpr ⟨rfl, le_rfl, by omega⟩
  rw [h] at key1
  rw [← h] at key2
  rw [mem_hblock] at key1 key2
  omega

theorem lower_vblock_inj {i j i' j' : ℕ} (h : vblock i j = vblock i' j') :
    i = i' ∧ j = j' := by
  have key1 : (i, j) ∈ vblock i j := mem_vblock.mpr ⟨le_rfl, by omega, rfl⟩
  have key2 : (i', j') ∈ vblock i' j' := mem_vblock.mpr ⟨le_rfl, by omega, rfl⟩
  rw [h] at key1
  rw [← h] at key2
  rw [mem_vblock] at key1 key2
  omega

theorem lower_hblock_ne_vblock {i j i' j' : ℕ} : hblock i j ≠ vblock i' j' := by
  intro h
  have key1 : (i', j') ∈ vblock i' j' := mem_vblock.mpr ⟨le_rfl, by omega, rfl⟩
  have key2 : (i' + 1, j') ∈ vblock i' j' := mem_vblock.mpr ⟨by omega, by omega, rfl⟩
  rw [← h] at key1 key2
  rw [mem_hblock] at key1 key2
  omega

theorem lower_card_segsH (n : ℕ) : (segsH n).card = n * (n - 2) := by
  rw [segsH, Finset.card_image_of_injOn, Finset.card_product, Finset.card_range,
    Finset.card_range]
  intro p _ q _ h
  obtain ⟨h1, h2⟩ := lower_hblock_inj h
  exact Prod.ext_iff.mpr ⟨h1, h2⟩

theorem lower_card_segsV (n : ℕ) : (segsV n).card = n * (n - 2) := by
  rw [segsV, Finset.card_image_of_injOn, Finset.card_product, Finset.card_range,
    Finset.card_range, Nat.mul_comm]
  intro p _ q _ h
  obtain ⟨h1, h2⟩ := lower_vblock_inj h
  exact Prod.ext_iff.mpr ⟨h1, h2⟩

theorem lower_disjoint_segs (n : ℕ) : Disjoint (segsH n) (segsV n) := by
  rw [Finset.disjoint_left]
  intro s hs hv
  rw [segsH, Finset.mem_image] at hs
  obtain ⟨p, -, rfl⟩ := hs
  rw [segsV, Finset.mem_image] at hv
  obtain ⟨q, -, h⟩ := hv
  exact lower_hblock_ne_vblock h.symm

theorem lower_card_segs (n : ℕ) : (segsH n ∪ segsV n).card = 2 * (n * (n - 2)) := by
  rw [Finset.card_union_of_disjoint (lower_disjoint_segs n), lower_card_segsH,
    lower_card_segsV, two_mul]

theorem lower_isBlock_of_mem_segs {n : ℕ} {s : Finset (ℕ × ℕ)}
    (h : s ∈ segsH n ∪ segsV n) : IsBlock n s := by
  rw [Finset.mem_union] at h
  obtain (hs | hs) := h
  · rw [segsH, Finset.mem_image] at hs
    obtain ⟨p, hp, rfl⟩ := hs
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp
    exact Or.inl ⟨p.1, p.2, hp.1, by omega, rfl⟩
  · rw [segsV, Finset.mem_image] at hs
    obtain ⟨p, hp, rfl⟩ := hs
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp
    exact Or.inr ⟨p.1, p.2, by omega, hp.2, rfl⟩

/-- Every block meets at most `14` of the possible block positions. -/
theorem lower_card_filter_le_fourteen {n : ℕ} {s : Finset (ℕ × ℕ)} (hs : IsBlock n s) :
    ((segsH n ∪ segsV n).filter fun u => ¬ Disjoint u s).card ≤ 14 := by
  obtain (⟨i, j, -, -, rfl⟩ | ⟨i, j, -, -, rfl⟩) := hs
  · -- `s` is the horizontal block `hblock i j`.
    rw [Finset.filter_union]
    have hsub1 : ((segsH n).filter fun u => ¬ Disjoint u (hblock i j)) ⊆
        (Finset.Icc (j - 2) (j + 2)).image fun j' => hblock i j' := by
      intro u hu
      rw [Finset.mem_filter] at hu
      obtain ⟨hu, hmeet⟩ := hu
      rw [segsH, Finset.mem_image] at hu
      obtain ⟨p, -, rfl⟩ := hu
      rw [Finset.not_disjoint_iff] at hmeet
      obtain ⟨⟨a, b⟩, hab1, hab2⟩ := hmeet
      rw [mem_hblock] at hab1 hab2
      rw [Finset.mem_image]
      refine ⟨p.2, ?_, ?_⟩
      · rw [Finset.mem_Icc]
        omega
      · have hpi : p.1 = i := by omega
        show hblock i p.2 = hblock p.1 p.2
        rw [← hpi]
    have hcard1 :
        ((Finset.Icc (j - 2) (j + 2)).image fun j' => hblock i j').card ≤ 5 := by
      refine Finset.card_image_le.trans ?_
      rw [Nat.card_Icc]
      omega
    have hsub2 : ((segsV n).filter fun u => ¬ Disjoint u (hblock i j)) ⊆
        ((Finset.Icc (i - 2) i ×ˢ {j, j + 1, j + 2}) : Finset (ℕ × ℕ)).image
          fun p => vblock p.1 p.2 := by
      intro u hu
      rw [Finset.mem_filter] at hu
      obtain ⟨hu, hmeet⟩ := hu
      rw [segsV, Finset.mem_image] at hu
      obtain ⟨p, -, rfl⟩ := hu
      rw [Finset.not_disjoint_iff] at hmeet
      obtain ⟨⟨a, b⟩, hab1, hab2⟩ := hmeet
      rw [mem_vblock] at hab1
      rw [mem_hblock] at hab2
      rw [Finset.mem_image]
      refine ⟨p, ?_, rfl⟩
      rw [Finset.mem_product, Finset.mem_Icc]
      refine ⟨by omega, ?_⟩
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    have hcard2 : (((Finset.Icc (i - 2) i ×ˢ {j, j + 1, j + 2}) : Finset (ℕ × ℕ)).image
          fun p => vblock p.1 p.2).card ≤ 9 := by
      refine Finset.card_image_le.trans ?_
      rw [Finset.card_product, Nat.card_Icc]
      have hIcc : i + 1 - (i - 2) ≤ 3 := by omega
      have h3 : ({j, j + 1, j + 2} : Finset ℕ).card ≤ 3 := by
        exact Finset.card_le_three
      exact (Nat.mul_le_mul hIcc h3).trans (by norm_num)
    exact (Finset.card_union_le _ _).trans
      ((add_le_add ((Finset.card_le_card hsub1).trans hcard1)
        ((Finset.card_le_card hsub2).trans hcard2)).trans (by norm_num))
  · -- `s` is the vertical block `vblock i j`.
    rw [Finset.filter_union]
    have hsub1 : ((segsH n).filter fun u => ¬ Disjoint u (vblock i j)) ⊆
        ((Finset.Icc i (i + 2) ×ˢ Finset.Icc (j - 2) j) : Finset (ℕ × ℕ)).image
          fun p => hblock p.1 p.2 := by
      intro u hu
      rw [Finset.mem_filter] at hu
      obtain ⟨hu, hmeet⟩ := hu
      rw [segsH, Finset.mem_image] at hu
      obtain ⟨p, -, rfl⟩ := hu
      rw [Finset.not_disjoint_iff] at hmeet
      obtain ⟨⟨a, b⟩, hab1, hab2⟩ := hmeet
      rw [mem_hblock] at hab1
      rw [mem_vblock] at hab2
      rw [Finset.mem_image]
      refine ⟨p, ?_, rfl⟩
      rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
      omega
    have hcard1 : (((Finset.Icc i (i + 2) ×ˢ Finset.Icc (j - 2) j) : Finset (ℕ × ℕ)).image
          fun p => hblock p.1 p.2).card ≤ 9 := by
      refine Finset.card_image_le.trans ?_
      rw [Finset.card_product, Nat.card_Icc, Nat.card_Icc]
      have hIcc1 : i + 2 + 1 - i ≤ 3 := by omega
      have hIcc2 : j + 1 - (j - 2) ≤ 3 := by omega
      exact (Nat.mul_le_mul hIcc1 hIcc2).trans (by norm_num)
    have hsub2 : ((segsV n).filter fun u => ¬ Disjoint u (vblock i j)) ⊆
        (Finset.Icc (i - 2) (i + 2)).image fun i' => vblock i' j := by
      intro u hu
      rw [Finset.mem_filter] at hu
      obtain ⟨hu, hmeet⟩ := hu
      rw [segsV, Finset.mem_image] at hu
      obtain ⟨p, -, rfl⟩ := hu
      rw [Finset.not_disjoint_iff] at hmeet
      obtain ⟨⟨a, b⟩, hab1, hab2⟩ := hmeet
      rw [mem_vblock] at hab1 hab2
      rw [Finset.mem_image]
      refine ⟨p.1, ?_, ?_⟩
      · rw [Finset.mem_Icc]
        omega
      · have hpj : p.2 = j := by omega
        show vblock p.1 j = vblock p.1 p.2
        rw [← hpj]
    have hcard2 :
        ((Finset.Icc (i - 2) (i + 2)).image fun i' => vblock i' j).card ≤ 5 := by
      refine Finset.card_image_le.trans ?_
      rw [Nat.card_Icc]
      omega
    exact (Finset.card_union_le _ _).trans
      ((add_le_add ((Finset.card_le_card hsub1).trans hcard1)
        ((Finset.card_le_card hsub2).trans hcard2)).trans (by norm_num))

/-- The lower bound `b(n) ≥ n(n - 2)/7`: double-counting pairs of a possible
block position and a torn-out block meeting it. Every one of the `2n(n - 2)`
positions must be met by the tearing, and every torn-out block meets at most
`14` positions. -/
theorem counting_lower_bound {n : ℕ} {T : Finset (Finset (ℕ × ℕ))}
    (hT : IsMaximalTearing n T) : 2 * (n * (n - 2)) ≤ 14 * T.card := by
  obtain ⟨hT1, -, hT3⟩ := hT
  -- Every position meets some block of `T`, so the positions inject into the pairs.
  have h1 : (segsH n ∪ segsV n).card ≤
      (((segsH n ∪ segsV n) ×ˢ T).filter fun p => ¬ Disjoint p.1 p.2).card := by
    have hsub : segsH n ∪ segsV n ⊆
        (((segsH n ∪ segsV n) ×ˢ T).filter fun p => ¬ Disjoint p.1 p.2).image
          Prod.fst := by
      intro s hs
      have hB := lower_isBlock_of_mem_segs hs
      obtain ⟨t, htT, hmeet⟩ := hT3 s hB
      rw [Finset.mem_image]
      exact ⟨(s, t), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hs, htT⟩, hmeet⟩,
        rfl⟩
    exact (Finset.card_le_card hsub).trans Finset.card_image_le
  -- Each block of `T` meets at most `14` positions, bounding the number of pairs.
  have h2 : (((segsH n ∪ segsV n) ×ˢ T).filter fun p => ¬ Disjoint p.1 p.2).card ≤
      T.card * 14 := by
    have hsub : (((segsH n ∪ segsV n) ×ˢ T).filter fun p => ¬ Disjoint p.1 p.2) ⊆
        T.biUnion fun t => (((segsH n ∪ segsV n).filter fun u => ¬ Disjoint u t).image
          fun u => (u, t)) := by
      intro p hp
      rw [Finset.mem_filter] at hp
      obtain ⟨hp_mem, hp_meet⟩ := hp
      rw [Finset.mem_product] at hp_mem
      rw [Finset.mem_biUnion]
      refine ⟨p.2, hp_mem.2, ?_⟩
      show p ∈ ((segsH n ∪ segsV n).filter fun u => ¬ Disjoint u p.2).image
        fun u => (u, p.2)
      rw [Finset.mem_image]
      exact ⟨p.1, Finset.mem_filter.mpr ⟨hp_mem.1, hp_meet⟩, rfl⟩
    calc (((segsH n ∪ segsV n) ×ˢ T).filter fun p => ¬ Disjoint p.1 p.2).card
        ≤ (T.biUnion fun t => (((segsH n ∪ segsV n).filter fun u => ¬ Disjoint u t).image
            fun u => (u, t))).card := Finset.card_le_card hsub
      _ ≤ ∑ t ∈ T, (((segsH n ∪ segsV n).filter fun u => ¬ Disjoint u t).image
            fun u => (u, t)).card := Finset.card_biUnion_le
      _ ≤ ∑ t ∈ T, ((segsH n ∪ segsV n).filter fun u => ¬ Disjoint u t).card :=
          Finset.sum_le_sum fun t _ => Finset.card_image_le
      _ ≤ ∑ t ∈ T, 14 := Finset.sum_le_sum fun t ht =>
          lower_card_filter_le_fourteen (hT1 t ht)
      _ = T.card * 14 := by simp [Finset.sum_const]
  calc 2 * (n * (n - 2)) = (segsH n ∪ segsV n).card := (lower_card_segs n).symm
    _ ≤ (((segsH n ∪ segsV n) ×ˢ T).filter fun p => ¬ Disjoint p.1 p.2).card := h1
    _ ≤ T.card * 14 := h2
    _ = 14 * T.card := mul_comm _ _

/-- Membership in a row of the efficient tearing pattern, in a usable form. -/
theorem mem_patRowTearing {n i : ℕ} {s : Finset (ℕ × ℕ)} (hs : s ∈ patRowTearing n i) :
    (∃ k, k < n / 5 + 1 ∧ phase i + 5 * k + 2 < n ∧ s = hblock i (phase i + 5 * k)) ∨
      (3 ≤ phase i ∧ s = hblock i 0) ∨
        (3 ≤ (n + 2 - phase i) % 5 ∧ s = hblock i (n - 3)) := by
  simp only [patRowTearing, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
    Finset.mem_range] at hs
  rcases hs with (⟨k, ⟨hk1, hk2⟩, rfl⟩ | hs) | hs
  · exact Or.inl ⟨k, hk1, hk2, rfl⟩
  · by_cases h3 : 3 ≤ phase i
    · rw [ite_eq_left h3] at hs
      exact Or.inr (Or.inl ⟨h3, Finset.mem_singleton.mp hs⟩)
    · rw [ite_eq_right h3] at hs
      exact absurd hs (Finset.notMem_empty _)
  · by_cases h3 : 3 ≤ (n + 2 - phase i) % 5
    · rw [ite_eq_left h3] at hs
      exact Or.inr (Or.inr ⟨h3, Finset.mem_singleton.mp hs⟩)
    · rw [ite_eq_right h3] at hs
      exact absurd hs (Finset.notMem_empty _)

/-- Every block of row `i` of the pattern lies entirely within row `i`. -/
theorem fst_eq_of_mem_patRowTearing {n i a b : ℕ} {s : Finset (ℕ × ℕ)}
    (hs : s ∈ patRowTearing n i) (hx : (a, b) ∈ s) : a = i := by
  rcases mem_patRowTearing hs with ⟨k, _, _, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
    rw [mem_hblock] at hx <;> omega

theorem patTearing_isBlock {n : ℕ} (hn : 6 ≤ n) {s : Finset (ℕ × ℕ)}
    (hs : s ∈ patTearing n) : IsBlock n s := by
  rw [patTearing, Finset.mem_biUnion] at hs
  obtain ⟨i, hi, hs⟩ := hs
  rw [Finset.mem_range] at hi
  rcases mem_patRowTearing hs with ⟨k, _, hk2, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
  · exact Or.inl ⟨i, phase i + 5 * k, hi, hk2, rfl⟩
  · exact Or.inl ⟨i, 0, hi, by omega, rfl⟩
  · exact Or.inl ⟨i, n - 3, hi, by omega, rfl⟩

theorem patTearing_disjoint {n : ℕ} (hn : 6 ≤ n) {s t : Finset (ℕ × ℕ)}
    (hs : s ∈ patTearing n) (ht : t ∈ patTearing n) (hst : s ≠ t) : Disjoint s t := by
  rw [patTearing, Finset.mem_biUnion] at hs ht
  obtain ⟨i, hi, hs⟩ := hs
  obtain ⟨i', hi', ht⟩ := ht
  rw [Finset.disjoint_left]
  intro x hxs hxt
  obtain ⟨a, b⟩ := x
  have ha : a = i := fst_eq_of_mem_patRowTearing hs hxs
  have hb : a = i' := fst_eq_of_mem_patRowTearing ht hxt
  subst ha
  subst hb
  rcases mem_patRowTearing hs with ⟨k, hk1, hk2, hs_eq⟩ | ⟨hs3, hs_eq⟩ | ⟨hs3, hs_eq⟩ <;>
    rcases mem_patRowTearing ht with ⟨l, hl1, hl2, ht_eq⟩ | ⟨ht3, ht_eq⟩ | ⟨ht3, ht_eq⟩ <;>
    subst hs_eq <;> subst ht_eq <;> rw [mem_hblock] at hxs hxt
  · -- two pattern blocks of the same row: the column ranges are 5 apart
    have hkl : k ≠ l := fun h => hst (by rw [h])
    omega
  · -- pattern block vs. extra left block
    omega
  · -- pattern block vs. extra right block
    omega
  · -- extra left block vs. pattern block
    omega
  · -- same block
    exact hst rfl
  · -- extra left block vs. extra right block: n ≥ 6
    omega
  · -- extra right block vs. pattern block
    omega
  · -- extra right block vs. extra left block: n ≥ 6
    omega
  · -- same block
    exact hst rfl

/-- Every cell satisfying `cov` is torn out by the pattern. -/
theorem cov_covered {n i j : ℕ} (hn : 6 ≤ n) (hi : i < n) (hj : j < n) (h : cov n i j) :
    ∃ s ∈ patRowTearing n i, (i, j) ∈ s := by
  rcases h with ⟨h3, hj2⟩ | ⟨h1, h2, h3⟩ | ⟨h3, hj3⟩
  · -- the extra left block covers the cell
    refine ⟨hblock i 0, ?_, by rw [mem_hblock]; omega⟩
    refine Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr ?_)))
    rw [ite_eq_left h3]
    exact Finset.mem_singleton_self _
  · -- a pattern block covers the cell
    refine ⟨hblock i (phase i + 5 * ((j - phase i) / 5)), ?_, by rw [mem_hblock]; omega⟩
    refine Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl ?_)))
    refine Finset.mem_image.mpr ⟨(j - phase i) / 5, ?_, rfl⟩
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, by omega⟩
  · -- the extra right block covers the cell
    refine ⟨hblock i (n - 3), ?_, by rw [mem_hblock]; omega⟩
    refine Finset.mem_union.mpr (Or.inr ?_)
    rw [ite_eq_left h3]
    exact Finset.mem_singleton_self _

/-- Every three consecutive cells of a row of the sheet contain a torn-out cell. -/
theorem row_cov {n i j : ℕ} (hn : 6 ≤ n) (hi : i < n) (hj : j + 2 < n) :
    cov n i j ∨ cov n i (j + 1) ∨ cov n i (j + 2) := by
  simp only [cov, phase]
  omega

/-- Every three consecutive cells of a column of the sheet contain a torn-out
cell. -/
theorem col_cov {n i j : ℕ} (hn : 6 ≤ n) (hi : i + 2 < n) (hj : j < n) :
    cov n i j ∨ cov n (i + 1) j ∨ cov n (i + 2) j := by
  simp only [cov, phase]
  omega

theorem patTearing_maximal {n : ℕ} (hn : 6 ≤ n) {s : Finset (ℕ × ℕ)} (hs : IsBlock n s) :
    ∃ t ∈ patTearing n, ¬ Disjoint s t := by
  rcases hs with ⟨i, j, hi, hj, rfl⟩ | ⟨i, j, hi, hj, rfl⟩
  · -- a horizontal block at row `i`, columns `j .. j+2`
    rcases row_cov hn hi hj with h | h | h
    · obtain ⟨t, ht, hcell⟩ := cov_covered hn hi (by omega) h
      exact ⟨t, Finset.mem_biUnion.mpr ⟨i, Finset.mem_range.mpr hi, ht⟩,
        Finset.not_disjoint_iff.mpr ⟨(i, j), by simp [hblock], hcell⟩⟩
    · obtain ⟨t, ht, hcell⟩ := cov_covered hn hi (by omega) h
      exact ⟨t, Finset.mem_biUnion.mpr ⟨i, Finset.mem_range.mpr hi, ht⟩,
        Finset.not_disjoint_iff.mpr ⟨(i, j + 1), by simp [hblock], hcell⟩⟩
    · obtain ⟨t, ht, hcell⟩ := cov_covered hn hi (by omega) h
      exact ⟨t, Finset.mem_biUnion.mpr ⟨i, Finset.mem_range.mpr hi, ht⟩,
        Finset.not_disjoint_iff.mpr ⟨(i, j + 2), by simp [hblock], hcell⟩⟩
  · -- a vertical block at column `j`, rows `i .. i+2`
    rcases col_cov hn hi hj with h | h | h
    · obtain ⟨t, ht, hcell⟩ := cov_covered hn (by omega) hj h
      exact ⟨t, Finset.mem_biUnion.mpr ⟨i, Finset.mem_range.mpr (by omega), ht⟩,
        Finset.not_disjoint_iff.mpr ⟨(i, j), by simp [vblock], hcell⟩⟩
    · obtain ⟨t, ht, hcell⟩ := cov_covered hn (by omega) hj h
      exact ⟨t, Finset.mem_biUnion.mpr ⟨i + 1, Finset.mem_range.mpr (by omega), ht⟩,
        Finset.not_disjoint_iff.mpr ⟨(i + 1, j), by simp [vblock], hcell⟩⟩
    · obtain ⟨t, ht, hcell⟩ := cov_covered hn (by omega) hj h
      exact ⟨t, Finset.mem_biUnion.mpr ⟨i + 2, Finset.mem_range.mpr (by omega), ht⟩,
        Finset.not_disjoint_iff.mpr ⟨(i + 2, j), by simp [vblock], hcell⟩⟩

theorem patRowTearing_card_le (n i : ℕ) : (patRowTearing n i).card ≤ n / 5 + 3 := by
  have h1 : (((Finset.range (n / 5 + 1)).filter fun k => phase i + 5 * k + 2 < n).image
      fun k => hblock i (phase i + 5 * k)).card ≤ n / 5 + 1 :=
    Finset.card_image_le.trans
      ((Finset.card_filter_le _ _).trans (by rw [Finset.card_range]))
  have h2 : ((if 3 ≤ phase i then {hblock i 0} else ∅) : Finset (Finset (ℕ × ℕ))).card ≤ 1 := by
    split <;> simp
  have h3 : ((if 3 ≤ (n + 2 - phase i) % 5 then {hblock i (n - 3)} else ∅) :
      Finset (Finset (ℕ × ℕ))).card ≤ 1 := by
    split <;> simp
  calc (patRowTearing n i).card
      ≤ _ + _ + _ :=
        (Finset.card_union_le _ _).trans
          (add_le_add (Finset.card_union_le _ _) le_rfl)
    _ ≤ (n / 5 + 1) + 1 + 1 := by gcongr
    _ = n / 5 + 3 := rfl

theorem patTearing_card_le (n : ℕ) : (patTearing n).card ≤ n * (n / 5 + 3) := by
  refine Finset.card_biUnion_le.trans ?_
  calc (∑ i ∈ Finset.range n, (patRowTearing n i).card)
      ≤ ∑ _i ∈ Finset.range n, (n / 5 + 3) :=
        Finset.sum_le_sum fun i _ => patRowTearing_card_le n i
    _ = n * (n / 5 + 3) := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

theorem patTearing_isMaximalTearing {n : ℕ} (hn : 6 ≤ n) :
    IsMaximalTearing n (patTearing n) :=
  ⟨fun _s hs => patTearing_isBlock hn hs,
   fun _s hs _t ht hst => patTearing_disjoint hn hs ht hst,
   fun _s hs => patTearing_maximal hn hs⟩

snip end

/-- **USAMO 2002, Problem 6.** There are real constants `c` and `d` such that
`(1/7)n² - cn ≤ b(n) ≤ (1/5)n² - dn` for all `n > 0`. Here we take `c = 2/7`
and `d = -3`. -/
problem usa2002_p6 :
    ∃ c d : ℝ, ∀ n : ℕ, 0 < n →
      (n : ℝ) ^ 2 / 7 - c * n ≤ (b n : ℝ) ∧ (b n : ℝ) ≤ (n : ℝ) ^ 2 / 5 - d * n := by
  refine ⟨2 / 7, -3, fun n hn => ⟨?_, ?_⟩⟩
  · -- the lower bound: every maximal tearing has at least `n(n - 2)/7` blocks
    obtain ⟨T, hT, hcard⟩ := b_spec n
    rcases le_or_gt n 2 with hn2 | hn2
    · -- for `n ≤ 2` the left-hand side is at most 0
      have hbn : (0 : ℝ) ≤ (b n : ℝ) := Nat.cast_nonneg _
      have hn' : (n : ℝ) ≤ 2 := by exact_mod_cast hn2
      nlinarith [hbn, hn',
        mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) (by linarith : (0 : ℝ) ≤ 2 - n)]
    · have h2 : 2 * (n * (n - 2)) ≤ 14 * T.card := counting_lower_bound hT
      rw [hcard] at h2
      have h : ((2 * (n * (n - 2)) : ℕ) : ℝ) ≤ ((14 * b n : ℕ) : ℝ) := Nat.cast_le.mpr h2
      rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (by omega : 2 ≤ n)] at h
      push_cast at h
      nlinarith [h]
  · -- the upper bound: there is a maximal tearing with at most `n²/5 + 3n` blocks
    rcases le_or_gt n 5 with hn5 | hn5
    · -- small `n`: the wasteful tearing is cheap enough
      have hb := b_le (trivialTearing_isMaximalTearing n)
      have hc := trivialTearing_card_le n
      have h1 : (b n : ℝ) ≤ (((n / 3) * n + (n % 3) * (n / 3) : ℕ) : ℝ) :=
        Nat.cast_le.mpr (hb.trans hc)
      have h2 : (((n / 3) * n + (n % 3) * (n / 3) : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 / 5 + 3 * n := by
        have hdiv : ((n / 3 : ℕ) : ℝ) ≤ (n : ℝ) / 3 := Nat.cast_div_le
        have hmod : ((n % 3 : ℕ) : ℝ) ≤ 2 := by
          have hmod3 : n % 3 ≤ 2 := by omega
          exact_mod_cast hmod3
        have hn' : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
        have hn'' : (n : ℝ) ≤ 5 := by exact_mod_cast hn5
        have e1 : ↑(n / 3 : ℕ) * (n : ℝ) ≤ (n : ℝ) ^ 2 / 3 := by
          calc ↑(n / 3 : ℕ) * (n : ℝ) ≤ ((n : ℝ) / 3) * n :=
                mul_le_mul_of_nonneg_right hdiv hn'
            _ = (n : ℝ) ^ 2 / 3 := by ring
        have e2 : ↑(n % 3 : ℕ) * ↑(n / 3 : ℕ) ≤ 2 * (n : ℝ) / 3 := by
          calc ↑(n % 3 : ℕ) * ↑(n / 3 : ℕ) ≤ 2 * ↑(n / 3 : ℕ) :=
                mul_le_mul_of_nonneg_right hmod (Nat.cast_nonneg _)
            _ ≤ 2 * ((n : ℝ) / 3) := mul_le_mul_of_nonneg_left hdiv (by norm_num)
            _ = 2 * (n : ℝ) / 3 := by ring
        push_cast
        nlinarith [e1, e2, hn', hn'', mul_le_mul_of_nonneg_left hn'' hn']
      nlinarith [h1, h2]
    · -- large `n`: the efficient pattern tearing
      have hb := b_le (patTearing_isMaximalTearing (by omega : 6 ≤ n))
      have hc := patTearing_card_le n
      have h1 : (b n : ℝ) ≤ ((n * (n / 5 + 3) : ℕ) : ℝ) := Nat.cast_le.mpr (hb.trans hc)
      have h2 : ((n * (n / 5 + 3) : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 / 5 + 3 * n := by
        push_cast
        have hdiv : ((n / 5 : ℕ) : ℝ) ≤ (n : ℝ) / 5 := Nat.cast_div_le
        have hn' : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
        nlinarith [hdiv, hn']
      nlinarith [h1, h2]

end Usa2002P6
