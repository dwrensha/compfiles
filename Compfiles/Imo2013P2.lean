/-
Copyright (c) 2026 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Combinatorics, .Geometry] }

/-!
# International Mathematical Olympiad 2013, Problem 2

A configuration of 4027 points of the plane is called Colombian if it
consists of 2013 red points and 2014 blue points, and no three of the
points of the configuration are collinear. By drawing some lines, the
plane is divided into several regions. An arrangement of lines is good
for a Colombian configuration if the following two conditions are
satisfied:

 * no line passes through any point of the configuration;
 * no region contains points of both colours.

Find the least value of k such that for any Colombian configuration of
4027 points, there is a good arrangement of k lines.
-/

namespace Imo2013P2

abbrev Pt := EuclideanSpace ℝ (Fin 2)

/-- A configuration of 2013 red points and 2014 blue points in the plane,
all distinct, such that no three points of the configuration are collinear. -/
structure ColombianConfiguration where
  red : Finset Pt
  blue : Finset Pt
  red_card : red.card = 2013
  blue_card : blue.card = 2014
  red_blue_disjoint : Disjoint red blue
  not_collinear : ∀ p₁ ∈ red ∪ blue, ∀ p₂ ∈ red ∪ blue, ∀ p₃ ∈ red ∪ blue,
    p₁ ≠ p₂ → p₁ ≠ p₃ → p₂ ≠ p₃ → ¬ Collinear ℝ {p₁, p₂, p₃}

/--
An arrangement of lines (one-dimensional affine subspaces of the plane)
is *good* for a configuration if no line passes through a point of the
configuration and every red point is strictly separated from every blue
point by at least one of the lines.

(The regions determined by an arrangement of lines are convex, and two
points lying on none of the lines belong to the same region if and only
if they are strictly on the same side of every line. Therefore, requiring
each red-blue pair to be strictly separated by some line is equivalent to
requiring that no region contains points of both colours.)
-/
def GoodArrangement (cfg : ColombianConfiguration) {k : ℕ}
    (lines : Fin k → AffineSubspace ℝ Pt) : Prop :=
  (∀ i, Module.finrank ℝ (lines i).direction = 1) ∧
  (∀ i, ∀ p ∈ cfg.red ∪ cfg.blue, p ∉ lines i) ∧
  (∀ p ∈ cfg.red, ∀ q ∈ cfg.blue, ∃ i, (lines i).SOppSide p q)

snip begin

open scoped RealInnerProductSpace

/-! ### Coordinates in the plane -/

theorem Pt.ext {x y : Pt} (h0 : x 0 = y 0) (h1 : x 1 = y 1) : x = y := by
  apply WithLp.ofLp_injective (p := 2)
  funext i
  fin_cases i <;> assumption

theorem inner_pt (n x : Pt) : ⟪n, x⟫ = n 0 * x 0 + n 1 * x 1 := by
  rw [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, RCLike.inner_apply]
  simp only [conj_trivial]
  ring

/-- Rotation by 90 degrees. -/
def rot90 (v : Pt) : Pt := !₂[-(v 1), v 0]

@[simp] theorem rot90_apply0 (v : Pt) : rot90 v 0 = -(v 1) := rfl

@[simp] theorem rot90_apply1 (v : Pt) : rot90 v 1 = v 0 := rfl

theorem inner_rot90_self (v : Pt) : ⟪rot90 v, v⟫ = 0 := by
  rw [inner_pt, rot90_apply0, rot90_apply1]
  ring

/-- The first standard basis vector. -/
def e₁ : Pt := !₂[1, 0]

theorem inner_e₁ (x : Pt) : ⟪e₁, x⟫ = x 0 := by
  rw [inner_pt]
  show 1 * x 0 + 0 * x 1 = x 0
  ring

theorem e₁_ne_zero : e₁ ≠ 0 := by
  intro h
  have h0 : e₁ 0 = (0 : Pt) 0 := by rw [h]
  have : (1 : ℝ) = 0 := h0
  norm_num at this

theorem rot90_ne_zero {v : Pt} (hv : v ≠ 0) : rot90 v ≠ 0 := by
  intro h
  apply hv
  have h0 : rot90 v 0 = (0 : Pt) 0 := by rw [h]
  have h1 : rot90 v 1 = (0 : Pt) 1 := by rw [h]
  rw [rot90_apply0] at h0
  rw [rot90_apply1] at h1
  exact Pt.ext (by simpa using h1) (by simpa using h0)

theorem eq_smul_of_inner_rot90_eq_zero {v y : Pt} (hv : v ≠ 0)
    (h : ⟪rot90 v, y⟫ = 0) : ∃ t : ℝ, y = t • v := by
  rw [inner_pt, rot90_apply0, rot90_apply1] at h
  have hv' : v 0 ≠ 0 ∨ v 1 ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hv (Pt.ext (by simpa using hc.1) (by simpa using hc.2))
  rcases hv' with h0 | h1
  · refine ⟨y 0 / v 0, Pt.ext ?_ ?_⟩
    · rw [PiLp.smul_apply, smul_eq_mul]
      field_simp
    · rw [PiLp.smul_apply, smul_eq_mul]
      field_simp
      linarith
  · refine ⟨y 1 / v 1, Pt.ext ?_ ?_⟩
    · rw [PiLp.smul_apply, smul_eq_mul]
      field_simp
      linarith
    · rw [PiLp.smul_apply, smul_eq_mul]
      field_simp

/-! ### Collinearity helpers -/

theorem collinear_triple_of_sub_eq_smul {z w x : Pt} (t : ℝ)
    (h : x - z = t • (w - z)) : Collinear ℝ {z, w, x} := by
  rw [collinear_iff_of_mem (Set.mem_insert z {w, x})]
  refine ⟨w - z, fun p hp => ?_⟩
  rcases hp with rfl | rfl | rfl
  · exact ⟨0, by simp⟩
  · exact ⟨1, by simp⟩
  · exact ⟨t, by rw [← h]; simp⟩

theorem collinear_of_inner_rot90_eq_zero {z w x : Pt} (hwz : w ≠ z)
    (h : ⟪rot90 (w - z), x - z⟫ = 0) : Collinear ℝ {z, w, x} := by
  obtain ⟨t, ht⟩ := eq_smul_of_inner_rot90_eq_zero (sub_ne_zero.mpr hwz) h
  exact collinear_triple_of_sub_eq_smul t ht

theorem collinear_of_subset_line {s : Set Pt} {ℓ : AffineSubspace ℝ Pt}
    (hl : Module.finrank ℝ ℓ.direction = 1) (h : s ⊆ ℓ) : Collinear ℝ s := by
  rw [collinear_iff_rank_le_one]
  have h2 : vectorSpan ℝ s ≤ ℓ.direction := vectorSpan_mono ℝ h
  have h3 := Submodule.rank_mono h2
  have h4 : Module.rank ℝ ℓ.direction = 1 := by
    rw [← Module.finrank_eq_rank ℝ, hl, Nat.cast_one]
  rw [h4] at h3
  exact h3

/-! ### Lines as level sets of linear functionals -/

/-- The line `{x | ⟪n, x⟫ = c}`. -/
def perp (n : Pt) (c : ℝ) : AffineSubspace ℝ Pt where
  carrier := {x | ⟪n, x⟫ = c}
  smul_vsub_vadd_mem t p₁ p₂ p₃ h₁ h₂ h₃ := by
    simp only [Set.mem_setOf_eq] at h₁ h₂ h₃ ⊢
    rw [vsub_eq_sub, vadd_eq_add, inner_add_right, real_inner_smul_right,
      inner_sub_right, h₁, h₂, h₃]
    ring

theorem mem_perp {n : Pt} {c : ℝ} {x : Pt} : x ∈ perp n c ↔ ⟪n, x⟫ = c := Iff.rfl

theorem direction_perp {n : Pt} (hn : n ≠ 0) (c : ℝ) :
    (perp n c).direction = LinearMap.ker (innerₛₗ ℝ n) := by
  have hnn : ⟪n, n⟫ ≠ 0 := inner_self_ne_zero.mpr hn
  have hx₀ : (c / ⟪n, n⟫) • n ∈ perp n c := by
    rw [mem_perp, real_inner_smul_right]
    field_simp
  ext v
  rw [AffineSubspace.mem_direction_iff_eq_vsub ⟨_, hx₀⟩]
  constructor
  · rintro ⟨p₁, hp₁, p₂, hp₂, rfl⟩
    rw [LinearMap.mem_ker]
    have e1 : ⟪n, p₁⟫ = c := hp₁
    have e2 : ⟪n, p₂⟫ = c := hp₂
    show ⟪n, p₁ -ᵥ p₂⟫ = 0
    rw [vsub_eq_sub, inner_sub_right, e1, e2, sub_self]
  · intro hv
    rw [LinearMap.mem_ker] at hv
    have hv' : ⟪n, v⟫ = 0 := hv
    refine ⟨v + (c / ⟪n, n⟫) • n, ?_, (c / ⟪n, n⟫) • n, hx₀, by
      rw [vsub_eq_sub]; abel⟩
    rw [mem_perp, inner_add_right, hv', zero_add]
    exact hx₀

theorem finrank_direction_perp {n : Pt} (hn : n ≠ 0) (c : ℝ) :
    Module.finrank ℝ (perp n c).direction = 1 := by
  rw [direction_perp hn]
  have hrn := LinearMap.finrank_range_add_finrank_ker (innerₛₗ ℝ n)
  rw [finrank_euclideanSpace_fin] at hrn
  have hr1 : Module.finrank ℝ (LinearMap.range (innerₛₗ ℝ n)) = 1 := by
    have hle : Module.finrank ℝ (LinearMap.range (innerₛₗ ℝ n)) ≤ 1 := by
      have := Submodule.finrank_le (LinearMap.range (innerₛₗ ℝ n))
      simpa using this
    have hne : LinearMap.range (innerₛₗ ℝ n) ≠ ⊥ := by
      rw [Submodule.ne_bot_iff]
      exact ⟨⟪n, n⟫, LinearMap.mem_range_self _ n, inner_self_ne_zero.mpr hn⟩
    have hpos : 0 < Module.finrank ℝ (LinearMap.range (innerₛₗ ℝ n)) := by
      by_contra hc
      push Not at hc
      rw [Nat.le_zero] at hc
      exact hne (Submodule.finrank_eq_zero.mp hc)
    omega
  omega

/-- The fundamental characterization: `x` and `y` are strictly on opposite sides
of the line `{z | ⟪n, z⟫ = c}` iff their inner products with `n` strictly
sandwich `c`. -/
theorem sOppSide_iff {ℓ : AffineSubspace ℝ Pt} {n : Pt} {c : ℝ}
    (hmem : ∀ z : Pt, z ∈ ℓ ↔ ⟪n, z⟫ = c) (x y : Pt) :
    ℓ.SOppSide x y ↔
      (⟪n, x⟫ < c ∧ c < ⟪n, y⟫) ∨ (⟪n, y⟫ < c ∧ c < ⟪n, x⟫) := by
  have key : ∀ a b : Pt, ⟪n, a⟫ < c → c < ⟪n, b⟫ → ℓ.SOppSide a b := by
    intro a b ha hb
    have hab : (0:ℝ) < ⟪n, b⟫ - ⟪n, a⟫ := by linarith
    set t : ℝ := (c - ⟪n, a⟫) / (⟪n, b⟫ - ⟪n, a⟫) with ht
    have ht0 : 0 < t := div_pos (by linarith) hab
    have ht1 : t < 1 := (div_lt_one hab).mpr (by linarith)
    set p : Pt := a + t • (b - a) with hp
    have hpl : p ∈ ℓ := by
      rw [hmem, hp, inner_add_right, real_inner_smul_right, inner_sub_right, ht]
      field_simp
      ring
    have hane : a ∉ ℓ := by rw [hmem]; exact ne_of_lt ha
    have hbne : b ∉ ℓ := by rw [hmem]; exact (ne_of_lt hb).symm
    refine ⟨⟨p, hpl, p, hpl, ?_⟩, hane, hbne⟩
    have e1 : a -ᵥ p = t • (a - b) := by
      rw [vsub_eq_sub, hp]
      module
    have e2 : p -ᵥ b = (1 - t) • (a - b) := by
      rw [vsub_eq_sub, hp]
      module
    rw [e1, e2]
    have hr : SameRay ℝ (a - b) (a - b) := SameRay.refl _
    exact (hr.nonneg_smul_left ht0.le).nonneg_smul_right (by linarith)
  constructor
  · rintro ⟨⟨p₁, hp₁, p₂, hp₂, hray⟩, hx, hy⟩
    have hxp₁ : x -ᵥ p₁ ≠ 0 := by
      rw [vsub_ne_zero]
      rintro rfl
      exact hx hp₁
    have hyp₂ : p₂ -ᵥ y ≠ 0 := by
      rw [vsub_ne_zero]
      rintro rfl
      exact hy hp₂
    obtain ⟨r₁, r₂, hr₁, hr₂, hr⟩ := hray.exists_pos hxp₁ hyp₂
    have hc₁ : ⟪n, p₁⟫ = c := (hmem p₁).mp hp₁
    have hc₂ : ⟪n, p₂⟫ = c := (hmem p₂).mp hp₂
    have hinner : r₁ * (⟪n, x⟫ - c) = r₂ * (c - ⟪n, y⟫) := by
      have := congrArg (fun v : Pt => ⟪n, v⟫) hr
      simp only [real_inner_smul_right, vsub_eq_sub, inner_sub_right] at this
      rw [hc₁, hc₂] at this
      linarith
    have hxc : ⟪n, x⟫ ≠ c := fun h => hx ((hmem x).mpr h)
    have hyc : ⟪n, y⟫ ≠ c := fun h => hy ((hmem y).mpr h)
    rcases lt_or_gt_of_ne hxc with hlt | hgt
    · left
      refine ⟨hlt, ?_⟩
      rcases lt_or_gt_of_ne hyc with hylt | hygt
      · exfalso
        have l1 : r₁ * (⟪n, x⟫ - c) < 0 :=
          mul_neg_of_pos_of_neg hr₁ (by linarith)
        have l2 : 0 < r₂ * (c - ⟪n, y⟫) := mul_pos hr₂ (by linarith)
        linarith
      · exact hygt
    · right
      refine ⟨?_, hgt⟩
      rcases lt_or_gt_of_ne hyc with hylt | hygt
      · exact hylt
      · exfalso
        have l1 : 0 < r₁ * (⟪n, x⟫ - c) := mul_pos hr₁ (by linarith)
        have l2 : r₂ * (c - ⟪n, y⟫) < 0 :=
          mul_neg_of_pos_of_neg hr₂ (by linarith)
        linarith
  · rintro (⟨hx, hy⟩ | ⟨hy, hx⟩)
    · exact key x y hx hy
    · exact (key y x hy hx).symm

/-- Every one-dimensional affine subspace of the plane is the level set
of a nonzero linear functional. -/
theorem exists_normal {ℓ : AffineSubspace ℝ Pt}
    (hl : Module.finrank ℝ ℓ.direction = 1) :
    ∃ (n : Pt) (c : ℝ), n ≠ 0 ∧ ∀ z : Pt, z ∈ ℓ ↔ ⟪n, z⟫ = c := by
  have hbot : ℓ ≠ ⊥ := by
    intro h
    rw [h, AffineSubspace.direction_bot] at hl
    simp at hl
  obtain ⟨p₀, hp₀⟩ := (AffineSubspace.nonempty_iff_ne_bot ℓ).mpr hbot
  set D := ℓ.direction with hD
  have horth : Module.finrank ℝ Dᗮ = 1 := by
    have := Submodule.finrank_add_finrank_orthogonal D
    rw [hl, finrank_euclideanSpace_fin] at this
    omega
  have hbot' : Dᗮ ≠ ⊥ := by
    intro h
    rw [h] at horth
    simp at horth
  obtain ⟨n, hn, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot'
  have hspan : (ℝ ∙ n) = Dᗮ := by
    apply Submodule.eq_of_le_of_finrank_le
      ((Submodule.span_singleton_le_iff_mem n Dᗮ).mpr hn)
    rw [horth, finrank_span_singleton hn0]
  refine ⟨n, ⟪n, p₀⟫, hn0, fun z => ?_⟩
  rw [← AffineSubspace.vsub_right_mem_direction_iff_mem hp₀ z, ← hD]
  constructor
  · intro hzD
    have : ⟪z -ᵥ p₀, n⟫ = 0 :=
      Submodule.inner_right_of_mem_orthogonal hzD hn
    rw [real_inner_comm] at this
    rw [vsub_eq_sub, inner_sub_right] at this
    linarith
  · intro hz
    have hmem : z -ᵥ p₀ ∈ (ℝ ∙ n)ᗮ := by
      rw [Submodule.mem_orthogonal_singleton_iff_inner_right, vsub_eq_sub,
        inner_sub_right, hz, sub_self]
    rw [hspan, Submodule.orthogonal_orthogonal] at hmem
    exact hmem

/-! ### Upper bound machinery -/

def No3Col (S : Finset Pt) : Prop :=
  ∀ p₁ ∈ S, ∀ p₂ ∈ S, ∀ p₃ ∈ S,
    p₁ ≠ p₂ → p₁ ≠ p₃ → p₂ ≠ p₃ → ¬ Collinear ℝ {p₁, p₂, p₃}

/-- Cut a subset `Z` of `S` off from the rest of `S` with a single line,
given a linear functional whose values on `Z` all lie strictly below its
values on `S \ Z`. -/
theorem exists_cut {S Z : Finset Pt} (hne : (S \ Z).Nonempty)
    {n : Pt} (hn : n ≠ 0) {t : ℝ} (hZ : ∀ p ∈ Z, ⟪n, p⟫ ≤ t)
    (hX : ∀ x ∈ S \ Z, t < ⟪n, x⟫) :
    ∃ ℓ : AffineSubspace ℝ Pt, Module.finrank ℝ ℓ.direction = 1 ∧
      (∀ p ∈ S, p ∉ ℓ) ∧ ∀ p ∈ Z, ∀ x ∈ S \ Z, ℓ.SOppSide p x := by
  obtain ⟨m, hmmem, hmle⟩ := (S \ Z).exists_min_image (fun x => ⟪n, x⟫) hne
  set c := (t + ⟪n, m⟫) / 2 with hc
  have htm : t < ⟪n, m⟫ := hX m hmmem
  have htc : t < c := by rw [hc]; linarith
  have hcm : c < ⟪n, m⟫ := by rw [hc]; linarith
  refine ⟨perp n c, finrank_direction_perp hn c, ?_, ?_⟩
  · intro p hp
    rw [mem_perp]
    by_cases hpZ : p ∈ Z
    · exact ne_of_lt (lt_of_le_of_lt (hZ p hpZ) htc)
    · have hps : p ∈ S \ Z := Finset.mem_sdiff.mpr ⟨hp, hpZ⟩
      exact (ne_of_lt (lt_of_lt_of_le hcm (hmle p hps))).symm
  · intro p hpZ x hx
    rw [sOppSide_iff (fun z => mem_perp) p x]
    exact Or.inl ⟨lt_of_le_of_lt (hZ p hpZ) htc,
                  lt_of_lt_of_le hcm (hmle x hx)⟩

/-- Cut a pair of points `{A, B}` of `S` off from the rest of `S` with two
lines parallel to the segment `AB`. -/
theorem exists_strip {S : Finset Pt} (h3 : No3Col S) {A B : Pt}
    (hA : A ∈ S) (hB : B ∈ S) (hAB : A ≠ B)
    (hne : (S \ ({A, B} : Finset Pt)).Nonempty) :
    ∃ ℓ₁ ℓ₂ : AffineSubspace ℝ Pt,
      Module.finrank ℝ ℓ₁.direction = 1 ∧ Module.finrank ℝ ℓ₂.direction = 1 ∧
      (∀ p ∈ S, p ∉ ℓ₁ ∧ p ∉ ℓ₂) ∧
      ∀ p ∈ ({A, B} : Finset Pt), ∀ x ∈ S \ ({A, B} : Finset Pt),
        ℓ₁.SOppSide p x ∨ ℓ₂.SOppSide p x := by
  set n := rot90 (B - A) with hn'
  have hn : n ≠ 0 := rot90_ne_zero (sub_ne_zero.mpr hAB.symm)
  set c₀ := ⟪n, A⟫ with hc₀
  have hcB : ⟪n, B⟫ = c₀ := by
    have h := inner_rot90_self (B - A)
    rw [inner_sub_right] at h
    rw [hc₀]
    linarith
  have hvals : ∀ p ∈ ({A, B} : Finset Pt), ⟪n, p⟫ = c₀ := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp'
    · rfl
    · rw [Finset.mem_singleton] at hp'
      subst hp'
      exact hcB
  have hoff : ∀ x ∈ S \ ({A, B} : Finset Pt), ⟪n, x⟫ ≠ c₀ := by
    intro x hx h
    rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at hx
    obtain ⟨hxS, hx2⟩ := hx
    push Not at hx2
    have hzero : ⟪rot90 (B - A), x - A⟫ = 0 := by
      rw [inner_sub_right, ← hn', h, hc₀, sub_self]
    have hcol : Collinear ℝ {A, B, x} :=
      collinear_of_inner_rot90_eq_zero hAB.symm hzero
    exact h3 A hA B hB x hxS hAB (Ne.symm hx2.1) (Ne.symm hx2.2) hcol
  obtain ⟨x₀, hx₀, hminx⟩ :=
    (S \ ({A, B} : Finset Pt)).exists_min_image (fun x => |⟪n, x⟫ - c₀|) hne
  set ε := |⟪n, x₀⟫ - c₀| with hε'
  have hε : 0 < ε := abs_pos.mpr (sub_ne_zero.mpr (hoff _ hx₀))
  have hbig : ∀ x ∈ S \ ({A, B} : Finset Pt), ε ≤ |⟪n, x⟫ - c₀| := hminx
  refine ⟨perp n (c₀ + ε / 2), perp n (c₀ - ε / 2),
    finrank_direction_perp hn _, finrank_direction_perp hn _, ?_, ?_⟩
  · intro p hp
    by_cases hp2 : p ∈ ({A, B} : Finset Pt)
    · have hv := hvals p hp2
      constructor <;> rw [mem_perp, hv] <;> intro h <;> linarith
    · have hps : p ∈ S \ ({A, B} : Finset Pt) := Finset.mem_sdiff.mpr ⟨hp, hp2⟩
      have h := hbig p hps
      constructor <;> rw [mem_perp] <;> intro heq <;> rw [heq] at h
      · rw [show c₀ + ε / 2 - c₀ = ε / 2 by ring,
          abs_of_pos (by linarith)] at h
        linarith
      · rw [show c₀ - ε / 2 - c₀ = -(ε / 2) by ring, abs_neg,
          abs_of_pos (by linarith)] at h
        linarith
  · intro p hp x hx
    have hv := hvals p hp
    have h := hbig x hx
    rcases le_or_gt c₀ ⟪n, x⟫ with hge | hlt
    · left
      rw [sOppSide_iff (fun z => mem_perp) p x]
      rw [abs_of_nonneg (by linarith)] at h
      exact Or.inl ⟨by rw [hv]; linarith, by linarith⟩
    · right
      rw [sOppSide_iff (fun z => mem_perp) p x]
      rw [abs_of_neg (by linarith)] at h
      exact Or.inr ⟨by linarith, by rw [hv]; linarith⟩

/-- Isolate an even-sized subset `C` of `S` into pairs, each pair confined
to its own strip between two parallel lines. -/
theorem pair_strips {S : Finset Pt} (h3 : No3Col S) (hcard : 4 ≤ S.card) :
    ∀ (m : ℕ) (C : Finset Pt), C ⊆ S → C.card = 2 * m →
    ∃ L : List (AffineSubspace ℝ Pt), L.length = 2 * m ∧
      (∀ ℓ ∈ L, Module.finrank ℝ ℓ.direction = 1) ∧
      (∀ ℓ ∈ L, ∀ p ∈ S, p ∉ ℓ) ∧
      (∀ p ∈ C, ∀ x ∈ S \ C, ∃ ℓ ∈ L, ℓ.SOppSide p x) := by
  intro m
  induction m with
  | zero =>
    intro C _ hC
    refine ⟨[], rfl, by simp, by simp, ?_⟩
    intro p hp
    rw [Finset.card_eq_zero.mp hC] at hp
    exact absurd hp (Finset.notMem_empty p)
  | succ m ih =>
    intro C hCS hC
    have h1 : 0 < C.card := by omega
    obtain ⟨A, hA⟩ := Finset.card_pos.mp h1
    have h2 : 0 < (C.erase A).card := by
      rw [Finset.card_erase_of_mem hA]
      omega
    obtain ⟨B, hB⟩ := Finset.card_pos.mp h2
    have hBA : B ≠ A := Finset.ne_of_mem_erase hB
    have hBC : B ∈ C := Finset.mem_of_mem_erase hB
    have hne : (S \ ({A, B} : Finset Pt)).Nonempty := by
      rw [← Finset.card_pos]
      have hsub := Finset.le_card_sdiff ({A, B} : Finset Pt) S
      have hABcard : ({A, B} : Finset Pt).card ≤ 2 :=
        le_trans (Finset.card_insert_le A {B}) (by rw [Finset.card_singleton])
      omega
    obtain ⟨ℓ₁, ℓ₂, hr₁, hr₂, havoid, hsep⟩ :=
      exists_strip h3 (hCS hA) (hCS hBC) hBA.symm hne
    set C' := (C.erase A).erase B with hC'
    have hC'sub : C' ⊆ C :=
      (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)
    have hC'card : C'.card = 2 * m := by
      rw [hC', Finset.card_erase_of_mem hB, Finset.card_erase_of_mem hA, hC]
      omega
    obtain ⟨L', hlen, hline, havoid', hsep'⟩ := ih C' (hC'sub.trans hCS) hC'card
    refine ⟨ℓ₁ :: ℓ₂ :: L', by rw [List.length_cons, List.length_cons, hlen]; ring, ?_, ?_, ?_⟩
    · intro ℓ hℓ
      rcases List.mem_cons.mp hℓ with rfl | hℓ
      · exact hr₁
      rcases List.mem_cons.mp hℓ with rfl | hℓ
      · exact hr₂
      · exact hline ℓ hℓ
    · intro ℓ hℓ
      rcases List.mem_cons.mp hℓ with rfl | hℓ
      · exact fun p hp => (havoid p hp).1
      rcases List.mem_cons.mp hℓ with rfl | hℓ
      · exact fun p hp => (havoid p hp).2
      · exact havoid' ℓ hℓ
    · intro p hp x hx
      rw [Finset.mem_sdiff] at hx
      obtain ⟨hxS, hxC⟩ := hx
      by_cases hpAB : p = A ∨ p = B
      · have hp2 : p ∈ ({A, B} : Finset Pt) := by
          rcases hpAB with rfl | rfl
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
        have hx2 : x ∈ S \ ({A, B} : Finset Pt) := by
          rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
          refine ⟨hxS, ?_⟩
          rintro (rfl | rfl)
          · exact hxC hA
          · exact hxC hBC
        rcases hsep p hp2 x hx2 with h | h
        · exact ⟨ℓ₁, List.mem_cons_self .., h⟩
        · exact ⟨ℓ₂, List.mem_cons_of_mem _ (List.mem_cons_self ..), h⟩
      · rw [not_or] at hpAB
        have hpC' : p ∈ C' := by
          rw [hC', Finset.mem_erase, Finset.mem_erase]
          exact ⟨hpAB.2, hpAB.1, hp⟩
        have hxC' : x ∈ S \ C' := by
          rw [Finset.mem_sdiff]
          exact ⟨hxS, fun hc => hxC (hC'sub hc)⟩
        obtain ⟨ℓ, hℓL, hℓ⟩ := hsep' p hpC' x hxC'
        exact ⟨ℓ, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hℓL), hℓ⟩

/-- The "tilting" trick: if all points of `S` other than `z` and `w` lie
strictly on the positive side of the line through `z` and `w`, then there is
a linear functional whose unique minimizer over `S` is `w`. -/
theorem mtrick {S : Finset Pt} {z w : Pt} (hzw : z ≠ w)
    {n₀ : Pt} (horth : ⟪n₀, w - z⟫ = 0)
    (hpos : ∀ x ∈ S, x ≠ z → x ≠ w → 0 < ⟪n₀, x - z⟫)
    (hne : (S \ ({z, w} : Finset Pt)).Nonempty) :
    ∃ n : Pt, n ≠ 0 ∧ ∀ x ∈ S, x ≠ w → ⟪n, w⟫ < ⟪n, x⟫ := by
  set u := w - z with hu
  have hu0 : u ≠ 0 := sub_ne_zero.mpr hzw.symm
  have huu : 0 < ⟪u, u⟫ := real_inner_self_pos.mpr hu0
  have hmemx : ∀ x ∈ S \ ({z, w} : Finset Pt), x ∈ S ∧ x ≠ z ∧ x ≠ w := by
    intro x hx
    rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hx
    exact ⟨hx.1, hx.2.1, hx.2.2⟩
  obtain ⟨xβ, hxβ, hβmin⟩ :=
    (S \ ({z, w} : Finset Pt)).exists_min_image (fun x => ⟪n₀, x - z⟫) hne
  set β := ⟪n₀, xβ - z⟫ with hβ
  have hβpos : 0 < β := by
    obtain ⟨h1, h2, h3'⟩ := hmemx xβ hxβ
    exact hpos xβ h1 h2 h3'
  obtain ⟨xγ, hxγ, hγmax⟩ :=
    (S \ ({z, w} : Finset Pt)).exists_max_image (fun x => ⟪u, x - z⟫) hne
  set γ := ⟪u, xγ - z⟫ with hγ
  set M := (|γ| + 1) / β with hM
  have hMpos : 0 < M := div_pos (by positivity) hβpos
  have hMβ : M * β = |γ| + 1 := div_mul_cancel₀ _ (ne_of_gt hβpos)
  refine ⟨M • n₀ - u, ?_, ?_⟩
  · intro h
    have h2 : ⟪M • n₀ - u, u⟫ = 0 := by rw [h, inner_zero_left]
    rw [inner_sub_left, real_inner_smul_left, hu, horth, ← hu] at h2
    rw [mul_zero, zero_sub, neg_eq_zero] at h2
    exact absurd h2 (ne_of_gt huu)
  · intro x hx hxw
    have hsub : ⟪M • n₀ - u, x⟫ - ⟪M • n₀ - u, w⟫ = ⟪M • n₀ - u, x - w⟫ :=
      (inner_sub_right _ _ _).symm
    by_cases hxz : x = z
    · subst hxz
      have hzw' : ⟪M • n₀ - u, x - w⟫ = ⟪u, u⟫ := by
        rw [show x - w = -u by rw [hu]; abel, inner_neg_right,
          inner_sub_left, real_inner_smul_left, hu, horth, ← hu]
        ring
      linarith [hzw' ▸ hsub]
    · have hp := hpos x hx hxz hxw
      have hxmem : x ∈ S \ ({z, w} : Finset Pt) := by
        rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hx, hxz, hxw⟩
      have hβle : β ≤ ⟪n₀, x - z⟫ := hβmin x hxmem
      have hγge : ⟪u, x - z⟫ ≤ γ := hγmax x hxmem
      have expand : ⟪M • n₀ - u, x - w⟫
          = M * ⟪n₀, x - z⟫ - M * ⟪n₀, u⟫ - ⟪u, x - z⟫ + ⟪u, u⟫ := by
        have hxw' : x - w = (x - z) - u := by rw [hu]; abel
        have e1 : ⟪M • n₀ - u, (x - z) - u⟫
            = ⟪M • n₀ - u, x - z⟫ - ⟪M • n₀ - u, u⟫ := inner_sub_right _ _ _
        have e2 : ⟪M • n₀ - u, x - z⟫ = M * ⟪n₀, x - z⟫ - ⟪u, x - z⟫ := by
          rw [inner_sub_left, real_inner_smul_left]
        have e3 : ⟪M • n₀ - u, u⟫ = M * ⟪n₀, u⟫ - ⟪u, u⟫ := by
          rw [inner_sub_left, real_inner_smul_left]
        rw [hxw', e1, e2, e3]
        ring
      rw [horth] at expand
      have l1 : M * β ≤ M * ⟪n₀, x - z⟫ :=
        mul_le_mul_of_nonneg_left hβle hMpos.le
      have l2 : γ ≤ |γ| := le_abs_self γ
      have : 0 < ⟪M • n₀ - u, x - w⟫ := by
        rw [expand]
        linarith
      linarith

/-- At the leftmost point `z` of `S` (assuming it is the unique leftmost
point), there is another point `w` of `S` such that the line through `z` and
`w` supports `S`: all other points are strictly on its positive side. -/
theorem exists_hull_edge {S : Finset Pt} (h3 : No3Col S) {z : Pt} (hz : z ∈ S)
    (hmin : ∀ x ∈ S, x ≠ z → z 0 < x 0) (hne : (S.erase z).Nonempty) :
    ∃ w ∈ S, w ≠ z ∧ ∃ n₀ : Pt, n₀ ≠ 0 ∧ ⟪n₀, w - z⟫ = 0 ∧
      ∀ x ∈ S, x ≠ z → x ≠ w → 0 < ⟪n₀, x - z⟫ := by
  obtain ⟨w, hw, hwmin⟩ :=
    (S.erase z).exists_min_image (fun x => (x 1 - z 1) / (x 0 - z 0)) hne
  have hwS : w ∈ S := Finset.mem_of_mem_erase hw
  have hwz : w ≠ z := Finset.ne_of_mem_erase hw
  set n₀ := rot90 (w - z) with hn₀
  have ha : 0 < w 0 - z 0 := by
    have := hmin w hwS hwz
    linarith
  refine ⟨w, hwS, hwz, n₀, rot90_ne_zero (sub_ne_zero.mpr hwz),
    inner_rot90_self _, ?_⟩
  intro x hx hxz hxw
  have hb : 0 < x 0 - z 0 := by
    have := hmin x hx hxz
    linarith
  have hslope : (w 1 - z 1) / (w 0 - z 0) ≤ (x 1 - z 1) / (x 0 - z 0) :=
    hwmin x (Finset.mem_erase.mpr ⟨hxz, hx⟩)
  have hcross : ⟪n₀, x - z⟫
      = (w 0 - z 0) * (x 1 - z 1) - (w 1 - z 1) * (x 0 - z 0) := by
    rw [hn₀, inner_pt, rot90_apply0, rot90_apply1,
      PiLp.sub_apply, PiLp.sub_apply, PiLp.sub_apply, PiLp.sub_apply]
    ring
  have hsne : (w 1 - z 1) / (w 0 - z 0) ≠ (x 1 - z 1) / (x 0 - z 0) := by
    intro h
    have hcross0 : ⟪n₀, x - z⟫ = 0 := by
      rw [hcross]
      rw [div_eq_div_iff (by linarith) (by linarith)] at h
      linarith
    have hcol : Collinear ℝ {z, w, x} :=
      collinear_of_inner_rot90_eq_zero hwz hcross0
    exact h3 z hz w hwS x hx hwz.symm hxz.symm hxw.symm hcol
  have hstrict : (w 1 - z 1) / (w 0 - z 0) < (x 1 - z 1) / (x 0 - z 0) :=
    lt_of_le_of_ne hslope hsne
  rw [hcross]
  have key : (w 0 - z 0) * (x 1 - z 1) - (w 1 - z 1) * (x 0 - z 0)
      = ((w 0 - z 0) * (x 0 - z 0))
        * ((x 1 - z 1) / (x 0 - z 0) - (w 1 - z 1) / (w 0 - z 0)) := by
    field_simp
  rw [key]
  exact mul_pos (mul_pos ha hb) (sub_pos.mpr hstrict)

/-- Given a single line cutting a subset `Z` of one of the two color classes
`C` off from the rest of the configuration, where `C \ Z` has 2012 elements,
complete it to a good arrangement of 2013 lines using strips. -/
theorem assemble (cfg : ColombianConfiguration)
    {C Z : Finset Pt} (hC : C = cfg.red ∨ C = cfg.blue) (hZC : Z ⊆ C)
    (hcards : (C \ Z).card = 2012)
    {ℓ₀ : AffineSubspace ℝ Pt} (hr₀ : Module.finrank ℝ ℓ₀.direction = 1)
    (havoid₀ : ∀ p ∈ cfg.red ∪ cfg.blue, p ∉ ℓ₀)
    (hsep₀ : ∀ p ∈ Z, ∀ x ∈ (cfg.red ∪ cfg.blue) \ Z, ℓ₀.SOppSide p x) :
    ∃ lines : Fin 2013 → AffineSubspace ℝ Pt, GoodArrangement cfg lines := by
  set S := cfg.red ∪ cfg.blue with hS
  have h3 : No3Col S := cfg.not_collinear
  have hScard : S.card = 4027 := by
    rw [hS, Finset.card_union_of_disjoint cfg.red_blue_disjoint,
      cfg.red_card, cfg.blue_card]
  have hCS : C ⊆ S := by
    rcases hC with rfl | rfl
    · exact Finset.subset_union_left
    · exact Finset.subset_union_right
  obtain ⟨L', hlen, hline, havoid', hsep'⟩ :=
    pair_strips h3 (by omega) 1006 (C \ Z)
      ((Finset.sdiff_subset).trans hCS) (by rw [hcards])
  have hmain : ∀ p ∈ C, ∀ x ∈ S \ C, ∃ ℓ ∈ ℓ₀ :: L', ℓ.SOppSide p x := by
    intro p hp x hx
    rw [Finset.mem_sdiff] at hx
    by_cases hpZ : p ∈ Z
    · refine ⟨ℓ₀, List.mem_cons_self .., hsep₀ p hpZ x ?_⟩
      rw [Finset.mem_sdiff]
      exact ⟨hx.1, fun hc => hx.2 (hZC hc)⟩
    · have hpC' : p ∈ C \ Z := Finset.mem_sdiff.mpr ⟨hp, hpZ⟩
      have hxC' : x ∈ S \ (C \ Z) := by
        rw [Finset.mem_sdiff]
        exact ⟨hx.1, fun hc => hx.2 (Finset.mem_sdiff.mp hc).1⟩
      obtain ⟨ℓ, hℓL, hℓ⟩ := hsep' p hpC' x hxC'
      exact ⟨ℓ, List.mem_cons_of_mem _ hℓL, hℓ⟩
  set L : List (AffineSubspace ℝ Pt) := ℓ₀ :: L' with hL
  have hLlen : L.length = 2013 := by
    rw [hL, List.length_cons, hlen]
  have hLline : ∀ ℓ ∈ L, Module.finrank ℝ ℓ.direction = 1 := by
    intro ℓ hℓ
    rcases List.mem_cons.mp hℓ with rfl | hℓ
    · exact hr₀
    · exact hline ℓ hℓ
  have hLavoid : ∀ ℓ ∈ L, ∀ p ∈ S, p ∉ ℓ := by
    intro ℓ hℓ
    rcases List.mem_cons.mp hℓ with rfl | hℓ
    · exact havoid₀
    · exact havoid' ℓ hℓ
  have hsep : ∀ p ∈ cfg.red, ∀ q ∈ cfg.blue, ∃ ℓ ∈ L, ℓ.SOppSide p q := by
    intro p hp q hq
    rcases hC with rfl | rfl
    · refine hmain p hp q ?_
      rw [Finset.mem_sdiff]
      exact ⟨Finset.mem_union_right _ hq,
        Finset.disjoint_right.mp cfg.red_blue_disjoint hq⟩
    · obtain ⟨ℓ, hℓL, hℓ⟩ := hmain q hq p (by
        rw [Finset.mem_sdiff]
        exact ⟨Finset.mem_union_left _ hp,
          Finset.disjoint_left.mp cfg.red_blue_disjoint hp⟩)
      exact ⟨ℓ, hℓL, hℓ.symm⟩
  refine ⟨fun i => L[i.val]'(by rw [hLlen]; exact i.isLt), ?_, ?_, ?_⟩
  · intro i
    exact hLline _ (List.getElem_mem _)
  · intro i p hp
    exact hLavoid _ (List.getElem_mem _) p hp
  · intro p hp q hq
    obtain ⟨ℓ, hℓL, hℓ⟩ := hsep p hp q hq
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hℓL
    rw [hLlen] at hj
    exact ⟨⟨j, hj⟩, hℓ⟩

/-- 2013 lines always suffice. -/
theorem upper_bound (cfg : ColombianConfiguration) :
    ∃ lines : Fin 2013 → AffineSubspace ℝ Pt, GoodArrangement cfg lines := by
  classical
  set S := cfg.red ∪ cfg.blue with hS
  have h3 : No3Col S := cfg.not_collinear
  have hScard : S.card = 4027 := by
    rw [hS, Finset.card_union_of_disjoint cfg.red_blue_disjoint,
      cfg.red_card, cfg.blue_card]
  have hSne : S.Nonempty := by
    rw [← Finset.card_pos, hScard]
    norm_num
  -- the leftmost points of the configuration
  obtain ⟨z', hz'S, hz'min⟩ := S.exists_min_image (fun p => p 0) hSne
  set m₀ : ℝ := z' 0 with hm₀
  set A : Finset Pt := S.filter (fun p => p 0 = m₀) with hA
  have hAS : A ⊆ S := Finset.filter_subset _ _
  have hz'A : z' ∈ A := by
    rw [hA, Finset.mem_filter]
    exact ⟨hz'S, rfl⟩
  have hAmem : ∀ p ∈ A, p ∈ S ∧ p 0 = m₀ := by
    intro p hp
    rw [hA, Finset.mem_filter] at hp
    exact hp
  have hnotA : ∀ x ∈ S, x ∉ A → m₀ < x 0 := by
    intro x hxS hxA
    have hge : m₀ ≤ x 0 := hz'min x hxS
    have hne : x 0 ≠ m₀ := by
      intro h
      exact hxA (by rw [hA, Finset.mem_filter]; exact ⟨hxS, h⟩)
    exact lt_of_le_of_ne hge (Ne.symm hne)
  -- at most two leftmost points, since they are all on a vertical line
  have hA2 : A.card ≤ 2 := by
    by_contra hc
    push Not at hc
    obtain ⟨a, ha, b, hb, c', hc', hab, hac, hbc⟩ := Finset.two_lt_card.mp hc
    obtain ⟨haS, ha0⟩ := hAmem a ha
    obtain ⟨hbS, hb0⟩ := hAmem b hb
    obtain ⟨hcS, hc0⟩ := hAmem c' hc'
    have hzero : ⟪rot90 (b - a), c' - a⟫ = 0 := by
      rw [inner_pt, rot90_apply0, rot90_apply1,
        PiLp.sub_apply, PiLp.sub_apply, PiLp.sub_apply, PiLp.sub_apply,
        ha0, hb0, hc0]
      ring
    exact h3 a haS b hbS c' hcS hab hac hbc
      (collinear_of_inner_rot90_eq_zero (Ne.symm hab) hzero)
  have hApos : 0 < A.card := Finset.card_pos.mpr ⟨z', hz'A⟩
  -- a helper to build the vertical-pair tilting data when `A = {z, w}`
  have hvert : ∀ z w : Pt, z ∈ A → w ∈ A → z ≠ w →
      ∃ n₀ : Pt, n₀ ≠ 0 ∧ ⟪n₀, w - z⟫ = 0 ∧
        ∀ x ∈ S, x ≠ z → x ≠ w → 0 < ⟪n₀, x - z⟫ := by
    intro z w hzA hwA hzw
    obtain ⟨hzS, hz0⟩ := hAmem z hzA
    obtain ⟨hwS, hw0⟩ := hAmem w hwA
    have hu1 : w 1 - z 1 ≠ 0 := by
      intro h
      exact hzw (Pt.ext (by rw [hz0, hw0]) (by linarith))
    set s : ℝ := -(w 1 - z 1) with hs'
    refine ⟨s⁻¹ • rot90 (w - z), ?_, ?_, ?_⟩
    · apply smul_ne_zero
      · rw [hs']
        intro h
        exact hu1 (by linarith [neg_eq_zero.mp (inv_eq_zero.mp h)])
      · exact rot90_ne_zero (sub_ne_zero.mpr hzw.symm)
    · rw [real_inner_smul_left, inner_rot90_self, mul_zero]
    · intro x hx hxz hxw
      have hx0 : m₀ < x 0 := by
        apply hnotA x hx
        intro hxA
        exact absurd (Finset.two_lt_card.mpr
          ⟨z, hzA, w, hwA, x, hxA, hzw, Ne.symm hxz, Ne.symm hxw⟩) (by omega)
      have hinner : ⟪rot90 (w - z), x - z⟫ = -(w 1 - z 1) * (x 0 - m₀) := by
        rw [inner_pt, rot90_apply0, rot90_apply1]
        simp only [PiLp.sub_apply]
        rw [hw0, hz0]
        ring
      have hs0 : s ≠ 0 := neg_ne_zero.mpr hu1
      rw [real_inner_smul_left, hinner, ← hs', inv_mul_cancel_left₀ hs0]
      linarith
  -- helper: cut a single point or a pair off, then assemble
  have hsingle : ∀ r : Pt, r ∈ S →
      (∃ n : Pt, n ≠ 0 ∧ ∀ x ∈ S, x ≠ r → ⟪n, r⟫ < ⟪n, x⟫) →
      ∃ ℓ₀ : AffineSubspace ℝ Pt,
        Module.finrank ℝ ℓ₀.direction = 1 ∧ (∀ p ∈ S, p ∉ ℓ₀) ∧
        ∀ p ∈ ({r} : Finset Pt), ∀ x ∈ S \ ({r} : Finset Pt),
          ℓ₀.SOppSide p x := by
    intro r hrS ⟨n, hn, hmin'⟩
    have hne : (S \ ({r} : Finset Pt)).Nonempty := by
      rw [← Finset.card_pos]
      have hd := Finset.le_card_sdiff ({r} : Finset Pt) S
      rw [Finset.card_singleton] at hd
      omega
    apply exists_cut hne hn (t := ⟪n, r⟫)
    · intro p hp
      rw [Finset.mem_singleton] at hp
      subst hp
      exact le_refl _
    · intro x hx
      rw [Finset.mem_sdiff, Finset.mem_singleton] at hx
      exact hmin' x hx.1 hx.2
  -- decide based on the colors of the leftmost points
  by_cases hred : ∃ r ∈ A, r ∈ cfg.red
  · -- a leftmost point is red: cut it off alone with one line
    obtain ⟨r, hrA, hrred⟩ := hred
    obtain ⟨hrS, hr0⟩ := hAmem r hrA
    have hone : ∃ ℓ₀ : AffineSubspace ℝ Pt,
        Module.finrank ℝ ℓ₀.direction = 1 ∧ (∀ p ∈ S, p ∉ ℓ₀) ∧
        ∀ p ∈ ({r} : Finset Pt), ∀ x ∈ S \ ({r} : Finset Pt),
          ℓ₀.SOppSide p x := by
      apply hsingle r hrS
      rcases (by omega : A.card = 1 ∨ A.card = 2) with h1 | h2
      · -- unique leftmost point: vertical cut
        refine ⟨e₁, e₁_ne_zero, ?_⟩
        intro x hx hxr
        have hxA : x ∉ A := by
          intro hxA
          obtain ⟨e, he⟩ := Finset.card_eq_one.mp h1
          rw [he, Finset.mem_singleton] at hxA hrA
          exact hxr (hxA.trans hrA.symm)
        rw [inner_e₁, inner_e₁, hr0]
        exact hnotA x hx hxA
      · -- two leftmost points: tilt
        obtain ⟨b', hb'⟩ : (A.erase r).Nonempty := by
          rw [← Finset.card_pos, Finset.card_erase_of_mem hrA, h2]
          norm_num
        have hb'A : b' ∈ A := Finset.mem_of_mem_erase hb'
        have hb'r : b' ≠ r := Finset.ne_of_mem_erase hb'
        obtain ⟨n₀, hn₀, horth, hpos⟩ := hvert b' r hb'A hrA hb'r
        have hne2 : (S \ ({b', r} : Finset Pt)).Nonempty := by
          rw [← Finset.card_pos]
          have hd := Finset.le_card_sdiff ({b', r} : Finset Pt) S
          have hc2 : ({b', r} : Finset Pt).card ≤ 2 :=
            le_trans (Finset.card_insert_le _ _) (by rw [Finset.card_singleton])
          omega
        exact mtrick hb'r horth hpos hne2
    obtain ⟨ℓ₀, hr₀, havoid₀, hsep₀⟩ := hone
    refine assemble cfg (Or.inl rfl)
      (Finset.singleton_subset_iff.mpr hrred) ?_ hr₀ havoid₀ hsep₀
    rw [Finset.card_sdiff_of_subset (Finset.singleton_subset_iff.mpr hrred),
      Finset.card_singleton, cfg.red_card]
  · -- all leftmost points are blue
    push Not at hred
    have hAblue : ∀ p ∈ A, p ∈ cfg.blue := by
      intro p hp
      have hpS := (hAmem p hp).1
      rw [hS, Finset.mem_union] at hpS
      rcases hpS with h | h
      · exact absurd h (hred p hp)
      · exact h
    rcases (by omega : A.card = 1 ∨ A.card = 2) with h1 | h2
    · -- unique leftmost point z', blue: find a supporting hull edge at z'
      have hAz : A = {z'} := by
        obtain ⟨e, he⟩ := Finset.card_eq_one.mp h1
        rw [he, Finset.mem_singleton] at hz'A
        rw [he, hz'A]
      have hminz : ∀ x ∈ S, x ≠ z' → z' 0 < x 0 := by
        intro x hx hxz
        apply hnotA x hx
        rw [hAz, Finset.mem_singleton]
        exact hxz
      have hneerase : (S.erase z').Nonempty := by
        rw [← Finset.card_pos, Finset.card_erase_of_mem hz'S]
        omega
      obtain ⟨w, hwS, hwz, n₀, hn₀, horth, hpos⟩ :=
        exists_hull_edge h3 hz'S hminz hneerase
      have hzblue : z' ∈ cfg.blue := hAblue z' hz'A
      have hne2 : (S \ ({z', w} : Finset Pt)).Nonempty := by
        rw [← Finset.card_pos]
        have hd := Finset.le_card_sdiff ({z', w} : Finset Pt) S
        have hc2 : ({z', w} : Finset Pt).card ≤ 2 :=
          le_trans (Finset.card_insert_le _ _) (by rw [Finset.card_singleton])
        omega
      have hwSu := Finset.mem_union.mp (hS ▸ hwS)
      rcases hwSu with hwred | hwblue
      · -- w is red: tilt to cut w off alone
        have hone := hsingle w hwS (mtrick (Ne.symm hwz) horth hpos hne2)
        obtain ⟨ℓ₀, hr₀, havoid₀, hsep₀⟩ := hone
        refine assemble cfg (Or.inl rfl)
          (Finset.singleton_subset_iff.mpr hwred) ?_ hr₀ havoid₀ hsep₀
        rw [Finset.card_sdiff_of_subset (Finset.singleton_subset_iff.mpr hwred),
          Finset.card_singleton, cfg.red_card]
      · -- w is blue: cut the blue pair {z', w} off with one line
        have hZb : ({z', w} : Finset Pt) ⊆ cfg.blue := by
          intro p hp
          rcases Finset.mem_insert.mp hp with rfl | hp'
          · exact hzblue
          · rw [Finset.mem_singleton] at hp'
            subst hp'
            exact hwblue
        have hcut : ∃ ℓ₀ : AffineSubspace ℝ Pt,
            Module.finrank ℝ ℓ₀.direction = 1 ∧ (∀ p ∈ S, p ∉ ℓ₀) ∧
            ∀ p ∈ ({z', w} : Finset Pt), ∀ x ∈ S \ ({z', w} : Finset Pt),
              ℓ₀.SOppSide p x := by
          apply exists_cut hne2 hn₀ (t := ⟪n₀, z'⟫)
          · intro p hp
            rcases Finset.mem_insert.mp hp with rfl | hp'
            · exact le_refl _
            · rw [Finset.mem_singleton] at hp'
              subst hp'
              have := horth
              rw [inner_sub_right] at this
              linarith
          · intro x hx
            rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton,
              not_or] at hx
            have := hpos x hx.1 hx.2.1 hx.2.2
            rw [inner_sub_right] at this
            linarith
        obtain ⟨ℓ₀, hr₀, havoid₀, hsep₀⟩ := hcut
        refine assemble cfg (Or.inr rfl) hZb ?_ hr₀ havoid₀ hsep₀
        rw [Finset.card_sdiff_of_subset hZb, cfg.blue_card]
        rw [Finset.card_insert_of_notMem (by
          rw [Finset.mem_singleton]
          exact Ne.symm hwz), Finset.card_singleton]
    · -- two leftmost points, both blue: cut the pair with one line
      have hAb : A ⊆ cfg.blue := fun p hp => hAblue p hp
      have hne2 : (S \ A).Nonempty := by
        rw [← Finset.card_pos]
        have hd := Finset.le_card_sdiff A S
        omega
      have hcut : ∃ ℓ₀ : AffineSubspace ℝ Pt,
          Module.finrank ℝ ℓ₀.direction = 1 ∧ (∀ p ∈ S, p ∉ ℓ₀) ∧
          ∀ p ∈ A, ∀ x ∈ S \ A, ℓ₀.SOppSide p x := by
        apply exists_cut hne2 e₁_ne_zero (t := m₀)
        · intro p hp
          rw [inner_e₁, (hAmem p hp).2]
        · intro x hx
          rw [Finset.mem_sdiff] at hx
          rw [inner_e₁]
          exact hnotA x hx.1 hx.2
      obtain ⟨ℓ₀, hr₀, havoid₀, hsep₀⟩ := hcut
      refine assemble cfg (Or.inr rfl) hAb ?_ hr₀ havoid₀ hsep₀
      rw [Finset.card_sdiff_of_subset hAb, cfg.blue_card, h2]

/-! ### Lower bound construction -/

/-- The angle of the `j`-th vertex of a regular 4027-gon. -/
noncomputable def ang (j : ℕ) : ℝ := 2 * Real.pi * j / 4027

theorem ang_nonneg (j : ℕ) : 0 ≤ ang j := by
  unfold ang
  positivity

theorem ang_lt_ang {i j : ℕ} (h : i < j) : ang i < ang j := by
  unfold ang
  gcongr

theorem ang_le_ang {i j : ℕ} (h : i ≤ j) : ang i ≤ ang j := by
  rcases h.lt_or_eq with h' | h'
  · exact (ang_lt_ang h').le
  · rw [h']

theorem ang_lt_two_pi {j : ℕ} (h : j < 4027) : ang j < 2 * Real.pi :=
  calc ang j < ang 4027 := ang_lt_ang h
    _ = 2 * Real.pi := by unfold ang; norm_num

/-- The `j`-th vertex of a regular 4027-gon inscribed in the unit circle. -/
noncomputable def pt (j : ℕ) : Pt := !₂[Real.cos (ang j), Real.sin (ang j)]

@[simp] theorem pt_apply0 (j : ℕ) : pt j 0 = Real.cos (ang j) := rfl

@[simp] theorem pt_apply1 (j : ℕ) : pt j 1 = Real.sin (ang j) := rfl

theorem inner_pt_eq (n : Pt) (j : ℕ) :
    ⟪n, pt j⟫ = n 0 * Real.cos (ang j) + n 1 * Real.sin (ang j) := by
  rw [inner_pt, pt_apply0, pt_apply1]

theorem pt_inj {i j : ℕ} (hi : i < 4027) (hj : j < 4027) (h : pt i = pt j) :
    i = j := by
  have h0 : pt i 0 = pt j 0 := by rw [h]
  have h1 : pt i 1 = pt j 1 := by rw [h]
  simp only [pt_apply0] at h0
  simp only [pt_apply1] at h1
  have hcos : Real.cos (ang i - ang j) = 1 := by
    rw [Real.cos_sub, h0, h1]
    linear_combination Real.sin_sq_add_cos_sq (ang j)
  have hlb : -(2 * Real.pi) < ang i - ang j := by
    have ha := ang_nonneg i
    have hb := ang_lt_two_pi hj
    linarith
  have hub : ang i - ang j < 2 * Real.pi := by
    have ha := ang_lt_two_pi hi
    have hb := ang_nonneg j
    linarith
  rw [Real.cos_eq_one_iff_of_lt_of_lt hlb hub] at hcos
  have hang : ang i = ang j := by linarith
  rcases Nat.lt_trichotomy i j with hlt | heq | hgt
  · exact absurd hang (ne_of_lt (ang_lt_ang hlt))
  · exact heq
  · exact absurd hang.symm (ne_of_lt (ang_lt_ang hgt))

theorem dist_pt_zero (j : ℕ) : dist (pt j) (0 : Pt) = 1 := by
  rw [dist_zero_right, norm_eq_sqrt_real_inner]
  rw [show ⟪pt j, pt j⟫ = 1 by
    rw [inner_pt_eq, pt_apply0, pt_apply1]
    linear_combination Real.sin_sq_add_cos_sq (ang j)]
  exact Real.sqrt_one

/-- The red points: vertices with odd indices. -/
noncomputable def redPts : Finset Pt :=
  (Finset.range 2013).image (fun i => pt (2 * i + 1))

/-- The blue points: vertices with even indices. -/
noncomputable def bluePts : Finset Pt :=
  (Finset.range 2014).image (fun i => pt (2 * i))

theorem redPts_card : redPts.card = 2013 := by
  rw [redPts, Finset.card_image_of_injOn, Finset.card_range]
  intro a ha b hb hab
  rw [Finset.coe_range, Set.mem_Iio] at ha hb
  have := pt_inj (by omega) (by omega) hab
  omega

theorem bluePts_card : bluePts.card = 2014 := by
  rw [bluePts, Finset.card_image_of_injOn, Finset.card_range]
  intro a ha b hb hab
  rw [Finset.coe_range, Set.mem_Iio] at ha hb
  have := pt_inj (by omega) (by omega) hab
  omega

theorem red_blue_disjoint : Disjoint redPts bluePts := by
  rw [Finset.disjoint_left]
  intro p hp hq
  rw [redPts, Finset.mem_image] at hp
  rw [bluePts, Finset.mem_image] at hq
  obtain ⟨a, ha, rfl⟩ := hp
  obtain ⟨b, hb, hba⟩ := hq
  rw [Finset.mem_range] at ha hb
  have := pt_inj (by omega) (by omega) hba
  omega

theorem mem_pts {p : Pt} (hp : p ∈ redPts ∪ bluePts) : ∃ j < 4027, p = pt j := by
  rw [Finset.mem_union] at hp
  rcases hp with hp | hp
  · rw [redPts, Finset.mem_image] at hp
    obtain ⟨i, hi, rfl⟩ := hp
    rw [Finset.mem_range] at hi
    exact ⟨2 * i + 1, by omega, rfl⟩
  · rw [bluePts, Finset.mem_image] at hp
    obtain ⟨i, hi, rfl⟩ := hp
    rw [Finset.mem_range] at hi
    exact ⟨2 * i, by omega, rfl⟩

/-- The Colombian configuration witnessing the lower bound: the vertices of a
regular 4027-gon, colored red at odd indices and blue at even indices. -/
noncomputable def lowerCfg : ColombianConfiguration where
  red := redPts
  blue := bluePts
  red_card := redPts_card
  blue_card := bluePts_card
  red_blue_disjoint := red_blue_disjoint
  not_collinear := by
    intro p₁ hp₁ p₂ hp₂ p₃ hp₃ h₁₂ h₁₃ h₂₃ hcol
    have hsph : EuclideanGeometry.Cospherical ({p₁, p₂, p₃} : Set Pt) := by
      refine ⟨0, 1, ?_⟩
      intro p hp
      have hp' : p ∈ redPts ∪ bluePts := by
        rcases hp with rfl | rfl | rfl <;> assumption
      obtain ⟨j, -, rfl⟩ := mem_pts hp'
      exact dist_pt_zero j
    have hai := hsph.affineIndependent_of_ne h₁₂ h₁₃ h₂₃
    rw [affineIndependent_iff_not_collinear_set] at hai
    exact hai hcol

/-- A sinusoid `r ↦ n 0 * cos r + n 1 * sin r` with `n ≠ 0` takes any value at
most twice on an interval shorter than a full period. -/
theorem sinusoid_roots {n : Pt} (hn : n ≠ 0) {c : ℝ} {r₁ r₂ r₃ : ℝ}
    (h₁₂ : r₁ < r₂) (h₂₃ : r₂ < r₃) (hspan : r₃ - r₁ < 2 * Real.pi)
    (e₁ : n 0 * Real.cos r₁ + n 1 * Real.sin r₁ = c)
    (e₂ : n 0 * Real.cos r₂ + n 1 * Real.sin r₂ = c)
    (e₃ : n 0 * Real.cos r₃ + n 1 * Real.sin r₃ = c) : False := by
  have hπ := Real.pi_pos
  -- two roots less than a period apart force the "midpoint functional" to vanish
  have key : ∀ u v : ℝ, u < v → v - u < 2 * Real.pi →
      n 0 * Real.cos u + n 1 * Real.sin u = c →
      n 0 * Real.cos v + n 1 * Real.sin v = c →
      n 1 * Real.cos ((u + v) / 2) - n 0 * Real.sin ((u + v) / 2) = 0 := by
    intro u v huv huv2 hu hv
    have hsin : 0 < Real.sin ((v - u) / 2) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    have hdiff : n 0 * (Real.cos u - Real.cos v) +
        n 1 * (Real.sin u - Real.sin v) = 0 := by linarith
    rw [Real.cos_sub_cos, Real.sin_sub_sin] at hdiff
    have hfac : Real.sin ((u - v) / 2) *
        (2 * (n 1 * Real.cos ((u + v) / 2) - n 0 * Real.sin ((u + v) / 2))) = 0 := by
      linear_combination hdiff
    have hsin' : Real.sin ((u - v) / 2) ≠ 0 := by
      rw [show (u - v) / 2 = -((v - u) / 2) by ring, Real.sin_neg, neg_ne_zero]
      exact ne_of_gt hsin
    have hker := (mul_eq_zero.mp hfac).resolve_left hsin'
    linarith
  have k₁₂ := key r₁ r₂ h₁₂ (by linarith) e₁ e₂
  have k₁₃ := key r₁ r₃ (h₁₂.trans h₂₃) (by linarith) e₁ e₃
  have hm : 0 < Real.sin ((r₁ + r₃) / 2 - (r₁ + r₂) / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  rw [Real.sin_sub] at hm
  have hfne : Real.sin ((r₁ + r₃) / 2) * Real.cos ((r₁ + r₂) / 2) -
      Real.cos ((r₁ + r₃) / 2) * Real.sin ((r₁ + r₂) / 2) ≠ 0 := ne_of_gt hm
  have hn0 : n 0 * (Real.sin ((r₁ + r₃) / 2) * Real.cos ((r₁ + r₂) / 2) -
      Real.cos ((r₁ + r₃) / 2) * Real.sin ((r₁ + r₂) / 2)) = 0 := by
    linear_combination Real.cos ((r₁ + r₃) / 2) * k₁₂ - Real.cos ((r₁ + r₂) / 2) * k₁₃
  have hn1 : n 1 * (Real.sin ((r₁ + r₃) / 2) * Real.cos ((r₁ + r₂) / 2) -
      Real.cos ((r₁ + r₃) / 2) * Real.sin ((r₁ + r₂) / 2)) = 0 := by
    linear_combination Real.sin ((r₁ + r₃) / 2) * k₁₂ - Real.sin ((r₁ + r₂) / 2) * k₁₃
  have h0 : n 0 = 0 := (mul_eq_zero.mp hn0).resolve_right hfne
  have h1 : n 1 = 0 := (mul_eq_zero.mp hn1).resolve_right hfne
  exact hn (Pt.ext (by simpa using h0) (by simpa using h1))

/-- If a line `{x | ⟪n, x⟫ = c}` strictly separates the adjacent vertices
`pt j` and `pt (j+1)`, then the sinusoid `r ↦ ⟪n, (cos r, sin r)⟫` takes the
value `c` somewhere strictly between their angles. -/
theorem exists_root_pair {n : Pt} {c : ℝ} {j : ℕ}
    (h : ⟪n, pt j⟫ < c ∧ c < ⟪n, pt (j + 1)⟫ ∨
         ⟪n, pt (j + 1)⟫ < c ∧ c < ⟪n, pt j⟫) :
    ∃ r ∈ Set.Ioo (ang j) (ang (j + 1)),
      n 0 * Real.cos r + n 1 * Real.sin r = c := by
  have hlt : ang j < ang (j + 1) := ang_lt_ang (Nat.lt_succ_self j)
  have hcont : Continuous (fun t : ℝ => n 0 * Real.cos t + n 1 * Real.sin t) := by
    fun_prop
  rw [inner_pt_eq n j, inner_pt_eq n (j + 1)] at h
  rcases h with h | h
  · exact intermediate_value_Ioo hlt.le hcont.continuousOn h
  · exact intermediate_value_Ioo' hlt.le hcont.continuousOn h

/-- A single line strictly separates at most two of the 4026 adjacent vertex
pairs of the regular 4027-gon. -/
theorem seps_card_le_two {n : Pt} (hn : n ≠ 0) {c : ℝ} {s : Finset ℕ}
    (hs : ∀ j ∈ s, j < 4026)
    (hsep : ∀ j ∈ s, ⟪n, pt j⟫ < c ∧ c < ⟪n, pt (j + 1)⟫ ∨
                     ⟪n, pt (j + 1)⟫ < c ∧ c < ⟪n, pt j⟫) :
    s.card ≤ 2 := by
  by_contra hcard
  push Not at hcard
  obtain ⟨a, ha, b, hb, d, hd, hab, had, hbd⟩ := Finset.two_lt_card.mp hcard
  have key : ∀ x ∈ s, ∀ y ∈ s, ∀ z ∈ s, x < y → y < z → False := by
    intro x hx y hy z hz hxy hyz
    obtain ⟨r₁, hr₁, he₁⟩ := exists_root_pair (hsep x hx)
    obtain ⟨r₂, hr₂, he₂⟩ := exists_root_pair (hsep y hy)
    obtain ⟨r₃, hr₃, he₃⟩ := exists_root_pair (hsep z hz)
    rw [Set.mem_Ioo] at hr₁ hr₂ hr₃
    have h12 : r₁ < r₂ :=
      (hr₁.2.trans_le (ang_le_ang (by omega : x + 1 ≤ y))).trans hr₂.1
    have h23 : r₂ < r₃ :=
      (hr₂.2.trans_le (ang_le_ang (by omega : y + 1 ≤ z))).trans hr₃.1
    have hspan : r₃ - r₁ < 2 * Real.pi := by
      have hz' : z < 4026 := hs z hz
      have h1 : r₃ < ang (z + 1) := hr₃.2
      have h2 : ang (z + 1) < 2 * Real.pi := ang_lt_two_pi (by omega)
      have h3 : 0 ≤ ang x := ang_nonneg x
      have h4 : ang x < r₁ := hr₁.1
      linarith
    exact sinusoid_roots hn h12 h23 hspan he₁ he₂ he₃
  rcases hab.lt_or_gt with h1 | h1 <;> rcases had.lt_or_gt with h2 | h2 <;>
      rcases hbd.lt_or_gt with h3 | h3
  · exact key a ha b hb d hd h1 h3
  · exact key a ha d hd b hb h2 h3
  · omega
  · exact key d hd a ha b hb h2 h1
  · exact key b hb a ha d hd h1 h2
  · omega
  · exact key b hb d hd a ha h3 h2
  · exact key d hd b hb a ha h3 h1

/-- No good arrangement for `lowerCfg` has fewer than 2013 lines: each of the
4026 adjacent opposite-colored vertex pairs must be separated by some line, and
each line separates at most two of them. -/
theorem lower_bound {k : ℕ} (lines : Fin k → AffineSubspace ℝ Pt)
    (h : GoodArrangement lowerCfg lines) : 2013 ≤ k := by
  obtain ⟨hdim, -, hsep⟩ := h
  have hred : ∀ m : ℕ, m < 2013 → pt (2 * m + 1) ∈ lowerCfg.red := by
    intro m hm
    show pt (2 * m + 1) ∈ redPts
    rw [redPts, Finset.mem_image]
    exact ⟨m, Finset.mem_range.mpr hm, rfl⟩
  have hblue : ∀ m : ℕ, m < 2014 → pt (2 * m) ∈ lowerCfg.blue := by
    intro m hm
    show pt (2 * m) ∈ bluePts
    rw [bluePts, Finset.mem_image]
    exact ⟨m, Finset.mem_range.mpr hm, rfl⟩
  have hsep' : ∀ j, j < 4026 →
      ∃ i : Fin k, (lines i).SOppSide (pt j) (pt (j + 1)) := by
    intro j hj
    rcases Nat.even_or_odd j with ⟨m, hm⟩ | ⟨m, hm⟩
    · -- `j` even: `pt j` is blue and `pt (j+1)` is red
      have hjm : j = 2 * m := by omega
      have hj1 : j + 1 = 2 * m + 1 := by omega
      obtain ⟨i, hi⟩ := hsep (pt (j + 1)) (by rw [hj1]; exact hred m (by omega))
        (pt j) (by rw [hjm]; exact hblue m (by omega))
      exact ⟨i, hi.symm⟩
    · -- `j` odd: `pt j` is red and `pt (j+1)` is blue
      have hj1 : j + 1 = 2 * (m + 1) := by omega
      obtain ⟨i, hi⟩ := hsep (pt j) (by rw [hm]; exact hred m (by omega))
        (pt (j + 1)) (by rw [hj1]; exact hblue (m + 1) (by omega))
      exact ⟨i, hi⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · obtain ⟨i, -⟩ := hsep' 0 (by norm_num)
    exact i.elim0
  have hchoice : ∀ j : ℕ, ∃ i : Fin k,
      j < 4026 → (lines i).SOppSide (pt j) (pt (j + 1)) := by
    intro j
    by_cases hj : j < 4026
    · obtain ⟨i, hi⟩ := hsep' j hj
      exact ⟨i, fun _ => hi⟩
    · exact ⟨⟨0, hk⟩, fun h' => absurd h' hj⟩
  choose F hF using hchoice
  have hcard : (Finset.range 4026).card =
      ∑ i : Fin k, ((Finset.range 4026).filter fun j => F j = i).card :=
    Finset.card_eq_sum_card_fiberwise fun j _ => Finset.mem_univ (F j)
  rw [Finset.card_range] at hcard
  have hbound : ∀ i : Fin k,
      ((Finset.range 4026).filter fun j => F j = i).card ≤ 2 := by
    intro i
    obtain ⟨n, c, hn, hmem⟩ := exists_normal (hdim i)
    apply seps_card_le_two hn (c := c)
    · intro j hj
      rw [Finset.mem_filter, Finset.mem_range] at hj
      exact hj.1
    · intro j hj
      rw [Finset.mem_filter, Finset.mem_range] at hj
      rw [← sOppSide_iff hmem]
      have hsop := hF j hj.1
      rw [hj.2] at hsop
      exact hsop
  have hsum : ∑ i : Fin k, ((Finset.range 4026).filter fun j => F j = i).card ≤
      ∑ _i : Fin k, 2 := Finset.sum_le_sum fun i _ => hbound i
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
  rw [← hcard] at hsum
  omega

snip end

determine solution_value : ℕ := 2013

problem imo2013_p2 :
    IsLeast {k | ∀ cfg : ColombianConfiguration,
                 ∃ lines : Fin k → AffineSubspace ℝ Pt, GoodArrangement cfg lines}
            solution_value := by
  constructor
  · intro cfg
    exact upper_bound cfg
  · intro k hk
    obtain ⟨lines, hlines⟩ := hk lowerCfg
    exact lower_bound lines hlines

end Imo2013P2
