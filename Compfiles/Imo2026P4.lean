/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import ProblemExtraction

@[expose] public section

problem_file {
  tags := [.Combinatorics]
  problemImportedFrom :=
    "https://github.com/humanfia/imo2026"
}

/-!
# International Mathematical Olympiad 2026, Problem 4

Shan-Yu and Mulan are playing a game. Let θ be an angle with 0° < θ < 180°
known to both players. Initially, Shan-Yu makes a paper triangle T with
measurements of his choice. Then, they repeatedly perform the following steps:

* If T has at least one angle measuring exactly θ, then the game stops and
  Mulan wins.
* Otherwise, Mulan chooses a point P on the perimeter of T, different from its
  three vertices. She then makes a straight cut from P to the opposite vertex
  of T, splitting it into two triangles.
* Shan-Yu discards one of the two triangles. The remaining triangle becomes
  the new T.

For which real values of θ can Mulan guarantee her victory in finitely many
steps, no matter how Shan-Yu plays?

Statement formalization adapted from AxiomMath/IMO2026; proof adapted from
Humanfia's Kimi-K3 solutions (https://github.com/humanfia/imo2026).
-/

namespace Imo2026P4

set_option backward.isDefEq.respectTransparency false

/-- A triangle, viewed as the multiset of its three interior angles (in degrees):
positive reals summing to `180`. -/
def IsTriangle (s : Multiset ℝ) : Prop :=
  s.card = 3 ∧ (∀ x ∈ s, 0 < x) ∧ s.sum = 180

/-- A triangle `s` has an interior angle equal to `θ`. -/
def HasAngle (θ : ℝ) (s : Multiset ℝ) : Prop := θ ∈ s

/-- One admissible cut of the triangle `s`, producing children `L` and `R`.

We pick an apex angle `α` and the two base angles `β, γ` (so `s = {α, β, γ}`), and a
cut parameter `x` in the open interval `(γ, 180 - β)`. The resulting two triangles
have angle multisets `L = {β, x, 180 - β - x}` and `R = {γ, 180 - x, x - γ}`.
Ranging over all `α, β, γ` with `s = {α, β, γ}` captures all three apex choices and
both assignments of the two base angles. -/
def IsCut (s L R : Multiset ℝ) : Prop :=
  ∃ α β γ x : ℝ,
    s = {α, β, γ} ∧ γ < x ∧ x < 180 - β ∧
      L = {β, x, 180 - β - x} ∧ R = {γ, 180 - x, x - γ}

/-- The set of triangles from which Mulan can force, in finitely many steps, a
triangle with an interior angle equal to `θ`, no matter how Shan-Yu discards.

This is the least predicate closed under:
* (`win`) if the current triangle already has an angle equal to `θ`, Mulan has won;
* (`move`) if Mulan can make a cut producing children `L` and `R` from *both* of
  which she wins (so whichever one Shan-Yu keeps, she still wins), then she wins
  from the current triangle.

Membership means Mulan wins in finitely many steps. -/
inductive MulanWins (θ : ℝ) : Multiset ℝ → Prop
  | win {s : Multiset ℝ} (h : HasAngle θ s) : MulanWins θ s
  | move {s L R : Multiset ℝ} (hcut : IsCut s L R)
      (hL : MulanWins θ L) (hR : MulanWins θ R) : MulanWins θ s

/-- Mulan can guarantee victory for the value `θ`: from every valid starting
triangle she wins in finitely many steps regardless of Shan-Yu's play. -/
def MulanCanGuarantee (θ : ℝ) : Prop :=
  ∀ s : Multiset ℝ, IsTriangle s → MulanWins θ s

snip begin

/-- Membership in a triple, as a disjunction. -/
lemma mem3 (x a b c : ℝ) : x ∈ ({a, b, c} : Multiset ℝ) ↔ x = a ∨ x = b ∨ x = c := by
  simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton]

/-- Rotation of a triple. -/
lemma rot3 (a b c : ℝ) : ({a, b, c} : Multiset ℝ) = {b, c, a} := by
  simp only [Multiset.insert_eq_cons]
  rw [Multiset.cons_swap a b, ← Multiset.insert_eq_cons a {c}, Multiset.pair_comm a c,
    Multiset.insert_eq_cons c {a}]

/-- Sum of a triple. -/
lemma triple_sum (a b c : ℝ) : ({a, b, c} : Multiset ℝ).sum = a + b + c := by
  simp only [Multiset.insert_eq_cons, Multiset.sum_cons, Multiset.sum_singleton]
  ring

/-- Card of a triple. -/
lemma triple_card (a b c : ℝ) : ({a, b, c} : Multiset ℝ).card = 3 :=
  Multiset.card_eq_three.mpr ⟨a, b, c, rfl⟩

/-- An open interval of length exceeding `θ`, with positive left endpoint,
contains a positive integer multiple of `θ`. -/
lemma exists_nat_mul_in (θ : ℝ) (hθ0 : 0 < θ) (u v : ℝ) (hu : 0 < u)
    (huv : u + θ < v) :
    ∃ m : ℕ, 1 ≤ m ∧ u < (m : ℝ) * θ ∧ (m : ℝ) * θ < v := by
  have h1 : u < ((⌊u / θ⌋ + 1 : ℤ) : ℝ) * θ := by
    have h2 : u / θ < ((⌊u / θ⌋ + 1 : ℤ) : ℝ) := by
      push_cast
      exact Int.lt_floor_add_one _
    exact (div_lt_iff₀ hθ0).mp h2
  have h4 : ((⌊u / θ⌋ + 1 : ℤ) : ℝ) * θ ≤ u + θ := by
    have h5 : ((⌊u / θ⌋ : ℤ) : ℝ) ≤ u / θ := Int.floor_le _
    have h6 : ((⌊u / θ⌋ : ℤ) : ℝ) * θ ≤ u := (le_div_iff₀ hθ0).mp h5
    have h7 : ((⌊u / θ⌋ + 1 : ℤ) : ℝ) * θ = ((⌊u / θ⌋ : ℤ) : ℝ) * θ + θ := by
      push_cast
      ring
    rw [h7]
    linarith
  have h8 : (1 : ℤ) ≤ ⌊u / θ⌋ + 1 := by
    by_contra h9
    push Not at h9
    have h10 : ((⌊u / θ⌋ + 1 : ℤ) : ℝ) ≤ 0 := by
      exact_mod_cast (by omega : ⌊u / θ⌋ + 1 ≤ 0)
    have h11 : ((⌊u / θ⌋ + 1 : ℤ) : ℝ) * θ ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg h10 (le_of_lt hθ0)
    linarith
  have hcast : ((⌊u / θ⌋ + 1).toNat : ℝ) = ((⌊u / θ⌋ + 1 : ℤ) : ℝ) := by
    have h12 : ((⌊u / θ⌋ + 1).toNat : ℤ) = ⌊u / θ⌋ + 1 :=
      Int.toNat_of_nonneg (by omega)
    exact_mod_cast h12
  refine ⟨(⌊u / θ⌋ + 1).toNat, ?_, ?_, ?_⟩
  · have h12 : ((⌊u / θ⌋ + 1).toNat : ℤ) = ⌊u / θ⌋ + 1 :=
      Int.toNat_of_nonneg (by omega)
    omega
  · rw [hcast]
    exact h1
  · rw [hcast]
    linarith

/-- A triangle (with sum 180 and positive angles) containing a positive integer
multiple `k * θ` of `θ` is winning for Mulan, by induction on `k`:
if `k ≥ 2`, transfer one `θ` from the apex `k * θ` to the angle `C`; the child
`{C, 180 - C - θ, θ}` already contains `θ`, and the other child contains
`(k - 1) * θ`. -/
lemma good_wins (θ : ℝ) (hθ0 : 0 < θ) : ∀ k : ℕ, 1 ≤ k → ∀ s : Multiset ℝ,
    (k : ℝ) * θ ∈ s → s.card = 3 → (∀ y ∈ s, 0 < y) → s.sum = 180 →
    MulanWins θ s := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    intro s hmem hcard hpos hsum
    simp only [Nat.cast_one, one_mul] at hmem
    exact MulanWins.win hmem
  | succ k hk ih =>
    intro s hmem hcard hpos hsum
    obtain ⟨t, ht⟩ := Multiset.exists_cons_of_mem hmem
    have hcardt : t.card = 2 := by
      have h1 : s.card = t.card + 1 := by rw [ht, Multiset.card_cons]
      omega
    obtain ⟨B, C, htBC⟩ := Multiset.card_eq_two.mp hcardt
    have hs' : s = {((k + 1 : ℕ) : ℝ) * θ, B, C} := by
      rw [ht, htBC]
      simp only [Multiset.insert_eq_cons]
    have hA' : ((k + 1 : ℕ) : ℝ) * θ = (k : ℝ) * θ + θ := by
      push_cast
      ring
    have hB : 0 < B := hpos B (by rw [hs', mem3]; exact Or.inr (Or.inl rfl))
    have hC : 0 < C := hpos C (by rw [hs', mem3]; exact Or.inr (Or.inr rfl))
    have hsum' : ((k + 1 : ℕ) : ℝ) * θ + B + C = 180 := by
      rw [hs', triple_sum] at hsum
      exact hsum
    have hkθ : (0 : ℝ) < (k : ℝ) * θ := by
      have h1 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
      positivity
    have hx1 : C < C + θ := by linarith
    have hx2 : C + θ < 180 - B := by linarith
    have h3 : 180 - B - (C + θ) = (k : ℝ) * θ := by linarith
    have hL : MulanWins θ {B, C + θ, 180 - B - (C + θ)} := by
      refine ih _ ?_ (triple_card _ _ _) ?_ ?_
      · rw [h3, mem3]
        exact Or.inr (Or.inr rfl)
      · intro y hy
        rw [mem3] at hy
        rcases hy with rfl | rfl | rfl
        · exact hB
        · linarith
        · rw [h3]
          exact hkθ
      · rw [triple_sum]
        ring
    have hR : MulanWins θ {C, 180 - (C + θ), (C + θ) - C} := by
      apply MulanWins.win
      show θ ∈ {C, 180 - (C + θ), (C + θ) - C}
      rw [(show (C + θ) - C = θ by ring), mem3]
      exact Or.inr (Or.inr rfl)
    exact MulanWins.move (L := {B, C + θ, 180 - B - (C + θ)})
      (R := {C, 180 - (C + θ), (C + θ) - C})
      ⟨((k + 1 : ℕ) : ℝ) * θ, B, C, C + θ, hs', hx1, hx2, rfl, rfl⟩ hL hR

/-- If `n * θ = 180` with `2 ≤ n` and the triangle `{a, b, c}` has no angle equal
to a positive integer multiple of `θ`, then some relabeling `{A, B, C}` of it
and some `1 ≤ m` satisfy `C < m * θ < 180 - B`. -/
lemma find_cut (θ : ℝ) (hθ0 : 0 < θ) : ∀ n : ℕ, 2 ≤ n → (n : ℝ) * θ = 180 →
    ∀ a b c : ℝ, 0 < a → 0 < b → 0 < c → a + b + c = 180 →
    (¬∃ k : ℕ, 1 ≤ k ∧ (a = (k : ℝ) * θ ∨ b = (k : ℝ) * θ ∨ c = (k : ℝ) * θ)) →
    ∃ A B C : ℝ, ∃ m : ℕ, ({a, b, c} : Multiset ℝ) = {A, B, C} ∧ 1 ≤ m ∧
      C < (m : ℝ) * θ ∧ (m : ℝ) * θ < 180 - B := by
  intro n hn2 hnθ a b c ha hb hc hsum hmul
  by_cases haθ : θ < a
  · obtain ⟨m, hm1, hmgt, hmlt⟩ := exists_nat_mul_in θ hθ0 c (180 - b) hc (by linarith)
    exact ⟨a, b, c, m, rfl, hm1, hmgt, hmlt⟩
  · by_cases hbθ : θ < b
    · obtain ⟨m, hm1, hmgt, hmlt⟩ := exists_nat_mul_in θ hθ0 a (180 - c) ha (by linarith)
      exact ⟨b, c, a, m, rot3 a b c, hm1, hmgt, hmlt⟩
    · by_cases hcθ : θ < c
      · obtain ⟨m, hm1, hmgt, hmlt⟩ := exists_nat_mul_in θ hθ0 b (180 - a) hb (by linarith)
        exact ⟨c, a, b, m, (rot3 a b c).trans (rot3 b c a), hm1, hmgt, hmlt⟩
      · push Not at haθ hbθ hcθ
        have ha' : a < θ := lt_of_le_of_ne haθ (by
          intro h
          exact hmul ⟨1, le_refl 1, Or.inl (by rw [h]; simp)⟩)
        have hb' : b < θ := lt_of_le_of_ne hbθ (by
          intro h
          exact hmul ⟨1, le_refl 1, Or.inr (Or.inl (by rw [h]; simp))⟩)
        have hc' : c < θ := lt_of_le_of_ne hcθ (by
          intro h
          exact hmul ⟨1, le_refl 1, Or.inr (Or.inr (by rw [h]; simp))⟩)
        have hn3 : n ≤ 3 := by
          have h1 : (n : ℝ) * θ ≤ 3 * θ := by
            rw [hnθ]
            linarith
          have h2 : (n : ℝ) ≤ 3 := le_of_mul_le_mul_right h1 hθ0
          exact_mod_cast h2
        have hnne3 : n ≠ 3 := by
          intro h3
          have h3180 : 3 * θ = 180 := by
            rw [h3] at hnθ
            push_cast at hnθ
            linarith
          have ha_eq : a = θ := by linarith
          exact hmul ⟨1, le_refl 1, Or.inl (by rw [ha_eq]; simp)⟩
        have hn2' : n = 2 := by omega
        have h2θ : 2 * θ = 180 := by
          rw [hn2'] at hnθ
          push_cast at hnθ
          linarith
        exact ⟨a, b, c, 1, rfl, le_refl 1, by simpa using hc', by
          simp only [Nat.cast_one, one_mul]
          linarith⟩

/-- Shan-Yu's invariant: assuming `180` is not an integer multiple of `θ`, for any
cut of a sum-`180` multiset with no angle an integer multiple of `θ`, at least
one child keeps the same property. -/
lemma invariant (θ : ℝ) : (∀ m : ℤ, (180 : ℝ) ≠ (m : ℝ) * θ) →
    ∀ {s L R : Multiset ℝ}, s.sum = 180 →
    (∀ y ∈ s, ∀ k : ℤ, y ≠ (k : ℝ) * θ) → IsCut s L R →
    (L.sum = 180 ∧ ∀ y ∈ L, ∀ k : ℤ, y ≠ (k : ℝ) * θ) ∨
    (R.sum = 180 ∧ ∀ y ∈ R, ∀ k : ℤ, y ≠ (k : ℝ) * θ) := by
  intro h180 s L R hs hP hcut
  obtain ⟨α, β, γ, x, hs', hγx, hxβ, hL, hR⟩ := hcut
  subst hs'
  subst hL
  subst hR
  have hsumα : α + β + γ = 180 := by
    rw [triple_sum] at hs
    exact hs
  have hα : ∀ k : ℤ, α ≠ (k : ℝ) * θ := hP α (by rw [mem3]; exact Or.inl rfl)
  have hβ : ∀ k : ℤ, β ≠ (k : ℝ) * θ := hP β (by rw [mem3]; exact Or.inr (Or.inl rfl))
  have hγ : ∀ k : ℤ, γ ≠ (k : ℝ) * θ := hP γ (by rw [mem3]; exact Or.inr (Or.inr rfl))
  have hsumL : ({β, x, 180 - β - x} : Multiset ℝ).sum = 180 := by
    rw [triple_sum]
    ring
  have hsumR : ({γ, 180 - x, x - γ} : Multiset ℝ).sum = 180 := by
    rw [triple_sum]
    ring
  by_contra H
  push Not at H
  obtain ⟨yL, hyL, kL, hkL⟩ := H.1 hsumL
  obtain ⟨yR, hyR, kR, hkR⟩ := H.2 hsumR
  rw [mem3] at hyL hyR
  have hcast2 : ∀ k l : ℤ, ((k + l : ℤ) : ℝ) * θ = (k : ℝ) * θ + (l : ℝ) * θ := by
    intro k l
    push_cast
    ring
  have hcast3 : ∀ k l : ℤ, ((k - l : ℤ) : ℝ) * θ = (k : ℝ) * θ - (l : ℝ) * θ := by
    intro k l
    push_cast
    ring
  rcases hyL with rfl | rfl | rfl
  · exact hβ kL hkL
  · rcases hyR with rfl | rfl | rfl
    · exact hγ kR hkR
    · exact h180 (kL + kR) (by rw [hcast2]; linarith)
    · exact hγ (kL - kR) (by rw [hcast3]; linarith)
  · rcases hyR with rfl | rfl | rfl
    · exact hγ kR hkR
    · exact hβ (kR - kL) (by rw [hcast3]; linarith)
    · exact hα (kL + kR) (by rw [hcast2]; linarith)

/-- Hence no sum-`180` multiset without integer multiples of `θ` is winning. -/
lemma not_wins (θ : ℝ) : (∀ m : ℤ, (180 : ℝ) ≠ (m : ℝ) * θ) → ∀ s : Multiset ℝ,
    MulanWins θ s → s.sum = 180 → (∀ y ∈ s, ∀ k : ℤ, y ≠ (k : ℝ) * θ) → False := by
  intro h180 s h
  induction h with
  | win hw =>
    intro hs hP
    exact hP θ hw 1 (by simp)
  | move hcut hL hR ihL ihR =>
    intro hs hP
    rcases invariant θ h180 hs hP hcut with ⟨hsumL, hPL⟩ | ⟨hsumR, hPR⟩
    · exact ihL hsumL hPL
    · exact ihR hsumR hPR

snip end

determine answer : Set ℝ := {θ : ℝ | ∃ n : ℕ, 2 ≤ n ∧ θ = 180 / n}

/-- **Main theorem.** For `0 < θ < 180`, Mulan can guarantee her victory in finitely
many steps, no matter how Shan-Yu plays, if and only if `θ = 180 / n` for some
integer `n ≥ 2`. -/
problem imo2026_p4 (θ : ℝ) (hθ0 : 0 < θ) (hθ180 : θ < 180) :
    MulanCanGuarantee θ ↔ θ ∈ answer := by
  classical
  change MulanCanGuarantee θ ↔ ∃ n : ℕ, 2 ≤ n ∧ θ = 180 / n
  constructor
  · -- (⇒) If Mulan can guarantee victory, then `θ = 180 / n` for some `n ≥ 2`.
    intro hG
    by_contra hθ
    push Not at hθ
    -- `180` is not an integer multiple of `θ`.
    have h180 : ∀ m : ℤ, (180 : ℝ) ≠ (m : ℝ) * θ := by
      intro m hm
      have hm1 : 1 ≤ m := by
        by_contra h
        push Not at h
        have h1 : ((m : ℤ) : ℝ) ≤ 0 := by exact_mod_cast (by omega : m ≤ 0)
        have h2 : ((m : ℤ) : ℝ) * θ ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg h1 (le_of_lt hθ0)
        linarith
      have hm2 : 2 ≤ m := by
        by_contra h
        push Not at h
        have h1 : m = 1 := by omega
        subst h1
        simp only [Int.cast_one, one_mul] at hm
        linarith
      have hmn : ((m.toNat : ℕ) : ℝ) = ((m : ℤ) : ℝ) := by
        have h2 : ((m.toNat : ℕ) : ℤ) = m := Int.toNat_of_nonneg (by omega)
        exact_mod_cast h2
      have hm2n : 2 ≤ m.toNat := by
        have h2 : ((m.toNat : ℕ) : ℤ) = m := Int.toNat_of_nonneg (by omega)
        omega
      have hne : ((m.toNat : ℕ) : ℝ) ≠ 0 := by
        rw [hmn]
        have h3 : (0 : ℝ) < ((m : ℤ) : ℝ) := by exact_mod_cast (by omega : 0 < m)
        exact ne_of_gt h3
      exact hθ m.toNat hm2n ((eq_div_iff hne).mpr (by rw [hmn, mul_comm]; exact hm.symm))
    -- The equilateral triangle is a valid starting triangle.
    have hsum60 : ({60, 60, 60} : Multiset ℝ).sum = 180 := by
      rw [triple_sum]
      norm_num
    have htri : IsTriangle ({60, 60, 60} : Multiset ℝ) := by
      refine ⟨triple_card _ _ _, ?_, hsum60⟩
      intro y hy
      have hy60 : y = 60 := by
        rw [mem3] at hy
        rcases hy with h | h | h <;> exact h
      rw [hy60]
      norm_num
    -- No angle of the equilateral triangle is an integer multiple of `θ`.
    have hP60 : ∀ y ∈ ({60, 60, 60} : Multiset ℝ), ∀ k : ℤ, y ≠ (k : ℝ) * θ := by
      intro y hy k hky
      have hy60 : y = 60 := by
        rw [mem3] at hy
        rcases hy with h | h | h <;> exact h
      subst hy60
      have hk1 : 1 ≤ k := by
        by_contra h
        push Not at h
        have h1 : ((k : ℤ) : ℝ) ≤ 0 := by exact_mod_cast (by omega : k ≤ 0)
        have h2 : ((k : ℤ) : ℝ) * θ ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg h1 (le_of_lt hθ0)
        linarith
      have hkn : ((3 * k.toNat : ℕ) : ℝ) = 3 * ((k : ℤ) : ℝ) := by
        have h2 : ((k.toNat : ℕ) : ℤ) = k := Int.toNat_of_nonneg (by omega)
        have h3 : ((k.toNat : ℕ) : ℝ) = ((k : ℤ) : ℝ) := by exact_mod_cast h2
        push_cast
        rw [h3]
      have h2n : 2 ≤ 3 * k.toNat := by
        have h2 : ((k.toNat : ℕ) : ℤ) = k := Int.toNat_of_nonneg (by omega)
        omega
      have hne : ((3 * k.toNat : ℕ) : ℝ) ≠ 0 := by
        rw [hkn]
        have h3 : (0 : ℝ) < ((k : ℤ) : ℝ) := by exact_mod_cast (by omega : 0 < k)
        exact ne_of_gt (mul_pos (by norm_num) h3)
      exact hθ (3 * k.toNat) h2n ((eq_div_iff hne).mpr (by
        rw [hkn, show θ * (3 * ((k : ℤ) : ℝ)) = 3 * (((k : ℤ) : ℝ) * θ) by ring, ← hky]
        norm_num))
    exact not_wins θ h180 _ (hG _ htri) hsum60 hP60
  · -- (⇐) If `θ = 180 / n` with `n ≥ 2`, Mulan wins from every starting triangle.
    rintro ⟨n, hn2, hθn⟩
    intro s hs
    obtain ⟨hcard, hpos, hsum⟩ := hs
    obtain ⟨a, b, c, rfl⟩ := Multiset.card_eq_three.mp hcard
    have ha : 0 < a := hpos a (by rw [mem3]; exact Or.inl rfl)
    have hb : 0 < b := hpos b (by rw [mem3]; exact Or.inr (Or.inl rfl))
    have hc : 0 < c := hpos c (by rw [mem3]; exact Or.inr (Or.inr rfl))
    have hsum3 : a + b + c = 180 := by
      rw [triple_sum] at hsum
      exact hsum
    have hn0 : (n : ℝ) ≠ 0 := by
      have h1 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
      exact ne_of_gt h1
    have hnθ : (n : ℝ) * θ = 180 := by
      rw [hθn]
      exact mul_div_cancel₀ _ hn0
    by_cases hmul : ∃ k : ℕ, 1 ≤ k ∧ (a = (k : ℝ) * θ ∨ b = (k : ℝ) * θ ∨ c = (k : ℝ) * θ)
    · -- Some angle is already a positive integer multiple of `θ`.
      obtain ⟨k, hk1, h | h | h⟩ := hmul
      · exact good_wins θ hθ0 k hk1 _ (by rw [mem3]; exact Or.inl h.symm) hcard hpos hsum
      · exact good_wins θ hθ0 k hk1 _ (by rw [mem3]; exact Or.inr (Or.inl h.symm))
          hcard hpos hsum
      · exact good_wins θ hθ0 k hk1 _ (by rw [mem3]; exact Or.inr (Or.inr h.symm))
          hcard hpos hsum
    · -- Otherwise one cut with `x = m * θ` makes both children contain a positive
      -- integer multiple of `θ` (namely `m * θ` and `(n - m) * θ`).
      obtain ⟨A, B, C, m, hsABC, hm1, hmC, hmB⟩ :=
        find_cut θ hθ0 n hn2 hnθ a b c ha hb hc hsum3 hmul
      have hB0 : 0 < B := hpos B (by rw [hsABC, mem3]; exact Or.inr (Or.inl rfl))
      have hC0 : 0 < C := hpos C (by rw [hsABC, mem3]; exact Or.inr (Or.inr rfl))
      have hmθ : (0 : ℝ) < (m : ℝ) * θ := by
        have h1 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
        positivity
      have hmn : m ≤ n - 1 := by
        have h1 : (m : ℝ) * θ < (n : ℝ) * θ := by linarith
        have h2 : (m : ℝ) < (n : ℝ) := lt_of_mul_lt_mul_right h1 (le_of_lt hθ0)
        have h3 : m < n := by exact_mod_cast h2
        omega
      have hnm : (((n - m : ℕ)) : ℝ) * θ = 180 - (m : ℝ) * θ := by
        rw [Nat.cast_sub (by omega : m ≤ n), sub_mul, hnθ]
      refine MulanWins.move (L := {B, (m : ℝ) * θ, 180 - B - (m : ℝ) * θ})
        (R := {C, 180 - (m : ℝ) * θ, (m : ℝ) * θ - C})
        ⟨A, B, C, (m : ℝ) * θ, hsABC, hmC, hmB, rfl, rfl⟩ ?_ ?_
      · refine good_wins θ hθ0 m hm1 _ ?_ (triple_card _ _ _) ?_ ?_
        · rw [mem3]
          exact Or.inr (Or.inl rfl)
        · intro y hy
          rw [mem3] at hy
          rcases hy with rfl | rfl | rfl
          · exact hB0
          · exact hmθ
          · linarith
        · rw [triple_sum]
          ring
      · refine good_wins θ hθ0 (n - m) (by omega) _ ?_ (triple_card _ _ _) ?_ ?_
        · rw [hnm, mem3]
          exact Or.inr (Or.inl rfl)
        · intro y hy
          rw [mem3] at hy
          rcases hy with rfl | rfl | rfl
          · exact hC0
          · linarith
          · linarith
        · rw [triple_sum]
          ring

end Imo2026P4
