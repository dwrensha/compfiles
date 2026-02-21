/-
Copyright (c) 2026 lean-tom. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-tom (with assistance from Gemini)
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic
import ProblemExtraction

problem_file {
  tags := [.Combinatorics]
}

/-!
# International Mathematical Olympiad 1999, Problem 3

Consider an `n × n` square board, where `n` is a fixed even positive integer.
The board is divided into `n^2` unit squares. We say that two different squares on the
board are adjacent if they have a common side.
`N` unit squares on the board are marked in such a way that every square (marked
or unmarked) on the board is adjacent to at least one marked square.
Determine the smallest possible value of `N`.
-/

namespace Imo1999P3

-- 1. Basic Definitions (Visible in Problem Statement)

abbrev Square (n : ℕ) := Fin n × Fin n

/-- Definition of adjacency: Two squares are adjacent if they share a common side. -/
def Adjacent {n : ℕ} (p1 p2 : Square n) : Prop :=
  let (r1, c1) := p1; let (r2, c2) := p2
  ((r1 : ℤ) - r2).natAbs + ((c1 : ℤ) - c2).natAbs = 1

/-- A set s is a valid marking if every square in the grid is adjacent to some square in s. -/
def IsValidMarking {n : ℕ} (s : Finset (Square n)) : Prop :=
  ∀ p : Square n, ∃ m ∈ s, Adjacent p m

snip begin

-- 2. Construction Definitions (Hidden implementation details)

open Finset Classical

/-- Helper predicate for the internal logic of the construction.
    We divide the grid based on parity and modulo 4 conditions. -/
def isSw (n : ℕ) (x y : ℕ) : Prop :=
  -- sw_lower: x, y even, x+y is divisible by 4, x+y < n
  (x % 2 = 0 ∧ y % 2 = 0 ∧ (x + y) % 4 = 0 ∧ x + y < n) ∨
  -- sw_upper: x, y odd, x+y is divisible by 4, x+y ≧ n (including the boundary)
  (x % 2 = 1 ∧ y % 2 = 1 ∧ (x + y) % 4 = 0 ∧ n ≤ x + y)

/-- The set "sw" (Marked squares with even coordinate sum). -/
noncomputable def sw (n : ℕ) : Finset (Square n) :=
  univ.filter (λ p => isSw n p.1 p.2)

/-- The set "sb" (Marked squares with odd coordinate sum, symmetric to sw). -/
noncomputable def sb (n : ℕ) : Finset (Square n) :=
  univ.filter (λ p => isSw n (n - 1 - p.1) p.2)

/-- The definition of the solution set based on the construction logic.
    Defined as the union of sw and sb. -/
noncomputable def solutionSet (n : ℕ) : Finset (Square n) :=
  sw n ∪ sb n

/-- Set of all squares where the sum of coordinates is even. -/
noncomputable def squaresEvenSum (n : ℕ) : Finset (Square n) :=
  univ.filter (λ p => (p.1.val + p.2.val) % 2 = 0)

/-- Set of all squares where the sum of coordinates is odd. -/
noncomputable def squaresOddSum (n : ℕ) : Finset (Square n) :=
  univ.filter (λ p => (p.1.val + p.2.val) % 2 = 1)


-- 3. Construction Lemmas

/--
The transformation used to map the set `sw` to a triangular region in `Fin k × Fin k`.
-/
def transform (n k : ℕ) (h_n : n = 2 * k) (p : Square n) : Fin k × Fin k :=
  let x := p.1.val; let y := p.2.val
  if _ : x % 2 = 0 then
    -- Lower part map
    let u : Fin k := ⟨x / 2, by omega⟩; let v : Fin k := ⟨y / 2, by omega⟩
    (u, v)
  else
    -- Upper part map
    let u : Fin k := ⟨k - 1 - x / 2, by omega⟩; let v : Fin k := ⟨k - 1 - y / 2, by omega⟩
    (u, v)

/-- Helper lemma for triangular number summation. -/
lemma sum_range_sub_eq_triangular (k : ℕ) : ∑ i ∈ range k, (k - i) = k * (k + 1) / 2 := by
  induction k with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ']; simp only [Nat.succ_sub_succ_eq_sub, Nat.sub_zero]; rw [ih]
    apply Nat.eq_div_of_mul_eq_left (by decide)
    rw [Nat.add_mul]
    have h_dvd : 2 ∣ m * (m + 1) :=
      Nat.dvd_of_mod_eq_zero (Nat.even_iff.mp (Nat.even_mul_succ_self m))
    rw [Nat.div_mul_cancel h_dvd]
    ring

/--
Lemma: The transformation is injective on the set sw.
-/
lemma transform_inj_on_sw (n k : ℕ) (h_n : n = 2 * k) :
  ∀ a ∈ sw n, ∀ b ∈ sw n, transform n k h_n a = transform n k h_n b → a = b := by
  intro a ha b hb h_eq

  -- Preparation: expand definitions
  unfold sw at ha hb; rw [mem_filter] at ha hb ; unfold isSw at hb; simp only [transform] at h_eq

  -- Split cases and simplify common goals immediately
  split_ifs at h_eq <;>
    simp only [Prod.mk.injEq] at h_eq <;>
    rcases h_eq with ⟨h_u, h_v⟩ <;>
    apply Fin.mk.inj at h_u <;> apply Fin.mk.inj at h_v
  -- Case 1: Both in Lower
  · ext
    · omega
    · have : a.2.val % 2 = 0 := by rcases ha.2 with h | h <;> omega
      omega
  -- Case 2: a in Lower, b in Upper -> Parity contradiction
  · exfalso
    have : (a.1.val / 2 + a.2.val / 2) % 2 = 0 := by
      rcases ha.2 with h | h <;> omega
    omega
  -- Case 3: a in Upper, b in Lower -> Parity contradiction
  · exfalso
    have : ((k - 1 - a.2.val / 2) + (k - 1 - a.1.val / 2)) % 2 = 1 := by
      rcases ha.2 with h | h <;> omega
    omega
  -- Case 4: Both in Upper
  · have : a.1.val % 2 = 1 ∧ a.2.val % 2 = 1 := by
      rcases ha.2 with h | h
      · have := h.1; contradiction
      · exact ⟨h.1, h.2.1⟩
    ext <;> omega

/--
Lemma: The transformation maps sw onto t (Surjectivity).
For every point p in the triangular set t, there exists a pre-image in sw.
-/
lemma transform_surjective_on_t (n k : ℕ) (h_n : n = 2 * k) :
  let t : Finset (Fin k × Fin k) := univ.filter (λ p => p.1.val + p.2.val < k)
  ∀ x ∈ t, ∃ p ∈ sw n, transform n k h_n p = x := by
  intro t x hx
  rw [mem_filter] at hx

  let u := x.1.val; let v := x.2.val

  -- Inverse construction logic
  if _ : (u + v) % 2 = 0 then
    -- Inverse to Lower
    let p : Square n := (⟨2 * u ,by omega⟩, ⟨2 * v , by omega⟩)
    use p
    constructor
    · -- p ∈ sw
      unfold sw; rw [mem_filter]; simp only [Finset.mem_univ, true_and]; unfold isSw
      left; simp only [p]; refine ⟨?_, ?_, ?_, ?_⟩ <;> omega
    · -- transform p = x
      simp only [transform, p]
      split_ifs with h_p_even
      · ext <;> dsimp <;> omega
      · omega
  else
    -- Inverse to Upper
    let p : Square n := (⟨2 * (k - 1 - u) + 1, by omega⟩, ⟨2 * (k - 1 - v) + 1, by omega⟩)
    use p
    constructor
    · -- p ∈ sw
      unfold sw; rw [mem_filter]; simp only [Finset.mem_univ, true_and]; unfold isSw
      right; simp only [p]; rw [h_n]; refine ⟨?_, ?_, ?_, ?_⟩ <;> omega
    · -- transform p = x
      simp only [transform, p]
      split_ifs with h_p_even
      · omega
      · ext <;> dsimp <;> omega

/-- Calculate the cardinality of the 'sw' set (White squares in the construction).
    It corresponds to a triangular number. -/
lemma card_sw_eq_triangular (n k : ℕ) (h_n : n = 2 * k) :
  (sw n).card = k * (k + 1) / 2 := by
  -- 1. Define a simple triangular target set t
  let t : Finset (Fin k × Fin k) := univ.filter (λ p => p.1.val + p.2.val < k)

  -- 2. Prove t has cardinality k(k+1)/2
  have h_card_t : t.card = k * (k + 1) / 2 := by
    let s := (Finset.range k).sigma (λ i => Finset.range (k - i))
    have h_bij : t.card = s.card := by
      apply Finset.card_bij (λ p _ => ⟨p.1.val, p.2.val⟩)
      · intro p hp
        rw [mem_filter] at hp; simp only [s, mem_sigma, mem_range]
        constructor <;> omega
      · intro _ _ _ _ h
        simp at h
        ext
        · exact h.1
        · exact h.2
      · intro ⟨i, j⟩ h
        simp only [s, mem_sigma, mem_range] at h
        refine ⟨(⟨i, by omega⟩, ⟨j, by omega⟩), ?_, ?_⟩
        · rw [mem_filter]; simp; omega
        · simp
    rw [h_bij, Finset.card_sigma]; simp only [Finset.card_range]
    exact sum_range_sub_eq_triangular k

  -- 3. Define mapping f using the global definition
  let f := transform n k h_n

  -- 4. Use card_bij to show |sw| = |t|
  rw [← h_card_t]
  apply Finset.card_bij (λ p _ => f p)

  -- [Goal A] Range check: p ∈ sw -> f p ∈ t
  · intro p hp
    unfold sw at hp; rw [mem_filter] at hp
    -- Expand f (transform) and split cases
    simp only [f, transform]
    split_ifs
    · -- Case: sw_lower
      simp [t, mem_filter]; unfold isSw at hp
      rcases hp.2 with h|h
      · -- Valid case
        omega
      · -- Contradiction case (x is odd)
        omega
    · -- Case: sw_upper
      simp [t, mem_filter]; unfold isSw at hp
      rcases hp.2 with h|h
      · -- Contradiction case (x is even)
        omega
      · -- Valid case
        omega

  -- [Goal B] Injectivity
  · apply transform_inj_on_sw n k h_n

  -- [Goal C] Surjectivity
  · intro b hb
    -- 1. Expand definitions
    simp only [f]
    -- 2. Obtain the pre-image p using the surjectivity lemma
    rcases transform_surjective_on_t n k h_n b hb with ⟨p, hp, heq⟩
    -- 3. Use p
    use p

/-- Lemma: Adjacent squares always have different parity of the sum of their coordinates. -/
lemma adjacent_parity_ne {n : ℕ} {p m : Square n} (h : Adjacent p m) :
    (p.1.val + p.2.val) % 2 ≠ (m.1.val + m.2.val) % 2 := by
  unfold Adjacent at h
  let r1 := (p.1.val : ℤ); let c1 := (p.2.val : ℤ)
  let r2 := (m.1.val : ℤ); let c2 := (m.2.val : ℤ)
  -- Since the sum of absolute differences is 1, (Δr, Δc) is (±1, 0) or (0, ±1)
  have h_cases : (r1 - r2).natAbs = 1 ∧ (c1 - c2).natAbs = 0 ∨
                 (r1 - r2).natAbs = 0 ∧ (c1 - c2).natAbs = 1 := by omega
  rcases h_cases with ⟨_, _⟩ | ⟨_, _⟩ <;> omega

-- 4. Lower Bound Lemma (Key Logic)

/-- Condition for a set of points to be "independent" (pairwise distance > 2).
    This matches the `sw` condition. -/
def IsIndependentPoint (n : ℕ) (p : Square n) : Prop := isSw n p.1 p.2

/-- Lemma: Independent points cannot share a common neighbor.
    If p1, p2 ∈ sw and they both are adjacent to m, then p1 = p2. -/
lemma independent_points_cant_share_neighbor (n : ℕ) (p1 p2 m : Square n)
  (h1 : IsIndependentPoint n p1) (h2 : IsIndependentPoint n p2)
  (h_adj1 : Adjacent p1 m) (h_adj2 : Adjacent p2 m) : p1 = p2 := by

  -- Prepare for contradiction and unfold definitions
  by_contra h_ne
  unfold IsIndependentPoint isSw at h1 h2; unfold Adjacent at h_adj1 h_adj2

  -- Decompose points into coordinates
  rcases p1 with ⟨⟨x1, _⟩, ⟨y1, _⟩⟩
  rcases p2 with ⟨⟨x2, _⟩, ⟨y2, _⟩⟩
  rcases m  with ⟨⟨xm, _⟩, ⟨ym, _⟩⟩
  simp only [Prod.ext_iff, Fin.ext_iff] at h_ne

  -- Cast to Int to avoid Nat subtraction saturation (crucial for omega)
  let ix1 : ℤ := x1; let iy1 : ℤ := y1
  let ix2 : ℤ := x2; let iy2 : ℤ := y2
  let ixm : ℤ := xm; let iym : ℤ := ym
  simp only at h1 h2 h_adj1 h_adj2

  -- Check all parity combinations (Lower/Upper) for contradiction
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> omega

/--
Helper: A parity-dependent transformation.
If target_parity is 0, it keeps points as is.
Otherwise (assumed to be 1), it reflects the x-coordinate (n - 1 - x).
-/
def parityTransform (n : ℕ) (target_parity : ℕ) (p : Square n) : Square n :=
  if target_parity = 0 then
    p
  else
    (⟨n - 1 - p.1.val, by omega⟩, p.2)

/--
Lemma: parityTransform is injective.
-/
lemma parity_transform_injective (n target_parity : ℕ) :
    Function.Injective (parityTransform n target_parity) := by
  intro p1 p2 h
  simp [parityTransform] at h; split_ifs at h <;> simp_all; ext <;> omega

/--
  **Lower Bound Lemma (Revised):**
  If s covers all squares with a specific target parity (0 or 1),
  then |s| ≥ n(n+2)/8.
-/
lemma card_lower_bound_of_cover (n k : ℕ) (h_n : n = 2 * k)
  (s : Finset (Square n)) (target_parity : ℕ)
  (h_tp_range : target_parity ≤ 1)
  (h_cover : ∀ p : Square n, (p.1.val + p.2.val) % 2 = target_parity → ∃ m ∈ s, Adjacent p m)
  : s.card ≥ n * (n + 2) / 8 := by

  -- 1. Base Set sw definition
  -- Use sw n directly to avoid shadowing issues
  have h_card_sw : (sw n).card = k * (k + 1) / 2 :=
    card_sw_eq_triangular n k h_n

  -- 2. Define the image set i using the parity transformation
  let trans := parityTransform n target_parity
  let i := (sw n).map ⟨trans, parity_transform_injective n target_parity⟩

  have h_card_i : i.card = k * (k + 1) / 2 := by simp [i, h_card_sw]

  -- 3. Property: All points in i have the correct target parity
  have h_i_parity : ∀ p ∈ i, (p.1.val + p.2.val) % 2 = target_parity := by
    intro p hp
    rw [mem_map] at hp
    rcases hp with ⟨a, ha_sw, rfl⟩
    -- Analyze parity of the transformed point
    simp [trans, parityTransform]
    split_ifs with h_tp_zero
    · -- target_parity = 0 (Identity)
      subst h_tp_zero
      unfold sw at ha_sw; rw [mem_filter] at ha_sw; unfold isSw at ha_sw
      rcases ha_sw.2 with h|h <;> omega
    · -- target_parity = 1 (Reflection)
      unfold sw at ha_sw; rw [mem_filter] at ha_sw; unfold isSw at ha_sw
      rcases ha_sw with ⟨_, h_sw⟩
      simp [h_n]
      rcases h_sw with h|h <;> omega

  -- 4. Construct injection f: i -> s
  -- We map each p ∈ i to its neighbor m ∈ s
  let f_rel : i → s → Prop := λ p m => Adjacent p.1 m.1
  have h_exists : ∀ p : i, ∃ m : s, f_rel p m := by
    intro p
    have h_par := h_i_parity p.1 p.2
    rcases h_cover p.1 h_par with ⟨m, hm_in, h_adj⟩
    use ⟨m, hm_in⟩

  let f (p : i) : s := Classical.choose (h_exists p)
  have h_f (p : i) : Adjacent p.1 (f p).1 := Classical.choose_spec (h_exists p)

  -- 5. Prove Injectivity of f
  -- This is the core logic: "Neighbors of independent points are distinct"
  have h_inj : Function.Injective f := by
    intro p1 p2 h_eq
    let m := (f p1).1
    have h_adj1 : Adjacent p1.1 m := h_f p1
    have h_adj2 : Adjacent p2.1 m := by
      have h_m_eq : (f p2).1 = m := by rw [← h_eq]
      rw [← h_m_eq]
      exact h_f p2

    -- Unpack the points back to the original sw set (Pre-image)
    rcases p1 with ⟨val1, prop1⟩
    rcases p2 with ⟨val2, prop2⟩
    simp [i] at prop1 prop2
    rcases prop1 with ⟨p1x, p1y, ⟨h_mem1, h_eq1⟩⟩
    rcases prop2 with ⟨p2x, p2y, ⟨h_mem2, h_eq2⟩⟩
    apply Subtype.ext

    if h_par : target_parity = 0 then
      -- Case 1: Identity transform
      simp [trans, parityTransform, h_par] at h_eq1 h_eq2
      have h_adj_v1 : Adjacent val1 m := h_adj1
      have h_adj_v2 : Adjacent val2 m := h_adj2
      rw [← h_eq1] at h_adj_v1; rw [← h_eq2] at h_adj_v2
      have h_indep1 : IsIndependentPoint n (p1x, p1y) := by
        unfold sw at h_mem1; rw [mem_filter] at h_mem1; exact h_mem1.2
      have h_indep2 : IsIndependentPoint n (p2x, p2y) := by
        unfold sw at h_mem2; rw [mem_filter] at h_mem2; exact h_mem2.2
      have h_base_eq : (p1x, p1y) = (p2x, p2y) :=
        independent_points_cant_share_neighbor n _ _ m h_indep1 h_indep2 h_adj_v1 h_adj_v2
      dsimp; rw [← h_eq1, ← h_eq2]; exact h_base_eq
    else
      -- Case 2: Reflection transform
      unfold Adjacent at h_adj1 h_adj2
      simp [trans, parityTransform, h_par] at h_eq1 h_eq2
      unfold sw at h_mem1 h_mem2; rw [mem_filter] at h_mem1 h_mem2
      let m_inv : Square n := (⟨n - 1 - m.1.val, by omega⟩, m.2)
      have h_adj_b1 : Adjacent (p1x, p1y) m_inv := by
        dsimp at h_adj1; rw [← h_eq1] at h_adj1; simp at h_adj1
        unfold Adjacent; dsimp [m_inv]; omega
      have h_adj_p2 : Adjacent (p2x, p2y) m_inv := by
        dsimp at h_adj2; rw [← h_eq2] at h_adj2; simp at h_adj2
        unfold Adjacent; dsimp [m_inv]; omega
      have h_base_eq : (p1x, p1y) = (p2x, p2y) :=
        independent_points_cant_share_neighbor n (p1x, p1y) (p2x, p2y) m_inv
          h_mem1.2 h_mem2.2 h_adj_b1 h_adj_p2
      dsimp; rw [← h_eq1, ← h_eq2]
      injection h_base_eq with h_b h_sw
      subst h_b h_sw; rfl

  -- 6. Final Calculation
  have h_card := Fintype.card_le_of_injective f h_inj
  simp only [Fintype.card_coe, card_map, i] at h_card
  rw [h_card_sw] at h_card
  have h_mul : n * (n + 2) = 4 * (k * (k + 1)) := by rw [h_n]; ring
  rw [h_mul]; omega


/--
Lemma: For any square `q` whose coordinate sum is odd,
there exists a marked square in `sw` adjacent to `q`.
This handles the detailed case analysis for the valid marking construction.
-/
lemma exists_adjacent_in_sw_of_odd_sum (n : ℕ) (h_pos : 0 < n) (h_even : Even n)
    (q : Square n) (h_sum_odd : (q.1.val + q.2.val) % 2 = 1) :
    ∃ m ∈ sw n, Adjacent q m := by
  let qx := q.1.val; let qy := q.2.val
  have h_n_mod2 : n % 2 = 0 := (Nat.even_iff).mp h_even
  -- The logic below exhaustively checks cases based on the construction of sw.
  unfold sw; simp only [mem_filter, Finset.mem_univ, true_and]; unfold isSw Adjacent

  if _ : qx + qy < n then
    -- Case: Lower Triangle region
    if _ : (qx + qy) % 4 = 1 then
      if _ : qy % 2 = 1 then
        -- Neighbor below
        let my : Fin n := ⟨qy - 1, by omega⟩
        use (q.1, my); have : my.val = qy - 1 := rfl; dsimp; omega
      else
        -- Neighbor left
        let mx : Fin n := ⟨qx - 1, by omega⟩
        use (mx, q.2); have : mx.val = qx - 1 := rfl; dsimp; omega
    else
        -- Case: Sum % 4 = 3 (Implied by odd sum and != 1)
        by_cases h_boundary : qx + qy = n - 1
        · -- Boundary case: requires care to stay within bounds
          if _ : qy % 2 = 1 then
            let mx : Fin n := ⟨qx + 1, by omega⟩
            use (mx, q.2); have : mx.val = qx + 1 := rfl; dsimp; omega
          else
            let my : Fin n := ⟨qy + 1, by omega⟩
            use (q.1, my); have : my.val = qy + 1 := rfl; dsimp; omega
        · -- Normal Lower case (Sum % 4 = 3, not boundary)
          if _ : qy % 2 = 1 then
            let my : Fin n := ⟨qy + 1, by omega⟩
            use (q.1, my); have : my.val = qy + 1 := rfl; dsimp; omega
          else
            let mx : Fin n := ⟨qx + 1, by omega⟩
            use (mx, q.2); have : mx.val = qx + 1 := rfl; dsimp; omega
  else
    -- Case: Upper Triangle region (qx + qy ≥ n)
    if _ : (qx + qy) % 4 = 1 then
        if _ : qy % 2 = 1 then
          let mx : Fin n := ⟨qx - 1, by omega⟩
          use (mx, q.2); have : mx.val = qx - 1 := rfl; dsimp; omega
        else
          let my : Fin n := ⟨qy - 1, by omega⟩
          use (q.1, my); have : my.val = qy - 1 := rfl; dsimp; omega
    else
        -- Case Sum % 4 = 3 in Upper
        if _ : qy % 2 = 1 then
          let mx : Fin n := ⟨qx + 1, by omega⟩
          use (mx, q.2); have : mx.val = qx + 1 := rfl; dsimp; omega
        else
          let my : Fin n := ⟨qy + 1, by omega⟩
          use (q.1, my); have : my.val = qy + 1 := rfl; dsimp; omega

/--
Lemma: The sets sw and sb are disjoint.
(Points in sw have even sum, points in sb have odd sum relative to the transform).
-/
lemma disjoint_sw_sb (n : ℕ) (h_pos : 0 < n) (h_even : Even n) :
  Disjoint (sw n) (sb n) := by
  rw [Finset.disjoint_left]
  intro p hp_sw hp_sb
  unfold sw at hp_sw; rw [mem_filter] at hp_sw
  unfold sb at hp_sb; rw [mem_filter] at hp_sb
  let x := p.1.val; let y := p.2.val

  -- Extract parity facts from predicates
  have h_sw_mod2 : (x + y) % 2 = 0 := by
    rcases hp_sw.2 with h | h <;> { have := h.2.2.1; omega }
  have h_sb_mod2 : (n - 1 - x + y) % 2 = 0 := by
    rcases hp_sb.2 with h | h <;> { have := h.2.2.1; omega }

  -- Derive contradiction
  have h_contra : (n - 1) % 2 = 0 := by omega
  have h_n_mod2 : n % 2 = 0 := (Nat.even_iff).mp h_even
  omega

/--
Lemma: Symmetry implies |sw| = |sb|.
The map x ↦ n - 1 - x is a bijection swapping the two sets.
-/
lemma card_sw_eq_card_sb (n : ℕ) :
  (sw n).card = (sb n).card := by
  let f : Square n → Square n := λ p =>
    (⟨n - 1 - p.1.val, by omega⟩, p.2)
  apply Finset.card_bijective f
  · -- Bijective
    rw [Function.Bijective]; constructor
    · intro a b h; simp [f] at h; ext <;> omega
    · intro b; use f b; simp [f]
      ext
      · have h_le : b.1.val ≤ n - 1 := Nat.le_pred_of_lt b.1.isLt
        apply Nat.sub_sub_self h_le
      · rfl
  · -- Maps sw to sb (and vice versa logic implies bijection on domains)
    intro p
    simp only [f]; unfold sw sb; simp only [mem_filter, Finset.mem_univ, true_and]
    have h_rev : n - 1 - (n - 1 - p.1.val) = p.1.val := by omega
    simp_rw [h_rev]

-- 5. Sufficiency Proof (Size and Validity)

theorem imo1999_p3_sufficiency (n : ℕ) (h_pos : 0 < n) (h_even : Even n) :
  let min_k := n * (n + 2) / 4; let s := solutionSet n
  s.card = min_k ∧ IsValidMarking s := by

  have h_n_mod2 : n % 2 = 0 := (Nat.even_iff).mp h_even

  intro min_k s
  constructor
  · -- Part 1: Cardinality (|s| = min_k)
    -- 1. Decomposition
    have h_union : s = sw n ∪ sb n := rfl

    -- 2. Apply Lemmata
    have h_disjoint := disjoint_sw_sb n h_pos h_even
    have h_sym := card_sw_eq_card_sb n

    -- Calculate |sw|
    have h_card_sw : (sw n).card = n * (n + 2) / 8 := by
      let k := n / 2
      have hk : n = 2 * k := by omega
      rw [card_sw_eq_triangular n k hk, hk]
      rw [← Nat.mul_add 2 k 1, Nat.mul_assoc, Nat.mul_left_comm k 2]; omega

    rw [h_union, Finset.card_union_of_disjoint h_disjoint, ← h_sym, h_card_sw]
    have h_arith : 2 * (n * (n + 2) / 8) = n * (n + 2) / 4 := by
      rcases h_even with ⟨k, rfl⟩
      simp only [← two_mul]
      rw [← Nat.mul_add 2 k 1, Nat.mul_assoc, Nat.mul_left_comm k 2]
      rcases Nat.even_mul_succ_self k with ⟨m, hm⟩; omega
    omega

  · -- Part 2: Validity
    intro p

    rcases Nat.mod_two_eq_zero_or_one (p.1.val + p.2.val) with h_even_sum | h_odd_sum
    · -- Case: Even sum (Use Reflection + Lemma)
      -- 1. Reflect point p to p'
      let p' : Square n := (⟨n - 1 - p.1.val, by omega⟩, p.2)

      -- 2. p' has odd sum
      have h_p'_odd : (p'.1.val + p'.2.val) % 2 = 1 := by
         have h_x_sum : p'.1.val + p.1.val = n - 1 := by
            have : p'.1.val = n - 1 - p.1.val := rfl; omega
         have h_y_eq : p'.2.val = p.2.val := rfl
         omega

      -- 3. Apply the global Lemma to p' to find neighbor m' in sw
      rcases exists_adjacent_in_sw_of_odd_sum n h_pos h_even p' h_p'_odd with ⟨m', hm'_sw, h_adj'⟩

      -- 4. Reflect m' back to m to find neighbor in sb
      let m : Square n := (⟨n - 1 - m'.1.val, by omega⟩, m'.2)
      use m
      constructor
      · -- m ∈ sb implies m ∈ s
        simp only [s, solutionSet, mem_union]
        right
        unfold sb; rw [mem_filter]; simp only [Finset.mem_univ, true_and]
        have h_coord : n - 1 - m.1.val = m'.1.val := by
            have : m.1.val = n - 1 - m'.1.val := rfl; omega
        rw [h_coord]; unfold sw at hm'_sw; rw [mem_filter] at hm'_sw; exact hm'_sw.2
      · -- Adjacency is preserved under reflection
        unfold Adjacent; simp
        have h_dist : ((p.1.val : ℤ) - m.1.val).natAbs = ((p'.1.val : ℤ) - m'.1.val).natAbs := by
           have : p'.1.val = n - 1 - p.1.val := rfl
           have : m.1.val = n - 1 - m'.1.val := rfl
           omega
        rw [h_dist]; exact h_adj'

    · -- Case: Odd sum (Directly apply Lemma)
      -- Directly call the lemma
      rcases exists_adjacent_in_sw_of_odd_sum n h_pos h_even p h_odd_sum with ⟨m, hm_sw, h_adj⟩
      use m
      constructor
      · -- m ∈ sw implies m ∈ s
        simp only [s, solutionSet, mem_union]
        left; exact hm_sw
      · exact h_adj


-- 6. Necessity Proof (|S| ≧ N)

theorem imo1999_p3_necessity (n : ℕ) (h_even : Even n) (s : Finset (Square n)) :
  IsValidMarking s → s.card ≥ n * (n + 2) / 4 := by
  intro h_valid
  have h_n_mod2 : n % 2 = 0 := Nat.even_iff.mp h_even
  rcases h_even with ⟨k, h_n⟩
  let sw := s.filter (λ p => (p.1.val + p.2.val) % 2 = 0)
  let sb := s.filter (λ p => (p.1.val + p.2.val) % 2 = 1)
  have h_disjoint : Disjoint sw sb := by
    rw [Finset.disjoint_left]
    intro p h_in_sw h_in_sb
    rw [mem_filter] at h_in_sw h_in_sb
    have h0 := h_in_sw.2; have h1 := h_in_sb.2
    rw [h0] at h1; contradiction
  have h_union : s = sw ∪ sb := by
    ext p; rw [mem_union, mem_filter, mem_filter]
    constructor <;> intro h
    · simp [h]; omega
    · rcases h with ⟨h, _⟩ | ⟨h, _⟩ <;> exact h

  have h_card_s : s.card = sw.card + sb.card := by
    rw [h_union, Finset.card_union_of_disjoint h_disjoint]

  let even_sum_squares := squaresEvenSum n
  let odd_sum_squares  := squaresOddSum n

  have h_cover_even : ∀ p ∈ even_sum_squares, ∃ m ∈ sb, Adjacent p m := by
    intro p hp
    rcases h_valid p with ⟨m, hm_in_s, h_adj⟩
    use m; constructor
    · dsimp [sb]; rw [mem_filter]
      use hm_in_s
      dsimp [even_sum_squares] at hp; unfold squaresEvenSum at hp; rw [mem_filter] at hp
      have h_ne := adjacent_parity_ne h_adj
      omega
    · exact h_adj

  have h_cover_odd : ∀ p ∈ odd_sum_squares, ∃ m ∈ sw, Adjacent p m := by
    intro p hp
    rcases h_valid p with ⟨m, hm_in_s, h_adj⟩
    use m; constructor
    · dsimp [sw]; rw [mem_filter]
      use hm_in_s
      dsimp [odd_sum_squares] at hp; unfold squaresOddSum at hp; rw [mem_filter] at hp
      have h_ne := adjacent_parity_ne h_adj
      omega
    · exact h_adj

  -- Apply Lower Bound Lemma
  have h_bound_sb : sb.card ≥ n * (n + 2) / 8 := by
    rw [← two_mul] at h_n
    apply card_lower_bound_of_cover n k h_n sb 0 zero_le_one
    intro p h_parity0
    refine h_cover_even p ?_
    dsimp [even_sum_squares, squaresEvenSum]
    exact (mem_filter_univ p).mpr h_parity0

  have h_bound_sw : sw.card ≥ n * (n + 2) / 8 := by
    rw [← two_mul] at h_n
    apply card_lower_bound_of_cover n k h_n sw 1 (le_refl _)
    intro p h_parity1
    refine h_cover_odd p ?_
    dsimp [odd_sum_squares, squaresOddSum]
    exact (mem_filter_univ p).mpr h_parity1

  rw [h_card_s]
  have h_sum_ge : sw.card + sb.card ≥ n * (n + 2) / 8 + n * (n + 2) / 8 :=
    Nat.add_le_add h_bound_sw h_bound_sb

  have h_mul : n * (n + 2) / 8 + n * (n + 2) / 8 = n * (n + 2) / 4 := by
    rw [h_n]
    rcases Nat.even_mul_succ_self k with ⟨m, hm⟩
    have h_eq : 2 * k * (2 * k + 2) = 8 * m := by
      rw [← Nat.mul_add 2 k 1, Nat.mul_assoc, Nat.mul_left_comm k 2, hm]; ring
    simp only [← two_mul]; rw [h_eq]; omega
  rw [h_mul] at h_sum_ge
  exact h_sum_ge

snip end

determine solution_value (n : ℕ) : ℕ := n * (n + 2) / 4

problem imo1999_p3 (n : ℕ) (h_pos : 0 < n) (h_even : Even n) :
  IsLeast
    {k : ℕ | ∃ s : Finset (Square n), IsValidMarking s ∧ s.card = k}
    (solution_value n) := by
  constructor
  -- 1. Membership (Sufficiency): A valid marking of size N exists.
  · simp only [Set.mem_setOf_eq]
    use solutionSet n
    exact (imo1999_p3_sufficiency n h_pos h_even).symm
  -- 2. Lower Bound (Necessity): Any valid marking has size at least N.
  · intro k hk
    simp only [Set.mem_setOf_eq] at hk
    rcases hk with ⟨s, h_valid, h_card_eq⟩
    have h_ge := imo1999_p3_necessity n h_even s h_valid
    rw [← h_card_eq]
    exact h_ge

end Imo1999P3
