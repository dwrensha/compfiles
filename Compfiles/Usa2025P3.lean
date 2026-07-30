/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.Order.CompletePartialOrder
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics, .Geometry] }

/-!
# USA Mathematical Olympiad 2025, Problem 3

Alice the architect and Bob the builder play a game. First, Alice chooses two points `P`
and `Q` in the plane and a subset `S` of the plane, which are announced to Bob. Next, Bob
marks infinitely many points in the plane, designating each a city. He may not place two
cities within distance at most one unit of each other, and no three cities he places may
be collinear. Finally, roads are constructed between the cities as follows: each pair
`A`, `B` of cities is connected with a road along the line segment `AB` if and only if
the following condition holds: for every city `C` distinct from `A` and `B`, there exists
`R ∈ S` such that `△PQR` is directly similar to either `△ABC` or `△BAC`.

Alice wins the game if (i) the resulting roads allow for travel between any pair of
cities via a finite sequence of roads and (ii) no two roads cross. Otherwise, Bob wins.
Determine, with proof, which player has a winning strategy.
-/

namespace Usa2025P3

/-- `DirectlySimilar P Q R A B C` asserts that triangle `PQR` is directly similar to
triangle `ABC` (with the vertices listed in corresponding order); in complex coordinates
this is the equation `(R - P) / (Q - P) = (C - A) / (B - A)`, written here in cleared
form. -/
def DirectlySimilar (P Q R A B C : ℂ) : Prop :=
  (R - P) * (B - A) = (C - A) * (Q - P)

/-- The road relation: cities `i` and `j` are joined by a road iff for every other city
`k` there is a point `R ∈ S` such that `△PQR` is directly similar to `△c i c j c k` or to
`△c j c i c k`. -/
def road (P Q : ℂ) (S : Set ℂ) (c : ℕ → ℂ) (i j : ℕ) : Prop :=
  i ≠ j ∧ ∀ k : ℕ, k ≠ i → k ≠ j →
    ∃ R ∈ S, DirectlySimilar P Q R (c i) (c j) (c k) ∨ DirectlySimilar P Q R (c j) (c i) (c k)

/-- The two players of the game. -/
inductive Player : Type
  | alice : Player
  | bob : Player

/-- The answer to the problem: Alice has a winning strategy. -/
determine winner : Player := .alice

snip begin

/-!
## Solution overview

Alice picks any two distinct points `P`, `Q` and takes `S` to be the complement of the
closed disk with diameter `PQ`. For cities `A ≠ B`, the two direct similarities sending
`{A, B}` to `{P, Q}` both map the closed disk with diameter `AB` onto the closed disk
with diameter `PQ`, so the road `AB` is built if and only if the disk with diameter `AB`
contains no third city: the road graph is exactly the *Gabriel graph* of the city set.
The Gabriel graph of a set of points at pairwise distance greater than `1` is connected
(by infinite descent: a non-edge `pq` forces a city in the disk with diameter `pq`, which
yields a non-edge whose squared distance dropped by more than `1`) and planar (if edges
`ac` and `bd` crossed, some corner of the resulting convex quadrilateral would have an
angle of at least `90°`, putting a city inside the opposite disk). Hence Alice wins.
-/

/-- Alice's choice of `S`: the complement of the closed disk with diameter `PQ`. -/
def aliceSet (P Q : ℂ) : Set ℂ := {z | dist P Q / 2 < dist z ((P + Q) / 2)}

/-- A point `r` lies in the closed disk with diameter `ab` iff `⟪r - a, r - b⟫_ℝ ≤ 0`. -/
lemma disk_mem_iff_inner_nonpos (a b r : ℂ) :
    dist r ((a + b) / 2) ≤ dist a b / 2 ↔ inner ℝ (r - a) (r - b) ≤ 0 := by
  have h1 : r - (a + b) / 2 = ((r - a) + (r - b)) / 2 := by ring
  have h2 : a - b = (r - b) - (r - a) := by ring
  rw [dist_eq_norm, dist_eq_norm, h1, h2, norm_div, RCLike.norm_two]
  rw [← sq_le_sq₀ (by positivity : (0:ℝ) ≤ ‖(r - a) + (r - b)‖ / 2)
    (by positivity : (0:ℝ) ≤ ‖(r - b) - (r - a)‖ / 2)]
  have e1 : (‖(r - a) + (r - b)‖ / 2) ^ 2 = ‖(r - a) + (r - b)‖ ^ 2 / 4 := by ring
  have e2 : (‖(r - b) - (r - a)‖ / 2) ^ 2 = ‖(r - b) - (r - a)‖ ^ 2 / 4 := by ring
  rw [e1, e2, norm_sub_sq_real, norm_add_sq_real, real_inner_comm (r - b) (r - a)]
  constructor <;> intro h <;> linarith

/-- The direct similarity sending `a` to `P` and `b` to `Q` maps the closed disk with
diameter `ab` onto the closed disk with diameter `PQ`. -/
lemma sim_aliceSet_iff (P Q : ℂ) (hPQ : P ≠ Q) {a b : ℂ} (hab : a ≠ b) (z : ℂ) :
    P + (z - a) * (Q - P) / (b - a) ∈ aliceSet P Q ↔
      dist a b / 2 < dist z ((a + b) / 2) := by
  have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  have hPQd : (0:ℝ) < dist P Q := dist_pos.mpr hPQ
  have habd : (0:ℝ) < dist a b := dist_pos.mpr hab
  have hid : (P + (z - a) * (Q - P) / (b - a)) - (P + Q) / 2 =
      (Q - P) / (b - a) * (z - (a + b) / 2) := by
    field_simp
    ring
  have hnorm : dist (P + (z - a) * (Q - P) / (b - a)) ((P + Q) / 2) =
      dist P Q / dist a b * dist z ((a + b) / 2) := by
    conv_lhs => rw [dist_eq_norm, hid, norm_mul, norm_div]
    rw [← dist_eq_norm Q P, dist_comm Q P, ← dist_eq_norm b a, dist_comm b a,
      ← dist_eq_norm z ((a + b) / 2)]
  show dist P Q / 2 < dist (P + (z - a) * (Q - P) / (b - a)) ((P + Q) / 2) ↔ _
  rw [hnorm, div_mul_eq_mul_div, lt_div_iff₀ habd,
    show dist P Q / 2 * dist a b = dist P Q * (dist a b / 2) by ring,
    mul_lt_mul_iff_right₀ hPQd]

/-- The road relation is symmetric. -/
lemma road_symm (P Q : ℂ) (S : Set ℂ) (c : ℕ → ℂ) {i j : ℕ}
    (h : road P Q S c i j) : road P Q S c j i := by
  obtain ⟨hne, h⟩ := h
  refine ⟨hne.symm, fun k hkj hki => ?_⟩
  obtain ⟨R, hR, hd | hd⟩ := h k hki hkj
  · exact ⟨R, hR, Or.inr hd⟩
  · exact ⟨R, hR, Or.inl hd⟩

/-- Reachability through roads is symmetric. -/
lemma conn_symm (P Q : ℂ) (S : Set ℂ) (c : ℕ → ℂ) {i j : ℕ}
    (h : Relation.ReflTransGen (road P Q S c) i j) :
    Relation.ReflTransGen (road P Q S c) j i := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih =>
    exact Relation.ReflTransGen.trans
      (Relation.ReflTransGen.single (road_symm P Q S c hbc)) ih

/-- If the road between `i` and `j` is built, then any other city `k` sees the segment
`c i c j` under an acute angle: `⟪c k - c i, c k - c j⟫_ℝ > 0`. -/
lemma road_inner_pos (P Q : ℂ) (hPQ : P ≠ Q) (c : ℕ → ℂ) (hinj : Function.Injective c)
    {i j k : ℕ} (hki : k ≠ i) (hkj : k ≠ j)
    (hijr : road P Q (aliceSet P Q) c i j) :
    0 < inner ℝ (c k - c i) (c k - c j) := by
  obtain ⟨hne, h⟩ := hijr
  obtain ⟨R, hRS, hd⟩ := h k hki hkj
  have hAB : c i ≠ c j := hinj.ne hne
  have hlt : dist (c i) (c j) / 2 < dist (c k) ((c i + c j) / 2) := by
    rcases hd with hd | hd
    · have hR : R = P + (c k - c i) * (Q - P) / (c j - c i) := by
        have h2 : R - P = (c k - c i) * (Q - P) / (c j - c i) :=
          eq_div_of_mul_eq (sub_ne_zero.mpr hAB.symm) hd
        rw [← h2]
        ring
      rw [hR] at hRS
      exact (sim_aliceSet_iff P Q hPQ hAB (c k)).mp hRS
    · have hR : R = P + (c k - c j) * (Q - P) / (c i - c j) := by
        have h2 : R - P = (c k - c j) * (Q - P) / (c i - c j) :=
          eq_div_of_mul_eq (sub_ne_zero.mpr hAB) hd
        rw [← h2]
        ring
      rw [hR] at hRS
      have hlt' := (sim_aliceSet_iff P Q hPQ hAB.symm (c k)).mp hRS
      rwa [dist_comm (c j) (c i), add_comm (c j) (c i)] at hlt'
  have hnot : ¬ inner ℝ (c k - c i) (c k - c j) ≤ 0 := by
    intro hi
    have hle := (disk_mem_iff_inner_nonpos (c i) (c j) (c k)).mpr hi
    linarith
  exact not_le.mp hnot

/-- Descent step: a pair of cities in different components of the road graph yields
another such pair whose squared distance dropped by more than `1`. -/
lemma conn_descent (P Q : ℂ) (hPQ : P ≠ Q) (c : ℕ → ℂ) (hinj : Function.Injective c)
    (hdist : ∀ ⦃i j⦄, i ≠ j → 1 < dist (c i) (c j))
    {i j : ℕ} (hij : ¬ Relation.ReflTransGen (road P Q (aliceSet P Q) c) i j) :
    ∃ i' j' : ℕ, ¬ Relation.ReflTransGen (road P Q (aliceSet P Q) c) i' j' ∧
      dist (c i') (c j') ^ 2 + 1 < dist (c i) (c j) ^ 2 := by
  classical
  have hne : i ≠ j := by
    rintro rfl
    exact hij Relation.ReflTransGen.refl
  have hnroad : ¬ road P Q (aliceSet P Q) c i j :=
    fun hr => hij (Relation.ReflTransGen.single hr)
  have hnr : ¬ ∀ k : ℕ, k ≠ i → k ≠ j → ∃ R ∈ aliceSet P Q,
      DirectlySimilar P Q R (c i) (c j) (c k) ∨
        DirectlySimilar P Q R (c j) (c i) (c k) :=
    fun h => hnroad ⟨hne, h⟩
  push Not at hnr
  obtain ⟨k, hki, hkj, hk⟩ := hnr
  have hAB : c i ≠ c j := hinj.ne hne
  -- The candidate point for the first similarity does not lie in `aliceSet P Q`,
  -- hence `c k` lies in the closed disk with diameter `c i c j`.
  have hDS₁ : DirectlySimilar P Q (P + (c k - c i) * (Q - P) / (c j - c i))
      (c i) (c j) (c k) := by
    show ((P + (c k - c i) * (Q - P) / (c j - c i)) - P) * (c j - c i) =
      (c k - c i) * (Q - P)
    rw [add_sub_cancel_left]
    exact div_mul_cancel₀ _ (sub_ne_zero.mpr hAB.symm)
  have hdisk : dist (c k) ((c i + c j) / 2) ≤ dist (c i) (c j) / 2 := by
    by_contra hlt
    have hlt' : dist (c i) (c j) / 2 < dist (c k) ((c i + c j) / 2) := not_le.mp hlt
    have hmem : P + (c k - c i) * (Q - P) / (c j - c i) ∈ aliceSet P Q :=
      (sim_aliceSet_iff P Q hPQ hAB (c k)).mpr hlt'
    exact (hk _ hmem).1 hDS₁
  have hinner : inner ℝ (c k - c i) (c k - c j) ≤ 0 :=
    (disk_mem_iff_inner_nonpos (c i) (c j) (c k)).mp hdisk
  have hpyt : dist (c i) (c k) ^ 2 + dist (c j) (c k) ^ 2 ≤ dist (c i) (c j) ^ 2 := by
    rw [dist_comm (c i) (c k), dist_comm (c j) (c k), dist_eq_norm, dist_eq_norm,
      dist_eq_norm]
    have e1 : c i - c j = (c k - c j) - (c k - c i) := by ring
    have e2 : ‖(c k - c j) - (c k - c i)‖ ^ 2 =
        ‖c k - c j‖ ^ 2 - 2 * inner ℝ (c k - c i) (c k - c j) + ‖c k - c i‖ ^ 2 := by
      rw [norm_sub_sq_real, real_inner_comm (c k - c i) (c k - c j)]
    rw [e1, e2]
    linarith
  have h1i : (1:ℝ) < dist (c i) (c k) ^ 2 := by
    have h := hdist hki
    rw [dist_comm (c k) (c i)] at h
    have hd0 : (0:ℝ) ≤ dist (c i) (c k) := dist_nonneg
    nlinarith
  have h1j : (1:ℝ) < dist (c j) (c k) ^ 2 := by
    have h := hdist hkj
    rw [dist_comm (c k) (c j)] at h
    have hd0 : (0:ℝ) ≤ dist (c j) (c k) := dist_nonneg
    nlinarith
  by_cases hcase : Relation.ReflTransGen (road P Q (aliceSet P Q) c) k i
  · refine ⟨k, j, fun hkjc => hij ((conn_symm P Q (aliceSet P Q) c hcase).trans hkjc), ?_⟩
    have h2 : dist (c k) (c j) = dist (c j) (c k) := dist_comm _ _
    rw [h2]
    linarith
  · refine ⟨k, i, hcase, ?_⟩
    have h2 : dist (c k) (c i) = dist (c i) (c k) := dist_comm _ _
    rw [h2]
    linarith

/-- The Gabriel graph of a legal play by Bob is connected. -/
lemma connected (P Q : ℂ) (hPQ : P ≠ Q) (c : ℕ → ℂ) (hinj : Function.Injective c)
    (hdist : ∀ ⦃i j⦄, i ≠ j → 1 < dist (c i) (c j)) (i j : ℕ) :
    Relation.ReflTransGen (road P Q (aliceSet P Q) c) i j := by
  by_contra hij
  have claim : ∀ n : ℕ, ∀ x y : ℕ,
      ¬ Relation.ReflTransGen (road P Q (aliceSet P Q) c) x y →
      (n : ℝ) < dist (c x) (c y) ^ 2 := by
    intro n
    induction n with
    | zero =>
      intro x y hxy
      have hne : x ≠ y := by
        rintro rfl
        exact hxy Relation.ReflTransGen.refl
      have hpos : (0:ℝ) < dist (c x) (c y) := dist_pos.mpr (hinj.ne hne)
      simp only [Nat.cast_zero]
      exact pow_pos hpos 2
    | succ n IH =>
      intro x y hxy
      obtain ⟨x', y', hconn', hd⟩ := conn_descent P Q hPQ c hinj hdist hxy
      have h1 := IH x' y' hconn'
      push_cast
      linarith
  obtain ⟨n, hn⟩ := exists_nat_gt (dist (c i) (c j) ^ 2)
  have h2 := claim n i j hij
  linarith

/-- The algebraic heart of planarity: if two segments cross, writing the crossing point
as the origin, the four cities are `u`, `-(l • u)`, `v`, `-(m • v)` with `0 < l, m`, and
the four "no city in the opposite disk" inequalities are contradictory: combining `A` and
`C` gives `l * (1 + l) * ⟪u,u⟫ > m * (1 + l) * ⟪v,v⟫` while `B` and `D` give the reverse
inequality. -/
lemma crossing_contradiction {u v : ℂ} {l m : ℝ} (hl : 0 < l) (hm : 0 < m)
    (hA : 0 < inner ℝ (u - v) (u + m • v))
    (hC : 0 < inner ℝ (-(l • u) - v) (-(l • u) + m • v))
    (hB : 0 < inner ℝ (v - u) (v + l • u))
    (hD : 0 < inner ℝ (-(m • v) - u) (-(m • v) + l • u)) : False := by
  have eA : inner ℝ (u - v) (u + m • v) =
      inner ℝ u u + (m - 1) * inner ℝ u v - m * inner ℝ v v := by
    simp only [inner_sub_left, inner_add_right, real_inner_smul_right,
      real_inner_comm u v]
    ring
  have eC : inner ℝ (-(l • u) - v) (-(l • u) + m • v) =
      l ^ 2 * inner ℝ u u + l * (1 - m) * inner ℝ u v - m * inner ℝ v v := by
    simp only [inner_sub_left, inner_add_right, inner_neg_left, inner_neg_right,
      real_inner_smul_left, real_inner_smul_right, real_inner_comm u v]
    ring
  have eB : inner ℝ (v - u) (v + l • u) =
      inner ℝ v v + (l - 1) * inner ℝ u v - l * inner ℝ u u := by
    simp only [inner_sub_left, inner_add_right, real_inner_smul_right,
      real_inner_comm u v]
    ring
  have eD : inner ℝ (-(m • v) - u) (-(m • v) + l • u) =
      m ^ 2 * inner ℝ v v + m * (1 - l) * inner ℝ u v - l * inner ℝ u u := by
    simp only [inner_sub_left, inner_add_right, inner_neg_left, inner_neg_right,
      real_inner_smul_left, real_inner_smul_right, real_inner_comm u v]
    ring
  rw [eA] at hA; rw [eB] at hB; rw [eC] at hC; rw [eD] at hD
  have key1 : m * (1 + l) * inner ℝ v v < l * (1 + l) * inner ℝ u u := by
    nlinarith [mul_pos hl hA]
  have key2 : l * (1 + m) * inner ℝ u u < m * (1 + m) * inner ℝ v v := by
    nlinarith [mul_pos hm hB]
  have g1 : (0:ℝ) < (l * inner ℝ u u - m * inner ℝ v v) * (1 + l) := by linarith
  have g2 : (0:ℝ) < (m * inner ℝ v v - l * inner ℝ u u) * (1 + m) := by linarith
  have p1 : (0:ℝ) < l * inner ℝ u u - m * inner ℝ v v :=
    pos_of_mul_pos_left g1 (by linarith)
  have p2 : (0:ℝ) < m * inner ℝ v v - l * inner ℝ u u :=
    pos_of_mul_pos_left g2 (by linarith)
  linarith

/-- The Gabriel graph of a legal play by Bob is planar: two roads on four distinct cities
never cross. -/
lemma planar (P Q : ℂ) (hPQ : P ≠ Q) (c : ℕ → ℂ) (hinj : Function.Injective c)
    {i j k l : ℕ} (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l)
    (hijr : road P Q (aliceSet P Q) c i j) (hklr : road P Q (aliceSet P Q) c k l) :
    Disjoint (openSegment ℝ (c i) (c j)) (openSegment ℝ (c k) (c l)) := by
  have hA := road_inner_pos P Q hPQ c hinj hik hil hklr
  have hC := road_inner_pos P Q hPQ c hinj hjk hjl hklr
  have hB := road_inner_pos P Q hPQ c hinj hik.symm hjk.symm hijr
  have hD := road_inner_pos P Q hPQ c hinj hil.symm hjl.symm hijr
  refine Set.disjoint_left.mpr fun x hx1 hx2 => ?_
  unfold openSegment at hx1 hx2
  simp only [Set.mem_setOf_eq] at hx1 hx2
  obtain ⟨a₁, a₂, ha₁, ha₂, ha, hxa⟩ := hx1
  obtain ⟨b₁, b₂, hb₁, hb₂, hb, hxb⟩ := hx2
  have ha₁' : a₁ = 1 - a₂ := by linarith
  have hb₁' : b₁ = 1 - b₂ := by linarith
  have hlam : (0:ℝ) < a₁ / a₂ := div_pos ha₁ ha₂
  have hmu : (0:ℝ) < b₁ / b₂ := div_pos hb₁ hb₂
  have hxi : c i - x = a₂ • (c i - c j) := by
    rw [← hxa, ha₁']
    module
  have hxj : c j - x = -((a₁ / a₂) • (c i - x)) := by
    rw [hxi, smul_smul, div_mul_cancel₀ _ (ne_of_gt ha₂), ← hxa, ha₁']
    module
  have hxk : c k - x = b₂ • (c k - c l) := by
    rw [← hxb, hb₁']
    module
  have hxl : c l - x = -((b₁ / b₂) • (c k - x)) := by
    rw [hxk, smul_smul, div_mul_cancel₀ _ (ne_of_gt hb₂), ← hxb, hb₁']
    module
  rw [show c i - c k = (c i - x) - (c k - x) by ring,
    show c i - c l = (c i - x) + (b₁ / b₂) • (c k - x) by
      rw [← sub_neg_eq_add, ← hxl]; ring] at hA
  rw [show c j - c k = (c j - x) - (c k - x) by ring, hxj,
    show c j - c l = (c j - x) - (c l - x) by ring, hxj, hxl, sub_neg_eq_add] at hC
  rw [show c k - c i = (c k - x) - (c i - x) by ring,
    show c k - c j = (c k - x) + (a₁ / a₂) • (c i - x) by
      rw [← sub_neg_eq_add, ← hxj]; ring] at hB
  rw [show c l - c i = (c l - x) - (c i - x) by ring, hxl,
    show c l - c j = (c l - x) - (c j - x) by ring, hxl, hxj, sub_neg_eq_add] at hD
  exact crossing_contradiction hlam hmu hA hC hB hD

snip end

/-- USA Mathematical Olympiad 2025, Problem 3: Alice has a winning strategy. She chooses
any two distinct points `P`, `Q` and the complement `S` of the closed disk with diameter
`PQ`; then whatever legal set of cities Bob builds, the road graph is connected and no
two roads cross. -/
problem usa2025_p3 :
    ∃ P Q : ℂ, ∃ S : Set ℂ, P ≠ Q ∧
      ∀ c : ℕ → ℂ, Function.Injective c →
        (∀ ⦃i j⦄, i ≠ j → 1 < dist (c i) (c j)) →
        (∀ ⦃i j k⦄, i ≠ j → i ≠ k → j ≠ k → ¬ Collinear ℝ {c i, c j, c k}) →
        (∀ i j, Relation.ReflTransGen (road P Q S c) i j) ∧
        ∀ i j k l : ℕ, i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l → k ≠ l →
          road P Q S c i j → road P Q S c k l →
          Disjoint (openSegment ℝ (c i) (c j)) (openSegment ℝ (c k) (c l)) := by
  refine ⟨0, 1, aliceSet 0 1, zero_ne_one, fun c hinj hdist _hcol =>
    ⟨fun i j => connected 0 1 zero_ne_one c hinj hdist i j,
     fun i j k l _hij hik hil hjk hjl _hkl hijr hklr =>
       planar 0 1 zero_ne_one c hinj hik hil hjk hjl hijr hklr⟩⟩

end Usa2025P3
