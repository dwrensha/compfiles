/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Tactic.Linarith
public import Mathlib.Topology.MetricSpace.Contracting
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# USA Mathematical Olympiad 1978, Problem 2

Two square maps cover exactly the same area of terrain on different scales.
The smaller map is placed on top of the larger map and inside its borders.
Show that there is a unique point on the top map which lies exactly above
the corresponding point on the lower map. How can this point be constructed?
-/

namespace Usa1978P2

open Function Set Filter
open scoped Topology

/-- A closed axis-aligned square in the Euclidean plane, described by its
lower-left corner `a` and its upper-right corner `b`. This models the region
of the plane occupied by the larger map. -/
def square (a b : EuclideanSpace ℝ (Fin 2)) : Set (EuclideanSpace ℝ (Fin 2)) :=
  {p | ∀ i, p i ∈ Set.Icc (a i) (b i)}

snip begin

/-- A square whose corners are ordered coordinatewise is nonempty:
it contains its lower-left corner. -/
theorem square_nonempty {a b : EuclideanSpace ℝ (Fin 2)} (h : ∀ i, a i ≤ b i) :
    (square a b).Nonempty :=
  ⟨a, fun i ↦ Set.left_mem_Icc.2 (h i)⟩

/-- A square is a closed subset of the plane. -/
theorem isClosed_square (a b : EuclideanSpace ℝ (Fin 2)) : IsClosed (square a b) := by
  have h : square a b =
      ⋂ i, (fun p : EuclideanSpace ℝ (Fin 2) ↦ p i) ⁻¹' Set.Icc (a i) (b i) := by
    ext p
    simp only [square, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
  rw [h]
  exact isClosed_iInter fun i ↦ isClosed_Icc.preimage (PiLp.continuous_apply 2 _ i)

/-- The correspondence between the two maps sends each pair of points to a pair
whose distance is scaled down by the factor `k < 1` (the ratio of the two scales);
in particular it is a contracting map in the sense of the Banach fixed-point
theorem. -/
theorem contractingWith_of_scale {k : NNReal} (hk : k < 1)
    {f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    (hf : ∀ p q, dist (f p) (f q) = k * dist p q) :
    ContractingWith k f :=
  ⟨hk, LipschitzWith.of_dist_le_mul fun p q ↦ (hf p q).le⟩

/-- Every iterate of a point of a forward-invariant set stays in that set. -/
theorem iterate_mem_of_mapsTo {f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    {s : Set (EuclideanSpace ℝ (Fin 2))} (hfs : MapsTo f s s)
    {x : EuclideanSpace ℝ (Fin 2)} (hx : x ∈ s) (n : ℕ) :
    f^[n] x ∈ s := by
  induction n with
  | zero => simpa using hx
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact hfs ih

snip end

problem usa1978_p2
    {k : NNReal} (hk : k < 1)
    {a b : EuclideanSpace ℝ (Fin 2)}
    (hsquare : b 0 - a 0 = b 1 - a 1) (hpos : a 0 < b 0)
    {f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    (hf : ∀ p q, dist (f p) (f q) = k * dist p q)
    (hfs : MapsTo f (square a b) (square a b)) :
    ∃! p, (p ∈ square a b ∧ IsFixedPt f p) ∧
      ∀ x ∈ square a b, Tendsto (fun n ↦ f^[n] x) atTop (𝓝 p) := by
  -- The correspondence `f` between the maps is a contraction with ratio `k < 1`,
  -- so the Banach fixed-point theorem applies.
  have hcontract : ContractingWith k f := contractingWith_of_scale hk hf
  -- The square is nonempty, since both sides have positive length.
  have hab : ∀ i, a i ≤ b i := by
    refine Fin.forall_fin_two.2 ⟨hpos.le, ?_⟩
    have h : 0 < b 1 - a 1 := by rw [← hsquare]; linarith
    linarith
  obtain ⟨x₀, hx₀⟩ := square_nonempty hab
  -- Existence: the limit of the orbit of `x₀` is a fixed point.
  obtain ⟨y, hy_fix, hy_lim, -⟩ :=
    hcontract.exists_fixedPoint x₀ (edist_ne_top x₀ (f x₀))
  -- The limit lies in the square because the square is closed and every
  -- iterate of `x₀` stays in it.
  have hy_mem : y ∈ square a b :=
    (isClosed_square a b).mem_of_tendsto hy_lim
      (Filter.Eventually.of_forall fun n ↦ iterate_mem_of_mapsTo hfs hx₀ n)
  -- Construction: starting from any point `x` of the larger map, the orbit
  -- `x, f x, f (f x), …` converges to the fixed point. (Geometrically, the
  -- fixed point can also be constructed as the intersection of the lines
  -- joining corresponding vertices of the two maps when their sides are
  -- parallel, or as the intersection of two explicitly constructible lines
  -- through intersection points of corresponding side lines in general.)
  have hlim : ∀ x ∈ square a b, Tendsto (fun n ↦ f^[n] x) atTop (𝓝 y) := by
    intro x hx
    obtain ⟨z, hz_fix, hz_lim, -⟩ :=
      hcontract.exists_fixedPoint x (edist_ne_top x (f x))
    rcases hcontract.eq_or_edist_eq_top_of_fixedPoints hz_fix hy_fix with h | h
    · rwa [← h]
    · exact absurd h (edist_ne_top z y)
  -- Uniqueness: two fixed points of a contraction coincide.
  refine ⟨y, ⟨⟨hy_mem, hy_fix⟩, hlim⟩, fun p hp ↦ ?_⟩
  rcases hcontract.eq_or_edist_eq_top_of_fixedPoints hp.1.2 hy_fix with h | h
  · exact h
  · exact absurd h (edist_ne_top p y)

end Usa1978P2
