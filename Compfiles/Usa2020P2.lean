/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.ConditionallyCompleteOrder
public import Mathlib.Data.Int.Star
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Zify
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics] }

/-!
# USA Mathematical Olympiad 2020 Problem 2

An empty 2020 × 2020 × 2020 cube is given, and a 2020 × 2020 grid of square
unit cells is drawn on each of its six faces. A beam is a 1 × 1 × 2020
rectangular prism. Several beams are placed inside the cube subject to the
following conditions:

* The two 1 × 1 faces of each beam coincide with unit cells lying on opposite
  faces of the cube. (Hence, there are 3 · 2020² possible positions for a beam.)
* No two beams have intersecting interiors.
* The interiors of each of the four 1 × 2020 faces of each beam touch either a
  face of the cube or the interior of the face of another beam.

What is the smallest positive number of beams that can be placed to satisfy
these conditions?
-/

namespace Usa2020P2

snip begin

/-
## Solution sketch

Answer: 3030 = 3·2020/2 beams.

We model a beam as one of three orientations (`xBeam`, `yBeam`, `zBeam`)
together with the two integer coordinates of its cross-section. The
non-intersection condition becomes a statement about pairs of beams, and the
face-support condition becomes, for each of the four long faces of each beam,
a three-way disjunction: the face lies on the boundary of the cube, or a
parallel neighboring beam of the same orientation supports it, or a beam of
one specific other orientation supports it.

For the lower bound, let `Nx, Ny, Nz` be the numbers of beams of each
orientation.

* If some orientation is missing, say `Nz = 0`, then each of the `n` horizontal
  layers is either completely empty or completely filled: an `xBeam` in a
  layer forces the whole row of `xBeam`s in that layer (induction through the
  face conditions), and likewise for `yBeam`s. Since some beam exists and the
  face conditions propagate between adjacent layers, every layer is filled,
  so at least `n²` beams are needed.
* Otherwise all `Nx, Ny, Nz > 0`. The face conditions in the vertical
  direction propagate the property "layer `k` contains an `xBeam` or a
  `yBeam`" to all layers, so each of the `n` layers contains such a beam and
  `Nx + Ny ≥ n`. By symmetry `Ny + Nz ≥ n` and `Nz + Nx ≥ n`, and summing
  gives `2(Nx + Ny + Nz) ≥ 3n`.

For `n = 2020` both cases give at least 3030 beams.

The construction with 3030 beams places, for each `t = 0, …, 1009`, a
`zBeam` at `(2t, 2t)`, a `yBeam` at `(2t+1, 2t)` and an `xBeam` at
`(2t+1, 2t+1)`, forming a staircase. (This is the construction from the
official solution.)
-/

/-- The three possible orientations of a beam. -/
inductive Dir | X | Y | Z deriving DecidableEq

/-- A beam in an `n × n × n` cube, given by its orientation and the two
coordinates of its cross-section:
* `xBeam j k` occupies `y = j`, `z = k` and spans the `x`-direction;
* `yBeam i k` occupies `x = i`, `z = k` and spans the `y`-direction;
* `zBeam i j` occupies `x = i`, `y = j` and spans the `z`-direction. -/
inductive Beam (n : ℕ)
  | xBeam (j k : Fin n)
  | yBeam (i k : Fin n)
  | zBeam (i j : Fin n)
  deriving DecidableEq

variable {n : ℕ}

namespace Beam

/-- The orientation of a beam. -/
def dir : Beam n → Dir
  | xBeam .. => .X
  | yBeam .. => .Y
  | zBeam .. => .Z

/-- `covers b x y z` means that beam `b` contains the unit cube at
coordinates `(x, y, z)`. -/
def covers : Beam n → Fin n → Fin n → Fin n → Prop
  | xBeam j k => fun _ y z => y = j ∧ z = k
  | yBeam i k => fun x _ z => x = i ∧ z = k
  | zBeam i j => fun x y _ => x = i ∧ y = j

end Beam

open Beam

/-- The non-intersection condition: two distinct beams do not share a unit
cube. -/
def DisjointBeams (S : Finset (Beam n)) : Prop :=
  ∀ b₁ ∈ S, ∀ b₂ ∈ S, (∃ x y z, b₁.covers x y z ∧ b₂.covers x y z) → b₁ = b₂

/-- The four side-face support conditions for `xBeam j k`:
faces at `y = j`, `y = j+1`, `z = k`, `z = k+1`. -/
def xSupp {n : ℕ} (S : Finset (Beam n)) (j k : Fin n) : Prop :=
  (j.val = 0 ∨ (∃ j' : Fin n, j'.val + 1 = j.val ∧ xBeam j' k ∈ S) ∨
      (∃ i' j' : Fin n, j'.val + 1 = j.val ∧ zBeam i' j' ∈ S)) ∧
    (j.val + 1 = n ∨ (∃ j' : Fin n, j'.val = j.val + 1 ∧ xBeam j' k ∈ S) ∨
      (∃ i' j' : Fin n, j'.val = j.val + 1 ∧ zBeam i' j' ∈ S)) ∧
    (k.val = 0 ∨ (∃ k' : Fin n, k'.val + 1 = k.val ∧ xBeam j k' ∈ S) ∨
      (∃ i' k' : Fin n, k'.val + 1 = k.val ∧ yBeam i' k' ∈ S)) ∧
    (k.val + 1 = n ∨ (∃ k' : Fin n, k'.val = k.val + 1 ∧ xBeam j k' ∈ S) ∨
      (∃ i' k' : Fin n, k'.val = k.val + 1 ∧ yBeam i' k' ∈ S))

/-- The four side-face support conditions for `yBeam i k`:
faces at `x = i`, `x = i+1`, `z = k`, `z = k+1`. -/
def ySupp {n : ℕ} (S : Finset (Beam n)) (i k : Fin n) : Prop :=
  (i.val = 0 ∨ (∃ i' : Fin n, i'.val + 1 = i.val ∧ yBeam i' k ∈ S) ∨
      (∃ i' j' : Fin n, i'.val + 1 = i.val ∧ zBeam i' j' ∈ S)) ∧
    (i.val + 1 = n ∨ (∃ i' : Fin n, i'.val = i.val + 1 ∧ yBeam i' k ∈ S) ∨
      (∃ i' j' : Fin n, i'.val = i.val + 1 ∧ zBeam i' j' ∈ S)) ∧
    (k.val = 0 ∨ (∃ k' : Fin n, k'.val + 1 = k.val ∧ yBeam i k' ∈ S) ∨
      (∃ j' k' : Fin n, k'.val + 1 = k.val ∧ xBeam j' k' ∈ S)) ∧
    (k.val + 1 = n ∨ (∃ k' : Fin n, k'.val = k.val + 1 ∧ yBeam i k' ∈ S) ∨
      (∃ j' k' : Fin n, k'.val = k.val + 1 ∧ xBeam j' k' ∈ S))

/-- The four side-face support conditions for `zBeam i j`:
faces at `x = i`, `x = i+1`, `y = j`, `y = j+1`. -/
def zSupp {n : ℕ} (S : Finset (Beam n)) (i j : Fin n) : Prop :=
  (i.val = 0 ∨ (∃ i' : Fin n, i'.val + 1 = i.val ∧ zBeam i' j ∈ S) ∨
      (∃ i' k' : Fin n, i'.val + 1 = i.val ∧ yBeam i' k' ∈ S)) ∧
    (i.val + 1 = n ∨ (∃ i' : Fin n, i'.val = i.val + 1 ∧ zBeam i' j ∈ S) ∨
      (∃ i' k' : Fin n, i'.val = i.val + 1 ∧ yBeam i' k' ∈ S)) ∧
    (j.val = 0 ∨ (∃ j' : Fin n, j'.val + 1 = j.val ∧ zBeam i j' ∈ S) ∨
      (∃ j' k' : Fin n, j'.val + 1 = j.val ∧ xBeam j' k' ∈ S)) ∧
    (j.val + 1 = n ∨ (∃ j' : Fin n, j'.val = j.val + 1 ∧ zBeam i j' ∈ S) ∨
      (∃ j' k' : Fin n, j'.val = j.val + 1 ∧ xBeam j' k' ∈ S))

/-- The face-support condition for every beam in `S`. -/
def Supp (S : Finset (Beam n)) : Prop :=
  (∀ j k, xBeam j k ∈ S → xSupp S j k) ∧
    (∀ i k, yBeam i k ∈ S → ySupp S i k) ∧
    (∀ i j, zBeam i j ∈ S → zSupp S i j)

/-- The `z`-layer of a beam (dummy value for `zBeam`s, which span all
layers). -/
def zLayer : Beam n → Fin n
  | xBeam _ k => k
  | yBeam _ k => k
  | zBeam i _ => i

/-- The `x`-layer of a beam (dummy value for `xBeam`s). -/
def xLayer : Beam n → Fin n
  | xBeam j _ => j
  | yBeam i _ => i
  | zBeam i _ => i

/-- The `y`-layer of a beam (dummy value for `yBeam`s). -/
def yLayer : Beam n → Fin n
  | xBeam j _ => j
  | yBeam i _ => i
  | zBeam _ j => j

/-- A one-dimensional propagation lemma: if a property of positions always
propagates to the left and right neighbors (unless at the boundary), then it
holds everywhere once it holds somewhere. -/
theorem fill1d {n : ℕ} (P : Fin n → Prop)
    (hP : ∀ i, P i → (i.val = 0 ∨ ∃ i', i'.val + 1 = i.val ∧ P i') ∧
      (i.val + 1 = n ∨ ∃ i', i'.val = i.val + 1 ∧ P i'))
    {i₀ : Fin n} (hi₀ : P i₀) (i : Fin n) : P i := by
  have right : ∀ d : ℕ, ∀ (h : i₀.val + d < n), P ⟨i₀.val + d, h⟩ := by
    intro d
    induction d with
    | zero => intro h; simpa using hi₀
    | succ d ih =>
      intro h
      have h1 : i₀.val + d < n := by omega
      obtain ⟨-, hsucc⟩ := hP _ (ih h1)
      rcases hsucc with habs | ⟨i', hi'1, hi'2⟩
      · have habs' : i₀.val + d + 1 = n := habs
        omega
      · have hi'' : i'.val = i₀.val + d + 1 := hi'1
        have e : i' = ⟨i₀.val + (d + 1), h⟩ :=
          Fin.ext (show i'.val = i₀.val + (d + 1) by omega)
        rwa [e] at hi'2
  have left : ∀ d : ℕ, ∀ (h : d ≤ i₀.val), P ⟨i₀.val - d, by omega⟩ := by
    intro d
    induction d with
    | zero => intro h; simpa using hi₀
    | succ d ih =>
      intro h
      have h1 : d ≤ i₀.val := by omega
      obtain ⟨hpred, -⟩ := hP _ (ih h1)
      rcases hpred with habs | ⟨i', hi'1, hi'2⟩
      · have habs' : i₀.val - d = 0 := habs
        omega
      · have hi'' : i'.val + 1 = i₀.val - d := hi'1
        have e : i' = ⟨i₀.val - (d + 1), by omega⟩ :=
          Fin.ext (show i'.val = i₀.val - (d + 1) by omega)
        rwa [e] at hi'2
  rcases le_total i₀.val i.val with hle | hle
  · have h2 := right (i.val - i₀.val) (by omega)
    have e : ⟨i₀.val + (i.val - i₀.val), by omega⟩ = i :=
      Fin.ext (show i₀.val + (i.val - i₀.val) = i.val by omega)
    rwa [e] at h2
  · have h2 := left (i₀.val - i.val) (by omega)
    have e : ⟨i₀.val - (i₀.val - i.val), by omega⟩ = i :=
      Fin.ext (show i₀.val - (i₀.val - i.val) = i.val by omega)
    rwa [e] at h2

/-- An `xBeam` in a cube without `zBeam`s fills its whole row along `y`. -/
theorem fill_xBeam_y {n : ℕ} {S : Finset (Beam n)} (hS : Supp S)
    (hz : ∀ i j, zBeam i j ∉ S) {k j : Fin n} (h : xBeam j k ∈ S) (j' : Fin n) :
    xBeam j' k ∈ S :=
  fill1d (fun j => xBeam j k ∈ S)
    (fun i hi => by
      obtain ⟨h1, h2, -, -⟩ := hS.1 i k hi
      constructor
      · rcases h1 with h0 | ⟨j₀, hj₁, hj₂⟩ | ⟨i', j₀, hj₁, hj₂⟩
        · exact Or.inl h0
        · exact Or.inr ⟨j₀, hj₁, hj₂⟩
        · exact absurd hj₂ (hz i' j₀)
      · rcases h2 with h0 | ⟨j₀, hj₁, hj₂⟩ | ⟨i', j₀, hj₁, hj₂⟩
        · exact Or.inl h0
        · exact Or.inr ⟨j₀, hj₁, hj₂⟩
        · exact absurd hj₂ (hz i' j₀))
    h j'

/-- A `yBeam` in a cube without `zBeam`s fills its whole column along `x`. -/
theorem fill_yBeam_x {n : ℕ} {S : Finset (Beam n)} (hS : Supp S)
    (hz : ∀ i j, zBeam i j ∉ S) {i k : Fin n} (h : yBeam i k ∈ S) (i' : Fin n) :
    yBeam i' k ∈ S :=
  fill1d (fun i => yBeam i k ∈ S)
    (fun a ha => by
      obtain ⟨h1, h2, -, -⟩ := hS.2.1 a k ha
      constructor
      · rcases h1 with h0 | ⟨i₀, hi₁, hi₂⟩ | ⟨i₀, j₀, hi₁, hi₂⟩
        · exact Or.inl h0
        · exact Or.inr ⟨i₀, hi₁, hi₂⟩
        · exact absurd hi₂ (hz i₀ j₀)
      · rcases h2 with h0 | ⟨i₀, hi₁, hi₂⟩ | ⟨i₀, j₀, hi₁, hi₂⟩
        · exact Or.inl h0
        · exact Or.inr ⟨i₀, hi₁, hi₂⟩
        · exact absurd hi₂ (hz i₀ j₀))
    h i'

/-- A `yBeam` in a cube without `xBeam`s fills its whole column along `z`. -/
theorem fill_yBeam_z {n : ℕ} {S : Finset (Beam n)} (hS : Supp S)
    (hx : ∀ j k, xBeam j k ∉ S) {i k : Fin n} (h : yBeam i k ∈ S) (k' : Fin n) :
    yBeam i k' ∈ S :=
  fill1d (fun k => yBeam i k ∈ S)
    (fun a ha => by
      obtain ⟨-, -, h3, h4⟩ := hS.2.1 i a ha
      constructor
      · rcases h3 with h0 | ⟨k₀, hk₁, hk₂⟩ | ⟨j₀, k₀, hk₁, hk₂⟩
        · exact Or.inl h0
        · exact Or.inr ⟨k₀, hk₁, hk₂⟩
        · exact absurd hk₂ (hx j₀ k₀)
      · rcases h4 with h0 | ⟨k₀, hk₁, hk₂⟩ | ⟨j₀, k₀, hk₁, hk₂⟩
        · exact Or.inl h0
        · exact Or.inr ⟨k₀, hk₁, hk₂⟩
        · exact absurd hk₂ (hx j₀ k₀))
    h k'

/-- An `xBeam` in a cube without `yBeam`s fills its whole row along `z`. -/
theorem fill_xBeam_z {n : ℕ} {S : Finset (Beam n)} (hS : Supp S)
    (hy : ∀ i k, yBeam i k ∉ S) {j k : Fin n} (h : xBeam j k ∈ S) (k' : Fin n) :
    xBeam j k' ∈ S :=
  fill1d (fun k => xBeam j k ∈ S)
    (fun a ha => by
      obtain ⟨-, -, h3, h4⟩ := hS.1 j a ha
      constructor
      · rcases h3 with h0 | ⟨k₀, hk₁, hk₂⟩ | ⟨i₀, k₀, hk₁, hk₂⟩
        · exact Or.inl h0
        · exact Or.inr ⟨k₀, hk₁, hk₂⟩
        · exact absurd hk₂ (hy i₀ k₀)
      · rcases h4 with h0 | ⟨k₀, hk₁, hk₂⟩ | ⟨i₀, k₀, hk₁, hk₂⟩
        · exact Or.inl h0
        · exact Or.inr ⟨k₀, hk₁, hk₂⟩
        · exact absurd hk₂ (hy i₀ k₀))
    h k'

/-- A `zBeam` in a cube without `yBeam`s fills its whole row along `x`. -/
theorem fill_zBeam_x {n : ℕ} {S : Finset (Beam n)} (hS : Supp S)
    (hy : ∀ i k, yBeam i k ∉ S) {i j : Fin n} (h : zBeam i j ∈ S) (i' : Fin n) :
    zBeam i' j ∈ S :=
  fill1d (fun i => zBeam i j ∈ S)
    (fun a ha => by
      obtain ⟨h1, h2, -, -⟩ := hS.2.2 a j ha
      constructor
      · rcases h1 with h0 | ⟨i₀, hi₁, hi₂⟩ | ⟨i₀, k₀, hi₁, hi₂⟩
        · exact Or.inl h0
        · exact Or.inr ⟨i₀, hi₁, hi₂⟩
        · exact absurd hi₂ (hy i₀ k₀)
      · rcases h2 with h0 | ⟨i₀, hi₁, hi₂⟩ | ⟨i₀, k₀, hi₁, hi₂⟩
        · exact Or.inl h0
        · exact Or.inr ⟨i₀, hi₁, hi₂⟩
        · exact absurd hi₂ (hy i₀ k₀))
    h i'

/-- A `zBeam` in a cube without `xBeam`s fills its whole row along `y`. -/
theorem fill_zBeam_y {n : ℕ} {S : Finset (Beam n)} (hS : Supp S)
    (hx : ∀ j k, xBeam j k ∉ S) {i j : Fin n} (h : zBeam i j ∈ S) (j' : Fin n) :
    zBeam i j' ∈ S :=
  fill1d (fun j => zBeam i j ∈ S)
    (fun a ha => by
      obtain ⟨-, -, h3, h4⟩ := hS.2.2 i a ha
      constructor
      · rcases h3 with h0 | ⟨j₀, hj₁, hj₂⟩ | ⟨j₀, k₀, hj₁, hj₂⟩
        · exact Or.inl h0
        · exact Or.inr ⟨j₀, hj₁, hj₂⟩
        · exact absurd hj₂ (hx j₀ k₀)
      · rcases h4 with h0 | ⟨j₀, hj₁, hj₂⟩ | ⟨j₀, k₀, hj₁, hj₂⟩
        · exact Or.inl h0
        · exact Or.inr ⟨j₀, hj₁, hj₂⟩
        · exact absurd hj₂ (hx j₀ k₀))
    h j'

/-- Layer `k` (in the `z`-direction) is completely filled. -/
def zFull (S : Finset (Beam n)) (k : Fin n) : Prop :=
  ∀ i j, xBeam j k ∈ S ∨ yBeam i k ∈ S

/-- Layer `i` (in the `x`-direction) is completely filled. -/
def xFull (S : Finset (Beam n)) (i : Fin n) : Prop :=
  ∀ k j, yBeam i k ∈ S ∨ zBeam i j ∈ S

/-- Layer `j` (in the `y`-direction) is completely filled. -/
def yFull (S : Finset (Beam n)) (j : Fin n) : Prop :=
  ∀ k i, xBeam j k ∈ S ∨ zBeam i j ∈ S

theorem zFull_of_mem {n : ℕ} {S : Finset (Beam n)} (hS : Supp S)
    (hz : ∀ i j, zBeam i j ∉ S) {b : Beam n} (hb : b ∈ S) : zFull S (zLayer b) := by
  cases b with
  | xBeam j k => exact fun i j' => Or.inl (fill_xBeam_y hS hz hb j')
  | yBeam i k => exact fun i' j => Or.inr (fill_yBeam_x hS hz hb i')
  | zBeam i j => exact absurd hb (hz i j)

theorem xFull_of_mem {n : ℕ} {S : Finset (Beam n)} (hS : Supp S)
    (hx : ∀ j k, xBeam j k ∉ S) {b : Beam n} (hb : b ∈ S) : xFull S (xLayer b) := by
  cases b with
  | xBeam j k => exact absurd hb (hx j k)
  | yBeam i k => exact fun k' j => Or.inl (fill_yBeam_z hS hx hb k')
  | zBeam i j => exact fun k j' => Or.inr (fill_zBeam_y hS hx hb j')

theorem yFull_of_mem {n : ℕ} {S : Finset (Beam n)} (hS : Supp S)
    (hy : ∀ i k, yBeam i k ∉ S) {b : Beam n} (hb : b ∈ S) : yFull S (yLayer b) := by
  cases b with
  | xBeam j k => exact fun k' i => Or.inl (fill_xBeam_z hS hy hb k')
  | yBeam i k => exact absurd hb (hy i k)
  | zBeam i j => exact fun k i' => Or.inr (fill_zBeam_x hS hy hb i')

theorem zFull_step {n : ℕ} (hn : 0 < n) {S : Finset (Beam n)} (hS : Supp S)
    (hz : ∀ i j, zBeam i j ∉ S) (k : Fin n) (hk : zFull S k) :
    (k.val = 0 ∨ ∃ k', k'.val + 1 = k.val ∧ zFull S k') ∧
      (k.val + 1 = n ∨ ∃ k', k'.val = k.val + 1 ∧ zFull S k') := by
  obtain h1 | h1 := hk ⟨0, hn⟩ ⟨0, hn⟩
  · obtain ⟨-, -, h3, h4⟩ := hS.1 _ _ h1
    constructor
    · rcases h3 with h0 | ⟨k', hk'1, hk'2⟩ | ⟨i', k', hk'1, hk'2⟩
      · exact Or.inl h0
      · exact Or.inr ⟨k', hk'1, fun i j => Or.inl (fill_xBeam_y hS hz hk'2 j)⟩
      · exact Or.inr ⟨k', hk'1, fun i j => Or.inr (fill_yBeam_x hS hz hk'2 i)⟩
    · rcases h4 with h0 | ⟨k', hk'1, hk'2⟩ | ⟨i', k', hk'1, hk'2⟩
      · exact Or.inl h0
      · exact Or.inr ⟨k', hk'1, fun i j => Or.inl (fill_xBeam_y hS hz hk'2 j)⟩
      · exact Or.inr ⟨k', hk'1, fun i j => Or.inr (fill_yBeam_x hS hz hk'2 i)⟩
  · obtain ⟨-, -, h3, h4⟩ := hS.2.1 _ _ h1
    constructor
    · rcases h3 with h0 | ⟨k', hk'1, hk'2⟩ | ⟨j', k', hk'1, hk'2⟩
      · exact Or.inl h0
      · exact Or.inr ⟨k', hk'1, fun i j => Or.inr (fill_yBeam_x hS hz hk'2 i)⟩
      · exact Or.inr ⟨k', hk'1, fun i j => Or.inl (fill_xBeam_y hS hz hk'2 j)⟩
    · rcases h4 with h0 | ⟨k', hk'1, hk'2⟩ | ⟨j', k', hk'1, hk'2⟩
      · exact Or.inl h0
      · exact Or.inr ⟨k', hk'1, fun i j => Or.inr (fill_yBeam_x hS hz hk'2 i)⟩
      · exact Or.inr ⟨k', hk'1, fun i j => Or.inl (fill_xBeam_y hS hz hk'2 j)⟩

theorem xFull_step {n : ℕ} (hn : 0 < n) {S : Finset (Beam n)} (hS : Supp S)
    (hx : ∀ j k, xBeam j k ∉ S) (i : Fin n) (hi : xFull S i) :
    (i.val = 0 ∨ ∃ i', i'.val + 1 = i.val ∧ xFull S i') ∧
      (i.val + 1 = n ∨ ∃ i', i'.val = i.val + 1 ∧ xFull S i') := by
  obtain h1 | h1 := hi ⟨0, hn⟩ ⟨0, hn⟩
  · obtain ⟨h1', h2', -, -⟩ := hS.2.1 _ _ h1
    constructor
    · rcases h1' with h0 | ⟨i', hi'1, hi'2⟩ | ⟨i', j', hi'1, hi'2⟩
      · exact Or.inl h0
      · exact Or.inr ⟨i', hi'1, fun k j => Or.inl (fill_yBeam_z hS hx hi'2 k)⟩
      · exact Or.inr ⟨i', hi'1, fun k j => Or.inr (fill_zBeam_y hS hx hi'2 j)⟩
    · rcases h2' with h0 | ⟨i', hi'1, hi'2⟩ | ⟨i', j', hi'1, hi'2⟩
      · exact Or.inl h0
      · exact Or.inr ⟨i', hi'1, fun k j => Or.inl (fill_yBeam_z hS hx hi'2 k)⟩
      · exact Or.inr ⟨i', hi'1, fun k j => Or.inr (fill_zBeam_y hS hx hi'2 j)⟩
  · obtain ⟨h1', h2', -, -⟩ := hS.2.2 _ _ h1
    constructor
    · rcases h1' with h0 | ⟨i', hi'1, hi'2⟩ | ⟨i', k', hi'1, hi'2⟩
      · exact Or.inl h0
      · exact Or.inr ⟨i', hi'1, fun k j => Or.inr (fill_zBeam_y hS hx hi'2 j)⟩
      · exact Or.inr ⟨i', hi'1, fun k j => Or.inl (fill_yBeam_z hS hx hi'2 k)⟩
    · rcases h2' with h0 | ⟨i', hi'1, hi'2⟩ | ⟨i', k', hi'1, hi'2⟩
      · exact Or.inl h0
      · exact Or.inr ⟨i', hi'1, fun k j => Or.inr (fill_zBeam_y hS hx hi'2 j)⟩
      · exact Or.inr ⟨i', hi'1, fun k j => Or.inl (fill_yBeam_z hS hx hi'2 k)⟩

theorem yFull_step {n : ℕ} (hn : 0 < n) {S : Finset (Beam n)} (hS : Supp S)
    (hy : ∀ i k, yBeam i k ∉ S) (j : Fin n) (hj : yFull S j) :
    (j.val = 0 ∨ ∃ j', j'.val + 1 = j.val ∧ yFull S j') ∧
      (j.val + 1 = n ∨ ∃ j', j'.val = j.val + 1 ∧ yFull S j') := by
  obtain h1 | h1 := hj ⟨0, hn⟩ ⟨0, hn⟩
  · obtain ⟨h1', h2', -, -⟩ := hS.1 _ _ h1
    constructor
    · rcases h1' with h0 | ⟨j', hj'1, hj'2⟩ | ⟨i', j', hj'1, hj'2⟩
      · exact Or.inl h0
      · exact Or.inr ⟨j', hj'1, fun k i => Or.inl (fill_xBeam_z hS hy hj'2 k)⟩
      · exact Or.inr ⟨j', hj'1, fun k i => Or.inr (fill_zBeam_x hS hy hj'2 i)⟩
    · rcases h2' with h0 | ⟨j', hj'1, hj'2⟩ | ⟨i', j', hj'1, hj'2⟩
      · exact Or.inl h0
      · exact Or.inr ⟨j', hj'1, fun k i => Or.inl (fill_xBeam_z hS hy hj'2 k)⟩
      · exact Or.inr ⟨j', hj'1, fun k i => Or.inr (fill_zBeam_x hS hy hj'2 i)⟩
  · obtain ⟨-, -, h3', h4'⟩ := hS.2.2 _ _ h1
    constructor
    · rcases h3' with h0 | ⟨j', hj'1, hj'2⟩ | ⟨j', k', hj'1, hj'2⟩
      · exact Or.inl h0
      · exact Or.inr ⟨j', hj'1, fun k i => Or.inr (fill_zBeam_x hS hy hj'2 i)⟩
      · exact Or.inr ⟨j', hj'1, fun k i => Or.inl (fill_xBeam_z hS hy hj'2 k)⟩
    · rcases h4' with h0 | ⟨j', hj'1, hj'2⟩ | ⟨j', k', hj'1, hj'2⟩
      · exact Or.inl h0
      · exact Or.inr ⟨j', hj'1, fun k i => Or.inr (fill_zBeam_x hS hy hj'2 i)⟩
      · exact Or.inr ⟨j', hj'1, fun k i => Or.inl (fill_xBeam_z hS hy hj'2 k)⟩

theorem zFull_all {n : ℕ} (hn : 0 < n) {S : Finset (Beam n)} (hS : Supp S)
    (hz : ∀ i j, zBeam i j ∉ S) (hne : S.Nonempty) : ∀ k, zFull S k := by
  obtain ⟨b, hb⟩ := hne
  exact fun k =>
    fill1d (zFull S) (fun i hi => zFull_step hn hS hz i hi) (zFull_of_mem hS hz hb) k

theorem xFull_all {n : ℕ} (hn : 0 < n) {S : Finset (Beam n)} (hS : Supp S)
    (hx : ∀ j k, xBeam j k ∉ S) (hne : S.Nonempty) : ∀ i, xFull S i := by
  obtain ⟨b, hb⟩ := hne
  exact fun i =>
    fill1d (xFull S) (fun a ha => xFull_step hn hS hx a ha) (xFull_of_mem hS hx hb) i

theorem yFull_all {n : ℕ} (hn : 0 < n) {S : Finset (Beam n)} (hS : Supp S)
    (hy : ∀ i k, yBeam i k ∉ S) (hne : S.Nonempty) : ∀ j, yFull S j := by
  obtain ⟨b, hb⟩ := hne
  exact fun j =>
    fill1d (yFull S) (fun a ha => yFull_step hn hS hy a ha) (yFull_of_mem hS hy hb) j

theorem card_zLayer (_hn : 0 < n) {S : Finset (Beam n)}
    (_hz : ∀ i j, zBeam i j ∉ S) (k : Fin n) (hk : zFull S k) :
    n ≤ (S.filter fun b => zLayer b = k).card := by
  classical
  by_cases hJ : ∀ j, xBeam j k ∈ S
  · have hsub : (Finset.univ.image fun j => xBeam j k) ⊆ S.filter (fun b => zLayer b = k) := by
      intro b hb
      rw [Finset.mem_image] at hb
      obtain ⟨j, -, rfl⟩ := hb
      rw [Finset.mem_filter]
      exact ⟨hJ j, rfl⟩
    calc n = (Finset.univ.image fun j => xBeam j k).card := by
          rw [Finset.card_image_of_injOn (fun a _ b _ h => (Beam.xBeam.inj h).1),
            Finset.card_univ, Fintype.card_fin]
      _ ≤ (S.filter fun b => zLayer b = k).card := Finset.card_le_card hsub
  · push Not at hJ
    obtain ⟨j₀, hj₀⟩ := hJ
    have hI : ∀ i, yBeam i k ∈ S := fun i => by
      obtain h | h := hk i j₀
      · exact absurd h hj₀
      · exact h
    have hsub : (Finset.univ.image fun i => yBeam i k) ⊆ S.filter (fun b => zLayer b = k) := by
      intro b hb
      rw [Finset.mem_image] at hb
      obtain ⟨i, -, rfl⟩ := hb
      rw [Finset.mem_filter]
      exact ⟨hI i, rfl⟩
    calc n = (Finset.univ.image fun i => yBeam i k).card := by
          rw [Finset.card_image_of_injOn (fun a _ b _ h => (Beam.yBeam.inj h).1),
            Finset.card_univ, Fintype.card_fin]
      _ ≤ (S.filter fun b => zLayer b = k).card := Finset.card_le_card hsub

theorem card_xLayer (_hn : 0 < n) {S : Finset (Beam n)}
    (_hx : ∀ j k, xBeam j k ∉ S) (i : Fin n) (hi : xFull S i) :
    n ≤ (S.filter fun b => xLayer b = i).card := by
  classical
  by_cases hI : ∀ k, yBeam i k ∈ S
  · have hsub : (Finset.univ.image fun k => yBeam i k) ⊆ S.filter (fun b => xLayer b = i) := by
      intro b hb
      rw [Finset.mem_image] at hb
      obtain ⟨k, -, rfl⟩ := hb
      rw [Finset.mem_filter]
      exact ⟨hI k, rfl⟩
    calc n = (Finset.univ.image fun k => yBeam i k).card := by
          rw [Finset.card_image_of_injOn (fun a _ b _ h => (Beam.yBeam.inj h).2),
            Finset.card_univ, Fintype.card_fin]
      _ ≤ (S.filter fun b => xLayer b = i).card := Finset.card_le_card hsub
  · push Not at hI
    obtain ⟨k₀, hk₀⟩ := hI
    have hJ : ∀ j, zBeam i j ∈ S := fun j => by
      obtain h | h := hi k₀ j
      · exact absurd h hk₀
      · exact h
    have hsub : (Finset.univ.image fun j => zBeam i j) ⊆ S.filter (fun b => xLayer b = i) := by
      intro b hb
      rw [Finset.mem_image] at hb
      obtain ⟨j, -, rfl⟩ := hb
      rw [Finset.mem_filter]
      exact ⟨hJ j, rfl⟩
    calc n = (Finset.univ.image fun j => zBeam i j).card := by
          rw [Finset.card_image_of_injOn (fun a _ b _ h => (Beam.zBeam.inj h).2),
            Finset.card_univ, Fintype.card_fin]
      _ ≤ (S.filter fun b => xLayer b = i).card := Finset.card_le_card hsub

theorem card_yLayer (_hn : 0 < n) {S : Finset (Beam n)}
    (_hy : ∀ i k, yBeam i k ∉ S) (j : Fin n) (hj : yFull S j) :
    n ≤ (S.filter fun b => yLayer b = j).card := by
  classical
  by_cases hJ : ∀ k, xBeam j k ∈ S
  · have hsub : (Finset.univ.image fun k => xBeam j k) ⊆ S.filter (fun b => yLayer b = j) := by
      intro b hb
      rw [Finset.mem_image] at hb
      obtain ⟨k, -, rfl⟩ := hb
      rw [Finset.mem_filter]
      exact ⟨hJ k, rfl⟩
    calc n = (Finset.univ.image fun k => xBeam j k).card := by
          rw [Finset.card_image_of_injOn (fun a _ b _ h => (Beam.xBeam.inj h).2),
            Finset.card_univ, Fintype.card_fin]
      _ ≤ (S.filter fun b => yLayer b = j).card := Finset.card_le_card hsub
  · push Not at hJ
    obtain ⟨k₀, hk₀⟩ := hJ
    have hI : ∀ i, zBeam i j ∈ S := fun i => by
      obtain h | h := hj k₀ i
      · exact absurd h hk₀
      · exact h
    have hsub : (Finset.univ.image fun i => zBeam i j) ⊆ S.filter (fun b => yLayer b = j) := by
      intro b hb
      rw [Finset.mem_image] at hb
      obtain ⟨i, -, rfl⟩ := hb
      rw [Finset.mem_filter]
      exact ⟨hI i, rfl⟩
    calc n = (Finset.univ.image fun i => zBeam i j).card := by
          rw [Finset.card_image_of_injOn (fun a _ b _ h => (Beam.zBeam.inj h).1),
            Finset.card_univ, Fintype.card_fin]
      _ ≤ (S.filter fun b => yLayer b = j).card := Finset.card_le_card hsub

/-- If there are no `zBeam`s, every layer is filled and `n² ≤ S.card`. -/
theorem card_ge_sq_of_no_zBeam {n : ℕ} (hn : 0 < n) {S : Finset (Beam n)} (hS : Supp S)
    (hz : ∀ i j, zBeam i j ∉ S) (hne : S.Nonempty) : n * n ≤ S.card := by
  classical
  have hall : ∀ k : Fin n, zFull S k := zFull_all hn hS hz hne
  rw [Finset.card_eq_sum_card_fiberwise (f := zLayer) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)]
  have h2 : (∑ _k : Fin n, n) = n * n := by
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [← h2]
  exact Finset.sum_le_sum fun k _ => card_zLayer hn hz k (hall k)

/-- If there are no `xBeam`s, every layer is filled and `n² ≤ S.card`. -/
theorem card_ge_sq_of_no_xBeam {n : ℕ} (hn : 0 < n) {S : Finset (Beam n)} (hS : Supp S)
    (hx : ∀ j k, xBeam j k ∉ S) (hne : S.Nonempty) : n * n ≤ S.card := by
  classical
  have hall : ∀ i : Fin n, xFull S i := xFull_all hn hS hx hne
  rw [Finset.card_eq_sum_card_fiberwise (f := xLayer) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)]
  have h2 : (∑ _i : Fin n, n) = n * n := by
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [← h2]
  exact Finset.sum_le_sum fun i _ => card_xLayer hn hx i (hall i)

/-- If there are no `yBeam`s, every layer is filled and `n² ≤ S.card`. -/
theorem card_ge_sq_of_no_yBeam {n : ℕ} (hn : 0 < n) {S : Finset (Beam n)} (hS : Supp S)
    (hy : ∀ i k, yBeam i k ∉ S) (hne : S.Nonempty) : n * n ≤ S.card := by
  classical
  have hall : ∀ j : Fin n, yFull S j := yFull_all hn hS hy hne
  rw [Finset.card_eq_sum_card_fiberwise (f := yLayer) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)]
  have h2 : (∑ _j : Fin n, n) = n * n := by
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [← h2]
  exact Finset.sum_le_sum fun j _ => card_yLayer hn hy j (hall j)

theorem card_filter_ne_z {n : ℕ} (S : Finset (Beam n)) :
    (S.filter fun b => b.dir ≠ .Z).card =
      (S.filter fun b => b.dir = .X).card + (S.filter fun b => b.dir = .Y).card := by
  classical
  have disj : Disjoint (S.filter fun b => b.dir = .X) (S.filter fun b => b.dir = .Y) := by
    rw [Finset.disjoint_left]
    intro b hb1 hb2
    rw [Finset.mem_filter] at hb1 hb2
    rw [hb1.2] at hb2
    exact absurd hb2.2 (by decide)
  rw [← Finset.card_union_of_disjoint disj]
  congr 1
  rw [← Finset.filter_or]
  apply Finset.filter_congr
  intro b _
  cases h : b.dir <;> simp

theorem card_filter_ne_x {n : ℕ} (S : Finset (Beam n)) :
    (S.filter fun b => b.dir ≠ .X).card =
      (S.filter fun b => b.dir = .Y).card + (S.filter fun b => b.dir = .Z).card := by
  classical
  have disj : Disjoint (S.filter fun b => b.dir = .Y) (S.filter fun b => b.dir = .Z) := by
    rw [Finset.disjoint_left]
    intro b hb1 hb2
    rw [Finset.mem_filter] at hb1 hb2
    rw [hb1.2] at hb2
    exact absurd hb2.2 (by decide)
  rw [← Finset.card_union_of_disjoint disj]
  congr 1
  rw [← Finset.filter_or]
  apply Finset.filter_congr
  intro b _
  cases h : b.dir <;> simp

theorem card_filter_ne_y {n : ℕ} (S : Finset (Beam n)) :
    (S.filter fun b => b.dir ≠ .Y).card =
      (S.filter fun b => b.dir = .Z).card + (S.filter fun b => b.dir = .X).card := by
  classical
  have disj : Disjoint (S.filter fun b => b.dir = .Z) (S.filter fun b => b.dir = .X) := by
    rw [Finset.disjoint_left]
    intro b hb1 hb2
    rw [Finset.mem_filter] at hb1 hb2
    rw [hb1.2] at hb2
    exact absurd hb2.2 (by decide)
  rw [← Finset.card_union_of_disjoint disj]
  congr 1
  rw [← Finset.filter_or]
  apply Finset.filter_congr
  intro b _
  cases h : b.dir <;> simp

/-- If some beam is not a `zBeam`, every `z`-layer contains an `xBeam` or a
`yBeam`, hence `n ≤ Nx + Ny`. -/
theorem n_le_of_mem_nonZ {n : ℕ} (_hn : 0 < n) {S : Finset (Beam n)} (hS : Supp S)
    (hxy : ∃ b ∈ S, b.dir ≠ .Z) :
    n ≤ (S.filter fun b => b.dir = .X).card + (S.filter fun b => b.dir = .Y).card := by
  classical
  have step : ∀ k : Fin n, (∃ b ∈ S, b.dir ≠ .Z ∧ zLayer b = k) →
      (k.val = 0 ∨ ∃ k', k'.val + 1 = k.val ∧ ∃ b ∈ S, b.dir ≠ .Z ∧ zLayer b = k') ∧
        (k.val + 1 = n ∨ ∃ k', k'.val = k.val + 1 ∧ ∃ b ∈ S, b.dir ≠ .Z ∧ zLayer b = k') := by
    intro k ⟨b, hb, hd, hkb⟩
    cases b with
    | xBeam j k₀ =>
      change k₀ = k at hkb
      subst hkb
      obtain ⟨-, -, h3, h4⟩ := hS.1 j k₀ hb
      constructor
      · rcases h3 with h0 | ⟨k', hk'1, hk'2⟩ | ⟨i', k', hk'1, hk'2⟩
        · exact Or.inl h0
        · exact Or.inr ⟨k', hk'1, xBeam j k', hk'2, by simp [Beam.dir], rfl⟩
        · exact Or.inr ⟨k', hk'1, yBeam i' k', hk'2, by simp [Beam.dir], rfl⟩
      · rcases h4 with h0 | ⟨k', hk'1, hk'2⟩ | ⟨i', k', hk'1, hk'2⟩
        · exact Or.inl h0
        · exact Or.inr ⟨k', hk'1, xBeam j k', hk'2, by simp [Beam.dir], rfl⟩
        · exact Or.inr ⟨k', hk'1, yBeam i' k', hk'2, by simp [Beam.dir], rfl⟩
    | yBeam i k₀ =>
      change k₀ = k at hkb
      subst hkb
      obtain ⟨-, -, h3, h4⟩ := hS.2.1 i k₀ hb
      constructor
      · rcases h3 with h0 | ⟨k', hk'1, hk'2⟩ | ⟨j', k', hk'1, hk'2⟩
        · exact Or.inl h0
        · exact Or.inr ⟨k', hk'1, yBeam i k', hk'2, by simp [Beam.dir], rfl⟩
        · exact Or.inr ⟨k', hk'1, xBeam j' k', hk'2, by simp [Beam.dir], rfl⟩
      · rcases h4 with h0 | ⟨k', hk'1, hk'2⟩ | ⟨j', k', hk'1, hk'2⟩
        · exact Or.inl h0
        · exact Or.inr ⟨k', hk'1, yBeam i k', hk'2, by simp [Beam.dir], rfl⟩
        · exact Or.inr ⟨k', hk'1, xBeam j' k', hk'2, by simp [Beam.dir], rfl⟩
    | zBeam i j => exact absurd rfl hd
  obtain ⟨b₀, hb₀, hd₀⟩ := hxy
  have hlayers : ∀ k : Fin n, ∃ b ∈ S, b.dir ≠ .Z ∧ zLayer b = k := fun k =>
    fill1d (fun k => ∃ b ∈ S, b.dir ≠ .Z ∧ zLayer b = k) step ⟨b₀, hb₀, hd₀, rfl⟩ k
  have hfiber : ∀ k : Fin n, 1 ≤ ((S.filter fun b => b.dir ≠ .Z).filter
      fun b => zLayer b = k).card := by
    intro k
    obtain ⟨b, hb, hd, hkb⟩ := hlayers k
    exact Finset.card_pos.mpr ⟨b, by rw [Finset.mem_filter, Finset.mem_filter]; exact ⟨⟨hb, hd⟩, hkb⟩⟩
  have h2 : n ≤ (S.filter fun b => b.dir ≠ .Z).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := zLayer) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)]
    calc n = ∑ _k : Fin n, 1 := by
          simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      _ ≤ ∑ k : Fin n, ((S.filter fun b => b.dir ≠ .Z).filter fun b => zLayer b = k).card :=
        Finset.sum_le_sum fun k _ => hfiber k
  rwa [card_filter_ne_z] at h2

/-- If some beam is not an `xBeam`, every `x`-layer contains a `yBeam` or a
`zBeam`, hence `n ≤ Ny + Nz`. -/
theorem n_le_of_mem_nonX {n : ℕ} (_hn : 0 < n) {S : Finset (Beam n)} (hS : Supp S)
    (hxy : ∃ b ∈ S, b.dir ≠ .X) :
    n ≤ (S.filter fun b => b.dir = .Y).card + (S.filter fun b => b.dir = .Z).card := by
  classical
  have step : ∀ i : Fin n, (∃ b ∈ S, b.dir ≠ .X ∧ xLayer b = i) →
      (i.val = 0 ∨ ∃ i', i'.val + 1 = i.val ∧ ∃ b ∈ S, b.dir ≠ .X ∧ xLayer b = i') ∧
        (i.val + 1 = n ∨ ∃ i', i'.val = i.val + 1 ∧ ∃ b ∈ S, b.dir ≠ .X ∧ xLayer b = i') := by
    intro i ⟨b, hb, hd, hib⟩
    cases b with
    | xBeam j k => exact absurd rfl hd
    | yBeam i₀ k =>
      change i₀ = i at hib
      subst hib
      obtain ⟨h1, h2, -, -⟩ := hS.2.1 i₀ k hb
      constructor
      · rcases h1 with h0 | ⟨i', hi'1, hi'2⟩ | ⟨i', j', hi'1, hi'2⟩
        · exact Or.inl h0
        · exact Or.inr ⟨i', hi'1, yBeam i' k, hi'2, by simp [Beam.dir], rfl⟩
        · exact Or.inr ⟨i', hi'1, zBeam i' j', hi'2, by simp [Beam.dir], rfl⟩
      · rcases h2 with h0 | ⟨i', hi'1, hi'2⟩ | ⟨i', j', hi'1, hi'2⟩
        · exact Or.inl h0
        · exact Or.inr ⟨i', hi'1, yBeam i' k, hi'2, by simp [Beam.dir], rfl⟩
        · exact Or.inr ⟨i', hi'1, zBeam i' j', hi'2, by simp [Beam.dir], rfl⟩
    | zBeam i₀ j =>
      change i₀ = i at hib
      subst hib
      obtain ⟨h1, h2, -, -⟩ := hS.2.2 i₀ j hb
      constructor
      · rcases h1 with h0 | ⟨i', hi'1, hi'2⟩ | ⟨i', k', hi'1, hi'2⟩
        · exact Or.inl h0
        · exact Or.inr ⟨i', hi'1, zBeam i' j, hi'2, by simp [Beam.dir], rfl⟩
        · exact Or.inr ⟨i', hi'1, yBeam i' k', hi'2, by simp [Beam.dir], rfl⟩
      · rcases h2 with h0 | ⟨i', hi'1, hi'2⟩ | ⟨i', k', hi'1, hi'2⟩
        · exact Or.inl h0
        · exact Or.inr ⟨i', hi'1, zBeam i' j, hi'2, by simp [Beam.dir], rfl⟩
        · exact Or.inr ⟨i', hi'1, yBeam i' k', hi'2, by simp [Beam.dir], rfl⟩
  obtain ⟨b₀, hb₀, hd₀⟩ := hxy
  have hlayers : ∀ i : Fin n, ∃ b ∈ S, b.dir ≠ .X ∧ xLayer b = i := fun i =>
    fill1d (fun i => ∃ b ∈ S, b.dir ≠ .X ∧ xLayer b = i) step ⟨b₀, hb₀, hd₀, rfl⟩ i
  have hfiber : ∀ i : Fin n, 1 ≤ ((S.filter fun b => b.dir ≠ .X).filter
      fun b => xLayer b = i).card := by
    intro i
    obtain ⟨b, hb, hd, hib⟩ := hlayers i
    exact Finset.card_pos.mpr ⟨b, by rw [Finset.mem_filter, Finset.mem_filter]; exact ⟨⟨hb, hd⟩, hib⟩⟩
  have h2 : n ≤ (S.filter fun b => b.dir ≠ .X).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := xLayer) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)]
    calc n = ∑ _i : Fin n, 1 := by
          simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      _ ≤ ∑ i : Fin n, ((S.filter fun b => b.dir ≠ .X).filter fun b => xLayer b = i).card :=
        Finset.sum_le_sum fun i _ => hfiber i
  rwa [card_filter_ne_x] at h2

/-- If some beam is not a `yBeam`, every `y`-layer contains a `zBeam` or an
`xBeam`, hence `n ≤ Nz + Nx`. -/
theorem n_le_of_mem_nonY {n : ℕ} (_hn : 0 < n) {S : Finset (Beam n)} (hS : Supp S)
    (hxy : ∃ b ∈ S, b.dir ≠ .Y) :
    n ≤ (S.filter fun b => b.dir = .Z).card + (S.filter fun b => b.dir = .X).card := by
  classical
  have step : ∀ j : Fin n, (∃ b ∈ S, b.dir ≠ .Y ∧ yLayer b = j) →
      (j.val = 0 ∨ ∃ j', j'.val + 1 = j.val ∧ ∃ b ∈ S, b.dir ≠ .Y ∧ yLayer b = j') ∧
        (j.val + 1 = n ∨ ∃ j', j'.val = j.val + 1 ∧ ∃ b ∈ S, b.dir ≠ .Y ∧ yLayer b = j') := by
    intro j ⟨b, hb, hd, hjb⟩
    cases b with
    | xBeam j₀ k =>
      change j₀ = j at hjb
      subst hjb
      obtain ⟨h1, h2, -, -⟩ := hS.1 j₀ k hb
      constructor
      · rcases h1 with h0 | ⟨j', hj'1, hj'2⟩ | ⟨i', j', hj'1, hj'2⟩
        · exact Or.inl h0
        · exact Or.inr ⟨j', hj'1, xBeam j' k, hj'2, by simp [Beam.dir], rfl⟩
        · exact Or.inr ⟨j', hj'1, zBeam i' j', hj'2, by simp [Beam.dir], rfl⟩
      · rcases h2 with h0 | ⟨j', hj'1, hj'2⟩ | ⟨i', j', hj'1, hj'2⟩
        · exact Or.inl h0
        · exact Or.inr ⟨j', hj'1, xBeam j' k, hj'2, by simp [Beam.dir], rfl⟩
        · exact Or.inr ⟨j', hj'1, zBeam i' j', hj'2, by simp [Beam.dir], rfl⟩
    | yBeam i k => exact absurd rfl hd
    | zBeam i j₀ =>
      change j₀ = j at hjb
      subst hjb
      obtain ⟨-, -, h3, h4⟩ := hS.2.2 i j₀ hb
      constructor
      · rcases h3 with h0 | ⟨j', hj'1, hj'2⟩ | ⟨j', k', hj'1, hj'2⟩
        · exact Or.inl h0
        · exact Or.inr ⟨j', hj'1, zBeam i j', hj'2, by simp [Beam.dir], rfl⟩
        · exact Or.inr ⟨j', hj'1, xBeam j' k', hj'2, by simp [Beam.dir], rfl⟩
      · rcases h4 with h0 | ⟨j', hj'1, hj'2⟩ | ⟨j', k', hj'1, hj'2⟩
        · exact Or.inl h0
        · exact Or.inr ⟨j', hj'1, zBeam i j', hj'2, by simp [Beam.dir], rfl⟩
        · exact Or.inr ⟨j', hj'1, xBeam j' k', hj'2, by simp [Beam.dir], rfl⟩
  obtain ⟨b₀, hb₀, hd₀⟩ := hxy
  have hlayers : ∀ j : Fin n, ∃ b ∈ S, b.dir ≠ .Y ∧ yLayer b = j := fun j =>
    fill1d (fun j => ∃ b ∈ S, b.dir ≠ .Y ∧ yLayer b = j) step ⟨b₀, hb₀, hd₀, rfl⟩ j
  have hfiber : ∀ j : Fin n, 1 ≤ ((S.filter fun b => b.dir ≠ .Y).filter
      fun b => yLayer b = j).card := by
    intro j
    obtain ⟨b, hb, hd, hjb⟩ := hlayers j
    exact Finset.card_pos.mpr ⟨b, by rw [Finset.mem_filter, Finset.mem_filter]; exact ⟨⟨hb, hd⟩, hjb⟩⟩
  have h2 : n ≤ (S.filter fun b => b.dir ≠ .Y).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := yLayer) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)]
    calc n = ∑ _j : Fin n, 1 := by
          simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      _ ≤ ∑ j : Fin n, ((S.filter fun b => b.dir ≠ .Y).filter fun b => yLayer b = j).card :=
        Finset.sum_le_sum fun j _ => hfiber j
  rwa [card_filter_ne_y] at h2

theorem card_eq_sum_dirs {n : ℕ} (S : Finset (Beam n)) :
    S.card = (S.filter fun b => b.dir = .X).card + (S.filter fun b => b.dir = .Y).card +
      (S.filter fun b => b.dir = .Z).card := by
  classical
  have disj1 : Disjoint (S.filter fun b => b.dir = .X) (S.filter fun b => b.dir = .Y) := by
    rw [Finset.disjoint_left]
    intro b hb1 hb2
    rw [Finset.mem_filter] at hb1 hb2
    rw [hb1.2] at hb2
    exact absurd hb2.2 (by decide)
  have disj2 : Disjoint ((S.filter fun b => b.dir = .X) ∪ (S.filter fun b => b.dir = .Y))
      (S.filter fun b => b.dir = .Z) := by
    rw [Finset.disjoint_left]
    intro b hb1 hb2
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter] at hb1
    rw [Finset.mem_filter] at hb2
    rcases hb1 with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] at hb2 <;> exact absurd hb2.2 (by decide)
  have hunion : (S.filter fun b => b.dir = .X) ∪ (S.filter fun b => b.dir = .Y) ∪
      (S.filter fun b => b.dir = .Z) = S := by
    rw [← Finset.filter_or, ← Finset.filter_or]
    rw [Finset.filter_true_of_mem]
    intro b _
    cases h : b.dir <;> simp
  calc S.card = ((S.filter fun b => b.dir = .X) ∪ (S.filter fun b => b.dir = .Y) ∪
        (S.filter fun b => b.dir = .Z)).card := by rw [hunion]
    _ = (S.filter fun b => b.dir = .X).card + (S.filter fun b => b.dir = .Y).card +
        (S.filter fun b => b.dir = .Z).card := by
        rw [Finset.card_union_of_disjoint disj2, Finset.card_union_of_disjoint disj1]

/-- The lower bound: any supported nonempty configuration has
`3 * n ≤ 2 * S.card`. -/
theorem lower_bound {n : ℕ} (hn : 2 ≤ n) {S : Finset (Beam n)} (hS : Supp S)
    (hne : S.Nonempty) : 3 * n ≤ 2 * S.card := by
  classical
  have hn0 : 0 < n := by omega
  have hn_sq : 3 * n ≤ 2 * (n * n) := by
    have h2 : 2 * n ≤ n * n := Nat.mul_le_mul hn le_rfl
    nlinarith [h2]
  by_cases hz : ∃ i j, zBeam i j ∈ S
  · by_cases hx : ∃ j k, xBeam j k ∈ S
    · by_cases hy : ∃ i k, yBeam i k ∈ S
      · obtain ⟨i, j, hzi⟩ := hz
        obtain ⟨j', k', hxj⟩ := hx
        obtain ⟨i', k'', hyi⟩ := hy
        have h1 := n_le_of_mem_nonZ hn0 hS ⟨xBeam j' k', hxj, by simp [Beam.dir]⟩
        have h2 := n_le_of_mem_nonX hn0 hS ⟨zBeam i j, hzi, by simp [Beam.dir]⟩
        have h3 := n_le_of_mem_nonY hn0 hS ⟨zBeam i j, hzi, by simp [Beam.dir]⟩
        have hcard := card_eq_sum_dirs S
        omega
      · push Not at hy
        have h := card_ge_sq_of_no_yBeam hn0 hS hy hne
        nlinarith [h, hn_sq]
    · push Not at hx
      have h := card_ge_sq_of_no_xBeam hn0 hS hx hne
      nlinarith [h, hn_sq]
  · push Not at hz
    have h := card_ge_sq_of_no_zBeam hn0 hS hz hne
    nlinarith [h, hn_sq]

/-! ## The construction with 3030 beams -/

/-- The `zBeam`s of the construction: `(2t, 2t)` for `t = 0, …, 1009`. -/
def zPart : Finset (Beam 2020) :=
  (Finset.range 1010).attach.image fun t =>
    zBeam ⟨2 * t.val, by have := Finset.mem_range.mp t.property; omega⟩
      ⟨2 * t.val, by have := Finset.mem_range.mp t.property; omega⟩

/-- The `yBeam`s of the construction: `(2t+1, 2t)` for `t = 0, …, 1009`. -/
def yPart : Finset (Beam 2020) :=
  (Finset.range 1010).attach.image fun t =>
    yBeam ⟨2 * t.val + 1, by have := Finset.mem_range.mp t.property; omega⟩
      ⟨2 * t.val, by have := Finset.mem_range.mp t.property; omega⟩

/-- The `xBeam`s of the construction: `(2t+1, 2t+1)` for `t = 0, …, 1009`. -/
def xPart : Finset (Beam 2020) :=
  (Finset.range 1010).attach.image fun t =>
    xBeam ⟨2 * t.val + 1, by have := Finset.mem_range.mp t.property; omega⟩
      ⟨2 * t.val + 1, by have := Finset.mem_range.mp t.property; omega⟩

/-- The construction: 3030 beams forming a staircase. -/
def halfBeams : Finset (Beam 2020) := zPart ∪ yPart ∪ xPart

/-! ### Membership helpers -/

theorem mem_zPart (t : ℕ) (ht : t < 1010) :
    zBeam ⟨2 * t, by omega⟩ ⟨2 * t, by omega⟩ ∈ zPart := by
  rw [zPart, Finset.mem_image]
  exact ⟨⟨t, Finset.mem_range.mpr ht⟩, by simp, rfl⟩

theorem mem_yPart (t : ℕ) (ht : t < 1010) :
    yBeam ⟨2 * t + 1, by omega⟩ ⟨2 * t, by omega⟩ ∈ yPart := by
  rw [yPart, Finset.mem_image]
  exact ⟨⟨t, Finset.mem_range.mpr ht⟩, by simp, rfl⟩

theorem mem_xPart (t : ℕ) (ht : t < 1010) :
    xBeam ⟨2 * t + 1, by omega⟩ ⟨2 * t + 1, by omega⟩ ∈ xPart := by
  rw [xPart, Finset.mem_image]
  exact ⟨⟨t, Finset.mem_range.mpr ht⟩, by simp, rfl⟩

theorem mem_halfBeams_z (t : ℕ) (ht : t < 1010) :
    zBeam ⟨2 * t, by omega⟩ ⟨2 * t, by omega⟩ ∈ halfBeams := by
  rw [halfBeams]
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact mem_zPart t ht

theorem mem_halfBeams_y (t : ℕ) (ht : t < 1010) :
    yBeam ⟨2 * t + 1, by omega⟩ ⟨2 * t, by omega⟩ ∈ halfBeams := by
  rw [halfBeams]
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact mem_yPart t ht

theorem mem_halfBeams_x (t : ℕ) (ht : t < 1010) :
    xBeam ⟨2 * t + 1, by omega⟩ ⟨2 * t + 1, by omega⟩ ∈ halfBeams := by
  rw [halfBeams]
  apply Finset.mem_union_right
  exact mem_xPart t ht

theorem of_mem_halfBeams_z {i j : Fin 2020} (h : zBeam i j ∈ halfBeams) :
    ∃ t : ℕ, t < 1010 ∧ i.val = 2 * t ∧ j.val = 2 * t := by
  rw [halfBeams, Finset.mem_union, Finset.mem_union] at h
  rcases h with (h | h) | h
  · rw [zPart, Finset.mem_image] at h
    obtain ⟨a, -, ha⟩ := h
    injection ha with h1 h2
    exact ⟨a.val, Finset.mem_range.mp a.property, (congrArg Fin.val h1).symm,
      (congrArg Fin.val h2).symm⟩
  · rw [yPart, Finset.mem_image] at h
    obtain ⟨_a, -, ha⟩ := h
    cases ha
  · rw [xPart, Finset.mem_image] at h
    obtain ⟨_a, -, ha⟩ := h
    cases ha

theorem of_mem_halfBeams_y {i k : Fin 2020} (h : yBeam i k ∈ halfBeams) :
    ∃ t : ℕ, t < 1010 ∧ i.val = 2 * t + 1 ∧ k.val = 2 * t := by
  rw [halfBeams, Finset.mem_union, Finset.mem_union] at h
  rcases h with (h | h) | h
  · rw [zPart, Finset.mem_image] at h
    obtain ⟨_a, -, ha⟩ := h
    cases ha
  · rw [yPart, Finset.mem_image] at h
    obtain ⟨a, -, ha⟩ := h
    injection ha with h1 h2
    exact ⟨a.val, Finset.mem_range.mp a.property, (congrArg Fin.val h1).symm,
      (congrArg Fin.val h2).symm⟩
  · rw [xPart, Finset.mem_image] at h
    obtain ⟨_a, -, ha⟩ := h
    cases ha

theorem of_mem_halfBeams_x {j k : Fin 2020} (h : xBeam j k ∈ halfBeams) :
    ∃ t : ℕ, t < 1010 ∧ j.val = 2 * t + 1 ∧ k.val = 2 * t + 1 := by
  rw [halfBeams, Finset.mem_union, Finset.mem_union] at h
  rcases h with (h | h) | h
  · rw [zPart, Finset.mem_image] at h
    obtain ⟨_a, -, ha⟩ := h
    cases ha
  · rw [yPart, Finset.mem_image] at h
    obtain ⟨_a, -, ha⟩ := h
    cases ha
  · rw [xPart, Finset.mem_image] at h
    obtain ⟨a, -, ha⟩ := h
    injection ha with h1 h2
    exact ⟨a.val, Finset.mem_range.mp a.property, (congrArg Fin.val h1).symm,
      (congrArg Fin.val h2).symm⟩

/-! ### Cardinalities -/

theorem zPart_card : zPart.card = 1010 := by
  rw [zPart, Finset.card_image_of_injOn ?_, Finset.card_attach, Finset.card_range]
  intro a _ b _ h
  injection h with h1 h2
  have h3 : 2 * a.val = 2 * b.val := congrArg Fin.val h1
  exact Subtype.ext (by omega)

theorem yPart_card : yPart.card = 1010 := by
  rw [yPart, Finset.card_image_of_injOn ?_, Finset.card_attach, Finset.card_range]
  intro a _ b _ h
  injection h with h1 h2
  have h3 : 2 * a.val + 1 = 2 * b.val + 1 := congrArg Fin.val h1
  exact Subtype.ext (by omega)

theorem xPart_card : xPart.card = 1010 := by
  rw [xPart, Finset.card_image_of_injOn ?_, Finset.card_attach, Finset.card_range]
  intro a _ b _ h
  injection h with h1 h2
  have h3 : 2 * a.val + 1 = 2 * b.val + 1 := congrArg Fin.val h1
  exact Subtype.ext (by omega)

theorem halfBeams_card : halfBeams.card = 3030 := by
  have dzy : Disjoint zPart yPart := by
    rw [Finset.disjoint_left]
    intro b hb hy
    rw [zPart, Finset.mem_image] at hb
    rw [yPart, Finset.mem_image] at hy
    obtain ⟨_a, -, rfl⟩ := hb
    obtain ⟨_c, -, hc⟩ := hy
    cases hc
  have dzx : Disjoint zPart xPart := by
    rw [Finset.disjoint_left]
    intro b hb hx
    rw [zPart, Finset.mem_image] at hb
    rw [xPart, Finset.mem_image] at hx
    obtain ⟨_a, -, rfl⟩ := hb
    obtain ⟨_c, -, hc⟩ := hx
    cases hc
  have dyx : Disjoint yPart xPart := by
    rw [Finset.disjoint_left]
    intro b hb hx
    rw [yPart, Finset.mem_image] at hb
    rw [xPart, Finset.mem_image] at hx
    obtain ⟨_a, -, rfl⟩ := hb
    obtain ⟨_c, -, hc⟩ := hx
    cases hc
  have h : Disjoint (zPart ∪ yPart) xPart := Finset.disjoint_union_left.mpr ⟨dzx, dyx⟩
  rw [halfBeams, Finset.card_union_of_disjoint h, Finset.card_union_of_disjoint dzy,
    zPart_card, yPart_card, xPart_card]

theorem halfBeams_nonempty : halfBeams.Nonempty := by
  rw [← Finset.card_pos, halfBeams_card]
  norm_num

/-! ### Disjointness of the construction -/

theorem halfBeams_disjoint : DisjointBeams halfBeams := by
  intro b₁ hb₁ b₂ hb₂ ⟨x, y, z, h1, h2⟩
  rw [halfBeams, Finset.mem_union, Finset.mem_union] at hb₁ hb₂
  rcases hb₁ with (hb₁ | hb₁) | hb₁ <;> rcases hb₂ with (hb₂ | hb₂) | hb₂
  · -- b₁, b₂ both from `zPart`
    rw [zPart, Finset.mem_image] at hb₁ hb₂
    obtain ⟨a₁, -, rfl⟩ := hb₁
    obtain ⟨a₂, -, rfl⟩ := hb₂
    obtain ⟨hx, -⟩ := h1
    obtain ⟨hx2, -⟩ := h2
    have e2 : 2 * a₁.val = 2 * a₂.val := congrArg Fin.val (hx.symm.trans hx2)
    have e : a₁ = a₂ := Subtype.ext (by omega)
    rw [e]
  · -- `zPart` vs `yPart`: shared `x`-coordinate, `2t = 2s+1`
    rw [zPart, Finset.mem_image] at hb₁
    rw [yPart, Finset.mem_image] at hb₂
    obtain ⟨a₁, -, rfl⟩ := hb₁
    obtain ⟨a₂, -, rfl⟩ := hb₂
    obtain ⟨hx, -⟩ := h1
    obtain ⟨hx2, -⟩ := h2
    have e2 : 2 * a₁.val = 2 * a₂.val + 1 := congrArg Fin.val (hx.symm.trans hx2)
    omega
  · -- `zPart` vs `xPart`: shared `y`-coordinate, `2t = 2s+1`
    rw [zPart, Finset.mem_image] at hb₁
    rw [xPart, Finset.mem_image] at hb₂
    obtain ⟨a₁, -, rfl⟩ := hb₁
    obtain ⟨a₂, -, rfl⟩ := hb₂
    obtain ⟨-, hy⟩ := h1
    obtain ⟨hy2, -⟩ := h2
    have e2 : 2 * a₁.val = 2 * a₂.val + 1 := congrArg Fin.val (hy.symm.trans hy2)
    omega
  · -- `yPart` vs `zPart`: shared `x`-coordinate, `2t+1 = 2s`
    rw [yPart, Finset.mem_image] at hb₁
    rw [zPart, Finset.mem_image] at hb₂
    obtain ⟨a₁, -, rfl⟩ := hb₁
    obtain ⟨a₂, -, rfl⟩ := hb₂
    obtain ⟨hx, -⟩ := h1
    obtain ⟨hx2, -⟩ := h2
    have e2 : 2 * a₁.val + 1 = 2 * a₂.val := congrArg Fin.val (hx.symm.trans hx2)
    omega
  · -- b₁, b₂ both from `yPart`
    rw [yPart, Finset.mem_image] at hb₁ hb₂
    obtain ⟨a₁, -, rfl⟩ := hb₁
    obtain ⟨a₂, -, rfl⟩ := hb₂
    obtain ⟨-, hz⟩ := h1
    obtain ⟨-, hz2⟩ := h2
    have e2 : 2 * a₁.val = 2 * a₂.val := congrArg Fin.val (hz.symm.trans hz2)
    have e : a₁ = a₂ := Subtype.ext (by omega)
    rw [e]
  · -- `yPart` vs `xPart`: shared `z`-coordinate, `2t = 2s+1`
    rw [yPart, Finset.mem_image] at hb₁
    rw [xPart, Finset.mem_image] at hb₂
    obtain ⟨a₁, -, rfl⟩ := hb₁
    obtain ⟨a₂, -, rfl⟩ := hb₂
    obtain ⟨-, hz⟩ := h1
    obtain ⟨-, hz2⟩ := h2
    have e2 : 2 * a₁.val = 2 * a₂.val + 1 := congrArg Fin.val (hz.symm.trans hz2)
    omega
  · -- `xPart` vs `zPart`: shared `y`-coordinate, `2t+1 = 2s`
    rw [xPart, Finset.mem_image] at hb₁
    rw [zPart, Finset.mem_image] at hb₂
    obtain ⟨a₁, -, rfl⟩ := hb₁
    obtain ⟨a₂, -, rfl⟩ := hb₂
    obtain ⟨hy, -⟩ := h1
    obtain ⟨-, hy2⟩ := h2
    have e2 : 2 * a₁.val + 1 = 2 * a₂.val := congrArg Fin.val (hy.symm.trans hy2)
    omega
  · -- `xPart` vs `yPart`: shared `z`-coordinate, `2t+1 = 2s`
    rw [xPart, Finset.mem_image] at hb₁
    rw [yPart, Finset.mem_image] at hb₂
    obtain ⟨a₁, -, rfl⟩ := hb₁
    obtain ⟨a₂, -, rfl⟩ := hb₂
    obtain ⟨-, hz⟩ := h1
    obtain ⟨-, hz2⟩ := h2
    have e2 : 2 * a₁.val + 1 = 2 * a₂.val := congrArg Fin.val (hz.symm.trans hz2)
    omega
  · -- b₁, b₂ both from `xPart`
    rw [xPart, Finset.mem_image] at hb₁ hb₂
    obtain ⟨a₁, -, rfl⟩ := hb₁
    obtain ⟨a₂, -, rfl⟩ := hb₂
    obtain ⟨hy, -⟩ := h1
    obtain ⟨hy2, -⟩ := h2
    have e2 : 2 * a₁.val + 1 = 2 * a₂.val + 1 := congrArg Fin.val (hy.symm.trans hy2)
    have e : a₁ = a₂ := Subtype.ext (by omega)
    rw [e]

/-! ### The support conditions -/

theorem halfBeams_supp : Supp halfBeams := by
  refine ⟨?_, ?_, ?_⟩
  · -- `xBeam (2t+1, 2t+1)`
    intro j k hj
    obtain ⟨t, ht, hvj, hvk⟩ := of_mem_halfBeams_x hj
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- face `y = 2t+1` rests on `zBeam (2t, 2t)`
      exact Or.inr (Or.inr ⟨⟨2 * t, by omega⟩, ⟨2 * t, by omega⟩,
        by show 2 * t + 1 = j.val; omega, mem_halfBeams_z t ht⟩)
    · -- face `y = 2t+2`: boundary if `t = 1009`, else `zBeam (2t+2, 2t+2)`
      by_cases htop : t = 1009
      · subst htop
        exact Or.inl (by omega)
      · exact Or.inr (Or.inr ⟨⟨2 * (t + 1), by omega⟩, ⟨2 * (t + 1), by omega⟩,
          by show 2 * (t + 1) = j.val + 1; omega, mem_halfBeams_z (t + 1) (by omega)⟩)
    · -- face `z = 2t+1` rests on `yBeam (2t+1, 2t)`
      exact Or.inr (Or.inr ⟨⟨2 * t + 1, by omega⟩, ⟨2 * t, by omega⟩,
        by show 2 * t + 1 = k.val; omega, mem_halfBeams_y t ht⟩)
    · -- face `z = 2t+2`: boundary if `t = 1009`, else `yBeam (2t+3, 2t+2)`
      by_cases htop : t = 1009
      · subst htop
        exact Or.inl (by omega)
      · exact Or.inr (Or.inr ⟨⟨2 * (t + 1) + 1, by omega⟩, ⟨2 * (t + 1), by omega⟩,
          by show 2 * (t + 1) = k.val + 1; omega, mem_halfBeams_y (t + 1) (by omega)⟩)
  · -- `yBeam (2t+1, 2t)`
    intro i k hj
    obtain ⟨t, ht, hvi, hvk⟩ := of_mem_halfBeams_y hj
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- face `x = 2t+1` rests on `zBeam (2t, 2t)`
      exact Or.inr (Or.inr ⟨⟨2 * t, by omega⟩, ⟨2 * t, by omega⟩,
        by show 2 * t + 1 = i.val; omega, mem_halfBeams_z t ht⟩)
    · -- face `x = 2t+2`: boundary if `t = 1009`, else `zBeam (2t+2, 2t+2)`
      by_cases htop : t = 1009
      · subst htop
        exact Or.inl (by omega)
      · exact Or.inr (Or.inr ⟨⟨2 * (t + 1), by omega⟩, ⟨2 * (t + 1), by omega⟩,
          by show 2 * (t + 1) = i.val + 1; omega, mem_halfBeams_z (t + 1) (by omega)⟩)
    · -- face `z = 2t`: boundary if `t = 0`, else `xBeam (2t-1, 2t-1)`
      by_cases hbot : t = 0
      · subst hbot
        exact Or.inl (by omega)
      · exact Or.inr (Or.inr ⟨⟨2 * (t - 1) + 1, by omega⟩, ⟨2 * (t - 1) + 1, by omega⟩,
          by show 2 * (t - 1) + 1 + 1 = k.val; omega, mem_halfBeams_x (t - 1) (by omega)⟩)
    · -- face `z = 2t+1` rests on `xBeam (2t+1, 2t+1)`
      exact Or.inr (Or.inr ⟨⟨2 * t + 1, by omega⟩, ⟨2 * t + 1, by omega⟩,
        by show 2 * t + 1 = k.val + 1; omega, mem_halfBeams_x t ht⟩)
  · -- `zBeam (2t, 2t)`
    intro i j hj
    obtain ⟨t, ht, hvi, hvj⟩ := of_mem_halfBeams_z hj
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- face `x = 2t`: boundary if `t = 0`, else `yBeam (2t-1, 2t-2)`
      by_cases hbot : t = 0
      · subst hbot
        exact Or.inl (by omega)
      · exact Or.inr (Or.inr ⟨⟨2 * (t - 1) + 1, by omega⟩, ⟨2 * (t - 1), by omega⟩,
          by show 2 * (t - 1) + 1 + 1 = i.val; omega, mem_halfBeams_y (t - 1) (by omega)⟩)
    · -- face `x = 2t+1` rests on `yBeam (2t+1, 2t)`
      exact Or.inr (Or.inr ⟨⟨2 * t + 1, by omega⟩, ⟨2 * t, by omega⟩,
        by show 2 * t + 1 = i.val + 1; omega, mem_halfBeams_y t ht⟩)
    · -- face `y = 2t`: boundary if `t = 0`, else `xBeam (2t-1, 2t-1)`
      by_cases hbot : t = 0
      · subst hbot
        exact Or.inl (by omega)
      · exact Or.inr (Or.inr ⟨⟨2 * (t - 1) + 1, by omega⟩, ⟨2 * (t - 1) + 1, by omega⟩,
          by show 2 * (t - 1) + 1 + 1 = j.val; omega, mem_halfBeams_x (t - 1) (by omega)⟩)
    · -- face `y = 2t+1` rests on `xBeam (2t+1, 2t+1)`
      exact Or.inr (Or.inr ⟨⟨2 * t + 1, by omega⟩, ⟨2 * t + 1, by omega⟩,
        by show 2 * t + 1 = j.val + 1; omega, mem_halfBeams_x t ht⟩)

snip end

determine solution : ℕ := 3030

problem usa2020_p2 :
    IsLeast {m | ∃ S : Finset (Beam 2020), S.Nonempty ∧ DisjointBeams S ∧ Supp S ∧
      S.card = m} solution := by
  constructor
  · exact ⟨halfBeams, halfBeams_nonempty, halfBeams_disjoint, halfBeams_supp, halfBeams_card⟩
  · intro m hm
    obtain ⟨S, hne, -, hsupp, hm⟩ := hm
    have hb := lower_bound (n := 2020) (by norm_num) hsupp hne
    show solution ≤ m
    rw [← hm]
    have : solution = 3030 := rfl
    omega

end Usa2020P2
