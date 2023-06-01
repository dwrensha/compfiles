import Mathlib.Topology.Bases
import Mathlib.Topology.Basic
import Mathlib.Analysis.NormedSpace.Basic
import Mathlib.Tactic.LibrarySearch

-- This is an attempt at be a formalization of
-- https://jcreedcmu.github.io/posts/2023-01-14/

-- I'm not completely sure about what the ideal approach is with
-- respect to lean type classes vs. structures for defining
-- sets-with-structure in this setting.

-- FIXME: The current definition below probably isn't quite right,
-- because the topology on E is not constrained in any way to reflect
-- the vector space structure on E.  I intend to assume E to be a
-- finite-dimensional real vector space, with the usual topology on
-- it.

namespace RigidSpaces

-- A rigid space is a choice of finite-dimensional real vector space E, together with:
-- a set C of "colors" and some additional data and axioms.
class RigidSpace (E : Type) [AddCommGroup E] [TopologicalSpace E] [Module ℝ E] (C : Type) where
  -- For any color, there is a map E → C (a "picture") that describes
  -- how its ℝⁿ-shaped "neighborhood" must be colored.
  dmap : C → E → C
  -- The color at the origin of this "picture" of c must be c itself.
  dzero : ∀ (c : C), dmap c 0 = c
  -- In this "picture", color is invariant under scaling by any
  -- positive constant Λ : ℝ
  dscale : ∀ (Λ : ℝ) (c : C) (v : E), Λ > 0 -> dmap c (Λ • v) = dmap c v
  -- If we "zoom in" enough around any point v in c's picture, it
  -- resembles a translated copy of the picture *of the color* at
  -- point v in c's picture.
  -- 
  -- In other words: around every one of the colored points in c's
  -- picture, there must also be a local neighborhood that is
  -- consistent with their own declared neighborhood-coloring.
  dnabe : ∀ (c : C) (v : E), ∃ (U : Set E), 0 ∈ U ∧ IsOpen U ∧ ∀ u ∈ U, 
          dmap c (v + u) = dmap (dmap c v) u

open RigidSpace

---- FIXME: I didn't seem able to replace uses of dimap with ∘ even
---- after making the following definition. Why?
-- infix:65   " ∘ " => dmap  

-- The "kernel" of a color c is the set of points in E that get colored c.
-- For example, dzero is saying that the origin is always in the kernel.
def ker : ∀ {E : Type} [AddCommGroup E] [TopologicalSpace E] [Module ℝ E]
            {C : Type} [RigidSpace E C], C → Set E := by
   intro E _ _ _ _ _ c
   exact { v : E | dmap c v = c}

-- We build up to a proof that the kernel is actually a linear subspace of E.

-- First we show that the kernel is always closed under scalar multiplication.
theorem lemma1 {E : Type} [AddCommGroup E] [TopologicalSpace E] [Module ℝ E]
            {C : Type} [RigidSpace E C]
            (c : C) (Λ : ℝ) {v : E} : v ∈ ker c → (Λ • v) ∈ ker c := by
  sorry

-- Then we show that the kernel is always closed under vector addition.
theorem lemma2 {E : Type} [AddCommGroup E] [TopologicalSpace E] [Module ℝ E]
            {C : Type} [RigidSpace E C]
            (c : C) {v w : E} : v ∈ ker c → w ∈ ker c → (v + w) ∈ ker c := by
  sorry

-- Now we can construct a witness to the fact that the kernel is a
-- submodule of E (which is synonymous with it being a linear
-- subspace, because a linear space is a module over a ring that
-- happens to be a field)
theorem kernel_submodule {E : Type} [AddCommGroup E] [TopologicalSpace E] [Module ℝ E]
            {C : Type} [RigidSpace E C] : C → Submodule ℝ E := by
  intro c
  exact {
   carrier := ker c
   smul_mem' := lemma1 c
   add_mem' :=  lemma2 c 
   zero_mem' := dzero c
  }

-- TODO: Formally state the theorem that:
-- ker(c) ⊆ ker(dmap c v)

-- TODO: Formally state the theorem that:
-- If c ≠ dmap c v, then we have the *strict* inequality dim(ker(dmap c v)) > dim(ker(c))
