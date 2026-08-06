/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.RingTheory.PicardGroup
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics] }

/-!
# USA Mathematical Olympiad 2008, Problem 6

At a certain mathematical conference, every pair of mathematicians are
either friends or strangers. At mealtime, every participant eats in one of
two large dining rooms. Each mathematician insists upon eating in a room
which contains an even number of his or her friends. Prove that the number
of ways that the mathematicians may be split between the two rooms is a
power of two (i.e., is of the form 2^k for some positive integer k).
-/

namespace Usa2008P6

snip begin

/-!
### Proof overview

Identify the two dining rooms with `ZMod 2`, so an assignment of the `n`
mathematicians to the rooms is a vector `x : Fin n → ZMod 2`. The condition
"vertex `v` shares its room with an even number of its friends" becomes, over
`ZMod 2`, the linear equation `(lap G x) v = (G.degree v : ZMod 2)`, where
`lap G` is the Laplacian (degrees on the diagonal, adjacency off-diagonal) of
the friendship graph `G`, viewed as a `ZMod 2`-linear endomorphism. Hence the
set of valid assignments is a coset of `LinearMap.ker (lap G)`, so — provided
it is nonempty — its cardinality is `2 ^ finrank (ker (lap G))`.

Existence of at least one valid assignment follows from the key identity
`∑ v, x v * (lap G x) v = ∑ v, (G.degree v : ZMod 2) * x v` (the off-diagonal
part vanishes because every edge is counted twice and `2 = 0`): it says that
the degree vector is orthogonal (for the standard dot product) to the kernel of
`lap G`. Since `lap G` is symmetric, its range has the same dimension as that
orthogonal complement, so the degree vector lies in the range of `lap G`.
-/

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

/-- The Laplacian of the friendship graph as a `ZMod 2`-linear map:
`(lap G x) v = deg(v) * x v + ∑_{u ∼ v} x u`. -/
def lap : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2) where
  toFun x := fun v => (G.degree v : ZMod 2) * x v + ∑ u ∈ G.neighborFinset v, x u
  map_add' x y := by
    funext v
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    abel
  map_smul' c x := by
    funext v
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [mul_add, Finset.mul_sum, mul_left_comm (G.degree v : ZMod 2) c (x v)]

lemma lap_apply (x : Fin n → ZMod 2) (v : Fin n) :
    lap G x v = (G.degree v : ZMod 2) * x v + ∑ u ∈ G.neighborFinset v, x u := rfl

/-- The degree vector, modulo 2. -/
def degVec : Fin n → ZMod 2 := fun v => (G.degree v : ZMod 2)

/-- In `ZMod 2` the indicator of `a = b` equals `1 + a + b`. -/
private lemma ite_eq_one_add :
    ∀ a b : ZMod 2, (if a = b then (1 : ZMod 2) else 0) = 1 + a + b := by decide

private lemma mul_self_eq : ∀ a : ZMod 2, a * a = a := by decide

/-- The combinatorial condition "an even number of friends share the room of `v`"
is the linear equation `(lap G x) v = deg(v)` in `ZMod 2`. -/
lemma even_card_filter_iff (x : Fin n → ZMod 2) (v : Fin n) :
    Even ((G.neighborFinset v).filter fun u => x u = x v).card ↔
      lap G x v = (G.degree v : ZMod 2) := by
  have hcard : (((G.neighborFinset v).filter fun u => x u = x v).card : ZMod 2)
      = ∑ u ∈ G.neighborFinset v, (1 + x u + x v) := by
    rw [Finset.card_filter]
    push_cast
    exact Finset.sum_congr rfl fun u _ => ite_eq_one_add (x u) (x v)
  have hsum : ∑ u ∈ G.neighborFinset v, (1 + x u + x v)
      = (G.degree v : ZMod 2) + lap G x v := by
    have e1 : ∑ u ∈ G.neighborFinset v, (1 + x u + x v)
        = ∑ u ∈ G.neighborFinset v, (1 : ZMod 2) + ∑ u ∈ G.neighborFinset v, x u
          + ∑ u ∈ G.neighborFinset v, x v := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    rw [e1, Finset.sum_const, Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree,
      nsmul_eq_mul, nsmul_eq_mul, mul_one, lap_apply]
    abel
  rw [even_iff_two_dvd, ← CharP.cast_eq_zero_iff (ZMod 2) 2 _, hcard, hsum,
    CharTwo.add_eq_zero]
  exact eq_comm

/-- Swapping the order of summation over ordered pairs of adjacent vertices. -/
lemma sum_neighbor_mul_comm (x y : Fin n → ZMod 2) :
    ∑ v, ∑ u ∈ G.neighborFinset v, x u * y v
      = ∑ v, ∑ u ∈ G.neighborFinset v, x v * y u := by
  have e : ∀ v : Fin n, ∀ f : Fin n → ZMod 2,
      ∑ u ∈ G.neighborFinset v, f u = ∑ u, if G.Adj v u then f u else 0 := by
    intro v f
    rw [SimpleGraph.neighborFinset_eq_filter, Finset.sum_filter]
  trans ∑ v : Fin n, ∑ u : Fin n, if G.Adj v u then x u * y v else (0 : ZMod 2)
  · exact Finset.sum_congr rfl fun v _ => e v (fun u => x u * y v)
  trans ∑ v : Fin n, ∑ u : Fin n, if G.Adj v u then x v * y u else (0 : ZMod 2)
  · have key : (∑ v : Fin n, ∑ u : Fin n, if G.Adj v u then x u * y v else (0 : ZMod 2))
        = ∑ v : Fin n, ∑ u : Fin n, if G.Adj u v then x v * y u else (0 : ZMod 2) := by
      rw [Finset.sum_comm]
    rw [key]
    exact Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun u _ => by
      by_cases h : G.Adj v u
      · rw [if_pos h, if_pos h.symm]
      · rw [if_neg h, if_neg fun h' => h h'.symm]
  · exact Finset.sum_congr rfl fun v _ => (e v (fun u => x v * y u)).symm

/-- The Laplacian is symmetric with respect to the dot product. -/
lemma lap_inner (x y : Fin n → ZMod 2) :
    ∑ v, lap G x v * y v = ∑ v, x v * lap G y v := by
  have h1 : ∀ v : Fin n, lap G x v * y v
      = (G.degree v : ZMod 2) * x v * y v + ∑ u ∈ G.neighborFinset v, x u * y v := by
    intro v
    rw [lap_apply, add_mul, Finset.sum_mul]
  have h2 : ∀ v : Fin n, x v * lap G y v
      = x v * ((G.degree v : ZMod 2) * y v) + ∑ u ∈ G.neighborFinset v, x v * y u := by
    intro v
    rw [lap_apply, mul_add, Finset.mul_sum]
  rw [Finset.sum_congr rfl fun v _ => h1 v, Finset.sum_congr rfl fun v _ => h2 v,
    Finset.sum_add_distrib, Finset.sum_add_distrib, sum_neighbor_mul_comm G x y]
  congr 1
  exact Finset.sum_congr rfl fun v _ => by ring

/-- The key identity: `xᵀ (L x) = ∑ v, deg(v) * x v` over `ZMod 2`. The cross
terms cancel because each edge is counted twice. -/
lemma inner_self_lap (x : Fin n → ZMod 2) :
    ∑ v, x v * lap G x v = ∑ v, (G.degree v : ZMod 2) * x v := by
  have h1 : ∀ v : Fin n, x v * lap G x v
      = (G.degree v : ZMod 2) * x v + ∑ u ∈ G.neighborFinset v, x v * x u := by
    intro v
    rw [lap_apply, mul_add, Finset.mul_sum]
    congr 1
    rw [mul_comm (x v), mul_assoc, mul_self_eq]
  rw [Finset.sum_congr rfl fun v _ => h1 v, Finset.sum_add_distrib]
  suffices h : ∑ v : Fin n, ∑ u ∈ G.neighborFinset v, x v * x u = 0 by rw [h, add_zero]
  have h3 : (∑ v : Fin n, ∑ u ∈ G.neighborFinset v, x v * x u)
      = ∑ p ∈ Finset.univ.filter fun p : Fin n × Fin n => G.Adj p.1 p.2, x p.1 * x p.2 := by
    have e : ∀ v : Fin n, ∑ u ∈ G.neighborFinset v, x v * x u
        = ∑ u : Fin n, if G.Adj v u then x v * x u else 0 := by
      intro v
      rw [SimpleGraph.neighborFinset_eq_filter, Finset.sum_filter]
    rw [Finset.sum_congr rfl fun v _ => e v, Finset.sum_filter, Fintype.sum_prod_type]
  rw [h3]
  refine Finset.sum_involution (fun p _ => Prod.swap p) ?_ ?_ ?_ ?_
  · intro p _
    show x p.1 * x p.2 + x p.2 * x p.1 = 0
    rw [mul_comm (x p.2) (x p.1)]
    exact CharTwo.add_self_eq_zero _
  · intro p hp _ hcontra
    rw [Finset.mem_filter] at hp
    have h12 : p.1 = p.2 := congrArg Prod.snd hcontra
    exact G.loopless.irrefl p.2 (h12 ▸ hp.2)
  · intro p hp
    rw [Finset.mem_filter] at hp ⊢
    exact ⟨Finset.mem_univ _, hp.2.symm⟩
  · intro p _
    cases p
    rfl

/-- Pairing with `d`, restricted to the kernel of `lap G`, as a linear map into
the dual of the kernel. -/
def Tmap : (Fin n → ZMod 2) →ₗ[ZMod 2] Module.Dual (ZMod 2) ↥(LinearMap.ker (lap G)) :=
  LinearMap.mk₂ (ZMod 2) (fun d x => ∑ v, d v * x.1 v)
    (fun a b x => by simp [Pi.add_apply, add_mul, Finset.sum_add_distrib])
    (fun c a x => by
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun v _ => mul_assoc ..)
    (fun d x y => by simp [mul_add, Finset.sum_add_distrib])
    (fun c d x => by
      simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun v _ => mul_left_comm ..)

lemma Tmap_apply (d : Fin n → ZMod 2) (x : ↥(LinearMap.ker (lap G))) :
    Tmap G d x = ∑ v, d v * x.1 v := rfl

lemma mem_ker_Tmap {d : Fin n → ZMod 2} :
    d ∈ LinearMap.ker (Tmap G) ↔ ∀ x : ↥(LinearMap.ker (lap G)), Tmap G d x = 0 := by
  rw [LinearMap.mem_ker, LinearMap.ext_iff]
  exact forall_congr' fun x => by rw [LinearMap.zero_apply]

/-- The range of `lap G` is contained in the "orthogonal complement" of its kernel. -/
lemma range_lap_le_ker_Tmap : LinearMap.range (lap G) ≤ LinearMap.ker (Tmap G) := by
  rintro z ⟨x, -, rfl⟩
  rw [mem_ker_Tmap]
  intro ⟨y, hy⟩
  rw [Tmap_apply]
  show ∑ v, lap G x v * y v = 0
  rw [lap_inner G x y, LinearMap.mem_ker.mp hy]
  simp

/-- The degree vector is orthogonal to the kernel of `lap G`. -/
lemma degVec_mem_ker_Tmap : degVec G ∈ LinearMap.ker (Tmap G) := by
  rw [mem_ker_Tmap]
  intro ⟨y, hy⟩
  rw [Tmap_apply]
  show ∑ v, (G.degree v : ZMod 2) * y v = 0
  rw [← inner_self_lap G y, LinearMap.mem_ker.mp hy]
  simp

/-- Every functional on the kernel of `lap G` is realized by a dot product:
extend it by zero on a complement and read off the coordinates. -/
lemma Tmap_surjective : Function.Surjective (Tmap G) := by
  intro φ
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (LinearMap.ker (lap G))
  let ψ : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
    φ.comp (Submodule.projectionOnto (LinearMap.ker (lap G)) C hC)
  refine ⟨fun v => ψ (Pi.single v 1), ?_⟩
  ext ⟨x, hx⟩
  rw [Tmap_apply]
  show ∑ v, ψ (Pi.single v 1) * x v = φ ⟨x, hx⟩
  have hxdecomp : x = ∑ v, x v • Pi.single v (1 : ZMod 2) := by
    funext u
    simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  have e1 : ψ x = ∑ v : Fin n, x v * ψ (Pi.single v 1) := by
    conv_lhs => rw [hxdecomp]
    rw [map_sum]
    exact Finset.sum_congr rfl fun v _ => by rw [map_smul, smul_eq_mul]
  rw [show (∑ v : Fin n, ψ (Pi.single v 1) * x v) = ∑ v, x v * ψ (Pi.single v 1) from
    Finset.sum_congr rfl fun v _ => mul_comm ..]
  rw [← e1]
  show φ (Submodule.projectionOnto (LinearMap.ker (lap G)) C hC x) = φ ⟨x, hx⟩
  rw [Submodule.projectionOnto_apply_left hC ⟨x, hx⟩]

/-- A symmetric matrix over `ZMod 2` has range equal to the orthogonal
complement of its kernel; here this is phrased via `Tmap`. -/
lemma range_lap_eq_ker_Tmap : LinearMap.range (lap G) = LinearMap.ker (Tmap G) := by
  apply Submodule.eq_of_le_of_finrank_eq (range_lap_le_ker_Tmap G)
  have hTL := LinearMap.finrank_range_add_finrank_ker (Tmap G)
  have hLK := LinearMap.finrank_range_add_finrank_ker (lap G)
  have htop : LinearMap.range (Tmap G) = ⊤ := LinearMap.range_eq_top.mpr (Tmap_surjective G)
  have hfr : Module.finrank (ZMod 2) ↥(LinearMap.range (Tmap G))
      = Module.finrank (ZMod 2) ↥(LinearMap.ker (lap G)) := by
    rw [htop, finrank_top]
    exact Subspace.dual_finrank_eq
  omega

/-- There is at least one valid room assignment. -/
lemma exists_solution : ∃ x0, lap G x0 = degVec G := by
  have h : degVec G ∈ LinearMap.range (lap G) := by
    rw [range_lap_eq_ker_Tmap G]
    exact degVec_mem_ker_Tmap G
  exact LinearMap.mem_range.mp h

/-- The valid assignments form a coset of the kernel of `lap G`. -/
def solutionEquiv (x0 : Fin n → ZMod 2) (hx0 : lap G x0 = degVec G) :
    ↥(LinearMap.ker (lap G)) ≃ {x // lap G x = degVec G} where
  toFun z := ⟨x0 + z.1, by rw [map_add, hx0, LinearMap.mem_ker.mp z.2, add_zero]⟩
  invFun x := ⟨x.1 - x0, by rw [LinearMap.mem_ker, map_sub, x.2, hx0, sub_self]⟩
  left_inv z := by
    apply Subtype.ext
    show x0 + z.1 - x0 = z.1
    exact add_sub_cancel_left ..
  right_inv x := Subtype.ext (add_sub_cancel ..)

lemma card_solutions (x0 : Fin n → ZMod 2) (hx0 : lap G x0 = degVec G) :
    Fintype.card {x : Fin n → ZMod 2 // lap G x = degVec G}
      = 2 ^ Module.finrank (ZMod 2) ↥(LinearMap.ker (lap G)) := by
  rw [← Nat.card_eq_fintype_card, Nat.card_congr (solutionEquiv G x0 hx0).symm,
    Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_eq_fintype_card, ZMod.card]

snip end

problem usa2008_p6 (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    ∃ k : ℕ, Fintype.card {x : Fin n → ZMod 2 // ∀ v : Fin n,
      Even ((G.neighborFinset v).filter fun u => x u = x v).card} = 2 ^ k := by
  obtain ⟨x0, hx0⟩ := exists_solution G
  refine ⟨Module.finrank (ZMod 2) ↥(LinearMap.ker (lap G)), ?_⟩
  have hiff : ∀ x : Fin n → ZMod 2,
      (∀ v : Fin n, Even ((G.neighborFinset v).filter fun u => x u = x v).card) ↔
        lap G x = degVec G := by
    intro x
    rw [funext_iff]
    exact forall_congr' fun v => even_card_filter_iff G x v
  rw [Fintype.card_congr (Equiv.subtypeEquivRight hiff), card_solutions G x0 hx0]

end Usa2008P6
