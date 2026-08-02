/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# USA Mathematical Olympiad 1978, Problem 4

Show that if the angle between each pair of faces of a tetrahedron is equal,
then the tetrahedron is regular. Does a tetrahedron have to be regular if five
of the angles are equal?
-/

namespace Usa1978P4

open scoped InnerProductSpace RealInnerProductSpace

/-- The ambient 3-dimensional Euclidean space. -/
abbrev Pt := EuclideanSpace ℝ (Fin 3)

/-- A tetrahedron with vertices `v` is **regular** if all six of its edges
have the same length. -/
def IsRegularTetrahedron (v : Fin 4 → Pt) : Prop :=
  ∃ L, ∀ i j : Fin 4, i ≠ j → dist (v i) (v j) = L

/-- `IsOutwardNormals v n` asserts that `n` is the family of outward-pointing
unit normals to the faces of the tetrahedron with vertices `v`: `n i` is a
unit vector, orthogonal to the face opposite `v i` (the plane through the
other three vertices), and pointing away from `v i`.

For a genuine (non-degenerate) tetrahedron such a family exists
(`exists_isOutwardNormals` below) and is easily seen to be unique, so the
dihedral angles defined in terms of `n` are the actual dihedral angles. -/
structure IsOutwardNormals (v n : Fin 4 → Pt) : Prop where
  /-- each normal is a unit vector -/
  norm_one : ∀ i : Fin 4, ‖n i‖ = 1
  /-- `n i` is orthogonal to every edge of face `i` -/
  flat : ∀ i j k : Fin 4, j ≠ i → k ≠ i → ⟪n i, v j - v k⟫_ℝ = 0
  /-- `n i` points away from the opposite vertex `v i` -/
  outward : ∀ i j : Fin 4, j ≠ i → ⟪n i, v i - v j⟫_ℝ < 0

/-- The (interior) dihedral angle along the edge shared by faces `i` and `j`
of a tetrahedron with outward unit normals `n`: it equals `π` minus the angle
between the two outward normals. -/
noncomputable def dihedralAngle (n : Fin 4 → Pt) (i j : Fin 4) : ℝ :=
  Real.pi - InnerProductGeometry.angle (n i) (n j)

snip begin

/-- Four pairwise distinct indices in `Fin 4` exhaust `Fin 4`. -/
lemma fin4_cover {i j k l : Fin 4} (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) (a : Fin 4) :
    a = i ∨ a = j ∨ a = k ∨ a = l := by
  by_contra! h
  have hcard : ({a, i, j, k, l} : Finset (Fin 4)).card = 5 := by
    rw [Finset.card_insert_of_notMem (by simp [h.1, h.2.1, h.2.2.1, h.2.2.2]),
        Finset.card_insert_of_notMem (by simp [hij, hik, hil]),
        Finset.card_insert_of_notMem (by simp [hjk, hjl]),
        Finset.card_insert_of_notMem (by simp [hkl]), Finset.card_singleton]
  have hle := Finset.card_le_card (Finset.subset_univ ({a, i, j, k, l} : Finset (Fin 4)))
  rw [hcard, Finset.card_univ, Fintype.card_fin] at hle
  norm_num at hle

/-- In an affinely independent family of four points, the three difference
vectors from one vertex to the other three are linearly independent. -/
lemma affineIndependent_three_vsub {v : Fin 4 → Pt} (hv : AffineIndependent ℝ v)
    {k i j l : Fin 4} (hi : i ≠ k) (hj : j ≠ k) (hl : l ≠ k)
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) :
    LinearIndependent ℝ ![v i - v k, v j - v k, v l - v k] := by
  have h1 := (affineIndependent_iff_linearIndependent_vsub ℝ v k).mp hv
  simp only [vsub_eq_sub] at h1
  have hinj : Function.Injective
      (![⟨i, hi⟩, ⟨j, hj⟩, ⟨l, hl⟩] : Fin 3 → {x // x ≠ k}) := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all
  have h3 : (fun x : {x // x ≠ k} => v x - v k) ∘
        (![⟨i, hi⟩, ⟨j, hj⟩, ⟨l, hl⟩] : Fin 3 → {x // x ≠ k})
      = ![v i - v k, v j - v k, v l - v k] := by
    funext t
    fin_cases t <;> rfl
  rw [← h3]
  exact h1.comp _ hinj

/-- For a non-degenerate tetrahedron, the outward unit normal to the face
opposite `v i` exists: take a nonzero vector `w` in the orthogonal complement
of the (2-dimensional) direction space of that face, and normalize it with the
appropriate sign. -/
lemma exists_normal_aux {v : Fin 4 → Pt} (hv : AffineIndependent ℝ v)
    {i j k l : Fin 4} (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    ∃ ni : Pt, ‖ni‖ = 1 ∧
      (∀ a b : Fin 4, a ≠ i → b ≠ i → ⟪ni, v a - v b⟫_ℝ = 0) ∧
      ∀ a : Fin 4, a ≠ i → ⟪ni, v i - v a⟫_ℝ < 0 := by
  classical
  have hLI := affineIndependent_three_vsub hv hik hjk hkl.symm hij hil hjl
  set S : Submodule ℝ Pt :=
    Submodule.span ℝ ({v j - v k, v l - v k} : Set Pt) with hS
  have hmem : ∀ m : Fin 4, m ≠ i → v m - v k ∈ S := by
    intro m hm
    rcases fin4_cover hij hik hil hjk hjl hkl m with rfl | rfl | rfl | rfl
    · exact (hm rfl).elim
    · rw [hS]; exact Submodule.subset_span (by simp)
    · simp
    · rw [hS]; exact Submodule.subset_span (by simp)
  have hfinrank : Module.finrank ℝ ↥S ≤ 2 := by
    rw [hS]
    refine (finrank_span_le_card _).trans ?_
    rw [Set.toFinset_insert, Set.toFinset_singleton]
    have hcard := Finset.card_insert_le (v j - v k) ({v l - v k} : Finset Pt)
    rw [Finset.card_singleton] at hcard
    exact hcard
  have hE3 : Module.finrank ℝ Pt = 3 := by
    simp [finrank_euclideanSpace, Fintype.card_fin]
  have hsum := S.finrank_add_finrank_orthogonal
  have hpos : 0 < Module.finrank ℝ ↥Sᗮ := by omega
  obtain ⟨⟨w, hwmem⟩, hwne⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
  have hwne' : w ≠ 0 := by simpa using hwne
  -- `w` is not orthogonal to `v i - v k`, otherwise it would be orthogonal to
  -- three linearly independent vectors, hence zero.
  have hvi : ⟪w, v i - v k⟫_ℝ ≠ 0 := by
    by_contra! hcon
    have htop : Submodule.span ℝ (Set.range ![v i - v k, v j - v k, v l - v k]) = ⊤ :=
      hLI.span_eq_top_of_card_eq_finrank' (by simp [finrank_euclideanSpace, Fintype.card_fin])
    have hwtop : w ∈ (⊤ : Submodule ℝ Pt)ᗮ := by
      rw [← htop, Submodule.mem_orthogonal']
      intro u hu
      induction hu using Submodule.span_induction with
      | mem x hx =>
          obtain ⟨t, rfl⟩ := hx
          fin_cases t
          · exact hcon
          · exact Submodule.inner_left_of_mem_orthogonal
              (Submodule.subset_span (by simp)) hwmem
          · exact Submodule.inner_left_of_mem_orthogonal
              (Submodule.subset_span (by simp)) hwmem
      | zero => exact inner_zero_right _
      | add x y _ _ hx hy => rw [inner_add_right, hx, hy, add_zero]
      | smul a x _ hx => rw [inner_smul_right, hx, mul_zero]
    have hww : ⟪w, w⟫_ℝ = 0 :=
      (Submodule.mem_orthogonal ⊤ w).mp hwtop w Submodule.mem_top
    exact hwne' (inner_self_eq_zero.mp hww)
  set s : ℝ := if 0 < ⟪w, v i - v k⟫_ℝ then -1 else 1 with hs_def
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hwne'
  have hs_abs : |s| = 1 := by by_cases h : 0 < ⟪w, v i - v k⟫_ℝ <;> simp [hs_def, h]
  refine ⟨(s / ‖w‖) • w, ?_, ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_div, hs_abs, abs_norm, one_div]
    exact inv_mul_cancel₀ hwpos.ne'
  · intro a b ha hb
    rw [real_inner_smul_left]
    have hab : v a - v b ∈ S := by
      have hdecomp : v a - v b = (v a - v k) - (v b - v k) := by abel
      rw [hdecomp]
      exact sub_mem (hmem a ha) (hmem b hb)
    rw [Submodule.inner_left_of_mem_orthogonal hab hwmem, mul_zero]
  · intro a ha
    rw [real_inner_smul_left]
    have hmemka : v k - v a ∈ S := by
      have hdecomp : v k - v a = (v k - v k) - (v a - v k) := by abel
      rw [hdecomp]
      exact sub_mem (hmem k hik.symm) (hmem a ha)
    have hflat : ⟪w, v k - v a⟫_ℝ = 0 :=
      Submodule.inner_left_of_mem_orthogonal hmemka hwmem
    have hdecomp : v i - v a = (v i - v k) + (v k - v a) := by abel
    rw [hdecomp, inner_add_right, hflat, add_zero]
    by_cases h : 0 < ⟪w, v i - v k⟫_ℝ
    · have hsr : s = -1 := by simp [hs_def, h]
      rw [hsr]
      exact mul_neg_of_neg_of_pos (div_neg_of_neg_of_pos (by norm_num) hwpos) h
    · have hsr : s = 1 := by simp [hs_def, h]
      rw [hsr, one_div]
      exact mul_neg_of_pos_of_neg (inv_pos.mpr hwpos) (lt_of_le_of_ne (not_lt.mp h) hvi)

/-- Every non-degenerate tetrahedron admits a family of outward unit normals. -/
lemma exists_isOutwardNormals {v : Fin 4 → Pt} (hv : AffineIndependent ℝ v) :
    ∃ n : Fin 4 → Pt, IsOutwardNormals v n := by
  have key : ∀ i : Fin 4, ∃ ni : Pt, ‖ni‖ = 1 ∧
      (∀ a b : Fin 4, a ≠ i → b ≠ i → ⟪ni, v a - v b⟫_ℝ = 0) ∧
      ∀ a : Fin 4, a ≠ i → ⟪ni, v i - v a⟫_ℝ < 0 := by
    intro i
    fin_cases i
    · exact exists_normal_aux hv (j := 1) (k := 2) (l := 3)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact exists_normal_aux hv (j := 0) (k := 2) (l := 3)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact exists_normal_aux hv (j := 0) (k := 1) (l := 3)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact exists_normal_aux hv (j := 0) (k := 1) (l := 2)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  choose n hn using key
  exact ⟨n, fun i => (hn i).1, fun i j k hj hk => (hn i).2.1 j k hj hk,
    fun i j hj => (hn i).2.2 j hj⟩

/-- For two distinct indices in `Fin 4` there is a third index different from
both. -/
lemma fin4_exists_ne_ne {i j : Fin 4} (hij : i ≠ j) : ∃ k : Fin 4, k ≠ i ∧ k ≠ j := by
  fin_cases i <;> fin_cases j <;> simp_all <;>
    first
    | exact ⟨0, by decide, by decide⟩
    | exact ⟨1, by decide, by decide⟩
    | exact ⟨2, by decide, by decide⟩

/-- For each face `j` of the tetrahedron, `⟪n j, ·⟫` is constant on the
vertices of that face: the common value is the plane constant of face `j`. -/
lemma exists_face_plane_const {v n : Fin 4 → Pt} (hn : IsOutwardNormals v n) :
    ∃ d : Fin 4 → ℝ, ∀ i j : Fin 4, i ≠ j → ⟪n j, v i⟫_ℝ = d j := by
  refine ⟨fun j => ⟪n j, v (if j = 0 then 1 else 0)⟫_ℝ, fun i j hij => ?_⟩
  have hk : (if j = 0 then 1 else 0 : Fin 4) ≠ j := by
    by_cases hj : j = 0
    · subst hj; decide
    · rw [if_neg hj]; exact Ne.symm hj
  have h := hn.flat j i (if j = 0 then 1 else 0) hij hk
  rw [inner_sub_right, sub_eq_zero] at h
  exact h

/-- The outward unit normals of a non-degenerate tetrahedron are pairwise
distinct: two equal normals would force two faces to be parallel, contradicting
the outward-pointing property. -/
lemma outwardNormals_pairwise_ne {v n : Fin 4 → Pt} (hn : IsOutwardNormals v n)
    {i j : Fin 4} (hij : i ≠ j) : n i ≠ n j := by
  intro hcontra
  have h3 : ⟪n i, v i⟫_ℝ < ⟪n i, v j⟫_ℝ := by
    have h := hn.outward i j hij.symm
    rwa [inner_sub_right, sub_lt_zero] at h
  have h4 : ⟪n j, v j⟫_ℝ < ⟪n j, v i⟫_ℝ := by
    have h := hn.outward j i hij
    rwa [inner_sub_right, sub_lt_zero] at h
  rw [hcontra] at h3
  linarith

/-- **Key lemma.** If all six pairwise inner products of the outward unit
normals of a tetrahedron are equal, then the tetrahedron is regular.

The proof is pure linear algebra: four vectors in a 3-dimensional space are
linearly dependent, which first forces the common inner product to be `c = -1/3`
and then `n 0 + n 1 + n 2 + n 3 = 0`.  Writing `d j` for the plane constant of
face `j` and `D = ∑ d`, one checks that `v i - v j = -(3/4)·D • (n i - n j)` by
comparing inner products against three linearly independent normals.  Hence all
six edges have length `|3D/4| · ‖n i - n j‖`, which is the same for every
pair. -/
lemma regular_of_normals {v n : Fin 4 → Pt} (hn : IsOutwardNormals v n)
    (h : ∀ i j k l : Fin 4, i ≠ j → k ≠ l → ⟪n i, n j⟫_ℝ = ⟪n k, n l⟫_ℝ) :
    IsRegularTetrahedron v := by
  obtain ⟨d, hvd⟩ := exists_face_plane_const hn
  obtain ⟨c, hc⟩ : ∃ c : ℝ, ∀ i j : Fin 4, i ≠ j → ⟪n i, n j⟫_ℝ = c :=
    ⟨⟪n 0, n 1⟫_ℝ, fun i j hij => h i j 0 1 hij (by decide)⟩
  have hnii : ∀ i : Fin 4, ⟪n i, n i⟫_ℝ = 1 := fun i => by
    rw [real_inner_self_eq_norm_sq, hn.norm_one i]; norm_num
  -- `c ≠ 1`, since the normals are pairwise distinct.
  have hc1 : c ≠ 1 := by
    intro hcontra
    have key : ⟪n 0 - n 1, n 0 - n 1⟫_ℝ = 0 := by
      rw [inner_sub_left, inner_sub_right, inner_sub_right, hnii 0, hnii 1,
          hc 0 1 (by decide), hc 1 0 (by decide), hcontra]
      norm_num
    have h01 : n 0 - n 1 = 0 := inner_self_eq_zero.mp key
    exact outwardNormals_pairwise_ne hn (by decide) (sub_eq_zero.mp h01)
  -- Four vectors in a 3-dimensional space are linearly dependent.
  have hdep : ¬ LinearIndependent ℝ n := by
    intro hli
    have hle := hli.fintype_card_le_finrank
    rw [finrank_euclideanSpace, Fintype.card_fin] at hle
    norm_num at hle
  obtain ⟨μ, hμsum, j0, hj0⟩ := Fintype.not_linearIndependent_iff.mp hdep
  have hμj : ∀ j : Fin 4, (1 - c) * μ j + c * (∑ i, μ i) = 0 := by
    intro j
    have h0 : ⟪∑ i : Fin 4, μ i • n i, n j⟫_ℝ = 0 := by
      rw [hμsum]; exact inner_zero_left _
    rw [sum_inner, Finset.sum_eq_sum_sdiff_singleton_add (Finset.mem_univ j) _] at h0
    have hcongr : ∀ x ∈ Finset.univ \ {j}, ⟪μ x • n x, n j⟫_ℝ = c * μ x := by
      intro x hx
      rw [real_inner_smul_left, hc x j (show x ≠ j by simpa using hx), mul_comm]
    rw [Finset.sum_congr rfl hcongr, ← Finset.mul_sum,
        real_inner_smul_left, hnii j, mul_one] at h0
    have hsd : ∑ x ∈ Finset.univ \ {j}, μ x = (∑ i, μ i) - μ j := by
      have hsd' : ∑ x ∈ Finset.univ \ {j}, μ x + ∑ x ∈ {j}, μ x = ∑ i, μ i :=
        Finset.sum_sdiff (Finset.subset_univ _)
      rw [Finset.sum_singleton] at hsd'
      exact eq_sub_of_add_eq hsd'
    rw [hsd] at h0
    linarith
  -- Summing these equations over `j` forces `c = -1/3`.
  have hc13 : c = -1 / 3 := by
    have hsum0 : (∑ j : Fin 4, ((1 - c) * μ j + c * (∑ i, μ i))) = 0 :=
      Finset.sum_eq_zero (fun j _ => hμj j)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul] at hsum0
    by_cases hT : (∑ i, μ i) = 0
    · exfalso
      have h0 := hμj j0
      rw [hT, mul_zero, add_zero] at h0
      exact hj0 ((mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hc1.symm))
    · have hT3 : (∑ i, μ i) * (1 + 3 * c) = 0 := by linear_combination hsum0
      rcases mul_eq_zero.mp hT3 with h | h
      · exact absurd h hT
      · linarith
  -- Hence the normals sum to zero.
  have hnsum : (∑ i : Fin 4, n i) = 0 := by
    have h2 : ⟪∑ i : Fin 4, n i, ∑ i : Fin 4, n i⟫_ℝ = 0 := by
      rw [sum_inner]
      have hterm : ∀ i : Fin 4, ⟪n i, ∑ j : Fin 4, n j⟫_ℝ = 1 + 3 * c := by
        intro i
        rw [inner_sum, Finset.sum_eq_sum_sdiff_singleton_add (Finset.mem_univ i) _, hnii i]
        have hcongr : ∀ x ∈ Finset.univ \ {i}, ⟪n i, n x⟫_ℝ = c := by
          intro x hx
          exact hc i x (show x ≠ i by simpa using hx).symm
        have hrest : (∑ x ∈ Finset.univ \ {i}, ⟪n i, n x⟫_ℝ) = 3 * c := by
          rw [Finset.sum_congr rfl hcongr, Finset.sum_const, Finset.card_sdiff,
              Finset.card_univ, Fintype.card_fin, Finset.inter_univ, Finset.card_singleton,
              show (4 : ℕ) - 1 = 3 from rfl, nsmul_eq_mul]
          norm_num
        linarith [hrest]
      rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul, hc13]
      norm_num
    exact inner_self_eq_zero.mp h2
  -- The value of `⟪n i, v i⟫` from `∑ n = 0`.
  have hvi_val : ∀ i : Fin 4, ⟪n i, v i⟫_ℝ = -(∑ t, d t) + d i := by
    intro i
    have h0 : ⟪∑ t : Fin 4, n t, v i⟫_ℝ = 0 := by rw [hnsum]; exact inner_zero_left _
    rw [sum_inner, Finset.sum_eq_sum_sdiff_singleton_add (Finset.mem_univ i) _] at h0
    have hcongr : ∀ x ∈ Finset.univ \ {i}, ⟪n x, v i⟫_ℝ = d x := by
      intro x hx
      exact hvd i x (show x ≠ i by simpa using hx).symm
    rw [Finset.sum_congr rfl hcongr] at h0
    have hsd : (Finset.univ \ {i}).sum d = (∑ t, d t) - d i := by
      have hsd' : (Finset.univ \ {i}).sum d + (∑ x ∈ {i}, d x) = ∑ t, d t :=
        Finset.sum_sdiff (Finset.subset_univ _)
      rw [Finset.sum_singleton] at hsd'
      exact eq_sub_of_add_eq hsd'
    rw [hsd] at h0
    linarith
  -- Each edge vector is a fixed multiple of the corresponding normal difference.
  have hdvd : ∀ i j : Fin 4, i ≠ j →
      v i - v j = (-(3 / 4) * ∑ t, d t) • (n i - n j) := by
    intro i j hij
    obtain ⟨k, hki, hkj⟩ := fin4_exists_ne_ne hij
    have hLI3 : LinearIndependent ℝ ![n i, n j, n k] := by
      rw [Fintype.linearIndependent_iff]
      intro g hg t
      rw [Fin.sum_univ_three] at hg
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons] at hg
      have e0 : g 0 * 1 + g 1 * c + g 2 * c = 0 := by
        have e : ⟪g 0 • n i + g 1 • n j + g 2 • n k, n i⟫_ℝ = 0 := by
          rw [hg]; exact inner_zero_left _
        rwa [inner_add_left, inner_add_left, real_inner_smul_left, real_inner_smul_left,
          real_inner_smul_left, hnii i, hc j i hij.symm, hc k i hki] at e
      have e1 : g 0 * c + g 1 * 1 + g 2 * c = 0 := by
        have e : ⟪g 0 • n i + g 1 • n j + g 2 • n k, n j⟫_ℝ = 0 := by
          rw [hg]; exact inner_zero_left _
        rwa [inner_add_left, inner_add_left, real_inner_smul_left, real_inner_smul_left,
          real_inner_smul_left, hnii j, hc i j hij, hc k j hkj] at e
      have e2 : g 0 * c + g 1 * c + g 2 * 1 = 0 := by
        have e : ⟪g 0 • n i + g 1 • n j + g 2 • n k, n k⟫_ℝ = 0 := by
          rw [hg]; exact inner_zero_left _
        rwa [inner_add_left, inner_add_left, real_inner_smul_left, real_inner_smul_left,
          real_inner_smul_left, hnii k, hc i k hki.symm, hc j k hkj.symm] at e
      have h01 : g 0 = g 1 := by
        have hz : (1 - c) * (g 0 - g 1) = 0 := by linear_combination e0 - e1
        have h01' := (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hc1.symm)
        linarith
      have h02 : g 0 = g 2 := by
        have hz : (1 - c) * (g 0 - g 2) = 0 := by linear_combination e0 - e2
        have h02' := (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hc1.symm)
        linarith
      have h0 : g 0 = 0 := by
        have hz : g 0 * (1 + 2 * c) = 0 := by linear_combination e0 + c * h01 + c * h02
        rcases mul_eq_zero.mp hz with h | h
        · exact h
        · exfalso; rw [hc13] at h; norm_num at h
      fin_cases t
      · exact h0
      · exact h01 ▸ h0
      · exact h02 ▸ h0
    have hspan : Submodule.span ℝ (Set.range ![n i, n j, n k]) = ⊤ :=
      hLI3.span_eq_top_of_card_eq_finrank' (by simp [finrank_euclideanSpace, Fintype.card_fin])
    have hinner : ∀ u ∈ Set.range ![n i, n j, n k],
        ⟪u, v i - v j⟫_ℝ = ⟪u, (-(3 / 4) * ∑ t, d t) • (n i - n j)⟫_ℝ := by
      intro u hu
      obtain ⟨t, rfl⟩ := hu
      fin_cases t
      · show ⟪n i, v i - v j⟫_ℝ = ⟪n i, (-(3 / 4) * ∑ t, d t) • (n i - n j)⟫_ℝ
        rw [inner_sub_right, hvi_val i, hvd j i hij.symm, real_inner_smul_right,
            inner_sub_right, hnii i, hc i j hij, hc13]
        ring
      · show ⟪n j, v i - v j⟫_ℝ = ⟪n j, (-(3 / 4) * ∑ t, d t) • (n i - n j)⟫_ℝ
        rw [inner_sub_right, hvd i j hij, hvi_val j, real_inner_smul_right,
            inner_sub_right, hnii j, hc j i hij.symm, hc13]
        ring
      · show ⟪n k, v i - v j⟫_ℝ = ⟪n k, (-(3 / 4) * ∑ t, d t) • (n i - n j)⟫_ℝ
        rw [inner_sub_right, hvd i k hki.symm, hvd j k hkj.symm, real_inner_smul_right,
            inner_sub_right, hc k i hki, hc k j hkj]
        ring
    have hsub : v i - v j - (-(3 / 4) * ∑ t, d t) • (n i - n j) ∈
        (⊤ : Submodule ℝ Pt)ᗮ := by
      rw [← hspan, Submodule.mem_orthogonal]
      intro u hu
      induction hu using Submodule.span_induction with
      | mem x hx => rw [inner_sub_right, hinner x hx, sub_self]
      | zero => exact inner_zero_left _
      | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
      | smul a x _ hx => rw [real_inner_smul_left, hx, mul_zero]
    have hz : ⟪v i - v j - (-(3 / 4) * ∑ t, d t) • (n i - n j),
        v i - v j - (-(3 / 4) * ∑ t, d t) • (n i - n j)⟫_ℝ = 0 :=
      (Submodule.mem_orthogonal ⊤ _).mp hsub _ Submodule.mem_top
    exact sub_eq_zero.mp (inner_self_eq_zero.mp hz)
  -- All squared edge lengths coincide.
  have hsq : ∀ a b : Fin 4, a ≠ b → ‖n a - n b‖ ^ 2 = 2 - 2 * c := by
    intro a b hab
    rw [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right, inner_sub_right,
        hnii a, hnii b, hc a b hab, hc b a hab.symm]
    ring
  refine ⟨|-(3 / 4) * ∑ t, d t| * ‖n 0 - n 1‖, fun i j hij => ?_⟩
  rw [dist_eq_norm, hdvd i j hij, norm_smul, Real.norm_eq_abs]
  congr 1
  have h3 : (‖n i - n j‖ - ‖n 0 - n 1‖) * (‖n i - n j‖ + ‖n 0 - n 1‖) = 0 := by
    have hs : ‖n i - n j‖ ^ 2 = ‖n 0 - n 1‖ ^ 2 := by
      rw [hsq i j hij, hsq 0 1 (by decide)]
    linear_combination hs
  rcases mul_eq_zero.mp h3 with h | h
  · linarith
  · have h1 := norm_nonneg (n i - n j)
    have h2 := norm_nonneg (n 0 - n 1)
    linarith

/-- The vertices of the counterexample tetrahedron for part 2. -/
noncomputable def cex_v : Fin 4 → Pt :=
  ![!₂[0, 0, -2], !₂[-4 * Real.sqrt 3, 0, 4], !₂[2 * Real.sqrt 3, -6, 4],
    !₂[4 * Real.sqrt 3 / 7, 12 / 7, -2 / 7]]

/-- Outward unit normals to the four faces of the counterexample tetrahedron. -/
noncomputable def cex_n : Fin 4 → Pt :=
  ![!₂[5 * Real.sqrt 3 / 28, 15 / 28, 11 / 14], !₂[Real.sqrt 3 / 2, 0, -1 / 2],
    !₂[-Real.sqrt 3 / 4, 3 / 4, -1 / 2], !₂[-Real.sqrt 3 / 4, -3 / 4, -1 / 2]]

/-- The four normals are unit vectors. -/
theorem cex_unit : ∀ i : Fin 4, ‖cex_n i‖ = 1 := by
  intro i
  fin_cases i <;>
    (rw [EuclideanSpace.norm_eq]
     simp only [cex_n, PiLp.toLp_apply, Fin.sum_univ_three, Real.norm_eq_abs, sq_abs,
       Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
       Matrix.tail_cons, Matrix.cons_val_zero', Matrix.cons_val_succ']
     rw [Real.sqrt_eq_one]
     nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)])

/-- The `i`-th normal paired with the `j`-th vertex (`i ≠ j`) equals `1`:
each `v j` with `j ≠ i` lies in the plane `⟪cex_n i, ·⟫ = 1`. -/
theorem cex_plane : ∀ i j : Fin 4, i ≠ j → ⟪cex_n i, cex_v j⟫_ℝ = 1 := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    first
      | exact absurd rfl hij
      | (simp only [cex_n, cex_v, PiLp.inner_apply, RCLike.inner_apply,
           conj_trivial, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
           Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_zero',
           Matrix.cons_val_succ']
         nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)])

/-- The `i`-th normal paired with the `i`-th vertex is `< 1`. -/
theorem cex_inner_self : ∀ i : Fin 4, ⟪cex_n i, cex_v i⟫_ℝ < 1 := by
  intro i
  fin_cases i <;>
    (simp only [cex_n, cex_v, PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
       Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
       Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_zero', Matrix.cons_val_succ']
     nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)])

/-- Inner products between distinct normals, excluding the two ordered pairs
`(0, 3)` and `(3, 0)`. -/
theorem cex_inner_nn : ∀ i j : Fin 4, i ≠ j → (i, j) ≠ (0, 3) → (i, j) ≠ (3, 0) →
    ⟪cex_n i, cex_n j⟫_ℝ = -1 / 8 := by
  intro i j hij hne1 hne2
  fin_cases i <;> fin_cases j <;>
    first
      | exact absurd rfl hij
      | exact absurd rfl hne1
      | exact absurd rfl hne2
      | (simp only [cex_n, PiLp.inner_apply, RCLike.inner_apply,
           conj_trivial, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
           Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_zero',
           Matrix.cons_val_succ']
         nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)])

/-- All dihedral angles except the `(0, 3)`/`(3, 0)` edge are equal. -/
theorem cex_dihed : ∀ i j : Fin 4, i ≠ j → (i, j) ≠ (0, 3) → (i, j) ≠ (3, 0) →
    dihedralAngle cex_n i j = dihedralAngle cex_n 0 1 := by
  intro i j hij hne1 hne2
  have e1 := cex_inner_nn i j hij hne1 hne2
  have e2 := cex_inner_nn 0 1 (by decide) (by decide) (by decide)
  unfold dihedralAngle InnerProductGeometry.angle
  rw [cex_unit i, cex_unit j, cex_unit 0, cex_unit 1, mul_one, div_one, div_one, e1, e2]

/-- `dist (v 0) (v 1) ^ 2 = 84`. -/
theorem cex_dist01_sq : dist (cex_v 0) (cex_v 1) ^ 2 = 84 := by
  rw [EuclideanSpace.dist_sq_eq]
  simp only [cex_v, PiLp.toLp_apply, Fin.sum_univ_three, Real.dist_eq, sq_abs,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)]

/-- `dist (v 1) (v 2) ^ 2 = 144`. -/
theorem cex_dist12_sq : dist (cex_v 1) (cex_v 2) ^ 2 = 144 := by
  rw [EuclideanSpace.dist_sq_eq]
  simp only [cex_v, PiLp.toLp_apply, Fin.sum_univ_three, Real.dist_eq, sq_abs,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)]

/-- The tetrahedron is not regular since `84 ≠ 144`. -/
theorem cex_notreg : ¬ IsRegularTetrahedron cex_v := by
  rintro ⟨L, hL⟩
  have h12 : dist (cex_v 0) (cex_v 1) = dist (cex_v 1) (cex_v 2) := by
    rw [hL 0 1 (by decide), hL 1 2 (by decide)]
  have hsq := congrArg (fun x : ℝ => x ^ 2) h12
  rw [cex_dist01_sq, cex_dist12_sq] at hsq
  norm_num at hsq

/-- The four vertices are affinely independent. -/
theorem cex_ai : AffineIndependent ℝ cex_v := by
  rw [affineIndependent_iff_linearIndependent_vsub ℝ cex_v 0]
  simp only [vsub_eq_sub]
  have hli : LinearIndependent ℝ ![cex_v 1 - cex_v 0, cex_v 2 - cex_v 0, cex_v 3 - cex_v 0] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hg
    have e0 := congrArg (· (0 : Fin 3)) hg
    have e1 := congrArg (· (1 : Fin 3)) hg
    have e2 := congrArg (· (2 : Fin 3)) hg
    simp only [cex_v, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, PiLp.zero_apply,
      smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
      at e0 e1 e2
    have hsqrt3 : Real.sqrt 3 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 3)).ne'
    have hgc : -4 * g 0 + 2 * g 1 + 4 / 7 * g 2 = 0 := by
      have h01 : (-4 * g 0 + 2 * g 1 + 4 / 7 * g 2) * Real.sqrt 3 = 0 := by
        linear_combination e0
      rcases mul_eq_zero.mp h01 with h | h
      · exact h
      · exact absurd h hsqrt3
    have e1' : -6 * g 1 + 12 / 7 * g 2 = 0 := by linear_combination e1
    have e2' : 6 * g 0 + 6 * g 1 + 12 / 7 * g 2 = 0 := by linear_combination e2
    have h0 : g 0 = 0 := by linarith
    have h1 : g 1 = 0 := by linarith
    have h2 : g 2 = 0 := by linarith
    intro t
    fin_cases t
    · exact h0
    · exact h1
    · exact h2
  rw [← linearIndependent_equiv
    (Equiv.ofBijective ![⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩] ⟨by decide, by decide⟩ :
      Fin 3 ≃ {x // x ≠ (0 : Fin 4)})]
  have hcomp : (fun i : {x // x ≠ (0 : Fin 4)} => cex_v ↑i - cex_v 0) ∘
      (Equiv.ofBijective ![⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩] ⟨by decide, by decide⟩ :
        Fin 3 ≃ {x // x ≠ (0 : Fin 4)})
      = ![cex_v 1 - cex_v 0, cex_v 2 - cex_v 0, cex_v 3 - cex_v 0] := by
    funext t
    fin_cases t <;> rfl
  rw [hcomp]
  exact hli

/-- The claimed normals satisfy the outward-normal conditions. -/
theorem cex_outwardNormals : IsOutwardNormals cex_v cex_n where
  norm_one := cex_unit
  flat i j k hj hk := by
    rw [inner_sub_right, cex_plane i j hj.symm, cex_plane i k hk.symm, sub_self]
  outward i j hij := by
    rw [inner_sub_right]
    have h1 := cex_inner_self i
    have h2 := cex_plane i j hij.symm
    linarith

/-- The counterexample tetrahedron, packaged. -/
theorem cex_part2 :
    ∃ v n : Fin 4 → Pt, AffineIndependent ℝ v ∧ IsOutwardNormals v n ∧
      (∀ i j : Fin 4, i ≠ j → (i, j) ≠ (0, 3) → (i, j) ≠ (3, 0) →
        dihedralAngle n i j = dihedralAngle n 0 1) ∧
      ¬ IsRegularTetrahedron v :=
  ⟨cex_v, cex_n, cex_ai, cex_outwardNormals, cex_dihed, cex_notreg⟩

snip end

/-- **USAMO 1978, Problem 4, first part.**  If the angle between each pair of
faces of a tetrahedron is equal, then the tetrahedron is regular.

The tetrahedron is given by its affinely independent (non-degenerate) vertices
`v : Fin 4 → Pt`.  The dihedral angles are expressed through the (unique)
family `n` of outward unit normals to the faces — the interior dihedral angle
along the edge shared by faces `i` and `j` equals `π` minus the angle between
`n i` and `n j` — so the hypothesis `heq` says that all six dihedral angles
coincide. -/
problem usa1978_p4_part1 {v : Fin 4 → Pt} (hv : AffineIndependent ℝ v)
    (heq : ∀ n : Fin 4 → Pt, IsOutwardNormals v n → ∀ i j k l : Fin 4,
      i ≠ j → k ≠ l → dihedralAngle n i j = dihedralAngle n k l) :
    IsRegularTetrahedron v := by
  obtain ⟨n, hn⟩ := exists_isOutwardNormals hv
  apply regular_of_normals hn
  intro i j k l hij hkl
  have h1 := heq n hn i j k l hij hkl
  have h2 : InnerProductGeometry.angle (n i) (n j) =
      InnerProductGeometry.angle (n k) (n l) := by
    unfold dihedralAngle at h1
    linarith
  have ha : ∀ a b : Fin 4, ⟪n a, n b⟫_ℝ / (‖n a‖ * ‖n b‖) = ⟪n a, n b⟫_ℝ := by
    intro a b
    rw [hn.norm_one a, hn.norm_one b, mul_one, div_one]
  have hij1 : -1 ≤ ⟪n i, n j⟫_ℝ ∧ ⟪n i, n j⟫_ℝ ≤ 1 := by
    have habs := abs_real_inner_le_norm (n i) (n j)
    rw [hn.norm_one i, hn.norm_one j, mul_one] at habs
    exact ⟨neg_le_of_abs_le habs, le_of_abs_le habs⟩
  have hkl1 : -1 ≤ ⟪n k, n l⟫_ℝ ∧ ⟪n k, n l⟫_ℝ ≤ 1 := by
    have habs := abs_real_inner_le_norm (n k) (n l)
    rw [hn.norm_one k, hn.norm_one l, mul_one] at habs
    exact ⟨neg_le_of_abs_le habs, le_of_abs_le habs⟩
  have h3 : Real.arccos (⟪n i, n j⟫_ℝ) = Real.arccos (⟪n k, n l⟫_ℝ) := by
    unfold InnerProductGeometry.angle at h2
    rwa [ha i j, ha k l] at h2
  exact (Real.arccos_inj hij1.1 hij1.2 hkl1.1 hkl1.2).mp h3

/-- **USAMO 1978, Problem 4, second part.**  A tetrahedron does *not* have to
be regular if five of the six angles between its faces are equal: the explicit
tetrahedron `cex_v` with outward unit normals `cex_n` (see the `snip` section
above) has five equal dihedral angles — only the one along the edge shared by
faces `0` and `3` differs — but its squared edge lengths take both values `84`
and `144`, so it is not regular. -/
problem usa1978_p4_part2 :
    ∃ v n : Fin 4 → Pt, AffineIndependent ℝ v ∧ IsOutwardNormals v n ∧
      (∀ i j : Fin 4, i ≠ j → (i, j) ≠ (0, 3) → (i, j) ≠ (3, 0) →
        dihedralAngle n i j = dihedralAngle n 0 1) ∧
      ¬ IsRegularTetrahedron v :=
  cex_part2

end Usa1978P4
