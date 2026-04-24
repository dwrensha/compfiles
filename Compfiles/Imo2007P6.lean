/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Rydh, Codex
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 2007, Problem 6

Let n be a positive integer. Consider
  S = {(x, y, z) : x, y, z ∈ {0, 1, ... , n}, x + y + z > 0}
as a set of (n + 1)³ - 1 points in three-dimensional space. Determine the smallest possible
number of planes, the union of which contains S but does not include (0, 0, 0).
-/

namespace Imo2007P6

abbrev Point := Fin 3 → ℝ

structure Plane where
  poly : MvPolynomial (Fin 3) ℝ
  totalDegree_eq_one : poly.totalDegree = 1

def coordSet (n : ℕ) : Finset ℝ := (Finset.range (n + 1)).map ⟨Nat.cast, Nat.cast_injective⟩
def S (n : ℕ) : Set Point := { p | (∀ i : Fin 3, p i ∈ coordSet n) ∧ p 0 + p 1 + p 2 > 0 }
def IsAdmissible (n : ℕ) (T : Finset Plane) : Prop :=
  (∀ p ∈ S n, ∃ P ∈ T, P.poly.eval p = 0) ∧
  (∀ P ∈ T, P.poly.eval 0 ≠ 0)

determine solution_value (n : ℕ+) : ℕ := 3 * n

snip begin

noncomputable def rootFactor (i : Fin 3) (x : ℝ) : MvPolynomial (Fin 3) ℝ :=
  MvPolynomial.X i - MvPolynomial.C x

lemma coeff_rootFactor (i : Fin 3) (x : ℝ) :
    MvPolynomial.coeff (Finsupp.single i 1) (rootFactor i x) = 1 := by
  simp [rootFactor, MvPolynomial.coeff_sub, MvPolynomial.coeff_C]
  intro h
  simpa using (DFunLike.congr (x := i) h rfl)

lemma totalDegree_rootFactor (i : Fin 3) (x : ℝ) : (rootFactor i x).totalDegree = 1 := by
  apply le_antisymm
  · simpa [rootFactor] using MvPolynomial.totalDegree_sub_C_le (MvPolynomial.X i) x
  · have : Finsupp.single i 1 ∈ (rootFactor i x).support := by
      simp [MvPolynomial.mem_support_iff, coeff_rootFactor]
    simpa using MvPolynomial.le_totalDegree this

noncomputable def rootPlane {n : ℕ} (i : Fin 3) (k : Fin n) : Plane where
  poly := rootFactor i ((k.val + 1 : ℕ) : ℝ)
  totalDegree_eq_one := totalDegree_rootFactor i _

lemma rootFactor_inj {i j : Fin 3} {r s : ℝ} (h : rootFactor i r = rootFactor j s) : i = j ∧ r = s := by
  have hrs : r = s := by
    have heval := congrArg (fun P => MvPolynomial.eval (0 : Fin 3 → ℝ) P) h
    simp [rootFactor] at heval
    linarith
  constructor
  · by_contra hij
    have hcoeff := congrArg (MvPolynomial.coeff (Finsupp.single i 1)) h
    simp [rootFactor, MvPolynomial.coeff_sub, MvPolynomial.coeff_C, Finsupp.ext_iff, hrs] at hcoeff
    exact hij hcoeff.symm
  · exact hrs

lemma rootPlane_injective {n : ℕ} : Function.Injective (fun p : Fin 3 × Fin n => rootPlane p.1 p.2) := by
  intro p q hpq
  obtain ⟨hij, hkl_val_succ⟩ := rootFactor_inj (congrArg Plane.poly hpq)
  have hval : p.2.val = q.2.val := by exact_mod_cast (Nat.succ.inj (by exact_mod_cast hkl_val_succ))
  exact Prod.ext hij (Fin.ext hval)

noncomputable def examplePlanes (n : ℕ) : Finset Plane :=
  Finset.univ.map ⟨fun p : Fin 3 × Fin n => rootPlane p.1 p.2, rootPlane_injective⟩

lemma solution_example (n : ℕ+) : ∃ T : Finset Plane, IsAdmissible n T ∧ T.card = 3 * n := by
  refine ⟨examplePlanes n, ?_, by simp [examplePlanes]⟩
  constructor
  · intro p hp
    simp [S, coordSet] at hp
    obtain ⟨i, hi_pos⟩ : ∃ i : Fin 3, 0 < p i := by grind only [Fin.sum_univ_three]
    rcases hp.1 i with ⟨x, hx_le, hx_eq⟩
    have hx_pos : 0 < x := by exact_mod_cast (show (0 : ℝ) < x by simpa [hx_eq] using hi_pos)
    let k : Fin n.val := ⟨x - 1, by lia⟩
    have hk : (((k.val + 1 : ℕ) : ℝ)) = p i := by
      rw [← hx_eq]
      exact_mod_cast Nat.sub_add_cancel hx_pos
    exact ⟨rootPlane i k, by simp [examplePlanes], by simp [rootPlane, rootFactor, hk]⟩
  · intro P hP
    rcases Finset.mem_map.mp hP with ⟨q, _, rfl⟩
    rcases q with ⟨i, k⟩
    have hk : (0 : ℝ) < ((k.val + 1 : ℕ) : ℝ) := by positivity
    simp [rootPlane, rootFactor]
    linarith

noncomputable instance : DecidableEq Plane := Classical.decEq _

lemma totalDegree_finset_prod_of_isDomain {ι : Type*} [DecidableEq ι]
    {s : Finset ι} {f : ι → MvPolynomial (Fin 3) ℝ} :
    (∀ i ∈ s, f i ≠ 0) → (∏ i ∈ s, f i).totalDegree = ∑ i ∈ s, (f i).totalDegree := by
  refine Finset.induction_on s (fun _ ↦ by simp) ?_
  intro i T hiT hT hf
  have hT_degree := hT (fun j hj => hf j (Finset.mem_insert_of_mem hj))
  rw [Finset.prod_insert hiT, Finset.sum_insert hiT]
  rw [MvPolynomial.totalDegree_mul_of_isDomain (hf i (Finset.mem_insert_self i T)), hT_degree]
  exact (Finset.prod_ne_zero_iff).mpr fun j hj => hf j (Finset.mem_insert_of_mem hj)

noncomputable def planeProduct (T : Finset Plane) : MvPolynomial (Fin 3) ℝ := ∏ P ∈ T, P.poly

lemma Plane_ne_zero {P : Plane} : P.poly ≠ 0 := by
  by_contra
  have : (0 : MvPolynomial (Fin 3) ℝ).totalDegree = 1 := by rw [← this, P.totalDegree_eq_one]
  simp_all only [MvPolynomial.totalDegree_zero, zero_ne_one]

lemma planeProduct_totalDegree (T : Finset Plane) : (planeProduct T).totalDegree = T.card := by
  rw [planeProduct, totalDegree_finset_prod_of_isDomain]
  · simp [Plane.totalDegree_eq_one]
  · exact fun P _ ↦ Plane_ne_zero

lemma origin_not_mem_admissible_plane {P : Plane} {T : Finset Plane} {n : ℕ+}
    (h_mem : P ∈ T) (h_admissible : IsAdmissible n T) : P.poly.eval 0 ≠ 0 := h_admissible.2 P h_mem

lemma planeProduct_eval_zero_ne_zero {T : Finset Plane} {n : ℕ+} (h : IsAdmissible n T) :
    (planeProduct T).eval 0 ≠ 0 := by
  simp only [planeProduct, map_prod, Finset.prod_ne_zero_iff]
  exact fun _ hP ↦ origin_not_mem_admissible_plane hP h

lemma planeProduct_eval_eq_zero_of_mem {T : Finset Plane} {p : Point} {P : Plane}
    (hP : P ∈ T) (hp : P.poly.eval p = 0) : (planeProduct T).eval p = 0 := by
  simpa [planeProduct, map_prod] using Finset.prod_eq_zero hP hp

noncomputable def rootsInCoord (S : Fin 3 → Finset ℝ) (i : Fin 3) := ∏ x ∈ S i, rootFactor i x

noncomputable def PolyFromRoots (S : Fin 3 → Finset ℝ) := ∏ i : Fin 3, rootsInCoord S i

lemma rootFactor_ne_zero (i : Fin 3) (x : ℝ) : rootFactor i x ≠ 0 :=
  fun hzero ↦ by simpa [hzero] using coeff_rootFactor i x

lemma totalDegree_rootsInCoord (S : Fin 3 → Finset ℝ) (i : Fin 3) :
    (rootsInCoord S i).totalDegree = (S i).card := by
  rw [rootsInCoord, totalDegree_finset_prod_of_isDomain]
  · simp [totalDegree_rootFactor]
  · exact fun x _ ↦ rootFactor_ne_zero i x

lemma rootsInCoord_ne_zero (S : Fin 3 → Finset ℝ) (i : Fin 3) : rootsInCoord S i ≠ 0 :=
  (Finset.prod_ne_zero_iff).mpr (fun x _ => rootFactor_ne_zero i x)

lemma totalDegree_PolyFromRoots {S : Fin 3 → Finset ℝ} {A : MvPolynomial (Fin 3) ℝ} :
    A = PolyFromRoots S → A.totalDegree = ∑ i, (S i).card := fun hA ↦ by
  rw [hA, PolyFromRoots, totalDegree_finset_prod_of_isDomain]
  · simp [totalDegree_rootsInCoord]
  · exact fun i _ ↦ rootsInCoord_ne_zero S i

lemma coeff_rootFactor_mul_top {p : MvPolynomial (Fin 3) ℝ} {t : Fin 3 →₀ ℕ}
    {i : Fin 3} {x : ℝ} (hpdeg : p.totalDegree = t.degree) (hpcoeff : p.coeff t = 1) :
    (rootFactor i x * p).coeff (t + Finsupp.single i 1) = 1 := by
  have hC : MvPolynomial.coeff (t + Finsupp.single i 1) (MvPolynomial.C x * p) = 0 := by
    rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_eq_zero_of_totalDegree_lt, mul_zero]
    rw [hpdeg, ← Finsupp.degree_apply, map_add, Finsupp.degree_single]
    lia
  simp [rootFactor, sub_mul, MvPolynomial.coeff_sub, MvPolynomial.coeff_X_mul', hpcoeff, hC]

lemma coeff_rootFactorFinset_mul_top (s : Finset ℝ) (i : Fin 3)
    {p : MvPolynomial (Fin 3) ℝ} {t : Fin 3 →₀ ℕ}
    (hpdeg : p.totalDegree = t.degree) (hpcoeff : p.coeff t = 1) :
    ((∏ x ∈ s, rootFactor i x) * p).coeff (t + Finsupp.single i s.card) = 1 := by
  induction s using Finset.induction_on with
  | empty => simp [hpcoeff]
  | insert x T hxT hT =>
      have hprevdeg : ((∏ x ∈ T, rootFactor i x) * p).totalDegree =
          (t + Finsupp.single i T.card).degree := by
        have hpne : p ≠ 0 := fun hp ↦ by simp [hp] at hpcoeff
        have hprod_ne : (∏ x ∈ T, rootFactor i x) ≠ 0 :=
          (Finset.prod_ne_zero_iff).mpr (fun z _ => rootFactor_ne_zero i z)
        rw [MvPolynomial.totalDegree_mul_of_isDomain hprod_ne hpne]
        rw [totalDegree_finset_prod_of_isDomain (fun z _ => rootFactor_ne_zero i z)]
        simp [hpdeg, totalDegree_rootFactor, map_add, Finsupp.degree_single]
        lia
      rw [Finset.prod_insert hxT, Finset.card_insert_of_notMem hxT, mul_assoc]
      convert coeff_rootFactor_mul_top hprevdeg hT using 2
      ext j
      simp [add_assoc]

lemma coeff_rootsInCoordFinset_top (S : Fin 3 → Finset ℝ) (U : Finset (Fin 3)) :
    (∏ i ∈ U, rootsInCoord S i).coeff (∑ i ∈ U, Finsupp.single i (S i).card) = 1 := by
  induction U using Finset.induction_on with
  | empty => simp
  | insert i T hiT hT =>
      have hprevdeg : (∏ i ∈ T, rootsInCoord S i).totalDegree =
          (∑ i ∈ T, Finsupp.single i (S i).card).degree := by
        rw [totalDegree_finset_prod_of_isDomain (fun j _ => rootsInCoord_ne_zero S j)]
        simp [totalDegree_rootsInCoord]
      rw [Finset.prod_insert hiT, Finset.sum_insert hiT, rootsInCoord]
      convert coeff_rootFactorFinset_mul_top (S i) i hprevdeg hT using 2
      grind only

lemma coeff_card {S : Fin 3 → Finset ℝ} {A : MvPolynomial (Fin 3) ℝ}
    {t : Fin 3 →₀ ℕ} (hA : A = PolyFromRoots S) (ht : ∀ i, t i = (S i).card) :
    A.coeff t = 1 := by
  rw [hA, PolyFromRoots]
  convert coeff_rootsInCoordFinset_top S Finset.univ using 2
  ext i
  fin_cases i <;> simp [Fin.sum_univ_three, ht]

lemma eval_rootsInCoord_eq_zero {S : Fin 3 → Finset ℝ} {p : Point} {i : Fin 3}
    (hi : p i ∈ S i) : (rootsInCoord S i).eval p = 0 := by
  simpa [rootsInCoord] using (Finset.prod_eq_zero hi (by simp [rootFactor]))

lemma zeros {S : Fin 3 → Finset ℝ} {A : MvPolynomial (Fin 3) ℝ} :
    A = PolyFromRoots S → ∀ p, (∃ i, p i ∈ S i) → A.eval p = 0 := by
  intro hA p hp
  rcases hp with ⟨i, hi⟩
  simpa [hA, PolyFromRoots] using
    (Finset.prod_eq_zero (Finset.mem_univ i) (eval_rootsInCoord_eq_zero hi))

def positiveCoordSet (n : ℕ) : Finset ℝ := (Finset.Icc 1 n).map ⟨Nat.cast, Nat.cast_injective⟩

lemma mem_S_of_mem_coordSet_of_ne_zero {n : ℕ} {p : Point}
    (hp : ∀ i : Fin 3, p i ∈ coordSet n) (hp_ne : p ≠ 0) : p ∈ S n := by
  refine ⟨hp, ?_⟩
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hp_ne
  simp [coordSet] at hp
  have : ∀ i, 0 ≤ p i := by intro i ; obtain ⟨a, ha⟩ := hp i ; simp [← ha.2]
  have hpj_pos : 0 < p j := by
    have hpj_ne_zero : p j ≠ 0 := RCLike.ofReal_ne_zero.mp hj
    exact lt_of_le_of_ne (this j) hpj_ne_zero.symm
  have h_ex : ∃ i ∈ Finset.univ, 0 < p i := ⟨j, Finset.mem_univ j, hpj_pos⟩
  fin_cases j <;> simp at hpj_pos <;> grind

lemma exists_poly_of_IsAdmissible {n : ℕ+} {T : Finset Plane} (hT : IsAdmissible n T) :
    ∃ B : MvPolynomial (Fin 3) ℝ, B.totalDegree = T.card ∧ B.eval 0 ≠ 0 ∧ ∀ p ∈ S n, B.eval p = 0 := by
  refine ⟨planeProduct T, planeProduct_totalDegree T, planeProduct_eval_zero_ne_zero hT, ?_⟩
  intro p hp
  rcases hT.1 p hp with ⟨P, hP, hP_zero⟩
  exact planeProduct_eval_eq_zero_of_mem hP hP_zero

lemma min_total_degree {n : ℕ} {B : MvPolynomial (Fin 3) ℝ}
    (hB_origin : B.eval 0 ≠ 0) (hB_zero : ∀ p ∈ S n, B.eval p = 0) :
    3 * n ≤ B.totalDegree := by
  by_contra h_deg_less
  simp at h_deg_less

  let Spos : Fin 3 → Finset ℝ := fun _ => positiveCoordSet n
  let A := PolyFromRoots Spos
  let α := (A.eval 0) / (B.eval 0)
  let P := A - α • B
  let t : Fin 3 →₀ ℕ := Finsupp.equivFunOnFinite.symm ![n, n, n]
  have ht_degree : t.degree = 3 * n := by
    have : ∀ i, ![n, n, n] i = n := fun i ↦ by fin_cases i <;> simp
    simp [t, Finsupp.equivFunOnFinite_symm_eq_sum, this]

  have hP_coeff : P.coeff t = 1 := by
    have hA_coeff : A.coeff t = 1 := by
      apply coeff_card (A := A) rfl
      intro i
      fin_cases i <;> simp [t, Spos, positiveCoordSet]
    have hB_coeff : B.coeff t = 0 := by
      rw [MvPolynomial.coeff_eq_zero_of_totalDegree_lt]
      rwa [← Finsupp.degree_apply, ht_degree]
    have : P.coeff t = A.coeff t - α * B.coeff t := rfl
    simp [this, hA_coeff, hB_coeff]

  have hP_degree : P.totalDegree = t.degree := by
    rw [ht_degree]
    apply le_antisymm
    · have hmax : max A.totalDegree (α • B).totalDegree = 3 * n := by
        simp [totalDegree_PolyFromRoots (A := A) rfl, Spos, positiveCoordSet]
        calc
          (α • B).totalDegree ≤ B.totalDegree := MvPolynomial.totalDegree_smul_le α B
          _ ≤ 3 * n := le_of_lt h_deg_less
      simpa [P, hmax] using MvPolynomial.totalDegree_sub A (α • B)
    · by_contra ht_not_le
      have hcoeff_zero : P.coeff t = 0 := by
        rw [MvPolynomial.coeff_eq_zero_of_totalDegree_lt]
        rw [← Finsupp.degree_apply, ht_degree]
        exact Nat.lt_of_not_ge ht_not_le
      simp [hP_coeff] at hcoeff_zero

  have ht_grid : ∀ i : Fin 3, t i < (coordSet n).card := fun i ↦ by
    fin_cases i <;> simp [t, coordSet]
  rcases MvPolynomial.combinatorial_nullstellensatz_exists_eval_nonzero P t
    (ne_zero_of_eq_one hP_coeff) hP_degree (fun _ : Fin 3 => coordSet n) ht_grid with
    ⟨s, hs_grid, hP_eval_s_ne_zero⟩

  have hP_zero : ∀ p, (∀ i : Fin 3, p i ∈ coordSet n) → P.eval p = 0 := by
    intro p hp
    rw [MvPolynomial.eval_sub, MvPolynomial.smul_eval]
    by_cases hp_zero : p = 0
    · rw [hp_zero, div_mul_cancel₀ (A.eval 0) hB_origin, sub_self]
    · have hp_pos : ∃ i, p i ∈ Spos i := by
        obtain ⟨j, hj⟩ := Function.ne_iff.mp hp_zero
        use j
        simp [Spos, positiveCoordSet]
        simp [coordSet] at hp
        rcases hp j with ⟨a, ha_le, ha_eq⟩
        rw [← ha_eq] at hj
        have ha_pos : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr (by aesop)
        exact ⟨a, ⟨ha_pos, ha_le⟩, ha_eq⟩
      simpa [hB_zero p (mem_S_of_mem_coordSet_of_ne_zero hp hp_zero)] using zeros rfl p hp_pos

  exact hP_eval_s_ne_zero (hP_zero s hs_grid)

lemma solution_lowerBounds (n : ℕ+) :
    solution_value n ∈ lowerBounds {k | ∃ T : Finset Plane, IsAdmissible n T ∧ T.card = k} := by
  simp [mem_lowerBounds, solution_value]
  intro T hT
  rcases exists_poly_of_IsAdmissible hT with ⟨B, hB_degree, hB_origin, hB_zero⟩
  rw [← hB_degree]
  exact min_total_degree hB_origin hB_zero

snip end

problem imo2007_p6 (n : ℕ+) :
    IsLeast { k | ∃ T : Finset Plane, IsAdmissible n T ∧ T.card = k } (solution_value n) := by
  exact ⟨solution_example n, solution_lowerBounds n⟩

end Imo2007P6
