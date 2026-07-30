/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Tactic.LinearCombination
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics, .Geometry] }

/-!
# USA Mathematical Olympiad 1973, Problem 3

Three vertices of a regular 2n+1 sided polygon are chosen at random.
Find the probability that the center of the polygon lies inside the
resulting triangle.
-/

namespace Usa1973P3

/-- The vertices of a regular `2n+1`-gon, identified with `ZMod (2n+1)`. -/
abbrev Vert (n : ℕ) := ZMod (2 * n + 1)

/-- A "triangle": a set of three distinct vertices of the polygon. -/
abbrev Triangle (n : ℕ) := {S : Finset (Vert n) // S.card = 3}

/-- The arc of `n + 1` consecutive vertices starting at `v`.
It spans `n` of the `2n+1` edges, i.e. strictly less than half the perimeter,
so it is the combinatorial counterpart of a closed semicircle. -/
def arc (n : ℕ) (v : Vert n) : Finset (Vert n) :=
  (Finset.range (n + 1)).image fun i : ℕ ↦ v + (i : Vert n)

/-- The arc with its starting point removed. -/
def arcTail (n : ℕ) (v : Vert n) : Finset (Vert n) := (arc n v).erase v

/-- A triangle fails to contain the center of the polygon iff its vertices are
contained in some closed semicircle. Since `2n+1` is odd there are no antipodal
pairs of vertices, and this happens iff the triangle is contained in `arc n v`
for one of its vertices `v` (the first vertex met after the unique gap of at
least `n+1` consecutive unchosen vertices). -/
abbrev IsBad (n : ℕ) (S : Finset (Vert n)) : Prop := ∃ v ∈ S, S ⊆ arc n v

/-- The event that the center of the polygon lies inside the triangle. -/
def goodTriangles (n : ℕ) : Set (Triangle n) := {S | ¬ IsBad n S.1}

snip begin

lemma triangle_nonempty {n : ℕ} (hn : 1 ≤ n) : Nonempty (Triangle n) := by
  have hm : 2 < 2 * n + 1 := by omega
  have h12 : (1 : Vert n) ≠ 2 := by
    have h' : ((1 : ℕ) : Vert n) ≠ ((2 : ℕ) : Vert n) := by
      rw [ne_eq, ZMod.natCast_eq_natCast_iff' 1 2 (2 * n + 1),
        Nat.mod_eq_of_lt (by omega : 1 < 2 * n + 1), Nat.mod_eq_of_lt hm]
      decide
    rwa [Nat.cast_one, Nat.cast_ofNat] at h'
  have h01 : (0 : Vert n) ≠ 1 := by
    have h' : ((0 : ℕ) : Vert n) ≠ ((1 : ℕ) : Vert n) := by
      rw [ne_eq, ZMod.natCast_eq_natCast_iff' 0 1 (2 * n + 1), Nat.zero_mod,
        Nat.mod_eq_of_lt (by omega : 1 < 2 * n + 1)]
      decide
    rwa [Nat.cast_zero, Nat.cast_one] at h'
  have h02 : (0 : Vert n) ≠ 2 := by
    have h' : ((0 : ℕ) : Vert n) ≠ ((2 : ℕ) : Vert n) := by
      rw [ne_eq, ZMod.natCast_eq_natCast_iff' 0 2 (2 * n + 1), Nat.zero_mod,
        Nat.mod_eq_of_lt hm]
      decide
    rwa [Nat.cast_zero, Nat.cast_ofNat] at h'
  exact ⟨⟨{0, 1, 2}, by
    rw [Finset.card_insert_of_notMem (by simp [h01, h02]),
      Finset.card_insert_of_notMem (by simp [h12]), Finset.card_singleton]⟩⟩

lemma mem_arc {n : ℕ} {v w : Vert n} :
    w ∈ arc n v ↔ ∃ i, i ≤ n ∧ v + (i : Vert n) = w := by
  simp only [arc, Finset.mem_image, Finset.mem_range, Nat.lt_succ_iff]

lemma card_arc {n : ℕ} (v : Vert n) : (arc n v).card = n + 1 := by
  rw [arc, Finset.card_image_of_injOn, Finset.card_range]
  intro a ha b hb hab
  simp only [Finset.coe_range, Set.mem_Iio] at ha hb
  have h := add_left_cancel hab
  rw [ZMod.natCast_eq_natCast_iff' a b (2 * n + 1)] at h
  rwa [Nat.mod_eq_of_lt (by omega : a < 2 * n + 1),
    Nat.mod_eq_of_lt (by omega : b < 2 * n + 1)] at h

lemma self_mem_arc {n : ℕ} (v : Vert n) : v ∈ arc n v := by
  rw [mem_arc]
  exact ⟨0, Nat.zero_le n, by simp⟩

lemma card_arcTail {n : ℕ} (v : Vert n) : (arcTail n v).card = n := by
  rw [arcTail, Finset.card_erase_of_mem (self_mem_arc v), card_arc, Nat.add_sub_cancel]

/-- If `w` lies in the tail of the arc starting at `v`, then `v` does not lie
in the tail of the arc starting at `w`: the two arcs together would cover more
than the whole polygon. -/
lemma not_mem_arcTail_of_mem_arcTail {n : ℕ} {v w : Vert n}
    (h : w ∈ arcTail n v) : v ∉ arcTail n w := by
  rw [arcTail, Finset.mem_erase] at h
  obtain ⟨hne, harc⟩ := h
  rw [mem_arc] at harc
  obtain ⟨i, hi, rfl⟩ := harc
  have hi0 : i ≠ 0 := by
    intro h0
    apply hne
    rw [h0, Nat.cast_zero, add_zero]
  intro hv
  rw [arcTail, Finset.mem_erase] at hv
  obtain ⟨hne2, harc2⟩ := hv
  rw [mem_arc] at harc2
  obtain ⟨j, hj, hjv⟩ := harc2
  have hj0 : j ≠ 0 := by
    intro h0
    apply hne2
    rw [h0, Nat.cast_zero, add_zero] at hjv
    exact hjv.symm
  have hij : ((i + j : ℕ) : Vert n) = 0 := by
    have h1 : v + ((i : Vert n) + (j : Vert n)) = v + 0 := by
      rw [add_zero, ← add_assoc]
      exact hjv
    have h2 := add_left_cancel h1
    rwa [← Nat.cast_add] at h2
  rw [ZMod.natCast_eq_zero_iff] at hij
  have hpos : 0 < i + j := Nat.add_pos_left (Nat.pos_of_ne_zero hi0) j
  have hle := Nat.le_of_dvd hpos hij
  omega

/-- Witnesses for badness: a vertex `v` together with two more vertices chosen
from the tail of the arc starting at `v`. -/
abbrev BadWitness (n : ℕ) :=
  Σ v : Vert n, {T : Finset (Vert n) // T ⊆ arcTail n v ∧ T.card = 2}

/-- The bad triangle built from a witness. -/
def badTriangleOfWitness {n : ℕ} (w : BadWitness n) : {S : Triangle n // IsBad n S.1} :=
  ⟨⟨insert w.1 w.2.1, by
      rw [Finset.card_insert_of_notMem (fun h ↦ Finset.notMem_erase _ _ (w.2.2.1 h)),
        w.2.2.2]⟩,
    ⟨w.1, Finset.mem_insert_self _ _,
      Finset.insert_subset (self_mem_arc _)
        (Finset.Subset.trans w.2.2.1 (Finset.erase_subset _ _))⟩⟩

lemma badTriangleOfWitness_bijective {n : ℕ} :
    Function.Bijective (badTriangleOfWitness (n := n)) := by
  constructor
  · rintro ⟨v, T, hTsub, hTcard⟩ ⟨v', T', hT'sub, hT'card⟩ heq
    have heq2 : insert v T = insert v' T' :=
      Subtype.ext_iff.mp (Subtype.ext_iff.mp heq)
    have hv_notin : v ∉ T := fun h ↦ Finset.notMem_erase _ _ (hTsub h)
    have hv'_notin : v' ∉ T' := fun h ↦ Finset.notMem_erase _ _ (hT'sub h)
    have hvv : v ∈ insert v' T' := heq2 ▸ Finset.mem_insert_self v T
    have hvv' : v' ∈ insert v T := heq2.symm ▸ Finset.mem_insert_self v' T'
    rw [Finset.mem_insert] at hvv hvv'
    by_cases h : v = v'
    · subst h
      have hTT : T = T' := by
        have e := congrArg (Finset.erase · v) heq2
        rwa [Finset.erase_insert hv_notin, Finset.erase_insert hv'_notin] at e
      subst hTT
      rfl
    · exfalso
      have hvT' : v ∈ T' := by
        rcases hvv with h1 | h1
        · exact absurd h1 h
        · exact h1
      have hv'T : v' ∈ T := by
        rcases hvv' with h2 | h2
        · exact absurd h2 (Ne.symm h)
        · exact h2
      exact not_mem_arcTail_of_mem_arcTail (hT'sub hvT') (hTsub hv'T)
  · rintro ⟨S, hbad⟩
    obtain ⟨v, hvS, hSsub⟩ := hbad
    refine ⟨⟨v, S.1.erase v, ?_, ?_⟩, ?_⟩
    · intro w hw
      rw [Finset.mem_erase] at hw
      rw [arcTail, Finset.mem_erase]
      exact ⟨hw.1, hSsub hw.2⟩
    · rw [Finset.card_erase_of_mem hvS, S.2]
    · apply Subtype.ext
      apply Subtype.ext
      show insert v (S.1.erase v) = S.1
      exact Finset.insert_erase hvS

lemma card_badWitness_fiber {n : ℕ} (v : Vert n) :
    Fintype.card {T : Finset (Vert n) // T ⊆ arcTail n v ∧ T.card = 2} = n.choose 2 := by
  classical
  have e : {T : Finset (Vert n) // T ⊆ arcTail n v ∧ T.card = 2} ≃
      {T : Finset (Vert n) // T ∈ (arcTail n v).powersetCard 2} :=
    Equiv.subtypeEquivRight fun T ↦ (Finset.mem_powersetCard).symm
  rw [Fintype.card_congr e, Fintype.card_coe, Finset.card_powersetCard, card_arcTail]

/-- Every bad triangle arises from exactly one witness: the starting vertex `v`
of the covering arc is the unique vertex of the triangle that follows the
unique gap of at least `n+1` unchosen vertices. -/
lemma card_badTriangles {n : ℕ} :
    Fintype.card {S : Triangle n // IsBad n S.1} = (2 * n + 1) * n.choose 2 := by
  classical
  rw [← Fintype.card_of_bijective (badTriangleOfWitness_bijective (n := n)),
    Fintype.card_sigma]
  simp only [card_badWitness_fiber, Finset.sum_const, Finset.card_univ, ZMod.card,
    nsmul_eq_mul, Nat.cast_id]

lemma card_triangles {n : ℕ} : Fintype.card (Triangle n) = (2 * n + 1).choose 3 := by
  classical
  rw [Fintype.card_subtype]
  have h : Finset.univ.filter (fun S : Finset (Vert n) ↦ S.card = 3) =
      Finset.univ.powersetCard 3 := by
    ext S
    simp [Finset.mem_powersetCard]
  rw [h, Finset.card_powersetCard, Finset.card_univ, ZMod.card]

lemma card_good_add_card_bad {n : ℕ} :
    Fintype.card {S : Triangle n // ¬ IsBad n S.1} +
        Fintype.card {S : Triangle n // IsBad n S.1} =
      Fintype.card (Triangle n) := by
  classical
  rw [Fintype.card_subtype_compl]
  exact Nat.sub_add_cancel (Fintype.card_subtype_le _)

lemma two_mul_choose_two (n : ℕ) : 2 * n.choose 2 = n * (n - 1) := by
  have h := Nat.descFactorial_eq_factorial_mul_choose n 2
  have hd : n.descFactorial 2 = (n - 1) * n := by
    simp [Nat.descFactorial_succ, Nat.descFactorial_zero]
  rw [hd, show Nat.factorial 2 = 2 from rfl] at h
  rw [← h]
  exact Nat.mul_comm _ _

lemma six_mul_choose_three (m : ℕ) : 6 * m.choose 3 = m * ((m - 1) * (m - 2)) := by
  have h := Nat.descFactorial_eq_factorial_mul_choose m 3
  have hd : m.descFactorial 3 = (m - 2) * ((m - 1) * m) := by
    simp [Nat.descFactorial_succ, Nat.descFactorial_zero]
  rw [hd, show Nat.factorial 3 = 6 from rfl] at h
  rw [← h]
  ring

/-- The key arithmetic identity: with `G` good, `B` bad and `T` total
triangles, `(4n-2) * G = (n+1) * T`. -/
lemma key_identity {G B T : ℕ} (n : ℕ) (hn : 1 ≤ n)
    (hsum : G + B = T) (hB : B = (2 * n + 1) * n.choose 2)
    (hT : T = (2 * n + 1).choose 3) :
    (4 * n - 2) * G = (n + 1) * T := by
  have hsumz : (G : ℤ) + (B : ℤ) = (T : ℤ) := by exact_mod_cast hsum
  have h2 : (2 : ℤ) * (n.choose 2 : ℤ) = (n : ℤ) * ((n : ℤ) - 1) := by
    have e := congrArg (fun x : ℕ ↦ (x : ℤ)) (two_mul_choose_two n)
    simp only [Nat.cast_mul, Nat.cast_ofNat] at e
    rwa [Nat.cast_sub hn, Nat.cast_one] at e
  have hBz : (2 : ℤ) * (B : ℤ) = (2 * (n : ℤ) + 1) * ((n : ℤ) * ((n : ℤ) - 1)) := by
    rw [hB]
    push_cast
    linear_combination (2 * (n : ℤ) + 1) * h2
  have hTz : (6 : ℤ) * (T : ℤ) =
      (2 * (n : ℤ) + 1) * ((2 * (n : ℤ)) * (2 * (n : ℤ) - 1)) := by
    have e := six_mul_choose_three (2 * n + 1)
    rw [show 2 * n + 1 - 1 = 2 * n by omega, show 2 * n + 1 - 2 = 2 * n - 1 by omega] at e
    have e' := congrArg (fun x : ℕ ↦ (x : ℤ)) e
    rw [hT]
    simp only [Nat.cast_mul, Nat.cast_ofNat] at e'
    rw [Nat.cast_sub (show 1 ≤ 2 * n by omega), Nat.cast_one] at e'
    push_cast at e'
    linear_combination e'
  have keyZ : 4 * (n : ℤ) * (G : ℤ) = ((n : ℤ) + 1) * (T : ℤ) + 2 * (G : ℤ) := by
    have key2 : 2 * (4 * (n : ℤ) * (G : ℤ)) =
        2 * (((n : ℤ) + 1) * (T : ℤ) + 2 * (G : ℤ)) := by
      linear_combination (8 * (n : ℤ) - 4) * hsumz + (2 - 4 * (n : ℤ)) * hBz +
        ((n : ℤ) - 1) * hTz
    exact mul_left_cancel₀ (two_ne_zero) key2
  have key4 : 4 * n * G = (n + 1) * T + 2 * G := by exact_mod_cast keyZ
  calc (4 * n - 2) * G = 4 * n * G - 2 * G := Nat.sub_mul _ _ _
    _ = (n + 1) * T + 2 * G - 2 * G := by rw [key4]
    _ = (n + 1) * T := Nat.add_sub_cancel _ _

snip end

noncomputable determine solution (n : ℕ) : ENNReal :=
  ((n + 1 : ℕ) : ENNReal) / ((4 * n - 2 : ℕ) : ENNReal)

/-- The uniform distribution on the set of triangles. -/
noncomputable def trianglePMF (n : ℕ) (hn : 1 ≤ n) : PMF (Triangle n) :=
  @PMF.uniformOfFintype (Triangle n) inferInstance (triangle_nonempty hn)

problem usa1973_p3 (n : ℕ) (hn : 1 ≤ n) :
    (trianglePMF n hn).toOuterMeasure (goodTriangles n) = solution n := by
  classical
  have hsum := card_good_add_card_bad (n := n)
  have hB := card_badTriangles (n := n)
  have hT := card_triangles (n := n)
  have key := key_identity n hn hsum hB hT
  rw [trianglePMF, PMF.uniformOfFintype, PMF.toOuterMeasure_uniformOfFinset_apply]
  simp only [goodTriangles, Set.mem_setOf_eq]
  rw [← Fintype.card_subtype (fun S : Triangle n ↦ ¬ IsBad n S.1), Finset.card_univ]
  -- goal: ↑G / ↑(Fintype.card (Triangle n)) = ↑((n+1)) / ↑((4*n-2))
  rw [solution]
  have hTpos : (0 : ENNReal) < (Fintype.card (Triangle n) : ENNReal) := by
    rw [hT]
    have h3 : 3 ≤ 2 * n + 1 := by omega
    exact_mod_cast Nat.choose_pos h3
  have h42pos : (0 : ENNReal) < ((4 * n - 2 : ℕ) : ENNReal) := by
    have : 0 < 4 * n - 2 := by omega
    exact_mod_cast this
  rw [ENNReal.div_eq_div_iff h42pos.ne' (ENNReal.natCast_ne_top _) hTpos.ne'
    (ENNReal.natCast_ne_top _)]
  -- goal: ↑((4*n-2)) * ↑G = ↑(Fintype.card (Triangle n)) * ↑(n+1)
  have key' : (4 * n - 2) *
      Fintype.card {S : Triangle n // ¬ IsBad n S.1} =
      Fintype.card (Triangle n) * (n + 1) := key.trans (Nat.mul_comm _ _)
  exact_mod_cast key'

end Usa1973P3
