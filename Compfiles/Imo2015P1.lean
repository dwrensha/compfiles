/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
public import Mathlib.Data.Int.Star
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics, .Geometry] }

/-!
# International Mathematical Olympiad 2015, Problem 1

We say that a finite set S of points in the plane is balanced if, for any two
different points A and B in S, there is a point C in S such that AC = BC.
We say that S is centre-free if for any three different points A, B and C in S,
there are no points P in S such that PA = PB = PC.

(a) Show that for all integers n ≥ 3, there exists a balanced set consisting of
n points.

(b) Determine all integers n ≥ 3 for which there exists a balanced centre-free
set consisting of n points.
-/

namespace Imo2015P1

/-- A finite set of points in the plane (represented as complex numbers) is
*balanced* if for any two different points A and B in S, there is a point C in S
such that AC = BC. -/
def Balanced (S : Finset ℂ) : Prop :=
  ∀ A ∈ S, ∀ B ∈ S, A ≠ B → ∃ C ∈ S, dist A C = dist B C

/-- A finite set of points in the plane is *centre-free* if for any three
different points A, B and C in S, there is no point P in S such that
PA = PB = PC. -/
def CenterFree (S : Finset ℂ) : Prop :=
  ∀ A ∈ S, ∀ B ∈ S, ∀ C ∈ S, A ≠ B → B ≠ C → A ≠ C →
    ¬∃ P ∈ S, dist P A = dist P B ∧ dist P B = dist P C

/-- The answer to part (b): the odd integers `n ≥ 3`. -/
determine SolutionSet : Set ℕ := {n | Odd n}

snip begin

/-- The point on the unit circle at angle `2πa/n`. This is the building block
for all our constructions (regular polygons and circle-plus-centre
configurations). -/
noncomputable def polyPt (n a : ℤ) : ℂ :=
  Complex.exp (↑(2 * Real.pi * a / n) * Complex.I)

lemma polyPt_add (n a b : ℤ) : polyPt n (a + b) = polyPt n a * polyPt n b := by
  rw [polyPt, polyPt, polyPt, ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma polyPt_neg (n a : ℤ) : polyPt n (-a) = (polyPt n a)⁻¹ := by
  rw [polyPt, polyPt, ← Complex.exp_neg]
  congr 1
  push_cast
  ring

lemma polyPt_norm (n a : ℤ) : ‖polyPt n a‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

lemma polyPt_ne_zero (n a : ℤ) : polyPt n a ≠ 0 := Complex.exp_ne_zero _

lemma polyPt_re (n a : ℤ) : (polyPt n a).re = Real.cos (2 * Real.pi * a / n) :=
  Complex.exp_ofReal_mul_I_re _

lemma polyPt_conj (n a : ℤ) : (starRingEnd ℂ) (polyPt n a) = polyPt n (-a) := by
  rw [polyPt, polyPt, ← Complex.exp_conj]
  congr 1
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

lemma polyPt_mul_conj (n a b : ℤ) :
    polyPt n a * (starRingEnd ℂ) (polyPt n b) = polyPt n (a - b) := by
  rw [polyPt_conj, ← polyPt_add, sub_eq_add_neg]

/-- The map `a ↦ polyPt n a` has period `n`. -/
lemma polyPt_eq_of_modEq {n : ℤ} (hn : 0 < n) {a b : ℤ} (h : a ≡ b [ZMOD n]) :
    polyPt n a = polyPt n b := by
  rw [Int.modEq_iff_dvd] at h
  obtain ⟨k, hk⟩ := h
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have h1 : (2 : ℝ) * Real.pi * a / n = 2 * Real.pi * b / n + (-k : ℝ) * (2 * Real.pi) := by
    have hk2 : (b : ℝ) - a = n * k := by exact_mod_cast hk
    have h3 : (a : ℝ) = b - n * k := by linarith
    rw [h3]
    field_simp [hn']
    ring
  rw [polyPt, polyPt, Complex.exp_eq_exp_iff_exists_int]
  refine ⟨-k, ?_⟩
  rw [h1]
  push_cast
  ring

/-- The map `a ↦ polyPt n a` is injective modulo `n`. -/
lemma modEq_of_polyPt_eq {n : ℤ} (hn : 0 < n) {a b : ℤ} (h : polyPt n a = polyPt n b) :
    a ≡ b [ZMOD n] := by
  rw [polyPt, polyPt, Complex.exp_eq_exp_iff_exists_int] at h
  obtain ⟨k, hk⟩ := h
  -- Move everything into a single `ofReal` multiplied by `I`.
  have h2 : (↑(2 * Real.pi * a / n) : ℂ) * Complex.I - (↑(2 * Real.pi * b / n) : ℂ) * Complex.I
      = ↑k * (2 * ↑Real.pi * Complex.I) := by
    linear_combination hk
  have hconv : (↑(2 * Real.pi * a / n - 2 * Real.pi * b / n - (k : ℝ) * (2 * Real.pi)) : ℂ)
        * Complex.I
      = (↑(2 * Real.pi * a / n) : ℂ) * Complex.I - (↑(2 * Real.pi * b / n)) * Complex.I -
        ↑k * (2 * ↑Real.pi * Complex.I) := by
    push_cast
    ring
  have h3 : (↑(2 * Real.pi * a / n - 2 * Real.pi * b / n - (k : ℝ) * (2 * Real.pi)) : ℂ)
      * Complex.I = 0 := by
    rw [hconv]
    linear_combination h2
  have h4 : 2 * Real.pi * a / n - 2 * Real.pi * b / n - (k : ℝ) * (2 * Real.pi) = 0 := by
    rcases mul_eq_zero.mp h3 with h | h
    · exact Complex.ofReal_eq_zero.mp h
    · exact absurd h Complex.I_ne_zero
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hπ : (2 : ℝ) * Real.pi ≠ 0 := by positivity
  have h5 : 2 * Real.pi * ((a : ℝ) - b - n * k) = 0 := by
    field_simp [hn'] at h4
    linear_combination h4
  have h6 : (a : ℝ) - b - n * k = 0 := by
    rcases mul_eq_zero.mp h5 with h | h
    · exact absurd h hπ
    · exact h
  have h7 : (a : ℝ) - b = n * k := by linarith
  have h8 : a - b = n * k := by exact_mod_cast h7
  rw [Int.modEq_iff_dvd]
  exact ⟨-k, by rw [mul_neg]; linarith [h8]⟩

/-- The real part of `polyPt n a` only depends on `a` modulo `n`. -/
lemma polyPt_re_of_modEq {n : ℤ} (hn : 0 < n) {a b : ℤ} (h : a ≡ b [ZMOD n]) :
    (polyPt n a).re = (polyPt n b).re := by
  rw [Int.modEq_iff_dvd] at h
  obtain ⟨k, hk⟩ := h
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [polyPt_re, polyPt_re]
  have h1 : 2 * Real.pi * a / n = 2 * Real.pi * b / n + (-k : ℤ) * (2 * Real.pi) := by
    have hk2 : (b : ℝ) - a = n * k := by exact_mod_cast hk
    have h3 : (a : ℝ) = b - n * k := by linarith
    rw [h3]
    field_simp [hn']
    push_cast
    ring
  rw [h1]
  exact (Real.cos_periodic.int_mul (-k)) (2 * Real.pi * b / n)

lemma polyPt_re_neg (n a : ℤ) : (polyPt n (-a)).re = (polyPt n a).re := by
  have h : (2 : ℝ) * Real.pi * ((-a : ℤ) : ℝ) / n = -(2 * Real.pi * a / n) := by
    push_cast
    ring
  rw [polyPt_re, polyPt_re, h, Real.cos_neg]

/-- The squared-distance formula for two of our points. -/
lemma dist_polyPt_sq {n : ℤ} (_hn : 0 < n) (a b : ℤ) :
    dist (polyPt n a) (polyPt n b) ^ 2 = 2 - 2 * (polyPt n (a - b)).re := by
  rw [dist_eq_norm, Complex.sq_norm, Complex.normSq_sub, polyPt_mul_conj,
    Complex.normSq_eq_norm_sq, polyPt_norm, Complex.normSq_eq_norm_sq, polyPt_norm]
  ring

lemma dist_zero_polyPt (n a : ℤ) : dist 0 (polyPt n a) = 1 := by
  rw [dist_eq_norm, zero_sub, norm_neg, polyPt_norm]

/-- Two distances between our points are equal as soon as the corresponding
real parts agree. -/
lemma dist_eq_of_re_eq {n : ℤ} (hn : 0 < n) {a b c d : ℤ}
    (h : (polyPt n (a - b)).re = (polyPt n (c - d)).re) :
    dist (polyPt n a) (polyPt n b) = dist (polyPt n c) (polyPt n d) := by
  apply (sq_eq_sq₀ dist_nonneg dist_nonneg).mp
  rw [dist_polyPt_sq hn, dist_polyPt_sq hn, h]

lemma dist_polyPt_eq_one {n : ℤ} (hn : 0 < n) {a b : ℤ}
    (h : (polyPt n (a - b)).re = 1 / 2) :
    dist (polyPt n a) (polyPt n b) = 1 := by
  apply (sq_eq_sq₀ dist_nonneg zero_le_one).mp
  rw [dist_polyPt_sq hn, h]
  norm_num

/-- `a ↦ polyPt n a` is injective on any finset of exponents below `n`. -/
lemma polyPt_injOn_of_lt {n : ℤ} (hn : 0 < n) {E : Finset ℕ}
    (hE : ∀ k ∈ E, (k : ℤ) < n) :
    Set.InjOn (fun k : ℕ => polyPt n k) ↑E := by
  intro a ha b hb hab
  have h1 := modEq_of_polyPt_eq hn hab
  have h2 : (a : ℤ) % n = (b : ℤ) % n := h1
  rw [Int.emod_eq_of_lt (by positivity) (hE a ha),
      Int.emod_eq_of_lt (by positivity) (hE b hb)] at h2
  exact_mod_cast h2

/-- The regular `n`-gon, as the set of `n`-th roots of unity. -/
noncomputable def regularGon (n : ℕ) : Finset ℂ :=
  (Finset.range n).image fun k : ℕ => polyPt n k

lemma regularGon_card {n : ℕ} (hn : 3 ≤ n) : (regularGon n).card = n := by
  have hn0 : (0 : ℤ) < (n : ℤ) := by exact_mod_cast (by omega)
  have hinj : Set.InjOn (fun k : ℕ => polyPt (n : ℤ) k) ↑(Finset.range n) :=
    polyPt_injOn_of_lt hn0 (fun k hk => by exact_mod_cast Finset.mem_range.mp hk)
  rw [regularGon, Finset.card_image_of_injOn hinj, Finset.card_range]

/-- The regular `n`-gon with `n` odd is balanced: for two vertices `A, B`, the
perpendicular bisector of `AB` passes through a third vertex, since `2` is
invertible modulo `n`. -/
lemma regularGon_balanced {n : ℕ} (hn : 3 ≤ n) (hodd : Odd n) : Balanced (regularGon n) := by
  obtain ⟨t, ht⟩ := hodd
  have hn0 : (0 : ℤ) < (n : ℤ) := by exact_mod_cast (by omega)
  intro A hA B hB hAB
  rw [regularGon, Finset.mem_image] at hA hB
  obtain ⟨a, ha, rfl⟩ := hA
  obtain ⟨b, hb, rfl⟩ := hB
  set M := (a + b) * ((n + 1) / 2) with hM
  have h2 : 2 * ((n + 1) / 2) = n + 1 := by omega
  have h2M : 2 * M = (a + b) * (n + 1) := by
    rw [hM]
    conv_rhs => rw [← h2]
    ring
  refine ⟨polyPt n ((M % n : ℕ) : ℤ),
    Finset.mem_image.mpr ⟨M % n, Finset.mem_range.mpr (Nat.mod_lt _ (by omega)), rfl⟩, ?_⟩
  apply dist_eq_of_re_eq hn0
  have key : (2 : ℤ) * ((M % n : ℕ) : ℤ) ≡ (a : ℤ) + b [ZMOD (n : ℤ)] := by
    rw [Int.modEq_iff_dvd]
    have hdiv : (M : ℤ) = n * ((M / n : ℕ) : ℤ) + ((M % n : ℕ) : ℤ) := by
      exact_mod_cast (Nat.div_add_mod M n).symm
    have h2M' : 2 * (M : ℤ) = ((a : ℤ) + b) * (n + 1) := by exact_mod_cast h2M
    exact ⟨2 * ((M / n : ℕ) : ℤ) - ((a : ℤ) + b), by linarith [hdiv, h2M']⟩
  have hac : (a : ℤ) - ((M % n : ℕ) : ℤ) ≡ -((b : ℤ) - ((M % n : ℕ) : ℤ)) [ZMOD (n : ℤ)] := by
    rw [Int.modEq_iff_dvd] at key ⊢
    obtain ⟨k, hk⟩ := key
    exact ⟨-k, by rw [mul_neg]; linarith [hk]⟩
  rw [polyPt_re_of_modEq hn0 hac, polyPt_re_neg]

/-- The regular `n`-gon is centre-free: a point `P` equidistant from three
vertices `A, B, C` would have to be the centre, which is not a vertex. -/
lemma regularGon_centerFree {n : ℕ} (hn : 3 ≤ n) : CenterFree (regularGon n) := by
  have hn0 : (0 : ℤ) < (n : ℤ) := by exact_mod_cast (by omega)
  intro A hA B hB C hC hAB hBC hAC
  rw [regularGon, Finset.mem_image] at hA hB hC
  obtain ⟨a, ha, rfl⟩ := hA
  obtain ⟨b, hb, rfl⟩ := hB
  obtain ⟨c, hc, rfl⟩ := hC
  rintro ⟨P, hP, hPAB, hPBC⟩
  rw [regularGon, Finset.mem_image] at hP
  obtain ⟨p, hp, rfl⟩ := hP
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn0.ne'
  have hπ : (2 : ℝ) * Real.pi ≠ 0 := by positivity
  -- From `dist P A = dist P B` we get `a ≡ b` or `2p ≡ a + b` (mod `n`).
  have step : ∀ a b : ℤ, dist (polyPt (n : ℤ) p) (polyPt (n : ℤ) a) =
      dist (polyPt (n : ℤ) p) (polyPt (n : ℤ) b) →
      a ≡ b [ZMOD (n : ℤ)] ∨ (2 : ℤ) * p ≡ a + b [ZMOD (n : ℤ)] := by
    intro a b hd
    have h1 : (polyPt (n : ℤ) (p - a)).re = (polyPt (n : ℤ) (p - b)).re := by
      have h2 : dist (polyPt (n : ℤ) p) (polyPt (n : ℤ) a) ^ 2 =
          dist (polyPt (n : ℤ) p) (polyPt (n : ℤ) b) ^ 2 := by rw [hd]
      rw [dist_polyPt_sq hn0, dist_polyPt_sq hn0] at h2
      linarith [h2]
    rw [polyPt_re, polyPt_re, Real.cos_eq_cos_iff] at h1
    obtain ⟨k, hk | hk⟩ := h1
    · left
      rw [Int.modEq_iff_dvd]
      have e1 : 2 * Real.pi * ↑(p - b) / ↑n - 2 * Real.pi * ↑(p - a) / ↑n =
          2 * (k : ℝ) * Real.pi := by
        linear_combination hk
      have e2 : 2 * Real.pi * ↑(p - b) / ↑n - 2 * Real.pi * ↑(p - a) / ↑n =
          2 * Real.pi * ((a : ℝ) - b) / n := by
        rw [div_sub_div_same]
        congr 1
        push_cast
        ring
      have e3 : 2 * Real.pi * ((a : ℝ) - b) / n = 2 * (k : ℝ) * Real.pi := by
        linarith [e1, e2]
      have e4 : 2 * Real.pi * ((a : ℝ) - b) = (2 * (k : ℝ) * Real.pi) * n := by
        have h6 := congrArg (· * (n : ℝ)) e3
        rw [mul_assoc, div_mul_cancel₀ _ hn'] at h6
        linear_combination h6
      have h4 : (a : ℝ) - b = (n : ℝ) * k :=
        mul_left_cancel₀ hπ (by linear_combination e4)
      have h5 : a - b = n * k := by exact_mod_cast h4
      exact ⟨-k, by rw [mul_neg]; linarith [h5]⟩
    · right
      rw [Int.modEq_iff_dvd]
      have e1 : 2 * Real.pi * ↑(p - b) / ↑n + 2 * Real.pi * ↑(p - a) / ↑n =
          2 * (k : ℝ) * Real.pi := by
        linear_combination hk
      have e2 : 2 * Real.pi * ↑(p - b) / ↑n + 2 * Real.pi * ↑(p - a) / ↑n =
          2 * Real.pi * (((p : ℝ) - b) + (p - a)) / n := by
        rw [← add_div]
        congr 1
        push_cast
        ring
      have e3 : 2 * Real.pi * (((p : ℝ) - b) + (p - a)) / n = 2 * (k : ℝ) * Real.pi := by
        linarith [e1, e2]
      have e4 : 2 * Real.pi * (((p : ℝ) - b) + (p - a)) = (2 * (k : ℝ) * Real.pi) * n := by
        have h6 := congrArg (· * (n : ℝ)) e3
        rw [mul_assoc, div_mul_cancel₀ _ hn'] at h6
        linear_combination h6
      have h4 : ((p : ℝ) - b) + (p - a) = (n : ℝ) * k :=
        mul_left_cancel₀ hπ (by linear_combination e4)
      have h5 : (p - b) + (p - a) = n * k := by exact_mod_cast h4
      exact ⟨-k, by rw [mul_neg]; linarith [h5]⟩
  have hAB' := step a b hPAB
  have hBC' := step b c hPBC
  have hab_ne : ¬((a : ℤ) ≡ b [ZMOD (n : ℤ)]) := fun h => hAB (polyPt_eq_of_modEq hn0 h)
  have hbc_ne : ¬((b : ℤ) ≡ c [ZMOD (n : ℤ)]) := fun h => hBC (polyPt_eq_of_modEq hn0 h)
  have h1 : (2 : ℤ) * p ≡ (a : ℤ) + b [ZMOD (n : ℤ)] := hAB'.resolve_left hab_ne
  have h2 : (2 : ℤ) * p ≡ (b : ℤ) + c [ZMOD (n : ℤ)] := hBC'.resolve_left hbc_ne
  rw [Int.modEq_iff_dvd] at h1 h2
  obtain ⟨k1, hk1⟩ := h1
  obtain ⟨k2, hk2⟩ := h2
  have hac : (a : ℤ) ≡ c [ZMOD (n : ℤ)] := by
    rw [Int.modEq_iff_dvd]
    exact ⟨k2 - k1, by rw [mul_sub]; linarith [hk1, hk2]⟩
  exact hAC (polyPt_eq_of_modEq hn0 hac)

/-- The point `polyPt (6s) s` is at angle `π/3` on the unit circle, so its
real part is `1/2`. This is what makes the `60°`-pair construction work. -/
lemma polyPt_re_sixth {N s : ℤ} (hs : 0 < s) (hN : N = 6 * s) :
    (polyPt N s).re = 1 / 2 := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  rw [polyPt_re, show 2 * Real.pi * (s : ℝ) / N = Real.pi / 3 by
    rw [hN]; push_cast; field_simp [hsR.ne']; ring, Real.cos_pi_div_three]

lemma polyPt_re_evenS (m : ℕ) :
    (polyPt (6 * (2 * m + 3) : ℕ) (2 * m + 3 : ℕ)).re = 1 / 2 := by
  apply polyPt_re_sixth
  · exact_mod_cast (by omega : 0 < 2 * m + 3)
  · push_cast
    ring

lemma polyPt_re_evenS_neg (m : ℕ) :
    (polyPt (6 * (2 * m + 3) : ℕ) (-((2 * m + 3 : ℕ) : ℤ))).re = 1 / 2 := by
  rw [polyPt_re_neg]
  exact polyPt_re_evenS m

/-- The exponents used in the even case: pairs `{j, j + s}` for `j < m` and one
triple `{m, m + s, m + 2s}`, where `s = 2m + 3` is a sixth of the circle. -/
def evenExp (m : ℕ) : Finset ℕ :=
  Finset.range m ∪ (Finset.range m).image (· + (2 * m + 3)) ∪
    {m, m + (2 * m + 3), m + 2 * (2 * m + 3)}

lemma evenExp_lt (m : ℕ) {k : ℕ} (hk : k ∈ evenExp m) : k < 6 * (2 * m + 3) := by
  simp only [evenExp, Finset.mem_union, Finset.mem_range, Finset.mem_image,
    Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with h | ⟨j, hj, rfl⟩ | rfl | rfl | rfl <;> omega

lemma evenExp_card (m : ℕ) : (evenExp m).card = 2 * m + 3 := by
  have hdisj1 : Disjoint (Finset.range m) ((Finset.range m).image (· + (2 * m + 3))) := by
    rw [Finset.disjoint_left]
    intro x hx hx2
    rw [Finset.mem_range] at hx
    rw [Finset.mem_image] at hx2
    obtain ⟨j, hj, rfl⟩ := hx2
    rw [Finset.mem_range] at hj
    omega
  have hdisj2 : Disjoint (Finset.range m ∪ (Finset.range m).image (· + (2 * m + 3)))
      {m, m + (2 * m + 3), m + 2 * (2 * m + 3)} := by
    rw [Finset.disjoint_left]
    intro x hx hx2
    simp only [Finset.mem_union, Finset.mem_range, Finset.mem_image] at hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx2
    rcases hx2 with rfl | rfl | rfl <;> rcases hx with h | ⟨j, hj, h⟩ <;> omega
  have h3 : ({m, m + (2 * m + 3), m + 2 * (2 * m + 3)} : Finset ℕ).card = 3 := by
    have h1 : m ∉ ({m + (2 * m + 3), m + 2 * (2 * m + 3)} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    have h2 : m + (2 * m + 3) ∉ ({m + 2 * (2 * m + 3)} : Finset ℕ) := by
      simp only [Finset.mem_singleton]
      omega
    rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2,
      Finset.card_singleton]
  rw [evenExp, Finset.card_union_of_disjoint hdisj2, Finset.card_union_of_disjoint hdisj1,
    Finset.card_image_of_injective _ (add_left_injective _), Finset.card_range, h3]
  omega

/-- Every exponent in `evenExp m` has a partner at `±s`, i.e. at chord distance
equal to the radius. -/
lemma evenExp_partner (m : ℕ) {k : ℕ} (hk : k ∈ evenExp m) :
    ∃ l ∈ evenExp m, (polyPt (6 * (2 * m + 3) : ℕ) ((k : ℤ) - l)).re = 1 / 2 := by
  simp only [evenExp, Finset.mem_union, Finset.mem_range, Finset.mem_image,
    Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with (h | ⟨j, hj, rfl⟩) | hkm | hks | hkt
  · refine ⟨k + (2 * m + 3), ?_, ?_⟩
    · rw [evenExp, Finset.mem_union, Finset.mem_union]
      exact Or.inl (Or.inr (Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr h, rfl⟩))
    · have h1 : ((k : ℤ) - ((k + (2 * m + 3) : ℕ) : ℤ)) = -((2 * m + 3 : ℕ) : ℤ) := by
        push_cast
        ring
      rw [h1]
      exact polyPt_re_evenS_neg m
  · refine ⟨j, ?_, ?_⟩
    · rw [evenExp, Finset.mem_union, Finset.mem_union]
      exact Or.inl (Or.inl (Finset.mem_range.mpr hj))
    · have h1 : (((j + (2 * m + 3) : ℕ) : ℤ) - (j : ℤ)) = ((2 * m + 3 : ℕ) : ℤ) := by
        push_cast
        ring
      rw [h1]
      exact polyPt_re_evenS m
  · rw [hkm]
    refine ⟨m + (2 * m + 3), ?_, ?_⟩
    · rw [evenExp, Finset.mem_union]
      exact Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl rfl))))
    · have h1 : ((m : ℤ) - ((m + (2 * m + 3) : ℕ) : ℤ)) = -((2 * m + 3 : ℕ) : ℤ) := by
        push_cast
        ring
      rw [h1]
      exact polyPt_re_evenS_neg m
  · rw [hks]
    refine ⟨m, ?_, ?_⟩
    · rw [evenExp, Finset.mem_union]
      exact Or.inr (Finset.mem_insert.mpr (Or.inl rfl))
    · have h1 : (((m + (2 * m + 3) : ℕ) : ℤ) - (m : ℤ)) = ((2 * m + 3 : ℕ) : ℤ) := by
        push_cast
        ring
      rw [h1]
      exact polyPt_re_evenS m
  · rw [hkt]
    refine ⟨m + (2 * m + 3), ?_, ?_⟩
    · rw [evenExp, Finset.mem_union]
      exact Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl rfl))))
    · have h1 : (((m + 2 * (2 * m + 3) : ℕ) : ℤ) - ((m + (2 * m + 3) : ℕ) : ℤ)) =
        ((2 * m + 3 : ℕ) : ℤ) := by
        push_cast
        ring
      rw [h1]
      exact polyPt_re_evenS m

/-- The construction for even `n`: the centre of a circle together with `n - 1`
points on the circle, consisting of pairs separated by `60°` arcs and one
triple of consecutive `60°` arcs. -/
noncomputable def evenSet (m : ℕ) : Finset ℂ :=
  insert 0 ((evenExp m).image fun k : ℕ => polyPt (6 * (2 * m + 3) : ℕ) k)

lemma evenSet_card (m : ℕ) : (evenSet m).card = 2 * m + 4 := by
  have hN : (0 : ℤ) < (6 * (2 * m + 3) : ℕ) := by exact_mod_cast (by omega)
  have h0 : (0 : ℂ) ∉ (evenExp m).image (fun k : ℕ => polyPt (6 * (2 * m + 3) : ℕ) k) := by
    intro h
    obtain ⟨k, -, hk⟩ := Finset.mem_image.mp h
    exact polyPt_ne_zero _ _ hk
  have hinj : Set.InjOn (fun k : ℕ => polyPt (6 * (2 * m + 3) : ℕ) k) ↑(evenExp m) :=
    polyPt_injOn_of_lt hN (fun k hk => by exact_mod_cast evenExp_lt m hk)
  rw [evenSet, Finset.card_insert_of_notMem h0, Finset.card_image_of_injOn hinj,
    evenExp_card]

lemma evenSet_balanced (m : ℕ) : Balanced (evenSet m) := by
  have hN : (0 : ℤ) < (6 * (2 * m + 3) : ℕ) := by exact_mod_cast (by omega)
  intro A hA B hB hAB
  rw [evenSet, Finset.mem_insert, Finset.mem_image] at hA hB
  rcases hA with rfl | ⟨a, ha, rfl⟩ <;> rcases hB with rfl | ⟨b, hb, rfl⟩
  · exact absurd rfl hAB
  · obtain ⟨l, hl, hlre⟩ := evenExp_partner m hb
    refine ⟨polyPt (6 * (2 * m + 3) : ℕ) l,
      Finset.mem_insert.mpr (Or.inr (Finset.mem_image.mpr ⟨l, hl, rfl⟩)), ?_⟩
    rw [dist_zero_polyPt]
    exact (dist_polyPt_eq_one hN hlre).symm
  · obtain ⟨l, hl, hlre⟩ := evenExp_partner m ha
    refine ⟨polyPt (6 * (2 * m + 3) : ℕ) l,
      Finset.mem_insert.mpr (Or.inr (Finset.mem_image.mpr ⟨l, hl, rfl⟩)), ?_⟩
    rw [dist_zero_polyPt]
    exact dist_polyPt_eq_one hN hlre
  · refine ⟨0, Finset.mem_insert.mpr (Or.inl rfl), ?_⟩
    rw [dist_eq_norm, sub_zero, polyPt_norm, dist_eq_norm, sub_zero, polyPt_norm]

/-- The ordered pairs of distinct points of `S`, both different from `C`,
that are equidistant from `C`. -/
noncomputable def covered (S : Finset ℂ) (C : ℂ) : Finset (ℂ × ℂ) :=
  (S.erase C).offDiag.filter (fun p => dist p.1 C = dist p.2 C)

/-- A balanced centre-free set with at least three points must have odd
cardinality. This is the double-counting argument: every pair of points must
have a point of `S` on its perpendicular bisector, but centre-freeness implies
each point of `S` lies on few such bisectors. -/
theorem even_card_impossible {S : Finset ℂ} (hS : Balanced S) (hC : CenterFree S)
    (hcard : 3 ≤ S.card) : Odd S.card := by
  by_contra hOdd
  have hEven : Even S.card := Nat.not_odd_iff_even.mp hOdd
  obtain ⟨k, hk⟩ := hEven
  -- Step 1: every ordered pair of distinct points is covered by some center.
  have hcov : S.offDiag ⊆ S.biUnion (covered S) := by
    rintro ⟨A, B⟩ hp
    rw [Finset.mem_offDiag] at hp
    obtain ⟨hA, hB, hAB⟩ := hp
    obtain ⟨C, hCS, hCdist⟩ := hS A hA B hB hAB
    have hAC : A ≠ C := by
      intro h
      have h0 : dist A C = 0 := by rw [h, dist_self]
      have h1 : dist B C = 0 := hCdist ▸ h0
      exact hAB (h.trans (dist_eq_zero.mp h1).symm)
    have hBC : B ≠ C := by
      intro h
      have h0 : dist B C = 0 := by rw [h, dist_self]
      have h1 : dist A C = 0 := hCdist.symm ▸ h0
      exact hAB ((dist_eq_zero.mp h1).trans h.symm)
    refine Finset.mem_biUnion.mpr ⟨C, hCS, ?_⟩
    unfold covered
    rw [Finset.mem_filter, Finset.mem_offDiag]
    exact ⟨⟨Finset.mem_erase.mpr ⟨hAC, hA⟩, Finset.mem_erase.mpr ⟨hBC, hB⟩, hAB⟩, hCdist⟩
  -- Step 2: each center covers at most `S.card - 2` pairs.
  have hbound : ∀ C ∈ S, (covered S C).card ≤ S.card - 2 := by
    intro C hCS
    -- rewrite `covered S C` as a biUnion over the possible distance values
    have heq : covered S C = ((S.erase C).image (fun A => dist A C)).biUnion
        (fun v => ((S.erase C).filter (fun A => dist A C = v)).offDiag) := by
      ext ⟨a, b⟩
      constructor
      · intro h
        have h' : (a, b) ∈ (S.erase C).offDiag.filter (fun p => dist p.1 C = dist p.2 C) := h
        rw [Finset.mem_filter, Finset.mem_offDiag] at h'
        obtain ⟨⟨haE, hbE, hab⟩, hd⟩ := h'
        refine Finset.mem_biUnion.mpr ⟨dist a C, Finset.mem_image_of_mem _ haE, ?_⟩
        refine Finset.mem_offDiag.mpr ⟨Finset.mem_filter.mpr ⟨haE, rfl⟩,
          Finset.mem_filter.mpr ⟨hbE, hd.symm⟩, hab⟩
      · intro h
        obtain ⟨v, _hv, hvoff⟩ := Finset.mem_biUnion.mp h
        have hvoff' : (a, b) ∈ ((S.erase C).filter (fun A => dist A C = v)).offDiag := hvoff
        rw [Finset.mem_offDiag] at hvoff'
        obtain ⟨haF, hbF, hab⟩ := hvoff'
        rw [Finset.mem_filter] at haF hbF
        unfold covered
        rw [Finset.mem_filter, Finset.mem_offDiag]
        exact ⟨⟨haF.1, hbF.1, hab⟩, haF.2.trans hbF.2.symm⟩
    -- center-freeness: each distance fiber has at most 2 points
    have hsv : ∀ v ∈ (S.erase C).image (fun A => dist A C),
        ((S.erase C).filter (fun A => dist A C = v)).card ≤ 2 := by
      intro v _hv
      by_contra hlt
      push Not at hlt
      have hpos : 0 < ((S.erase C).filter (fun A => dist A C = v)).card := by omega
      obtain ⟨A, hAF⟩ := Finset.card_pos.mp hpos
      have h2 : 1 < (((S.erase C).filter (fun A => dist A C = v)).erase A).card := by
        rw [Finset.card_erase_of_mem hAF]; omega
      rw [Finset.one_lt_card_iff] at h2
      obtain ⟨D, E, hDF, hEF, hDE⟩ := h2
      have hdA : dist A C = v := (Finset.mem_filter.mp hAF).2
      have hdD : dist D C = v := (Finset.mem_filter.mp (Finset.mem_erase.mp hDF).2).2
      have hdE : dist E C = v := (Finset.mem_filter.mp (Finset.mem_erase.mp hEF).2).2
      have hAS : A ∈ S := (Finset.mem_erase.mp (Finset.mem_filter.mp hAF).1).2
      have hDS : D ∈ S := (Finset.mem_erase.mp (Finset.mem_filter.mp (Finset.mem_erase.mp hDF).2).1).2
      have hES : E ∈ S := (Finset.mem_erase.mp (Finset.mem_filter.mp (Finset.mem_erase.mp hEF).2).1).2
      have hDA : D ≠ A := (Finset.mem_erase.mp hDF).1
      have hEA : E ≠ A := (Finset.mem_erase.mp hEF).1
      exact hC A hAS D hDS E hES hDA.symm hDE hEA.symm
        ⟨C, hCS, by rw [dist_comm C A, dist_comm C D, hdA, hdD],
          by rw [dist_comm C D, dist_comm C E, hdD, hdE]⟩
    -- every fiber over the image is nonempty
    have hone : ∀ v ∈ (S.erase C).image (fun A => dist A C),
        1 ≤ ((S.erase C).filter (fun A => dist A C = v)).card := by
      intro v hv
      rw [Finset.mem_image] at hv
      obtain ⟨A, hAE, hAv⟩ := hv
      exact Finset.card_pos.mpr ⟨A, Finset.mem_filter.mpr ⟨hAE, hAv⟩⟩
    -- the fiber sizes sum to the size of `S.erase C`
    have hsum_card : ∑ v ∈ (S.erase C).image (fun A => dist A C),
        ((S.erase C).filter (fun A => dist A C = v)).card = (S.erase C).card :=
      (Finset.card_eq_sum_card_fiberwise (s := S.erase C)
        (t := (S.erase C).image (fun A => dist A C)) (f := fun A => dist A C)
        (fun x hx => Finset.mem_image_of_mem _ hx)).symm
    -- split each fiber size as `(s_v - 1) + 1`
    have hkey : ∑ v ∈ (S.erase C).image (fun A => dist A C),
          ((S.erase C).filter (fun A => dist A C = v)).card
        = ∑ v ∈ (S.erase C).image (fun A => dist A C),
            (((S.erase C).filter (fun A => dist A C = v)).card - 1)
          + ((S.erase C).image (fun A => dist A C)).card := by
      calc ∑ v ∈ (S.erase C).image (fun A => dist A C),
              ((S.erase C).filter (fun A => dist A C = v)).card
          = ∑ v ∈ (S.erase C).image (fun A => dist A C),
              (((S.erase C).filter (fun A => dist A C = v)).card - 1 + 1) :=
            Finset.sum_congr rfl (fun v hv => (Nat.sub_add_cancel (hone v hv)).symm)
        _ = ∑ v ∈ (S.erase C).image (fun A => dist A C),
              (((S.erase C).filter (fun A => dist A C = v)).card - 1)
            + ∑ v ∈ (S.erase C).image (fun A => dist A C), 1 := Finset.sum_add_distrib
        _ = ∑ v ∈ (S.erase C).image (fun A => dist A C),
              (((S.erase C).filter (fun A => dist A C = v)).card - 1)
            + ((S.erase C).image (fun A => dist A C)).card := by
            rw [Finset.sum_const, Nat.nsmul_eq_mul, mul_one]
    have hsum : ∑ v ∈ (S.erase C).image (fun A => dist A C),
          (((S.erase C).filter (fun A => dist A C = v)).card - 1)
        = (S.erase C).card - ((S.erase C).image (fun A => dist A C)).card := by
      omega
    -- card of offDiag of a fiber, in factored form
    have hoff : ∀ v, (((S.erase C).filter (fun A => dist A C = v)).offDiag).card
        = ((S.erase C).filter (fun A => dist A C = v)).card
          * (((S.erase C).filter (fun A => dist A C = v)).card - 1) := by
      intro v
      rw [Finset.offDiag_card, mul_tsub, mul_one]
    -- assemble the per-center bound
    have hfin : (covered S C).card
        ≤ 2 * ((S.erase C).card - ((S.erase C).image (fun A => dist A C)).card) := by
      calc (covered S C).card
          ≤ ∑ v ∈ (S.erase C).image (fun A => dist A C),
              (((S.erase C).filter (fun A => dist A C = v)).offDiag).card := by
            rw [heq]; exact Finset.card_biUnion_le
        _ = ∑ v ∈ (S.erase C).image (fun A => dist A C),
              ((S.erase C).filter (fun A => dist A C = v)).card
              * (((S.erase C).filter (fun A => dist A C = v)).card - 1) :=
            Finset.sum_congr rfl (fun v _ => hoff v)
        _ ≤ ∑ v ∈ (S.erase C).image (fun A => dist A C),
              2 * (((S.erase C).filter (fun A => dist A C = v)).card - 1) :=
            Finset.sum_le_sum (fun v hv => Nat.mul_le_mul (hsv v hv) (Nat.le_refl _))
        _ = 2 * ∑ v ∈ (S.erase C).image (fun A => dist A C),
              (((S.erase C).filter (fun A => dist A C = v)).card - 1) := by
            rw [Finset.mul_sum]
        _ = 2 * ((S.erase C).card - ((S.erase C).image (fun A => dist A C)).card) := by
            rw [hsum]
    -- the image of distances is large
    have hVge : (S.erase C).card
        ≤ 2 * ((S.erase C).image (fun A => dist A C)).card := by
      have hle : ∑ v ∈ (S.erase C).image (fun A => dist A C),
            ((S.erase C).filter (fun A => dist A C = v)).card
          ≤ ∑ v ∈ (S.erase C).image (fun A => dist A C), 2 :=
        Finset.sum_le_sum (fun v hv => hsv v hv)
      rw [hsum_card, Finset.sum_const, Nat.nsmul_eq_mul] at hle
      omega
    have herase : (S.erase C).card = S.card - 1 := Finset.card_erase_of_mem hCS
    omega
  -- Step 3: double counting gives `n * (n - 1) ≤ n * (n - 2)`, a contradiction.
  have htotal : S.offDiag.card ≤ ∑ C ∈ S, (covered S C).card :=
    le_trans (Finset.card_le_card hcov) Finset.card_biUnion_le
  have hle2 : ∑ C ∈ S, (covered S C).card ≤ S.card * (S.card - 2) := by
    calc ∑ C ∈ S, (covered S C).card ≤ ∑ C ∈ S, (S.card - 2) :=
          Finset.sum_le_sum (fun C hCS => hbound C hCS)
      _ = S.card * (S.card - 2) := by rw [Finset.sum_const, Nat.nsmul_eq_mul]
  rw [Finset.offDiag_card] at htotal
  have hfac : S.card * S.card - S.card = S.card * (S.card - 1) := by
    rw [mul_tsub, mul_one]
  have hmul : S.card * (S.card - 1) ≤ S.card * (S.card - 2) :=
    hfac ▸ le_trans htotal hle2
  have hcancel : S.card - 1 ≤ S.card - 2 := Nat.le_of_mul_le_mul_left hmul (by omega)
  omega

snip end

/-- **IMO 2015 Problem 1 (a).** -/
problem imo2015_p1_a (n : ℕ) (hn : 3 ≤ n) : ∃ S : Finset ℂ, S.card = n ∧ Balanced S := by
  rcases Nat.even_or_odd n with hev | hod
  · obtain ⟨k, hk⟩ := hev
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
    exact ⟨evenSet m, by rw [evenSet_card]; omega, evenSet_balanced m⟩
  · exact ⟨regularGon n, regularGon_card hn, regularGon_balanced hn hod⟩

/-- **IMO 2015 Problem 1 (b).** -/
problem imo2015_p1_b (n : ℕ) (hn : 3 ≤ n) :
    n ∈ SolutionSet ↔ ∃ S : Finset ℂ, S.card = n ∧ Balanced S ∧ CenterFree S := by
  constructor
  · intro hod
    rw [SolutionSet, Set.mem_setOf_eq] at hod
    exact ⟨regularGon n, regularGon_card hn, regularGon_balanced hn hod,
      regularGon_centerFree hn⟩
  · rintro ⟨S, hcard, hbal, hcf⟩
    rw [SolutionSet, Set.mem_setOf_eq, ← hcard]
    exact even_card_impossible hbal hcf (by omega)

end Imo2015P1
