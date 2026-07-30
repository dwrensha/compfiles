/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Euclidean.Sphere.Basic
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# USA Mathematical Olympiad 2005, Problem 3

Let ABC be an acute-angled triangle, and let P and Q be two points on side BC.
Construct a point C₁ in such a way that the convex quadrilateral APBC₁ is cyclic,
QC₁ ∥ CA, and C₁ and Q lie on opposite sides of line AB. Construct a point B₁ in
such a way that the convex quadrilateral APCB₁ is cyclic, QB₁ ∥ BA, and B₁ and Q
lie on opposite sides of line AC. Prove that the points B₁, C₁, P, and Q lie on a
circle.
-/

namespace Usa2005P3

open scoped InnerProductSpace

open EuclideanGeometry

/-- The Euclidean plane. -/
abbrev Pt := EuclideanSpace ℝ (Fin 2)

snip begin

/-- Squared distance, in coordinates. -/
def d2 (x y : Pt) : ℝ := (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2

/-- Inner product, in coordinates. -/
def ip (u v : Pt) : ℝ := u 0 * v 0 + u 1 * v 1

/-- Cross product (signed area), in coordinates. -/
def cr (u v : Pt) : ℝ := u 0 * v 1 - u 1 * v 0

lemma pt_ext {x y : Pt} (h0 : x 0 = y 0) (h1 : x 1 = y 1) : x = y :=
  PiLp.ext (Fin.forall_fin_two.mpr ⟨h0, h1⟩)

lemma dist_sq_eq (x y : Pt) : dist x y ^ 2 = d2 x y := by
  rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq, Real.dist_eq, sq_abs, sq_abs]
  rfl

lemma dist_eq_of_d2_eq {x y z : Pt} (h : d2 x z = d2 y z) : dist x z = dist y z := by
  have h1 : dist x z ^ 2 = dist y z ^ 2 := by rw [dist_sq_eq, dist_sq_eq]; exact h
  exact (sq_eq_sq₀ dist_nonneg dist_nonneg).mp h1

lemma d2_symm (x y : Pt) : d2 x y = d2 y x := by simp only [d2]; ring

lemma d2_self (x : Pt) : d2 x x = 0 := by simp only [d2]; ring

lemma d2_pos {x y : Pt} (h : x ≠ y) : 0 < d2 x y := by
  rcases eq_or_ne (d2 x y) 0 with hd | hd
  · exfalso
    apply h
    have hsq : (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 = 0 := hd
    rw [add_eq_zero_iff_of_nonneg (sq_nonneg _) (sq_nonneg _)] at hsq
    rw [sq_eq_zero_iff, sq_eq_zero_iff] at hsq
    exact pt_ext (sub_eq_zero.mp hsq.1) (sub_eq_zero.mp hsq.2)
  · exact lt_of_le_of_ne (add_nonneg (sq_nonneg _) (sq_nonneg _)) (Ne.symm hd)

/-- Two vectors in the plane with vanishing cross product are proportional. -/
lemma exists_smul_of_cr_eq_zero {u v : Pt} (h : cr u v = 0) (hv : v ≠ 0) :
    ∃ t : ℝ, u = t • v := by
  have key : u 0 * v 1 = u 1 * v 0 := by
    have h' := h
    simp only [cr] at h'
    linarith [h']
  by_cases h0 : v 0 = 0
  · have h1 : v 1 ≠ 0 := by
      intro h1
      exact hv (pt_ext h0 h1)
    have hu0 : u 0 = 0 := by
      have e : u 0 * v 1 = 0 := by rw [h0, mul_zero] at key; exact key
      exact (mul_eq_zero.mp e).resolve_right h1
    refine ⟨u 1 / v 1, pt_ext ?_ ?_⟩
    · rw [PiLp.smul_apply, smul_eq_mul, hu0, h0, mul_zero]
    · rw [PiLp.smul_apply, smul_eq_mul]
      field_simp [h1]
  · refine ⟨u 0 / v 0, pt_ext ?_ ?_⟩
    · rw [PiLp.smul_apply, smul_eq_mul]
      field_simp [h0]
    · rw [PiLp.smul_apply, smul_eq_mul]
      field_simp [h0]
      linarith [key]

lemma cr_anti (u v : Pt) : cr u v = -cr v u := by simp only [cr]; ring

/-- Three affinely independent points in the plane span a nonzero area. -/
lemma cr_ne_zero_of_affineIndependent {A B C : Pt} (h : AffineIndependent ℝ ![A, B, C]) :
    cr (B - A) (C - A) ≠ 0 := by
  intro hcr
  have hnc : ¬ Collinear ℝ ({A, B, C} : Set Pt) :=
    (affineIndependent_iff_not_collinear_set (k := ℝ)).mp h
  apply hnc
  by_cases hAB : B - A = 0
  · rw [sub_eq_zero] at hAB
    rw [hAB, Set.insert_idem]
    exact collinear_pair ℝ A C
  · obtain ⟨t, ht⟩ := exists_smul_of_cr_eq_zero (u := C - A) (v := B - A)
      (by rw [cr_anti, hcr, neg_zero]) hAB
    rw [collinear_iff_of_mem (show A ∈ ({A, B, C} : Set Pt) by simp)]
    refine ⟨B - A, fun p hp => ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
    · exact ⟨t, by rw [← ht]; simp⟩

/-- The "master identity": squared distance from a barycentric combination.
This is the barycentric formula for the power of a point; the quantity
`d2 B C * β * γ + d2 A C * α * γ + d2 A B * α * β` is the barycentric
"circle form". -/
lemma bary_dist {O X A B C : Pt} (α β γ : ℝ) (hX : X = α • A + β • B + γ • C)
    (hsum : α + β + γ = 1) :
    d2 X O = α * d2 A O + β * d2 B O + γ * d2 C O
      - (d2 B C * β * γ + d2 A C * α * γ + d2 A B * α * β) := by
  subst hX
  simp only [d2, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  linear_combination
    (α * (A 0 ^ 2 + A 1 ^ 2) + β * (B 0 ^ 2 + B 1 ^ 2) + γ * (C 0 ^ 2 + C 1 ^ 2)
      - (O 0 ^ 2 + O 1 ^ 2)) • hsum

lemma d2_add_smul (X M R : Pt) (τ : ℝ) :
    d2 X (M + τ • R) = d2 X M - 2 * τ * ip (X - M) R + τ ^ 2 * d2 R 0 := by
  simp only [d2, ip, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, PiLp.zero_apply,
    smul_eq_mul]
  ring

/-- The algebraic heart of the problem: two quadratics with reciprocal roots.
If `z` and `y` are both negative and satisfy the two displayed quadratic equations
(coming from the two cyclic quadrilaterals), then `y * z = r * s`. -/
lemma key_lemma {b2 c2 D E r s z y : ℝ}
    (hb2 : 0 < b2) (hc2 : 0 < c2) (hr : 0 < r) (hs : 0 < s)
    (hz : z < 0) (hy : y < 0) (hDE : D + E = 0)
    (h1 : b2 * z ^ 2 + D * z - c2 * r * s = 0)
    (h2 : c2 * y ^ 2 + E * y - b2 * r * s = 0) :
    y * z = r * s := by
  have hr' : r ≠ 0 := ne_of_gt hr
  have hy' : y ≠ 0 := ne_of_lt hy
  have hζ : z / r < 0 := div_neg_of_neg_of_pos hz hr
  have hζ' : s / y < 0 := div_neg_of_pos_of_neg hs hy
  -- both `z / r` and `s / y` are roots of the quadratic `b2 * r * T^2 + D * T - c2 * s`
  have hΦζ : b2 * r * (z / r) ^ 2 + D * (z / r) - c2 * s = 0 := by
    have e : b2 * r * (z / r) ^ 2 + D * (z / r) - c2 * s
        = (b2 * z ^ 2 + D * z - c2 * r * s) / r := by
      field_simp [hr']
    rw [e, h1, zero_div]
  have hΦη : b2 * r * (s / y) ^ 2 + D * (s / y) - c2 * s = 0 := by
    have e : b2 * r * (s / y) ^ 2 + D * (s / y) - c2 * s
        = (-s * (c2 * y ^ 2 + E * y - b2 * r * s) + (s * y) * (D + E)) / y ^ 2 := by
      field_simp [hy']
      ring
    rw [e, show -s * (c2 * y ^ 2 + E * y - b2 * r * s) + (s * y) * (D + E) = 0 by
      linear_combination (s * y) • hDE - s • h2, zero_div]
  have hroot : z / r = s / y := by
    by_contra hne
    have hfact : (z / r - s / y) * (b2 * r * (z / r + s / y) + D) = 0 := by
      linear_combination hΦζ - hΦη
    have hsum : b2 * r * (z / r + s / y) + D = 0 := by
      rcases mul_eq_zero.mp hfact with h | h
      · exact absurd (sub_eq_zero.mp h) hne
      · exact h
    have hprod : b2 * r * (z / r) * (s / y) = -(c2 * s) := by
      linear_combination (z / r) • hsum - hΦζ
    have hpos : (0:ℝ) < (b2 * r) * ((z / r) * (s / y)) :=
      mul_pos (mul_pos hb2 hr) (mul_pos_of_neg_of_neg hζ hζ')
    have hcs : (0:ℝ) < c2 * s := mul_pos hc2 hs
    linarith [hprod, hpos, hcs]
  field_simp [hr', hy'] at hroot
  linear_combination hroot

snip end

problem usa2005_p3
    (A B C P Q C₁ B₁ : Pt)
    (hABC : AffineIndependent ℝ ![A, B, C])
    (_hacute : 0 < ⟪B - A, C - A⟫_ℝ ∧ 0 < ⟪A - B, C - B⟫_ℝ ∧ 0 < ⟪A - C, B - C⟫_ℝ)
    (hP : P ∈ openSegment ℝ B C)
    (hQ : Q ∈ openSegment ℝ B C)
    (hcyc₁ : Cospherical {A, P, B, C₁})
    (hpar₁ : cr (C₁ - Q) (A - C) = 0)
    (hside₁ : cr (B - A) (C₁ - A) * cr (B - A) (Q - A) < 0)
    (hcyc₂ : Cospherical {A, P, C, B₁})
    (hpar₂ : cr (B₁ - Q) (A - B) = 0)
    (hside₂ : cr (C - A) (B₁ - A) * cr (C - A) (Q - A) < 0) :
    Cospherical {B₁, C₁, P, Q} := by
  -- distinctness of the vertices
  have hABne : A ≠ B := by
    simpa using hABC.injective.ne (show (0 : Fin 3) ≠ 1 by decide)
  have hACne : A ≠ C := by
    simpa using hABC.injective.ne (show (0 : Fin 3) ≠ 2 by decide)
  have hΔne' : cr (B - A) (C - A) ≠ 0 := cr_ne_zero_of_affineIndependent hABC
  -- parametrize P and Q on side BC
  rw [openSegment_eq_image] at hP hQ
  obtain ⟨n, ⟨hn0, hn1⟩, (hPn : (1 - n) • B + n • C = P)⟩ := hP
  obtain ⟨s, ⟨hs0, hs1⟩, (hQn : (1 - s) • B + s • C = Q)⟩ := hQ
  have hPform : P = (0:ℝ) • A + (1 - n) • B + n • C := by rw [← hPn]; module
  have hQform : Q = (0:ℝ) • A + (1 - s) • B + s • C := by rw [← hQn]; module
  -- parametrize C₁ on the line through Q parallel to CA
  obtain ⟨t, ht⟩ := exists_smul_of_cr_eq_zero hpar₁ (sub_ne_zero.mpr hACne)
  set z := s - t with hz_def
  have hC₁ : C₁ = (s - z) • A + (1 - s) • B + z • C := by
    have h1 : C₁ = Q + t • (A - C) := by rw [← ht, add_sub_cancel]
    rw [h1, ← hQn, hz_def]
    module
  -- parametrize B₁ on the line through Q parallel to BA
  obtain ⟨u, hu⟩ := exists_smul_of_cr_eq_zero hpar₂ (sub_ne_zero.mpr hABne)
  set y := (1 - s) - u with hy_def
  have hB₁ : B₁ = ((1 - s) - y) • A + y • B + s • C := by
    have h1 : B₁ = Q + u • (A - B) := by rw [← hu, add_sub_cancel]
    rw [h1, ← hQn, hy_def]
    module
  set Δ := cr (B - A) (C - A) with hΔ
  have hΔne : Δ ≠ 0 := by rw [hΔ]; exact hΔne'
  -- the side conditions force z < 0 and y < 0
  have hcr₁ : cr (B - A) (C₁ - A) = z * Δ := by
    rw [hC₁, hΔ]
    simp only [cr, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  have hcrQ : cr (B - A) (Q - A) = s * Δ := by
    rw [← hQn, hΔ]
    simp only [cr, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  have hΔ'ne : cr (C - A) (B - A) ≠ 0 := by
    intro h
    apply hΔne
    rw [hΔ]
    simp only [cr] at h ⊢
    linarith
  have hcr₂ : cr (C - A) (B₁ - A) = y * cr (C - A) (B - A) := by
    rw [hB₁]
    simp only [cr, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  have hcrQ₂ : cr (C - A) (Q - A) = (1 - s) * cr (C - A) (B - A) := by
    rw [← hQn]
    simp only [cr, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  have hz : z < 0 := by
    rw [hcr₁, hcrQ] at hside₁
    have hΔ2 : (0:ℝ) < Δ ^ 2 := sq_pos_of_ne_zero hΔne
    have e1 : z * Δ * (s * Δ) = (z * s) * Δ ^ 2 := by ring
    rw [e1] at hside₁
    have h2 : z * s < 0 := by nlinarith [hside₁, hΔ2]
    nlinarith [h2, hs0]
  have hy : y < 0 := by
    rw [hcr₂, hcrQ₂] at hside₂
    have hΔ'2 : (0:ℝ) < (cr (C - A) (B - A)) ^ 2 := sq_pos_of_ne_zero hΔ'ne
    have e1 : y * cr (C - A) (B - A) * ((1 - s) * cr (C - A) (B - A))
        = (y * (1 - s)) * (cr (C - A) (B - A)) ^ 2 := by ring
    rw [e1] at hside₂
    have h2 : y * (1 - s) < 0 := by nlinarith [hside₂, hΔ'2]
    have h1s : (0:ℝ) < 1 - s := by linarith [hs1]
    nlinarith [h2, h1s]
  have h1s : (0:ℝ) < 1 - s := by linarith [hs1]
  -- sum checks for barycentric combinations
  have hsumP : (0:ℝ) + (1 - n) + n = 1 := by ring
  have hsumQ : (0:ℝ) + (1 - s) + s = 1 := by ring
  have hsumC1 : (s - z) + (1 - s) + z = 1 := by ring
  have hsumB1 : ((1 - s) - y) + y + s = 1 := by ring
  -- first circle: the quadratic equation for z
  obtain ⟨O₁, r₁, hO₁⟩ := hcyc₁
  have hdA₁ : d2 A O₁ = r₁ ^ 2 := by rw [← dist_sq_eq, hO₁ A (by simp)]
  have hdP₁ : d2 P O₁ = r₁ ^ 2 := by rw [← dist_sq_eq, hO₁ P (by simp)]
  have hdB₁ : d2 B O₁ = r₁ ^ 2 := by rw [← dist_sq_eq, hO₁ B (by simp)]
  have hdC₁₁ : d2 C₁ O₁ = r₁ ^ 2 := by rw [← dist_sq_eq, hO₁ C₁ (by simp)]
  have hMP := bary_dist (O := O₁) 0 (1 - n) n hPform hsumP
  rw [hdP₁, hdA₁, hdB₁] at hMP
  have hMC := bary_dist (O := O₁) (s - z) (1 - s) z hC₁ hsumC1
  rw [hdC₁₁, hdA₁, hdB₁] at hMC
  have hEq1n : n * (d2 A C * z ^ 2
      + (d2 B C * (s - n) + d2 A B * (1 - s) - d2 A C * s) * z
      - d2 A B * (1 - s) * s) = 0 := by
    linear_combination z • hMP - n • hMC
  have hEq1 : d2 A C * z ^ 2
      + (d2 B C * (s - n) + d2 A B * (1 - s) - d2 A C * s) * z
      - d2 A B * (1 - s) * s = 0 :=
    (mul_eq_zero.mp hEq1n).resolve_left (ne_of_gt hn0)
  -- second circle: the quadratic equation for y
  obtain ⟨O₂, r₂, hO₂⟩ := hcyc₂
  have hdA₂ : d2 A O₂ = r₂ ^ 2 := by rw [← dist_sq_eq, hO₂ A (by simp)]
  have hdP₂ : d2 P O₂ = r₂ ^ 2 := by rw [← dist_sq_eq, hO₂ P (by simp)]
  have hdC₂ : d2 C O₂ = r₂ ^ 2 := by rw [← dist_sq_eq, hO₂ C (by simp)]
  have hdB₁₂ : d2 B₁ O₂ = r₂ ^ 2 := by rw [← dist_sq_eq, hO₂ B₁ (by simp)]
  have hMP2 := bary_dist (O := O₂) 0 (1 - n) n hPform hsumP
  rw [hdP₂, hdA₂, hdC₂] at hMP2
  have hMB1 := bary_dist (O := O₂) ((1 - s) - y) y s hB₁ hsumB1
  rw [hdB₁₂, hdA₂, hdC₂] at hMB1
  have hEq2n : (1 - n) * (d2 A B * y ^ 2
      + (d2 B C * (n - s) + d2 A C * s - d2 A B * (1 - s)) * y
      - d2 A C * (1 - s) * s) = 0 := by
    linear_combination y • hMP2 - (1 - n) • hMB1
  have hEq2 : d2 A B * y ^ 2
      + (d2 B C * (n - s) + d2 A C * s - d2 A B * (1 - s)) * y
      - d2 A C * (1 - s) * s = 0 :=
    (mul_eq_zero.mp hEq2n).resolve_left (by linarith [hn1] : (1:ℝ) - n ≠ 0)
  -- the reciprocal-roots argument: y * z = (1 - s) * s, i.e. A, B₁, C₁ collinear
  have hDE : (d2 B C * (s - n) + d2 A B * (1 - s) - d2 A C * s)
      + (d2 B C * (n - s) + d2 A C * s - d2 A B * (1 - s)) = 0 := by ring
  have hyz : y * z = (1 - s) * s :=
    key_lemma (d2_pos hACne) (d2_pos hABne) h1s hs0 hz hy hDE hEq1 hEq2
  have hG : d2 A C * (z - s) + d2 A B * ((1 - s) - y) - d2 B C * (n - s) = 0 := by
    have hz' : z ≠ 0 := ne_of_lt hz
    have h1 : z * (d2 A C * (z - s) + d2 A B * ((1 - s) - y) - d2 B C * (n - s)) = 0 := by
      linear_combination hEq1 - (d2 A B) • hyz
    exact (mul_eq_zero.mp h1).resolve_left hz'
  -- the midpoint M of PQ, the 90°-rotation R of C - B, and the center O = M + τR
  have hbg : (2 - n - s) / 2 + (n + s) / 2 = 1 := by ring
  have hsumbg : (0:ℝ) + (2 - n - s) / 2 + (n + s) / 2 = 1 := by ring
  set M : Pt := (2⁻¹ : ℝ) • (P + Q) with hM
  have hMform : M = (0:ℝ) • A + ((2 - n - s) / 2) • B + ((n + s) / 2) • C := by
    rw [hM, hPform, hQform]
    module
  set R : Pt := !₂[-(C 1 - B 1), C 0 - B 0] with hR
  have hsz : (0:ℝ) < s - z := by linarith [hs0, hz]
  set Dτ : ℝ := 2 * ((s - z) * Δ) with hDτ
  have hDτne : Dτ ≠ 0 := by
    rw [hDτ]
    exact mul_ne_zero (by norm_num) (mul_ne_zero (ne_of_gt hsz) hΔne)
  set τ : ℝ := (d2 C₁ M - d2 P M) / Dτ with hτ
  have hτD : τ * Dτ = d2 C₁ M - d2 P M := by
    rw [hτ]
    exact div_mul_cancel₀ _ hDτne
  have hτD2 : 2 * τ * ((s - z) * Δ) = d2 C₁ M - d2 P M := by
    have e : 2 * τ * ((s - z) * Δ) = τ * Dτ := by rw [hDτ]; ring
    rw [e, hτD]
  have hdAM : d2 A M = ((2 - n - s) / 2) * d2 A B + ((n + s) / 2) * d2 A C
      - d2 B C * ((2 - n - s) / 2) * ((n + s) / 2) := by
    have h1 := bary_dist (O := A) 0 ((2 - n - s) / 2) ((n + s) / 2) hMform hsumbg
    simp only [d2_self] at h1
    rw [d2_symm B A, d2_symm C A] at h1
    rw [d2_symm A M]
    linear_combination h1
  have hdBM : d2 B M = d2 B C * ((n + s) / 2) ^ 2 := by
    have h1 := bary_dist (O := B) 0 ((2 - n - s) / 2) ((n + s) / 2) hMform hsumbg
    simp only [d2_self] at h1
    rw [d2_symm C B] at h1
    rw [d2_symm B M]
    linear_combination h1
  have hdCM : d2 C M = d2 B C * ((2 - n - s) / 2) ^ 2 := by
    have h1 := bary_dist (O := C) 0 ((2 - n - s) / 2) ((n + s) / 2) hMform hsumbg
    simp only [d2_self] at h1
    rw [d2_symm C M]
    linear_combination h1
  have hdQM : d2 Q M = d2 P M := by
    have hQ' := bary_dist (O := M) 0 (1 - s) s hQform hsumQ
    have hP' := bary_dist (O := M) 0 (1 - n) n hPform hsumP
    rw [hdBM, hdCM] at hQ' hP'
    linear_combination hQ' - hP'
  have hK : (d2 B₁ M - d2 P M) * (s - z) = (d2 C₁ M - d2 P M) * (1 - s - y) := by
    have hB := bary_dist (O := M) ((1 - s) - y) y s hB₁ hsumB1
    have hC := bary_dist (O := M) (s - z) (1 - s) z hC₁ hsumC1
    have hP' := bary_dist (O := M) 0 (1 - n) n hPform hsumP
    rw [hdAM, hdBM, hdCM] at hB hC hP'
    linear_combination
      ((z - s) * (y - (1 - s))) • hG + (s - z) • hB + (-(1 - s - y)) • hC
        + ((1 - s - y) - (s - z)) • hP'
  have hRnorm : d2 R 0 = d2 B C := by
    rw [hR]
    simp only [d2, Matrix.cons_val_zero, Matrix.cons_val_one, PiLp.zero_apply]
    ring
  have hipA : ip (A - M) R = Δ := by
    rw [hMform, hR, hΔ]
    simp only [ip, cr, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination (B 0 * C 1 - B 1 * C 0) • hbg
  have hipB : ip (B - M) R = 0 := by
    rw [hMform, hR]
    simp only [ip, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination (B 0 * C 1 - B 1 * C 0) • hbg
  have hipC : ip (C - M) R = 0 := by
    rw [hMform, hR]
    simp only [ip, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination (B 0 * C 1 - B 1 * C 0) • hbg
  have hAO : d2 A (M + τ • R) = d2 A M - 2 * τ * Δ + τ ^ 2 * d2 B C := by
    rw [d2_add_smul, hipA, hRnorm]
  have hBO : d2 B (M + τ • R) = d2 B M + τ ^ 2 * d2 B C := by
    rw [d2_add_smul, hipB, hRnorm]
    ring
  have hCO : d2 C (M + τ • R) = d2 C M + τ ^ 2 * d2 B C := by
    rw [d2_add_smul, hipC, hRnorm]
    ring
  -- the distance from a barycentric point to the center O
  have hmain : ∀ (X : Pt) (α β γ : ℝ), X = α • A + β • B + γ • C → α + β + γ = 1 →
      d2 X (M + τ • R) - τ ^ 2 * d2 B C = d2 X M - 2 * τ * α * Δ := by
    intro X α β γ hX hsum
    have h1 := bary_dist (O := M + τ • R) α β γ hX hsum
    rw [hAO, hBO, hCO] at h1
    have h2 := bary_dist (O := M) α β γ hX hsum
    linear_combination h1 - h2 + (τ ^ 2 * d2 B C) • hsum
  have hQO : d2 Q (M + τ • R) = d2 P (M + τ • R) := by
    have h1 := hmain Q 0 (1 - s) s hQform hsumQ
    have h2 := hmain P 0 (1 - n) n hPform hsumP
    linarith [h1, h2, hdQM]
  have hC1O : d2 C₁ (M + τ • R) = d2 P (M + τ • R) := by
    have h1 := hmain C₁ (s - z) (1 - s) z hC₁ hsumC1
    have h2 := hmain P 0 (1 - n) n hPform hsumP
    have h3 : d2 C₁ M - 2 * τ * (s - z) * Δ = d2 P M := by
      have e : 2 * τ * (s - z) * Δ = 2 * τ * ((s - z) * Δ) := by ring
      rw [e, hτD2]
      ring
    linarith [h1, h2, h3]
  have hB1O : d2 B₁ (M + τ • R) = d2 P (M + τ • R) := by
    have h1 := hmain B₁ ((1 - s) - y) y s hB₁ hsumB1
    have h2 := hmain P 0 (1 - n) n hPform hsumP
    have h3 : d2 B₁ M - 2 * τ * ((1 - s) - y) * Δ = d2 P M := by
      have hsz' : (s - z) ≠ 0 := ne_of_gt hsz
      have h4 : (d2 B₁ M - 2 * τ * ((1 - s) - y) * Δ - d2 P M) * (s - z) = 0 := by
        have e1 : (d2 B₁ M - 2 * τ * ((1 - s) - y) * Δ - d2 P M) * (s - z)
            = (d2 B₁ M - d2 P M) * (s - z) - (2 * τ * ((1 - s) - y) * Δ) * (s - z) := by
          ring
        rw [e1, hK]
        have e2 : (2 * τ * ((1 - s) - y) * Δ) * (s - z)
            = (2 * τ * ((s - z) * Δ)) * ((1 - s) - y) := by ring
        rw [e2, hτD2]
        ring
      have h5 : d2 B₁ M - 2 * τ * ((1 - s) - y) * Δ - d2 P M = 0 :=
        (mul_eq_zero.mp h4).resolve_right hsz'
      linarith [h5]
    linarith [h1, h2, h3]
  -- assemble the circle
  refine ⟨M + τ • R, dist P (M + τ • R), fun p hp => ?_⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact dist_eq_of_d2_eq hB1O
  · exact dist_eq_of_d2_eq hC1O
  · rfl
  · exact dist_eq_of_d2_eq hQO

end Usa2005P3
