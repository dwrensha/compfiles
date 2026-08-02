/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# USA Mathematical Olympiad 2007, Problem 2

A square grid on the Euclidean plane consists of all points (m, n), where m and n
are integers. Is it possible to cover all grid points by an infinite family of discs
with non-overlapping interiors if each disc in the family has radius at least 5?

We show that the answer is **no**: such a covering cannot exist.  The proof proceeds
by contradiction.  Write `f i x = dist x (c i) - r i` for the *clearance* of disk `i`
at `x` (negative iff `x` lies in the disk's interior) and let `g x` be the infimum of
the clearances.  The key facts are:

* a "three rays" lemma: at any point, at most two disks of radius ≥ 5 with disjoint
  interiors can have clearance `< R0 := 10/√3 - 5` (the inradius of the gap between
  three mutually tangent disks of radius 5);
* hence, starting from a point whose clearance is close to the supremum `R` of `g`,
  one can iterate ("climb") to a point with `g > R`, contradicting the definition of
  `R`; the climb uses a potential that strictly decreases at every step;
* therefore some point `x` has `g x > 1/√2`, so the open disk around `x` of radius
  `g x` contains a lattice point, which is then not covered by any disk.
-/

namespace Usa2007P2

open scoped InnerProductSpace

snip begin

/-- The Euclidean plane. -/
abbrev Pl := EuclideanSpace ℝ (Fin 2)

/-- The "clearance" of disk `i` at point `x`: its (signed) distance to the disk's
boundary, i.e. `dist x (c i) - r i`.  Negative values mean `x` lies strictly inside
the disk; `f i x < ρ` iff the closed ball of radius `ρ` around `x` meets the disk. -/
noncomputable def f {ι : Type*} (c : ι → Pl) (r : ι → ℝ) (i : ι) (x : Pl) : ℝ := dist x (c i) - r i

/-- The clearance function: infimum of all disks' clearances at `x`. -/
noncomputable def g {ι : Type*} (c : ι → Pl) (r : ι → ℝ) (x : Pl) : ℝ := ⨅ i, f c r i x

lemma f_apply {ι : Type*} (c : ι → Pl) (r : ι → ℝ) (i : ι) (x : Pl) :
    f c r i x = dist x (c i) - r i := rfl

/-- Each disk's clearance is 1-Lipschitz. -/
lemma f_lipschitz {ι : Type*} (c : ι → Pl) (r : ι → ℝ) (i : ι) :
    LipschitzWith 1 (f c r i) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [f_apply, f_apply, NNReal.coe_one, one_mul, Real.dist_eq]
  have h : (dist x (c i) - r i) - (dist y (c i) - r i) = dist x (c i) - dist y (c i) := by ring
  rw [h]
  exact abs_dist_sub_le x y (c i)

/-- The clearance difference is bounded by the distance. -/
lemma f_sub_le {ι : Type*} (c : ι → Pl) (r : ι → ℝ) (i : ι) (x y : Pl) :
    f c r i x - f c r i y ≤ dist x y := by
  rw [f_apply, f_apply]
  have h := (f_lipschitz c r i).dist_le_mul x y
  rw [NNReal.coe_one, one_mul, Real.dist_eq, f_apply, f_apply] at h
  have h2 : (dist x (c i) - r i) - (dist y (c i) - r i) = dist x (c i) - dist y (c i) := by ring
  rw [h2] at h
  linarith [(abs_le.mp h).2]

/-- The lattice point with integer coordinates `m`, `n`. -/
def lat (m n : ℤ) : Pl := !₂[(m : ℝ), (n : ℝ)]

/-- The distance in the plane is the Euclidean norm of the coordinate differences. -/
lemma dist_eq_sqrt_sq (p q : Pl) :
    dist p q = Real.sqrt ((p 0 - q 0)^2 + (p 1 - q 1)^2) := by
  rw [dist_eq_norm, EuclideanSpace.norm_eq, Fin.sum_univ_two]
  simp [Real.norm_eq_abs, sq_abs]

/-- A single coordinate difference is bounded by the distance. -/
lemma abs_coord_sub_le_dist (p q : Pl) (k : Fin 2) : |p k - q k| ≤ dist p q := by
  rw [dist_eq_sqrt_sq]
  have hk : |p k - q k| = Real.sqrt ((p k - q k)^2) := by rw [Real.sqrt_sq_eq_abs]
  rw [hk]
  apply Real.sqrt_le_sqrt
  fin_cases k <;> simp <;> nlinarith [sq_nonneg (p 1 - q 1), sq_nonneg (p 0 - q 0)]

/-- Every point of the plane is within `1/√2` of a lattice point. -/
lemma exists_lat_dist_le (x : Pl) : ∃ m n : ℤ, dist (lat m n) x ≤ 1 / Real.sqrt 2 := by
  use round (x 0), round (x 1)
  have h0 : |x 0 - round (x 0)| ≤ 1/2 := abs_sub_round (x 0)
  have h1 : |x 1 - round (x 1)| ≤ 1/2 := abs_sub_round (x 1)
  have hdist : dist (lat (round (x 0)) (round (x 1))) x =
      Real.sqrt (((round (x 0) : ℝ) - x 0)^2 + ((round (x 1) : ℝ) - x 1)^2) := by
    rw [dist_eq_sqrt_sq]
    simp [lat, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hdist]
  have hsq : ((round (x 0) : ℝ) - x 0)^2 + ((round (x 1) : ℝ) - x 1)^2 ≤ 1/2 := by
    have h0'' : |(round (x 0) : ℝ) - x 0| ≤ 1/2 := by
      rw [abs_sub_comm]; exact h0
    have h1'' : |(round (x 1) : ℝ) - x 1| ≤ 1/2 := by
      rw [abs_sub_comm]; exact h1
    have h00 : ((round (x 0) : ℝ) - x 0)^2 ≤ (1/2)^2 := by
      nlinarith [abs_le.mp h0'']
    have h01 : ((round (x 1) : ℝ) - x 1)^2 ≤ (1/2)^2 := by
      nlinarith [abs_le.mp h1'']
    linarith
  have hsqrt : Real.sqrt (1/2) = 1 / Real.sqrt 2 := by
    rw [Real.sqrt_div (by norm_num : (0:ℝ) ≤ 1), Real.sqrt_one]
  rw [← hsqrt]
  exact Real.sqrt_le_sqrt hsq

/-- Two open balls of positive radius with disjoint interiors are at distance at
least the sum of the radii.  (Local copy of `dist_add_dist_of_disjoint_balls`,
which is only stated later in this file and so cannot be used here.) -/
private lemma disjoint_balls_add_le_dist {x y : Pl} {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (h : Disjoint (Metric.ball x r₁) (Metric.ball y r₂)) : r₁ + r₂ ≤ dist x y := by
  by_contra! hlt
  have hxy : x ≠ y := by
    intro he
    subst he
    exact Set.disjoint_left.mp h (Metric.mem_ball_self hr₁) (Metric.mem_ball_self hr₂)
  set d := dist x y with hd
  have hd0 : 0 < d := by rw [hd]; exact dist_pos.mpr hxy
  rcases le_or_gt d (r₁ - r₂) with h1 | h1
  · -- then `y` lies in both balls
    have h2 : dist y x < r₁ := by rw [dist_comm, ← hd]; linarith
    exact Set.disjoint_left.mp h h2 (Metric.mem_ball_self hr₂)
  rcases le_or_gt d (r₂ - r₁) with h2 | h2
  · have h3 : dist x y < r₂ := by rw [← hd]; linarith
    exact Set.disjoint_right.mp h h3 (Metric.mem_ball_self hr₁)
  · -- generic case: pick a point on the segment
    set t := (r₁ - r₂ + d) / (2 * d) with ht
    have hyn : ‖y - x‖ = d := by rw [hd, dist_eq_norm, norm_sub_rev]
    have ht0 : 0 < t := by
      rw [ht]; apply div_pos _ (by positivity); linarith
    have ht1 : t < 1 := by
      rw [ht]; apply (div_lt_one (by positivity)).mpr; linarith
    have hz1 : dist (x + t • (y - x)) x = t * d := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs t,
        abs_of_pos ht0, hyn]
    have hz2 : dist (x + t • (y - x)) y = (1 - t) * d := by
      have h4 : x + t • (y - x) - y = (t - 1) • (y - x) := by
        rw [sub_smul, one_smul, smul_sub]; abel
      rw [dist_eq_norm, h4, norm_smul, Real.norm_eq_abs (t - 1),
        abs_of_neg (by linarith), hyn]
      ring
    have h3 : dist (x + t • (y - x)) x < r₁ := by
      have htd : t * d = (r₁ - r₂ + d) / 2 := by
        rw [ht]; field_simp [hd0.ne']
      rw [hz1, htd]; linarith
    have h4 : dist (x + t • (y - x)) y < r₂ := by
      have h1td : (1 - t) * d = (d - r₁ + r₂) / 2 := by
        have htd : t * d = (r₁ - r₂ + d) / 2 := by
          rw [ht]; field_simp [hd0.ne']
        linarith
      rw [hz2, h1td]; linarith
    exact Set.disjoint_left.mp h h3 h4

/-- Two reals with the same floor differ by less than `1`. -/
private lemma abs_sub_lt_one_of_floor_eq_floor' {a b : ℝ} (h : ⌊a⌋ = ⌊b⌋) : |a - b| < 1 := by
  have ha : a < b + 1 := by
    calc a < ⌊a⌋ + 1 := Int.lt_floor_add_one a
      _ = ⌊b⌋ + 1 := by rw [h]
      _ ≤ b + 1 := by linarith [Int.floor_le b]
  have hb : b < a + 1 := by
    calc b < ⌊b⌋ + 1 := Int.lt_floor_add_one b
      _ = ⌊a⌋ + 1 := by rw [h]
      _ ≤ a + 1 := by linarith [Int.floor_le a]
  rw [abs_sub_lt_iff]
  exact ⟨by linarith, by linarith⟩

/-- The "sub-center" of a disk of radius `r₀` seen from a point `x` outside the
disk: the point on the segment from the center `c₀` to the boundary point nearest
`x` that is at distance `r₀ - 5` from `c₀`. -/
private noncomputable def subcenter (x c₀ : Pl) (r₀ : ℝ) : Pl :=
  c₀ + ((r₀ - 5) / r₀) • ((r₀ / dist x c₀) • (x - c₀))

/-- Properties of the sub-center of a disk of radius `r₀ ≥ 5` whose clearance at
`x` is nonnegative: it is at distance `r₀ - 5` from the center and at distance at
most `5 + (dist x c₀ - r₀)` from `x`; in particular the open ball of radius `5`
around it is contained in the original open disk. -/
private lemma subcenter_props (x c₀ : Pl) {r₀ : ℝ} (hr₀ : 5 ≤ r₀) (hrd : r₀ ≤ dist x c₀) :
    dist (subcenter x c₀ r₀) c₀ = r₀ - 5 ∧
    dist (subcenter x c₀ r₀) x ≤ 5 + (dist x c₀ - r₀) ∧
    Metric.ball (subcenter x c₀ r₀) 5 ⊆ Metric.ball c₀ r₀ := by
  have hd : 0 < dist x c₀ := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 5) (le_trans hr₀ hrd)
  have hr₀' : 0 < r₀ := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 5) hr₀
  show dist (c₀ + ((r₀ - 5) / r₀) • ((r₀ / dist x c₀) • (x - c₀))) c₀ = r₀ - 5 ∧
    dist (c₀ + ((r₀ - 5) / r₀) • ((r₀ / dist x c₀) • (x - c₀))) x ≤
      5 + (dist x c₀ - r₀) ∧
    Metric.ball (c₀ + ((r₀ - 5) / r₀) • ((r₀ / dist x c₀) • (x - c₀))) 5 ⊆
      Metric.ball c₀ r₀
  set d := dist x c₀ with hd_def
  set v := x - c₀ with hv
  set s := r₀ / d with hs
  set t := (r₀ - 5) / r₀ with ht
  set p := c₀ + s • v with hp
  have hnv : ‖v‖ = d := by rw [hv, hd_def, dist_eq_norm]
  have hs0 : 0 ≤ s := by rw [hs]; exact div_nonneg hr₀'.le hd.le
  have hs1 : s ≤ 1 := by rw [hs]; exact (div_le_one hd).mpr hrd
  have hsd : s * d = r₀ := by rw [hs]; exact div_mul_cancel₀ r₀ hd.ne'
  have ht0 : 0 ≤ t := by rw [ht]; exact div_nonneg (by linarith) hr₀'.le
  have ht1 : t ≤ 1 := by rw [ht]; exact (div_le_one hr₀').mpr (by linarith)
  have htr : t * r₀ = r₀ - 5 := by rw [ht]; exact div_mul_cancel₀ (r₀ - 5) hr₀'.ne'
  have hsv : ‖s • v‖ = r₀ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0, hnv, hsd]
  have hpc : dist p c₀ = r₀ := by
    have h1 : p - c₀ = s • v := by rw [hp]; exact add_sub_cancel_left _ _
    rw [dist_eq_norm, h1, hsv]
  have hpx : dist p x = d - r₀ := by
    have h1 : p - x = (s - 1) • v := by
      rw [hp, hv, sub_smul, one_smul]
      abel
    have h2 : (1 - s) * d = d - r₀ := by
      have h3 : (1 - s) * d = d - s * d := by ring
      rw [h3, hsd]
    have h4 : -(s - 1) = 1 - s := by ring
    rw [dist_eq_norm, h1, norm_smul, Real.norm_eq_abs,
      abs_of_nonpos (by linarith : s - 1 ≤ 0), hnv, h4, h2]
  have hoc : dist (c₀ + t • (s • v)) c₀ = r₀ - 5 := by
    have h1 : c₀ + t • (s • v) - c₀ = t • (s • v) := add_sub_cancel_left _ _
    rw [dist_eq_norm, h1, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0, hsv, htr]
  have hop : dist (c₀ + t • (s • v)) p = 5 := by
    have h1 : c₀ + t • (s • v) - p = (t - 1) • (s • v) := by
      rw [hp, sub_smul, one_smul]
      abel
    have h3 : (1 - t) * r₀ = 5 := by
      have h4 : (1 - t) * r₀ = r₀ - t * r₀ := by ring
      rw [h4, htr]
      ring
    have h5 : -(t - 1) = 1 - t := by ring
    rw [dist_eq_norm, h1, norm_smul, Real.norm_eq_abs,
      abs_of_nonpos (by linarith : t - 1 ≤ 0), hsv, h5, h3]
  refine ⟨hoc, ?_, ?_⟩
  · calc dist (c₀ + t • (s • v)) x
        ≤ dist (c₀ + t • (s • v)) p + dist p x := dist_triangle _ _ _
      _ = 5 + (d - r₀) := by rw [hop, hpx]
  · intro z hz
    rw [Metric.mem_ball] at hz ⊢
    calc dist z c₀ ≤ dist z (c₀ + t • (s • v)) + dist (c₀ + t • (s • v)) c₀ :=
          dist_triangle _ _ _
      _ = dist z (c₀ + t • (s • v)) + (r₀ - 5) := by rw [hoc]
      _ < 5 + (r₀ - 5) := by linarith
      _ = r₀ := by ring

/-- The packing bound: only finitely many disks have their boundary within a fixed
distance `C` of a given point. -/
lemma packing_finite {ι : Type*} {c : ι → Pl} {r : ι → ℝ} (hr : ∀ i, 5 ≤ r i)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Metric.ball (c i) (r i)) (Metric.ball (c j) (r j)))
    (x : Pl) (C : ℝ) : {i | f c r i x ≤ C}.Finite := by
  classical
  have hsplit : {i | f c r i x ≤ C} =
      {i | 0 ≤ f c r i x ∧ f c r i x ≤ C} ∪ {i | f c r i x < 0 ∧ f c r i x ≤ C} := by
    ext i
    simp only [Set.mem_setOf_eq, Set.mem_union]
    constructor
    · intro hi
      rcases le_or_gt 0 (f c r i x) with h0 | h0
      · exact Or.inl ⟨h0, hi⟩
      · exact Or.inr ⟨h0, hi⟩
    · rintro (⟨-, h⟩ | ⟨-, h⟩) <;> exact h
  rw [hsplit]
  refine Set.Finite.union ?_ ?_
  · -- indices with nonnegative clearance: a grid argument
    have hP : ∀ i ∈ {i | 0 ≤ f c r i x ∧ f c r i x ≤ C},
        dist (subcenter x (c i) (r i)) (c i) = r i - 5 ∧
        dist (subcenter x (c i) (r i)) x ≤ 5 + (dist x (c i) - r i) ∧
        Metric.ball (subcenter x (c i) (r i)) 5 ⊆ Metric.ball (c i) (r i) := by
      intro i hi
      obtain ⟨h0, -⟩ := hi
      rw [f_apply] at h0
      exact subcenter_props x (c i) (hr i) (by linarith)
    have hdist10 : ∀ i ∈ {i | 0 ≤ f c r i x ∧ f c r i x ≤ C},
        ∀ j ∈ {i | 0 ≤ f c r i x ∧ f c r i x ≤ C}, i ≠ j →
        10 ≤ dist (subcenter x (c i) (r i)) (subcenter x (c j) (r j)) := by
      intro i hi j hj hne
      have hd : Disjoint (Metric.ball (subcenter x (c i) (r i)) 5)
          (Metric.ball (subcenter x (c j) (r j)) 5) :=
        Disjoint.mono (hP i hi).2.2 (hP j hj).2.2 (hdisj i j hne)
      have h := disjoint_balls_add_le_dist (by norm_num : (0 : ℝ) < 5)
        (by norm_num : (0 : ℝ) < 5) hd
      linarith
    have hinj : Set.InjOn (fun i => (⌊subcenter x (c i) (r i) 0 / 7⌋,
        ⌊subcenter x (c i) (r i) 1 / 7⌋)) {i | 0 ≤ f c r i x ∧ f c r i x ≤ C} := by
      intro i hi j hj hij
      by_contra hne
      have h0 : ⌊subcenter x (c i) (r i) 0 / 7⌋ = ⌊subcenter x (c j) (r j) 0 / 7⌋ :=
        congrArg Prod.fst hij
      have h1 : ⌊subcenter x (c i) (r i) 1 / 7⌋ = ⌊subcenter x (c j) (r j) 1 / 7⌋ :=
        congrArg Prod.snd hij
      have hc0 : |subcenter x (c i) (r i) 0 - subcenter x (c j) (r j) 0| < 7 := by
        have h := abs_sub_lt_one_of_floor_eq_floor' h0
        rw [← sub_div, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 7),
          div_lt_one (by norm_num : (0 : ℝ) < 7)] at h
        exact h
      have hc1 : |subcenter x (c i) (r i) 1 - subcenter x (c j) (r j) 1| < 7 := by
        have h := abs_sub_lt_one_of_floor_eq_floor' h1
        rw [← sub_div, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 7),
          div_lt_one (by norm_num : (0 : ℝ) < 7)] at h
        exact h
      have hlt : dist (subcenter x (c i) (r i)) (subcenter x (c j) (r j)) < 10 := by
        rw [dist_eq_sqrt_sq]
        have hsq : (subcenter x (c i) (r i) 0 - subcenter x (c j) (r j) 0) ^ 2 +
            (subcenter x (c i) (r i) 1 - subcenter x (c j) (r j) 1) ^ 2 <
            (10 : ℝ) ^ 2 := by
          obtain ⟨ha0l, ha0u⟩ := abs_lt.mp hc0
          obtain ⟨ha1l, ha1u⟩ := abs_lt.mp hc1
          nlinarith
        have h2 := Real.sqrt_lt_sqrt (by positivity) hsq
        rwa [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 10)] at h2
      have hge := hdist10 i hi j hj hne
      linarith
    have hcoord : ∀ i ∈ {i | 0 ≤ f c r i x ∧ f c r i x ≤ C}, ∀ k : Fin 2,
        |subcenter x (c i) (r i) k - x k| ≤ C + 5 := by
      intro i hi k
      have hle : dist (subcenter x (c i) (r i)) x ≤ C + 5 := by
        have h2 := (hP i hi).2.1
        obtain ⟨-, hC⟩ := hi
        rw [f_apply] at hC
        linarith
      exact le_trans (abs_coord_sub_le_dist _ _ k) hle
    have hIm : (fun i => (⌊subcenter x (c i) (r i) 0 / 7⌋,
        ⌊subcenter x (c i) (r i) 1 / 7⌋)) ''
        {i | 0 ≤ f c r i x ∧ f c r i x ≤ C} ⊆
        ↑(Finset.Icc ⌊(x 0 - (C + 5)) / 7⌋ ⌊(x 0 + (C + 5)) / 7⌋ ×ˢ
          Finset.Icc ⌊(x 1 - (C + 5)) / 7⌋ ⌊(x 1 + (C + 5)) / 7⌋) := by
      rintro y ⟨i, hi, rfl⟩
      obtain ⟨hb0l, hb0u⟩ := abs_le.mp (hcoord i hi 0)
      obtain ⟨hb1l, hb1u⟩ := abs_le.mp (hcoord i hi 1)
      have h7 : (0 : ℝ) < 7 := by norm_num
      have hlo0 : ⌊(x 0 - (C + 5)) / 7⌋ ≤ ⌊subcenter x (c i) (r i) 0 / 7⌋ :=
        Int.floor_mono ((div_le_div_iff_of_pos_right h7).mpr (by linarith))
      have hhi0 : ⌊subcenter x (c i) (r i) 0 / 7⌋ ≤ ⌊(x 0 + (C + 5)) / 7⌋ :=
        Int.floor_mono ((div_le_div_iff_of_pos_right h7).mpr (by linarith))
      have hlo1 : ⌊(x 1 - (C + 5)) / 7⌋ ≤ ⌊subcenter x (c i) (r i) 1 / 7⌋ :=
        Int.floor_mono ((div_le_div_iff_of_pos_right h7).mpr (by linarith))
      have hhi1 : ⌊subcenter x (c i) (r i) 1 / 7⌋ ≤ ⌊(x 1 + (C + 5)) / 7⌋ :=
        Int.floor_mono ((div_le_div_iff_of_pos_right h7).mpr (by linarith))
      exact Finset.mem_coe.mpr (Finset.mem_product.mpr
        ⟨Finset.mem_Icc.mpr ⟨hlo0, hhi0⟩, Finset.mem_Icc.mpr ⟨hlo1, hhi1⟩⟩)
    exact ((Finset.finite_toSet _).subset hIm).of_finite_image hinj
  · -- indices with negative clearance: at most one
    have hsub : {i | f c r i x < 0}.Subsingleton := by
      intro i hi j hj
      simp only [Set.mem_setOf_eq, f_apply] at hi hj
      by_contra hne
      have hxi : x ∈ Metric.ball (c i) (r i) := by
        rw [Metric.mem_ball]
        linarith
      have hxj : x ∈ Metric.ball (c j) (r j) := by
        rw [Metric.mem_ball]
        linarith
      exact Set.disjoint_left.mp (hdisj i j hne) hxi hxj
    exact hsub.finite.subset (fun i hi => hi.1)

/-- Attainment: at each point, the infimum clearance is attained by some disk. -/
lemma exists_f_min {ι : Type*} [hι : Nonempty ι] {c : ι → Pl} {r : ι → ℝ} (hr : ∀ i, 5 ≤ r i)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Metric.ball (c i) (r i)) (Metric.ball (c j) (r j)))
    (x : Pl) : ∃ i₀, ∀ j, f c r i₀ x ≤ f c r j x := by
  obtain ⟨i₀⟩ := hι
  have hfin : {i | f c r i x ≤ f c r i₀ x}.Finite := packing_finite hr hdisj x (f c r i₀ x)
  let s := hfin.toFinset
  have hs : s.Nonempty := ⟨i₀, hfin.mem_toFinset.mpr (by simp)⟩
  obtain ⟨im, him, hmin⟩ := s.exists_min_image (fun i => f c r i x) hs
  refine ⟨im, fun j => ?_⟩
  by_cases hj : f c r j x ≤ f c r i₀ x
  · exact hmin j (hfin.mem_toFinset.mpr hj)
  · push Not at hj
    have hle : f c r im x ≤ f c r i₀ x := by
      simpa [s, hfin] using him
    linarith

/-- The clearance function equals the attained minimum. -/
lemma g_eq_f_min {ι : Type*} [hι : Nonempty ι] {c : ι → Pl} {r : ι → ℝ} (hr : ∀ i, 5 ≤ r i)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Metric.ball (c i) (r i)) (Metric.ball (c j) (r j)))
    (x : Pl) : ∃ i₀, g c r x = f c r i₀ x ∧ ∀ j, f c r i₀ x ≤ f c r j x := by
  obtain ⟨i₀, hmin⟩ := exists_f_min (c := c) (r := r) hr hdisj x
  refine ⟨i₀, ?_, hmin⟩
  have hleast : IsLeast (Set.range (fun i => f c r i x)) (f c r i₀ x) :=
    ⟨⟨i₀, rfl⟩, fun b hb => by obtain ⟨j, rfl⟩ := hb; exact hmin j⟩
  rw [g, iInf]
  exact hleast.csInf_eq

/-- The clearance is below every disk's clearance. -/
lemma g_le_f {ι : Type*} [Nonempty ι] {c : ι → Pl} {r : ι → ℝ} (hr : ∀ i, 5 ≤ r i)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Metric.ball (c i) (r i)) (Metric.ball (c j) (r j)))
    (x : Pl) (i : ι) : g c r x ≤ f c r i x := by
  obtain ⟨i₀, hge, hmin⟩ := g_eq_f_min hr hdisj x
  rw [hge]
  exact hmin i

/-- The clearance function is 1-Lipschitz. -/
lemma g_lipschitz {ι : Type*} [Nonempty ι] {c : ι → Pl} {r : ι → ℝ} (hr : ∀ i, 5 ≤ r i)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Metric.ball (c i) (r i)) (Metric.ball (c j) (r j))) :
    LipschitzWith 1 (g c r) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [NNReal.coe_one, one_mul, Real.dist_eq]
  obtain ⟨ix, hgx, hminx⟩ := g_eq_f_min (c := c) (r := r) hr hdisj x
  obtain ⟨iy, hgy, hminy⟩ := g_eq_f_min (c := c) (r := r) hr hdisj y
  have h2 : f c r ix x - f c r iy y ≤ dist x y := by
    have h21 : f c r ix x ≤ f c r iy x := hminx iy
    have h22 : f c r iy x - f c r iy y ≤ dist x y := f_sub_le c r iy x y
    linarith
  have h5 : f c r iy y - f c r ix x ≤ dist x y := by
    have h51 : f c r iy y ≤ f c r ix y := hminy ix
    have h52 : f c r ix y - f c r ix x ≤ dist x y := by
      rw [dist_comm]; exact f_sub_le c r ix y x
    linarith
  rw [hgx, hgy]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The clearance function is continuous. -/
lemma g_continuous {ι : Type*} [Nonempty ι] {c : ι → Pl} {r : ι → ℝ} (hr : ∀ i, 5 ≤ r i)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Metric.ball (c i) (r i)) (Metric.ball (c j) (r j))) :
    Continuous (g c r) := (g_lipschitz hr hdisj).continuous

lemma lat_apply (m n : ℤ) (i : Fin 2) :
    lat m n i = ![((m : ℝ)), ((n : ℝ))] i := rfl

/-- The inradius of the gap between three mutually tangent disks of radius 5,
`R0 = 10/√3 - 5 ≈ 0.7735`.  It is the critical threshold of the problem:
three disks of radius ≥ 5 with disjoint interiors cannot all have clearance
`< R0` at any point, while `R0 > 1/√2`, so a clearance `> R0` (in fact
`> 1/√2`) forces an uncovered lattice point. -/
noncomputable def R0 : ℝ := 10 / Real.sqrt 3 - 5

/-- If `0 ≤ t` and `3t² + 30t - 25 ≥ 0` then `t ≥ R0`. -/
lemma R0_le_of_quadratic {t : ℝ} (ht0 : 0 ≤ t) (h : 0 ≤ 3 * t^2 + 30 * t - 25) :
    R0 ≤ t := by
  have hsq : 100/3 ≤ (t + 5)^2 := by nlinarith
  have h10 : (10 / Real.sqrt 3)^2 = 100/3 := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]; norm_num
  have h9 : 10 / Real.sqrt 3 = Real.sqrt (100/3) := by
    rw [← h10, Real.sqrt_sq (by positivity : (0:ℝ) ≤ 10 / Real.sqrt 3)]
  have h5 : Real.sqrt (100/3) ≤ t + 5 := Real.sqrt_le_iff.mpr ⟨by linarith, hsq⟩
  rw [R0, h9]; linarith

lemma R0_pos : 0 < R0 := by
  have h : (5:ℝ) < 10 / Real.sqrt 3 := by
    have h1 : (5:ℝ)^2 < (10 / Real.sqrt 3)^2 := by
      rw [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]; norm_num
    have h2 := sq_lt_sq.mp h1
    rwa [abs_of_pos (by norm_num), abs_of_pos (by positivity)] at h2
  rw [R0]; linarith

lemma R0_gt_inv_sqrt2 : 1 / Real.sqrt 2 < R0 := by
  have h : 5 + 1 / Real.sqrt 2 < 10 / Real.sqrt 3 := by
    have h1 : (5 + 1 / Real.sqrt 2)^2 < (10 / Real.sqrt 3)^2 := by
      rw [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
      have h2 : 5 * Real.sqrt 2 < 47/6 := by
        have h50 : (5 * Real.sqrt 2)^2 < (47/6)^2 := by
          rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]; norm_num
        have h6 := sq_lt_sq.mp h50
        rwa [abs_of_pos (by positivity), abs_of_pos (by norm_num)] at h6
      have h3 : 1 / Real.sqrt 2 = Real.sqrt 2 / 2 := by
        field_simp
        rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
      rw [h3]
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)]
    have h2 := sq_lt_sq.mp h1
    rwa [abs_of_pos (by positivity), abs_of_pos (by positivity)] at h2
  rw [R0]; linarith

lemma R0_lt_53 : R0 < 5/3 := by
  have h : 10 / Real.sqrt 3 < 5 + 5/3 := by
    have h1 : (10 / Real.sqrt 3)^2 < (5 + 5/3)^2 := by
      rw [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]; norm_num
    have h2 := sq_lt_sq.mp h1
    rwa [abs_of_pos (by positivity), abs_of_pos (by norm_num)] at h2
  rw [R0]; linarith

lemma R0_lt_one : R0 < 1 := by
  have h : 10 / Real.sqrt 3 < 6 := by
    have h1 : (10 / Real.sqrt 3)^2 < (6:ℝ)^2 := by
      rw [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]; norm_num
    have h2 := sq_lt_sq.mp h1
    rwa [abs_of_pos (by positivity), abs_of_pos (by norm_num)] at h2
  rw [R0]; linarith

/-- Two open balls of positive radius with disjoint interiors are at distance at
least the sum of the radii. -/
lemma dist_add_dist_of_disjoint_balls {x y : Pl} {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (h : Disjoint (Metric.ball x r₁) (Metric.ball y r₂)) : r₁ + r₂ ≤ dist x y := by
  by_contra! hlt
  have hxy : x ≠ y := by
    intro he
    subst he
    exact Set.disjoint_left.mp h (Metric.mem_ball_self hr₁) (Metric.mem_ball_self hr₂)
  set d := dist x y with hd
  have hd0 : 0 < d := by rw [hd]; exact dist_pos.mpr hxy
  rcases le_or_gt d (r₁ - r₂) with h1 | h1
  · -- then `y` lies in both balls
    have h2 : dist y x < r₁ := by rw [dist_comm, ← hd]; linarith
    exact Set.disjoint_left.mp h h2 (Metric.mem_ball_self hr₂)
  rcases le_or_gt d (r₂ - r₁) with h2 | h2
  · have h3 : dist x y < r₂ := by rw [← hd]; linarith
    exact Set.disjoint_right.mp h h3 (Metric.mem_ball_self hr₁)
  · -- generic case: pick a point on the segment
    set t := (r₁ - r₂ + d) / (2 * d) with ht
    have hyn : ‖y - x‖ = d := by rw [hd, dist_eq_norm, norm_sub_rev]
    have ht0 : 0 < t := by
      rw [ht]; apply div_pos _ (by positivity); linarith
    have ht1 : t < 1 := by
      rw [ht]; apply (div_lt_one (by positivity)).mpr; linarith
    have hz1 : dist (x + t • (y - x)) x = t * d := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs t,
        abs_of_pos ht0, hyn]
    have hz2 : dist (x + t • (y - x)) y = (1 - t) * d := by
      have h4 : x + t • (y - x) - y = (t - 1) • (y - x) := by
        rw [sub_smul, one_smul, smul_sub]; abel
      rw [dist_eq_norm, h4, norm_smul, Real.norm_eq_abs (t - 1),
        abs_of_neg (by linarith), hyn]
      ring
    have h3 : dist (x + t • (y - x)) x < r₁ := by
      have htd : t * d = (r₁ - r₂ + d) / 2 := by
        rw [ht]; field_simp [hd0.ne']
      rw [hz1, htd]; linarith
    have h4 : dist (x + t • (y - x)) y < r₂ := by
      have h1td : (1 - t) * d = (d - r₁ + r₂) / 2 := by
        have htd : t * d = (r₁ - r₂ + d) / 2 := by
          rw [ht]; field_simp [hd0.ne']
        linarith
      rw [hz2, h1td]; linarith
    exact Set.disjoint_left.mp h h3 h4

/-- The algebraic heart: from `(r₁ + r₂)² ≤ (f₁ + r₁)² + (f₂ + r₂)² + (f₁ + r₁)(f₂ + r₂)`
(the law of cosines for an angle of at most 120°) with `r₁, r₂ ≥ 5` and
`0 ≤ f₁ + f₂` and `0 ≤ max f₁ f₂ < 5/3`, deduce `max f₁ f₂ ≥ R0`. -/
lemma R0_le_of_sq_le {ri rj fi fj : ℝ} (hri : 5 ≤ ri) (hrj : 5 ≤ rj)
    (hsum : 0 ≤ fi + fj) (hfi : 0 ≤ max fi fj) (hfj53 : max fi fj < 5/3)
    (h : (ri + rj)^2 ≤ (fi + ri)^2 + (fj + rj)^2 + (fi + ri) * (fj + rj)) :
    R0 ≤ max fi fj := by
  apply R0_le_of_quadratic hfi
  have h1 : ri * rj ≤ fi^2 + fj^2 + fi * fj + 2 * fi * ri + 2 * fj * rj + fi * rj + fj * ri := by
    nlinarith
  have h2 : ri * rj ≤ 3 * (max fi fj)^2 + 3 * (max fi fj) * (ri + rj) := by
    have hfi_le : fi ≤ max fi fj := le_max_left _ _
    have hfj_le : fj ≤ max fi fj := le_max_right _ _
    have habs_i : |fi| ≤ max fi fj := by
      rw [abs_le]
      constructor <;> nlinarith [hfi_le, hsum]
    have habs_j : |fj| ≤ max fi fj := by
      rw [abs_le]
      constructor <;> nlinarith [hfj_le, hsum]
    have p1 : 2 * fi * ri + fj * ri ≤ 3 * (max fi fj) * ri := by
      have h9 : 2 * fi + fj ≤ 3 * max fi fj := by nlinarith [hfi_le, hfj_le]
      have h10 : 0 ≤ ri := by linarith [hri]
      nlinarith [mul_le_mul_of_nonneg_right h9 h10]
    have p2 : 2 * fj * rj + fi * rj ≤ 3 * (max fi fj) * rj := by
      have h9 : 2 * fj + fi ≤ 3 * max fi fj := by nlinarith [hfi_le, hfj_le]
      have h10 : 0 ≤ rj := by linarith [hrj]
      nlinarith [mul_le_mul_of_nonneg_right h9 h10]
    have p3 : fi^2 + fj^2 + fi * fj ≤ 3 * (max fi fj)^2 := by
      have h11 : fi^2 ≤ (max fi fj)^2 := by
        have e : fi^2 = |fi|^2 := by rw [sq_abs]
        rw [e]
        exact pow_le_pow_left₀ (abs_nonneg _) habs_i 2
      have h12 : fj^2 ≤ (max fi fj)^2 := by
        have e : fj^2 = |fj|^2 := by rw [sq_abs]
        rw [e]
        exact pow_le_pow_left₀ (abs_nonneg _) habs_j 2
      have h13 : fi * fj ≤ (max fi fj)^2 := by
        have h14 : |fi * fj| ≤ max fi fj * max fi fj := by
          rw [abs_mul]
          exact mul_le_mul habs_i habs_j (abs_nonneg fj) ((abs_nonneg fi).trans habs_i)
        calc fi * fj ≤ |fi * fj| := le_abs_self _
        _ ≤ max fi fj * max fi fj := h14
        _ = (max fi fj)^2 := by ring
      nlinarith
    nlinarith
  have h3 : (ri - 3 * max fi fj) * (rj - 3 * max fi fj) ≤ 12 * (max fi fj)^2 := by
    nlinarith
  have h4 : (5 - 3 * max fi fj)^2 ≤ (ri - 3 * max fi fj) * (rj - 3 * max fi fj) := by
    have h5 : 0 ≤ 5 - 3 * max fi fj := by nlinarith [hfj53]
    have h6 : 5 - 3 * max fi fj ≤ ri - 3 * max fi fj := by nlinarith [hri]
    have h7 : 5 - 3 * max fi fj ≤ rj - 3 * max fi fj := by nlinarith [hrj]
    have h8 : 0 ≤ ri - 3 * max fi fj := by nlinarith [hri, hfj53]
    have h9 : 0 ≤ rj - 3 * max fi fj := by nlinarith [hrj, hfj53]
    rw [pow_two]
    exact mul_le_mul h6 h7 h5 h8
  nlinarith

/-- The pair analysis: two distinct disks, both with clearance `< R0` at `z`, whose
centers make an angle of at most 120° at `z` — impossible. -/
lemma not_two_within_R0_of_inner_ge {ι : Type*} {c : ι → Pl} {r : ι → ℝ} (hr : ∀ i, 5 ≤ r i)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Metric.ball (c i) (r i)) (Metric.ball (c j) (r j)))
    (z : Pl) (i j : ι) (hij : i ≠ j)
    (hfi : f c r i z < R0) (hfj : f c r j z < R0)
    (hang : -(1/2) * (‖c i - z‖ * ‖c j - z‖) ≤ ⟪c i - z, c j - z⟫_ℝ) : False := by
  have hd : r i + r j ≤ dist (c i) (c j) :=
    dist_add_dist_of_disjoint_balls (by linarith [hr i]) (by linarith [hr j]) (hdisj i j hij)
  have h1 : dist z (c i) = f c r i z + r i := by rw [f_apply]; ring
  have h2 : dist z (c j) = f c r j z + r j := by rw [f_apply]; ring
  have hsum : 0 ≤ f c r i z + f c r j z := by
    have h3 : dist (c i) (c j) ≤ dist z (c i) + dist z (c j) := by
      have h4 := dist_triangle (c i) z (c j)
      rwa [← dist_comm z (c i)] at h4
    rw [f_apply, f_apply] at *
    linarith [hd]
  have hmax0 : 0 ≤ max (f c r i z) (f c r j z) := by
    have h5 : f c r i z + f c r j z ≤ 2 * max (f c r i z) (f c r j z) := by
      nlinarith [le_max_left (f c r i z) (f c r j z), le_max_right (f c r i z) (f c r j z)]
    linarith
  have hmax53 : max (f c r i z) (f c r j z) < 5/3 :=
    max_lt (lt_trans hfi R0_lt_53) (lt_trans hfj R0_lt_53)
  have hn1 : ‖c i - z‖ = dist z (c i) := by
    rw [dist_comm z (c i)]
    exact (dist_eq_norm (c i) z).symm
  have hn2 : ‖c j - z‖ = dist z (c j) := by
    rw [dist_comm z (c j)]
    exact (dist_eq_norm (c j) z).symm
  have hsq : (r i + r j)^2 ≤ (f c r i z + r i)^2 + (f c r j z + r j)^2 +
      (f c r i z + r i) * (f c r j z + r j) := by
    have e : c i - c j = (c i - z) - (c j - z) := by abel
    have h3 : dist (c i) (c j) = ‖(c i - z) - (c j - z)‖ := by rw [dist_eq_norm, e]
    have h4 : ‖(c i - z) - (c j - z)‖^2 = (f c r i z + r i)^2 + (f c r j z + r j)^2 -
        2 * ⟪c i - z, c j - z⟫_ℝ := by
      rw [norm_sub_sq_real, hn1, hn2, h1, h2]
      ring
    have h5 : -2 * ⟪c i - z, c j - z⟫_ℝ ≤ (f c r i z + r i) * (f c r j z + r j) := by
      rw [hn1, hn2, h1, h2] at hang
      linarith [hang]
    have h6 : (r i + r j)^2 ≤ ‖(c i - z) - (c j - z)‖^2 := by
      have h7 := pow_le_pow_left₀ (by linarith [hr i, hr j]) hd 2
      rwa [h3] at h7
    rw [h4] at h6
    linarith [h6, h5]
  have hR := R0_le_of_sq_le (hr i) (hr j) hsum hmax0 hmax53 hsq
  have hcontra : max (f c r i z) (f c r j z) < R0 := max_lt hfi hfj
  linarith

/-- Auxiliary orthonormal vector for planar inner-product computations. -/
lemma exists_perp_unit (d : Pl) (hd : ‖d‖ = 1) :
    ∃ e : Pl, ‖e‖ = 1 ∧ ⟪d, e⟫_ℝ = 0 ∧
      ∀ v : Pl, v = (⟪d, v⟫_ℝ) • d + (⟪e, v⟫_ℝ) • e := by
  have hn : (d 0)^2 + (d 1)^2 = 1 := by
    have h := EuclideanSpace.norm_eq d
    rw [Fin.sum_univ_two, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs, hd] at h
    have h2 := congrArg (fun t => t^2) h
    simp at h2
    rw [Real.sq_sqrt (by positivity)] at h2
    linarith
  refine ⟨!₂[-(d 1), d 0], ?_, ?_, ?_⟩
  · rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, neg_sq, add_comm, hn, Real.sqrt_one]
  · simp [inner, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  · intro v
    apply PiLp.ext
    intro i
    fin_cases i
    · simp [smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
        PiLp.inner_apply, Fin.sum_univ_two]
      have e0 : (v 0 * d 0 + v 1 * d 1) * d 0 + -((-(v 0 * d 1) + v 1 * d 0) * d 1) =
          v 0 * ((d 0)^2 + (d 1)^2) := by ring
      rw [e0, hn, mul_one]
    · simp [smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
        PiLp.inner_apply, Fin.sum_univ_two]
      have e1 : (v 0 * d 0 + v 1 * d 1) * d 1 + (-(v 0 * d 1) + v 1 * d 0) * d 0 =
          v 1 * ((d 0)^2 + (d 1)^2) := by ring
      rw [e1, hn, mul_one]

/-- Given three unit vectors in the plane, some pair has inner product at least `-1/2`
(i.e. makes an angle of at most 120°). -/
lemma exists_pair_inner_ge_of_three_unit (d₁ d₂ d₃ : Pl)
    (h₁ : ‖d₁‖ = 1) (h₂ : ‖d₂‖ = 1) (h₃ : ‖d₃‖ = 1) :
    -1/2 ≤ ⟪d₁, d₂⟫_ℝ ∨ -1/2 ≤ ⟪d₁, d₃⟫_ℝ ∨ -1/2 ≤ ⟪d₂, d₃⟫_ℝ := by
  by_contra! h
  obtain ⟨e, he_norm, he_perp, he_span⟩ := exists_perp_unit d₁ h₁
  set a₂ := ⟪d₁, d₂⟫_ℝ with ha₂
  set b₂ := ⟪e, d₂⟫_ℝ with hb₂
  set a₃ := ⟪d₁, d₃⟫_ℝ with ha₃
  set b₃ := ⟪e, d₃⟫_ℝ with hb₃
  have hd₂ : d₂ = a₂ • d₁ + b₂ • e := he_span d₂
  have hd₃ : d₃ = a₃ • d₁ + b₃ • e := he_span d₃
  have hsq₂ : a₂^2 + b₂^2 = 1 := by
    have h := h₂
    rw [hd₂] at h
    have h2 : ‖a₂ • d₁ + b₂ • e‖^2 = 1 := by rw [h]; norm_num
    rw [norm_add_sq_real, norm_smul, norm_smul, h₁, he_norm] at h2
    simp only [mul_one, Real.norm_eq_abs, sq_abs] at h2
    have hi : ⟪a₂ • d₁, b₂ • e⟫_ℝ = 0 := by
      rw [inner_smul_left, inner_smul_right, he_perp]; ring
    rw [hi] at h2
    nlinarith
  have hsq₃ : a₃^2 + b₃^2 = 1 := by
    have h := h₃
    rw [hd₃] at h
    have h2 : ‖a₃ • d₁ + b₃ • e‖^2 = 1 := by rw [h]; norm_num
    rw [norm_add_sq_real, norm_smul, norm_smul, h₁, he_norm] at h2
    simp only [mul_one, Real.norm_eq_abs, sq_abs] at h2
    have hi : ⟪a₃ • d₁, b₃ • e⟫_ℝ = 0 := by
      rw [inner_smul_left, inner_smul_right, he_perp]; ring
    rw [hi] at h2
    nlinarith
  have h23 : ⟪d₂, d₃⟫_ℝ = a₂ * a₃ + b₂ * b₃ := by
    rw [hd₂, hd₃]
    have he2 : ⟪e, d₁⟫_ℝ = 0 := inner_eq_zero_symm.mp he_perp
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      he_perp, he2, real_inner_self_eq_norm_sq, h₁, he_norm, starRingEnd_apply, star_trivial]
    ring
  have ha : 1/4 < a₂ * a₃ := by nlinarith [h.1, h.2.1]
  have hb2 : |b₂| < Real.sqrt 3 / 2 := by
    have h4 : b₂^2 < 3/4 := by nlinarith [h.1]
    have h5 : |b₂| = Real.sqrt (b₂^2) := by rw [Real.sqrt_sq_eq_abs]
    rw [h5]
    have h6 : Real.sqrt (b₂^2) < Real.sqrt (3/4) := Real.sqrt_lt_sqrt (by positivity) h4
    have h7 : Real.sqrt (3/4) = Real.sqrt 3 / 2 := by
      rw [Real.sqrt_div (by norm_num : (0:ℝ) ≤ 3)]
      have h8 : Real.sqrt (4:ℝ) = 2 := by
        rw [Real.sqrt_eq_iff_eq_sq (by norm_num : (0:ℝ) ≤ 4) (by norm_num : (0:ℝ) ≤ 2)]
        norm_num
      rw [h8]
    rw [h7] at h6
    exact h6
  have hb3 : |b₃| < Real.sqrt 3 / 2 := by
    have h4 : b₃^2 < 3/4 := by nlinarith [h.2.1]
    have h5 : |b₃| = Real.sqrt (b₃^2) := by rw [Real.sqrt_sq_eq_abs]
    rw [h5]
    have h6 : Real.sqrt (b₃^2) < Real.sqrt (3/4) := Real.sqrt_lt_sqrt (by positivity) h4
    have h7 : Real.sqrt (3/4) = Real.sqrt 3 / 2 := by
      rw [Real.sqrt_div (by norm_num : (0:ℝ) ≤ 3)]
      have h8 : Real.sqrt (4:ℝ) = 2 := by
        rw [Real.sqrt_eq_iff_eq_sq (by norm_num : (0:ℝ) ≤ 4) (by norm_num : (0:ℝ) ≤ 2)]
        norm_num
      rw [h8]
    rw [h7] at h6
    exact h6
  have hb : -3/4 < b₂ * b₃ := by
    have h8 : |b₂ * b₃| < (Real.sqrt 3 / 2) * (Real.sqrt 3 / 2) := by
      rw [abs_mul]
      rcases eq_or_ne |b₃| 0 with hzero | hpos
      · rw [hzero]; simp
      · have hpos' : 0 < |b₃| := lt_of_le_of_ne' (abs_nonneg _) hpos
        calc |b₂| * |b₃| < (Real.sqrt 3 / 2) * |b₃| :=
            mul_lt_mul_of_pos_right hb2 hpos'
        _ < (Real.sqrt 3 / 2) * (Real.sqrt 3 / 2) :=
            mul_lt_mul_of_pos_left hb3 (by positivity)
    have h9 : (Real.sqrt 3 / 2) * (Real.sqrt 3 / 2) = 3/4 := by
      rw [div_mul_div_comm, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 3)]; norm_num
    rw [h9] at h8
    have h11 := (abs_lt.mp h8).1
    linarith
  have h10 : -1/2 < ⟪d₂, d₃⟫_ℝ := by rw [h23]; nlinarith [ha, hb]
  linarith [h10, h.2.2]

/-- The three-rays lemma: at any point, at most two disks have clearance `< R0`. -/
lemma not_three_within_R0 {ι : Type*} {c : ι → Pl} {r : ι → ℝ} (hr : ∀ i, 5 ≤ r i)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Metric.ball (c i) (r i)) (Metric.ball (c j) (r j)))
    (z : Pl) (i₁ i₂ i₃ : ι) (h12 : i₁ ≠ i₂) (h13 : i₁ ≠ i₃) (h23 : i₂ ≠ i₃)
    (hf1 : f c r i₁ z < R0) (hf2 : f c r i₂ z < R0) (hf3 : f c r i₃ z < R0) : False := by
  -- If `z` is a center, the other two disks must be far (disjointness) — contradiction.
  by_cases hz1 : z = c i₁
  · subst hz1
    have h2 : dist (c i₁) (c i₂) = f c r i₂ (c i₁) + r i₂ := by rw [f_apply]; ring
    have hd : r i₁ + r i₂ ≤ dist (c i₁) (c i₂) :=
      dist_add_dist_of_disjoint_balls (by linarith [hr i₁]) (by linarith [hr i₂]) (hdisj i₁ i₂ h12)
    have : 5 ≤ f c r i₂ (c i₁) := by rw [h2] at hd; linarith [hr i₁]
    have h4 : f c r i₂ (c i₁) < 1 := lt_trans hf2 R0_lt_one
    linarith
  by_cases hz2 : z = c i₂
  · subst hz2
    have h2 : dist (c i₂) (c i₁) = f c r i₁ (c i₂) + r i₁ := by rw [f_apply]; ring
    have hd : r i₂ + r i₁ ≤ dist (c i₂) (c i₁) :=
      dist_add_dist_of_disjoint_balls (by linarith [hr i₂]) (by linarith [hr i₁]) (hdisj i₂ i₁ h12.symm)
    have : 5 ≤ f c r i₁ (c i₂) := by rw [h2] at hd; linarith [hr i₂]
    have h4 : f c r i₁ (c i₂) < 1 := lt_trans hf1 R0_lt_one
    linarith
  by_cases hz3 : z = c i₃
  · subst hz3
    have h2 : dist (c i₃) (c i₁) = f c r i₁ (c i₃) + r i₁ := by rw [f_apply]; ring
    have hd : r i₃ + r i₁ ≤ dist (c i₃) (c i₁) :=
      dist_add_dist_of_disjoint_balls (by linarith [hr i₃]) (by linarith [hr i₁]) (hdisj i₃ i₁ h13.symm)
    have : 5 ≤ f c r i₁ (c i₃) := by rw [h2] at hd; linarith [hr i₃]
    have h4 : f c r i₁ (c i₃) < 1 := lt_trans hf1 R0_lt_one
    linarith
  -- Generic case: take the three directions and find a pair with angle ≤ 120°.
  have hn1 : ‖c i₁ - z‖ ≠ 0 := by
    rw [Ne, norm_eq_zero]; intro h; exact hz1 (eq_of_sub_eq_zero h).symm
  have hn2 : ‖c i₂ - z‖ ≠ 0 := by
    rw [Ne, norm_eq_zero]; intro h; exact hz2 (eq_of_sub_eq_zero h).symm
  have hn3 : ‖c i₃ - z‖ ≠ 0 := by
    rw [Ne, norm_eq_zero]; intro h; exact hz3 (eq_of_sub_eq_zero h).symm
  set d₁ := (‖c i₁ - z‖⁻¹) • (c i₁ - z) with hd₁
  set d₂ := (‖c i₂ - z‖⁻¹) • (c i₂ - z) with hd₂
  set d₃ := (‖c i₃ - z‖⁻¹) • (c i₃ - z) with hd₃
  have hn₁ : ‖d₁‖ = 1 := by rw [hd₁, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _), inv_mul_cancel₀ hn1]
  have hn₂ : ‖d₂‖ = 1 := by rw [hd₂, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _), inv_mul_cancel₀ hn2]
  have hn₃ : ‖d₃‖ = 1 := by rw [hd₃, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _), inv_mul_cancel₀ hn3]
  obtain hp | hp | hp := exists_pair_inner_ge_of_three_unit d₁ d₂ d₃ hn₁ hn₂ hn₃
  · -- pair (1, 2) has angle ≤ 120°
    have hang : -(1/2) * (‖c i₁ - z‖ * ‖c i₂ - z‖) ≤ ⟪c i₁ - z, c i₂ - z⟫_ℝ := by
      have hinner : ⟪d₁, d₂⟫_ℝ = (‖c i₁ - z‖⁻¹ * ‖c i₂ - z‖⁻¹) * ⟪c i₁ - z, c i₂ - z⟫_ℝ := by
        rw [hd₁, hd₂, inner_smul_left, inner_smul_right, starRingEnd_apply, star_trivial]; ring
      have h5 : ⟪c i₁ - z, c i₂ - z⟫_ℝ = (‖c i₁ - z‖ * ‖c i₂ - z‖) * ⟪d₁, d₂⟫_ℝ := by
        rw [hinner]; field_simp [hn1, hn2]
      rw [h5]
      have h6 : 0 ≤ ‖c i₁ - z‖ * ‖c i₂ - z‖ := by positivity
      nlinarith [hp, h6]
    exact not_two_within_R0_of_inner_ge hr hdisj z i₁ i₂ h12 hf1 hf2 hang
  · have hang : -(1/2) * (‖c i₁ - z‖ * ‖c i₃ - z‖) ≤ ⟪c i₁ - z, c i₃ - z⟫_ℝ := by
      have hinner : ⟪d₁, d₃⟫_ℝ = (‖c i₁ - z‖⁻¹ * ‖c i₃ - z‖⁻¹) * ⟪c i₁ - z, c i₃ - z⟫_ℝ := by
        rw [hd₁, hd₃, inner_smul_left, inner_smul_right, starRingEnd_apply, star_trivial]; ring
      have h5 : ⟪c i₁ - z, c i₃ - z⟫_ℝ = (‖c i₁ - z‖ * ‖c i₃ - z‖) * ⟪d₁, d₃⟫_ℝ := by
        rw [hinner]; field_simp [hn1, hn3]
      rw [h5]
      have h6 : 0 ≤ ‖c i₁ - z‖ * ‖c i₃ - z‖ := by positivity
      nlinarith [hp, h6]
    exact not_two_within_R0_of_inner_ge hr hdisj z i₁ i₃ h13 hf1 hf3 hang
  · have hang : -(1/2) * (‖c i₂ - z‖ * ‖c i₃ - z‖) ≤ ⟪c i₂ - z, c i₃ - z⟫_ℝ := by
      have hinner : ⟪d₂, d₃⟫_ℝ = (‖c i₂ - z‖⁻¹ * ‖c i₃ - z‖⁻¹) * ⟪c i₂ - z, c i₃ - z⟫_ℝ := by
        rw [hd₂, hd₃, inner_smul_left, inner_smul_right, starRingEnd_apply, star_trivial]; ring
      have h5 : ⟪c i₂ - z, c i₃ - z⟫_ℝ = (‖c i₂ - z‖ * ‖c i₃ - z‖) * ⟪d₂, d₃⟫_ℝ := by
        rw [hinner]; field_simp [hn2, hn3]
      rw [h5]
      have h6 : 0 ≤ ‖c i₂ - z‖ * ‖c i₃ - z‖ := by positivity
      nlinarith [hp, h6]
    exact not_two_within_R0_of_inner_ge hr hdisj z i₂ i₃ h23 hf2 hf3 hang

/-- Any set containing no three distinct elements is finite. -/
lemma finite_of_forall_not_three {α : Type*} {P : α → Prop}
    (h : ∀ a b c : α, P a → P b → P c → a ≠ b → a ≠ c → b ≠ c → False) :
    {x | P x}.Finite := by
  classical
  by_contra hinf
  have hs : {x | P x}.Infinite := Set.not_finite.mp hinf
  obtain ⟨a₁, ha₁⟩ := hs.nonempty
  obtain ⟨a₂, ha₂⟩ := (hs.sdiff (Set.finite_singleton a₁)).nonempty
  obtain ⟨a₃, ha₃⟩ := (hs.sdiff ((Set.finite_singleton a₁).union (Set.finite_singleton a₂))).nonempty
  have hne12 : a₁ ≠ a₂ := by
    intro he
    rw [he] at ha₂
    simp at ha₂
  have hne13 : a₁ ≠ a₃ := by
    intro he
    rw [he] at ha₃
    simp at ha₃
  have hne23 : a₂ ≠ a₃ := by
    intro he
    rw [he] at ha₃
    simp at ha₃
  exact h a₁ a₂ a₃ ha₁ ha₂.1 ha₃.1 hne12 hne13 hne23

/-- The disks with clearance `< R` at `z` are finitely many (in fact, at most two
by the three-rays lemma). -/
lemma finite_within {ι : Type*} {c : ι → Pl} {r : ι → ℝ} (hr : ∀ i, 5 ≤ r i)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Metric.ball (c i) (r i)) (Metric.ball (c j) (r j)))
    (R : ℝ) (hRlt : R < R0) (z : Pl) :
    {i | f c r i z < R}.Finite := by
  apply finite_of_forall_not_three
  intro i₁ i₂ i₃ h1 h2 h3 h12 h13 h23
  exact not_three_within_R0 hr hdisj z i₁ i₂ i₃ h12 h13 h23
    (lt_trans h1 hRlt) (lt_trans h2 hRlt) (lt_trans h3 hRlt)

/-- The disks with clearance `< R0` at `z` are finitely many. -/
lemma finite_within_R0 {ι : Type*} {c : ι → Pl} {r : ι → ℝ} (hr : ∀ i, 5 ≤ r i)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Metric.ball (c i) (r i)) (Metric.ball (c j) (r j)))
    (z : Pl) :
    {i | f c r i z < R0}.Finite := by
  apply finite_of_forall_not_three
  intro i₁ i₂ i₃ h1 h2 h3 h12 h13 h23
  exact not_three_within_R0 hr hdisj z i₁ i₂ i₃ h12 h13 h23 h1 h2 h3

/-- The finite set of disks with clearance `< R` at `z`. -/
noncomputable def withinSet {ι : Type*} {c : ι → Pl} {r : ι → ℝ} (hr : ∀ i, 5 ≤ r i)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Metric.ball (c i) (r i)) (Metric.ball (c j) (r j)))
    (R : ℝ) (hRlt : R < R0) (z : Pl) : Finset ι :=
  (finite_within hr hdisj R hRlt z).toFinset

lemma mem_withinSet {ι : Type*} {c : ι → Pl} {r : ι → ℝ} (hr : ∀ i, 5 ≤ r i)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Metric.ball (c i) (r i)) (Metric.ball (c j) (r j)))
    (R : ℝ) (hRlt : R < R0) (z : Pl) (i : ι) :
    i ∈ withinSet hr hdisj R hRlt z ↔ f c r i z < R :=
  (finite_within hr hdisj R hRlt z).mem_toFinset

/-- The potential: sum over the within-R disks of `(R - f i z) * (f i z + r i)`.
This is nonnegative and strictly decreases at each climb step. -/
noncomputable def Phi {ι : Type*} {c : ι → Pl} {r : ι → ℝ} (hr : ∀ i, 5 ≤ r i)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Metric.ball (c i) (r i)) (Metric.ball (c j) (r j)))
    (R : ℝ) (hRlt : R < R0) (z : Pl) : ℝ :=
  ∑ i ∈ withinSet hr hdisj R hRlt z, (R - f c r i z) * (f c r i z + r i)

lemma Phi_nonneg {ι : Type*} {c : ι → Pl} {r : ι → ℝ} (hr : ∀ i, 5 ≤ r i)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Metric.ball (c i) (r i)) (Metric.ball (c j) (r j)))
    (R : ℝ) (hRlt : R < R0) (z : Pl) :
    0 ≤ Phi hr hdisj R hRlt z := by
  apply Finset.sum_nonneg
  intro i hi
  rw [mem_withinSet] at hi
  have h1 : 0 < R - f c r i z := by linarith [hi]
  have h2 : 0 ≤ f c r i z + r i := by rw [f_apply]; linarith [dist_nonneg (x := z) (y := c i)]
  exact mul_nonneg (le_of_lt h1) h2

/-- Moving directly away from a disk's center increases its clearance by exactly
the step size. -/
lemma f_move_away {ι : Type*} (c : ι → Pl) (r : ι → ℝ) (i : ι) (z : Pl) (s : ℝ) (hs : 0 ≤ s)
    (hz : z ≠ c i) :
    f c r i (z + s • ((‖z - c i‖⁻¹) • (z - c i))) = f c r i z + s := by
  have hn : ‖z - c i‖ ≠ 0 := by
    rw [Ne, norm_eq_zero]; intro h; exact hz (eq_of_sub_eq_zero h)
  have h3 : ‖(‖z - c i‖⁻¹) • (z - c i)‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _), inv_mul_cancel₀ hn]
  have h2 : dist (z + s • ((‖z - c i‖⁻¹) • (z - c i))) (c i) = ‖z - c i‖ + s := by
    have e : z + s • ((‖z - c i‖⁻¹) • (z - c i)) - c i = (‖z - c i‖ + s) • ((‖z - c i‖⁻¹) • (z - c i)) := by
      have e1 : (‖z - c i‖ + s) • ((‖z - c i‖⁻¹) • (z - c i)) =
          (z - c i) + s • ((‖z - c i‖⁻¹) • (z - c i)) := by
        rw [add_smul, smul_smul, mul_inv_cancel₀ hn, one_smul]
      rw [e1]; abel
    rw [dist_eq_norm, e, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), h3, mul_one]
  rw [f_apply, f_apply, h2, dist_eq_norm]
  ring

/-- If only one disk has clearance `< R0` at `z`, moving directly away from it raises
the clearance above `R`. -/
lemma first_order_single {ι : Type*} [Nonempty ι] {c : ι → Pl} {r : ι → ℝ} (hr : ∀ i, 5 ≤ r i)
    (_hdisj : ∀ i j, i ≠ j → Disjoint (Metric.ball (c i) (r i)) (Metric.ball (c j) (r j)))
    (R : ℝ) (hR : ∀ x, g c r x ≤ R) (hRlt : R < R0)
    (z : Pl) (a : ι) (hga : g c r z = f c r a z)
    (hothers : ∀ i, i ≠ a → R0 ≤ f c r i z)
    (hpos : (3 * R - R0) / 2 < g c r z) :
    ∃ z', R < g c r z' := by
  by_cases hz : z = c a
  · -- the center case: move in a fixed direction by a large step
    subst hz
    set s := (r a + R0) / 2 with hs
    have hs0 : 0 < s := by rw [hs]; nlinarith [hr a, R0_pos]
    use c a + s • !₂[(1:ℝ), (0:ℝ)]
    have hnorm : ‖!₂[(1:ℝ), (0:ℝ)]‖ = 1 := by
      rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
      simp
    have hdist : dist (c a + s • !₂[(1:ℝ), (0:ℝ)]) (c a) = s := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, hnorm, mul_one,
        abs_of_pos hs0]
    have hfa : f c r a (c a + s • !₂[(1:ℝ), (0:ℝ)]) = s - r a := by
      rw [f_apply, hdist]
    have h5 : R < (R0 - r a) / 2 := by
      have h6 : f c r a (c a) = - r a := by rw [f_apply, dist_self, zero_sub]
      rw [hga, h6] at hpos
      nlinarith [R0_pos, hr a]
    have hfa2 : (R0 - r a) / 2 ≤ f c r a (c a + s • !₂[(1:ℝ), (0:ℝ)]) := by
      rw [hfa]; nlinarith [hs]
    have hothers2 : ∀ i, i ≠ a → (R0 - r a) / 2 ≤ f c r i (c a + s • !₂[(1:ℝ), (0:ℝ)]) := by
      intro i hi
      have h3 := f_sub_le c r i (c a) (c a + s • !₂[(1:ℝ), (0:ℝ)])
      rw [dist_comm, hdist] at h3
      have h4 := hothers i hi
      have h5' : (R0 - r a) / 2 = R0 - s := by rw [hs]; ring
      linarith [h3, h4, h5']
    have h7 : (R0 - r a) / 2 ≤ g c r (c a + s • !₂[(1:ℝ), (0:ℝ)]) := by
      apply le_ciInf
      intro i
      by_cases hi : i = a
      · subst hi; linarith [hfa2]
      · exact hothers2 i hi
    linarith [h5, h7]
  · -- the generic case: move directly away from the single near disk
    set s := (R0 + R) / 2 - g c r z with hs
    have hs0 : 0 < s := by
      rw [hs]; have h1 := hR z; nlinarith [R0_pos, hRlt]
    use z + s • ((‖z - c a‖⁻¹) • (z - c a))
    have hfa : f c r a (z + s • ((‖z - c a‖⁻¹) • (z - c a))) = f c r a z + s :=
      f_move_away c r a z s (le_of_lt hs0) hz
    have hdist : dist z (z + s • ((‖z - c a‖⁻¹) • (z - c a))) = s := by
      have e : z - (z + s • ((‖z - c a‖⁻¹) • (z - c a))) = - (s • ((‖z - c a‖⁻¹) • (z - c a))) := by abel
      rw [dist_eq_norm, e, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hs0]
      have h5 : ‖(‖z - c a‖⁻¹) • (z - c a)‖ = 1 := by
        rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _), inv_mul_cancel₀]
        · rw [Ne, norm_eq_zero]; intro h6; exact hz (eq_of_sub_eq_zero h6)
      rw [h5, mul_one]
    have h1 : f c r a z + s = (R0 + R) / 2 := by rw [← hga, hs]; ring
    have h2 : ∀ i, i ≠ a → R0 - s ≤ f c r i (z + s • ((‖z - c a‖⁻¹) • (z - c a))) := by
      intro i hi
      have h3 := f_sub_le c r i z (z + s • ((‖z - c a‖⁻¹) • (z - c a)))
      rw [hdist] at h3
      have h7 := hothers i hi
      linarith [h3, h7]
    have h10 : (R0 + R) / 2 > R := by nlinarith [hRlt]
    have h9 : R < R0 - s := by
      have h8 : R0 - s = (R0 - R) / 2 + g c r z := by rw [hs]; ring
      rw [h8]; nlinarith [hpos]
    have h11 : min ((R0 + R) / 2) (R0 - s) ≤ g c r (z + s • ((‖z - c a‖⁻¹) • (z - c a))) := by
      apply le_ciInf
      intro i
      by_cases hi : i = a
      · subst hi
        rw [hfa, ← h1]
        apply min_le_left
      · exact le_trans (min_le_right _ _) (h2 i hi)
    have h12 : R < min ((R0 + R) / 2) (R0 - s) := by
      rw [lt_min_iff]
      exact ⟨h10, h9⟩
    linarith [h11, h12]

/-- Algebraic identity for the rise of the clearance after a perpendicular move:
`√(A² + t²) - A = t² / (√(A² + t²) + A)`. -/
lemma sqrt_sq_add_sq_sub_self (A t : ℝ) (hA : 0 ≤ A) :
    Real.sqrt (A^2 + t^2) - A = t^2 / (Real.sqrt (A^2 + t^2) + A) := by
  by_cases h : A = 0 ∧ t = 0
  · rw [h.1, h.2]; simp
  · have h2 : 0 < Real.sqrt (A^2 + t^2) + A := by
      have h3 : 0 ≤ Real.sqrt (A^2 + t^2) := Real.sqrt_nonneg _
      by_contra! h4
      have h5 : Real.sqrt (A^2 + t^2) = 0 := by linarith
      have h6 : A^2 + t^2 ≤ 0 := (Real.sqrt_eq_zero' (x := A^2 + t^2)).mp h5
      have h7 : A = 0 := by nlinarith [sq_nonneg t, hA, h6]
      have h8 : t = 0 := by nlinarith [sq_nonneg A, h7]
      exact h ⟨h7, h8⟩
    have h1 : (Real.sqrt (A^2 + t^2) - A) * (Real.sqrt (A^2 + t^2) + A) = t^2 := by
      have h9 : (Real.sqrt (A^2 + t^2))^2 = A^2 + t^2 := Real.sq_sqrt (by positivity)
      nlinarith
    field_simp [h2.ne']
    nlinarith [h1]

/-- A lower bound for the rise: `t² / (√(A² + t²) + A) ≥ t² / (2A + t²/(2A))`. -/
lemma rise_lb (A t : ℝ) (hA : 0 < A) :
    t^2 / (2 * A + t^2 / (2 * A)) ≤ t^2 / (Real.sqrt (A^2 + t^2) + A) := by
  have h1 : Real.sqrt (A^2 + t^2) ≤ A + t^2 / (2 * A) := by
    have h2 : A^2 + t^2 ≤ (A + t^2 / (2 * A))^2 := by
      rw [add_pow_two]
      have h3 : A * (t^2 / (2 * A)) = t^2 / 2 := by field_simp
      nlinarith [h3, sq_nonneg (t^2 / (2 * A))]
    have h4 : 0 ≤ A + t^2 / (2 * A) := by positivity
    have h5 := (Real.sqrt_le_iff (x := A^2 + t^2) (y := A + t^2 / (2 * A))).mpr ⟨h4, h2⟩
    exact h5
  have h6 : 0 < 2 * A + t^2 / (2 * A) := by positivity
  have h7 : Real.sqrt (A^2 + t^2) + A ≤ 2 * A + t^2 / (2 * A) := by linarith
  have h8 : 0 < Real.sqrt (A^2 + t^2) + A := by positivity
  exact div_le_div_of_nonneg_left (sq_nonneg t) h8 h7

/-- The step used in the climb: a unit vector `v` perpendicular to `z - c a` with
`⟪c b - z, v⟫ ≤ 0`, together with the exact distance computations. -/
lemma climb_step {ι : Type*} {c : ι → Pl}
    (z : Pl) (a b : ι) (t : ℝ) (ht : 0 < t) (hza : z ≠ c a) :
    ∃ v : Pl, ‖v‖ = 1 ∧ ⟪z - c a, v⟫_ℝ = 0 ∧ ⟪c b - z, v⟫_ℝ ≤ 0 ∧
      dist (z + t • v) (c a) = Real.sqrt ((dist z (c a))^2 + t^2) ∧
      Real.sqrt ((dist z (c b))^2 + t^2) ≤ dist (z + t • v) (c b) ∧
      dist z (z + t • v) = t := by
  have hn : ‖z - c a‖ ≠ 0 := by
    rw [Ne, norm_eq_zero]; intro h; exact hza (eq_of_sub_eq_zero h)
  obtain ⟨e, he_norm, he_perp, _⟩ := exists_perp_unit ((‖z - c a‖⁻¹) • (z - c a)) (by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _), inv_mul_cancel₀ hn])
  have heq : z - c a = (‖z - c a‖) • ((‖z - c a‖⁻¹) • (z - c a)) := by
    rw [smul_smul, mul_inv_cancel₀ hn, one_smul]
  have he0 : ⟪z - c a, e⟫_ℝ = 0 := by
    rw [heq, inner_smul_left, he_perp, mul_zero]
  set v := if ⟪c b - z, e⟫_ℝ ≤ 0 then e else -e with hv_def
  have hv_norm : ‖v‖ = 1 := by
    rw [hv_def]; split_ifs with h
    · exact he_norm
    · rw [norm_neg]; exact he_norm
  have hv_perp : ⟪z - c a, v⟫_ℝ = 0 := by
    rw [hv_def]; split_ifs with h
    · exact he0
    · rw [inner_neg_right, he0]; simp
  have hv_sign : ⟪c b - z, v⟫_ℝ ≤ 0 := by
    rw [hv_def]; split_ifs with h
    · exact h
    · rw [inner_neg_right]; linarith
  refine ⟨v, hv_norm, hv_perp, hv_sign, ?_, ?_, ?_⟩
  · -- exact distance to `c a`
    have h1 : (z + t • v) - c a = (z - c a) + t • v := by abel
    have h2 : ‖(z - c a) + t • v‖ ^ 2 = (dist z (c a))^2 + t^2 := by
      rw [norm_add_sq_real, inner_smul_right, hv_perp, norm_smul, hv_norm,
        Real.norm_eq_abs, abs_of_pos ht, dist_eq_norm]
      ring
    have h3 : ‖(z - c a) + t • v‖ = Real.sqrt ((dist z (c a))^2 + t^2) := by
      rw [← h2]
      exact ((Real.sqrt_sq_eq_abs _).trans (abs_of_nonneg (norm_nonneg _))).symm
    rw [dist_eq_norm, h1, h3]
  · -- lower bound for the distance to `c b`
    have h1 : (z + t • v) - c b = (z - c b) + t • v := by abel
    have h2 : (dist z (c b))^2 + t^2 ≤ ‖(z - c b) + t • v‖ ^ 2 := by
      rw [norm_add_sq_real, inner_smul_right, norm_smul, hv_norm,
        Real.norm_eq_abs, abs_of_pos ht, dist_eq_norm]
      have h4 : 0 ≤ ⟪z - c b, v⟫_ℝ := by
        have h5 : z - c b = - (c b - z) := by abel
        rw [h5, inner_neg_left]
        linarith [hv_sign]
      nlinarith
    have h3 : Real.sqrt ((dist z (c b))^2 + t^2) ≤ dist (z + t • v) (c b) := by
      rw [dist_eq_norm, dist_eq_norm, h1]
      have h4 : Real.sqrt ((dist z (c b))^2 + t^2) ≤ Real.sqrt (‖(z - c b) + t • v‖ ^ 2) :=
        Real.sqrt_le_sqrt h2
      rwa [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)] at h4
    exact h3
  · -- the step length
    have h1 : z - (z + t • v) = - (t • v) := by abel
    rw [dist_eq_norm, h1, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos ht, hv_norm, mul_one]

/-- The algebraic heart of the potential drop: from `2 * t^2 * A * B / (4 * A^2 + t^2) ≥ t^2 / 4`
whenever `8 * A * B ≥ 4 * A^2 + t^2`. -/
lemma drop_of_8AB (A B t : ℝ) (hA : 0 < A) (h : 8 * A * B ≥ 4 * A^2 + t^2) (_ht : 0 ≤ t) :
    t^2 / 4 ≤ 2 * t^2 * A * B / (4 * A^2 + t^2) := by
  have h1 : 0 < 4 * A^2 + t^2 := by nlinarith [hA, sq_nonneg t]
  have h2 : 0 ≤ 2 * t^2 * A * B / (4 * A^2 + t^2) - t^2 / 4 := by
    have h3 : (2 * t^2 * A * B / (4 * A^2 + t^2)) - t^2 / 4 =
        (8 * t^2 * A * B - t^2 * (4 * A^2 + t^2)) / (4 * (4 * A^2 + t^2)) := by
      field_simp
      ring
    rw [h3]
    apply div_nonneg
    · nlinarith [h, sq_nonneg t]
    · positivity
  linarith

/-- There is a point with nonnegative clearance: the open disks cannot cover the
whole plane (they are pairwise disjoint and the plane is connected). -/
lemma exists_g_nonneg {ι : Type*} [Nonempty ι] {c : ι → Pl} {r : ι → ℝ} (hr : ∀ i, 5 ≤ r i)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Metric.ball (c i) (r i)) (Metric.ball (c j) (r j))) :
    ∃ x, 0 ≤ g c r x := by
  by_contra! h
  have hne : Nonempty ι := inferInstance
  obtain ⟨i₀⟩ := hne
  have hcov : ∀ x : Pl, ∃ i, x ∈ Metric.ball (c i) (r i) := by
    intro x
    have h1 := h x
    by_contra! h3
    have h4 : 0 ≤ g c r x := by
      apply le_ciInf
      intro i
      by_contra! h5
      have h6 : x ∈ Metric.ball (c i) (r i) := by
        rw [Metric.mem_ball]
        rw [f_apply] at h5
        exact sub_neg.mp h5
      exact h3 i h6
    linarith [h1, h4]
  have hclosed : IsClosed (Metric.ball (c i₀) (r i₀)) := by
    have hcomp : (Metric.ball (c i₀) (r i₀))ᶜ = ⋃ j ∈ {j | j ≠ i₀}, Metric.ball (c j) (r j) := by
      ext x
      simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_setOf_eq]
      constructor
      · intro hx
        obtain ⟨j, hj⟩ := hcov x
        by_cases h6 : j = i₀
        · subst h6
          exact (hx hj).elim
        · exact ⟨j, h6, hj⟩
      · rintro ⟨j, hj1, hj2⟩
        intro hx
        have hdis := hdisj j i₀ hj1
        exact Set.disjoint_left.mp hdis hj2 hx
    rw [← isOpen_compl_iff, hcomp]
    exact isOpen_iUnion fun j => isOpen_iUnion fun _ => Metric.isOpen_ball
  have huniv : Metric.ball (c i₀) (r i₀) = ∅ ∨ Metric.ball (c i₀) (r i₀) = Set.univ :=
    (isClopen_iff (s := Metric.ball (c i₀) (r i₀))).mp ⟨hclosed, Metric.isOpen_ball⟩
  rcases huniv with huniv | huniv
  · have h9 : (Metric.ball (c i₀) (r i₀)).Nonempty := ⟨c i₀, Metric.mem_ball_self (by linarith [hr i₀])⟩
    rw [huniv] at h9
    exact Set.not_nonempty_empty h9
  · have hout : c i₀ + (r i₀ + 1) • !₂[(1:ℝ), (0:ℝ)] ∉ Metric.ball (c i₀) (r i₀) := by
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
      have hnorm : ‖!₂[(1:ℝ), (0:ℝ)]‖ = 1 := by
        rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
        simp
      rw [hnorm, mul_one]
      have h5 : |r i₀ + 1| = r i₀ + 1 := abs_of_pos (by nlinarith [hr i₀])
      rw [h5]
      nlinarith [hr i₀]
    have hin : c i₀ + (r i₀ + 1) • !₂[(1:ℝ), (0:ℝ)] ∈ (Set.univ : Set Pl) := Set.mem_univ _
    rw [← huniv] at hin
    exact hout hin

/-- Center case of the deficit-zero step: the point `z` is the center of the
attaining disk `a`, while disk `b` is also within `R0`. A step of size
`t = (R0 - R)/2` perpendicular to `z - c b` strictly exceeds `R`. -/
lemma deficit_zero_kill_center {ι : Type*} [Nonempty ι] {c : ι → Pl} {r : ι → ℝ}
    (hr : ∀ i, 5 ≤ r i)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Metric.ball (c i) (r i)) (Metric.ball (c j) (r j)))
    (R : ℝ) (hR0 : 0 ≤ R) (hRlt : R < R0)
    (z : Pl) (hgz : g c r z = R) (a b : ι) (hb_ne : b ≠ a)
    (hfaz : f c r a z = R) (hfb : f c r b z < R0) (hzc : z = c a) :
    ∃ z', R < g c r z' := by
  have hfa_lt : f c r a z < R0 := by rw [hfaz]; exact hRlt
  set t := (R0 - R) / 2 with ht_def
  have ht0 : 0 < t := by rw [ht_def]; nlinarith [R0_pos, hRlt]
  have hca_ne : c a ≠ c b := by
    intro h
    have h1 := dist_add_dist_of_disjoint_balls (by linarith [hr a]) (by linarith [hr b])
      (hdisj a b hb_ne.symm)
    rw [h, dist_self] at h1
    linarith [hr a, hr b]
  obtain ⟨v, hv_norm, _hv_perp, _hv_sign, hdist_b, _hdist_a, hdist_z⟩ :=
    climb_step z b a t ht0 (by intro h; exact hca_ne (hzc.symm.trans h))
  use z + t • v
  have hfa : f c r a (z + t • v) > R := by
    rw [f_apply, hzc, dist_eq_norm, add_sub_cancel_left, norm_smul, hv_norm, mul_one,
      Real.norm_eq_abs, abs_of_pos ht0]
    have hca : f c r a (c a) = - r a := by rw [f_apply, dist_self, zero_sub]
    rw [hzc] at hfaz
    rw [hca] at hfaz
    nlinarith [ht0, hr a]
  have hfb' : f c r b (z + t • v) > R := by
    rw [f_apply]
    have h1 : dist z (c b) = f c r b z + r b := by rw [f_apply]; ring
    have h2 : f c r b z ≥ R := by
      have h3 := g_le_f (c := c) (r := r) hr hdisj z b
      rwa [hgz] at h3
    have h4 : (f c r b z + r b)^2 < (f c r b z + r b)^2 + t^2 := by
      nlinarith [sq_pos_of_pos ht0]
    have h5 : (f c r b z + r b) < Real.sqrt ((f c r b z + r b)^2 + t^2) := by
      have h6 := Real.sqrt_lt_sqrt (by positivity) h4
      rwa [Real.sqrt_sq_eq_abs,
        abs_of_nonneg (show 0 ≤ f c r b z + r b by nlinarith [hr b, h2, hR0])] at h6
    have h6 : dist (z + t • v) (c b) = Real.sqrt ((dist z (c b))^2 + t^2) := hdist_b
    rw [h6, h1]
    nlinarith [h2, h5]
  have hothers : ∀ i, i ≠ a → i ≠ b → R0 - t ≤ f c r i (z + t • v) := by
    intro i hi1 hi2
    have h3 := f_sub_le c r i z (z + t • v)
    rw [hdist_z] at h3
    have h4 : R0 ≤ f c r i z := by
      by_contra! h5
      exact not_three_within_R0 hr hdisj z a b i hb_ne.symm hi1.symm hi2.symm hfa_lt hfb h5
    linarith [h3, h4]
  have h8 : R < R0 - t := by rw [ht_def]; nlinarith [R0_pos, hRlt]
  have h10 : R < min (f c r a (z + t • v)) (min (f c r b (z + t • v)) (R0 - t)) := by
    rw [lt_min_iff, lt_min_iff]
    exact ⟨hfa, hfb', h8⟩
  have h11 : min (f c r a (z + t • v)) (min (f c r b (z + t • v)) (R0 - t)) ≤
      g c r (z + t • v) := by
    apply le_ciInf
    intro i
    by_cases hi1 : i = a
    · subst hi1; exact min_le_left _ _
    · by_cases hi2 : i = b
      · subst hi2; exact le_trans (min_le_right _ _) (min_le_left _ _)
      · exact (min_le_right _ _).trans ((min_le_right _ _).trans (hothers i hi1 hi2))
  exact lt_of_lt_of_le h10 h11

/-- Generic case of the deficit-zero step: `z` is not the center of the
attaining disk `a`, and disk `b` is also within `R0`. A step of size
`t = (R0 - R)/2` perpendicular to `z - c a`, away from `c b`, strictly
exceeds `R`. -/
lemma deficit_zero_kill_generic {ι : Type*} [Nonempty ι] {c : ι → Pl} {r : ι → ℝ}
    (hr : ∀ i, 5 ≤ r i)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Metric.ball (c i) (r i)) (Metric.ball (c j) (r j)))
    (R : ℝ) (hR0 : 0 ≤ R) (hRlt : R < R0)
    (z : Pl) (hgz : g c r z = R) (a b : ι) (hb_ne : b ≠ a)
    (hfaz : f c r a z = R) (hfb : f c r b z < R0) (hzc : z ≠ c a) :
    ∃ z', R < g c r z' := by
  have hfa_lt : f c r a z < R0 := by rw [hfaz]; exact hRlt
  set t := (R0 - R) / 2 with ht_def
  have ht0 : 0 < t := by rw [ht_def]; nlinarith [R0_pos, hRlt]
  obtain ⟨v, _hv_norm, _hv_perp, _hv_sign, hdist_a, hdist_b, hdist_z⟩ :=
    climb_step z a b t ht0 hzc
  use z + t • v
  have hfa : f c r a (z + t • v) > R := by
    rw [f_apply, hdist_a]
    have h1 : dist z (c a) = f c r a z + r a := by rw [f_apply]; ring
    rw [h1, hfaz]
    have h2 : R + r a < Real.sqrt ((R + r a)^2 + t^2) := by
      have h3 : (R + r a)^2 < (R + r a)^2 + t^2 := by nlinarith [sq_pos_of_pos ht0]
      have h4 : 0 ≤ R + r a := by nlinarith [hr a, hR0]
      have h5 := Real.sqrt_lt_sqrt (by positivity) h3
      rwa [Real.sqrt_sq_eq_abs, abs_of_nonneg h4] at h5
    linarith
  have hfb' : f c r b (z + t • v) > R := by
    have h1 : dist z (c b) = f c r b z + r b := by rw [f_apply]; ring
    have h2 : f c r b z ≥ R := by
      have h3 := g_le_f (c := c) (r := r) hr hdisj z b
      rwa [hgz] at h3
    rw [f_apply]
    have h4 : Real.sqrt ((R + r b)^2 + t^2) ≤ Real.sqrt ((dist z (c b))^2 + t^2) := by
      have h5 : (R + r b)^2 + t^2 ≤ (dist z (c b))^2 + t^2 := by
        rw [h1]
        have h6 : (R + r b)^2 ≤ (f c r b z + r b)^2 :=
          pow_le_pow_left₀ (by nlinarith [hr b, h2, hR0]) (by nlinarith [h2, hr b]) 2
        nlinarith [h6, sq_nonneg t]
      exact Real.sqrt_le_sqrt h5
    have h6 : Real.sqrt ((dist z (c b))^2 + t^2) ≤ dist (z + t • v) (c b) := hdist_b
    have h7 : R + r b < Real.sqrt ((R + r b)^2 + t^2) := by
      have h8 : (R + r b)^2 < (R + r b)^2 + t^2 := by nlinarith [sq_pos_of_pos ht0]
      have h9 : 0 ≤ R + r b := by nlinarith [hr b, hR0]
      have h10 := Real.sqrt_lt_sqrt (by positivity) h8
      rwa [Real.sqrt_sq_eq_abs, abs_of_nonneg h9] at h10
    linarith [h6, h4, h7]
  have hothers : ∀ i, i ≠ a → i ≠ b → R0 - t ≤ f c r i (z + t • v) := by
    intro i hi1 hi2
    have h3 := f_sub_le c r i z (z + t • v)
    rw [hdist_z] at h3
    have h4 : R0 ≤ f c r i z := by
      by_contra! h5
      exact not_three_within_R0 hr hdisj z a b i hb_ne.symm hi1.symm hi2.symm hfa_lt hfb h5
    linarith [h3, h4]
  have h8 : R < R0 - t := by rw [ht_def]; nlinarith [R0_pos, hRlt]
  have h10 : R < min (f c r a (z + t • v)) (min (f c r b (z + t • v)) (R0 - t)) := by
    rw [lt_min_iff, lt_min_iff]
    exact ⟨hfa, hfb', h8⟩
  have h11 : min (f c r a (z + t • v)) (min (f c r b (z + t • v)) (R0 - t)) ≤
      g c r (z + t • v) := by
    apply le_ciInf
    intro i
    by_cases hi1 : i = a
    · subst hi1; exact min_le_left _ _
    · by_cases hi2 : i = b
      · subst hi2; exact le_trans (min_le_right _ _) (min_le_left _ _)
      · exact (min_le_right _ _).trans ((min_le_right _ _).trans (hothers i hi1 hi2))
  exact lt_of_lt_of_le h10 h11

/-- At a point where the clearance equals `R` (the supremum), one can strictly
exceed it. This is the "deficit zero" step of the climb. -/
lemma deficit_zero_kill {ι : Type*} [Nonempty ι] {c : ι → Pl} {r : ι → ℝ} (hr : ∀ i, 5 ≤ r i)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Metric.ball (c i) (r i)) (Metric.ball (c j) (r j)))
    (R : ℝ) (hR : ∀ x, g c r x ≤ R) (hRlt : R < R0)
    (z : Pl) (hgz : g c r z = R) :
    ∃ z', R < g c r z' := by
  have hR0 : 0 ≤ R := by
    obtain ⟨x0, hx0⟩ := exists_g_nonneg hr hdisj
    linarith [hx0, hR x0]
  obtain ⟨a, hga, _hamina⟩ := g_eq_f_min (c := c) (r := r) hr hdisj z
  have hfaz : f c r a z = R := by rw [← hga, hgz]
  by_cases hb : ∃ b, b ≠ a ∧ f c r b z < R0
  · -- two disks within `R0`: pair analysis or a step
    obtain ⟨b, hb_ne, hfb⟩ := hb
    have hfa_lt : f c r a z < R0 := by rw [hfaz]; exact hRlt
    by_cases hang : ⟪c a - z, c b - z⟫_ℝ < -(1/2) * (‖c a - z‖ * ‖c b - z‖)
    · -- angle > 120°: a step perpendicular to one radius
      by_cases hzc : z = c a
      · exact deficit_zero_kill_center hr hdisj R hR0 hRlt z hgz a b hb_ne hfaz hfb hzc
      · exact deficit_zero_kill_generic hr hdisj R hR0 hRlt z hgz a b hb_ne hfaz hfb hzc
    · -- angle ≤ 120°: pair algebra gives a contradiction
      push Not at hang
      exact False.elim (not_two_within_R0_of_inner_ge hr hdisj z a b hb_ne.symm hfa_lt hfb hang)
  · -- only `a` within `R0`: first-order move
    push Not at hb
    exact first_order_single hr hdisj R hR hRlt z a hga (fun i hi => hb i hi) (by
      rw [hgz]; nlinarith [hRlt, R0_pos])


/-- The analytic heart of the potential drop: after a perpendicular step of size `t`,
the decrease `(D' - D) * (D' + fval - R)` of the weighted deficit of a disk whose
center is at distance `D ≥ 4` from the basepoint (moving to distance
`D' ≥ √(D² + t²)`, with clearance `fval > R - t/2`) is at least `t²/4`. -/
lemma quarter_drop (D D' fval R t : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1) (hD : 4 ≤ D)
    (hD' : Real.sqrt (D^2 + t^2) ≤ D') (hf : R - t / 2 ≤ fval) :
    t^2 / 4 ≤ (D' - D) * (D' + fval - R) := by
  have hD0 : 0 < D := by linarith
  have hρ : Real.sqrt (D^2 + t^2) - D = t^2 / (Real.sqrt (D^2 + t^2) + D) :=
    sqrt_sq_add_sq_sub_self D t (le_of_lt hD0)
  have hρ2 := rise_lb D t hD0
  have h1 : t^2 / (2 * D + t^2 / (2 * D)) = 2 * D * t^2 / (4 * D^2 + t^2) := by
    have hn1 : (2:ℝ) * D ≠ 0 := ne_of_gt (by linarith [hD0])
    have hn2 : 4 * D^2 + t^2 ≠ 0 := ne_of_gt (by nlinarith [sq_pos_of_pos hD0, sq_nonneg t])
    field_simp
    ring
  rw [h1] at hρ2
  have hsqrt_ge : D ≤ Real.sqrt (D^2 + t^2) := by
    have h5 := Real.sqrt_le_sqrt (show D^2 ≤ D^2 + t^2 by nlinarith [sq_nonneg t])
    rwa [Real.sqrt_sq_eq_abs, abs_of_nonneg (le_of_lt hD0)] at h5
  have h2 : Real.sqrt (D^2 + t^2) - D ≤ D' - D := by linarith [hD']
  have h3 : D - t / 2 ≤ D' + fval - R := by linarith [hD', hsqrt_ge, hf]
  have h4 : 0 ≤ Real.sqrt (D^2 + t^2) - D := by linarith [hsqrt_ge]
  have h5 : 0 < D - t / 2 := by linarith
  have h6 : (Real.sqrt (D^2 + t^2) - D) * (D - t / 2) ≤ (D' - D) * (D' + fval - R) :=
    mul_le_mul h2 h3 (le_of_lt h5) (by linarith [h2, h4])
  have hden : 0 < Real.sqrt (D^2 + t^2) + D := by
    linarith [Real.sqrt_nonneg (D^2 + t^2), hD0]
  have h7 : (2 * D * t^2 / (4 * D^2 + t^2)) * (D - t / 2) ≤
      (Real.sqrt (D^2 + t^2) - D) * (D - t / 2) := by
    rw [hρ]
    exact mul_le_mul hρ2 (le_refl _) (le_of_lt h5)
      (le_of_lt (div_pos (sq_pos_of_pos ht0) hden))
  have h8 : t^2 / 4 ≤ (2 * D * t^2 / (4 * D^2 + t^2)) * (D - t / 2) := by
    have h9 : 0 < 4 * D^2 + t^2 := by nlinarith [sq_pos_of_pos hD0, sq_nonneg t]
    have h10 : (2 * D * t^2 / (4 * D^2 + t^2)) * (D - t / 2) =
        (2 * D * t^2 * (D - t / 2)) / (4 * D^2 + t^2) := by rw [div_mul_eq_mul_div]
    rw [h10, div_le_div_iff₀ (by norm_num : (0:ℝ) < 4) h9]
    have e1 : D * t ≤ D := by
      have h11 := mul_le_mul_of_nonneg_left ht1 (le_of_lt hD0)
      rwa [mul_one] at h11
    have e2 : t^2 ≤ 1 := by nlinarith [ht0, ht1]
    have e3 : 4 * D + 1 ≤ 4 * D^2 := by nlinarith [hD, hD0]
    nlinarith [e1, e2, e3, sq_pos_of_pos ht0, hD0]
  exact h8.trans (h7.trans h6)

/-- Unfolding lemma for the potential. -/
lemma Phi_eq_sum {ι : Type*} {c : ι → Pl} {r : ι → ℝ} (hr : ∀ i, 5 ≤ r i)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Metric.ball (c i) (r i)) (Metric.ball (c j) (r j)))
    (R : ℝ) (hRlt : R < R0) (z : Pl) :
    Phi hr hdisj R hRlt z =
      ∑ i ∈ withinSet hr hdisj R hRlt z, (R - f c r i z) * (f c r i z + r i) := rfl

/-- One step of the climb. Starting from a point `z` where the minimum clearance
`g z < R` is attained by disk `a`, with a second disk `b` within `R0`, the
perpendicular step of size `t = R0 - R` to `z' = z + t • v` either reaches
`R ≤ g z'` or strictly decreases the potential `Phi` by at least `(R0 - R)²/4`
while keeping `g z'` above the threshold `(3R - R0)/2`. -/
lemma phi_drop {ι : Type*} [Nonempty ι] {c : ι → Pl} {r : ι → ℝ} (hr : ∀ i, 5 ≤ r i)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Metric.ball (c i) (r i)) (Metric.ball (c j) (r j)))
    (R : ℝ) (hR0 : 0 ≤ R) (hRlt : R < R0)
    (z : Pl) (a b : ι) (hb_ne : b ≠ a)
    (hga : g c r z = f c r a z) (hamina : ∀ j, f c r a z ≤ f c r j z)
    (hfb : f c r b z < R0) (hglt : g c r z < R) (hpos : (3 * R - R0) / 2 < g c r z) :
    ∃ z', R ≤ g c r z' ∨
      ((3 * R - R0) / 2 < g c r z' ∧
        Phi hr hdisj R hRlt z' ≤ Phi hr hdisj R hRlt z - (R0 - R)^2 / 4) := by
  classical
  set t := R0 - R with ht_def
  have ht0 : 0 < t := by rw [ht_def]; linarith [hRlt]
  have ht1 : t < 1 := by rw [ht_def]; nlinarith [hR0, R0_lt_one, hRlt]
  have hRt : R0 - t = R := by rw [ht_def]; ring
  have hfa_lt_R : f c r a z < R := by rw [← hga]; exact hglt
  have hfa_pos : R - t / 2 < f c r a z := by
    have e : R - t / 2 = (3 * R - R0) / 2 := by rw [ht_def]; ring
    rw [e, ← hga]; exact hpos
  have hfa_lt_R0 : f c r a z < R0 := lt_trans hfa_lt_R hRlt
  have hza : z ≠ c a := by
    intro h
    rw [h] at hfa_pos
    have h1 : f c r a (c a) = - r a := by rw [f_apply, dist_self, zero_sub]
    rw [h1] at hfa_pos
    nlinarith [hr a, hR0, ht0, ht1]
  obtain ⟨v, _hv_norm, _hv_perp, _hv_sign, hdist_a, hdist_b, hdist_z⟩ :=
    climb_step z a b t ht0 hza
  use z + t • v
  have hDa : dist z (c a) = f c r a z + r a := by rw [f_apply]; ring
  have hDb : dist z (c b) = f c r b z + r b := by rw [f_apply]; ring
  have hD4a : 4 ≤ dist z (c a) := by rw [hDa]; nlinarith [hr a, hfa_pos, ht1, hR0]
  have hD4b : 4 ≤ dist z (c b) := by
    rw [hDb]
    have h1 := hamina b
    nlinarith [hr b, hfa_pos, ht1, hR0, h1]
  have hfb_pos : R - t / 2 < f c r b z := lt_of_lt_of_le hfa_pos (hamina b)
  have hfa' : f c r a (z + t • v) = Real.sqrt ((dist z (c a))^2 + t^2) - r a := by
    rw [f_apply, hdist_a]
  have hfb' : Real.sqrt ((dist z (c b))^2 + t^2) - r b ≤ f c r b (z + t • v) := by
    rw [f_apply]; linarith [hdist_b]
  have hsqrt_lt_a : dist z (c a) < Real.sqrt ((dist z (c a))^2 + t^2) := by
    have h2 : (dist z (c a))^2 < (dist z (c a))^2 + t^2 := by nlinarith [sq_pos_of_pos ht0]
    have h3 := Real.sqrt_lt_sqrt (by positivity) h2
    rwa [Real.sqrt_sq_eq_abs, abs_of_nonneg (by linarith [hD4a])] at h3
  have hsqrt_lt_b : dist z (c b) < Real.sqrt ((dist z (c b))^2 + t^2) := by
    have h2 : (dist z (c b))^2 < (dist z (c b))^2 + t^2 := by nlinarith [sq_pos_of_pos ht0]
    have h3 := Real.sqrt_lt_sqrt (by positivity) h2
    rwa [Real.sqrt_sq_eq_abs, abs_of_nonneg (by linarith [hD4b])] at h3
  -- the other disks stay at clearance `≥ R`
  have hothers : ∀ i, i ≠ a → i ≠ b → R ≤ f c r i (z + t • v) := by
    intro i hi1 hi2
    have h3 := f_sub_le c r i z (z + t • v)
    rw [hdist_z] at h3
    have h4 : R0 ≤ f c r i z := by
      by_contra! h5
      exact not_three_within_R0 hr hdisj z a b i hb_ne.symm hi1.symm hi2.symm hfa_lt_R0 hfb h5
    linarith [h3, h4, hRt]
  -- `g` at the new point stays above the threshold
  have hpos' : (3 * R - R0) / 2 < g c r (z + t • v) := by
    have e4 : (3 * R - R0) / 2 < f c r a (z + t • v) := by
      rw [hfa']
      have h1 : f c r a z = dist z (c a) - r a := by rw [f_apply]
      linarith [hpos, hga, hsqrt_lt_a, h1]
    have e5 : (3 * R - R0) / 2 < f c r b (z + t • v) := by
      have h1 : f c r b z = dist z (c b) - r b := by rw [f_apply]
      have h2 := hamina b
      linarith [hpos, hga, h2, hfb', hsqrt_lt_b, h1]
    have e3 : (3 * R - R0) / 2 < R := by nlinarith [hRlt]
    have e6 : min (f c r a (z + t • v)) (min (f c r b (z + t • v)) R) ≤
        g c r (z + t • v) := by
      apply le_ciInf
      intro i
      by_cases hi1 : i = a
      · subst hi1; exact min_le_left _ _
      · by_cases hi2 : i = b
        · subst hi2; exact le_trans (min_le_right _ _) (min_le_left _ _)
        · exact (min_le_right _ _).trans ((min_le_right _ _).trans (hothers i hi1 hi2))
    have e7 : (3 * R - R0) / 2 < min (f c r a (z + t • v)) (min (f c r b (z + t • v)) R) := by
      rw [lt_min_iff, lt_min_iff]
      exact ⟨e4, e5, e3⟩
    linarith [e6, e7]
  by_cases hRle : R ≤ g c r (z + t • v)
  · exact Or.inl hRle
  · -- the potential strictly decreases by at least `t²/4`
    refine Or.inr ⟨hpos', ?_⟩
    push Not at hRle
    have hsub : withinSet hr hdisj R hRlt (z + t • v) ⊆ {a, b} := by
      intro i hi
      rw [mem_withinSet] at hi
      by_cases hi1 : i = a
      · subst hi1; exact Finset.mem_insert_self _ _
      · by_cases hi2 : i = b
        · subst hi2; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
        · exfalso
          have h1 := hothers i hi1 hi2
          linarith
    have hPhi' : Phi hr hdisj R hRlt (z + t • v) ≤
        max ((R - f c r a (z + t • v)) * dist (z + t • v) (c a)) 0 +
        max ((R - f c r b (z + t • v)) * dist (z + t • v) (c b)) 0 := by
      rw [Phi_eq_sum]
      have h1a : ∑ i ∈ withinSet hr hdisj R hRlt (z + t • v),
            (R - f c r i (z + t • v)) * (f c r i (z + t • v) + r i) ≤
          ∑ i ∈ withinSet hr hdisj R hRlt (z + t • v),
            max ((R - f c r i (z + t • v)) * (f c r i (z + t • v) + r i)) 0 := by
        apply Finset.sum_le_sum
        intro i _
        exact le_max_left _ _
      have h1b : ∑ i ∈ withinSet hr hdisj R hRlt (z + t • v),
            max ((R - f c r i (z + t • v)) * (f c r i (z + t • v) + r i)) 0 ≤
          ∑ i ∈ {a, b}, max ((R - f c r i (z + t • v)) * (f c r i (z + t • v) + r i)) 0 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro i _ _
        exact le_max_right _ _
      have h2 : ∑ i ∈ {a, b}, max ((R - f c r i (z + t • v)) * (f c r i (z + t • v) + r i)) 0 =
          max ((R - f c r a (z + t • v)) * dist (z + t • v) (c a)) 0 +
          max ((R - f c r b (z + t • v)) * dist (z + t • v) (c b)) 0 := by
        rw [Finset.sum_insert (by rw [Finset.mem_singleton]; exact hb_ne.symm),
          Finset.sum_singleton]
        have e1 : f c r a (z + t • v) + r a = dist (z + t • v) (c a) := by rw [f_apply]; ring
        have e2 : f c r b (z + t • v) + r b = dist (z + t • v) (c b) := by rw [f_apply]; ring
        rw [e1, e2]
      exact (h1a.trans h1b).trans h2.le
    have ha_mem : a ∈ withinSet hr hdisj R hRlt z := by
      rw [mem_withinSet]; exact hfa_lt_R
    have hterm_nonneg : ∀ i ∈ withinSet hr hdisj R hRlt z,
        0 ≤ (R - f c r i z) * (f c r i z + r i) := by
      intro i hi
      rw [mem_withinSet] at hi
      exact mul_nonneg (by linarith [hi])
        (by rw [f_apply]; linarith [dist_nonneg (x := z) (y := c i)])
    have hPhi_ge : (R - f c r a z) * dist z (c a) + max ((R - f c r b z) * dist z (c b)) 0 ≤
        Phi hr hdisj R hRlt z := by
      by_cases hbb : f c r b z < R
      · have hb_memW : b ∈ withinSet hr hdisj R hRlt z := by rw [mem_withinSet]; exact hbb
        have hsubW : ({a, b} : Finset ι) ⊆ withinSet hr hdisj R hRlt z := by
          intro i hi
          rw [Finset.mem_insert, Finset.mem_singleton] at hi
          rcases hi with rfl | rfl
          · exact ha_mem
          · exact hb_memW
        have h1 : ∑ i ∈ ({a, b} : Finset ι), (R - f c r i z) * (f c r i z + r i) ≤
            Phi hr hdisj R hRlt z := by
          rw [Phi_eq_sum]
          apply Finset.sum_le_sum_of_subset_of_nonneg hsubW
          intro i hi _
          exact hterm_nonneg i hi
        have h2 : ∑ i ∈ ({a, b} : Finset ι), (R - f c r i z) * (f c r i z + r i) =
            (R - f c r a z) * dist z (c a) + (R - f c r b z) * dist z (c b) := by
          rw [Finset.sum_insert (by rw [Finset.mem_singleton]; exact hb_ne.symm),
            Finset.sum_singleton, hDa, hDb]
        have hTb : max ((R - f c r b z) * dist z (c b)) 0 = (R - f c r b z) * dist z (c b) :=
          max_eq_left (mul_nonneg (by linarith [hbb]) dist_nonneg)
        linarith [h1, h2, hTb]
      · push Not at hbb
        have hTb : max ((R - f c r b z) * dist z (c b)) 0 = 0 :=
          max_eq_right (mul_nonpos_of_nonpos_of_nonneg (by linarith [hbb]) dist_nonneg)
        have hsubW : ({a} : Finset ι) ⊆ withinSet hr hdisj R hRlt z := by
          intro i hi
          rw [Finset.mem_singleton] at hi
          rw [hi]
          exact ha_mem
        have h1 : ∑ i ∈ ({a} : Finset ι), (R - f c r i z) * (f c r i z + r i) ≤
            Phi hr hdisj R hRlt z := by
          rw [Phi_eq_sum]
          apply Finset.sum_le_sum_of_subset_of_nonneg hsubW
          intro i hi _
          exact hterm_nonneg i hi
        have h2 : ∑ i ∈ ({a} : Finset ι), (R - f c r i z) * (f c r i z + r i) =
            (R - f c r a z) * dist z (c a) := by
          rw [Finset.sum_singleton, hDa]
        linarith [h1, h2, hTb]
    -- the weighted-deficit identities for the two disks
    have hpsi_a : (R - f c r a z) * dist z (c a) -
        (R - f c r a (z + t • v)) * dist (z + t • v) (c a) =
        (dist (z + t • v) (c a) - dist z (c a)) * (dist (z + t • v) (c a) + f c r a z - R) := by
      have e1 : f c r a (z + t • v) = dist (z + t • v) (c a) - r a := by rw [f_apply]
      have e2 : f c r a z = dist z (c a) - r a := by rw [f_apply]
      rw [e1, e2]
      ring
    have hpsi_b : (R - f c r b z) * dist z (c b) -
        (R - f c r b (z + t • v)) * dist (z + t • v) (c b) =
        (dist (z + t • v) (c b) - dist z (c b)) * (dist (z + t • v) (c b) + f c r b z - R) := by
      have e1 : f c r b (z + t • v) = dist (z + t • v) (c b) - r b := by rw [f_apply]
      have e2 : f c r b z = dist z (c b) - r b := by rw [f_apply]
      rw [e1, e2]
      ring
    by_cases ha' : f c r a (z + t • v) < R
    · -- disk `a` is still within `R` at `z'` and accounts for the drop
      have hqa := quarter_drop (dist z (c a)) (dist (z + t • v) (c a)) (f c r a z) R t
        ht0 (le_of_lt ht1) hD4a (le_of_eq hdist_a.symm) (le_of_lt hfa_pos)
      have hTa' : max ((R - f c r a (z + t • v)) * dist (z + t • v) (c a)) 0 =
          (R - f c r a (z + t • v)) * dist (z + t • v) (c a) :=
        max_eq_left (mul_nonneg (by linarith [ha']) dist_nonneg)
      have hmono : max ((R - f c r b (z + t • v)) * dist (z + t • v) (c b)) 0 ≤
          max ((R - f c r b z) * dist z (c b)) 0 := by
        have hstep : (R - f c r b (z + t • v)) * dist (z + t • v) (c b) ≤
            (R - f c r b z) * dist z (c b) := by
          have hqb := quarter_drop (dist z (c b)) (dist (z + t • v) (c b)) (f c r b z) R t
            ht0 (le_of_lt ht1) hD4b hdist_b (le_of_lt hfb_pos)
          linarith [hpsi_b, hqb, sq_nonneg t]
        exact max_le_max hstep (le_refl 0)
      linarith [hPhi', hPhi_ge, hTa', hmono, hpsi_a, hqa]
    · -- disk `a` escaped; then disk `b` is within `R` at `z'` and accounts for the drop
      push Not at ha'
      have hb'_lt : f c r b (z + t • v) < R := by
        obtain ⟨i₀, hg0, -⟩ := g_eq_f_min (c := c) (r := r) hr hdisj (z + t • v)
        have hmem : i₀ ∈ withinSet hr hdisj R hRlt (z + t • v) := by
          rw [mem_withinSet, ← hg0]; exact hRle
        have h2 := hsub hmem
        rw [Finset.mem_insert, Finset.mem_singleton] at h2
        rcases h2 with rfl | rfl
        · exfalso; linarith [hg0, hRle, ha']
        · rw [← hg0]; exact hRle
      have hfb_lt : f c r b z < R := by
        have h1 : f c r b z = dist z (c b) - r b := by rw [f_apply]
        linarith [hfb', hsqrt_lt_b, h1, hb'_lt]
      have hqb := quarter_drop (dist z (c b)) (dist (z + t • v) (c b)) (f c r b z) R t
        ht0 (le_of_lt ht1) hD4b hdist_b (le_of_lt hfb_pos)
      have hTa : 0 ≤ (R - f c r a z) * dist z (c a) :=
        mul_nonneg (by linarith [hfa_lt_R]) dist_nonneg
      have hTa'max : max ((R - f c r a (z + t • v)) * dist (z + t • v) (c a)) 0 = 0 :=
        max_eq_right (mul_nonpos_of_nonpos_of_nonneg (by linarith [ha']) dist_nonneg)
      have hTb'max : max ((R - f c r b (z + t • v)) * dist (z + t • v) (c b)) 0 =
          (R - f c r b (z + t • v)) * dist (z + t • v) (c b) :=
        max_eq_left (mul_nonneg (by linarith [hb'_lt]) dist_nonneg)
      have hTb : max ((R - f c r b z) * dist z (c b)) 0 = (R - f c r b z) * dist z (c b) :=
        max_eq_left (mul_nonneg (by linarith [hfb_lt]) dist_nonneg)
      linarith [hPhi', hPhi_ge, hTa'max, hTb'max, hTb, hpsi_b, hqb, hTa]

/-- The climb iteration: starting from any point whose clearance exceeds the
threshold `(3R - R0)/2` and whose potential is at most `K * ((R0 - R)²/4)`, one
reaches a point with clearance strictly above `R`. -/
lemma climb_aux {ι : Type*} [Nonempty ι] {c : ι → Pl} {r : ι → ℝ} (hr : ∀ i, 5 ≤ r i)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Metric.ball (c i) (r i)) (Metric.ball (c j) (r j)))
    (R : ℝ) (hR : ∀ x, g c r x ≤ R) (hRlt : R < R0) :
    ∀ (K : ℕ) (z : Pl), (3 * R - R0) / 2 < g c r z →
      Phi hr hdisj R hRlt z ≤ K * ((R0 - R)^2 / 4) → ∃ z', R < g c r z' := by
  classical
  have hR0 : 0 ≤ R := by
    obtain ⟨x0, hx0⟩ := exists_g_nonneg hr hdisj
    linarith [hx0, hR x0]
  intro K
  induction K with
  | zero =>
    intro z hpos hPhi
    rw [Nat.cast_zero, zero_mul] at hPhi
    have hPhi0 : Phi hr hdisj R hRlt z = 0 := le_antisymm hPhi (Phi_nonneg hr hdisj R hRlt z)
    have hgz : g c r z = R := by
      by_contra hne
      have hlt : g c r z < R := lt_of_le_of_ne (hR z) hne
      obtain ⟨a, hga, -⟩ := g_eq_f_min (c := c) (r := r) hr hdisj z
      have ha_mem : a ∈ withinSet hr hdisj R hRlt z := by
        rw [mem_withinSet, ← hga]; exact hlt
      have hterm_nonneg : ∀ i ∈ withinSet hr hdisj R hRlt z,
          0 ≤ (R - f c r i z) * (f c r i z + r i) := by
        intro i hi
        rw [mem_withinSet] at hi
        exact mul_nonneg (by linarith [hi])
          (by rw [f_apply]; linarith [dist_nonneg (x := z) (y := c i)])
      have h3 : 0 < (R - f c r a z) * (f c r a z + r a) := by
        have hfa : f c r a z < R := by rw [← hga]; exact hlt
        have h4 : 0 < f c r a z + r a := by
          rw [hga] at hpos
          nlinarith [hpos, hr a, hR0, R0_lt_one]
        exact mul_pos (by linarith [hfa]) h4
      have hsp : 0 < ∑ i ∈ withinSet hr hdisj R hRlt z, (R - f c r i z) * (f c r i z + r i) :=
        Finset.sum_pos' hterm_nonneg ⟨a, ha_mem, h3⟩
      rw [Phi_eq_sum] at hPhi0
      linarith [hsp, hPhi0]
    exact deficit_zero_kill hr hdisj R hR hRlt z hgz
  | succ K ih =>
    intro z hpos hPhi
    by_cases hgz : g c r z = R
    · exact deficit_zero_kill hr hdisj R hR hRlt z hgz
    · have hglt : g c r z < R := lt_of_le_of_ne (hR z) hgz
      obtain ⟨a, hga, hamina⟩ := g_eq_f_min (c := c) (r := r) hr hdisj z
      by_cases hb : ∃ b, b ≠ a ∧ f c r b z < R0
      · obtain ⟨b, hb_ne, hfb⟩ := hb
        obtain ⟨z', hz' | ⟨hpos', hdrop⟩⟩ :=
          phi_drop hr hdisj R hR0 hRlt z a b hb_ne hga hamina hfb hglt hpos
        · rcases lt_or_eq_of_le hz' with h | h
          · exact ⟨z', h⟩
          · exact deficit_zero_kill hr hdisj R hR hRlt z' h.symm
        · have hPhi' : Phi hr hdisj R hRlt z' ≤ (K : ℝ) * ((R0 - R)^2 / 4) := by
            have h1 : ((K : ℝ) + 1) * ((R0 - R)^2 / 4) =
                (K : ℝ) * ((R0 - R)^2 / 4) + (R0 - R)^2 / 4 := by ring
            rw [Nat.cast_succ, h1] at hPhi
            linarith [hPhi, hdrop]
          exact ih z' hpos' hPhi'
      · push Not at hb
        exact first_order_single hr hdisj R hR hRlt z a hga (fun i hi => hb i hi) hpos

snip end

/-- **USAMO 2007 Problem 2.** A square grid on the Euclidean plane consists of all
points `(m, n)` with `m` and `n` integers. It is impossible to cover all grid points
by a family of discs with non-overlapping interiors if each disc has radius at
least 5: such a family cannot exist. -/
problem usa2007_p2 (ι : Type*) (c : ι → EuclideanSpace ℝ (Fin 2)) (r : ι → ℝ)
    (hr : ∀ i, 5 ≤ r i)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Metric.ball (c i) (r i)) (Metric.ball (c j) (r j)))
    (hcov : ∀ m n : ℤ, ∃ i, (!₂[(m : ℝ), (n : ℝ)] : EuclideanSpace ℝ (Fin 2)) ∈
      Metric.closedBall (c i) (r i)) : False := by
  by_cases hι : Nonempty ι
  · haveI := hι
    -- the clearance function is bounded above by `1 / √2`, since every lattice
    -- point is covered
    have hcov' : ∀ x : Pl, g c r x ≤ 1 / Real.sqrt 2 := by
      intro x
      obtain ⟨m, n, hmn⟩ := exists_lat_dist_le x
      obtain ⟨i, hi⟩ := hcov m n
      change lat m n ∈ Metric.closedBall (c i) (r i) at hi
      rw [Metric.mem_closedBall] at hi
      have h1 : f c r i x ≤ 1 / Real.sqrt 2 := by
        have h2 : dist x (c i) ≤ dist x (lat m n) + dist (lat m n) (c i) := dist_triangle _ _ _
        rw [dist_comm x (lat m n)] at h2
        rw [f_apply]
        linarith [hmn, hi, h2]
      exact (g_le_f (c := c) (r := r) hr hdisj x i).trans h1
    set R := sSup (Set.range (g c r)) with hR_def
    have hR_le : R ≤ 1 / Real.sqrt 2 := by
      rw [hR_def]
      apply csSup_le (Set.range_nonempty _)
      intro y hy
      obtain ⟨x, rfl⟩ := hy
      exact hcov' x
    have hRlt : R < R0 := lt_of_le_of_lt hR_le R0_gt_inv_sqrt2
    have hbdd : BddAbove (Set.range (g c r)) := ⟨1 / Real.sqrt 2, fun y hy => by
      obtain ⟨x, rfl⟩ := hy
      exact hcov' x⟩
    have hR : ∀ x, g c r x ≤ R := by
      intro x
      exact le_csSup hbdd ⟨x, rfl⟩
    have hR0 : 0 ≤ R := by
      obtain ⟨x0, hx0⟩ := exists_g_nonneg hr hdisj
      linarith [hx0, hR x0]
    -- a starting point for the climb, whose clearance is above the threshold
    have hthr : (3 * R - R0) / 2 < R := by nlinarith [hRlt]
    obtain ⟨y0, ⟨z0, rfl⟩, hgt⟩ :=
      exists_lt_of_lt_csSup (Set.range_nonempty _) (hR_def ▸ hthr)
    -- a bound on the potential at the starting point
    obtain ⟨K, hK⟩ := exists_nat_ge (Phi hr hdisj R hRlt z0 / ((R0 - R)^2 / 4))
    have hc3 : 0 < (R0 - R)^2 / 4 := by
      have e : 0 < R0 - R := by linarith [hRlt]
      exact div_pos (sq_pos_of_pos e) (by norm_num)
    have hK2 : Phi hr hdisj R hRlt z0 ≤ K * ((R0 - R)^2 / 4) :=
      (div_le_iff₀ hc3).mp hK
    obtain ⟨z', hz'⟩ := climb_aux hr hdisj R hR hRlt K z0 hgt hK2
    linarith [hR z', hz']
  · obtain ⟨i, -⟩ := hcov 0 0
    exact hι ⟨i⟩


end Usa2007P2
