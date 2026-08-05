/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import ProblemExtraction

@[expose] public section

problem_file {
  tags := [.Combinatorics]
}

/-!
# International Mathematical Olympiad 2017, Problem 3

A hunter and an invisible rabbit play a game in the Euclidean plane.
The rabbit's starting point, A₀, and the hunter's starting point, B₀,
are the same. After n − 1 rounds of the game, the rabbit is at point
A_{n−1} and the hunter is at point B_{n−1}. In the n-th round of the game,
three things occur in order:

(i) The rabbit moves invisibly to a point Aₙ such that the distance
    between A_{n−1} and Aₙ is exactly 1.
(ii) A tracking device reports a point Pₙ to the hunter. The only
    guarantee provided by the tracking device to the hunter is that the
    distance between Pₙ and Aₙ is at most 1.
(iii) The hunter moves visibly to a point Bₙ such that the distance
    between B_{n−1} and Bₙ is exactly 1.

Is it always possible, no matter how the rabbit moves, and no matter what
points are reported by the tracking device, for the hunter to choose her
moves so that after 10⁹ rounds she can ensure that the distance between
her and the rabbit is at most 100?

The answer is **no**: we show that for every valid hunter strategy there
is a rabbit path and a sequence of reported points such that after `10⁹`
rounds the distance between the hunter and the rabbit exceeds `100`.
The construction formalized here follows Evan Chen's notes
(https://web.evanchen.cc/exams/IMO-2017-notes.pdf): the rabbit repeatedly
increases the square of its distance from the hunter by `1/2` per "phase"
of `400` rounds, using a two-worlds trick (it runs to one of two points
`X`, `Y` symmetric about the line through the current positions, while the
tracking device reports points on that line, so the hunter cannot tell
which point the rabbit went to).
-/

namespace Imo2017P3

open InnerProductSpace

/-- Points of the Euclidean plane. -/
abbrev Pt := EuclideanSpace ℝ (Fin 2)

/-- The number of rounds in the game. -/
def totalRounds : ℕ := 10 ^ 9

/-- A hunter strategy: given the list of points reported by the tracking
device in rounds `1, ..., n` (in chronological order), choose the hunter's
position `Bₙ`. The hunter's move may depend only on the reported points,
not on the rabbit's actual positions. -/
abbrev Strategy := List Pt → Pt

/-- A strategy is valid if the hunter starts at the common starting point
`0` and moves by exactly `1` in every round, whatever is reported. -/
def ValidStrategy (σ : Strategy) : Prop :=
  σ [] = 0 ∧ ∀ (L : List Pt) (q : Pt), dist (σ L) (σ (L ++ [q])) = 1

/-- The reports made in rounds `1, ..., n`, as a list in chronological order. -/
def reportList (p : ℕ → Pt) : ℕ → List Pt
  | 0 => []
  | (n + 1) => reportList p n ++ [p (n + 1)]

/-- The hunter's position after round `n` when using strategy `σ` against
the reported points `p 1, ..., p n`. -/
def hunterPos (σ : Strategy) (p : ℕ → Pt) (n : ℕ) : Pt := σ (reportList p n)

/-- A rabbit path is valid if it starts at the common starting point `0`
and moves by exactly `1` in every round. -/
def ValidRabbit (A : ℕ → Pt) : Prop :=
  A 0 = 0 ∧ ∀ n, dist (A n) (A (n + 1)) = 1

/-- The reported points are valid for a rabbit path if each report is
within distance `1` of the rabbit's actual position. -/
def ValidReports (A p : ℕ → Pt) : Prop :=
  ∀ n, 1 ≤ n → dist (p n) (A n) ≤ 1

snip begin

noncomputable section

/-! ### Geometry: the phase lemma (following Evan Chen's notes) -/

/-- Pythagoras in an orthonormal frame. -/
lemma norm_sq_frame (u w : Pt) (s : ℝ) (hu : ‖u‖ = 1) (hw : ‖w‖ = 1)
    (huw : ⟪u, w⟫_ℝ = 0) :
    ‖s • u + w‖ ^ 2 = s ^ 2 + 1 ∧ ‖s • u - w‖ ^ 2 = s ^ 2 + 1 := by
  have hns : ‖s • u‖ ^ 2 = s ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, hu, mul_one, sq_abs]
  have h0 : ⟪s • u, w⟫_ℝ = 0 := by rw [real_inner_smul_left, huw, mul_zero]
  have hw2 : ‖w‖ ^ 2 = 1 := by rw [hw]; norm_num
  constructor
  · rw [norm_add_sq_real, hns, h0, hw2]; ring
  · rw [norm_sub_sq_real, hns, h0, hw2]; ring

/-- The analytic heart of the phase lemma: with `n ≥ 4d` steps, the
squared distance grows by at least `1/2`. -/
lemma core_ineq (n d h₁ h₂ s : ℝ) (hn : 1 ≤ n) (hd : 0 ≤ d) (hnd : 4 * d ≤ n)
    (hs : n - 1 / n ≤ s) (_hs' : s ≤ n) (hH : (h₁ + d) ^ 2 + h₂ ^ 2 ≤ n ^ 2) :
    d ^ 2 + 1 / 2 ≤ (h₁ - s) ^ 2 + h₂ ^ 2 + 1 := by
  have hnpos : 0 < n := by linarith
  by_cases hd2 : d ^ 2 ≤ 1 / 2
  · nlinarith [sq_nonneg (h₁ - s), sq_nonneg h₂, hd2]
  · push Not at hd2
    have hh1 : h₁ + d ≤ n := by
      by_contra hcon
      push Not at hcon
      nlinarith [sq_nonneg h₂, hH,
        mul_pos (sub_pos.mpr hcon) (show (0 : ℝ) < h₁ + d + n by linarith)]
    have hnd1 : 1 < n * d := by
      have h1 : (0 : ℝ) ≤ (n - 4 * d) * d := mul_nonneg (by linarith) hd
      nlinarith [h1, hd2]
    have ht : 0 < 1 / n := by positivity
    have hnt : n * (1 / n) = 1 := by field_simp
    have hdpos : 0 < d - 1 / n := by
      have key : (0 : ℝ) < n * (d - 1 / n) := by nlinarith [hnd1, hnt]
      exact pos_of_mul_pos_right key (le_of_lt hnpos)
    have hge : d - 1 / n ≤ s - h₁ := by linarith [hs, hh1]
    have hsq : (d - 1 / n) ^ 2 ≤ (s - h₁) ^ 2 := by
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (s - h₁) - (d - 1 / n))
        (by linarith : (0 : ℝ) ≤ (s - h₁) + (d - 1 / n))]
    have e_t : 4 * d * (1 / n) ≤ 1 := by
      have h2 : (0 : ℝ) ≤ (n - 4 * d) * (1 / n) := mul_nonneg (by linarith) (le_of_lt ht)
      nlinarith [h2, hnt]
    nlinarith [sq_nonneg h₂, sq_nonneg (1 / n), hsq, e_t]

/-- An orthonormal frame adapted to the pair `(a, b)`: `u` points from
`b` to `a`. -/
lemma frame_exists (a b : Pt) :
    ∃ u w : Pt, ‖u‖ = 1 ∧ ‖w‖ = 1 ∧ ⟪u, w⟫_ℝ = 0 ∧
      (∀ v : Pt, v = ⟪v, u⟫_ℝ • u + ⟪v, w⟫_ℝ • w) ∧ b = a - dist a b • u := by
  have inner_coord : ∀ x y : Pt, ⟪x, y⟫_ℝ = x 0 * y 0 + x 1 * y 1 := by
    intro x y
    rw [PiLp.inner_apply, Fin.sum_univ_two]
    simp [RCLike.inner_apply, mul_comm]
  have norm_sq_coord : ∀ x : Pt, ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
    intro x
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  have norm_eq_one_of_sq : ∀ x : Pt, ‖x‖ ^ 2 = 1 → ‖x‖ = 1 := by
    intro x hx
    have h : ‖x‖ ^ 2 = (1 : ℝ) ^ 2 := by rw [hx]; norm_num
    exact (sq_eq_sq₀ (norm_nonneg x) zero_le_one).mp h
  have rot : ∀ u w : Pt, u 0 ^ 2 + u 1 ^ 2 = 1 → w 0 = -u 1 → w 1 = u 0 →
      ‖w‖ = 1 ∧ ⟪u, w⟫_ℝ = 0 ∧ ∀ v : Pt, v = ⟪v, u⟫_ℝ • u + ⟪v, w⟫_ℝ • w := by
    intro u w hu2 hw0 hw1
    refine ⟨?_, ?_, ?_⟩
    · apply norm_eq_one_of_sq
      rw [norm_sq_coord, hw0, hw1]
      linear_combination hu2
    · rw [inner_coord, hw0, hw1]; ring
    · intro v
      apply PiLp.ext
      rw [Fin.forall_fin_two]
      constructor
      · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
        rw [inner_coord v u, inner_coord v w, hw0, hw1]
        linear_combination (-(v 0)) * hu2
      · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
        rw [inner_coord v u, inner_coord v w, hw0, hw1]
        linear_combination (-(v 1)) * hu2
  by_cases hab : a = b
  · subst hab
    set u : Pt := !₂[(1 : ℝ), 0] with hu_def
    set w : Pt := !₂[-u 1, u 0] with hw_def
    have hu2 : u 0 ^ 2 + u 1 ^ 2 = 1 := by rw [hu_def]; simp
    have hu1 : ‖u‖ = 1 := norm_eq_one_of_sq u (by rw [norm_sq_coord]; exact hu2)
    have hw0 : w 0 = -u 1 := by rw [hw_def]; simp
    have hw1 : w 1 = u 0 := by rw [hw_def]; simp
    obtain ⟨hnw, huw, hspan⟩ := rot u w hu2 hw0 hw1
    exact ⟨u, w, hu1, hnw, huw, hspan, by rw [dist_self, zero_smul, sub_zero]⟩
  · set u : Pt := (dist a b)⁻¹ • (a - b) with hu_def
    set w : Pt := !₂[-u 1, u 0] with hw_def
    have hdpos : 0 < dist a b := dist_pos.mpr hab
    have hu1 : ‖u‖ = 1 := by
      rw [hu_def, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hdpos),
        ← dist_eq_norm, inv_mul_cancel₀ (ne_of_gt hdpos)]
    have hu2 : u 0 ^ 2 + u 1 ^ 2 = 1 := by
      have h := norm_sq_coord u
      rw [hu1] at h
      norm_num at h
      linarith
    have hw0 : w 0 = -u 1 := by rw [hw_def]; simp
    have hw1 : w 1 = u 0 := by rw [hw_def]; simp
    obtain ⟨hnw, huw, hspan⟩ := rot u w hu2 hw0 hw1
    refine ⟨u, w, hu1, hnw, huw, hspan, ?_⟩
    rw [hu_def, smul_smul, mul_inv_cancel₀ (ne_of_gt hdpos), one_smul]
    abel

/-- **Phase lemma** (geometry). If the rabbit is at `a`, the hunter at
`b`, and the rabbit runs for `n ≥ 4 · dist a b` rounds to one of the two
points `a + s • u ± w` (with `s ≈ n`), while the device reports points on
the line, then the hunter, wherever it goes within `n` steps of `b`, ends
at distance at least `√(dist a b² + 1/2)` from one of the two points. -/
lemma phase_geom (a b H : Pt) (u w : Pt) (n s : ℝ)
    (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) (huw : ⟪u, w⟫_ℝ = 0)
    (hspan : ∀ v : Pt, v = ⟪v, u⟫_ℝ • u + ⟪v, w⟫_ℝ • w)
    (hb : b = a - dist a b • u)
    (hn : 1 ≤ n) (hnd : 4 * dist a b ≤ n)
    (hs : n - 1 / n ≤ s) (hs' : s ≤ n)
    (hH : dist b H ≤ n) :
    Real.sqrt (dist a b ^ 2 + 1 / 2) ≤
      max (dist H (a + s • u + w)) (dist H (a + s • u - w)) := by
  set h₁ := ⟪H - a, u⟫_ℝ with hh₁
  set h₂ := ⟪H - a, w⟫_ℝ with hh₂
  have hsH : H - a = h₁ • u + h₂ • w := hspan (H - a)
  have pyth : ∀ α β : ℝ, ‖α • u + β • w‖ ^ 2 = α ^ 2 + β ^ 2 := by
    intro α β
    have h1 : ‖α • u‖ ^ 2 = α ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, hu, mul_one, sq_abs]
    have h2 : ‖β • w‖ ^ 2 = β ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, hw, mul_one, sq_abs]
    have h3 : ⟪α • u, β • w⟫_ℝ = 0 := by
      rw [real_inner_smul_left, real_inner_smul_right, huw, mul_zero, mul_zero]
    rw [norm_add_sq_real, h1, h2, h3]
    ring
  have e1 : H - (a + s • u + w) = (h₁ - s) • u + (h₂ - 1) • w := by
    rw [show H - (a + s • u + w) = (H - a) - s • u - w by abel, hsH, sub_smul, sub_smul,
      one_smul]
    abel
  have e2 : H - (a + s • u - w) = (h₁ - s) • u + (h₂ + 1) • w := by
    rw [show H - (a + s • u - w) = (H - a) - s • u + w by abel, hsH, add_smul, sub_smul,
      one_smul]
    abel
  have e3 : H - b = (h₁ + dist a b) • u + h₂ • w := by
    conv_lhs => rw [hb]
    rw [show H - (a - dist a b • u) = (H - a) + dist a b • u by abel, hsH, add_smul]
    abel
  have dH1 : dist H (a + s • u + w) ^ 2 = (h₁ - s) ^ 2 + (h₂ - 1) ^ 2 := by
    rw [dist_eq_norm, e1, pyth]
  have dH2 : dist H (a + s • u - w) ^ 2 = (h₁ - s) ^ 2 + (h₂ + 1) ^ 2 := by
    rw [dist_eq_norm, e2, pyth]
  have dHb : dist b H ^ 2 = (h₁ + dist a b) ^ 2 + h₂ ^ 2 := by
    rw [dist_comm b H, dist_eq_norm, e3, pyth]
  have hH2 : (h₁ + dist a b) ^ 2 + h₂ ^ 2 ≤ n ^ 2 := by
    rw [← dHb]
    exact pow_le_pow_left₀ dist_nonneg hH 2
  have hcore : dist a b ^ 2 + 1 / 2 ≤ (h₁ - s) ^ 2 + h₂ ^ 2 + 1 :=
    core_ineq n (dist a b) h₁ h₂ s hn dist_nonneg hnd hs hs' hH2
  have hmax2 : dist a b ^ 2 + 1 / 2 ≤
      (max (dist H (a + s • u + w)) (dist H (a + s • u - w))) ^ 2 := by
    have hd1 : dist H (a + s • u + w) ^ 2 ≤
        (max (dist H (a + s • u + w)) (dist H (a + s • u - w))) ^ 2 :=
      pow_le_pow_left₀ dist_nonneg (le_max_left _ _) 2
    have hd2 : dist H (a + s • u - w) ^ 2 ≤
        (max (dist H (a + s • u + w)) (dist H (a + s • u - w))) ^ 2 :=
      pow_le_pow_left₀ dist_nonneg (le_max_right _ _) 2
    nlinarith [hcore, dH1, dH2, hd1, hd2]
  have hmaxnn : 0 ≤ max (dist H (a + s • u + w)) (dist H (a + s • u - w)) :=
    le_max_of_le_left dist_nonneg
  exact (Real.sqrt_le_left hmaxnn).mpr hmax2

/-- Bounds for `√(n² - 1)`. -/
lemma sqrt_est (n : ℝ) (hn : 1 ≤ n) : n - 1 / n ≤ Real.sqrt (n ^ 2 - 1) ∧
    Real.sqrt (n ^ 2 - 1) ≤ n := by
  have hn0 : (0:ℝ) < n := by linarith
  have hnn : (0:ℝ) ≤ n := le_of_lt hn0
  have h1 : (0:ℝ) ≤ n - 1 / n := by
    have h2 : (1:ℝ) / n ≤ 1 := by
      rw [div_le_one hn0]; exact hn
    linarith
  have e1 : n * (1 / n) = 1 := mul_one_div_cancel (ne_of_gt hn0)
  have e2 : (1:ℝ) ≤ n ^ 2 := by nlinarith [hn, hnn]
  have e3 : (1 / n) ^ 2 ≤ (1:ℝ) := by
    rw [div_pow, div_le_one (by positivity : (0:ℝ) < n ^ 2)]
    nlinarith [e2]
  have h2 : (n - 1 / n) ^ 2 ≤ n ^ 2 - 1 := by nlinarith [e1, e3, sq_nonneg (1 / n)]
  constructor
  · rw [Real.le_sqrt h1 (by nlinarith [sq_nonneg n])]
    exact h2
  · calc Real.sqrt (n ^ 2 - 1) ≤ Real.sqrt (n ^ 2) :=
          Real.sqrt_le_sqrt (by nlinarith [sq_nonneg n])
      _ = n := Real.sqrt_sq hnn

/-! ### The adversary construction -/

/-- Total number of phases: `20000` phases of 400 rounds, one phase
of 3600 rounds, then maintenance phases of 400 rounds; in total exactly
`10^9` rounds. -/
def totalPhases : ℕ := 2499992

/-- The length of phase `j`. -/
def phaseLen (j : ℕ) : ℕ := if j = 20000 then 3600 else 400

/-- The state of the adversary's construction at the start of a phase:
the rabbit's position `a`, the list `L` of reports made so far, and the
phase index `j`. -/
structure PState where
  a : Pt
  L : List Pt
  j : ℕ

/-- Running one maintenance round: the rabbit runs directly away from the
hunter and the device reports the rabbit's position honestly. -/
def maintSeq (σ : Strategy) (a : Pt) (L : List Pt) : ℕ → Pt × List Pt
  | 0 => (a, L)
  | (k + 1) =>
    let prev := maintSeq σ a L k
    let a' := prev.1 + (dist prev.1 (σ prev.2))⁻¹ • (prev.1 - σ prev.2)
    (a', prev.2 ++ [a'])

/-- The reports made during an escape phase: the device reports the point
on the line through the previous positions, at the same fractional
distance as the rabbit. -/
def escReps (a : Pt) (u : Pt) (t n : ℝ) (k : ℕ) : Pt := a + ((k : ℝ) / n) • (t • u)

/-- The rabbit's path during an escape phase when it chooses the point
`a + t • u + w`. -/
def escPath (a : Pt) (u w : Pt) (t n : ℝ) (k : ℕ) : Pt := a + ((k : ℝ) / n) • (t • u + w)

/-- The rabbit's path during an escape phase when it chooses the point
`a + t • u - w`. -/
def escPathY (a : Pt) (u w : Pt) (t n : ℝ) (k : ℕ) : Pt := a + ((k : ℝ) / n) • (t • u - w)

/-- One escape phase with frame `{u, w}`: the rabbit runs to one of the
two points `a + t • u ± w` (choosing the one farther from where the hunter
ends up), while the device reports points on the line. -/
def escStep (σ : Strategy) (s : PState) (u w : Pt) : PState × (ℕ → Pt) × (ℕ → Pt) :=
  let t := Real.sqrt (((phaseLen s.j : ℝ)) ^ 2 - 1)
  let L' := s.L ++ List.ofFn (fun k : Fin (phaseLen s.j) => escReps s.a u t (phaseLen s.j) (k + 1))
  let H := σ L'
  let path := if dist H (s.a + t • u - w) ≤ dist H (s.a + t • u + w)
    then escPath s.a u w t (phaseLen s.j)
    else escPathY s.a u w t (phaseLen s.j)
  (⟨path (phaseLen s.j), L', s.j + 1⟩, path, escReps s.a u t (phaseLen s.j))

/-- One phase of the construction. Given the state at the start of the
phase, produce the state at its end, the rabbit's positions during the
phase (as a function of the offset `k = 0, ..., phaseLen j`), and the
reports made (as a function of the offset `k = 1, ..., phaseLen j`). -/
def phaseStep (σ : Strategy) (s : PState) : PState × (ℕ → Pt) × (ℕ → Pt) :=
  if _h : dist s.a (σ s.L) ≤ 100 ∧ s.j ≤ 20000 then
    -- escape phase
    escStep σ s (Classical.choose (frame_exists s.a (σ s.L)))
      (Classical.choose (Classical.choose_spec (frame_exists s.a (σ s.L))))
  else
    -- maintenance phase
    (⟨(maintSeq σ s.a s.L (phaseLen s.j)).1, (maintSeq σ s.a s.L (phaseLen s.j)).2, s.j + 1⟩,
      (fun k => (maintSeq σ s.a s.L k).1), (fun k => (maintSeq σ s.a s.L k).1))

/-- The state at the start of phase `j`. -/
def States (σ : Strategy) : ℕ → PState
  | 0 => ⟨0, [], 0⟩
  | (j + 1) => (phaseStep σ (States σ j)).1

/-- The rabbit's positions during phase `j` (offsets `0, ..., phaseLen j`). -/
def Paths (σ : Strategy) (j : ℕ) : ℕ → Pt := (phaseStep σ (States σ j)).2.1

/-- The reports made during phase `j` (offsets `1, ..., phaseLen j`). -/
def Reps (σ : Strategy) (j : ℕ) : ℕ → Pt := (phaseStep σ (States σ j)).2.2

/-- The first round of phase `j`. -/
def startRound : ℕ → ℕ
  | 0 => 0
  | (j + 1) => startRound j + phaseLen j

/-- The phase containing round `n`. -/
def phaseOf : ℕ → ℕ
  | 0 => 0
  | (n + 1) =>
    if n + 1 < startRound (phaseOf n + 1) then phaseOf n else phaseOf n + 1

/-- The rabbit's position after round `n`. -/
def rabbit (σ : Strategy) (n : ℕ) : Pt :=
  Paths σ (phaseOf n) (n - startRound (phaseOf n))

/-- The point reported in round `n`. -/
def reports (σ : Strategy) (n : ℕ) : Pt :=
  if n = 0 then 0
  else Reps σ (phaseOf (n - 1)) (n - startRound (phaseOf (n - 1)))

/-! ### Verification -/

lemma phaseLen_pos (j : ℕ) : 0 < phaseLen j := by
  unfold phaseLen
  split_ifs <;> norm_num

lemma phaseLen_ge (j : ℕ) : 400 ≤ phaseLen j := by
  unfold phaseLen
  split_ifs <;> norm_num

lemma startRound_succ (j : ℕ) : startRound (j + 1) = startRound j + phaseLen j := rfl

lemma startRound_strictMono : StrictMono startRound := by
  apply strictMono_nat_of_lt_succ
  intro j
  rw [startRound_succ]
  have := phaseLen_pos j
  omega

lemma startRound_eq_of_le (j : ℕ) (hj : j ≤ 20000) : startRound j = 400 * j := by
  induction j with
  | zero => rfl
  | succ k ih =>
    have hk : k ≠ 20000 := by omega
    rw [startRound_succ, ih (by omega)]
    simp only [phaseLen, if_neg hk]
    ring

lemma startRound_two : startRound (20000 + 1) = 8003600 := by
  rw [startRound_succ, startRound_eq_of_le 20000 le_rfl]
  simp [phaseLen]

lemma startRound_eq_of_ge (j : ℕ) (hj : 20001 ≤ j) :
    startRound j = 8003600 + 400 * (j - 20001) := by
  induction j, hj using Nat.le_induction with
  | base => rw [startRound_two]
  | succ k hk ih =>
    have hkn : k ≠ 20000 := by omega
    rw [startRound_succ, ih]
    simp only [phaseLen, if_neg hkn]
    omega

lemma startRound_total : startRound totalPhases = totalRounds := by
  rw [startRound_eq_of_ge totalPhases (by norm_num [totalPhases])]
  norm_num [totalPhases, totalRounds]

lemma phaseOf_succ (n : ℕ) :
    phaseOf (n + 1) =
      if n + 1 < startRound (phaseOf n + 1) then phaseOf n else phaseOf n + 1 := rfl

lemma phaseOf_spec (n : ℕ) :
    startRound (phaseOf n) ≤ n ∧ n < startRound (phaseOf n + 1) := by
  induction n with
  | zero => simp [phaseOf, startRound, phaseLen]
  | succ k ih =>
    rw [phaseOf_succ]
    split_ifs with hc
    · exact ⟨le_trans ih.1 (Nat.le_succ k), hc⟩
    · rw [not_lt] at hc
      refine ⟨hc, ?_⟩
      have hk1 : k + 1 = startRound (phaseOf k + 1) :=
        le_antisymm (Nat.succ_le_of_lt ih.2) hc
      have hpos := phaseLen_pos (phaseOf k + 1)
      rw [startRound_succ]
      omega

lemma phaseOf_unique (j n : ℕ) (h₁ : startRound j ≤ n) (h₂ : n < startRound (j + 1)) :
    phaseOf n = j := by
  rcases phaseOf_spec n with ⟨g₁, g₂⟩
  rcases lt_trichotomy j (phaseOf n) with h | h | h
  · exfalso
    have h3 := startRound_strictMono.le_iff_le.mpr (show j + 1 ≤ phaseOf n by omega)
    omega
  · exact h.symm
  · exfalso
    have h3 := startRound_strictMono.le_iff_le.mpr (show phaseOf n + 1 ≤ j by omega)
    omega

/-- The hunter moves at most one list-element per round: chaining the
validity condition over an appended list of reports. -/
lemma dist_strategy_append (σ : Strategy) (hσ : ValidStrategy σ) (L : List Pt)
    (l : List Pt) :
    dist (σ L) (σ (L ++ l)) ≤ (l.length : ℝ) := by
  induction l generalizing L with
  | nil => simp
  | cons q l' ih =>
    have e : L ++ q :: l' = (L ++ [q]) ++ l' := by simp
    rw [e, List.length_cons]
    have h1 : dist (σ L) (σ (L ++ [q])) = 1 := hσ.2 L q
    have h2 := ih (L ++ [q])
    have h3 := dist_triangle (σ L) (σ (L ++ [q])) (σ ((L ++ [q]) ++ l'))
    push_cast
    linarith

lemma escReps_zero (a : Pt) (u : Pt) (t n : ℝ) : escReps a u t n 0 = a := by
  simp [escReps]

lemma escPath_zero (a : Pt) (u w : Pt) (t n : ℝ) : escPath a u w t n 0 = a := by
  simp [escPath]

lemma escPathY_zero (a : Pt) (u w : Pt) (t n : ℝ) : escPathY a u w t n 0 = a := by
  simp [escPathY]

lemma escPath_step (a : Pt) (u w : Pt) (t n : ℝ) (hn : (0:ℝ) < n)
    (hvn : ‖t • u + w‖ = n) (k : ℕ) :
    dist (escPath a u w t n k) (escPath a u w t n (k + 1)) = 1 := by
  have e : escPath a u w t n (k + 1) - escPath a u w t n k = (1 / n) • (t • u + w) := by
    unfold escPath
    rw [Nat.cast_add, Nat.cast_one, add_sub_add_left_eq_sub, ← sub_smul, add_div,
      add_sub_cancel_left]
  rw [dist_comm, dist_eq_norm, e, norm_smul, Real.norm_eq_abs,
    abs_of_pos (one_div_pos.mpr hn), hvn, one_div_mul_cancel (ne_of_gt hn)]

lemma escPathY_step (a : Pt) (u w : Pt) (t n : ℝ) (hn : (0:ℝ) < n)
    (hvn : ‖t • u - w‖ = n) (k : ℕ) :
    dist (escPathY a u w t n k) (escPathY a u w t n (k + 1)) = 1 := by
  have e : escPathY a u w t n (k + 1) - escPathY a u w t n k = (1 / n) • (t • u - w) := by
    unfold escPathY
    rw [Nat.cast_add, Nat.cast_one, add_sub_add_left_eq_sub, ← sub_smul, add_div,
      add_sub_cancel_left]
  rw [dist_comm, dist_eq_norm, e, norm_smul, Real.norm_eq_abs,
    abs_of_pos (one_div_pos.mpr hn), hvn, one_div_mul_cancel (ne_of_gt hn)]

lemma escReps_dist (a : Pt) (u w : Pt) (t n : ℝ) (hn : (0:ℝ) < n) (hw : ‖w‖ = 1)
    (k : ℕ) (hk : (k : ℝ) ≤ n) :
    dist (escReps a u t n k) (escPath a u w t n k) ≤ 1 := by
  have e : escReps a u t n k - escPath a u w t n k = -(((k : ℝ) / n) • w) := by
    unfold escReps escPath
    rw [add_sub_add_left_eq_sub, ← smul_sub, sub_add_eq_sub_sub, sub_self, zero_sub, smul_neg]
  rw [dist_eq_norm, e, norm_neg, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) (le_of_lt hn)), hw, mul_one,
    div_le_one hn]
  exact hk

lemma escReps_distY (a : Pt) (u w : Pt) (t n : ℝ) (hn : (0:ℝ) < n) (hw : ‖w‖ = 1)
    (k : ℕ) (hk : (k : ℝ) ≤ n) :
    dist (escReps a u t n k) (escPathY a u w t n k) ≤ 1 := by
  have e : escReps a u t n k - escPathY a u w t n k = ((k : ℝ) / n) • w := by
    unfold escReps escPathY
    rw [add_sub_add_left_eq_sub, ← smul_sub, sub_sub_self]
  rw [dist_eq_norm, e, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) (le_of_lt hn)), hw, mul_one,
    div_le_one hn]
  exact hk

lemma escPath_end (a : Pt) (u w : Pt) (t : ℝ) (m : ℕ) (hm : (0:ℝ) < (m : ℝ)) :
    escPath a u w t (m : ℝ) m = a + (t • u + w) := by
  simp [escPath, div_self (ne_of_gt hm)]

lemma escPathY_end (a : Pt) (u w : Pt) (t : ℝ) (m : ℕ) (hm : (0:ℝ) < (m : ℝ)) :
    escPathY a u w t (m : ℝ) m = a + (t • u - w) := by
  simp [escPathY, div_self (ne_of_gt hm)]

/-- Specification of one escape phase (with the frame made explicit). -/
lemma escStep_spec (σ : Strategy) (hσ : ValidStrategy σ) (s : PState) (u w : Pt)
    (hd : dist s.a (σ s.L) ≤ 100)
    (hu1 : ‖u‖ = 1) (hw1 : ‖w‖ = 1) (huw : ⟪u, w⟫_ℝ = 0)
    (hspan : ∀ v : Pt, v = ⟪v, u⟫_ℝ • u + ⟪v, w⟫_ℝ • w)
    (hb : σ s.L = s.a - dist s.a (σ s.L) • u) :
    let n := phaseLen s.j
    (escStep σ s u w).2.1 0 = s.a ∧
    (escStep σ s u w).2.1 n = (escStep σ s u w).1.a ∧
    (∀ k, k < n → dist ((escStep σ s u w).2.1 k) ((escStep σ s u w).2.1 (k + 1)) = 1) ∧
    (∀ k, 1 ≤ k → k ≤ n → dist ((escStep σ s u w).2.2 k) ((escStep σ s u w).2.1 k) ≤ 1) ∧
    (escStep σ s u w).1.L =
      s.L ++ List.ofFn (fun k : Fin n => (escStep σ s u w).2.2 (k + 1)) ∧
    dist s.a (σ s.L) ^ 2 + 1 / 2 ≤
      dist ((escStep σ s u w).1.a) (σ (escStep σ s u w).1.L) ^ 2 := by
  unfold escStep
  dsimp only
  set t : ℝ := Real.sqrt (((phaseLen s.j : ℝ)) ^ 2 - 1) with ht_def
  set L' := s.L ++ List.ofFn (fun k : Fin (phaseLen s.j) => escReps s.a u t (phaseLen s.j) (k + 1))
    with hL'_def
  set H := σ L' with hH_def
  have hn1 : (1:ℝ) ≤ (phaseLen s.j : ℝ) := by
    have h400 : (400 : ℝ) ≤ (phaseLen s.j : ℝ) := by exact_mod_cast phaseLen_ge s.j
    linarith
  have hnpos : (0:ℝ) < (phaseLen s.j : ℝ) := by linarith
  have ht2 : t ^ 2 = (phaseLen s.j : ℝ) ^ 2 - 1 := by
    rw [ht_def]
    exact Real.sq_sqrt (by nlinarith [hn1])
  obtain ⟨hs, hs'⟩ : (phaseLen s.j : ℝ) - 1 / (phaseLen s.j : ℝ) ≤ t ∧
      t ≤ (phaseLen s.j : ℝ) := by
    rw [ht_def]
    exact sqrt_est _ hn1
  have hvnX : ‖t • u + w‖ = (phaseLen s.j : ℝ) := by
    have h2 := (norm_sq_frame u w t hu1 hw1 huw).1
    have h3 : ‖t • u + w‖ ^ 2 = ((phaseLen s.j : ℝ)) ^ 2 := by
      rw [h2, ht2]; ring
    exact (sq_eq_sq₀ (norm_nonneg _) (by linarith)).mp h3
  have hvnY : ‖t • u - w‖ = (phaseLen s.j : ℝ) := by
    have h2 := (norm_sq_frame u w t hu1 hw1 huw).2
    have h3 : ‖t • u - w‖ ^ 2 = ((phaseLen s.j : ℝ)) ^ 2 := by
      rw [h2, ht2]; ring
    exact (sq_eq_sq₀ (norm_nonneg _) (by linarith)).mp h3
  have hHreach : dist (σ s.L) H ≤ (phaseLen s.j : ℝ) := by
    rw [hH_def, hL'_def]
    refine le_trans (dist_strategy_append σ hσ s.L _) ?_
    rw [List.length_ofFn]
  have hpg := phase_geom s.a (σ s.L) H u w (phaseLen s.j : ℝ) t hu1 hw1 huw hspan hb
    hn1 (by
      have h400 : (400 : ℝ) ≤ (phaseLen s.j : ℝ) := by exact_mod_cast phaseLen_ge s.j
      linarith [hd])
    hs hs' hHreach
  by_cases hc : dist H (s.a + t • u - w) ≤ dist H (s.a + t • u + w)
  · rw [if_pos hc]
    refine ⟨escPath_zero _ _ _ _ _, rfl, ?_, ?_, rfl, ?_⟩
    · intro k _
      exact escPath_step _ _ _ _ _ hnpos hvnX k
    · intro k _ hk
      exact escReps_dist _ _ _ _ _ hnpos hw1 k (by exact_mod_cast hk)
    · have hend := escPath_end s.a u w t (phaseLen s.j) hnpos
      have hmax : max (dist H (s.a + t • u + w)) (dist H (s.a + t • u - w)) =
          dist H (s.a + (t • u + w)) := by
        rw [max_eq_left hc, add_assoc]
      have hdist : Real.sqrt (dist s.a (σ s.L) ^ 2 + 1 / 2) ≤
          dist H (s.a + (t • u + w)) := hpg.trans hmax.le
      have hsq : dist s.a (σ s.L) ^ 2 + 1 / 2 ≤ (dist H (s.a + (t • u + w))) ^ 2 := by
        have hA := Real.sq_sqrt (show (0:ℝ) ≤ dist s.a (σ s.L) ^ 2 + 1 / 2 by positivity)
        nlinarith [hA, hdist, show (0:ℝ) ≤ dist H (s.a + (t • u + w)) from dist_nonneg,
          Real.sqrt_nonneg (dist s.a (σ s.L) ^ 2 + 1 / 2)]
      rw [hend, dist_comm (s.a + (t • u + w)) H]
      exact hsq
  · rw [if_neg hc]
    push Not at hc
    refine ⟨escPathY_zero _ _ _ _ _, rfl, ?_, ?_, rfl, ?_⟩
    · intro k _
      exact escPathY_step _ _ _ _ _ hnpos hvnY k
    · intro k _ hk
      exact escReps_distY _ _ _ _ _ hnpos hw1 k (by exact_mod_cast hk)
    · have hend := escPathY_end s.a u w t (phaseLen s.j) hnpos
      have hmax : max (dist H (s.a + t • u + w)) (dist H (s.a + t • u - w)) =
          dist H (s.a + (t • u - w)) := by
        rw [max_eq_right (le_of_lt hc), add_sub_assoc]
      have hdist : Real.sqrt (dist s.a (σ s.L) ^ 2 + 1 / 2) ≤
          dist H (s.a + (t • u - w)) := hpg.trans hmax.le
      have hsq : dist s.a (σ s.L) ^ 2 + 1 / 2 ≤ (dist H (s.a + (t • u - w))) ^ 2 := by
        have hA := Real.sq_sqrt (show (0:ℝ) ≤ dist s.a (σ s.L) ^ 2 + 1 / 2 by positivity)
        nlinarith [hA, hdist, show (0:ℝ) ≤ dist H (s.a + (t • u - w)) from dist_nonneg,
          Real.sqrt_nonneg (dist s.a (σ s.L) ^ 2 + 1 / 2)]
      rw [hend, dist_comm (s.a + (t • u - w)) H]
      exact hsq

/-- Specification of one phase, escape case. -/
lemma phaseStep_spec_escape (σ : Strategy) (hσ : ValidStrategy σ) (s : PState)
    (hd : dist s.a (σ s.L) ≤ 100) (hj : s.j ≤ 20000) :
    let n := phaseLen s.j
    (phaseStep σ s).2.1 0 = s.a ∧
    (phaseStep σ s).2.1 n = (phaseStep σ s).1.a ∧
    (∀ k, k < n → dist ((phaseStep σ s).2.1 k) ((phaseStep σ s).2.1 (k + 1)) = 1) ∧
    (∀ k, 1 ≤ k → k ≤ n → dist ((phaseStep σ s).2.2 k) ((phaseStep σ s).2.1 k) ≤ 1) ∧
    (phaseStep σ s).1.L = s.L ++ List.ofFn (fun k : Fin n => (phaseStep σ s).2.2 (k + 1)) ∧
    dist s.a (σ s.L) ^ 2 + 1 / 2 ≤ dist ((phaseStep σ s).1.a) (σ (phaseStep σ s).1.L) ^ 2 := by
  obtain ⟨hu1, hw1, huw, hspan, hb⟩ :=
    Classical.choose_spec (Classical.choose_spec (frame_exists s.a (σ s.L)))
  rw [show phaseStep σ s = escStep σ s (Classical.choose (frame_exists s.a (σ s.L)))
      (Classical.choose (Classical.choose_spec (frame_exists s.a (σ s.L)))) from by
    unfold phaseStep
    rw [dif_pos ⟨hd, hj⟩]]
  exact escStep_spec σ hσ s _ _ hd hu1 hw1 huw hspan hb

lemma maintSeq_succ_fst (σ : Strategy) (a : Pt) (L : List Pt) (k : ℕ) :
    (maintSeq σ a L (k + 1)).1 =
      (maintSeq σ a L k).1 +
        (dist ((maintSeq σ a L k).1) (σ ((maintSeq σ a L k).2)))⁻¹ •
          ((maintSeq σ a L k).1 - σ ((maintSeq σ a L k).2)) := rfl

lemma maintSeq_succ_snd (σ : Strategy) (a : Pt) (L : List Pt) (k : ℕ) :
    (maintSeq σ a L (k + 1)).2 =
      (maintSeq σ a L k).2 ++
        [(maintSeq σ a L k).1 +
          (dist ((maintSeq σ a L k).1) (σ ((maintSeq σ a L k).2)))⁻¹ •
            ((maintSeq σ a L k).1 - σ ((maintSeq σ a L k).2))] := rfl

/-- Specification of the maintenance iteration: honest reports, unit
steps, and the distance from the hunter never decreases. -/
lemma maintSeq_spec (σ : Strategy) (hσ : ValidStrategy σ) (a : Pt) (L : List Pt)
    (hd : 100 ≤ dist a (σ L)) (k : ℕ) :
    (maintSeq σ a L k).2 =
        L ++ List.ofFn (fun i : Fin k => (maintSeq σ a L (i + 1)).1) ∧
      (∀ i, i < k → dist ((maintSeq σ a L i).1) ((maintSeq σ a L (i + 1)).1) = 1) ∧
      dist a (σ L) ≤ dist ((maintSeq σ a L k).1) (σ ((maintSeq σ a L k).2)) := by
  induction k with
  | zero => exact ⟨by simp [maintSeq], fun i hi => absurd hi (Nat.not_lt_zero i), le_refl _⟩
  | succ k ih =>
    obtain ⟨ihL, ihstep, ihdist⟩ := ih
    have hd100 : 100 ≤ dist ((maintSeq σ a L k).1) (σ ((maintSeq σ a L k).2)) :=
      le_trans hd ihdist
    have hdk : (0:ℝ) < dist ((maintSeq σ a L k).1) (σ ((maintSeq σ a L k).2)) := by
      linarith
    have hunit : dist ((maintSeq σ a L k).1)
        ((maintSeq σ a L k).1 +
          (dist ((maintSeq σ a L k).1) (σ ((maintSeq σ a L k).2)))⁻¹ •
            ((maintSeq σ a L k).1 - σ ((maintSeq σ a L k).2))) = 1 := by
      rw [dist_comm, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hdk), ← dist_eq_norm]
      exact inv_mul_cancel₀ (ne_of_gt hdk)
    have hfar : dist
        ((maintSeq σ a L k).1 +
          (dist ((maintSeq σ a L k).1) (σ ((maintSeq σ a L k).2)))⁻¹ •
            ((maintSeq σ a L k).1 - σ ((maintSeq σ a L k).2)))
        (σ ((maintSeq σ a L k).2)) =
        dist ((maintSeq σ a L k).1) (σ ((maintSeq σ a L k).2)) + 1 := by
      have e : (maintSeq σ a L k).1 +
            (dist ((maintSeq σ a L k).1) (σ ((maintSeq σ a L k).2)))⁻¹ •
              ((maintSeq σ a L k).1 - σ ((maintSeq σ a L k).2)) -
            σ ((maintSeq σ a L k).2) =
          (1 + (dist ((maintSeq σ a L k).1) (σ ((maintSeq σ a L k).2)))⁻¹) •
            ((maintSeq σ a L k).1 - σ ((maintSeq σ a L k).2)) := by
        rw [add_sub_right_comm, add_smul, one_smul]
      rw [dist_eq_norm, e, norm_smul, Real.norm_eq_abs,
        abs_of_pos (by
          have hi : (0:ℝ) ≤
              (dist ((maintSeq σ a L k).1) (σ ((maintSeq σ a L k).2)))⁻¹ :=
            le_of_lt (inv_pos.mpr hdk)
          linarith),
        ← dist_eq_norm, add_mul, one_mul, inv_mul_cancel₀ (ne_of_gt hdk)]
    refine ⟨?_, ?_, ?_⟩
    · rw [maintSeq_succ_snd, ihL, List.append_assoc]
      congr 1
      rw [List.ofFn_succ', List.concat_eq_append]
      simp only [Fin.val_castSucc, Fin.val_last]
      conv_rhs => rw [maintSeq_succ_fst]
      rw [← ihL]
    · intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hik | hik
      · exact ihstep i hik
      · subst hik
        rw [maintSeq_succ_fst]
        exact hunit
    · rw [maintSeq_succ_snd, maintSeq_succ_fst]
      have h1 := hσ.2 ((maintSeq σ a L k).2)
        ((maintSeq σ a L k).1 +
          (dist ((maintSeq σ a L k).1) (σ ((maintSeq σ a L k).2)))⁻¹ •
            ((maintSeq σ a L k).1 - σ ((maintSeq σ a L k).2)))
      have h1symm : dist (σ ((maintSeq σ a L k).2 ++
            [(maintSeq σ a L k).1 +
              (dist ((maintSeq σ a L k).1) (σ ((maintSeq σ a L k).2)))⁻¹ •
                ((maintSeq σ a L k).1 - σ ((maintSeq σ a L k).2))]))
          (σ ((maintSeq σ a L k).2)) = 1 := by
        rw [dist_comm]; exact h1
      have h2 := dist_triangle
        ((maintSeq σ a L k).1 +
          (dist ((maintSeq σ a L k).1) (σ ((maintSeq σ a L k).2)))⁻¹ •
            ((maintSeq σ a L k).1 - σ ((maintSeq σ a L k).2)))
        (σ ((maintSeq σ a L k).2 ++
          [(maintSeq σ a L k).1 +
            (dist ((maintSeq σ a L k).1) (σ ((maintSeq σ a L k).2)))⁻¹ •
              ((maintSeq σ a L k).1 - σ ((maintSeq σ a L k).2))]))
        (σ ((maintSeq σ a L k).2))
      linarith

/-- Specification of one phase, maintenance case. -/
lemma phaseStep_spec_maint (σ : Strategy) (hσ : ValidStrategy σ) (s : PState)
    (hd : 100 ≤ dist s.a (σ s.L))
    (hbr : ¬ (dist s.a (σ s.L) ≤ 100 ∧ s.j ≤ 20000)) :
    let n := phaseLen s.j
    (phaseStep σ s).2.1 0 = s.a ∧
    (phaseStep σ s).2.1 n = (phaseStep σ s).1.a ∧
    (∀ k, k < n → dist ((phaseStep σ s).2.1 k) ((phaseStep σ s).2.1 (k + 1)) = 1) ∧
    (∀ k, 1 ≤ k → k ≤ n → dist ((phaseStep σ s).2.2 k) ((phaseStep σ s).2.1 k) ≤ 1) ∧
    (phaseStep σ s).1.L = s.L ++ List.ofFn (fun k : Fin n => (phaseStep σ s).2.2 (k + 1)) ∧
    100 ≤ dist ((phaseStep σ s).1.a) (σ (phaseStep σ s).1.L) ∧
    dist s.a (σ s.L) ≤ dist ((phaseStep σ s).1.a) (σ (phaseStep σ s).1.L) := by
  obtain ⟨hL, hstep, hdist⟩ := maintSeq_spec σ hσ s.a s.L hd (phaseLen s.j)
  have hd100 : 100 ≤ dist ((maintSeq σ s.a s.L (phaseLen s.j)).1)
      (σ ((maintSeq σ s.a s.L (phaseLen s.j)).2)) := le_trans hd hdist
  unfold phaseStep
  rw [dif_neg hbr]
  dsimp only
  refine ⟨rfl, rfl, hstep, ?_, hL, hd100, hdist⟩
  intro k _ _
  simp [dist_self]

lemma phaseStep_escape_eq (σ : Strategy) (s : PState)
    (hbr : dist s.a (σ s.L) ≤ 100 ∧ s.j ≤ 20000) :
    phaseStep σ s = escStep σ s (Classical.choose (frame_exists s.a (σ s.L)))
      (Classical.choose (Classical.choose_spec (frame_exists s.a (σ s.L)))) := by
  unfold phaseStep
  rw [dif_pos hbr]

lemma states_j (σ : Strategy) (j : ℕ) : (States σ j).j = j := by
  induction j with
  | zero => rfl
  | succ k ih =>
    show ((phaseStep σ (States σ k)).1).j = k + 1
    by_cases hbr : dist (States σ k).a (σ (States σ k).L) ≤ 100 ∧ (States σ k).j ≤ 20000
    · rw [phaseStep_escape_eq σ (States σ k) hbr]
      unfold escStep
      dsimp only
      rw [ih]
    · unfold phaseStep
      rw [dif_neg hbr]
      dsimp only
      rw [ih]

/-- The branch-independent part of the phase specification. -/
lemma phaseStep_spec (σ : Strategy) (hσ : ValidStrategy σ) (s : PState)
    (hdm : ¬ (dist s.a (σ s.L) ≤ 100 ∧ s.j ≤ 20000) → 100 ≤ dist s.a (σ s.L)) :
    let n := phaseLen s.j
    (phaseStep σ s).2.1 0 = s.a ∧
    (phaseStep σ s).2.1 n = (phaseStep σ s).1.a ∧
    (∀ k, k < n → dist ((phaseStep σ s).2.1 k) ((phaseStep σ s).2.1 (k + 1)) = 1) ∧
    (∀ k, 1 ≤ k → k ≤ n → dist ((phaseStep σ s).2.2 k) ((phaseStep σ s).2.1 k) ≤ 1) ∧
    (phaseStep σ s).1.L = s.L ++ List.ofFn (fun k : Fin n => (phaseStep σ s).2.2 (k + 1)) := by
  by_cases hbr : dist s.a (σ s.L) ≤ 100 ∧ s.j ≤ 20000
  · obtain ⟨a, b, c, d, e, -⟩ := phaseStep_spec_escape σ hσ s hbr.1 hbr.2
    exact ⟨a, b, c, d, e⟩
  · obtain ⟨a, b, c, d, e, -, -⟩ := phaseStep_spec_maint σ hσ s (hdm hbr) hbr
    exact ⟨a, b, c, d, e⟩

/-- The invariant: after phase `j` the squared distance is at least
`min 10000 (j/2)`, and after phase `20000` it exceeds `100`. -/
lemma invariant (σ : Strategy) (hσ : ValidStrategy σ) (j : ℕ) :
    min 10000 ((j : ℝ) / 2) ≤ dist ((States σ j).a) (σ (States σ j).L) ^ 2 ∧
    (20000 < j → 100 < dist ((States σ j).a) (σ (States σ j).L)) := by
  induction j with
  | zero =>
    refine ⟨?_, fun h => absurd h (by norm_num)⟩
    rw [show States σ 0 = ⟨0, [], 0⟩ from rfl]
    simp [hσ.1]
  | succ k ih =>
    have hsucc : States σ (k + 1) = (phaseStep σ (States σ k)).1 := rfl
    have hjk : (States σ k).j = k := states_j σ k
    by_cases hbr : dist (States σ k).a (σ (States σ k).L) ≤ 100 ∧ (States σ k).j ≤ 20000
    · obtain ⟨h0, hend, hstep, hreps, hL, hgrow⟩ :=
        phaseStep_spec_escape σ hσ (States σ k) hbr.1 hbr.2
      refine ⟨?_, ?_⟩
      · have e2 : min 10000 (((k : ℝ) + 1) / 2) ≤ min 10000 ((k : ℝ) / 2) + 1 / 2 := by
          by_cases hcase : (k : ℝ) / 2 ≤ 10000
          · rw [min_eq_right hcase]
            exact le_trans (min_le_right _ _) (by linarith)
          · rw [not_le] at hcase
            rw [min_eq_left (le_of_lt hcase)]
            exact le_trans (min_le_left _ _) (by linarith)
        push_cast
        rw [hsucc]
        linarith [ih.1, hgrow, e2]
      · intro hk20
        have hk : k = 20000 := by rw [hjk] at hbr; omega
        have hd2 : (10000 : ℝ) + 1 / 2 ≤
            dist ((phaseStep σ (States σ k)).1.a) (σ (phaseStep σ (States σ k)).1.L) ^ 2 := by
          have htmp : (10000:ℝ) ≤ min 10000 ((k : ℝ) / 2) := by
            rw [hk]; norm_num
          linarith [hgrow, htmp, ih.1]
        rw [hsucc]
        have hnn : (0:ℝ) ≤ dist ((phaseStep σ (States σ k)).1.a)
            (σ (phaseStep σ (States σ k)).1.L) := dist_nonneg
        by_contra hle
        have hsqle := pow_le_pow_left₀ hnn (le_of_not_gt hle) 2
        norm_num at hsqle
        linarith [hd2, hsqle]
    · have hd' : 100 < dist (States σ k).a (σ (States σ k).L) := by
        rw [not_and_or] at hbr
        rcases hbr with h | h
        · exact not_le.mp h
        · rw [hjk] at h
          exact ih.2 (by omega)
      obtain ⟨h0, hend, hstep, hreps, hL, hd100, hmono⟩ :=
        phaseStep_spec_maint σ hσ (States σ k) (le_of_lt hd') hbr
      refine ⟨?_, ?_⟩
      · rw [hsucc]
        refine le_trans (min_le_left _ _) ?_
        nlinarith [hd100, show (0:ℝ) ≤
          dist ((phaseStep σ (States σ k)).1.a) (σ (phaseStep σ (States σ k)).1.L) from
          dist_nonneg]
      · intro _
        rw [hsucc]
        exact lt_of_lt_of_le hd' hmono

/-- The maintenance mode hypothesis is always satisfiable. -/
lemma hdm_of (σ : Strategy) (hσ : ValidStrategy σ) (j : ℕ)
    (hbr : ¬ (dist (States σ j).a (σ (States σ j).L) ≤ 100 ∧ (States σ j).j ≤ 20000)) :
    100 ≤ dist (States σ j).a (σ (States σ j).L) := by
  rw [not_and_or] at hbr
  rcases hbr with h | h
  · exact le_of_lt (not_le.mp h)
  · have hj : 20000 < j := by have := states_j σ j; omega
    exact le_of_lt ((invariant σ hσ j).2 hj)

lemma reportList_succ (p : ℕ → Pt) (n : ℕ) :
    reportList p (n + 1) = reportList p n ++ [p (n + 1)] := rfl

lemma reportList_add (p : ℕ → Pt) (m c : ℕ) :
    reportList p (m + c) =
      reportList p m ++ List.ofFn (fun k : Fin c => p (m + (k : ℕ) + 1)) := by
  induction c with
  | zero => simp
  | succ c ih =>
    have h1 : m + (c + 1) = m + c + 1 := by omega
    rw [h1, reportList_succ, ih, List.append_assoc]
    congr 1
    rw [List.ofFn_succ', List.concat_eq_append]
    simp

lemma reportList_eq (σ : Strategy) (hσ : ValidStrategy σ) (j : ℕ) :
    reportList (reports σ) (startRound j) = (States σ j).L := by
  induction j with
  | zero => rfl
  | succ k ih =>
    rw [startRound_succ, reportList_add, ih,
      show (States σ (k + 1)) = (phaseStep σ (States σ k)).1 from rfl]
    obtain ⟨h0, hend, hstep, hreps, hL⟩ :=
      phaseStep_spec σ hσ (States σ k) (hdm_of σ hσ k)
    rw [states_j] at hL
    rw [hL]
    congr 1
    apply List.ofFn_inj.mpr
    funext i
    have hne : startRound k + ↑i + 1 ≠ 0 := by omega
    have hpk : phaseOf (startRound k + ↑i + 1 - 1) = k := by
      have e : startRound k + ↑i + 1 - 1 = startRound k + ↑i := by omega
      rw [e]
      apply phaseOf_unique
      · exact Nat.le_add_right _ _
      · rw [startRound_succ]
        have hi := i.isLt
        omega
    have harg : startRound k + ↑i + 1 - startRound k = ↑i + 1 := by omega
    unfold reports
    rw [if_neg hne, hpk, harg]
    rfl

lemma rabbit_valid (σ : Strategy) (hσ : ValidStrategy σ) : ValidRabbit (rabbit σ) := by
  refine ⟨?_, ?_⟩
  · have h1 : Paths σ 0 0 = (States σ 0).a :=
      (phaseStep_spec σ hσ (States σ 0) (hdm_of σ hσ 0)).1
    show rabbit σ 0 = 0
    show Paths σ 0 0 = 0
    exact h1
  · intro n
    obtain ⟨g1, g2⟩ := phaseOf_spec n
    obtain ⟨h0, hend, hstep, hreps, hL⟩ :=
      phaseStep_spec σ hσ (States σ (phaseOf n)) (hdm_of σ hσ (phaseOf n))
    have hjk : (States σ (phaseOf n)).j = phaseOf n := states_j σ (phaseOf n)
    rw [hjk] at hend hstep hreps hL
    set j := phaseOf n with hj_def
    set k := n - startRound j with hk_def
    have hk : k < phaseLen j := by
      rw [startRound_succ] at g2
      omega
    rcases eq_or_lt_of_le (Nat.succ_le_of_lt hk) with hke | hkl
    · have hn1 : phaseOf (n + 1) = j + 1 := by
        apply phaseOf_unique
        · rw [startRound_succ]; omega
        · rw [startRound_succ, startRound_succ]
          have hp := phaseLen_pos (j + 1)
          omega
      have e0 : n + 1 - startRound (phaseOf (n + 1)) = 0 := by
        rw [hn1, startRound_succ]; omega
      have e5 : rabbit σ n = (phaseStep σ (States σ j)).2.1 k := rfl
      have e1 : rabbit σ (n + 1) = (phaseStep σ (States σ (j + 1))).2.1 0 := by
        show Paths σ (phaseOf (n + 1)) (n + 1 - startRound (phaseOf (n + 1))) = _
        rw [e0, hn1]
        rfl
      rw [e5, e1]
      have e2 : (phaseStep σ (States σ (j + 1))).2.1 0 = (States σ (j + 1)).a :=
        (phaseStep_spec σ hσ (States σ (j + 1)) (hdm_of σ hσ (j + 1))).1
      have e3 : (States σ (j + 1)).a = (phaseStep σ (States σ j)).1.a := rfl
      rw [e2, e3, ← hend, ← hke]
      exact hstep k hk
    · have hn1 : phaseOf (n + 1) = j := by
        apply phaseOf_unique
        · omega
        · rw [startRound_succ]; omega
      have e0 : n + 1 - startRound (phaseOf (n + 1)) = k + 1 := by rw [hn1]; omega
      have e5 : rabbit σ n = (phaseStep σ (States σ j)).2.1 k := rfl
      have e1 : rabbit σ (n + 1) = (phaseStep σ (States σ j)).2.1 (k + 1) := by
        show Paths σ (phaseOf (n + 1)) (n + 1 - startRound (phaseOf (n + 1))) = _
        rw [e0, hn1]
        rfl
      rw [e5, e1]
      exact hstep k hk

lemma reports_valid (σ : Strategy) (hσ : ValidStrategy σ) :
    ValidReports (rabbit σ) (reports σ) := by
  intro n hn
  obtain ⟨g1, g2⟩ := phaseOf_spec (n - 1)
  obtain ⟨h0, hend, hstep, hreps, hL⟩ :=
    phaseStep_spec σ hσ (States σ (phaseOf (n - 1))) (hdm_of σ hσ (phaseOf (n - 1)))
  have hjk : (States σ (phaseOf (n - 1))).j = phaseOf (n - 1) := states_j σ (phaseOf (n - 1))
  rw [hjk] at hend hstep hreps hL
  set j := phaseOf (n - 1) with hj_def
  set k := n - 1 - startRound j with hk_def
  have hk : k < phaseLen j := by
    rw [startRound_succ] at g2
    omega
  have hne : n ≠ 0 := by omega
  have hoff : n - startRound (phaseOf (n - 1)) = k + 1 := by
    show n - startRound j = k + 1
    omega
  have erep : reports σ n = (phaseStep σ (States σ j)).2.2 (k + 1) := by
    unfold reports
    rw [if_neg hne, hoff]
    rfl
  have hk1 : 1 ≤ k + 1 := by omega
  rcases eq_or_lt_of_le (Nat.succ_le_of_lt hk) with hke | hkl
  · have hn1 : phaseOf n = j + 1 := by
      apply phaseOf_unique
      · rw [startRound_succ]; omega
      · rw [startRound_succ, startRound_succ]
        have hp := phaseLen_pos (j + 1)
        omega
    have e0 : n - startRound (phaseOf n) = 0 := by
      rw [hn1, startRound_succ]; omega
    have erab : rabbit σ n = (phaseStep σ (States σ (j + 1))).2.1 0 := by
      show Paths σ (phaseOf n) (n - startRound (phaseOf n)) = _
      rw [e0, hn1]
      rfl
    rw [erep, erab]
    have e2 : (phaseStep σ (States σ (j + 1))).2.1 0 = (States σ (j + 1)).a :=
      (phaseStep_spec σ hσ (States σ (j + 1)) (hdm_of σ hσ (j + 1))).1
    have e3 : (States σ (j + 1)).a = (phaseStep σ (States σ j)).1.a := rfl
    rw [e2, e3, ← hend, ← hke]
    exact hreps (k + 1) hk1 (by omega)
  · have hn1 : phaseOf n = j := by
      apply phaseOf_unique
      · omega
      · rw [startRound_succ]; omega
    have e0 : n - startRound (phaseOf n) = k + 1 := by rw [hn1]; omega
    have erab : rabbit σ n = (phaseStep σ (States σ j)).2.1 (k + 1) := by
      show Paths σ (phaseOf n) (n - startRound (phaseOf n)) = _
      rw [e0, hn1]
      rfl
    rw [erep, erab]
    exact hreps (k + 1) hk1 (by omega)

/-- The adversary wins: for every valid hunter strategy, the rabbit and
the tracking device can force the distance after `10⁹` rounds to exceed
`100`. -/
lemma adversary (σ : Strategy) (hσ : ValidStrategy σ) :
    ∃ A p : ℕ → Pt, ValidRabbit A ∧ ValidReports A p ∧
      100 < dist (A totalRounds) (hunterPos σ p totalRounds) := by
  refine ⟨rabbit σ, reports σ, rabbit_valid σ hσ, reports_valid σ hσ, ?_⟩
  have hpo : phaseOf totalRounds = totalPhases := by
    apply phaseOf_unique
    · rw [startRound_total]
    · rw [startRound_succ, startRound_total]
      have hp := phaseLen_pos totalPhases
      omega
  have hoff : totalRounds - startRound (phaseOf totalRounds) = 0 := by
    rw [hpo, startRound_total, Nat.sub_self]
  have hr : rabbit σ totalRounds = (States σ totalPhases).a := by
    show Paths σ (phaseOf totalRounds) (totalRounds - startRound (phaseOf totalRounds)) = _
    rw [hoff, hpo]
    exact (phaseStep_spec σ hσ (States σ totalPhases) (hdm_of σ hσ totalPhases)).1
  have hh : hunterPos σ (reports σ) totalRounds = σ ((States σ totalPhases).L) := by
    show σ (reportList (reports σ) totalRounds) = _
    rw [← startRound_total, reportList_eq σ hσ totalPhases]
  rw [hr, hh]
  exact (invariant σ hσ totalPhases).2 (by norm_num [totalPhases])

end

snip end

/-- The answer to the question "can the hunter always ensure that the distance
between her and the rabbit becomes at most 100?" is no. -/
determine does_exist : Bool := false

problem imo2017_p3 :
    if does_exist then
      ∃ σ : Strategy, ValidStrategy σ ∧
        ∀ A p : ℕ → Pt, ValidRabbit A → ValidReports A p →
          dist (A totalRounds) (hunterPos σ p totalRounds) ≤ 100
    else
      ¬ ∃ σ : Strategy, ValidStrategy σ ∧
        ∀ A p : ℕ → Pt, ValidRabbit A → ValidReports A p →
          dist (A totalRounds) (hunterPos σ p totalRounds) ≤ 100 := by
  change ¬ ∃ σ : Strategy, ValidStrategy σ ∧
        ∀ A p : ℕ → Pt, ValidRabbit A → ValidReports A p →
          dist (A totalRounds) (hunterPos σ p totalRounds) ≤ 100
  rintro ⟨σ, hσ, hgua⟩
  obtain ⟨A, p, hA, hp, hdist⟩ := adversary σ hσ
  exact absurd (hgua A p hA hp) (not_le.mpr hdist)

end Imo2017P3
