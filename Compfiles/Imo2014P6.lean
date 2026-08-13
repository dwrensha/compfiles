/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.EuclideanDomain.Basic
public import Mathlib.Algebra.EuclideanDomain.Field
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Order.CompletePartialOrder
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Olympiad 2014, Problem 6

A set of lines in the plane is in general position if no two are
parallel and no three pass through the same point. A set of lines in
general position cuts the plane into regions, some of which have finite
area; we call these its finite regions. Prove that for all sufficiently
large n, in any set of n lines in general position it is possible to
colour at least √n lines blue in such a way that none of its finite
regions has a completely blue boundary.
-/

namespace Imo2014P6

/-- A line in the plane `ℝ × ℝ`, given by the equation `a * x + b * y + c = 0`
with `(a, b) ≠ (0, 0)`. -/
structure Line where
  a : ℝ
  b : ℝ
  c : ℝ
  hab : a ≠ 0 ∨ b ≠ 0

noncomputable instance : DecidableEq Line := Classical.decEq _

namespace Line

/-- The affine function whose zero set is the line. -/
def val (ℓ : Line) (p : ℝ × ℝ) : ℝ := ℓ.a * p.1 + ℓ.b * p.2 + ℓ.c

/-- The line as a set of points. -/
def set (ℓ : Line) : Set (ℝ × ℝ) := {p | ℓ.val p = 0}

/-- The determinant of the two normals; nonzero iff the lines are not parallel. -/
def det (ℓ m : Line) : ℝ := ℓ.a * m.b - m.a * ℓ.b

/-- The intersection point of two non-parallel lines. -/
noncomputable def interPt (ℓ m : Line) : ℝ × ℝ :=
  ((ℓ.b * m.c - m.b * ℓ.c) / ℓ.det m, (m.a * ℓ.c - ℓ.a * m.c) / ℓ.det m)

end Line

/-- A set of lines is in *general position* if no two are parallel and no three
pass through the same point. -/
def GeneralPosition (L : Finset Line) : Prop :=
  (∀ ℓ ∈ L, ∀ m ∈ L, ℓ ≠ m → ℓ.det m ≠ 0) ∧
  (∀ ℓ ∈ L, ∀ m ∈ L, ∀ n ∈ L, ℓ ≠ m → ℓ ≠ n → m ≠ n → n.val (ℓ.interPt m) ≠ 0)

/-- The sign `±1` attached to a side of a line. -/
def sgn (b : Bool) : ℝ := if b then 1 else -1

/-- The *cell* of a sign vector `σ`: the set of points lying on the prescribed
side of every line of `L`. The nonempty cells are exactly the regions into which
the lines of `L` cut the plane, and the bounded nonempty cells are its finite
regions. -/
def Cell (L : Finset Line) (σ : Line → Bool) : Set (ℝ × ℝ) :=
  {p | ∀ ℓ ∈ L, sgn (σ ℓ) * ℓ.val p > 0}

snip begin

/-
# Solution

We follow the official solution (IMO 2014 shortlist, problem C5, Comment 2;
see also E. Chen's IMO 2014 solution notes).

Take a maximal (by inclusion) set `B` of blue lines such that no finite region
has a completely blue boundary, and write `k = |B|`. For every non-blue
(red) line `ℓ`, maximality yields a finite region whose only red boundary line
is `ℓ`. Walking around the boundary of that region clockwise, let `r` be the
endpoint of the red side where the boundary leaves the red line, and let `b` be
the next vertex; then `r` is a red point (red line × blue line) and `b` is a
blue point (blue × blue). One shows that at most two red lines can be
associated to the same blue point `b`: three of them would give three red
points `r₁, r₂, r₃` on the four blue rays from `b`; two of them, say `r₂, r₃`,
lie on one blue line through `b` while `r₁` lies on the other; the region of
`ℓ₁` must then turn at `b` towards `r₂` (or `r₃`), forcing a third line through
`r₂`, contradicting general position. Hence `n - k ≤ 2 * (k.choose 2) = k² - k`,
so `n ≤ k²` and `k ≥ √n`.

The arrangement of lines is handled through sign vectors: a region is the set of
points lying on a prescribed side of every line, and its boundary edges are
analyzed through the standard one-dimensional parametrization of each line.
-/

namespace Line

lemma val_interPt_left {ℓ m : Line} (h : ℓ.det m ≠ 0) : ℓ.val (ℓ.interPt m) = 0 := by
  have key : ℓ.a * (ℓ.b * m.c - m.b * ℓ.c) + ℓ.b * (m.a * ℓ.c - ℓ.a * m.c) +
      ℓ.c * ℓ.det m = 0 := by
    simp only [det]
    ring
  have e2 : ℓ.val (ℓ.interPt m) * ℓ.det m = 0 := by
    simp only [val, interPt]
    rw [add_mul, add_mul, mul_assoc, mul_assoc, div_mul_cancel₀ _ h, div_mul_cancel₀ _ h]
    exact key
  exact (mul_eq_zero.mp e2).resolve_right h

lemma val_interPt_right {ℓ m : Line} (h : ℓ.det m ≠ 0) : m.val (ℓ.interPt m) = 0 := by
  have key : m.a * (ℓ.b * m.c - m.b * ℓ.c) + m.b * (m.a * ℓ.c - ℓ.a * m.c) +
      m.c * ℓ.det m = 0 := by
    simp only [det]
    ring
  have e2 : m.val (ℓ.interPt m) * ℓ.det m = 0 := by
    simp only [val, interPt]
    rw [add_mul, add_mul, mul_assoc, mul_assoc, div_mul_cancel₀ _ h, div_mul_cancel₀ _ h]
    exact key
  exact (mul_eq_zero.mp e2).resolve_right h

lemma eq_interPt {ℓ m : Line} (h : ℓ.det m ≠ 0) {p : ℝ × ℝ}
    (h₁ : ℓ.val p = 0) (h₂ : m.val p = 0) : p = ℓ.interPt m := by
  have hD : ℓ.a * m.b - m.a * ℓ.b ≠ 0 := h
  have e₁ : ℓ.a * p.1 + ℓ.b * p.2 = -ℓ.c := by
    have h1 := h₁
    simp only [val] at h1
    linarith
  have e₂ : m.a * p.1 + m.b * p.2 = -m.c := by
    have h2 := h₂
    simp only [val] at h2
    linarith
  have key₁ : (ℓ.a * m.b - m.a * ℓ.b) * p.1 = ℓ.b * m.c - m.b * ℓ.c := by
    linear_combination m.b * e₁ - ℓ.b * e₂
  have key₂ : (ℓ.a * m.b - m.a * ℓ.b) * p.2 = m.a * ℓ.c - ℓ.a * m.c := by
    linear_combination ℓ.a * e₂ - m.a * e₁
  apply Prod.ext
  · exact eq_div_of_mul_eq hD (by rw [mul_comm]; exact key₁)
  · exact eq_div_of_mul_eq hD (by rw [mul_comm]; exact key₂)

/-- A distinguished point on the line: the foot of the perpendicular from the origin. -/
noncomputable def base (ℓ : Line) : ℝ × ℝ :=
  (-ℓ.c * ℓ.a / (ℓ.a ^ 2 + ℓ.b ^ 2), -ℓ.c * ℓ.b / (ℓ.a ^ 2 + ℓ.b ^ 2))

/-- A direction vector of the line: the normal `(a, b)` rotated by 90 degrees. -/
def dir (ℓ : Line) : ℝ × ℝ := (-ℓ.b, ℓ.a)

/-- The standard parametrization of the line by `ℝ`. -/
noncomputable def param (ℓ : Line) (t : ℝ) : ℝ × ℝ :=
  (ℓ.base.1 + t * ℓ.dir.1, ℓ.base.2 + t * ℓ.dir.2)

lemma sq_add_sq_pos (ℓ : Line) : 0 < ℓ.a ^ 2 + ℓ.b ^ 2 := by
  rcases ℓ.hab with h | h
  · have h1 : 0 < ℓ.a ^ 2 := sq_pos_of_ne_zero h
    linarith [sq_nonneg ℓ.b]
  · have h1 : 0 < ℓ.b ^ 2 := sq_pos_of_ne_zero h
    linarith [sq_nonneg ℓ.a]

lemma val_base (ℓ : Line) : ℓ.val ℓ.base = 0 := by
  have hQ : (ℓ.a ^ 2 + ℓ.b ^ 2) ≠ 0 := ne_of_gt ℓ.sq_add_sq_pos
  simp only [val, base]
  field_simp
  ring

lemma val_param (ℓ : Line) (t : ℝ) : ℓ.val (ℓ.param t) = 0 := by
  have h0 := ℓ.val_base
  simp only [val, param, dir] at h0 ⊢
  linear_combination h0

lemma val_param_eq (ℓ m : Line) (t : ℝ) :
    m.val (ℓ.param t) = ℓ.det m * t + m.val ℓ.base := by
  simp only [val, param, dir, det]
  ring

lemma param_injective (ℓ : Line) : Function.Injective ℓ.param := by
  intro t s h
  simp only [param, dir, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  rcases ℓ.hab with ha | hb
  · have h3 : t * ℓ.a = s * ℓ.a := by linarith
    exact mul_right_cancel₀ ha h3
  · have h3 : t * (-ℓ.b) = s * (-ℓ.b) := by linarith
    exact mul_right_cancel₀ (neg_ne_zero.mpr hb) h3

lemma mem_set_of_param (ℓ : Line) (t : ℝ) : ℓ.param t ∈ ℓ.set := ℓ.val_param t

lemma exists_param_of_mem_set (ℓ : Line) {p : ℝ × ℝ} (hp : p ∈ ℓ.set) :
    ∃ t, ℓ.param t = p := by
  have hp' : ℓ.a * p.1 + ℓ.b * p.2 = -ℓ.c := by
    have h := hp
    simp only [set, val, Set.mem_ofPred_eq] at h
    linarith
  have hbase : ℓ.a * ℓ.base.1 + ℓ.b * ℓ.base.2 = -ℓ.c := by
    have h := ℓ.val_base
    simp only [val] at h
    linarith
  rcases ℓ.hab with ha | hb
  · refine ⟨(p.2 - ℓ.base.2) / ℓ.a, Prod.ext ?_ ?_⟩
    · simp only [param, dir]
      field_simp
      linarith
    · simp only [param, dir]
      field_simp
      ring
  · refine ⟨(p.1 - ℓ.base.1) / (-ℓ.b), Prod.ext ?_ ?_⟩
    · simp only [param, dir]
      field_simp
      ring
    · simp only [param, dir]
      field_simp
      linarith

end Line

namespace GP

variable {L : Finset Line} (hGP : GeneralPosition L)

include hGP

lemma det_ne {ℓ m : Line} (hℓ : ℓ ∈ L) (hm : m ∈ L) (h : ℓ ≠ m) : ℓ.det m ≠ 0 :=
  hGP.1 ℓ hℓ m hm h

lemma not_concurrent {ℓ m n : Line} (hℓ : ℓ ∈ L) (hm : m ∈ L) (hn : n ∈ L)
    (h₁ : ℓ ≠ m) (h₂ : ℓ ≠ n) (h₃ : m ≠ n) {p : ℝ × ℝ}
    (hp₁ : ℓ.val p = 0) (hp₂ : m.val p = 0) (hp₃ : n.val p = 0) : False := by
  have hd := det_ne hGP hℓ hm h₁
  have hp := Line.eq_interPt hd hp₁ hp₂
  rw [hp] at hp₃
  exact hGP.2 ℓ hℓ m hm n hn h₁ h₂ h₃ hp₃

/-- Any line through the intersection of two distinct lines of `L` is one of them. -/
lemma eq_of_val_eq_zero {ℓ m n : Line} (hℓ : ℓ ∈ L) (hm : m ∈ L) (hn : n ∈ L)
    (hd : ℓ ≠ m) {p : ℝ × ℝ}
    (hp₁ : ℓ.val p = 0) (hp₂ : m.val p = 0) (hp₃ : n.val p = 0) : n = ℓ ∨ n = m := by
  by_cases h1 : n = ℓ
  · exact Or.inl h1
  · by_cases h2 : n = m
    · exact Or.inr h2
    · exact (not_concurrent hGP hℓ hm hn hd (Ne.symm h1) (Ne.symm h2) hp₁ hp₂ hp₃).elim

end GP

lemma sgn_ne_zero (b : Bool) : sgn b ≠ 0 := by cases b <;> norm_num [sgn]

lemma sgn_cases (b : Bool) : sgn b = 1 ∨ sgn b = -1 := by cases b <;> simp [sgn]

lemma sgn_mul_self (b : Bool) : sgn b * sgn b = 1 := by cases b <;> norm_num [sgn]

lemma Line.continuous_val (ℓ : Line) : Continuous ℓ.val := by
  unfold Line.val
  continuity

lemma isOpen_cell (L : Finset Line) (σ : Line → Bool) : IsOpen (Cell L σ) := by
  have h : Cell L σ = ⋂ ℓ ∈ L, {p : ℝ × ℝ | sgn (σ ℓ) * ℓ.val p > 0} := by
    ext p
    simp [Cell]
  rw [h]
  apply isOpen_biInter_finset
  intro ℓ _
  exact isOpen_lt continuous_const ((Line.continuous_val ℓ).const_mul _)

lemma isClosed_cellCl (L : Finset Line) (σ : Line → Bool) :
    IsClosed {p : ℝ × ℝ | ∀ ℓ ∈ L, sgn (σ ℓ) * ℓ.val p ≥ 0} := by
  have h : {p : ℝ × ℝ | ∀ ℓ ∈ L, sgn (σ ℓ) * ℓ.val p ≥ 0} =
      ⋂ ℓ ∈ L, {p : ℝ × ℝ | sgn (σ ℓ) * ℓ.val p ≥ 0} := by
    ext p
    simp
  rw [h]
  apply isClosed_biInter
  intro ℓ _
  exact isClosed_le continuous_const ((Line.continuous_val ℓ).const_mul _)

/-- The closure of a nonempty cell is given by the corresponding weak inequalities. -/
lemma closure_cell {L : Finset Line} {σ : Line → Bool} (hne : (Cell L σ).Nonempty) :
    closure (Cell L σ) = {p | ∀ ℓ ∈ L, sgn (σ ℓ) * ℓ.val p ≥ 0} := by
  obtain ⟨q, hq⟩ := hne
  apply Set.Subset.antisymm
  · apply closure_minimal
    · intro p hp ℓ hℓ
      exact le_of_lt (hp ℓ hℓ)
    · exact isClosed_cellCl L σ
  · intro p hp
    rw [Metric.mem_closure_iff]
    intro ε hε
    by_cases hpq : p = q
    · exact ⟨q, hq, by rw [← hpq, dist_self]; exact hε⟩
    · have hD : 0 < dist q p := dist_pos.mpr (Ne.symm hpq)
      set t := min (1 / 2 : ℝ) (ε / (2 * dist q p)) with ht
      have ht0 : 0 < t := lt_min (by norm_num) (by positivity)
      have ht1 : t ≤ 1 := le_trans (min_le_left _ _) (by norm_num)
      have htε : t * dist q p < ε := by
        have h1 : t * dist q p ≤ (ε / (2 * dist q p)) * dist q p := by
          gcongr
          exact min_le_right _ _
        have h2 : (ε / (2 * dist q p)) * dist q p = ε / 2 := by
          field_simp
        linarith
      refine ⟨p + t • (q - p), ?_, ?_⟩
      · intro ℓ hℓ
        have hv : ℓ.val (p + t • (q - p)) = ℓ.val p + t * (ℓ.val q - ℓ.val p) := by
          simp [Line.val, smul_eq_mul]
          ring
        rw [hv]
        have hp' : 0 ≤ sgn (σ ℓ) * ℓ.val p := hp ℓ hℓ
        have hq' : 0 < sgn (σ ℓ) * ℓ.val q := hq ℓ hℓ
        have h3 : sgn (σ ℓ) * (ℓ.val p + t * (ℓ.val q - ℓ.val p)) =
            (1 - t) * (sgn (σ ℓ) * ℓ.val p) + t * (sgn (σ ℓ) * ℓ.val q) := by ring
        rw [h3]
        nlinarith [ht0, ht1, hp', hq']
      · rwa [dist_eq_norm, sub_add_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos ht0, ← dist_eq_norm]

/-- The frontier of a cell: its closure minus itself. -/
lemma frontier_cell (L : Finset Line) (σ : Line → Bool) :
    frontier (Cell L σ) = closure (Cell L σ) \ Cell L σ :=
  (isOpen_cell L σ).frontier_eq

/-- A point lies in the frontier of a nonempty cell iff all weak sign conditions
hold and it lies on at least one line. -/
lemma mem_frontier_iff {L : Finset Line} {σ : Line → Bool} (hne : (Cell L σ).Nonempty)
    {p : ℝ × ℝ} :
    p ∈ frontier (Cell L σ) ↔
      (∀ ℓ ∈ L, sgn (σ ℓ) * ℓ.val p ≥ 0) ∧ (∃ ℓ ∈ L, ℓ.val p = 0) := by
  rw [frontier_cell L σ, closure_cell hne]
  constructor
  · intro hp
    refine ⟨hp.1, ?_⟩
    by_contra h
    have hpc : p ∈ Cell L σ := by
      intro ℓ hℓ
      have h1 := hp.1 ℓ hℓ
      have h3 : ℓ.val p ≠ 0 := by
        intro hz
        exact h ⟨ℓ, hℓ, hz⟩
      rcases lt_or_eq_of_le h1 with h4 | h4
      · exact h4
      · exfalso
        rcases mul_eq_zero.mp h4.symm with h5 | h5
        · exact sgn_ne_zero (σ ℓ) h5
        · exact h3 h5
    exact hp.2 hpc
  · intro hp
    obtain ⟨hp1, ℓ, hℓ, hp2⟩ := hp
    refine ⟨hp1, ?_⟩
    intro hpc
    have h5 := hpc ℓ hℓ
    rw [hp2, mul_zero] at h5
    exact (lt_irrefl 0) h5

/-- The working definition of "no finite region has a completely blue boundary":
for every nonempty bounded cell, some line meeting the closure of the cell is
not blue. -/
def ValidBlue (L B : Finset Line) : Prop :=
  ∀ σ : Line → Bool, (Cell L σ).Nonempty → Bornology.IsBounded (Cell L σ) →
    ∃ ℓ ∈ L, (closure (Cell L σ) ∩ ℓ.set).Nonempty ∧ ℓ ∉ B

/-! ### Edge analysis of a bounded cell

The intersection of the closure of a bounded cell with a boundary line `ℓ` is a
closed segment. Pulling back along the standard parametrization of `ℓ`, the set
of parameters giving points of the closure is a closed bounded interval
`[T₁, T₂]` with `T₁ < T₂`; the endpoints are the vertices of the edge. -/

namespace Line

/-- The parameter value where the standard parametrization of `ℓ` crosses `m`. -/
noncomputable def crossT (ℓ m : Line) : ℝ := - m.val ℓ.base / ℓ.det m

lemma val_param_crossT {ℓ m : Line} (h : ℓ.det m ≠ 0) :
    m.val (ℓ.param (ℓ.crossT m)) = 0 := by
  rw [val_param_eq, crossT, ← mul_div_assoc, mul_div_cancel_left₀ _ h, neg_add_cancel]

lemma crossT_eq_of_val_param_eq_zero {ℓ m : Line} (h : ℓ.det m ≠ 0) {t : ℝ}
    (ht : m.val (ℓ.param t) = 0) : t = ℓ.crossT m := by
  rw [val_param_eq] at ht
  have h1 : ℓ.det m * t = - m.val ℓ.base := by linarith
  rw [crossT]
  field_simp
  linarith

/-- The sign constraint on `m` along the parametrization of `ℓ`, as a bound on `t`. -/
lemma constraint_iff {σ : Line → Bool} {ℓ m : Line} (hdet : ℓ.det m ≠ 0) (t : ℝ) :
    0 ≤ sgn (σ m) * m.val (ℓ.param t) ↔
      (if 0 < sgn (σ m) * ℓ.det m then ℓ.crossT m ≤ t else t ≤ ℓ.crossT m) := by
  rw [val_param_eq]
  have key : sgn (σ m) * (ℓ.det m * t + m.val ℓ.base) =
      (sgn (σ m) * ℓ.det m) * (t - ℓ.crossT m) := by
    simp only [crossT]
    field_simp
    ring
  rw [key]
  by_cases h : 0 < sgn (σ m) * ℓ.det m
  · rw [if_pos h, mul_nonneg_iff_right_nonneg_of_pos h, sub_nonneg]
  · rw [if_neg h]
    have h2 : sgn (σ m) * ℓ.det m < 0 := by
      have h3 : sgn (σ m) * ℓ.det m ≠ 0 := mul_ne_zero (sgn_ne_zero _) hdet
      exact lt_of_le_of_ne' (le_of_not_gt h) h3.symm
    have h4 : (0:ℝ) ≤ (sgn (σ m) * ℓ.det m) * (t - ℓ.crossT m) ↔ t - ℓ.crossT m ≤ 0 :=
      ⟨(nonpos_of_mul_nonneg_right · h2), (mul_nonneg_of_nonpos_of_nonpos h2.le ·)⟩
    rw [h4, sub_nonpos]

end Line

/-- The lines whose constraint is a lower bound on the parameter along `ℓ`. -/
noncomputable def lows (L : Finset Line) (σ : Line → Bool) (ℓ : Line) : Finset Line :=
  L.filter fun m => m ≠ ℓ ∧ 0 < sgn (σ m) * ℓ.det m

/-- The lines whose constraint is an upper bound on the parameter along `ℓ`. -/
noncomputable def upps (L : Finset Line) (σ : Line → Bool) (ℓ : Line) : Finset Line :=
  L.filter fun m => m ≠ ℓ ∧ sgn (σ m) * ℓ.det m < 0

lemma mem_lows {L : Finset Line} {σ : Line → Bool} {ℓ m : Line} :
    m ∈ lows L σ ℓ ↔ m ∈ L ∧ m ≠ ℓ ∧ 0 < sgn (σ m) * ℓ.det m := by
  simp [lows]

lemma mem_upps {L : Finset Line} {σ : Line → Bool} {ℓ m : Line} :
    m ∈ upps L σ ℓ ↔ m ∈ L ∧ m ≠ ℓ ∧ sgn (σ m) * ℓ.det m < 0 := by
  simp [upps]

lemma lows_or_upps {L : Finset Line} {σ : Line → Bool} {ℓ m : Line}
    (hGP : GeneralPosition L) (hℓ : ℓ ∈ L) (hm : m ∈ L) (h : m ≠ ℓ) :
    m ∈ lows L σ ℓ ∨ m ∈ upps L σ ℓ := by
  have hd := GP.det_ne hGP hℓ hm (Ne.symm h)
  have h2 : sgn (σ m) * ℓ.det m ≠ 0 := mul_ne_zero (sgn_ne_zero _) hd
  rcases lt_or_gt_of_ne h2 with h3 | h3
  · exact Or.inr (mem_upps.mpr ⟨hm, h, h3⟩)
  · exact Or.inl (mem_lows.mpr ⟨hm, h, h3⟩)

lemma param_constraint_iff {L : Finset Line} {ℓ : Line} (hGP : GeneralPosition L) (hℓ : ℓ ∈ L)
    (σ : Line → Bool) (t : ℝ) :
    (∀ m ∈ L, 0 ≤ sgn (σ m) * m.val (ℓ.param t)) ↔
      (∀ m ∈ lows L σ ℓ, ℓ.crossT m ≤ t) ∧ (∀ m ∈ upps L σ ℓ, t ≤ ℓ.crossT m) := by
  constructor
  · intro h
    constructor
    · intro m hm
      obtain ⟨hmL, hmℓ, hpos⟩ := mem_lows.mp hm
      have h1 := h m hmL
      rw [Line.constraint_iff (GP.det_ne hGP hℓ hmL (Ne.symm hmℓ)) t, if_pos hpos] at h1
      exact h1
    · intro m hm
      obtain ⟨hmL, hmℓ, hneg⟩ := mem_upps.mp hm
      have h1 := h m hmL
      rw [Line.constraint_iff (GP.det_ne hGP hℓ hmL (Ne.symm hmℓ)) t, if_neg (not_lt.mpr hneg.le)] at h1
      exact h1
  · intro h m hm
    by_cases hml : m = ℓ
    · rw [hml, Line.val_param, mul_zero]
    · rcases lows_or_upps hGP hℓ hm hml with hl | hu
      · have h1 := h.1 m hl
        rw [Line.constraint_iff (GP.det_ne hGP hℓ hm (Ne.symm hml)) t,
          if_pos (mem_lows.mp hl).2.2]
        exact h1
      · have h1 := h.2 m hu
        rw [Line.constraint_iff (GP.det_ne hGP hℓ hm (Ne.symm hml)) t,
          if_neg (not_lt.mpr (mem_upps.mp hu).2.2.le)]
        exact h1

lemma abs_fst_sub_le_dist (p q : ℝ × ℝ) : |p.1 - q.1| ≤ dist p q := by
  rw [dist_eq_norm]
  calc |p.1 - q.1| = ‖(p - q).1‖ := by simp [Real.norm_eq_abs]
    _ ≤ ‖p - q‖ := by rw [Prod.norm_def]; exact le_max_left _ _

lemma abs_snd_sub_le_dist (p q : ℝ × ℝ) : |p.2 - q.2| ≤ dist p q := by
  rw [dist_eq_norm]
  calc |p.2 - q.2| = ‖(p - q).2‖ := by simp [Real.norm_eq_abs]
    _ ≤ ‖p - q‖ := by rw [Prod.norm_def]; exact le_max_right _ _

/-- A bounded cell of an arrangement in general position, together with a
distinguished boundary line `ℓ`. -/
structure EdgeCtx (L : Finset Line) where
  σ : Line → Bool
  ℓ : Line
  hGP : GeneralPosition L
  hne : (Cell L σ).Nonempty
  hbdd : Bornology.IsBounded (Cell L σ)
  hℓ : ℓ ∈ L
  hedge : (closure (Cell L σ) ∩ ℓ.set).Nonempty

namespace EdgeCtx

/-- The parameters of points of the closure of the cell on the line `ℓ`
form a bounded set. -/
lemma exists_abs_le {L : Finset Line} (E : EdgeCtx L) : ∃ B : ℝ, ∀ t : ℝ,
    (∀ m ∈ L, 0 ≤ sgn (E.σ m) * m.val (E.ℓ.param t)) → |t| ≤ B := by
  obtain ⟨r, hr⟩ := Bornology.IsBounded.subset_closedBall E.hbdd.closure E.ℓ.base
  have hcell : ∀ t : ℝ, (∀ m ∈ L, 0 ≤ sgn (E.σ m) * m.val (E.ℓ.param t)) →
      E.ℓ.param t ∈ closure (Cell L E.σ) := by
    intro t ht
    rw [closure_cell E.hne]
    exact ht
  rcases E.ℓ.hab with ha | hb
  · refine ⟨r / |E.ℓ.a|, fun t ht => ?_⟩
    have h1 : E.ℓ.param t ∈ Metric.closedBall E.ℓ.base r := hr (hcell t ht)
    rw [Metric.mem_closedBall] at h1
    have h2 : |(E.ℓ.param t).2 - E.ℓ.base.2| ≤ dist (E.ℓ.param t) E.ℓ.base :=
      abs_snd_sub_le_dist _ _
    have h3 : (E.ℓ.param t).2 - E.ℓ.base.2 = t * E.ℓ.a := by
      simp [Line.param, Line.dir]
    rw [h3, abs_mul] at h2
    have h4 : |t| * |E.ℓ.a| ≤ r := le_trans h2 h1
    exact (le_div_iff₀ (abs_pos.mpr ha)).mpr h4
  · refine ⟨r / |E.ℓ.b|, fun t ht => ?_⟩
    have h1 : E.ℓ.param t ∈ Metric.closedBall E.ℓ.base r := hr (hcell t ht)
    rw [Metric.mem_closedBall] at h1
    have h2 : |(E.ℓ.param t).1 - E.ℓ.base.1| ≤ dist (E.ℓ.param t) E.ℓ.base :=
      abs_fst_sub_le_dist _ _
    have h3 : (E.ℓ.param t).1 - E.ℓ.base.1 = t * (-E.ℓ.b) := by
      simp [Line.param, Line.dir]
    rw [h3, abs_mul, abs_neg] at h2
    have h4 : |t| * |E.ℓ.b| ≤ r := le_trans h2 h1
    exact (le_div_iff₀ (abs_pos.mpr hb)).mpr h4

/-- Some parameter realizes a point of the closure on `ℓ`. -/
lemma exists_param_mem {L : Finset Line} (E : EdgeCtx L) :
    ∃ t : ℝ, (∀ m ∈ L, 0 ≤ sgn (E.σ m) * m.val (E.ℓ.param t)) := by
  obtain ⟨p, hp1, hp2⟩ := E.hedge
  obtain ⟨t, rfl⟩ := E.ℓ.exists_param_of_mem_set hp2
  refine ⟨t, ?_⟩
  rw [closure_cell E.hne] at hp1
  exact hp1

lemma upps_nonempty {L : Finset Line} (E : EdgeCtx L) : (upps L E.σ E.ℓ).Nonempty := by
  obtain ⟨B, hB⟩ := E.exists_abs_le
  obtain ⟨t₀, ht₀⟩ := E.exists_param_mem
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB t₀ ht₀)
  by_contra h
  rw [Finset.not_nonempty_iff_eq_empty] at h
  set t := B + 1 + ∑ m ∈ lows L E.σ E.ℓ, |E.ℓ.crossT m| with ht
  have hlow : ∀ m ∈ lows L E.σ E.ℓ, E.ℓ.crossT m ≤ t := by
    intro m hm
    have h1 : |E.ℓ.crossT m| ≤ ∑ m' ∈ lows L E.σ E.ℓ, |E.ℓ.crossT m'| :=
      Finset.single_le_sum (f := fun m' => |E.ℓ.crossT m'|) (fun m' _ => abs_nonneg _) hm
    have h2 : E.ℓ.crossT m ≤ |E.ℓ.crossT m| := le_abs_self _
    linarith
  have hup : ∀ m ∈ upps L E.σ E.ℓ, t ≤ E.ℓ.crossT m := by
    intro m hm
    rw [h] at hm
    simp at hm
  have htE : ∀ m ∈ L, 0 ≤ sgn (E.σ m) * m.val (E.ℓ.param t) :=
    (param_constraint_iff E.hGP E.hℓ E.σ t).mpr ⟨hlow, hup⟩
  have htB : |t| ≤ B := hB t htE
  have htpos : 0 < t := by
    have h1 : 0 ≤ ∑ m ∈ lows L E.σ E.ℓ, |E.ℓ.crossT m| := Finset.sum_nonneg (fun m _ => abs_nonneg _)
    linarith
  rw [abs_of_pos htpos] at htB
  have h1 : 0 ≤ ∑ m ∈ lows L E.σ E.ℓ, |E.ℓ.crossT m| := Finset.sum_nonneg (fun m _ => abs_nonneg _)
  linarith

lemma lows_nonempty {L : Finset Line} (E : EdgeCtx L) : (lows L E.σ E.ℓ).Nonempty := by
  obtain ⟨B, hB⟩ := E.exists_abs_le
  obtain ⟨t₀, ht₀⟩ := E.exists_param_mem
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB t₀ ht₀)
  by_contra h
  rw [Finset.not_nonempty_iff_eq_empty] at h
  set t := -(B + 1) - ∑ m ∈ upps L E.σ E.ℓ, |E.ℓ.crossT m| with ht
  have hup : ∀ m ∈ upps L E.σ E.ℓ, t ≤ E.ℓ.crossT m := by
    intro m hm
    have h1 : |E.ℓ.crossT m| ≤ ∑ m' ∈ upps L E.σ E.ℓ, |E.ℓ.crossT m'| :=
      Finset.single_le_sum (f := fun m' => |E.ℓ.crossT m'|) (fun m' _ => abs_nonneg _) hm
    have h2 : E.ℓ.crossT m ≥ -|E.ℓ.crossT m| := neg_abs_le _
    linarith
  have hlow : ∀ m ∈ lows L E.σ E.ℓ, E.ℓ.crossT m ≤ t := by
    intro m hm
    rw [h] at hm
    simp at hm
  have htE : ∀ m ∈ L, 0 ≤ sgn (E.σ m) * m.val (E.ℓ.param t) :=
    (param_constraint_iff E.hGP E.hℓ E.σ t).mpr ⟨hlow, hup⟩
  have htB : |t| ≤ B := hB t htE
  have htneg : t < 0 := by
    have h1 : 0 ≤ ∑ m ∈ upps L E.σ E.ℓ, |E.ℓ.crossT m| := Finset.sum_nonneg (fun m _ => abs_nonneg _)
    linarith
  rw [abs_of_neg htneg] at htB
  have h1 : 0 ≤ ∑ m ∈ upps L E.σ E.ℓ, |E.ℓ.crossT m| := Finset.sum_nonneg (fun m _ => abs_nonneg _)
  linarith

/-- The lower endpoint of the edge, in parameter form. -/
noncomputable def Tmin {L : Finset Line} (E : EdgeCtx L) : ℝ :=
  ((lows L E.σ E.ℓ).image (Line.crossT E.ℓ)).max' (Finset.image_nonempty.mpr E.lows_nonempty)

/-- The upper endpoint of the edge, in parameter form. -/
noncomputable def Tmax {L : Finset Line} (E : EdgeCtx L) : ℝ :=
  ((upps L E.σ E.ℓ).image (Line.crossT E.ℓ)).min' (Finset.image_nonempty.mpr E.upps_nonempty)

lemma E_eq_Icc {L : Finset Line} (E : EdgeCtx L) :
    {t : ℝ | ∀ m ∈ L, 0 ≤ sgn (E.σ m) * m.val (E.ℓ.param t)} = Set.Icc E.Tmin E.Tmax := by
  ext t
  simp only [Set.mem_ofPred_eq]
  rw [param_constraint_iff E.hGP E.hℓ E.σ t, Set.mem_Icc]
  constructor
  · intro h
    constructor
    · apply Finset.max'_le
      intro y hy
      simp only [Finset.mem_image] at hy
      obtain ⟨m, hm, rfl⟩ := hy
      exact h.1 m hm
    · apply Finset.le_min'
      intro y hy
      simp only [Finset.mem_image] at hy
      obtain ⟨m, hm, rfl⟩ := hy
      exact h.2 m hm
  · intro h
    obtain ⟨h1, h2⟩ := h
    constructor
    · intro m hm
      have h3 : E.ℓ.crossT m ≤ E.Tmin :=
        Finset.le_max' _ _ (Finset.mem_image_of_mem _ hm)
      exact le_trans h3 h1
    · intro m hm
      have h3 : E.Tmax ≤ E.ℓ.crossT m :=
        Finset.min'_le _ _ (Finset.mem_image_of_mem _ hm)
      exact le_trans h2 h3

lemma Tmin_le_Tmax {L : Finset Line} (E : EdgeCtx L) : E.Tmin ≤ E.Tmax := by
  obtain ⟨t₀, ht₀⟩ := E.exists_param_mem
  have ht : t₀ ∈ Set.Icc E.Tmin E.Tmax := by
    rw [← E.E_eq_Icc]
    exact ht₀
  exact ht.1.trans ht.2

lemma exists_low_cross {L : Finset Line} (E : EdgeCtx L) :
    ∃ m ∈ lows L E.σ E.ℓ, E.ℓ.crossT m = E.Tmin := by
  have h := ((lows L E.σ E.ℓ).image (Line.crossT E.ℓ)).max'_mem
    (Finset.image_nonempty.mpr E.lows_nonempty)
  simp only [Finset.mem_image] at h
  obtain ⟨m, hm, hmt⟩ := h
  exact ⟨m, hm, hmt⟩

lemma exists_upp_cross {L : Finset Line} (E : EdgeCtx L) :
    ∃ m ∈ upps L E.σ E.ℓ, E.ℓ.crossT m = E.Tmax := by
  have h := ((upps L E.σ E.ℓ).image (Line.crossT E.ℓ)).min'_mem
    (Finset.image_nonempty.mpr E.upps_nonempty)
  simp only [Finset.mem_image] at h
  obtain ⟨m, hm, hmt⟩ := h
  exact ⟨m, hm, hmt⟩

/-- The two endpoints are distinct: they would otherwise give three concurrent lines. -/
lemma Tmin_lt_Tmax {L : Finset Line} (E : EdgeCtx L) : E.Tmin < E.Tmax := by
  obtain ⟨m₁, hm₁, hmt₁⟩ := E.exists_low_cross
  obtain ⟨m₂, hm₂, hmt₂⟩ := E.exists_upp_cross
  have h1 := mem_lows.mp hm₁
  have h2 := mem_upps.mp hm₂
  have hm12 : m₁ ≠ m₂ := by
    intro h
    rw [h] at h1
    linarith [h1.2.2, h2.2.2]
  have hle := E.Tmin_le_Tmax
  rcases eq_or_lt_of_le hle with heq | hlt
  · exfalso
    have hp1 : m₁.val (E.ℓ.param E.Tmin) = 0 := by
      rw [← hmt₁]
      exact Line.val_param_crossT (GP.det_ne E.hGP E.hℓ h1.1 (Ne.symm h1.2.1))
    have hp2 : m₂.val (E.ℓ.param E.Tmin) = 0 := by
      rw [heq, ← hmt₂]
      exact Line.val_param_crossT (GP.det_ne E.hGP E.hℓ h2.1 (Ne.symm h2.2.1))
    have hp3 : E.ℓ.val (E.ℓ.param E.Tmin) = 0 := Line.val_param _ _
    exact GP.not_concurrent E.hGP E.hℓ h1.1 h2.1 (Ne.symm h1.2.1) (Ne.symm h2.2.1)
      hm12 hp3 hp1 hp2
  · exact hlt

/-- The pullback of the edge along the parametrization contains no crossing
in its interior. -/
lemma val_ne_zero_of_mem_Ioo {L : Finset Line} (E : EdgeCtx L) {m : Line} (hm : m ∈ L)
    (hmℓ : m ≠ E.ℓ) {t : ℝ}
    (ht : t ∈ Set.Ioo E.Tmin E.Tmax) : m.val (E.ℓ.param t) ≠ 0 := by
  intro hz
  rcases lows_or_upps E.hGP E.hℓ hm hmℓ with hl | hu
  · have h2 : t = E.ℓ.crossT m :=
      Line.crossT_eq_of_val_param_eq_zero (GP.det_ne E.hGP E.hℓ hm (Ne.symm hmℓ)) hz
    have h3 : E.ℓ.crossT m ≤ E.Tmin :=
      Finset.le_max' _ _ (Finset.mem_image_of_mem _ hl)
    linarith [ht.1]
  · have h2 : t = E.ℓ.crossT m :=
      Line.crossT_eq_of_val_param_eq_zero (GP.det_ne E.hGP E.hℓ hm (Ne.symm hmℓ)) hz
    have h3 : E.Tmax ≤ E.ℓ.crossT m :=
      Finset.min'_le _ _ (Finset.mem_image_of_mem _ hu)
    linarith [ht.2]

/-- The parametrized points of the edge segment lie in the closure of the cell
and on the line. -/
lemma param_mem_closure_inter {L : Finset Line} (E : EdgeCtx L) {t : ℝ}
    (ht : t ∈ Set.Icc E.Tmin E.Tmax) :
    E.ℓ.param t ∈ closure (Cell L E.σ) ∩ E.ℓ.set := by
  constructor
  · rw [closure_cell E.hne]
    have ht2 : t ∈ {t : ℝ | ∀ m ∈ L, 0 ≤ sgn (E.σ m) * m.val (E.ℓ.param t)} := by
      rw [E.E_eq_Icc]
      exact ht
    exact ht2
  · exact Line.val_param _ _

/-- At the upper endpoint, some other line of the arrangement passes:
the line realizing the upper bound. -/
lemma exists_line_at_Tmax {L : Finset Line} (E : EdgeCtx L) :
    ∃ m ∈ L, m ≠ E.ℓ ∧ m.val (E.ℓ.param E.Tmax) = 0 := by
  obtain ⟨m, hm, hmt⟩ := E.exists_upp_cross
  have h1 := mem_upps.mp hm
  refine ⟨m, h1.1, h1.2.1, ?_⟩
  rw [← hmt]
  exact Line.val_param_crossT (GP.det_ne E.hGP E.hℓ h1.1 (Ne.symm h1.2.1))

/-- At the lower endpoint, some other line of the arrangement passes. -/
lemma exists_line_at_Tmin {L : Finset Line} (E : EdgeCtx L) :
    ∃ m ∈ L, m ≠ E.ℓ ∧ m.val (E.ℓ.param E.Tmin) = 0 := by
  obtain ⟨m, hm, hmt⟩ := E.exists_low_cross
  have h1 := mem_lows.mp hm
  refine ⟨m, h1.1, h1.2.1, ?_⟩
  rw [← hmt]
  exact Line.val_param_crossT (GP.det_ne E.hGP E.hℓ h1.1 (Ne.symm h1.2.1))

/-- At most one other line passes through an endpoint (general position). -/
lemma eq_of_val_at_param {L : Finset Line} (E : EdgeCtx L) {m n : Line} (hm : m ∈ L)
    (hn : n ∈ L) (hmℓ : m ≠ E.ℓ) (hnℓ : n ≠ E.ℓ) {t : ℝ}
    (hmt : m.val (E.ℓ.param t) = 0) (hnt : n.val (E.ℓ.param t) = 0) : m = n := by
  by_cases h : m = n
  · exact h
  · exfalso
    exact GP.not_concurrent E.hGP E.hℓ hm hn (Ne.symm hmℓ) (Ne.symm hnℓ) h
      (Line.val_param _ _) hmt hnt

end EdgeCtx

lemma Line.det_comm (ℓ m : Line) : ℓ.det m = - m.det ℓ := by
  simp only [det]
  ring

/-! ### The witness region of a red line and the association `ℓ ↦ (r, b)`

For a maximal valid blue set `B`, every red line `ℓ` comes with a finite region
whose only non-blue boundary line is `ℓ`.  We call the two endpoints of the
red edge `r₁, r` (in clockwise order) and the next vertex `b`; the pair
`(r, b)` consists of a red point and a blue point, and we show that at most two
red lines can be associated to the same blue point. -/

/-- A witness region for a red line `ℓ`: a bounded cell of the arrangement whose
boundary lines are all blue, except `ℓ`, which does occur on the boundary. -/
structure Witness (L B : Finset Line) (ℓ : Line) where
  σ : Line → Bool
  hne : (Cell L σ).Nonempty
  hbdd : Bornology.IsBounded (Cell L σ)
  hbd : ∀ m ∈ L, (closure (Cell L σ) ∩ m.set).Nonempty → m ∈ insert ℓ B
  hℓ : (closure (Cell L σ) ∩ ℓ.set).Nonempty

namespace Witness

variable {L B : Finset Line} {ℓ : Line} (W : Witness L B ℓ)

/-- The edge context of the red line `ℓ`. -/
noncomputable def ectx (hGP : GeneralPosition L) (hℓL : ℓ ∈ L) : EdgeCtx L :=
  ⟨W.σ, ℓ, hGP, W.hne, W.hbdd, hℓL, W.hℓ⟩

/-- The parameter of the red point `r`: the endpoint of the red edge at which
the clockwise traversal of the boundary leaves the red line. -/
noncomputable def rT (hGP : GeneralPosition L) (hℓL : ℓ ∈ L) : ℝ :=
  if W.σ ℓ then (W.ectx hGP hℓL).Tmax else (W.ectx hGP hℓL).Tmin

/-- The red point associated to `ℓ`. -/
noncomputable def r (hGP : GeneralPosition L) (hℓL : ℓ ∈ L) : ℝ × ℝ :=
  ℓ.param (W.rT hGP hℓL)

lemma rT_mem_Icc (hGP : GeneralPosition L) (hℓL : ℓ ∈ L) :
    W.rT hGP hℓL ∈ Set.Icc (W.ectx hGP hℓL).Tmin (W.ectx hGP hℓL).Tmax := by
  rw [rT]
  split
  · exact Set.right_mem_Icc.mpr (W.ectx hGP hℓL).Tmin_le_Tmax
  · exact Set.left_mem_Icc.mpr (W.ectx hGP hℓL).Tmin_le_Tmax

lemma r_mem_closure (hGP : GeneralPosition L) (hℓL : ℓ ∈ L) :
    W.r hGP hℓL ∈ closure (Cell L W.σ) ∩ ℓ.set :=
  (W.ectx hGP hℓL).param_mem_closure_inter (W.rT_mem_Icc hGP hℓL)

lemma rT_ne (hGP : GeneralPosition L) (hℓL : ℓ ∈ L) :
    W.rT hGP hℓL ≠ (W.ectx hGP hℓL).Tmin ∧ W.rT hGP hℓL ≠ (W.ectx hGP hℓL).Tmax →
      False := by
  intro h
  rw [rT] at h
  split at h
  · exact h.2 rfl
  · exact h.1 rfl

/-- The other line through `r` exists. -/
lemma exists_g1 (hGP : GeneralPosition L) (hℓL : ℓ ∈ L) :
    ∃ g ∈ L, g ≠ ℓ ∧ g.val (W.r hGP hℓL) = 0 := by
  rw [r, rT]
  split
  · exact (W.ectx hGP hℓL).exists_line_at_Tmax
  · exact (W.ectx hGP hℓL).exists_line_at_Tmin

/-- The other line through `r` is unique. -/
lemma g1_unique (hGP : GeneralPosition L) (hℓL : ℓ ∈ L) {g g' : Line}
    (hg : g ∈ L) (hg' : g' ∈ L) (hgℓ : g ≠ ℓ) (hg'ℓ : g' ≠ ℓ)
    (hgr : g.val (W.r hGP hℓL) = 0) (hg'r : g'.val (W.r hGP hℓL) = 0) : g = g' :=
  (W.ectx hGP hℓL).eq_of_val_at_param hg hg' hgℓ hg'ℓ hgr hg'r

/-- The other line through `r` (a blue line). -/
noncomputable def g1 (hGP : GeneralPosition L) (hℓL : ℓ ∈ L) : Line :=
  Classical.choose (W.exists_g1 hGP hℓL)

lemma g1_mem (hGP : GeneralPosition L) (hℓL : ℓ ∈ L) : W.g1 hGP hℓL ∈ L :=
  (Classical.choose_spec (W.exists_g1 hGP hℓL)).1

lemma g1_ne (hGP : GeneralPosition L) (hℓL : ℓ ∈ L) : W.g1 hGP hℓL ≠ ℓ :=
  (Classical.choose_spec (W.exists_g1 hGP hℓL)).2.1

lemma g1_val_r (hGP : GeneralPosition L) (hℓL : ℓ ∈ L) :
    (W.g1 hGP hℓL).val (W.r hGP hℓL) = 0 :=
  (Classical.choose_spec (W.exists_g1 hGP hℓL)).2.2

lemma r_mem_g1 (hGP : GeneralPosition L) (hℓL : ℓ ∈ L) :
    W.r hGP hℓL ∈ closure (Cell L W.σ) ∩ (W.g1 hGP hℓL).set :=
  ⟨(W.r_mem_closure hGP hℓL).1, W.g1_val_r hGP hℓL⟩

/-- The edge context of the blue line `g₁`. -/
noncomputable def g1ctx (hGP : GeneralPosition L) (hℓL : ℓ ∈ L) : EdgeCtx L :=
  ⟨W.σ, W.g1 hGP hℓL, hGP, W.hne, W.hbdd, W.g1_mem hGP hℓL,
    ⟨W.r hGP hℓL, W.r_mem_g1 hGP hℓL⟩⟩

@[simp] lemma ectx_σ (hGP : GeneralPosition L) (hℓL : ℓ ∈ L) :
    (W.ectx hGP hℓL).σ = W.σ := rfl

@[simp] lemma ectx_ℓ (hGP : GeneralPosition L) (hℓL : ℓ ∈ L) :
    (W.ectx hGP hℓL).ℓ = ℓ := rfl

@[simp] lemma g1ctx_σ (hGP : GeneralPosition L) (hℓL : ℓ ∈ L) :
    (W.g1ctx hGP hℓL).σ = W.σ := rfl

@[simp] lemma g1ctx_ℓ (hGP : GeneralPosition L) (hℓL : ℓ ∈ L) :
    (W.g1ctx hGP hℓL).ℓ = W.g1 hGP hℓL := rfl

lemma g1_blue (hGP : GeneralPosition L) (hℓL : ℓ ∈ L) : W.g1 hGP hℓL ∈ B := by
  have h := W.hbd (W.g1 hGP hℓL) (W.g1_mem hGP hℓL) ⟨W.r hGP hℓL, W.r_mem_g1 hGP hℓL⟩
  rcases Finset.mem_insert.mp h with h1 | h2
  · exact absurd h1 (W.g1_ne hGP hℓL)
  · exact h2

/-- The parameter of `r` in the parametrization of `g₁`. -/
lemma exists_s_r (hGP : GeneralPosition L) (hℓL : ℓ ∈ L) :
    ∃ s : ℝ, (W.g1 hGP hℓL).param s = W.r hGP hℓL ∧
      s ∈ Set.Icc (W.g1ctx hGP hℓL).Tmin (W.g1ctx hGP hℓL).Tmax := by
  obtain ⟨s, hs⟩ := (W.g1 hGP hℓL).exists_param_of_mem_set (W.g1_val_r hGP hℓL)
  refine ⟨s, hs, ?_⟩
  have hcl := (W.r_mem_closure hGP hℓL).1
  rw [closure_cell W.hne] at hcl
  rw [← hs] at hcl
  rw [← (W.g1ctx hGP hℓL).E_eq_Icc]
  exact hcl

/-- The consistency lemma: `r` is the clockwise-first endpoint of the `g₁`-edge,
i.e. `b` and `r` are two clockwise-consecutive vertices of the region. -/
lemma r_eq_g1_param (hGP : GeneralPosition L) (hℓL : ℓ ∈ L) :
    W.r hGP hℓL = (W.g1 hGP hℓL).param
      (if W.σ (W.g1 hGP hℓL) then (W.g1ctx hGP hℓL).Tmin else (W.g1ctx hGP hℓL).Tmax) := by
  obtain ⟨s, hs, hsI⟩ := W.exists_s_r hGP hℓL
  have hdet : ℓ.det (W.g1 hGP hℓL) ≠ 0 :=
    GP.det_ne hGP hℓL (W.g1_mem hGP hℓL) (Ne.symm (W.g1_ne hGP hℓL))
  have hgval : ∀ t : ℝ, (W.g1 hGP hℓL).val (ℓ.param t) =
      ℓ.det (W.g1 hGP hℓL) * (t - W.rT hGP hℓL) := by
    intro t
    have h1 : (W.g1 hGP hℓL).val (ℓ.param t) =
        ℓ.det (W.g1 hGP hℓL) * t + (W.g1 hGP hℓL).val ℓ.base := Line.val_param_eq _ _ _
    have h2 : (W.g1 hGP hℓL).val (ℓ.param (W.rT hGP hℓL)) = 0 := W.g1_val_r hGP hℓL
    rw [Line.val_param_eq] at h2
    linarith
  -- the sign of `ℓ.det g₁`, read off from the red edge
  have hsign : sgn (W.σ (W.g1 hGP hℓL)) * ℓ.det (W.g1 hGP hℓL) *
      (if W.σ ℓ then (-1 : ℝ) else 1) > 0 := by
    have hcl : ∀ t : ℝ, t ∈ Set.Icc (W.ectx hGP hℓL).Tmin (W.ectx hGP hℓL).Tmax →
        0 ≤ sgn (W.σ (W.g1 hGP hℓL)) * (W.g1 hGP hℓL).val (ℓ.param t) := by
      intro t ht
      have h1 := ((W.ectx hGP hℓL).param_mem_closure_inter ht).1
      simp only [ectx_σ, ectx_ℓ] at h1
      rw [closure_cell W.hne] at h1
      exact h1 (W.g1 hGP hℓL) (W.g1_mem hGP hℓL)
    have hlt : (W.ectx hGP hℓL).Tmin < (W.ectx hGP hℓL).Tmax := (W.ectx hGP hℓL).Tmin_lt_Tmax
    cases hσℓ : W.σ ℓ
    · -- σ ℓ = false: rT = Tmin; sample t = Tmax
      have hrT : W.rT hGP hℓL = (W.ectx hGP hℓL).Tmin := by
        rw [rT, hσℓ]
        simp
      have h1 := hcl ((W.ectx hGP hℓL).Tmax)
        (Set.right_mem_Icc.mpr (W.ectx hGP hℓL).Tmin_le_Tmax)
      rw [hgval, hrT] at h1
      have h2 : (0:ℝ) < (W.ectx hGP hℓL).Tmax - (W.ectx hGP hℓL).Tmin := by linarith
      simp
      rcases eq_or_lt_of_le h1 with hz | h1
      · exfalso
        rcases mul_eq_zero.mp hz.symm with h4 | h4
        · exact sgn_ne_zero _ h4
        · rcases mul_eq_zero.mp h4 with h5 | h5
          · exact hdet h5
          · linarith
      · nlinarith [h1, h2]
    · -- σ ℓ = true: rT = Tmax; sample t = Tmin
      have hrT : W.rT hGP hℓL = (W.ectx hGP hℓL).Tmax := by
        rw [rT, hσℓ]
        simp
      have h1 := hcl ((W.ectx hGP hℓL).Tmin)
        (Set.left_mem_Icc.mpr (W.ectx hGP hℓL).Tmin_le_Tmax)
      rw [hgval, hrT] at h1
      have h2 : (W.ectx hGP hℓL).Tmin - (W.ectx hGP hℓL).Tmax < 0 := by linarith
      simp
      rcases eq_or_lt_of_le h1 with hz | h1
      · exfalso
        rcases mul_eq_zero.mp hz.symm with h4 | h4
        · exact sgn_ne_zero _ h4
        · rcases mul_eq_zero.mp h4 with h5 | h5
          · exact hdet h5
          · linarith
      · nlinarith [h1, h2]
  -- the `ℓ`-constraint on the `g₁`-edge
  have hcon : ∀ u : ℝ, u ∈ Set.Icc (W.g1ctx hGP hℓL).Tmin (W.g1ctx hGP hℓL).Tmax →
      0 ≤ sgn (W.σ ℓ) * ℓ.val ((W.g1 hGP hℓL).param u) := by
    intro u hu
    have h1 := ((W.g1ctx hGP hℓL).param_mem_closure_inter hu).1
    simp only [g1ctx_σ, g1ctx_ℓ] at h1
    rw [closure_cell W.hne] at h1
    exact h1 ℓ hℓL
  have hlval : ∀ u : ℝ, ℓ.val ((W.g1 hGP hℓL).param u) =
      (W.g1 hGP hℓL).det ℓ * (u - s) := by
    intro u
    have h1 : ℓ.val ((W.g1 hGP hℓL).param u) =
        (W.g1 hGP hℓL).det ℓ * u + ℓ.val (W.g1 hGP hℓL).base := Line.val_param_eq _ _ _
    have h2 : ℓ.val ((W.g1 hGP hℓL).param s) = 0 := by
      rw [hs]
      exact (W.r_mem_closure hGP hℓL).2
    rw [Line.val_param_eq] at h2
    linarith
  have hdet2 : (W.g1 hGP hℓL).det ℓ = -ℓ.det (W.g1 hGP hℓL) := Line.det_comm _ _
  have hS : (W.g1ctx hGP hℓL).Tmin < (W.g1ctx hGP hℓL).Tmax := (W.g1ctx hGP hℓL).Tmin_lt_Tmax
  cases hσℓ : W.σ ℓ <;> cases hσg : W.σ (W.g1 hGP hℓL)
  all_goals (
    rw [hσℓ, hσg] at hsign
    simp [sgn] at hsign
    rw [hσℓ] at hcon
    simp only [sgn, hlval, hdet2] at hcon
    simp at hcon
  )
  · -- σ ℓ = false, σ g = false
    have h1 : ∀ u : ℝ, u ∈ Set.Icc (W.g1ctx hGP hℓL).Tmin (W.g1ctx hGP hℓL).Tmax → u ≤ s := by
      intro u hu
      have h2 := hcon u hu.1 hu.2
      nlinarith [hsign]
    have h3 : s ≤ (W.g1ctx hGP hℓL).Tmax := hsI.2
    have h4 : (W.g1ctx hGP hℓL).Tmax ≤ s :=
      h1 _ (Set.right_mem_Icc.mpr (W.g1ctx hGP hℓL).Tmin_le_Tmax)
    have h5 : s = (W.g1ctx hGP hℓL).Tmax := le_antisymm h3 h4
    rw [← hs]
    simp
    rw [h5]
  · -- σ ℓ = false, σ g = true
    have h1 : ∀ u : ℝ, u ∈ Set.Icc (W.g1ctx hGP hℓL).Tmin (W.g1ctx hGP hℓL).Tmax → s ≤ u := by
      intro u hu
      have h2 := hcon u hu.1 hu.2
      nlinarith [hsign]
    have h3 : (W.g1ctx hGP hℓL).Tmin ≤ s := hsI.1
    have h4 : s ≤ (W.g1ctx hGP hℓL).Tmin :=
      h1 _ (Set.left_mem_Icc.mpr (W.g1ctx hGP hℓL).Tmin_le_Tmax)
    have h5 : s = (W.g1ctx hGP hℓL).Tmin := le_antisymm h4 h3
    rw [← hs]
    simp
    rw [h5]
  · -- σ ℓ = true, σ g = false
    have h1 : ∀ u : ℝ, u ∈ Set.Icc (W.g1ctx hGP hℓL).Tmin (W.g1ctx hGP hℓL).Tmax → u ≤ s := by
      intro u hu
      have h2 := hcon u hu.1 hu.2
      nlinarith [hsign]
    have h3 : s ≤ (W.g1ctx hGP hℓL).Tmax := hsI.2
    have h4 : (W.g1ctx hGP hℓL).Tmax ≤ s :=
      h1 _ (Set.right_mem_Icc.mpr (W.g1ctx hGP hℓL).Tmin_le_Tmax)
    have h5 : s = (W.g1ctx hGP hℓL).Tmax := le_antisymm h3 h4
    rw [← hs]
    simp
    rw [h5]
  · -- σ ℓ = true, σ g = true
    have h1 : ∀ u : ℝ, u ∈ Set.Icc (W.g1ctx hGP hℓL).Tmin (W.g1ctx hGP hℓL).Tmax → s ≤ u := by
      intro u hu
      have h2 := hcon u hu.1 hu.2
      nlinarith [hsign]
    have h3 : (W.g1ctx hGP hℓL).Tmin ≤ s := hsI.1
    have h4 : s ≤ (W.g1ctx hGP hℓL).Tmin :=
      h1 _ (Set.left_mem_Icc.mpr (W.g1ctx hGP hℓL).Tmin_le_Tmax)
    have h5 : s = (W.g1ctx hGP hℓL).Tmin := le_antisymm h4 h3
    rw [← hs]
    simp
    rw [h5]

/-- The parameter of the blue point `b` in the parametrization of `g₁`:
the other endpoint of the `g₁`-edge. -/
noncomputable def bT (hGP : GeneralPosition L) (hℓL : ℓ ∈ L) : ℝ :=
  if W.σ (W.g1 hGP hℓL) then (W.g1ctx hGP hℓL).Tmax else (W.g1ctx hGP hℓL).Tmin

/-- The blue point associated to `ℓ`: the next vertex of the region after `r`
in clockwise order. -/
noncomputable def b (hGP : GeneralPosition L) (hℓL : ℓ ∈ L) : ℝ × ℝ :=
  (W.g1 hGP hℓL).param (W.bT hGP hℓL)

lemma bT_mem_Icc (hGP : GeneralPosition L) (hℓL : ℓ ∈ L) :
    W.bT hGP hℓL ∈ Set.Icc (W.g1ctx hGP hℓL).Tmin (W.g1ctx hGP hℓL).Tmax := by
  rw [bT]
  split
  · exact Set.right_mem_Icc.mpr (W.g1ctx hGP hℓL).Tmin_le_Tmax
  · exact Set.left_mem_Icc.mpr (W.g1ctx hGP hℓL).Tmin_le_Tmax

lemma b_mem_closure (hGP : GeneralPosition L) (hℓL : ℓ ∈ L) :
    W.b hGP hℓL ∈ closure (Cell L W.σ) ∩ (W.g1 hGP hℓL).set :=
  (W.g1ctx hGP hℓL).param_mem_closure_inter (W.bT_mem_Icc hGP hℓL)

lemma b_ne_r (hGP : GeneralPosition L) (hℓL : ℓ ∈ L) : W.b hGP hℓL ≠ W.r hGP hℓL := by
  rw [b, W.r_eq_g1_param hGP hℓL]
  intro h
  have hlt : (W.g1ctx hGP hℓL).Tmin < (W.g1ctx hGP hℓL).Tmax := (W.g1ctx hGP hℓL).Tmin_lt_Tmax
  cases hσg : W.σ (W.g1 hGP hℓL)
  · rw [hσg] at h
    simp at h
    have h1 := (W.g1 hGP hℓL).param_injective h
    rw [bT, hσg] at h1
    simp at h1
    linarith
  · rw [hσg] at h
    simp at h
    have h1 := (W.g1 hGP hℓL).param_injective h
    rw [bT, hσg] at h1
    simp at h1
    linarith

/-- The other line through `b` exists. -/
lemma exists_g2 (hGP : GeneralPosition L) (hℓL : ℓ ∈ L) :
    ∃ g ∈ L, g ≠ W.g1 hGP hℓL ∧ g.val (W.b hGP hℓL) = 0 := by
  rw [b, bT]
  split
  · exact (W.g1ctx hGP hℓL).exists_line_at_Tmax
  · exact (W.g1ctx hGP hℓL).exists_line_at_Tmin

/-- The other line through `b` (another blue line). -/
noncomputable def g2 (hGP : GeneralPosition L) (hℓL : ℓ ∈ L) : Line :=
  Classical.choose (W.exists_g2 hGP hℓL)

lemma g2_mem (hGP : GeneralPosition L) (hℓL : ℓ ∈ L) : W.g2 hGP hℓL ∈ L :=
  (Classical.choose_spec (W.exists_g2 hGP hℓL)).1

lemma g2_ne_g1 (hGP : GeneralPosition L) (hℓL : ℓ ∈ L) : W.g2 hGP hℓL ≠ W.g1 hGP hℓL :=
  (Classical.choose_spec (W.exists_g2 hGP hℓL)).2.1

lemma g2_val_b (hGP : GeneralPosition L) (hℓL : ℓ ∈ L) :
    (W.g2 hGP hℓL).val (W.b hGP hℓL) = 0 :=
  (Classical.choose_spec (W.exists_g2 hGP hℓL)).2.2

lemma g2_ne_red (hGP : GeneralPosition L) (hℓL : ℓ ∈ L) : W.g2 hGP hℓL ≠ ℓ := by
  intro h
  have hdet : ℓ.det (W.g1 hGP hℓL) ≠ 0 :=
    GP.det_ne hGP hℓL (W.g1_mem hGP hℓL) (Ne.symm (W.g1_ne hGP hℓL))
  have hbℓ : ℓ.val (W.b hGP hℓL) = 0 := by
    have h2 := W.g2_val_b hGP hℓL
    rw [h] at h2
    exact h2
  have hbg : (W.g1 hGP hℓL).val (W.b hGP hℓL) = 0 := (W.b_mem_closure hGP hℓL).2
  have hrg : (W.g1 hGP hℓL).val (W.r hGP hℓL) = 0 := W.g1_val_r hGP hℓL
  have hrℓ : ℓ.val (W.r hGP hℓL) = 0 := (W.r_mem_closure hGP hℓL).2
  have h1 := Line.eq_interPt hdet hrℓ hrg
  have h2 := Line.eq_interPt hdet hbℓ hbg
  exact (W.b_ne_r hGP hℓL) (h2 ▸ h1 ▸ rfl)

lemma b_mem_g2 (hGP : GeneralPosition L) (hℓL : ℓ ∈ L) :
    W.b hGP hℓL ∈ closure (Cell L W.σ) ∩ (W.g2 hGP hℓL).set :=
  ⟨(W.b_mem_closure hGP hℓL).1, W.g2_val_b hGP hℓL⟩

lemma g2_blue (hGP : GeneralPosition L) (hℓL : ℓ ∈ L) : W.g2 hGP hℓL ∈ B := by
  have h := W.hbd (W.g2 hGP hℓL) (W.g2_mem hGP hℓL) ⟨W.b hGP hℓL, W.b_mem_g2 hGP hℓL⟩
  rcases Finset.mem_insert.mp h with h1 | h2
  · exact absurd h1 (W.g2_ne_red hGP hℓL)
  · exact h2

/-- The two blue lines through `b` are exactly `g₁` and `g₂`. -/
lemma eq_of_val_b_eq_zero (hGP : GeneralPosition L) (hℓL : ℓ ∈ L) {m : Line}
    (hm : m ∈ L) (hmv : m.val (W.b hGP hℓL) = 0) :
    m = W.g1 hGP hℓL ∨ m = W.g2 hGP hℓL :=
  GP.eq_of_val_eq_zero hGP (W.g1_mem hGP hℓL) (W.g2_mem hGP hℓL) hm
    (Ne.symm (W.g2_ne_g1 hGP hℓL)) (W.b_mem_closure hGP hℓL).2 (W.g2_val_b hGP hℓL) hmv

/-- The edge context of the blue line `g₂`. -/
noncomputable def g2ctx (hGP : GeneralPosition L) (hℓL : ℓ ∈ L) : EdgeCtx L :=
  ⟨W.σ, W.g2 hGP hℓL, hGP, W.hne, W.hbdd, W.g2_mem hGP hℓL,
    ⟨W.b hGP hℓL, W.b_mem_g2 hGP hℓL⟩⟩

@[simp] lemma g2ctx_σ (hGP : GeneralPosition L) (hℓL : ℓ ∈ L) :
    (W.g2ctx hGP hℓL).σ = W.σ := rfl

@[simp] lemma g2ctx_ℓ (hGP : GeneralPosition L) (hℓL : ℓ ∈ L) :
    (W.g2ctx hGP hℓL).ℓ = W.g2 hGP hℓL := rfl

/-- The parameter of `r` in the parametrization of `g₁`. -/
noncomputable def s_r (hGP : GeneralPosition L) (hℓL : ℓ ∈ L) : ℝ :=
  if W.σ (W.g1 hGP hℓL) then (W.g1ctx hGP hℓL).Tmin else (W.g1ctx hGP hℓL).Tmax

/-- The parameter of `b` in the parametrization of `g₁`. -/
noncomputable def s_b (hGP : GeneralPosition L) (hℓL : ℓ ∈ L) : ℝ :=
  if W.σ (W.g1 hGP hℓL) then (W.g1ctx hGP hℓL).Tmax else (W.g1ctx hGP hℓL).Tmin

lemma r_eq_param_s_r (hGP : GeneralPosition L) (hℓL : ℓ ∈ L) :
    W.r hGP hℓL = (W.g1 hGP hℓL).param (W.s_r hGP hℓL) :=
  W.r_eq_g1_param hGP hℓL

lemma b_eq_param_s_b (hGP : GeneralPosition L) (hℓL : ℓ ∈ L) :
    W.b hGP hℓL = (W.g1 hGP hℓL).param (W.s_b hGP hℓL) := rfl

lemma s_bT (hGP : GeneralPosition L) (hℓL : ℓ ∈ L) :
    W.s_b hGP hℓL = W.bT hGP hℓL := rfl

lemma s_r_ne_s_b (hGP : GeneralPosition L) (hℓL : ℓ ∈ L) :
    W.s_r hGP hℓL ≠ W.s_b hGP hℓL := by
  have hlt : (W.g1ctx hGP hℓL).Tmin < (W.g1ctx hGP hℓL).Tmax := (W.g1ctx hGP hℓL).Tmin_lt_Tmax
  cases hσg : W.σ (W.g1 hGP hℓL) <;> rw [s_r, s_b, hσg] <;> simp <;> linarith

/-- A parameter strictly between `s_r` and `s_b` lies in the interior of the
`g₁`-edge. -/
lemma mem_Ioo_of_between (hGP : GeneralPosition L) (hℓL : ℓ ∈ L) {t : ℝ}
    (ht : (t - W.s_r hGP hℓL) * (t - W.s_b hGP hℓL) < 0) :
    t ∈ Set.Ioo (W.g1ctx hGP hℓL).Tmin (W.g1ctx hGP hℓL).Tmax := by
  rcases mul_neg_iff.mp ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
  all_goals (
    cases hσg : W.σ (W.g1 hGP hℓL) <;>
      rw [s_r, hσg] at h1 <;> rw [s_b, hσg] at h2 <;> simp at h1 h2 <;>
      simp only [Set.mem_Ioo] <;> constructor <;>
      linarith [(W.g1ctx hGP hℓL).Tmin_lt_Tmax]
  )

/-- The `g₁`-edge contains no crossing of another line in its interior. -/
lemma g1_edge_uncut (hGP : GeneralPosition L) (hℓL : ℓ ∈ L) {m : Line} (hm : m ∈ L)
    (hm1 : m ≠ W.g1 hGP hℓL) {t : ℝ}
    (ht : t ∈ Set.Ioo (W.g1ctx hGP hℓL).Tmin (W.g1ctx hGP hℓL).Tmax) :
    m.val ((W.g1 hGP hℓL).param t) ≠ 0 :=
  (W.g1ctx hGP hℓL).val_ne_zero_of_mem_Ioo hm hm1 ht

/-- The `g₂`-edge contains no crossing of another line in its interior. -/
lemma g2_edge_uncut (hGP : GeneralPosition L) (hℓL : ℓ ∈ L) {m : Line} (hm : m ∈ L)
    (hm2 : m ≠ W.g2 hGP hℓL) {t : ℝ}
    (ht : t ∈ Set.Ioo (W.g2ctx hGP hℓL).Tmin (W.g2ctx hGP hℓL).Tmax) :
    m.val ((W.g2 hGP hℓL).param t) ≠ 0 :=
  (W.g2ctx hGP hℓL).val_ne_zero_of_mem_Ioo hm hm2 ht

end Witness

/-- Two distinct red points associated to the same blue point along the same blue
line must lie on opposite sides of the blue point: on the same side, the nearer
region's side would be crossed by the farther region's red line. -/
lemma opp_sides {L B : Finset Line} (hGP : GeneralPosition L)
    {ℓi ℓj : Line} (Wi : Witness L B ℓi) (Wj : Witness L B ℓj)
    (hiL : ℓi ∈ L) (hjL : ℓj ∈ L) (hiB : ℓi ∉ B) (hjB : ℓj ∉ B)
    (hgq : Wi.g1 hGP hiL = Wj.g1 hGP hjL)
    (hq : Wi.b hGP hiL = Wj.b hGP hjL)
    (hrr : Wi.r hGP hiL ≠ Wj.r hGP hjL) :
    (Wi.s_r hGP hiL - Wi.s_b hGP hiL) * (Wj.s_r hGP hjL - Wi.s_b hGP hiL) < 0 := by
  have hpg : ∀ t : ℝ, (Wj.g1 hGP hjL).param t = (Wi.g1 hGP hiL).param t := fun t => by
    rw [hgq]
  have hb_i := Wi.b_eq_param_s_b hGP hiL
  have hb_j := Wj.b_eq_param_s_b hGP hjL
  have hpeq : (Wi.g1 hGP hiL).param (Wi.s_b hGP hiL) =
      (Wi.g1 hGP hiL).param (Wj.s_b hGP hjL) := by
    calc (Wi.g1 hGP hiL).param (Wi.s_b hGP hiL) = Wi.b hGP hiL := hb_i.symm
      _ = Wj.b hGP hjL := hq
      _ = (Wj.g1 hGP hjL).param (Wj.s_b hGP hjL) := hb_j
      _ = (Wi.g1 hGP hiL).param (Wj.s_b hGP hjL) := hpg _
  have hs : Wi.s_b hGP hiL = Wj.s_b hGP hjL := (Wi.g1 hGP hiL).param_injective hpeq
  have hne1 : Wi.s_r hGP hiL ≠ Wi.s_b hGP hiL := by
    intro h
    have h2 : Wi.r hGP hiL = Wi.b hGP hiL := by
      rw [Wi.r_eq_param_s_r hGP hiL, hb_i, h]
    exact Wi.b_ne_r hGP hiL h2.symm
  have hne2 : Wj.s_r hGP hjL ≠ Wi.s_b hGP hiL := by
    rw [hs]
    intro h
    have h2 : Wj.r hGP hjL = Wj.b hGP hjL := by
      rw [Wj.r_eq_param_s_r hGP hjL, hb_j, h]
    exact Wj.b_ne_r hGP hjL h2.symm
  have hne3 : Wi.s_r hGP hiL ≠ Wj.s_r hGP hjL := by
    intro h
    have h1 : Wi.r hGP hiL = Wj.r hGP hjL := by
      rw [Wi.r_eq_param_s_r hGP hiL, Wj.r_eq_param_s_r hGP hjL, ← hpg, h]
    exact hrr h1
  by_contra hnot
  have hpos : 0 < (Wi.s_r hGP hiL - Wi.s_b hGP hiL) * (Wj.s_r hGP hjL - Wi.s_b hGP hiL) := by
    have h1 : (Wi.s_r hGP hiL - Wi.s_b hGP hiL) * (Wj.s_r hGP hjL - Wi.s_b hGP hiL) ≠ 0 :=
      mul_ne_zero (sub_ne_zero.mpr hne1) (sub_ne_zero.mpr hne2)
    exact lt_of_le_of_ne' (le_of_not_gt hnot) h1
  have hLi : ℓi ≠ Wj.g1 hGP hjL := by
    intro h
    rw [h] at hiB
    exact hiB (Wj.g1_blue hGP hjL)
  have hLj : ℓj ≠ Wi.g1 hGP hiL := by
    intro h
    rw [h] at hjB
    exact hjB (Wi.g1_blue hGP hiL)
  have hvi : ℓi.val ((Wj.g1 hGP hjL).param (Wi.s_r hGP hiL)) = 0 := by
    have e3 := (Wi.r_eq_param_s_r hGP hiL).symm
    have e2 : (Wj.g1 hGP hjL).param (Wi.s_r hGP hiL) = Wi.r hGP hiL := by
      rw [← e3, hgq]
    rw [e2]
    exact (Wi.r_mem_closure hGP hiL).2
  have hvj : ℓj.val ((Wi.g1 hGP hiL).param (Wj.s_r hGP hjL)) = 0 := by
    have e3 := (Wj.r_eq_param_s_r hGP hjL).symm
    have e2 : (Wi.g1 hGP hiL).param (Wj.s_r hGP hjL) = Wj.r hGP hjL := by
      rw [← e3, hgq]
    rw [e2]
    exact (Wj.r_mem_closure hGP hjL).2
  rcases lt_trichotomy (Wi.s_r hGP hiL) (Wj.s_r hGP hjL) with hlt | heq | hgt
  · -- `s_ri < s_rj`
    rcases lt_or_ge (Wi.s_b hGP hiL) (Wi.s_r hGP hiL) with hlt2 | hge2
    · -- `s_b < s_ri < s_rj`: `s_ri` strictly inside `Wⱼ`'s edge
      have hbet : (Wi.s_r hGP hiL - Wj.s_r hGP hjL) * (Wi.s_r hGP hiL - Wj.s_b hGP hjL) < 0 := by
        rw [← hs]
        nlinarith [hpos]
      exact (Wj.g1_edge_uncut hGP hjL hiL hLi (Wj.mem_Ioo_of_between hGP hjL hbet)) hvi
    · -- `s_ri < s_rj < s_b`: `s_rj` strictly inside `Wᵢ`'s edge
      have hsb : Wi.s_b hGP hiL ≠ Wi.s_r hGP hiL := Ne.symm hne1
      have hbet : (Wj.s_r hGP hjL - Wi.s_r hGP hiL) * (Wj.s_r hGP hjL - Wi.s_b hGP hiL) < 0 := by
        nlinarith [hpos]
      exact (Wi.g1_edge_uncut hGP hiL hjL hLj (Wi.mem_Ioo_of_between hGP hiL hbet)) hvj
  · exact absurd heq hne3
  · -- `s_rj < s_ri`
    rcases lt_or_ge (Wi.s_b hGP hiL) (Wj.s_r hGP hjL) with hlt2 | hge2
    · -- `s_b < s_rj < s_ri`: `s_rj` strictly inside `Wᵢ`'s edge
      have hbet : (Wj.s_r hGP hjL - Wi.s_r hGP hiL) * (Wj.s_r hGP hjL - Wi.s_b hGP hiL) < 0 := by
        nlinarith [hpos]
      exact (Wi.g1_edge_uncut hGP hiL hjL hLj (Wi.mem_Ioo_of_between hGP hiL hbet)) hvj
    · -- `s_rj < s_ri < s_b`: `s_ri` strictly inside `Wⱼ`'s edge
      have hbet : (Wi.s_r hGP hiL - Wj.s_r hGP hjL) * (Wi.s_r hGP hiL - Wj.s_b hGP hjL) < 0 := by
        rw [← hs]
        nlinarith [hpos]
      exact (Wj.g1_edge_uncut hGP hjL hiL hLi (Wj.mem_Ioo_of_between hGP hjL hbet)) hvi

/-- The key turning argument: the region of the third red line must turn at `q`
towards one of the two red points, forcing three concurrent lines. -/
lemma turn_at_blue_pt {L B : Finset Line} (hGP : GeneralPosition L)
    {ℓₖ ℓi ℓj : Line} (W : Witness L B ℓₖ) (Wi : Witness L B ℓi) (Wj : Witness L B ℓj)
    (hkL : ℓₖ ∈ L) (hiL : ℓi ∈ L) (hjL : ℓj ∈ L)
    (hkB : ℓₖ ∉ B) (hiB : ℓi ∉ B) (hjB : ℓj ∉ B)
    (hki : ℓₖ ≠ ℓi) (hkj : ℓₖ ≠ ℓj)
    (hgq : Wi.g1 hGP hiL = Wj.g1 hGP hjL)
    (hq : Wi.b hGP hiL = Wj.b hGP hjL)
    (hqW : W.b hGP hkL = Wi.b hGP hiL)
    (hgW : Wi.g1 hGP hiL ≠ W.g1 hGP hkL)
    (hopp : (Wi.s_r hGP hiL - Wi.s_b hGP hiL) * (Wj.s_r hGP hjL - Wi.s_b hGP hiL) < 0) :
    False := by
  set v' := Wi.g1 hGP hiL with hv'
  set q := Wi.b hGP hiL with hqq
  have hv'L : v' ∈ L := Wi.g1_mem hGP hiL
  have hv'B : v' ∈ B := Wi.g1_blue hGP hiL
  have hv'q : v'.val q = 0 := (Wi.b_mem_closure hGP hiL).2
  have hg1q : (W.g1 hGP hkL).val q = 0 := hqW ▸ (W.b_mem_closure hGP hkL).2
  have hg2q : (W.g2 hGP hkL).val q = 0 := hqW ▸ W.g2_val_b hGP hkL
  -- the two lines through `q`: so `v' = W.g₂`
  have hv'qW : v'.val (W.b hGP hkL) = 0 := by rw [hqW]; exact hv'q
  have hqline : v' = W.g1 hGP hkL ∨ v' = W.g2 hGP hkL :=
    W.eq_of_val_b_eq_zero hGP hkL hv'L hv'qW
  have hv'2 : v' = W.g2 hGP hkL := by
    rcases hqline with h | h
    · exact absurd h hgW
    · exact h
  -- `q` on the `g₂`-edge of `W`
  obtain ⟨s, hsq⟩ := v'.exists_param_of_mem_set hv'q
  have hscl : (W.g2ctx hGP hkL).ℓ.param s ∈ closure (Cell L W.σ) := by
    simp only [Witness.g2ctx_ℓ] at hsq ⊢
    rw [← hv'2, hsq, ← hqW]
    exact (W.b_mem_closure hGP hkL).1
  have hsI : s ∈ Set.Icc (W.g2ctx hGP hkL).Tmin (W.g2ctx hGP hkL).Tmax := by
    rw [← (W.g2ctx hGP hkL).E_eq_Icc]
    rw [closure_cell W.hne] at hscl
    exact hscl
  -- `s` must be an endpoint of the `g₂`-edge
  have hdets : (W.g2 hGP hkL).det (W.g1 hGP hkL) ≠ 0 :=
    GP.det_ne hGP (W.g2_mem hGP hkL) (W.g1_mem hGP hkL) (W.g2_ne_g1 hGP hkL)
  have hcon : ∀ u : ℝ, u ∈ Set.Icc (W.g2ctx hGP hkL).Tmin (W.g2ctx hGP hkL).Tmax →
      0 ≤ sgn (W.σ (W.g1 hGP hkL)) * (W.g1 hGP hkL).val ((W.g2 hGP hkL).param u) := by
    intro u hu
    have h1 := ((W.g2ctx hGP hkL).param_mem_closure_inter hu).1
    simp only [Witness.g2ctx_σ, Witness.g2ctx_ℓ] at h1
    rw [closure_cell W.hne] at h1
    exact h1 (W.g1 hGP hkL) (W.g1_mem hGP hkL)
  have hg1val : ∀ u : ℝ, (W.g1 hGP hkL).val ((W.g2 hGP hkL).param u) =
      (W.g2 hGP hkL).det (W.g1 hGP hkL) * (u - s) := by
    intro u
    have h1 : (W.g1 hGP hkL).val ((W.g2 hGP hkL).param u) =
        (W.g2 hGP hkL).det (W.g1 hGP hkL) * u + (W.g1 hGP hkL).val (W.g2 hGP hkL).base :=
      Line.val_param_eq _ _ _
    have h2 : (W.g1 hGP hkL).val ((W.g2 hGP hkL).param s) = 0 := by
      rw [← hv'2, hsq]
      exact hg1q
    rw [Line.val_param_eq] at h2
    linarith
  have hU : (W.g2ctx hGP hkL).Tmin < (W.g2ctx hGP hkL).Tmax := (W.g2ctx hGP hkL).Tmin_lt_Tmax
  have hend : s = (W.g2ctx hGP hkL).Tmin ∨ s = (W.g2ctx hGP hkL).Tmax := by
    rcases eq_or_lt_of_le hsI.1 with h1 | h1
    · exact Or.inl h1.symm
    · rcases eq_or_lt_of_le hsI.2 with h2 | h2
      · exact Or.inr h2
      · exfalso
        have c1 := hcon _ (Set.left_mem_Icc.mpr hU.le)
        have c2 := hcon _ (Set.right_mem_Icc.mpr hU.le)
        rw [hg1val] at c1 c2
        have h3 : sgn (W.σ (W.g1 hGP hkL)) * ((W.g2 hGP hkL).det (W.g1 hGP hkL)) = 0 := by
          nlinarith [c1, c2, h1, h2]
        rcases mul_eq_zero.mp h3 with h4 | h4
        · exact sgn_ne_zero _ h4
        · exact hdets h4
  -- the other endpoint `w` and the line `h` through it
  set w := if s = (W.g2ctx hGP hkL).Tmin then (W.g2ctx hGP hkL).Tmax else (W.g2ctx hGP hkL).Tmin with hw
  have hwne : w ≠ s := by
    rw [hw]
    rcases hend with h5 | h5
    · rw [if_pos h5, h5]
      exact ne_of_gt hU
    · have h6 : ¬ (s = (W.g2ctx hGP hkL).Tmin) := by
        rw [h5]
        exact ne_of_gt hU
      rw [if_neg h6, h5]
      exact ne_of_lt hU
  have hline : ∃ h ∈ L, h ≠ v' ∧ h.val (v'.param w) = 0 := by
    rw [hw]
    rcases hend with h5 | h5
    · rw [if_pos h5]
      have e := (W.g2ctx hGP hkL).exists_line_at_Tmax
      simp only [Witness.g2ctx_ℓ] at e
      rw [← hv'2] at e
      exact e
    · have h6 : ¬ (s = (W.g2ctx hGP hkL).Tmin) := by
        rw [h5]
        exact ne_of_gt hU
      rw [if_neg h6]
      have e := (W.g2ctx hGP hkL).exists_line_at_Tmin
      simp only [Witness.g2ctx_ℓ] at e
      rw [← hv'2] at e
      exact e
  obtain ⟨h, hhL, hhv', hhw⟩ := hline
  -- `w` lies on the same side as one of the two red points
  have hwr : w = Wi.s_r hGP hiL ∨ w = Wj.s_r hGP hjL := by
    have hsb : ∀ {ℓr : Line} (Wr : Witness L B ℓr) (hrL : ℓr ∈ L) (hrB : ℓr ∉ B)
        (hg1r : Wr.g1 hGP hrL = Wi.g1 hGP hiL) (hbr : Wr.b hGP hrL = q),
        Wr.s_b hGP hrL = s := by
      intro ℓr Wr hrL hrB hg1r hbr
      have h1 : v'.param (Wr.s_b hGP hrL) = q := by
        rw [hv', ← hg1r, ← Wr.b_eq_param_s_b hGP hrL]
        exact hbr
      rw [← hsq] at h1
      exact v'.param_injective h1
    -- auxiliary: `w` cannot be on the same side as a red point while distinct from it
    have aux : ∀ {ℓr : Line} (Wr : Witness L B ℓr) (hrL : ℓr ∈ L) (hrB : ℓr ∉ B)
        (hg1r : Wr.g1 hGP hrL = Wi.g1 hGP hiL) (hbr : Wr.b hGP hrL = q)
        (hside : 0 < (Wr.s_r hGP hrL - s) * (w - s)), w = Wr.s_r hGP hrL := by
      intro ℓr Wr hrL hrB hg1r hbr hside
      by_cases hcase : w = Wr.s_r hGP hrL
      · exact hcase
      · exfalso
        -- two contradiction patterns: `h` crossing inside `Wr`'s edge, or
        -- `ℓr` crossing inside `W`'s `g₂`-edge
        have con1 : (w - Wr.s_r hGP hrL) * (w - Wr.s_b hGP hrL) < 0 → False := by
          intro hbet
          have hIoo := Wr.mem_Ioo_of_between hGP hrL hbet
          have hhr : h ≠ Wr.g1 hGP hrL := by
            rw [hg1r]
            exact hhv'
          have huncut := Wr.g1_edge_uncut hGP hrL hhL hhr hIoo
          have hhwv : h.val ((Wr.g1 hGP hrL).param w) = 0 := by
            rw [hg1r]
            exact hhw
          exact huncut hhwv
        have con2 : (Wr.s_r hGP hrL - s) * (Wr.s_r hGP hrL - w) < 0 → False := by
          intro hbet
          have hIoo : Wr.s_r hGP hrL ∈ Set.Ioo (W.g2ctx hGP hkL).Tmin (W.g2ctx hGP hkL).Tmax := by
            rcases hend with h5 | h5
            · rw [hw, if_pos h5] at hbet
              simp only [Set.mem_Ioo]
              constructor <;> nlinarith [hbet]
            · rw [hw, if_neg (by rw [h5]; exact ne_of_gt hU)] at hbet
              simp only [Set.mem_Ioo]
              constructor <;> nlinarith [hbet]
          have hvr : ℓr.val (v'.param (Wr.s_r hGP hrL)) = 0 := by
            rw [hv', ← hg1r, ← Wr.r_eq_param_s_r hGP hrL]
            exact (Wr.r_mem_closure hGP hrL).2
          have hℓr2 : ℓr ≠ W.g2 hGP hkL := by
            rw [← hv'2]
            intro h6
            rw [h6] at hrB
            exact hrB hv'B
          have huncut := W.g2_edge_uncut hGP hkL hrL hℓr2 hIoo
          rw [← hv'2] at huncut
          exact huncut hvr
        rcases mul_pos_iff.mp hside with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · -- `s < s_r` and `s < w`, both on the positive side of `s`
          rcases lt_or_gt_of_ne hcase with hlt | hgt
          · -- `s < w < s_r`
            exact con1 (by rw [hsb Wr hrL hrB hg1r hbr]; nlinarith)
          · -- `s < s_r < w`
            exact con2 (by nlinarith)
        · -- `s_r < s` and `w < s`, both on the negative side of `s`
          rcases lt_or_gt_of_ne hcase with hlt | hgt
          · -- `w < s_r < s`
            exact con2 (by nlinarith)
          · -- `s_r < w < s`
            exact con1 (by rw [hsb Wr hrL hrB hg1r hbr]; nlinarith)
    have hsb1 : Wi.s_b hGP hiL = s := hsb Wi hiL hiB rfl rfl
    have hsri : (Wi.s_r hGP hiL - s) * (Wj.s_r hGP hjL - s) < 0 := hsb1 ▸ hopp
    have hws : (w - s) ≠ 0 := sub_ne_zero.mpr hwne
    -- `w` is on one of the two sides; matching side forces equality
    by_cases hc : 0 < (Wi.s_r hGP hiL - s) * (w - s)
    · exact Or.inl (aux Wi hiL hiB rfl rfl hc)
    · by_cases hc2 : 0 < (Wj.s_r hGP hjL - s) * (w - s)
      · exact Or.inr (aux Wj hjL hjB hgq.symm hq.symm hc2)
      · exfalso
        rcases mul_neg_iff.mp hsri with ⟨hpi, hnj⟩ | ⟨hni, hpj⟩
        · have hws' : w - s ≤ 0 := by
            by_contra h3
            exact hc (mul_pos hpi (not_le.mp h3))
          have hws'' : w - s < 0 := lt_of_le_of_ne' hws' hws.symm
          exact hc2 (mul_pos_of_neg_of_neg hnj hws'')
        · have hws' : w - s ≤ 0 := by
            by_contra h3
            exact hc2 (mul_pos hpj (not_le.mp h3))
          have hws'' : w - s < 0 := lt_of_le_of_ne' hws' hws.symm
          exact hc (mul_pos_of_neg_of_neg hni hws'')
  -- the line `h` at `w` passes through a red point: three concurrent lines
  have hbdr : (closure (Cell L W.σ) ∩ h.set).Nonempty := by
    have hmem : v'.param w ∈ closure (Cell L W.σ) := by
      have hmemI : w ∈ Set.Icc (W.g2ctx hGP hkL).Tmin (W.g2ctx hGP hkL).Tmax := by
        rw [hw]
        split
        · exact Set.right_mem_Icc.mpr hU.le
        · exact Set.left_mem_Icc.mpr hU.le
      have h1 := ((W.g2ctx hGP hkL).param_mem_closure_inter hmemI).1
      simp only [Witness.g2ctx_σ, Witness.g2ctx_ℓ] at h1
      rw [hv'2]
      exact h1
    exact ⟨v'.param w, hmem, hhw⟩
  have hins := W.hbd h hhL hbdr
  rcases hwr with hwr | hwr
  · -- `w = s_ri`: red point `rᵢ`
    have hri : v'.param (Wi.s_r hGP hiL) = Wi.r hGP hiL := (Wi.r_eq_param_s_r hGP hiL).symm
    have hhri : h.val (Wi.r hGP hiL) = 0 := by
      rw [← hri, ← hwr]
      exact hhw
    have hℓri : ℓi.val (Wi.r hGP hiL) = 0 := (Wi.r_mem_closure hGP hiL).2
    have hv'ri : v'.val (Wi.r hGP hiL) = 0 := by
      rw [← hri]
      exact Line.val_param _ _
    rcases Finset.mem_insert.mp hins with h1 | h1
    · -- `h = ℓₖ`
      rw [h1] at hhri
      have hv'ℓi : v' ≠ ℓi := by
        intro h2
        rw [h2] at hv'B
        exact hiB hv'B
      have hℓₖv' : ℓₖ ≠ v' := by
        intro h2
        rw [← h2] at hv'B
        exact hkB hv'B
      exact GP.not_concurrent hGP hkL hiL hv'L hki hℓₖv' (Ne.symm hv'ℓi) hhri hℓri hv'ri
    · -- `h ∈ B`
      have hhℓi : h ≠ ℓi := by
        intro h2
        rw [h2] at h1
        exact hiB h1
      have hv'ℓi : v' ≠ ℓi := by
        intro h2
        rw [h2] at hv'B
        exact hiB hv'B
      exact GP.not_concurrent hGP hhL hv'L hiL hhv' hhℓi hv'ℓi hhri hv'ri hℓri
  · -- symmetric with `rⱼ`
    have hrj : (Wi.g1 hGP hiL).param (Wj.s_r hGP hjL) = Wj.r hGP hjL := by
      have e1 := (Wj.r_eq_param_s_r hGP hjL).symm
      rw [← e1, ← hv', hgq]
    have hhrj : h.val (Wj.r hGP hjL) = 0 := by
      rw [← hrj, ← hwr]
      exact hhw
    have hℓrj : ℓj.val (Wj.r hGP hjL) = 0 := (Wj.r_mem_closure hGP hjL).2
    have hv'rj : v'.val (Wj.r hGP hjL) = 0 := by
      rw [← hrj]
      exact Line.val_param _ _
    rcases Finset.mem_insert.mp hins with h1 | h1
    · rw [h1] at hhrj
      have hv'ℓj : v' ≠ ℓj := by
        intro h2
        rw [h2] at hv'B
        exact hjB hv'B
      have hℓₖv' : ℓₖ ≠ v' := by
        intro h2
        rw [← h2] at hv'B
        exact hkB hv'B
      exact GP.not_concurrent hGP hkL hjL hv'L hkj hℓₖv' (Ne.symm hv'ℓj) hhrj hℓrj hv'rj
    · have hhℓj : h ≠ ℓj := by
        intro h2
        rw [h2] at h1
        exact hjB h1
      have hv'ℓj : v' ≠ ℓj := by
        intro h2
        rw [h2] at hv'B
        exact hjB hv'B
      exact GP.not_concurrent hGP hhL hv'L hjL hhv' hhℓj hv'ℓj hhrj hv'rj hℓrj

/-- Two distinct points determine a line (in general position). -/
lemma Line.eq_of_two_mem {L : Finset Line} (hGP : GeneralPosition L) {g g' : Line}
    (hg : g ∈ L) (hg' : g' ∈ L) {p q : ℝ × ℝ} (hpq : p ≠ q)
    (hgp : g.val p = 0) (hgq : g.val q = 0) (hg'p : g'.val p = 0) (hg'q : g'.val q = 0) :
    g = g' := by
  by_contra h
  have hd := GP.det_ne hGP hg hg' h
  have h1 := Line.eq_interPt hd hgp hg'p
  have h2 := Line.eq_interPt hd hgq hg'q
  exact hpq (h1.trans h2.symm)

lemma Line.interPt_comm {ℓ m : Line} (h : ℓ.det m ≠ 0) : ℓ.interPt m = m.interPt ℓ := by
  have h' : m.det ℓ ≠ 0 := by
    rw [Line.det_comm]
    exact neg_ne_zero.mpr h
  exact (Line.eq_interPt h (Line.val_interPt_right h') (Line.val_interPt_left h')).symm

/-- The association map from red lines to blue points, for a choice of witnesses. -/
noncomputable def assocB (L B : Finset Line) (W : ∀ m ∈ L \ B, Witness L B m)
    (hGP : GeneralPosition L) (ℓ : Line) : ℝ × ℝ :=
  if h : ℓ ∈ L \ B then (W ℓ h).b hGP ((Finset.mem_sdiff.mp h).1) else (0, 0)

namespace Witness

/-- On the same blue line through the same blue point, the parameter of `b`
is the same for two witnesses. -/
lemma s_b_eq_s_b {L B : Finset Line} (hGP : GeneralPosition L)
    {ℓi ℓj : Line} (Wi : Witness L B ℓi) (Wj : Witness L B ℓj)
    (hiL : ℓi ∈ L) (hjL : ℓj ∈ L)
    (hgq : Wi.g1 hGP hiL = Wj.g1 hGP hjL)
    (hq : Wi.b hGP hiL = Wj.b hGP hjL) :
    Wi.s_b hGP hiL = Wj.s_b hGP hjL := by
  have hpg : ∀ t : ℝ, (Wj.g1 hGP hjL).param t = (Wi.g1 hGP hiL).param t := fun t => by
    rw [hgq]
  have hb_i := Wi.b_eq_param_s_b hGP hiL
  have hb_j := Wj.b_eq_param_s_b hGP hjL
  have hpeq : (Wi.g1 hGP hiL).param (Wi.s_b hGP hiL) =
      (Wi.g1 hGP hiL).param (Wj.s_b hGP hjL) := by
    calc (Wi.g1 hGP hiL).param (Wi.s_b hGP hiL) = Wi.b hGP hiL := hb_i.symm
      _ = Wj.b hGP hjL := hq
      _ = (Wj.g1 hGP hjL).param (Wj.s_b hGP hjL) := hb_j
      _ = (Wi.g1 hGP hiL).param (Wj.s_b hGP hjL) := hpg _
  exact (Wi.g1 hGP hiL).param_injective hpeq

end Witness

/-- The key counting lemma: at most two red lines are associated to the same
blue point. -/
lemma fiber_card_le_two (L B : Finset Line) (W : ∀ m ∈ L \ B, Witness L B m)
    (hGP : GeneralPosition L) (q : ℝ × ℝ) :
    ((L \ B).filter fun ℓ => assocB L B W hGP ℓ = q).card ≤ 2 := by
  by_contra h
  have h3 : 2 < ((L \ B).filter fun ℓ => assocB L B W hGP ℓ = q).card := Nat.lt_of_not_le h
  set S := (L \ B).filter (fun ℓ => assocB L B W hGP ℓ = q) with hS
  obtain ⟨ℓ₁, h1⟩ : S.Nonempty := Finset.card_pos.mp (by omega : 0 < S.card)
  have hS1 : 1 < (S.erase ℓ₁).card := by
    rw [Finset.card_erase_of_mem h1]
    omega
  obtain ⟨ℓ₂, h2, ℓ₃, h3', h23⟩ := Finset.one_lt_card.mp hS1
  rw [Finset.mem_erase] at h2 h3'
  obtain ⟨d21, h2S⟩ := h2
  obtain ⟨d31, h3S⟩ := h3'
  have d12 : ℓ₁ ≠ ℓ₂ := Ne.symm d21
  have d13 : ℓ₁ ≠ ℓ₃ := Ne.symm d31
  rw [hS, Finset.mem_filter] at h1 h2S h3S
  obtain ⟨h1L, hq1⟩ := h1
  obtain ⟨h2L, hq2⟩ := h2S
  obtain ⟨h3L, hq3⟩ := h3S
  rw [assocB, dif_pos h1L] at hq1
  rw [assocB, dif_pos h2L] at hq2
  rw [assocB, dif_pos h3L] at hq3
  have h1L' := (Finset.mem_sdiff.mp h1L).1
  have h2L' := (Finset.mem_sdiff.mp h2L).1
  have h3L' := (Finset.mem_sdiff.mp h3L).1
  have h1B := (Finset.mem_sdiff.mp h1L).2
  have h2B := (Finset.mem_sdiff.mp h2L).2
  have h3B := (Finset.mem_sdiff.mp h3L).2
  -- shorthand for the three witnesses
  set W₁ := W ℓ₁ h1L with hW₁
  set W₂ := W ℓ₂ h2L with hW₂
  set W₃ := W ℓ₃ h3L with hW₃
  -- basic facts about each line
  have h1g1q : (W₁.g1 hGP h1L').val q = 0 := hq1 ▸ (W₁.b_mem_closure hGP h1L').2
  have h1g2q : (W₁.g2 hGP h1L').val q = 0 := hq1 ▸ W₁.g2_val_b hGP h1L'
  have h2g1q : (W₂.g1 hGP h2L').val q = 0 := hq2 ▸ (W₂.b_mem_closure hGP h2L').2
  have h3g1q : (W₃.g1 hGP h3L').val q = 0 := hq3 ▸ (W₃.b_mem_closure hGP h3L').2
  have h1rq : W₁.r hGP h1L' ≠ q := by
    have h := W₁.b_ne_r hGP h1L'
    rw [hq1] at h
    exact h.symm
  have h2rq : W₂.r hGP h2L' ≠ q := by
    have h := W₂.b_ne_r hGP h2L'
    rw [hq2] at h
    exact h.symm
  have h3rq : W₃.r hGP h3L' ≠ q := by
    have h := W₃.b_ne_r hGP h3L'
    rw [hq3] at h
    exact h.symm
  -- the red points are pairwise distinct
  have rdist : ∀ {ℓi ℓj : Line} (hiL : ℓi ∈ L \ B) (hjL : ℓj ∈ L \ B)
      (hqi : (W ℓi hiL).b hGP ((Finset.mem_sdiff.mp hiL).1) = q)
      (hqj : (W ℓj hjL).b hGP ((Finset.mem_sdiff.mp hjL).1) = q)
      (hij : ℓi ≠ ℓj),
      (W ℓi hiL).r hGP ((Finset.mem_sdiff.mp hiL).1) ≠
        (W ℓj hjL).r hGP ((Finset.mem_sdiff.mp hjL).1) := by
    intro ℓi ℓj hiL hjL hqi hqj hij hr
    have hiL' := (Finset.mem_sdiff.mp hiL).1
    have hjL' := (Finset.mem_sdiff.mp hjL).1
    have hiB := (Finset.mem_sdiff.mp hiL).2
    have hjB := (Finset.mem_sdiff.mp hjL).2
    have hriq : (W ℓi hiL).r hGP hiL' ≠ q := by
      have h := (W ℓi hiL).b_ne_r hGP hiL'
      rw [hqi] at h
      exact h.symm
    have hg : (W ℓi hiL).g1 hGP hiL' = (W ℓj hjL).g1 hGP hjL' := by
      apply Line.eq_of_two_mem hGP ((W ℓi hiL).g1_mem hGP hiL') ((W ℓj hjL).g1_mem hGP hjL')
        hriq ((W ℓi hiL).g1_val_r hGP hiL') (hqi ▸ (W ℓi hiL).b_mem_closure hGP hiL' |>.2)
      · rw [hr]
        exact (W ℓj hjL).g1_val_r hGP hjL'
      · exact hqj ▸ (W ℓj hjL).b_mem_closure hGP hjL' |>.2
    have h3lines : (W ℓi hiL).g1 hGP hiL' = ℓi ∨ (W ℓi hiL).g1 hGP hiL' = ℓj :=
      GP.eq_of_val_eq_zero hGP hiL' hjL' ((W ℓi hiL).g1_mem hGP hiL') hij
        ((W ℓi hiL).r_mem_closure hGP hiL').2
        (by rw [hr]; exact (W ℓj hjL).r_mem_closure hGP hjL' |>.2)
        ((W ℓi hiL).g1_val_r hGP hiL')
    rcases h3lines with h4 | h4
    · rw [← h4] at hiB
      exact hiB ((W ℓi hiL).g1_blue hGP hiL')
    · rw [← h4] at hjB
      exact hjB ((W ℓi hiL).g1_blue hGP hiL')
  have rd12 : W₁.r hGP h1L' ≠ W₂.r hGP h2L' := rdist h1L h2L hq1 hq2 d12
  have rd13 : W₁.r hGP h1L' ≠ W₃.r hGP h3L' := rdist h1L h3L hq1 hq3 d13
  have rd23 : W₂.r hGP h2L' ≠ W₃.r hGP h3L' := rdist h2L h3L hq2 hq3 h23
  -- the two blue lines through `q`
  have qlines : ∀ m ∈ L, m.val q = 0 → m = W₁.g1 hGP h1L' ∨ m = W₁.g2 hGP h1L' := by
    intro m hmL hmq
    have hm' : m.val (W₁.b hGP h1L') = 0 := by
      rw [hq1]
      exact hmq
    exact W₁.eq_of_val_b_eq_zero hGP h1L' hmL hm'
  have g1_2 : W₂.g1 hGP h2L' = W₁.g1 hGP h1L' ∨ W₂.g1 hGP h2L' = W₁.g2 hGP h1L' :=
    qlines (W₂.g1 hGP h2L') (W₂.g1_mem hGP h2L') h2g1q
  have g1_3 : W₃.g1 hGP h3L' = W₁.g1 hGP h1L' ∨ W₃.g1 hGP h3L' = W₁.g2 hGP h1L' :=
    qlines (W₃.g1 hGP h3L') (W₃.g1_mem hGP h3L') h3g1q
  have hg2ne : W₁.g2 hGP h1L' ≠ W₁.g1 hGP h1L' := W₁.g2_ne_g1 hGP h1L'
  -- helper: opposite sides for a pair
  have opp : ∀ {ℓi ℓj : Line} (hiL : ℓi ∈ L \ B) (hjL : ℓj ∈ L \ B)
      (hqi : (W ℓi hiL).b hGP ((Finset.mem_sdiff.mp hiL).1) = q)
      (hqj : (W ℓj hjL).b hGP ((Finset.mem_sdiff.mp hjL).1) = q)
      (hg : (W ℓi hiL).g1 hGP ((Finset.mem_sdiff.mp hiL).1) =
        (W ℓj hjL).g1 hGP ((Finset.mem_sdiff.mp hjL).1))
      (hrr : (W ℓi hiL).r hGP ((Finset.mem_sdiff.mp hiL).1) ≠
        (W ℓj hjL).r hGP ((Finset.mem_sdiff.mp hjL).1)),
      ((W ℓi hiL).s_r hGP ((Finset.mem_sdiff.mp hiL).1) -
        (W ℓi hiL).s_b hGP ((Finset.mem_sdiff.mp hiL).1)) *
      ((W ℓj hjL).s_r hGP ((Finset.mem_sdiff.mp hjL).1) -
        (W ℓi hiL).s_b hGP ((Finset.mem_sdiff.mp hiL).1)) < 0 := by
    intro ℓi ℓj hiL hjL hqi hqj hg hrr
    have hiL' := (Finset.mem_sdiff.mp hiL).1
    have hjL' := (Finset.mem_sdiff.mp hjL).1
    have hiB := (Finset.mem_sdiff.mp hiL).2
    have hjB := (Finset.mem_sdiff.mp hjL).2
    exact opp_sides hGP (W ℓi hiL) (W ℓj hjL) hiL' hjL' hiB hjB hg (hqi.trans hqj.symm) hrr
  rcases g1_2 with g12 | g12 <;> rcases g1_3 with g13 | g13
  · -- all three `g₁` equal: pairwise opposite sides, impossible
    exfalso
    have o12 := opp h1L h2L hq1 hq2 g12.symm rd12
    have o13 := opp h1L h3L hq1 hq3 g13.symm rd13
    have o23 := opp h2L h3L hq2 hq3 (g12.trans g13.symm) rd23
    have hs2 : W₂.s_b hGP h2L' = W₁.s_b hGP h1L' :=
      (Witness.s_b_eq_s_b hGP W₁ W₂ h1L' h2L' g12.symm (hq1.trans hq2.symm)).symm
    rw [hs2] at o23
    have ha : W₁.s_r hGP h1L' - W₁.s_b hGP h1L' ≠ 0 := by
      intro hz
      rw [hz, zero_mul] at o12
      exact (lt_irrefl 0) o12
    nlinarith [o12, o13, o23, sq_pos_of_ne_zero ha]
  · -- pair (1,2) on `W₁.g₁`, third `ℓ₃` on `W₁.g₂`
    have hgW : W₁.g1 hGP h1L' ≠ W₃.g1 hGP h3L' := by
      intro h
      rw [g13] at h
      exact hg2ne h.symm
    have o12 := opp h1L h2L hq1 hq2 g12.symm rd12
    exact turn_at_blue_pt hGP W₃ W₁ W₂ h3L' h1L' h2L' h3B h1B h2B d31 h23.symm
      g12.symm (hq1.trans hq2.symm) (hq3.trans hq1.symm) hgW o12
  · -- pair (1,3) on `W₁.g₁`, third `ℓ₂` on `W₁.g₂`
    have hgW : W₁.g1 hGP h1L' ≠ W₂.g1 hGP h2L' := by
      intro h
      rw [g12] at h
      exact hg2ne h.symm
    have o13 := opp h1L h3L hq1 hq3 g13.symm rd13
    exact turn_at_blue_pt hGP W₂ W₁ W₃ h2L' h1L' h3L' h2B h1B h3B d21 h23
      g13.symm (hq1.trans hq3.symm) (hq2.trans hq1.symm) hgW o13
  · -- pair (2,3) on `W₁.g₂`, third `ℓ₁` on `W₁.g₁`
    have hgW : W₂.g1 hGP h2L' ≠ W₁.g1 hGP h1L' := by
      intro h
      rw [g12] at h
      exact hg2ne h
    have o23 := opp h2L h3L hq2 hq3 (g12.trans g13.symm) rd23
    exact turn_at_blue_pt hGP W₁ W₂ W₃ h1L' h2L' h3L' h1B h2B h3B d12 d13
      (g12.trans g13.symm) (hq2.trans hq3.symm) (hq1.trans hq2.symm) hgW o23

/-! ### Maximal valid blue sets and the final count -/

/-- Every bounded nonempty cell has a boundary line: follow a ray from an
interior point; since the cell is bounded, some constraint must stop the ray. -/
lemma exists_boundary_line {L : Finset Line} {σ : Line → Bool} (hne : (Cell L σ).Nonempty)
    (hbdd : Bornology.IsBounded (Cell L σ)) :
    ∃ m ∈ L, (closure (Cell L σ) ∩ m.set).Nonempty := by
  obtain ⟨q, hq⟩ := hne
  obtain ⟨r, hr⟩ := Bornology.IsBounded.subset_closedBall hbdd.closure q
  have hval : ∀ m : Line, ∀ t : ℝ, m.val (q + t • ((1, 0) : ℝ × ℝ)) = m.val q + t * m.a := by
    intro m t
    simp [Line.val, smul_eq_mul]
    ring
  set U := L.filter fun m => sgn (σ m) * m.a < 0 with hU
  by_cases hUe : U.Nonempty
  · set bd := fun m : Line => -(sgn (σ m) * m.val q) / (sgn (σ m) * m.a) with hbd
    set b := (U.image bd).min' (by simp [hUe]) with hb
    have hbm := (U.image bd).min'_mem (by simp [hUe])
    simp only [Finset.mem_image] at hbm
    obtain ⟨m₀, hm₀, hm₀b⟩ := hbm
    have hm₀U := Finset.mem_filter.mp hm₀
    have hb2 : b = -(sgn (σ m₀) * m₀.val q) / (sgn (σ m₀) * m₀.a) := by
      rw [hb, ← hm₀b, hbd]
    have hb0 : 0 ≤ b := by
      rw [hb2]
      have h1 : 0 < sgn (σ m₀) * m₀.val q := hq m₀ hm₀U.1
      have h2 : sgn (σ m₀) * m₀.a < 0 := hm₀U.2
      exact le_of_lt (div_pos_of_neg_of_neg (by linarith) h2)
    have hcl : ∀ m ∈ L, 0 ≤ sgn (σ m) * m.val (q + b • ((1, 0) : ℝ × ℝ)) := by
      intro m hm
      rw [hval]
      by_cases hma : 0 ≤ sgn (σ m) * m.a
      · have h1 : 0 < sgn (σ m) * m.val q := hq m hm
        nlinarith [mul_nonneg hb0 hma]
      · have hmU : m ∈ U := Finset.mem_filter.mpr ⟨hm, lt_of_not_ge hma⟩
        have hle : b ≤ bd m := Finset.min'_le _ _ (Finset.mem_image_of_mem _ hmU)
        have h2 : sgn (σ m) * m.a < 0 := lt_of_not_ge hma
        have h3 : 0 < sgn (σ m) * m.val q := hq m hm
        have h4 : b * (sgn (σ m) * m.a) ≥ bd m * (sgn (σ m) * m.a) :=
          mul_le_mul_of_nonpos_right hle h2.le
        have h5 : bd m * (sgn (σ m) * m.a) = -(sgn (σ m) * m.val q) := by
          rw [hbd]
          exact div_mul_cancel₀ _ (ne_of_lt h2)
        have h6 : sgn (σ m) * (m.val q + b * m.a) =
            sgn (σ m) * m.val q + b * (sgn (σ m) * m.a) := by ring
        rw [h6]
        linarith [h4, h5, h3]
    refine ⟨m₀, hm₀U.1, q + b • ((1, 0) : ℝ × ℝ), ?_, ?_⟩
    · rw [closure_cell ⟨q, hq⟩]
      exact hcl
    · have h2 : sgn (σ m₀) * m₀.a ≠ 0 := ne_of_lt hm₀U.2
      have h3 : sgn (σ m₀) * m₀.val (q + b • ((1, 0) : ℝ × ℝ)) = 0 := by
        rw [hval]
        have h4 : sgn (σ m₀) * m₀.val q + b * (sgn (σ m₀) * m₀.a) = 0 := by
          rw [hb2, div_mul_cancel₀ _ h2, add_neg_cancel]
        have h5 : sgn (σ m₀) * (m₀.val q + b * m₀.a) =
            sgn (σ m₀) * m₀.val q + b * (sgn (σ m₀) * m₀.a) := by ring
        rw [h5, h4]
      exact (mul_eq_zero.mp h3).resolve_left (sgn_ne_zero _)
  · rw [Finset.not_nonempty_iff_eq_empty] at hUe
    have hcl : ∀ t : ℝ, 0 ≤ t → q + t • ((1, 0) : ℝ × ℝ) ∈ closure (Cell L σ) := by
      intro t ht
      rw [closure_cell ⟨q, hq⟩]
      intro m hm
      rw [hval]
      have h1 : 0 < sgn (σ m) * m.val q := hq m hm
      have h2 : 0 ≤ sgn (σ m) * m.a := by
        by_contra h3
        have h4 : m ∈ U := Finset.mem_filter.mpr ⟨hm, lt_of_not_ge h3⟩
        rw [hUe] at h4
        simp at h4
      nlinarith [mul_nonneg ht h2]
    have h1 := hcl (|r| + 1) (by positivity)
    have h2 : dist (q + (|r| + 1) • ((1, 0) : ℝ × ℝ)) q ≤ r := hr h1
    have h3 : dist (q + (|r| + 1) • ((1, 0) : ℝ × ℝ)) q = |r| + 1 := by
      rw [dist_eq_norm]
      have h4 : q + (|r| + 1) • ((1, 0) : ℝ × ℝ) - q = (|r| + 1) • ((1, 0) : ℝ × ℝ) := by
        module
      rw [h4, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : (0:ℝ) < |r| + 1)]
      have h5 : ‖((1, 0) : ℝ × ℝ)‖ = 1 := by
        rw [Prod.norm_def]
        simp
      rw [h5, mul_one]
    linarith [h2, h3, le_abs_self r]

/-- The empty blue set is valid. -/
lemma validBlue_empty (L : Finset Line) : ValidBlue L ∅ := by
  intro σ hne hbdd
  obtain ⟨m, hmL, hmb⟩ := exists_boundary_line hne hbdd
  exact ⟨m, hmL, hmb, by simp⟩

/-- A maximal valid blue set exists. -/
lemma exists_maximal_valid (L : Finset Line) :
    ∃ B ⊆ L, ValidBlue L B ∧ ∀ m ∈ L, m ∉ B → ¬ ValidBlue L (insert m B) := by
  classical
  have hne : (L.powerset.filter (ValidBlue L)).Nonempty :=
    ⟨∅, Finset.mem_filter.mpr ⟨Finset.empty_mem_powerset L, validBlue_empty L⟩⟩
  have hne' : ((L.powerset.filter (ValidBlue L)).image Finset.card).Nonempty :=
    Finset.image_nonempty.mpr hne
  set K := ((L.powerset.filter (ValidBlue L)).image Finset.card).max' hne' with hK
  have hKm := Finset.max'_mem _ hne'
  simp only [Finset.mem_image, Finset.mem_filter] at hKm
  obtain ⟨B, ⟨hBL, hBV⟩, hBK⟩ := hKm
  have hBL' : B ⊆ L := Finset.mem_powerset.mp hBL
  refine ⟨B, hBL', hBV, fun m hmL hmB hMV => ?_⟩
  have hm : insert m B ∈ L.powerset.filter (ValidBlue L) := by
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_powerset.mpr (Finset.insert_subset hmL (Finset.mem_powerset.mp hBL)), hMV⟩
  have hcard : (insert m B).card ≤ K := Finset.le_max' _ _ (Finset.mem_image_of_mem _ hm)
  rw [hK, ← hBK] at hcard
  have hgt : B.card < (insert m B).card := Finset.card_lt_card (Finset.ssubset_insert hmB)
  omega

/-- Every red line has a witness region. -/
lemma exists_witness (L : Finset Line) {B : Finset Line} (hBV : ValidBlue L B)
    (hmax : ∀ m ∈ L, m ∉ B → ¬ ValidBlue L (insert m B))
    {ℓ : Line} (hℓL : ℓ ∈ L) (hℓB : ℓ ∉ B) : Nonempty (Witness L B ℓ) := by
  have h1 := hmax ℓ hℓL hℓB
  have h2 : ∃ σ : Line → Bool, (Cell L σ).Nonempty ∧ Bornology.IsBounded (Cell L σ) ∧
      ∀ m ∈ L, (closure (Cell L σ) ∩ m.set).Nonempty → m ∈ insert ℓ B := by
    by_contra hc
    have h3 : ValidBlue L (insert ℓ B) := by
      intro σ hne' hbdd'
      by_contra hc2
      apply hc
      refine ⟨σ, hne', hbdd', fun m hmL hmB => ?_⟩
      by_contra hmB2
      exact hc2 ⟨m, hmL, hmB, hmB2⟩
    exact h1 h3
  obtain ⟨σ, hne', hbdd', hbd⟩ := h2
  obtain ⟨m, hmL, hmb, hmB⟩ := hBV σ hne' hbdd'
  have hm : m ∈ insert ℓ B := hbd m hmL hmb
  have hℓb : (closure (Cell L σ) ∩ ℓ.set).Nonempty := by
    rcases Finset.mem_insert.mp hm with h | h
    · rw [← h]
      exact hmb
    · exact absurd h hmB
  exact ⟨σ, hne', hbdd', hbd, hℓb⟩

/-- The choice of a witness region for every red line. -/
noncomputable def redWitness (L : Finset Line) {B : Finset Line} (hBV : ValidBlue L B)
    (hmax : ∀ m ∈ L, m ∉ B → ¬ ValidBlue L (insert m B))
    {m : Line} (hm : m ∈ L \ B) : Witness L B m :=
  Classical.choice (exists_witness L hBV hmax (Finset.mem_sdiff.mp hm).1 (Finset.mem_sdiff.mp hm).2)

/-- The blue points: the intersection points of pairs of distinct blue lines. -/
noncomputable def bluePts (B : Finset Line) : Finset (ℝ × ℝ) :=
  B.offDiag.image fun gg => gg.1.interPt gg.2

/-- Each blue point has at least two preimages among the ordered pairs of blue lines. -/
lemma two_mul_card_bluePts {L : Finset Line} {B : Finset Line}
    (hGP : GeneralPosition L) (hBL : B ⊆ L) :
    2 * (bluePts B).card ≤ B.card * B.card - B.card := by
  rw [← Finset.offDiag_card]
  rw [bluePts]
  apply Finset.mul_card_image_le_card
  intro p hp
  simp only [Finset.mem_image] at hp
  obtain ⟨gg, hgg, rfl⟩ := hp
  rw [Finset.mem_offDiag] at hgg
  obtain ⟨hg1, hg2, hgg12⟩ := hgg
  have hgg' : gg ∈ B.offDiag := Finset.mem_offDiag.mpr ⟨hg1, hg2, hgg12⟩
  have hmem1 : gg ∈ B.offDiag.filter (fun a => a.1.interPt a.2 = gg.1.interPt gg.2) :=
    Finset.mem_filter.mpr ⟨hgg', rfl⟩
  have hmem2 : (gg.2, gg.1) ∈ B.offDiag.filter (fun a => a.1.interPt a.2 = gg.1.interPt gg.2) := by
    rw [Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · rw [Finset.mem_offDiag]
      exact ⟨hg2, hg1, Ne.symm hgg12⟩
    · exact Line.interPt_comm (GP.det_ne hGP (hBL hg2) (hBL hg1) (Ne.symm hgg12))
  have hne2 : gg ≠ (gg.2, gg.1) := by
    intro h
    have h1 : gg.1 = gg.2 := (Prod.ext_iff.mp h).1
    exact hgg12 h1
  have hsub : ({gg, (gg.2, gg.1)} : Finset (Line × Line)) ⊆
      B.offDiag.filter (fun a => a.1.interPt a.2 = gg.1.interPt gg.2) := by
    rw [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨hmem1, hmem2⟩
  have hcard : ({gg, (gg.2, gg.1)} : Finset (Line × Line)).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simp [hne2]), Finset.card_singleton]
  rw [← hcard]
  exact Finset.card_le_card hsub

/-- The association map sends red lines into the blue points. -/
lemma assocB_mem_bluePts (L : Finset Line) {B : Finset Line} (hBL : B ⊆ L)
    (W : ∀ m ∈ L \ B, Witness L B m)
    (hGP : GeneralPosition L) {ℓ : Line} (hℓ : ℓ ∈ L \ B) :
    assocB L B W hGP ℓ ∈ bluePts B := by
  rw [assocB, dif_pos hℓ]
  have hℓL := (Finset.mem_sdiff.mp hℓ).1
  set W' := W ℓ hℓ with hW'
  have h1 : (W'.g1 hGP hℓL).val (W'.b hGP hℓL) = 0 := (W'.b_mem_closure hGP hℓL).2
  have h2 : (W'.g2 hGP hℓL).val (W'.b hGP hℓL) = 0 := W'.g2_val_b hGP hℓL
  have hd : (W'.g1 hGP hℓL).det (W'.g2 hGP hℓL) ≠ 0 :=
    GP.det_ne hGP (hBL (W'.g1_blue hGP hℓL)) (hBL (W'.g2_blue hGP hℓL))
      (Ne.symm (W'.g2_ne_g1 hGP hℓL))
  have h3 : W'.b hGP hℓL = (W'.g1 hGP hℓL).interPt (W'.g2 hGP hℓL) :=
    Line.eq_interPt hd h1 h2
  rw [h3, bluePts]
  exact Finset.mem_image.mpr ⟨(W'.g1 hGP hℓL, W'.g2 hGP hℓL), by
    rw [Finset.mem_offDiag]
    exact ⟨W'.g1_blue hGP hℓL, W'.g2_blue hGP hℓL, Ne.symm (W'.g2_ne_g1 hGP hℓL)⟩, rfl⟩

/-- The number of red lines is at most twice the number of blue points. -/
lemma card_red_le (L B : Finset Line) (W : ∀ m ∈ L \ B, Witness L B m)
    (hGP : GeneralPosition L) :
    (L \ B).card ≤ 2 * ((L \ B).image (assocB L B W hGP)).card := by
  apply Finset.card_le_mul_card_image
  intro p hp
  exact fiber_card_le_two L B W hGP p

/-- The grand count: `n ≤ k²`. -/
lemma main_counting {L : Finset Line} {B : Finset Line} (hGP : GeneralPosition L) (hBL : B ⊆ L)
    (W : ∀ m ∈ L \ B, Witness L B m) : L.card ≤ B.card ^ 2 := by
  have h1 := card_red_le L B W hGP
  have h2 : ((L \ B).image (assocB L B W hGP)).card ≤ (bluePts B).card := by
    apply Finset.card_le_card
    intro p hp
    simp only [Finset.mem_image] at hp
    obtain ⟨ℓ, hℓ, rfl⟩ := hp
    exact assocB_mem_bluePts L hBL W hGP hℓ
  have h3 := two_mul_card_bluePts hGP hBL
  have h4 : (L \ B).card = L.card - B.card := Finset.card_sdiff_of_subset hBL
  have h5 : B.card * B.card - B.card + B.card = B.card * B.card :=
    Nat.sub_add_cancel (Nat.le_mul_self B.card)
  have h6 : B.card * B.card = B.card ^ 2 := (sq B.card).symm
  omega

/-- If no finite region has a completely blue boundary in the working sense,
then no finite region has a completely blue boundary in the geometric sense. -/
lemma not_frontier_subset_of_validBlue {L : Finset Line} {B : Finset Line}
    (hGP : GeneralPosition L) (hBL : B ⊆ L)
    (hBV : ValidBlue L B) {σ : Line → Bool} (hne : (Cell L σ).Nonempty)
    (hbdd : Bornology.IsBounded (Cell L σ)) :
    ¬ (frontier (Cell L σ) ⊆ ⋃ ℓ ∈ B, ℓ.set) := by
  obtain ⟨m, hmL, hmb, hmB⟩ := hBV σ hne hbdd
  intro hsub
  apply hmB
  set E : EdgeCtx L := ⟨σ, m, hGP, hne, hbdd, hmL, hmb⟩ with hE
  have hlt : E.Tmin < E.Tmax := E.Tmin_lt_Tmax
  set S := E.ℓ.param '' Set.Icc E.Tmin E.Tmax with hS
  have hSI : S.Infinite := (Set.Icc_infinite hlt).image E.ℓ.param_injective.injOn
  have hSf : S ⊆ frontier (Cell L σ) := by
    rintro p ⟨t, ht, rfl⟩
    have h1 := E.param_mem_closure_inter ht
    rw [mem_frontier_iff hne]
    constructor
    · have h2 := h1.1
      rw [closure_cell hne] at h2
      exact h2
    · exact ⟨m, hmL, h1.2⟩
  have hSB : S ⊆ ⋃ ℓ ∈ B, ℓ.set := hSf.trans hsub
  have hchoice : ∀ p ∈ S, ∃ mm ∈ B, p ∈ mm.set := by
    intro p hp
    have h := hSB hp
    simp only [Set.mem_iUnion] at h
    obtain ⟨mm, hmm, hpm⟩ := h
    exact ⟨mm, hmm, hpm⟩
  choose f hf using hchoice
  set g := fun p : S => f p p.2 with hg
  have : Infinite S := Set.infinite_coe_iff.mpr hSI
  have hSI' : (Set.univ : Set S).Infinite := Set.infinite_univ
  have hMaps : Set.MapsTo g Set.univ (B : Set Line) := fun p _ => (hf p p.2).1
  obtain ⟨p₁, -, p₂, -, hp12, hpeq⟩ :=
    hSI'.exists_ne_map_eq_of_mapsTo hMaps (Finset.finite_toSet B)
  -- both points lie on `m` and on the same blue line `g p₁`, so `m = g p₁ ∈ B`
  have hp1S : p₁.1 ∈ E.ℓ.param '' Set.Icc E.Tmin E.Tmax := p₁.2
  have hp2S : p₂.1 ∈ E.ℓ.param '' Set.Icc E.Tmin E.Tmax := p₂.2
  obtain ⟨t₁, ht₁, hpt₁⟩ := hp1S
  obtain ⟨t₂, ht₂, hpt₂⟩ := hp2S
  have hv1 : (g p₁).val p₁.1 = 0 := (hf p₁.1 p₁.2).2
  have hv2 : (g p₂).val p₂.1 = 0 := (hf p₂.1 p₂.2).2
  have hmB1 : g p₁ ∈ B := (hf p₁.1 p₁.2).1
  have hne12 : p₁.1 ≠ p₂.1 := fun h => hp12 (Subtype.ext h)
  have hline := Line.eq_of_two_mem hGP hmL (hBL hmB1) hne12
    (by rw [← hpt₁]; exact Line.val_param _ _)
    (by rw [← hpt₂]; exact Line.val_param _ _)
    hv1 (hpeq ▸ hv2)
  rw [hline]
  exact hmB1

/-- The main result: one can colour at least `√n` lines. -/
lemma main_result (L : Finset Line) (hGP : GeneralPosition L) :
    ∃ B : Finset Line, B ⊆ L ∧ Real.sqrt L.card ≤ B.card ∧ ValidBlue L B := by
  obtain ⟨B, hBL, hBV, hmax⟩ := exists_maximal_valid L
  refine ⟨B, hBL, ?_, hBV⟩
  have hW : ∀ m ∈ L \ B, Witness L B m := fun m hm => redWitness L hBV hmax hm
  have hcount := main_counting hGP hBL hW
  have h1 : (L.card : ℝ) ≤ (B.card : ℝ) ^ 2 := by exact_mod_cast hcount
  have h2 := Real.sqrt_le_sqrt h1
  rwa [Real.sqrt_sq (Nat.cast_nonneg B.card)] at h2

snip end

problem imo2014_p6 :
    ∃ N : ℕ, ∀ n ≥ N, ∀ L : Finset Line, L.card = n → GeneralPosition L →
      ∃ B : Finset Line, B ⊆ L ∧ Real.sqrt n ≤ B.card ∧
        ∀ σ : Line → Bool, (Cell L σ).Nonempty → Bornology.IsBounded (Cell L σ) →
          ¬ (frontier (Cell L σ) ⊆ ⋃ ℓ ∈ B, ℓ.set) := by
  refine ⟨0, fun n _ L hn hGP => ?_⟩
  obtain ⟨B, hBL, hk, hBV⟩ := main_result L hGP
  refine ⟨B, hBL, ?_, ?_⟩
  · rwa [hn] at hk
  · intro σ hne hbdd
    exact not_frontier_subset_of_validBlue hGP hBL hBV hne hbdd

end Imo2014P6
