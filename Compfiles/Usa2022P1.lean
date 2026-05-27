import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# USA Mathematical Olympiad 2022, Problem 1

Let a and b be positive integers. The cells of an (a+b+1) × (a+b+1) grid
are colored amber and bronze such that there are at least a² + ab - b
amber cells and at least b² + ab - a bronze cells. Prove that it is
possible to choose a amber cells and b bronze cells such that no two
of the a + b chosen cells lie in the same row or column.
-/

namespace Usa2022P1

snip begin

open Finset

variable {N : ℕ}

abbrev Cell (N : ℕ) := Fin N × Fin N

def colorCount (color : Cell N → Fin 2) (c : Fin 2) (p : Equiv.Perm (Fin N)) : ℕ :=
  (univ.filter fun r : Fin N => color (r, p r) = c).card

def rowsToCells (p : Equiv.Perm (Fin N)) (s : Finset (Fin N)) : Finset (Cell N) :=
  s.map
    ⟨fun r : Fin N => (r, p r), by
      intro r t h
      exact Prod.ext_iff.mp h |>.1⟩

lemma rowsToCells_card (p : Equiv.Perm (Fin N)) (s : Finset (Fin N)) :
    (rowsToCells p s).card = s.card := by
  simp [rowsToCells]

lemma mem_rowsToCells {p : Equiv.Perm (Fin N)} {s : Finset (Fin N)} {x : Cell N} :
    x ∈ rowsToCells p s ↔ ∃ r ∈ s, x = (r, p r) := by
  constructor
  · intro hx
    rw [rowsToCells, mem_map] at hx
    rcases hx with ⟨r, hr, h⟩
    exact ⟨r, hr, h.symm⟩
  · rintro ⟨r, hr, rfl⟩
    simp [rowsToCells, hr]

lemma rowsToCells_color {color : Cell N → Fin 2} {p : Equiv.Perm (Fin N)}
    {s : Finset (Fin N)} {c : Fin 2}
    (hs : ∀ r ∈ s, color (r, p r) = c) :
    ∀ x ∈ rowsToCells p s, color x = c := by
  intro x hx
  rw [mem_rowsToCells] at hx
  rcases hx with ⟨r, hr, rfl⟩
  exact hs r hr

lemma rowsToCells_no_conflict
    (p : Equiv.Perm (Fin N)) (s t : Finset (Fin N)) :
    ∀ x ∈ rowsToCells p s ∪ rowsToCells p t,
      ∀ y ∈ rowsToCells p s ∪ rowsToCells p t,
        x ≠ y → x.fst ≠ y.fst ∧ x.snd ≠ y.snd := by
  intro x hx y hy hxy
  have hx' : ∃ r : Fin N, x = (r, p r) := by
    rw [mem_union] at hx
    rcases hx with hx | hx <;> rw [mem_rowsToCells] at hx
    · rcases hx with ⟨r, _hr, h⟩
      exact ⟨r, h⟩
    · rcases hx with ⟨r, _hr, h⟩
      exact ⟨r, h⟩
  have hy' : ∃ r : Fin N, y = (r, p r) := by
    rw [mem_union] at hy
    rcases hy with hy | hy <;> rw [mem_rowsToCells] at hy
    · rcases hy with ⟨r, _hr, h⟩
      exact ⟨r, h⟩
    · rcases hy with ⟨r, _hr, h⟩
      exact ⟨r, h⟩
  rcases hx' with ⟨rx, rfl⟩
  rcases hy' with ⟨ry, rfl⟩
  constructor
  · intro hfst
    apply hxy
    have hrow : rx = ry := by
      simpa using hfst
    simp [hrow]
  · intro hsnd
    apply hxy
    have hrow : rx = ry := p.injective hsnd
    simp [hrow]

lemma color_ne_zero_iff_eq_one (c : Fin 2) : c ≠ 0 ↔ c = 1 := by
  fin_cases c <;> simp

lemma colorCount_zero_add_one (color : Cell N → Fin 2) (p : Equiv.Perm (Fin N)) :
    colorCount color 0 p + colorCount color 1 p = N := by
  classical
  rw [colorCount, colorCount]
  have h :
      (univ.filter fun r : Fin N => color (r, p r) = 1)
        = (univ.filter fun r : Fin N => ¬ color (r, p r) = 0) := by
    ext r
    simp [color_ne_zero_iff_eq_one]
  rw [h, Finset.card_filter_add_card_filter_not]
  simp

lemma colorCount_one_le_iff (color : Cell N → Fin 2) (p : Equiv.Perm (Fin N))
    {b : ℕ} (hb : b ≤ N) :
    b ≤ colorCount color 1 p ↔ colorCount color 0 p ≤ N - b := by
  constructor
  · intro h
    have hsum := colorCount_zero_add_one color p
    omega
  · intro h
    have hsum := colorCount_zero_add_one color p
    omega

-- Adjacent permutations in the transposition graph differ in at most two rows.
lemma colorCount_swap_le_add_two
    (color : Cell N → Fin 2) (p : Equiv.Perm (Fin N)) (x y : Fin N) :
    colorCount color 0 (p * Equiv.swap x y) ≤ colorCount color 0 p + 2 := by
  classical
  unfold colorCount
  let s : Finset (Fin N) := univ.filter fun r : Fin N => color (r, p r) = 0
  let t : Finset (Fin N) := univ.filter fun r : Fin N => color (r, (p * Equiv.swap x y) r) = 0
  have hsub : t ⊆ s ∪ {x, y} := by
    intro r hr
    simp only [t, mem_filter, mem_univ, true_and] at hr
    by_cases hx : r = x
    · simp [hx]
    · by_cases hy : r = y
      · simp [hy]
      · have hswap : Equiv.swap x y r = r := Equiv.swap_apply_of_ne_of_ne hx hy
        have : color (r, p r) = 0 := by
          simpa [Equiv.Perm.mul_def, Function.comp_apply, hswap] using hr
        simp [s, this]
  calc
    t.card ≤ (s ∪ {x, y}).card := card_le_card hsub
    _ ≤ s.card + ({x, y} : Finset (Fin N)).card := card_union_le _ _
    _ ≤ s.card + 2 := by
      gcongr
      exact card_le_two

lemma colorCount_swap_ge_sub_two
    (color : Cell N → Fin 2) (p : Equiv.Perm (Fin N)) (x y : Fin N) :
    colorCount color 0 p ≤ colorCount color 0 (p * Equiv.swap x y) + 2 := by
  simpa [mul_assoc] using
    colorCount_swap_le_add_two color (p * Equiv.swap x y) x y

-- Walking from a color-rich transversal to a color-poor one gives count a or a+1.
lemma exists_transversal_with_exact_or_succ_color_count
    (color : Cell N → Fin 2) (a : ℕ) (p q : Equiv.Perm (Fin N))
    (hp : a ≤ colorCount color 0 p)
    (hq : colorCount color 0 q ≤ a + 1) :
    ∃ r : Equiv.Perm (Fin N), colorCount color 0 r = a ∨ colorCount color 0 r = a + 1 := by
  classical
  let τ : Equiv.Perm (Fin N) := p.symm * q
  have hq' : colorCount color 0 (p * τ) ≤ a + 1 := by
    have hpq : p * (p.symm * q) = q := by
      ext r
      simp [Equiv.Perm.mul_def]
    simpa [τ, hpq] using hq
  have main :
      ∀ τ : Equiv.Perm (Fin N), colorCount color 0 p ≥ a →
        colorCount color 0 (p * τ) ≤ a + 1 →
        ∃ r : Equiv.Perm (Fin N), colorCount color 0 r = a ∨ colorCount color 0 r = a + 1 := by
    intro τ
    refine Equiv.Perm.swap_induction_on' τ ?base ?step
    · intro hstart hend
      refine ⟨p, ?_⟩
      simp only [mul_one] at hend
      omega
    · intro τ x y hxy ih hstart hend
      by_cases hmid : colorCount color 0 (p * τ) ≤ a + 1
      · exact ih hstart hmid
      · refine ⟨p * (τ * Equiv.swap x y), ?_⟩
        have hge : a ≤ colorCount color 0 (p * (τ * Equiv.swap x y)) := by
          have hdrop := colorCount_swap_ge_sub_two color (p * τ) x y
          rw [mul_assoc] at hdrop
          have hmid' : a + 2 ≤ colorCount color 0 (p * τ) := by omega
          omega
        omega
  exact main τ hp hq'

/-- Columns containing a good cell in one of the rows in `R`. -/
def neighborCols (good : Cell N → Prop) [DecidablePred good]
    (R : Finset (Fin N)) : Finset (Fin N) :=
  univ.filter fun c : Fin N => ∃ r ∈ R, good (r, c)

/-- The dummy columns used to turn "at least `k` real matches" into a full matching. -/
def dummyCols (N k : ℕ) : Finset (Fin N ⊕ Fin (N - k)) :=
  univ.map Function.Embedding.inr

/-- Hall targets for row `r`: good real columns, plus all dummy columns. -/
def hallTargets (good : Cell N → Prop) [DecidablePred good]
    (k : ℕ) (r : Fin N) : Finset (Fin N ⊕ Fin (N - k)) :=
  (univ.filter fun c : Fin N => good (r, c)).disjSum (univ : Finset (Fin (N - k)))

/--
If Hall fails on rows `R`, then the rows outside `R` together with the
neighboring columns of `R` form at most `k - 1` covering lines.
-/
lemma line_count_le_of_hall_failure
    (good : Cell N → Prop) [DecidablePred good] {k : ℕ} {R : Finset (Fin N)}
    (hfail : (R.biUnion (hallTargets good k)).card < R.card) :
    ((univ : Finset (Fin N)) \ R).card + (neighborCols good R).card ≤ k - 1 := by
  classical
  have hRne : R.Nonempty := by
    exact Finset.card_pos.mp (by omega)
  have hRcard_le : R.card ≤ N := by
    simpa using card_le_univ R
  have hdummy_subset : dummyCols N k ⊆ R.biUnion (hallTargets good k) := by
    intro z hz
    rcases hRne with ⟨r0, hr0⟩
    rw [mem_biUnion]
    rw [dummyCols, mem_map] at hz
    rcases hz with ⟨d, _hd, hzd⟩
    refine ⟨r0, hr0, ?_⟩
    rw [← hzd]
    simp [hallTargets]
  have hreal_subset :
      (neighborCols good R).map Function.Embedding.inl ⊆ R.biUnion (hallTargets good k) := by
    intro z hz
    rw [mem_map] at hz
    rcases hz with ⟨c, hc, rfl⟩
    simp only [neighborCols, mem_filter, mem_univ, true_and] at hc
    rcases hc with ⟨r, hrR, hgood⟩
    rw [mem_biUnion]
    refine ⟨r, hrR, ?_⟩
    simp [hallTargets, hgood]
  have hunion_subset :
      (neighborCols good R).map Function.Embedding.inl ∪ dummyCols N k
        ⊆ R.biUnion (hallTargets good k) :=
    union_subset hreal_subset hdummy_subset
  have hdisj :
      Disjoint ((neighborCols good R).map Function.Embedding.inl) (dummyCols N k) := by
    simpa [dummyCols] using
      (Finset.disjoint_map_inl_map_inr (s := neighborCols good R)
        (t := (univ : Finset (Fin (N - k)))))
  have hline_lt :
      (neighborCols good R).card + (N - k) < R.card := by
    have hcard_union :
        (((neighborCols good R).map Function.Embedding.inl) ∪ dummyCols N k).card
          = (neighborCols good R).card + (N - k) := by
      rw [card_union_of_disjoint hdisj, card_map]
      simp [dummyCols, Fintype.card_fin]
    calc
      (neighborCols good R).card + (N - k)
          = (((neighborCols good R).map Function.Embedding.inl) ∪ dummyCols N k).card :=
            hcard_union.symm
      _ ≤ (R.biUnion (hallTargets good k)).card := card_le_card hunion_subset
      _ < R.card := hfail
  have houtside_card : ((univ : Finset (Fin N)) \ R).card = N - R.card := by
    simp [card_sdiff_of_subset, Fintype.card_fin]
  have hlt' : ((univ : Finset (Fin N)) \ R).card + (neighborCols good R).card < k := by
    rw [houtside_card]
    omega
  omega

/-- Any good cells covered by at most `k - 1` rows/columns number at most `(k - 1) * N`. -/
lemma good_cells_card_le_of_neighbor_line_count
    (good : Cell N → Prop) [DecidablePred good] {k : ℕ} (R : Finset (Fin N))
    (hline : ((univ : Finset (Fin N)) \ R).card + (neighborCols good R).card ≤ k - 1) :
    (univ.filter good).card ≤ (k - 1) * N := by
  classical
  let outside : Finset (Fin N) := univ \ R
  let cover : Finset (Cell N) :=
    (outside ×ˢ (univ : Finset (Fin N))) ∪
      ((univ : Finset (Fin N)) ×ˢ neighborCols good R)
  have hgood_subset_cover : (univ.filter good) ⊆ cover := by
    intro x hx
    rcases x with ⟨r, c⟩
    simp only [mem_filter, mem_univ, true_and] at hx
    by_cases hr : r ∈ R
    · have hc : c ∈ neighborCols good R := by
        simp only [neighborCols, mem_filter, mem_univ, true_and]
        exact ⟨r, hr, hx⟩
      simp [cover, hc]
    · have hrout : r ∈ outside := by
        simp [outside, hr]
      simp [cover, hrout]
  have hcover_card :
      cover.card ≤ (outside.card + (neighborCols good R).card) * N := by
    calc
      cover.card
          ≤ (outside ×ˢ (univ : Finset (Fin N))).card
              + ((univ : Finset (Fin N)) ×ˢ neighborCols good R).card := card_union_le _ _
      _ = outside.card * N + N * (neighborCols good R).card := by
        simp [card_product, Fintype.card_fin]
      _ = (outside.card + (neighborCols good R).card) * N := by ring
  calc
    (univ.filter good).card ≤ cover.card := card_le_card hgood_subset_cover
    _ ≤ (outside.card + (neighborCols good R).card) * N := hcover_card
    _ ≤ (k - 1) * N := by
      gcongr

-- Hall step: more than (k-1)N good cells force a transversal with k good cells.
lemma exists_transversal_with_many_good_cells
    (good : Cell N → Prop) [DecidablePred good] {k : ℕ}
    (hkN : k ≤ N)
    (hcard : (k - 1) * N < (univ.filter good).card) :
    ∃ p : Equiv.Perm (Fin N),
      k ≤ (univ.filter fun r : Fin N => good (r, p r)).card := by
  classical
  let dummy : Finset (Fin N ⊕ Fin (N - k)) := dummyCols N k
  let t (r : Fin N) : Finset (Fin N ⊕ Fin (N - k)) := hallTargets good k r
  -- If Hall failed, the outside rows plus neighbor columns would cover all good cells.
  have hall : ∀ R : Finset (Fin N), R.card ≤ (R.biUnion t).card := by
    intro R
    by_contra hle
    have hlt : (R.biUnion t).card < R.card := Nat.lt_of_not_ge hle
    have hline_count_le :
        ((univ : Finset (Fin N)) \ R).card + (neighborCols good R).card ≤ k - 1 := by
      apply line_count_le_of_hall_failure (good := good) (k := k) (R := R)
      simpa [t] using hlt
    have hgood_card_le : (univ.filter good).card ≤ (k - 1) * N :=
      good_cells_card_le_of_neighbor_line_count (good := good) (k := k) R hline_count_le
    exact not_lt_of_ge hgood_card_le hcard
  rcases (Finset.all_card_le_biUnion_card_iff_existsInjective' t).mp hall with
    ⟨f, hfinj, hfmem⟩
  -- Dummy columns absorb at most N-k rows, leaving at least k real matched rows.
  let realRows : Finset (Fin N) := univ.filter fun r : Fin N => ∃ c : Fin N, f r = Sum.inl c
  let dummyRows : Finset (Fin N) := univ \ realRows
  have hpartition_card : realRows.card + dummyRows.card = N := by
    have h := Finset.card_sdiff_add_card_eq_card (s := realRows) (t := univ) (by simp)
    simpa [dummyRows, Fintype.card_fin, Nat.add_comm] using h
  have hdummy_card_le : dummyRows.card ≤ N - k := by
    have himage_subset : dummyRows.image f ⊆ dummy := by
      intro z hz
      rw [mem_image] at hz
      rcases hz with ⟨r, hr, rfl⟩
      have hr_not_real : r ∉ realRows := by
        simpa [dummyRows] using hr
      cases h : f r with
      | inl c =>
          exfalso
          exact hr_not_real (by simp [realRows, h])
      | inr d =>
          simp [dummy, dummyCols]
    calc
      dummyRows.card = (dummyRows.image f).card := by
        rw [card_image_of_injective]
        exact hfinj
      _ ≤ dummy.card := card_le_card himage_subset
      _ = N - k := by simp [dummy, dummyCols, Fintype.card_fin]
  have hreal_card_ge : k ≤ realRows.card := by
    omega
  have hreal_exists : ∀ r : {r // r ∈ realRows}, ∃ c : Fin N, f r = Sum.inl c := by
    intro r
    have hr := r.2
    simp only [realRows, mem_filter, mem_univ, true_and] at hr
    exact hr
  choose col hcol using hreal_exists
  have hcol_inj : Function.Injective col := by
    intro r s h
    apply Subtype.ext
    apply hfinj
    rw [hcol r, hcol s, h]
  obtain ⟨p, hp_ext⟩ := Equiv.Perm.exists_extending_pair
    (fun r : {r // r ∈ realRows} => (r : Fin N)) col
    Subtype.val_injective hcol_inj
  refine ⟨p, hreal_card_ge.trans ?_⟩
  apply card_le_card
  intro r hr
  simp only [mem_filter, mem_univ, true_and]
  let rr : {r // r ∈ realRows} := ⟨r, hr⟩
  have hf_in_t := hfmem r
  have hcol_eq : f r = Sum.inl (col rr) := hcol rr
  have hgood : good (r, col rr) := by
    have : Sum.inl (col rr) ∈ hallTargets good k r := by
      simpa [t, hcol_eq] using hf_in_t
    simpa [hallTargets] using this
  have hp : p r = col rr := hp_ext rr
  simpa [hp] using hgood

/-- The density hypotheses give a transversal with exactly `a` or `a+1` amber cells. -/
lemma exists_intermediate_transversal_of_card_bounds
    (a b : ℕ)
    (ha : 0 < a)
    (hb : 0 < b)
    (color : Cell (a + b + 1) → Fin 2)
    (c0 : a ^ 2 + a * b - b ≤ Fintype.card {s // color s = 0})
    (c1 : b ^ 2 + a * b - a ≤ Fintype.card {s // color s = 1}) :
    ∃ p : Equiv.Perm (Fin (a + b + 1)),
      colorCount color 0 p = a ∨ colorCount color 0 p = a + 1 := by
  classical
  let N := a + b + 1
  -- Convert the statement's cardinality hypotheses into filtered finset counts.
  have haN : a ≤ N := by omega
  have hbN : b ≤ N := by omega
  have hc0' :
      a ^ 2 + a * b - b ≤ (univ.filter fun s : Cell N => color s = 0).card := by
    simpa [N, Fintype.card_subtype] using c0
  have hc1' :
      b ^ 2 + a * b - a ≤ (univ.filter fun s : Cell N => color s = 1).card := by
    simpa [N, Fintype.card_subtype] using c1
  have hstrict0 : (a - 1) * N < a ^ 2 + a * b - b := by
    have hformula : (a - 1) * N + 1 = a ^ 2 + a * b - b := by
      cases a with
      | zero => cases ha
      | succ a' =>
          simp [N]
          ring_nf
          rw [Nat.add_sub_cancel]
    rw [← hformula]
    exact Nat.lt_succ_self _
  have hstrict1 : (b - 1) * N < b ^ 2 + a * b - a := by
    have hformula : (b - 1) * N + 1 = b ^ 2 + a * b - a := by
      cases b with
      | zero => cases hb
      | succ b' =>
          simp [N]
          ring_nf
          rw [Nat.add_sub_cancel]
    rw [← hformula]
    exact Nat.lt_succ_self _
  have hcard0 : (a - 1) * N < (univ.filter fun s : Cell N => color s = 0).card :=
    lt_of_lt_of_le hstrict0 hc0'
  have hcard1 : (b - 1) * N < (univ.filter fun s : Cell N => color s = 1).card :=
    lt_of_lt_of_le hstrict1 hc1'
  -- Find one transversal rich in amber and one rich in bronze.
  rcases exists_transversal_with_many_good_cells (N := N) (fun s : Cell N => color s = 0)
      haN hcard0 with ⟨p0, hp0⟩
  rcases exists_transversal_with_many_good_cells (N := N) (fun s : Cell N => color s = 1)
      hbN hcard1 with ⟨p1, hp1⟩
  have hp1_zero : colorCount color 0 p1 ≤ a + 1 := by
    have h := (colorCount_one_le_iff color p1 hbN).mp hp1
    have hNb : a + b + 1 - b = a + 1 := by
      omega
    simpa [N, hNb] using h
  -- Interpolate between those transversals until the amber count is a or a+1.
  simpa [N] using exists_transversal_with_exact_or_succ_color_count color a p0 p1 hp0 hp1_zero

/-- A transversal with `a` or `a+1` amber cells contains the required amber/bronze choices. -/
lemma exists_cells_of_intermediate_transversal
    {a b : ℕ}
    (color : Cell (a + b + 1) → Fin 2)
    (p : Equiv.Perm (Fin (a + b + 1)))
    (hp : colorCount color 0 p = a ∨ colorCount color 0 p = a + 1) :
    ∃ A B : Finset (Cell (a + b + 1)),
      A.card = a ∧ B.card = b ∧
      (∀ x ∈ A, color x = 0) ∧
      (∀ y ∈ B, color y = 1) ∧
      ∀ x ∈ A ∪ B, ∀ y ∈ A ∪ B, x ≠ y → x.fst ≠ y.fst ∧ x.snd ≠ y.snd := by
  classical
  let rows0 : Finset (Fin (a + b + 1)) := univ.filter fun r => color (r, p r) = 0
  let rows1 : Finset (Fin (a + b + 1)) := univ.filter fun r => color (r, p r) = 1
  have hsum : rows0.card + rows1.card = a + b + 1 := by
    simpa [rows0, rows1, colorCount] using colorCount_zero_add_one color p
  -- The final transversal is already conflict-free; trim one color if it has one extra row.
  rcases hp with hp | hp
  · have hrows0 : rows0.card = a := by
      simpa [rows0, colorCount] using hp
    have hb_le_rows1 : b ≤ rows1.card := by
      omega
    rcases Finset.exists_subset_card_eq hb_le_rows1 with ⟨brows, hbsub, hbcard⟩
    refine ⟨rowsToCells p rows0, rowsToCells p brows, ?_, ?_, ?_, ?_, ?_⟩
    · simp [rowsToCells_card, hrows0]
    · simp [rowsToCells_card, hbcard]
    · apply rowsToCells_color
      intro r hr
      simpa [rows0] using hr
    · apply rowsToCells_color
      intro r hr
      have : r ∈ rows1 := hbsub hr
      simpa [rows1] using this
    · exact rowsToCells_no_conflict p rows0 brows
  · have hrows0 : rows0.card = a + 1 := by
      simpa [rows0, colorCount] using hp
    have ha_le_rows0 : a ≤ rows0.card := by omega
    rcases Finset.exists_subset_card_eq ha_le_rows0 with ⟨arows, hasub, hacard⟩
    have hrows1 : rows1.card = b := by omega
    refine ⟨rowsToCells p arows, rowsToCells p rows1, ?_, ?_, ?_, ?_, ?_⟩
    · simp [rowsToCells_card, hacard]
    · simp [rowsToCells_card, hrows1]
    · apply rowsToCells_color
      intro r hr
      have : r ∈ rows0 := hasub hr
      simpa [rows0] using this
    · apply rowsToCells_color
      intro r hr
      simpa [rows1] using hr
    · exact rowsToCells_no_conflict p arows rows1

snip end

problem usa2022_p1
    (a b : ℕ)
    (ha : 0 < a)
    (hb : 0 < b)
    (color : Fin (a + b + 1) × Fin (a + b + 1) → Fin 2)
    (c0 : a ^ 2 + a * b - b ≤ Fintype.card {s // color s = 0})
    (c1 : b ^ 2 + a * b - a ≤ Fintype.card {s // color s = 1}) :
    ∃ A B : Finset (Fin (a + b + 1) × Fin (a + b + 1)),
      A.card = a ∧ B.card = b ∧
      (∀ x ∈ A, color x = 0) ∧
      (∀ y ∈ B, color y = 1) ∧
      ∀ x ∈ A ∪ B, ∀ y ∈ A ∪ B, x ≠ y → x.fst ≠ y.fst ∧ x.snd ≠ y.snd := by
  rcases exists_intermediate_transversal_of_card_bounds a b ha hb color c0 c1 with ⟨p, hp⟩
  exact exists_cells_of_intermediate_transversal color p hp


end Usa2022P1
