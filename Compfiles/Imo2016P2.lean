/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Olympiad 2016, Problem 2

Find all positive integers $n$ for which each cell of an $n \times n$ table can
be filled with one of the letters $I$, $M$ and $O$ in such a way that:

* in each row and each column, one third of the entries are $I$, one third are
  $M$ and one third are $O$; and
* in any diagonal, if the number of entries on the diagonal is a multiple of
  three, then one third of the entries are $I$, one third are $M$ and one third
  are $O$.

Note. The rows and columns of an $n \times n$ table are each labelled $1$ to $n$
in a natural order. Thus each cell corresponds to a pair of positive integers
$(i, j)$ with $1 \le i, j \le n$. For $n > 1$, the table has $4n - 2$ diagonals
of two types. A diagonal of the first type consists of all cells $(i, j)$ for
which $i + j$ is a constant, and a diagonal of the second type consists of all
cells $(i, j)$ for which $i - j$ is constant.
-/

namespace Imo2016P2

/-- The three letters `I`, `M`, `O`. -/
abbrev Letter := Fin 3

variable {n : ℕ}

/-- A finite set of cells is *balanced* under the coloring `f` if each of the
three letters occurs on exactly one third of its cells. -/
def Balanced (f : Fin n → Fin n → Letter) (cells : Finset (Fin n × Fin n)) : Prop :=
  ∀ c : Letter, (cells.filter (fun p ↦ f p.1 p.2 = c)).card = cells.card / 3

/-- The cells of row `r`. -/
def row (r : Fin n) : Finset (Fin n × Fin n) := Finset.univ.filter (fun p ↦ p.1 = r)

/-- The cells of column `k`. -/
def col (k : Fin n) : Finset (Fin n × Fin n) := Finset.univ.filter (fun p ↦ p.2 = k)

/-- A diagonal of the first type: the cells `(i, j)` with `i + j = s`. -/
def diagSum (s : ℕ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun p ↦ (p.1 : ℕ) + (p.2 : ℕ) = s)

/-- A diagonal of the second type: the cells `(i, j)` with `i - j = d`. -/
def diagDiff (d : ℤ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun p ↦ ((p.1 : ℕ) : ℤ) - ((p.2 : ℕ) : ℤ) = d)

/-- The coloring `f` of the `n × n` table satisfies all the required conditions:
every row and column is balanced, and every diagonal whose length is a multiple
of three is balanced. -/
def MODTable (f : Fin n → Fin n → Letter) : Prop :=
  (∀ r : Fin n, Balanced f (row r)) ∧
  (∀ k : Fin n, Balanced f (col k)) ∧
  (∀ s : ℕ, 3 ∣ (diagSum (n := n) s).card → Balanced f (diagSum s)) ∧
  (∀ d : ℤ, 3 ∣ (diagDiff (n := n) d).card → Balanced f (diagDiff d))

determine solution : Set ℕ := { n | 9 ∣ n }

snip begin

def periodicColor {n : ℕ} (i j : Fin n) : Letter :=
  Fin.ofNat 3 ((i : ℕ) + (j : ℕ) / 3)

lemma row_eq_product {n : ℕ} (r : Fin n) : row r = {r} ×ˢ Finset.univ := by
  ext p
  rcases p with ⟨i, j⟩
  simp [row, eq_comm]

lemma map_filter_periodicColor (r : Fin n) (c : Letter) :
    (Finset.univ.filter (fun j ↦ periodicColor r j = c)).map Fin.valEmbedding =
      (Finset.range n).filter (fun j ↦ Fin.ofNat 3 ((r : ℕ) + j / 3) = c) := by
  ext j
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_range, Fin.valEmbedding_apply]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a.isLt, ha⟩
  · rintro ⟨hj, hc⟩
    exact ⟨⟨j, hj⟩, hc, rfl⟩

lemma row_block_count (a : ℕ) (c : Letter) :
    ((Finset.range 9).filter (fun j ↦ Fin.ofNat 3 (a + j / 3) = c)).card = 3 := by
  have ha : a % 3 < 3 := Nat.mod_lt _ (by omega)
  interval_cases h : a % 3 <;> fin_cases c <;>
    norm_num [Fin.ofNat, Nat.add_mod, h] <;> decide

lemma row_periodic_count (a : ℕ) (c : Letter) (k : ℕ) :
    ((Finset.range (9 * k)).filter
      (fun j ↦ Fin.ofNat 3 (a + j / 3) = c)).card = 3 * k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [show 9 * (k + 1) = 9 * k + 9 by omega, Finset.range_add_eq_union,
        Finset.filter_union]
      rw [Finset.card_union_of_disjoint
        ((Finset.disjoint_range_addLeftEmbedding (9 * k) (Finset.range 9)).mono
          (Finset.filter_subset _ _) (Finset.filter_subset _ _))]
      rw [ih]
      have hblock :
          (((Finset.range 9).map (addLeftEmbedding (9 * k))).filter
            (fun j ↦ Fin.ofNat 3 (a + j / 3) = c)).card = 3 := by
        rw [Finset.filter_map, Finset.card_map]
        calc
          ((Finset.range 9).filter
              ((fun j ↦ Fin.ofNat 3 (a + j / 3) = c) ∘ addLeftEmbedding (9 * k))).card =
              ((Finset.range 9).filter
                (fun j ↦ Fin.ofNat 3 (a + j / 3) = c)).card := by
            congr 1
            ext j
            simp only [Finset.mem_filter, Finset.mem_range, Function.comp_apply,
              addLeftEmbedding_apply]
            have hcolor :
                Fin.ofNat 3 (a + (9 * k + j) / 3) =
                  Fin.ofNat 3 (a + j / 3) := by
              apply Fin.ext
              have hdiv : (9 * k + j) / 3 = 3 * k + j / 3 := by omega
              simp [Fin.ofNat, hdiv, Nat.add_mod]
            constructor
            · rintro ⟨hj, hc⟩
              exact ⟨hj, by rw [← hcolor]; exact hc⟩
            · rintro ⟨hj, hc⟩
              exact ⟨hj, by rw [hcolor]; exact hc⟩
          _ = 3 := row_block_count a c
      rw [hblock]
      omega

lemma add_block_count (a : ℕ) (c : Letter) :
    ((Finset.range 3).filter (fun j ↦ Fin.ofNat 3 (a + j) = c)).card = 1 := by
  have ha : a % 3 < 3 := Nat.mod_lt _ (by omega)
  interval_cases h : a % 3 <;> fin_cases c <;>
    norm_num [Fin.ofNat, Nat.add_mod, h] <;> decide

lemma add_periodic_count (a : ℕ) (c : Letter) (k : ℕ) :
    ((Finset.range (3 * k)).filter
      (fun j ↦ Fin.ofNat 3 (a + j) = c)).card = k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [show 3 * (k + 1) = 3 * k + 3 by omega, Finset.range_add_eq_union,
        Finset.filter_union]
      rw [Finset.card_union_of_disjoint
        ((Finset.disjoint_range_addLeftEmbedding (3 * k) (Finset.range 3)).mono
          (Finset.filter_subset _ _) (Finset.filter_subset _ _))]
      rw [ih]
      have hblock :
          (((Finset.range 3).map (addLeftEmbedding (3 * k))).filter
            (fun j ↦ Fin.ofNat 3 (a + j) = c)).card = 1 := by
        rw [Finset.filter_map, Finset.card_map]
        calc
          ((Finset.range 3).filter
              ((fun j ↦ Fin.ofNat 3 (a + j) = c) ∘ addLeftEmbedding (3 * k))).card =
              ((Finset.range 3).filter
                (fun j ↦ Fin.ofNat 3 (a + j) = c)).card := by
            congr 1
            ext j
            simp only [Finset.mem_filter, Finset.mem_range, Function.comp_apply,
              addLeftEmbedding_apply]
            have hcolor :
                Fin.ofNat 3 (a + (3 * k + j)) = Fin.ofNat 3 (a + j) := by
              apply Fin.ext
              simp [Fin.ofNat, Nat.add_mod]
            constructor
            · rintro ⟨hj, hc⟩
              exact ⟨hj, by rw [← hcolor]; exact hc⟩
            · rintro ⟨hj, hc⟩
              exact ⟨hj, by rw [hcolor]; exact hc⟩
          _ = 1 := add_block_count a c
      rw [hblock]

lemma col_eq_product {n : ℕ} (k : Fin n) : col k = Finset.univ ×ˢ {k} := by
  ext p
  rcases p with ⟨i, j⟩
  simp [col, eq_comm]

lemma map_filter_periodicColor_col (k : Fin n) (c : Letter) :
    (Finset.univ.filter (fun i ↦ periodicColor i k = c)).map Fin.valEmbedding =
      (Finset.range n).filter (fun i ↦ Fin.ofNat 3 (i + (k : ℕ) / 3) = c) := by
  ext i
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_range, Fin.valEmbedding_apply]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a.isLt, ha⟩
  · rintro ⟨hi, hc⟩
    exact ⟨⟨i, hi⟩, hc, rfl⟩

lemma diagSum_card_eq (n s : ℕ) :
    (diagSum (n := n) s).card = min n (s + 1) - (s + 1 - n) := by
  classical
  calc
    (diagSum (n := n) s).card =
        (Finset.Ico (s + 1 - n) (min n (s + 1))).card := by
      apply Finset.card_bij (fun p _ ↦ (p.2 : ℕ))
      · intro p hp
        simp only [diagSum, Finset.mem_filter, Finset.mem_univ, true_and] at hp
        simp only [Finset.mem_Ico]
        constructor <;> omega
      · intro p hp q hq hpq
        simp only [diagSum, Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
        apply Prod.ext
        · apply Fin.ext
          omega
        · apply Fin.ext
          exact hpq
      · intro j hj
        simp only [Finset.mem_Ico] at hj
        let p : Fin n × Fin n :=
          (⟨s - j, by omega⟩, ⟨j, by omega⟩)
        refine ⟨p, ?_, rfl⟩
        simp [diagSum, p]
        omega
    _ = min n (s + 1) - (s + 1 - n) := Nat.card_Ico _ _

lemma diagSum_color_card_eq (n s : ℕ) (c : Letter) :
    ((diagSum (n := n) s).filter
        (fun p ↦ periodicColor p.1 p.2 = c)).card =
      ((Finset.Ico (s + 1 - n) (min n (s + 1))).filter
        (fun j ↦ Fin.ofNat 3 ((s - j) + j / 3) = c)).card := by
  classical
  apply Finset.card_bij (fun p _ ↦ (p.2 : ℕ))
  · intro p hp
    simp only [Finset.mem_filter] at hp ⊢
    simp only [diagSum, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    refine ⟨?_, ?_⟩
    · simp only [Finset.mem_Ico]
      constructor <;> omega
    · have hsub : s - (p.2 : ℕ) = (p.1 : ℕ) := by omega
      simpa [periodicColor, hsub] using hp.2
  · intro p hp q hq hpq
    simp only [Finset.mem_filter] at hp hq
    simp only [diagSum, Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
    apply Prod.ext
    · apply Fin.ext
      omega
    · apply Fin.ext
      exact hpq
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_Ico] at hj
    let p : Fin n × Fin n :=
      (⟨s - j, by omega⟩, ⟨j, by omega⟩)
    refine ⟨p, ?_, rfl⟩
    simp only [Finset.mem_filter]
    constructor
    · simp [diagSum, p]
      omega
    · simpa [periodicColor, p] using hj.2

lemma desc_block_count (a : ℕ) (c : Letter) :
    ((Finset.range 3).filter
      (fun j ↦ Fin.ofNat 3 (a + 3 - j) = c)).card = 1 := by
  calc
    ((Finset.range 3).filter
        (fun j ↦ Fin.ofNat 3 (a + 3 - j) = c)).card =
        ((Finset.range 3).filter
          (fun j ↦ Fin.ofNat 3 (a % 3 + 3 - j) = c)).card := by
      congr 1
      ext j
      simp only [Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨hj, hc⟩
        refine ⟨hj, ?_⟩
        rw [← hc]
        apply Fin.ext
        have ha := Nat.div_add_mod a 3
        have hsub : a + 3 - j = 3 * (a / 3) + (a % 3 + 3 - j) := by omega
        simp [Fin.ofNat, hsub, Nat.add_mod]
      · rintro ⟨hj, hc⟩
        refine ⟨hj, ?_⟩
        rw [← hc]
        apply Fin.ext
        have ha := Nat.div_add_mod a 3
        have hsub : a + 3 - j = 3 * (a / 3) + (a % 3 + 3 - j) := by omega
        simp [Fin.ofNat, hsub, Nat.add_mod]
    _ = 1 := by
      have ha : a % 3 < 3 := Nat.mod_lt _ (by omega)
      interval_cases h : a % 3 <;> fin_cases c <;>
        norm_num [Fin.ofNat, h] <;> decide

lemma desc_block_count' (a : ℕ) (ha : 2 ≤ a) (c : Letter) :
    ((Finset.range 3).filter
      (fun j ↦ Fin.ofNat 3 (a - j) = c)).card = 1 := by
  calc
    ((Finset.range 3).filter
        (fun j ↦ Fin.ofNat 3 (a - j) = c)).card =
        ((Finset.range 3).filter
          (fun j ↦ Fin.ofNat 3 (a + 3 - j) = c)).card := by
      congr 1
      ext j
      simp only [Finset.mem_filter, Finset.mem_range]
      have hcolor (hj : j < 3) :
          Fin.ofNat 3 (a - j) = Fin.ofNat 3 (a + 3 - j) := by
        apply Fin.ext
        have hsub : a + 3 - j = (a - j) + 3 := by omega
        simp [Fin.ofNat, hsub]
      constructor
      · rintro ⟨hj, hc⟩
        exact ⟨hj, by rw [← hcolor hj]; exact hc⟩
      · rintro ⟨hj, hc⟩
        exact ⟨hj, by rw [hcolor hj]; exact hc⟩
    _ = 1 := desc_block_count a c

lemma desc_periodic_count (A B : ℕ) (c : Letter) (k : ℕ) (hA : 3 * k ≤ A + 1) :
    ((Finset.range (3 * k)).filter
      (fun j ↦ Fin.ofNat 3 (A - j + B + j / 3) = c)).card = k := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hAk : 3 * k ≤ A + 1 := by omega
      rw [show 3 * (k + 1) = 3 * k + 3 by omega, Finset.range_add_eq_union,
        Finset.filter_union]
      rw [Finset.card_union_of_disjoint
        ((Finset.disjoint_range_addLeftEmbedding (3 * k) (Finset.range 3)).mono
          (Finset.filter_subset _ _) (Finset.filter_subset _ _))]
      rw [ih hAk]
      have hconst : 2 ≤ A - 3 * k + B + k := by omega
      have hblock :
          (((Finset.range 3).map (addLeftEmbedding (3 * k))).filter
            (fun j ↦ Fin.ofNat 3 (A - j + B + j / 3) = c)).card = 1 := by
        rw [Finset.filter_map, Finset.card_map]
        calc
          ((Finset.range 3).filter
              ((fun j ↦ Fin.ofNat 3 (A - j + B + j / 3) = c) ∘
                addLeftEmbedding (3 * k))).card =
              ((Finset.range 3).filter
                (fun j ↦ Fin.ofNat 3 (A - 3 * k + B + k - j) = c)).card := by
            congr 1
            ext j
            simp only [Finset.mem_filter, Finset.mem_range, Function.comp_apply,
              addLeftEmbedding_apply]
            have hcolor (hj : j < 3) :
                Fin.ofNat 3 (A - (3 * k + j) + B + (3 * k + j) / 3) =
                  Fin.ofNat 3 (A - 3 * k + B + k - j) := by
              have hdiv : (3 * k + j) / 3 = k := by omega
              have heq : A - (3 * k + j) + B + (3 * k + j) / 3 =
                  A - 3 * k + B + k - j := by omega
              rw [heq]
            constructor
            · rintro ⟨hj, hc⟩
              exact ⟨hj, by rw [← hcolor hj]; exact hc⟩
            · rintro ⟨hj, hc⟩
              exact ⟨hj, by rw [hcolor hj]; exact hc⟩
          _ = 1 := desc_block_count' (A - 3 * k + B + k) hconst c
      rw [hblock]

lemma Ico_eq_map_range (a b : ℕ) :
    Finset.Ico a b = (Finset.range (b - a)).map (addLeftEmbedding a) := by
  ext x
  simp only [Finset.mem_Ico, Finset.mem_map, Finset.mem_range,
    addLeftEmbedding_apply]
  constructor
  · intro hx
    exact ⟨x - a, by omega, by omega⟩
  · rintro ⟨y, hy, rfl⟩
    omega

lemma periodicColor_diagSum (n : ℕ) (h9 : 9 ∣ n) (s : ℕ)
    (hs : 3 ∣ (diagSum (n := n) s).card) :
    Balanced (periodicColor (n := n)) (diagSum (n := n) s) := by
  unfold Balanced
  intro c
  rw [diagSum_color_card_eq, diagSum_card_eq]
  let lo := s + 1 - n
  let hi := min n (s + 1)
  change ((Finset.Ico lo hi).filter
      (fun j ↦ Fin.ofNat 3 (s - j + j / 3) = c)).card = (hi - lo) / 3
  have hlen3 : 3 ∣ hi - lo := by
    simpa [lo, hi, diagSum_card_eq] using hs
  by_cases hlen : hi - lo = 0
  · rw [Ico_eq_map_range, hlen]
    simp
  obtain ⟨q, hq⟩ := hlen3
  have hlohi : lo < hi := by omega
  have hn3 : 3 ∣ n := dvd_trans (by norm_num) h9
  obtain ⟨m, hm⟩ := hn3
  have hlo3 : 3 ∣ lo := by
    by_cases hsn : s + 1 ≤ n
    · have : lo = 0 := by simp [lo, Nat.sub_eq_zero_of_le hsn]
      simp [this]
    · have hns : n ≤ s + 1 := (Nat.lt_of_not_ge hsn).le
      have hhi : hi = n := by simp [hi, Nat.min_eq_left hns]
      refine ⟨m - q, ?_⟩
      omega
  obtain ⟨u, hu⟩ := hlo3
  have hbound : 3 * q ≤ (s - lo) + 1 := by omega
  rw [Ico_eq_map_range, Finset.filter_map, Finset.card_map, hq]
  calc
    ((Finset.range (3 * q)).filter
        ((fun j ↦ Fin.ofNat 3 (s - j + j / 3) = c) ∘
          addLeftEmbedding lo)).card =
        ((Finset.range (3 * q)).filter
          (fun t ↦ Fin.ofNat 3 ((s - lo) - t + lo / 3 + t / 3) = c)).card := by
      apply congrArg Finset.card
      ext t
      simp only [Finset.mem_filter, Finset.mem_range, Function.comp_apply,
        addLeftEmbedding_apply]
      have hcolor (ht : t < 3 * q) :
          Fin.ofNat 3 (s - (lo + t) + (lo + t) / 3) =
            Fin.ofNat 3 ((s - lo) - t + lo / 3 + t / 3) := by
        have hsub : s - (lo + t) = (s - lo) - t := by omega
        have hdiv : (lo + t) / 3 = lo / 3 + t / 3 := by omega
        rw [hsub, hdiv]
        simp [Nat.add_assoc]
      constructor
      · rintro ⟨ht, hc⟩
        exact ⟨ht, by rw [← hcolor ht]; exact hc⟩
      · rintro ⟨ht, hc⟩
        exact ⟨ht, by rw [hcolor ht]; exact hc⟩
    _ = q := desc_periodic_count (s - lo) (lo / 3) c q hbound
    _ = (3 * q) / 3 := by omega

lemma diagDiff_card_eq_nonneg (n δ : ℕ) :
    (diagDiff (n := n) (δ : ℤ)).card = n - δ := by
  classical
  calc
    (diagDiff (n := n) (δ : ℤ)).card = (Finset.range (n - δ)).card := by
      apply Finset.card_bij (fun p _ ↦ (p.2 : ℕ))
      · intro p hp
        simp only [diagDiff, Finset.mem_filter, Finset.mem_univ, true_and] at hp
        simp only [Finset.mem_range]
        omega
      · intro p hp q hq hpq
        simp only [diagDiff, Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
        apply Prod.ext
        · apply Fin.ext
          omega
        · apply Fin.ext
          exact hpq
      · intro j hj
        simp only [Finset.mem_range] at hj
        let p : Fin n × Fin n :=
          (⟨δ + j, by omega⟩, ⟨j, by omega⟩)
        refine ⟨p, ?_, rfl⟩
        simp [diagDiff, p]
    _ = n - δ := Finset.card_range _

lemma diagDiff_card_eq_neg (n δ : ℕ) :
    (diagDiff (n := n) (-(δ : ℤ))).card = n - δ := by
  classical
  calc
    (diagDiff (n := n) (-(δ : ℤ))).card = (Finset.range (n - δ)).card := by
      apply Finset.card_bij (fun p _ ↦ (p.1 : ℕ))
      · intro p hp
        simp only [diagDiff, Finset.mem_filter, Finset.mem_univ, true_and] at hp
        simp only [Finset.mem_range]
        omega
      · intro p hp q hq hpq
        simp only [diagDiff, Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
        apply Prod.ext
        · apply Fin.ext
          exact hpq
        · apply Fin.ext
          omega
      · intro i hi
        simp only [Finset.mem_range] at hi
        let p : Fin n × Fin n :=
          (⟨i, by omega⟩, ⟨δ + i, by omega⟩)
        refine ⟨p, ?_, rfl⟩
        simp [diagDiff, p]
    _ = n - δ := Finset.card_range _

lemma diagDiff_color_card_eq_nonneg (n δ : ℕ) (c : Letter) :
    ((diagDiff (n := n) (δ : ℤ)).filter
        (fun p ↦ periodicColor p.1 p.2 = c)).card =
      ((Finset.range (n - δ)).filter
        (fun j ↦ Fin.ofNat 3 (δ + j + j / 3) = c)).card := by
  classical
  apply Finset.card_bij (fun p _ ↦ (p.2 : ℕ))
  · intro p hp
    simp only [Finset.mem_filter] at hp ⊢
    simp only [diagDiff, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    refine ⟨?_, ?_⟩
    · simp only [Finset.mem_range]
      omega
    · have hval : (p.1 : ℕ) = δ + (p.2 : ℕ) := by omega
      simpa [periodicColor, hval, Nat.add_assoc] using hp.2
  · intro p hp q hq hpq
    simp only [Finset.mem_filter] at hp hq
    simp only [diagDiff, Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
    apply Prod.ext
    · apply Fin.ext
      omega
    · apply Fin.ext
      exact hpq
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj
    let p : Fin n × Fin n :=
      (⟨δ + j, by omega⟩, ⟨j, by omega⟩)
    refine ⟨p, ?_, rfl⟩
    simp only [Finset.mem_filter]
    constructor
    · simp [diagDiff, p]
    · simpa [periodicColor, p, Nat.add_assoc] using hj.2

lemma diagDiff_color_card_eq_neg (n δ : ℕ) (c : Letter) :
    ((diagDiff (n := n) (-(δ : ℤ))).filter
        (fun p ↦ periodicColor p.1 p.2 = c)).card =
      ((Finset.range (n - δ)).filter
        (fun i ↦ Fin.ofNat 3 (i + (δ + i) / 3) = c)).card := by
  classical
  apply Finset.card_bij (fun p _ ↦ (p.1 : ℕ))
  · intro p hp
    simp only [Finset.mem_filter] at hp ⊢
    simp only [diagDiff, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    refine ⟨?_, ?_⟩
    · simp only [Finset.mem_range]
      omega
    · have hval : (p.2 : ℕ) = δ + (p.1 : ℕ) := by omega
      simpa [periodicColor, hval] using hp.2
  · intro p hp q hq hpq
    simp only [Finset.mem_filter] at hp hq
    simp only [diagDiff, Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
    apply Prod.ext
    · apply Fin.ext
      exact hpq
    · apply Fin.ext
      omega
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    let p : Fin n × Fin n :=
      (⟨i, by omega⟩, ⟨δ + i, by omega⟩)
    refine ⟨p, ?_, rfl⟩
    simp only [Finset.mem_filter]
    constructor
    · simp [diagDiff, p]
    · simpa [periodicColor, p] using hi.2

lemma asc_periodic_count (A : ℕ) (c : Letter) (k : ℕ) :
    ((Finset.range (3 * k)).filter
      (fun j ↦ Fin.ofNat 3 (A + j + j / 3) = c)).card = k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [show 3 * (k + 1) = 3 * k + 3 by omega, Finset.range_add_eq_union,
        Finset.filter_union]
      rw [Finset.card_union_of_disjoint
        ((Finset.disjoint_range_addLeftEmbedding (3 * k) (Finset.range 3)).mono
          (Finset.filter_subset _ _) (Finset.filter_subset _ _))]
      rw [ih]
      have hblock :
          (((Finset.range 3).map (addLeftEmbedding (3 * k))).filter
            (fun j ↦ Fin.ofNat 3 (A + j + j / 3) = c)).card = 1 := by
        rw [Finset.filter_map, Finset.card_map]
        calc
          ((Finset.range 3).filter
              ((fun j ↦ Fin.ofNat 3 (A + j + j / 3) = c) ∘
                addLeftEmbedding (3 * k))).card =
              ((Finset.range 3).filter
                (fun j ↦ Fin.ofNat 3 (A + 4 * k + j) = c)).card := by
            congr 1
            ext j
            simp only [Finset.mem_filter, Finset.mem_range, Function.comp_apply,
              addLeftEmbedding_apply]
            have hcolor (hj : j < 3) :
                Fin.ofNat 3 (A + (3 * k + j) + (3 * k + j) / 3) =
                  Fin.ofNat 3 (A + 4 * k + j) := by
              have hdiv : (3 * k + j) / 3 = k := by omega
              congr 1
              omega
            constructor
            · rintro ⟨hj, hc⟩
              exact ⟨hj, by rw [← hcolor hj]; exact hc⟩
            · rintro ⟨hj, hc⟩
              exact ⟨hj, by rw [hcolor hj]; exact hc⟩
          _ = 1 := add_block_count (A + 4 * k) c
      rw [hblock]

lemma periodicColor_diagDiff (n : ℕ) (h9 : 9 ∣ n) (d : ℤ)
    (hdcard : 3 ∣ (diagDiff (n := n) d).card) :
    Balanced (periodicColor (n := n)) (diagDiff (n := n) d) := by
  unfold Balanced
  intro c
  by_cases hd : 0 ≤ d
  · let δ := d.toNat
    have hδ : (δ : ℤ) = d := Int.toNat_of_nonneg hd
    have hlen3 : 3 ∣ n - δ := by
      rw [← diagDiff_card_eq_nonneg n δ]
      simpa [hδ] using hdcard
    obtain ⟨q, hq⟩ := hlen3
    rw [← hδ, diagDiff_color_card_eq_nonneg, diagDiff_card_eq_nonneg, hq]
    calc
      ((Finset.range (3 * q)).filter
          (fun j ↦ Fin.ofNat 3 (δ + j + j / 3) = c)).card = q :=
        asc_periodic_count δ c q
      _ = 3 * q / 3 := by omega
  · let δ := (-d).toNat
    have hneg : 0 ≤ -d := by omega
    have hδpos : (δ : ℤ) = -d := Int.toNat_of_nonneg hneg
    have hδ : -(δ : ℤ) = d := by omega
    have hlen3 : 3 ∣ n - δ := by
      rw [← diagDiff_card_eq_neg n δ]
      simpa [hδ] using hdcard
    by_cases hlen : n - δ = 0
    · rw [← hδ, diagDiff_color_card_eq_neg, diagDiff_card_eq_neg, hlen]
      simp
    obtain ⟨q, hq⟩ := hlen3
    have hn3 : 3 ∣ n := dvd_trans (by norm_num) h9
    obtain ⟨m, hm⟩ := hn3
    have hδ3 : 3 ∣ δ := by
      refine ⟨m - q, ?_⟩
      omega
    obtain ⟨u, hu⟩ := hδ3
    rw [← hδ, diagDiff_color_card_eq_neg, diagDiff_card_eq_neg, hq]
    calc
      ((Finset.range (3 * q)).filter
          (fun i ↦ Fin.ofNat 3 (i + (δ + i) / 3) = c)).card =
          ((Finset.range (3 * q)).filter
            (fun i ↦ Fin.ofNat 3 (u + i + i / 3) = c)).card := by
        apply congrArg Finset.card
        ext i
        simp only [Finset.mem_filter, Finset.mem_range]
        have hcolor :
            Fin.ofNat 3 (i + (δ + i) / 3) = Fin.ofNat 3 (u + i + i / 3) := by
          have hdiv : (δ + i) / 3 = u + i / 3 := by omega
          rw [hdiv]
          congr 1
          omega
        constructor
        · rintro ⟨hi, hc⟩
          exact ⟨hi, by rw [← hcolor]; exact hc⟩
        · rintro ⟨hi, hc⟩
          exact ⟨hi, by rw [hcolor]; exact hc⟩
      _ = q := asc_periodic_count u c q
      _ = 3 * q / 3 := by omega

lemma periodicColor_row {n : ℕ} (r : Fin n) (h9 : 9 ∣ n) :
    Balanced periodicColor (row r) := by
  unfold Balanced
  intro c
  rw [row_eq_product]
  have hfilter :
      ({r} ×ˢ (Finset.univ : Finset (Fin n))).filter
          (fun p ↦ periodicColor p.1 p.2 = c) =
        {r} ×ˢ Finset.univ.filter (fun j ↦ periodicColor r j = c) := by
    ext p
    rcases p with ⟨i, j⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_singleton,
      Finset.mem_univ, and_true]
    constructor
    · rintro ⟨hi, hc⟩
      subst i
      exact ⟨rfl, trivial, hc⟩
    · rintro ⟨hi, hc⟩
      subst i
      exact ⟨rfl, hc.2⟩
  rw [hfilter]
  simp only [Finset.card_product, Finset.card_singleton, one_mul, Finset.card_univ,
    Fintype.card_fin]
  rw [← Finset.card_map Fin.valEmbedding,
    map_filter_periodicColor]
  obtain ⟨k, rfl⟩ := h9
  have hdiv : 9 * k / 3 = 3 * k := by omega
  rw [hdiv]
  exact row_periodic_count (r : ℕ) c k

lemma periodicColor_col {n : ℕ} (k : Fin n) (h9 : 9 ∣ n) :
    Balanced periodicColor (col k) := by
  unfold Balanced
  intro c
  rw [col_eq_product]
  have hfilter :
      ((Finset.univ : Finset (Fin n)) ×ˢ {k}).filter
          (fun p ↦ periodicColor p.1 p.2 = c) =
        Finset.univ.filter (fun i ↦ periodicColor i k = c) ×ˢ {k} := by
    ext p
    rcases p with ⟨i, j⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_singleton,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hj, hc⟩
      subst j
      exact ⟨hc, rfl⟩
    · rintro ⟨hc, hj⟩
      subst j
      exact ⟨rfl, hc⟩
  rw [hfilter]
  simp only [Finset.card_product, Finset.card_singleton, mul_one, Finset.card_univ,
    Fintype.card_fin]
  rw [← Finset.card_map Fin.valEmbedding,
    map_filter_periodicColor_col]
  obtain ⟨q, rfl⟩ := h9
  have hcount := add_periodic_count ((k : ℕ) / 3) c (3 * q)
  have hlen : 3 * (3 * q) = 9 * q := by omega
  rw [hlen] at hcount
  calc
    ((Finset.range (9 * q)).filter
        (fun i ↦ Fin.ofNat 3 (i + (k : ℕ) / 3) = c)).card = 3 * q := by
      simpa [Nat.add_comm] using hcount
    _ = 9 * q / 3 := by omega

lemma exists_modTable_of_nine_dvd (n : ℕ) (h9 : 9 ∣ n) :
    ∃ f : Fin n → Fin n → Letter, MODTable f := by
  refine ⟨periodicColor, ?_⟩
  exact ⟨fun r ↦ periodicColor_row r h9,
    fun k ↦ periodicColor_col k h9,
    fun s hs ↦ periodicColor_diagSum n h9 s hs,
    fun d hd ↦ periodicColor_diagDiff n h9 d hd⟩

lemma Balanced.three_dvd_card {f : Fin n → Fin n → Letter}
    {cells : Finset (Fin n × Fin n)} (h : Balanced f cells) : 3 ∣ cells.card := by
  have hsum := Finset.card_eq_sum_card_fiberwise
    (s := cells) (t := (Finset.univ : Finset Letter))
    (f := fun p ↦ f p.1 p.2) (by simp)
  have heq : cells.card = 3 * (cells.card / 3) := by
    calc
      cells.card = ∑ c : Letter, (cells.filter (fun p ↦ f p.1 p.2 = c)).card := by
        simpa using hsum
      _ = ∑ _c : Letter, cells.card / 3 := by
        apply Finset.sum_congr rfl
        intro c _
        exact h c
      _ = 3 * (cells.card / 3) := by simp
  exact ⟨cells.card / 3, heq⟩

lemma balanced_of_fibers {κ : Type*} [DecidableEq κ]
    (f : Fin n → Fin n → Letter) (cells : Finset (Fin n × Fin n))
    (keys : Finset κ) (g : Fin n × Fin n → κ)
    (hmap : ∀ p ∈ cells, g p ∈ keys)
    (hbalanced : ∀ x ∈ keys, Balanced f (cells.filter (fun p ↦ g p = x))) :
    Balanced f cells := by
  classical
  have htotal : cells.card =
      ∑ x ∈ keys, (cells.filter (fun p ↦ g p = x)).card :=
    Finset.card_eq_sum_card_fiberwise hmap
  have hfiber (x : κ) (hx : x ∈ keys) :
      (cells.filter (fun p ↦ g p = x)).card =
        3 * ((cells.filter (fun p ↦ g p = x)).card / 3) := by
    obtain ⟨q, hq⟩ := (hbalanced x hx).three_dvd_card
    omega
  have htotal' : cells.card =
      3 * ∑ x ∈ keys, (cells.filter (fun p ↦ g p = x)).card / 3 := by
    calc
      cells.card = ∑ x ∈ keys, (cells.filter (fun p ↦ g p = x)).card := htotal
      _ = ∑ x ∈ keys, 3 * ((cells.filter (fun p ↦ g p = x)).card / 3) := by
        apply Finset.sum_congr rfl
        exact hfiber
      _ = 3 * ∑ x ∈ keys, (cells.filter (fun p ↦ g p = x)).card / 3 := by
        rw [Finset.mul_sum]
  intro c
  have hcolorMap : ∀ p ∈ cells.filter (fun p ↦ f p.1 p.2 = c), g p ∈ keys := by
    intro p hp
    exact hmap p (Finset.mem_filter.mp hp).1
  calc
    (cells.filter (fun p ↦ f p.1 p.2 = c)).card =
        ∑ x ∈ keys,
          ((cells.filter (fun p ↦ f p.1 p.2 = c)).filter (fun p ↦ g p = x)).card :=
      Finset.card_eq_sum_card_fiberwise hcolorMap
    _ = ∑ x ∈ keys,
        ((cells.filter (fun p ↦ g p = x)).filter
          (fun p ↦ f p.1 p.2 = c)).card := by
      apply Finset.sum_congr rfl
      intro x _
      congr 1
      ext p
      simp only [Finset.mem_filter]
      tauto
    _ = ∑ x ∈ keys, (cells.filter (fun p ↦ g p = x)).card / 3 := by
      apply Finset.sum_congr rfl
      intro x hx
      exact hbalanced x hx c
    _ = cells.card / 3 := by omega

def vitalIndices (k : ℕ) : Finset (Fin (3 * k)) :=
  Finset.univ.filter (fun i ↦ Fin.ofNat 3 (i : ℕ) = 1)

def vitalRowCells (k : ℕ) : Finset (Fin (3 * k) × Fin (3 * k)) :=
  vitalIndices k ×ˢ Finset.univ

def vitalColCells (k : ℕ) : Finset (Fin (3 * k) × Fin (3 * k)) :=
  Finset.univ ×ˢ vitalIndices k

def vitalSumCells (k : ℕ) : Finset (Fin (3 * k) × Fin (3 * k)) :=
  Finset.univ.filter (fun p ↦ Fin.ofNat 3 ((p.1 : ℕ) + (p.2 : ℕ)) = 2)

def vitalDiffCells (k : ℕ) : Finset (Fin (3 * k) × Fin (3 * k)) :=
  Finset.univ.filter (fun p ↦ Fin.ofNat 3 (p.1 : ℕ) = Fin.ofNat 3 (p.2 : ℕ))

def centerCells (k : ℕ) : Finset (Fin (3 * k) × Fin (3 * k)) :=
  vitalIndices k ×ˢ vitalIndices k

def colorCount {n : ℕ} (f : Fin n → Fin n → Letter)
    (cells : Finset (Fin n × Fin n)) (c : Letter) : ℕ :=
  (cells.filter (fun p ↦ f p.1 p.2 = c)).card

def vitalSumKeys (k : ℕ) : Finset ℕ :=
  (Finset.range (6 * k)).filter (fun s ↦ Fin.ofNat 3 s = 2)

def vitalDiffKeys (k : ℕ) : Finset ℤ :=
  ((Finset.range (6 * k + 1)).map
    ⟨fun t : ℕ ↦ (t : ℤ) - (3 * k : ℤ), fun a b h ↦ by
      exact_mod_cast (sub_left_inj.mp h : (a : ℤ) = (b : ℤ))⟩).filter
      (fun d ↦ (3 : ℤ) ∣ d)

lemma card_filter_grid {n : ℕ} (P : Fin n → Fin n → Prop) [DecidableRel P] :
    ((Finset.univ : Finset (Fin n × Fin n)).filter (fun p ↦ P p.1 p.2)).card =
      ∑ i : Fin n, ((Finset.univ : Finset (Fin n)).filter (P i)).card := by
  classical
  let cells := (Finset.univ : Finset (Fin n × Fin n)).filter (fun p ↦ P p.1 p.2)
  have hmap : ∀ p ∈ cells, p.1 ∈ (Finset.univ : Finset (Fin n)) := by simp
  calc
    cells.card = ∑ i : Fin n, (cells.filter (fun p ↦ p.1 = i)).card := by
      simpa using Finset.card_eq_sum_card_fiberwise hmap
    _ = ∑ i : Fin n, ((Finset.univ : Finset (Fin n)).filter (P i)).card := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.card_bij (fun p _ ↦ p.2)
      · intro p hp
        simp only [cells, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
        simpa [hp.2] using hp.1
      · intro p hp q hq hpq
        simp only [cells, Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
        apply Prod.ext
        · exact hp.2.trans hq.2.symm
        · exact hpq
      · intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        exact ⟨(i, j), by simp [cells, hj], rfl⟩

lemma fin_add_count (k a : ℕ) (c : Letter) :
    ((Finset.univ : Finset (Fin (3 * k))).filter
      (fun j : Fin (3 * k) ↦ Fin.ofNat 3 (a + (j : ℕ)) = c)).card = k := by
  have hmap :
      ((Finset.univ : Finset (Fin (3 * k))).filter
        (fun j : Fin (3 * k) ↦ Fin.ofNat 3 (a + (j : ℕ)) = c)).map Fin.valEmbedding =
        (Finset.range (3 * k)).filter (fun j ↦ Fin.ofNat 3 (a + j) = c) := by
    ext j
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_range, Fin.valEmbedding_apply]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.isLt, hx⟩
    · rintro ⟨hj, hc⟩
      exact ⟨⟨j, hj⟩, hc, rfl⟩
  rw [← Finset.card_map Fin.valEmbedding, hmap]
  exact add_periodic_count a c k

lemma vitalIndices_card (k : ℕ) : (vitalIndices k).card = k := by
  simpa [vitalIndices] using fin_add_count k 0 (1 : Letter)

lemma vitalRowCells_card (k : ℕ) : (vitalRowCells k).card = 3 * k ^ 2 := by
  simp [vitalRowCells, vitalIndices_card]
  ring

lemma vitalColCells_card (k : ℕ) : (vitalColCells k).card = 3 * k ^ 2 := by
  simp [vitalColCells, vitalIndices_card]
  ring

lemma vitalSumCells_card (k : ℕ) : (vitalSumCells k).card = 3 * k ^ 2 := by
  calc
    (vitalSumCells k).card = ∑ i : Fin (3 * k),
        ((Finset.univ : Finset (Fin (3 * k))).filter
          (fun j : Fin (3 * k) ↦ Fin.ofNat 3 ((i : ℕ) + (j : ℕ)) = 2)).card := by
      exact card_filter_grid
        (fun i j : Fin (3 * k) ↦ Fin.ofNat 3 ((i : ℕ) + (j : ℕ)) = 2)
    _ =
        ∑ _i : Fin (3 * k), k := by
      apply Finset.sum_congr rfl
      intro i _
      exact fin_add_count k (i : ℕ) 2
    _ = 3 * k ^ 2 := by simp; ring

lemma vitalDiffCells_card (k : ℕ) : (vitalDiffCells k).card = 3 * k ^ 2 := by
  calc
    (vitalDiffCells k).card = ∑ i : Fin (3 * k),
        ((Finset.univ : Finset (Fin (3 * k))).filter
          (fun j : Fin (3 * k) ↦ Fin.ofNat 3 (i : ℕ) = Fin.ofNat 3 (j : ℕ))).card := by
      exact card_filter_grid
        (fun i j : Fin (3 * k) ↦ Fin.ofNat 3 (i : ℕ) = Fin.ofNat 3 (j : ℕ))
    _ =
        ∑ _i : Fin (3 * k), k := by
      apply Finset.sum_congr rfl
      intro i _
      simpa [eq_comm] using fin_add_count k 0 (Fin.ofNat 3 (i : ℕ))
    _ = 3 * k ^ 2 := by simp; ring

lemma three_dvd_diagSum_card (k s : ℕ) (hs : Fin.ofNat 3 s = 2) :
    3 ∣ (diagSum (n := 3 * k) s).card := by
  have hsmod : s % 3 = 2 := by
    simpa [Fin.ofNat] using congrArg Fin.val hs
  have hsdiv := Nat.div_add_mod s 3
  have hsucc : s + 1 = 3 * (s / 3 + 1) := by omega
  rw [diagSum_card_eq]
  by_cases hsmall : s + 1 ≤ 3 * k
  · refine ⟨s / 3 + 1, ?_⟩
    rw [Nat.min_eq_right hsmall]
    have hsub : s + 1 - 3 * k = 0 := Nat.sub_eq_zero_of_le hsmall
    omega
  by_cases hlarge : 2 * (3 * k) ≤ s + 1
  · refine ⟨0, ?_⟩
    rw [Nat.min_eq_left (by omega)]
    omega
  · refine ⟨2 * k - (s / 3 + 1), ?_⟩
    rw [Nat.min_eq_left (by omega)]
    omega

lemma three_dvd_diagDiff_card (k : ℕ) (d : ℤ) (hd : (3 : ℤ) ∣ d) :
    3 ∣ (diagDiff (n := 3 * k) d).card := by
  obtain ⟨z, hz⟩ := hd
  by_cases hdz : 0 ≤ d
  · let δ := d.toNat
    have hδ : (δ : ℤ) = d := Int.toNat_of_nonneg hdz
    have hz0 : 0 ≤ z := by omega
    let u := z.toNat
    have hu : (u : ℤ) = z := Int.toNat_of_nonneg hz0
    have hδu : δ = 3 * u := by omega
    rw [← hδ, diagDiff_card_eq_nonneg, hδu]
    exact ⟨k - u, by omega⟩
  · let δ := (-d).toNat
    have hneg : 0 ≤ -d := by omega
    have hδ : (δ : ℤ) = -d := Int.toNat_of_nonneg hneg
    have hz0 : 0 ≤ -z := by omega
    let u := (-z).toNat
    have hu : (u : ℤ) = -z := Int.toNat_of_nonneg hz0
    have hδu : δ = 3 * u := by omega
    have hdneg : d = -(δ : ℤ) := by omega
    rw [hdneg, diagDiff_card_eq_neg, hδu]
    exact ⟨k - u, by omega⟩

lemma finMod_eq_iff_three_dvd_sub (i j : ℕ) :
    Fin.ofNat 3 i = Fin.ofNat 3 j ↔ (3 : ℤ) ∣ (i : ℤ) - (j : ℤ) := by
  constructor
  · intro h
    have hmod : i % 3 = j % 3 := by
      simpa [Fin.ofNat] using congrArg Fin.val h
    have hi := Nat.div_add_mod i 3
    have hj := Nat.div_add_mod j 3
    refine ⟨(i / 3 : ℤ) - (j / 3 : ℤ), ?_⟩
    omega
  · rintro ⟨z, hz⟩
    apply Fin.ext
    simp only [Fin.val_ofNat]
    have hi := Nat.div_add_mod i 3
    have hj := Nat.div_add_mod j 3
    have himod := Nat.mod_lt i (by omega : 0 < 3)
    have hjmod := Nat.mod_lt j (by omega : 0 < 3)
    omega

lemma univ_balanced_of_rows {n : ℕ} (f : Fin n → Fin n → Letter)
    (hrows : ∀ r, Balanced f (row r)) :
    Balanced f (Finset.univ : Finset (Fin n × Fin n)) := by
  apply balanced_of_fibers f Finset.univ Finset.univ (fun p ↦ p.1)
  · simp
  · intro r _
    simpa [row] using hrows r

lemma vitalRowCells_balanced (k : ℕ) (f : Fin (3 * k) → Fin (3 * k) → Letter)
    (hrows : ∀ r, Balanced f (row r)) :
    Balanced f (vitalRowCells k) := by
  apply balanced_of_fibers f (vitalRowCells k) (vitalIndices k) (fun p ↦ p.1)
  · intro p hp
    exact (Finset.mem_product.mp hp).1
  · intro r hr
    have h := hrows r
    convert h using 1
    ext p
    rcases p with ⟨i, j⟩
    simp only [vitalRowCells, row, Finset.mem_product, Finset.mem_filter,
      Finset.mem_univ, and_true, true_and]
    constructor
    · exact fun hri ↦ hri.2
    · intro hri
      exact ⟨hri ▸ hr, hri⟩

lemma vitalColCells_balanced (k : ℕ) (f : Fin (3 * k) → Fin (3 * k) → Letter)
    (hcols : ∀ j, Balanced f (col j)) :
    Balanced f (vitalColCells k) := by
  apply balanced_of_fibers f (vitalColCells k) (vitalIndices k) (fun p ↦ p.2)
  · intro p hp
    exact (Finset.mem_product.mp hp).2
  · intro j hj
    have h := hcols j
    convert h using 1
    ext p
    rcases p with ⟨i, l⟩
    simp only [vitalColCells, col, Finset.mem_product, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · exact fun hjl ↦ hjl.2
    · intro hjl
      exact ⟨hjl ▸ hj, hjl⟩

lemma vitalSumCells_balanced (k : ℕ) (f : Fin (3 * k) → Fin (3 * k) → Letter)
    (hsums : ∀ s, 3 ∣ (diagSum (n := 3 * k) s).card → Balanced f (diagSum s)) :
    Balanced f (vitalSumCells k) := by
  apply balanced_of_fibers f (vitalSumCells k) (vitalSumKeys k)
    (fun p ↦ (p.1 : ℕ) + (p.2 : ℕ))
  · intro p hp
    simp only [vitalSumCells, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    simp only [vitalSumKeys, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hp⟩
  · intro s hs
    simp only [vitalSumKeys, Finset.mem_filter, Finset.mem_range] at hs
    have h := hsums s (three_dvd_diagSum_card k s hs.2)
    convert h using 1
    ext p
    rcases p with ⟨i, j⟩
    simp only [vitalSumCells, diagSum, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hcolor, hsum⟩
      exact hsum
    · intro hsum
      refine ⟨?_, hsum⟩
      simpa [hsum] using hs.2

lemma vitalDiffCells_balanced (k : ℕ) (f : Fin (3 * k) → Fin (3 * k) → Letter)
    (hdiffs : ∀ d, 3 ∣ (diagDiff (n := 3 * k) d).card → Balanced f (diagDiff d)) :
    Balanced f (vitalDiffCells k) := by
  apply balanced_of_fibers f (vitalDiffCells k) (vitalDiffKeys k)
    (fun p ↦ ((p.1 : ℕ) : ℤ) - ((p.2 : ℕ) : ℤ))
  · intro p hp
    simp only [vitalDiffCells, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    simp only [vitalDiffKeys, Finset.mem_filter, Finset.mem_map, Function.Embedding.coeFn_mk]
    refine ⟨?_, (finMod_eq_iff_three_dvd_sub (p.1 : ℕ) (p.2 : ℕ)).mp hp⟩
    let t := (p.1 : ℕ) + 3 * k - (p.2 : ℕ)
    refine ⟨t, ?_, ?_⟩
    · simp only [Finset.mem_range]
      omega
    · dsimp [t]
      omega
  · intro d hd
    simp only [vitalDiffKeys, Finset.mem_filter] at hd
    have h := hdiffs d (three_dvd_diagDiff_card k d hd.2)
    convert h using 1
    ext p
    rcases p with ⟨i, j⟩
    simp only [vitalDiffCells, diagDiff, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨_, hdiff⟩
      exact hdiff
    · intro hdiff
      refine ⟨?_, hdiff⟩
      apply (finMod_eq_iff_three_dvd_sub (i : ℕ) (j : ℕ)).mpr
      simpa [hdiff] using hd.2

lemma three_dvd_of_modTable (n : ℕ) (hn : 0 < n)
    (f : Fin n → Fin n → Letter) (hf : MODTable f) : 3 ∣ n := by
  let r : Fin n := ⟨0, hn⟩
  have h := (hf.1 r).three_dvd_card
  rw [row_eq_product] at h
  simpa using h

lemma vital_incidence_indicator (k : ℕ) (p : Fin (3 * k) × Fin (3 * k)) :
    (if p ∈ vitalRowCells k then 1 else 0) +
        (if p ∈ vitalColCells k then 1 else 0) +
        (if p ∈ vitalSumCells k then 1 else 0) +
        (if p ∈ vitalDiffCells k then 1 else 0) =
      1 + 3 * (if p ∈ centerCells k then 1 else 0) := by
  have hsum : Fin.ofNat 3 ((p.1 : ℕ) + (p.2 : ℕ)) =
      Fin.ofNat 3 (p.1 : ℕ) + Fin.ofNat 3 (p.2 : ℕ) := by
    apply Fin.ext
    simp [Fin.ofNat, Nat.add_mod, Fin.val_add]
  simp only [vitalRowCells, vitalColCells, vitalSumCells, vitalDiffCells, centerCells,
    vitalIndices, Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and,
    and_true]
  rw [hsum]
  generalize ha : Fin.ofNat 3 (p.1 : ℕ) = a
  generalize hb : Fin.ofNat 3 (p.2 : ℕ) = b
  fin_cases a <;> fin_cases b <;> decide

lemma colorCount_eq_sum_indicator {n : ℕ} (f : Fin n → Fin n → Letter)
    (cells : Finset (Fin n × Fin n)) (c : Letter) :
    colorCount f cells c =
      ∑ p : Fin n × Fin n, if p ∈ cells ∧ f p.1 p.2 = c then 1 else 0 := by
  unfold colorCount
  rw [Finset.card_eq_sum_ite (t := (Finset.univ : Finset (Fin n × Fin n))) (by simp)]
  simp only [Finset.mem_filter]

lemma vital_color_count_identity (k : ℕ) (f : Fin (3 * k) → Fin (3 * k) → Letter)
    (c : Letter) :
    colorCount f (vitalRowCells k) c + colorCount f (vitalColCells k) c +
        colorCount f (vitalSumCells k) c + colorCount f (vitalDiffCells k) c =
      colorCount f Finset.univ c + 3 * colorCount f (centerCells k) c := by
  simp only [colorCount_eq_sum_indicator]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hc : f p.1 p.2 = c
  · simp only [hc, and_true]
    simpa using vital_incidence_indicator k p
  · simp [hc]

lemma colorCount_eq_of_balanced_card {n q : ℕ} (f : Fin n → Fin n → Letter)
    (cells : Finset (Fin n × Fin n)) (c : Letter) (hbalanced : Balanced f cells)
    (hcard : cells.card = 3 * q) : colorCount f cells c = q := by
  unfold colorCount
  rw [hbalanced c, hcard]
  omega

lemma nine_dvd_of_modTable (n : ℕ) (hn : 0 < n)
    (f : Fin n → Fin n → Letter) (hf : MODTable f) : 9 ∣ n := by
  have hn3 := three_dvd_of_modTable n hn f hf
  obtain ⟨k, rfl⟩ := hn3
  rcases hf with ⟨hrows, hcols, hsums, hdiffs⟩
  have hrowBal := vitalRowCells_balanced k f hrows
  have hcolBal := vitalColCells_balanced k f hcols
  have hsumBal := vitalSumCells_balanced k f hsums
  have hdiffBal := vitalDiffCells_balanced k f hdiffs
  have hunivBal := univ_balanced_of_rows f hrows
  let c : Letter := 0
  have hrowCount : colorCount f (vitalRowCells k) c = k ^ 2 :=
    colorCount_eq_of_balanced_card f _ c hrowBal (vitalRowCells_card k)
  have hcolCount : colorCount f (vitalColCells k) c = k ^ 2 :=
    colorCount_eq_of_balanced_card f _ c hcolBal (vitalColCells_card k)
  have hsumCount : colorCount f (vitalSumCells k) c = k ^ 2 :=
    colorCount_eq_of_balanced_card f _ c hsumBal (vitalSumCells_card k)
  have hdiffCount : colorCount f (vitalDiffCells k) c = k ^ 2 :=
    colorCount_eq_of_balanced_card f _ c hdiffBal (vitalDiffCells_card k)
  have hunivCard :
      (Finset.univ : Finset (Fin (3 * k) × Fin (3 * k))).card = 3 * (3 * k ^ 2) := by
    simp
    ring
  have hunivCount : colorCount f Finset.univ c = 3 * k ^ 2 :=
    colorCount_eq_of_balanced_card f _ c hunivBal hunivCard
  have hcount := vital_color_count_identity k f c
  rw [hrowCount, hcolCount, hsumCount, hdiffCount, hunivCount] at hcount
  have hk2 : 3 ∣ k ^ 2 := by
    refine ⟨colorCount f (centerCells k) c, ?_⟩
    omega
  have hk : 3 ∣ k := Nat.prime_three.dvd_of_dvd_pow hk2
  obtain ⟨q, hq⟩ := hk
  exact ⟨q, by omega⟩

snip end

problem imo2016_p2 (n : ℕ) (hn : 0 < n) :
    n ∈ solution ↔ ∃ f : Fin n → Fin n → Letter, MODTable f := by
  constructor
  · exact exists_modTable_of_nine_dvd n
  · rintro ⟨f, hf⟩
    exact nine_dvd_of_modTable n hn f hf

end Imo2016P2
