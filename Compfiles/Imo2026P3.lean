/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Data.List.GetD
public import Mathlib.RingTheory.PicardGroup
public import ProblemExtraction

@[expose] public section

problem_file {
  tags := [.Combinatorics]
  problemImportedFrom :=
    "https://github.com/humanfia/imo2026"
}

/-!
# International Mathematical Olympiad 2026, Problem 3

Let n be a positive integer. Liu Bang and Xiang Yu have a stick of length 1
and want to divide it between themselves. Liu marks at most n points on the
stick, and then Xiang marks at most n points on the stick. The marked points
are distinct. Then, the stick is cut at all marked points, creating a number
of pieces. Afterwards, they take turns claiming any unclaimed piece of the
stick, with Liu going first. Each player's goal is to maximise the total
length of their own pieces.

For each n, determine the largest value c such that Liu may guarantee a total
length of at least c, regardless of Xiang's play.
-/

namespace Imo2026P3

noncomputable section

open scoped BigOperators

/-- The multiset of piece lengths obtained by cutting `[0,1]` at the points of a
finite set `S ⊆ (0,1)`.  We sort `S` ascending, prepend `0` and append `1`, and
take consecutive differences.  The result is a list of `|S| + 1` positive reals
summing to `1` (when `S ⊆ (0,1)`). -/
def pieceLengths (S : Finset ℝ) : List ℝ :=
  let l : List ℝ := (0 : ℝ) :: (S.sort (· ≤ ·)) ++ [1]
  List.zipWith (fun a b => b - a) l l.tail

/-- The sum of the entries of a list `L` at the (0-indexed) even positions, after
sorting `L` in non-increasing order.  These are the entries in the `1`st, `3`rd,
`5`th, … positions of the sorted (decreasing) list, i.e. the pieces claimed by
the first mover under the greedy claiming rule. -/
def firstPlayerShare (L : List ℝ) : ℝ :=
  let sorted := L.mergeSort (· ≥ ·)
  ((sorted.zipIdx.filter (fun p => p.2 % 2 = 0)).map (fun p => p.1)).sum

/-- `L(A,B)`: Liu Bang's total length, given Liu Bang's marks `A` and Xiang Yu's
marks `B`. -/
def L (A B : Finset ℝ) : ℝ :=
  firstPlayerShare (pieceLengths (A ∪ B))

/-- The set of admissible markings for a player: a finite subset of `(0,1)` of
size at most `n`.  We encode it as a `Finset ℝ` subject to the side conditions. -/
def AdmissibleMark (n : ℕ) (X : Finset ℝ) : Prop :=
  (↑X ⊆ Set.Ioo (0 : ℝ) 1) ∧ X.card ≤ n

/-- The value Liu Bang can guarantee.

`V n` is the supremum over Liu Bang's admissible markings `A` of the infimum,
over Xiang Yu's admissible markings `B` disjoint from `A`, of `L A B`. -/
def V (n : ℕ) : ℝ :=
  ⨆ A : {A : Finset ℝ // AdmissibleMark n A},
    ⨅ B : {B : Finset ℝ // AdmissibleMark n B ∧ Disjoint A.1 B}, L A.1 B.1

snip begin
/-! The claimed answer value `V(n) = 2^n / (2^(n+1) - 1)`. -/
snip end
determine answer (n : ℕ) : ℝ := (2 : ℝ) ^ n / ((2 : ℝ) ^ (n + 1) - 1)

end

snip begin
/-! ## Correctness statements for the definitions

These pin down that the encoded definitions behave as intended. -/

/-- The piece lengths of an admissible cut set sum to `1` (the total stick
length). -/
theorem pieceLengths_sum (S : Finset ℝ) (_hS : ↑S ⊆ Set.Ioo (0 : ℝ) 1) :
    (pieceLengths S).sum = 1 := by
  have tele : ∀ l : List ℝ,
      (List.zipWith (fun a b => b - a) l l.tail).sum = l.getLastD 0 - l.headD 0 := by
    intro l
    induction l with
    | nil => simp
    | cons x xs ih =>
      cases xs with
      | nil => simp
      | cons y ys =>
        have eq : List.zipWith (fun a b => b - a) (x :: y :: ys) (x :: y :: ys).tail
            = (y - x) :: List.zipWith (fun a b => b - a) (y :: ys) (y :: ys).tail := rfl
        rw [eq, List.sum_cons, ih]
        have h1 : (x :: y :: ys).getLastD 0 = (y :: ys).getLastD 0 := by
          simp only [List.getLastD_cons]
        have h2 : (x :: y :: ys).headD 0 = x := rfl
        have h3 : (y :: ys).headD 0 = y := rfl
        rw [h1, h2, h3]
        ring
  have h0 : ((0 : ℝ) :: (S.sort (· ≤ ·)) ++ [1]).getLastD 0 = 1 := List.getLastD_concat
  have hh : ((0 : ℝ) :: (S.sort (· ≤ ·)) ++ [1]).headD 0 = 0 := rfl
  have h : pieceLengths S = List.zipWith (fun a b => b - a)
      ((0 : ℝ) :: (S.sort (· ≤ ·)) ++ [1])
      (((0 : ℝ) :: (S.sort (· ≤ ·)) ++ [1]).tail) := rfl
  rw [h, tele, h0, hh]
  ring

/-- There are `|S| + 1` pieces. -/
theorem pieceLengths_length (S : Finset ℝ) :
    (pieceLengths S).length = S.card + 1 := by
  have h : pieceLengths S = List.zipWith (fun a b => b - a)
      ((0 : ℝ) :: (S.sort (· ≤ ·)) ++ [1])
      (((0 : ℝ) :: (S.sort (· ≤ ·)) ++ [1]).tail) := rfl
  rw [h, List.length_zipWith]
  simp [Finset.length_sort]

/-- Basic sanity bound: Liu Bang's share lies in `[0, 1]` for admissible cut
sets (it is a subset-sum of the piece lengths, which are nonnegative and sum to
`1`). -/
theorem L_mem_Icc (A B : Finset ℝ)
    (hA : ↑A ⊆ Set.Ioo (0 : ℝ) 1) (hB : ↑B ⊆ Set.Ioo (0 : ℝ) 1) :
    L A B ∈ Set.Icc (0 : ℝ) 1 := by
  have hS : ↑(A ∪ B) ⊆ Set.Ioo (0 : ℝ) 1 := by
    rw [Finset.coe_union]; exact Set.union_subset hA hB
  -- Every piece length is nonnegative: consecutive elements of
  -- `0 :: sort S ++ [1]` are nondecreasing, so the differences are ≥ 0.
  have NN : ∀ (s : List ℝ) (a : ℝ), s.Pairwise (· ≤ ·) → (∀ x ∈ s, a ≤ x) →
      (∀ x ∈ s, x ≤ 1) → a ≤ 1 →
      ∀ z ∈ List.zipWith (fun a b => b - a) (a :: s ++ [1]) ((a :: s ++ [1]).tail), 0 ≤ z := by
    intro s
    induction s with
    | nil =>
      intro a _ _ _ ha1 z hz
      have : z = 1 - a := by simpa using hz
      rw [this]; exact sub_nonneg.mpr ha1
    | cons b s' ih =>
      intro a hsorted hab hle ha1 z hz
      rw [List.pairwise_cons] at hsorted
      obtain ⟨hb, hs'⟩ := hsorted
      have eq : List.zipWith (fun a b => b - a) (a :: b :: s' ++ [1])
          ((a :: b :: s' ++ [1]).tail)
          = (b - a) :: List.zipWith (fun a b => b - a) (b :: s' ++ [1])
            ((b :: s' ++ [1]).tail) := rfl
      rw [eq, List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact sub_nonneg.mpr (hab b List.mem_cons_self)
      · exact ih b hs' (fun x hx => hb x hx)
          (fun x hx => hle x (List.mem_cons_of_mem _ hx)) (hle b List.mem_cons_self) z hz
  have pieces_nn : ∀ z ∈ pieceLengths (A ∪ B), 0 ≤ z := by
    intro z hz
    have h : pieceLengths (A ∪ B) = List.zipWith (fun a b => b - a)
        ((0 : ℝ) :: ((A ∪ B).sort (· ≤ ·)) ++ [1])
        (((0 : ℝ) :: ((A ∪ B).sort (· ≤ ·)) ++ [1]).tail) := rfl
    rw [h] at hz
    exact NN _ 0 (Finset.pairwise_sort _ _)
      (fun x hx => le_of_lt (hS ((Finset.mem_sort _).mp hx)).1)
      (fun x hx => le_of_lt (hS ((Finset.mem_sort _).mp hx)).2)
      zero_le_one z hz
  -- The first-player share is the sum of a sublist of the sorted pieces.
  have hsub : ∀ (l : List ℝ),
      List.Sublist ((l.zipIdx.filter (fun p => p.2 % 2 = 0)).map (fun p => p.1)) l := by
    intro l
    have h1 := List.Sublist.map Prod.fst
      (List.filter_sublist (l := l.zipIdx) (p := fun p => p.2 % 2 = 0))
    rw [List.zipIdx_map_fst 0 l] at h1
    exact h1
  set P := pieceLengths (A ∪ B) with hP
  set M := P.mergeSort (· ≥ ·) with hM
  have hMperm : List.Perm M P := List.mergeSort_perm _ _
  have hMnn : ∀ x ∈ M, 0 ≤ x := fun x hx => pieces_nn x (hMperm.mem_iff.mp hx)
  have hge0 : 0 ≤ ((M.zipIdx.filter (fun p => p.2 % 2 = 0)).map (fun p => p.1)).sum :=
    List.sum_nonneg (fun x hx => hMnn x ((hsub M).mem hx))
  have hle1 : ((M.zipIdx.filter (fun p => p.2 % 2 = 0)).map (fun p => p.1)).sum ≤ 1 := by
    have hs : ((M.zipIdx.filter (fun p => p.2 % 2 = 0)).map (fun p => p.1)).sum ≤ M.sum :=
      (hsub M).sum_le_sum hMnn
    have hsum : M.sum = 1 := by
      rw [hMperm.sum_eq]
      exact pieceLengths_sum _ hS
    rw [hsum] at hs
    exact hs
  have hL : L A B = ((M.zipIdx.filter (fun p => p.2 % 2 = 0)).map (fun p => p.1)).sum := rfl
  rw [hL]
  exact ⟨hge0, hle1⟩


open scoped BigOperators


noncomputable def interiorPartialSums (l : List ℝ) : List ℝ :=
  (l.scanl (· + ·) 0).tail.dropLast

noncomputable def cutsOfLengths (l : List ℝ) : Finset ℝ :=
  (interiorPartialSums l).toFinset

lemma scanl_mem_ge (l : List ℝ) (a : ℝ)
    (hnn : ∀ x ∈ l, 0 ≤ x) {y : ℝ} (hy : y ∈ l.scanl (· + ·) a) : a ≤ y := by
  induction l generalizing a with
  | nil =>
      simp only [List.scanl_nil, List.mem_singleton] at hy
      subst y
      exact le_rfl
  | cons x xs ih =>
      rw [List.scanl_cons] at hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact le_rfl
      · have hx : 0 ≤ x := hnn x List.mem_cons_self
        have htail : ∀ z ∈ xs, 0 ≤ z := fun z hz => hnn z (List.mem_cons_of_mem _ hz)
        exact le_of_add_le_of_nonneg_left (ih (a + x) htail hy) hx

lemma pairwise_scanl_lt (l : List ℝ) (a : ℝ)
    (hpos : ∀ x ∈ l, 0 < x) : (l.scanl (· + ·) a).Pairwise (· < ·) := by
  induction l generalizing a with
  | nil => simp
  | cons x xs ih =>
      rw [List.scanl_cons, List.pairwise_cons]
      have hx : 0 < x := hpos x List.mem_cons_self
      have htailpos : ∀ z ∈ xs, 0 < z :=
        fun z hz => hpos z (List.mem_cons_of_mem _ hz)
      refine ⟨?_, ih (a := a + x) htailpos⟩
      intro y hy
      have hyge : a + x ≤ y :=
        scanl_mem_ge xs (a + x) (fun z hz => (htailpos z hz).le) hy
      linarith

lemma zipWith_scanl_tail (l : List ℝ) (a : ℝ) :
    List.zipWith (fun x y => y - x) (l.scanl (· + ·) a)
      (l.scanl (· + ·) a).tail = l := by
  induction l generalizing a with
  | nil => simp
  | cons x xs ih =>
      rw [List.scanl_cons]
      simp only [List.tail_cons]
      have hq : xs.scanl (· + ·) (a + x) =
          (a + x) :: (xs.scanl (· + ·) (a + x)).tail := by
        cases xs <;> simp [List.scanl_cons]
      have ih' := ih (a := a + x)
      rw [hq] at ih' ⊢
      simp only [List.zipWith_cons_cons, List.cons.injEq]
      exact ⟨by ring, ih'⟩

lemma scanl_zipWith_diff (l : List ℝ) (a : ℝ) :
    (List.zipWith (fun x y => y - x) (a :: l) l).scanl (· + ·) a = a :: l := by
  induction l generalizing a with
  | nil => simp
  | cons x xs ih =>
      rw [List.zipWith_cons_cons, List.scanl_cons]
      have hax : a + (x - a) = x := by ring
      rw [hax, ih]

lemma zipWith_diff_pos_of_pairwise : ∀ q : List ℝ,
    q.Pairwise (· < ·) →
      ∀ x ∈ List.zipWith (fun a b => b - a) q q.tail, 0 < x := by
  intro q
  induction q with
  | nil => simp
  | cons a rest ih =>
      cases rest with
      | nil => simp
      | cons b t =>
          intro hq x hx
          have htail : (b :: t).Pairwise (· < ·) := (List.pairwise_cons.mp hq).2
          change x ∈ (b - a) ::
            List.zipWith (fun u v => v - u) (b :: t) (b :: t).tail at hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact sub_pos.mpr ((List.pairwise_cons.mp hq).1 b List.mem_cons_self)
          · exact ih htail x hx

lemma pieceLengths_pos (S : Finset ℝ) (hS : ↑S ⊆ Set.Ioo (0 : ℝ) 1) :
    ∀ x ∈ pieceLengths S, 0 < x := by
  let s := S.sort (· ≤ ·)
  let q : List ℝ := (0 : ℝ) :: s ++ [1]
  have hslt : s.Pairwise (· < ·) := Finset.sortedLT_sort S |>.pairwise
  have h0s : ∀ x ∈ s, (0 : ℝ) < x := by
    intro x hx
    exact (hS (Finset.mem_sort (· ≤ ·) |>.mp hx)).1
  have hs1 : ∀ x ∈ s, x < (1 : ℝ) := by
    intro x hx
    exact (hS (Finset.mem_sort (· ≤ ·) |>.mp hx)).2
  have hq : q.Pairwise (· < ·) := by
    unfold q
    rw [List.pairwise_append, List.pairwise_cons]
    refine ⟨⟨h0s, hslt⟩, by simp, ?_⟩
    intro x hx y hy
    have hy1 : y = 1 := by simpa using hy
    subst y
    rcases List.mem_cons.mp hx with rfl | hx
    · norm_num
    · exact hs1 x hx
  exact zipWith_diff_pos_of_pairwise q hq

lemma foldl_add_init (l : List ℝ) (a : ℝ) :
    List.foldl (· + ·) a l = a + l.sum := by
  induction l generalizing a with
  | nil => simp
  | cons x xs ih =>
      rw [List.foldl_cons, ih, List.sum_cons]
      ring

lemma scanl_last_eq_sum (l : List ℝ) (a : ℝ)
    (hscan : l.scanl (· + ·) a ≠ []) :
    (l.scanl (· + ·) a).getLast hscan = a + l.sum := by
  rw [List.getLast_scanl, foldl_add_init]

lemma interiorPartialSums_pairwise (l : List ℝ)
    (hpos : ∀ x ∈ l, 0 < x) :
    (interiorPartialSums l).Pairwise (· < ·) := by
  exact ((pairwise_scanl_lt l 0 hpos).sublist (List.tail_sublist _)).sublist
    (List.dropLast_sublist _)

lemma sort_cutsOfLengths (l : List ℝ) (hpos : ∀ x ∈ l, 0 < x) :
    (cutsOfLengths l).sort (· ≤ ·) = interiorPartialSums l := by
  apply (List.toFinset_sort (· ≤ ·) ?_).2
  · exact (interiorPartialSums_pairwise l hpos).imp fun h => h.le
  · exact (interiorPartialSums_pairwise l hpos).nodup

lemma boundaryList_eq_scanl (l : List ℝ) (hne : l ≠ []) (hsum : l.sum = 1) :
    (0 : ℝ) :: interiorPartialSums l ++ [1] = l.scanl (· + ·) 0 := by
  cases l with
  | nil => contradiction
  | cons x xs =>
      unfold interiorPartialSums
      rw [List.scanl_cons]
      simp only [List.tail_cons]
      have hneScan : xs.scanl (· + ·) (0 + x) ≠ [] := by simp
      have hlast : (xs.scanl (· + ·) (0 + x)).getLast hneScan = 1 := by
        rw [scanl_last_eq_sum]
        simpa [List.sum_cons] using hsum
      rw [List.cons_append]
      congr 1
      calc
        (xs.scanl (· + ·) (0 + x)).dropLast ++ [1] =
            (xs.scanl (· + ·) (0 + x)).dropLast ++
              [(xs.scanl (· + ·) (0 + x)).getLast hneScan] := by rw [hlast]
        _ = xs.scanl (· + ·) (0 + x) := List.dropLast_append_getLast hneScan

lemma pieceLengths_cutsOfLengths (l : List ℝ) (hne : l ≠ [])
    (hpos : ∀ x ∈ l, 0 < x) (hsum : l.sum = 1) :
    pieceLengths (cutsOfLengths l) = l := by
  unfold pieceLengths
  rw [sort_cutsOfLengths l hpos, boundaryList_eq_scanl l hne hsum]
  exact zipWith_scanl_tail l 0

lemma interiorPartialSums_pieceLengths (S : Finset ℝ) :
    interiorPartialSums (pieceLengths S) = S.sort (· ≤ ·) := by
  unfold interiorPartialSums pieceLengths
  let t : List ℝ := S.sort (· ≤ ·) ++ [1]
  change ((List.zipWith (fun a b => b - a) ((0 : ℝ) :: t) t).scanl
    (· + ·) 0).tail.dropLast = S.sort (· ≤ ·)
  rw [scanl_zipWith_diff t 0, List.tail_cons]
  simp [t]

lemma cutsOfLengths_pieceLengths (S : Finset ℝ) :
    cutsOfLengths (pieceLengths S) = S := by
  unfold cutsOfLengths
  rw [interiorPartialSums_pieceLengths, Finset.sort_toFinset]

lemma mem_interiorPartialSums_Ioo (l : List ℝ) (hne : l ≠ [])
    (hpos : ∀ x ∈ l, 0 < x) (hsum : l.sum = 1) {z : ℝ}
    (hz : z ∈ interiorPartialSums l) : z ∈ Set.Ioo (0 : ℝ) 1 := by
  have hp : ((0 : ℝ) :: interiorPartialSums l ++ [1]).Pairwise (· < ·) := by
    rw [boundaryList_eq_scanl l hne hsum]
    exact pairwise_scanl_lt l 0 hpos
  obtain ⟨hpLeft, -, hpCross⟩ := List.pairwise_append.mp hp
  have hzpos : 0 < z := (List.pairwise_cons.mp hpLeft).1 z hz
  have hzone : z < 1 := hpCross z (List.mem_cons_of_mem _ hz) 1 (by simp)
  exact ⟨hzpos, hzone⟩

lemma card_cutsOfLengths (l : List ℝ) (hne : l ≠ [])
    (hpos : ∀ x ∈ l, 0 < x) :
    (cutsOfLengths l).card + 1 = l.length := by
  unfold cutsOfLengths
  rw [List.toFinset_card_of_nodup (interiorPartialSums_pairwise l hpos).nodup]
  unfold interiorPartialSums
  rw [List.length_dropLast, List.length_tail, List.length_scanl]
  have hlen : 0 < l.length := List.length_pos_iff.mpr hne
  lia

lemma admissible_cutsOfLengths (n : ℕ) (l : List ℝ) (hne : l ≠ [])
    (hpos : ∀ x ∈ l, 0 < x) (hsum : l.sum = 1)
    (hlen : l.length ≤ n + 1) : AdmissibleMark n (cutsOfLengths l) := by
  constructor
  · intro z hz
    exact mem_interiorPartialSums_Ioo l hne hpos hsum
      (by simpa [cutsOfLengths] using hz)
  · have hcard := card_cutsOfLengths l hne hpos
    lia

lemma exists_reply_of_refinement (n : ℕ) (A : Finset ℝ) (l : List ℝ)
    (hne : l ≠ []) (hpos : ∀ x ∈ l, 0 < x) (hsum : l.sum = 1)
    (hsub : A ⊆ cutsOfLengths l)
    (hnew : (cutsOfLengths l).card - A.card ≤ n) :
    ∃ B : Finset ℝ, AdmissibleMark n B ∧ Disjoint A B ∧
      L A B = firstPlayerShare l := by
  let B := cutsOfLengths l \ A
  refine ⟨B, ?_, ?_, ?_⟩
  · constructor
    · intro z hz
      have hzCuts : z ∈ cutsOfLengths l := (Finset.mem_sdiff.mp hz).1
      exact mem_interiorPartialSums_Ioo l hne hpos hsum
        (by simpa [cutsOfLengths] using hzCuts)
    · simpa [B, Finset.card_sdiff, Finset.inter_eq_left.mpr hsub]
        using hnew
  · exact Finset.sdiff_disjoint.symm
  · unfold L
    rw [show A ∪ B = cutsOfLengths l from Finset.union_sdiff_of_subset hsub]
    rw [pieceLengths_cutsOfLengths l hne hpos hsum]

lemma exists_reply_of_refinement_length (n : ℕ) (A : Finset ℝ) (l : List ℝ)
    (hne : l ≠ []) (hpos : ∀ x ∈ l, 0 < x) (hsum : l.sum = 1)
    (hsub : A ⊆ cutsOfLengths l) (hlen : l.length ≤ A.card + n + 1) :
    ∃ B : Finset ℝ, AdmissibleMark n B ∧ Disjoint A B ∧
      L A B = firstPlayerShare l := by
  apply exists_reply_of_refinement n A l hne hpos hsum hsub
  have hcard := card_cutsOfLengths l hne hpos
  lia

lemma exists_reply_of_piece_refinement (n : ℕ) (A : Finset ℝ) (l : List ℝ)
    (hne : l ≠ []) (hpos : ∀ x ∈ l, 0 < x) (hsum : l.sum = 1)
    (href : cutsOfLengths (pieceLengths A) ⊆ cutsOfLengths l)
    (hlen : l.length ≤ A.card + n + 1) :
    ∃ B : Finset ℝ, AdmissibleMark n B ∧ Disjoint A B ∧
      L A B = firstPlayerShare l := by
  apply exists_reply_of_refinement_length n A l hne hpos hsum
  · simpa [cutsOfLengths_pieceLengths] using href
  · exact hlen


open scoped BigOperators


/-- The "greedy surplus" of a list: sum of adjacent pair differences, plus the
last entry if the length is odd.  For a decreasing list this equals
`2 * (even-position sum) - (total sum)`. -/
def surplus : List ℝ → ℝ
  | [] => 0
  | [x] => x
  | x :: y :: t => (x - y) + surplus t

/-- The sum of entries at even (0-indexed) positions. -/
def evenSum (l : List ℝ) : ℝ :=
  ((l.zipIdx.filter (fun p => p.2 % 2 = 0)).map Prod.fst).sum

lemma evenSum_zipIdx_offset' (l : List ℝ) (n m : ℕ) (h : n % 2 = m % 2) :
    ((l.zipIdx n).filter (fun p => p.2 % 2 = 0)).map Prod.fst
      = ((l.zipIdx m).filter (fun p => p.2 % 2 = 0)).map Prod.fst := by
  induction l generalizing n m with
  | nil => simp
  | cons a l ih =>
    rw [List.zipIdx_cons, List.zipIdx_cons, List.filter_cons, List.filter_cons]
    have h' : (n + 1) % 2 = (m + 1) % 2 := by lia
    by_cases hn : n % 2 = 0
    · have hm : m % 2 = 0 := by lia
      simp [hn, hm]
      exact ih (n + 1) (m + 1) h'
    · have hm : ¬ m % 2 = 0 := by lia
      simp [hn, hm]
      exact ih (n + 1) (m + 1) h'

lemma evenSum_cons2 (x y : ℝ) (t : List ℝ) :
    evenSum (x :: y :: t) = x + evenSum t := by
  unfold evenSum
  rw [List.zipIdx_cons, List.zipIdx_cons]
  simp only [List.filter_cons]
  have h0 : ((0 : ℕ) % 2 = 0) := by simp
  have h1 : ¬ ((1 : ℕ) % 2 = 0) := by simp
  simp [h1]
  rw [evenSum_zipIdx_offset' t 2 0 (by simp)]

lemma evenSum_nil : evenSum [] = 0 := rfl

lemma evenSum_singleton (x : ℝ) : evenSum [x] = x := by
  unfold evenSum
  simp [List.zipIdx_cons]

/-- For any list, `2 * evenSum - sum = surplus`.  No sortedness needed. -/
lemma two_mul_evenSum_sub_sum : ∀ l : List ℝ, 2 * evenSum l - l.sum = surplus l := by
  intro l
  induction l using surplus.induct with
  | case1 => simp [evenSum_nil, surplus]
  | case2 x => simp [evenSum_singleton, surplus]; ring
  | case3 x y t ih =>
    rw [List.sum_cons, List.sum_cons, evenSum_cons2, surplus]
    have := ih
    linarith [this]

/-- `firstPlayerShare` of a list equals `evenSum` of its decreasing sort. -/
lemma firstPlayerShare_eq_evenSum (l : List ℝ) :
    firstPlayerShare l = evenSum (l.mergeSort (· ≥ ·)) := rfl

/-- `firstPlayerShare` is invariant under permutation: both mergeSorts are
decreasing-sorted perms of each other, hence equal. -/
lemma firstPlayerShare_congr {l₁ l₂ : List ℝ} (h : l₁.Perm l₂) :
    firstPlayerShare l₁ = firstPlayerShare l₂ := by
  have hperm : List.Perm (l₁.mergeSort (· ≥ ·)) (l₂.mergeSort (· ≥ ·)) :=
    (List.mergeSort_perm _ _).trans (h.trans (List.mergeSort_perm _ _).symm)
  have hp1 : (l₁.mergeSort (· ≥ ·)).Pairwise (· ≥ ·) := List.pairwise_mergeSort' _ _
  have hp2 : (l₂.mergeSort (· ≥ ·)).Pairwise (· ≥ ·) := List.pairwise_mergeSort' _ _
  rw [firstPlayerShare_eq_evenSum, firstPlayerShare_eq_evenSum,
    hperm.eq_of_pairwise' hp1 hp2]


open scoped BigOperators


def pairDup (xs : List ℝ) : List ℝ := xs.flatMap fun x => [x, x]

lemma even_zip_sum_pairDup_aux (xs : List ℝ) (n : ℕ) (hn : n % 2 = 0) :
    ((((pairDup xs).zipIdx n).filter (fun p => p.2 % 2 = 0)).map (fun p => p.1)).sum
      = xs.sum := by
  induction xs generalizing n with
  | nil => simp [pairDup]
  | cons x xs ih =>
      have hn2 : (n + 1 + 1) % 2 = 0 := by lia
      have hn1 : (n + 1) % 2 ≠ 0 := by lia
      simp [pairDup, List.zipIdx_cons, hn, hn1]
      change ((((pairDup xs).zipIdx (n + 1 + 1)).filter
        (fun p => p.2 % 2 = 0)).map (fun p => p.1)).sum = xs.sum
      exact ih (n + 1 + 1) hn2

lemma even_zip_sum_pairDup (xs : List ℝ) :
    ((((pairDup xs).zipIdx).filter (fun p => p.2 % 2 = 0)).map (fun p => p.1)).sum
      = xs.sum :=
  even_zip_sum_pairDup_aux xs 0 rfl

lemma odd_zip_sum_pairDup_aux (xs : List ℝ) (n : ℕ) (hn : n % 2 = 1) :
    ((((pairDup xs).zipIdx n).filter (fun p => p.2 % 2 = 0)).map (fun p => p.1)).sum
      = xs.sum := by
  induction xs generalizing n with
  | nil => simp [pairDup]
  | cons x xs ih =>
      have hn1 : (n + 1) % 2 = 0 := by lia
      have hn2 : (n + 1 + 1) % 2 = 1 := by lia
      simp [pairDup, List.zipIdx_cons, hn, hn1]
      change ((((pairDup xs).zipIdx (n + 1 + 1)).filter
        (fun p => p.2 % 2 = 0)).map (fun p => p.1)).sum = xs.sum
      exact ih (n + 1 + 1) hn2

lemma zip_sum_pairDup_aux (xs : List ℝ) (n : ℕ) :
    ((((pairDup xs).zipIdx n).filter (fun p => p.2 % 2 = 0)).map (fun p => p.1)).sum
      = xs.sum := by
  by_cases hn : n % 2 = 0
  · exact even_zip_sum_pairDup_aux xs n hn
  · have hn' : n % 2 = 1 := by lia
    exact odd_zip_sum_pairDup_aux xs n hn'

lemma length_pairDup (xs : List ℝ) : (pairDup xs).length = 2 * xs.length := by
  induction xs with
  | nil => simp [pairDup]
  | cons x xs ih =>
      rw [show pairDup (x :: xs) = x :: x :: pairDup xs by rfl]
      simp [ih]
      lia

lemma even_zip_sum_pairs_singleton_pairs (xs ys : List ℝ) (r : ℝ) :
    (((((pairDup xs) ++ r :: pairDup ys).zipIdx).filter
      (fun p => p.2 % 2 = 0)).map (fun p => p.1)).sum = xs.sum + r + ys.sum := by
  rw [List.zipIdx_append]
  simp only [List.filter_append, List.map_append, List.sum_append]
  rw [zip_sum_pairDup_aux]
  have heven : (pairDup xs).length % 2 = 0 := by
    rw [length_pairDup]
    lia
  simp [heven]
  rw [zip_sum_pairDup_aux]
  ring

lemma pairwise_pairDup {xs : List ℝ} (hxs : xs.Pairwise (· ≥ ·)) :
    (pairDup xs).Pairwise (· ≥ ·) := by
  induction xs with
  | nil => simp [pairDup]
  | cons x xs ih =>
      rw [List.pairwise_cons] at hxs
      have hxdup : ∀ z ∈ pairDup xs, x ≥ z := by
        intro z hz
        simp only [pairDup, List.mem_flatMap] at hz
        obtain ⟨w, hw, hz⟩ := hz
        have hzw : z = w := by simpa using hz
        rw [hzw]
        exact hxs.1 w hw
      change (x :: x :: pairDup xs).Pairwise (· ≥ ·)
      rw [List.pairwise_cons, List.pairwise_cons]
      exact ⟨by
        intro z hz
        cases List.mem_cons.mp hz with
        | inl hzx => simp [hzx]
        | inr hzrest => exact hxdup z hzrest,
        hxdup, ih hxs.2⟩

lemma firstPlayerShare_pairDup_of_pairwise (xs : List ℝ)
    (hxs : xs.Pairwise (· ≥ ·)) : firstPlayerShare (pairDup xs) = xs.sum := by
  unfold firstPlayerShare
  rw [List.mergeSort_eq_self (r := (· ≥ ·)) (pairwise_pairDup hxs)]
  exact even_zip_sum_pairDup xs

lemma firstPlayerShare_pairs_singleton_pairs (xs ys : List ℝ) (r : ℝ)
    (hsorted : (pairDup xs ++ r :: pairDup ys).Pairwise (· ≥ ·)) :
    firstPlayerShare (pairDup xs ++ r :: pairDup ys) = xs.sum + r + ys.sum := by
  unfold firstPlayerShare
  rw [List.mergeSort_eq_self (r := (· ≥ ·)) hsorted]
  exact even_zip_sum_pairs_singleton_pairs xs ys r

open scoped BigOperators
open Finset


/-- Geometric sum of powers of two over `range m`. -/
lemma geom_two (m : ℕ) : ∑ j ∈ range m, (2 : ℝ) ^ j = 2 ^ m - 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, ih]
    ring

/-- The discrete punchline: a signed sum of distinct powers of two, with at
least one nonzero sign, has absolute value at least one. -/
lemma pow_two_punch {ι : Type} [Fintype ι] [DecidableEq ι]
    (p : ι → ℕ) (hp : Function.Injective p)
    (s : ι → ℝ) (hs : ∀ i, s i = 1 ∨ s i = -1 ∨ s i = 0) (hne : ∃ i, s i ≠ 0) :
    1 ≤ |∑ i, s i * 2 ^ p i| := by
  set supp := univ.filter (fun i => s i ≠ 0) with hsupp
  obtain ⟨i₀, hi₀⟩ := hne
  have hsupp_ne : supp.Nonempty := ⟨i₀, mem_filter.mpr ⟨mem_univ _, hi₀⟩⟩
  obtain ⟨a, ha, hmax⟩ := supp.exists_max_image p hsupp_ne
  have hsa : s a ≠ 0 := (mem_filter.mp ha).2
  have hsa1 : |s a| = 1 := by
    rcases hs a with h | h | h <;> simp [h] at hsa ⊢
  have hp2_pos : ∀ j, (0 : ℝ) < 2 ^ j := fun j => pow_pos (by norm_num) j
  -- split off the dominant term
  have hsplit : ∑ i, s i * 2 ^ p i
      = s a * 2 ^ p a + ∑ i ∈ univ.erase a, s i * 2 ^ p i := by
    rw [← add_sum_erase univ _ (mem_univ a)]
  -- the rest is supported on `supp.erase a`
  have hrest0 : ∑ i ∈ univ.erase a, s i * 2 ^ p i
      = ∑ i ∈ supp.erase a, s i * 2 ^ p i := by
    symm
    apply sum_subset
    · intro i hi
      rw [mem_erase] at hi ⊢
      exact ⟨hi.1, mem_univ i⟩
    · intro i hi hni
      rw [mem_erase, hsupp, mem_filter, not_and_or] at hni
      have hsi : s i = 0 := by
        rcases hni with h | h
        · exact absurd (mem_erase.mp hi).1 h
        · by_contra h0
          exact h ⟨mem_univ i, h0⟩
      rw [hsi]
      simp
  -- bound the rest by the geometric sum of smaller powers
  have hrest_le : |∑ i ∈ supp.erase a, s i * 2 ^ p i| ≤ 2 ^ p a - 1 := by
    have h1 : |∑ i ∈ supp.erase a, s i * 2 ^ p i|
        ≤ ∑ i ∈ supp.erase a, 2 ^ p i := by
      refine (abs_sum_le_sum_abs _ _).trans ?_
      apply sum_le_sum
      intro i hi
      have hsi1 : |s i| ≤ 1 := by
        rcases hs i with h | h | h <;> simp [h]
      rw [abs_mul, abs_of_pos (hp2_pos _)]
      exact (mul_le_iff_le_one_left (hp2_pos (p i))).mpr hsi1
    refine h1.trans ?_
    rw [← sum_image (fun x _ y _ h => hp h)]
    have hsub : (supp.erase a).image p ⊆ range (p a) := by
      intro j hj
      rw [mem_image] at hj
      obtain ⟨i, hi, rfl⟩ := hj
      rw [mem_erase] at hi
      rw [mem_range]
      have hle : p i ≤ p a := hmax i hi.2
      have hne : p i ≠ p a := fun h => hi.1 (hp h)
      lia
    refine (sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => le_of_lt (hp2_pos j))).trans
      ?_
    rw [geom_two]
  -- assemble
  have hT : |s a * 2 ^ p a| = 2 ^ p a := by
    rw [abs_mul, hsa1, abs_of_pos (hp2_pos _), one_mul]
  have key : |s a * 2 ^ p a|
      ≤ |∑ i, s i * 2 ^ p i| + |∑ i ∈ supp.erase a, s i * 2 ^ p i| := by
    have h1 : s a * 2 ^ p a
        = (∑ i, s i * 2 ^ p i) - ∑ i ∈ supp.erase a, s i * 2 ^ p i := by
      rw [hsplit, ← hrest0]
      ring
    rw [h1, sub_eq_add_neg, ← abs_neg (∑ i ∈ supp.erase a, s i * 2 ^ p i)]
    exact abs_add_le _ _
  linarith [key, hrest_le, hT, hp2_pos (p a)]


open scoped BigOperators


noncomputable def codexDenom (n : ℕ) : ℝ := (2 : ℝ) ^ (n + 1) - 1

noncomputable def codexDyadicWeights (n : ℕ) : List ℝ :=
  (List.range (n + 1)).map fun i => (2 : ℝ) ^ i / codexDenom n

lemma codex_list_geom_two (m : ℕ) :
    ((List.range m).map fun i => (2 : ℝ) ^ i).sum = 2 ^ m - 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [List.range_succ, List.map_append, List.sum_append, ih]
      simp
      ring

lemma codex_sum_map_div (l : List ℝ) (d : ℝ) :
    (l.map fun x => x / d).sum = l.sum / d := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      rw [List.map_cons, List.sum_cons, List.sum_cons, ih]
      ring

lemma codexDenom_pos (n : ℕ) : 0 < codexDenom n := by
  unfold codexDenom
  have hpow : (1 : ℝ) < 2 ^ (n + 1) := by
    exact one_lt_pow₀ (by norm_num) (by lia)
  linarith

lemma codexDyadicWeights_pos (n : ℕ) :
    ∀ x ∈ codexDyadicWeights n, 0 < x := by
  intro x hx
  simp only [codexDyadicWeights, List.mem_map, List.mem_range] at hx
  obtain ⟨i, -, rfl⟩ := hx
  exact div_pos (pow_pos (by norm_num) _) (codexDenom_pos n)

lemma codexDyadicWeights_length (n : ℕ) :
    (codexDyadicWeights n).length = n + 1 := by
  simp [codexDyadicWeights]

lemma codexDyadicWeights_ne_nil (n : ℕ) : codexDyadicWeights n ≠ [] := by
  intro h
  have := congrArg List.length h
  rw [codexDyadicWeights_length] at this
  simp at this

lemma codexDyadicWeights_sum (n : ℕ) : (codexDyadicWeights n).sum = 1 := by
  unfold codexDyadicWeights
  rw [show (List.range (n + 1)).map (fun i => (2 : ℝ) ^ i / codexDenom n) =
      ((List.range (n + 1)).map fun i => (2 : ℝ) ^ i).map
        (fun x => x / codexDenom n) by simp [List.map_map]]
  rw [codex_sum_map_div, codex_list_geom_two]
  change codexDenom n / codexDenom n = 1
  exact div_self (ne_of_gt (codexDenom_pos n))

noncomputable def codexLowerCuts (n : ℕ) : Finset ℝ :=
  cutsOfLengths (codexDyadicWeights n)

lemma codexLowerCuts_admissible (n : ℕ) : AdmissibleMark n (codexLowerCuts n) := by
  exact admissible_cutsOfLengths n (codexDyadicWeights n)
    (codexDyadicWeights_ne_nil n) (codexDyadicWeights_pos n)
    (codexDyadicWeights_sum n) (by rw [codexDyadicWeights_length])

lemma codexLowerCuts_pieces (n : ℕ) :
    pieceLengths (codexLowerCuts n) = codexDyadicWeights n := by
  exact pieceLengths_cutsOfLengths (codexDyadicWeights n)
    (codexDyadicWeights_ne_nil n) (codexDyadicWeights_pos n)
    (codexDyadicWeights_sum n)


open scoped BigOperators

namespace CodexMod3

noncomputable def incidence {V E : Type*} [Fintype V] [Fintype E]
    (src dst : E → V) : (V → ZMod 3) →ₗ[ZMod 3] (E → ZMod 3) where
  toFun s e := s (src e) + s (dst e)
  map_add' s t := by
    funext e
    simp only [Pi.add_apply]
    ring
  map_smul' c s := by
    funext e
    simp only [Pi.smul_apply, RingHom.id_apply]
    ring

theorem exists_mod3_kernel {V E : Type*} [Fintype V] [Fintype E]
    (src dst : E → V) (hcard : Fintype.card E < Fintype.card V) :
    ∃ s : V → ZMod 3, s ≠ 0 ∧ ∀ e, s (src e) + s (dst e) = 0 := by
  let T := incidence src dst
  have hrank : Module.finrank (ZMod 3) (E → ZMod 3) <
      Module.finrank (ZMod 3) (V → ZMod 3) := by
    simpa only [Module.finrank_pi] using hcard
  have hker : LinearMap.ker T ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt hrank
  obtain ⟨s, hsT, hs0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  refine ⟨s, hs0, ?_⟩
  have hTs : T s = 0 := LinearMap.mem_ker.mp hsT
  intro e
  have := congrFun hTs e
  change s (src e) + s (dst e) = 0 at this
  exact this

def sign3 (z : ZMod 3) : ℝ :=
  if z = 0 then 0 else if z = 1 then 1 else -1

theorem sign3_cases (z : ZMod 3) : sign3 z = 0 ∨ sign3 z = 1 ∨ sign3 z = -1 := by
  by_cases h0 : z = 0
  · simp [sign3, h0]
  · by_cases h1 : z = 1
    · simp [sign3, h1]
    · simp [sign3, h0, h1]

theorem sign3_ne_zero {z : ZMod 3} (hz : z ≠ 0) : sign3 z ≠ 0 := by
  simp only [sign3, hz, ite_false]
  split <;> norm_num

theorem zmod3_cases (z : ZMod 3) : z = 0 ∨ z = 1 ∨ z = -1 := by
  fin_cases z
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · apply Or.inr
    apply Or.inr
    apply ZMod.val_injective 3
    rw [ZMod.val_neg_one]
    exact ZMod.val_natCast_of_lt (n := 3) (a := 2) (by lia)

theorem sign3_add_eq_zero {x y : ZMod 3} (h : x + y = 0) :
    sign3 x + sign3 y = 0 := by
  have hy : y = -x := by linear_combination h
  rw [hy]
  have hm0 : (-1 : ZMod 3) ≠ 0 := by decide
  have hm1 : (-1 : ZMod 3) ≠ 1 := by decide
  rcases zmod3_cases x with rfl | rfl | rfl
  · simp [sign3]
  · simp [sign3, hm0, hm1]
  · simp [sign3, hm0, hm1]

theorem exists_real_signing {V E : Type*} [Fintype V] [Fintype E]
    (src dst : E → V) (hcard : Fintype.card E < Fintype.card V) :
    ∃ s : V → ℝ,
      (∀ v, s v = 0 ∨ s v = 1 ∨ s v = -1) ∧
      (∃ v, s v ≠ 0) ∧
      ∀ e, s (src e) + s (dst e) = 0 := by
  obtain ⟨t, ht0, htE⟩ := exists_mod3_kernel src dst hcard
  have htne : ∃ v, t v ≠ 0 := by
    by_contra h
    push Not at h
    apply ht0
    funext v
    exact h v
  refine ⟨fun v => sign3 (t v), (fun v => sign3_cases (t v)), ?_, ?_⟩
  · obtain ⟨v, hv⟩ := htne
    exact ⟨v, sign3_ne_zero hv⟩
  · exact fun e => sign3_add_eq_zero (htE e)

end CodexMod3

open scoped BigOperators

variable {α β : Type*} {ι : Type*}

def pairUp : List α → List (α × α)
  | a :: b :: t => (a, b) :: pairUp t
  | _ => []

def unpaired : List α → Option α
  | [] => none
  | [a] => some a
  | _ :: _ :: t => unpaired t

def unpair : List (α × α) → List α
  | [] => []
  | (a, b) :: t => a :: b :: unpair t

theorem length_pairUp : ∀ l : List α, (pairUp l).length = l.length / 2 := by
  intro l
  induction l using pairUp.induct with
  | case1 a b t ih =>
      simp only [pairUp, List.length_cons, ih]
      lia
  | case2 l h =>
      cases l with
      | nil => simp [pairUp]
      | cons a t =>
          cases t with
          | nil => simp [pairUp]
          | cons b u => exact (h a b u rfl).elim

theorem pairUp_sum (f : α → ℝ) : ∀ l : List α,
    (l.map f).sum = ((pairUp l).map (fun p => f p.1 + f p.2)).sum +
      (unpaired l).elim 0 f := by
  intro l
  induction l using pairUp.induct with
  | case1 a b t ih => simp [pairUp, unpaired, ih]; ring
  | case2 l h =>
      cases l with
      | nil => simp [pairUp, unpaired]
      | cons a t =>
          cases t with
          | nil => simp [pairUp, unpaired]
          | cons b u => exact (h a b u rfl).elim

theorem surplus_eq_pairUp : ∀ l : List ℝ,
    surplus l = ((pairUp l).map (fun p => p.1 - p.2)).sum +
      (unpaired l).getD 0 := by
  intro l
  induction l using pairUp.induct with
  | case1 a b t ih => simp [surplus, pairUp, unpaired, ih]; ring
  | case2 l h =>
      cases l with
      | nil => simp [surplus, pairUp, unpaired]
      | cons a t =>
          cases t with
          | nil => simp [surplus, pairUp, unpaired]
          | cons b u => exact (h a b u rfl).elim

theorem pairUp_rel {R : α → α → Prop} {l : List α} (h : l.Pairwise R) :
    ∀ p ∈ pairUp l, R p.1 p.2 := by
  induction l using pairUp.induct with
  | case1 a b t ih =>
      rw [List.pairwise_cons] at h
      simp only [pairUp, List.mem_cons]
      rintro p (rfl | hp)
      · exact h.1 b (by simp)
      · exact ih h.2.tail p hp
  | case2 l hshape =>
      cases l with
      | nil => simp [pairUp]
      | cons a t =>
          cases t with
          | nil => simp [pairUp]
          | cons b u => exact (hshape a b u rfl).elim

theorem pairUp_map (f : α → β) : ∀ l : List α,
    pairUp (l.map f) = (pairUp l).map (fun p => (f p.1, f p.2)) := by
  intro l
  induction l using pairUp.induct with
  | case1 a b t ih => simp [pairUp, ih]
  | case2 l hshape =>
      cases l with
      | nil => simp [pairUp]
      | cons a t =>
          cases t with
          | nil => simp [pairUp]
          | cons b u => exact (hshape a b u rfl).elim

theorem unpaired_map (f : α → β) : ∀ l : List α,
    unpaired (l.map f) = (unpaired l).map f := by
  intro l
  induction l using pairUp.induct with
  | case1 a b t ih => simpa [unpaired] using ih
  | case2 l hshape =>
      cases l with
      | nil => simp [unpaired]
      | cons a t =>
          cases t with
          | nil => simp [unpaired]
          | cons b u => exact (hshape a b u rfl).elim

theorem mem_of_unpaired_eq_some {a : α} : ∀ {l : List α},
    unpaired l = some a → a ∈ l := by
  intro l
  induction l using pairUp.induct with
  | case1 b c t ih =>
      intro h
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (ih h))
  | case2 l hshape =>
      cases l with
      | nil => simp [unpaired]
      | cons b t =>
          cases t with
          | nil =>
              intro h
              simp [unpaired] at h
              simp [h]
          | cons c u => exact (hshape b c u rfl).elim

def labelWeight [DecidableEq ι] (l : List (ℝ × ι)) (v : ι) : ℝ :=
  ((l.filter (fun z => z.2 = v)).map Prod.fst).sum

theorem labelWeight_cons [DecidableEq ι] (z : ℝ × ι) (t : List (ℝ × ι)) (v : ι) :
    labelWeight (z :: t) v =
      (if z.2 = v then z.1 else 0) + labelWeight t v := by
  by_cases h : z.2 = v <;> simp [labelWeight, h]

theorem labelWeight_perm [DecidableEq ι] {l₁ l₂ : List (ℝ × ι)}
    (h : l₁.Perm l₂) (v : ι) : labelWeight l₁ v = labelWeight l₂ v := by
  unfold labelWeight
  exact ((h.filter (fun z => z.2 = v)).map Prod.fst).sum_eq

theorem labelWeight_scale [DecidableEq ι] (D : ℝ) : ∀ l : List (ℝ × ι), ∀ v,
    labelWeight (l.map (fun z => (D * z.1, z.2))) v = D * labelWeight l v := by
  intro l
  induction l with
  | nil => simp [labelWeight]
  | cons z t ih =>
      intro v
      rw [List.map_cons, labelWeight_cons, labelWeight_cons, ih]
      by_cases h : z.2 = v <;> simp [h]
      ring

theorem surplus_scale (D : ℝ) : ∀ l : List ℝ,
    surplus (l.map (fun x => D * x)) = D * surplus l := by
  intro l
  induction l using surplus.induct with
  | case1 => simp [surplus]
  | case2 x => simp [surplus]
  | case3 x y t ih => simp [surplus, ih]; ring

theorem sum_sign_labelWeight {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → ℝ) : ∀ l : List (ℝ × ι),
    (∑ v, s v * labelWeight l v) =
      (l.map (fun z => s z.2 * z.1)).sum := by
  intro l
  induction l with
  | nil => simp [labelWeight]
  | cons z t ih =>
      calc
        (∑ v, s v * labelWeight (z :: t) v) =
            ∑ v, s v * ((if z.2 = v then z.1 else 0) + labelWeight t v) := by
              apply Finset.sum_congr rfl
              intro v _
              rw [labelWeight_cons]
        _ = (∑ v, s v * (if z.2 = v then z.1 else 0)) +
              ∑ v, s v * labelWeight t v := by
              simp_rw [mul_add]
              exact Finset.sum_add_distrib
        _ = s z.2 * z.1 + ∑ v, s v * labelWeight t v := by
              congr 1
              simpa only [mul_ite, mul_zero, Finset.mem_univ, ite_true] using
                (Finset.sum_ite_eq (Finset.univ : Finset ι) z.2
                  (fun v => s v * z.1))
        _ = s z.2 * z.1 + (t.map (fun z => s z.2 * z.1)).sum := by rw [ih]
        _ = ((z :: t).map (fun z => s z.2 * z.1)).sum := by simp

theorem fin_sum_get_map {α M : Type*} [AddCommMonoid M]
    (l : List α) (f : α → M) :
    (∑ i : Fin l.length, f (l.get i)) = (l.map f).sum := by
  rw [← List.sum_ofFn]
  exact congrArg List.sum (List.ofFn_getElem_eq_map l f)

theorem sum_sign_weight_pairUp {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → ℝ) (l : List (ℝ × ι)) :
    (∑ v, s v * labelWeight l v) =
      ((pairUp l).map
        (fun p => s p.1.2 * p.1.1 + s p.2.2 * p.2.1)).sum +
      (unpaired l).elim 0 (fun z => s z.2 * z.1) := by
  rw [sum_sign_labelWeight]
  exact pairUp_sum (fun z => s z.2 * z.1) l

theorem abstract_lower {ι : Type} [Fintype ι] [DecidableEq ι]
    (p : ι → ℕ) (hp : Function.Injective p)
    (l : List (ℝ × ι))
    (hsorted : l.Pairwise (fun a b => a.1 ≥ b.1))
    (hnonneg : ∀ z ∈ l, 0 ≤ z.1)
    (hlen : l.length < 2 * Fintype.card ι)
    (hweight : ∀ i, labelWeight l i = (2 : ℝ) ^ p i) :
    1 ≤ surplus (l.map Prod.fst) := by
  let P := pairUp l
  let src : Fin P.length → ι := fun e => (P.get e).1.2
  let dst : Fin P.length → ι := fun e => (P.get e).2.2
  let x : Fin P.length → ℝ := fun e => (P.get e).1.1
  let y : Fin P.length → ℝ := fun e => (P.get e).2.1
  have hcardP : Fintype.card (Fin P.length) < Fintype.card ι := by
    simp only [Fintype.card_fin]
    change (pairUp l).length < Fintype.card ι
    rw [length_pairUp]
    lia
  obtain ⟨s, hs, hsne, hsedge⟩ :=
    CodexMod3.exists_real_signing src dst hcardP
  let rem : ℝ := (unpaired l).elim 0 (fun z => s z.2 * z.1)
  let r : ℝ := (unpaired (l.map Prod.fst)).getD 0
  have hfull : (∑ v, s v * labelWeight l v) =
      (∑ e, (s (src e) * x e + s (dst e) * y e)) + rem := by
    have hpair := sum_sign_weight_pairUp s l
    calc
      (∑ v, s v * labelWeight l v) =
          (P.map (fun q => s q.1.2 * q.1.1 + s q.2.2 * q.2.1)).sum + rem := by
            simpa [P, rem] using hpair
      _ = (∑ e : Fin P.length,
          (fun q => s q.1.2 * q.1.1 + s q.2.2 * q.2.1) (P.get e)) + rem := by
            congr 1
            exact (fin_sum_get_map P
              (fun q => s q.1.2 * q.1.1 + s q.2.2 * q.2.1)).symm
      _ = (∑ e, (s (src e) * x e + s (dst e) * y e)) + rem := by rfl
  have hedge_bound :
      |∑ e, (s (src e) * x e + s (dst e) * y e)| ≤
        ∑ e, |x e - y e| := by
    calc
      |∑ e, (s (src e) * x e + s (dst e) * y e)| =
          |∑ e, s (src e) * (x e - y e)| := by
            congr 1
            apply Finset.sum_congr rfl
            intro e _
            have he' : s (dst e) = -s (src e) := by linarith [hsedge e]
            rw [he']
            ring
      _ ≤ ∑ e, |s (src e) * (x e - y e)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ e, |x e - y e| := by
        apply Finset.sum_le_sum
        intro e _
        rcases hs (src e) with h | h | h <;> rw [h] <;> simp [abs_sub_comm]
  have hrem_bound : |rem| ≤ r := by
    cases hu : unpaired l with
    | none => simp [rem, r, unpaired_map, hu]
    | some z =>
        have hzmem : z ∈ l := mem_of_unpaired_eq_some hu
        have hz0 : 0 ≤ z.1 := hnonneg z hzmem
        dsimp [rem, r]
        rw [hu, Option.elim_some, unpaired_map, hu]
        simp only [Option.map_some, Option.getD_some]
        rcases hs z.2 with h | h | h
        · rw [h]
          simpa using hz0
        · rw [h]
          simp [abs_of_nonneg hz0]
        · rw [h]
          simp [abs_of_nonneg hz0]
  have hbound : |∑ v, s v * labelWeight l v| ≤
      (∑ e, |x e - y e|) + r := by
    rw [hfull]
    exact (abs_add_le _ _).trans (add_le_add hedge_bound hrem_bound)
  have hspow : ∀ i, s i = 1 ∨ s i = -1 ∨ s i = 0 := fun i => or_rotate.mp (hs i)
  have hpunch := pow_two_punch (ι := ι) p hp s hspow hsne
  have hsumpow :
      (∑ i, s i * labelWeight l i) = ∑ i, s i * 2 ^ p i :=
    Finset.sum_congr rfl fun i _ => by rw [hweight]
  rw [hsumpow] at hbound
  have hedge_nonneg : ∀ q ∈ P, 0 ≤ q.1.1 - q.2.1 := by
    intro q hq
    exact sub_nonneg.mpr (pairUp_rel hsorted q (by simpa [P] using hq))
  have hright : (∑ e, |x e - y e|) + r = surplus (l.map Prod.fst) := by
    rw [show (∑ e, |x e - y e|) =
        (P.map (fun q => |q.1.1 - q.2.1|)).sum by
      simpa [x, y] using
        (fin_sum_get_map P (fun q => |q.1.1 - q.2.1|))]
    have habs : (P.map (fun q => |q.1.1 - q.2.1|)).sum =
        (P.map (fun q => q.1.1 - q.2.1)).sum := by
      apply congrArg List.sum
      exact List.map_congr_left fun z hz => abs_of_nonneg (hedge_nonneg z hz)
    rw [habs]
    have hsur := surplus_eq_pairUp (l.map Prod.fst)
    simpa [pairUp_map, unpaired_map, P, r, List.map_map,
      Function.comp_def] using hsur.symm
  rw [hright] at hbound
  exact hpunch.trans hbound


open scoped BigOperators List


lemma sort_sublist_sort_of_subset {S T : Finset ℝ} (hST : S ⊆ T) :
    S.sort (· ≤ ·) <+ T.sort (· ≤ ·) := by
  apply List.sublist_of_subperm_of_sortedLE
  · apply List.subperm_of_subset (Finset.sort_nodup S (· ≤ ·))
    intro x hx
    rw [Finset.mem_sort] at hx ⊢
    exact hST hx
  · exact (Finset.pairwise_sort S (· ≤ ·)).sortedLE
  · exact (Finset.pairwise_sort T (· ≤ ·)).sortedLE

def taggedBlocks {N : ℕ} (b : Fin N → List ℝ) : List (ℝ × Fin N) :=
  (List.finRange N).flatMap fun i => (b i).map fun x => (x, i)

lemma labelWeight_append [DecidableEq ι] (l₁ l₂ : List (ℝ × ι)) (v : ι) :
    labelWeight (l₁ ++ l₂) v = labelWeight l₁ v + labelWeight l₂ v := by
  simp [labelWeight]

lemma labelWeight_same_block [DecidableEq ι] (l : List ℝ) (i v : ι) :
    labelWeight (l.map fun x => (x, i)) v = if i = v then l.sum else 0 := by
  induction l with
  | nil => simp [labelWeight]
  | cons x t ih =>
      rw [List.map_cons, labelWeight_cons, ih, List.sum_cons]
      by_cases h : i = v <;> simp [h]

lemma labelWeight_flatMap_blocks [DecidableEq ι] (l : List ι)
    (b : ι → List ℝ) (v : ι) :
    labelWeight (l.flatMap fun i => (b i).map fun x => (x, i)) v =
      (l.map fun i => if i = v then (b i).sum else 0).sum := by
  induction l with
  | nil => simp [labelWeight]
  | cons i t ih =>
      rw [List.flatMap_cons, labelWeight_append, labelWeight_same_block, ih,
        List.map_cons, List.sum_cons]

lemma labelWeight_taggedBlocks {N : ℕ} (b : Fin N → List ℝ) (v : Fin N) :
    labelWeight (taggedBlocks b) v = (b v).sum := by
  rw [taggedBlocks, labelWeight_flatMap_blocks]
  rw [← List.sum_toFinset _ (List.nodup_finRange N)]
  simp

def intervalBlock {N : ℕ} (r : ℕ → ℝ) (f : ℕ → ℕ) (i : Fin N) : List ℝ :=
  (List.range' (f i) (f (i + 1) - f i)).map fun j => r (j + 1) - r j

lemma intervalBlock_sum {N : ℕ} (r : ℕ → ℝ) (f : ℕ → ℕ) (i : Fin N)
    (hf : f i ≤ f (i + 1)) :
    (intervalBlock r f i).sum = r (f (i + 1)) - r (f i) := by
  unfold intervalBlock
  rw [← List.sum_toFinset _ (List.nodup_range')]
  rw [List.toFinset_range'_1, Nat.add_sub_of_le hf]
  exact Finset.sum_Ico_sub r hf

def blockIndices (f : ℕ → ℕ) (N : ℕ) : List ℕ :=
  (List.range N).flatMap fun i => List.range' (f i) (f (i + 1) - f i)

lemma blockIndices_eq_range' (f : ℕ → ℕ) (hf : Monotone f) (N : ℕ) :
    blockIndices f N = List.range' (f 0) (f N - f 0) := by
  induction N with
  | zero => simp [blockIndices]
  | succ N ih =>
      rw [blockIndices, List.range_succ, List.flatMap_append]
      simp only [List.flatMap_singleton]
      rw [show (List.range N).flatMap
          (fun i => List.range' (f i) (f (i + 1) - f i)) = blockIndices f N by rfl,
        ih]
      have h0N : f 0 ≤ f N := hf (Nat.zero_le N)
      have hNN : f N ≤ f (N + 1) := hf (Nat.le_succ N)
      calc
        List.range' (f 0) (f N - f 0) ++
            List.range' (f N) (f (N + 1) - f N) =
            List.range' (f 0) (f N - f 0) ++
              List.range' (f 0 + (f N - f 0)) (f (N + 1) - f N) := by
                rw [Nat.add_sub_of_le h0N]
        _ = List.range' (f 0)
              ((f N - f 0) + (f (N + 1) - f N)) := by
                simp
        _ = List.range' (f 0) (f (N + 1) - f 0) := by congr 2; lia

lemma map_fst_tagged_intervalBlocks {N : ℕ} (r : ℕ → ℝ) (f : ℕ → ℕ)
    (hf : Monotone f) :
    (taggedBlocks (intervalBlock r f : Fin N → List ℝ)).map Prod.fst =
      (List.range' (f 0) (f N - f 0)).map fun j => r (j + 1) - r j := by
  unfold taggedBlocks intervalBlock
  rw [List.map_flatMap]
  simp only [List.map_map]
  change (List.finRange N).flatMap (fun a =>
      (List.range' (f a.val) (f (a.val + 1) - f a.val)).map
        (fun j => r (j + 1) - r j)) = _
  rw [show (List.finRange N).flatMap (fun a =>
        (List.range' (f a.val) (f (a.val + 1) - f a.val)).map
          (fun j => r (j + 1) - r j)) =
      ((List.finRange N).map (fun a => a.val)).flatMap (fun i =>
        (List.range' (f i) (f (i + 1) - f i)).map
          (fun j => r (j + 1) - r j)) by
        rw [List.flatMap_map]]
  rw [List.map_coe_finRange_eq_range]
  rw [← List.map_flatMap]
  change (blockIndices f N).map (fun j => r (j + 1) - r j) = _
  rw [blockIndices_eq_range' f hf N]

def indexedDiffs (q : List ℝ) : List ℝ :=
  (List.range (q.length - 1)).map fun j => q.getD (j + 1) 0 - q.getD j 0

lemma indexedDiffs_getD (q : List ℝ) {i : ℕ} (hi : i < q.length - 1) :
    (indexedDiffs q).getD i 0 = q.getD (i + 1) 0 - q.getD i 0 := by
  have hidx : i < (indexedDiffs q).length := by simp [indexedDiffs, hi]
  rw [List.getD_eq_getElem (hn := hidx)]
  simp [indexedDiffs]

lemma zipWith_tail_diff_eq_indexedDiffs (q : List ℝ) :
    List.zipWith (fun a b => b - a) q q.tail = indexedDiffs q := by
  apply List.ext_getElem
  · simp [indexedDiffs, List.length_zipWith]
  · intro i h₁ h₂
    simp only [indexedDiffs, List.getElem_map, List.getElem_range]
    simp only [List.getElem_zipWith, List.getElem_tail]
    rw [List.getD_eq_getElem, List.getD_eq_getElem]

noncomputable def boundaryPoints (S : Finset ℝ) : List ℝ :=
  (0 : ℝ) :: S.sort (· ≤ ·) ++ [1]

lemma boundaryPoints_length (S : Finset ℝ) :
    (boundaryPoints S).length = S.card + 2 := by
  simp [boundaryPoints, Finset.length_sort]

lemma boundaryPoints_pairwise (S : Finset ℝ)
    (hS : ↑S ⊆ Set.Ioo (0 : ℝ) 1) :
    (boundaryPoints S).Pairwise (· < ·) := by
  unfold boundaryPoints
  rw [List.pairwise_append, List.pairwise_cons]
  refine ⟨⟨?_, Finset.sortedLT_sort S |>.pairwise⟩, by simp, ?_⟩
  · intro x hx
    exact (hS ((Finset.mem_sort (· ≤ ·)).mp hx)).1
  · intro x hx y hy
    have hy1 : y = 1 := by simpa using hy
    subst y
    rcases List.mem_cons.mp hx with rfl | hx
    · norm_num
    · exact (hS ((Finset.mem_sort (· ≤ ·)).mp hx)).2

lemma boundaryPoints_sublist {S T : Finset ℝ} (hST : S ⊆ T) :
    boundaryPoints S <+ boundaryPoints T := by
  unfold boundaryPoints
  exact ((sort_sublist_sort_of_subset hST).append (List.Sublist.refl [1])).cons_cons 0

lemma pieceLengths_eq_indexedDiffs_boundaryPoints (S : Finset ℝ) :
    pieceLengths S = indexedDiffs (boundaryPoints S) := by
  unfold pieceLengths boundaryPoints
  exact zipWith_tail_diff_eq_indexedDiffs _

def clippedEmbedding {N M : ℕ} (e : Fin (N + 1) ↪o Fin (M + 1)) (j : ℕ) : ℕ :=
  (e ⟨min j N, by lia⟩).val

lemma clippedEmbedding_mono {N M : ℕ} (e : Fin (N + 1) ↪o Fin (M + 1)) :
    Monotone (clippedEmbedding e) := by
  intro a b hab
  apply e.monotone
  simp only [Fin.mk_le_mk]
  lia

lemma clippedEmbedding_of_le {N M : ℕ} (e : Fin (N + 1) ↪o Fin (M + 1))
    {j : ℕ} (hj : j ≤ N) :
    clippedEmbedding e j = (e ⟨j, by lia⟩).val := by
  simp [clippedEmbedding, Nat.min_eq_left hj]

theorem exists_tagged_piece_refinement {S T : Finset ℝ}
    (hST : S ⊆ T) (_hS : ↑S ⊆ Set.Ioo (0 : ℝ) 1)
    (hT : ↑T ⊆ Set.Ioo (0 : ℝ) 1) :
    ∃ l : List (ℝ × Fin (S.card + 1)),
      l.map Prod.fst = pieceLengths T ∧
      ∀ i, labelWeight l i = (pieceLengths S).getD i.val 0 := by
  let N := S.card + 1
  let M := T.card + 1
  let q := boundaryPoints S
  let r := boundaryPoints T
  have hqLen : q.length = N + 1 := boundaryPoints_length S
  have hrLen : r.length = M + 1 := boundaryPoints_length T
  have hsub : q <+ r := boundaryPoints_sublist hST
  rw [List.sublist_iff_exists_fin_orderEmbedding_get_eq] at hsub
  obtain ⟨e₀, he₀⟩ := hsub
  let e : Fin (N + 1) ↪o Fin (M + 1) :=
    (Fin.castOrderIso hqLen.symm).toOrderEmbedding |>.trans
      (e₀.trans (Fin.castOrderIso hrLen).toOrderEmbedding)
  have he : ∀ ix : Fin (N + 1),
      q.getD ix.val 0 = r.getD (e ix).val 0 := by
    intro ix
    have hri : (e ix).val < r.length := by
      rw [hrLen]
      exact (e ix).isLt
    rw [List.getD_eq_getElem (hn := by lia),
      List.getD_eq_getElem (hn := hri)]
    simpa [e] using he₀ ((Fin.castOrderIso hqLen.symm) ix)
  have hq0 : q.get ⟨0, by lia⟩ = 0 := by simp [q, boundaryPoints]
  have hr0 : r.get ⟨0, by lia⟩ = 0 := by simp [r, boundaryPoints]
  have hq0D : q.getD 0 0 = 0 := by simp [q, boundaryPoints]
  have hr0D : r.getD 0 0 = 0 := by simp [r, boundaryPoints]
  have hqLast : q.get ⟨N, by lia⟩ = 1 := by
    dsimp [q, N, boundaryPoints]
    simp [Finset.length_sort]
  have hrLast : r.get ⟨M, by lia⟩ = 1 := by
    dsimp [r, M, boundaryPoints]
    simp [Finset.length_sort]
  have hrNodup : r.Nodup := by
    exact (boundaryPoints_pairwise T hT).nodup
  have he0 : e ⟨0, by lia⟩ = ⟨0, by lia⟩ := by
    apply Fin.ext
    let a : Fin r.length := ⟨(e ⟨0, by lia⟩).val, by rw [hrLen]; lia⟩
    let b : Fin r.length := ⟨0, by lia⟩
    have hv : r.getD (e ⟨0, by lia⟩).val 0 = r.getD 0 0 := by
      rw [← he ⟨0, by lia⟩]
      rw [hq0D, hr0D]
    have hra : (e ⟨0, by lia⟩).val < r.length := by rw [hrLen]; lia
    have hrb : 0 < r.length := by lia
    rw [List.getD_eq_getElem (hn := hra), List.getD_eq_getElem (hn := hrb)] at hv
    have hab : a = b := hrNodup.injective_get (by simpa [a, b] using hv)
    simpa [a, b] using congrArg Fin.val hab
  have heLast : e ⟨N, by lia⟩ = ⟨M, by lia⟩ := by
    apply Fin.ext
    let a : Fin r.length := ⟨(e ⟨N, by lia⟩).val, by rw [hrLen]; lia⟩
    let b : Fin r.length := ⟨M, by lia⟩
    have hv : r.getD (e ⟨N, by lia⟩).val 0 = r.getD M 0 := by
      rw [← he ⟨N, by lia⟩]
      rw [List.getD_eq_getElem, List.getD_eq_getElem]
      simpa using hqLast.trans hrLast.symm
    have hra : (e ⟨N, by lia⟩).val < r.length := by rw [hrLen]; lia
    have hrb : M < r.length := by lia
    rw [List.getD_eq_getElem (hn := hra), List.getD_eq_getElem (hn := hrb)] at hv
    have hab : a = b := hrNodup.injective_get (by simpa [a, b] using hv)
    simpa [a, b] using congrArg Fin.val hab
  let F : ℕ → ℕ := clippedEmbedding e
  let rv : ℕ → ℝ := fun j => r.getD j 0
  let l : List (ℝ × Fin N) := taggedBlocks (intervalBlock rv F)
  have hFmono : Monotone F := clippedEmbedding_mono e
  have hF0 : F 0 = 0 := by
    rw [show F 0 = (e ⟨0, by lia⟩).val by
      exact clippedEmbedding_of_le e (Nat.zero_le N)]
    rw [he0]
  have hFN : F N = M := by
    rw [show F N = (e ⟨N, by lia⟩).val by
      exact clippedEmbedding_of_le e (le_rfl)]
    rw [heLast]
  refine ⟨l, ?_, ?_⟩
  · rw [show l.map Prod.fst =
        (List.range' (F 0) (F N - F 0)).map
          (fun j => rv (j + 1) - rv j) by
      exact map_fst_tagged_intervalBlocks rv F hFmono]
    rw [hF0, hFN]
    unfold rv
    rw [show List.range' 0 (M - 0) = List.range (r.length - 1) by
      rw [Nat.sub_zero, hrLen]
      simp only [Nat.add_sub_cancel_right]
      exact List.range_eq_range'.symm]
    exact (pieceLengths_eq_indexedDiffs_boundaryPoints T).symm
  · intro i
    change labelWeight l i = _
    rw [show labelWeight l i = (intervalBlock rv F i).sum by
      exact labelWeight_taggedBlocks _ i]
    rw [intervalBlock_sum rv F i (hFmono (Nat.le_succ i.val))]
    have hi : i.val ≤ N := Nat.le_of_lt i.isLt
    have his : i.val + 1 ≤ N := i.isLt
    have hFi : F i.val = (e ⟨i.val, by lia⟩).val :=
      clippedEmbedding_of_le e hi
    have hFis : F (i.val + 1) = (e ⟨i.val + 1, by lia⟩).val :=
      clippedEmbedding_of_le e his
    rw [hFi, hFis]
    unfold rv
    change r.getD (e ⟨i.val + 1, by lia⟩).val 0 -
        r.getD (e ⟨i.val, by lia⟩).val 0 =
      (pieceLengths S).getD i.val 0
    rw [← he ⟨i.val + 1, by lia⟩, ← he ⟨i.val, by lia⟩]
    rw [pieceLengths_eq_indexedDiffs_boundaryPoints]
    dsimp [q]
    have hiq : i.val < (boundaryPoints S).length - 1 := by
      rw [boundaryPoints_length]
      lia
    rw [indexedDiffs_getD _ hiq]


open scoped BigOperators


lemma codexLowerCuts_card (n : ℕ) : (codexLowerCuts n).card = n := by
  have h := card_cutsOfLengths (codexDyadicWeights n)
    (codexDyadicWeights_ne_nil n) (codexDyadicWeights_pos n)
  have h' : (codexLowerCuts n).card + 1 = n + 1 := by
    simpa [codexLowerCuts, codexDyadicWeights_length] using h
  lia

lemma codexLowerCuts_piece_getD (n : ℕ) (i : Fin (n + 1)) :
    (pieceLengths (codexLowerCuts n)).getD i.val 0 =
      (2 : ℝ) ^ i.val / codexDenom n := by
  rw [codexLowerCuts_pieces]
  have hi : i.val < (codexDyadicWeights n).length := by
    rw [codexDyadicWeights_length]
    exact i.isLt
  rw [List.getD_eq_getElem (hn := hi)]
  simp [codexDyadicWeights]

theorem codex_lower_bound_complete (n : ℕ) (_hn : 0 < n) :
    ∃ A : Finset ℝ, AdmissibleMark n A ∧
      ∀ B : Finset ℝ, AdmissibleMark n B → Disjoint A B →
        (2 : ℝ) ^ n / ((2 : ℝ) ^ (n + 1) - 1) ≤ L A B := by
  let A := codexLowerCuts n
  refine ⟨A, codexLowerCuts_admissible n, ?_⟩
  intro B hB hdisj
  let T := A ∪ B
  have hA : AdmissibleMark n A := codexLowerCuts_admissible n
  have hT : ↑T ⊆ Set.Ioo (0 : ℝ) 1 := by
    dsimp [T]
    rw [Finset.coe_union]
    exact Set.union_subset hA.1 hB.1
  obtain ⟨l, hlmap, hlweight⟩ := exists_tagged_piece_refinement
    (S := A) (T := T) (Finset.subset_union_left) hA.1 hT
  have hAcard : A.card = n := codexLowerCuts_card n
  let D := codexDenom n
  let ls := l.mergeSort (fun a b : ℝ × Fin (A.card + 1) => a.1 ≥ b.1)
  let scaled := ls.map fun z => (D * z.1, z.2)
  have hDpos : 0 < D := codexDenom_pos n
  have hlsSorted : ls.Pairwise (fun a b => a.1 ≥ b.1) :=
    List.pairwise_mergeSort' _ _
  have hscaledSorted : scaled.Pairwise (fun a b => a.1 ≥ b.1) := by
    exact hlsSorted.map _ (fun _ _ h => mul_le_mul_of_nonneg_left h hDpos.le)
  have hl_nonneg : ∀ z ∈ l, 0 ≤ z.1 := by
    intro z hz
    have hzfst : z.1 ∈ pieceLengths T := by
      rw [← hlmap]
      exact List.mem_map.mpr ⟨z, hz, rfl⟩
    exact (pieceLengths_pos T hT z.1 hzfst).le
  have hscaled_nonneg : ∀ z ∈ scaled, 0 ≤ z.1 := by
    intro z hz
    simp only [scaled, List.mem_map] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    exact mul_nonneg hDpos.le
      (hl_nonneg w ((List.mergeSort_perm l _).mem_iff.mp hw))
  have hlenL : l.length = T.card + 1 := by
    rw [← pieceLengths_length T, ← hlmap, List.length_map]
  have hTcard : T.card = A.card + B.card := Finset.card_union_of_disjoint hdisj
  have hscaledLen : scaled.length < 2 * Fintype.card (Fin (A.card + 1)) := by
    simp only [scaled, List.length_map, ls, List.length_mergeSort, Fintype.card_fin]
    rw [hlenL, hTcard]
    have hBcard : B.card ≤ n := hB.2
    lia
  have hscaledWeight : ∀ i : Fin (A.card + 1),
      labelWeight scaled i = (2 : ℝ) ^ i.val := by
    intro i
    rw [show labelWeight scaled i = D * labelWeight ls i by
      exact labelWeight_scale D ls i]
    rw [show labelWeight ls i = labelWeight l i by
      exact labelWeight_perm (List.mergeSort_perm l _) i]
    rw [hlweight]
    have hi' : i.val < n + 1 := by lia
    let j : Fin (n + 1) := ⟨i.val, hi'⟩
    rw [show (pieceLengths A).getD i.val 0 =
        (2 : ℝ) ^ i.val / D by
      simpa [A, D, j] using codexLowerCuts_piece_getD n j]
    field_simp
  have habstract : 1 ≤ surplus (scaled.map Prod.fst) := by
    apply abstract_lower (p := fun i : Fin (A.card + 1) => i.val)
      Fin.val_injective scaled hscaledSorted hscaled_nonneg hscaledLen hscaledWeight
  have hlsMap : ls.map Prod.fst =
      (pieceLengths T).mergeSort (· ≥ ·) := by
    calc
      ls.map Prod.fst = (l.map Prod.fst).mergeSort (· ≥ ·) := by
        exact List.map_mergeSort fun _ _ _ => congrFun rfl
      _ = (pieceLengths T).mergeSort (· ≥ ·) := by rw [hlmap]
  have hscaledMap : scaled.map Prod.fst =
      ((pieceLengths T).mergeSort (· ≥ ·)).map (fun x => D * x) := by
    calc
      scaled.map Prod.fst = (ls.map Prod.fst).map (fun x => D * x) := by
        simp [scaled, List.map_map]
      _ = ((pieceLengths T).mergeSort (· ≥ ·)).map
          (fun x => D * x) := by rw [hlsMap]
  rw [hscaledMap, surplus_scale] at habstract
  let sorted := (pieceLengths T).mergeSort (· ≥ ·)
  have hsumSorted : sorted.sum = 1 := by
    dsimp [sorted]
    rw [(List.mergeSort_perm (pieceLengths T) _).sum_eq]
    exact pieceLengths_sum T hT
  have hsurplus : surplus sorted = 2 * firstPlayerShare (pieceLengths T) - 1 := by
    rw [← two_mul_evenSum_sub_sum sorted, hsumSorted]
    rfl
  have hpow : (2 : ℝ) ^ (n + 1) = 2 * 2 ^ n := by ring
  have hD : D = (2 : ℝ) ^ (n + 1) - 1 := rfl
  have hshare : (2 : ℝ) ^ n / D ≤ firstPlayerShare (pieceLengths T) := by
    change 1 ≤ D * surplus sorted at habstract
    rw [hsurplus] at habstract
    rw [hD]
    apply (div_le_iff₀ (by simpa [hD] using hDpos)).2
    nlinarith [hpow]
  simpa [L, T, A, D, codexDenom] using hshare


open scoped BigOperators


noncomputable def bisectLengths (l : List ℝ) : List ℝ :=
  pairDup (l.map fun x => x / 2)

lemma bisectLengths_cons (x : ℝ) (l : List ℝ) :
    bisectLengths (x :: l) = x / 2 :: x / 2 :: bisectLengths l := rfl

lemma bisectLengths_pos {l : List ℝ} (hpos : ∀ x ∈ l, 0 < x) :
    ∀ x ∈ bisectLengths l, 0 < x := by
  intro x hx
  simp only [bisectLengths, pairDup, List.mem_flatMap, List.mem_map] at hx
  obtain ⟨y, ⟨z, hz, rfl⟩, hxy⟩ := hx
  have : x = z / 2 := by simpa using hxy
  subst x
  exact div_pos (hpos z hz) (by norm_num)

lemma bisectLengths_sum (l : List ℝ) : (bisectLengths l).sum = l.sum := by
  induction l with
  | nil => simp [bisectLengths, pairDup]
  | cons x xs ih =>
      rw [bisectLengths_cons, List.sum_cons, List.sum_cons, ih, List.sum_cons]
      ring

lemma sum_map_half (l : List ℝ) :
    (l.map fun x => x / 2).sum = l.sum / 2 := codex_sum_map_div l 2

lemma bisectLengths_length (l : List ℝ) :
    (bisectLengths l).length = 2 * l.length := by
  rw [bisectLengths, length_pairDup, List.length_map]

lemma scanl_mem_bisectLengths (l : List ℝ) (a : ℝ) {z : ℝ}
    (hz : z ∈ l.scanl (· + ·) a) : z ∈ (bisectLengths l).scanl (· + ·) a := by
  induction l generalizing a with
  | nil => simpa [bisectLengths, pairDup] using hz
  | cons x xs ih =>
      rw [List.scanl_cons] at hz
      rcases List.mem_cons.mp hz with rfl | hz
      · simp [bisectLengths_cons, List.scanl_cons]
      · have htail := ih (a := a + x) hz
        rw [bisectLengths_cons, List.scanl_cons, List.scanl_cons]
        have hhalf : a + x / 2 + x / 2 = a + x := by ring
        rw [hhalf]
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ htail)

lemma mem_interiorPartialSums_of_mem_scanl_Ioo (l : List ℝ) (hne : l ≠ [])
    (_hpos : ∀ x ∈ l, 0 < x) (hsum : l.sum = 1) {z : ℝ}
    (hzfull : z ∈ l.scanl (· + ·) 0) (hzIoo : z ∈ Set.Ioo (0 : ℝ) 1) :
    z ∈ interiorPartialSums l := by
  rw [← boundaryList_eq_scanl l hne hsum] at hzfull
  rcases List.mem_append.mp hzfull with hzleft | hzright
  · rcases List.mem_cons.mp hzleft with rfl | hz
    · exact (lt_irrefl 0 hzIoo.1).elim
    · exact hz
  · have hz1 : z = 1 := by simpa using hzright
    subst z
    exact (lt_irrefl 1 hzIoo.2).elim

lemma cutsOfLengths_subset_bisectLengths (l : List ℝ) (hne : l ≠ [])
    (hpos : ∀ x ∈ l, 0 < x) (hsum : l.sum = 1) :
    cutsOfLengths l ⊆ cutsOfLengths (bisectLengths l) := by
  intro z hz
  have hzint : z ∈ interiorPartialSums l := by simpa [cutsOfLengths] using hz
  have hzIoo := mem_interiorPartialSums_Ioo l hne hpos hsum hzint
  have hzTail : z ∈ (l.scanl (· + ·) 0).tail := by
    exact List.mem_of_mem_dropLast hzint
  have hzfull : z ∈ l.scanl (· + ·) 0 := List.mem_of_mem_tail hzTail
  have hbpos : ∀ x ∈ bisectLengths l, 0 < x := bisectLengths_pos hpos
  have hbne : bisectLengths l ≠ [] := by
    intro hb
    have h := congrArg List.sum hb
    rw [bisectLengths_sum, hsum] at h
    simp at h
  have hbsum : (bisectLengths l).sum = 1 := by rw [bisectLengths_sum, hsum]
  have hzfull' := scanl_mem_bisectLengths l 0 hzfull
  have hzint' := mem_interiorPartialSums_of_mem_scanl_Ioo
    (bisectLengths l) hbne hbpos hbsum hzfull' hzIoo
  simpa [cutsOfLengths] using hzint'

lemma firstPlayerShare_bisectLengths (l : List ℝ) :
    firstPlayerShare (bisectLengths l) = l.sum / 2 := by
  let h : List ℝ := l.map fun x => x / 2
  let hs : List ℝ := h.mergeSort (· ≥ ·)
  have hp : List.Perm h hs := (List.mergeSort_perm h (· ≥ ·)).symm
  have hpdup : List.Perm (pairDup h) (pairDup hs) := by
    unfold pairDup
    exact hp.flatMap_right fun a => [a, a]
  calc
    firstPlayerShare (bisectLengths l) = firstPlayerShare (pairDup hs) := by
      apply firstPlayerShare_congr
      simpa [bisectLengths, h] using hpdup
    _ = hs.sum := firstPlayerShare_pairDup_of_pairwise hs
      (List.pairwise_mergeSort' _ _)
    _ = h.sum := hp.sum_eq.symm
    _ = l.sum / 2 := by
      unfold h
      exact sum_map_half l

lemma exists_bisect_reply (n : ℕ) (A : Finset ℝ)
    (hA : AdmissibleMark n A) (hsmall : A.card < n) :
    ∃ B : Finset ℝ, AdmissibleMark n B ∧ Disjoint A B ∧ L A B = 1 / 2 := by
  let p := pieceLengths A
  have hpne : p ≠ [] := by
    intro h
    have := congrArg List.length h
    rw [pieceLengths_length] at this
    simp at this
  have hppos : ∀ x ∈ p, 0 < x :=
    pieceLengths_pos A hA.1
  have hpsum : p.sum = 1 := pieceLengths_sum A hA.1
  have hbne : bisectLengths p ≠ [] := by
    intro hb
    have h := congrArg List.sum hb
    rw [bisectLengths_sum, hpsum] at h
    simp at h
  obtain ⟨B, hBadm, hdisj, hL⟩ := exists_reply_of_piece_refinement n A
    (bisectLengths p) hbne
    (bisectLengths_pos hppos) (by rw [bisectLengths_sum, hpsum])
    (cutsOfLengths_subset_bisectLengths p hpne hppos hpsum)
    (by
      rw [bisectLengths_length]
      dsimp [p]
      rw [pieceLengths_length]
      lia)
  refine ⟨B, hBadm, hdisj, ?_⟩
  rw [hL, firstPlayerShare_bisectLengths, hpsum]


open scoped BigOperators

namespace CodexClosePoints

private theorem zip_tail_rel {α : Type*} {R : α → α → Prop} {l : List α}
    (h : l.Pairwise R) : ∀ p ∈ l.zip l.tail, R p.1 p.2 := by
  induction l with
  | nil => simp
  | cons a t ih =>
    cases t with
    | nil => simp
    | cons b u =>
      rw [List.pairwise_cons] at h
      simp only [List.tail_cons, List.zip_cons_cons, List.mem_cons]
      rintro p (rfl | hp)
      · exact h.1 b (by simp)
      · exact ih h.2 p hp

private theorem zip_tail_sum (f : α → ℝ) (d : α) : ∀ l : List α,
    ((l.zip l.tail).map (fun p => f p.2 - f p.1)).sum =
      f (l.getLastD d) - f (l.headD d) := by
  intro l
  induction l with
  | nil => simp
  | cons a t ih =>
    cases t with
    | nil => simp
    | cons b u =>
      simp only [List.tail_cons, List.zip_cons_cons, List.map_cons, List.sum_cons]
      have hih :
          ((List.zip (b :: u) u).map (fun p => f p.2 - f p.1)).sum =
            f ((b :: u).getLastD d) - f ((b :: u).headD d) := by
        simpa only [List.tail_cons] using ih
      rw [hih]
      simp only [List.getLastD_cons, List.headD_cons]
      ring

theorem exists_close_pair_of_finite {α : Type*} [Fintype α]
    (f : α → ℝ) (hcard : 2 ≤ Fintype.card α)
    (h0 : ∀ a, 0 ≤ f a) (h1 : ∀ a, f a ≤ 1) :
    ∃ a b, a ≠ b ∧
      |f a - f b| ≤ 1 / ((Fintype.card α : ℝ) - 1) := by
  by_cases hf : Function.Injective f
  · let _ : LinearOrder α := LinearOrder.lift' f hf
    let s : List α := Finset.univ.sort (· ≤ ·)
    have hslen : s.length = Fintype.card α := by
      simp [s]
    have hspw : s.Pairwise (fun a b => f a ≤ f b) := by
      have h := Finset.pairwise_sort (Finset.univ : Finset α) (· ≤ ·)
      exact h.imp (by
        intro a b hab
        exact hab)
    have hsnd : s.Nodup := by
      exact Finset.sort_nodup _ _
    cases hs : s with
    | nil =>
      simp [hs] at hslen
      exfalso
      lia
    | cons a t =>
      cases ht : t with
      | nil => simp [hs, ht] at hslen; lia
      | cons b u =>
        have hsform : s = a :: b :: u := by simp [hs, ht]
        let p : List (α × α) := (a :: b :: u).zip (b :: u)
        have hpne : p ≠ [] := by simp [p]
        have hp_len : p.length = Fintype.card α - 1 := by
          have hlen : (a :: b :: u).length = Fintype.card α := by
            simpa [hsform] using hslen
          have hc : Fintype.card α = u.length + 2 := by simpa using hlen.symm
          rw [hc]
          simp [p]
        have hp_rel : ∀ q ∈ p, f q.1 ≤ f q.2 := by
          have hpw : (a :: b :: u).Pairwise (fun x y => f x ≤ f y) := by
            simpa [hsform] using hspw
          simpa [p] using zip_tail_rel hpw
        have hp_ne : ∀ q ∈ p, q.1 ≠ q.2 := by
          have hnd : (a :: b :: u).Nodup := by simpa [hsform] using hsnd
          simpa [p] using zip_tail_rel hnd
        have hgap_sum :
            ((p.map (fun q => f q.2 - f q.1)).sum : ℝ) ≤ 1 := by
          have htel := zip_tail_sum f a (a :: b :: u)
          have hpdef : p = (a :: b :: u).zip (a :: b :: u).tail := by
            simp [p]
          rw [← hpdef] at htel
          simp only [List.headD_cons] at htel
          rw [htel]
          linarith [h0 a, h1 ((a :: b :: u).getLastD a)]
        have hden_nat : 1 ≤ Fintype.card α := by lia
        have hden_pos : 0 < (Fintype.card α : ℝ) - 1 := by
          have hc : (1 : ℝ) < Fintype.card α := by
            exact_mod_cast (show 1 < Fintype.card α by lia)
          linarith
        have hconst_sum :
            (p.map (fun _ => 1 / ((Fintype.card α : ℝ) - 1))).sum = 1 := by
          rw [List.map_const', List.sum_replicate, hp_len, nsmul_eq_mul,
            Nat.cast_sub hden_nat]
          field_simp
          norm_num
        have hsum_le :
            (p.map (fun q => f q.2 - f q.1)).sum ≤
              (p.map (fun _ => 1 / ((Fintype.card α : ℝ) - 1))).sum := by
          rw [hconst_sum]
          exact hgap_sum
        obtain ⟨q, hqp, hq⟩ :=
          List.exists_le_of_sum_le hpne
            (fun q => f q.2 - f q.1)
            (fun _ => 1 / ((Fintype.card α : ℝ) - 1)) hsum_le
        refine ⟨q.1, q.2, hp_ne q hqp, ?_⟩
        rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (hp_rel q hqp))]
        exact hq
  · obtain ⟨a, b, hab, hne⟩ := Function.not_injective_iff.mp hf
    refine ⟨a, b, hne, ?_⟩
    rw [hab, sub_self, abs_zero]
    have hc : (1 : ℝ) < Fintype.card α := by
      exact_mod_cast (show 1 < Fintype.card α by lia)
    positivity

theorem exists_disjoint_subset_sums_close (m : ℕ) (hm : 0 < m)
    (a : Fin m → ℝ) (ha : ∀ i, 0 ≤ a i) (hasum : ∑ i, a i = 1) :
    ∃ I J : Finset (Fin m), Disjoint I J ∧ (I ∪ J).Nonempty ∧
      0 ≤ (∑ i ∈ I, a i) - ∑ j ∈ J, a j ∧
      (∑ i ∈ I, a i) - ∑ j ∈ J, a j ≤ 1 / ((2 : ℝ) ^ m - 1) := by
  have hcard : 2 ≤ Fintype.card (Finset (Fin m)) := by
    simp only [Fintype.card_finset, Fintype.card_fin]
    exact Nat.le_pow hm
  have hsum0 : ∀ I : Finset (Fin m), 0 ≤ ∑ i ∈ I, a i :=
    fun I => Finset.sum_nonneg fun i _ => ha i
  have hsum1 : ∀ I : Finset (Fin m), (∑ i ∈ I, a i) ≤ 1 := by
    intro I
    rw [← hasum]
    exact Finset.sum_le_univ_sum_of_nonneg ha
  obtain ⟨A, B, hABne, hABclose⟩ :=
    exists_close_pair_of_finite (fun I : Finset (Fin m) => ∑ i ∈ I, a i)
      hcard hsum0 hsum1
  have hclose :
      |(∑ i ∈ A, a i) - ∑ j ∈ B, a j| ≤ 1 / ((2 : ℝ) ^ m - 1) := by
    simpa only [Fintype.card_finset, Fintype.card_fin, Nat.cast_pow,
      Nat.cast_ofNat] using hABclose
  let I₀ := A \ B
  let J₀ := B \ A
  have hdisj : Disjoint I₀ J₀ := disjoint_sdiff_sdiff
  have hnonempty : (I₀ ∪ J₀).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty, Finset.union_eq_empty] at h
    apply hABne
    apply Finset.Subset.antisymm
    · exact Finset.sdiff_eq_empty_iff_subset.mp (by simpa [I₀] using h.1)
    · exact Finset.sdiff_eq_empty_iff_subset.mp (by simpa [J₀] using h.2)
  have hdiff :
      (∑ i ∈ I₀, a i) - ∑ j ∈ J₀, a j =
        (∑ i ∈ A, a i) - ∑ j ∈ B, a j :=
    Finset.sum_sdiff_sub_sum_sdiff
  by_cases horient : (∑ j ∈ B, a j) ≤ ∑ i ∈ A, a i
  · refine ⟨I₀, J₀, hdisj, hnonempty, ?_, ?_⟩
    · rw [hdiff]
      linarith
    · rw [hdiff]
      exact le_of_abs_le hclose
  · refine ⟨J₀, I₀, hdisj.symm, by simpa [Finset.union_comm] using hnonempty, ?_, ?_⟩
    · rw [← neg_sub, hdiff]
      linarith
    · rw [← neg_sub, hdiff]
      rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge horient))] at hclose
      linarith

end CodexClosePoints

open scoped BigOperators List


theorem firstPlayerShare_pairDup_append_singleton (xs : List ℝ) (r : ℝ) :
    firstPlayerShare (pairDup xs ++ [r]) = xs.sum + r := by
  let H := xs.filter fun x => decide (r ≤ x)
  let L := xs.filter fun x => !(decide (r ≤ x))
  let hi := H.mergeSort (· ≥ ·)
  let lo := L.mergeSort (· ≥ ·)
  have hhiPerm : hi.Perm H := List.mergeSort_perm H (· ≥ ·)
  have hloPerm : lo.Perm L := List.mergeSort_perm L (· ≥ ·)
  have hpartition : (H ++ L).Perm xs := List.filter_append_perm _ xs
  have hhiloperm : (hi ++ lo).Perm xs :=
    (hhiPerm.append hloPerm).trans hpartition
  have hhipw : hi.Pairwise (· ≥ ·) := List.pairwise_mergeSort' (· ≥ ·) H
  have hlopw : lo.Pairwise (· ≥ ·) := List.pairwise_mergeSort' (· ≥ ·) L
  have hhi : ∀ x ∈ hi, r ≤ x := by
    intro x hx
    have hxH : x ∈ H := hhiPerm.mem_iff.mp hx
    have hxH' : x ∈ xs ∧ r ≤ x := by simpa [H] using hxH
    exact hxH'.2
  have hlo : ∀ x ∈ lo, x ≤ r := by
    intro x hx
    have hxL : x ∈ L := hloPerm.mem_iff.mp hx
    have hxL' : x ∈ xs ∧ x < r := by simpa [L] using hxL
    exact hxL'.2.le
  have hpairHi : ∀ z ∈ pairDup hi, r ≤ z := by
    intro z hz
    simp only [pairDup, List.mem_flatMap] at hz
    obtain ⟨x, hx, hz⟩ := hz
    have hz' : z = x := by simpa using hz
    subst z
    exact hhi x hx
  have hpairLo : ∀ z ∈ pairDup lo, z ≤ r := by
    intro z hz
    simp only [pairDup, List.mem_flatMap] at hz
    obtain ⟨x, hx, hz⟩ := hz
    have hz' : z = x := by simpa using hz
    subst z
    exact hlo x hx
  have hsorted : (pairDup hi ++ r :: pairDup lo).Pairwise (· ≥ ·) := by
    rw [List.pairwise_append]
    refine ⟨pairwise_pairDup hhipw, ?_, ?_⟩
    · rw [List.pairwise_cons]
      exact ⟨hpairLo, pairwise_pairDup hlopw⟩
    · intro x hx y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hpairHi x hx
      · exact (hpairLo y hy).trans (hpairHi x hx)
  have hdup : (pairDup (hi ++ lo)).Perm (pairDup xs) := by
    unfold pairDup
    exact hhiloperm.flatMap_right fun a => [a, a]
  have harrange : (pairDup xs ++ [r]).Perm (pairDup hi ++ r :: pairDup lo) := by
    have h₁ : (pairDup xs ++ [r]).Perm (pairDup (hi ++ lo) ++ [r]) :=
      hdup.symm.append_right [r]
    have h₂ : pairDup (hi ++ lo) ++ [r] =
        pairDup hi ++ (pairDup lo ++ [r]) := by
      simp [pairDup, List.flatMap_append, List.append_assoc]
    rw [h₂] at h₁
    exact h₁.trans (List.perm_append_comm.append_left (pairDup hi))
  calc
    firstPlayerShare (pairDup xs ++ [r]) =
        firstPlayerShare (pairDup hi ++ r :: pairDup lo) :=
      firstPlayerShare_congr harrange
    _ = hi.sum + r + lo.sum :=
      firstPlayerShare_pairs_singleton_pairs hi lo r hsorted
    _ = xs.sum + r := by
      have hsum := hhiloperm.sum_eq
      rw [List.sum_append] at hsum
      linarith

theorem firstPlayerShare_pairDup (xs : List ℝ) :
    firstPlayerShare (pairDup xs) = xs.sum := by
  let s := xs.mergeSort (· ≥ ·)
  have hsperm : s.Perm xs := List.mergeSort_perm xs (· ≥ ·)
  have hdup : (pairDup s).Perm (pairDup xs) := by
    unfold pairDup
    exact hsperm.flatMap_right fun a => [a, a]
  calc
    firstPlayerShare (pairDup xs) = firstPlayerShare (pairDup s) :=
      firstPlayerShare_congr hdup.symm
    _ = s.sum := firstPlayerShare_pairDup_of_pairwise s
      (List.pairwise_mergeSort' (· ≥ ·) xs)
    _ = xs.sum := hsperm.sum_eq

lemma pairDup_perm_append_self (xs : List ℝ) :
    (pairDup xs).Perm (xs ++ xs) := by
  induction xs with
  | nil => simp [pairDup]
  | cons x tail ih =>
      change (x :: x :: pairDup tail).Perm ((x :: tail) ++ x :: tail)
      have h₁ : (x :: x :: pairDup tail).Perm (x :: x :: (tail ++ tail)) :=
        (ih.cons x).cons x
      exact h₁.trans (by
        apply List.Perm.cons
        exact List.perm_middle.symm)


/-! ## Xiang Yu's reply

We describe Xiang Yu's cuts on the level of multisets of piece lengths:
`Refines s t` says that the pieces `t` arise from the pieces `s` by repeatedly
cutting a piece in two. -/

/-- `Refines s t`: the multiset of pieces `t` is obtained from the multiset of
pieces `s` by repeatedly cutting one piece into two. -/
inductive Refines : Multiset ℝ → Multiset ℝ → Prop
  | refl (s : Multiset ℝ) : Refines s s
  | cut {s t : Multiset ℝ} {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
      Refines (a ::ₘ b ::ₘ s) t → Refines ((a + b) ::ₘ s) t

lemma Refines.trans {s t u : Multiset ℝ} (h : Refines s t) (h' : Refines t u) :
    Refines s u := by
  induction h with
  | refl => exact h'
  | cut ha hb _ ih => exact .cut ha hb (ih h')

lemma Refines.add_right {s t : Multiset ℝ} (h : Refines s t) (u : Multiset ℝ) :
    Refines (s + u) (t + u) := by
  induction h with
  | refl s => exact .refl _
  | cut ha hb _ ih =>
    rw [Multiset.cons_add]
    exact .cut ha hb (by simpa only [Multiset.cons_add] using ih)

lemma Refines.add {s t s' t' : Multiset ℝ} (h : Refines s t) (h' : Refines s' t') :
    Refines (s + s') (t + t') :=
  (h.add_right s').trans (by simpa only [add_comm] using h'.add_right t)

lemma Refines.sum_eq {s t : Multiset ℝ} (h : Refines s t) : t.sum = s.sum := by
  induction h with
  | refl => rfl
  | cut _ _ _ ih => rw [ih]; simp [add_assoc]

lemma Refines.pos {s t : Multiset ℝ} (h : Refines s t) (hs : ∀ x ∈ s, 0 < x) :
    ∀ x ∈ t, 0 < x := by
  induction h with
  | refl => exact hs
  | cut ha hb _ ih =>
    refine ih fun x hx ↦ ?_
    simp only [Multiset.mem_cons] at hx hs
    rcases hx with rfl | rfl | hx
    · exact ha
    · exact hb
    · exact hs x (.inr hx)

/-- Cutting the piece `a` into `b` and `a - b`. -/
lemma Refines.cut_sub {a b : ℝ} (hb : 0 < b) (hab : b < a) (s : Multiset ℝ) :
    Refines (a ::ₘ s) (b ::ₘ (a - b) ::ₘ s) := by
  have := Refines.cut hb (sub_pos.mpr hab) (.refl (b ::ₘ (a - b) ::ₘ s))
  rwa [add_sub_cancel] at this

/-- Every piece can be cut in half. -/
lemma Refines.bisect (o : Multiset ℝ) (ho : ∀ x ∈ o, 0 < x) :
    Refines o (o.map (· / 2) + o.map (· / 2)) := by
  induction o using Multiset.induction with
  | empty => exact .refl _
  | cons a o ih =>
    have ha : 0 < a := ho a (Multiset.mem_cons_self a o)
    have h1 := (Refines.cut_sub (half_pos ha) (half_lt_self ha) 0).add
      (ih fun x hx ↦ ho x (Multiset.mem_cons_of_mem hx))
    rw [sub_half] at h1
    convert h1 using 1
    · simp
    · rw [Multiset.map_cons]; simp only [← Multiset.singleton_add, add_zero]; abel

/-- The partial sums of a list, excluding the last one. -/
lemma dropLast_scanl_cons (c x : ℝ) (l : List ℝ) :
    ((x :: l).scanl (· + ·) c).dropLast = c :: (l.scanl (· + ·) (c + x)).dropLast := by
  rw [List.scanl_cons, List.dropLast_cons_of_ne_nil (by simp)]

/-- Cutting a piece of the stick in two only adds a cut point. -/
lemma cutsOfLengths_subset_cut (u v : List ℝ) (a b : ℝ) :
    cutsOfLengths (u ++ (a + b) :: v) ⊆ cutsOfLengths (u ++ a :: b :: v) := by
  have key : ∀ c : ℝ, List.Sublist ((u ++ (a + b) :: v).scanl (· + ·) c).dropLast
      ((u ++ a :: b :: v).scanl (· + ·) c).dropLast := by
    induction u with
    | nil =>
      intro c
      simp only [List.nil_append, dropLast_scanl_cons, add_assoc]
      exact .cons_cons _ (.cons _ (.refl _))
    | cons x u ih =>
      intro c
      simp only [List.cons_append, dropLast_scanl_cons]
      exact .cons_cons _ (ih _)
  intro z hz
  simp only [cutsOfLengths, interiorPartialSums, List.mem_toFinset, ← List.tail_dropLast]
    at hz ⊢
  exact (key 0).tail.subset hz

/-- A refinement of multisets of pieces can be carried out on the stick. -/
lemma Refines.exists_list {s t : Multiset ℝ} (h : Refines s t) :
    ∀ p : List ℝ, (p : Multiset ℝ) = s →
      ∃ l : List ℝ, (l : Multiset ℝ) = t ∧ cutsOfLengths p ⊆ cutsOfLengths l := by
  induction h with
  | refl s => exact fun p hp ↦ ⟨p, hp, subset_rfl⟩
  | @cut s t a b ha hb _ ih =>
    intro p hp
    have hmem : a + b ∈ p := by
      have : a + b ∈ (p : Multiset ℝ) := hp ▸ Multiset.mem_cons_self _ _
      simpa using this
    obtain ⟨u, v, rfl⟩ := List.append_of_mem hmem
    have hs : s = ↑(u ++ v) := by
      have h1 : (a + b) ::ₘ (↑(u ++ v) : Multiset ℝ) = (a + b) ::ₘ s := by
        rw [← hp]
        exact (Multiset.coe_eq_coe.mpr List.perm_middle).symm
      exact ((Multiset.cons_inj_right _).mp h1).symm
    obtain ⟨l, hl, hsub⟩ := ih (u ++ a :: b :: v) (by
      rw [hs]
      exact Multiset.coe_eq_coe.mpr (List.perm_middle.trans (List.perm_middle.cons a)))
    exact ⟨l, hl, (cutsOfLengths_subset_cut u v a b).trans hsub⟩

/-- **Matching.** Given two groups of pieces `s` and `t`, where `t` has total
length at most that of `s`, Xiang Yu can cut the pieces of `s + t` so that all
resulting pieces come in pairs of equal length, except for at most one piece, of
length at most the difference of the totals.  The number of cuts needed is less
than the number of pieces in `s + t`.

To do so, compare a piece `a` of `s` to a piece `b` of `t`, cut the longer of
the two so as to split off a copy of the shorter, and repeat.  Once `t` is used
up, halve all but one of the remaining pieces of `s`. -/
lemma exists_refines_pairs (s t : Multiset ℝ) (hs : ∀ x ∈ s, 0 < x)
    (ht : ∀ x ∈ t, 0 < x) (hst : t.sum ≤ s.sum) :
    ∃ xs res : Multiset ℝ, Refines (s + t) (xs + xs + res) ∧ res.card ≤ 1 ∧
      res.sum ≤ s.sum - t.sum ∧
      2 * xs.card + res.card ≤ 2 * (s.card + t.card) - 1 := by
  induction hN : s.card + t.card using Nat.strong_induction_on generalizing s t with
  | _ N ih =>
  subst hN
  -- the pair `a, a` together with a solution of a smaller problem
  have step : ∀ (a : ℝ) (u s' t' : Multiset ℝ), Refines u (a ::ₘ a ::ₘ (s' + t')) →
      (∀ x ∈ s', 0 < x) → (∀ x ∈ t', 0 < x) → t'.sum ≤ s'.sum →
      s'.card + t'.card < s.card + t.card → s'.sum - t'.sum ≤ s.sum - t.sum →
      (2 * (s'.card + t'.card) - 1) + 2 ≤ 2 * (s.card + t.card) - 1 →
      ∃ xs res : Multiset ℝ, Refines u (xs + xs + res) ∧ res.card ≤ 1 ∧
        res.sum ≤ s.sum - t.sum ∧ 2 * xs.card + res.card ≤ 2 * (s.card + t.card) - 1 := by
    intro a u s' t' hu hs' ht' hst' hlt hsum hcard
    obtain ⟨xs, res, h1, h2, h3, h4⟩ := ih _ hlt s' t' hs' ht' hst' rfl
    refine ⟨a ::ₘ xs, res, hu.trans ?_, h2, h3.trans hsum, ?_⟩
    · convert (Refines.refl {a, a}).add h1 using 1
      · simp
      · simp only [← Multiset.singleton_add, Multiset.insert_eq_cons]; abel
    · rw [Multiset.card_cons]; lia
  obtain rfl | ⟨b, hb⟩ := t.empty_or_exists_mem
  · obtain rfl | ⟨a, ha⟩ := s.empty_or_exists_mem
    · exact ⟨0, 0, by simpa using Refines.refl 0, by simp, by simp, by simp⟩
    obtain ⟨s', rfl⟩ := Multiset.exists_cons_of_mem ha
    obtain rfl | hs0 := eq_or_ne s' 0
    · -- a single piece: leave it alone
      exact ⟨0, {a}, by simpa using Refines.refl {a}, by simp, by simp, by simp⟩
    · -- halve `a` and continue
      have ha0 := hs a ha
      have hs' : ∀ x ∈ s', 0 < x := fun x hx ↦ hs x (Multiset.mem_cons_of_mem hx)
      have hc : 0 < s'.card := Multiset.card_pos.mpr hs0
      refine step (a / 2) _ s' 0 ?_ hs' (by simp)
        (by simpa using Multiset.sum_nonneg fun x hx ↦ (hs' x hx).le)
        (by simp) (by simp; linarith) (by simp only [Multiset.card_cons]; lia)
      have := Refines.cut_sub (half_pos ha0) (half_lt_self ha0) s'
      rw [sub_half] at this
      simpa using this
  · obtain ⟨t', rfl⟩ := Multiset.exists_cons_of_mem hb
    have hb0 := ht b hb
    have ht' : ∀ x ∈ t', 0 < x := fun x hx ↦ ht x (Multiset.mem_cons_of_mem hx)
    have ht0 : 0 ≤ t'.sum := Multiset.sum_nonneg fun x hx ↦ (ht' x hx).le
    obtain ⟨a, ha⟩ : ∃ a, a ∈ s := by
      obtain rfl | h := s.empty_or_exists_mem
      · simp at hst; linarith
      · exact h
    obtain ⟨s', rfl⟩ := Multiset.exists_cons_of_mem ha
    have ha0 := hs a ha
    have hs' : ∀ x ∈ s', 0 < x := fun x hx ↦ hs x (Multiset.mem_cons_of_mem hx)
    simp only [Multiset.sum_cons, Multiset.card_cons] at hst step ⊢
    obtain hab | rfl | hab := lt_trichotomy a b
    · -- cut `b` into `a` and `b - a`
      refine step a _ s' ((b - a) ::ₘ t') ?_ hs'
        (by simpa using ⟨hab, ht'⟩) (by simp; linarith)
        (by simp only [Multiset.card_cons]; lia) (by simp; linarith)
        (by simp only [Multiset.card_cons]; lia)
      convert (Refines.cut_sub ha0 hab (a ::ₘ (s' + t'))) using 1
      · simp only [← Multiset.singleton_add]; abel
      · simp only [← Multiset.singleton_add]; abel
    · -- equal pieces: no cut needed
      refine step a _ s' t' ?_ hs' ht' (by linarith) (by lia) (by linarith) (by lia)
      convert Refines.refl (a ::ₘ a ::ₘ (s' + t')) using 1
      simp only [← Multiset.singleton_add]; abel
    · -- cut `a` into `b` and `a - b`
      refine step b _ ((a - b) ::ₘ s') t' ?_
        (by simpa using ⟨hab, hs'⟩) ht' (by simp; linarith)
        (by simp only [Multiset.card_cons]; lia) (by simp; linarith)
        (by simp only [Multiset.card_cons]; lia)
      convert (Refines.cut_sub hb0 hab (b ::ₘ (s' + t'))) using 1
      · simp only [← Multiset.singleton_add]; abel
      · simp only [← Multiset.singleton_add]; abel

open scoped BigOperators List

/-- Xiang Yu's reply.  Among the subsets of Liu Bang's `m` pieces, two have total
lengths differing by at most `1 / (2 ^ m - 1)`.  Xiang Yu matches the pieces of
the two (disjoint) subsets against each other and halves all other pieces. -/
theorem exists_close_refinement (p : List ℝ)
    (hpne : p ≠ []) (hppos : ∀ x ∈ p, 0 < x) (hpsum : p.sum = 1) :
    ∃ l : List ℝ,
      l ≠ [] ∧
      (∀ z ∈ l, 0 < z) ∧
      l.sum = 1 ∧
      cutsOfLengths p ⊆ cutsOfLengths l ∧
      l.length ≤ 2 * p.length - 1 ∧
      firstPlayerShare l ≤
        (1 + 1 / ((2 : ℝ) ^ p.length - 1)) / 2 := by
  have hm : 0 < p.length := List.length_pos_iff.mpr hpne
  have hpos : ∀ i : Fin p.length, 0 < p.get i := fun i ↦ hppos _ (List.get_mem p i)
  have hunivval : (Finset.univ : Finset (Fin p.length)).val.map p.get = ↑p := by
    rw [Fin.univ_val_map, List.ofFn_get]
  have hsumFin : ∑ i : Fin p.length, p.get i = 1 := by
    rw [Finset.sum_eq_multiset_sum, hunivval, Multiset.sum_coe, hpsum]
  obtain ⟨I, J, hIJ, hnonempty, hdiff0, hdiff⟩ :=
    CodexClosePoints.exists_disjoint_subset_sums_close
      p.length hm p.get (fun i ↦ (hpos i).le) hsumFin
  -- the pieces in `I`, the pieces in `J`, and all other pieces
  set s := I.val.map p.get with hs_def
  set t := J.val.map p.get with ht_def
  set o := (I ∪ J)ᶜ.val.map p.get with ho_def
  have hmempos : ∀ K : Finset (Fin p.length), ∀ x ∈ K.val.map p.get, 0 < x := by
    intro K x hx
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.mp hx
    exact hpos i
  have hp : (p : Multiset ℝ) = s + t + o := by
    have e1 : (I ∪ J).val = I.val + J.val := by
      rw [← Finset.disjUnion_eq_union _ _ hIJ]; rfl
    have e2 : (Finset.univ : Finset (Fin p.length)).val = (I ∪ J).val + (I ∪ J)ᶜ.val := by
      rw [← Finset.union_compl (I ∪ J), ← Finset.disjUnion_eq_union _ _ disjoint_compl_right]
      rfl
    rw [← hunivval, e2, e1, Multiset.map_add, Multiset.map_add]
  have hcard : p.length = s.card + t.card + o.card := by
    simpa using congrArg Multiset.card hp
  have hcard1 : 0 < s.card + t.card := by
    simpa [hs_def, ht_def, ← Finset.card_union_of_disjoint hIJ] using hnonempty.card_pos
  obtain ⟨xs, res, href, hres1, hres, hlen⟩ :=
    exists_refines_pairs s t (hmempos I) (hmempos J) (sub_nonneg.mp hdiff0)
  replace hres : res.sum ≤ 1 / ((2 : ℝ) ^ p.length - 1) := hres.trans hdiff
  -- all pieces now come in pairs `ys + ys`, except for `res`
  set ys := xs + o.map (· / 2) with hys
  have href' : Refines (↑p) (ys + ys + res) := by
    convert href.add (Refines.bisect o (hmempos _)) using 1
    rw [hys]; abel
  obtain ⟨l, hl, hcuts⟩ := href'.exists_list p rfl
  have hlsum : l.sum = 1 := by
    rw [← Multiset.sum_coe, hl, href'.sum_eq, Multiset.sum_coe, hpsum]
  have hshare : firstPlayerShare l = ys.sum + res.sum := by
    clear_value ys
    obtain ⟨ys', rfl⟩ : ∃ ys' : List ℝ, (ys' : Multiset ℝ) = ys := ⟨_, ys.coe_toList⟩
    obtain ⟨res', rfl⟩ : ∃ res' : List ℝ, (res' : Multiset ℝ) = res := ⟨_, res.coe_toList⟩
    have hperm : l ~ pairDup ys' ++ res' :=
      (Multiset.coe_eq_coe.mp (by simpa using hl) : l ~ ys' ++ ys' ++ res').trans
        ((pairDup_perm_append_self ys').symm.append_right res')
    rw [firstPlayerShare_congr hperm]
    match res', hres1 with
    | [], _ => simpa using firstPlayerShare_pairDup ys'
    | [r], _ => simpa using firstPlayerShare_pairDup_append_singleton ys' r
  refine ⟨l, ?_, ?_, hlsum, hcuts, ?_, ?_⟩
  · rintro rfl; simp at hlsum
  · intro z hz
    exact href'.pos (fun x hx ↦ hppos x (by simpa using hx)) z (hl ▸ (by simpa using hz))
  · have : l.length = 2 * xs.card + res.card + 2 * o.card := by
      have := congrArg Multiset.card hl
      simp [hys] at this
      lia
    lia
  · have h2 : 2 * ys.sum + res.sum = 1 := by
      have := href'.sum_eq
      rw [Multiset.sum_coe, hpsum] at this
      simp at this
      linarith
    rw [hshare]
    linarith


open scoped BigOperators List


lemma upper_denom_pos (n : ℕ) :
    0 < (2 : ℝ) ^ (n + 1) - 1 := by
  have hpow : (1 : ℝ) < 2 ^ (n + 1) :=
    one_lt_pow₀ (by norm_num) (by lia)
  linarith

lemma upper_answer_identity (n : ℕ) :
    (1 + 1 / ((2 : ℝ) ^ (n + 1) - 1)) / 2 =
      (2 : ℝ) ^ n / ((2 : ℝ) ^ (n + 1) - 1) := by
  have hD : (2 : ℝ) ^ (n + 1) - 1 ≠ 0 :=
    ne_of_gt (upper_denom_pos n)
  have hpow : (2 : ℝ) ^ (n + 1) = 2 * 2 ^ n := by ring
  field_simp [hD]
  nlinarith

lemma half_le_upper_answer (n : ℕ) :
    (1 : ℝ) / 2 ≤ (2 : ℝ) ^ n / ((2 : ℝ) ^ (n + 1) - 1) := by
  rw [← upper_answer_identity]
  have hrecip : 0 < 1 / ((2 : ℝ) ^ (n + 1) - 1) :=
    one_div_pos.mpr (upper_denom_pos n)
  linarith

theorem exists_hard_reply (n : ℕ) (A : Finset ℝ)
    (hA : AdmissibleMark n A) (hcard : A.card = n) :
    ∃ B : Finset ℝ, AdmissibleMark n B ∧ Disjoint A B ∧
      L A B ≤ (2 : ℝ) ^ n / ((2 : ℝ) ^ (n + 1) - 1) := by
  let p := pieceLengths A
  have hpne : p ≠ [] := by
    intro hnil
    have hlen := congrArg List.length hnil
    rw [show p.length = A.card + 1 by
      exact pieceLengths_length A] at hlen
    simp at hlen
  have hppos : ∀ x ∈ p, 0 < x := pieceLengths_pos A hA.1
  have hpsum : p.sum = 1 := pieceLengths_sum A hA.1
  obtain ⟨l, hlne, hlpos, hlsum, hlcuts, hllen, hlshare⟩ :=
    exists_close_refinement p hpne hppos hpsum
  have hplen : p.length = n + 1 := by
    rw [pieceLengths_length A, hcard]
  have hreplyLen : l.length ≤ A.card + n + 1 := by
    rw [hplen] at hllen
    lia
  obtain ⟨B, hBadm, hdisj, hL⟩ :=
    exists_reply_of_piece_refinement n A l hlne hlpos hlsum hlcuts hreplyLen
  refine ⟨B, hBadm, hdisj, ?_⟩
  rw [hL]
  apply hlshare.trans_eq
  rw [hplen]
  exact upper_answer_identity n

theorem codex_upper_bound_aux (n : ℕ) (_hn : 0 < n) :
    ∀ A : Finset ℝ, AdmissibleMark n A →
      ∃ B : Finset ℝ, AdmissibleMark n B ∧ Disjoint A B ∧
        L A B ≤ (2 : ℝ) ^ n / ((2 : ℝ) ^ (n + 1) - 1) := by
  intro A hA
  by_cases hsmall : A.card < n
  · obtain ⟨B, hBadm, hdisj, hL⟩ := exists_bisect_reply n A hA hsmall
    refine ⟨B, hBadm, hdisj, ?_⟩
    rw [hL]
    exact half_le_upper_answer n
  · have hcardle : A.card ≤ n := hA.2
    have hcard : A.card = n := by lia
    exact exists_hard_reply n A hA hcard

/-- Auxiliary form of the lower bound, declared before `V_eq` so that the main
reduction can refer to it.  Its content is identical to `lower_bound`. -/
theorem lower_bound_aux (n : ℕ) (hn : 0 < n) :
    ∃ A : Finset ℝ, AdmissibleMark n A ∧
      ∀ B : Finset ℝ, AdmissibleMark n B → Disjoint A B →
        (2 : ℝ) ^ n / ((2 : ℝ) ^ (n + 1) - 1) ≤ L A B := by
  exact codex_lower_bound_complete n hn

/-- Auxiliary form of the upper bound, declared before `V_eq` so that the main
reduction can refer to it.  Its content is identical to `upper_bound`. -/
theorem upper_bound_aux (n : ℕ) (hn : 0 < n) :
    ∀ A : Finset ℝ, AdmissibleMark n A →
      ∃ B : Finset ℝ, AdmissibleMark n B ∧ Disjoint A B ∧
        L A B ≤ (2 : ℝ) ^ n / ((2 : ℝ) ^ (n + 1) - 1) := by
  exact codex_upper_bound_aux n hn

/-- **Lower bound.** Liu Bang has an admissible marking `A` such that for every
admissible marking `B` disjoint from `A`, his guaranteed share is at least
`2^n / (2^(n+1) - 1)`. -/
theorem lower_bound (n : ℕ) (hn : 0 < n) :
    ∃ A : Finset ℝ, AdmissibleMark n A ∧
      ∀ B : Finset ℝ, AdmissibleMark n B → Disjoint A B →
        (2 : ℝ) ^ n / ((2 : ℝ) ^ (n + 1) - 1) ≤ L A B := by
  exact lower_bound_aux n hn

/-- **Upper bound / optimality.** For every admissible marking `A` of Liu Bang,
Xiang Yu has an admissible marking `B` disjoint from `A` with
`L A B ≤ 2^n / (2^(n+1) - 1)`, so Liu Bang cannot guarantee more. -/
theorem upper_bound (n : ℕ) (hn : 0 < n) :
    ∀ A : Finset ℝ, AdmissibleMark n A →
      ∃ B : Finset ℝ, AdmissibleMark n B ∧ Disjoint A B ∧
        L A B ≤ (2 : ℝ) ^ n / ((2 : ℝ) ^ (n + 1) - 1) := by
  exact upper_bound_aux n hn

/-! **Main statement.** For every positive integer `n`, Liu Bang's guaranteed value equals `2^n / (2^(n+1) - 1)`. -/
snip end

problem imo2026_p3 (n : ℕ) (hn : 0 < n) : V n = answer n := by
  obtain ⟨A₀, hA₀adm, hA₀⟩ := lower_bound_aux n hn
  have hub := upper_bound_aux n hn
  have hemptyA : AdmissibleMark n ∅ := by constructor <;> simp
  have : Nonempty {A : Finset ℝ // AdmissibleMark n A} := ⟨⟨∅, hemptyA⟩⟩
  apply le_antisymm
  · -- For every admissible `A`, Xiang Yu's reply makes the infimum `≤ answer`.
    apply ciSup_le
    intro A
    obtain ⟨B, hBadm, hdisj, hB⟩ := hub A.1 A.2
    have hbdd : BddBelow (Set.range fun B : {B : Finset ℝ // AdmissibleMark n B ∧ Disjoint A.1 B} =>
        L A.1 B.1) := by
      refine ⟨0, ?_⟩
      rintro _ ⟨B', rfl⟩
      exact (L_mem_Icc A.1 B'.1 A.2.1 B'.2.1.1).1
    exact ciInf_le_of_le hbdd ⟨B, hBadm, hdisj⟩ hB
  · -- For Liu Bang's special `A₀`, the infimum is `≥ answer`, hence so is the supremum.
    have hbddAbove : BddAbove (Set.range fun A : {A : Finset ℝ // AdmissibleMark n A} =>
        ⨅ B : {B : Finset ℝ // AdmissibleMark n B ∧ Disjoint A.1 B}, L A.1 B.1) := by
      refine ⟨1, ?_⟩
      rintro _ ⟨A, rfl⟩
      have hemptyB : AdmissibleMark n ∅ ∧ Disjoint A.1 (∅ : Finset ℝ) :=
        ⟨hemptyA, Finset.disjoint_empty_right _⟩
      have hbddBelow : BddBelow (Set.range fun B : {B : Finset ℝ // AdmissibleMark n B ∧ Disjoint A.1 B} =>
          L A.1 B.1) := by
        refine ⟨0, ?_⟩
        rintro _ ⟨B', rfl⟩
        exact (L_mem_Icc A.1 B'.1 A.2.1 B'.2.1.1).1
      have h1 := ciInf_le hbddBelow ⟨∅, hemptyB⟩
      refine h1.trans ?_
      exact (L_mem_Icc A.1 ∅ A.2.1 (by simp)).2
    have h1 : (2 : ℝ) ^ n / ((2 : ℝ) ^ (n + 1) - 1) ≤
        ⨅ B : {B : Finset ℝ // AdmissibleMark n B ∧ Disjoint A₀ B}, L A₀ B.1 := by
      have : Nonempty {B : Finset ℝ // AdmissibleMark n B ∧ Disjoint A₀ B} :=
        ⟨⟨∅, hemptyA, Finset.disjoint_empty_right _⟩⟩
      apply le_ciInf
      intro B
      exact hA₀ B.1 B.2.1 B.2.2
    exact le_ciSup_of_le hbddAbove ⟨A₀, hA₀adm⟩ h1

end Imo2026P3
