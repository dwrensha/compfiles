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

Statement formalization adapted from AxiomMath/IMO2026; proof adapted from
Humanfia's Kimi-K3 solutions (https://github.com/humanfia/imo2026).
-/

namespace Imo2026P3

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

/-- The multiset of piece lengths obtained by cutting `[0,1]` at the points of a
finite set `S ⊆ (0,1)`.  We sort `S` ascending, prepend `0` and append `1`, and
take consecutive differences.  The result is a list of `|S| + 1` positive reals
summing to `1` (when `S ⊆ (0,1)`). -/
noncomputable def pieceLengths (S : Finset ℝ) : List ℝ :=
  let l : List ℝ := (0 : ℝ) :: (S.sort (· ≤ ·)) ++ [1]
  List.zipWith (fun a b => b - a) l l.tail

/-- The sum of the entries of a list `L` at the (0-indexed) even positions, after
sorting `L` in non-increasing order.  These are the entries in the `1`st, `3`rd,
`5`th, … positions of the sorted (decreasing) list, i.e. the pieces claimed by
the first mover under the greedy claiming rule. -/
noncomputable def firstPlayerShare (L : List ℝ) : ℝ :=
  let sorted := L.mergeSort (· ≥ ·)
  ((sorted.zipIdx.filter (fun p => p.2 % 2 = 0)).map (fun p => p.1)).sum

/-- `L(A,B)`: Liu Bang's total length, given Liu Bang's marks `A` and Xiang Yu's
marks `B`. -/
noncomputable def L (A B : Finset ℝ) : ℝ :=
  firstPlayerShare (pieceLengths (A ∪ B))

/-- The set of admissible markings for a player: a finite subset of `(0,1)` of
size at most `n`.  We encode it as a `Finset ℝ` subject to the side conditions. -/
def AdmissibleMark (n : ℕ) (X : Finset ℝ) : Prop :=
  (↑X ⊆ Set.Ioo (0 : ℝ) 1) ∧ X.card ≤ n

/-- The value Liu Bang can guarantee.

`V n` is the supremum over Liu Bang's admissible markings `A` of the infimum,
over Xiang Yu's admissible markings `B` disjoint from `A`, of `L A B`. -/
noncomputable def V (n : ℕ) : ℝ :=
  ⨆ A : {A : Finset ℝ // AdmissibleMark n A},
    ⨅ B : {B : Finset ℝ // AdmissibleMark n B ∧ Disjoint A.1 B}, L A.1 B.1

/-- The claimed answer value `V(n) = 2^n / (2^(n+1) - 1)`. -/
noncomputable determine answer (n : ℕ) : ℝ := (2 : ℝ) ^ n / ((2 : ℝ) ^ (n + 1) - 1)

/-! ## Correctness statements for the definitions

These pin down that the encoded definitions behave as intended. -/

/-- The piece lengths of an admissible cut set sum to `1` (the total stick
length). -/
problem pieceLengths_sum (S : Finset ℝ) (_hS : ↑S ⊆ Set.Ioo (0 : ℝ) 1) :
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
problem pieceLengths_length (S : Finset ℝ) :
    (pieceLengths S).length = S.card + 1 := by
  have h : pieceLengths S = List.zipWith (fun a b => b - a)
      ((0 : ℝ) :: (S.sort (· ≤ ·)) ++ [1])
      (((0 : ℝ) :: (S.sort (· ≤ ·)) ++ [1]).tail) := rfl
  rw [h, List.length_zipWith]
  simp [Finset.length_sort]

/-- Basic sanity bound: Liu Bang's share lies in `[0, 1]` for admissible cut
sets (it is a subset-sum of the piece lengths, which are nonnegative and sum to
`1`). -/
problem L_mem_Icc (A B : Finset ℝ)
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
    have h2 : ∀ (l : List ℝ) (n : ℕ), (l.zipIdx n).map Prod.fst = l := by
      intro l n
      induction l generalizing n with
      | nil => rfl
      | cons a l ih =>
        rw [List.zipIdx_cons, List.map_cons]
        have : Prod.fst (a, n) = a := rfl
        rw [this, ih (n + 1)]
    intro l
    have h1 := List.Sublist.map Prod.fst
      (List.filter_sublist (l := l.zipIdx) (p := fun p => p.2 % 2 = 0))
    rw [h2 l 0] at h1
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


snip begin

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
        exact le_trans (by linarith : a ≤ a + x) (ih (a := a + x) htail hy)

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
  have hlen : 0 < l.length := by
    cases l with
    | nil => contradiction
    | cons => simp
  omega

lemma admissible_cutsOfLengths (n : ℕ) (l : List ℝ) (hne : l ≠ [])
    (hpos : ∀ x ∈ l, 0 < x) (hsum : l.sum = 1)
    (hlen : l.length ≤ n + 1) : AdmissibleMark n (cutsOfLengths l) := by
  constructor
  · intro z hz
    exact mem_interiorPartialSums_Ioo l hne hpos hsum
      (by simpa [cutsOfLengths] using hz)
  · have hcard := card_cutsOfLengths l hne hpos
    omega

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
    rw [show A ∪ B = cutsOfLengths l by
      simpa [B] using Finset.union_sdiff_of_subset hsub]
    rw [pieceLengths_cutsOfLengths l hne hpos hsum]

lemma exists_reply_of_refinement_length (n : ℕ) (A : Finset ℝ) (l : List ℝ)
    (hne : l ≠ []) (hpos : ∀ x ∈ l, 0 < x) (hsum : l.sum = 1)
    (hsub : A ⊆ cutsOfLengths l) (hlen : l.length ≤ A.card + n + 1) :
    ∃ B : Finset ℝ, AdmissibleMark n B ∧ Disjoint A B ∧
      L A B = firstPlayerShare l := by
  apply exists_reply_of_refinement n A l hne hpos hsum hsub
  have hcard := card_cutsOfLengths l hne hpos
  omega

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
    have h' : (n + 1) % 2 = (m + 1) % 2 := by omega
    by_cases hn : n % 2 = 0
    · have hm : m % 2 = 0 := by omega
      simp [hn, hm]
      exact ih (n + 1) (m + 1) h'
    · have hm : ¬ m % 2 = 0 := by omega
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
      have hn2 : (n + 1 + 1) % 2 = 0 := by omega
      have hn1 : (n + 1) % 2 ≠ 0 := by omega
      simp [pairDup, List.zipIdx_cons, hn, hn1]
      change ((((pairDup xs).zipIdx (n + 1 + 1)).filter
        (fun p => p.2 % 2 = 0)).map (fun p => p.1)).sum = xs.sum
      exact ih (n + 1 + 1) hn2

lemma even_zip_sum_pairDup (xs : List ℝ) :
    ((((pairDup xs).zipIdx).filter (fun p => p.2 % 2 = 0)).map (fun p => p.1)).sum
      = xs.sum := by
  exact even_zip_sum_pairDup_aux xs 0 (by simp)

lemma odd_zip_sum_pairDup_aux (xs : List ℝ) (n : ℕ) (hn : n % 2 = 1) :
    ((((pairDup xs).zipIdx n).filter (fun p => p.2 % 2 = 0)).map (fun p => p.1)).sum
      = xs.sum := by
  induction xs generalizing n with
  | nil => simp [pairDup]
  | cons x xs ih =>
      have hn1 : (n + 1) % 2 = 0 := by omega
      have hn2 : (n + 1 + 1) % 2 = 1 := by omega
      simp [pairDup, List.zipIdx_cons, hn, hn1]
      change ((((pairDup xs).zipIdx (n + 1 + 1)).filter
        (fun p => p.2 % 2 = 0)).map (fun p => p.1)).sum = xs.sum
      exact ih (n + 1 + 1) hn2

lemma zip_sum_pairDup_aux (xs : List ℝ) (n : ℕ) :
    ((((pairDup xs).zipIdx n).filter (fun p => p.2 % 2 = 0)).map (fun p => p.1)).sum
      = xs.sum := by
  by_cases hn : n % 2 = 0
  · exact even_zip_sum_pairDup_aux xs n hn
  · have hn' : n % 2 = 1 := by omega
    exact odd_zip_sum_pairDup_aux xs n hn'

lemma length_pairDup (xs : List ℝ) : (pairDup xs).length = 2 * xs.length := by
  induction xs with
  | nil => simp [pairDup]
  | cons x xs ih =>
      rw [show pairDup (x :: xs) = x :: x :: pairDup xs by rfl]
      simp [ih]
      omega

lemma even_zip_sum_pairs_singleton_pairs (xs ys : List ℝ) (r : ℝ) :
    (((((pairDup xs) ++ r :: pairDup ys).zipIdx).filter
      (fun p => p.2 % 2 = 0)).map (fun p => p.1)).sum = xs.sum + r + ys.sum := by
  rw [List.zipIdx_append]
  simp only [List.filter_append, List.map_append, List.sum_append]
  rw [zip_sum_pairDup_aux]
  have heven : (pairDup xs).length % 2 = 0 := by
    rw [length_pairDup]
    omega
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

lemma sum_pairDup (xs : List ℝ) : (pairDup xs).sum = 2 * xs.sum := by
  induction xs with
  | nil => simp [pairDup]
  | cons x xs ih =>
      rw [show pairDup (x :: xs) = x :: x :: pairDup xs by rfl,
        List.sum_cons, List.sum_cons, ih, List.sum_cons]
      ring

lemma twice_firstPlayerShare_pairDup (xs : List ℝ) (hxs : xs.Pairwise (· ≥ ·)) :
    2 * firstPlayerShare (pairDup xs) = (pairDup xs).sum := by
  rw [firstPlayerShare_pairDup_of_pairwise xs hxs, sum_pairDup]

lemma firstPlayerShare_pairs_singleton_pairs (xs ys : List ℝ) (r : ℝ)
    (hsorted : (pairDup xs ++ r :: pairDup ys).Pairwise (· ≥ ·)) :
    firstPlayerShare (pairDup xs ++ r :: pairDup ys) = xs.sum + r + ys.sum := by
  unfold firstPlayerShare
  rw [List.mergeSort_eq_self (r := (· ≥ ·)) hsorted]
  exact even_zip_sum_pairs_singleton_pairs xs ys r

lemma surplus_pairs_singleton_pairs (xs ys : List ℝ) (r : ℝ)
    (hsorted : (pairDup xs ++ r :: pairDup ys).Pairwise (· ≥ ·)) :
    2 * firstPlayerShare (pairDup xs ++ r :: pairDup ys) =
      (pairDup xs ++ r :: pairDup ys).sum + r := by
  rw [firstPlayerShare_pairs_singleton_pairs xs ys r hsorted,
    List.sum_append, List.sum_cons, sum_pairDup, sum_pairDup]
  ring


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
  classical
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
      calc |s i| * 2 ^ p i ≤ 1 * 2 ^ p i :=
            mul_le_mul_of_nonneg_right hsi1 (le_of_lt (hp2_pos _))
        _ = 2 ^ p i := one_mul _
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
      omega
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
    exact one_lt_pow₀ (by norm_num) (by omega)
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
  simp only [sign3, hz, if_false]
  split <;> norm_num

theorem zmod3_cases (z : ZMod 3) : z = 0 ∨ z = 1 ∨ z = -1 := by
  fin_cases z
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · apply Or.inr
    apply Or.inr
    apply ZMod.val_injective 3
    rw [ZMod.val_neg_one]
    exact ZMod.val_natCast_of_lt (n := 3) (a := 2) (by omega)

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
  · intro e
    exact sign3_add_eq_zero (htE e)

theorem exists_signed_edge_bound {V E : Type*} [Fintype V] [Fintype E]
    (src dst : E → V) (x y : E → ℝ) (weight : V → ℝ)
    (hcard : Fintype.card E < Fintype.card V)
    (htotal : ∀ s : V → ℝ,
      (∑ v, s v * weight v) =
        ∑ e, (s (src e) * x e + s (dst e) * y e)) :
    ∃ s : V → ℝ,
      (∀ v, s v = 0 ∨ s v = 1 ∨ s v = -1) ∧
      (∃ v, s v ≠ 0) ∧
      |∑ v, s v * weight v| ≤ ∑ e, |x e - y e| := by
  obtain ⟨s, hs, hsne, hsedge⟩ := exists_real_signing src dst hcard
  refine ⟨s, hs, hsne, ?_⟩
  rw [htotal s]
  calc
    |∑ e, (s (src e) * x e + s (dst e) * y e)| =
        |∑ e, s (src e) * (x e - y e)| := by
          congr 1
          apply Finset.sum_congr rfl
          intro e _
          have he := hsedge e
          have he' : s (dst e) = -s (src e) := by linarith
          rw [he']
          ring
    _ ≤ ∑ e, |s (src e) * (x e - y e)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ e, |x e - y e| := by
      apply Finset.sum_le_sum
      intro e _
      rcases hs (src e) with h | h | h <;> rw [h] <;> simp [abs_sub_comm]

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

theorem unpair_pairUp_append_unpaired : ∀ l : List α,
    unpair (pairUp l) ++ (unpaired l).toList = l := by
  intro l
  induction l using pairUp.induct with
  | case1 a b t ih => simp [pairUp, unpaired, unpair, ih]
  | case2 l h =>
      cases l with
      | nil => simp [pairUp, unpaired, unpair]
      | cons a t =>
          cases t with
          | nil => simp [pairUp, unpaired, unpair]
          | cons b u => exact (h a b u rfl).elim

theorem length_pairUp : ∀ l : List α, (pairUp l).length = l.length / 2 := by
  intro l
  induction l using pairUp.induct with
  | case1 a b t ih =>
      simp only [pairUp, List.length_cons, ih]
      omega
  | case2 l h =>
      cases l with
      | nil => simp [pairUp]
      | cons a t =>
          cases t with
          | nil => simp [pairUp]
          | cons b u => exact (h a b u rfl).elim

theorem unpaired_isSome_iff : ∀ l : List α,
    (unpaired l).isSome ↔ l.length % 2 = 1 := by
  intro l
  induction l using pairUp.induct with
  | case1 a b t ih =>
      rw [unpaired, ih]
      simp only [List.length_cons]
      omega
  | case2 l h =>
      cases l with
      | nil => simp [unpaired]
      | cons a t =>
          cases t with
          | nil => simp [unpaired]
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

theorem map_fst_mergeSort_tagged (l : List (ℝ × ι)) :
    (l.mergeSort (fun a b => a.1 ≥ b.1)).map Prod.fst =
      (l.map Prod.fst).mergeSort (· ≥ ·) := by
  have hperm :
      List.Perm ((l.mergeSort (fun a b => a.1 ≥ b.1)).map Prod.fst)
        ((l.map Prod.fst).mergeSort (· ≥ ·)) :=
    ((List.mergeSort_perm _ _).map _).trans
      ((List.mergeSort_perm (l.map Prod.fst) (· ≥ ·)).symm)
  have htag :
      (l.mergeSort (fun a b : ℝ × ι => a.1 ≥ b.1)).Pairwise
        (fun a b : ℝ × ι => a.1 ≥ b.1) :=
    List.pairwise_mergeSort' _ _
  have hleft : ((l.mergeSort (fun a b => a.1 ≥ b.1)).map Prod.fst).Pairwise (· ≥ ·) :=
    htag.map Prod.fst (fun _ _ h => h)
  have hright : ((l.map Prod.fst).mergeSort (· ≥ ·)).Pairwise (· ≥ ·) :=
    List.pairwise_mergeSort' _ _
  exact hperm.eq_of_pairwise' hleft hright

theorem sum_sign_labelWeight {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → ℝ) : ∀ l : List (ℝ × ι),
    (∑ v, s v * labelWeight l v) =
      (l.map (fun z => s z.2 * z.1)).sum := by
  classical
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
              simpa only [mul_ite, mul_zero, Finset.mem_univ, if_true] using
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

theorem abstract_even_lower {ι : Type} [Fintype ι] [DecidableEq ι]
    (p : ι → ℕ) (hp : Function.Injective p)
    (l : List (ℝ × ι))
    (hsorted : l.Pairwise (fun a b => a.1 ≥ b.1))
    (hunpaired : unpaired l = none)
    (hlen : l.length < 2 * Fintype.card ι)
    (hweight : ∀ i, labelWeight l i = (2 : ℝ) ^ p i) :
    1 ≤ surplus (l.map Prod.fst) := by
  classical
  let P := pairUp l
  let src : Fin P.length → ι := fun e => (P.get e).1.2
  let dst : Fin P.length → ι := fun e => (P.get e).2.2
  let x : Fin P.length → ℝ := fun e => (P.get e).1.1
  let y : Fin P.length → ℝ := fun e => (P.get e).2.1
  have hcardP : Fintype.card (Fin P.length) < Fintype.card ι := by
    simp only [Fintype.card_fin]
    change (pairUp l).length < Fintype.card ι
    rw [length_pairUp]
    omega
  have htotal : ∀ s : ι → ℝ,
      (∑ v, s v * labelWeight l v) =
        ∑ e, (s (src e) * x e + s (dst e) * y e) := by
    intro s
    have hpair := sum_sign_weight_pairUp s l
    rw [hunpaired] at hpair
    simp only [Option.elim_none, add_zero] at hpair
    calc
      (∑ v, s v * labelWeight l v) =
          (P.map (fun q => s q.1.2 * q.1.1 + s q.2.2 * q.2.1)).sum := by
            simpa [P] using hpair
      _ = ∑ e : Fin P.length,
          (fun q => s q.1.2 * q.1.1 + s q.2.2 * q.2.1) (P.get e) := by
            exact (fin_sum_get_map P
              (fun q => s q.1.2 * q.1.1 + s q.2.2 * q.2.1)).symm
      _ = ∑ e, (s (src e) * x e + s (dst e) * y e) := by rfl
  obtain ⟨s, hs, hsne, hbound⟩ :=
    CodexMod3.exists_signed_edge_bound src dst x y (labelWeight l) hcardP htotal
  have hspow : ∀ i, s i = 1 ∨ s i = -1 ∨ s i = 0 := by
    intro i
    rcases hs i with h | h | h
    · exact Or.inr (Or.inr h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  have hpunch := pow_two_punch (ι := ι) p hp s hspow hsne
  have hsumpow :
      (∑ i, s i * labelWeight l i) = ∑ i, s i * 2 ^ p i := by
    apply Finset.sum_congr rfl
    intro i _
    rw [hweight]
  rw [hsumpow] at hbound
  have hedge_nonneg : ∀ q ∈ P, 0 ≤ q.1.1 - q.2.1 := by
    intro q hq
    exact sub_nonneg.mpr (pairUp_rel hsorted q (by simpa [P] using hq))
  have hright : (∑ e, |x e - y e|) = surplus (l.map Prod.fst) := by
    rw [show (∑ e, |x e - y e|) =
        (P.map (fun q => |q.1.1 - q.2.1|)).sum by
      simpa [x, y] using
        (fin_sum_get_map P (fun q => |q.1.1 - q.2.1|))]
    have habs : (P.map (fun q => |q.1.1 - q.2.1|)).sum =
        (P.map (fun q => q.1.1 - q.2.1)).sum := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro z hz
      rw [abs_of_nonneg (hedge_nonneg z hz)]
    rw [habs]
    have hsur := surplus_eq_pairUp (l.map Prod.fst)
    simpa [pairUp_map, unpaired_map, hunpaired, P, List.map_map,
      Function.comp_def] using hsur.symm
  rw [hright] at hbound
  exact hpunch.trans hbound

theorem abstract_lower {ι : Type} [Fintype ι] [DecidableEq ι]
    (p : ι → ℕ) (hp : Function.Injective p)
    (l : List (ℝ × ι))
    (hsorted : l.Pairwise (fun a b => a.1 ≥ b.1))
    (hnonneg : ∀ z ∈ l, 0 ≤ z.1)
    (hlen : l.length < 2 * Fintype.card ι)
    (hweight : ∀ i, labelWeight l i = (2 : ℝ) ^ p i) :
    1 ≤ surplus (l.map Prod.fst) := by
  classical
  let P := pairUp l
  let src : Fin P.length → ι := fun e => (P.get e).1.2
  let dst : Fin P.length → ι := fun e => (P.get e).2.2
  let x : Fin P.length → ℝ := fun e => (P.get e).1.1
  let y : Fin P.length → ℝ := fun e => (P.get e).2.1
  have hcardP : Fintype.card (Fin P.length) < Fintype.card ι := by
    simp only [Fintype.card_fin]
    change (pairUp l).length < Fintype.card ι
    rw [length_pairUp]
    omega
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
  have hspow : ∀ i, s i = 1 ∨ s i = -1 ∨ s i = 0 := by
    intro i
    rcases hs i with h | h | h
    · exact Or.inr (Or.inr h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  have hpunch := pow_two_punch (ι := ι) p hp s hspow hsne
  have hsumpow :
      (∑ i, s i * labelWeight l i) = ∑ i, s i * 2 ^ p i := by
    apply Finset.sum_congr rfl
    intro i _
    rw [hweight]
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
      apply List.map_congr_left
      intro z hz
      rw [abs_of_nonneg (hedge_nonneg z hz)]
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
  rw [Finset.sum_Ico_eq_sub _ hf, Finset.sum_range_sub, Finset.sum_range_sub]
  ring

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
        _ = List.range' (f 0) (f (N + 1) - f 0) := by congr 2; omega

lemma map_val_finRange (N : ℕ) :
    (List.finRange N).map (fun i => i.val) = List.range N := by
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    simp

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
  rw [map_val_finRange]
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
  (e ⟨min j N, by omega⟩).val

lemma clippedEmbedding_mono {N M : ℕ} (e : Fin (N + 1) ↪o Fin (M + 1)) :
    Monotone (clippedEmbedding e) := by
  intro a b hab
  apply e.monotone
  simp only [Fin.mk_le_mk]
  omega

lemma clippedEmbedding_of_le {N M : ℕ} (e : Fin (N + 1) ↪o Fin (M + 1))
    {j : ℕ} (hj : j ≤ N) :
    clippedEmbedding e j = (e ⟨j, by omega⟩).val := by
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
  have hqLen : q.length = N + 1 := by
    dsimp [q, N]
    rw [boundaryPoints_length]
  have hrLen : r.length = M + 1 := by
    dsimp [r, M]
    rw [boundaryPoints_length]
  have hsub : q <+ r := by
    dsimp [q, r]
    exact boundaryPoints_sublist hST
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
    rw [List.getD_eq_getElem (hn := by omega),
      List.getD_eq_getElem (hn := hri)]
    simpa [e] using he₀ ((Fin.castOrderIso hqLen.symm) ix)
  have hq0 : q.get ⟨0, by omega⟩ = 0 := by simp [q, boundaryPoints]
  have hr0 : r.get ⟨0, by omega⟩ = 0 := by simp [r, boundaryPoints]
  have hq0D : q.getD 0 0 = 0 := by simp [q, boundaryPoints]
  have hr0D : r.getD 0 0 = 0 := by simp [r, boundaryPoints]
  have hqLast : q.get ⟨N, by omega⟩ = 1 := by
    dsimp [q, N, boundaryPoints]
    simp [Finset.length_sort]
  have hrLast : r.get ⟨M, by omega⟩ = 1 := by
    dsimp [r, M, boundaryPoints]
    simp [Finset.length_sort]
  have hrNodup : r.Nodup := by
    exact (boundaryPoints_pairwise T hT).nodup
  have he0 : e ⟨0, by omega⟩ = ⟨0, by omega⟩ := by
    apply Fin.ext
    let a : Fin r.length := ⟨(e ⟨0, by omega⟩).val, by rw [hrLen]; omega⟩
    let b : Fin r.length := ⟨0, by omega⟩
    have hv : r.getD (e ⟨0, by omega⟩).val 0 = r.getD 0 0 := by
      rw [← he ⟨0, by omega⟩]
      rw [hq0D, hr0D]
    have hra : (e ⟨0, by omega⟩).val < r.length := by rw [hrLen]; omega
    have hrb : 0 < r.length := by omega
    rw [List.getD_eq_getElem (hn := hra), List.getD_eq_getElem (hn := hrb)] at hv
    have hab : a = b := hrNodup.injective_get (by simpa [a, b] using hv)
    simpa [a, b] using congrArg Fin.val hab
  have heLast : e ⟨N, by omega⟩ = ⟨M, by omega⟩ := by
    apply Fin.ext
    let a : Fin r.length := ⟨(e ⟨N, by omega⟩).val, by rw [hrLen]; omega⟩
    let b : Fin r.length := ⟨M, by omega⟩
    have hv : r.getD (e ⟨N, by omega⟩).val 0 = r.getD M 0 := by
      rw [← he ⟨N, by omega⟩]
      rw [List.getD_eq_getElem, List.getD_eq_getElem]
      simpa using hqLast.trans hrLast.symm
    have hra : (e ⟨N, by omega⟩).val < r.length := by rw [hrLen]; omega
    have hrb : M < r.length := by omega
    rw [List.getD_eq_getElem (hn := hra), List.getD_eq_getElem (hn := hrb)] at hv
    have hab : a = b := hrNodup.injective_get (by simpa [a, b] using hv)
    simpa [a, b] using congrArg Fin.val hab
  let F : ℕ → ℕ := clippedEmbedding e
  let rv : ℕ → ℝ := fun j => r.getD j 0
  let l : List (ℝ × Fin N) := taggedBlocks (intervalBlock rv F)
  have hFmono : Monotone F := clippedEmbedding_mono e
  have hF0 : F 0 = 0 := by
    rw [show F 0 = (e ⟨0, by omega⟩).val by
      exact clippedEmbedding_of_le e (Nat.zero_le N)]
    rw [he0]
  have hFN : F N = M := by
    rw [show F N = (e ⟨N, by omega⟩).val by
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
    change indexedDiffs r = pieceLengths T
    rw [pieceLengths_eq_indexedDiffs_boundaryPoints]
  · intro i
    change labelWeight l i = _
    rw [show labelWeight l i = (intervalBlock rv F i).sum by
      exact labelWeight_taggedBlocks _ i]
    rw [intervalBlock_sum rv F i (hFmono (Nat.le_succ i.val))]
    have hi : i.val ≤ N := Nat.le_of_lt i.isLt
    have his : i.val + 1 ≤ N := i.isLt
    have hFi : F i.val = (e ⟨i.val, by omega⟩).val :=
      clippedEmbedding_of_le e hi
    have hFis : F (i.val + 1) = (e ⟨i.val + 1, by omega⟩).val :=
      clippedEmbedding_of_le e his
    rw [hFi, hFis]
    unfold rv
    change r.getD (e ⟨i.val + 1, by omega⟩).val 0 -
        r.getD (e ⟨i.val, by omega⟩).val 0 =
      (pieceLengths S).getD i.val 0
    rw [← he ⟨i.val + 1, by omega⟩, ← he ⟨i.val, by omega⟩]
    rw [pieceLengths_eq_indexedDiffs_boundaryPoints]
    dsimp [q]
    have hiq : i.val < (boundaryPoints S).length - 1 := by
      rw [boundaryPoints_length]
      omega
    rw [indexedDiffs_getD _ hiq]


open scoped BigOperators


lemma codexLowerCuts_card (n : ℕ) : (codexLowerCuts n).card = n := by
  have h := card_cutsOfLengths (codexDyadicWeights n)
    (codexDyadicWeights_ne_nil n) (codexDyadicWeights_pos n)
  have h' : (codexLowerCuts n).card + 1 = n + 1 := by
    simpa [codexLowerCuts, codexDyadicWeights_length] using h
  omega

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
  have hAcard : A.card = n := by exact codexLowerCuts_card n
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
  have hTcard : T.card = A.card + B.card := by
    dsimp [T]
    rw [Finset.card_union_of_disjoint hdisj]
  have hscaledLen : scaled.length < 2 * Fintype.card (Fin (A.card + 1)) := by
    simp only [scaled, List.length_map, ls, List.length_mergeSort, Fintype.card_fin]
    rw [hlenL, hTcard]
    have hBcard : B.card ≤ n := hB.2
    omega
  have hscaledWeight : ∀ i : Fin (A.card + 1),
      labelWeight scaled i = (2 : ℝ) ^ i.val := by
    intro i
    rw [show labelWeight scaled i = D * labelWeight ls i by
      exact labelWeight_scale D ls i]
    rw [show labelWeight ls i = labelWeight l i by
      exact labelWeight_perm (List.mergeSort_perm l _) i]
    rw [hlweight]
    have hi' : i.val < n + 1 := by omega
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
        exact map_fst_mergeSort_tagged l
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
    (l.map fun x => x / 2).sum = l.sum / 2 := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      rw [List.map_cons, List.sum_cons, List.sum_cons, ih]
      ring

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
    exact hp.flatMap fun a _ => List.Perm.refl [a, a]
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
  have hppos : ∀ x ∈ p, 0 < x := by
    exact pieceLengths_pos A hA.1
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
      omega)
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
  classical
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
      omega
    | cons a t =>
      cases ht : t with
      | nil => simp [hs, ht] at hslen; omega
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
        have hden_nat : 1 ≤ Fintype.card α := by omega
        have hden_pos : 0 < (Fintype.card α : ℝ) - 1 := by
          have hc : (1 : ℝ) < Fintype.card α := by
            exact_mod_cast (show 1 < Fintype.card α by omega)
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
      exact_mod_cast (show 1 < Fintype.card α by omega)
    positivity

theorem exists_disjoint_subset_sums_close (m : ℕ) (hm : 0 < m)
    (a : Fin m → ℝ) (ha : ∀ i, 0 ≤ a i) (hasum : ∑ i, a i = 1) :
    ∃ I J : Finset (Fin m), Disjoint I J ∧ (I ∪ J).Nonempty ∧
      0 ≤ (∑ i ∈ I, a i) - ∑ j ∈ J, a j ∧
      (∑ i ∈ I, a i) - ∑ j ∈ J, a j ≤ 1 / ((2 : ℝ) ^ m - 1) := by
  classical
  have hcard : 2 ≤ Fintype.card (Finset (Fin m)) := by
    simp only [Fintype.card_finset, Fintype.card_fin]
    have hpow : 2 ^ 1 ≤ 2 ^ m :=
      Nat.pow_le_pow_right (by omega) (by omega)
    simpa using hpow
  have hsum0 : ∀ I : Finset (Fin m), 0 ≤ ∑ i ∈ I, a i := by
    intro I
    exact Finset.sum_nonneg fun i _ => ha i
  have hsum1 : ∀ I : Finset (Fin m), (∑ i ∈ I, a i) ≤ 1 := by
    intro I
    rw [← hasum]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ I)
      (fun i _ _ => ha i)
  obtain ⟨A, B, hABne, hABclose⟩ :=
    exists_close_pair_of_finite (fun I : Finset (Fin m) => ∑ i ∈ I, a i)
      hcard hsum0 hsum1
  have hclose :
      |(∑ i ∈ A, a i) - ∑ j ∈ B, a j| ≤ 1 / ((2 : ℝ) ^ m - 1) := by
    simpa only [Fintype.card_finset, Fintype.card_fin, Nat.cast_pow,
      Nat.cast_ofNat] using hABclose
  let I₀ := A \ B
  let J₀ := B \ A
  have hdisj : Disjoint I₀ J₀ := by
    rw [Finset.disjoint_left]
    intro x hxI hxJ
    simp only [I₀, Finset.mem_sdiff] at hxI
    simp only [J₀, Finset.mem_sdiff] at hxJ
    exact hxI.2 hxJ.1
  have hnonempty : (I₀ ∪ J₀).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty, Finset.union_eq_empty] at h
    apply hABne
    apply Finset.Subset.antisymm
    · exact Finset.sdiff_eq_empty_iff_subset.mp (by simpa [I₀] using h.1)
    · exact Finset.sdiff_eq_empty_iff_subset.mp (by simpa [J₀] using h.2)
  have hdiff :
      (∑ i ∈ I₀, a i) - ∑ j ∈ J₀, a j =
        (∑ i ∈ A, a i) - ∑ j ∈ B, a j := by
    have hA := Finset.sum_inter_add_sum_sdiff A B a
    have hB := Finset.sum_inter_add_sum_sdiff B A a
    rw [Finset.inter_comm B A] at hB
    dsimp [I₀, J₀]
    linarith
  by_cases horient : (∑ j ∈ B, a j) ≤ ∑ i ∈ A, a i
  · refine ⟨I₀, J₀, hdisj, hnonempty, ?_, ?_⟩
    · rw [hdiff]
      linarith
    · rw [hdiff]
      rw [abs_of_nonneg (sub_nonneg.mpr horient)] at hclose
      exact hclose
  · refine ⟨J₀, I₀, hdisj.symm, by simpa [Finset.union_comm] using hnonempty, ?_, ?_⟩
    · rw [← neg_sub, hdiff]
      linarith
    · rw [← neg_sub, hdiff]
      rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge horient))] at hclose
      linarith

end CodexClosePoints

open List


theorem subperm_perm_of_length_eq {α : Type*} {a b : List α}
    (h : a <+~ b) (hl : a.length = b.length) : a ~ b := by
  rw [subperm_iff] at h
  obtain ⟨l, hlb, hal⟩ := h
  have hlen : a.length = l.length := by
    rw [hl, hlb.length_eq]
  have hal_eq : a = l := hal.eq_of_length hlen
  simpa [hal_eq] using hlb

open scoped BigOperators

variable {m : ℕ}

def finBlocks (b : Fin m → List ℝ) : List (List ℝ) :=
  (List.finRange m).map b

def flattenFinBlocks (b : Fin m → List ℝ) : List ℝ :=
  (finBlocks b).flatten

lemma map_fst_taggedBlocks_eq_flattenFinBlocks (b : Fin m → List ℝ) :
    (taggedBlocks b).map Prod.fst = flattenFinBlocks b := by
  unfold taggedBlocks flattenFinBlocks finBlocks
  rw [List.map_flatMap]
  change (List.finRange m).flatMap
      (fun i => ((b i).map fun x => (x, i)).map Prod.fst) =
    (List.finRange m).flatMap b
  apply List.flatMap_congr
  intro i hi
  rw [List.map_map]
  change (b i).map (fun x => x) = b i
  simp

lemma indexedDiffs_scanl (l : List ℝ) (a : ℝ) :
    indexedDiffs (l.scanl (· + ·) a) = l := by
  rw [← zipWith_tail_diff_eq_indexedDiffs]
  exact zipWith_scanl_tail l a

lemma map_sum_finBlocks_eq (p : List ℝ) (b : Fin p.length → List ℝ)
    (hsum : ∀ i, (b i).sum = p.get i) :
    (finBlocks b).map List.sum = p := by
  unfold finBlocks
  rw [List.map_map]
  have hcongr : (List.finRange p.length).map (List.sum ∘ b) =
      (List.finRange p.length).map p.get := by
    apply List.map_congr_left
    intro i hi
    exact hsum i
  rw [hcongr]
  exact List.map_get_finRange p

lemma flattenFinBlocks_sum (p : List ℝ) (b : Fin p.length → List ℝ)
    (hsum : ∀ i, (b i).sum = p.get i) :
    (flattenFinBlocks b).sum = p.sum := by
  unfold flattenFinBlocks
  rw [List.sum_flatten, map_sum_finBlocks_eq p b hsum]

lemma flattenFinBlocks_pos (b : Fin m → List ℝ)
    (hpos : ∀ i, ∀ x ∈ b i, 0 < x) :
    ∀ x ∈ flattenFinBlocks b, 0 < x := by
  intro x hx
  simp only [flattenFinBlocks, finBlocks, List.mem_flatten, List.mem_map,
    List.mem_finRange, true_and] at hx
  obtain ⟨block, ⟨i, rfl⟩, hx⟩ := hx
  exact hpos i x hx

lemma flattenFinBlocks_ne_nil (b : Fin m → List ℝ)
    (hm : 0 < m) (hne : ∀ i, b i ≠ []) :
    flattenFinBlocks b ≠ [] := by
  intro h
  have i : Fin m := ⟨0, hm⟩
  have hmem : b i ∈ finBlocks b := by
    simp [finBlocks]
  have : b i = [] := by
    exact List.flatten_eq_nil_iff.mp (by simpa [flattenFinBlocks] using h) _ hmem
  exact hne i this

lemma scanl_blockSums_mem_flatten (L : List (List ℝ)) (a z : ℝ)
    (hz : z ∈ (L.map List.sum).scanl (· + ·) a) :
    z ∈ L.flatten.scanl (· + ·) a := by
  induction L generalizing a z with
  | nil => simpa using hz
  | cons block rest ih =>
      rw [List.map_cons, List.scanl_cons] at hz
      rcases List.mem_cons.mp hz with rfl | hz
      · rw [List.flatten_cons, List.scanl_append]
        exact List.mem_append_left _ (by cases block <;> simp [List.scanl_cons])
      · have hz' := ih (a := a + block.sum) (z := z) hz
        have hscan : rest.flatten.scanl (· + ·) (a + block.sum) =
            (a + block.sum) ::
              (rest.flatten.scanl (· + ·) (a + block.sum)).tail := by
          cases rest.flatten <;> simp [List.scanl_cons]
        rw [hscan] at hz'
        rcases List.mem_cons.mp hz' with hzeq | hztail
        · rw [hzeq, List.flatten_cons, List.scanl_append, foldl_add_init]
          apply List.mem_append_left
          have hlast := scanl_last_eq_sum block a (by simp)
          rw [← hlast]
          exact List.getLast_mem (by simp)
        · rw [List.flatten_cons, List.scanl_append, foldl_add_init]
          exact List.mem_append_right _ hztail

lemma scanl_piece_mem_flattenFinBlocks (p : List ℝ)
    (b : Fin p.length → List ℝ)
    (hsum : ∀ i, (b i).sum = p.get i) {z : ℝ}
    (hz : z ∈ p.scanl (· + ·) 0) :
    z ∈ (flattenFinBlocks b).scanl (· + ·) 0 := by
  have hmapsum := map_sum_finBlocks_eq p b hsum
  rw [← hmapsum] at hz
  exact scanl_blockSums_mem_flatten (finBlocks b) 0 z hz

lemma cutsOfLengths_subset_flattenFinBlocks (p : List ℝ)
    (hpne : p ≠ []) (hppos : ∀ x ∈ p, 0 < x) (hpsum : p.sum = 1)
    (b : Fin p.length → List ℝ) (hbne : ∀ i, b i ≠ [])
    (hbpos : ∀ i, ∀ x ∈ b i, 0 < x)
    (hbsum : ∀ i, (b i).sum = p.get i) :
    cutsOfLengths p ⊆ cutsOfLengths (flattenFinBlocks b) := by
  intro z hz
  have hzint : z ∈ interiorPartialSums p := by simpa [cutsOfLengths] using hz
  have hzIoo := mem_interiorPartialSums_Ioo p hpne hppos hpsum hzint
  have hzfull : z ∈ p.scanl (· + ·) 0 := by
    exact List.mem_of_mem_tail (List.mem_of_mem_dropLast hzint)
  have hzfull' := scanl_piece_mem_flattenFinBlocks p b hbsum hzfull
  have hm : 0 < p.length := by
    cases p with
    | nil => contradiction
    | cons => simp
  have hfne : flattenFinBlocks b ≠ [] := flattenFinBlocks_ne_nil b hm hbne
  have hfpos : ∀ x ∈ flattenFinBlocks b, 0 < x :=
    flattenFinBlocks_pos b hbpos
  have hfsum : (flattenFinBlocks b).sum = 1 := by
    rw [flattenFinBlocks_sum p b hbsum, hpsum]
  have hzint' := mem_interiorPartialSums_of_mem_scanl_Ioo
    (flattenFinBlocks b) hfne hfpos hfsum hzfull' hzIoo
  simpa [cutsOfLengths] using hzint'


open scoped BigOperators


noncomputable def commonAtoms : List ℝ → List ℝ → List ℝ
  | [], _ => []
  | _, [] => []
  | x :: xs, y :: ys =>
      if x = y then
        x :: commonAtoms xs ys
      else if x < y then
        x :: commonAtoms xs ((y - x) :: ys)
      else
        y :: commonAtoms ((x - y) :: xs) ys
termination_by xs ys => xs.length + ys.length
decreasing_by all_goals simp_all <;> omega

lemma sum_pos_of_all_pos {l : List ℝ} (hne : l ≠ [])
    (hpos : ∀ x ∈ l, 0 < x) : 0 < l.sum := by
  cases l with
  | nil => contradiction
  | cons x xs =>
      have hx : 0 < x := hpos x List.mem_cons_self
      have hxs : 0 ≤ xs.sum := List.sum_nonneg fun z hz =>
        (hpos z (List.mem_cons_of_mem _ hz)).le
      simp only [List.sum_cons]
      linarith

set_option maxHeartbeats 1000000 in
theorem commonAtoms_spec (xs ys : List ℝ)
    (hxpos : ∀ x ∈ xs, 0 < x) (hypos : ∀ y ∈ ys, 0 < y)
    (hsum : xs.sum = ys.sum) :
    (∀ z ∈ commonAtoms xs ys, 0 < z) ∧
      (commonAtoms xs ys).sum = xs.sum ∧
      (commonAtoms xs ys).length ≤ xs.length + ys.length - 1 := by
  cases xs with
  | nil =>
      have hys : ys = [] := by
        by_contra hne
        have hp := sum_pos_of_all_pos hne hypos
        simp at hsum
        linarith
      subst ys
      simp [commonAtoms]
  | cons x xt =>
      cases ys with
      | nil =>
          have hxs : (x :: xt).sum > 0 :=
            sum_pos_of_all_pos (by simp) hxpos
          have hz : (x :: xt).sum = 0 := by simpa using hsum
          exact (ne_of_gt hxs hz).elim
      | cons y yt =>
          have hx : 0 < x := hxpos x List.mem_cons_self
          have hy : 0 < y := hypos y List.mem_cons_self
          have hxt : ∀ z ∈ xt, 0 < z :=
            fun z hz => hxpos z (List.mem_cons_of_mem _ hz)
          have hyt : ∀ z ∈ yt, 0 < z :=
            fun z hz => hypos z (List.mem_cons_of_mem _ hz)
          by_cases heq : x = y
          · subst y
            have htailSum : xt.sum = yt.sum := by
              simpa using hsum
            have ih := commonAtoms_spec xt yt hxt hyt htailSum
            refine ⟨?_, ?_, ?_⟩
            · intro z hz
              simp [commonAtoms] at hz
              rcases hz with rfl | hz
              · exact hx
              · exact ih.1 z hz
            · simp [commonAtoms, ih.2.1]
            · simp [commonAtoms]
              have hlen := ih.2.2
              omega
          · by_cases hlt : x < y
            · have hdiff : 0 < y - x := sub_pos.mpr hlt
              have hnewpos : ∀ z ∈ (y - x) :: yt, 0 < z := by
                intro z hz
                rcases List.mem_cons.mp hz with rfl | hz
                · exact hdiff
                · exact hyt z hz
              have hnewsum : xt.sum = ((y - x) :: yt).sum := by
                simp only [List.sum_cons] at hsum ⊢
                linarith
              have ih := commonAtoms_spec xt ((y - x) :: yt) hxt hnewpos hnewsum
              refine ⟨?_, ?_, ?_⟩
              · intro z hz
                simp [commonAtoms, heq, hlt] at hz
                rcases hz with rfl | hz
                · exact hx
                · exact ih.1 z hz
              · simp [commonAtoms, heq, hlt, ih.2.1]
              · simp [commonAtoms, heq, hlt]
                have hlen := ih.2.2
                simp only [List.length_cons] at hlen
                omega
            · have hyx : y < x := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm heq)
              have hdiff : 0 < x - y := sub_pos.mpr hyx
              have hnewpos : ∀ z ∈ (x - y) :: xt, 0 < z := by
                intro z hz
                rcases List.mem_cons.mp hz with rfl | hz
                · exact hdiff
                · exact hxt z hz
              have hnewsum : ((x - y) :: xt).sum = yt.sum := by
                simp only [List.sum_cons] at hsum ⊢
                linarith
              have ih := commonAtoms_spec ((x - y) :: xt) yt hnewpos hyt hnewsum
              refine ⟨?_, ?_, ?_⟩
              · intro z hz
                simp [commonAtoms, heq, hlt] at hz
                rcases hz with rfl | hz
                · exact hy
                · exact ih.1 z hz
              · simp [commonAtoms, heq, hlt, ih.2.1]
                simp only [List.sum_cons] at hsum
                linarith
              · simp [commonAtoms, heq, hlt]
                have hlen := ih.2.2
                simp only [List.length_cons] at hlen
                omega
termination_by xs.length + ys.length
decreasing_by all_goals simp_all <;> omega

def ScanRefines (coarse fine : List ℝ) : Prop :=
  ∀ a z, z ∈ coarse.scanl (· + ·) a → z ∈ fine.scanl (· + ·) a

lemma ScanRefines.cons_same {coarse fine : List ℝ}
    (h : ScanRefines coarse fine) (x : ℝ) :
    ScanRefines (x :: coarse) (x :: fine) := by
  intro a z hz
  rw [List.scanl_cons] at hz ⊢
  rcases List.mem_cons.mp hz with rfl | hz
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ (h (a + x) z hz)

lemma ScanRefines.absorb_left {d : ℝ} {coarse fine : List ℝ}
    (h : ScanRefines (d :: coarse) fine) (x : ℝ) :
    ScanRefines ((x + d) :: coarse) (x :: fine) := by
  intro a z hz
  rw [List.scanl_cons] at hz ⊢
  rcases List.mem_cons.mp hz with rfl | hz
  · exact List.mem_cons_self
  · apply List.mem_cons_of_mem
    apply h (a + x) z
    rw [List.scanl_cons]
    apply List.mem_cons_of_mem
    simpa only [add_assoc] using hz

set_option maxHeartbeats 1000000 in
theorem commonAtoms_scanRefines (xs ys : List ℝ)
    (hxpos : ∀ x ∈ xs, 0 < x) (hypos : ∀ y ∈ ys, 0 < y)
    (hsum : xs.sum = ys.sum) :
    ScanRefines xs (commonAtoms xs ys) ∧
      ScanRefines ys (commonAtoms xs ys) := by
  cases xs with
  | nil =>
      have hys : ys = [] := by
        by_contra hne
        have hp := sum_pos_of_all_pos hne hypos
        simp at hsum
        linarith
      subst ys
      constructor <;> intro a z hz <;> simpa [commonAtoms] using hz
  | cons x xt =>
      cases ys with
      | nil =>
          have hxs : (x :: xt).sum > 0 :=
            sum_pos_of_all_pos (by simp) hxpos
          have hz : (x :: xt).sum = 0 := by simpa using hsum
          exact (ne_of_gt hxs hz).elim
      | cons y yt =>
          have hx : 0 < x := hxpos x List.mem_cons_self
          have hy : 0 < y := hypos y List.mem_cons_self
          have hxt : ∀ z ∈ xt, 0 < z :=
            fun z hz => hxpos z (List.mem_cons_of_mem _ hz)
          have hyt : ∀ z ∈ yt, 0 < z :=
            fun z hz => hypos z (List.mem_cons_of_mem _ hz)
          by_cases heq : x = y
          · subst y
            have htailSum : xt.sum = yt.sum := by simpa using hsum
            have ih := commonAtoms_scanRefines xt yt hxt hyt htailSum
            simpa [commonAtoms] using
              And.intro (ih.1.cons_same x) (ih.2.cons_same x)
          · by_cases hlt : x < y
            · let d := y - x
              have hd : 0 < d := sub_pos.mpr hlt
              have hnewpos : ∀ z ∈ d :: yt, 0 < z := by
                intro z hz
                rcases List.mem_cons.mp hz with rfl | hz
                · exact hd
                · exact hyt z hz
              have hnewsum : xt.sum = (d :: yt).sum := by
                dsimp [d]
                simp only [List.sum_cons] at hsum ⊢
                linarith
              have ih := commonAtoms_scanRefines xt (d :: yt) hxt hnewpos hnewsum
              have hleft : ScanRefines (x :: xt)
                  (x :: commonAtoms xt (d :: yt)) := ih.1.cons_same x
              have hright0 : ScanRefines ((x + d) :: yt)
                  (x :: commonAtoms xt (d :: yt)) := ih.2.absorb_left x
              have hxd : x + d = y := by dsimp [d]; ring
              have hright : ScanRefines (y :: yt)
                  (x :: commonAtoms xt (d :: yt)) := by simpa [hxd] using hright0
              simpa [commonAtoms, heq, hlt, d] using And.intro hleft hright
            · have hyx : y < x := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm heq)
              let d := x - y
              have hd : 0 < d := sub_pos.mpr hyx
              have hnewpos : ∀ z ∈ d :: xt, 0 < z := by
                intro z hz
                rcases List.mem_cons.mp hz with rfl | hz
                · exact hd
                · exact hxt z hz
              have hnewsum : (d :: xt).sum = yt.sum := by
                dsimp [d]
                simp only [List.sum_cons] at hsum ⊢
                linarith
              have ih := commonAtoms_scanRefines (d :: xt) yt hnewpos hyt hnewsum
              have hleft0 : ScanRefines ((y + d) :: xt)
                  (y :: commonAtoms (d :: xt) yt) := ih.1.absorb_left y
              have hyd : y + d = x := by dsimp [d]; ring
              have hleft : ScanRefines (x :: xt)
                  (y :: commonAtoms (d :: xt) yt) := by simpa [hyd] using hleft0
              have hright : ScanRefines (y :: yt)
                  (y :: commonAtoms (d :: xt) yt) := ih.2.cons_same y
              simpa [commonAtoms, heq, hlt, d] using And.intro hleft hright
termination_by xs.length + ys.length
decreasing_by all_goals simp_all <;> omega


open scoped BigOperators List


theorem scanl_sublist_of_scanRefines (coarse fine : List ℝ)
    (hcpos : ∀ x ∈ coarse, 0 < x) (hfpos : ∀ x ∈ fine, 0 < x)
    (href : ScanRefines coarse fine) :
    coarse.scanl (· + ·) 0 <+ fine.scanl (· + ·) 0 := by
  apply List.sublist_of_subperm_of_sortedLE
  · apply List.subperm_of_subset (pairwise_scanl_lt coarse 0 hcpos).nodup
    intro z hz
    exact href 0 z hz
  · exact ((pairwise_scanl_lt coarse 0 hcpos).imp fun h => h.le).sortedLE
  · exact ((pairwise_scanl_lt fine 0 hfpos).imp fun h => h.le).sortedLE

theorem exists_blocks_of_scanRefines (coarse fine : List ℝ)
    (hcpos : ∀ x ∈ coarse, 0 < x) (hfpos : ∀ x ∈ fine, 0 < x)
    (hsum : coarse.sum = fine.sum) (href : ScanRefines coarse fine) :
    ∃ b : Fin coarse.length → List ℝ,
      (∀ i, b i ≠ []) ∧
      (∀ i, ∀ x ∈ b i, 0 < x) ∧
      (∀ i, (b i).sum = coarse.get i) ∧
      flattenFinBlocks b = fine := by
  let N := coarse.length
  let M := fine.length
  let q := coarse.scanl (· + ·) 0
  let r := fine.scanl (· + ·) 0
  have hqLen : q.length = N + 1 := by simp [q, N]
  have hrLen : r.length = M + 1 := by simp [r, M]
  have hsub : q <+ r := by
    dsimp [q, r]
    exact scanl_sublist_of_scanRefines coarse fine hcpos hfpos href
  rw [List.sublist_iff_exists_fin_orderEmbedding_get_eq] at hsub
  obtain ⟨e₀, he₀⟩ := hsub
  let e : Fin (N + 1) ↪o Fin (M + 1) :=
    (Fin.castOrderIso hqLen.symm).toOrderEmbedding |>.trans
      (e₀.trans (Fin.castOrderIso hrLen).toOrderEmbedding)
  have he : ∀ ix : Fin (N + 1),
      q.getD ix.val 0 = r.getD (e ix).val 0 := by
    intro ix
    have hri : (e ix).val < r.length := by rw [hrLen]; exact (e ix).isLt
    rw [List.getD_eq_getElem (hn := by rw [hqLen]; exact ix.isLt),
      List.getD_eq_getElem (hn := hri)]
    simpa [e] using he₀ ((Fin.castOrderIso hqLen.symm) ix)
  have hq0D : q.getD 0 0 = 0 := by simp [q]
  have hr0D : r.getD 0 0 = 0 := by simp [r]
  have hqLastD : q.getD N 0 = coarse.sum := by
    have hlast := scanl_last_eq_sum coarse 0 (by simp)
    rw [List.getLast_eq_getElem] at hlast
    simp only [zero_add] at hlast
    rw [List.getD_eq_getElem (hn := by rw [hqLen]; omega)]
    convert hlast using 1; simp [q, N]
  have hrLastD : r.getD M 0 = fine.sum := by
    have hlast := scanl_last_eq_sum fine 0 (by simp)
    rw [List.getLast_eq_getElem] at hlast
    simp only [zero_add] at hlast
    rw [List.getD_eq_getElem (hn := by rw [hrLen]; omega)]
    convert hlast using 1; simp [r, M]
  have hrNodup : r.Nodup := by
    dsimp [r]
    exact (pairwise_scanl_lt fine 0 hfpos).nodup
  have he0 : e ⟨0, by omega⟩ = ⟨0, by omega⟩ := by
    apply Fin.ext
    let a : Fin r.length := ⟨(e ⟨0, by omega⟩).val, by rw [hrLen]; omega⟩
    let b : Fin r.length := ⟨0, by rw [hrLen]; omega⟩
    have hv : r.getD (e ⟨0, by omega⟩).val 0 = r.getD 0 0 := by
      rw [← he ⟨0, by omega⟩, hq0D, hr0D]
    have hra : (e ⟨0, by omega⟩).val < r.length := by rw [hrLen]; omega
    have hrb : 0 < r.length := by rw [hrLen]; omega
    rw [List.getD_eq_getElem (hn := hra), List.getD_eq_getElem (hn := hrb)] at hv
    have hab : a = b := hrNodup.injective_get (by simpa [a, b] using hv)
    simpa [a, b] using congrArg Fin.val hab
  have heLast : e ⟨N, by omega⟩ = ⟨M, by omega⟩ := by
    apply Fin.ext
    let a : Fin r.length := ⟨(e ⟨N, by omega⟩).val, by rw [hrLen]; omega⟩
    let b : Fin r.length := ⟨M, by rw [hrLen]; omega⟩
    have hv : r.getD (e ⟨N, by omega⟩).val 0 = r.getD M 0 := by
      rw [← he ⟨N, by omega⟩, hqLastD, hrLastD, hsum]
    have hra : (e ⟨N, by omega⟩).val < r.length := by rw [hrLen]; omega
    have hrb : M < r.length := by rw [hrLen]; omega
    rw [List.getD_eq_getElem (hn := hra), List.getD_eq_getElem (hn := hrb)] at hv
    have hab : a = b := hrNodup.injective_get (by simpa [a, b] using hv)
    simpa [a, b] using congrArg Fin.val hab
  let F : ℕ → ℕ := clippedEmbedding e
  let rv : ℕ → ℝ := fun j => r.getD j 0
  let b : Fin N → List ℝ := intervalBlock rv F
  have hFmono : Monotone F := clippedEmbedding_mono e
  have hF0 : F 0 = 0 := by
    rw [show F 0 = (e ⟨0, by omega⟩).val by
      exact clippedEmbedding_of_le e (Nat.zero_le N)]
    rw [he0]
  have hFN : F N = M := by
    rw [show F N = (e ⟨N, by omega⟩).val by
      exact clippedEmbedding_of_le e (le_rfl)]
    rw [heLast]
  have hflat : flattenFinBlocks b = fine := by
    rw [← map_fst_taggedBlocks_eq_flattenFinBlocks]
    rw [show (taggedBlocks b).map Prod.fst =
        (List.range' (F 0) (F N - F 0)).map
          (fun j => rv (j + 1) - rv j) by
      exact map_fst_tagged_intervalBlocks rv F hFmono]
    rw [hF0, hFN]
    unfold rv
    rw [show List.range' 0 (M - 0) = List.range (r.length - 1) by
      rw [Nat.sub_zero, hrLen]
      simp only [Nat.add_sub_cancel_right]
      exact List.range_eq_range'.symm]
    change indexedDiffs r = fine
    dsimp [r]
    exact indexedDiffs_scanl fine 0
  have hbsum : ∀ i, (b i).sum = coarse.get i := by
    intro i
    change (intervalBlock rv F i).sum = coarse.get i
    rw [intervalBlock_sum rv F i (hFmono (Nat.le_succ i.val))]
    have hi : i.val ≤ N := Nat.le_of_lt i.isLt
    have his : i.val + 1 ≤ N := i.isLt
    have hFi : F i.val = (e ⟨i.val, by omega⟩).val :=
      clippedEmbedding_of_le e hi
    have hFis : F (i.val + 1) = (e ⟨i.val + 1, by omega⟩).val :=
      clippedEmbedding_of_le e his
    rw [hFi, hFis]
    unfold rv
    rw [← he ⟨i.val + 1, by omega⟩, ← he ⟨i.val, by omega⟩]
    have hiq : i.val < q.length - 1 := by rw [hqLen]; omega
    rw [← indexedDiffs_getD q hiq]
    rw [show indexedDiffs q = coarse by
      dsimp [q]
      exact indexedDiffs_scanl coarse 0]
    rw [List.getD_eq_getElem (hn := by simp [N])]
    rfl
  have hbne : ∀ i, b i ≠ [] := by
    intro i hnil
    have hi : i.val ≤ N := Nat.le_of_lt i.isLt
    have his : i.val + 1 ≤ N := i.isLt
    have hFi : F i.val = (e ⟨i.val, by omega⟩).val :=
      clippedEmbedding_of_le e hi
    have hFis : F (i.val + 1) = (e ⟨i.val + 1, by omega⟩).val :=
      clippedEmbedding_of_le e his
    have hlt : F i.val < F (i.val + 1) := by
      rw [hFi, hFis]
      exact e.strictMono (by simp)
    have hlen := congrArg List.length hnil
    simp [b, intervalBlock] at hlen
    omega
  have hbpos : ∀ i, ∀ x ∈ b i, 0 < x := by
    intro i x hx
    apply hfpos x
    have hxflat : x ∈ flattenFinBlocks b := by
      simp only [flattenFinBlocks, finBlocks, List.mem_flatten, List.mem_map,
        List.mem_finRange, true_and]
      exact ⟨b i, ⟨i, rfl⟩, hx⟩
    simpa [hflat] using hxflat
  exact ⟨b, hbne, hbpos, hbsum, hflat⟩


open scoped BigOperators List


noncomputable def selectedList (p : List ℝ) (I : Finset (Fin p.length)) : List ℝ :=
  (I.sort (· ≤ ·)).map p.get

lemma selectedList_length (p : List ℝ) (I : Finset (Fin p.length)) :
    (selectedList p I).length = I.card := by
  simp [selectedList, Finset.length_sort]

lemma selectedList_pos (p : List ℝ) (I : Finset (Fin p.length))
    (hp : ∀ x ∈ p, 0 < x) :
    ∀ x ∈ selectedList p I, 0 < x := by
  intro x hx
  simp only [selectedList, List.mem_map] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  exact hp (p.get i) (List.get_mem p i)

lemma selectedList_sum (p : List ℝ) (I : Finset (Fin p.length)) :
    (selectedList p I).sum = ∑ i ∈ I, p.get i := by
  unfold selectedList
  rw [← List.sum_toFinset p.get (Finset.sort_nodup I (· ≤ ·))]
  simp

noncomputable def selectedIndex (p : List ℝ) (I : Finset (Fin p.length))
    (i : Fin p.length) (hi : i ∈ I) : Fin (selectedList p I).length :=
  Fin.cast (selectedList_length p I).symm
    ((I.orderIsoOfFin rfl).symm ⟨i, hi⟩)

lemma selectedList_get_orderEmb (p : List ℝ) (I : Finset (Fin p.length))
    (k : Fin I.card) :
    (selectedList p I).get (Fin.cast (selectedList_length p I).symm k) =
      p.get (I.orderEmbOfFin rfl k) := by
  unfold selectedList
  rw [List.get_eq_getElem]
  simp only [List.getElem_map]
  apply congrArg p.get
  apply Fin.ext
  rfl

lemma selectedList_get_selectedIndex (p : List ℝ) (I : Finset (Fin p.length))
    (i : Fin p.length) (hi : i ∈ I) :
    (selectedList p I).get (selectedIndex p I i hi) = p.get i := by
  unfold selectedIndex
  rw [selectedList_get_orderEmb]
  apply congrArg p.get
  apply Fin.ext
  change ↑(I.orderIsoOfFin rfl ((I.orderIsoOfFin rfl).symm ⟨i, hi⟩)) = i.val
  rw [OrderIso.apply_symm_apply]

lemma selectedIndex_orderEmb (p : List ℝ) (I : Finset (Fin p.length))
    (k : Fin I.card) :
    selectedIndex p I (I.orderEmbOfFin rfl k) (I.orderEmbOfFin_mem rfl k) =
      Fin.cast (selectedList_length p I).symm k := by
  unfold selectedIndex
  apply Fin.ext
  change ↑((I.orderIsoOfFin rfl).symm (I.orderIsoOfFin rfl k)) = k.val
  rw [OrderIso.symm_apply_apply]

lemma sort_eq_ofFn_orderEmb (I : Finset (Fin m)) :
    I.sort (· ≤ ·) = List.ofFn (I.orderEmbOfFin rfl) := by
  apply List.ext_getElem
  · simp [Finset.length_sort]
  · intro k h₁ h₂
    simp only [List.getElem_ofFn]
    exact (Finset.orderEmbOfFin_apply I rfl ⟨k, by simpa using h₁⟩).symm

noncomputable def selectedBlockAt (p : List ℝ)
    (I : Finset (Fin p.length))
    (b : Fin (selectedList p I).length → List ℝ) (i : Fin p.length) : List ℝ :=
  if hi : i ∈ I then b (selectedIndex p I i hi) else []

lemma flatMap_sort_selectedBlockAt (p : List ℝ)
    (I : Finset (Fin p.length))
    (b : Fin (selectedList p I).length → List ℝ) :
    (I.sort (· ≤ ·)).flatMap (selectedBlockAt p I b) = flattenFinBlocks b := by
  rw [sort_eq_ofFn_orderEmb]
  unfold List.flatMap flattenFinBlocks finBlocks
  rw [← List.ofFn_eq_map]
  have hmap : (List.ofFn (I.orderEmbOfFin rfl)).map (selectedBlockAt p I b) =
      List.ofFn (fun k : Fin I.card => b (Fin.cast
        (selectedList_length p I).symm k)) := by
    rw [← List.ofFn_comp']
    rw [List.ofFn_inj]
    funext k
    simp [selectedBlockAt, selectedIndex_orderEmb]
  rw [hmap]
  rw [List.ofFn_congr (selectedList_length p I).symm]
  congr 2

noncomputable def halfBlockAt (p : List ℝ) (i : Fin p.length) : List ℝ :=
  [p.get i / 2, p.get i / 2]

lemma flatMap_sort_halfBlockAt (p : List ℝ) (I : Finset (Fin p.length)) :
    (I.sort (· ≤ ·)).flatMap (halfBlockAt p) = bisectLengths (selectedList p I) := by
  unfold selectedList
  generalize I.sort (· ≤ ·) = idxs
  induction idxs with
  | nil => simp [bisectLengths, pairDup]
  | cons i tail ih =>
      simp [halfBlockAt, bisectLengths, pairDup, ih]

noncomputable def assembleSelectedBlocks (p : List ℝ)
    (I : Finset (Fin p.length))
    (b : Fin (selectedList p I).length → List ℝ) :
    Fin p.length → List ℝ := fun i =>
  if hi : i ∈ I then b (selectedIndex p I i hi)
  else [p.get i / 2, p.get i / 2]

lemma assembleSelectedBlocks_ne_nil (p : List ℝ)
    (I : Finset (Fin p.length))
    (b : Fin (selectedList p I).length → List ℝ)
    (hbne : ∀ k, b k ≠ []) :
    ∀ i, assembleSelectedBlocks p I b i ≠ [] := by
  intro i
  by_cases hi : i ∈ I
  · simpa [assembleSelectedBlocks, hi] using hbne (selectedIndex p I i hi)
  · simp [assembleSelectedBlocks, hi]

lemma assembleSelectedBlocks_pos (p : List ℝ)
    (I : Finset (Fin p.length))
    (b : Fin (selectedList p I).length → List ℝ)
    (hp : ∀ x ∈ p, 0 < x) (hbpos : ∀ k, ∀ x ∈ b k, 0 < x) :
    ∀ i, ∀ x ∈ assembleSelectedBlocks p I b i, 0 < x := by
  intro i x hx
  by_cases hi : i ∈ I
  · exact hbpos (selectedIndex p I i hi) x (by
      simpa [assembleSelectedBlocks, hi] using hx)
  · have hx' : x = p.get i / 2 := by
      simpa [assembleSelectedBlocks, hi] using hx
    subst x
    exact div_pos (hp (p.get i) (List.get_mem p i)) (by norm_num)

lemma assembleSelectedBlocks_sum (p : List ℝ)
    (I : Finset (Fin p.length))
    (b : Fin (selectedList p I).length → List ℝ)
    (hbsum : ∀ k, (b k).sum = (selectedList p I).get k) :
    ∀ i, (assembleSelectedBlocks p I b i).sum = p.get i := by
  intro i
  by_cases hi : i ∈ I
  · simp only [assembleSelectedBlocks, hi, dite_true]
    rw [hbsum, selectedList_get_selectedIndex]
  · simp [assembleSelectedBlocks, hi]

lemma cutsOfLengths_subset_assembleSelectedBlocks (p : List ℝ)
    (hpne : p ≠ []) (hp : ∀ x ∈ p, 0 < x) (hpsum : p.sum = 1)
    (I : Finset (Fin p.length))
    (b : Fin (selectedList p I).length → List ℝ)
    (hbne : ∀ k, b k ≠ []) (hbpos : ∀ k, ∀ x ∈ b k, 0 < x)
    (hbsum : ∀ k, (b k).sum = (selectedList p I).get k) :
    cutsOfLengths p ⊆
      cutsOfLengths (flattenFinBlocks (assembleSelectedBlocks p I b)) := by
  apply cutsOfLengths_subset_flattenFinBlocks p hpne hp hpsum
  · exact assembleSelectedBlocks_ne_nil p I b hbne
  · exact assembleSelectedBlocks_pos p I b hp hbpos
  · exact assembleSelectedBlocks_sum p I b hbsum

lemma flatten_assembleSelectedBlocks_pos (p : List ℝ)
    (hp : ∀ x ∈ p, 0 < x) (I : Finset (Fin p.length))
    (b : Fin (selectedList p I).length → List ℝ)
    (hbpos : ∀ k, ∀ x ∈ b k, 0 < x) :
    ∀ x ∈ flattenFinBlocks (assembleSelectedBlocks p I b), 0 < x := by
  exact flattenFinBlocks_pos _ (assembleSelectedBlocks_pos p I b hp hbpos)

lemma flatten_assembleSelectedBlocks_sum (p : List ℝ)
    (I : Finset (Fin p.length))
    (b : Fin (selectedList p I).length → List ℝ)
    (hbsum : ∀ k, (b k).sum = (selectedList p I).get k) :
    (flattenFinBlocks (assembleSelectedBlocks p I b)).sum = p.sum := by
  exact flattenFinBlocks_sum p _ (assembleSelectedBlocks_sum p I b hbsum)

noncomputable def assembleTwoSelectedBlocks (p : List ℝ)
    (I J : Finset (Fin p.length))
    (bI : Fin (selectedList p I).length → List ℝ)
    (bJ : Fin (selectedList p J).length → List ℝ) :
    Fin p.length → List ℝ := fun i =>
  if hi : i ∈ I then bI (selectedIndex p I i hi)
  else if hj : i ∈ J then bJ (selectedIndex p J i hj)
  else [p.get i / 2, p.get i / 2]

lemma assembleTwoSelectedBlocks_ne_nil (p : List ℝ)
    (I J : Finset (Fin p.length))
    (bI : Fin (selectedList p I).length → List ℝ)
    (bJ : Fin (selectedList p J).length → List ℝ)
    (hIne : ∀ k, bI k ≠ []) (hJne : ∀ k, bJ k ≠ []) :
    ∀ i, assembleTwoSelectedBlocks p I J bI bJ i ≠ [] := by
  intro i
  by_cases hi : i ∈ I
  · simpa [assembleTwoSelectedBlocks, hi] using hIne (selectedIndex p I i hi)
  · by_cases hj : i ∈ J
    · simpa [assembleTwoSelectedBlocks, hi, hj] using hJne (selectedIndex p J i hj)
    · simp [assembleTwoSelectedBlocks, hi, hj]

lemma assembleTwoSelectedBlocks_pos (p : List ℝ)
    (I J : Finset (Fin p.length))
    (bI : Fin (selectedList p I).length → List ℝ)
    (bJ : Fin (selectedList p J).length → List ℝ)
    (hp : ∀ x ∈ p, 0 < x)
    (hIpos : ∀ k, ∀ x ∈ bI k, 0 < x)
    (hJpos : ∀ k, ∀ x ∈ bJ k, 0 < x) :
    ∀ i, ∀ x ∈ assembleTwoSelectedBlocks p I J bI bJ i, 0 < x := by
  intro i x hx
  by_cases hi : i ∈ I
  · exact hIpos (selectedIndex p I i hi) x (by
      simpa [assembleTwoSelectedBlocks, hi] using hx)
  · by_cases hj : i ∈ J
    · exact hJpos (selectedIndex p J i hj) x (by
        simpa [assembleTwoSelectedBlocks, hi, hj] using hx)
    · have hx' : x = p.get i / 2 := by
        simpa [assembleTwoSelectedBlocks, hi, hj] using hx
      subst x
      exact div_pos (hp (p.get i) (List.get_mem p i)) (by norm_num)

lemma assembleTwoSelectedBlocks_sum (p : List ℝ)
    (I J : Finset (Fin p.length)) (_hIJ : Disjoint I J)
    (bI : Fin (selectedList p I).length → List ℝ)
    (bJ : Fin (selectedList p J).length → List ℝ)
    (hIsum : ∀ k, (bI k).sum = (selectedList p I).get k)
    (hJsum : ∀ k, (bJ k).sum = (selectedList p J).get k) :
    ∀ i, (assembleTwoSelectedBlocks p I J bI bJ i).sum = p.get i := by
  intro i
  by_cases hi : i ∈ I
  · simp only [assembleTwoSelectedBlocks, hi, dite_true]
    rw [hIsum, selectedList_get_selectedIndex]
  · by_cases hj : i ∈ J
    · simp only [assembleTwoSelectedBlocks, hi, dite_false, hj, dite_true]
      rw [hJsum, selectedList_get_selectedIndex]
    · simp [assembleTwoSelectedBlocks, hi, hj]

lemma cutsOfLengths_subset_assembleTwoSelectedBlocks (p : List ℝ)
    (hpne : p ≠ []) (hp : ∀ x ∈ p, 0 < x) (hpsum : p.sum = 1)
    (I J : Finset (Fin p.length)) (hIJ : Disjoint I J)
    (bI : Fin (selectedList p I).length → List ℝ)
    (bJ : Fin (selectedList p J).length → List ℝ)
    (hIne : ∀ k, bI k ≠ []) (hJne : ∀ k, bJ k ≠ [])
    (hIpos : ∀ k, ∀ x ∈ bI k, 0 < x)
    (hJpos : ∀ k, ∀ x ∈ bJ k, 0 < x)
    (hIsum : ∀ k, (bI k).sum = (selectedList p I).get k)
    (hJsum : ∀ k, (bJ k).sum = (selectedList p J).get k) :
    cutsOfLengths p ⊆ cutsOfLengths
      (flattenFinBlocks (assembleTwoSelectedBlocks p I J bI bJ)) := by
  apply cutsOfLengths_subset_flattenFinBlocks p hpne hp hpsum
  · exact assembleTwoSelectedBlocks_ne_nil p I J bI bJ hIne hJne
  · exact assembleTwoSelectedBlocks_pos p I J bI bJ hp hIpos hJpos
  · exact assembleTwoSelectedBlocks_sum p I J hIJ bI bJ hIsum hJsum


open scoped BigOperators List


theorem exists_equal_subset_common_blocks (p : List ℝ)
    (hp : ∀ x ∈ p, 0 < x) (I J : Finset (Fin p.length))
    (hsum : (selectedList p I).sum = (selectedList p J).sum) :
    ∃ c : List ℝ,
      (∀ z ∈ c, 0 < z) ∧
      c.length ≤ I.card + J.card - 1 ∧
      ∃ bI : Fin (selectedList p I).length → List ℝ,
        (∀ i, bI i ≠ []) ∧
        (∀ i, ∀ z ∈ bI i, 0 < z) ∧
        (∀ i, (bI i).sum = (selectedList p I).get i) ∧
        flattenFinBlocks bI = c ∧
      ∃ bJ : Fin (selectedList p J).length → List ℝ,
        (∀ j, bJ j ≠ []) ∧
        (∀ j, ∀ z ∈ bJ j, 0 < z) ∧
        (∀ j, (bJ j).sum = (selectedList p J).get j) ∧
        flattenFinBlocks bJ = c := by
  let x := selectedList p I
  let y := selectedList p J
  let c := commonAtoms x y
  have hxpos : ∀ z ∈ x, 0 < z := by
    dsimp [x]
    exact selectedList_pos p I hp
  have hypos : ∀ z ∈ y, 0 < z := by
    dsimp [y]
    exact selectedList_pos p J hp
  have hxy : x.sum = y.sum := by simpa [x, y] using hsum
  have hspec := commonAtoms_spec x y hxpos hypos hxy
  have href := commonAtoms_scanRefines x y hxpos hypos hxy
  have hxc : x.sum = c.sum := by
    dsimp [c]
    exact hspec.2.1.symm
  have hyc : y.sum = c.sum := by
    rw [← hxy]
    exact hxc
  obtain ⟨bI, hIne, hIpos, hIsum, hIflat⟩ :=
    exists_blocks_of_scanRefines x c hxpos hspec.1 hxc href.1
  obtain ⟨bJ, hJne, hJpos, hJsum, hJflat⟩ :=
    exists_blocks_of_scanRefines y c hypos hspec.1 hyc href.2
  refine ⟨c, hspec.1, ?_, bI, hIne, hIpos, hIsum, hIflat,
    bJ, hJne, hJpos, hJsum, hJflat⟩
  simpa [c, x, y, selectedList_length] using hspec.2.2


open scoped BigOperators List


theorem firstPlayerShare_pairDup_append_singleton (xs : List ℝ) (r : ℝ) :
    firstPlayerShare (pairDup xs ++ [r]) = xs.sum + r := by
  let H := xs.filter fun x => decide (r ≤ x)
  let L := xs.filter fun x => !(decide (r ≤ x))
  let hi := H.mergeSort (· ≥ ·)
  let lo := L.mergeSort (· ≥ ·)
  have hhiPerm : hi.Perm H := List.mergeSort_perm H (· ≥ ·)
  have hloPerm : lo.Perm L := List.mergeSort_perm L (· ≥ ·)
  have hpartition : (H ++ L).Perm xs := by
    simpa [H, L] using List.filter_append_perm (fun x : ℝ => decide (r ≤ x)) xs
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
    exact hhiloperm.flatMap fun a _ => List.Perm.refl [a, a]
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
    exact hsperm.flatMap fun a _ => List.Perm.refl [a, a]
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


open scoped BigOperators List


theorem exists_crossing_decomposition (xs : List ℝ)
    (hpos : ∀ x ∈ xs, 0 < x) (target : ℝ)
    (htarget : 0 < target) (hle : target ≤ xs.sum) :
    ∃ pre x post, xs = pre ++ x :: post ∧
      pre.sum < target ∧ target ≤ pre.sum + x := by
  induction xs generalizing target with
  | nil => simp at hle; linarith
  | cons x tail ih =>
      have hx : 0 < x := hpos x List.mem_cons_self
      have htail : ∀ z ∈ tail, 0 < z :=
        fun z hz => hpos z (List.mem_cons_of_mem _ hz)
      by_cases htx : target ≤ x
      · exact ⟨[], x, tail, by simp, by simpa using htarget, by simpa using htx⟩
      · have hxt : x < target := lt_of_not_ge htx
        have ht' : 0 < target - x := sub_pos.mpr hxt
        have hle' : target - x ≤ tail.sum := by
          simp only [List.sum_cons] at hle
          linarith
        obtain ⟨pre, y, post, htailEq, hpre, hcross⟩ :=
          ih htail (target - x) ht' hle'
        refine ⟨x :: pre, y, post, ?_, ?_, ?_⟩
        · simp [htailEq]
        · simp only [List.sum_cons]
          linarith
        · simp only [List.sum_cons]
          linarith

theorem exists_prefix_match_residual (xs : List ℝ)
    (hpos : ∀ x ∈ xs, 0 < x) (target : ℝ)
    (htarget : 0 < target) (hle : target ≤ xs.sum) :
    ∃ pre x post t rho,
      xs = pre ++ x :: post ∧
      0 < t ∧ 0 ≤ rho ∧ rho ≤ xs.sum - target ∧
      x = t + rho ∧ (pre ++ [t]).sum = target := by
  obtain ⟨pre, x, post, hxs, hpre, hcross⟩ :=
    exists_crossing_decomposition xs hpos target htarget hle
  let t := target - pre.sum
  let rho := pre.sum + x - target
  have ht : 0 < t := by dsimp [t]; linarith
  have hrho : 0 ≤ rho := by dsimp [rho]; linarith
  have hpost : 0 ≤ post.sum := List.sum_nonneg fun z hz =>
    (hpos z (by rw [hxs]; simp [hz])).le
  have hxsum : xs.sum = pre.sum + x + post.sum := by
    rw [hxs, List.sum_append, List.sum_cons]
    ring
  have hrhoBound : rho ≤ xs.sum - target := by
    dsimp [rho]
    linarith
  refine ⟨pre, x, post, t, rho, hxs, ht, hrho, hrhoBound, ?_, ?_⟩
  · dsimp [t, rho]
    ring
  · dsimp [t]
    rw [List.sum_append]
    simp only [List.sum_singleton]
    ring


open scoped BigOperators List


noncomputable def residualList (rho : ℝ) : List ℝ :=
  if rho = 0 then [] else [rho]

lemma residualList_sum (rho : ℝ) : (residualList rho).sum = rho := by
  by_cases h : rho = 0 <;> simp [residualList, h]

lemma residualList_length_le_one (rho : ℝ) : (residualList rho).length ≤ 1 := by
  by_cases h : rho = 0 <;> simp [residualList, h]

lemma residualList_pos {rho : ℝ} (hrho : 0 ≤ rho) :
    ∀ z ∈ residualList rho, 0 < z := by
  intro z hz
  by_cases h : rho = 0
  · simp [residualList, h] at hz
  · have : 0 < rho := lt_of_le_of_ne hrho (Ne.symm h)
    have hz' : z = rho := by simpa [residualList, h] using hz
    subst z
    exact this

lemma firstPlayerShare_pairDup_residualList (xs : List ℝ) (rho : ℝ) :
    firstPlayerShare (pairDup xs ++ residualList rho) = xs.sum + rho := by
  by_cases h : rho = 0
  · subst rho
    simpa [residualList] using firstPlayerShare_pairDup xs
  · simpa [residualList, h] using
      firstPlayerShare_pairDup_append_singleton xs rho

noncomputable def prefixRefinementBlocks (pre : List ℝ) (x : ℝ)
    (post : List ℝ) (t rho : ℝ)
    (bm : Fin (pre ++ [t]).length → List ℝ) :
    Fin (pre ++ x :: post).length → List ℝ := fun i =>
  if hpre : i.val < pre.length then
    bm ⟨i.val, by simp; omega⟩
  else if hcross : i.val = pre.length then
    bm ⟨pre.length, by simp⟩ ++ residualList rho
  else
    [((pre ++ x :: post).get i) / 2, ((pre ++ x :: post).get i) / 2]

lemma prefixRefinementBlocks_ne_nil (pre : List ℝ) (x : ℝ)
    (post : List ℝ) (t rho : ℝ)
    (bm : Fin (pre ++ [t]).length → List ℝ) (hbm : ∀ k, bm k ≠ []) :
    ∀ i, prefixRefinementBlocks pre x post t rho bm i ≠ [] := by
  intro i
  by_cases hpre : i.val < pre.length
  · simpa [prefixRefinementBlocks, hpre] using hbm ⟨i.val, by simp; omega⟩
  · by_cases hcross : i.val = pre.length
    · rw [prefixRefinementBlocks, dif_neg hpre, dif_pos hcross]
      exact List.append_ne_nil_of_left_ne_nil (hbm ⟨pre.length, by simp⟩)
        (residualList rho)
    · simp [prefixRefinementBlocks, hpre, hcross]

lemma prefixRefinementBlocks_pos (pre : List ℝ) (x : ℝ)
    (post : List ℝ) (t rho : ℝ)
    (bm : Fin (pre ++ [t]).length → List ℝ)
    (horig : ∀ z ∈ pre ++ x :: post, 0 < z)
    (hrho : 0 ≤ rho) (hbm : ∀ k, ∀ z ∈ bm k, 0 < z) :
    ∀ i, ∀ z ∈ prefixRefinementBlocks pre x post t rho bm i, 0 < z := by
  intro i z hz
  by_cases hpre : i.val < pre.length
  · exact hbm ⟨i.val, by simp; omega⟩ z (by
      simpa [prefixRefinementBlocks, hpre] using hz)
  · by_cases hcross : i.val = pre.length
    · rw [prefixRefinementBlocks, dif_neg hpre, dif_pos hcross] at hz
      rw [List.mem_append] at hz
      rcases hz with hz | hz
      · exact hbm ⟨pre.length, by simp⟩ z hz
      · exact residualList_pos hrho z hz
    · have hz' : z = (pre ++ x :: post).get i / 2 := by
        simpa [prefixRefinementBlocks, hpre, hcross] using hz
      subst z
      exact div_pos (horig _ (List.get_mem _ i)) (by norm_num)

lemma prefixRefinementBlocks_sum (pre : List ℝ) (x : ℝ)
    (post : List ℝ) (t rho : ℝ) (hx : x = t + rho)
    (bm : Fin (pre ++ [t]).length → List ℝ)
    (hbmsum : ∀ k, (bm k).sum = (pre ++ [t]).get k) :
    ∀ i, (prefixRefinementBlocks pre x post t rho bm i).sum =
      (pre ++ x :: post).get i := by
  intro i
  by_cases hpre : i.val < pre.length
  · simp only [prefixRefinementBlocks, hpre, dite_true]
    rw [hbmsum]
    rw [List.get_eq_getElem, List.get_eq_getElem,
      List.getElem_append_left hpre, List.getElem_append_left hpre]
  · by_cases hcross : i.val = pre.length
    · rw [prefixRefinementBlocks, dif_neg hpre, dif_pos hcross,
        List.sum_append, residualList_sum, hbmsum]
      have hiEq : i = ⟨pre.length, by simp⟩ := Fin.ext hcross
      subst i
      simp [List.get_eq_getElem, hx]
    · simp [prefixRefinementBlocks, hpre, hcross]


open scoped BigOperators List


def appendToLast {n : ℕ} (b : Fin (n + 1) → List ℝ) (extra : List ℝ) :
    Fin (n + 1) → List ℝ := fun i =>
  if i = Fin.last n then b i ++ extra else b i

lemma ofFn_appendToLast {n : ℕ} (b : Fin (n + 1) → List ℝ)
    (extra : List ℝ) :
    List.ofFn (appendToLast b extra) =
      (List.ofFn b).dropLast ++ [b (Fin.last n) ++ extra] := by
  rw [List.ofFn_succ', List.ofFn_succ']
  have hfront :
      List.ofFn (fun i : Fin n => appendToLast b extra (Fin.castSucc i)) =
        List.ofFn (fun i : Fin n => b (Fin.castSucc i)) := by
    rw [List.ofFn_inj]
    funext i
    simp [appendToLast]
  rw [hfront]
  simp [appendToLast]

noncomputable def prefixFlattenBlocks (pre : List ℝ) (x : ℝ)
    (post : List ℝ) (_t rho : ℝ)
    (bm : Fin (pre.length + 1) → List ℝ) :
    Fin (pre ++ x :: post).length → List ℝ := fun i =>
  let hlen : (pre ++ x :: post).length = (pre.length + 1) + post.length := by
    simp only [List.length_append, List.length_cons]
    omega
  let k : Fin ((pre.length + 1) + post.length) := Fin.cast hlen i
  Fin.append
    (appendToLast (n := pre.length) bm (residualList rho))
    (fun j : Fin post.length => [post.get j / 2, post.get j / 2]) k

lemma prefixRefinementBlocks_eq_prefixFlattenBlocks (pre : List ℝ) (x : ℝ)
    (post : List ℝ) (t rho : ℝ)
    (bm : Fin (pre.length + 1) → List ℝ) :
    prefixRefinementBlocks pre x post t rho
        (fun k => bm (Fin.cast (by simp) k)) =
      prefixFlattenBlocks pre x post t rho bm := by
  funext i
  by_cases hpre : i.val < pre.length
  · simp [prefixRefinementBlocks, prefixFlattenBlocks, appendToLast, hpre,
      Fin.append, Fin.addCases]
    split <;> rename_i houter
    · split <;> rename_i hlast
      · have hv := congrArg Fin.val hlast
        simp at hv
        omega
      · congr 2
    · omega
  · by_cases hcross : i.val = pre.length
    · simp [prefixRefinementBlocks, prefixFlattenBlocks, appendToLast,
        hcross, Fin.append, Fin.addCases]
      split <;> rename_i hlast
      · rw [hlast]
        have heq : (⟨pre.length, by omega⟩ : Fin (pre.length + 1)) =
            Fin.last pre.length := by apply Fin.ext; rfl
        rw [heq]
      · exfalso
        apply hlast
        apply Fin.ext
        simpa using hcross
    · simp [prefixRefinementBlocks, prefixFlattenBlocks, appendToLast, hpre,
        hcross, Fin.append, Fin.addCases]
      split <;> rename_i houter
      · omega
      · have hiPost : i.val - (pre.length + 1) < post.length := by
          have hi := i.isLt
          simp only [List.length_append, List.length_cons] at hi
          omega
        have hval : (pre ++ x :: post).get i =
            post.get ⟨i.val - (pre.length + 1), hiPost⟩ := by
          rw [List.get_eq_getElem, List.get_eq_getElem]
          rw [List.getElem_append_right (by omega)]
          have hidx : i.val - pre.length =
              (i.val - (pre.length + 1)) + 1 := by omega
          have hs := List.getElem_cons_succ x post
            (i.val - (pre.length + 1)) (by simp; omega)
          simpa only [hidx] using hs
        have hval' : (pre ++ x :: post)[i.val]'i.isLt =
            post[i.val - (pre.length + 1)]'hiPost := by
          simpa only [List.get_eq_getElem] using hval
        rw [hval']

lemma prefixFlattenBlocks_ne_nil (pre : List ℝ) (x : ℝ)
    (post : List ℝ) (t rho : ℝ)
    (bm : Fin (pre.length + 1) → List ℝ) (hbm : ∀ k, bm k ≠ []) :
    ∀ i, prefixFlattenBlocks pre x post t rho bm i ≠ [] := by
  rw [← prefixRefinementBlocks_eq_prefixFlattenBlocks]
  apply prefixRefinementBlocks_ne_nil
  intro k
  exact hbm (Fin.cast (by simp) k)

lemma prefixFlattenBlocks_pos (pre : List ℝ) (x : ℝ)
    (post : List ℝ) (t rho : ℝ)
    (bm : Fin (pre.length + 1) → List ℝ)
    (horig : ∀ z ∈ pre ++ x :: post, 0 < z)
    (hrho : 0 ≤ rho) (hbm : ∀ k, ∀ z ∈ bm k, 0 < z) :
    ∀ i, ∀ z ∈ prefixFlattenBlocks pre x post t rho bm i, 0 < z := by
  rw [← prefixRefinementBlocks_eq_prefixFlattenBlocks]
  apply prefixRefinementBlocks_pos pre x post t rho _ horig hrho
  intro k z hz
  exact hbm (Fin.cast (by simp) k) z hz

lemma prefixFlattenBlocks_sum (pre : List ℝ) (x : ℝ)
    (post : List ℝ) (t rho : ℝ) (hx : x = t + rho)
    (bm : Fin (pre.length + 1) → List ℝ)
    (hbmsum : ∀ k, (bm k).sum =
      (pre ++ [t]).get (Fin.cast (by simp) k)) :
    ∀ i, (prefixFlattenBlocks pre x post t rho bm i).sum =
      (pre ++ x :: post).get i := by
  rw [← prefixRefinementBlocks_eq_prefixFlattenBlocks]
  apply prefixRefinementBlocks_sum pre x post t rho hx
  intro k
  have h := hbmsum (Fin.cast (by simp) k)
  simpa using h

lemma finBlocks_prefixFlattenBlocks (pre : List ℝ) (x : ℝ)
    (post : List ℝ) (t rho : ℝ)
    (bm : Fin (pre.length + 1) → List ℝ) :
    finBlocks (prefixFlattenBlocks pre x post t rho bm) =
      List.ofFn (appendToLast (n := pre.length) bm (residualList rho)) ++
        List.ofFn (fun j : Fin post.length => [post.get j / 2, post.get j / 2]) := by
  unfold finBlocks
  rw [← List.ofFn_eq_map]
  let hlen : (pre ++ x :: post).length = (pre.length + 1) + post.length := by
    simp only [List.length_append, List.length_cons]
    omega
  rw [List.ofFn_congr hlen]
  change List.ofFn (Fin.append
      (appendToLast (n := pre.length) bm (residualList rho))
      (fun j : Fin post.length => [post.get j / 2, post.get j / 2])) = _
  exact List.ofFn_fin_append _ _

lemma flatten_ofFn_appendToLast {n : ℕ} (b : Fin (n + 1) → List ℝ)
    (extra : List ℝ) :
    (List.ofFn (appendToLast b extra)).flatten =
      (List.ofFn b).flatten ++ extra := by
  rw [ofFn_appendToLast, List.flatten_append, List.flatten_singleton]
  have hbne : List.ofFn b ≠ [] := by simp
  have hlast : (List.ofFn b).getLast hbne = b (Fin.last n) := by
    exact List.getLast_ofFn_succ b
  have hdecomp := List.dropLast_append_getLast hbne
  rw [hlast] at hdecomp
  calc
    (List.ofFn b).dropLast.flatten ++ (b (Fin.last n) ++ extra) =
        ((List.ofFn b).dropLast.flatten ++ b (Fin.last n)) ++ extra := by
      rw [List.append_assoc]
    _ = ((List.ofFn b).dropLast ++ [b (Fin.last n)]).flatten ++ extra := by
      simp
    _ = (List.ofFn b).flatten ++ extra := by rw [hdecomp]

lemma flatten_map_halfBlock (post : List ℝ) :
    (post.map (fun z : ℝ => [z / 2, z / 2])).flatten = bisectLengths post := by
  induction post with
  | nil => simp [bisectLengths, pairDup]
  | cons z zs ih => simp [bisectLengths, pairDup, ih]

lemma flattenFinBlocks_prefixFlattenBlocks (pre : List ℝ) (x : ℝ)
    (post : List ℝ) (t rho : ℝ)
    (bm : Fin (pre.length + 1) → List ℝ) :
    flattenFinBlocks (prefixFlattenBlocks pre x post t rho bm) =
      flattenFinBlocks bm ++ residualList rho ++ bisectLengths post := by
  unfold flattenFinBlocks
  rw [finBlocks_prefixFlattenBlocks, List.flatten_append,
    flatten_ofFn_appendToLast]
  rw [show finBlocks bm = List.ofFn bm by
    exact List.ofFn_eq_map.symm]
  rw [show (List.ofFn
      (fun j : Fin post.length => [post.get j / 2, post.get j / 2])).flatten =
      bisectLengths post by
    change (List.ofFn (fun j : Fin post.length =>
      (fun z : ℝ => [z / 2, z / 2]) (post.get j))).flatten = _
    have hof : List.ofFn (fun j : Fin post.length =>
        (fun z : ℝ => [z / 2, z / 2]) (post.get j)) =
        post.map (fun z : ℝ => [z / 2, z / 2]) := by
      calc
        _ = (List.ofFn post.get).map (fun z : ℝ => [z / 2, z / 2]) :=
          List.ofFn_comp' post.get (fun z : ℝ => [z / 2, z / 2])
        _ = _ := by rw [List.ofFn_get]
    rw [hof]
    exact flatten_map_halfBlock post]

lemma prefix_local_perm_pairs (c post : List ℝ) (rho : ℝ) :
    (c ++ residualList rho ++ bisectLengths post ++ c).Perm
      (pairDup (c ++ post.map fun z => z / 2) ++ residualList rho) := by
  let R := residualList rho
  let H := pairDup (post.map fun z => z / 2)
  have hbis : bisectLengths post = H := by rfl
  rw [hbis]
  have h₁ : (c ++ R ++ H ++ c).Perm (c ++ c ++ R ++ H) := by
    have hmove : ((R ++ H) ++ c).Perm (c ++ (R ++ H)) :=
      List.perm_append_comm
    simpa [List.append_assoc] using hmove.append_left c
  have h₂ : (c ++ c ++ R ++ H).Perm (c ++ c ++ H ++ R) := by
    simpa [List.append_assoc] using List.perm_append_comm.append_left (c ++ c)
  have h₃ : (c ++ c ++ H ++ R).Perm (pairDup c ++ H ++ R) := by
    simpa [List.append_assoc] using
      (pairDup_perm_append_self c).symm.append_right (H ++ R)
  have heq : pairDup c ++ H = pairDup (c ++ post.map fun z => z / 2) := by
    simp [H, pairDup, List.flatMap_append]
  exact (h₁.trans (h₂.trans h₃)).trans (by
    rw [← heq])

theorem firstPlayerShare_prefix_local (c post : List ℝ) (rho : ℝ) :
    firstPlayerShare (c ++ residualList rho ++ bisectLengths post ++ c) =
      c.sum + post.sum / 2 + rho := by
  rw [firstPlayerShare_congr (prefix_local_perm_pairs c post rho)]
  rw [firstPlayerShare_pairDup_residualList]
  rw [List.sum_append, sum_map_half]

lemma prefix_local_length (c post : List ℝ) (rho : ℝ) :
    (c ++ residualList rho ++ bisectLengths post ++ c).length =
      2 * c.length + (residualList rho).length + 2 * post.length := by
  simp only [List.length_append, bisectLengths_length]
  omega

lemma prefix_local_length_le (c post : List ℝ) (rho : ℝ)
    (p q : ℕ) (hpq : 0 < p + q) (hc : c.length ≤ p + q - 1) :
    (c ++ residualList rho ++ bisectLengths post ++ c).length ≤
      2 * (p + q + post.length) - 1 := by
  rw [prefix_local_length]
  have hr := residualList_length_le_one rho
  omega

lemma prefix_global_perm_pairs (c post outside : List ℝ) (rho : ℝ) :
    (c ++ residualList rho ++ bisectLengths post ++ c ++
        bisectLengths outside).Perm
      (pairDup (c ++ (post.map fun z => z / 2) ++
        (outside.map fun z => z / 2)) ++ residualList rho) := by
  let X := c ++ post.map fun z => z / 2
  let Y := outside.map fun z => z / 2
  have hlocal := (prefix_local_perm_pairs c post rho).append_right
    (bisectLengths outside)
  have hbis : bisectLengths outside = pairDup Y := by rfl
  have hswap : (pairDup X ++ residualList rho ++ pairDup Y).Perm
      (pairDup X ++ pairDup Y ++ residualList rho) := by
    simpa [List.append_assoc] using
      List.perm_append_comm.append_left (pairDup X)
  have heq : pairDup X ++ pairDup Y = pairDup (X ++ Y) := by
    simp [pairDup, List.flatMap_append]
  have hlocal' :
      (c ++ residualList rho ++ bisectLengths post ++ c ++
          bisectLengths outside).Perm
        (pairDup X ++ residualList rho ++ pairDup Y) := by
    simpa [X, Y, List.append_assoc, hbis] using hlocal
  have hfinal :
      (pairDup X ++ pairDup Y ++ residualList rho).Perm
        (pairDup (X ++ Y) ++ residualList rho) := by
    rw [← heq]
  exact hlocal'.trans (hswap.trans hfinal)

theorem firstPlayerShare_prefix_global (c post outside : List ℝ) (rho : ℝ) :
    firstPlayerShare (c ++ residualList rho ++ bisectLengths post ++ c ++
        bisectLengths outside) =
      c.sum + post.sum / 2 + outside.sum / 2 + rho := by
  rw [firstPlayerShare_congr (prefix_global_perm_pairs c post outside rho)]
  rw [firstPlayerShare_pairDup_residualList]
  rw [List.sum_append, List.sum_append, sum_map_half, sum_map_half]

lemma prefix_global_length (c post outside : List ℝ) (rho : ℝ) :
    (c ++ residualList rho ++ bisectLengths post ++ c ++
        bisectLengths outside).length =
      2 * c.length + (residualList rho).length +
        2 * post.length + 2 * outside.length := by
  simp only [List.length_append, bisectLengths_length]
  omega


open scoped BigOperators List


def outsideIndices (I J : Finset (Fin m)) : Finset (Fin m) :=
  Finset.univ \ (I ∪ J)

noncomputable def groupedIndices (I J : Finset (Fin m)) : List (Fin m) :=
  I.sort (· ≤ ·) ++ J.sort (· ≤ ·) ++ (outsideIndices I J).sort (· ≤ ·)

lemma groupedIndices_nodup {I J : Finset (Fin m)} (hIJ : Disjoint I J) :
    (groupedIndices I J).Nodup := by
  have hI := Finset.sort_nodup I (· ≤ ·)
  have hJ := Finset.sort_nodup J (· ≤ ·)
  have hK := Finset.sort_nodup (outsideIndices I J) (· ≤ ·)
  unfold groupedIndices
  rw [List.append_assoc]
  apply hI.append (hJ.append hK ?_) ?_
  · rw [List.disjoint_left]
    intro x hxJ hxK
    have hxJ' : x ∈ J := (Finset.mem_sort (· ≤ ·)).mp hxJ
    have hxK' : x ∈ outsideIndices I J :=
      (Finset.mem_sort (· ≤ ·)).mp hxK
    exact (Finset.mem_sdiff.mp hxK').2 (Finset.mem_union_right I hxJ')
  · rw [List.disjoint_left]
    intro x hxI hxRest
    have hxI' : x ∈ I := (Finset.mem_sort (· ≤ ·)).mp hxI
    rcases List.mem_append.mp hxRest with hxJ | hxK
    · exact (Finset.disjoint_left.mp hIJ hxI'
        ((Finset.mem_sort (· ≤ ·)).mp hxJ))
    · have hxK' : x ∈ outsideIndices I J :=
        (Finset.mem_sort (· ≤ ·)).mp hxK
      exact (Finset.mem_sdiff.mp hxK').2 (Finset.mem_union_left J hxI')

lemma groupedIndices_length (I J : Finset (Fin m)) (hIJ : Disjoint I J) :
    (groupedIndices I J).length = m := by
  have hnd := groupedIndices_nodup hIJ
  calc
    (groupedIndices I J).length = (groupedIndices I J).toFinset.card :=
      (List.toFinset_card_of_nodup hnd).symm
    _ = m := by
      have heq : I ∪ (J ∪ outsideIndices I J) = Finset.univ := by
        ext i
        simp [outsideIndices]
        tauto
      simp [groupedIndices, heq]

lemma groupedIndices_perm_finRange (I J : Finset (Fin m))
    (hIJ : Disjoint I J) :
    (groupedIndices I J).Perm (List.finRange m) := by
  have hsub : (groupedIndices I J) <+~ List.finRange m := by
    apply List.subperm_of_subset (groupedIndices_nodup hIJ)
    intro i hi
    simp
  exact subperm_perm_of_length_eq hsub (by
    rw [groupedIndices_length I J hIJ, List.length_finRange])

theorem flatten_assembleTwoSelectedBlocks_perm (p : List ℝ)
    (I J : Finset (Fin p.length)) (hIJ : Disjoint I J)
    (bI : Fin (selectedList p I).length → List ℝ)
    (bJ : Fin (selectedList p J).length → List ℝ) :
    (flattenFinBlocks (assembleTwoSelectedBlocks p I J bI bJ)).Perm
      (flattenFinBlocks bI ++ flattenFinBlocks bJ ++
        bisectLengths (selectedList p (outsideIndices I J))) := by
  let b := assembleTwoSelectedBlocks p I J bI bJ
  let K := outsideIndices I J
  have hI : (I.sort (· ≤ ·)).flatMap b = flattenFinBlocks bI := by
    rw [← flatMap_sort_selectedBlockAt p I bI]
    apply List.flatMap_congr
    intro i hi
    have hii : i ∈ I := (Finset.mem_sort (· ≤ ·)).mp hi
    simp [b, assembleTwoSelectedBlocks, selectedBlockAt, hii]
  have hJ : (J.sort (· ≤ ·)).flatMap b = flattenFinBlocks bJ := by
    rw [← flatMap_sort_selectedBlockAt p J bJ]
    apply List.flatMap_congr
    intro i hi
    have hij : i ∈ J := (Finset.mem_sort (· ≤ ·)).mp hi
    have hni : i ∉ I := fun hii => Finset.disjoint_left.mp hIJ hii hij
    simp [b, assembleTwoSelectedBlocks, selectedBlockAt, hij, hni]
  have hK : (K.sort (· ≤ ·)).flatMap b =
      bisectLengths (selectedList p K) := by
    rw [← flatMap_sort_halfBlockAt p K]
    apply List.flatMap_congr
    intro i hi
    have hik : i ∈ K := (Finset.mem_sort (· ≤ ·)).mp hi
    have hik' : i ∈ Finset.univ \ (I ∪ J) := by
      simpa [K, outsideIndices] using hik
    have hni : i ∉ I := fun hii =>
      (Finset.mem_sdiff.mp hik').2 (Finset.mem_union_left J hii)
    have hnj : i ∉ J := fun hij =>
      (Finset.mem_sdiff.mp hik').2 (Finset.mem_union_right I hij)
    simp [b, assembleTwoSelectedBlocks, halfBlockAt, hni, hnj]
  have hidx := groupedIndices_perm_finRange I J hIJ
  have hflat := hidx.flatMap (f := b) (g := b)
    (fun _ _ => List.Perm.refl _)
  unfold groupedIndices at hflat
  simp only [List.flatMap_append] at hflat
  rw [hI, hJ, hK] at hflat
  change ((List.finRange p.length).flatMap b).Perm _
  simpa [b, K] using hflat.symm


open scoped BigOperators List


lemma flattenFinBlocks_cast {m n : ℕ} (h : m = n)
    (b : Fin n → List ℝ) :
    flattenFinBlocks (fun i : Fin m => b (Fin.cast h i)) =
      flattenFinBlocks b := by
  subst n
  simp

structure PositivePrefixData (xs ys : List ℝ) where
  c : List ℝ
  post : List ℝ
  rho : ℝ
  bX : Fin xs.length → List ℝ
  bY : Fin ys.length → List ℝ
  rho_nonneg : 0 ≤ rho
  rho_le : rho ≤ xs.sum - ys.sum
  sum_relation : xs.sum = ys.sum + rho + post.sum
  c_pos : ∀ z ∈ c, 0 < z
  c_sum : c.sum = ys.sum
  bX_ne : ∀ i, bX i ≠ []
  bX_pos : ∀ i, ∀ z ∈ bX i, 0 < z
  bX_sum : ∀ i, (bX i).sum = xs.get i
  bY_ne : ∀ j, bY j ≠ []
  bY_pos : ∀ j, ∀ z ∈ bY j, 0 < z
  bY_sum : ∀ j, (bY j).sum = ys.get j
  flatten_bX : flattenFinBlocks bX =
    c ++ residualList rho ++ bisectLengths post
  flatten_bY : flattenFinBlocks bY = c
  local_length :
    (c ++ residualList rho ++ bisectLengths post ++ c).length ≤
      2 * (xs.length + ys.length) - 1

theorem exists_positive_prefix_data (xs ys : List ℝ)
    (hxpos : ∀ x ∈ xs, 0 < x) (hypos : ∀ y ∈ ys, 0 < y)
    (hysum : 0 < ys.sum) (hle : ys.sum ≤ xs.sum) :
    Nonempty (PositivePrefixData xs ys) := by
  obtain ⟨pre, x, post, t, rho, hxs, ht, hrho, hrhoBound,
      hx, hmatch⟩ :=
    exists_prefix_match_residual xs hxpos ys.sum hysum hle
  subst xs
  let matched := pre ++ [t]
  let c := commonAtoms matched ys
  have hmatchedPos : ∀ z ∈ matched, 0 < z := by
    intro z hz
    rcases List.mem_append.mp hz with hz | hz
    · exact hxpos z (by simp [hz])
    · have hz' : z = t := by simpa using hz
      simpa [hz'] using ht
  have hmatchedSum : matched.sum = ys.sum := by
    simpa [matched] using hmatch
  have hspec := commonAtoms_spec matched ys hmatchedPos hypos hmatchedSum
  have href := commonAtoms_scanRefines matched ys hmatchedPos hypos hmatchedSum
  have hmatchedC : matched.sum = c.sum := by
    dsimp [c]
    exact hspec.2.1.symm
  have hysC : ys.sum = c.sum := by
    rw [← hmatchedSum]
    exact hmatchedC
  obtain ⟨bm, hbmNe, hbmPos, hbmSum, hbmFlat⟩ :=
    exists_blocks_of_scanRefines matched c hmatchedPos hspec.1 hmatchedC href.1
  obtain ⟨bY, hbYNe, hbYPos, hbYSum, hbYFlat⟩ :=
    exists_blocks_of_scanRefines ys c hypos hspec.1 hysC href.2
  let bm' : Fin (pre.length + 1) → List ℝ := fun i =>
    bm (Fin.cast (by simp [matched]) i)
  have hbm'Ne : ∀ i, bm' i ≠ [] := by
    intro i
    exact hbmNe (Fin.cast (by simp [matched]) i)
  have hbm'Pos : ∀ i, ∀ z ∈ bm' i, 0 < z := by
    intro i z hz
    exact hbmPos (Fin.cast (by simp [matched]) i) z hz
  have hbm'Sum : ∀ i, (bm' i).sum =
      (pre ++ [t]).get (Fin.cast (by simp) i) := by
    intro i
    simpa [bm', matched] using hbmSum (Fin.cast (by simp [matched]) i)
  have hbm'Flat : flattenFinBlocks bm' = c := by
    calc
      flattenFinBlocks bm' = flattenFinBlocks bm := by
        exact flattenFinBlocks_cast (by simp [matched]) bm
      _ = c := hbmFlat
  let bX := prefixFlattenBlocks pre x post t rho bm'
  have hbXNe : ∀ i, bX i ≠ [] := by
    exact prefixFlattenBlocks_ne_nil pre x post t rho bm' hbm'Ne
  have hbXPos : ∀ i, ∀ z ∈ bX i, 0 < z := by
    apply prefixFlattenBlocks_pos pre x post t rho bm' hxpos hrho hbm'Pos
  have hbXSum : ∀ i, (bX i).sum = (pre ++ x :: post).get i := by
    exact prefixFlattenBlocks_sum pre x post t rho hx bm' hbm'Sum
  have hbXFlat : flattenFinBlocks bX =
      c ++ residualList rho ++ bisectLengths post := by
    rw [show flattenFinBlocks bX =
        flattenFinBlocks bm' ++ residualList rho ++ bisectLengths post by
      exact flattenFinBlocks_prefixFlattenBlocks pre x post t rho bm']
    rw [hbm'Flat]
  have hsumRelation : (pre ++ x :: post).sum =
      ys.sum + rho + post.sum := by
    have hm : pre.sum + t = ys.sum := by
      simpa [matched, List.sum_append] using hmatchedSum
    simp only [List.sum_append, List.sum_cons]
    linarith
  have hcLen : c.length ≤ matched.length + ys.length - 1 := by
    simpa [c, matched] using hspec.2.2
  have hlocalLen :
      (c ++ residualList rho ++ bisectLengths post ++ c).length ≤
        2 * ((pre ++ x :: post).length + ys.length) - 1 := by
    have hrlen := residualList_length_le_one rho
    have hmatchedLen : matched.length = pre.length + 1 := by
      simp [matched]
    rw [prefix_local_length]
    simp only [List.length_append, List.length_cons] at ⊢
    omega
  exact ⟨{
    c := c
    post := post
    rho := rho
    bX := bX
    bY := bY
    rho_nonneg := hrho
    rho_le := hrhoBound
    sum_relation := hsumRelation
    c_pos := hspec.1
    c_sum := hspec.2.1.trans hmatchedSum
    bX_ne := hbXNe
    bX_pos := hbXPos
    bX_sum := hbXSum
    bY_ne := hbYNe
    bY_pos := hbYPos
    bY_sum := hbYSum
    flatten_bX := hbXFlat
    flatten_bY := hbYFlat
    local_length := hlocalLen
  }⟩


open scoped BigOperators List


theorem selected_partition_sum (p : List ℝ)
    (I J : Finset (Fin p.length)) (hIJ : Disjoint I J) :
    (selectedList p I).sum + (selectedList p J).sum +
        (selectedList p (outsideIndices I J)).sum = p.sum := by
  have hperm := (groupedIndices_perm_finRange I J hIJ).map p.get
  have hsum := hperm.sum_eq
  unfold groupedIndices at hsum
  simp only [List.map_append, List.sum_append] at hsum
  simpa [selectedList] using hsum

theorem selected_partition_length (p : List ℝ)
    (I J : Finset (Fin p.length)) (hIJ : Disjoint I J) :
    (selectedList p I).length + (selectedList p J).length +
        (selectedList p (outsideIndices I J)).length = p.length := by
  have hlen := (groupedIndices_perm_finRange I J hIJ).length_eq
  unfold groupedIndices at hlen
  simpa [selectedList_length, Finset.length_sort, Nat.add_assoc] using hlen

theorem exists_positive_close_refinement (p : List ℝ)
    (hpne : p ≠ []) (hppos : ∀ x ∈ p, 0 < x) (hpsum : p.sum = 1)
    (I J : Finset (Fin p.length)) (hIJ : Disjoint I J)
    (hJsum : 0 < (selectedList p J).sum)
    (hdiff0 : 0 ≤ (selectedList p I).sum - (selectedList p J).sum)
    {delta : ℝ}
    (hdiff : (selectedList p I).sum - (selectedList p J).sum ≤ delta) :
    ∃ l : List ℝ,
      l ≠ [] ∧
      (∀ z ∈ l, 0 < z) ∧
      l.sum = 1 ∧
      cutsOfLengths p ⊆ cutsOfLengths l ∧
      l.length ≤ 2 * p.length - 1 ∧
      firstPlayerShare l ≤ (1 + delta) / 2 := by
  let xs := selectedList p I
  let ys := selectedList p J
  let outside := selectedList p (outsideIndices I J)
  have hxpos : ∀ x ∈ xs, 0 < x := selectedList_pos p I hppos
  have hypos : ∀ y ∈ ys, 0 < y := selectedList_pos p J hppos
  have hyle : ys.sum ≤ xs.sum := by
    dsimp [xs, ys]
    linarith
  obtain ⟨d⟩ := exists_positive_prefix_data xs ys hxpos hypos
    (by simpa [ys] using hJsum) hyle
  let b := assembleTwoSelectedBlocks p I J d.bX d.bY
  let l := flattenFinBlocks b
  have hbne : ∀ i, b i ≠ [] :=
    assembleTwoSelectedBlocks_ne_nil p I J d.bX d.bY d.bX_ne d.bY_ne
  have hbpos : ∀ i, ∀ z ∈ b i, 0 < z :=
    assembleTwoSelectedBlocks_pos p I J d.bX d.bY hppos d.bX_pos d.bY_pos
  have hbsum : ∀ i, (b i).sum = p.get i :=
    assembleTwoSelectedBlocks_sum p I J hIJ d.bX d.bY d.bX_sum d.bY_sum
  have hm : 0 < p.length := by
    cases p with
    | nil => contradiction
    | cons => simp
  have hlne : l ≠ [] := flattenFinBlocks_ne_nil b hm hbne
  have hlpos : ∀ z ∈ l, 0 < z := flattenFinBlocks_pos b hbpos
  have hlsum : l.sum = 1 := by
    rw [show l.sum = p.sum by exact flattenFinBlocks_sum p b hbsum]
    exact hpsum
  have hlcuts : cutsOfLengths p ⊆ cutsOfLengths l := by
    exact cutsOfLengths_subset_assembleTwoSelectedBlocks p hpne hppos hpsum
      I J hIJ d.bX d.bY d.bX_ne d.bY_ne d.bX_pos d.bY_pos
      d.bX_sum d.bY_sum
  have hperm := flatten_assembleTwoSelectedBlocks_perm p I J hIJ d.bX d.bY
  have hcanon : l.Perm
      (d.c ++ residualList d.rho ++ bisectLengths d.post ++ d.c ++
        bisectLengths outside) := by
    rw [d.flatten_bX, d.flatten_bY] at hperm
    simpa [l, b, outside, List.append_assoc] using hperm
  have hpartSum : xs.sum + ys.sum + outside.sum = 1 := by
    have h := selected_partition_sum p I J hIJ
    rw [hpsum] at h
    simpa [xs, ys, outside] using h
  have hshareEq : firstPlayerShare l = (1 + d.rho) / 2 := by
    rw [firstPlayerShare_congr hcanon]
    rw [firstPlayerShare_prefix_global]
    have hc := d.c_sum
    have hr := d.sum_relation
    linarith
  have hrhoDelta : d.rho ≤ delta := by
    have hr := d.rho_le
    dsimp [xs, ys] at hr
    exact hr.trans hdiff
  have hshare : firstPlayerShare l ≤ (1 + delta) / 2 := by
    rw [hshareEq]
    linarith
  have hpartLen : xs.length + ys.length + outside.length = p.length := by
    simpa [xs, ys, outside] using selected_partition_length p I J hIJ
  have hysLen : 0 < ys.length := by
    have hysPos : 0 < ys.sum := by simpa [ys] using hJsum
    apply List.length_pos_iff.mpr
    intro hnil
    rw [hnil] at hysPos
    norm_num at hysPos
  have hlen : l.length ≤ 2 * p.length - 1 := by
    calc
      l.length =
          (d.c ++ residualList d.rho ++ bisectLengths d.post ++ d.c ++
            bisectLengths outside).length := hcanon.length_eq
      _ = (d.c ++ residualList d.rho ++ bisectLengths d.post ++ d.c).length +
          (bisectLengths outside).length := by
            simp only [List.length_append]
      _ ≤ (2 * (xs.length + ys.length) - 1) + 2 * outside.length := by
            exact Nat.add_le_add d.local_length (by rw [bisectLengths_length])
      _ = 2 * p.length - 1 := by omega
  exact ⟨l, hlne, hlpos, hlsum, hlcuts, hlen, hshare⟩


open scoped BigOperators List


lemma flattenFinBlocks_singletons (xs : List ℝ) :
    flattenFinBlocks (fun i : Fin xs.length => [xs.get i]) = xs := by
  unfold flattenFinBlocks finBlocks
  rw [← List.ofFn_eq_map]
  rw [show List.ofFn (fun i : Fin xs.length => [xs.get i]) =
      xs.map (fun x => [x]) by
    calc
      List.ofFn (fun i : Fin xs.length => [xs.get i]) =
          (List.ofFn xs.get).map (fun x => [x]) :=
        List.ofFn_comp' xs.get (fun x => [x])
      _ = xs.map (fun x => [x]) := by rw [List.ofFn_get]]
  induction xs with
  | nil => simp
  | cons x tail ih => simp [ih]

theorem exists_singleton_close_refinement (p : List ℝ)
    (hpne : p ≠ []) (hppos : ∀ x ∈ p, 0 < x) (hpsum : p.sum = 1)
    (i : Fin p.length) {delta : ℝ} (hiDelta : p.get i ≤ delta) :
    ∃ l : List ℝ,
      l ≠ [] ∧
      (∀ z ∈ l, 0 < z) ∧
      l.sum = 1 ∧
      cutsOfLengths p ⊆ cutsOfLengths l ∧
      l.length = 2 * p.length - 1 ∧
      firstPlayerShare l ≤ (1 + delta) / 2 := by
  let I : Finset (Fin p.length) := {i}
  let J : Finset (Fin p.length) := ∅
  let xs := selectedList p I
  let ys := selectedList p J
  let outside := selectedList p (outsideIndices I J)
  have hIJ : Disjoint I J := Finset.disjoint_empty_right I
  have hxs : xs = [p.get i] := by
    simp [xs, I, selectedList]
  have hys : ys = [] := by
    simp [ys, J, selectedList]
  let bI : Fin xs.length → List ℝ := fun k => [xs.get k]
  let bJ : Fin ys.length → List ℝ := fun k =>
    Fin.elim0 (Fin.cast (congrArg List.length hys) k)
  have hbINe : ∀ k, bI k ≠ [] := by simp [bI]
  have hbIPos : ∀ k, ∀ z ∈ bI k, 0 < z := by
    intro k z hz
    have hz' : z = xs.get k := by simpa [bI] using hz
    subst z
    exact selectedList_pos p I hppos _ (List.get_mem xs k)
  have hbISum : ∀ k, (bI k).sum = xs.get k := by simp [bI]
  have hbJNe : ∀ k, bJ k ≠ [] := by
    intro k
    exact Fin.elim0 (Fin.cast (congrArg List.length hys) k)
  have hbJPos : ∀ k, ∀ z ∈ bJ k, 0 < z := by
    intro k
    exact Fin.elim0 (Fin.cast (congrArg List.length hys) k)
  have hbJSum : ∀ k, (bJ k).sum = ys.get k := by
    intro k
    exact Fin.elim0 (Fin.cast (congrArg List.length hys) k)
  let b := assembleTwoSelectedBlocks p I J bI bJ
  let l := flattenFinBlocks b
  have hbne : ∀ k, b k ≠ [] :=
    assembleTwoSelectedBlocks_ne_nil p I J bI bJ hbINe hbJNe
  have hbpos : ∀ k, ∀ z ∈ b k, 0 < z :=
    assembleTwoSelectedBlocks_pos p I J bI bJ hppos hbIPos hbJPos
  have hbsum : ∀ k, (b k).sum = p.get k :=
    assembleTwoSelectedBlocks_sum p I J hIJ bI bJ hbISum hbJSum
  have hm : 0 < p.length := List.length_pos_iff.mpr hpne
  have hlne : l ≠ [] := flattenFinBlocks_ne_nil b hm hbne
  have hlpos : ∀ z ∈ l, 0 < z := flattenFinBlocks_pos b hbpos
  have hlsum : l.sum = 1 := by
    rw [show l.sum = p.sum by exact flattenFinBlocks_sum p b hbsum]
    exact hpsum
  have hlcuts : cutsOfLengths p ⊆ cutsOfLengths l := by
    exact cutsOfLengths_subset_assembleTwoSelectedBlocks p hpne hppos hpsum
      I J hIJ bI bJ hbINe hbJNe hbIPos hbJPos hbISum hbJSum
  have hbIFlat : flattenFinBlocks bI = [p.get i] := by
    rw [flattenFinBlocks_singletons xs, hxs]
  have hbJFlat : flattenFinBlocks bJ = [] := by
    unfold flattenFinBlocks finBlocks
    have hlen : ys.length = 0 := congrArg List.length hys
    have hrange : List.finRange ys.length = [] := by
      apply List.eq_nil_of_length_eq_zero
      simp [hlen]
    rw [hrange]
    simp
  have hperm := flatten_assembleTwoSelectedBlocks_perm p I J hIJ bI bJ
  rw [hbIFlat, hbJFlat] at hperm
  have hcanon : l.Perm (bisectLengths outside ++ [p.get i]) := by
    have hswap : ([p.get i] ++ bisectLengths outside).Perm
        (bisectLengths outside ++ [p.get i]) := List.perm_append_comm
    have hperm' : l.Perm ([p.get i] ++ bisectLengths outside) := by
      simpa [l, b, outside] using hperm
    exact hperm'.trans hswap
  have hpartSum : p.get i + outside.sum = 1 := by
    have h := selected_partition_sum p I J hIJ
    rw [hpsum] at h
    simpa [xs, ys, outside, hxs, hys] using h
  have hshareEq : firstPlayerShare l = (1 + p.get i) / 2 := by
    rw [firstPlayerShare_congr hcanon]
    rw [show bisectLengths outside =
        pairDup (outside.map fun x => x / 2) by rfl]
    rw [firstPlayerShare_pairDup_append_singleton, sum_map_half]
    linarith
  have hshare : firstPlayerShare l ≤ (1 + delta) / 2 := by
    rw [hshareEq]
    linarith
  have hpartLen : 1 + outside.length = p.length := by
    have h := selected_partition_length p I J hIJ
    simpa [xs, ys, outside, hxs, hys] using h
  have hlen : l.length = 2 * p.length - 1 := by
    rw [hcanon.length_eq, List.length_append, bisectLengths_length]
    simp only [List.length_singleton]
    omega
  exact ⟨l, hlne, hlpos, hlsum, hlcuts, hlen, hshare⟩


open scoped BigOperators List


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
  have hnonneg : ∀ i : Fin p.length, 0 ≤ p.get i := fun i =>
    (hppos (p.get i) (List.get_mem p i)).le
  have hsumFin : ∑ i : Fin p.length, p.get i = 1 := by
    have hbridge : (∑ i : Fin p.length, p.get i) =
        ((List.finRange p.length).map p.get).sum := by
      symm
      simp
    rw [hbridge, List.map_get_finRange, hpsum]
  obtain ⟨I, J, hIJ, hnonempty, hdiff0, hdiff⟩ :=
    CodexClosePoints.exists_disjoint_subset_sums_close
      p.length hm p.get hnonneg hsumFin
  have hdiff0' :
      0 ≤ (selectedList p I).sum - (selectedList p J).sum := by
    simpa only [selectedList_sum] using hdiff0
  have hdiff' :
      (selectedList p I).sum - (selectedList p J).sum ≤
        1 / ((2 : ℝ) ^ p.length - 1) := by
    simpa only [selectedList_sum] using hdiff
  by_cases hJpos : 0 < (selectedList p J).sum
  · exact exists_positive_close_refinement p hpne hppos hpsum I J hIJ
      hJpos hdiff0' hdiff'
  · have hJnonneg : 0 ≤ (selectedList p J).sum :=
      List.sum_nonneg fun z hz =>
        (selectedList_pos p J hppos z hz).le
    have hJzero : (selectedList p J).sum = 0 := by linarith
    have hJempty : J = ∅ := by
      rw [← Finset.not_nonempty_iff_eq_empty]
      rintro ⟨j, hj⟩
      have hjle : p.get j ≤ ∑ k ∈ J, p.get k :=
        Finset.single_le_sum (fun k _ => hnonneg k) hj
      rw [← selectedList_sum] at hjle
      have hjpos := hppos (p.get j) (List.get_mem p j)
      linarith
    have hInonempty : I.Nonempty := by
      rw [hJempty] at hnonempty
      simpa using hnonempty
    obtain ⟨i, hi⟩ := hInonempty
    have hipiece : p.get i ≤ (selectedList p I).sum := by
      rw [selectedList_sum]
      exact Finset.single_le_sum (fun k _ => hnonneg k) hi
    have hiDelta : p.get i ≤ 1 / ((2 : ℝ) ^ p.length - 1) := by
      linarith
    obtain ⟨l, hlne, hlpos, hlsum, hlcuts, hllen, hlshare⟩ :=
      exists_singleton_close_refinement p hpne hppos hpsum i hiDelta
    exact ⟨l, hlne, hlpos, hlsum, hlcuts, hllen.le, hlshare⟩


open scoped BigOperators List


lemma upper_denom_pos (n : ℕ) :
    0 < (2 : ℝ) ^ (n + 1) - 1 := by
  have hpow : (1 : ℝ) < 2 ^ (n + 1) :=
    one_lt_pow₀ (by norm_num) (by omega)
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
    rw [show p.length = A.card + 1 by exact pieceLengths_length A, hcard]
  have hreplyLen : l.length ≤ A.card + n + 1 := by
    rw [hplen] at hllen
    omega
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
    have hcard : A.card = n := by omega
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

snip end

/-! ## Main Statements -/

/-- **Main statement.** For every positive integer `n`, Liu Bang's guaranteed
value equals `2^n / (2^(n+1) - 1)`. -/
problem V_eq (n : ℕ) (hn : 0 < n) : V n = answer n := by
  obtain ⟨A₀, hA₀adm, hA₀⟩ := lower_bound_aux n hn
  have hub := upper_bound_aux n hn
  have hemptyA : AdmissibleMark n ∅ := by
    constructor
    · simp
    · simp
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

/-- **Lower bound.** Liu Bang has an admissible marking `A` such that for every
admissible marking `B` disjoint from `A`, his guaranteed share is at least
`2^n / (2^(n+1) - 1)`. -/
problem lower_bound (n : ℕ) (hn : 0 < n) :
    ∃ A : Finset ℝ, AdmissibleMark n A ∧
      ∀ B : Finset ℝ, AdmissibleMark n B → Disjoint A B →
        (2 : ℝ) ^ n / ((2 : ℝ) ^ (n + 1) - 1) ≤ L A B := by
  exact lower_bound_aux n hn

/-- **Upper bound / optimality.** For every admissible marking `A` of Liu Bang,
Xiang Yu has an admissible marking `B` disjoint from `A` with
`L A B ≤ 2^n / (2^(n+1) - 1)`, so Liu Bang cannot guarantee more. -/
problem upper_bound (n : ℕ) (hn : 0 < n) :
    ∀ A : Finset ℝ, AdmissibleMark n A →
      ∃ B : Finset ℝ, AdmissibleMark n B ∧ Disjoint A B ∧
        L A B ≤ (2 : ℝ) ^ n / ((2 : ℝ) ^ (n + 1) - 1) := by
  exact upper_bound_aux n hn

end Imo2026P3
