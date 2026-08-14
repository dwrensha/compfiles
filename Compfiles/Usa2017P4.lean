/-
Copyright (c) 2026 Kimi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Card
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics] }

/-!
# USA Mathematical Olympiad 2017, Problem 4

Let P₁, P₂, ..., P_{2n} be 2n distinct points on the unit circle x² + y² = 1, other than
(1, 0). Each point is colored either red or blue, with exactly n red points and n blue
points. Let R₁, R₂, ..., Rₙ be any ordering of the red points. Let B₁ be the nearest
blue point to R₁ traveling counterclockwise around the circle starting from R₁. Then let
B₂ be the nearest of the remaining blue points to R₂ traveling counterclockwise around
the circle from R₂, and so on, until we have labeled all of the blue points B₁, ..., Bₙ.
Show that the number of counterclockwise arcs of the form Rᵢ → Bᵢ that contain the point
(1, 0) is independent of the way we chose the ordering R₁, ..., Rₙ of the red points.
-/

namespace Usa2017P4

/-!
## Combinatorial setup

We cut the circle at (1, 0) and record the 2n points in counterclockwise order,
starting right after (1, 0), as the elements of `Fin (2 * n)`. The coloring is given
by `c : Fin (2 * n) → Bool` with `true` for red and `false` for blue. Traveling
counterclockwise from a point `r` one meets the positions `r + 1, r + 2, ...`
cyclically; the counterclockwise arc from `r` to `b` contains (1, 0) exactly when
`b.val < r.val`. The greedy labeling process is modeled by `wraps`, which counts the
arcs through (1, 0) produced when the red points are processed in a given order.
-/

section Geometry

variable {m : ℕ}

/-- Shift `p` forward (counterclockwise) by `d` positions, cyclically. -/
def shift (p : Fin m) (d : ℕ) : Fin m :=
  ⟨(p.val + d) % m, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) p.isLt)⟩

/-- The cyclic (counterclockwise) distance from `a` to `b`; it is `0` iff `a = b`. -/
def cdist (a b : Fin m) : ℕ := (b.val + m - a.val) % m

/-- `wrap r b` is `1` when the counterclockwise arc from `r` to `b` passes through
the cut point (1, 0), and `0` otherwise. -/
def wrap (r b : Fin m) : ℕ := if b.val < r.val then 1 else 0

end Geometry

section Process

variable {m : ℕ} (c : Fin m → Bool)

/-- The set of blue points that have not been used yet. -/
def avail (used : Finset (Fin m)) : Finset (Fin m) :=
  Finset.univ.filter (fun b => c b = false ∧ b ∉ used)

/-- The nearest available blue point to `r`, going counterclockwise from `r`
(if one exists; otherwise, arbitrarily, `r` itself). -/
noncomputable def nb (used : Finset (Fin m)) (r : Fin m) : Fin m :=
  if h : (avail c used).Nonempty then
    Classical.choose (Finset.exists_min_image (avail c used) (cdist r) h)
  else r

/-- The total number of arcs through (1, 0) produced when the red points listed in
`l` are processed in order, starting from the set `used` of already-taken blue
points. -/
noncomputable def wraps : List (Fin m) → Finset (Fin m) → ℕ
  | [], _ => 0
  | (r :: rs), used => wrap r (nb c used r) + wraps rs (insert (nb c used r) used)

end Process

snip begin

section GeometryLemmas

variable {m : ℕ}

lemma cdist_if (a b : Fin m) :
    cdist a b = if a.val ≤ b.val then b.val - a.val else b.val + m - a.val := by
  show (b.val + m - a.val) % m = _
  split_ifs with h
  · have e : b.val + m - a.val = (b.val - a.val) + m := by lia
    rw [e, Nat.add_mod_right, Nat.mod_eq_of_lt (by lia : b.val - a.val < m)]
  · exact Nat.mod_eq_of_lt (by lia)

lemma shift_cdist (a b : Fin m) : shift a (cdist a b) = b := by
  apply Fin.ext
  show (a.val + (b.val + m - a.val) % m) % m = b.val
  rcases le_total a.val b.val with h | h
  · have e : b.val + m - a.val = (b.val - a.val) + m := by lia
    rw [e, Nat.add_mod_right, Nat.mod_eq_of_lt (by lia : b.val - a.val < m)]
    have e2 : a.val + (b.val - a.val) = b.val := by lia
    rw [e2, Nat.mod_eq_of_lt b.isLt]
  · rcases eq_or_lt_of_le h with hbeq | hlt
    · have e : b.val + m - a.val = m := by lia
      rw [e, Nat.mod_self, Nat.add_zero, Nat.mod_eq_of_lt a.isLt, hbeq]
    · have e : (b.val + m - a.val) % m = b.val + m - a.val :=
        Nat.mod_eq_of_lt (by lia)
      rw [e]
      have e2 : a.val + (b.val + m - a.val) = b.val + m := by lia
      rw [e2, Nat.add_mod_right, Nat.mod_eq_of_lt b.isLt]

lemma cdist_left_inj {a b₁ b₂ : Fin m} (h : cdist a b₁ = cdist a b₂) : b₁ = b₂ := by
  rw [← shift_cdist a b₁, ← shift_cdist a b₂, h]

lemma cdist_pos {a b : Fin m} (h : a ≠ b) : 0 < cdist a b := by
  rw [cdist_if]
  have hab : a.val ≠ b.val := fun e => h (Fin.ext e)
  split_ifs with h2 <;> lia

lemma cdist_add_of_lt {a b e : Fin m} (h : cdist a b < cdist a e) :
    cdist a e = cdist a b + cdist b e := by
  simp only [cdist_if] at h ⊢
  have ha := a.isLt; have hb := b.isLt; have he := e.isLt
  split_ifs at h ⊢ <;> lia

lemma arc_rotate {a b e : Fin m} (hab : a ≠ b) (h : cdist a b < cdist a e) :
    cdist b e < cdist b a := by
  simp only [cdist_if] at h ⊢
  have ha := a.isLt; have hb := b.isLt; have he := e.isLt
  have hab' : a.val ≠ b.val := fun e' => hab (Fin.ext e')
  split_ifs at h ⊢ <;> lia

/-- Key fact for the swapping argument: if `p` lies on the open counterclockwise
arc from `y` to `x`, then `wrap p y` and `wrap p x` differ by an amount that does
not depend on `p`. -/
lemma wrap_eq_of_mem_arc {y x p : Fin m} (hpy : p ≠ y) (h : cdist y p < cdist y x) :
    wrap p y = wrap p x + (if y.val < x.val then 1 else 0) := by
  have hp0 : 0 < cdist y p := cdist_pos (Ne.symm hpy)
  simp only [cdist_if] at h hp0
  have hy := y.isLt; have hx := x.isLt; have hp := p.isLt
  have e1 : wrap p y = if y.val < p.val then 1 else 0 := rfl
  have e2 : wrap p x = if x.val < p.val then 1 else 0 := rfl
  rw [e1, e2]
  split_ifs at h hp0 ⊢ <;> lia

end GeometryLemmas

section ProcessLemmas

variable {m : ℕ} (c : Fin m → Bool)

lemma mem_avail {used : Finset (Fin m)} {b : Fin m} :
    b ∈ avail c used ↔ c b = false ∧ b ∉ used := by
  simp only [avail, Finset.mem_filter, Finset.mem_univ, true_and]

lemma nb_eq_choose {used : Finset (Fin m)} {r : Fin m} (h : (avail c used).Nonempty) :
    nb c used r = Classical.choose (Finset.exists_min_image (avail c used) (cdist r) h) :=
  dite_eq_left h

lemma nb_mem {used : Finset (Fin m)} {r : Fin m} (h : (avail c used).Nonempty) :
    nb c used r ∈ avail c used := by
  rw [nb_eq_choose c h]
  exact (Classical.choose_spec (Finset.exists_min_image (avail c used) (cdist r) h)).1

lemma nb_min {used : Finset (Fin m)} {r : Fin m} (h : (avail c used).Nonempty)
    {q : Fin m} (hq : q ∈ avail c used) :
    cdist r (nb c used r) ≤ cdist r q := by
  rw [nb_eq_choose c h]
  exact (Classical.choose_spec (Finset.exists_min_image (avail c used) (cdist r) h)).2 q hq

/-- Uniqueness of the nearest available blue point. -/
lemma nb_eq_of {used : Finset (Fin m)} {r b : Fin m} (h : (avail c used).Nonempty)
    (hb : b ∈ avail c used) (hmin : ∀ q ∈ avail c used, cdist r b ≤ cdist r q) :
    nb c used r = b :=
  cdist_left_inj (le_antisymm (nb_min c h hb) (hmin _ (nb_mem c h)))

lemma avail_insert (b : Fin m) (used : Finset (Fin m)) :
    avail c (insert b used) = (avail c used).erase b := by
  ext x
  simp only [mem_avail, Finset.mem_erase, Finset.mem_insert, not_or]
  tauto

lemma card_avail_insert {b : Fin m} {used : Finset (Fin m)} (hb : b ∈ avail c used) :
    (avail c (insert b used)).card = (avail c used).card - 1 := by
  rw [avail_insert, Finset.card_erase_of_mem hb]

lemma wraps_cons (r : Fin m) (rs : List (Fin m)) (used : Finset (Fin m)) :
    wraps c (r :: rs) used =
      wrap r (nb c used r) + wraps c rs (insert (nb c used r) used) := rfl

/-- The heart of the proof: processing two consecutive red points in either order
produces the same number of arcs through (1, 0) and the same set of used blue points. -/
lemma wraps_swap_pair {r r' : Fin m} (hr : c r = true) (hr' : c r' = true)
    {used : Finset (Fin m)} (hcard : 2 ≤ (avail c used).card) :
    wrap r (nb c used r) + wrap r' (nb c (insert (nb c used r) used) r') =
      wrap r' (nb c used r') + wrap r (nb c (insert (nb c used r') used) r) ∧
    insert (nb c (insert (nb c used r) used) r') (insert (nb c used r) used) =
      insert (nb c (insert (nb c used r') used) r) (insert (nb c used r') used) := by
  have hne : (avail c used).Nonempty := Finset.card_pos.mp (by lia)
  have hb1 : nb c used r ∈ avail c used := nb_mem c hne
  have hd1 : nb c used r' ∈ avail c used := nb_mem c hne
  have hne2 : (avail c (insert (nb c used r) used)).Nonempty := by
    rw [← Finset.card_pos, card_avail_insert c hb1]
    lia
  have hne2' : (avail c (insert (nb c used r') used)).Nonempty := by
    rw [← Finset.card_pos, card_avail_insert c hd1]
    lia
  have hb2 : nb c (insert (nb c used r) used) r' ∈ avail c (insert (nb c used r) used) :=
    nb_mem c hne2
  -- the nearest blue point to `r` is strictly closer than any other available one
  have hlt_r : ∀ q ∈ avail c used, q ≠ nb c used r →
      cdist r (nb c used r) < cdist r q := by
    intro q hq hqne
    exact lt_of_le_of_ne (nb_min c hne hq) (fun e => hqne (cdist_left_inj e).symm)
  have hlt_r' : ∀ q ∈ avail c used, q ≠ nb c used r' →
      cdist r' (nb c used r') < cdist r' q := by
    intro q hq hqne
    exact lt_of_le_of_ne (nb_min c hne hq) (fun e => hqne (cdist_left_inj e).symm)
  by_cases hcase : nb c used r = nb c used r'
  · -- Case A: both red points have the same nearest blue point `x = nb c used r`;
    -- then both second choices equal the next available blue point `y` after `x`.
    have hb2e : nb c (insert (nb c used r) used) r' ≠ nb c used r ∧
        nb c (insert (nb c used r) used) r' ∈ avail c used := by
      have h := hb2
      rw [avail_insert] at h
      exact Finset.mem_erase.mp h
    have hlt_r'b1 : cdist r' (nb c used r) <
        cdist r' (nb c (insert (nb c used r) used) r') := by
      have h := hlt_r' _ hb2e.2 (by rw [← hcase]; exact hb2e.1)
      rwa [← hcase] at h
    have hlt_rq : ∀ q ∈ avail c used, q ≠ nb c used r →
        cdist r' (nb c used r) < cdist r' q := by
      intro q hq hqne
      have h := hlt_r' q hq (by rw [← hcase]; exact hqne)
      rwa [← hcase] at h
    -- the second choice from `r'` is also the nearest available blue point from `r`
    have hmin_b2 : ∀ q ∈ avail c (insert (nb c used r) used),
        cdist r (nb c (insert (nb c used r) used) r') ≤ cdist r q := by
      intro q hq
      have hq' := hq
      rw [avail_insert] at hq'
      obtain ⟨hqne, hqmem⟩ := Finset.mem_erase.mp hq'
      -- decompose the cyclic distances through `x = nb c used r`
      have e1 : cdist r (nb c (insert (nb c used r) used) r') =
          cdist r (nb c used r) +
            cdist (nb c used r) (nb c (insert (nb c used r) used) r') :=
        cdist_add_of_lt (hlt_r _ hb2e.2 hb2e.1)
      have e2 : cdist r q = cdist r (nb c used r) + cdist (nb c used r) q :=
        cdist_add_of_lt (hlt_r q hqmem hqne)
      have e3 : cdist r' (nb c (insert (nb c used r) used) r') =
          cdist r' (nb c used r) +
            cdist (nb c used r) (nb c (insert (nb c used r) used) r') :=
        cdist_add_of_lt hlt_r'b1
      have e4 : cdist r' q = cdist r' (nb c used r) + cdist (nb c used r) q :=
        cdist_add_of_lt (hlt_rq q hqmem hqne)
      have hmin : cdist r' (nb c (insert (nb c used r) used) r') ≤ cdist r' q :=
        nb_min c hne2 hq
      lia
    have hd2_eq : nb c (insert (nb c used r') used) r =
        nb c (insert (nb c used r) used) r' := by
      rw [← hcase]
      exact nb_eq_of c hne2 hb2 hmin_b2
    -- colors and distinctness facts
    have hb1b : c (nb c used r) = false := ((mem_avail c).mp hb1).1
    have hr_ne_b1 : r ≠ nb c used r := by
      intro e; rw [e, hb1b] at hr; contradiction
    have hr'_ne_b1 : r' ≠ nb c used r := by
      intro e; rw [e, hb1b] at hr'; contradiction
    have hr_ne_b2 : r ≠ nb c (insert (nb c used r) used) r' := by
      intro e
      have hb : c (nb c (insert (nb c used r) used) r') = false := ((mem_avail c).mp hb2).1
      rw [e, hb] at hr; contradiction
    have hr'_ne_b2 : r' ≠ nb c (insert (nb c used r) used) r' := by
      intro e
      have hb : c (nb c (insert (nb c used r) used) r') = false := ((mem_avail c).mp hb2).1
      rw [e, hb] at hr'; contradiction
    have hb1_ne_b2 : nb c used r ≠ nb c (insert (nb c used r) used) r' :=
      fun e => hb2e.1 e.symm
    -- both `r` and `r'` lie on the open counterclockwise arc from `y` to `x`
    have harc1 : cdist (nb c used r) (nb c (insert (nb c used r) used) r') <
        cdist (nb c used r) r :=
      arc_rotate hr_ne_b1 (hlt_r _ hb2e.2 hb2e.1)
    have harc1' : cdist (nb c used r) (nb c (insert (nb c used r) used) r') <
        cdist (nb c used r) r' :=
      arc_rotate hr'_ne_b1 hlt_r'b1
    have harc2 : cdist (nb c (insert (nb c used r) used) r') r <
        cdist (nb c (insert (nb c used r) used) r') (nb c used r) :=
      arc_rotate hb1_ne_b2 harc1
    have harc2' : cdist (nb c (insert (nb c used r) used) r') r' <
        cdist (nb c (insert (nb c used r) used) r') (nb c used r) :=
      arc_rotate hb1_ne_b2 harc1'
    -- conclude
    rw [hd2_eq, ← hcase]
    refine ⟨?_, rfl⟩
    have w1 := wrap_eq_of_mem_arc hr_ne_b2 harc2
    have w2 := wrap_eq_of_mem_arc hr'_ne_b2 harc2'
    lia
  · -- Case B: the two red points have different nearest blue points; each keeps
    -- its own blue point regardless of the order.
    have hd1mem : nb c used r' ∈ avail c (insert (nb c used r) used) := by
      rw [avail_insert]
      exact Finset.mem_erase.mpr ⟨Ne.symm hcase, hd1⟩
    have hmin1 : ∀ q ∈ avail c (insert (nb c used r) used),
        cdist r' (nb c used r') ≤ cdist r' q := by
      intro q hq
      rw [avail_insert] at hq
      exact nb_min c hne (Finset.mem_erase.mp hq).2
    have hb2_eq : nb c (insert (nb c used r) used) r' = nb c used r' :=
      nb_eq_of c hne2 hd1mem hmin1
    have hb1mem : nb c used r ∈ avail c (insert (nb c used r') used) := by
      rw [avail_insert]
      exact Finset.mem_erase.mpr ⟨hcase, hb1⟩
    have hmin2 : ∀ q ∈ avail c (insert (nb c used r') used),
        cdist r (nb c used r) ≤ cdist r q := by
      intro q hq
      rw [avail_insert] at hq
      exact nb_min c hne (Finset.mem_erase.mp hq).2
    have hd2_eq : nb c (insert (nb c used r') used) r = nb c used r :=
      nb_eq_of c hne2' hb1mem hmin2
    rw [hb2_eq, hd2_eq]
    exact ⟨Nat.add_comm _ _, Finset.insert_comm _ _ _⟩

/-- The wrap count is invariant under permuting the processing order of the red
points (given that enough blue points remain available at every step). -/
lemma wraps_perm {l₁ l₂ : List (Fin m)} (h : List.Perm l₁ l₂) :
    (∀ r ∈ l₁, c r = true) → ∀ used : Finset (Fin m),
      l₁.length ≤ (avail c used).card → wraps c l₁ used = wraps c l₂ used := by
  refine List.Perm.rec (motive := fun x y _ => (∀ r ∈ x, c r = true) →
    ∀ used : Finset (Fin m), x.length ≤ (avail c used).card →
      wraps c x used = wraps c y used) ?hn ?hc ?hs ?ht h
  · intros; rfl
  · intro a x y hp ih hred used hcard
    have hpos : 0 < (avail c used).card := by
      have hlen : (a :: x).length = x.length + 1 := rfl
      lia
    have hb : nb c used a ∈ avail c used := nb_mem c (Finset.card_pos.mp hpos)
    rw [wraps_cons, wraps_cons]
    have hcard' : x.length ≤ (avail c (insert (nb c used a) used)).card := by
      rw [card_avail_insert c hb]
      have hlen : (a :: x).length = x.length + 1 := rfl
      lia
    rw [ih (fun r hr => hred r (List.mem_cons_of_mem a hr))
      (insert (nb c used a) used) hcard']
  · intro a b l hred used hcard
    have ha : c a = true := hred a (by simp)
    have hb : c b = true := hred b (by simp)
    have h2 : 2 ≤ (avail c used).card := by
      have hlen : (b :: a :: l).length = l.length + 2 := rfl
      lia
    obtain ⟨hsum, hset⟩ := wraps_swap_pair c hb ha h2
    simp only [wraps_cons]
    rw [hset]
    lia
  · intro x y z hp1 hp2 ih1 ih2 hred used hcard
    exact (ih1 hred used hcard).trans
      (ih2 (fun r hr => hred r ((hp1.mem_iff).mpr hr)) used (hp1.length_eq ▸ hcard))

end ProcessLemmas

snip end

/-- **USAMO 2017 Problem 4.** With the notation introduced above (points recorded in
counterclockwise order starting from (1, 0), `true` = red), the number of
counterclockwise arcs `Rᵢ → Bᵢ` containing (1, 0) does not depend on the ordering
`R₁, ..., Rₙ` of the red points. -/
problem usa2017_p4 (n : ℕ) (_hn : 0 < n) (c : Fin (2 * n) → Bool)
    (hred : (Finset.univ.filter (fun i => c i = true)).card = n)
    (l₁ l₂ : List (Fin (2 * n)))
    (hnod₁ : l₁.Nodup) (hlen₁ : l₁.length = n) (hred₁ : ∀ r ∈ l₁, c r = true)
    (hnod₂ : l₂.Nodup) (hlen₂ : l₂.length = n) (hred₂ : ∀ r ∈ l₂, c r = true) :
    wraps c l₁ ∅ = wraps c l₂ ∅ := by
  -- each ordering lists exactly the red points
  have huniv₁ : l₁.toFinset = Finset.univ.filter (fun i => c i = true) := by
    apply Finset.eq_of_subset_of_card_le
    · intro a ha
      rw [List.mem_toFinset] at ha
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ a, hred₁ a ha⟩
    · rw [hred, List.toFinset_card_of_nodup hnod₁, hlen₁]
  have huniv₂ : l₂.toFinset = Finset.univ.filter (fun i => c i = true) := by
    apply Finset.eq_of_subset_of_card_le
    · intro a ha
      rw [List.mem_toFinset] at ha
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ a, hred₂ a ha⟩
    · rw [hred, List.toFinset_card_of_nodup hnod₂, hlen₂]
  have hmem : ∀ a : Fin (2 * n), a ∈ l₁ ↔ a ∈ l₂ := by
    intro a
    rw [← List.mem_toFinset, ← List.mem_toFinset, huniv₁, huniv₂]
  have hperm : List.Perm l₁ l₂ :=
    List.Subperm.antisymm (List.Nodup.subperm hnod₁ (fun a ha => (hmem a).mp ha))
      (List.Nodup.subperm hnod₂ (fun a ha => (hmem a).mpr ha))
  -- there are exactly `n` blue points
  have havail : avail c (∅ : Finset (Fin (2 * n))) =
      Finset.univ.filter (fun i => c i = false) := by
    ext x
    simp only [mem_avail, Finset.mem_filter, Finset.mem_univ, Finset.notMem_empty,
      not_false_eq_true, and_true, true_and]
  have hblue : (avail c (∅ : Finset (Fin (2 * n)))).card = n := by
    rw [havail]
    have hpart : (Finset.univ.filter (fun i => c i = true)).card +
        (Finset.univ.filter (fun i => c i = false)).card = 2 * n := by
      have h : (Finset.univ.filter fun i => c i = false) =
          Finset.univ.filter (fun i => ¬ (c i = true)) := by
        apply Finset.filter_congr
        intro x _
        exact Bool.eq_false_iff
      rw [h, Finset.card_filter_add_card_filter_not (s := Finset.univ)
        (p := fun i => c i = true)]
      simp
    lia
  exact wraps_perm c hperm hred₁ ∅ (by rw [hblue, hlen₁])

end Usa2017P4
