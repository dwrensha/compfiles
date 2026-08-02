/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Module.Torsion.Prod
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.TotallySplit
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Olympiad 2016, Problem 6

There are n ≥ 2 line segments in the plane such that every two segments
cross, and no three segments meet at a point. Geoff has to choose an
endpoint of each segment and place a frog on it facing the other
endpoint. Then he will clap his hands n − 1 times. Every time he claps,
each frog will immediately jump forward to the next intersection point on
its segment. Frogs never change the direction of their jumps. Geoff
wishes to place the frogs in such a way that no two of them will ever
occupy the same intersection point at the same time.

(a) Prove that Geoff can always fulfill his wish if n is odd.
(b) Prove that Geoff can never fulfill his wish if n is even.

# Formalization notes

We follow the standard solution (as in Evan Chen's IMO 2016 solution
notes, solution communicated by Yang Liu). Extend every segment to a
chord of a circle ω that is large enough to contain all the intersection
points, and label the 2n endpoints on ω by P₁, …, P₂ₙ in clockwise
order. Since every two segments cross, the segments must be the chords
PᵢPᵢ₊ₙ (indices modulo 2n). Extending the segments changes neither the
intersection points nor their order along each segment, so the frog
dynamics is unchanged.

We model the endpoints by `ZMod (2 * n)`; the segment through the
endpoint `a` has endpoints `a` and `a + n`. A *frog schedule* `k`
records, for endpoints `a b` on different segments, the clap number
`k a b` at which the frog starting at `a` reaches the intersection point
of its segment with the segment through `b`. Two frogs placed at `a` and
at `b` meet if and only if `k a b = k b a`.

The geometric content of the problem is captured by the fields of
`FrogSchedule`, which hold for the schedule of any configuration of
segments. The last two (the only ones used in the proofs below) follow
from the following counting argument. Let `X` be the intersection of
the chords through `a` and through `b`, where `b` is `d` steps clockwise
from `a` with `1 ≤ d ≤ n - 1`. Any other chord crosses the piece of
chord `a` from `P_a` to `X` if and only if it crosses the piece of
chord `b` from `P_b` to `X`, except for the `d - 1` chords with an
endpoint on the arc from `P_a` to `P_b`, each of which crosses exactly
one of the two pieces. Hence `k a b - k b a` has the same parity as
`d - 1`, so `k a b ≠ k b a` when `d` is even, while for `d = 1` the two
sets of crossing chords coincide, forcing `k a b = k b a`.

# Status of the geometric formalization

The file has two layers. The combinatorial core (`FrogSchedule` and the
two lemmas `imo2016_p6_part_a` and `imo2016_p6_part_b` below it) proves
parts (a) and (b) from the schedule properties `k_consec` and `k_even`.
The geometric layer (namespace `Imo2016P6Geo`) develops the geometry of
arbitrary segment configurations from first principles: the 2D
determinant algebra and crossing criterion, the configuration structure
`SegConf`, the circle extension (`SegConf.radius`, `SegConf.circlePt`),
the cyclic labeling `SegConf.label : ZMod (2 * n) → Fin n × Bool` of the
circle endpoints with the antipodality `SegConf.label_add_n`, the
counting bridge (`SegConf.arrival_segPt_eq_card_oppSide`) linking
arrival times to separating chords, and the two key parity lemmas
(`SegConf.arrival_segPt_eq_of_consec`, `SegConf.arrival_segPt_ne_of_even`).
From these, `SegConf.schedule` builds a `FrogSchedule` for any
configuration, and the two `problem` declarations at the end of the file
(`imo2016_p6_part_a_geo`, `imo2016_p6_part_b_geo`) state and prove the
problem in faithful geometric form.
-/

namespace Imo2016P6

/-- A *frog schedule* for the IMO 2016 Problem 6 frog jumping process:
`k a b` is the clap number at which the frog starting at endpoint `a`
reaches the intersection point of its segment with the segment through
endpoint `b`, where the 2n endpoints are indexed by `ZMod (2 * n)` in
clockwise order and the segment through `a` has endpoints `a` and
`a + n`. The fields are the geometric facts about such schedules; see
the module docstring above for their geometric justification. -/
structure FrogSchedule (n : ℕ) where
  /-- The arrival time of the frog starting at `a` at the crossing with
  the segment through `b`. -/
  k : ZMod (2 * n) → ZMod (2 * n) → ℕ
  /-- The segment through `b` is the same as the segment through
  `b + n`. -/
  k_add_n : ∀ a b, k a b = k a (b + (n : ZMod (2 * n)))
  /-- A frog jumps exactly `n - 1` times, once per clap. -/
  k_mem : ∀ a b, b ≠ a → b ≠ a + (n : ZMod (2 * n)) →
    1 ≤ k a b ∧ k a b ≤ n - 1
  /-- Distinct crossings on the same segment are reached at distinct
  times. -/
  k_inj : ∀ a b c, b ≠ a → b ≠ a + (n : ZMod (2 * n)) →
    c ≠ a → c ≠ a + (n : ZMod (2 * n)) → k a b = k a c →
    c = b ∨ c = b + (n : ZMod (2 * n))
  /-- Frogs placed at consecutive endpoints meet: they reach the
  crossing of their two segments at the same time. -/
  k_consec : ∀ a, k a (a + 1) = k (a + 1) a
  /-- Frogs placed at endpoints an even circular distance apart never
  meet. -/
  k_even : ∀ a b, (b - a).val % 2 = 0 → b ≠ a →
    b ≠ a + (n : ZMod (2 * n)) → k a b ≠ k b a

snip begin

lemma val_add_mod_two {m : ℕ} [NeZero m] (hm : 2 ∣ m) (x y : ZMod m) :
    (x + y).val % 2 = (x.val + y.val) % 2 := by
  rw [ZMod.val_add, Nat.mod_mod_of_dvd _ hm]

lemma val_sub_mod_two {m : ℕ} [NeZero m] (hm : 2 ∣ m) (x y : ZMod m) :
    (x - y).val % 2 = (x.val + y.val) % 2 := by
  have h := val_add_mod_two hm (x - y) y
  rw [sub_add_cancel] at h
  omega

/-- A placement that chooses exactly one endpoint of each segment uses
exactly `n` frogs. -/
lemma card_filter_eq_of_forall_not {n : ℕ} [NeZero (2 * n)] (f : ZMod (2 * n) → Bool)
    (hf : ∀ i, f i = !f (i + (n : ZMod (2 * n)))) :
    (Finset.univ.filter fun i => f i = true).card = n := by
  have hinj : Function.Injective (· + (n : ZMod (2 * n))) :=
    fun _ _ h => add_right_cancel h
  have hbij : Function.Bijective (· + (n : ZMod (2 * n))) :=
    Finite.injective_iff_bijective.mp hinj
  have hg : ∀ i, (if f i = true then (1 : ℕ) else 0) +
      (if f (i + (n : ZMod (2 * n))) = true then 1 else 0) = 1 := by
    intro i
    have h' : f (i + (n : ZMod (2 * n))) = !f i := by rw [hf i, Bool.not_not]
    rw [h']
    cases f i <;> simp
  have hperm :
      ∑ i : ZMod (2 * n), (if f (i + (n : ZMod (2 * n))) = true then (1 : ℕ) else 0)
        = ∑ i : ZMod (2 * n), (if f i = true then 1 else 0) := by
    exact Function.Bijective.sum_comp hbij (fun i => if f i = true then (1 : ℕ) else 0)
  have htot : ∑ _i : ZMod (2 * n), (1 : ℕ) = 2 * n := by
    rw [Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul, mul_one]
  have hsum : (∑ i : ZMod (2 * n), (if f i = true then (1 : ℕ) else 0)) +
      (∑ i : ZMod (2 * n), (if f (i + (n : ZMod (2 * n))) = true then 1 else 0))
      = 2 * n := by
    have h1 : (∑ i : ZMod (2 * n), (if f i = true then (1 : ℕ) else 0)) +
        (∑ i : ZMod (2 * n), (if f (i + (n : ZMod (2 * n))) = true then 1 else 0))
        = ∑ _i : ZMod (2 * n), (1 : ℕ) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => hg i
    exact h1.trans htot
  rw [hperm, Finset.sum_boole, Nat.cast_id] at hsum
  omega

snip end

lemma imo2016_p6_part_a (n : ℕ) (hn : 2 ≤ n) (hodd : Odd n) (s : FrogSchedule n) :
    ∃ f : ZMod (2 * n) → Bool,
      (∀ i, f i = !f (i + (n : ZMod (2 * n)))) ∧
      (∀ a b, f a → f b → a ≠ b → s.k a b ≠ s.k b a) := by
  haveI : NeZero (2 * n) := ⟨by omega⟩
  have h2dvd : 2 ∣ 2 * n := by omega
  refine ⟨fun i => decide (Odd i.val), fun i => ?_, fun a b ha hb hab => ?_⟩
  · -- The placement puts a frog on every other endpoint; since `n` is
    -- odd, `i` and `i + n` have opposite parity, so every segment gets
    -- exactly one frog.
    have hpar : (i + (n : ZMod (2 * n))).val % 2 = (i.val + n) % 2 := by
      rw [val_add_mod_two h2dvd, ZMod.val_natCast_of_lt (by omega)]
    have hodd2 : Odd (i + (n : ZMod (2 * n))).val ↔ ¬Odd i.val := by
      have hn1 : n % 2 = 1 := Nat.odd_iff.mp hodd
      simp only [Nat.odd_iff, hpar]
      omega
    show decide (Odd i.val) = !decide (Odd (i + (n : ZMod (2 * n))).val)
    rw [Bool.decide_congr hodd2, decide_not, Bool.not_not]
  · -- Any two frogs are an even circular distance apart, so by
    -- `k_even` they never occupy the same point at the same time.
    have ha2 : Odd a.val := of_decide_eq_true ha
    have hb2 : Odd b.val := of_decide_eq_true hb
    have hpar : (b - a).val % 2 = 0 := by
      rw [val_sub_mod_two h2dvd]
      have h2 := Nat.odd_iff.mp ha2
      have h3 := Nat.odd_iff.mp hb2
      omega
    have hbna : b ≠ a + (n : ZMod (2 * n)) := by
      intro hcon
      rw [hcon] at hpar
      have e : a + (n : ZMod (2 * n)) - a = (n : ZMod (2 * n)) := by ring
      rw [e, ZMod.val_natCast_of_lt (by omega)] at hpar
      have hn1 : n % 2 = 1 := Nat.odd_iff.mp hodd
      omega
    exact s.k_even a b hpar hab.symm hbna

lemma imo2016_p6_part_b (n : ℕ) (hn : 2 ≤ n) (heven : Even n) (s : FrogSchedule n) :
    ∀ f : ZMod (2 * n) → Bool,
      (∀ i, f i = !f (i + (n : ZMod (2 * n)))) →
      ∃ a b, f a ∧ f b ∧ a ≠ b ∧ s.k a b = s.k b a := by
  intro f hf
  haveI : NeZero (2 * n) := ⟨by omega⟩
  haveI : Fact (1 < 2 * n) := ⟨by omega⟩
  by_contra hcon
  push Not at hcon
  -- No two frogs can sit at consecutive endpoints (`k_consec`).
  have hnoc : ∀ i, f i → f (i + 1) = false := by
    intro i hi
    cases h1 : f (i + 1) with
    | false => rfl
    | true =>
      exfalso
      have hne : i ≠ i + 1 := by
        intro h
        have h2 : (0 : ZMod (2 * n)) = 1 :=
          add_left_cancel (a := i) (b := 0) (c := 1) (by rw [add_zero]; exact h)
        exact zero_ne_one h2
      exact hcon i (i + 1) hi h1 hne (s.k_consec i)
  have hcard := card_filter_eq_of_forall_not f hf
  -- The frogs form an independent set of size `n` in the `2n`-cycle, so
  -- they must alternate: shifting by one endpoint swaps frogs and
  -- non-frogs.
  have hTsub : ((Finset.univ.filter fun i => f i = true).image (· + 1)) ⊆
      (Finset.univ.filter fun i => f i = true)ᶜ := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    rw [Finset.mem_compl, Finset.mem_filter]
    intro hxf
    rw [Finset.mem_filter] at hy
    rw [← hyx] at hxf
    have h3 := hnoc y hy.2
    rw [h3] at hxf
    exact Bool.noConfusion hxf.2
  have hinj1 : Function.Injective (· + (1 : ZMod (2 * n))) :=
    fun _ _ h => add_right_cancel h
  have hTeq : ((Finset.univ.filter fun i => f i = true).image (· + 1)) =
      (Finset.univ.filter fun i => f i = true)ᶜ := by
    apply Finset.eq_of_subset_of_card_le hTsub
    rw [Finset.card_compl, hcard, Finset.card_image_of_injective _ hinj1, hcard,
      ZMod.card]
    omega
  have hstep : ∀ i, f (i + 1) = !f i := by
    intro i
    cases h1 : f i with
    | true => rw [hnoc i h1, Bool.not_true]
    | false =>
      cases h2 : f (i + 1) with
      | true => rw [Bool.not_false]
      | false =>
        exfalso
        have hmem : i + 1 ∈ (Finset.univ.filter fun i => f i = true)ᶜ := by
          simp only [Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and]
          rw [h2]
          exact Bool.noConfusion
        rw [← hTeq, Finset.mem_image] at hmem
        obtain ⟨y, hy, hyx⟩ := hmem
        rw [Finset.mem_filter] at hy
        have hyi : y = i := add_right_cancel hyx
        rw [hyi, h1] at hy
        exact Bool.noConfusion hy.2
  -- Hence the placement is 2-periodic, so the two endpoints `0` and `n`
  -- of one segment either both get a frog or neither does:
  -- contradiction, since `n` is even.
  have hper : ∀ j : ℕ, f (((j + j : ℕ)) : ZMod (2 * n)) = f 0 := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have e : (((j + 1) + (j + 1) : ℕ) : ZMod (2 * n))
          = (((j + j : ℕ)) : ZMod (2 * n)) + 1 + 1 := by
        push_cast
        ring
      rw [e, hstep, hstep, Bool.not_not, ih]
  obtain ⟨m, hm⟩ := heven
  have h1 : f ((n : ZMod (2 * n))) = f 0 := by
    have e : (n : ZMod (2 * n)) = ((m + m : ℕ) : ZMod (2 * n)) := by rw [hm]
    rw [e]
    exact hper m
  have h2 := hf 0
  rw [zero_add, h1] at h2
  cases h : f 0 <;> rw [h] at h2 <;> exact Bool.noConfusion h2

end Imo2016P6

/-! ## Geometric layer: segment configurations and frog dynamics

The definitions and lemmas in this section (namespace `Imo2016P6Geo`)
develop the geometry of the problem faithfully from the planar segment
hypotheses; see the module docstring for how they fit into the proof.
Status: complete (the cyclic labeling, the counting bridge, the
schedule, and the faithful geometric statements are all in place). -/

namespace Imo2016P6Geo

/-- The 2D determinant (scalar cross product) of two vectors in `ℝ × ℝ`. -/
def detv (u v : ℝ × ℝ) : ℝ := u.1 * v.2 - u.2 * v.1

lemma detv_def (u v : ℝ × ℝ) : detv u v = u.1 * v.2 - u.2 * v.1 := rfl

lemma detv_self (u : ℝ × ℝ) : detv u u = 0 := by
  show u.1 * u.2 - u.2 * u.1 = 0
  ring

lemma detv_antisymm (u v : ℝ × ℝ) : detv u v = -detv v u := by
  show u.1 * v.2 - u.2 * v.1 = -(v.1 * u.2 - v.2 * u.1)
  ring

lemma detv_add_left (u v w : ℝ × ℝ) : detv (u + w) v = detv u v + detv w v := by
  show (u.1 + w.1) * v.2 - (u.2 + w.2) * v.1
    = u.1 * v.2 - u.2 * v.1 + (w.1 * v.2 - w.2 * v.1)
  ring

lemma detv_add_right (u v w : ℝ × ℝ) : detv u (v + w) = detv u v + detv u w := by
  show u.1 * (v.2 + w.2) - u.2 * (v.1 + w.1)
    = u.1 * v.2 - u.2 * v.1 + (u.1 * w.2 - u.2 * w.1)
  ring

lemma detv_smul_left (c : ℝ) (u v : ℝ × ℝ) : detv (c • u) v = c * detv u v := by
  show c * u.1 * v.2 - c * u.2 * v.1 = c * (u.1 * v.2 - u.2 * v.1)
  ring

lemma detv_smul_right (c : ℝ) (u v : ℝ × ℝ) : detv u (c • v) = c * detv u v := by
  show u.1 * (c * v.2) - u.2 * (c * v.1) = c * (u.1 * v.2 - u.2 * v.1)
  ring

lemma detv_neg_left (u v : ℝ × ℝ) : detv (-u) v = -detv u v := by
  show -u.1 * v.2 - -u.2 * v.1 = -(u.1 * v.2 - u.2 * v.1)
  ring

lemma detv_neg_right (u v : ℝ × ℝ) : detv u (-v) = -detv u v := by
  show u.1 * (-v.2) - u.2 * (-v.1) = -(u.1 * v.2 - u.2 * v.1)
  ring

lemma detv_sub_left (u v w : ℝ × ℝ) : detv (u - w) v = detv u v - detv w v := by
  show (u.1 - w.1) * v.2 - (u.2 - w.2) * v.1
    = u.1 * v.2 - u.2 * v.1 - (w.1 * v.2 - w.2 * v.1)
  ring

lemma detv_sub_right (u v w : ℝ × ℝ) : detv u (v - w) = detv u v - detv u w := by
  show u.1 * (v.2 - w.2) - u.2 * (v.1 - w.1)
    = u.1 * v.2 - u.2 * v.1 - (u.1 * w.2 - u.2 * w.1)
  ring

/-- If the determinant of `u` and `v` vanishes and `u ≠ 0`, then `v` is a
scalar multiple of `u`. -/
lemma exists_smul_of_detv_eq_zero {u v : ℝ × ℝ} (hu : u ≠ 0) (h : detv u v = 0) :
    ∃ c : ℝ, v = c • u := by
  have hu' : u.1 ≠ 0 ∨ u.2 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hu (Prod.ext hcon.1 hcon.2)
  simp only [detv_def] at h
  rcases hu' with h1 | h1
  · refine ⟨v.1 / u.1, ?_⟩
    have e1 : v.1 = (v.1 / u.1) * u.1 := by field_simp
    have e2 : v.2 = (v.1 / u.1) * u.2 := by field_simp; linarith
    ext
    · show v.1 = (v.1 / u.1) • u.1
      rw [smul_eq_mul, ← e1]
    · show v.2 = (v.1 / u.1) • u.2
      rw [smul_eq_mul, ← e2]
  · refine ⟨v.2 / u.2, ?_⟩
    have e1 : v.2 = (v.2 / u.2) * u.2 := by field_simp
    have e2 : v.1 = (v.2 / u.2) * u.1 := by field_simp; linarith
    ext
    · show v.1 = (v.2 / u.2) • u.1
      rw [smul_eq_mul, ← e2]
    · show v.2 = (v.2 / u.2) • u.2
      rw [smul_eq_mul, ← e1]

/-- The intersection of the line through `a` in direction `u` with the line
through `p` in direction `v`, expressed as a point on the first line. -/
noncomputable def lineMeet (a u p v : ℝ × ℝ) : ℝ × ℝ :=
  a + (detv (p - a) v / detv u v) • u

lemma detv_lineMeet_sub_left (a u p v : ℝ × ℝ) :
    detv (lineMeet a u p v - a) u = 0 := by
  have e : lineMeet a u p v - a = (detv (p - a) v / detv u v) • u := by
    show (a + _ • u) - a = _ • u
    abel
  rw [e, detv_smul_left, detv_self, mul_zero]

lemma detv_lineMeet_sub_right (a u p v : ℝ × ℝ) (h : detv u v ≠ 0) :
    detv (lineMeet a u p v - p) v = 0 := by
  have e : lineMeet a u p v - p = (a - p) + (detv (p - a) v / detv u v) • u := by
    show (a + _ • u) - p = (a - p) + _ • u
    abel
  rw [e, detv_add_left, detv_smul_left, div_mul_cancel₀ _ h]
  show (a.1 - p.1) * v.2 - (a.2 - p.2) * v.1
    + ((p.1 - a.1) * v.2 - (p.2 - a.2) * v.1) = 0
  ring

/-- Membership in an open segment in terms of the parameter along the
segment. -/
lemma mem_openSegment_iff_param {a b X : ℝ × ℝ} :
    X ∈ openSegment ℝ a b ↔ ∃ t ∈ Set.Ioo (0 : ℝ) 1, X = a + t • (b - a) := by
  rw [openSegment_eq_image]
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨t, ht, ?_⟩
    show (1 - t) • a + t • b = a + t • (b - a)
    rw [sub_smul, one_smul, smul_sub]
    abel
  · rintro ⟨t, ht, rfl⟩
    refine ⟨t, ht, ?_⟩
    show (1 - t) • a + t • b = a + t • (b - a)
    rw [sub_smul, one_smul, smul_sub]
    abel

/-- The parameter of the intersection point on the first line. -/
noncomputable def meetParam (a u p v : ℝ × ℝ) : ℝ := detv (p - a) v / detv u v

lemma lineMeet_eq_add (a u p v : ℝ × ℝ) :
    lineMeet a u p v = a + meetParam a u p v • u := rfl

/-- `p` and `q` are strictly on the same side of the line through `a` in
direction `u`. -/
def SameSide (a u p q : ℝ × ℝ) : Prop := 0 < detv u (p - a) * detv u (q - a)

/-- `p` and `q` are strictly on opposite sides of the line through `a` in
direction `u`. -/
def OppSide (a u p q : ℝ × ℝ) : Prop := detv u (p - a) * detv u (q - a) < 0

lemma div_mem_Ioo {x y : ℝ} (hy : y ≠ 0) :
    x / y ∈ Set.Ioo (0 : ℝ) 1 ↔ 0 < x * y ∧ x * y < y * y := by
  rw [Set.mem_Ioo]
  rcases lt_or_gt_of_ne hy with h | h
  · constructor
    · rintro ⟨h1, h2⟩
      have hx : x < 0 := by
        rcases div_pos_iff.mp h1 with ⟨g1, g2⟩ | ⟨g1, g2⟩ <;> linarith
      have hxy : y < x := by
        rw [div_lt_iff_of_neg h] at h2
        linarith
      exact ⟨mul_pos_of_neg_of_neg hx h, by nlinarith [hxy, h]⟩
    · rintro ⟨h1, h2⟩
      have hx : x < 0 := by
        rcases mul_pos_iff.mp h1 with ⟨g1, g2⟩ | ⟨g1, g2⟩ <;> linarith
      have e : (x - y) * y = x * y - y * y := by ring
      have h3 : (x - y) * y < 0 := by rw [e]; linarith
      have hxy : y < x := by
        rcases mul_neg_iff.mp h3 with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> linarith
      refine ⟨div_pos_of_neg_of_neg hx h, ?_⟩
      rw [div_lt_iff_of_neg h]
      linarith
  · constructor
    · rintro ⟨h1, h2⟩
      have hx : 0 < x := by
        rcases div_pos_iff.mp h1 with ⟨g1, g2⟩ | ⟨g1, g2⟩ <;> linarith
      have hxy : x < y := by
        rw [div_lt_iff₀ h] at h2
        linarith
      exact ⟨mul_pos hx h, mul_lt_mul_of_pos_right hxy h⟩
    · rintro ⟨h1, h2⟩
      have hx : 0 < x := by
        rcases mul_pos_iff.mp h1 with ⟨g1, g2⟩ | ⟨g1, g2⟩ <;> linarith
      have e : (y - x) * y = y * y - x * y := by ring
      have h3 : 0 < (y - x) * y := by rw [e]; linarith
      have hxy : x < y := by
        rcases mul_pos_iff.mp h3 with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> linarith
      refine ⟨div_pos hx h, ?_⟩
      rw [div_lt_iff₀ h]
      linarith

end Imo2016P6Geo

namespace Imo2016P6Geo

lemma detv_zero_left (v : ℝ × ℝ) : detv 0 v = 0 := by
  simp [detv_def]

lemma detv_zero_right (u : ℝ × ℝ) : detv u 0 = 0 := by
  simp [detv_def]

/-- Sign lemma: `F (F - D) < 0` iff `F / D ∈ (0, 1)` (product form). -/
lemma sign_S1 {F D : ℝ} : F * (F - D) < 0 ↔ 0 < F * D ∧ F * D < D * D := by
  constructor
  · intro h
    rcases mul_neg_iff.mp h with ⟨g1, g2⟩ | ⟨g1, g2⟩
    · have hD : 0 < D := by linarith
      exact ⟨mul_pos g1 hD, mul_lt_mul_of_pos_right (by linarith : F < D) hD⟩
    · have hD : D < 0 := by linarith
      exact ⟨mul_pos_of_neg_of_neg g1 hD, mul_lt_mul_of_neg_right (by linarith : D < F) hD⟩
  · intro ⟨h1, h2⟩
    rcases mul_pos_iff.mp h1 with ⟨g1, g2⟩ | ⟨g1, g2⟩
    · have hFD : F < D := lt_of_mul_lt_mul_right h2 g2.le
      exact mul_neg_of_pos_of_neg g1 (by linarith)
    · have h3 : 0 < (D - F) * D := by nlinarith [h2]
      have hDF : D - F < 0 := by
        rcases mul_pos_iff.mp h3 with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> linarith
      exact mul_neg_of_neg_of_pos g1 (by linarith)

/-- Sign lemma: `G (G + D) < 0` iff `-G / D ∈ (0, 1)` (product form). -/
lemma sign_S2 {G D : ℝ} : G * (G + D) < 0 ↔ G * D < 0 ∧ -G * D < D * D := by
  constructor
  · intro h
    rcases mul_neg_iff.mp h with ⟨g1, g2⟩ | ⟨g1, g2⟩
    · have hD : D < 0 := by linarith
      refine ⟨by nlinarith, ?_⟩
      nlinarith [mul_lt_mul_of_neg_right (show D < -G from by linarith) hD]
    · have hD : 0 < D := by linarith
      refine ⟨by nlinarith, ?_⟩
      nlinarith [mul_lt_mul_of_pos_right (show -G < D from by linarith) hD]
  · intro ⟨h1, h2⟩
    rcases mul_neg_iff.mp h1 with ⟨g1, g2⟩ | ⟨g1, g2⟩
    · have h3 : 0 < (G + D) * D := by nlinarith [h2]
      have hGD : G + D < 0 := by
        rcases mul_pos_iff.mp h3 with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> linarith
      exact mul_neg_of_pos_of_neg g1 hGD
    · have h3 : 0 < (G + D) * D := by nlinarith [h2]
      have hGD : 0 < G + D := by
        rcases mul_pos_iff.mp h3 with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> linarith
      exact mul_neg_of_neg_of_pos g1 hGD

/-- If two segments cross properly and their directions are not parallel,
then the endpoints of each segment lie on opposite sides of the other
segment's line. -/
lemma oppSide_of_properCross {a a' b b' X : ℝ × ℝ}
    (hX : X ∈ openSegment ℝ a a' ∧ X ∈ openSegment ℝ b b')
    (hd : detv (a' - a) (b' - b) ≠ 0) :
    OppSide a (a' - a) b b' ∧ OppSide b (b' - b) a a' := by
  obtain ⟨t, ht, hXt⟩ := mem_openSegment_iff_param.mp hX.1
  obtain ⟨s, hs, hXs⟩ := mem_openSegment_iff_param.mp hX.2
  have e : b - a = t • (a' - a) - s • (b' - b) := by
    have h1 : a + t • (a' - a) = b + s • (b' - b) := hXt.symm.trans hXs
    calc b - a = (a + t • (a' - a)) - a - s • (b' - b) := by rw [h1]; abel
    _ = t • (a' - a) - s • (b' - b) := by abel
  have h1 : detv (a' - a) (b - a) = -s * detv (a' - a) (b' - b) := by
    rw [e, detv_sub_right, detv_smul_right, detv_self, mul_zero, zero_sub,
      detv_smul_right]
    ring
  have h2 : detv (a' - a) (b' - a) = (1 - s) * detv (a' - a) (b' - b) := by
    have e2 : b' - a = (b - a) + (b' - b) := by abel
    rw [e2, detv_add_right, h1]
    ring
  have h3 : detv (a' - a) (b - a) * detv (a' - a) (b' - a) < 0 := by
    rw [h1, h2]
    have hD2 : 0 < detv (a' - a) (b' - b) ^ 2 := sq_pos_of_ne_zero hd
    have hsp : 0 < s * (1 - s) := mul_pos hs.1 (by linarith [hs.2])
    have e3 : (-s * detv (a' - a) (b' - b)) * ((1 - s) * detv (a' - a) (b' - b))
        = -(s * (1 - s)) * detv (a' - a) (b' - b) ^ 2 := by ring
    rw [e3]
    exact mul_neg_of_neg_of_pos (neg_lt_zero.mpr hsp) hD2
  have e' : a - b = s • (b' - b) - t • (a' - a) := by
    have h1 : b + s • (b' - b) = a + t • (a' - a) := hXs.symm.trans hXt
    calc a - b = (b + s • (b' - b)) - b - t • (a' - a) := by rw [h1]; abel
    _ = s • (b' - b) - t • (a' - a) := by abel
  have g1 : detv (b' - b) (a - b) = -t * detv (b' - b) (a' - a) := by
    rw [e', detv_sub_right, detv_smul_right, detv_self, mul_zero, zero_sub,
      detv_smul_right]
    ring
  have g2 : detv (b' - b) (a' - b) = (1 - t) * detv (b' - b) (a' - a) := by
    have e2 : a' - b = (a - b) + (a' - a) := by abel
    rw [e2, detv_add_right, g1]
    ring
  have g3 : detv (b' - b) (a - b) * detv (b' - b) (a' - b) < 0 := by
    rw [g1, g2]
    have hd' : detv (b' - b) (a' - a) ≠ 0 := by
      rw [detv_antisymm]
      exact neg_ne_zero.mpr hd
    have hD2 : 0 < detv (b' - b) (a' - a) ^ 2 := sq_pos_of_ne_zero hd'
    have hsp : 0 < t * (1 - t) := mul_pos ht.1 (by linarith [ht.2])
    have e3 : (-t * detv (b' - b) (a' - a)) * ((1 - t) * detv (b' - b) (a' - a))
        = -(t * (1 - t)) * detv (b' - b) (a' - a) ^ 2 := by ring
    rw [e3]
    exact mul_neg_of_neg_of_pos (neg_lt_zero.mpr hsp) hD2
  exact ⟨h3, g3⟩

/-- If the endpoints of each segment lie on opposite sides of the other
segment's line, the two segments cross properly. -/
lemma properCross_of_oppSide {a a' b b' : ℝ × ℝ}
    (h1 : OppSide a (a' - a) b b') (h2 : OppSide b (b' - b) a a') :
    ∃ X, X ∈ openSegment ℝ a a' ∧ X ∈ openSegment ℝ b b' := by
  have hD : detv (a' - a) (b' - b) ≠ 0 := by
    intro hd
    have he : detv (a' - a) (b' - a) = detv (a' - a) (b - a) := by
      have e : b' - a = (b - a) + (b' - b) := by abel
      rw [e, detv_add_right, hd, add_zero]
    have h1c : detv (a' - a) (b - a) * detv (a' - a) (b' - a) < 0 := h1
    rw [he] at h1c
    exact not_lt_of_ge (mul_self_nonneg _) h1c
  have hDv : detv (b' - b) (a' - a) ≠ 0 := by
    rw [detv_antisymm]; exact neg_ne_zero.mpr hD
  -- Sign conditions in the `t`- and `s`-parameter form
  have hG : detv (a' - a) (b - a) * (detv (a' - a) (b - a) + detv (a' - a) (b' - b)) < 0 := by
    have he : detv (a' - a) (b' - a) = detv (a' - a) (b - a) + detv (a' - a) (b' - b) := by
      have e : b' - a = (b - a) + (b' - b) := by abel
      rw [e, detv_add_right]
    have h1c : detv (a' - a) (b - a) * detv (a' - a) (b' - a) < 0 := h1
    rw [he] at h1c
    exact h1c
  have hF : detv (b' - b) (a - b) * (detv (b' - b) (a - b) - detv (a' - a) (b' - b)) < 0 := by
    have he : detv (b' - b) (a' - b) = detv (b' - b) (a - b) - detv (a' - a) (b' - b) := by
      have e : a' - b = (a - b) + (a' - a) := by abel
      rw [e, detv_add_right, detv_antisymm (b' - b) (a' - a)]
      ring
    have h2c : detv (b' - b) (a - b) * detv (b' - b) (a' - b) < 0 := h2
    rw [he] at h2c
    exact h2c
  obtain ⟨hGD1, hGD2⟩ := sign_S2.mp hG
  obtain ⟨hFD1, hFD2⟩ := sign_S1.mp hF
  have eF : detv (b - a) (b' - b) = detv (b' - b) (a - b) := by
    show (b.1 - a.1) * (b' - b).2 - (b.2 - a.2) * (b' - b).1
      = (b' - b).1 * (a.2 - b.2) - (b' - b).2 * (a.1 - b.1)
    ring
  have htIoo : meetParam a (a' - a) b (b' - b) ∈ Set.Ioo (0 : ℝ) 1 := by
    rw [meetParam, div_mem_Ioo hD, eF]
    exact ⟨hFD1, hFD2⟩
  have eG : detv (a - b) (a' - a) = detv (a' - a) (b - a) := by
    show (a.1 - b.1) * (a' - a).2 - (a.2 - b.2) * (a' - a).1
      = (a' - a).1 * (b.2 - a.2) - (a' - a).2 * (b.1 - a.1)
    ring
  have hsIoo : detv (a - b) (a' - a) / detv (b' - b) (a' - a) ∈ Set.Ioo (0 : ℝ) 1 := by
    rw [div_mem_Ioo hDv, eG, detv_antisymm (b' - b) (a' - a)]
    constructor <;> nlinarith [hGD1, hGD2]
  refine ⟨lineMeet a (a' - a) b (b' - b), ?_, ?_⟩
  · rw [mem_openSegment_iff_param]
    exact ⟨meetParam a (a' - a) b (b' - b), htIoo, rfl⟩
  · rw [mem_openSegment_iff_param]
    have hv : b' - b ≠ 0 := by
      intro hzero
      rw [hzero, detv_zero_right] at hD
      exact hD rfl
    obtain ⟨c, hc⟩ := exists_smul_of_detv_eq_zero hv (by
      rw [detv_antisymm, detv_lineMeet_sub_right a (a' - a) b (b' - b) hD, neg_zero])
    have hcs : c = detv (a - b) (a' - a) / detv (b' - b) (a' - a) := by
      have hdet : detv (lineMeet a (a' - a) b (b' - b) - b) (a' - a)
          = detv (a - b) (a' - a) := by
        have e : lineMeet a (a' - a) b (b' - b) - b
            = (a - b) + meetParam a (a' - a) b (b' - b) • (a' - a) := by
          rw [lineMeet_eq_add]
          abel
        rw [e, detv_add_left, detv_smul_left, detv_self, mul_zero, add_zero]
      rw [hc, detv_smul_left] at hdet
      have hDv' : detv (b' - b) (a' - a) ≠ 0 := hDv
      field_simp
      linarith [hdet]
    refine ⟨c, hcs ▸ hsIoo, ?_⟩
    rw [← hc]
    exact (add_sub_cancel _ _).symm

end Imo2016P6Geo

namespace Imo2016P6Geo

/-- A configuration of `n` segments in the plane as in IMO 2016 Problem 6:
every two segments cross (at an interior point of each, with non-parallel
directions, which makes the crossing point unique), and no three segments
have a point in common. -/
structure SegConf (n : ℕ) where
  /-- The segments, given by their two endpoints. -/
  seg : Fin n → (ℝ × ℝ) × (ℝ × ℝ)
  /-- The directions of any two segments are not parallel. -/
  dir_ne : ∀ i j, i ≠ j → detv ((seg i).2 - (seg i).1) ((seg j).2 - (seg j).1) ≠ 0
  /-- Every two segments cross: they share a point of both open segments. -/
  crosses : ∀ i j, i ≠ j → ∃ X, X ∈ openSegment ℝ (seg i).1 (seg i).2 ∧
    X ∈ openSegment ℝ (seg j).1 (seg j).2
  /-- No three segments pass through a common point. -/
  noconcur : ∀ i j k, i ≠ j → j ≠ k → i ≠ k → ¬∃ X,
    X ∈ segment ℝ (seg i).1 (seg i).2 ∧ X ∈ segment ℝ (seg j).1 (seg j).2 ∧
    X ∈ segment ℝ (seg k).1 (seg k).2

namespace SegConf

variable {n : ℕ} (C : SegConf n)

/-- Every segment is nondegenerate: its two endpoints differ. -/
lemma endpoints_ne (hn : 2 ≤ n) (i : Fin n) : (C.seg i).1 ≠ (C.seg i).2 := by
  intro h
  obtain ⟨j, hj⟩ := Fintype.exists_ne_of_one_lt_card (α := Fin n) (by
    rw [Fintype.card_fin]; omega) i
  have hd := C.dir_ne i j hj.symm
  rw [h, sub_self, detv_zero_left] at hd
  exact hd rfl

/-- The crossing point of two segments. -/
noncomputable def xpoint (i j : Fin n) (h : i ≠ j) : ℝ × ℝ :=
  Classical.choose (C.crosses i j h)

lemma xpoint_mem (i j : Fin n) (h : i ≠ j) :
    C.xpoint i j h ∈ openSegment ℝ (C.seg i).1 (C.seg i).2 ∧
    C.xpoint i j h ∈ openSegment ℝ (C.seg j).1 (C.seg j).2 :=
  Classical.choose_spec (C.crosses i j h)

/-- The crossing point is the unique common point of the two segments. -/
lemma xpoint_unique (i j : Fin n) (h : i ≠ j) {X : ℝ × ℝ}
    (hX : X ∈ openSegment ℝ (C.seg i).1 (C.seg i).2 ∧
      X ∈ openSegment ℝ (C.seg j).1 (C.seg j).2) :
    X = C.xpoint i j h := by
  have hd := C.dir_ne i j h
  obtain ⟨t1, ht1, hXt1⟩ := mem_openSegment_iff_param.mp hX.1
  obtain ⟨s1, hs1, hXs1⟩ := mem_openSegment_iff_param.mp hX.2
  obtain ⟨t2, ht2, hXt2⟩ := mem_openSegment_iff_param.mp (C.xpoint_mem i j h).1
  obtain ⟨s2, hs2, hXs2⟩ := mem_openSegment_iff_param.mp (C.xpoint_mem i j h).2
  have e0 : (t1 - t2) • ((C.seg i).2 - (C.seg i).1)
      - (s1 - s2) • ((C.seg j).2 - (C.seg j).1) = 0 := by
    have h1 : (C.seg i).1 + t1 • ((C.seg i).2 - (C.seg i).1)
        = (C.seg j).1 + s1 • ((C.seg j).2 - (C.seg j).1) := hXt1.symm.trans hXs1
    have h2 : (C.seg i).1 + t2 • ((C.seg i).2 - (C.seg i).1)
        = (C.seg j).1 + s2 • ((C.seg j).2 - (C.seg j).1) := hXt2.symm.trans hXs2
    have h3 : (t1 - t2) • ((C.seg i).2 - (C.seg i).1) - (s1 - s2) • ((C.seg j).2 - (C.seg j).1)
        = ((C.seg i).1 + t1 • ((C.seg i).2 - (C.seg i).1))
          - ((C.seg i).1 + t2 • ((C.seg i).2 - (C.seg i).1))
          - (((C.seg j).1 + s1 • ((C.seg j).2 - (C.seg j).1))
            - ((C.seg j).1 + s2 • ((C.seg j).2 - (C.seg j).1))) := by
      rw [sub_smul, sub_smul]
      abel
    rw [h3, h1, h2]
    abel
  have ht : t1 = t2 := by
    have hdet : detv ((t1 - t2) • ((C.seg i).2 - (C.seg i).1)) ((C.seg j).2 - (C.seg j).1)
        = detv ((s1 - s2) • ((C.seg j).2 - (C.seg j).1)) ((C.seg j).2 - (C.seg j).1) := by
      rw [sub_eq_zero] at e0
      rw [e0]
    rw [detv_smul_left, detv_smul_left, detv_self, mul_zero] at hdet
    rcases mul_eq_zero.mp hdet with h4 | h4
    · linarith
    · exact absurd h4 hd
  rw [hXt1, hXt2, ht]

/-- The crossing points on one segment are distinct for distinct other
segments. -/
lemma xpoint_ne_of_ne {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    C.xpoint i j hij ≠ C.xpoint i k hik := by
  intro heq
  have h1 := (C.xpoint_mem i j hij).1
  have h2 := (C.xpoint_mem i j hij).2
  have h3 := (C.xpoint_mem i k hik).2
  rw [← heq] at h3
  exact C.noconcur i j k hij hjk hik
    ⟨C.xpoint i j hij, openSegment_subset_segment _ _ _ h1,
      openSegment_subset_segment _ _ _ h2, openSegment_subset_segment _ _ _ h3⟩

/-- The set of crossing points on segment `i`, as a `Finset` with `n - 1`
elements. -/
noncomputable def crossings (i : Fin n) : Finset (ℝ × ℝ) :=
  Finset.univ.image fun j : {j // i ≠ j} => C.xpoint i j j.2

lemma mem_crossings {i : Fin n} {X : ℝ × ℝ} :
    X ∈ C.crossings i ↔ ∃ j, ∃ h : i ≠ j, X = C.xpoint i j h := by
  rw [crossings, Finset.mem_image]
  constructor
  · rintro ⟨j, _, rfl⟩
    exact ⟨j, j.2, rfl⟩
  · rintro ⟨j, h, rfl⟩
    exact ⟨⟨j, h⟩, Finset.mem_univ _, rfl⟩

lemma crossings_card (i : Fin n) : (C.crossings i).card = n - 1 := by
  have hinj : Function.Injective fun j : {j // i ≠ j} => C.xpoint i j j.2 := by
    intro ⟨j, hj⟩ ⟨k, hk⟩ heq
    by_contra hcon
    have hjk : j ≠ k := fun h => hcon (Subtype.ext h)
    exact C.xpoint_ne_of_ne hj hk hjk heq
  rw [crossings, Finset.card_image_of_injective _ hinj, Finset.card_univ,
    Fintype.card_subtype]
  have hfe : (Finset.univ.filter fun j => i ≠ j) = Finset.univ \ {i} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff,
      Finset.mem_singleton]
    exact not_congr eq_comm
  rw [hfe, Finset.card_univ_sdiff, Fintype.card_fin, Finset.card_singleton]

/-- Distances from an endpoint `A` are injective on the crossing points of
segment `i`: the crossings lie on the ray from `A` along the segment. -/
lemma dist_eq_of_mem_crossings (hn : 2 ≤ n) {i : Fin n} {A X Y : ℝ × ℝ}
    (hA : A = (C.seg i).1 ∨ A = (C.seg i).2)
    (hX : X ∈ C.crossings i) (hY : Y ∈ C.crossings i)
    (hd : dist A X = dist A Y) : X = Y := by
  obtain ⟨B, hB1, hAB⟩ : ∃ B, openSegment ℝ A B
      = openSegment ℝ (C.seg i).1 (C.seg i).2 ∧ A ≠ B := by
    rcases hA with rfl | rfl
    · exact ⟨(C.seg i).2, rfl, C.endpoints_ne hn i⟩
    · exact ⟨(C.seg i).1, openSegment_symm ℝ _ _, (C.endpoints_ne hn i).symm⟩
  have hmemX : X ∈ openSegment ℝ (C.seg i).1 (C.seg i).2 := by
    obtain ⟨j, hj, rfl⟩ := C.mem_crossings.mp hX
    exact (C.xpoint_mem i j hj).1
  have hmemY : Y ∈ openSegment ℝ (C.seg i).1 (C.seg i).2 := by
    obtain ⟨j, hj, rfl⟩ := C.mem_crossings.mp hY
    exact (C.xpoint_mem i j hj).1
  rw [← hB1] at hmemX hmemY
  obtain ⟨t1, ht1, hX2⟩ := mem_openSegment_iff_param.mp hmemX
  obtain ⟨t2, ht2, hY2⟩ := mem_openSegment_iff_param.mp hmemY
  have hdistAB : dist A B ≠ 0 := dist_ne_zero.mpr hAB
  have hnorm : ∀ t : ℝ, 0 < t → dist A (A + t • (B - A)) = t * dist A B := by
    intro t ht
    rw [dist_comm, dist_eq_norm]
    have e : A + t • (B - A) - A = t • (B - A) := by abel
    rw [e, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    have e3 : A - B = -(B - A) := by abel
    rw [dist_eq_norm, e3, norm_neg]
  have ht : t1 = t2 := by
    have h1 := hnorm t1 ht1.1
    have h2 := hnorm t2 ht2.1
    rw [hX2] at hd
    rw [hY2] at hd
    rw [h1, h2] at hd
    exact mul_right_cancel₀ hdistAB hd
  rw [hX2, hY2, ht]

/-- The minimizing segment for the distance from `A`: existence. -/
lemma exists_firstSeg (hn : 2 ≤ n) (i : Fin n) (A : ℝ × ℝ) :
    ∃ j : {j // i ≠ j}, ∀ k : {j // i ≠ j},
      dist A (C.xpoint i j j.2) ≤ dist A (C.xpoint i k k.2) := by
  have hnemp : (Finset.univ : Finset {j // i ≠ j}).Nonempty := by
    rw [Finset.univ_nonempty_iff]
    obtain ⟨j, hj⟩ := Fintype.exists_ne_of_one_lt_card (α := Fin n) (by
      rw [Fintype.card_fin]; omega) i
    exact ⟨⟨j, hj.symm⟩⟩
  obtain ⟨j, _, hj⟩ := Finset.exists_min_image Finset.univ
    (fun j : {j // i ≠ j} => dist A (C.xpoint i j j.2)) hnemp
  exact ⟨j, fun k => hj k (Finset.mem_univ k)⟩

/-- The segment of the first crossing from endpoint `A` of segment `i`. -/
noncomputable def firstSeg (hn : 2 ≤ n) (i : Fin n) (A : ℝ × ℝ) : {j // i ≠ j} :=
  Classical.choose (C.exists_firstSeg hn i A)

lemma firstSeg_spec (hn : 2 ≤ n) (i : Fin n) (A : ℝ × ℝ) (k : {j // i ≠ j}) :
    dist A (C.xpoint i (C.firstSeg hn i A) (C.firstSeg hn i A).2) ≤
      dist A (C.xpoint i k k.2) :=
  Classical.choose_spec (C.exists_firstSeg hn i A) k

/-- The first crossing from endpoint `A` of segment `i`. -/
noncomputable def firstCrossing (hn : 2 ≤ n) (i : Fin n) (A : ℝ × ℝ) : ℝ × ℝ :=
  C.xpoint i (C.firstSeg hn i A) (C.firstSeg hn i A).2

/-- The minimizing segment is unique. -/
lemma firstSeg_unique (hn : 2 ≤ n) (i : Fin n) (A : ℝ × ℝ)
    (hA : A = (C.seg i).1 ∨ A = (C.seg i).2) (k : {j // i ≠ j})
    (hk : ∀ l : {j // i ≠ j}, dist A (C.xpoint i k k.2) ≤ dist A (C.xpoint i l l.2)) :
    k = C.firstSeg hn i A := by
  have h1 := C.firstSeg_spec hn i A k
  have h2 := hk (C.firstSeg hn i A)
  have hdist : dist A (C.xpoint i k k.2)
      = dist A (C.xpoint i (C.firstSeg hn i A) (C.firstSeg hn i A).2) :=
    le_antisymm h2 h1
  have heq : C.xpoint i k k.2
      = C.xpoint i (C.firstSeg hn i A) (C.firstSeg hn i A).2 :=
    C.dist_eq_of_mem_crossings hn hA (C.mem_crossings.mpr ⟨k, k.2, rfl⟩)
      (C.mem_crossings.mpr ⟨C.firstSeg hn i A, (C.firstSeg hn i A).2, rfl⟩) hdist
  by_contra hcon
  have hne : (k : Fin n) ≠ (C.firstSeg hn i A : Fin n) :=
    fun h => hcon (Subtype.ext h)
  exact C.xpoint_ne_of_ne k.2 (C.firstSeg hn i A).2 hne heq

/- The first crossing from an endpoint `A` is with the segment
`firstSeg`; note that the segment of the first crossing is in general
NOT the cyclic successor of `A` on the convex hull of the endpoints (the
arc between them can be long) — see the work-in-progress notes at the
end of the file. The cyclic order will instead come from the circle
model described there. -/

end SegConf

end Imo2016P6Geo

namespace Imo2016P6Geo

/-- If `A` lies in the segment `(a, a')` and `X` in the open segment, then
the open segment `(A, X)` is contained in the open segment `(a, a')`. -/
lemma openSegment_sub_openSegment {a a' A X : ℝ × ℝ}
    (hA : A ∈ segment ℝ a a') (hX : X ∈ openSegment ℝ a a') :
    openSegment ℝ A X ⊆ openSegment ℝ a a' := by
  rw [segment_eq_image] at hA
  obtain ⟨α, hα, hA2⟩ := hA
  obtain ⟨T, hT, hX2⟩ := mem_openSegment_iff_param.mp hX
  intro Y hY
  obtain ⟨r, hr, hY2⟩ := mem_openSegment_iff_param.mp hY
  rw [mem_openSegment_iff_param]
  have hA3 : A = a + α • (a' - a) := by
    have hA2' : (1 - α) • a + α • a' = A := hA2
    rw [← hA2']
    module
  refine ⟨(1 - r) * α + r * T, ⟨?_, ?_⟩, ?_⟩
  · have g1 : 0 ≤ (1 - r) * α := mul_nonneg (by linarith [hr.2]) hα.1
    have g2 : 0 < r * T := mul_pos hr.1 hT.1
    linarith [g1, g2]
  · have h1 : (1 - r) * α ≤ (1 - r) * 1 :=
      mul_le_mul_of_nonneg_left hα.2 (by linarith [hr.2])
    have h2 : r * T < r * 1 := mul_lt_mul_of_pos_left hT.2 hr.1
    nlinarith
  · rw [hY2, hA3, hX2]
    module

namespace SegConf

variable {n : ℕ} (C : SegConf n)

/-- Direction vector of segment `i`. -/
def dir (i : Fin n) : ℝ × ℝ := (C.seg i).2 - (C.seg i).1

/-- If `A` lies on the line of segment `i`, determinants against `dir i`
do not depend on the base point on that line. -/
lemma detv_dir_eq_of_mem {i : Fin n} {A p : ℝ × ℝ}
    (hA : detv (C.dir i) (A - (C.seg i).1) = 0) :
    detv (C.dir i) (p - A) = detv (C.dir i) (p - (C.seg i).1) := by
  have e : p - A = (p - (C.seg i).1) - (A - (C.seg i).1) := by abel
  rw [e, detv_sub_right, hA, sub_zero]

/-- The parameter on the line of segment `i` of a point `A` of
`segment ℝ (C.seg i).1 (C.seg i).2`, as a scalar of `C.dir i`. -/
lemma detv_dir_self_left {i : Fin n} {A : ℝ × ℝ}
    (hA : A ∈ segment ℝ (C.seg i).1 (C.seg i).2) :
    detv (C.dir i) (A - (C.seg i).1) = 0 := by
  rw [segment_eq_image] at hA
  obtain ⟨α, hα, hA2⟩ := hA
  have hA2' : (1 - α) • (C.seg i).1 + α • (C.seg i).2 = A := hA2
  have e : A - (C.seg i).1 = α • ((C.seg i).2 - (C.seg i).1) := by
    rw [← hA2']
    module
  have hdir : C.dir i = (C.seg i).2 - (C.seg i).1 := rfl
  rw [e, detv_smul_right, hdir, detv_self, mul_zero]

/-- `OppSide` is invariant under rescaling the direction by a nonzero
scalar. -/
lemma oppSide_smul_dir {c : ℝ} (hc : c ≠ 0) (A p q u : ℝ × ℝ) :
    OppSide A (c • u) p q ↔ OppSide A u p q := by
  have e : detv (c • u) (p - A) * detv (c • u) (q - A)
      = c ^ 2 * (detv u (p - A) * detv u (q - A)) := by
    rw [detv_smul_left, detv_smul_left]
    ring
  show detv (c • u) (p - A) * detv (c • u) (q - A) < 0 ↔
    detv u (p - A) * detv u (q - A) < 0
  rw [e]
  have hpos : 0 < c ^ 2 := sq_pos_of_ne_zero hc
  constructor
  · intro h
    by_contra hX
    push Not at hX
    exact absurd h (not_lt_of_ge (mul_nonneg hpos.le hX))
  · intro h
    exact mul_neg_of_pos_of_neg hpos h

/-- An endpoint of a segment and a point of its open segment differ. -/
lemma endpoint_ne_of_mem_openSegment (hn : 2 ≤ n) {i : Fin n} {A X : ℝ × ℝ}
    (hA : A = (C.seg i).1 ∨ A = (C.seg i).2)
    (hX : X ∈ openSegment ℝ (C.seg i).1 (C.seg i).2) :
    A ≠ X := by
  obtain ⟨T, hT, hX2⟩ := mem_openSegment_iff_param.mp hX
  have hne := C.endpoints_ne hn i
  intro heq
  rcases hA with rfl | rfl
  · have e : T • ((C.seg i).2 - (C.seg i).1) = 0 := by
      have h1 : (C.seg i).1 + T • ((C.seg i).2 - (C.seg i).1) = (C.seg i).1 := by
        rw [← hX2, heq]
      exact add_left_cancel (a := (C.seg i).1) (b := T • ((C.seg i).2 - (C.seg i).1))
        (c := 0) (by rw [add_zero]; exact h1)
    rw [smul_eq_zero] at e
    rcases e with e | e
    · exact hT.1.ne' e
    · exact hne (sub_eq_zero.mp e).symm
  · have e : (T - 1) • ((C.seg i).2 - (C.seg i).1) = 0 := by
      have h1 : (C.seg i).1 + T • ((C.seg i).2 - (C.seg i).1) = (C.seg i).2 := by
        rw [← hX2, heq]
      have h2 : (T - 1) • ((C.seg i).2 - (C.seg i).1)
          = (C.seg i).1 + T • ((C.seg i).2 - (C.seg i).1) - (C.seg i).2 := by
        rw [sub_smul, one_smul]
        module
      rw [h2, h1]
      module
    rw [smul_eq_zero] at e
    rcases e with e | e
    · have : T = 1 := by linarith [e]
      rw [this] at hT
      exact absurd hT.2 (lt_irrefl 1)
    · exact hne (sub_eq_zero.mp e).symm

/-- The direction from an endpoint of segment `i` to a point of its open
segment is a nonzero multiple of `C.dir i`. -/
lemma exists_smul_dir_sub_endpoint {i : Fin n} {A X : ℝ × ℝ}
    (hA : A = (C.seg i).1 ∨ A = (C.seg i).2)
    (hX : X ∈ openSegment ℝ (C.seg i).1 (C.seg i).2) :
    ∃ c : ℝ, c ≠ 0 ∧ X - A = c • (C.dir i) := by
  obtain ⟨T, hT, hX2⟩ := mem_openSegment_iff_param.mp hX
  have hdir : C.dir i = (C.seg i).2 - (C.seg i).1 := rfl
  rcases hA with rfl | rfl
  · refine ⟨T, hT.1.ne', ?_⟩
    rw [hdir]
    show X - (C.seg i).1 = T • ((C.seg i).2 - (C.seg i).1)
    rw [hX2]
    module
  · refine ⟨T - 1, by intro hcon; apply hT.2.ne; linarith [hcon], ?_⟩
    rw [hdir]
    show X - (C.seg i).2 = (T - 1) • ((C.seg i).2 - (C.seg i).1)
    rw [hX2]
    module

/-- Region-counting core, part 1: for a third segment `k`, its crossing
with segment `i` lies in the open segment `(A, X)` iff its endpoints see
`A` and `X` on opposite sides (`OppSide`). Here `A` is an endpoint of
segment `i` and `X` is a point of its open segment. -/
lemma xpoint_mem_openSegment_iff {i k : Fin n} (hik : i ≠ k)
    {A X : ℝ × ℝ}
    (hA : A = (C.seg i).1 ∨ A = (C.seg i).2)
    (hX : X ∈ openSegment ℝ (C.seg i).1 (C.seg i).2) :
    C.xpoint i k hik ∈ openSegment ℝ A X ↔
      OppSide (C.seg k).1 (C.dir k) A X := by
  have hd : detv (C.dir i) (C.dir k) ≠ 0 := C.dir_ne i k hik
  have hproper := C.xpoint_mem i k hik
  have hAseg : A ∈ segment ℝ (C.seg i).1 (C.seg i).2 := by
    rcases hA with rfl | rfl
    · exact left_mem_segment _ _ _
    · exact right_mem_segment _ _ _
  have hA0 : detv (C.dir i) (A - (C.seg i).1) = 0 := by
    rcases hA with rfl | rfl
    · rw [sub_self, detv_zero_right]
    · have hdir : C.dir i = (C.seg i).2 - (C.seg i).1 := rfl
      rw [hdir, detv_self]
  obtain ⟨c, hc, hce⟩ := C.exists_smul_dir_sub_endpoint hA hX
  have hdirX : detv (X - A) (C.dir k) ≠ 0 := by
    rw [hce, detv_smul_left]
    exact mul_ne_zero hc hd
  constructor
  · intro h
    have h1 : C.xpoint i k hik ∈ openSegment ℝ A X ∧ C.xpoint i k hik ∈
        openSegment ℝ (C.seg k).1 (C.seg k).2 := ⟨h, hproper.2⟩
    exact (oppSide_of_properCross h1 hdirX).2
  · intro hOpp
    have hOpp2 : OppSide A (C.dir i) (C.seg k).1 (C.seg k).2 := by
      have h1 := (oppSide_of_properCross hproper hd).1
      have e1 : detv (C.dir i) ((C.seg k).1 - A)
          = detv (C.dir i) ((C.seg k).1 - (C.seg i).1) :=
        C.detv_dir_eq_of_mem hA0
      have e2 : detv (C.dir i) ((C.seg k).2 - A)
          = detv (C.dir i) ((C.seg k).2 - (C.seg i).1) :=
        C.detv_dir_eq_of_mem hA0
      have h1c : detv (C.dir i) ((C.seg k).1 - A) * detv (C.dir i) ((C.seg k).2 - A) < 0 := by
        rw [e1, e2]
        exact h1
      exact h1c
    have hOpp2' : OppSide A (X - A) (C.seg k).1 (C.seg k).2 := by
      rw [hce, oppSide_smul_dir hc]
      exact hOpp2
    obtain ⟨Y, hY1, hY2⟩ := properCross_of_oppSide hOpp2' hOpp
    have hY3 : Y ∈ openSegment ℝ (C.seg i).1 (C.seg i).2 :=
      openSegment_sub_openSegment hAseg hX hY1
    have hY4 : Y = C.xpoint i k hik :=
      C.xpoint_unique i k hik ⟨hY3, hY2⟩
    rw [hY4] at hY1
    exact hY1

end SegConf

end Imo2016P6Geo

namespace Imo2016P6Geo

/-- Pure sign dichotomy: with `S ≠ 0`, if `A * B < 0` the products
`A * S`, `B * S` have opposite signs, and if `0 < A * B` they have the
same sign. -/
lemma sign_xor_of_mul_neg {A B S : ℝ} (h : A * B < 0) (hS : S ≠ 0) :
    (A * S < 0 ↔ 0 < B * S) ∧ (0 < A * S ↔ B * S < 0) := by
  rcases mul_neg_iff.mp h with ⟨g1, g2⟩ | ⟨g1, g2⟩ <;>
    rcases lt_or_gt_of_ne hS with hS' | hS' <;>
    constructor <;> constructor <;> intro h1 <;> nlinarith

lemma sign_same_of_mul_pos {A B S : ℝ} (h : 0 < A * B) (hS : S ≠ 0) :
    (A * S < 0 ↔ B * S < 0) ∧ (0 < A * S ↔ 0 < B * S) := by
  rcases mul_pos_iff.mp h with ⟨g1, g2⟩ | ⟨g1, g2⟩ <;>
    rcases lt_or_gt_of_ne hS with hS' | hS' <;>
    constructor <;> constructor <;> intro h1 <;> nlinarith

/-- Uniqueness of the intersection point of two non-parallel lines. -/
lemma eq_of_detv_eq_zero_of_detv_eq_zero {u w : ℝ × ℝ} (huw : detv u w ≠ 0)
    {a p X Y : ℝ × ℝ} (h1 : detv u (X - a) = 0) (h2 : detv u (Y - a) = 0)
    (h3 : detv w (X - p) = 0) (h4 : detv w (Y - p) = 0) : X = Y := by
  have hu : u ≠ 0 := by
    intro hzero
    rw [hzero, detv_zero_left] at huw
    exact huw rfl
  have hd1 : detv u (X - Y) = 0 := by
    have e : X - Y = (X - a) - (Y - a) := by abel
    rw [e, detv_sub_right, h1, h2, sub_zero]
  obtain ⟨α, hα⟩ := exists_smul_of_detv_eq_zero hu hd1
  have hd2 : detv w (X - Y) = 0 := by
    have e : X - Y = (X - p) - (Y - p) := by abel
    rw [e, detv_sub_right, h3, h4, sub_zero]
  rw [hα, detv_smul_right] at hd2
  have hw : detv w u ≠ 0 := by
    rw [detv_antisymm]
    exact neg_ne_zero.mpr huw
  have hα0 : α = 0 := by
    rcases mul_eq_zero.mp hd2 with g | g
    · exact g
    · exact absurd g hw
  rw [hα0, zero_smul] at hα
  exact sub_eq_zero.mp hα

namespace SegConf

variable {n : ℕ} (C : SegConf n)

/-- The crossing point of segments `i` and `j` does not lie on the line of
a third segment `k` (otherwise the three segments would concur). -/
lemma detv_dir_xpoint_ne_zero {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    detv (C.dir k) (C.xpoint i j hij - (C.seg k).1) ≠ 0 := by
  intro hd
  have huw : detv (C.dir i) (C.dir k) ≠ 0 := C.dir_ne i k hik
  have h1 := C.detv_dir_self_left
    (openSegment_subset_segment _ _ _ (C.xpoint_mem i j hij).1)
  have h2 := C.detv_dir_self_left
    (openSegment_subset_segment _ _ _ (C.xpoint_mem i k hik).1)
  have h4 := C.detv_dir_self_left
    (openSegment_subset_segment _ _ _ (C.xpoint_mem i k hik).2)
  have heq : C.xpoint i j hij = C.xpoint i k hik :=
    eq_of_detv_eq_zero_of_detv_eq_zero huw h1 h2 hd h4
  exact C.noconcur i j k hij hjk hik
    ⟨C.xpoint i j hij,
      openSegment_subset_segment _ _ _ (C.xpoint_mem i j hij).1,
      openSegment_subset_segment _ _ _ (C.xpoint_mem i j hij).2,
      heq ▸ openSegment_subset_segment _ _ _ (C.xpoint_mem i k hik).2⟩

/-- Euclidean norm squared on `ℝ × ℝ` (Mathlib's product norm on `ℝ × ℝ`
is the sup norm, so we define our own; used for the circle model). -/
def nsq (v : ℝ × ℝ) : ℝ := v.1 ^ 2 + v.2 ^ 2

/-- The dot product on `ℝ × ℝ`. -/
def dotv (u v : ℝ × ℝ) : ℝ := u.1 * v.1 + u.2 * v.2

lemma nsq_def (v : ℝ × ℝ) : nsq v = v.1 ^ 2 + v.2 ^ 2 := rfl
lemma dotv_def (u v : ℝ × ℝ) : dotv u v = u.1 * v.1 + u.2 * v.2 := rfl

lemma nsq_nonneg (v : ℝ × ℝ) : 0 ≤ nsq v := by
  show 0 ≤ v.1 ^ 2 + v.2 ^ 2
  positivity

lemma nsq_pos_of_ne {v : ℝ × ℝ} (hv : v ≠ 0) : 0 < nsq v := by
  have hu' : v.1 ≠ 0 ∨ v.2 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hv (Prod.ext hcon.1 hcon.2)
  show 0 < v.1 ^ 2 + v.2 ^ 2
  rcases hu' with h | h <;> positivity

lemma nsq_eq_zero_iff {v : ℝ × ℝ} : nsq v = 0 ↔ v = 0 := by
  constructor
  · intro h
    have h' : v.1 ^ 2 + v.2 ^ 2 = 0 := h
    have h1 : v.1 ^ 2 = 0 := by linarith [sq_nonneg v.1, sq_nonneg v.2]
    have h2 : v.2 ^ 2 = 0 := by linarith [sq_nonneg v.1, sq_nonneg v.2]
    exact Prod.ext (sq_eq_zero_iff.mp h1) (sq_eq_zero_iff.mp h2)
  · intro h
    rw [h]
    show (0 : ℝ) ^ 2 + (0 : ℝ) ^ 2 = 0
    ring

lemma dotv_add_left (u v w : ℝ × ℝ) : dotv (u + w) v = dotv u v + dotv w v := by
  show (u.1 + w.1) * v.1 + (u.2 + w.2) * v.2
    = u.1 * v.1 + u.2 * v.2 + (w.1 * v.1 + w.2 * v.2)
  ring

lemma dotv_smul_left (c : ℝ) (u v : ℝ × ℝ) : dotv (c • u) v = c * dotv u v := by
  show c * u.1 * v.1 + c * u.2 * v.2 = c * (u.1 * v.1 + u.2 * v.2)
  ring

lemma dotv_comm (u v : ℝ × ℝ) : dotv u v = dotv v u := by
  show u.1 * v.1 + u.2 * v.2 = v.1 * u.1 + v.2 * u.2
  ring

lemma dotv_sub_right (u v w : ℝ × ℝ) : dotv u (v - w) = dotv u v - dotv u w := by
  show u.1 * (v.1 - w.1) + u.2 * (v.2 - w.2)
    = u.1 * v.1 + u.2 * v.2 - (u.1 * w.1 + u.2 * w.2)
  ring

lemma dotv_self (u : ℝ × ℝ) : dotv u u = nsq u := by
  show u.1 * u.1 + u.2 * u.2 = u.1 ^ 2 + u.2 ^ 2
  ring

lemma nsq_sub (u v : ℝ × ℝ) : nsq (u - v) = nsq u - 2 * dotv u v + nsq v := by
  show (u.1 - v.1) ^ 2 + (u.2 - v.2) ^ 2
    = u.1 ^ 2 + u.2 ^ 2 - 2 * (u.1 * v.1 + u.2 * v.2) + (v.1 ^ 2 + v.2 ^ 2)
  ring

lemma nsq_smul (c : ℝ) (v : ℝ × ℝ) : nsq (c • v) = c ^ 2 * nsq v := by
  show (c * v.1) ^ 2 + (c * v.2) ^ 2 = c ^ 2 * (v.1 ^ 2 + v.2 ^ 2)
  ring

lemma nsq_add_smul (A u : ℝ × ℝ) (t : ℝ) :
    nsq (A + t • u) = nsq A + 2 * t * dotv A u + t ^ 2 * nsq u := by
  show (A.1 + t * u.1) ^ 2 + (A.2 + t * u.2) ^ 2
    = A.1 ^ 2 + A.2 ^ 2 + 2 * t * (A.1 * u.1 + A.2 * u.2) + t ^ 2 * (u.1 ^ 2 + u.2 ^ 2)
  ring

/-- The Lagrange identity relating `detv`, `dotv` and `nsq`. -/
lemma detv_sq_eq (u A : ℝ × ℝ) : detv u A ^ 2 = nsq u * nsq A - dotv u A ^ 2 := by
  show (u.1 * A.2 - u.2 * A.1) ^ 2
    = (u.1 ^ 2 + u.2 ^ 2) * (A.1 ^ 2 + A.2 ^ 2) - (u.1 * A.1 + u.2 * A.2) ^ 2
  ring

/-- The discriminant of the quadratic `t ↦ nsq (A + t • u) - r ^ 2`, in
factored form: `4 * (nsq u * r ^ 2 - detv u A ^ 2)`. -/
lemma quadratic_disc_factor (A u : ℝ × ℝ) (r : ℝ) :
    (2 * dotv A u) ^ 2 - 4 * nsq u * (nsq A - r ^ 2)
      = 4 * (nsq u * r ^ 2 - detv u A ^ 2) := by
  rw [detv_sq_eq, dotv_comm u A]
  ring

/-- A root computation: the two parameters where a line meets a circle. -/
lemma quadratic_roots (A u : ℝ × ℝ) (r : ℝ) (hu : u ≠ 0)
    (hΔ : detv u A ^ 2 < nsq u * r ^ 2) :
    ∃ t1 t2 : ℝ, t1 < t2 ∧ nsq (A + t1 • u) = r ^ 2 ∧ nsq (A + t2 • u) = r ^ 2 ∧
      (∀ t : ℝ, nsq (A + t • u) ≤ r ^ 2 ↔ t1 ≤ t ∧ t ≤ t2) ∧
      (∀ t : ℝ, nsq (A + t • u) < r ^ 2 ↔ t1 < t ∧ t < t2) := by
  set a := nsq u with ha
  set b := 2 * dotv A u with hb
  set c := nsq A - r ^ 2 with hc
  have hapos : 0 < a := nsq_pos_of_ne hu
  have hane : a ≠ 0 := hapos.ne'
  have hΔval : b ^ 2 - 4 * a * c = 4 * (nsq u * r ^ 2 - detv u A ^ 2) := by
    rw [hb, hc, ha, quadratic_disc_factor]
  have hΔpos : 0 < b ^ 2 - 4 * a * c := by
    rw [hΔval]
    have h2 : 0 < nsq u * r ^ 2 - detv u A ^ 2 := by linarith
    linarith
  have hΔnn : 0 ≤ b ^ 2 - 4 * a * c := hΔpos.le
  set s := Real.sqrt (b ^ 2 - 4 * a * c) with hs
  have hss : s ^ 2 = b ^ 2 - 4 * a * c := Real.sq_sqrt hΔnn
  have hs0 : 0 < s := Real.sqrt_pos_of_pos hΔpos
  refine ⟨(-b - s) / (2 * a), (-b + s) / (2 * a), ?_, ?_, ?_, ?_, ?_⟩
  · have h2a : 0 < 2 * a := by linarith
    have : -b - s < -b + s := by linarith
    exact (div_lt_div_iff_of_pos_right h2a).mpr this
  · have hquad : ∀ t : ℝ, nsq (A + t • u) - r ^ 2 = a * t ^ 2 + b * t + c := by
      intro t
      rw [nsq_add_smul]
      ring
    have hz : a * ((-b - s) / (2 * a)) ^ 2 + b * ((-b - s) / (2 * a)) + c = 0 := by
      field_simp
      nlinarith [hss]
    have e := hquad ((-b - s) / (2 * a))
    linarith [hz]
  · have hquad : ∀ t : ℝ, nsq (A + t • u) - r ^ 2 = a * t ^ 2 + b * t + c := by
      intro t
      rw [nsq_add_smul]
      ring
    have hz : a * ((-b + s) / (2 * a)) ^ 2 + b * ((-b + s) / (2 * a)) + c = 0 := by
      field_simp
      nlinarith [hss]
    have e := hquad ((-b + s) / (2 * a))
    linarith [hz]
  · intro t
    have hlt : (-b - s) / (2 * a) < (-b + s) / (2 * a) := by
      have h2a : 0 < 2 * a := by linarith
      have hbs : -b - s < -b + s := by linarith
      exact (div_lt_div_iff_of_pos_right h2a).mpr hbs
    have hquad : nsq (A + t • u) - r ^ 2 = a * (t - (-b - s) / (2 * a)) * (t - (-b + s) / (2 * a)) := by
      rw [nsq_add_smul]
      field_simp
      nlinarith [hss]
    rw [← sub_nonpos, hquad]
    have hsign : a * (t - (-b - s) / (2 * a)) * (t - (-b + s) / (2 * a)) ≤ 0 ↔
        (t - (-b - s) / (2 * a)) * (t - (-b + s) / (2 * a)) ≤ 0 := by
      constructor
      · intro h
        by_contra hP
        push Not at hP
        have h2 : 0 < a * ((t - (-b - s) / (2 * a)) * (t - (-b + s) / (2 * a))) :=
          mul_pos hapos hP
        rw [← mul_assoc] at h2
        exact not_lt_of_ge h h2
      · intro h
        rw [mul_assoc]
        exact mul_nonpos_of_nonneg_of_nonpos hapos.le h
    rw [hsign]
    constructor
    · intro h
      rcases mul_nonpos_iff.mp h with g | g
      · exact ⟨by linarith [g.1], by linarith [g.2]⟩
      · exfalso
        nlinarith [hlt]
    · rintro ⟨g1, g2⟩
      exact mul_nonpos_of_nonneg_of_nonpos (by linarith [g1]) (by linarith [g2])
  · intro t
    have hlt : (-b - s) / (2 * a) < (-b + s) / (2 * a) := by
      have h2a : 0 < 2 * a := by linarith
      have hbs : -b - s < -b + s := by linarith
      exact (div_lt_div_iff_of_pos_right h2a).mpr hbs
    have hquad : nsq (A + t • u) - r ^ 2 = a * (t - (-b - s) / (2 * a)) * (t - (-b + s) / (2 * a)) := by
      rw [nsq_add_smul]
      field_simp
      nlinarith [hss]
    rw [← sub_neg, hquad]
    have hsign : a * (t - (-b - s) / (2 * a)) * (t - (-b + s) / (2 * a)) < 0 ↔
        (t - (-b - s) / (2 * a)) * (t - (-b + s) / (2 * a)) < 0 := by
      constructor
      · intro h
        by_contra hP
        push Not at hP
        have h2 : 0 ≤ a * ((t - (-b - s) / (2 * a)) * (t - (-b + s) / (2 * a))) :=
          mul_nonneg hapos.le hP
        rw [← mul_assoc] at h2
        exact absurd h (not_lt_of_ge h2)
      · intro h
        rw [mul_assoc]
        exact mul_neg_of_pos_of_neg hapos h
    rw [hsign]
    constructor
    · intro h
      rcases mul_neg_iff.mp h with g | g
      · exact ⟨by linarith [g.1], by linarith [g.2]⟩
      · exfalso
        nlinarith [hlt]
    · rintro ⟨g1, g2⟩
      exact mul_neg_of_pos_of_neg (by linarith [g1]) (by linarith [g2])

/-- The crossing point of segments `i` and `j` if they differ,
and `(0, 0)` otherwise (a total function used to define the radius). -/
noncomputable def nxpoint (i j : Fin n) : ℝ × ℝ :=
  if h : i ≠ j then C.xpoint i j h else 0

lemma nxpoint_eq (i j : Fin n) (h : i ≠ j) : C.nxpoint i j = C.xpoint i j h := by
  rw [nxpoint, dif_pos h]

/-- A radius strictly larger than the Euclidean norm of every crossing
point of the configuration. -/
noncomputable def radius (C : SegConf n) : ℝ :=
  1 + ∑ i : Fin n, ∑ j : Fin n, Real.sqrt (nsq (C.nxpoint i j))

lemma radius_pos (C : SegConf n) : 0 < C.radius := by
  rw [radius]
  have hsum : 0 ≤ ∑ i : Fin n, ∑ j : Fin n, Real.sqrt (nsq (C.nxpoint i j)) :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => Real.sqrt_nonneg _
  linarith

lemma xpoint_sqrt_nsq_lt_radius (i j : Fin n) (h : i ≠ j) :
    Real.sqrt (nsq (C.xpoint i j h)) < C.radius := by
  have hle1 : (∑ j' : Fin n, Real.sqrt (nsq (C.nxpoint i j')))
      ≤ ∑ i' : Fin n, ∑ j' : Fin n, Real.sqrt (nsq (C.nxpoint i' j')) := by
    apply Finset.single_le_sum (f := fun i' : Fin n =>
      ∑ j' : Fin n, Real.sqrt (nsq (C.nxpoint i' j')))
    · intro i' _
      exact Finset.sum_nonneg fun j' _ => Real.sqrt_nonneg _
    · exact Finset.mem_univ i
  have hle2 : Real.sqrt (nsq (C.nxpoint i j))
      ≤ ∑ j' : Fin n, Real.sqrt (nsq (C.nxpoint i j')) := by
    apply Finset.single_le_sum (f := fun j' : Fin n => Real.sqrt (nsq (C.nxpoint i j')))
    · intro j' _
      exact Real.sqrt_nonneg _
    · exact Finset.mem_univ j
  rw [radius, ← C.nxpoint_eq i j h]
  linarith [hle1, hle2]

lemma xpoint_nsq_lt_radius_sq (i j : Fin n) (h : i ≠ j) :
    nsq (C.xpoint i j h) < C.radius ^ 2 := by
  have h1 := C.xpoint_sqrt_nsq_lt_radius i j h
  have hr := C.radius_pos
  have h2 : (Real.sqrt (nsq (C.xpoint i j h))) ^ 2 < C.radius ^ 2 := by
    rw [sq_lt_sq, abs_of_nonneg (Real.sqrt_nonneg _), abs_of_pos hr]
    exact h1
  rwa [Real.sq_sqrt (nsq_nonneg _)] at h2

lemma dir_ne_of (hn : 2 ≤ n) (i : Fin n) : C.dir i ≠ 0 := by
  obtain ⟨j, hj⟩ := Fintype.exists_ne_of_one_lt_card (α := Fin n) (by
    rw [Fintype.card_fin]; omega) i
  have hd := C.dir_ne i j hj.symm
  intro hzero
  have hdir : C.dir i = (C.seg i).2 - (C.seg i).1 := rfl
  rw [hdir] at hzero
  rw [hzero, detv_zero_left] at hd
  exact hd rfl

/-- The Euclidean distance from the origin to the line of segment `i` is
strictly less than the radius (the line passes through a crossing point,
which lies strictly inside the circle). -/
lemma detv_dir_sq_lt (hn : 2 ≤ n) (i : Fin n) :
    detv (C.dir i) ((C.seg i).1) ^ 2 < nsq (C.dir i) * C.radius ^ 2 := by
  obtain ⟨j, hj⟩ := Fintype.exists_ne_of_one_lt_card (α := Fin n) (by
    rw [Fintype.card_fin]; omega) i
  have hu := C.dir_ne_of hn i
  have hdet : detv (C.dir i) (C.seg i).1 = detv (C.dir i) (C.xpoint i j hj.symm) := by
    have h0 : detv (C.dir i) (C.xpoint i j hj.symm - (C.seg i).1) = 0 :=
      C.detv_dir_self_left (openSegment_subset_segment _ _ _ (C.xpoint_mem i j hj.symm).1)
    have e : detv (C.dir i) (C.xpoint i j hj.symm) - detv (C.dir i) (C.seg i).1
        = detv (C.dir i) (C.xpoint i j hj.symm - (C.seg i).1) := by
      rw [← detv_sub_right]
    linarith [e, h0]
  rw [hdet, detv_sq_eq]
  have hn2 : 0 < nsq (C.dir i) := nsq_pos_of_ne hu
  have hx : nsq (C.dir i) * nsq (C.xpoint i j hj.symm) < nsq (C.dir i) * C.radius ^ 2 :=
    mul_lt_mul_of_pos_left (C.xpoint_nsq_lt_radius_sq i j hj.symm) hn2
  have hdot : 0 ≤ dotv (C.dir i) (C.xpoint i j hj.symm) ^ 2 := sq_nonneg _
  linarith [hx, hdot]

/-- The parameters of the two circle points of segment `i`. -/
noncomputable def circleParams (hn : 2 ≤ n) (i : Fin n) : ℝ × ℝ :=
  let h := quadratic_roots ((C.seg i).1) (C.dir i) C.radius
    (C.dir_ne_of hn i) (C.detv_dir_sq_lt hn i)
  ⟨h.choose, h.choose_spec.choose⟩

lemma circleParams_spec (hn : 2 ≤ n) (i : Fin n) :
    (C.circleParams hn i).1 < (C.circleParams hn i).2 ∧
    nsq ((C.seg i).1 + (C.circleParams hn i).1 • C.dir i) = C.radius ^ 2 ∧
    nsq ((C.seg i).1 + (C.circleParams hn i).2 • C.dir i) = C.radius ^ 2 ∧
    (∀ t : ℝ, nsq ((C.seg i).1 + t • C.dir i) ≤ C.radius ^ 2 ↔
      (C.circleParams hn i).1 ≤ t ∧ t ≤ (C.circleParams hn i).2) ∧
    (∀ t : ℝ, nsq ((C.seg i).1 + t • C.dir i) < C.radius ^ 2 ↔
      (C.circleParams hn i).1 < t ∧ t < (C.circleParams hn i).2) := by
  have h := quadratic_roots ((C.seg i).1) (C.dir i) C.radius
    (C.dir_ne_of hn i) (C.detv_dir_sq_lt hn i)
  exact h.choose_spec.choose_spec

/-- The two points where the line of segment `i` meets the circle of
radius `C.radius` around the origin: the smaller and larger parameter
points along the direction of the segment. -/
noncomputable def circlePts (hn : 2 ≤ n) (i : Fin n) : (ℝ × ℝ) × (ℝ × ℝ) :=
  ((C.seg i).1 + (C.circleParams hn i).1 • C.dir i,
    (C.seg i).1 + (C.circleParams hn i).2 • C.dir i)

lemma circlePts_fst_eq (hn : 2 ≤ n) (i : Fin n) :
    (C.circlePts hn i).1 = (C.seg i).1 + (C.circleParams hn i).1 • C.dir i := rfl

lemma circlePts_snd_eq (hn : 2 ≤ n) (i : Fin n) :
    (C.circlePts hn i).2 = (C.seg i).1 + (C.circleParams hn i).2 • C.dir i := rfl

lemma circlePts_fst_nsq (hn : 2 ≤ n) (i : Fin n) :
    nsq (C.circlePts hn i).1 = C.radius ^ 2 := (C.circleParams_spec hn i).2.1

lemma circlePts_snd_nsq (hn : 2 ≤ n) (i : Fin n) :
    nsq (C.circlePts hn i).2 = C.radius ^ 2 := (C.circleParams_spec hn i).2.2.1

lemma circleParams_lt (hn : 2 ≤ n) (i : Fin n) :
    (C.circleParams hn i).1 < (C.circleParams hn i).2 := (C.circleParams_spec hn i).1

lemma circlePts_ne (hn : 2 ≤ n) (i : Fin n) :
    (C.circlePts hn i).1 ≠ (C.circlePts hn i).2 := by
  intro heq
  have hlt := C.circleParams_lt hn i
  have hu := C.dir_ne_of hn i
  have e : ((C.circleParams hn i).2 - (C.circleParams hn i).1) • C.dir i = 0 := by
    have h1 : (C.seg i).1 + (C.circleParams hn i).1 • C.dir i
        = (C.seg i).1 + (C.circleParams hn i).2 • C.dir i := heq
    have h2 := add_left_cancel h1
    have h3 : ((C.circleParams hn i).2 - (C.circleParams hn i).1) • C.dir i
        = (C.circleParams hn i).2 • C.dir i - (C.circleParams hn i).1 • C.dir i := by
      rw [sub_smul]
    rw [h3, ← h2, sub_self]
  rw [smul_eq_zero] at e
  rcases e with e | e
  · linarith
  · exact hu e

/-- A crossing point lies strictly between the two circle points of its
segment's line (in the line's parametrization). -/
lemma xpoint_param_mem (hn : 2 ≤ n) (i j : Fin n) (h : i ≠ j) :
    ∃ t : ℝ, t ∈ Set.Ioo (C.circleParams hn i).1 (C.circleParams hn i).2 ∧
      C.xpoint i j h = (C.seg i).1 + t • C.dir i := by
  obtain ⟨t, ht, hXt⟩ := mem_openSegment_iff_param.mp (C.xpoint_mem i j h).1
  have hdir : C.dir i = (C.seg i).2 - (C.seg i).1 := rfl
  rw [← hdir] at hXt
  refine ⟨t, ?_, hXt⟩
  have hnsq : nsq (C.xpoint i j h) < C.radius ^ 2 := C.xpoint_nsq_lt_radius_sq i j h
  have hspec := (C.circleParams_spec hn i).2.2.2.2 t
  rw [← hXt] at hspec
  exact hspec.mp hnsq

/-- The circle endpoint corresponding to an original endpoint:
`(i, false)` is the smaller-parameter circle point of segment `i` (on
the `(seg i).1` side), `(i, true)` the larger one (on the `(seg i).2`
side). -/
noncomputable def circlePt (hn : 2 ≤ n) (e : Fin n × Bool) : ℝ × ℝ :=
  if e.2 then (C.circlePts hn e.1).2 else (C.circlePts hn e.1).1

lemma circlePt_nsq (hn : 2 ≤ n) (e : Fin n × Bool) :
    nsq (C.circlePt hn e) = C.radius ^ 2 := by
  rw [circlePt]
  cases e.2 with
  | false => exact C.circlePts_fst_nsq hn e.1
  | true => exact C.circlePts_snd_nsq hn e.1

lemma circlePt_on_line (hn : 2 ≤ n) (e : Fin n × Bool) :
    detv (C.dir e.1) (C.circlePt hn e - (C.seg e.1).1) = 0 := by
  rw [circlePt]
  cases e.2 with
  | false =>
    rw [if_neg (show ¬(false = true) from by simp)]
    rw [circlePts_fst_eq]
    have e2 : (C.seg e.1).1 + (C.circleParams hn e.1).1 • C.dir e.1 - (C.seg e.1).1
        = (C.circleParams hn e.1).1 • C.dir e.1 := by abel
    rw [e2, detv_smul_right, detv_self, mul_zero]
  | true =>
    rw [if_pos rfl]
    rw [circlePts_snd_eq]
    have e2 : (C.seg e.1).1 + (C.circleParams hn e.1).2 • C.dir e.1 - (C.seg e.1).1
        = (C.circleParams hn e.1).2 • C.dir e.1 := by abel
    rw [e2, detv_smul_right, detv_self, mul_zero]

/-- Two circle endpoints coming from different segments or different
sides are distinct. -/
lemma circlePt_injective (hn : 2 ≤ n) : Function.Injective (C.circlePt hn) := by
  intro ⟨i, a⟩ ⟨j, b⟩ heq
  by_cases hij : i = j
  · subst hij
    -- same segment: different sides give different points
    rw [circlePt, circlePt] at heq
    have hne := C.circlePts_ne hn i
    cases a <;> cases b <;> simp_all
  · -- points on both lines, hence equal to the crossing, which is inside
    exfalso
    have h1 := C.circlePt_on_line hn ⟨i, a⟩
    have h2 := C.circlePt_on_line hn ⟨j, b⟩
    rw [← heq] at h2
    have h3 := C.detv_dir_self_left (openSegment_subset_segment _ _ _ (C.xpoint_mem i j hij).1)
    have h4 := C.detv_dir_self_left (openSegment_subset_segment _ _ _ (C.xpoint_mem i j hij).2)
    have huw : detv (C.dir i) (C.dir j) ≠ 0 := C.dir_ne i j hij
    have heq2 : C.circlePt hn ⟨i, a⟩ = C.xpoint i j hij :=
      eq_of_detv_eq_zero_of_detv_eq_zero huw h1 h3 h2 h4
    have hnsq := C.circlePt_nsq hn ⟨i, a⟩
    have hlt : nsq (C.xpoint i j hij) < C.radius ^ 2 := C.xpoint_nsq_lt_radius_sq i j hij
    rw [heq2] at hnsq
    rw [hnsq] at hlt
    exact (lt_irrefl _) hlt

/-- The parameter of a point of the line of segment `i` is unique. -/
lemma eq_of_smul_eq_smul_of_param {i : Fin n} {A : ℝ × ℝ} {s t : ℝ}
    (hu : C.dir i ≠ 0) (h : A + s • C.dir i = A + t • C.dir i) : s = t := by
  have h2 := add_left_cancel h
  have e : (s - t) • C.dir i = 0 := by
    have h3 : s • C.dir i - t • C.dir i = 0 := by rw [h2]; abel
    rwa [← sub_smul] at h3
  rcases smul_eq_zero.mp e with g | g
  · linarith
  · exact absurd g hu

/-- No crossing lies in the open segment from `(seg i).1` to the
smaller-parameter circle point of segment `i`. -/
lemma no_xpoint_openSegment_circlePt_fst (hn : 2 ≤ n) (i : Fin n) :
    ∀ j (h : i ≠ j), C.xpoint i j h ∉ openSegment ℝ (C.seg i).1 (C.circlePts hn i).1 := by
  intro j h hx
  have hu := C.dir_ne_of hn i
  obtain ⟨tX, htX, hXtX⟩ := C.xpoint_param_mem hn i j h
  have htX01 : tX ∈ Set.Ioo (0 : ℝ) 1 := by
    obtain ⟨t2, ht2, hXt2⟩ := mem_openSegment_iff_param.mp (C.xpoint_mem i j h).1
    have hdir : C.dir i = (C.seg i).2 - (C.seg i).1 := rfl
    rw [← hdir] at hXt2
    have h2 : tX = t2 := C.eq_of_smul_eq_smul_of_param hu (hXtX.symm.trans hXt2)
    rw [h2]
    exact ht2
  rw [circlePts_fst_eq] at hx
  obtain ⟨s, hs, hYs⟩ := mem_openSegment_iff_param.mp hx
  have e2 : (C.seg i).1 + (C.circleParams hn i).1 • C.dir i - (C.seg i).1
      = (C.circleParams hn i).1 • C.dir i := by abel
  rw [e2, smul_smul] at hYs
  have hts : tX = s * (C.circleParams hn i).1 :=
    C.eq_of_smul_eq_smul_of_param hu (hXtX.symm.trans hYs)
  by_cases htn : (C.circleParams hn i).1 ≤ 0
  · have h2 : s * (C.circleParams hn i).1 ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hs.1.le htn
    rw [← hts] at h2
    linarith [htX01.1]
  · push Not at htn
    have h1 : 0 < (C.circleParams hn i).1 * (1 - s) :=
      mul_pos htn (by linarith [hs.2])
    have h2 : s * (C.circleParams hn i).1 < (C.circleParams hn i).1 := by nlinarith
    rw [← hts] at h2
    linarith [htX.1]

/-- No crossing lies in the open segment from `(seg i).2` to the
larger-parameter circle point of segment `i`. -/
lemma no_xpoint_openSegment_circlePt_snd (hn : 2 ≤ n) (i : Fin n) :
    ∀ j (h : i ≠ j), C.xpoint i j h ∉ openSegment ℝ (C.seg i).2 (C.circlePts hn i).2 := by
  intro j h hx
  have hu := C.dir_ne_of hn i
  obtain ⟨tX, htX, hXtX⟩ := C.xpoint_param_mem hn i j h
  have htX01 : tX ∈ Set.Ioo (0 : ℝ) 1 := by
    obtain ⟨t2, ht2, hXt2⟩ := mem_openSegment_iff_param.mp (C.xpoint_mem i j h).1
    have hdir : C.dir i = (C.seg i).2 - (C.seg i).1 := rfl
    rw [← hdir] at hXt2
    have h2 : tX = t2 := C.eq_of_smul_eq_smul_of_param hu (hXtX.symm.trans hXt2)
    rw [h2]
    exact ht2
  rw [circlePts_snd_eq] at hx
  obtain ⟨s, hs, hYs⟩ := mem_openSegment_iff_param.mp hx
  have e2 : (C.seg i).1 + (C.circleParams hn i).2 • C.dir i - (C.seg i).2
      = ((C.circleParams hn i).2 - 1) • C.dir i := by
    have hdir : C.dir i = (C.seg i).2 - (C.seg i).1 := rfl
    rw [hdir]
    show (C.seg i).1 + (C.circleParams hn i).2 • ((C.seg i).2 - (C.seg i).1) - (C.seg i).2
      = ((C.circleParams hn i).2 - 1) • ((C.seg i).2 - (C.seg i).1)
    module
  rw [e2, smul_smul] at hYs
  -- Y = (seg i).2 + s • (Z₊ - (seg i).2) = (seg i).1 + (1 + s * (t₊ - 1)) • u
  have e3 : (C.seg i).2 + (s * ((C.circleParams hn i).2 - 1)) • C.dir i
      = (C.seg i).1 + (1 + s * ((C.circleParams hn i).2 - 1)) • C.dir i := by
    have hdir : C.dir i = (C.seg i).2 - (C.seg i).1 := rfl
    rw [hdir]
    show (C.seg i).2 + (s * ((C.circleParams hn i).2 - 1)) • ((C.seg i).2 - (C.seg i).1)
      = (C.seg i).1 + (1 + s * ((C.circleParams hn i).2 - 1)) • ((C.seg i).2 - (C.seg i).1)
    module
  rw [e3] at hYs
  have hts : tX = 1 + s * ((C.circleParams hn i).2 - 1) :=
    C.eq_of_smul_eq_smul_of_param hu (hXtX.symm.trans hYs)
  by_cases htn : 1 ≤ (C.circleParams hn i).2
  · have h2 : (1 : ℝ) ≤ tX := by
      rw [hts]
      nlinarith [htn, hs.1]
    linarith [htX01.2]
  · push Not at htn
    have h2 : (C.circleParams hn i).2 < tX := by
      rw [hts]
      nlinarith [hs.1, hs.2, htn]
    linarith [htX.2]

/-- The arrival time of a frog starting at point `P` at the crossing of
segment `i` with segment `k`: one plus the number of crossings on
segment `i` strictly closer to `P` than the crossing with `k`. -/
noncomputable def arrival (i k : Fin n) (hk : i ≠ k) (P : ℝ × ℝ) : ℕ :=
  ((C.crossings i).filter fun Y => dist P Y < dist P (C.xpoint i k hk)).card + 1

/-- Distance from a point of the line of segment `i` to another point of
the same line, in terms of the parameters. -/
lemma dist_along_dir (i : Fin n) {P : ℝ × ℝ} {tP : ℝ}
    (hP : P = (C.seg i).1 + tP • C.dir i) {Y : ℝ × ℝ} {t : ℝ}
    (hY : Y = (C.seg i).1 + t • C.dir i) :
    dist P Y = |t - tP| * ‖C.dir i‖ := by
  rw [hP, hY, dist_eq_norm]
  have e : ((C.seg i).1 + tP • C.dir i) - ((C.seg i).1 + t • C.dir i) = (tP - t) • C.dir i := by
    module
  rw [e, norm_smul, Real.norm_eq_abs, abs_sub_comm]

/-- The parameter of a crossing on segment `i`, in `(0, 1)` and in the
circle-parameter interval. -/
lemma xpoint_param (hn : 2 ≤ n) (i j : Fin n) (h : i ≠ j) :
    ∃ t : ℝ, t ∈ Set.Ioo (0 : ℝ) 1 ∧
      t ∈ Set.Ioo (C.circleParams hn i).1 (C.circleParams hn i).2 ∧
      C.xpoint i j h = (C.seg i).1 + t • C.dir i := by
  obtain ⟨t, ht, hXt⟩ := C.xpoint_param_mem hn i j h
  obtain ⟨t2, ht2, hXt2⟩ := mem_openSegment_iff_param.mp (C.xpoint_mem i j h).1
  have hdir : C.dir i = (C.seg i).2 - (C.seg i).1 := rfl
  rw [← hdir] at hXt2
  have hu := C.dir_ne_of hn i
  have h2 : t = t2 := C.eq_of_smul_eq_smul_of_param hu (hXt.symm.trans hXt2)
  exact ⟨t, h2 ▸ ht2, ht, hXt⟩

/-- The arrival time of a frog starting at `(seg i).1` equals the arrival
time from its circle endpoint (the smaller-parameter circle point). -/
lemma arrival_eq_circlePt_fst (hn : 2 ≤ n) (i k : Fin n) (hk : i ≠ k) :
    C.arrival i k hk ((C.seg i).1) = C.arrival i k hk (C.circlePt hn ⟨i, false⟩) := by
  have hu := C.dir_ne_of hn i
  obtain ⟨tX, htX01, htX, hXtX⟩ := C.xpoint_param hn i k hk
  have hZ : C.circlePt hn ⟨i, false⟩ = (C.seg i).1 + (C.circleParams hn i).1 • C.dir i := by
    rw [circlePt, if_neg (show ¬(false = true) from by simp), circlePts_fst_eq]
  have hnorm : ‖C.dir i‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  have hPA : (C.seg i).1 = (C.seg i).1 + (0 : ℝ) • C.dir i := by rw [zero_smul, add_zero]
  rw [arrival, arrival]
  congr 2
  apply Finset.filter_congr
  intro Y hY
  obtain ⟨j, hj, rfl⟩ := C.mem_crossings.mp hY
  obtain ⟨tY, htY01, htY, hYtY⟩ := C.xpoint_param hn i j hj
  -- dist from A = t·‖u‖, dist from Z₋ = (t - t₋)·‖u‖, both increasing in t
  have hd1 : dist ((C.seg i).1) (C.xpoint i j hj) = |tY| * ‖C.dir i‖ := by
    have h := C.dist_along_dir (i := i) (tP := 0) hPA hYtY
    rw [sub_zero] at h
    exact h
  have hd2 : dist (C.circlePt hn ⟨i, false⟩) (C.xpoint i j hj)
      = |tY - (C.circleParams hn i).1| * ‖C.dir i‖ :=
    C.dist_along_dir i hZ hYtY
  have hd3 : dist ((C.seg i).1) (C.xpoint i k hk) = |tX| * ‖C.dir i‖ := by
    have h := C.dist_along_dir (i := i) (tP := 0) hPA hXtX
    rw [sub_zero] at h
    exact h
  have hd4 : dist (C.circlePt hn ⟨i, false⟩) (C.xpoint i k hk)
      = |tX - (C.circleParams hn i).1| * ‖C.dir i‖ :=
    C.dist_along_dir i hZ hXtX
  rw [hd1, hd2, hd3, hd4]
  have h1 : |tY| = tY := abs_of_pos htY01.1
  have h2 : |tX| = tX := abs_of_pos htX01.1
  have h3 : |tY - (C.circleParams hn i).1| = tY - (C.circleParams hn i).1 :=
    abs_of_pos (sub_pos.mpr htY.1)
  have h4 : |tX - (C.circleParams hn i).1| = tX - (C.circleParams hn i).1 :=
    abs_of_pos (sub_pos.mpr htX.1)
  rw [h1, h2, h3, h4]
  have hp : 0 < ‖C.dir i‖ := norm_pos_iff.mpr hu
  constructor
  · intro h
    have h2 := (mul_lt_mul_iff_of_pos_right hp).mp h
    exact (mul_lt_mul_iff_of_pos_right hp).mpr (by linarith [h2])
  · intro h
    have h2 := (mul_lt_mul_iff_of_pos_right hp).mp h
    exact (mul_lt_mul_iff_of_pos_right hp).mpr (by linarith [h2])

/-- The arrival time of a frog starting at `(seg i).2` equals the arrival
time from its circle endpoint (the larger-parameter circle point). -/
lemma arrival_eq_circlePt_snd (hn : 2 ≤ n) (i k : Fin n) (hk : i ≠ k) :
    C.arrival i k hk ((C.seg i).2) = C.arrival i k hk (C.circlePt hn ⟨i, true⟩) := by
  have hu := C.dir_ne_of hn i
  obtain ⟨tX, htX01, htX, hXtX⟩ := C.xpoint_param hn i k hk
  have hZ : C.circlePt hn ⟨i, true⟩ = (C.seg i).1 + (C.circleParams hn i).2 • C.dir i := by
    rw [circlePt, if_pos rfl, circlePts_snd_eq]
  have hB : (C.seg i).2 = (C.seg i).1 + (1 : ℝ) • C.dir i := by
    rw [one_smul]
    have hdir : C.dir i = (C.seg i).2 - (C.seg i).1 := rfl
    rw [hdir]
    module
  have hnorm : ‖C.dir i‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  rw [arrival, arrival]
  congr 2
  apply Finset.filter_congr
  intro Y hY
  obtain ⟨j, hj, rfl⟩ := C.mem_crossings.mp hY
  obtain ⟨tY, htY01, htY, hYtY⟩ := C.xpoint_param hn i j hj
  have hd1 : dist ((C.seg i).2) (C.xpoint i j hj) = |tY - 1| * ‖C.dir i‖ := by
    have h := C.dist_along_dir i hB hYtY
    exact h
  have hd2 : dist (C.circlePt hn ⟨i, true⟩) (C.xpoint i j hj)
      = |tY - (C.circleParams hn i).2| * ‖C.dir i‖ :=
    C.dist_along_dir i hZ hYtY
  have hd3 : dist ((C.seg i).2) (C.xpoint i k hk) = |tX - 1| * ‖C.dir i‖ := by
    have h := C.dist_along_dir i hB hXtX
    exact h
  have hd4 : dist (C.circlePt hn ⟨i, true⟩) (C.xpoint i k hk)
      = |tX - (C.circleParams hn i).2| * ‖C.dir i‖ :=
    C.dist_along_dir i hZ hXtX
  rw [hd1, hd2, hd3, hd4]
  have h1 : |tY - 1| = 1 - tY := by
    rw [abs_of_nonpos (by linarith [htY01.2])]
    ring
  have h2 : |tX - 1| = 1 - tX := by
    rw [abs_of_nonpos (by linarith [htX01.2])]
    ring
  have h3 : |tY - (C.circleParams hn i).2| = (C.circleParams hn i).2 - tY := by
    rw [abs_of_nonpos (by linarith [htY.2])]
    ring
  have h4 : |tX - (C.circleParams hn i).2| = (C.circleParams hn i).2 - tX := by
    rw [abs_of_nonpos (by linarith [htX.2])]
    ring
  rw [h1, h2, h3, h4]
  have hp : 0 < ‖C.dir i‖ := norm_pos_iff.mpr hu
  constructor
  · intro h
    have h2 := (mul_lt_mul_iff_of_pos_right hp).mp h
    exact (mul_lt_mul_iff_of_pos_right hp).mpr (by linarith [h2])
  · intro h
    have h2 := (mul_lt_mul_iff_of_pos_right hp).mp h
    exact (mul_lt_mul_iff_of_pos_right hp).mpr (by linarith [h2])

/-- The far-arc from circle endpoint `a` to circle endpoint `b`: the
circle endpoints on the opposite side of the chord line through `a` and
`b` from the crossing of the segments of `a` and `b` (defined whenever
`a.1 ≠ b.1`; junk otherwise). -/
noncomputable def farArc (hn : 2 ≤ n) (a b : Fin n × Bool) : Finset (Fin n × Bool) :=
  Finset.univ.filter fun q =>
    detv (C.circlePt hn b - C.circlePt hn a) (C.circlePt hn q - C.circlePt hn a) *
      detv (C.circlePt hn b - C.circlePt hn a) (C.nxpoint a.1 b.1 - C.circlePt hn a) < 0

/-- A chord `k` *separates* points `A` and `B`: they lie on opposite
sides of the line of segment `k`. -/
def separates (k : Fin n) (A B : ℝ × ℝ) : Prop :=
  detv (C.dir k) (A - (C.seg k).1) * detv (C.dir k) (B - (C.seg k).1) < 0

/-- The crossing of the segments of circle endpoints `a` and `b` does not
lie on the line through the circle endpoints `a` and `b`. -/
lemma detv_xpoint_circlePt_ne_zero (hn : 2 ≤ n) {a b : Fin n × Bool} (hab : a.1 ≠ b.1) :
    detv (C.circlePt hn b - C.circlePt hn a)
      (C.xpoint a.1 b.1 hab - C.circlePt hn a) ≠ 0 := by
  intro hd
  have hne1 : C.circlePt hn b - C.circlePt hn a ≠ 0 := by
    intro hzero
    have heq : C.circlePt hn b = C.circlePt hn a := sub_eq_zero.mp hzero
    have h3 := C.circlePt_injective hn heq
    rw [h3] at hab
    exact hab rfl
  obtain ⟨c, hc⟩ := exists_smul_of_detv_eq_zero hne1 hd
  have hXa := C.detv_dir_self_left (openSegment_subset_segment _ _ _
    (C.xpoint_mem a.1 b.1 hab).1)
  have hAa := C.circlePt_on_line hn a
  have e1 : detv (C.dir a.1) (C.xpoint a.1 b.1 hab - C.circlePt hn a) = 0 := by
    have e : C.xpoint a.1 b.1 hab - C.circlePt hn a
        = (C.xpoint a.1 b.1 hab - (C.seg a.1).1) - (C.circlePt hn a - (C.seg a.1).1) := by abel
    rw [e, detv_sub_right, hXa, hAa, sub_zero]
  rw [hc, detv_smul_right] at e1
  have e2 : detv (C.dir a.1) (C.circlePt hn b - C.circlePt hn a) = 0 := by
    rcases mul_eq_zero.mp e1 with g | g
    · have heq : C.xpoint a.1 b.1 hab = C.circlePt hn a := by
        rw [g, zero_smul] at hc
        exact sub_eq_zero.mp hc
      have hnsq := C.circlePt_nsq hn a
      have hlt : nsq (C.xpoint a.1 b.1 hab) < C.radius ^ 2 :=
        C.xpoint_nsq_lt_radius_sq a.1 b.1 hab
      rw [heq, hnsq] at hlt
      exact absurd hlt (lt_irrefl _)
    · exact g
  have e3 : detv (C.dir a.1) (C.circlePt hn b - (C.seg a.1).1) = 0 := by
    have e : C.circlePt hn b - (C.seg a.1).1
        = (C.circlePt hn b - C.circlePt hn a) + (C.circlePt hn a - (C.seg a.1).1) := by abel
    rw [e, detv_add_right, e2, hAa, add_zero]
  have hXb := C.detv_dir_self_left (openSegment_subset_segment _ _ _
    (C.xpoint_mem a.1 b.1 hab).2)
  have hBb := C.circlePt_on_line hn b
  have heq : C.circlePt hn b = C.xpoint a.1 b.1 hab :=
    eq_of_detv_eq_zero_of_detv_eq_zero (C.dir_ne a.1 b.1 hab) e3 hXa hBb hXb
  have hnsq := C.circlePt_nsq hn b
  have hlt : nsq (C.xpoint a.1 b.1 hab) < C.radius ^ 2 := C.xpoint_nsq_lt_radius_sq a.1 b.1 hab
  rw [← heq] at hlt
  rw [hnsq] at hlt
  exact (lt_irrefl _) hlt

/-- The open chord of segment `i`: the open segment between its two
circle endpoints. -/
def openChord (hn : 2 ≤ n) (i : Fin n) : Set (ℝ × ℝ) :=
  openSegment ℝ (C.circlePts hn i).1 (C.circlePts hn i).2

/-- The direction vector of the open chord of segment `k`. -/
lemma openChord_dir (hn : 2 ≤ n) (k : Fin n) :
    (C.circlePts hn k).2 - (C.circlePts hn k).1
      = ((C.circleParams hn k).2 - (C.circleParams hn k).1) • C.dir k := by
  rw [circlePts_fst_eq, circlePts_snd_eq]
  module

lemma dir_sub_circlePts_fst (hn : 2 ≤ n) (k : Fin n) (p : ℝ × ℝ) :
    detv (C.dir k) (p - (C.circlePts hn k).1)
      = detv (C.dir k) (p - (C.seg k).1) := by
  have e : p - (C.circlePts hn k).1
      = (p - (C.seg k).1) - ((C.circlePts hn k).1 - (C.seg k).1) := by abel
  rw [e, detv_sub_right, circlePts_fst_eq]
  have e2 : (C.seg k).1 + (C.circleParams hn k).1 • C.dir k - (C.seg k).1
      = (C.circleParams hn k).1 • C.dir k := by abel
  rw [e2, detv_smul_right, detv_self, mul_zero, sub_zero]

lemma dir_circlePts_fst_sub (hn : 2 ≤ n) (k : Fin n) :
    detv (C.dir k) ((C.circlePts hn k).1 - (C.seg k).1) = 0 := by
  rw [circlePts_fst_eq]
  have e : (C.seg k).1 + (C.circleParams hn k).1 • C.dir k - (C.seg k).1
      = (C.circleParams hn k).1 • C.dir k := by abel
  rw [e, detv_smul_right, detv_self, mul_zero]


/-- A point strictly inside the closed disk on the line of segment `i`
lies on the open chord of `i`. -/
lemma mem_openChord_of_nsq_lt (hn : 2 ≤ n) (i : Fin n) {Y : ℝ × ℝ}
    (hY : nsq Y < C.radius ^ 2) (hd : detv (C.dir i) (Y - (C.seg i).1) = 0) :
    Y ∈ C.openChord hn i := by
  have hu := C.dir_ne_of hn i
  obtain ⟨c, hc⟩ := exists_smul_of_detv_eq_zero hu hd
  rw [openChord]
  rw [mem_openSegment_iff_param] at *
  -- Y = (seg i).1 + c • dir i; the chord params are t₋ t₊
  have hspec := (C.circleParams_spec hn i).2.2.2.2 c
  have h2 : nsq ((C.seg i).1 + c • C.dir i) < C.radius ^ 2 := by
    rw [← hc, add_sub_cancel]
    exact hY
  obtain ⟨h3, h4⟩ := hspec.mp h2
  -- Y = Z₋ + ((c - t₋)/(t₊ - t₋)) • (Z₊ - Z₋)
  have hlt : 0 < (C.circleParams hn i).2 - (C.circleParams hn i).1 := by
    have := C.circleParams_lt hn i
    linarith
  have hratio : 0 < (c - (C.circleParams hn i).1) / ((C.circleParams hn i).2 - (C.circleParams hn i).1) := by
    exact div_pos (by linarith) hlt
  have hratio1 : (c - (C.circleParams hn i).1) / ((C.circleParams hn i).2 - (C.circleParams hn i).1) < 1 := by
    exact (div_lt_one hlt).mpr (by linarith)
  rw [circlePts_fst_eq, circlePts_snd_eq]
  refine ⟨(c - (C.circleParams hn i).1) / ((C.circleParams hn i).2 - (C.circleParams hn i).1),
    ⟨hratio, hratio1⟩, ?_⟩
  have e2 : ((C.seg i).1 + (C.circleParams hn i).2 • C.dir i) - ((C.seg i).1 + (C.circleParams hn i).1 • C.dir i)
      = ((C.circleParams hn i).2 - (C.circleParams hn i).1) • C.dir i := by module
  rw [e2, smul_smul]
  have e3 : ((C.seg i).1 + (C.circleParams hn i).1 • C.dir i) +
      ((((c - (C.circleParams hn i).1) / ((C.circleParams hn i).2 - (C.circleParams hn i).1)) *
        ((C.circleParams hn i).2 - (C.circleParams hn i).1)) • C.dir i)
      = (C.seg i).1 + c • C.dir i := by
    have hlt2 : (C.circleParams hn i).2 - (C.circleParams hn i).1 ≠ 0 := by
      have := C.circleParams_lt hn i
      linarith
    have e4 : ((c - (C.circleParams hn i).1) / ((C.circleParams hn i).2 - (C.circleParams hn i).1)) *
        ((C.circleParams hn i).2 - (C.circleParams hn i).1) = c - (C.circleParams hn i).1 :=
      div_mul_cancel₀ _ hlt2
    rw [e4]
    module
  rw [e3, ← hc, add_sub_cancel]

/-- If chord `k` separates circle endpoints `A` and `B`, then the segment
`(A, B)` and the open chord of `k` cross properly. -/
lemma separates_properCross (hn : 2 ≤ n) {a b : Fin n × Bool} {k : Fin n}
    (hab : a.1 ≠ b.1) (hsep : C.separates k (C.circlePt hn a) (C.circlePt hn b)) :
    ∃ Y, Y ∈ openSegment ℝ (C.circlePt hn a) (C.circlePt hn b) ∧
      Y ∈ C.openChord hn k := by
  have hu := C.dir_ne_of hn k
  set A := C.circlePt hn a
  set B := C.circlePt hn b
  set p := (C.seg k).1
  set w := C.dir k
  -- G(G + D) < 0 where G = detv w (A - p), D = detv w (B - A)
  have hD : detv w (B - A) ≠ 0 := by
    intro hd
    have h1 : detv w (B - p) = detv w (A - p) := by
      have e : B - p = (B - A) + (A - p) := by abel
      rw [e, detv_add_right, hd, zero_add]
    have hsepc : detv w (A - p) * detv w (B - p) < 0 := hsep
    rw [h1] at hsepc
    exact not_lt_of_ge (mul_self_nonneg _) hsepc
  have hGD : detv w (A - p) * (detv w (A - p) + detv w (B - A)) < 0 := by
    have e : detv w (B - p) = detv w (A - p) + detv w (B - A) := by
      have e2 : B - p = (B - A) + (A - p) := by abel
      rw [e2, detv_add_right, add_comm]
    have hsepc : detv w (A - p) * detv w (B - p) < 0 := hsep
    rw [e] at hsepc
    exact hsepc
  obtain ⟨hGD1, hGD2⟩ := sign_S2.mp hGD
  -- t = detv (p - A) w / detv (B - A) w = G / (-D)
  have htIoo : detv (p - A) w / detv (B - A) w ∈ Set.Ioo (0 : ℝ) 1 := by
    have eG : detv (p - A) w = detv w (A - p) := by
      show (p.1 - A.1) * w.2 - (p.2 - A.2) * w.1
        = w.1 * (A.2 - p.2) - w.2 * (A.1 - p.1)
      ring
    have eD : detv (B - A) w = -detv w (B - A) := detv_antisymm _ _
    rw [eG, eD, div_mem_Ioo (neg_ne_zero.mpr hD)]
    constructor <;> nlinarith [hGD1, hGD2]
  refine ⟨A + (detv (p - A) w / detv (B - A) w) • (B - A), ?_, ?_⟩
  · rw [mem_openSegment_iff_param]
    exact ⟨_, htIoo, rfl⟩
  · -- Y on line k with nsq Y < r²
    set t := detv (p - A) w / detv (B - A) w with ht_def
    have hYline : detv w ((A + t • (B - A)) - p) = 0 := by
      have e : (A + t • (B - A)) - p = (A - p) + t • (B - A) := by module
      rw [e, detv_add_right, detv_smul_right]
      have ht2 : detv (p - A) w = detv w (A - p) := by
        show (p.1 - A.1) * w.2 - (p.2 - A.2) * w.1
          = w.1 * (A.2 - p.2) - w.2 * (A.1 - p.1)
        ring
      have hD' : detv (B - A) w ≠ 0 := by
        have eD : detv (B - A) w = -detv w (B - A) := detv_antisymm _ _
        rw [eD]
        exact neg_ne_zero.mpr hD
      have eD2 : detv w (B - A) = -detv (B - A) w := detv_antisymm _ _
      rw [ht_def, ht2, eD2, mul_neg, div_mul_cancel₀ _ hD']
      ring
    have hYnsq : nsq (A + t • (B - A)) < C.radius ^ 2 := by
      have hnsqA := C.circlePt_nsq hn a
      have hnsqB := C.circlePt_nsq hn b
      have hdot : dotv A B < C.radius ^ 2 := by
        have hLag := detv_sq_eq A B
        rw [hnsqA, hnsqB] at hLag
        have hr : 0 < C.radius ^ 2 := sq_pos_of_ne_zero (ne_of_gt C.radius_pos)
        have hsq : dotv A B ^ 2 ≤ (C.radius ^ 2) ^ 2 := by
          nlinarith [sq_nonneg (detv A B), hLag]
        have hle : dotv A B ≤ C.radius ^ 2 := by
          have h1 : |dotv A B| ≤ |C.radius ^ 2| := sq_le_sq.mp hsq
          rw [abs_of_pos hr] at h1
          exact le_trans (le_abs_self _) h1
        have hne : dotv A B ≠ C.radius ^ 2 := by
          intro hd2
          have hdet : detv A B = 0 := by
            have h2 : detv A B ^ 2 = 0 := by nlinarith [hLag, hd2]
            exact sq_eq_zero_iff.mp h2
          have h6 : nsq (C.circlePt hn b - C.circlePt hn a) = 0 := by
            rw [nsq_sub, hnsqA, hnsqB, dotv_comm (C.circlePt hn b) (C.circlePt hn a), hd2]
            ring
          rw [nsq_eq_zero_iff] at h6
          have heq : C.circlePt hn b = C.circlePt hn a := sub_eq_zero.mp h6
          have h7 := C.circlePt_injective hn heq
          rw [h7] at hab
          exact hab rfl
        exact lt_of_le_of_ne hle hne
      rw [nsq_add_smul, hnsqA, nsq_sub, hnsqB, dotv_sub_right, dotv_self, hnsqA,
        dotv_comm B A]
      have ht01 : t ∈ Set.Ioo (0 : ℝ) 1 := htIoo
      have h1 : 0 < t * (1 - t) * (C.radius ^ 2 - dotv A B) :=
        mul_pos (mul_pos ht01.1 (by linarith [ht01.2])) (by linarith [hdot])
      nlinarith [h1]
    exact C.mem_openChord_of_nsq_lt hn k hYnsq hYline

/-- Membership in the open chord of segment `i` in terms of the
parameter along the line. -/
lemma mem_openChord_of_param (hn : 2 ≤ n) (i : Fin n) {Y : ℝ × ℝ} {s : ℝ}
    (hY : Y = (C.seg i).1 + s • C.dir i)
    (hs : s ∈ Set.Ioo (C.circleParams hn i).1 (C.circleParams hn i).2) :
    Y ∈ C.openChord hn i := by
  rw [openChord, mem_openSegment_iff_param]
  rw [circlePts_fst_eq, circlePts_snd_eq]
  have hlt : 0 < (C.circleParams hn i).2 - (C.circleParams hn i).1 := by
    have := C.circleParams_lt hn i
    linarith
  refine ⟨(s - (C.circleParams hn i).1) / ((C.circleParams hn i).2 - (C.circleParams hn i).1),
    ⟨div_pos (by linarith [hs.1]) hlt, (div_lt_one hlt).mpr (by linarith [hs.2])⟩, ?_⟩
  have e2 : ((C.seg i).1 + (C.circleParams hn i).2 • C.dir i)
      - ((C.seg i).1 + (C.circleParams hn i).1 • C.dir i)
      = ((C.circleParams hn i).2 - (C.circleParams hn i).1) • C.dir i := by module
  rw [e2, smul_smul]
  have hlt2 : (C.circleParams hn i).2 - (C.circleParams hn i).1 ≠ 0 := by linarith
  have e3 : ((C.seg i).1 + (C.circleParams hn i).1 • C.dir i) +
      (((s - (C.circleParams hn i).1) / ((C.circleParams hn i).2 - (C.circleParams hn i).1)) *
        ((C.circleParams hn i).2 - (C.circleParams hn i).1)) • C.dir i
      = (C.seg i).1 + s • C.dir i := by
    have e4 : ((s - (C.circleParams hn i).1) / ((C.circleParams hn i).2 - (C.circleParams hn i).1)) *
        ((C.circleParams hn i).2 - (C.circleParams hn i).1) = s - (C.circleParams hn i).1 :=
      div_mul_cancel₀ _ hlt2
    rw [e4]
    module
  rw [e3, hY]

/-- Points of the open chord of segment `i` lie strictly inside the
circle. -/
lemma nsq_lt_of_mem_openChord (hn : 2 ≤ n) (i : Fin n) {Y : ℝ × ℝ}
    (hY : Y ∈ C.openChord hn i) : nsq Y < C.radius ^ 2 := by
  rw [openChord, mem_openSegment_iff_param] at hY
  obtain ⟨s, hs, hYs⟩ := hY
  have hnsq1 := C.circlePts_fst_nsq hn i
  have hnsq2 := C.circlePts_snd_nsq hn i
  have hne := C.circlePts_ne hn i
  have hdot : dotv (C.circlePts hn i).1 (C.circlePts hn i).2 < C.radius ^ 2 := by
    have hLag := detv_sq_eq (C.circlePts hn i).1 (C.circlePts hn i).2
    rw [hnsq1, hnsq2] at hLag
    have hr : 0 < C.radius ^ 2 := sq_pos_of_ne_zero (ne_of_gt C.radius_pos)
    have hsq : dotv (C.circlePts hn i).1 (C.circlePts hn i).2 ^ 2 ≤ (C.radius ^ 2) ^ 2 := by
      nlinarith [sq_nonneg (detv (C.circlePts hn i).1 (C.circlePts hn i).2), hLag]
    have hle : dotv (C.circlePts hn i).1 (C.circlePts hn i).2 ≤ C.radius ^ 2 := by
      have h1 : |dotv (C.circlePts hn i).1 (C.circlePts hn i).2| ≤ |C.radius ^ 2| :=
        sq_le_sq.mp hsq
      rw [abs_of_pos hr] at h1
      exact le_trans (le_abs_self _) h1
    have hne2 : dotv (C.circlePts hn i).1 (C.circlePts hn i).2 ≠ C.radius ^ 2 := by
      intro hd2
      have hdet : detv (C.circlePts hn i).1 (C.circlePts hn i).2 = 0 := by
        have h2 : detv (C.circlePts hn i).1 (C.circlePts hn i).2 ^ 2 = 0 := by
          nlinarith [hLag, hd2]
        exact sq_eq_zero_iff.mp h2
      have h6 : nsq ((C.circlePts hn i).2 - (C.circlePts hn i).1) = 0 := by
        rw [nsq_sub, hnsq2, hnsq1, dotv_comm (C.circlePts hn i).2 (C.circlePts hn i).1, hd2]
        ring
      rw [nsq_eq_zero_iff] at h6
      exact hne (sub_eq_zero.mp h6).symm
    exact lt_of_le_of_ne hle hne2
  rw [hYs]
  have e : (C.circlePts hn i).1 + s • ((C.circlePts hn i).2 - (C.circlePts hn i).1)
      = (1 - s) • (C.circlePts hn i).1 + s • (C.circlePts hn i).2 := by module
  rw [e]
  have hnsq2' : nsq ((1 - s) • (C.circlePts hn i).1 + s • (C.circlePts hn i).2)
      = (1 - s) ^ 2 * nsq (C.circlePts hn i).1 + 2 * ((1 - s) * s) *
        dotv (C.circlePts hn i).1 (C.circlePts hn i).2 + s ^ 2 * nsq (C.circlePts hn i).2 := by
    rw [nsq_add_smul, nsq_smul, dotv_smul_left]
    ring
  rw [hnsq2', hnsq1, hnsq2]
  have h1 : 0 < s * (1 - s) * (C.radius ^ 2 - dotv (C.circlePts hn i).1 (C.circlePts hn i).2) :=
    mul_pos (mul_pos hs.1 (by linarith [hs.2])) (by linarith [hdot])
  nlinarith [h1]






/-- A linear function with values of opposite signs at `t1 < t2` has a
root strictly between them. -/
lemma exists_root_of_mul_neg {f0 D t1 t2 : ℝ} (hD : D ≠ 0) (ht : t1 < t2)
    (h : (f0 + t1 * D) * (f0 + t2 * D) < 0) :
    ∃ s ∈ Set.Ioo t1 t2, f0 + s * D = 0 := by
  have hD2 : 0 < D ^ 2 := sq_pos_of_ne_zero hD
  have h1 : (-f0 / D - t1) * (-f0 / D - t2) < 0 := by
    have e2 : (-f0 / D - t1) * (-f0 / D - t2)
        = ((f0 + t1 * D) * (f0 + t2 * D)) / (D * D) := by
      field_simp
      ring
    rw [e2]
    exact div_neg_of_neg_of_pos h (by nlinarith [hD2])
  have h2 : t1 < -f0 / D ∧ -f0 / D < t2 := by
    rcases mul_neg_iff.mp h1 with g | g
    · exact ⟨by linarith [g.1], by linarith [g.2]⟩
    · exfalso
      nlinarith [ht]
  refine ⟨-f0 / D, h2, ?_⟩
  field_simp
  ring

/-- From `OppSide` on the open chord of `k` to `separates`: the
determinant factor is a positive square times the `separates` product. -/
lemma separates_of_oppSide_chord (hn : 2 ≤ n) (k : Fin n) {A B : ℝ × ℝ}
    (h1 : detv ((C.circlePts hn k).2 - (C.circlePts hn k).1) (A - (C.circlePts hn k).1) *
      detv ((C.circlePts hn k).2 - (C.circlePts hn k).1) (B - (C.circlePts hn k).1) < 0) :
    detv (C.dir k) (A - (C.seg k).1) * detv (C.dir k) (B - (C.seg k).1) < 0 := by
  have e1 : detv ((C.circlePts hn k).2 - (C.circlePts hn k).1) (A - (C.circlePts hn k).1)
      = ((C.circleParams hn k).2 - (C.circleParams hn k).1) *
        detv (C.dir k) (A - (C.seg k).1) := by
    rw [C.openChord_dir hn k, detv_smul_left]
    have e3 : detv (C.dir k) (A - (C.circlePts hn k).1)
        = detv (C.dir k) (A - (C.seg k).1) := by
      have e4 : A - (C.circlePts hn k).1
          = (A - (C.seg k).1) - ((C.circlePts hn k).1 - (C.seg k).1) := by abel
      rw [e4, detv_sub_right, C.dir_circlePts_fst_sub hn k, sub_zero]
    rw [e3]
  have e2 : detv ((C.circlePts hn k).2 - (C.circlePts hn k).1) (B - (C.circlePts hn k).1)
      = ((C.circleParams hn k).2 - (C.circleParams hn k).1) *
        detv (C.dir k) (B - (C.seg k).1) := by
    rw [C.openChord_dir hn k, detv_smul_left]
    have e3 : detv (C.dir k) (B - (C.circlePts hn k).1)
        = detv (C.dir k) (B - (C.seg k).1) := by
      have e4 : B - (C.circlePts hn k).1
          = (B - (C.seg k).1) - ((C.circlePts hn k).1 - (C.seg k).1) := by abel
      rw [e4, detv_sub_right, C.dir_circlePts_fst_sub hn k, sub_zero]
    rw [e3]
  rw [e1, e2] at h1
  have hlt := C.circleParams_lt hn k
  have hpos : 0 < ((C.circleParams hn k).2 - (C.circleParams hn k).1) ^ 2 :=
    sq_pos_of_ne_zero (by linarith)
  rcases mul_neg_iff.mp h1 with g | g
  · have h3 := mul_lt_mul_of_pos_right g.1 hpos
    have h4 := mul_lt_mul_of_pos_right g.2 hpos
    nlinarith
  · have h3 := mul_lt_mul_of_pos_right g.1 hpos
    have h4 := mul_lt_mul_of_pos_right g.2 hpos
    nlinarith

/-- A point on the line of segment `i` and on the circle is one of the two
circle points of `i`. -/
lemma eq_circlePts_of_mem_line_circle (hn : 2 ≤ n) (i : Fin n) {p : ℝ × ℝ}
    (hp : nsq p = C.radius ^ 2) (hd : detv (C.dir i) (p - (C.seg i).1) = 0) :
    p = (C.circlePts hn i).1 ∨ p = (C.circlePts hn i).2 := by
  have hu := C.dir_ne_of hn i
  obtain ⟨c, hc⟩ := exists_smul_of_detv_eq_zero hu hd
  have hq : nsq ((C.seg i).1 + c • C.dir i) = C.radius ^ 2 := by
    rw [← hc, add_sub_cancel]
    exact hp
  have hq1 : nsq ((C.seg i).1 + (C.circleParams hn i).1 • C.dir i) = C.radius ^ 2 :=
    (C.circleParams_spec hn i).2.1
  have hq2 : nsq ((C.seg i).1 + (C.circleParams hn i).2 • C.dir i) = C.radius ^ 2 :=
    (C.circleParams_spec hn i).2.2.1
  have hQ : ∀ x : ℝ, nsq ((C.seg i).1 + x • C.dir i) - C.radius ^ 2
      = nsq (C.dir i) * x ^ 2 + 2 * dotv (C.seg i).1 (C.dir i) * x + (nsq (C.seg i).1 - C.radius ^ 2) := by
    intro x
    rw [nsq_add_smul]
    ring
  have hQc : nsq (C.dir i) * c ^ 2 + 2 * dotv (C.seg i).1 (C.dir i) * c + (nsq (C.seg i).1 - C.radius ^ 2) = 0 := by
    have h1 := hQ c
    nlinarith [h1, hq]
  have hQ1 : nsq (C.dir i) * (C.circleParams hn i).1 ^ 2 + 2 * dotv (C.seg i).1 (C.dir i) * (C.circleParams hn i).1 + (nsq (C.seg i).1 - C.radius ^ 2) = 0 := by
    have h1 := hQ (C.circleParams hn i).1
    nlinarith [h1, hq1]
  have hQ2 : nsq (C.dir i) * (C.circleParams hn i).2 ^ 2 + 2 * dotv (C.seg i).1 (C.dir i) * (C.circleParams hn i).2 + (nsq (C.seg i).1 - C.radius ^ 2) = 0 := by
    have h1 := hQ (C.circleParams hn i).2
    nlinarith [h1, hq2]
  have hsub : (c - (C.circleParams hn i).1) * (nsq (C.dir i) * (c + (C.circleParams hn i).1) + 2 * dotv (C.seg i).1 (C.dir i)) = 0 := by
    nlinarith [hQc, hQ1]
  have h5 : nsq (C.dir i) * ((C.circleParams hn i).1 + (C.circleParams hn i).2) = -2 * dotv (C.seg i).1 (C.dir i) := by
    have hsub2 : ((C.circleParams hn i).2 - (C.circleParams hn i).1) *
        (nsq (C.dir i) * ((C.circleParams hn i).1 + (C.circleParams hn i).2) + 2 * dotv (C.seg i).1 (C.dir i)) = 0 := by
      nlinarith [hQ1, hQ2]
    have hne : (C.circleParams hn i).2 - (C.circleParams hn i).1 ≠ 0 := by
      have := C.circleParams_lt hn i
      linarith
    rcases mul_eq_zero.mp hsub2 with h4 | h4
    · exact absurd h4 hne
    · nlinarith [h4]
  rcases mul_eq_zero.mp hsub with hcase | hcase
  · left
    have hp2 : p = (C.seg i).1 + c • C.dir i := by
      rw [← hc]
      abel
    rw [hp2, show c = (C.circleParams hn i).1 from by linarith [hcase], circlePts_fst_eq]
  · right
    have hp2 : p = (C.seg i).1 + c • C.dir i := by
      rw [← hc]
      abel
    have hc2 : c = (C.circleParams hn i).2 := by
      have h6 : nsq (C.dir i) * (c - (C.circleParams hn i).2) = 0 := by
        nlinarith [hcase, h5]
      rcases mul_eq_zero.mp h6 with g | g
      · exact (hu (nsq_eq_zero_iff.mp g)).elim
      · nlinarith [g]
    rw [hp2, hc2, circlePts_snd_eq]

/-- Backward direction of the alternation: if the two circle endpoints of
chord `k` lie on opposite sides of the line through the circle endpoints
of `a` and `b`, then `k` separates the circle endpoints of `a` and `b`. -/
lemma separates_of_opp_far (hn : 2 ≤ n) {a b : Fin n × Bool} {k : Fin n}
    (hab : a.1 ≠ b.1)
    (hopp : detv (C.circlePt hn b - C.circlePt hn a) ((C.circlePts hn k).1 - C.circlePt hn a) *
      detv (C.circlePt hn b - C.circlePt hn a) ((C.circlePts hn k).2 - C.circlePt hn a) < 0) :
    C.separates k (C.circlePt hn a) (C.circlePt hn b) := by
  have hu := C.dir_ne_of hn k
  set A := C.circlePt hn a
  set B := C.circlePt hn b
  set p := (C.seg k).1
  set w := C.dir k
  have hD : detv (C.circlePt hn b - C.circlePt hn a) w ≠ 0 := by
    intro hd
    have e1 : detv (C.circlePt hn b - C.circlePt hn a) ((C.circlePts hn k).1 - A)
        = detv (C.circlePt hn b - C.circlePt hn a) (p - A) := by
      rw [circlePts_fst_eq, detv_sub_right, detv_add_right, detv_smul_right, hd, mul_zero,
        add_zero, ← detv_sub_right]
    have e2 : detv (C.circlePt hn b - C.circlePt hn a) ((C.circlePts hn k).2 - A)
        = detv (C.circlePt hn b - C.circlePt hn a) (p - A) := by
      rw [circlePts_snd_eq, detv_sub_right, detv_add_right, detv_smul_right, hd, mul_zero,
        add_zero, ← detv_sub_right]
    rw [e1, e2] at hopp
    exact not_lt_of_ge (mul_self_nonneg _) hopp
  have hf : ∀ s : ℝ, detv (C.circlePt hn b - C.circlePt hn a) ((p + s • w) - A)
      = detv (C.circlePt hn b - C.circlePt hn a) (p - A) + s * detv (C.circlePt hn b - C.circlePt hn a) w := by
    intro s
    have e : (p + s • w) - A = (p - A) + s • w := by module
    rw [e, detv_add_right, detv_smul_right]
  have hopp2 : (detv (C.circlePt hn b - C.circlePt hn a) (p - A) + (C.circleParams hn k).1 *
      detv (C.circlePt hn b - C.circlePt hn a) w) *
    (detv (C.circlePt hn b - C.circlePt hn a) (p - A) + (C.circleParams hn k).2 *
      detv (C.circlePt hn b - C.circlePt hn a) w) < 0 := by
    have e1 := hf (C.circleParams hn k).1
    have e2 := hf (C.circleParams hn k).2
    rw [circlePts_fst_eq, circlePts_snd_eq] at hopp
    rw [e1, e2] at hopp
    exact hopp
  obtain ⟨s0, hs0, hs0eq⟩ := exists_root_of_mul_neg hD (C.circleParams_lt hn k) hopp2
  have hY1 : p + s0 • w ∈ C.openChord hn k :=
    C.mem_openChord_of_param hn k rfl hs0
  have hYline : detv (C.circlePt hn b - C.circlePt hn a) ((p + s0 • w) - A) = 0 := by
    rw [hf s0, hs0eq]
  have hYnsq : nsq (p + s0 • w) < C.radius ^ 2 := C.nsq_lt_of_mem_openChord hn k hY1
  -- Y ∈ openSegment A B via the exact factorization of the (A,B) chord
  have hneAB : C.circlePt hn b - A ≠ 0 := by
    intro hzero
    have heq : C.circlePt hn b = A := sub_eq_zero.mp hzero
    have h := C.circlePt_injective hn heq
    rw [h] at hab
    exact hab rfl
  have hquadAB : ∀ t : ℝ, nsq (A + t • (C.circlePt hn b - A)) - C.radius ^ 2
      = nsq (C.circlePt hn b - A) * t * (t - 1) := by
    intro t
    have hnsqA := C.circlePt_nsq hn a
    have hnsqB := C.circlePt_nsq hn b
    rw [nsq_add_smul, hnsqA, nsq_sub, hnsqB, dotv_sub_right, dotv_self, hnsqA,
      dotv_comm B A]
    ring
  obtain ⟨s, hs⟩ := exists_smul_of_detv_eq_zero hneAB hYline
  have hYs : p + s0 • w = A + s • (C.circlePt hn b - A) := by
    rw [← hs]
    abel
  have hs01 : s ∈ Set.Ioo (0 : ℝ) 1 := by
    have h1 : nsq (A + s • (C.circlePt hn b - A)) < C.radius ^ 2 := by
      rw [← hYs]
      exact hYnsq
    have h2 : nsq (C.circlePt hn b - A) * s * (s - 1) < 0 := by
      have h3 := hquadAB s
      nlinarith [h3, h1]
    have h4 : 0 < nsq (C.circlePt hn b - A) := nsq_pos_of_ne hneAB
    have h5 : s * (s - 1) < 0 := by
      have h6 : nsq (C.circlePt hn b - A) * (s * (s - 1)) < 0 := by
        rw [mul_assoc] at h2
        exact h2
      rcases mul_neg_iff.mp h6 with g | g
      · exact g.2
      · exfalso
        nlinarith [g.1, h4]
    rcases mul_neg_iff.mp h5 with g | g
    · exact ⟨by linarith [g.1], by linarith [g.2]⟩
    · nlinarith [g.1, g.2]
  have hY2 : p + s0 • w ∈ openSegment ℝ A B := by
    rw [mem_openSegment_iff_param]
    exact ⟨s, hs01, hYs⟩
  -- criterion backward on (A,B) and openChord k
  have hd : detv (C.circlePt hn b - A) ((C.circlePts hn k).2 - (C.circlePts hn k).1) ≠ 0 := by
    rw [C.openChord_dir hn k, detv_smul_right]
    have hlt := C.circleParams_lt hn k
    exact mul_ne_zero (by linarith) hD
  have h1cr := (oppSide_of_properCross ⟨hY2, hY1⟩ hd).2
  exact C.separates_of_oppSide_chord hn k h1cr

end SegConf

end Imo2016P6Geo









namespace Imo2016P6Geo

namespace SegConf

variable {n : ℕ} (C : SegConf n)

/-! ## Cyclic labeling, part 1: the angle coordinate and its dictionary -/

/-- The point `p : ℝ × ℝ` viewed as a complex number. -/
def toC (p : ℝ × ℝ) : ℂ := ⟨p.1, p.2⟩

/-- The angle (argument) of a point, in `(-π, π]`. -/
noncomputable def theta (p : ℝ × ℝ) : ℝ := Complex.arg (toC p)

lemma nsq_toC (p : ℝ × ℝ) : Complex.normSq (toC p) = nsq p := by
  rw [Complex.normSq_apply]
  show p.1 * p.1 + p.2 * p.2 = p.1 ^ 2 + p.2 ^ 2
  ring

lemma norm_toC (p : ℝ × ℝ) : ‖toC p‖ = Real.sqrt (nsq p) := by
  rw [Complex.norm_def, nsq_toC]

lemma norm_toC_eq {R : ℝ} {p : ℝ × ℝ} (hp : nsq p = R ^ 2) (hR : 0 < R) :
    ‖toC p‖ = R := by
  rw [norm_toC, hp, Real.sqrt_sq hR.le]

lemma toC_ne_zero_of_nsq {R : ℝ} {p : ℝ × ℝ} (hp : nsq p = R ^ 2) (hR : 0 < R) :
    toC p ≠ 0 := by
  intro hcon
  have h := norm_toC_eq hp hR
  rw [hcon, norm_zero] at h
  linarith

lemma neg_pi_lt_theta (p : ℝ × ℝ) : -Real.pi < theta p := Complex.neg_pi_lt_arg _

lemma theta_le_pi (p : ℝ × ℝ) : theta p ≤ Real.pi := Complex.arg_le_pi _

/-- A point on the circle of radius `R` has first coordinate `R * cos θ`. -/
lemma fst_eq_radius_cos {R : ℝ} {p : ℝ × ℝ} (hp : nsq p = R ^ 2) (hR : 0 < R) :
    p.1 = R * Real.cos (theta p) := by
  have hnorm := norm_toC_eq hp hR
  have h := Complex.cos_arg (toC_ne_zero_of_nsq hp hR)
  rw [hnorm] at h
  have h2 : Real.cos (theta p) = p.1 / R := h
  rw [h2]
  have hR0 : R ≠ 0 := hR.ne'
  field_simp

/-- A point on the circle of radius `R` has second coordinate `R * sin θ`. -/
lemma snd_eq_radius_sin {R : ℝ} {p : ℝ × ℝ} (hp : nsq p = R ^ 2) (hR : 0 < R) :
    p.2 = R * Real.sin (theta p) := by
  have hnorm := norm_toC_eq hp hR
  have h := Complex.sin_arg (toC p)
  rw [hnorm] at h
  have h2 : Real.sin (theta p) = p.2 / R := h
  rw [h2]
  have hR0 : R ≠ 0 := hR.ne'
  field_simp

/-- The determinant of two points on the circle of radius `R` around the
origin equals `R²` times the sine of the angle difference. -/
lemma detv_eq_radius_sq_sin {R : ℝ} {p q : ℝ × ℝ} (hp : nsq p = R ^ 2)
    (hq : nsq q = R ^ 2) (hR : 0 < R) :
    detv p q = R ^ 2 * Real.sin (theta q - theta p) := by
  rw [detv_def, fst_eq_radius_cos hp hR, snd_eq_radius_sin hp hR,
    fst_eq_radius_cos hq hR, snd_eq_radius_sin hq hR, Real.sin_sub]
  ring

/-- Two points on a circle around the origin with the same angle coincide. -/
lemma arg_eq_of_nsq_eq {R : ℝ} {p q : ℝ × ℝ} (hp : nsq p = R ^ 2) (hq : nsq q = R ^ 2)
    (hR : 0 < R) (h : theta p = theta q) : p = q := by
  have h1 := fst_eq_radius_cos hp hR
  have h2 := snd_eq_radius_sin hp hR
  have h3 := fst_eq_radius_cos hq hR
  have h4 := snd_eq_radius_sin hq hR
  rw [h] at h1 h2
  exact Prod.ext (h1.trans h3.symm) (h2.trans h4.symm)

/-! ## Cyclic labeling, part 2: the sine factorization and the arc sign -/

/-- Auxiliary sine identity, in terms of half-angles. -/
lemma sin_factorization_aux (a b : ℝ) :
    Real.sin (2 * (a + b)) - Real.sin (2 * a) - Real.sin (2 * b) =
      -4 * Real.sin a * Real.sin b * Real.sin (a + b) := by
  rw [Real.sin_two_mul, Real.sin_two_mul, Real.sin_two_mul, Real.sin_add, Real.cos_add]
  have h1 : Real.cos a ^ 2 = 1 - Real.sin a ^ 2 := by
    have h := Real.sin_sq_add_cos_sq a
    linarith
  have h2 : Real.cos b ^ 2 = 1 - Real.sin b ^ 2 := by
    have h := Real.sin_sq_add_cos_sq b
    linarith
  linear_combination 2 * Real.sin a * Real.cos a * h2 + 2 * Real.sin b * Real.cos b * h1

/-- The sine factorization identity behind the triangle sign computation. -/
lemma sin_factorization (x y : ℝ) :
    Real.sin (x + y) - Real.sin x - Real.sin y =
      -4 * Real.sin (x / 2) * Real.sin (y / 2) * Real.sin ((x + y) / 2) := by
  have h := sin_factorization_aux (x / 2) (y / 2)
  have e1 : 2 * (x / 2 + y / 2) = x + y := by ring
  have e2 : 2 * (x / 2) = x := by ring
  have e3 : 2 * (y / 2) = y := by ring
  have e4 : x / 2 + y / 2 = (x + y) / 2 := by ring
  rw [e1, e2, e3, e4] at h
  exact h

/-- For `δ ∈ (0, 2π)`, the sine of `δ / 2` is positive. -/
lemma sin_half_pos {δ : ℝ} (h1 : 0 < δ) (h2 : δ < 2 * Real.pi) :
    0 < Real.sin (δ / 2) :=
  Real.sin_pos_of_mem_Ioo ⟨by linarith, by linarith⟩

/-- For `δ ∈ (-2π, 0)`, the sine of `δ / 2` is negative. -/
lemma sin_half_neg {δ : ℝ} (h1 : -2 * Real.pi < δ) (h2 : δ < 0) :
    Real.sin (δ / 2) < 0 :=
  Real.sin_neg_of_neg_of_neg_pi_lt (by linarith) (by linarith)

/-- The triangle determinant identity: `detv (b - a) (q - a)` as the sum of
three circle-point determinants. -/
lemma detv_sub_sub (a b q : ℝ × ℝ) :
    detv (b - a) (q - a) = detv b q + detv a b + detv q a := by
  show (b.1 - a.1) * (q.2 - a.2) - (b.2 - a.2) * (q.1 - a.1)
    = (b.1 * q.2 - b.2 * q.1) + (a.1 * b.2 - a.2 * b.1) + (q.1 * a.2 - q.2 * a.1)
  ring

/-- The triangle sign formula: `detv (b - a) (q - a)` for three points on the
circle as a product of three half-angle sines. -/
lemma arc_sign {R : ℝ} {a b q : ℝ × ℝ} (ha : nsq a = R ^ 2) (hb : nsq b = R ^ 2)
    (hq : nsq q = R ^ 2) (hR : 0 < R) :
    detv (b - a) (q - a) = -4 * R ^ 2 * Real.sin ((theta b - theta q) / 2)
      * Real.sin ((theta q - theta a) / 2) * Real.sin ((theta b - theta a) / 2) := by
  rw [detv_sub_sub, detv_eq_radius_sq_sin hb hq hR, detv_eq_radius_sq_sin ha hb hR,
    detv_eq_radius_sq_sin hq ha hR]
  have h := sin_factorization (theta b - theta q) (theta q - theta a)
  have hxy : theta b - theta q + (theta q - theta a) = theta b - theta a := by ring
  rw [hxy] at h
  have hsin1 : Real.sin (theta q - theta b) = -Real.sin (theta b - theta q) := by
    have e : theta q - theta b = -(theta b - theta q) := by ring
    rw [e, Real.sin_neg]
  have hsin2 : Real.sin (theta a - theta q) = -Real.sin (theta q - theta a) := by
    have e : theta a - theta q = -(theta q - theta a) := by ring
    rw [e, Real.sin_neg]
  rw [hsin1, hsin2]
  linear_combination R ^ 2 * h

/-! ## Cyclic labeling, part 3: the arc predicate and its sign
characterization -/

/-- The normalized angle difference from `a` to `b`, in `[0, 2π)`. -/
noncomputable def deltaOf (a b : ℝ × ℝ) : ℝ :=
  theta b - theta a - 2 * Real.pi * ⌊(theta b - theta a) / (2 * Real.pi)⌋

lemma two_pi_pos : 0 < 2 * Real.pi := mul_pos two_pos Real.pi_pos

lemma deltaOf_nonneg (a b : ℝ × ℝ) : 0 ≤ deltaOf a b := by
  have h := Int.floor_le ((theta b - theta a) / (2 * Real.pi))
  have h2 : 2 * Real.pi * ⌊(theta b - theta a) / (2 * Real.pi)⌋
      ≤ 2 * Real.pi * ((theta b - theta a) / (2 * Real.pi)) :=
    mul_le_mul_of_nonneg_left h two_pi_pos.le
  have h3 : 2 * Real.pi * ((theta b - theta a) / (2 * Real.pi)) = theta b - theta a := by
    have h2pi : (2 : ℝ) * Real.pi ≠ 0 := two_pi_pos.ne'
    field_simp
  rw [h3] at h2
  rw [deltaOf]
  linarith

lemma deltaOf_lt_two_pi (a b : ℝ × ℝ) : deltaOf a b < 2 * Real.pi := by
  have h := Int.lt_floor_add_one ((theta b - theta a) / (2 * Real.pi))
  have h2 : 2 * Real.pi * ((theta b - theta a) / (2 * Real.pi))
      < 2 * Real.pi * (⌊(theta b - theta a) / (2 * Real.pi)⌋ + 1) :=
    mul_lt_mul_of_pos_left h two_pi_pos
  have h3 : 2 * Real.pi * ((theta b - theta a) / (2 * Real.pi)) = theta b - theta a := by
    have h2pi : (2 : ℝ) * Real.pi ≠ 0 := two_pi_pos.ne'
    field_simp
  rw [h3] at h2
  rw [deltaOf]
  linarith

/-- The normalized angle difference when `theta a ≤ theta b`. -/
lemma deltaOf_of_le {a b : ℝ × ℝ} (h : theta a ≤ theta b) :
    deltaOf a b = theta b - theta a := by
  have hfloor : ⌊(theta b - theta a) / (2 * Real.pi)⌋ = 0 := by
    rw [Int.floor_eq_iff]
    refine ⟨?_, ?_⟩
    · rw [Int.cast_zero]
      exact div_nonneg (sub_nonneg.mpr h) two_pi_pos.le
    · rw [Int.cast_zero, zero_add, div_lt_one two_pi_pos]
      have h1 := theta_le_pi b
      have h2 := neg_pi_lt_theta a
      linarith
  rw [deltaOf, hfloor, Int.cast_zero, mul_zero, sub_zero]

/-- The normalized angle difference when `theta b < theta a`. -/
lemma deltaOf_of_lt {a b : ℝ × ℝ} (h : theta b < theta a) :
    deltaOf a b = theta b - theta a + 2 * Real.pi := by
  have hfloor : ⌊(theta b - theta a) / (2 * Real.pi)⌋ = -1 := by
    rw [Int.floor_eq_iff]
    refine ⟨?_, ?_⟩
    · rw [Int.cast_neg, Int.cast_one, le_div_iff₀ two_pi_pos]
      have h1 := theta_le_pi a
      have h2 := neg_pi_lt_theta b
      linarith
    · rw [Int.cast_neg, Int.cast_one, neg_add_cancel]
      exact div_neg_of_neg_of_pos (by linarith) two_pi_pos
  rw [deltaOf, hfloor, Int.cast_neg, Int.cast_one]
  ring

lemma deltaOf_self (a : ℝ × ℝ) : deltaOf a a = 0 := by
  rw [deltaOf, sub_self, zero_div, Int.floor_zero, Int.cast_zero, mul_zero, sub_zero]

lemma deltaOf_eq_zero_iff {a b : ℝ × ℝ} : deltaOf a b = 0 ↔ theta a = theta b := by
  have h1 := theta_le_pi a
  have h2 := neg_pi_lt_theta a
  have h3 := theta_le_pi b
  have h4 := neg_pi_lt_theta b
  constructor
  · intro h
    rw [deltaOf, sub_eq_zero] at h
    by_contra hne
    have hk : ⌊(theta b - theta a) / (2 * Real.pi)⌋ ≠ 0 := by
      intro hcon
      rw [hcon, Int.cast_zero, mul_zero] at h
      exact hne (by linarith)
    have habs : (1 : ℝ) ≤ |(⌊(theta b - theta a) / (2 * Real.pi)⌋ : ℝ)| := by
      have h5 := Int.one_le_abs hk
      rw [← Int.cast_abs]
      exact_mod_cast h5
    have h6 : |theta b - theta a|
        = 2 * Real.pi * |(⌊(theta b - theta a) / (2 * Real.pi)⌋ : ℝ)| := by
      conv_lhs => rw [h]
      rw [abs_mul, abs_of_pos two_pi_pos]
    have h7 : |theta b - theta a| < 2 * Real.pi := abs_lt.mpr ⟨by linarith, by linarith⟩
    have h8 : 2 * Real.pi * 1
        ≤ 2 * Real.pi * |(⌊(theta b - theta a) / (2 * Real.pi)⌋ : ℝ)| :=
      mul_le_mul_of_nonneg_left habs two_pi_pos.le
    rw [h6] at h7
    linarith
  · intro h
    rw [deltaOf, h, sub_self, zero_div, Int.floor_zero, Int.cast_zero, mul_zero, sub_zero]

lemma deltaOf_pos_iff_ne {a b : ℝ × ℝ} : 0 < deltaOf a b ↔ theta a ≠ theta b := by
  have hnn := deltaOf_nonneg a b
  have h0 := deltaOf_eq_zero_iff (a := a) (b := b)
  constructor
  · intro h hcon
    rw [h0.mpr hcon] at h
    exact (lt_irrefl 0) h
  · intro h
    rcases eq_or_lt_of_le hnn with h1 | h1
    · exact absurd (h0.mp h1.symm) h
    · exact h1

/-- Multiplying by a negative constant flips the sign. -/
lemma neg_mul_pos_iff {c P : ℝ} (hc : c < 0) : c * P < 0 ↔ 0 < P := by
  constructor
  · intro h
    rcases mul_neg_iff.mp h with ⟨g1, g2⟩ | ⟨g1, g2⟩
    · linarith
    · exact g2
  · intro h
    exact mul_neg_of_neg_of_pos hc h

/-- Sign of the product of the three half-angle sines, for
`x, y, x + y ∈ (-2π, 2π)`. -/
lemma sin_prod_pos_iff {x y : ℝ}
    (hx1 : -2 * Real.pi < x) (hx2 : x < 2 * Real.pi)
    (hy1 : -2 * Real.pi < y) (hy2 : y < 2 * Real.pi)
    (hxy1 : -2 * Real.pi < x + y) (hxy2 : x + y < 2 * Real.pi) :
    0 < Real.sin (x / 2) * Real.sin (y / 2) * Real.sin ((x + y) / 2) ↔
      (0 < x ∧ 0 < y) ∨ (0 < x ∧ y < 0 ∧ x + y < 0) ∨ (x < 0 ∧ 0 < y ∧ x + y < 0) := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · rcases lt_trichotomy y 0 with hy | hy | hy
    · have s1 : Real.sin (x / 2) < 0 := sin_half_neg hx1 hx
      have s2 : Real.sin (y / 2) < 0 := sin_half_neg hy1 hy
      have s3 : Real.sin ((x + y) / 2) < 0 := sin_half_neg hxy1 (by linarith)
      have hp : Real.sin (x / 2) * Real.sin (y / 2) * Real.sin ((x + y) / 2) < 0 :=
        mul_neg_of_pos_of_neg (mul_pos_of_neg_of_neg s1 s2) s3
      exact iff_of_false (not_lt_of_ge hp.le) (by
        rintro (⟨h1, -⟩ | ⟨h1, -, -⟩ | ⟨-, h1, -⟩) <;> linarith)
    · subst hy
      have hs : Real.sin ((0 : ℝ) / 2) = 0 := by rw [zero_div, Real.sin_zero]
      rw [hs, mul_zero, zero_mul]
      exact iff_of_false (lt_irrefl 0) (by
        rintro (⟨-, h1⟩ | ⟨-, h1, -⟩ | ⟨-, h1, -⟩) <;> linarith)
    · have s1 : Real.sin (x / 2) < 0 := sin_half_neg hx1 hx
      have s2 : 0 < Real.sin (y / 2) := sin_half_pos hy hy2
      rcases lt_trichotomy (x + y) 0 with hxy | hxy | hxy
      · have s3 : Real.sin ((x + y) / 2) < 0 := sin_half_neg hxy1 hxy
        have hp : 0 < Real.sin (x / 2) * Real.sin (y / 2) * Real.sin ((x + y) / 2) :=
          mul_pos_of_neg_of_neg (mul_neg_of_neg_of_pos s1 s2) s3
        exact iff_of_true hp (Or.inr (Or.inr ⟨hx, hy, hxy⟩))
      · rw [hxy]
        have hs : Real.sin ((0 : ℝ) / 2) = 0 := by rw [zero_div, Real.sin_zero]
        rw [hs, mul_zero]
        exact iff_of_false (lt_irrefl 0) (by
          rintro (⟨h1, -⟩ | ⟨h1, -, -⟩ | ⟨-, -, h1⟩) <;> linarith)
      · have s3 : 0 < Real.sin ((x + y) / 2) := sin_half_pos hxy hxy2
        have hp : Real.sin (x / 2) * Real.sin (y / 2) * Real.sin ((x + y) / 2) < 0 :=
          mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos s1 s2) s3
        exact iff_of_false (not_lt_of_ge hp.le) (by
          rintro (⟨h1, -⟩ | ⟨h1, -, -⟩ | ⟨-, -, h1⟩) <;> linarith)
  · subst hx
    have hs : Real.sin ((0 : ℝ) / 2) = 0 := by rw [zero_div, Real.sin_zero]
    rw [hs, zero_mul, zero_mul]
    exact iff_of_false (lt_irrefl 0) (by
      rintro (⟨h1, -⟩ | ⟨h1, -, -⟩ | ⟨h1, -, -⟩) <;> linarith)
  · rcases lt_trichotomy y 0 with hy | hy | hy
    · have s1 : 0 < Real.sin (x / 2) := sin_half_pos hx hx2
      have s2 : Real.sin (y / 2) < 0 := sin_half_neg hy1 hy
      rcases lt_trichotomy (x + y) 0 with hxy | hxy | hxy
      · have s3 : Real.sin ((x + y) / 2) < 0 := sin_half_neg hxy1 hxy
        have hp : 0 < Real.sin (x / 2) * Real.sin (y / 2) * Real.sin ((x + y) / 2) :=
          mul_pos_of_neg_of_neg (mul_neg_of_pos_of_neg s1 s2) s3
        exact iff_of_true hp (Or.inr (Or.inl ⟨hx, hy, hxy⟩))
      · rw [hxy]
        have hs : Real.sin ((0 : ℝ) / 2) = 0 := by rw [zero_div, Real.sin_zero]
        rw [hs, mul_zero]
        exact iff_of_false (lt_irrefl 0) (by
          rintro (⟨-, h1⟩ | ⟨-, -, h1⟩ | ⟨h1, -, -⟩) <;> linarith)
      · have s3 : 0 < Real.sin ((x + y) / 2) := sin_half_pos hxy hxy2
        have hp : Real.sin (x / 2) * Real.sin (y / 2) * Real.sin ((x + y) / 2) < 0 :=
          mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg s1 s2) s3
        exact iff_of_false (not_lt_of_ge hp.le) (by
          rintro (⟨-, h1⟩ | ⟨-, -, h1⟩ | ⟨h1, -, -⟩) <;> linarith)
    · subst hy
      have hs : Real.sin ((0 : ℝ) / 2) = 0 := by rw [zero_div, Real.sin_zero]
      rw [hs, mul_zero, zero_mul]
      exact iff_of_false (lt_irrefl 0) (by
        rintro (⟨-, h1⟩ | ⟨-, h1, -⟩ | ⟨-, h1, -⟩) <;> linarith)
    · have s1 : 0 < Real.sin (x / 2) := sin_half_pos hx hx2
      have s2 : 0 < Real.sin (y / 2) := sin_half_pos hy hy2
      have s3 : 0 < Real.sin ((x + y) / 2) := sin_half_pos (by linarith) hxy2
      have hp : 0 < Real.sin (x / 2) * Real.sin (y / 2) * Real.sin ((x + y) / 2) :=
        mul_pos (mul_pos s1 s2) s3
      exact iff_of_true hp (Or.inl ⟨hx, hy⟩)

/-- The sign of `detv (b - a) (q - a)` in terms of the cyclic order of the
angles of the three points on the circle. -/
lemma detv_neg_iff_order {R : ℝ} {a b q : ℝ × ℝ} (ha : nsq a = R ^ 2) (hb : nsq b = R ^ 2)
    (hq : nsq q = R ^ 2) (hR : 0 < R) :
    detv (b - a) (q - a) < 0 ↔
      (theta a < theta q ∧ theta q < theta b) ∨ (theta q < theta b ∧ theta b < theta a) ∨
        (theta b < theta a ∧ theta a < theta q) := by
  have hsign := arc_sign ha hb hq hR
  have hb1 := neg_pi_lt_theta b
  have hb2 := theta_le_pi b
  have ha1 := neg_pi_lt_theta a
  have ha2 := theta_le_pi a
  have hq1 := neg_pi_lt_theta q
  have hq2 := theta_le_pi q
  have hdet_iff : detv (b - a) (q - a) < 0 ↔
      0 < Real.sin ((theta b - theta q) / 2) * Real.sin ((theta q - theta a) / 2) *
        Real.sin ((theta b - theta a) / 2) := by
    have hR4 : (-4 : ℝ) * R ^ 2 < 0 := mul_neg_of_neg_of_pos (by norm_num) (pow_pos hR 2)
    rw [hsign]
    have e : (-4 : ℝ) * R ^ 2 * Real.sin ((theta b - theta q) / 2)
        * Real.sin ((theta q - theta a) / 2) * Real.sin ((theta b - theta a) / 2)
        = (-4 * R ^ 2) * (Real.sin ((theta b - theta q) / 2)
          * Real.sin ((theta q - theta a) / 2) * Real.sin ((theta b - theta a) / 2)) := by ring
    rw [e]
    exact neg_mul_pos_iff hR4
  rw [hdet_iff]
  have hsp := sin_prod_pos_iff (x := theta b - theta q) (y := theta q - theta a)
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  have hxy : theta b - theta q + (theta q - theta a) = theta b - theta a := by ring
  rw [hxy] at hsp
  rw [hsp]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
    · exact Or.inl ⟨by linarith, by linarith⟩
    · exact Or.inr (Or.inl ⟨by linarith, by linarith⟩)
    · exact Or.inr (Or.inr ⟨by linarith, by linarith⟩)
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inl ⟨by linarith, by linarith⟩
    · exact Or.inr (Or.inl ⟨by linarith, by linarith, by linarith⟩)
    · exact Or.inr (Or.inr ⟨by linarith, by linarith, by linarith⟩)

/-- The `deltaOf` interval condition in terms of the cyclic order of the
angles of the three points. -/
lemma deltaOf_lt_iff_order {a b q : ℝ × ℝ} :
    (0 < deltaOf a q ∧ deltaOf a q < deltaOf a b) ↔
      (theta a < theta q ∧ theta q < theta b) ∨ (theta q < theta b ∧ theta b < theta a) ∨
        (theta b < theta a ∧ theta a < theta q) := by
  have ha1 := neg_pi_lt_theta a
  have ha2 := theta_le_pi a
  have hb1 := neg_pi_lt_theta b
  have hb2 := theta_le_pi b
  have hq1 := neg_pi_lt_theta q
  have hq2 := theta_le_pi q
  rcases lt_trichotomy (theta a) (theta b) with hab | hab | hab
  · rw [deltaOf_of_le hab.le]
    rcases lt_trichotomy (theta q) (theta a) with hqa | hqa | hqa
    · rw [deltaOf_of_lt hqa]
      exact iff_of_false (fun h => by linarith [h.2]) (by
        rintro (⟨h1, -⟩ | ⟨-, h1⟩ | ⟨h1, -⟩) <;> linarith)
    · have hdq : deltaOf a q = 0 := by
        rw [deltaOf_of_le (a := a) (b := q) (le_of_eq hqa.symm)]
        linarith
      rw [hdq]
      exact iff_of_false (fun h => absurd h.1 (lt_irrefl 0)) (by
        rintro (⟨h1, -⟩ | ⟨-, h1⟩ | ⟨h1, -⟩) <;> linarith)
    · rw [deltaOf_of_le hqa.le]
      rcases lt_trichotomy (theta q) (theta b) with hqb | hqb | hqb
      · exact iff_of_true ⟨by linarith, by linarith⟩ (Or.inl ⟨hqa, hqb⟩)
      · rw [hqb]
        exact iff_of_false (fun h => absurd h.2 (lt_irrefl _)) (by
          rintro (⟨-, h1⟩ | ⟨h1, -⟩ | ⟨h1, -⟩) <;> linarith)
      · exact iff_of_false (fun h => by linarith [h.2]) (by
          rintro (⟨-, h1⟩ | ⟨h1, -⟩ | ⟨h1, -⟩) <;> linarith)
  · have hdb : deltaOf a b = 0 := by
      rw [deltaOf_of_le (a := a) (b := b) (le_of_eq hab)]
      linarith
    rw [hdb]
    have hnn := deltaOf_nonneg a q
    exact iff_of_false (fun h => by linarith [h.2]) (by
      rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩) <;> linarith [hab])
  · rw [deltaOf_of_lt hab]
    rcases lt_trichotomy (theta q) (theta a) with hqa | hqa | hqa
    · rw [deltaOf_of_lt hqa]
      rcases lt_trichotomy (theta q) (theta b) with hqb | hqb | hqb
      · exact iff_of_true ⟨by linarith, by linarith⟩ (Or.inr (Or.inl ⟨hqb, hab⟩))
      · rw [hqb]
        exact iff_of_false (fun h => absurd h.2 (lt_irrefl _)) (by
          rintro (⟨-, h1⟩ | ⟨h1, -⟩ | ⟨-, h1⟩) <;> linarith)
      · exact iff_of_false (fun h => by linarith [h.2]) (by
          rintro (⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, h1⟩) <;> linarith)
    · have hdq : deltaOf a q = 0 := by
        rw [deltaOf_of_le (a := a) (b := q) (le_of_eq hqa.symm)]
        linarith
      rw [hdq]
      exact iff_of_false (fun h => absurd h.1 (lt_irrefl 0)) (by
        rintro (⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, h1⟩) <;> linarith)
    · rw [deltaOf_of_le hqa.le]
      exact iff_of_true ⟨by linarith, by linarith⟩ (Or.inr (Or.inr ⟨hab, hqa⟩))

/-- The full dictionary between the determinant sign and the normalized
angle differences: `q` is on the counterclockwise arc from `a` to `b`. -/
lemma detv_neg_iff_deltaOf {R : ℝ} {a b q : ℝ × ℝ} (ha : nsq a = R ^ 2) (hb : nsq b = R ^ 2)
    (hq : nsq q = R ^ 2) (hR : 0 < R) :
    detv (b - a) (q - a) < 0 ↔ 0 < deltaOf a q ∧ deltaOf a q < deltaOf a b :=
  (detv_neg_iff_order ha hb hq hR).trans (deltaOf_lt_iff_order).symm

/-- `q` lies on the counterclockwise open arc from `a` to `b` on the circle
of circle endpoints. -/
@[reducible] def arcPred (hn : 2 ≤ n) (a b q : Fin n × Bool) : Prop :=
  detv (C.circlePt hn b - C.circlePt hn a) (C.circlePt hn q - C.circlePt hn a) < 0

/-- The arc predicate in terms of normalized angle differences. -/
lemma arcPred_congr (hn : 2 ≤ n) (a b q : Fin n × Bool) :
    C.arcPred hn a b q ↔
      0 < deltaOf (C.circlePt hn a) (C.circlePt hn q) ∧
        deltaOf (C.circlePt hn a) (C.circlePt hn q) <
          deltaOf (C.circlePt hn a) (C.circlePt hn b) :=
  detv_neg_iff_deltaOf (C.circlePt_nsq hn a) (C.circlePt_nsq hn b) (C.circlePt_nsq hn q)
    C.radius_pos

/-- `k` separates the circle endpoints of `a` and `b` iff the segment
through them meets the open chord of `k`. -/
lemma separates_iff_mem_openChord (hn : 2 ≤ n) {a b : Fin n × Bool} {k : Fin n}
    (hab : a.1 ≠ b.1) :
    C.separates k (C.circlePt hn a) (C.circlePt hn b) ↔
      ∃ Y, Y ∈ openSegment ℝ (C.circlePt hn a) (C.circlePt hn b) ∧
        Y ∈ C.openChord hn k := by
  constructor
  · exact C.separates_properCross hn hab
  · intro ⟨Y, hY1, hY2⟩
    have hd : detv (C.circlePt hn b - C.circlePt hn a)
        ((C.circlePts hn k).2 - (C.circlePts hn k).1) ≠ 0 := by
      have hD : detv (C.dir k) (C.circlePt hn b - C.circlePt hn a) ≠ 0 := by
        intro hd2
        obtain ⟨t, ht, hYt⟩ := mem_openSegment_iff_param.mp hY1
        have hYk : detv (C.dir k) (Y - (C.seg k).1) = 0 := by
          rw [openChord, mem_openSegment_iff_param] at hY2
          obtain ⟨r, hr, hYr⟩ := hY2
          rw [hYr]
          have e : (C.circlePts hn k).1 + r • ((C.circlePts hn k).2 - (C.circlePts hn k).1)
              = (C.seg k).1 + ((C.circleParams hn k).1 + r * ((C.circleParams hn k).2 - (C.circleParams hn k).1)) • C.dir k := by
            rw [C.openChord_dir hn k, circlePts_fst_eq, smul_smul]
            module
          rw [e]
          have e2 : (C.seg k).1 + ((C.circleParams hn k).1 + r * ((C.circleParams hn k).2 - (C.circleParams hn k).1)) • C.dir k - (C.seg k).1
              = ((C.circleParams hn k).1 + r * ((C.circleParams hn k).2 - (C.circleParams hn k).1)) • C.dir k := by abel
          rw [e2, detv_smul_right, detv_self, mul_zero]
        have hAon : detv (C.dir k) (C.circlePt hn a - (C.seg k).1) = 0 := by
          have e : C.circlePt hn a - (C.seg k).1
              = (C.circlePt hn a - Y) + (Y - (C.seg k).1) := by abel
          rw [e, detv_add_right, hYk, add_zero]
          have e2 : C.circlePt hn a - Y = -t • (C.circlePt hn b - C.circlePt hn a) := by
            rw [hYt]
            module
          rw [e2, detv_smul_right, hd2, mul_zero]
        have hBon : detv (C.dir k) (C.circlePt hn b - (C.seg k).1) = 0 := by
          have e : C.circlePt hn b - (C.seg k).1
              = (C.circlePt hn b - Y) + (Y - (C.seg k).1) := by abel
          rw [e, detv_add_right, hYk, add_zero]
          have e2 : C.circlePt hn b - Y = (1 - t) • (C.circlePt hn b - C.circlePt hn a) := by
            rw [hYt]
            module
          rw [e2, detv_smul_right, hd2, mul_zero]
        have hAin := C.eq_circlePts_of_mem_line_circle hn k (C.circlePt_nsq hn a) hAon
        have hBin := C.eq_circlePts_of_mem_line_circle hn k (C.circlePt_nsq hn b) hBon
        have hak : a.1 = k := by
          rcases hAin with hAin | hAin
          · have h3 : C.circlePt hn a = C.circlePt hn ⟨k, false⟩ := by
              rw [hAin]
              show (C.circlePts hn k).1 = if false = true then (C.circlePts hn k).2 else (C.circlePts hn k).1
              rw [if_neg (show ¬(false = true) from by simp)]
            have h4 := C.circlePt_injective hn h3
            rw [h4]
          · have h3 : C.circlePt hn a = C.circlePt hn ⟨k, true⟩ := by
              rw [hAin]
              show (C.circlePts hn k).2 = if true = true then (C.circlePts hn k).2 else (C.circlePts hn k).1
              rw [if_pos rfl]
            have h4 := C.circlePt_injective hn h3
            rw [h4]
        have hbk : b.1 = k := by
          rcases hBin with hBin | hBin
          · have h3 : C.circlePt hn b = C.circlePt hn ⟨k, false⟩ := by
              rw [hBin]
              show (C.circlePts hn k).1 = if false = true then (C.circlePts hn k).2 else (C.circlePts hn k).1
              rw [if_neg (show ¬(false = true) from by simp)]
            have h4 := C.circlePt_injective hn h3
            rw [h4]
          · have h3 : C.circlePt hn b = C.circlePt hn ⟨k, true⟩ := by
              rw [hBin]
              show (C.circlePts hn k).2 = if true = true then (C.circlePts hn k).2 else (C.circlePts hn k).1
              rw [if_pos rfl]
            have h4 := C.circlePt_injective hn h3
            rw [h4]
        rw [hak, hbk] at hab
        exact hab rfl
      rw [C.openChord_dir hn k, detv_smul_right]
      have hlt := C.circleParams_lt hn k
      have hD' : detv (C.circlePt hn b - C.circlePt hn a) (C.dir k) ≠ 0 := by
        rw [detv_antisymm]
        exact neg_ne_zero.mpr hD
      exact mul_ne_zero (by linarith) hD' 
    have h1 := (oppSide_of_properCross ⟨hY1, hY2⟩ hd).2
    -- OppSide Z₋ (Z₊-Z₋) A B gives detv w (A-p)·detv w (B-p) < 0
    have h2 : detv (C.dir k) (C.circlePt hn a - (C.seg k).1) *
        detv (C.dir k) (C.circlePt hn b - (C.seg k).1) < 0 := by
      have e1 : detv ((C.circlePts hn k).2 - (C.circlePts hn k).1)
          (C.circlePt hn a - (C.circlePts hn k).1)
          = ((C.circleParams hn k).2 - (C.circleParams hn k).1) *
            detv (C.dir k) (C.circlePt hn a - (C.seg k).1) := by
        rw [C.openChord_dir hn k, detv_smul_left]
        have e3 : detv (C.dir k) (C.circlePt hn a - (C.circlePts hn k).1)
            = detv (C.dir k) (C.circlePt hn a - (C.seg k).1) := by
          have e4 : C.circlePt hn a - (C.circlePts hn k).1
              = (C.circlePt hn a - (C.seg k).1) - ((C.circlePts hn k).1 - (C.seg k).1) := by abel
          rw [e4, detv_sub_right, C.dir_circlePts_fst_sub hn k, sub_zero]
        rw [e3]
      have e2 : detv ((C.circlePts hn k).2 - (C.circlePts hn k).1)
          (C.circlePt hn b - (C.circlePts hn k).1)
          = ((C.circleParams hn k).2 - (C.circleParams hn k).1) *
            detv (C.dir k) (C.circlePt hn b - (C.seg k).1) := by
        rw [C.openChord_dir hn k, detv_smul_left]
        have e3 : detv (C.dir k) (C.circlePt hn b - (C.circlePts hn k).1)
            = detv (C.dir k) (C.circlePt hn b - (C.seg k).1) := by
          have e4 : C.circlePt hn b - (C.circlePts hn k).1
              = (C.circlePt hn b - (C.seg k).1) - ((C.circlePts hn k).1 - (C.seg k).1) := by abel
          rw [e4, detv_sub_right, C.dir_circlePts_fst_sub hn k, sub_zero]
        rw [e3]
      have hlt := C.circleParams_lt hn k
      have hpos : 0 < ((C.circleParams hn k).2 - (C.circleParams hn k).1) ^ 2 :=
        sq_pos_of_ne_zero (by linarith)
      have h1c : detv ((C.circlePts hn k).2 - (C.circlePts hn k).1)
          (C.circlePt hn a - (C.circlePts hn k).1) *
        detv ((C.circlePts hn k).2 - (C.circlePts hn k).1)
          (C.circlePt hn b - (C.circlePts hn k).1) < 0 := h1
      rw [e1, e2] at h1c
      have h1c2 : (detv (C.dir k) (C.circlePt hn a - (C.seg k).1) * detv (C.dir k) (C.circlePt hn b - (C.seg k).1)) *
          ((C.circleParams hn k).2 - (C.circleParams hn k).1) ^ 2 < 0 := by
        nlinarith [h1c]
      exact neg_of_mul_neg_left h1c2 hpos.le
    exact h2

/-! ## Cyclic labeling, part 4: the cyclic order and the label -/

/-- The angle of a circle endpoint. -/
noncomputable def thetaPt (hn : 2 ≤ n) (e : Fin n × Bool) : ℝ := theta (C.circlePt hn e)

lemma thetaPt_injective (hn : 2 ≤ n) : Function.Injective (C.thetaPt hn) := fun e f h =>
  C.circlePt_injective hn (arg_eq_of_nsq_eq (C.circlePt_nsq hn e) (C.circlePt_nsq hn f)
    C.radius_pos h)

/-- The rank of a circle endpoint in the angular order: the number of
endpoints with strictly smaller angle. -/
noncomputable def arcRank (hn : 2 ≤ n) (e : Fin n × Bool) : ℕ :=
  (Finset.univ.filter fun e' => C.thetaPt hn e' < C.thetaPt hn e).card

lemma arcRank_lt (hn : 2 ≤ n) (e : Fin n × Bool) : C.arcRank hn e < 2 * n := by
  have hss : (Finset.univ.filter fun e' => C.thetaPt hn e' < C.thetaPt hn e) ⊂ Finset.univ := by
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨Finset.filter_subset _ _, ?_⟩
    intro hcon
    have hmem : e ∈ (Finset.univ.filter fun e' => C.thetaPt hn e' < C.thetaPt hn e) := by
      rw [hcon]
      exact Finset.mem_univ e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, lt_irrefl] at hmem
  have h1 := Finset.card_lt_card hss
  rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool] at h1
  show (Finset.univ.filter fun e' => C.thetaPt hn e' < C.thetaPt hn e).card < 2 * n
  omega

lemma thetaPt_lt_iff_arcRank_lt (hn : 2 ≤ n) (e f : Fin n × Bool) :
    C.thetaPt hn e < C.thetaPt hn f ↔ C.arcRank hn e < C.arcRank hn f := by
  constructor
  · intro h
    have hss : (Finset.univ.filter fun e' => C.thetaPt hn e' < C.thetaPt hn e) ⊂
        (Finset.univ.filter fun e' => C.thetaPt hn e' < C.thetaPt hn f) := by
      rw [Finset.ssubset_iff_subset_ne]
      refine ⟨?_, ?_⟩
      · intro g hg
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
        exact lt_trans hg h
      · intro hcon
        have hmem : e ∈ (Finset.univ.filter fun e' => C.thetaPt hn e' < C.thetaPt hn f) := by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact h
        rw [← hcon] at hmem
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, lt_irrefl] at hmem
    exact Finset.card_lt_card hss
  · intro h
    rcases lt_trichotomy (C.thetaPt hn e) (C.thetaPt hn f) with h1 | h1 | h1
    · exact h1
    · exfalso
      have heq : (Finset.univ.filter fun e' => C.thetaPt hn e' < C.thetaPt hn e)
          = (Finset.univ.filter fun e' => C.thetaPt hn e' < C.thetaPt hn f) := by
        apply Finset.filter_congr
        intro g _
        rw [h1]
      have h2 : C.arcRank hn e = C.arcRank hn f := by
        show (Finset.univ.filter fun e' => C.thetaPt hn e' < C.thetaPt hn e).card
          = (Finset.univ.filter fun e' => C.thetaPt hn e' < C.thetaPt hn f).card
        rw [heq]
      omega
    · exfalso
      have hss : (Finset.univ.filter fun e' => C.thetaPt hn e' < C.thetaPt hn f) ⊂
          (Finset.univ.filter fun e' => C.thetaPt hn e' < C.thetaPt hn e) := by
        rw [Finset.ssubset_iff_subset_ne]
        refine ⟨?_, ?_⟩
        · intro g hg
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
          exact lt_trans hg h1
        · intro hcon
          have hmem : f ∈ (Finset.univ.filter fun e' => C.thetaPt hn e' < C.thetaPt hn e) := by
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            exact h1
          rw [← hcon] at hmem
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, lt_irrefl] at hmem
      have h2 : C.arcRank hn f < C.arcRank hn e := Finset.card_lt_card hss
      omega

lemma arcRank_injective (hn : 2 ≤ n) : Function.Injective (C.arcRank hn) := by
  intro e f h
  by_contra hne
  have hθ : C.thetaPt hn e ≠ C.thetaPt hn f := fun h2 => hne (C.thetaPt_injective hn h2)
  rcases lt_or_gt_of_ne hθ with h1 | h1
  · have h2 := (C.thetaPt_lt_iff_arcRank_lt hn e f).mp h1
    omega
  · have h2 := (C.thetaPt_lt_iff_arcRank_lt hn f e).mp h1
    omega

/-- The angular rank as an element of `Fin (2 * n)`. -/
noncomputable def arcRankFin (hn : 2 ≤ n) (e : Fin n × Bool) : Fin (2 * n) :=
  ⟨C.arcRank hn e, C.arcRank_lt hn e⟩

lemma arcRankFin_bijective (hn : 2 ≤ n) : Function.Bijective (C.arcRankFin hn) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, ?_⟩
  · intro e f h
    exact C.arcRank_injective hn (Fin.ext_iff.mp h)
  · rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, Fintype.card_fin]
    omega

/-- The equivalence between circle endpoints and `Fin (2 * n)` given by the
angular rank. -/
noncomputable def arcRankEquiv (hn : 2 ≤ n) : (Fin n × Bool) ≃ Fin (2 * n) :=
  Equiv.ofBijective _ (C.arcRankFin_bijective hn)

lemma arcRankEquiv_apply (hn : 2 ≤ n) (e : Fin n × Bool) :
    C.arcRankEquiv hn e = C.arcRankFin hn e := rfl

/-- The equivalence `ZMod N ≃ Fin N` via `ZMod.val`. -/
noncomputable def zmodFinEquiv (N : ℕ) [NeZero N] : ZMod N ≃ Fin N := by
  apply Equiv.ofBijective (fun m => ⟨m.val, ZMod.val_lt m⟩)
  constructor
  · intro x y h
    exact ZMod.val_injective _ (Fin.ext_iff.mp h)
  · intro j
    refine ⟨(j.val : ZMod N), ?_⟩
    exact Fin.ext (ZMod.val_natCast_of_lt j.isLt)

/-- The cyclic labeling as an equivalence: `label hn m` is the circle
endpoint of angular rank `m.val`. -/
noncomputable def labelEquiv (hn : 2 ≤ n) : ZMod (2 * n) ≃ (Fin n × Bool) :=
  letI : NeZero (2 * n) := ⟨by omega⟩
  (zmodFinEquiv (2 * n)).trans (C.arcRankEquiv hn).symm

/-- The cyclic labeling of the circle endpoints by `ZMod (2 * n)` in
increasing angle order. -/
noncomputable def label (hn : 2 ≤ n) (m : ZMod (2 * n)) : Fin n × Bool :=
  C.labelEquiv hn m

lemma label_injective (hn : 2 ≤ n) : Function.Injective (C.label hn) :=
  (C.labelEquiv hn).injective

lemma label_surjective (hn : 2 ≤ n) : Function.Surjective (C.label hn) :=
  (C.labelEquiv hn).surjective

lemma label_bijective (hn : 2 ≤ n) : Function.Bijective (C.label hn) :=
  (C.labelEquiv hn).bijective

lemma arcRank_label (hn : 2 ≤ n) (m : ZMod (2 * n)) :
    C.arcRank hn (C.label hn m) = m.val := by
  haveI : NeZero (2 * n) := ⟨by omega⟩
  have h1 : C.arcRankFin hn (C.label hn m) = ⟨m.val, ZMod.val_lt m⟩ := by
    have h2 : C.arcRankEquiv hn (C.label hn m) = (zmodFinEquiv (2 * n)) m :=
      Equiv.apply_symm_apply _ _
    rw [arcRankEquiv_apply] at h2
    exact h2
  exact congrArg Fin.val h1

lemma theta_label_lt_iff (hn : 2 ≤ n) (x y : ZMod (2 * n)) :
    C.thetaPt hn (C.label hn x) < C.thetaPt hn (C.label hn y) ↔ x.val < y.val := by
  rw [thetaPt_lt_iff_arcRank_lt, C.arcRank_label hn x, C.arcRank_label hn y]

/-- Variant of `theta_label_lt_iff` with `thetaPt` unfolded. -/
lemma theta_circlePt_label_lt_iff (hn : 2 ≤ n) (x y : ZMod (2 * n)) :
    theta (C.circlePt hn (C.label hn x)) < theta (C.circlePt hn (C.label hn y)) ↔
      x.val < y.val :=
  C.theta_label_lt_iff hn x y

lemma zmod_val_sub_of_le {N : ℕ} [NeZero N] {x y : ZMod N} (h : y.val ≤ x.val) :
    (x - y).val = x.val - y.val := by
  have hN : 0 < N := NeZero.pos N
  have h1 : x = y + (x - y) := by ring
  have h2 := congrArg ZMod.val h1
  rw [ZMod.val_add] at h2
  have hv : (x - y).val < N := ZMod.val_lt _
  have hy : y.val < N := ZMod.val_lt _
  have hx : x.val < N := ZMod.val_lt _
  rcases lt_or_ge (y.val + (x - y).val) N with h3 | h3
  · rw [Nat.mod_eq_of_lt h3] at h2
    omega
  · have h4 : (y.val + (x - y).val) % N = y.val + (x - y).val - N := by
      rw [Nat.mod_eq_sub_mod h3, Nat.mod_eq_of_lt (by omega)]
    rw [h4] at h2
    omega

lemma zmod_val_sub_of_lt {N : ℕ} [NeZero N] {x y : ZMod N} (h : x.val < y.val) :
    (x - y).val = x.val + N - y.val := by
  have hN : 0 < N := NeZero.pos N
  have h1 : x = y + (x - y) := by ring
  have h2 := congrArg ZMod.val h1
  rw [ZMod.val_add] at h2
  have hv : (x - y).val < N := ZMod.val_lt _
  have hy : y.val < N := ZMod.val_lt _
  have hx : x.val < N := ZMod.val_lt _
  rcases lt_or_ge (y.val + (x - y).val) N with h3 | h3
  · rw [Nat.mod_eq_of_lt h3] at h2
    omega
  · have h4 : (y.val + (x - y).val) % N = y.val + (x - y).val - N := by
      rw [Nat.mod_eq_sub_mod h3, Nat.mod_eq_of_lt (by omega)]
    rw [h4] at h2
    omega

/-- Comparing normalized angle differences from a labeled endpoint is the
same as comparing `ZMod` distances. -/
lemma deltaOf_label_lt_iff (hn : 2 ≤ n) (a b c : ZMod (2 * n)) :
    deltaOf (C.circlePt hn (C.label hn a)) (C.circlePt hn (C.label hn c)) <
      deltaOf (C.circlePt hn (C.label hn a)) (C.circlePt hn (C.label hn b)) ↔
        (c - a).val < (b - a).val := by
  haveI : NeZero (2 * n) := ⟨by omega⟩
  have haN : a.val < 2 * n := ZMod.val_lt _
  have hbN : b.val < 2 * n := ZMod.val_lt _
  have hcN : c.val < 2 * n := ZMod.val_lt _
  have ha1 : -Real.pi < theta (C.circlePt hn (C.label hn a)) := neg_pi_lt_theta _
  have ha2 : theta (C.circlePt hn (C.label hn a)) ≤ Real.pi := theta_le_pi _
  have hb1 : -Real.pi < theta (C.circlePt hn (C.label hn b)) := neg_pi_lt_theta _
  have hb2 : theta (C.circlePt hn (C.label hn b)) ≤ Real.pi := theta_le_pi _
  have hc1 : -Real.pi < theta (C.circlePt hn (C.label hn c)) := neg_pi_lt_theta _
  have hc2 : theta (C.circlePt hn (C.label hn c)) ≤ Real.pi := theta_le_pi _
  rcases le_or_gt (ZMod.val a) (ZMod.val c) with hca | hca <;>
    rcases le_or_gt (ZMod.val a) (ZMod.val b) with hba | hba
  · have hΘca : theta (C.circlePt hn (C.label hn a)) ≤ theta (C.circlePt hn (C.label hn c)) := by
      by_contra hcon
      push Not at hcon
      have h2 := (C.theta_circlePt_label_lt_iff hn c a).mp hcon
      omega
    have hΘba : theta (C.circlePt hn (C.label hn a)) ≤ theta (C.circlePt hn (C.label hn b)) := by
      by_contra hcon
      push Not at hcon
      have h2 := (C.theta_circlePt_label_lt_iff hn b a).mp hcon
      omega
    rw [deltaOf_of_le hΘca, deltaOf_of_le hΘba, zmod_val_sub_of_le hca, zmod_val_sub_of_le hba]
    constructor
    · intro h
      have h2 : theta (C.circlePt hn (C.label hn c)) < theta (C.circlePt hn (C.label hn b)) := by
        linarith
      have h3 := (C.theta_circlePt_label_lt_iff hn c b).mp h2
      omega
    · intro h
      have h2 : c.val < b.val := by omega
      have h3 := (C.theta_circlePt_label_lt_iff hn c b).mpr h2
      linarith
  · have hΘca : theta (C.circlePt hn (C.label hn a)) ≤ theta (C.circlePt hn (C.label hn c)) := by
      by_contra hcon
      push Not at hcon
      have h2 := (C.theta_circlePt_label_lt_iff hn c a).mp hcon
      omega
    have hΘba : theta (C.circlePt hn (C.label hn b)) < theta (C.circlePt hn (C.label hn a)) :=
      (C.theta_circlePt_label_lt_iff hn b a).mpr hba
    rw [deltaOf_of_le hΘca, deltaOf_of_lt hΘba, zmod_val_sub_of_le hca, zmod_val_sub_of_lt hba]
    exact iff_of_true (by linarith) (by omega)
  · have hΘca : theta (C.circlePt hn (C.label hn c)) < theta (C.circlePt hn (C.label hn a)) :=
      (C.theta_circlePt_label_lt_iff hn c a).mpr hca
    have hΘba : theta (C.circlePt hn (C.label hn a)) ≤ theta (C.circlePt hn (C.label hn b)) := by
      by_contra hcon
      push Not at hcon
      have h2 := (C.theta_circlePt_label_lt_iff hn b a).mp hcon
      omega
    rw [deltaOf_of_lt hΘca, deltaOf_of_le hΘba, zmod_val_sub_of_lt hca, zmod_val_sub_of_le hba]
    exact iff_of_false (not_lt_of_ge (by linarith)) (by omega)
  · have hΘca : theta (C.circlePt hn (C.label hn c)) < theta (C.circlePt hn (C.label hn a)) :=
      (C.theta_circlePt_label_lt_iff hn c a).mpr hca
    have hΘba : theta (C.circlePt hn (C.label hn b)) < theta (C.circlePt hn (C.label hn a)) :=
      (C.theta_circlePt_label_lt_iff hn b a).mpr hba
    rw [deltaOf_of_lt hΘca, deltaOf_of_lt hΘba, zmod_val_sub_of_lt hca, zmod_val_sub_of_lt hba]
    constructor
    · intro h
      have h2 : theta (C.circlePt hn (C.label hn c)) < theta (C.circlePt hn (C.label hn b)) := by
        linarith
      have h3 := (C.theta_circlePt_label_lt_iff hn c b).mp h2
      omega
    · intro h
      have h2 : c.val < b.val := by omega
      have h3 := (C.theta_circlePt_label_lt_iff hn c b).mpr h2
      linarith

/-- The arc predicate between labeled endpoints, in terms of `ZMod`
distances. -/
lemma arcPred_label_iff (hn : 2 ≤ n) (a b c : ZMod (2 * n)) :
    C.arcPred hn (C.label hn a) (C.label hn b) (C.label hn c) ↔
      0 < (c - a).val ∧ (c - a).val < (b - a).val := by
  haveI : NeZero (2 * n) := ⟨by omega⟩
  rw [C.arcPred_congr hn (C.label hn a) (C.label hn b) (C.label hn c)]
  rw [deltaOf_pos_iff_ne, C.deltaOf_label_lt_iff hn a b c]
  have hca : (theta (C.circlePt hn (C.label hn a)) ≠ theta (C.circlePt hn (C.label hn c))) ↔
      (0 < (c - a).val) := by
    constructor
    · intro h
      by_contra hcon
      push Not at hcon
      have h0 : (c - a).val = 0 := Nat.le_zero.mp hcon
      have h1 : c - a = 0 := (ZMod.val_eq_zero _).mp h0
      have h2 : c = a := sub_eq_zero.mp h1
      exact h (by rw [h2])
    · intro h hcon
      have h1 : C.label hn a = C.label hn c :=
        C.circlePt_injective hn (arg_eq_of_nsq_eq (C.circlePt_nsq hn _)
          (C.circlePt_nsq hn _) C.radius_pos hcon)
      have h2 : a = c := C.label_injective hn h1
      rw [h2, sub_self] at h
      rw [ZMod.val_zero] at h
      exact (lt_irrefl 0) h
  rw [hca]

/-! ## Cyclic labeling, part 5: halving and antipodality -/

/-- The determinants of the two circle endpoints of chord `i` against the
line of chord `j` (`i ≠ j`), as affine functions of the chord parameter:
they straddle the crossing of `i` and `j`. -/
lemma detv_dir_circlePt_eq (hn : 2 ≤ n) {i j : Fin n} (hij : i ≠ j) :
    ∃ tX : ℝ, tX ∈ Set.Ioo (C.circleParams hn i).1 (C.circleParams hn i).2 ∧
      detv (C.dir j) (C.circlePt hn ⟨i, false⟩ - (C.seg j).1)
        = ((C.circleParams hn i).1 - tX) * detv (C.dir j) (C.dir i) ∧
      detv (C.dir j) (C.circlePt hn ⟨i, true⟩ - (C.seg j).1)
        = ((C.circleParams hn i).2 - tX) * detv (C.dir j) (C.dir i) := by
  obtain ⟨tX, _htX01, htX, hXtX⟩ := C.xpoint_param hn i j hij
  have hXj : detv (C.dir j) (C.xpoint i j hij - (C.seg j).1) = 0 :=
    C.detv_dir_self_left (openSegment_subset_segment _ _ _ (C.xpoint_mem i j hij).2)
  have hcalc : ∀ t : ℝ, detv (C.dir j) ((C.seg i).1 + t • C.dir i - (C.seg j).1)
      = detv (C.dir j) ((C.seg i).1 - (C.seg j).1) + t * detv (C.dir j) (C.dir i) := by
    intro t
    rw [detv_sub_right, detv_add_right, detv_smul_right, detv_sub_right]
    ring
  have hXcalc := hcalc tX
  rw [← hXtX, hXj] at hXcalc
  have hbase : detv (C.dir j) ((C.seg i).1 - (C.seg j).1)
      = -tX * detv (C.dir j) (C.dir i) := by
    linarith [hXcalc]
  refine ⟨tX, htX, ?_, ?_⟩
  · have hcp : C.circlePt hn ⟨i, false⟩ = (C.seg i).1 + (C.circleParams hn i).1 • C.dir i :=
      C.circlePts_fst_eq hn i
    rw [hcp, hcalc, hbase]
    ring
  · have hcp : C.circlePt hn ⟨i, true⟩ = (C.seg i).1 + (C.circleParams hn i).2 • C.dir i :=
      C.circlePts_snd_eq hn i
    rw [hcp, hcalc, hbase]
    ring

/-- The two circle endpoints of chord `i` lie on opposite sides of the line
of chord `j` (`i ≠ j`). -/
lemma side_sign_pair (hn : 2 ≤ n) {i j : Fin n} (hij : i ≠ j) :
    detv (C.dir j) (C.circlePt hn ⟨i, false⟩ - (C.seg j).1) *
      detv (C.dir j) (C.circlePt hn ⟨i, true⟩ - (C.seg j).1) < 0 := by
  obtain ⟨tX, htX, h0, h1⟩ := C.detv_dir_circlePt_eq hn hij
  rw [h0, h1]
  have hD : detv (C.dir j) (C.dir i) ≠ 0 := by
    have h := C.dir_ne i j hij
    rw [detv_antisymm]
    exact neg_ne_zero.mpr h
  have hlt1 : (C.circleParams hn i).1 - tX < 0 := sub_neg.mpr htX.1
  have hgt2 : 0 < (C.circleParams hn i).2 - tX := sub_pos.mpr htX.2
  have hD2 : 0 < detv (C.dir j) (C.dir i) ^ 2 := sq_pos_of_ne_zero hD
  have e : ((C.circleParams hn i).1 - tX) * detv (C.dir j) (C.dir i) *
      (((C.circleParams hn i).2 - tX) * detv (C.dir j) (C.dir i))
      = ((C.circleParams hn i).1 - tX) * (((C.circleParams hn i).2 - tX) *
        detv (C.dir j) (C.dir i) ^ 2) := by ring
  rw [e]
  exact mul_neg_of_neg_of_pos hlt1 (mul_pos hgt2 hD2)

/-- No circle endpoint of a chord `i ≠ j` lies on the line of chord `j`. -/
lemma detv_dir_circlePt_ne_zero (hn : 2 ≤ n) {i j : Fin n} {q : Fin n × Bool}
    (hq : q.1 = i) (hij : i ≠ j) :
    detv (C.dir j) (C.circlePt hn q - (C.seg j).1) ≠ 0 := by
  obtain ⟨tX, htX, h0, h1⟩ := C.detv_dir_circlePt_eq hn hij
  have hD : detv (C.dir j) (C.dir i) ≠ 0 := by
    have h := C.dir_ne i j hij
    rw [detv_antisymm]
    exact neg_ne_zero.mpr h
  rcases q with ⟨qi, qb⟩
  cases qb with
  | false =>
    have hq2 : qi = i := hq
    subst hq2
    rw [h0]
    exact mul_ne_zero (sub_ne_zero.mpr htX.1.ne) hD
  | true =>
    have hq2 : qi = i := hq
    subst hq2
    rw [h1]
    exact mul_ne_zero (sub_ne_zero.mpr htX.2.ne') hD

/-- Halving: the two sides of the line of chord `j` each contain exactly
`n - 1` of the circle endpoints. -/
lemma card_sides (hn : 2 ≤ n) (j : Fin n) :
    (Finset.univ.filter fun q : Fin n × Bool =>
        0 < detv (C.dir j) (C.circlePt hn q - (C.seg j).1)).card = n - 1 ∧
      (Finset.univ.filter fun q : Fin n × Bool =>
        detv (C.dir j) (C.circlePt hn q - (C.seg j).1) < 0).card = n - 1 := by
  have hpair : ∀ q : Fin n × Bool, q.1 ≠ j →
      detv (C.dir j) (C.circlePt hn q - (C.seg j).1) *
        detv (C.dir j) (C.circlePt hn ⟨q.1, !q.2⟩ - (C.seg j).1) < 0 := by
    intro q hq
    have h := C.side_sign_pair hn hq
    rcases q with ⟨qi, qb⟩
    cases qb with
    | false =>
      show detv (C.dir j) (C.circlePt hn ⟨qi, false⟩ - (C.seg j).1) *
        detv (C.dir j) (C.circlePt hn ⟨qi, true⟩ - (C.seg j).1) < 0
      exact h
    | true =>
      show detv (C.dir j) (C.circlePt hn ⟨qi, true⟩ - (C.seg j).1) *
        detv (C.dir j) (C.circlePt hn ⟨qi, false⟩ - (C.seg j).1) < 0
      rw [mul_comm]
      exact h
  have honline : (Finset.univ.filter fun q : Fin n × Bool => q.1 = j)
      = {⟨j, false⟩, ⟨j, true⟩} := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro hq
      rcases q with ⟨qi, qb⟩
      cases qb with
      | false => exact Or.inl (Prod.ext hq rfl)
      | true => exact Or.inr (Prod.ext hq rfl)
    · rintro (rfl | rfl) <;> rfl
  have hcardonline : ({⟨j, false⟩, ⟨j, true⟩} : Finset (Fin n × Bool)).card = 2 :=
    Finset.card_pair (fun h => Bool.false_ne_true (congrArg Prod.snd h))
  have hT : (Finset.univ.filter fun q : Fin n × Bool => q.1 ≠ j).card = 2 * n - 2 := by
    have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n × Bool)))
      (fun q => q.1 = j)
    rw [honline, hcardonline] at h
    have h2n : (Finset.univ : Finset (Fin n × Bool)).card = 2 * n := by
      rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
      omega
    rw [h2n] at h
    have hconv : (Finset.univ.filter fun q : Fin n × Bool => q.1 ≠ j)
        = (Finset.univ.filter fun q : Fin n × Bool => ¬ q.1 = j) := by
      apply Finset.filter_congr
      intro q _
      exact Iff.rfl
    rw [hconv]
    omega
  have hunion : (Finset.univ.filter fun q : Fin n × Bool =>
        0 < detv (C.dir j) (C.circlePt hn q - (C.seg j).1)) ∪
      (Finset.univ.filter fun q : Fin n × Bool =>
        detv (C.dir j) (C.circlePt hn q - (C.seg j).1) < 0)
      = Finset.univ.filter fun q : Fin n × Bool => q.1 ≠ j := by
    rw [← Finset.filter_or]
    apply Finset.filter_congr
    intro q _
    constructor
    · intro h hcon
      have h0 := C.circlePt_on_line hn q
      rw [hcon] at h0
      rcases h with h1 | h1 <;> linarith [h0, h1]
    · intro hq
      have hne := C.detv_dir_circlePt_ne_zero hn rfl hq
      rcases lt_or_gt_of_ne hne with h1 | h1
      · exact Or.inr h1
      · exact Or.inl h1
  have hdisj : Disjoint
      (Finset.univ.filter fun q : Fin n × Bool =>
        0 < detv (C.dir j) (C.circlePt hn q - (C.seg j).1))
      (Finset.univ.filter fun q : Fin n × Bool =>
        detv (C.dir j) (C.circlePt hn q - (C.seg j).1) < 0) := by
    rw [Finset.disjoint_left]
    intro q h1 h2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    linarith
  have hcard := Finset.card_union_of_disjoint hdisj
  rw [hunion, hT] at hcard
  have hcardEq : (Finset.univ.filter fun q : Fin n × Bool =>
        0 < detv (C.dir j) (C.circlePt hn q - (C.seg j).1)).card
      = (Finset.univ.filter fun q : Fin n × Bool =>
        detv (C.dir j) (C.circlePt hn q - (C.seg j).1) < 0).card := by
    apply Finset.card_bij (fun q _ => ⟨q.1, !q.2⟩)
    · intro q hq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
      have hq1 : q.1 ≠ j := by
        intro hcon
        have h0 := C.circlePt_on_line hn q
        rw [hcon] at h0
        linarith [h0, hq]
      have hp := hpair q hq1
      rcases mul_neg_iff.mp hp with ⟨g1, g2⟩ | ⟨g1, g2⟩
      · exact g2
      · linarith [hq]
    · intro q1 _ q2 _ h
      obtain ⟨h1, h2⟩ := Prod.ext_iff.mp h
      have h3 : q1.2 = q2.2 := by
        have h4 := congrArg Bool.not h2
        rw [Bool.not_not, Bool.not_not] at h4
        exact h4
      exact Prod.ext h1 h3
    · intro q hq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
      refine ⟨⟨q.1, !q.2⟩, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        have hq1 : q.1 ≠ j := by
          intro hcon
          have h0 := C.circlePt_on_line hn q
          rw [hcon] at h0
          linarith [h0, hq]
        have hp := hpair q hq1
        rcases mul_neg_iff.mp hp with ⟨g1, g2⟩ | ⟨g1, g2⟩
        · linarith [hq]
        · exact g2
      · show (⟨q.1, !(!q.2)⟩ : Fin n × Bool) = q
        rw [Bool.not_not]
  have h2n : 2 * n - 2 = 2 * (n - 1) := by omega
  rw [h2n] at hcard
  constructor <;> omega

/-- Halving: the counterclockwise arc from a circle endpoint to its partner
contains exactly `n - 1` circle endpoints. -/
lemma arc_card_partner (hn : 2 ≤ n) (e : Fin n × Bool) :
    (Finset.univ.filter fun q : Fin n × Bool =>
      C.arcPred hn e ⟨e.1, !e.2⟩ q).card = n - 1 := by
  obtain ⟨hp, hn2⟩ := C.card_sides hn e.1
  have hline : detv (C.dir e.1) (C.circlePt hn e - (C.seg e.1).1) = 0 :=
    C.circlePt_on_line hn e
  have hqe : ∀ q : Fin n × Bool,
      detv (C.dir e.1) (C.circlePt hn q - C.circlePt hn e)
        = detv (C.dir e.1) (C.circlePt hn q - (C.seg e.1).1) := by
    intro q
    have e1 : C.circlePt hn q - C.circlePt hn e
        = (C.circlePt hn q - (C.seg e.1).1) - (C.circlePt hn e - (C.seg e.1).1) := by abel
    rw [e1, detv_sub_right, hline, sub_zero]
  rcases Bool.dichotomy e.2 with he2 | he2
  · -- e.2 = false: the arc is the negative side of the line of chord `e.1`
    have hpe : C.circlePt hn ⟨e.1, !e.2⟩ - C.circlePt hn e
        = ((C.circleParams hn e.1).2 - (C.circleParams hn e.1).1) • C.dir e.1 := by
      have h1 : C.circlePt hn e = (C.seg e.1).1 + (C.circleParams hn e.1).1 • C.dir e.1 := by
        have hqe2 : e = ⟨e.1, false⟩ := Prod.ext rfl he2
        rw [hqe2]
        exact C.circlePts_fst_eq hn e.1
      have h2 : C.circlePt hn ⟨e.1, !e.2⟩
          = (C.seg e.1).1 + (C.circleParams hn e.1).2 • C.dir e.1 := by
        have hpe2 : (⟨e.1, !e.2⟩ : Fin n × Bool) = ⟨e.1, true⟩ := by rw [he2]; rfl
        rw [hpe2]
        exact C.circlePts_snd_eq hn e.1
      rw [h1, h2]
      module
    have hpos : 0 < (C.circleParams hn e.1).2 - (C.circleParams hn e.1).1 := by
      have hcl := C.circleParams_lt hn e.1
      linarith
    have hfilter : (Finset.univ.filter fun q : Fin n × Bool => C.arcPred hn e ⟨e.1, !e.2⟩ q)
        = (Finset.univ.filter fun q : Fin n × Bool =>
            detv (C.dir e.1) (C.circlePt hn q - (C.seg e.1).1) < 0) := by
      apply Finset.filter_congr
      intro q _
      show detv (C.circlePt hn ⟨e.1, !e.2⟩ - C.circlePt hn e) (C.circlePt hn q - C.circlePt hn e) < 0
        ↔ detv (C.dir e.1) (C.circlePt hn q - (C.seg e.1).1) < 0
      rw [hpe, detv_smul_left, hqe q, mul_neg_iff]
      constructor
      · rintro (⟨g1, g2⟩ | ⟨g1, g2⟩)
        · exact g2
        · linarith
      · intro h
        exact Or.inl ⟨hpos, h⟩
    rw [hfilter]
    exact hn2
  · -- e.2 = true: the arc is the positive side of the line of chord `e.1`
    have hpe : C.circlePt hn ⟨e.1, !e.2⟩ - C.circlePt hn e
        = ((C.circleParams hn e.1).1 - (C.circleParams hn e.1).2) • C.dir e.1 := by
      have h1 : C.circlePt hn e = (C.seg e.1).1 + (C.circleParams hn e.1).2 • C.dir e.1 := by
        have hqe2 : e = ⟨e.1, true⟩ := Prod.ext rfl he2
        rw [hqe2]
        exact C.circlePts_snd_eq hn e.1
      have h2 : C.circlePt hn ⟨e.1, !e.2⟩
          = (C.seg e.1).1 + (C.circleParams hn e.1).1 • C.dir e.1 := by
        have hpe2 : (⟨e.1, !e.2⟩ : Fin n × Bool) = ⟨e.1, false⟩ := by rw [he2]; rfl
        rw [hpe2]
        exact C.circlePts_fst_eq hn e.1
      rw [h1, h2]
      module
    have hneg : (C.circleParams hn e.1).1 - (C.circleParams hn e.1).2 < 0 := by
      have hcl := C.circleParams_lt hn e.1
      linarith
    have hfilter : (Finset.univ.filter fun q : Fin n × Bool => C.arcPred hn e ⟨e.1, !e.2⟩ q)
        = (Finset.univ.filter fun q : Fin n × Bool =>
            0 < detv (C.dir e.1) (C.circlePt hn q - (C.seg e.1).1)) := by
      apply Finset.filter_congr
      intro q _
      show detv (C.circlePt hn ⟨e.1, !e.2⟩ - C.circlePt hn e) (C.circlePt hn q - C.circlePt hn e) < 0
        ↔ 0 < detv (C.dir e.1) (C.circlePt hn q - (C.seg e.1).1)
      rw [hpe, detv_smul_left, hqe q, mul_neg_iff]
      constructor
      · rintro (⟨g1, g2⟩ | ⟨g1, g2⟩)
        · linarith
        · exact g2
      · intro h
        exact Or.inr ⟨hneg, h⟩
    rw [hfilter]
    exact hp

/-- The number of circle endpoints on the counterclockwise arc from
`label m` to `label (m + k)` is `k.val - 1`. -/
lemma arc_card_eq (hn : 2 ≤ n) (m k : ZMod (2 * n)) :
    (Finset.univ.filter fun q : Fin n × Bool =>
      C.arcPred hn (C.label hn m) (C.label hn (m + k)) q).card = k.val - 1 := by
  haveI : NeZero (2 * n) := ⟨by omega⟩
  have hkN : k.val < 2 * n := ZMod.val_lt _
  have himg : (Finset.univ.filter fun q : Fin n × Bool =>
        C.arcPred hn (C.label hn m) (C.label hn (m + k)) q)
      = (Finset.univ.filter fun c : ZMod (2 * n) =>
          C.arcPred hn (C.label hn m) (C.label hn (m + k)) (C.label hn c)).image (C.label hn) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro h
      obtain ⟨c, hc⟩ := C.label_surjective hn q
      refine ⟨c, ?_, hc⟩
      rw [hc]
      exact h
    · rintro ⟨c, h, rfl⟩
      exact h
  rw [himg, Finset.card_image_of_injective _ (C.label_injective hn)]
  have hcongr : (Finset.univ.filter fun c : ZMod (2 * n) =>
        C.arcPred hn (C.label hn m) (C.label hn (m + k)) (C.label hn c))
      = Finset.univ.filter fun c : ZMod (2 * n) =>
          0 < (c - m).val ∧ (c - m).val < ((m + k) - m).val := by
    apply Finset.filter_congr
    intro c _
    exact C.arcPred_label_iff hn m (m + k) c
  have hmk : (m + k) - m = k := by ring
  rw [hcongr, hmk]
  have himg2 : (Finset.univ.filter fun c : ZMod (2 * n) => 0 < (c - m).val ∧ (c - m).val < k.val)
      = (Finset.univ.filter fun d : ZMod (2 * n) => 0 < d.val ∧ d.val < k.val).image (· + m) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro h
      exact ⟨c - m, h, sub_add_cancel c m⟩
    · rintro ⟨d, hd, rfl⟩
      have hdm : (d + m - m : ZMod (2 * n)) = d := by ring
      rw [hdm]
      exact hd
  rw [himg2, Finset.card_image_of_injective _ (fun x y h => add_right_cancel h)]
  have hbij : (Finset.univ.filter fun d : ZMod (2 * n) => 0 < d.val ∧ d.val < k.val).card
      = (Finset.Ioo 0 k.val).card := by
    apply Finset.card_bij (fun d _ => d.val)
    · intro d hd
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd
      exact Finset.mem_Ioo.mpr hd
    · intro d1 _ d2 _ h
      exact ZMod.val_injective _ h
    · intro v hv
      simp only [Finset.mem_Ioo] at hv
      refine ⟨(v : ZMod (2 * n)), ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [ZMod.val_natCast_of_lt (by omega)]
        exact hv
      · rw [ZMod.val_natCast_of_lt (by omega)]
  rw [hbij, Nat.card_Ioo]
  omega

/-- The antipodality of the labeling: the partner of the `m`-th endpoint is
exactly `n` steps ahead in the cyclic order. -/
lemma label_add_n (hn : 2 ≤ n) (m : ZMod (2 * n)) :
    C.label hn (m + (n : ZMod (2 * n))) = ⟨(C.label hn m).1, !(C.label hn m).2⟩ := by
  haveI : NeZero (2 * n) := ⟨by omega⟩
  set e := C.label hn m with he
  obtain ⟨b, hb⟩ := C.label_surjective hn (⟨e.1, !e.2⟩ : Fin n × Bool)
  have hcard1 : (Finset.univ.filter fun q : Fin n × Bool =>
      C.arcPred hn e ⟨e.1, !e.2⟩ q).card = n - 1 := C.arc_card_partner hn e
  have hcard2 : (Finset.univ.filter fun q : Fin n × Bool =>
      C.arcPred hn e ⟨e.1, !e.2⟩ q).card = (b - m).val - 1 := by
    have h := C.arc_card_eq hn m (b - m)
    have hmk : m + (b - m) = b := by ring
    rw [hmk] at h
    rw [← he, hb] at h
    exact h
  have hbme : b ≠ m := by
    intro hcon
    rw [hcon] at hb
    rw [← he] at hb
    have h2 : e.2 = !e.2 := congrArg Prod.snd hb
    exact Bool.self_ne_not _ h2
  have hval : (b - m).val = n := by
    have hge : 1 ≤ (b - m).val := by
      rcases Nat.eq_zero_or_pos (b - m).val with h0 | h0
      · exfalso
        have h1 : b - m = 0 := (ZMod.val_eq_zero _).mp h0
        exact hbme (sub_eq_zero.mp h1)
      · exact h0
    omega
  have hbm : b - m = (n : ZMod (2 * n)) := by
    apply ZMod.val_injective
    rw [hval, ZMod.val_natCast_of_lt (by omega)]
  have hfin : b = m + (n : ZMod (2 * n)) := by
    rw [← hbm]
    ring
  rw [← hfin]
  exact hb

/-- The arc between two consecutive endpoints in the cyclic order is
empty. -/
lemma consec_arc_empty (hn : 2 ≤ n) (m : ZMod (2 * n)) (e : Fin n × Bool)
    (_he : e ≠ C.label hn m) (_he1 : e ≠ C.label hn (m + 1)) :
    ¬ C.arcPred hn (C.label hn m) (C.label hn (m + 1)) e := by
  haveI : NeZero (2 * n) := ⟨by omega⟩
  obtain ⟨c, rfl⟩ := C.label_surjective hn e
  rw [C.arcPred_label_iff hn m (m + 1) c]
  have h1 : (m + 1 - m : ZMod (2 * n)) = 1 := by ring
  rw [h1]
  have hv1 : (1 : ZMod (2 * n)).val = 1 := by
    have h2 : ((1 : ℕ) : ZMod (2 * n)).val = 1 := ZMod.val_natCast_of_lt (by omega)
    rwa [Nat.cast_one] at h2
  rw [hv1]
  rintro ⟨h2, h3⟩
  omega

/-- If the segment through circle endpoints `A B` meets the open chord
of `k`, then the line through `A B` and the line of `k` are not
parallel. -/
lemma dir_BA_ne_of_mem_openChord (hn : 2 ≤ n) {a b : Fin n × Bool} {k : Fin n}
    (hab : a.1 ≠ b.1) (Y : ℝ × ℝ)
    (hY1 : Y ∈ openSegment ℝ (C.circlePt hn a) (C.circlePt hn b))
    (hY2 : Y ∈ C.openChord hn k) :
    detv (C.dir k) (C.circlePt hn b - C.circlePt hn a) ≠ 0 := by
  intro hd2
  obtain ⟨t, ht, hYt⟩ := mem_openSegment_iff_param.mp hY1
  have hYk : detv (C.dir k) (Y - (C.seg k).1) = 0 := by
    rw [openChord, mem_openSegment_iff_param] at hY2
    obtain ⟨r, hr, hYr⟩ := hY2
    rw [hYr]
    have e : (C.circlePts hn k).1 + r • ((C.circlePts hn k).2 - (C.circlePts hn k).1)
        = (C.seg k).1 + ((C.circleParams hn k).1 + r * ((C.circleParams hn k).2 - (C.circleParams hn k).1)) • C.dir k := by
      rw [C.openChord_dir hn k, circlePts_fst_eq, smul_smul]
      module
    rw [e]
    have e2 : (C.seg k).1 + ((C.circleParams hn k).1 + r * ((C.circleParams hn k).2 - (C.circleParams hn k).1)) • C.dir k - (C.seg k).1
        = ((C.circleParams hn k).1 + r * ((C.circleParams hn k).2 - (C.circleParams hn k).1)) • C.dir k := by abel
    rw [e2, detv_smul_right, detv_self, mul_zero]
  have hAon : detv (C.dir k) (C.circlePt hn a - (C.seg k).1) = 0 := by
    have e : C.circlePt hn a - (C.seg k).1
        = (C.circlePt hn a - Y) + (Y - (C.seg k).1) := by abel
    rw [e, detv_add_right, hYk, add_zero]
    have e2 : C.circlePt hn a - Y = -t • (C.circlePt hn b - C.circlePt hn a) := by
      rw [hYt]
      module
    rw [e2, detv_smul_right, hd2, mul_zero]
  have hBon : detv (C.dir k) (C.circlePt hn b - (C.seg k).1) = 0 := by
    have e : C.circlePt hn b - (C.seg k).1
        = (C.circlePt hn b - Y) + (Y - (C.seg k).1) := by abel
    rw [e, detv_add_right, hYk, add_zero]
    have e2 : C.circlePt hn b - Y = (1 - t) • (C.circlePt hn b - C.circlePt hn a) := by
      rw [hYt]
      module
    rw [e2, detv_smul_right, hd2, mul_zero]
  have hAin := C.eq_circlePts_of_mem_line_circle hn k (C.circlePt_nsq hn a) hAon
  have hBin := C.eq_circlePts_of_mem_line_circle hn k (C.circlePt_nsq hn b) hBon
  have hak : a.1 = k := by
    rcases hAin with hAin | hAin
    · have h3 : C.circlePt hn a = C.circlePt hn ⟨k, false⟩ := by
        rw [hAin]
        show (C.circlePts hn k).1 = if false = true then (C.circlePts hn k).2 else (C.circlePts hn k).1
        rw [if_neg (show ¬(false = true) from by simp)]
      have h4 := C.circlePt_injective hn h3
      rw [h4]
    · have h3 : C.circlePt hn a = C.circlePt hn ⟨k, true⟩ := by
        rw [hAin]
        show (C.circlePts hn k).2 = if true = true then (C.circlePts hn k).2 else (C.circlePts hn k).1
        rw [if_pos rfl]
      have h4 := C.circlePt_injective hn h3
      rw [h4]
  have hbk : b.1 = k := by
    rcases hBin with hBin | hBin
    · have h3 : C.circlePt hn b = C.circlePt hn ⟨k, false⟩ := by
        rw [hBin]
        show (C.circlePts hn k).1 = if false = true then (C.circlePts hn k).2 else (C.circlePts hn k).1
        rw [if_neg (show ¬(false = true) from by simp)]
      have h4 := C.circlePt_injective hn h3
      rw [h4]
    · have h3 : C.circlePt hn b = C.circlePt hn ⟨k, true⟩ := by
        rw [hBin]
        show (C.circlePts hn k).2 = if true = true then (C.circlePts hn k).2 else (C.circlePts hn k).1
        rw [if_pos rfl]
      have h4 := C.circlePt_injective hn h3
      rw [h4]
  rw [hak, hbk] at hab
  exact hab rfl

/-- Alternation for chords of the circle: `k` separates the circle
endpoints of `a` and `b` iff its two circle endpoints lie on opposite
sides of the line through them. -/
lemma separates_iff_alternation (hn : 2 ≤ n) {a b : Fin n × Bool} {k : Fin n}
    (hab : a.1 ≠ b.1) :
    C.separates k (C.circlePt hn a) (C.circlePt hn b) ↔
      detv (C.circlePt hn b - C.circlePt hn a) ((C.circlePts hn k).1 - C.circlePt hn a) *
        detv (C.circlePt hn b - C.circlePt hn a) ((C.circlePts hn k).2 - C.circlePt hn a) < 0 := by
  rw [C.separates_iff_mem_openChord hn hab]
  constructor
  · intro ⟨Y, hY1, hY2⟩
    have hd := C.dir_BA_ne_of_mem_openChord hn hab Y hY1 hY2
    have hd2 : detv (C.circlePt hn b - C.circlePt hn a) ((C.circlePts hn k).2 - (C.circlePts hn k).1) ≠ 0 := by
      rw [C.openChord_dir hn k, detv_smul_right]
      have hlt := C.circleParams_lt hn k
      have hd3 : detv (C.circlePt hn b - C.circlePt hn a) (C.dir k) ≠ 0 := by
        rw [detv_antisymm]
        exact neg_ne_zero.mpr hd
      exact mul_ne_zero (by linarith) hd3
    exact (oppSide_of_properCross ⟨hY1, hY2⟩ hd2).1
  · intro hopp
    exact (C.separates_iff_mem_openChord hn hab).mp (C.separates_of_opp_far hn hab hopp)

/-- Membership in the far-arc from `a` to `b`. -/
lemma mem_farArc (hn : 2 ≤ n) {a b q : Fin n × Bool} (hab : a.1 ≠ b.1) :
    q ∈ C.farArc hn a b ↔
      detv (C.circlePt hn b - C.circlePt hn a) (C.circlePt hn q - C.circlePt hn a) *
        detv (C.circlePt hn b - C.circlePt hn a) (C.xpoint a.1 b.1 hab - C.circlePt hn a) < 0 := by
  rw [farArc, Finset.mem_filter, C.nxpoint_eq a.1 b.1 hab]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ q, h⟩⟩

/-- For a separating chord, exactly one of its circle endpoints lies in
the far-arc. -/
lemma farArc_unique_mem (hn : 2 ≤ n) {a b : Fin n × Bool} (hab : a.1 ≠ b.1) {k : Fin n}
    (hsep : C.separates k (C.circlePt hn a) (C.circlePt hn b)) :
    ((⟨k, false⟩ : Fin n × Bool) ∈ C.farArc hn a b ∧ (⟨k, true⟩ : Fin n × Bool) ∉ C.farArc hn a b) ∨
      ((⟨k, false⟩ : Fin n × Bool) ∉ C.farArc hn a b ∧ (⟨k, true⟩ : Fin n × Bool) ∈ C.farArc hn a b) := by
  have hopp := (C.separates_iff_alternation hn hab).mp hsep
  have hS : detv (C.circlePt hn b - C.circlePt hn a) (C.xpoint a.1 b.1 hab - C.circlePt hn a) ≠ 0 :=
    C.detv_xpoint_circlePt_ne_zero hn hab
  rw [C.mem_farArc hn hab, C.mem_farArc hn hab]
  have h1 : detv (C.circlePt hn b - C.circlePt hn a) (C.circlePt hn ⟨k, false⟩ - C.circlePt hn a) *
      detv (C.circlePt hn b - C.circlePt hn a) (C.circlePt hn ⟨k, true⟩ - C.circlePt hn a) < 0 := hopp
  -- the two determinants have opposite signs; exactly one matches -S
  set S := detv (C.circlePt hn b - C.circlePt hn a) (C.xpoint a.1 b.1 hab - C.circlePt hn a)
  rcases lt_or_gt_of_ne hS with hS' | hS'
  · rcases mul_neg_iff.mp h1 with g | g
    · -- S < 0, d1 > 0, d2 < 0: fst in, snd out
      exact Or.inl ⟨mul_neg_of_pos_of_neg g.1 hS', by
        intro hmem
        nlinarith [hmem, mul_pos_of_neg_of_neg g.2 hS']⟩
    · -- S < 0, d1 < 0, d2 > 0: fst out, snd in
      exact Or.inr ⟨by
        intro hmem
        nlinarith [hmem, mul_pos_of_neg_of_neg g.1 hS'], mul_neg_of_pos_of_neg g.2 hS'⟩
  · rcases mul_neg_iff.mp h1 with g | g
    · -- S > 0, d1 > 0, d2 < 0: fst out, snd in
      exact Or.inr ⟨by
        intro hmem
        nlinarith [hmem, mul_pos g.1 hS'], mul_neg_of_neg_of_pos g.2 hS'⟩
    · -- S > 0, d1 < 0, d2 > 0: fst in, snd out
      exact Or.inl ⟨mul_neg_of_neg_of_pos g.1 hS', by
        intro hmem
        nlinarith [hmem, mul_pos g.2 hS']⟩

noncomputable instance (hn : 2 ≤ n) (a b : Fin n × Bool) :
    DecidablePred fun k : Fin n => C.separates k (C.circlePt hn a) (C.circlePt hn b) := by
  intro k
  show Decidable (C.separates k (C.circlePt hn a) (C.circlePt hn b))
  rw [separates]
  infer_instance

/-- The circle endpoint of `a` as a scalar multiple of the segment
direction from `(seg a).1`: it is the smaller-parameter point when
`a.2 = false`, the larger when `a.2 = true`. -/
lemma circlePt_eq_dir_smul (hn : 2 ≤ n) (a : Fin n × Bool) :
    C.circlePt hn a = (C.seg a.1).1 +
      (if a.2 then (C.circleParams hn a.1).2 else (C.circleParams hn a.1).1) • C.dir a.1 := by
  cases h : a.2 with
  | false =>
    rw [if_neg (show ¬(false = true) from by simp)]
    have h1 : C.circlePt hn a = (C.circlePts hn a.1).1 := by
      rw [show a = ⟨a.1, false⟩ from Prod.ext rfl h, circlePt,
        if_neg (show ¬(false = true) from by simp)]
    rw [h1, circlePts_fst_eq]
  | true =>
    rw [if_pos rfl]
    have h1 : C.circlePt hn a = (C.circlePts hn a.1).2 := by
      rw [show a = ⟨a.1, true⟩ from Prod.ext rfl h, circlePt, if_pos rfl]
    rw [h1, circlePts_snd_eq]

/-- The value of `detv (B-A)(·-A)` at the crossing of chord `q` with
chord `a.1` has the same sign as at the crossing `X` of chords `a.1` and
`b.1` (both crossings lie on segment `a.1` on the same side of the circle
endpoint of `a`). -/
lemma sign_cross_same_side (hn : 2 ≤ n) {a b : Fin n × Bool} (hab : a.1 ≠ b.1)
    {q : Fin n} (hqa : q ≠ a.1) :
    (detv (C.circlePt hn b - C.circlePt hn a) (C.xpoint q a.1 hqa - C.circlePt hn a) *
      detv (C.circlePt hn b - C.circlePt hn a) (C.xpoint a.1 b.1 hab - C.circlePt hn a)) > 0 := by
  obtain ⟨tX', htX'01, htX', hXtX'⟩ := C.xpoint_param hn a.1 q hqa.symm
  obtain ⟨tX, htX01, htX, hXtX⟩ := C.xpoint_param hn a.1 b.1 hab
  have hqa2 : a.1 ≠ q := hqa.symm
  have hX'eq : C.xpoint q a.1 hqa = C.xpoint a.1 q hqa2 :=
    (C.xpoint_unique q a.1 hqa ⟨(C.xpoint_mem a.1 q hqa2).2, (C.xpoint_mem a.1 q hqa2).1⟩).symm
  set tA := if a.2 then (C.circleParams hn a.1).2 else (C.circleParams hn a.1).1
  have htA : C.circlePt hn a = (C.seg a.1).1 + tA • C.dir a.1 := C.circlePt_eq_dir_smul hn a
  have e1 : detv (C.circlePt hn b - C.circlePt hn a) (C.xpoint q a.1 hqa - C.circlePt hn a)
      = (tX' - tA) * detv (C.circlePt hn b - C.circlePt hn a) (C.dir a.1) := by
    rw [hX'eq]
    have e2 : C.xpoint a.1 q hqa.symm - C.circlePt hn a
        = (tX' - tA) • C.dir a.1 := by
      rw [hXtX', htA]
      module
    rw [e2, detv_smul_right]
  have e3 : detv (C.circlePt hn b - C.circlePt hn a) (C.xpoint a.1 b.1 hab - C.circlePt hn a)
      = (tX - tA) * detv (C.circlePt hn b - C.circlePt hn a) (C.dir a.1) := by
    have e2 : C.xpoint a.1 b.1 hab - C.circlePt hn a
        = (tX - tA) • C.dir a.1 := by
      rw [hXtX, htA]
      module
    rw [e2, detv_smul_right]
  rw [e1, e3]
  have hne : detv (C.circlePt hn b - C.circlePt hn a) (C.dir a.1) ≠ 0 := by
    have h5 := C.detv_xpoint_circlePt_ne_zero hn hab
    rw [e3] at h5
    exact (mul_ne_zero_iff.mp h5).2
  have hsgn : 0 < (tX' - tA) * (tX - tA) := by
    cases h : a.2 with
    | false =>
      have htA2 : tA = (C.circleParams hn a.1).1 := by
        show (if a.2 then (C.circleParams hn a.1).2 else (C.circleParams hn a.1).1)
          = (C.circleParams hn a.1).1
        simp [h]
      rw [htA2]
      exact mul_pos (sub_pos.mpr htX'.1) (sub_pos.mpr htX.1)
    | true =>
      have htA2 : tA = (C.circleParams hn a.1).2 := by
        show (if a.2 then (C.circleParams hn a.1).2 else (C.circleParams hn a.1).1)
          = (C.circleParams hn a.1).2
        simp [h]
      rw [htA2]
      exact mul_pos_of_neg_of_neg (sub_neg.mpr htX'.2) (sub_neg.mpr htX.2)
  have h7 : detv (C.circlePt hn b - C.circlePt hn a) (C.dir a.1) ^ 2 > 0 :=
    sq_pos_of_ne_zero hne
  nlinarith [hsgn, h7]

/-- The partner of the circle endpoint of `a` lies on the same side of
the line through the circle endpoints of `a` and `b` as the crossing `X`
of the chords of `a` and `b` (both lie on the chord of `a.1`, strictly
beyond the circle endpoint of `a`). -/
lemma detv_partner_mul_detv_xpoint_pos (hn : 2 ≤ n) {a b : Fin n × Bool} (hab : a.1 ≠ b.1) :
    detv (C.circlePt hn b - C.circlePt hn a) (C.circlePt hn ⟨a.1, !a.2⟩ - C.circlePt hn a) *
      detv (C.circlePt hn b - C.circlePt hn a) (C.xpoint a.1 b.1 hab - C.circlePt hn a) > 0 := by
  obtain ⟨tX, htX01, htX, hXtX⟩ := C.xpoint_param hn a.1 b.1 hab
  set tA := if a.2 then (C.circleParams hn a.1).2 else (C.circleParams hn a.1).1
  set tA' := if !a.2 then (C.circleParams hn a.1).2 else (C.circleParams hn a.1).1
  have htA : C.circlePt hn a = (C.seg a.1).1 + tA • C.dir a.1 := C.circlePt_eq_dir_smul hn a
  have htA' : C.circlePt hn ⟨a.1, !a.2⟩ = (C.seg a.1).1 + tA' • C.dir a.1 :=
    C.circlePt_eq_dir_smul hn ⟨a.1, !a.2⟩
  have e1 : detv (C.circlePt hn b - C.circlePt hn a) (C.circlePt hn ⟨a.1, !a.2⟩ - C.circlePt hn a)
      = (tA' - tA) * detv (C.circlePt hn b - C.circlePt hn a) (C.dir a.1) := by
    have e2 : C.circlePt hn ⟨a.1, !a.2⟩ - C.circlePt hn a
        = (tA' - tA) • C.dir a.1 := by
      rw [htA', htA]
      module
    rw [e2, detv_smul_right]
  have e3 : detv (C.circlePt hn b - C.circlePt hn a) (C.xpoint a.1 b.1 hab - C.circlePt hn a)
      = (tX - tA) * detv (C.circlePt hn b - C.circlePt hn a) (C.dir a.1) := by
    have e2 : C.xpoint a.1 b.1 hab - C.circlePt hn a
        = (tX - tA) • C.dir a.1 := by
      rw [hXtX, htA]
      module
    rw [e2, detv_smul_right]
  rw [e1, e3]
  have hne : detv (C.circlePt hn b - C.circlePt hn a) (C.dir a.1) ≠ 0 := by
    have h5 := C.detv_xpoint_circlePt_ne_zero hn hab
    rw [e3] at h5
    exact (mul_ne_zero_iff.mp h5).2
  have hsgn : 0 < (tA' - tA) * (tX - tA) := by
    cases h : a.2 with
    | false =>
      have htA2 : tA = (C.circleParams hn a.1).1 := by
        show (if a.2 then (C.circleParams hn a.1).2 else (C.circleParams hn a.1).1)
          = (C.circleParams hn a.1).1
        simp [h]
      have htA'2 : tA' = (C.circleParams hn a.1).2 := by
        show (if !a.2 then (C.circleParams hn a.1).2 else (C.circleParams hn a.1).1)
          = (C.circleParams hn a.1).2
        simp [h]
      rw [htA2, htA'2]
      exact mul_pos (sub_pos.mpr (C.circleParams_lt hn a.1)) (sub_pos.mpr htX.1)
    | true =>
      have htA2 : tA = (C.circleParams hn a.1).2 := by
        show (if a.2 then (C.circleParams hn a.1).2 else (C.circleParams hn a.1).1)
          = (C.circleParams hn a.1).2
        simp [h]
      have htA'2 : tA' = (C.circleParams hn a.1).1 := by
        show (if !a.2 then (C.circleParams hn a.1).2 else (C.circleParams hn a.1).1)
          = (C.circleParams hn a.1).1
        simp [h]
      rw [htA2, htA'2]
      exact mul_pos_of_neg_of_neg (sub_neg.mpr (C.circleParams_lt hn a.1)) (sub_neg.mpr htX.2)
  have h7 : detv (C.circlePt hn b - C.circlePt hn a) (C.dir a.1) ^ 2 > 0 :=
    sq_pos_of_ne_zero hne
  nlinarith [hsgn, h7]

/-- The number of chords separating circle endpoints `A` and `B` equals
the number of circle endpoints on the far-arc from `a` to `b`. -/
lemma sep_card_eq_farArc_card (hn : 2 ≤ n) {a b : Fin n × Bool} (hab : a.1 ≠ b.1) :
    ((Finset.univ.filter fun k : Fin n => C.separates k (C.circlePt hn a) (C.circlePt hn b)).card)
      = (C.farArc hn a b).card := by
  classical
  set S : Finset (Fin n) :=
    Finset.univ.filter fun k : Fin n => C.separates k (C.circlePt hn a) (C.circlePt hn b)
  set T : Finset (Fin n × Bool) := C.farArc hn a b
  set X := C.xpoint a.1 b.1 hab
  let f : (k : Fin n) → k ∈ S → Fin n × Bool := fun k _ =>
    if detv (C.circlePt hn b - C.circlePt hn a) ((C.circlePts hn k).1 - C.circlePt hn a) *
        detv (C.circlePt hn b - C.circlePt hn a) (X - C.circlePt hn a) < 0
      then ⟨k, false⟩ else ⟨k, true⟩
  apply Finset.card_bij f
  · intro k hk
    have hsep : C.separates k (C.circlePt hn a) (C.circlePt hn b) := by
      have hk2 : k ∈ (Finset.univ.filter fun k : Fin n => C.separates k (C.circlePt hn a) (C.circlePt hn b)) := hk
      rw [Finset.mem_filter] at hk2
      exact hk2.2
    have hun := C.farArc_unique_mem hn hab hsep
    have hgoal : (if detv (C.circlePt hn b - C.circlePt hn a) ((C.circlePts hn k).1 - C.circlePt hn a) *
        detv (C.circlePt hn b - C.circlePt hn a) (X - C.circlePt hn a) < 0
      then ⟨k, false⟩ else ⟨k, true⟩) ∈ T := by
      rcases hun with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [if_pos (by
          have h := h1
          rw [C.mem_farArc hn hab] at h
          exact h)]
        exact h1
      · rw [if_neg (by
          have h := h1
          rw [C.mem_farArc hn hab] at h
          exact h)]
        exact h2
    exact hgoal
  · intro k1 h1 k2 h2 heq

    have hsep1 : C.separates k1 (C.circlePt hn a) (C.circlePt hn b) := by
      have h12 : k1 ∈ (Finset.univ.filter fun k : Fin n => C.separates k (C.circlePt hn a) (C.circlePt hn b)) := h1
      rw [Finset.mem_filter] at h12
      exact h12.2
    have hsep2 : C.separates k2 (C.circlePt hn a) (C.circlePt hn b) := by
      have h22 : k2 ∈ (Finset.univ.filter fun k : Fin n => C.separates k (C.circlePt hn a) (C.circlePt hn b)) := h2
      rw [Finset.mem_filter] at h22
      exact h22.2
    have hun1 := C.farArc_unique_mem hn hab hsep1
    have hun2 := C.farArc_unique_mem hn hab hsep2
    -- if the if-picks agree, then (k1, false) and (k2, false) have the same
    -- farArc status; conclude k1 = k2 from the endpoint map
    simp only [f] at heq
    by_cases hc1 : detv (C.circlePt hn b - C.circlePt hn a) ((C.circlePts hn k1).1 - C.circlePt hn a) *
        detv (C.circlePt hn b - C.circlePt hn a) (X - C.circlePt hn a) < 0
    · rw [if_pos hc1] at heq
      by_cases hc2 : detv (C.circlePt hn b - C.circlePt hn a) ((C.circlePts hn k2).1 - C.circlePt hn a) *
          detv (C.circlePt hn b - C.circlePt hn a) (X - C.circlePt hn a) < 0
      · rw [if_pos hc2] at heq
        have h5 : (⟨k1, false⟩ : Fin n × Bool) = ⟨k2, false⟩ := heq
        rw [Prod.mk.injEq] at h5
        exact h5.1
      · rw [if_neg hc2] at heq
        exact absurd heq (by simp)
    · rw [if_neg hc1] at heq
      by_cases hc2 : detv (C.circlePt hn b - C.circlePt hn a) ((C.circlePts hn k2).1 - C.circlePt hn a) *
          detv (C.circlePt hn b - C.circlePt hn a) (X - C.circlePt hn a) < 0
      · rw [if_pos hc2] at heq
        exact absurd heq (by simp)
      · rw [if_neg hc2] at heq
        have h5 : (⟨k1, true⟩ : Fin n × Bool) = ⟨k2, true⟩ := heq
        rw [Prod.mk.injEq] at h5
        exact h5.1
  · intro q hq
    have hq2 : q ∈ C.farArc hn a b := hq
    rw [C.mem_farArc hn hab] at hq2
    -- The chord of `q` is not the chord of `a`: `q` is not `a` (its
    -- determinant is nonzero), and the partner of `a` lies on `X`'s side.
    have hqa : q.1 ≠ a.1 := by
      intro hcon
      by_cases h2 : q.2 = a.2
      · have hqa2 : q = a := Prod.ext hcon h2
        rw [hqa2] at hq2
        have hz : detv (C.circlePt hn b - C.circlePt hn a)
            (C.circlePt hn a - C.circlePt hn a) = 0 := by
          rw [sub_self, detv_zero_right]
        rw [hz, zero_mul] at hq2
        exact (lt_irrefl (0 : ℝ)) hq2
      · have h2' : q.2 = !a.2 := Bool.eq_not_iff.mpr h2
        have hqe2 : q = ⟨a.1, !a.2⟩ := Prod.ext hcon h2'
        rw [hqe2] at hq2
        exact absurd hq2 (not_lt_of_gt (C.detv_partner_mul_detv_xpoint_pos hn hab))
    -- The crossing `X'` of the chords of `q` and `a` sees `X` on the same
    -- side, hence opposite from `q`; interpolating along the chord of `q`,
    -- the partner of `q` must lie on the opposite side of the line `AB`.
    set tQ := if q.2 then (C.circleParams hn q.1).2 else (C.circleParams hn q.1).1
    set tQ' := if !q.2 then (C.circleParams hn q.1).2 else (C.circleParams hn q.1).1
    have htQ : C.circlePt hn q = (C.seg q.1).1 + tQ • C.dir q.1 := C.circlePt_eq_dir_smul hn q
    have htQ' : C.circlePt hn ⟨q.1, !q.2⟩ = (C.seg q.1).1 + tQ' • C.dir q.1 :=
      C.circlePt_eq_dir_smul hn ⟨q.1, !q.2⟩
    obtain ⟨tX', htX'01, htX', hXtX'⟩ := C.xpoint_param hn q.1 a.1 hqa
    have hDQne : detv (C.circlePt hn b - C.circlePt hn a)
        (C.circlePt hn q - C.circlePt hn a) ≠ 0 := by
      intro hzero
      rw [hzero, zero_mul] at hq2
      exact (lt_irrefl (0 : ℝ)) hq2
    have hDX'X : detv (C.circlePt hn b - C.circlePt hn a)
        (C.xpoint q.1 a.1 hqa - C.circlePt hn a) *
        detv (C.circlePt hn b - C.circlePt hn a) (X - C.circlePt hn a) > 0 :=
      C.sign_cross_same_side hn hab hqa
    have hDQX' : detv (C.circlePt hn b - C.circlePt hn a) (C.circlePt hn q - C.circlePt hn a) *
        detv (C.circlePt hn b - C.circlePt hn a) (C.xpoint q.1 a.1 hqa - C.circlePt hn a) < 0 := by
      rcases mul_neg_iff.mp hq2 with ⟨hdq, hdx⟩ | ⟨hdq, hdx⟩
      · rcases mul_pos_iff.mp hDX'X with ⟨hdx', hdx2⟩ | ⟨hdx', hdx2⟩
        · exact absurd hdx (not_lt_of_gt hdx2)
        · exact mul_neg_of_pos_of_neg hdq hdx'
      · rcases mul_pos_iff.mp hDX'X with ⟨hdx', hdx2⟩ | ⟨hdx', hdx2⟩
        · exact mul_neg_of_neg_of_pos hdq hdx'
        · exact absurd hdx2 (not_lt_of_gt hdx)
    -- determinant values as affine functions of the chord parameter
    have hDQ : detv (C.circlePt hn b - C.circlePt hn a) (C.circlePt hn q - C.circlePt hn a)
        = detv (C.circlePt hn b - C.circlePt hn a) ((C.seg q.1).1 - C.circlePt hn a) +
          tQ * detv (C.circlePt hn b - C.circlePt hn a) (C.dir q.1) := by
      have e2 : C.circlePt hn q - C.circlePt hn a
          = ((C.seg q.1).1 - C.circlePt hn a) + tQ • C.dir q.1 := by
        rw [htQ]
        module
      rw [e2, detv_add_right, detv_smul_right]
    have hDQ' : detv (C.circlePt hn b - C.circlePt hn a)
        (C.circlePt hn ⟨q.1, !q.2⟩ - C.circlePt hn a)
        = detv (C.circlePt hn b - C.circlePt hn a) ((C.seg q.1).1 - C.circlePt hn a) +
          tQ' * detv (C.circlePt hn b - C.circlePt hn a) (C.dir q.1) := by
      have e2 : C.circlePt hn ⟨q.1, !q.2⟩ - C.circlePt hn a
          = ((C.seg q.1).1 - C.circlePt hn a) + tQ' • C.dir q.1 := by
        rw [htQ']
        module
      rw [e2, detv_add_right, detv_smul_right]
    have hDX' : detv (C.circlePt hn b - C.circlePt hn a) (C.xpoint q.1 a.1 hqa - C.circlePt hn a)
        = detv (C.circlePt hn b - C.circlePt hn a) ((C.seg q.1).1 - C.circlePt hn a) +
          tX' * detv (C.circlePt hn b - C.circlePt hn a) (C.dir q.1) := by
      have e2 : C.xpoint q.1 a.1 hqa - C.circlePt hn a
          = ((C.seg q.1).1 - C.circlePt hn a) + tX' • C.dir q.1 := by
        rw [hXtX']
        module
      rw [e2, detv_add_right, detv_smul_right]
    have hkey : detv (C.circlePt hn b - C.circlePt hn a) (C.xpoint q.1 a.1 hqa - C.circlePt hn a) *
        (tQ' - tQ)
        = detv (C.circlePt hn b - C.circlePt hn a) (C.circlePt hn q - C.circlePt hn a) * (tQ' - tX') +
          detv (C.circlePt hn b - C.circlePt hn a) (C.circlePt hn ⟨q.1, !q.2⟩ - C.circlePt hn a) *
            (tX' - tQ) := by
      rw [hDQ, hDQ', hDX']
      ring
    have hsgn1 : 0 < (tQ' - tX') * (tX' - tQ) := by
      cases hq22 : q.2 with
      | false =>
        have htQ2 : tQ = (C.circleParams hn q.1).1 := by
          show (if q.2 then (C.circleParams hn q.1).2 else (C.circleParams hn q.1).1)
            = (C.circleParams hn q.1).1
          simp [hq22]
        have htQ'2 : tQ' = (C.circleParams hn q.1).2 := by
          show (if !q.2 then (C.circleParams hn q.1).2 else (C.circleParams hn q.1).1)
            = (C.circleParams hn q.1).2
          simp [hq22]
        rw [htQ2, htQ'2]
        exact mul_pos (sub_pos.mpr htX'.2) (sub_pos.mpr htX'.1)
      | true =>
        have htQ2 : tQ = (C.circleParams hn q.1).2 := by
          show (if q.2 then (C.circleParams hn q.1).2 else (C.circleParams hn q.1).1)
            = (C.circleParams hn q.1).2
          simp [hq22]
        have htQ'2 : tQ' = (C.circleParams hn q.1).1 := by
          show (if !q.2 then (C.circleParams hn q.1).2 else (C.circleParams hn q.1).1)
            = (C.circleParams hn q.1).1
          simp [hq22]
        rw [htQ2, htQ'2]
        exact mul_pos_of_neg_of_neg (sub_neg.mpr htX'.1) (sub_neg.mpr htX'.2)
    have hsgn2 : 0 < (tQ' - tQ) * (tX' - tQ) := by
      cases hq22 : q.2 with
      | false =>
        have htQ2 : tQ = (C.circleParams hn q.1).1 := by
          show (if q.2 then (C.circleParams hn q.1).2 else (C.circleParams hn q.1).1)
            = (C.circleParams hn q.1).1
          simp [hq22]
        have htQ'2 : tQ' = (C.circleParams hn q.1).2 := by
          show (if !q.2 then (C.circleParams hn q.1).2 else (C.circleParams hn q.1).1)
            = (C.circleParams hn q.1).2
          simp [hq22]
        rw [htQ2, htQ'2]
        exact mul_pos (sub_pos.mpr (C.circleParams_lt hn q.1)) (sub_pos.mpr htX'.1)
      | true =>
        have htQ2 : tQ = (C.circleParams hn q.1).2 := by
          show (if q.2 then (C.circleParams hn q.1).2 else (C.circleParams hn q.1).1)
            = (C.circleParams hn q.1).2
          simp [hq22]
        have htQ'2 : tQ' = (C.circleParams hn q.1).1 := by
          show (if !q.2 then (C.circleParams hn q.1).2 else (C.circleParams hn q.1).1)
            = (C.circleParams hn q.1).1
          simp [hq22]
        rw [htQ2, htQ'2]
        exact mul_pos_of_neg_of_neg (sub_neg.mpr (C.circleParams_lt hn q.1)) (sub_neg.mpr htX'.2)
    have hQQ' : detv (C.circlePt hn b - C.circlePt hn a) (C.circlePt hn q - C.circlePt hn a) *
        detv (C.circlePt hn b - C.circlePt hn a) (C.circlePt hn ⟨q.1, !q.2⟩ - C.circlePt hn a)
        < 0 := by
      by_contra hcon
      push Not at hcon
      have hcontra : 0 < (detv (C.circlePt hn b - C.circlePt hn a) (C.circlePt hn q - C.circlePt hn a) *
          detv (C.circlePt hn b - C.circlePt hn a) (C.xpoint q.1 a.1 hqa - C.circlePt hn a)) *
          ((tQ' - tQ) * (tX' - tQ)) := by
        have e : (detv (C.circlePt hn b - C.circlePt hn a) (C.circlePt hn q - C.circlePt hn a) *
            detv (C.circlePt hn b - C.circlePt hn a) (C.xpoint q.1 a.1 hqa - C.circlePt hn a)) *
            ((tQ' - tQ) * (tX' - tQ))
            = detv (C.circlePt hn b - C.circlePt hn a) (C.circlePt hn q - C.circlePt hn a) ^ 2 *
              ((tQ' - tX') * (tX' - tQ)) +
              (detv (C.circlePt hn b - C.circlePt hn a) (C.circlePt hn q - C.circlePt hn a) *
              detv (C.circlePt hn b - C.circlePt hn a) (C.circlePt hn ⟨q.1, !q.2⟩ - C.circlePt hn a)) *
              ((tX' - tQ) ^ 2) := by
          have hkey2 := congrArg (fun z =>
            detv (C.circlePt hn b - C.circlePt hn a) (C.circlePt hn q - C.circlePt hn a) * z *
              (tX' - tQ)) hkey
          linear_combination hkey2
        rw [e]
        have g1 : 0 < detv (C.circlePt hn b - C.circlePt hn a) (C.circlePt hn q - C.circlePt hn a) ^ 2 *
            ((tQ' - tX') * (tX' - tQ)) := mul_pos (sq_pos_of_ne_zero hDQne) hsgn1
        have g2 : 0 ≤ (detv (C.circlePt hn b - C.circlePt hn a) (C.circlePt hn q - C.circlePt hn a) *
            detv (C.circlePt hn b - C.circlePt hn a) (C.circlePt hn ⟨q.1, !q.2⟩ - C.circlePt hn a)) *
            ((tX' - tQ) ^ 2) := mul_nonneg hcon (sq_nonneg _)
        linarith
      exact (not_lt_of_gt hcontra) (mul_neg_of_neg_of_pos hDQX' hsgn2)
    -- convert to the two endpoints of the chord in `circlePts` order
    have hopp : detv (C.circlePt hn b - C.circlePt hn a) ((C.circlePts hn q.1).1 - C.circlePt hn a) *
        detv (C.circlePt hn b - C.circlePt hn a) ((C.circlePts hn q.1).2 - C.circlePt hn a)
        < 0 := by
      cases hq22 : q.2 with
      | false =>
        have hQ : C.circlePt hn q = (C.circlePts hn q.1).1 := by
          rw [show q = ⟨q.1, false⟩ from Prod.ext rfl hq22, circlePt,
            if_neg (show ¬(false = true) from by simp)]
        have hQ' : C.circlePt hn ⟨q.1, !q.2⟩ = (C.circlePts hn q.1).2 := by
          rw [show (⟨q.1, !q.2⟩ : Fin n × Bool) = ⟨q.1, true⟩ from by simp [hq22], circlePt,
            if_pos rfl]
        rw [← hQ, ← hQ']
        exact hQQ'
      | true =>
        have hQ : C.circlePt hn q = (C.circlePts hn q.1).2 := by
          rw [show q = ⟨q.1, true⟩ from Prod.ext rfl hq22, circlePt, if_pos rfl]
        have hQ' : C.circlePt hn ⟨q.1, !q.2⟩ = (C.circlePts hn q.1).1 := by
          rw [show (⟨q.1, !q.2⟩ : Fin n × Bool) = ⟨q.1, false⟩ from by simp [hq22], circlePt,
            if_neg (show ¬(false = true) from by simp)]
        rw [← hQ, ← hQ', mul_comm]
        exact hQQ'
    -- q's chord separates, and the if-pick for q.1 chooses q
    have hsepq : C.separates q.1 (C.circlePt hn a) (C.circlePt hn b) :=
      (C.separates_iff_alternation hn hab).mpr hopp
    refine ⟨q.1, ?_, ?_⟩
    · show q.1 ∈ (Finset.univ.filter fun k : Fin n => C.separates k (C.circlePt hn a) (C.circlePt hn b))
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ q.1, hsepq⟩
    · simp only [f]
      cases hq22 : q.2 with
      | false =>
        have hQ : C.circlePt hn q = (C.circlePts hn q.1).1 := by
          rw [show q = ⟨q.1, false⟩ from Prod.ext rfl hq22, circlePt,
            if_neg (show ¬(false = true) from by simp)]
        have hc : detv (C.circlePt hn b - C.circlePt hn a) ((C.circlePts hn q.1).1 - C.circlePt hn a) *
            detv (C.circlePt hn b - C.circlePt hn a) (X - C.circlePt hn a) < 0 := by
          rw [← hQ]
          exact hq2
        rw [if_pos hc]
        exact Prod.ext rfl hq22.symm
      | true =>
        have hQ : C.circlePt hn q = (C.circlePts hn q.1).2 := by
          rw [show q = ⟨q.1, true⟩ from Prod.ext rfl hq22, circlePt, if_pos rfl]
        have hQ' : C.circlePt hn ⟨q.1, !q.2⟩ = (C.circlePts hn q.1).1 := by
          rw [show (⟨q.1, !q.2⟩ : Fin n × Bool) = ⟨q.1, false⟩ from by simp [hq22], circlePt,
            if_neg (show ¬(false = true) from by simp)]
        have hpos : 0 < detv (C.circlePt hn b - C.circlePt hn a)
            ((C.circlePts hn q.1).1 - C.circlePt hn a) *
            detv (C.circlePt hn b - C.circlePt hn a) (X - C.circlePt hn a) := by
          rw [← hQ']
          rcases mul_neg_iff.mp hQQ' with ⟨hdq, hdq'⟩ | ⟨hdq, hdq'⟩
          · rcases mul_neg_iff.mp hq2 with ⟨hdq2, hdx⟩ | ⟨hdq2, hdx⟩
            · exact mul_pos_of_neg_of_neg hdq' hdx
            · exact absurd hdq2 (not_lt_of_gt hdq)
          · rcases mul_neg_iff.mp hq2 with ⟨hdq2, hdx⟩ | ⟨hdq2, hdx⟩
            · exact absurd hdq (not_lt_of_gt hdq2)
            · exact mul_pos hdq' hdx
        rw [if_neg (not_lt_of_gt hpos)]
        exact Prod.ext rfl hq22.symm

/-- The endpoint of segment `a.1` on the side of the circle endpoint
`a`: this is where the frog that faces along `a` actually starts. -/
def segPt (a : Fin n × Bool) : ℝ × ℝ := if a.2 then (C.seg a.1).2 else (C.seg a.1).1

lemma segPt_eq_snd (a : Fin n × Bool) (h : a.2 = true) : C.segPt a = (C.seg a.1).2 := by
  rw [segPt, if_pos h]

lemma segPt_eq_fst (a : Fin n × Bool) (h : a.2 = false) : C.segPt a = (C.seg a.1).1 := by
  rw [segPt, if_neg (by simp [h])]

lemma segPt_eq_endpoints (a : Fin n × Bool) :
    C.segPt a = (C.seg a.1).1 ∨ C.segPt a = (C.seg a.1).2 := by
  cases h : a.2 with
  | false => exact Or.inl (C.segPt_eq_fst a h)
  | true => exact Or.inr (C.segPt_eq_snd a h)

/-- The arrival time from the circle endpoint of `a` equals the arrival
time from the corresponding segment endpoint. -/
lemma arrival_circlePt_eq_segPt (hn : 2 ≤ n) (a b : Fin n × Bool) (hab : a.1 ≠ b.1) :
    C.arrival a.1 b.1 hab (C.circlePt hn a) = C.arrival a.1 b.1 hab (C.segPt a) := by
  cases h : a.2 with
  | false =>
    have h2 : C.circlePt hn a = C.circlePt hn ⟨a.1, false⟩ := by
      rw [show a = ⟨a.1, false⟩ from Prod.ext rfl h]
    have h3 : C.segPt a = C.segPt ⟨a.1, false⟩ := by
      rw [show a = ⟨a.1, false⟩ from Prod.ext rfl h]
    rw [h2, h3, ← C.arrival_eq_circlePt_fst hn a.1 b.1 hab, C.segPt_eq_fst _ rfl]
  | true =>
    have h2 : C.circlePt hn a = C.circlePt hn ⟨a.1, true⟩ := by
      rw [show a = ⟨a.1, true⟩ from Prod.ext rfl h]
    have h3 : C.segPt a = C.segPt ⟨a.1, true⟩ := by
      rw [show a = ⟨a.1, true⟩ from Prod.ext rfl h]
    rw [h2, h3, ← C.arrival_eq_circlePt_snd hn a.1 b.1 hab, C.segPt_eq_snd _ rfl]

/-- For an endpoint `A` of segment `i`, the crossing with segment `k` is
strictly closer to `A` than the crossing with segment `j` iff it lies in
the open segment from `A` to the latter crossing. -/
lemma dist_xpoint_lt_iff_mem_openSegment (hn : 2 ≤ n) {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k)
    {A : ℝ × ℝ} (hA : A = (C.seg i).1 ∨ A = (C.seg i).2) :
    dist A (C.xpoint i k hik) < dist A (C.xpoint i j hij) ↔
      C.xpoint i k hik ∈ openSegment ℝ A (C.xpoint i j hij) := by
  obtain ⟨B, hB1, hAB⟩ : ∃ B, openSegment ℝ A B
      = openSegment ℝ (C.seg i).1 (C.seg i).2 ∧ A ≠ B := by
    rcases hA with rfl | rfl
    · exact ⟨(C.seg i).2, rfl, C.endpoints_ne hn i⟩
    · exact ⟨(C.seg i).1, openSegment_symm ℝ _ _, (C.endpoints_ne hn i).symm⟩
  have hY0 : C.xpoint i k hik ∈ openSegment ℝ (C.seg i).1 (C.seg i).2 :=
    (C.xpoint_mem i k hik).1
  have hX0 : C.xpoint i j hij ∈ openSegment ℝ (C.seg i).1 (C.seg i).2 :=
    (C.xpoint_mem i j hij).1
  rw [← hB1] at hY0 hX0
  obtain ⟨tY, htY, hYe⟩ := mem_openSegment_iff_param.mp hY0
  obtain ⟨tX, htX, hXe⟩ := mem_openSegment_iff_param.mp hX0
  have hdistAB : 0 < dist A B := dist_pos.mpr hAB
  have hnorm : ∀ t : ℝ, 0 < t → dist A (A + t • (B - A)) = t * dist A B := by
    intro t ht
    rw [dist_comm, dist_eq_norm]
    have e : A + t • (B - A) - A = t • (B - A) := by abel
    rw [e, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    have e3 : A - B = -(B - A) := by abel
    rw [dist_eq_norm, e3, norm_neg]
  constructor
  · intro hlt
    rw [hYe, hXe, hnorm tY htY.1, hnorm tX htX.1] at hlt
    have htlt : tY < tX := (mul_lt_mul_iff_of_pos_right hdistAB).mp hlt
    rw [mem_openSegment_iff_param]
    refine ⟨tY / tX, ⟨div_pos htY.1 htX.1, (div_lt_one htX.1).mpr htlt⟩, ?_⟩
    have e2 : A + tX • (B - A) - A = tX • (B - A) := by abel
    rw [hYe, hXe, e2, smul_smul, div_mul_cancel₀ _ (ne_of_gt htX.1)]
  · intro hmem
    obtain ⟨s, hs, hse⟩ := mem_openSegment_iff_param.mp hmem
    have hdX : 0 < dist A (C.xpoint i j hij) := by
      rw [hXe, hnorm tX htX.1]
      exact mul_pos htX.1 hdistAB
    have hdY : dist A (C.xpoint i k hik) = s * dist A (C.xpoint i j hij) := by
      rw [hse, hXe]
      have e2 : A + tX • (B - A) - A = tX • (B - A) := by abel
      have e : A + s • (A + tX • (B - A) - A) = A + (s * tX) • (B - A) := by
        rw [e2, smul_smul]
      rw [e, hnorm _ (mul_pos hs.1 htX.1), hnorm tX htX.1]
      ring
    rw [hdY]
    have h1 : s * dist A (C.xpoint i j hij) < 1 * dist A (C.xpoint i j hij) :=
      mul_lt_mul_of_pos_right hs.2 hdX
    rw [one_mul] at h1
    exact h1

/-- The crossing of chord `a.1` with chord `k` is closer to the start
point than the crossing `X` of the chords of `a` and `b` iff the line of
`k` separates the start point from `X`. -/
lemma dist_xpoint_lt_iff_oppSide (hn : 2 ≤ n) {a b : Fin n × Bool} (hab : a.1 ≠ b.1)
    {k : Fin n} (hak : a.1 ≠ k) :
    dist (C.segPt a) (C.xpoint a.1 k hak) < dist (C.segPt a) (C.xpoint a.1 b.1 hab) ↔
      OppSide (C.seg k).1 (C.dir k) (C.segPt a) (C.xpoint a.1 b.1 hab) := by
  rw [C.dist_xpoint_lt_iff_mem_openSegment hn hab hak (C.segPt_eq_endpoints a)]
  exact C.xpoint_mem_openSegment_iff hak (C.segPt_eq_endpoints a)
    (C.xpoint_mem a.1 b.1 hab).1

/-- The line of segment `a.1` does not separate its own endpoint from the
crossing `X` (both lie on the line). -/
lemma not_oppSide_self {a b : Fin n × Bool} (hab : a.1 ≠ b.1) :
    ¬ OppSide (C.seg a.1).1 (C.dir a.1) (C.segPt a) (C.xpoint a.1 b.1 hab) := by
  intro hO
  rw [OppSide] at hO
  have hz : detv (C.dir a.1) (C.segPt a - (C.seg a.1).1) = 0 := by
    cases h : a.2 with
    | false => rw [C.segPt_eq_fst a h, sub_self, detv_zero_right]
    | true =>
      rw [C.segPt_eq_snd a h]
      have hdir : C.dir a.1 = (C.seg a.1).2 - (C.seg a.1).1 := rfl
      rw [hdir, detv_self]
  rw [hz, zero_mul] at hO
  exact (lt_irrefl (0 : ℝ)) hO

noncomputable instance (P Q : ℝ × ℝ) :
    DecidablePred fun k : Fin n => OppSide (C.seg k).1 (C.dir k) P Q := by
  intro k
  show Decidable (OppSide (C.seg k).1 (C.dir k) P Q)
  rw [OppSide]
  infer_instance

/-- The arrival time from a segment endpoint is one plus the number of
segments whose line separates the start point from the target crossing. -/
lemma arrival_segPt_eq_card_oppSide (hn : 2 ≤ n) {a b : Fin n × Bool} (hab : a.1 ≠ b.1) :
    C.arrival a.1 b.1 hab (C.segPt a) =
      ((Finset.univ.filter fun k : Fin n =>
        OppSide (C.seg k).1 (C.dir k) (C.segPt a) (C.xpoint a.1 b.1 hab)).card) + 1 := by
  classical
  have hinj : Function.Injective fun j : {j // a.1 ≠ j} => C.xpoint a.1 j.1 j.2 := by
    intro ⟨j, hj⟩ ⟨k, hk⟩ heq
    by_contra hcon
    have hjk : j ≠ k := fun h => hcon (Subtype.ext h)
    exact C.xpoint_ne_of_ne hj hk hjk heq
  rw [arrival, crossings, Finset.filter_image, Finset.card_image_of_injective _ hinj]
  congr 1
  apply Finset.card_bij (fun (j : {j // a.1 ≠ j}) _ => (j : Fin n))
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, (C.dist_xpoint_lt_iff_oppSide hn hab j.2).mp hj⟩
  · intro j1 _ j2 _ h
    exact Subtype.ext h
  · intro k hk
    rw [Finset.mem_filter] at hk
    have hak : a.1 ≠ k := by
      intro hcon
      rw [← hcon] at hk
      exact C.not_oppSide_self hab hk.2
    exact ⟨⟨k, hak⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (C.dist_xpoint_lt_iff_oppSide hn hab hak).mpr hk.2⟩, rfl⟩

/-- The circle endpoint of `a` and its segment endpoint lie on the same
side of the line of any other segment `k`: the line of `k` meets the
chord of `a.1` at the crossing, which lies strictly between the two
circle endpoints of the chord, and the segment endpoint lies between
them too. -/
lemma sameSide_circlePt_segPt (hn : 2 ≤ n) {a : Fin n × Bool} {k : Fin n} (hak : a.1 ≠ k) :
    0 < detv (C.dir k) (C.circlePt hn a - (C.seg k).1) *
      detv (C.dir k) (C.segPt a - (C.seg k).1) := by
  obtain ⟨tY, htY01, htY, hYtY⟩ := C.xpoint_param hn a.1 k hak
  set tA := if a.2 then (C.circleParams hn a.1).2 else (C.circleParams hn a.1).1
  have htA : C.circlePt hn a = (C.seg a.1).1 + tA • C.dir a.1 := C.circlePt_eq_dir_smul hn a
  set t0 : ℝ := if a.2 then 1 else 0
  have ht0 : C.segPt a = (C.seg a.1).1 + t0 • C.dir a.1 := by
    cases h : a.2 with
    | false =>
      rw [C.segPt_eq_fst a h]
      have ht02 : t0 = 0 := by
        show (if a.2 then (1 : ℝ) else 0) = 0
        simp [h]
      rw [ht02, zero_smul, add_zero]
    | true =>
      rw [C.segPt_eq_snd a h]
      have ht02 : t0 = 1 := by
        show (if a.2 then (1 : ℝ) else 0) = 1
        simp [h]
      rw [ht02, one_smul]
      have hdir : C.dir a.1 = (C.seg a.1).2 - (C.seg a.1).1 := rfl
      rw [hdir]
      module
  have hYk : detv (C.dir k) (C.xpoint a.1 k hak - (C.seg k).1) = 0 :=
    C.detv_dir_self_left (openSegment_subset_segment _ _ _ (C.xpoint_mem a.1 k hak).2)
  set E := detv (C.dir k) (C.dir a.1)
  set D0 := detv (C.dir k) ((C.seg a.1).1 - (C.seg k).1)
  have hDY : D0 + tY * E = 0 := by
    have e : C.xpoint a.1 k hak - (C.seg k).1
        = ((C.seg a.1).1 - (C.seg k).1) + tY • C.dir a.1 := by
      rw [hYtY]
      module
    rw [e, detv_add_right, detv_smul_right] at hYk
    exact hYk
  have hDA : detv (C.dir k) (C.circlePt hn a - (C.seg k).1) = D0 + tA * E := by
    have e : C.circlePt hn a - (C.seg k).1
        = ((C.seg a.1).1 - (C.seg k).1) + tA • C.dir a.1 := by
      rw [htA]
      module
    rw [e, detv_add_right, detv_smul_right]
  have hD0 : detv (C.dir k) (C.segPt a - (C.seg k).1) = D0 + t0 * E := by
    have e : C.segPt a - (C.seg k).1
        = ((C.seg a.1).1 - (C.seg k).1) + t0 • C.dir a.1 := by
      rw [ht0]
      module
    rw [e, detv_add_right, detv_smul_right]
  rw [hDA, hD0]
  have hDA' : D0 + tA * E = (tA - tY) * E := by linear_combination hDY
  have hD0' : D0 + t0 * E = (t0 - tY) * E := by linear_combination hDY
  rw [hDA', hD0']
  have hE : E ≠ 0 := by
    have h2 : detv (C.dir a.1) (C.dir k) ≠ 0 := C.dir_ne a.1 k hak
    show detv (C.dir k) (C.dir a.1) ≠ 0
    rw [detv_antisymm]
    exact neg_ne_zero.mpr h2
  have hsgn : 0 < (tA - tY) * (t0 - tY) := by
    cases h : a.2 with
    | false =>
      have htA2 : tA = (C.circleParams hn a.1).1 := by
        show (if a.2 then (C.circleParams hn a.1).2 else (C.circleParams hn a.1).1)
          = (C.circleParams hn a.1).1
        simp [h]
      have ht02 : t0 = 0 := by
        show (if a.2 then (1 : ℝ) else 0) = 0
        simp [h]
      rw [htA2, ht02]
      exact mul_pos_of_neg_of_neg (sub_neg.mpr htY.1) (sub_neg.mpr htY01.1)
    | true =>
      have htA2 : tA = (C.circleParams hn a.1).2 := by
        show (if a.2 then (C.circleParams hn a.1).2 else (C.circleParams hn a.1).1)
          = (C.circleParams hn a.1).2
        simp [h]
      have ht02 : t0 = 1 := by
        show (if a.2 then (1 : ℝ) else 0) = 1
        simp [h]
      rw [htA2, ht02]
      exact mul_pos (sub_pos.mpr htY.2) (sub_pos.mpr htY01.2)
  have h7 : E ^ 2 > 0 := sq_pos_of_ne_zero hE
  nlinarith [hsgn, h7]

/-- For the purpose of side-testing against the line of `k`, the circle
endpoint of `a` can be replaced by the actual segment endpoint. -/
lemma oppSide_circlePt_iff_segPt (hn : 2 ≤ n) {a : Fin n × Bool} {k : Fin n} (hak : a.1 ≠ k)
    (P : ℝ × ℝ) :
    OppSide (C.seg k).1 (C.dir k) (C.circlePt hn a) P ↔
      OppSide (C.seg k).1 (C.dir k) (C.segPt a) P := by
  have hss := C.sameSide_circlePt_segPt hn hak
  by_cases hP : detv (C.dir k) (P - (C.seg k).1) = 0
  · rw [OppSide, OppSide, hP, mul_zero, mul_zero]
  · exact (sign_same_of_mul_pos hss hP).1

/-- If the chord of `k` does not separate the circle endpoints of `a`
and `b`, then the line of `k` separates both start points from `X` or
neither. -/
lemma oppSide_segPt_iff_of_not_separates (hn : 2 ≤ n) {a b : Fin n × Bool} (hab : a.1 ≠ b.1)
    {k : Fin n} (hak : a.1 ≠ k) (hbk : b.1 ≠ k)
    (hsep : ¬ C.separates k (C.circlePt hn a) (C.circlePt hn b)) :
    (OppSide (C.seg k).1 (C.dir k) (C.segPt a) (C.xpoint a.1 b.1 hab) ↔
      OppSide (C.seg k).1 (C.dir k) (C.segPt b) (C.xpoint a.1 b.1 hab)) := by
  rw [← C.oppSide_circlePt_iff_segPt hn hak, ← C.oppSide_circlePt_iff_segPt hn hbk]
  have hside : 0 < detv (C.dir k) (C.circlePt hn a - (C.seg k).1) *
      detv (C.dir k) (C.circlePt hn b - (C.seg k).1) := by
    rcases eq_or_lt_of_le (not_lt.mp hsep) with h | h
    · exact absurd h.symm (mul_ne_zero (C.detv_dir_circlePt_ne_zero hn rfl hak)
        (C.detv_dir_circlePt_ne_zero hn rfl hbk))
    · exact h
  exact (sign_same_of_mul_pos hside (C.detv_dir_xpoint_ne_zero hab hak hbk)).1

/-- If the chord of `k` separates the circle endpoints of `a` and `b`,
then the line of `k` separates the start point from `X` for exactly one
of the two. -/
lemma oppSide_segPt_xor_of_separates (hn : 2 ≤ n) {a b : Fin n × Bool} (hab : a.1 ≠ b.1)
    {k : Fin n} (hak : a.1 ≠ k) (hbk : b.1 ≠ k)
    (hsep : C.separates k (C.circlePt hn a) (C.circlePt hn b)) :
    (OppSide (C.seg k).1 (C.dir k) (C.segPt a) (C.xpoint a.1 b.1 hab) ↔
      ¬ OppSide (C.seg k).1 (C.dir k) (C.segPt b) (C.xpoint a.1 b.1 hab)) := by
  rw [← C.oppSide_circlePt_iff_segPt hn hak, ← C.oppSide_circlePt_iff_segPt hn hbk]
  have hside : detv (C.dir k) (C.circlePt hn a - (C.seg k).1) *
      detv (C.dir k) (C.circlePt hn b - (C.seg k).1) < 0 := hsep
  have hXne := C.detv_dir_xpoint_ne_zero hab hak hbk
  constructor
  · intro h
    have h2 := (sign_xor_of_mul_neg hside hXne).1.mp h
    intro h3
    exact absurd h3 (not_lt_of_gt h2)
  · intro h
    have hB2 : 0 < detv (C.dir k) (C.circlePt hn b - (C.seg k).1) *
        detv (C.dir k) (C.xpoint a.1 b.1 hab - (C.seg k).1) := by
      rcases lt_or_gt_of_ne (mul_ne_zero (C.detv_dir_circlePt_ne_zero hn rfl hbk) hXne) with h1 | h1
      · exact absurd h1 h
      · exact h1
    exact (sign_xor_of_mul_neg hside hXne).1.mpr hB2

/-- Consecutive labels index different segments. -/
lemma label_fst_ne_add_one (hn : 2 ≤ n) (m : ZMod (2 * n)) :
    (C.label hn m).1 ≠ (C.label hn (m + 1)).1 := by
  haveI : NeZero (2 * n) := ⟨by omega⟩
  intro hcon
  by_cases h2 : (C.label hn (m + 1)).2 = (C.label hn m).2
  · have h3 : C.label hn (m + 1) = C.label hn m := Prod.ext hcon.symm h2
    have h4 : m + 1 = m := C.label_injective hn h3
    have h5 : (1 : ZMod (2 * n)) = 0 := by
      have h6 : m + 1 = m + (0 : ZMod (2 * n)) := by rw [add_zero]; exact h4
      exact add_left_cancel h6
    have h7 : (1 : ZMod (2 * n)).val = 1 := by
      have h8 : ((1 : ℕ) : ZMod (2 * n)).val = 1 := ZMod.val_natCast_of_lt (by omega)
      rwa [Nat.cast_one] at h8
    rw [h5, ZMod.val_zero] at h7
    exact zero_ne_one h7
  · have h2' : (C.label hn (m + 1)).2 = !(C.label hn m).2 := Bool.eq_not_iff.mpr h2
    have h3 : C.label hn (m + 1) = ⟨(C.label hn m).1, !(C.label hn m).2⟩ := Prod.ext hcon.symm h2'
    have h4 : C.label hn (m + 1) = C.label hn (m + (n : ZMod (2 * n))) := by
      rw [h3, C.label_add_n hn m]
    have h5 : m + 1 = m + (n : ZMod (2 * n)) := C.label_injective hn h4
    have h6 : (1 : ZMod (2 * n)) = (n : ZMod (2 * n)) := add_left_cancel h5
    have h7 : (1 : ZMod (2 * n)).val = (n : ZMod (2 * n)).val := congrArg ZMod.val h6
    have h8 : (1 : ZMod (2 * n)).val = 1 := by
      have h9 : ((1 : ℕ) : ZMod (2 * n)).val = 1 := ZMod.val_natCast_of_lt (by omega)
      rwa [Nat.cast_one] at h9
    have h10 : (n : ZMod (2 * n)).val = n := ZMod.val_natCast_of_lt (by omega)
    rw [h8, h10] at h7
    omega

/-- No chord separates the circle endpoints of two consecutive labels:
such a chord would have an endpoint on the empty arc between them. -/
lemma sep_empty_of_consec (hn : 2 ≤ n) (m : ZMod (2 * n)) :
    (Finset.univ.filter fun k : Fin n =>
      C.separates k (C.circlePt hn (C.label hn m)) (C.circlePt hn (C.label hn (m + 1)))) = ∅ := by
  haveI : NeZero (2 * n) := ⟨by omega⟩
  have hab := C.label_fst_ne_add_one hn m
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro k hk
  rw [Finset.mem_filter] at hk
  have hsep : C.separates k (C.circlePt hn (C.label hn m)) (C.circlePt hn (C.label hn (m + 1))) := hk.2
  have hopp := (C.separates_iff_alternation hn hab).mp hsep
  rcases mul_neg_iff.mp hopp with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · -- `0 < D1`, `D2 < 0`: the endpoint `⟨k, true⟩` lies on the arc
    have harc : C.arcPred hn (C.label hn m) (C.label hn (m + 1)) ⟨k, true⟩ := by
      show detv (C.circlePt hn (C.label hn (m + 1)) - C.circlePt hn (C.label hn m))
        (C.circlePt hn ⟨k, true⟩ - C.circlePt hn (C.label hn m)) < 0
      rw [show C.circlePt hn ⟨k, true⟩ = (C.circlePts hn k).2 from by
        rw [circlePt, if_pos rfl]]
      exact h2
    have hne1 : (⟨k, true⟩ : Fin n × Bool) ≠ C.label hn m := by
      intro hcon
      rw [hcon] at harc
      have harc2 : detv (C.circlePt hn (C.label hn (m + 1)) - C.circlePt hn (C.label hn m))
          (C.circlePt hn (C.label hn m) - C.circlePt hn (C.label hn m)) < 0 := harc
      rw [sub_self, detv_zero_right] at harc2
      exact (lt_irrefl (0 : ℝ)) harc2
    have hne2 : (⟨k, true⟩ : Fin n × Bool) ≠ C.label hn (m + 1) := by
      intro hcon
      rw [hcon] at harc
      have harc2 : detv (C.circlePt hn (C.label hn (m + 1)) - C.circlePt hn (C.label hn m))
          (C.circlePt hn (C.label hn (m + 1)) - C.circlePt hn (C.label hn m)) < 0 := harc
      rw [detv_self] at harc2
      exact (lt_irrefl (0 : ℝ)) harc2
    exact C.consec_arc_empty hn m ⟨k, true⟩ hne1 hne2 harc
  · -- `D1 < 0`, `0 < D2`: the endpoint `⟨k, false⟩` lies on the arc
    have harc : C.arcPred hn (C.label hn m) (C.label hn (m + 1)) ⟨k, false⟩ := by
      show detv (C.circlePt hn (C.label hn (m + 1)) - C.circlePt hn (C.label hn m))
        (C.circlePt hn ⟨k, false⟩ - C.circlePt hn (C.label hn m)) < 0
      rw [show C.circlePt hn ⟨k, false⟩ = (C.circlePts hn k).1 from by
        rw [circlePt, if_neg (show ¬(false = true) from by simp)]]
      exact h1
    have hne1 : (⟨k, false⟩ : Fin n × Bool) ≠ C.label hn m := by
      intro hcon
      rw [hcon] at harc
      have harc2 : detv (C.circlePt hn (C.label hn (m + 1)) - C.circlePt hn (C.label hn m))
          (C.circlePt hn (C.label hn m) - C.circlePt hn (C.label hn m)) < 0 := harc
      rw [sub_self, detv_zero_right] at harc2
      exact (lt_irrefl (0 : ℝ)) harc2
    have hne2 : (⟨k, false⟩ : Fin n × Bool) ≠ C.label hn (m + 1) := by
      intro hcon
      rw [hcon] at harc
      have harc2 : detv (C.circlePt hn (C.label hn (m + 1)) - C.circlePt hn (C.label hn m))
          (C.circlePt hn (C.label hn (m + 1)) - C.circlePt hn (C.label hn m)) < 0 := harc
      rw [detv_self] at harc2
      exact (lt_irrefl (0 : ℝ)) harc2
    exact C.consec_arc_empty hn m ⟨k, false⟩ hne1 hne2 harc

/-- The line through the circle endpoints of `a` and `b` meets the
circle exactly in those two points. -/
lemma detv_circlePt_eq_zero_iff (hn : 2 ≤ n) {a b : Fin n × Bool} (hab : a.1 ≠ b.1)
    (q : Fin n × Bool) :
    detv (C.circlePt hn b - C.circlePt hn a) (C.circlePt hn q - C.circlePt hn a) = 0 ↔
      q = a ∨ q = b := by
  constructor
  · intro hd
    have hne : C.circlePt hn b - C.circlePt hn a ≠ 0 := by
      intro hzero
      have heq : C.circlePt hn b = C.circlePt hn a := sub_eq_zero.mp hzero
      have h3 := C.circlePt_injective hn heq
      rw [h3] at hab
      exact hab rfl
    obtain ⟨c, hc⟩ := exists_smul_of_detv_eq_zero hne hd
    have hnsq_q := C.circlePt_nsq hn q
    have hnsq_a := C.circlePt_nsq hn a
    have hnsq_b := C.circlePt_nsq hn b
    have hq2 : C.circlePt hn q
        = C.circlePt hn a + c • (C.circlePt hn b - C.circlePt hn a) := by
      have e := congrArg (fun v => v + C.circlePt hn a) hc
      rw [sub_add_cancel, add_comm] at e
      exact e
    have hw : C.circlePt hn b
        = C.circlePt hn a + (1 : ℝ) • (C.circlePt hn b - C.circlePt hn a) := by
      rw [one_smul]
      module
    rw [hq2, nsq_add_smul] at hnsq_q
    rw [hw, nsq_add_smul] at hnsq_b
    have eq_q : 2 * c * dotv (C.circlePt hn a) (C.circlePt hn b - C.circlePt hn a) +
        c ^ 2 * nsq (C.circlePt hn b - C.circlePt hn a) = 0 := by
      rw [← hnsq_a] at hnsq_q
      linarith [hnsq_q]
    have eq_b : 2 * dotv (C.circlePt hn a) (C.circlePt hn b - C.circlePt hn a) +
        nsq (C.circlePt hn b - C.circlePt hn a) = 0 := by
      rw [← hnsq_a] at hnsq_b
      linarith [hnsq_b]
    have hc01 : c * (c - 1) = 0 := by
      have h2 : nsq (C.circlePt hn b - C.circlePt hn a) * (c * (c - 1)) = 0 := by
        linear_combination eq_q - c * eq_b
      rcases mul_eq_zero.mp h2 with hnw | hc2
      · exact absurd hnw (ne_of_gt (nsq_pos_of_ne hne))
      · exact hc2
    rcases mul_eq_zero.mp hc01 with h0 | h0
    · left
      apply C.circlePt_injective hn
      rw [hq2, h0, zero_smul, add_zero]
    · right
      apply C.circlePt_injective hn
      have hc1 : c = 1 := by linarith
      rw [hq2, hc1, one_smul]
      module
  · intro h
    rcases h with rfl | rfl
    · rw [sub_self, detv_zero_right]
    · rw [detv_self]

/-- The number of chords separating the circle endpoints of `a` and `b`
is odd when the circular distance from `a` to `b` is even: it is the
size of the far arc, which is `d - 1` or `2 * n - d - 1` according to
which side the crossing lies on. -/
lemma sep_card_odd (hn : 2 ≤ n) {ma mb : ZMod (2 * n)}
    (hd : (mb - ma).val % 2 = 0) (hd0 : mb ≠ ma)
    (hab : (C.label hn ma).1 ≠ (C.label hn mb).1) :
    Odd ((Finset.univ.filter fun k : Fin n =>
      C.separates k (C.circlePt hn (C.label hn ma)) (C.circlePt hn (C.label hn mb))).card) := by
  haveI : NeZero (2 * n) := ⟨by omega⟩
  set a := C.label hn ma
  set b := C.label hn mb
  set X := C.xpoint a.1 b.1 hab
  set sX := detv (C.circlePt hn b - C.circlePt hn a) (X - C.circlePt hn a)
  have hsX : sX ≠ 0 := C.detv_xpoint_circlePt_ne_zero hn hab
  have hd1 : 1 ≤ (mb - ma).val := by
    rcases Nat.eq_zero_or_pos (mb - ma).val with h0 | h0
    · exfalso
      exact hd0 (sub_eq_zero.mp ((ZMod.val_eq_zero _).mp h0))
    · exact h0
  have hlt : (mb - ma).val < 2 * n := ZMod.val_lt _
  have harc : (Finset.univ.filter fun q : Fin n × Bool =>
      detv (C.circlePt hn b - C.circlePt hn a) (C.circlePt hn q - C.circlePt hn a) < 0).card
      = (mb - ma).val - 1 := by
    have hmk : ma + (mb - ma) = mb := by ring
    have h := C.arc_card_eq hn ma (mb - ma)
    rw [hmk] at h
    exact h
  have hab2 : a ≠ b := fun hcon => hab (by rw [hcon])
  rw [C.sep_card_eq_farArc_card hn hab]
  have hfar : (C.farArc hn a b).card = (Finset.univ.filter fun q : Fin n × Bool =>
      detv (C.circlePt hn b - C.circlePt hn a) (C.circlePt hn q - C.circlePt hn a) * sX < 0).card := by
    congr 1
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact C.mem_farArc hn hab
  rw [hfar]
  rcases lt_or_gt_of_ne hsX with hsX' | hsX'
  · -- `sX < 0`: the far arc is the positive side, of size `2 * n - d - 1`
    have hf : (Finset.univ.filter fun q : Fin n × Bool =>
        detv (C.circlePt hn b - C.circlePt hn a) (C.circlePt hn q - C.circlePt hn a) * sX < 0)
        = Finset.univ.filter fun q : Fin n × Bool =>
        0 < detv (C.circlePt hn b - C.circlePt hn a) (C.circlePt hn q - C.circlePt hn a) := by
      apply Finset.filter_congr
      intro q _
      constructor
      · intro h
        rcases mul_neg_iff.mp h with ⟨g1, g2⟩ | ⟨g1, g2⟩
        · exact g1
        · exact absurd hsX' (not_lt_of_gt g2)
      · intro h
        exact mul_neg_of_pos_of_neg h hsX'
    rw [hf]
    have hzero : (Finset.univ.filter fun q : Fin n × Bool =>
        detv (C.circlePt hn b - C.circlePt hn a) (C.circlePt hn q - C.circlePt hn a) = 0)
        = {a, b} := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      exact C.detv_circlePt_eq_zero_iff hn hab q
    have hle : (Finset.univ.filter fun q : Fin n × Bool =>
        detv (C.circlePt hn b - C.circlePt hn a) (C.circlePt hn q - C.circlePt hn a) ≤ 0)
        = (Finset.univ.filter fun q : Fin n × Bool =>
          detv (C.circlePt hn b - C.circlePt hn a) (C.circlePt hn q - C.circlePt hn a) < 0) ∪
          (Finset.univ.filter fun q : Fin n × Bool =>
          detv (C.circlePt hn b - C.circlePt hn a) (C.circlePt hn q - C.circlePt hn a) = 0) := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
      constructor
      · intro h
        rcases lt_or_eq_of_le h with h1 | h1
        · exact Or.inl h1
        · exact Or.inr h1
      · rintro (h1 | h1)
        · exact le_of_lt h1
        · exact le_of_eq h1
    have hdis : Disjoint (Finset.univ.filter fun q : Fin n × Bool =>
          detv (C.circlePt hn b - C.circlePt hn a) (C.circlePt hn q - C.circlePt hn a) < 0)
        (Finset.univ.filter fun q : Fin n × Bool =>
          detv (C.circlePt hn b - C.circlePt hn a) (C.circlePt hn q - C.circlePt hn a) = 0) := by
      rw [Finset.disjoint_filter]
      intro x _ h1 h2
      rw [h2] at h1
      exact (lt_irrefl (0 : ℝ)) h1
    have hpos : (Finset.univ.filter fun q : Fin n × Bool =>
          0 < detv (C.circlePt hn b - C.circlePt hn a) (C.circlePt hn q - C.circlePt hn a))
        = (Finset.univ.filter fun q : Fin n × Bool =>
          detv (C.circlePt hn b - C.circlePt hn a) (C.circlePt hn q - C.circlePt hn a) ≤ 0)ᶜ := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl]
      exact ⟨fun h => not_le_of_gt h, fun h => lt_of_not_ge h⟩
    rw [hpos, Finset.card_compl, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, hle,
      Finset.card_union_of_disjoint hdis, hzero, harc, Finset.card_pair hab2, Nat.odd_iff]
    omega
  · -- `sX > 0`: the far arc is the negative side, of size `d - 1`
    have hf : (Finset.univ.filter fun q : Fin n × Bool =>
        detv (C.circlePt hn b - C.circlePt hn a) (C.circlePt hn q - C.circlePt hn a) * sX < 0)
        = Finset.univ.filter fun q : Fin n × Bool =>
        detv (C.circlePt hn b - C.circlePt hn a) (C.circlePt hn q - C.circlePt hn a) < 0 := by
      apply Finset.filter_congr
      intro q _
      constructor
      · intro h
        rcases mul_neg_iff.mp h with ⟨g1, g2⟩ | ⟨g1, g2⟩
        · exact absurd g2 (not_lt_of_gt hsX')
        · exact g1
      · intro h
        exact mul_neg_of_neg_of_pos h hsX'
    rw [hf, harc, Nat.odd_iff]
    omega

/-- Frogs starting at the segment endpoints of two consecutive labels
reach the crossing of their segments at the same time: no chord
separates their circle endpoints, so every chord separates both start
points from the crossing or neither. -/
lemma arrival_segPt_eq_of_consec (hn : 2 ≤ n) (m : ZMod (2 * n))
    (hab : (C.label hn m).1 ≠ (C.label hn (m + 1)).1) :
    C.arrival (C.label hn m).1 (C.label hn (m + 1)).1 hab (C.segPt (C.label hn m))
    = C.arrival (C.label hn (m + 1)).1 (C.label hn m).1 hab.symm
      (C.segPt (C.label hn (m + 1))) := by
  haveI : NeZero (2 * n) := ⟨by omega⟩
  set a := C.label hn m
  set b := C.label hn (m + 1)
  have hX : C.xpoint b.1 a.1 hab.symm = C.xpoint a.1 b.1 hab :=
    (C.xpoint_unique b.1 a.1 hab.symm ⟨(C.xpoint_mem a.1 b.1 hab).2,
      (C.xpoint_mem a.1 b.1 hab).1⟩).symm
  rw [C.arrival_segPt_eq_card_oppSide hn hab, C.arrival_segPt_eq_card_oppSide hn hab.symm]
  have hfilter : (Finset.univ.filter fun k : Fin n =>
        OppSide (C.seg k).1 (C.dir k) (C.segPt b) (C.xpoint b.1 a.1 hab.symm))
      = (Finset.univ.filter fun k : Fin n =>
        OppSide (C.seg k).1 (C.dir k) (C.segPt b) (C.xpoint a.1 b.1 hab)) := by
    apply Finset.filter_congr
    intro k _
    rw [hX]
  rw [hfilter]
  congr 2
  apply Finset.filter_congr
  intro k _
  by_cases hka : k = a.1
  · subst hka
    constructor
    · intro h
      exact absurd h (C.not_oppSide_self hab)
    · intro h
      exfalso
      have h2 : detv (C.dir a.1) (C.segPt b - (C.seg a.1).1) *
          detv (C.dir a.1) (C.xpoint a.1 b.1 hab - (C.seg a.1).1) < 0 := h
      have hz : detv (C.dir a.1) (C.xpoint a.1 b.1 hab - (C.seg a.1).1) = 0 :=
        C.detv_dir_self_left (openSegment_subset_segment _ _ _ (C.xpoint_mem a.1 b.1 hab).1)
      rw [hz, mul_zero] at h2
      exact (lt_irrefl (0 : ℝ)) h2
  · by_cases hkb : k = b.1
    · subst hkb
      constructor
      · intro h
        exfalso
        have h2 : detv (C.dir b.1) (C.segPt a - (C.seg b.1).1) *
            detv (C.dir b.1) (C.xpoint a.1 b.1 hab - (C.seg b.1).1) < 0 := h
        have hz : detv (C.dir b.1) (C.xpoint a.1 b.1 hab - (C.seg b.1).1) = 0 :=
          C.detv_dir_self_left (openSegment_subset_segment _ _ _ (C.xpoint_mem a.1 b.1 hab).2)
        rw [hz, mul_zero] at h2
        exact (lt_irrefl (0 : ℝ)) h2
      · intro h
        rw [← hX] at h
        exact absurd h (C.not_oppSide_self hab.symm)
    · have hsep : ¬ C.separates k (C.circlePt hn a) (C.circlePt hn b) := by
        have hempty := C.sep_empty_of_consec hn m
        intro hs
        have hmem : k ∈ (Finset.univ.filter fun k : Fin n =>
            C.separates k (C.circlePt hn (C.label hn m))
              (C.circlePt hn (C.label hn (m + 1)))) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩
        rw [hempty] at hmem
        exact absurd hmem (Finset.notMem_empty k)
      exact C.oppSide_segPt_iff_of_not_separates hn hab (Ne.symm hka) (Ne.symm hkb) hsep

/-- Frogs starting at the segment endpoints of two labels an even
circular distance apart never reach the crossing of their segments at
the same time: an odd number of chords separate their circle endpoints,
and each separating chord contributes to exactly one of the two counts. -/
lemma arrival_segPt_ne_of_even (hn : 2 ≤ n) {ma mb : ZMod (2 * n)}
    (hd : (mb - ma).val % 2 = 0) (hd0 : mb ≠ ma) (_hdn : mb ≠ ma + (n : ZMod (2 * n)))
    (hab : (C.label hn ma).1 ≠ (C.label hn mb).1) :
    C.arrival (C.label hn ma).1 (C.label hn mb).1 hab (C.segPt (C.label hn ma))
    ≠ C.arrival (C.label hn mb).1 (C.label hn ma).1 hab.symm (C.segPt (C.label hn mb)) := by
  haveI : NeZero (2 * n) := ⟨by omega⟩
  set a := C.label hn ma
  set b := C.label hn mb
  have hX : C.xpoint b.1 a.1 hab.symm = C.xpoint a.1 b.1 hab :=
    (C.xpoint_unique b.1 a.1 hab.symm ⟨(C.xpoint_mem a.1 b.1 hab).2,
      (C.xpoint_mem a.1 b.1 hab).1⟩).symm
  rw [C.arrival_segPt_eq_card_oppSide hn hab, C.arrival_segPt_eq_card_oppSide hn hab.symm]
  have hfilter : (Finset.univ.filter fun k : Fin n =>
        OppSide (C.seg k).1 (C.dir k) (C.segPt b) (C.xpoint b.1 a.1 hab.symm))
      = (Finset.univ.filter fun k : Fin n =>
        OppSide (C.seg k).1 (C.dir k) (C.segPt b) (C.xpoint a.1 b.1 hab)) := by
    apply Finset.filter_congr
    intro k _
    rw [hX]
  rw [hfilter]
  intro hcon
  have hcard : (Finset.univ.filter fun k : Fin n =>
      OppSide (C.seg k).1 (C.dir k) (C.segPt a) (C.xpoint a.1 b.1 hab)).card
      = (Finset.univ.filter fun k : Fin n =>
      OppSide (C.seg k).1 (C.dir k) (C.segPt b) (C.xpoint a.1 b.1 hab)).card :=
    Nat.succ.inj hcon
  -- the separating chords are exactly the symmetric difference of the two sets
  have hsep_eq : (Finset.univ.filter fun k : Fin n =>
      C.separates k (C.circlePt hn a) (C.circlePt hn b))
      = ((Finset.univ.filter fun k : Fin n =>
          OppSide (C.seg k).1 (C.dir k) (C.segPt a) (C.xpoint a.1 b.1 hab)) \
         (Finset.univ.filter fun k : Fin n =>
          OppSide (C.seg k).1 (C.dir k) (C.segPt b) (C.xpoint a.1 b.1 hab))) ∪
        ((Finset.univ.filter fun k : Fin n =>
          OppSide (C.seg k).1 (C.dir k) (C.segPt b) (C.xpoint a.1 b.1 hab)) \
         (Finset.univ.filter fun k : Fin n =>
          OppSide (C.seg k).1 (C.dir k) (C.segPt a) (C.xpoint a.1 b.1 hab))) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_sdiff]
    by_cases hka : k = a.1
    · subst hka
      constructor
      · intro hsep
        exfalso
        have hsep2 : detv (C.dir a.1) (C.circlePt hn a - (C.seg a.1).1) *
            detv (C.dir a.1) (C.circlePt hn b - (C.seg a.1).1) < 0 := hsep
        have hz : detv (C.dir a.1) (C.circlePt hn a - (C.seg a.1).1) = 0 :=
          C.circlePt_on_line hn a
        rw [hz, zero_mul] at hsep2
        exact (lt_irrefl (0 : ℝ)) hsep2
      · intro h
        rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact absurd h1 (C.not_oppSide_self hab)
        · exfalso
          have h1' : detv (C.dir a.1) (C.segPt b - (C.seg a.1).1) *
              detv (C.dir a.1) (C.xpoint a.1 b.1 hab - (C.seg a.1).1) < 0 := h1
          have hz : detv (C.dir a.1) (C.xpoint a.1 b.1 hab - (C.seg a.1).1) = 0 :=
            C.detv_dir_self_left (openSegment_subset_segment _ _ _ (C.xpoint_mem a.1 b.1 hab).1)
          rw [hz, mul_zero] at h1'
          exact (lt_irrefl (0 : ℝ)) h1'
    · by_cases hkb : k = b.1
      · subst hkb
        constructor
        · intro hsep
          exfalso
          have hsep2 : detv (C.dir b.1) (C.circlePt hn a - (C.seg b.1).1) *
              detv (C.dir b.1) (C.circlePt hn b - (C.seg b.1).1) < 0 := hsep
          have hz : detv (C.dir b.1) (C.circlePt hn b - (C.seg b.1).1) = 0 :=
            C.circlePt_on_line hn b
          rw [hz, mul_zero] at hsep2
          exact (lt_irrefl (0 : ℝ)) hsep2
        · intro h
          rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exfalso
            have h1' : detv (C.dir b.1) (C.segPt a - (C.seg b.1).1) *
                detv (C.dir b.1) (C.xpoint a.1 b.1 hab - (C.seg b.1).1) < 0 := h1
            have hz : detv (C.dir b.1) (C.xpoint a.1 b.1 hab - (C.seg b.1).1) = 0 :=
              C.detv_dir_self_left (openSegment_subset_segment _ _ _ (C.xpoint_mem a.1 b.1 hab).2)
            rw [hz, mul_zero] at h1'
            exact (lt_irrefl (0 : ℝ)) h1'
          · rw [← hX] at h1
            exact absurd h1 (C.not_oppSide_self hab.symm)
      · have hak : a.1 ≠ k := Ne.symm hka
        have hbk : b.1 ≠ k := Ne.symm hkb
        constructor
        · intro hsep2
          have hxor := C.oppSide_segPt_xor_of_separates hn hab hak hbk hsep2
          by_cases hA : OppSide (C.seg k).1 (C.dir k) (C.segPt a) (C.xpoint a.1 b.1 hab)
          · exact Or.inl ⟨hA, hxor.mp hA⟩
          · have hB : OppSide (C.seg k).1 (C.dir k) (C.segPt b) (C.xpoint a.1 b.1 hab) := by
              by_contra hBn
              exact hA (hxor.mpr hBn)
            exact Or.inr ⟨hB, hA⟩
        · intro h
          rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · by_contra hnsep
            have hiff := C.oppSide_segPt_iff_of_not_separates hn hab hak hbk hnsep
            exact h2 (hiff.mp h1)
          · by_contra hnsep
            have hiff := C.oppSide_segPt_iff_of_not_separates hn hab hak hbk hnsep
            exact h2 (hiff.mpr h1)
  set SA := Finset.univ.filter fun k : Fin n =>
    OppSide (C.seg k).1 (C.dir k) (C.segPt a) (C.xpoint a.1 b.1 hab)
  set SB := Finset.univ.filter fun k : Fin n =>
    OppSide (C.seg k).1 (C.dir k) (C.segPt b) (C.xpoint a.1 b.1 hab)
  have hdis : Disjoint (SA \ SB) (SB \ SA) := disjoint_sdiff_sdiff
  have hcardAB' : (SA \ SB).card = (SB \ SA).card := by
    have hu1 : (SA \ SB) ∪ (SA ∩ SB) = SA := Finset.sdiff_union_inter SA SB
    have hu2 : (SB \ SA) ∪ (SB ∩ SA) = SB := Finset.sdiff_union_inter SB SA
    have hd1 : Disjoint (SA \ SB) (SA ∩ SB) := Finset.disjoint_sdiff_inter SA SB
    have hd2 : Disjoint (SB \ SA) (SB ∩ SA) := Finset.disjoint_sdiff_inter SB SA
    have hc1 : SA.card = (SA \ SB).card + (SA ∩ SB).card := by
      rw [← Finset.card_union_of_disjoint hd1, hu1]
    have hc2 : SB.card = (SB \ SA).card + (SB ∩ SA).card := by
      rw [← Finset.card_union_of_disjoint hd2, hu2]
    rw [← Finset.inter_comm] at hc2
    omega
  have hodd := C.sep_card_odd hn hd hd0 hab
  have hev : Even ((Finset.univ.filter fun k : Fin n =>
      C.separates k (C.circlePt hn a) (C.circlePt hn b)).card) := by
    rw [hsep_eq, Finset.card_union_of_disjoint hdis, hcardAB']
    exact ⟨_, rfl⟩
  exact Nat.not_even_iff_odd.mpr hodd hev

end SegConf

end Imo2016P6Geo

namespace Imo2016P6Geo

namespace SegConf

variable {n : ℕ} (C : SegConf n)

/-- If `b` is neither `a` nor the partner of `a`, the segments through
their labels differ. -/
lemma label_fst_ne_of_ne (hn : 2 ≤ n) {a b : ZMod (2 * n)}
    (hb0 : b ≠ a) (hbn : b ≠ a + (n : ZMod (2 * n))) :
    (C.label hn a).1 ≠ (C.label hn b).1 := by
  haveI : NeZero (2 * n) := ⟨by omega⟩
  intro hcon
  by_cases h2 : (C.label hn b).2 = (C.label hn a).2
  · exact hb0 (C.label_injective hn (Prod.ext hcon.symm h2))
  · have h2' : (C.label hn b).2 = !(C.label hn a).2 := Bool.eq_not_iff.mpr h2
    have h3 : C.label hn b = ⟨(C.label hn a).1, !(C.label hn a).2⟩ := Prod.ext hcon.symm h2'
    have h4 : C.label hn b = C.label hn (a + (n : ZMod (2 * n))) := by
      rw [h3, C.label_add_n hn a]
    exact hbn (C.label_injective hn h4)

/-- Arrival times are proof-irrelevant in the segment indices. -/
lemma arrival_congr {i i' k k' : Fin n} (h : i ≠ k) (h' : i' ≠ k') (hi : i = i') (hk : k = k')
    (P : ℝ × ℝ) :
    C.arrival i k h P = C.arrival i' k' h' P := by
  subst hi; subst hk; rfl

/-- The frog schedule of a segment configuration: the arrival times at
the crossings, built from the cyclic labeling of the circle endpoints. -/
noncomputable def schedule (hn : 2 ≤ n) : Imo2016P6.FrogSchedule n where
  k := fun a b =>
    if h : (C.label hn a).1 ≠ (C.label hn b).1 then
      C.arrival (C.label hn a).1 (C.label hn b).1 h (C.circlePt hn (C.label hn a))
    else 0
  k_add_n := by
    intro a b
    show (if h : (C.label hn a).1 ≠ (C.label hn b).1 then
        C.arrival (C.label hn a).1 (C.label hn b).1 h (C.circlePt hn (C.label hn a)) else 0)
      = (if h : (C.label hn a).1 ≠ (C.label hn (b + (n : ZMod (2 * n)))).1 then
        C.arrival (C.label hn a).1 (C.label hn (b + (n : ZMod (2 * n)))).1 h
          (C.circlePt hn (C.label hn a)) else 0)
    rw [C.label_add_n hn b]
  k_mem := by
    intro a b hb0 hbn
    haveI : NeZero (2 * n) := ⟨by omega⟩
    have hab : (C.label hn a).1 ≠ (C.label hn b).1 := C.label_fst_ne_of_ne hn hb0 hbn
    show 1 ≤ (if h : (C.label hn a).1 ≠ (C.label hn b).1 then
        C.arrival (C.label hn a).1 (C.label hn b).1 h (C.circlePt hn (C.label hn a)) else 0) ∧
      (if h : (C.label hn a).1 ≠ (C.label hn b).1 then
        C.arrival (C.label hn a).1 (C.label hn b).1 h (C.circlePt hn (C.label hn a)) else 0) ≤ n - 1
    rw [dif_pos hab, arrival]
    constructor
    · omega
    · have hmem : C.xpoint (C.label hn a).1 (C.label hn b).1 hab
          ∈ C.crossings (C.label hn a).1 := C.mem_crossings.mpr ⟨_, hab, rfl⟩
      have hnot : C.xpoint (C.label hn a).1 (C.label hn b).1 hab ∉
          (C.crossings (C.label hn a).1).filter
            (fun Y => dist (C.circlePt hn (C.label hn a)) Y
              < dist (C.circlePt hn (C.label hn a))
                (C.xpoint (C.label hn a).1 (C.label hn b).1 hab)) := by
        rw [Finset.mem_filter]
        push Not
        intro _
        exact le_rfl
      have hss : (C.crossings (C.label hn a).1).filter
            (fun Y => dist (C.circlePt hn (C.label hn a)) Y
              < dist (C.circlePt hn (C.label hn a))
                (C.xpoint (C.label hn a).1 (C.label hn b).1 hab))
          ⊂ C.crossings (C.label hn a).1 :=
        ⟨Finset.filter_subset _ _, fun hsub => hnot (hsub hmem)⟩
      have hcard := Finset.card_lt_card hss
      rw [C.crossings_card] at hcard
      omega
  k_inj := by
    intro a b c hb0 hbn hc0 hcn hk
    haveI : NeZero (2 * n) := ⟨by omega⟩
    have hab : (C.label hn a).1 ≠ (C.label hn b).1 := C.label_fst_ne_of_ne hn hb0 hbn
    have hac : (C.label hn a).1 ≠ (C.label hn c).1 := C.label_fst_ne_of_ne hn hc0 hcn
    have hk2 : (if h : (C.label hn a).1 ≠ (C.label hn b).1 then
        C.arrival (C.label hn a).1 (C.label hn b).1 h (C.circlePt hn (C.label hn a)) else 0)
      = (if h : (C.label hn a).1 ≠ (C.label hn c).1 then
        C.arrival (C.label hn a).1 (C.label hn c).1 h (C.circlePt hn (C.label hn a)) else 0) := hk
    rw [dif_pos hab, dif_pos hac,
      C.arrival_circlePt_eq_segPt hn (C.label hn a) (C.label hn b) hab,
      C.arrival_circlePt_eq_segPt hn (C.label hn a) (C.label hn c) hac,
      arrival, arrival] at hk2
    set A := C.segPt (C.label hn a)
    set Xb := C.xpoint (C.label hn a).1 (C.label hn b).1 hab
    set Xc := C.xpoint (C.label hn a).1 (C.label hn c).1 hac
    by_cases hdist : dist A Xb = dist A Xc
    · have hAXb : Xb ∈ C.crossings (C.label hn a).1 := C.mem_crossings.mpr ⟨_, hab, rfl⟩
      have hAXc : Xc ∈ C.crossings (C.label hn a).1 := C.mem_crossings.mpr ⟨_, hac, rfl⟩
      have heq : Xb = Xc :=
        C.dist_eq_of_mem_crossings hn (C.segPt_eq_endpoints _) hAXb hAXc hdist
      by_cases hbc : (C.label hn b).1 = (C.label hn c).1
      · by_cases h2 : (C.label hn c).2 = (C.label hn b).2
        · exact Or.inl (C.label_injective hn (Prod.ext hbc.symm h2))
        · have h2' : (C.label hn c).2 = !(C.label hn b).2 := Bool.eq_not_iff.mpr h2
          have h3 : C.label hn c = ⟨(C.label hn b).1, !(C.label hn b).2⟩ := Prod.ext hbc.symm h2'
          have h4 : C.label hn c = C.label hn (b + (n : ZMod (2 * n))) := by
            rw [h3, C.label_add_n hn b]
          exact Or.inr (C.label_injective hn h4)
      · exact absurd heq (C.xpoint_ne_of_ne hab hac hbc)
    · exfalso
      rcases lt_or_gt_of_ne hdist with hlt | hlt
      · have hss : (C.crossings (C.label hn a).1).filter (fun Y => dist A Y < dist A Xb)
            ⊂ (C.crossings (C.label hn a).1).filter (fun Y => dist A Y < dist A Xc) := by
          constructor
          · intro Y hY
            rw [Finset.mem_filter] at hY ⊢
            exact ⟨hY.1, lt_trans hY.2 hlt⟩
          · intro hsub
            have hmemXb : Xb ∈ (C.crossings (C.label hn a).1).filter
                (fun Y => dist A Y < dist A Xc) :=
              Finset.mem_filter.mpr ⟨C.mem_crossings.mpr ⟨_, hab, rfl⟩, hlt⟩
            have h2 := hsub hmemXb
            rw [Finset.mem_filter] at h2
            exact (lt_irrefl _) h2.2
        have hcard := Finset.card_lt_card hss
        omega
      · have hss : (C.crossings (C.label hn a).1).filter (fun Y => dist A Y < dist A Xc)
            ⊂ (C.crossings (C.label hn a).1).filter (fun Y => dist A Y < dist A Xb) := by
          constructor
          · intro Y hY
            rw [Finset.mem_filter] at hY ⊢
            exact ⟨hY.1, lt_trans hY.2 hlt⟩
          · intro hsub
            have hmemXc : Xc ∈ (C.crossings (C.label hn a).1).filter
                (fun Y => dist A Y < dist A Xb) :=
              Finset.mem_filter.mpr ⟨C.mem_crossings.mpr ⟨_, hac, rfl⟩, hlt⟩
            have h2 := hsub hmemXc
            rw [Finset.mem_filter] at h2
            exact (lt_irrefl _) h2.2
        have hcard := Finset.card_lt_card hss
        omega
  k_consec := by
    intro a
    haveI : NeZero (2 * n) := ⟨by omega⟩
    have hab : (C.label hn a).1 ≠ (C.label hn (a + 1)).1 := C.label_fst_ne_add_one hn a
    show (if h : (C.label hn a).1 ≠ (C.label hn (a + 1)).1 then
        C.arrival (C.label hn a).1 (C.label hn (a + 1)).1 h (C.circlePt hn (C.label hn a)) else 0)
      = (if h : (C.label hn (a + 1)).1 ≠ (C.label hn a).1 then
        C.arrival (C.label hn (a + 1)).1 (C.label hn a).1 h (C.circlePt hn (C.label hn (a + 1)))
        else 0)
    rw [dif_pos hab, dif_pos (show (C.label hn (a + 1)).1 ≠ (C.label hn a).1 from hab.symm),
      C.arrival_circlePt_eq_segPt hn (C.label hn a) (C.label hn (a + 1)) hab,
      C.arrival_circlePt_eq_segPt hn (C.label hn (a + 1)) (C.label hn a) hab.symm]
    exact C.arrival_segPt_eq_of_consec hn a hab
  k_even := by
    intro a b hd hb0 hbn
    haveI : NeZero (2 * n) := ⟨by omega⟩
    have hab : (C.label hn a).1 ≠ (C.label hn b).1 := C.label_fst_ne_of_ne hn hb0 hbn
    show (if h : (C.label hn a).1 ≠ (C.label hn b).1 then
        C.arrival (C.label hn a).1 (C.label hn b).1 h (C.circlePt hn (C.label hn a)) else 0)
      ≠ (if h : (C.label hn b).1 ≠ (C.label hn a).1 then
        C.arrival (C.label hn b).1 (C.label hn a).1 h (C.circlePt hn (C.label hn b)) else 0)
    rw [dif_pos hab, dif_pos (show (C.label hn b).1 ≠ (C.label hn a).1 from hab.symm),
      C.arrival_circlePt_eq_segPt hn (C.label hn a) (C.label hn b) hab,
      C.arrival_circlePt_eq_segPt hn (C.label hn b) (C.label hn a) hab.symm]
    exact C.arrival_segPt_ne_of_even hn hd hb0 hbn hab

end SegConf

end Imo2016P6Geo

namespace Imo2016P6Geo

/-- IMO 2016 Problem 6, part (a), in faithful geometric form: for odd
`n`, Geoff can place the frogs so that no two of them ever occupy the
same intersection point at the same time (two frogs can only meet at
the crossing of their two segments, at equal arrival times). -/
problem imo2016_p6_part_a_geo (n : ℕ) (hn : 2 ≤ n) (hodd : Odd n) (C : SegConf n) :
    ∃ f : Fin n → Bool, ∀ i j (hij : i ≠ j),
      C.arrival i j hij (if f i then (C.seg i).2 else (C.seg i).1) ≠
        C.arrival j i hij.symm (if f j then (C.seg j).2 else (C.seg j).1) := by
  obtain ⟨f', hf', hnc⟩ := Imo2016P6.imo2016_p6_part_a n hn hodd (C.schedule hn)
  haveI : NeZero (2 * n) := ⟨by omega⟩
  refine ⟨fun i => f' ((C.labelEquiv hn).symm ⟨i, true⟩), fun i j hij => ?_⟩
  set ma : ZMod (2 * n) :=
    (C.labelEquiv hn).symm ⟨i, f' ((C.labelEquiv hn).symm ⟨i, true⟩)⟩
  set mb : ZMod (2 * n) :=
    (C.labelEquiv hn).symm ⟨j, f' ((C.labelEquiv hn).symm ⟨j, true⟩)⟩
  have hma : C.label hn ma = ⟨i, f' ((C.labelEquiv hn).symm ⟨i, true⟩)⟩ :=
    Equiv.apply_symm_apply _ _
  have hmb : C.label hn mb = ⟨j, f' ((C.labelEquiv hn).symm ⟨j, true⟩)⟩ :=
    Equiv.apply_symm_apply _ _
  -- swapping the side of a label corresponds to adding `n`
  have hswap : ∀ (x : Fin n) (s : Bool),
      ((C.labelEquiv hn).symm ⟨x, !s⟩ : ZMod (2 * n))
        = (C.labelEquiv hn).symm ⟨x, s⟩ + (n : ZMod (2 * n)) := by
    intro x s
    have h2 : C.label hn ((C.labelEquiv hn).symm ⟨x, s⟩) = ⟨x, s⟩ := Equiv.apply_symm_apply _ _
    have h1 : C.label hn (((C.labelEquiv hn).symm ⟨x, s⟩) + (n : ZMod (2 * n))) = ⟨x, !s⟩ := by
      rw [C.label_add_n hn, h2]
    have h3 := (C.labelEquiv hn).injective
      (h1.trans (Equiv.apply_symm_apply (C.labelEquiv hn) ⟨x, !s⟩).symm)
    exact h3.symm
  -- both chosen endpoints carry frogs
  have hfma : f' ma = true := by
    cases hg : f' ((C.labelEquiv hn).symm ⟨i, true⟩) with
    | true =>
      have h2 : ma = (C.labelEquiv hn).symm ⟨i, true⟩ := by
        show (C.labelEquiv hn).symm ⟨i, f' ((C.labelEquiv hn).symm ⟨i, true⟩)⟩ = _
        rw [hg]
      rw [h2, hg]
    | false =>
      have h2 : ma = (C.labelEquiv hn).symm ⟨i, false⟩ := by
        show (C.labelEquiv hn).symm ⟨i, f' ((C.labelEquiv hn).symm ⟨i, true⟩)⟩ = _
        rw [hg]
      have h3 : f' (((C.labelEquiv hn).symm ⟨i, true⟩) + (n : ZMod (2 * n))) = true := by
        have h6 : (!f' (((C.labelEquiv hn).symm ⟨i, true⟩) + (n : ZMod (2 * n))))
          = f' ((C.labelEquiv hn).symm ⟨i, true⟩) := (hf' _).symm
        rw [hg] at h6
        cases hx : f' (((C.labelEquiv hn).symm ⟨i, true⟩) + (n : ZMod (2 * n))) with
        | true => rfl
        | false =>
          rw [hx] at h6
          exact Bool.noConfusion h6
      rw [h2, show (⟨i, false⟩ : Fin n × Bool) = ⟨i, !true⟩ from rfl, hswap i true, h3]
  have hfmb : f' mb = true := by
    cases hg : f' ((C.labelEquiv hn).symm ⟨j, true⟩) with
    | true =>
      have h2 : mb = (C.labelEquiv hn).symm ⟨j, true⟩ := by
        show (C.labelEquiv hn).symm ⟨j, f' ((C.labelEquiv hn).symm ⟨j, true⟩)⟩ = _
        rw [hg]
      rw [h2, hg]
    | false =>
      have h2 : mb = (C.labelEquiv hn).symm ⟨j, false⟩ := by
        show (C.labelEquiv hn).symm ⟨j, f' ((C.labelEquiv hn).symm ⟨j, true⟩)⟩ = _
        rw [hg]
      have h3 : f' (((C.labelEquiv hn).symm ⟨j, true⟩) + (n : ZMod (2 * n))) = true := by
        have h6 : (!f' (((C.labelEquiv hn).symm ⟨j, true⟩) + (n : ZMod (2 * n))))
          = f' ((C.labelEquiv hn).symm ⟨j, true⟩) := (hf' _).symm
        rw [hg] at h6
        cases hx : f' (((C.labelEquiv hn).symm ⟨j, true⟩) + (n : ZMod (2 * n))) with
        | true => rfl
        | false =>
          rw [hx] at h6
          exact Bool.noConfusion h6
      rw [h2, show (⟨j, false⟩ : Fin n × Bool) = ⟨j, !true⟩ from rfl, hswap j true, h3]
  have hne : ma ≠ mb := by
    intro hcon
    have h1 : (⟨i, f' ((C.labelEquiv hn).symm ⟨i, true⟩)⟩ : Fin n × Bool)
        = ⟨j, f' ((C.labelEquiv hn).symm ⟨j, true⟩)⟩ := by
      rw [← hma, ← hmb, hcon]
    have h2 := congrArg Prod.fst h1
    exact hij h2
  have hkl := hnc ma mb hfma hfmb hne
  -- translate the schedule arrival times back to the segment endpoints
  have hma1 : (C.label hn ma).1 = i := by rw [hma]
  have hmb1 : (C.label hn mb).1 = j := by rw [hmb]
  have hab2 : (C.label hn ma).1 ≠ (C.label hn mb).1 := by rw [hma1, hmb1]; exact hij
  have hba2 : (C.label hn mb).1 ≠ (C.label hn ma).1 := hab2.symm
  have hsk1 : (C.schedule hn).k ma mb
      = C.arrival i j hij (if f' ((C.labelEquiv hn).symm ⟨i, true⟩)
          then (C.seg i).2 else (C.seg i).1) := by
    show (if h : (C.label hn ma).1 ≠ (C.label hn mb).1 then
        C.arrival (C.label hn ma).1 (C.label hn mb).1 h (C.circlePt hn (C.label hn ma)) else 0)
      = C.arrival i j hij (if f' ((C.labelEquiv hn).symm ⟨i, true⟩)
        then (C.seg i).2 else (C.seg i).1)
    rw [dif_pos hab2]
    have he1 : C.arrival (C.label hn ma).1 (C.label hn mb).1 hab2 (C.circlePt hn (C.label hn ma))
        = C.arrival i j hij (C.circlePt hn ⟨i, f' ((C.labelEquiv hn).symm ⟨i, true⟩)⟩) := by
      rw [C.arrival_congr hab2 hij hma1 hmb1 (C.circlePt hn (C.label hn ma)), hma]
    have htr : C.arrival i j hij (C.circlePt hn ⟨i, f' ((C.labelEquiv hn).symm ⟨i, true⟩)⟩)
        = C.arrival i j hij (C.segPt ⟨i, f' ((C.labelEquiv hn).symm ⟨i, true⟩)⟩) :=
      C.arrival_circlePt_eq_segPt hn ⟨i, f' ((C.labelEquiv hn).symm ⟨i, true⟩)⟩ ⟨j, true⟩ hij
    rw [he1, htr, SegConf.segPt]
  have hsk2 : (C.schedule hn).k mb ma
      = C.arrival j i hij.symm (if f' ((C.labelEquiv hn).symm ⟨j, true⟩)
          then (C.seg j).2 else (C.seg j).1) := by
    show (if h : (C.label hn mb).1 ≠ (C.label hn ma).1 then
        C.arrival (C.label hn mb).1 (C.label hn ma).1 h (C.circlePt hn (C.label hn mb)) else 0)
      = C.arrival j i hij.symm (if f' ((C.labelEquiv hn).symm ⟨j, true⟩)
        then (C.seg j).2 else (C.seg j).1)
    rw [dif_pos hba2]
    have he2 : C.arrival (C.label hn mb).1 (C.label hn ma).1 hba2 (C.circlePt hn (C.label hn mb))
        = C.arrival j i hij.symm (C.circlePt hn ⟨j, f' ((C.labelEquiv hn).symm ⟨j, true⟩)⟩) := by
      rw [C.arrival_congr hba2 hij.symm hmb1 hma1 (C.circlePt hn (C.label hn mb)), hmb]
    have htr : C.arrival j i hij.symm (C.circlePt hn ⟨j, f' ((C.labelEquiv hn).symm ⟨j, true⟩)⟩)
        = C.arrival j i hij.symm (C.segPt ⟨j, f' ((C.labelEquiv hn).symm ⟨j, true⟩)⟩) :=
      C.arrival_circlePt_eq_segPt hn ⟨j, f' ((C.labelEquiv hn).symm ⟨j, true⟩)⟩ ⟨i, true⟩ hij.symm
    rw [he2, htr, SegConf.segPt]
  rw [hsk1, hsk2] at hkl
  exact hkl

/-- IMO 2016 Problem 6, part (b), in faithful geometric form: for even
`n`, no matter how Geoff places the frogs, two of them will eventually
occupy the same intersection point at the same time. -/
problem imo2016_p6_part_b_geo (n : ℕ) (hn : 2 ≤ n) (heven : Even n) (C : SegConf n) :
    ∀ f : Fin n → Bool, ∃ i j, ∃ (hij : i ≠ j),
      C.arrival i j hij (if f i then (C.seg i).2 else (C.seg i).1) =
        C.arrival j i hij.symm (if f j then (C.seg j).2 else (C.seg j).1) := by
  intro f
  haveI : NeZero (2 * n) := ⟨by omega⟩
  -- the placement on the cyclic labels: `f' m` iff the label `m` is the
  -- chosen endpoint of its segment
  set f' : ZMod (2 * n) → Bool := fun m => f (C.label hn m).1 == (C.label hn m).2
  have hf' : ∀ m, f' m = !f' (m + (n : ZMod (2 * n))) := by
    intro m
    have h1 : f' (m + (n : ZMod (2 * n)))
        = (f (C.label hn m).1 == !(C.label hn m).2) := by
      show (f (C.label hn (m + (n : ZMod (2 * n)))).1 == (C.label hn (m + (n : ZMod (2 * n)))).2)
        = (f (C.label hn m).1 == !(C.label hn m).2)
      rw [C.label_add_n hn m]
    show f' m = !f' (m + (n : ZMod (2 * n)))
    rw [h1]
    show (f (C.label hn m).1 == (C.label hn m).2)
      = !(f (C.label hn m).1 == !(C.label hn m).2)
    cases f (C.label hn m).1 <;> cases (C.label hn m).2 <;> rfl
  obtain ⟨a, b, ha, hb, hab, hkl⟩ :=
    Imo2016P6.imo2016_p6_part_b n hn heven (C.schedule hn) f' hf'
  have ha2 : (f (C.label hn a).1 == (C.label hn a).2) = true := ha
  have hb2 : (f (C.label hn b).1 == (C.label hn b).2) = true := hb
  have ha3 : f (C.label hn a).1 = (C.label hn a).2 := by
    cases h1 : f (C.label hn a).1 with
    | false =>
      cases h2 : (C.label hn a).2 with
      | false => rfl
      | true => rw [h1, h2] at ha2; exact Bool.noConfusion ha2
    | true =>
      cases h2 : (C.label hn a).2 with
      | false => rw [h1, h2] at ha2; exact Bool.noConfusion ha2
      | true => rfl
  have hb3 : f (C.label hn b).1 = (C.label hn b).2 := by
    cases h1 : f (C.label hn b).1 with
    | false =>
      cases h2 : (C.label hn b).2 with
      | false => rfl
      | true => rw [h1, h2] at hb2; exact Bool.noConfusion hb2
    | true =>
      cases h2 : (C.label hn b).2 with
      | false => rw [h1, h2] at hb2; exact Bool.noConfusion hb2
      | true => rfl
  have hij : (C.label hn a).1 ≠ (C.label hn b).1 := by
    intro hcon
    by_cases h2 : (C.label hn b).2 = (C.label hn a).2
    · exact hab (C.label_injective hn (Prod.ext hcon h2.symm))
    · have h2' : (C.label hn b).2 = !(C.label hn a).2 := Bool.eq_not_iff.mpr h2
      have h3 : C.label hn b = ⟨(C.label hn a).1, !(C.label hn a).2⟩ := Prod.ext hcon.symm h2'
      have h4 : C.label hn b = C.label hn (a + (n : ZMod (2 * n))) := by
        rw [h3, C.label_add_n hn a]
      have h5 : b = a + (n : ZMod (2 * n)) := C.label_injective hn h4
      have h6 := hf' a
      rw [← h5, ha, hb] at h6
      exact Bool.noConfusion h6
  refine ⟨(C.label hn a).1, (C.label hn b).1, hij, ?_⟩
  have hla : C.label hn a = ⟨(C.label hn a).1, f (C.label hn a).1⟩ := Prod.ext rfl ha3.symm
  have hlb : C.label hn b = ⟨(C.label hn b).1, f (C.label hn b).1⟩ := Prod.ext rfl hb3.symm
  have hsk1 : (C.schedule hn).k a b
      = C.arrival (C.label hn a).1 (C.label hn b).1 hij
        (if f (C.label hn a).1 then (C.seg (C.label hn a).1).2
          else (C.seg (C.label hn a).1).1) := by
    show (if h : (C.label hn a).1 ≠ (C.label hn b).1 then
        C.arrival (C.label hn a).1 (C.label hn b).1 h (C.circlePt hn (C.label hn a)) else 0)
      = C.arrival (C.label hn a).1 (C.label hn b).1 hij
        (if f (C.label hn a).1 then (C.seg (C.label hn a).1).2
          else (C.seg (C.label hn a).1).1)
    rw [dif_pos hij]
    have hla2 : C.circlePt hn (C.label hn a)
        = C.circlePt hn ⟨(C.label hn a).1, f (C.label hn a).1⟩ := by rw [hla]
    have htr : C.arrival (C.label hn a).1 (C.label hn b).1 hij
        (C.circlePt hn ⟨(C.label hn a).1, f (C.label hn a).1⟩)
        = C.arrival (C.label hn a).1 (C.label hn b).1 hij
          (C.segPt ⟨(C.label hn a).1, f (C.label hn a).1⟩) :=
      C.arrival_circlePt_eq_segPt hn ⟨(C.label hn a).1, f (C.label hn a).1⟩
        ⟨(C.label hn b).1, true⟩ hij
    rw [hla2, htr, SegConf.segPt]
  have hsk2 : (C.schedule hn).k b a
      = C.arrival (C.label hn b).1 (C.label hn a).1 hij.symm
        (if f (C.label hn b).1 then (C.seg (C.label hn b).1).2
          else (C.seg (C.label hn b).1).1) := by
    show (if h : (C.label hn b).1 ≠ (C.label hn a).1 then
        C.arrival (C.label hn b).1 (C.label hn a).1 h (C.circlePt hn (C.label hn b)) else 0)
      = C.arrival (C.label hn b).1 (C.label hn a).1 hij.symm
        (if f (C.label hn b).1 then (C.seg (C.label hn b).1).2
          else (C.seg (C.label hn b).1).1)
    rw [dif_pos hij.symm]
    have hlb2 : C.circlePt hn (C.label hn b)
        = C.circlePt hn ⟨(C.label hn b).1, f (C.label hn b).1⟩ := by rw [hlb]
    have htr : C.arrival (C.label hn b).1 (C.label hn a).1 hij.symm
        (C.circlePt hn ⟨(C.label hn b).1, f (C.label hn b).1⟩)
        = C.arrival (C.label hn b).1 (C.label hn a).1 hij.symm
          (C.segPt ⟨(C.label hn b).1, f (C.label hn b).1⟩) :=
      C.arrival_circlePt_eq_segPt hn ⟨(C.label hn b).1, f (C.label hn b).1⟩
        ⟨(C.label hn a).1, true⟩ hij.symm
    rw [hlb2, htr, SegConf.segPt]
  rw [hsk1, hsk2] at hkl
  exact hkl

end Imo2016P6Geo








/-!
# NOTES (geometric layer), 2026-07-25 — COMPLETE

The geometric layer is now complete: the schedule `SegConf.schedule` is
built and all `FrogSchedule` fields are verified, and the two faithful
geometric statements `imo2016_p6_part_a_geo` / `imo2016_p6_part_b_geo`
are proved.

## What is proved (all in namespace `Imo2016P6Geo`)

G0 — 2D determinant algebra:
  `detv` (scalar cross product on ℝ × ℝ) with add/smul/neg/sub/antisymmetry
  lemmas, `exists_smul_of_detv_eq_zero` (detv u v = 0, u ≠ 0 ⇒ v = c • u),
  `lineMeet`/`meetParam` (line intersection with parameter formula),
  `mem_openSegment_iff_param` (open segment = parameters (0,1)),
  `div_mem_Ioo` (x/y ∈ (0,1) ⇔ 0 < x·y ∧ x·y < y²).

G1 — crossing criterion:
  `oppSide_of_properCross` (proper crossing ⇒ endpoints on opposite sides),
  `properCross_of_oppSide` (converse). Sign lemmas `sign_S1`, `sign_S2`.

G2 — configuration:
  `SegConf n` (segments `seg : Fin n → (ℝ×ℝ)×(ℝ×ℝ)`; `dir_ne`: pairwise
  non-parallel directions; `crosses`: every two open segments share a point;
  `noconcur`: no three segments share a point).
  `endpoints_ne`, `xpoint` (the unique crossing), `xpoint_mem`,
  `xpoint_unique`, `xpoint_ne_of_ne`, `crossings` (n−1 crossing points per
  segment), `mem_crossings`, `crossings_card`.

G3a — region counting API:
  `openSegment_sub_openSegment` (openSegment (A,X) ⊆ openSegment (a,a') when
  A ∈ segment, X ∈ openSegment), `detv_dir_self_left` (points of a segment
  have detv = 0 against its direction), `oppSide_smul_dir` (OppSide invariant
  under nonzero rescaling of the direction), `exists_smul_dir_sub_endpoint`
  (X − A = c • dir i, c ≠ 0), `xpoint_mem_openSegment_iff`:
    xpoint i k ∈ openSegment (A, X) ⇔ OppSide (seg k).1 (dir k) A X
  (THE entry point of the region counting). `sign_xor_of_mul_neg`,
  `sign_same_of_mul_pos` (pure sign dichotomy), line-meet uniqueness
  `eq_of_detv_eq_zero_of_detv_eq_zero`, `detv_dir_xpoint_ne_zero`
  (the crossing of i,j is not on the line of k — from `noconcur`).

## Key mathematical fact behind the region counting (already formalized)

For chords (a,a'), (b,b') crossing at X and a third chord c = (p,p'):
  c crosses piece (a,X)  ⇔  OppSide p (dir c) a X
  c crosses piece (b,X)  ⇔  OppSide p (dir c) b X
Write A := detv w (a−p), B := detv w (b−p), S := detv w (X−p) ≠ 0
(`detv_dir_xpoint_ne_zero`). Then `sign_xor_of_mul_neg` says: if
A·B < 0 (a, b on opposite sides of line c ⟺ c separates a from b) exactly
one piece is crossed; `sign_same_of_mul_pos` says: if A·B > 0, both or
neither. Therefore, with M the number of chords crossing both pieces,
  k_a(X) − 1 = M + A',  k_b(X) − 1 = M + B',  A' + B' = #separating chords,
so k_a = k_b ⇔ A' = B' (impossible when #sep is odd; forced when #sep = 0).

## Refined understanding from numerical experiments (2026-07-25, session 2)

* The crossing-order and collision structure was validated on ~20 random
  convex configurations (parabola model):
  - for a pair (a, b) with d = cyclic distance (1 ≤ d ≤ n−1), writing X
    for the crossing of the chords through a and b:
    k_a(X) + k_b(X) = (d + 1) + 2M (M = #chords crossing both pieces);
    collision ⟺ k_a = k_b ⟺ (d odd and balanced A′ = B′ = (d−1)/2).
  - the first crossing from A on its segment has k_A = 1, but the
    first-crossing partner B is NOT necessarily the cyclic successor of A:
    the d-arc arc(A, B) can have any size, and k_B(X) = 1 + B′ with
    B′ = #{arc(A,B)-chords crossing piece (B,X)} ≥ 0. So the cyclic order
    must NOT be defined via the first-crossing map.
  - the original endpoints can be COLLINEAR with a third one (explicit
    3-segment counterexample satisfying all hypotheses), i.e. the original
    endpoints are not always in strictly convex position. The circle
    extension is therefore essential, not cosmetic: it replaces the
    endpoints by 2n points on a large circle (always strictly convex),
    without changing the crossing points or their order along each
    segment, hence without changing any arrival time.

## Completion record (what the later sections of the file actually do)

1. CIRCLE EXTENSION (done). Center (0,0), radius
   `r := 1 + Σᵢ Σⱼ √(nsq (nxpoint i j))` strictly dominates all
   crossings. `quadratic_roots` (with `Real.sqrt`) gives the two circle
   parameters of each chord line; `circlePts`, `circlePt` (the 2n circle
   endpoints, injective), `arrival` and the transfers
   `arrival_eq_circlePt_fst/snd` (frog dynamics from a segment endpoint
   equals dynamics from its circle endpoint).

2. CYCLIC LABELING (done). `theta := Complex.arg ∘ toC` gives the angle;
   `arcPred a b q := detv (circlePt b − circlePt a) (circlePt q −
   circlePt a) < 0` is the (reducible) arc predicate; `arcRank` and
   `labelEquiv`/`label : ZMod (2n) → Fin n × Bool` (a bijection in
   increasing-angle order). Key facts: `label_add_n` (antipodality:
   partner of label m is label (m+n), from `card_sides`), `arc_card_eq`
   (arc from m to m+k has exactly k.val − 1 points), `consec_arc_empty`,
   `arcPred_label_iff` (arc membership by ZMod distances).

3. SEPARATION COUNTING (done). `separates k A B` (endpoints on opposite
   sides of the chord line k) ⟺ alternation
   (`separates_iff_alternation`); `farArc a b` (endpoints on the side of
   line AB opposite the crossing X); `sep_card_eq_farArc_card` (the
   bijection chord ↦ its far-arc endpoint); `sep_card_odd` (#sep is odd
   when the circular distance is even: the far arc has d−1 or 2n−d−1
   points, both odd).

4. COUNTING BRIDGE (done). `segPt` (the segment endpoint on the side of
   a circle endpoint); `dist_xpoint_lt_iff_mem_openSegment` and
   `xpoint_mem_openSegment_iff` give
   `arrival_segPt_eq_card_oppSide` (arrival = 1 + #lines separating the
   start from the target crossing). The dichotomy:
   `oppSide_segPt_iff_of_not_separates` / `oppSide_segPt_xor_of_separates`
   (via `sameSide_circlePt_segPt` and the sign lemmas). Consequences:
   `sep_empty_of_consec` ⟹ `arrival_segPt_eq_of_consec`;
   `sep_card_odd` + symmetric-difference argument ⟹
   `arrival_segPt_ne_of_even`.

5. SCHEDULE (done). `schedule : FrogSchedule n` with
   `k a b := arrival (label a).1 (label b).1 _ (circlePt (label a))`.
   Fields: `k_consec`/`k_even` from the two arrival lemmas (via
   `arrival_circlePt_eq_segPt`), `k_add_n` from `label_add_n`, `k_mem`
   from `crossings_card` (the target crossing itself is not counted),
   `k_inj` from `dist_eq_of_mem_crossings` + `xpoint_ne_of_ne`.

6. WIRING (done). The old schedule-conditional statements are the
   lemmas `Imo2016P6.imo2016_p6_part_a/b`; the faithful geometric
   problems `imo2016_p6_part_a_geo` (odd n: ∃ placement with no equal
   arrival times) and `imo2016_p6_part_b_geo` (even n: ∀ placement, ∃
   pair with equal arrival times) are proved by transporting placements
   between `Fin n → Bool` (segment sides) and `ZMod (2n) → Bool` (circle
   endpoints) via `labelEquiv`.

## Design notes / pitfalls encountered

- detv (2D cross product) on ℝ × ℝ replaces any circle/cyclic-order API:
  all side/betweenness relations are determinant signs.
- "cross" in SegConf is proper crossing with non-parallel directions
  (faithful: collinear overlapping segments do not cross in the intended
  sense and would make the frog process ill-defined).
- `openSegment 𝕜 x x = {x}` (not ∅!); degenerate directions are excluded
  by `dir_ne` whenever another segment exists.
- `module` tactic closes vector identities with smul where `abel` fails.
- Hypotheses of def-type predicates (OppSide/SameSide) must be unfolded
  (or type-ascribed) before `rw`.
-/
