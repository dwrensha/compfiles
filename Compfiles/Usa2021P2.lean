/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw, Kimi K3
-/

module

public import Mathlib.Tactic
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics] }

/-!
# USA Mathematical Olympiad 2021, Problem 2

The Planar National Park is a subset of the Euclidean plane consisting of several
trails which meet at junctions. Every trail has its two endpoints at two different
junctions, whereas each junction is the endpoint of exactly three trails. Trails
only intersect at junctions (in particular, trails only meet at endpoints).
Finally, no trails begin and end at the same two junctions.

A visitor walks through the park as follows: she begins at a junction and starts
walking along a trail. At the end of that first trail, she enters a junction and
turns left. On the next junction she turns right, and so on, alternating left and
right turns at each junction. She does this until she gets back to the junction
where she started. What is the largest possible number of times she could have
entered any junction during her walk, over all possible layouts of the park?

# Formalization notes

A park is axiomatized below as a finite simple 3-regular graph equipped with a
rotation system (`Park`). The example park `Park.wangPark` is the example of
Danielle Wang from the official solution.
-/

namespace Usa2021P2

snip begin

/-- A *park*: the combinatorial data of the Planar National Park, namely a finite
simple graph (the junctions and trails) that is 3-regular (each junction is the
endpoint of exactly three trails), together with a *rotation system* `rot`
giving the cyclic order of the three trails at each junction (as provided by a
planar layout; `rot v` sends each neighbour of `v` to the next one clockwise).

Turning "left" at a junction `v`, having arrived from `u`, means leaving towards
`rot v u`; turning "right" means leaving towards `rot v (rot v u)`. -/
structure Park where
  V : Type
  [fintypeV : Fintype V]
  [decidableEqV : DecidableEq V]
  /-- the trails of the park -/
  G : SimpleGraph V
  [decidableAdj : DecidableRel G.Adj]
  /-- each junction is the endpoint of exactly three trails -/
  cubic : ∀ v, (Finset.univ.filter fun u ↦ G.Adj v u).card = 3
  /-- the cyclic order of the trails at a junction -/
  rot : V → V → V
  rot_adj : ∀ u v, G.Adj v u → G.Adj v (rot v u)
  rot_ne : ∀ u v, G.Adj v u → rot v u ≠ u
  rot_inv : ∀ u v, G.Adj v u → rot v (rot v (rot v u)) = u

namespace Park

instance (P : Park) : Fintype P.V := P.fintypeV
instance (P : Park) : DecidableEq P.V := P.decidableEqV
instance (P : Park) : DecidableRel P.G.Adj := P.decidableAdj

variable (P : Park)

/-- Leaving junction `v` (having arrived from `u`) by the trail on the left
(`p = true`) or on the right (`p = false`). -/
def turn (v u : P.V) (p : Bool) : P.V :=
  cond p (P.rot v u) (P.rot v (P.rot v u))

lemma turn_adj {u v : P.V} (h : P.G.Adj v u) (p : Bool) :
    P.G.Adj v (P.turn v u p) := by
  cases p
  · exact P.rot_adj _ _ (P.rot_adj _ _ h)
  · exact P.rot_adj _ _ h

lemma rot_inv_ne {u v : P.V} (h : P.G.Adj v u) : P.rot v (P.rot v u) ≠ u := by
  intro h2
  have h3 := P.rot_inv _ _ h
  rw [h2] at h3
  exact P.rot_ne _ _ h h3

/-- The visitor never leaves a junction by the trail she arrived on. -/
lemma turn_ne {u v : P.V} (h : P.G.Adj v u) (p : Bool) : P.turn v u p ≠ u := by
  cases p
  · exact P.rot_inv_ne h
  · exact P.rot_ne _ _ h

/-- Turning one way and then, from the same junction, the other way undoes the
turn: `rot` and `rot ∘ rot` are inverse 3-cycles on the neighbours. -/
lemma turn_inv_turn {u v : P.V} (h : P.G.Adj v u) (p : Bool) :
    P.turn v (P.turn v u p) (!p) = u := by
  cases p <;> exact P.rot_inv _ _ h

lemma turn_inj {u₁ u₂ v : P.V} (h₁ : P.G.Adj v u₁) (h₂ : P.G.Adj v u₂) (p : Bool)
    (h : P.turn v u₁ p = P.turn v u₂ p) : u₁ = u₂ := by
  have h' := congrArg (fun w ↦ P.turn v w (!p)) h
  rw [P.turn_inv_turn h₁ p, P.turn_inv_turn h₂ p] at h'
  exact h'

/-- A turn and its mirror image cannot both be turns in the same direction:
the 3-cycle `turn v · p` has no 2-cycle. -/
lemma turn_not_two_cycle {a c v : P.V} (ha : P.G.Adj v a) (p : Bool)
    (hac : P.turn v a p = c) (hca : P.turn v c p = a) : False := by
  cases p
  · have hac' : P.rot v (P.rot v a) = c := hac
    have hca' : P.rot v (P.rot v c) = a := hca
    have h5 : P.rot v (P.rot v (P.rot v (P.rot v a))) = a := by
      have h7 : P.rot v (P.rot v (P.rot v (P.rot v a))) = P.rot v (P.rot v c) := by
        rw [hac']
      rw [h7, hca']
    have h6 : P.rot v (P.rot v (P.rot v (P.rot v a))) = P.rot v a := by
      rw [P.rot_inv _ _ ha]
    rw [h6] at h5
    exact P.rot_ne _ _ ha h5
  · have hac' : P.rot v a = c := hac
    have hca' : P.rot v c = a := hca
    have h2 : P.rot v (P.rot v a) = a := by
      rw [hac']
      exact hca'
    exact P.rot_inv_ne ha h2

/-- The states of the visitor that occur in a walk: the junction she came from
and the junction she has just entered are joined by a trail. The last component
is the direction of her next turn (`true` = left). -/
def Valid (σ : P.V × P.V × Bool) : Prop := P.G.Adj σ.2.1 σ.1

instance (σ : P.V × P.V × Bool) : Decidable (P.Valid σ) :=
  inferInstanceAs (Decidable (P.G.Adj σ.2.1 σ.1))

/-- One step of the walk: turn at the current junction and traverse the chosen
trail; the next turn has the opposite direction. -/
def step (σ : P.V × P.V × Bool) : P.V × P.V × Bool :=
  (σ.2.1, P.turn σ.2.1 σ.1 σ.2.2, !σ.2.2)

/-- The inverse step: the process is deterministic in both directions. -/
def stepInv (σ : P.V × P.V × Bool) : P.V × P.V × Bool :=
  (P.turn σ.1 σ.2.1 σ.2.2, σ.1, !σ.2.2)

lemma valid_step {σ : P.V × P.V × Bool} (h : P.Valid σ) : P.Valid (P.step σ) :=
  (P.turn_adj h σ.2.2).symm

lemma valid_stepInv {σ : P.V × P.V × Bool} (h : P.Valid σ) : P.Valid (P.stepInv σ) :=
  P.turn_adj h.symm σ.2.2

lemma stepInv_step {σ : P.V × P.V × Bool} (h : P.Valid σ) :
    P.stepInv (P.step σ) = σ := by
  obtain ⟨u, v, p⟩ := σ
  exact Prod.ext (P.turn_inv_turn h p) (Prod.ext rfl (Bool.not_not p))

lemma step_stepInv {σ : P.V × P.V × Bool} (h : P.Valid σ) :
    P.step (P.stepInv σ) = σ := by
  obtain ⟨u, v, p⟩ := σ
  exact Prod.ext rfl (Prod.ext (P.turn_inv_turn h.symm p) (Bool.not_not p))

lemma step_injective {σ τ : P.V × P.V × Bool} (hσ : P.Valid σ) (hτ : P.Valid τ)
    (h : P.step σ = P.step τ) : σ = τ := by
  rw [← P.stepInv_step hσ, ← P.stepInv_step hτ, h]

lemma valid_walk {σ₀ : P.V × P.V × Bool} (h₀ : P.Valid σ₀) (k : ℕ) :
    P.Valid (P.step^[k] σ₀) := by
  induction k with
  | zero => exact h₀
  | succ k ih => rw [Function.iterate_succ_apply']; exact P.valid_step ih

/-- The direction of the turns alternates between left and right. -/
lemma parity_walk (σ₀ : P.V × P.V × Bool) (k : ℕ) :
    (P.step^[k] σ₀).2.2 = if Even k then σ₀.2.2 else !σ₀.2.2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    show (!(P.step^[k] σ₀).2.2) = _
    rw [ih]
    by_cases hk : Even k
    · rw [ite_eq_left hk, ite_eq_right (by simp [Nat.even_add_one, hk])]
    · rw [ite_eq_right hk, Bool.not_not, ite_eq_left (by simp [Nat.even_add_one, hk])]

lemma stepInv_iterate {σ₀ : P.V × P.V × Bool} (h₀ : P.Valid σ₀) :
    ∀ {i j : ℕ}, i ≤ j → P.stepInv^[i] (P.step^[j] σ₀) = P.step^[j - i] σ₀ := by
  intro i
  induction i with
  | zero => intro j _
            rfl
  | succ i ih =>
    intro j hij
    have h1 : P.stepInv (P.step^[j] σ₀) = P.step^[j - 1] σ₀ := by
      conv_lhs => rw [show j = j - 1 + 1 by lia, Function.iterate_succ_apply']
      rw [P.stepInv_step (P.valid_walk h₀ _)]
    rw [Function.iterate_succ_apply, h1, ih (by lia : i ≤ j - 1)]
    congr 1
    lia

/-- If two iterates of the walk agree, the orbit has closed up with period
`j - i`. -/
lemma eq_of_walk_eq {σ₀ : P.V × P.V × Bool} (h₀ : P.Valid σ₀) {i j : ℕ} (hij : i ≤ j)
    (h : P.step^[i] σ₀ = P.step^[j] σ₀) : P.step^[j - i] σ₀ = σ₀ := by
  have key : P.stepInv^[i] (P.step^[i] σ₀) = σ₀ := by
    have h1 := P.stepInv_iterate h₀ (i := i) (j := i) le_rfl
    rw [Nat.sub_self] at h1
    exact h1
  rw [h, P.stepInv_iterate h₀ hij] at key
  exact key

/-- The walk is periodic: some positive iterate returns to the initial state. -/
lemma exists_period {σ₀ : P.V × P.V × Bool} (h₀ : P.Valid σ₀) :
    ∃ T > 0, P.step^[T] σ₀ = σ₀ := by
  obtain ⟨i, hi, j, hj, hne, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to
      (s := Finset.range (Fintype.card {σ : P.V × P.V × Bool // P.Valid σ} + 1))
      (t := (Finset.univ : Finset {σ : P.V × P.V × Bool // P.Valid σ}))
      (f := fun k ↦ (⟨P.step^[k] σ₀, P.valid_walk h₀ k⟩ :
        {σ : P.V × P.V × Bool // P.Valid σ}))
      (by simp only [Finset.card_univ, Finset.card_range]; lia)
      (fun _ _ ↦ Finset.mem_univ _)
  have heq' : P.step^[i] σ₀ = P.step^[j] σ₀ := congrArg Subtype.val heq
  rcases le_total i j with hij | hji
  · exact ⟨j - i, by lia, P.eq_of_walk_eq h₀ hij heq'⟩
  · exact ⟨i - j, by lia, P.eq_of_walk_eq h₀ hji heq'.symm⟩

/-- The (minimal) period of the walk from `σ₀`. -/
noncomputable def period {σ₀ : P.V × P.V × Bool} (h₀ : P.Valid σ₀) : ℕ :=
  Nat.find (P.exists_period h₀)

lemma period_pos {σ₀ : P.V × P.V × Bool} (h₀ : P.Valid σ₀) : 0 < P.period h₀ :=
  (Nat.find_spec (P.exists_period h₀)).1

lemma period_eq {σ₀ : P.V × P.V × Bool} (h₀ : P.Valid σ₀) :
    P.step^[P.period h₀] σ₀ = σ₀ :=
  (Nat.find_spec (P.exists_period h₀)).2

lemma period_ne_of_lt {σ₀ : P.V × P.V × Bool} (h₀ : P.Valid σ₀) {k : ℕ} (hk0 : 0 < k)
    (hk : k < P.period h₀) : P.step^[k] σ₀ ≠ σ₀ := by
  intro h'
  have hle : P.period h₀ ≤ k := Nat.find_min' (P.exists_period h₀) ⟨hk0, h'⟩
  lia

/-- The iterates of the walk within one period are pairwise distinct. -/
lemma walk_inj_of_lt_period {σ₀ : P.V × P.V × Bool} (h₀ : P.Valid σ₀) {i j : ℕ}
    (hi : i < P.period h₀) (hj : j < P.period h₀)
    (h : P.step^[i] σ₀ = P.step^[j] σ₀) : i = j := by
  rcases le_total i j with hij | hji
  · rcases eq_or_lt_of_le hij with rfl | hlt
    · rfl
    · exact absurd (P.eq_of_walk_eq h₀ hij h) (P.period_ne_of_lt h₀ (by lia) (by lia))
  · rcases eq_or_lt_of_le hji with rfl | hlt
    · rfl
    · exact absurd (P.eq_of_walk_eq h₀ hji h.symm) (P.period_ne_of_lt h₀ (by lia) (by lia))

/-- The period is at least two: one step never returns to the initial state. -/
lemma one_lt_period {σ₀ : P.V × P.V × Bool} (h₀ : P.Valid σ₀) : 1 < P.period h₀ := by
  have hpos := P.period_pos h₀
  by_contra h
  push Not at h
  have h1 : P.period h₀ = 1 := by lia
  have heq := P.period_eq h₀
  rw [h1] at heq
  obtain ⟨u, v, p⟩ := σ₀
  have hfst : v = u := congrArg Prod.fst heq
  exact h₀.ne hfst

/-- The walk enters the starting junction again one step before the period. -/
lemma return_at_period_sub_one {σ₀ : P.V × P.V × Bool} (h₀ : P.Valid σ₀) :
    0 < P.period h₀ - 1 ∧ (P.step^[P.period h₀ - 1] σ₀).2.1 = σ₀.1 := by
  have h2 := P.one_lt_period h₀
  refine ⟨by lia, ?_⟩
  have hstep : P.step (P.step^[P.period h₀ - 1] σ₀) = σ₀ := by
    have h := P.period_eq h₀
    rw [show P.period h₀ = P.period h₀ - 1 + 1 by lia,
      Function.iterate_succ_apply'] at h
    exact h
  have hInv : P.step^[P.period h₀ - 1] σ₀ = P.stepInv σ₀ :=
    P.step_injective (P.valid_walk h₀ _) (P.valid_stepInv h₀)
      (hstep.trans (P.step_stepInv h₀).symm)
  rw [hInv]
  rfl

/-- The visitor always gets back to the junction where she started. -/
lemma exists_return {σ₀ : P.V × P.V × Bool} (h₀ : P.Valid σ₀) :
    ∃ k > 0, (P.step^[k] σ₀).2.1 = σ₀.1 :=
  ⟨P.period h₀ - 1, (P.return_at_period_sub_one h₀).1, (P.return_at_period_sub_one h₀).2⟩

/-- The first time (`> 0`) at which the walk re-enters the starting junction. -/
noncomputable def retTime {σ₀ : P.V × P.V × Bool} (h₀ : P.Valid σ₀) : ℕ :=
  Nat.find (P.exists_return h₀)

lemma retTime_pos {σ₀ : P.V × P.V × Bool} (h₀ : P.Valid σ₀) : 0 < P.retTime h₀ :=
  (Nat.find_spec (P.exists_return h₀)).1

lemma retTime_eq {σ₀ : P.V × P.V × Bool} (h₀ : P.Valid σ₀) :
    (P.step^[P.retTime h₀] σ₀).2.1 = σ₀.1 :=
  (Nat.find_spec (P.exists_return h₀)).2

lemma retTime_min {σ₀ : P.V × P.V × Bool} (h₀ : P.Valid σ₀) {k : ℕ} (hk0 : 0 < k)
    (hk : k < P.retTime h₀) : (P.step^[k] σ₀).2.1 ≠ σ₀.1 := by
  intro h
  have hle : P.retTime h₀ ≤ k := Nat.find_min' (P.exists_return h₀) ⟨hk0, h⟩
  lia

lemma retTime_le_period_sub_one {σ₀ : P.V × P.V × Bool} (h₀ : P.Valid σ₀) :
    P.retTime h₀ ≤ P.period h₀ - 1 :=
  Nat.find_min' _ (P.return_at_period_sub_one h₀)

/-- The number of times the visitor enters junction `v` during her walk, from the
initial state `σ₀` until she gets back to the starting junction (the final
re-entry into the starting junction counts, the departure from it does not). -/
noncomputable def entries (σ₀ : P.V × P.V × Bool) (h₀ : P.Valid σ₀) (v : P.V) : ℕ :=
  ((Finset.range (P.retTime h₀)).filter fun k ↦ (P.step^[k] σ₀).2.1 = v).card +
    if v = σ₀.1 then 1 else 0

/-- The key lemma: a trajectory never contains a turn and its mirror image,
i.e. turns `a → b → c` and `c → b → a` through the same junction. Otherwise the
turns adjacent to them at `c` would again be mirror images of each other, with a
strictly smaller gap — an infinite descent. -/
theorem no_mirror {σ₀ : P.V × P.V × Bool} (h₀ : P.Valid σ₀) :
    ∀ n : ℕ, ∀ (i : ℕ) (a b c : P.V) (p q : Bool),
      1 ≤ n → P.step^[i] σ₀ = (a, (b, p)) → P.step^[i + n] σ₀ = (c, (b, q)) →
      P.turn b a p = c → P.turn b c q = a → False := by
  intro n
  refine Nat.strongRecOn n fun n IH i a b c p q hn hi hin habc hcba ↦ ?_
  have hab : P.G.Adj b a := by
    have hv := P.valid_walk h₀ i
    rw [hi] at hv
    exact hv
  have hcb : P.G.Adj b c := habc ▸ P.turn_adj hab p
  rcases Nat.lt_or_ge n 2 with hsmall | hbig
  · -- `n = 1`: consecutive states would force `b = c`, contradicting adjacency.
    have hn1 : n = 1 := by lia
    rw [hn1, Function.iterate_succ_apply', hi] at hin
    have hbc : b = c := congrArg Prod.fst hin
    exact hcb.ne hbc
  · -- `n ≥ 2`
    have hqp : q = !p := by
      by_cases h : q = p
      · rw [h] at hcba
        exact (P.turn_not_two_cycle hab p habc hcba).elim
      · cases q <;> cases p <;> simp_all
    have hpar : (P.step^[i + n] σ₀).2.2 = if Even n then p else !p := by
      rw [show i + n = n + i by lia, Function.iterate_add_apply, P.parity_walk, hi]
    have hq2 : (P.step^[i + n] σ₀).2.2 = q := by rw [hin]
    rw [hpar, hqp] at hq2
    have hnodd : ¬ Even n := by
      intro he
      rw [ite_eq_left he] at hq2
      cases p <;> simp at hq2
    have hn3 : 3 ≤ n := by
      rw [Nat.even_iff] at hnodd
      lia
    -- the mirror pair at `c`, with the strictly smaller gap `n - 2`
    set u := P.turn c b (!p) with hu
    have hcb' : P.G.Adj c b := hcb.symm
    have hu_eq : P.turn c u p = b := by
      rw [hu]
      have h2 := P.turn_inv_turn hcb' (!p)
      rw [Bool.not_not] at h2
      exact h2
    have hi1 : P.step^[i + 1] σ₀ = (b, (c, !p)) := by
      rw [Function.iterate_succ_apply', hi]
      exact Prod.ext rfl (Prod.ext habc rfl)
    have hin1 : P.step^[i + n - 1] σ₀ = (u, (c, p)) := by
      have hnm1 : i + n - 1 + 1 = i + n := by lia
      have hstep : P.step (P.step^[i + n - 1] σ₀) = (c, (b, q)) := by
        rw [← hnm1, Function.iterate_succ_apply'] at hin
        exact hin
      have hstep2 : P.step (P.step^[i + n - 1] σ₀) =
          P.step ((u, (c, p)) : P.V × P.V × Bool) := by
        rw [hstep]
        show (c, (b, q)) = (c, (P.turn c u p, !p))
        rw [hu_eq, ← hqp]
      have hvalid : P.Valid ((u, (c, p)) : P.V × P.V × Bool) := by
        rw [hu]
        exact P.turn_adj hcb' (!p)
      exact P.step_injective (P.valid_walk h₀ _) hvalid hstep2
    exact IH (n - 2) (by lia) (i + 1) b c u (!p) p (by lia) hi1
      (by rw [show i + 1 + (n - 2) = i + n - 1 by lia]; exact hin1) hu.symm hu_eq

/-- In one period of the walk, any junction is entered at most three times: the
(at most six) turns at `v` pair up into three mirror pairs, of which at most one
turn each can occur by `no_mirror`. -/
theorem arrivals_le_three {σ₀ : P.V × P.V × Bool} (h₀ : P.Valid σ₀) (v : P.V) :
    ((Finset.range (P.period h₀)).filter
      fun k ↦ (P.step^[k] σ₀).2.1 = v).card ≤ 3 := by
  set F := (Finset.range (P.period h₀)).filter fun k ↦ (P.step^[k] σ₀).2.1 = v with hF
  set φ : ℕ → P.V × Bool := fun k ↦ ((P.step^[k] σ₀).1, (P.step^[k] σ₀).2.2) with hφ
  have φfst : ∀ k, (φ k).1 = (P.step^[k] σ₀).1 := fun _ ↦ rfl
  have φsnd : ∀ k, (φ k).2 = (P.step^[k] σ₀).2.2 := fun _ ↦ rfl
  set T : Finset (P.V × Bool) :=
    (Finset.univ.filter fun u ↦ P.G.Adj v u) ×ˢ Finset.univ with hT
  have hTcard : T.card = 6 := by
    rw [hT, Finset.card_product, P.cubic v, Finset.card_univ, Fintype.card_bool]
  have hmaps : Set.MapsTo φ F T := by
    intro k hk
    simp only [hF, Finset.mem_coe, Finset.mem_filter] at hk
    have hadj : P.G.Adj v (P.step^[k] σ₀).1 := by
      have hv := P.valid_walk h₀ k
      simp only [Park.Valid] at hv
      rw [hk.2] at hv
      exact hv
    simp only [hT, Finset.mem_coe, Finset.mem_product, Finset.mem_filter]
    exact ⟨⟨Finset.mem_univ _, hadj⟩, Finset.mem_univ _⟩
  have hinj : Set.InjOn φ F := by
    intro k₁ hk₁ k₂ hk₂ h
    simp only [hF, Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hk₁ hk₂
    have h1 : (P.step^[k₁] σ₀).1 = (P.step^[k₂] σ₀).1 := by
      have h' := congrArg Prod.fst h
      rw [φfst, φfst] at h'
      exact h'
    have h2 : (P.step^[k₁] σ₀).2.2 = (P.step^[k₂] σ₀).2.2 := by
      have h' := congrArg Prod.snd h
      rw [φsnd, φsnd] at h'
      exact h'
    have htri : P.step^[k₁] σ₀ = P.step^[k₂] σ₀ :=
      calc P.step^[k₁] σ₀
          = ((P.step^[k₁] σ₀).1, ((P.step^[k₁] σ₀).2.1, (P.step^[k₁] σ₀).2.2)) :=
            (Prod.mk.eta).symm
        _ = ((P.step^[k₂] σ₀).1, ((P.step^[k₂] σ₀).2.1, (P.step^[k₂] σ₀).2.2)) := by
            rw [h1, hk₁.2, hk₂.2, h2]
        _ = P.step^[k₂] σ₀ := Prod.mk.eta
    exact P.walk_inj_of_lt_period h₀ hk₁.1 hk₂.1 htri
  set M := F.image φ with hM
  have hMcard : M.card = F.card := Finset.card_image_of_injOn hinj
  have hMT : M ⊆ T := by
    intro x hx
    simp only [hM, Finset.mem_image] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    exact hmaps hk
  -- the mirror involution on the turns at `v`
  set m : P.V × Bool → P.V × Bool := fun x ↦ (P.turn v x.1 x.2, !x.2) with hm
  have mfst : ∀ x, (m x).1 = P.turn v x.1 x.2 := fun _ ↦ rfl
  have msnd : ∀ x, (m x).2 = !x.2 := fun _ ↦ rfl
  have hm_inj : Set.InjOn m T := by
    intro x₁ hx₁ x₂ hx₂ h
    simp only [hT, Finset.mem_coe, Finset.mem_product, Finset.mem_filter] at hx₁ hx₂
    obtain ⟨a₁, b₁⟩ := x₁
    obtain ⟨a₂, b₂⟩ := x₂
    have hb : b₁ = b₂ := by
      have h2' := congrArg Prod.snd h
      have h2'' : (!b₁) = (!b₂) := h2'
      cases b₁ <;> cases b₂ <;> simp_all
    have ha : a₁ = a₂ := by
      have h' := congrArg Prod.fst h
      rw [mfst, mfst, ← hb] at h'
      exact P.turn_inj hx₁.1.2 hx₂.1.2 b₁ h'
    exact Prod.ext ha hb
  have hmM_T : M.image m ⊆ T := by
    intro x hx
    simp only [Finset.mem_image] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hyT := hMT hy
    simp only [hT, Finset.mem_product, Finset.mem_filter] at hyT ⊢
    exact ⟨⟨Finset.mem_univ _, P.turn_adj hyT.1.2 y.2⟩, Finset.mem_univ _⟩
  have hdisj : Disjoint M (M.image m) := by
    rw [Finset.disjoint_left]
    intro x hxM hxmM
    simp only [hM, Finset.mem_image] at hxM hxmM
    obtain ⟨k₁, hk₁, hkx1⟩ := hxM
    obtain ⟨y, hyM, hmyx⟩ := hxmM
    obtain ⟨k₂, hk₂, hky⟩ := hyM
    rw [← hky, ← hkx1] at hmyx
    -- hmyx : m (φ k₂) = φ k₁
    simp only [hF, Finset.mem_filter, Finset.mem_range] at hk₁ hk₂
    have hpa : (P.step^[k₁] σ₀).2.2 = !(P.step^[k₂] σ₀).2.2 := by
      have h' := congrArg Prod.snd hmyx
      rw [msnd, φsnd, φsnd] at h'
      exact h'.symm
    have ha : P.turn v (P.step^[k₂] σ₀).1 (P.step^[k₂] σ₀).2.2 = (P.step^[k₁] σ₀).1 := by
      have h' := congrArg Prod.fst hmyx
      rw [mfst, φfst, φsnd, φfst] at h'
      exact h'
    have hadj2 : P.G.Adj v (P.step^[k₂] σ₀).1 := by
      have hv := P.valid_walk h₀ k₂
      simp only [Park.Valid] at hv
      rw [hk₂.2] at hv
      exact hv
    have htp : P.turn v (P.step^[k₁] σ₀).1 (P.step^[k₁] σ₀).2.2 = (P.step^[k₂] σ₀).1 := by
      rw [← ha, hpa]
      exact P.turn_inv_turn hadj2 _
    have htri1 : P.step^[k₁] σ₀ = ((P.step^[k₁] σ₀).1, (v, (P.step^[k₁] σ₀).2.2)) := by
      calc P.step^[k₁] σ₀
          = ((P.step^[k₁] σ₀).1, ((P.step^[k₁] σ₀).2.1, (P.step^[k₁] σ₀).2.2)) :=
            (Prod.mk.eta).symm
        _ = ((P.step^[k₁] σ₀).1, (v, (P.step^[k₁] σ₀).2.2)) := by rw [hk₁.2]
    have htri2 : P.step^[k₂] σ₀ = ((P.step^[k₂] σ₀).1, (v, (P.step^[k₂] σ₀).2.2)) := by
      calc P.step^[k₂] σ₀
          = ((P.step^[k₂] σ₀).1, ((P.step^[k₂] σ₀).2.1, (P.step^[k₂] σ₀).2.2)) :=
            (Prod.mk.eta).symm
        _ = ((P.step^[k₂] σ₀).1, (v, (P.step^[k₂] σ₀).2.2)) := by rw [hk₂.2]
    have hne : k₁ ≠ k₂ := by
      intro hkk
      rw [hkk] at hpa
      rcases Bool.eq_false_or_eq_true (P.step^[k₂] σ₀).2.2 with hbb | hbb <;>
        exact absurd hpa (by rw [hbb]; decide)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact P.no_mirror h₀ (k₂ - k₁) k₁ _ v _ _ _ (by lia) htri1
        (by rw [show k₁ + (k₂ - k₁) = k₂ by lia]; exact htri2) htp ha
    · have hk1lt : k₁ < P.period h₀ := hk₁.1
      have hwrap : P.step^[k₁ + (P.period h₀ - k₁ + k₂)] σ₀ = P.step^[k₂] σ₀ := by
        have h1 : k₁ + (P.period h₀ - k₁ + k₂) = k₂ + P.period h₀ := by lia
        rw [h1, Function.iterate_add_apply, P.period_eq h₀]
      exact P.no_mirror h₀ (P.period h₀ - k₁ + k₂) k₁ _ v _ _ _ (by lia) htri1
        (by rw [hwrap]; exact htri2) htp ha
  have hmMcard : (M.image m).card = M.card :=
    Finset.card_image_of_injOn (Set.InjOn.mono (fun x hx ↦ hMT hx) hm_inj)
  have h2M : 2 * M.card ≤ 6 := by
    have hunion : (M ∪ M.image m).card = M.card + (M.image m).card :=
      Finset.card_union_of_disjoint hdisj
    have hsub : M ∪ M.image m ⊆ T := Finset.union_subset hMT hmM_T
    have hle := Finset.card_le_card hsub
    lia
  have hFM : F.card ≤ 3 := by lia
  exact hFM

/-- The visitor enters any junction at most three times during her walk. -/
theorem entries_le_three {σ₀ : P.V × P.V × Bool} (h₀ : P.Valid σ₀) (v : P.V) :
    P.entries σ₀ h₀ v ≤ 3 := by
  unfold Park.entries
  by_cases hv : v = σ₀.1
  · rw [ite_eq_left hv]
    have hempty : ((Finset.range (P.retTime h₀)).filter
        fun k ↦ (P.step^[k] σ₀).2.1 = v) = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro k hk
      rw [Finset.mem_filter, Finset.mem_range] at hk
      rcases eq_or_ne k 0 with rfl | hk0
      · rw [hv] at hk
        exact h₀.ne hk.2
      · exact P.retTime_min h₀ (Nat.pos_of_ne_zero hk0) hk.1 (hk.2.trans hv)
    rw [hempty, Finset.card_empty]
    lia
  · rw [ite_eq_right hv]
    have hle : P.retTime h₀ ≤ P.period h₀ :=
      le_trans (P.retTime_le_period_sub_one h₀) (Nat.sub_le _ _)
    exact le_trans
      (Finset.card_le_card
        (Finset.filter_subset_filter _ (Finset.range_subset_range.mpr hle)))
      (P.arrivals_le_three h₀ v)

/-- The example of Danielle Wang from the official solution: a park with ten
junctions `A, B, ..., J` (numbered `0` through `9`) in which the visitor enters
junction `A = 0` three times. (This rotation system is planar — it has seven
faces, so `10 - 15 + 7 = 2` — hence it really comes from a planar layout, though
the formal statement does not require this.) -/
def wangEdges : List (Fin 10 × Fin 10) :=
  [(2, 0), (0, 7), (7, 8), (8, 5), (5, 6), (6, 3), (3, 1), (1, 0),
   (7, 4), (4, 5), (6, 9), (9, 1), (2, 3), (2, 4), (8, 9)]

def wangAdj (a b : Fin 10) : Prop := (a, b) ∈ wangEdges ∨ (b, a) ∈ wangEdges

instance (a b : Fin 10) : Decidable (wangAdj a b) :=
  inferInstanceAs (Decidable ((a, b) ∈ wangEdges ∨ (b, a) ∈ wangEdges))

def wangG : SimpleGraph (Fin 10) where
  Adj := wangAdj
  symm := ⟨fun a b h ↦ by
    simp only [wangAdj] at h ⊢
    exact h.elim Or.inr Or.inl⟩
  loopless := ⟨by decide⟩

instance : DecidableRel wangG.Adj :=
  fun a b ↦ inferInstanceAs (Decidable ((a, b) ∈ wangEdges ∨ (b, a) ∈ wangEdges))

/-- The cyclic order of the trails at each junction of `wangPark`. -/
def wangRotN : ℕ → ℕ → ℕ
  | 0, 1 => 2 | 0, 2 => 7 | 0, 7 => 1
  | 1, 0 => 9 | 1, 3 => 0 | 1, 9 => 3
  | 2, 0 => 3 | 2, 3 => 4 | 2, 4 => 0
  | 3, 1 => 6 | 3, 2 => 1 | 3, 6 => 2
  | 4, 2 => 5 | 4, 5 => 7 | 4, 7 => 2
  | 5, 4 => 6 | 5, 6 => 8 | 5, 8 => 4
  | 6, 3 => 9 | 6, 5 => 3 | 6, 9 => 5
  | 7, 0 => 4 | 7, 4 => 8 | 7, 8 => 0
  | 8, 5 => 9 | 8, 7 => 5 | 8, 9 => 7
  | 9, 1 => 8 | 9, 6 => 1 | 9, 8 => 6
  | _, _ => 0

def wangRot (a b : Fin 10) : Fin 10 :=
  ⟨wangRotN a.val b.val % 10, Nat.mod_lt _ (by lia)⟩

def wangPark : Park where
  V := Fin 10
  fintypeV := inferInstance
  decidableEqV := inferInstance
  G := wangG
  decidableAdj := inferInstance
  cubic := by decide
  rot := wangRot
  rot_adj := by decide
  rot_ne := by decide
  rot_inv := by decide

lemma wang_valid : wangPark.Valid ((2, 0, true) : Fin 10 × Fin 10 × Bool) := by
  show wangAdj 0 2
  decide

/-- Starting from junction `C = 2` along the trail to `A = 0`, the visitor's walk
is `C A H I F G D B A H E F G J B A C`: she gets back to `C` after 16 trails,
having entered junction `A` three times. -/
theorem wang_entries :
    wangPark.entries ((2, 0, true) : Fin 10 × Fin 10 × Bool) wang_valid (0 : Fin 10) = 3 := by
  have hT : wangPark.retTime (σ₀ := ((2, 0, true) : Fin 10 × Fin 10 × Bool)) wang_valid = 15 :=
    (Nat.find_eq_iff _).mpr ⟨by decide, by decide⟩
  simp only [Park.entries, hT]
  decide

end Park

snip end

/-- The set of all possible numbers of times the visitor could have entered a
junction during her walk, over all parks and all choices of starting junction
and first trail. -/
def numberOfEntries : Set ℕ :=
  { n | ∃ (P : Park) (σ₀ : P.V × P.V × Bool) (h₀ : P.Valid σ₀) (v : P.V),
      P.entries σ₀ h₀ v = n }

determine solution : ℕ := 3

problem usa2021_p2 : IsGreatest numberOfEntries solution := by
  refine ⟨?_, ?_⟩
  · exact ⟨Park.wangPark, ((2, 0, true) : Fin 10 × Fin 10 × Bool), Park.wang_valid,
      (0 : Fin 10), Park.wang_entries⟩
  · intro n hn
    obtain ⟨P, σ₀, h₀, v, rfl⟩ := hn
    exact P.entries_le_three h₀ v

end Usa2021P2
