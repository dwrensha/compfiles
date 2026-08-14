/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Group.Nat.Range
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Tactic.IntervalCases
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics] }

/-!
# USA Mathematical Olympiad 2013, Problem 3

Let n be a positive integer. There are n(n+1)/2 tokens, each with a black
side and a white side, arranged into an equilateral triangle, with the
biggest row containing n tokens. Initially, each token has the white side
up. An operation is to choose a line parallel to the sides of the triangle,
and flip all the tokens on that line. A configuration is called admissible
if it can be obtained from the initial configuration by performing a finite
number of operations. For each admissible configuration C, let f(C) denote
the smallest number of operations required to obtain C from the initial
configuration. Find the maximum value of f(C), where C varies over all
admissible configurations.
-/

namespace Usa2013P3

/-! ### Basic definitions -/

/-- The tokens are indexed by pairs `(a, b)` of natural numbers with
`a + b < n`. One should think of barycentric coordinates `(a, b, c)` with
`a + b + c = n - 1`, so that `c = n - 1 - a - b` is determined. -/
def Token (n : ℕ) := { p : ℕ × ℕ // p.1 + p.2 < n }

lemma lt_left {n a b : ℕ} (h : a + b < n) : a < n := by omega
lemma lt_right {n a b : ℕ} (h : a + b < n) : b < n := by omega
lemma lt_third {n a b : ℕ} (h : a + b < n) : n - 1 - a - b < n := by omega

/-- A choice of lines to flip: for each of the three directions and each
`i < n`, whether the `i`-th line in that direction is flipped. The three
lines through the token `(a, b, c)` are the `a`-th, `b`-th and `c`-th lines
of the three directions respectively. -/
@[ext]
structure Moves (n : ℕ) where
  x : Fin n → Bool
  y : Fin n → Bool
  z : Fin n → Bool

/-- The configuration reached from the initial (all-white) configuration by
performing the moves `v`: token `(a, b)` ends up black iff an odd number of
the three lines through it were flipped. -/
def applyMoves {n : ℕ} (v : Moves n) (t : Token n) : Bool :=
  v.x ⟨t.1.1, lt_left t.2⟩ ^^
  v.y ⟨t.1.2, lt_right t.2⟩ ^^
  v.z ⟨n - 1 - t.1.1 - t.1.2, lt_third t.2⟩

/-- A configuration is admissible if it can be obtained from the initial
configuration by a finite number of operations. Since the operations commute
and are involutions, every sequence of operations is described by a `Moves`. -/
def Admissible {n : ℕ} (C : Token n → Bool) : Prop := ∃ v : Moves n, applyMoves v = C

/-- The number of operations in a `Moves`: the total number of flipped lines. -/
def weight {n : ℕ} (v : Moves n) : ℕ :=
  (Finset.univ.filter fun i => v.x i = true).card +
  (Finset.univ.filter fun i => v.y i = true).card +
  (Finset.univ.filter fun i => v.z i = true).card

/-- `f C` is the smallest number of operations required to obtain `C`. -/
noncomputable def f {n : ℕ} (C : Token n → Bool) : ℕ :=
  sInf {m : ℕ | ∃ v : Moves n, applyMoves v = C ∧ weight v = m}

determine answer (n : ℕ) : ℕ := 6 * (n / 4) + n % 4

snip begin

/-- Pointwise xor of two `Moves`. -/
def Moves.vxor {n : ℕ} (v w : Moves n) : Moves n :=
  ⟨fun i => v.x i ^^ w.x i, fun i => v.y i ^^ w.y i, fun i => v.z i ^^ w.z i⟩

/-- The "even-length line" indicator: the `i`-th line of any direction
contains `n - i` tokens, which is even iff `i ≡ n (mod 2)`. -/
def e (n : ℕ) : Fin n → Bool := fun i => decide (i.val % 2 = n % 2)

/-- The element of the move-span indexed by three bits. With
`g₁ = (1,1,0)`, `g₂ = (0,1,1)` and `θ = (e,e,e)`, this is
`ε₁ • g₁ ^^ ε₂ • g₂ ^^ ε₃ • θ`. -/
def sp (n : ℕ) (ε : Bool × Bool × Bool) : Moves n :=
  ⟨fun i => ε.1 ^^ (ε.2.2 && e n i),
   fun i => (ε.1 ^^ ε.2.1) ^^ (ε.2.2 && e n i),
   fun i => ε.2.1 ^^ (ε.2.2 && e n i)⟩

lemma xor_eq_false_iff {a b : Bool} : ((a ^^ b) = false) ↔ a = b := by
  cases a <;> cases b <;> simp

lemma applyMoves_vxor {n : ℕ} (v w : Moves n) (t : Token n) :
    applyMoves (Moves.vxor v w) t = (applyMoves v t ^^ applyMoves w t) := by
  obtain ⟨⟨a, b⟩, h⟩ := t
  dsimp only [applyMoves, Moves.vxor]
  have id : ∀ a1 b1 c1 a2 b2 c2 : Bool,
      ((a1 ^^ a2) ^^ (b1 ^^ b2) ^^ (c1 ^^ c2)) =
        ((a1 ^^ b1 ^^ c1) ^^ (a2 ^^ b2 ^^ c2)) := by
    decide
  exact id _ _ _ _ _ _

/-- The key property of `θ = (e,e,e)`: every token lies on an even number of
even-length lines. Indeed, with `c = n - 1 - a - b` we have
`a + b + c = n - 1`, so among `a % 2`, `b % 2`, `c % 2` the number of values
equal to `n % 2` is even. -/
lemma theta_aux (n a b : ℕ) (h : a + b < n) :
    (decide (a % 2 = n % 2) ^^ decide (b % 2 = n % 2) ^^
      decide ((n - 1 - a - b) % 2 = n % 2)) = false := by
  have key : (a % 2 + b % 2 + (n - 1 - a - b) % 2) % 2 = (n % 2 + 1) % 2 := by
    omega
  have ha : a % 2 < 2 := by omega
  have hb : b % 2 < 2 := by omega
  have hz : (n - 1 - a - b) % 2 < 2 := by omega
  have hn : n % 2 < 2 := by omega
  interval_cases (a % 2) <;> interval_cases (b % 2) <;>
    interval_cases ((n - 1 - a - b) % 2) <;> interval_cases (n % 2) <;>
    first
    | decide
    | (exfalso; norm_num at key)

/-- Every element of the span acts trivially on configurations. -/
lemma applyMoves_sp {n : ℕ} (ε : Bool × Bool × Bool) (t : Token n) :
    applyMoves (sp n ε) t = false := by
  obtain ⟨ε1, ε2, ε3⟩ := ε
  obtain ⟨⟨a, b⟩, h⟩ := t
  have th := theta_aux n a b h
  dsimp only [applyMoves, sp, e]
  generalize h1 : decide (a % 2 = n % 2) = d1
  generalize h2 : decide (b % 2 = n % 2) = d2
  generalize h3 : decide ((n - 1 - a - b) % 2 = n % 2) = d3
  rw [h1, h2, h3] at th
  cases ε1 <;> cases ε2 <;> cases ε3 <;> cases d1 <;> cases d2 <;> cases d3 <;>
    simp_all

/-- The span elements are closed under xor, componentwise on the bits. -/
lemma sp_vxor {n : ℕ} (ε ε' : Bool × Bool × Bool) :
    Moves.vxor (sp n ε) (sp n ε') =
      sp n (ε.1 ^^ ε'.1, ε.2.1 ^^ ε'.2.1, ε.2.2 ^^ ε'.2.2) := by
  obtain ⟨ε1, ε2, ε3⟩ := ε
  obtain ⟨ε1', ε2', ε3'⟩ := ε'
  apply Moves.ext
  · funext i
    dsimp only [Moves.vxor, sp]
    have id : ∀ p q r s d : Bool,
        ((p ^^ (r && d)) ^^ (q ^^ (s && d))) = ((p ^^ q) ^^ ((r ^^ s) && d)) := by
      decide
    exact id _ _ _ _ _
  · funext i
    dsimp only [Moves.vxor, sp]
    have id : ∀ p1 p2 q1 q2 r s d : Bool,
        (((p1 ^^ p2) ^^ (r && d)) ^^ ((q1 ^^ q2) ^^ (s && d))) =
          (((p1 ^^ q1) ^^ (p2 ^^ q2)) ^^ ((r ^^ s) && d)) := by
      decide
    exact id _ _ _ _ _ _ _
  · funext i
    dsimp only [Moves.vxor, sp]
    have id : ∀ p q r s d : Bool,
        ((p ^^ (r && d)) ^^ (q ^^ (s && d))) = ((p ^^ q) ^^ ((r ^^ s) && d)) := by
      decide
    exact id _ _ _ _ _

/-- The zero move. -/
def zeroMove (n : ℕ) : Moves n := ⟨fun _ => false, fun _ => false, fun _ => false⟩

lemma vxor_self {n : ℕ} (v : Moves n) : Moves.vxor v v = zeroMove n := by
  apply Moves.ext <;> funext i <;> simp [Moves.vxor, zeroMove]

lemma vxor_zero {n : ℕ} (v : Moves n) : Moves.vxor v (zeroMove n) = v := by
  apply Moves.ext <;> funext i <;> simp [Moves.vxor, zeroMove]

lemma vxor_comm {n : ℕ} (v w : Moves n) : Moves.vxor v w = Moves.vxor w v := by
  apply Moves.ext
  · funext i; dsimp only [Moves.vxor]; exact Bool.xor_comm _ _
  · funext i; dsimp only [Moves.vxor]; exact Bool.xor_comm _ _
  · funext i; dsimp only [Moves.vxor]; exact Bool.xor_comm _ _

lemma vxor_assoc {n : ℕ} (u v w : Moves n) :
    Moves.vxor (Moves.vxor u v) w = Moves.vxor u (Moves.vxor v w) := by
  apply Moves.ext
  · funext i; dsimp only [Moves.vxor]; exact Bool.xor_assoc _ _ _
  · funext i; dsimp only [Moves.vxor]; exact Bool.xor_assoc _ _ _
  · funext i; dsimp only [Moves.vxor]; exact Bool.xor_assoc _ _ _

lemma vxor_eq_zero {n : ℕ} {v w : Moves n} (h : Moves.vxor v w = zeroMove n) :
    v = w := by
  apply Moves.ext
  · funext i
    have hx : (v.x i ^^ w.x i) = false := congrFun (congrArg Moves.x h) i
    exact (xor_eq_false_iff).1 hx
  · funext i
    have hy : (v.y i ^^ w.y i) = false := congrFun (congrArg Moves.y h) i
    exact (xor_eq_false_iff).1 hy
  · funext i
    have hz : (v.z i ^^ w.z i) = false := congrFun (congrArg Moves.z h) i
    exact (xor_eq_false_iff).1 hz

/- Counting lemmas for periodic predicates (used to evaluate the weights of
the extremal configuration). -/
namespace Count

private lemma period_shift (q : ℕ → Bool) (hq : ∀ i, q (i + 4) = q i) (i k : ℕ) :
    q (i + 4 * k) = q i := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_add, mul_one, ← add_assoc, hq (i + 4 * k), ih]

private lemma card_filter_range_four_mul (q : ℕ → Bool) (hq : ∀ i, q (i + 4) = q i) (k : ℕ) :
    ((Finset.range (4 * k)).filter fun i => q i = true).card =
      k * ((Finset.range 4).filter fun i => q i = true).card := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hdisj : Disjoint ((Finset.range (4 * k)).filter fun i => q i = true)
        (((Finset.range 4).map (addLeftEmbedding (4 * k))).filter fun i => q i = true) := by
      rw [Finset.disjoint_left]
      intro a ha hb
      have ha' : a < 4 * k := Finset.mem_range.1 (Finset.mem_filter.1 ha).1
      obtain ⟨i, -, hia⟩ := Finset.mem_map.1 (Finset.mem_filter.1 hb).1
      rw [addLeftEmbedding_apply] at hia
      omega
    have hmap :
        (((Finset.range 4).map (addLeftEmbedding (4 * k))).filter fun i => q i = true).card =
          ((Finset.range 4).filter fun i => q i = true).card := by
      rw [Finset.filter_map, Finset.card_map]
      congr 1
      apply Finset.filter_congr
      intro i _
      simp only [Function.comp_apply, addLeftEmbedding_apply, Nat.add_comm (4 * k) i,
        period_shift q hq i k]
    rw [mul_add, mul_one, Finset.range_add, Finset.filter_union,
      Finset.card_union_of_disjoint hdisj, ih, hmap, Nat.succ_mul]

/-- Count of a periodic (period 4) predicate over `Finset.range (4 * k + r)`. -/
lemma card_filter_range_periodic (q : ℕ → Bool) (hq : ∀ i, q (i + 4) = q i) (k r : ℕ) :
    ((Finset.range (4 * k + r)).filter fun i => q i = true).card =
      k * ((Finset.range 4).filter fun i => q i = true).card +
        ((Finset.range r).filter fun i => q i = true).card := by
  have hdisj : Disjoint ((Finset.range (4 * k)).filter fun i => q i = true)
      (((Finset.range r).map (addLeftEmbedding (4 * k))).filter fun i => q i = true) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    have ha' : a < 4 * k := Finset.mem_range.1 (Finset.mem_filter.1 ha).1
    obtain ⟨i, -, hia⟩ := Finset.mem_map.1 (Finset.mem_filter.1 hb).1
    rw [addLeftEmbedding_apply] at hia
    omega
  have hmap : (((Finset.range r).map (addLeftEmbedding (4 * k))).filter fun i => q i = true).card =
      ((Finset.range r).filter fun i => q i = true).card := by
    rw [Finset.filter_map, Finset.card_map]
    congr 1
    apply Finset.filter_congr
    intro i _
    simp only [Function.comp_apply, addLeftEmbedding_apply, Nat.add_comm (4 * k) i,
      period_shift q hq i k]
  rw [Finset.range_add, Finset.filter_union, Finset.card_union_of_disjoint hdisj,
    card_filter_range_four_mul q hq k, hmap]

/-- Bridge: counting a `ℕ`-predicate on `Fin n` vs on `Finset.range n`. -/
lemma card_fin_filter (q : ℕ → Bool) (n : ℕ) :
    (Finset.univ.filter fun i : Fin n => q i.val = true).card =
      ((Finset.range n).filter fun i => q i = true).card := by
  rw [Finset.card_filter, Finset.card_filter]
  exact Fin.sum_univ_eq_sum_range (fun i => if q i = true then 1 else 0) n

/-- Combined: count of a 4-periodic predicate over `Fin (4 * k + r)`. -/
lemma count_eval (P : ℕ → Bool) (hP : ∀ i, P (i + 4) = P i) {n k r : ℕ} (hn : n = 4 * k + r) :
    (Finset.univ.filter fun i : Fin n => P i.val = true).card =
      k * ((Finset.range 4).filter fun i => P i = true).card +
        ((Finset.range r).filter fun i => P i = true).card := by
  rw [card_fin_filter P n, hn]
  exact card_filter_range_periodic P hP k r

/-- Number of `i < n` with `i % 2 = n % 2`. -/
lemma card_range_modeq (n : ℕ) :
    ((Finset.range n).filter fun i => i % 2 = n % 2).card = n / 2 := by
  induction n using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more n ih0 _ =>
    have hnin : n ∉ (Finset.range n).filter fun i => i % 2 = n % 2 :=
      fun h => Finset.notMem_range_self (Finset.mem_filter.1 h).1
    rw [Nat.add_mod_right, Finset.range_add_one, Finset.range_add_one,
      Finset.filter_insert, Finset.filter_insert, ite_eq_right (by lia), ite_eq_left rfl,
      Finset.card_insert_of_notMem hnin, ih0, Nat.add_div_right n (Nat.zero_lt_succ _)]

end Count

/-- The contribution of one direction to the weight of `v ^^ sp ε`: the number
of flipped lines of that direction, as a function of the "full flip" bit `δ`
and the "theta flip" bit `τ`. -/
def bv {n : ℕ} (α : Fin n → Bool) (δ τ : Bool) : ℕ :=
  (Finset.univ.filter fun i => (α i ^^ δ ^^ (τ && e n i)) = true).card

/-- Number of ones of `α` on odd-length lines. -/
def pon {n : ℕ} (α : Fin n → Bool) : ℕ :=
  (Finset.univ.filter fun i => (α i = true) ∧ (e n i = false)).card

/-- Number of ones of `α` on even-length lines. -/
def qon {n : ℕ} (α : Fin n → Bool) : ℕ :=
  (Finset.univ.filter fun i => (α i = true) ∧ (e n i = true)).card

/-- Number of odd-length lines in one direction. -/
def Ocard (n : ℕ) : ℕ := (Finset.univ.filter fun i => e n i = false).card

/-- Number of even-length lines in one direction. -/
def Ecard (n : ℕ) : ℕ := (Finset.univ.filter fun i => e n i = true).card

lemma Ecard_eq (n : ℕ) : Ecard n = n / 2 := by
  have h1 : (Finset.univ.filter fun i : Fin n => decide (i.val % 2 = n % 2) = true).card =
      ((Finset.range n).filter fun i => decide (i % 2 = n % 2) = true).card :=
    Count.card_fin_filter (fun i => decide (i % 2 = n % 2)) n
  have h2 : (Finset.univ.filter fun i : Fin n => e n i = true).card =
      (Finset.univ.filter fun i : Fin n => decide (i.val % 2 = n % 2) = true).card :=
    congrArg Finset.card (Finset.filter_congr (fun i _ => by simp [e]))
  rw [Ecard, h2, h1]
  rw [show ((Finset.range n).filter fun i => decide (i % 2 = n % 2) = true) =
      ((Finset.range n).filter fun i => i % 2 = n % 2) from
    Finset.filter_congr (fun i _ => by simp)]
  exact Count.card_range_modeq n

lemma OE_sum (n : ℕ) : Ocard n + Ecard n = n := by
  rw [Ocard, Ecard]
  rw [show (Finset.univ.filter fun i : Fin n => e n i = false) =
      (Finset.univ.filter fun i : Fin n => ¬ (e n i = true)) from
    Finset.filter_congr (fun i _ => by cases (e n i) <;> simp)]
  rw [Nat.add_comm, Finset.card_filter_add_card_filter_not, Finset.card_univ, Fintype.card_fin]

lemma pon_le {n : ℕ} (α : Fin n → Bool) : pon α ≤ Ocard n := by
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter] at hi ⊢
  exact ⟨Finset.mem_univ i, hi.2.2⟩

lemma qon_le {n : ℕ} (α : Fin n → Bool) : qon α ≤ Ecard n := by
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter] at hi ⊢
  exact ⟨Finset.mem_univ i, hi.2.2⟩

/-- Counting ones of `α ^^ c` on the even-length lines. -/
lemma card_e_true {n : ℕ} (α : Fin n → Bool) (c : Bool) :
    ((Finset.univ.filter fun i => e n i = true).filter fun i => (α i ^^ c) = true).card =
      cond c (Ecard n - qon α) (qon α) := by
  cases c
  · simp only [Bool.cond_false]
    rw [show (Finset.univ.filter fun i => e n i = true).filter (fun i => (α i ^^ false) = true) =
        (Finset.univ.filter fun i => e n i = true).filter (fun i => α i = true) from
      Finset.filter_congr (fun i _ => by simp)]
    rw [Finset.filter_filter]
    rw [show (Finset.univ.filter fun i => (e n i = true) ∧ (α i = true)) =
        (Finset.univ.filter fun i => (α i = true) ∧ (e n i = true)) from
      Finset.filter_congr (fun i _ => and_comm)]
    rfl
  · simp only [Bool.cond_true]
    rw [show (Finset.univ.filter fun i => e n i = true).filter (fun i => (α i ^^ true) = true) =
        (Finset.univ.filter fun i => e n i = true).filter (fun i => α i = false) from
      Finset.filter_congr (fun i _ => by cases (α i) <;> simp)]
    rw [Finset.filter_filter]
    have h2 := Finset.card_filter_add_card_filter_not
      (s := Finset.univ.filter fun i : Fin n => e n i = true) (p := fun i => α i = true)
    rw [Finset.filter_filter, Finset.filter_filter] at h2
    rw [show (Finset.univ.filter fun i => (e n i = true) ∧ (α i = true)) =
        (Finset.univ.filter fun i => (α i = true) ∧ (e n i = true)) from
      Finset.filter_congr (fun i _ => and_comm)] at h2
    rw [show (Finset.univ.filter fun i => (e n i = true) ∧ ¬(α i = true)) =
        (Finset.univ.filter fun i => (e n i = true) ∧ (α i = false)) from
      Finset.filter_congr (fun i _ => by cases (α i) <;> simp)] at h2
    have hQ : (Finset.univ.filter fun i => (α i = true) ∧ (e n i = true)).card = qon α := rfl
    have hE : (Finset.univ.filter fun i => e n i = true).card = Ecard n := rfl
    omega

/-- Counting ones of `α ^^ c` on the odd-length lines. -/
lemma card_e_false {n : ℕ} (α : Fin n → Bool) (c : Bool) :
    ((Finset.univ.filter fun i => e n i = false).filter fun i => (α i ^^ c) = true).card =
      cond c (Ocard n - pon α) (pon α) := by
  cases c
  · simp only [Bool.cond_false]
    rw [show (Finset.univ.filter fun i => e n i = false).filter (fun i => (α i ^^ false) = true) =
        (Finset.univ.filter fun i => e n i = false).filter (fun i => α i = true) from
      Finset.filter_congr (fun i _ => by simp)]
    rw [Finset.filter_filter]
    rw [show (Finset.univ.filter fun i => (e n i = false) ∧ (α i = true)) =
        (Finset.univ.filter fun i => (α i = true) ∧ (e n i = false)) from
      Finset.filter_congr (fun i _ => and_comm)]
    rfl
  · simp only [Bool.cond_true]
    rw [show (Finset.univ.filter fun i => e n i = false).filter (fun i => (α i ^^ true) = true) =
        (Finset.univ.filter fun i => e n i = false).filter (fun i => α i = false) from
      Finset.filter_congr (fun i _ => by cases (α i) <;> simp)]
    rw [Finset.filter_filter]
    have h2 := Finset.card_filter_add_card_filter_not
      (s := Finset.univ.filter fun i : Fin n => e n i = false) (p := fun i => α i = true)
    rw [Finset.filter_filter, Finset.filter_filter] at h2
    rw [show (Finset.univ.filter fun i => (e n i = false) ∧ (α i = true)) =
        (Finset.univ.filter fun i => (α i = true) ∧ (e n i = false)) from
      Finset.filter_congr (fun i _ => and_comm)] at h2
    rw [show (Finset.univ.filter fun i => (e n i = false) ∧ ¬(α i = true)) =
        (Finset.univ.filter fun i => (e n i = false) ∧ (α i = false)) from
      Finset.filter_congr (fun i _ => by cases (α i) <;> simp)] at h2
    have hP : (Finset.univ.filter fun i => (α i = true) ∧ (e n i = false)).card = pon α := rfl
    have hO : (Finset.univ.filter fun i => e n i = false).card = Ocard n := rfl
    omega

/-- Master formula for the block values. -/
lemma bv_eq {n : ℕ} (α : Fin n → Bool) (δ τ : Bool) :
    bv α δ τ = cond (δ ^^ τ) (Ecard n - qon α) (qon α) +
      cond δ (Ocard n - pon α) (pon α) := by
  have split : (Finset.univ.filter fun i => (α i ^^ δ ^^ (τ && e n i)) = true) =
      (Finset.univ.filter fun i => (e n i = true) ∧ ((α i ^^ δ ^^ τ) = true)) ∪
      (Finset.univ.filter fun i => (e n i = false) ∧ ((α i ^^ δ) = true)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and]
    constructor
    · intro h
      cases he : e n i
      · refine Or.inr ⟨rfl, ?_⟩
        rw [he] at h
        simpa [Bool.and_false, Bool.xor_false] using h
      · refine Or.inl ⟨rfl, ?_⟩
        rw [he] at h
        simpa [Bool.and_true] using h
    · intro h
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1]
        simpa using h2
      · rw [h1]
        simpa using h2
  rw [bv, split]
  have hdisj : Disjoint (Finset.univ.filter fun i => (e n i = true) ∧ ((α i ^^ δ ^^ τ) = true))
      (Finset.univ.filter fun i => (e n i = false) ∧ ((α i ^^ δ) = true)) := by
    rw [Finset.disjoint_left]
    intro i hi1 hi2
    simp only [Finset.mem_filter] at hi1 hi2
    rw [hi1.2.1] at hi2
    simp at hi2
  rw [Finset.card_union_of_disjoint hdisj]
  have e1 : (Finset.univ.filter fun i => (e n i = true) ∧ ((α i ^^ δ ^^ τ) = true)) =
      (Finset.univ.filter fun i => e n i = true).filter fun i => (α i ^^ (δ ^^ τ)) = true := by
    rw [Finset.filter_filter]
    apply Finset.filter_congr
    intro i _
    simp
  have e2 : (Finset.univ.filter fun i => (e n i = false) ∧ ((α i ^^ δ) = true)) =
      (Finset.univ.filter fun i => e n i = false).filter fun i => (α i ^^ δ) = true := by
    rw [Finset.filter_filter]
  rw [e1, e2, card_e_true, card_e_false]

/-- The four block values. -/
lemma bv_ff {n : ℕ} (α : Fin n → Bool) : bv α false false = pon α + qon α := by
  rw [bv_eq]
  simp
  omega

lemma bv_tf {n : ℕ} (α : Fin n → Bool) :
    bv α true false = (Ocard n - pon α) + (Ecard n - qon α) := by
  rw [bv_eq]
  simp
  omega

lemma bv_ft {n : ℕ} (α : Fin n → Bool) :
    bv α false true = pon α + (Ecard n - qon α) := by
  rw [bv_eq]
  simp
  omega

lemma bv_tt {n : ℕ} (α : Fin n → Bool) :
    bv α true true = (Ocard n - pon α) + qon α := by
  rw [bv_eq]
  simp
  omega

/-- Pair identity: the two values obtained by flipping a whole direction
sum to `n`. -/
lemma pair_id {n : ℕ} (α : Fin n → Bool) (τ : Bool) :
    bv α false τ + bv α true τ = n := by
  rw [bv_eq, bv_eq]
  have hp := pon_le α
  have hq := qon_le α
  have hO := OE_sum n
  cases τ <;> simp <;> omega
/-- The weight of a coset element splits into the three block values. -/
lemma weight_vxor_sp {n : ℕ} (v : Moves n) (ε1 ε2 ε3 : Bool) :
    weight (Moves.vxor v (sp n (ε1, ε2, ε3))) =
      bv v.x ε1 ε3 + bv v.y (ε1 ^^ ε2) ε3 + bv v.z ε2 ε3 := by
  simp only [weight, bv, Moves.vxor, sp, Bool.xor_assoc]

/-- The weights of the eight coset elements sum to `12n`. -/
lemma sum_weights {n : ℕ} (v : Moves n) :
    weight (Moves.vxor v (sp n (false, false, false))) +
    weight (Moves.vxor v (sp n (false, false, true))) +
    weight (Moves.vxor v (sp n (false, true, false))) +
    weight (Moves.vxor v (sp n (false, true, true))) +
    weight (Moves.vxor v (sp n (true, false, false))) +
    weight (Moves.vxor v (sp n (true, false, true))) +
    weight (Moves.vxor v (sp n (true, true, false))) +
    weight (Moves.vxor v (sp n (true, true, true))) = 12 * n := by
  simp only [weight_vxor_sp]
  have pxf := pair_id v.x false
  have pxt := pair_id v.x true
  have pyf := pair_id v.y false
  have pyt := pair_id v.y true
  have pzf := pair_id v.z false
  have pzt := pair_id v.z true
  simp only [Bool.xor_false, Bool.xor_true, Bool.not_true, Bool.not_false]
  omega
lemma pair_weight {n : ℕ} (v : Moves n) (ε1 τ : Bool) :
    weight (Moves.vxor v (sp n (ε1, false, τ))) +
      weight (Moves.vxor v (sp n (ε1, true, τ))) = 2 * bv v.x ε1 τ + 2 * n := by
  have py := pair_id v.y τ
  have pz := pair_id v.z τ
  rw [weight_vxor_sp, weight_vxor_sp]
  cases ε1
  · simp only [Bool.false_xor]
    omega
  · simp only [Bool.xor_false, Bool.xor_true, Bool.not_true]
    omega

/-- Pairing to isolate the `y`-block. -/
lemma pair_weight_y {n : ℕ} (v : Moves n) (ε2 τ : Bool) :
    weight (Moves.vxor v (sp n (false, ε2, τ))) +
      weight (Moves.vxor v (sp n (true, !ε2, τ))) = 2 * bv v.y ε2 τ + 2 * n := by
  have px := pair_id v.x τ
  have pz := pair_id v.z τ
  rw [weight_vxor_sp, weight_vxor_sp]
  cases ε2 <;> simp <;> omega

/-- Pairing to isolate the `z`-block. -/
lemma pair_weight_z {n : ℕ} (v : Moves n) (ε2 τ : Bool) :
    weight (Moves.vxor v (sp n (false, ε2, τ))) +
      weight (Moves.vxor v (sp n (true, ε2, τ))) = 2 * bv v.z ε2 τ + 2 * n := by
  have px := pair_id v.x τ
  have py := pair_id v.y τ
  rw [weight_vxor_sp, weight_vxor_sp]
  cases ε2 <;> simp <;> omega

/-- In the case `n = 4k + 3`, if all eight coset weights are at least `6k+4`,
then for each block the two values where the block contributes `2k+1` form the
graph of `δ ↦ τ ⊕ c` for some bit `c`. -/
lemma graph_of {n : ℕ} (α : Fin n → Bool) (k : ℕ)
    (hO : Ocard n = 2 * k + 2) (hE : Ecard n = 2 * k + 1)
    (hb : ∀ δ τ : Bool, 2 * k + 1 ≤ bv α δ τ ∧ bv α δ τ ≤ 2 * k + 2) :
    ∃ c : Bool, ∀ δ τ : Bool, (bv α δ τ = 2 * k + 1) ↔ ((δ ^^ τ) = c) := by
  have hp1 : bv α false false + bv α true true = Ocard n + 2 * qon α := by
    rw [bv_ff, bv_tt]
    have hp := pon_le α
    omega
  have hp2 : bv α false false + bv α false true = 2 * pon α + Ecard n := by
    rw [bv_ff, bv_ft]
    have hq := qon_le α
    omega
  have hp3 := pair_id α false
  have hp4 := pair_id α true
  by_cases h0 : bv α false false = 2 * k + 1
  · refine ⟨false, ?_⟩
    have hbff := hb false false
    have hbft := hb false true
    have hbtf := hb true false
    have hbtt := hb true true
    have g1 : bv α true true = 2 * k + 1 := by omega
    have g2 : bv α false true = 2 * k + 2 := by omega
    have g3 : bv α true false = 2 * k + 2 := by omega
    intro δ τ
    cases δ <;> cases τ <;> simp_all
  · refine ⟨true, ?_⟩
    have hbff := hb false false
    have hbft := hb false true
    have hbtf := hb true false
    have hbtt := hb true true
    have g0 : bv α false false = 2 * k + 2 := by omega
    have g1 : bv α true true = 2 * k + 2 := by omega
    have g2 : bv α false true = 2 * k + 1 := by omega
    have g3 : bv α true false = 2 * k + 1 := by omega
    intro δ τ
    cases δ <;> cases τ <;> simp_all

/-- The upper bound: every coset contains an element of weight at most
`6 * (n / 4) + n % 4`. The proof averages the eight coset weights (their sum
is always `12n`), with a parity refinement when `n % 4 ∈ {2, 3}`. -/
lemma upper_bound {n : ℕ} (v : Moves n) :
    ∃ ε : Bool × Bool × Bool, weight (Moves.vxor v (sp n ε)) ≤ answer n := by
  by_contra hnc
  push Not at hnc
  have hsum := sum_weights v
  obtain ⟨k, r, hk, hr⟩ : ∃ k r, n = 4 * k + r ∧ r < 4 :=
    ⟨n / 4, n % 4, by omega, by omega⟩
  have h000 := hnc (false, false, false)
  have h001 := hnc (false, false, true)
  have h010 := hnc (false, true, false)
  have h011 := hnc (false, true, true)
  have h100 := hnc (true, false, false)
  have h101 := hnc (true, false, true)
  have h110 := hnc (true, true, false)
  have h111 := hnc (true, true, true)
  interval_cases r
  · have hans : answer n = 6 * k := by simp only [answer]; omega
    omega
  · have hans : answer n = 6 * k + 1 := by simp only [answer]; omega
    omega
  · have hans : answer n = 6 * k + 2 := by simp only [answer]; omega
    have hW : ∀ ε : Bool × Bool × Bool, weight (Moves.vxor v (sp n ε)) = 6 * k + 3 := by
      intro ε
      obtain ⟨a, b, c⟩ := ε
      cases a <;> cases b <;> cases c <;> omega
    have hbvx : ∀ δ τ : Bool, bv v.x δ τ = 2 * k + 1 := by
      intro δ τ
      have h1 := hW (δ, false, τ)
      have h2 := hW (δ, true, τ)
      have h3 := pair_weight v δ τ
      omega
    have hff := bv_ff v.x
    have hft := bv_ft v.x
    have hE := Ecard_eq n
    have hq := qon_le v.x
    have h1 := hbvx false false
    have h2 := hbvx false true
    omega
  · have hans : answer n = 6 * k + 3 := by simp only [answer]; omega
    have hbx : ∀ δ τ : Bool, 2 * k + 1 ≤ bv v.x δ τ ∧ bv v.x δ τ ≤ 2 * k + 2 := by
      intro δ τ
      have lower : ∀ δ' τ' : Bool, 2 * k + 1 ≤ bv v.x δ' τ' := by
        intro δ' τ'
        have h1 := hnc (δ', false, τ')
        have h2 := hnc (δ', true, τ')
        have h3 := pair_weight v δ' τ'
        omega
      have h4 := pair_id v.x τ
      have h5 := lower false τ
      have h6 := lower true τ
      refine ⟨lower δ τ, ?_⟩
      cases δ <;> omega
    have hby : ∀ δ τ : Bool, 2 * k + 1 ≤ bv v.y δ τ ∧ bv v.y δ τ ≤ 2 * k + 2 := by
      intro δ τ
      have lower : ∀ δ' τ' : Bool, 2 * k + 1 ≤ bv v.y δ' τ' := by
        intro δ' τ'
        have h1 := hnc (false, δ', τ')
        have h2 := hnc (true, !δ', τ')
        have h3 := pair_weight_y v δ' τ'
        omega
      have h4 := pair_id v.y τ
      have h5 := lower false τ
      have h6 := lower true τ
      refine ⟨lower δ τ, ?_⟩
      cases δ <;> omega
    have hbz : ∀ δ τ : Bool, 2 * k + 1 ≤ bv v.z δ τ ∧ bv v.z δ τ ≤ 2 * k + 2 := by
      intro δ τ
      have lower : ∀ δ' τ' : Bool, 2 * k + 1 ≤ bv v.z δ' τ' := by
        intro δ' τ'
        have h1 := hnc (false, δ', τ')
        have h2 := hnc (true, δ', τ')
        have h3 := pair_weight_z v δ' τ'
        omega
      have h4 := pair_id v.z τ
      have h5 := lower false τ
      have h6 := lower true τ
      refine ⟨lower δ τ, ?_⟩
      cases δ <;> omega
    have hE2 : Ecard n = 2 * k + 1 := by have hE := Ecard_eq n; omega
    have hO2 : Ocard n = 2 * k + 2 := by have hE := Ecard_eq n; have hO := OE_sum n; omega
    obtain ⟨cX, hcX⟩ := graph_of v.x k hO2 hE2 hbx
    obtain ⟨cY, hcY⟩ := graph_of v.y k hO2 hE2 hby
    obtain ⟨cZ, hcZ⟩ := graph_of v.z k hO2 hE2 hbz
    by_cases hcc : (cX ^^ cZ) = cY
    · have hW := hnc (cX, cZ, false)
      rw [weight_vxor_sp, hans] at hW
      have g1 : bv v.x cX false = 2 * k + 1 := (hcX cX false).2 (by cases cX <;> simp)
      have g2 : bv v.z cZ false = 2 * k + 1 := (hcZ cZ false).2 (by cases cZ <;> simp)
      have g3 : bv v.y (cX ^^ cZ) false = 2 * k + 1 :=
        (hcY (cX ^^ cZ) false).2 (by rw [hcc]; simp)
      omega
    · have hW := hnc (cX ^^ true, cZ ^^ true, true)
      rw [weight_vxor_sp, hans] at hW
      have g1 : bv v.x (cX ^^ true) true = 2 * k + 1 :=
        (hcX (cX ^^ true) true).2 (by cases cX <;> simp)
      have g2 : bv v.z (cZ ^^ true) true = 2 * k + 1 :=
        (hcZ (cZ ^^ true) true).2 (by cases cZ <;> simp)
      have g3 : bv v.y ((cX ^^ true) ^^ (cZ ^^ true)) true = 2 * k + 1 := by
        apply (hcY ((cX ^^ true) ^^ (cZ ^^ true)) true).2
        cases cX <;> cases cY <;> cases cZ <;> simp_all
      omega

/-- Proof-producing helpers for token indices (kept as term-mode applications
so that indices are syntactically reproducible). -/
lemma lt_n2 {n : ℕ} (hn : 2 ≤ n) : n - 2 < n := by omega
lemma lt_n1 {n : ℕ} (hn : 2 ≤ n) : n - 1 < n := by omega
lemma lt_n1j {n j : ℕ} (hj : j < n) : n - 1 - j < n := by omega
lemma lt_n2m {n m : ℕ} (hm : m + 1 < n) : n - 2 - m < n := by omega
lemma tp_y {n j : ℕ} (hj : j < n) : (n - 1 - j) + j < n := by omega
lemma tp_z {n j : ℕ} (hj : j < n) : (n - 1 - j) + 0 < n := by omega
lemma tp_y1 {n : ℕ} (hn : 2 ≤ n) : (n - 2) + 1 < n := by omega
lemma tp_last {n : ℕ} (hn : 0 < n) : (n - 1) + 0 < n := by omega

/-- Converting between `Fin n` indices with equal values. -/
lemma convFin {n : ℕ} (f : Fin n → Bool) (a b : ℕ) (ha : a < n) (hb : b < n)
    (hab : a = b) : f ⟨a, ha⟩ = f ⟨b, hb⟩ := by
  subst hab
  congr 1

/-- The main reduction: if `v` acts trivially on all tokens and `S` is a span
element that agrees with `v` on the three "boundary" lines (the length-`n`
`y`-line, the length-`n` `z`-line and the length-`2` `x`-line), then `v = S`.
This is the propagation step of the kernel classification. -/
lemma kernel_of_reduction {n : ℕ} (hn : 0 < n) (hn2 : 2 ≤ n) (v S : Moves n)
    (hv : applyMoves v = fun _ => false)
    (hS : applyMoves S = fun _ => false)
    (hy : S.y ⟨0, hn⟩ = v.y ⟨0, hn⟩)
    (hz : S.z ⟨0, hn⟩ = v.z ⟨0, hn⟩)
    (hx : S.x ⟨n - 2, lt_n2 hn2⟩ = v.x ⟨n - 2, lt_n2 hn2⟩) :
    v = S := by
  set v3 := Moves.vxor v S with hv3
  have hv3app : applyMoves v3 = fun _ => false := by
    funext t
    rw [applyMoves_vxor]
    simp [hS, hv]
  have key : ∀ (a b : ℕ) (h : a + b < n),
      (v3.x ⟨a, lt_left h⟩ ^^ v3.y ⟨b, lt_right h⟩ ^^
        v3.z ⟨n - 1 - a - b, lt_third h⟩) = false := by
    intro a b h
    exact congrFun hv3app ⟨(a, b), h⟩
  have hy0 : v3.y ⟨0, hn⟩ = false := by
    have h1 : v3.y ⟨0, hn⟩ = (v.y ⟨0, hn⟩ ^^ S.y ⟨0, hn⟩) := rfl
    rw [h1, hy]
    exact Bool.xor_self _
  have hz0 : v3.z ⟨0, hn⟩ = false := by
    have h1 : v3.z ⟨0, hn⟩ = (v.z ⟨0, hn⟩ ^^ S.z ⟨0, hn⟩) := rfl
    rw [h1, hz]
    exact Bool.xor_self _
  have hx2 : v3.x ⟨n - 2, lt_n2 hn2⟩ = false := by
    have h1 : v3.x ⟨n - 2, lt_n2 hn2⟩ = (v.x ⟨n - 2, lt_n2 hn2⟩ ^^ S.x ⟨n - 2, lt_n2 hn2⟩) :=
      rfl
    rw [h1, hx]
    exact Bool.xor_self _
  -- propagation: `y` and `z` lines are mirrors of `x` lines
  have h_y : ∀ j (hj : j < n), v3.y ⟨j, hj⟩ = v3.x ⟨n - 1 - j, lt_n1j hj⟩ := by
    intro j hj
    have hk := key (n - 1 - j) j (tp_y hj)
    rw [convFin v3.z (n - 1 - (n - 1 - j) - j) 0 (lt_third (tp_y hj)) hn (by omega)] at hk
    rw [hz0] at hk
    rw [convFin v3.y j j (lt_right (tp_y hj)) hj rfl] at hk
    simp only [Bool.xor_false] at hk
    rw [xor_eq_false_iff] at hk
    rw [← hk]
  have h_z : ∀ j (hj : j < n), v3.z ⟨j, hj⟩ = v3.x ⟨n - 1 - j, lt_n1j hj⟩ := by
    intro j hj
    have hk := key (n - 1 - j) 0 (tp_z hj)
    rw [convFin v3.y 0 0 (lt_right (tp_z hj)) hn rfl, hy0] at hk
    rw [convFin v3.z (n - 1 - (n - 1 - j) - 0) j (lt_third (tp_z hj)) hj (by omega)] at hk
    simp only [Bool.xor_false] at hk
    rw [xor_eq_false_iff] at hk
    rw [← hk]
  -- the second `y`-line vanishes
  have h_y1 : ∀ (h1 : 1 < n), v3.y ⟨1, h1⟩ = false := by
    intro h1
    have hk := key (n - 2) 1 (tp_y1 hn2)
    rw [convFin v3.x (n - 2) (n - 2) (lt_left (tp_y1 hn2)) (lt_n2 hn2) rfl, hx2] at hk
    rw [convFin v3.z (n - 1 - (n - 2) - 1) 0 (lt_third (tp_y1 hn2)) hn (by omega)] at hk
    rw [hz0] at hk
    rw [convFin v3.y 1 1 (lt_right (tp_y1 hn2)) h1 rfl] at hk
    simp only [Bool.xor_false, Bool.false_xor] at hk
    exact hk
  -- the `x` lines are all equal
  have hchain : ∀ m (hm : m + 1 < n), v3.x ⟨m, lt_left hm⟩ = v3.x ⟨m + 1, hm⟩ := by
    intro m hm
    have hk := key m 1 hm
    rw [convFin v3.z (n - 1 - m - 1) (n - 2 - m) (lt_third hm) (lt_n2m hm) (by omega)] at hk
    rw [h_z (n - 2 - m) (lt_n2m hm)] at hk
    rw [convFin v3.x (n - 1 - (n - 2 - m)) (m + 1) (lt_n1j (lt_n2m hm)) hm (by omega)] at hk
    rw [h_y1 (lt_right hm)] at hk
    simp only [Bool.xor_false] at hk
    exact (xor_eq_false_iff).1 hk
  have x_last : ∀ (h : n - 1 < n), v3.x ⟨n - 1, h⟩ = false := by
    intro h
    have hk := key (n - 1) 0 (tp_last hn)
    rw [convFin v3.y 0 0 (lt_right (tp_last hn)) hn rfl, hy0] at hk
    rw [convFin v3.z (n - 1 - (n - 1) - 0) 0 (lt_third (tp_last hn)) hn (by omega)] at hk
    rw [hz0] at hk
    rw [convFin v3.x (n - 1) (n - 1) (lt_left (tp_last hn)) h rfl] at hk
    simp only [Bool.xor_false] at hk
    exact hk
  have x_const : ∀ j (hj : j < n), v3.x ⟨j, hj⟩ = v3.x ⟨0, hn⟩ := by
    intro j
    induction j with
    | zero => intro hj; exact convFin v3.x 0 0 hj hn rfl
    | succ j ih =>
      intro hj1
      have hj : j < n := by omega
      rw [← hchain j hj1, convFin v3.x j j (lt_left hj1) hj rfl]
      exact ih hj
  have hx0 : v3.x ⟨0, hn⟩ = false := by
    have h1 := x_last (lt_n1 hn2)
    have h2 := x_const (n - 1) (lt_n1 hn2)
    rw [h1] at h2
    exact h2.symm
  have x_all : ∀ j (hj : j < n), v3.x ⟨j, hj⟩ = false := by
    intro j hj
    rw [x_const j hj, hx0]
  have hv3z : v3 = zeroMove n := by
    apply Moves.ext
    · funext i
      have h1 : v3.x i = v3.x ⟨i.val, i.2⟩ := congrArg v3.x (Fin.ext rfl)
      rw [h1]
      exact x_all i.val i.2
    · funext i
      have h1 : v3.y i = v3.y ⟨i.val, i.2⟩ := congrArg v3.y (Fin.ext rfl)
      rw [h1, h_y i.val i.2]
      exact x_all (n - 1 - i.val) (lt_n1j i.2)
    · funext i
      have h1 : v3.z i = v3.z ⟨i.val, i.2⟩ := congrArg v3.z (Fin.ext rfl)
      rw [h1, h_z i.val i.2]
      exact x_all (n - 1 - i.val) (lt_n1j i.2)
  have hA : Moves.vxor v S = zeroMove n := by rwa [hv3] at hv3z
  exact vxor_eq_zero hA

/-- The kernel classification: a move that flips every token an even number of
times is one of the eight span elements. -/
lemma kernel_eq_span {n : ℕ} (hn : 0 < n) {v : Moves n}
    (hv : applyMoves v = fun _ => false) : ∃ ε : Bool × Bool × Bool, v = sp n ε := by
  rcases (show n = 1 ∨ 2 ≤ n by omega) with rfl | hn2
  · -- n = 1: direct case analysis on the three line-values
    set z : Fin 1 := ⟨0, by omega⟩ with hzdef
    have hzv : z.val = 0 := rfl
    have key : (v.x z ^^ v.y z ^^ v.z z) = false := by
      have h00 : (0 : ℕ) + 0 < 1 := by omega
      exact congrFun hv ⟨(0, 0), h00⟩
    have cx : v.x = fun _ => v.x z := by
      funext i
      congr 1
      exact Fin.ext (by omega)
    have cy : v.y = fun _ => v.y z := by
      funext i
      congr 1
      exact Fin.ext (by omega)
    have cz : v.z = fun _ => v.z z := by
      funext i
      congr 1
      exact Fin.ext (by omega)
    generalize hA : v.x z = A
    generalize hB : v.y z = B
    generalize hC : v.z z = C
    rw [hA] at cx
    rw [hB] at cy
    rw [hC] at cz
    rw [hA, hB, hC] at key
    refine ⟨(A, C, false), ?_⟩
    apply Moves.ext
    · funext i
      rw [cx]
      cases A <;> cases B <;> cases C <;> simp_all [sp]
    · funext i
      rw [cy]
      cases A <;> cases B <;> cases C <;> simp_all [sp]
    · funext i
      rw [cz]
      cases A <;> cases B <;> cases C <;> simp_all [sp]
  · -- n ≥ 2: reduce to the propagation lemma
    generalize hA : v.y ⟨0, hn⟩ = A
    generalize hB : v.z ⟨0, hn⟩ = B
    generalize hX : v.x ⟨n - 2, lt_n2 hn2⟩ = X
    by_cases hnodd : n % 2 = 1
    · have he0 : e n ⟨0, hn⟩ = false := by
        have h2 : ¬ (0 : ℕ) % 2 = n % 2 := by omega
        simp [e, h2]
      have hex2 : e n ⟨n - 2, lt_n2 hn2⟩ = true := by
        have h2 : (n - 2) % 2 = n % 2 := by omega
        simp [e, h2]
      refine ⟨(A ^^ B, B, X ^^ A ^^ B), ?_⟩
      apply kernel_of_reduction hn hn2 v (sp n (A ^^ B, B, X ^^ A ^^ B)) hv
        (funext (applyMoves_sp _))
      · rw [← hA]
        dsimp only [sp]
        rw [he0]
        cases A <;> cases B <;> cases X <;> simp
      · rw [← hB]
        dsimp only [sp]
        rw [he0]
        cases A <;> cases B <;> cases X <;> simp
      · rw [← hX]
        dsimp only [sp]
        rw [hex2]
        cases A <;> cases B <;> cases X <;> simp
    · have hnodd2 : n % 2 = 0 := by omega
      have he0 : e n ⟨0, hn⟩ = true := by
        have h2 : (0 : ℕ) % 2 = n % 2 := by omega
        simp [e, h2]
      have hex2 : e n ⟨n - 2, lt_n2 hn2⟩ = true := by
        have h2 : (n - 2) % 2 = n % 2 := by omega
        simp [e, h2]
      refine ⟨(A ^^ B, B ^^ (X ^^ A ^^ B), X ^^ A ^^ B), ?_⟩
      apply kernel_of_reduction hn hn2 v (sp n (A ^^ B, B ^^ (X ^^ A ^^ B), X ^^ A ^^ B)) hv
        (funext (applyMoves_sp _))
      · rw [← hA]
        dsimp only [sp]
        rw [he0]
        cases A <;> cases B <;> cases X <;> simp
      · rw [← hB]
        dsimp only [sp]
        rw [he0]
        cases A <;> cases B <;> cases X <;> simp
      · rw [← hX]
        dsimp only [sp]
        rw [hex2]
        cases A <;> cases B <;> cases X <;> simp

/-- The four line-flipping patterns used for the extremal configuration:
flip the lines whose index is `1` or `2` modulo `4`. -/
def P12 : ℕ → Bool := fun i => decide (i % 4 = 1 ∨ i % 4 = 2)
/-- Indices `0` or `3` modulo `4`. -/
def P03 : ℕ → Bool := fun i => decide (i % 4 = 0 ∨ i % 4 = 3)
/-- Indices `2` or `3` modulo `4`. -/
def P23 : ℕ → Bool := fun i => decide (i % 4 = 2 ∨ i % 4 = 3)
/-- Indices `0` or `1` modulo `4`. -/
def P01 : ℕ → Bool := fun i => decide (i % 4 = 0 ∨ i % 4 = 1)

lemma P12_per : ∀ i, P12 (i + 4) = P12 i := by intro i; simp [P12]
lemma P03_per : ∀ i, P03 (i + 4) = P03 i := by intro i; simp [P03]
lemma P23_per : ∀ i, P23 (i + 4) = P23 i := by intro i; simp [P23]
lemma P01_per : ∀ i, P01 (i + 4) = P01 i := by intro i; simp [P01]

/-- Moves built from three periodic patterns. -/
def v0of (n : ℕ) (Px Py Pz : ℕ → Bool) : Moves n :=
  ⟨fun i => Px i.val, fun i => Py i.val, fun i => Pz i.val⟩

lemma card_range4 (P : ℕ → Prop) [DecidablePred P] :
    ((Finset.range 4).filter P).card =
      (if P 0 then 1 else 0) + (if P 1 then 1 else 0) +
        (if P 2 then 1 else 0) + (if P 3 then 1 else 0) := by
  rw [Finset.card_filter]
  repeat rw [Finset.sum_range_succ]
  simp

lemma card_range0 (P : ℕ → Prop) [DecidablePred P] :
    ((Finset.range 0).filter P).card = 0 := by simp

lemma card_range1 (P : ℕ → Prop) [DecidablePred P] :
    ((Finset.range 1).filter P).card = (if P 0 then 1 else 0) := by
  rw [Finset.card_filter]
  repeat rw [Finset.sum_range_succ]
  simp

lemma card_range2 (P : ℕ → Prop) [DecidablePred P] :
    ((Finset.range 2).filter P).card = (if P 0 then 1 else 0) + (if P 1 then 1 else 0) := by
  rw [Finset.card_filter]
  repeat rw [Finset.sum_range_succ]
  simp

lemma card_range3 (P : ℕ → Prop) [DecidablePred P] :
    ((Finset.range 3).filter P).card =
      (if P 0 then 1 else 0) + (if P 1 then 1 else 0) + (if P 2 then 1 else 0) := by
  rw [Finset.card_filter]
  repeat rw [Finset.sum_range_succ]
  simp

/-- Evaluating `pon` of a pattern move. -/
lemma pon_eval {n : ℕ} (F : Fin n → Bool) (P : ℕ → Bool) (hF : ∀ i, F i = P i.val)
    (hP : ∀ i, P (i + 4) = P i) {k r s : ℕ} (hk : n = 4 * k + r) (hn2 : n % 2 = s) :
    pon F = k * (((Finset.range 4).filter fun i => ((P i && !decide (i % 2 = s))) = true).card) +
      (((Finset.range r).filter fun i => ((P i && !decide (i % 2 = s))) = true).card) := by
  have e1 : pon F = (Finset.univ.filter fun i : Fin n => (F i && !(e n i)) = true).card := by
    apply congrArg Finset.card
    apply Finset.filter_congr
    intro i _
    cases (F i) <;> cases (e n i) <;> simp
  rw [e1]
  rw [show (Finset.univ.filter fun i : Fin n => (F i && !(e n i)) = true) =
      (Finset.univ.filter fun i : Fin n => (P i.val && !decide (i.val % 2 = n % 2)) = true) from
    Finset.filter_congr (fun i _ => by rw [hF i]; simp [e])]
  rw [Count.card_fin_filter (fun i => (P i && !decide (i % 2 = n % 2))) n]
  rw [hn2]
  rw [hk]
  rw [Count.card_filter_range_periodic _ (by intro i; simp [hP i, Nat.add_mod]) k r]

/-- Evaluating `qon` of a pattern move. -/
lemma qon_eval {n : ℕ} (F : Fin n → Bool) (P : ℕ → Bool) (hF : ∀ i, F i = P i.val)
    (hP : ∀ i, P (i + 4) = P i) {k r s : ℕ} (hk : n = 4 * k + r) (hn2 : n % 2 = s) :
    qon F = k * (((Finset.range 4).filter fun i => ((P i && decide (i % 2 = s))) = true).card) +
      (((Finset.range r).filter fun i => ((P i && decide (i % 2 = s))) = true).card) := by
  have e1 : qon F = (Finset.univ.filter fun i : Fin n => (F i && (e n i)) = true).card := by
    apply congrArg Finset.card
    apply Finset.filter_congr
    intro i _
    cases (F i) <;> cases (e n i) <;> simp
  rw [e1]
  rw [show (Finset.univ.filter fun i : Fin n => (F i && (e n i)) = true) =
      (Finset.univ.filter fun i : Fin n => (P i.val && decide (i.val % 2 = n % 2)) = true) from
    Finset.filter_congr (fun i _ => by rw [hF i]; simp [e])]
  rw [Count.card_fin_filter (fun i => (P i && decide (i % 2 = n % 2))) n]
  rw [hn2]
  rw [hk]
  rw [Count.card_filter_range_periodic _ (by intro i; simp [hP i, Nat.add_mod]) k r]

/-- The lower bound: an explicit move all of whose coset elements have weight
at least `6 * (n / 4) + n % 4`. -/
lemma lower_bound {n : ℕ} :
    ∃ v : Moves n, ∀ ε : Bool × Bool × Bool, answer n ≤ weight (Moves.vxor v (sp n ε)) := by
  obtain ⟨k, r, hk, hr⟩ : ∃ k r, n = 4 * k + r ∧ r < 4 :=
    ⟨n / 4, n % 4, by omega, by omega⟩
  interval_cases r
  · refine ⟨v0of n P12 P12 P12, ?_⟩
    have hans : answer n = 6 * k := by simp only [answer]; omega
    have hn2 : n % 2 = 0 := by omega
    have hE : Ecard n = 2 * k := by have h1 := Ecard_eq n; omega
    have hO : Ocard n = 2 * k := by have h1 := Ecard_eq n; have h2 := OE_sum n; omega
    have c1 : pon (v0of n P12 P12 P12).x = k := by
      rw [pon_eval (v0of n P12 P12 P12).x P12 (fun i => rfl) P12_per hk hn2, card_range4, card_range0]
      simp [P12]
    have c2 : qon (v0of n P12 P12 P12).x = k := by
      rw [qon_eval (v0of n P12 P12 P12).x P12 (fun i => rfl) P12_per hk hn2, card_range4, card_range0]
      simp [P12]
    have c3 : pon (v0of n P12 P12 P12).y = k := c1
    have c4 : qon (v0of n P12 P12 P12).y = k := c2
    have c5 : pon (v0of n P12 P12 P12).z = k := c1
    have c6 : qon (v0of n P12 P12 P12).z = k := c2
    intro ε
    obtain ⟨ε1, ε2, ε3⟩ := ε
    cases ε1 <;> cases ε2 <;> cases ε3 <;> rw [weight_vxor_sp] <;> simp [bv_eq] <;> omega
  · refine ⟨v0of n P03 P12 P12, ?_⟩
    have hans : answer n = 6 * k + 1 := by simp only [answer]; omega
    have hn2 : n % 2 = 1 := by omega
    have hE : Ecard n = 2 * k := by have h1 := Ecard_eq n; omega
    have hO : Ocard n = 2 * k + 1 := by have h1 := Ecard_eq n; have h2 := OE_sum n; omega
    have c1 : pon (v0of n P03 P12 P12).x = k + 1 := by
      rw [pon_eval (v0of n P03 P12 P12).x P03 (fun i => rfl) P03_per hk hn2, card_range4, card_range1]
      simp [P03]
    have c2 : qon (v0of n P03 P12 P12).x = k := by
      rw [qon_eval (v0of n P03 P12 P12).x P03 (fun i => rfl) P03_per hk hn2, card_range4, card_range1]
      simp [P03]
    have c3 : pon (v0of n P03 P12 P12).y = k := by
      rw [pon_eval (v0of n P03 P12 P12).y P12 (fun i => rfl) P12_per hk hn2, card_range4, card_range1]
      simp [P12]
    have c4 : qon (v0of n P03 P12 P12).y = k := by
      rw [qon_eval (v0of n P03 P12 P12).y P12 (fun i => rfl) P12_per hk hn2, card_range4, card_range1]
      simp [P12]
    have c5 : pon (v0of n P03 P12 P12).z = k := c3
    have c6 : qon (v0of n P03 P12 P12).z = k := c4
    intro ε
    obtain ⟨ε1, ε2, ε3⟩ := ε
    cases ε1 <;> cases ε2 <;> cases ε3 <;> rw [weight_vxor_sp] <;> simp [bv_eq] <;> omega
  · refine ⟨v0of n P23 P23 P01, ?_⟩
    have hans : answer n = 6 * k + 2 := by simp only [answer]; omega
    have hn2 : n % 2 = 0 := by omega
    have hE : Ecard n = 2 * k + 1 := by have h1 := Ecard_eq n; omega
    have hO : Ocard n = 2 * k + 1 := by have h1 := Ecard_eq n; have h2 := OE_sum n; omega
    have c1 : pon (v0of n P23 P23 P01).x = k := by
      rw [pon_eval (v0of n P23 P23 P01).x P23 (fun i => rfl) P23_per hk hn2, card_range4, card_range2]
      simp [P23]
    have c2 : qon (v0of n P23 P23 P01).x = k := by
      rw [qon_eval (v0of n P23 P23 P01).x P23 (fun i => rfl) P23_per hk hn2, card_range4, card_range2]
      simp [P23]
    have c3 : pon (v0of n P23 P23 P01).y = k := c1
    have c4 : qon (v0of n P23 P23 P01).y = k := c2
    have c5 : pon (v0of n P23 P23 P01).z = k + 1 := by
      rw [pon_eval (v0of n P23 P23 P01).z P01 (fun i => rfl) P01_per hk hn2, card_range4, card_range2]
      simp [P01]
    have c6 : qon (v0of n P23 P23 P01).z = k + 1 := by
      rw [qon_eval (v0of n P23 P23 P01).z P01 (fun i => rfl) P01_per hk hn2, card_range4, card_range2]
      simp [P01]
    intro ε
    obtain ⟨ε1, ε2, ε3⟩ := ε
    cases ε1 <;> cases ε2 <;> cases ε3 <;> rw [weight_vxor_sp] <;> simp [bv_eq] <;> omega
  · refine ⟨v0of n P01 P01 P01, ?_⟩
    have hans : answer n = 6 * k + 3 := by simp only [answer]; omega
    have hn2 : n % 2 = 1 := by omega
    have hE : Ecard n = 2 * k + 1 := by have h1 := Ecard_eq n; omega
    have hO : Ocard n = 2 * k + 2 := by have h1 := Ecard_eq n; have h2 := OE_sum n; omega
    have c1 : pon (v0of n P01 P01 P01).x = k + 1 := by
      rw [pon_eval (v0of n P01 P01 P01).x P01 (fun i => rfl) P01_per hk hn2, card_range4, card_range3]
      simp [P01]
    have c2 : qon (v0of n P01 P01 P01).x = k + 1 := by
      rw [qon_eval (v0of n P01 P01 P01).x P01 (fun i => rfl) P01_per hk hn2, card_range4, card_range3]
      simp [P01]
    have c3 : pon (v0of n P01 P01 P01).y = k + 1 := c1
    have c4 : qon (v0of n P01 P01 P01).y = k + 1 := c2
    have c5 : pon (v0of n P01 P01 P01).z = k + 1 := c1
    have c6 : qon (v0of n P01 P01 P01).z = k + 1 := c2
    intro ε
    obtain ⟨ε1, ε2, ε3⟩ := ε
    cases ε1 <;> cases ε2 <;> cases ε3 <;> rw [weight_vxor_sp] <;> simp [bv_eq] <;> omega

/-- `f C` is at most the weight of any move producing `C`. -/
lemma f_le {n : ℕ} {C : Token n → Bool} {v : Moves n} (h : applyMoves v = C) :
    f C ≤ weight v :=
  Nat.sInf_le ⟨v, h, rfl⟩

/-- The minimum is attained: some move produces `C` with weight `f C`. -/
lemma f_spec {n : ℕ} {C : Token n → Bool} (hC : Admissible C) :
    ∃ w : Moves n, applyMoves w = C ∧ weight w = f C := by
  obtain ⟨v, hv⟩ := hC
  have hmem : sInf {m : ℕ | ∃ v : Moves n, applyMoves v = C ∧ weight v = m} ∈
      {m : ℕ | ∃ v : Moves n, applyMoves v = C ∧ weight v = m} :=
    Nat.sInf_mem ⟨weight v, v, hv, rfl⟩
  obtain ⟨w, hw1, hw2⟩ := hmem
  exact ⟨w, hw1, hw2⟩

/-- The upper bound for `f`. -/
lemma f_le_answer {n : ℕ} (C : Token n → Bool) (hC : Admissible C) :
    f C ≤ answer n := by
  obtain ⟨v, hv⟩ := hC
  obtain ⟨ε, hε⟩ := upper_bound (n := n) (v := v)
  apply le_trans (f_le (v := Moves.vxor v (sp n ε)) ?_) hε
  rw [← hv]
  funext t
  rw [applyMoves_vxor, applyMoves_sp]
  simp

/-- The lower bound for `f`: some admissible configuration needs at least
`answer n` operations. -/
lemma answer_le_f {n : ℕ} (hn : 0 < n) :
    ∃ C : Token n → Bool, Admissible C ∧ answer n ≤ f C := by
  obtain ⟨v, hv⟩ := lower_bound (n := n)
  refine ⟨applyMoves v, ⟨v, rfl⟩, ?_⟩
  have key : ∀ w : Moves n, applyMoves w = applyMoves v → answer n ≤ weight w := by
    intro w hw
    obtain ⟨ε, hε⟩ := kernel_eq_span hn (v := Moves.vxor w v) (by
      funext t
      rw [applyMoves_vxor, hw]
      simp)
    have h2 : w = Moves.vxor v (sp n ε) := by
      have h1 := congrArg (fun u => Moves.vxor u v) hε
      rw [vxor_assoc, vxor_self, vxor_zero, vxor_comm] at h1
      exact h1
    rw [h2]
    exact hv ε
  obtain ⟨w, hw1, hw2⟩ := f_spec (C := applyMoves v) ⟨v, rfl⟩
  rw [← hw2]
  exact key w hw1

snip end

problem usa2013_p3 (n : ℕ) (hn : 0 < n) :
    IsGreatest {m : ℕ | ∃ C : Token n → Bool, Admissible C ∧ f C = m} (answer n) := by
  obtain ⟨C, hCadm, hCge⟩ := answer_le_f hn
  have hCle : f C ≤ answer n := f_le_answer C hCadm
  have hCeq : f C = answer n := le_antisymm hCle hCge
  refine ⟨?_, ?_⟩
  · exact ⟨C, hCadm, hCeq⟩
  · intro m hm
    obtain ⟨C', hC', rfl⟩ := hm
    exact f_le_answer C' hC'

end Usa2013P3
