/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Tactic
public import Mathlib.Data.Nat.Find
public import Mathlib.Logic.Relation
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics] }

/-!
# USA Mathematical Olympiad 2026, Problem 2

Annie is playing a game where she starts with a row of positive integers, written
on a blackboard, each of which is a power of 2. On each turn, she can erase two
adjacent numbers and replace them with a power of 2 that is greater than either of
the erased numbers. This shortens the row of numbers, and she continues to take
turns until only one number remains. Annie wins the game if the final remaining
number is less than 4 times the sum of the original numbers. Is it always possible
for Annie to win, regardless of the starting row of numbers?
-/

namespace Usa2026P2

/-- A positive integer which is a power of two (in particular `1 = 2 ^ 0` counts). -/
def IsPow2 (x : ℕ) : Prop := ∃ k, x = 2 ^ k

/-- One legal turn of the game: the two adjacent entries `x` and `y` are erased and
replaced by a power of two `z` which is strictly larger than both of them. -/
inductive Move : List ℕ → List ℕ → Prop
  | mk (l r : List ℕ) (x y z : ℕ) (hz : IsPow2 z) (hx : x < z) (hy : y < z) :
      Move (l ++ x :: y :: r) (l ++ z :: r)

snip begin

/-!
### Proof sketch

(following Evan Chen's USAMO 2026 solution notes,
<https://web.evanchen.cc/exams/USAMO-2026-notes.pdf>)

The answer is *yes*.  We prove the stronger statement that Annie can always finish
with a number which is at most
`S a = 2 * a₁ + 4 * a₂ + ... + 4 * a_{n-1} + 2 * aₙ`
(for a row `a = [a₁, ..., aₙ]` with `n ≥ 2`; `S a = a₁` for `n = 1`), and
`S a < 4 * (a₁ + ... + aₙ)`.

The proof is by strong induction on the length of the row.  The key combinatorial
step (`exists_split`) shows that any row with at least two entries can be cut into
a nonempty prefix `u` and a nonempty suffix `v` with `2 * S u ≤ S a` and
`2 * S v ≤ S a`: take the *longest* prefix `u` with `2 * S u ≤ S a`.  If `u` is
already everything but the last entry, that last entry alone works as `v`.
Otherwise the next longer prefix `u ++ [x]` violates the bound, and the overlap
identity `S a = S (u ++ [x]) + S (x :: q)` (where `a = u ++ x :: q`) shows that
the suffix `v = x :: q` satisfies `2 * S v ≤ S a`.  Both halves are then reduced
inductively to powers of two `2 ^ p ≤ S u` and `2 ^ q ≤ S v`, and Annie combines
them into `2 ^ (max p q + 1) = 2 * max (2 ^ p) (2 ^ q) ≤ S a`.
-/

/-- For `l = [b₁, ..., bₘ]`, `innerSum l` is `4 * b₁ + 4 * b₂ + ... + 4 * b_{m-1} + 2 * bₘ`
(and `0` for the empty list): the "tail" of `S` after the first entry. -/
def innerSum : List ℕ → ℕ
  | [] => 0
  | [x] => 2 * x
  | x :: y :: rest => 4 * x + innerSum (y :: rest)

/-- The target bound for a row `a = [a₁, ..., aₙ]`: `a₁` if `n = 1`, and
`2 * a₁ + 4 * a₂ + ... + 4 * a_{n-1} + 2 * aₙ` if `n ≥ 2` (and `0` if `n = 0`). -/
def S : List ℕ → ℕ
  | [] => 0
  | [x] => x
  | x :: y :: rest => 2 * x + innerSum (y :: rest)

@[simp] theorem innerSum_nil : innerSum [] = 0 := rfl
@[simp] theorem innerSum_singleton (x : ℕ) : innerSum [x] = 2 * x := rfl
@[simp] theorem innerSum_cons_cons (x y : ℕ) (rest : List ℕ) :
    innerSum (x :: y :: rest) = 4 * x + innerSum (y :: rest) := rfl

@[simp] theorem S_nil : S [] = 0 := rfl
@[simp] theorem S_singleton (x : ℕ) : S [x] = x := rfl
@[simp] theorem S_cons_cons (x y : ℕ) (rest : List ℕ) :
    S (x :: y :: rest) = 2 * x + innerSum (y :: rest) := rfl

theorem innerSum_le_four_mul_sum : ∀ l : List ℕ, innerSum l ≤ 4 * l.sum
  | [] => by simp
  | [x] => by simp; lia
  | x :: y :: rest => by
      have ih := innerSum_le_four_mul_sum (y :: rest)
      simp only [innerSum_cons_cons, List.sum_cons] at ih ⊢
      lia

/-- The bound `S a` is always less than four times the sum of the row. -/
theorem S_lt_four_mul_sum : ∀ (a : List ℕ), a ≠ [] → (∀ x ∈ a, 0 < x) → S a < 4 * a.sum
  | [], h, _ => (h rfl).elim
  | [x], _, h => by
      have hx : 0 < x := h x (List.mem_singleton_self x)
      simp only [S_singleton, List.sum_singleton]
      lia
  | x :: y :: rest, _, h => by
      have hx : 0 < x := h x List.mem_cons_self
      have h1 := innerSum_le_four_mul_sum (y :: rest)
      simp only [S_cons_cons, List.sum_cons] at h1 ⊢
      lia

/-- The last entry of a nonempty row, doubled, is at most `innerSum` of the row. -/
theorem two_mul_last_le_innerSum : ∀ (q : List ℕ) (y : ℕ), 2 * y ≤ innerSum (q ++ [y])
  | [], y => le_refl _
  | [x], y => by
      simp only [List.singleton_append, innerSum_cons_cons, innerSum_singleton]
      lia
  | x :: z :: q', y => by
      have ih := two_mul_last_le_innerSum (z :: q') y
      rw [show (x :: z :: q') ++ [y] = x :: z :: (q' ++ [y]) from rfl, innerSum_cons_cons,
        show z :: (q' ++ [y]) = (z :: q') ++ [y] from rfl]
      lia

/-- The last entry of a row with at least two entries, doubled, is at most `S` of
the row. -/
theorem two_mul_getLast_le_S (a : List ℕ) (ha : 2 ≤ a.length) (h : a ≠ []) :
    2 * a.getLast h ≤ S a := by
  obtain ⟨x, l, rfl⟩ := List.exists_cons_of_ne_nil h
  have hne2 : l ≠ [] := by rintro rfl; simp at ha
  obtain ⟨y, rest, rfl⟩ := List.exists_cons_of_ne_nil hne2
  rw [S_cons_cons]
  have hgl : (x :: y :: rest).getLast h = (y :: rest).getLast (List.cons_ne_nil y rest) :=
    rfl
  rw [hgl]
  have h2 := two_mul_last_le_innerSum (y :: rest).dropLast
    ((y :: rest).getLast (List.cons_ne_nil y rest))
  rw [List.dropLast_concat_getLast] at h2
  lia

/-- Expanding `innerSum` at the head of a nonempty tail: the head entry is counted
with coefficient `4` in `innerSum` but with coefficient `2` in `S`. -/
theorem innerSum_cons (y : ℕ) (m : List ℕ) (hm : m ≠ []) :
    innerSum (y :: m) = S (y :: m) + 2 * y := by
  obtain ⟨z, rest, rfl⟩ := List.exists_cons_of_ne_nil hm
  simp only [innerSum_cons_cons, S_cons_cons]
  ring

/-- Expanding `S` at the two leftmost entries of a row. -/
theorem S_cons_cons_append (p₁ p₂ : ℕ) (p'' l : List ℕ) (h : p'' ++ l ≠ []) :
    S ((p₁ :: p₂ :: p'') ++ l) = 2 * p₁ + (S ((p₂ :: p'') ++ l) + 2 * p₂) := by
  rw [show (p₁ :: p₂ :: p'') ++ l = p₁ :: p₂ :: (p'' ++ l) from rfl,
    show (p₂ :: p'') ++ l = p₂ :: (p'' ++ l) from rfl, S_cons_cons, innerSum_cons _ _ h]

/-- The overlap identity: if a row is decomposed as `p ++ x :: q` with both `p` and `q`
nonempty (so `x` is a middle entry, counted with coefficient `4`), then its `S`-value
is the sum of the `S`-values of the overlapping parts `p ++ [x]` and `x :: q`. -/
theorem S_append : ∀ (p q : List ℕ) (x : ℕ), p ≠ [] → q ≠ [] →
    S (p ++ x :: q) = S (p ++ [x]) + S (x :: q)
  | [], _, _, h, _ => (h rfl).elim
  | [p₁], q, x, _, hq => by
      obtain ⟨q₁, q', rfl⟩ := List.exists_cons_of_ne_nil hq
      rw [show [p₁] ++ x :: q₁ :: q' = p₁ :: x :: q₁ :: q' from rfl,
        show [p₁] ++ [x] = [p₁, x] from rfl]
      simp only [S_cons_cons, innerSum_cons_cons, innerSum_singleton]
      ring
  | p₁ :: p₂ :: p'', q, x, _, hq => by
      have ih := S_append (p₂ :: p'') q x (by simp) hq
      rw [S_cons_cons_append _ _ _ _ (by simp), S_cons_cons_append _ _ _ _ (by simp), ih]
      ring

/-- The key combinatorial step: any row with at least two entries can be cut into a
nonempty prefix and a nonempty suffix whose `S`-values are both at most `S a / 2`. -/
theorem exists_split (a : List ℕ) (ha : 2 ≤ a.length) :
    ∃ k, 1 ≤ k ∧ k < a.length ∧ 2 * S (a.take k) ≤ S a ∧ 2 * S (a.drop k) ≤ S a := by
  have hne : a ≠ [] := by rintro rfl; simp at ha
  -- Twice the `S`-value of the length-one prefix is at most `S a`.
  have hP1 : 2 * S (a.take 1) ≤ S a := by
    obtain ⟨x, l, rfl⟩ := List.exists_cons_of_ne_nil hne
    have hne2 : l ≠ [] := by rintro rfl; simp at ha
    obtain ⟨y, rest, rfl⟩ := List.exists_cons_of_ne_nil hne2
    have htk : (x :: y :: rest).take 1 = [x] := rfl
    rw [htk, S_singleton, S_cons_cons]
    exact Nat.le_add_right _ _
  have h1 : 1 ≤ a.length - 1 := by lia
  -- Take the longest prefix whose doubled `S`-value is still at most `S a`.
  obtain ⟨k, hk1, hkle, hPk, hmax⟩ : ∃ k, 1 ≤ k ∧ k ≤ a.length - 1 ∧
      2 * S (a.take k) ≤ S a ∧ ∀ m, k < m → m ≤ a.length - 1 →
        ¬ 2 * S (a.take m) ≤ S a :=
    ⟨Nat.findGreatest (fun k => 2 * S (a.take k) ≤ S a) (a.length - 1),
     Nat.le_findGreatest (P := fun k => 2 * S (a.take k) ≤ S a) h1 hP1,
     Nat.findGreatest_le _,
     Nat.findGreatest_spec (P := fun k => 2 * S (a.take k) ≤ S a) h1 hP1,
     fun m hm hml => Nat.findGreatest_is_greatest
       (P := fun k => 2 * S (a.take k) ≤ S a) hm hml⟩
  have hklt : k < a.length := by lia
  refine ⟨k, hk1, hklt, hPk, ?_⟩
  by_cases hcase : k = a.length - 1
  · -- The suffix consists of the last entry alone, which is at most `S a / 2`.
    rw [hcase, List.drop_length_sub_one hne, S_singleton]
    exact two_mul_getLast_le_S a ha hne
  · -- The next longer prefix `take (k+1) a` violates the bound; the overlap identity
    -- `S a = S (take (k+1) a) + S (drop k a)` then gives the claim for the suffix.
    have hkn : k + 1 ≤ a.length - 1 := by lia
    have hnot : ¬ 2 * S (a.take (k + 1)) ≤ S a := hmax (k + 1) (by lia) hkn
    have hp : a.take k ≠ [] := by
      rw [ne_eq, List.take_eq_nil_iff]
      rintro (h | h)
      · lia
      · exact absurd h hne
    have hq : a.drop (k + 1) ≠ [] := by
      rw [ne_eq, List.drop_eq_nil_iff]
      lia
    have hid : S a = S (a.take (k + 1)) + S (a.drop k) := by
      conv_lhs => rw [← List.take_append_drop k a]
      rw [List.drop_eq_getElem_cons hklt, S_append _ _ _ hp hq,
        List.take_append_getElem hklt]
    lia

/-- `Reduces a m` means that the row `a` can be reduced to the single number `m` by a
sequence of legal moves.  A derivation is a full binary tree whose leaves are the
entries of `a` and whose internal nodes are powers of two larger than their children;
conversely any play of the game produces such a tree (the last move combines the
reductions of two complementary blocks), so `Reduces a m` holds exactly when Annie
can achieve the final number `m`. -/
inductive Reduces : List ℕ → ℕ → Prop
  | base (x : ℕ) : Reduces [x] x
  | append (u v : List ℕ) (x y z : ℕ) (hu : Reduces u x) (hv : Reduces v y)
      (hz : IsPow2 z) (hx : x < z) (hy : y < z) : Reduces (u ++ v) z

/-- A number reachable from a row of powers of two is again a power of two. -/
theorem reduces_isPow2 {l : List ℕ} {m : ℕ} (h : Reduces l m)
    (hp : ∀ x ∈ l, IsPow2 x) : IsPow2 m := by
  induction h with
  | base x => exact hp x (List.mem_singleton_self x)
  | append u v x y z hu hv hz hx hy ihu ihv => exact hz

/-- The main induction: every nonempty row of powers of two can be reduced to a
single number which is at most `S` of the row. -/
theorem exists_reduces_le :
    ∀ n : ℕ, ∀ a : List ℕ, a.length = n → a ≠ [] → (∀ x ∈ a, IsPow2 x) →
      ∃ m, Reduces a m ∧ m ≤ S a := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a hn ha hp
    rcases a with _ | ⟨x, l⟩
    · exact (ha rfl).elim
    · rcases l with _ | ⟨y, rest⟩
      · exact ⟨x, Reduces.base x, le_of_eq (S_singleton x).symm⟩
      · -- Split the row, reduce both halves inductively, and combine the results.
        have hlen : 2 ≤ (x :: y :: rest).length := by simp
        obtain ⟨k, hk1, hkn, htk, hdk⟩ := exists_split (x :: y :: rest) hlen
        have hkn' : k < n := by lia
        have hne_take : (x :: y :: rest).take k ≠ [] := by
          rw [ne_eq, List.take_eq_nil_iff]
          rintro (h | h)
          · lia
          · simp at h
        have hlen_take : ((x :: y :: rest).take k).length = k := by
          rw [List.length_take]; lia
        have hp_take : ∀ m ∈ (x :: y :: rest).take k, IsPow2 m :=
          fun m hm => hp m (List.mem_of_mem_take hm)
        obtain ⟨m₁, hm₁r, hm₁s⟩ := ih k hkn' _ hlen_take hne_take hp_take
        have hlt_drop : n - k < n := by lia
        have hlen_drop : ((x :: y :: rest).drop k).length = n - k := by
          rw [List.length_drop]; lia
        have hne_drop : (x :: y :: rest).drop k ≠ [] := by
          rw [ne_eq, List.drop_eq_nil_iff]; lia
        have hp_drop : ∀ m ∈ (x :: y :: rest).drop k, IsPow2 m :=
          fun m hm => hp m (List.mem_of_mem_drop hm)
        obtain ⟨m₂, hm₂r, hm₂s⟩ := ih (n - k) hlt_drop _ hlen_drop hne_drop hp_drop
        obtain ⟨p, rfl⟩ := reduces_isPow2 hm₁r hp_take
        obtain ⟨q, rfl⟩ := reduces_isPow2 hm₂r hp_drop
        refine ⟨2 ^ (max p q + 1), ?_, ?_⟩
        · have hlt1 : (2 : ℕ) ^ p < 2 ^ (max p q + 1) :=
            pow_lt_pow_right₀ (by norm_num) (by lia)
          have hlt2 : (2 : ℕ) ^ q < 2 ^ (max p q + 1) :=
            pow_lt_pow_right₀ (by norm_num) (by lia)
          have hr := Reduces.append _ _ _ _ _ hm₁r hm₂r ⟨max p q + 1, rfl⟩ hlt1 hlt2
          rwa [List.take_append_drop] at hr
        · have h2p : 2 * (2 : ℕ) ^ p ≤ S (x :: y :: rest) := by lia
          have h2q : 2 * (2 : ℕ) ^ q ≤ S (x :: y :: rest) := by lia
          have hmax : max ((2 : ℕ) ^ p) (2 ^ q) = 2 ^ max p q := by
            rcases le_total p q with h | h
            · rw [max_eq_right h, max_eq_right (pow_le_pow_right₀ (by norm_num) h)]
            · rw [max_eq_left h, max_eq_left (pow_le_pow_right₀ (by norm_num) h)]
          have hz : (2 : ℕ) ^ (max p q + 1) = 2 * 2 ^ max p q := by rw [pow_succ]; ring
          rw [hz, ← hmax]
          lia

/-- Moves can also be performed with an additional row appended on the right. -/
theorem Move.append_right {a b : List ℕ} (h : Move a b) (r : List ℕ) :
    Move (a ++ r) (b ++ r) := by
  obtain ⟨l, r', x, y, z, hz, hx, hy⟩ := h
  rw [show (l ++ x :: y :: r') ++ r = l ++ x :: y :: (r' ++ r) by simp,
    show (l ++ z :: r') ++ r = l ++ z :: (r' ++ r) by simp]
  exact Move.mk l (r' ++ r) x y z hz hx hy

/-- Moves can also be performed with an additional row appended on the left. -/
theorem Move.append_left (l : List ℕ) {a b : List ℕ} (h : Move a b) :
    Move (l ++ a) (l ++ b) := by
  obtain ⟨l', r, x, y, z, hz, hx, hy⟩ := h
  rw [show l ++ (l' ++ x :: y :: r) = (l ++ l') ++ x :: y :: r by simp,
    show l ++ (l' ++ z :: r) = (l ++ l') ++ z :: r by simp]
  exact Move.mk (l ++ l') r x y z hz hx hy

/-- Pushing a chain of moves through a context map. -/
theorem reflTransGen_map (f : List ℕ → List ℕ)
    (hf : ∀ {s t : List ℕ}, Move s t → Move (f s) (f t)) {a b : List ℕ}
    (h : Relation.ReflTransGen Move a b) : Relation.ReflTransGen Move (f a) (f b) := by
  induction h with
  | refl => exact .refl
  | tail _ hbc ih => exact ih.trans (.single (hf hbc))

/-- A `Reduces` derivation yields an actual sequence of legal moves: reduce the left
block, then the right block, then combine the two remaining adjacent numbers. -/
theorem reduces_moves {a : List ℕ} {m : ℕ} (h : Reduces a m) :
    Relation.ReflTransGen Move a [m] := by
  induction h with
  | base x => exact .refl
  | append u v x y z hu hv hz hx hy ihu ihv =>
      have step1 : Relation.ReflTransGen Move (u ++ v) (x :: v) :=
        reflTransGen_map (· ++ v) (fun hs => Move.append_right hs v) ihu
      have step2 : Relation.ReflTransGen Move (x :: v) [x, y] :=
        reflTransGen_map (x :: ·) (fun hs => Move.append_left [x] hs) ihv
      have step3 : Relation.ReflTransGen Move [x, y] [z] :=
        .single (Move.mk [] [] x y z hz hx hy)
      exact step1.trans (step2.trans step3)

/-- Powers of two are positive. -/
theorem IsPow2.pos {x : ℕ} (h : IsPow2 x) : 0 < x := by
  obtain ⟨k, rfl⟩ := h
  positivity

snip end

/-- The answer is **yes**: from any starting row of powers of two, Annie can always
reach a single number which is less than four times the sum of the starting row. -/
problem usa2026_p2 (a : List ℕ) (ha : a ≠ []) (hp : ∀ x ∈ a, IsPow2 x) :
    ∃ m, Relation.ReflTransGen Move a [m] ∧ m < 4 * a.sum := by
  obtain ⟨m, hm, hle⟩ := exists_reduces_le a.length a rfl ha hp
  have hpos : ∀ x ∈ a, 0 < x := fun x hx => (hp x hx).pos
  exact ⟨m, reduces_moves hm, lt_of_le_of_lt hle (S_lt_four_mul_sum a ha hpos)⟩

end Usa2026P2
