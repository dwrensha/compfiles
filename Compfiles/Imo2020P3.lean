/-
Copyright (c) 2025 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Kimi K3
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Nat.SuccPred
public import Mathlib.Tactic.Ring
public import ProblemExtraction

@[expose] public section

problem_file {
  tags := [.Combinatorics]
}

/-!
# International Mathematical Olympiad 2020, Problem 3

There are 4n pebbles of weights 1,2,3,...,4n. Each pebble is colored
in one of n colors and there are four pebbles of each color. Show
that we can arrange the pebbles into two piles such that the total
weights of both piles are the same, and each pile contains two
pebbles of each color.
-/

namespace Imo2020P3

open scoped Finset

snip begin

section TwoFactor

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- In a pseudograph with endpoint functions `a b : E → V`, the edge `e` connects `v` and `w`. -/
def conn (a b : E → V) (e : E) (v w : V) : Prop :=
  (a e = v ∧ b e = w) ∨ (a e = w ∧ b e = v)

/-- A walk in a pseudograph: the vertex list has one more entry than the edge list. -/
inductive IsWalk (a b : E → V) : List V → List E → Prop
  | nil (v : V) : IsWalk a b [v] []
  | cons {v w : V} {e : E} {vs : List V} {es : List E} :
      conn a b e v w → IsWalk a b (w :: vs) es → IsWalk a b (v :: w :: vs) (e :: es)

/-- The multiplicity of vertex `x` as an endpoint of edge `e`. -/
def mult (a b : E → V) (e : E) (x : V) : ℕ :=
  (if a e = x then 1 else 0) + (if b e = x then 1 else 0)

lemma mult_conn {a b : E → V} {e : E} {v w : V} (h : conn a b e v w) (x : V) :
    mult a b e x = (if v = x then 1 else 0) + (if w = x then 1 else 0) := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp [mult]
  · simp [mult, add_comm]

/-- Total number of edge-slots of a list of edges at vertex `x`. -/
def slotCount (a b : E → V) (es : List E) (x : V) : ℕ :=
  (es.map (fun e => mult a b e x)).sum

lemma IsWalk.vs_ne_nil {a b : E → V} {vs : List V} {es : List E} (h : IsWalk a b vs es) :
    vs ≠ [] := by
  cases h <;> simp

/-- In any walk, the slot count at `x` equals twice the number of
interior occurrences of `x`, plus the endpoint contributions. -/
lemma slotCount_eq {a b : E → V} {vs : List V} {es : List E} (h : IsWalk a b vs es)
    (hne : es ≠ []) (x : V) :
    slotCount a b es x =
      2 * ((vs.drop 1).dropLast.count x) +
        (if vs.head? = some x then 1 else 0) + (if vs.getLast? = some x then 1 else 0) := by
  induction h with
  | nil v => exact absurd rfl hne
  | @cons v w e vs es hconn hw ih =>
    cases hw with
    | nil =>
      have hc0 : slotCount a b [e] x = mult a b e x := rfl
      have hd1 : ([v, w] : List V).drop 1 = [w] := rfl
      have hd2 : ([w] : List V).dropLast = [] := rfl
      rw [hc0, mult_conn hconn x, hd1, hd2, List.count_nil, List.head?_cons,
        List.getLast?_cons_cons, List.getLast?_singleton]
      simp only [beq_iff_eq, Option.some.injEq]
      split_ifs <;> omega
    | @cons w u e' vs' es' hconn' hw' =>
      have ih' := ih (by simp)
      have hd : (w :: u :: vs').dropLast = w :: (u :: vs').dropLast := rfl
      have hc0 : slotCount a b (e :: e' :: es') x =
        mult a b e x + slotCount a b (e' :: es') x := rfl
      have hd1 : (v :: w :: u :: vs').drop 1 = w :: u :: vs' := rfl
      have hd' : (w :: u :: vs').drop 1 = u :: vs' := rfl
      rw [hc0, ih', mult_conn hconn x, hd1, hd', hd]
      simp only [List.count_cons, List.head?_cons, List.getLast?_cons_cons, beq_iff_eq,
        Option.some.injEq]
      split_ifs <;> simp_all <;> omega

/-- In a closed walk, the slot count at `x` is twice the number of occurrences of `x`. -/
lemma slotCount_closed {a b : E → V} {vs : List V} {es : List E} (h : IsWalk a b vs es)
    (hc : vs.head? = vs.getLast?) (x : V) :
    slotCount a b es x = 2 * vs.dropLast.count x := by
  by_cases hne : es = []
  · subst hne
    cases h with
    | nil v => simp [slotCount]
  · rw [slotCount_eq h hne x]
    cases h with
    | nil v => simp at hne
    | @cons v w e vs' es' hconn hw =>
      cases hw with
      | nil =>
        have hd1 : ([v, w] : List V).drop 1 = [w] := rfl
        have hd2 : ([w] : List V).dropLast = [] := rfl
        have hd3 : ([v, w] : List V).dropLast = [v] := rfl
        simp only [List.head?_cons, List.getLast?_cons_cons, List.getLast?_singleton,
          Option.some.injEq] at hc
        subst hc
        rw [hd1, hd2, List.count_nil, List.head?_cons, List.getLast?_cons_cons,
          List.getLast?_singleton, hd3, List.count_cons, List.count_nil]
        simp only [beq_iff_eq, Option.some.injEq]
        split_ifs <;> simp_all <;> omega
      | @cons w u e' vs'' es'' hconn' hw' =>
        have hd : (v :: w :: u :: vs'').dropLast = v :: (w :: u :: vs'').dropLast := rfl
        have hd1 : (v :: w :: u :: vs'').drop 1 = w :: u :: vs'' := rfl
        have hd2 : (w :: u :: vs'').dropLast = w :: (u :: vs'').dropLast := rfl
        rw [hd, hd1, hd2, ← hc, List.head?_cons]
        simp only [List.count_cons, beq_iff_eq, Option.some.injEq]
        split_ifs <;> simp_all <;> omega

/-- The alternating slot count along a walk, red at positions with parity `s`. -/
lemma altCount_eq {a b : E → V} {vs : List V} {es : List E} (h : IsWalk a b vs es)
    (hne : es ≠ []) {s : ℕ} (hs : s ≤ 1) (x : V) :
    ((es.mapIdx fun i e => if s = i % 2 then mult a b e x else 0).sum) =
      ((vs.drop 1).dropLast.count x) +
        (if vs.head? = some x ∧ s = 0 then 1 else 0) +
        (if vs.getLast? = some x ∧ s = (es.length - 1) % 2 then 1 else 0) := by
  induction h generalizing s with
  | nil v => exact absurd rfl hne
  | @cons v w e vs es hconn hw ih =>
    cases hw with
    | nil =>
      rw [List.mapIdx_cons, List.mapIdx_nil, List.sum_cons, List.sum_nil, mult_conn hconn x]
      simp only [List.drop_succ_cons, List.drop_zero, List.dropLast_singleton, List.count_nil,
        List.head?_cons, List.getLast?_cons_cons, List.getLast?_singleton, List.length_cons,
        List.length_nil, Nat.reduceSub, Nat.reduceMod, Nat.zero_mod, zero_add, beq_iff_eq,
        Option.some.injEq, eq_self_iff_true, and_true, and_false]
      by_cases hv : v = x <;> by_cases hw : w = x <;> by_cases hs0 : s = 0 <;>
        simp_all <;> omega
    | @cons w u e' vs' es' hconn' hw' =>
      have ih' := ih (by simp) (show 1 - s ≤ 1 by omega)
      have hd : (w :: u :: vs').dropLast = w :: (u :: vs').dropLast := rfl
      have hpar : ∀ i : ℕ, (s = (i + 1) % 2) ↔ (1 - s = i % 2) := by
        intro i; omega
      have hlast : ∀ m : ℕ, (s = (m + 1) % 2) ↔ (1 - s = m % 2) := by
        intro m; omega
      rw [List.mapIdx_cons, List.sum_cons, mult_conn hconn x]
      simp_rw [hpar]
      rw [ih']
      simp only [List.drop_succ_cons, List.drop_zero, hd, List.count_cons, List.head?_cons,
        List.getLast?_cons_cons, List.length_cons, Nat.add_sub_cancel, Nat.zero_mod, zero_add,
        beq_iff_eq, Option.some.injEq, eq_self_iff_true, and_true, and_false]
      by_cases hv : v = x <;> by_cases hw : w = x <;> by_cases hs0 : s = 0 <;>
        simp_all <;> omega

lemma mapIdx_congr {α : Type*} (l : List α) (f g : ℕ → α → ℕ) (h : ∀ i, f i = g i) :
    l.mapIdx f = l.mapIdx g := by
  induction l generalizing f g with
  | nil => rfl
  | cons a l ih =>
    rw [List.mapIdx_cons, List.mapIdx_cons, h 0]
    congr 1
    exact ih _ _ (fun i => h (i + 1))

/-- In a closed walk of even length, the alternating slot count at `x` equals the number of
occurrences of `x` among the positions. -/
lemma altCount_closed {a b : E → V} {vs : List V} {es : List E} (h : IsWalk a b vs es)
    (hc : vs.head? = vs.getLast?) (hL : Even es.length) (x : V) :
    ((es.mapIdx fun i e => if i % 2 = 0 then mult a b e x else 0).sum) =
      vs.dropLast.count x := by
  by_cases hne : es = []
  · subst hne
    cases h with
    | nil v => simp
  · obtain ⟨k, hk⟩ := hL
    have hlen : 0 < es.length := Nat.pos_of_ne_zero (fun hh => hne
      (List.eq_nil_of_length_eq_zero hh))
    have hm : ∃ m, es.length = 2 * m + 2 := ⟨k - 1, by omega⟩
    obtain ⟨m, hm⟩ := hm
    have glue2 : (es.mapIdx fun i e => if i % 2 = 0 then mult a b e x else 0) =
        es.mapIdx fun i e => if 0 = i % 2 then mult a b e x else 0 :=
      mapIdx_congr es _ _ fun i => funext fun e => if_congr (by omega) rfl rfl
    rw [glue2, altCount_eq h hne (by omega : 0 ≤ 1) x]
    have hmod : (es.length - 1) % 2 = 1 := by rw [hm]; omega
    have hlast : (0 = (es.length - 1) % 2) ↔ False := by rw [hmod]; simp
    simp only [hlast, and_false, if_false, add_zero]
    cases h with
    | nil v => simp at hne
    | @cons v w e vs es hconn hw =>
      have hd : (v :: w :: vs).dropLast = v :: (w :: vs).dropLast := by
        cases hw with
        | nil => rfl
        | cons _ _ => rfl
      simp only [hd, List.count_cons, List.drop_succ_cons, List.drop_zero, List.head?_cons,
        eq_self_iff_true, and_true, beq_iff_eq, Option.some.injEq]
      try (by_cases hv : v = x <;> simp_all <;> omega)

lemma IsWalk.length {a b : E → V} {vs : List V} {es : List E} (h : IsWalk a b vs es) :
    vs.length = es.length + 1 := by
  induction h with
  | nil v => rfl
  | cons _ _ ih => simp [List.length_cons, ih]

lemma IsWalk.append {a b : E → V} {vs ws : List V} {es fs : List E}
    (h₁ : IsWalk a b vs es) (h₂ : IsWalk a b ws fs)
    (h : vs.getLast? = ws.head?) : IsWalk a b (vs ++ ws.tail) (es ++ fs) := by
  induction h₁ with
  | nil v =>
    cases ws with
    | nil => simp at h
    | cons w ws' =>
      simp only [List.getLast?_singleton, List.head?_cons, Option.some.injEq] at h
      subst h
      simpa using h₂
  | @cons v w e vs' es' hconn hw ih =>
    have h' : (w :: vs').getLast? = ws.head? := by
      have hh : (v :: w :: vs').getLast? = (w :: vs').getLast? := by
        cases vs' with
        | nil => rfl
        | cons a l => rfl
      rw [← hh]; exact h
    exact IsWalk.cons hconn (ih h')

lemma IsWalk.take {a b : E → V} {vs : List V} {es : List E} (h : IsWalk a b vs es) (k : ℕ) :
    IsWalk a b (vs.take (k + 1)) (es.take k) := by
  induction h generalizing k with
  | nil v =>
    cases k with
    | zero => exact IsWalk.nil v
    | succ k =>
      rw [List.take_of_length_le (by simp), List.take_nil]
      exact IsWalk.nil v
  | @cons v w e vs' es' hconn hw ih =>
    cases k with
    | zero =>
      rw [List.take_one, List.take_zero]
      exact IsWalk.nil v
    | succ k =>
      rw [List.take_succ_cons, List.take_succ_cons]
      exact IsWalk.cons hconn (ih k)

lemma IsWalk.drop {a b : E → V} {vs : List V} {es : List E} (h : IsWalk a b vs es) (k : ℕ)
    (hk : k ≤ es.length) : IsWalk a b (vs.drop k) (es.drop k) := by
  induction h generalizing k with
  | nil v =>
    have hk0 : k = 0 := by simpa using hk
    subst hk0
    exact IsWalk.nil v
  | @cons v w e vs' es' hconn hw ih =>
    cases k with
    | zero => exact IsWalk.cons hconn hw
    | succ k =>
      rw [List.drop_succ_cons, List.drop_succ_cons]
      exact ih k (by simpa using hk)

/-- A closed trail in a pseudograph: a closed walk with no repeated edges. -/
structure CTrail (a b : E → V) where
  vs : List V
  es : List E
  nodup : es.Nodup
  walk : IsWalk a b vs es
  closed : vs.head? = vs.getLast?

lemma getLast?_drop_of_lt {l : List V} {k : ℕ} (h : k < l.length) :
    (l.drop k).getLast? = l.getLast? := by
  have h1 : l.drop k ≠ [] := by
    rw [List.ne_nil_iff_length_pos, List.length_drop]; omega
  rw [List.getLast?_eq_getLast_of_ne_nil h1, List.getLast?_eq_getLast_of_ne_nil (by
    rw [List.ne_nil_iff_length_pos]; omega)]
  congr 1
  exact List.getLast_drop h1

lemma head?_take_of_pos {l : List V} {k : ℕ} (h : 0 < k) : (l.take k).head? = l.head? := by
  cases l with
  | nil => simp
  | cons a t =>
    cases k with
    | zero => omega
    | succ k => simp

lemma getLast?_take_succ {l : List V} {k : ℕ} (h : k + 1 ≤ l.length) :
    (l.take (k + 1)).getLast? = l[k]? := by
  have h1 : l.take (k + 1) ≠ [] := by
    rw [List.ne_nil_iff_length_pos, List.length_take]; omega
  rw [List.getLast?_eq_getLast_of_ne_nil h1]
  have h2 : (l.take (k + 1)).getLast h1 = l[k] := by
    rw [List.getLast_eq_getElem h1, List.getElem_take]
    · congr 1
      rw [List.length_take]; omega
  rw [h2]
  exact (List.getElem?_eq_getElem (by omega)).symm

lemma head?_drop_of_lt {l : List V} {k : ℕ} (h : k < l.length) : (l.drop k).head? = l[k]? := by
  have h1 : l.drop k ≠ [] := by
    rw [List.ne_nil_iff_length_pos, List.length_drop]; omega
  rw [List.head?_eq_head h1, List.head_drop, List.getElem?_eq_getElem h]

lemma getLast?_tail_of_ne {l : List V} (h : l.tail ≠ []) : l.tail.getLast? = l.getLast? := by
  cases l with
  | nil => simp at h
  | cons a t =>
    cases t with
    | nil => simp at h
    | cons b u => rfl

/-- Rotate a closed trail at position `k` (an index of a vertex occurrence). -/
def CTrail.rotate {a b : E → V} (T : CTrail a b) (k : ℕ) (hk : k < T.es.length) :
    CTrail a b where
  vs := T.vs.drop k ++ (T.vs.take (k + 1)).tail
  es := T.es.rotate k
  nodup := List.nodup_rotate.mpr T.nodup
  walk := by
    have hlen : T.vs.length = T.es.length + 1 := T.walk.length
    have hk' : k ≤ T.es.length := le_of_lt hk
    have h1 : (T.vs.drop k).getLast? = (T.vs.take (k + 1)).head? := by
      rw [getLast?_drop_of_lt (by omega), head?_take_of_pos (by omega), T.closed]
    have happ := (T.walk.drop k hk').append (T.walk.take k) h1
    rw [List.rotate_eq_drop_append_take hk']
    exact happ
  closed := by
    have hlen : T.vs.length = T.es.length + 1 := T.walk.length
    have hkV : k < T.vs.length := by omega
    by_cases ht : (T.vs.take (k + 1)).tail = []
    · have hk0 : k = 0 := by
        have hh := congrArg List.length ht
        rw [List.length_tail, List.length_take, Nat.min_eq_left (by omega),
          List.length_nil] at hh
        omega
      subst hk0
      have ht1 : (T.vs.take 1).tail = [] := by
        rw [List.take_one]
        cases T.vs.head? with
        | none => rfl
        | some v => rfl
      rw [List.drop_zero, ht1, List.append_nil]
      exact T.closed
    · have hne1 : T.vs.drop k ≠ [] := by
        rw [List.ne_nil_iff_length_pos, List.length_drop]; omega
      have hne2 : (T.vs.take (k + 1)).tail ≠ [] := ht
      rw [List.head?_append_of_ne_nil _ hne1, head?_drop_of_lt hkV,
        List.getLast?_append_of_ne_nil _ hne2]
      rw [getLast?_tail_of_ne hne2, getLast?_take_succ (by omega)]

lemma list_sum_eq_toFinset_sum {α : Type*} [DecidableEq α] {l : List α} (hn : l.Nodup)
    {f : α → ℕ} : (l.map f).sum = ∑ e ∈ l.toFinset, f e := by
  rw [Finset.sum_eq_multiset_sum, List.toFinset_val, List.dedup_eq_self.mpr hn,
    Multiset.map_coe, Multiset.sum_coe]

/-- A maximal walk from `v` using only edges of `U`, with distinct edges. -/
lemma exists_max_walk (a b : E → V) (U : Finset E) (v : V) :
    ∃ vs es y, IsWalk a b vs es ∧ vs.head? = some v ∧ vs.getLast? = some y ∧ es.Nodup ∧
      (∀ e ∈ es, e ∈ U) ∧ (∀ e ∈ U, ∀ w, conn a b e y w → e ∈ es) := by
  classical
  set S : Finset ℕ := (Finset.range (U.card + 1)).filter fun L =>
    ∃ vs es, IsWalk a b vs es ∧ vs.head? = some v ∧ es.Nodup ∧ (∀ e ∈ es, e ∈ U) ∧
      es.length = L with hS
  have h0 : 0 ∈ S := by
    rw [hS, Finset.mem_filter]
    refine ⟨by simp, [v], [], IsWalk.nil v, rfl, List.nodup_nil, ?_, rfl⟩
    intro e he
    simp at he
  obtain ⟨m, hmS, hmax⟩ : ∃ m ∈ S, ∀ L ∈ S, L ≤ m :=
    ⟨S.max' ⟨0, h0⟩, S.max'_mem _, fun L hL => S.le_max' L hL⟩
  rw [hS, Finset.mem_filter] at hmS
  obtain ⟨_, vs, es, hwalk, hhead, hnodup, hsub, hlen⟩ := hmS
  have hne : vs ≠ [] := hwalk.vs_ne_nil
  refine ⟨vs, es, vs.getLast hne, hwalk, hhead, ?_, hnodup, hsub, ?_⟩
  · rw [List.getLast?_eq_getLast_of_ne_nil hne]
  · intro e heU w hconn
    by_contra he
    have happ : IsWalk a b (vs ++ [w]) (es ++ [e]) := by
      have hs : IsWalk a b [vs.getLast hne, w] [e] := IsWalk.cons hconn (IsWalk.nil w)
      have hGL : vs.getLast? = [vs.getLast hne, w].head? := by
        rw [List.getLast?_eq_getLast_of_ne_nil hne]; rfl
      simpa using hwalk.append hs hGL
    have hnodup' : (es ++ [e]).Nodup := by
      rw [List.nodup_append]
      refine ⟨hnodup, by simp, fun a ha b hb => ?_⟩
      rw [List.mem_singleton] at hb
      subst hb
      intro hab
      exact he (hab ▸ ha)
    have hbound : es.length + 1 ≤ U.card := by
      have h1 : (es ++ [e]).toFinset.card ≤ U.card :=
        Finset.card_le_card fun x hx => by
          rw [List.mem_toFinset, List.mem_append, List.mem_singleton] at hx
          rcases hx with hx | hx
          · exact hsub x hx
          · rw [hx]; exact heU
      rwa [List.toFinset_card_of_nodup hnodup', List.length_append, List.length_singleton] at h1
    have hmem : es.length + 1 ∈ S := by
      rw [hS, Finset.mem_filter]
      refine ⟨by rw [Finset.mem_range]; omega, vs ++ [w], es ++ [e], happ, ?_, hnodup', ?_, by simp⟩
      · rw [List.head?_append_of_ne_nil _ hne, hhead]
      · intro x hx
        rw [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | hx
        · exact hsub x hx
        · rw [hx]; exact heU
    have := hmax _ hmem
    omega

/-- Any edge of `U` lies in a closed trail within `U`, provided all `U`-degrees are even. -/
lemma exists_closed_trail (a b : E → V) (U : Finset E)
    (hU : ∀ x, Even (∑ e ∈ U, mult a b e x)) (e₀ : E) (he₀ : e₀ ∈ U) :
    ∃ T : CTrail a b, (∀ e ∈ T.es, e ∈ U) ∧ T.es ≠ [] := by
  obtain ⟨vs, es, y, hwalk, hhead, hlast, hnodup, hsub, hmax⟩ := exists_max_walk a b U (a e₀)
  have hne : es ≠ [] := by
    intro hnil
    subst hnil
    cases hwalk with
    | nil v =>
      simp only [List.head?_cons, Option.some.injEq] at hhead
      simp only [List.getLast?_singleton, Option.some.injEq] at hlast
      subst hhead
      subst hlast
      have h1 := hmax e₀ he₀ (b e₀) (Or.inl ⟨rfl, rfl⟩)
      simp at h1
  have hclose : y = a e₀ := by
    have hslot : slotCount a b es y = ∑ e ∈ U, mult a b e y := by
      rw [slotCount, list_sum_eq_toFinset_sum hnodup]
      apply Finset.sum_subset
      · intro e he
        exact hsub e (List.mem_toFinset.mp he)
      · intro e heU hnin
        rw [List.mem_toFinset] at hnin
        by_contra hm
        rw [mult] at hm
        have hconn : conn a b e y (if a e = y then b e else a e) := by
          by_cases hay : a e = y
          · rw [if_pos hay]; exact Or.inl ⟨hay, rfl⟩
          · rw [if_neg hay]
            have hby : b e = y := by
              by_contra hb
              simp [hay, hb] at hm
            exact Or.inr ⟨rfl, hby⟩
        exact hnin (hmax e heU _ hconn)
    have hsc := slotCount_eq hwalk hne y
    rw [hhead, hlast, hslot] at hsc
    obtain ⟨k, hk⟩ := hU y
    by_contra hy
    have hay : a e₀ ≠ y := fun h => hy h.symm
    simp [hay] at hsc
    omega
  exact ⟨⟨vs, es, hnodup, hwalk, by rw [hhead, hlast, hclose]⟩, hsub, hne⟩

/-- Decompose an even-degree edge set into edge-disjoint closed trails. -/
lemma decompose (a b : E → V) (U : Finset E) (hU : ∀ x, Even (∑ e ∈ U, mult a b e x)) :
    ∃ F : List (CTrail a b),
      (∀ T ∈ F, ∀ e ∈ T.es, e ∈ U) ∧
      (∀ T ∈ F, T.es ≠ []) ∧
      (∀ e ∈ U, ∃ T ∈ F, e ∈ T.es) ∧
      F.Pairwise (fun T₁ T₂ => Disjoint T₁.es.toFinset T₂.es.toFinset) := by
  induction U using Finset.strongInduction with
  | _ U ih =>
    by_cases hUe : U = ∅
    · subst hUe
      exact ⟨[], by simp, by simp, by simp, by simp⟩
    · obtain ⟨e₀, he₀⟩ := Finset.nonempty_of_ne_empty hUe
      obtain ⟨T, hTU, hTne⟩ := exists_closed_trail a b U hU e₀ he₀
      have hsU : T.es.toFinset ⊆ U := fun e he => hTU e (List.mem_toFinset.mp he)
      have hU' : ∀ x, Even (∑ e ∈ U \ T.es.toFinset, mult a b e x) := by
        intro x
        have hsub : ∑ e ∈ U \ T.es.toFinset, mult a b e x =
            (∑ e ∈ U, mult a b e x) - slotCount a b T.es x := by
          rw [← Finset.sum_sdiff hsU, slotCount, list_sum_eq_toFinset_sum T.nodup,
            Nat.add_sub_cancel]
        have hle : slotCount a b T.es x ≤ ∑ e ∈ U, mult a b e x := by
          rw [slotCount, list_sum_eq_toFinset_sum T.nodup]
          exact Finset.sum_le_sum_of_subset hsU
        obtain ⟨k, hk⟩ := hU x
        obtain ⟨k2, hk2⟩ : Even (slotCount a b T.es x) := by
          rw [slotCount_closed T.walk T.closed x]
          exact ⟨T.vs.dropLast.count x, by omega⟩
        rw [hsub, hk, hk2]
        exact ⟨k - k2, by omega⟩
      obtain ⟨e1, he1⟩ := List.exists_mem_of_ne_nil T.es hTne
      have hss : U \ T.es.toFinset ⊂ U := by
        rw [Finset.ssubset_iff_subset_ne]
        refine ⟨Finset.sdiff_subset, fun hcon => ?_⟩
        have h1 : 0 < T.es.toFinset.card := Finset.card_pos.mpr ⟨e1, List.mem_toFinset.mpr he1⟩
        have h2 : (U \ T.es.toFinset).card = U.card := by rw [hcon]
        rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsU] at h2
        have hle : T.es.toFinset.card ≤ U.card := Finset.card_le_card hsU
        omega
      obtain ⟨F', hF'U, hF'ne, hF'cov, hF'dj⟩ := ih (U \ T.es.toFinset) hss hU'
      refine ⟨T :: F', ?_, ?_, ?_, ?_⟩
      · intro T' hT' e he
        rw [List.mem_cons] at hT'
        rcases hT' with rfl | hT'
        · exact hTU e he
        · have := hF'U T' hT' e he
          exact Finset.mem_sdiff.mp this |>.1
      · intro T' hT'
        rw [List.mem_cons] at hT'
        rcases hT' with rfl | hT'
        · exact hTne
        · exact hF'ne T' hT'
      · intro e he
        by_cases heT : e ∈ T.es.toFinset
        · exact ⟨T, by simp, List.mem_toFinset.mp heT⟩
        · have heU' : e ∈ U \ T.es.toFinset := Finset.mem_sdiff.mpr ⟨he, heT⟩
          obtain ⟨T', hT', heT'⟩ := hF'cov e heU'
          exact ⟨T', List.mem_cons_of_mem T hT', heT'⟩
      · rw [List.pairwise_cons]
        refine ⟨?_, hF'dj⟩
        intro T' hT'
        rw [Finset.disjoint_left]
        intro e he heT'
        have h1 := hF'U T' hT' e (List.mem_toFinset.mp heT')
        exact Finset.mem_sdiff.mp h1 |>.2 he

lemma CTrail.rotate_head? {a b : E → V} {v : V} (T : CTrail a b) (k : ℕ) (hk : k < T.es.length)
    (hv : T.vs[k]? = some v) : (T.rotate k hk).vs.head? = some v := by
  have hlen : T.vs.length = T.es.length + 1 := T.walk.length
  show (T.vs.drop k ++ (T.vs.take (k + 1)).tail).head? = some v
  rw [List.head?_append_of_ne_nil _ (by
    rw [List.ne_nil_iff_length_pos, List.length_drop]; omega), head?_drop_of_lt (by omega)]
  exact hv

lemma CTrail.rotate_es_toFinset {a b : E → V} (T : CTrail a b) (k : ℕ) (hk : k < T.es.length) :
    (T.rotate k hk).es.toFinset = T.es.toFinset := by
  show (T.es.rotate k).toFinset = T.es.toFinset
  ext e
  simp [List.mem_toFinset, List.mem_rotate]

/-- Append two closed trails that both start at the same vertex `v`. -/
def CTrail.append {a b : E → V} {v : V} (T₁ T₂ : CTrail a b)
    (h₁ : T₁.vs.head? = some v) (h₂ : T₂.vs.head? = some v)
    (hdj : Disjoint T₁.es.toFinset T₂.es.toFinset) : CTrail a b where
  vs := T₁.vs ++ T₂.vs.tail
  es := T₁.es ++ T₂.es
  nodup := by
    rw [List.nodup_append]
    refine ⟨T₁.nodup, T₂.nodup, fun a ha b hb hab => ?_⟩
    exact Finset.disjoint_left.mp hdj (List.mem_toFinset.mpr ha) (hab ▸ List.mem_toFinset.mpr hb)
  walk := T₁.walk.append T₂.walk (by rw [← T₁.closed, h₁, h₂])
  closed := by
    rw [List.head?_append_of_ne_nil _ T₁.walk.vs_ne_nil, h₁]
    by_cases ht : T₂.vs.tail = []
    · rw [ht, List.append_nil, ← T₁.closed, h₁]
    · rw [List.getLast?_append_of_ne_nil _ ht]
      have hgl : T₂.vs.tail.getLast? = T₂.vs.getLast? := by
        cases htl : T₂.vs with
        | nil => exact absurd htl T₂.walk.vs_ne_nil
        | cons x t =>
          cases t with
          | nil => rw [htl] at ht; exact (ht rfl).elim
          | cons y u => rfl
      rw [hgl, ← T₂.closed, h₂]

lemma CTrail.exists_rotate_index {a b : E → V} (T : CTrail a b) (hne : T.es ≠ []) {v : V}
    (hv : v ∈ T.vs) : ∃ k < T.es.length, T.vs[k]? = some v := by
  obtain ⟨⟨k, hkL⟩, hkv⟩ := List.get_of_mem hv
  have hlen : T.vs.length = T.es.length + 1 := T.walk.length
  by_cases hk2 : k < T.es.length
  · refine ⟨k, hk2, ?_⟩
    rw [List.getElem?_eq_getElem (by omega : k < T.vs.length)]
    have hkv' : T.vs[k] = v := hkv
    rw [hkv']
  · have hk3 : k = T.es.length := by omega
    subst hk3
    refine ⟨0, Nat.pos_of_ne_zero (fun hh => hne (List.eq_nil_of_length_eq_zero hh)), ?_⟩
    have hgl : T.vs.getLast? = some v := by
      rw [List.getLast?_eq_getElem?]
      have hll : T.vs.length - 1 = T.es.length := by omega
      rw [hll, List.getElem?_eq_getElem (by omega)]
      have hkv' : T.vs[T.es.length] = v := hkv
      rw [hkv']
    rw [← T.closed] at hgl
    rw [List.head?_eq_getElem?] at hgl
    exact hgl

instance (a b : E → V) :
    Std.Symm (fun T₁ T₂ : CTrail a b => Disjoint T₁.es.toFinset T₂.es.toFinset) :=
  ⟨fun _ _ h => Disjoint.symm h⟩

lemma two_le_length {α : Type*} {l : List α} {a b : α} (ha : a ∈ l) (hb : b ∈ l)
    (hne : a ≠ b) : 2 ≤ l.length := by
  induction l generalizing a b with
  | nil => simp at ha
  | cons x l ih =>
    rw [List.length_cons]
    rw [List.mem_cons] at ha hb
    rcases ha with rfl | ha
    · rcases hb with rfl | hb
      · exact absurd rfl hne
      · have h1 : 0 < l.length := List.length_pos_of_mem hb
        omega
    · rcases hb with rfl | hb
      · have h1 : 0 < l.length := List.length_pos_of_mem ha
        omega
      · have h2 := ih ha hb hne
        omega

/-- Merge trails sharing vertices until the family is vertex-disjoint. -/
lemma merge_disjoint (a b : E → V) :
    ∀ n : ℕ, ∀ F : List (CTrail a b), F.length = n →
    (∀ e, ∃ T ∈ F, e ∈ T.es) →
    (∀ T ∈ F, T.es ≠ []) →
    F.Pairwise (fun T₁ T₂ => Disjoint T₁.es.toFinset T₂.es.toFinset) →
    ∃ F' : List (CTrail a b),
      (∀ e, ∃ T ∈ F', e ∈ T.es) ∧
      (∀ T ∈ F', T.es ≠ []) ∧
      F'.Pairwise (fun T₁ T₂ => Disjoint T₁.es.toFinset T₂.es.toFinset) ∧
      F'.Pairwise (fun T₁ T₂ => Disjoint T₁.vs.toFinset T₂.vs.toFinset) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro F hlen cov hneF disj
    classical
    by_cases hshare : ∃ T₁ ∈ F, ∃ T₂ ∈ F, T₁ ≠ T₂ ∧ ∃ v, v ∈ T₁.vs ∧ v ∈ T₂.vs
    · obtain ⟨T₁, hT₁, T₂, hT₂, hne12, v, hv1, hv2⟩ := hshare
      obtain ⟨k₁, hk₁, hkv₁⟩ := T₁.exists_rotate_index (hneF T₁ hT₁) hv1
      obtain ⟨k₂, hk₂, hkv₂⟩ := T₂.exists_rotate_index (hneF T₂ hT₂) hv2
      have hh1 : (T₁.rotate k₁ hk₁).vs.head? = some v := T₁.rotate_head? k₁ hk₁ hkv₁
      have hh2 : (T₂.rotate k₂ hk₂).vs.head? = some v := T₂.rotate_head? k₂ hk₂ hkv₂
      have hdj12 : Disjoint (T₁.rotate k₁ hk₁).es.toFinset (T₂.rotate k₂ hk₂).es.toFinset := by
        rw [CTrail.rotate_es_toFinset T₁ k₁ hk₁, CTrail.rotate_es_toFinset T₂ k₂ hk₂]
        exact disj.forall hT₁ hT₂ hne12
      set T := (T₁.rotate k₁ hk₁).append (T₂.rotate k₂ hk₂) hh1 hh2 hdj12 with hT
      have hTe : T.es = (T₁.rotate k₁ hk₁).es ++ (T₂.rotate k₂ hk₂).es := rfl
      have hFl : 2 ≤ F.length := by
        rcases F with _ | ⟨A, F⟩
        · simp at hT₁
        · cases F with
          | nil =>
            simp only [List.mem_singleton] at hT₁ hT₂
            rw [hT₁, hT₂] at hne12
            exact absurd rfl hne12
          | cons B F => simp
      set F'' := T :: F.filter (fun T' => T' ≠ T₁ ∧ T' ≠ T₂) with hF''
      have hF''len : F''.length ≤ F.length - 1 := by
        rw [hF'', List.length_cons]
        have hbound : (F.filter fun T' => T' ≠ T₁ ∧ T' ≠ T₂).length + 2 ≤ F.length := by
          have hadd := List.length_eq_length_filter_add (l := F) (fun T' => T' ≠ T₁ ∧ T' ≠ T₂)
          have htwo : 2 ≤ (F.filter fun a => !decide (a ≠ T₁ ∧ a ≠ T₂)).length := by
            apply two_le_length (a := T₁) (b := T₂) (hne := hne12)
            · rw [List.mem_filter]
              exact ⟨hT₁, by simp⟩
            · rw [List.mem_filter]
              exact ⟨hT₂, by simp⟩
          omega
        omega
      have hF''cov : ∀ e, ∃ T' ∈ F'', e ∈ T'.es := by
        intro e
        obtain ⟨T', hT', heT'⟩ := cov e
        by_cases h1 : T' = T₁
        · refine ⟨T, by rw [hF'']; exact List.mem_cons_self, ?_⟩
          rw [h1] at heT'
          have he1 : e ∈ (T₁.rotate k₁ hk₁).es := by
            rw [← List.mem_toFinset, CTrail.rotate_es_toFinset T₁ k₁ hk₁, List.mem_toFinset]
            exact heT'
          rw [hTe]
          exact List.mem_append_left _ he1
        · by_cases h2 : T' = T₂
          · refine ⟨T, by rw [hF'']; exact List.mem_cons_self, ?_⟩
            rw [h2] at heT'
            have he2 : e ∈ (T₂.rotate k₂ hk₂).es := by
              rw [← List.mem_toFinset, CTrail.rotate_es_toFinset T₂ k₂ hk₂, List.mem_toFinset]
              exact heT'
            rw [hTe]
            exact List.mem_append_right _ he2
          · refine ⟨T', ?_, heT'⟩
            rw [hF'', List.mem_cons]
            exact Or.inr (List.mem_filter.mpr ⟨hT', by simp [h1, h2]⟩)
      have hF''ne : ∀ T' ∈ F'', T'.es ≠ [] := by
        intro T' hT'
        rw [hF'', List.mem_cons] at hT'
        rcases hT' with rfl | hT'
        · rw [hTe]
          intro hnil
          have hr1 : (T₁.rotate k₁ hk₁).es ≠ [] := by
            show (T₁.es.rotate k₁) ≠ []
            intro h
            exact hneF T₁ hT₁ (List.rotate_eq_nil_iff.mp h)
          have hlen0 : ((T₁.rotate k₁ hk₁).es ++ (T₂.rotate k₂ hk₂).es).length = 0 := by
            rw [hnil, List.length_nil]
          rw [List.length_append] at hlen0
          have hz : (T₁.rotate k₁ hk₁).es = [] :=
            List.length_eq_zero_iff.mp (by omega)
          exact hr1 hz
        · exact hneF T' (List.mem_filter.mp hT' |>.1)
      have hF''dj : F''.Pairwise (fun S₁ S₂ => Disjoint S₁.es.toFinset S₂.es.toFinset) := by
        rw [hF'', List.pairwise_cons]
        refine ⟨?_, disj.sublist List.filter_sublist⟩
        intro T' hT'
        have hT'F : T' ∈ F := (List.mem_filter.mp hT').1
        have hne1 : T' ≠ T₁ := (of_decide_eq_true (List.mem_filter.mp hT').2).1
        have hne2 : T' ≠ T₂ := (of_decide_eq_true (List.mem_filter.mp hT').2).2
        have d1 : Disjoint (T₁.rotate k₁ hk₁).es.toFinset T'.es.toFinset := by
          rw [CTrail.rotate_es_toFinset T₁ k₁ hk₁]
          exact disj.forall hT₁ hT'F hne1.symm
        have d2 : Disjoint (T₂.rotate k₂ hk₂).es.toFinset T'.es.toFinset := by
          rw [CTrail.rotate_es_toFinset T₂ k₂ hk₂]
          exact disj.forall hT₂ hT'F hne2.symm
        rw [hTe, List.toFinset_append, Finset.disjoint_union_left]
        exact ⟨d1, d2⟩
      obtain ⟨F', h1, h2, h3, h4⟩ := ih (F''.length) (by omega) F'' rfl hF''cov hF''ne hF''dj
      exact ⟨F', h1, h2, h3, h4⟩
    · refine ⟨F, cov, hneF, disj, ?_⟩
      rw [List.pairwise_iff_getElem]
      intro i j hi hj hij
      by_contra hndj
      rw [Finset.not_disjoint_iff] at hndj
      obtain ⟨v, hv1, hv2⟩ := hndj
      rw [List.mem_toFinset] at hv1 hv2
      by_cases hEq : F[i] = F[j]
      · have hd := (List.pairwise_iff_getElem.mp disj) i j hi hj hij
        rw [hEq, Finset.disjoint_self_iff_empty] at hd
        have hEj : F[j].es = [] := by
          by_contra hne
          obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil _ hne
          rw [← List.mem_toFinset, hd] at he
          simp at he
        exact hneF F[j] (List.getElem_mem hj) hEj
      · exact hshare ⟨F[i], List.getElem_mem hi, F[j], List.getElem_mem hj, hEq, v, hv1, hv2⟩

lemma mult_sum (a b : E → V) (e : E) : ∑ x : V, mult a b e x = 2 := by
  classical
  simp [mult, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq]

lemma IsWalk.mem_vs_of_mem_es {a b : E → V} {vs : List V} {es : List E}
    (h : IsWalk a b vs es) {e : E} (he : e ∈ es) : a e ∈ vs ∧ b e ∈ vs := by
  induction h with
  | nil v => simp at he
  | @cons v w e' vs' es' hconn hw ih =>
    rw [List.mem_cons] at he
    rcases he with rfl | he
    · rcases hconn with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨List.mem_cons_self, List.mem_cons_of_mem _ (List.mem_cons_self)⟩
      · exact ⟨List.mem_cons_of_mem _ (List.mem_cons_self), List.mem_cons_self⟩
    · have ⟨h1, h2⟩ := ih he
      exact ⟨List.mem_cons_of_mem _ h1, List.mem_cons_of_mem _ h2⟩

instance (a b : E → V) :
    Std.Symm (fun T₁ T₂ : CTrail a b => Disjoint T₁.vs.toFinset T₂.vs.toFinset) :=
  ⟨fun _ _ h => Disjoint.symm h⟩

lemma even_length_of_mem {a b : E → V} (F : List (CTrail a b))
    (hcov : ∀ e, ∃ T ∈ F, e ∈ T.es)
    (hdjv : F.Pairwise (fun T₁ T₂ => Disjoint T₁.vs.toFinset T₂.vs.toFinset))
    (hdeg : ∀ x, (∑ e : E, mult a b e x) = 4)
    {T : CTrail a b} (hT : T ∈ F) : Even T.es.length := by
  have key1 : ∑ x : V, slotCount a b T.es x = 2 * T.es.length := by
    have h1 : ∀ x : V, slotCount a b T.es x = ∑ e ∈ T.es.toFinset, mult a b e x := by
      intro x
      exact list_sum_eq_toFinset_sum T.nodup
    rw [Finset.sum_congr rfl (fun x _ => h1 x), Finset.sum_comm]
    simp [mult_sum]
    rw [List.toFinset_card_of_nodup T.nodup]
    ring
  have key2 : ∑ x : V, slotCount a b T.es x =
      ∑ x ∈ T.vs.toFinset, ∑ e : E, mult a b e x := by
    have h1 : ∀ x, x ∉ T.vs.toFinset → slotCount a b T.es x = 0 := by
      intro x hx
      rw [List.mem_toFinset] at hx
      rw [slotCount, list_sum_eq_toFinset_sum T.nodup]
      apply Finset.sum_eq_zero
      intro e he
      rw [List.mem_toFinset] at he
      by_contra hm
      have ⟨h2, h3⟩ := T.walk.mem_vs_of_mem_es he
      have hor : a e = x ∨ b e = x := by
        by_contra h'
        push_neg at h'
        simp [mult, h'.1, h'.2] at hm
      rcases hor with rfl | rfl
      · exact hx h2
      · exact hx h3
    have h2 : ∀ x, x ∈ T.vs.toFinset → slotCount a b T.es x = ∑ e : E, mult a b e x := by
      intro x hx
      rw [List.mem_toFinset] at hx
      rw [slotCount, list_sum_eq_toFinset_sum T.nodup]
      apply Finset.sum_subset (Finset.subset_univ _)
      intro e heU hnin
      rw [List.mem_toFinset] at hnin
      by_contra hm
      have hconn : a e = x ∨ b e = x := by
        by_contra h'
        push_neg at h'
        simp [mult, h'.1, h'.2] at hm
      obtain ⟨T', hT', heT'⟩ := hcov e
      have hxT' : x ∈ T'.vs := by
        have ⟨h2', h3'⟩ := T'.walk.mem_vs_of_mem_es heT'
        rcases hconn with rfl | rfl
        · exact h2'
        · exact h3'
      by_cases hTT : T' = T
      · subst hTT
        exact hnin heT'
      · have hd := hdjv.forall hT' hT hTT
        rw [Finset.disjoint_left] at hd
        exact (hd (List.mem_toFinset.mpr hxT') (List.mem_toFinset.mpr hx)).elim
    calc ∑ x : V, slotCount a b T.es x
        = ∑ x ∈ T.vs.toFinset, slotCount a b T.es x :=
          (Finset.sum_subset (Finset.subset_univ _) fun x _ hxn =>
            h1 x (by simpa using hxn)).symm
      _ = ∑ x ∈ T.vs.toFinset, ∑ e : E, mult a b e x :=
          Finset.sum_congr rfl fun x hx => h2 x (by simpa using hx)
  have h3 : 2 * T.es.length = 4 * T.vs.toFinset.card := by
    rw [← key1, key2]
    simp only [hdeg, Finset.sum_const, nsmul_eq_mul, Nat.cast_id]
    ring
  exact ⟨T.vs.toFinset.card, by omega⟩

lemma mapIdx_eq_map_idxOf {l : List E} (hn : l.Nodup) (g : ℕ → E → ℕ) :
    l.mapIdx g = l.map (fun e => g (l.idxOf e) e) := by
  induction l generalizing g with
  | nil => rfl
  | cons a l ih =>
    have hnl : l.Nodup := List.Nodup.of_cons hn
    rw [List.mapIdx_cons, List.map_cons, ih hnl (fun i e => g (i + 1) e)]
    have h0 : (a :: l).idxOf a = 0 := by rw [List.idxOf_cons_eq _ rfl]
    rw [h0]
    congr 1
    apply List.map_congr_left
    intro e he
    have hne : e ≠ a := fun h => by
      rw [h] at he
      exact (List.nodup_cons.mp hn).1 he
    rw [List.idxOf_cons_ne _ hne.symm]

/-- Every 4-regular pseudograph has a 2-factor: a 2-coloring of its edges such that
every vertex sees exactly two half-edges of each color. -/
theorem two_factor (a b : E → V) (hdeg : ∀ x, (∑ e : E, mult a b e x) = 4) :
    ∃ red : E → Bool, ∀ x : V, (∑ e : E, if red e then mult a b e x else 0) = 2 := by
  classical
  obtain ⟨F, hFU, hFne, hFcov, hFdj⟩ :=
    decompose a b Finset.univ (fun x => by rw [hdeg x]; exact ⟨2, rfl⟩)
  obtain ⟨F', hF'cov, hF'ne, hF'dj, hFvdj⟩ :=
    merge_disjoint a b F.length F rfl (fun e => hFcov e (Finset.mem_univ e)) hFne hFdj
  set T₀ : E → CTrail a b := fun e => Classical.choose (hF'cov e) with hT₀def
  have hT₀ : ∀ e, T₀ e ∈ F' ∧ e ∈ (T₀ e).es := fun e => Classical.choose_spec (hF'cov e)
  have huniq : ∀ e T, T ∈ F' → e ∈ T.es → T = T₀ e := by
    intro e T hT heT
    obtain ⟨hT0e, heT0⟩ := hT₀ e
    by_contra hne
    have hd := hF'dj.forall hT hT0e hne
    rw [Finset.disjoint_left] at hd
    exact (hd (List.mem_toFinset.mpr heT) (List.mem_toFinset.mpr heT0)).elim
  set red : E → Bool := fun e => decide (((T₀ e).es.idxOf e) % 2 = 0) with hred
  refine ⟨red, fun x => ?_⟩
  have hex : ∃ e₀, mult a b e₀ x ≠ 0 := by
    by_contra h'
    push_neg at h'
    have h4 : (∑ e : E, mult a b e x) = 0 := Finset.sum_eq_zero fun e _ => h' e
    rw [hdeg x] at h4
    simp at h4
  obtain ⟨e₀, he₀⟩ := hex
  set Tx := T₀ e₀ with hTx
  obtain ⟨hTxF, he₀Tx⟩ := hT₀ e₀
  have hxTx : x ∈ Tx.vs := by
    have ⟨h1, h2⟩ := Tx.walk.mem_vs_of_mem_es he₀Tx
    by_cases h1' : a e₀ = x
    · rw [h1'] at h1; exact h1
    · have h2' : b e₀ = x := by
        by_contra hb
        simp [mult, h1', hb] at he₀
      rw [h2'] at h2; exact h2
  have hedges : ∀ e, mult a b e x ≠ 0 → e ∈ Tx.es := by
    intro e he
    obtain ⟨hTeF, heTe⟩ := hT₀ e
    have hxe : x ∈ (T₀ e).vs := by
      have ⟨h1, h2⟩ := (T₀ e).walk.mem_vs_of_mem_es heTe
      by_cases h1' : a e = x
      · rw [h1'] at h1; exact h1
      · have h2' : b e = x := by
          by_contra hb
          simp [mult, h1', hb] at he
        rw [h2'] at h2; exact h2
    by_cases hTT : T₀ e = Tx
    · rw [hTT] at heTe; exact heTe
    · have hd := hFvdj.forall hTeF hTxF hTT
      rw [Finset.disjoint_left] at hd
      exact (hd (List.mem_toFinset.mpr hxe) (List.mem_toFinset.mpr hxTx)).elim
  have hLen : Even Tx.es.length := even_length_of_mem F' hF'cov hFvdj hdeg hTxF
  have hs1 : (∑ e : E, if red e then mult a b e x else 0) =
      (Tx.es.map (fun e => if red e then mult a b e x else 0)).sum := by
    rw [list_sum_eq_toFinset_sum Tx.nodup]
    apply (Finset.sum_subset (Finset.subset_univ _) _).symm
    intro e heU hnin
    rw [List.mem_toFinset] at hnin
    by_cases hre : red e
    · rw [if_pos hre]
      by_contra hm
      exact hnin (hedges e hm)
    · rw [if_neg hre]
  rw [hs1]
  have hs2 : (Tx.es.map (fun e => if red e then mult a b e x else 0)).sum =
      (Tx.es.mapIdx (fun i e => if i % 2 = 0 then mult a b e x else 0)).sum := by
    rw [mapIdx_eq_map_idxOf Tx.nodup]
    apply congrArg List.sum
    apply List.map_congr_left
    intro e he
    have hTe : T₀ e = Tx := (huniq e Tx hTxF he).symm
    by_cases hip : Tx.es.idxOf e % 2 = 0 <;> simp [hred, hTe, hip]
  rw [hs2, altCount_closed Tx.walk Tx.closed hLen x]
  have hsc : slotCount a b Tx.es x = 4 := by
    rw [← hdeg x, slotCount, list_sum_eq_toFinset_sum Tx.nodup]
    apply Finset.sum_subset (Finset.subset_univ _)
    intro e heU hnin
    rw [List.mem_toFinset] at hnin
    by_contra hm
    exact hnin (hedges e hm)
  rw [slotCount_closed Tx.walk Tx.closed x] at hsc
  omega

end TwoFactor

section Assembly

variable {n : ℕ} (c : Fin (4 * n) → Fin n)

/-- The lighter pebble of pair `k`. -/
def apeb : Fin (2 * n) → Fin (4 * n) := fun k => ⟨k.val, by omega⟩

/-- The heavier pebble of pair `k`. -/
def bpeb : Fin (2 * n) → Fin (4 * n) := fun k => ⟨4 * n - 1 - k.val, by omega⟩

lemma apeb_inj : Function.Injective (@apeb n) := fun k₁ k₂ h => by
  have h2 : (apeb k₁).val = (apeb k₂).val := Fin.ext_iff.mp h
  exact Fin.ext h2
lemma bpeb_inj : Function.Injective (@bpeb n) := fun k₁ k₂ h => by
  have h2 : (bpeb k₁).val = (bpeb k₂).val := Fin.ext_iff.mp h
  have h3 : k₁.val = k₂.val := by
    have h4 := h2
    simp [bpeb] at h4
    omega
  exact Fin.ext h3
lemma apeb_ne_bpeb (k₁ k₂ : Fin (2 * n)) : apeb k₁ ≠ bpeb k₂ := by
  intro h
  have := Fin.ext_iff.mp h
  simp [apeb, bpeb] at this
  omega

/-- The pair (one of the `2n` complementary pairs) that pebble `j` belongs to. -/
def pairOf : Fin (4 * n) → Fin (2 * n) := fun j =>
  if h : j.val < 2 * n then ⟨j.val, h⟩ else ⟨4 * n - 1 - j.val, by omega⟩

lemma pairOf_apeb (k : Fin (2 * n)) : pairOf (apeb k) = k := by
  show pairOf ⟨k.val, _⟩ = k
  rw [pairOf, dif_pos k.isLt]

lemma pairOf_bpeb (k : Fin (2 * n)) : pairOf (bpeb k) = k := by
  show pairOf ⟨4 * n - 1 - k.val, _⟩ = k
  rw [pairOf, dif_neg (by omega : ¬ (4 * n - 1 - k.val) < 2 * n)]
  exact Fin.ext (by simp; omega)

lemma pairOf_mem_pair (j : Fin (4 * n)) : j = apeb (pairOf j) ∨ j = bpeb (pairOf j) := by
  by_cases hj : j.val < 2 * n
  · left
    rw [pairOf, dif_pos hj]
    exact Fin.ext rfl
  · right
    rw [pairOf, dif_neg hj]
    exact Fin.ext (by simp [bpeb]; omega)

/-- The pseudograph on colors whose edges are the complementary pairs. -/
def pgA : Fin (2 * n) → Fin n := fun k => c (apeb k)
def pgB : Fin (2 * n) → Fin n := fun k => c (bpeb k)

lemma univ_eq_map_union :
    (Finset.univ : Finset (Fin (4 * n))) =
      (Finset.univ.map ⟨apeb, @apeb_inj n⟩) ∪ (Finset.univ.map ⟨bpeb, @bpeb_inj n⟩) := by
  ext j
  simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_map, Function.Embedding.coeFn_mk]
  constructor
  · intro _
    by_cases hj : j.val < 2 * n
    · left
      refine ⟨⟨j.val, hj⟩, trivial, Fin.ext rfl⟩
    · right
      refine ⟨⟨4 * n - 1 - j.val, by omega⟩, trivial, ?_⟩
      exact Fin.ext (by show 4 * n - 1 - (4 * n - 1 - j.val) = j.val; omega)
  · rintro (⟨k, -, rfl⟩ | ⟨k, -, rfl⟩) <;> simp

lemma disjoint_map_map :
    Disjoint (Finset.univ.map ⟨apeb, @apeb_inj n⟩) (Finset.univ.map ⟨bpeb, @bpeb_inj n⟩) := by
  rw [Finset.disjoint_left]
  intro j hj1 hj2
  simp only [Finset.mem_map, Function.Embedding.coeFn_mk, Finset.mem_univ, true_and] at hj1 hj2
  obtain ⟨k₁, rfl⟩ := hj1
  obtain ⟨k₂, hk₂⟩ := hj2
  exact apeb_ne_bpeb k₁ k₂ hk₂.symm

lemma pg_deg (h : ∀ i, #{j | c j = i} = 4) (x : Fin n) :
    (∑ e : Fin (2 * n), mult (pgA c) (pgB c) e x) = 4 := by
  rw [Finset.sum_congr rfl (fun e _ => by rw [mult, pgA, pgB]), Finset.sum_add_distrib]
  have h4 := h x
  rw [Finset.card_filter, univ_eq_map_union, Finset.sum_union disjoint_map_map,
    Finset.sum_map, Finset.sum_map] at h4
  simp only [Function.Embedding.coeFn_mk] at h4
  exact h4

lemma weight_sum (r : Fin (2 * n) → Bool) :
    ∑ j ∈ Finset.univ.filter (fun j => r (pairOf j) = true), (j.val + 1) =
      (Finset.univ.filter (fun e => r e = true)).card * (4 * n + 1) := by
  have hdisj : (↑(Finset.univ.filter (fun e => r e = true)) : Set (Fin (2 * n))).PairwiseDisjoint
      fun k => ({apeb k, bpeb k} : Finset (Fin (4 * n))) := by
    intro k₁ hk₁ k₂ hk₂ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro j hj1 hj2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj1 hj2
    rcases hj1 with rfl | rfl <;> rcases hj2 with hj2 | hj2
    · exact hne (apeb_inj hj2)
    · exact apeb_ne_bpeb k₁ k₂ hj2
    · exact apeb_ne_bpeb k₂ k₁ hj2.symm
    · exact hne (bpeb_inj hj2)
  have h1 : Finset.univ.filter (fun j => r (pairOf j) = true) =
      (Finset.univ.filter (fun e => r e = true)).biUnion fun k => ({apeb k, bpeb k} : Finset (Fin (4 * n))) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hr
      exact ⟨pairOf j, hr, pairOf_mem_pair j⟩
    · rintro ⟨k, hr, hj⟩
      rcases hj with rfl | rfl
      · rw [pairOf_apeb]; exact hr
      · rw [pairOf_bpeb]; exact hr
  rw [h1, Finset.sum_biUnion hdisj]
  have hpair : ∀ k : Fin (2 * n),
      ∑ j ∈ ({apeb k, bpeb k} : Finset (Fin (4 * n))), (j.val + 1) = 4 * n + 1 := by
    intro k
    rw [Finset.sum_insert (by simp [apeb_ne_bpeb]), Finset.sum_singleton]
    have hv1 : (apeb k).val = k.val := rfl
    have hv2 : (bpeb k).val = 4 * n - 1 - k.val := rfl
    rw [hv1, hv2]
    omega
  rw [Finset.sum_congr rfl (fun k _ => hpair k), Finset.sum_const, nsmul_eq_mul, Nat.cast_id]

lemma red_card (h : ∀ i, #{j | c j = i} = 4) (red : Fin (2 * n) → Bool)
    (hred : ∀ x : Fin n, (∑ e : Fin (2 * n), if red e then mult (pgA c) (pgB c) e x else 0) = 2) :
    (Finset.univ.filter (fun e => red e = true)).card = n := by
  have h1 : ∑ x : Fin n, (∑ e : Fin (2 * n), if red e then mult (pgA c) (pgB c) e x else 0) =
      2 * n := by
    simp only [hred, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_id]
    ring
  rw [Finset.sum_comm] at h1
  have h2 : ∑ e : Fin (2 * n), (∑ x : Fin n, if red e then mult (pgA c) (pgB c) e x else 0) =
      (Finset.univ.filter (fun e => red e = true)).card * 2 := by
    have h3 : ∀ e : Fin (2 * n), (∑ x : Fin n, if red e then mult (pgA c) (pgB c) e x else 0) =
        if red e then 2 else 0 := by
      intro e
      by_cases hr : red e <;> simp [hr, mult_sum]
    rw [Finset.sum_congr rfl (fun e _ => h3 e)]
    simp only [Finset.sum_ite, Finset.sum_const, nsmul_eq_mul, Nat.cast_id, mul_zero,
      add_zero]
  omega

lemma compl_filter_pairOf (red : Fin (2 * n) → Bool) :
    (Finset.univ.filter (fun j => red (pairOf j) = true))ᶜ =
      Finset.univ.filter (fun j => (!red (pairOf j)) = true) := by
  ext j
  simp [Finset.mem_compl, Finset.mem_filter, Bool.not_eq_true]

end Assembly

snip end

problem imo2020_p3 {n : ℕ} {c : Fin (4 * n) → Fin n} (h : ∀ i, #{j | c j = i} = 4) :
    ∃ S : Finset (Fin (4 * n)), ∑ i ∈ S, ((i : ℕ) + 1) = ∑ i ∈ Sᶜ, ((i : ℕ) + 1) ∧
      ∀ i, #{j ∈ S | c j = i} = 2 := by
  classical
  obtain ⟨red, hred⟩ := two_factor (pgA c) (pgB c) (pg_deg c h)
  have hN : (Finset.univ.filter (fun e => red e = true)).card = n := red_card c h red hred
  refine ⟨Finset.univ.filter (fun j => red (pairOf j) = true), ?_, ?_⟩
  · rw [compl_filter_pairOf red, weight_sum red, weight_sum (fun e => !red e), hN]
    congr 1
    have h1 : (Finset.univ.filter (fun e => (!red e) = true)).card +
        (Finset.univ.filter (fun e => red e = true)).card = 2 * n := by
      have h2 : (Finset.univ.filter (fun e => red e = true)).card +
        (Finset.univ.filter (fun e => ¬(red e = true))).card = Finset.univ.card :=
        Finset.card_filter_add_card_filter_not (fun e => red e = true)
      have h3 : (Finset.univ.filter fun e => ¬(red e = true)) =
        (Finset.univ.filter fun e => (!red e) = true) := by
        ext e
        by_cases hr : red e <;> simp [hr]
      rw [h3, Finset.card_univ, Fintype.card_fin] at h2
      omega
    omega
  · intro i
    have hcol : ((Finset.univ.filter (fun j => red (pairOf j) = true)).filter
        (fun j => c j = i)).card = 2 := by
      rw [Finset.filter_filter, Finset.card_filter, ← hred i, univ_eq_map_union,
        Finset.sum_union disjoint_map_map, Finset.sum_map, Finset.sum_map,
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro e _
      by_cases hr : red e
      · rw [if_pos hr, mult, pgA, pgB]
        simp only [hr, true_and, pairOf_apeb, pairOf_bpeb, ite_true,
          Function.Embedding.coeFn_mk]
      · simp only [hr, false_and, if_false, pairOf_apeb, pairOf_bpeb, Bool.false_eq_true,
          Function.Embedding.coeFn_mk]
    exact hcol

end Imo2020P3
