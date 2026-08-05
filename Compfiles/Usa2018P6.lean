/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Data.Rat.Star
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Lemmas
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics] }

/-!
# USA Mathematical Olympiad 2018, Problem 6

Let $a_n$ be the number of permutations $(x_1, x_2, \ldots, x_n)$ of the numbers
$(1, 2, \ldots, n)$ such that the $n$ ratios $\frac{x_k}{k}$ for $1 \le k \le n$
are all distinct. Prove that $a_n$ is odd for all $n \ge 1$.
-/

namespace Usa2018P6

open Equiv Finset Function

snip begin

/-! ### Basic definitions -/

/-- The ratio `x_k / k` attached to position `k` of a permutation of `{1, ..., n}`,
with positions and values encoded by `Fin n` via `·.val + 1`. -/
def ratio {n : ℕ} (σ : Equiv.Perm (Fin n)) (k : Fin n) : ℚ :=
  ((σ k).val + 1) / (k.val + 1)

/-- A permutation is *valid* if all its ratios are distinct. -/
def Valid {n : ℕ} (σ : Equiv.Perm (Fin n)) : Prop :=
  Function.Injective (ratio σ)

instance {n : ℕ} : DecidablePred (Valid (n := n)) := fun σ => by
  unfold Valid Function.Injective
  infer_instance

/-- The numerators of an involution: positions sent to a strictly larger value. -/
def nums {n : ℕ} (σ : Equiv.Perm (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter fun k => k.val < (σ k).val

/-- The label of the edge `{k, σ k}` as seen from its smaller endpoint `k`:
the rational `(k+1)/(σ k + 1)`. -/
def label {n : ℕ} (σ : Equiv.Perm (Fin n)) (k : Fin n) : ℚ :=
  (k.val + 1) / ((σ k).val + 1)

/-- An involution is *fantastic* if its edges have pairwise distinct labels. -/
def Fantastic {n : ℕ} (σ : Equiv.Perm (Fin n)) : Prop :=
  Set.InjOn (label σ) (nums σ)

instance {n : ℕ} (σ : Equiv.Perm (Fin n)) : Decidable (Fantastic σ) := by
  unfold Fantastic Set.InjOn
  infer_instance

/-- A *vertex* is an involution with at most one fixed point
(equivalently, a maximal matching of the complete graph). -/
def IsVertex {n : ℕ} (σ : Equiv.Perm (Fin n)) : Prop :=
  Function.Involutive σ ∧ (Finset.univ.filter fun x => σ x = x).card ≤ 1

instance {n : ℕ} : DecidablePred (IsVertex (n := n)) := fun σ => by
  unfold IsVertex Function.Involutive
  infer_instance

/-- A *switching involution* on a vertex `σ`: an involution `φ` supported on the
numerators of `σ` which preserves labels. -/
def IsSwitch {n : ℕ} (σ φ : Equiv.Perm (Fin n)) : Prop :=
  Function.Involutive φ ∧ (∀ x, x ∉ nums σ → φ x = x) ∧
    ∀ x, x ∈ nums σ → label σ (φ x) = label σ x

instance {n : ℕ} (σ : Equiv.Perm (Fin n)) : DecidablePred (IsSwitch σ) := fun φ => by
  unfold IsSwitch Function.Involutive
  infer_instance

/-- The type of pairs `(σ, φ)` with `σ` a vertex and `φ` a switching involution of `σ`. -/
def WPairs (n : ℕ) : Type :=
  {p : Equiv.Perm (Fin n) × Equiv.Perm (Fin n) // IsVertex p.1 ∧ IsSwitch p.1 p.2}

instance {n : ℕ} : Fintype (WPairs n) := by
  unfold WPairs
  infer_instance

/-! ### Cardinality of involutions modulo two -/

/-- A fixed-point-free involution on a fintype forces the cardinality to be even. -/
theorem even_card_of_involutive_ne {α : Type*} [Fintype α] {f : α → α}
    (hf : Function.Involutive f) (hfree : ∀ x, f x ≠ x) : Even (Fintype.card α) := by
  classical
  let e := (Fintype.truncEquivFin α).out
  -- split `α` into the two halves `{x | e x < e (f x)}` and its complement
  set s₁ := Finset.univ.filter fun x => e x < e (f x) with hs₁
  set s₂ := Finset.univ.filter fun x => ¬ e x < e (f x) with hs₂
  have hcard : s₁.card = s₂.card := by
    apply Finset.card_bij (fun x _ => f x)
    · intro x hx
      simp only [hs₁, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      simp only [hs₂, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hf x]
      exact fun h => h.not_gt hx
    · intro x _ y _ hxy
      exact hf.injective hxy
    · intro y hy
      simp only [hs₂, Finset.mem_filter, Finset.mem_univ, true_and] at hy
      have h1 : e (f y) ≠ e y := fun h => hfree y (e.injective h)
      have h2 : e (f y) < e y := lt_of_le_of_ne (not_lt.1 hy) h1
      refine ⟨f y, ?_, hf y⟩
      simp only [hs₁, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hf y]
      exact h2
  have hunion : s₁.card + s₂.card = Fintype.card α := by
    rw [hs₁, hs₂, Finset.card_filter_add_card_filter_not]
    simp
  refine ⟨s₁.card, ?_⟩
  rw [← hunion, hcard]

/-- For an involution `f` on a fintype, the cardinality of the whole type is congruent
modulo two to the cardinality of the fixed-point subtype. -/
theorem card_modEq_of_involutive {α : Type*} [Fintype α] [DecidableEq α] (f : α → α)
    (hf : Function.Involutive f) :
    Fintype.card α ≡ Fintype.card {x // f x = x} [MOD 2] := by
  classical
  have hsplit : Fintype.card α =
      Fintype.card {x // f x = x} + Fintype.card {x // f x ≠ x} := by
    rw [Fintype.card_subtype_compl]
    exact (Nat.add_sub_of_le (Fintype.card_subtype_le _)).symm
  have heven : Even (Fintype.card {x // f x ≠ x}) := by
    let g : {x // f x ≠ x} → {x // f x ≠ x} := fun x =>
      ⟨f x.1, fun h => x.2 (h.symm.trans (hf x.1))⟩
    apply even_card_of_involutive_ne (f := g)
    · intro x
      apply Subtype.ext
      show f (f x.1) = x.1
      exact hf x.1
    · intro x h
      exact x.2 (Subtype.mk_eq_mk.1 h)
  obtain ⟨k, hk⟩ := heven
  rw [hsplit, hk]
  have : (Fintype.card {x // f x = x} + (k + k)) % 2 = (Fintype.card {x // f x = x}) % 2 := by
    omega
  exact this

/-! ### Small arithmetic helpers -/

lemma val_add_one_pos {n : ℕ} (k : Fin n) : (0 : ℚ) < k.val + 1 := by positivity

/-- Cross-multiplied form of an equality of labels. -/
lemma nat_mul_eq_of_label_eq {n : ℕ} {σ : Equiv.Perm (Fin n)} {x y : Fin n}
    (h : label σ x = label σ y) :
    (x.val + 1) * ((σ y).val + 1) = (y.val + 1) * ((σ x).val + 1) := by
  have h1 : (x.val + 1 : ℚ) * ((σ y).val + 1) = (y.val + 1) * ((σ x).val + 1) := by
    rw [label, label, div_eq_div_iff (val_add_one_pos _).ne' (val_add_one_pos _).ne'] at h
    exact h
  exact_mod_cast h1

/-- If `A * D = C * B` with `A < C` then `B < D` (natural numbers). -/
lemma lt_of_mul_eq_mul_lt {A B C D : ℕ} (h : A * D = C * B) (hAC : A < C) (hD : 0 < D) :
    B < D := by
  have h1 : B * C < D * C := by
    rw [Nat.mul_comm B C, Nat.mul_comm D C, ← h]
    exact Nat.mul_lt_mul_of_pos_right hAC hD
  exact Nat.lt_of_mul_lt_mul_right h1

/-- If `A * D = C * B` with `A = C` and `0 < A` then `B = D`. -/
lemma eq_of_mul_eq_mul_eq {A B C D : ℕ} (h : A * D = C * B) (hAC : A = C) (hA : 0 < A) :
    B = D := by
  subst hAC
  exact (Nat.mul_left_cancel hA h).symm

/-- Label equality transfers the order of numerators to the order of denominators. -/
lemma label_order_transfer {n : ℕ} {σ : Equiv.Perm (Fin n)} {x y : Fin n}
    (h : label σ x = label σ y) :
    x.val < y.val → (σ x).val < (σ y).val := by
  intro hxy
  have h1 := nat_mul_eq_of_label_eq h
  have h2 : (σ x).val + 1 < (σ y).val + 1 := lt_of_mul_eq_mul_lt h1 (by omega) (by omega)
  omega

/-! ### Validity and inversion -/

lemma ratio_pos {n : ℕ} (σ : Equiv.Perm (Fin n)) (k : Fin n) : 0 < ratio σ k := by
  unfold ratio
  positivity

/-- A permutation is valid iff its inverse is (one direction). -/
theorem valid_inv {n : ℕ} {σ : Equiv.Perm (Fin n)} (h : Valid σ) : Valid σ⁻¹ := by
  intro a b hab
  have hri : ∀ x : Fin n, ratio σ⁻¹ x = (ratio σ (σ⁻¹ x))⁻¹ := by
    intro x
    have hx : σ (σ⁻¹ x) = x := by simp
    unfold ratio
    rw [hx, inv_div]
  rw [hri, hri] at hab
  have h2 : ratio σ (σ⁻¹ a) = ratio σ (σ⁻¹ b) := inv_injective hab
  have h3 := h h2
  exact (σ⁻¹).injective h3

/-! ### Valid involutions are exactly the fantastic vertices -/

lemma ratio_eq_one_iff {n : ℕ} {σ : Equiv.Perm (Fin n)} {k : Fin n} :
    ratio σ k = 1 ↔ σ k = k := by
  unfold ratio
  rw [div_eq_one_iff_eq (val_add_one_pos k).ne']
  constructor
  · intro h
    have h2 : (σ k).val + 1 = k.val + 1 := by exact_mod_cast h
    exact Fin.ext (Nat.succ.inj h2)
  · intro h
    rw [h]

lemma one_lt_ratio_iff {n : ℕ} {σ : Equiv.Perm (Fin n)} {k : Fin n} :
    1 < ratio σ k ↔ k.val < (σ k).val := by
  unfold ratio
  rw [one_lt_div (val_add_one_pos k)]
  constructor
  · intro h
    have : k.val + 1 < (σ k).val + 1 := by exact_mod_cast h
    omega
  · intro h
    have : k.val + 1 < (σ k).val + 1 := by omega
    exact_mod_cast this

lemma ratio_lt_one_iff {n : ℕ} {σ : Equiv.Perm (Fin n)} {k : Fin n} :
    ratio σ k < 1 ↔ (σ k).val < k.val := by
  unfold ratio
  rw [div_lt_one (val_add_one_pos k)]
  constructor
  · intro h
    have : (σ k).val + 1 < k.val + 1 := by exact_mod_cast h
    omega
  · intro h
    have : (σ k).val + 1 < k.val + 1 := by omega
    exact_mod_cast this

lemma label_eq_ratio {n : ℕ} {σ : Equiv.Perm (Fin n)} (hinv : Function.Involutive σ)
    (k : Fin n) : label σ k = ratio σ (σ k) := by
  unfold label ratio
  rw [hinv k]

lemma mem_nums_iff {n : ℕ} {σ : Equiv.Perm (Fin n)} {k : Fin n} :
    k ∈ nums σ ↔ k.val < (σ k).val := by
  simp [nums]

/-- For an involution, every element is fixed, a numerator, or a denominator. -/
lemma fixed_or_num_or_denom {n : ℕ} {σ : Equiv.Perm (Fin n)}
    (hinv : Function.Involutive σ) (k : Fin n) :
    σ k = k ∨ k ∈ nums σ ∨ σ k ∈ nums σ := by
  rcases lt_trichotomy k.val (σ k).val with h | h | h
  · exact Or.inr (Or.inl (mem_nums_iff.2 h))
  · exact Or.inl (Fin.ext h.symm)
  · exact Or.inr (Or.inr (mem_nums_iff.2 (by rw [hinv k]; exact h)))

/-- A valid involution has at most one fixed point and distinct edge labels;
the converse also holds. -/
theorem valid_iff_of_involutive {n : ℕ} {σ : Equiv.Perm (Fin n)}
    (hinv : Function.Involutive σ) :
    Valid σ ↔ (Finset.univ.filter fun x => σ x = x).card ≤ 1 ∧ Fantastic σ := by
  constructor
  · intro hV
    constructor
    · rw [Finset.card_le_one]
      intro a ha b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      apply hV
      rw [ratio_eq_one_iff.2 ha, ratio_eq_one_iff.2 hb]
    · intro a ha b hb hab
      have h1 : ratio σ (σ a) = ratio σ (σ b) := by
        rw [← label_eq_ratio hinv a, ← label_eq_ratio hinv b, hab]
      exact σ.injective (hV h1)
  · rintro ⟨hfix, hfant⟩
    rw [Finset.card_le_one] at hfix
    intro a b hab
    have hlabel_inv : ∀ k : Fin n, label σ k = (ratio σ k)⁻¹ := fun k => by
      unfold label ratio
      rw [inv_div]
    rcases fixed_or_num_or_denom hinv a with ha | ha | ha <;>
      rcases fixed_or_num_or_denom hinv b with hb | hb | hb
    · -- both fixed
      exact hfix a (by simp [ha]) b (by simp [hb])
    · -- a fixed, b numerator: ratio a = 1 < ratio b
      exfalso
      have h1 : ratio σ a = 1 := ratio_eq_one_iff.2 ha
      have h2 : 1 < ratio σ b := one_lt_ratio_iff.2 (mem_nums_iff.1 hb)
      linarith
    · -- a fixed, b denominator: ratio b < 1
      exfalso
      have h1 : ratio σ a = 1 := ratio_eq_one_iff.2 ha
      have h2 : ratio σ b < 1 := by
        rw [ratio_lt_one_iff]
        have hb2 : (σ b).val < (σ (σ b)).val := mem_nums_iff.1 hb
        rwa [hinv b] at hb2
      linarith
    · -- a numerator, b fixed
      exfalso
      have h1 : ratio σ b = 1 := ratio_eq_one_iff.2 hb
      have h2 : 1 < ratio σ a := one_lt_ratio_iff.2 (mem_nums_iff.1 ha)
      linarith
    · -- both numerators
      have h1 : label σ a = label σ b := by rw [hlabel_inv, hlabel_inv, hab]
      exact hfant ha hb h1
    · -- a numerator, b denominator
      exfalso
      have h1 : 1 < ratio σ a := one_lt_ratio_iff.2 (mem_nums_iff.1 ha)
      have h2 : ratio σ b < 1 := by
        rw [ratio_lt_one_iff]
        have hb2 : (σ b).val < (σ (σ b)).val := mem_nums_iff.1 hb
        rwa [hinv b] at hb2
      linarith
    · -- a denominator, b fixed
      exfalso
      have h1 : ratio σ b = 1 := ratio_eq_one_iff.2 hb
      have h2 : ratio σ a < 1 := by
        rw [ratio_lt_one_iff]
        have ha2 : (σ a).val < (σ (σ a)).val := mem_nums_iff.1 ha
        rwa [hinv a] at ha2
      linarith
    · -- a denominator, b numerator
      exfalso
      have h1 : 1 < ratio σ b := one_lt_ratio_iff.2 (mem_nums_iff.1 hb)
      have h2 : ratio σ a < 1 := by
        rw [ratio_lt_one_iff]
        have ha2 : (σ a).val < (σ (σ a)).val := mem_nums_iff.1 ha
        rwa [hinv a] at ha2
      linarith
    · -- both denominators
      have h1 : label σ (σ a) = label σ (σ b) := by
        rw [label_eq_ratio hinv (σ a), label_eq_ratio hinv (σ b), hinv a, hinv b, hab]
      exact σ.injective (hfant ha hb h1)

/-! ### Products of disjoint swaps over lists -/

section ProdSwap

variable {ι α : Type*} [DecidableEq α]

omit [DecidableEq α] in
lemma list_prod_perms_apply_of_forall_fix [DecidableEq ι] (l : List ι) (F : ι → Equiv.Perm α)
    (z : α) (h : ∀ i ∈ l, F i z = z) :
    (l.map F).prod z = z := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, Equiv.Perm.mul_apply,
      ih (fun b hb => h b (List.mem_cons_of_mem a hb)), h a List.mem_cons_self]

/-- A product of swaps of pairwise disjoint pairs sends `u i` to `v i`. -/
lemma list_prod_swap_apply_left [DecidableEq ι] (l : List ι) (u v : ι → α) (hnd : l.Nodup)
    (hd : ∀ i ∈ l, ∀ j ∈ l, i ≠ j → u i ≠ u j ∧ u i ≠ v j ∧ v i ≠ u j ∧ v i ≠ v j)
    (i : ι) (hi : i ∈ l) :
    ((l.map fun j => Equiv.swap (u j) (v j)).prod) (u i) = v i := by
  induction l with
  | nil => simp at hi
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, Equiv.Perm.mul_apply]
    by_cases hai : a = i
    · -- the head swap is the mover
      have hand : i ∉ l := by
        rw [← hai]
        exact (List.nodup_cons.1 hnd).1
      have hf : ∀ j ∈ l, Equiv.swap (u j) (v j) (u i) = u i := by
        intro j hj
        have hij : i ≠ j := fun h => hand (h ▸ hj)
        obtain ⟨h1, h2, -, -⟩ :=
          hd i (hai ▸ List.mem_cons_self) j (List.mem_cons_of_mem a hj) hij
        exact Equiv.swap_apply_of_ne_of_ne h1 h2
      rw [list_prod_perms_apply_of_forall_fix l _ (u i) hf, hai]
      exact Equiv.swap_apply_left _ _
    · have hi' : i ∈ l := (List.mem_cons.1 hi).resolve_left (fun h => hai h.symm)
      have hnd' : l.Nodup := (List.nodup_cons.1 hnd).2
      have hd' : ∀ i ∈ l, ∀ j ∈ l, i ≠ j → u i ≠ u j ∧ u i ≠ v j ∧ v i ≠ u j ∧ v i ≠ v j :=
        fun i hi j hj => hd i (List.mem_cons_of_mem a hi) j (List.mem_cons_of_mem a hj)
      rw [ih hnd' hd' hi']
      obtain ⟨-, -, h3, h4⟩ :=
        hd i (List.mem_cons_of_mem a hi') a List.mem_cons_self (Ne.symm hai)
      exact Equiv.swap_apply_of_ne_of_ne h3 h4

/-- A product of swaps of pairwise disjoint pairs sends `v i` to `u i`. -/
lemma list_prod_swap_apply_right [DecidableEq ι] (l : List ι) (u v : ι → α) (hnd : l.Nodup)
    (hd : ∀ i ∈ l, ∀ j ∈ l, i ≠ j → u i ≠ u j ∧ u i ≠ v j ∧ v i ≠ u j ∧ v i ≠ v j)
    (i : ι) (hi : i ∈ l) :
    ((l.map fun j => Equiv.swap (u j) (v j)).prod) (v i) = u i := by
  induction l with
  | nil => simp at hi
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, Equiv.Perm.mul_apply]
    by_cases hai : a = i
    · -- the head swap is the mover
      have hand : i ∉ l := by
        rw [← hai]
        exact (List.nodup_cons.1 hnd).1
      have hf : ∀ j ∈ l, Equiv.swap (u j) (v j) (v i) = v i := by
        intro j hj
        have hij : i ≠ j := fun h => hand (h ▸ hj)
        obtain ⟨-, -, h3, h4⟩ :=
          hd i (hai ▸ List.mem_cons_self) j (List.mem_cons_of_mem a hj) hij
        exact Equiv.swap_apply_of_ne_of_ne h3 h4
      rw [list_prod_perms_apply_of_forall_fix l _ (v i) hf, hai]
      exact Equiv.swap_apply_right _ _
    · have hi' : i ∈ l := (List.mem_cons.1 hi).resolve_left (fun h => hai h.symm)
      have hnd' : l.Nodup := (List.nodup_cons.1 hnd).2
      have hd' : ∀ i ∈ l, ∀ j ∈ l, i ≠ j → u i ≠ u j ∧ u i ≠ v j ∧ v i ≠ u j ∧ v i ≠ v j :=
        fun i hi j hj => hd i (List.mem_cons_of_mem a hi) j (List.mem_cons_of_mem a hj)
      rw [ih hnd' hd' hi']
      obtain ⟨h1, h2, -, -⟩ :=
        hd i (List.mem_cons_of_mem a hi') a List.mem_cons_self (Ne.symm hai)
      exact Equiv.swap_apply_of_ne_of_ne h1 h2

/-- A product of swaps fixes any point avoided by all the swaps. -/
lemma list_prod_swap_apply_of_not_mem [DecidableEq ι] (l : List ι) (u v : ι → α) (z : α)
    (hz : ∀ i ∈ l, z ≠ u i ∧ z ≠ v i) :
    ((l.map fun j => Equiv.swap (u j) (v j)).prod) z = z :=
  list_prod_perms_apply_of_forall_fix l _ z fun i hi =>
    Equiv.swap_apply_of_ne_of_ne (hz i hi).1 (hz i hi).2

end ProdSwap

/-! ### The flip construction -/

/-- The representatives of the pairs switched by `φ`: the smaller element of each
transposed pair of numerators. -/
def reps {n : ℕ} (σ φ : Equiv.Perm (Fin n)) : Finset (Fin n) :=
  (nums σ).filter fun x => φ x ≠ x ∧ x.val < (φ x).val

/-- The conjugating permutation: the product of the swaps `(σ x, φ x)` over the
representatives. -/
def conjPerm {n : ℕ} (σ φ : Equiv.Perm (Fin n)) : Equiv.Perm (Fin n) :=
  (((reps σ φ).sort (· ≤ ·)).map fun x => Equiv.swap (σ x) (φ x)).prod

/-- The new switching involution: the product of the swaps `(x, σ x)` over the
representatives. -/
def newSwitch {n : ℕ} (σ φ : Equiv.Perm (Fin n)) : Equiv.Perm (Fin n) :=
  (((reps σ φ).sort (· ≤ ·)).map fun x => Equiv.swap x (σ x)).prod

lemma mem_reps {n : ℕ} {σ φ : Equiv.Perm (Fin n)} {x : Fin n} :
    x ∈ reps σ φ ↔ x ∈ nums σ ∧ φ x ≠ x ∧ x.val < (φ x).val := by
  simp [reps]

/-- A switching involution maps numerators to numerators. -/
lemma switch_mapsTo_nums {n : ℕ} {σ φ : Equiv.Perm (Fin n)}
    (hφ : IsSwitch σ φ) {x : Fin n} (hx : x ∈ nums σ) : φ x ∈ nums σ := by
  by_contra hcon
  have h1 : φ (φ x) = φ x := hφ.2.1 _ hcon
  have h2 : φ x = x := by
    have h3 := hφ.1 x
    rw [h1] at h3
    exact h3
  have h4 : φ x ∈ nums σ := by
    rw [h2]
    exact hx
  exact hcon h4

/-- The image of a numerator is not a numerator. -/
lemma denom_not_mem_nums {n : ℕ} {σ : Equiv.Perm (Fin n)} (hσ : Function.Involutive σ)
    {x : Fin n} (hx : x ∈ nums σ) : σ x ∉ nums σ := by
  simp only [nums, Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
  rw [hσ x]
  exact le_of_lt (mem_nums_iff.1 hx)

/-- The pairs `(σ x, φ x)` for distinct representatives are pairwise disjoint. -/
lemma reps_four_distinct {n : ℕ} {σ φ : Equiv.Perm (Fin n)}
    (hσ : Function.Involutive σ) (hφ : IsSwitch σ φ)
    {x y : Fin n} (hx : x ∈ reps σ φ) (hy : y ∈ reps σ φ) (hxy : x ≠ y) :
    σ x ≠ σ y ∧ σ x ≠ φ y ∧ φ x ≠ σ y ∧ φ x ≠ φ y := by
  have hxn : x ∈ nums σ := (mem_reps.1 hx).1
  have hyn : y ∈ nums σ := (mem_reps.1 hy).1
  refine ⟨fun h => hxy (σ.injective h), ?_, ?_, fun h => hxy (hφ.1.injective h)⟩
  · intro h
    exact denom_not_mem_nums hσ hxn (h ▸ switch_mapsTo_nums hφ hyn)
  · intro h
    exact denom_not_mem_nums hσ hyn (h.symm ▸ switch_mapsTo_nums hφ hxn)

/-- The pairs `(x, σ x)` for distinct representatives are pairwise disjoint. -/
lemma reps_four_distinct' {n : ℕ} {σ φ : Equiv.Perm (Fin n)}
    (hσ : Function.Involutive σ) (_hφ : IsSwitch σ φ)
    {x y : Fin n} (hx : x ∈ reps σ φ) (hy : y ∈ reps σ φ) (hxy : x ≠ y) :
    x ≠ y ∧ x ≠ σ y ∧ σ x ≠ y ∧ σ x ≠ σ y := by
  have hxn : x ∈ nums σ := (mem_reps.1 hx).1
  have hyn : y ∈ nums σ := (mem_reps.1 hy).1
  refine ⟨hxy, ?_, ?_, fun h => hxy (σ.injective h)⟩
  · intro h
    exact denom_not_mem_nums hσ hyn (h ▸ hxn)
  · intro h
    exact denom_not_mem_nums hσ hxn (h.symm ▸ hyn)

/-- The pairs `(x, φ x)` for distinct representatives are pairwise disjoint. -/
lemma reps_four_distinct'' {n : ℕ} {σ φ : Equiv.Perm (Fin n)}
    (hφ : IsSwitch σ φ)
    {x y : Fin n} (hx : x ∈ reps σ φ) (hy : y ∈ reps σ φ) (hxy : x ≠ y) :
    x ≠ y ∧ x ≠ φ y ∧ φ x ≠ y ∧ φ x ≠ φ y := by
  have hltx : x.val < (φ x).val := (mem_reps.1 hx).2.2
  have hlty : y.val < (φ y).val := (mem_reps.1 hy).2.2
  refine ⟨hxy, ?_, ?_, fun h => hxy (hφ.1.injective h)⟩
  · intro h
    have h1 : φ x = y := (congrArg φ h).trans (hφ.1 y)
    rw [h1] at hltx
    rw [← h] at hlty
    exact absurd hltx (not_lt_of_gt hlty)
  · intro h
    have h1 : φ y = x := (congrArg φ h.symm).trans (hφ.1 x)
    rw [h] at hltx
    rw [h1] at hlty
    exact absurd hlty (not_lt_of_gt hltx)

lemma conjPerm_apply_left {n : ℕ} {σ φ : Equiv.Perm (Fin n)}
    (hσ : Function.Involutive σ) (hφ : IsSwitch σ φ)
    {x : Fin n} (hx : x ∈ reps σ φ) :
    conjPerm σ φ (σ x) = φ x := by
  unfold conjPerm
  exact list_prod_swap_apply_left _ _ _ (Finset.sort_nodup _ _)
    (fun i hi j hj hij => reps_four_distinct hσ hφ
      ((Finset.mem_sort _).1 hi) ((Finset.mem_sort _).1 hj) hij)
    x ((Finset.mem_sort _).2 hx)

lemma conjPerm_apply_right {n : ℕ} {σ φ : Equiv.Perm (Fin n)}
    (hσ : Function.Involutive σ) (hφ : IsSwitch σ φ)
    {x : Fin n} (hx : x ∈ reps σ φ) :
    conjPerm σ φ (φ x) = σ x := by
  unfold conjPerm
  exact list_prod_swap_apply_right _ _ _ (Finset.sort_nodup _ _)
    (fun i hi j hj hij => reps_four_distinct hσ hφ
      ((Finset.mem_sort _).1 hi) ((Finset.mem_sort _).1 hj) hij)
    x ((Finset.mem_sort _).2 hx)

lemma conjPerm_apply_of_not_mem {n : ℕ} {σ φ : Equiv.Perm (Fin n)} {z : Fin n}
    (hz : ∀ x ∈ reps σ φ, z ≠ σ x ∧ z ≠ φ x) :
    conjPerm σ φ z = z := by
  unfold conjPerm
  exact list_prod_swap_apply_of_not_mem _ _ _ z fun i hi =>
    hz i ((Finset.mem_sort _).1 hi)

lemma newSwitch_apply_left {n : ℕ} {σ φ : Equiv.Perm (Fin n)}
    (hσ : Function.Involutive σ) (hφ : IsSwitch σ φ)
    {x : Fin n} (hx : x ∈ reps σ φ) :
    newSwitch σ φ x = σ x := by
  unfold newSwitch
  exact list_prod_swap_apply_left _ _ _ (Finset.sort_nodup _ _)
    (fun i hi j hj hij => reps_four_distinct' hσ hφ
      ((Finset.mem_sort _).1 hi) ((Finset.mem_sort _).1 hj) hij)
    x ((Finset.mem_sort _).2 hx)

lemma newSwitch_apply_right {n : ℕ} {σ φ : Equiv.Perm (Fin n)}
    (hσ : Function.Involutive σ) (hφ : IsSwitch σ φ)
    {x : Fin n} (hx : x ∈ reps σ φ) :
    newSwitch σ φ (σ x) = x := by
  unfold newSwitch
  exact list_prod_swap_apply_right _ _ _ (Finset.sort_nodup _ _)
    (fun i hi j hj hij => reps_four_distinct' hσ hφ
      ((Finset.mem_sort _).1 hi) ((Finset.mem_sort _).1 hj) hij)
    x ((Finset.mem_sort _).2 hx)

lemma newSwitch_apply_of_not_mem {n : ℕ} {σ φ : Equiv.Perm (Fin n)} {z : Fin n}
    (hz : ∀ x ∈ reps σ φ, z ≠ x ∧ z ≠ σ x) :
    newSwitch σ φ z = z := by
  unfold newSwitch
  exact list_prod_swap_apply_of_not_mem _ _ _ z fun i hi =>
    hz i ((Finset.mem_sort _).1 hi)

lemma conjPerm_involutive {n : ℕ} {σ φ : Equiv.Perm (Fin n)}
    (hσ : Function.Involutive σ) (hφ : IsSwitch σ φ) :
    Function.Involutive (conjPerm σ φ) := by
  intro z
  by_cases hz : ∃ x ∈ reps σ φ, σ x = z ∨ φ x = z
  · obtain ⟨x, hx, hxz⟩ := hz
    cases hxz with
    | inl h =>
      rw [← h, conjPerm_apply_left hσ hφ hx, conjPerm_apply_right hσ hφ hx]
    | inr h =>
      rw [← h, conjPerm_apply_right hσ hφ hx, conjPerm_apply_left hσ hφ hx]
  · push Not at hz
    have h1 : conjPerm σ φ z = z :=
      conjPerm_apply_of_not_mem fun x hx => by
        obtain ⟨h1, h2⟩ := hz x hx
        exact ⟨fun h => h1 h.symm, fun h => h2 h.symm⟩
    rw [h1, h1]

lemma newSwitch_involutive {n : ℕ} {σ φ : Equiv.Perm (Fin n)}
    (hσ : Function.Involutive σ) (hφ : IsSwitch σ φ) :
    Function.Involutive (newSwitch σ φ) := by
  intro z
  by_cases hz : ∃ x ∈ reps σ φ, x = z ∨ σ x = z
  · obtain ⟨x, hx, hxz⟩ := hz
    cases hxz with
    | inl h =>
      rw [← h, newSwitch_apply_left hσ hφ hx, newSwitch_apply_right hσ hφ hx]
    | inr h =>
      rw [← h, newSwitch_apply_right hσ hφ hx, newSwitch_apply_left hσ hφ hx]
  · push Not at hz
    have h1 : newSwitch σ φ z = z :=
      newSwitch_apply_of_not_mem fun x hx => by
        obtain ⟨h1, h2⟩ := hz x hx
        exact ⟨fun h => h1 h.symm, fun h => h2 h.symm⟩
    rw [h1, h1]

/-- The flipped involution `π σ π` is involutive. -/
lemma flip1_involutive {n : ℕ} {σ φ : Equiv.Perm (Fin n)}
    (hσ : Function.Involutive σ) (hφ : IsSwitch σ φ) :
    Function.Involutive (conjPerm σ φ * σ * conjPerm σ φ) := by
  intro z
  have hπ := conjPerm_involutive hσ hφ
  simp only [Equiv.Perm.mul_apply]
  rw [hπ, hσ, hπ]

/-- Fixed points of the flipped involution are the `π`-images of fixed points of `σ`. -/
lemma flip1_fixed_iff {n : ℕ} {σ φ : Equiv.Perm (Fin n)}
    (hσ : Function.Involutive σ) (hφ : IsSwitch σ φ) (z : Fin n) :
    (conjPerm σ φ * σ * conjPerm σ φ) z = z ↔ σ (conjPerm σ φ z) = conjPerm σ φ z := by
  have hπ := conjPerm_involutive hσ hφ
  simp only [Equiv.Perm.mul_apply]
  constructor
  · intro h
    have h2 := congrArg (⇑(conjPerm σ φ)) h
    rw [hπ] at h2
    exact h2
  · intro h
    rw [h, hπ]

/-- The flipped involution has the same number of fixed points as `σ`. -/
lemma flip1_fixed_card {n : ℕ} {σ φ : Equiv.Perm (Fin n)}
    (hσ : Function.Involutive σ) (hφ : IsSwitch σ φ) :
    (Finset.univ.filter fun x => (conjPerm σ φ * σ * conjPerm σ φ) x = x).card =
    (Finset.univ.filter fun x => σ x = x).card := by
  have hπ := conjPerm_involutive hσ hφ
  apply Finset.card_bij (fun x _ => conjPerm σ φ x)
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact (flip1_fixed_iff hσ hφ x).1 hx
  · intro x _ y _ hxy
    exact hπ.injective hxy
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    refine ⟨conjPerm σ φ y, ?_, hπ y⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [flip1_fixed_iff hσ hφ, hπ]
    exact hy

/-- On a representative `x`, the flipped involution acts as `φ`. -/
lemma flip1_apply_of_mem_reps {n : ℕ} {σ φ : Equiv.Perm (Fin n)}
    (hσ : Function.Involutive σ) (hφ : IsSwitch σ φ)
    {x : Fin n} (hx : x ∈ reps σ φ) :
    (conjPerm σ φ * σ * conjPerm σ φ) x = φ x := by
  have hx1 : conjPerm σ φ x = x := by
    apply conjPerm_apply_of_not_mem
    intro i hi
    have hxn := (mem_reps.1 hx).1
    have hin := (mem_reps.1 hi).1
    constructor
    · intro h
      exact denom_not_mem_nums hσ hin (h ▸ hxn)
    · intro h
      have h1 : φ x = i := (congrArg φ h).trans (hφ.1 i)
      have hlt1 : i.val < (φ i).val := (mem_reps.1 hi).2.2
      have hlt2 : x.val < (φ x).val := (mem_reps.1 hx).2.2
      rw [← h] at hlt1
      rw [h1] at hlt2
      exact absurd hlt1 (not_lt_of_gt hlt2)
  simp only [Equiv.Perm.mul_apply]
  rw [hx1, conjPerm_apply_left hσ hφ hx]

/-- On the denominator `σ x` of a representative, the flipped involution acts as
`σ ∘ φ`. -/
lemma flip1_apply_denom_of_mem_reps {n : ℕ} {σ φ : Equiv.Perm (Fin n)}
    (hσ : Function.Involutive σ) (hφ : IsSwitch σ φ)
    {x : Fin n} (hx : x ∈ reps σ φ) :
    (conjPerm σ φ * σ * conjPerm σ φ) (σ x) = σ (φ x) := by
  have hx1 : conjPerm σ φ (σ (φ x)) = σ (φ x) := by
    apply conjPerm_apply_of_not_mem
    intro i hi
    constructor
    · intro h
      have h1 : φ x = i := σ.injective h
      rw [← h1] at hi
      obtain ⟨-, -, hlt⟩ := mem_reps.1 hi
      rw [hφ.1 x] at hlt
      have hlt2 : x.val < (φ x).val := (mem_reps.1 hx).2.2
      exact absurd hlt (not_lt_of_gt hlt2)
    · intro h
      have h1 : σ (φ x) ∉ nums σ :=
        denom_not_mem_nums hσ (switch_mapsTo_nums hφ (mem_reps.1 hx).1)
      rw [h] at h1
      exact h1 (switch_mapsTo_nums hφ (mem_reps.1 hi).1)
  simp only [Equiv.Perm.mul_apply]
  rw [conjPerm_apply_left hσ hφ hx, hx1]

/-- Points moved by the new switching involution are numerators of the flipped
involution. -/
lemma newSwitch_mem_nums_flip {n : ℕ} {σ φ : Equiv.Perm (Fin n)}
    (hσ : Function.Involutive σ) (hφ : IsSwitch σ φ) {z : Fin n}
    (hz : newSwitch σ φ z ≠ z) :
    z ∈ nums (conjPerm σ φ * σ * conjPerm σ φ) := by
  have hmove : ∃ x ∈ reps σ φ, z = x ∨ z = σ x := by
    by_contra hcon
    push Not at hcon
    exact hz (newSwitch_apply_of_not_mem hcon)
  obtain ⟨x, hx, h | h⟩ := hmove
  · rw [h, mem_nums_iff, flip1_apply_of_mem_reps hσ hφ hx]
    exact (mem_reps.1 hx).2.2
  · rw [h, mem_nums_iff, flip1_apply_denom_of_mem_reps hσ hφ hx]
    have hlt : x.val < (φ x).val := (mem_reps.1 hx).2.2
    have hlabel : label σ x = label σ (φ x) := (hφ.2.2 x (mem_reps.1 hx).1).symm
    exact label_order_transfer hlabel hlt

/-- The new switching involution preserves labels of the flipped involution. -/
lemma flip2_label {n : ℕ} {σ φ : Equiv.Perm (Fin n)}
    (hσ : Function.Involutive σ) (hφ : IsSwitch σ φ) {z : Fin n}
    (_hz : z ∈ nums (conjPerm σ φ * σ * conjPerm σ φ)) :
    label (conjPerm σ φ * σ * conjPerm σ φ) (newSwitch σ φ z) =
    label (conjPerm σ φ * σ * conjPerm σ φ) z := by
  by_cases hmove : ∃ x ∈ reps σ φ, z = x ∨ z = σ x
  · obtain ⟨x, hx, h | h⟩ := hmove
    · rw [h, newSwitch_apply_left hσ hφ hx]
      unfold label
      rw [flip1_apply_denom_of_mem_reps hσ hφ hx, flip1_apply_of_mem_reps hσ hφ hx]
      have hl := hφ.2.2 x (mem_reps.1 hx).1
      unfold label at hl
      rw [div_eq_div_iff (val_add_one_pos _).ne' (val_add_one_pos _).ne'] at hl ⊢
      rw [mul_comm ((σ x).val + 1 : ℚ) ((φ x).val + 1 : ℚ)]
      exact hl
    · rw [h, newSwitch_apply_right hσ hφ hx]
      unfold label
      rw [flip1_apply_denom_of_mem_reps hσ hφ hx, flip1_apply_of_mem_reps hσ hφ hx]
      have hl := hφ.2.2 x (mem_reps.1 hx).1
      unfold label at hl
      rw [div_eq_div_iff (val_add_one_pos _).ne' (val_add_one_pos _).ne'] at hl ⊢
      rw [mul_comm ((σ x).val + 1 : ℚ) ((φ x).val + 1 : ℚ)]
      exact hl.symm
  · push Not at hmove
    have h1 : newSwitch σ φ z = z := newSwitch_apply_of_not_mem hmove
    rw [h1]

/-- The representatives of the flipped pair are the original representatives. -/
lemma reps_flip {n : ℕ} {σ φ : Equiv.Perm (Fin n)}
    (hσ : Function.Involutive σ) (hφ : IsSwitch σ φ) :
    reps (conjPerm σ φ * σ * conjPerm σ φ) (newSwitch σ φ) = reps σ φ := by
  ext z
  simp only [mem_reps]
  constructor
  · intro ⟨hzn, hzne, hzlt⟩
    have hmove : ∃ x ∈ reps σ φ, z = x ∨ z = σ x := by
      by_contra hcon
      push Not at hcon
      exact hzne (newSwitch_apply_of_not_mem hcon)
    obtain ⟨x, hx, h | h⟩ := hmove
    · rw [h]
      exact mem_reps.1 hx
    · exfalso
      rw [h, newSwitch_apply_right hσ hφ hx] at hzlt
      have hlt : x.val < (σ x).val := mem_nums_iff.1 (mem_reps.1 hx).1
      exact absurd hlt (not_lt_of_gt hzlt)
  · intro hz
    have hzr : z ∈ reps σ φ := mem_reps.2 hz
    obtain ⟨hzn, hzne, hzlt⟩ := hz
    have hz2 : z ≠ σ z := fun h =>
      (ne_of_lt (mem_nums_iff.1 hzn)) (congrArg Fin.val h)
    refine ⟨?_, ?_, ?_⟩
    · exact newSwitch_mem_nums_flip hσ hφ (by rw [newSwitch_apply_left hσ hφ hzr]; exact fun h => hz2 h.symm)
    · rw [newSwitch_apply_left hσ hφ hzr]
      exact fun h => hz2 h.symm
    · rw [newSwitch_apply_left hσ hφ hzr]
      exact mem_nums_iff.1 hzn

/-- The conjugating permutation of the flipped pair is the original one. -/
lemma conjPerm_flip {n : ℕ} {σ φ : Equiv.Perm (Fin n)}
    (hσ : Function.Involutive σ) (hφ : IsSwitch σ φ) :
    conjPerm (conjPerm σ φ * σ * conjPerm σ φ) (newSwitch σ φ) = conjPerm σ φ := by
  show (((reps (conjPerm σ φ * σ * conjPerm σ φ) (newSwitch σ φ)).sort (· ≤ ·)).map
      fun x => Equiv.swap ((conjPerm σ φ * σ * conjPerm σ φ) x) (newSwitch σ φ x)).prod =
    (((reps σ φ).sort (· ≤ ·)).map fun x => Equiv.swap (σ x) (φ x)).prod
  rw [reps_flip hσ hφ]
  congr 1
  apply List.map_congr_left
  intro x hx
  rw [flip1_apply_of_mem_reps hσ hφ ((Finset.mem_sort _).1 hx),
    newSwitch_apply_left hσ hφ ((Finset.mem_sort _).1 hx), Equiv.swap_comm]

/-- A switching involution is the product of its own transpositions. -/
lemma eq_prod_swap_self {n : ℕ} {σ φ : Equiv.Perm (Fin n)}
    (hφ : IsSwitch σ φ) :
    φ = (((reps σ φ).sort (· ≤ ·)).map fun x => Equiv.swap x (φ x)).prod := by
  ext z
  by_cases hz : ∃ x ∈ reps σ φ, x = z ∨ φ x = z
  · obtain ⟨x, hx, h | h⟩ := hz
    · rw [← h, list_prod_swap_apply_left _ _ _ (Finset.sort_nodup _ (· ≤ ·))
        (fun i hi j hj hij => reps_four_distinct'' hφ
          ((Finset.mem_sort _).1 hi) ((Finset.mem_sort _).1 hj) hij)
        x ((Finset.mem_sort _).2 hx)]
    · rw [← h, list_prod_swap_apply_right _ _ _ (Finset.sort_nodup _ (· ≤ ·))
        (fun i hi j hj hij => reps_four_distinct'' hφ
          ((Finset.mem_sort _).1 hi) ((Finset.mem_sort _).1 hj) hij)
        x ((Finset.mem_sort _).2 hx), hφ.1 x]
  · push Not at hz
    have h2 : φ z = z := by
      by_contra hzne
      have hzn : z ∈ nums σ := by
        by_contra hcon
        exact hzne (hφ.2.1 z hcon)
      have hφzn : φ z ∈ nums σ := switch_mapsTo_nums hφ hzn
      rcases lt_trichotomy z.val (φ z).val with hlt | heq | hgt
      · exact (hz z (mem_reps.2 ⟨hzn, hzne, hlt⟩)).1 rfl
      · exact hzne (Fin.ext heq).symm
      · have hφzr : φ z ∈ reps σ φ := by
          apply mem_reps.2
          refine ⟨hφzn, ?_, ?_⟩
          · rw [hφ.1 z]
            exact fun h => hzne h.symm
          · rw [hφ.1 z]
            exact hgt
        exact (hz (φ z) hφzr).2 (hφ.1 z)
    have h3 : (((reps σ φ).sort (· ≤ ·)).map fun x => Equiv.swap x (φ x)).prod z = z :=
      list_prod_swap_apply_of_not_mem ((reps σ φ).sort (· ≤ ·)) (fun x => x)
        (fun x => φ x) z fun i hi => by
          obtain ⟨h1, h2'⟩ := hz i ((Finset.mem_sort (· ≤ ·)).1 hi)
          exact ⟨Ne.symm h1, Ne.symm h2'⟩
    rw [h2, h3]

/-- The new switching involution of the flipped pair is the original switching
involution. -/
lemma newSwitch_flip {n : ℕ} {σ φ : Equiv.Perm (Fin n)}
    (hσ : Function.Involutive σ) (hφ : IsSwitch σ φ) :
    newSwitch (conjPerm σ φ * σ * conjPerm σ φ) (newSwitch σ φ) = φ := by
  show (((reps (conjPerm σ φ * σ * conjPerm σ φ) (newSwitch σ φ)).sort (· ≤ ·)).map
      fun x => Equiv.swap x ((conjPerm σ φ * σ * conjPerm σ φ) x)).prod = φ
  rw [reps_flip hσ hφ]
  conv_rhs => rw [eq_prod_swap_self hφ]
  congr 1
  apply List.map_congr_left
  intro x hx
  rw [flip1_apply_of_mem_reps hσ hφ ((Finset.mem_sort _).1 hx)]

/-- The flip on pairs `(σ, φ)`. -/
def flipPair {n : ℕ} (p : Equiv.Perm (Fin n) × Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin n) × Equiv.Perm (Fin n) :=
  (conjPerm p.1 p.2 * p.1 * conjPerm p.1 p.2, newSwitch p.1 p.2)

/-- The flip is an involution on valid pairs. -/
lemma flipPair_involutive_on {n : ℕ} {σ φ : Equiv.Perm (Fin n)}
    (hσ : Function.Involutive σ) (hφ : IsSwitch σ φ) :
    flipPair (flipPair (σ, φ)) = (σ, φ) := by
  have hπ : Function.Involutive (conjPerm σ φ) := conjPerm_involutive hσ hφ
  have h1 : conjPerm (conjPerm σ φ * σ * conjPerm σ φ) (newSwitch σ φ) = conjPerm σ φ :=
    conjPerm_flip hσ hφ
  have h2 : newSwitch (conjPerm σ φ * σ * conjPerm σ φ) (newSwitch σ φ) = φ :=
    newSwitch_flip hσ hφ
  have hπ2 : conjPerm σ φ * conjPerm σ φ = 1 := by
    ext z
    simp only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
    exact congrArg Fin.val (hπ z)
  unfold flipPair
  dsimp only
  rw [h1, h2]
  congr 1
  calc conjPerm σ φ * (conjPerm σ φ * σ * conjPerm σ φ) * conjPerm σ φ
      = (conjPerm σ φ * conjPerm σ φ) * σ * (conjPerm σ φ * conjPerm σ φ) := by group
    _ = σ := by rw [hπ2, one_mul, mul_one]

/-- The flip preserves membership in the vertex-switching set. -/
lemma flipPair_mem {n : ℕ} {σ φ : Equiv.Perm (Fin n)}
    (hσ : IsVertex σ) (hφ : IsSwitch σ φ) :
    IsVertex (conjPerm σ φ * σ * conjPerm σ φ) ∧
    IsSwitch (conjPerm σ φ * σ * conjPerm σ φ) (newSwitch σ φ) := by
  obtain ⟨hσv, hσf⟩ := hσ
  constructor
  · exact ⟨flip1_involutive hσv hφ, by rw [flip1_fixed_card hσv hφ]; exact hσf⟩
  · refine ⟨newSwitch_involutive hσv hφ, ?_, fun z hz => flip2_label hσv hφ hz⟩
    intro z hz
    by_contra hcon
    exact hz (newSwitch_mem_nums_flip hσv hφ hcon)

/-- A fixed point of the flip has trivial switching involution. -/
lemma flipPair_eq_self_iff {n : ℕ} {σ φ : Equiv.Perm (Fin n)}
    (hσ : Function.Involutive σ) (hφ : IsSwitch σ φ)
    (h : flipPair (σ, φ) = (σ, φ)) : φ = 1 := by
  have h2 : newSwitch σ φ = φ := congrArg Prod.snd h
  have hreps : reps σ φ = ∅ := by
    by_contra hne
    obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.2 hne
    have h1 : φ x = σ x := by
      rw [← h2]
      exact newSwitch_apply_left hσ hφ hx
    have h2a : φ x ∈ nums σ := switch_mapsTo_nums hφ (mem_reps.1 hx).1
    rw [h1] at h2a
    exact denom_not_mem_nums hσ (mem_reps.1 hx).1 h2a
  rw [← h2]
  unfold newSwitch
  simp [hreps]

/-- Any pair with trivial switching involution is a fixed point of the flip. -/
lemma flipPair_eq_self_of_eq_one {n : ℕ} {σ φ : Equiv.Perm (Fin n)} (h : φ = 1) :
    flipPair (σ, φ) = (σ, φ) := by
  subst h
  have hreps : reps σ 1 = ∅ := by
    ext x
    simp [reps]
  have hc : conjPerm σ 1 = 1 := by
    unfold conjPerm
    simp [hreps]
  have hn : newSwitch σ 1 = 1 := by
    unfold newSwitch
    simp [hreps]
  show (conjPerm σ 1 * σ * conjPerm σ 1, newSwitch σ 1) = (σ, 1)
  rw [hc, hn, one_mul, mul_one]

/-! ### Counting switching involutions modulo two -/

/-- The identity is a switching involution. -/
lemma isSwitch_id {n : ℕ} {σ : Equiv.Perm (Fin n)} : IsSwitch σ (1 : Equiv.Perm (Fin n)) := by
  refine ⟨fun x => ?_, fun x _ => ?_, fun x _ => ?_⟩
  · show (1 : Equiv.Perm (Fin n)) ((1 : Equiv.Perm (Fin n)) x) = x
    simp
  · simp
  · simp

/-- An involution squares to one. -/
lemma Perm_mul_self_eq_one_of_involutive {n : ℕ} {ψ : Equiv.Perm (Fin n)}
    (h : Function.Involutive ψ) : ψ * ψ = 1 := by
  ext x
  simp only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
  exact congrArg Fin.val (h x)

/-- Swaps are involutions. -/
lemma swap_involutive {α : Type*} [DecidableEq α] (a b : α) :
    Function.Involutive (Equiv.swap a b) := fun x => by
  have h := Equiv.swap_swap a b
  have h2 := Equiv.ext_iff.1 h x
  simp only [Equiv.trans_apply, Equiv.refl_apply] at h2
  exact h2

/-- A fantastic vertex admits only the trivial switching involution. -/
theorem card_switch_eq_one_of_fantastic {n : ℕ} {σ : Equiv.Perm (Fin n)}
    (hf : Fantastic σ) : Fintype.card {φ : Equiv.Perm (Fin n) // IsSwitch σ φ} = 1 := by
  have hall : ∀ φ : Equiv.Perm (Fin n), IsSwitch σ φ → φ = 1 := by
    intro φ hφ
    apply Equiv.Perm.ext_iff.2
    intro x
    by_cases hx : x ∈ nums σ
    · have h1 : label σ (φ x) = label σ x := hφ.2.2 x hx
      have h2 : φ x ∈ nums σ := switch_mapsTo_nums hφ hx
      have h3 : φ x = x := hf h2 hx h1
      rw [h3]
      simp
    · have h3 : φ x = x := hφ.2.1 x hx
      rw [h3]
      simp
  have hle : Fintype.card {φ : Equiv.Perm (Fin n) // IsSwitch σ φ} ≤ 1 :=
    Fintype.card_le_one_iff.2 fun φ ψ =>
      Subtype.ext ((hall φ.1 φ.2).trans (hall ψ.1 ψ.2).symm)
  have hpos : 0 < Fintype.card {φ : Equiv.Perm (Fin n) // IsSwitch σ φ} :=
    Fintype.card_pos_iff.2 ⟨⟨1, isSwitch_id⟩⟩
  omega

/-- Conjugating a switching involution by the swap of two equal-labelled numerators
yields a switching involution. -/
lemma conj_isSwitch {n : ℕ} {σ : Equiv.Perm (Fin n)}
    {a b : Fin n} (ha : a ∈ nums σ) (hb : b ∈ nums σ) (hab : label σ a = label σ b)
    {φ : Equiv.Perm (Fin n)} (hφ : IsSwitch σ φ) :
    IsSwitch σ (Equiv.swap a b * φ * Equiv.swap a b) := by
  set c := Equiv.swap a b with hc
  have hc_a : c a = b := Equiv.swap_apply_left a b
  have hc_b : c b = a := Equiv.swap_apply_right a b
  have hc_fix : ∀ x : Fin n, x ≠ a → x ≠ b → c x = x := fun x hxa hxb =>
    Equiv.swap_apply_of_ne_of_ne hxa hxb
  have hc_invol : Function.Involutive c := swap_involutive a b
  have hc_nums : ∀ x : Fin n, c x ∈ nums σ ↔ x ∈ nums σ := by
    intro x
    by_cases hxa : x = a
    · subst hxa
      rw [hc_a]
      exact iff_of_true hb ha
    by_cases hxb : x = b
    · subst hxb
      rw [hc_b]
      exact iff_of_true ha hb
    rw [hc_fix x hxa hxb]
  have hc_label : ∀ x : Fin n, x ∈ nums σ → label σ (c x) = label σ x := by
    intro x hx
    by_cases hxa : x = a
    · subst hxa
      rw [hc_a]
      exact hab.symm
    by_cases hxb : x = b
    · subst hxb
      rw [hc_b]
      exact hab
    rw [hc_fix x hxa hxb]
  refine ⟨?_, ?_, ?_⟩
  · intro x
    simp only [Equiv.Perm.mul_apply]
    rw [hc_invol, hφ.1, hc_invol]
  · intro x hx
    have h1 : c x ∉ nums σ := by
      rw [hc_nums]
      exact hx
    simp only [Equiv.Perm.mul_apply]
    rw [hφ.2.1 _ h1, hc_invol]
  · intro x hx
    have h1 : c x ∈ nums σ := (hc_nums x).2 hx
    have h2 : φ (c x) ∈ nums σ := switch_mapsTo_nums hφ h1
    simp only [Equiv.Perm.mul_apply]
    rw [hc_label _ h2, hφ.2.2 _ h1, hc_label _ hx]

/-! ### Removing two edges from an involution -/

/-- The involution obtained from `σ` by removing the two edges through `a` and `b`. -/
def rho {n : ℕ} (σ : Equiv.Perm (Fin n)) (a b : Fin n) : Equiv.Perm (Fin n) :=
  Equiv.swap a (σ a) * Equiv.swap b (σ b) * σ

lemma rho_apply_a {n : ℕ} {σ : Equiv.Perm (Fin n)} (hσ : Function.Involutive σ)
    {a b : Fin n} (ha : a ∈ nums σ) (hb : b ∈ nums σ) (hne : a ≠ b) :
    rho σ a b a = a := by
  have h1 : σ a ≠ b := fun h => denom_not_mem_nums hσ ha (h ▸ hb)
  have h2 : σ a ≠ σ b := fun h => hne (σ.injective h)
  simp only [rho, Equiv.Perm.mul_apply]
  rw [Equiv.swap_apply_of_ne_of_ne h1 h2, Equiv.swap_apply_right]

lemma rho_apply_σa {n : ℕ} {σ : Equiv.Perm (Fin n)} (hσ : Function.Involutive σ)
    {a b : Fin n} (ha : a ∈ nums σ) (hb : b ∈ nums σ) (hne : a ≠ b) :
    rho σ a b (σ a) = σ a := by
  have h2 : a ≠ σ b := fun h => denom_not_mem_nums hσ hb (h ▸ ha)
  simp only [rho, Equiv.Perm.mul_apply]
  rw [hσ a, Equiv.swap_apply_of_ne_of_ne hne h2, Equiv.swap_apply_left]

lemma rho_apply_b {n : ℕ} {σ : Equiv.Perm (Fin n)} (hσ : Function.Involutive σ)
    {a b : Fin n} (ha : a ∈ nums σ) (hb : b ∈ nums σ) (hne : a ≠ b) :
    rho σ a b b = b := by
  have h2 : b ≠ σ a := fun h => denom_not_mem_nums hσ ha (h ▸ hb)
  simp only [rho, Equiv.Perm.mul_apply]
  rw [Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hne.symm h2]

lemma rho_apply_σb {n : ℕ} {σ : Equiv.Perm (Fin n)} (hσ : Function.Involutive σ)
    {a b : Fin n} (ha : a ∈ nums σ) (hb : b ∈ nums σ) (hne : a ≠ b) :
    rho σ a b (σ b) = σ b := by
  have h1 : σ b ≠ a := fun h => denom_not_mem_nums hσ hb (h ▸ ha)
  have h2 : σ b ≠ σ a := fun h => hne.symm (σ.injective h)
  simp only [rho, Equiv.Perm.mul_apply]
  rw [hσ b, Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne h1 h2]

lemma rho_apply_of_not_mem {n : ℕ} {σ : Equiv.Perm (Fin n)} (hσ : Function.Involutive σ)
    {a b x : Fin n} (hx : x ≠ a ∧ x ≠ σ a ∧ x ≠ b ∧ x ≠ σ b) :
    rho σ a b x = σ x := by
  have h1 : σ x ≠ b := fun h => hx.2.2.2 ((hσ x).symm.trans (congrArg σ h))
  have h2 : σ x ≠ σ b := fun h => hx.2.2.1 (σ.injective h)
  have h3 : σ x ≠ a := fun h => hx.2.1 ((hσ x).symm.trans (congrArg σ h))
  have h4 : σ x ≠ σ a := fun h => hx.1 (σ.injective h)
  simp only [rho, Equiv.Perm.mul_apply]
  rw [Equiv.swap_apply_of_ne_of_ne h1 h2, Equiv.swap_apply_of_ne_of_ne h3 h4]

lemma rho_involutive {n : ℕ} {σ : Equiv.Perm (Fin n)} (hσ : Function.Involutive σ)
    {a b : Fin n} (ha : a ∈ nums σ) (hb : b ∈ nums σ) (hne : a ≠ b) :
    Function.Involutive (rho σ a b) := by
  intro z
  by_cases hz : z = a ∨ z = σ a ∨ z = b ∨ z = σ b
  · rcases hz with rfl | rfl | rfl | rfl
    · rw [rho_apply_a hσ ha hb hne, rho_apply_a hσ ha hb hne]
    · rw [rho_apply_σa hσ ha hb hne, rho_apply_σa hσ ha hb hne]
    · rw [rho_apply_b hσ ha hb hne, rho_apply_b hσ ha hb hne]
    · rw [rho_apply_σb hσ ha hb hne, rho_apply_σb hσ ha hb hne]
  · push Not at hz
    have h1 : rho σ a b z = σ z := rho_apply_of_not_mem hσ hz
    have h2 : σ z ≠ a ∧ σ z ≠ σ a ∧ σ z ≠ b ∧ σ z ≠ σ b := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro h
        exact hz.2.1 ((hσ z).symm.trans (congrArg σ h))
      · intro h
        exact hz.1 (σ.injective h)
      · intro h
        exact hz.2.2.2 ((hσ z).symm.trans (congrArg σ h))
      · intro h
        exact hz.2.2.1 (σ.injective h)
    rw [h1, rho_apply_of_not_mem hσ h2, hσ z]

lemma not_mem_four_of_mem_nums_rho {n : ℕ} {σ : Equiv.Perm (Fin n)}
    (hσ : Function.Involutive σ) {a b x : Fin n}
    (ha : a ∈ nums σ) (hb : b ∈ nums σ) (hne : a ≠ b)
    (hx : x ∈ nums (rho σ a b)) :
    x ≠ a ∧ x ≠ σ a ∧ x ≠ b ∧ x ≠ σ b := by
  have h := mem_nums_iff.1 hx
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro hcon <;> subst hcon
  · rw [rho_apply_a hσ ha hb hne] at h
    exact absurd h (lt_irrefl _)
  · rw [rho_apply_σa hσ ha hb hne] at h
    exact absurd h (lt_irrefl _)
  · rw [rho_apply_b hσ ha hb hne] at h
    exact absurd h (lt_irrefl _)
  · rw [rho_apply_σb hσ ha hb hne] at h
    exact absurd h (lt_irrefl _)

lemma nums_rho {n : ℕ} {σ : Equiv.Perm (Fin n)} (hσ : Function.Involutive σ)
    {a b : Fin n} (ha : a ∈ nums σ) (hb : b ∈ nums σ) (hne : a ≠ b) :
    nums (rho σ a b) = (nums σ).filter fun x => x ≠ a ∧ x ≠ b := by
  ext x
  simp only [mem_nums_iff, Finset.mem_filter]
  constructor
  · intro hx
    have hx1 := not_mem_four_of_mem_nums_rho hσ ha hb hne (mem_nums_iff.2 hx)
    rw [rho_apply_of_not_mem hσ hx1] at hx
    exact ⟨hx, hx1.1, hx1.2.2.1⟩
  · intro ⟨hx, hxa, hxb⟩
    have hx1 : x ≠ a ∧ x ≠ σ a ∧ x ≠ b ∧ x ≠ σ b := by
      refine ⟨hxa, ?_, hxb, ?_⟩
      · intro h
        exact denom_not_mem_nums hσ ha (h ▸ mem_nums_iff.2 hx)
      · intro h
        exact denom_not_mem_nums hσ hb (h ▸ mem_nums_iff.2 hx)
    rw [rho_apply_of_not_mem hσ hx1]
    exact hx

lemma label_rho {n : ℕ} {σ : Equiv.Perm (Fin n)} (hσ : Function.Involutive σ)
    {a b x : Fin n} (ha : a ∈ nums σ) (hb : b ∈ nums σ) (hne : a ≠ b)
    (hx : x ∈ nums (rho σ a b)) :
    label (rho σ a b) x = label σ x := by
  have hx1 := not_mem_four_of_mem_nums_rho hσ ha hb hne hx
  unfold label
  rw [rho_apply_of_not_mem hσ hx1]

/-! ### The fixed-point decomposition for the conjugation involution -/

/-- Package an involutive function as a permutation. -/
def permOfInvolutive {α : Type*} (f : α → α) (hf : Function.Involutive f) : Equiv.Perm α where
  toFun := f
  invFun := f
  left_inv := hf
  right_inv := hf

@[simp]
lemma permOfInvolutive_apply {α : Type*} (f : α → α) (hf : Function.Involutive f) (x : α) :
    permOfInvolutive f hf x = f x := rfl

/-- If `c * ψ = ψ * c` for `c = swap a b`, then `ψ` preserves the pair `{a, b}`. -/
lemma fixed_perm_ab {n : ℕ} {σ ψ : Equiv.Perm (Fin n)}
    {a b : Fin n} (_ha : a ∈ nums σ) (_hb : b ∈ nums σ) (_hab : label σ a = label σ b)
    (hne : a ≠ b)
    (_hψ : IsSwitch σ ψ) (hcomm : Equiv.swap a b * ψ = ψ * Equiv.swap a b) :
    ψ a ∈ ({a, b} : Finset (Fin n)) ∧ ψ b ∈ ({a, b} : Finset (Fin n)) := by
  have hc_a : Equiv.swap a b a = b := Equiv.swap_apply_left a b
  have hca : ∀ x : Fin n, Equiv.swap a b (ψ x) = ψ (Equiv.swap a b x) := by
    intro x
    have h1 := Equiv.Perm.mul_apply (Equiv.swap a b) ψ x
    rw [hcomm, Equiv.Perm.mul_apply] at h1
    exact h1.symm
  constructor
  · by_contra hcon
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcon
    have h1 : ψ b = ψ a := by
      have e1 : ψ b = ψ (Equiv.swap a b a) := (congrArg ψ hc_a).symm
      have e2 : ψ (Equiv.swap a b a) = Equiv.swap a b (ψ a) := (hca a).symm
      rw [e1, e2, Equiv.swap_apply_of_ne_of_ne hcon.1 hcon.2]
    exact hne (ψ.injective h1).symm
  · by_contra hcon
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcon
    have h1 : ψ a = ψ b := by
      have e1 : ψ a = ψ (Equiv.swap a b b) := (congrArg ψ (Equiv.swap_apply_right a b)).symm
      have e2 : ψ (Equiv.swap a b b) = Equiv.swap a b (ψ b) := (hca b).symm
      rw [e1, e2, Equiv.swap_apply_of_ne_of_ne hcon.1 hcon.2]
    exact hne (ψ.injective h1)

/-- A permutation preserving a two-element set also preserves its complement. -/
lemma perm_compl_of_perm_ab {n : ℕ} {ψ : Equiv.Perm (Fin n)} {a b : Fin n}
    (h : ∀ y ∈ ({a, b} : Finset (Fin n)), ψ y ∈ ({a, b} : Finset (Fin n)))
    (y : Fin n) (hy : y ∉ ({a, b} : Finset (Fin n))) :
    ψ y ∉ ({a, b} : Finset (Fin n)) := by
  have hsub : Finset.image ψ {a, b} ⊆ ({a, b} : Finset (Fin n)) := by
    intro z hz
    obtain ⟨w, hw, hwz⟩ := Finset.mem_image.1 hz
    rw [← hwz]
    exact h w hw
  have hcard : (Finset.image ψ {a, b}).card = ({a, b} : Finset (Fin n)).card := by
    rw [Finset.card_image_of_injective _ ψ.injective]
  have h2 : Finset.image ψ {a, b} = {a, b} :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hcard])
  intro hcon
  rw [← h2] at hcon
  obtain ⟨z, hz, hzy⟩ := Finset.mem_image.1 hcon
  exact hy (ψ.injective hzy ▸ hz)

/-- The restriction of an involution to a preserved pair `{a, b}`. -/
def restrictAb {n : ℕ} {ψ : Equiv.Perm (Fin n)} (hψ : Function.Involutive ψ)
    {a b : Fin n} (h : ∀ y ∈ ({a, b} : Finset (Fin n)), ψ y ∈ ({a, b} : Finset (Fin n))) :
    Equiv.Perm (Fin n) :=
  permOfInvolutive (fun x => if x ∈ ({a, b} : Finset (Fin n)) then ψ x else x) (by
    intro x
    show (if (if x ∈ ({a, b} : Finset (Fin n)) then ψ x else x) ∈ ({a, b} : Finset (Fin n))
      then ψ (if x ∈ ({a, b} : Finset (Fin n)) then ψ x else x)
      else (if x ∈ ({a, b} : Finset (Fin n)) then ψ x else x)) = x
    by_cases hx : x ∈ ({a, b} : Finset (Fin n))
    · rw [if_pos hx, if_pos (h x hx), hψ x]
    · rw [if_neg hx, if_neg hx])

lemma restrictAb_apply_of_mem {n : ℕ} {ψ : Equiv.Perm (Fin n)}
    (hψ : Function.Involutive ψ) {a b : Fin n}
    (h : ∀ y ∈ ({a, b} : Finset (Fin n)), ψ y ∈ ({a, b} : Finset (Fin n)))
    {x : Fin n} (hx : x ∈ ({a, b} : Finset (Fin n))) :
    restrictAb hψ h x = ψ x := by
  unfold restrictAb
  rw [permOfInvolutive_apply, if_pos hx]

lemma restrictAb_apply_of_not_mem {n : ℕ} {ψ : Equiv.Perm (Fin n)}
    (hψ : Function.Involutive ψ) {a b : Fin n}
    (h : ∀ y ∈ ({a, b} : Finset (Fin n)), ψ y ∈ ({a, b} : Finset (Fin n)))
    {x : Fin n} (hx : x ∉ ({a, b} : Finset (Fin n))) :
    restrictAb hψ h x = x := by
  unfold restrictAb
  rw [permOfInvolutive_apply, if_neg hx]

lemma restrictAb_involutive {n : ℕ} {ψ : Equiv.Perm (Fin n)}
    (hψ : Function.Involutive ψ) {a b : Fin n}
    (h : ∀ y ∈ ({a, b} : Finset (Fin n)), ψ y ∈ ({a, b} : Finset (Fin n))) :
    Function.Involutive (restrictAb hψ h) := by
  intro x
  by_cases hx : x ∈ ({a, b} : Finset (Fin n))
  · rw [restrictAb_apply_of_mem hψ h hx, restrictAb_apply_of_mem hψ h (h x hx), hψ x]
  · rw [restrictAb_apply_of_not_mem hψ h hx, restrictAb_apply_of_not_mem hψ h hx]

/-- The restriction of an involution to the complement of a preserved pair `{a, b}`. -/
def restrictCompl {n : ℕ} {ψ : Equiv.Perm (Fin n)} (hψ : Function.Involutive ψ)
    {a b : Fin n} (h : ∀ y ∈ ({a, b} : Finset (Fin n)), ψ y ∈ ({a, b} : Finset (Fin n))) :
    Equiv.Perm (Fin n) :=
  permOfInvolutive (fun x => if x ∈ ({a, b} : Finset (Fin n)) then x else ψ x) (by
    intro x
    show (if (if x ∈ ({a, b} : Finset (Fin n)) then x else ψ x) ∈ ({a, b} : Finset (Fin n))
      then (if x ∈ ({a, b} : Finset (Fin n)) then x else ψ x)
      else ψ (if x ∈ ({a, b} : Finset (Fin n)) then x else ψ x)) = x
    by_cases hx : x ∈ ({a, b} : Finset (Fin n))
    · rw [if_pos hx, if_pos hx]
    · rw [if_neg hx, if_neg (perm_compl_of_perm_ab h x hx), hψ x])

lemma restrictCompl_apply_of_mem {n : ℕ} {ψ : Equiv.Perm (Fin n)}
    (hψ : Function.Involutive ψ) {a b : Fin n}
    (h : ∀ y ∈ ({a, b} : Finset (Fin n)), ψ y ∈ ({a, b} : Finset (Fin n)))
    {x : Fin n} (hx : x ∈ ({a, b} : Finset (Fin n))) :
    restrictCompl hψ h x = x := by
  unfold restrictCompl
  rw [permOfInvolutive_apply, if_pos hx]

lemma restrictCompl_apply_of_not_mem {n : ℕ} {ψ : Equiv.Perm (Fin n)}
    (hψ : Function.Involutive ψ) {a b : Fin n}
    (h : ∀ y ∈ ({a, b} : Finset (Fin n)), ψ y ∈ ({a, b} : Finset (Fin n)))
    {x : Fin n} (hx : x ∉ ({a, b} : Finset (Fin n))) :
    restrictCompl hψ h x = ψ x := by
  unfold restrictCompl
  rw [permOfInvolutive_apply, if_neg hx]

lemma restrictCompl_involutive {n : ℕ} {ψ : Equiv.Perm (Fin n)}
    (hψ : Function.Involutive ψ) {a b : Fin n}
    (h : ∀ y ∈ ({a, b} : Finset (Fin n)), ψ y ∈ ({a, b} : Finset (Fin n))) :
    Function.Involutive (restrictCompl hψ h) := by
  intro x
  by_cases hx : x ∈ ({a, b} : Finset (Fin n))
  · rw [restrictCompl_apply_of_mem hψ h hx, restrictCompl_apply_of_mem hψ h hx]
  · rw [restrictCompl_apply_of_not_mem hψ h hx,
      restrictCompl_apply_of_not_mem hψ h (perm_compl_of_perm_ab h x hx), hψ x]

/-- An involution decomposes as the product of its two restrictions. -/
lemma mul_restrictAb_restrictCompl {n : ℕ} {ψ : Equiv.Perm (Fin n)}
    (hψ : Function.Involutive ψ) {a b : Fin n}
    (h : ∀ y ∈ ({a, b} : Finset (Fin n)), ψ y ∈ ({a, b} : Finset (Fin n))) :
    restrictAb hψ h * restrictCompl hψ h = ψ := by
  apply Equiv.Perm.ext_iff.2
  intro x
  rw [Equiv.Perm.mul_apply]
  by_cases hx : x ∈ ({a, b} : Finset (Fin n))
  · rw [restrictCompl_apply_of_mem hψ h hx, restrictAb_apply_of_mem hψ h hx]
  · rw [restrictCompl_apply_of_not_mem hψ h hx,
      restrictAb_apply_of_not_mem hψ h (perm_compl_of_perm_ab h x hx)]

/-- On a preserved pair `{a, b}`, an involution is either the identity or the swap. -/
lemma restrictAb_eq_one_or_c {n : ℕ} {ψ : Equiv.Perm (Fin n)}
    {a b : Fin n} (hne : a ≠ b) (hψ : Function.Involutive ψ)
    (h : ∀ y ∈ ({a, b} : Finset (Fin n)), ψ y ∈ ({a, b} : Finset (Fin n))) :
    restrictAb hψ h = 1 ∨ restrictAb hψ h = Equiv.swap a b := by
  have ha' : ψ a ∈ ({a, b} : Finset (Fin n)) := h a (Finset.mem_insert_self a {b})
  have hbmem : b ∈ ({a, b} : Finset (Fin n)) := by simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha'
  cases ha' with
  | inl h1 =>
    have hb2 : ψ b = b := by
      have hb2' : ψ b ∈ ({a, b} : Finset (Fin n)) := h b hbmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb2'
      cases hb2' with
      | inl h2 => exact absurd (ψ.injective (h2.trans h1.symm)).symm hne
      | inr h2 => exact h2
    left
    apply Equiv.Perm.ext_iff.2
    intro x
    by_cases hx : x ∈ ({a, b} : Finset (Fin n))
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      cases hx with
      | inl h2 =>
        rw [h2, restrictAb_apply_of_mem hψ h (Finset.mem_insert_self a {b}), h1]
        exact (Equiv.Perm.one_apply a).symm
      | inr h2 =>
        rw [h2, restrictAb_apply_of_mem hψ h hbmem, hb2]
        exact (Equiv.Perm.one_apply b).symm
    · rw [restrictAb_apply_of_not_mem hψ h hx]
      exact (Equiv.Perm.one_apply x).symm
  | inr h1 =>
    have hb2 : ψ b = a := by
      have hb2' : ψ b ∈ ({a, b} : Finset (Fin n)) := h b hbmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb2'
      cases hb2' with
      | inl h2 => exact h2
      | inr h2 => exact absurd (ψ.injective (h2.trans h1.symm)) hne.symm
    right
    apply Equiv.Perm.ext_iff.2
    intro x
    by_cases hx : x ∈ ({a, b} : Finset (Fin n))
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      cases hx with
      | inl h2 =>
        rw [h2, restrictAb_apply_of_mem hψ h (Finset.mem_insert_self a {b}), h1]
        exact (Equiv.swap_apply_left a b).symm
      | inr h2 =>
        rw [h2, restrictAb_apply_of_mem hψ h hbmem, hb2]
        exact (Equiv.swap_apply_right a b).symm
    · rw [restrictAb_apply_of_not_mem hψ h hx]
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
      exact (Equiv.swap_apply_of_ne_of_ne hx.1 hx.2).symm

/-- The complement restriction of a fixed switching involution is a switching
involution of the reduced vertex `ρ`. -/
lemma isSwitch_rho_of_restrictCompl {n : ℕ} {σ ψ : Equiv.Perm (Fin n)}
    (hσ : Function.Involutive σ)
    {a b : Fin n} (ha : a ∈ nums σ) (hb : b ∈ nums σ) (_hab : label σ a = label σ b)
    (hne : a ≠ b) (hψ : IsSwitch σ ψ)
    (h : ∀ y ∈ ({a, b} : Finset (Fin n)), ψ y ∈ ({a, b} : Finset (Fin n))) :
    IsSwitch (rho σ a b) (restrictCompl hψ.1 h) := by
  refine ⟨restrictCompl_involutive hψ.1 h, ?_, ?_⟩
  · intro x hx
    by_cases hxab : x ∈ ({a, b} : Finset (Fin n))
    · exact restrictCompl_apply_of_mem hψ.1 h hxab
    · rw [restrictCompl_apply_of_not_mem hψ.1 h hxab]
      have hxn : x ∉ nums σ := by
        intro hcon
        rw [nums_rho hσ ha hb hne] at hx
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hxab
        exact hx (Finset.mem_filter.2 ⟨hcon, hxab.1, hxab.2⟩)
      exact hψ.2.1 x hxn
  · intro x hx
    have hxab : x ∉ ({a, b} : Finset (Fin n)) := by
      intro hcon
      rw [nums_rho hσ ha hb hne] at hx
      simp only [Finset.mem_filter] at hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hcon
      cases hcon with
      | inl h1 => exact hx.2.1 h1
      | inr h1 => exact hx.2.2 h1
    rw [restrictCompl_apply_of_not_mem hψ.1 h hxab]
    have hxn : x ∈ nums σ := by
      rw [nums_rho hσ ha hb hne] at hx
      exact (Finset.mem_filter.1 hx).1
    have h1 : ψ x ∈ nums σ := switch_mapsTo_nums hψ hxn
    have h2 : ψ x ∉ ({a, b} : Finset (Fin n)) := perm_compl_of_perm_ab h x hxab
    have h3 : ψ x ∈ nums (rho σ a b) := by
      rw [nums_rho hσ ha hb hne]
      apply Finset.mem_filter.2
      exact ⟨h1, by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at h2
        exact ⟨h2.1, h2.2⟩⟩
    rw [label_rho hσ ha hb hne h3, hψ.2.2 x hxn, label_rho hσ ha hb hne hx]

/-- The product of a permutation of `{a, b}` (identity or swap) with a switching
involution of the reduced vertex `ρ` is a switching involution of `σ`. -/
lemma isSwitch_mul {n : ℕ} {σ : Equiv.Perm (Fin n)} (hσ : Function.Involutive σ)
    {a b : Fin n} (ha : a ∈ nums σ) (hb : b ∈ nums σ) (hab : label σ a = label σ b)
    (hne : a ≠ b)
    {ψ₀ ψ₁ : Equiv.Perm (Fin n)} (hψ₀ : ψ₀ = 1 ∨ ψ₀ = Equiv.swap a b)
    (hψ₁ : IsSwitch (rho σ a b) ψ₁) :
    IsSwitch σ (ψ₀ * ψ₁) := by
  have hc_a : Equiv.swap a b a = b := Equiv.swap_apply_left a b
  have hc_b : Equiv.swap a b b = a := Equiv.swap_apply_right a b
  have habmem : ∀ x : Fin n, x ∈ ({a, b} : Finset (Fin n)) → x ∈ nums σ := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    cases hx with
    | inl h1 => exact h1 ▸ ha
    | inr h1 => exact h1 ▸ hb
  have hψ₁_fix_ab : ∀ x : Fin n, x ∈ ({a, b} : Finset (Fin n)) → ψ₁ x = x := by
    intro x hx
    apply hψ₁.2.1
    intro hcon
    rw [nums_rho hσ ha hb hne] at hcon
    simp only [Finset.mem_filter] at hcon
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    cases hx with
    | inl h1 => exact hcon.2.1 h1
    | inr h1 => exact hcon.2.2 h1
  have hψ₀_apply : ∀ x : Fin n, x ∉ ({a, b} : Finset (Fin n)) → ψ₀ x = x := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
    cases hψ₀ with
    | inl h1 => rw [h1]; exact Equiv.Perm.one_apply x
    | inr h1 => rw [h1]; exact Equiv.swap_apply_of_ne_of_ne hx.1 hx.2
  have hψ₀_ab : ∀ x : Fin n, x ∈ ({a, b} : Finset (Fin n)) → ψ₀ x ∈ ({a, b} : Finset (Fin n)) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
    cases hψ₀ with
    | inl h1 => rw [h1]; rw [Equiv.Perm.one_apply]; exact hx
    | inr h1 =>
      rw [h1]
      cases hx with
      | inl h2 => rw [h2, Equiv.swap_apply_left]; exact Or.inr rfl
      | inr h2 => rw [h2, Equiv.swap_apply_right]; exact Or.inl rfl
  have hcomm : Commute ψ₀ ψ₁ := by
    apply Equiv.Perm.Disjoint.commute
    intro x
    by_cases hx : x ∈ ({a, b} : Finset (Fin n))
    · exact Or.inr (hψ₁_fix_ab x hx)
    · exact Or.inl (hψ₀_apply x hx)
  have h0sq : ψ₀ * ψ₀ = 1 := by
    cases hψ₀ with
    | inl h1 => rw [h1, one_mul]
    | inr h1 => rw [h1]; exact Perm_mul_self_eq_one_of_involutive (swap_involutive a b)
  have h1sq : ψ₁ * ψ₁ = 1 := Perm_mul_self_eq_one_of_involutive hψ₁.1
  have hsq : (ψ₀ * ψ₁) * (ψ₀ * ψ₁) = 1 := by
    calc (ψ₀ * ψ₁) * (ψ₀ * ψ₁)
        = (ψ₀ * ψ₀) * (ψ₁ * ψ₁) := by
          rw [mul_assoc, ← mul_assoc ψ₁ ψ₀ ψ₁, ← hcomm.eq, mul_assoc ψ₀ ψ₁ ψ₁, ← mul_assoc]
      _ = 1 := by rw [h0sq, h1sq, one_mul]
  refine ⟨?_, ?_, ?_⟩
  · intro x
    rw [← Equiv.Perm.mul_apply, hsq, Equiv.Perm.one_apply]
  · intro x hx
    have hxab : x ∉ ({a, b} : Finset (Fin n)) := fun hcon => hx (habmem x hcon)
    have hx1 : ψ₁ x = x := by
      apply hψ₁.2.1
      intro hcon
      rw [nums_rho hσ ha hb hne] at hcon
      exact hx (Finset.mem_filter.1 hcon).1
    rw [Equiv.Perm.mul_apply, hx1, hψ₀_apply x hxab]
  · intro x hx
    by_cases hxab : x ∈ ({a, b} : Finset (Fin n))
    · rw [Equiv.Perm.mul_apply, hψ₁_fix_ab x hxab]
      cases hψ₀ with
      | inl h1 => rw [h1, Equiv.Perm.one_apply]
      | inr h1 =>
        rw [h1]
        have hc_label : ∀ y : Fin n, y ∈ nums σ → label σ (Equiv.swap a b y) = label σ y := by
          intro y hy
          by_cases hya : y = a
          · subst hya; rw [hc_a]; exact hab.symm
          by_cases hyb : y = b
          · subst hyb; rw [hc_b]; exact hab
          rw [Equiv.swap_apply_of_ne_of_ne hya hyb]
        exact hc_label x hx
    · have hx1 : x ∈ nums (rho σ a b) := by
        rw [nums_rho hσ ha hb hne]
        apply Finset.mem_filter.2
        exact ⟨hx, by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hxab
          exact ⟨hxab.1, hxab.2⟩⟩
      have h1 : ψ₁ x ∈ nums (rho σ a b) := switch_mapsTo_nums hψ₁ hx1
      have h2 : ψ₁ x ∉ ({a, b} : Finset (Fin n)) := by
        intro hcon
        rw [nums_rho hσ ha hb hne] at h1
        simp only [Finset.mem_filter] at h1
        simp only [Finset.mem_insert, Finset.mem_singleton] at hcon
        cases hcon with
        | inl h3 => exact h1.2.1 h3
        | inr h3 => exact h1.2.2 h3
      rw [Equiv.Perm.mul_apply, hψ₀_apply _ h2, ← label_rho hσ ha hb hne h1, hψ₁.2.2 x hx1,
        label_rho hσ ha hb hne hx1]

/-- A switching involution of the reduced vertex fixes both `a` and `b`. -/
lemma switch_rho_fix_of_mem_ab {n : ℕ} {σ ψ₁ : Equiv.Perm (Fin n)} (hσ : Function.Involutive σ)
    {a b : Fin n} (ha : a ∈ nums σ) (hb : b ∈ nums σ) (hne : a ≠ b)
    (hψ₁ : IsSwitch (rho σ a b) ψ₁) {x : Fin n} (hx : x ∈ ({a, b} : Finset (Fin n))) :
    ψ₁ x = x := by
  apply hψ₁.2.1
  intro hcon
  rw [nums_rho hσ ha hb hne] at hcon
  have h2 := (Finset.mem_filter.1 hcon).2
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  cases hx with
  | inl h3 => exact h2.1 h3
  | inr h3 => exact h2.2 h3

/-- A fixed switching involution preserves the pair `{a, b}` (bundled form). -/
lemma perm_ab_of_fixed {n : ℕ} {σ ψ : Equiv.Perm (Fin n)}
    {a b : Fin n} (ha : a ∈ nums σ) (hb : b ∈ nums σ) (hab : label σ a = label σ b)
    (hne : a ≠ b) (hψ : IsSwitch σ ψ) (hcomm : Equiv.swap a b * ψ = ψ * Equiv.swap a b) :
    ∀ y ∈ ({a, b} : Finset (Fin n)), ψ y ∈ ({a, b} : Finset (Fin n)) := by
  have h := fixed_perm_ab ha hb hab hne hψ hcomm
  intro y hy
  simp only [Finset.mem_insert, Finset.mem_singleton] at hy
  cases hy with
  | inl h1 => subst h1; exact h.1
  | inr h1 => subst h1; exact h.2

/-- The product `ψ₀ * ψ₁` commutes with `swap a b` when `ψ₀ ∈ {1, swap a b}` and `ψ₁`
is a switching involution of the reduced vertex. -/
lemma commute_c_of_mem {n : ℕ} {σ : Equiv.Perm (Fin n)} (hσ : Function.Involutive σ)
    {a b : Fin n} (ha : a ∈ nums σ) (hb : b ∈ nums σ) (hne : a ≠ b)
    {ψ₀ ψ₁ : Equiv.Perm (Fin n)} (hψ₀ : ψ₀ = 1 ∨ ψ₀ = Equiv.swap a b)
    (hψ₁ : IsSwitch (rho σ a b) ψ₁) :
    Equiv.swap a b * (ψ₀ * ψ₁) = (ψ₀ * ψ₁) * Equiv.swap a b := by
  have h0 : Commute (Equiv.swap a b) ψ₀ := by
    cases hψ₀ with
    | inl h1 => rw [h1]; exact Commute.one_right (Equiv.swap a b)
    | inr h1 => rw [h1]
  have h1 : Commute (Equiv.swap a b) ψ₁ := by
    apply Equiv.Perm.Disjoint.commute
    intro x
    by_cases hx : x ∈ ({a, b} : Finset (Fin n))
    · exact Or.inr (switch_rho_fix_of_mem_ab hσ ha hb hne hψ₁ hx)
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
      exact Or.inl (Equiv.swap_apply_of_ne_of_ne hx.1 hx.2)
  calc Equiv.swap a b * (ψ₀ * ψ₁)
      = (Equiv.swap a b * ψ₀) * ψ₁ := (mul_assoc _ _ _).symm
    _ = (ψ₀ * Equiv.swap a b) * ψ₁ := by rw [h0.eq]
    _ = ψ₀ * (Equiv.swap a b * ψ₁) := mul_assoc _ _ _
    _ = ψ₀ * (ψ₁ * Equiv.swap a b) := by rw [h1.eq]
    _ = (ψ₀ * ψ₁) * Equiv.swap a b := (mul_assoc _ _ _).symm

/-- The fixed points of the conjugation involution decompose as a choice on `{a, b}`
(identity or swap) times a switching involution of the reduced vertex. -/
def fixedDecompEquiv {n : ℕ} {σ : Equiv.Perm (Fin n)} (hσ : Function.Involutive σ)
    {a b : Fin n} (ha : a ∈ nums σ) (hb : b ∈ nums σ) (hab : label σ a = label σ b)
    (hne : a ≠ b) :
    {ψ : Equiv.Perm (Fin n) // IsSwitch σ ψ ∧ Equiv.swap a b * ψ = ψ * Equiv.swap a b} ≃
      {ψ₀ : Equiv.Perm (Fin n) // ψ₀ = 1 ∨ ψ₀ = Equiv.swap a b} ×
        {ψ₁ : Equiv.Perm (Fin n) // IsSwitch (rho σ a b) ψ₁} where
  toFun := fun ψ =>
    (⟨restrictAb ψ.2.1.1 (perm_ab_of_fixed ha hb hab hne ψ.2.1 ψ.2.2),
      restrictAb_eq_one_or_c hne ψ.2.1.1 (perm_ab_of_fixed ha hb hab hne ψ.2.1 ψ.2.2)⟩,
     ⟨restrictCompl ψ.2.1.1 (perm_ab_of_fixed ha hb hab hne ψ.2.1 ψ.2.2),
      isSwitch_rho_of_restrictCompl hσ ha hb hab hne ψ.2.1
        (perm_ab_of_fixed ha hb hab hne ψ.2.1 ψ.2.2)⟩)
  invFun := fun p =>
    ⟨p.1.1 * p.2.1, isSwitch_mul hσ ha hb hab hne p.1.2 p.2.2,
      commute_c_of_mem hσ ha hb hne p.1.2 p.2.2⟩
  left_inv := fun ψ => by
    apply Subtype.ext
    exact mul_restrictAb_restrictCompl ψ.2.1.1
      (perm_ab_of_fixed ha hb hab hne ψ.2.1 ψ.2.2)
  right_inv := fun p => by
    obtain ⟨ψ₀, ψ₁⟩ := p
    have hψ₁_fix : ∀ x : Fin n, x ∈ ({a, b} : Finset (Fin n)) → ψ₁.1 x = x :=
      fun x hx => switch_rho_fix_of_mem_ab hσ ha hb hne ψ₁.2 hx
    have hψ₀_fix : ∀ x : Fin n, x ∉ ({a, b} : Finset (Fin n)) → ψ₀.1 x = x := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
      cases ψ₀.2 with
      | inl h1 => rw [h1]; exact Equiv.Perm.one_apply x
      | inr h1 => rw [h1]; exact Equiv.swap_apply_of_ne_of_ne hx.1 hx.2
    have hψ₀_ab : ∀ x : Fin n, x ∈ ({a, b} : Finset (Fin n)) → ψ₀.1 x ∈ ({a, b} : Finset (Fin n)) := by
      intro x hx
      cases ψ₀.2 with
      | inl h1 => rw [h1, Equiv.Perm.one_apply]; exact hx
      | inr h1 =>
        rw [h1]
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
        cases hx with
        | inl h2 => rw [h2, Equiv.swap_apply_left]; exact Or.inr rfl
        | inr h2 => rw [h2, Equiv.swap_apply_right]; exact Or.inl rfl
    have hψ₁_compl : ∀ x : Fin n, x ∉ ({a, b} : Finset (Fin n)) → ψ₁.1 x ∉ ({a, b} : Finset (Fin n)) := by
      intro x hx hcon
      by_cases h2 : ψ₁.1 x = x
      · rw [h2] at hcon
        exact hx hcon
      · have hxn : x ∈ nums (rho σ a b) := by
          by_contra h4
          exact h2 (ψ₁.2.2.1 x h4)
        have h3 : ψ₁.1 x ∈ nums (rho σ a b) := switch_mapsTo_nums ψ₁.2 hxn
        rw [nums_rho hσ ha hb hne] at h3
        have h5 := (Finset.mem_filter.1 h3).2
        simp only [Finset.mem_insert, Finset.mem_singleton] at hcon
        cases hcon with
        | inl h6 => exact h5.1 h6
        | inr h6 => exact h5.2 h6
    apply Prod.ext
    · apply Subtype.ext
      show restrictAb (isSwitch_mul hσ ha hb hab hne ψ₀.2 ψ₁.2).1
        (perm_ab_of_fixed ha hb hab hne (isSwitch_mul hσ ha hb hab hne ψ₀.2 ψ₁.2)
          (commute_c_of_mem hσ ha hb hne ψ₀.2 ψ₁.2)) = ψ₀.1
      apply Equiv.Perm.ext_iff.2
      intro x
      by_cases hx : x ∈ ({a, b} : Finset (Fin n))
      · rw [restrictAb_apply_of_mem _ _ hx, Equiv.Perm.mul_apply, hψ₁_fix x hx]
      · rw [restrictAb_apply_of_not_mem _ _ hx, hψ₀_fix x hx]
    · apply Subtype.ext
      show restrictCompl (isSwitch_mul hσ ha hb hab hne ψ₀.2 ψ₁.2).1
        (perm_ab_of_fixed ha hb hab hne (isSwitch_mul hσ ha hb hab hne ψ₀.2 ψ₁.2)
          (commute_c_of_mem hσ ha hb hne ψ₀.2 ψ₁.2)) = ψ₁.1
      apply Equiv.Perm.ext_iff.2
      intro x
      by_cases hx : x ∈ ({a, b} : Finset (Fin n))
      · rw [restrictCompl_apply_of_mem _ _ hx, hψ₁_fix x hx]
      · rw [restrictCompl_apply_of_not_mem _ _ hx, Equiv.Perm.mul_apply, hψ₀_fix _ (hψ₁_compl x hx)]

/-- A non-fantastic vertex admits an even number of switching involutions. -/
theorem even_card_switch_of_not_fantastic {n : ℕ} {σ : Equiv.Perm (Fin n)}
    (hσ : Function.Involutive σ) (hf : ¬ Fantastic σ) :
    Even (Fintype.card {φ : Equiv.Perm (Fin n) // IsSwitch σ φ}) := by
  obtain ⟨a, ha, b, hb, hab, hne⟩ : ∃ a ∈ nums σ, ∃ b ∈ nums σ,
      label σ a = label σ b ∧ a ≠ b := by
    unfold Fantastic Set.InjOn at hf
    push Not at hf
    exact hf
  have hc2 : Equiv.swap a b * Equiv.swap a b = 1 :=
    Perm_mul_self_eq_one_of_involutive (swap_involutive a b)
  have hc_ne : (1 : Equiv.Perm (Fin n)) ≠ Equiv.swap a b := by
    intro h
    have h1 := congrArg (fun x => x a) h
    rw [Equiv.Perm.one_apply, Equiv.swap_apply_left] at h1
    exact hne h1
  let G : {φ : Equiv.Perm (Fin n) // IsSwitch σ φ} → {φ : Equiv.Perm (Fin n) // IsSwitch σ φ} :=
    fun φ => ⟨Equiv.swap a b * φ.1 * Equiv.swap a b, conj_isSwitch ha hb hab φ.2⟩
  have hG_invol : Function.Involutive G := by
    intro φ
    apply Subtype.ext
    show Equiv.swap a b * (Equiv.swap a b * φ.1 * Equiv.swap a b) * Equiv.swap a b = φ.1
    calc Equiv.swap a b * (Equiv.swap a b * φ.1 * Equiv.swap a b) * Equiv.swap a b
        = (Equiv.swap a b * Equiv.swap a b) * φ.1 * (Equiv.swap a b * Equiv.swap a b) := by
          group
      _ = φ.1 := by rw [hc2, one_mul, mul_one]
  have hmod : Fintype.card {φ : Equiv.Perm (Fin n) // IsSwitch σ φ} ≡
      Fintype.card {x // G x = x} [MOD 2] :=
    card_modEq_of_involutive G hG_invol
  have fixed_iff : ∀ φ : {φ : Equiv.Perm (Fin n) // IsSwitch σ φ},
      G φ = φ ↔ Equiv.swap a b * φ.1 = φ.1 * Equiv.swap a b := by
    intro φ
    constructor
    · intro h
      have h1 := congrArg (fun x => Equiv.swap a b * x) (congrArg Subtype.val h)
      have h2 : Equiv.swap a b * (Equiv.swap a b * φ.1 * Equiv.swap a b) =
          φ.1 * Equiv.swap a b := by
        calc Equiv.swap a b * (Equiv.swap a b * φ.1 * Equiv.swap a b)
            = ((Equiv.swap a b * Equiv.swap a b) * φ.1) * Equiv.swap a b := by group
          _ = φ.1 * Equiv.swap a b := by rw [hc2, one_mul]
      rw [h2] at h1
      exact h1.symm
    · intro h
      apply Subtype.ext
      show Equiv.swap a b * φ.1 * Equiv.swap a b = φ.1
      rw [h, mul_assoc, hc2, mul_one]
  have hequiv1 : {x // G x = x} ≃
      {ψ : Equiv.Perm (Fin n) // IsSwitch σ ψ ∧ Equiv.swap a b * ψ = ψ * Equiv.swap a b} := {
    toFun := fun x => ⟨x.1.1, x.1.2, (fixed_iff x.1).1 x.2⟩
    invFun := fun ψ => ⟨⟨ψ.1, ψ.2.1⟩, Subtype.ext (by
      show Equiv.swap a b * ψ.1 * Equiv.swap a b = ψ.1
      rw [ψ.2.2, mul_assoc, hc2, mul_one])⟩
    left_inv := fun x => rfl
    right_inv := fun ψ => rfl }
  have hequiv := hequiv1.trans (fixedDecompEquiv hσ ha hb hab hne)
  have hcard0 : Fintype.card {ψ₀ : Equiv.Perm (Fin n) // ψ₀ = 1 ∨ ψ₀ = Equiv.swap a b} = 2 := by
    let e : {ψ₀ : Equiv.Perm (Fin n) // ψ₀ = 1 ∨ ψ₀ = Equiv.swap a b} ≃ Fin 2 := {
      toFun := fun ψ₀ => if ψ₀.1 = 1 then 0 else 1
      invFun := fun i => if i = 0 then ⟨1, Or.inl rfl⟩ else ⟨Equiv.swap a b, Or.inr rfl⟩
      left_inv := fun ψ₀ => by
        obtain ⟨ψ₀, hψ₀⟩ := ψ₀
        show (if (if ψ₀ = 1 then (0 : Fin 2) else 1) = 0 then
            (⟨1, Or.inl rfl⟩ : {ψ₀ : Equiv.Perm (Fin n) // ψ₀ = 1 ∨ ψ₀ = Equiv.swap a b})
          else ⟨Equiv.swap a b, Or.inr rfl⟩) = ⟨ψ₀, hψ₀⟩
        by_cases h : ψ₀ = 1
        · rw [if_pos h, if_pos rfl]
          exact Subtype.ext h.symm
        · rw [if_neg h, if_neg (by decide)]
          exact Subtype.ext (hψ₀.resolve_left h).symm
      right_inv := fun i => by
        fin_cases i
        · show (if ((⟨1, Or.inl rfl⟩ : {ψ₀ : Equiv.Perm (Fin n) // ψ₀ = 1 ∨ ψ₀ = Equiv.swap a b}).1 = 1)
            then (0 : Fin 2) else 1) = 0
          rw [if_pos rfl]
        · show (if ((⟨Equiv.swap a b, Or.inr rfl⟩ : {ψ₀ : Equiv.Perm (Fin n) // ψ₀ = 1 ∨ ψ₀ = Equiv.swap a b}).1 = 1)
            then (0 : Fin 2) else 1) = 1
          rw [if_neg hc_ne.symm] }
    rw [Fintype.card_congr e, Fintype.card_fin]
  have hev : Fintype.card {x // G x = x} % 2 = 0 := by
    rw [Fintype.card_congr hequiv, Fintype.card_prod, hcard0]
    omega
  rw [Nat.even_iff, hmod, hev]

/-! ### Counting involutions with at most one fixed point -/

namespace usa2018p6_aux

/-- Decidability of being an involution on `Fin n`. -/
instance decInvol {n : ℕ} : DecidablePred (Function.Involutive (α := Fin n)) := fun σ =>
  inferInstanceAs (Decidable (∀ x, σ (σ x) = x))

/-- Fixed-point-free involutions of `Fin n`. -/
def fpfSubtype (n : ℕ) :=
  {σ : Equiv.Perm (Fin n) // Function.Involutive σ ∧ ∀ x, σ x ≠ x}

/-- Involutions of `Fin n` with at most one fixed point. -/
def vtxSubtype (n : ℕ) :=
  {σ : Equiv.Perm (Fin n) //
    Function.Involutive σ ∧ (Finset.univ.filter fun x => σ x = x).card ≤ 1}

instance (n : ℕ) : Fintype (fpfSubtype n) := by
  unfold fpfSubtype; infer_instance

instance (n : ℕ) : Fintype (vtxSubtype n) := by
  unfold vtxSubtype; infer_instance

/-- The number of fixed-point-free involutions of `Fin n`. -/
noncomputable def fcard (n : ℕ) : ℕ := Fintype.card (fpfSubtype n)

/-- The number of involutions of `Fin n` with at most one fixed point. -/
noncomputable def vcard (n : ℕ) : ℕ := Fintype.card (vtxSubtype n)

/-! ### Basic facts about `Equiv.Perm.decomposeFin` -/

theorem decomposeFin_fst {n : ℕ} (σ : Equiv.Perm (Fin (n + 2))) :
    (Equiv.Perm.decomposeFin σ).1 = σ 0 := by
  rw [← Equiv.Perm.decomposeFin_symm_apply_zero (Equiv.Perm.decomposeFin σ).1
    (Equiv.Perm.decomposeFin σ).2, Prod.mk.eta, Equiv.Perm.decomposeFin.symm_apply_apply]

/-- The partner of `0` under a permutation that moves `0`, seen as an element of
`Fin (n + 1)` via `Fin.pred`. -/
noncomputable def partner {n : ℕ} (σ : Equiv.Perm (Fin (n + 2))) (_h0 : σ 0 ≠ 0) :
    Fin (n + 1) :=
  ((Equiv.Perm.decomposeFin σ).1).pred (by
    rw [decomposeFin_fst]
    exact _h0)

theorem partner_succ {n : ℕ} (σ : Equiv.Perm (Fin (n + 2))) (h0 : σ 0 ≠ 0) :
    (partner σ h0).succ = σ 0 := by
  unfold partner
  rw [Fin.succ_pred, decomposeFin_fst]

theorem decomposeFin_eq_symm_partner {n : ℕ} (σ : Equiv.Perm (Fin (n + 2))) (h0 : σ 0 ≠ 0) :
    σ = Equiv.Perm.decomposeFin.symm ((partner σ h0).succ, (Equiv.Perm.decomposeFin σ).2) := by
  rw [partner_succ, ← decomposeFin_fst, Prod.mk.eta]
  exact (Equiv.Perm.decomposeFin.symm_apply_apply σ).symm

theorem decomposeFin_eq_symm_zero {n : ℕ} (σ : Equiv.Perm (Fin (n + 2))) (h0 : σ 0 = 0) :
    σ = Equiv.Perm.decomposeFin.symm (0, (Equiv.Perm.decomposeFin σ).2) := by
  have h1 : (Equiv.Perm.decomposeFin σ).1 = 0 := by
    rw [decomposeFin_fst]
    exact h0
  rw [← h1, Prod.mk.eta]
  exact (Equiv.Perm.decomposeFin.symm_apply_apply σ).symm

/-- The partner of `0` under `decomposeFin.symm (j.succ, e)` is `j` itself. -/
theorem partner_symm_succ {n : ℕ} (j : Fin (n + 1)) (e : Equiv.Perm (Fin (n + 1)))
    (h0 : (Equiv.Perm.decomposeFin.symm (j.succ, e)) 0 ≠ 0) :
    partner (Equiv.Perm.decomposeFin.symm (j.succ, e)) h0 = j := by
  have h1 := partner_succ (Equiv.Perm.decomposeFin.symm (j.succ, e)) h0
  rw [Equiv.Perm.decomposeFin_symm_apply_zero] at h1
  exact Fin.succ_inj.mp h1

/-! ### The core analysis: involutivity and fixed points of `decomposeFin.symm` -/

/-- Involutivity of `decomposeFin.symm (j.succ, e)` corresponds to involutivity of `e`
together with `e j = j`. -/
theorem involutive_symm_succ {n : ℕ} (j : Fin (n + 1)) (e : Equiv.Perm (Fin (n + 1))) :
    Function.Involutive (Equiv.Perm.decomposeFin.symm (j.succ, e)) ↔
      Function.Involutive e ∧ e j = j := by
  have swap0 : ∀ y : Fin (n + 2), Equiv.swap 0 j.succ y = 0 → y = j.succ := by
    intro y hy
    by_cases h0 : y = 0
    · subst h0
      rw [Equiv.swap_apply_left] at hy
      exact absurd hy (Fin.succ_ne_zero j)
    · by_cases hp : y = j.succ
      · exact hp
      · rw [Equiv.swap_apply_of_ne_of_ne h0 hp] at hy
        exact absurd hy h0
  constructor
  · intro h
    have hej : e j = j := by
      have h0 := h 0
      rw [Equiv.Perm.decomposeFin_symm_apply_zero] at h0
      rw [Equiv.Perm.decomposeFin_symm_apply_succ] at h0
      have hs := swap0 _ h0
      rwa [Fin.succ_inj] at hs
    refine ⟨?_, hej⟩
    intro x
    have hx := h x.succ
    rw [Equiv.Perm.decomposeFin_symm_apply_succ] at hx
    by_cases hex : e x = j
    · have h1 : Equiv.swap 0 j.succ ((e x).succ) = 0 := by
        rw [hex]
        exact Equiv.swap_apply_right 0 j.succ
      rw [h1, Equiv.Perm.decomposeFin_symm_apply_zero] at hx
      have hxj : x = j := Fin.succ_inj.mp hx.symm
      subst x
      rw [hex, hej]
    · have h1 : Equiv.swap 0 j.succ ((e x).succ) = (e x).succ :=
        Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) (fun h => hex (Fin.succ_inj.mp h))
      rw [h1, Equiv.Perm.decomposeFin_symm_apply_succ] at hx
      by_cases h2 : e (e x) = j
      · rw [h2, Equiv.swap_apply_right] at hx
        exact absurd hx.symm (Fin.succ_ne_zero _)
      · rw [Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) (fun h => h2 (Fin.succ_inj.mp h))]
          at hx
        rwa [Fin.succ_inj] at hx
  · rintro ⟨he, hej⟩ y
    induction y using Fin.cases with
    | zero =>
      rw [Equiv.Perm.decomposeFin_symm_apply_zero, Equiv.Perm.decomposeFin_symm_apply_succ, hej,
        Equiv.swap_apply_right]
    | succ x =>
      rw [Equiv.Perm.decomposeFin_symm_apply_succ]
      by_cases hex : e x = j
      · have hxj : x = j := by
          have h2 : x = e (e x) := (he x).symm
          rw [hex, hej] at h2
          exact h2
        subst x
        rw [hex, Equiv.swap_apply_right, Equiv.Perm.decomposeFin_symm_apply_zero]
      · have h1 : Equiv.swap 0 j.succ ((e x).succ) = (e x).succ :=
          Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) (fun h => hex (Fin.succ_inj.mp h))
        rw [h1, Equiv.Perm.decomposeFin_symm_apply_succ, he x]
        have hxj : x ≠ j := by
          rintro rfl
          exact hex hej
        exact Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) (fun h => hxj (Fin.succ_inj.mp h))

/-- `decomposeFin.symm (j.succ, e)` is fixed-point-free iff `e` has no fixed point
other than `j`. -/
theorem fpf_symm_succ {n : ℕ} (j : Fin (n + 1)) (e : Equiv.Perm (Fin (n + 1)))
    (he : Function.Involutive e) (hej : e j = j) :
    (∀ y : Fin (n + 2), Equiv.Perm.decomposeFin.symm (j.succ, e) y ≠ y) ↔
      ∀ x : Fin (n + 1), x ≠ j → e x ≠ x := by
  constructor
  · intro h x hxj hex
    have hx := h x.succ
    rw [Equiv.Perm.decomposeFin_symm_apply_succ] at hx
    have hexj : e x ≠ j := by
      rintro rfl
      exact hxj ((he x).symm.trans hej)
    rw [Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _)
        (fun h' => hexj (Fin.succ_inj.mp h'))] at hx
    exact hx (congrArg Fin.succ hex)
  · intro h y
    induction y using Fin.cases with
    | zero =>
      rw [Equiv.Perm.decomposeFin_symm_apply_zero]
      exact Fin.succ_ne_zero j
    | succ x =>
      rw [Equiv.Perm.decomposeFin_symm_apply_succ]
      by_cases hxj : x = j
      · subst x
        rw [hej, Equiv.swap_apply_right]
        exact (Fin.succ_ne_zero j).symm
      · have hexj : e x ≠ j := by
          rintro rfl
          exact hxj ((he x).symm.trans hej)
        rw [Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _)
          (fun h' => hexj (Fin.succ_inj.mp h'))]
        exact fun h' => h x hxj (Fin.succ_inj.mp h')

/-- The fixed points of `decomposeFin.symm (j.succ, e)` are in bijection with the fixed
points of `e` different from `j`. -/
theorem card_fp_symm_succ {n : ℕ} (j : Fin (n + 1)) (e : Equiv.Perm (Fin (n + 1)))
    (he : Function.Involutive e) (hej : e j = j) :
    (Finset.univ.filter fun y : Fin (n + 2) =>
        Equiv.Perm.decomposeFin.symm (j.succ, e) y = y).card =
      (Finset.univ.filter fun x : Fin (n + 1) => x ≠ j ∧ e x = x).card := by
  symm
  apply Finset.card_bij (fun x _ => x.succ)
  · intro x hx
    rw [Finset.mem_filter] at hx ⊢
    obtain ⟨-, hxj, hex⟩ := hx
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [Equiv.Perm.decomposeFin_symm_apply_succ,
      Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _)
        (fun h1 => hxj (by rw [← hex]; exact Fin.succ_inj.mp h1)),
      hex]
  · intro x₁ _ x₂ _ h
    exact Fin.succ_inj.mp h
  · intro y hy
    rw [Finset.mem_filter] at hy
    obtain ⟨-, hy⟩ := hy
    rcases Fin.eq_zero_or_eq_succ y with rfl | ⟨x, rfl⟩
    · rw [Equiv.Perm.decomposeFin_symm_apply_zero] at hy
      exact absurd hy (Fin.succ_ne_zero j)
    · rw [Equiv.Perm.decomposeFin_symm_apply_succ] at hy
      by_cases hxj : x = j
      · subst x
        rw [hej, Equiv.swap_apply_right] at hy
        exact absurd hy.symm (Fin.succ_ne_zero j)
      · have hexj : e x ≠ j := by
          rintro rfl
          exact hxj ((he x).symm.trans hej)
        rw [Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _)
          (fun h => hexj (Fin.succ_inj.mp h))] at hy
        exact ⟨x, by
          rw [Finset.mem_filter]
          exact ⟨Finset.mem_univ _, hxj, Fin.succ_inj.mp hy⟩, rfl⟩

/-- Involutivity of `decomposeFin.symm (0, e)` corresponds to involutivity of `e`. -/
theorem involutive_symm_zero {n : ℕ} (e : Equiv.Perm (Fin (n + 1))) :
    Function.Involutive (Equiv.Perm.decomposeFin.symm (0, e)) ↔ Function.Involutive e := by
  constructor
  · intro h x
    have hx := h x.succ
    rwa [Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_self, Equiv.refl_apply,
      Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_self, Equiv.refl_apply,
      Fin.succ_inj] at hx
  · intro h y
    induction y using Fin.cases with
    | zero =>
      rw [Equiv.Perm.decomposeFin_symm_apply_zero, Equiv.Perm.decomposeFin_symm_apply_zero]
    | succ x =>
      rw [Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_self, Equiv.refl_apply,
        Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_self, Equiv.refl_apply, h x]

/-- The fixed points of `decomposeFin.symm (0, e)` are `0` together with the successors
of fixed points of `e`. -/
theorem fp_symm_zero {n : ℕ} (e : Equiv.Perm (Fin (n + 1))) (y : Fin (n + 2)) :
    Equiv.Perm.decomposeFin.symm (0, e) y = y ↔
      y = 0 ∨ ∃ x : Fin (n + 1), y = x.succ ∧ e x = x := by
  induction y using Fin.cases with
  | zero => simp [Equiv.Perm.decomposeFin_symm_apply_zero]
  | succ x =>
    rw [Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_self, Equiv.refl_apply]
    constructor
    · intro h
      exact Or.inr ⟨x, rfl, Fin.succ_inj.mp h⟩
    · rintro (h | ⟨x', h, hex⟩)
      · exact absurd h (Fin.succ_ne_zero _)
      · rw [Fin.succ_inj] at h
        subst h
        rw [hex]

/-- `decomposeFin.symm (0, e)` has at most one fixed point iff `e` is fixed-point-free. -/
theorem card_le_one_symm_zero_iff {n : ℕ} (e : Equiv.Perm (Fin (n + 1))) :
    (Finset.univ.filter fun y : Fin (n + 2) =>
        Equiv.Perm.decomposeFin.symm (0, e) y = y).card ≤ 1 ↔
      ∀ x : Fin (n + 1), e x ≠ x := by
  constructor
  · intro h x hex
    have h0 : (0 : Fin (n + 2)) ∈ Finset.univ.filter (fun y : Fin (n + 2) =>
        Equiv.Perm.decomposeFin.symm (0, e) y = y) := by
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, (fp_symm_zero e 0).mpr (Or.inl rfl)⟩
    have hx : x.succ ∈ Finset.univ.filter (fun y : Fin (n + 2) =>
        Equiv.Perm.decomposeFin.symm (0, e) y = y) := by
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, (fp_symm_zero e x.succ).mpr (Or.inr ⟨x, rfl, hex⟩)⟩
    have hne : (0 : Fin (n + 2)) ≠ x.succ := (Fin.succ_ne_zero x).symm
    have hsub : ({0, x.succ} : Finset (Fin (n + 2))) ⊆
        Finset.univ.filter (fun y : Fin (n + 2) =>
          Equiv.Perm.decomposeFin.symm (0, e) y = y) := by
      intro z hz
      rw [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact h0
      · exact hx
    have h2 : 2 ≤ (Finset.univ.filter fun y : Fin (n + 2) =>
        Equiv.Perm.decomposeFin.symm (0, e) y = y).card :=
      calc 2 = ({0, x.succ} : Finset (Fin (n + 2))).card := (Finset.card_pair hne).symm
        _ ≤ _ := Finset.card_le_card hsub
    omega
  · intro h
    have hset : (Finset.univ.filter fun y : Fin (n + 2) =>
        Equiv.Perm.decomposeFin.symm (0, e) y = y) = {0} := by
      ext y
      rw [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · intro hy
        obtain ⟨-, hy⟩ := hy
        rcases (fp_symm_zero e y).mp hy with h0 | ⟨x, rfl, hex⟩
        · exact h0
        · exact absurd hex (h x)
      · intro hy
        rw [hy]
        exact ⟨Finset.mem_univ _, (fp_symm_zero e 0).mpr (Or.inl rfl)⟩
    rw [hset, Finset.card_singleton]

/-! ### Restriction to the complement of a fixed point -/

/-- Restriction of a permutation fixing `j` to the complement of `j`, transported to
`Fin n` along `finSuccAboveEquiv`. -/
noncomputable def restrictPerm {n : ℕ} {j : Fin (n + 1)} (e : Equiv.Perm (Fin (n + 1)))
    (hej : e j = j) : Equiv.Perm (Fin n) :=
  Equiv.permCongr (finSuccAboveEquiv j).symm
    (Equiv.Perm.subtypePerm e fun _x =>
      ⟨fun h1 h2 => h1 ((congrArg e h2).trans hej), fun h1 h2 => h1 (e.injective (h2.trans hej.symm))⟩)

theorem restrictPerm_apply {n : ℕ} {j : Fin (n + 1)} (e : Equiv.Perm (Fin (n + 1)))
    (hej : e j = j) (y : Fin n) :
    ((finSuccAboveEquiv j) (restrictPerm e hej y)).1 = e ((finSuccAboveEquiv j) y).1 := by
  simp [restrictPerm]

theorem restrictPerm_involutive {n : ℕ} {j : Fin (n + 1)} (e : Equiv.Perm (Fin (n + 1)))
    (he : Function.Involutive e) (hej : e j = j) :
    Function.Involutive (restrictPerm e hej) := by
  intro y
  apply (finSuccAboveEquiv j).injective
  apply Subtype.ext
  rw [restrictPerm_apply, restrictPerm_apply, he]

theorem restrictPerm_fix_iff {n : ℕ} {j : Fin (n + 1)} (e : Equiv.Perm (Fin (n + 1)))
    (hej : e j = j) (y : Fin n) :
    restrictPerm e hej y = y ↔ e ((finSuccAboveEquiv j) y).1 = ((finSuccAboveEquiv j) y).1 := by
  constructor
  · intro h
    have h2 := congrArg (finSuccAboveEquiv j) h
    have h3 : ((finSuccAboveEquiv j) (restrictPerm e hej y)).1 = e ((finSuccAboveEquiv j) y).1 :=
      restrictPerm_apply e hej y
    rw [h2] at h3
    exact h3.symm
  · intro h
    apply (finSuccAboveEquiv j).injective
    apply Subtype.ext
    rw [restrictPerm_apply e hej y]
    exact h

/-- The fixed points of `restrictPerm e hej` are in bijection with the fixed points of
`e` different from `j`. -/
theorem card_fp_restrictPerm {n : ℕ} {j : Fin (n + 1)} (e : Equiv.Perm (Fin (n + 1)))
    (hej : e j = j) :
    (Finset.univ.filter fun y : Fin n => restrictPerm e hej y = y).card =
      (Finset.univ.filter fun x : Fin (n + 1) => x ≠ j ∧ e x = x).card := by
  apply Finset.card_bij (fun y _ => ((finSuccAboveEquiv j) y).1)
  · intro y hy
    rw [Finset.mem_filter] at hy ⊢
    exact ⟨Finset.mem_univ _, ((finSuccAboveEquiv j) y).2,
      (restrictPerm_fix_iff e hej y).mp hy.2⟩
  · intro y₁ _ y₂ _ h
    exact (finSuccAboveEquiv j).injective (Subtype.ext h)
  · intro x hx
    rw [Finset.mem_filter] at hx
    obtain ⟨-, hxj, hex⟩ := hx
    refine ⟨(finSuccAboveEquiv j).symm ⟨x, hxj⟩, ?_, ?_⟩
    · rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by
        rw [restrictPerm_fix_iff e hej, Equiv.apply_symm_apply]
        exact hex⟩
    · exact congrArg Subtype.val (Equiv.apply_symm_apply _ _)

theorem fpf_restrictPerm {n : ℕ} {j : Fin (n + 1)} {e : Equiv.Perm (Fin (n + 1))}
    (hej : e j = j) (h : ∀ x : Fin (n + 1), x ≠ j → e x ≠ x) :
    ∀ y : Fin n, restrictPerm e hej y ≠ y := by
  intro y hy
  exact h _ ((finSuccAboveEquiv j) y).2 ((restrictPerm_fix_iff e hej y).mp hy)

/-! ### Extension by a fixed point -/

/-- Extension of a permutation of `Fin n` to `Fin (n + 1)` fixing `j`, via the
identification `Fin n ≃ {x // x ≠ j}`. -/
noncomputable def extendPerm {n : ℕ} (j : Fin (n + 1)) (τ : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin (n + 1)) :=
  (Equiv.sumCompl (· = j)).symm.trans
    (((Equiv.refl _).sumCongr (Equiv.permCongr (finSuccAboveEquiv j) τ)).trans
      (Equiv.sumCompl (· = j)))

theorem extendPerm_apply_self {n : ℕ} (j : Fin (n + 1)) (τ : Equiv.Perm (Fin n)) :
    extendPerm j τ j = j := by
  have h1 : (Equiv.sumCompl (· = j)).symm j = Sum.inl ⟨j, rfl⟩ :=
    Equiv.sumCompl_symm_apply_of_pos (p := (· = j)) (a := j) rfl
  simp [extendPerm, h1]

theorem extendPerm_apply_ne {n : ℕ} (j : Fin (n + 1)) (τ : Equiv.Perm (Fin n))
    {x : Fin (n + 1)} (hx : x ≠ j) :
    extendPerm j τ x =
      ((finSuccAboveEquiv j) (τ ((finSuccAboveEquiv j).symm ⟨x, hx⟩))).1 := by
  have h1 : (Equiv.sumCompl (· = j)).symm x = Sum.inr ⟨x, hx⟩ :=
    Equiv.sumCompl_symm_apply_of_neg (p := (· = j)) (a := x) hx
  simp [extendPerm, h1]

theorem extendPerm_involutive {n : ℕ} (j : Fin (n + 1)) {τ : Equiv.Perm (Fin n)}
    (hτ : Function.Involutive τ) : Function.Involutive (extendPerm j τ) := by
  intro x
  by_cases hx : x = j
  · rw [hx, extendPerm_apply_self, extendPerm_apply_self]
  · rw [extendPerm_apply_ne j τ hx]
    have hz : ((finSuccAboveEquiv j) (τ ((finSuccAboveEquiv j).symm ⟨x, hx⟩))).1 ≠ j :=
      ((finSuccAboveEquiv j) _).2
    rw [extendPerm_apply_ne j τ hz]
    rw [show (⟨((finSuccAboveEquiv j) (τ ((finSuccAboveEquiv j).symm ⟨x, hx⟩))).1, hz⟩ :
        {x : Fin (n + 1) // x ≠ j}) =
          (finSuccAboveEquiv j) (τ ((finSuccAboveEquiv j).symm ⟨x, hx⟩)) from Subtype.ext rfl]
    rw [Equiv.symm_apply_apply, hτ, Equiv.apply_symm_apply]

theorem extendPerm_fix_iff {n : ℕ} (j : Fin (n + 1)) (τ : Equiv.Perm (Fin n))
    {x : Fin (n + 1)} (hx : x ≠ j) :
    extendPerm j τ x = x ↔
      τ ((finSuccAboveEquiv j).symm ⟨x, hx⟩) = (finSuccAboveEquiv j).symm ⟨x, hx⟩ := by
  rw [extendPerm_apply_ne j τ hx]
  constructor
  · intro h
    apply (finSuccAboveEquiv j).injective
    rw [Equiv.apply_symm_apply]
    exact Subtype.ext h
  · intro h
    rw [h]
    exact congrArg Subtype.val (Equiv.apply_symm_apply _ _)

theorem extendPerm_restrictPerm {n : ℕ} {j : Fin (n + 1)} (e : Equiv.Perm (Fin (n + 1)))
    (hej : e j = j) : extendPerm j (restrictPerm e hej) = e := by
  apply Equiv.ext
  intro x
  by_cases hx : x = j
  · rw [hx, extendPerm_apply_self, hej]
  · rw [extendPerm_apply_ne j _ hx, restrictPerm_apply, Equiv.apply_symm_apply]

theorem restrictPerm_extendPerm {n : ℕ} (j : Fin (n + 1)) (τ : Equiv.Perm (Fin n)) :
    restrictPerm (extendPerm j τ) (extendPerm_apply_self j τ) = τ := by
  apply Equiv.ext
  intro y
  apply (finSuccAboveEquiv j).injective
  apply Subtype.ext
  rw [restrictPerm_apply, extendPerm_apply_ne j τ ((finSuccAboveEquiv j) y).2]
  rw [show (⟨((finSuccAboveEquiv j) y).1, ((finSuccAboveEquiv j) y).2⟩ :
      {x : Fin (n + 1) // x ≠ j}) = (finSuccAboveEquiv j) y from Subtype.ext rfl]
  rw [Equiv.symm_apply_apply]

theorem fpf_extendPerm {n : ℕ} (j : Fin (n + 1)) {τ : Equiv.Perm (Fin n)}
    (hτ : ∀ y, τ y ≠ y) : ∀ x : Fin (n + 1), x ≠ j → extendPerm j τ x ≠ x := by
  intro x hx hfix
  exact hτ _ ((extendPerm_fix_iff j τ hx).mp hfix)

/-! ### Wrapper lemmas combining the pieces -/

theorem invol_decomposeFin_symm {n : ℕ} (σ : Equiv.Perm (Fin (n + 2))) (h0 : σ 0 ≠ 0)
    (hinv : Function.Involutive σ) :
    Function.Involutive (Equiv.Perm.decomposeFin σ).2 ∧
      (Equiv.Perm.decomposeFin σ).2 (partner σ h0) = partner σ h0 := by
  have h := hinv
  rw [decomposeFin_eq_symm_partner σ h0] at h
  exact (involutive_symm_succ _ _).mp h

theorem fpf_e {n : ℕ} (σ : Equiv.Perm (Fin (n + 2))) (h0 : σ 0 ≠ 0)
    (hinv : Function.Involutive σ) (hfpf : ∀ x, σ x ≠ x) :
    ∀ x : Fin (n + 1), x ≠ partner σ h0 → (Equiv.Perm.decomposeFin σ).2 x ≠ x := by
  have h := hfpf
  rw [decomposeFin_eq_symm_partner σ h0] at h
  exact (fpf_symm_succ _ _ (invol_decomposeFin_symm σ h0 hinv).1
    (invol_decomposeFin_symm σ h0 hinv).2).mp h

theorem card_e_le_one {n : ℕ} (σ : Equiv.Perm (Fin (n + 2))) (h0 : σ 0 ≠ 0)
    (hinv : Function.Involutive σ)
    (hcard : (Finset.univ.filter fun y => σ y = y).card ≤ 1) :
    (Finset.univ.filter fun y : Fin n =>
        restrictPerm (Equiv.Perm.decomposeFin σ).2
          (invol_decomposeFin_symm σ h0 hinv).2 y = y).card ≤ 1 := by
  have h := hcard
  rw [decomposeFin_eq_symm_partner σ h0] at h
  rw [card_fp_symm_succ _ _ (invol_decomposeFin_symm σ h0 hinv).1
    (invol_decomposeFin_symm σ h0 hinv).2,
    ← card_fp_restrictPerm _ (invol_decomposeFin_symm σ h0 hinv).2] at h
  exact h

theorem card_extend_le_one {n : ℕ} (j : Fin (n + 1)) (τ : Equiv.Perm (Fin n))
    (hτ : Function.Involutive τ)
    (hcard : (Finset.univ.filter fun y => τ y = y).card ≤ 1) :
    (Finset.univ.filter fun y : Fin (n + 2) =>
        Equiv.Perm.decomposeFin.symm (j.succ, extendPerm j τ) y = y).card ≤ 1 := by
  have h2 : (Finset.univ.filter fun x : Fin (n + 1) => x ≠ j ∧ extendPerm j τ x = x).card =
      (Finset.univ.filter fun y : Fin n => τ y = y).card := by
    rw [← card_fp_restrictPerm _ (extendPerm_apply_self j τ), restrictPerm_extendPerm]
  rw [card_fp_symm_succ _ _ (extendPerm_involutive j hτ) (extendPerm_apply_self j τ), h2]
  exact hcard

theorem invol_e0 {n : ℕ} (σ : Equiv.Perm (Fin (n + 2))) (h0 : σ 0 = 0)
    (hinv : Function.Involutive σ) : Function.Involutive (Equiv.Perm.decomposeFin σ).2 := by
  have h := hinv
  rw [decomposeFin_eq_symm_zero σ h0] at h
  exact (involutive_symm_zero _).mp h

theorem fpf_e0 {n : ℕ} (σ : Equiv.Perm (Fin (n + 2))) (h0 : σ 0 = 0)
    (hcard : (Finset.univ.filter fun y => σ y = y).card ≤ 1) :
    ∀ x : Fin (n + 1), (Equiv.Perm.decomposeFin σ).2 x ≠ x := by
  have h := hcard
  rw [decomposeFin_eq_symm_zero σ h0] at h
  exact (card_le_one_symm_zero_iff _).mp h

/-! ### The decomposition equivalences -/

/-- Fixed-point-free involutions of `Fin (n + 2)` are in bijection with pairs of an
element `j : Fin (n + 1)` (the partner of `0`) and a fixed-point-free involution of
`Fin n`. -/
noncomputable def fpfDecomposeEquiv (n : ℕ) :
    fpfSubtype (n + 2) ≃ Fin (n + 1) × fpfSubtype n where
  toFun σ := ⟨partner σ.1 (σ.2.2 0),
    restrictPerm _ (invol_decomposeFin_symm σ.1 (σ.2.2 0) σ.2.1).2,
    restrictPerm_involutive _ (invol_decomposeFin_symm σ.1 (σ.2.2 0) σ.2.1).1 _,
    fpf_restrictPerm _ (fpf_e σ.1 (σ.2.2 0) σ.2.1 σ.2.2)⟩
  invFun jτ := ⟨Equiv.Perm.decomposeFin.symm (jτ.1.succ, extendPerm jτ.1 jτ.2.1),
    (involutive_symm_succ jτ.1 _).mpr ⟨extendPerm_involutive jτ.1 jτ.2.2.1,
      extendPerm_apply_self jτ.1 jτ.2.1⟩,
    (fpf_symm_succ jτ.1 _ (extendPerm_involutive jτ.1 jτ.2.2.1)
      (extendPerm_apply_self jτ.1 jτ.2.1)).mpr (fpf_extendPerm jτ.1 jτ.2.2.2)⟩
  left_inv σ := by
    apply Subtype.ext
    show Equiv.Perm.decomposeFin.symm ((partner σ.1 (σ.2.2 0)).succ, _) = σ.1
    rw [extendPerm_restrictPerm]
    exact (decomposeFin_eq_symm_partner σ.1 (σ.2.2 0)).symm
  right_inv jτ := by
    obtain ⟨j, τ⟩ := jτ
    apply Prod.ext
    · have h0 : (Equiv.Perm.decomposeFin.symm (j.succ, extendPerm j τ.1)) 0 ≠ 0 := by
        rw [Equiv.Perm.decomposeFin_symm_apply_zero]
        exact Fin.succ_ne_zero _
      exact partner_symm_succ j (extendPerm j τ.1) h0
    · apply Subtype.ext
      have h0 : (Equiv.Perm.decomposeFin.symm (j.succ, extendPerm j τ.1)) 0 ≠ 0 := by
        rw [Equiv.Perm.decomposeFin_symm_apply_zero]
        exact Fin.succ_ne_zero _
      have hinv : Function.Involutive (Equiv.Perm.decomposeFin.symm (j.succ, extendPerm j τ.1)) :=
        (involutive_symm_succ j _).mpr ⟨extendPerm_involutive j τ.2.1,
          extendPerm_apply_self j τ.1⟩
      show restrictPerm (Equiv.Perm.decomposeFin (Equiv.Perm.decomposeFin.symm (j.succ,
          extendPerm j τ.1))).2 (invol_decomposeFin_symm _ h0 hinv).2 = τ.1
      simp only [Equiv.apply_symm_apply]
      exact restrictPerm_extendPerm j τ.1

/-- The two cases of involutions of `Fin (n + 2)` with at most one fixed point,
according to whether `0` is fixed. -/
abbrev vtxSplitType (n : ℕ) :=
  {σ : Equiv.Perm (Fin (n + 2)) //
    (Function.Involutive σ ∧ (Finset.univ.filter fun x => σ x = x).card ≤ 1) ∧ σ 0 = 0} ⊕
  {σ : Equiv.Perm (Fin (n + 2)) //
    (Function.Involutive σ ∧ (Finset.univ.filter fun x => σ x = x).card ≤ 1) ∧ σ 0 ≠ 0}

/-- Split involutions of `Fin (n + 2)` according to whether `0` is a fixed point. -/
noncomputable def splitZeroEquiv (n : ℕ) :
    vtxSubtype (n + 2) ≃ vtxSplitType n where
  toFun σ := if h : σ.1 0 = 0 then Sum.inl ⟨σ.1, σ.2, h⟩ else Sum.inr ⟨σ.1, σ.2, h⟩
  invFun s := s.elim (fun σ => ⟨σ.1, σ.2.1⟩) (fun σ => ⟨σ.1, σ.2.1⟩)
  left_inv σ := by
    dsimp only
    split_ifs with h <;> rfl
  right_inv s := by
    rcases s with (⟨σ, hp, h0⟩ | ⟨σ, hp, h0⟩)
    · show ((if h : σ 0 = 0 then Sum.inl ⟨σ, hp, h⟩ else Sum.inr ⟨σ, hp, h⟩) : vtxSplitType n) =
        Sum.inl ⟨σ, hp, h0⟩
      rw [dif_pos h0]
    · show ((if h : σ 0 = 0 then Sum.inl ⟨σ, hp, h⟩ else Sum.inr ⟨σ, hp, h⟩) : vtxSplitType n) =
        Sum.inr ⟨σ, hp, h0⟩
      rw [dif_neg h0]

/-- Involutions of `Fin (n + 2)` with at most one fixed point that fix `0` are in
bijection with fixed-point-free involutions of `Fin (n + 1)`. -/
noncomputable def vtxZeroEquiv (n : ℕ) :
    {σ : Equiv.Perm (Fin (n + 2)) //
      (Function.Involutive σ ∧ (Finset.univ.filter fun x => σ x = x).card ≤ 1) ∧ σ 0 = 0} ≃
        fpfSubtype (n + 1) where
  toFun σ := ⟨(Equiv.Perm.decomposeFin σ.1).2, invol_e0 σ.1 σ.2.2 σ.2.1.1,
    fpf_e0 σ.1 σ.2.2 σ.2.1.2⟩
  invFun e := ⟨Equiv.Perm.decomposeFin.symm (0, e.1),
    ⟨(involutive_symm_zero e.1).mpr e.2.1, (card_le_one_symm_zero_iff e.1).mpr e.2.2⟩,
    Equiv.Perm.decomposeFin_symm_apply_zero 0 e.1⟩
  left_inv σ := by
    apply Subtype.ext
    show Equiv.Perm.decomposeFin.symm (0, (Equiv.Perm.decomposeFin σ.1).2) = σ.1
    exact (decomposeFin_eq_symm_zero σ.1 σ.2.2).symm
  right_inv e := by
    apply Subtype.ext
    show (Equiv.Perm.decomposeFin (Equiv.Perm.decomposeFin.symm (0, e.1))).2 = e.1
    rw [Equiv.apply_symm_apply]

/-- Involutions of `Fin (n + 2)` with at most one fixed point that move `0` are in
bijection with pairs of an element `j : Fin (n + 1)` and an involution of `Fin n` with
at most one fixed point. -/
noncomputable def vtxSuccEquiv (n : ℕ) :
    {σ : Equiv.Perm (Fin (n + 2)) //
      (Function.Involutive σ ∧ (Finset.univ.filter fun x => σ x = x).card ≤ 1) ∧ σ 0 ≠ 0} ≃
        Fin (n + 1) × vtxSubtype n where
  toFun σ := ⟨partner σ.1 σ.2.2,
    restrictPerm _ (invol_decomposeFin_symm σ.1 σ.2.2 σ.2.1.1).2,
    restrictPerm_involutive _ (invol_decomposeFin_symm σ.1 σ.2.2 σ.2.1.1).1 _,
    card_e_le_one σ.1 σ.2.2 σ.2.1.1 σ.2.1.2⟩
  invFun jτ := ⟨Equiv.Perm.decomposeFin.symm (jτ.1.succ, extendPerm jτ.1 jτ.2.1),
    ⟨(involutive_symm_succ jτ.1 _).mpr ⟨extendPerm_involutive jτ.1 jτ.2.2.1,
        extendPerm_apply_self jτ.1 jτ.2.1⟩,
      card_extend_le_one jτ.1 jτ.2.1 jτ.2.2.1 jτ.2.2.2⟩,
    by rw [Equiv.Perm.decomposeFin_symm_apply_zero]; exact Fin.succ_ne_zero _⟩
  left_inv σ := by
    apply Subtype.ext
    show Equiv.Perm.decomposeFin.symm ((partner σ.1 σ.2.2).succ, _) = σ.1
    rw [extendPerm_restrictPerm]
    exact (decomposeFin_eq_symm_partner σ.1 σ.2.2).symm
  right_inv jτ := by
    obtain ⟨j, τ⟩ := jτ
    apply Prod.ext
    · have h0 : (Equiv.Perm.decomposeFin.symm (j.succ, extendPerm j τ.1)) 0 ≠ 0 := by
        rw [Equiv.Perm.decomposeFin_symm_apply_zero]
        exact Fin.succ_ne_zero _
      exact partner_symm_succ j (extendPerm j τ.1) h0
    · apply Subtype.ext
      have h0 : (Equiv.Perm.decomposeFin.symm (j.succ, extendPerm j τ.1)) 0 ≠ 0 := by
        rw [Equiv.Perm.decomposeFin_symm_apply_zero]
        exact Fin.succ_ne_zero _
      have hinv : Function.Involutive (Equiv.Perm.decomposeFin.symm (j.succ, extendPerm j τ.1)) :=
        (involutive_symm_succ j _).mpr ⟨extendPerm_involutive j τ.2.1,
          extendPerm_apply_self j τ.1⟩
      show restrictPerm (Equiv.Perm.decomposeFin (Equiv.Perm.decomposeFin.symm (j.succ,
          extendPerm j τ.1))).2 (invol_decomposeFin_symm _ h0 hinv).2 = τ.1
      simp only [Equiv.apply_symm_apply]
      exact restrictPerm_extendPerm j τ.1

/-- The full decomposition for involutions with at most one fixed point. -/
noncomputable def vtxDecomposeEquiv (n : ℕ) :
    vtxSubtype (n + 2) ≃ fpfSubtype (n + 1) ⊕ Fin (n + 1) × vtxSubtype n :=
  (splitZeroEquiv n).trans (Equiv.sumCongr (vtxZeroEquiv n) (vtxSuccEquiv n))

/-! ### Cardinality recurrences -/

theorem fcard_succ_succ (n : ℕ) : fcard (n + 2) = (n + 1) * fcard n := by
  unfold fcard
  rw [Fintype.card_congr (fpfDecomposeEquiv n), Fintype.card_prod, Fintype.card_fin]

theorem vcard_succ_succ (n : ℕ) : vcard (n + 2) = fcard (n + 1) + (n + 1) * vcard n := by
  unfold vcard fcard
  rw [Fintype.card_congr (vtxDecomposeEquiv n), Fintype.card_sum, Fintype.card_prod,
    Fintype.card_fin]

theorem fcard_zero : fcard 0 = 1 := by
  have e : fpfSubtype 0 ≃ Equiv.Perm (Fin 0) :=
    Equiv.subtypeUnivEquiv fun σ => ⟨fun x => x.elim0, fun x => x.elim0⟩
  unfold fcard
  rw [Fintype.card_congr e, Fintype.card_perm, Fintype.card_fin, Nat.factorial_zero]

theorem fcard_one : fcard 1 = 0 := by
  unfold fcard
  haveI : IsEmpty (fpfSubtype 1) := ⟨fun σ => σ.2.2 0 (Fin.eq_zero _)⟩
  exact Fintype.card_of_isEmpty

theorem vcard_zero : vcard 0 = 1 := by
  have e : vtxSubtype 0 ≃ Equiv.Perm (Fin 0) :=
    Equiv.subtypeUnivEquiv fun σ =>
      ⟨fun x => x.elim0, Finset.card_le_one.mpr fun a _ _ _ => a.elim0⟩
  unfold vcard
  rw [Fintype.card_congr e, Fintype.card_perm, Fintype.card_fin, Nat.factorial_zero]

theorem vcard_one : vcard 1 = 1 := by
  have key : ∀ σ : Equiv.Perm (Fin 1),
      Function.Involutive σ ∧ (Finset.univ.filter fun x => σ x = x).card ≤ 1 := by
    intro σ
    refine ⟨fun x => ?_, Finset.card_le_one.mpr fun a _ b _ => ?_⟩
    · rw [Fin.eq_zero (σ (σ x)), Fin.eq_zero x]
    · rw [Fin.eq_zero a, Fin.eq_zero b]
  have e : vtxSubtype 1 ≃ Equiv.Perm (Fin 1) := Equiv.subtypeUnivEquiv key
  unfold vcard
  rw [Fintype.card_congr e, Fintype.card_perm, Fintype.card_fin, Nat.factorial_one]

/-! ### Parity -/

theorem fcard_parity (n : ℕ) : (Even n → Odd (fcard n)) ∧ (Odd n → fcard n = 0) := by
  induction n using Nat.twoStepInduction with
  | zero =>
    refine ⟨fun _ => by rw [fcard_zero]; exact odd_one, fun h => ?_⟩
    rw [Nat.odd_iff] at h
    simp at h
  | one =>
    refine ⟨fun h => ?_, fun _ => fcard_one⟩
    rw [Nat.even_iff] at h
    simp at h
  | more n ihn _ =>
    constructor
    · intro hn
      rw [fcard_succ_succ]
      have hn' : Even n := by
        rw [Nat.even_iff] at hn ⊢
        omega
      have ho : Odd (n + 1) := by
        rw [Nat.odd_iff]
        rw [Nat.even_iff] at hn'
        omega
      exact ho.mul (ihn.1 hn')
    · intro hn
      rw [fcard_succ_succ, ihn.2 (by
        rw [Nat.odd_iff] at hn ⊢
        omega), Nat.mul_zero]

theorem vcard_odd (n : ℕ) : Odd (vcard n) := by
  induction n using Nat.twoStepInduction with
  | zero => rw [vcard_zero]; exact odd_one
  | one => rw [vcard_one]; exact odd_one
  | more n ihn _ =>
    rw [vcard_succ_succ]
    rcases Nat.even_or_odd n with hn | hn
    · have ho : Odd (n + 1) := by
        rw [Nat.odd_iff]
        rw [Nat.even_iff] at hn
        omega
      have h1 : fcard (n + 1) = 0 := (fcard_parity (n + 1)).2 ho
      rw [h1, Nat.zero_add]
      exact ho.mul ihn
    · have he : Even (n + 1) := by
        rw [Nat.even_iff]
        rw [Nat.odd_iff] at hn
        omega
      have h2 : Odd (fcard (n + 1)) := (fcard_parity (n + 1)).1 he
      exact h2.add_even (he.mul_right (vcard n))

end usa2018p6_aux

/-- The number of involutions of `Fin n` with at most one fixed point is odd. -/
theorem odd_card_vertex (n : ℕ) :
    Odd (Fintype.card {σ : Equiv.Perm (Fin n) //
      Function.Involutive σ ∧ (Finset.univ.filter fun x => σ x = x).card ≤ 1}) :=
  usa2018p6_aux.vcard_odd n

snip end

/-- Summed `Nat.ModEq` over a finset. -/
lemma sum_modEq_of_forall {ι : Type*} [DecidableEq ι] (s : Finset ι) (f g : ι → ℕ)
    (h : ∀ i ∈ s, f i ≡ g i [MOD 2]) : (∑ i ∈ s, f i) ≡ (∑ i ∈ s, g i) [MOD 2] := by
  induction s using Finset.induction with
  | empty => exact Nat.ModEq.rfl
  | insert a s has ih =>
    rw [Finset.sum_insert has, Finset.sum_insert has]
    exact Nat.ModEq.add (h a (Finset.mem_insert_self a s))
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-- USAMO 2018, Problem 6: the number of permutations of `(1, …, n)` whose ratios
`xₖ/k` are all distinct is odd for every `n ≥ 1`. -/
problem usa2018_p6 (n : ℕ) (_hn : 1 ≤ n) :
    Odd (Fintype.card {σ : Equiv.Perm (Fin n) // Valid σ}) := by
  classical
  -- Step 1: inversion is an involution on valid permutations, so the count is
  -- congruent modulo two to the number of valid involutions.
  have step1 : Fintype.card {σ : Equiv.Perm (Fin n) // Valid σ} ≡
      Fintype.card {σ : Equiv.Perm (Fin n) // Valid σ ∧ Function.Involutive σ} [MOD 2] := by
    let f : {σ : Equiv.Perm (Fin n) // Valid σ} → {σ : Equiv.Perm (Fin n) // Valid σ} :=
      fun σ => ⟨σ.1⁻¹, valid_inv σ.2⟩
    have hf : Function.Involutive f := by
      intro σ
      apply Subtype.ext
      show (σ.1⁻¹)⁻¹ = σ.1
      exact inv_inv σ.1
    have h1 := card_modEq_of_involutive f hf
    have he : Fintype.card {x // f x = x} =
        Fintype.card {σ : Equiv.Perm (Fin n) // Valid σ ∧ Function.Involutive σ} := by
      apply Fintype.card_congr
      exact {
        toFun := fun x => ⟨x.1.1, x.1.2, by
          have h : (x.1.1)⁻¹ = x.1.1 := congrArg Subtype.val x.2
          exact fun y => by
            have h2 : x.1.1 * x.1.1 = 1 := by
              have h3 := mul_inv_cancel (x.1.1)
              rwa [h] at h3
            have h3 := Equiv.Perm.mul_apply (x.1.1) (x.1.1) y
            rw [h2, Equiv.Perm.one_apply] at h3
            exact h3.symm⟩
        invFun := fun σ => ⟨⟨σ.1, σ.2.1⟩, Subtype.ext (by
          show (σ.1)⁻¹ = σ.1
          exact inv_eq_of_mul_eq_one_left (Perm_mul_self_eq_one_of_involutive σ.2.2))⟩
        left_inv := fun x => rfl
        right_inv := fun σ => rfl }
    exact h1.trans (he ▸ Nat.ModEq.rfl)
  -- Step 2: valid involutions are exactly the fantastic vertices.
  have step2 : Fintype.card {σ : Equiv.Perm (Fin n) // Valid σ ∧ Function.Involutive σ} =
      Fintype.card {v : {σ : Equiv.Perm (Fin n) // IsVertex σ} // Fantastic v.1} := by
    apply Fintype.card_congr
    exact {
      toFun := fun σ => ⟨⟨σ.1, σ.2.2, ((valid_iff_of_involutive σ.2.2).1 σ.2.1).1⟩,
        ((valid_iff_of_involutive σ.2.2).1 σ.2.1).2⟩
      invFun := fun v => ⟨v.1.1, (valid_iff_of_involutive v.1.2.1).2 ⟨v.1.2.2, v.2⟩, v.1.2.1⟩
      left_inv := fun σ => rfl
      right_inv := fun v => rfl }
  -- Step 3: the flip involution on pairs `(σ, φ)` shows the number of pairs is
  -- congruent to the number of vertices.
  have hterm : ∀ v : {σ : Equiv.Perm (Fin n) // IsVertex σ},
      Fintype.card {φ : Equiv.Perm (Fin n) // IsSwitch v.1 φ} ≡
        (if Fantastic v.1 then 1 else 0) [MOD 2] := by
    intro v
    by_cases hf : Fantastic v.1
    · rw [if_pos hf, card_switch_eq_one_of_fantastic hf]
    · rw [if_neg hf]
      obtain ⟨k, hk⟩ := even_card_switch_of_not_fantastic v.2.1 hf
      rw [hk]
      have : (k + k) % 2 = 0 := by omega
      exact this
  have heW : WPairs n ≃ Σ v : {σ : Equiv.Perm (Fin n) // IsVertex σ},
      {φ : Equiv.Perm (Fin n) // IsSwitch v.1 φ} := {
    toFun := fun p => ⟨⟨p.1.1, p.2.1⟩, ⟨p.1.2, p.2.2⟩⟩
    invFun := fun v => ⟨(v.1.1, v.2.1), v.1.2, v.2.2⟩
    left_inv := fun p => rfl
    right_inv := fun v => rfl }
  have hW : Fintype.card (WPairs n) = ∑ v : {σ : Equiv.Perm (Fin n) // IsVertex σ},
      Fintype.card {φ : Equiv.Perm (Fin n) // IsSwitch v.1 φ} := by
    rw [Fintype.card_congr heW, Fintype.card_sigma]
  have hfilter : (∑ v : {σ : Equiv.Perm (Fin n) // IsVertex σ},
        (if Fantastic v.1 then 1 else 0)) =
      Fintype.card {v : {σ : Equiv.Perm (Fin n) // IsVertex σ} // Fantastic v.1} := by
    rw [Finset.sum_boole, eq_comm]
    exact Fintype.card_of_subtype _ (fun v => by simp)
  have step3 : Fintype.card {v : {σ : Equiv.Perm (Fin n) // IsVertex σ} // Fantastic v.1} ≡
      Fintype.card (WPairs n) [MOD 2] := by
    have e1 : (∑ v : {σ : Equiv.Perm (Fin n) // IsVertex σ},
          Fintype.card {φ : Equiv.Perm (Fin n) // IsSwitch v.1 φ}) ≡
        Fintype.card {v : {σ : Equiv.Perm (Fin n) // IsVertex σ} // Fantastic v.1} [MOD 2] :=
      (sum_modEq_of_forall _ _ _ (fun v _ => hterm v)).trans (by rw [hfilter])
    rw [hW]
    exact e1.symm
  -- Step 4: the flip is an involution on `W` whose fixed points are the pairs `(σ, 1)`.
  have step4 : Fintype.card (WPairs n) ≡ Fintype.card {σ : Equiv.Perm (Fin n) // IsVertex σ} [MOD 2] := by
    let f : WPairs n → WPairs n := fun p =>
      ⟨(conjPerm p.1.1 p.1.2 * p.1.1 * conjPerm p.1.1 p.1.2, newSwitch p.1.1 p.1.2),
        flipPair_mem p.2.1 p.2.2⟩
    have hf : Function.Involutive f := by
      intro p
      apply Subtype.ext
      show flipPair (flipPair p.1) = p.1
      exact flipPair_involutive_on p.2.1.1 p.2.2
    have h1 := card_modEq_of_involutive f hf
    have he : Fintype.card {x // f x = x} =
        Fintype.card {σ : Equiv.Perm (Fin n) // IsVertex σ} := by
      apply Fintype.card_congr
      exact {
        toFun := fun x => ⟨x.1.1.1, x.1.2.1⟩
        invFun := fun v => ⟨⟨(v.1, 1), v.2, isSwitch_id⟩,
          Subtype.ext (flipPair_eq_self_of_eq_one rfl)⟩
        left_inv := fun x => by
          apply Subtype.ext
          apply Subtype.ext
          show ((x.1.1.1, 1) : Equiv.Perm (Fin n) × Equiv.Perm (Fin n)) = x.1.1
          have h2 : x.1.1.2 = 1 :=
            flipPair_eq_self_iff x.1.2.1.1 x.1.2.2 (congrArg Subtype.val x.2)
          apply Prod.ext
          · rfl
          · exact h2.symm
        right_inv := fun v => rfl }
    have h2 : Fintype.card {x // f x = x} ≡
        Fintype.card {σ : Equiv.Perm (Fin n) // IsVertex σ} [MOD 2] := by
      rw [he]
    exact h1.trans h2
  -- Step 5: the number of vertices is odd (delegated counting module).
  have step5 : Odd (Fintype.card {σ : Equiv.Perm (Fin n) // IsVertex σ}) :=
    odd_card_vertex n
  -- Chain the congruences.
  have h := ((step1.trans (step2 ▸ Nat.ModEq.rfl)).trans step3).trans step4
  have h1 : (Fintype.card {σ : Equiv.Perm (Fin n) // Valid σ}) % 2 = 1 := by
    rw [h]
    exact Nat.odd_iff.1 step5
  exact Nat.odd_iff.2 h1

end Usa2018P6
