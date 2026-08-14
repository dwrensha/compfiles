/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.AffineMonoid.Basic
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.GroupTheory.Perm.Fin
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics] }

/-!
# USA Mathematical Olympiad 2017, Problem 2

Let $m_1, m_2, \ldots, m_n$ be a collection of $n$ positive integers, not necessarily
distinct. For any sequence of integers $A = (a_1, \ldots, a_n)$ and any permutation
$w = w_1 w_2 \cdots w_n$ of $m_1, \ldots, m_n$, define an $A$-inversion of $w$ to be a
pair of entries $w_i, w_j$ with $i < j$ for which one of the following conditions holds:
* $a_i \ge w_i > w_j$,
* $w_j > a_i \ge w_i$, or
* $w_i > w_j > a_i$.

Show that, for any two sequences of integers $A = (a_1, \ldots, a_n)$ and
$B = (b_1, \ldots, b_n)$, and for any positive integer $k$, the number of permutations of
$m_1, \ldots, m_n$ having exactly $k$ A-inversions is equal to the number of permutations
of $m_1, \ldots, m_n$ having exactly $k$ B-inversions.
-/

namespace Usa2017P2

open Finset Polynomial Equiv

snip begin

/-!
## Basic definitions

We count permutations of the multiset of entries *with multiplicity*, i.e. a permutation
is an element `σ` of `Equiv.Perm (Fin n)` and the entry at position `i` is `m (σ i)`.
This is the counting used in the official solution; it differs from the count over
distinct arrangements only by a factor `∏ (multiplicity)!` which is independent of `A`
and `k`, so both readings of the problem are equivalent.
-/

/-- The `A`-inversion relation on a pair of entries: `x` is the left entry (at position
`i`, with threshold `c = a_i`) and `y` is the right entry. -/
def invPair (c x y : ℤ) : Prop := (x ≤ c ∧ y < x) ∨ (c < y ∧ x ≤ c) ∨ (y < x ∧ c < y)

instance (c x y : ℤ) : Decidable (invPair c x y) := by
  unfold invPair; infer_instance

/-- The number of `A`-inversions of the permutation `σ`. -/
def ainvCount {n : ℕ} (m : Fin n → ℤ) (A : Fin n → ℤ) (σ : Perm (Fin n)) : ℕ :=
  ∑ i : Fin n, ∑ j : Fin n, if i < j ∧ invPair (A i) (m (σ i)) (m (σ j)) then 1 else 0

/-- The generating function `∑ σ, X ^ (ainvCount m A σ)` of the `A`-inversion statistic. -/
noncomputable def genFun {n : ℕ} (m : Fin n → ℤ) (A : Fin n → ℤ) : ℤ[X] :=
  ∑ σ : Perm (Fin n), X ^ ainvCount m A σ

/-- The geometric sum `1 + X + ⋯ + X^(t-1)`. -/
noncomputable def qq (t : ℕ) : ℤ[X] := ∑ s ∈ range t, X ^ s

/-- The multiset of values of the entries. -/
def valMul {n : ℕ} (m : Fin n → ℤ) : Multiset ℤ := Finset.univ.val.map m

/-- The multiplicity of the value `v` among the entries. -/
def eCnt {n : ℕ} (m : Fin n → ℤ) (v : ℤ) : ℕ := (valMul m).count v

/-- The number of entries satisfying `p`. -/
def cntP {n : ℕ} (m : Fin n → ℤ) (p : ℤ → Prop) [DecidablePred p] : ℕ :=
  (valMul m).countP p

/-- The number of inversions contributed by the first position when it has entry `x` and
threshold `c`, over the remaining entries `w`. -/
def frontContrib {t : ℕ} (c x : ℤ) (w : Fin t → ℤ) : ℕ :=
  ∑ ℓ : Fin t, if invPair c x (w ℓ) then 1 else 0

/-- The embedding `Fin n ↪ Fin (n+1)` whose range is everything except `p`, as used in
`Equiv.Perm.decomposeFin`. -/
def skipEmb {n : ℕ} (p : Fin (n + 1)) : Fin n ↪ Fin (n + 1) where
  toFun i := Equiv.swap 0 p i.succ
  inj' := fun _ _ h => Fin.succ_injective _ ((Equiv.swap 0 p).injective h)

/-- Compact characterization of `invPair`: the pair is an inversion iff the truth values
"`c` lies in the half-open interval between the entries" and "`x > y`" differ. -/
lemma invPair_iff (c x y : ℤ) :
    invPair c x y ↔ (y < x ∧ (x ≤ c ∨ c < y)) ∨ (x ≤ y ∧ x ≤ c ∧ c < y) := by
  unfold invPair; lia

lemma frontContrib_le {t : ℕ} (c x : ℤ) (w : Fin t → ℤ) (h : x ≤ c) :
    frontContrib c x w =
      (∑ ℓ : Fin t, if w ℓ < x then 1 else 0) + ∑ ℓ : Fin t, if c < w ℓ then 1 else 0 := by
  unfold frontContrib
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro ℓ _
  have hiff : invPair c x (w ℓ) ↔ (w ℓ < x ∨ c < w ℓ) := by
    rw [invPair_iff]; lia
  by_cases h1 : w ℓ < x
  · by_cases h2 : c < w ℓ
    · exfalso; lia
    · rw [ite_eq_left (hiff.mpr (Or.inl h1)), ite_eq_left h1, ite_eq_right h2]
  · by_cases h2 : c < w ℓ
    · rw [ite_eq_left (hiff.mpr (Or.inr h2)), ite_eq_right h1, ite_eq_left h2]
    · rw [ite_eq_right (fun hp => (hiff.mp hp).elim h1 h2), ite_eq_right h1, ite_eq_right h2]

lemma frontContrib_gt {t : ℕ} (c x : ℤ) (w : Fin t → ℤ) (h : c < x) :
    frontContrib c x w = ∑ ℓ : Fin t, if c < w ℓ ∧ w ℓ < x then 1 else 0 := by
  unfold frontContrib
  apply Finset.sum_congr rfl; intro ℓ _
  have hiff : invPair c x (w ℓ) ↔ (c < w ℓ ∧ w ℓ < x) := by
    rw [invPair_iff]; lia
  by_cases h1 : c < w ℓ ∧ w ℓ < x
  · rw [ite_eq_left (hiff.mpr h1), ite_eq_left h1]
  · rw [ite_eq_right (fun hp => h1 (hiff.mp hp)), ite_eq_right h1]

lemma skipEmb_ne {n : ℕ} (p : Fin (n + 1)) (i : Fin n) : skipEmb p i ≠ p := by
  have h : Equiv.swap 0 p i.succ ≠ Equiv.swap 0 p 0 :=
    fun hh => Fin.succ_ne_zero i ((Equiv.swap 0 p).injective hh)
  rwa [Equiv.swap_apply_left] at h

/-- Splitting a sum over `Fin (n+1)` into the term at `p` and the rest. -/
lemma sum_univ_add_skipEmb {n : ℕ} {M : Type*} [AddCommMonoid M] (p : Fin (n + 1))
    (g : Fin (n + 1) → M) : ∑ i, g i = g p + ∑ i : Fin n, g (skipEmb p i) := by
  have himg : univ.image (skipEmb p) = univ.erase p := by
    ext x
    constructor
    · intro h
      obtain ⟨i, -, rfl⟩ := mem_image.mp h
      exact mem_erase.mpr ⟨skipEmb_ne p i, mem_univ _⟩
    · intro h
      obtain ⟨hxp, -⟩ := mem_erase.mp h
      have h1 : Equiv.swap 0 p x ≠ 0 := by
        intro hh
        exact hxp ((Equiv.swap 0 p).injective (hh.trans (Equiv.swap_apply_right 0 p).symm))
      obtain ⟨i, hi⟩ := Fin.eq_succ_of_ne_zero h1
      refine mem_image.mpr ⟨i, mem_univ _, ?_⟩
      show Equiv.swap 0 p i.succ = x
      rw [← hi]; exact swap_apply_self 0 p x
  rw [← Finset.add_sum_erase univ g (mem_univ p), ← himg, Finset.sum_image]
  intro i _ j _ h
  exact (skipEmb p).injective h

/-- Relabeling the entries by a permutation does not change the number of `A`-inversions
(thresholds are positional). -/
lemma ainvCount_comp {n : ℕ} (e : Perm (Fin n)) (m : Fin n → ℤ) (A : Fin n → ℤ)
    (σ : Perm (Fin n)) : ainvCount (m ∘ e) A σ = ainvCount m A (e * σ) := rfl

lemma genFun_comp {n : ℕ} (e : Perm (Fin n)) (m : Fin n → ℤ) (A : Fin n → ℤ) :
    genFun (m ∘ e) A = genFun m A := by
  unfold genFun
  simp_rw [ainvCount_comp]
  exact Equiv.sum_comp (Equiv.mulLeft e) (fun σ => X ^ ainvCount m A σ)

/-- The first-position decomposition of the inversion count: under
`Equiv.Perm.decomposeFin`, the `A`-inversions split into the pairs involving the first
position (`frontContrib`) and the inversions of the remaining permutation. -/
lemma ainvCount_decompose {n : ℕ} (m : Fin (n + 1) → ℤ) (A : Fin (n + 1) → ℤ)
    (p : Fin (n + 1)) (π : Perm (Fin n)) :
    ainvCount m A (Equiv.Perm.decomposeFin.symm (p, π)) =
      frontContrib (A 0) (m p) (m ∘ skipEmb p) + ainvCount (m ∘ skipEmb p) (A ∘ Fin.succ) π := by
  have h0 : Equiv.Perm.decomposeFin.symm (p, π) 0 = p :=
    Equiv.Perm.decomposeFin_symm_apply_zero p π
  have hs : ∀ i : Fin n, Equiv.Perm.decomposeFin.symm (p, π) i.succ = skipEmb p (π i) :=
    fun i => Equiv.Perm.decomposeFin_symm_apply_succ π p i
  unfold ainvCount frontContrib
  rw [Fin.sum_univ_succ]
  congr 1
  · -- the pairs with left index `0`
    rw [Fin.sum_univ_succ]
    have hz : (if (0 : Fin (n + 1)) < 0 ∧ invPair (A 0)
        (m (Equiv.Perm.decomposeFin.symm (p, π) 0))
        (m (Equiv.Perm.decomposeFin.symm (p, π) 0)) then (1 : ℕ) else 0) = 0 :=
      ite_eq_right (fun h => lt_irrefl _ h.1)
    rw [hz, zero_add]
    rw [← Equiv.sum_comp π (fun ℓ => if invPair (A 0) (m p) ((m ∘ skipEmb p) ℓ) then (1 : ℕ) else 0)]
    apply Finset.sum_congr rfl; intro j _
    refine if_congr ?_ rfl rfl
    rw [h0, hs]
    constructor
    · exact And.right
    · intro hP
      exact ⟨lt_of_le_of_ne (Fin.zero_le _) (Ne.symm (Fin.succ_ne_zero j)), hP⟩
  · -- the pairs with left index `i.succ`
    apply Finset.sum_congr rfl; intro i _
    rw [Fin.sum_univ_succ]
    have hz : (if i.succ < (0 : Fin (n + 1)) ∧ invPair (A i.succ)
        (m (Equiv.Perm.decomposeFin.symm (p, π) i.succ))
        (m (Equiv.Perm.decomposeFin.symm (p, π) 0)) then (1 : ℕ) else 0) = 0 :=
      ite_eq_right (fun h => Fin.not_lt_zero _ h.1)
    rw [hz, zero_add]
    apply Finset.sum_congr rfl; intro j _
    refine if_congr ?_ rfl rfl
    rw [hs, hs]
    constructor
    · intro h
      exact ⟨Fin.strictMono_succ.lt_iff_lt.mp h.1, h.2⟩
    · intro h
      exact ⟨Fin.strictMono_succ.lt_iff_lt.mpr h.1, h.2⟩

/-- The first-position recurrence for the generating function. -/
lemma genFun_rec {n : ℕ} (m : Fin (n + 1) → ℤ) (A : Fin (n + 1) → ℤ) :
    genFun m A = ∑ p : Fin (n + 1),
      X ^ frontContrib (A 0) (m p) (m ∘ skipEmb p) * genFun (m ∘ skipEmb p) (A ∘ Fin.succ) := by
  unfold genFun
  rw [← Equiv.sum_comp Equiv.Perm.decomposeFin.symm, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl; intro p _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro π _
  rw [ainvCount_decompose, pow_add]

/-! ## Multiset-of-values bookkeeping -/

lemma sum_if_eq_count {n : ℕ} (m : Fin n → ℤ) (y : ℤ) :
    (∑ i : Fin n, if m i = y then (1 : ℕ) else 0) = (valMul m).count y := by
  rw [← Finset.card_filter]
  have h : univ.filter (fun i => m i = y) = univ.filter (fun i => y = m i) :=
    Finset.filter_congr fun i _ => eq_comm
  rw [h]
  show (univ.filter (fun i => y = m i)).card = (univ.val.map m).countP (y = ·)
  rw [Multiset.countP_map]
  rfl

lemma sum_if_eq_cntP {n : ℕ} (m : Fin n → ℤ) (q : ℤ → Prop) [DecidablePred q] :
    (∑ i : Fin n, if q (m i) then (1 : ℕ) else 0) = cntP m q := by
  rw [← Finset.card_filter]
  show (univ.filter (fun i => q (m i))).card = (univ.val.map m).countP q
  rw [Multiset.countP_map]
  rfl

lemma eCnt_eq_card_filter {n : ℕ} (m : Fin n → ℤ) (v : ℤ) :
    eCnt m v = (univ.filter (fun i => m i = v)).card := by
  rw [Finset.card_filter]
  exact (sum_if_eq_count m v).symm

/-- Deleting one occurrence of a value from the entry multiset. -/
lemma valMul_comp_skipEmb {n : ℕ} (m : Fin (n + 1) → ℤ) (p : Fin (n + 1)) :
    valMul (m ∘ skipEmb p) = (valMul m).erase (m p) := by
  have key : ∀ y : ℤ, (valMul m).count y =
      (valMul (m ∘ skipEmb p)).count y + (if m p = y then 1 else 0) := by
    intro y
    have h := sum_univ_add_skipEmb p (fun i => if m i = y then (1 : ℕ) else 0)
    rw [sum_if_eq_count m y] at h
    have hcomp : (∑ i : Fin n, if m ((skipEmb p) i) = y then (1 : ℕ) else 0) =
        ∑ i : Fin n, if (m ∘ skipEmb p) i = y then (1 : ℕ) else 0 := rfl
    rw [hcomp, sum_if_eq_count] at h
    rw [h, add_comm]
  apply Multiset.ext.mpr; intro y
  have keyy := key y
  by_cases hy : m p = y
  · subst hy
    rw [ite_eq_left rfl] at keyy
    rw [Multiset.count_erase_self]
    lia
  · rw [ite_eq_right hy] at keyy
    rw [Multiset.count_erase_of_ne (Ne.symm hy)]
    lia

/-- Two entry functions with the same multiset of values differ by a permutation of the
indices. -/
lemma exists_perm_of_valMul_eq {n : ℕ} :
    ∀ {m₁ m₂ : Fin n → ℤ}, valMul m₁ = valMul m₂ → ∃ e : Perm (Fin n), m₂ = m₁ ∘ e := by
  induction n with
  | zero =>
    intro m₁ m₂ _
    exact ⟨1, funext fun i => i.elim0⟩
  | succ n ih =>
    intro m₁ m₂ h
    have hmem : m₂ 0 ∈ valMul m₁ := by
      rw [h]
      exact Multiset.mem_map.mpr ⟨0, Finset.mem_val.mpr (mem_univ 0), rfl⟩
    obtain ⟨p, -, hp⟩ := Multiset.mem_map.mp hmem
    have h2 : valMul (m₁ ∘ skipEmb p) = valMul (m₂ ∘ skipEmb 0) := by
      rw [valMul_comp_skipEmb, valMul_comp_skipEmb, hp, h]
    obtain ⟨e', he'⟩ := ih h2
    refine ⟨Equiv.Perm.decomposeFin.symm (p, e'), funext fun i => Fin.cases ?_ ?_ i⟩
    · show m₂ 0 = (m₁ ∘ Equiv.Perm.decomposeFin.symm (p, e')) 0
      rw [Function.comp_apply, Equiv.Perm.decomposeFin_symm_apply_zero, hp]
    · intro i
      have h2i := congr_fun he' i
      simp only [Function.comp_apply] at h2i
      have hs0 : (skipEmb (0 : Fin (n + 1))) i = i.succ := by
        show Equiv.swap 0 (0 : Fin (n + 1)) i.succ = i.succ
        rw [Equiv.swap_self]; rfl
      rw [hs0] at h2i
      show m₂ i.succ = (m₁ ∘ Equiv.Perm.decomposeFin.symm (p, e')) i.succ
      rw [Function.comp_apply, Equiv.Perm.decomposeFin_symm_apply_succ]
      exact h2i

/-- The generating function only depends on the multiset of values. -/
lemma genFun_eq_of_valMul_eq {n : ℕ} {m₁ m₂ : Fin n → ℤ} (h : valMul m₁ = valMul m₂)
    (A : Fin n → ℤ) : genFun m₁ A = genFun m₂ A := by
  obtain ⟨e, rfl⟩ := exists_perm_of_valMul_eq h
  exact (genFun_comp e m₁ A).symm

/-- Explicit evaluation of `frontContrib` in terms of the full entry multiset. -/
lemma frontContrib_eval {n : ℕ} (m : Fin (n + 1) → ℤ) (c : ℤ) (p : Fin (n + 1)) :
    frontContrib c (m p) (m ∘ skipEmb p) =
      if m p ≤ c then cntP m (· < m p) + cntP m (c < ·)
      else cntP m (fun y => c < y ∧ y < m p) := by
  by_cases h : m p ≤ c
  · rw [ite_eq_left h, frontContrib_le c (m p) (m ∘ skipEmb p) h]
    congr 1
    · have h2 := sum_univ_add_skipEmb p (fun i => if m i < m p then (1 : ℕ) else 0)
      rw [ite_eq_right (lt_irrefl _), zero_add] at h2
      have h3 : (∑ i : Fin (n + 1), if m i < m p then (1 : ℕ) else 0) = cntP m (· < m p) :=
        sum_if_eq_cntP m (· < m p)
      rw [h3] at h2
      simp only [Function.comp_apply]
      exact h2.symm
    · have h2 := sum_univ_add_skipEmb p (fun i => if c < m i then (1 : ℕ) else 0)
      rw [ite_eq_right (not_lt.mpr h), zero_add] at h2
      have h3 : (∑ i : Fin (n + 1), if c < m i then (1 : ℕ) else 0) = cntP m (c < ·) :=
        sum_if_eq_cntP m (c < ·)
      rw [h3] at h2
      simp only [Function.comp_apply]
      exact h2.symm
  · rw [ite_eq_right h, frontContrib_gt c (m p) (m ∘ skipEmb p) (not_le.mp h)]
    have h2 := sum_univ_add_skipEmb p (fun i => if c < m i ∧ m i < m p then (1 : ℕ) else 0)
    rw [ite_eq_right (fun hc => lt_irrefl _ hc.2), zero_add] at h2
    have h3 : (∑ i : Fin (n + 1), if c < m i ∧ m i < m p then (1 : ℕ) else 0) =
        cntP m (fun y => c < y ∧ y < m p) := sum_if_eq_cntP m (fun y => c < y ∧ y < m p)
    rw [h3] at h2
    simp only [Function.comp_apply]
    exact h2.symm

/-- The contribution of the first position, as a function of its value. -/
def gc {n : ℕ} (m : Fin n → ℤ) (c v : ℤ) : ℕ :=
  if v ≤ c then cntP m (· < v) + cntP m (c < ·) else cntP m (fun y => c < y ∧ y < v)

/-! ## The pure polynomial identity -/

lemma qq_add (a b : ℕ) : qq (a + b) = qq a + X ^ a * qq b := by
  unfold qq
  rw [Finset.sum_range_add, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  rw [pow_add]

lemma block_tele (es : List ℕ) :
    ∑ t ∈ range es.length, X ^ (es.take t).sum * qq es[t]! = qq es.sum := by
  induction es with
  | nil => simp [qq]
  | cons e es ih =>
    have hget0 : (e :: es)[0]! = e := List.getElem!_cons_zero
    rw [List.length_cons, Finset.sum_range_succ']
    simp only [List.take_zero, List.sum_nil, pow_zero, one_mul, hget0]
    rw [List.sum_cons, qq_add, add_comm (qq e)]
    congr 1
    rw [← ih, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    rw [List.take_succ_cons, List.sum_cons, List.getElem!_cons_succ, pow_add, mul_assoc]

lemma pureId (es : List ℕ) (k : ℕ) (hk : k ≤ es.length) :
    X ^ (es.sum - (es.take k).sum) *
        (∑ t ∈ range k, X ^ (es.take t).sum * qq es[t]!) +
      (∑ t ∈ Ico k es.length, X ^ ((es.take t).sum - (es.take k).sum) * qq es[t]!) =
      qq es.sum := by
  have hlen : (es.take k).length = k := by
    rw [List.length_take, Nat.min_eq_left hk]
  have hPkN : (es.take k).sum ≤ es.sum := by
    have h1 : es.sum = ((es.take k) ++ (es.drop k)).sum := by
      rw [List.take_append_drop]
    rw [h1, List.sum_append]
    exact Nat.le_add_right _ _
  have htake : ∀ t : ℕ, t ≤ k → (es.take k).take t = es.take t := fun t ht => by
    rw [List.take_take, Nat.min_eq_left ht]
  have hget : ∀ t : ℕ, t < k → (es.take k)[t]! = es[t]! := fun t ht => by
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_take_of_lt ht,
      ← List.getElem!_eq_getElem?_getD]
  have hmono : ∀ t : ℕ, k ≤ t → (es.take k).sum ≤ (es.take t).sum := by
    intro t ht
    have h1 : (es.take t).sum = ((es.take t).take k ++ (es.take t).drop k).sum := by
      rw [List.take_append_drop]
    have h2 : (es.take t).take k = es.take k := by
      rw [List.take_take, Nat.min_eq_left ht]
    rw [h1, List.sum_append, h2]
    exact Nat.le_add_right _ _
  have hS : ∑ t ∈ range k, X ^ (es.take t).sum * qq es[t]! = qq (es.take k).sum := by
    have hb := block_tele (es.take k)
    rw [hlen] at hb
    rw [← hb]
    apply Finset.sum_congr rfl
    intro t ht
    rw [htake t (Finset.mem_range.mp ht).le, hget t (Finset.mem_range.mp ht)]
  have hT : ∑ t ∈ Ico k es.length, X ^ (es.take t).sum * qq es[t]! =
      qq es.sum - qq (es.take k).sum := by
    have hb_es := block_tele es
    rw [← Finset.sum_range_add_sum_Ico (fun t => X ^ (es.take t).sum * qq es[t]!) hk,
      hS] at hb_es
    exact eq_sub_of_add_eq' hb_es
  have hT' : X ^ (es.take k).sum *
      (∑ t ∈ Ico k es.length, X ^ ((es.take t).sum - (es.take k).sum) * qq es[t]!) =
      ∑ t ∈ Ico k es.length, X ^ (es.take t).sum * qq es[t]! := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t ht
    have ht' : k ≤ t := (Finset.mem_Ico.mp ht).1
    rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' (hmono t ht')]
  have hXS : X ^ (es.take k).sum * (X ^ (es.sum - (es.take k).sum) *
      (∑ t ∈ range k, X ^ (es.take t).sum * qq es[t]!)) =
      X ^ es.sum * (∑ t ∈ range k, X ^ (es.take t).sum * qq es[t]!) := by
    rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' hPkN]
  apply mul_left_cancel₀ (pow_ne_zero (es.take k).sum X_ne_zero)
  rw [mul_add, hXS, hT', hS, hT]
  have e1 : X ^ es.sum - 1 = qq es.sum * (X - 1) := (geom_sum_mul X es.sum).symm
  have e2 : X ^ (es.take k).sum - 1 = qq (es.take k).sum * (X - 1) :=
    (geom_sum_mul X (es.take k).sum).symm
  have g1 : X ^ es.sum = qq es.sum * (X - 1) + 1 := by
    rw [← e1]; ring
  have g2 : X ^ (es.take k).sum = qq (es.take k).sum * (X - 1) + 1 := by
    rw [← e2]; ring
  rw [g1, g2]
  ring

-- ==== helpers ====

/-- The cardinality of a filter of a finite sum of multisets. -/
lemma multiset_card_filter_finset_sum {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → Multiset ℤ) (p : ℤ → Prop) [DecidablePred p] :
    Multiset.card (Multiset.filter p (∑ v ∈ s, f v)) =
      ∑ v ∈ s, Multiset.card (Multiset.filter p (f v)) := by
  induction s using Finset.induction with
  | empty => simp [Multiset.filter_zero]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Multiset.filter_add, Multiset.card_add, ih,
      Finset.sum_insert ha]

/-- Filtering a replicated multiset. -/
lemma multiset_filter_replicate (p : ℤ → Prop) [DecidablePred p] (k : ℕ) (v : ℤ) :
    Multiset.filter p (Multiset.replicate k v) = if p v then Multiset.replicate k v else 0 := by
  induction k with
  | zero => simp [Multiset.filter_zero]
  | succ k ih =>
    rw [Multiset.replicate_succ, Multiset.filter_cons, ih]
    by_cases hv : p v
    · simp only [ite_eq_left hv]
      rw [Multiset.singleton_add]
    · simp only [ite_eq_right hv]
      rw [Multiset.zero_add]

/-- Reindexing the sum of a mapped list as a sum over `range`. -/
lemma list_map_sum_eq_sum_range {α : Type*} {β : Type*} [Inhabited α] [AddCommMonoid β]
    (l : List α) (f : α → β) :
    (l.map f).sum = ∑ t ∈ Finset.range l.length, f l[t]! := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons, List.length_cons, Finset.sum_range_succ',
      List.getElem!_cons_zero, ih]
    have hs : (∑ t ∈ Finset.range l.length, f l[t]!) =
        ∑ t ∈ Finset.range l.length, f (a :: l)[t + 1]! := by
      apply Finset.sum_congr rfl
      intro t _
      rw [List.getElem!_cons_succ]
    rw [hs]
    exact add_comm _ _

/-- The sum of a list of naturals as a sum over `range`. -/
lemma list_sum_eq_sum_range (l : List ℕ) :
    l.sum = ∑ t ∈ Finset.range l.length, l[t]! := by
  have h := list_map_sum_eq_sum_range l id
  rw [List.map_id] at h
  exact h

/-- The sum of an initial segment of a list of naturals. -/
lemma list_sum_take_eq_sum_range (l : List ℕ) {j : ℕ} (hj : j ≤ l.length) :
    (l.take j).sum = ∑ t ∈ Finset.range j, l[t]! := by
  rw [list_sum_eq_sum_range (l.take j), List.length_take, Nat.min_eq_left hj]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Finset.mem_range] at ht
  have h1 : t < (l.take j).length := by
    rw [List.length_take]
    lia
  have h2 : t < l.length := by lia
  have g1 : (l.take j)[t]! = (l.take j)[t]'h1 := by
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem h1, Option.getD_some]
  have g2 : l[t]! = l[t]'h2 := by
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem h2, Option.getD_some]
  rw [g1, g2, List.getElem_take]

/-- In a sorted list of integers, the elements `≤ c` form an initial segment. -/
lemma sorted_filter_eq_take (l : List ℤ) (c : ℤ) (hp : l.Pairwise (· ≤ ·)) :
    l.filter (· ≤ c) = l.take (l.filter (· ≤ c)).length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.pairwise_cons] at hp
    obtain ⟨hhd, htl⟩ := hp
    by_cases hac : a ≤ c
    · rw [List.filter_cons_of_pos (p := fun x => decide (x ≤ c)) (decide_eq_true hac),
        List.length_cons, List.take_succ_cons, ← ih htl]
    · rw [List.filter_cons_of_neg (p := fun x => decide (x ≤ c))
        (by simpa only [decide_eq_true_eq] using hac)]
      have hempty : l.filter (· ≤ c) = [] := by
        rw [List.filter_eq_nil_iff]
        intro y hy
        have hay : a ≤ y := hhd y hy
        have hcy : c < y := lt_of_lt_of_le (not_le.mp hac) hay
        show ¬ decide (y ≤ c) = true
        rw [decide_eq_true_eq]
        exact not_le.mpr hcy
      rw [hempty, List.length_nil, List.take_zero]

/-- A sorted list of distinct integers is strictly increasing. -/
lemma sorted_get_lt_iff {l : List ℤ} (hp : l.Pairwise (· ≤ ·)) (hn : l.Nodup)
    (s t : Fin l.length) : l.get s < l.get t ↔ s < t := by
  constructor
  · intro h
    by_contra hts
    rw [not_lt] at hts
    rcases eq_or_lt_of_le hts with rfl | hts
    · exact absurd h (lt_irrefl _)
    · exact absurd h (not_lt.mpr (hp.rel_get_of_lt hts))
  · intro h
    have hle : l.get s ≤ l.get t := hp.rel_get_of_lt h
    have hne : l.get s ≠ l.get t := fun heq =>
      absurd ((hn.get_inj_iff).mp heq) (ne_of_lt h)
    exact lt_of_le_of_ne hle hne

/-- `getElem!` version of `sorted_get_lt_iff`. -/
lemma sorted_getElem!_lt_iff {l : List ℤ} (hp : l.Pairwise (· ≤ ·)) (hn : l.Nodup)
    {s t : ℕ} (hs : s < l.length) (ht : t < l.length) :
    l[s]! < l[t]! ↔ s < t := by
  have hget : ∀ (i : ℕ) (hi : i < l.length), l[i]! = l.get ⟨i, hi⟩ := fun i hi => by
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some,
      List.get_eq_getElem]
  rw [hget s hs, hget t ht, sorted_get_lt_iff hp hn ⟨s, hs⟩ ⟨t, ht⟩]
  exact Fin.mk_lt_mk

/-- In a sorted list of distinct integers, the elements at positions `< k` are exactly
those `≤ c`, where `k` is the number of elements `≤ c`. -/
lemma sorted_getElem!_le_iff {l : List ℤ} (hp : l.Pairwise (· ≤ ·)) (hn : l.Nodup)
    (c : ℤ) {t : ℕ} (ht : t < l.length) :
    l[t]! ≤ c ↔ t < (l.filter (· ≤ c)).length := by
  have hget : ∀ (i : ℕ) (hi : i < l.length), l[i]! = l.get ⟨i, hi⟩ := fun i hi => by
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some,
      List.get_eq_getElem]
  have hB1 : l.filter (· ≤ c) = l.take (l.filter (· ≤ c)).length :=
    sorted_filter_eq_take l c hp
  have hklen : (l.filter (· ≤ c)).length ≤ l.length := List.length_filter_le _ _
  constructor
  · intro h
    by_contra htk
    rw [not_lt] at htk
    have hmem1 : l[t]! ∈ l.filter (· ≤ c) := by
      rw [List.mem_filter]
      constructor
      · rw [hget t ht]
        exact List.getElem_mem ht
      · exact decide_eq_true h
    rw [hB1, List.mem_take_iff_getElem] at hmem1
    obtain ⟨j, hj, hjt⟩ := hmem1
    have hjl : j < l.length := by lia
    rw [hget t ht] at hjt
    have heq : l.get ⟨j, hjl⟩ = l.get ⟨t, ht⟩ := hjt
    have hFinEq : (⟨j, hjl⟩ : Fin l.length) = ⟨t, ht⟩ := (hn.get_inj_iff).mp heq
    have hjet : j = t := congrArg Fin.val hFinEq
    lia
  · intro htk
    have hmem1 : l[t]! ∈ l.take (l.filter (· ≤ c)).length := by
      rw [List.mem_take_iff_getElem]
      exact ⟨t, by lia, (hget t ht).symm⟩
    rw [← hB1, List.mem_filter] at hmem1
    exact of_decide_eq_true hmem1.2

/-- A sum over the image finset reindexed as a list sum over the sorted distinct values. -/
lemma sum_image_eq_sort_map_sum {n : ℕ} {β : Type*} [AddCommMonoid β]
    (m : Fin n → ℤ) (G : ℤ → β) :
    ∑ v ∈ univ.image m, G v = (((univ.image m).sort (· ≤ ·)).map G).sum := by
  have h1 : ((univ.image m).sort (· ≤ ·) : Multiset ℤ) = (univ.image m).val :=
    Finset.sort_eq _ _
  show Multiset.sum ((univ.image m).val.map G) = _
  rw [← h1, Multiset.map_coe, Multiset.sum_coe]

-- ==== main lemmas ====

lemma valMul_eq_sum_eCnt {n : ℕ} (m : Fin n → ℤ) :
    valMul m = ∑ v ∈ univ.image m, eCnt m v • {v} := by
  have hmem : ∀ w : ℤ, w ∈ valMul m ↔ w ∈ univ.image m := by
    intro w
    simp [valMul, Finset.mem_image]
  refine Multiset.ext.mpr fun w => ?_
  rw [Multiset.count_sum']
  have hcnt : ∀ v : ℤ, Multiset.count w (eCnt m v • {v}) = if w = v then eCnt m v else 0 := by
    intro v
    rw [Multiset.nsmul_singleton, Multiset.count_replicate]
    by_cases h : v = w
    · subst h
      simp
    · simp [h, Ne.symm h]
  rw [show (∑ v ∈ univ.image m, Multiset.count w (eCnt m v • {v})) =
      ∑ v ∈ univ.image m, (if w = v then eCnt m v else 0) from
    Finset.sum_congr rfl fun v _ => hcnt v]
  rw [Finset.sum_ite_eq]
  by_cases hw : w ∈ univ.image m
  · rw [ite_eq_left hw]
    rfl
  · rw [ite_eq_right hw]
    exact Multiset.count_eq_zero_of_notMem (mt (hmem w).mp hw)

lemma cntP_eq_sum_eCnt {n : ℕ} (m : Fin n → ℤ) (q : ℤ → Prop) [DecidablePred q] :
    cntP m q = ∑ v ∈ univ.image m, if q v then eCnt m v else 0 := by
  unfold cntP
  rw [Multiset.countP_eq_card_filter, valMul_eq_sum_eCnt, multiset_card_filter_finset_sum]
  apply Finset.sum_congr rfl
  intro v _
  rw [Multiset.nsmul_singleton, multiset_filter_replicate]
  by_cases hv : q v
  · simp only [ite_eq_left hv, Multiset.card_replicate]
  · simp only [ite_eq_right hv, Multiset.card_zero]

/-- The pure polynomial identity in value form: the key combinatorial input behind both
the ratio identity and the main induction. Proven by writing the value multiset as a
sorted list of distinct values `vs` with multiplicity list `es` and split point
`k = #(values ≤ c)`, evaluating the counts via `cntP_eq_sum_eCnt`, and telescoping with
`pureId`. -/
lemma pureId_value {n : ℕ} (m : Fin (n + 1) → ℤ) (c : ℤ) :
    ∑ v ∈ univ.image m, X ^ gc m c v * qq (eCnt m v) = qq (n + 1) := by
  set vs := (univ.image m).sort (· ≤ ·) with hvs
  set es := vs.map (eCnt m) with hes
  set k := (vs.filter (· ≤ c)).length with hk
  have hp : vs.Pairwise (· ≤ ·) := Finset.pairwise_sort _ _
  have hn : vs.Nodup := Finset.sort_nodup _ _
  have hvsval : (vs : Multiset ℤ) = (univ.image m).val := Finset.sort_eq _ _
  have hlen : es.length = vs.length := by simp [hes]
  have hkvs : k ≤ vs.length := List.length_filter_le _ _
  have hkes : k ≤ es.length := by lia
  have hesget : ∀ t : ℕ, t < vs.length → es[t]! = eCnt m (vs[t]!) := by
    intro t ht
    have ht' : t < es.length := by lia
    have g1 : es[t]! = es[t]'ht' := by
      rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem ht', Option.getD_some]
    have g2 : vs[t]! = vs[t]'ht := by
      rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem ht, Option.getD_some]
    rw [g1, g2]
    show (vs.map (eCnt m))[t]'ht' = eCnt m (vs[t]'ht)
    simp only [List.getElem_map]
  have hesum : es.sum = n + 1 := by
    have h1 : es.sum = ∑ v ∈ univ.image m, eCnt m v := by
      rw [hes, ← Multiset.sum_coe, ← Multiset.map_coe, hvsval]
      rfl
    have h2 : ∑ v ∈ univ.image m, eCnt m v = (valMul m).card :=
      Multiset.toFinset_sum_count_eq (valMul m)
    have h3 : (valMul m).card = n + 1 := by
      unfold valMul
      rw [Multiset.card_map, ← Finset.card_def, Finset.card_univ, Fintype.card_fin]
    lia
  have hE1 : ∀ t : ℕ, t < vs.length → cntP m (· < vs[t]!) = (es.take t).sum := by
    intro t ht
    rw [cntP_eq_sum_eCnt, sum_image_eq_sort_map_sum, ← hvs, list_map_sum_eq_sum_range]
    show ∑ s ∈ range vs.length, (if vs[s]! < vs[t]! then eCnt m (vs[s]!) else 0) =
      (es.take t).sum
    rw [← Finset.sum_filter]
    have hset : (range vs.length).filter (fun s => vs[s]! < vs[t]!) = range t := by
      ext s
      simp only [Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨hs, hst⟩
        exact (sorted_getElem!_lt_iff hp hn hs ht).mp hst
      · intro hst
        have hs : s < vs.length := by lia
        exact ⟨hs, (sorted_getElem!_lt_iff hp hn hs ht).mpr hst⟩
    rw [hset, list_sum_take_eq_sum_range es (by lia)]
    apply Finset.sum_congr rfl
    intro s hs
    rw [Finset.mem_range] at hs
    rw [hesget s (by lia)]
  have hE2 : cntP m (c < ·) = es.sum - (es.take k).sum := by
    rw [cntP_eq_sum_eCnt, sum_image_eq_sort_map_sum, ← hvs, list_map_sum_eq_sum_range]
    show ∑ s ∈ range vs.length, (if c < vs[s]! then eCnt m (vs[s]!) else 0) =
      es.sum - (es.take k).sum
    rw [← Finset.sum_filter]
    have hset : (range vs.length).filter (fun s => c < vs[s]!) = Ico k vs.length := by
      ext s
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      constructor
      · rintro ⟨hs, hcs⟩
        have hb3 : vs[s]! ≤ c ↔ s < k := sorted_getElem!_le_iff hp hn c hs
        constructor
        · by_contra hsk
          rw [not_le] at hsk
          exact absurd hcs (not_lt.mpr (hb3.mpr hsk))
        · exact hs
      · rintro ⟨hks, hs⟩
        refine ⟨hs, ?_⟩
        have hb3 : vs[s]! ≤ c ↔ s < k := sorted_getElem!_le_iff hp hn c hs
        by_contra hcs
        rw [not_lt] at hcs
        rw [hb3] at hcs
        lia
    rw [hset]
    have h1 : es.sum = ∑ t ∈ range es.length, es[t]! := list_sum_eq_sum_range es
    have h2 : ∑ t ∈ range k, es[t]! = (es.take k).sum :=
      (list_sum_take_eq_sum_range es hkes).symm
    rw [← Finset.sum_range_add_sum_Ico (fun t => es[t]!) hkes, hlen, h2] at h1
    have h3 : ∑ t ∈ Ico k vs.length, eCnt m (vs[t]!) = ∑ t ∈ Ico k vs.length, es[t]! := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [hesget t (Finset.mem_Ico.mp ht).2]
    lia
  have hE3 : ∀ t : ℕ, k ≤ t → t < vs.length →
      cntP m (fun y => c < y ∧ y < vs[t]!) = (es.take t).sum - (es.take k).sum := by
    intro t hkt ht
    rw [cntP_eq_sum_eCnt, sum_image_eq_sort_map_sum, ← hvs, list_map_sum_eq_sum_range]
    show ∑ s ∈ range vs.length, (if c < vs[s]! ∧ vs[s]! < vs[t]! then eCnt m (vs[s]!) else 0) =
      (es.take t).sum - (es.take k).sum
    rw [← Finset.sum_filter]
    have hset : (range vs.length).filter (fun s => c < vs[s]! ∧ vs[s]! < vs[t]!) =
        Ico k t := by
      ext s
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      constructor
      · rintro ⟨hs, hcs, hst⟩
        have hb3 : vs[s]! ≤ c ↔ s < k := sorted_getElem!_le_iff hp hn c hs
        have hks : k ≤ s := by
          by_contra hsk
          rw [not_le] at hsk
          exact absurd hcs (not_lt.mpr (hb3.mpr hsk))
        exact ⟨hks, (sorted_getElem!_lt_iff hp hn hs ht).mp hst⟩
      · rintro ⟨hks, hst⟩
        have hs : s < vs.length := by lia
        have hb3 : vs[s]! ≤ c ↔ s < k := sorted_getElem!_le_iff hp hn c hs
        have hcs : c < vs[s]! := by
          by_contra h
          rw [not_lt] at h
          rw [hb3] at h
          lia
        exact ⟨hs, hcs, (sorted_getElem!_lt_iff hp hn hs ht).mpr hst⟩
    rw [hset]
    have h1 : (es.take t).sum = ∑ s ∈ range t, es[s]! :=
      list_sum_take_eq_sum_range es (by lia)
    have h2 : ∑ s ∈ range k, es[s]! = (es.take k).sum :=
      (list_sum_take_eq_sum_range es hkes).symm
    rw [← Finset.sum_range_add_sum_Ico (fun s => es[s]!) hkt, h2] at h1
    have h3 : ∑ s ∈ Ico k t, eCnt m (vs[s]!) = ∑ s ∈ Ico k t, es[s]! := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [Finset.mem_Ico] at hs
      rw [hesget s (by lia)]
    lia
  have hreindex : ∑ v ∈ univ.image m, X ^ gc m c v * qq (eCnt m v) =
      ∑ t ∈ range vs.length, X ^ gc m c (vs[t]!) * qq es[t]! := by
    rw [sum_image_eq_sort_map_sum, ← hvs, list_map_sum_eq_sum_range]
    apply Finset.sum_congr rfl
    intro t ht
    rw [Finset.mem_range] at ht
    show X ^ gc m c (vs[t]!) * qq (eCnt m (vs[t]!)) = X ^ gc m c (vs[t]!) * qq es[t]!
    rw [hesget t ht]
  have hA : ∑ t ∈ range k, X ^ gc m c (vs[t]!) * qq es[t]! =
      X ^ (es.sum - (es.take k).sum) * ∑ t ∈ range k, X ^ (es.take t).sum * qq es[t]! := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t ht
    rw [Finset.mem_range] at ht
    have htl : t < vs.length := by lia
    have hle : vs[t]! ≤ c := (sorted_getElem!_le_iff hp hn c htl).mpr ht
    have hgc : gc m c (vs[t]!) = cntP m (· < vs[t]!) + cntP m (c < ·) := by
      unfold gc
      rw [ite_eq_left hle]
    rw [hgc, hE1 t htl, hE2, pow_add]
    ring
  have hB : ∑ t ∈ Ico k vs.length, X ^ gc m c (vs[t]!) * qq es[t]! =
      ∑ t ∈ Ico k es.length, X ^ ((es.take t).sum - (es.take k).sum) * qq es[t]! := by
    rw [← hlen]
    apply Finset.sum_congr rfl
    intro t ht
    rw [Finset.mem_Ico] at ht
    have htl : t < vs.length := by lia
    have hle : ¬ vs[t]! ≤ c := by
      have hb3 : vs[t]! ≤ c ↔ t < k := sorted_getElem!_le_iff hp hn c htl
      intro h
      rw [hb3] at h
      lia
    have hgc : gc m c (vs[t]!) = cntP m (fun y => c < y ∧ y < vs[t]!) := by
      unfold gc
      rw [ite_eq_right hle]
    rw [hgc, hE3 t ht.1 htl]
  rw [hreindex]
  rw [← Finset.sum_range_add_sum_Ico (fun t => X ^ gc m c (vs[t]!) * qq es[t]!) hkvs]
  rw [hA, hB, pureId es k hkes, hesum]

/-- Grouping a sum over positions by the value of the entry. -/
lemma sum_eq_sum_image_card {n : ℕ} (m : Fin (n + 1) → ℤ) (H : Fin (n + 1) → ℤ[X])
    (K : ℤ → ℤ[X]) (hHK : ∀ q, H q = K (m q)) :
    ∑ q, H q = ∑ v ∈ univ.image m, (eCnt m v : ℤ[X]) * K v := by
  have key : ∑ q, K (m q) = ∑ v ∈ univ.image m, ∑ q ∈ univ.filter (fun q => m q = v), K (m q) :=
    Eq.symm (sum_image' (fun i => K (m i)) fun i => congrFun rfl)
  rw [Finset.sum_congr rfl (fun q _ => hHK q), key]
  apply Finset.sum_congr rfl; intro v _
  rw [Finset.sum_congr rfl (fun q hq => by rw [(Finset.mem_filter.mp hq).2])]
  rw [Finset.sum_const, ← eCnt_eq_card_filter, nsmul_eq_mul]

lemma genFun_zero (m : Fin 0 → ℤ) (A : Fin 0 → ℤ) : genFun m A = 1 := by
  unfold genFun
  have h0 : ∀ σ : Perm (Fin 0), ainvCount m A σ = 0 := by
    intro σ; unfold ainvCount
    exact Finset.sum_eq_zero fun i _ => i.elim0
  rw [Finset.sum_congr rfl (fun σ _ => by rw [h0 σ, pow_zero])]
  simp

lemma genFun_one (m : Fin 1 → ℤ) (A : Fin 1 → ℤ) : genFun m A = 1 := by
  unfold genFun
  have h0 : ∀ σ : Perm (Fin 1), ainvCount m A σ = 0 := by
    intro σ; unfold ainvCount
    apply Finset.sum_eq_zero; intro i _
    apply Finset.sum_eq_zero; intro j _
    have hij : i = j := Subsingleton.elim i j
    exact ite_eq_right (fun hh => lt_irrefl _ (hij ▸ hh.1))
  rw [Finset.sum_congr rfl (fun σ _ => by rw [h0 σ, pow_zero])]
  simp

/-- The image of `skipEmb p` is everything except `p`. -/
lemma image_skipEmb {n : ℕ} (p : Fin (n + 1)) : univ.image (skipEmb p) = univ.erase p := by
  ext x
  constructor
  · intro h
    obtain ⟨i, -, rfl⟩ := mem_image.mp h
    exact mem_erase.mpr ⟨skipEmb_ne p i, mem_univ _⟩
  · intro h
    obtain ⟨hxp, -⟩ := mem_erase.mp h
    have h1 : Equiv.swap 0 p x ≠ 0 := by
      intro hh
      exact hxp ((Equiv.swap 0 p).injective (hh.trans (Equiv.swap_apply_right 0 p).symm))
    obtain ⟨i, hi⟩ := Fin.eq_succ_of_ne_zero h1
    refine mem_image.mpr ⟨i, mem_univ _, ?_⟩
    show Equiv.swap 0 p i.succ = x
    rw [← hi]; exact swap_apply_self 0 p x

lemma exists_skipEmb_eq {n : ℕ} {p q : Fin (n + 1)} (h : p ≠ q) :
    ∃ i : Fin n, skipEmb q i = p := by
  have hp : p ∈ univ.image (skipEmb q) := by
    rw [image_skipEmb]
    exact mem_erase.mpr ⟨h, mem_univ _⟩
  obtain ⟨i, -, hi⟩ := mem_image.mp hp
  exact ⟨i, hi⟩

/-- A chosen representative index for a value. -/
noncomputable def repr {n : ℕ} (m : Fin (n + 1) → ℤ) (v : ℤ) : Fin (n + 1) :=
  if h : ∃ i, m i = v then Classical.choose h else 0

lemma repr_spec {n : ℕ} (m : Fin (n + 1) → ℤ) {v : ℤ} (h : ∃ i, m i = v) :
    m (repr m v) = v := by
  unfold repr
  rw [dite_eq_left h]
  exact Classical.choose_spec h

/-- Deleting an index whose value `w` does not match does not change the count of `w`. -/
lemma eCnt_comp_skipEmb_of_ne {n : ℕ} (m : Fin (n + 1) → ℤ) (q : Fin (n + 1)) {w : ℤ}
    (h : m q ≠ w) : eCnt (m ∘ skipEmb q) w = eCnt m w := by
  have h2 := sum_univ_add_skipEmb q (fun i => if m i = w then (1 : ℕ) else 0)
  rw [sum_if_eq_count m w] at h2
  have hcomp : (∑ i : Fin n, if m ((skipEmb q) i) = w then (1 : ℕ) else 0) =
      ∑ i : Fin n, if (m ∘ skipEmb q) i = w then (1 : ℕ) else 0 := rfl
  rw [hcomp, sum_if_eq_count] at h2
  rw [ite_eq_right h, zero_add] at h2
  exact h2.symm

/-- Deleting two different indices with the same value gives the same generating
function. -/
lemma genFun_skipEmb_congr {n : ℕ} (m : Fin (n + 1) → ℤ) {q r : Fin (n + 1)}
    (h : m q = m r) (A : Fin n → ℤ) :
    genFun (m ∘ skipEmb q) A = genFun (m ∘ skipEmb r) A := by
  apply genFun_eq_of_valMul_eq
  rw [valMul_comp_skipEmb, valMul_comp_skipEmb, h]

/-- The ratio identity, by induction on `n`.

Proof plan (algebra verified on paper): induction on `n`.
* Base `n = 0`: `m : Fin 1 → ℤ`; `eCnt m (m p) = 1` (via `eCnt_eq_card_filter`, filter is
  everything by `Subsingleton`), `genFun_one`, `genFun_zero`, `qq 1 = 1`.
* Step: `m : Fin (n+2) → ℤ`, `θ := m p`, `e := eCnt m θ`. Expand `genFun m 0` by
  `genFun_rec` (with `A = 0`; note `(0 : Fin _ → ℤ) 0 = 0` and `0 ∘ Fin.succ = 0`),
  rewrite each `frontContrib 0 (m q) (m ∘ skipEmb q)` as `gc m 0 (m q)`
  (`frontContrib_eval` + `gc` def), then group by value with `sum_eq_sum_image_card`
  using `K v := X ^ gc m 0 v * genFun (m ∘ skipEmb (repr v)) 0` where `repr v` is a
  chosen index with value `v` (`Classical.choose`; the `genFun` term is independent of
  the choice by `genFun_eq_of_valMul_eq` + `valMul_comp_skipEmb`).
  Multiply by `qq e`, split off the `v = θ` term (`Finset.add_sum_erase`), and for
  `v ≠ θ` apply the IH twice (once to `m ∘ skipEmb (repr v)` at the index mapping to `p`
  — exists because `univ.image (skipEmb q) = univ.erase q`, cf. the proof of
  `sum_univ_add_skipEmb`; once to `m ∘ skipEmb p` at the index mapping to `repr v`), using
  `eCnt (m ∘ skipEmb q) w = eCnt m w` when `m q ≠ w` (prove via `sum_univ_add_skipEmb` +
  `sum_if_eq_count`) and `Multiset.erase_comm` + `genFun_eq_of_valMul_eq` to identify the
  double deletions. Everything becomes `e * genFun (m ∘ skipEmb p) 0` times
  `∑ v, X ^ gc m 0 v * qq (eCnt m v) = qq (n+2)` (`pureId_value`). -/
lemma QL {n : ℕ} : ∀ (m : Fin (n + 1) → ℤ) (p : Fin (n + 1)),
    qq (eCnt m (m p)) * genFun m 0 =
      qq (n + 1) * (eCnt m (m p) : ℤ[X]) * genFun (m ∘ skipEmb p) 0 := by
  induction n with
  | zero =>
    intro m p
    have h1 : ∀ i : Fin 1, i = 0 := fun i => by
      have hlt := i.is_lt
      ext
      simp only [Fin.val_zero]
      lia
    have hp : p = 0 := h1 p
    subst hp
    have he : eCnt m (m 0) = 1 := by
      rw [eCnt_eq_card_filter]
      have huf : univ.filter (fun i : Fin 1 => m i = m 0) = univ :=
        Finset.filter_true_of_mem fun i _ => congr_arg m (h1 i)
      rw [huf]
      simp
    simp [he, genFun_one, genFun_zero, qq]
  | succ n ih =>
    intro m p
    set e := eCnt m (m p) with he
    have hθ : m p ∈ univ.image m := mem_image.mpr ⟨p, mem_univ p, rfl⟩
    -- expansion of `genFun m 0` by the first-position recurrence, grouped by value
    have hrec : genFun m 0 = ∑ v ∈ univ.image m, (eCnt m v : ℤ[X]) *
        (X ^ gc m 0 v * genFun (m ∘ skipEmb (repr m v)) 0) := by
      have h1 := genFun_rec m (0 : Fin (n + 2) → ℤ)
      have hker : ∀ q : Fin (n + 2),
          X ^ frontContrib ((0 : Fin (n + 2) → ℤ) 0) (m q) (m ∘ skipEmb q) *
            genFun (m ∘ skipEmb q) ((0 : Fin (n + 2) → ℤ) ∘ Fin.succ) =
          X ^ gc m 0 (m q) * genFun (m ∘ skipEmb (repr m (m q))) 0 := by
        intro q
        have hfc : frontContrib ((0 : Fin (n + 2) → ℤ) 0) (m q) (m ∘ skipEmb q) =
            gc m 0 (m q) := frontContrib_eval m _ q
        have hzero : ((0 : Fin (n + 2) → ℤ) ∘ Fin.succ) = (0 : Fin (n + 1) → ℤ) := rfl
        rw [hfc, hzero]
        congr 1
        exact (genFun_skipEmb_congr m (repr_spec m ⟨q, rfl⟩) 0).symm
      rw [h1]
      exact sum_eq_sum_image_card m
        (fun q => X ^ frontContrib ((0 : Fin (n + 2) → ℤ) 0) (m q) (m ∘ skipEmb q) *
          genFun (m ∘ skipEmb q) ((0 : Fin (n + 2) → ℤ) ∘ Fin.succ))
        (fun v => X ^ gc m 0 v * genFun (m ∘ skipEmb (repr m v)) 0) hker
    have hGθ : genFun (m ∘ skipEmb (repr m (m p))) 0 = genFun (m ∘ skipEmb p) 0 :=
      genFun_skipEmb_congr m (repr_spec m ⟨p, rfl⟩) 0
    -- split off the term of the value `m p`
    have hsplit : ∑ v ∈ univ.image m, (eCnt m v : ℤ[X]) *
          (X ^ gc m 0 v * genFun (m ∘ skipEmb (repr m v)) 0) =
        (e : ℤ[X]) * (X ^ gc m 0 (m p) * genFun (m ∘ skipEmb (repr m (m p))) 0) +
        ∑ v ∈ (univ.image m).erase (m p), (eCnt m v : ℤ[X]) *
          (X ^ gc m 0 v * genFun (m ∘ skipEmb (repr m v)) 0) := by
      rw [← Finset.add_sum_erase (univ.image m)
        (fun v => (eCnt m v : ℤ[X]) * (X ^ gc m 0 v * genFun (m ∘ skipEmb (repr m v)) 0)) hθ]
    -- the heart: each remaining summand, multiplied by `qq e`, collapses
    have hvFacts : ∀ v ∈ (univ.image m).erase (m p),
        qq e * ((eCnt m v : ℤ[X]) * (X ^ gc m 0 v * genFun (m ∘ skipEmb (repr m v)) 0)) =
        (e : ℤ[X]) * genFun (m ∘ skipEmb p) 0 * (X ^ gc m 0 v * qq (eCnt m v)) := by
      intro v hv
      have hvne : v ≠ m p := (mem_erase.mp hv).1
      have hvimg : ∃ i, m i = v := by
        have hvm : v ∈ univ.image m := mem_of_mem_erase hv
        obtain ⟨i, -, hi⟩ := mem_image.mp hvm
        exact ⟨i, hi⟩
      have hrv : m (repr m v) = v := repr_spec m hvimg
      have hnp : repr m v ≠ p := fun h => hvne (hrv.symm.trans (congr_arg m h))
      obtain ⟨p', hp'⟩ := exists_skipEmb_eq (Ne.symm hnp)
      obtain ⟨v', hv'⟩ := exists_skipEmb_eq hnp
      have hval1 : (m ∘ skipEmb (repr m v)) p' = m p := by
        show m ((skipEmb (repr m v)) p') = m p
        rw [hp']
      have hval2 : (m ∘ skipEmb p) v' = v := by
        show m ((skipEmb p) v') = v
        rw [hv', hrv]
      have hIH1 := ih (m ∘ skipEmb (repr m v)) p'
      rw [hval1, eCnt_comp_skipEmb_of_ne m (repr m v) (fun h => hvne (hrv.symm.trans h)), ← he] at hIH1
      have hIH2 := ih (m ∘ skipEmb p) v'
      rw [hval2, eCnt_comp_skipEmb_of_ne m p (Ne.symm hvne)] at hIH2
      have hdd : genFun ((m ∘ skipEmb p) ∘ skipEmb v') (0 : Fin n → ℤ) =
          genFun ((m ∘ skipEmb (repr m v)) ∘ skipEmb p') 0 := by
        apply genFun_eq_of_valMul_eq
        rw [valMul_comp_skipEmb, valMul_comp_skipEmb, hval2, valMul_comp_skipEmb,
          valMul_comp_skipEmb, hval1, hrv, Multiset.erase_comm]
      rw [hdd] at hIH2
      calc qq e * ((eCnt m v : ℤ[X]) * (X ^ gc m 0 v * genFun (m ∘ skipEmb (repr m v)) 0))
          = X ^ gc m 0 v * (eCnt m v : ℤ[X]) *
              (qq e * genFun (m ∘ skipEmb (repr m v)) 0) := by ring
        _ = X ^ gc m 0 v * (eCnt m v : ℤ[X]) *
              (qq (n + 1) * (e : ℤ[X]) *
                genFun ((m ∘ skipEmb (repr m v)) ∘ skipEmb p') 0) := by rw [hIH1]
        _ = X ^ gc m 0 v * (e : ℤ[X]) *
              (qq (n + 1) * (eCnt m v : ℤ[X]) *
                genFun ((m ∘ skipEmb (repr m v)) ∘ skipEmb p') 0) := by ring
        _ = X ^ gc m 0 v * (e : ℤ[X]) * (qq (eCnt m v) * genFun (m ∘ skipEmb p) 0) := by
            rw [← hIH2]
        _ = (e : ℤ[X]) * genFun (m ∘ skipEmb p) 0 * (X ^ gc m 0 v * qq (eCnt m v)) := by ring
    -- assemble
    calc qq e * genFun m 0
        = qq e * ((e : ℤ[X]) * (X ^ gc m 0 (m p) * genFun (m ∘ skipEmb (repr m (m p))) 0) +
            ∑ v ∈ (univ.image m).erase (m p), (eCnt m v : ℤ[X]) *
              (X ^ gc m 0 v * genFun (m ∘ skipEmb (repr m v)) 0)) := by rw [hrec, hsplit]
      _ = (e : ℤ[X]) * genFun (m ∘ skipEmb p) 0 * (X ^ gc m 0 (m p) * qq e) +
            ∑ v ∈ (univ.image m).erase (m p), (e : ℤ[X]) * genFun (m ∘ skipEmb p) 0 *
              (X ^ gc m 0 v * qq (eCnt m v)) := by
          rw [mul_add, Finset.mul_sum]
          have h1 : qq e * ((e : ℤ[X]) *
                (X ^ gc m 0 (m p) * genFun (m ∘ skipEmb (repr m (m p))) 0)) =
              (e : ℤ[X]) * genFun (m ∘ skipEmb p) 0 * (X ^ gc m 0 (m p) * qq e) := by
            rw [hGθ]; ring
          rw [h1, Finset.sum_congr rfl hvFacts]
      _ = (e : ℤ[X]) * genFun (m ∘ skipEmb p) 0 *
            ((X ^ gc m 0 (m p) * qq e) +
              ∑ v ∈ (univ.image m).erase (m p), (X ^ gc m 0 v * qq (eCnt m v))) := by
          rw [mul_add, Finset.mul_sum]
      _ = (e : ℤ[X]) * genFun (m ∘ skipEmb p) 0 *
            (∑ v ∈ univ.image m, X ^ gc m 0 v * qq (eCnt m v)) := by
          rw [← Finset.add_sum_erase (univ.image m) (fun v => X ^ gc m 0 v * qq (eCnt m v)) hθ]
      _ = (e : ℤ[X]) * genFun (m ∘ skipEmb p) 0 * qq (n + 1 + 1) := by
          rw [pureId_value m 0]
      _ = qq (n + 1 + 1) * ((e : ℤ[X]) * genFun (m ∘ skipEmb p) 0) := mul_comm _ _
      _ = qq (n + 1 + 1) * (e : ℤ[X]) * genFun (m ∘ skipEmb p) 0 := by rw [mul_assoc]

/-- The main induction: the `A`-inversion generating function does not depend on `A`.

Proof plan: induction on `n`. Base `n = 0`: both sides `1` (`genFun_zero`).
Step `n+1`: expand `genFun m A` by `genFun_rec` + `frontContrib_eval` (as `gc m (A 0)`),
rewrite each `genFun (m ∘ skipEmb p) (A ∘ Fin.succ)` to `genFun (m ∘ skipEmb p) 0` by IH,
group by value (`sum_eq_sum_image_card` with the `repr`-kernel as in `QL`), then:
multiply by `qq (n+1)`; use `QL` at each representative to rewrite
`qq (n+1) * eCnt m v * genFun (m ∘ skipEmb (repr v)) 0 = qq (eCnt m v) * genFun m 0`;
the sum becomes `genFun m 0 * ∑ v, X ^ gc m (A 0) v * qq (eCnt m v) = genFun m 0 * qq (n+1)`
by `pureId_value`; cancel `qq (n+1) ≠ 0` (`mul_left_cancel₀`; `qq (n+1) ≠ 0` since its
constant coefficient is `1`). -/
lemma PL {n : ℕ} : ∀ (m : Fin n → ℤ) (A : Fin n → ℤ), genFun m A = genFun m 0 := by
  induction n with
  | zero => intro m A; rw [genFun_zero m A, genFun_zero m 0]
  | succ n ih =>
    intro m A
    have hrec : genFun m A = ∑ v ∈ univ.image m, (eCnt m v : ℤ[X]) *
        (X ^ gc m (A 0) v * genFun (m ∘ skipEmb (repr m v)) 0) := by
      have h1 := genFun_rec m A
      have hker : ∀ q : Fin (n + 1),
          X ^ frontContrib (A 0) (m q) (m ∘ skipEmb q) *
            genFun (m ∘ skipEmb q) (A ∘ Fin.succ) =
          X ^ gc m (A 0) (m q) * genFun (m ∘ skipEmb (repr m (m q))) 0 := by
        intro q
        have hfc : frontContrib (A 0) (m q) (m ∘ skipEmb q) = gc m (A 0) (m q) :=
          frontContrib_eval m _ q
        rw [hfc, ih (m ∘ skipEmb q) (A ∘ Fin.succ)]
        congr 1
        exact (genFun_skipEmb_congr m (repr_spec m ⟨q, rfl⟩) 0).symm
      rw [h1]
      exact sum_eq_sum_image_card m
        (fun q => X ^ frontContrib (A 0) (m q) (m ∘ skipEmb q) *
          genFun (m ∘ skipEmb q) (A ∘ Fin.succ))
        (fun v => X ^ gc m (A 0) v * genFun (m ∘ skipEmb (repr m v)) 0) hker
    have hqq : qq (n + 1) ≠ 0 := by
      have hcoeff : (qq (n + 1)).coeff 0 = 1 := by
        unfold qq
        have h1 : ∀ s : Finset ℕ, (∑ x ∈ s, X ^ x).coeff 0 = ∑ x ∈ s, (X ^ x).coeff 0 :=
          fun s => map_sum (Polynomial.lcoeff ℤ 0) _ s
        rw [h1]
        simp only [Polynomial.coeff_X_pow]
        rw [Finset.sum_ite_eq]
        simp
      intro h
      rw [h] at hcoeff
      simp at hcoeff
    apply mul_left_cancel₀ hqq
    calc qq (n + 1) * genFun m A
        = qq (n + 1) * ∑ v ∈ univ.image m, (eCnt m v : ℤ[X]) *
            (X ^ gc m (A 0) v * genFun (m ∘ skipEmb (repr m v)) 0) := by rw [hrec]
      _ = ∑ v ∈ univ.image m, X ^ gc m (A 0) v *
            (qq (n + 1) * (eCnt m v : ℤ[X]) * genFun (m ∘ skipEmb (repr m v)) 0) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro v _
          ring
      _ = ∑ v ∈ univ.image m, X ^ gc m (A 0) v * (qq (eCnt m v) * genFun m 0) := by
          apply Finset.sum_congr rfl; intro v hv
          have hvimg : ∃ i, m i = v := by
            obtain ⟨i, -, hi⟩ := mem_image.mp hv
            exact ⟨i, hi⟩
          have hQL := QL m (repr m v)
          rw [repr_spec m hvimg] at hQL
          rw [← hQL]
      _ = genFun m 0 * ∑ v ∈ univ.image m, X ^ gc m (A 0) v * qq (eCnt m v) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro v _
          ring
      _ = genFun m 0 * qq (n + 1) := by rw [pureId_value m (A 0)]
      _ = qq (n + 1) * genFun m 0 := by ring

/-- The coefficient of `X^k` in the generating function counts permutations with
exactly `k` `A`-inversions. -/
lemma coeff_genFun {n : ℕ} (m : Fin n → ℤ) (A : Fin n → ℤ) (k : ℕ) :
    (genFun m A).coeff k =
      ((univ.filter (fun σ : Perm (Fin n) => ainvCount m A σ = k)).card : ℤ) := by
  unfold genFun
  have hsum : ∀ s : Finset (Perm (Fin n)),
      (∑ σ ∈ s, X ^ ainvCount m A σ).coeff k = ∑ σ ∈ s, (X ^ ainvCount m A σ).coeff k :=
    fun s => map_sum (Polynomial.lcoeff ℤ k) _ s
  rw [hsum]
  simp_rw [Polynomial.coeff_X_pow]
  rw [Finset.sum_boole]
  have : univ.filter (fun σ : Perm (Fin n) => k = ainvCount m A σ) =
      univ.filter (fun σ : Perm (Fin n) => ainvCount m A σ = k) :=
    Finset.filter_congr fun i _ => eq_comm
  rw [this]

snip end

/-- **USA Mathematical Olympiad 2017, Problem 2.** The number of permutations of
`m₁, …, mₙ` with exactly `k` `A`-inversions equals the number with exactly `k`
`B`-inversions. Permutations are counted with multiplicity (as positional permutations
`σ : Equiv.Perm (Fin n)`), which is equivalent to the count over distinct arrangements:
each distinct arrangement corresponds to the same positive number `∏ (multiplicity)!` of
positional permutations, independently of `A`, `B` and `k`. Note: the positivity
hypothesis `hm` is actually not needed for the conclusion. -/
problem usa2017_p2 {n : ℕ} (m : Fin n → ℕ) (_hm : ∀ i, 0 < m i) (A B : Fin n → ℤ) (k : ℕ) :
    (univ.filter (fun σ : Perm (Fin n) => ainvCount (fun i => (m i : ℤ)) A σ = k)).card =
    (univ.filter (fun σ : Perm (Fin n) => ainvCount (fun i => (m i : ℤ)) B σ = k)).card := by
  have hA := PL (fun i => (m i : ℤ)) A
  have hB := PL (fun i => (m i : ℤ)) B
  have cA := coeff_genFun (fun i => (m i : ℤ)) A k
  have cB := coeff_genFun (fun i => (m i : ℤ)) B k
  rw [hA] at cA
  rw [hB] at cB
  exact Int.ofNat_inj.mp (cA.symm.trans cB)

end Usa2017P2
