/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.GCDMonoid.Multiset
public import Mathlib.Algebra.GCDMonoid.Nat
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Prod.Lex
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import ProblemExtraction

@[expose] public section

set_option backward.isDefEq.respectTransparency false

problem_file {
  tags := [.NumberTheory]
  problemImportedFrom :=
    "https://github.com/humanfia/imo2026"
}

/-!
# International Mathematical Olympiad 2026, Problem 1

There are 2026 integers greater than 1 written on a blackboard, not necessarily
different. In a move, Confucius chooses two integers m > 1 and n > 1 from
different places on the blackboard and replaces these two integers with
gcd(m, n) and lcm(m, n) / gcd(m, n). He continues to make moves while it is
possible to do so.

(a) Prove that, regardless of the choices of Confucius, after finitely many
moves, exactly one integer M on the blackboard is greater than 1.

(b) Prove that the value of M does not depend on the choices of Confucius.

(Note that gcd(x, y) denotes the greatest common divisor of positive integers
x and y, and lcm(x, y) denotes the least common multiple of x and y.)

Statement formalization adapted from AxiomMath/IMO2026; proof adapted from
Humanfia's Kimi-K3 solutions (https://github.com/humanfia/imo2026).
-/

namespace Imo2026P1

/-- A *board* is a finite multiset of natural numbers.  The full board discipline
(entries `≥ 1`, cardinality `2026`) is captured by the predicate `IsInitial`. -/
abbrev Board := Multiset ℕ

/-- An *initial board*: exactly `2026` entries, each strictly greater than `1`. -/
def IsInitial (B : Board) : Prop :=
  Multiset.card B = 2026 ∧ ∀ a ∈ B, 1 < a

/-- A single *move*: pick two entries `m, n` (from two distinct positions,
modelled as two separate elements of the multiset) both `> 1`, remove them and
insert `gcd(m, n)` and `lcm(m, n) / gcd(m, n)`.  Using `m ::ₘ n ::ₘ s` for the
source board automatically encodes that the two chosen positions are distinct
(they are two separate multiset elements, whose *values* may coincide). -/
def Move (B B' : Board) : Prop :=
  ∃ (m n : ℕ) (s : Board), 1 < m ∧ 1 < n ∧
    B = m ::ₘ n ::ₘ s ∧
    B' = Nat.gcd m n ::ₘ (Nat.lcm m n / Nat.gcd m n) ::ₘ s

/-- A board is *terminal* when at most one entry is `> 1`, so no move is possible. -/
def IsTerminal (B : Board) : Prop :=
  Multiset.card (B.filter (fun a => 1 < a)) ≤ 1

/-- A board has a *unique large entry* when exactly one entry is `> 1`. -/
def HasUniqueLarge (B : Board) : Prop :=
  Multiset.card (B.filter (fun a => 1 < a)) = 1

/-- `Reachable B B'` : `B'` can be obtained from `B` by a finite sequence of moves
(the reflexive–transitive closure of `Move`).  A finite play from `B` to a
terminal board `B'` is precisely a witness of `Reachable B B'` with `IsTerminal B'`. -/
def Reachable (B B' : Board) : Prop := Relation.ReflTransGen Move B B'

/-- The exponent `g_p` for a prime `p` and board `B`: the `gcd` of the `p`-adic
valuations of the entries of `B`.  Since `gcd(a, 0) = a`, valuations equal to `0`
(entries not divisible by `p`) do not affect this gcd, so `gExp p B` is the gcd of
the *positive* `p`-adic valuations occurring in `B`. -/
noncomputable def gExp (p : ℕ) (B : Board) : ℕ :=
  (B.map (fun a => padicValNat p a)).gcd

/-- The claimed invariant terminal value
`M = ∏_{p ∣ ∏ B} p ^ gExp p B`, the product over all primes dividing some entry
of `B` of `p` raised to the gcd of the `p`-adic valuations. -/
noncomputable def Mval (B : Board) : ℕ :=
  ∏ p ∈ B.prod.primeFactors, p ^ gExp p B

snip begin

/-!
### Proof sketch

Termination (part (a), first half) follows from a lexicographic measure: a move
either lowers the product of the board (when `gcd(m, n) > 1`, since
`gcd(m, n) * (lcm(m, n) / gcd(m, n)) = lcm(m, n) < m * n`), or keeps the product
unchanged (when `gcd(m, n) = 1`) but strictly lowers the number of entries
greater than `1`.  Hence there is no infinite play.

For the rest, the key invariant is `gExp p B`, the `gcd` of the `p`-adic
valuations of the entries: a move replaces `v_p m, v_p n` by
`min (v_p m) (v_p n)` and `max (v_p m) (v_p n) - min (v_p m) (v_p n)`, whose
`gcd` with the remaining valuations is unchanged.  Consequently
`Mval B = ∏_{p ∣ ∏ B} p ^ gExp p B` is invariant along any play.  A move always
produces at least one entry `> 1`, so a reachable terminal board has *exactly*
one entry `M > 1`; on such a board every other entry equals `1`, hence
`gExp p B' = v_p M` for every prime `p` and `M = Mval B' = Mval B₀`, which
proves both the uniqueness in (a) and the invariance in (b), and identifies the
terminal value explicitly.
-/

/-- Moves preserve the property that all entries are `≥ 1`. -/
lemma move_ge_one {B B' : Board} (hmove : Move B B') (hB : ∀ a ∈ B, 1 ≤ a) :
    ∀ a ∈ B', 1 ≤ a := by
  obtain ⟨m, n, s, hm, hn, rfl, rfl⟩ := hmove
  have hm0 : m ≠ 0 := by omega
  have hn0 : n ≠ 0 := by omega
  intro a ha
  rw [Multiset.mem_cons] at ha
  rcases ha with rfl | ha
  · exact Nat.one_le_iff_ne_zero.mpr (fun h => by
      rw [Nat.gcd_eq_zero_iff] at h
      exact hm0 h.1)
  rw [Multiset.mem_cons] at ha
  rcases ha with rfl | ha
  · have hlcm0 : Nat.lcm m n ≠ 0 := fun h => by
      have h2 := Nat.gcd_mul_lcm m n
      rw [h, mul_zero] at h2
      exact (mul_ne_zero hm0 hn0) h2.symm
    have hgl : Nat.gcd m n ≤ Nat.lcm m n :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero hlcm0)
        ((Nat.gcd_dvd_left m n).trans (Nat.dvd_lcm_left m n))
    have hg0 : 0 < Nat.gcd m n := Nat.pos_of_ne_zero (fun h => by
      rw [Nat.gcd_eq_zero_iff] at h
      exact hm0 h.1)
    exact Nat.div_pos hgl hg0
  · exact hB a (Multiset.mem_cons_of_mem (Multiset.mem_cons_of_mem ha))

/-- Reachable boards have all entries `≥ 1`, provided the start board does. -/
lemma ge_one_reachable {B₀ B : Board} (hge : ∀ a ∈ B₀, 1 ≤ a) (hreach : Reachable B₀ B) :
    ∀ a ∈ B, 1 ≤ a := by
  induction hreach with
  | refl => exact hge
  | tail _ hmove ih => exact move_ge_one hmove ih

/-- A move always produces at least one entry `> 1`. -/
lemma large_count_pos_of_move {B B' : Board} (hmove : Move B B') :
    1 ≤ (B'.filter fun a => 1 < a).card := by
  obtain ⟨m, n, s, hm, hn, rfl, rfl⟩ := hmove
  have hm0 : m ≠ 0 := by omega
  have hn0 : n ≠ 0 := by omega
  have card_pos_of_mem {x : ℕ}
      (hx : x ∈ (Nat.gcd m n ::ₘ (Nat.lcm m n / Nat.gcd m n) ::ₘ s).filter (fun a => 1 < a)) :
      1 ≤ ((Nat.gcd m n ::ₘ (Nat.lcm m n / Nat.gcd m n) ::ₘ s).filter fun a => 1 < a).card := by
    have hne : (Nat.gcd m n ::ₘ (Nat.lcm m n / Nat.gcd m n) ::ₘ s).filter (fun a => 1 < a) ≠ 0 :=
      fun h => by
        rw [h] at hx
        exact Multiset.notMem_zero x hx
    exact Nat.one_le_iff_ne_zero.mpr (fun hc => hne (Multiset.card_eq_zero.mp hc))
  by_cases hg : 1 < Nat.gcd m n
  · exact card_pos_of_mem (Multiset.mem_filter.mpr ⟨Multiset.mem_cons_self _ _, hg⟩)
  · have hl : 1 < Nat.lcm m n / Nat.gcd m n := by
      have hg1 : Nat.gcd m n = 1 := by
        have hg0 : 0 < Nat.gcd m n := Nat.pos_of_ne_zero (fun h => by
          rw [Nat.gcd_eq_zero_iff] at h
          exact hm0 h.1)
        omega
      have hlcm : Nat.lcm m n = m * n := by
        have h := Nat.gcd_mul_lcm m n
        rw [hg1, one_mul] at h
        exact h
      rw [hlcm, hg1, Nat.div_one]
      calc 1 < 2 * 2 := by norm_num
        _ ≤ m * n := Nat.mul_le_mul hm hn
    exact card_pos_of_mem (Multiset.mem_filter.mpr
      ⟨Multiset.mem_cons_of_mem (Multiset.mem_cons_self _ _), hl⟩)

/-- Reachable boards have at least one entry `> 1`, provided the start board does. -/
lemma large_count_pos_of_reachable {B₀ B : Board}
    (h : 1 ≤ (B₀.filter fun a => 1 < a).card) (hreach : Reachable B₀ B) :
    1 ≤ (B.filter fun a => 1 < a).card := by
  induction hreach with
  | refl => exact h
  | tail _ hmove _ => exact large_count_pos_of_move hmove

/-- `gcd(min a b, max a b - min a b) = gcd(a, b)`. -/
lemma gcd_min_sub_max (a b : ℕ) : Nat.gcd (min a b) (max a b - min a b) = Nat.gcd a b := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, max_eq_right h, Nat.gcd_comm, Nat.gcd_sub_self_left h, Nat.gcd_comm]
  · rw [min_eq_right h, max_eq_left h, Nat.gcd_comm, Nat.gcd_sub_self_left h]

/-- For a prime `p`, the quantity `gExp p` is preserved by a move. -/
lemma gExp_move {m n : ℕ} (hm : 1 < m) (hn : 1 < n) (s : Board) {p : ℕ} (hp : p.Prime) :
    gExp p (Nat.gcd m n ::ₘ (Nat.lcm m n / Nat.gcd m n) ::ₘ s) =
      gExp p (m ::ₘ n ::ₘ s) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hm0 : m ≠ 0 := by omega
  have hn0 : n ≠ 0 := by omega
  have hg0 : Nat.gcd m n ≠ 0 := fun h => by
    rw [Nat.gcd_eq_zero_iff] at h
    exact hm0 h.1
  have hlcm0 : Nat.lcm m n ≠ 0 := fun h => by
    have h2 := Nat.gcd_mul_lcm m n
    rw [h, mul_zero] at h2
    exact (mul_ne_zero hm0 hn0) h2.symm
  have hl0 : Nat.lcm m n / Nat.gcd m n ≠ 0 := by
    have hgl : Nat.gcd m n ≤ Nat.lcm m n :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero hlcm0)
        ((Nat.gcd_dvd_left m n).trans (Nat.dvd_lcm_left m n))
    have h2 : 0 < Nat.gcd m n := Nat.pos_of_ne_zero hg0
    exact (Nat.div_pos hgl h2).ne'
  have hvg : padicValNat p (Nat.gcd m n) = min (padicValNat p m) (padicValNat p n) := by
    rw [← Nat.factorization_def _ hp, ← Nat.factorization_def _ hp,
      ← Nat.factorization_def _ hp, Nat.factorization_gcd hm0 hn0, Finsupp.inf_apply]
  have hvlcm : padicValNat p (Nat.lcm m n) = max (padicValNat p m) (padicValNat p n) := by
    rw [← Nat.factorization_def _ hp, ← Nat.factorization_def _ hp,
      ← Nat.factorization_def _ hp, Nat.factorization_lcm hm0 hn0, Finsupp.sup_apply]
  have hvdiv : padicValNat p (Nat.lcm m n / Nat.gcd m n) =
      max (padicValNat p m) (padicValNat p n) - min (padicValNat p m) (padicValNat p n) := by
    have hgl : Nat.gcd m n * (Nat.lcm m n / Nat.gcd m n) = Nat.lcm m n :=
      Nat.mul_div_cancel' ((Nat.gcd_dvd_left m n).trans (Nat.dvd_lcm_left m n))
    have h := padicValNat.mul (p := p) hg0 hl0
    rw [hgl, hvlcm, hvg] at h
    omega
  simp only [gExp, Multiset.map_cons, Multiset.gcd_cons]
  rw [hvg, hvdiv]
  change Nat.gcd (min (padicValNat p m) (padicValNat p n))
      (Nat.gcd (max (padicValNat p m) (padicValNat p n) - min (padicValNat p m) (padicValNat p n))
        (Multiset.map (fun a => padicValNat p a) s).gcd) =
    Nat.gcd (padicValNat p m)
      (Nat.gcd (padicValNat p n) (Multiset.map (fun a => padicValNat p a) s).gcd)
  rw [← Nat.gcd_assoc, gcd_min_sub_max, Nat.gcd_assoc]

/-- `Mval` is invariant under a move, for boards whose remaining entries are `≥ 1`. -/
lemma Mval_move {m n : ℕ} (hm : 1 < m) (hn : 1 < n) (s : Board) (hs : ∀ a ∈ s, 1 ≤ a) :
    Mval (Nat.gcd m n ::ₘ (Nat.lcm m n / Nat.gcd m n) ::ₘ s) = Mval (m ::ₘ n ::ₘ s) := by
  have hm0 : m ≠ 0 := by omega
  have hn0 : n ≠ 0 := by omega
  have hP0 : s.prod ≠ 0 := fun h => by
    rw [Multiset.prod_eq_zero_iff] at h
    have := hs 0 h
    omega
  have hlcm0 : Nat.lcm m n ≠ 0 := fun h => by
    have h2 := Nat.gcd_mul_lcm m n
    rw [h, mul_zero] at h2
    exact (mul_ne_zero hm0 hn0) h2.symm
  have hgl : Nat.gcd m n * (Nat.lcm m n / Nat.gcd m n) = Nat.lcm m n :=
    Nat.mul_div_cancel' ((Nat.gcd_dvd_left m n).trans (Nat.dvd_lcm_left m n))
  have hprodL : (Nat.gcd m n ::ₘ (Nat.lcm m n / Nat.gcd m n) ::ₘ s).prod =
      Nat.lcm m n * s.prod := by
    rw [Multiset.prod_cons, Multiset.prod_cons, ← mul_assoc, hgl]
  have hprodR : (m ::ₘ n ::ₘ s).prod = (m * n) * s.prod := by
    rw [Multiset.prod_cons, Multiset.prod_cons, ← mul_assoc]
  have hpf_lcm : (Nat.lcm m n).primeFactors = m.primeFactors ∪ n.primeFactors := by
    have h1 : (Nat.lcm m n).primeFactors = (Nat.lcm m n).factorization.support := rfl
    rw [h1, Nat.factorization_lcm hm0 hn0, Finsupp.support_sup]
    rfl
  have hsets : ((m * n) * s.prod).primeFactors = (Nat.lcm m n * s.prod).primeFactors := by
    rw [Nat.primeFactors_mul (mul_ne_zero hm0 hn0) hP0, Nat.primeFactors_mul hlcm0 hP0,
      Nat.primeFactors_mul hm0 hn0, hpf_lcm]
  unfold Mval
  rw [hprodL, hprodR, hsets]
  apply Finset.prod_congr rfl
  intro p hp
  rw [gExp_move hm hn s (Nat.prime_of_mem_primeFactors hp)]

/-- `Mval` is invariant along any finite play. -/
lemma Mval_reachable {B₀ B : Board} (hge : ∀ a ∈ B₀, 1 ≤ a) (hreach : Reachable B₀ B) :
    Mval B = Mval B₀ := by
  induction hreach with
  | refl => rfl
  | tail hb hmove ih =>
    rename_i Bmid Bend
    obtain ⟨m, n, s, hm, hn, hbm, hbe⟩ := hmove
    have hs : ∀ a ∈ s, 1 ≤ a := by
      intro a ha
      exact ge_one_reachable hge hb a
        (hbm ▸ Multiset.mem_cons_of_mem (Multiset.mem_cons_of_mem ha))
    rw [hbe, Mval_move hm hn s hs, ← hbm]
    exact ih

/-- A board whose entries are all `1` has product `1`. -/
lemma prod_eq_one_of_forall_eq_one (s : Board) (h : ∀ a ∈ s, a = 1) : s.prod = 1 := by
  induction s using Multiset.induction_on with
  | empty => rfl
  | cons a s ih =>
    rw [Multiset.prod_cons, h a (Multiset.mem_cons_self a s),
      ih (fun b hb => h b (Multiset.mem_cons_of_mem hb)), mul_one]

/-- On a terminal board with entries `≥ 1`, `Mval` equals the unique large entry. -/
lemma Mval_terminal {B' : Board} (hge : ∀ a ∈ B', 1 ≤ a) (huniq : HasUniqueLarge B')
    {M : ℕ} (hM : 1 < M) (hMem : M ∈ B') : Mval B' = M := by
  have hfilt : B'.filter (fun a => 1 < a) = {M} := by
    have hMf : M ∈ B'.filter (fun a => 1 < a) := Multiset.mem_filter.mpr ⟨hMem, hM⟩
    obtain ⟨x, hx⟩ := Multiset.card_eq_one.mp huniq
    rw [hx] at hMf
    have hxM : x = M := (Multiset.mem_singleton.mp hMf).symm
    rw [hx, hxM]
  have hsplit : B' = B'.filter (fun a => 1 < a) + B'.filter (fun a => ¬ 1 < a) :=
    (Multiset.filter_add_not (fun a => 1 < a) B').symm
  have hnot1 : ∀ a ∈ B'.filter (fun a => ¬ 1 < a), a = 1 := by
    intro a ha
    rw [Multiset.mem_filter] at ha
    have h1 := hge a ha.1
    omega
  have hprod : B'.prod = M := by
    conv_lhs => rw [hsplit]
    rw [Multiset.prod_add, hfilt, Multiset.prod_singleton,
      prod_eq_one_of_forall_eq_one _ hnot1, mul_one]
  have hgexp : ∀ p : ℕ, p.Prime → gExp p B' = padicValNat p M := by
    intro p hp
    have hz : ((B'.filter (fun a => ¬ 1 < a)).map fun a => padicValNat p a).gcd = 0 := by
      rw [Multiset.gcd_eq_zero_iff]
      intro x hx
      rw [Multiset.mem_map] at hx
      obtain ⟨a, ha, rfl⟩ := hx
      rw [hnot1 a ha, padicValNat_one_right]
    simp only [gExp]
    conv_lhs => rw [hsplit]
    rw [Multiset.map_add, Multiset.gcd_add, hfilt, Multiset.map_singleton,
      Multiset.gcd_singleton, hz, gcd_zero_right, normalize_idem, normalize_eq]
  have hM0 : M ≠ 0 := by omega
  have hfin : M = M.factorization.prod (· ^ ·) := (Nat.prod_factorization_pow_eq_self hM0).symm
  unfold Mval
  rw [hprod]
  conv_rhs => rw [hfin, Nat.prod_factorization_eq_prod_primeFactors]
  apply Finset.prod_congr rfl
  intro p hp
  have hpp := Nat.prime_of_mem_primeFactors hp
  rw [hgexp p hpp, Nat.factorization_def M hpp]

/-- Any terminal board reachable from an initial board `B₀` has exactly one
entry `> 1`. -/
lemma unique_large_of_reachable_terminal (B₀ : Board) (hB₀ : IsInitial B₀)
    (B' : Board) (hreach : Reachable B₀ B') (hterm : IsTerminal B') :
    HasUniqueLarge B' := by
  have hf : B₀.filter (fun a => 1 < a) = B₀ := Multiset.filter_eq_self.mpr hB₀.2
  have h0 : 1 ≤ (B₀.filter fun a => 1 < a).card := by
    have hc : (B₀.filter fun a => 1 < a).card = 2026 := by rw [hf, hB₀.1]
    omega
  have h1 : 1 ≤ (B'.filter fun a => 1 < a).card := large_count_pos_of_reachable h0 hreach
  exact le_antisymm hterm h1

/-- Any entry `> 1` of a terminal board reachable from an initial board `B₀`
equals `Mval B₀`. -/
lemma large_mem_eq_Mval {B₀ B' : Board} (hB₀ : IsInitial B₀) (hreach : Reachable B₀ B')
    (hterm : IsTerminal B') {M : ℕ} (hM : 1 < M) (hMem : M ∈ B') : M = Mval B₀ := by
  have hge : ∀ a ∈ B', 1 ≤ a := ge_one_reachable (fun a ha => (hB₀.2 a ha).le) hreach
  have huniq : HasUniqueLarge B' := unique_large_of_reachable_terminal B₀ hB₀ B' hreach hterm
  have h1 : Mval B' = M := Mval_terminal hge huniq hM hMem
  have h2 : Mval B' = Mval B₀ := Mval_reachable (fun a ha => (hB₀.2 a ha).le) hreach
  rw [h2] at h1
  exact h1.symm

snip end

/-- **Statement (a), part 1 — termination.**  There is no infinite play starting
from an initial board `B₀`: no infinite sequence of boards can start at `B₀` and
have every consecutive pair related by a `Move`. -/
problem imo2026_p1a_termination (B₀ : Board) (hB₀ : IsInitial B₀) :
    ¬ ∃ f : ℕ → Board, f 0 = B₀ ∧ ∀ k, Move (f k) (f (k + 1)) := by
  -- Local helper: the product of a board with all entries `≥ 1` is positive.
  have prod_pos_of_ge_one : ∀ (B : Board), (∀ a ∈ B, 1 ≤ a) → 0 < B.prod := by
    intro B h
    have h0 : (0 : ℕ) ∉ B := fun h0 => by
      have := h 0 h0
      omega
    exact Nat.pos_of_ne_zero (fun hp => h0 (Multiset.prod_eq_zero_iff.mp hp))
  -- Local helper: the lexicographic measure `(product, number of entries > 1)`
  -- strictly decreases under a move, on boards whose entries are all `≥ 1`.
  have move_measure : ∀ {B B' : Board}, Move B B' → (∀ a ∈ B, 1 ≤ a) →
      (toLex (B'.prod, (B'.filter fun a => 1 < a).card) : ℕ ×ₗ ℕ) <
        toLex (B.prod, (B.filter fun a => 1 < a).card) := by
    intro B B' hmove hB
    obtain ⟨m, n, s, hm, hn, rfl, rfl⟩ := hmove
    have hm0 : m ≠ 0 := by omega
    have hn0 : n ≠ 0 := by omega
    have hg0 : 0 < Nat.gcd m n := Nat.pos_of_ne_zero (fun h => by
      rw [Nat.gcd_eq_zero_iff] at h
      exact hm0 h.1)
    have hlcm0 : 0 < Nat.lcm m n := Nat.pos_of_ne_zero (fun h => by
      have h2 := Nat.gcd_mul_lcm m n
      rw [h, mul_zero] at h2
      exact (mul_ne_zero hm0 hn0) h2.symm)
    have hgl : Nat.gcd m n * (Nat.lcm m n / Nat.gcd m n) = Nat.lcm m n :=
      Nat.mul_div_cancel' ((Nat.gcd_dvd_left m n).trans (Nat.dvd_lcm_left m n))
    have hPs : 0 < s.prod := prod_pos_of_ge_one s (fun a ha =>
      hB a (Multiset.mem_cons_of_mem (Multiset.mem_cons_of_mem ha)))
    have hprodB : (m ::ₘ n ::ₘ s).prod = Nat.gcd m n * (Nat.lcm m n * s.prod) := by
      rw [Multiset.prod_cons, Multiset.prod_cons]
      calc m * (n * s.prod) = (m * n) * s.prod := (mul_assoc ..).symm
        _ = (Nat.gcd m n * Nat.lcm m n) * s.prod := by rw [Nat.gcd_mul_lcm]
        _ = Nat.gcd m n * (Nat.lcm m n * s.prod) := mul_assoc ..
    have hprodB' : (Nat.gcd m n ::ₘ (Nat.lcm m n / Nat.gcd m n) ::ₘ s).prod =
        Nat.lcm m n * s.prod := by
      rw [Multiset.prod_cons, Multiset.prod_cons, ← mul_assoc, hgl]
    rw [Prod.Lex.toLex_lt_toLex]
    by_cases hg1 : Nat.gcd m n = 1
    · right
      refine ⟨?_, ?_⟩
      · rw [hprodB, hprodB', hg1, one_mul]
      · have hl1 : 1 < Nat.lcm m n / Nat.gcd m n := by
          have hlcm : Nat.lcm m n = m * n := by
            have h := Nat.gcd_mul_lcm m n
            rw [hg1, one_mul] at h
            exact h
          rw [hlcm, hg1, Nat.div_one]
          calc 1 < 2 * 2 := by norm_num
            _ ≤ m * n := Nat.mul_le_mul hm hn
        have hg1' : ¬ (1 < Nat.gcd m n) := by omega
        have cfB : ((m ::ₘ n ::ₘ s).filter fun a => 1 < a).card =
            (s.filter fun a => 1 < a).card + 2 := by
          rw [Multiset.filter_cons, Multiset.filter_cons, if_pos hm, if_pos hn,
            Multiset.card_add, Multiset.card_add, Multiset.card_singleton,
            Multiset.card_singleton]
          omega
        have cfB' : ((Nat.gcd m n ::ₘ (Nat.lcm m n / Nat.gcd m n) ::ₘ s).filter
              fun a => 1 < a).card = (s.filter fun a => 1 < a).card + 1 := by
          rw [Multiset.filter_cons, Multiset.filter_cons, if_neg hg1', if_pos hl1,
            Multiset.card_add, Multiset.card_add, Multiset.card_singleton,
            Multiset.card_zero]
          omega
        rw [cfB', cfB]
        omega
    · left
      have hg2 : 2 ≤ Nat.gcd m n := by omega
      rw [hprodB, hprodB']
      have hpos : 0 < Nat.lcm m n * s.prod := Nat.mul_pos hlcm0 hPs
      calc Nat.lcm m n * s.prod = 1 * (Nat.lcm m n * s.prod) := (one_mul _).symm
        _ < Nat.gcd m n * (Nat.lcm m n * s.prod) :=
            Nat.mul_lt_mul_of_pos_right (by omega) hpos
  -- Local helper: the lexicographic order on `ℕ ×ₗ ℕ` is well-founded, so it
  -- admits no infinite descending sequence.
  have no_descending : ∀ (x : ℕ ×ₗ ℕ),
      ¬ ∃ f : ℕ → ℕ ×ₗ ℕ, f 0 = x ∧ ∀ k, f (k + 1) < f k := by
    intro x
    have hacc : Acc ((· < ·) : ℕ ×ₗ ℕ → ℕ ×ₗ ℕ → Prop) x := wellFounded_lt.apply x
    induction hacc with
    | intro x _ ih =>
      rintro ⟨f, h0, hf⟩
      exact ih (f 1) (h0 ▸ hf 0) ⟨fun k => f (k + 1), rfl, fun k => hf (k + 1)⟩
  -- Main argument: the measure of the boards would form an infinite descending
  -- sequence in the well-founded lexicographic order on `ℕ × ℕ`.
  rintro ⟨f, h0, hf⟩
  have hge : ∀ k, ∀ a ∈ f k, 1 ≤ a := by
    intro k
    induction k with
    | zero =>
      rw [h0]
      exact fun a ha => (hB₀.2 a ha).le
    | succ k ih =>
      exact move_ge_one (hf k) ih
  have hdesc : ∀ k,
      (toLex ((f (k + 1)).prod, ((f (k + 1)).filter fun a => 1 < a).card) : ℕ ×ₗ ℕ) <
        toLex ((f k).prod, ((f k).filter fun a => 1 < a).card) :=
    fun k => move_measure (hf k) (hge k)
  exact no_descending (toLex (B₀.prod, (B₀.filter fun a => 1 < a).card))
    ⟨fun k => toLex ((f k).prod, ((f k).filter fun a => 1 < a).card), by
      show toLex ((f 0).prod, ((f 0).filter fun a => 1 < a).card) =
        toLex (B₀.prod, (B₀.filter fun a => 1 < a).card)
      rw [h0], hdesc⟩

/-- **Statement (a), part 2 — unique large entry.**  Any terminal board reachable
from an initial board `B₀` has exactly one entry `> 1`. -/
problem imo2026_p1a_unique_large (B₀ : Board) (hB₀ : IsInitial B₀)
    (B' : Board) (hreach : Reachable B₀ B') (hterm : IsTerminal B') :
    HasUniqueLarge B' :=
  unique_large_of_reachable_terminal B₀ hB₀ B' hreach hterm

/-- **Statement (b) — invariance of `M`.**  Any two terminal boards reachable from
the same initial board `B₀` have the same set of entries `> 1`; since (by (a)) each
has exactly one such entry, this says the terminal value `M` is the same for both. -/
problem imo2026_p1b_invariance (B₀ : Board) (hB₀ : IsInitial B₀)
    (B₁ B₂ : Board) (h₁ : Reachable B₀ B₁) (h₂ : Reachable B₀ B₂)
    (t₁ : IsTerminal B₁) (t₂ : IsTerminal B₂) :
    ∀ M, (1 < M ∧ M ∈ B₁) ↔ (1 < M ∧ M ∈ B₂) := by
  have ex : ∀ B : Board, Reachable B₀ B → IsTerminal B → ∃ x, 1 < x ∧ x ∈ B := by
    intro B hr ht
    have hu := unique_large_of_reachable_terminal B₀ hB₀ B hr ht
    have hu' : (B.filter fun a => 1 < a).card = 1 := hu
    have hne : B.filter (fun a => 1 < a) ≠ 0 := by
      intro hz
      rw [hz, Multiset.card_zero] at hu'
      exact absurd hu' (by decide)
    obtain ⟨x, hx⟩ := Multiset.exists_mem_of_ne_zero hne
    exact ⟨x, (Multiset.mem_filter.mp hx).2, (Multiset.mem_filter.mp hx).1⟩
  obtain ⟨x₁, hx₁, hx₁mem⟩ := ex B₁ h₁ t₁
  obtain ⟨x₂, hx₂, hx₂mem⟩ := ex B₂ h₂ t₂
  have hx₁val : x₁ = Mval B₀ := large_mem_eq_Mval hB₀ h₁ t₁ hx₁ hx₁mem
  have hx₂val : x₂ = Mval B₀ := large_mem_eq_Mval hB₀ h₂ t₂ hx₂ hx₂mem
  intro M
  constructor
  · intro ⟨hM, hMem⟩
    have hMv := large_mem_eq_Mval hB₀ h₁ t₁ hM hMem
    exact ⟨hM, (hMv.trans hx₂val.symm) ▸ hx₂mem⟩
  · intro ⟨hM, hMem⟩
    have hMv := large_mem_eq_Mval hB₀ h₂ t₂ hM hMem
    exact ⟨hM, (hMv.trans hx₁val.symm) ▸ hx₁mem⟩

/-- **Value of `M` (correctness of the explicit formula).**  For any terminal board
`B'` reachable from an initial board `B₀`, the unique entry `M > 1` of `B'` equals
the invariant `Mval B₀`. -/
problem imo2026_p1_terminal_value (B₀ : Board) (hB₀ : IsInitial B₀)
    (B' : Board) (hreach : Reachable B₀ B') (hterm : IsTerminal B')
    (M : ℕ) (hM : 1 < M) (hMem : M ∈ B') :
    M = Mval B₀ :=
  large_mem_eq_Mval hB₀ hreach hterm hM hMem

/-- The invariant terminal value is itself `> 1`, since all initial entries exceed
`1`. -/
problem imo2026_p1_mval_gt_one (B₀ : Board) (hB₀ : IsInitial B₀) : 1 < Mval B₀ := by
  have hge2 : ∀ a ∈ B₀, 2 ≤ a := hB₀.2
  have hcard : B₀.card = 2026 := hB₀.1
  have hB₀ne : B₀ ≠ 0 := by
    intro hz
    rw [hz, Multiset.card_zero] at hcard
    exact absurd hcard (by decide)
  obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero hB₀ne
  have ha2 : 2 ≤ a := hge2 a ha
  obtain ⟨p, hpp, hpdvd⟩ := Nat.exists_prime_and_dvd (n := a) (by omega)
  have hproddvd : a ∣ B₀.prod := Multiset.dvd_prod ha
  have hpd : p ∣ B₀.prod := hpdvd.trans hproddvd
  have hp0 : B₀.prod ≠ 0 := by
    rw [Ne, Multiset.prod_eq_zero_iff]
    intro h0
    have := hge2 0 h0
    omega
  have hpmem : p ∈ B₀.prod.primeFactors := Nat.mem_primeFactors.mpr ⟨hpp, hpd, hp0⟩
  haveI : Fact p.Prime := ⟨hpp⟩
  have hva : 1 ≤ padicValNat p a := one_le_padicValNat_of_dvd (by omega) hpdvd
  have hgexp : 1 ≤ gExp p B₀ := by
    have hmem : padicValNat p a ∈ B₀.map (fun a => padicValNat p a) :=
      Multiset.mem_map.mpr ⟨a, ha, rfl⟩
    have hne : (B₀.map fun a => padicValNat p a).gcd ≠ 0 := by
      intro hz0
      rw [Multiset.gcd_eq_zero_iff] at hz0
      exact (show padicValNat p a ≠ 0 by omega) (hz0 _ hmem)
    exact Nat.one_le_iff_ne_zero.mpr hne
  have hpow : p ≤ p ^ gExp p B₀ := by
    conv_lhs => rw [← pow_one p]
    exact Nat.pow_le_pow_right hpp.one_lt.le hgexp
  have hp2 : 1 < p := hpp.one_lt
  have hbig : 1 < p ^ gExp p B₀ := lt_of_lt_of_le hp2 hpow
  unfold Mval
  exact lt_of_lt_of_le hbig
    (Finset.single_le_prod'
      (fun q hq => Nat.one_le_pow (gExp q B₀) q (Nat.prime_of_mem_primeFactors hq).pos) hpmem)

end Imo2026P1
