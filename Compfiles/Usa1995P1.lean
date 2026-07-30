/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.List.GetD
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.NumberTheory] }

/-!
# USA Mathematical Olympiad 1995, Problem 1

Let `p` be an odd prime. The sequence `(aₙ) n ≥ 0` is defined as follows:
`a₀ = 0, a₁ = 1, ..., a_{p-2} = p - 2`, and for all `n ≥ p - 1`, `aₙ` is the
least integer greater than `a_{n-1}` such that `a₀, a₁, ..., aₙ` does not
contain an arithmetic progression of length `p`.

Prove that, for all `n`, `aₙ` is the number obtained by writing `n` in base
`p - 1` and reading the result in base `p`.
-/

namespace Usa1995P1

/-- `HasAp a p n m` means that the first `n + 1` terms `a 0, a 1, …, a (n-1), m`
(where the candidate `m` is the `n`-th term) contain an arithmetic progression
of length `p`: there are strictly increasing indices `v 0 < v 1 < … < v (p-1)`,
all at most `n`, whose values form an arithmetic progression. The last
conjunct splits the value condition according to whether the index is the
final position `n` (where the candidate `m` sits) or not. -/
def HasAp (a : ℕ → ℕ) (p n m : ℕ) : Prop :=
  ∃ v : Fin p → ℕ, StrictMono v ∧ (∀ i, v i ≤ n) ∧
    ∃ x d : ℕ, ∀ i : Fin p, (v i < n → a (v i) = x + i.val * d) ∧
      (v i = n → m = x + i.val * d)

snip begin

/-- A natural number is `(p)`-digit-free if no digit of its base-`p` expansion
equals `p - 1`. -/
def DigitFree (p m : ℕ) : Prop := ∀ d ∈ Nat.digits p m, d ≠ p - 1

/-- `bSeq p n` is the number obtained by writing `n` in base `p - 1` and reading
the result in base `p`. -/
def bSeq (p n : ℕ) : ℕ := Nat.ofDigits p (Nat.digits (p - 1) n)

/-- `phi p m` reads the base-`p` digits of `m` in base `p - 1`. On digit-free
numbers it is the inverse of `bSeq p`. -/
def phi (p m : ℕ) : ℕ := Nat.ofDigits (p - 1) (Nat.digits p m)

lemma phi_def (p m : ℕ) : phi p m = Nat.ofDigits (p - 1) (Nat.digits p m) := rfl

lemma bSeq_def (p n : ℕ) : bSeq p n = Nat.ofDigits p (Nat.digits (p - 1) n) := rfl

lemma ofDigits_cons_nat (b a : ℕ) (l : List ℕ) :
    Nat.ofDigits b (a :: l) = a + b * Nat.ofDigits b l := by
  simp only [Nat.ofDigits_cons]

lemma ofDigits_eq_zero_iff {b : ℕ} (hb : b ≠ 0) (l : List ℕ) :
    Nat.ofDigits b l = 0 ↔ ∀ d ∈ l, d = 0 := by
  induction l with
  | nil => simp
  | cons a l ih =>
      rw [ofDigits_cons_nat]
      simp only [Nat.add_eq_zero_iff, Nat.mul_eq_zero, List.forall_mem_cons, ih]
      constructor
      · rintro ⟨ha, hb' | hl⟩
        · exact absurd hb' hb
        · exact ⟨ha, hl⟩
      · rintro ⟨ha, hl⟩
        exact ⟨ha, Or.inr hl⟩

lemma phi_pos {p : ℕ} (hp : 2 ≤ p) {m : ℕ} (hm : 0 < m) : 0 < phi p m := by
  rw [Nat.pos_iff_ne_zero] at hm ⊢
  intro h
  apply hm
  have hall : ∀ d ∈ Nat.digits p m, d = 0 :=
    (ofDigits_eq_zero_iff (by omega : p - 1 ≠ 0) _).mp h
  have h0 : Nat.ofDigits p (Nat.digits p m) = 0 :=
    (ofDigits_eq_zero_iff (by omega : p ≠ 0) _).mpr hall
  rwa [Nat.ofDigits_digits] at h0

/-- If every entry of `l` is `< b` and different from `c`, then every base-`b`
digit of `Nat.ofDigits b l` is different from `c`. -/
lemma digits_ofDigits_ne {b c : ℕ} (hb : 1 < b) :
    ∀ {l : List ℕ}, (∀ d ∈ l, d < b) → (∀ d ∈ l, d ≠ c) →
      ∀ d ∈ Nat.digits b (Nat.ofDigits b l), d ≠ c := by
  intro l
  induction l with
  | nil =>
      intro _ _ d hd
      rw [Nat.ofDigits_nil, Nat.digits_zero] at hd
      exact absurd hd (by simp)
  | cons a l ih =>
      intro hlt hne d hd
      rcases Nat.eq_zero_or_pos (Nat.ofDigits b (a :: l)) with h0 | hpos
      · rw [h0, Nat.digits_zero] at hd
        exact absurd hd (by simp)
      · have ha : a < b := hlt a List.mem_cons_self
        have hmod : Nat.ofDigits b (a :: l) % b = a := by
          rw [ofDigits_cons_nat, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]
        have hdiv : Nat.ofDigits b (a :: l) / b = Nat.ofDigits b l := by
          rw [ofDigits_cons_nat, Nat.add_mul_div_left _ _ (by omega : 0 < b),
            Nat.div_eq_of_lt ha, Nat.zero_add]
        have hdig : Nat.digits b (Nat.ofDigits b (a :: l)) =
            a :: Nat.digits b (Nat.ofDigits b l) := by
          rw [Nat.digits_def' hb hpos, hmod, hdiv]
        rw [hdig] at hd
        rcases List.mem_cons.mp hd with hda | hd'
        · rw [hda]; exact hne a List.mem_cons_self
        · exact ih (fun e he => hlt e (List.mem_cons_of_mem a he))
            (fun e he => hne e (List.mem_cons_of_mem a he)) d hd'

/-- The `k`-th digit of `m` in base `b` (with `0` padding). -/
lemma digits_getD {b : ℕ} (hb : 1 < b) (m k : ℕ) :
    (Nat.digits b m).getD k 0 = m / b ^ k % b := by
  induction k generalizing m with
  | zero =>
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp [Nat.digits_zero]
      · rw [Nat.digits_def' hb hm, List.getD_cons_zero, pow_zero, Nat.div_one]
  | succ k ih =>
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp [Nat.digits_zero]
      · rw [Nat.digits_def' hb hm, List.getD_cons_succ, ih (m / b),
          Nat.div_div_eq_div_mul, ← pow_succ']

lemma mem_digits_of_getD_ne_zero {b m k c : ℕ} (h : (Nat.digits b m).getD k 0 = c)
    (hc : c ≠ 0) : c ∈ Nat.digits b m := by
  have hk : k < (Nat.digits b m).length := by
    by_contra h'
    have h'' := Nat.le_of_not_lt h'
    rw [List.getD_eq_default _ _ h''] at h
    exact hc h.symm
  rw [List.getD_eq_getElem _ _ hk] at h
  rw [← h]
  exact List.getElem_mem hk

/-- Adding a multiple of `d = e * p^(k+1) + c * p^k` only affects the `k`-th
base-`p` digit through `c` (no carries into that digit from below). -/
lemma digit_add_mul_eq {p : ℕ} (hp : 1 < p) {x d k c e : ℕ} (i : ℕ)
    (hd : d = e * p ^ (k + 1) + c * p ^ k) :
    (x + i * d) / p ^ k % p = (x / p ^ k % p + i * c) % p := by
  have hp0 : 0 < p := by omega
  have hpk : 0 < p ^ k := pow_pos hp0 k
  have hpk1 : p ^ (k + 1) = p * p ^ k := pow_succ' p k
  set X := x / p ^ (k + 1) with hX
  set xk := x / p ^ k % p with hxk
  set r := x % p ^ k with hr
  have hrlt : r < p ^ k := hr ▸ Nat.mod_lt x hpk
  have hx1 : x / p ^ k = X * p + xk := by
    have h1 := Nat.div_add_mod (x / p ^ k) p
    rw [Nat.div_div_eq_div_mul, ← pow_succ p k, ← hX, ← hxk] at h1
    rw [← h1, mul_comm p X]
  have hx2 : x = X * p ^ (k + 1) + xk * p ^ k + r := by
    have h2 := Nat.div_add_mod x (p ^ k)
    rw [hx1, ← hr] at h2
    rw [← h2, hpk1]
    ring
  set Q := xk + i * c with hQ
  have hsum : x + i * d = (X + i * e) * p ^ (k + 1) + Q * p ^ k + r := by
    conv_lhs => rw [hd, hx2]
    rw [hQ]
    ring
  have hq : Q * p ^ k = Q / p * p ^ (k + 1) + Q % p * p ^ k := by
    have h3 : Q = Q / p * p + Q % p := by rw [mul_comm, Nat.div_add_mod]
    conv_lhs => rw [h3]
    rw [hpk1]
    ring
  have hsum2 : x + i * d = ((X + i * e + Q / p) * p + Q % p) * p ^ k + r := by
    rw [hsum, hq, hpk1]
    ring
  have hdiv : (x + i * d) / p ^ k = (X + i * e + Q / p) * p + Q % p := by
    rw [hsum2, mul_comm ((X + i * e + Q / p) * p + Q % p) (p ^ k),
      Nat.mul_add_div hpk, Nat.div_eq_of_lt hrlt, add_zero]
  rw [hdiv, add_comm ((X + i * e + Q / p) * p) (Q % p), Nat.add_mul_mod_self_right,
    Nat.mod_eq_of_lt (Nat.mod_lt Q hp0)]

lemma ofDigits_map_add_mul {b c : ℕ} {g h : ℕ → ℕ} (l : List ℕ) :
    Nat.ofDigits b (l.map (fun d => g d + c * h d)) =
      Nat.ofDigits b (l.map g) + c * Nat.ofDigits b (l.map h) := by
  induction l with
  | nil => simp
  | cons a l ih =>
      rw [List.map_cons, List.map_cons, List.map_cons, ofDigits_cons_nat,
        ofDigits_cons_nat, ofDigits_cons_nat, ih]
      ring

/-- The key monotonicity fact: `phi` is strictly increasing on digit-free
numbers. Proved by strong induction on the smaller number, comparing the
least significant base-`p` digits. -/
lemma phi_strictMono_on_digitFree {p : ℕ} (hp : 2 ≤ p) (x : ℕ) :
    ∀ y, DigitFree p x → DigitFree p y → x < y → phi p x < phi p y := by
  induction x using Nat.strong_induction_on with
  | _ x' IH =>
  intro y hx hy hxy
  rcases Nat.eq_zero_or_pos x' with rfl | hxpos
  · have hypos : 0 < y := hxy
    have h0 : phi p 0 = 0 := by simp [phi, Nat.digits_zero]
    rw [h0]
    exact phi_pos hp hypos
  · have hypos : 0 < y := hxpos.trans hxy
    have hdx : Nat.digits p x' = x' % p :: Nat.digits p (x' / p) :=
      Nat.digits_def' (by omega) hxpos
    have hdy : Nat.digits p y = y % p :: Nat.digits p (y / p) :=
      Nat.digits_def' (by omega) hypos
    have hpx : phi p x' = x' % p + (p - 1) * phi p (x' / p) := by
      rw [phi_def, hdx, ofDigits_cons_nat, ← phi_def]
    have hpy : phi p y = y % p + (p - 1) * phi p (y / p) := by
      rw [phi_def, hdy, ofDigits_cons_nat, ← phi_def]
    have hxf : DigitFree p (x' / p) := fun d hd => hx d (by
      rw [hdx]; exact List.mem_cons_of_mem _ hd)
    have hyf : DigitFree p (y / p) := fun d hd => hy d (by
      rw [hdy]; exact List.mem_cons_of_mem _ hd)
    have hrx : x' % p ≠ p - 1 := hx _ (by
      rw [hdx]; exact List.mem_cons_self)
    have hrlt : x' % p < p := Nat.mod_lt _ (by omega)
    have hxy' : x' / p ≤ y / p := Nat.div_le_div_right hxy.le
    rcases lt_or_eq_of_le hxy' with h | h
    · have hlt : x' / p < x' := Nat.div_lt_self hxpos (by omega)
      have hphi := IH _ hlt _ hxf hyf h
      rw [hpx, hpy]
      have h1 : (p - 1) * phi p (x' / p) + (p - 1) ≤ (p - 1) * phi p (y / p) := by
        have h2 := Nat.mul_le_mul_left (p - 1) (Nat.succ_le_of_lt hphi)
        rwa [Nat.succ_eq_add_one, mul_add, mul_one] at h2
      omega
    · have hrs : x' % p < y % p := by
        have hx' := Nat.div_add_mod x' p
        have hy' := Nat.div_add_mod y p
        rw [h] at hx'
        omega
      rw [hpx, hpy, h]
      omega

/-- The base-`p` digits of `bSeq p n` are exactly the base-`(p-1)` digits of `n`. -/
lemma digits_bSeq {p : ℕ} (hp : 3 ≤ p) (n : ℕ) :
    Nat.digits p (bSeq p n) = Nat.digits (p - 1) n := by
  rw [bSeq_def]
  apply Nat.digits_ofDigits p (by omega)
  · intro d hd
    exact (Nat.digits_lt_base (by omega : 1 < p - 1) hd).trans (by omega)
  · intro hne
    rcases eq_or_ne n 0 with rfl | hn
    · rw [Nat.digits_zero] at hne
      exact (hne rfl).elim
    · exact Nat.getLast_digit_ne_zero _ hn

lemma phi_bSeq {p : ℕ} (hp : 3 ≤ p) (n : ℕ) : phi p (bSeq p n) = n := by
  rw [phi_def, digits_bSeq hp n, Nat.ofDigits_digits]

lemma digitFree_bSeq {p : ℕ} (hp : 3 ≤ p) (n : ℕ) : DigitFree p (bSeq p n) := by
  intro d hd
  rw [digits_bSeq hp n] at hd
  have h := Nat.digits_lt_base (by omega : 1 < p - 1) hd
  omega

lemma bSeq_phi {p : ℕ} (hp : 3 ≤ p) {m : ℕ} (hm : DigitFree p m) : bSeq p (phi p m) = m := by
  rw [bSeq_def, phi_def,
    Nat.digits_ofDigits (p - 1) (by omega : 1 < p - 1) (Nat.digits p m)
      (fun d hd => by
        have hlt := Nat.digits_lt_base (by omega : 1 < p) hd
        have hne := hm d hd
        omega)
      (fun hne => by
        rcases eq_or_ne m 0 with rfl | h0
        · rw [Nat.digits_zero] at hne
          exact (hne rfl).elim
        · exact Nat.getLast_digit_ne_zero p h0),
    Nat.ofDigits_digits]

lemma bSeq_strictMono {p : ℕ} (hp : 3 ≤ p) : StrictMono (bSeq p) := by
  intro m n hmn
  rcases lt_trichotomy (bSeq p m) (bSeq p n) with h | h | h
  · exact h
  · have h2 := congrArg (phi p) h
    rw [phi_bSeq hp, phi_bSeq hp] at h2
    exact absurd h2 (ne_of_lt hmn)
  · have h2 := phi_strictMono_on_digitFree (by omega) _ _ (digitFree_bSeq hp n)
      (digitFree_bSeq hp m) h
    rw [phi_bSeq hp, phi_bSeq hp] at h2
    omega

lemma bSeq_eq_self_of_lt {p : ℕ} (_hp : 3 ≤ p) {n : ℕ} (hn : n < p - 1) : bSeq p n = n := by
  rw [bSeq_def]
  rcases Nat.eq_zero_or_pos n with rfl | h0
  · rw [Nat.digits_zero, Nat.ofDigits_nil]
  · rw [Nat.digits_of_lt (p - 1) n (by omega) hn, Nat.ofDigits_cons, Nat.ofDigits_nil]
    simp

/-- The non-existence part: among the values `bSeq p i` there is no arithmetic
progression of length `p`. If `x, x + d, …, x + (p-1) d` are all digit-free and
`d > 0`, then looking at the least significant nonzero base-`p` digit of `d`,
the `k`-th digits of the progression terms run through all residues mod `p`,
so one of them equals `p - 1`: contradiction. -/
lemma exists_mem_digits_pred {p : ℕ} (hp : p.Prime) {x d : ℕ} (hd : 0 < d) :
    ∃ i < p, p - 1 ∈ Nat.digits p (x + i * d) := by
  have hpp : 1 < p := hp.one_lt
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨by omega⟩
  set K := padicValNat p d with hK
  have hdvd : p ^ K ∣ d := pow_padicValNat_dvd
  have hndvd : ¬ p ^ (K + 1) ∣ d := pow_succ_padicValNat_not_dvd (by omega)
  obtain ⟨e, he⟩ := hdvd
  have hpe : ¬ p ∣ e := by
    rintro ⟨f, hf⟩
    apply hndvd
    exact ⟨f, by rw [he, hf, pow_succ']; ring⟩
  have hc0 : e % p ≠ 0 := fun hz => hpe (Nat.dvd_of_mod_eq_zero hz)
  have hcnz : (((e % p : ℕ) : ZMod p)) ≠ 0 := by
    rw [ne_eq, ZMod.natCast_eq_zero_iff]
    exact fun hdiv => hc0 (Nat.eq_zero_of_dvd_of_lt hdiv (Nat.mod_lt e (by omega)))
  obtain ⟨j, hj⟩ : ∃ j : ZMod p,
      ((x / p ^ K % p : ℕ) : ZMod p) + j * ((e % p : ℕ) : ZMod p) =
        ((p - 1 : ℕ) : ZMod p) := by
    refine ⟨(((p - 1 : ℕ) : ZMod p) - ((x / p ^ K % p : ℕ) : ZMod p)) /
      (((e % p : ℕ) : ZMod p)), ?_⟩
    rw [div_mul_cancel₀ _ hcnz, add_sub_cancel]
  have hmod : (x / p ^ K % p + j.val * (e % p)) % p = p - 1 := by
    have h2 : ((x / p ^ K % p + j.val * (e % p) : ℕ) : ZMod p) =
        ((p - 1 : ℕ) : ZMod p) := by
      rw [Nat.cast_add, Nat.cast_mul, ZMod.natCast_zmod_val j]
      exact hj
    have h3 := (ZMod.natCast_eq_natCast_iff' _ _ _).mp h2
    rwa [Nat.mod_eq_of_lt (by omega : p - 1 < p)] at h3
  refine ⟨j.val, ZMod.val_lt j, ?_⟩
  have hdecomp : d = (e / p) * p ^ (K + 1) + e % p * p ^ K := by
    have h1 : e = e / p * p + e % p := by rw [mul_comm, Nat.div_add_mod]
    rw [h1] at he
    rw [he, pow_succ']
    ring
  have hdig := digit_add_mul_eq (x := x) hpp j.val hdecomp
  have hgetD : (Nat.digits p (x + j.val * d)).getD K 0 = p - 1 := by
    rw [digits_getD hpp, hdig]
    exact hmod
  exact mem_digits_of_getD_ne_zero hgetD (by omega)

/-- If all candidate values are digit-free (here: values of `bSeq p`), there is
no arithmetic progression of length `p`. -/
lemma not_hasAp {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) {a : ℕ → ℕ} {n m : ℕ}
    (h : ∀ i ≤ n, (if i < n then a i else m) = bSeq p i) : ¬ HasAp a p n m := by
  rintro ⟨v, hvmono, hvle, x, d, hval⟩
  have hval' : ∀ i : Fin p, (if v i < n then a (v i) else m) = x + i.val * d := by
    intro i
    by_cases hi : v i < n
    · rw [if_pos hi]
      exact (hval i).1 hi
    · have hni : v i = n := by have hvi := hvle i; omega
      rw [if_neg hi]
      exact (hval i).2 hni
  have hw : ∀ i : Fin p, DigitFree p (x + i.val * d) := by
    intro i
    rw [← hval' i, h (v i) (hvle i)]
    exact digitFree_bSeq hp3 _
  have hd0 : d ≠ 0 := by
    intro hz
    have hv01 : v ⟨0, by omega⟩ < v ⟨1, by omega⟩ :=
      hvmono (Fin.mk_lt_mk.mpr Nat.one_pos)
    have e0 := hval' ⟨0, by omega⟩
    have e1 := hval' ⟨1, by omega⟩
    rw [hz] at e0 e1
    simp only [mul_zero, add_zero] at e0 e1
    rw [h _ (hvle ⟨0, by omega⟩)] at e0
    rw [h _ (hvle ⟨1, by omega⟩)] at e1
    have hinj : v ⟨0, by omega⟩ = v ⟨1, by omega⟩ :=
      (bSeq_strictMono hp3).injective (e0.trans e1.symm)
    omega
  obtain ⟨i, hi, hmem⟩ := exists_mem_digits_pred hp (x := x) (d := d)
    (Nat.pos_of_ne_zero hd0)
  have hcon := hw ⟨i, hi⟩
  exact (hcon (p - 1) hmem) rfl

/-- The construction part: if `m < bSeq p n` has a base-`p` digit equal to
`p - 1`, then reducing every such digit of `m` by `j` (for `j = p-1, …, 0`)
gives an arithmetic progression of length `p` whose first `p - 1` terms are
digit-free, hence equal to `a` at indices below `n`. -/
lemma hasAp_of_mem_digits_pred {p : ℕ} (hp : 3 ≤ p) {a : ℕ → ℕ} {n m : ℕ}
    (IH : ∀ k < n, a k = bSeq p k) (hhi : m < bSeq p n)
    (hmem : p - 1 ∈ Nat.digits p m) : HasAp a p n m := by
  set L := Nat.digits p m with hL
  set m₀ := Nat.ofDigits p (L.map fun d => if d = p - 1 then 0 else d) with hm₀
  set E := Nat.ofDigits p (L.map fun d => if d = p - 1 then 1 else 0) with hE
  have hf : ∀ j ≤ p - 1,
      (fun d => if d = p - 1 then p - 1 - j else d) =
        fun d => (if d = p - 1 then 0 else d) + (p - 1 - j) *
          (if d = p - 1 then 1 else 0) := by
    intro j hj
    funext d
    by_cases hd : d = p - 1 <;> simp [hd]
  have hlin : ∀ j ≤ p - 1,
      Nat.ofDigits p (L.map fun d => if d = p - 1 then p - 1 - j else d) =
        m₀ + (p - 1 - j) * E := by
    intro j hj
    rw [hf j hj, ofDigits_map_add_mul]
  have hEpos : 0 < E := by
    rw [Nat.pos_iff_ne_zero]
    intro hz
    have hall : ∀ d ∈ L.map (fun d => if d = p - 1 then 1 else 0), d = 0 :=
      (ofDigits_eq_zero_iff (by omega : p ≠ 0) _).mp hz
    have h1 : (1 : ℕ) ∈ L.map (fun d => if d = p - 1 then 1 else 0) := by
      apply List.mem_map.mpr
      exact ⟨p - 1, hmem, if_pos rfl⟩
    have h10 := hall 1 h1
    omega
  have hm_eq : m = m₀ + (p - 1) * E := by
    have h0 := hlin 0 (by omega)
    have hid : L.map (fun d => if d = p - 1 then p - 1 - 0 else d) = L := by
      have hfun : (fun d => if d = p - 1 then p - 1 - 0 else d) = fun d => d := by
        funext d
        by_cases hd : d = p - 1 <;> simp [hd]
      rw [hfun]
      exact List.map_id' L
    rw [hid] at h0
    have hsub : p - 1 - 0 = p - 1 := Nat.sub_zero _
    rw [hsub] at h0
    have hmm : m = Nat.ofDigits p L := by
      rw [hL]
      exact (Nat.ofDigits_digits p m).symm
    rw [hmm]
    exact h0
  have htfree : ∀ i < p - 1, DigitFree p (m₀ + i * E) := by
    intro i hi
    have hti : m₀ + i * E =
        Nat.ofDigits p (L.map fun d => if d = p - 1 then p - 1 - (p - 1 - i) else d) := by
      rw [hlin (p - 1 - i) (by omega), show p - 1 - (p - 1 - i) = i by omega]
    rw [hti]
    intro d hd
    have hlt : ∀ e ∈ L.map (fun d => if d = p - 1 then p - 1 - (p - 1 - i) else d),
        e < p := by
      intro e he
      obtain ⟨d', hd', rfl⟩ := List.mem_map.mp he
      have hd'' := Nat.digits_lt_base (by omega : 1 < p) hd'
      by_cases h2 : d' = p - 1
      · rw [if_pos h2]; omega
      · rw [if_neg h2]; exact hd''
    have hne : ∀ e ∈ L.map (fun d => if d = p - 1 then p - 1 - (p - 1 - i) else d),
        e ≠ p - 1 := by
      intro e he
      obtain ⟨d', hd', rfl⟩ := List.mem_map.mp he
      by_cases h2 : d' = p - 1
      · rw [if_pos h2]; omega
      · rw [if_neg h2]; exact h2
    exact digits_ofDigits_ne (by omega : 1 < p) hlt hne d hd
  have htlt : ∀ i < p - 1, m₀ + i * E < m := by
    intro i hi
    rw [hm_eq]
    have h1 : i * E < (p - 1) * E := Nat.mul_lt_mul_of_pos_right hi hEpos
    omega
  have hphi : ∀ i < p - 1, phi p (m₀ + i * E) < n := by
    intro i hi
    have h1 : m₀ + i * E < bSeq p n := (htlt i hi).trans hhi
    have h2 := phi_strictMono_on_digitFree (by omega) _ _ (htfree i hi)
      (digitFree_bSeq hp n) h1
    rwa [phi_bSeq hp] at h2
  refine ⟨fun i => if i.val = p - 1 then n else phi p (m₀ + i.val * E), ?_, ?_,
    m₀, E, ?_⟩
  · intro i j hij
    obtain ⟨i, hi'⟩ := i
    obtain ⟨j, hj'⟩ := j
    have hji : i < j := hij
    dsimp only
    by_cases hj : j = p - 1
    · subst hj
      have hi2 : i ≠ p - 1 := by omega
      rw [if_pos rfl, if_neg hi2]
      exact hphi i (by omega)
    · have hi2 : i ≠ p - 1 := by omega
      rw [if_neg hj, if_neg hi2]
      have hlt2 : m₀ + i * E < m₀ + j * E := by
        have := Nat.mul_lt_mul_of_pos_right hji hEpos
        omega
      exact phi_strictMono_on_digitFree (by omega) _ _ (htfree _ (by omega))
        (htfree _ (by omega)) hlt2
  · intro i
    obtain ⟨i, hi'⟩ := i
    dsimp only
    by_cases hi : i = p - 1
    · subst hi
      rw [if_pos rfl]
    · rw [if_neg hi]
      exact (hphi i (by omega)).le
  · intro i
    obtain ⟨i, hi'⟩ := i
    refine ⟨?_, ?_⟩
    · intro hvi
      dsimp only at hvi ⊢
      by_cases hi : i = p - 1
      · subst hi
        rw [if_pos rfl] at hvi
        exact absurd hvi (lt_irrefl n)
      · rw [if_neg hi] at hvi ⊢
        rw [IH _ hvi, bSeq_phi hp (htfree i (by omega))]
    · intro hvi
      dsimp only at hvi
      by_cases hi : i = p - 1
      · subst hi
        exact hm_eq
      · rw [if_neg hi] at hvi
        have := hphi i (by omega)
        omega

snip end

/-- USA Mathematical Olympiad 1995, Problem 1. -/
problem usa1995_p1 (p : ℕ) (hp : p.Prime) (ho : Odd p) (a : ℕ → ℕ)
    (ha₀ : ∀ n < p - 1, a n = n)
    (ha₁ : ∀ n ≥ p - 1, IsLeast {m | a (n - 1) < m ∧ ¬ HasAp a p n m} (a n)) :
    ∀ n, a n = Nat.ofDigits p (Nat.digits (p - 1) n) := by
  have hp3 : 3 ≤ p := by
    have h2 := hp.two_le
    obtain ⟨k, hk⟩ := ho
    omega
  have key : ∀ n, a n = bSeq p n := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n IH =>
    rcases lt_or_ge n (p - 1) with hn | hn
    · rw [ha₀ n hn, bSeq_eq_self_of_lt hp3 hn]
    · have hn1 : 1 ≤ n := by omega
      have hprev : a (n - 1) = bSeq p (n - 1) := IH (n - 1) (by omega)
      have hbn_mem : a (n - 1) < bSeq p n ∧ ¬ HasAp a p n (bSeq p n) := by
        refine ⟨?_, ?_⟩
        · rw [hprev]
          exact bSeq_strictMono hp3 (by omega)
        · exact not_hasAp hp hp3 (fun i hi => by
            by_cases h'i : i < n
            · rw [if_pos h'i, IH i h'i]
            · have h'n : i = n := by omega
              rw [if_neg h'i, h'n])
      have hbn_le : ∀ m, a (n - 1) < m → ¬ HasAp a p n m → bSeq p n ≤ m := by
        intro m hmlo hmno
        by_contra hmlt
        have hmlt' : m < bSeq p n := lt_of_not_ge hmlt
        rw [hprev] at hmlo
        have hndf : ¬ DigitFree p m := by
          intro hdf
          have h1 := phi_strictMono_on_digitFree (by omega) _ _ (digitFree_bSeq hp3 _)
            hdf hmlo
          have h2 := phi_strictMono_on_digitFree (by omega) _ _ hdf
            (digitFree_bSeq hp3 _) hmlt'
          rw [phi_bSeq hp3] at h1 h2
          omega
        have hmem : p - 1 ∈ Nat.digits p m := by
          by_contra hc
          apply hndf
          intro d hd hd2
          exact hc (hd2 ▸ hd)
        exact hmno (hasAp_of_mem_digits_pred hp3 IH hmlt' hmem)
      obtain ⟨hmem, hlb⟩ := ha₁ n hn
      exact le_antisymm (hlb hbn_mem) (hbn_le (a n) hmem.1 hmem.2)
  intro n
  exact key n

end Usa1995P1
