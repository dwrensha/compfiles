/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Nat.Totient
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.NumberTheory] }

/-!
# USA Mathematical Olympiad 2018, Problem 3

Let n ≥ 2 be an integer, and let {a₁, ..., aₘ} denote the m = φ(n) integers
less than n and relatively prime to n. Assume that every prime divisor of m
also divides n. Prove that m divides a₁ᵏ + ⋯ + aₘᵏ for every positive integer k.
-/

namespace Usa2018P3

snip begin

/-- The set of integers in `[0, n)` that are coprime to `n`. For `n ≥ 2` this is
the set `{a₁, ..., aₘ}` of the problem statement. -/
def coprimeSet (n : ℕ) : Finset ℕ := (Finset.range n).filter (Nat.Coprime n)

/-- The sum of the `k`-th powers of the elements of `coprimeSet n`. -/
def powSum (n k : ℕ) : ℕ := ∑ a ∈ coprimeSet n, a ^ k

lemma mem_coprimeSet {n a : ℕ} : a ∈ coprimeSet n ↔ a < n ∧ Nat.Coprime n a := by
  simp [coprimeSet]

lemma coprimeSet_card (n : ℕ) : (coprimeSet n).card = n.totient :=
  (Nat.totient_eq_card_coprime n).symm

lemma one_mem_coprimeSet (n : ℕ) (hn : 2 ≤ n) : 1 ∈ coprimeSet n := by
  rw [mem_coprimeSet]
  exact ⟨by omega, Nat.coprime_one_right n⟩

lemma powSum_pos (n : ℕ) (hn : 2 ≤ n) (k : ℕ) : 0 < powSum n k := by
  have h1 : 1 ∈ coprimeSet n := one_mem_coprimeSet n hn
  calc (0 : ℕ) < 1 ^ k := by simp
    _ ≤ powSum n k := Finset.single_le_sum (fun a _ => Nat.zero_le (a ^ k)) h1

lemma powSum_zero (n : ℕ) : powSum n 0 = n.totient := by
  have h : ∑ a ∈ coprimeSet n, a ^ 0 = ∑ _a ∈ coprimeSet n, 1 :=
    Finset.sum_congr rfl (fun a _ => pow_zero a)
  rw [powSum, h, Finset.sum_const, smul_eq_mul, mul_one, coprimeSet_card]

/-- Coprimality is preserved when taking a value modulo the left argument. -/
lemma coprime_mod_left' {m x : ℕ} (h : Nat.Coprime m x) : Nat.Coprime m (x % m) := by
  have hmod : x % m + m * (x / m) = x := Nat.mod_add_div x m
  rw [← hmod] at h
  exact (Nat.coprime_add_mul_left_right m (x % m) (x / m)).mp h

/-- Elements of the form `a + n * h` with `a < n`, `h < q` are `< n * q`. -/
lemma add_mul_lt {n q a h : ℕ} (ha : a < n) (hh : h < q) : a + n * h < n * q := by
  calc a + n * h < n + n * h := Nat.add_lt_add_right ha _
    _ = n * (h + 1) := by ring
    _ ≤ n * q := Nat.mul_le_mul_left n (Nat.succ_le_of_lt hh)

/-- The map `(a, h) ↦ a + n * h` is injective when `a, a' < n`. -/
lemma add_mul_inj {n a h a' h' : ℕ} (ha : a < n) (ha' : a' < n)
    (heq : a + n * h = a' + n * h') : a = a' ∧ h = h' := by
  have hmod : (a + n * h) % n = (a' + n * h') % n := congrArg (· % n) heq
  rw [Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt ha'] at hmod
  have hnpos : 0 < n := by omega
  have hnmul : n * h = n * h' := by omega
  exact ⟨hmod, Nat.eq_of_mul_eq_mul_left hnpos hnmul⟩

/-- Key identity, case `q ∣ n`: the reduced residues mod `n*q` are exactly
`{a + n*h | a ∈ coprimeSet n, h < q}`. -/
lemma powSum_mul_prime_of_dvd {n q : ℕ} (hn : 2 ≤ n) (hq : q.Prime) (hqd : q ∣ n) (k : ℕ) :
    powSum (n * q) k = ∑ a ∈ coprimeSet n, ∑ h ∈ Finset.range q, (a + n * h) ^ k := by
  -- Note: primality of `q` is not needed in this case, only `q ∣ n`.
  have := hq.pos
  have hn0 : 0 < n := by omega
  have hset : coprimeSet (n * q) =
      (coprimeSet n ×ˢ Finset.range q).image (fun p : ℕ × ℕ => p.1 + n * p.2) := by
    ext x
    constructor
    · intro hx
      rw [mem_coprimeSet] at hx
      obtain ⟨hxlt, hxcp⟩ := hx
      rw [Finset.mem_image]
      refine ⟨⟨x % n, x / n⟩, ?_, Nat.mod_add_div x n⟩
      rw [Finset.mem_product, mem_coprimeSet, Finset.mem_range]
      refine ⟨⟨Nat.mod_lt x hn0,
          coprime_mod_left' (hxcp.coprime_dvd_left (Nat.dvd_mul_right n q))⟩, ?_⟩
      show x / n < q
      rw [Nat.div_lt_iff_lt_mul hn0, mul_comm q n]
      exact hxlt
    · intro hx
      rw [Finset.mem_image] at hx
      obtain ⟨⟨a, h⟩, hmem, rfl⟩ := hx
      rw [Finset.mem_product, mem_coprimeSet, Finset.mem_range] at hmem
      obtain ⟨⟨halt, hacp⟩, hh⟩ := hmem
      show a + n * h ∈ coprimeSet (n * q)
      rw [mem_coprimeSet]
      refine ⟨add_mul_lt halt hh, ?_⟩
      have hqa : Nat.Coprime q a := hacp.coprime_dvd_left hqd
      obtain ⟨c, hc⟩ := hqd
      have h1 : Nat.Coprime n (a + n * h) := (Nat.coprime_add_mul_left_right n a h).mpr hacp
      have h2 : Nat.Coprime q (a + n * h) := by
        have heq : a + n * h = a + q * (c * h) := by rw [hc]; ring
        rw [heq]
        exact (Nat.coprime_add_mul_left_right q a (c * h)).mpr hqa
      exact h1.mul_left h2
  have hinj : Set.InjOn (fun p : ℕ × ℕ => p.1 + n * p.2)
      ↑(coprimeSet n ×ˢ Finset.range q) := by
    intro ⟨a, h⟩ hx ⟨a', h'⟩ hy heq
    rw [Finset.mem_coe, Finset.mem_product, mem_coprimeSet] at hx hy
    obtain ⟨h1, h2⟩ := add_mul_inj hx.1.1 hy.1.1 heq
    rw [Prod.mk.injEq]
    exact ⟨h1, h2⟩
  calc powSum (n * q) k = ∑ x ∈ coprimeSet (n * q), x ^ k := by simp only [powSum]
    _ = ∑ x ∈ (coprimeSet n ×ˢ Finset.range q).image (fun p : ℕ × ℕ => p.1 + n * p.2),
          x ^ k := by rw [hset]
    _ = ∑ x ∈ coprimeSet n ×ˢ Finset.range q, (x.1 + n * x.2) ^ k :=
        Finset.sum_image (f := fun x : ℕ => x ^ k) hinj
    _ = ∑ a ∈ coprimeSet n, ∑ h ∈ Finset.range q, (a + n * h) ^ k :=
        Finset.sum_product _ _ _

/-- Key identity, case `q ∤ n`: the reduced residues mod `n*q` are
`{a + n*h | a ∈ coprimeSet n, h < q}` with the multiples `q * a` removed. -/
lemma powSum_mul_prime_of_not_dvd {n q : ℕ} (hn : 2 ≤ n) (hq : q.Prime) (hqd : ¬ q ∣ n) (k : ℕ) :
    powSum (n * q) k + q ^ k * powSum n k =
      ∑ a ∈ coprimeSet n, ∑ h ∈ Finset.range q, (a + n * h) ^ k := by
  have hn0 : 0 < n := by omega
  have hq0 : 0 < q := hq.pos
  have hnq : Nat.Coprime n q := Nat.coprime_comm.mp (hq.coprime_iff_not_dvd.mpr hqd)
  have hset : (coprimeSet n ×ˢ Finset.range q).image (fun p : ℕ × ℕ => p.1 + n * p.2) =
      coprimeSet (n * q) ∪ (coprimeSet n).image (· * q) := by
    ext x
    constructor
    · intro hx
      rw [Finset.mem_image] at hx
      obtain ⟨⟨a, h⟩, hmem, rfl⟩ := hx
      rw [Finset.mem_product, mem_coprimeSet, Finset.mem_range] at hmem
      obtain ⟨⟨halt, hacp⟩, hh⟩ := hmem
      show a + n * h ∈ coprimeSet (n * q) ∪ (coprimeSet n).image (· * q)
      by_cases hqx : q ∣ a + n * h
      · rw [Finset.mem_union]
        right
        rw [Finset.mem_image]
        refine ⟨(a + n * h) / q, ?_, ?_⟩
        · rw [mem_coprimeSet]
          refine ⟨?_, ?_⟩
          · rw [Nat.div_lt_iff_lt_mul hq0]
            exact add_mul_lt halt hh
          · exact ((Nat.coprime_add_mul_left_right n a h).mpr hacp).coprime_dvd_right
              ⟨q, by rw [mul_comm ((a + n * h) / q) q]; exact (Nat.mul_div_cancel' hqx).symm⟩
        · show (a + n * h) / q * q = a + n * h
          rw [mul_comm ((a + n * h) / q) q]
          exact Nat.mul_div_cancel' hqx
      · rw [Finset.mem_union]
        left
        rw [mem_coprimeSet]
        exact ⟨add_mul_lt halt hh,
          ((Nat.coprime_add_mul_left_right n a h).mpr hacp).mul_left
            (hq.coprime_iff_not_dvd.mpr hqx)⟩
    · intro hx
      rw [Finset.mem_union] at hx
      rw [Finset.mem_image]
      rcases hx with hx | hx
      · rw [mem_coprimeSet] at hx
        obtain ⟨hxlt, hxcp⟩ := hx
        refine ⟨⟨x % n, x / n⟩, ?_, Nat.mod_add_div x n⟩
        rw [Finset.mem_product, mem_coprimeSet, Finset.mem_range]
        refine ⟨⟨Nat.mod_lt x hn0,
            coprime_mod_left' (hxcp.coprime_dvd_left (Nat.dvd_mul_right n q))⟩, ?_⟩
        show x / n < q
        rw [Nat.div_lt_iff_lt_mul hn0, mul_comm q n]
        exact hxlt
      · rw [Finset.mem_image] at hx
        obtain ⟨a, ha, rfl⟩ := hx
        rw [mem_coprimeSet] at ha
        obtain ⟨halt, hacp⟩ := ha
        refine ⟨⟨(a * q) % n, (a * q) / n⟩, ?_, Nat.mod_add_div _ n⟩
        rw [Finset.mem_product, mem_coprimeSet, Finset.mem_range]
        refine ⟨⟨Nat.mod_lt _ hn0, coprime_mod_left' (hacp.mul_right hnq)⟩, ?_⟩
        show (a * q) / n < q
        rw [Nat.div_lt_iff_lt_mul hn0, mul_comm q n]
        exact (Nat.mul_lt_mul_right hq0).mpr halt
  have hdisj : Disjoint (coprimeSet (n * q)) ((coprimeSet n).image (· * q)) := by
    rw [Finset.disjoint_left]
    intro x hx hxim
    rw [mem_coprimeSet] at hx
    rw [Finset.mem_image] at hxim
    obtain ⟨a, _, rfl⟩ := hxim
    have hcopq : Nat.Coprime q (a * q) := hx.2.coprime_dvd_left (Nat.dvd_mul_left q n)
    exact (hq.coprime_iff_not_dvd.mp hcopq) ⟨a, mul_comm a q⟩
  have hinj : Set.InjOn (fun p : ℕ × ℕ => p.1 + n * p.2)
      ↑(coprimeSet n ×ˢ Finset.range q) := by
    intro ⟨a, h⟩ hx ⟨a', h'⟩ hy heq
    rw [Finset.mem_coe, Finset.mem_product, mem_coprimeSet] at hx hy
    obtain ⟨h1, h2⟩ := add_mul_inj hx.1.1 hy.1.1 heq
    rw [Prod.mk.injEq]
    exact ⟨h1, h2⟩
  have hinjq : Set.InjOn (· * q) ↑(coprimeSet n) := by
    intro a _ b _ hab
    exact Nat.mul_right_cancel hq0 hab
  calc powSum (n * q) k + q ^ k * powSum n k
      = ∑ x ∈ coprimeSet (n * q), x ^ k + q ^ k * ∑ a ∈ coprimeSet n, a ^ k := by
        simp only [powSum]
    _ = ∑ x ∈ coprimeSet (n * q), x ^ k + ∑ a ∈ coprimeSet n, (a * q) ^ k := by
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        rw [mul_pow]
        ring
    _ = ∑ x ∈ coprimeSet (n * q), x ^ k + ∑ x ∈ (coprimeSet n).image (· * q), x ^ k := by
        congr 1
        exact (Finset.sum_image (f := fun x : ℕ => x ^ k) hinjq).symm
    _ = ∑ x ∈ coprimeSet (n * q) ∪ (coprimeSet n).image (· * q), x ^ k :=
        (Finset.sum_union hdisj).symm
    _ = ∑ x ∈ (coprimeSet n ×ˢ Finset.range q).image (fun p : ℕ × ℕ => p.1 + n * p.2),
          x ^ k := by rw [hset]
    _ = ∑ x ∈ coprimeSet n ×ˢ Finset.range q, (x.1 + n * x.2) ^ k :=
        Finset.sum_image (f := fun x : ℕ => x ^ k) hinj
    _ = ∑ a ∈ coprimeSet n, ∑ h ∈ Finset.range q, (a + n * h) ^ k :=
        Finset.sum_product _ _ _

/-- Binomial expansion of the double sum. -/
lemma sum_add_pow_eq (n q k : ℕ) :
    ∑ a ∈ coprimeSet n, ∑ h ∈ Finset.range q, (a + n * h) ^ k =
      q * powSum n k + ∑ j ∈ Finset.range k,
        (k.choose (j + 1)) * (n ^ (j + 1) * powSum n (k - (j + 1)) *
          ∑ h ∈ Finset.range q, h ^ (j + 1)) := by
  have hexp : ∀ a h : ℕ, (a + n * h) ^ k =
      ∑ m ∈ Finset.range (k + 1), (n * h) ^ m * a ^ (k - m) * k.choose m := by
    intro a h
    rw [add_comm a (n * h), add_pow]
    apply Finset.sum_congr rfl
    intro m _
    rw [Nat.cast_id]
  have key : ∀ m : ℕ,
      ∑ a ∈ coprimeSet n, ∑ h ∈ Finset.range q, (n * h) ^ m * a ^ (k - m) * k.choose m =
        k.choose m * (n ^ m * powSum n (k - m) * ∑ h ∈ Finset.range q, h ^ m) := by
    intro m
    have h1 : ∀ a : ℕ, ∑ h ∈ Finset.range q, (n * h) ^ m * a ^ (k - m) * k.choose m =
        (k.choose m * n ^ m * a ^ (k - m)) * ∑ h ∈ Finset.range q, h ^ m := by
      intro a
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h _
      rw [mul_pow]
      ring
    calc ∑ a ∈ coprimeSet n, ∑ h ∈ Finset.range q, (n * h) ^ m * a ^ (k - m) * k.choose m
        = ∑ a ∈ coprimeSet n,
            (k.choose m * n ^ m * a ^ (k - m)) * ∑ h ∈ Finset.range q, h ^ m :=
          Finset.sum_congr rfl fun a _ => h1 a
      _ = (∑ a ∈ coprimeSet n, k.choose m * n ^ m * a ^ (k - m)) *
            ∑ h ∈ Finset.range q, h ^ m := by
          rw [← Finset.sum_mul]
      _ = (k.choose m * n ^ m * ∑ a ∈ coprimeSet n, a ^ (k - m)) *
            ∑ h ∈ Finset.range q, h ^ m := by
          rw [← Finset.mul_sum]
      _ = k.choose m * (n ^ m * powSum n (k - m) * ∑ h ∈ Finset.range q, h ^ m) := by
          simp only [powSum]; ring
  have hsum0 : ∑ h ∈ Finset.range q, h ^ 0 = q := by
    simp
  calc ∑ a ∈ coprimeSet n, ∑ h ∈ Finset.range q, (a + n * h) ^ k
      = ∑ a ∈ coprimeSet n, ∑ h ∈ Finset.range q, ∑ m ∈ Finset.range (k + 1),
          (n * h) ^ m * a ^ (k - m) * k.choose m :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun h _ => hexp a h
    _ = ∑ a ∈ coprimeSet n, ∑ m ∈ Finset.range (k + 1), ∑ h ∈ Finset.range q,
          (n * h) ^ m * a ^ (k - m) * k.choose m :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ m ∈ Finset.range (k + 1), ∑ a ∈ coprimeSet n, ∑ h ∈ Finset.range q,
          (n * h) ^ m * a ^ (k - m) * k.choose m :=
        Finset.sum_comm
    _ = ∑ m ∈ Finset.range (k + 1),
          k.choose m * (n ^ m * powSum n (k - m) * ∑ h ∈ Finset.range q, h ^ m) :=
        Finset.sum_congr rfl fun m _ => key m
    _ = (∑ j ∈ Finset.range k,
          k.choose (j + 1) * (n ^ (j + 1) * powSum n (k - (j + 1)) *
            ∑ h ∈ Finset.range q, h ^ (j + 1))) +
        k.choose 0 * (n ^ 0 * powSum n (k - 0) * ∑ h ∈ Finset.range q, h ^ 0) :=
        Finset.sum_range_succ' _ _
    _ = q * powSum n k + ∑ j ∈ Finset.range k,
          k.choose (j + 1) * (n ^ (j + 1) * powSum n (k - (j + 1)) *
            ∑ h ∈ Finset.range q, h ^ (j + 1)) := by
        rw [Nat.choose_zero_right, hsum0, pow_zero, Nat.sub_zero]
        ring

/-- The prime power case: `p^(e-1) ∣ powSum (p^e) k`. -/
lemma pow_pred_dvd_powSum_prime_pow {p : ℕ} (hp : p.Prime) :
    ∀ e : ℕ, 1 ≤ e → ∀ k : ℕ, p ^ (e - 1) ∣ powSum (p ^ e) k := by
  intro e he
  induction e, he using Nat.le_induction with
  | base =>
    intro k
    exact one_dvd _
  | succ e he ih =>
    intro k
    have hpe2 : 2 ≤ p ^ e := le_trans hp.two_le (Nat.le_self_pow (by omega : e ≠ 0) p)
    have hpd : p ∣ p ^ e := dvd_pow_self p (by omega : e ≠ 0)
    have hid := powSum_mul_prime_of_dvd hpe2 hp hpd k
    rw [sum_add_pow_eq] at hid
    rw [show p ^ (e + 1) = p ^ e * p from (pow_succ p e).symm, hid,
      show e + 1 - 1 = e from by omega]
    apply dvd_add
    · have h := ih k
      have h1 : p ^ e = p * p ^ (e - 1) := by
        conv_lhs => rw [show e = e - 1 + 1 from by omega]
        rw [pow_succ']
      nth_rewrite 1 [h1]
      exact mul_dvd_mul_left _ h
    · apply Finset.dvd_sum
      intro j _hj
      have h2 : p ^ e ∣ (p ^ e) ^ (j + 1) := by
        rw [← pow_mul]
        exact pow_dvd_pow p (Nat.le_mul_of_pos_right e (by omega : 0 < j + 1))
      have h3 : (p ^ e) ^ (j + 1) ∣
          (p ^ e) ^ (j + 1) * powSum (p ^ e) (k - (j + 1)) *
            ∑ h ∈ Finset.range p, h ^ (j + 1) :=
        dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_refl _) _) _
      exact dvd_trans h2 (dvd_mul_of_dvd_right h3 _)

/-- Helper: `∑ h ∈ range q, h^(j+1) = ∑ h ∈ Icc 1 (q-1), h^(j+1)`. -/
lemma sum_range_pow_eq_sum_Icc (q j : ℕ) :
    ∑ h ∈ Finset.range q, h ^ (j + 1) = ∑ h ∈ Finset.Icc 1 (q - 1), h ^ (j + 1) := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp
  · obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
    rw [Finset.sum_range_succ' (fun h => h ^ (j + 1)) q,
      zero_pow (by omega : j + 1 ≠ 0), add_zero]
    have hIcc : Finset.Icc 1 (q + 1 - 1) = Finset.Ico 1 (q + 1) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_Ico]
      omega
    rw [hIcc, Finset.sum_Ico_eq_sum_range]
    exact Finset.sum_congr rfl fun x _ => by rw [add_comm]

/-- Corollary: `p^(c-1) ∣ 1^j + ⋯ + t^j` when `p^c ∣ t`, `c ≥ 1`, `j ≥ 1`. -/
lemma pow_pred_dvd_sum_pow_Icc {p : ℕ} (hp : p.Prime) :
    ∀ c : ℕ, 1 ≤ c → ∀ t : ℕ, p ^ c ∣ t → ∀ j : ℕ, 1 ≤ j →
      p ^ (c - 1) ∣ ∑ h ∈ Finset.Icc 1 t, h ^ j := by
  intro c hc
  induction c, hc using Nat.le_induction with
  | base =>
    intro t ht j hj
    exact one_dvd _
  | succ c hc ih =>
    intro t ht j hj
    rw [Nat.add_sub_cancel]
    have hp0 : 0 < p := hp.pos
    set m := p ^ (c + 1) with hm
    have hm0 : 0 < m := hm ▸ pow_pos hp0 (c + 1)
    set w := t / m with hw
    have htw : t = m * w := (Nat.mul_div_cancel' ht).symm
    have hsplit : ∑ h ∈ Finset.Icc 1 t, h ^ j =
        ∑ h ∈ (Finset.Icc 1 t).filter (fun h => p ∣ h), h ^ j +
        ∑ h ∈ (Finset.Icc 1 t).filter (fun h => ¬ p ∣ h), h ^ j := by
      rw [← Finset.sum_union (Finset.disjoint_filter_filter_not _ _ _),
        Finset.filter_union_filter_not_eq]
    rw [hsplit]
    apply dvd_add
    · -- multiples of `p`: `∑ = (∑ i ∈ Icc 1 (t/p), i^j) * p^j`
      have hpart2 : (Finset.Icc 1 t).filter (fun h => p ∣ h) =
          (Finset.Icc 1 (t / p)).image (· * p) := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
        constructor
        · rintro ⟨⟨h1, h2⟩, ⟨y, rfl⟩⟩
          refine ⟨y, ⟨?_, ?_⟩, mul_comm y p⟩
          · exact Nat.pos_of_mul_pos_right ((mul_comm y p).symm ▸ h1)
          · rw [Nat.le_div_iff_mul_le hp0]
            calc y * p = p * y := by ring
              _ ≤ t := h2
        · rintro ⟨y, ⟨h1, h2⟩, rfl⟩
          refine ⟨⟨Nat.mul_pos h1 hp0, ?_⟩, dvd_mul_left p y⟩
          exact (Nat.le_div_iff_mul_le hp0).1 h2
      rw [hpart2,
        Finset.sum_image (fun x _ y _ hxy => Nat.mul_right_cancel hp0 hxy)]
      have hsum2 : ∀ y : ℕ, (y * p) ^ j = y ^ j * p ^ j := fun y => mul_pow y p j
      rw [Finset.sum_congr rfl (fun y _ => hsum2 y), ← Finset.sum_mul]
      have htp : t / p = p ^ c * w := by
        have h1 : t = p * (p ^ c * w) := by rw [htw, hm, pow_succ']; ring
        rw [h1, Nat.mul_div_cancel_left _ hp0]
      have hdvd : p ^ (c - 1) ∣ ∑ y ∈ Finset.Icc 1 (t / p), y ^ j :=
        ih (t / p) (htp.symm ▸ dvd_mul_right _ _) j hj
      have hle : c ≤ c - 1 + j := by omega
      have hfinal : p ^ c ∣ p ^ (c - 1) * p ^ j := by
        rw [← pow_add]
        exact pow_dvd_pow p hle
      have h1' : p ^ (c - 1) * p ^ j ∣ (∑ y ∈ Finset.Icc 1 (t / p), y ^ j) * p ^ j :=
        mul_dvd_mul hdvd dvd_rfl
      exact dvd_trans hfinal h1'
    · -- the `p ∤ h` part: blocks of length `m` over `coprimeSet m`
      have hpart1 : (Finset.Icc 1 t).filter (fun h => ¬ p ∣ h) =
          ((Finset.range w ×ˢ coprimeSet m)).image (fun x => x.1 * m + x.2) := by
        have hpm : p ∣ m := by
          rw [hm]
          exact dvd_pow_self p (by omega : c + 1 ≠ 0)
        ext x
        constructor
        · intro hx
          rw [Finset.mem_filter] at hx
          obtain ⟨hxIcc, hpx⟩ := hx
          rw [Finset.mem_Icc] at hxIcc
          obtain ⟨h1, h2⟩ := hxIcc
          have hlt : (x - 1) / m < w := by
            rw [Nat.div_lt_iff_lt_mul hm0]
            calc x - 1 < t := by omega
              _ = w * m := by rw [htw, mul_comm]
          have hmod : (x - 1) % m < m := Nat.mod_lt _ hm0
          have hxeq2 : x = m * ((x - 1) / m) + ((x - 1) % m + 1) := by
            have hda : m * ((x - 1) / m) + (x - 1) % m = x - 1 := Nat.div_add_mod (x - 1) m
            calc x = (x - 1) + 1 := by omega
              _ = m * ((x - 1) / m) + (x - 1) % m + 1 := by rw [hda]
              _ = m * ((x - 1) / m) + ((x - 1) % m + 1) := by rw [add_assoc]
          have hr1 : (x - 1) % m + 1 < m := by
            by_contra hcon
            have hrm : (x - 1) % m + 1 = m :=
              le_antisymm (Nat.succ_le_of_lt hmod) (Nat.not_lt.1 hcon)
            have hpx' : p ∣ x := by
              rw [hxeq2, hrm]
              exact dvd_add (dvd_mul_of_dvd_left hpm _) hpm
            exact hpx hpx'
          have hr2 : Nat.Coprime m ((x - 1) % m + 1) := by
            rw [hm, Nat.coprime_pow_left_iff (by omega : 0 < c + 1), hp.coprime_iff_not_dvd]
            intro hpr
            have hpdx : p ∣ x := by
              rw [hxeq2]
              exact dvd_add (dvd_mul_of_dvd_left hpm _) hpr
            exact hpx hpdx
          rw [Finset.mem_image]
          refine ⟨⟨(x - 1) / m, (x - 1) % m + 1⟩, ?_, ?_⟩
          · rw [Finset.mem_product, Finset.mem_range, mem_coprimeSet]
            exact ⟨hlt, hr1, hr2⟩
          · show (x - 1) / m * m + ((x - 1) % m + 1) = x
            rw [mul_comm ((x - 1) / m) m]
            exact hxeq2.symm
        · intro hx
          rw [Finset.mem_image] at hx
          obtain ⟨⟨u, r⟩, hmem, rfl⟩ := hx
          dsimp only
          rw [Finset.mem_product] at hmem
          obtain ⟨hu, hrc⟩ := hmem
          rw [Finset.mem_range] at hu
          rw [mem_coprimeSet] at hrc
          obtain ⟨hr1, hr2⟩ := hrc
          have hrp : ¬ p ∣ r := by
            intro hpr
            have hcr : Nat.Coprime p r := Nat.Coprime.coprime_dvd_left hpm hr2
            exact (hp.coprime_iff_not_dvd.1 hcr) hpr
          have hr0 : r ≠ 0 := by
            rintro rfl
            exact hrp (dvd_zero p)
          rw [Finset.mem_filter, Finset.mem_Icc]
          refine ⟨⟨?_, ?_⟩, ?_⟩
          · omega
          · have h4 : (u + 1) * m ≤ w * m := by
              gcongr
              omega
            rw [Nat.succ_mul] at h4
            have htw' : t = w * m := by rw [htw, mul_comm]
            omega
          · intro hpx
            have h5 : p ∣ u * m := dvd_mul_of_dvd_right hpm u
            have h6 : p ∣ r := (Nat.dvd_add_iff_left h5).2 (add_comm (u * m) r ▸ hpx)
            exact hrp h6
      rw [hpart1]
      rw [Finset.sum_image (fun x hx y hy hxy => by
        obtain ⟨u1, r1⟩ := x
        obtain ⟨u2, r2⟩ := y
        rw [Finset.mem_coe, Finset.mem_product] at hx hy
        have hx2 : r1 < m := (mem_coprimeSet.1 hx.2).1
        have hy2 : r2 < m := (mem_coprimeSet.1 hy.2).1
        dsimp only at hxy
        have e1 : (u1 * m + r1) / m = u1 := by
          rw [add_comm (u1 * m) r1, Nat.add_mul_div_right _ _ hm0, Nat.div_eq_of_lt hx2,
            zero_add]
        have e2 : (u2 * m + r2) / m = u2 := by
          rw [add_comm (u2 * m) r2, Nat.add_mul_div_right _ _ hm0, Nat.div_eq_of_lt hy2,
            zero_add]
        have h12 : u1 = u2 := by
          have h := congrArg (· / m) hxy
          rw [e1, e2] at h
          exact h
        have hAB : u1 * m = u2 * m := by rw [h12]
        have h22 : r1 = r2 := by omega
        exact Prod.ext h12 h22)]
      rw [Finset.sum_product]
      apply Finset.dvd_sum
      intro u hu
      dsimp only
      have hexp : ∀ r : ℕ, (u * m + r) ^ j =
          ∑ i ∈ Finset.range (j + 1), (u * m) ^ i * r ^ (j - i) * j.choose i := by
        intro r
        rw [add_pow]
        exact Finset.sum_congr rfl fun i _ => by rw [Nat.cast_id]
      rw [Finset.sum_congr rfl (fun r _ => hexp r), Finset.sum_comm]
      apply Finset.dvd_sum
      intro i hi
      have hring : ∑ r ∈ coprimeSet m, (u * m) ^ i * r ^ (j - i) * j.choose i =
          ((u * m) ^ i * j.choose i) * powSum m (j - i) := by
        show ∑ r ∈ coprimeSet m, (u * m) ^ i * r ^ (j - i) * j.choose i =
          ((u * m) ^ i * j.choose i) * ∑ r ∈ coprimeSet m, r ^ (j - i)
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun r _ => by ring)
      rw [hring]
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · rw [pow_zero]
        simp only [Nat.choose_zero_right, one_mul, mul_one, tsub_zero]
        have h6 := pow_pred_dvd_powSum_prime_pow hp (c + 1) (by omega) j
        rwa [Nat.add_sub_cancel] at h6
      · have h5 : p ^ c ∣ (u * m) ^ i := by
          rw [hm, mul_pow, ← pow_mul]
          exact dvd_mul_of_dvd_right
            (pow_dvd_pow p (le_trans (Nat.le_succ c) (Nat.le_mul_of_pos_right (c + 1) hi0))) _
        exact dvd_trans h5 (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_refl _) _) _)

/-- `p ^ padicValNat p m ∣ m` for nonzero `m`. -/
lemma pow_padicValNat_dvd' {p m : ℕ} (hp : p.Prime) (hm : m ≠ 0) : p ^ padicValNat p m ∣ m := by
  haveI := Fact.mk hp
  exact (padicValNat_dvd_iff_le hm).2 le_rfl

lemma padicValNat_totient_mul_prime_of_dvd {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) {n : ℕ} (hn : n ≠ 0) (hqd : q ∣ n) :
    padicValNat p (Nat.totient (n * q)) = padicValNat p (Nat.totient n) := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Fact p.Prime := ⟨hp⟩
  set f := padicValNat q n with hf
  have hf1 : 1 ≤ f := one_le_padicValNat_of_dvd hn hqd
  have hqfn : q ^ f ∣ n := pow_padicValNat_dvd' hq hn
  set v := n / q ^ f with hv
  have hnv : n = q ^ f * v := (Nat.mul_div_cancel' hqfn).symm
  have hvnz : v ≠ 0 := by
    intro hv0
    rw [hv0, mul_zero] at hnv
    exact hn hnv
  have hqdv : ¬ q ∣ v := by
    intro hqv
    have h : q ^ (f + 1) ∣ n := by
      rw [hnv, pow_succ]
      exact mul_dvd_mul_left _ hqv
    exact pow_succ_padicValNat_not_dvd hn h
  have hcv : ∀ e : ℕ, 0 < e → Nat.Coprime (q ^ e) v := by
    intro e he
    rw [Nat.coprime_pow_left_iff he, hq.coprime_iff_not_dvd]
    exact hqdv
  have hq1 : q - 1 ≠ 0 := by
    have := hq.two_le
    omega
  have htv : Nat.totient v ≠ 0 := (Nat.totient_pos.2 (Nat.pos_of_ne_zero hvnz)).ne'
  have hqnz : q ≠ 0 := hq.ne_zero
  have hvpow : ∀ e : ℕ, padicValNat p (q ^ e) = 0 := by
    intro e
    rw [padicValNat.eq_zero_iff]
    refine Or.inr (Or.inr ?_)
    intro hd
    exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).1 (hp.dvd_of_dvd_pow hd))
  have htn : Nat.totient n = q ^ (f - 1) * (q - 1) * Nat.totient v := by
    rw [hnv, Nat.totient_mul (hcv f (by omega)), Nat.totient_prime_pow hq (by omega : 0 < f)]
  have htnq : Nat.totient (n * q) = q ^ f * (q - 1) * Nat.totient v := by
    have hnq : n * q = q ^ (f + 1) * v := by
      have h1 : n * q = (q ^ f * v) * q := by rw [← hnv]
      rw [h1, pow_succ]
      ring
    rw [hnq, Nat.totient_mul (hcv (f + 1) (by omega)),
      Nat.totient_prime_pow hq (by omega : 0 < f + 1), Nat.add_sub_cancel]
  rw [htn, htnq,
    padicValNat.mul (mul_ne_zero (pow_ne_zero _ hqnz) hq1) htv,
    padicValNat.mul (mul_ne_zero (pow_ne_zero _ hqnz) hq1) htv,
    padicValNat.mul (pow_ne_zero _ hqnz) hq1,
    padicValNat.mul (pow_ne_zero _ hqnz) hq1,
    hvpow f, hvpow (f - 1)]

lemma padicValNat_totient_mul_prime_of_not_dvd {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    {n : ℕ} (hn : n ≠ 0) (hqd : ¬ q ∣ n) :
    padicValNat p (Nat.totient (n * q)) =
      padicValNat p (Nat.totient n) + padicValNat p (q - 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcop : Nat.Coprime n q := (hq.coprime_iff_not_dvd.2 hqd).symm
  have hq1 : q - 1 ≠ 0 := by
    have := hq.two_le
    omega
  rw [Nat.totient_mul hcop, Nat.totient_prime hq,
    padicValNat.mul (Nat.totient_pos.2 (Nat.pos_of_ne_zero hn)).ne' hq1]

/-- The main claim: for `p` prime with `p ∣ n`, `p ^ ν_p (φ n) ∣ powSum n k`. -/
lemma pow_padicValNat_totient_dvd_powSum {p : ℕ} (hp : p.Prime) :
    ∀ n : ℕ, 2 ≤ n → p ∣ n → ∀ k : ℕ, p ^ padicValNat p (Nat.totient n) ∣ powSum n k := by
  haveI := Fact.mk hp
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro hn2 hpn k
    rcases k with _ | k
    · rw [powSum_zero]
      exact pow_padicValNat_dvd' hp (Nat.totient_pos.2 (by omega)).ne'
    · have hnnz : n ≠ 0 := by omega
      set e := padicValNat p n with he
      have he1 : 1 ≤ e := one_le_padicValNat_of_dvd hnnz hpn
      have hpen : p ^ e ∣ n := pow_padicValNat_dvd' hp hnnz
      set u := n / p ^ e with hu
      have hnu : n = p ^ e * u := (Nat.mul_div_cancel' hpen).symm
      have hu1 : 1 ≤ u := by
        by_contra hcon
        have hcon' : u < 1 := Nat.not_le.1 hcon
        interval_cases u
        simp at hnu
        exact hnnz hnu
      rcases Nat.lt_or_ge u 2 with hu2 | hu2
      · -- `u = 1`, i.e. `n = p ^ e`: the prime power case
        have hu1' : u = 1 := by omega
        have hnp : n = p ^ e := by rw [hnu, hu1', mul_one]
        have hp2 := hp.two_le
        rw [hnp, Nat.totient_prime_pow hp (by omega : 0 < e),
          padicValNat.mul (pow_ne_zero _ hp.ne_zero) (by omega : p - 1 ≠ 0),
          padicValNat.prime_pow]
        have h0 : padicValNat p (p - 1) = 0 := by
          rw [padicValNat.eq_zero_iff]
          refine Or.inr (Or.inr ?_)
          intro hd
          have hle := Nat.le_of_dvd (by omega : 0 < p - 1) hd
          omega
        rw [h0, add_zero]
        exact pow_pred_dvd_powSum_prime_pow hp e he1 (k + 1)
      · -- `u ≥ 2`: strip off the prime `q = minFac u ≠ p` and use induction
        set q := Nat.minFac u with hqdef
        have hune1 : u ≠ 1 := by omega
        have hq : q.Prime := Nat.minFac_prime hune1
        have hq2 := hq.two_le
        have hqu : q ∣ u := Nat.minFac_dvd u
        have hqn : q ∣ n := by
          rw [hnu]
          exact dvd_mul_of_dvd_right hqu _
        have hpnu : ¬ p ∣ u := by
          intro hpu
          have hd : p ^ (e + 1) ∣ n := by
            rw [hnu, pow_succ]
            exact mul_dvd_mul_left _ hpu
          exact pow_succ_padicValNat_not_dvd hnnz hd
        have hpq : p ≠ q := fun h => hpnu (h ▸ hqu)
        set n' := n / q with hn'def
        have hnn' : n = n' * q := (Nat.div_mul_cancel hqn).symm
        have hpen' : p ^ e ∣ n' := by
          have hcop : Nat.Coprime (p ^ e) q := by
            rw [Nat.coprime_pow_left_iff (by omega : 0 < e), hp.coprime_iff_not_dvd]
            exact fun h => hpq ((Nat.prime_dvd_prime_iff_eq hp hq).1 h)
          have h2 : p ^ e * q ∣ n := hcop.mul_dvd_of_dvd_of_dvd hpen hqn
          obtain ⟨s, hs⟩ := h2
          have hs' : n' = p ^ e * s := by
            have h3 : n' * q = (p ^ e * s) * q := by
              rw [← hnn', hs]
              ring
            exact Nat.mul_right_cancel (by omega : 0 < q) h3
          rw [hs']
          exact dvd_mul_right _ _
        have hpn' : p ∣ n' := dvd_trans (dvd_pow_self p (by omega : e ≠ 0)) hpen'
        have hn'2 : 2 ≤ n' := by
          have hpos : 0 < n' := by
            by_contra hcon
            have hcon' : n' ≤ 0 := Nat.not_lt.1 hcon
            interval_cases n'
            simp at hnn'
            omega
          exact le_trans hp.two_le (Nat.le_of_dvd hpos hpn')
        have hn'lt : n' < n := Nat.div_lt_self (by omega : 0 < n) hq.one_lt
        have IH' : ∀ k', p ^ padicValNat p (Nat.totient n') ∣ powSum n' k' :=
          fun k' => IH n' hn'lt hn'2 hpn' k'
        by_cases hcase : q ∣ n'
        · -- case `q ∣ n'`: no extra factor of `p` in `φ (n'*q)`
          have hval := padicValNat_totient_mul_prime_of_dvd hp hq hpq (by omega : n' ≠ 0) hcase
          rw [hnn', hval]
          have hid := powSum_mul_prime_of_dvd hn'2 hq hcase (k + 1)
          rw [sum_add_pow_eq] at hid
          rw [hid]
          apply dvd_add
          · exact dvd_mul_of_dvd_right (IH' (k + 1)) q
          · apply Finset.dvd_sum
            intro j _hj
            exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (IH' _) _) _) _
        · -- case `q ∤ n'`: `ν_p` gains `ν_p (q - 1)`
          have hval :=
            padicValNat_totient_mul_prime_of_not_dvd hp hq (by omega : n' ≠ 0) hcase
          rw [hnn', hval]
          have hid := powSum_mul_prime_of_not_dvd hn'2 hq hcase (k + 1)
          rw [sum_add_pow_eq] at hid
          have hqq : q ≤ q ^ (k + 1) := by
            calc q = q ^ 1 := (pow_one q).symm
              _ ≤ q ^ (k + 1) := Nat.pow_le_pow_right (by omega : 0 < q) (by omega)
          have hsplit : q ^ (k + 1) * powSum n' (k + 1) =
              (q ^ (k + 1) - q) * powSum n' (k + 1) + q * powSum n' (k + 1) := by
            rw [Nat.sub_mul, Nat.sub_add_cancel (Nat.mul_le_mul hqq le_rfl)]
          rw [hsplit, ← add_assoc, add_comm (q * powSum n' (k + 1))] at hid
          have hJ : powSum (n' * q) (k + 1) + (q ^ (k + 1) - q) * powSum n' (k + 1) =
              ∑ j ∈ Finset.range (k + 1), ((k + 1).choose (j + 1)) *
                (n' ^ (j + 1) * powSum n' (k + 1 - (j + 1)) *
                  ∑ h ∈ Finset.range q, h ^ (j + 1)) :=
            Nat.add_right_cancel hid
          have hdJ : p ^ (padicValNat p (Nat.totient n') + padicValNat p (q - 1)) ∣
              ∑ j ∈ Finset.range (k + 1), ((k + 1).choose (j + 1)) *
                (n' ^ (j + 1) * powSum n' (k + 1 - (j + 1)) *
                  ∑ h ∈ Finset.range q, h ^ (j + 1)) := by
            apply Finset.dvd_sum
            intro j _hj
            have hS := IH' (k + 1 - (j + 1))
            have hT : p ^ padicValNat p (q - 1) ∣
                n' ^ (j + 1) * ∑ h ∈ Finset.range q, h ^ (j + 1) := by
              rcases Nat.eq_zero_or_pos (padicValNat p (q - 1)) with h0 | h0
              · rw [h0, pow_zero]
                exact one_dvd _
              · have hc1 : 1 ≤ padicValNat p (q - 1) := h0
                have hd1 : p ^ 1 ∣ n' ^ (j + 1) := by
                  rw [pow_one]
                  exact dvd_pow hpn' (by omega : j + 1 ≠ 0)
                have hd2 : p ^ (padicValNat p (q - 1) - 1) ∣
                    ∑ h ∈ Finset.range q, h ^ (j + 1) := by
                  rw [sum_range_pow_eq_sum_Icc]
                  exact pow_pred_dvd_sum_pow_Icc hp _ hc1 (q - 1)
                    (pow_padicValNat_dvd' hp (by omega : q - 1 ≠ 0)) _ (by omega)
                have hadd : padicValNat p (q - 1) = 1 + (padicValNat p (q - 1) - 1) := by
                  omega
                rw [hadd, pow_add]
                exact mul_dvd_mul hd1 hd2
            have hdvd1 : p ^ (padicValNat p (Nat.totient n') + padicValNat p (q - 1)) ∣
                powSum n' (k + 1 - (j + 1)) *
                  (n' ^ (j + 1) * ∑ h ∈ Finset.range q, h ^ (j + 1)) :=
              (pow_add p _ _).symm ▸ mul_dvd_mul hS hT
            exact dvd_trans hdvd1 ⟨((k + 1).choose (j + 1)), by ring⟩
          have hdX : p ^ (padicValNat p (Nat.totient n') + padicValNat p (q - 1)) ∣
              (q ^ (k + 1) - q) * powSum n' (k + 1) := by
            have h1 : p ^ padicValNat p (q - 1) ∣ q ^ (k + 1) - q := by
              have hsub : q ^ (k + 1) - q = q * (q ^ k - 1) := by
                rw [Nat.mul_sub_left_distrib, mul_one, pow_succ, mul_comm]
              rw [hsub]
              have hd : q - 1 ∣ q ^ k - 1 := Nat.sub_one_dvd_pow_sub_one q k
              exact dvd_mul_of_dvd_right
                (dvd_trans (pow_padicValNat_dvd' hp (by omega : q - 1 ≠ 0)) hd) q
            exact dvd_trans ((pow_add p _ _).symm ▸ mul_dvd_mul (IH' (k + 1)) h1) ⟨1, by ring⟩
          have hA : powSum (n' * q) (k + 1) =
              (∑ j ∈ Finset.range (k + 1), ((k + 1).choose (j + 1)) *
                (n' ^ (j + 1) * powSum n' (k + 1 - (j + 1)) *
                  ∑ h ∈ Finset.range q, h ^ (j + 1))) -
                (q ^ (k + 1) - q) * powSum n' (k + 1) := by
            rw [← hJ]
            exact (Nat.add_sub_cancel _ _).symm
          rw [hA]
          exact Nat.dvd_sub hdJ hdX

snip end

problem usa2018_p3 (n : ℕ) (hn : 2 ≤ n) (k : ℕ) (_hk : 1 ≤ k)
    (h : ∀ p : ℕ, p.Prime → p ∣ n.totient → p ∣ n) :
    n.totient ∣ ∑ a ∈ (Finset.range n).filter (Nat.Coprime n), a ^ k := by
  have htot : n.totient ≠ 0 := (Nat.totient_pos.2 (by omega)).ne'
  have hS : powSum n k ≠ 0 := (powSum_pos n hn k).ne'
  show n.totient ∣ powSum n k
  rw [← Nat.factorization_prime_le_iff_dvd htot hS]
  intro q hq
  haveI := Fact.mk hq
  rw [Nat.factorization_def _ hq, Nat.factorization_def _ hq]
  by_cases hqd : q ∣ n.totient
  · have hqn : q ∣ n := h q hq hqd
    have hdvd := pow_padicValNat_totient_dvd_powSum hq n hn hqn k
    exact (padicValNat_dvd_iff_le hS).1 hdvd
  · rw [show padicValNat q n.totient = 0 from
      padicValNat.eq_zero_iff.2 (Or.inr (Or.inr hqd))]
    exact Nat.zero_le _

end Usa2018P3
