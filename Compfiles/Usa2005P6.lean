/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Data.Nat.Digits.Lemmas
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics, .NumberTheory] }

/-!
# USA Mathematical Olympiad 2005, Problem 6

For a positive integer m, let s(m) denote the sum of the decimal digits of m.
A set S of positive integers is k-stable if s(∑_{x∈X} x) = k for any nonempty
subset X ⊆ S. For each integer n ≥ 2 let f(n) be the minimal k for which there
exists a k-stable set with n integers. Prove that there are constants
0 < C₁ < C₂ with C₁ log₁₀ n ≤ f(n) ≤ C₂ log₁₀ n.
-/

namespace Usa2005P6

/-- The sum of the decimal digits of `m`. -/
def s (m : ℕ) : ℕ := (Nat.digits 10 m).sum

/-- A set `S` of positive integers is `k`-stable if the sum of the elements of
any nonempty subset `X ⊆ S` has digit sum equal to `k`. -/
def IsStable (k : ℕ) (S : Finset ℕ) : Prop :=
  (∀ x ∈ S, 0 < x) ∧ ∀ X ∈ S.powerset, X.Nonempty → s (∑ x ∈ X, x) = k

/-- `f n` is the minimal `k` for which there exists a `k`-stable set with `n`
integers. (That the defining set is nonempty is proved in `stable_exists`. -/
noncomputable def f (n : ℕ) : ℕ := sInf {k | ∃ S : Finset ℕ, IsStable k S ∧ S.card = n}

snip begin

/- ## Solution outline

*Upper bound (construction).* If `n * (n + 1) / 2 < 10 ^ e` then the set
`{10^e - 1, 2 * (10^e - 1), ..., n * (10^e - 1)}` is `9 * e`-stable: a nonempty
subset sum has the form `t * (10^e - 1) = (t - 1) * 10^e + (10^e - t)` with
`1 ≤ t ≤ n * (n+1) / 2 < 10 ^ e`, and the decimal digits of `t - 1` and
`10 ^ e - t` are complementary (they add to `10 ^ e - 1`, a string of nines),
so the digit sum is exactly `9 * e`.

*Lower bound.* Every set of `n` positive integers has a nonempty subset whose
sum has digit sum at least `9 * e` whenever `10 ^ e ≤ n + 1`: order the elements
arbitrarily and apply the pigeonhole principle to the `n + 1 ≥ 10 ^ e` prefix
sums modulo `10 ^ e - 1`. Two of them agree, their difference is a nonempty
consecutive-block sum divisible by `10 ^ e - 1`, and every positive multiple of
`10 ^ e - 1` has digit sum at least `9 * e`.

Combining the two bounds and estimating the natural logarithms gives
`(1/2) * log₁₀ n ≤ f n ≤ 48 * log₁₀ n` for all `n ≥ 2`.
-/

/-! ### Basic facts about the digit sum -/

@[simp]
lemma s_zero : s 0 = 0 := rfl

/-- The defining recurrence of the digit sum, valid for all `m`. -/
lemma s_eq (m : ℕ) : s m = m % 10 + s (m / 10) := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp [s]
  · rw [s, Nat.digits_of_two_le_of_pos (by norm_num) (Nat.pos_of_ne_zero hm), List.sum_cons, ← s]

/-- The digits of a concatenation are the concatenation of the digits:
if `c < 10 ^ e` then `s (10 ^ e * a + c) = s a + s c`. -/
lemma s_concat (e a c : ℕ) (hc : c < 10 ^ e) : s (10 ^ e * a + c) = s a + s c := by
  induction e generalizing a c with
  | zero =>
    simp only [pow_zero] at hc
    interval_cases c
    simp  | succ e ih =>
    have h10 : 10 ^ (e + 1) = 10 * 10 ^ e := by ring
    by_cases h : 10 ^ (e + 1) * a + c = 0
    · obtain ⟨ha0, hc0⟩ := Nat.add_eq_zero_iff.mp h
      have ha : a = 0 := by
        rcases (Nat.mul_eq_zero.mp ha0) with h1 | h1
        · exact absurd h1 (pow_ne_zero _ (by norm_num))
        · exact h1
      subst ha; subst hc0; simp [s_zero]
    · rw [s_eq]
      have h10a : 10 ^ (e + 1) * a = 10 * (10 ^ e * a) := by ring
      rw [h10a]
      have hmod : (10 * (10 ^ e * a) + c) % 10 = c % 10 := by omega
      have hdiv : (10 * (10 ^ e * a) + c) / 10 = 10 ^ e * a + c / 10 := by omega
      have hc' : c / 10 < 10 ^ e := by omega
      rw [hmod, hdiv, ih a (c / 10) hc', s_eq c]
      omega

/-- If `a + b = 10 ^ e - 1` then the digits of `a` and `b` are complementary,
so `s a + s b = 9 * e`. -/
lemma s_complement (e a b : ℕ) (h : a + b = 10 ^ e - 1) : s a + s b = 9 * e := by
  induction e generalizing a b with
  | zero =>
    simp only [pow_zero, Nat.sub_self] at h
    obtain rfl : a = 0 := by omega
    obtain rfl : b = 0 := by omega
    simp [s_zero]
  | succ e ih =>
    have h10 : 10 ^ (e + 1) = 10 * 10 ^ e := by ring
    have hpos : 1 ≤ 10 ^ e := Nat.one_le_pow _ _ (by norm_num)
    have key1 : a % 10 + b % 10 = 9 := by omega
    have key2 : a / 10 + b / 10 = 10 ^ e - 1 := by omega
    have := ih (a / 10) (b / 10) key2
    rw [s_eq a, s_eq b]
    omega

lemma s_pow_ten_sub_one (e : ℕ) : s (10 ^ e - 1) = 9 * e := by
  have h := s_complement e (10 ^ e - 1) 0 (by rw [add_zero])
  simpa [s_zero] using h

/-- Subadditivity of the digit sum. -/
lemma s_add_le (a b : ℕ) : s (a + b) ≤ s a + s b := by
  suffices h : ∀ N a b, a + b ≤ N → s (a + b) ≤ s a + s b from h _ a b le_rfl
  intro N
  induction N with
  | zero =>
    intro a b hab
    obtain rfl : a = 0 := by omega
    obtain rfl : b = 0 := by omega
    simp [s_zero]
  | succ N ih =>
    intro a b hab
    rcases eq_or_ne a 0 with rfl | ha
    · simp [s_zero]
    rcases eq_or_ne b 0 with rfl | hb
    · simp [s_zero]
    rw [s_eq (a + b)]
    by_cases hcarry : a % 10 + b % 10 < 10
    · have h1 : (a + b) % 10 = a % 10 + b % 10 := by omega
      have h2 : (a + b) / 10 = a / 10 + b / 10 := by omega
      have h3 : s (a / 10 + b / 10) ≤ s (a / 10) + s (b / 10) := ih _ _ (by omega)
      rw [h1, h2, s_eq a, s_eq b]
      omega
    · have h1 : (a + b) % 10 = a % 10 + b % 10 - 10 := by omega
      have h2 : (a + b) / 10 = a / 10 + b / 10 + 1 := by omega
      have h3 : s (a / 10 + b / 10 + 1) ≤ s (a / 10 + b / 10) + s 1 := ih _ _ (by omega)
      have h4 : s (a / 10 + b / 10) ≤ s (a / 10) + s (b / 10) := ih _ _ (by omega)
      have h5 : s 1 = 1 := by
        rw [s_eq]
        norm_num [s_zero]
      rw [h1, h2, s_eq a, s_eq b]
      omega

/-- The digit sum of a positive integer is positive. -/
lemma s_pos_of_pos (m : ℕ) (hm : 0 < m) : 1 ≤ s m := by
  have h1 : Nat.digits 10 m ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr (ne_of_gt hm)
  have h2 : (Nat.digits 10 m).getLast h1 ≠ 0 := Nat.getLast_digit_ne_zero 10 (ne_of_gt hm)
  rw [Nat.one_le_iff_ne_zero]
  intro hz
  rw [s, List.sum_eq_zero_iff_forall_eq_nat] at hz
  exact h2 (hz _ (List.getLast_mem h1))

/-- Every positive multiple of `10 ^ e - 1` has digit sum at least `9 * e`.
The proof repeatedly replaces `m` by `m % 10 ^ e + m / 10 ^ e`, which preserves
divisibility by `10 ^ e - 1` and does not increase the digit sum. -/
lemma nine_le_s_of_dvd (e : ℕ) (he : 1 ≤ e) :
    ∀ m : ℕ, 0 < m → (10 ^ e - 1) ∣ m → 9 * e ≤ s m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm hdvd
    have hP : 1 ≤ 10 ^ e := Nat.one_le_pow _ _ (by norm_num)
    have hP2 : 2 ≤ 10 ^ e := by
      calc 2 ≤ 10 ^ 1 := by norm_num
        _ ≤ 10 ^ e := Nat.pow_le_pow_right (by norm_num) he
    by_cases hlt : m < 10 ^ e
    · -- then `m = 10 ^ e - 1`
      obtain ⟨q, rfl⟩ := hdvd
      have hq : q = 1 := by
        rcases q with _ | q'
        · simp at hm
        · by_contra hq
          have hq2 : 2 ≤ q' + 1 := by omega
          have hle : (10 ^ e - 1) * 2 ≤ (10 ^ e - 1) * (q' + 1) := Nat.mul_le_mul le_rfl hq2
          omega
      rw [hq, mul_one]
      exact le_of_eq (s_pow_ten_sub_one e).symm
    · push Not at hlt
      -- recurse on `m' = m % 10 ^ e + m / 10 ^ e`
      have hdiv : 10 ^ e * (m / 10 ^ e) + m % 10 ^ e = m := Nat.div_add_mod m _
      have hq : 1 ≤ m / 10 ^ e := Nat.div_pos hlt (by omega)
      have hm'pos : 0 < m % 10 ^ e + m / 10 ^ e := by omega
      have hm'lt : m % 10 ^ e + m / 10 ^ e < m := by
        have hmul : 2 * (m / 10 ^ e) ≤ 10 ^ e * (m / 10 ^ e) := Nat.mul_le_mul hP2 le_rfl
        omega
      have hdvd' : 10 ^ e - 1 ∣ m % 10 ^ e + m / 10 ^ e := by
        obtain ⟨q, hqeq⟩ := hdvd
        have key : (10 ^ e - 1) * (m / 10 ^ e) = 10 ^ e * (m / 10 ^ e) - m / 10 ^ e := by
          rw [Nat.sub_mul, one_mul]
        refine ⟨q - m / 10 ^ e, ?_⟩
        rw [Nat.mul_sub]
        omega
      have ih' := ih _ hm'lt hm'pos hdvd'
      have hsm : s (m % 10 ^ e + m / 10 ^ e) ≤ s m := by
        have h1 := s_add_le (m % 10 ^ e) (m / 10 ^ e)
        have h2 : s m = s (m / 10 ^ e) + s (m % 10 ^ e) := by
          conv_lhs => rw [← Nat.div_add_mod m (10 ^ e)]
          rw [s_concat e (m / 10 ^ e) (m % 10 ^ e) (Nat.mod_lt _ (by omega))]
        omega
      omega

/-- The Gauss sum `1 + 2 + ... + n`. -/
lemma sum_Icc_id (n : ℕ) : ∑ i ∈ Finset.Icc 1 n, i = n * (n + 1) / 2 := by
  have key : (∑ i ∈ Finset.Icc 1 n, i) * 2 = n * (n + 1) := by
    induction n with
    | zero => simp
    | succ n ih =>
      have hinsert : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
        ext x
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      rw [hinsert, Finset.sum_insert (by simp), add_mul, ih]
      ring
  omega

/-- *Upper bound (construction).* If `n * (n + 1) / 2 < 10 ^ e` then
`{10^e - 1, 2 * (10^e - 1), ..., n * (10^e - 1)}` is a `9 * e`-stable set of
`n` positive integers. -/
lemma construction (n e : ℕ) (he : 1 ≤ e) (h : n * (n + 1) / 2 < 10 ^ e) :
    IsStable (9 * e) ((Finset.Icc 1 n).image (· * (10 ^ e - 1))) ∧
    ((Finset.Icc 1 n).image (· * (10 ^ e - 1))).card = n := by
  have hP : 1 ≤ 10 ^ e := Nat.one_le_pow _ _ (by norm_num)
  have hP10 : 10 ≤ 10 ^ e := by
    calc 10 = 10 ^ 1 := by norm_num
      _ ≤ 10 ^ e := Nat.pow_le_pow_right (by norm_num) he
  have hM : 0 < 10 ^ e - 1 := by omega
  have hinj : Function.Injective (· * (10 ^ e - 1)) :=
    fun _ _ hab => Nat.mul_right_cancel hM hab
  constructor
  · constructor
    · -- positivity of the elements
      intro x hx
      simp only [Finset.mem_image, Finset.mem_Icc] at hx
      obtain ⟨i, ⟨hi1, -⟩, rfl⟩ := hx
      exact Nat.mul_pos hi1 hM
    · -- stability
      intro X hX hXne
      rw [Finset.mem_powerset] at hX
      obtain ⟨I, hI, hIim⟩ := Finset.subset_image_iff.mp hX
      have hIne : I.Nonempty := by
        rcases I.eq_empty_or_nonempty with rfl | hne
        · simp only [Finset.image_empty] at hIim
          rw [← hIim] at hXne
          exact hXne
        · exact hne
      rw [← hIim, Finset.sum_image (fun x _ y _ hxy => hinj hxy), ← Finset.sum_mul]
      -- `t = ∑ i ∈ I, i` satisfies `1 ≤ t < 10 ^ e`
      have ht1 : 1 ≤ ∑ i ∈ I, i := by
        obtain ⟨i0, hi0⟩ := hIne
        have h1 : 1 ≤ i0 := (Finset.mem_Icc.mp (hI hi0)).1
        exact le_trans h1 (Finset.single_le_sum (fun i _ => Nat.zero_le i) hi0)
      have ht2 : ∑ i ∈ I, i ≤ n * (n + 1) / 2 := by
        rw [← sum_Icc_id n]
        exact Finset.sum_le_sum_of_subset hI
      have ht3 : ∑ i ∈ I, i < 10 ^ e := lt_of_le_of_lt ht2 h
      -- the digit computation
      have hsplit : (∑ i ∈ I, i) * (10 ^ e - 1)
          = 10 ^ e * ((∑ i ∈ I, i) - 1) + (10 ^ e - (∑ i ∈ I, i)) := by
        have e1 : (∑ i ∈ I, i) * (10 ^ e - 1) = (∑ i ∈ I, i) * 10 ^ e - (∑ i ∈ I, i) := by
          rw [Nat.mul_sub, mul_one]
        have e2 : 10 ^ e * ((∑ i ∈ I, i) - 1) = (∑ i ∈ I, i) * 10 ^ e - 10 ^ e := by
          rw [Nat.mul_sub, Nat.mul_one, Nat.mul_comm]
        have hiP : 10 ^ e ≤ (∑ i ∈ I, i) * 10 ^ e := by
          calc 10 ^ e = 1 * 10 ^ e := by ring
            _ ≤ (∑ i ∈ I, i) * 10 ^ e := Nat.mul_le_mul ht1 le_rfl
        rw [e1, e2]
        omega
      rw [hsplit, s_concat e ((∑ i ∈ I, i) - 1) (10 ^ e - (∑ i ∈ I, i)) (by omega)]
      exact s_complement e _ _ (by omega)
  · rw [Finset.card_image_of_injective _ hinj, Nat.card_Icc]
    omega

/-- *Lower bound.* If `S` is `k`-stable and `10 ^ e ≤ S.card + 1`, then
`9 * e ≤ k`: among the `S.card + 1 ≥ 10 ^ e` prefix sums of an arbitrary
ordering of `S`, two agree modulo `10 ^ e - 1`, and their difference is a
nonempty subset sum that is a positive multiple of `10 ^ e - 1`. -/
lemma stable_lower (k e : ℕ) (he : 1 ≤ e) (S : Finset ℕ) (hS : IsStable k S)
    (hn : 10 ^ e ≤ S.card + 1) : 9 * e ≤ k := by
  obtain ⟨hpos, hstab⟩ := hS
  have hP : 1 ≤ 10 ^ e := Nat.one_le_pow _ _ (by norm_num)
  have hM : 0 < 10 ^ e - 1 := by
    have h10 : 10 ≤ 10 ^ e := by
      calc 10 = 10 ^ 1 := by norm_num
        _ ≤ 10 ^ e := Nat.pow_le_pow_right (by norm_num) he
    omega
  -- work with the sorted list of `S`
  set l := S.sort (· ≤ ·) with hl
  have hln : l.Nodup := S.sort_nodup _
  have hll : l.length = S.card := S.length_sort _
  have hmem : ∀ x : ℕ, x ∈ l ↔ x ∈ S := fun _ => S.mem_sort _
  -- the prefix sums and the pigeonhole principle
  set p : ℕ → ℕ := fun j => (l.take j).sum with hp
  have hmaps : ∀ a ∈ Finset.range (S.card + 1),
      p a % (10 ^ e - 1) ∈ Finset.range (10 ^ e - 1) := by
    intro a _
    exact Finset.mem_range.mpr (Nat.mod_lt _ hM)
  have hcardlt : (Finset.range (10 ^ e - 1)).card < (Finset.range (S.card + 1)).card := by
    rw [Finset.card_range, Finset.card_range]
    omega
  obtain ⟨i, hi, j, hj, hij, hpij⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcardlt hmaps
  rw [Finset.mem_range] at hi hj
  -- the key claim: `i < j` with equal residues gives the desired subset
  have key : ∀ i j : ℕ, i ≤ S.card → j ≤ S.card → i < j →
      p i % (10 ^ e - 1) = p j % (10 ^ e - 1) → 9 * e ≤ k := by
    intro i j hi hj hltij hmod
    -- the slice `u = [a_i, ..., a_{j-1}]`
    set u := (l.drop i).take (j - i) with hu
    have hsub : List.Sublist u l := (List.take_sublist _ _).trans (List.drop_sublist _ _)
    have hunodup : u.Nodup := hln.sublist hsub
    have htake : l.take j = l.take i ++ u := by
      have h1 : (l.take j).take i ++ (l.take j).drop i = l.take j := List.take_append_drop _ _
      have h2 : (l.take j).take i = l.take i := by
        rw [List.take_take, min_eq_left (le_of_lt hltij)]
      have h3 : (l.take j).drop i = u := by
        rw [hu, List.take_drop, Nat.add_sub_cancel' (le_of_lt hltij)]
      rw [← h1, h2, h3]
    have hsum_split : p j = p i + u.sum := by
      show (l.take j).sum = (l.take i).sum + u.sum
      rw [htake, List.sum_append]
    have hulen : u.length = j - i := by
      rw [hu, List.length_take, List.length_drop, hll, min_eq_left (by omega)]
    have hune : u ≠ [] := by
      intro hz
      rw [hz, List.length_nil] at hulen
      omega
    have huS : ∀ x ∈ u, x ∈ S := fun x hx => (hmem x).mp (hsub.subset hx)
    have husum_pos : 0 < u.sum := List.sum_pos u (fun x hx => hpos x (huS x hx)) hune
    -- divisibility of the slice sum
    have hdvd : 10 ^ e - 1 ∣ u.sum := by
      have h1 : p i ≤ p j := by rw [hsum_split]; exact Nat.le_add_right _ _
      have h2 := (Nat.modEq_iff_dvd' h1).mp hmod
      rwa [show p j - p i = u.sum by omega] at h2
    -- the finset given by the slice
    have hXmem : u.toFinset ∈ S.powerset := by
      rw [Finset.mem_powerset]
      intro x hx
      rw [List.mem_toFinset] at hx
      exact huS x hx
    have hXne : u.toFinset.Nonempty := by
      obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil u hune
      exact ⟨x, List.mem_toFinset.mpr hx⟩
    have hsum_toFinset : ∑ x ∈ u.toFinset, x = u.sum := by
      have h2 := List.sum_toFinset (fun x => x) hunodup
      simpa using h2
    -- apply stability and the digit lemma
    have hA := nine_le_s_of_dvd e he u.sum husum_pos hdvd
    have hstab' := hstab u.toFinset hXmem hXne
    rw [hsum_toFinset] at hstab'
    omega
  -- resolve the trichotomy on `i` and `j`
  rcases lt_trichotomy i j with hlt | heq | hgt
  · exact key i j (by omega) (by omega) hlt hpij
  · exact absurd heq hij
  · exact key j i (by omega) (by omega) hgt hpij.symm

/-- The set defining `f n` is nonempty: the construction with
`e = Nat.log 10 (n * (n + 1) / 2) + 1` works. -/
lemma stable_exists (n : ℕ) :
    ∃ S : Finset ℕ, IsStable (9 * (Nat.log 10 (n * (n + 1) / 2) + 1)) S ∧ S.card = n := by
  refine ⟨_, construction n _ (by omega) ?_⟩
  have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 10) (n * (n + 1) / 2)
  rwa [Nat.succ_eq_add_one] at h

lemma f_spec (n : ℕ) : ∃ S : Finset ℕ, IsStable (f n) S ∧ S.card = n := by
  have h : sInf {k | ∃ S : Finset ℕ, IsStable k S ∧ S.card = n}
      ∈ {k | ∃ S : Finset ℕ, IsStable k S ∧ S.card = n} :=
    Nat.sInf_mem ⟨9 * (Nat.log 10 (n * (n + 1) / 2) + 1), stable_exists n⟩
  exact h

lemma f_le {n k : ℕ} (h : ∃ S : Finset ℕ, IsStable k S ∧ S.card = n) : f n ≤ k :=
  Nat.sInf_le (s := {k | ∃ S : Finset ℕ, IsStable k S ∧ S.card = n}) h

/-- Every stable set has stability constant at least `1`, hence `1 ≤ f n`. -/
lemma one_le_f (n : ℕ) (hn : 1 ≤ n) : 1 ≤ f n := by
  obtain ⟨S, ⟨hpos, hstab⟩, hcard⟩ := f_spec n
  have hne : S.Nonempty := by
    rw [← Finset.card_pos, hcard]
    omega
  have h1 := hstab S (Finset.mem_powerset.mpr (Finset.Subset.refl S)) hne
  have hsum : 0 < ∑ x ∈ S, x := Finset.sum_pos hpos hne
  have h2 : 1 ≤ s (∑ x ∈ S, x) := s_pos_of_pos _ hsum
  omega

/-- The lower bound for `f n` coming from the pigeonhole argument. -/
lemma f_lower (n e : ℕ) (he : 1 ≤ e) (hn : 10 ^ e ≤ n + 1) : 9 * e ≤ f n := by
  obtain ⟨S, hS, hcard⟩ := f_spec n
  exact stable_lower (f n) e he S hS (by rw [hcard]; exact hn)

/-- The upper bound for `f n` coming from the explicit construction. -/
lemma f_upper (n : ℕ) : f n ≤ 9 * (Nat.log 10 (n * (n + 1) / 2) + 1) :=
  Nat.sInf_le (s := {k | ∃ S : Finset ℕ, IsStable k S ∧ S.card = n}) (stable_exists n)

snip end

problem usa2005_p6 : ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ C₁ < C₂ ∧
    ∀ n : ℕ, 2 ≤ n → C₁ * Real.logb 10 n ≤ (f n : ℝ) ∧ (f n : ℝ) ≤ C₂ * Real.logb 10 n := by
  -- `log₁₀ 2 ≥ 3/10`, since `10 ^ (3/10) ≤ 2` (as `10³ = 1000 ≤ 1024 = 2¹⁰`)
  have hlog10_2 : (3 : ℝ) / 10 ≤ Real.logb 10 2 := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by norm_num)]
    by_contra hlt
    push Not at hlt
    have h1 : (2 : ℝ) ^ (10 : ℕ) < ((10 : ℝ) ^ ((3 : ℝ) / 10)) ^ (10 : ℕ) :=
      pow_lt_pow_left₀ hlt (by norm_num) (by norm_num)
    have h2 : ((10 : ℝ) ^ ((3 : ℝ) / 10)) ^ (10 : ℕ) = 1000 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 10)]
      norm_num [Real.rpow_natCast]
    rw [h2] at h1
    norm_num at h1
  have hlogb_self : Real.logb 10 10 = 1 := Real.logb_self_eq_one (by norm_num)
  have hlogb_100 : Real.logb 10 100 = 2 := by
    rw [show (100 : ℝ) = 10 ^ (2 : ℕ) by norm_num, Real.logb_pow, hlogb_self]
    norm_num
  refine ⟨1 / 2, 48, by norm_num, by norm_num, fun n hn => ?_⟩
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hLn2 : (3 : ℝ) / 10 ≤ Real.logb 10 n :=
    le_trans hlog10_2 (Real.logb_le_logb_of_le (by norm_num) (by norm_num) hn2)
  refine ⟨?_, ?_⟩
  · -- lower bound: `(1/2) * log₁₀ n ≤ f n`
    by_cases hn100 : n < 100
    · -- small `n`: `log₁₀ n ≤ 2` and `1 ≤ f n`
      have h1 : (1 : ℝ) ≤ (f n : ℝ) := by exact_mod_cast one_le_f n (by omega)
      have h2 : Real.logb 10 n ≤ 2 := by
        have hle : Real.logb 10 n ≤ Real.logb 10 100 :=
          Real.logb_le_logb_of_le (by norm_num) hn0 (by exact_mod_cast le_of_lt hn100)
        rw [hlogb_100] at hle
        exact hle
      linarith
    · -- large `n`: the pigeonhole bound
      push Not at hn100
      have h100 : (100 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn100
      have hL2 : 2 ≤ Real.logb 10 n := by
        have hle : Real.logb 10 100 ≤ Real.logb 10 n :=
          Real.logb_le_logb_of_le (by norm_num) (by norm_num) h100
        rw [hlogb_100] at hle
        exact hle
      have he1 : 1 ≤ Nat.log 10 (n + 1) :=
        Nat.le_log_of_pow_le (by norm_num) (by omega)
      have hnat : 9 * Nat.log 10 (n + 1) ≤ f n :=
        f_lower n _ he1 (Nat.pow_log_le_self 10 (by omega))
      have hr1 : (9 : ℝ) * (Nat.log 10 (n + 1) : ℝ) ≤ (f n : ℝ) := by exact_mod_cast hnat
      -- `Nat.log 10 (n+1) + 1 > log₁₀ (n+1) ≥ log₁₀ n`
      have hlt : ((n + 1 : ℕ) : ℝ) < ((10 ^ (Nat.log 10 (n + 1) + 1) : ℕ) : ℝ) := by
        have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 10) (n + 1)
        rw [Nat.succ_eq_add_one] at h
        exact_mod_cast h
      have hlog_lt : Real.logb 10 ((n : ℝ) + 1) < (Nat.log 10 (n + 1) : ℝ) + 1 := by
        push_cast at hlt
        have h2 : Real.logb 10 ((n : ℝ) + 1)
            < Real.logb 10 ((10 : ℝ) ^ (Nat.log 10 (n + 1) + 1 : ℕ)) :=
          Real.logb_lt_logb (by norm_num) (by positivity) hlt
        rw [Real.logb_pow, hlogb_self, mul_one] at h2
        push_cast at h2
        exact h2
      have hlog_le : Real.logb 10 n ≤ Real.logb 10 ((n : ℝ) + 1) :=
        Real.logb_le_logb_of_le (by norm_num) hn0 (by linarith)
      have hfin : (9 : ℝ) * (Real.logb 10 n - 1) < (f n : ℝ) := by linarith
      linarith
  · -- upper bound: `f n ≤ 48 * log₁₀ n`
    have hnat := f_upper n
    have hr1 : (f n : ℝ) ≤ 9 * ((Nat.log 10 (n * (n + 1) / 2) : ℝ) + 1) := by
      exact_mod_cast hnat
    have hm0 : n * (n + 1) / 2 ≠ 0 := by
      have h6 : 2 * 3 ≤ n * (n + 1) := Nat.mul_le_mul hn (show 3 ≤ n + 1 by omega)
      omega
    -- `Nat.log 10 m ≤ log₁₀ m` for `m = n * (n+1)/2`
    have hlog1 : (Nat.log 10 (n * (n + 1) / 2) : ℝ) ≤ Real.logb 10 (↑(n * (n + 1) / 2)) := by
      have h1 : (10 : ℝ) ^ (Nat.log 10 (n * (n + 1) / 2)) ≤ ((n * (n + 1) / 2 : ℕ) : ℝ) := by
        exact_mod_cast Nat.pow_log_le_self 10 hm0
      have h2 : Real.logb 10 ((10 : ℝ) ^ (Nat.log 10 (n * (n + 1) / 2) : ℕ))
          = (Nat.log 10 (n * (n + 1) / 2) : ℝ) := by
        rw [Real.logb_pow, hlogb_self, mul_one]
      rw [← h2]
      exact Real.logb_le_logb_of_le (by norm_num) (by positivity) h1
    -- `log₁₀ m ≤ log₁₀ (n²) = 2 log₁₀ n`
    have hlog2 : Real.logb 10 (↑(n * (n + 1) / 2)) ≤ 2 * Real.logb 10 n := by
      have hmn : ((n * (n + 1) / 2 : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 := by
        have hstep : ((n * (n + 1) / 2 : ℕ) : ℝ) ≤ ((n * (n + 1) : ℕ) : ℝ) / 2 :=
          Nat.cast_div_le
        push_cast at hstep
        nlinarith [hstep, hn2]
      have h3 : Real.logb 10 (↑(n * (n + 1) / 2)) ≤ Real.logb 10 ((n : ℝ) ^ 2) :=
        Real.logb_le_logb_of_le (by norm_num)
          (by exact_mod_cast Nat.pos_of_ne_zero hm0) hmn
      rw [Real.logb_pow] at h3
      norm_num at h3
      exact h3
    have hfin : (f n : ℝ) ≤ 9 * (2 * Real.logb 10 n + 1) := by linarith
    linarith
