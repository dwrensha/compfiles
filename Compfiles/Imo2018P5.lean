/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Tactic
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.NumberTheory] }

/-!
# International Mathematical Olympiad 2018, Problem 5

Let a₁, a₂, ... be an infinite sequence of positive integers.
Suppose that there is an integer N > 1 such that for each n ≥ N
the number

   a₁/a₂ + a₂/a₃ ... + aₙ₋₁/aₙ + aₙ/a₁

is an integer. Prove that there is a positive integer M such that
aₘ = aₘ₊₁ for all m ≥ M.
-/

namespace Imo2018P5

snip begin

/- The sum `a₀/a₁ + a₁/a₂ + ... + aₙ₋₁/a₀` of the problem statement. -/
def S (a : ℕ → ℤ) (n : ℕ) : ℚ := ∑ i ∈ Finset.range n, (a i : ℚ) / a ((i + 1) % n)

/- Difference of two consecutive sums: for `n ≥ 1`,
`S (n+1) - S n = aₙ₋₁/aₙ + (aₙ - aₙ₋₁)/a₀`. -/
lemma S_sub (a : ℕ → ℤ) (n : ℕ) (hn : 1 ≤ n) :
    S a (n + 1) - S a n = (a (n - 1) : ℚ) / a n + ((a n : ℚ) - a (n - 1)) / a 0 := by
  have h1 : S a (n + 1) = (∑ i ∈ Finset.range n, (a i : ℚ) / a (i + 1)) + (a n : ℚ) / a 0 := by
    unfold S
    rw [Finset.sum_range_succ]
    congr 1
    · apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mem_range] at hi
      rw [Nat.mod_eq_of_lt (by omega : i + 1 < n + 1)]
    · rw [Nat.mod_self]
  have h2 : S a n = (∑ i ∈ Finset.range (n - 1), (a i : ℚ) / a (i + 1)) + (a (n - 1) : ℚ) / a 0 := by
    unfold S
    conv_lhs => rw [← Nat.sub_add_cancel hn]
    rw [Finset.sum_range_succ]
    congr 1
    · apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mem_range] at hi
      rw [Nat.mod_eq_of_lt (by omega : i + 1 < n - 1 + 1)]
    · rw [Nat.mod_self]
  have h3 : ∑ i ∈ Finset.range n, (a i : ℚ) / a (i + 1) =
      (∑ i ∈ Finset.range (n - 1), (a i : ℚ) / a (i + 1)) + (a (n - 1) : ℚ) / a n := by
    conv_lhs => rw [← Nat.sub_add_cancel hn]
    rw [Finset.sum_range_succ, Nat.sub_add_cancel hn]
  rw [h1, h2, h3]
  ring

/- The key per-step relation. If `S n` and `S (n+1)` are both integers, then there is an
integer `k` (namely `a₀·aₙ₋₁/aₙ`) with `aₙ * k = a₀ * aₙ₋₁` and `a₀ ∣ k + aₙ - aₙ₋₁`. -/
lemma step (a : ℕ → ℤ) (apos : ∀ n, 0 < a n) (N : ℕ)
    (h : ∀ n, N ≤ n → ∃ z : ℤ, z = S a n) {n : ℕ} (hn : N ≤ n) (hn1 : 1 ≤ n) :
    ∃ k : ℤ, a n * k = a 0 * a (n - 1) ∧ a 0 ∣ k + a n - a (n - 1) := by
  obtain ⟨z₁, hz₁⟩ := h n hn
  obtain ⟨z₂, hz₂⟩ := h (n + 1) (by omega)
  have hsum := S_sub a n hn1
  rw [← hz₁, ← hz₂] at hsum
  refine ⟨a 0 * (z₂ - z₁) - (a n - a (n - 1)), ?_, ?_⟩
  · have hcast : ((a n * (a 0 * (z₂ - z₁) - (a n - a (n - 1)))) : ℤ) = ((a 0 * a (n - 1) : ℤ) : ℚ) := by
      push_cast
      rw [show ((z₂ : ℚ) - (z₁ : ℚ)) = (a (n - 1) : ℚ) / a n + ((a n : ℚ) - a (n - 1)) / a 0 from hsum]
      have hann : (a n : ℚ) ≠ 0 := by exact_mod_cast (apos n).ne'
      have ha0 : (a 0 : ℚ) ≠ 0 := by exact_mod_cast (apos 0).ne'
      field_simp
      ring
    exact_mod_cast hcast
  · rw [show a 0 * (z₂ - z₁) - (a n - a (n - 1)) + a n - a (n - 1) = a 0 * (z₂ - z₁) from by ring]
    exact Dvd.intro _ rfl

/- The valuation rule. For a prime `p`, write `α, κ, V, V'` for the `p`-adic valuations of
`a₀, k, aₙ₋₁, aₙ` respectively, where `k` comes from `step`. Then:
`κ < α` forces `V = κ` and `V' = α`; `κ = α` forces `V' = V`; `α < κ` forces `α ≤ V' < V`. -/
lemma val_rule (a : ℕ → ℤ) (apos : ∀ n, 0 < a n) {p : ℕ} (hp : p.Prime)
    {n : ℕ} {k : ℤ} (hk1 : a n * k = a 0 * a (n - 1)) (hk2 : a 0 ∣ k + a n - a (n - 1)) :
    (padicValInt p k < padicValInt p (a 0) →
        padicValInt p (a (n - 1)) = padicValInt p k ∧ padicValInt p (a n) = padicValInt p (a 0)) ∧
    (padicValInt p k = padicValInt p (a 0) → padicValInt p (a n) = padicValInt p (a (n - 1))) ∧
    (padicValInt p (a 0) < padicValInt p k →
        padicValInt p (a n) < padicValInt p (a (n - 1)) ∧
        padicValInt p (a 0) ≤ padicValInt p (a n)) := by
  have : Fact p.Prime := ⟨hp⟩
  set α := padicValInt p (a 0) with hα
  set κ := padicValInt p k with hκ
  set V := padicValInt p (a (n - 1)) with hV
  set V' := padicValInt p (a n) with hV'
  have ha0 : a 0 ≠ 0 := (apos 0).ne'
  have han : a n ≠ 0 := (apos n).ne'
  have han1 : a (n - 1) ≠ 0 := (apos (n - 1)).ne'
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hk1
    exact (mul_ne_zero ha0 han1) hk1.symm
  have hE : V' + κ = α + V := by
    have h := congrArg (padicValInt p) hk1
    rw [padicValInt.mul han hk0, padicValInt.mul ha0 han1] at h
    exact h
  -- the difference `k + a n - a (n-1)` is divisible by `a 0`, hence by `p^α`
  have hD : (p : ℤ) ^ α ∣ k + a n - a (n - 1) := dvd_trans (padicValInt_dvd (a 0)) hk2
  have hvD : k + a n - a (n - 1) ≠ 0 → α ≤ padicValInt p (k + a n - a (n - 1)) := by
    intro hD0
    exact ((padicValInt_dvd_iff α (k + a n - a (n - 1))).mp hD).resolve_left hD0
  -- coerced valuations of the difference `a (n-1) - a n`, assuming `V ≠ V'`
  have hdiff : V ≠ V' → padicValRat p ((a (n - 1) : ℚ) - (a n : ℚ)) = min V V' := by
    intro hne
    have hne2 : (a (n - 1) : ℚ) + -(a n : ℚ) ≠ 0 := by
      rw [← sub_eq_add_neg]
      intro hz
      apply hne
      have : a (n - 1) = a n := by exact_mod_cast sub_eq_zero.mp hz
      rw [hV, hV', this]
    have h1 : padicValRat p (a (n - 1) : ℚ) = V := by simp [hV]
    have h2 : padicValRat p (a n : ℚ) = V' := by simp [hV']
    have h3 : padicValRat p (a (n - 1) : ℚ) ≠ padicValRat p (-(a n : ℚ)) := by
      rw [padicValRat.neg, h1, h2]
      exact_mod_cast hne
    have hrw := padicValRat.add_eq_min hne2 (by exact_mod_cast han1)
      (neg_ne_zero.mpr (by exact_mod_cast han)) h3
    rw [padicValRat.neg, h1, h2] at hrw
    rw [sub_eq_add_neg, Nat.cast_min]
    exact hrw
  have hdiff_int : V ≠ V' → padicValInt p (a (n - 1) - a n) = min V V' := by
    intro hne
    have h := hdiff hne
    rw [← Int.cast_sub, padicValRat.of_int] at h
    exact_mod_cast h
  refine ⟨?_, ?_, ?_⟩
  · -- case `κ < α`
    intro hlt
    have hVV : V < V' := by omega
    have hne : V ≠ V' := by omega
    rw [min_eq_left (by omega)] at hdiff_int
    have hkV : κ = V := by
      by_cases hD0 : k + a n - a (n - 1) = 0
      · have hke : k = a (n - 1) - a n := by omega
        rw [hκ, hke]
        exact hdiff_int hne
      · have hvD' := hvD hD0
        have hkDE : (k : ℚ) = ((k + a n - a (n - 1) : ℤ) : ℚ) + ((a (n - 1) - a n : ℤ) : ℚ) := by
          push_cast; ring
        have hqD : padicValRat p ((k + a n - a (n - 1) : ℤ) : ℚ) =
            padicValInt p (k + a n - a (n - 1)) := padicValRat.of_int
        have hqE : padicValRat p ((a (n - 1) - a n : ℤ) : ℚ) = V := by
          rw [padicValRat.of_int]; exact_mod_cast hdiff_int hne
        have hkne : ((k + a n - a (n - 1) : ℤ) : ℚ) + ((a (n - 1) - a n : ℤ) : ℚ) ≠ 0 := by
          rw [← hkDE]; exact_mod_cast hk0
        by_cases hcase : padicValInt p (k + a n - a (n - 1)) = V
        · have hge := padicValRat.min_le_padicValRat_add (p := p) hkne
          rw [hqD, hqE, hcase, ← hkDE, padicValRat.of_int, ← hκ] at hge
          omega
        · have heq := padicValRat.add_eq_min (p := p) hkne (by exact_mod_cast hD0)
            (by exact_mod_cast sub_ne_zero.mpr (by
              intro he
              apply hne
              rw [hV, hV', he])) (by rw [hqD, hqE]; exact_mod_cast hcase)
          rw [hqD, hqE, ← hkDE, padicValRat.of_int, ← hκ] at heq
          omega
    exact ⟨hkV.symm, by omega⟩
  · -- case `κ = α`
    intro heq
    omega
  · -- case `α < κ`
    intro hgt
    have hVV : V' < V := by omega
    have hne : V ≠ V' := by omega
    rw [min_eq_right (by omega)] at hdiff_int
    have hV'α : α ≤ V' := by
      by_cases hD0 : k + a n - a (n - 1) = 0
      · have hke : a (n - 1) - a n = k := by omega
        have : padicValInt p (a (n - 1) - a n) = κ := by rw [hke, hκ]
        rw [hdiff_int hne] at this
        omega
      · have hvD' := hvD hD0
        have hDE : ((a (n - 1) - a n : ℤ) : ℚ) =
            (k : ℚ) - ((k + a n - a (n - 1) : ℤ) : ℚ) := by push_cast; ring
        have hqD : padicValRat p ((k + a n - a (n - 1) : ℤ) : ℚ) =
            padicValInt p (k + a n - a (n - 1)) := padicValRat.of_int
        have hqk : padicValRat p (k : ℚ) = κ := padicValRat.of_int
        have hne3 : (k : ℚ) - ((k + a n - a (n - 1) : ℤ) : ℚ) ≠ 0 := by
          rw [← hDE]
          exact_mod_cast sub_ne_zero.mpr (by
            intro he
            apply hne
            rw [hV, hV', he])
        have hge := padicValRat.min_le_padicValRat_add (p := p) (q := (k : ℚ))
          (r := -((k + a n - a (n - 1) : ℤ) : ℚ)) (by rwa [sub_eq_add_neg] at hne3)
        rw [padicValRat.neg, hqD, hqk] at hge
        rw [show (k : ℚ) + -((k + a n - a (n - 1) : ℤ) : ℚ) = ((a (n - 1) - a n : ℤ) : ℚ) from by
          push_cast; ring] at hge
        rw [padicValRat.of_int, hdiff_int hne] at hge
        have hmin : α ≤ min κ (padicValInt p (k + a n - a (n - 1))) := le_min (by omega) hvD'
        have hge' : min κ (padicValInt p (k + a n - a (n - 1))) ≤ V' := by exact_mod_cast hge
        exact le_trans hmin hge'
    exact ⟨by omega, hV'α⟩

/- Boundedness: for `n ≥ N - 1` and every prime `p`,
`v_p(aₙ) ≤ v_p(a₀) + v_p(a_{N-1})`, proved by induction using `val_rule`. -/
lemma bound (a : ℕ → ℤ) (apos : ∀ n, 0 < a n) (N : ℕ) (hN : 0 < N)
    (h : ∀ n, N ≤ n → ∃ z : ℤ, z = S a n)
    (n : ℕ) (hn : N - 1 ≤ n) (p : ℕ) (hp : p.Prime) :
    padicValInt p (a n) ≤ padicValInt p (a 0) + padicValInt p (a (N - 1)) := by
  induction n, hn using Nat.le_induction with
  | base => exact Nat.le_add_left _ _
  | succ n hn ih =>
    obtain ⟨k, hk1, hk2⟩ := step a apos N h (n := n + 1) (by omega) (by omega)
    obtain ⟨c1, c2, c3⟩ := val_rule a apos hp hk1 hk2
    rw [show n + 1 - 1 = n from by omega] at c1 c2 c3
    rcases lt_trichotomy (padicValInt p k) (padicValInt p (a 0)) with hlt | heq | hgt
    · obtain ⟨-, e2⟩ := c1 hlt
      rw [e2]
      exact Nat.le_add_right _ _
    · rw [c2 heq]
      exact ih
    · obtain ⟨g1, -⟩ := c3 hgt
      omega

/- Divisibility form of the bound: `aₙ ∣ a₀ · a_{N-1}` for `n ≥ N - 1`. -/
lemma dvd_bound (a : ℕ → ℤ) (apos : ∀ n, 0 < a n) (N : ℕ) (hN : 0 < N)
    (h : ∀ n, N ≤ n → ∃ z : ℤ, z = S a n) (n : ℕ) (hn : N - 1 ≤ n) :
    a n ∣ a 0 * a (N - 1) := by
  have key : (a n).natAbs ∣ (a 0 * a (N - 1)).natAbs := by
    rw [Int.natAbs_mul]
    rw [← Nat.factorization_le_iff_dvd (Int.natAbs_ne_zero.mpr (apos n).ne')
      (mul_ne_zero (Int.natAbs_ne_zero.mpr (apos 0).ne') (Int.natAbs_ne_zero.mpr (apos (N - 1)).ne'))]
    intro p
    by_cases hp : p.Prime
    · rw [Nat.factorization_mul (Int.natAbs_ne_zero.mpr (apos 0).ne')
        (Int.natAbs_ne_zero.mpr (apos (N - 1)).ne'), Finsupp.add_apply,
        Nat.factorization_def _ hp, Nat.factorization_def _ hp, Nat.factorization_def _ hp]
      exact bound a apos N hN h n hn p hp
    · rw [Nat.factorization_eq_zero_of_not_prime _ hp,
        Nat.factorization_eq_zero_of_not_prime _ hp]
  have e1 : ((a n).natAbs : ℤ) = a n := Int.natAbs_of_nonneg (apos n).le
  have e2 : (((a 0 * a (N - 1)).natAbs) : ℤ) = a 0 * a (N - 1) :=
    Int.natAbs_of_nonneg (mul_pos (apos 0) (apos _)).le
  rw [← e1, ← e2]
  exact Int.ofNat_dvd.mpr key

/- No closed walk. If the sequence returns to the same value (`a n₁ = a n₂` with `n₁ < n₂`,
`N ≤ n₁`), then it was constant on the whole interval `[n₁, n₂]`. -/
lemma walk_const (a : ℕ → ℤ) (apos : ∀ n, 0 < a n) (N : ℕ) (hN : 0 < N)
    (h : ∀ n, N ≤ n → ∃ z : ℤ, z = S a n)
    {n₁ n₂ : ℕ} (hn₁ : N ≤ n₁) (hlt : n₁ < n₂) (heq : a n₁ = a n₂)
    (j : ℕ) (hj1 : n₁ ≤ j) (hj2 : j ≤ n₂) : a j = a n₁ := by
  -- choose multipliers `kᵢ` on each step of the walk
  have hkk : ∀ i, ∃ k : ℤ, i ∈ Finset.Ioc n₁ n₂ →
      a i * k = a 0 * a (i - 1) ∧ a 0 ∣ k + a i - a (i - 1) := by
    intro i
    by_cases hi : i ∈ Finset.Ioc n₁ n₂
    · have hi' := Finset.mem_Ioc.mp hi
      obtain ⟨k, hk1, hk2⟩ := step a apos N h (n := i) (by omega) (by omega)
      exact ⟨k, fun _ => ⟨hk1, hk2⟩⟩
    · exact ⟨1, fun h' => absurd h' hi⟩
  choose! kk hkk using hkk
  -- for every prime `p`, every multiplier of the walk has valuation `v_p(a₀)`
  have hkappa : ∀ p : ℕ, p.Prime → ∀ i ∈ Finset.Ioc n₁ n₂,
      padicValInt p (kk i) = padicValInt p (a 0) := by
    intro p hp
    -- one-step propagation of `α ≤ Vᵢ` along the walk
    have F : ∀ i ∈ Finset.Ioc n₁ n₂, padicValInt p (a 0) ≤ padicValInt p (a (i - 1)) →
        padicValInt p (a 0) ≤ padicValInt p (a i) := by
      intro i hi hprev
      obtain ⟨hk1, hk2⟩ := hkk i hi
      obtain ⟨c1, c2, c3⟩ := val_rule a apos hp hk1 hk2
      rcases lt_trichotomy (padicValInt p (kk i)) (padicValInt p (a 0)) with hlt | heq | hgt
      · obtain ⟨e1, -⟩ := c1 hlt
        omega
      · rw [c2 heq]; exact hprev
      · exact (c3 hgt).2
    have Fgen : ∀ s ∈ Finset.Icc n₁ n₂, padicValInt p (a 0) ≤ padicValInt p (a s) →
        ∀ m, s + m ≤ n₂ → padicValInt p (a 0) ≤ padicValInt p (a (s + m)) := by
      intro s hs hα m
      induction m with
      | zero => intro _; exact hα
      | succ m ihm =>
        intro hm
        have hmem : s + (m + 1) ∈ Finset.Ioc n₁ n₂ := by
          have := Finset.mem_Icc.mp hs
          rw [Finset.mem_Ioc]
          omega
        have hprev : padicValInt p (a 0) ≤ padicValInt p (a (s + (m + 1) - 1)) := by
          rw [show s + (m + 1) - 1 = s + m from by omega]
          exact ihm (by omega)
        exact F (s + (m + 1)) hmem hprev
    -- dichotomy: either all valuations are `≥ α`, or all are `< α`
    have hsplit : (∀ i ∈ Finset.Icc n₁ n₂, padicValInt p (a 0) ≤ padicValInt p (a i)) ∨
        (∀ i ∈ Finset.Icc n₁ n₂, padicValInt p (a i) < padicValInt p (a 0)) := by
      by_cases hall : ∀ i ∈ Finset.Icc n₁ n₂, padicValInt p (a 0) ≤ padicValInt p (a i)
      · exact Or.inl hall
      · right
        push Not at hall
        obtain ⟨j₁, hj₁mem, hj₁⟩ := hall
        intro i himem
        by_contra hcon
        push Not at hcon
        have h1 : padicValInt p (a 0) ≤ padicValInt p (a n₂) := by
          have hgi := Fgen i himem hcon (n₂ - i) (by have := Finset.mem_Icc.mp himem; omega)
          rwa [show i + (n₂ - i) = n₂ from by have := Finset.mem_Icc.mp himem; omega] at hgi
        have h2 : padicValInt p (a 0) ≤ padicValInt p (a n₁) := by rwa [← heq] at h1
        have h3 : padicValInt p (a 0) ≤ padicValInt p (a j₁) := by
          have hgi := Fgen n₁ (by rw [Finset.mem_Icc]; omega) h2 (j₁ - n₁)
            (by have := Finset.mem_Icc.mp hj₁mem; omega)
          rwa [show n₁ + (j₁ - n₁) = j₁ from by have := Finset.mem_Icc.mp hj₁mem; omega] at hgi
        omega
    rcases hsplit with hall | hall
    · -- all `≥ α`: the valuations are all equal, hence `κᵢ = α`
      have T : ∀ i ∈ Finset.Ioc n₁ n₂, padicValInt p (a i) ≤ padicValInt p (a (i - 1)) := by
        intro i hi
        obtain ⟨hk1, hk2⟩ := hkk i hi
        obtain ⟨c1, c2, c3⟩ := val_rule a apos hp hk1 hk2
        rcases lt_trichotomy (padicValInt p (kk i)) (padicValInt p (a 0)) with hlt | heq | hgt
        · obtain ⟨e1, -⟩ := c1 hlt
          have := hall (i - 1) (by have := Finset.mem_Ioc.mp hi; rw [Finset.mem_Icc]; omega)
          omega
        · rw [c2 heq]
        · exact (c3 hgt).1.le
      have hupper : ∀ m, n₁ + m ≤ n₂ → padicValInt p (a (n₁ + m)) ≤ padicValInt p (a n₁) := by
        intro m
        induction m with
        | zero => intro _; exact le_rfl
        | succ m ihm =>
          intro hm
          have hmem : n₁ + (m + 1) ∈ Finset.Ioc n₁ n₂ := by rw [Finset.mem_Ioc]; omega
          have hle := T (n₁ + (m + 1)) hmem
          rw [show n₁ + (m + 1) - 1 = n₁ + m from by omega] at hle
          exact le_trans hle (ihm (by omega))
      have hlower : ∀ m, n₁ ≤ n₂ - m → padicValInt p (a n₂) ≤ padicValInt p (a (n₂ - m)) := by
        intro m
        induction m with
        | zero => intro _; exact le_rfl
        | succ m ihm =>
          intro hm
          have hmem : n₂ - m ∈ Finset.Ioc n₁ n₂ := by rw [Finset.mem_Ioc]; omega
          have hle := T (n₂ - m) hmem
          rw [show n₂ - m - 1 = n₂ - (m + 1) from by omega] at hle
          exact le_trans (ihm (by omega)) hle
      have hVeq : ∀ i ∈ Finset.Icc n₁ n₂, padicValInt p (a i) = padicValInt p (a n₁) := by
        intro i hi
        rw [Finset.mem_Icc] at hi
        have hu := hupper (i - n₁) (by omega)
        rw [show n₁ + (i - n₁) = i from by omega] at hu
        have hl := hlower (n₂ - i) (by omega)
        rw [show n₂ - (n₂ - i) = i from by omega] at hl
        rw [← heq] at hl
        exact le_antisymm hu hl
      intro i hi
      obtain ⟨hk1, hk2⟩ := hkk i hi
      obtain ⟨c1, c2, c3⟩ := val_rule a apos hp hk1 hk2
      rcases lt_trichotomy (padicValInt p (kk i)) (padicValInt p (a 0)) with hlt | heq | hgt
      · obtain ⟨e1, -⟩ := c1 hlt
        have hge := hall (i - 1) (by have := Finset.mem_Ioc.mp hi; rw [Finset.mem_Icc]; omega)
        omega
      · exact heq
      · obtain ⟨g1, -⟩ := c3 hgt
        have e1 := hVeq i (by have := Finset.mem_Ioc.mp hi; rw [Finset.mem_Icc]; omega)
        have e2 := hVeq (i - 1) (by have := Finset.mem_Ioc.mp hi; rw [Finset.mem_Icc]; omega)
        omega
    · -- all `< α`: the rule immediately forces `κᵢ = α`
      intro i hi
      obtain ⟨hk1, hk2⟩ := hkk i hi
      obtain ⟨c1, c2, c3⟩ := val_rule a apos hp hk1 hk2
      rcases lt_trichotomy (padicValInt p (kk i)) (padicValInt p (a 0)) with hlt | heq | hgt
      · obtain ⟨-, e2⟩ := c1 hlt
        have hlt' := hall i (by have := Finset.mem_Ioc.mp hi; rw [Finset.mem_Icc]; omega)
        omega
      · exact heq
      · obtain ⟨-, g2⟩ := c3 hgt
        have hlt' := hall i (by have := Finset.mem_Ioc.mp hi; rw [Finset.mem_Icc]; omega)
        omega
  -- hence every multiplier equals `a 0`
  have hkk_eq : ∀ i ∈ Finset.Ioc n₁ n₂, kk i = a 0 := by
    intro i hi
    have hpos_k : 0 < kk i := by
      obtain ⟨hk1, -⟩ := hkk i hi
      exact pos_of_mul_pos_right (by rw [hk1]; exact mul_pos (apos 0) (apos _)) (apos i).le
    have hfac : (kk i).natAbs = (a 0).natAbs := by
      apply Nat.eq_of_factorization_eq (Int.natAbs_ne_zero.mpr hpos_k.ne')
        (Int.natAbs_ne_zero.mpr (apos 0).ne')
      intro p
      by_cases hp : p.Prime
      · rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp]
        exact hkappa p hp i hi
      · rw [Nat.factorization_eq_zero_of_not_prime _ hp, Nat.factorization_eq_zero_of_not_prime _ hp]
    have e1 : ((kk i).natAbs : ℤ) = kk i := Int.natAbs_of_nonneg hpos_k.le
    have e2 : ((a 0).natAbs : ℤ) = a 0 := Int.natAbs_of_nonneg (apos 0).le
    rw [← e1, ← e2, hfac]
  -- therefore every step is a stay
  have hstay : ∀ i ∈ Finset.Ioc n₁ n₂, a i = a (i - 1) := by
    intro i hi
    obtain ⟨hk1, -⟩ := hkk i hi
    rw [hkk_eq i hi, mul_comm (a i) (a 0)] at hk1
    exact mul_left_cancel₀ (apos 0).ne' hk1
  -- and the sequence is constant on the walk
  have hfinal : ∀ m, n₁ + m ≤ n₂ → a (n₁ + m) = a n₁ := by
    intro m
    induction m with
    | zero => intro _; rfl
    | succ m ihm =>
      intro hm
      have hmem : n₁ + (m + 1) ∈ Finset.Ioc n₁ n₂ := by rw [Finset.mem_Ioc]; omega
      have hst := hstay (n₁ + (m + 1)) hmem
      rw [show n₁ + (m + 1) - 1 = n₁ + m from by omega] at hst
      rw [hst]
      exact ihm (by omega)
  have := hfinal (j - n₁) (by omega)
  rwa [show n₁ + (j - n₁) = j from by omega] at this

snip end

problem imo2018_p5
    (a : ℕ → ℤ)
    (apos : ∀ n, 0 < a n)
    (N : ℕ)
    (hN : 0 < N)
    (h : ∀ n, N ≤ n →
      ∃ z : ℤ,
        z = ∑ i ∈ Finset.range n, (a i : ℚ) / a ((i + 1) % n))
    : ∃ M, ∀ m, M ≤ m → a m = a (m + 1) := by
  have hS : ∀ n, N ≤ n → ∃ z : ℤ, z = S a n := fun n hn => h n hn
  by_contra hnc
  push Not at hnc
  -- the bound `C`
  set C := a 0 * a (N - 1) with hC
  have hCpos : 0 < C := mul_pos (apos 0) (apos _)
  -- values are bounded for `n ≥ N - 1`
  have hmem : ∀ n ≥ N - 1, a n ∈ Finset.Icc (1 : ℤ) C := by
    intro n hn
    rw [Finset.mem_Icc]
    exact ⟨apos n, Int.le_of_dvd hCpos (dvd_bound a apos N hN hS n hn)⟩
  -- the set of indices `m ≥ N` with `a m ≠ a (m+1)` is infinite
  have hU : Set.Infinite {m : ℕ | N ≤ m ∧ a m ≠ a (m + 1)} := by
    apply Set.infinite_of_forall_exists_gt
    intro M
    obtain ⟨m, hm, hne⟩ := hnc (max (M + 1) N)
    exact ⟨m, ⟨by omega, hne⟩, by omega⟩
  -- pigeonhole: two indices with the same pair `(a m, a (m+1))`
  obtain ⟨m₁, hm₁, m₂, hm₂, hlt, hpair⟩ :=
    hU.exists_lt_map_eq_of_mapsTo (f := fun m => (a m, a (m + 1)))
      (fun m hm => by
        rw [Set.mem_ofPred_eq] at hm
        exact Finset.mem_product.mpr ⟨hmem m (by omega), hmem (m + 1) (by omega)⟩)
      ((Finset.Icc (1 : ℤ) C ×ˢ Finset.Icc (1 : ℤ) C).finite_toSet)
  rw [Set.mem_ofPred_eq] at hm₁ hm₂
  rw [Prod.mk.injEq] at hpair
  obtain ⟨hp1, hp2⟩ := hpair
  -- the walk from `m₁ + 1` to `m₂ + 1` closes, so the sequence is constant there
  have hconst := walk_const a apos N hN hS (n₁ := m₁ + 1) (n₂ := m₂ + 1)
    (by omega) (by omega) hp2 m₂ (by omega) (by omega)
  have hconst2 := walk_const a apos N hN hS (n₁ := m₁ + 1) (n₂ := m₂ + 1)
    (by omega) (by omega) hp2 (m₂ + 1) (by omega) (by omega)
  -- but the step at `m₂` is a non-stay, contradiction
  omega

end Imo2018P5
