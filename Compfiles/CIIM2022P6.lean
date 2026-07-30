/-
Copyright (c) 2024 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw, Kimi K3
-/

module

public import Mathlib.Tactic
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.NumberTheory] }

/-!
# Iberoamerican Interuniversity Mathematics Competition 2022, Problem 6

Given a positive integer m, let d(m) be the number of postive
divisors of m. Show that for every positive integer n, one
has
       d((n + 1)!) ≤ 2d(n!).
-/

namespace CIIM2022P6

def d : ℕ → ℕ
| m => (Nat.divisors m).card

snip begin

/-- If `p ≥ 2` and `1 ≤ v` then `v * p ≤ p ^ v`. -/
lemma mul_le_self_pow {p v : ℕ} (hp : 2 ≤ p) (hv : 1 ≤ v) : v * p ≤ p ^ v := by
  have h1 : v ≤ 2 ^ (v - 1) := by
    have h := Nat.lt_two_pow_self (n := v - 1)
    omega
  have h2 : (2 : ℕ) ^ (v - 1) ≤ p ^ (v - 1) := Nat.pow_le_pow_left hp _
  have h3 : v ≤ p ^ (v - 1) := h1.trans h2
  calc v * p ≤ p ^ (v - 1) * p := Nat.mul_le_mul h3 le_rfl
    _ = p ^ v := by rw [← pow_succ]; congr 1; omega

/-- Key combinatorial estimate. Let `P` be a finset of primes with multiplicities
`v p ≥ 1`, and set `N = ∏ p ∈ P, p ^ v p`. Then the sum of `(∏ p ∈ S, p ^ v p) / N ^ |S|`
over nonempty `S ⊆ P` is at most `1`. (Proof: induction on `P`, peeling off one prime.)
This is the exact estimate behind `d((n+1)!) ≤ 2 d(n!)`. -/
lemma sum_div_pow_le_one (P : Finset ℕ) (v : ℕ → ℕ) :
    (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 1 ≤ v p) →
    ∑ S ∈ P.powerset.erase ∅, ((∏ p ∈ S, p ^ v p : ℕ) : ℚ) / (∏ p ∈ P, p ^ v p : ℕ) ^ S.card ≤ 1 := by
  refine Finset.strongInductionOn P fun P ih => ?_
  intro hP hv
  rcases P.eq_empty_or_nonempty with rfl | hne
  · simp
  obtain ⟨p₀, hmax⟩ := hne
  set P' : Finset ℕ := P.erase p₀ with hP'def
  have hp₀notin : p₀ ∉ P' := Finset.notMem_erase p₀ P
  have hPP' : insert p₀ P' = P := Finset.insert_erase hmax
  have hP'ss : P' ⊂ P := Finset.erase_ssubset hmax
  have hP'sub : P' ⊆ P := Finset.erase_subset p₀ P
  have hP'prime : ∀ p ∈ P', p.Prime := fun p hp => hP p (hP'sub hp)
  have hP'v : ∀ p ∈ P', 1 ≤ v p := fun p hp => hv p (hP'sub hp)
  have hp₀P : p₀.Prime := hP p₀ hmax
  have hp₀v : 1 ≤ v p₀ := hv p₀ hmax
  set M : ℕ := ∏ p ∈ P', p ^ v p with hMdef
  set qq : ℕ := p₀ ^ v p₀ with hqqdef
  set N : ℕ := ∏ p ∈ P, p ^ v p with hNdef
  set A : ℚ := ∑ S ∈ P'.powerset.erase ∅, ((∏ p ∈ S, p ^ v p : ℕ) : ℚ) / (N : ℚ) ^ S.card with hAdef
  set AM : ℚ := ∑ S ∈ P'.powerset.erase ∅, ((∏ p ∈ S, p ^ v p : ℕ) : ℚ) / (M : ℚ) ^ S.card with hAMdef
  have hNeq : N = M * qq := by
    rw [hNdef, ← hPP', Finset.prod_insert hp₀notin, ← hqqdef, ← hMdef, mul_comm]
  have hMpos : 0 < M := by
    rw [hMdef]
    exact Finset.prod_pos fun p hp => pow_pos (hP'prime p hp).pos _
  have hqqpos : 0 < qq := by
    rw [hqqdef]
    exact pow_pos hp₀P.pos _
  have hNpos : 0 < N := by
    rw [hNeq]
    exact Nat.mul_pos hMpos hqqpos
  have hMpos' : (0 : ℚ) < M := by exact_mod_cast hMpos
  have hqqpos' : (0 : ℚ) < qq := by exact_mod_cast hqqpos
  have hqq2 : 2 ≤ qq := by
    rw [hqqdef]
    exact hp₀P.two_le.trans (Nat.le_self_pow (by omega : v p₀ ≠ 0) p₀)
  have ihP' : AM ≤ 1 := ih P' hP'ss hP'prime hP'v
  -- The per-term bound for `A` in terms of `AM`.
  have hA_le : A ≤ AM / (qq : ℚ) := by
    rw [hAdef, hAMdef, Finset.sum_div]
    apply Finset.sum_le_sum
    intro S hS
    have hcard : 1 ≤ S.card := by
      have h2 : S ≠ ∅ := (Finset.mem_erase.1 hS).1
      exact Finset.card_pos.2 (Finset.nonempty_iff_ne_empty.2 h2)
    have hden : (M : ℚ) ^ S.card * qq ≤ (N : ℚ) ^ S.card := by
      have hdenN : M ^ S.card * qq ≤ N ^ S.card := by
        rw [hNeq, mul_pow]
        have h1 : qq ≤ qq ^ S.card := Nat.le_self_pow (by omega : S.card ≠ 0) qq
        exact Nat.mul_le_mul le_rfl h1
      exact_mod_cast hdenN
    rw [div_div]
    exact div_le_div₀ (by positivity) le_rfl (by positivity) hden
  -- The powerset of `P` splits according to membership of `p₀`.
  have hpow : P.powerset = P'.powerset ∪ P'.powerset.image (insert p₀) := by
    rw [← hPP', Finset.powerset_insert]
  have hdisj : Disjoint P'.powerset (P'.powerset.image (insert p₀)) := by
    rw [Finset.disjoint_left]
    intro S hS hSimg
    rw [Finset.mem_image] at hSimg
    obtain ⟨T, hT, hTS⟩ := hSimg
    have h1 : p₀ ∈ S := hTS ▸ Finset.mem_insert_self p₀ T
    exact hp₀notin (Finset.mem_powerset.1 hS h1)
  have himg : ∀ x ∈ P'.powerset, ∀ y ∈ P'.powerset, insert p₀ x = insert p₀ y → x = y := by
    intro x hx y hy h
    have hxp : p₀ ∉ x := fun h2 => hp₀notin (Finset.mem_powerset.1 hx h2)
    have hyp : p₀ ∉ y := fun h2 => hp₀notin (Finset.mem_powerset.1 hy h2)
    rw [← Finset.erase_insert hxp, ← Finset.erase_insert hyp, h]
  have hterm : ∀ S ∈ P'.powerset,
      ((∏ p ∈ insert p₀ S, p ^ v p : ℕ) : ℚ) / (N : ℚ) ^ (insert p₀ S).card
        = (1 / (M : ℚ)) * (((∏ p ∈ S, p ^ v p : ℕ) : ℚ) / (N : ℚ) ^ S.card) := by
    intro S hS
    have hp₀S : p₀ ∉ S := fun h2 => hp₀notin (Finset.mem_powerset.1 hS h2)
    rw [Finset.prod_insert hp₀S, Finset.card_insert_of_notMem hp₀S, ← hqqdef]
    have hNq : (N : ℚ) = (M : ℚ) * qq := by exact_mod_cast hNeq
    rw [hNq]
    push_cast
    field_simp [hMpos'.ne', hqqpos'.ne']
    ring
  have himg_sum : ∑ S ∈ P'.powerset.image (insert p₀), ((∏ p ∈ S, p ^ v p : ℕ) : ℚ) / (N : ℚ) ^ S.card
      = (1 / (M : ℚ)) * ∑ S ∈ P'.powerset, ((∏ p ∈ S, p ^ v p : ℕ) : ℚ) / (N : ℚ) ^ S.card := by
    rw [Finset.sum_image himg, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro S hS
    exact hterm S hS
  have h1' : insert ∅ (P'.powerset.erase ∅) = P'.powerset :=
    Finset.insert_erase (Finset.empty_mem_powerset _)
  have hsumA : ∑ S ∈ P'.powerset, ((∏ p ∈ S, p ^ v p : ℕ) : ℚ) / (N : ℚ) ^ S.card = 1 + A := by
    have h2 : ((∏ p ∈ (∅ : Finset ℕ), p ^ v p : ℕ) : ℚ) / (N : ℚ) ^ (∅ : Finset ℕ).card = 1 := by
      simp
    rw [← h1', Finset.sum_insert (Finset.notMem_erase _ _), ← hAdef, h2]
  have hfull : ∑ S ∈ P.powerset, ((∏ p ∈ S, p ^ v p : ℕ) : ℚ) / (N : ℚ) ^ S.card
      = (1 + A) * (1 + 1 / (M : ℚ)) := by
    rw [hpow, Finset.sum_union hdisj, himg_sum, hsumA]
    ring
  have hgoal_eq : ∑ S ∈ P.powerset.erase ∅, ((∏ p ∈ S, p ^ v p : ℕ) : ℚ) / (N : ℚ) ^ S.card
      = (1 + A) * (1 + 1 / (M : ℚ)) - 1 := by
    have h1 : insert ∅ (P.powerset.erase ∅) = P.powerset :=
      Finset.insert_erase (Finset.empty_mem_powerset _)
    have h2 : ((∏ p ∈ (∅ : Finset ℕ), p ^ v p : ℕ) : ℚ) / (N : ℚ) ^ (∅ : Finset ℕ).card = 1 := by
      simp
    have h3 := Finset.sum_insert (s := P.powerset.erase ∅)
      (f := fun S => ((∏ p ∈ S, p ^ v p : ℕ) : ℚ) / (N : ℚ) ^ S.card) (Finset.notMem_erase ∅ _)
    rw [h1, hfull, h2] at h3
    linarith [h3]
  have hA1 : A ≤ 1 / (qq : ℚ) := by
    have h2 : AM / (qq : ℚ) ≤ 1 / (qq : ℚ) := (div_le_div_iff_of_pos_right hqqpos').2 ihP'
    exact hA_le.trans h2
  rcases P'.eq_empty_or_nonempty with hP'e | hP'ne
  · -- `P'` empty: the sum is `1`.
    have hA0 : A = 0 := by
      rw [hAdef, hP'e]
      simp
    have hM1 : (M : ℚ) = 1 := by
      have h1 : M = 1 := by
        rw [hMdef, hP'e]
        simp
      exact_mod_cast h1
    rw [hgoal_eq, hA0, hM1]
    norm_num
  · -- `P'` nonempty: use `(qq - 2)(M - 2) ≥ 0` and `qq + M ≥ 5`.
    have hP'ne0 : P' ≠ ∅ := Finset.nonempty_iff_ne_empty.1 hP'ne
    have hM2 : 2 ≤ M := by
      obtain ⟨p, hp⟩ := hP'ne
      have h1 : p ^ v p ≤ M := by
        rw [hMdef]
        exact Finset.single_le_prod' (fun i hi => Nat.one_le_pow _ _ (hP'prime i hi).pos) hp
      have hvp : 1 ≤ v p := hP'v p hp
      have h2 : 2 ≤ p ^ v p := (hP'prime p hp).two_le.trans (Nat.le_self_pow (by omega : v p ≠ 0) p)
      exact h2.trans h1
    have hsum5 : 5 ≤ qq + M := by
      rcases eq_or_lt_of_le hM2 with hM2eq | hM3
      · have hsub : P' ⊆ {2} := by
          intro p hp
          have h1 : p ^ v p ≤ M := by
            rw [hMdef]
            exact Finset.single_le_prod' (fun i hi => Nat.one_le_pow _ _ (hP'prime i hi).pos) hp
          have hvp : 1 ≤ v p := hP'v p hp
          have h2 : p ≤ p ^ v p := Nat.le_self_pow (by omega : v p ≠ 0) p
          have h3 : 2 ≤ p := (hP'prime p hp).two_le
          rw [Finset.mem_singleton]
          omega
        have hP'2 : P' = {2} := by
          rcases Finset.subset_singleton_iff.1 hsub with h | h
          · exact absurd h hP'ne0
          · exact h
        have hp₀ne2 : p₀ ≠ 2 := by
          have h : p₀ ∉ ({2} : Finset ℕ) := hP'2 ▸ hp₀notin
          exact Finset.notMem_singleton.1 h
        have hp₀3 : 3 ≤ p₀ := by
          have h := hp₀P.two_le
          omega
        have hqq3 : 3 ≤ qq := by
          rw [hqqdef]
          exact hp₀3.trans (Nat.le_self_pow (by omega : v p₀ ≠ 0) p₀)
        omega
      · omega
    have h1 : (1 + A) * (1 + 1 / (M : ℚ)) ≤ (1 + 1 / (qq : ℚ)) * (1 + 1 / (M : ℚ)) := by
      have h2 : (0 : ℚ) ≤ 1 + 1 / (M : ℚ) := by positivity
      gcongr
    have h3 : (1 + 1 / (qq : ℚ)) * (1 + 1 / (M : ℚ)) - 1
        = 1 / (qq : ℚ) + 1 / (M : ℚ) + 1 / ((qq : ℚ) * M) := by
      field_simp [hMpos'.ne', hqqpos'.ne']
      ring
    have h4 : (M : ℚ) + qq + 1 ≤ (qq : ℚ) * M := by
      have h5 : (0 : ℚ) ≤ ((qq : ℚ) - 2) * (M - 2) := by
        have h6 : (2 : ℚ) ≤ qq := by exact_mod_cast hqq2
        have h7 : (2 : ℚ) ≤ M := by exact_mod_cast hM2
        exact mul_nonneg (by linarith) (by linarith)
      have h8 : (5 : ℚ) ≤ (qq : ℚ) + M := by exact_mod_cast hsum5
      nlinarith [h5, h8]
    have h9 : 1 / (qq : ℚ) + 1 / (M : ℚ) + 1 / ((qq : ℚ) * M) ≤ 1 := by
      have h10 : 1 / (qq : ℚ) + 1 / (M : ℚ) + 1 / ((qq : ℚ) * M)
          = ((M : ℚ) + qq + 1) / ((qq : ℚ) * M) := by
        field_simp [hMpos'.ne', hqqpos'.ne']
      rw [h10, div_le_one (by positivity : (0 : ℚ) < qq * M)]
      exact h4
    rw [hgoal_eq]
    linarith [h1, h3, h9]

/-- The multiplicative bound `∏_{p | n+1} (v_p(n!) + v_p(n+1) + 1) ≤ 2 ∏_{p | n+1} (v_p(n!) + 1)`.
Together with the factorization of `(n+1)!` this is the heart of the problem. -/
lemma prod_factorization_le (n : ℕ) (hn : 0 < n) :
    ∏ p ∈ (n + 1).primeFactors, ((Nat.factorial n).factorization p + (n + 1).factorization p + 1)
      ≤ 2 * ∏ p ∈ (n + 1).primeFactors, ((Nat.factorial n).factorization p + 1) := by
  set P : Finset ℕ := (n + 1).primeFactors with hPdef
  have hn1 : n + 1 ≠ 0 := by omega
  have hpP : ∀ p ∈ P, p.Prime := fun p hp => (Nat.mem_primeFactors.1 hp).1
  have hwP : ∀ p ∈ P, 1 ≤ (n + 1).factorization p := fun p hp =>
    (hpP p hp).factorization_pos_of_dvd hn1 (Nat.mem_primeFactors.1 hp).2.1
  have hNN : ∏ p ∈ P, p ^ (n + 1).factorization p = n + 1 := by
    rw [hPdef, Nat.prod_primeFactors_prod_factorization]
    exact Nat.prod_factorization_pow_eq_self hn1
  have hbP : ∀ p ∈ P, n + 1 ≤ p * ((Nat.factorial n).factorization p + 1) := by
    intro p hp
    have hpp : p.Prime := hpP p hp
    rcases le_or_gt p n with hpn | hpn
    · have hlog : Nat.log p n < n + 1 := by
        refine (Nat.log_lt_iff_lt_pow hpp.one_lt (x := n + 1) (y := n) (by omega : n ≠ 0)).2 ?_
        calc n < 2 ^ n := Nat.lt_two_pow_self
          _ ≤ 2 ^ (n + 1) := pow_le_pow_right' (by omega : 1 ≤ 2) (by omega : n ≤ n + 1)
          _ ≤ p ^ (n + 1) := Nat.pow_le_pow_left hpp.two_le _
      have h1 : n / p ≤ (Nat.factorial n).factorization p := by
        rw [Nat.factorization_factorial hpp hlog]
        have hmem : (1 : ℕ) ∈ Finset.Ico 1 (n + 1) := by
          rw [Finset.mem_Ico]
          exact ⟨le_refl 1, by omega⟩
        have h2 := Finset.single_le_sum (f := fun i => n / p ^ i) (fun i _ => Nat.zero_le _) hmem
        rwa [pow_one] at h2
      have h2 : n % p + p * (n / p) = n := Nat.mod_add_div n p
      have h3 : n % p < p := Nat.mod_lt n hpp.pos
      have h4 : n + 1 - p ≤ p * (n / p) := by omega
      have h5 : p * (n / p) ≤ p * (Nat.factorial n).factorization p := Nat.mul_le_mul le_rfl h1
      calc n + 1 = (n + 1 - p) + p := by omega
        _ ≤ p * (n / p) + p := Nat.add_le_add_right h4 _
        _ ≤ p * (Nat.factorial n).factorization p + p := Nat.add_le_add_right h5 _
        _ = p * ((Nat.factorial n).factorization p + 1) := by ring
    · calc n + 1 ≤ p := hpn
        _ ≤ p * ((Nat.factorial n).factorization p + 1) := by
          have h2 : p * 1 ≤ p * ((Nat.factorial n).factorization p + 1) :=
            Nat.mul_le_mul le_rfl (by omega)
          simpa using h2
  -- Now prove the inequality in `ℚ` and cast back.
  have key : ((∏ p ∈ P, (((Nat.factorial n).factorization p + (n + 1).factorization p + 1 : ℕ) : ℚ))
      ≤ 2 * (∏ p ∈ P, (((Nat.factorial n).factorization p + 1 : ℕ) : ℚ))) := by
    set N : ℕ := ∏ p ∈ P, p ^ (n + 1).factorization p with hNdef
    have hNpos : (0 : ℚ) < (N : ℚ) := by
      have h : 0 < N := by
        rw [hNN]
        omega
      exact_mod_cast h
    -- Per-factor estimate: `b + w + 1 ≤ (b + 1) * (1 + w * p / N)`.
    have h1 : ∀ p ∈ P, (((Nat.factorial n).factorization p + (n + 1).factorization p + 1 : ℕ) : ℚ)
        ≤ (((Nat.factorial n).factorization p + 1 : ℕ) : ℚ)
          * (1 + (((n + 1).factorization p * p : ℕ) : ℚ) / (N : ℚ)) := by
      intro p hp
      have h2 : (((n + 1).factorization p : ℕ) : ℚ)
          ≤ (((Nat.factorial n).factorization p + 1 : ℕ) : ℚ)
            * ((((n + 1).factorization p * p : ℕ) : ℚ) / (N : ℚ)) := by
        have hbp : (N : ℚ) ≤ ((((Nat.factorial n).factorization p + 1) * p : ℕ) : ℚ) := by
          have h := hbP p hp
          rw [← hNN, mul_comm p ((Nat.factorial n).factorization p + 1)] at h
          exact_mod_cast h
        rw [← mul_div_assoc, le_div_iff₀ hNpos]
        calc (((n + 1).factorization p : ℕ) : ℚ) * (N : ℚ)
            ≤ (((n + 1).factorization p : ℕ) : ℚ) * ((((Nat.factorial n).factorization p + 1) * p : ℕ) : ℚ) := by
              gcongr
          _ = (((Nat.factorial n).factorization p + 1 : ℕ) : ℚ) * (((n + 1).factorization p * p : ℕ) : ℚ) := by
            push_cast
            ring
      have h3 : (((Nat.factorial n).factorization p + (n + 1).factorization p + 1 : ℕ) : ℚ)
          = (((Nat.factorial n).factorization p + 1 : ℕ) : ℚ) + (((n + 1).factorization p : ℕ) : ℚ) := by
        push_cast
        ring
      rw [h3, mul_add, mul_one]
      gcongr
    have hprod1 : (∏ p ∈ P, (((Nat.factorial n).factorization p + (n + 1).factorization p + 1 : ℕ) : ℚ))
        ≤ (∏ p ∈ P, (((Nat.factorial n).factorization p + 1 : ℕ) : ℚ))
          * (∏ p ∈ P, (1 + (((n + 1).factorization p * p : ℕ) : ℚ) / (N : ℚ) : ℚ)) := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_le_prod (fun p _ => by positivity) h1
    have hprod2 : (∏ p ∈ P, (1 + (((n + 1).factorization p * p : ℕ) : ℚ) / (N : ℚ) : ℚ)) ≤ 2 := by
      have hcomm : (∏ p ∈ P, (1 + (((n + 1).factorization p * p : ℕ) : ℚ) / (N : ℚ) : ℚ))
          = ∏ p ∈ P, ((((n + 1).factorization p * p : ℕ) : ℚ) / (N : ℚ) + 1) :=
        Finset.prod_congr rfl fun p _ => add_comm _ _
      have heq : (∑ t ∈ P.powerset,
            (∏ p ∈ t, ((((n + 1).factorization p * p : ℕ) : ℚ) / (N : ℚ))) * ∏ p ∈ P \ t, (1 : ℚ))
          = ∑ t ∈ P.powerset, ∏ p ∈ t, ((((n + 1).factorization p * p : ℕ) : ℚ) / (N : ℚ)) :=
        Finset.sum_congr rfl fun t ht => by simp
      rw [hcomm, Finset.prod_add, heq]
      -- Bound each term and apply the key sum estimate.
      have h4 : ∀ t ∈ P.powerset,
          (∏ p ∈ t, ((((n + 1).factorization p * p : ℕ) : ℚ) / (N : ℚ)))
            ≤ ((∏ p ∈ t, p ^ (n + 1).factorization p : ℕ) : ℚ) / (N : ℚ) ^ t.card := by
        intro t ht
        rw [Finset.prod_div_distrib, Finset.prod_const]
        refine (div_le_div_iff_of_pos_right (by positivity : (0 : ℚ) < (N : ℚ) ^ t.card)).2 ?_
        exact_mod_cast Finset.prod_le_prod (fun p _ => Nat.zero_le _)
          (fun p hp => mul_le_self_pow (hpP p (Finset.mem_powerset.1 ht hp)).two_le
            (hwP p (Finset.mem_powerset.1 ht hp)))
      have h5 : ∑ t ∈ P.powerset,
          ((∏ p ∈ t, p ^ (n + 1).factorization p : ℕ) : ℚ) / (N : ℚ) ^ t.card ≤ 2 := by
        have h1 : insert ∅ (P.powerset.erase ∅) = P.powerset :=
          Finset.insert_erase (Finset.empty_mem_powerset _)
        have h7 : ∑ S ∈ P.powerset.erase ∅,
            ((∏ p ∈ S, p ^ (n + 1).factorization p : ℕ) : ℚ) / (N : ℚ) ^ S.card ≤ 1 :=
          sum_div_pow_le_one P _ hpP hwP
        have h8 : ((∏ p ∈ (∅ : Finset ℕ), p ^ (n + 1).factorization p : ℕ) : ℚ)
            / (N : ℚ) ^ (∅ : Finset ℕ).card = 1 := by
          simp
        have h9 := Finset.sum_insert (s := P.powerset.erase ∅)
          (f := fun S => ((∏ p ∈ S, p ^ (n + 1).factorization p : ℕ) : ℚ) / (N : ℚ) ^ S.card)
          (Finset.notMem_erase ∅ _)
        rw [h1] at h9
        rw [h8] at h9
        linarith [h9, h7]
      exact (Finset.sum_le_sum h4).trans h5
    calc (∏ p ∈ P, (((Nat.factorial n).factorization p + (n + 1).factorization p + 1 : ℕ) : ℚ))
        ≤ (∏ p ∈ P, (((Nat.factorial n).factorization p + 1 : ℕ) : ℚ))
          * (∏ p ∈ P, (1 + (((n + 1).factorization p * p : ℕ) : ℚ) / (N : ℚ) : ℚ)) := hprod1
      _ ≤ (∏ p ∈ P, (((Nat.factorial n).factorization p + 1 : ℕ) : ℚ)) * 2 := by
          gcongr
      _ = 2 * (∏ p ∈ P, (((Nat.factorial n).factorization p + 1 : ℕ) : ℚ)) := by ring
  exact_mod_cast key

snip end

problem ciim2022_p6 (n : ℕ) (hn : 0 < n) :
    d (Nat.factorial (n + 1)) ≤ 2 * d (Nat.factorial n) := by
  have hn1 : n + 1 ≠ 0 := by omega
  have hfn : (Nat.factorial n) ≠ 0 := Nat.factorial_ne_zero n
  have hfn1 : (Nat.factorial (n + 1)) ≠ 0 := Nat.factorial_ne_zero (n + 1)
  have hfact : ∀ p : ℕ, (Nat.factorial (n + 1)).factorization p
      = (Nat.factorial n).factorization p + (n + 1).factorization p := by
    intro p
    rw [Nat.factorial_succ, Nat.factorization_mul hn1 hfn, Finsupp.add_apply, Nat.add_comm]
  have hPF : (Nat.factorial (n + 1)).primeFactors = (Nat.factorial n).primeFactors ∪ (n + 1).primeFactors := by
    ext p
    simp only [Nat.mem_primeFactors, Finset.mem_union]
    constructor
    · rintro ⟨hp, hdvd, _⟩
      rw [Nat.factorial_succ] at hdvd
      rcases hp.dvd_mul.1 hdvd with h | h
      · exact Or.inr ⟨hp, h, hn1⟩
      · exact Or.inl ⟨hp, h, hfn⟩
    · rintro (⟨hp, hdvd, _⟩ | ⟨hp, hdvd, _⟩)
      · exact ⟨hp, dvd_trans hdvd (Nat.factorial_dvd_factorial (Nat.le_succ n)), hfn1⟩
      · exact ⟨hp, dvd_trans hdvd (Nat.dvd_factorial (Nat.succ_pos n) le_rfl), hfn1⟩
  show (Nat.factorial (n + 1)).divisors.card ≤ 2 * (Nat.factorial n).divisors.card
  rw [Nat.card_divisors hfn1, Nat.card_divisors hfn, hPF]
  have hunion : (Nat.factorial n).primeFactors ∪ (n + 1).primeFactors
      = (n + 1).primeFactors ∪ ((Nat.factorial n).primeFactors \ (n + 1).primeFactors) := by
    ext p
    simp only [Finset.mem_union, Finset.mem_sdiff]
    tauto
  rw [hunion, Finset.prod_union (Finset.disjoint_sdiff)]
  -- Rewrite the two products.
  have hz : ∀ p ∈ (Nat.factorial n).primeFactors \ (n + 1).primeFactors, (n + 1).factorization p = 0 := by
    intro p hp
    rw [Finset.mem_sdiff] at hp
    have hprime : p.Prime := (Nat.mem_primeFactors.1 hp.1).1
    apply Nat.factorization_eq_zero_of_not_dvd
    intro hdvd
    exact hp.2 (Nat.mem_primeFactors.2 ⟨hprime, hdvd, hn1⟩)
  rw [Finset.prod_congr rfl (show ∀ p ∈ (n + 1).primeFactors,
      (Nat.factorial (n + 1)).factorization p + 1 = (Nat.factorial n).factorization p + (n + 1).factorization p + 1 from
      fun p hp => by rw [hfact p])]
  rw [Finset.prod_congr rfl (show ∀ p ∈ (Nat.factorial n).primeFactors \ (n + 1).primeFactors,
      (Nat.factorial (n + 1)).factorization p + 1 = (Nat.factorial n).factorization p + 1 from
      fun p hp => by rw [hfact p, hz p hp, add_zero])]
  -- Split the right-hand side.
  have hsplit : ∏ p ∈ (Nat.factorial n).primeFactors, ((Nat.factorial n).factorization p + 1)
      = (∏ p ∈ (Nat.factorial n).primeFactors \ (n + 1).primeFactors, ((Nat.factorial n).factorization p + 1))
        * ∏ p ∈ (Nat.factorial n).primeFactors ∩ (n + 1).primeFactors, ((Nat.factorial n).factorization p + 1) := by
    have h1 : (Nat.factorial n).primeFactors \ ((Nat.factorial n).primeFactors ∩ (n + 1).primeFactors)
        = (Nat.factorial n).primeFactors \ (n + 1).primeFactors := by
      ext p
      simp only [Finset.mem_sdiff, Finset.mem_inter]
      tauto
    rw [← h1]
    exact (Finset.prod_sdiff (f := fun p => (Nat.factorial n).factorization p + 1)
      Finset.inter_subset_left).symm
  have hTP : ∏ p ∈ (Nat.factorial n).primeFactors ∩ (n + 1).primeFactors, ((Nat.factorial n).factorization p + 1)
      = ∏ p ∈ (n + 1).primeFactors, ((Nat.factorial n).factorization p + 1) := by
    have h1 : (n + 1).primeFactors
        = ((Nat.factorial n).primeFactors ∩ (n + 1).primeFactors)
          ∪ ((n + 1).primeFactors \ (Nat.factorial n).primeFactors) := by
      ext p
      simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
      tauto
    have hz2 : ∀ p ∈ (n + 1).primeFactors \ (Nat.factorial n).primeFactors, (Nat.factorial n).factorization p = 0 := by
      intro p hp
      rw [Finset.mem_sdiff] at hp
      have hprime : p.Prime := (Nat.mem_primeFactors.1 hp.1).1
      apply Nat.factorization_eq_zero_of_not_dvd
      intro hdvd
      exact hp.2 (Nat.mem_primeFactors.2 ⟨hprime, hdvd, hfn⟩)
    have hdisj2 : Disjoint ((Nat.factorial n).primeFactors ∩ (n + 1).primeFactors)
        ((n + 1).primeFactors \ (Nat.factorial n).primeFactors) := by
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      rw [Finset.mem_inter] at hp1
      rw [Finset.mem_sdiff] at hp2
      exact hp2.2 hp1.1
    conv_rhs => rw [h1, Finset.prod_union hdisj2]
    rw [Finset.prod_congr rfl (show ∀ p ∈ (n + 1).primeFactors \ (Nat.factorial n).primeFactors,
        (Nat.factorial n).factorization p + 1 = 1 from fun p hp => by rw [hz2 p hp])]
    simp
  rw [hsplit, hTP]
  -- Apply the key multiplicative bound.
  have hkey := prod_factorization_le n hn
  calc (∏ p ∈ (n + 1).primeFactors, ((Nat.factorial n).factorization p + (n + 1).factorization p + 1))
        * (∏ p ∈ (Nat.factorial n).primeFactors \ (n + 1).primeFactors, ((Nat.factorial n).factorization p + 1))
      ≤ (2 * ∏ p ∈ (n + 1).primeFactors, ((Nat.factorial n).factorization p + 1))
        * (∏ p ∈ (Nat.factorial n).primeFactors \ (n + 1).primeFactors, ((Nat.factorial n).factorization p + 1)) :=
        Nat.mul_le_mul hkey le_rfl
    _ = 2 * ((∏ p ∈ (Nat.factorial n).primeFactors \ (n + 1).primeFactors, ((Nat.factorial n).factorization p + 1))
        * ∏ p ∈ (n + 1).primeFactors, ((Nat.factorial n).factorization p + 1)) := by ring

end CIIM2022P6
