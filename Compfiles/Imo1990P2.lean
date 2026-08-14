/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Tactic
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Olympiad 1990, Problem 2

Take n ≥ 3 and consider a set E of 2n - 1 distinct points on a circle.
Suppose that exactly k of these points are to be colored black. Such a
coloring is said to be "good" if there is at least one pair of black points
such that the interior of one of the arcs between them contains exactly n
points from E. Find the smallest value of k so that every such coloring of
k points of E is good.
-/

namespace Imo1990P2

determine solution (n : ℕ) : ℕ := if n % 3 = 2 then n - 1 else n

/-- Label the points by `ZMod (2 * n - 1)`. A set `B` of black points is
*good* if it contains two points `x` and `y` with `y - x = n + 1` or
`x - y = n + 1`, which is exactly the condition that one of the two arcs
between them contains `n` points of `E` in its interior. -/
def IsGood (n : ℕ) (B : Finset (ZMod (2 * n - 1))) : Prop :=
  ∃ x ∈ B, ∃ y ∈ B, y - x = ((n + 1 : ℕ) : ZMod (2 * n - 1)) ∨
    x - y = ((n + 1 : ℕ) : ZMod (2 * n - 1))

snip begin

theorem IsGood.mono {n : ℕ} {B B' : Finset (ZMod (2 * n - 1))} (hsub : B' ⊆ B)
    (h : IsGood n B') : IsGood n B := by
  obtain ⟨x, hx, y, hy, hxy⟩ := h
  exact ⟨x, hsub hx, y, hsub hy, hxy⟩

/-- A bad (i.e. not good) coloring and its translate by `n + 1` are disjoint. -/
theorem bad_disjoint_translate {n : ℕ} {B : Finset (ZMod (2 * n - 1))}
    (hbad : ¬ IsGood n B) :
    Disjoint B (B.image (· + ((n + 1 : ℕ) : ZMod (2 * n - 1)))) := by
  rw [Finset.disjoint_left]
  intro x hxB hxim
  rw [Finset.mem_image] at hxim
  obtain ⟨y, hyB, hxy⟩ := hxim
  apply hbad
  refine ⟨y, hyB, x, hxB, Or.inl ?_⟩
  rw [← hxy, add_sub_cancel_left]

/-- Exactly `t` of the numbers `0, ..., 3 * t - 1` are congruent to `j` mod 3. -/
theorem card_range_filter_mod_eq (t j : ℕ) (hj : j < 3) :
    ((Finset.range (3 * t)).filter (· % 3 = j)).card = t := by
  have h : ((Finset.range (3 * t)).filter (· % 3 = j)).card = (Finset.range t).card := by
    apply Finset.card_bij (fun v _ => v / 3)
    · intro v hv
      rw [Finset.mem_filter, Finset.mem_range] at hv
      rw [Finset.mem_range]
      omega
    · intro v hv w hw hvw
      rw [Finset.mem_filter, Finset.mem_range] at hv hw
      omega
    · intro q hq
      rw [Finset.mem_range] at hq
      refine ⟨3 * q + j, ?_, by omega⟩
      rw [Finset.mem_filter, Finset.mem_range]
      omega
  rwa [Finset.card_range] at h

/-- When `3 ∣ N`, exactly `N / 3` elements of `ZMod N` have a given
`val` residue mod 3. -/
theorem card_univ_filter_val_mod_eq {N : ℕ} [NeZero N] (hN : 3 ∣ N) (j : ℕ)
    (hj : j < 3) :
    ((Finset.univ : Finset (ZMod N)).filter (fun x => x.val % 3 = j)).card = N / 3 := by
  have himg : Finset.univ.filter (fun x : ZMod N => x.val % 3 = j) =
      ((Finset.range N).filter (· % 3 = j)).image (Nat.cast : ℕ → ZMod N) := by
    ext x
    rw [Finset.mem_filter, Finset.mem_image]
    simp only [Finset.mem_univ, true_and, Finset.mem_filter, Finset.mem_range]
    constructor
    · intro h
      exact ⟨x.val, ⟨ZMod.val_lt x, h⟩, ZMod.natCast_rightInverse x⟩
    · rintro ⟨v, ⟨hvN, hvj⟩, rfl⟩
      rwa [ZMod.val_natCast_of_lt hvN]
  rw [himg, Finset.card_image_of_injOn]
  · obtain ⟨t, rfl⟩ := hN
    rw [card_range_filter_mod_eq t j hj]
    omega
  · intro a ha b hb hab
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at ha hb
    have hmod : a ≡ b [MOD N] := (ZMod.natCast_eq_natCast_iff a b N).1 hab
    have hmod' : a % N = b % N := hmod
    rwa [Nat.mod_eq_of_lt ha.1, Nat.mod_eq_of_lt hb.1] at hmod'

/-- Translation by `n + 1` preserves `val % 3` when `3 ∣ n + 1`
and `3 ∣ 2 * n - 1`. -/
theorem val_mod_translate {n : ℕ} [NeZero (2 * n - 1)] (h3n : 3 ∣ n + 1)
    (h3N : 3 ∣ 2 * n - 1) (x : ZMod (2 * n - 1)) :
    (x + ((n + 1 : ℕ) : ZMod (2 * n - 1))).val % 3 = x.val % 3 := by
  have hmodN : (x + ((n + 1 : ℕ) : ZMod (2 * n - 1))).val ≡ x.val + (n + 1)
      [MOD 2 * n - 1] := by
    rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_add x.val (n + 1),
      ZMod.natCast_rightInverse x]
    exact ZMod.natCast_rightInverse _
  have hmod3 : (x + ((n + 1 : ℕ) : ZMod (2 * n - 1))).val ≡ x.val [MOD 3] := by
    have h1 := hmodN.of_dvd h3N
    have h2 : x.val + (n + 1) ≡ x.val [MOD 3] := by
      obtain ⟨c, hc⟩ := h3n
      show (x.val + (n + 1)) % 3 = x.val % 3
      omega
    exact h1.trans h2
  exact hmod3

/-- If `n % 3 ≠ 2` then `2 * n - 1` and `n + 1` are coprime. -/
theorem coprime_aux {n : ℕ} (hn : 3 ≤ n) (h3 : n % 3 ≠ 2) :
    Nat.Coprime (2 * n - 1) (n + 1) := by
  rw [Nat.coprime_iff_gcd_eq_one]
  have hdvd : Nat.gcd (2 * n - 1) (n + 1) ∣ 3 := by
    have h1 : Nat.gcd (2 * n - 1) (n + 1) ∣ 2 * (n + 1) :=
      dvd_trans (Nat.gcd_dvd_right _ _) (dvd_mul_left (n + 1) 2)
    have h2 : Nat.gcd (2 * n - 1) (n + 1) ∣ 2 * n - 1 := Nat.gcd_dvd_left _ _
    have h3' := Nat.dvd_sub h1 h2
    rwa [show 2 * (n + 1) - (2 * n - 1) = 3 by omega] at h3'
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).1 hdvd with h | h
  · exact h
  · exfalso
    have h31 : 3 ∣ n + 1 := h ▸ Nat.gcd_dvd_right _ _
    have h4 : (n + 1) % 3 = 0 := Nat.mod_eq_zero_of_dvd h31
    omega

/-- Upper bound: a bad coloring has at most `solution n - 1` black points. -/
theorem card_le_of_bad {n : ℕ} (hn : 3 ≤ n) {B : Finset (ZMod (2 * n - 1))}
    (hbad : ¬ IsGood n B) : B.card ≤ solution n - 1 := by
  have : NeZero (2 * n - 1) := ⟨by omega⟩
  have key := bad_disjoint_translate hbad
  have hinj : Function.Injective (· + ((n + 1 : ℕ) : ZMod (2 * n - 1))) :=
    fun _ _ h => add_right_cancel h
  by_cases h3 : n % 3 = 2
  · -- Case `n = 3 * m + 2`: the graph splits into three cycles of length
    -- `2 * m + 1`, given by the residue classes of `val` mod 3.
    obtain ⟨m, rfl⟩ : ∃ m, n = 3 * m + 2 := ⟨n / 3, by omega⟩
    simp only [solution]
    rw [ite_eq_left h3]
    have h3dvd : 3 ∣ (3 * m + 2) + 1 := ⟨m + 1, by ring⟩
    have hN3 : 3 ∣ 2 * (3 * m + 2) - 1 := ⟨2 * m + 1, by omega⟩
    have hfib : ∀ j ∈ Finset.range 3,
        (B.filter (fun x => x.val % 3 = j)).card ≤ m := by
      intro j hj
      rw [Finset.mem_range] at hj
      have hT : ((Finset.univ : Finset (ZMod (2 * (3 * m + 2) - 1))).filter
          (fun x => x.val % 3 = j)).card = 2 * m + 1 := by
        rw [card_univ_filter_val_mod_eq hN3 j hj]
        omega
      have hsub1 : B.filter (fun x => x.val % 3 = j) ⊆
          Finset.univ.filter (fun x => x.val % 3 = j) :=
        Finset.filter_subset_filter _ (Finset.subset_univ _)
      have hsub2 : (B.filter (fun x => x.val % 3 = j)).image
          (· + (((3 * m + 2) + 1 : ℕ) : ZMod (2 * (3 * m + 2) - 1))) ⊆
          Finset.univ.filter (fun x => x.val % 3 = j) := by
        intro z hz
        rw [Finset.mem_image] at hz
        obtain ⟨x, hx, rfl⟩ := hz
        rw [Finset.mem_filter] at hx ⊢
        exact ⟨Finset.mem_univ _, (val_mod_translate h3dvd hN3 x).trans hx.2⟩
      have hdisj : Disjoint (B.filter (fun x => x.val % 3 = j))
          ((B.filter (fun x => x.val % 3 = j)).image
            (· + (((3 * m + 2) + 1 : ℕ) : ZMod (2 * (3 * m + 2) - 1)))) :=
        key.mono (Finset.filter_subset _ _)
          (Finset.image_subset_image (Finset.filter_subset _ _))
      have h2 : 2 * (B.filter (fun x => x.val % 3 = j)).card ≤ 2 * m + 1 := by
        have hcu := Finset.card_union_of_disjoint hdisj
        have hle := Finset.card_le_card (Finset.union_subset hsub1 hsub2)
        rw [Finset.card_image_of_injective _ hinj] at hcu
        omega
      omega
    have hsum : B.card = ∑ j ∈ Finset.range 3,
        (B.filter (fun x => x.val % 3 = j)).card :=
      Finset.card_eq_sum_card_fiberwise fun x _ =>
        Finset.mem_range.2 (Nat.mod_lt _ (by norm_num : 0 < 3))
    rw [hsum]
    refine (Finset.sum_le_sum hfib).trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    omega
  · -- Case `n % 3 ≠ 2`: `2 * n - 1` and `n + 1` are coprime, so the graph is a
    -- single cycle of length `2 * n - 1` and `B`, `B + (n + 1)` are disjoint.
    simp only [solution]
    rw [ite_eq_right h3]
    have h2 : 2 * B.card ≤ 2 * n - 1 := by
      have hcu := Finset.card_union_of_disjoint key
      have hle := Finset.card_le_card (Finset.subset_univ
        (B ∪ B.image (· + ((n + 1 : ℕ) : ZMod (2 * n - 1)))))
      rw [Finset.card_image_of_injective _ hinj] at hcu
      rw [Finset.card_univ, ZMod.card] at hle
      omega
    omega

/-- Lower bound: there is a bad coloring with `solution n - 1` black points. -/
theorem exists_bad {n : ℕ} (hn : 3 ≤ n) :
    ∃ B : Finset (ZMod (2 * n - 1)), B.card = solution n - 1 ∧ ¬ IsGood n B := by
  have : NeZero (2 * n - 1) := ⟨by omega⟩
  by_cases h3 : n % 3 = 2
  · -- The set `{1, 2, ..., n - 2}` is bad and has `n - 2` elements.
    refine ⟨(Finset.Icc 1 (n - 2)).image (Nat.cast : ℕ → ZMod (2 * n - 1)), ?_, ?_⟩
    · simp only [solution]
      rw [ite_eq_left h3, Finset.card_image_of_injOn, Nat.card_Icc]
      · omega
      · intro a ha b hb hab
        rw [Finset.mem_coe, Finset.mem_Icc] at ha hb
        have hmod : a ≡ b [MOD 2 * n - 1] := (ZMod.natCast_eq_natCast_iff a b _).1 hab
        have hmod' : a % (2 * n - 1) = b % (2 * n - 1) := hmod
        rwa [Nat.mod_eq_of_lt (by omega : a < 2 * n - 1),
          Nat.mod_eq_of_lt (by omega : b < 2 * n - 1)] at hmod'
    · rintro ⟨x, hx, y, hy, hxy⟩
      rw [Finset.mem_image] at hx hy
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hy
      rw [Finset.mem_Icc] at ha hb
      rcases hxy with hxy | hxy
      · have hb' : (b : ZMod (2 * n - 1)) = ((a + (n + 1) : ℕ) : ZMod (2 * n - 1)) := by
          rw [Nat.cast_add]
          rw [sub_eq_iff_eq_add.1 hxy, add_comm]
        have hmod : b ≡ a + (n + 1) [MOD 2 * n - 1] :=
          (ZMod.natCast_eq_natCast_iff _ _ _).1 hb'
        have hmod' : b % (2 * n - 1) = (a + (n + 1)) % (2 * n - 1) := hmod
        rw [Nat.mod_eq_of_lt (by omega : b < 2 * n - 1)] at hmod'
        by_cases hle : a + (n + 1) < 2 * n - 1
        · rw [Nat.mod_eq_of_lt hle] at hmod'
          omega
        · have heq : a + (n + 1) = 2 * n - 1 := by omega
          rw [heq, Nat.mod_self] at hmod'
          omega
      · have ha' : (a : ZMod (2 * n - 1)) = ((b + (n + 1) : ℕ) : ZMod (2 * n - 1)) := by
          rw [Nat.cast_add]
          rw [sub_eq_iff_eq_add.1 hxy, add_comm]
        have hmod : a ≡ b + (n + 1) [MOD 2 * n - 1] :=
          (ZMod.natCast_eq_natCast_iff _ _ _).1 ha'
        have hmod' : a % (2 * n - 1) = (b + (n + 1)) % (2 * n - 1) := hmod
        rw [Nat.mod_eq_of_lt (by omega : a < 2 * n - 1)] at hmod'
        by_cases hle : b + (n + 1) < 2 * n - 1
        · rw [Nat.mod_eq_of_lt hle] at hmod'
          omega
        · have heq : b + (n + 1) = 2 * n - 1 := by omega
          rw [heq, Nat.mod_self] at hmod'
          omega
  · -- The set `{2 * j * (n + 1) mod (2 * n - 1) : 0 ≤ j ≤ n - 2}` is bad and
    -- has `n - 1` elements: these are every other vertex of the cycle.
    have hcop : Nat.Coprime (2 * n - 1) (n + 1) := coprime_aux hn h3
    refine ⟨(Finset.range (n - 1)).image
      (fun j => ((2 * j * (n + 1) : ℕ) : ZMod (2 * n - 1))), ?_, ?_⟩
    · simp only [solution]
      rw [ite_eq_right h3, Finset.card_image_of_injOn, Finset.card_range]
      · intro i hi j hj hij
        rw [Finset.mem_coe, Finset.mem_range] at hi hj
        have hmod : 2 * i * (n + 1) ≡ 2 * j * (n + 1) [MOD 2 * n - 1] :=
          (ZMod.natCast_eq_natCast_iff _ _ _).1 hij
        rcases le_total i j with hle | hle
        · have hle' : 2 * i * (n + 1) ≤ 2 * j * (n + 1) := by nlinarith [hle]
          have hdvd : (2 * n - 1) ∣ 2 * j * (n + 1) - 2 * i * (n + 1) :=
            (Nat.modEq_iff_dvd' hle').1 hmod
          rw [← Nat.sub_mul] at hdvd
          have hdvd2 := hcop.dvd_of_dvd_mul_right hdvd
          have hz : 2 * j - 2 * i = 0 := Nat.eq_zero_of_dvd_of_lt hdvd2 (by omega)
          omega
        · have hle' : 2 * j * (n + 1) ≤ 2 * i * (n + 1) := by nlinarith [hle]
          have hdvd : (2 * n - 1) ∣ 2 * i * (n + 1) - 2 * j * (n + 1) :=
            (Nat.modEq_iff_dvd' hle').1 hmod.symm
          rw [← Nat.sub_mul] at hdvd
          have hdvd2 := hcop.dvd_of_dvd_mul_right hdvd
          have hz : 2 * i - 2 * j = 0 := Nat.eq_zero_of_dvd_of_lt hdvd2 (by omega)
          omega
    · rintro ⟨x, hx, y, hy, hxy⟩
      rw [Finset.mem_image] at hx hy
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hy
      rw [Finset.mem_range] at ha hb
      have key : ∀ c d : ℕ, c < n - 1 → d < n - 1 →
          ((2 * d * (n + 1) : ℕ) : ZMod (2 * n - 1)) -
            ((2 * c * (n + 1) : ℕ) : ZMod (2 * n - 1)) ≠
            ((n + 1 : ℕ) : ZMod (2 * n - 1)) := by
        intro c d hc hd hcd
        have hmod : 2 * d * (n + 1) ≡ 2 * c * (n + 1) + (n + 1) [MOD 2 * n - 1] := by
          have h := sub_eq_iff_eq_add.1 hcd
          rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_add, h, add_comm]
        rcases le_total (2 * c + 1) (2 * d) with hle | hle
        · have hle' : 2 * c * (n + 1) + (n + 1) ≤ 2 * d * (n + 1) := by
            nlinarith [hle]
          have hdvd : (2 * n - 1) ∣ 2 * d * (n + 1) - (2 * c * (n + 1) + (n + 1)) :=
            (Nat.modEq_iff_dvd' hle').1 hmod.symm
          have h1 : 2 * c * (n + 1) + (n + 1) = (2 * c + 1) * (n + 1) := by
            rw [add_mul, one_mul]
          rw [h1, ← Nat.sub_mul] at hdvd
          have hdvd2 := hcop.dvd_of_dvd_mul_right hdvd
          have hz : 2 * d - (2 * c + 1) = 0 :=
            Nat.eq_zero_of_dvd_of_lt hdvd2 (by omega)
          omega
        · have hle' : 2 * d * (n + 1) ≤ 2 * c * (n + 1) + (n + 1) := by
            nlinarith [hle]
          have hdvd : (2 * n - 1) ∣ (2 * c * (n + 1) + (n + 1)) - 2 * d * (n + 1) :=
            (Nat.modEq_iff_dvd' hle').1 hmod
          have h1 : 2 * c * (n + 1) + (n + 1) = (2 * c + 1) * (n + 1) := by
            rw [add_mul, one_mul]
          rw [h1, ← Nat.sub_mul] at hdvd
          have hdvd2 := hcop.dvd_of_dvd_mul_right hdvd
          have hz : (2 * c + 1) - 2 * d = 0 :=
            Nat.eq_zero_of_dvd_of_lt hdvd2 (by omega)
          omega
      rcases hxy with hxy | hxy
      · exact key a b ha hb hxy
      · exact key b a hb ha hxy

snip end

problem imo1990_p2 (n : ℕ) (hn : 3 ≤ n) :
    IsLeast {k : ℕ | ∀ B : Finset (ZMod (2 * n - 1)), B.card = k → IsGood n B}
      (solution n) := by
  constructor
  · -- Every coloring of `solution n` points is good, by `card_le_of_bad`.
    intro B hB
    by_contra hbad
    have hle := card_le_of_bad hn hbad
    by_cases h3 : n % 3 = 2
    · simp only [solution] at hB hle
      rw [ite_eq_left h3] at hB hle
      omega
    · simp only [solution] at hB hle
      rw [ite_eq_right h3] at hB hle
      omega
  · -- No smaller `k` works, by the bad coloring from `exists_bad`.
    intro k hk
    obtain ⟨B, hBcard, hBbad⟩ := exists_bad hn
    by_contra hlt
    push Not at hlt
    have hsol : 1 ≤ solution n := Nat.one_le_of_lt hlt
    have hkle : k ≤ B.card := by omega
    obtain ⟨B', hsub, hB'card⟩ := Finset.exists_subset_card_eq hkle
    exact hBbad (IsGood.mono hsub (hk B' hB'card))

end Imo1990P2
