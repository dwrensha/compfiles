/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Data.Int.Star
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity.Basic
public import ProblemExtraction

@[expose] public section

problem_file {
  tags := [.Inequality],
}

/-!
# International Mathematical Olympiad 1987, Problem 3

Let $x_1, x_2, \ldots, x_n$ be real numbers satisfying
$x_1^2 + x_2^2 + \cdots + x_n^2 = 1$. Prove that for every integer $k \geq 2$
there are integers $a_1, a_2, \ldots, a_n$, not all zero, such that
$|a_i| \leq k - 1$ for all $i$, and
$$|a_1 x_1 + a_2 x_2 + \cdots + a_n x_n| \leq \frac{(k - 1)\sqrt{n}}{k^n - 1}.$$
-/

namespace Imo1987P3

snip begin

-- Solution formalized from https://prase.cz/kalva/imo/isoln/isoln873.html

/- The proof is an application of the pigeonhole principle. Consider the $k^n$
sums $\sum_i b_i |x_i|$ with $b_i \in \{0, 1, \ldots, k - 1\}$. By the
Cauchy-Schwarz inequality, $\sum_i |x_i| \leq \sqrt{n}$, so all of these sums lie
in the interval $[0, (k-1)\sqrt{n}]$. Splitting this interval into $k^n - 1$ equal
subintervals, two of the sums land in the same subinterval; their difference has
the form $\sum_i a_i |x_i|$ with $|a_i| \leq k - 1$ and not all $a_i$ zero, and its
absolute value is at most $\frac{(k-1)\sqrt{n}}{k^n - 1}$. Flipping the sign of
$a_i$ wherever $x_i < 0$ turns this into the required estimate for
$\sum_i a_i x_i$. -/

/-- The sum `∑ i, bᵢ * |x i|` attached to a tuple `b : Fin n → Fin k` of coefficients. -/
noncomputable def S {n : ℕ} (x : Fin n → ℝ) {k : ℕ} (b : Fin n → Fin k) : ℝ :=
  ∑ i, ((b i : ℕ) : ℝ) * |x i|

/-- Cauchy-Schwarz: `∑ i, |x i| ≤ √n` whenever `∑ i, x i ^ 2 = 1`. -/
lemma sum_abs_le_sqrt {n : ℕ} {x : Fin n → ℝ} (hx : ∑ i, x i ^ 2 = 1) :
    ∑ i, |x i| ≤ Real.sqrt n := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n))
    (fun i => |x i|) (fun _ => (1 : ℝ))
  have h2 : ∑ i, |x i| ^ 2 = 1 := by
    rw [← hx]
    exact Finset.sum_congr rfl fun i _ => sq_abs (x i)
  simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, h2] at h
  apply Real.le_sqrt_of_sq_le
  linarith [h]

/-- Every coefficient of `b : Fin k` is at most `k - 1`, as a real number. -/
lemma fin_coe_le {k : ℕ} (hk : 2 ≤ k) (b : Fin k) : ((b : ℕ) : ℝ) ≤ (k : ℝ) - 1 := by
  have h : (b : ℕ) ≤ k - 1 := Nat.le_pred_of_lt b.isLt
  calc ((b : ℕ) : ℝ) ≤ ((k - 1 : ℕ) : ℝ) := by exact_mod_cast h
  _ = (k : ℝ) - 1 := by rw [Nat.cast_sub (by lia : 1 ≤ k), Nat.cast_one]

/-- Every coefficient of `b : Fin k` is at most `k - 1`, as an integer. -/
lemma fin_coe_le_int {k : ℕ} (hk : 2 ≤ k) (b : Fin k) : ((b : ℕ) : ℤ) ≤ (k : ℤ) - 1 := by
  have h : (b : ℕ) ≤ k - 1 := Nat.le_pred_of_lt b.isLt
  calc ((b : ℕ) : ℤ) ≤ ((k - 1 : ℕ) : ℤ) := by exact_mod_cast h
  _ = (k : ℤ) - 1 := by rw [Nat.cast_sub (by lia : 1 ≤ k), Nat.cast_one]

lemma S_nonneg {n : ℕ} (x : Fin n → ℝ) {k : ℕ} (b : Fin n → Fin k) : 0 ≤ S x b :=
  Finset.sum_nonneg fun i _ => by positivity

lemma S_le {n : ℕ} {x : Fin n → ℝ} (hx : ∑ i, x i ^ 2 = 1)
    {k : ℕ} (hk : 2 ≤ k) (b : Fin n → Fin k) :
    S x b ≤ ((k : ℝ) - 1) * Real.sqrt n := by
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  calc S x b ≤ ∑ i, ((k : ℝ) - 1) * |x i| := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_right (fin_coe_le hk (b i)) (abs_nonneg _)
  _ = ((k : ℝ) - 1) * ∑ i, |x i| := by rw [Finset.mul_sum]
  _ ≤ ((k : ℝ) - 1) * Real.sqrt n :=
      mul_le_mul_of_nonneg_left (sum_abs_le_sqrt hx) (by linarith)

/-- Pure floor lemma: if `u, v ≤ m` have the same clamped floor, then `|u - v| ≤ 1`. -/
lemma floor_min_sub_le {u v : ℝ} {m : ℤ} (hum : u ≤ (m : ℝ)) (hvm : v ≤ (m : ℝ))
    (h : min ⌊u⌋ (m - 1) = min ⌊v⌋ (m - 1)) : |u - v| ≤ 1 := by
  wlog huv : u ≤ v generalizing u v with H
  · rw [abs_sub_comm]
    exact H hvm hum h.symm (not_le.mp huv).le
  · have h1 : (⌊u⌋ : ℝ) ≤ u := Int.floor_le u
    have h2 : v < (⌊v⌋ : ℝ) + 1 := Int.lt_floor_add_one v
    rcases le_total ⌊v⌋ (m - 1) with hc | hc
    · rw [min_eq_left hc] at h
      have h3 : ⌊v⌋ ≤ ⌊u⌋ := h ▸ min_le_left ⌊u⌋ (m - 1)
      have h4 : ⌊u⌋ ≤ ⌊v⌋ := Int.floor_mono huv
      have h5 : (⌊u⌋ : ℝ) = (⌊v⌋ : ℝ) := by exact_mod_cast le_antisymm h4 h3
      rw [abs_of_nonpos (by linarith : u - v ≤ 0)]
      linarith
    · rw [min_eq_right hc] at h
      have h8 : m - 1 ≤ ⌊u⌋ := h ▸ min_le_left ⌊u⌋ (m - 1)
      have h9 : ((m - 1 : ℤ) : ℝ) ≤ u := Int.le_floor.mp h8
      have h10 : ((m - 1 : ℤ) : ℝ) = (m : ℝ) - 1 := by push_cast; ring
      rw [h10] at h9
      rw [abs_of_nonpos (by linarith : u - v ≤ 0)]
      linarith

/-- The choice of integer coefficients: take the differences `bᵢ - b'ᵢ`,
flipping the sign wherever `x i < 0`. -/
noncomputable def coef {n : ℕ} (x : Fin n → ℝ) {k : ℕ} (b b' : Fin n → Fin k) (i : Fin n) : ℤ :=
  (if 0 ≤ x i then (1 : ℤ) else -1) * (((b i : ℕ) : ℤ) - ((b' i : ℕ) : ℤ))

lemma coef_cast_mul {n : ℕ} {x : Fin n → ℝ} {k : ℕ} (b b' : Fin n → Fin k) (i : Fin n) :
    (coef x b b' i : ℝ) * x i = (((b i : ℕ) : ℝ) - ((b' i : ℕ) : ℝ)) * |x i| := by
  unfold coef
  by_cases h : 0 ≤ x i
  · rw [ite_eq_left h, abs_of_nonneg h]
    push_cast
    ring
  · rw [ite_eq_right h, abs_of_neg (lt_of_not_ge h)]
    push_cast
    ring

snip end

problem imo1987_p3 {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) (hx : ∑ i, x i ^ 2 = 1)
    {k : ℕ} (hk : 2 ≤ k) :
    ∃ a : Fin n → ℤ, (∀ i, |a i| ≤ (k : ℤ) - 1) ∧ (∃ i, a i ≠ 0) ∧
      |∑ i, (a i : ℝ) * x i| ≤ ((k : ℝ) - 1) * Real.sqrt n / ((k : ℝ) ^ n - 1) := by
  set L : ℝ := ((k : ℝ) - 1) * Real.sqrt n with hL
  set M : ℝ := (k : ℝ) ^ n - 1 with hM
  have hkn2 : 2 ≤ k ^ n := by
    calc 2 ≤ k := hk
    _ = k ^ 1 := (pow_one k).symm
    _ ≤ k ^ n := pow_le_pow_right' (by lia : (1 : ℕ) ≤ k) (by lia : 1 ≤ n)
  have hkn1 : 1 ≤ k ^ n := by lia
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hk1 : (0 : ℝ) < (k : ℝ) - 1 := by linarith
  have hkn2' : (2 : ℝ) ≤ (k : ℝ) ^ n := by exact_mod_cast hkn2
  have hMpos : 0 < M := by rw [hM]; linarith
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hLpos : 0 < L := by rw [hL]; positivity
  -- every scaled sum lies in `[0, M]`
  have hub : ∀ b : Fin n → Fin k, 0 ≤ S x b * M / L ∧ S x b * M / L ≤ M := by
    intro b
    have h1 : 0 ≤ S x b := S_nonneg x b
    have h2 : S x b ≤ L := by rw [hL]; exact S_le hx hk b
    refine ⟨by positivity, ?_⟩
    rw [div_le_iff₀ hLpos]
    calc S x b * M ≤ L * M := mul_le_mul_of_nonneg_right h2 hMpos.le
    _ = M * L := by ring
  have hfloor0 : ∀ b : Fin n → Fin k, 0 ≤ ⌊S x b * M / L⌋ :=
    fun b => Int.floor_nonneg.mpr (hub b).1
  -- the pigeonhole map into `Fin (k ^ n - 1)`
  have hbnd : ∀ b : Fin n → Fin k, min (⌊S x b * M / L⌋.toNat) (k ^ n - 2) < k ^ n - 1 := by
    intro b
    calc min (⌊S x b * M / L⌋.toNat) (k ^ n - 2) ≤ k ^ n - 2 := min_le_right _ _
    _ < k ^ n - 1 := by lia
  have hcard : Fintype.card (Fin (k ^ n - 1)) < Fintype.card (Fin n → Fin k) := by
    simp only [Fintype.card_fun, Fintype.card_fin]
    lia
  obtain ⟨b, b', hne, hge⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun b : Fin n → Fin k =>
      (⟨min (⌊S x b * M / L⌋.toNat) (k ^ n - 2), hbnd b⟩ : Fin (k ^ n - 1)))
    hcard
  have hv : min (⌊S x b * M / L⌋.toNat) (k ^ n - 2)
      = min (⌊S x b' * M / L⌋.toNat) (k ^ n - 2) := congrArg Fin.val hge
  -- back to integers
  have hgi : min ⌊S x b * M / L⌋ ((k : ℤ) ^ n - 1 - 1)
      = min ⌊S x b' * M / L⌋ ((k : ℤ) ^ n - 1 - 1) := by
    have h1 : ((min (⌊S x b * M / L⌋.toNat) (k ^ n - 2) : ℕ) : ℤ)
        = ((min (⌊S x b' * M / L⌋.toNat) (k ^ n - 2) : ℕ) : ℤ) := by exact_mod_cast hv
    rw [Nat.cast_min, Nat.cast_min, Int.toNat_of_nonneg (hfloor0 b),
      Int.toNat_of_nonneg (hfloor0 b'), Nat.cast_sub hkn2, Nat.cast_pow,
      Nat.cast_ofNat] at h1
    have e : (k : ℤ) ^ n - 1 - 1 = (k : ℤ) ^ n - 2 := by ring
    rw [e]
    exact h1
  -- apply the floor lemma
  have hMcast : (((k : ℤ) ^ n - 1 : ℤ) : ℝ) = M := by rw [hM]; push_cast; ring
  have hub2 : ∀ b : Fin n → Fin k, S x b * M / L ≤ (((k : ℤ) ^ n - 1 : ℤ) : ℝ) := by
    intro b
    rw [hMcast]
    exact (hub b).2
  have habs1 : |S x b * M / L - S x b' * M / L| ≤ 1 :=
    floor_min_sub_le (hub2 b) (hub2 b') hgi
  -- rescale by `M / L`
  have hSabs : |S x b - S x b'| ≤ L / M := by
    have hML : (0 : ℝ) < M / L := div_pos hMpos hLpos
    have e : S x b * M / L - S x b' * M / L = (S x b - S x b') * (M / L) := by ring
    rw [e, abs_mul, abs_of_pos hML] at habs1
    have h2 := (le_div_iff₀ hML).mpr habs1
    rwa [one_div_div] at h2
  -- assemble the answer
  refine ⟨coef x b b', ?_, ?_, ?_⟩
  · intro i
    have hbi0 : (0 : ℤ) ≤ ((b i : ℕ) : ℤ) := by positivity
    have hb'i0 : (0 : ℤ) ≤ ((b' i : ℕ) : ℤ) := by positivity
    have hbi : ((b i : ℕ) : ℤ) ≤ (k : ℤ) - 1 := fin_coe_le_int hk (b i)
    have hb'i : ((b' i : ℕ) : ℤ) ≤ (k : ℤ) - 1 := fin_coe_le_int hk (b' i)
    have hsign : |(if 0 ≤ x i then (1 : ℤ) else -1)| = 1 := by split_ifs <;> simp
    show |(if 0 ≤ x i then (1 : ℤ) else -1) * (((b i : ℕ) : ℤ) - ((b' i : ℕ) : ℤ))|
        ≤ (k : ℤ) - 1
    rw [abs_mul, hsign, one_mul, abs_le]
    constructor <;> lia
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
    refine ⟨i, ?_⟩
    have hv' : (b i : ℕ) ≠ (b' i : ℕ) := fun h' => hi (Fin.ext h')
    show (if 0 ≤ x i then (1 : ℤ) else -1) * (((b i : ℕ) : ℤ) - ((b' i : ℕ) : ℤ)) ≠ 0
    apply mul_ne_zero
    · split_ifs <;> norm_num
    · exact sub_ne_zero.mpr (by exact_mod_cast hv')
  · have hsum : ∑ i, (coef x b b' i : ℝ) * x i = S x b - S x b' :=
      calc ∑ i, (coef x b b' i : ℝ) * x i
          = ∑ i, (((b i : ℕ) : ℝ) - ((b' i : ℕ) : ℝ)) * |x i| :=
            Finset.sum_congr rfl fun i _ => coef_cast_mul b b' i
        _ = ∑ i, (((b i : ℕ) : ℝ) * |x i| - ((b' i : ℕ) : ℝ) * |x i|) :=
            Finset.sum_congr rfl fun i _ => sub_mul _ _ _
        _ = S x b - S x b' := by unfold S; rw [Finset.sum_sub_distrib]
    rw [hsum]
    exact hSabs

end Imo1987P3
