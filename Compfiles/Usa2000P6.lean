/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Star.Real
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Algebra, .Inequality] }

/-!
# USA Mathematical Olympiad 2000, Problem 6

Let a₁, b₁, a₂, b₂, ..., aₙ, bₙ be nonnegative real numbers.
Prove that

  ∑ᵢⱼ min(aᵢaⱼ, bᵢbⱼ) ≤ ∑ᵢⱼ min(aᵢbⱼ, aⱼbᵢ),

where each sum is taken over all n² pairs (i, j).
-/

namespace Usa2000P6

snip begin

/-!
## Solution outline

Write Dᵢⱼ = min(aᵢbⱼ, aⱼbᵢ) − min(aᵢaⱼ, bᵢbⱼ) for the difference of the two
summands. The key algebraic identity (`key_identity`) is

  Dᵢⱼ = σᵢσⱼ min(uᵢwⱼ, uⱼwᵢ),

where uᵢ = min(aᵢ, bᵢ), wᵢ = |aᵢ − bᵢ|, and σᵢ = 1 if bᵢ ≤ aᵢ and σᵢ = −1
otherwise. Hence it suffices to show that the matrix Mᵢⱼ = min(uᵢwⱼ, uⱼwᵢ) is
positive semidefinite, for then ∑ᵢⱼ Dᵢⱼ = ∑ᵢⱼ σᵢσⱼ Mᵢⱼ = σᵀMσ ≥ 0.

On the support of w we can write min(uᵢwⱼ, uⱼwᵢ) = wᵢwⱼ min(uᵢ/wᵢ, uⱼ/wⱼ), so
everything reduces to positivity of the "min kernel" Kᵢⱼ = min(sᵢ, sⱼ)
(`min_kernel_nonneg`). Peeling off an index i₀ where s attains its minimum t,
we have min(sᵢ, sⱼ) = t + min(sᵢ−t, sⱼ−t), and the shifted kernel vanishes on
the i₀-th row and column, so

  ∑ᵢⱼ zᵢzⱼ min(sᵢ, sⱼ) = t(∑ᵢ zᵢ)² + ∑'ᵢⱼ zᵢzⱼ min(sᵢ−t, sⱼ−t) ≥ 0

by induction on the number of indices. (This is the discrete shadow of
min(s, t) = ∫₀^∞ 1[s≥r] 1[t≥r] dr, i.e. the min kernel is the covariance of
Brownian motion.)
-/

/-- The key algebraic identity: the difference of the two min-terms of a pair
of indices factors as a sign times a nonnegative min-kernel entry. -/
theorem key_identity (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    min (a * d) (c * b) - min (a * c) (b * d) =
      (if b ≤ a then (1 : ℝ) else -1) * (if d ≤ c then (1 : ℝ) else -1) *
        min (min a b * |c - d|) (min c d * |a - b|) := by
  by_cases hba : b ≤ a
  · by_cases hdc : d ≤ c
    · -- case b ≤ a, d ≤ c: both signs are +1
      rw [ite_eq_left hba, ite_eq_left hdc, min_eq_right (mul_le_mul hba hdc hd ha),
        min_eq_right hba, min_eq_right hdc, abs_of_nonneg (sub_nonneg.mpr hdc),
        abs_of_nonneg (sub_nonneg.mpr hba), ← min_sub_sub_right]
      have e : min (a * d - b * d) (c * b - b * d) = min (b * (c - d)) (d * (a - b)) := by
        rw [min_comm]; congr 1 <;> ring
      rw [e]; ring
    · -- case b ≤ a, c < d: the signs multiply to −1
      have hcd : c < d := not_le.mp hdc
      rw [ite_eq_left hba, ite_eq_right hdc]
      have h1 : min (a * d) (c * b) = c * b := by
        apply min_eq_right
        rw [mul_comm a d]
        exact mul_le_mul hcd.le hba hb hd
      rw [h1, min_eq_right hba, min_eq_left hcd.le, abs_of_nonpos (sub_nonpos.mpr hcd.le),
        abs_of_nonneg (sub_nonneg.mpr hba)]
      have e : min (b * -(c - d)) (c * (a - b)) = min (a * c - c * b) (b * d - c * b) := by
        rw [min_comm]; congr 1 <;> ring
      rw [e, min_sub_sub_right]; ring
  · have hab : a < b := not_le.mp hba
    by_cases hdc : d ≤ c
    · -- case a < b, d ≤ c: the signs multiply to −1
      rw [ite_eq_right hba, ite_eq_left hdc]
      have h1 : min (a * d) (c * b) = a * d := by
        apply min_eq_left
        rw [mul_comm c b]
        exact mul_le_mul hab.le hdc hd hb
      rw [h1, min_eq_left hab.le, min_eq_right hdc, abs_of_nonneg (sub_nonneg.mpr hdc),
        abs_of_nonpos (sub_nonpos.mpr hab.le)]
      have e : min (a * (c - d)) (d * -(a - b)) = min (a * c - a * d) (b * d - a * d) := by
        congr 1 <;> ring
      rw [e, min_sub_sub_right]; ring
    · -- case a < b, c < d: both signs are −1
      have hcd : c < d := not_le.mp hdc
      rw [ite_eq_right hba, ite_eq_right hdc]
      have h1 : min (a * c) (b * d) = a * c := min_eq_left (mul_le_mul hab.le hcd.le hc hb)
      rw [h1, min_eq_left hab.le, min_eq_left hcd.le, abs_of_nonpos (sub_nonpos.mpr hcd.le),
        abs_of_nonpos (sub_nonpos.mpr hab.le), ← min_sub_sub_right]
      have e : min (a * d - a * c) (c * b - a * c) = min (a * -(c - d)) (c * -(a - b)) := by
        congr 1 <;> ring
      rw [e]; ring

/-- The min kernel `Kᵢⱼ = min (s i) (s j)` is positive semidefinite: its
quadratic form is nonnegative for every real vector `z`. Proved by strong
induction on the index set, peeling off an index where `s` is minimal. -/
theorem min_kernel_nonneg {ι : Type*} [DecidableEq ι] (z : ι → ℝ) :
    ∀ (T : Finset ι) (s : ι → ℝ), (∀ i ∈ T, 0 ≤ s i) →
      0 ≤ ∑ i ∈ T, ∑ j ∈ T, z i * z j * min (s i) (s j) := by
  intro T
  induction T using Finset.strongInduction with
  | H T ih =>
    intro s hs
    rcases T.eq_empty_or_nonempty with rfl | hTne
    · simp
    · obtain ⟨i₀, hi₀, hmin⟩ := Finset.exists_min_image T s hTne
      have ht : 0 ≤ s i₀ := hs i₀ hi₀
      have hsplit : ∑ i ∈ T, ∑ j ∈ T, z i * z j * min (s i) (s j)
          = s i₀ * (∑ i ∈ T, z i) ^ 2
            + ∑ i ∈ T, ∑ j ∈ T, z i * z j * min (s i - s i₀) (s j - s i₀) := by
        have h1 : ∀ i ∈ T, ∀ j ∈ T, z i * z j * min (s i) (s j)
            = z i * z j * min (s i - s i₀) (s j - s i₀) + z i * z j * s i₀ := by
          intro i _ j _
          rw [min_sub_sub_right]
          ring
        have hB : ∑ i ∈ T, ∑ j ∈ T, z i * z j * s i₀ = s i₀ * (∑ i ∈ T, z i) ^ 2 := by
          have e1 : ∑ i ∈ T, ∑ j ∈ T, z i * z j * s i₀
              = (∑ i ∈ T, ∑ j ∈ T, z i * z j) * s i₀ := by
            rw [Finset.sum_congr rfl fun i _ => (Finset.sum_mul T (fun j => z i * z j) (s i₀)).symm,
              ← Finset.sum_mul]
          rw [e1, ← Finset.sum_mul_sum]; ring
        calc ∑ i ∈ T, ∑ j ∈ T, z i * z j * min (s i) (s j)
            = ∑ i ∈ T, ∑ j ∈ T,
                (z i * z j * min (s i - s i₀) (s j - s i₀) + z i * z j * s i₀) :=
              Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => h1 i hi j hj
          _ = (∑ i ∈ T, ∑ j ∈ T, z i * z j * min (s i - s i₀) (s j - s i₀))
                + ∑ i ∈ T, ∑ j ∈ T, z i * z j * s i₀ := by
              simp only [Finset.sum_add_distrib]
          _ = s i₀ * (∑ i ∈ T, z i) ^ 2
                + ∑ i ∈ T, ∑ j ∈ T, z i * z j * min (s i - s i₀) (s j - s i₀) := by
              rw [hB]; ring
      have hrestrict : ∑ i ∈ T, ∑ j ∈ T, z i * z j * min (s i - s i₀) (s j - s i₀)
          = ∑ i ∈ T.erase i₀, ∑ j ∈ T.erase i₀,
            z i * z j * min (s i - s i₀) (s j - s i₀) := by
        have hvi : ∀ i ∈ T, i ∉ T.erase i₀ →
            (∑ j ∈ T, z i * z j * min (s i - s i₀) (s j - s i₀)) = 0 := by
          intro i hi hi'
          have hii : i = i₀ := by
            by_contra hne
            exact hi' (Finset.mem_erase.mpr ⟨hne, hi⟩)
          rw [hii]
          apply Finset.sum_eq_zero
          intro j hj
          have h0 : min (s i₀ - s i₀) (s j - s i₀) = 0 := by
            rw [sub_self]
            exact min_eq_left (sub_nonneg.mpr (hmin j hj))
          rw [h0, mul_zero]
        rw [(Finset.sum_subset (T.erase_ssubset hi₀).subset hvi).symm]
        apply Finset.sum_congr rfl
        intro i hi
        have hvi' : ∀ j ∈ T, j ∉ T.erase i₀ →
            z i * z j * min (s i - s i₀) (s j - s i₀) = 0 := by
          intro j hj hj'
          have hjj : j = i₀ := by
            by_contra hne
            exact hj' (Finset.mem_erase.mpr ⟨hne, hj⟩)
          rw [hjj]
          have h0 : min (s i - s i₀) (s i₀ - s i₀) = 0 := by
            rw [sub_self]
            exact min_eq_right (sub_nonneg.mpr (hmin i (Finset.mem_of_mem_erase hi)))
          rw [h0, mul_zero]
        exact (Finset.sum_subset (T.erase_ssubset hi₀).subset hvi').symm
      rw [hsplit, hrestrict]
      apply add_nonneg
      · exact mul_nonneg ht (sq_nonneg _)
      · exact ih _ (T.erase_ssubset hi₀) (fun i => s i - s i₀)
          (fun i hi => sub_nonneg.mpr (hmin i (Finset.mem_of_mem_erase hi)))

/-- The generalized min kernel `Mᵢⱼ = min (u i * w j) (u j * w i)`, with `u` and
`w` nonnegative, is positive semidefinite. On the support of `w` it equals
`w i * w j * min (u i / w i) (u j / w j)`, so this reduces to `min_kernel_nonneg`. -/
theorem kernel_nonneg {ι : Type*} [DecidableEq ι] (S : Finset ι) (u w z : ι → ℝ)
    (hu : ∀ i ∈ S, 0 ≤ u i) (hw : ∀ i ∈ S, 0 ≤ w i) :
    0 ≤ ∑ i ∈ S, ∑ j ∈ S, z i * z j * min (u i * w j) (u j * w i) := by
  have hsub : S.filter (fun i => 0 < w i) ⊆ S := Finset.filter_subset _ _
  have hvan_i : ∀ i ∈ S, i ∉ S.filter (fun i => 0 < w i) → ∀ j ∈ S,
      z i * z j * min (u i * w j) (u j * w i) = 0 := by
    intro i hi hi' j hj
    have hwi : w i = 0 := by
      by_contra hne
      exact hi' (Finset.mem_filter.mpr ⟨hi, lt_of_le_of_ne (hw i hi) (Ne.symm hne)⟩)
    rw [hwi, mul_zero, min_eq_right (mul_nonneg (hu i hi) (hw j hj)), mul_zero]
  have hvan_j : ∀ i ∈ S, ∀ j ∈ S, j ∉ S.filter (fun i => 0 < w i) →
      z i * z j * min (u i * w j) (u j * w i) = 0 := by
    intro i hi j hj hj'
    have hwj : w j = 0 := by
      by_contra hne
      exact hj' (Finset.mem_filter.mpr ⟨hj, lt_of_le_of_ne (hw j hj) (Ne.symm hne)⟩)
    rw [hwj, mul_zero, min_eq_left (mul_nonneg (hu j hj) (hw i hi)), mul_zero]
  have hrestrict : ∑ i ∈ S, ∑ j ∈ S, z i * z j * min (u i * w j) (u j * w i)
      = ∑ i ∈ S.filter (fun i => 0 < w i), ∑ j ∈ S.filter (fun i => 0 < w i),
        z i * z j * min (u i * w j) (u j * w i) := by
    rw [(Finset.sum_subset hsub (fun i hi hi' => Finset.sum_eq_zero (hvan_i i hi hi'))).symm]
    apply Finset.sum_congr rfl
    intro i hi
    exact (Finset.sum_subset hsub (hvan_j i (hsub hi))).symm
  have hkey : ∀ i ∈ S.filter (fun i => 0 < w i), ∀ j ∈ S.filter (fun i => 0 < w i),
      z i * z j * min (u i * w j) (u j * w i)
        = (z i * w i) * (z j * w j) * min (u i / w i) (u j / w j) := by
    intro i hi j hj
    have hwi : 0 < w i := (Finset.mem_filter.mp hi).2
    have hwj : 0 < w j := (Finset.mem_filter.mp hj).2
    have e : min (u i * w j) (u j * w i) = w i * w j * min (u i / w i) (u j / w j) := by
      rw [mul_min_of_nonneg _ _ (mul_pos hwi hwj).le]
      congr 1 <;> field_simp
    rw [e]; ring
  rw [hrestrict, Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl (hkey i hi)]
  exact min_kernel_nonneg (fun i => z i * w i) _ (fun i => u i / w i)
    (fun i hi => div_nonneg (hu i (hsub hi)) (Finset.mem_filter.mp hi).2.le)

snip end

problem usa2000_p6 (n : ℕ) (a b : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) :
    ∑ i, ∑ j, min (a i * a j) (b i * b j) ≤
    ∑ i, ∑ j, min (a i * b j) (a j * b i) := by
  rw [← sub_nonneg]
  have hmerge : (∑ i, ∑ j, min (a i * b j) (a j * b i))
      - (∑ i, ∑ j, min (a i * a j) (b i * b j))
      = ∑ i, ∑ j, (min (a i * b j) (a j * b i) - min (a i * a j) (b i * b j)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_sub_distrib]
  rw [hmerge]
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    key_identity (a i) (b i) (a j) (b j) (ha i) (hb i) (ha j) (hb j)]
  exact kernel_nonneg Finset.univ (fun i => min (a i) (b i)) (fun i => |a i - b i|)
    (fun i => if b i ≤ a i then (1 : ℝ) else -1) (fun i _ => le_min (ha i) (hb i))
    (fun i _ => abs_nonneg _)

end Usa2000P6
