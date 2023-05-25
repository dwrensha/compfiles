import Mathlib.Data.Real.Basic
import Mathlib.Analysis.MeanInequalities

/-
Iranian Mathematical Olympiad 1998, problem 3

Let x₁, x₂, x₃, x₄ be positive real numbers such that

  x₁ ⬝ x₂ ⬝ x₃ ⬝ x₄ = 1.

Prove that
  x₁³ + x₂³ + x₃³ + x₄³ ≥ max(x₁ + x₂ + x₃ + x₄, 1/x₁ + 1/x₂ + 1/x₃ + 1/x₄).

-/

namespace Iran1998Q3

open BigOperators

lemma cube_root_cube (x : ℝ) (h: 0 ≤ x): (x^(3:ℝ)) ^ ((1:ℝ)/3) = x := by
  rw[←Real.rpow_mul h, mul_div_cancel' (1:ℝ) three_ne_zero]
  exact Real.rpow_one x

/- seems like there should be something like this in mathlib... -/
lemma prod_pow' (S : Finset ℕ) (e : ℝ) (f : ℕ → ℝ) (hf : ∀ s ∈ S, (0:ℝ) ≤ f s)  :
    S.prod (λ (s : ℕ) ↦ f s ^ e) = S.prod (λ (s : ℕ) ↦ f s) ^ e := by
  suffices 0 ≤ S.prod (λ (s : ℕ) ↦ f s ) ∧
   S.prod (λ (s : ℕ) ↦ f s ^ e) = S.prod (λ (s : ℕ)↦ f s) ^ e by exact this.2
  induction' S using Finset.induction with s S' hs ih
  · exact ⟨zero_le_one, (Real.one_rpow e).symm⟩
  · rw[Finset.prod_insert hs, Finset.prod_insert hs]
    obtain ⟨hs0, hs⟩ := ih (λ s hs' ↦ hf s (Finset.mem_insert_of_mem hs'))
    rw [hs]
    have hsnn := hf s (Finset.mem_insert_self s S')
    constructor
    · rw [mul_comm]
      exact mul_nonneg hs0 hsnn
    · exact (Real.mul_rpow hsnn hs0).symm

theorem iran1998_q3
    (x : ℕ → ℝ)
    (x_positive : ∀ i, 0 < x i)
    (h : ∏ i in Finset.range 4, x i = 1)
    : max (∑ i in Finset.range 4, x i) (∑ i in Finset.range 4, 1 / x i)
     ≤ ∑ i in Finset.range 4, (x i)^(3 : ℝ) := by
  rw[max_le_iff]
  constructor
  · have amgm' := Real.geom_mean_le_arith_mean_weighted
                    (Finset.range 4)
                    (λ ii ↦ (1:ℝ)/4)
                    (λ ii ↦ x ii)
                    (by intros i _; norm_num)
                    (by simp)
                    (by intros j _; exact le_of_lt (x_positive j))
    have xnonneg : ∀ i ∈ Finset.range 4, 0 ≤ x i := by
      intros i _; exact le_of_lt (x_positive i)
    rw[prod_pow' (Finset.range 4) (1/4) x xnonneg, h, Real.one_rpow] at amgm'
    dsimp at amgm'
    rw [←Finset.mul_sum] at amgm'

    let C := 1/4 * ∑ i in Finset.range 4, x i
    have hcp' : 0 ≤ ∑ i in Finset.range 4, x i := Finset.sum_nonneg xnonneg
    have hcp : 0 ≤ C := mul_nonneg (by norm_num) hcp'
    have hccp : 0 ≤ C * C := mul_nonneg hcp hcp

    have hCC : C * C * C = C^(3:ℝ) := by norm_cast; ring
    have hC := calc C
                ≤ C * C := le_mul_of_one_le_left hcp amgm'
              _ ≤ C * C * C := le_mul_of_one_le_right hccp amgm'
              _ = C^(3 : ℝ) := hCC

    have h13 : (1:ℝ) ≤ 3 := by norm_num
    have holder := Real.rpow_sum_le_const_mul_sum_rpow (Finset.range 4) x h13

    have habs : ∀ i ∈ Finset.range 4, |x i| = x i := by
      intros i _; exact abs_of_pos (x_positive i)
    rw[Finset.sum_congr rfl habs] at holder

    have habs3 : ∀ i ∈ Finset.range 4, |x i| ^ (3:ℝ) = x i ^ (3:ℝ) := by
      intros i hi; have := habs i hi; exact congr_fun (congr_arg _ this) 3
    rw[Finset.sum_congr rfl habs3] at holder
    have hccc: (4:ℝ) * C =  ∑ i in Finset.range 4, x i := by {field_simp; ring}
    rw[←hccc] at holder

    rw[Real.mul_rpow zero_le_four hcp] at holder

    have h43nn : (0:ℝ) ≤ 4 ^ (3:ℝ) := by norm_cast
    rw[Finset.card_range 4] at holder

    have hss: C ^ (3:ℝ) ≤ ((1:ℝ) / 4) * ∑ i in Finset.range 4, x i ^ (3:ℝ) := by
      have h32 : (3:ℝ) - 1 = 2 := by norm_num
      rw[h32] at holder
      --clear_except holder
      have hknn : (0:ℝ) ≤ (4:ℝ) ^ (-3 : ℝ) := by norm_cast; norm_num
      have hh := mul_le_mul_of_nonneg_left holder hknn
      rw[←mul_assoc] at hh
      have h4mm: (4:ℝ) ^ (-3: ℝ) * (4:ℝ) ^ (3:ℝ) = 1 := by norm_cast; norm_num
      rw[h4mm, one_mul, ←mul_assoc] at hh
      have h4mm': (4:ℝ) ^ (-3: ℝ) * ((4:ℕ):ℝ) ^ (2:ℝ) = 1/4 := by norm_cast; norm_num
      rw[h4mm'] at hh
      exact hh

    have htrans := le_trans hC hss
    have hm4 : 4 * C ≤ 4 * ((1/4) * ∑ i in Finset.range 4, x i ^ (3:ℝ)) :=
      mul_le_mul_of_nonneg_left htrans zero_le_four

    have h4c: 4 * C = ∑ i in Finset.range 4, x i := by field_simp; ring

    rw[h4c] at hm4
    have hro : 4 * (1 / 4 * ∑ i in Finset.range 4, x i ^ (3:ℝ)) =
                    ∑ i in Finset.range 4, x i ^ (3:ℝ) := by
      field_simp; ring

    rw[hro] at hm4
    exact hm4

  · let A := ∑ i in Finset.range 4, (x i)^(3:ℝ)
    let B : ℕ → ℝ := λ j ↦ (∑ i in (Finset.range 4).erase j, (x i)^(3:ℝ))
    have hab : A = (1/3) * (∑ i in Finset.range 4, B i) := by
      simp[Finset.sum_range_succ]; ring
    have h2 : ∀ j ∈ (Finset.range 4), ∏ i in (Finset.range 4).erase j, x i ≤ (1/3) * B j := by
      intros j hj
      have hcard1 : (Finset.range 4).card = 4 := Finset.card_range 4
      have hcard : ((Finset.range 4).erase j).card = (Finset.range 4).card - 1 :=
        Finset.card_erase_of_mem hj
      rw[hcard1] at hcard
      norm_num at hcard

      have amgm := Real.geom_mean_le_arith_mean_weighted
                    ((Finset.range 4).erase j)
                    (λ ii ↦ (1:ℝ)/3)
                    (λ ii ↦ x ii ^ (3:ℝ))
                    (by intros i _; simp only [one_div, inv_nonneg]; exact zero_le_three)
                    (by simp[Finset.sum_range_succ, hcard])
                    (by intros i _
                        exact Real.rpow_nonneg_of_nonneg (le_of_lt (x_positive i)) 3)
      have hr : ∀ i ∈ ((Finset.range 4).erase j),
                   (λ (ii : ℕ) ↦ x ii ^ (3:ℝ)) i ^ (λ (ii : ℕ) ↦ (1:ℝ) / 3) i = x i := by
        intros i _; exact cube_root_cube _ (le_of_lt (x_positive i))
      rw [Finset.prod_congr rfl hr] at amgm
      have hs : ∀ i ∈ ((Finset.range 4).erase j),
        (λ (ii : ℕ) ↦ (1:ℝ) / 3) i * (λ (ii : ℕ) ↦ x ii ^ (3:ℝ)) i =
         ((1:ℝ)/3) * x i ^ (3:ℝ) := by simp
      rw [Finset.sum_congr rfl hs, ←Finset.mul_sum] at amgm
      exact amgm
    have h3 : ∀ j ∈ (Finset.range 4), ∏ i in (Finset.range 4).erase j, x i = 1 / x j := by
      intros j hj
      rw [←h, ←Finset.prod_erase_mul _ _ hj]
      have : x j ≠ 0 := ne_of_gt (x_positive j)
      field_simp
    have h4 : ∀ j ∈ Finset.range 4, 1 / x j ≤ 1 / 3 * B j := by
      intros j hj
      have h2j := h2 j hj
      rw[h3 j hj] at h2j
      exact h2j
    have h5 : ∑ i in Finset.range 4, 1 / x i ≤ A := by
      have h5': ∑ i in Finset.range 4, 1 / x i ≤ ∑ i in Finset.range 4, (1 / 3) * B i :=
        Finset.sum_le_sum h4
      rw [←Finset.mul_sum] at h5'
      rw [hab]
      exact h5'
    exact h5
