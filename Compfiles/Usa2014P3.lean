import Mathlib.Tactic
import ProblemExtraction
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

notation "Pt" => EuclideanSpace ℝ (Fin 2)

namespace Usa2014P3

snip begin

open Finset

def N : ℝ := 2014

noncomputable def f (x : ℝ) : Pt :=
  !₂[x - (N / 3), (x - (N / 3)) ^ 3]

lemma f_injective {x y : ℝ} (hxy : x ≠ y) :
    f x ≠ f y := by
  by_contra
  unfold f at this
  aesop

lemma collinear_iff_sum {a b c : ℝ} (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) :
    Collinear ℝ {(f a), (f b), (f c)}
    ↔ (a + b + c = N) := by
  set A := f a
  set B := f b
  set C := f c
  have hAB : A ≠ B := by exact f_injective hab
  have hBC : B ≠ C := by exact f_injective hbc
  have hCA : C ≠ A := by exact f_injective hca
  let S : Finset Pt := {A, B, C}
  rw [collinear_iff_finrank_le_one]
  rw [show {A, B, C} = (S : Set Pt) by simp [S]]
  rw [vectorSpan_eq_span_vsub_finset_right_ne ℝ (show C ∈ S by simp [S])]
  rw [show S.erase C = {A, B} by grind only [= mem_erase, = mem_insert, = mem_singleton]]
  rw [image_insert, image_singleton]
  simp only [vsub_eq_sub]
  -- grab the dimension n
  let n : ℕ := ?_
  change n ≤ 1 ↔ _
  have hn : n ≤ 1 ↔ 2 ≠ n := by
    have : n ≤ 2 := (finrank_span_le_card _).trans (by simp; grind only [= card_insert_of_notMem,
      = card_singleton, = mem_singleton, = Set.mem_singleton_iff])
    omega
  rw [hn]
  -- type cast like crazy
  let X : Fin 2 → Pt := ![A - C, B - C]
  have h := linearIndependent_iff_card_eq_finrank_span (b := X) (R := ℝ)
  simp only [Fintype.card_fin] at h
  rw [show Set.range X = ({A-C, B-C}: Finset Pt) by aesop] at h
  refine h.not.symm.trans ?_
  let isom := WithLp.linearEquiv 2 ℝ (Fin 2 → ℝ)
  rw [← LinearMap.linearIndependent_iff isom.toLinearMap (by simp)]
  simp only [LinearEquiv.coe_coe]
  let M : Matrix (Fin 2) (Fin 2) ℝ := .of (isom ∘ X)
  rw [show isom ∘ X = M.row by rfl]
  rw [Matrix.linearIndependent_rows_iff_isUnit, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  -- Write the explicit matrix
  have hM : M = !![a-c, (a-(N/3))^3-(c-(N/3))^3; b-c, (b-(N/3))^3-(c-(N/3))^3] := by
    simp [← Matrix.ext_iff, Fin.forall_fin_succ]
    simp [M, isom, X, A, B, C]
    unfold f
    aesop
  rw [hM]
  simp [Matrix.det_fin_two]
  grind only

snip end

problem usamo2014_p3 : ∃ P : ℤ → Pt, ∀ a b c : ℤ,
    a ≠ b ∧ b ≠ c ∧ c ≠ a → (Collinear ℝ {P a, P b, P c} ↔ a + b + c = 2014) := by
  use fun n ↦ f (n : ℝ)
  intro a b c
  simp only [and_imp]
  intro hab hbc hca
  rify at hab hbc hca
  convert (collinear_iff_sum hab hbc hca) using 1
  unfold N
  rify
end Usa2014P3
