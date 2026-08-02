/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Geometry.Euclidean.Angle.Sphere
public import Mathlib.RingTheory.SimpleRing.Principal
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# USA Mathematical Olympiad 2006, Problem 6

Let ABCD be a quadrilateral, and let E and F be points on sides AD and BC,
respectively, such that AE/ED = BF/FC. Ray FE meets rays BA and CD at S and T,
respectively. Prove that the circumcircles of triangles SAE, SBF, TCF, and TDE
pass through a common point.
-/

namespace Usa2006P6

open EuclideanGeometry

open scoped EuclideanGeometry

local instance : Fact (Module.finrank ℝ ℂ = 2) := Complex.finrank_real_complex_fact

/-- The standard (counterclockwise) orientation of the complex plane, as an instance
local to this file. -/
@[reducible]
noncomputable def complexOriented : Module.Oriented ℝ ℂ (Fin 2) := ⟨Complex.orientation⟩

attribute [local instance] complexOriented

snip begin

/-- A point expressed as a real scalar multiple along the direction from `p` to `q`
lies on the line through `p` and `q`. -/
lemma mem_line_of_eq {p q r : ℂ} (c : ℝ) (h : r - p = c • (q - p)) :
    r ∈ line[ℝ, p, q] := by
  have h' : r = (c • (q -ᵥ p)) +ᵥ p := by
    rw [vsub_eq_sub, vadd_eq_add]
    exact sub_eq_iff_eq_add.mp h
  rw [h', vadd_left_mem_affineSpan_pair]
  exact ⟨c, rfl⟩

/-- If `x ≠ p` lies on line `pq` and `y` lies on line `pr` while `r` lies on line `py`,
then `{p, x, y}` is not collinear whenever `{p, q, r}` is not collinear. -/
lemma not_collinear_of_mem_line {p q r x y : ℂ} (hne : x ≠ p)
    (hx : x ∈ line[ℝ, p, q]) (_hy : y ∈ line[ℝ, p, r]) (hr : r ∈ line[ℝ, p, y])
    (h : ¬Collinear ℝ ({p, q, r} : Set ℂ)) : ¬Collinear ℝ ({p, x, y} : Set ℂ) := by
  intro hc
  apply h
  have hy' : y ∈ line[ℝ, p, x] := hc.mem_affineSpan_of_mem_of_ne
    (Set.mem_insert p _) (Set.mem_insert_of_mem _ (Set.mem_insert x _))
    (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton y))) hne.symm
  have hle1 : line[ℝ, p, x] ≤ line[ℝ, p, q] := by
    rw [affineSpan_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨left_mem_affineSpan_pair ℝ p q, hx⟩
  have hyq : y ∈ line[ℝ, p, q] := hle1 hy'
  have hle2 : line[ℝ, p, y] ≤ line[ℝ, p, q] := by
    rw [affineSpan_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨left_mem_affineSpan_pair ℝ p q, hyq⟩
  have hrq : r ∈ line[ℝ, p, q] := hle2 hr
  have hcr : Collinear ℝ ({r, p, q} : Set ℂ) := collinear_insert_of_mem_affineSpan_pair hrq
  have hset : ({r, p, q} : Set ℂ) = {p, q, r} := by
    ext w
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  rwa [hset] at hcr

/-- If the cross-ratio `(e - s) * (a - m) / ((a - s) * (e - m))` is real and `a, s, e`
are not collinear, then `m, s, a, e` are cospherical. In the application, `m` is the
center of a spiral similarity, the reality of the cross-ratio is the angle equality
`∡ a s e = ∡ a m e` mod `π`, and the conclusion says that `m` lies on the circumcircle
of the triangle `s a e`. -/
lemma cospherical_of_im_div_eq_zero {a s e m : ℂ}
    (has : a ≠ s) (hes : e ≠ s) (ham : a ≠ m) (hem : e ≠ m)
    (hncol : ¬Collinear ℝ ({a, s, e} : Set ℂ))
    (h : ((e - s) * (a - m) / ((a - s) * (e - m))).im = 0) :
    Cospherical ({m, s, a, e} : Set ℂ) := by
  have hpo : (positiveOrientation : Orientation ℝ ℂ (Fin 2)) = Complex.orientation := rfl
  set ρ : ℂ := (e - s) * (a - m) / ((a - s) * (e - m)) with hρ
  have hρ0 : ρ ≠ 0 := by
    rw [hρ]
    exact div_ne_zero (mul_ne_zero (sub_ne_zero.mpr hes) (sub_ne_zero.mpr ham))
      (mul_ne_zero (sub_ne_zero.mpr has) (sub_ne_zero.mpr hem))
  have him : ρ.im = 0 := h
  have harg : (Complex.arg ρ : Real.Angle) = 0 ∨ (Complex.arg ρ : Real.Angle) = Real.pi := by
    rcases lt_trichotomy ρ.re 0 with hlt | heq | hgt
    · right
      have ha : Complex.arg ρ = Real.pi := Complex.arg_eq_pi_iff.mpr ⟨hlt, him⟩
      rw [ha]
    · exfalso
      exact hρ0 (Complex.ext_iff.mpr ⟨heq, him⟩)
    · left
      have ha : Complex.arg ρ = 0 := Complex.arg_eq_zero_iff.mpr ⟨hgt.le, him⟩
      rw [ha]
      exact Real.Angle.coe_zero
  have h2ρ : (2 : ℤ) • (Complex.arg ρ : Real.Angle) = 0 := by
    rcases harg with h0 | hπ
    · rw [h0, smul_zero]
    · rw [hπ, Real.Angle.two_zsmul_coe_pi]
  have hne1 : starRingEnd ℂ (a - s) ≠ 0 := by
    rw [starRingEnd_apply]
    exact star_ne_zero.mpr (sub_ne_zero.mpr has)
  have hne2 : starRingEnd ℂ (a - m) ≠ 0 := by
    rw [starRingEnd_apply]
    exact star_ne_zero.mpr (sub_ne_zero.mpr ham)
  have e1 : ∡ a s e = -(Complex.arg (a - s) : Real.Angle) + Complex.arg (e - s) := by
    simp only [EuclideanGeometry.oangle, vsub_eq_sub, hpo, Complex.oangle,
      Complex.arg_mul_coe_angle hne1 (sub_ne_zero.mpr hes), Complex.arg_conj_coe_angle]
  have e2 : ∡ a m e = -(Complex.arg (a - m) : Real.Angle) + Complex.arg (e - m) := by
    simp only [EuclideanGeometry.oangle, vsub_eq_sub, hpo, Complex.oangle,
      Complex.arg_mul_coe_angle hne2 (sub_ne_zero.mpr hem), Complex.arg_conj_coe_angle]
  have e3 : (Complex.arg ρ : Real.Angle) =
      (Complex.arg (e - s) : Real.Angle) + (Complex.arg (a - m) : Real.Angle) -
      ((Complex.arg (a - s) : Real.Angle) + (Complex.arg (e - m) : Real.Angle)) := by
    rw [hρ, Complex.arg_div_coe_angle (mul_ne_zero (sub_ne_zero.mpr hes)
        (sub_ne_zero.mpr ham)) (mul_ne_zero (sub_ne_zero.mpr has) (sub_ne_zero.mpr hem)),
      Complex.arg_mul_coe_angle (sub_ne_zero.mpr hes) (sub_ne_zero.mpr ham),
      Complex.arg_mul_coe_angle (sub_ne_zero.mpr has) (sub_ne_zero.mpr hem)]
  have hdiff : ∡ a s e - ∡ a m e = (Complex.arg ρ : Real.Angle) := by
    rw [e1, e2, e3]
    abel
  have h1 : ∡ a s e = (Complex.arg ρ : Real.Angle) + ∡ a m e := sub_eq_iff_eq_add.mp hdiff
  have key : (2 : ℤ) • ∡ a s e = (2 : ℤ) • ∡ a m e := by
    calc (2 : ℤ) • ∡ a s e = ∡ a s e + ∡ a s e := two_zsmul _
      _ = (↑(Complex.arg ρ) + ↑(Complex.arg ρ)) + (∡ a m e + ∡ a m e) := by
          rw [h1]; abel
      _ = ∡ a m e + ∡ a m e := by rw [← two_zsmul, h2ρ, zero_add]
      _ = (2 : ℤ) • ∡ a m e := (two_zsmul _).symm
  have hc := cospherical_of_two_zsmul_oangle_eq_of_not_collinear key hncol
  have hset : ({a, s, m, e} : Set ℂ) = {m, s, a, e} := by
    ext w
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  rwa [hset] at hc

snip end

problem usa2006_p6 {A B C D E F S T : ℂ}
    (hABC : ¬Collinear ℝ ({A, B, C} : Set ℂ)) (hABD : ¬Collinear ℝ ({A, B, D} : Set ℂ))
    (hACD : ¬Collinear ℝ ({A, C, D} : Set ℂ)) (hBCD : ¬Collinear ℝ ({B, C, D} : Set ℂ))
    (hEF : E ≠ F) (hSA : S ≠ A) (hSB : S ≠ B) (hTC : T ≠ C) (hTD : T ≠ D)
    (hratio : ∃ t : ℝ, 0 < t ∧ t < 1 ∧ E = A + t • (D - A) ∧ F = B + t • (C - B))
    (hSBA : ∃ u : ℝ, 0 ≤ u ∧ S = B + u • (A - B))
    (hSFE : ∃ v : ℝ, 0 ≤ v ∧ S = F + v • (E - F))
    (hTCD : ∃ w : ℝ, 0 ≤ w ∧ T = C + w • (D - C))
    (hTFE : ∃ z : ℝ, 0 ≤ z ∧ T = F + z • (E - F)) :
    ∃ M : ℂ, Cospherical ({M, S, A, E} : Set ℂ) ∧ Cospherical ({M, S, B, F} : Set ℂ) ∧
      Cospherical ({M, T, C, F} : Set ℂ) ∧ Cospherical ({M, T, D, E} : Set ℂ) := by
  obtain ⟨t, ht0, ht1, hE, hF⟩ := hratio
  obtain ⟨u, -, hSu⟩ := hSBA
  obtain ⟨v, -, hSv⟩ := hSFE
  obtain ⟨w, -, hTw⟩ := hTCD
  obtain ⟨z, -, hTz⟩ := hTFE
  -- Scalar parameters are nonzero exactly when the points they determine are distinct.
  have hu1r : u ≠ 1 := by
    intro hur
    apply hSA
    rw [hSu, hur, one_smul, add_sub_cancel]
  have hu0r : u ≠ 0 := by
    intro hur
    apply hSB
    rw [hSu, hur, zero_smul, add_zero]
  have hw0r : w ≠ 0 := by
    intro hur
    apply hTC
    rw [hTw, hur, zero_smul, add_zero]
  have hw1r : w ≠ 1 := by
    intro hur
    apply hTD
    rw [hTw, hur, one_smul, add_sub_cancel]
  -- Rewrite the parametrizations as complex multiplications.
  rw [Complex.real_smul] at hSu hSv hTw hTz hE hF
  -- Affine relations derived from the parametrizations.
  have hSA' : S - A = (1 - (u : ℂ)) * (B - A) := by rw [hSu]; ring
  have hSB' : S - B = (u : ℂ) * (A - B) := by rw [hSu]; ring
  have hSE' : S - E = (1 - (v : ℂ)) * (F - E) := by rw [hSv]; ring
  have hSF' : S - F = (v : ℂ) * (E - F) := by rw [hSv]; ring
  have hTC' : T - C = (w : ℂ) * (D - C) := by rw [hTw]; ring
  have hTD' : T - D = (1 - (w : ℂ)) * (C - D) := by rw [hTw]; ring
  have hTF' : T - F = (z : ℂ) * (E - F) := by rw [hTz]; ring
  have hTE' : T - E = (1 - (z : ℂ)) * (F - E) := by rw [hTz]; ring
  have hEA : E - A = (t : ℂ) * (D - A) := by rw [hE]; ring
  have hFB : F - B = (t : ℂ) * (C - B) := by rw [hF]; ring
  have hED : E - D = (1 - (t : ℂ)) * (A - D) := by rw [hE]; ring
  have hFC : F - C = (1 - (t : ℂ)) * (B - C) := by rw [hF]; ring
  -- Distinctness of the vertices from the non-collinearity hypotheses.
  have hAB : A ≠ B := ne₁₂_of_not_collinear hABC
  have hBC : B ≠ C := ne₂₃_of_not_collinear hABC
  have hCD : C ≠ D := ne₂₃_of_not_collinear hBCD
  have hAD : A ≠ D := ne₁₃_of_not_collinear hABD
  have ht0' : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
  have ht1' : (1 : ℂ) - (t : ℂ) ≠ 0 :=
    sub_ne_zero.mpr (by exact_mod_cast (ne_of_lt ht1).symm)
  -- Line memberships used for the non-collinearity of the mixed triples.
  have hsAB : S ∈ line[ℝ, A, B] :=
    mem_line_of_eq (1 - u) (by rw [Complex.real_smul]; push_cast; exact hSA')
  have hsBA : S ∈ line[ℝ, B, A] := by
    rw [AffineSubspace.affineSpan_pair_comm]; exact hsAB
  have heAD : E ∈ line[ℝ, A, D] :=
    mem_line_of_eq t (by rw [Complex.real_smul]; exact hEA)
  have hDA : D - A = (t : ℂ)⁻¹ * (E - A) := by
    rw [show D - A = (t : ℂ)⁻¹ * ((t : ℂ) * (D - A)) by
      rw [← mul_assoc, inv_mul_cancel₀ ht0', one_mul], ← hEA]
  have hdAE : D ∈ line[ℝ, A, E] :=
    mem_line_of_eq t⁻¹ (by rw [Complex.real_smul]; push_cast; exact hDA)
  have hfBC : F ∈ line[ℝ, B, C] :=
    mem_line_of_eq t (by rw [Complex.real_smul]; exact hFB)
  have hCB : C - B = (t : ℂ)⁻¹ * (F - B) := by
    rw [show C - B = (t : ℂ)⁻¹ * ((t : ℂ) * (C - B)) by
      rw [← mul_assoc, inv_mul_cancel₀ ht0', one_mul], ← hFB]
  have hcBF : C ∈ line[ℝ, B, F] :=
    mem_line_of_eq t⁻¹ (by rw [Complex.real_smul]; push_cast; exact hCB)
  have hfCB : F ∈ line[ℝ, C, B] := by
    rw [AffineSubspace.affineSpan_pair_comm]; exact hfBC
  have htCD : T ∈ line[ℝ, C, D] :=
    mem_line_of_eq w (by rw [Complex.real_smul]; exact hTC')
  have htDC : T ∈ line[ℝ, D, C] := by
    rw [AffineSubspace.affineSpan_pair_comm]; exact htCD
  have heDA : E ∈ line[ℝ, D, A] :=
    mem_line_of_eq (1 - t) (by rw [Complex.real_smul]; push_cast; exact hED)
  have hAD' : A - D = (1 - (t : ℂ))⁻¹ * (E - D) := by
    rw [show A - D = (1 - (t : ℂ))⁻¹ * ((1 - (t : ℂ)) * (A - D)) by
      rw [← mul_assoc, inv_mul_cancel₀ ht1', one_mul], ← hED]
  have haDE : A ∈ line[ℝ, D, E] :=
    mem_line_of_eq (1 - t)⁻¹ (by rw [Complex.real_smul]; push_cast; exact hAD')
  have hBC' : B - C = (1 - (t : ℂ))⁻¹ * (F - C) := by
    rw [show B - C = (1 - (t : ℂ))⁻¹ * ((1 - (t : ℂ)) * (B - C)) by
      rw [← mul_assoc, inv_mul_cancel₀ ht1', one_mul], ← hFC]
  have hbCF : B ∈ line[ℝ, C, F] :=
    mem_line_of_eq (1 - t)⁻¹ (by rw [Complex.real_smul]; push_cast; exact hBC')
  -- The four mixed non-collinearities.
  have hASE : ¬Collinear ℝ ({A, S, E} : Set ℂ) :=
    not_collinear_of_mem_line hSA hsAB heAD hdAE hABD
  have hBAC : ¬Collinear ℝ ({B, A, C} : Set ℂ) := by rwa [Set.insert_comm]
  have hBSF : ¬Collinear ℝ ({B, S, F} : Set ℂ) :=
    not_collinear_of_mem_line hSB hsBA hfBC hcBF hBAC
  have hCDB : ¬Collinear ℝ ({C, D, B} : Set ℂ) := by
    have hset : ({C, D, B} : Set ℂ) = {B, C, D} := by
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    rwa [hset]
  have hCTF : ¬Collinear ℝ ({C, T, F} : Set ℂ) :=
    not_collinear_of_mem_line hTC htCD hfCB hbCF hCDB
  have hDCA : ¬Collinear ℝ ({D, C, A} : Set ℂ) := by
    have hset : ({D, C, A} : Set ℂ) = {A, C, D} := by
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    rwa [hset]
  have hDTE : ¬Collinear ℝ ({D, T, E} : Set ℂ) :=
    not_collinear_of_mem_line hTD htDC heDA haDE hDCA
  -- Further distinctness harvested from the non-collinearities.
  have hSE : S ≠ E := ne₂₃_of_not_collinear hASE
  have hSF : S ≠ F := ne₂₃_of_not_collinear hBSF
  have hTF : T ≠ F := ne₂₃_of_not_collinear hCTF
  have hTE : T ≠ E := ne₂₃_of_not_collinear hDTE
  -- The multiplier `μ` of the spiral similarity is not `1`: otherwise `EF` would be
  -- parallel to `AB` and the two lines could not meet at `S`.
  have hBCAD : B - C ≠ A - D := by
    intro hbc
    have hCD' : C - D = B - A := by linear_combination -hbc
    have hFE' : F - E = B - A := by
      rw [hF, hE]
      linear_combination (t : ℂ) * hCD'
    have h2 : E - A = ((v : ℂ) - u) * (B - A) := by
      have h3 : E - A = (S - A) - (S - E) := by ring
      rw [h3, hSA', hSE', hFE']
      ring
    have h4 : (t : ℂ) * (D - A) = ((v : ℂ) - u) * (B - A) := hEA.symm.trans h2
    have h3 : D - A = (((v : ℂ) - u) / t) * (B - A) := by
      have h5 : D - A = (t : ℂ)⁻¹ * ((t : ℂ) * (D - A)) := by
        rw [← mul_assoc, inv_mul_cancel₀ ht0', one_mul]
      rw [h5, h4]
      ring
    have h3r : D - A = ((((v : ℝ) - u) / t : ℝ) : ℂ) * (B - A) := by
      push_cast
      exact h3
    have hdAB : D ∈ line[ℝ, A, B] :=
      mem_line_of_eq (((v : ℝ) - u) / t) (by rw [Complex.real_smul]; exact h3r)
    have hcoll : Collinear ℝ ({D, A, B} : Set ℂ) :=
      collinear_insert_of_mem_affineSpan_pair hdAB
    have hset : ({D, A, B} : Set ℂ) = {A, B, D} := by
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    rw [hset] at hcoll
    exact hABD hcoll
  -- The spiral similarity `z ↦ μ * z + (1 - μ) * M` with center `M` taking `A ↦ B`
  -- and `D ↦ C`.
  set μ : ℂ := (B - C) / (A - D) with hμ
  have hμ0 : μ ≠ 0 := by
    rw [hμ]
    exact div_ne_zero (sub_ne_zero.mpr hBC) (sub_ne_zero.mpr hAD)
  have hμ1 : μ ≠ 1 := by
    rw [hμ]
    intro hcon
    have h1 : B - C = (B - C) / (A - D) * (A - D) :=
      (div_mul_cancel₀ _ (sub_ne_zero.mpr hAD)).symm
    rw [hcon, one_mul] at h1
    exact hBCAD h1
  have hμ1' : (1 : ℂ) - μ ≠ 0 := sub_ne_zero.mpr hμ1.symm
  set M : ℂ := (B - μ * A) / (1 - μ) with hM
  have hM1 : M * (1 - μ) = B - μ * A := by
    rw [hM]
    exact div_mul_cancel₀ _ hμ1'
  have hμAD : μ * (A - D) = B - C := by
    rw [hμ]
    exact div_mul_cancel₀ _ (sub_ne_zero.mpr hAD)
  have hσA : B - M = μ * (A - M) := by
    apply mul_right_cancel₀ hμ1'
    rw [sub_mul, hM1]
    conv_rhs => rw [mul_assoc, sub_mul, hM1]
    ring
  have hσD : C - M = μ * (D - M) := by
    apply mul_right_cancel₀ hμ1'
    rw [sub_mul, hM1]
    conv_rhs => rw [mul_assoc, sub_mul, hM1]
    linear_combination (1 - μ) * hμAD
  have hσE : F - M = μ * (E - M) := by
    have h1 : F - M = (1 - (t : ℂ)) * (B - M) + (t : ℂ) * (C - M) := by rw [hF]; ring
    have h2 : E - M = (1 - (t : ℂ)) * (A - M) + (t : ℂ) * (D - M) := by rw [hE]; ring
    rw [h1, h2, hσA, hσD]
    ring
  -- The center is distinct from all six points.
  have hMA : M ≠ A := by
    intro h
    rw [h, sub_self, mul_zero] at hσA
    exact hAB (sub_eq_zero.mp hσA).symm
  have hMB : M ≠ B := by
    intro h
    rw [h, sub_self] at hσA
    rw [eq_comm, mul_eq_zero] at hσA
    rcases hσA with h1 | h1
    · exact hμ0 h1
    · exact hAB (sub_eq_zero.mp h1)
  have hMC : M ≠ C := by
    intro h
    rw [h, sub_self] at hσD
    rw [eq_comm, mul_eq_zero] at hσD
    rcases hσD with h1 | h1
    · exact hμ0 h1
    · exact hCD (sub_eq_zero.mp h1).symm
  have hMD : M ≠ D := by
    intro h
    rw [h, sub_self, mul_zero] at hσD
    exact hCD (sub_eq_zero.mp hσD)
  have hME : M ≠ E := by
    intro h
    rw [h, sub_self, mul_zero] at hσE
    exact hEF (sub_eq_zero.mp hσE).symm
  have hMF : M ≠ F := by
    intro h
    rw [h, sub_self] at hσE
    rw [eq_comm, mul_eq_zero] at hσE
    rcases hσE with h1 | h1
    · exact hμ0 h1
    · exact hEF (sub_eq_zero.mp h1)
  -- Side-length relations along the three relevant directions.
  have hFE : F - E = (1 - μ) * (M - E) := by
    have h1 : F - E = (F - M) - (E - M) := by ring
    rw [h1, hσE]
    ring
  have hBA : B - A = (1 - μ) * (M - A) := by
    have h1 : B - A = (B - M) - (A - M) := by ring
    rw [h1, hσA]
    ring
  have hDC : C - D = (1 - μ) * (M - D) := by
    have h1 : C - D = (C - M) - (D - M) := by ring
    rw [h1, hσD]
    ring
  -- The four cross-ratios are real.
  have hES : E - S = ((v : ℂ) - 1) * (F - E) := by
    rw [show E - S = -(S - E) by ring, hSE']; ring
  have hAS : A - S = ((u : ℂ) - 1) * (B - A) := by
    rw [show A - S = -(S - A) by ring, hSA']; ring
  have key1 : (E - S) * (A - M) * ((u : ℂ) - 1) = ((v : ℂ) - 1) * ((A - S) * (E - M)) := by
    rw [hES, hFE, hAS, hBA]
    ring
  have hu1 : (u : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hu1r)
  have hρ1 : ((E - S) * (A - M) / ((A - S) * (E - M))).im = 0 := by
    have hden : (A - S) * (E - M) ≠ 0 :=
      mul_ne_zero (sub_ne_zero.mpr hSA.symm) (sub_ne_zero.mpr hME.symm)
    have hρ1e : (E - S) * (A - M) / ((A - S) * (E - M)) =
        ((((v : ℝ) - 1) / ((u : ℝ) - 1) : ℝ) : ℂ) := by
      push_cast
      rw [div_eq_div_iff hden hu1]
      exact key1
    rw [hρ1e, Complex.ofReal_im]
  have hFS : F - S = (v : ℂ) * (F - E) := by
    rw [show F - S = -(S - F) by ring, hSF']; ring
  have hBS : B - S = (u : ℂ) * (B - A) := by
    rw [show B - S = -(S - B) by ring, hSB']; ring
  have key2 : (F - S) * (B - M) * (u : ℂ) = (v : ℂ) * ((B - S) * (F - M)) := by
    rw [hFS, hFE, hσA, hBS, hBA, hσE]
    ring
  have hu0 : (u : ℂ) ≠ 0 := by exact_mod_cast hu0r
  have hρ2 : ((F - S) * (B - M) / ((B - S) * (F - M))).im = 0 := by
    have hden : (B - S) * (F - M) ≠ 0 :=
      mul_ne_zero (sub_ne_zero.mpr hSB.symm) (sub_ne_zero.mpr hMF.symm)
    have hρ2e : (F - S) * (B - M) / ((B - S) * (F - M)) = (((v / u : ℝ)) : ℂ) := by
      push_cast
      rw [div_eq_div_iff hden hu0]
      exact key2
    rw [hρ2e, Complex.ofReal_im]
  have hFT : F - T = (z : ℂ) * (F - E) := by
    rw [show F - T = -(T - F) by ring, hTF']; ring
  have hCT : C - T = (w : ℂ) * (C - D) := by
    rw [show C - T = -(T - C) by ring, hTC']; ring
  have key3 : (F - T) * (C - M) * (w : ℂ) = (z : ℂ) * ((C - T) * (F - M)) := by
    rw [hFT, hFE, hσD, hCT, hDC, hσE]
    ring
  have hw0 : (w : ℂ) ≠ 0 := by exact_mod_cast hw0r
  have hρ3 : ((F - T) * (C - M) / ((C - T) * (F - M))).im = 0 := by
    have hden : (C - T) * (F - M) ≠ 0 :=
      mul_ne_zero (sub_ne_zero.mpr hTC.symm) (sub_ne_zero.mpr hMF.symm)
    have hρ3e : (F - T) * (C - M) / ((C - T) * (F - M)) = (((z / w : ℝ)) : ℂ) := by
      push_cast
      rw [div_eq_div_iff hden hw0]
      exact key3
    rw [hρ3e, Complex.ofReal_im]
  have hET : E - T = ((z : ℂ) - 1) * (F - E) := by
    rw [show E - T = -(T - E) by ring, hTE']; ring
  have hDT : D - T = ((w : ℂ) - 1) * (C - D) := by
    rw [show D - T = -(T - D) by ring, hTD']; ring
  have key4 : (E - T) * (D - M) * ((w : ℂ) - 1) = ((z : ℂ) - 1) * ((D - T) * (E - M)) := by
    rw [hET, hFE, hDT, hDC]
    ring
  have hw1 : (w : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hw1r)
  have hρ4 : ((E - T) * (D - M) / ((D - T) * (E - M))).im = 0 := by
    have hden : (D - T) * (E - M) ≠ 0 :=
      mul_ne_zero (sub_ne_zero.mpr hTD.symm) (sub_ne_zero.mpr hME.symm)
    have hρ4e : (E - T) * (D - M) / ((D - T) * (E - M)) =
        ((((z : ℝ) - 1) / ((w : ℝ) - 1) : ℝ) : ℂ) := by
      push_cast
      rw [div_eq_div_iff hden hw1]
      exact key4
    rw [hρ4e, Complex.ofReal_im]
  -- The Miquel point lies on all four circumcircles.
  exact ⟨M, cospherical_of_im_div_eq_zero hSA.symm hSE.symm hMA.symm hME.symm hASE hρ1,
    cospherical_of_im_div_eq_zero hSB.symm hSF.symm hMB.symm hMF.symm hBSF hρ2,
    cospherical_of_im_div_eq_zero hTC.symm hTF.symm hMC.symm hMF.symm hCTF hρ3,
    cospherical_of_im_div_eq_zero hTD.symm hTE.symm hMD.symm hME.symm hDTE hρ4⟩

end Usa2006P6
