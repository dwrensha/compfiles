/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Tactic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Data.Matrix.Basic
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 1978, Problem 2

P is a point inside a sphere. Three mutually perpendicular rays from P
intersect the sphere at points U, V and W. Q denotes the vertex diagonally
opposite P in the parallelepiped determined by PU, PV, PW. Find the locus
of Q for all possible sets of such rays from P.

(Problem and answer source: https://prase.cz/kalva/imo/isoln/isoln782.html)
-/

namespace Imo1978P2

/-- Euclidean three-dimensional space, coordinatized as `ℝ³`. -/
abbrev Point := Fin 3 → ℝ

/-- The inner (dot) product of two vectors. -/
def ip (u v : Point) : ℝ := ∑ i, u i * v i

/-- The squared Euclidean norm of a vector. -/
def sqNorm (u : Point) : ℝ := ∑ i, u i ^ 2

/-- The Euclidean distance between two points. -/
noncomputable def Dist (A B : Point) : ℝ := Real.sqrt (sqNorm (A - B))

/-- The standard basis vectors. -/
def e (i : Fin 3) : Point := fun j => if i = j then 1 else 0

/-- The unit vector obtained as a trigonometric combination of two vectors. -/
noncomputable def rot (x y : Point) (θ : ℝ) : Point := Real.cos θ • x + Real.sin θ • y

/-- The quadratic form `F(u) = ⟨b,u⟩² - ⟨a,u⟩²` governing the construction. -/
def F (a b u : Point) : ℝ := ip b u ^ 2 - ip a u ^ 2

snip begin

theorem ip_comm (u v : Point) : ip u v = ip v u := by
  unfold ip
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem ip_add_left (u v w : Point) : ip (u + v) w = ip u w + ip v w := by
  unfold ip
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp [Pi.add_apply]
  ring

theorem ip_add_right (u v w : Point) : ip u (v + w) = ip u v + ip u w := by
  unfold ip
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp [Pi.add_apply]
  ring

theorem ip_sub_left (u v w : Point) : ip (u - v) w = ip u w - ip v w := by
  unfold ip
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp [Pi.sub_apply]
  ring

theorem ip_smul_left (c : ℝ) (u v : Point) : ip (c • u) v = c * ip u v := by
  unfold ip
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [Pi.smul_apply, smul_eq_mul]
  ring

theorem ip_smul_right (c : ℝ) (u v : Point) : ip u (c • v) = c * ip u v := by
  unfold ip
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [Pi.smul_apply, smul_eq_mul]
  ring

theorem ip_self (u : Point) : ip u u = sqNorm u := by
  unfold ip sqNorm
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem sqNorm_nonneg (u : Point) : 0 ≤ sqNorm u :=
  Finset.sum_nonneg fun i _ => sq_nonneg (u i)

theorem sqNorm_add (u v : Point) :
    sqNorm (u + v) = sqNorm u + 2 * ip u v + sqNorm v := by
  unfold sqNorm ip
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp [Pi.add_apply]
  ring

theorem sqNorm_smul (c : ℝ) (u : Point) : sqNorm (c • u) = c ^ 2 * sqNorm u := by
  unfold sqNorm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [Pi.smul_apply, smul_eq_mul]
  ring

/-- The standard basis is orthonormal. -/
theorem ip_e (x : Point) (i : Fin 3) : ip x (e i) = x i := by
  unfold ip e
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    rw [if_neg (Ne.symm hji)]
    ring
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem ip_e_left (x : Point) (i : Fin 3) : ip (e i) x = x i := by
  rw [ip_comm, ip_e]

theorem ip_e_e (i j : Fin 3) : ip (e i) (e j) = if i = j then 1 else 0 := by
  rw [ip_e_left]
  by_cases h : i = j
  · subst h
    simp [e]
  · rw [if_neg h]
    simp [e, Ne.symm h]

theorem rot_zero (x y : Point) : rot x y 0 = x := by
  simp [rot, Real.cos_zero, Real.sin_zero]

theorem rot_pi_div_two (x y : Point) : rot x y (Real.pi / 2) = y := by
  simp [rot, Real.cos_pi_div_two, Real.sin_pi_div_two]

theorem ip_rot_right (u x y : Point) (θ : ℝ) :
    ip u (rot x y θ) = Real.cos θ * ip u x + Real.sin θ * ip u y := by
  simp [rot, ip_add_right, ip_smul_right]

theorem ip_rot_left (x y u : Point) (θ : ℝ) :
    ip (rot x y θ) u = Real.cos θ * ip x u + Real.sin θ * ip y u := by
  simp [rot, ip_add_left, ip_smul_left]

/-- Trigonometric combinations of orthonormal vectors remain unit. -/
theorem ip_rot_self {x y : Point} (hxx : ip x x = 1) (hyy : ip y y = 1)
    (hxy : ip x y = 0) (θ : ℝ) : ip (rot x y θ) (rot x y θ) = 1 := by
  have hyx : ip y x = 0 := by rw [ip_comm]; exact hxy
  simp only [rot, ip_add_left, ip_add_right, ip_smul_left, ip_smul_right,
    hxx, hyy, hxy, hyx]
  linear_combination Real.cos_sq_add_sin_sq θ

/-- The rotated vector by `θ + π/2` is perpendicular to the one by `θ`. -/
theorem perp_rot {x y : Point} (hxx : ip x x = 1) (hyy : ip y y = 1)
    (hxy : ip x y = 0) (θ : ℝ) : ip (rot x y θ) (rot x y (θ + Real.pi / 2)) = 0 := by
  have c2 : Real.cos (θ + Real.pi / 2) = -Real.sin θ := Real.cos_add_pi_div_two θ
  have s2 : Real.sin (θ + Real.pi / 2) = Real.cos θ := Real.sin_add_pi_div_two θ
  have hyx : ip y x = 0 := by rw [ip_comm]; exact hxy
  simp only [rot, c2, s2, ip_add_left, ip_add_right, ip_smul_left, ip_smul_right,
    hxx, hyy, hxy, hyx]
  ring

/-- The sum of `F` over a perpendicular rotated pair is constant. -/
theorem F_rot_add (a b x y : Point) (θ : ℝ) :
    F a b (rot x y θ) + F a b (rot x y (θ + Real.pi / 2)) = F a b x + F a b y := by
  have c2 : Real.cos (θ + Real.pi / 2) = -Real.sin θ := Real.cos_add_pi_div_two θ
  have s2 : Real.sin (θ + Real.pi / 2) = Real.cos θ := Real.sin_add_pi_div_two θ
  simp only [F, ip_rot_right, c2, s2]
  linear_combination
    ((ip b x) ^ 2 + (ip b y) ^ 2 - (ip a x) ^ 2 - (ip a y) ^ 2) *
      Real.cos_sq_add_sin_sq θ

/-- `F` is continuous along rotated paths. -/
theorem continuous_F_rot (a b x y : Point) :
    Continuous fun θ => F a b (rot x y θ) := by
  have heq : (fun θ => F a b (rot x y θ)) =
      fun θ => (Real.cos θ * ip b x + Real.sin θ * ip b y) ^ 2 -
        (Real.cos θ * ip a x + Real.sin θ * ip a y) ^ 2 := by
    funext θ
    simp [F, ip_rot_right]
  rw [heq]
  exact (((Real.continuous_cos.mul continuous_const).add
      (Real.continuous_sin.mul continuous_const)).pow 2).sub
    (((Real.continuous_cos.mul continuous_const).add
      (Real.continuous_sin.mul continuous_const)).pow 2)

/-- The intermediate value theorem along a rotated path. -/
theorem exists_F_rot_eq (a b x y : Point) {μ : ℝ}
    (h : μ ∈ Set.uIcc (F a b x) (F a b y)) : ∃ θ, F a b (rot x y θ) = μ := by
  have hcont : ContinuousOn (fun θ => F a b (rot x y θ)) (Set.uIcc 0 (Real.pi / 2)) :=
    (continuous_F_rot a b x y).continuousOn
  have hIVT := intermediate_value_uIcc (f := fun θ => F a b (rot x y θ))
    (a := 0) (b := Real.pi / 2) hcont
  simp only [rot_zero, rot_pi_div_two] at hIVT
  obtain ⟨θ, -, hθ⟩ := hIVT h
  exact ⟨θ, hθ⟩

open Matrix in
/-- An orthonormal triple in `ℝ³` spans: every vector is the sum of its
coordinates along the triple. -/
theorem expansion (u : Fin 3 → Point) (hn : ∀ i, ip (u i) (u i) = 1)
    (ho : ∀ i j, i ≠ j → ip (u i) (u j) = 0) (x : Point) :
    x = ∑ i, ip x (u i) • u i := by
  classical
  let U : Matrix (Fin 3) (Fin 3) ℝ := fun i j => u j i
  have hUTU : Uᵀ * U = 1 := by
    ext i j
    have hij : (Uᵀ * U) i j = ip (u i) (u j) := by
      simp [Matrix.mul_apply, Fin.sum_univ_three, ip, U]
    rw [hij]
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.one_apply, ↓reduceIte] <;> first
      | exact hn _
      | exact ho _ _ (by decide)
  have hUUT : U * Uᵀ = 1 := mul_eq_one_comm.mp hUTU
  have h1 : (U * Uᵀ) *ᵥ x = x := by
    rw [hUUT]
    exact Matrix.one_mulVec x
  have h2 : U *ᵥ (Uᵀ *ᵥ x) = ∑ i, ip x (u i) • u i := by
    have hmv : ∀ (M : Matrix (Fin 3) (Fin 3) ℝ) (v : Point) (i : Fin 3),
        (M *ᵥ v) i = ∑ j, M i j * v j := fun M v i => rfl
    have hUr : ∀ i j, U i j = u j i := fun i j => rfl
    ext l
    simp only [hmv, Matrix.transpose_apply, hUr, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, ip, Fin.sum_univ_three]
    ring
  calc x = (U * Uᵀ) *ᵥ x := h1.symm
  _ = U *ᵥ (Uᵀ *ᵥ x) := (Matrix.mulVec_mulVec x U Uᵀ).symm
  _ = ∑ i, ip x (u i) • u i := h2

/-- The key geometric step: an orthonormal triple on which `F` takes the
constant value `μ`. -/
theorem exists_triple {a b : Point} {μ : ℝ} (_hμ : 0 < μ)
    (hsum : ∑ i, F a b (e i) = 3 * μ) :
    ∃ u : Fin 3 → Point, (∀ i, ip (u i) (u i) = 1) ∧
      (∀ i j, i ≠ j → ip (u i) (u j) = 0) ∧ (∀ i, F a b (u i) = μ) := by
  classical
  obtain ⟨i₀, -, hi₀⟩ :=
    Finset.exists_max_image Finset.univ (fun i => F a b (e i)) Finset.univ_nonempty
  obtain ⟨i₁, -, hi₁⟩ :=
    Finset.exists_min_image Finset.univ (fun i => F a b (e i)) Finset.univ_nonempty
  have hle1 : μ ≤ F a b (e i₀) := by
    have h := Finset.sum_le_card_nsmul Finset.univ (fun i => F a b (e i))
      (F a b (e i₀)) hi₀
    rw [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat] at h
    linarith [hsum, h]
  have hle2 : F a b (e i₁) ≤ μ := by
    have h := Finset.card_nsmul_le_sum Finset.univ (fun i => F a b (e i))
      (F a b (e i₁)) hi₁
    rw [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat] at h
    linarith [hsum, h]
  have hee : ∀ i, ip (e i) (e i) = 1 := fun i => by rw [ip_e_e]; simp
  have hee' : ∀ i j, i ≠ j → ip (e i) (e j) = 0 := fun i j h => by
    rw [ip_e_e, if_neg h]
  by_cases hEq : F a b (e i₀) = F a b (e i₁)
  · -- All basis values are equal to `μ`; the standard basis works.
    have hμ0 : F a b (e i₀) = μ := by linarith [hle1, hle2, hEq]
    have hGE : ∀ j, F a b (e j) = μ := by
      intro j
      have h1 := hi₁ j (Finset.mem_univ j)
      have h2 := hi₀ j (Finset.mem_univ j)
      linarith [h1, h2, hμ0, hEq]
    exact ⟨e, hee, hee', hGE⟩
  · -- Otherwise rotate in coordinate planes twice, using the IVT.
    have hne : i₀ ≠ i₁ := fun h => hEq (h ▸ rfl)
    have hμmem : μ ∈ Set.uIcc (F a b (e i₀)) (F a b (e i₁)) :=
      Set.mem_uIcc.mpr (Or.inr ⟨hle2, hle1⟩)
    obtain ⟨θ, hθ⟩ := exists_F_rot_eq a b (e i₀) (e i₁) hμmem
    obtain ⟨k, hki₀, hki₁⟩ : ∃ k : Fin 3, k ≠ i₀ ∧ k ≠ i₁ := by
      fin_cases i₀ <;> fin_cases i₁ <;> first
        | exact absurd rfl hne
        | exact ⟨0, by decide, by decide⟩
        | exact ⟨1, by decide, by decide⟩
        | exact ⟨2, by decide, by decide⟩
    have hcard3 : ({i₀, i₁, k} : Finset (Fin 3)).card = 3 := by
      simp [Finset.card_insert_of_notMem, hne, hki₀.symm, hki₁.symm]
    have huniv : (Finset.univ : Finset (Fin 3)) = {i₀, i₁, k} := by
      symm
      apply Finset.eq_univ_of_card
      rw [hcard3, Fintype.card_fin]
    have hGik : F a b (e i₀) + F a b (e i₁) + F a b (e k) = 3 * μ := by
      rw [← hsum, huniv]
      simp [Finset.sum_insert, Finset.sum_singleton, hne, hki₀.symm, hki₁.symm]
      ring
    set u₃ := rot (e i₀) (e i₁) θ with hu₃
    set w := rot (e i₀) (e i₁) (θ + Real.pi / 2) with hw
    have hF₃ : F a b u₃ = μ := hθ
    have hFw : F a b w = F a b (e i₀) + F a b (e i₁) - μ := by
      have h := F_rot_add a b (e i₀) (e i₁) θ
      linarith [hF₃, h]
    have hu₃sq : ip u₃ u₃ = 1 := ip_rot_self (hee i₀) (hee i₁) (hee' i₀ i₁ hne) θ
    have hwsq : ip w w = 1 := ip_rot_self (hee i₀) (hee i₁) (hee' i₀ i₁ hne) _
    have hu₃w : ip u₃ w = 0 := perp_rot (hee i₀) (hee i₁) (hee' i₀ i₁ hne) θ
    have hkw : ip (e k) w = 0 := by
      rw [hw, ip_rot_right, hee' k i₀ hki₀, hee' k i₁ hki₁]
      ring
    have hku₃ : ip (e k) u₃ = 0 := by
      rw [hu₃, ip_rot_right, hee' k i₀ hki₀, hee' k i₁ hki₁]
      ring
    have hGk : F a b (e k) = 2 * μ - F a b w := by linarith [hFw, hGik]
    have hμmem2 : μ ∈ Set.uIcc (F a b (e k)) (F a b w) := by
      rw [Set.mem_uIcc]
      by_cases h : F a b (e k) ≤ μ
      · exact Or.inl ⟨h, by linarith [hGk]⟩
      · exact Or.inr ⟨by linarith [hGk], le_of_not_ge h⟩
    obtain ⟨φ, hφ⟩ := exists_F_rot_eq a b (e k) w hμmem2
    set u₁ := rot (e k) w φ with hu₁
    set u₂ := rot (e k) w (φ + Real.pi / 2) with hu₂
    have hF₁ : F a b u₁ = μ := hφ
    have hF₂ : F a b u₂ = μ := by
      have h := F_rot_add a b (e k) w φ
      linarith [hGk, h, hF₁]
    have hu₁sq : ip u₁ u₁ = 1 := ip_rot_self (hee k) hwsq hkw φ
    have hu₂sq : ip u₂ u₂ = 1 := ip_rot_self (hee k) hwsq hkw _
    have hu₁u₂ : ip u₁ u₂ = 0 := perp_rot (hee k) hwsq hkw φ
    have hu₁u₃ : ip u₁ u₃ = 0 := by
      rw [hu₁, ip_rot_left, hku₃, ip_comm w u₃, hu₃w]
      ring
    have hu₂u₃ : ip u₂ u₃ = 0 := by
      rw [hu₂, ip_rot_left, hku₃, ip_comm w u₃, hu₃w]
      ring
    refine ⟨![u₁, u₂, u₃], ?_, ?_, ?_⟩
    · intro i
      fin_cases i <;> first
        | exact hu₁sq
        | exact hu₂sq
        | exact hu₃sq
    · intro i j hij
      fin_cases i <;> fin_cases j <;> first
        | exact absurd rfl hij
        | exact hu₁u₂
        | exact hu₁u₃
        | exact hu₂u₃
        | (rw [ip_comm]; exact hu₁u₂)
        | (rw [ip_comm]; exact hu₁u₃)
        | (rw [ip_comm]; exact hu₂u₃)
    · intro i
      fin_cases i <;> first
        | exact hF₁
        | exact hF₂
        | exact hF₃

/-- Assembling the parallelepiped from the orthonormal triple. -/
theorem endgame {O P : Point} {R : ℝ} (hR : 0 < R)
    (u : Fin 3 → Point) (hn : ∀ i, ip (u i) (u i) = 1)
    (ho : ∀ i j, i ≠ j → ip (u i) (u j) = 0)
    {Q : Point} (hF : ∀ i, F (P - O) (Q - O) (u i) = R ^ 2 - sqNorm (P - O)) :
    ∃ U V W : Point, Dist U O = R ∧ Dist V O = R ∧ Dist W O = R ∧
      ip (U - P) (V - P) = 0 ∧ ip (U - P) (W - P) = 0 ∧
      ip (V - P) (W - P) = 0 ∧ Q = U + V + W - (2 : ℝ) • P := by
  set a := P - O with ha
  set b := Q - O with hb
  have hsphere : ∀ i, sqNorm (a + ip (b - a) (u i) • u i) = R ^ 2 := by
    intro i
    have h1 : ip b (u i) = ip (b - a) (u i) + ip a (u i) := by
      have h2 := ip_sub_left b a (u i)
      linarith [h2]
    have hF' := hF i
    rw [F, h1] at hF'
    have hn' : sqNorm (u i) = 1 := by rw [← ip_self]; exact hn i
    rw [sqNorm_add, sqNorm_smul, ip_smul_right, hn']
    linear_combination hF'
  refine ⟨P + ip (b - a) (u 0) • u 0, P + ip (b - a) (u 1) • u 1,
    P + ip (b - a) (u 2) • u 2, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hsub : P + ip (b - a) (u 0) • u 0 - O = a + ip (b - a) (u 0) • u 0 := by
      ext j
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ha]
      ring
    have hsp := hsphere 0
    rw [← hsub] at hsp
    show Real.sqrt (sqNorm (P + ip (b - a) (u 0) • u 0 - O)) = R
    rw [hsp, Real.sqrt_sq hR.le]
  · have hsub : P + ip (b - a) (u 1) • u 1 - O = a + ip (b - a) (u 1) • u 1 := by
      ext j
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ha]
      ring
    have hsp := hsphere 1
    rw [← hsub] at hsp
    show Real.sqrt (sqNorm (P + ip (b - a) (u 1) • u 1 - O)) = R
    rw [hsp, Real.sqrt_sq hR.le]
  · have hsub : P + ip (b - a) (u 2) • u 2 - O = a + ip (b - a) (u 2) • u 2 := by
      ext j
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ha]
      ring
    have hsp := hsphere 2
    rw [← hsub] at hsp
    show Real.sqrt (sqNorm (P + ip (b - a) (u 2) • u 2 - O)) = R
    rw [hsp, Real.sqrt_sq hR.le]
  · have hsub0 : P + ip (b - a) (u 0) • u 0 - P = ip (b - a) (u 0) • u 0 := by
      ext j
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have hsub1 : P + ip (b - a) (u 1) • u 1 - P = ip (b - a) (u 1) • u 1 := by
      ext j
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hsub0, hsub1, ip_smul_left, ip_smul_right, ho 0 1 (by decide)]
    ring
  · have hsub0 : P + ip (b - a) (u 0) • u 0 - P = ip (b - a) (u 0) • u 0 := by
      ext j
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have hsub2 : P + ip (b - a) (u 2) • u 2 - P = ip (b - a) (u 2) • u 2 := by
      ext j
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hsub0, hsub2, ip_smul_left, ip_smul_right, ho 0 2 (by decide)]
    ring
  · have hsub1 : P + ip (b - a) (u 1) • u 1 - P = ip (b - a) (u 1) • u 1 := by
      ext j
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have hsub2 : P + ip (b - a) (u 2) • u 2 - P = ip (b - a) (u 2) • u 2 := by
      ext j
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hsub1, hsub2, ip_smul_left, ip_smul_right, ho 1 2 (by decide)]
    ring
  · have hexp := expansion u hn ho (b - a)
    rw [Fin.sum_univ_three] at hexp
    have h2P : (2 : ℝ) • P = P + P := by
      ext j
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
      ring
    have hcomb : P + ip (b - a) (u 0) • u 0 + (P + ip (b - a) (u 1) • u 1) +
        (P + ip (b - a) (u 2) • u 2) - (2 : ℝ) • P =
        P + (ip (b - a) (u 0) • u 0 + ip (b - a) (u 1) • u 1 +
          ip (b - a) (u 2) • u 2) := by
      rw [h2P]
      abel
    rw [hcomb, ← hexp, hb, ha]
    abel

/-- The forward direction: every such `Q` lies on the claimed sphere. -/
theorem forward {O P : Point} {R : ℝ} (hR : 0 < R)
    {U V W Q : Point} (hU : Dist U O = R) (hV : Dist V O = R) (hW : Dist W O = R)
    (hUV : ip (U - P) (V - P) = 0) (hUW : ip (U - P) (W - P) = 0)
    (hVW : ip (V - P) (W - P) = 0) (hQ : Q = U + V + W - (2 : ℝ) • P) :
    Dist Q O = Real.sqrt (3 * R ^ 2 - 2 * (Dist P O) ^ 2) := by
  set a := P - O with ha
  set x := U - P with hx
  set y := V - P with hy
  set z := W - P with hz
  have hUO : U - O = a + x := by
    ext j
    simp only [Pi.add_apply, Pi.sub_apply, ha, hx]
    ring
  have hVO : V - O = a + y := by
    ext j
    simp only [Pi.add_apply, Pi.sub_apply, ha, hy]
    ring
  have hWO : W - O = a + z := by
    ext j
    simp only [Pi.add_apply, Pi.sub_apply, ha, hz]
    ring
  have hUsq : sqNorm (U - O) = R ^ 2 := by
    have h1 : Dist U O = Real.sqrt (sqNorm (U - O)) := rfl
    rw [h1, Real.sqrt_eq_iff_mul_self_eq (sqNorm_nonneg _) hR.le] at hU
    rw [← pow_two] at hU
    exact hU
  have hVsq : sqNorm (V - O) = R ^ 2 := by
    have h1 : Dist V O = Real.sqrt (sqNorm (V - O)) := rfl
    rw [h1, Real.sqrt_eq_iff_mul_self_eq (sqNorm_nonneg _) hR.le] at hV
    rw [← pow_two] at hV
    exact hV
  have hWsq : sqNorm (W - O) = R ^ 2 := by
    have h1 : Dist W O = Real.sqrt (sqNorm (W - O)) := rfl
    rw [h1, Real.sqrt_eq_iff_mul_self_eq (sqNorm_nonneg _) hR.le] at hW
    rw [← pow_two] at hW
    exact hW
  have hx' : sqNorm x + 2 * ip a x = R ^ 2 - sqNorm a := by
    rw [hUO, sqNorm_add] at hUsq
    linarith [hUsq]
  have hy' : sqNorm y + 2 * ip a y = R ^ 2 - sqNorm a := by
    rw [hVO, sqNorm_add] at hVsq
    linarith [hVsq]
  have hz' : sqNorm z + 2 * ip a z = R ^ 2 - sqNorm a := by
    rw [hWO, sqNorm_add] at hWsq
    linarith [hWsq]
  have hQO : Q - O = a + x + y + z := by
    rw [hQ]
    ext j
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ha, hx, hy, hz]
    ring
  have hkey : sqNorm (a + x + y + z) =
      sqNorm a + (sqNorm x + 2 * ip a x) + (sqNorm y + 2 * ip a y) +
        (sqNorm z + 2 * ip a z) +
      2 * (ip x y + ip x z + ip y z) := by
    simp only [sqNorm_add, ip_add_left]
    ring
  rw [hx', hy', hz', hUV, hUW, hVW] at hkey
  have hfin : sqNorm (Q - O) = 3 * R ^ 2 - 2 * sqNorm a := by
    rw [hQO, hkey]
    ring
  show Real.sqrt (sqNorm (Q - O)) = Real.sqrt (3 * R ^ 2 - 2 * (Dist P O) ^ 2)
  rw [hfin, show Dist P O = Real.sqrt (sqNorm a) from rfl,
    Real.sq_sqrt (sqNorm_nonneg a)]

/-- The backward direction: every point of the claimed sphere is attained. -/
theorem backward {O P : Point} {R : ℝ} (hR : 0 < R) (hP : Dist P O < R)
    {Q : Point} (hQ : Dist Q O = Real.sqrt (3 * R ^ 2 - 2 * (Dist P O) ^ 2)) :
    ∃ U V W : Point, Dist U O = R ∧ Dist V O = R ∧ Dist W O = R ∧
      ip (U - P) (V - P) = 0 ∧ ip (U - P) (W - P) = 0 ∧
      ip (V - P) (W - P) = 0 ∧ Q = U + V + W - (2 : ℝ) • P := by
  set a := P - O with ha
  set b := Q - O with hb
  have hsa : sqNorm a < R ^ 2 := by
    have h1 : Dist P O = Real.sqrt (sqNorm a) := rfl
    rw [h1, Real.sqrt_lt' hR] at hP
    exact hP
  have hR2 : 0 ≤ 3 * R ^ 2 - 2 * sqNorm a := by nlinarith [hsa, hR]
  have hQ2 : Real.sqrt (sqNorm b) = Real.sqrt (3 * R ^ 2 - 2 * sqNorm a) := by
    have h := hQ
    change Real.sqrt (sqNorm b) =
      Real.sqrt (3 * R ^ 2 - 2 * (Real.sqrt (sqNorm a)) ^ 2) at h
    rwa [Real.sq_sqrt (sqNorm_nonneg a)] at h
  have hsb : sqNorm b = 3 * R ^ 2 - 2 * sqNorm a := by
    have h3 := congrArg (· ^ 2) hQ2
    rw [Real.sq_sqrt (sqNorm_nonneg b), Real.sq_sqrt hR2] at h3
    exact h3
  set μ := R ^ 2 - sqNorm a with hμdef
  have hμ : 0 < μ := by
    rw [hμdef]
    linarith [hsa]
  have hsum : ∑ i, F a b (e i) = 3 * μ := by
    have h1 : ∑ i, F a b (e i) = sqNorm b - sqNorm a := by
      simp [F, ip_e, sqNorm, Finset.sum_sub_distrib]
    rw [h1, hsb, hμdef]
    ring
  obtain ⟨u, hn, ho, hF⟩ := exists_triple hμ hsum
  exact endgame hR u hn ho hF

snip end

/-- The radius of the locus sphere. -/
noncomputable determine locusRadius (R d : ℝ) : ℝ := Real.sqrt (3 * R ^ 2 - 2 * d ^ 2)

problem imo1978_p2 {O P : Point} {R : ℝ} (hR : 0 < R) (hP : Dist P O < R) :
    {Q : Point | ∃ U V W : Point,
        Dist U O = R ∧ Dist V O = R ∧ Dist W O = R ∧
        ip (U - P) (V - P) = 0 ∧ ip (U - P) (W - P) = 0 ∧
        ip (V - P) (W - P) = 0 ∧ Q = U + V + W - (2 : ℝ) • P} =
      {Q : Point | Dist Q O = locusRadius R (Dist P O)} := by
  ext Q
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨U, V, W, hU, hV, hW, hUV, hUW, hVW, rfl⟩
    exact forward hR hU hV hW hUV hUW hVW rfl
  · intro hQ
    exact backward hR hP hQ

end Imo1978P2
