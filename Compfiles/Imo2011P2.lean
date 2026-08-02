/-
Copyright (c) 2026 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw, Kimi K3
-/

module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.RingTheory.SimpleRing.Principal
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics, .Geometry] }

/-!
# International Mathematical Olympiad 2011, Problem 2

Let S be a finite set of at least two points in the plane. Assume that
no three points of S are collinear. A windmill is a process that starts
with a line ℓ going through a single point P ∈ S. The line rotates
clockwise about the pivot P until the first time that the line meets
some other point belonging to S. This point, Q, takes over as the new
pivot, and the line now rotates clockwise about Q, until it next meets
a point of S. This process continues indefinitely.
Show that we can choose a point P in S and a line ℓ going through P
such that the resulting windmill uses each point of S as a pivot
infinitely many times.
-/

namespace Imo2011P2

open Real

/-- The 2-dimensional cross product of two complex numbers:
`cross u v = |u| |v| sin(arg v - arg u)`. Positive iff `v` is
strictly counterclockwise of `u` (when both are nonzero). -/
def cross (u v : ℂ) : ℝ := (star u * v).im

/-- The signed side of point `x` with respect to the directed line
through `c` in direction `θ` (the direction being the unit vector
`exp (θ * I)`). Positive iff `x` lies strictly to the left of the line. -/
noncomputable def side (θ : ℝ) (c x : ℂ) : ℝ :=
  cross (Complex.exp (θ * Complex.I)) (x - c)

/-- The clockwise angle (in `(0, π]`) from the (unoriented) line
direction `θ` to the direction from `c` to `x`. -/
noncomputable def cw (θ : ℝ) (c x : ℂ) : ℝ :=
  toIocMod Real.pi_pos 0 (θ - (x - c).arg)

/-- The first point of `S \ {b}` met by a line in direction `dir`
rotating clockwise about `b`. (Returns `b` if `S \ {b}` is empty.) -/
noncomputable def firstHit (S : Finset ℂ) (b : ℂ) (dir : ℝ) : ℂ :=
  if h : (S \ {b}).Nonempty then
    Classical.choose (Finset.exists_min_image (S \ {b}) (fun x ↦ cw dir b x) h)
  else b

/-- The sequence of pivots of the windmill process that starts with the
line through `P` in direction `θ₀`. -/
noncomputable def pivots (S : Finset ℂ) (P : ℂ) (θ₀ : ℝ) : ℕ → ℂ
  | 0 => P
  | 1 => firstHit S P θ₀
  | n + 2 => firstHit S (pivots S P θ₀ (n + 1))
      ((pivots S P θ₀ n - pivots S P θ₀ (n + 1)).arg)

snip begin

section BasicAPI

@[simp] theorem cross_self (u : ℂ) : cross u u = 0 := by
  have h : star u * u = (Complex.normSq u : ℝ) := by
    rw [Complex.star_def, mul_comm]; exact Complex.mul_conj u
  rw [cross, h, Complex.ofReal_im]

theorem cross_smul_right (t : ℝ) (u v : ℂ) : cross u (t • v) = t * cross u v := by
  rw [cross, cross, Complex.real_smul, ← mul_assoc, mul_comm (star u) (t : ℂ), mul_assoc]
  simp [Complex.mul_im]

theorem cross_neg_left (u v : ℂ) : cross (-u) v = -cross u v := by
  rw [cross, cross, star_neg, neg_mul]; simp

theorem cross_sub_left (u v w : ℂ) : cross u (v - w) = cross u v - cross u w := by
  rw [cross, cross, cross, mul_sub, Complex.sub_im]

theorem cross_add_left (u v w : ℂ) : cross u (v + w) = cross u v + cross u w := by
  rw [cross, cross, cross, mul_add, Complex.add_im]

theorem cross_eq_zero_iff {u : ℂ} (hu : u ≠ 0) (v : ℂ) :
    cross u v = 0 ↔ ∃ t : ℝ, v = t • u := by
  constructor
  · intro h
    have him : (star u * v).im = 0 := h
    have hre : star u * v = ((star u * v).re : ℂ) := by
      apply Complex.ext
      · simp
      · rw [Complex.ofReal_im]; exact him
    have hc : star u * u = ((Complex.normSq u : ℝ) : ℂ) := by
      rw [Complex.star_def, mul_comm]; exact Complex.mul_conj u
    have hn : (Complex.normSq u : ℝ) ≠ 0 := ne_of_gt (Complex.normSq_pos.mpr hu)
    refine ⟨(star u * v).re / Complex.normSq u, ?_⟩
    have e : star u * (((star u * v).re / Complex.normSq u : ℝ) • u) = star u * v := by
      rw [Complex.real_smul, mul_left_comm, hc, ← Complex.ofReal_mul,
        div_mul_cancel₀ _ hn]
      exact hre.symm
    have := mul_left_cancel₀ (star_ne_zero.mpr hu) e
    exact this.symm
  · rintro ⟨t, rfl⟩
    rw [cross_smul_right, cross_self, mul_zero]

theorem collinear_of_cross_eq_zero {a b c : ℂ} (h : cross (b - a) (c - a) = 0) :
    Collinear ℝ {a, b, c} := by
  by_cases hba : b = a
  · rw [hba, Set.insert_idem]
    exact collinear_pair ℝ _ _
  · obtain ⟨t, ht⟩ := (cross_eq_zero_iff (sub_ne_zero.mpr hba) (c - a)).mp h
    rw [collinear_iff_of_mem (Set.mem_insert a {b, c})]
    refine ⟨b - a, fun p hp ↦ ?_⟩
    rcases Set.mem_insert_iff.mp hp with rfl | hp
    · exact ⟨0, by simp⟩
    rcases Set.mem_insert_iff.mp hp with rfl | hp
    · exact ⟨1, by simp⟩
    · rw [Set.mem_singleton_iff] at hp; subst hp
      refine ⟨t, ?_⟩
      rw [← ht]
      simp

theorem cross_ne_of_not_collinear {a b c : ℂ} (h : ¬ Collinear ℝ {a, b, c}) :
    cross (b - a) (c - a) ≠ 0 :=
  fun hc ↦ h (collinear_of_cross_eq_zero hc)

/-- Congruence of angles modulo `π`. -/
def ModPi (a b : ℝ) : Prop := ∃ k : ℤ, a = b + k * π

theorem modPi_refl (a : ℝ) : ModPi a a := ⟨0, by ring⟩

theorem modPi_symm {a b : ℝ} (h : ModPi a b) : ModPi b a := by
  obtain ⟨k, rfl⟩ := h; exact ⟨-k, by push_cast; ring⟩

theorem modPi_trans {a b c : ℝ} (h1 : ModPi a b) (h2 : ModPi b c) : ModPi a c := by
  obtain ⟨k1, rfl⟩ := h1; obtain ⟨k2, rfl⟩ := h2; exact ⟨k1 + k2, by push_cast; ring⟩

theorem modPi_add (a : ℝ) {b c : ℝ} (h : ModPi b c) : ModPi (a + b) (a + c) := by
  obtain ⟨k, rfl⟩ := h; exact ⟨k, by ring⟩

theorem modPi_sub (a : ℝ) {b c : ℝ} (h : ModPi b c) : ModPi (a - b) (a - c) := by
  obtain ⟨k, rfl⟩ := h; exact ⟨-k, by push_cast; ring⟩

theorem modPi_sub_right {b c : ℝ} (h : ModPi b c) (a : ℝ) : ModPi (b - a) (c - a) := by
  obtain ⟨k, rfl⟩ := h; exact ⟨k, by ring⟩

theorem modPi_add_pi (a : ℝ) : ModPi (a + π) a := ⟨1, by ring⟩

theorem sin_add_int_mul_pi (x : ℝ) (k : ℤ) :
    Real.sin (x + k * π) = (-1 : ℝ) ^ k * Real.sin x := by
  rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · have h1 : x + ↑(m + m) * π = x + ↑m * (2 * π) := by push_cast; ring
    rw [h1, Real.sin_add_int_mul_two_pi, Even.neg_one_zpow ⟨m, rfl⟩, one_mul]
  · have h1 : x + ↑(2 * m + 1) * π = (x + π) + ↑m * (2 * π) := by push_cast; ring
    rw [h1, Real.sin_add_int_mul_two_pi, Real.sin_add_pi, Odd.neg_one_zpow ⟨m, rfl⟩]
    ring

theorem star_exp_ofReal_mul_I (θ : ℝ) :
    star (Complex.exp (θ * Complex.I)) = Complex.exp (-(θ * Complex.I)) := by
  have e : -(θ * Complex.I) = (-θ : ℝ) * Complex.I := by push_cast; ring
  rw [e, Complex.star_def]
  apply Complex.ext
  · rw [Complex.conj_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_re,
      Real.cos_neg]
  · rw [Complex.conj_im, Complex.exp_ofReal_mul_I_im, Complex.exp_ofReal_mul_I_im,
      Real.sin_neg]

theorem cross_exp (θ : ℝ) (x : ℂ) :
    cross (Complex.exp (θ * Complex.I)) x = ‖x‖ * Real.sin (x.arg - θ) := by
  have hx2 : x = ↑‖x‖ * Complex.exp (↑x.arg * Complex.I) :=
    (Complex.norm_mul_exp_arg_mul_I x).symm
  conv_lhs => rw [hx2]
  have h : -(θ * Complex.I) + ↑x.arg * Complex.I = ↑(x.arg - θ) * Complex.I := by
    push_cast; ring
  rw [cross, star_exp_ofReal_mul_I, mul_left_comm, ← Complex.exp_add, h,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
    Complex.exp_ofReal_mul_I_im]

theorem side_eq_norm_sin {θ : ℝ} {c x : ℂ} (_hx : x ≠ c) :
    side θ c x = ‖x - c‖ * Real.sin ((x - c).arg - θ) := by
  rw [side, cross_exp]

theorem side_eq_zero_iff_modPi {θ : ℝ} {c x : ℂ} (hx : x ≠ c) :
    side θ c x = 0 ↔ ModPi (x - c).arg θ := by
  rw [side_eq_norm_sin hx, mul_eq_zero]
  have hn : ‖x - c‖ ≠ 0 := by
    rw [norm_ne_zero_iff]; exact sub_ne_zero.mpr hx
  constructor
  · rintro (h | h)
    · exact absurd h hn
    · obtain ⟨n, hn2⟩ := Real.sin_eq_zero_iff.mp h
      exact ⟨n, by rw [hn2]; ring⟩
  · rintro ⟨k, hk⟩
    right
    rw [hk, add_sub_cancel_left]
    exact Real.sin_eq_zero_iff.mpr ⟨k, rfl⟩

theorem side_add_pi (θ : ℝ) (c x : ℂ) : side (θ + π) c x = -side θ c x := by
  have e1 : ((θ + π : ℝ) : ℂ) * Complex.I =
      (θ : ℂ) * Complex.I + (π : ℂ) * Complex.I := by
    push_cast; ring
  have h : Complex.exp ((θ + π : ℝ) * Complex.I) = -Complex.exp (θ * Complex.I) := by
    rw [e1, Complex.exp_add, Complex.exp_pi_mul_I, mul_neg, mul_one]
  rw [side, side, h, cross_neg_left]

theorem smul_of_modPi_arg {x : ℂ} {θ : ℝ} (h : ModPi x.arg θ) :
    ∃ t : ℝ, x = t • Complex.exp (θ * Complex.I) := by
  obtain ⟨k, hk⟩ := h
  have h2 : Complex.exp (x.arg * Complex.I) =
      Complex.exp (θ * Complex.I) * (Complex.exp ((π : ℂ) * Complex.I)) ^ k := by
    have e1 : (x.arg : ℂ) * Complex.I =
        (θ : ℂ) * Complex.I + (k : ℂ) * ((π : ℂ) * Complex.I) := by
      rw [hk]; push_cast; ring
    rw [e1, Complex.exp_add, Complex.exp_int_mul]
  have e1 : Complex.exp (x.arg * Complex.I) =
      Complex.exp (θ * Complex.I) * (-1 : ℂ) ^ k := by
    rw [h2, Complex.exp_pi_mul_I]
  refine ⟨‖x‖ * (-1 : ℝ) ^ k, ?_⟩
  rw [Complex.real_smul]
  calc x = ↑‖x‖ * Complex.exp (x.arg * Complex.I) :=
        (Complex.norm_mul_exp_arg_mul_I x).symm
    _ = ↑‖x‖ * (Complex.exp (θ * Complex.I) * (-1 : ℂ) ^ k) := by rw [e1]
    _ = ↑(‖x‖ * (-1 : ℝ) ^ k) * Complex.exp (θ * Complex.I) := by
      push_cast; ring

theorem side_center_indep {θ : ℝ} {c c' x : ℂ} {t : ℝ}
    (h : c' - c = t • Complex.exp (θ * Complex.I)) : side θ c x = side θ c' x := by
  have e : x - c = (x - c') + (c' - c) := by ring
  rw [side, side, e, cross_add_left, h, cross_smul_right, cross_self, mul_zero, add_zero]

theorem smul_of_modPi_arg_sub {x y : ℂ} (hy : y ≠ 0) (h : ModPi x.arg y.arg) :
    ∃ t : ℝ, x = t • y := by
  obtain ⟨ty, hty⟩ := smul_of_modPi_arg (x := y) (θ := y.arg) (modPi_refl y.arg)
  obtain ⟨tx, htx⟩ := smul_of_modPi_arg (x := x) (θ := y.arg) h
  have htyne : ty ≠ 0 := by
    rintro rfl
    rw [hty, zero_smul] at hy
    exact hy rfl
  refine ⟨tx / ty, ?_⟩
  rw [hty, smul_smul, div_mul_cancel₀ _ htyne]
  exact htx

section CwAPI

theorem cw_mem_Ioc (θ : ℝ) (c x : ℂ) : cw θ c x ∈ Set.Ioc 0 π := by
  have h := toIocMod_mem_Ioc Real.pi_pos (0 : ℝ) (θ - (x - c).arg)
  rwa [zero_add] at h

theorem zero_lt_cw (θ : ℝ) (c x : ℂ) : 0 < cw θ c x := (cw_mem_Ioc θ c x).1

theorem cw_le_pi (θ : ℝ) (c x : ℂ) : cw θ c x ≤ π := (cw_mem_Ioc θ c x).2

theorem cw_spec (θ : ℝ) (c x : ℂ) : ModPi (θ - cw θ c x) (x - c).arg := by
  have h : toIocMod Real.pi_pos 0 (θ - (x - c).arg) = cw θ c x := rfl
  obtain ⟨z, hz⟩ := ((toIocMod_eq_iff Real.pi_pos).mp h).2
  exact ⟨z, by rw [zsmul_eq_mul] at hz; linarith [hz]⟩

theorem cw_eq_of_modPi {θ₁ θ₂ : ℝ} (h : ModPi θ₁ θ₂) (c x : ℂ) :
    cw θ₁ c x = cw θ₂ c x := by
  obtain ⟨k, rfl⟩ := h
  unfold cw
  have e : θ₂ + ↑k * π - (x - c).arg = (θ₂ - (x - c).arg) + k • π := by
    rw [zsmul_eq_mul]; ring
  rw [e, toIocMod_add_zsmul]

theorem cw_self_arg (c x : ℂ) : cw (x - c).arg c x = π := by
  unfold cw
  rw [sub_self, toIocMod_apply_left Real.pi_pos, zero_add]

theorem cw_eq_pi_of_modPi {θ : ℝ} {c x : ℂ} (h : ModPi (x - c).arg θ) :
    cw θ c x = π := by
  rw [cw_eq_of_modPi (modPi_symm h), cw_self_arg]

end CwAPI

section FirstHit

theorem sdiff_singleton_nonempty {S : Finset ℂ} {b : ℂ} (_hb : b ∈ S)
    (h2 : 2 ≤ S.card) : (S \ {b}).Nonempty := by
  have h1c : 1 < S.card := by omega
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp h1c
  by_cases hxb : x = b
  · exact ⟨y, Finset.mem_sdiff.mpr
      ⟨hy, fun h ↦ hxy (hxb.trans (Finset.mem_singleton.mp h).symm)⟩⟩
  · exact ⟨x, Finset.mem_sdiff.mpr ⟨hx, fun h ↦ hxb (Finset.mem_singleton.mp h)⟩⟩

theorem firstHit_mem {S : Finset ℂ} {b : ℂ} (h : (S \ {b}).Nonempty) (dir : ℝ) :
    firstHit S b dir ∈ S \ {b} := by
  rw [firstHit, dif_pos h]
  exact (Classical.choose_spec
    (Finset.exists_min_image (S \ {b}) (fun x ↦ cw dir b x) h)).1

theorem firstHit_le {S : Finset ℂ} {b : ℂ} (h : (S \ {b}).Nonempty) (dir : ℝ)
    {y : ℂ} (hy : y ∈ S \ {b}) :
    cw dir b (firstHit S b dir) ≤ cw dir b y := by
  rw [firstHit, dif_pos h]
  exact (Classical.choose_spec
    (Finset.exists_min_image (S \ {b}) (fun x ↦ cw dir b x) h)).2 y hy

theorem firstHit_ne {S : Finset ℂ} {b : ℂ} (h : (S \ {b}).Nonempty) (dir : ℝ) :
    firstHit S b dir ≠ b := by
  have hm := firstHit_mem h dir
  rw [Finset.mem_sdiff] at hm
  exact fun hb ↦ hm.2 (Finset.mem_singleton.mpr hb)

end FirstHit

theorem modPi_arg_neg {z : ℂ} (hz : z ≠ 0) : ModPi (-z).arg z.arg := by
  have hz2 : -z ≠ 0 := neg_ne_zero.mpr hz
  rcases lt_trichotomy z.im 0 with h | h | h
  · rw [Complex.arg_neg_eq_arg_add_pi_of_im_neg h]
    exact modPi_add_pi z.arg
  · have harg : ∀ w : ℂ, w ≠ 0 → w.im = 0 → w.arg = 0 ∨ w.arg = π := by
      intro w hw him
      by_cases h0 : w.arg = 0
      · exact Or.inl h0
      · right
        have h2 : 0 ≤ w.arg := Complex.arg_nonneg_iff.mpr (le_of_eq him.symm)
        rcases eq_or_lt_of_le (Complex.arg_le_pi w) with h3 | h3
        · exact h3
        · exfalso
          rcases Complex.arg_lt_pi_iff.mp h3 with h4 | h4
          · exact h0 (Complex.arg_eq_zero_iff.mpr ⟨h4, him⟩)
          · exact h4 him
    have him2 : (-z).im = 0 := by rw [Complex.neg_im, h, neg_zero]
    rcases harg z hz h with h1 | h1 <;> rcases harg (-z) hz2 him2 with h2 | h2 <;>
      rw [h1, h2]
    · exact modPi_refl 0
    · exact ⟨1, by ring⟩
    · exact ⟨-1, by ring⟩
    · exact modPi_refl π
  · rw [Complex.arg_neg_eq_arg_sub_pi_of_im_pos h]
    exact ⟨-1, by ring⟩

section WindmillSetup

theorem cw_inj {S : Finset ℂ}
    (hS3 : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → a ≠ c → b ≠ c →
      ¬ Collinear ℝ {a, b, c})
    {θ : ℝ} {c x₁ x₂ : ℂ} (hc : c ∈ S)
    (hx1 : x₁ ∈ S \ {c}) (hx2 : x₂ ∈ S \ {c})
    (h : cw θ c x₁ = cw θ c x₂) : x₁ = x₂ := by
  have hx1ne : x₁ ≠ c :=
    fun he ↦ (Finset.mem_sdiff.mp hx1).2 (Finset.mem_singleton.mpr he)
  have hx2ne : x₂ ≠ c :=
    fun he ↦ (Finset.mem_sdiff.mp hx2).2 (Finset.mem_singleton.mpr he)
  have h' : toIocMod Real.pi_pos 0 (θ - (x₁ - c).arg) =
      toIocMod Real.pi_pos 0 (θ - (x₂ - c).arg) := h
  obtain ⟨n, hn⟩ := (toIocMod_eq_toIocMod Real.pi_pos).mp h'
  rw [zsmul_eq_mul] at hn
  have hm : ModPi (x₁ - c).arg (x₂ - c).arg := ⟨n, by linarith [hn]⟩
  by_cases h12 : x₁ = x₂
  · exact h12
  · exfalso
    obtain ⟨t, ht⟩ := smul_of_modPi_arg_sub (sub_ne_zero.mpr hx1ne) (modPi_symm hm)
    have hcross : cross (x₁ - c) (x₂ - c) = 0 := by
      rw [ht, cross_smul_right, cross_self, mul_zero]
    exact hS3 c hc x₁ (Finset.mem_sdiff.mp hx1).1 x₂ (Finset.mem_sdiff.mp hx2).1
      (fun he ↦ hx1ne he.symm) (fun he ↦ hx2ne he.symm) h12
      (collinear_of_cross_eq_zero hcross)

theorem firstHit_eq_of_le {S : Finset ℂ} (hS2 : 2 ≤ S.card)
    (hS3 : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → a ≠ c → b ≠ c →
      ¬ Collinear ℝ {a, b, c})
    {b y : ℂ} (hb : b ∈ S) (hy : y ∈ S \ {b}) {dir : ℝ}
    (hle : cw dir b y ≤ cw dir b (firstHit S b dir)) : y = firstHit S b dir := by
  have hn := sdiff_singleton_nonempty hb hS2
  have hm := firstHit_mem hn dir
  have hge := firstHit_le hn dir hy
  exact cw_inj hS3 hb hy hm (le_antisymm hle hge)

theorem firstHit_mem_S {S : Finset ℂ} (hS2 : 2 ≤ S.card) {b : ℂ} (hb : b ∈ S)
    (dir : ℝ) : firstHit S b dir ∈ S :=
  (Finset.mem_sdiff.mp (firstHit_mem (sdiff_singleton_nonempty hb hS2) dir)).1

end WindmillSetup

section WindmillDefs

variable (S : Finset ℂ) (P : ℂ) (θ₀ : ℝ)

/-- The direction of the (unoriented) windmill line just after the `n`-th hit. -/
noncomputable def linedir (n : ℕ) : ℝ :=
  match n with
  | 0 => θ₀
  | n + 1 => (pivots S P θ₀ n - pivots S P θ₀ (n + 1)).arg

/-- The clockwise rotation performed between the `n`-th and `n+1`-th hit. -/
noncomputable def rot (n : ℕ) : ℝ :=
  cw (linedir S P θ₀ n) (pivots S P θ₀ n) (pivots S P θ₀ (n + 1))

/-- The direction of the directed windmill line after `n` hits,
tracked continuously (so it strictly decreases). -/
noncomputable def dirseq (n : ℕ) : ℝ := θ₀ - ∑ j ∈ Finset.range n, rot S P θ₀ j

/-- The midpoint direction between the `n`-th and `n+1`-th hit. -/
noncomputable def mid (n : ℕ) : ℝ := (dirseq S P θ₀ n + dirseq S P θ₀ (n + 1)) / 2

/-- The number of points of `S` lying strictly to the left of the directed
windmill line between the `n`-th and `n+1`-th hit. -/
noncomputable def leftCount (n : ℕ) : ℕ :=
  (S.filter fun x ↦ 0 < side (mid S P θ₀ n) (pivots S P θ₀ n) x).card

end WindmillDefs

section Windmill

variable (S : Finset ℂ) (P : ℂ) (θ₀ : ℝ)

theorem pivots_zero : pivots S P θ₀ 0 = P := by rw [pivots]

theorem pivots_one : pivots S P θ₀ 1 = firstHit S P θ₀ := by rw [pivots]

theorem pivots_succ_succ (n : ℕ) :
    pivots S P θ₀ (n + 2) =
      firstHit S (pivots S P θ₀ (n + 1))
        ((pivots S P θ₀ n - pivots S P θ₀ (n + 1)).arg) := by
  rw [pivots]

theorem p_mem (hS2 : 2 ≤ S.card) (hP : P ∈ S) (n : ℕ) : pivots S P θ₀ n ∈ S := by
  induction n using Nat.twoStepInduction with
  | zero => rw [pivots_zero S P θ₀]; exact hP
  | one => rw [pivots_one S P θ₀]; exact firstHit_mem_S hS2 hP θ₀
  | more n _ ih2 =>
    rw [pivots_succ_succ S P θ₀]
    exact firstHit_mem_S hS2 ih2 _

theorem p_ne_succ (hS2 : 2 ≤ S.card) (hP : P ∈ S) (n : ℕ) :
    pivots S P θ₀ n ≠ pivots S P θ₀ (n + 1) := by
  cases n with
  | zero =>
    rw [pivots_zero S P θ₀, pivots_one S P θ₀]
    exact (firstHit_ne (sdiff_singleton_nonempty hP hS2) θ₀).symm
  | succ n =>
    rw [pivots_succ_succ S P θ₀]
    exact (firstHit_ne
      (sdiff_singleton_nonempty (p_mem S P θ₀ hS2 hP (n + 1)) hS2) _).symm

theorem dirseq_zero : dirseq S P θ₀ 0 = θ₀ := by simp [dirseq]

theorem dirseq_succ (n : ℕ) :
    dirseq S P θ₀ (n + 1) = dirseq S P θ₀ n - rot S P θ₀ n := by
  rw [dirseq, dirseq, Finset.sum_range_succ]
  ring

theorem rot_pos (n : ℕ) : 0 < rot S P θ₀ n := zero_lt_cw _ _ _

theorem rot_le_pi (n : ℕ) : rot S P θ₀ n ≤ π := cw_le_pi _ _ _

theorem dirseq_coherence (hS2 : 2 ≤ S.card)
    (hP : P ∈ S) (n : ℕ) :
    ModPi (dirseq S P θ₀ (n + 1))
      ((pivots S P θ₀ (n + 1) - pivots S P θ₀ n).arg) := by
  induction n with
  | zero =>
    have e : dirseq S P θ₀ 1 = θ₀ - rot S P θ₀ 0 := by
      rw [dirseq_succ S P θ₀ 0, dirseq_zero S P θ₀]
    rw [e, pivots_zero S P θ₀]
    have e2 : rot S P θ₀ 0 = cw θ₀ P (pivots S P θ₀ 1) := by
      unfold rot linedir
      rw [pivots_zero S P θ₀]
    rw [e2]
    exact cw_spec θ₀ P (pivots S P θ₀ 1)
  | succ n ih =>
    rw [dirseq_succ S P θ₀ _]
    have h1 : ModPi (linedir S P θ₀ (n + 1) - rot S P θ₀ (n + 1))
        ((pivots S P θ₀ (n + 2) - pivots S P θ₀ (n + 1)).arg) :=
      cw_spec (linedir S P θ₀ (n + 1)) (pivots S P θ₀ (n + 1)) (pivots S P θ₀ (n + 2))
    have hih : ModPi (dirseq S P θ₀ (n + 1)) (linedir S P θ₀ (n + 1)) := by
      have h2 : linedir S P θ₀ (n + 1) =
          (-(pivots S P θ₀ (n + 1) - pivots S P θ₀ n)).arg := by
        unfold linedir; rw [neg_sub]
      rw [h2]
      exact modPi_trans ih (modPi_symm
        (modPi_arg_neg (sub_ne_zero.mpr (p_ne_succ S P θ₀ hS2 hP n).symm)))
    exact modPi_trans (modPi_sub_right hih (rot S P θ₀ (n + 1))) h1

theorem linedir_modPi (hS2 : 2 ≤ S.card)
    (hP : P ∈ S) (n : ℕ) :
    ModPi (dirseq S P θ₀ (n + 1)) (linedir S P θ₀ (n + 1)) := by
  have hc := dirseq_coherence S P θ₀ hS2 hP n
  have h2 : linedir S P θ₀ (n + 1) =
      (-(pivots S P θ₀ (n + 1) - pivots S P θ₀ n)).arg := by
    unfold linedir; rw [neg_sub]
  rw [h2]
  exact modPi_trans hc (modPi_symm
    (modPi_arg_neg (sub_ne_zero.mpr (p_ne_succ S P θ₀ hS2 hP n).symm)))

theorem rot_eq_cw_dirseq (hS2 : 2 ≤ S.card)
    (hP : P ∈ S) (n : ℕ) :
    rot S P θ₀ n = cw (dirseq S P θ₀ n) (pivots S P θ₀ n) (pivots S P θ₀ (n + 1)) := by
  cases n with
  | zero =>
    rw [dirseq_zero S P θ₀]
    rfl
  | succ n =>
    unfold rot
    exact (cw_eq_of_modPi (linedir_modPi S P θ₀ hS2 hP n) _ _).symm

theorem cw_min (hS2 : 2 ≤ S.card)
    (hP : P ∈ S) (n : ℕ) {y : ℂ} (hy : y ∈ S \ {pivots S P θ₀ n}) :
    cw (dirseq S P θ₀ n) (pivots S P θ₀ n) (pivots S P θ₀ (n + 1)) ≤
      cw (dirseq S P θ₀ n) (pivots S P θ₀ n) y := by
  cases n with
  | zero =>
    rw [dirseq_zero S P θ₀, pivots_zero S P θ₀, pivots_one S P θ₀]
    exact firstHit_le (sdiff_singleton_nonempty hP hS2) θ₀ hy
  | succ n =>
    have hmod := linedir_modPi S P θ₀ hS2 hP n
    have e : linedir S P θ₀ (n + 1) =
        (pivots S P θ₀ n - pivots S P θ₀ (n + 1)).arg := rfl
    rw [cw_eq_of_modPi hmod (pivots S P θ₀ (n + 1)) (pivots S P θ₀ (n + 2)),
      cw_eq_of_modPi hmod (pivots S P θ₀ (n + 1)) y, e, pivots_succ_succ S P θ₀]
    exact firstHit_le (sdiff_singleton_nonempty
      (p_mem S P θ₀ hS2 hP (n + 1)) hS2) _ hy

theorem dirseq_strictAnti : StrictAnti (dirseq S P θ₀) := by
  apply strictAnti_nat_of_succ_lt
  intro n
  rw [dirseq_succ S P θ₀ _]
  exact sub_lt_self _ (rot_pos S P θ₀ n)

theorem dirseq_not_modPi (hS2 : 2 ≤ S.card)
    (hP : P ∈ S)
    (hgen : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ ModPi (x - y).arg θ₀)
    (n : ℕ) (k : ℤ) : dirseq S P θ₀ (n + 1) ≠ θ₀ + k * π := by
  intro h
  have hc := dirseq_coherence S P θ₀ hS2 hP n
  have h1 : ModPi (dirseq S P θ₀ (n + 1)) θ₀ := by
    rw [h]
    exact ⟨k, by ring⟩
  exact hgen _ (p_mem S P θ₀ hS2 hP (n + 1)) _ (p_mem S P θ₀ hS2 hP n)
    (p_ne_succ S P θ₀ hS2 hP n).symm (modPi_trans (modPi_symm hc) h1)

end Windmill

section Signs

variable (S : Finset ℂ) (P : ℂ) (θ₀ : ℝ)

theorem cross_smul_left (t : ℝ) (u v : ℂ) : cross (t • u) v = t * cross u v := by
  have e : star (t • u) = (t : ℂ) * star u := by
    rw [star_smul, star_trivial, Complex.real_smul]
  rw [cross, cross, e, mul_assoc]
  simp [Complex.mul_im]

theorem side_self (θ : ℝ) (c : ℂ) : side θ c c = 0 := by
  rw [side, sub_self]; simp [cross]

theorem side_pos_iff_of_no_zero {c x : ℂ} (hx : x ≠ c) {θ₁ θ₂ : ℝ} (hθ : θ₁ ≤ θ₂)
    (h1 : side θ₁ c x ≠ 0) (h2 : side θ₂ c x ≠ 0)
    (hmid : ∀ θ ∈ Set.Ioo θ₁ θ₂, side θ c x ≠ 0) :
    (0 < side θ₁ c x) ↔ (0 < side θ₂ c x) := by
  have hcont : Continuous (fun θ : ℝ ↦ side θ c x) := by
    have h2' : (fun θ : ℝ ↦ side θ c x) =
        fun θ ↦ ‖x - c‖ * Real.sin ((x - c).arg - θ) := by
      funext θ; exact side_eq_norm_sin hx
    rw [h2']
    exact continuous_const.mul
      (Real.continuous_sin.comp (continuous_const.sub continuous_id))
  by_cases h1' : 0 < side θ₁ c x
  · by_cases h2' : 0 < side θ₂ c x
    · exact ⟨fun _ ↦ h2', fun _ ↦ h1'⟩
    · exfalso
      have h2'' : side θ₂ c x < 0 := lt_of_le_of_ne (le_of_not_gt h2') h2
      have hmem : (0 : ℝ) ∈ Set.Icc (side θ₂ c x) (side θ₁ c x) :=
        Set.mem_Icc.mpr ⟨le_of_lt h2'', le_of_lt h1'⟩
      obtain ⟨θ, hθmem, hθ0⟩ := intermediate_value_Icc' hθ hcont.continuousOn hmem
      rw [Set.mem_Icc] at hθmem
      have hθ1 : θ₁ ≠ θ := fun he ↦ h1 (he ▸ hθ0)
      have hθ2 : θ₂ ≠ θ := fun he ↦ h2 (he ▸ hθ0)
      exact hmid θ ⟨lt_of_le_of_ne hθmem.1 hθ1, lt_of_le_of_ne hθmem.2 hθ2.symm⟩ hθ0
  · by_cases h2' : 0 < side θ₂ c x
    · exfalso
      have h1'' : side θ₁ c x < 0 := lt_of_le_of_ne (le_of_not_gt h1') h1
      have hmem : (0 : ℝ) ∈ Set.Icc (side θ₁ c x) (side θ₂ c x) :=
        Set.mem_Icc.mpr ⟨le_of_lt h1'', le_of_lt h2'⟩
      obtain ⟨θ, hθmem, hθ0⟩ := intermediate_value_Icc hθ hcont.continuousOn hmem
      rw [Set.mem_Icc] at hθmem
      have hθ1 : θ₁ ≠ θ := fun he ↦ h1 (he ▸ hθ0)
      have hθ2 : θ₂ ≠ θ := fun he ↦ h2 (he ▸ hθ0)
      exact hmid θ ⟨lt_of_le_of_ne hθmem.1 hθ1, lt_of_le_of_ne hθmem.2 hθ2.symm⟩ hθ0
    · exact ⟨fun h ↦ absurd h h1', fun h ↦ absurd h h2'⟩

theorem mid_mem_Ioo (n : ℕ) :
    mid S P θ₀ n ∈ Set.Ioo (dirseq S P θ₀ (n + 1)) (dirseq S P θ₀ n) := by
  have h1 : mid S P θ₀ n = dirseq S P θ₀ (n + 1) + rot S P θ₀ n / 2 := by
    rw [mid, dirseq_succ S P θ₀ n]; ring
  rw [h1, dirseq_succ S P θ₀ n]
  constructor <;> linarith [rot_pos S P θ₀ n]

theorem side_ne_zero_of_mem_Ioo (hS2 : 2 ≤ S.card) (hP : P ∈ S) (n : ℕ)
    {x : ℂ} (hx : x ∈ S \ {pivots S P θ₀ n}) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (dirseq S P θ₀ (n + 1)) (dirseq S P θ₀ n)) :
    side θ (pivots S P θ₀ n) x ≠ 0 := by
  intro hz
  have hxne : x ≠ pivots S P θ₀ n := fun he ↦
    (Finset.mem_sdiff.mp hx).2 (Finset.mem_singleton.mpr he)
  rw [side_eq_zero_iff_modPi hxne] at hz
  have hcs := cw_spec (dirseq S P θ₀ n) (pivots S P θ₀ n) x
  obtain ⟨k, hk⟩ := modPi_trans hcs hz
  have hcwpos : 0 < cw (dirseq S P θ₀ n) (pivots S P θ₀ n) x := zero_lt_cw _ _ _
  have hcwle : cw (dirseq S P θ₀ n) (pivots S P θ₀ n) x ≤ π := cw_le_pi _ _ _
  have hmin := cw_min S P θ₀ hS2 hP n hx
  rw [← rot_eq_cw_dirseq S P θ₀ hS2 hP n] at hmin
  have hlt : dirseq S P θ₀ (n + 1) < θ := hθ.1
  have hgt : θ < dirseq S P θ₀ n := hθ.2
  rw [dirseq_succ S P θ₀ n] at hlt
  rcases lt_trichotomy k 0 with hkn | hk0 | hkp
  · have h1 : (k : ℝ) * π ≤ -π := by
      have hk1 : (k : ℝ) ≤ -1 := by
        have h3 : k ≤ -1 := by omega
        exact_mod_cast h3
      nlinarith [Real.pi_pos]
    linarith [hk, hcwle, hgt, Real.pi_pos]
  · subst hk0
    rw [Int.cast_zero, zero_mul, add_zero] at hk
    linarith [hk, hmin, hgt, hlt]
  · have h1 : π ≤ (k : ℝ) * π := by
      have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hkp
      nlinarith [Real.pi_pos]
    have hrot := rot_le_pi S P θ₀ n
    linarith [hk, hcwpos, hgt, hlt, Real.pi_pos]

theorem side_dirseq_succ_ne_zero (hS2 : 2 ≤ S.card)
    (hS3 : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → a ≠ c → b ≠ c →
      ¬ Collinear ℝ {a, b, c})
    (hP : P ∈ S) (n : ℕ) {x : ℂ}
    (hx0 : x ∈ S) (hx1 : x ≠ pivots S P θ₀ n) (hx2 : x ≠ pivots S P θ₀ (n + 1)) :
    side (dirseq S P θ₀ (n + 1)) (pivots S P θ₀ n) x ≠ 0 := by
  intro hz
  rw [side_eq_zero_iff_modPi hx1] at hz
  have hc := dirseq_coherence S P θ₀ hS2 hP n
  have hm : ModPi (x - pivots S P θ₀ n).arg
      ((pivots S P θ₀ (n + 1) - pivots S P θ₀ n).arg) :=
    modPi_trans hz hc
  obtain ⟨t, ht⟩ := smul_of_modPi_arg_sub
    (sub_ne_zero.mpr (p_ne_succ S P θ₀ hS2 hP n).symm) hm
  have hcross : cross (x - pivots S P θ₀ n)
      (pivots S P θ₀ (n + 1) - pivots S P θ₀ n) = 0 := by
    rw [ht, cross_smul_left, cross_self, mul_zero]
  exact hS3 _ (p_mem S P θ₀ hS2 hP n) _ hx0 _ (p_mem S P θ₀ hS2 hP (n + 1))
    hx1.symm (p_ne_succ S P θ₀ hS2 hP n) hx2 (collinear_of_cross_eq_zero hcross)

theorem p_succ_mem_sdiff (hS2 : 2 ≤ S.card) (hP : P ∈ S) (n : ℕ) :
    pivots S P θ₀ (n + 1) ∈ S \ {pivots S P θ₀ n} :=
  Finset.mem_sdiff.mpr ⟨p_mem S P θ₀ hS2 hP (n + 1),
    fun h ↦ (p_ne_succ S P θ₀ hS2 hP n) (Finset.mem_singleton.mp h).symm⟩

theorem eq_p_succ_of_cw_eq (hS2 : 2 ≤ S.card)
    (hS3 : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → a ≠ c → b ≠ c →
      ¬ Collinear ℝ {a, b, c})
    (hP : P ∈ S) (n : ℕ) {y : ℂ}
    (hy : y ∈ S \ {pivots S P θ₀ n})
    (h : cw (dirseq S P θ₀ n) (pivots S P θ₀ n) y = rot S P θ₀ n) :
    y = pivots S P θ₀ (n + 1) := by
  rw [rot_eq_cw_dirseq S P θ₀ hS2 hP n] at h
  exact cw_inj hS3 (p_mem S P θ₀ hS2 hP n) hy (p_succ_mem_sdiff S P θ₀ hS2 hP n) h

theorem side_pos_chain (hS2 : 2 ≤ S.card)
    (hS3 : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → a ≠ c → b ≠ c →
      ¬ Collinear ℝ {a, b, c})
    (hP : P ∈ S) (n : ℕ) {x : ℂ}
    (hx0 : x ∈ S) (hx1 : x ≠ pivots S P θ₀ n) (hx2 : x ≠ pivots S P θ₀ (n + 1))
    {θ θ' : ℝ} (hθ : θ ∈ Set.Ioo (dirseq S P θ₀ (n + 1)) (dirseq S P θ₀ n))
    (hθ' : θ' ∈ Set.Ioo (dirseq S P θ₀ (n + 2)) (dirseq S P θ₀ (n + 1))) :
    (0 < side θ (pivots S P θ₀ n) x) ↔
      (0 < side θ' (pivots S P θ₀ (n + 1)) x) := by
  have hxn : x ∈ S \ {pivots S P θ₀ n} :=
    Finset.mem_sdiff.mpr ⟨hx0, fun h ↦ hx1 (Finset.mem_singleton.mp h)⟩
  have hxn1 : x ∈ S \ {pivots S P θ₀ (n + 1)} :=
    Finset.mem_sdiff.mpr ⟨hx0, fun h ↦ hx2 (Finset.mem_singleton.mp h)⟩
  have hne1 : side (dirseq S P θ₀ (n + 1)) (pivots S P θ₀ n) x ≠ 0 :=
    side_dirseq_succ_ne_zero S P θ₀ hS2 hS3 hP n hx0 hx1 hx2
  have step1 : (0 < side θ (pivots S P θ₀ n) x) ↔
      (0 < side (dirseq S P θ₀ (n + 1)) (pivots S P θ₀ n) x) :=
    (side_pos_iff_of_no_zero hx1 (le_of_lt hθ.1) hne1
      (side_ne_zero_of_mem_Ioo S P θ₀ hS2 hP n hxn hθ)
      (fun θ'' hθ'' ↦ side_ne_zero_of_mem_Ioo S P θ₀ hS2 hP n hxn
        ⟨hθ''.1, lt_trans hθ''.2 hθ.2⟩)).symm
  have step2 : side (dirseq S P θ₀ (n + 1)) (pivots S P θ₀ n) x =
      side (dirseq S P θ₀ (n + 1)) (pivots S P θ₀ (n + 1)) x := by
    obtain ⟨t, ht⟩ := smul_of_modPi_arg
      (x := pivots S P θ₀ (n + 1) - pivots S P θ₀ n) (θ := dirseq S P θ₀ (n + 1))
      (modPi_symm (dirseq_coherence S P θ₀ hS2 hP n))
    exact side_center_indep ht
  rw [step2] at step1 hne1
  have step3 : (0 < side θ' (pivots S P θ₀ (n + 1)) x) ↔
      (0 < side (dirseq S P θ₀ (n + 1)) (pivots S P θ₀ (n + 1)) x) :=
    side_pos_iff_of_no_zero hx2 (le_of_lt hθ'.2)
      (side_ne_zero_of_mem_Ioo S P θ₀ hS2 hP (n + 1) hxn1 hθ') hne1
      (fun θ'' hθ'' ↦ side_ne_zero_of_mem_Ioo S P θ₀ hS2 hP (n + 1) hxn1
        ⟨lt_trans hθ'.1 hθ''.1, hθ''.2⟩)
  exact step1.trans step3.symm

theorem rot_lt_pi (hS2 : 2 ≤ S.card)
    (hS3 : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → a ≠ c → b ≠ c →
      ¬ Collinear ℝ {a, b, c})
    (hP : P ∈ S) (h3 : 3 ≤ S.card) (n : ℕ) :
    rot S P θ₀ n < π := by
  obtain ⟨y, hy, hyne⟩ : ∃ y ∈ S \ {pivots S P θ₀ n}, y ≠ pivots S P θ₀ (n + 1) := by
    have hcard : 1 < (S \ {pivots S P θ₀ n}).card := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr
        (Finset.singleton_subset_iff.mpr (p_mem S P θ₀ hS2 hP n)), Finset.card_singleton]
      omega
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hcard
    by_cases hae : a = pivots S P θ₀ (n + 1)
    · exact ⟨b, hb, fun h ↦ hab (hae.trans h.symm)⟩
    · exact ⟨a, ha, hae⟩
  have hmin := cw_min S P θ₀ hS2 hP n hy
  rw [← rot_eq_cw_dirseq S P θ₀ hS2 hP n] at hmin
  rcases eq_or_lt_of_le hmin with heq | hlt
  · exfalso
    exact hyne (eq_p_succ_of_cw_eq S P θ₀ hS2 hS3 hP n hy heq.symm)
  · exact lt_of_lt_of_le hlt (cw_le_pi _ _ _)

theorem arg_neg_modPi_odd {z : ℂ} (hz : z ≠ 0) :
    ∃ k : ℤ, (-z).arg = z.arg + (2 * k + 1) * π := by
  have hz2 : -z ≠ 0 := neg_ne_zero.mpr hz
  rcases lt_trichotomy z.im 0 with h | h | h
  · rw [Complex.arg_neg_eq_arg_add_pi_of_im_neg h]
    exact ⟨0, by ring⟩
  · have harg : ∀ w : ℂ, w ≠ 0 → w.im = 0 → w.arg = 0 ∨ w.arg = π := by
      intro w hw him
      by_cases h0 : w.arg = 0
      · exact Or.inl h0
      · right
        rcases eq_or_lt_of_le (Complex.arg_le_pi w) with h3 | h3
        · exact h3
        · exfalso
          rcases Complex.arg_lt_pi_iff.mp h3 with h4 | h4
          · exact h0 (Complex.arg_eq_zero_iff.mpr ⟨h4, him⟩)
          · exact h4 him
    have him2 : (-z).im = 0 := by rw [Complex.neg_im, h, neg_zero]
    rcases harg z hz h with h1 | h1 <;> rcases harg (-z) hz2 him2 with h2 | h2
    · exfalso
      have hr1 : 0 ≤ z.re := (Complex.arg_eq_zero_iff.mp h1).1
      have hr2 : 0 ≤ (-z).re := (Complex.arg_eq_zero_iff.mp h2).1
      rw [Complex.neg_re] at hr2
      have hre : z.re = 0 := by linarith
      exact hz (Complex.ext (by simp [hre]) (by simp [h]))
    · rw [h1, h2]; exact ⟨0, by ring⟩
    · rw [h1, h2]; exact ⟨-1, by ring⟩
    · exfalso
      have hr1 : z.re < 0 := (Complex.arg_eq_pi_iff.mp h1).1
      have hr2 : (-z).re < 0 := (Complex.arg_eq_pi_iff.mp h2).1
      rw [Complex.neg_re] at hr2
      linarith
  · rw [Complex.arg_neg_eq_arg_sub_pi_of_im_pos h]
    exact ⟨-1, by ring⟩

theorem modPi_arg_neg' {z : ℂ} (hz : z ≠ 0) : ModPi (-z).arg z.arg := by
  obtain ⟨k, hk⟩ := arg_neg_modPi_odd hz
  refine ⟨2 * k + 1, ?_⟩
  push_cast
  exact hk

theorem side_mid_pivot_sign (hS2 : 2 ≤ S.card)
    (hS3 : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → a ≠ c → b ≠ c →
      ¬ Collinear ℝ {a, b, c})
    (hP : P ∈ S) (h3 : 3 ≤ S.card) (n : ℕ) :
    (0 < side (mid S P θ₀ (n + 1)) (pivots S P θ₀ (n + 1)) (pivots S P θ₀ n)) ↔
      (0 < side (mid S P θ₀ n) (pivots S P θ₀ n) (pivots S P θ₀ (n + 1))) := by
  obtain ⟨k, hk⟩ := modPi_symm (dirseq_coherence S P θ₀ hS2 hP n)
  obtain ⟨m, hm⟩ := arg_neg_modPi_odd
    (sub_ne_zero.mpr (p_ne_succ S P θ₀ hS2 hP n).symm)
  rw [neg_sub] at hm
  have hne : pivots S P θ₀ (n + 1) ≠ pivots S P θ₀ n := (p_ne_succ S P θ₀ hS2 hP n).symm
  have hmid1 : mid S P θ₀ n = dirseq S P θ₀ (n + 1) + rot S P θ₀ n / 2 := by
    rw [mid, dirseq_succ S P θ₀ n]; ring
  have hmid2 : mid S P θ₀ (n + 1) = dirseq S P θ₀ (n + 1) - rot S P θ₀ (n + 1) / 2 := by
    rw [mid, dirseq_succ S P θ₀ (n + 1)]; ring
  have hsin1 : Real.sin (dirseq S P θ₀ (n + 1) + ↑k * π -
      (dirseq S P θ₀ (n + 1) + rot S P θ₀ n / 2)) =
      (-1 : ℝ) ^ k * Real.sin (-(rot S P θ₀ n / 2)) := by
    have e : dirseq S P θ₀ (n + 1) + ↑k * π -
        (dirseq S P θ₀ (n + 1) + rot S P θ₀ n / 2) =
        (-(rot S P θ₀ n / 2)) + ↑k * π := by ring
    rw [e, sin_add_int_mul_pi]
  have hsin2 : Real.sin (dirseq S P θ₀ (n + 1) + (↑k + (2 * ↑m + 1)) * π -
      (dirseq S P θ₀ (n + 1) - rot S P θ₀ (n + 1) / 2)) =
      (-1 : ℝ) ^ (k + (2 * m + 1)) * Real.sin (rot S P θ₀ (n + 1) / 2) := by
    have e : dirseq S P θ₀ (n + 1) + (↑k + (2 * ↑m + 1)) * π -
        (dirseq S P θ₀ (n + 1) - rot S P θ₀ (n + 1) / 2) =
        (rot S P θ₀ (n + 1) / 2) + ↑(k + (2 * m + 1)) * π := by push_cast; ring
    rw [e, sin_add_int_mul_pi]
  have hpow : (-1 : ℝ) ^ (k + (2 * m + 1)) = -(-1 : ℝ) ^ k := by
    rw [zpow_add₀ (show (-1 : ℝ) ≠ 0 by norm_num),
      Odd.neg_one_zpow ⟨m, rfl⟩, mul_neg, mul_one]
  have hside1 : side (mid S P θ₀ n) (pivots S P θ₀ n) (pivots S P θ₀ (n + 1)) =
      -(-1 : ℝ) ^ k * (‖pivots S P θ₀ (n + 1) - pivots S P θ₀ n‖ *
        Real.sin (rot S P θ₀ n / 2)) := by
    rw [side_eq_norm_sin hne, hk, hmid1, hsin1, Real.sin_neg]
    ring
  have hside2 : side (mid S P θ₀ (n + 1)) (pivots S P θ₀ (n + 1)) (pivots S P θ₀ n) =
      -(-1 : ℝ) ^ k * (‖pivots S P θ₀ n - pivots S P θ₀ (n + 1)‖ *
        Real.sin (rot S P θ₀ (n + 1) / 2)) := by
    have hk2 : (pivots S P θ₀ n - pivots S P θ₀ (n + 1)).arg =
        dirseq S P θ₀ (n + 1) + (↑k + (2 * ↑m + 1)) * π := by
      rw [hm, hk]; ring
    rw [side_eq_norm_sin (p_ne_succ S P θ₀ hS2 hP n), hk2, hmid2, hsin2, hpow]
    ring
  have hA : (0 : ℝ) < ‖pivots S P θ₀ (n + 1) - pivots S P θ₀ n‖ *
      Real.sin (rot S P θ₀ n / 2) := by
    apply mul_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne))
    apply Real.sin_pos_of_pos_of_lt_pi
    · linarith [rot_pos S P θ₀ n]
    · have hrl := rot_lt_pi S P θ₀ hS2 hS3 hP h3 n; linarith [Real.pi_pos]
  have hB : (0 : ℝ) < ‖pivots S P θ₀ n - pivots S P θ₀ (n + 1)‖ *
      Real.sin (rot S P θ₀ (n + 1) / 2) := by
    apply mul_pos (norm_pos_iff.mpr (sub_ne_zero.mpr (p_ne_succ S P θ₀ hS2 hP n)))
    apply Real.sin_pos_of_pos_of_lt_pi
    · linarith [rot_pos S P θ₀ (n + 1)]
    · have hrl := rot_lt_pi S P θ₀ hS2 hS3 hP h3 (n + 1); linarith [Real.pi_pos]
  rw [hside1, hside2]
  constructor
  · intro h
    rcases mul_pos_iff.mp h with ⟨h1, -⟩ | ⟨h1, h2⟩
    · exact mul_pos h1 hA
    · linarith [hB]
  · intro h
    rcases mul_pos_iff.mp h with ⟨h1, -⟩ | ⟨h1, h2⟩
    · exact mul_pos h1 hB
    · linarith [hA]

theorem leftCount_succ (hS2 : 2 ≤ S.card)
    (hS3 : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → a ≠ c → b ≠ c →
      ¬ Collinear ℝ {a, b, c})
    (hP : P ∈ S) (h3 : 3 ≤ S.card) (n : ℕ) :
    leftCount S P θ₀ (n + 1) = leftCount S P θ₀ n := by
  set F0 := S.filter fun x ↦ 0 < side (mid S P θ₀ n) (pivots S P θ₀ n) x with hF0
  set F1 := S.filter
    fun x ↦ 0 < side (mid S P θ₀ (n + 1)) (pivots S P θ₀ (n + 1)) x with hF1
  have hswap : (0 < side (mid S P θ₀ (n + 1)) (pivots S P θ₀ (n + 1))
      (pivots S P θ₀ n)) ↔
      (0 < side (mid S P θ₀ n) (pivots S P θ₀ n) (pivots S P θ₀ (n + 1))) :=
    side_mid_pivot_sign S P θ₀ hS2 hS3 hP h3 n
  have hself1 : ¬ (0 < side (mid S P θ₀ n) (pivots S P θ₀ n) (pivots S P θ₀ n)) := by
    rw [side_self]; exact lt_irrefl 0
  have hself2 : ¬ (0 < side (mid S P θ₀ (n + 1)) (pivots S P θ₀ (n + 1))
      (pivots S P θ₀ (n + 1))) := by
    rw [side_self]; exact lt_irrefl 0
  have hchain : ∀ x ∈ S, x ≠ pivots S P θ₀ n → x ≠ pivots S P θ₀ (n + 1) →
      ((0 < side (mid S P θ₀ (n + 1)) (pivots S P θ₀ (n + 1)) x) ↔
       (0 < side (mid S P θ₀ n) (pivots S P θ₀ n) x)) := by
    intro x hx hx1 hx2
    exact (side_pos_chain S P θ₀ hS2 hS3 hP n hx hx1 hx2
      (mid_mem_Ioo S P θ₀ n) (mid_mem_Ioo S P θ₀ (n + 1))).symm
  have herase : F1.erase (pivots S P θ₀ n) = F0.erase (pivots S P θ₀ (n + 1)) := by
    ext x
    rw [Finset.mem_erase, Finset.mem_erase]
    constructor
    · rintro ⟨hxne, hxF⟩
      have hxS := (Finset.mem_filter.mp hxF).1
      have hxside := (Finset.mem_filter.mp hxF).2
      by_cases hx2 : x = pivots S P θ₀ (n + 1)
      · subst hx2
        exact absurd hxside hself2
      · exact ⟨hx2, Finset.mem_filter.mpr ⟨hxS, (hchain x hxS hxne hx2).mp hxside⟩⟩
    · rintro ⟨hxne, hxF⟩
      have hxS := (Finset.mem_filter.mp hxF).1
      have hxside := (Finset.mem_filter.mp hxF).2
      by_cases hx1 : x = pivots S P θ₀ n
      · subst hx1
        exact absurd hxside hself1
      · exact ⟨hx1, Finset.mem_filter.mpr ⟨hxS, (hchain x hxS hx1 hxne).mpr hxside⟩⟩
  have hcard1 : F1.card = (F1.erase (pivots S P θ₀ n)).card +
      (if pivots S P θ₀ n ∈ F1 then 1 else 0) := by
    by_cases hmem : pivots S P θ₀ n ∈ F1
    · rw [if_pos hmem, Finset.card_erase_add_one hmem]
    · rw [if_neg hmem, Finset.erase_eq_of_notMem hmem, add_zero]
  have hcard0 : F0.card = (F0.erase (pivots S P θ₀ (n + 1))).card +
      (if pivots S P θ₀ (n + 1) ∈ F0 then 1 else 0) := by
    by_cases hmem : pivots S P θ₀ (n + 1) ∈ F0
    · rw [if_pos hmem, Finset.card_erase_add_one hmem]
    · rw [if_neg hmem, Finset.erase_eq_of_notMem hmem, add_zero]
  have hif : (pivots S P θ₀ n ∈ F1) ↔ (pivots S P θ₀ (n + 1) ∈ F0) := by
    rw [Finset.mem_filter, Finset.mem_filter]
    exact ⟨fun h ↦ ⟨p_mem S P θ₀ hS2 hP _, hswap.mp h.2⟩,
      fun h ↦ ⟨p_mem S P θ₀ hS2 hP _, hswap.mpr h.2⟩⟩
  rw [leftCount, leftCount, ← hF0, ← hF1, hcard1, hcard0, herase]
  by_cases hmem : pivots S P θ₀ (n + 1) ∈ F0
  · rw [if_pos hmem, if_pos (hif.mpr hmem)]
  · rw [if_neg hmem, if_neg (fun h ↦ hmem (hif.mp h))]

end Signs

section Periodic

variable (S : Finset ℂ) (P : ℂ) (θ₀ : ℝ)

/-- The state of the windmill as an ordered pair of consecutive pivots. -/
noncomputable def state (n : ℕ) : ℂ × ℂ := (pivots S P θ₀ n, pivots S P θ₀ (n + 1))

/-- The deterministic transition on states. -/
noncomputable def step (q : ℂ × ℂ) : ℂ × ℂ :=
  (q.2, firstHit S q.2 ((q.1 - q.2).arg))

/-- The rotation between hits, as a function of the state. -/
noncomputable def stRot (q : ℂ × ℂ) : ℝ :=
  cw (q.1 - q.2).arg q.2 (firstHit S q.2 ((q.1 - q.2).arg))

theorem state_succ (n : ℕ) : state S P θ₀ (n + 1) = step S (state S P θ₀ n) := by
  simp only [state, step, pivots_succ_succ]

theorem rot_eq_stRot (n : ℕ) : rot S P θ₀ (n + 1) = stRot S (state S P θ₀ n) := by
  have e : linedir S P θ₀ (n + 1) =
      (pivots S P θ₀ n - pivots S P θ₀ (n + 1)).arg := rfl
  rw [rot, e, stRot, state, pivots_succ_succ]

theorem exists_state_repeat (hS2 : 2 ≤ S.card) (hP : P ∈ S) :
    ∃ i j : ℕ, i < j ∧ state S P θ₀ i = state S P θ₀ j := by
  have hmaps : ∀ n ∈ Finset.range ((S ×ˢ S).card + 1), state S P θ₀ n ∈ S ×ˢ S := by
    intro n _
    rw [state, Finset.mem_product]
    exact ⟨p_mem S P θ₀ hS2 hP n, p_mem S P θ₀ hS2 hP (n + 1)⟩
  have hcard : (S ×ˢ S).card < (Finset.range ((S ×ˢ S).card + 1)).card := by
    rw [Finset.card_range]; omega
  obtain ⟨i, hi, j, hj, hij, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
  rcases lt_trichotomy i j with h | h | h
  · exact ⟨i, j, h, heq⟩
  · subst h; exact absurd rfl hij
  · exact ⟨j, i, h, heq.symm⟩

theorem state_periodic (_hS2 : 2 ≤ S.card) (_hP : P ∈ S) {i j : ℕ} (_hij : i < j)
    (heq : state S P θ₀ i = state S P θ₀ j) (k : ℕ) :
    state S P θ₀ (i + k) = state S P θ₀ (j + k) := by
  induction k with
  | zero => exact heq
  | succ k ih =>
    have e1 : i + (k + 1) = (i + k) + 1 := by ring
    have e2 : j + (k + 1) = (j + k) + 1 := by ring
    rw [e1, e2, state_succ, state_succ, ih]

theorem state_periodic' (hS2 : 2 ≤ S.card) (hP : P ∈ S) {i j : ℕ} (hij : i < j)
    (heq : state S P θ₀ i = state S P θ₀ j) {T : ℕ} (hT : T = j - i) {n : ℕ}
    (hn : i ≤ n) : state S P θ₀ (n + T) = state S P θ₀ n := by
  have h1 : n + T = (n - i) + j := by omega
  rw [h1]
  have h2 := state_periodic S P θ₀ hS2 hP hij heq (n - i)
  rw [show i + (n - i) = n by omega, show j + (n - i) = (n - i) + j by ring] at h2
  exact h2.symm

theorem rot_periodic (hS2 : 2 ≤ S.card) (hP : P ∈ S) {i j : ℕ} (hij : i < j)
    (heq : state S P θ₀ i = state S P θ₀ j) {T : ℕ} (hT : T = j - i) {n : ℕ}
    (hn : i + 1 ≤ n) : rot S P θ₀ (n + T) = rot S P θ₀ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm : i ≤ m := by omega
  rw [show m + 1 + T = (m + T) + 1 by ring, rot_eq_stRot, rot_eq_stRot,
    state_periodic' S P θ₀ hS2 hP hij heq hT hm]

theorem rot_periodic_mul (hS2 : 2 ≤ S.card) (hP : P ∈ S) {i j : ℕ} (hij : i < j)
    (heq : state S P θ₀ i = state S P θ₀ j) {T : ℕ} (hT : T = j - i) {n : ℕ}
    (hn : i + 1 ≤ n) (k : ℕ) : rot S P θ₀ (n + k * T) = rot S P θ₀ n := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : n + (k + 1) * T = (n + k * T) + T := by ring
    rw [e, rot_periodic S P θ₀ hS2 hP hij heq hT (by omega : i + 1 ≤ n + k * T), ih]

theorem dirseq_add (m k : ℕ) :
    dirseq S P θ₀ (m + k) =
      dirseq S P θ₀ m - ∑ r ∈ Finset.range k, rot S P θ₀ (m + r) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : m + (k + 1) = (m + k) + 1 := by ring
    rw [e, dirseq_succ S P θ₀ _, ih, Finset.sum_range_succ]
    ring

theorem dirseq_periodic_sub (hS2 : 2 ≤ S.card) (hP : P ∈ S) {i j : ℕ} (hij : i < j)
    (heq : state S P θ₀ i = state S P θ₀ j) {T : ℕ} (hT : T = j - i) (k : ℕ) :
    dirseq S P θ₀ (i + 1 + k * T) =
      dirseq S P θ₀ (i + 1) - k * ∑ r ∈ Finset.range T, rot S P θ₀ (i + 1 + r) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : i + 1 + (k + 1) * T = (i + 1 + k * T) + T := by ring
    have hsum : ∑ r ∈ Finset.range T, rot S P θ₀ (i + 1 + k * T + r) =
        ∑ r ∈ Finset.range T, rot S P θ₀ (i + 1 + r) := by
      apply Finset.sum_congr rfl
      intro r _
      have e2 : i + 1 + k * T + r = (i + 1 + r) + k * T := by ring
      rw [e2, rot_periodic_mul S P θ₀ hS2 hP hij heq hT (by omega : i + 1 ≤ i + 1 + r) k]
    rw [e, dirseq_add, ih, hsum]
    push_cast
    ring

theorem dirseq_unbounded (hS2 : 2 ≤ S.card) (hP : P ∈ S) (B : ℝ) :
    ∃ n : ℕ, dirseq S P θ₀ n ≤ B := by
  obtain ⟨i, j, hij, heq⟩ := exists_state_repeat S P θ₀ hS2 hP
  have hT : j - i = j - i := rfl
  set Sper := ∑ r ∈ Finset.range (j - i), rot S P θ₀ (i + 1 + r) with hSper
  have hSperpos : 0 < Sper := by
    apply Finset.sum_pos (fun r _ ↦ rot_pos S P θ₀ _)
    rw [Finset.nonempty_range_iff]
    omega
  obtain ⟨k, hk⟩ := exists_nat_gt ((dirseq S P θ₀ (i + 1) - B) / Sper)
  have hk2 : dirseq S P θ₀ (i + 1) - B < k * Sper := by
    rw [div_lt_iff₀ hSperpos] at hk
    exact hk
  exact ⟨i + 1 + k * (j - i), by
    rw [dirseq_periodic_sub S P θ₀ hS2 hP hij heq hT k]
    linarith⟩

end Periodic

section Sweep

variable (S : Finset ℂ) (P : ℂ) (θ₀ : ℝ)

theorem dirseq_unbounded' (hS2 : 2 ≤ S.card) (hP : P ∈ S) (B : ℝ) :
    ∃ n : ℕ, dirseq S P θ₀ (n + 1) ≤ B := by
  obtain ⟨n, hn⟩ := dirseq_unbounded S P θ₀ hS2 hP B
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · rw [h0] at hn
    refine ⟨0, le_trans ?_ hn⟩
    rw [dirseq_succ S P θ₀ 0, dirseq_zero]
    exact sub_le_self _ (rot_pos S P θ₀ 0).le
  · exact ⟨n - 1, by rwa [show n - 1 + 1 = n from by omega]⟩

/-- The least hit index whose line direction has rotated (weakly) past
`θ₀ - M * π`. -/
noncomputable def crossIdx (hS2 : 2 ≤ S.card) (hP : P ∈ S) (M : ℕ) : ℕ :=
  Nat.find (dirseq_unbounded' S P θ₀ hS2 hP (θ₀ - M * π))

theorem crossIdx_spec (hS2 : 2 ≤ S.card) (hP : P ∈ S) (M : ℕ) :
    dirseq S P θ₀ (crossIdx S P θ₀ hS2 hP M + 1) ≤ θ₀ - M * π :=
  Nat.find_spec (dirseq_unbounded' S P θ₀ hS2 hP (θ₀ - M * π))

theorem crossIdx_spec_lt (hS2 : 2 ≤ S.card) (hP : P ∈ S)
    (hgen : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ ModPi (x - y).arg θ₀) (M : ℕ) :
    dirseq S P θ₀ (crossIdx S P θ₀ hS2 hP M + 1) < θ₀ - M * π := by
  have h1 := crossIdx_spec S P θ₀ hS2 hP M
  rcases eq_or_lt_of_le h1 with heq | hlt
  · exfalso
    have hne := dirseq_not_modPi S P θ₀ hS2 hP hgen
      (crossIdx S P θ₀ hS2 hP M) (-(M : ℤ))
    exact hne (by rw [heq]; push_cast; ring)
  · exact hlt

theorem crossIdx_le (hS2 : 2 ≤ S.card) (hP : P ∈ S) {M n : ℕ}
    (h : dirseq S P θ₀ (n + 1) ≤ θ₀ - M * π) : crossIdx S P θ₀ hS2 hP M ≤ n :=
  Nat.find_min' (dirseq_unbounded' S P θ₀ hS2 hP (θ₀ - M * π)) h

theorem dirseq_crossIdx_gt (hS2 : 2 ≤ S.card) (hP : P ∈ S) (M : ℕ) (hM : 1 ≤ M) :
    θ₀ - M * π < dirseq S P θ₀ (crossIdx S P θ₀ hS2 hP M) := by
  rcases Nat.eq_zero_or_pos (crossIdx S P θ₀ hS2 hP M) with h0 | h0
  · rw [h0, dirseq_zero]
    have hM0 : (0 : ℝ) < (M : ℝ) := by
      have : 0 < M := by omega
      exact_mod_cast this
    have h1 : (0 : ℝ) < (M : ℝ) * π := mul_pos hM0 Real.pi_pos
    linarith
  · have hmin := Nat.find_min (dirseq_unbounded' S P θ₀ hS2 hP (θ₀ - M * π))
      (m := crossIdx S P θ₀ hS2 hP M - 1) (by
        have hrfl : crossIdx S P θ₀ hS2 hP M =
            Nat.find (dirseq_unbounded' S P θ₀ hS2 hP (θ₀ - M * π)) := rfl
        omega)
    rw [show crossIdx S P θ₀ hS2 hP M - 1 + 1 = crossIdx S P θ₀ hS2 hP M from by omega]
      at hmin
    exact not_le.mp hmin

theorem crossIdx_le_crossIdx_succ (hS2 : 2 ≤ S.card) (hP : P ∈ S) (M : ℕ) :
    crossIdx S P θ₀ hS2 hP M ≤ crossIdx S P θ₀ hS2 hP (M + 1) := by
  apply crossIdx_le S P θ₀ hS2 hP
  have h1 := crossIdx_spec S P θ₀ hS2 hP (M + 1)
  have h2 : θ₀ - ((M + 1 : ℕ) : ℝ) * π ≤ θ₀ - (M : ℝ) * π := by
    have h3 : (M : ℝ) ≤ ((M + 1 : ℕ) : ℝ) := by push_cast; linarith
    nlinarith [Real.pi_pos]
  linarith

theorem side_at_mpi_ne_zero {S : Finset ℂ} {θ₀ : ℝ}
    (hgen : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ ModPi (x - y).arg θ₀)
    (M : ℕ) {c x : ℂ} (hc : c ∈ S) (hx : x ∈ S) (hxc : x ≠ c) :
    side (θ₀ - M * π) c x ≠ 0 := by
  intro hz
  rw [side_eq_zero_iff_modPi hxc] at hz
  exact hgen x hx c hc hxc (modPi_trans hz ⟨-(M : ℤ), by push_cast; ring⟩)

theorem side_swap (D : ℝ) (c x : ℂ) : side D c x = -side D x c := by
  have e : x - c = -(c - x) := by ring
  rw [side, side, e, cross, cross, mul_neg, Complex.neg_im]

theorem side_sub_add (D : ℝ) (a x z : ℂ) : side D a z = side D x z + side D a x := by
  have e : z - a = (z - x) + (x - a) := by ring
  rw [side, side, side, e, cross_add_left]

/-- The rank of a point: the number of points of `S` lying strictly to the
left of the directed line through it in direction `D`. -/
noncomputable def rankS (D : ℝ) (y : ℂ) : ℕ := (S.filter fun z ↦ 0 < side D y z).card

theorem rankS_lt_iff (D : ℝ)
    (hgenD : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ ModPi (x - y).arg D)
    {a x : ℂ} (ha : a ∈ S) (hx : x ∈ S) :
    rankS S D x < rankS S D a ↔ 0 < side D a x := by
  by_cases hxa : x = a
  · subst hxa
    constructor
    · intro h; exact absurd h (lt_irrefl _)
    · intro h; rw [side_self] at h; exact absurd h (lt_irrefl 0)
  · have hne : side D a x ≠ 0 := by
      intro hz
      rw [side_eq_zero_iff_modPi hxa] at hz
      exact hgenD x hx a ha hxa hz
    constructor
    · intro h
      by_contra hneg
      have hlt : side D a x < 0 := lt_of_le_of_ne (le_of_not_gt hneg) hne
      have hsub : S.filter (fun z ↦ 0 < side D a z) ⊂
          S.filter (fun z ↦ 0 < side D x z) := by
        rw [Finset.ssubset_iff]
        refine ⟨a, ?_, ?_⟩
        · rw [Finset.mem_filter, side_self]
          exact fun hh ↦ lt_irrefl 0 hh.2
        · rw [Finset.insert_subset_iff]
          refine ⟨?_, ?_⟩
          · rw [Finset.mem_filter]
            exact ⟨ha, by rw [side_swap]; linarith [hlt]⟩
          · intro z hz
            rw [Finset.mem_filter] at hz
            rw [Finset.mem_filter]
            have h1 : side D x z = side D a z - side D a x := by
              have h2 := side_sub_add D a x z
              linarith
            exact ⟨hz.1, by rw [h1]; linarith [hz.2, hlt]⟩
      have h2 := Finset.card_lt_card hsub
      rw [rankS, rankS] at h
      omega
    · intro hpos
      have hsub : S.filter (fun z ↦ 0 < side D x z) ⊂
          S.filter (fun z ↦ 0 < side D a z) := by
        rw [Finset.ssubset_iff]
        refine ⟨x, ?_, ?_⟩
        · rw [Finset.mem_filter, side_self]
          exact fun hh ↦ lt_irrefl 0 hh.2
        · rw [Finset.insert_subset_iff]
          refine ⟨?_, ?_⟩
          · rw [Finset.mem_filter]
            exact ⟨hx, hpos⟩
          · intro z hz
            rw [Finset.mem_filter] at hz
            rw [Finset.mem_filter]
            have h1 : side D a z = side D x z + side D a x := side_sub_add D a x z
            exact ⟨hz.1, by rw [h1]; linarith [hz.2, hpos]⟩
      exact Finset.card_lt_card hsub

theorem rankS_inj (D : ℝ)
    (hgenD : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ ModPi (x - y).arg D)
    {x y : ℂ} (hx : x ∈ S) (hy : y ∈ S)
    (h : rankS S D x = rankS S D y) : x = y := by
  by_contra hxy
  have hne : side D y x ≠ 0 := by
    intro hz
    rw [side_eq_zero_iff_modPi hxy] at hz
    exact hgenD x hx y hy hxy hz
  rcases lt_trichotomy (side D y x) 0 with hlt | heq | hgt
  · have h1 : rankS S D y < rankS S D x :=
      (rankS_lt_iff S D hgenD hx hy).mpr (by rw [side_swap]; linarith [hlt])
    omega
  · exact hne heq
  · have h1 : rankS S D x < rankS S D y := (rankS_lt_iff S D hgenD hy hx).mpr hgt
    omega

theorem leftCount_zero (hS2 : 2 ≤ S.card) (hP : P ∈ S)
    (hgen : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ ModPi (x - y).arg θ₀) :
    leftCount S P θ₀ 0 = (S.filter fun x ↦ 0 < side θ₀ P x).card := by
  rw [leftCount, pivots_zero]
  congr 1
  apply Finset.filter_congr
  intro x hx
  by_cases hxP : x = P
  · subst hxP
    rw [side_self, side_self]
  · have hne1 : side θ₀ P x ≠ 0 := by
      intro hz
      rw [side_eq_zero_iff_modPi hxP] at hz
      exact hgen x hx P hP hxP hz
    have hxsd : x ∈ S \ {P} :=
      Finset.mem_sdiff.mpr ⟨hx, fun h ↦ hxP (Finset.mem_singleton.mp h)⟩
    have hne2 : side (mid S P θ₀ 0) P x ≠ 0 :=
      side_ne_zero_of_mem_Ioo S P θ₀ hS2 hP 0 hxsd (mid_mem_Ioo S P θ₀ 0)
    have hm : mid S P θ₀ 0 ∈ Set.Ioo (dirseq S P θ₀ 1) θ₀ := by
      have h1 := mid_mem_Ioo S P θ₀ 0
      rwa [dirseq_zero] at h1
    have hd1 : dirseq S P θ₀ 1 < θ₀ := by
      rw [dirseq_succ S P θ₀ 0, dirseq_zero]
      exact sub_lt_self _ (rot_pos S P θ₀ 0)
    rcases le_total (mid S P θ₀ 0) θ₀ with hle | hle
    · exact side_pos_iff_of_no_zero hxP hle hne2 hne1
        (fun θ'' hθ'' ↦ side_ne_zero_of_mem_Ioo S P θ₀ hS2 hP 0 hxsd
          ⟨lt_trans hm.1 hθ''.1, by rw [dirseq_zero]; exact hθ''.2⟩)
    · exact (side_pos_iff_of_no_zero hxP hle hne1 hne2
        (fun θ'' hθ'' ↦ side_ne_zero_of_mem_Ioo S P θ₀ hS2 hP 0 hxsd
          ⟨lt_trans hd1 hθ''.1, by rw [dirseq_zero]; exact lt_trans hθ''.2 hm.2⟩)).symm

theorem leftCount_const (hS2 : 2 ≤ S.card)
    (hS3 : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → a ≠ c → b ≠ c →
      ¬ Collinear ℝ {a, b, c})
    (hP : P ∈ S) (h3 : 3 ≤ S.card) (n : ℕ) :
    leftCount S P θ₀ n = leftCount S P θ₀ 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [leftCount_succ S P θ₀ hS2 hS3 hP h3 n, ih]

theorem side_const_mpi_mid (hS2 : 2 ≤ S.card)
    (hP : P ∈ S)
    (hgen : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ ModPi (x - y).arg θ₀)
    (M : ℕ) (hM : 1 ≤ M) {x : ℂ} (hx : x ∈ S) :
    (0 < side (θ₀ - M * π) (pivots S P θ₀ (crossIdx S P θ₀ hS2 hP M)) x) ↔
      (0 < side (mid S P θ₀ (crossIdx S P θ₀ hS2 hP M))
        (pivots S P θ₀ (crossIdx S P θ₀ hS2 hP M)) x) := by
  have hspec : dirseq S P θ₀ (crossIdx S P θ₀ hS2 hP M + 1) < θ₀ - M * π :=
    crossIdx_spec_lt S P θ₀ hS2 hP hgen M
  have hgt : θ₀ - M * π < dirseq S P θ₀ (crossIdx S P θ₀ hS2 hP M) :=
    dirseq_crossIdx_gt S P θ₀ hS2 hP M hM
  have hmid : mid S P θ₀ (crossIdx S P θ₀ hS2 hP M) ∈
      Set.Ioo (dirseq S P θ₀ (crossIdx S P θ₀ hS2 hP M + 1))
        (dirseq S P θ₀ (crossIdx S P θ₀ hS2 hP M)) :=
    mid_mem_Ioo S P θ₀ (crossIdx S P θ₀ hS2 hP M)
  by_cases hxc : x = pivots S P θ₀ (crossIdx S P θ₀ hS2 hP M)
  · rw [hxc, side_self, side_self]
  · have hne1 : side (θ₀ - M * π) (pivots S P θ₀ (crossIdx S P θ₀ hS2 hP M)) x ≠ 0 :=
      side_at_mpi_ne_zero hgen M (p_mem S P θ₀ hS2 hP _) hx hxc
    have hxsd : x ∈ S \ {pivots S P θ₀ (crossIdx S P θ₀ hS2 hP M)} :=
      Finset.mem_sdiff.mpr ⟨hx, fun h ↦ hxc (Finset.mem_singleton.mp h)⟩
    have hne2 : side (mid S P θ₀ (crossIdx S P θ₀ hS2 hP M))
        (pivots S P θ₀ (crossIdx S P θ₀ hS2 hP M)) x ≠ 0 :=
      side_ne_zero_of_mem_Ioo S P θ₀ hS2 hP _ hxsd hmid
    rcases le_total (θ₀ - M * π) (mid S P θ₀ (crossIdx S P θ₀ hS2 hP M)) with hle | hle
    · exact side_pos_iff_of_no_zero hxc hle hne1 hne2
        (fun θ'' hθ'' ↦ side_ne_zero_of_mem_Ioo S P θ₀ hS2 hP _ hxsd
          ⟨lt_trans hspec hθ''.1, lt_trans hθ''.2 hmid.2⟩)
    · exact (side_pos_iff_of_no_zero hxc hle hne2 hne1
        (fun θ'' hθ'' ↦ side_ne_zero_of_mem_Ioo S P θ₀ hS2 hP _ hxsd
          ⟨lt_trans hmid.1 hθ''.1, lt_trans hθ''.2 hgt⟩)).symm

theorem count_at_mpi (hS2 : 2 ≤ S.card)
    (hP : P ∈ S)
    (hgen : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ ModPi (x - y).arg θ₀)
    (M : ℕ) (hM : 1 ≤ M) :
    (S.filter fun x ↦ 0 < side (θ₀ - M * π)
        (pivots S P θ₀ (crossIdx S P θ₀ hS2 hP M)) x).card =
      leftCount S P θ₀ (crossIdx S P θ₀ hS2 hP M) := by
  rw [leftCount]
  congr 1
  apply Finset.filter_congr
  intro x hx
  exact side_const_mpi_mid S P θ₀ hS2 hP hgen M hM hx

theorem count_left_add_right (hgen : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ ModPi (x - y).arg θ₀)
    (M : ℕ) {c : ℂ} (hc : c ∈ S) :
    (S.filter fun x ↦ 0 < side (θ₀ - M * π) c x).card +
      (S.filter fun x ↦ side (θ₀ - M * π) c x < 0).card = S.card - 1 := by
  have hdisj : Disjoint (S.filter fun x ↦ 0 < side (θ₀ - M * π) c x)
      (S.filter fun x ↦ side (θ₀ - M * π) c x < 0) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    rw [Finset.mem_filter] at hx1 hx2
    linarith [hx1.2, hx2.2]
  have hunion : (S.filter fun x ↦ 0 < side (θ₀ - M * π) c x) ∪
      (S.filter fun x ↦ side (θ₀ - M * π) c x < 0) = S.erase c := by
    ext x
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro (⟨hx, hside⟩ | ⟨hx, hside⟩)
      · exact ⟨fun he ↦ by rw [he, side_self] at hside; exact lt_irrefl 0 hside, hx⟩
      · exact ⟨fun he ↦ by rw [he, side_self] at hside; exact lt_irrefl 0 hside, hx⟩
    · rintro ⟨hxne, hx⟩
      have hne : side (θ₀ - M * π) c x ≠ 0 := side_at_mpi_ne_zero hgen M hc hx hxne
      rcases lt_trichotomy 0 (side (θ₀ - M * π) c x) with h | h | h
      · exact Or.inl ⟨hx, h⟩
      · exact absurd h.symm hne
      · exact Or.inr ⟨hx, h⟩
  have h1 := Finset.card_union_of_disjoint hdisj
  rw [hunion] at h1
  rw [← h1, Finset.card_erase_of_mem hc]

theorem sweep_sign_const (hS2 : 2 ≤ S.card)
    (hS3 : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → a ≠ c → b ≠ c →
      ¬ Collinear ℝ {a, b, c})
    (hP : P ∈ S)
    (hgen : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ ModPi (x - y).arg θ₀)
    (M : ℕ) {x : ℂ} (hx0 : x ∈ S)
    (hxn : ∀ m : ℕ, crossIdx S P θ₀ hS2 hP (M + 1) ≤ m →
      m ≤ crossIdx S P θ₀ hS2 hP (M + 2) → pivots S P θ₀ m ≠ x) :
    (0 < side (θ₀ - (M + 1 : ℕ) * π) (pivots S P θ₀ (crossIdx S P θ₀ hS2 hP (M + 1)))
        x) ↔
      (0 < side (θ₀ - ((M + 2 : ℕ)) * π) (pivots S P θ₀ (crossIdx S P θ₀ hS2 hP (M + 2)))
        x) := by
  have hlink1 := side_const_mpi_mid S P θ₀ hS2 hP hgen (M + 1) (by omega) hx0
  have hlink2 := side_const_mpi_mid S P θ₀ hS2 hP hgen (M + 2) (by omega) hx0
  have hi₁₂ : crossIdx S P θ₀ hS2 hP (M + 1) ≤ crossIdx S P θ₀ hS2 hP (M + 2) :=
    crossIdx_le_crossIdx_succ S P θ₀ hS2 hP (M + 1)
  have h2 : ∀ d : ℕ, crossIdx S P θ₀ hS2 hP (M + 1) + d ≤ crossIdx S P θ₀ hS2 hP (M + 2) →
      ((0 < side (mid S P θ₀ (crossIdx S P θ₀ hS2 hP (M + 1)))
          (pivots S P θ₀ (crossIdx S P θ₀ hS2 hP (M + 1))) x) ↔
        (0 < side (mid S P θ₀ (crossIdx S P θ₀ hS2 hP (M + 1) + d))
          (pivots S P θ₀ (crossIdx S P θ₀ hS2 hP (M + 1) + d)) x)) := by
    intro d
    induction d with
    | zero => intro _; exact Iff.rfl
    | succ d ihd =>
      intro hd
      rw [show crossIdx S P θ₀ hS2 hP (M + 1) + (d + 1) =
        (crossIdx S P θ₀ hS2 hP (M + 1) + d) + 1 by ring]
      exact (ihd (by omega)).trans
        (side_pos_chain S P θ₀ hS2 hS3 hP (crossIdx S P θ₀ hS2 hP (M + 1) + d) hx0
          (hxn (crossIdx S P θ₀ hS2 hP (M + 1) + d) (by omega) (by omega)).symm
          (hxn (crossIdx S P θ₀ hS2 hP (M + 1) + d + 1) (by omega) (by omega)).symm
          (mid_mem_Ioo S P θ₀ (crossIdx S P θ₀ hS2 hP (M + 1) + d))
          (mid_mem_Ioo S P θ₀ (crossIdx S P θ₀ hS2 hP (M + 1) + d + 1)))
  have h3 := h2 (crossIdx S P θ₀ hS2 hP (M + 2) - crossIdx S P θ₀ hS2 hP (M + 1)) (by omega)
  rw [show crossIdx S P θ₀ hS2 hP (M + 1) +
    (crossIdx S P θ₀ hS2 hP (M + 2) - crossIdx S P θ₀ hS2 hP (M + 1)) =
    crossIdx S P θ₀ hS2 hP (M + 2) from by omega] at h3
  exact hlink1.trans (h3.trans hlink2.symm)

/-- The key step: after the windmill line has rotated by `π` (from `θ₀ - (M+1) * π`
to `θ₀ - (M+2) * π`), every point of `S` has been used as a pivot. -/
theorem sweep (hS2 : 2 ≤ S.card)
    (hS3 : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → a ≠ c → b ≠ c →
      ¬ Collinear ℝ {a, b, c})
    (hP : P ∈ S)
    (hgen : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ ModPi (x - y).arg θ₀)
    (h3 : 3 ≤ S.card)
    (hPbal : (S.filter fun x ↦ 0 < side θ₀ P x).card = (S.card - 1) / 2)
    (M : ℕ) {x : ℂ} (hx0 : x ∈ S)
    (hxn : ∀ m : ℕ, crossIdx S P θ₀ hS2 hP (M + 1) ≤ m →
      m ≤ crossIdx S P θ₀ hS2 hP (M + 2) → pivots S P θ₀ m ≠ x) :
    pivots S P θ₀ (crossIdx S P θ₀ hS2 hP (M + 1)) = x := by
  by_contra hxa
  set i₁ := crossIdx S P θ₀ hS2 hP (M + 1) with hi₁
  set i₂ := crossIdx S P θ₀ hS2 hP (M + 2) with hi₂
  have hgenD : ∀ x₁ ∈ S, ∀ y₁ ∈ S, x₁ ≠ y₁ →
      ¬ ModPi (x₁ - y₁).arg (θ₀ - ((M + 1 : ℕ)) * π) := by
    intro x₁ hx1 y₁ hy1 hxy hmod
    exact hgen x₁ hx1 y₁ hy1 hxy (modPi_trans hmod ⟨-(M + 1 : ℤ), by push_cast; ring⟩)
  have hD2 : θ₀ - ((M + 1 : ℕ)) * π = (θ₀ - ((M + 2 : ℕ)) * π) + π := by
    push_cast; ring
  have hi₁₂' : crossIdx S P θ₀ hS2 hP (M + 1) ≤ crossIdx S P θ₀ hS2 hP (M + 2) :=
    crossIdx_le_crossIdx_succ S P θ₀ hS2 hP (M + 1)
  have hxb : pivots S P θ₀ i₂ ≠ x := hxn i₂ (by rw [hi₂]; exact hi₁₂') (by rw [hi₂])
  have hside : side (θ₀ - ((M + 1 : ℕ)) * π) (pivots S P θ₀ i₂) x =
      - side (θ₀ - ((M + 2 : ℕ)) * π) (pivots S P θ₀ i₂) x := by
    rw [hD2, side_add_pi]
  have hne2 : side (θ₀ - ((M + 2 : ℕ)) * π) (pivots S P θ₀ i₂) x ≠ 0 :=
    side_at_mpi_ne_zero hgen (M + 2) (p_mem S P θ₀ hS2 hP i₂) hx0 hxb.symm
  have hflip : (0 < side (θ₀ - ((M + 1 : ℕ)) * π) (pivots S P θ₀ i₁) x) ↔
      ¬ (0 < side (θ₀ - ((M + 1 : ℕ)) * π) (pivots S P θ₀ i₂) x) := by
    have hconst := sweep_sign_const S P θ₀ hS2 hS3 hP hgen M hx0 hxn
    rw [hconst, hside]
    constructor
    · intro h hh
      linarith
    · intro h
      by_contra hneg
      have hle : side (θ₀ - ((M + 2 : ℕ)) * π) (pivots S P θ₀ i₂) x ≤ 0 :=
        le_of_not_gt hneg
      rcases eq_or_lt_of_le hle with heq | hlt
      · exact hne2 heq
      · exact h (by linarith)
  have hrank_a : rankS S (θ₀ - ((M + 1 : ℕ)) * π) (pivots S P θ₀ i₁) =
      (S.card - 1) / 2 := by
    have h1 : rankS S (θ₀ - ((M + 1 : ℕ)) * π) (pivots S P θ₀ i₁) =
        leftCount S P θ₀ i₁ :=
      count_at_mpi S P θ₀ hS2 hP hgen (M + 1) (by omega)
    rw [h1, leftCount_const S P θ₀ hS2 hS3 hP h3 i₁, leftCount_zero S P θ₀ hS2 hP hgen]
    exact hPbal
  have hrank_b : rankS S (θ₀ - ((M + 1 : ℕ)) * π) (pivots S P θ₀ i₂) =
      S.card - 1 - (S.card - 1) / 2 := by
    have hsum := count_left_add_right S θ₀ hgen (M + 1) (p_mem S P θ₀ hS2 hP i₂)
    have hneg : (S.filter fun z ↦ side (θ₀ - ((M + 1 : ℕ)) * π)
        (pivots S P θ₀ i₂) z < 0).card = leftCount S P θ₀ i₂ := by
      have h2 : (S.filter fun z ↦ side (θ₀ - ((M + 1 : ℕ)) * π) (pivots S P θ₀ i₂) z < 0) =
          (S.filter fun z ↦ 0 < side (θ₀ - ((M + 2 : ℕ)) * π) (pivots S P θ₀ i₂) z) := by
        apply Finset.filter_congr
        intro z hz
        rw [hD2, side_add_pi]
        constructor <;> intro h <;> linarith
      rw [h2]
      exact count_at_mpi S P θ₀ hS2 hP hgen (M + 2) (by omega)
    have hlc : leftCount S P θ₀ i₂ = (S.card - 1) / 2 := by
      rw [leftCount_const S P θ₀ hS2 hS3 hP h3 i₂, leftCount_zero S P θ₀ hS2 hP hgen]
      exact hPbal
    rw [hneg, hlc] at hsum
    rw [rankS]
    exact Nat.eq_sub_of_add_eq hsum
  rw [← rankS_lt_iff S (θ₀ - ((M + 1 : ℕ)) * π) hgenD (p_mem S P θ₀ hS2 hP i₁) hx0,
    ← rankS_lt_iff S (θ₀ - ((M + 1 : ℕ)) * π) hgenD (p_mem S P θ₀ hS2 hP i₂) hx0] at hflip
  have hxne_a : rankS S (θ₀ - ((M + 1 : ℕ)) * π) x ≠
      rankS S (θ₀ - ((M + 1 : ℕ)) * π) (pivots S P θ₀ i₁) :=
    fun h ↦ hxa (rankS_inj S (θ₀ - ((M + 1 : ℕ)) * π) hgenD hx0
      (p_mem S P θ₀ hS2 hP i₁) h).symm
  have hxne_b : rankS S (θ₀ - ((M + 1 : ℕ)) * π) x ≠
      rankS S (θ₀ - ((M + 1 : ℕ)) * π) (pivots S P θ₀ i₂) :=
    fun h ↦ hxb (rankS_inj S (θ₀ - ((M + 1 : ℕ)) * π) hgenD hx0
      (p_mem S P θ₀ hS2 hP i₂) h).symm
  by_cases hc : rankS S (θ₀ - ((M + 1 : ℕ)) * π) x <
      rankS S (θ₀ - ((M + 1 : ℕ)) * π) (pivots S P θ₀ i₂)
  · have h1 : ¬ (rankS S (θ₀ - ((M + 1 : ℕ)) * π) x <
      rankS S (θ₀ - ((M + 1 : ℕ)) * π) (pivots S P θ₀ i₁)) := fun hA ↦ (hflip.mp hA) hc
    have h2 : rankS S (θ₀ - ((M + 1 : ℕ)) * π) (pivots S P θ₀ i₁) ≤
        rankS S (θ₀ - ((M + 1 : ℕ)) * π) x := le_of_not_gt h1
    have h3 : rankS S (θ₀ - ((M + 1 : ℕ)) * π) (pivots S P θ₀ i₁) <
        rankS S (θ₀ - ((M + 1 : ℕ)) * π) x := lt_of_le_of_ne h2 hxne_a.symm
    omega
  · have h1 : rankS S (θ₀ - ((M + 1 : ℕ)) * π) x <
        rankS S (θ₀ - ((M + 1 : ℕ)) * π) (pivots S P θ₀ i₁) := hflip.mpr hc
    have h2 : rankS S (θ₀ - ((M + 1 : ℕ)) * π) (pivots S P θ₀ i₂) ≤
        rankS S (θ₀ - ((M + 1 : ℕ)) * π) x := le_of_not_gt hc
    have h3 : rankS S (θ₀ - ((M + 1 : ℕ)) * π) (pivots S P θ₀ i₂) <
        rankS S (θ₀ - ((M + 1 : ℕ)) * π) x := lt_of_le_of_ne h2 hxne_b.symm
    omega

theorem visits_infinitely (hS2 : 2 ≤ S.card)
    (hS3 : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → a ≠ c → b ≠ c →
      ¬ Collinear ℝ {a, b, c})
    (hP : P ∈ S)
    (hgen : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ ModPi (x - y).arg θ₀)
    (h3 : 3 ≤ S.card)
    (hPbal : (S.filter fun x ↦ 0 < side θ₀ P x).card = (S.card - 1) / 2)
    {x : ℂ} (hx0 : x ∈ S) (N : ℕ) :
    ∃ n ≥ N, pivots S P θ₀ n = x := by
  by_contra hcon
  push Not at hcon
  obtain ⟨M0, hM0⟩ := exists_nat_gt ((θ₀ - dirseq S P θ₀ N) / π)
  have hlt : θ₀ - ((M0 + 1 : ℕ) : ℝ) * π < dirseq S P θ₀ N := by
    have h1 : (θ₀ - dirseq S P θ₀ N) / π < (M0 : ℝ) := hM0
    rw [div_lt_iff₀ Real.pi_pos] at h1
    have h2 : ((M0 + 1 : ℕ) : ℝ) * π = (M0 : ℝ) * π + π := by push_cast; ring
    push_cast
    nlinarith [Real.pi_pos]
  have hspec := crossIdx_spec_lt S P θ₀ hS2 hP hgen (M0 + 1)
  have hNle : N ≤ crossIdx S P θ₀ hS2 hP (M0 + 1) := by
    by_contra h2
    push Not at h2
    have h3 := (dirseq_strictAnti S P θ₀).antitone
      (show crossIdx S P θ₀ hS2 hP (M0 + 1) + 1 ≤ N from by omega)
    linarith [h3, hspec, hlt]
  have hvisit := sweep S P θ₀ hS2 hS3 hP hgen h3 hPbal M0 hx0
    (fun m hm1 _hm2 ↦ hcon m (by omega))
  exact hcon _ hNle hvisit

end Sweep

section Final

variable (S : Finset ℂ) (P : ℂ) (θ₀ : ℝ)

theorem pivots_alternating (hS2 : 2 ≤ S.card) (hP : P ∈ S) {Q : ℂ} (hQS : Q ∈ S)
    (hPQ : Q ≠ P) (hS : S = {P, Q}) (n : ℕ) :
    pivots S P θ₀ (2 * n) = P ∧ pivots S P θ₀ (2 * n + 1) = Q := by
  have hSP : S \ {P} = {Q} := by
    ext x
    rw [hS]
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨h1 | h1, h2⟩
      · exact absurd h1 h2
      · exact h1
    · intro h
      subst h
      exact ⟨Or.inr rfl, hPQ⟩
  have hSQ : S \ {Q} = {P} := by
    ext x
    rw [hS]
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨h1 | h1, h2⟩
      · exact h1
      · exact absurd h1 h2
    · intro h
      subst h
      exact ⟨Or.inl rfl, fun h' ↦ hPQ h'.symm⟩
  induction n with
  | zero =>
    constructor
    · show pivots S P θ₀ 0 = P
      rw [pivots_zero]
    · show pivots S P θ₀ 1 = Q
      rw [pivots_one]
      have hm := firstHit_mem (sdiff_singleton_nonempty hP hS2) θ₀
      rw [hSP, Finset.mem_singleton] at hm
      exact hm
  | succ n ih =>
    obtain ⟨ihP, ihQ⟩ := ih
    have h2n2 : pivots S P θ₀ (2 * (n + 1)) = P := by
      have e : 2 * (n + 1) = 2 * n + 2 := by ring
      rw [e, pivots_succ_succ S P θ₀ (2 * n), ihP, ihQ]
      have hm := firstHit_mem (sdiff_singleton_nonempty hQS hS2) ((P - Q).arg)
      rw [hSQ, Finset.mem_singleton] at hm
      exact hm
    refine ⟨h2n2, ?_⟩
    have e : 2 * (n + 1) + 1 = (2 * n + 1) + 2 := by ring
    rw [e, pivots_succ_succ S P θ₀ (2 * n + 1), ihQ,
      show (2 * n + 1 + 1 : ℕ) = 2 * (n + 1) from by ring, h2n2]
    have hm := firstHit_mem (sdiff_singleton_nonempty hP hS2) ((Q - P).arg)
    rw [hSP, Finset.mem_singleton] at hm
    exact hm

theorem windmill_of_two_points (hS2 : 2 ≤ S.card) (hP : P ∈ S) {Q : ℂ} (hQS : Q ∈ S)
    (hPQ : Q ≠ P) (hS : S = {P, Q}) (x : ℂ) (hx : x ∈ S) (N : ℕ) :
    ∃ n ≥ N, pivots S P θ₀ n = x := by
  rw [hS] at hx
  rcases Finset.mem_insert.mp hx with h | hxQ
  · rw [h]
    exact ⟨2 * N, by omega, (pivots_alternating S P θ₀ hS2 hP hQS hPQ hS N).1⟩
  · rw [Finset.mem_singleton] at hxQ
    rw [hxQ]
    exact ⟨2 * N + 1, by omega, (pivots_alternating S P θ₀ hS2 hP hQS hPQ hS N).2⟩

end Final






/-- There exists a direction `θ₀` that is not parallel (mod `π`) to any of the
finitely many directions determined by pairs of distinct points of `S`. -/
theorem exists_generic_dir (S : Finset ℂ) :
    ∃ θ₀ : ℝ, ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ ModPi (x - y).arg θ₀ := by
  classical
  -- The "bad" directions, folded back into `Set.Ico 0 π`.
  set B : Finset ℝ := ((S ×ˢ S).filter fun p ↦ p.1 ≠ p.2).image
      (fun p ↦ toIcoMod Real.pi_pos 0 ((p.1 - p.2).arg)) with hB
  have hBmem : ∀ b ∈ B, 0 ≤ b ∧ b < π := by
    intro b hb
    rw [hB, Finset.mem_image] at hb
    obtain ⟨p, _, rfl⟩ := hb
    have h := toIcoMod_mem_Ico Real.pi_pos 0 ((p.1 - p.2).arg)
    rw [zero_add] at h
    exact h
  set B' := insert 0 B with hB'
  have hB'ne : B'.Nonempty := ⟨0, Finset.mem_insert_self 0 B⟩
  set m := B'.max' hB'ne
  have hmlt : m < π := by
    have h1 : ∀ b ∈ B', b < π := by
      intro b hb
      rw [hB', Finset.mem_insert] at hb
      rcases hb with rfl | hb
      · exact Real.pi_pos
      · exact (hBmem b hb).2
    have hmem : m ∈ B' := Finset.max'_mem B' hB'ne
    exact h1 m hmem
  have hmge : 0 ≤ m := by
    have h1 : (0 : ℝ) ∈ B' := by
      rw [hB']
      exact Finset.mem_insert_self 0 B
    exact Finset.le_max' B' 0 h1
  refine ⟨(m + π) / 2, ?_⟩
  have hmθ : m < (m + π) / 2 := by linarith
  have hθπ : (m + π) / 2 < π := by linarith
  have hθge : 0 ≤ (m + π) / 2 := by linarith [Real.pi_pos]
  have hθnotB : (m + π) / 2 ∉ B := by
    intro hb
    have hb' : (m + π) / 2 ∈ B' := by
      rw [hB']
      exact Finset.mem_insert_of_mem hb
    have hle : (m + π) / 2 ≤ m := Finset.le_max' B' _ hb'
    linarith
  intro x hx y hy hxy hmod
  apply hθnotB
  obtain ⟨k, hk⟩ := hmod
  have hpair : (x, y) ∈ (S ×ˢ S).filter fun p ↦ p.1 ≠ p.2 := by
    rw [Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨hx, hy⟩, hxy⟩
  have heq : toIcoMod Real.pi_pos 0 ((x - y).arg) = (m + π) / 2 := by
    rw [hk, ← zsmul_eq_mul, toIcoMod_add_zsmul Real.pi_pos,
      toIcoMod_eq_self Real.pi_pos, zero_add, Set.mem_Ico]
    exact ⟨hθge, hθπ⟩
  rw [hB, Finset.mem_image]
  exact ⟨(x, y), hpair, heq⟩

/-- If no line through two points of `S` is parallel to the direction `θ₀`,
then some point `P ∈ S` has exactly `(S.card - 1) / 2` points of `S` strictly
on its positive side (with respect to the direction `θ₀`). -/
theorem exists_balanced_point (S : Finset ℂ) (hS2 : 2 ≤ S.card) (θ₀ : ℝ)
    (hgen : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ ModPi (x - y).arg θ₀) :
    ∃ P ∈ S, (S.filter fun x ↦ 0 < side θ₀ P x).card = (S.card - 1) / 2 := by
  classical
  set u := Complex.exp (θ₀ * Complex.I)
  have hside : ∀ c x : ℂ, side θ₀ c x = cross u x - cross u c := by
    intro c x
    have h0 : side θ₀ c x = cross u (x - c) := rfl
    rw [h0, cross_sub_left]
  -- The projection `cross u ·` is injective on `S`.
  have hinj : ∀ x ∈ S, ∀ y ∈ S, cross u x = cross u y → x = y := by
    intro x hx y hy hxy
    by_contra hne
    have h0 : side θ₀ y x = 0 := by
      rw [hside, hxy, sub_self]
    have hmod : ModPi (x - y).arg θ₀ := (side_eq_zero_iff_modPi hne).mp h0
    exact hgen x hx y hy hne hmod
  -- The rank of `y` is the number of points of `S` with larger projection.
  set rank : ℂ → ℕ := fun y ↦ (S.filter fun x ↦ cross u y < cross u x).card
  have hrank_lt : ∀ y ∈ S, rank y < S.card := by
    intro y hy
    have hsub : S.filter (fun x ↦ cross u y < cross u x) ⊆ S.erase y := by
      intro x hx
      rw [Finset.mem_filter] at hx
      rw [Finset.mem_erase]
      refine ⟨fun he ↦ ?_, hx.1⟩
      subst he
      exact lt_irrefl _ hx.2
    have hcard : rank y ≤ (S.erase y).card := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem hy] at hcard
    omega
  have hrank_inj : ∀ x ∈ S, ∀ y ∈ S, rank x = rank y → x = y := by
    intro x hx y hy hxy
    by_contra hne
    have hproj_ne : cross u x ≠ cross u y := fun h ↦ hne (hinj x hx y hy h)
    rcases lt_or_gt_of_ne hproj_ne with hlt | hlt
    · have hss : S.filter (fun z ↦ cross u y < cross u z) ⊂
          S.filter (fun z ↦ cross u x < cross u z) := by
        rw [Finset.ssubset_iff_subset_ne]
        refine ⟨fun z hz ↦ ?_, ?_⟩
        · rw [Finset.mem_filter] at hz ⊢
          exact ⟨hz.1, lt_trans hlt hz.2⟩
        · intro hcon
          have hymem : y ∈ S.filter (fun z ↦ cross u x < cross u z) := by
            rw [Finset.mem_filter]
            exact ⟨hy, hlt⟩
          rw [← hcon] at hymem
          rw [Finset.mem_filter] at hymem
          exact lt_irrefl _ hymem.2
      have hlt2 : rank y < rank x := Finset.card_lt_card hss
      omega
    · have hss : S.filter (fun z ↦ cross u x < cross u z) ⊂
          S.filter (fun z ↦ cross u y < cross u z) := by
        rw [Finset.ssubset_iff_subset_ne]
        refine ⟨fun z hz ↦ ?_, ?_⟩
        · rw [Finset.mem_filter] at hz ⊢
          exact ⟨hz.1, lt_trans hlt hz.2⟩
        · intro hcon
          have hxmem : x ∈ S.filter (fun z ↦ cross u y < cross u z) := by
            rw [Finset.mem_filter]
            exact ⟨hx, hlt⟩
          rw [← hcon] at hxmem
          rw [Finset.mem_filter] at hxmem
          exact lt_irrefl _ hxmem.2
      have hlt2 : rank x < rank y := Finset.card_lt_card hss
      omega
  have hinjOn : Set.InjOn rank S := by
    intro a ha b hb hab
    exact hrank_inj a ha b hb hab
  have himage : S.image rank = Finset.range S.card := by
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      rw [Finset.mem_image] at hz
      obtain ⟨y, hy, rfl⟩ := hz
      rw [Finset.mem_range]
      exact hrank_lt y hy
    · rw [Finset.card_range, Finset.card_image_of_injOn hinjOn]
  have hltc : (S.card - 1) / 2 < S.card := by omega
  have hmem : (S.card - 1) / 2 ∈ S.image rank := by
    rw [himage, Finset.mem_range]
    exact hltc
  rw [Finset.mem_image] at hmem
  obtain ⟨P, hP, hPrank⟩ := hmem
  refine ⟨P, hP, ?_⟩
  have hfilter : S.filter (fun x ↦ 0 < side θ₀ P x) =
      S.filter (fun x ↦ cross u P < cross u x) := by
    apply Finset.filter_congr
    intro x hx
    rw [hside P x]
    exact sub_pos
  rw [hfilter]
  exact hPrank

end BasicAPI

snip end

problem imo2011_p2 (S : Finset ℂ) (hS2 : 2 ≤ S.card)
    (hS3 : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → a ≠ c → b ≠ c →
      ¬ Collinear ℝ {a, b, c}) :
    ∃ P ∈ S, ∃ θ₀ : ℝ,
      (∀ x ∈ S, x ≠ P → side θ₀ P x ≠ 0) ∧
      (∀ x ∈ S, ∀ N : ℕ, ∃ n ≥ N, pivots S P θ₀ n = x) := by
  obtain ⟨θ₀, hgen⟩ := exists_generic_dir S
  obtain ⟨P, hP, hPbal⟩ := exists_balanced_point S hS2 θ₀ hgen
  have hstart : ∀ x ∈ S, x ≠ P → side θ₀ P x ≠ 0 := by
    intro x hx hxP hz
    rw [side_eq_zero_iff_modPi hxP] at hz
    exact hgen x hx P hP hxP hz
  refine ⟨P, hP, θ₀, hstart, ?_⟩
  intro x hx N
  by_cases h3 : 3 ≤ S.card
  · exact visits_infinitely S P θ₀ hS2 hS3 hP hgen h3 hPbal hx N
  · have hcard : S.card = 2 := by omega
    obtain ⟨a, b, hab, hS⟩ := Finset.card_eq_two.mp hcard
    rw [hS] at hP
    rcases Finset.mem_insert.mp hP with rfl | hP'
    · exact windmill_of_two_points S P θ₀ hS2 (hS.symm ▸ hP)
        (hS.symm ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self b)) hab.symm hS x hx N
    · rw [Finset.mem_singleton] at hP'
      subst hP'
      exact windmill_of_two_points S P θ₀ hS2 (hS.symm ▸ hP)
        (hS.symm ▸ Finset.mem_insert_self a {P}) hab
        (hS.trans (Finset.pair_comm a P)) x hx N

end Imo2011P2
