/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw, Kimi K3
-/

module

public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Tactic.Ring
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.NumberTheory] }

/-!
# International Mathematical Olympiad 2017, Problem 6

A point (x,y) ∈ ℤ × ℤ is called primitive if gcd(x,y) = 1.
Let S be a finite set of primitive points.
Prove that there exists n > 0 and integers a₀,a₁,...,aₙ
such that

  a₀xⁿ + a₁xⁿ⁻¹y + a₂xⁿ⁻²y² + ... + aₙ₋₁xyⁿ⁻¹ + aₙyⁿ = 1

for each (x,y) ∈ S.
-/

namespace Imo2017P6

snip begin

/-- A homogeneous polynomial in two variables with integer coefficients,
represented by its degree and coefficient function. Evaluation is
`∑ i ∈ range (deg + 1), coeff i * x^i * y^(deg - i)`. -/
structure HForm where
  deg : ℕ
  coeff : ℕ → ℤ

namespace HForm

/-- Evaluation of a homogeneous form at a point. -/
def eval (f : HForm) (x y : ℤ) : ℤ :=
  ∑ i ∈ Finset.range (f.deg + 1), f.coeff i * x ^ i * y ^ (f.deg - i)

/-- The constant form. -/
def const (c : ℤ) : HForm := ⟨0, fun _ => c⟩

/-- The linear form `α * x + β * y`. -/
def linear (α β : ℤ) : HForm := ⟨1, fun i => if i = 0 then β else α⟩

/-- Coefficient function truncated above the degree. -/
def trunc (f : HForm) : ℕ → ℤ := fun i => if i ≤ f.deg then f.coeff i else 0

lemma trunc_of_le (f : HForm) {i : ℕ} (h : i ≤ f.deg) : f.trunc i = f.coeff i :=
  ite_eq_left h

lemma trunc_of_lt (f : HForm) {i : ℕ} (h : f.deg < i) : f.trunc i = 0 :=
  ite_eq_right (not_le.mpr h)

lemma eval_const (c : ℤ) (x y : ℤ) : (const c).eval x y = c := by
  simp [eval, const]

lemma eval_linear (α β : ℤ) (x y : ℤ) : (linear α β).eval x y = α * x + β * y := by
  simp [eval, linear, Finset.sum_range_succ]
  ring

lemma eval_eq_trunc (f : HForm) (x y : ℤ) :
    f.eval x y = ∑ i ∈ Finset.range (f.deg + 1), f.trunc i * x ^ i * y ^ (f.deg - i) := by
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range, Nat.lt_succ_iff] at hi
  rw [trunc_of_le f hi]

/-- The Cauchy product formula for finite sums with vanishing tails. -/
lemma cauchy_sum (m n : ℕ) (u v : ℕ → ℤ) (hu : ∀ i, m < i → u i = 0)
    (hv : ∀ j, n < j → v j = 0) :
    (∑ i ∈ Finset.range (m + 1), u i) * (∑ j ∈ Finset.range (n + 1), v j) =
    ∑ k ∈ Finset.range (m + n + 1), ∑ i ∈ Finset.range (k + 1), u i * v (k - i) := by
  have h2 : ∀ k : ℕ, ∑ i ∈ Finset.range (k + 1), u i * v (k - i) =
      ∑ p ∈ (Finset.range (m + 1) ×ˢ Finset.range (n + 1)).filter (fun p => p.1 + p.2 = k),
        u p.1 * v p.2 := by
    intro k
    rw [← Finset.Nat.sum_antidiagonal_eq_sum_range_succ (f := fun i j => u i * v j)]
    symm
    apply Finset.sum_subset
    · intro p hp
      rw [Finset.mem_filter] at hp
      exact Finset.mem_antidiagonal.mpr hp.2
    · intro p hpant hpnot
      rw [Finset.mem_antidiagonal] at hpant
      have hmem : ¬(p.1 < m + 1 ∧ p.2 < n + 1) := by
        intro hmem
        exact hpnot (Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr hmem.1, Finset.mem_range.mpr hmem.2⟩,
            hpant⟩)
      by_cases hp1 : p.1 < m + 1
      · have hp2 : ¬ p.2 < n + 1 := fun h => hmem ⟨hp1, h⟩
        rw [hv p.2 (by lia), mul_zero]
      · rw [hu p.1 (by lia), zero_mul]
  have h1 : (∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1), u i * v j) =
      ∑ k ∈ Finset.range (m + n + 1),
        ∑ p ∈ (Finset.range (m + 1) ×ˢ Finset.range (n + 1)).filter (fun p => p.1 + p.2 = k),
          u p.1 * v p.2 := by
    rw [← Finset.sum_product']
    exact (Finset.sum_fiberwise_of_maps_to
      (s := Finset.range (m + 1) ×ˢ Finset.range (n + 1))
      (t := Finset.range (m + n + 1)) (g := fun p => p.1 + p.2)
      (f := fun p => u p.1 * v p.2) (by
        intro p hp
        rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp
        rw [Finset.mem_range]
        lia)).symm
  rw [Finset.sum_mul_sum, h1]
  exact Finset.sum_congr rfl (fun k _ => (h2 k).symm)

/-- Multiplication of homogeneous forms (degrees add). -/
def mul (f g : HForm) : HForm where
  deg := f.deg + g.deg
  coeff := fun k => ∑ i ∈ Finset.range (k + 1), f.trunc i * g.trunc (k - i)

lemma eval_mul (f g : HForm) (x y : ℤ) :
    (f.mul g).eval x y = f.eval x y * g.eval x y := by
  rw [eval_eq_trunc f, eval_eq_trunc g, cauchy_sum f.deg g.deg _
    (fun j => g.trunc j * x ^ j * y ^ (g.deg - j))
    (fun i hi => by rw [trunc_of_lt f hi, zero_mul, zero_mul])
    (fun j hj => by rw [trunc_of_lt g hj, zero_mul, zero_mul])]
  show ∑ k ∈ Finset.range (f.deg + g.deg + 1),
      (∑ i ∈ Finset.range (k + 1), f.trunc i * g.trunc (k - i)) * x ^ k * y ^ (f.deg + g.deg - k)
    = _
  simp_rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range, Nat.lt_succ_iff] at hi
  by_cases hi1 : i ≤ f.deg
  · by_cases hi2 : k - i ≤ g.deg
    · have hexp : f.deg - i + (g.deg - (k - i)) = f.deg + g.deg - k := by lia
      calc f.trunc i * g.trunc (k - i) * x ^ k * y ^ (f.deg + g.deg - k)
          = f.trunc i * g.trunc (k - i) * (x ^ i * x ^ (k - i)) *
              (y ^ (f.deg - i) * y ^ (g.deg - (k - i))) := by
            rw [← pow_add, ← pow_add, Nat.add_sub_cancel' hi, hexp]
        _ = f.trunc i * x ^ i * y ^ (f.deg - i) *
              (g.trunc (k - i) * x ^ (k - i) * y ^ (g.deg - (k - i))) := by ring
    · rw [trunc_of_lt g (by lia : g.deg < k - i)]; simp
  · rw [trunc_of_lt f (by lia : f.deg < i)]; simp

/-- Powers of a homogeneous form. -/
def pow (f : HForm) : ℕ → HForm
  | 0 => const 1
  | n + 1 => mul (pow f n) f

lemma pow_deg (f : HForm) : ∀ n : ℕ, (f.pow n).deg = n * f.deg
  | 0 => (Nat.zero_mul _).symm
  | n + 1 => by
    show (mul (f.pow n) f).deg = (n + 1) * f.deg
    rw [show (mul (f.pow n) f).deg = (f.pow n).deg + f.deg from rfl, pow_deg f n]
    ring

lemma eval_pow (f : HForm) : ∀ n : ℕ, ∀ x y : ℤ, (f.pow n).eval x y = (f.eval x y) ^ n
  | 0, _, _ => by simp [pow, eval_const]
  | n + 1, x, y => by
    show (mul (f.pow n) f).eval x y = (f.eval x y) ^ (n + 1)
    rw [eval_mul, eval_pow f n, _root_.pow_succ]

/-- Addition of two forms of the same degree. -/
def add (f g : HForm) (_h : f.deg = g.deg) : HForm :=
  ⟨f.deg, fun i => f.coeff i + g.coeff i⟩

lemma eval_add (f g : HForm) (h : f.deg = g.deg) (x y : ℤ) :
    (f.add g h).eval x y = f.eval x y + g.eval x y := by
  have hg : g.eval x y =
      ∑ i ∈ Finset.range (f.deg + 1), g.coeff i * x ^ i * y ^ (f.deg - i) := by
    rw [h]; rfl
  rw [hg]
  show ∑ i ∈ Finset.range (f.deg + 1), (f.coeff i + g.coeff i) * x ^ i * y ^ (f.deg - i) =
    (∑ i ∈ Finset.range (f.deg + 1), f.coeff i * x ^ i * y ^ (f.deg - i)) +
    ∑ i ∈ Finset.range (f.deg + 1), g.coeff i * x ^ i * y ^ (f.deg - i)
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Negation of a form. -/
def neg (f : HForm) : HForm := ⟨f.deg, fun i => -f.coeff i⟩

lemma eval_neg (f : HForm) (x y : ℤ) : (f.neg).eval x y = -f.eval x y := by
  have h : ∀ i : ℕ, (-f.coeff i) * x ^ i * y ^ (f.deg - i) =
      -(f.coeff i * x ^ i * y ^ (f.deg - i)) := fun i => by ring
  simp only [eval, neg, h, Finset.sum_neg_distrib]

/-- Subtraction of two forms of the same degree. -/
def sub (f g : HForm) (h : f.deg = g.deg) : HForm := f.add g.neg (by simp [neg, h])

lemma sub_deg (f g : HForm) (h : f.deg = g.deg) : (f.sub g h).deg = f.deg := rfl

lemma eval_sub (f g : HForm) (h : f.deg = g.deg) (x y : ℤ) :
    (f.sub g h).eval x y = f.eval x y - g.eval x y := by
  simp [sub, eval_add, eval_neg, sub_eq_add_neg]

/-- Scalar multiplication of a form by an integer. -/
def cmul (c : ℤ) (f : HForm) : HForm := mul (const c) f

lemma cmul_deg (c : ℤ) (f : HForm) : (cmul c f).deg = f.deg := zero_add _

lemma eval_cmul (c : ℤ) (f : HForm) (x y : ℤ) : (cmul c f).eval x y = c * f.eval x y := by
  show (mul (const c) f).eval x y = c * f.eval x y
  rw [eval_mul, eval_const]

/-- Sum of a family of forms of the same degree. -/
def sum {ι : Type*} (s : Finset ι) (F : ι → HForm) (n : ℕ)
    (_h : ∀ i ∈ s, (F i).deg = n) : HForm :=
  ⟨n, fun k => ∑ i ∈ s, (F i).coeff k⟩

lemma sum_deg {ι : Type*} (s : Finset ι) (F : ι → HForm) (n : ℕ)
    (h : ∀ i ∈ s, (F i).deg = n) : (sum s F n h).deg = n := rfl

lemma eval_sum {ι : Type*} (s : Finset ι) (F : ι → HForm) (n : ℕ)
    (h : ∀ i ∈ s, (F i).deg = n) (x y : ℤ) :
    (sum s F n h).eval x y = ∑ i ∈ s, (F i).eval x y := by
  simp only [eval, sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [h i hi]

/-- Products of families of homogeneous forms exist with the expected degree
and evaluation. -/
lemma exists_prod {ι : Type*} (s : Finset ι) (F : ι → HForm) :
    ∃ G : HForm, G.deg = ∑ i ∈ s, (F i).deg ∧
      ∀ x y, G.eval x y = ∏ i ∈ s, (F i).eval x y := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨const 1, show (0 : ℕ) = _ by rw [Finset.sum_empty],
      fun x y => by rw [eval_const, Finset.prod_empty]⟩
  | insert a s ha ih =>
    obtain ⟨G, hGdeg, hGeval⟩ := ih
    refine ⟨mul G (F a), ?_, ?_⟩
    · show G.deg + (F a).deg = _
      rw [hGdeg, Finset.sum_insert ha, add_comm]
    · intro x y
      rw [eval_mul, hGeval, Finset.prod_insert ha, mul_comm]

/-- Evaluation at the antipode of a form of even degree. -/
lemma eval_neg_of_even (f : HForm) (hfe : Even f.deg) (x y : ℤ) :
    f.eval (-x) (-y) = f.eval x y := by
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range, Nat.lt_succ_iff] at hi
  have h1 : (-1 : ℤ) ^ (i + (f.deg - i)) = 1 := by
    rw [Nat.add_sub_cancel' hi]
    exact hfe.neg_one_pow
  calc f.coeff i * (-x) ^ i * (-y) ^ (f.deg - i)
      = f.coeff i * x ^ i * y ^ (f.deg - i) * ((-1) ^ i * (-1) ^ (f.deg - i)) := by
        rw [neg_pow, neg_pow]; ring
    _ = f.coeff i * x ^ i * y ^ (f.deg - i) := by rw [← pow_add, h1]; ring

end HForm

/-- Canonical orientation of a nonzero lattice point: exactly one of `s`, `-s`
satisfies `canon s`. -/
def canon (s : ℤ × ℤ) : Prop := 0 < s.1 ∨ (s.1 = 0 ∧ 0 < s.2)

instance (s : ℤ × ℤ) : Decidable (canon s) := by
  unfold canon
  infer_instance

lemma canon_iff_not_neg {s : ℤ × ℤ} (hs : s ≠ (0, 0)) : canon s ↔ ¬ canon (-s) := by
  have hf : (-s).1 = -s.1 := rfl
  have hd : (-s).2 = -s.2 := rfl
  have hs12 : ¬(s.1 = 0 ∧ s.2 = 0) := fun h => hs (Prod.ext h.1 h.2)
  unfold canon
  rw [hf, hd]
  constructor
  · rintro (h | ⟨e, h⟩) (h' | ⟨e', h'⟩) <;> lia
  · intro h
    by_cases e1 : s.1 = 0
    · by_cases e2 : 0 < s.2
      · exact Or.inr ⟨e1, e2⟩
      · exfalso
        have e2' : s.2 < 0 := by
          have hz : s.2 ≠ 0 := fun hz => hs12 ⟨e1, hz⟩
          lia
        apply h
        exact Or.inr ⟨by lia, by lia⟩
    · by_cases h1 : 0 < s.1
      · exact Or.inl h1
      · exfalso
        apply h
        exact Or.inl (by lia)

/-- Representative of the antipodal class of `s`, chosen inside `S`
whenever possible. -/
def rep (S : Finset (ℤ × ℤ)) (s : ℤ × ℤ) : ℤ × ℤ :=
  if canon s ∧ s ∈ S then s else if canon (-s) ∧ (-s) ∈ S then -s else s

lemma rep_mem {S : Finset (ℤ × ℤ)} {s : ℤ × ℤ} (hs : s ∈ S) : rep S s ∈ S := by
  unfold rep
  by_cases h1 : canon s ∧ s ∈ S
  · rw [ite_eq_left h1]; exact hs
  · rw [ite_eq_right h1]
    by_cases h2 : canon (-s) ∧ (-s) ∈ S
    · rw [ite_eq_left h2]; exact h2.2
    · rw [ite_eq_right h2]; exact hs

lemma rep_eq_self_or_neg {S : Finset (ℤ × ℤ)} {s : ℤ × ℤ} :
    rep S s = s ∨ rep S s = -s := by
  unfold rep
  by_cases h1 : canon s ∧ s ∈ S
  · rw [ite_eq_left h1]; exact Or.inl rfl
  · rw [ite_eq_right h1]
    by_cases h2 : canon (-s) ∧ (-s) ∈ S
    · rw [ite_eq_left h2]; exact Or.inr rfl
    · rw [ite_eq_right h2]; exact Or.inl rfl

lemma rep_neg {S : Finset (ℤ × ℤ)} {s : ℤ × ℤ} (hs : s ∈ S) (hns : -s ∈ S)
    (hs0 : s ≠ (0, 0)) : rep S (-s) = rep S s := by
  have hcan := canon_iff_not_neg hs0
  by_cases hA : canon s
  · have hB : ¬ canon (-s) := hcan.mp hA
    have hrep_s : rep S s = s := by unfold rep; rw [ite_eq_left ⟨hA, hs⟩]
    have hrep_ns : rep S (-s) = s := by
      unfold rep
      rw [ite_eq_right (fun h => hB h.1)]
      rw [ite_eq_left (by rw [neg_neg]; exact ⟨hA, hs⟩ : canon (-(-s)) ∧ (-(-s)) ∈ S)]
      exact neg_neg s
    rw [hrep_s, hrep_ns]
  · have hB : canon (-s) := by
      by_contra hB
      exact hA (hcan.mpr hB)
    have hrep_s : rep S s = -s := by
      unfold rep
      rw [ite_eq_right (fun h => hA h.1), ite_eq_left ⟨hB, hns⟩]
    have hrep_ns : rep S (-s) = -s := by
      unfold rep
      rw [ite_eq_left ⟨hB, hns⟩]
    rw [hrep_s, hrep_ns]

lemma rep_idem {S : Finset (ℤ × ℤ)} {s : ℤ × ℤ} (hs : s ∈ S) (hs0 : s ≠ (0, 0)) :
    rep S (rep S s) = rep S s := by
  rcases rep_eq_self_or_neg (S := S) (s := s) with h | h
  · conv_lhs => rw [h]
  · have hns : -s ∈ S := by
      have hm := rep_mem hs
      rw [h] at hm
      exact hm
    calc rep S (rep S s) = rep S (-s) := by rw [h]
      _ = rep S s := rep_neg hs hns hs0

/-- The set of antipodal class representatives of `S`. -/
def T (S : Finset (ℤ × ℤ)) : Finset (ℤ × ℤ) := S.image (rep S)

lemma T_subset {S : Finset (ℤ × ℤ)} : T S ⊆ S := by
  intro t ht
  rw [T, Finset.mem_image] at ht
  obtain ⟨s, hs, rfl⟩ := ht
  exact rep_mem hs

lemma rep_mem_T {S : Finset (ℤ × ℤ)} {s : ℤ × ℤ} (hs : s ∈ S) : rep S s ∈ T S :=
  Finset.mem_image_of_mem _ hs

lemma rep_spec {S : Finset (ℤ × ℤ)} {s : ℤ × ℤ} (_hs : s ∈ S) :
    s = rep S s ∨ s = -rep S s := by
  rcases rep_eq_self_or_neg (S := S) (s := s) with h | h
  · exact Or.inl h.symm
  · exact Or.inr (by rw [h, neg_neg])

lemma ne_zero_of_isCoprime {s : ℤ × ℤ} (h : IsCoprime s.1 s.2) : s ≠ (0, 0) := by
  intro hz
  subst hz
  change IsCoprime (0 : ℤ) (0 : ℤ) at h
  rw [Int.isCoprime_iff_gcd_eq_one] at h
  simp at h

lemma T_ne_neg {S : Finset (ℤ × ℤ)} (hS : ∀ s ∈ S, IsCoprime s.1 s.2) {t₁ t₂ : ℤ × ℤ}
    (ht₁ : t₁ ∈ T S) (ht₂ : t₂ ∈ T S) (hne : t₁ ≠ t₂) : t₁ ≠ -t₂ := by
  intro h
  rw [T, Finset.mem_image] at ht₁ ht₂
  obtain ⟨s₁, hs₁, rfl⟩ := ht₁
  obtain ⟨s₂, hs₂, rfl⟩ := ht₂
  have hz₁ : s₁ ≠ (0, 0) := ne_zero_of_isCoprime (hS s₁ hs₁)
  have hz₂ : s₂ ≠ (0, 0) := ne_zero_of_isCoprime (hS s₂ hs₂)
  have hrz₂ : rep S s₂ ≠ (0, 0) := ne_zero_of_isCoprime (hS _ (rep_mem hs₂))
  have key : rep S s₁ = rep S s₂ := by
    calc rep S s₁ = rep S (rep S s₁) := (rep_idem hs₁ hz₁).symm
      _ = rep S (-rep S s₂) := by rw [h]
      _ = rep S (rep S s₂) :=
        rep_neg (rep_mem hs₂) (by rw [← h]; exact rep_mem hs₁) hrz₂
      _ = rep S s₂ := rep_idem hs₂ hz₂
  exact hne key

/-- If two primitive points have cross-product zero, they are equal or
antipodal. -/
lemma eq_or_neg_of_mul_eq {x₁ y₁ x₂ y₂ : ℤ} (h₁ : IsCoprime x₁ y₁) (h₂ : IsCoprime x₂ y₂)
    (h : x₁ * y₂ = x₂ * y₁) : (x₁ = x₂ ∧ y₁ = y₂) ∨ (x₁ = -x₂ ∧ y₁ = -y₂) := by
  have hdvd1 : x₁ ∣ x₂ :=
    h₁.dvd_of_dvd_mul_left ⟨y₂, by rw [mul_comm y₁ x₂]; exact h.symm⟩
  have hdvd2 : x₂ ∣ x₁ :=
    h₂.dvd_of_dvd_mul_left ⟨y₁, by rw [mul_comm y₂ x₁]; exact h⟩
  have hdvd3 : y₁ ∣ y₂ :=
    h₁.symm.dvd_of_dvd_mul_left ⟨x₂, by rw [mul_comm y₁ x₂]; exact h⟩
  have hdvd4 : y₂ ∣ y₁ :=
    h₂.symm.dvd_of_dvd_mul_left ⟨x₁, by rw [mul_comm y₂ x₁]; exact h.symm⟩
  have hx : x₁ = x₂ ∨ x₁ = -x₂ := by
    have h12 : x₁.natAbs ∣ x₂.natAbs := Int.natAbs_dvd_natAbs.mpr hdvd1
    have h21 : x₂.natAbs ∣ x₁.natAbs := Int.natAbs_dvd_natAbs.mpr hdvd2
    exact Int.natAbs_eq_natAbs_iff.mp (Nat.dvd_antisymm h12 h21)
  have hy : y₁ = y₂ ∨ y₁ = -y₂ := by
    have h12 : y₁.natAbs ∣ y₂.natAbs := Int.natAbs_dvd_natAbs.mpr hdvd3
    have h21 : y₂.natAbs ∣ y₁.natAbs := Int.natAbs_dvd_natAbs.mpr hdvd4
    exact Int.natAbs_eq_natAbs_iff.mp (Nat.dvd_antisymm h12 h21)
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact Or.inl ⟨hx, hy⟩
  · have h2 : x₂ * y₂ = 0 := by
      rw [hx, hy] at h
      have hh : (2 : ℤ) * (x₂ * y₂) = 0 := by linear_combination h
      rcases mul_eq_zero.mp hh with h2' | h2'
      · norm_num at h2'
      · exact h2'
    rcases mul_eq_zero.mp h2 with hx0 | hy0
    · exact Or.inr ⟨by rw [hx, hx0, neg_zero], hy⟩
    · have hy10 : y₁ = 0 := by rw [hy, hy0, neg_zero]
      exact Or.inl ⟨hx, by rw [hy10, hy0]⟩
  · have h2 : x₂ * y₂ = 0 := by
      rw [hx, hy] at h
      have hh : (2 : ℤ) * (x₂ * y₂) = 0 := by linear_combination -h
      rcases mul_eq_zero.mp hh with h2' | h2'
      · norm_num at h2'
      · exact h2'
    rcases mul_eq_zero.mp h2 with hx0 | hy0
    · have hx10 : x₁ = 0 := by rw [hx, hx0, neg_zero]
      exact Or.inl ⟨by rw [hx10, hx0], hy⟩
    · have hy10 : y₁ = 0 := by rw [hy, hy0]
      exact Or.inr ⟨hx, by rw [hy10, hy0, neg_zero]⟩
  · exact Or.inr ⟨hx, hy⟩

/-- Points of distinct classes in `T` have nonzero determinant. -/
lemma det_ne_zero {S : Finset (ℤ × ℤ)} (hS : ∀ s ∈ S, IsCoprime s.1 s.2) {t t' : ℤ × ℤ}
    (ht : t ∈ T S) (ht' : t' ∈ T S) (hne : t' ≠ t) :
    t'.2 * t.1 - t'.1 * t.2 ≠ 0 := by
  intro h
  have hmem_t : t ∈ S := T_subset ht
  have hmem_t' : t' ∈ S := T_subset ht'
  have h1 : t'.2 * t.1 = t'.1 * t.2 := sub_eq_zero.mp h
  have h0 : t.1 * t'.2 = t'.1 * t.2 := by
    calc t.1 * t'.2 = t'.2 * t.1 := mul_comm _ _
      _ = t'.1 * t.2 := h1
  rcases eq_or_neg_of_mul_eq (hS t hmem_t) (hS t' hmem_t') h0 with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · exact hne (Prod.ext e1.symm e2.symm)
  · have h' : t' = -t := by
      have e : t = -t' := Prod.ext e1 e2
      rw [e, neg_neg]
    exact T_ne_neg hS ht' ht hne h'

/-- The coordinate form `x`. -/
def Xf : HForm := HForm.linear 1 0

/-- The coordinate form `y`. -/
def Yf : HForm := HForm.linear 0 1

lemma Xf_eval (x y : ℤ) : Xf.eval x y = x := by
  rw [Xf, HForm.eval_linear]
  ring

lemma Yf_eval (x y : ℤ) : Yf.eval x y = y := by
  rw [Yf, HForm.eval_linear]
  ring

lemma Xf_deg : Xf.deg = 1 := rfl

lemma Yf_deg : Yf.deg = 1 := rfl

lemma zmod_natCast_eq_zero_iff_dvd (a n : ℕ) : ((a : ZMod n)) = 0 ↔ n ∣ a := by
  rw [show ((a : ZMod n)) = ((a : ℤ) : ZMod n) by norm_cast,
    ZMod.intCast_zmod_eq_zero_iff_dvd, Int.natCast_dvd_natCast]

lemma not_coprime_of_both_dvd {x y : ℤ} (h : IsCoprime x y) {c : ℤ}
    (hx : c ∣ x) (hy : c ∣ y) : c ∣ 1 := by
  obtain ⟨u, v, huv⟩ := h
  rw [← huv]
  exact dvd_add (hx.mul_left u) (hy.mul_left v)

/-- In `ZMod 2`, the form `x² + xy + y²` does not vanish at a primitive point. -/
lemma two_not_dvd_quad_zmod {x y : ℤ} (h : IsCoprime x y) :
    ((x ^ 2 + x * y + y ^ 2 : ℤ) : ZMod 2) ≠ 0 := by
  intro hcast
  push_cast at hcast
  have h2d : ∀ a b : ZMod 2, ¬(a = 0 ∧ b = 0) → a ^ 2 + a * b + b ^ 2 ≠ 0 := by decide
  have hab : ¬((x : ZMod 2) = 0 ∧ (y : ZMod 2) = 0) := by
    rintro ⟨hx0, hy0⟩
    have h2x : (2 : ℤ) ∣ x := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hx0
    have h2y : (2 : ℤ) ∣ y := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hy0
    have h21 := not_coprime_of_both_dvd h h2x h2y
    norm_num at h21
  exact h2d _ _ hab hcast

/-- In `ZMod p` for an odd prime `p`, the form `x^(p-1) + y^(p-1)` does not
vanish at a primitive point. -/
lemma odd_not_dvd_powsum_zmod {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {x y : ℤ}
    (h : IsCoprime x y) : ((x ^ (p - 1) + y ^ (p - 1) : ℤ) : ZMod p) ≠ 0 := by
  have hp3 : 3 ≤ p := by
    have h2 := hp.two_le
    lia
  have : Fact p.Prime := ⟨hp⟩
  intro hcast
  push_cast at hcast
  have hab : ¬((x : ZMod p) = 0 ∧ (y : ZMod p) = 0) := by
    rintro ⟨hx0, hy0⟩
    have hpx : (p : ℤ) ∣ x := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hx0
    have hpy : (p : ℤ) ∣ y := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hy0
    have hp1 := not_coprime_of_both_dvd h hpx hpy
    rw [show (1 : ℤ) = ((1 : ℕ) : ℤ) by norm_cast, Int.natCast_dvd_natCast] at hp1
    have := Nat.le_of_dvd one_pos hp1
    lia
  by_cases hx0 : (x : ZMod p) = 0
  · have hy0 : (y : ZMod p) ≠ 0 := fun h' => hab ⟨hx0, h'⟩
    rw [hx0, zero_pow (by lia : p - 1 ≠ 0), zero_add] at hcast
    rw [ZMod.pow_card_sub_one_eq_one hy0] at hcast
    exact one_ne_zero hcast
  · by_cases hy0 : (y : ZMod p) = 0
    · rw [hy0, zero_pow (by lia : p - 1 ≠ 0), add_zero] at hcast
      rw [ZMod.pow_card_sub_one_eq_one hx0] at hcast
      exact one_ne_zero hcast
    · rw [ZMod.pow_card_sub_one_eq_one hx0, ZMod.pow_card_sub_one_eq_one hy0] at hcast
      have h2ne : (2 : ZMod p) ≠ 0 := by
        have h2i : ¬ (p ∣ 2) := by
          intro hd2
          have := Nat.le_of_dvd (by norm_num) hd2
          lia
        intro h20
        apply h2i
        have h' : (((2 : ℕ) : ℤ) : ZMod p) = 0 := by
          rw [show (((2 : ℕ) : ℤ) : ZMod p) = (2 : ZMod p) by norm_cast]
          exact h20
        exact Int.natCast_dvd_natCast.mp ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h')
      have h11 : (1 : ZMod p) + 1 = 2 := by norm_cast
      rw [h11] at hcast
      exact h2ne hcast

/-- The local form used modulo the prime `p`: `x² + xy + y²` for `p = 2` and
`x^(p-1) + y^(p-1)` for odd `p`. -/
def Gform (p : ℕ) : HForm :=
  if p = 2 then ((Xf.pow 2).add (Xf.mul Yf) (by rw [HForm.pow_deg]; rfl)).add (Yf.pow 2)
    (by show ((Xf.pow 2).add (Xf.mul Yf) _).deg = (Yf.pow 2).deg
        show (Xf.pow 2).deg = (Yf.pow 2).deg
        rw [HForm.pow_deg, HForm.pow_deg, Xf_deg, Yf_deg])
  else (Xf.pow (p - 1)).add (Yf.pow (p - 1))
    (by show (Xf.pow (p - 1)).deg = (Yf.pow (p - 1)).deg
        rw [HForm.pow_deg, HForm.pow_deg, Xf_deg, Yf_deg])

lemma Gform_deg (p : ℕ) : (Gform p).deg = if p = 2 then 2 else p - 1 := by
  rw [Gform]
  split_ifs with hp2
  · show (Xf.pow 2).deg = 2
    rw [HForm.pow_deg, Xf_deg]
  · show (Xf.pow (p - 1)).deg = p - 1
    rw [HForm.pow_deg, Xf_deg, mul_one]

lemma Gform_eval_zmod (p : ℕ) [Fact p.Prime] {x y : ℤ} (hcop : IsCoprime x y) :
    ((Gform p).eval x y : ZMod p) ≠ 0 := by
  rw [Gform]
  by_cases hp2 : p = 2
  · subst hp2
    rw [ite_eq_left rfl, HForm.eval_add, HForm.eval_add, HForm.eval_pow, HForm.eval_mul,
      HForm.eval_pow, Xf_eval, Yf_eval]
    exact two_not_dvd_quad_zmod hcop
  · rw [ite_eq_right hp2, HForm.eval_add, HForm.eval_pow, HForm.eval_pow, Xf_eval, Yf_eval]
    exact odd_not_dvd_powsum_zmod Fact.out hp2 hcop

/-- The key construction: a homogeneous form `g` of positive even degree whose
value at every point of `T S` is nonzero and not divisible by any prime
dividing `D` (the product of all inter-class determinants). -/
lemma exists_g (S : Finset (ℤ × ℤ)) (hS : ∀ s ∈ S, IsCoprime s.1 s.2)
    (_hne : (T S).Nonempty) :
    ∃ g : HForm, Even g.deg ∧ 0 < g.deg ∧
      (∀ t ∈ T S, g.eval t.1 t.2 ≠ 0) ∧
      (∀ t ∈ T S, ∀ p : ℕ, p.Prime →
        (p : ℤ) ∣ (∏ t ∈ T S, ∏ t' ∈ (T S).erase t, (t'.2 * t.1 - t'.1 * t.2)) →
        ¬ (p : ℤ) ∣ g.eval t.1 t.2) := by
  set TS := T S with hTS
  -- the product of all determinants between distinct classes
  set D : ℤ := ∏ t ∈ TS, ∏ t' ∈ TS.erase t, (t'.2 * t.1 - t'.1 * t.2) with hD
  have hdne : ∀ t ∈ TS, ∀ t' ∈ TS.erase t, t'.2 * t.1 - t'.1 * t.2 ≠ 0 := by
    intro t ht t' ht'
    rw [Finset.mem_erase] at ht'
    exact det_ne_zero hS ht ht'.2 ht'.1
  have hDne : D ≠ 0 := by
    rw [hD, Finset.prod_ne_zero_iff]
    intro t ht
    rw [Finset.prod_ne_zero_iff]
    exact hdne t ht
  -- bad primes
  set Ps : Finset ℕ := D.natAbs.primeFactors with hPs
  -- the degree
  set E : ℕ := 2 * ∏ p ∈ Ps, (p - 1) with hE
  have hEe : Even E := ⟨∏ p ∈ Ps, (p - 1), by rw [hE]; ring⟩
  have hEpos : 0 < E := by
    rw [hE]
    apply Nat.mul_pos (by norm_num)
    exact Finset.prod_pos (fun p hp => by
      have := (Nat.prime_of_mem_primeFactors hp).two_le
      lia)
  -- divisibility of the degree by the local degrees
  have hdegE : ∀ p ∈ Ps, (Gform p).deg ∣ E := by
    intro p hp
    rw [Gform_deg, hE]
    by_cases hp2 : p = 2
    · rw [ite_eq_left hp2]
      exact dvd_mul_right 2 _
    · rw [ite_eq_right hp2]
      exact dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem (fun q => q - 1) hp) 2
  -- powers of the local forms
  set ex : ℕ → ℕ := fun p => E / (Gform p).deg with hex
  have hexE : ∀ p ∈ Ps, ex p * (Gform p).deg = E :=
    fun p hp => Nat.div_mul_cancel (hdegE p hp)
  set Hp : ℕ → HForm := fun p => (Gform p).pow (ex p) with hHp
  have hHpdeg : ∀ p ∈ Ps, (Hp p).deg = E := by
    intro p hp
    show ((Gform p).pow (ex p)).deg = E
    rw [HForm.pow_deg]
    exact hexE p hp
  have hHpne : ∀ t ∈ TS, ∀ p ∈ Ps, ((Hp p).eval t.1 t.2 : ZMod p) ≠ 0 := by
    intro t ht p hp
    have : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
    show (((Gform p).pow (ex p)).eval t.1 t.2 : ZMod p) ≠ 0
    rw [HForm.eval_pow]
    push_cast
    exact pow_ne_zero _ (Gform_eval_zmod p (hS t (T_subset ht)))
  -- the CRT modulus and weights
  set M : ℕ := ∏ p ∈ Ps, p with hM
  have hMpos : 0 < M :=
    Finset.prod_pos (fun p hp => (Nat.prime_of_mem_primeFactors hp).pos)
  set Mp : ℕ → ℕ := fun p => ∏ q ∈ Ps.erase p, q with hMp
  have hMpe : ∀ p ∈ Ps, p * Mp p = M := by
    intro p hp
    show p * (∏ q ∈ Ps.erase p, q) = ∏ q ∈ Ps, q
    exact Finset.mul_prod_erase Ps (fun q => q) hp
  have hcopMp : ∀ p ∈ Ps, Nat.Coprime (Mp p) p := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hpp]
    intro hdvd
    have hdvd' := (hpp.prime.dvd_finsetProd_iff (fun q => (q : ℕ))).mp hdvd
    obtain ⟨q, hq, hpq⟩ := hdvd'
    rw [Finset.mem_erase] at hq
    have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq.2
    have hpqeq : p = q := (Nat.prime_dvd_prime_iff_eq hpp hqp).mp hpq
    exact hq.1 hpqeq.symm
  set up : ℕ → ℤ := fun p => Int.gcdA (Mp p : ℤ) (p : ℤ) with hup
  set wp : ℕ → ℤ := fun p => Int.gcdB (Mp p : ℤ) (p : ℤ) with hwp
  have hbez : ∀ p ∈ Ps, (1 : ℤ) = (Mp p : ℤ) * up p + (p : ℤ) * wp p := by
    intro p hp
    have hg : Int.gcd (Mp p : ℤ) (p : ℤ) = 1 := by
      have h1 : Int.gcd (Mp p : ℤ) (p : ℤ) = Nat.gcd (Mp p) p := rfl
      rw [h1, ← Nat.coprime_iff_gcd_eq_one]
      exact hcopMp p hp
    have h2 := Int.gcd_eq_gcd_ab (Mp p : ℤ) (p : ℤ)
    rw [hg] at h2
    show (1 : ℤ) = (Mp p : ℤ) * Int.gcdA (Mp p : ℤ) (p : ℤ) +
      (p : ℤ) * Int.gcdB (Mp p : ℤ) (p : ℤ)
    simpa using h2
  -- the CRT combination
  set G : HForm := HForm.sum Ps (fun p => HForm.cmul (up p * (Mp p : ℤ)) (Hp p)) E
    (by intro p hp
        rw [HForm.cmul_deg]
        exact hHpdeg p hp) with hG
  have hGeval : ∀ x y : ℤ, G.eval x y =
      ∑ p ∈ Ps, (up p * (Mp p : ℤ)) * (Hp p).eval x y := by
    intro x y
    rw [hG, HForm.eval_sum]
    apply Finset.sum_congr rfl
    intro p hp
    show (HForm.cmul (up p * (Mp p : ℤ)) (Hp p)).eval x y =
      (up p * (Mp p : ℤ)) * (Hp p).eval x y
    rw [HForm.eval_cmul]
  have hCRT : ∀ t ∈ TS, ∀ p ∈ Ps, (G.eval t.1 t.2 : ZMod p) = (Hp p).eval t.1 t.2 := by
    intro t ht p hp
    have h1 : (up p : ZMod p) * (Mp p : ZMod p) = 1 := by
      have hbez' := hbez p hp
      have hcast : (((Mp p : ℤ) * up p + (p : ℤ) * wp p : ℤ) : ZMod p) = 1 := by
        rw [← hbez']
        norm_cast
      push_cast at hcast
      have hp0 : ((p : ZMod p)) = 0 := (zmod_natCast_eq_zero_iff_dvd p p).mpr dvd_rfl
      rw [hp0, zero_mul, add_zero] at hcast
      rw [mul_comm]
      exact hcast
    rw [hGeval]
    push_cast
    rw [Finset.sum_eq_single p]
    · rw [h1, one_mul]
    · intro q hq hqp
      have hpdvd : p ∣ Mp q := by
        show p ∣ ∏ r ∈ Ps.erase q, r
        exact Finset.dvd_prod_of_mem (fun r => r) (Finset.mem_erase.mpr ⟨hqp.symm, hp⟩)
      have hM0 : ((Mp q : ℕ) : ZMod p) = 0 :=
        (zmod_natCast_eq_zero_iff_dvd (Mp q) p).mpr hpdvd
      rw [hM0, mul_zero, zero_mul]
    · intro hnotin
      exact (hnotin hp).elim
  -- shift to make all values nonzero
  set bad : Finset ℤ := TS.image (fun t => -(G.eval t.1 t.2) / ((M : ℤ) * (t.1 ^ E + t.2 ^ E)))
    with hbad
  obtain ⟨t₀, ht₀⟩ : ∃ a : ℤ, a ∉ bad := Infinite.exists_notMem_finset bad
  set g : HForm := G.add (HForm.cmul ((M : ℤ) * t₀) ((Xf.pow E).add (Yf.pow E)
    (by show (Xf.pow E).deg = (Yf.pow E).deg
        rw [HForm.pow_deg, HForm.pow_deg, Xf_deg, Yf_deg])))
    (by show G.deg = (HForm.cmul ((M : ℤ) * t₀) ((Xf.pow E).add (Yf.pow E) _)).deg
        rw [HForm.cmul_deg]
        show E = (Xf.pow E).deg
        rw [HForm.pow_deg, Xf_deg, mul_one]) with hg
  have hgdeg : g.deg = E := rfl
  have hgeval : ∀ x y : ℤ, g.eval x y = G.eval x y + (M : ℤ) * t₀ * (x ^ E + y ^ E) := by
    intro x y
    rw [hg, HForm.eval_add, HForm.eval_cmul, HForm.eval_add, HForm.eval_pow, HForm.eval_pow,
      Xf_eval, Yf_eval]
  have hgne : ∀ t ∈ TS, g.eval t.1 t.2 ≠ 0 := by
    intro t ht
    rw [hgeval]
    intro hzero
    have ht0 : t ≠ (0, 0) := ne_zero_of_isCoprime (hS t (T_subset ht))
    have hCpos : (0 : ℤ) < (M : ℤ) * (t.1 ^ E + t.2 ^ E) := by
      apply mul_pos (by exact_mod_cast hMpos)
      have h1 : 0 ≤ t.1 ^ E := hEe.pow_nonneg _
      have h2 : 0 ≤ t.2 ^ E := hEe.pow_nonneg _
      by_contra hsum
      have hsum2 : t.1 ^ E + t.2 ^ E ≤ 0 := not_lt.mp hsum
      have h10 : t.1 ^ E = 0 := by lia
      have h20 : t.2 ^ E = 0 := by lia
      have hEne : E ≠ 0 := by lia
      have ht1 : t.1 = 0 := (pow_eq_zero_iff hEne).mp h10
      have ht2 : t.2 = 0 := (pow_eq_zero_iff hEne).mp h20
      exact ht0 (Prod.ext ht1 ht2)
    have heq : (M : ℤ) * (t.1 ^ E + t.2 ^ E) * t₀ = -(G.eval t.1 t.2) := by
      linear_combination hzero
    have hCne : (M : ℤ) * (t.1 ^ E + t.2 ^ E) ≠ 0 := ne_of_gt hCpos
    have heq2 : -(G.eval t.1 t.2) = t₀ * ((M : ℤ) * (t.1 ^ E + t.2 ^ E)) := by
      rw [mul_comm]
      exact heq.symm
    have ht0mem : t₀ ∈ bad := by
      rw [hbad, Finset.mem_image]
      exact ⟨t, ht, Int.ediv_eq_of_eq_mul_left hCne heq2⟩
    exact ht₀ ht0mem
  have hgcop : ∀ t ∈ TS, ∀ p ∈ Ps, ¬ (p : ℤ) ∣ g.eval t.1 t.2 := by
    intro t ht p hp hdvd
    have hcast : ((g.eval t.1 t.2 : ℤ) : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdvd
    rw [hgeval] at hcast
    push_cast at hcast
    have hM0 : ((M : ℕ) : ZMod p) = 0 :=
      (zmod_natCast_eq_zero_iff_dvd M p).mpr (Finset.dvd_prod_of_mem (fun q => q) hp)
    rw [hM0, zero_mul, zero_mul, add_zero] at hcast
    rw [hCRT t ht p hp] at hcast
    exact hHpne t ht p hp hcast
  refine ⟨g, ?_, ?_, hgne, ?_⟩
  · rw [hgdeg]; exact hEe
  · rw [hgdeg]; exact hEpos
  · intro t ht p hpp hpdvdD
    apply hgcop t ht p
    rw [hPs, Nat.mem_primeFactors]
    refine ⟨hpp, ?_, ?_⟩
    · have h1 : (p : ℤ).natAbs ∣ D.natAbs := Int.natAbs_dvd_natAbs.mpr hpdvdD
      rwa [Int.natAbs_natCast] at h1
    · exact Int.natAbs_ne_zero.mpr hDne


snip end

problem imo2017_p6 (S : Finset (ℤ × ℤ)) (hS : ∀ s ∈ S, gcd s.1 s.2 = 1) :
    ∃ n : ℕ, 0 < n ∧ ∃ a : ℕ → ℤ,
      ∀ s ∈ S, ∑ i ∈ Finset.range (n + 1), a i * s.1 ^ i * s.2 ^ (n - i) = 1 := by
  have hS' : ∀ s ∈ S, IsCoprime s.1 s.2 := by
    intro s hs
    rw [Int.isCoprime_iff_gcd_eq_one]
    have h := hS s hs
    rw [← Int.coe_gcd] at h
    exact_mod_cast h
  by_cases hTne : (T S).Nonempty
  · -- main construction
    obtain ⟨g, hge, hgpos, hgne, hgcop⟩ := exists_g S hS' hTne
    set TS := T S with hTS
    set E := g.deg with hE
    -- value of `g` at `t`
    set v : ℤ × ℤ → ℤ := fun t => g.eval t.1 t.2 with hv
    -- Bézout linear form with `Lf t` evaluating to `1` at `t`
    set Lf : ℤ × ℤ → HForm := fun t => HForm.linear (Int.gcdA t.1 t.2) (Int.gcdB t.1 t.2)
      with hLf
    have hL : ∀ t ∈ TS, (Lf t).eval t.1 t.2 = 1 := by
      intro t ht
      show (HForm.linear (Int.gcdA t.1 t.2) (Int.gcdB t.1 t.2)).eval t.1 t.2 = 1
      rw [HForm.eval_linear]
      have hbez := Int.gcd_eq_gcd_ab t.1 t.2
      have hgcd1 : Int.gcd t.1 t.2 = 1 := Int.isCoprime_iff_gcd_eq_one.mp (hS' t (T_subset ht))
      rw [hgcd1] at hbez
      linear_combination hbez.symm
    -- linear form vanishing on the class of `t`
    set ell : ℤ × ℤ → HForm := fun t => HForm.linear t.2 (-t.1) with hell
    have hell_eval : ∀ t : ℤ × ℤ, ∀ x y : ℤ, (ell t).eval x y = t.2 * x - t.1 * y := by
      intro t x y
      show (HForm.linear t.2 (-t.1)).eval x y = t.2 * x - t.1 * y
      rw [HForm.eval_linear]
      ring
    -- the determinant product `Δ t`
    set Δ : ℤ × ℤ → ℤ := fun t => ∏ t' ∈ TS.erase t, ((ell t').eval t.1 t.2) ^ E with hΔ
    have hΔne : ∀ t ∈ TS, Δ t ≠ 0 := by
      intro t ht
      show (∏ t' ∈ TS.erase t, ((ell t').eval t.1 t.2) ^ E) ≠ 0
      rw [Finset.prod_ne_zero_iff]
      intro t' ht'
      rw [Finset.mem_erase] at ht'
      rw [hell_eval]
      exact pow_ne_zero E (det_ne_zero hS' ht ht'.2 ht'.1)
    -- `v t` and `Δ t` are coprime
    have hgcoprime : ∀ t ∈ TS, Int.gcd (v t) (Δ t) = 1 := by
      intro t ht
      by_contra h1
      obtain ⟨p, hpp, hpdvd⟩ := Nat.exists_prime_and_dvd h1
      have hpv : (p : ℤ) ∣ v t := dvd_trans (Int.natCast_dvd_natCast.mpr hpdvd) (Int.gcd_dvd_left (v t) (Δ t))
      have hpΔ : (p : ℤ) ∣ Δ t := dvd_trans (Int.natCast_dvd_natCast.mpr hpdvd) (Int.gcd_dvd_right (v t) (Δ t))
      have hpP : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hpp
      have h2 : ∃ t' ∈ TS.erase t, (p : ℤ) ∣ ((ell t').eval t.1 t.2) ^ E :=
        Prime.exists_mem_finset_dvd hpP hpΔ
      obtain ⟨t', ht', hp3⟩ := h2
      have hp4 : (p : ℤ) ∣ (ell t').eval t.1 t.2 := hpP.dvd_of_dvd_pow hp3
      rw [hell_eval] at hp4
      have hpD : (p : ℤ) ∣ ∏ t ∈ TS, ∏ t' ∈ TS.erase t, (t'.2 * t.1 - t'.1 * t.2) :=
        dvd_trans hp4 (dvd_trans
          (Finset.dvd_prod_of_mem (fun t' : ℤ × ℤ => (t'.2 * t.1 - t'.1 * t.2)) ht')
          (Finset.dvd_prod_of_mem (fun t : ℤ × ℤ => ∏ t' ∈ TS.erase t, (t'.2 * t.1 - t'.1 * t.2)) ht))
      exact hgcop t ht p hpp hpD hpv
    -- the Euler exponent
    set K : ℕ := TS.card * ∏ t ∈ TS, (Δ t).natAbs.totient with hK
    have htotpos : ∀ t ∈ TS, 0 < (Δ t).natAbs.totient := by
      intro t ht
      exact Nat.totient_pos.mpr (Int.natAbs_pos.mpr (hΔne t ht))
    have hKpos : 0 < K := by
      rw [hK]
      exact Nat.mul_pos (Finset.card_pos.mpr hTne) (Finset.prod_pos htotpos)
    have hKge : TS.card ≤ K := by
      rw [hK]
      have h1 : 1 ≤ ∏ t ∈ TS, (Δ t).natAbs.totient := Finset.prod_pos htotpos
      calc TS.card = TS.card * 1 := (Nat.mul_one _).symm
        _ ≤ TS.card * ∏ t ∈ TS, (Δ t).natAbs.totient := Nat.mul_le_mul_left _ h1
    -- Euler's theorem: `Δ t ∣ v t ^ K - 1`
    have hEuler : ∀ t ∈ TS, Δ t ∣ v t ^ K - 1 := by
      intro t ht
      have hcopN : Nat.Coprime (v t).natAbs (Δ t).natAbs := by
        rw [Nat.coprime_iff_gcd_eq_one]
        exact hgcoprime t ht
      have hKdiv : (Δ t).natAbs.totient ∣ K := by
        rw [hK]
        exact dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem (fun t => (Δ t).natAbs.totient) ht)
          TS.card
      have hmain : ((Δ t).natAbs : ℤ) ∣ v t ^ K - 1 := by
        have hu : IsUnit (v t : ZMod (Δ t).natAbs) := by
          have hu' : IsUnit ((v t).natAbs : ZMod (Δ t).natAbs) :=
            (ZMod.isUnit_iff_coprime (v t).natAbs (Δ t).natAbs).mpr hcopN
          rcases Int.natAbs_eq (v t) with habs | habs
          · rw [habs, Int.cast_natCast]; exact hu'
          · rw [habs, Int.cast_neg, Int.cast_natCast]; exact hu'.neg
        obtain ⟨u, hu⟩ := hu
        have h1 : (v t : ZMod (Δ t).natAbs) ^ (Δ t).natAbs.totient = 1 := by
          rw [← hu, ← Units.val_pow_eq_pow_val, ZMod.pow_totient u, Units.val_one]
        have h2 : (v t : ZMod (Δ t).natAbs) ^ K = 1 := by
          rw [show K = (Δ t).natAbs.totient * (K / (Δ t).natAbs.totient) from
            (Nat.mul_div_cancel' hKdiv).symm, pow_mul, h1, one_pow]
        have h3 : (((v t) ^ K - 1 : ℤ) : ZMod (Δ t).natAbs) = 0 := by
          push_cast
          rw [h2]
          ring
        exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h3
      exact Int.natAbs_dvd.mp hmain
    -- correction constants
    set c : ℤ × ℤ → ℤ := fun t => (v t ^ K - 1) / Δ t with hc
    have hct : ∀ t ∈ TS, c t * Δ t = v t ^ K - 1 := by
      intro t ht
      show (v t ^ K - 1) / Δ t * Δ t = v t ^ K - 1
      exact Int.ediv_mul_cancel (hEuler t ht)
    -- correction exponent
    set m : ℕ := E * K - (TS.card - 1) * E with hm
    have hmle : (TS.card - 1) * E ≤ E * K := by
      rw [Nat.mul_comm E K]
      have h1 := hKge
      have h2 : TS.card - 1 ≤ K := by lia
      exact Nat.mul_le_mul_right _ h2
    -- the product of the `ℓ`-powers over the other classes
    have hprod : ∀ t ∈ TS, ∃ P : HForm, P.deg = (TS.card - 1) * E ∧
        ∀ x y : ℤ, P.eval x y = ∏ t' ∈ TS.erase t, ((ell t').eval x y) ^ E := by
      intro t ht
      obtain ⟨P, hPdeg, hPeval⟩ := HForm.exists_prod (TS.erase t) (fun t' => (ell t').pow E)
      refine ⟨P, ?_, ?_⟩
      · rw [hPdeg]
        have hterm : ∀ t' ∈ TS.erase t, ((ell t').pow E).deg = E := by
          intro t' _
          rw [HForm.pow_deg, show (ell t').deg = 1 from rfl, mul_one]
        rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_erase_of_mem ht,
          smul_eq_mul]
      · intro x y
        rw [hPeval]
        apply Finset.prod_congr rfl
        intro t' _
        rw [HForm.eval_pow]
    have hprodAll : ∀ t : ℤ × ℤ, ∃ P : HForm, t ∈ TS → P.deg = (TS.card - 1) * E ∧
        (∀ x y : ℤ, P.eval x y = ∏ t' ∈ TS.erase t, ((ell t').eval x y) ^ E) := by
      intro t
      by_cases ht : t ∈ TS
      · obtain ⟨P, hPdeg, hPeval⟩ := hprod t ht
        exact ⟨P, fun _ => ⟨hPdeg, hPeval⟩⟩
      · exact ⟨HForm.const 1, fun h => (ht h).elim⟩
    set P : ℤ × ℤ → HForm := fun t => Classical.choose (hprodAll t) with hP
    have hPdeg : ∀ t ∈ TS, (P t).deg = (TS.card - 1) * E :=
      fun t ht => (Classical.choose_spec (hprodAll t) ht).1
    have hPeval : ∀ t ∈ TS, ∀ x y : ℤ, (P t).eval x y =
        ∏ t' ∈ TS.erase t, ((ell t').eval x y) ^ E :=
      fun t ht => (Classical.choose_spec (hprodAll t) ht).2
    -- the correction forms
    set hform : ℤ × ℤ → HForm := fun t =>
      HForm.mul (HForm.cmul (c t) ((Lf t).pow m)) (P t) with hhform
    have hhformdeg : ∀ t ∈ TS, (hform t).deg = E * K := by
      intro t ht
      show (HForm.cmul (c t) ((Lf t).pow m)).deg + (P t).deg = E * K
      rw [HForm.cmul_deg, HForm.pow_deg, hPdeg t ht, hm]
      show m * (Lf t).deg + (TS.card - 1) * E = E * K
      rw [show (Lf t).deg = 1 from rfl, mul_one]
      exact Nat.sub_add_cancel hmle
    have hhformeval : ∀ t ∈ TS, ∀ x y : ℤ, (hform t).eval x y =
        c t * ((Lf t).eval x y) ^ m * (P t).eval x y := by
      intro t ht x y
      show (HForm.mul (HForm.cmul (c t) ((Lf t).pow m)) (P t)).eval x y = _
      rw [HForm.eval_mul, HForm.eval_cmul, HForm.eval_pow]
    -- the final form
    set F : HForm := HForm.sub (g.pow K) (HForm.sum TS hform (E * K) hhformdeg)
      (by rw [HForm.pow_deg]
          show K * g.deg = E * K
          rw [hE, mul_comm]) with hF
    have hFdeg : F.deg = K * E := by
      show (g.pow K).deg = K * E
      rw [HForm.pow_deg, hE]
    have hFdegpos : 0 < F.deg := by
      rw [hFdeg]
      exact Nat.mul_pos hKpos hgpos
    have hFeven : Even F.deg := by
      rw [hFdeg]
      exact hge.mul_left K
    have hFeval : ∀ s ∈ S, F.eval s.1 s.2 = 1 := by
      intro s hs
      set t := rep S s with ht
      have htT : t ∈ TS := by rw [hTS]; exact rep_mem_T hs
      have hts : s = t ∨ s = -t := rep_spec hs
      have hmain : F.eval t.1 t.2 = 1 := by
        rw [hF, HForm.eval_sub, HForm.eval_pow, HForm.eval_sum]
        have hsum : ∑ t' ∈ TS, (hform t').eval t.1 t.2 = (hform t).eval t.1 t.2 := by
          apply Finset.sum_eq_single t
          · intro t' ht' hne
            rw [hhformeval t' ht', hPeval t' ht']
            have hmem : t ∈ TS.erase t' := Finset.mem_erase.mpr ⟨hne.symm, htT⟩
            have h0 : ((ell t).eval t.1 t.2) ^ E = 0 := by
              rw [hell_eval]
              have h1 : t.2 * t.1 - t.1 * t.2 = 0 := by ring
              rw [h1]
              exact zero_pow (by lia : E ≠ 0)
            rw [Finset.prod_eq_zero hmem h0, mul_zero]
          · intro hnotin
            exact (hnotin htT).elim
        rw [hsum, hhformeval t htT, hL t htT, one_pow, mul_one, hPeval t htT]
        rw [show c t * (∏ t' ∈ TS.erase t, ((ell t').eval t.1 t.2) ^ E) = v t ^ K - 1 from
          hct t htT]
        show v t ^ K - (v t ^ K - 1) = 1
        ring
      rcases hts with h | h
      · rw [h]
        exact hmain
      · rw [h]
        show F.eval (-t).1 (-t).2 = 1
        show F.eval (-t.1) (-t.2) = 1
        rw [HForm.eval_neg_of_even F hFeven]
        exact hmain
    exact ⟨F.deg, hFdegpos, F.coeff, fun s hs => hFeval s hs⟩
  · -- if `T S` is empty then `S` is empty and the claim is vacuous
    have hSe : S = ∅ := by
      by_contra hSne
      have hne2 : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hSne
      obtain ⟨s, hs⟩ := hne2
      exact hTne ⟨rep S s, rep_mem_T hs⟩
    subst hSe
    exact ⟨1, one_pos, fun _ => 0, fun s hs => by simp at hs⟩

end Imo2017P6
