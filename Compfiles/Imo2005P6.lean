/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Data.Int.ConditionallyCompleteOrder
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Star
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import ProblemExtraction

@[expose] public section

problem_file {
  tags := [.Combinatorics],
}

/-!
# International Mathematical Olympiad 2005, Problem 6

In a mathematical competition 6 problems were posed to the contestants. Each
pair of problems was solved by more than 2/5 of the contestants. Nobody solved
all 6 problems. Show that there were at least 2 contestants who each solved
exactly 5 problems.
-/

namespace Imo2005P6

open Finset

snip begin

-- Solution formalized from https://web.evanchen.cc/exams/IMO-2005-notes.pdf

set_option maxHeartbeats 1000000 in
/-- The arithmetic heart of the problem: fifteen pair counts, each at least `(2 * n + 1) / 5`,
with sum `6 * n + 4` and satisfying ten congruences modulo 3, cannot exist. The congruence for
the pair `{a, b} ⊆ {0, 1, 2, 3, 4}` involves the counts for the pairs contained in the
complementary triple together with the pairs joining the triple to problem `5`. -/
theorem arith_core (n : ℕ)
    (t01 t02 t03 t04 t05 t12 t13 t14 t15 t23 t24 t25 t34 t35 t45 : ℕ)
    (hsum : t01 + t02 + t03 + t04 + t05 + t12 + t13 + t14 + t15 + t23 + t24 + t25 + t34 + t35 + t45
      = 6 * n + 4)
    (h01 : 2 * n + 1 ≤ 5 * t01) (h02 : 2 * n + 1 ≤ 5 * t02) (h03 : 2 * n + 1 ≤ 5 * t03)
    (h04 : 2 * n + 1 ≤ 5 * t04) (h05 : 2 * n + 1 ≤ 5 * t05) (h12 : 2 * n + 1 ≤ 5 * t12)
    (h13 : 2 * n + 1 ≤ 5 * t13) (h14 : 2 * n + 1 ≤ 5 * t14) (h15 : 2 * n + 1 ≤ 5 * t15)
    (h23 : 2 * n + 1 ≤ 5 * t23) (h24 : 2 * n + 1 ≤ 5 * t24) (h25 : 2 * n + 1 ≤ 5 * t25)
    (h34 : 2 * n + 1 ≤ 5 * t34) (h35 : 2 * n + 1 ≤ 5 * t35) (h45 : 2 * n + 1 ≤ 5 * t45)
    (c01 : (t01 : ℤ) ≡ 1 + t25 + t35 + t45 + t23 + t24 + t34 [ZMOD 3])
    (c02 : (t02 : ℤ) ≡ 1 + t15 + t35 + t45 + t13 + t14 + t34 [ZMOD 3])
    (c03 : (t03 : ℤ) ≡ 1 + t15 + t25 + t45 + t12 + t14 + t24 [ZMOD 3])
    (c04 : (t04 : ℤ) ≡ 1 + t15 + t25 + t35 + t12 + t13 + t23 [ZMOD 3])
    (c12 : (t12 : ℤ) ≡ 1 + t05 + t35 + t45 + t03 + t04 + t34 [ZMOD 3])
    (c13 : (t13 : ℤ) ≡ 1 + t05 + t25 + t45 + t02 + t04 + t24 [ZMOD 3])
    (c14 : (t14 : ℤ) ≡ 1 + t05 + t25 + t35 + t02 + t03 + t23 [ZMOD 3])
    (c23 : (t23 : ℤ) ≡ 1 + t05 + t15 + t45 + t01 + t04 + t14 [ZMOD 3])
    (c24 : (t24 : ℤ) ≡ 1 + t05 + t15 + t35 + t01 + t03 + t13 [ZMOD 3])
    (c34 : (t34 : ℤ) ≡ 1 + t05 + t15 + t25 + t01 + t02 + t12 [ZMOD 3]) :
    False := by
  -- First, `2 * n + 1` must be divisible by `5`; we case on `(2 * n + 1) % 5` manually,
  -- since `omega` is slow when it has to do the division elimination itself.
  have hdm := Nat.div_add_mod (2 * n + 1) 5
  set k := (2 * n + 1) / 5 with hkD
  have hr : (2 * n + 1) % 5 = 0 ∨ (2 * n + 1) % 5 = 1 ∨ (2 * n + 1) % 5 = 2 ∨
      (2 * n + 1) % 5 = 3 ∨ (2 * n + 1) % 5 = 4 := by omega
  rcases hr with h0 | h1 | h2 | h3 | h4
  swap
  · exfalso; rw [h1] at hdm; omega
  swap
  · exfalso; rw [h2] at hdm; omega
  swap
  · exfalso; rw [h3] at hdm; omega
  swap
  · exfalso; rw [h4] at hdm; omega
  rw [h0] at hdm
  have hk : 2 * n + 1 = 5 * k := by omega
  -- Every pair count is at least `k`, and the sum is `15 * k + 1`, so exactly one of them
  -- is `k + 1`; we check all fifteen possibilities, each contradicting two congruences.
  have hge : k ≤ t01 ∧ k ≤ t02 ∧ k ≤ t03 ∧ k ≤ t04 ∧ k ≤ t05 ∧ k ≤ t12 ∧ k ≤ t13 ∧ k ≤ t14 ∧
      k ≤ t15 ∧ k ≤ t23 ∧ k ≤ t24 ∧ k ≤ t25 ∧ k ≤ t34 ∧ k ≤ t35 ∧ k ≤ t45 := by omega
  have hsumk : t01 + t02 + t03 + t04 + t05 + t12 + t13 + t14 + t15 + t23 + t24 + t25 + t34 +
      t35 + t45 = 15 * k + 1 := by omega
  have clash (x y : ℤ) (r r' : ℤ) (hxy : y = x + 1) (hr : x = 3 * r) (hr' : y = 3 * r') :
      False := by
    omega
  by_cases e01 : t01 = k + 1
  · obtain ⟨h2, h3, h4, h5, h12, h13, h14, h15, h23, h24, h25, h34, h35, h45⟩ :
        t02 = k ∧ t03 = k ∧ t04 = k ∧ t05 = k ∧ t12 = k ∧ t13 = k ∧ t14 = k ∧ t15 = k ∧
        t23 = k ∧ t24 = k ∧ t25 = k ∧ t34 = k ∧ t35 = k ∧ t45 = k := by omega
    subst h2 h3 h4 h5 h12 h13 h14 h15 h23 h24 h25 h34 h35 h45 e01
    rw [Int.modEq_iff_add_fac] at c01 c02
    obtain ⟨r1, c01⟩ := c01; obtain ⟨r2, c02⟩ := c02
    push_cast at c01 c02
    exact clash (5 * (k:ℤ)) (5 * (k:ℤ) + 1) r1 r2 (by ring) (by linarith [c01]) (by linarith [c02])
  by_cases e02 : t02 = k + 1
  · obtain ⟨h1', h3, h4, h5, h12, h13, h14, h15, h23, h24, h25, h34, h35, h45⟩ :
        t01 = k ∧ t03 = k ∧ t04 = k ∧ t05 = k ∧ t12 = k ∧ t13 = k ∧ t14 = k ∧ t15 = k ∧
        t23 = k ∧ t24 = k ∧ t25 = k ∧ t34 = k ∧ t35 = k ∧ t45 = k := by omega
    subst h1' h3 h4 h5 h12 h13 h14 h15 h23 h24 h25 h34 h35 h45 e02
    rw [Int.modEq_iff_add_fac] at c01 c02
    obtain ⟨r1, c01⟩ := c01; obtain ⟨r2, c02⟩ := c02
    push_cast at c01 c02
    exact clash (5 * (k:ℤ)) (5 * (k:ℤ) + 1) r2 r1 (by ring) (by linarith [c02]) (by linarith [c01])
  by_cases e03 : t03 = k + 1
  · obtain ⟨h1', h2', h4, h5, h12, h13, h14, h15, h23, h24, h25, h34, h35, h45⟩ :
        t01 = k ∧ t02 = k ∧ t04 = k ∧ t05 = k ∧ t12 = k ∧ t13 = k ∧ t14 = k ∧ t15 = k ∧
        t23 = k ∧ t24 = k ∧ t25 = k ∧ t34 = k ∧ t35 = k ∧ t45 = k := by omega
    subst h1' h2' h4 h5 h12 h13 h14 h15 h23 h24 h25 h34 h35 h45 e03
    rw [Int.modEq_iff_add_fac] at c01 c03
    obtain ⟨r1, c01⟩ := c01; obtain ⟨r3, c03⟩ := c03
    push_cast at c01 c03
    exact clash (5 * (k:ℤ)) (5 * (k:ℤ) + 1) r3 r1 (by ring) (by linarith [c03]) (by linarith [c01])
  by_cases e04 : t04 = k + 1
  · obtain ⟨h1', h2', h3', h5, h12, h13, h14, h15, h23, h24, h25, h34, h35, h45⟩ :
        t01 = k ∧ t02 = k ∧ t03 = k ∧ t05 = k ∧ t12 = k ∧ t13 = k ∧ t14 = k ∧ t15 = k ∧
        t23 = k ∧ t24 = k ∧ t25 = k ∧ t34 = k ∧ t35 = k ∧ t45 = k := by omega
    subst h1' h2' h3' h5 h12 h13 h14 h15 h23 h24 h25 h34 h35 h45 e04
    rw [Int.modEq_iff_add_fac] at c01 c04
    obtain ⟨r1, c01⟩ := c01; obtain ⟨r4, c04⟩ := c04
    push_cast at c01 c04
    exact clash (5 * (k:ℤ)) (5 * (k:ℤ) + 1) r4 r1 (by ring) (by linarith [c04]) (by linarith [c01])
  by_cases e05 : t05 = k + 1
  · obtain ⟨h1', h2', h3', h4', h12, h13, h14, h15, h23, h24, h25, h34, h35, h45⟩ :
        t01 = k ∧ t02 = k ∧ t03 = k ∧ t04 = k ∧ t12 = k ∧ t13 = k ∧ t14 = k ∧ t15 = k ∧
        t23 = k ∧ t24 = k ∧ t25 = k ∧ t34 = k ∧ t35 = k ∧ t45 = k := by omega
    subst h1' h2' h3' h4' h12 h13 h14 h15 h23 h24 h25 h34 h35 h45 e05
    rw [Int.modEq_iff_add_fac] at c01 c12
    obtain ⟨r1, c01⟩ := c01; obtain ⟨r5, c12⟩ := c12
    push_cast at c01 c12
    exact clash (5 * (k:ℤ) + 1) (5 * (k:ℤ) + 2) r1 r5 (by ring) (by linarith [c01]) (by linarith [c12])
  by_cases e12 : t12 = k + 1
  · obtain ⟨h1', h2', h3', h4', h5', h13, h14, h15, h23, h24, h25, h34, h35, h45⟩ :
        t01 = k ∧ t02 = k ∧ t03 = k ∧ t04 = k ∧ t05 = k ∧ t13 = k ∧ t14 = k ∧ t15 = k ∧
        t23 = k ∧ t24 = k ∧ t25 = k ∧ t34 = k ∧ t35 = k ∧ t45 = k := by omega
    subst h1' h2' h3' h4' h5' h13 h14 h15 h23 h24 h25 h34 h35 h45 e12
    rw [Int.modEq_iff_add_fac] at c01 c12
    obtain ⟨r1, c01⟩ := c01; obtain ⟨r5, c12⟩ := c12
    push_cast at c01 c12
    exact clash (5 * (k:ℤ)) (5 * (k:ℤ) + 1) r5 r1 (by ring) (by linarith [c12]) (by linarith [c01])
  by_cases e13 : t13 = k + 1
  · obtain ⟨h1', h2', h3', h4', h5', h12', h14, h15, h23, h24, h25, h34, h35, h45⟩ :
        t01 = k ∧ t02 = k ∧ t03 = k ∧ t04 = k ∧ t05 = k ∧ t12 = k ∧ t14 = k ∧ t15 = k ∧
        t23 = k ∧ t24 = k ∧ t25 = k ∧ t34 = k ∧ t35 = k ∧ t45 = k := by omega
    subst h1' h2' h3' h4' h5' h12' h14 h15 h23 h24 h25 h34 h35 h45 e13
    rw [Int.modEq_iff_add_fac] at c01 c13
    obtain ⟨r1, c01⟩ := c01; obtain ⟨r6, c13⟩ := c13
    push_cast at c01 c13
    exact clash (5 * (k:ℤ)) (5 * (k:ℤ) + 1) r6 r1 (by ring) (by linarith [c13]) (by linarith [c01])
  by_cases e14 : t14 = k + 1
  · obtain ⟨h1', h2', h3', h4', h5', h12', h13', h15, h23, h24, h25, h34, h35, h45⟩ :
        t01 = k ∧ t02 = k ∧ t03 = k ∧ t04 = k ∧ t05 = k ∧ t12 = k ∧ t13 = k ∧ t15 = k ∧
        t23 = k ∧ t24 = k ∧ t25 = k ∧ t34 = k ∧ t35 = k ∧ t45 = k := by omega
    subst h1' h2' h3' h4' h5' h12' h13' h15 h23 h24 h25 h34 h35 h45 e14
    rw [Int.modEq_iff_add_fac] at c01 c14
    obtain ⟨r1, c01⟩ := c01; obtain ⟨r7, c14⟩ := c14
    push_cast at c01 c14
    exact clash (5 * (k:ℤ)) (5 * (k:ℤ) + 1) r7 r1 (by ring) (by linarith [c14]) (by linarith [c01])
  by_cases e15 : t15 = k + 1
  · obtain ⟨h1', h2', h3', h4', h5', h12', h13', h14', h23, h24, h25, h34, h35, h45⟩ :
        t01 = k ∧ t02 = k ∧ t03 = k ∧ t04 = k ∧ t05 = k ∧ t12 = k ∧ t13 = k ∧ t14 = k ∧
        t23 = k ∧ t24 = k ∧ t25 = k ∧ t34 = k ∧ t35 = k ∧ t45 = k := by omega
    subst h1' h2' h3' h4' h5' h12' h13' h14' h23 h24 h25 h34 h35 h45 e15
    rw [Int.modEq_iff_add_fac] at c01 c23
    obtain ⟨r1, c01⟩ := c01; obtain ⟨r8, c23⟩ := c23
    push_cast at c01 c23
    exact clash (5 * (k:ℤ) + 1) (5 * (k:ℤ) + 2) r1 r8 (by ring) (by linarith [c01]) (by linarith [c23])
  by_cases e23 : t23 = k + 1
  · obtain ⟨h1', h2', h3', h4', h5', h12', h13', h14', h15', h24, h25, h34, h35, h45⟩ :
        t01 = k ∧ t02 = k ∧ t03 = k ∧ t04 = k ∧ t05 = k ∧ t12 = k ∧ t13 = k ∧ t14 = k ∧
        t15 = k ∧ t24 = k ∧ t25 = k ∧ t34 = k ∧ t35 = k ∧ t45 = k := by omega
    subst h1' h2' h3' h4' h5' h12' h13' h14' h15' h24 h25 h34 h35 h45 e23
    rw [Int.modEq_iff_add_fac] at c02 c23
    obtain ⟨r2, c02⟩ := c02; obtain ⟨r8, c23⟩ := c23
    push_cast at c02 c23
    exact clash (5 * (k:ℤ)) (5 * (k:ℤ) + 1) r8 r2 (by ring) (by linarith [c23]) (by linarith [c02])
  by_cases e24 : t24 = k + 1
  · obtain ⟨h1', h2', h3', h4', h5', h12', h13', h14', h15', h23', h25, h34, h35, h45⟩ :
        t01 = k ∧ t02 = k ∧ t03 = k ∧ t04 = k ∧ t05 = k ∧ t12 = k ∧ t13 = k ∧ t14 = k ∧
        t15 = k ∧ t23 = k ∧ t25 = k ∧ t34 = k ∧ t35 = k ∧ t45 = k := by omega
    subst h1' h2' h3' h4' h5' h12' h13' h14' h15' h23' h25 h34 h35 h45 e24
    rw [Int.modEq_iff_add_fac] at c02 c24
    obtain ⟨r2, c02⟩ := c02; obtain ⟨r9, c24⟩ := c24
    push_cast at c02 c24
    exact clash (5 * (k:ℤ)) (5 * (k:ℤ) + 1) r9 r2 (by ring) (by linarith [c24]) (by linarith [c02])
  by_cases e25 : t25 = k + 1
  · obtain ⟨h1', h2', h3', h4', h5', h12', h13', h14', h15', h23', h24', h34, h35, h45⟩ :
        t01 = k ∧ t02 = k ∧ t03 = k ∧ t04 = k ∧ t05 = k ∧ t12 = k ∧ t13 = k ∧ t14 = k ∧
        t15 = k ∧ t23 = k ∧ t24 = k ∧ t34 = k ∧ t35 = k ∧ t45 = k := by omega
    subst h1' h2' h3' h4' h5' h12' h13' h14' h15' h23' h24' h34 h35 h45 e25
    rw [Int.modEq_iff_add_fac] at c12 c34
    obtain ⟨r5, c12⟩ := c12; obtain ⟨r10, c34⟩ := c34
    push_cast at c12 c34
    exact clash (5 * (k:ℤ) + 1) (5 * (k:ℤ) + 2) r5 r10 (by ring) (by linarith [c12]) (by linarith [c34])
  by_cases e34 : t34 = k + 1
  · obtain ⟨h1', h2', h3', h4', h5', h12', h13', h14', h15', h23', h24', h25', h35, h45⟩ :
        t01 = k ∧ t02 = k ∧ t03 = k ∧ t04 = k ∧ t05 = k ∧ t12 = k ∧ t13 = k ∧ t14 = k ∧
        t15 = k ∧ t23 = k ∧ t24 = k ∧ t25 = k ∧ t35 = k ∧ t45 = k := by omega
    subst h1' h2' h3' h4' h5' h12' h13' h14' h15' h23' h24' h25' h35 h45 e34
    rw [Int.modEq_iff_add_fac] at c03 c34
    obtain ⟨r3, c03⟩ := c03; obtain ⟨r10, c34⟩ := c34
    push_cast at c03 c34
    exact clash (5 * (k:ℤ)) (5 * (k:ℤ) + 1) r10 r3 (by ring) (by linarith [c34]) (by linarith [c03])
  by_cases e35 : t35 = k + 1
  · obtain ⟨h1', h2', h3', h4', h5', h12', h13', h14', h15', h23', h24', h25', h34', h45⟩ :
        t01 = k ∧ t02 = k ∧ t03 = k ∧ t04 = k ∧ t05 = k ∧ t12 = k ∧ t13 = k ∧ t14 = k ∧
        t15 = k ∧ t23 = k ∧ t24 = k ∧ t25 = k ∧ t34 = k ∧ t45 = k := by omega
    subst h1' h2' h3' h4' h5' h12' h13' h14' h15' h23' h24' h25' h34' h45 e35
    rw [Int.modEq_iff_add_fac] at c12 c13
    obtain ⟨r5, c12⟩ := c12; obtain ⟨r6, c13⟩ := c13
    push_cast at c12 c13
    exact clash (5 * (k:ℤ) + 1) (5 * (k:ℤ) + 2) r6 r5 (by ring) (by linarith [c13]) (by linarith [c12])
  by_cases e45 : t45 = k + 1
  · obtain ⟨h1', h2', h3', h4', h5', h12', h13', h14', h15', h23', h24', h25', h34', h35'⟩ :
        t01 = k ∧ t02 = k ∧ t03 = k ∧ t04 = k ∧ t05 = k ∧ t12 = k ∧ t13 = k ∧ t14 = k ∧
        t15 = k ∧ t23 = k ∧ t24 = k ∧ t25 = k ∧ t34 = k ∧ t35 = k := by omega
    subst h1' h2' h3' h4' h5' h12' h13' h14' h15' h23' h24' h25' h34' h35' e45
    rw [Int.modEq_iff_add_fac] at c12 c14
    obtain ⟨r5, c12⟩ := c12; obtain ⟨r7, c14⟩ := c14
    push_cast at c12 c14
    exact clash (5 * (k:ℤ) + 1) (5 * (k:ℤ) + 2) r7 r5 (by ring) (by linarith [c14]) (by linarith [c12])
  clear c01 c02 c03 c04 c12 c13 c14 c23 c24 c34
  omega

set_option maxRecDepth 4096 in
/-- For every 2-subset `P` of the five problems `{0, 1, 2, 3, 4}` and every 4-subset `st` of
all six problems, the per-contestant contribution to the mod-3 congruences (the indicator of
solving `P`, minus the indicators of solving `{u, 5}` for `u` in the complementary triple,
minus the indicators of solving the pairs inside the triple) is divisible by `3`. This finite
check is the content of Evan Chen's second claim. -/
theorem cong_aux : ∀ (P st : Finset (Fin 6)), P ⊆ Finset.univ.erase 5 → P.card = 2 →
    st.card = 4 →
    ((if P ⊆ st then (1 : ℤ) else 0)
      - ∑ u ∈ Finset.univ.erase 5 \ P, (if ({u, 5} : Finset (Fin 6)) ⊆ st then (1 : ℤ) else 0)
      - ∑ Q ∈ (Finset.univ.erase 5 \ P).powersetCard 2,
          (if Q ⊆ st then (1 : ℤ) else 0)) ≡ 0 [ZMOD 3] := by
  decide

/-- The fifteen 2-subsets of `Fin 6`, as a literal finset. -/
theorem pc2_univ : (Finset.univ : Finset (Fin 6)).powersetCard 2 =
    {{0, 1}, {0, 2}, {0, 3}, {0, 4}, {0, 5}, {1, 2}, {1, 3}, {1, 4}, {1, 5}, {2, 3}, {2, 4},
      {2, 5}, {3, 4}, {3, 5}, {4, 5}} := by
  decide

/-- Any set of at most `k ≤ 6` problems can be extended to a set of exactly `k` problems. -/
theorem exists_superset_card {s : Finset (Fin 6)} {k : ℕ} (h1 : s.card ≤ k) (h2 : k ≤ 6) :
    ∃ t : Finset (Fin 6), s ⊆ t ∧ t.card = k := by
  obtain ⟨u, hus, huc⟩ := Finset.exists_subset_card_eq (s := sᶜ) (n := k - s.card) (by
    rw [Finset.card_compl, Fintype.card_fin]
    omega)
  refine ⟨s ∪ u, Finset.subset_union_left, ?_⟩
  rw [Finset.card_union_of_disjoint ?_, huc]
  · omega
  · rw [Finset.disjoint_left]
    intro x hxs hxu
    exact Finset.mem_compl.mp (hus hxu) hxs

/-- The number of contestants who solved both problems of the pair `P`. -/
def pairCount {n : ℕ} (s : Fin n → Finset (Fin 6)) (P : Finset (Fin 6)) : ℕ :=
  (Finset.univ.filter fun i => P ⊆ s i).card

theorem pairCount_two {n : ℕ} (s : Fin n → Finset (Fin 6)) (p q : Fin 6) :
    pairCount s {p, q} = (Finset.univ.filter fun i => p ∈ s i ∧ q ∈ s i).card := by
  unfold pairCount
  congr 1
  ext x
  simp [Finset.insert_subset_iff, Finset.singleton_subset_iff]

/-- Double counting: the sum of the pair counts over all fifteen pairs equals the sum over
contestants of the number of pairs of problems they solved. -/
theorem sum_pairCount {n : ℕ} (s : Fin n → Finset (Fin 6)) :
    ∑ P ∈ (Finset.univ : Finset (Fin 6)).powersetCard 2, pairCount s P
      = ∑ i, ((s i).powersetCard 2).card := by
  have e : ∀ i : Fin n, ((Finset.univ : Finset (Fin 6)).powersetCard 2).bipartiteBelow
        (fun P i => P ⊆ s i) i = (s i).powersetCard 2 := by
    intro i
    ext P
    simp only [Finset.mem_bipartiteBelow, Finset.mem_powersetCard]
    constructor
    · rintro ⟨⟨-, hP2⟩, hP3⟩
      exact ⟨hP3, hP2⟩
    · rintro ⟨hP1, hP2⟩
      exact ⟨⟨Finset.subset_univ P, hP2⟩, hP1⟩
  calc ∑ P ∈ (Finset.univ : Finset (Fin 6)).powersetCard 2, pairCount s P
      = ∑ P ∈ (Finset.univ : Finset (Fin 6)).powersetCard 2,
          (Finset.univ.bipartiteAbove (fun P i => P ⊆ s i) P).card :=
        Finset.sum_congr rfl fun P _ => rfl
    _ = ∑ i ∈ Finset.univ, (((Finset.univ : Finset (Fin 6)).powersetCard 2).bipartiteBelow
          (fun P i => P ⊆ s i) i).card :=
        Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (fun P i => P ⊆ s i)
    _ = ∑ i, ((s i).powersetCard 2).card :=
        Finset.sum_congr rfl fun i _ => by rw [e i]

/-- The congruences: for every pair `P ⊆ {0, 1, 2, 3, 4}` of problems, writing `T` for the
complementary triple, the number of contestants solving `P` is congruent modulo `3` to
`1 + ∑_{u ∈ T} (contestants solving {u, 5}) + ∑_{Q ∈ T choose 2} (contestants solving Q)`.
This holds per contestant: the distinguished contestant `c0` (who solved exactly
`{0, 1, 2, 3, 4}`) contributes `-2 ≡ 1`, and every other contestant, who solved exactly
four problems, contributes a multiple of `3` (see `cong_aux`). -/
theorem pairCount_modEq {n : ℕ} {s : Fin n → Finset (Fin 6)} {c0 : Fin n}
    (hc0 : s c0 = Finset.univ.erase 5) (h4 : ∀ i : Fin n, i ≠ c0 → (s i).card = 4)
    {P : Finset (Fin 6)} (hP : P ∈ (Finset.univ.erase 5 : Finset (Fin 6)).powersetCard 2) :
    (pairCount s P : ℤ)
      ≡ 1 + ∑ u ∈ Finset.univ.erase 5 \ P, (pairCount s {u, 5} : ℤ)
        + ∑ Q ∈ (Finset.univ.erase 5 \ P).powersetCard 2, (pairCount s Q : ℤ) [ZMOD 3] := by
  obtain ⟨hPsub, hPcard⟩ := Finset.mem_powersetCard.mp hP
  set D : Finset (Fin 6) := Finset.univ.erase 5 \ P with hD
  set E : Finset (Finset (Fin 6)) := D.powersetCard 2 with hE
  have ec : ∀ Q : Finset (Fin 6), (pairCount s Q : ℤ)
      = ∑ i, (if Q ⊆ s i then (1 : ℤ) else 0) :=
    fun Q => Finset.natCast_card_filter (fun i => Q ⊆ s i) Finset.univ
  have e2 : ∑ u ∈ D, (pairCount s {u, 5} : ℤ)
      = ∑ i, ∑ u ∈ D, (if ({u, 5} : Finset (Fin 6)) ⊆ s i then (1 : ℤ) else 0) := by
    rw [Finset.sum_congr rfl (fun u _ => ec {u, 5}), Finset.sum_comm]
  have e3 : ∑ Q ∈ E, (pairCount s Q : ℤ)
      = ∑ i, ∑ Q ∈ E, (if Q ⊆ s i then (1 : ℤ) else 0) := by
    rw [Finset.sum_congr rfl (fun Q _ => ec Q), Finset.sum_comm]
  -- The contribution of every contestant other than `c0` is divisible by `3`.
  have hsum0 : ∑ i ∈ Finset.univ.erase c0,
      ((if P ⊆ s i then (1 : ℤ) else 0)
        - ∑ u ∈ D, (if ({u, 5} : Finset (Fin 6)) ⊆ s i then (1 : ℤ) else 0)
        - ∑ Q ∈ E, (if Q ⊆ s i then (1 : ℤ) else 0)) ≡ 0 [ZMOD 3] := by
    apply Int.modEq_zero_iff_dvd.mpr
    apply dvd_sum
    intro i hi
    apply Int.modEq_zero_iff_dvd.mp
    rw [Finset.mem_erase] at hi
    exact cong_aux P (s i) hPsub hPcard (h4 i hi.1)
  -- The contribution of `c0` is `-2 ≡ 1`.
  have hDcard : D.card = 3 := by
    rw [hD, Finset.card_sdiff, Finset.inter_eq_left.mpr hPsub,
      Finset.card_erase_of_mem (Finset.mem_univ 5), Finset.card_univ, Fintype.card_fin, hPcard]
  have hEcard : E.card = 3 := by
    rw [hE, Finset.card_powersetCard, hDcard]
    decide
  have hu0 : ∑ u ∈ D, (if ({u, 5} : Finset (Fin 6)) ⊆ s c0 then (1 : ℤ) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro u _
    apply if_neg
    intro hsub
    have h5 : (5 : Fin 6) ∈ s c0 :=
      hsub (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self 5)))
    rw [hc0] at h5
    exact (Finset.mem_erase.mp h5).1 rfl
  have hQ1 : ∑ Q ∈ E, (if Q ⊆ s c0 then (1 : ℤ) else 0) = 3 := by
    have hQ : ∀ Q ∈ E, (if Q ⊆ s c0 then (1 : ℤ) else 0) = 1 := by
      intro Q hQm
      apply if_pos
      rw [hc0]
      exact (Finset.mem_powersetCard.mp hQm).1.trans Finset.sdiff_subset
    rw [Finset.sum_congr rfl hQ, Finset.sum_const, hEcard]
    norm_num
  have hc0' : (if P ⊆ s c0 then (1 : ℤ) else 0)
      - ∑ u ∈ D, (if ({u, 5} : Finset (Fin 6)) ⊆ s c0 then (1 : ℤ) else 0)
      - ∑ Q ∈ E, (if Q ⊆ s c0 then (1 : ℤ) else 0) = -2 := by
    rw [if_pos (by rw [hc0]; exact hPsub), hu0, hQ1]
    norm_num
  have key : (pairCount s P : ℤ)
      - ∑ u ∈ D, (pairCount s {u, 5} : ℤ) - ∑ Q ∈ E, (pairCount s Q : ℤ) ≡ 1 [ZMOD 3] := by
    rw [ec P, e2, e3, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
      ← Finset.add_sum_erase _ _ (Finset.mem_univ c0), hc0']
    have h21 : (-2 : ℤ) ≡ 1 [ZMOD 3] := by decide
    simpa using h21.add hsum0
  obtain ⟨t, ht⟩ := Int.modEq_iff_add_fac.mp key
  exact Int.modEq_iff_add_fac.mpr ⟨t, by linarith⟩

snip end

problem imo2005_p6 {n : ℕ} (s : Fin n → Finset (Fin 6))
    (pair : ∀ p q : Fin 6, p ≠ q →
      2 * n < 5 * (Finset.univ.filter fun i => p ∈ s i ∧ q ∈ s i).card)
    (hall : ∀ i, (s i).card < 6) :
    ∃ i j, i ≠ j ∧ (s i).card = 5 ∧ (s j).card = 5 := by
  classical
  by_contra hcon
  push Not at hcon
  -- There is at least one contestant.
  have hn : 0 < n := by
    by_contra hz
    have hz0 : n = 0 := by omega
    subst hz0
    have h := pair 0 1 (by decide)
    rw [Finset.univ_eq_empty, Finset.filter_empty, Finset.card_empty, mul_zero] at h
    exact Nat.lt_irrefl 0 h
  -- At most one contestant solved exactly five problems.
  have hF : (Finset.univ.filter fun i => (s i).card = 5).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    by_contra hab
    exact hcon a b hab (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2
  -- Normalization: we may add solved problems to contestants, which only makes the pair
  -- condition stronger. So we may assume some contestant `c0` solved exactly five problems
  -- and every other contestant solved exactly four.
  obtain ⟨c0, s', hsub, hc0, hrest⟩ : ∃ c0, ∃ s' : Fin n → Finset (Fin 6),
      (∀ i, s i ⊆ s' i) ∧ (s' c0).card = 5 ∧ ∀ i, i ≠ c0 → (s' i).card = 4 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hF with hF0 | hF1
    · -- Nobody solved five problems: promote contestant `⟨0, hn⟩` to five.
      have hFempty : Finset.univ.filter (fun i => (s i).card = 5) = ∅ := Finset.card_eq_zero.mp hF0
      have hle : ∀ i, (s i).card ≤ 4 := by
        intro i
        by_contra h'
        push Not at h'
        have h5 : (s i).card = 5 := by have h6 := hall i; omega
        have hmem : i ∈ Finset.univ.filter (fun i => (s i).card = 5) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ i, h5⟩
        rw [hFempty] at hmem
        exact Finset.notMem_empty i hmem
      have ext : ∀ i, ∃ t : Finset (Fin 6), s i ⊆ t ∧ t.card = if i = ⟨0, hn⟩ then 5 else 4 := by
        intro i
        by_cases hci : i = ⟨0, hn⟩
        · subst hci
          rw [if_pos rfl]
          exact exists_superset_card (by have h := hle ⟨0, hn⟩; omega) (by norm_num)
        · rw [if_neg hci]
          exact exists_superset_card (hle i) (by norm_num)
      choose s' hsub hcard using ext
      exact ⟨⟨0, hn⟩, s', hsub, by rw [hcard ⟨0, hn⟩, if_pos rfl],
        fun i hi => by rw [hcard i, if_neg hi]⟩
    · -- Somebody solved five problems: everyone else gets promoted to four.
      obtain ⟨c0, hFc0⟩ := Finset.card_eq_one.mp hF1
      have hc0card : (s c0).card = 5 := by
        have hmem : c0 ∈ Finset.univ.filter (fun i => (s i).card = 5) := by
          rw [hFc0]
          exact Finset.mem_singleton_self c0
        exact (Finset.mem_filter.mp hmem).2
      have hle : ∀ i, i ≠ c0 → (s i).card ≤ 4 := by
        intro i hi
        by_contra h'
        push Not at h'
        have h5 : (s i).card = 5 := by have h6 := hall i; omega
        have hmem : i ∈ Finset.univ.filter (fun i => (s i).card = 5) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ i, h5⟩
        rw [hFc0, Finset.mem_singleton] at hmem
        exact hi hmem
      have ext : ∀ i, ∃ t : Finset (Fin 6), s i ⊆ t ∧ t.card = if i = c0 then 5 else 4 := by
        intro i
        by_cases hci : i = c0
        · subst i
          exact ⟨s c0, Finset.Subset.refl _, by rw [if_pos rfl]; exact hc0card⟩
        · rw [if_neg hci]
          exact exists_superset_card (hle i hci) (by norm_num)
      choose s' hsub hcard using ext
      exact ⟨c0, s', hsub, by rw [hcard c0, if_pos rfl], fun i hi => by rw [hcard i, if_neg hi]⟩
  -- The pair condition is preserved (and only strengthened) by the promotion.
  have pair' : ∀ p q : Fin 6, p ≠ q →
      2 * n < 5 * (Finset.univ.filter fun i => p ∈ s' i ∧ q ∈ s' i).card := by
    intro p q hpq
    have hle : (Finset.univ.filter fun i => p ∈ s i ∧ q ∈ s i).card
        ≤ (Finset.univ.filter fun i => p ∈ s' i ∧ q ∈ s' i).card := by
      apply Finset.card_le_card
      intro x hx
      rw [Finset.mem_filter] at hx ⊢
      exact ⟨hx.1, hsub x hx.2.1, hsub x hx.2.2⟩
    exact lt_of_lt_of_le (pair p q hpq) (Nat.mul_le_mul_left 5 hle)
  -- Relabel the problems so that `c0` missed problem `5`.
  obtain ⟨m, hm⟩ : ∃ m : Fin 6, Finset.univ \ s' c0 = {m} := by
    have hcard1 : (Finset.univ \ s' c0).card = 1 := by
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, hc0]
    exact Finset.card_eq_one.mp hcard1
  set σ : Fin 6 ≃ Fin 6 := Equiv.swap m 5 with hσ
  set s'' : Fin n → Finset (Fin 6) := fun i => (s' i).map σ.toEmbedding with hs''
  have mem_s'' : ∀ (x : Fin 6) (i : Fin n), x ∈ s'' i ↔ σ x ∈ s' i := by
    intro x i
    simp only [hs'']
    rw [Finset.mem_map_equiv, hσ, Equiv.symm_swap]
  have hs''c0 : s'' c0 = Finset.univ.erase 5 := by
    ext x
    rw [mem_s'' x c0, Finset.mem_erase]
    constructor
    · intro h
      refine ⟨fun hx5 => ?_, Finset.mem_univ x⟩
      subst hx5
      have hmin : m ∈ s' c0 := by
        have h5 : σ 5 ∈ s' c0 := h
        rwa [hσ, Equiv.swap_apply_right] at h5
      have hmout : m ∉ s' c0 := by
        have hmem : m ∈ Finset.univ \ s' c0 := by
          rw [hm]
          exact Finset.mem_singleton_self m
        exact (Finset.mem_sdiff.mp hmem).2
      exact hmout hmin
    · intro h
      by_contra hmem
      have h1 : σ x ∈ Finset.univ \ s' c0 := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hmem⟩
      rw [hm, Finset.mem_singleton] at h1
      have hx5 : x = 5 := by
        have h2 : σ (σ x) = σ m := congrArg σ h1
        rw [hσ, Equiv.swap_apply_self, Equiv.swap_apply_left] at h2
        exact h2
      exact h.1 hx5
  have hs''c0card : (s'' c0).card = 5 := by
    simp only [hs'']
    rw [Finset.card_map]
    exact hc0
  have hs''4 : ∀ i : Fin n, i ≠ c0 → (s'' i).card = 4 := by
    intro i hi
    simp only [hs'']
    rw [Finset.card_map]
    exact hrest i hi
  have pair'' : ∀ p q : Fin 6, p ≠ q →
      2 * n < 5 * (Finset.univ.filter fun i => p ∈ s'' i ∧ q ∈ s'' i).card := by
    intro p q hpq
    have heq : (Finset.univ.filter fun i => p ∈ s'' i ∧ q ∈ s'' i)
        = Finset.univ.filter fun i => σ p ∈ s' i ∧ σ q ∈ s' i :=
      Finset.filter_congr fun x _ => by rw [mem_s'' p x, mem_s'' q x]
    rw [heq]
    exact pair' (σ p) (σ q) (fun h => hpq (σ.injective h))
  -- Counting: the sum of all fifteen pair counts is `6 * n + 4`.
  have hsum1 : ∑ P ∈ (Finset.univ : Finset (Fin 6)).powersetCard 2, pairCount s'' P
      = 6 * n + 4 := by
    rw [sum_pairCount]
    rw [Finset.sum_congr rfl (fun i _ => Finset.card_powersetCard 2 (s'' i))]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ c0)]
    have hc : ∀ x ∈ Finset.univ.erase c0, (s'' x).card.choose 2 = 6 := by
      intro x hx
      rw [hs''4 x (Finset.mem_erase.mp hx).1]
      decide
    have e : ∑ x ∈ Finset.univ.erase c0, (s'' x).card.choose 2 = 6 * (n - 1) := by
      rw [Finset.sum_congr rfl hc, Finset.sum_const,
        Finset.card_erase_of_mem (Finset.mem_univ c0), Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      norm_num
      ring
    have h5c : (5).choose 2 = 10 := by decide
    rw [hs''c0card, e, h5c]
    omega
  have hsum2 : pairCount s'' {0, 1} + pairCount s'' {0, 2} + pairCount s'' {0, 3}
      + pairCount s'' {0, 4} + pairCount s'' {0, 5} + pairCount s'' {1, 2}
      + pairCount s'' {1, 3} + pairCount s'' {1, 4} + pairCount s'' {1, 5}
      + pairCount s'' {2, 3} + pairCount s'' {2, 4} + pairCount s'' {2, 5}
      + pairCount s'' {3, 4} + pairCount s'' {3, 5} + pairCount s'' {4, 5} = 6 * n + 4 := by
    rw [pc2_univ] at hsum1
    repeat rw [Finset.sum_insert (by decide)] at hsum1
    rw [Finset.sum_singleton] at hsum1
    omega
  -- Each pair count is at least `(2 * n + 1) / 5`.
  have hb : ∀ p q : Fin 6, p ≠ q → 2 * n + 1 ≤ 5 * pairCount s'' {p, q} := by
    intro p q hpq
    rw [pairCount_two]
    exact pair'' p q hpq
  -- The ten congruences, specialized to concrete pairs.
  have c01 : (pairCount s'' {0, 1} : ℤ)
      ≡ 1 + pairCount s'' {2, 5} + pairCount s'' {3, 5} + pairCount s'' {4, 5}
        + pairCount s'' {2, 3} + pairCount s'' {2, 4} + pairCount s'' {3, 4} [ZMOD 3] := by
    have h := pairCount_modEq hs''c0 hs''4 (P := {0, 1}) (by decide)
    rw [show (Finset.univ.erase 5 \ {0, 1} : Finset (Fin 6)) = {2, 3, 4} from by decide] at h
    rw [show ({2, 3, 4} : Finset (Fin 6)).powersetCard 2 = {{2, 3}, {2, 4}, {3, 4}}
      from by decide] at h
    repeat rw [Finset.sum_insert (by decide)] at h
    repeat rw [Finset.sum_singleton] at h
    obtain ⟨r, hr⟩ := Int.modEq_iff_add_fac.mp h
    exact Int.modEq_iff_add_fac.mpr ⟨r, by linarith⟩
  have c02 : (pairCount s'' {0, 2} : ℤ)
      ≡ 1 + pairCount s'' {1, 5} + pairCount s'' {3, 5} + pairCount s'' {4, 5}
        + pairCount s'' {1, 3} + pairCount s'' {1, 4} + pairCount s'' {3, 4} [ZMOD 3] := by
    have h := pairCount_modEq hs''c0 hs''4 (P := {0, 2}) (by decide)
    rw [show (Finset.univ.erase 5 \ {0, 2} : Finset (Fin 6)) = {1, 3, 4} from by decide] at h
    rw [show ({1, 3, 4} : Finset (Fin 6)).powersetCard 2 = {{1, 3}, {1, 4}, {3, 4}}
      from by decide] at h
    repeat rw [Finset.sum_insert (by decide)] at h
    repeat rw [Finset.sum_singleton] at h
    obtain ⟨r, hr⟩ := Int.modEq_iff_add_fac.mp h
    exact Int.modEq_iff_add_fac.mpr ⟨r, by linarith⟩
  have c03 : (pairCount s'' {0, 3} : ℤ)
      ≡ 1 + pairCount s'' {1, 5} + pairCount s'' {2, 5} + pairCount s'' {4, 5}
        + pairCount s'' {1, 2} + pairCount s'' {1, 4} + pairCount s'' {2, 4} [ZMOD 3] := by
    have h := pairCount_modEq hs''c0 hs''4 (P := {0, 3}) (by decide)
    rw [show (Finset.univ.erase 5 \ {0, 3} : Finset (Fin 6)) = {1, 2, 4} from by decide] at h
    rw [show ({1, 2, 4} : Finset (Fin 6)).powersetCard 2 = {{1, 2}, {1, 4}, {2, 4}}
      from by decide] at h
    repeat rw [Finset.sum_insert (by decide)] at h
    repeat rw [Finset.sum_singleton] at h
    obtain ⟨r, hr⟩ := Int.modEq_iff_add_fac.mp h
    exact Int.modEq_iff_add_fac.mpr ⟨r, by linarith⟩
  have c04 : (pairCount s'' {0, 4} : ℤ)
      ≡ 1 + pairCount s'' {1, 5} + pairCount s'' {2, 5} + pairCount s'' {3, 5}
        + pairCount s'' {1, 2} + pairCount s'' {1, 3} + pairCount s'' {2, 3} [ZMOD 3] := by
    have h := pairCount_modEq hs''c0 hs''4 (P := {0, 4}) (by decide)
    rw [show (Finset.univ.erase 5 \ {0, 4} : Finset (Fin 6)) = {1, 2, 3} from by decide] at h
    rw [show ({1, 2, 3} : Finset (Fin 6)).powersetCard 2 = {{1, 2}, {1, 3}, {2, 3}}
      from by decide] at h
    repeat rw [Finset.sum_insert (by decide)] at h
    repeat rw [Finset.sum_singleton] at h
    obtain ⟨r, hr⟩ := Int.modEq_iff_add_fac.mp h
    exact Int.modEq_iff_add_fac.mpr ⟨r, by linarith⟩
  have c12 : (pairCount s'' {1, 2} : ℤ)
      ≡ 1 + pairCount s'' {0, 5} + pairCount s'' {3, 5} + pairCount s'' {4, 5}
        + pairCount s'' {0, 3} + pairCount s'' {0, 4} + pairCount s'' {3, 4} [ZMOD 3] := by
    have h := pairCount_modEq hs''c0 hs''4 (P := {1, 2}) (by decide)
    rw [show (Finset.univ.erase 5 \ {1, 2} : Finset (Fin 6)) = {0, 3, 4} from by decide] at h
    rw [show ({0, 3, 4} : Finset (Fin 6)).powersetCard 2 = {{0, 3}, {0, 4}, {3, 4}}
      from by decide] at h
    repeat rw [Finset.sum_insert (by decide)] at h
    repeat rw [Finset.sum_singleton] at h
    obtain ⟨r, hr⟩ := Int.modEq_iff_add_fac.mp h
    exact Int.modEq_iff_add_fac.mpr ⟨r, by linarith⟩
  have c13 : (pairCount s'' {1, 3} : ℤ)
      ≡ 1 + pairCount s'' {0, 5} + pairCount s'' {2, 5} + pairCount s'' {4, 5}
        + pairCount s'' {0, 2} + pairCount s'' {0, 4} + pairCount s'' {2, 4} [ZMOD 3] := by
    have h := pairCount_modEq hs''c0 hs''4 (P := {1, 3}) (by decide)
    rw [show (Finset.univ.erase 5 \ {1, 3} : Finset (Fin 6)) = {0, 2, 4} from by decide] at h
    rw [show ({0, 2, 4} : Finset (Fin 6)).powersetCard 2 = {{0, 2}, {0, 4}, {2, 4}}
      from by decide] at h
    repeat rw [Finset.sum_insert (by decide)] at h
    repeat rw [Finset.sum_singleton] at h
    obtain ⟨r, hr⟩ := Int.modEq_iff_add_fac.mp h
    exact Int.modEq_iff_add_fac.mpr ⟨r, by linarith⟩
  have c14 : (pairCount s'' {1, 4} : ℤ)
      ≡ 1 + pairCount s'' {0, 5} + pairCount s'' {2, 5} + pairCount s'' {3, 5}
        + pairCount s'' {0, 2} + pairCount s'' {0, 3} + pairCount s'' {2, 3} [ZMOD 3] := by
    have h := pairCount_modEq hs''c0 hs''4 (P := {1, 4}) (by decide)
    rw [show (Finset.univ.erase 5 \ {1, 4} : Finset (Fin 6)) = {0, 2, 3} from by decide] at h
    rw [show ({0, 2, 3} : Finset (Fin 6)).powersetCard 2 = {{0, 2}, {0, 3}, {2, 3}}
      from by decide] at h
    repeat rw [Finset.sum_insert (by decide)] at h
    repeat rw [Finset.sum_singleton] at h
    obtain ⟨r, hr⟩ := Int.modEq_iff_add_fac.mp h
    exact Int.modEq_iff_add_fac.mpr ⟨r, by linarith⟩
  have c23 : (pairCount s'' {2, 3} : ℤ)
      ≡ 1 + pairCount s'' {0, 5} + pairCount s'' {1, 5} + pairCount s'' {4, 5}
        + pairCount s'' {0, 1} + pairCount s'' {0, 4} + pairCount s'' {1, 4} [ZMOD 3] := by
    have h := pairCount_modEq hs''c0 hs''4 (P := {2, 3}) (by decide)
    rw [show (Finset.univ.erase 5 \ {2, 3} : Finset (Fin 6)) = {0, 1, 4} from by decide] at h
    rw [show ({0, 1, 4} : Finset (Fin 6)).powersetCard 2 = {{0, 1}, {0, 4}, {1, 4}}
      from by decide] at h
    repeat rw [Finset.sum_insert (by decide)] at h
    repeat rw [Finset.sum_singleton] at h
    obtain ⟨r, hr⟩ := Int.modEq_iff_add_fac.mp h
    exact Int.modEq_iff_add_fac.mpr ⟨r, by linarith⟩
  have c24 : (pairCount s'' {2, 4} : ℤ)
      ≡ 1 + pairCount s'' {0, 5} + pairCount s'' {1, 5} + pairCount s'' {3, 5}
        + pairCount s'' {0, 1} + pairCount s'' {0, 3} + pairCount s'' {1, 3} [ZMOD 3] := by
    have h := pairCount_modEq hs''c0 hs''4 (P := {2, 4}) (by decide)
    rw [show (Finset.univ.erase 5 \ {2, 4} : Finset (Fin 6)) = {0, 1, 3} from by decide] at h
    rw [show ({0, 1, 3} : Finset (Fin 6)).powersetCard 2 = {{0, 1}, {0, 3}, {1, 3}}
      from by decide] at h
    repeat rw [Finset.sum_insert (by decide)] at h
    repeat rw [Finset.sum_singleton] at h
    obtain ⟨r, hr⟩ := Int.modEq_iff_add_fac.mp h
    exact Int.modEq_iff_add_fac.mpr ⟨r, by linarith⟩
  have c34 : (pairCount s'' {3, 4} : ℤ)
      ≡ 1 + pairCount s'' {0, 5} + pairCount s'' {1, 5} + pairCount s'' {2, 5}
        + pairCount s'' {0, 1} + pairCount s'' {0, 2} + pairCount s'' {1, 2} [ZMOD 3] := by
    have h := pairCount_modEq hs''c0 hs''4 (P := {3, 4}) (by decide)
    rw [show (Finset.univ.erase 5 \ {3, 4} : Finset (Fin 6)) = {0, 1, 2} from by decide] at h
    rw [show ({0, 1, 2} : Finset (Fin 6)).powersetCard 2 = {{0, 1}, {0, 2}, {1, 2}}
      from by decide] at h
    repeat rw [Finset.sum_insert (by decide)] at h
    repeat rw [Finset.sum_singleton] at h
    obtain ⟨r, hr⟩ := Int.modEq_iff_add_fac.mp h
    exact Int.modEq_iff_add_fac.mpr ⟨r, by linarith⟩
  -- Feed everything into the arithmetic core.
  exact arith_core n _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hsum2
    (hb 0 1 (by decide)) (hb 0 2 (by decide)) (hb 0 3 (by decide)) (hb 0 4 (by decide))
    (hb 0 5 (by decide)) (hb 1 2 (by decide)) (hb 1 3 (by decide)) (hb 1 4 (by decide))
    (hb 1 5 (by decide)) (hb 2 3 (by decide)) (hb 2 4 (by decide)) (hb 2 5 (by decide))
    (hb 3 4 (by decide)) (hb 3 5 (by decide)) (hb 4 5 (by decide))
    c01 c02 c03 c04 c12 c13 c14 c23 c24 c34

end Imo2005P6
