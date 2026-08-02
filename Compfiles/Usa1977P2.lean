/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Tactic.Ring
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# USA Mathematical Olympiad 1977, Problem 2

The triangles ABC and DEF have AD, BE and CF parallel. Show that

  [AEF] + [DBF] + [DEC] + [DBC] + [AEC] + [ABF] = 3 [ABC] + 3 [DEF],

where [XYZ] denotes the *signed* area of the triangle XYZ. Thus [XYZ] is
+ area XYZ if the order X, Y, Z is anti-clockwise and - area XYZ if the
order X, Y, Z is clockwise. So, in particular, [XYZ] = [YZX] = -[YXZ].
-/

namespace Usa1977P2

abbrev Pt := EuclideanSpace ℝ (Fin 2)

snip begin

/-- The scalar cross product of two vectors in the plane. -/
def cross (u v : Pt) : ℝ := u 0 * v 1 - u 1 * v 0

/-- The signed area of the triangle XYZ: it is + area XYZ if the order
X, Y, Z is anti-clockwise and - area XYZ if the order is clockwise. -/
noncomputable def signedArea (X Y Z : Pt) : ℝ := cross (Y - X) (Z - X) / 2

snip end

problem usa1977_p2 (A B C D E F : Pt) (h k : ℝ)
    (hE : E = B + h • (D - A))
    (hF : F = C + k • (D - A)) :
    signedArea A E F + signedArea D B F + signedArea D E C +
      signedArea D B C + signedArea A E C + signedArea A B F =
      3 * signedArea A B C + 3 * signedArea D E F := by
  subst hE hF
  simp only [signedArea, cross, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
    smul_eq_mul]
  ring

end Usa1977P2
