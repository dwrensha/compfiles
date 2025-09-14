/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InternLM-MATH LEAN Formalizer v0.1 , Shahar Blumentzvaig
-/

import Mathlib.Tactic
import ProblemExtraction


problem_file { tags := [.Algebra] }
/-!
# International Mathematical Olympiad 1973, Problem 5

$G$ is a set of non-constant functions of the real variable $x$ of the form
\[f(x) = ax + b, a \text{ and } b \text{ are real numbers,}\] and $G$ has the following properties:
(a) If $f$ and $g$ are in $G$, then $g \circ f$ is in $G$; here $(g \circ f)(x) = g[f(x)]$.
(b) If $f$ is in $G$, then its inverse $f^{-1}$ is in $G$;
    here the inverse of $f(x) = ax + b$ is $f^{-1}(x) = (x - b) / a$.
(c) For every $f$ in $G$, there exists a real number $x_f$ such that $f(x_f) = x_f$.
Prove that there exists a real number $k$ such that $f(k) = k$ for all $f$ in $G$.
-/

namespace Imo1973P5

problem imo1973_p5 {G : Set (ℝ → ℝ)}
    (hf: ∀ f ∈ G, ∃ a b : ℝ, a ≠ 0 ∧ ∀ x : ℝ, f x = a * x + b)
    (hG : ∀ f ∈ G, ∀ g ∈ G, g ∘ f ∈ G)
    (hinv : ∀ f ∈ G, (Function.invFun f) ∈ G)
    (hfix : ∀ f ∈ G, ∃ x, f x = x) :
    ∃ k : ℝ, ∀ f ∈ G, f k = k := by
  by_cases hnep : Set.Nonempty G
  · by_cases non_id : ∃f∈G , f≠id
    · obtain ⟨f,hf1⟩ := non_id
      obtain ⟨hf2,hf3⟩ := hf1

      have h1 := hfix f hf2
      obtain ⟨x,hx⟩ := h1
      use x
      intro g hg2
      have hf3 := hf f hf2
      obtain ⟨a,ha⟩ := hf3
      obtain ⟨b,hb⟩ := ha
      obtain ⟨hb1,hb2⟩ := hb

      have hf3 := hf g hg2
      obtain ⟨c,hc⟩ := hf3
      obtain ⟨d,hd⟩ := hc
      obtain ⟨hd1,hd2⟩ := hd

      have r1 := hG f hf2 g hg2
      have s1 : ∀x:ℝ , (g ∘ f) x = a*c*x + c*b+d := by
        intro x
        simp
        rw [hb2 x, hd2 (a*x+b)]
        grind
      have r2 := hG g hg2 f hf2
      have s2 : ∀x:ℝ , (f ∘ g) x = a*c*x + a*d+b := by
        intro x
        simp
        rw [hd2 x, hb2 (c*x+d)]
        grind
      have r3 := hinv (g ∘ f) r1

      have inj : Function.Injective (g ∘ f) := by
        intro a1 a2
        rw [s1,s1]
        simp
        intro h
        rcases h with h1|h1|h1
        · exact h1
        · exfalso
          exact hb1 h1
        · exfalso
          exact hd1 h1

      have s3 : ∀x:ℝ , (Function.invFun (g ∘ f)) x = (1/(a*c))*x - (c*b+d)/(a*c) := by
        intro x
        have t : (g ∘ f) ((1/(a*c))*x - (c*b+d)/(a*c)) = x := by
          rw [s1]
          field_simp
          ring
        nth_rw 1 [← t]
        rw [Function.leftInverse_invFun inj]

      have r4 := hG (Function.invFun (g∘f)) r3 (f∘g) r2
      have s4 : ∀x:ℝ , ((f ∘ g) ∘ Function.invFun (g ∘ f)) x = x + (a*d+b) - (c*b+d) := by
        intro x
        simp
        rw [s3,hd2,hb2]
        field_simp
        ring
      obtain ⟨y,hy⟩ := hfix (((f ∘ g) ∘ Function.invFun (g ∘ f))) r4
      rw [s4] at hy
      have h1 : (a * d + b) = (c * b + d) := by
        grind
      by_cases ha1 : a - 1 = 0
      · replace ha1 : a = 1 := by
          calc
            a = (a-1)+1 := by ring
            _ = 0+1 := by rw[ha1]
            _ = 1 := by ring
        rw [hb2, ha1] at hx
        simp at hx
        rw [ha1,hx] at hb2
        simp at hb2
        exfalso
        have r : f = id := by
          exact Function.forall_isFixedPt_iff.mp hb2
        exact hf3 r
      · by_cases hc1 : c-1=0
        · replace hc1 : c=1 := by
            calc
              c = (c-1)+1 := by ring
              _ = 0+1 := by rw[hc1]
              _ = 1 := by ring
          obtain ⟨z,hz⟩ := hfix g hg2
          rw [hd2,hc1] at hz
          simp at hz
          rw [hd2,hc1,hz]
          ring
        · have h2 : -b/(a-1) = -d/(c-1) := by
            rw [div_eq_div_iff ha1 hc1]
            grind
          rw [hb2] at hx
          have hx' : x = -b/(a-1) := by
            grind
          rw [hx', hd2, h2]
          field_simp
          ring
    · push_neg at non_id
      use 0
      intro f hf2
      rw [non_id f hf2]
      rfl
  · push_neg at hnep
    use 0
    intro f hf2
    exfalso
    rw [hnep] at hf2
    exact hf2

end Imo1973P5
