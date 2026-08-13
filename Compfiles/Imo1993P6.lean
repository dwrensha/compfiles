/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Tactic
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Olympiad 1993, Problem 6

There are n > 1 lamps L₀, L₁, ..., Lₙ₋₁ in a circle. We use L_{n+k} to mean L_k.
A lamp is at all times either on or off. Initially they are all on.
Perform steps s₀, s₁, ... as follows: at step sᵢ, if L_{i-1} is lit, then switch Lᵢ
from on to off or vice versa, otherwise do nothing. Show that:

(a) There is a positive integer M(n) such that after M(n) steps all the lamps are
    on again;
(b) If n = 2ᵏ, then we can take M(n) = n² - 1.
(c) If n = 2ᵏ + 1, then we can take M(n) = n² - n + 1.
-/

namespace Imo1993P6

open scoped Fin.NatCast

/-- The state of the system: the on/off states of the lamps (`true` = on), together
with the position of the lamp that may be switched at the next step. Positions are
taken modulo `n`, i.e. in `Fin n`. -/
abbrev State (n : ℕ) := (Fin n → Bool) × Fin n

/-- One step of the process, performed at the current position `s.2`: if lamp
`s.2 - 1` is on then lamp `s.2` is switched, otherwise nothing happens to the lamps;
in any case the position advances by one (modulo `n`). -/
def step {n : ℕ} [NeZero n] (s : State n) : State n :=
  (Function.update s.1 s.2 (if s.1 (s.2 - 1) then !s.1 s.2 else s.1 s.2), s.2 + 1)

/-- The initial state: all lamps on, and the next step happens at lamp `0`. -/
abbrev initial (n : ℕ) [NeZero n] : State n := (fun _ => true, 0)

/-- The lamp states after `t` steps of the process. -/
abbrev lampsAfter (n : ℕ) [NeZero n] (t : ℕ) : Fin n → Bool :=
  (step^[t] (initial n)).1

snip begin

/-- For a fixed condition `c`, the map `v ↦ (if c then !v else v)` is injective. -/
lemma toggle_inj (c : Bool) :
    Function.Injective (fun v : Bool => if c then !v else v) := by
  intro a b h
  cases c <;> cases a <;> cases b <;> simp_all

/-- Toggling a lamp according to condition `c` is xor with `c`. -/
lemma bool_toggle (c v : Bool) : (if c then !v else v) = (c ^^ v) := by
  cases c <;> simp

/-- The lamp component of one step. -/
lemma step_lamps {n : ℕ} [NeZero n] (s : State n) :
    (step s).1 = Function.update s.1 s.2 (if s.1 (s.2 - 1) then !s.1 s.2 else s.1 s.2) :=
  rfl

/-- The position component of one step. -/
lemma step_pos {n : ℕ} [NeZero n] (s : State n) : (step s).2 = s.2 + 1 := rfl

/-- After `t` steps the position is `t` (modulo `n`). -/
lemma pos_after (n : ℕ) [NeZero n] (t : ℕ) :
    (step^[t] (initial n)).2 = ((t : ℕ) : Fin n) := by
  induction t with
  | zero =>
    show (0 : Fin n) = ((0 : ℕ) : Fin n)
    rw [Fin.natCast_zero]
  | succ t ih =>
    rw [Function.iterate_succ_apply', step_pos, ih]
    exact (Nat.cast_add_one t).symm

/-- The step map is injective: a state has exactly one precursor. Indeed, the new
position tells us which lamp was just considered, and whether it was toggled is
recorded in the (unchanged) previous lamp. -/
lemma step_injective {n : ℕ} [NeZero n] (hn : 1 < n) :
    Function.Injective (step : State n → State n) := by
  rintro ⟨L, p⟩ ⟨M, q⟩ h
  simp only [step] at h
  obtain ⟨hLM, hpq⟩ := Prod.mk.inj h
  -- The positions agree, since `· + 1` is injective.
  have hpq' : p = q := add_right_cancel_iff.mp hpq
  subst hpq'
  -- Since `1 < n`, the previous lamp `p - 1` differs from the current lamp `p`.
  have hne : p - 1 ≠ p := by
    intro hc
    have h1 : p - 1 + 1 = p + 1 := congrArg (· + 1) hc
    rw [sub_add_cancel] at h1
    have h2 : (0 : Fin n) = 1 := by
      apply add_left_cancel (a := p)
      rwa [add_zero]
    have h3 := congrArg Fin.val h2
    rw [Fin.val_one', Nat.mod_eq_of_lt hn] at h3
    rcases n with _ | m
    · omega
    · rw [Fin.val_zero] at h3
      exact Nat.zero_ne_one h3
  -- Lamp `p - 1` is unchanged by the step, so it agrees in `L` and `M`.
  have hL1 : L (p - 1) = M (p - 1) := by
    have e := congrFun hLM (p - 1)
    rwa [Function.update_of_ne hne, Function.update_of_ne hne] at e
  -- The values at `p` agree, since both are obtained by the same injective toggle.
  have hLp : L p = M p := by
    have e := congrFun hLM p
    rw [Function.update_self, Function.update_self, hL1] at e
    exact toggle_inj _ e
  -- The remaining lamps are unchanged by the step, hence agree.
  rw [Prod.ext_iff]
  refine ⟨funext fun j => ?_, rfl⟩
  by_cases hjp : j = p
  · subst hjp; exact hLp
  · have e := congrFun hLM j
    rwa [Function.update_of_ne hjp, Function.update_of_ne hjp] at e

/-- The process is periodic: some positive iterate of `step` fixes the initial state.
This is because `step` is an injective (hence bijective) self-map of a finite set, so
it has finite order as a permutation. -/
lemma step_periodic (n : ℕ) [NeZero n] (hn : 1 < n) :
    ∃ M : ℕ, 0 < M ∧ step^[M] (initial n) = initial n := by
  have hinj : Function.Injective (step : State n → State n) := step_injective hn
  have hbij : Function.Bijective (step : State n → State n) := hinj.bijective_of_finite
  let σ : Equiv.Perm (State n) := Equiv.ofBijective _ hbij
  refine ⟨orderOf σ, orderOf_pos _, ?_⟩
  have h : (σ ^ orderOf σ) (initial n) = initial n := by
    rw [pow_orderOf_eq_one]
    rfl
  rw [Equiv.Perm.coe_pow] at h
  exact h

/-- Generic final phase: if after `n * (n - 1)` steps only the last lamp `L_{n-1}`
is on, then the lamps are turned on one by one and after `n² - 1` steps they are all
on again. -/
lemma all_on_of_last_only {n : ℕ} [NeZero n] (hn : 1 < n)
    (h : ∀ i : Fin n, lampsAfter n (n * (n - 1)) i = decide (i.val = n - 1)) :
    ∀ i : Fin n, lampsAfter n (n ^ 2 - 1) i = true := by
  have hT0 : ((n * (n - 1) : ℕ) : Fin n) = 0 := by
    ext
    rw [Fin.coe_natCast_eq_mod, Nat.mul_mod_right]
    simp
  have h' : ∀ i : Fin n, (step^[n * (n - 1)] (initial n)).1 i = decide (i.val = n - 1) :=
    h
  -- After `n * (n - 1) + j` steps (for `j ≤ n - 1`), exactly the lamps with index
  -- `< j` and the lamp `n - 1` are on.
  have key : ∀ j : ℕ, j ≤ n - 1 → ∀ i : Fin n,
      (step^[n * (n - 1) + j] (initial n)).1 i = decide (i.val < j ∨ i.val = n - 1) := by
    intro j
    induction j with
    | zero =>
      intro _ i
      rw [Nat.add_zero]
      simp only [Nat.not_lt_zero, false_or]
      exact h' i
    | succ j ih =>
      intro hj
      have hj1 : j < n := by omega
      have ih' := ih (by omega : j ≤ n - 1)
      have hpos : (step^[n * (n - 1) + j] (initial n)).2 = (j : Fin n) := by
        rw [pos_after, Nat.cast_add, hT0, zero_add]
      have hstep : step^[n * (n - 1) + (j + 1)] (initial n) =
          step (step^[n * (n - 1) + j] (initial n)) := by
        rw [← add_assoc, Function.iterate_succ_apply']
      intro i
      show (step^[n * (n - 1) + (j + 1)] (initial n)).1 i =
        decide (i.val < j + 1 ∨ i.val = n - 1)
      rw [hstep, step_lamps]
      by_cases hi : i = (step^[n * (n - 1) + j] (initial n)).2
      · -- Lamp `j` is toggled: its predecessor is on, so it switches from off to on.
        subst hi
        rw [Function.update_self, hpos, bool_toggle]
        have hm : ((j : Fin n) - 1).val < j ∨ ((j : Fin n) - 1).val = n - 1 := by
          by_cases hj0 : j = 0
          · subst hj0
            right
            rcases n with _ | m
            · omega
            · rw [Fin.natCast_zero, zero_sub, Fin.coe_neg_one]
              exact (Nat.add_sub_cancel m 1).symm
          · left
            have h1 : (j : Fin n) ≠ 0 := by
              rw [← Fin.val_ne_zero_iff, Fin.val_natCast, Nat.mod_eq_of_lt hj1]
              exact hj0
            rw [Fin.val_sub_one_of_ne_zero h1, Fin.val_natCast, Nat.mod_eq_of_lt hj1]
            omega
        have hpred : (step^[n * (n - 1) + j] (initial n)).1 ((j : Fin n) - 1) = true := by
          rw [ih', decide_eq_true_eq]
          exact hm
        have hcur : (step^[n * (n - 1) + j] (initial n)).1 (j : Fin n) = false := by
          rw [ih', Fin.val_natCast, Nat.mod_eq_of_lt hj1, decide_eq_false_iff_not]
          push Not
          exact ⟨le_refl j, by omega⟩
        rw [hpred, hcur, Fin.val_natCast, Nat.mod_eq_of_lt hj1, Bool.true_xor,
          Bool.not_false]
        symm
        rw [decide_eq_true_eq]
        omega
      · -- All other lamps keep their state; the threshold condition is unchanged
        -- since `i.val ≠ j`.
        rw [Function.update_of_ne hi, ih']
        have hvi : i.val ≠ j := by
          intro hv
          apply hi
          rw [hpos, Fin.ext_iff, Fin.val_natCast, Nat.mod_eq_of_lt hj1, hv]
        rw [Bool.decide_congr (by omega :
          (i.val < j ∨ i.val = n - 1) ↔ (i.val < j + 1 ∨ i.val = n - 1))]
  intro i
  have hfin : n * (n - 1) + (n - 1) = n ^ 2 - 1 := by
    have h1 : n * (n - 1) = n * n - n := by rw [Nat.mul_sub_left_distrib, mul_one]
    have h2 : n ≤ n * n := Nat.le_mul_of_pos_right n (by omega)
    rw [h1, pow_two]
    omega
  rw [← hfin]
  show (step^[n * (n - 1) + (n - 1)] (initial n)).1 i = true
  rw [key (n - 1) le_rfl i, decide_eq_true_eq]
  have := i.isLt
  omega

/-- If the lamp checked at a step is off, the step leaves all lamps unchanged. -/
lemma step_lamps_eq_of_pred_off {n : ℕ} [NeZero n] {s : State n}
    (h : s.1 (s.2 - 1) = false) : (step s).1 = s.1 := by
  rw [step_lamps]
  funext i
  by_cases hi : i = s.2
  · subst hi
    rw [Function.update_self, h]
    simp
  · rw [Function.update_of_ne hi]

/-- If the lamp checked at a step is on, the step flips the current lamp. -/
lemma step_lamps_toggle {n : ℕ} [NeZero n] {s : State n}
    (h : s.1 (s.2 - 1) = true) (i : Fin n) :
    (step s).1 i = (if i = s.2 then !s.1 i else s.1 i) := by
  rw [step_lamps]
  by_cases hi : i = s.2
  · subst hi
    rw [Function.update_self, h]
    simp
  · rw [Function.update_of_ne hi, if_neg hi]

/-- Generic final phase for the `n = 2ᵏ + 1` case: if after `n * (n - 2)` steps only
lamp `L₁` is on, then after two idle steps the lamps `L₂, L₃, …, L_{n-1}, L₀` are
turned on one by one, and after `n² - n + 1` steps they are all on again. -/
lemma all_on_of_lamp1_only {n : ℕ} [NeZero n] (hn : 2 < n)
    (h : ∀ i : Fin n, lampsAfter n (n * (n - 2)) i = decide (i.val = 1)) :
    ∀ i : Fin n, lampsAfter n (n ^ 2 - n + 1) i = true := by
  have h' : ∀ i : Fin n, (step^[n * (n - 2)] (initial n)).1 i = decide (i.val = 1) := h
  have hT0 : ((n * (n - 2) : ℕ) : Fin n) = 0 := by
    ext
    rw [Fin.coe_natCast_eq_mod, Nat.mul_mod_right]
    simp
  -- First idle step: the position is `0` and lamp `n - 1` is off.
  have hidle1 : (step^[n * (n - 2) + 1] (initial n)).1 =
      (step^[n * (n - 2)] (initial n)).1 := by
    have hcond : (step^[n * (n - 2)] (initial n)).1
        ((step^[n * (n - 2)] (initial n)).2 - 1) = false := by
      rw [pos_after, hT0, h', decide_eq_false_iff_not]
      rcases n with _ | m
      · omega
      · rw [zero_sub, Fin.coe_neg_one]
        omega
    rw [Function.iterate_succ_apply', step_lamps_eq_of_pred_off hcond]
  -- Second idle step: the position is `1` and lamp `0` is off.
  have hidle2 : (step^[n * (n - 2) + 2] (initial n)).1 =
      (step^[n * (n - 2)] (initial n)).1 := by
    have hcond : (step^[n * (n - 2) + 1] (initial n)).1
        ((step^[n * (n - 2) + 1] (initial n)).2 - 1) = false := by
      rw [hidle1, pos_after, Nat.cast_add_one, hT0, zero_add,
        sub_self, h', decide_eq_false_iff_not]
      have hz : ((0 : Fin n) : ℕ) = 0 := by simp
      rw [hz]
      omega
    rw [Function.iterate_succ_apply', step_lamps_eq_of_pred_off hcond, hidle1]
  -- Lamps `1, …, j - 1` are on after `n * (n - 2) + j` steps, for `2 ≤ j ≤ n`.
  have key : ∀ j : ℕ, 2 ≤ j → j ≤ n → ∀ i : Fin n,
      (step^[n * (n - 2) + j] (initial n)).1 i = decide (1 ≤ i.val ∧ i.val < j) := by
    intro j
    induction j with
    | zero => intro hj; omega
    | succ j ih =>
      intro hj2 hjN
      by_cases hjbase : j + 1 = 2
      · intro i
        rw [hjbase, hidle2, h']
        rw [Bool.decide_congr (by omega : (i.val = 1) ↔ (1 ≤ i.val ∧ i.val < 2))]
      · have hj2' : 2 ≤ j := by omega
        have ih' := ih hj2' (by omega : j ≤ n)
        have hj1 : j < n := by omega
        have hpos : (step^[n * (n - 2) + j] (initial n)).2 = (j : Fin n) := by
          rw [pos_after, Nat.cast_add, hT0, zero_add]
        have hpred : (step^[n * (n - 2) + j] (initial n)).1
            ((step^[n * (n - 2) + j] (initial n)).2 - 1) = true := by
          rw [hpos, ih', decide_eq_true_eq]
          have h1 : (j : Fin n) ≠ 0 := by
            rw [← Fin.val_ne_zero_iff, Fin.val_natCast, Nat.mod_eq_of_lt hj1]
            omega
          rw [Fin.val_sub_one_of_ne_zero h1, Fin.val_natCast, Nat.mod_eq_of_lt hj1]
          omega
        intro i
        show (step^[n * (n - 2) + (j + 1)] (initial n)).1 i =
          decide (1 ≤ i.val ∧ i.val < j + 1)
        rw [← add_assoc, Function.iterate_succ_apply', step_lamps_toggle hpred, hpos]
        by_cases hi : i = (j : Fin n)
        · subst hi
          rw [if_pos rfl, ih', Fin.val_natCast, Nat.mod_eq_of_lt hj1]
          have hoff : decide (1 ≤ j ∧ j < j) = false := by
            rw [decide_eq_false_iff_not]
            omega
          rw [hoff, Bool.not_false]
          symm
          rw [decide_eq_true_eq]
          omega
        · rw [if_neg hi, ih']
          have hvi : i.val ≠ j := by
            intro hv
            apply hi
            rw [Fin.ext_iff, Fin.val_natCast, Nat.mod_eq_of_lt hj1, hv]
          rw [Bool.decide_congr (by omega :
            (1 ≤ i.val ∧ i.val < j) ↔ (1 ≤ i.val ∧ i.val < j + 1))]
  -- The last step (position wraps to `0`) turns lamp `0` on, since lamp `n - 1` is on.
  have hlast : ∀ i : Fin n, (step^[n * (n - 2) + (n + 1)] (initial n)).1 i = true := by
    have hposN : (step^[n * (n - 2) + n] (initial n)).2 = (0 : Fin n) := by
      rw [pos_after, Nat.cast_add, hT0, Fin.natCast_self, add_zero]
    have hpredN : (step^[n * (n - 2) + n] (initial n)).1
        ((step^[n * (n - 2) + n] (initial n)).2 - 1) = true := by
      rw [hposN, key n (by omega) le_rfl, decide_eq_true_eq]
      rcases n with _ | m
      · omega
      · rw [zero_sub, Fin.coe_neg_one]
        omega
    intro i
    rw [← add_assoc, Function.iterate_succ_apply', step_lamps_toggle hpredN, hposN]
    by_cases hi : i = (0 : Fin n)
    · subst hi
      rw [if_pos rfl, key n (by omega) le_rfl]
      have hz : ((0 : Fin n) : ℕ) = 0 := by simp
      rw [hz]
      have hoff : decide (1 ≤ (0 : ℕ) ∧ (0 : ℕ) < n) = false := by
        rw [decide_eq_false_iff_not]
        omega
      rw [hoff, Bool.not_false]
    · rw [if_neg hi, key n (by omega) le_rfl, decide_eq_true_eq]
      have hvi : i.val ≠ 0 := by
        intro hv
        apply hi
        rw [Fin.ext_iff, hv]
        simp
      have hlt := i.isLt
      omega
  have hfin : n * (n - 2) + (n + 1) = n ^ 2 - n + 1 := by
    have h1 : n * (n - 2) = n * n - 2 * n := by
      rw [Nat.mul_sub_left_distrib]
      ring_nf
    have h2 : 2 * n ≤ n * n := Nat.mul_le_mul (by omega) le_rfl
    rw [h1, pow_two]
    omega
  intro i
  rw [← hfin]
  exact hlast i

/- The cores of parts (b) and (c) are proved at the end of this section
(`last_lamp_only_of_two_pow` and `lamp1_only_of_two_pow_add_one`): induction on `k`
via a `ZMod 2` model of the process (toggling is adding the predecessor); see
`all_on_of_last_only` and `all_on_of_lamp1_only` for the final phases. -/
/-! ### ZMod 2 model of the process -/

/-- The same process with lamp values in `ZMod 2`: toggling is adding the predecessor. -/
def zstep {n : ℕ} [NeZero n] (s : (Fin n → ZMod 2) × Fin n) : (Fin n → ZMod 2) × Fin n :=
  (Function.update s.1 s.2 (s.1 s.2 + s.1 (s.2 - 1)), s.2 + 1)

def zinit (n : ℕ) [NeZero n] : (Fin n → ZMod 2) × Fin n := (fun _ => 1, 0)

def z2b (a : ZMod 2) : Bool := decide (a = 1)

lemma z2b_one : z2b 1 = true := rfl

lemma z2b_zero : z2b 0 = false := rfl

lemma z2b_add : ∀ a b : ZMod 2, (if z2b b then !z2b a else z2b a) = z2b (a + b) := by decide

lemma zadd_self : ∀ a : ZMod 2, a + a = 0 := by decide

lemma one_add_one_zmod : (1 : ZMod 2) + 1 = 0 := by decide

lemma one_add_one_cancel (a : ZMod 2) : (1 + a) + 1 = a := by
  rw [add_assoc, ← add_left_comm a 1 1, one_add_one_zmod, add_zero]

/-- The position after `t` steps. -/
lemma pos_lemma {n : ℕ} [NeZero n] (x : Fin n → ZMod 2) (p : Fin n) (t : ℕ) :
    (zstep^[t] (x, p)).2 = p + (t : Fin n) := by
  have hn : 0 < n := NeZero.pos n
  induction t with
  | zero =>
    show p = p + ((0 : ℕ) : Fin n)
    simp
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    show (zstep^[t] (x, p)).2 + 1 = p + ((t + 1 : ℕ) : Fin n)
    rw [ih, Nat.cast_succ, ← add_assoc]

/-- Correspondence between the Bool process and the ZMod 2 process. -/
lemma glue {n : ℕ} [NeZero n] (t : ℕ) :
    (step^[t] (initial n)) =
      (fun i => z2b ((zstep^[t] (zinit n)).1 i), (zstep^[t] (zinit n)).2) := by
  induction t with
  | zero =>
    apply Prod.ext
    · funext i
      show true = z2b 1
      rfl
    · rfl
  | succ t ih =>
    have ih1 : (step^[t] (initial n)).1 = fun i => z2b ((zstep^[t] (zinit n)).1 i) :=
      congrArg Prod.fst ih
    have ih2 : (step^[t] (initial n)).2 = (zstep^[t] (zinit n)).2 := congrArg Prod.snd ih
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    apply Prod.ext
    · funext j
      show (Function.update (step^[t] (initial n)).1 (step^[t] (initial n)).2
          (if (step^[t] (initial n)).1 ((step^[t] (initial n)).2 - 1)
          then !(step^[t] (initial n)).1 (step^[t] (initial n)).2
          else (step^[t] (initial n)).1 (step^[t] (initial n)).2)) j
        = z2b ((Function.update (zstep^[t] (zinit n)).1 (zstep^[t] (zinit n)).2
          ((zstep^[t] (zinit n)).1 (zstep^[t] (zinit n)).2
            + (zstep^[t] (zinit n)).1 ((zstep^[t] (zinit n)).2 - 1))) j)
      rw [ih1, ih2]
      by_cases hj : j = (zstep^[t] (zinit n)).2
      · subst hj
        rw [Function.update_self, Function.update_self]
        exact z2b_add _ _
      · rw [Function.update_of_ne hj, Function.update_of_ne hj]
    · show (step^[t] (initial n)).2 + 1 = (zstep^[t] (zinit n)).2 + 1
      rw [ih2]

/-! ### The round map `L` and its algebra -/

/-- The last index of `Fin n`. -/
def lasti (n : ℕ) [NeZero n] : Fin n := ⟨n - 1, by have := NeZero.pos n; omega⟩

lemma lasti_val (n : ℕ) [NeZero n] : (lasti n).val = n - 1 := rfl

lemma zero_sub_one_eq_lasti (n : ℕ) [NeZero n] : ((0 : Fin n) - 1) = lasti n := by
  have hn := NeZero.pos n
  have hc : lasti n = ((n - 1 : ℕ) : Fin n) := by
    apply Fin.ext
    show n - 1 = ((n - 1 : ℕ) : Fin n).val
    rw [Fin.val_natCast, Nat.mod_eq_of_lt (by omega : n - 1 < n)]
  rw [hc, sub_eq_iff_eq_add]
  show (0 : Fin n) = ((n - 1 : ℕ) : Fin n) + 1
  rw [← Nat.cast_add_one]
  have hnn : n - 1 + 1 = n := by omega
  rw [hnn, Fin.natCast_self]

/-- One full round of the process: `L x p = x last + ∑_{i ≤ p} x i` in `ZMod 2`. -/
def L {n : ℕ} [NeZero n] (x : Fin n → ZMod 2) : Fin n → ZMod 2 :=
  fun p => x (lasti n) + ∑ i ∈ Finset.range (p.val + 1), x ⟨i % n, Nat.mod_lt i (NeZero.pos n)⟩

/-- Total parity of a lamp vector. -/
def tot {n : ℕ} (x : Fin n → ZMod 2) : ZMod 2 := ∑ i, x i

/-- The vector with only the last lamp on. -/
def eFn (n : ℕ) [NeZero n] : Fin n → ZMod 2 := fun j => if j = lasti n then 1 else 0

lemma L_apply {n : ℕ} [NeZero n] (x : Fin n → ZMod 2) (p : Fin n) :
    L x p = x (lasti n) + ∑ i ∈ Finset.range (p.val + 1), x ⟨i % n, Nat.mod_lt i (NeZero.pos n)⟩ :=
  rfl

lemma L_add {n : ℕ} [NeZero n] (a b : Fin n → ZMod 2) :
    L (a + b) = fun j => L a j + L b j := by
  funext j
  simp only [L_apply, Pi.add_apply, Finset.sum_add_distrib]
  ring

lemma tot_add {n : ℕ} (a b : Fin n → ZMod 2) : tot (a + b) = tot a + tot b := by
  simp only [tot, Pi.add_apply, Finset.sum_add_distrib]

lemma tot_eq {n : ℕ} [NeZero n] (x : Fin n → ZMod 2) :
    tot x = ∑ i ∈ Finset.range n, x ⟨i % n, Nat.mod_lt i (NeZero.pos n)⟩ := by
  have h := Fin.sum_univ_eq_sum_range (fun i => x ⟨i % n, Nat.mod_lt i (NeZero.pos n)⟩) n
  rw [tot, ← h]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact Fin.ext (Nat.mod_eq_of_lt i.isLt).symm

lemma eFn_lasti {n : ℕ} [NeZero n] : eFn n (lasti n) = 1 := by
  simp [eFn]

lemma tot_eFn {n : ℕ} [NeZero n] : tot (eFn n) = 1 := by
  show (∑ i, (if i = lasti n then (1 : ZMod 2) else 0)) = 1
  rw [Finset.sum_ite_eq']
  simp

lemma L_eFn {n : ℕ} [NeZero n] : L (eFn n) = (fun _ => 1) + eFn n := by
  funext p
  rw [L_apply, eFn_lasti]
  have hsum : (∑ i ∈ Finset.range (p.val + 1),
      eFn n ⟨i % n, Nat.mod_lt i (NeZero.pos n)⟩) = if p.val = n - 1 then (1 : ZMod 2) else 0 := by
    have key : ∀ i ∈ Finset.range (p.val + 1),
        eFn n ⟨i % n, Nat.mod_lt i (NeZero.pos n)⟩ = if i = n - 1 then (1 : ZMod 2) else 0 := by
      intro i hi
      have hi2 : i < n := by
        have hp := p.isLt
        rw [Finset.mem_range] at hi
        omega
      have hmk : (⟨i % n, Nat.mod_lt i (NeZero.pos n)⟩ : Fin n) = ⟨i, hi2⟩ :=
        Fin.ext (Nat.mod_eq_of_lt hi2)
      rw [hmk]
      show (if (⟨i, hi2⟩ : Fin n) = lasti n then (1 : ZMod 2) else 0)
        = if i = n - 1 then 1 else 0
      by_cases h : i = n - 1
      · rw [if_pos h, if_pos (Fin.ext h)]
      · rw [if_neg h, if_neg (fun hc => h (Fin.ext_iff.mp hc))]
    rw [Finset.sum_congr rfl key, Finset.sum_ite_eq']
    by_cases hp : p.val = n - 1
    · rw [if_pos hp, if_pos (by rw [Finset.mem_range]; have := p.isLt; omega)]
    · rw [if_neg hp, if_neg (by rw [Finset.mem_range]; have := p.isLt; omega)]
  rw [hsum]
  show (1 : ZMod 2) + (if p.val = n - 1 then 1 else 0)
    = 1 + (if p = lasti n then 1 else 0)
  by_cases hp : p = lasti n
  · rw [if_pos hp, if_pos (show p.val = n - 1 from Fin.ext_iff.mp hp)]
  · rw [if_neg hp, if_neg (show p.val ≠ n - 1 from fun hc => hp (Fin.ext hc))]

/-! ### The round lemma -/

lemma roundInv {n : ℕ} [NeZero n] (x : Fin n → ZMod 2) (m : ℕ) (hm : m ≤ n) :
    (zstep^[m] (x, 0)).1 = fun j => if j.val < m then L x j else x j := by
  induction m with
  | zero =>
    funext j
    show x j = if j.val < 0 then L x j else x j
    rw [if_neg (Nat.not_lt_zero _)]
  | succ m ih =>
    have hmn : m ≤ n := by omega
    have hlt : m < n := by omega
    rw [Function.iterate_succ_apply']
    have hpos := pos_lemma x 0 m
    show Function.update (zstep^[m] (x, 0)).1 (zstep^[m] (x, 0)).2
        ((zstep^[m] (x, 0)).1 (zstep^[m] (x, 0)).2
          + (zstep^[m] (x, 0)).1 ((zstep^[m] (x, 0)).2 - 1)) = _
    rw [ih hmn, hpos]
    simp only [zero_add]
    funext j
    have hvm : ((m : Fin n)).val = m := by
      rw [Fin.val_natCast]
      exact Nat.mod_eq_of_lt hlt
    by_cases hj : j = (m : Fin n)
    · subst hj
      rw [Function.update_self, hvm, if_pos (Nat.lt_succ_self m)]
      by_cases hm0 : m = 0
      · subst hm0
        rw [Fin.natCast_zero, zero_sub_one_eq_lasti,
          if_neg (Nat.not_lt_zero _), if_neg (Nat.not_lt_zero _), L_apply]
        have hv0 : ((0 : Fin n)).val = 0 := by simp
        rw [hv0, Finset.sum_range_one]
        have hmk : (⟨0 % n, Nat.mod_lt 0 (NeZero.pos n)⟩ : Fin n) = (0 : Fin n) := by
          apply Fin.ext
          show 0 % n = ((0 : Fin n)).val
          rw [hv0]
          exact Nat.zero_mod n
        rw [hmk, add_comm (x (0 : Fin n)) (x (lasti n))]
      · have hsub : ((m : Fin n) - 1) = ⟨m - 1, by omega⟩ := by
          apply Fin.ext
          rw [Fin.val_sub_one_of_ne_zero]
          · show ((m : Fin n)).val - 1 = m - 1
            rw [Fin.val_natCast, Nat.mod_eq_of_lt hlt]
          · intro hc
            rw [Fin.ext_iff] at hc
            simp [Fin.val_natCast, Nat.mod_eq_of_lt hlt] at hc
            omega
        rw [hsub, if_pos (show m - 1 < m by omega), if_neg (Nat.lt_irrefl m),
          L_apply, L_apply, hvm]
        have hm1 : m - 1 + 1 = m := by omega
        rw [hm1, Finset.sum_range_succ]
        have hmk : (⟨m % n, Nat.mod_lt m (NeZero.pos n)⟩ : Fin n) = (m : Fin n) := by
          apply Fin.ext
          show m % n = ((m : Fin n)).val
          rw [hvm]
          exact Nat.mod_eq_of_lt hlt
        rw [hmk]
        ring
    · rw [Function.update_of_ne hj]
      have hjm : j.val ≠ m := by
        intro h
        apply hj
        apply Fin.ext
        rw [hvm]
        exact h
      by_cases h2 : j.val < m
      · rw [if_pos h2, if_pos (by omega : j.val < m + 1)]
      · rw [if_neg h2, if_neg (by omega : ¬ j.val < m + 1)]

/-- One full round of the process applies `L` and returns to position `0`. -/
lemma round {n : ℕ} [NeZero n] (x : Fin n → ZMod 2) :
    zstep^[n] (x, 0) = (L x, (0 : Fin n)) := by
  apply Prod.ext
  · rw [roundInv x n (le_refl n)]
    funext j
    show (if j.val < n then L x j else x j) = L x j
    rw [if_pos j.isLt]
  · rw [pos_lemma, Fin.natCast_self, add_zero]

lemma aux {n : ℕ} [NeZero n] (m : ℕ) :
    (zstep^[n])^[m] (zinit n) = (L^[m] (fun _ => 1), (0 : Fin n)) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih, round, Function.iterate_succ_apply']

/-! ### Concatenation and the `n → n+n` relation -/

/-- Concatenation of two lamp vectors. -/
def cat {n : ℕ} (y z : Fin n → ZMod 2) : Fin (n + n) → ZMod 2 :=
  fun i => if h : i.val < n then y ⟨i.val, h⟩ else z ⟨i.val - n, by have h2 := i.isLt; omega⟩

lemma tot_cat {n : ℕ} [NeZero n] (y z : Fin n → ZMod 2) :
    tot (cat y z) = tot y + tot z := by
  have : NeZero (n + n) := ⟨by have := NeZero.ne n; omega⟩
  rw [tot_eq, tot_eq, tot_eq]
  have hsplit : ∀ f : ℕ → ZMod 2,
      (∑ i ∈ Finset.range (n + n), f i)
        = (∑ i ∈ Finset.range n, f i) + ∑ i ∈ Finset.range n, f (n + i) := by
    intro f
    have h1 : Finset.range (n + n) = Finset.Ico 0 (n + n) := Finset.range_eq_Ico (n + n)
    rw [h1, ← Finset.sum_Ico_consecutive f (Nat.zero_le n) (Nat.le_add_right n n),
      ← Finset.range_eq_Ico]
    congr 1
    rw [Finset.sum_Ico_eq_sum_range]
    have h2 : n + n - n = n := by omega
    rw [h2]
  rw [hsplit]
  have hleft : (∑ i ∈ Finset.range n,
      cat y z ⟨i % (n + n), Nat.mod_lt i (NeZero.pos _)⟩)
      = ∑ i ∈ Finset.range n, y ⟨i % n, Nat.mod_lt i (NeZero.pos n)⟩ := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    have hmk : (⟨i % (n + n), Nat.mod_lt i (NeZero.pos _)⟩ : Fin (n + n))
        = ⟨i, by omega⟩ :=
      Fin.ext (Nat.mod_eq_of_lt (by omega))
    rw [hmk]
    show (if h2 : i < n then y ⟨i, h2⟩ else z ⟨i - n, by omega⟩)
      = y ⟨i % n, Nat.mod_lt i (NeZero.pos n)⟩
    rw [dif_pos (show i < n by omega)]
    congr 1
    apply Fin.ext
    show i = i % n
    rw [Nat.mod_eq_of_lt hi]
  have hright : (∑ i ∈ Finset.range n,
      cat y z ⟨(n + i) % (n + n), Nat.mod_lt (n + i) (NeZero.pos _)⟩)
      = ∑ i ∈ Finset.range n, z ⟨i % n, Nat.mod_lt i (NeZero.pos n)⟩ := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    have hmk : (⟨(n + i) % (n + n), Nat.mod_lt (n + i) (NeZero.pos _)⟩ : Fin (n + n))
        = ⟨n + i, by omega⟩ :=
      Fin.ext (Nat.mod_eq_of_lt (by omega))
    rw [hmk]
    show (if h2 : n + i < n then y ⟨n + i, h2⟩ else z ⟨n + i - n, by omega⟩)
      = z ⟨i % n, Nat.mod_lt i (NeZero.pos n)⟩
    rw [dif_neg (show ¬ n + i < n by omega)]
    congr 1
    apply Fin.ext
    show n + i - n = i % n
    rw [Nat.mod_eq_of_lt hi]
    omega
  rw [hleft, hright]

lemma catL {n : ℕ} [NeZero n] (y z : Fin n → ZMod 2) :
    L (cat y z) = cat (fun j => L y j + (y (lasti n) + z (lasti n)))
      (fun j => L z j + tot y) := by
  have : NeZero (n + n) := ⟨by have := NeZero.ne n; omega⟩
  funext p
  rw [L_apply]
  have hlast : cat y z (lasti (n + n)) = z (lasti n) := by
    show (if h : (lasti (n + n)).val < n then y ⟨(lasti (n + n)).val, h⟩
      else z ⟨(lasti (n + n)).val - n, by omega⟩) = z (lasti n)
    rw [dif_neg (by rw [lasti_val]; have := NeZero.pos n; omega)]
    congr 1
    apply Fin.ext
    show (lasti (n + n)).val - n = (lasti n).val
    rw [lasti_val, lasti_val]
    have := NeZero.pos n
    omega
  rw [hlast]
  by_cases hp : p.val < n
  · have hsum : (∑ i ∈ Finset.range (p.val + 1),
        cat y z ⟨i % (n + n), Nat.mod_lt i (NeZero.pos _)⟩)
        = ∑ i ∈ Finset.range (p.val + 1), y ⟨i % n, Nat.mod_lt i (NeZero.pos n)⟩ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mem_range] at hi
      have hmk : (⟨i % (n + n), Nat.mod_lt i (NeZero.pos _)⟩ : Fin (n + n))
          = ⟨i, by omega⟩ :=
        Fin.ext (Nat.mod_eq_of_lt (by omega))
      rw [hmk]
      show (if h2 : i < n then y ⟨i, h2⟩ else z ⟨i - n, by omega⟩)
        = y ⟨i % n, Nat.mod_lt i (NeZero.pos n)⟩
      rw [dif_pos (show i < n by omega)]
      congr 1
      apply Fin.ext
      show i = i % n
      rw [Nat.mod_eq_of_lt (by omega : i < n)]
    rw [hsum]
    have hcat : cat (fun j => L y j + (y (lasti n) + z (lasti n))) (fun j => L z j + tot y) p
        = L y ⟨p.val, hp⟩ + (y (lasti n) + z (lasti n)) := by
      show (if h : p.val < n then (fun j => L y j + (y (lasti n) + z (lasti n))) ⟨p.val, h⟩
          else (fun j => L z j + tot y) ⟨p.val - n, by omega⟩)
          = L y ⟨p.val, hp⟩ + (y (lasti n) + z (lasti n))
      rw [dif_pos hp]
    rw [hcat, L_apply]
    have hv : (⟨p.val, hp⟩ : Fin n).val = p.val := rfl
    rw [hv, add_add_add_comm, zadd_self, zero_add, add_comm]
  · have hq : p.val - n < n := by have := p.isLt; omega
    have hsum : (∑ i ∈ Finset.range (p.val + 1),
        cat y z ⟨i % (n + n), Nat.mod_lt i (NeZero.pos _)⟩)
        = (∑ i ∈ Finset.range n, y ⟨i % n, Nat.mod_lt i (NeZero.pos n)⟩)
          + ∑ i ∈ Finset.range (p.val + 1 - n), z ⟨i % n, Nat.mod_lt i (NeZero.pos n)⟩ := by
      have hsplit : (∑ i ∈ Finset.range (p.val + 1),
          cat y z ⟨i % (n + n), Nat.mod_lt i (NeZero.pos _)⟩)
          = (∑ i ∈ Finset.range n, cat y z ⟨i % (n + n), Nat.mod_lt i (NeZero.pos _)⟩)
            + ∑ i ∈ Finset.range (p.val + 1 - n),
              cat y z ⟨(n + i) % (n + n), Nat.mod_lt (n + i) (NeZero.pos _)⟩ := by
        have h1 : Finset.range (p.val + 1) = Finset.Ico 0 (p.val + 1) :=
          Finset.range_eq_Ico (p.val + 1)
        rw [h1, ← Finset.sum_Ico_consecutive _ (Nat.zero_le n) (by omega : n ≤ p.val + 1),
          ← Finset.range_eq_Ico, Finset.sum_Ico_eq_sum_range]
      rw [hsplit]
      congr 1
      · apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mem_range] at hi
        have hmk : (⟨i % (n + n), Nat.mod_lt i (NeZero.pos _)⟩ : Fin (n + n))
            = ⟨i, by omega⟩ :=
          Fin.ext (Nat.mod_eq_of_lt (by omega))
        rw [hmk]
        show (if h2 : i < n then y ⟨i, h2⟩ else z ⟨i - n, by omega⟩)
          = y ⟨i % n, Nat.mod_lt i (NeZero.pos n)⟩
        rw [dif_pos (show i < n by omega)]
        congr 1
        apply Fin.ext
        show i = i % n
        rw [Nat.mod_eq_of_lt hi]
      · apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mem_range] at hi
        have hmk : (⟨(n + i) % (n + n), Nat.mod_lt (n + i) (NeZero.pos _)⟩ : Fin (n + n))
            = ⟨n + i, by omega⟩ :=
          Fin.ext (Nat.mod_eq_of_lt (by omega))
        rw [hmk]
        show (if h2 : n + i < n then y ⟨n + i, h2⟩ else z ⟨n + i - n, by omega⟩)
          = z ⟨i % n, Nat.mod_lt i (NeZero.pos n)⟩
        rw [dif_neg (show ¬ n + i < n by omega)]
        congr 1
        apply Fin.ext
        show n + i - n = i % n
        rw [Nat.mod_eq_of_lt (by omega : i < n)]
        omega
    rw [hsum]
    have hcat : cat (fun j => L y j + (y (lasti n) + z (lasti n))) (fun j => L z j + tot y) p
        = L z ⟨p.val - n, hq⟩ + tot y := by
      show (if h : p.val < n then (fun j => L y j + (y (lasti n) + z (lasti n))) ⟨p.val, h⟩
          else (fun j => L z j + tot y) ⟨p.val - n, by omega⟩)
          = L z ⟨p.val - n, hq⟩ + tot y
      rw [dif_neg hp]
    rw [hcat, L_apply, tot_eq]
    have hv : (⟨p.val - n, hq⟩ : Fin n).val = p.val - n := rfl
    rw [hv, show p.val - n + 1 = p.val + 1 - n by omega]
    rw [add_left_comm, add_comm]

/-! ### The strengthened induction statement -/

def A (n : ℕ) [NeZero n] : Prop := L^[n - 1] ((fun _ => 1) : Fin n → ZMod 2) = eFn n

def B (n : ℕ) [NeZero n] : Prop :=
  ∀ m, m ≤ n - 2 → tot (L^[m] ((fun _ => 1) : Fin n → ZMod 2)) = 0

def C (n : ℕ) [NeZero n] : Prop :=
  ∀ m, m ≤ n - 1 → (L^[m] ((fun _ => 1) : Fin n → ZMod 2)) (lasti n) = 1

/-- Lamp `n-2` is off at every positive round `m ≤ n-1`. -/
def D (n : ℕ) [NeZero n] : Prop :=
  ∀ m, 1 ≤ m → m ≤ n - 1 → (L^[m] ((fun _ => 1) : Fin n → ZMod 2)) ⟨n - 2, by have := NeZero.pos n; omega⟩ = 0

lemma base_case : A 2 ∧ B 2 ∧ C 2 ∧ D 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · show L^[2 - 1] (fun _ => 1) = eFn 2
    decide
  · show ∀ m, m ≤ 2 - 2 → tot (L^[m] ((fun _ => 1) : Fin 2 → ZMod 2)) = 0
    intro m hm
    have h0 : m = 0 := by
      have h1 : m ≤ 0 := hm
      omega
    subst h0
    decide
  · show ∀ m, m ≤ 2 - 1 → (L^[m] ((fun _ => 1) : Fin 2 → ZMod 2)) (lasti 2) = 1
    intro m hm
    interval_cases m <;> decide
  · show ∀ m, 1 ≤ m → m ≤ 2 - 1 → (L^[m] ((fun _ => 1) : Fin 2 → ZMod 2)) ⟨2 - 2, by omega⟩ = 0
    intro m h1 hm
    interval_cases m; decide

lemma stepLemma (n : ℕ) [NeZero n] (h2 : 2 ≤ n) (hA : A n) (hB : B n) (hC : C n)
    (hD : D n) :
    A (n + n) ∧ B (n + n) ∧ C (n + n) ∧ D (n + n) := by
  have : NeZero (n + n) := ⟨by have := NeZero.ne n; omega⟩
  -- Phase A: the first `n-1` rounds duplicate the `n`-lamp process.
  have hPA : ∀ M, M ≤ n - 1 →
      L^[M] ((fun _ => (1 : ZMod 2)) : Fin (n + n) → ZMod 2) =
        cat (L^[M] ((fun _ => (1 : ZMod 2)) : Fin n → ZMod 2))
          (L^[M] ((fun _ => (1 : ZMod 2)) : Fin n → ZMod 2)) := by
    intro M
    induction M with
    | zero =>
      intro _
      funext i
      show (1 : ZMod 2) = cat (fun _ => 1) (fun _ => 1) i
      unfold cat
      by_cases h : i.val < n
      · rw [dif_pos h]
      · rw [dif_neg h]
    | succ M ih =>
      intro hM
      rw [Function.iterate_succ_apply', ih (by omega : M ≤ n - 1), catL (n := n),
        Function.iterate_succ_apply']
      have hσ : tot (L^[M] (fun _ => (1 : ZMod 2))) = 0 := hB M (by omega : M ≤ n - 2)
      congr 1
      · funext j
        show L (L^[M] (fun _ => 1)) j
            + ((L^[M] (fun _ => 1)) (lasti n) + (L^[M] (fun _ => 1)) (lasti n))
          = L (L^[M] (fun _ => 1)) j
        rw [zadd_self, add_zero]
      · funext j
        show L (L^[M] (fun _ => 1)) j + tot (L^[M] (fun _ => 1))
          = L (L^[M] (fun _ => 1)) j
        rw [hσ, add_zero]
  -- Phase B: the next `n` rounds.
  have hPB : ∀ j, 1 ≤ j → j ≤ n →
      L^[n - 1 + j] ((fun _ => (1 : ZMod 2)) : Fin (n + n) → ZMod 2) =
        cat (L^[j - 1] ((fun _ => (1 : ZMod 2)) : Fin n → ZMod 2) + eFn n) (eFn n) := by
    intro j
    induction j with
    | zero => intro h; omega
    | succ j ih =>
      intro h1 hj
      by_cases hj0 : j = 0
      · subst hj0
        rw [Function.iterate_succ_apply', hPA (n - 1) (le_refl _), hA, catL (n := n)]
        have hσ : tot (eFn n) = 1 := tot_eFn
        have hel : eFn n (lasti n) = 1 := eFn_lasti
        congr 1
        · funext i
          show L (eFn n) i + (eFn n (lasti n) + eFn n (lasti n))
            = (fun _ => (1 : ZMod 2)) i + eFn n i
          rw [hel, zadd_self, add_zero, L_eFn, Pi.add_apply]
        · funext i
          show L (eFn n) i + tot (eFn n) = eFn n i
          rw [hσ, L_eFn, Pi.add_apply]
          show (1 : ZMod 2) + eFn n i + 1 = eFn n i
          rw [add_assoc, ← add_left_comm (eFn n i) 1 1, one_add_one_zmod, add_zero]
      · have h1j : 1 ≤ j := by omega
        rw [show n - 1 + (j + 1) = (n - 1 + j) + 1 by omega, Function.iterate_succ_apply',
          ih h1j (by omega : j ≤ n), catL (n := n)]
        have hy1 : (L^[j - 1] ((fun _ => (1 : ZMod 2)) : Fin n → ZMod 2) + eFn n) (lasti n) = 0 := by
          rw [Pi.add_apply, hC (j - 1) (by omega : j - 1 ≤ n - 1), eFn_lasti, one_add_one_zmod]
        have hy2 : tot (L^[j - 1] ((fun _ => (1 : ZMod 2)) : Fin n → ZMod 2) + eFn n) = 1 := by
          rw [tot_add, hB (j - 1) (by omega : j - 1 ≤ n - 2), tot_eFn, zero_add]
        rw [hy1, hy2, eFn_lasti]
        have hLsplit : L (L^[j - 1] (fun _ => (1 : ZMod 2)) + eFn n)
            = fun i => L (L^[j - 1] (fun _ => 1)) i + L (eFn n) i := L_add _ _
        rw [hLsplit, show (j + 1) - 1 = j by omega]
        congr 1
        · funext i
          conv_rhs => rw [show (j : ℕ) = j - 1 + 1 by omega, Function.iterate_succ_apply']
          show L (L^[j - 1] ((fun _ => (1 : ZMod 2)) : Fin n → ZMod 2)) i + L (eFn n) i + (0 + 1)
            = (L (L^[j - 1] ((fun _ => (1 : ZMod 2)) : Fin n → ZMod 2)) + eFn n) i
          rw [L_eFn, Pi.add_apply]
          show L (L^[j - 1] (fun _ => 1)) i + ((1 : ZMod 2) + eFn n i) + (0 + 1)
            = L (L^[j - 1] (fun _ => 1)) i + eFn n i
          rw [zero_add, add_assoc, one_add_one_cancel]
        · funext i
          show L (eFn n) i + 1 = eFn n i
          rw [L_eFn, Pi.add_apply]
          show (1 : ZMod 2) + eFn n i + 1 = eFn n i
          rw [add_assoc, ← add_left_comm (eFn n i) 1 1, one_add_one_zmod, add_zero]
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- A (n + n)
    show L^[n + n - 1] (fun _ => 1) = eFn (n + n)
    rw [show n + n - 1 = n - 1 + n by omega, hPB n (by omega : 1 ≤ n) (le_refl n), hA]
    have hee : eFn n + eFn n = (0 : Fin n → ZMod 2) := by
      funext i
      rw [Pi.add_apply, zadd_self]
      rfl
    rw [hee]
    funext i
    show cat (0 : Fin n → ZMod 2) (eFn n) i = eFn (n + n) i
    unfold cat eFn
    by_cases h : i.val < n
    · rw [dif_pos h, if_neg (by
        intro hc
        rw [Fin.ext_iff, lasti_val] at hc
        have := i.isLt
        omega)]
      rfl
    · rw [dif_neg h]
      by_cases h1 : i = lasti (n + n)
      · rw [if_pos h1, if_pos (by
          apply Fin.ext
          show i.val - n = (lasti n).val
          rw [lasti_val]
          rw [Fin.ext_iff, lasti_val] at h1
          have := i.isLt
          have hn' := NeZero.pos n
          omega)]
      · rw [if_neg h1, if_neg (by
          intro hc
          have hc' : i.val - n = n - 1 := Fin.ext_iff.mp hc
          apply h1
          rw [Fin.ext_iff, lasti_val]
          have := i.isLt
          have hn' := NeZero.pos n
          omega)]
  · -- B (n + n)
    intro M hM
    by_cases hMn : M ≤ n - 1
    · rw [hPA M hMn, tot_cat]
      exact zadd_self _
    · have hMr : n - 1 + (M - (n - 1)) = M := by omega
      have hj1 : 1 ≤ M - (n - 1) := by omega
      have hjn : M - (n - 1) ≤ n := by omega
      rw [← hMr, hPB _ hj1 hjn, tot_cat, tot_add,
        hB (M - (n - 1) - 1) (by omega : M - (n - 1) - 1 ≤ n - 2), tot_eFn,
        zero_add, one_add_one_zmod]
  · -- C (n + n)
    intro M hM
    by_cases hMn : M ≤ n - 1
    · rw [hPA M hMn]
      show cat (L^[M] (fun _ => 1)) (L^[M] (fun _ => 1)) (lasti (n + n)) = 1
      unfold cat
      rw [dif_neg (by rw [lasti_val]; have := NeZero.pos n; omega)]
      have hmk : (⟨(lasti (n + n)).val - n, by omega⟩ : Fin n) = lasti n := by
        apply Fin.ext
        show (lasti (n + n)).val - n = (lasti n).val
        rw [lasti_val, lasti_val]
        have := NeZero.pos n
        omega
      rw [hmk]
      exact hC M (by omega)
    · have hMr : n - 1 + (M - (n - 1)) = M := by omega
      have hj1 : 1 ≤ M - (n - 1) := by omega
      have hjn : M - (n - 1) ≤ n := by omega
      rw [← hMr, hPB _ hj1 hjn]
      show cat (L^[M - (n - 1) - 1] (fun _ => 1) + eFn n) (eFn n) (lasti (n + n)) = 1
      unfold cat
      rw [dif_neg (by rw [lasti_val]; have := NeZero.pos n; omega)]
      have hmk : (⟨(lasti (n + n)).val - n, by omega⟩ : Fin n) = lasti n := by
        apply Fin.ext
        show (lasti (n + n)).val - n = (lasti n).val
        rw [lasti_val, lasti_val]
        have := NeZero.pos n
        omega
      rw [hmk]
      exact eFn_lasti
  · -- D (n + n)
    intro M hM1 hM
    by_cases hMn : M ≤ n - 1
    · rw [hPA M hMn]
      show cat (L^[M] (fun _ => 1)) (L^[M] (fun _ => 1)) ⟨(n + n) - 2, by have := NeZero.pos n; omega⟩
          = 0
      unfold cat
      rw [dif_neg (by show ¬ ((n + n) - 2) < n; omega)]
      have hmk : (⟨(⟨(n + n) - 2, by have := NeZero.pos n; omega⟩ : Fin (n + n)).val - n,
          by omega⟩ : Fin n) = ⟨n - 2, by have := NeZero.pos n; omega⟩ := by
        apply Fin.ext
        show (n + n) - 2 - n = n - 2
        omega
      rw [hmk]
      exact hD M hM1 (by omega)
    · have hMr : n - 1 + (M - (n - 1)) = M := by omega
      have hj1 : 1 ≤ M - (n - 1) := by omega
      have hjn : M - (n - 1) ≤ n := by omega
      rw [← hMr, hPB _ hj1 hjn]
      show cat (L^[M - (n - 1) - 1] (fun _ => 1) + eFn n) (eFn n)
          ⟨(n + n) - 2, by have := NeZero.pos n; omega⟩ = 0
      unfold cat
      rw [dif_neg (by show ¬ ((n + n) - 2) < n; omega)]
      have hmk : (⟨(⟨(n + n) - 2, by have := NeZero.pos n; omega⟩ : Fin (n + n)).val - n,
          by omega⟩ : Fin n) = ⟨n - 2, by have := NeZero.pos n; omega⟩ := by
        apply Fin.ext
        show (n + n) - 2 - n = n - 2
        omega
      rw [hmk]
      show eFn n ⟨n - 2, by have := NeZero.pos n; omega⟩ = 0
      unfold eFn
      rw [if_neg (by
        intro hc
        have hc' : n - 2 = n - 1 := Fin.ext_iff.mp hc
        omega)]

theorem core (k : ℕ) (hk : 1 ≤ k) : ∀ (n : ℕ) [NeZero n], n = 2 ^ k → A n ∧ B n ∧ C n ∧ D n := by
  induction k with
  | zero => exact absurd hk (by decide)
  | succ k ih =>
    intro n hn2 hn
    cases k with
    | zero =>
      rw [pow_one] at hn
      subst hn
      exact base_case
    | succ k' =>
      have : NeZero (2 ^ (k' + 1)) := ⟨pow_ne_zero _ (by decide)⟩
      have ih2 := ih (by omega : 1 ≤ k' + 1) (2 ^ (k' + 1)) rfl
      have e : n = 2 ^ (k' + 1) + 2 ^ (k' + 1) := by rw [hn, pow_succ, mul_two]
      subst e
      exact stepLemma _ (by
        have h22 : (2 : ℕ) ^ 1 ≤ 2 ^ (k' + 1) := Nat.pow_le_pow_right (by decide) (by omega)
        rwa [pow_one] at h22) ih2.1 ih2.2.1 ih2.2.2.1 ih2.2.2.2

theorem last_lamp_only_of_two_pow (n k : ℕ) [NeZero n] (hk : 0 < k) (hn : n = 2 ^ k) :
    ∀ i : Fin n, lampsAfter n (n * (n - 1)) i = decide (i.val = n - 1) := by
  subst hn
  intro i
  have hA := (core k hk (2 ^ k) rfl).1
  show (step^[2 ^ k * (2 ^ k - 1)] (initial (2 ^ k))).1 i = decide (i.val = 2 ^ k - 1)
  have hgl : (step^[2 ^ k * (2 ^ k - 1)] (initial (2 ^ k))).1 i
      = z2b ((zstep^[2 ^ k * (2 ^ k - 1)] (zinit (2 ^ k))).1 i) :=
    congrFun (congrArg Prod.fst (glue _)) i
  rw [hgl, Function.iterate_mul, aux, hA]
  show z2b (eFn (2 ^ k) i) = decide (i.val = 2 ^ k - 1)
  unfold eFn
  by_cases hi : i = lasti (2 ^ k)
  · rw [if_pos hi, z2b_one]
    rw [Fin.ext_iff, lasti_val] at hi
    simp [hi]
  · rw [if_neg hi, z2b_zero]
    have hne : i.val ≠ 2 ^ k - 1 := by
      intro hc
      apply hi
      exact Fin.ext hc
    simp [hne]

/-! ### Part (c): `n = 2^k + 1`, only lamp 1 on after `n*(n-2)` steps -/

/-- State of the `n'+1`-lamp process of "shifted" form: lamp 0 off, lamp 1 on,
and lamps `2..n'` given by the vector `x` on `Fin n'`. -/
def cStateVec {n' : ℕ} [NeZero n'] (x : Fin n' → ZMod 2) : Fin (n' + 1) → ZMod 2 :=
  fun i => if i.val = 1 then 1
    else if h : 2 ≤ i.val then x ⟨i.val - 2, by have h2 := i.isLt; omega⟩ else 0

/-- One round of the `n'+1`-process maps a shifted state to the shifted state of `L x`,
provided `x`'s last-but-one lamp is off (so lamp 0 stays off) and `x`'s last lamp is on
(so lamp 2's wrap-around toggle matches lamp 0 of the `n'`-process). -/
lemma LcState {n' : ℕ} [NeZero n'] [NeZero (n' + 1)] (h2 : 2 ≤ n') (x : Fin n' → ZMod 2)
    (hα : x ⟨n' - 2, by have := NeZero.pos n'; omega⟩ = 0) (hβ : x (lasti n') = 1) :
    L (cStateVec x) = cStateVec (L x) := by
  funext p
  rw [L_apply]
  have hlast : cStateVec x (lasti (n' + 1)) = 0 := by
    show (if (lasti (n' + 1)).val = 1 then (1 : ZMod 2)
      else if h : 2 ≤ (lasti (n' + 1)).val then x ⟨(lasti (n' + 1)).val - 2, by omega⟩ else 0) = 0
    rw [if_neg (by show (n' : ℕ) ≠ 1; omega),
      dif_pos (by show (2 : ℕ) ≤ n'; omega)]
    have hmk : (⟨(lasti (n' + 1)).val - 2, by omega⟩ : Fin n')
        = ⟨n' - 2, by have := NeZero.pos n'; omega⟩ := by
      apply Fin.ext
      rfl
    rw [hmk, hα]
  rw [hlast, zero_add]
  have hf0 : cStateVec x ⟨0 % (n' + 1), Nat.mod_lt 0 (NeZero.pos _)⟩ = 0 := by
    have hmk : (⟨0 % (n' + 1), Nat.mod_lt 0 (NeZero.pos _)⟩ : Fin (n' + 1))
        = ⟨0, by omega⟩ := by
      apply Fin.ext
      show 0 % (n' + 1) = 0
      exact Nat.zero_mod _
    rw [hmk]
    show (if (0 : ℕ) = 1 then (1 : ZMod 2) else if h : 2 ≤ (0 : ℕ) then x ⟨0 - 2, by omega⟩ else 0) = 0
    rw [if_neg (by decide : ¬ (0 : ℕ) = 1), dif_neg (by decide : ¬ 2 ≤ (0 : ℕ))]
  have hf1 : cStateVec x ⟨1 % (n' + 1), Nat.mod_lt 1 (NeZero.pos _)⟩ = 1 := by
    have hmk : (⟨1 % (n' + 1), Nat.mod_lt 1 (NeZero.pos _)⟩ : Fin (n' + 1))
        = ⟨1, by omega⟩ := by
      apply Fin.ext
      show 1 % (n' + 1) = 1
      exact Nat.mod_eq_of_lt (by omega)
    rw [hmk]
    show (if (1 : ℕ) = 1 then (1 : ZMod 2) else if h : 2 ≤ (1 : ℕ) then x ⟨1 - 2, by omega⟩ else 0) = 1
    rw [if_pos rfl]
  show (∑ i ∈ Finset.range (p.val + 1), cStateVec x ⟨i % (n' + 1), Nat.mod_lt i (NeZero.pos _)⟩)
    = (if p.val = 1 then (1 : ZMod 2)
      else if h : 2 ≤ p.val then (L x) ⟨p.val - 2, by omega⟩ else 0)
  by_cases hp0 : p.val = 0
  · have hr : Finset.range (p.val + 1) = Finset.range 1 := by rw [hp0]
    rw [hr, Finset.sum_range_one, hf0, if_neg (by omega : ¬ p.val = 1),
      dif_neg (by omega : ¬ 2 ≤ p.val)]
  · by_cases hp1 : p.val = 1
    · have hr : Finset.range (p.val + 1) = Finset.range 2 := by rw [hp1]
      rw [hr, Finset.sum_range_succ, Finset.sum_range_one, hf0, hf1, if_pos hp1, zero_add]
    · have hp2 : 2 ≤ p.val := by omega
      rw [if_neg hp1, dif_pos hp2, L_apply]
      have hvv : (⟨p.val - 2, by omega⟩ : Fin n').val = p.val - 2 := rfl
      rw [hvv, show p.val - 2 + 1 = p.val - 1 by omega, hβ]
      have hsplit : (∑ i ∈ Finset.range (p.val + 1),
          cStateVec x ⟨i % (n' + 1), Nat.mod_lt i (NeZero.pos _)⟩)
          = cStateVec x ⟨0 % (n' + 1), Nat.mod_lt 0 (NeZero.pos _)⟩
            + cStateVec x ⟨1 % (n' + 1), Nat.mod_lt 1 (NeZero.pos _)⟩
            + ∑ j ∈ Finset.range (p.val - 1), x ⟨j % n', Nat.mod_lt j (NeZero.pos n')⟩ := by
        have h1 : Finset.range (p.val + 1) = Finset.Ico 0 (p.val + 1) :=
          Finset.range_eq_Ico (p.val + 1)
        rw [h1, ← Finset.sum_Ico_consecutive _ (Nat.zero_le 2) (by omega : 2 ≤ p.val + 1),
          ← Finset.range_eq_Ico, Finset.sum_Ico_eq_sum_range,
          Finset.sum_range_succ, Finset.sum_range_one]
        have hp1a : p.val + 1 - 2 = p.val - 1 := by omega
        rw [hp1a]
        have hconv : ∀ j ∈ Finset.range (p.val - 1),
            cStateVec x ⟨(2 + j) % (n' + 1), Nat.mod_lt (2 + j) (NeZero.pos _)⟩
              = x ⟨j % n', Nat.mod_lt j (NeZero.pos n')⟩ := by
          intro j hj
          rw [Finset.mem_range] at hj
          have hmk : (⟨(2 + j) % (n' + 1), Nat.mod_lt (2 + j) (NeZero.pos _)⟩ : Fin (n' + 1))
              = ⟨2 + j, by omega⟩ :=
            Fin.ext (Nat.mod_eq_of_lt (by omega))
          rw [hmk]
          show (if (2 + j : ℕ) = 1 then (1 : ZMod 2)
            else if h : 2 ≤ (2 + j : ℕ) then x ⟨(2 + j) - 2, by omega⟩ else 0)
            = x ⟨j % n', Nat.mod_lt j (NeZero.pos n')⟩
          rw [if_neg (by omega : ¬ (2 + j : ℕ) = 1), dif_pos (by omega : 2 ≤ 2 + j)]
          congr 1
          apply Fin.ext
          show 2 + j - 2 = j % n'
          rw [Nat.mod_eq_of_lt (by omega : j < n')]
          omega
        rw [Finset.sum_congr rfl hconv]
      rw [hsplit, hf0, hf1, zero_add]
/-- One round from the all-on state gives the alternating vector. -/
lemma L_one {n : ℕ} [NeZero n] :
    L ((fun _ => (1 : ZMod 2)) : Fin n → ZMod 2) = fun p => (p.val : ZMod 2) := by
  funext p
  rw [L_apply]
  have hbody : ∀ i ∈ Finset.range (p.val + 1),
      ((fun _ => (1 : ZMod 2)) : Fin n → ZMod 2) ⟨i % n, Nat.mod_lt i (NeZero.pos n)⟩ = 1 :=
    fun i _ => rfl
  rw [Finset.sum_congr rfl hbody, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  show (1 : ZMod 2) + ((p.val + 1 : ℕ) : ZMod 2) = (p.val : ZMod 2)
  rw [Nat.cast_succ, ← add_assoc, one_add_one_cancel]

/-- The round-level invariant of part (c): after `m` rounds (`1 ≤ m ≤ 2^k - 1`), the
`(2^k+1)`-process is in shifted form. -/
lemma invC (k : ℕ) (hk : 1 ≤ k) :
    ∀ m, 1 ≤ m → m ≤ 2 ^ k - 1 →
      L^[m] ((fun _ => (1 : ZMod 2)) : Fin (2 ^ k + 1) → ZMod 2)
        = cStateVec (L^[m] ((fun _ => (1 : ZMod 2)) : Fin (2 ^ k) → ZMod 2)) := by
  have : NeZero (2 ^ k) := ⟨pow_ne_zero _ (by decide)⟩
  have : NeZero (2 ^ k + 1) := ⟨ne_of_gt (by positivity)⟩
  have hcore := core k hk (2 ^ k) rfl
  have h22 : 2 ≤ 2 ^ k := by
    have h : (2 : ℕ) ^ 1 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) (by omega)
    rwa [pow_one] at h
  intro m
  induction m with
  | zero => intro h; omega
  | succ m ih =>
    intro h1 hm
    cases m with
    | zero =>
      show L^[1] ((fun _ => (1 : ZMod 2)) : Fin (2 ^ k + 1) → ZMod 2)
        = cStateVec (L^[1] ((fun _ => (1 : ZMod 2)) : Fin (2 ^ k) → ZMod 2))
      rw [Function.iterate_one, Function.iterate_one, L_one (n := 2 ^ k + 1), L_one (n := 2 ^ k)]
      funext i
      show ((i.val : ℕ) : ZMod 2)
        = (if i.val = 1 then (1 : ZMod 2)
          else if h : 2 ≤ i.val then (fun j : Fin (2 ^ k) => ((j.val : ℕ) : ZMod 2)) ⟨i.val - 2, by omega⟩
          else 0)
      by_cases h : i.val = 1
      · rw [if_pos h, h, Nat.cast_one]
      · by_cases h2 : 2 ≤ i.val
        · rw [if_neg h, dif_pos h2]
          show ((i.val : ℕ) : ZMod 2) = ((i.val - 2 : ℕ) : ZMod 2)
          have h4 : i.val - 2 + 2 = i.val := by omega
          have h5 := congrArg (fun a : ℕ => ((a : ℕ) : ZMod 2)) h4
          rw [Nat.cast_add] at h5
          have h6 : ((2 : ℕ) : ZMod 2) = 0 := ZMod.natCast_self 2
          rw [h6, add_zero] at h5
          exact h5.symm
        · rw [if_neg h, dif_neg h2, show i.val = 0 by omega, Nat.cast_zero]
    | succ m' =>
      have h1m : 1 ≤ m' + 1 := by omega
      have ih' := ih (by omega) (by omega)
      rw [show m' + 1 + 1 = (m' + 1) + 1 by omega, Function.iterate_succ_apply',
        Function.iterate_succ_apply' (L) (m' + 1) ((fun _ => (1 : ZMod 2)) : Fin (2 ^ k) → ZMod 2),
        ih']
      have hα : (L^[m' + 1] ((fun _ => (1 : ZMod 2)) : Fin (2 ^ k) → ZMod 2))
          ⟨2 ^ k - 2, by have := pow_pos (by decide : (0 : ℕ) < 2) k; omega⟩ = 0 :=
        hcore.2.2.2 (m' + 1) (by omega) (by omega)
      have hβ : (L^[m' + 1] ((fun _ => (1 : ZMod 2)) : Fin (2 ^ k) → ZMod 2)) (lasti (2 ^ k)) = 1 :=
        hcore.2.2.1 (m' + 1) (by omega)
      rw [LcState h22 _ hα hβ]

/-- The shifted state of `eFn (2^k)` is exactly "only lamp 1 on". -/
lemma cState_eFn (k : ℕ) (hk : 1 ≤ k) :
    cStateVec (eFn (2 ^ k)) = fun i => if i.val = 1 then (1 : ZMod 2) else 0 := by
  have : NeZero (2 ^ k) := ⟨pow_ne_zero _ (by decide)⟩
  have : NeZero (2 ^ k + 1) := ⟨ne_of_gt (by positivity)⟩
  have h22 : 2 ≤ 2 ^ k := by
    have h : (2 : ℕ) ^ 1 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) (by omega)
    rwa [pow_one] at h
  funext i
  show (if i.val = 1 then (1 : ZMod 2)
    else if h : 2 ≤ i.val then eFn (2 ^ k) ⟨i.val - 2, by omega⟩ else 0)
    = if i.val = 1 then (1 : ZMod 2) else 0
  by_cases h : i.val = 1
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]
    by_cases h2 : 2 ≤ i.val
    · rw [dif_pos h2]
      show (if (⟨i.val - 2, by omega⟩ : Fin (2 ^ k)) = lasti (2 ^ k) then (1 : ZMod 2) else 0) = 0
      rw [if_neg]
      intro hc
      have hc' : i.val - 2 = 2 ^ k - 1 := Fin.ext_iff.mp hc
      have hi := i.isLt
      omega
    · rw [dif_neg h2]

theorem lamp1_only_of_two_pow_add_one (n k : ℕ) [NeZero n] (hk : 0 < k) (hn : n = 2 ^ k + 1) :
    ∀ i : Fin n, lampsAfter n (n * (n - 2)) i = decide (i.val = 1) := by
  subst hn
  intro i
  have hk1 : 1 ≤ k := hk
  have hcore := core k hk1 (2 ^ k) rfl
  have h22 : 2 ≤ 2 ^ k := by
    have h : (2 : ℕ) ^ 1 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) (by omega)
    rwa [pow_one] at h
  have hinv := invC k hk1 (2 ^ k - 1) (by omega) (le_refl _)
  rw [hcore.1] at hinv
  show (step^[(2 ^ k + 1) * (2 ^ k + 1 - 2)] (initial (2 ^ k + 1))).1 i = decide (i.val = 1)
  have hgl : (step^[(2 ^ k + 1) * (2 ^ k + 1 - 2)] (initial (2 ^ k + 1))).1 i
      = z2b ((zstep^[(2 ^ k + 1) * (2 ^ k + 1 - 2)] (zinit (2 ^ k + 1))).1 i) :=
    congrFun (congrArg Prod.fst (glue _)) i
  rw [hgl, Function.iterate_mul, aux]
  have he : 2 ^ k + 1 - 2 = 2 ^ k - 1 := by omega
  rw [he, hinv, cState_eFn k hk1]
  show z2b (if i.val = 1 then (1 : ZMod 2) else 0) = decide (i.val = 1)
  by_cases hi : i.val = 1
  · rw [if_pos hi, z2b_one]
    simp [hi]
  · rw [if_neg hi, z2b_zero]
    simp [hi]


snip end

problem imo1993_p6_a (n : ℕ) [NeZero n] (hn : 1 < n) :
    ∃ M : ℕ, 0 < M ∧ ∀ i : Fin n, lampsAfter n M i = true := by
  obtain ⟨M, hMpos, hM⟩ := step_periodic n hn
  refine ⟨M, hMpos, fun i => ?_⟩
  show (step^[M] (initial n)).1 i = true
  rw [hM]

problem imo1993_p6_b (n k : ℕ) [NeZero n] (hn : n = 2 ^ k) (hk : 0 < k) :
    ∀ i : Fin n, lampsAfter n (n ^ 2 - 1) i = true := by
  have hn2 : 1 < n := by
    have h2 : (2 : ℕ) ≤ 2 ^ k :=
      calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    omega
  exact all_on_of_last_only hn2 (last_lamp_only_of_two_pow n k hk hn)

problem imo1993_p6_c (n k : ℕ) [NeZero n] (hn : n = 2 ^ k + 1) (hk : 0 < k) :
    ∀ i : Fin n, lampsAfter n (n ^ 2 - n + 1) i = true := by
  have hn2 : 2 < n := by
    have h2 : (2 : ℕ) ≤ 2 ^ k :=
      calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    omega
  exact all_on_of_lamp1_only hn2 (lamp1_only_of_two_pow_add_one n k hk hn)

end Imo1993P6
