/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Olympiad 2014, Problem 2

Let $n \ge 2$ be an integer. Consider an $n \times n$ chessboard consisting of
$n^2$ unit squares. A configuration of $n$ rooks on this board is *peaceful* if
every row and every column contains exactly one rook. Find the greatest positive
integer $k$ such that, for each peaceful configuration of $n$ rooks, there is a
$k \times k$ square which does not contain a rook on any of its $k^2$ unit
squares.
-/

namespace Imo2014P2

variable {n : ℕ}

/-- A peaceful configuration of `n` rooks is a permutation `σ`: the rook in
row `i` sits in column `σ i`. Such a configuration has a rook-free `k × k`
square if there is a block of `k` consecutive rows and `k` consecutive columns
(fitting on the board) containing no rook. -/
def HasEmptySquare (σ : Equiv.Perm (Fin n)) (k : ℕ) : Prop :=
  ∃ r c : ℕ, r + k ≤ n ∧ c + k ≤ n ∧
    ∀ i : Fin n, r ≤ (i : ℕ) → (i : ℕ) < r + k →
      ¬ (c ≤ (σ i : ℕ) ∧ (σ i : ℕ) < c + k)

snip begin

/-- An empty `k × k` square contains an empty `j × j` square whenever `j ≤ k`. -/
lemma hasEmptySquare_mono {σ : Equiv.Perm (Fin n)} {j k : ℕ}
    (hjk : j ≤ k) (h : HasEmptySquare σ k) : HasEmptySquare σ j := by
  obtain ⟨r, c, hr, hc, hempty⟩ := h
  exact ⟨r, c, by lia, by lia, fun i hri hir hmem ↦ hempty i hri (by lia) ⟨hmem.1, by lia⟩⟩

/-- `⌊√(n-1)⌋² < n ≤ (⌊√(n-1)⌋+1)²`. -/
lemma sqrt_bounds (hn : 2 ≤ n) :
    Nat.sqrt (n - 1) * Nat.sqrt (n - 1) < n ∧
      n ≤ (Nat.sqrt (n - 1) + 1) * (Nat.sqrt (n - 1) + 1) := by
  refine ⟨?_, ?_⟩
  · have := Nat.sqrt_le' (n - 1); lia
  · have := Nat.lt_succ_sqrt' (n - 1); lia

/-- Existence (lower bound): every peaceful configuration has an empty
`⌊√(n-1)⌋ × ⌊√(n-1)⌋` square.

Following Evan Chen: let `R` be the rook in the top row, in column `col₀`, and
stack `k` squares of size `k × k` directly below it. The `k` columns of that
stack contain `k` rooks in total, but `R`'s rook sits at row `0`, above the
stack — so the stack holds at most `k - 1` rooks among `k` disjoint squares,
and one of them is empty. -/
lemma exists_empty_square (hn : 2 ≤ n) (σ : Equiv.Perm (Fin n)) :
    HasEmptySquare σ (Nat.sqrt (n - 1)) := by
  set k := Nat.sqrt (n - 1) with hk_def
  have hk2 : k * k < n := by rw [hk_def]; exact (sqrt_bounds hn).1
  have hk1 : 1 ≤ k := by rw [hk_def]; exact Nat.le_sqrt.mpr (by lia)
  have h0 : 0 < n := by lia
  have hkn : k < n := by have h := Nat.mul_le_mul_left k hk1; omega
  -- `R` is the rook in the top row, at column `col₀`.
  set col0 : ℕ := (σ ⟨0, h0⟩ : ℕ) with hcol0
  have hcol0_lt : col0 < n := (σ ⟨0, h0⟩).isLt
  -- A window of `k` columns containing `col₀`.
  set c0 : ℕ := min col0 (n - k) with hc0_def
  have hc0_le : c0 ≤ n - k := min_le_right _ _
  have hc0k : c0 + k ≤ n := by lia
  have hmem0 : c0 ≤ col0 ∧ col0 < c0 + k := by
    refine ⟨min_le_left _ _, ?_⟩
    by_cases h : col0 ≤ n - k
    · have : c0 = col0 := min_eq_left h; lia
    · have : c0 = n - k := min_eq_right (le_of_lt (not_le.mp h)); lia
  set W : Finset ℕ := Finset.Ico c0 (c0 + k) with hW
  have hWcard : W.card = k := by rw [hW, Nat.card_Ico]; lia
  -- `P` = rows whose rook lies in the window; at most `k` of them.
  set P : Finset (Fin n) := Finset.univ.filter (fun i => (σ i : ℕ) ∈ W) with hP
  have hPcard : P.card ≤ k := by
    rw [← hWcard]
    apply Finset.card_le_card_of_injOn (fun i => (σ i : ℕ))
    · intro i hi
      rw [Finset.mem_coe, hP, Finset.mem_filter] at hi
      rw [Finset.mem_coe]
      exact hi.2
    · intro a _ b _ hab
      exact σ.injective (Fin.ext hab)
  by_contra hcontra
  -- If no empty square, every one of the `k` stacked squares has a rook.
  have hAll : ∀ t : Fin k, ∃ i : Fin n,
      (1 + t.val * k ≤ (i : ℕ) ∧ (i : ℕ) < 1 + t.val * k + k) ∧
      (c0 ≤ (σ i : ℕ) ∧ (σ i : ℕ) < c0 + k) := by
    intro t
    have hrk : 1 + t.val * k + k ≤ n := by
      have h : (t.val + 1) * k ≤ k * k := Nat.mul_le_mul_right k (Nat.succ_le_of_lt t.isLt)
      rw [add_one_mul] at h; omega
    by_contra hno
    exact hcontra ⟨1 + t.val * k, c0, hrk, hc0k,
      fun i hi1 hi2 hcc => hno ⟨i, ⟨hi1, hi2⟩, hcc⟩⟩
  choose g hg using hAll
  set z : Fin n := ⟨0, h0⟩ with hz
  have hz_mem : z ∈ P := by
    rw [hP, Finset.mem_filter, hW, Finset.mem_Ico]; exact ⟨Finset.mem_univ _, hmem0⟩
  have hg_mem : ∀ t, g t ∈ P := fun t => by
    rw [hP, Finset.mem_filter, hW, Finset.mem_Ico]; exact ⟨Finset.mem_univ _, (hg t).2⟩
  have hg_inj : Function.Injective g := by
    intro s t hst
    have hval : (g s : ℕ) = (g t : ℕ) := congrArg Fin.val hst
    apply Fin.ext
    have hle1 : s.val * k < (t.val + 1) * k := by
      have : 1 + s.val * k < 1 + (t.val + 1) * k :=
        calc 1 + s.val * k ≤ (g s : ℕ) := (hg s).1.1
          _ = (g t : ℕ) := hval
          _ < 1 + t.val * k + k := (hg t).1.2
          _ = 1 + (t.val + 1) * k := by ring
      lia
    have hle2 : t.val * k < (s.val + 1) * k := by
      have : 1 + t.val * k < 1 + (s.val + 1) * k :=
        calc 1 + t.val * k ≤ (g t : ℕ) := (hg t).1.1
          _ = (g s : ℕ) := hval.symm
          _ < 1 + s.val * k + k := (hg s).1.2
          _ = 1 + (s.val + 1) * k := by ring
      lia
    have := Nat.lt_of_mul_lt_mul_right hle1
    have := Nat.lt_of_mul_lt_mul_right hle2
    lia
  -- But then `P` contains the `k` distinct rows `g t` plus row `0`: at least `k+1`.
  have hnotmem : z ∉ Finset.image g Finset.univ := by
    rw [Finset.mem_image]
    rintro ⟨t, -, ht⟩
    have h1 : 1 + t.val * k ≤ (g t : ℕ) := (hg t).1.1
    have h2 : (g t : ℕ) = 0 := by rw [ht]
    rw [h2] at h1
    omega
  have hsub : insert z (Finset.image g Finset.univ) ⊆ P := by
    intro x hx
    rw [Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · exact hz_mem
    · rw [Finset.mem_image] at hx
      obtain ⟨t, -, rfl⟩ := hx
      exact hg_mem t
  have : k + 1 ≤ P.card :=
    calc k + 1 = (Finset.image g Finset.univ).card + 1 := by
              rw [Finset.card_image_of_injective _ hg_inj, Finset.card_univ, Fintype.card_fin]
      _ = (insert z (Finset.image g Finset.univ)).card :=
            (Finset.card_insert_of_notMem hnotmem).symm
      _ ≤ P.card := Finset.card_le_card hsub
  lia

/-- `σ` places a rook in every axis-aligned `K × K` square — exactly the
negation of `HasEmptySquare`. -/
def HasRook {m : ℕ} (σ : Equiv.Perm (Fin m)) (K : ℕ) : Prop :=
  ∀ r c, r + K ≤ m → c + K ≤ m →
    ∃ i : Fin m, r ≤ (i : ℕ) ∧ (i : ℕ) < r + K ∧ c ≤ (σ i : ℕ) ∧ (σ i : ℕ) < c + K

/-- Restriction reduction: a rook-covering configuration on an `M × M` board
restricts (top-left, then completed arbitrarily) to one on any smaller `N × N`
board. The key point: every `K × K` square of the `N × N` board lies inside
`[0,N)²`, so its witnessing rook already has both coordinates `< N` and survives
the restriction; the arbitrary completion only adds rooks. -/
lemma covering_restrict {K M N : ℕ} (hNM : N ≤ M)
    (τ : Equiv.Perm (Fin M)) (hτ : HasRook τ K) :
    ∃ σ : Equiv.Perm (Fin N), HasRook σ K := by
  classical
  set f : Fin N → Fin N := fun i =>
    if h : ((τ (Fin.castLE hNM i)) : ℕ) < N then ⟨(τ (Fin.castLE hNM i)), h⟩ else i with hf_def
  set good : Set (Fin N) := {i | ((τ (Fin.castLE hNM i)) : ℕ) < N} with hgood_def
  have hfinj : Set.InjOn f good := by
    intro a ha b hb hab
    have ha' : ((τ (Fin.castLE hNM a)) : ℕ) < N := by simpa [hgood_def] using ha
    have hb' : ((τ (Fin.castLE hNM b)) : ℕ) < N := by simpa [hgood_def] using hb
    have hval : ((τ (Fin.castLE hNM a)) : ℕ) = (τ (Fin.castLE hNM b) : ℕ) := by
      simpa [hf_def, ha', hb'] using congrArg Fin.val hab
    exact Fin.castLE_injective hNM (τ.injective (Fin.ext hval))
  have hmaps : good.MapsTo f (Finset.univ : Finset (Fin N)) := by
    intro i hi
    simp
  obtain ⟨g, hg⟩ := Set.MapsTo.exists_equiv_extend_of_card_eq
    (α := Fin N) (β := Fin N) (t := (Finset.univ : Finset (Fin N)))
    (s := good) (f := f) (by simp) hmaps hfinj
  let eUniv : ↑(Finset.univ : Finset (Fin N)) ≃ Fin N :=
    Equiv.ofBijective (fun x => (x : Fin N))
      ⟨Subtype.val_injective, fun y => ⟨⟨y, by simp⟩, rfl⟩⟩
  let σ : Equiv.Perm (Fin N) := g.trans eUniv
  refine ⟨σ, ?_⟩
  intro r c hr hc
  obtain ⟨i, hi1, hi2, hc1, hc2⟩ := hτ r c (le_trans hr hNM) (le_trans hc hNM)
  have hiN : (i : ℕ) < N := lt_of_lt_of_le hi2 hr
  have hcastle : Fin.castLE hNM ⟨i, hiN⟩ = i := by apply Fin.ext; simp
  have hi_good : (⟨i, hiN⟩ : Fin N) ∈ good := by
    rw [hgood_def]
    change ((τ (Fin.castLE hNM ⟨i, hiN⟩)) : ℕ) < N
    rw [hcastle]
    omega
  refine ⟨⟨i, hiN⟩, hi1, hi2, ?_, ?_⟩ <;>
  · have hval : (σ ⟨i, hiN⟩ : ℕ) = (τ i : ℕ) := by
      have hσf : σ ⟨i, hiN⟩ = f ⟨i, hiN⟩ := by
        simpa [σ, eUniv] using hg ⟨i, hiN⟩ hi_good
      rw [hσf]
      simp only [hf_def]
      rw [dif_pos (by rw [hcastle]; exact lt_of_lt_of_le hc2 hc)]
      simp [hcastle]
    rw [hval]
    first | exact hc1 | exact hc2

/-- Base case of the construction: the grid-transpose `i ↦ K·(i % K) + i / K` is
a permutation of the `K² × K²` board placing a rook in every `K × K` square. -/
lemma transpose_covering (K : ℕ) (hK : 1 ≤ K) :
    ∃ τ : Equiv.Perm (Fin (K * K)), HasRook τ K := by
  have hKpos : 0 < K := hK
  have hdiv : ∀ i : Fin (K * K), i.val / K < K := fun i =>
    (Nat.div_lt_iff_lt_mul hKpos).mpr i.isLt
  have hbound : ∀ i : Fin (K * K), K * (i.val % K) + (i.val / K) < K * K := by
    intro i
    have h1 : i.val % K < K := Nat.mod_lt _ hKpos
    exact Nat.mul_add_lt_mul_of_lt_of_lt h1 (hdiv i)
  -- the grid-transpose `t`, an involution
  set t : Fin (K * K) → Fin (K * K) := fun i => ⟨K * (i.val % K) + (i.val / K), hbound i⟩
    with ht_def
  have htval : ∀ i : Fin (K * K), (t i).val = K * (i.val % K) + (i.val / K) := fun _ => rfl
  have hinvol : Function.Involutive t := by
    intro i
    apply Fin.ext
    rw [htval (t i), htval i, Nat.mul_add_mod, Nat.mod_eq_of_lt (hdiv i),
        Nat.mul_add_div hKpos, Nat.div_eq_of_lt (hdiv i), Nat.add_zero]
    exact Nat.div_add_mod i.val K
  refine ⟨⟨t, t, hinvol, hinvol⟩, ?_⟩
  intro r c hr hc
  obtain ⟨ra, rb, hr_eq, hrb⟩ : ∃ ra rb, r = K * ra + rb ∧ rb < K :=
    ⟨r / K, r % K, (Nat.div_add_mod r K).symm, Nat.mod_lt _ hKpos⟩
  obtain ⟨ca, cb, hc_eq, hcb⟩ : ∃ ca cb, c = K * ca + cb ∧ cb < K :=
    ⟨c / K, c % K, (Nat.div_add_mod c K).symm, Nat.mod_lt _ hKpos⟩
  have hra : ra < K := by
    have h : K * (ra + 1) ≤ K * K := by rw [Nat.mul_succ]; omega
    have := Nat.le_of_mul_le_mul_left h hKpos; omega
  have hca : ca < K := by
    have h : K * (ca + 1) ≤ K * K := by rw [Nat.mul_succ]; omega
    have := Nat.le_of_mul_le_mul_left h hKpos; omega
  have hexpR : K * (ra + 1) = K * ra + K := by ring
  have hexpC : K * (ca + 1) = K * ca + K := by ring
  -- it suffices to find the row/column offsets `a, b` of a rook in the square
  suffices h : ∃ a b : ℕ, (r ≤ K * a + b ∧ K * a + b < r + K) ∧
      (c ≤ K * b + a ∧ K * b + a < c + K) ∧ b < K by
    obtain ⟨a, b, ⟨hrow1, hrow2⟩, ⟨hcol1, hcol2⟩, hbK⟩ := h
    have hboundi : K * a + b < K * K := lt_of_lt_of_le hrow2 hr
    have hcolval : (t ⟨K * a + b, hboundi⟩).val = K * b + a := by
      rw [htval, Nat.mul_add_mod, Nat.mod_eq_of_lt hbK, Nat.mul_add_div hKpos,
          Nat.div_eq_of_lt hbK, Nat.add_zero]
    refine ⟨⟨K * a + b, hboundi⟩, hrow1, hrow2, ?_, ?_⟩
    · show c ≤ (t ⟨K * a + b, hboundi⟩).val
      rw [hcolval]; exact hcol1
    · show (t ⟨K * a + b, hboundi⟩).val < c + K
      rw [hcolval]; exact hcol2
  -- choose `(a,b)` by how the column window straddles the residue blocks
  by_cases h1 : cb ≤ ra
  · by_cases h2 : rb ≤ ca
    · exact ⟨ra, ca, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩, hca⟩
    · have hrow2 : K * (ra + 1) + ca < r + K := by rw [hexpR]; omega
      have hh : K * (ra + 1) < K * K := by have := lt_of_lt_of_le hrow2 hr; omega
      have haK : ra + 1 < K := Nat.lt_of_mul_lt_mul_left hh
      exact ⟨ra + 1, ca, ⟨by omega, hrow2⟩, ⟨by omega, by omega⟩, hca⟩
  · by_cases h2 : rb ≤ ca
    · have hcol2 : K * (ca + 1) + ra < c + K := by rw [hexpC]; omega
      have hh : K * (ca + 1) < K * K := by have := lt_of_lt_of_le hcol2 hc; omega
      have hbK : ca + 1 < K := Nat.lt_of_mul_lt_mul_left hh
      exact ⟨ra, ca + 1, ⟨by omega, by omega⟩, ⟨by omega, hcol2⟩, hbK⟩
    · by_cases h3 : rb ≤ ca + 1
      · exact ⟨ra, ca + 1, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩, by omega⟩
      · by_cases h4 : cb ≤ ra + 1
        · exact ⟨ra + 1, ca, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩, hca⟩
        · exact ⟨ra + 1, ca + 1, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩, by omega⟩

/-- Optimality (upper bound): some peaceful configuration has no empty
`(⌊√(n-1)⌋+1) × (⌊√(n-1)⌋+1)` square. -/
lemma exists_config_no_square (hn : 2 ≤ n) :
    ∃ σ : Equiv.Perm (Fin n), ¬ HasEmptySquare σ (Nat.sqrt (n - 1) + 1) := by
  set K := Nat.sqrt (n - 1) + 1 with hK_def
  have hK1 : 1 ≤ K := by rw [hK_def]; omega
  have hnKK : n ≤ K * K := by rw [hK_def]; exact (sqrt_bounds hn).2
  obtain ⟨τ, hτ⟩ := transpose_covering K hK1
  obtain ⟨σ, hσ⟩ := covering_restrict hnKK τ hτ
  refine ⟨σ, ?_⟩
  rintro ⟨r, c, hr, hc, hempty⟩
  obtain ⟨i, hi1, hi2, hc1, hc2⟩ := hσ r c hr hc
  exact hempty i hi1 hi2 ⟨hc1, hc2⟩

snip end

determine greatestK : ℕ → ℕ := fun n ↦ Nat.sqrt (n - 1)

problem imo2014_p2 (n : ℕ) (hn : 2 ≤ n) :
    IsGreatest {k : ℕ | ∀ σ : Equiv.Perm (Fin n), HasEmptySquare σ k} (greatestK n) := by
  constructor
  · -- `⌊√(n-1)⌋` works: every configuration has an empty square of that size.
    intro σ
    exact exists_empty_square hn σ
  · -- and no larger `k` works, by shrinking a hypothetical empty square down to
    -- size `⌊√(n-1)⌋+1`, which the optimal configuration rules out.
    intro k' hk'
    show k' ≤ Nat.sqrt (n - 1)
    by_contra hcon
    obtain ⟨σ, hσ⟩ := exists_config_no_square hn
    exact hσ (hasEmptySquare_mono (by lia) (hk' σ))

end Imo2014P2
