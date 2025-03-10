import Mathlib

set_option linter.unusedVariables.analyzeTactics true

lemma aux_1
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n)) :
  ∀ (n : ℕ) (x : NNReal), 0 < n ∧ 0 < x → 0 < f n x := by
  intros n x hp
  have hz₇: n ≤ 7 ∨ 7 < n := by
    exact le_or_lt n 7
  cases' hp with hn₀ hx₀
  by_cases hn₁: 1 < n
  . refine Nat.le_induction ?_ ?_ n hn₁
    . rw [h₁ 1 x (by norm_num)]
      rw [h₀ x]
      refine mul_pos hx₀ ?_
      refine add_pos hx₀ (by norm_num)
    . intros m hm₀ hm₁
      rw [h₁ m x (by linarith)]
      refine mul_pos hm₁ ?_
      refine add_pos hm₁ ?_
      refine one_div_pos.mpr ?_
      norm_cast
      exact Nat.zero_lt_of_lt hm₀
  . interval_cases n
    rw [h₀ x]
    exact hx₀


lemma aux_2
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (h₂ : ∀ (n : ℕ) (x : NNReal), 0 < n ∧ 0 < x → 0 < f n x)
  (h₃ : ∀ (n : ℕ) (x : NNReal), 0 < n → 0 ≤ f n x) :
  ∀ (n : ℕ) (x y : NNReal), 0 < n → x < y → f n x < f n y := by
  intros n x y hn hxy
  by_cases hn₁: 1 < n
  . refine Nat.le_induction ?_ ?_ n hn₁
    . rw [h₁ 1 x (by norm_num)]
      rw [h₁ 1 y (by norm_num)]
      norm_num
      refine mul_lt_mul ?_ ?_ ?_ ?_
      . rw [h₀ x, h₀ y]
        exact hxy
      . refine _root_.add_le_add ?_ (by norm_num)
        rw [h₀ x, h₀ y]
        exact le_of_lt hxy
      . refine add_pos_of_nonneg_of_pos ?_ (by linarith)
        rw [h₀ x]
        exact NNReal.zero_le_coe
      . refine le_of_lt ?_
        refine h₂ 1 y ?_
        norm_num
        exact pos_of_gt hxy
    . intros m hm₀ hm₁
      rw [h₁ m x (by linarith)]
      rw [h₁ m y (by linarith)]
      refine mul_lt_mul hm₁ ?_ ?_ ?_
      . refine _root_.add_le_add ?_ (by norm_num)
        exact le_of_lt hm₁
      . refine add_pos_of_nonneg_of_pos ?_ ?_
        . exact h₃ m x (by linarith)
        . refine one_div_pos.mpr ?_
          norm_cast
          exact Nat.zero_lt_of_lt hm₀
      . refine le_of_lt ?_
        refine h₂ m y ?_
        constructor
        . exact Nat.zero_lt_of_lt hm₀
        . exact pos_of_gt hxy
  . interval_cases n
    rw [h₀ x, h₀ y]
    exact hxy


lemma aux_3
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (h₄ : ∀ (n : ℕ) (x y : NNReal), 0 < n → x < y → f n x < f n y) :
  ∀ (n : ℕ) (x : NNReal), 1 < n ∧ 1 ≤ x → 1 < f n x := by
  intros n x hx₀
  cases' hx₀ with hn₀ hx₁
  have g₂₀: f n 1 ≤ f n x := by
    by_cases hx₂: 1 < x
    . refine le_of_lt ?_
      refine h₄ n 1 x ?_ hx₂
      exact Nat.zero_lt_of_lt hn₀
    . push_neg at hx₂
      have hx₃: x = 1 := by exact le_antisymm hx₂ hx₁
      rw [hx₃]
  have g₂₁: f 1 1 < f n 1 := by
    rw [h₀]
    refine Nat.le_induction ?_ ?_ n hn₀
    . rw [h₁ 1 1 (by norm_num), h₀]
      norm_num
    . intros m hm₀ hm₁
      rw [h₁ m 1 (by linarith)]
      refine one_lt_mul_of_lt_of_le hm₁ ?_
      nth_rw 1 [← add_zero 1]
      refine add_le_add ?_ ?_
      . exact le_of_lt hm₁
      . refine one_div_nonneg.mpr ?_
        exact Nat.cast_nonneg' m
  refine lt_of_lt_of_le ?_ g₂₀
  exact (lt_iff_lt_of_cmp_eq_cmp (congrFun (congrArg cmp (h₀ 1)) (f n 1))).mp g₂₁


lemma aux_4
  (f : ℕ → NNReal → ℝ)
  (h₃ : ∀ (n : ℕ) (x : NNReal), 0 < n → 0 ≤ f n x)
  (h₄ : ∀ (n : ℕ) (x y : NNReal), 0 < n → x < y → f n x < f n y)
  (f₀ : ℕ → NNReal → NNReal)
  (hf₀ : f₀ = fun n x => (f n x).toNNReal) :
  ∀ (n : ℕ), 0 < n → StrictMono (f₀ n) := by
  intros n hn₀
  refine Monotone.strictMono_of_injective ?_ ?_
  . refine monotone_iff_forall_lt.mpr ?_
    intros a b hab
    refine le_of_lt ?_
    rw [hf₀]
    exact (Real.toNNReal_lt_toNNReal_iff_of_nonneg (h₃ n a hn₀)).mpr (h₄ n a b hn₀ hab)
  . intros p q hpq
    contrapose! hpq
    apply lt_or_gt_of_ne at hpq
    cases' hpq with hpq hpq
    . refine ne_of_lt ?_
      rw [hf₀]
      exact (Real.toNNReal_lt_toNNReal_iff_of_nonneg (h₃ n p hn₀)).mpr (h₄ n p q hn₀ hpq)
    . symm
      refine ne_of_lt ?_
      rw [hf₀]
      exact (Real.toNNReal_lt_toNNReal_iff_of_nonneg (h₃ n q hn₀)).mpr (h₄ n q p hn₀ hpq)


lemma aux_5
  (f : ℕ → NNReal → ℝ)
  (hmo₁ : ∀ (n : ℕ), 0 < n → Function.Injective (f n))
  (f₀ : ℕ → NNReal → NNReal)
  (hmo₂ : ∀ (n : ℕ), 0 < n → StrictMono (f₀ n))
  (fi : ℕ → NNReal → NNReal)
  (hfi : fi = fun n => Function.invFun (f₀ n)):
  ∀ (n : ℕ) (x y : NNReal), 0 < n → f₀ n x = y → fi n y = x := by
  intros n x y hn₀ hn₁
  have hf₃: ∀ n y, fi n y = Function.invFun (f₀ n) y := by
    exact fun n y => congrFun (congrFun hfi n) y
  rw [← hn₁, hf₃]
  have hmo₃: ∀ n, 0 < n → Function.Injective (f₀ n) := by
    exact fun n a => StrictMono.injective (hmo₂ n a)
  have hn₂: (Function.invFun (f₀ n)) ∘ (f₀ n) = id := by exact Function.invFun_comp (hmo₃ n hn₀)
  rw [Function.comp_def (Function.invFun (f₀ n)) (f₀ n)] at hn₂
  have hn₃: (fun x => Function.invFun (f₀ n) (f₀ n x)) x = id x := by exact Eq.symm (NNReal.eq (congrArg NNReal.toReal (congrFun (id (Eq.symm hn₂)) x)))
  exact hmo₁ n hn₀ (congrArg (f n) hn₃)


lemma aux_6
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (f₀ : ℕ → NNReal → NNReal)
  (hf₀ : f₀ = fun n x => (f n x).toNNReal) :
  ∀ (n : ℕ), 0 < n → Continuous (f₀ n) := by
  intros n hn₀
  rw [hf₀]
  refine Continuous.comp' ?_ ?_
  . exact continuous_real_toNNReal
  . refine Nat.le_induction ?_ ?_ n hn₀
    . have hn₁: f 1 = fun (x:NNReal) => (x:ℝ) := by exact (Set.eqOn_univ (f 1) fun x => ↑x).mp fun ⦃x⦄ _ => h₀ x
      rw [hn₁]
      exact NNReal.continuous_coe
    . intros d hd₀ hd₁
      have hd₂: f (d + 1) = fun x => f d x * (f d x + 1 / ↑d) := by
        exact (Set.eqOn_univ (f (d + 1)) fun x => f d x * (f d x + 1 / ↑d)).mp fun ⦃x⦄ _ => h₁ d x hd₀
      rw [hd₂]
      refine Continuous.mul hd₁ ?_
      refine Continuous.add hd₁ ?_
      exact continuous_const


lemma aux_7
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (h₃ : ∀ (n : ℕ) (x : NNReal), 0 < n → 0 ≤ f n x)
  (h₅ : ∀ (n : ℕ) (x : NNReal), 1 < n ∧ 1 ≤ x → 1 < f n x)
  (f₀ : ℕ → NNReal → NNReal)
  (hf₂ : ∀ (n : ℕ) (x : NNReal), 0 < n → f₀ n x = (f n x).toNNReal)
  (hmo₂ : ∀ (n : ℕ), 0 < n → StrictMono (f₀ n))
  (hmo₄ : ∀ (n : ℕ), 0 < n → Continuous (f₀ n)) :
  ∀ (n : ℕ), 0 < n → Function.Surjective (f₀ n) := by
  intros n hn₀
  refine Continuous.surjective (hmo₄ n hn₀) ?_ ?_
  . refine Monotone.tendsto_atTop_atTop ?_ ?_
    . exact StrictMono.monotone (hmo₂ n hn₀)
    . intro b
      use (b + 1)
      refine Nat.le_induction ?_ ?_ n hn₀
      . rw [hf₂ 1 (b + 1) (by linarith), h₀]
        simp
      . intros d hd₀ hd₁
        rw [hf₂ (d + 1) (b + 1) (by linarith), h₁ d (b + 1) (by linarith)]
        have hd₂: b ≤ f d (b + 1) := by
          rw [hf₂ d (b + 1) (by linarith)] at hd₁
          exact (Real.le_toNNReal_iff_coe_le (h₃ d (b + 1) hd₀)).mp hd₁
        have hd₃: 1 < (f d (b + 1) + 1 / ↑d) := by
          by_cases hd₄: 1 < d
          . refine lt_add_of_lt_of_pos ?_ ?_
            . refine h₅ d (b + 1) ?_
              constructor
              . exact hd₄
              . exact le_add_self
            . refine div_pos (by linarith) ?_
              exact Nat.cast_pos'.mpr hd₀
          . have hd₅: d = 1 := by linarith
            rw [hd₅, h₀]
            simp
            norm_cast
            refine add_pos_of_nonneg_of_pos ?_ ?_
            . exact _root_.zero_le b
            . exact zero_lt_one' NNReal
        refine NNReal.le_toNNReal_of_coe_le ?_
        nth_rw 1 [← mul_one (↑b:ℝ)]
        refine mul_le_mul hd₂ (le_of_lt hd₃) (by linarith) ?_
        exact h₃ d (b + 1) hd₀
  . refine Filter.tendsto_atBot_atBot.mpr ?_
    intro b
    use 0
    intro a ha₀
    have ha₁: a = 0 := by exact nonpos_iff_eq_zero.mp ha₀
    have ha₂: f₀ n 0 = 0 := by
      refine Nat.le_induction ?_ ?_ n hn₀
      . rw [hf₂ 1 0 (by linarith), h₀]
        exact Real.toNNReal_coe
      . intros d hd₀ hd₁
        rw [hf₂ (d + 1) 0 (by linarith), h₁ d 0 (by linarith)]
        have hd₂: 0 ≤ f d 0 := by exact h₃ d 0 hd₀
        have hd₃: f d 0 = 0 := by
          rw [hf₂ d 0 (by linarith)] at hd₁
          apply Real.toNNReal_eq_zero.mp at hd₁
          exact eq_of_le_of_le hd₁ hd₂
        rw [hd₃, zero_mul]
        exact Real.toNNReal_zero
    rw [ha₁, ha₂]
    exact _root_.zero_le b


lemma aux_8
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (hmo₀ : ∀ (n : ℕ), 0 < n → StrictMono (f n))
  (hmo₁ : ∀ (n : ℕ), 0 < n → Function.Injective (f n))
  (f₀ : ℕ → NNReal → NNReal)
  (hf₂ : ∀ (n : ℕ) (x : NNReal), 0 < n → f₀ n x = (f n x).toNNReal)
  (sn : Set ℕ)
  (fb : ↑sn → NNReal)
  (hsn₁ : ∀ (n : ↑sn), ↑n ∈ sn ∧ 0 < n.1)
  (hfb₁ : ∀ (n : ↑sn), f₀ (↑n) (fb n) = 1 - 1 / ↑↑n) :
  ∀ (n : ↑sn), fb n < 1 := by
  intros n
  have hn₀: 0 < (n:ℕ) := by exact (hsn₁ n).2
  let z := fb n
  have hz₀: z = fb n := by rfl
  rw [← hz₀]
  by_contra! hc₀
  have hc₁: 1 ≤ f n z := by
    by_cases hn₁: 1 < (n:ℕ)
    . refine le_of_lt ?_
      refine aux_3 f h₀ h₁ ?_ (↑n) z ?_
      . exact fun n x y a a_1 => hmo₀ n a a_1
      . exact ⟨hn₁, hc₀⟩
    . have hn₂: (n:ℕ) = 1 := by linarith
      rw [hn₂, h₀]
      exact hc₀
  have hz₁: f₀ n z = 1 - 1 / n := by
    exact hfb₁ n
  have hz₃: f n z = 1 - 1 / n := by
    rw [hf₂ n z hn₀] at hz₁
    by_cases hn₁: 1 < (n:ℕ)
    . have hz₂: 1 - 1 / (n:NNReal) ≠ 0 := by
        have g₀: (n:NNReal) ≠ 0 := by
          norm_cast
          linarith
        nth_rw 1 [← div_self g₀, ← NNReal.sub_div]
        refine div_ne_zero ?_ g₀
        norm_cast
        exact Nat.sub_ne_zero_iff_lt.mpr hn₁
      apply (Real.toNNReal_eq_iff_eq_coe hz₂).mp at hz₁
      rw [hz₁]
      exact Eq.symm ((fun {r} {p:NNReal} hp => (Real.toNNReal_eq_iff_eq_coe hp).mp) hz₂ (hmo₁ n hn₀ rfl))
    . have hn₂: (n:ℕ) = 1 := by linarith
      rw [hn₂, h₀] at hz₁
      simp at hz₁
      rw [hn₂, h₀, hz₁]
      simp
  rw [hz₃] at hc₁
  have hz₄: 0 < 1 / (n:ℝ) := by
    refine div_pos (by linarith) ?_
    exact Nat.cast_pos'.mpr hn₀
  linarith


lemma aux_9
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (f₀ : ℕ → NNReal → NNReal)
  (hf₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f n x = ↑(f₀ n x))
  (hf₂ : ∀ (n : ℕ) (x : NNReal), 0 < n → f₀ n x = (f n x).toNNReal)
  (hmo₂ : ∀ (n : ℕ), 0 < n → StrictMono (f₀ n))
  (fi : ℕ → NNReal → NNReal)
  (hf₅ : ∀ (x : NNReal), fi 1 x = x)
  (hmo₇ : ∀ (n : ℕ), 0 < n → Function.RightInverse (fi n) (f₀ n))
  (hf₇ : ∀ (n : ℕ) (x y : NNReal), 0 < n → (f₀ n x = y ↔ fi n y = x))
  (fb : ℕ → NNReal)
  (hfb₀ : fb = fun n => fi n (1 - 1 / ↑n))
  (sn : Set ℕ)
  (hsn : sn = Set.Ici 1) :
  StrictMonoOn fb sn := by
  rw [hsn]
  refine strictMonoOn_Ici_of_pred_lt ?hψ
  intros m hm₀
  rw [hfb₀]
  refine Nat.le_induction ?_ ?_ m hm₀
  . have g₁: fi 1 0 = 0 := by exact hf₅ 0
    have g₂: (2:NNReal).IsConjExponent (2:NNReal) := by
      refine (NNReal.isConjExponent_iff_eq_conjExponent ?_).mpr ?_
      . exact one_lt_two
      . norm_cast
        simp
    simp
    norm_cast
    rw [g₁, NNReal.IsConjExponent.one_sub_inv g₂]
    let x := fi 2 2⁻¹
    have hx₀: x = fi 2 2⁻¹ := by rfl
    have hx₁: f₀ 2 x = 2⁻¹ := by
      rw [hx₀]
      have g₃: Function.RightInverse (fi 2) (f₀ 2) := by exact hmo₇ 2 (by linarith)
      exact g₃ 2⁻¹
    rw [← hx₀]
    contrapose! hx₁
    have hc₁: x = 0 := by exact nonpos_iff_eq_zero.mp hx₁
    have hc₃: f₀ 2 x = 0 := by
      rw [hc₁, hf₂ 2 0 (by linarith), h₁ 1 0 (by linarith), h₀ 0]
      norm_cast
      rw [zero_mul]
      exact Real.toNNReal_zero
    rw [hc₃]
    exact Ne.symm (NNReal.IsConjExponent.inv_ne_zero g₂)
  . simp
    intros n hn₀ _
    let i := fi n (1 - (↑n)⁻¹)
    let j := fi (n + 1) (1 - ((↑n:NNReal) + 1)⁻¹)
    have hi₀: i = fi n (1 - (↑n)⁻¹) := by rfl
    have hj₀: j = fi (n + 1) (1 - ((↑n:NNReal) + 1)⁻¹) := by rfl
    have hi₁: f₀ n i = (1 - (↑n)⁻¹) := by exact (hf₇ n i (1 - (↑n:NNReal)⁻¹) (by linarith)).mpr hi₀.symm
    have hj₁: f₀ (n + 1) j = (1 - ((↑n:NNReal) + 1)⁻¹) := by
      exact (hf₇ (n + 1) j _ (by linarith)).mpr hj₀.symm
    have hj₂: (1 - ((↑n:NNReal) + 1)⁻¹) = (1 - ((n:ℝ) + 1)⁻¹).toNNReal := by
      exact rfl
    have hn₂: f₀ (n + 1) i < f₀ (n + 1) j := by
      rw [hj₁, hj₂, hf₂ (n + 1) _ (by linarith), h₁ n i (by linarith)]
      rw [hf₁ n i (by linarith), hi₁]
      refine (Real.toNNReal_lt_toNNReal_iff ?_).mpr ?_
      . refine sub_pos.mpr ?_
        refine inv_lt_one_of_one_lt₀ ?_
        norm_cast
        exact Nat.lt_add_right 1 hn₀
      . have g₀: (↑n:NNReal)⁻¹ ≤ 1 := by exact Nat.cast_inv_le_one n
        rw [NNReal.coe_sub g₀, NNReal.coe_inv]
        simp
        refine inv_strictAnti₀ ?_ ?_
        . norm_cast
          exact Nat.zero_lt_of_lt hn₀
        . norm_cast
          exact lt_add_one n
    refine (StrictMono.lt_iff_lt ?_).mp hn₂
    exact hmo₂ (n + 1) (by linarith)


lemma aux_10
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (f₀ : ℕ → NNReal → NNReal)
  (hf₂ : ∀ (n : ℕ) (x : NNReal), 0 < n → f₀ n x = (f n x).toNNReal)
  (fi : ℕ → NNReal → NNReal)
  (hmo₇ : ∀ (n : ℕ), 0 < n → Function.RightInverse (fi n) (f₀ n))
  (sn : Set ℕ)
  (sb : Set NNReal)
  (fb : ↑sn → NNReal)
  (hsn₀ : sn = Set.Ici 1)
  (hfb₀ : fb = fun n:↑sn => fi (↑n) (1 - 1 / ↑↑n))
  (hsb₀ : sb = Set.range fb)
  (fr : NNReal → ℝ)
  (hfr: fr = fun x => ↑x)
  (sbr : Set ℝ)
  (hsbr: sbr = fr '' sb)
  (br: ℝ)
  (hbr₀ : IsLUB sbr br) :
  0 < br := by
  have hnb₀: 2 ∈ sn := by
    rw [hsn₀]
    decide
  let nb : ↑sn := ⟨2, hnb₀⟩
  have g₀: 0 < fb nb := by
    have g₁: (2:NNReal).IsConjExponent (2:NNReal) := by
      refine (NNReal.isConjExponent_iff_eq_conjExponent ?_).mpr ?_
      . exact one_lt_two
      . norm_cast
        simp
    rw [hfb₀]
    simp
    have hnb₁: nb.val = 2 := by exact rfl
    rw [hnb₁]
    norm_cast
    rw [NNReal.IsConjExponent.one_sub_inv g₁]
    let x := fi 2 2⁻¹
    have hx₀: x = fi 2 2⁻¹ := by rfl
    have hx₁: f₀ 2 x = 2⁻¹ := by
      rw [hx₀]
      have g₃: Function.RightInverse (fi 2) (f₀ 2) := by exact hmo₇ 2 (by linarith)
      exact g₃ 2⁻¹
    rw [← hx₀]
    contrapose! hx₁
    have hc₁: x = 0 := by exact nonpos_iff_eq_zero.mp hx₁
    have hc₃: f₀ 2 x = 0 := by
      rw [hc₁, hf₂ 2 0 (by linarith), h₁ 1 0 (by linarith), h₀ 0]
      norm_cast
      rw [zero_mul]
      exact Real.toNNReal_zero
    rw [hc₃]
    exact Ne.symm (NNReal.IsConjExponent.inv_ne_zero g₁)
  have g₁: ∃ x, 0 < x ∧ x ∈ sbr := by
    use (fb nb).toReal
    constructor
    . exact g₀
    . rw [hsbr]
      simp
      use fb ↑nb
      constructor
      . rw [hsb₀]
        exact Set.mem_range_self nb
      . exact congrFun hfr (fb ↑nb)
  obtain ⟨x, hx₀, hx₁⟩ := g₁
  have hx₂: br ∈ upperBounds sbr := by
    refine (isLUB_le_iff hbr₀).mp ?_
    exact Preorder.le_refl br
  exact gt_of_ge_of_gt (hx₂ hx₁) hx₀


lemma aux_11
  (sn : Set ℕ)
  (fb fc : ↑sn → NNReal)
  (hfc₂ : ∀ (n : ↑sn), fb n < fc n)
  (hfb₃ : StrictMono fb)
  (hfc₃ : StrictAnti fc)
  (sb sc : Set NNReal)
  (hsb₀ : sb = Set.range fb)
  (hsc₀ : sc = Set.range fc)
  (fr : NNReal → ℝ)
  (hfr : fr = fun x ↦ ↑x)
  (sbr scr : Set ℝ)
  (hsbr : sbr = fr '' sb)
  (hscr : scr = fr '' sc)
  (br cr : ℝ)
  (hbr₀ : IsLUB sbr br)
  (hcr₀ : IsGLB scr cr)
  (hfb₄ : ∀ (n : ↑sn), 0 ≤ fb n) :
  br ≤ cr := by
  have hfc₄: ∀ nb nc, fb nb < fc nc := by
    intros nb nc
    cases' (lt_or_le nb nc) with hn₀ hn₀
    . refine lt_trans ?_ (hfc₂ nc)
      exact hfb₃ hn₀
    cases' lt_or_eq_of_le hn₀ with hn₁ hn₁
    . refine lt_trans (hfc₂ nb) ?_
      exact hfc₃ hn₁
    . rw [hn₁]
      exact hfc₂ nb
  by_contra! hc₀
  have hc₁: ∃ x ∈ sbr, cr < x ∧ x ≤ br := by exact IsLUB.exists_between hbr₀ hc₀
  let ⟨x, hx₀, hx₁, _⟩ := hc₁
  have hc₂: ∃ y ∈ scr, cr ≤ y ∧ y < x := by exact IsGLB.exists_between hcr₀ hx₁
  let ⟨y, hy₀, _, hy₂⟩ := hc₂
  have hc₃: x < y := by
    have hx₃: x.toNNReal ∈ sb := by
      rw [hsbr] at hx₀
      apply (Set.mem_image fr sb x).mp at hx₀
      obtain ⟨z, hz₀, hz₁⟩ := hx₀
      rw [← hz₁, hfr, Real.toNNReal_coe]
      exact hz₀
    have hy₃: y.toNNReal ∈ sc := by
      rw [hscr] at hy₀
      apply (Set.mem_image fr sc y).mp at hy₀
      obtain ⟨z, hz₀, hz₁⟩ := hy₀
      rw [← hz₁, hfr, Real.toNNReal_coe]
      exact hz₀
    rw [hsb₀] at hx₃
    rw [hsc₀] at hy₃
    apply Set.mem_range.mp at hx₃
    apply Set.mem_range.mp at hy₃
    let ⟨nx, hnx₀⟩ := hx₃
    let ⟨ny, hny₀⟩ := hy₃
    have hy₄: 0 < y := by
      contrapose! hy₃
      have hy₅: y.toNNReal = 0 := by exact Real.toNNReal_of_nonpos hy₃
      intro z
      rw [hy₅]
      refine ne_of_gt ?_
      refine lt_of_le_of_lt ?_ (hfc₂ z)
      exact hfb₄ z
    refine (Real.toNNReal_lt_toNNReal_iff hy₄).mp ?_
    rw [← hnx₀, ← hny₀]
    exact hfc₄ nx ny
  refine (lt_self_iff_false x).mp ?_
  exact lt_trans hc₃ hy₂


lemma aux_exists
  (f : ℕ → NNReal → ℝ)
  (h₂ : ∀ (n : ℕ) (x : NNReal), 0 < n ∧ 0 < x → 0 < f n x)
  (hmo₀ : ∀ (n : ℕ), 0 < n → StrictMono (f n))
  (f₀ : ℕ → NNReal → NNReal)
  (hf₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f n x = ↑(f₀ n x))
  (sn : Set ℕ)
  (hsn₀ : sn = Set.Ici 1)
  (fb fc : ↑sn → NNReal)
  (hfb₁ : ∀ (n : ↑sn), f₀ (↑n) (fb n) = 1 - 1 / ↑↑n)
  (hfc₁ : ∀ (n : ↑sn), f₀ (↑n) (fc n) = 1)
  (hfb₃ : StrictMono fb)
  (hfc₃ : StrictAnti fc)
  (sb sc : Set NNReal)
  (hsb₀ : sb = Set.range fb)
  (hsc₀ : sc = Set.range fc)
  (fr : NNReal → ℝ)
  (hfr : fr = fun x => ↑x)
  (sbr scr : Set ℝ)
  (hsbr : sbr = fr '' sb)
  (hscr : scr = fr '' sc)
  (br cr : ℝ)
  (h₈ : ∀ (n : ℕ) (x : NNReal), 0 < n → 0 < x → 1 - 1 / ↑n < f n x → f n x < f (n + 1) x)
  (hbr₁ : 0 < br)
  (hu₅ : br ≤ cr)
  (hbr₃ : ∀ x ∈ sbr, x ≤ br)
  (hcr₃ : ∀ x ∈ scr, cr ≤ x) :
  ∃ x, ∀ (n : ℕ), 0 < n → 0 < f n x ∧ f n x < f (n + 1) x ∧ f (n + 1) x < 1 := by
  cases' lt_or_eq_of_le hu₅ with hu₆ hu₆
  . apply exists_between at hu₆
    let ⟨a, ha₀, ha₁⟩ := hu₆
    have ha₂: 0 < a := by exact gt_trans ha₀ hbr₁
    have ha₃: 0 < a.toNNReal := by exact Real.toNNReal_pos.mpr ha₂
    use a.toNNReal
    intros n hn₀
    have hn₁: n ∈ sn := by
      rw [hsn₀]
      exact hn₀
    constructor
    . exact h₂ n a.toNNReal ⟨hn₀, ha₃⟩
    constructor
    . refine h₈ n a.toNNReal hn₀ ?_ ?_
      . exact Real.toNNReal_pos.mpr ha₂
      . let nn : ↑sn := ⟨n, hn₁⟩
        have hn₂: f n (fb nn) = 1 - 1 / n := by
          rw [hf₁ n _ hn₀, hfb₁ nn]
          refine NNReal.coe_sub ?_
          refine div_le_self ?_ ?_
          . exact zero_le_one' NNReal
          . exact Nat.one_le_cast.mpr hn₀
        rw [← hn₂]
        refine hmo₀ n hn₀ ?_
        refine Real.lt_toNNReal_iff_coe_lt.mpr ?_
        refine lt_of_le_of_lt ?_ ha₀
        refine hbr₃ _ ?_
        rw [hsbr]
        refine (Set.mem_image fr sb _).mpr ?_
        use (fb nn)
        rw [hfr, hsb₀]
        refine ⟨?_, rfl⟩
        exact Set.mem_range_self nn
    . have hn₂: n + 1 ∈ sn := by
        rw [hsn₀]
        exact Set.mem_Ici.mpr (by linarith)
      let nn : ↑sn := ⟨n + 1, hn₂⟩
      have hn₃: f (n + 1) (fc (nn)) = 1 := by
        rw [hf₁ (n + 1) _ (by linarith), hfc₁ nn]
        exact rfl
      rw [← hn₃]
      refine hmo₀ (n + 1) (by linarith) ?_
      refine (Real.toNNReal_lt_iff_lt_coe (le_of_lt ha₂)).mpr ?_
      refine lt_of_lt_of_le ha₁ ?_
      refine hcr₃ _ ?_
      rw [hscr]
      refine (Set.mem_image fr sc _).mpr ?_
      use (fc nn)
      rw [hfr, hsc₀]
      refine ⟨?_, rfl⟩
      exact Set.mem_range_self nn
  . use br.toNNReal
    intros n hn₀
    have hn₁: n ∈ sn := by
      rw [hsn₀]
      exact hn₀
    constructor
    . refine h₂ n br.toNNReal ⟨hn₀, ?_⟩
      exact Real.toNNReal_pos.mpr hbr₁
    constructor
    . refine h₈ n br.toNNReal hn₀ ?_ ?_
      . exact Real.toNNReal_pos.mpr hbr₁
      . let nn : ↑sn := ⟨n, hn₁⟩
        have hn₂: fb nn < br := by
          by_contra! hc₀
          have hbr₅: (fb nn) = br := by
            refine eq_of_le_of_le ?_ hc₀
            refine hbr₃ _ ?_
            rw [hsbr]
            refine (Set.mem_image fr sb _).mpr ?_
            use (fb nn)
            rw [hfr, hsb₀]
            constructor
            . exact Set.mem_range_self nn
            . exact rfl
          have hn₂: n + 1 ∈ sn := by
            rw [hsn₀]
            refine Set.mem_Ici.mpr ?_
            exact Nat.le_add_right_of_le hn₀
          let ns : ↑sn := ⟨n + 1, hn₂⟩
          have hc₁: fb nn < fb ns := by
            refine hfb₃ ?_
            refine Subtype.mk_lt_mk.mpr ?_
            exact lt_add_one n
          have hbr₆: fb ns ≤ fb nn := by
            refine NNReal.coe_le_coe.mp ?_
            rw [hbr₅]
            refine hbr₃ _ ?_
            rw [hsbr]
            refine (Set.mem_image fr sb _).mpr ?_
            use (fb ns)
            rw [hfr, hsb₀]
            refine ⟨?_, rfl⟩
            exact Set.mem_range_self ns
          refine (lt_self_iff_false (fb nn)).mp ?_
          exact lt_of_lt_of_le hc₁ hbr₆
        have hn₃: f n (fb nn) = 1 - 1 / n := by
          rw [hf₁ n _ hn₀, hfb₁ nn]
          refine NNReal.coe_sub ?_
          refine div_le_self ?_ ?_
          . exact zero_le_one' NNReal
          . exact Nat.one_le_cast.mpr hn₀
        rw [← hn₃]
        refine hmo₀ n hn₀ ?_
        exact Real.lt_toNNReal_iff_coe_lt.mpr hn₂
    . have hn₂: n + 1 ∈ sn := by
        rw [hsn₀]
        exact Set.mem_Ici.mpr (by linarith)
      let nn : ↑sn := ⟨n + 1, hn₂⟩
      have hcr₁: 0 < cr := by exact gt_of_ge_of_gt hu₅ hbr₁
      have hn₃: f (n + 1) (fc (nn)) = 1 := by
        rw [hf₁ (n + 1) _ (by linarith), hfc₁ nn]
        exact rfl
      rw [← hn₃, hu₆]
      refine hmo₀ (n + 1) (by linarith) ?_
      refine (Real.toNNReal_lt_iff_lt_coe (le_of_lt hcr₁)).mpr ?_
      by_contra! hc₀
      have hc₁: fc nn = cr := by
        refine eq_of_le_of_le hc₀ ?_
        refine hcr₃ _ ?_
        rw [hscr]
        refine (Set.mem_image fr sc _).mpr ?_
        use (fc nn)
        rw [hfr, hsc₀]
        refine ⟨?_, rfl⟩
        exact Set.mem_range_self nn
      have hn₄: n + 2 ∈ sn := by
        rw [hsn₀]
        refine Set.mem_Ici.mpr ?_
        exact Nat.le_add_right_of_le hn₀
      let ns : ↑sn := ⟨n + 2, hn₄⟩
      have hn₅: fc ns < fc nn := by
        refine hfc₃ ?_
        refine Subtype.mk_lt_mk.mpr ?_
        exact Nat.lt_add_one (n + 1)
      have hc₂: fc nn ≤ fc ns := by
        refine NNReal.coe_le_coe.mp ?_
        rw [hc₁]
        refine hcr₃ _ ?_
        rw [hscr]
        refine (Set.mem_image fr sc _).mpr ?_
        use (fc ns)
        rw [hfr, hsc₀]
        refine ⟨?_, rfl⟩
        exact Set.mem_range_self ns
      refine (lt_self_iff_false (fc ns)).mp ?_
      exact lt_of_lt_of_le hn₅ hc₂




lemma aux_unique_top_ind
  (f : ℕ → NNReal → ℝ)
  (sd : Set ℕ)
  (hsd : sd = Set.Ici 2)
  (fd : NNReal → NNReal → ↑sd → ℝ)
  (hfd₁ : ∀ (y₁ y₂ : NNReal) (n : ↑sd), fd y₁ y₂ n = f (↑n) y₂ - f (↑n) y₁)
  (hd₁ : ∀ (n : ↑sd) (a b : NNReal), a < b → 0 < fd a b n)
  (a b : NNReal)
  (ha₀ : a < b)
  (hd₃: ∀ (nd : ↑sd), nd.1 + (1:ℕ) ∈ sd)
  (hd₂ : ∀ (nd : ↑sd), fd a b nd * (2 - 1 / ↑↑nd) ≤ fd a b ⟨nd.1 + 1, hd₃ nd⟩)
  (hi₀ : 2 ∈ sd)
  (i : ↑sd)
  (hi₁ : i = ⟨2, hi₀⟩) :
  ∀ (nd : ↑sd), fd a b i * (3 / 2) ^ (nd.1 - 2) ≤ fd a b nd := by
  intro nd
  rw [hfd₁ a b nd]
  have hnd₀: 2 ≤ nd.1 := by
    refine Set.mem_Ici.mp ?_
    rw [← hsd]
    exact nd.2
  refine Nat.le_induction ?_ ?_ nd.1 hnd₀
  . have hi₂: i.val = (2:ℕ) := by
      simp_all only [Subtype.forall]
    rw [hfd₁ a b i, hi₂]
    simp
  . simp
    intros n hn₀ hn₁
    have hn₂: n - 1 = n - 2 + 1 := by
      simp
      exact (Nat.sub_eq_iff_eq_add hn₀).mp rfl
    have hn₃: n ∈ sd := by
      rw [hsd]
      exact hn₀
    let nn : ↑sd := ⟨n, hn₃⟩
    have hnn: nn.1 = n := by exact rfl
    have hn₄: nn.1 + 1 ∈ sd := by
      rw [hnn, hsd]
      refine Set.mem_Ici.mpr ?_
      exact Nat.le_add_right_of_le hn₀
    have hn₅: fd a b nn * (2 - 1 / ↑n) ≤ fd a b ⟨nn.1 + 1, hn₄⟩ := by exact hd₂ nn
    rw [hfd₁ a b ⟨nn.1 + 1, hn₄⟩] at hn₅
    have hn₆: f (↑nn + 1) b - f (↑nn + 1) a = f (n + 1) b - f (n + 1) a := by exact rfl
    rw [hn₆] at hn₅
    refine le_trans ?_ hn₅
    rw [hn₂, pow_succ (3/2) (n - 2), ← mul_assoc (fd a b i)]
    refine mul_le_mul ?_ ?_ (by linarith) ?_
    . refine le_of_le_of_eq hn₁ ?_
      rw [hfd₁]
    . refine (div_le_iff₀ (two_pos)).mpr ?_
      rw [sub_mul, one_div_mul_eq_div _ 2]
      refine le_sub_iff_add_le.mpr ?_
      refine le_sub_iff_add_le'.mp ?_
      refine (div_le_iff₀ ?_).mpr ?_
      . refine Nat.cast_pos.mpr ?_
        exact lt_of_lt_of_le (two_pos) hn₀
      . ring_nf
        exact Nat.ofNat_le_cast.mpr hn₀
    . exact le_of_lt (hd₁ nn a b ha₀)



lemma aux_unique_top
  (f : ℕ → NNReal → ℝ)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (h₇ : ∀ (n : ℕ) (x : NNReal), 0 < n → f n x < f (n + 1) x → 1 - 1 / ↑n < f n x)
  (sd : Set ℕ)
  (hsd : sd = Set.Ici 2)
  (fd : NNReal → NNReal → ↑sd → ℝ)
  (hfd₁ : ∀ (y₁ y₂ : NNReal) (n : ↑sd), fd y₁ y₂ n = f (↑n) y₂ - f (↑n) y₁)
  (hd₁ : ∀ (n : ↑sd) (a b : NNReal), a < b → 0 < fd a b n) :
  ∀ (a b : NNReal),
    a < b →
      (∀ (n : ↑sd), f (↑n) a < f (↑n + 1) a ∧ f (↑n) b < f (↑n + 1) b)
      → Filter.Tendsto (fd a b) Filter.atTop Filter.atTop := by
  intros a b ha₀ ha₁
  have hd₀: ∀ (nd:↑sd), (nd.1 + 1) ∈ sd := by
    intro nd
    let t : ℕ := nd.1
    have ht: t = nd.1 := by rfl
    rw [← ht, hsd]
    refine Set.mem_Ici.mpr ?_
    refine Nat.le_add_right_of_le ?_
    refine Set.mem_Ici.mp ?_
    rw [ht, ← hsd]
    exact nd.2
  have hd₂: ∀ nd, fd a b nd  * (2 - 1 / nd.1) ≤ fd a b ⟨nd.1 + 1, hd₀ nd⟩ := by
    intro nd
    have hnd₀: 0 < nd.1 := by
      have g₀: 2 ≤ nd.1 := by
        refine Set.mem_Ici.mp ?_
        rw [← hsd]
        exact nd.2
      exact Nat.zero_lt_of_lt g₀
    rw [hfd₁, hfd₁, h₁ nd.1 _ hnd₀, h₁ nd.1 _ hnd₀]
    have hnd₁: f (↑nd) b * (f (↑nd) b + 1 / ↑↑nd) - f (↑nd) a * (f (↑nd) a + 1 / ↑↑nd) =
      (f (↑nd) b - f (↑nd) a) * (f (↑nd) b + f (↑nd) a + 1 / nd.1) := by
      ring_nf
    rw [hnd₁]
    refine (mul_le_mul_left ?_).mpr ?_
    . rw [← hfd₁]
      exact hd₁ nd a b ha₀
    . refine le_sub_iff_add_le.mp ?_
      rw [sub_neg_eq_add]
      have hnd₂: 1 - 1 / nd.1 < f (↑nd) b := by
        exact h₇ nd.1 b hnd₀ (ha₁ nd).2
      have hnd₃: 1 - 1 / nd.1 < f (↑nd) a := by
        exact h₇ nd.1 a hnd₀ (ha₁ nd).1
      linarith
  have hi: 2 ∈ sd := by
    rw [hsd]
    decide
  let i : ↑sd := ⟨(2:ℕ), hi⟩
  have hd₃: ∀ nd, fd a b i * (3 / 2) ^ (nd.1 - 2) ≤ fd a b nd := by
    intro nd
    exact aux_unique_top_ind f sd hsd fd hfd₁ hd₁ a b ha₀ hd₀ hd₂ hi i rfl nd
  have hsd₁: Nonempty ↑sd := by
    refine Set.Nonempty.to_subtype ?_
    exact Set.nonempty_of_mem (hd₀ i)
  refine Filter.tendsto_atTop_atTop.mpr ?_
  intro z
  by_cases hz₀: z ≤ fd a b i
  . use i
    intros j _
    refine le_trans hz₀ ?_
    refine le_trans ?_ (hd₃ j)
    refine le_mul_of_one_le_right ?_ ?_
    . refine le_of_lt ?_
      exact hd₁ i a b ha₀
    . refine one_le_pow₀ ?_
      linarith
  . push_neg at hz₀
    have hz₁: 0 < fd a b i := by exact hd₁ i a b ha₀
    have hz₂: 0 < Real.log (z / fd a b i) := by
      refine Real.log_pos ?_
      exact (one_lt_div hz₁).mpr hz₀
    let j : ℕ := Nat.ceil (2 + Real.log (z / fd a b i) / Real.log (3 / 2))
    have hj₀: 2 < j := by
      refine Nat.lt_ceil.mpr ?_
      norm_cast
      refine lt_add_of_pos_right 2 ?_
      refine div_pos ?_ ?_
      . exact hz₂
      . refine Real.log_pos ?_
        linarith
    have hj₁: j ∈ sd := by
      rw [hsd]
      exact Set.mem_Ici_of_Ioi hj₀
    use ⟨j, hj₁⟩
    intro k hk₀
    have hk₁: fd a b i * (3 / 2) ^ (k.1 - 2) ≤ fd a b k := by
      exact hd₃ k
    have hk₂: i < k := by
      refine lt_of_lt_of_le ?_ hk₀
      refine Subtype.mk_lt_mk.mpr ?_
      refine Nat.lt_ceil.mpr ?_
      norm_cast
      refine lt_add_of_pos_right 2 ?_
      refine div_pos ?_ ?_
      . exact hz₂
      . refine Real.log_pos ?_
        linarith
    refine le_trans ?_ hk₁
    refine (div_le_iff₀' ?_).mp ?_
    . exact hz₁
    . refine Real.le_pow_of_log_le (by linarith) ?_
      refine (div_le_iff₀ ?_).mp ?_
      . refine Real.log_pos ?_
        linarith
      . rw [Nat.cast_sub ?_]
        . rw [Nat.cast_two]
          refine le_sub_iff_add_le'.mpr ?_
          exact Nat.le_of_ceil_le hk₀
        . exact Nat.le_of_succ_le hk₂



lemma aux_unique_nhds
  (f : ℕ → NNReal → ℝ)
  (sd : Set ℕ)
  (hsd : sd = Set.Ici 2)
  (fd : NNReal → NNReal → ↑sd → ℝ)
  (hfd₁ : ∀ (y₁ y₂ : NNReal) (n : ↑sd), fd y₁ y₂ n = f (↑n) y₂ - f (↑n) y₁)
  (hd₁ : ∀ (n : ↑sd) (a b : NNReal), a < b → 0 < fd a b n) :
  ∀ (a b : NNReal),
    a < b →
      (∀ (n : ↑sd), (1 - 1 / ↑↑n < f (↑n) a ∧ 1 - 1 / ↑↑n < f (↑n) b) ∧ f (↑n) a < 1 ∧ f (↑n) b < 1) →
        Filter.Tendsto (fd a b) Filter.atTop (nhds 0) := by
  intros a b ha₀ ha₁
  have hsd₁: Nonempty ↑sd := by
    rw [hsd]
    refine Set.Nonempty.to_subtype ?_
    exact Set.nonempty_Ici
  refine tendsto_atTop_nhds.mpr ?_
  intros U hU₀ hU₁
  have hU₂: U ∈ nhds 0 := by exact IsOpen.mem_nhds hU₁ hU₀
  apply mem_nhds_iff_exists_Ioo_subset.mp at hU₂
  obtain ⟨l, u, hl₀, hl₁⟩ := hU₂
  have hl₂: 0 < u := by exact (Set.mem_Ioo.mpr hl₀).2
  let nd := 2 + Nat.ceil (1/u)
  have hnd₀: nd ∈ sd := by
    rw [hsd]
    refine Set.mem_Ici.mpr ?_
    exact Nat.le_add_right 2 ⌈1 / u⌉₊
  use ⟨nd, hnd₀⟩
  intros n hn₀
  refine (IsOpen.mem_nhds_iff hU₁).mp ?_
  refine mem_nhds_iff.mpr ?_
  use Set.Ioo l u
  constructor
  . exact hl₁
  constructor
  . exact isOpen_Ioo
  . refine Set.mem_Ioo.mpr ?_
    constructor
    . refine lt_trans ?_ (hd₁ n a b ha₀)
      exact (Set.mem_Ioo.mp hl₀).1
    . have hn₁: fd a b n < 1 / n := by
        rw [hfd₁]
        have ha₂: 1 - 1 / n < f n a := by exact (ha₁ n).1.1
        have hb₁: f n b < 1 := by exact (ha₁ n).2.2
        refine sub_lt_iff_lt_add.mpr ?_
        refine lt_trans hb₁ ?_
        exact sub_lt_iff_lt_add'.mp ha₂
      have hn₂: (1:ℝ) / n ≤ 1 / nd := by
        refine one_div_le_one_div_of_le ?_ ?_
        . refine Nat.cast_pos.mpr ?_
          rw [hsd] at hnd₀
          exact lt_of_lt_of_le (Nat.zero_lt_two) hnd₀
        . exact Nat.cast_le.mpr hn₀
      refine lt_of_lt_of_le hn₁ ?_
      refine le_trans hn₂ ?_
      refine div_le_of_le_mul₀ ?_ ?_ ?_
      . exact Nat.cast_nonneg' nd
      . exact le_of_lt hl₂
      . have hl₃: u * (2 + 1 / u) ≤ u * ↑((2:ℕ) + ⌈(1:ℝ) / u⌉₊) := by
          refine (mul_le_mul_left hl₂).mpr ?_
          rw [Nat.cast_add 2 _, Nat.cast_two]
          refine add_le_add_left ?_ 2
          exact Nat.le_ceil (1 / u)
        refine le_trans ?_ hl₃
        rw [mul_add, mul_one_div u u, div_self (ne_of_gt hl₂)]
        refine le_of_lt ?_
        refine sub_lt_iff_lt_add.mp ?_
        rw [sub_self 1]
        exact mul_pos hl₂ (two_pos)




lemma aux_unique
  (f : ℕ → NNReal → ℝ)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (hmo₀ : ∀ (n : ℕ), 0 < n → StrictMono (f n))
  (h₇ : ∀ (n : ℕ) (x : NNReal), 0 < n → f n x < f (n + 1) x → 1 - 1 / ↑n < f n x) :
  ∀ (y₁ y₂ : NNReal),
    (∀ (n : ℕ), 0 < n → 0 < f n y₁ ∧ f n y₁ < f (n + 1) y₁ ∧ f (n + 1) y₁ < 1) →
      (∀ (n : ℕ), 0 < n → 0 < f n y₂ ∧ f n y₂ < f (n + 1) y₂ ∧ f (n + 1) y₂ < 1) → y₁ = y₂ := by
  intros x y hx₀ hy₀
  let sd : Set ℕ := Set.Ici 2
  let fd : NNReal → NNReal → ↑sd → ℝ := fun y₁ y₂ n => (f n.1 y₂ - f n.1 y₁)
  have hfd₁: ∀ y₁ y₂ n, fd y₁ y₂ n = f n.1 y₂ - f n.1 y₁ := by exact fun y₁ y₂ n => rfl
  have hd₁: ∀ n a b, a < b → 0 < fd a b n := by
    intros nd a b hnd₀
    rw [hfd₁]
    refine sub_pos.mpr ?_
    refine hmo₀ nd.1 ?_ hnd₀
    exact lt_of_lt_of_le (Nat.zero_lt_two) nd.2
  have hfd₂: ∀ a b, a < b → (∀ n:↑sd, f n.1 a < f (n.1 + 1) a ∧ f n.1 b < f (n.1 + 1) b)
      → Filter.Tendsto (fd a b) Filter.atTop Filter.atTop := by
    intros a b ha₀ ha₁
    exact aux_unique_top f h₁ h₇ sd rfl fd hfd₁ hd₁ a b ha₀ ha₁
  have hfd₃: ∀ a b, a < b → (∀ (n:↑sd), (1 - 1 / n.1 < f n.1 a ∧ 1 - 1 / n.1 < f n.1 b) ∧ (f n.1 a < 1 ∧ f n.1 b < 1))
      → Filter.Tendsto (fd a b) Filter.atTop (nhds 0) := by
    intros a b ha₀ ha₁
    exact aux_unique_nhds f sd rfl fd hfd₁ hd₁ a b ha₀ ha₁
  by_contra! hc₀
  by_cases hy₁: x < y
  . have hy₂: Filter.Tendsto (fd x y) Filter.atTop Filter.atTop := by
      refine hfd₂ x y hy₁ ?_
      intro nd
      have hnd₀: 0 < nd.1 := by exact lt_of_lt_of_le (two_pos) nd.2
      constructor
      . exact (hx₀ nd.1 hnd₀).2.1
      . exact (hy₀ nd.1 hnd₀).2.1
    have hy₃: Filter.Tendsto (fd x y) Filter.atTop (nhds 0) := by
      refine hfd₃ x y hy₁ ?_
      intro nd
      have hnd₀: 0 < nd.1 := by
        refine lt_of_lt_of_le ?_ nd.2
        exact Nat.zero_lt_two
      have hnd₁: nd.1 - 1 + 1 = nd.1 := by exact Nat.sub_add_cancel hnd₀
      have hnd₂: 0 < nd.1 - 1 := by
        refine Nat.sub_pos_of_lt ?_
        refine lt_of_lt_of_le ?_ nd.2
        exact Nat.one_lt_two
      constructor
      . constructor
        . refine h₇ nd.1 x hnd₀ ?_
          exact (hx₀ (nd.1) hnd₀).2.1
        . refine h₇ nd.1 y hnd₀ ?_
          exact (hy₀ (nd.1) hnd₀).2.1
      . constructor
        . rw [← hnd₁]
          exact (hx₀ (nd.1 - 1) hnd₂).2.2
        . rw [← hnd₁]
          exact (hy₀ (nd.1 - 1) hnd₂).2.2
    apply Filter.tendsto_atTop_atTop.mp at hy₂
    apply tendsto_atTop_nhds.mp at hy₃
    contrapose! hy₃
    clear hy₃
    let sx : Set ℝ := Set.Ioo (-1) 1
    use sx
    constructor
    . refine Set.mem_Ioo.mpr ?_
      simp
    constructor
    . exact isOpen_Ioo
    . intro N
      have hy₅: ∃ i, ∀ (a : ↑sd), i ≤ a → N + 3 ≤ fd x y a := by exact hy₂ (N + 3)
      obtain ⟨i, hi₀⟩ := hy₅
      have hi₁: (N.1 + i.1) ∈ sd := by
        refine Set.mem_Ici.mpr ?_
        rw [← add_zero 2]
        refine Nat.add_le_add ?_ ?_
        . exact N.2
        . refine le_trans ?_ i.2
          exact Nat.zero_le 2
      let a : ↑sd := ⟨N + i, hi₁⟩
      use a
      constructor
      . refine Subtype.mk_le_mk.mpr ?_
        exact Nat.le_add_right ↑N ↑i
      . refine Set.not_mem_Ioo_of_ge ?_
        have hi₂: ↑↑N + 3 ≤ fd x y a := by
          refine hi₀ a ?_
          refine Subtype.mk_le_mk.mpr ?_
          exact Nat.le_add_left ↑i ↑N
        refine le_trans ?_ hi₂
        norm_cast
        exact Nat.le_add_left 1 (↑N + 2)
  . have hy₂: y < x := by
      push_neg at hy₁
      exact lt_of_le_of_ne hy₁ hc₀.symm
    have hy₃: Filter.Tendsto (fd y x) Filter.atTop Filter.atTop := by
      refine hfd₂ y x hy₂ ?_
      intro nd
      have hnd₀: 0 < nd.1 := by exact lt_of_lt_of_le (two_pos) nd.2
      constructor
      . exact (hy₀ nd.1 hnd₀).2.1
      . exact (hx₀ nd.1 hnd₀).2.1
    have hy₄: Filter.Tendsto (fd y x) Filter.atTop (nhds 0) := by
      refine hfd₃ y x hy₂ ?_
      intro nd
      have hnd₀: 0 < nd.1 := by exact lt_of_lt_of_le (Nat.zero_lt_two) nd.2
      have hnd₁: nd.1 - 1 + 1 = nd.1 := by exact Nat.sub_add_cancel hnd₀
      have hnd₂: 0 < nd.1 - 1 := by
        refine Nat.sub_pos_of_lt ?_
        exact lt_of_lt_of_le (Nat.one_lt_two) nd.2
      constructor
      . constructor
        . refine h₇ nd.1 y hnd₀ ?_
          exact (hy₀ (nd.1) hnd₀).2.1
        . refine h₇ nd.1 x hnd₀ ?_
          exact (hx₀ (nd.1) hnd₀).2.1
      . constructor
        . rw [← hnd₁]
          exact (hy₀ (nd.1 - 1) hnd₂).2.2
        . rw [← hnd₁]
          exact (hx₀ (nd.1 - 1) hnd₂).2.2
    apply Filter.tendsto_atTop_atTop.mp at hy₃
    apply tendsto_atTop_nhds.mp at hy₄
    contrapose! hy₄
    clear hy₄
    let sx : Set ℝ := Set.Ioo (-1) 1
    use sx
    constructor
    . refine Set.mem_Ioo.mpr ?_
      simp
    constructor
    . exact isOpen_Ioo
    . intro N
      have hy₅: ∃ i, ∀ (a : ↑sd), i ≤ a → N + 3 ≤ fd y x a := by exact hy₃ (N + 3)
      obtain ⟨i, hi₀⟩ := hy₅
      have hi₁: (N.1 + i.1) ∈ sd := by
        refine Set.mem_Ici.mpr ?_
        rw [← add_zero 2]
        refine Nat.add_le_add ?_ ?_
        . exact N.2
        . refine le_trans ?_ i.2
          exact Nat.zero_le 2
      let a : ↑sd := ⟨N + i, hi₁⟩
      use a
      constructor
      . refine Subtype.mk_le_mk.mpr ?_
        exact Nat.le_add_right ↑N ↑i
      . refine Set.not_mem_Ioo_of_ge ?_
        have hi₂: ↑↑N + 3 ≤ fd y x a := by
          refine hi₀ a ?_
          refine Subtype.mk_le_mk.mpr ?_
          exact Nat.le_add_left ↑i ↑N
        refine le_trans ?_ hi₂
        norm_cast
        exact Nat.le_add_left 1 (↑N + 2)




theorem imo_1985_p6
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ x, f 1 x = x)
  (h₁ : ∀ n x, 0 < n → f (n + 1) x = f n x * (f n x + 1 / n)) :
  ∃! a, ∀ n, 0 < n → 0 < f n a ∧ f n a < f (n + 1) a ∧ f (n + 1) a < 1 := by
  have h₂: ∀ n x, 0 < n ∧ 0 < x → 0 < f n x := by
    exact fun n x a => aux_1 f h₀ h₁ n x a
  have h₃: ∀ n x, 0 < n → 0 ≤ f n x := by
    intros n x hn
    refine Nat.le_induction ?_ ?_ n hn
    . rw [h₀ x]
      exact NNReal.zero_le_coe
    . intros d hd₀ hd₁
      rw [h₁ d x hd₀]
      refine mul_nonneg hd₁ ?_
      refine add_nonneg hd₁ ?_
      refine div_nonneg (by linarith) ?_
      exact Nat.cast_nonneg' d
  have hmo₀: ∀ n, 0 < n → StrictMono (f n) := by
    intros n hn₀
    refine Monotone.strictMono_of_injective ?h₁ ?h₂
    . refine monotone_iff_forall_lt.mpr ?h₁.a
      intros a b hab
      refine le_of_lt ?_
      exact aux_2 f h₀ h₁ h₂ h₃ n a b hn₀ hab
    . intros p q hpq
      contrapose! hpq
      apply lt_or_gt_of_ne at hpq
      cases' hpq with hpq hpq
      . refine ne_of_lt ?_
        exact aux_2 f h₀ h₁ h₂ h₃ n p q hn₀ hpq
      . symm
        refine ne_of_lt ?_
        exact aux_2 f h₀ h₁ h₂ h₃ n q p hn₀ hpq
  have hmo₁: ∀ n, 0 < n → Function.Injective (f n) := by exact fun n a => StrictMono.injective (hmo₀ n a)
  let f₀: ℕ → NNReal → NNReal := fun n x => (f n x).toNNReal
  have hf₀: f₀ = fun n x => (f n x).toNNReal := by rfl
  have hf₁: ∀ n x, 0 < n → f n x = f₀ n x := by
    intros n x hn₀
    rw [hf₀]
    simp
    exact h₃ n x hn₀
  have hf₂: ∀ n x, 0 < n → f₀ n x = (f n x).toNNReal := by
    intros n x _
    rw [hf₀]
  have hmo₂: ∀ n, 0 < n → StrictMono (f₀ n) := by
    intros n hn₀
    refine aux_4 f h₃ ?_ f₀ hf₀ n hn₀
    exact fun n x y a a_1 => hmo₀ n a a_1
  let fi : ℕ → NNReal → NNReal := fun n => Function.invFun (f₀ n)
  have hmo₇: ∀ n, 0 < n → Function.RightInverse (fi n) (f₀ n) := by
    intros n hn₀
    refine Function.rightInverse_invFun ?_
    have h₄: ∀ n x y, 0 < n → x < y → f n x < f n y := by
      exact fun n x y a a_1 => aux_2 f h₀ h₁ h₂ h₃ n x y a a_1
    refine aux_7 f h₀ h₁ h₃ ?_ f₀ hf₂ hmo₂ ?_ n hn₀
    . exact fun n x a => aux_3 f h₀ h₁ h₄ n x a
    . intros m hm₀
      exact aux_6 f h₀ h₁ f₀ hf₀ m hm₀
  have hf₇: ∀ n x y, 0 < n → (f₀ n x = y ↔ fi n y = x) := by
    intros n x y hn₀
    constructor
    . intro hn₁
      rw [← hn₁, hf₀]
      have hn₂: (Function.invFun (f n)) ∘ (f n) = id := by exact Function.invFun_comp (hmo₁ n hn₀)
      rw [Function.comp_def (Function.invFun (f n)) (f n)] at hn₂
      exact aux_5 f hmo₁ f₀ hmo₂ fi rfl n x ((fun n x => (f n x).toNNReal) n x) hn₀ (hf₂ n x hn₀)
    . intro hn₁
      rw [← hn₁]
      exact hmo₁ n hn₀ (congrArg (f n) (hmo₇ n hn₀ y))
  let sn : Set ℕ := Set.Ici 1
  let fb : ↑sn → NNReal := sn.restrict (fun (n:ℕ) => fi n (1 - 1 / (n:NNReal)))
  let fc : ↑sn → NNReal := sn.restrict (fun (n:ℕ) => fi n 1)
  have hsn₁: ∀ n:↑sn, ↑n ∈ sn ∧ 0 < (↑n:ℕ) := by
    intro n
    have hn₀: ↑n ∈ sn := by exact Subtype.coe_prop n
    constructor
    . exact Subtype.coe_prop n
    . exact hn₀
  have hfb₀: fb = fun (n:↑sn) => fi n (1 - 1 / (n:NNReal)) := by rfl
  have hfc₀: fc = fun (n:↑sn) => fi n 1 := by rfl
  have hfb₁: ∀ n:↑sn, f₀ n (fb n) = 1 - 1 / (n:NNReal) := by
    intros n
    have hn₀: 0 < (n:ℕ) := by exact (hsn₁ n).2
    rw [hfb₀]
    exact hmo₁ n hn₀ (congrArg (f n) (hmo₇ n hn₀ (1 - 1 / (n:NNReal))))
  have hfc₁: ∀ n:↑sn, f₀ n (fc n) = 1 := by
    intros n
    have hn₀: 0 < (n:ℕ) := by exact (hsn₁ n).2
    rw [hfc₀]
    exact hmo₁ n hn₀ (congrArg (f n) (hmo₇ n hn₀ 1))
  have hu₁: ∀ n:↑sn, fb n < 1 := by
    exact aux_8 f h₀ h₁ hmo₀ hmo₁ f₀ hf₂ sn fb hsn₁ hfb₁
  have hfc₂: ∀ n:↑sn, fb n < fc n := by
    intros n
    have hn₀: 0 < (n:ℕ) := by exact (hsn₁ n).2
    have g₀: f₀ n (fb n) < f₀ n (fc n) := by
      rw [hfb₁ n, hfc₁ n]
      simp
      exact (hsn₁ n).2
    exact (StrictMono.lt_iff_lt (hmo₂ n hn₀)).mp g₀
  have hfb₃: StrictMono fb := by
    refine StrictMonoOn.restrict ?_
    refine aux_9 f h₀ h₁ f₀ hf₁ hf₂ hmo₂ fi ?_ hmo₇ hf₇ _ (by rfl) sn (by rfl)
    intro x
    refine (hf₇ 1 x x (by linarith)).mp ?_
    rw [hf₂ 1 x (by linarith), h₀]
    exact Real.toNNReal_coe
  have hfc₃: StrictAnti fc := by
    have g₀: StrictAntiOn (fun n => fi n 1) sn := by
      refine strictAntiOn_Ici_of_lt_pred ?_
      intros m hm₀
      have hm₁: 0 < m - 1 := by exact Nat.zero_lt_sub_of_lt hm₀
      have hm₂: m = m - 1 + 1 := by rw [Nat.sub_add_cancel (le_of_lt hm₀)]
      have hm₃: 0 < m := by exact Nat.zero_lt_of_lt hm₀
      simp
      let x := fi m 1
      let y := fi (m - 1) 1
      have hx₀: x = fi m 1 := by rfl
      have hy₀: y = fi (m - 1) 1 := by rfl
      have hx₁: f₀ m x = 1 := by exact (hf₇ m x 1 (by linarith)).mpr hx₀.symm
      have hy₁: f₀ (m - 1) y = 1 := by
        exact (hf₇ (m - 1) y 1 hm₁).mpr hy₀.symm
      have hy₂: f (m - 1) y = 1 := by
        rw [hf₁ (m - 1) y hm₁, hy₁]
        exact rfl
      have hf: StrictMono (f m) := by exact hmo₀ m hm₃
      refine (StrictMono.lt_iff_lt hf).mp ?_
      rw [← hx₀, ← hy₀]
      rw [hf₁ m x hm₃, hf₁ m y hm₃]
      refine NNReal.coe_lt_coe.mpr ?_
      rw [hx₁, hf₂ m y hm₃, hm₂, h₁ (m - 1) y hm₁, hy₂]
      simp
      exact hm₀
    intros m n hmn
    rw [hfc₀]
    simp
    let mn : ℕ := ↑m
    let nn : ℕ := ↑n
    have hm₀: mn ∈ sn := by exact Subtype.coe_prop m
    have hn₀: nn ∈ sn := by exact Subtype.coe_prop n
    exact g₀ hm₀ hn₀ hmn
  let sb := Set.range fb
  let sc := Set.range fc
  have hsb₀: sb = Set.range fb := by rfl
  have hsc₀: sc = Set.range fc := by rfl
  let fr : NNReal → ℝ := fun x => x.toReal
  let sbr := Set.image fr sb
  let scr := Set.image fr sc
  have hu₃: ∃ br, IsLUB sbr br := by
    refine Real.exists_isLUB ?_ ?_
    . exact Set.Nonempty.of_subtype
    . refine NNReal.bddAbove_coe.mpr ?_
      refine (bddAbove_iff_exists_ge 1).mpr ?_
      use 1
      constructor
      . exact Preorder.le_refl 1
      . intros y hy₀
        apply Set.mem_range.mp at hy₀
        obtain ⟨na, hna₀⟩ := hy₀
        refine le_of_lt ?_
        rw [← hna₀]
        exact hu₁ na
  have hu₄: ∃ cr, IsGLB scr cr := by
    refine Real.exists_isGLB ?_ ?_
    . refine Set.Nonempty.image fr ?_
      exact Set.range_nonempty fc
    . exact NNReal.bddBelow_coe sc
  obtain ⟨br, hbr₀⟩ := hu₃
  obtain ⟨cr, hcr₀⟩ := hu₄
  have h₇: ∀ n x, 0 < n → (f n x < f (n + 1) x → 1 - 1 / n < f n x) := by
    intros n x hn₀ hn₁
    rw [h₁ n x hn₀] at hn₁
    nth_rw 1 [← mul_one (f n x)] at hn₁
    suffices g₀: 1 < f n x + 1 / ↑n
    . exact sub_right_lt_of_lt_add g₀
    . refine lt_of_mul_lt_mul_left hn₁ ?_
      exact h₃ n x hn₀
  have h₈: ∀ n x, 0 < n → 0 < x → 1 - 1 / n < f n x → f n x < f (n + 1) x := by
    intros n x hn₀ hx₀ hn₁
    rw [h₁ n x hn₀]
    suffices g₀: 1 < f n x + 1 / ↑n
    . nth_rw 1 [← mul_one (f n x)]
      refine mul_lt_mul' ?_ g₀ ?_ ?_
      . exact Preorder.le_refl (f n x)
      . exact zero_le_one' ℝ
      . exact gt_of_gt_of_ge (hmo₀ n hn₀ hx₀) (h₃ n 0 hn₀)
    . exact lt_add_of_tsub_lt_right hn₁
  have hbr₁: 0 < br := by
    exact aux_10 f h₀ h₁ f₀ hf₂ fi hmo₇ sn sb fb (by rfl) hfb₀ hsb₀ fr (by rfl) sbr (by rfl) br hbr₀
  have hfb₄: ∀ n, 0 ≤ fb n := by
    intro n
    have hfb₂: fb = fun (n:↑sn) => Function.invFun (f₀ n) (1 - 1 / ↑n) := by exact hfb₀
    rw [hfb₂]
    simp
  have hu₅: br ≤ cr := by
    exact aux_11 sn fb fc hfc₂ hfb₃ hfc₃ sb sc hsb₀ hsc₀ fr (by rfl) sbr scr (by rfl) (by rfl) br cr hbr₀ hcr₀ hfb₄
  have hbr₃: ∀ x ∈ sbr, x ≤ br := by
    refine mem_upperBounds.mp ?_
    refine (isLUB_le_iff hbr₀).mp ?_
    exact Preorder.le_refl br
  have hcr₃: ∀ x ∈ scr, cr ≤ x := by
      refine mem_lowerBounds.mp ?_
      refine (le_isGLB_iff hcr₀).mp ?_
      exact Preorder.le_refl cr
  refine existsUnique_of_exists_of_unique ?_ ?_
  . exact aux_exists f h₂ hmo₀ f₀ hf₁ sn (by rfl) fb fc hfb₁ hfc₁ hfb₃ hfc₃ sb sc hsb₀ hsc₀ fr (by rfl) sbr scr (by rfl) (by rfl) br cr h₈ hbr₁ hu₅ hbr₃ hcr₃
  . intros x y hx₀ hy₀
    exact aux_unique f h₁ hmo₀ h₇ x y hx₀ hy₀
