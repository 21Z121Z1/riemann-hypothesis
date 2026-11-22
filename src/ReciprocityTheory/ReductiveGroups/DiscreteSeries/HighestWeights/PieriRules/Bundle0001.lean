import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Bundle0001
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PieriRules.KTypeIntDomStatement
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Bundle0003
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ContinuousRepresentations.DerivExistsAllPosStatement

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PieriRules.KtintExpApplyOfEig
section
noncomputable section

open Matrix

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

lemma ktint_exp_apply_of_eig {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (A : E →L[ℂ] E) (c : ℂ) (v : E) (h : A v = c • v) :
    NormedSpace.exp A v = NormedSpace.exp c • v := by
  have hpow : ∀ k : ℕ, (A ^ k) v = c ^ k • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ]
      show (A ^ k) (A v) = _
      rw [h, map_smul, ih, smul_smul, pow_succ, mul_comm]
  have hA := NormedSpace.expSeries_summable' (𝕂 := ℂ) A
  have hc := NormedSpace.expSeries_summable' (𝕂 := ℂ) c
  have e1 : NormedSpace.exp A = ∑' k : ℕ, ((k.factorial : ℂ)⁻¹) • A ^ k :=
    congr_fun (NormedSpace.exp_eq_tsum ℂ) A
  have e2 : NormedSpace.exp c = ∑' k : ℕ, ((k.factorial : ℂ)⁻¹) • c ^ k :=
    congr_fun (NormedSpace.exp_eq_tsum ℂ) c
  rw [e1, e2]
  have e3 := ContinuousLinearMap.map_tsum (ContinuousLinearMap.apply ℂ E v) hA
  simp only [ContinuousLinearMap.apply_apply] at e3
  rw [e3]
  simp only [_root_.smul_apply, hpow, smul_smul]
  exact Summable.tsum_smul_const hc v

lemma ktint_inK (ε : Fin n → Bool) (a : Fin n) :
    inK ε (Complex.I • Matrix.single a a (1 : ℂ)) := by
  have hc : Commute (Complex.I • Matrix.single a a (1 : ℂ)) (Jm ε) := by
    apply Commute.smul_left
    ext i j
    simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.single_apply]
    by_cases h : a = i ∧ a = j
    · obtain ⟨rfl, rfl⟩ := h
      simp
    · simp [h]
  refine ⟨?_, hc.eq⟩
  unfold inG
  have hs : (Complex.I • Matrix.single a a (1 : ℂ))ᴴ = -(Complex.I • Matrix.single a a (1 : ℂ)) := by
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_single, star_one, Complex.star_def,
      Complex.conj_I, neg_smul]
  rw [hs, Matrix.neg_mul, hc.eq, neg_add_cancel]

lemma ktint_exp_two_pi (a : Fin n) :
    NormedSpace.exp (((2 * Real.pi : ℝ) : ℂ) • (Complex.I • Matrix.single a a (1 : ℂ))) =
      (1 : Matrix (Fin n) (Fin n) ℂ) := by
  have hd : ((2 * Real.pi : ℝ) : ℂ) • (Complex.I • Matrix.single a a (1 : ℂ)) =
      Matrix.diagonal (fun i => if i = a then 2 * (Real.pi : ℂ) * Complex.I else 0) := by
    ext i j
    simp only [Matrix.smul_apply, Matrix.single_apply, Matrix.diagonal_apply, smul_eq_mul]
    by_cases h : a = i ∧ a = j
    · obtain ⟨rfl, rfl⟩ := h
      push_cast
      simp only [and_self, if_true, mul_one]
    · rw [if_neg h]
      by_cases hij : i = j
      · subst hij
        have hia : i ≠ a := fun e => h ⟨e.symm, e.symm⟩
        simp [hia]
      · simp [hij]
  rw [hd, Matrix.exp_diagonal, Pi.exp_def, ← Matrix.diagonal_one]
  congr 1
  funext i
  by_cases hi : i = a
  · simp only [hi, if_true, ← Complex.exp_eq_exp_ℂ, Complex.exp_two_pi_mul_I]
  · simp only [hi, if_false, NormedSpace.exp_zero]

theorem kType_int {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) : ∀ a, ∃ m : ℤ, Λ a = m := by
  intro a
  have hX := ktint_inK ε a
  obtain ⟨γ, hγ⟩ := exists_curve ε hX
  have hop := KType.op_curve T hX γ hγ (2 * Real.pi)
  have h1 : γ (2 * Real.pi) = 1 := by
    apply onep_KG_ext
    rw [hγ, ktint_exp_two_pi]
    rfl
  have hw : (((2 * Real.pi : ℝ) : ℂ) • T.dτ (Complex.I • Matrix.single a a (1 : ℂ))) T.w =
      (((2 * Real.pi : ℝ) : ℂ) * (Complex.I * (Λ a : ℂ))) • T.w := by
    rw [_root_.smul_apply, map_smul, _root_.smul_apply, T.w_wt, smul_smul, smul_smul, mul_assoc]
  have key := ktint_exp_apply_of_eig _ _ _ hw
  rw [← hop, h1] at key
  have hone : T.op 1 = 1 := by
    simp [KType.op]
  rw [hone] at key
  change T.w = _ at key
  have hw0 : T.w ≠ 0 := by
    intro h
    have := T.w_norm
    rw [h, norm_zero] at this
    exact zero_ne_one this
  have he : NormedSpace.exp (((2 * Real.pi : ℝ) : ℂ) * (Complex.I * (Λ a : ℂ))) = 1 := by
    by_contra hne
    have h2 : (1 - NormedSpace.exp (((2 * Real.pi : ℝ) : ℂ) * (Complex.I * (Λ a : ℂ)))) • T.w = 0 := by
      rw [sub_smul, one_smul, ← key, sub_self]
    rcases smul_eq_zero.mp h2 with h3 | h3
    · exact hne (sub_eq_zero.mp h3).symm
    · exact hw0 h3
  rw [← Complex.exp_eq_exp_ℂ, Complex.exp_eq_one_iff] at he
  obtain ⟨m, hm⟩ := he
  refine ⟨m, ?_⟩
  have hpi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Complex.I_ne_zero, Real.pi_ne_zero]
  have h4 : (Λ a : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) = (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    rw [← hm]
    push_cast
    ring
  have h5 : (Λ a : ℂ) = ((m : ℝ) : ℂ) := by
    rw [mul_right_cancel₀ hpi h4]
    push_cast
    rfl
  exact_mod_cast h5

end ReciprocityTheory.ChartRestriction.DS.HW
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PieriRules.LowComp
section
noncomputable section

open Matrix Finset

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

def lowCompLin {n : ℕ} (μ : Fin n → ℝ) : ℝ :=
  ∑ c : Fin n, ((c : ℕ) : ℝ) * μ c

theorem lowComp_tensAct_apply {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {ι : Type*}
    [Fintype ι] {n : ℕ} (A : Fin n → Fin n → Module.End ℂ V) (M : Fin n → Fin n → Matrix ι ι ℂ)
    (a b : Fin n) (x : PiLp 2 (fun _ : ι => V)) (i : ι) :
    tensAct A M a b x i = A a b (x i) + ∑ j, M a b i j • x j := by
  simp [tensAct]

theorem lowComp_entry_wt {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} {ε : Fin n → Bool}
    {M : Fin n → Fin n → Matrix ι ι ℂ} {γ : ι → Fin n → ℝ}
    (hM : Formalism.REAL.KRel ε M) (hd : ∀ a, M a a = Matrix.diagonal fun i => ((γ i a : ℝ) : ℂ))
    {a b : Fin n} (hab : a < b) (he : ε a = ε b) {j k : ι} (hne : M a b j k ≠ 0) (c : Fin n) :
    γ k c = γ j c + ((if c = b then 1 else 0) - (if c = a then 1 else 0)) := by
  have h := congrFun (congrFun (hM a b c c he rfl) j) k
  rw [hd c] at h
  simp only [Matrix.sub_apply, Matrix.mul_diagonal, Matrix.diagonal_mul] at h
  have hba : b ≠ a := ne_of_gt hab
  have key : ((γ k c : ℝ) : ℂ) - ((γ j c : ℝ) : ℂ) =
      (((if c = b then 1 else 0) - (if c = a then 1 else 0) : ℝ) : ℂ) := by
    by_cases hcb : c = b
    · subst hcb
      have hca : ¬ c = a := hba
      simp only [if_neg hca, ite_true, Matrix.zero_apply, sub_zero] at h
      simp only [if_neg hca]
      apply mul_left_cancel₀ hne
      push_cast
      linear_combination h
    · by_cases hca : c = a
      · subst hca
        simp only [if_neg (Ne.symm hcb), ite_true, Matrix.zero_apply, zero_sub] at h
        simp only [if_neg hcb]
        apply mul_left_cancel₀ hne
        push_cast
        linear_combination h
      · simp only [if_neg (Ne.symm hcb), if_neg hca, Matrix.zero_apply, sub_zero] at h
        simp only [if_neg hcb, if_neg hca]
        apply mul_left_cancel₀ hne
        push_cast
        linear_combination h
  have key' : ((γ k c - γ j c : ℝ) : ℂ) =
      (((if c = b then 1 else 0) - (if c = a then 1 else 0) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sub (γ k c)]; exact key
  have := Complex.ofReal_injective key'
  linarith

theorem lowComp_lin_entry {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} {ε : Fin n → Bool}
    {M : Fin n → Fin n → Matrix ι ι ℂ} {γ : ι → Fin n → ℝ}
    (hM : Formalism.REAL.KRel ε M) (hd : ∀ a, M a a = Matrix.diagonal fun i => ((γ i a : ℝ) : ℂ))
    {a b : Fin n} (hab : a < b) (he : ε a = ε b) {j k : ι} (hne : M a b j k ≠ 0) :
    lowCompLin (γ k) = lowCompLin (γ j) + (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) := by
  have hk := lowComp_entry_wt hM hd hab he hne
  unfold lowCompLin
  simp only [hk, mul_add, mul_sub, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp

theorem lowComp : LowCompStatement := by
  intro V _ _ n ε A ι _ _ M γ hM hd ν x hx hhw
  classical
  obtain ⟨hwt, hup⟩ := hhw
  set S : Finset ι := Finset.univ.filter (fun i => x i ≠ 0) with hS
  have hSne : S.Nonempty := by
    by_contra h
    apply hx
    ext i
    by_contra hi
    exact h ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, by simpa using hi⟩⟩
  obtain ⟨i0, hi0, hmax⟩ := S.exists_max_image (fun i => lowCompLin (γ i)) hSne
  refine ⟨γ i0, ⟨i0, rfl, (Finset.mem_filter.1 hi0).2⟩, ?_⟩
  intro j hj
  constructor
  · intro c
    have h := congrArg (fun y : PiLp 2 (fun _ : ι => V) => y j) (hwt c)
    simp only [lowComp_tensAct_apply, hd c, Matrix.diagonal_apply, ite_smul, zero_smul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true, PiLp.smul_apply] at h
    rw [Pi.sub_apply, Complex.ofReal_sub, sub_smul, ← h, hj]
    abel
  · intro a b hab he
    have h := congrArg (fun y : PiLp 2 (fun _ : ι => V) => y j) (hup a b hab he)
    simp only [lowComp_tensAct_apply, PiLp.zero_apply] at h
    have hsum : ∑ k, M a b j k • x k = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      by_cases hne : M a b j k = 0
      · simp [hne]
      · have hxk : x k = 0 := by
          by_contra hxk
          have hle := hmax k (Finset.mem_filter.2 ⟨Finset.mem_univ _, hxk⟩)
          have hl := lowComp_lin_entry hM hd hab he hne
          rw [hj] at hl
          have hab' : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hab
          linarith
        simp [hxk]
    rw [hsum, add_zero] at h
    exact h

end ReciprocityTheory.ChartRestriction.DS.HW
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PieriRules.PPlusPWtInjective
section
noncomputable section

open Matrix Finset

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem pPlus_fst_ne_snd {ε : Fin n → Bool} {β : Bool} (p : pIdx ε β) : p.1.1 ≠ p.1.2 := by
  intro h
  obtain ⟨h1, h2⟩ := p.2
  rw [h] at h1
  rw [h1] at h2
  cases β <;> simp at h2

theorem pPlus_pAdM_diag (ε : Fin n → Bool) (β : Bool) (a : Fin n) :
    pAdM ε β a a = Matrix.diagonal fun p => ((pWt ε β p a : ℝ) : ℂ) := by
  ext p q
  by_cases hpq : p = q
  · subst hpq
    simp only [pAdM, pWt, Pi.single_apply, Pi.sub_apply, Matrix.diagonal_apply_eq, and_true, and_self]
    by_cases h1 : p.1.1 = a <;> by_cases h2 : p.1.2 = a
    · exact absurd (h1.trans h2.symm) (pPlus_fst_ne_snd p)
    · rw [if_pos h1, if_neg h2, if_pos h1.symm, if_neg (Ne.symm h2)]; simp
    · rw [if_neg h1, if_pos h2, if_neg (Ne.symm h1), if_pos h2.symm]; simp
    · rw [if_neg h1, if_neg h2, if_neg (Ne.symm h1), if_neg (Ne.symm h2)]; simp
  · rw [Matrix.diagonal_apply_ne _ hpq]
    have h1 : ¬ (p.1.1 = a ∧ q.1.1 = a ∧ p.1.2 = q.1.2) := fun h =>
      hpq (Subtype.ext (Prod.ext (h.1.trans h.2.1.symm) h.2.2))
    have h2 : ¬ (q.1.2 = a ∧ p.1.2 = a ∧ p.1.1 = q.1.1) := fun h =>
      hpq (Subtype.ext (Prod.ext h.2.2 (h.2.1.trans h.1.symm)))
    simp only [pAdM, if_neg h1, if_neg h2, sub_self]

theorem pPlus_pWt_injective (ε : Fin n → Bool) (β : Bool) : Function.Injective (pWt ε β) := by
  intro p q h
  have hp := pPlus_fst_ne_snd p
  have e1 := congrFun h p.1.1
  have e2 := congrFun h p.1.2
  simp only [pWt, Pi.sub_apply, Pi.single_apply] at e1 e2
  rw [if_pos trivial, if_neg hp] at e1
  rw [if_neg (Ne.symm hp), if_pos trivial] at e2
  have h1 : p.1.1 = q.1.1 := by
    by_contra hne
    rw [if_neg hne] at e1
    split_ifs at e1 <;> norm_num at e1
  have h2 : p.1.2 = q.1.2 := by
    by_contra hne
    rw [if_neg hne] at e2
    split_ifs at e2 <;> norm_num at e2
  exact Subtype.ext (Prod.ext h1 h2)

theorem pPlus_card_eq_one (ε : Fin n → Bool) (β : Bool) (Λ : Fin n → ℝ) (p : pIdx ε β) :
    Nat.card {q : pIdx ε β // Λ + pWt ε β p = Λ + pWt ε β q} = 1 :=
  Nat.card_eq_one_iff_exists.mpr
    ⟨⟨p, rfl⟩, fun q => Subtype.ext (pPlus_pWt_injective ε β (add_left_cancel q.2).symm)⟩

theorem pPlus_of_parts (hcount : PieriCountStatement) (htens : TensHWStatement)
    (hkt : KTypeIntDomStatement) (hws : WeylSumPStatement)
    (hρ : ∀ (n : ℕ) (ε : Fin n → Bool) (β : Bool),
      ∃ (ρ : KG ε →* unitary (Matrix (pIdx ε β) (pIdx ε β) ℂ))
        (dρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (pIdx ε β) (pIdx ε β) ℂ),
        Continuous (fun k : KG ε =>
          ((ρ k : unitary (Matrix (pIdx ε β) (pIdx ε β) ℂ)) : Matrix (pIdx ε β) (pIdx ε β) ℂ)) ∧
        (∀ X, inK ε X → ∀ γ : ℝ → KG ε, (∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) →
          ∀ i j, HasDerivAt (fun t : ℝ =>
            ((ρ (γ t) : unitary (Matrix (pIdx ε β) (pIdx ε β) ℂ)) : Matrix (pIdx ε β) (pIdx ε β) ℂ) i j)
            (dρ X i j) 0) ∧
        ∀ a b, dρ (Matrix.single a b 1) = pAdM ε β a b)
    (hrel : ∀ (n : ℕ) (ε : Fin n → Bool) (β : Bool), Formalism.REAL.KRel ε (pAdM ε β)) :
    PPlusStatement := by
  intro n ε β Λ T
  obtain ⟨ρ, dρ, hcont, hder, hsingle⟩ := hρ n ε β
  have hfun : (fun a b => dρ (Matrix.single a b 1)) = pAdM ε β := by
    funext a b
    exact hsingle a b
  obtain ⟨hint, hdom⟩ := hkt n ε Λ T
  obtain ⟨hsum, hvan⟩ := hws n ε β Λ hint hdom
  have hc := hcount n ε Λ T (pIdx ε β) ρ dρ (pWt ε β) hcont hder
    (by rw [hfun]; exact hrel n ε β)
    (fun a => by rw [hsingle]; exact pPlus_pAdM_diag ε β a) (pPlus_pWt_injective ε β)
    (by rw [hsum, Nat.card_eq_fintype_card]) hvan
  rw [hfun] at hc
  obtain ⟨hexist, hall⟩ := hc
  have ht := htens T.V n ε (kunits T) Λ T.w (pIdx ε β) (pAdM ε β) (pWt ε β) (KType.kRel T) (KType.kUnit T)
    (KType.kHighest_w T) (KType.kSpan_eq_top T) (hrel n ε β) (pPlus_pAdM_diag ε β)
  refine ⟨hall, fun p => ?_, hexist⟩
  calc Module.finrank ℂ (khwSub ε (tensAct (kunits T) (pAdM ε β)) (Λ + pWt ε β p))
      ≤ Nat.card {q : pIdx ε β // Λ + pWt ε β p = Λ + pWt ε β q} := (ht.2 _).2
    _ = 1 := pPlus_card_eq_one ε β Λ p

end ReciprocityTheory.ChartRestriction.DS.HW
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PieriRules.StTest
section
noncomputable section

open Matrix Finset

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

theorem pieriSt_mem_khwSub_iff {W : Type*} [AddCommGroup W] [Module ℂ W] {n : ℕ} (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ W) (ν : Fin n → ℝ) (v : W) :
    v ∈ khwSub ε E ν ↔ Formalism.REAL.KHighest ε E ν v := by
  simp only [khwSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker]
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, sub_eq_zero, Formalism.REAL.KHighest,
    Formalism.REAL.IsWeight]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun a => by simpa using h1 a, fun a b hab he => h2 a b ⟨hab, he⟩⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun a => by simpa using h1 a, fun a b h => h2 a b h.1 h.2⟩

theorem pieriSt_isKHWVec_iff {W : Type*} [AddCommGroup W] [Module ℂ W] {n : ℕ} (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ W) (μ : Fin n → ℝ) (v : W) :
    IsKHWVec ε E μ v ↔ Formalism.REAL.KHighest ε E μ v := Iff.rfl

theorem pieriSt_tensAct_apply {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {ι : Type*}
    [Fintype ι] {n : ℕ} (A : Fin n → Fin n → Module.End ℂ V) (M : Fin n → Fin n → Matrix ι ι ℂ)
    (a b : Fin n) (x : PiLp 2 (fun _ : ι => V)) (i : ι) :
    tensAct A M a b x i = A a b (x i) + ∑ j, M a b i j • x j := by
  simp [tensAct]

theorem pieriSt_kRel_stdM {n : ℕ} (ε : Fin n → Bool) : Formalism.REAL.KRel ε (stdM n) := by
  intro a b c d _ _
  simp only [stdM]
  by_cases h1 : b = c <;> by_cases h2 : d = a
  · subst h1 h2; simp [Matrix.single_mul_single_same]
  · subst h1; simp [Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne, h2]
  · subst h2; simp [Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne, h1]
  · simp [Matrix.single_mul_single_of_ne, h1, h2]

theorem pieriSt_stdM_diag {n : ℕ} (a : Fin n) :
    stdM n a a = Matrix.diagonal fun i => ((stdWt n i a : ℝ) : ℂ) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    by_cases hai : a = i
    · subst hai; simp [stdM, stdWt]
    · simp [stdM, stdWt, hai, Pi.single_apply]
  · simp [stdM, Matrix.single_apply, hij]
    intro h1 h2; exact hij (h1.symm.trans h2)

theorem pieriSt_tensHW_inhabited {n : ℕ} (ε : Fin n → Bool) :
    Formalism.REAL.KRel ε (0 : Fin n → Fin n → Module.End ℂ ℂ) ∧
    Formalism.REAL.KUnit ε (0 : Fin n → Fin n → Module.End ℂ ℂ) ∧
    Formalism.REAL.KHighest ε (0 : Fin n → Fin n → Module.End ℂ ℂ) 0 (1 : ℂ) ∧
    Formalism.REAL.kSpan ε (0 : Fin n → Fin n → Module.End ℂ ℂ) (1 : ℂ) = ⊤ ∧
    Formalism.REAL.KRel ε (stdM n) ∧
    (∀ a, stdM n a a = Matrix.diagonal fun i => ((stdWt n i a : ℝ) : ℂ)) := by
  refine ⟨?_, ?_, ?_, ?_, pieriSt_kRel_stdM ε, pieriSt_stdM_diag⟩
  · intro a b c d _ _; simp
  · intro a b _ x y; simp
  · exact ⟨fun a => by simp, fun a b _ _ => by simp⟩
  · refine eq_top_iff.mpr fun v _ => ?_
    simp only [Formalism.REAL.kSpan, Submodule.mem_sInf, Set.mem_ofPred_eq]
    rintro S ⟨h1, _⟩
    have : v = v • (1 : ℂ) := by simp
    rw [this]
    exact S.smul_mem v h1

theorem pieriSt_count_inhabited {n : ℕ} (ε : Fin n → Bool) :
    Continuous (fun k : KG ε =>
      (((1 : KG ε →* unitary (Matrix Unit Unit ℂ)) k : unitary (Matrix Unit Unit ℂ)) : Matrix Unit Unit ℂ)) ∧
    (∀ X, inK ε X → ∀ γ : ℝ → KG ε, (∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) →
      ∀ i j, HasDerivAt (fun t : ℝ =>
        (((1 : KG ε →* unitary (Matrix Unit Unit ℂ)) (γ t) : unitary (Matrix Unit Unit ℂ)) :
          Matrix Unit Unit ℂ) i j)
        ((0 : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix Unit Unit ℂ) X i j) 0) ∧
    Formalism.REAL.KRel ε (fun a b => (0 : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix Unit Unit ℂ) (Matrix.single a b 1)) ∧
    (∀ a, (0 : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix Unit Unit ℂ) (Matrix.single a a 1) =
      Matrix.diagonal fun i => (((fun _ : Unit => (0 : Fin n → ℝ)) i a : ℝ) : ℂ)) ∧
    Function.Injective (fun _ : Unit => (0 : Fin n → ℝ)) ∧
    (∑ i : Unit, weylK ε ((0 : Fin n → ℝ) + (fun _ : Unit => (0 : Fin n → ℝ)) i) =
      (Fintype.card Unit : ℝ) * weylK ε 0) ∧
    (∀ i : Unit, ¬ KDom ε ((0 : Fin n → ℝ) + (fun _ : Unit => (0 : Fin n → ℝ)) i) →
      weylK ε ((0 : Fin n → ℝ) + (fun _ : Unit => (0 : Fin n → ℝ)) i) = 0) ∧
    Nonempty (KType ε 0) := by
  refine ⟨?_, ?_, ?_, ?_, fun a b _ => Subsingleton.elim a b, ?_, ?_, ⟨trivialKType ε⟩⟩
  · simp only [MonoidHom.one_apply]; exact continuous_const
  · intro X _ γ _ i j
    simp only [MonoidHom.one_apply, LinearMap.zero_apply]
    exact hasDerivAt_const _ _
  · intro a b c d _ _; simp
  · intro a; ext i j; simp
  · simp
  · intro i h
    exact absurd (fun a b _ _ => by simp) h

theorem pieriSt_cartan_inhabited {n : ℕ} (ε : Fin n → Bool) :
    (∀ a : Fin n, ((0 : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix Unit Unit ℂ) (Matrix.single a a 1)) *ᵥ
      (fun _ : Unit => (1 : ℂ)) = (((0 : Fin n → ℝ) a : ℝ) : ℂ) • (fun _ : Unit => (1 : ℂ))) ∧
    (∀ a b : Fin n, a < b → ε a = ε b →
      ((0 : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix Unit Unit ℂ) (Matrix.single a b 1)) *ᵥ
        (fun _ : Unit => (1 : ℂ)) = 0) ∧
    (fun _ : Unit => (1 : ℂ)) ≠ 0 ∧
    Formalism.REAL.KHighest ε (kunits (trivialKType ε)) 0 (trivialKType ε).w ∧ (trivialKType ε).w ≠ 0 := by
  refine ⟨fun a => by ext; simp, fun a b _ _ => by ext; simp, fun h => by simpa using congrFun h (), ?_, ?_⟩
  · exact ⟨fun a => (trivialKType ε).w_wt a, fun a b hab he => (trivialKType ε).w_hw a b hab he⟩
  · show (1 : ℂ) ≠ 0; exact one_ne_zero

end ReciprocityTheory.ChartRestriction.DS.HW
end
end

