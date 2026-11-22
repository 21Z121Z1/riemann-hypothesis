import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.Bundle0013
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.Bundle0001
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.Imports
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.IoBlockSupported

-- bundled from Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.BFCoarse
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

section

variable (C0 CE1 CE2 : ℝ) (X : Loc) [NeZero X.m] (j : Fin (numSeg X.TT))

theorem symbol_variable_first_columns (b : SegBlock (segS X.TT j) X.m) (v : BV C0 CE1 CE2 X j) (h : mu0 C0 CE1 CE2 X j b v ≠ 0) :
    (symVar C0 CE1 CE2 X j v).2 = 0 ∨ (symVar C0 CE1 CE2 X j v).2 = Fin.succ 0 := by
  rcases v with ⟨a, c⟩ | ⟨l, bo⟩
  · right
    have hc : c = 0 := by
      by_contra hc
      exact h (by show mu0F C0 CE1 CE2 X j b (Sum.inl (a, c)) = 0; simp [mu0F, hc])
    subst hc
    simp only [symVar]
    split_ifs <;> rfl
  · left
    simp only [symVar]
    split_ifs <;> rfl

theorem card_supp_le (b : SegBlock (segS X.TT j) X.m) (x : X.TT × Bool) :
    open Classical in
    (Finset.univ.filter (fun v : BV C0 CE1 CE2 X j => (symVar C0 CE1 CE2 X j v).1 = x ∧
      mu0 C0 CE1 CE2 X j b v ≠ 0)).card ≤ 2 := by
  classical
  have hsub : (Finset.univ.filter (fun v : BV C0 CE1 CE2 X j => (symVar C0 CE1 CE2 X j v).1 = x ∧
      mu0 C0 CE1 CE2 X j b v ≠ 0)) ⊆
      (Finset.univ.filter (fun v : BV C0 CE1 CE2 X j => symVar C0 CE1 CE2 X j v = (x, 0))) ∪
      (Finset.univ.filter (fun v : BV C0 CE1 CE2 X j => symVar C0 CE1 CE2 X j v = (x, Fin.succ 0))) := by
    intro v hv
    obtain ⟨h1, h2⟩ := (Finset.mem_filter.1 hv).2
    rcases symbol_variable_first_columns C0 CE1 CE2 X j b v h2 with h | h
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, Prod.ext h1 h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, Prod.ext h1 h⟩)
  have hone : ∀ y, (Finset.univ.filter (fun v : BV C0 CE1 CE2 X j => symVar C0 CE1 CE2 X j v = y)).card ≤ 1 := by
    intro y
    refine Finset.card_le_one.2 fun v hv v' hv' => ?_
    exact symVar_inj C0 CE1 CE2 X j (((Finset.mem_filter.1 hv).2).trans ((Finset.mem_filter.1 hv').2).symm)
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ _ := Finset.card_union_le _ _
    _ ≤ 1 + 1 := Nat.add_le_add (hone _) (hone _)

theorem cdeg_le_tdeg (hp : 0 < X.p) (b : SegBlock (segS X.TT j) X.m) (x : X.TT × Bool) :
    cdeg C0 CE1 CE2 X j b x ≤ tdeg C0 CE1 CE2 X j b x := by
  classical
  rw [← sum_fiber C0 CE1 CE2 X j b (mu0 C0 CE1 CE2 X j b) (leading_exponent_homogeneous C0 CE1 CE2 X j b) x]
  set μ0 := mu0 C0 CE1 CE2 X j b
  have hco : ∀ c : Fin (X.m + 1), (μ0.sum fun v n => Finsupp.single (symVar C0 CE1 CE2 X j v)
      (symLev X.p C0 CE1 CE2 X j v * n)) (x, c) =
      ∑ v : BV C0 CE1 CE2 X j, if symVar C0 CE1 CE2 X j v = (x, c) then symLev X.p C0 CE1 CE2 X j v * μ0 v else 0 := by
    intro c
    rw [Finsupp.sum_apply, Finsupp.sum_fintype _ _ (fun v => by simp)]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finsupp.single_apply]
  have hswap : (∑ c : Fin (X.m + 1), ∑ v : BV C0 CE1 CE2 X j,
      (if symVar C0 CE1 CE2 X j v = (x, c) then symLev X.p C0 CE1 CE2 X j v * μ0 v else 0)) =
      ∑ v : BV C0 CE1 CE2 X j, if (symVar C0 CE1 CE2 X j v).1 = x then symLev X.p C0 CE1 CE2 X j v * μ0 v else 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun v _ => ?_
    by_cases h : (symVar C0 CE1 CE2 X j v).1 = x
    · rw [if_pos h, Finset.sum_eq_single (symVar C0 CE1 CE2 X j v).2]
      · rw [if_pos (Prod.ext h rfl : symVar C0 CE1 CE2 X j v = (x, (symVar C0 CE1 CE2 X j v).2))]
      · intro c _ hc
        rw [if_neg (fun e => hc (by rw [e]))]
      · intro hh; exact absurd (Finset.mem_univ _) hh
    · rw [if_neg h]
      exact Finset.sum_eq_zero fun c _ => if_neg (fun e => h (by rw [e]))
  calc (∑ v ∈ Finset.univ.filter (fun v : BV C0 CE1 CE2 X j => (symVar C0 CE1 CE2 X j v).1 = x), μ0 v)
      = ∑ v : BV C0 CE1 CE2 X j, if (symVar C0 CE1 CE2 X j v).1 = x then μ0 v else 0 := Finset.sum_filter _ _
    _ ≤ ∑ v : BV C0 CE1 CE2 X j, if (symVar C0 CE1 CE2 X j v).1 = x then symLev X.p C0 CE1 CE2 X j v * μ0 v else 0 := by
        refine Finset.sum_le_sum fun v _ => ?_
        split_ifs
        · exact Nat.le_mul_of_pos_left _ (symLev_pos C0 CE1 CE2 X hp j v)
        · exact le_rfl
    _ = ∑ c : Fin (X.m + 1), (μ0.sum fun v n => Finsupp.single (symVar C0 CE1 CE2 X j v)
          (symLev X.p C0 CE1 CE2 X j v * n)) (x, c) := by
        rw [Finset.sum_congr rfl fun c _ => hco c, hswap]
    _ ≤ tdeg C0 CE1 CE2 X j b x := by
        unfold tdeg multideg ioExp
        refine Finset.sum_le_sum fun c _ => ?_
        rw [Finsupp.add_apply]
        exact Nat.le_add_left _ _

end

theorem coarseMultAt_of {C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ} (hO : OPlusAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc) :
    CoarseMultAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc := by
  classical
  intro X _ hD1 hH hc j b hb
  have hp : 0 < X.p := hD1.1.pos
  have ho := hO X hD1 hH hc j b hb
  set μ0 := mu0 C0 CE1 CE2 X j b with hμ0
  let F : X.TT × Bool → Finset (BV C0 CE1 CE2 X j) :=
    fun x => Finset.univ.filter (fun v : BV C0 CE1 CE2 X j => (symVar C0 CE1 CE2 X j v).1 = x)
  let s : X.TT × Bool → Finset (BV C0 CE1 CE2 X j) := fun x => (F x).filter (fun v => μ0 v ≠ 0)
  have hfac : ∀ x, (cdeg C0 CE1 CE2 X j b x).factorial =
      (∏ v ∈ F x, (μ0 v).factorial) * Nat.multinomial (s x) μ0 := by
    intro x
    rw [← sum_fiber C0 CE1 CE2 X j b μ0 (leading_exponent_homogeneous C0 CE1 CE2 X j b) x]
    show (∑ v ∈ F x, μ0 v).factorial = _
    rw [← Finset.sum_filter_ne_zero, ← Finset.prod_filter_of_ne (p := fun v => μ0 v ≠ 0)
      (fun v _ hv h0 => hv (by rw [h0]; rfl))]
    exact (Nat.multinomial_spec _ _).symm
  have hE : expFact μ0 = ∏ x : X.TT × Bool, ∏ v ∈ F x, (μ0 v).factorial := by
    unfold expFact
    rw [Finsupp.prod_fintype _ _ (fun _ => rfl)]
    exact (Finset.prod_fiberwise Finset.univ (fun v => (symVar C0 CE1 CE2 X j v).1) (fun v => (μ0 v).factorial)).symm
  have hE0 : expFact μ0 ≠ 0 := by
    unfold expFact; exact Finsupp.prod_ne_zero_iff.2 fun _ _ => Nat.factorial_ne_zero _
  have hM0 : ∀ x ∈ (Finset.univ : Finset (X.TT × Bool)), Nat.multinomial (s x) μ0 ≠ 0 :=
    fun x _ => (Nat.multinomial_pos _ _).ne'
  rw [Finset.prod_congr rfl (fun x _ => hfac x), Finset.prod_mul_distrib, ← hE,
    Nat.factorization_mul hE0 (Finset.prod_ne_zero_iff.2 hM0), Finsupp.add_apply, Nat.factorization_prod hM0,
    Finsupp.finsetSum_apply]
  refine Nat.add_le_add_left ?_ _
  calc (∑ x : X.TT × Bool, (Nat.multinomial (s x) μ0).factorization X.p)
      ≤ ∑ x : X.TT × Bool, Nat.log X.p (cdeg C0 CE1 CE2 X j b x) := by
        refine Finset.sum_le_sum fun x _ => (multinomial_val X.p (s x) μ0).trans ?_
        have hc2 : (s x).card ≤ 2 := by
          have := card_supp_le C0 CE1 CE2 X j b x
          simp only [s, F, Finset.filter_filter]
          convert this
        rw [Finset.sum_filter_ne_zero]
        show ((s x).card - 1) * Nat.log X.p (∑ v ∈ F x, μ0 v) ≤ _
        rw [sum_fiber C0 CE1 CE2 X j b μ0 (leading_exponent_homogeneous C0 CE1 CE2 X j b) x]
        calc ((s x).card - 1) * Nat.log X.p (cdeg C0 CE1 CE2 X j b x) ≤ 1 * Nat.log X.p (cdeg C0 CE1 CE2 X j b x) :=
              Nat.mul_le_mul_right _ (by omega)
          _ = _ := one_mul _
    _ ≤ ∑ x : X.TT × Bool, Nat.log X.p (tdeg C0 CE1 CE2 X j b x) :=
        Finset.sum_le_sum fun x _ => Nat.log_mono_right (cdeg_le_tdeg C0 CE1 CE2 X j hp b x)
    _ = lgSeg X j := by
        rw [sum_tdeg C0 CE1 CE2 X j (Nat.log X.p) (Nat.log_zero_right _) b hb ho]
        unfold lgSeg
        rw [Finset.sum_add_distrib]

end Formalism.MainNotions.ColumnSystems.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.IoBlockEqSum
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

section

variable (C0 CE1 CE2 : ℝ) (X : Loc) [NeZero X.m] (j : Fin (numSeg X.TT))

theorem hom_of_ssz {O : Type} [CommRing O] [IsDomain O] (b : SegBlock (segS X.TT j) X.m) (mm : ℝ)
    (u : MvPolynomial (BV C0 CE1 CE2 X j) (KK O)) (hu : u ∈ sszB O C0 CE1 CE2 X j mm b) (μ : BV C0 CE1 CE2 X j →₀ ℕ)
    (hμ : μ ∈ u.support) : HomExp C0 CE1 CE2 X j b μ := by
  intro ω ωL hB
  obtain ⟨h1, h2, h3⟩ := hB
  have hw := ssz_wh O X.p _ _ _ mm b ω ωL h1 h2 h3 u hu (mem_support_iff.1 hμ)
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ (fun i c => c • ω i) (fun _ => zero_smul _ _)] at hw
  simpa [smul_eq_mul] using hw

theorem sep (hp : 0 < X.p) (b b' : SegBlock (segS X.TT j) X.m)
    (hb : Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b)
    (hb' : Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b') (μ μ' : BV C0 CE1 CE2 X j →₀ ℕ)
    (hμ : HomExp C0 CE1 CE2 X j b μ) (hμ' : HomExp C0 CE1 CE2 X j b' μ')
    (he : ioExp C0 CE1 CE2 X j b μ = ioExp C0 CE1 CE2 X j b' μ') : b = b' := by
  classical
  have hrz : ∀ i c, b.rz i c = b'.rz i c := by
    intro i c
    have h1 := ioExp_mod C0 CE1 CE2 X j b hb μ i true c
    have h2 := ioExp_mod C0 CE1 CE2 X j b' hb' μ' i true c
    rw [he, if_pos rfl] at h1
    rw [if_pos rfl] at h2
    exact h1.symm.trans h2
  have hry : ∀ i c, b.ry i c = b'.ry i c := by
    intro i c
    have h1 := ioExp_mod C0 CE1 CE2 X j b hb μ i false c
    have h2 := ioExp_mod C0 CE1 CE2 X j b' hb' μ' i false c
    rw [he, if_neg Bool.false_ne_true] at h1
    rw [if_neg Bool.false_ne_true] at h2
    exact h1.symm.trans h2
  have hrz' : b.rz = b'.rz := funext fun i => funext fun c => hrz i c
  have hry' : b.ry = b'.ry := funext fun i => funext fun c => hry i c
  have hA : ∀ i, coarseA X.p (X.seg C0 CE1 CE2 j) b i = coarseA X.p (X.seg C0 CE1 CE2 j) b' i := by
    intro i; unfold coarseA; rw [hrz']
  have hC : ∀ i, coarseC X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b i =
      coarseC X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b' i := by
    intro i; unfold coarseC; rw [hry']
  have hS : ∀ i : Fin (segS X.TT j), (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma → b.w i = b'.w i ∧ b.sg i = b'.sg i := by
    intro i hi
    have hP : 0 < (X.seg C0 CE1 CE2 j).P X.p i := pow_pos hp _
    have k1 := hb.2.2.1 i hi
    have k1' := hb'.2.2.1 i hi
    have v1 := congrArg (fun e => e ((topOdd X j i, true), (0 : Fin (X.m + 1)))) he
    have v2 := congrArg (fun e => e ((topOdd X j i, false), (0 : Fin (X.m + 1)))) he
    simp only [ioExp, Finsupp.add_apply] at v1 v2
    rw [coarse_spec C0 CE1 CE2 X j μ i true hi, coarse_spec C0 CE1 CE2 X j μ' i true hi, add_zero, add_zero,
      baseExp_odd, baseExp_odd, if_pos rfl, if_pos rfl, if_pos (⟨hi, rfl⟩ : _ ∧ _), if_pos (⟨hi, rfl⟩ : _ ∧ _),
      if_pos rfl, if_pos rfl, hrz i 0, hA i] at v1
    rw [coarse_spec C0 CE1 CE2 X j μ i false hi, coarse_spec C0 CE1 CE2 X j μ' i false hi, add_zero, add_zero,
      baseExp_odd, baseExp_odd, if_neg Bool.false_ne_true, if_neg Bool.false_ne_true, if_pos (⟨hi, rfl⟩ : _ ∧ _),
      if_pos (⟨hi, rfl⟩ : _ ∧ _), if_neg Bool.false_ne_true, if_neg Bool.false_ne_true, hry i 0] at v2
    have w1 := Nat.eq_of_mul_eq_mul_left hP (Nat.add_left_cancel v1)
    have w2 := Nat.eq_of_mul_eq_mul_left hP (Nat.add_left_cancel v2)
    have a1 := k1.2.1
    have a2 := k1'.2.1
    rw [hA i] at a1
    exact ⟨by omega, w2⟩
  have hbase : baseExp C0 CE1 CE2 X j b = baseExp C0 CE1 CE2 X j b' := by
    unfold baseExp
    rw [hrz', hry']
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs with hi
    · rw [(hS i hi).1, (hS i hi).2, hA i]
    · rfl
  have hμμ : μ = μ' := by
    unfold ioExp at he
    rw [hbase] at he
    have h' := add_left_cancel he
    ext v0
    have := DFunLike.congr_fun h' (symVar C0 CE1 CE2 X j v0)
    rw [coarse_eval, coarse_eval] at this
    exact Nat.eq_of_mul_eq_mul_left (symLev_pos C0 CE1 CE2 X hp j v0) this
  subst hμμ
  have ho : ∀ l, b.o (uTop (X.seg C0 CE1 CE2 j) l) = b'.o (uTop (X.seg C0 CE1 CE2 j) l) := by
    intro l
    rw [← omB_ωo C0 CE1 CE2 X j b l, ← omB_ωo C0 CE1 CE2 X j b' l, ← hμ _ _ (ωo_bal C0 CE1 CE2 X j l),
      ← hμ' _ _ (ωo_bal C0 CE1 CE2 X j l)]
  have hoP : b.oPlus = b'.oPlus := by
    rw [← omB_ωp C0 CE1 CE2 X j b, ← omB_ωp C0 CE1 CE2 X j b', ← hμ _ _ (ωp_bal C0 CE1 CE2 X j),
      ← hμ' _ _ (ωp_bal C0 CE1 CE2 X j)]
  have hofun : b.o = b'.o := funext fun i => by
    by_cases hi : (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma
    · rw [(hb.2.2.1 i hi).1, (hb'.2.2.1 i hi).1]
    · have hl : (i : ℕ) - (X.seg C0 CE1 CE2 j).sigma < (X.seg C0 CE1 CE2 j).t := by
        have := i.2; unfold SegData.t; omega
      have e : uTop (X.seg C0 CE1 CE2 j) ⟨(i : ℕ) - (X.seg C0 CE1 CE2 j).sigma, hl⟩ = i :=
        Fin.ext (by show (X.seg C0 CE1 CE2 j).sigma + ((i : ℕ) - (X.seg C0 CE1 CE2 j).sigma) = i; omega)
      rw [← e]
      exact ho _
  have hwfun : b.w = b'.w := funext fun i => by
    by_cases hi : (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma
    · exact (hS i hi).1
    · rw [(hb.2.1 i (not_lt.1 hi)).2.2.1, (hb'.2.1 i (not_lt.1 hi)).2.2.1]
  have hsgfun : b.sg = b'.sg := funext fun i => by
    by_cases hi : (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma
    · exact (hS i hi).2
    · rw [(hb.2.1 i (not_lt.1 hi)).2.2.2, (hb'.2.1 i (not_lt.1 hi)).2.2.2]
  cases b
  cases b'
  simp only at hrz' hry' hofun hwfun hsgfun hoP
  rw [hrz', hry', hofun, hwfun, hsgfun, hoP]

theorem ioBlock_eq_sum (K : Type) [Field K] (b : SegBlock (segS X.TT j) X.m) (t : MvPolynomial (BV C0 CE1 CE2 X j) K) :
    ioBlock K X.p C0 CE1 CE2 X j b t = ∑ μ ∈ t.support, monomial (ioExp C0 CE1 CE2 X j b μ) (t.coeff μ) := by
  let f : MvPolynomial (BV C0 CE1 CE2 X j) K →ₗ[K] MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) K :=
    (LinearMap.mulLeft K (digitMon K C0 CE1 CE2 X j b * sTopMon K X.p C0 CE1 CE2 X j b)).comp
      (aeval (fun v => (MvPolynomial.X (symVar C0 CE1 CE2 X j v) :
        MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) K) ^ symLev X.p C0 CE1 CE2 X j v)).toLinearMap
  have hf : ∀ t, ioBlock K X.p C0 CE1 CE2 X j b t = f t := fun _ => rfl
  conv_lhs => rw [hf, ← t.support_sum_monomial_coeff, map_sum]
  exact Finset.sum_congr rfl fun μ _ => by rw [← hf, ioBlock_monomial]

end

theorem orthAt (C0 CE1 CE2 : ℝ) : OrthAt C0 CE1 CE2 := by
  classical
  intro X _ O _ _ mm hD1 j b b' hb hb' hne s hs s' hs'
  have hp : 0 < X.p := hD1.1.pos
  rw [ioBlock_eq_sum C0 CE1 CE2 X j (KK O) b s, Formalism.MainNotions.G.GLWeightTheory.fock_form_finset_sum _ _ _ (support_sum)]
  refine Finset.sum_eq_zero fun e he => ?_
  obtain ⟨μ, hμ, he'⟩ := Finset.mem_biUnion.1 he
  have hem := support_monomial_subset he'
  rw [Finset.mem_singleton] at hem
  subst hem
  have h0 : coeff (ioExp C0 CE1 CE2 X j b μ) (ioBlock (KK O) X.p C0 CE1 CE2 X j b' s') = 0 := by
    rw [ioBlock_eq_sum C0 CE1 CE2 X j (KK O) b' s', coeff_sum]
    refine Finset.sum_eq_zero fun μ' hμ' => ?_
    rw [coeff_monomial, if_neg]
    intro h
    exact hne (sep C0 CE1 CE2 X j hp b' b hb' hb μ' μ (hom_of_ssz C0 CE1 CE2 X j b' mm s' hs' μ' hμ')
      (hom_of_ssz C0 CE1 CE2 X j b mm s hs μ hμ) h).symm
  rw [h0, mul_zero, zero_mul]

end Formalism.MainNotions.ColumnSystems.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.Loc4DivOf
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial Formalism.MainNotions.LemmaBAlt

def psiRes (X : Loc) [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [Algebra (WF X.p X.n') O] (w : O)
    (g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n')) (j : Fin (numSeg X.TT)) (a : Fin (X.m + 1)) :
    O ⧸ Ideal.span {w} :=
  Ideal.Quotient.mk (Ideal.span {w}) (psiO X.p X.n' O ((topStart X j : X.TT).val.val : ℤ) (g⁻¹ 0 a))

def LocalResidueBound : Prop :=
  ∀ (X : Loc) [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra (WF X.p X.n') O] (S : UniformizedDVR X.p O), S.SqP → D1num X → 2 ≤ numSeg X.TT →
    ∀ (j0 : Fin (numSeg X.TT)) (g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n')), IsGLW g →
      ratPlane X.p X.n' 1 g ≠ ratPlane X.p X.n' 1 1 →
      psiRes X O S.w g j0 0 = 0 ∨ ∃ c : Fin X.m,
        ∏ j : Fin (numSeg X.TT), psiRes X O S.w g j 0 ^ (X.p ^ segG X.TT j - 1) =
          ∏ j : Fin (numSeg X.TT), psiRes X O S.w g j c.succ ^ (X.p ^ segG X.TT j - 1)

theorem map_xvL (X : Loc) [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [Algebra (WF X.p X.n') O] (w : O)
    (g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n')) (j : Fin (numSeg X.TT)) (a : Fin (X.m + 1)) :
    map (Ideal.Quotient.mk (Ideal.span {w})) (xvL X O w g j a) =
      C (psiRes X O w g j a) * MvPolynomial.X ((topStart X j, true), 0) := by
  have hw0 : Ideal.Quotient.mk (Ideal.span {w}) w = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self w)
  unfold xvL psiRes
  rw [map_sum, Finset.sum_eq_single 0]
  · simp [Formalism.MainNotions.LemmaBAlt.dW, Formalism.MainNotions.ColumnSystems.hhLetters]
    try ring
  · intro b _ hb
    have hb1 : 1 ≤ b.val := Nat.one_le_iff_ne_zero.mpr (fun h => hb (Fin.ext h))
    simp [Formalism.MainNotions.LemmaBAlt.dW, Formalism.MainNotions.ColumnSystems.hhLetters, hb1, hw0]
  · intro h
    exact absurd (Finset.mem_univ 0) h

theorem loc4Div_of (h : LocalResidueBound) : LocalDivisibilityBound := by
  intro X _ O _ _ _ _ S hS hD hn j0 g hg hne
  rw [MvPolynomial.C_dvd_iff_map_hom_eq_zero (Ideal.Quotient.mk (Ideal.span {S.w})) S.w
    (fun x => by rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton])]
  unfold locExpr
  simp only [map_mul, map_prod, map_sub, map_pow, map_xvL]
  rcases h X O S hS hD hn j0 g hg hne with h0 | ⟨c, hc⟩
  · rw [h0]
    simp
  · apply mul_eq_zero_of_right
    apply Finset.prod_eq_zero (Finset.mem_univ c)
    simp only [mul_pow, Finset.prod_mul_distrib, ← map_pow, ← map_prod]
    rw [hc, sub_self]

end Formalism.MainNotions.ColumnSystems.Pf
end
end

