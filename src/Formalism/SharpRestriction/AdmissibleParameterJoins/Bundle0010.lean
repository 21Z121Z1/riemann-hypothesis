import Formalism.SharpRestriction.AdmissibleParameterJoins.Bundle0009
import Formalism.SharpRestriction.AdmissibleParameterJoins.DIVfromGLo
import Formalism.SharpRestriction.AdmissibleParameterJoins.Bundle0007
import Formalism.SharpRestriction.GlobalSchurBounds.WachTwistLocalTheory
import Formalism.SharpRestriction.GlobalSchurBounds.Bundle0004
import Formalism.LocalRingCardinality.Bundle0001
import Formalism.SharpRestriction.Divisibility.ChainOperators.Bundle0002

-- bundled from Formalism.SharpRestriction.AdmissibleParameterJoins.DIVfromGLbud
section
noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions

variable {D : D7} {L : SizeData₂ D}

theorem levelPrime_budget_of_fifth {C : ℝ} (h : ∀ u, product_first_zeroth_parts.WeightBudgetBound D u L C) : WeightDegreeSizes.LevelPrimeBudget D L C := by
  unfold WeightDegreeSizes.LevelPrimeBudget
  exact h

theorem setting_fam {eps : ℝ} (Fm : FamP eps) (hT : TuSize Fm) (hDl : DlSize Fm) :
    ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (i : Fm.Ix x) u, product_first_zeroth_parts.HidaSetting (Fm.D x i) u := by
  have key : ∀ X e : ℝ, 256 ≤ X → 0 < e → e < 1 / 52 →
      (4 : ℝ) ≤ X ^ (-(e / 100)) * Real.sqrt (X * X ^ (-(e / 8))) := by
    intro X e hX he he'
    have hX0 : 0 < X := by linarith
    have h1 : X * X ^ (-(e / 8)) = X ^ (1 + -(e / 8)) := by
      rw [Real.rpow_add hX0, Real.rpow_one]
    rw [h1, Real.sqrt_eq_rpow, ← Real.rpow_mul hX0.le, ← Real.rpow_add hX0]
    have h256 : (4 : ℝ) = (256 : ℝ) ^ ((1 : ℝ) / 4) := by
      rw [show (256 : ℝ) = 4 ^ (4 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
      norm_num
    rw [h256]
    calc (256 : ℝ) ^ ((1 : ℝ) / 4) ≤ X ^ ((1 : ℝ) / 4) :=
          Real.rpow_le_rpow (by norm_num) hX (by norm_num)
      _ ≤ X ^ (-(e / 100) + (1 + -(e / 8)) * (1 / 2)) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  obtain ⟨Cn₀, hCn⟩ := numsL_wtsL_fam Fm hT hDl
  obtain ⟨x2, hx2⟩ := hCn Cn₀ le_rfl 3 le_rfl
  obtain ⟨x3, hx3⟩ := hT
  refine ⟨max (max x2 x3) (max (Fm.x1 + 1) 256), fun x hx i u => ?_⟩
  have hxa : x2 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hxb : x3 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx1 : Fm.x1 < x := by
    have : Fm.x1 + 1 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
    linarith
  have h256 : (256 : ℝ) ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  obtain ⟨hN, hW⟩ := hx2 x hxa i
  have hTu := (hx3 x hxb i).1
  have hm : 4 ≤ (Fm.D x i).R.m := by
    have S := Fm.sizes x hx1 i
    have hM : SizeM (Fm.L x i) := S.2.1
    unfold SizeM szTh Scale.delta1 at hM
    have hX : (256 : ℝ) ≤ (Fm.L x i).sc.x := by
      rw [Fm.L_x x i hx1]
      exact h256
    have h4 := key _ _ hX (Fm.L x i).sc.eps_pos (Fm.L x i).sc.eps_lt
    exact_mod_cast h4.trans hM.1
  exact levelPrime_setting_of_sizes le_rfl hN hW hTu hm u

theorem family_levelPrime_budget {eps : ℝ} (Fm : FamP eps) (hT : TuSize Fm) (hDl : DlSize Fm) (hB : product_first_zeroth_parts.BudF Fm) :
    ∃ C x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, WeightDegreeSizes.LevelPrimeBudget (Fm.D x i) (Fm.L x i) C := by
  obtain ⟨x1, hx1⟩ := setting_fam Fm hT hDl
  obtain ⟨C, x0, hB⟩ := hB
  refine ⟨C, max x0 x1, fun x hx i => levelPrime_budget_of_fifth (fun u =>
    hB x (le_trans (le_max_left _ _) hx) i u (hx1 x (le_trans (le_max_right _ _) hx) i u))⟩

theorem gammaDiscriminant_budget_of_sizes {Cn cL CG : ℝ} (hcL : 1 ≤ cL) (hCG : 0 ≤ CG) (hN : NumsL D L Cn cL) (hG : FactDGam D CG) :
    WeightDegreeSizes.StabiliserLogBound D L (4 * CG) := by
  unfold WeightDegreeSizes.StabiliserLogBound
  unfold FactDGam at hG
  intro u
  have hNu := hN u
  unfold flipTwoThree.Nums at hNu
  obtain ⟨hb0, -, -, -, -, hb', -, -, -, -, hNL, -, -, hx2, -, -⟩ := hNu
  have hfk : D.R.f ≤ D.R.k := by
    unfold Ranks.f
    exact D.R.f_le_k
  have hmf : D.R.m ≤ D.R.f := by
    unfold Ranks.f
    exact D.R.m_le_f
  have hm2 : 2 ≤ D.R.m := D.R.two_le_m
  have hkN : D.R.k ≤ D.R.N D.R.m := by
    unfold Ranks.N
    omega
  have hfN : (D.R.f : ℝ) ≤ (D.R.N D.R.m : ℝ) := by exact_mod_cast hfk.trans hkN
  have hf2 : (2 : ℝ) ≤ D.R.f := by exact_mod_cast hm2.trans hmf
  have hm2r : (2 : ℝ) ≤ D.R.m := by exact_mod_cast hm2
  have hN0 : (0 : ℝ) < D.R.N D.R.m := by linarith
  have hx1 := L.sc.one_lt_alt
  have hLr : 1 ≤ L.sc.L := by
    unfold Scale.L
    exact Real.one_le_rpow hx1.le L.sc.eps_pos.le
  have hbb : L.sc.x * L.sc.b / L.sc.x = L.sc.b := by
    field_simp
  rw [hbb] at hb'
  have hT0 : 0 ≤ Real.log ((flipTwoThree.Tu D u : ℕ) : ℝ) := Real.log_natCast_nonneg _
  have hNL' : (D.R.N D.R.m : ℝ) * L.sc.L ≤ L.sc.b := by
    have : (D.R.N D.R.m : ℝ) * L.sc.L ≤ (D.R.N D.R.m : ℝ) * (cL * L.sc.L) := by
      apply mul_le_mul_of_nonneg_left _ hN0.le
      nlinarith
    linarith
  have hlogN : Real.log (D.R.N D.R.m : ℝ) ≤ L.sc.L := by
    have hNb : (D.R.N D.R.m : ℝ) ≤ Real.exp L.sc.L := by
      have : (D.R.N D.R.m : ℝ) ≤ (D.R.N D.R.m : ℝ) * L.sc.L := le_mul_of_one_le_right hN0.le hLr
      have hb : L.sc.b = Real.exp L.sc.L := rfl
      linarith
    calc Real.log (D.R.N D.R.m : ℝ) ≤ Real.log (Real.exp L.sc.L) := Real.log_le_log hN0 hNb
      _ = L.sc.L := Real.log_exp _
  have hlogf : Real.log (D.R.f : ℝ) ≤ Real.log (D.R.N D.R.m : ℝ) := Real.log_le_log (by linarith) hfN
  have hlog : Real.log ((D.R.f : ℝ) * (D.R.N D.R.m : ℝ)) ≤ 2 * L.sc.L := by
    rw [Real.log_mul (by linarith) hN0.ne']
    linarith
  have hB0 : L.B0 = (D.R.f : ℝ) * D.R.m * L.sc.b * L.sc.L := rfl
  have hb0' : 0 < L.sc.b := Real.exp_pos _
  have key : (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) * Real.log ((D.R.f : ℝ) * (D.R.N D.R.m : ℝ)) ≤ 2 * L.B0 := by
    have h1 : (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) * Real.log ((D.R.f : ℝ) * (D.R.N D.R.m : ℝ)) ≤
        (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) * (2 * L.sc.L) :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    have h2 : (D.R.f : ℝ) * ((D.R.N D.R.m : ℝ) * L.sc.L) ≤ (D.R.f : ℝ) * L.sc.b :=
      mul_le_mul_of_nonneg_left hNL' (by positivity)
    have h3 : (D.R.f : ℝ) * L.sc.b * 1 ≤ (D.R.f : ℝ) * L.sc.b * ((D.R.m : ℝ) * L.sc.L) :=
      mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
    rw [hB0]
    nlinarith
  have hG' := hG u
  have := mul_le_mul_of_nonneg_left key hCG
  nlinarith

theorem family_gammaDiscriminant_budget {eps : ℝ} (Fm : FamP eps) (hT : TuSize Fm) (hDl : DlSize Fm) (hG : DGamSize Fm) :
    ∃ C x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, WeightDegreeSizes.StabiliserLogBound (Fm.D x i) (Fm.L x i) C := by
  obtain ⟨CG, x0, hG⟩ := hG
  obtain ⟨Cn₀, hCn⟩ := numsL_wtsL_fam Fm hT hDl
  obtain ⟨x2, hx2⟩ := hCn Cn₀ le_rfl 3 le_rfl
  refine ⟨4 * max CG 0, max x0 x2, fun x hx i => ?_⟩
  exact gammaDiscriminant_budget_of_sizes (by norm_num) (le_max_right _ _) (hx2 x (le_trans (le_max_right _ _) hx) i).1
    (factDGam_mono (hG x (le_trans (le_max_left _ _) hx) i) (le_max_left _ _))

end Formalism.MainNotions.J

end
end

-- bundled from Formalism.SharpRestriction.AdmissibleParameterJoins.DIVfromGLs
section
noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions.WeilJacquetShalikaLaw Formalism.MainNotions.WeightDegreeSizes

variable {D : D7} {L : SizeData₂ D}

theorem levelColumn_of_sharp_twisted {Dx : DivX D} {T : TwForms D} (h : ∀ u, Formalism.MainNotions.product_first_zeroth_parts.TupleChainSharpColumnValuation Dx T u) : LevelPrimeColumnOtherTuples D Dx T :=
  fun u w hw μ _ hq x hx => h u w hw μ hq x hx

theorem level_column_closed {Dx : DivX D} {T : TwForms D} (h5 : ∀ u, Formalism.MainNotions.product_first_zeroth_parts.Conclusion5Sharp D u)
    (h5T : ∀ u, Formalism.MainNotions.product_first_zeroth_parts.TupleChainSharpColumnValuation Dx T u) : ValuationAtLevelPrime D Dx T :=
  levelColumn_of_sharpBound h5 (levelColumn_of_sharp_twisted h5T)

theorem level_primes_ne_type_primes (D : D7) : LevelPrimeNotTypePrime D :=
  fun u i => (D.T_ne_g u i).symm

theorem sizeData_at_level_primes {X : ErrX D} {K : Formalism.MainNotions.G.Consts} {c : ErrC} (P : ParameterChoice' D L) (hF : L.FDef)
    (hE : L.EDef X K c) : LevelPrimeSizes D L :=
  sizeData_at_level_primes_of_defs P hF hE (level_primes_ne_type_primes D)

theorem periodBound_at_level_closed {Dx : DivX D} {T : TwForms D} {X : ErrX D} {K : Formalism.MainNotions.G.Consts} {c : ErrC} (P : ParameterChoice' D L)
    (hD : DGamDef D) (hF : L.FDef) (hE : L.EDef X K c) (hN : NuAtTDef D L) (hG : LevelPrimeCoprimeStabiliser D) (hp : PeriodClassSumWeyl D)
    (h6T : TwistedChainIntegral D T) (hpT : TwistedPeriodIntegral D Dx T) (h5 : ∀ u, Formalism.MainNotions.product_first_zeroth_parts.Conclusion5Sharp D u)
    (h5T : ∀ u, Formalism.MainNotions.product_first_zeroth_parts.TupleChainSharpColumnValuation Dx T u) (h6 : ∀ u, Formalism.MainNotions.product_first_zeroth_parts.Conclusion6 D u) : PeriodBoundAtLevelPrime D L :=
  periodBound_at_level_of_twisted hD (ETDef_of P hF hE (level_primes_ne_type_primes D)) hN hG hp h6T hpT (levelColumn_of_sharp_twisted h5T) h5 h6

theorem family_level_column_bound {eps : ℝ} (Fm : FamP eps)
    (hE : ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (hx : Fm.x1 < x) (i : Fm.Ix x),
      (∀ u, Formalism.MainNotions.product_first_zeroth_parts.Conclusion5Sharp (Fm.D x i) u) ∧ (∀ u, Formalism.MainNotions.product_first_zeroth_parts.TupleChainSharpColumnValuation (Fm.X x i) (Fm.ex x hx i).tw u) ∧
        LevelPrimeCoprimeStabiliser (Fm.D x i) ∧ ServedHasModel (Fm.Gx x i) Fm.GK) : FamilyLevelPrimeInputs Fm := by
  unfold FamilyLevelPrimeInputs
  obtain ⟨x0, h⟩ := hE
  exact ⟨x0, fun x hx0 hx i => ⟨level_column_closed (h x hx0 hx i).1 (h x hx0 hx i).2.1,
    sizeData_at_level_primes (Fm.params x hx i) (Fm.ex x hx i).fdef (Fm.ex x hx i).err.edef,
    (h x hx0 hx i).2.2.1, (h x hx0 hx i).2.2.2⟩⟩

theorem family_pairing_integrality {eps : ℝ} (Fm : FamP eps)
    (hE : ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (hx : Fm.x1 < x) (i : Fm.Ix x),
      (∀ u, Formalism.MainNotions.product_first_zeroth_parts.Conclusion6 (Fm.D x i) u) ∧ TwistedChainIntegral (Fm.D x i) (Fm.ex x hx i).tw ∧ PeriodClassSumWeyl (Fm.D x i) ∧
        TwistedPeriodIntegral (Fm.D x i) (Fm.X x i) (Fm.ex x hx i).tw) : familyPairing Fm := by
  unfold familyPairing
  obtain ⟨x0, h⟩ := hE
  refine ⟨x0, fun x hx0 hx i => ?_⟩
  obtain ⟨h6, hT, hp0, hpT⟩ := h x hx0 hx i
  exact pairing_integrality_both_sides _ _ (chain_norm_of_sixth h6) hT hp0 hpT

theorem family_periodBound_at_level {eps : ℝ} (Fm : FamP eps) (hS : ServF Fm)
    (hE : ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (hx : Fm.x1 < x) (i : Fm.Ix x),
      ((∀ u, Formalism.MainNotions.product_first_zeroth_parts.Conclusion5Sharp (Fm.D x i) u) ∧ (∀ u, Formalism.MainNotions.product_first_zeroth_parts.TupleChainSharpColumnValuation (Fm.X x i) (Fm.ex x hx i).tw u) ∧
        (∀ u, Formalism.MainNotions.product_first_zeroth_parts.Conclusion6 (Fm.D x i) u)) ∧
      (TwistedChainIntegral (Fm.D x i) (Fm.ex x hx i).tw ∧ PeriodClassSumWeyl (Fm.D x i) ∧
        TwistedPeriodIntegral (Fm.D x i) (Fm.X x i) (Fm.ex x hx i).tw) ∧
      LevelPrimeCoprimeStabiliser (Fm.D x i) ∧ ServedHasModel (Fm.Gx x i) Fm.GK) {C1 C2 : ℝ} (hCL : FamilyPeriodFormCond Fm C1 C2) (hSg : familySizeBoundAtTypePrime Fm C1)
    (hlin : ∀ x (i : Fm.Ix x), PerColSmul (Fm.D x i)) : familyL2Bound Fm ∧ familyFourthComplement Fm := by
  obtain ⟨x0, hE⟩ := hE
  refine l2_and_fourth_complement_family Fm (family_pairing_integrality Fm ⟨x0, fun x hx hx1 i => ?_⟩) hS
    (family_level_column_bound Fm ⟨x0, fun x hx hx1 i => ?_⟩) hCL hSg hlin
  · obtain ⟨⟨_, _, a⟩, ⟨b, c, d⟩, _, _⟩ := hE x hx hx1 i
    exact ⟨a, b, c, d⟩
  · obtain ⟨⟨a, b, _⟩, _, c, d⟩ := hE x hx hx1 i
    exact ⟨a, b, c, d⟩

theorem theta_term_of_integrality (D : D7) (large₂ : SizeData₂ D) (Cn C cL : ℝ) (T : Formalism.MainNotions.TaylorLogMetric.Tor D) (e : Formalism.MainNotions.TaylorLogMetric.FamE D)
    (hth : Formalism.MainNotions.TaylorLogMetric.th22 D T C e) (hfree : Formalism.MainNotions.GlobalTheoryTheory.ThFree D) (hl : Formalism.MainNotions.GlobalTheoryTheory.ThLinkLe D T e)
    (hN : NumsL D large₂ Cn cL) : Formalism.MainNotions.placeRankTwoOne.GenusOneThetaNorm D large₂ (C * (1 + Cn) * cL) :=
  genusOne_theta_norm_bound D large₂ Cn (C * (1 + Cn)) cL (flipTwoThree.second_hypothesis_of_lifting D Cn C large₂.sc.x T e hth hfree hl) hN

theorem family_theta_term_of_integrality {eps : ℝ} (Fm : FamP eps) (C : ℝ) (hT : TuSize Fm) (hDl : DlSize Fm)
    (hfree : ∀ x (i : Fm.Ix x), Formalism.MainNotions.GlobalTheoryTheory.ThFree (Fm.D x i))
    (h22 : ∀ x (i : Fm.Ix x), Formalism.MainNotions.GlobalTheoryTheory.ExistsTwelfthRootCharacterThetaFamily (Fm.D x i) C) : Formalism.MainNotions.placeRankTwoOne.ThetaNormFamily Fm := by
  unfold Formalism.MainNotions.placeRankTwoOne.ThetaNormFamily
  obtain ⟨Cn₀, hN⟩ := numsL_wtsL_fam Fm hT hDl
  obtain ⟨x0, hx0⟩ := hN Cn₀ le_rfl 3 le_rfl
  refine ⟨C * (1 + Cn₀) * 3, x0, fun x hx i => ?_⟩
  obtain ⟨δ, -, χ, -, e, hcl, hl⟩ := h22 x i
  exact theta_term_of_integrality (Fm.D x i) (Fm.L x i) Cn₀ C 3 _ e (by unfold GlobalTheoryTheory.Cl22 at hcl; exact hcl.2.1) (hfree x i) hl (hx0 x hx i).1

end Formalism.MainNotions.J

end
end

-- bundled from Formalism.SharpRestriction.AdmissibleParameterJoins.GandSaj
section
noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions.G Formalism.MainNotions.WeilJacquetShalikaLaw

variable {D : D7} {L : SizeData₂ D}

theorem sgAtG_of {K : Consts} {lev : LevelData D} {Xe : ErrX D} {ce : ErrC} {C1 : ℝ} (hF : L.FDef)
    (hE : ErrDefs D L Xe lev K ce) (hC1 : 0 ≤ C1) (hC : 2 * C1 ≤ ce.g) : Formalism.MainNotions.WeightDegreeSizes.SgAtG D L Xe C1 :=
  fun i w hwi u hw => sumFE_atG_le hF hE hC1 hC i w hwi u hw

theorem periodBound_at_type_of_local {K : Consts} {lev : LevelData D} {Xe : ErrX D} {ce : ErrC} {C1 C2 : ℝ} (hF : L.FDef)
    (hE : ErrDefs D L Xe lev K ce) (hC1 : 0 ≤ C1) (hC : 2 * C1 ≤ ce.g) (h : Formalism.MainNotions.LiftErrorLocal.PropositionCLatticeBound D L Xe C1 C2)
    (hN : Formalism.MainNotions.WeightDegreeSizes.NuInM D L) : PeriodBoundAtTypePrimes D L := by
  intro u w hw hgm φ hφ F hF1 _
  obtain ⟨i, hwi⟩ : ∃ i : Fin 2, D.what₂.places.resChar w = D.host.g i := by
    rcases Finset.mem_insert.1 hgm with h0 | h1
    · exact ⟨0, h0⟩
    · exact ⟨1, Finset.mem_singleton.1 h1⟩
  exact Formalism.MainNotions.WeightDegreeSizes.period_integral_at_typePrime h (sgAtG_of hF hE hC1 hC) hN (Formalism.MainNotions.DIV.perColSmul D) u w i hwi hw φ hφ F hF1

theorem period_conditions_of_pairing_twist {X : Inst D L} {Y : LatInst D} {K : Consts} {c : LatCmp D} {Dx : DivX D} {T : TwForms D}
    {lev : LevelData D} {Xe : ErrX D} {ce : ErrC}
    (hP : Formalism.MainNotions.WeightDegreeSizes.PairingAtEveryPlace D Dx T) (hE : ErrDefs D L Xe lev K ce) (hET : Formalism.MainNotions.WeightDegreeSizes.LevelPrimeSizes D L)
    (ht : Ties9 D L X Y c) (hS : c.NuServedDef X Y K) (hNT : NuAtTDef D L) (hN : Formalism.MainNotions.WeightDegreeSizes.NuInM D L)
    (hGI : Formalism.MainNotions.WeightDegreeSizes.ServedHasModel X K) (hF : ∀ w, ParametersFill X K w)
    (hcs : ∀ p : ℕ, p.Prime → IsCs D p → p ∈ L.drop) (hG : Formalism.MainNotions.WeightDegreeSizes.LevelPrimeCoprimeStabiliser D)
    (h1 : Formalism.MainNotions.WeilJacquetShalikaLaw.Conclusion1 D L X Y K c Dx T lev Xe ce 1) (h5 : Formalism.MainNotions.WeightDegreeSizes.ValuationAtLevelPrime D Dx T) {C1 C2 : ℝ}
    (hCL : Formalism.MainNotions.LiftErrorLocal.PropositionCLatticeBound D L Xe C1 C2) (hC1 : 0 ≤ C1) (hC : 2 * C1 ≤ ce.g) : Formalism.MainNotions.LocalQuadraticParts.adm2 D L :=
  period_conditions_of_pairing hP hE hET ht hS hNT hN hGI hF hcs hG h1 h5 hCL (sgAtG_of ht.fdef hE hC1 hC) (Formalism.MainNotions.DIV.perColSmul D)

theorem no_gain_condition_of_local {K : Consts} {Dx : DivX D} {T : TwForms D} {lev : LevelData D} {Xe : ErrX D} {ce : ErrC}
    (hP : Formalism.MainNotions.WeightDegreeSizes.PairingAtEveryPlace D Dx T) (hE : ErrDefs D L Xe lev K ce) (hF : L.FDef)
    (h : Formalism.MainNotions.WeilJacquetShalikaLaw.ColumnValuationAwayFromTypePrimes D L K Dx T lev Xe ce 1) {C1 C2 : ℝ} (hCL : Formalism.MainNotions.LiftErrorLocal.PropositionCLatticeBound D L Xe C1 C2)
    (hC1 : 0 ≤ C1) (hC : 2 * C1 ≤ ce.g) : Formalism.MainNotions.LocalQuadraticParts.adm12 D L :=
  no_gain_condition_of_pairing_sign hP hE hF h hCL (sgAtG_of hF hE hC1 hC)

theorem family_type_prime_loss {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) {C1 : ℝ} (hC1 : 0 ≤ C1) (hC : 2 * C1 ≤ Fm.cX.err.g) :
    Formalism.MainNotions.WeightDegreeSizes.familySizeBoundAtTypePrime Fm C1 :=
  ⟨0, fun x hx _ i => sgAtG_of (local_compatibility_family Fm x hx i).fdef (Fm.ex x hx i).err hC1 hC⟩

end Formalism.MainNotions.J

end
end

