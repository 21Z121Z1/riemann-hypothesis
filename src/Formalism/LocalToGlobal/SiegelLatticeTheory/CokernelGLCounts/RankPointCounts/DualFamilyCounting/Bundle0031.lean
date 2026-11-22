import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.CoeffOfSpan
import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0028
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0019
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0023

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.IsAdmissibleIntegralBasisChangeOne
section
noncomputable section

open NumberField Module IsDedekindDomain Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.CntLocal
open Classical

namespace Formalism.L2.SG.Pf.Cnt.R3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section General

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E} {r : ℕ}

theorem frameAct_one (f : Fin (r + 1) → S.V) (b : Fin (r + 1)) : frameAct f 1 b = f b := by
  unfold frameAct
  rw [Finset.sum_eq_single b]
  · simp
  · intro a _ hab
    simp [Matrix.one_apply_ne hab]
  · simp

end General

variable {D : Formalism.BasicNotions.D7} {T T' : D.host.E} {F0 : FlagG (VS D) D.R.rS T} {F' : LFlag (VS D) D.R.rS T'}
  {Λ : Submodule (𝓞 D.host.E) (VS D).V}

theorem f_mem_UUS (i : Fin (D.R.rS + 1)) : F0.fvec i ∈ UUS D F0 F' := by
  unfold UUS
  refine Fin.lastCases ?_ (fun a => ?_) i
  · have e : F0.fvec (Fin.last _) = F0.z := by simp [FlagG.fvec]
    rw [e]
    exact Submodule.mem_sup_left (Submodule.mem_sup_left
      (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)))
  · have e : F0.fvec (Fin.castSucc a) = F0.e a := by simp [FlagG.fvec]
    rw [e]
    refine Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_left ?_))
    exact Submodule.subset_span ⟨a, 1, one_mem_ddS D a, (one_smul _ _).symm⟩

theorem f'_mem_UUS (i : Fin (D.R.rS + 1)) : F'.fl.fvec i ∈ UUS D F0 F' := by
  unfold UUS
  refine Fin.lastCases ?_ (fun a => ?_) i
  · have e : F'.fl.fvec (Fin.last _) = F'.fl.z := by simp [FlagG.fvec]
    rw [e]
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  · have e : F'.fl.fvec (Fin.castSucc a) = F'.fl.e a := by simp [FlagG.fvec]
    rw [e]
    refine Submodule.mem_sup_left (Submodule.mem_sup_right ?_)
    exact Submodule.subset_span ⟨a, 1, one_mem_ddS D a, (one_smul _ _).symm⟩

theorem spanE_UUS : spanE (VS D) (UUS D F0 F') = UPair D F0 F' := by
  apply le_antisymm
  · unfold spanE
    rw [Submodule.span_le]
    intro y hy
    have hle : UUS D F0 F' ≤ (UPair D F0 F').restrictScalars (𝓞 D.host.E) := by
      unfold UUS
      refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
      · unfold XS
        rw [Submodule.span_le]
        rintro _ ⟨a, x, -, rfl⟩
        exact (UPair D F0 F').smul_mem x (Submodule.subset_span (Or.inl ⟨Fin.castSucc a, by simp [FlagG.fvec]⟩))
      · rw [Submodule.span_le, Set.singleton_subset_iff]
        exact Submodule.subset_span (Or.inl ⟨Fin.last _, by simp [FlagG.fvec]⟩)
      · unfold XS
        rw [Submodule.span_le]
        rintro _ ⟨a, x, -, rfl⟩
        exact (UPair D F0 F').smul_mem x (Submodule.subset_span (Or.inr ⟨Fin.castSucc a, by simp [FlagG.fvec]⟩))
      · rw [Submodule.span_le, Set.singleton_subset_iff]
        exact Submodule.subset_span (Or.inr ⟨Fin.last _, by simp [FlagG.fvec]⟩)
    exact hle hy
  · unfold UPair
    rw [Submodule.span_le]
    rintro _ (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact Submodule.subset_span (f_mem_UUS i)
    · exact Submodule.subset_span (f'_mem_UUS i)

theorem UU_eq (hX0 : XLam Λ (lf D F0) = XS D F0) (hX1 : XLam Λ F' = XS D F'.fl) (hz : F'.zt = F'.fl.z) :
    UU Λ (lf D F0) F' = UUS D F0 F' := by
  unfold UU
  rw [hX0, hX1, hz]
  rfl

theorem blat_eq (hX0 : XLam Λ (lf D F0) = XS D F0) (hX1 : XLam Λ F' = XS D F'.fl) (hz : F'.zt = F'.fl.z) :
    BLat Λ (lf D F0) F' = Λ ⊓ (UPair D F0 F').restrictScalars (𝓞 D.host.E) := by
  unfold BLat UUE
  rw [UU_eq hX0 hX1 hz, spanE_UUS]

theorem mplus1_loc (hX0 : XLam Λ (lf D F0) = XS D F0) (P : Ideal (𝓞 D.host.E)) [P.IsPrime]
    (hg : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P) :
    Formalism.HermitianLatticesTheory.localization₂ P (Mplus Λ (gS D) (lf D F0) F' 1) = Formalism.HermitianLatticesTheory.localization₂ P (BB D F0 F') := by
  rw [loc_BB_g D F0 F' P hg]
  refine le_antisymm (Formalism.L2.SG.Pf.locP_le_locP' (Submodule.span_le.2 ?_))
    (Formalism.L2.SG.Pf.localization_mono' (Submodule.span_le.2 ?_))
  · rintro v ((hv | hv) | ⟨b, rfl⟩)
    · have hv' : v ∈ XS D F0 := by rw [← hX0]; exact hv
      refine ((XS_le_locP_e D F0 P hg).trans (Formalism.L2.SG.Pf.localization_mono' (Submodule.span_le.2 ?_))) hv'
      rintro _ ⟨a, rfl⟩; exact e_mem_MMg D F0 F' a
    · rw [Set.mem_singleton_iff] at hv
      rw [hv]
      exact Formalism.L2.SG.Pf.le_locP' _ _ (z_mem_MMg D F0 F')
    · refine Formalism.L2.SG.Pf.le_locP' _ _ ?_
      simp only [frame, frameAct_one]
      exact m_mem_MMg D F0 F' b
  · rintro v (⟨i, rfl⟩ | ⟨b, rfl⟩)
    · induction i using Fin.lastCases with
      | last => rw [fvec_last]; exact Submodule.subset_span (Or.inl (Or.inr rfl))
      | cast a =>
        rw [fvec_cast]
        refine Submodule.subset_span (Or.inl (Or.inl ?_))
        rw [hX0]; exact e_mem_XS D F0 a
    · refine Submodule.subset_span (Or.inr ⟨b, ?_⟩)
      simp only [frame, frameAct_one]

theorem isAdmissibleIntegralBasisChange_one (hB : Λ ⊓ (UPair D F0 F').restrictScalars (𝓞 D.host.E) = BB D F0 F') :
    AdmWit Λ (gS D) (lf D F0) F' 1 := by
  refine ⟨fun a b h => Matrix.one_apply_ne (ne_of_lt h).symm, fun a => Matrix.one_apply_eq a, fun b P _ => ?_⟩
  have := P.isPrime
  have hm : (((gS D : ℕ) : D.host.E))⁻¹ • (F'.fl.fvec b - F0.fvec b) ∈ Λ := by
    have := MMg_le_BB D F0 F' (m_mem_MMg D F0 F' b)
    rw [← hB] at this
    exact this.1
  refine ⟨1, P.asIdeal.primeCompl.one_mem, ?_⟩
  rw [one_smul]
  have e : frame F' b - frameAct (frame (lf D F0)) 1 b =
      ((gS D : ℕ) : 𝓞 D.host.E) • ((((gS D : ℕ) : D.host.E))⁻¹ • (F'.fl.fvec b - F0.fvec b)) := by
    rw [frameAct_one, smulO, map_natCast, smul_smul, mul_inv_cancel₀ (g_ne D), one_smul]
  rw [e]
  exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hm

theorem forward {Z : MatZ D} (hz : F'.zt = F'.fl.z) (hR : IsRowLat D F0 Λ) (hE : F' ∈ EZ T' F0 Λ Z) :
    Λ ⊓ (UPair D F0 F').restrictScalars (𝓞 D.host.E) = BB D F0 F' := by
  obtain ⟨-, ⟨-, -, hL, hF⟩, hX0⟩ := hR
  obtain ⟨⟨hL', -, -⟩, h1, ⟨ξ, hξ, hgen⟩, ⟨hF', hX1⟩, -⟩ := hE
  rw [← blat_eq hX0 hX1 hz]
  apply Formalism.L2.SG.Pf.eq_of_locP
  intro P
  have := P.isPrime
  by_cases hg : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal
  · rw [(hgen P).1 hg, Formalism.L2.SG.Pf.Mplus_eq_MplusInt hL hF hL' hF' P hg ξ hξ,
      ← Formalism.L2.SG.Pf.Mplus_eq_MplusInt hL hF hL' hF' P hg 1 h1, mplus1_loc hX0 P.asIdeal hg]
  · rw [(hgen P).2 hg, UU_eq hX0 hX1 hz, ← loc_BB_ng D F0 F' P.asIdeal hg]

theorem backward (hU : Formalism.MainNotions.BridgeRowsGenus.LocUnimod) {Z : MatZ D} (hz : F'.zt = F'.fl.z)
    (hZ : ZhatL (lf D F0) F' = Z) (hG : GZ T T' (Zhat F0 F'.fl) ≠ 0)
    (hlat : Submodule.IsLattice D.host.E Λ) (huni : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ)
    (hB : Λ ⊓ (UPair D F0 F').restrictScalars (𝓞 D.host.E) = BB D F0 F') :
    IsRowLat D F0 Λ ∧ F' ∈ EZ T' F0 Λ Z := by
  have hw := indep D F0 F'.fl hG
  have hX0 := xlam0 hw hB
  have hX1 := xlam1 hw hB
  have hzΛ : F0.z ∈ Λ := BB_le_Lam hw hB (MMg_le_BB D F0 F' (z_mem_MMg D F0 F'))
  have hz'Λ : F'.fl.z ∈ Λ := BB_le_Lam hw hB (MMg_le_BB D F0 F' (z'_mem_MMg D F0 F'))
  have hFC0 : IsFixedConv Λ (gS D) (lf D F0) := by
    refine ⟨fun P => ?_, prim0 hw hB⟩
    obtain ⟨c, hc0, hc1, hc2⟩ := xs_locGen D F0 P
    exact ⟨c, hc0, hc1, by rw [hX0]; exact hc2⟩
  have hFC1 : IsFixedConv Λ (gS D) F' := by
    refine ⟨fun P => ?_, prim1 hw hB⟩
    obtain ⟨c, hc0, hc1, hc2⟩ := xs_locGen D F'.fl P
    exact ⟨c, hc0, hc1, by rw [hX1]; exact hc2⟩
  have h1 := isAdmissibleIntegralBasisChange_one hB
  refine ⟨⟨Formalism.MainNotions.BridgeRowsGenus.unimodular_mem_genus hU D.sp.cm (VS D) Λ hlat huni,
    ⟨hlat, huni, ⟨hzΛ, rfl⟩, hFC0⟩, hX0⟩, ⟨⟨hz'Λ, hz⟩, ⟨1, h1⟩, hG⟩, h1, ⟨1, h1, fun P => ?_⟩,
    ⟨hFC1, hX1⟩, hZ⟩
  have := P.isPrime
  refine ⟨fun hg => ?_, fun hg => ?_⟩
  · rw [blat_eq hX0 hX1 hz, hB, mplus1_loc hX0 P.asIdeal hg]
  · rw [blat_eq hX0 hX1 hz, hB, UU_eq hX0 hX1 hz, loc_BB_ng D F0 F' P.asIdeal hg]

end Formalism.L2.SG.Pf.Cnt.R3

namespace Formalism.L2.SG.Pf.Cnt

open Formalism.L2.SG.Pf.Cnt.R3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem mmChar_of (hU : Formalism.MainNotions.BridgeRowsGenus.LocUnimod) : MMChar := by
  intro D u u' _ F0 what₂ _ Z F' hz hZ hP
  have hG : GZ (Tn u) (Tn u') (Zhat F0 F'.fl) ≠ 0 := by
    subst hZ
    exact totPos_ne D hP
  rw [MMof_eq]
  refine ⟨BB_latIn D F0 F', fun Λ => ⟨fun ⟨hR, hE⟩ => ?_, fun ⟨hlat, huni, hB⟩ => ?_⟩⟩
  · exact ⟨hR.2.1.1, hR.2.1.2.1, forward hz hR hE⟩
  · exact backward hU hz hZ hG hlat huni hB

end Formalism.L2.SG.Pf.Cnt
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcArithG
section
noncomputable section

namespace Formalism.L2.SG.Pf.NcArithG

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.LocVol Formalism.L2.SG.MassDataConc Formalism.L2.SG.TypedSets MeasureTheory NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
  (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
  (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)
  {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (T : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁) (sd C Th : ℝ)
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {what₂ : Finset (Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V)}
  (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
  (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)

theorem rm_eq (D : D7) : D.R.m = 2 * (D.R.rS + 1) := by
  obtain ⟨j, hj⟩ := D.R.m_even
  have h2 := D.R.two_le_m
  show D.R.m = 2 * (D.R.m / 2 - 1 + 1)
  omega

theorem cMass_succ {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    (k : ℕ) (hk : 2 ≤ k) :
    Formalism.L2.SG.Pf.Cnt.cMass K F k = Formalism.L2.SG.Pf.Cnt.cMass K F (k - 1) * Formalism.HermitianLatticesTheory.massRatioRightSide K k := by
  unfold Formalism.L2.SG.Pf.Cnt.cMass
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [Finset.prod_Icc_succ_top (by omega), Nat.add_sub_cancel, mul_assoc]

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem ncValueC_of_global (a' Ω ATyp A' AT PT : ℝ)
    (hP : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).Pos)
    (ha : 0 < a') (hATyp : 0 < ATyp) (hA' : 0 < A') (hPT : 0 < PT)
    (hS : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μK * a' =
      (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μH' * Ω)
    (hR : Formalism.L2.SG.RealObj.DisintegrationConstant X u u' 1 * (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volH *
        (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volN *
        (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volN' =
      a' * 2 ^ (D.R.k * Module.finrank ℚ D.host.F) *
        (Real.pi ^ D.R.k / (Nat.factorial (D.R.k - 1) : ℝ)) ^ Module.finrank ℚ D.host.F *
        ((Tw u : ℕ) : ℝ) ^ (-((D.R.k * Module.finrank ℚ D.host.F : ℕ) : ℤ)) *
        |(NumberField.discr D.host.F : ℝ)| ^
          (-(8 * (D.R.rS : ℝ) ^ 3 + 6 * (D.R.rS : ℝ) ^ 2 + 6 * D.R.k * (D.R.rS : ℝ) ^ 2 + D.R.rS) / 3))
    (hG1 : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).unitLevelVolume /
        (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volZZ =
      |(NumberField.discr D.host.F : ℝ)| ^ (((D.R.rS : ℝ) + 1) * (8 * (D.R.rS : ℝ) ^ 2 + 10 * D.R.rS + 3) / 3) *
        ((Lat.gS D : ℕ) : ℝ) ^ ((D.R.rS + 1) * (2 * D.R.rS + 3) * Module.finrank ℚ D.host.F))
    (hG2 : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μKnat /
        (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μK =
      ((Lat.gS D : ℕ) : ℝ) ^ (-(((D.R.rS + 1) * (2 * D.R.k + 2 * D.R.rS + 1) * Module.finrank ℚ D.host.F : ℕ) : ℤ)) /
        ATyp)
    (hG3 : Ω = |(NumberField.discr D.host.F : ℝ)| ^
        (-((D.R.r : ℝ) * (2 * D.R.rS + 1) - ((2 * (D.R.rS : ℝ) + 1) ^ 2) / 2)) * A')
    (hG4 : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).al * ATyp = AT * A')
    (hG5 : AT * ∏ i ∈ Finset.Icc (D.R.k + 1) D.R.r, Formalism.HermitianLattices.Ext.L3.lValEtaF D.host.E D.host.F i = PT)
    (hRM : Formalism.MainNotions.S.Cnt.massRows D F0 what₂ =
      Formalism.L2.SG.Pf.Cnt.cMass D.host.E D.host.F D.R.k * ((Tw u : ℕ) : ℝ) ^ (D.R.k * Module.finrank ℚ D.host.F) * PT)
    (hV : Formalism.HermitianLatticesTheory.vInv D.host.E =
      |(NumberField.discr D.host.F : ℝ)| ^ ((1 : ℝ) / Module.finrank ℚ D.host.F) / 2)
    (hfE : Formalism.HermitianLatticesTheory.fDeg D.host.E = Module.finrank ℚ D.host.F)
    (hng : ngFac D = ((Lat.gS D : ℕ) : ℝ) ^ (D.R.m * Module.finrank ℚ D.host.F * (D.R.k - 1))) :
    Formalism.L2.SG.Pf.NcAsm.NcValueC X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq := by

  set B := bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq with hB
  obtain ⟨hKc, hFc, -⟩ := Formalism.L2.SG.Pf.Cnt.field_dictionary_holds D
  set dd : ℝ := |(NumberField.discr D.host.F : ℝ)| with hdd
  set f : ℕ := Module.finrank ℚ D.host.F with hfdef
  set k : ℕ := D.R.k with hkdef
  set s : ℕ := D.R.rS with hsdef
  set gg : ℝ := ((Lat.gS D : ℕ) : ℝ) with hgg
  set TT : ℝ := ((Tw u : ℕ) : ℝ) with hTT
  set Lk : ℝ := ∏ i ∈ Finset.Icc (k + 1) D.R.r, Formalism.HermitianLattices.Ext.L3.lValEtaF D.host.E D.host.F i with hLk
  have hm : D.R.m = 2 * (s + 1) := rm_eq D
  have hk5 : D.R.m + 3 ≤ k := D.R.m_add_three_le_k
  have hk2 : 2 ≤ k := by omega
  have hr : D.R.r = k + 2 * s + 1 := by
    show D.R.k + D.R.m - 1 = k + 2 * s + 1
    omega
  have hf : 0 < f := Module.finrank_pos
  have hdpos : 0 < dd := abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero D.host.F)
  have hgpos : 0 < gg := by
    have h0 := (D.host.g_prime 0).pos
    have h1' := (D.host.g_prime 1).pos
    rw [hgg]
    unfold Lat.gS
    exact_mod_cast Nat.mul_pos h0 h1'
  have hTpos : 0 < TT := by rw [hTT]; exact_mod_cast (D.mem u).A.T_prime.pos

  obtain ⟨hp, hKo, hSo, hSo', hMo, hU00o, hH, hH', hHpp, hHpp', hN, hN', hZZ, hPP, hal, -⟩ := hP
  have hKp : ∀ p, 0 < B.μKp p := fun p => (hp p).2.2.2.2.2.1
  have hμK : 0 < B.μK := mul_pos hKo (Finset.prod_pos fun p _ => hKp p)

  have hLkpos : 0 < Formalism.HermitianLattices.Ext.L3.lValEtaF D.host.E D.host.F k := by
    rw [← Formalism.HermitianLattices.Ext.L3.lValEta_eq_lValEtaF hKc hFc k hk2]
    exact Formalism.HermitianLattices.Ext.L3.lValEta_pos hKc k hk2
  have hLkk : 0 < Lk := by
    apply Finset.prod_pos
    intro i hi
    have hi2 : 2 ≤ i := by simp only [Finset.mem_Icc] at hi; omega
    rw [← Formalism.HermitianLattices.Ext.L3.lValEta_eq_lValEtaF hKc hFc i hi2]
    exact Formalism.HermitianLattices.Ext.L3.lValEta_pos hKc i hi2
  have hcm := (Formalism.L2.SG.Pf.Asm.cMass_spec hKc hFc (k - 1) (by omega)).1
  have hIcc : (∏ i ∈ Finset.Icc k D.R.r, Formalism.HermitianLattices.Ext.L3.lValEtaF D.host.E D.host.F i) =
      Formalism.HermitianLattices.Ext.L3.lValEtaF D.host.E D.host.F k * Lk := by
    have hIo : Finset.Ioc k D.R.r = Finset.Icc (k + 1) D.R.r := by
      ext i; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
    rw [Finset.Icc_eq_cons_Ioc (show k ≤ D.R.r by omega), Finset.prod_cons, hLk, hIo]

  have hvI : 2 * Formalism.HermitianLatticesTheory.vInv D.host.E = dd ^ ((1 : ℝ) / f) := by rw [hV]; ring
  have hvIpos : 0 < Formalism.HermitianLatticesTheory.vInv D.host.E := by
    rw [hV]; positivity
  have hpow1 : (dd ^ ((1 : ℝ) / f)) ^ f = dd := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hdpos.le]
    rw [show (1 : ℝ) / f * (f : ℝ) = 1 by field_simp]
    exact Real.rpow_one dd
  have hsq : Real.sqrt ((2 * Formalism.HermitianLatticesTheory.vInv D.host.E) ^ f) = dd ^ ((1 : ℝ) / 2) := by
    rw [hvI, hpow1, Real.sqrt_eq_rpow]
  have hvk : (Formalism.HermitianLatticesTheory.vInv D.host.E) ^ (k * f) = dd ^ (k : ℝ) / 2 ^ (k * f) := by
    have h2 : Formalism.HermitianLatticesTheory.vInv D.host.E = dd ^ ((1 : ℝ) / f) / 2 := by rw [hV]
    rw [h2, div_pow, pow_mul', hpow1, Real.rpow_natCast]

  set e : ℝ := -(8 * (s : ℝ) ^ 3 + 6 * (s : ℝ) ^ 2 + 6 * k * (s : ℝ) ^ 2 + s) / 3 with he
  set Xe : ℝ := ((s : ℝ) + 1) * (8 * (s : ℝ) ^ 2 + 10 * s + 3) / 3 with hXe
  set e2 : ℝ := (D.R.r : ℝ) * (2 * s + 1) - ((2 * (s : ℝ) + 1) ^ 2) / 2 with he2
  set E1 : ℝ := -((2 * s * (s + 1) * (k - 1) : ℕ) : ℝ) + 1 / 2 - k with hE1
  have hrR : (D.R.r : ℝ) = k + 2 * s + 1 := by rw [hr]; push_cast; ring
  have hk1 : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
  have hexp : e = E1 - Xe + e2 := by
    rw [he, hE1, hXe, he2, hrR]
    push_cast
    rw [hk1]
    ring
  have hde : dd ^ e = dd ^ E1 * (dd ^ Xe)⁻¹ * dd ^ e2 := by
    rw [hexp, Real.rpow_add hdpos, Real.rpow_sub hdpos, div_eq_mul_inv]
  have hdE1 : dd ^ E1 = dd ^ ((-((2 * s * (s + 1) * (k - 1) : ℕ) : ℤ) : ℤ) : ℝ) * dd ^ ((1 : ℝ) / 2) *
      (dd ^ (k : ℝ))⁻¹ := by
    rw [hE1, ← Real.rpow_neg hdpos.le, ← Real.rpow_add hdpos, ← Real.rpow_add hdpos]
    congr 1
    push_cast
    ring

  have hgc : gg ^ ((s + 1) * (2 * s + 3) * f) * gg ^ (D.R.m * f * (k - 1)) =
      gg ^ ((s + 1) * (2 * k + 2 * s + 1) * f) := by
    rw [← pow_add]
    congr 1
    rw [hm]
    obtain ⟨j, hj⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [hj, Nat.add_sub_cancel]
    ring
  have hgpow : gg ^ (-(((s + 1) * (2 * k + 2 * s + 1) * f : ℕ) : ℤ)) =
      (gg ^ ((s + 1) * (2 * k + 2 * s + 1) * f))⁻¹ := by
    rw [zpow_neg, zpow_natCast]
  have hTpow : TT ^ (-((k * f : ℕ) : ℤ)) = (TT ^ (k * f))⁻¹ := by rw [zpow_neg, zpow_natCast]

  have hal : B.al = AT * A' / ATyp := by rw [eq_div_iff hATyp.ne']; exact hG4
  have hAT : AT = PT / Lk := by rw [eq_div_iff hLkk.ne']; exact hG5
  have hratio : Formalism.HermitianLatticesTheory.massRatioRightSide D.host.E k =
      ((Nat.factorial (k - 1) : ℝ) ^ f * (dd ^ (k : ℝ) / 2 ^ (k * f)) / Real.pi ^ (k * f)) /
        dd ^ ((1 : ℝ) / 2) * Formalism.HermitianLattices.Ext.L3.lValEtaF D.host.E D.host.F k := by
    unfold Formalism.HermitianLatticesTheory.massRatioRightSide
    rw [hfE, hsq, Formalism.HermitianLattices.Ext.L3.lValEta_eq_lValEtaF hKc hFc k hk2, mul_pow, ← pow_mul, div_pow, hvk]
    ring
  have hratio_pos : 0 < Formalism.HermitianLatticesTheory.massRatioRightSide D.host.E k := Formalism.HermitianLattices.Ext.L3.massRatio_pos hKc k hk2

  have hKrat : B.μKnat / B.μH' = (B.μKnat / B.μK) * (Ω / a') := by
    have h1 : B.μK / B.μH' = Ω / a' := by
      rw [div_eq_div_iff hH'.ne' ha.ne']
      linarith [hS]
    rw [← h1]
    field_simp
  unfold Formalism.L2.SG.Pf.NcAsm.NcValueC
  rw [← hB]
  calc _ = dd ^ E1 * 2 ^ (k * f) * (Real.pi ^ k / (Nat.factorial (k - 1) : ℝ)) ^ f * TT ^ (-((k * f : ℕ) : ℤ)) *
          A' / ATyp := by
        unfold Formalism.L2.SG.Pf.Cnt.cExpl
        try rw [← hdd]
        try rw [← hfdef]
        try rw [← hkdef]
        try rw [← hsdef]
        rw [hIcc, hRM, cMass_succ k hk2, hratio, hal, hAT, hdE1,
          ← Real.rpow_intCast dd, hTpow, div_pow, ← pow_mul]
        have hpi : 0 < Real.pi := Real.pi_pos
        have hfac : (0 : ℝ) < (Nat.factorial (k - 1) : ℝ) := by exact_mod_cast Nat.factorial_pos _
        field_simp
    _ = Formalism.L2.SG.RealObj.DisintegrationConstant X u u' 1 * B.volH * B.volN * B.volN' * (B.unitLevelVolume / B.volZZ) * B.μKnat / B.μH' *
          ngFac D := by
        rw [show Formalism.L2.SG.RealObj.DisintegrationConstant X u u' 1 * B.volH * B.volN * B.volN' * (B.unitLevelVolume / B.volZZ) * B.μKnat /
            B.μH' * ngFac D = (Formalism.L2.SG.RealObj.DisintegrationConstant X u u' 1 * B.volH * B.volN * B.volN') *
            (B.unitLevelVolume / B.volZZ) * (B.μKnat / B.μH') * ngFac D by ring]
        rw [hR, hG1, hKrat, hG2, hG3, hng]
        try rw [← hdd]
        try rw [← hfdef]
        try rw [← hkdef]
        try rw [← hsdef]
        try rw [← hgg]
        try rw [← hTT]
        rw [hde, hgpow, Real.rpow_neg hdpos.le]
        rw [← hgc]
        have hX : 0 < dd ^ Xe := Real.rpow_pos_of_pos hdpos _
        have he2p : 0 < dd ^ e2 := Real.rpow_pos_of_pos hdpos _
        have hgA : 0 < gg ^ ((s + 1) * (2 * s + 3) * f) := pow_pos hgpos _
        have hgC : 0 < gg ^ (D.R.m * f * (k - 1)) := pow_pos hgpos _
        field_simp

end Formalism.L2.SG.Pf.NcArithG
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcXOmVTop
section
noncomputable section

namespace Formalism.L2.SG.Pf.NcX.OmVSt

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  MeasureTheory NumberField IsDedekindDomain

variable {D : D7} (X : HidaSetting D) (u u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

theorem n_sub_a : X.B.I.n - (D.R.rS + 1 + D.R.rS) = D.R.k := by
  have h1 := X.n_eq
  have h2 := D.R.rS_two
  unfold Ranks.r at h1
  omega

theorem a_le_n : D.R.rS + 1 + D.R.rS ≤ X.B.I.n := by
  have h1 := X.n_eq
  have h2 := D.R.rS_two
  unfold Ranks.r at h1
  omega

theorem fac_nonneg (v : PlX X) (j : ℕ) :
    0 ≤ 1 - (etaV (E := X.B.I.E) v : ℝ) ^ j * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(j : ℤ)) := by
  have hq : (1 : ℝ) ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
    have : Ideal.absNorm v.asIdeal ≠ 0 := fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
  have h1 : ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(j : ℤ)) ≤ 1 := zpow_le_one_of_nonpos₀ hq (by omega)
  have h0 : 0 ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(j : ℤ)) := by positivity
  have he : (etaV (E := X.B.I.E) v : ℝ) ^ j = 1 ∨ (etaV (E := X.B.I.E) v : ℝ) ^ j = -1 := by
    unfold etaV
    split_ifs
    · left; simp
    · push_cast; exact neg_one_pow_eq_or ℝ j
  rcases he with h | h <;> rw [h] <;> linarith

theorem val_nonneg (v : PlX X) (x : ℝ) (s : Finset ℕ) :
    0 ≤ absV v (dV v) ^ x * ∏ j ∈ s,
      (1 - (etaV (E := X.B.I.E) v : ℝ) ^ j * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(j : ℤ))) := by
  refine mul_nonneg (Real.rpow_nonneg ?_ _) (Finset.prod_nonneg fun j _ => fac_nonneg X v j)
  unfold absV
  split_ifs <;> positivity

theorem prod_eq (v : PlX X) (s : Finset ℕ) :
    ∏ j ∈ s, (1 - (etaV (E := X.B.I.E) v : ℝ) ^ j * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(j : ℤ))) =
      ∏ i ∈ s, (1 - ((etaV (E := X.B.I.E) v : ℤ) : ℝ) ^ i / ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ i) := by
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [zpow_neg, zpow_natCast, div_eq_mul_inv]

theorem exp_eq :
    (X.B.I.n : ℝ) * ((D.R.rS + 1 + D.R.rS : ℕ) : ℝ) - ((D.R.rS + 1 + D.R.rS : ℕ) : ℝ) ^ 2 / 2 =
      (X.B.I.n : ℝ) * (2 * D.R.rS + 1) - ((2 * (D.R.rS : ℝ) + 1) ^ 2) / 2 := by
  push_cast; ring

theorem omV_of (hStd : OmVStd X ψ) (hLat : OmVLat X) (hSD : OmVSD X) (hUn : OmVUnram X) (hPrim : OmVPrim X u')
    (hGram : OmVGram X u') (hDet : OmVDet X u') (hScale : OmVScale X u' ψ) (hBad : OmVBadT X u' ψ)
    (hLocU : OmVLocU X ψ) : Formalism.L2.SG.Pf.NcVal.OmV X u' ψ := by
  intro hψ hψ' v
  show (omAt X.B.I.cm.sig X.B.I.J ψ v (localGramMatrixFrame X u' v)
      {Y | ∃ k ∈ Kv X.B.I.cm.sig X.B.I.J (abelian₂ X) v, Y = k • ratTup (Fv X.B.I.F v) (tupH (frameOf X u'))}).toReal = _
  rw [hScale hψ hψ' v]
  by_cases hT : ((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal
  · rw [hBad hψ hψ' v hT (hSD v) (hUn v) (hPrim v), ENNReal.toReal_ofReal (val_nonneg X v _ _), exp_eq X, prod_eq X v]
    unfold aP
    rw [if_pos hT, n_sub_a X]
  · have h := hLocU v _ (yTup X u' v) (hStd hψ hψ') hLat (hSD v) (hUn v) (a_le_n X) (hPrim v)
      (by rw [hGram v]; exact hDet v hT)
    rw [hGram v] at h
    rw [h, ENNReal.toReal_ofReal (val_nonneg X v _ _), exp_eq X, prod_eq X v]
    unfold aP
    rw [if_neg hT, n_sub_a X]

end Formalism.L2.SG.Pf.NcX.OmVSt
end
end

