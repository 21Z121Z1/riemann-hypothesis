import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0223
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0018
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0191
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.AbsCentralAlt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0309
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0017
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0685
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.SupportCompat
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0012
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0192
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0600
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0046
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0054
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0037
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0105
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0137
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DescentTopStandardCharacter
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0048
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0051
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0050
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0049
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0035
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0027
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0030
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0033
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0039
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0410
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2147
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0057
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0123
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0067
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0078
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0179

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocParOfCharUnrIff
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.RankOneComp
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField
  IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil ValuativeRel
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
section Char
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [IsTotallyComplex E]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
theorem locParT_ofChar_unr_iff_unrAt (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (χ : HChar E) (h : IsPlaceOver A w) :
    (_root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (CG.ofChar χ) h).unr ↔ χ.UnrAt w := by
  first | (have hOpn := UpperTheory.One.M.opn _ (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL h); obtain ⟨a, ha, ε, H⟩ := hOpn) | obtain ⟨a, ha, ε, -, H⟩ := _root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL h
  rw [_root_.GlobalTheory.CuspRep.ParLaws.local_parameter_of_hecke_character_eq_reciprocity, H.one, Test.unr_lpOfChar_iff ha (ParLaws.isSmoothChar_loc χ w)]
  refine forall_congr' fun x => imp_congr_left ?_
  have h0 : Valued.v (x : w.adicCompletion E) ≠ 0 := by simp
  rw [← ord_eq_zero_iff, SphCompletion.ord_completion, neg_eq_zero, IsUnitAt]
  constructor
  · intro hl
    rw [← WithZero.exp_log h0, hl, WithZero.exp_zero]
  · intro hv
    rw [hv, WithZero.log_one]
theorem frobEig_locParT_ofChar_of_unrAt (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (χ : HChar E) (h : IsPlaceOver A w) (hu : χ.UnrAt w) :
    (_root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (CG.ofChar χ) h).frobEig = {(((χ.val w)⁻¹ : ℂˣ) : ℂ)} := by
  have e : χ.loc w = SmGL.unrChar (w.adicCompletion E) (χ.val w) := by
    refine MonoidHom.ext fun x => ?_
    have h2 := unif_spec w
    have h0 : Valued.v (x : w.adicCompletion E) ≠ 0 := by simp
    have h1 : IsUnitAt w (x * (atFin w (unif w) ^ ord (w.adicCompletion E) x)⁻¹) := by
      unfold IsUnitAt IsUnifAt at *
      rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, map_mul,
        map_inv₀, map_zpow₀, h2, ← WithZero.exp_zsmul, SphCompletion.ord_completion]
      simp only [smul_eq_mul, mul_neg, mul_one, neg_neg]
      rw [WithZero.exp_log h0, mul_inv_cancel₀ h0]
    have h3 := hu _ h1
    rw [map_mul, map_inv, map_zpow, mul_inv_eq_one] at h3
    exact h3
  first | (have hOpn := UpperTheory.One.M.opn _ (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL h); obtain ⟨a, ha, ε, H⟩ := hOpn) | obtain ⟨a, ha, ε, -, H⟩ := _root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL h
  have e2 : _root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (CG.ofChar χ) h = WD.mk (WDRep.diag h fun _ : Fin 1 => (χ.val w)⁻¹) := by
    rw [_root_.GlobalTheory.CuspRep.ParLaws.local_parameter_of_hecke_character_eq_reciprocity, H.one]
    have : ∀ (ξ : (w.adicCompletion E)ˣ →* ℂˣ) (hξ : WeilDeligne.IsSmooth (ξ.comp a)),
        ξ = SmGL.unrChar (w.adicCompletion E) (χ.val w) →
        WD.lpOfChar h (ξ.comp a) hξ = WD.mk (WDRep.diag h fun _ : Fin 1 => (χ.val w)⁻¹) := by
      rintro ξ hξ rfl
      exact Test.lpOfChar_unrChar ha _ _
    exact this _ _ e
  rw [e2, WD.frobEig_diag]
  simp
end Char
theorem e_locG_eq_rcAt_ofDet_of_isComp : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D),
    ∀ (π : D.naut.CG 1) (w : PlE D.host) (ξ : (w.adicCompletion D.host.E)ˣ →* ℂˣ) (h : IsComp (P.chr.e1 π).1 w ξ),
    P.T.e w (D.naut.locG π w) = _root_.GlobalTheory.NPin.weilDeligneOfLocalIrrep hL D w 1 (Irr.ofDet 1 ξ h.1) := by
  intro _ hL D P π w ξ h
  haveI := host_isCMField D.host
  set χ' := (CGu.equivChar D.host.E (P.cg.e 1 π)).1 with hχ'
  set χ := (P.chr.e1 π).1 with hχ
  have hloc : ∀ v, P.T.e v (D.naut.locG π v) = _root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (CG.ofChar χ') (D.nd.plOm.2 v) := fun v => by
    rw [P.cg.loc, hχ', CGu.ofChar_equivChar]; rfl
  have unr' : ∀ v, D.naut.unr (D.naut.locG π v) ↔ χ'.UnrAt v := fun v => by
    rw [P.T.unr, hloc v]; exact _root_.GlobalTheory.RankOneComp.locParT_ofChar_unr_iff_unrAt hL χ' _
  have hchar : χ' = χ := by
    rw [← mul_inv_eq_one]
    apply GlobalTheory.HeckeSplitRow.eq_one_of_split D.host
    filter_upwards [D.naut.locG_unr_ae π] with v hv _
    have u1 := (P.chr.unr_iff π v).1 hv
    have u2 := (unr' v).1 hv
    refine ⟨fun x hx => ?_, ?_⟩
    · rw [HChar.loc_mul, HChar.loc_inv, u1 x hx, u2 x hx, inv_one, mul_one]
    · have hf := P.chr.frob π v u1
      have hf' : D.naut.frobEig (D.naut.locG π v) = {(((χ'.val v)⁻¹ : ℂˣ) : ℂ)} := by
        rw [P.T.frobEig _ _ hv, hloc v]; exact _root_.GlobalTheory.RankOneComp.frobEig_locParT_ofChar_of_unrAt hL χ' _ u2
      rw [hf', Multiset.singleton_inj, Units.val_inj, inv_inj] at hf
      rw [HChar.val_mul, HChar.val_inv, hf, mul_inv_cancel]
  have hcomp : IsComp χ w (χ.loc w) := ⟨ParLaws.isSmoothChar_loc χ w, fun x => rfl⟩
  obtain ⟨ξ₀, -, huniq, -⟩ := GlobalTheory.T.heckeChar_localComponent_exists_unique_unitary D.host.E χ w
  have hξ : ξ = χ.loc w := (huniq _ h).trans (huniq _ hcomp).symm
  subst hξ
  rw [hloc, _root_.GlobalTheory.CuspRep.ParLaws.local_parameter_of_hecke_character_eq_reciprocity, _root_.GlobalTheory.NPin.weilDeligneOfLocalIrrep]
  rw [hchar]
  rfl
end GlobalTheory.RankOneComp
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocVUnrFrobEigOfHasSatake
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.LlcSplit
theorem locV_unr_frobEig_of_hasSatake_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (i : D.nd.Loc) (Q : D.naut.AV i) (sp : SplitPlace D.host.E) (σ : GlobalTheory.SmGL.IrrRep (GL (Fin D.R.nV) (sp.w.adicCompletion D.host.E))) (α : Fin D.R.nV → ℂˣ), IsLocS (P.H.av.S i Q) sp σ → GlobalTheory.SmGL.HasSatake σ.ρ α → D.naut.unr (D.naut.locV i Q sp.w) ∧ D.naut.frobEig (D.naut.locV i Q sp.w) = Finset.univ.val.map (fun k => (((α k)⁻¹ : ℂˣ) : ℂ)) := by
  intro hL D P i Q sp σ α hS hα
  have h3 := P.au (D.nd.j i) (D.nd.j_range i).1 (D.nd.j_range i).2 (P.H.av.rep i Q) sp σ hS
  rw [← P.H.emb i Q, ← D.nbc.embAV_loc i Q sp.w,
    _root_.GlobalTheory.CuspRep.ParLaws.reciprocity_eq_diagonal_inv_of_has_satake (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 sp.w)) hα] at h3
  have hu : D.naut.unr (D.naut.locV i Q sp.w) :=
    (P.T.unr _ _).2 (by rw [h3]; exact (GlobalTheory.WeilDeligne.WD.unr_mk _).2 (GlobalTheory.WeilDeligne.WDRep.unr_diag _))
  refine ⟨hu, ?_⟩
  rw [P.T.frobEig _ _ hu, h3, GlobalTheory.WeilDeligne.WD.frobEig_diag]
end GlobalTheory.LlcSplit
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LpSumSegmentsNuStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_segments_langlands_at_place : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)),
    letI := GlobalTheory.LocalData.complRel w
    haveI := GlobalTheory.LocalData.isLocalField w
    ∀ (h : IsPlaceOver A w) (rc : IrrGL (w.adicCompletion E) → WD h), _root_.UpperTheory.Zero.LLC.IsRecT h rc →
    ∀ (l : List (Segment (w.adicCompletion E))) (c : ℝ),
      sumList ((l.map fun Γ => Γ.nu (c : ℂ)).map fun Δ =>
          ((rc Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)).lpChar (WD.lpSp h Δ.len)) =
        (sumList (l.map fun Δ => ((rc Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)).lpChar (WD.lpSp h Δ.len))).lpTw c := by
  first | exact @_root_.GlobalTheory.lpSum_segments_nu_alt | exact _root_.GlobalTheory.lpSum_segments_nu_alt | (intros; apply _root_.GlobalTheory.lpSum_segments_nu_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MSuppC
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG
namespace UpperTheory.One.M
open GlobalTheory GlobalTheory.SerSys GlobalTheory.LocGL GlobalTheory.SmGL GlobalTheory.SplitWeil
theorem supportCompat_alt_alt : GlobalTheory.Published.ZelevinskyPolynomialRing → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (I : Ident D) (rc : GlobalTheory.SerSys.Corr D), _root_.GlobalTheory.TypeRec.IsSeriesCorrespondence hL T I rc → ∀ k v, TameGen.SupportCompat (fun a => D.naut.inePol a (D.ntypes.tg k v)) (fun π : Supp.GLRep _ => rc k v π.1 π.2) := by
  intro hZ hL D T I rc hrc k v π hi hs
  obtain ⟨L, y, hind, -, hsup, hf⟩ := GlobalTheory.SerSys.SuppTame.chain hZ (D.host.g k) π hi hs
  refine ⟨_, inInd_reps hind y hf, fun ρ hρ => ?_, ?_⟩
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hρ
    have hc := hsup.isCusp (Multiset.mem_coe.2 hx)
    exact ⟨hc.1, Ysupp.IrreducibleSupport.isIrrRep_of_isIrreducible (IrrRep.irr _),
      GlobalTheory.CuspCoef.isSupercuspidal_of_isCuspidal ℚ_[D.host.g k] x.1 _ x.rep hc.2⟩
  show D.naut.inePol (rc k v π.1 π.2) (D.ntypes.tg k v) = _
  rw [_root_.GlobalTheory.SuppIne.ine_pol_rc_eq_prod_of_has_support hL D T I rc hrc k v π y hsup, List.map_map]
  rfl
end UpperTheory.One.M
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MiStar2OfFamilies
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
namespace GlobalTheory.MiTop
theorem miStar2_of_bot_lev_fam_served_puNZ : GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.HarishChandraModules → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.MiTop.BottomHypotheses W → _root_.GlobalTheory.MiS.LevelHypothesis W → _root_.GlobalTheory.MiTop.FamilyAllConditions W → _root_.GlobalTheory.MiTop.FamilyServedCondition W → PuNZ D → (_root_.GlobalTheory.MiS.packageCoefficientSpace W).MIstar2 (W.Q.F.eV (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs) W.Q.sEE := by
  intro hDS hCR hHC D L hT Gi Gl Kc Yd cX ex W hB hLv hFam hSv hPu
  exact _root_.GlobalTheory.T.joint_star_product_nonvanishing_alt hDS hCR W hB (_root_.GlobalTheory.MiTop.descent_eV_mem_level_alt W hB hLv) (_root_.GlobalTheory.T.joint_of_famAllQ_of_servedQ hCR hHC W hFam hSv) hPu
end GlobalTheory.MiTop
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MovedTopDatum
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam
noncomputable section
namespace GlobalTheory.TopDatumTheta
open GlobalTheory.LocMod.StepVec
open GlobalTheory.FunObj.Comparison₂ (IsRed)
section Gen
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] {S T : HSp D}
end Gen
section Fam
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : D.what₂.Word} {f : _root_.GlobalTheory.Fam.FamilyCharacter W u}
  {v : VCom f.c}
theorem k_add_s_succ_eq_r (G : GLoc v) : D.R.k + (G.s + 1) = D.R.r := by
  have := G.hs
  unfold Ranks.r
  omega
def ReducesModIdeal (G : GLoc v) (w : Pl D.host.E) (x : G.S.P.J) (g : GL (Fin D.R.r) (kP w)) : Prop :=
  ∀ (a b : Fin D.R.k ⊕ Fin (G.s + 1)) (a' b' : Fin D.R.r),
    a'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ a → b'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ b → ∀ z : 𝓞 D.host.E,
      Ideal.Quotient.mk w.asIdeal z = g.val a' b' →
      valuation G.k ((x : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val a b - (ofSplit G.q).pr (z : D.host.E)) < 1
theorem reducesModIdeal_iff_maxM_sub {w : Pl D.host.E} (G : GLoc v) {π' : Datum.EAf D →+* G.k} (hπ : ∀ a, π' (toEAf D a) = G.q.pr a)
    (hred : IsRed (resS D.host.F w) (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype)) (x : G.S.P.J)
    (g : GL (Fin D.R.r) (kP w)) (M : Matrix (Fin D.R.k ⊕ Fin (G.s + 1)) (Fin D.R.k ⊕ Fin (G.s + 1)) (Formalism.L2.Herm.intAf D.host.F D.host.E))
    (hM : g.val.submatrix (firstOrd (_root_.GlobalTheory.TopDatumTheta.k_add_s_succ_eq_r G)) (firstOrd (_root_.GlobalTheory.TopDatumTheta.k_add_s_succ_eq_r G)) = M.map (resS D.host.F w)) :
    _root_.GlobalTheory.TopDatumTheta.ReducesModIdeal G w x g ↔ MaxM ((x : GL _ G.k).val - M.map (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype)) := by
  have key : ∀ a b (z : 𝓞 D.host.E), Ideal.Quotient.mk w.asIdeal z = g.val (firstOrd (_root_.GlobalTheory.TopDatumTheta.k_add_s_succ_eq_r G) a) (firstOrd (_root_.GlobalTheory.TopDatumTheta.k_add_s_succ_eq_r G) b) →
      valuation G.k ((π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) (M a b) - (ofSplit G.q).pr (z : D.host.E)) < 1 :=
    fun a b z hz => by
      have h1 : (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) (Formalism.L2.DIV.oToS D.host.F D.host.E z) =
          (ofSplit G.q).pr (z : D.host.E) := hπ (incA D (z : D.host.E))
      rw [← h1, ← RingHom.map_sub, ← hred.ker, RingHom.map_sub, Formalism.L2.DIV.resS_oToS, sub_eq_zero]
      exact (hz.trans (congrFun (congrFun hM a) b)).symm
  constructor
  · intro h a b
    obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (g.val (firstOrd (_root_.GlobalTheory.TopDatumTheta.k_add_s_succ_eq_r G) a) (firstOrd (_root_.GlobalTheory.TopDatumTheta.k_add_s_succ_eq_r G) b))
    have := Valuation.map_sub_lt _ (h a b _ _ (firstOrd_val _ a) (firstOrd_val _ b) z hz) (key a b z hz)
    rwa [sub_sub_sub_cancel_right] at this
  · intro h a b a' b' ha hb z hz
    obtain rfl : a' = firstOrd (_root_.GlobalTheory.TopDatumTheta.k_add_s_succ_eq_r G) a := Fin.ext (ha.trans (firstOrd_val _ a).symm)
    obtain rfl : b' = firstOrd (_root_.GlobalTheory.TopDatumTheta.k_add_s_succ_eq_r G) b := Fin.ext (hb.trans (firstOrd_val _ b).symm)
    have := Valuation.map_add_lt _ (h a b) (key a b z hz)
    rwa [Matrix.sub_apply, Matrix.map_apply, sub_add_sub_cancel] at this
theorem chS_eq_chrStep_fst (hPk : _root_.GlobalTheory.Fam.PackageHypotheses W) (j : ℕ) : (_root_.GlobalTheory.BaseChain.com_z W).chS j = (Lift.chrStep (_root_.GlobalTheory.Fam.pk_z W).mu0 (_root_.GlobalTheory.Fam.pk_z W).eta j).1 := by
  have hL : (_root_.GlobalTheory.Fam.pk_z W).toLevCh.Is W.P.A3.A.μ0 := hPk.bot.hyp.2.2.2.1.lev
  have hb : (_root_.GlobalTheory.Fam.pk_z W).xi W.P.A3.A.μ0 = 1 :=
    MonoidHom.ext (GlobalTheory.TwistFactorCompare.eq_one_of_chrEq_one (hL.xi_base ▸ hL.xi W.P.A3.A.μ0))
  have e : (_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu W.P.A3.A.μ0 = (_root_.GlobalTheory.Fam.pk_z W).mu0 := funext fun i => by
    change (_root_.GlobalTheory.Fam.pk_z W).mu0 i * (_root_.GlobalTheory.Fam.pk_z W).xi W.P.A3.A.μ0 = _
    rw [hb, mul_one]
  change (Lift.chrStep ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu W.P.A3.A.μ0) (_root_.GlobalTheory.Fam.pk_z W).eta j).1 = _
  rw [e]
theorem locF_iter_alt {w : Pl D.host.E} (G : GLoc v) {π' : Datum.EAf D →+* G.k} (hπ : ∀ a, π' (toEAf D a) = G.q.pr a)
    (hred : IsRed (resS D.host.F w) (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype)) {j a b : ℕ}
    (ha : a = D.R.r + j * D.R.t) (hb : b = D.R.r + (j + 1) * D.R.t) (hr : D.R.r ≤ a)
    {ea : Ix (Fin D.R.k ⊕ Fin (G.s + 1)) (Fin D.R.t) j ≃ Fin a} {eb : Ix (Fin D.R.k ⊕ Fin (G.s + 1)) (Fin D.R.t) (j + 1) ≃ Fin b}
    (oa : GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos ea) (ob : GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos eb) (χ : ℕ → (kP w)ˣ →* ℂˣ)
    (hχ : ∀ c, c ≤ j → GlobalTheory.FunObj.Comparison₂.Compat (resS D.host.F w) (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype)
      (χ (c + 1)) (G.S.μ (c + 1))) {N : Matrix (Fin b) (Fin a) (Datum.EAf D)} (hN : IsIntM N) :
    locF D.R.t j hr (_root_.GlobalTheory.TopDatumTheta.ReducesModIdeal G w) (fun y => G.S.P.lam y) χ (redM w N) =
      G.S.P.iterPhi (Fin D.R.t) G.S.μ G.S.tame j ((N.map π').submatrix eb ea) := by
  rw [redM_eq_map _ hN]
  exact locF_eq (GlobalTheory.FunObj.TieLev.iterPhi_read _ _ _ _ _ hred _ _ _ _ _ _ (firstOrd (_root_.GlobalTheory.TopDatumTheta.k_add_s_succ_eq_r G)) ea eb
    (isIx_of_isOrd _ ha oa) (isIx_of_isOrd _ hb ob) hr G.S.P G.S.μ G.S.tame χ hχ (_root_.GlobalTheory.TopDatumTheta.ReducesModIdeal G w) (_root_.GlobalTheory.TopDatumTheta.reducesModIdeal_iff_maxM_sub G hπ hred)
    (Matrix.of fun i j => (⟨N i j, hN i j⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E)))
theorem chi_compat_of_mu_eq (hPk : _root_.GlobalTheory.Fam.PackageHypotheses W) (G : GLoc v) (w : (_root_.GlobalTheory.Fam.pk_z W).Pg) (hq : Formalism.L2.NTheta.IsIdemAt G.q.e w.1) {π' : Datum.EAf D →+* G.k}
    (hπ : ∀ a, π' (toEAf D a) = G.q.pr a)
    (hred : IsRed (resS D.host.F w.1) (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype)) {c : ℕ} (h1 : 1 ≤ c) (h2 : c ≤ D.R.m)
    (hμ : (ofSplit G.q).IsComp (Lift.chrStep (_root_.GlobalTheory.Fam.pk_z W).mu0 (_root_.GlobalTheory.Fam.pk_z W).eta c).1⁻¹ (G.S.μ c)) :
    GlobalTheory.FunObj.Comparison₂.Compat (resS D.host.F w.1) (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) ((_root_.GlobalTheory.Fam.pk_z W).chi c w.1) (G.S.μ c) :=
  GlobalTheory.ChainOnto.chi_compat_of_isComp D _ G.q w.1 hq π' hπ hred (_root_.GlobalTheory.BaseChain.com_z W) (_root_.GlobalTheory.BaseChain.com_is_alt W hPk) w.2 c h1 h2 _
    (G.S.tame _) (by rw [_root_.GlobalTheory.TopDatumTheta.chS_eq_chrStep_fst hPk]; exact hμ)
set_option maxHeartbeats 1000000 in
theorem place_alt (hPk : _root_.GlobalTheory.Fam.PackageHypotheses W) {n : ℕ} {G : Fin n → GLoc v} {pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg} (hGR : _root_.GlobalTheory.Fam.LocalGroupReading f G pl) (i : Fin n) {j : ℕ}
    (h : j + 2 * 0 + 2 = D.R.m) (x : WO (Yc D (j + 1)) D.sp.X') {N : Matrix (Fin D.sp.X'.rank) (Fin (Yc D (j + 1)).rank) (Datum.EAf D)}
    (hN : N = frMapO (Yc D (j + 1)) D.sp.X' ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) (_root_.GlobalTheory.Fam.pk_z W).βX (actO _ _ (f.g.b (j + 1))⁻¹ f.g.bT⁻¹ x)) :
    (((G i).S.T (Fin D.R.t)).PhiTop ((ofSplit (G i).q).down (_root_.GlobalTheory.TopLocData.frameOfSuccessor (G i) h) (G i).FT x) ≠ 0 →
      ∀ a b, toEAf D (G i).q.e * N a b ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) ∧
    (IsIntM N → locF D.R.t (j + 1) (r_le_Y (j + 1)) (_root_.GlobalTheory.TopDatumTheta.ReducesModIdeal (G i) (pl i).1) (fun y => (G i).S.P.lam y) (fun c => (_root_.GlobalTheory.Fam.pk_z W).chi c (pl i).1)
      (redM (pl i).1 N) = ((G i).S.T (Fin D.R.t)).PhiTop ((ofSplit (G i).q).down (_root_.GlobalTheory.TopLocData.frameOfSuccessor (G i) h) (G i).FT x)) := by
  obtain rfl : (G i).s = j := _root_.GlobalTheory.TopLocData.s_eq_alt (G i) h
  have hq := (hGR.idem i).1
  obtain ⟨π', hπ, hred, hint, -⟩ := GlobalTheory.FinPl.SplitPt.exists_lift_isRed D _ (G i).q (pl i).1 hq
  obtain ⟨ea, ha, mS⟩ := hGR.frame i ((G i).s + 1) 0 rfl
  obtain ⟨eb, hb, mT⟩ := hGR.frameTop i
  have hco := coords_moved (ofSplit (G i).q) ((G i).FY ((G i).s + 1) 0 rfl) (G i).FT hπ
    (typeFrame (G i).S.ϖ (stdOrd _ _ ((G i).s + 1) 0 rfl)) (LatFrame.refl _ _) ea eb mS
    (by rw [show (LatFrame.refl (G i).k _).bas.val = 1 from rfl, Matrix.mul_one]; exact mT) x
  have hP : ((G i).S.T (Fin D.R.t)).PhiTop ((ofSplit (G i).q).down (_root_.GlobalTheory.TopLocData.frameOfSuccessor (G i) h) (G i).FT x) =
      (G i).S.P.iterPhi (Fin D.R.t) (G i).S.μ (G i).S.tame ((G i).s + 1) ((N.map π').submatrix eb ea) := by
    rw [hN]
    exact congrArg ((G i).S.P.iterPhi (Fin D.R.t) (G i).S.μ (G i).S.tame ((G i).s + 1)) hco
  rw [hP]
  refine ⟨fun hz a b => part_int (G i).q hπ hint ?_, fun hI => ?_⟩
  · simpa using TypeDatum.intM_of_Phi_ne_zero _ _ hz ((ixSucc _ _ ((G i).s + 1)).symm (eb.symm a)) (ea.symm b)
  · have r1 : (Yc D ((G i).s + 1)).rank = D.R.r + ((G i).s + 1) * D.R.t := by
      rw [D.sp.Y_rank _ (min_le_right _ _), min_eq_left (by omega)]; rfl
    have r2 : D.sp.X'.rank = D.R.r + ((G i).s + 1 + 1) * D.R.t := by
      rw [D.sp.X'_rank, (G i).hs]; rfl
    have hs := (G i).hs
    exact _root_.GlobalTheory.TopDatumTheta.locF_iter_alt (G i) hπ hred r1 r2 _ ha hb (fun c => (_root_.GlobalTheory.Fam.pk_z W).chi c (pl i).1)
      (fun c hc => _root_.GlobalTheory.TopDatumTheta.chi_compat_of_mu_eq hPk (G i) (pl i) hq hπ hred (by omega) (by omega) (hGR.mu i (c + 1) (by omega) (by omega))) hI
set_option maxHeartbeats 1000000 in
theorem datum_eq_alt (hPk : _root_.GlobalTheory.Fam.PackageHypotheses W) {n : ℕ} {G : Fin n → GLoc v} {pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg} (hGR : _root_.GlobalTheory.Fam.LocalGroupReading f G pl) {j : ℕ}
    (h : j + 2 * 0 + 2 = D.R.m) (x : WO (Yc D (j + 1)) D.sp.X') :
    (if IsHalf (∑ i, (G i).q.e) (actO _ _ (f.g.b (j + 1))⁻¹ f.g.bT⁻¹ x) ∧
        IsIntM (frMapO (Yc D (j + 1)) D.sp.X' ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) (_root_.GlobalTheory.Fam.pk_z W).βX (actO _ _ (f.g.b (j + 1))⁻¹ f.g.bT⁻¹ x)) then
      omegaG (datY _ D.R.r D.R.t (j + 1) (r_le_Y (j + 1)) (_root_.GlobalTheory.Fam.pk_z W).Pg ∅ (_root_.GlobalTheory.Fam.complexLevelStructure W) (_root_.GlobalTheory.Fam.pk_z W).chi (fun _ => 1) Frm.B) ((_root_.GlobalTheory.Fam.pk_z W).chi (j + 1 + 1))
          (fun PP => redM PP (frMapO (Yc D (j + 1)) D.sp.X' ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) (_root_.GlobalTheory.Fam.pk_z W).βX (actO _ _ (f.g.b (j + 1))⁻¹ f.g.bT⁻¹ x))) *
        omegaQ ∅ (datY _ D.R.r D.R.t (j + 1) (r_le_Y (j + 1)) (_root_.GlobalTheory.Fam.pk_z W).Pg ∅ (_root_.GlobalTheory.Fam.complexLevelStructure W) (_root_.GlobalTheory.Fam.pk_z W).chi (fun _ => 1) Frm.B).r (fun _ => 1) 1
          (fun PP => redM PP (frMapO (Yc D (j + 1)) D.sp.X' ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) (_root_.GlobalTheory.Fam.pk_z W).βX (actO _ _ (f.g.b (j + 1))⁻¹ f.g.bT⁻¹ x)))
      else 0) =
    if IsHalf (∑ i, (G i).q.e) x then
      ∏ i, ((G i).S.T (Fin D.R.t)).PhiTop ((ofSplit (G i).q).down (_root_.GlobalTheory.TopLocData.frameOfSuccessor (G i) h) (G i).FT x) else 0 := by
  obtain ⟨G', rfl⟩ : ∃ G' : (_root_.GlobalTheory.Fam.pk_z W).Pg → GLoc v, G = fun i => G' (pl i) :=
    ⟨fun w => G (pl.symm w), funext fun i => congrArg G (pl.symm_apply_apply i).symm⟩
  have hpl := fun i => _root_.GlobalTheory.TopDatumTheta.place_alt hPk hGR i h x rfl
  by_cases hx : IsHalf (∑ i, (G' (pl i)).q.e) x
  swap
  · rw [if_neg hx, if_neg fun H => hx ((isHalf_actO_iff _ _ _).1 H.1)]
  have hy := (isHalf_actO_iff (f.g.b (j + 1))⁻¹ f.g.bT⁻¹ x).2 hx
  rw [if_pos hx]
  by_cases hI : IsIntM (frMapO (Yc D (j + 1)) D.sp.X' ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) (_root_.GlobalTheory.Fam.pk_z W).βX (actO _ _ (f.g.b (j + 1))⁻¹ f.g.bT⁻¹ x))
  · rw [if_pos ⟨hy, hI⟩, GlobalTheory.FunObj.Comparison₂.omegaQ_eq_prod, Finset.prod_empty, mul_one,
      omegaG_eq_prod (r_le_Y (j + 1)) _ _ _ _ _ (fun w => _root_.GlobalTheory.TopDatumTheta.ReducesModIdeal (G' w) w.1) (fun w y => (G' w).S.P.lam y)
        (fun g => (hGR.lev g).1.trans (pl.forall_congr_right (q := fun w => ∃ y, _root_.GlobalTheory.TopDatumTheta.ReducesModIdeal (G' w) w.1 y (g w))))
        (fun g y hy => ((hGR.lev g.1).2 g.2 (fun i => y (pl i)) fun i => hy (pl i)).trans
          (Equiv.prod_comp pl fun w => (G' w).S.P.lam (y w))), ← Equiv.prod_comp pl]
    exact Finset.prod_congr rfl fun i _ => (hpl i).2 hI
  · rw [if_neg fun H => hI H.2]
    refine (Finset.prod_eq_zero_iff.2 (by_contra fun hne => hI fun a b => ?_)).symm
    have h1 : (∑ i, (G' (pl i)).q.e) • actO _ _ (f.g.b (j + 1))⁻¹ f.g.bT⁻¹ x = actO _ _ (f.g.b (j + 1))⁻¹ f.g.bT⁻¹ x :=
      Matrix.ext fun r s => hy r s
    rw [← h1, frMapO_smul]
    exact sum_part_mem _ _ _ _ fun i => (hpl i).1 (fun h0 => hne ⟨i, Finset.mem_univ _, h0⟩) a b
theorem exists_isWeilDatumO_omT_at_last (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (j : ℕ) (h : j + 2 * 0 + 2 = D.R.m) : ∃ χS χT, IsWeilDatumO (_root_.GlobalTheory.Fam.pk_z W).ψ (Yc D (j + 1)) D.sp.X' χS χT
    (omT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h) := by
  have key : ∀ n (e : D.R.m - 1 = n), IsWeilDatumO (_root_.GlobalTheory.Fam.pk_z W).ψ (Yc D n) D.sp.X'
      (Lift.chrStep ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu W.P.A3.A.μ0) (_root_.GlobalTheory.Fam.pk_z W).eta D.R.m).1
      (Lift.chrStep ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu W.P.A3.A.μ0) (_root_.GlobalTheory.Fam.pk_z W).eta D.R.m).2
      (Eq.rec (motive := fun n _ => Om (Yc D n) D.sp.X') ((_root_.GlobalTheory.Fam.pk_z W).ωX W.P.A3.A.μ0) e) := by
    rintro n rfl
    exact W.Q.charW.base.chain.ωX W.P.A3.A.μ0
  exact ⟨_, _, key _ (GlobalTheory.Fam.idx_top h)⟩
end Fam
set_option maxHeartbeats 1000000 in
theorem moved_top_datum_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ v : VCom f.c, v.Is → _root_.GlobalTheory.Fam.CommutingVectorTie f v → ∀ (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg) (hGP : GPin G), _root_.GlobalTheory.Fam.LocalGroupReading f G pl → ∀ j (h : j + 2 * 0 + 2 = D.R.m) (hψ : IsStdChar D f.c.ψ (-1)) d₀, _root_.GlobalTheory.Fam.IsDivisorGlobal W (j + 1) (_root_.GlobalTheory.Fam.pk_z W).MX (_root_.GlobalTheory.Fam.pk_z W).ΛX (_root_.GlobalTheory.Fam.pk_z W).βX (vacT (_root_.GlobalTheory.Fam.pk_z W) j h) d₀ → IsSelfDualC (Yc D (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) → IsSelfDualC D.sp.X' (_root_.GlobalTheory.Fam.pk_z W).ΛX → ∀ (M : GlobalTheory.FinPl.Lat (Yc D (j + 1))) (hM : IsSelfDualC (Yc D (j + 1)) M) (hLT : IsSelfDualC D.sp.X' f.g.LT), (∀ P, GlobalTheory.FinPl.Moves (Yc D (j + 1)) (f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) M P) → ∃ κ : ℂ, κ ≠ 0 ∧ ∀ d, _root_.GlobalTheory.Fam.IsDivisorGlobal W (j + 1) (_root_.GlobalTheory.Fam.pk_z W).MX (_root_.GlobalTheory.Fam.pk_z W).ΛX (_root_.GlobalTheory.Fam.pk_z W).βX (vacT (_root_.GlobalTheory.Fam.pk_z W) j h) d → ∃ F, IsThetaAt f.c.ψ (symplO (Yc D (j + 1)) D.sp.X') (heisO f.c.ψ (Yc D (j + 1)) D.sp.X') (∑ i, (_root_.GlobalTheory.TopLocData.localLatticeAtPlace hψ hGP h hM hLT i).q.e) (latO (Yc D (j + 1)) D.sp.X' (M : Set _) (f.g.LT : Set _) fun _ => True) 1 (omT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h (f.g.b (j + 1), f.g.bT) (vacT (_root_.GlobalTheory.Fam.pk_z W) j h)) (prodDat (_root_.GlobalTheory.TopLocData.localLatticeAtPlace hψ hGP h hM hLT)) F ∧ IsThetaFunO f.c.ψ (Yc D (j + 1)) D.sp.X' F ∧ omT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h (f.g.b (j + 1), f.g.bT) (comb f.c.ψ _ _ d (vacT (_root_.GlobalTheory.Fam.pk_z W) j h)) = κ • F := by
  intro D L hT Gi Gl Kc Yd cX ex W u f hPk _ v hv hVT n G pl hGP hGR j h hψ _ _ hΛ hΛX M hM hLT hMv
  refine ⟨1, one_ne_zero, fun d hd => ?_⟩
  obtain ⟨hvac, e, he, hθ⟩ := hd.2
  obtain ⟨χS, χT, hWe⟩ := _root_.GlobalTheory.TopDatumTheta.exists_isWeilDatumO_omT_at_last W j h
  have hb : f.g.b (j + 1) ∈ GfC _ := hVT.b (j + 1) ▸ hv.b (j + 1)
  have hb' : f.g.bT ∈ GfC _ := hVT.bT.1 ▸ hv.bT
  have hcth := GlobalTheory.VecTheta.isThetaFunO_stepVec hd.2
  have he' : IsIdemSum e ((_root_.GlobalTheory.Fam.pk_z W).Pg) := by simpa only [datY, Finset.union_empty] using he
  have hee : e = ∑ i, (G i).q.e := idem_eq he' _ pl fun i => (hGR.idem i).1
  have hmove := GlobalTheory.VacMove.isThetaAt_moveLat D f.c.ψ _ _ _ _ _ hWe ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) M (_root_.GlobalTheory.Fam.pk_z W).ΛX f.g.LT hΛ hM hΛX hLT
    _ hb _ hb' (hMv _) (hVT.movesT _) e _ _ _ (GlobalTheory.PlaceDatum.idemSum_mul_self he) (GlobalTheory.PlaceDatum.infPart_idemSum he)
    hvac.2.theta hcth hθ
  subst hee
  refine ⟨_, ?_, hWe.om_pres _ _ hcth, (one_smul _ _).symm⟩
  have hfun : prodDat (_root_.GlobalTheory.TopLocData.localLatticeAtPlace hψ hGP h hM hLT) = _ := funext fun x => (_root_.GlobalTheory.TopDatumTheta.datum_eq_alt hPk hGR h x).symm
  rw [hfun]
  exact hmove
end GlobalTheory.TopDatumTheta
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.OneFieldOfNAt
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField ReciprocityTheory.Gal GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.Fc GlobalTheory.NFacts
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.NFacts.AtMemFacts
theorem oneField_of_nAt_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} {cf : Formalism.L2.Host.CharFrame D} {C : NChoice D} {tp : Formalism.L2.Host.TupTied D cf C}
    (a : _root_.GlobalTheory.Mem.Top.Bl.NAtData hL D cf C tp) : GlobalTheory.HeightCounting.SameTw.OneField D C := by
  have key : ∀ X : Σ (D₁ : D7) (c₁ : Formalism.L2.Host.CharFrame D₁) (C₁ : NChoice D₁), Formalism.L2.Host.TupTied D₁ c₁ C₁,
      X = ⟨withLoc a.nt.L, cfL a.nt.L a.nt.cf, chL a.nt.L a.nt.C, tpL a.nt.L a.nt.tp⟩ →
        GlobalTheory.HeightCounting.SameTw.OneField X.1 X.2.2.1 := by
    rintro _ rfl
    exact (GlobalTheory.HeightCounting.SameTw.oneField_withLoc a.nt.L a.nt.C).2 a.nt.Sp.tw_reads
  exact key _ a.nt.pack
end GlobalTheory.NFacts.AtMemFacts
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ReadTwistedStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop NumberField IsDedekindDomain
open GlobalTheory.FunObj.SqNum (nuH halfRank IsTor)
open GlobalTheory.CMVal GlobalTheory.HeckeGal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.toric_ratio_field_data_abelian_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (CF : ℝ) (d : FunIn p CF), p.PointConditions' → Fitted (@Comparison₂) p CF d → GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.ToricRatioConjugates → (∃ (_ : IsCMField D.host.E) (_ : IsAbelianGalois ℚ D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData D.host.d (GlobalTheory.FunObj.SqNum.cmPhi D) ∧
    GlobalTheory.CMVal.IsBaseCond (GlobalTheory.FunObj.SqNum.condF d.G.pl) ∧ ∃ Λ, GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice D.host.d Λ) → ∀ w : D.what₂.places.Pl, TwistedAt D w → ∀ (i j : Fin D.R.m) (s : ℕ), 1 ≤ s → s ≤ halfRank D i j →
    ∀ (T₀ : ℂ) (ψc : PicO (condQ (GlobalTheory.FunObj.SqNum.condF d.G.pl) (GlobalTheory.ToricDenom.belowSet (ex.nch.Q w))) →* ℂˣ) (T : (PicO (condQ (GlobalTheory.FunObj.SqNum.condF d.G.pl) (GlobalTheory.ToricDenom.belowSet (ex.nch.Q w))) →* ℂˣ) → ℂ), IsValChar (GlobalTheory.FunObj.SqNum.cmPhi D) s (GlobalTheory.FunObj.SqNum.kap D 1 i j s) (GlobalTheory.FunObj.SqNum.condF d.G.pl) ∅ (nuH d.G p.P.A3.A.μ0 i j * p.R.C.delAt (D.what₂.places.resChar w)) →
      IsToricSum (GlobalTheory.FunObj.SqNum.cmPhi D) s (GlobalTheory.FunObj.SqNum.kap D 1 i j s) (GlobalTheory.FunObj.SqNum.condF d.G.pl) (nuH d.G p.P.A3.A.μ0 i j * p.R.C.delAt (D.what₂.places.resChar w)) T₀ → T₀ ≠ 0 →
      (∀ y, finPart (p.Tp.psi w) y = ψc (QuotientGroup.mk y)) →
      (∀ ψ, GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.IsTwistedSum (GlobalTheory.FunObj.SqNum.cmPhi D) s (GlobalTheory.FunObj.SqNum.kap D 1 i j s) (condQ (GlobalTheory.FunObj.SqNum.condF d.G.pl) (GlobalTheory.ToricDenom.belowSet (ex.nch.Q w))) (nuH d.G p.P.A3.A.μ0 i j * p.R.C.delAt (D.what₂.places.resChar w)) ψ (T ψ)) → (∃ ι : ℂ →+* GlobalTheory.ToricDenom.Kbar D.ntw (ex.nch.twI w),
        (∀ x : D.LL0, ι (D.what₂.embLL (x : D.what₂.LL)) = GlobalTheory.ToricDenom.toBar D.ntw (ex.nch.twI w) (D.ntw.emb0 (ex.nch.twI w) x)) ∧
        ∀ b : Bool, ∃ (lam : D.ntw.abelian₂ (ex.nch.twI w)) (jk : FractionRing (D.ntw.Ok (ex.nch.twI w) (ex.nch.k' w)) →+* GlobalTheory.ToricDenom.Kbar D.ntw (ex.nch.twI w)) (c : ℤ),
            D.ntw.sideL (ex.nch.twI w) lam = b ∧ IsCoprime c (D.ntw.l (ex.nch.twI w) : ℤ) ∧
            jk.comp (BlochKatoReduction.Gen.kMap D.ntw (ex.nch.twI w) (ex.nch.k' w)) = algebraMap (FractionRing (D.ntw.O (ex.nch.twI w))) (GlobalTheory.ToricDenom.Kbar D.ntw (ex.nch.twI w)) ∧
            ∀ a : ℤ, jk (BlochKatoReduction.Gen.thEval D.ntw (ex.nch.twI w) (ex.nch.Q w) lam (ex.nch.k' w) (BlochKatoReduction.Gen.psiAt (D.ntw.sideL (ex.nch.twI w) lam) (ex.nch.psi' w ^ a))) *
                GlobalTheory.ToricDenom.atSide D.ntw b ι T₀ =
              jk (BlochKatoReduction.Gen.kMap D.ntw (ex.nch.twI w) (ex.nch.k' w) (∑ δ, D.ntw.th (ex.nch.twI w) ∅ lam δ)) * GlobalTheory.ToricDenom.atSide D.ntw b ι (T (ψc ^ (c * a)))) := by
  first | exact @_root_.GlobalTheory.ThmAUpper.read_twisted_alt | exact _root_.GlobalTheory.ThmAUpper.read_twisted_alt | (intros; apply _root_.GlobalTheory.ThmAUpper.read_twisted_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowHServOfLinkStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hServ_of_linkR : GlobalTheory.Published.GlobalArtinReciprocity → ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) (Lk : LkT _root_.GlobalTheory.Fc.BundleCondition), (∀ (K : Ctx) (β : BPt K) (c : ℝ) (b : _root_.GlobalTheory.Fc.BundleCondition β.D β.O c), Lk K β c b → _root_.GlobalTheory.Mem.Top.Bl.ReciprocityLinkage p K β c b.R) → _root_.GlobalTheory.Fc.R1.SlotServiceCondition (IsGoodE p.s) Lk := by
  first | exact @_root_.GlobalTheory.row_hServ_of_link_alt | exact _root_.GlobalTheory.row_hServ_of_link_alt | (intros; apply _root_.GlobalTheory.row_hServ_of_link_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WeilDeligneRankOneEqLocal
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.TripleGal GlobalTheory.CuspRep
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section
namespace GlobalTheory.AwayLGC
theorem weil_deligne_rank_one_eq_local_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (E Ω : Type) [Field E] [NumberField E] [IsTotallyComplex E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (art : Ideles E →* Gab E Ω), IsGlobalArtin art → ∀ (χ : HChar E) (n : (E →+* ℂ) → ℤ) (μ : G E Ω →* (Qbar l)ˣ), Continuous μ → IsLAdicOf art ι χ n μ → ∀ (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal), GlobalTheory.WeilDeligne.wdOf h hl ι (rk1 μ) = _root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (CG.ofChar χ) h := by
  intro hL E Ω _ _ _ _ _ _ l _ ι art hart χ n μ hμ hlad A w h hl
  first | (have hOpn := UpperTheory.One.M.opn _ (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL h); obtain ⟨a, ha, ε, H⟩ := hOpn) | obtain ⟨a, ha, ε, -, H⟩ := _root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL h
  rw [_root_.GlobalTheory.CuspRep.ParLaws.local_parameter_of_hecke_character_eq_reciprocity, H.one]
  refine GlobalTheory.WeilDeligne.wdOf_eq_mk hl _ rfl fun g => ?_
  have e := hlad.loc_away (Or.inl hl) (a g) (g : G E Ω) (ha.glob art hart g)
  refine LinearMap.ext fun v => funext fun i => ?_
  rw [Subsingleton.elim i 0]
  simp [GlobalTheory.WeilDeligne.toEndC_apply, GlobalTheory.TripleGal.rk1, Matrix.mulVec, dotProduct, e]
end GlobalTheory.AwayLGC
end
end
end

